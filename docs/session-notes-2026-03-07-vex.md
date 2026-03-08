# Session Notes — 2026-03-07 — VEX Reference Path

## Scope of this session

The session started after the module reorg had already been completed and committed as:

- `1ae081be` — `reorganize Lean modules into Core/SymExec/Learnability/Instances`

The new work in this session focused on:

1. switching the VEX reference path to a nix-flake-based workflow
2. ensuring Python tooling uses `uv` only inside the nix shell
3. grounding the VEX work against pinned `angr` / `pyvex`
4. building one minimal end-to-end concrete VEX example checked against `angr`
5. stopping before the symbolic-summary design boundary

An unrelated prototype file from earlier work:

- `Learnability/TierTransport.lean`

was explicitly removed during this session and is no longer in the working copy.


## High-level decisions made

### 1. Reference backend choice

The reference backend for the first implementation slice is:

- `angr` VEX, not p-code

Reasons:

- `angr` is VEX-first
- VEX support in `angr` is more mature than p-code support
- it gives a realistic anchor without needing a full ISA formalization first

### 2. Pinning strategy

Two different kinds of pins were distinguished:

- packaging pin: `angr-nix`
- semantic/tooling pins: upstream `angr` and `pyvex`

Pinned values used:

- packaging flake remote: `git@github.com:heartpunk/angr-nix.git`
- packaging flake commit: `2f20f9ed68506bd151ed171e505942ac9a2a0b43`
- upstream `angr` tag/commit:
  - `v9.2.204`
  - `359a018f01e27b6d4a8e872d08f4f17c0a092441`
- upstream `pyvex` tag/commit:
  - `v9.2.204`
  - `623dbb9c40df8eed7d514c6767d86afd315a5b4e`

### 3. Python toolchain policy

The user required:

- use nix flake
- use `uv` with that nix environment
- do not use host `uv`
- revert earlier ad hoc setup that this obviates

The final policy implemented is:

- Python reference tooling runs only inside `nix develop`
- `uv` is provided by the nix shell
- `uv venv --system-site-packages` is used inside the nix shell so the venv inherits nix-provided `angr` / `pyvex`

### 4. Immediate VEX implementation scope

The first implemented slice is deliberately narrow:

- architecture: AMD64
- IR: VEX IRSB
- fragment: straight-line block
- no memory side effects
- no flags
- no calls
- no syscalls
- no dirty helpers
- no exceptions
- only boring fallthrough exit

### 5. Concrete-before-symbolic sequencing

The session explicitly stopped at the boundary where a symbolic-summary representation would need to be chosen.

What was implemented:

- concrete VEX fragment evaluator
- `angr` fixture extraction
- end-to-end comparison

What was not implemented:

- a `SymbolicISA` instance for VEX
- any symbolic substitution/path-condition algebra for VEX


## Problems encountered and how they were resolved

### Problem 1: ad hoc Python environment

Earlier exploratory work had created:

- `.venv-angr`

This conflicted with the new requirement to use nix + `uv`.

Resolution:

- `.venv-angr` was removed

### Problem 2: broken `cache.lix.systems` substituter

Running `nix develop` initially failed because the configured `cache.lix.systems` substituter was unreachable.

Observed behavior:

- repeated `.narinfo` download failures from `https://cache.lix.systems/...`

Resolution:

- switched to `nix develop --fallback`
- Lix then disabled the broken cache and pulled/build from other sources

This remains a runtime annoyance but is workable.

### Problem 3: wrong attempt to use host `uv`

There was an intermediate mistake where `uv` from the host environment was used.

The user explicitly rejected this.

Resolution:

- all subsequent `uv` use was moved inside `nix develop`

### Problem 4: trying to use `~/code/angr-nix/result/bin/python`

This failed with:

- `exec format error`

That path pointed at a non-runnable result for the local machine in this context.

Resolution:

- dropped that path
- standardized on `nix develop ... --fallback`

### Problem 5: flake lock command confusion

Running:

- `nix flake lock`
- `nix flake lock "$PWD"`

hit path/git resolution issues in this environment.

Working solution:

- `nix flake lock "path:$PWD"`

### Problem 6: Lean imports from Mathlib tactics

The initial VEX Lean files imported:

- `Mathlib.Tactic.NativeDecide`
- then `Mathlib.Tactic`

These object files were not available in the current pinned mathlib build.

Resolution:

- removed those imports
- used `decide` directly in the small example proof

### Problem 7: one proof in `VexISA.lean`

The initial proof of `ConcreteState.read_write_other` used `contradiction` in a way that failed.

Resolution:

- replaced it with a direct case split:
  - `cases reg <;> cases reg' <;> first | cases (h rfl) | rfl`

### Problem 8: `lake build` failed because `Instances` root module did not exist

After adding `Instances` to `defaultTargets`, `lake build` failed with:

- missing file `Instances.lean`

Resolution:

- added `Instances.lean` importing the new and existing instance/example modules


## Files added or modified

### New files

- `flake.nix`
- `flake.lock`
- `docs/vex-plan.md`
- `docs/session-notes-2026-03-07-vex.md`
- `tools/vex_ref/pyproject.toml`
- `tools/vex_ref/uv.lock`
- `tools/vex_ref/extract_fixture.py`
- `tools/vex_ref/fixtures/amd64_lea_rdi_plus_5.json`
- `Instances/ISAs/VexISA.lean`
- `Instances/Examples/VexLeaRdiPlus5Fixture.lean`
- `Instances/Examples/VexLeaExample.lean`
- `Instances.lean`

### Modified files

- `.gitignore`
- `lakefile.toml`

### Removed file

- `Learnability/TierTransport.lean`


## Exact repo changes and their purpose

### `flake.nix`

Added a repo-local flake to provide a reference VEX environment.

Inputs:

- `nixpkgs`
- `angr-nix` pinned to the chosen remote commit

Shell packages:

- `angr-nix.packages.${system}.default`
- `uv`
- `jq`

Environment:

- `UV_NO_MANAGED_PYTHON=1`
- `UV_PYTHON_DOWNLOADS=never`

Purpose:

- make the VEX reference path reproducible in the repo

### `flake.lock`

Generated and checked into the repo.

Purpose:

- lock the flake inputs for reproducibility

### `docs/vex-plan.md`

Documents:

- the pins
- initial VEX fragment scope
- the first fixture
- the exact reference workflow command

Purpose:

- make the intended workflow explicit

### `tools/vex_ref/pyproject.toml`

Tiny Python project for the reference extractor.

Purpose:

- gives `uv` a project root

### `tools/vex_ref/uv.lock`

`uv` lockfile for the tiny extractor project.

Purpose:

- keep the tool subproject reproducible
- even though the actual heavy dependencies come from nix system-site packages

### `tools/vex_ref/extract_fixture.py`

This script:

1. lifts raw machine code bytes with `pyvex`
2. executes one block concretely with `angr`
3. normalizes the VEX statements into a small JSON form
4. emits:
   - JSON fixture
   - Lean fixture module

Current supported expressions:

- `Get`
- `RdTmp`
- `Const`
- `Binop Iop_Add64`

Current supported statements:

- `IMark` (ignored)
- `WrTmp`
- `Put`

Current supported block shape:

- constant `next`
- straight-line

Current supported architecture:

- `amd64`

Purpose:

- extract a real VEX/angr reference artifact that Lean can check against

### `tools/vex_ref/fixtures/amd64_lea_rdi_plus_5.json`

Generated fixture for the first end-to-end target.

It records:

- metadata (`name`, `arch`, `base`, bytes)
- pretty VEX IRSB text
- normalized block:
  - `t2 = GET(rdi)`
  - `t1 = Add64(t2, 5)`
  - `PUT(rax) = t1`
  - `next = 0x400004`
- concrete input:
  - `rax = 0`
  - `rdi = 0x10`
  - `rip = 0x400000`
- concrete expected output from `angr`:
  - `rax = 0x15`
  - `rdi = 0x10`
  - `rip = 0x400004`

Purpose:

- provide a durable cross-check artifact

### `Instances/ISAs/VexISA.lean`

This file defines a minimal concrete VEX-like evaluator.

Datatypes:

- `Reg`:
  - `rax`
  - `rdi`
  - `rip`
- `Expr`:
  - `const`
  - `get`
  - `tmp`
  - `add64`
- `Stmt`:
  - `wrTmp`
  - `put`
- `Block`
- `ConcreteState`

Semantics:

- temporary environment
- state read/write
- expression evaluation
- statement execution
- block execution

Notably:

- this is concrete execution only
- it is not yet a `SymbolicISA`

Purpose:

- provide the Lean-side executable model for the first VEX fragment

### `Instances/Examples/VexLeaRdiPlus5Fixture.lean`

Auto-generated from the extractor.

Contains:

- `bytes`
- `block`
- `input`
- `expected`

Purpose:

- give Lean a checked-in reference fixture

### `Instances/Examples/VexLeaExample.lean`

Contains the end-to-end check:

- `example : execBlock block input = expected := by decide`

Purpose:

- verify the Lean concrete VEX evaluator matches the `angr` fixture

### `Instances.lean`

Added as the root module for the `Instances` library.

Imports:

- `Instances.Examples.BranchExample`
- `Instances.Examples.VexLeaExample`
- `Instances.Examples.VexLeaRdiPlus5Fixture`
- `Instances.ISAs.MachineISA`
- `Instances.ISAs.VexISA`

Purpose:

- make the new modules visible to Lake as part of the `Instances` target

### `.gitignore`

Added ignores for:

- `tools/vex_ref/.venv/`
- `.uv-angr/`

Purpose:

- prevent local venv artifacts from being tracked

### `lakefile.toml`

Updated `defaultTargets` to include:

- `Instances`

Purpose:

- make the new VEX instance/examples part of normal `lake build`


## Commands and validation steps performed

### Repo state / reorg verification

Checked working copy and reorganized module layout after the earlier commit.

### angr-nix discovery

Verified:

- remote URL
- `flake.nix`
- exposed packages/shells

### Confirmed upstream pins

Previously established during the session:

- `angr v9.2.204`
- `pyvex v9.2.204`

### Nix shell validation

Validated:

```sh
nix develop "path:$PWD" --fallback -c ...
```

Within the shell:

- `python` imports `angr`, `pyvex`, `archinfo`
- `uv --version` works
- `uv venv --system-site-packages` works
- the activated venv still sees nix-provided `angr`/`pyvex`

Observed versions inside the shell:

- `angr 9.2.204`
- `pyvex 9.2.204`
- `archinfo 9.2.204`
- `uv 0.10.6`

Note:

- a warning about unicorn loading appears:
  - `failed loading "unicornlib.dylib", unicorn support disabled`
- it did not block the workflow used here

### Fixture generation

Successfully ran:

```sh
nix develop "path:$PWD" --fallback -c sh -lc '
  cd tools/vex_ref
  uv venv --clear --python "$(command -v python)" --system-site-packages .venv >/dev/null
  . .venv/bin/activate
  uv run --active ./extract_fixture.py \
    --name amd64_lea_rdi_plus_5 \
    --arch amd64 \
    --base 0x400000 \
    --bytes 488d4705 \
    --input-reg rdi=0x10
'
```

Generated:

- JSON fixture
- Lean fixture

### Lean validation

Validated the new Lean pieces in stages:

- `lake env lean Instances/ISAs/VexISA.lean`
- `lake build Instances.ISAs.VexISA Instances.Examples.VexLeaRdiPlus5Fixture Instances.Examples.VexLeaExample`
- `lake build`

Final result:

- `lake build` succeeded
- build completed successfully with `Instances` included


## What the first fixture concretely demonstrated

The chosen block:

- bytes: `48 8d 47 05`
- instruction: `lea rax, [rdi+0x5]`

`pyvex` lifted it to an IRSB equivalent to:

- `t2 = GET:I64(rdi)`
- `t1 = Add64(t2, 0x5)`
- `PUT(rax) = t1`
- `NEXT: PUT(rip) = 0x400004; Ijk_Boring`

`angr` executed it on input:

- `rdi = 0x10`

and produced:

- `rax = 0x15`
- `rip = 0x400004`

The Lean evaluator on the generated block produced the same result.


## Architectural conclusion reached

The current `Instances/ISAs/VexISA.lean` is:

- a concrete executable semantics for a tiny VEX fragment

It is **not yet**:

- a `SymbolicISA` instance

The important conceptual conclusion of the session was:

- the next real design step is to define the **symbolic summary object** for VEX blocks

This was discussed in the light of:

- ICTAC paper (`25-tcs.pdf`)
- memory-model-parametric CSE paper (`3763151.pdf`)

The resulting direction is:

- keep the ICTAC `(σ, φ)` shape
- make `σ` a symbolic transformer over full machine state
- include memory in the state transformer
- treat VEX temps as local lowering artifacts, not part of the external composed summary

So the intended symbolic object is not raw IRSB syntax, but a canonical block summary:

- symbolic state update
- path condition


## Why the work stopped where it did

The user had asked to stop if the work needed to diverge from the agreed plan.

The agreed plan allowed:

1. pinning and documenting the reference toolchain
2. adding the Python extractor
3. adding a tiny Lean VEX subset and concrete evaluator
4. establishing one end-to-end check against `angr`

The next step would have been:

- “lift the subset into `SymbolicISA`”

That step is not mechanical. It requires a design choice about:

- the symbolic substitution/state-update representation
- path conditions
- memory representation in the symbolic summary
- how composition should work over those summaries

So the implementation stopped before crossing that design boundary.


## Current working copy summary at the end of the session

Tracked changes present:

- `.gitignore` (modified)
- `Instances/Examples/VexLeaExample.lean` (added)
- `Instances/Examples/VexLeaRdiPlus5Fixture.lean` (added)
- `Instances/ISAs/VexISA.lean` (added)
- `Instances.lean` (added)
- `docs/vex-plan.md` (added)
- `docs/session-notes-2026-03-07-vex.md` (added)
- `flake.lock` (added)
- `flake.nix` (added)
- `lakefile.toml` (modified)
- `tools/vex_ref/extract_fixture.py` (added)
- `tools/vex_ref/fixtures/amd64_lea_rdi_plus_5.json` (added)
- `tools/vex_ref/pyproject.toml` (added)
- `tools/vex_ref/uv.lock` (added)

Removed:

- `Learnability/TierTransport.lean`

No new commit was made in this session.


## Immediate next-step recommendation from this session

Do not jump directly to “all of VEX as raw syntax under `SymbolicISA`”.

Instead:

1. keep the current concrete VEX frontend
2. define a symbolic VEX block summary type `(σ, φ)` over full machine state
3. lower the current straight-line fragment into that summary type
4. prove concrete/symbolic correspondence for that fragment
5. instantiate `SymbolicISA` on the summary type
6. then extend the frontend and lowering to more VEX features


## Continuation update: rebased coverage and memory milestone progress

This session continued substantially past the initial straight-line `lea` slice.

Committed follow-up work:

- `5c92663df987` `add fixed memory to VEX concrete and symbolic state`
- `da8d30c546d0` `expand VEX coverage corpus`
- `0fd138f5f2f4` `regenerate VEX coverage fixtures for memory-aware state`
- `6870e7643968` `clean unused-variable warnings in Learnability.Framework`
- `14d3589425b7` `add VEX load64 semantics and lowering`
- `6e413af7cea2` `add angr-backed VEX load64 fixture generation and example`
- `3ea5984739b8` `add VEX store64 semantics and lowering`
- `1fc9db26f2f0` `add angr-backed VEX store64 fixture generation and example`

Current VEX state after those commits:

- concrete state now includes full byte-addressed memory:
  - `ConcreteState.mem : ByteMem`
- symbolic summaries now also include memory:
  - `SymSub.regs : Reg -> SymExpr`
  - `SymSub.mem : SymMem`
- symbolic memory is represented as a store-chain:
  - `SymMem.base`
  - `SymMem.store64`
- symbolic expressions can read memory:
  - `SymExpr.load64`

Concrete VEX fragment now implemented:

- registers:
  - `rax`
  - `rcx`
  - `rdi`
  - `rip`
- expressions:
  - `const`
  - `get`
  - `tmp`
  - `add64`
  - `load64`
- conditions:
  - `eq64`
- statements:
  - `wrTmp`
  - `put`
  - `store64`
  - `exit`

Symbolic/lowering status:

- straight-line and guarded blocks lower to ICTAC-style summaries `(σ, φ)`
- the lowering proofs now cover:
  - register-only blocks
  - guarded exit blocks
  - `load64`
  - `store64`
- `VexSummaryISA` is a real `SymbolicISA` instance over the current summary algebra

Reference-validation status:

- full corpus revalidated after the memory-state rebase
- added one real `angr`-backed load fixture:
  - `amd64_mov_rax_mem_rdi`
- added one real `angr`-backed store fixture:
  - `amd64_mov_mem_rdi_rax`

Build status at this point:

- `lake build` succeeds for the full repository
- build size at this point: `792 jobs`

Current milestone status:

- the initial VEX memory milestone is complete
- both `load64` and `store64` now exist in all three layers:
  - concrete execution
  - symbolic lowering to `(σ, φ)`
  - `angr`-backed reference fixtures

Natural next step after this milestone:

- decide whether to widen coverage within the current fragment in a separate workspace,
  or shift back to theory work on convergence objects / normalization / quotients
