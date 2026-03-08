# VEX Genericity Boundaries

This document records what the current Lean VEX model is generic over, what remains architecture-sensitive, and what other workstreams may assume.

## Generic Now

The core VEX Lean stack is generic over a finite register type:

- `Reg : Type`
- `[DecidableEq Reg]`
- `[Fintype Reg]`

The core semantics and proofs are no longer hardcoded to AMD64 register names.

The instruction-pointer register is explicit:

- each `Block Reg` carries `ip_reg : Reg`

This means fallthrough and exit updates are generic over the chosen register file.

The theorem/proof stack is generic through:

- raw VEX syntax
- concrete execution
- symbolic summaries `(σ, φ)`
- bridge enforcement and lowering correctness

AMD64 is now a frontend instantiation, not part of the theorem-level core.

## Frontend Responsibility

Architecture-specific VEX register offsets are translated in the frontend/extractor layer.

Today that means:

- the Python extractor maps VEX offsets to `Amd64Reg`
- the Lean core works over `Reg`, not raw VEX offsets

This separation is intentional. Offset-layout knowledge belongs in the lift/import layer, not in the generic proof stack.

## Not Generic Yet

Two important semantic boundaries remain deferred.

### 1. Endianness

The current memory model and lowering are little-endian for the implemented memory operations.

Current assumptions include:

- `load64` is little-endian
- `store64` is little-endian

This is adequate for the current AMD64 slice, but not a generic VEX memory semantics.

### 2. Sub-Register / Width Semantics

The current register semantics are full-width only for the implemented slice.

Not yet modeled generically:

- partial-register writes
- width-specific register behavior
- zero/sign extension rules tied to narrower writes
- aliasing between overlapping architectural registers

This is the next major semantic boundary for realistic lifted x86/AMD64 coverage.

## What Coverage Work May Assume

Coverage work may safely expand only within the current semantic slice:

- finite register-file generic core
- explicit `ip_reg`
- little-endian `load64` / `store64`
- full-width register behavior only
- current branch model and `(σ, φ)` summary discipline

Coverage work must stop and coordinate if a new fixture requires:

- big-endian memory behavior
- partial-register or narrower-width semantics
- flags/cc machinery beyond the current modeled slice
- richer CFG/multi-exit structure outside the current bridge surface

## Priority Of Next Semantic Boundaries

Recommended order:

1. sub-register / width semantics
2. endianness-aware memory ops

Reason:

- width semantics are more likely to affect near-term AMD64 lifted coverage
- endianness is important, but less urgent for the current AMD64-focused corpus

## Practical Consequence

The current model should be understood as:

- a register-generic VEX core
- with AMD64 as the first frontend instance
- and with endianness + width semantics still to be generalized

That is the boundary other lanes should code against.
