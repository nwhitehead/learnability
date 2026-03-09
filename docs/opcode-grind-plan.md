# Opcode Grind Plan

This document is the execution plan for extending the current VEX core with additional operations.

Scope:
- This is for the current VEX expression/condition core under `Instances/ISAs/`.
- The goal is to make mechanical opcode additions easy to hand to fresh Codex instances.
- This document is intentionally concrete: exact files, exact functions, exact patterns.

Current supported expression/condition surface:

```text
Expr:
  const
  get
  tmp
  narrow32
  zext64
  add32
  add64
  load64

Cond:
  eq64
  amd64CalculateCondition
```

Core files involved:

```text
Instances/ISAs/VexSyntax.lean
Instances/ISAs/VexConcrete.lean
Instances/ISAs/VexSummary.lean
Instances/ISAs/VexLowerCore.lean
Instances/ISAs/VexBridgeCore.lean
Instances/ISAs/VexLoweringCorrectness.lean
```

Reference template ops:

```text
Expr-level arithmetic template: add64
Expr-level width-aware template: add32
Cond-level template: eq64
```

For each opcode task below:
- keep build green
- do not widen semantics beyond the named op
- use the existing `add64` pattern unless the section explicitly says otherwise

## Mechanical Expr Ops

These are good grind tasks. They do not change the PC language, only the expression language.

### Common pattern for every mechanical expr op

Add the constructor to:

```text
Instances/ISAs/VexSyntax.lean
  - `inductive Expr`

Instances/ISAs/VexSummary.lean
  - `inductive SymExpr`
  - `evalSymExpr`
  - `substSymExpr`

Instances/ISAs/VexConcrete.lean
  - `evalExpr`

Instances/ISAs/VexLowerCore.lean
  - `lowerExpr`

Instances/ISAs/VexBridgeCore.lean
  - `lowerExpr_sound`
```

`Instances/ISAs/VexLoweringCorrectness.lean` should usually require **no direct edits**. The existing generic proofs should replay once `lowerExpr_sound` is extended.

### 1. `sub64`

Use `add64` as the exact template.

Files/functions:

```text
VexSyntax.lean
  Expr.sub64 : Expr Reg -> Expr Reg -> Expr Reg

VexConcrete.lean
  evalExpr
    | .sub64 lhs rhs => evalExpr state temps lhs - evalExpr state temps rhs

VexSummary.lean
  SymExpr.sub64
  evalSymExpr
    | .sub64 lhs rhs => evalSymExpr state lhs - evalSymExpr state rhs
  substSymExpr
    | .sub64 lhs rhs => .sub64 (substSymExpr sub lhs) (substSymExpr sub rhs)

VexLowerCore.lean
  lowerExpr
    | .sub64 lhs rhs => .sub64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)

VexBridgeCore.lean
  lowerExpr_sound
    | sub64 lhs rhs ihL ihR =>
        simp [lowerExpr, ihL, ihR]
```

### 2. `xor64`

Use `add64` as template, but concrete/symbolic semantics use `^^^`.

Files/functions:

```text
VexSyntax.lean
  Expr.xor64

VexConcrete.lean
  evalExpr
    | .xor64 lhs rhs => evalExpr state temps lhs ^^^ evalExpr state temps rhs

VexSummary.lean
  SymExpr.xor64
  evalSymExpr
    | .xor64 lhs rhs => evalSymExpr state lhs ^^^ evalSymExpr state rhs
  substSymExpr
    | .xor64 lhs rhs => .xor64 (substSymExpr sub lhs) (substSymExpr sub rhs)

VexLowerCore.lean
  lowerExpr
    | .xor64 lhs rhs => .xor64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)

VexBridgeCore.lean
  lowerExpr_sound
    | xor64 lhs rhs ihL ihR =>
        simp [lowerExpr, ihL, ihR]
```

### 3. `and64`

Use `add64` as template, but semantics use `&&&`.

Files/functions:

```text
VexSyntax.lean
  Expr.and64

VexConcrete.lean
  evalExpr
    | .and64 lhs rhs => evalExpr state temps lhs &&& evalExpr state temps rhs

VexSummary.lean
  SymExpr.and64
  evalSymExpr
    | .and64 lhs rhs => evalSymExpr state lhs &&& evalSymExpr state rhs
  substSymExpr
    | .and64 lhs rhs => .and64 (substSymExpr sub lhs) (substSymExpr sub rhs)

VexLowerCore.lean
  lowerExpr
    | .and64 lhs rhs => .and64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)

VexBridgeCore.lean
  lowerExpr_sound
    | and64 lhs rhs ihL ihR =>
        simp [lowerExpr, ihL, ihR]
```

### 4. `or64`

Use `add64` as template, but semantics use `|||`.

Files/functions:

```text
VexSyntax.lean
  Expr.or64

VexConcrete.lean
  evalExpr
    | .or64 lhs rhs => evalExpr state temps lhs ||| evalExpr state temps rhs

VexSummary.lean
  SymExpr.or64
  evalSymExpr
    | .or64 lhs rhs => evalSymExpr state lhs ||| evalSymExpr state rhs
  substSymExpr
    | .or64 lhs rhs => .or64 (substSymExpr sub lhs) (substSymExpr sub rhs)

VexLowerCore.lean
  lowerExpr
    | .or64 lhs rhs => .or64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)

VexBridgeCore.lean
  lowerExpr_sound
    | or64 lhs rhs ihL ihR =>
        simp [lowerExpr, ihL, ihR]
```

### 5. `shl64`

Use `add64` as template, but semantics use `UInt64.shiftLeft`.

Concrete note:
- the right operand is still a `UInt64`
- just pass it directly to `UInt64.shiftLeft`

Files/functions:

```text
VexSyntax.lean
  Expr.shl64

VexConcrete.lean
  evalExpr
    | .shl64 lhs rhs => UInt64.shiftLeft (evalExpr state temps lhs) (evalExpr state temps rhs)

VexSummary.lean
  SymExpr.shl64
  evalSymExpr
    | .shl64 lhs rhs => UInt64.shiftLeft (evalSymExpr state lhs) (evalSymExpr state rhs)
  substSymExpr
    | .shl64 lhs rhs => .shl64 (substSymExpr sub lhs) (substSymExpr sub rhs)

VexLowerCore.lean
  lowerExpr
    | .shl64 lhs rhs => .shl64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)

VexBridgeCore.lean
  lowerExpr_sound
    | shl64 lhs rhs ihL ihR =>
        simp [lowerExpr, ihL, ihR]
```

### 6. `shr64`

Use `add64` as template, but semantics use `UInt64.shiftRight`.

Files/functions:

```text
VexSyntax.lean
  Expr.shr64

VexConcrete.lean
  evalExpr
    | .shr64 lhs rhs => UInt64.shiftRight (evalExpr state temps lhs) (evalExpr state temps rhs)

VexSummary.lean
  SymExpr.shr64
  evalSymExpr
    | .shr64 lhs rhs => UInt64.shiftRight (evalSymExpr state lhs) (evalSymExpr state rhs)
  substSymExpr
    | .shr64 lhs rhs => .shr64 (substSymExpr sub lhs) (substSymExpr sub rhs)

VexLowerCore.lean
  lowerExpr
    | .shr64 lhs rhs => .shr64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)

VexBridgeCore.lean
  lowerExpr_sound
    | shr64 lhs rhs ihL ihR =>
        simp [lowerExpr, ihL, ihR]
```

## Unsigned Comparison Ops

These are the next step after the mechanical expr ops.

Recommended first pair:

```text
lt64  -- unsigned <
le64  -- unsigned <=
```

These are **not** pure expr-only grind tasks because the symbolic PC language must grow.

### Required changes

```text
Instances/ISAs/VexSyntax.lean
  Cond.ult64 : Expr Reg -> Expr Reg -> Cond Reg
  Cond.ule64 : Expr Reg -> Expr Reg -> Cond Reg

Instances/ISAs/VexConcrete.lean
  evalCond
    | .ult64 lhs rhs => decide (evalExpr state temps lhs < evalExpr state temps rhs)
    | .ule64 lhs rhs => decide (evalExpr state temps lhs <= evalExpr state temps rhs)

Instances/ISAs/VexSummary.lean
  SymPC.ult : SymExpr Reg -> SymExpr Reg -> SymPC Reg
  SymPC.ule : SymExpr Reg -> SymExpr Reg -> SymPC Reg

  evalSymPC
    | .ult lhs rhs => decide (evalSymExpr state lhs < evalSymExpr state rhs)
    | .ule lhs rhs => decide (evalSymExpr state lhs <= evalSymExpr state rhs)

  substSymPC
    | .ult lhs rhs => .ult (substSymExpr sub lhs) (substSymExpr sub rhs)
    | .ule lhs rhs => .ule (substSymExpr sub lhs) (substSymExpr sub rhs)

Instances/ISAs/VexLowerCore.lean
  lowerCond
    | .ult64 lhs rhs => .ult (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
    | .ule64 lhs rhs => .ule (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)

Instances/ISAs/VexBridgeCore.lean
  lowerCond_sound
    | .ult64 lhs rhs =>
        simp [lowerCond,
          lowerExpr_sound ... lhs,
          lowerExpr_sound ... rhs]
    | .ule64 lhs rhs =>
        simp [lowerCond,
          lowerExpr_sound ... lhs,
          lowerExpr_sound ... rhs]
```

### Notes

- This is still fairly mechanical, but it is a **PC-language extension**, not just an expression-language extension.
- Because `SemClosed` examples and refinement proofs depend on `SymPC`, this deserves more review than the pure expr ops.
- Do **unsigned** first. Signed comparisons need a separate design choice for signed interpretation of `UInt64`.

## Load8 + Byte-Width Path (Needs Review)

Do **not** hand this out as a blind grind task yet.

This is likely the real prerequisite for realistic parser binaries.

### What likely needs to happen

```text
VexSyntax.lean
  Expr.load8 : Expr Reg -> Expr Reg
  possibly width-extension ops:
    narrow8 / zext8to64
    or a more general width representation

VexConcrete.lean
  ByteMem.readByte is already present
  evalExpr
    | .load8 addr => UInt64.ofNat ((ByteMem.readByte state.mem (evalExpr state temps addr)).toNat)

VexSummary.lean
  SymExpr.load8 : SymMem Reg -> SymExpr Reg -> SymExpr Reg
  evalSymExpr
    | .load8 mem addr => UInt64.ofNat ((ByteMem.readByte (evalSymMem state mem) (evalSymExpr state addr)).toNat)
  substSymExpr
    | .load8 mem addr => .load8 (substSymMem sub mem) (substSymExpr sub addr)

VexLowerCore.lean
  lowerExpr
    | .load8 addr => .load8 sub.mem (lowerExpr sub temps addr)

VexBridgeCore.lean
  lowerExpr_sound
    | load8 addr ih => ...
```

### Why this needs review

- Width design is currently ad hoc (`narrow32`, `zext64`, `add32`).
- A realistic byte path wants:
  - `load8`
  - zero-extension to 64
  - comparison against byte-sized constants
- This is the point where you should decide whether to:
  - keep adding one-off width constructors, or
  - introduce a more uniform width story

Recommendation:
- do not grind this in parallel until the width design is reviewed

## Minimal Useful Set for a Real x86-64 Parser Loop

If the target is a simple byte-matching dispatch loop in a real binary, the priority order is:

```text
1. and64
2. sub64
3. unsigned comparisons (ult64, ule64)
4. load8 + byte-width path
```

Why:
- `and64` is common for masking and cheap byte extraction patterns
- `sub64` is common for pointer/length arithmetic
- unsigned `<`/`<=` are common for bounds checks
- byte loads are the real missing parser primitive

Lower priority for parser-like code:

```text
xor64
or64
shl64
shr64
signed comparisons
```

## Commit Structure

Recommended grouping:

### Mechanical expr ops

Best default:

```text
one commit per op
```

Reason:
- easy review
- easy revert
- parallel-friendly
- low merge ambiguity

Alternative if one agent is doing a single batch:

```text
group by family:
  commit 1: sub64 + xor64
  commit 2: and64 + or64
  commit 3: shl64 + shr64
```

That is acceptable, but only if each commit stays green independently.

### Unsigned comparisons

Recommended:

```text
one commit for lt64 + le64 together
```

Reason:
- both touch the same `SymPC` / `lowerCond_sound` area
- batching them avoids repeated churn in the same files

### Byte-width path

Do not batch this with the above.

Recommended:

```text
separate design/review pass first
then one or more dedicated commits
```

## Fresh Codex Task Template

For a fresh Codex instance assigned one mechanical op:

```text
Goal:
  Add <OP> to the VEX core.

Files to edit:
  Instances/ISAs/VexSyntax.lean
  Instances/ISAs/VexConcrete.lean
  Instances/ISAs/VexSummary.lean
  Instances/ISAs/VexLowerCore.lean
  Instances/ISAs/VexBridgeCore.lean

Pattern:
  Follow add64 exactly, replacing the operator semantics appropriately.

Do not touch:
  Quotient/Refinement/VexWitness/example files unless the build forces it.

Validation:
  lake build
  lake build 2>&1 | rg "warning:"

Commit:
  one atomic commit for <OP>
```

For unsigned comparisons:

```text
Goal:
  Add ult64 and ule64 to the VEX condition and symbolic-PC core.

Files to edit:
  Instances/ISAs/VexSyntax.lean
  Instances/ISAs/VexConcrete.lean
  Instances/ISAs/VexSummary.lean
  Instances/ISAs/VexLowerCore.lean
  Instances/ISAs/VexBridgeCore.lean

Pattern:
  Follow eq64 as the condition-level template, but extend SymPC with ult/ule.

Validation:
  lake build
  lake build 2>&1 | rg "warning:"
```

