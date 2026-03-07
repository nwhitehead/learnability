import SymExec.Bisimulation
import Mathlib.Data.Fintype.Pi

/-!
# MachineISA — Concrete Symbolic ISA Instance

A concrete `SymbolicISA` over flat-state bitvector machines, grounding the
framework in a real-ish instruction set architecture.

- `MState n w := Fin n → BitVec w` — n locations, w-bit words
- `MSub n w := Fin n → MExpr n w` — symbolic expressions per location
- `MPC n w := MBool n w` — boolean expressions as path conditions

Expression language aligned with SMT-LIB QF_BV: arithmetic, bitwise, shifts,
comparisons, boolean connectives. Conditionals (`ite`) are NOT in the expression
language — they are handled at the `CompTree` level (Phase 7) via
`choice (seq (assert φ) t₁) (seq (assert (pc_not φ)) t₂)`, matching ICTAC's
program-level nondeterministic choice.

## ICTAC Correspondence

| MachineISA | ICTAC |
|---|---|
| `MExpr` | `Aexpr` |
| `MBool` | `Bexpr` |
| `MSub` | `sub = string → Aexpr` |
| `MState` | `Valuation = string → nat` |
| `evalExpr` | `Aeval` |
| `evalBool` | `Beval` |
| `substExpr` | `Aapply` |
| `substBool` | `Bapply` |
| `composeSub` | `compose_subs` |
| `evalSub` | `denot_sub` / `Comp` |
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MachineISA

/-! ## Expression Types -/

/-- Bitvector expressions over `n` locations with `w`-bit words.
    Each location is addressed by `Fin n`; expressions evaluate to `BitVec w`. -/
inductive MExpr (n : Nat) (w : Nat) : Type where
  | loc : Fin n → MExpr n w
  | lit : BitVec w → MExpr n w
  | add : MExpr n w → MExpr n w → MExpr n w
  | bvsub : MExpr n w → MExpr n w → MExpr n w
  | mul : MExpr n w → MExpr n w → MExpr n w
  | udiv : MExpr n w → MExpr n w → MExpr n w
  | urem : MExpr n w → MExpr n w → MExpr n w
  | bvand : MExpr n w → MExpr n w → MExpr n w
  | bvor : MExpr n w → MExpr n w → MExpr n w
  | bvxor : MExpr n w → MExpr n w → MExpr n w
  | shl : MExpr n w → MExpr n w → MExpr n w
  | shr : MExpr n w → MExpr n w → MExpr n w
  deriving DecidableEq

/-- Boolean expressions over bitvector expressions.
    Evaluate to `Bool`; used as path conditions. Not mutually recursive
    with `MExpr` — boolean operators don't appear inside arithmetic
    expressions. Conditionals are handled at the `CompTree` level. -/
inductive MBool (n : Nat) (w : Nat) : Type where
  | eq : MExpr n w → MExpr n w → MBool n w
  | ult : MExpr n w → MExpr n w → MBool n w
  | ule : MExpr n w → MExpr n w → MBool n w
  | slt : MExpr n w → MExpr n w → MBool n w
  | sle : MExpr n w → MExpr n w → MBool n w
  | mand : MBool n w → MBool n w → MBool n w
  | mor : MBool n w → MBool n w → MBool n w
  | mnot : MBool n w → MBool n w
  | mtrue : MBool n w
  | mfalse : MBool n w
  deriving DecidableEq

/-! ## Derived Types -/

abbrev MSub (n : Nat) (w : Nat) := Fin n → MExpr n w
abbrev MPC (n : Nat) (w : Nat) := MBool n w
abbrev MState (n : Nat) (w : Nat) := Fin n → BitVec w

/-! ## Evaluation -/

variable {n w : Nat}

/-- Evaluate an expression in a concrete state. ICTAC: `Aeval`. -/
def evalExpr (e : MExpr n w) (s : MState n w) : BitVec w :=
  match e with
  | .loc i => s i
  | .lit v => v
  | .add e₁ e₂ => evalExpr e₁ s + evalExpr e₂ s
  | .bvsub e₁ e₂ => evalExpr e₁ s - evalExpr e₂ s
  | .mul e₁ e₂ => evalExpr e₁ s * evalExpr e₂ s
  | .udiv e₁ e₂ => evalExpr e₁ s / evalExpr e₂ s
  | .urem e₁ e₂ => evalExpr e₁ s % evalExpr e₂ s
  | .bvand e₁ e₂ => evalExpr e₁ s &&& evalExpr e₂ s
  | .bvor e₁ e₂ => evalExpr e₁ s ||| evalExpr e₂ s
  | .bvxor e₁ e₂ => evalExpr e₁ s ^^^ evalExpr e₂ s
  | .shl e₁ e₂ => evalExpr e₁ s <<< (evalExpr e₂ s).toNat
  | .shr e₁ e₂ => evalExpr e₁ s >>> (evalExpr e₂ s).toNat

/-- Evaluate a boolean expression in a concrete state. ICTAC: `Beval`. -/
def evalBool (b : MBool n w) (s : MState n w) : Bool :=
  match b with
  | .eq e₁ e₂ => evalExpr e₁ s == evalExpr e₂ s
  | .ult e₁ e₂ => decide (evalExpr e₁ s < evalExpr e₂ s)
  | .ule e₁ e₂ => decide (evalExpr e₁ s ≤ evalExpr e₂ s)
  | .slt e₁ e₂ => decide (BitVec.slt (evalExpr e₁ s) (evalExpr e₂ s))
  | .sle e₁ e₂ => decide (BitVec.sle (evalExpr e₁ s) (evalExpr e₂ s))
  | .mand b₁ b₂ => evalBool b₁ s && evalBool b₂ s
  | .mor b₁ b₂ => evalBool b₁ s || evalBool b₂ s
  | .mnot b' => !evalBool b' s
  | .mtrue => true
  | .mfalse => false

/-- Evaluate a substitution on a concrete state. ICTAC: `denot_sub` / `Comp`. -/
def evalSub (σ : MSub n w) (s : MState n w) : MState n w :=
  fun i => evalExpr (σ i) s

/-! ## Syntactic Substitution

`substExpr σ e` replaces each `loc i` in `e` with `σ i`.
ICTAC: `Aapply`. This is the key operation connecting syntactic
composition of substitutions with semantic evaluation. -/

/-- Apply a substitution to an expression: replace `loc i` with `σ i`.
    ICTAC: `Aapply`. -/
def substExpr (σ : MSub n w) : MExpr n w → MExpr n w
  | .loc i => σ i
  | .lit v => .lit v
  | .add e₁ e₂ => .add (substExpr σ e₁) (substExpr σ e₂)
  | .bvsub e₁ e₂ => .bvsub (substExpr σ e₁) (substExpr σ e₂)
  | .mul e₁ e₂ => .mul (substExpr σ e₁) (substExpr σ e₂)
  | .udiv e₁ e₂ => .udiv (substExpr σ e₁) (substExpr σ e₂)
  | .urem e₁ e₂ => .urem (substExpr σ e₁) (substExpr σ e₂)
  | .bvand e₁ e₂ => .bvand (substExpr σ e₁) (substExpr σ e₂)
  | .bvor e₁ e₂ => .bvor (substExpr σ e₁) (substExpr σ e₂)
  | .bvxor e₁ e₂ => .bvxor (substExpr σ e₁) (substExpr σ e₂)
  | .shl e₁ e₂ => .shl (substExpr σ e₁) (substExpr σ e₂)
  | .shr e₁ e₂ => .shr (substExpr σ e₁) (substExpr σ e₂)

/-- Apply a substitution to a boolean expression.
    ICTAC: `Bapply`. -/
def substBool (σ : MSub n w) : MBool n w → MBool n w
  | .eq e₁ e₂ => .eq (substExpr σ e₁) (substExpr σ e₂)
  | .ult e₁ e₂ => .ult (substExpr σ e₁) (substExpr σ e₂)
  | .ule e₁ e₂ => .ule (substExpr σ e₁) (substExpr σ e₂)
  | .slt e₁ e₂ => .slt (substExpr σ e₁) (substExpr σ e₂)
  | .sle e₁ e₂ => .sle (substExpr σ e₁) (substExpr σ e₂)
  | .mand b₁ b₂ => .mand (substBool σ b₁) (substBool σ b₂)
  | .mor b₁ b₂ => .mor (substBool σ b₁) (substBool σ b₂)
  | .mnot b' => .mnot (substBool σ b')
  | .mtrue => .mtrue
  | .mfalse => .mfalse

/-! ## Composition -/

/-- Identity substitution: each location maps to itself. ICTAC: `id_sub`. -/
def idSub : MSub n w := fun i => .loc i

/-- Compose substitutions syntactically. ICTAC: `compose_subs`.
    `composeSub σ₁ σ₂` means "apply σ₁ first, then σ₂":
    semantically `evalSub (composeSub σ₁ σ₂) s = evalSub σ₂ (evalSub σ₁ s)`.
    Syntactically: substitute σ₁ into each expression of σ₂. -/
def composeSub (σ₁ σ₂ : MSub n w) : MSub n w :=
  fun i => substExpr σ₁ (σ₂ i)

/-- Lift a path condition through a substitution. ICTAC: `Bapply`. -/
def liftPC (σ : MSub n w) (φ : MPC n w) : MPC n w :=
  substBool σ φ

/-! ## Key Lemmas

The algebraic laws required by `SymbolicISA`, proved via structural
induction on expressions. -/

/-- Substitution commutes with evaluation (the fundamental lemma).
    ICTAC: `comp_sub` — `Aeval (Comp V s) e = Aeval V (Aapply s e)`. -/
theorem evalExpr_subst (σ : MSub n w) (e : MExpr n w) (s : MState n w) :
    evalExpr (substExpr σ e) s = evalExpr e (evalSub σ s) := by
  induction e with
  | loc i => simp [substExpr, evalExpr, evalSub]
  | lit v => simp [substExpr, evalExpr]
  | add e₁ e₂ ih₁ ih₂ => simp [substExpr, evalExpr, ih₁, ih₂]
  | bvsub e₁ e₂ ih₁ ih₂ => simp [substExpr, evalExpr, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp [substExpr, evalExpr, ih₁, ih₂]
  | udiv e₁ e₂ ih₁ ih₂ => simp [substExpr, evalExpr, ih₁, ih₂]
  | urem e₁ e₂ ih₁ ih₂ => simp [substExpr, evalExpr, ih₁, ih₂]
  | bvand e₁ e₂ ih₁ ih₂ => simp [substExpr, evalExpr, ih₁, ih₂]
  | bvor e₁ e₂ ih₁ ih₂ => simp [substExpr, evalExpr, ih₁, ih₂]
  | bvxor e₁ e₂ ih₁ ih₂ => simp [substExpr, evalExpr, ih₁, ih₂]
  | shl e₁ e₂ ih₁ ih₂ => simp [substExpr, evalExpr, ih₁, ih₂]
  | shr e₁ e₂ ih₁ ih₂ => simp [substExpr, evalExpr, ih₁, ih₂]

/-- Boolean substitution commutes with evaluation.
    ICTAC: `comp_subB`. -/
theorem evalBool_subst (σ : MSub n w) (b : MBool n w) (s : MState n w) :
    evalBool (substBool σ b) s = evalBool b (evalSub σ s) := by
  induction b with
  | eq e₁ e₂ => simp [substBool, evalBool, evalExpr_subst]
  | ult e₁ e₂ => simp [substBool, evalBool, evalExpr_subst]
  | ule e₁ e₂ => simp [substBool, evalBool, evalExpr_subst]
  | slt e₁ e₂ => simp [substBool, evalBool, evalExpr_subst]
  | sle e₁ e₂ => simp [substBool, evalBool, evalExpr_subst]
  | mand b₁ b₂ ih₁ ih₂ => simp [substBool, evalBool, ih₁, ih₂]
  | mor b₁ b₂ ih₁ ih₂ => simp [substBool, evalBool, ih₁, ih₂]
  | mnot b' ih => simp [substBool, evalBool, ih]
  | mtrue => simp [substBool, evalBool]
  | mfalse => simp [substBool, evalBool]

/-- Identity substitution is syntactic identity on expressions. -/
theorem substExpr_id (e : MExpr n w) :
    substExpr idSub e = e := by
  induction e with
  | loc i => simp [substExpr, idSub]
  | lit v => simp [substExpr]
  | add _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | bvsub _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | udiv _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | urem _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | bvand _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | bvor _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | bvxor _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | shl _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | shr _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]

/-- Substitution distributes over composition: `substExpr` is functorial.
    ICTAC: `Aapply_compose`. -/
theorem substExpr_compose (σ₁ σ₂ : MSub n w) (e : MExpr n w) :
    substExpr (composeSub σ₁ σ₂) e = substExpr σ₁ (substExpr σ₂ e) := by
  induction e with
  | loc i => simp [substExpr, composeSub]
  | lit v => simp [substExpr]
  | add _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | bvsub _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | udiv _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | urem _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | bvand _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | bvor _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | bvxor _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | shl _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]
  | shr _ _ ih₁ ih₂ => simp [substExpr, ih₁, ih₂]

/-- Boolean substitution distributes over composition. -/
theorem substBool_compose (σ₁ σ₂ : MSub n w) (b : MBool n w) :
    substBool (composeSub σ₁ σ₂) b = substBool σ₁ (substBool σ₂ b) := by
  induction b with
  | eq e₁ e₂ => simp [substBool, substExpr_compose]
  | ult e₁ e₂ => simp [substBool, substExpr_compose]
  | ule e₁ e₂ => simp [substBool, substExpr_compose]
  | slt e₁ e₂ => simp [substBool, substExpr_compose]
  | sle e₁ e₂ => simp [substBool, substExpr_compose]
  | mand _ _ ih₁ ih₂ => simp [substBool, ih₁, ih₂]
  | mor _ _ ih₁ ih₂ => simp [substBool, ih₁, ih₂]
  | mnot _ ih => simp [substBool, ih]
  | mtrue => simp [substBool]
  | mfalse => simp [substBool]

/-! ## SymbolicISA Instance -/

/-- The machine ISA: bitvector symbolic execution algebra.
    Satisfies all `SymbolicISA` axioms. -/
def machineISA (n : Nat) (w : Nat) : SymbolicISA (MSub n w) (MPC n w) (MState n w) where
  id_sub := idSub
  compose_sub := composeSub
  eval_sub := evalSub
  pc_true := .mtrue
  pc_and := .mand
  pc_lift := liftPC
  satisfies := fun s φ => evalBool φ s = true
  pc_not := .mnot
  eval_compose := by
    intro σ₁ σ₂ s
    funext i
    simp [evalSub, composeSub, evalExpr_subst]
  eval_id := by
    intro s
    funext i
    simp [evalSub, idSub, evalExpr]
  compose_id_left := by
    intro σ
    funext i
    simp [composeSub, substExpr_id]
  compose_id_right := by
    intro σ
    funext i
    simp [composeSub, substExpr, idSub]
  compose_assoc := by
    intro σ₁ σ₂ σ₃
    funext i
    simp [composeSub, substExpr_compose]
  sat_true := by
    intro s
    simp [evalBool]
  sat_and := by
    intro s φ₁ φ₂
    simp [evalBool, Bool.and_eq_true]
  sat_lift := by
    intro s σ φ
    simp [liftPC, evalBool_subst]
  sat_not := by
    intro s φ
    show (!evalBool φ s) = true ↔ ¬ (evalBool φ s = true)
    cases evalBool φ s <;> simp

/-! ## Smoke Test

A 1-location, 1-bit toggle program through the Phase 1-3 pipeline.
- State space: `Fin 1 → BitVec 1` ≅ `{0, 1}`
- Behavior: 0 → 1, 1 → 0
- Two branches: one for each direction
- Oracle converges to bisimilar model in 2 steps -/

section SmokeTest

abbrev SmSub := MSub 1 1
abbrev SmPC := MPC 1 1
abbrev SmState := MState 1 1

/-- The machine ISA specialized to 1-location 1-bit. -/
abbrev smISA := machineISA 1 1

/-- Toggle behavior: the single bit flips. -/
def smBehavior (s s' : SmState) : Prop :=
  s' 0 = s 0 ^^^ 1

/-- Branch A: when bit is 0, set to 1.
    sub: loc[0] ↦ lit 1
    pc: loc[0] = 0 -/
def smBranchA : Branch SmSub SmPC where
  sub := fun _ => .lit 1
  pc := .eq (.loc 0) (.lit 0)

/-- Branch B: when bit is 1, set to 0.
    sub: loc[0] ↦ lit 0
    pc: loc[0] = 1 -/
def smBranchB : Branch SmSub SmPC where
  sub := fun _ => .lit 0
  pc := .eq (.loc 0) (.lit 1)

def smTarget : Finset (Branch SmSub SmPC) := {smBranchA, smBranchB}

/-- Helper: the only element of `Fin 1` is `0`. -/
private theorem fin1_eq_zero (i : Fin 1) : i = 0 := by ext; omega

/-- Helper: `BitVec 1` has exactly two values: 0 and 1. -/
private theorem bv1_cases (v : BitVec 1) : v = 0 ∨ v = 1 := by
  have h : v.toNat < 2 ^ 1 := v.isLt
  have : v.toNat = 0 ∨ v.toNat = 1 := by omega
  rcases this with h | h
  · left; exact BitVec.eq_of_toNat_eq h
  · right; exact BitVec.eq_of_toNat_eq h

/-- Helper: state is determined by its value at 0. -/
private theorem smState_ext {s₁ s₂ : SmState} (h : s₁ 0 = s₂ 0) : s₁ = s₂ := by
  funext i; rw [fin1_eq_zero i]; exact h

theorem smTarget_sound :
    BranchModel.Sound smISA (↑smTarget : Set (Branch SmSub SmPC)) smBehavior := by
  intro b hb s hsat
  have hmem := Finset.mem_coe.mp hb
  rw [smTarget, Finset.mem_insert] at hmem
  rcases hmem with rfl | hmem
  · -- Branch A: pc says s(0) = 0, sub maps to 1
    change evalBool smBranchA.pc s = true at hsat
    simp only [smBranchA, evalBool, evalExpr, beq_iff_eq] at hsat
    change smBehavior s (evalSub smBranchA.sub s)
    simp only [smBehavior, evalSub, evalExpr, smBranchA, hsat]
    decide
  · -- Branch B: pc says s(0) = 1, sub maps to 0
    rw [Finset.mem_singleton] at hmem; subst hmem
    change evalBool smBranchB.pc s = true at hsat
    simp only [smBranchB, evalBool, evalExpr, beq_iff_eq] at hsat
    change smBehavior s (evalSub smBranchB.sub s)
    simp only [smBehavior, evalSub, evalExpr, smBranchB, hsat]
    decide

theorem smTarget_complete :
    BranchModel.Complete smISA (↑smTarget : Set (Branch SmSub SmPC)) smBehavior := by
  intro s s' hbeh
  simp only [smBehavior] at hbeh
  rcases bv1_cases (s 0) with h0 | h1
  · -- s(0) = 0 → branch A fires
    refine ⟨smBranchA, ?_, ?_, ?_⟩
    · exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
    · change evalBool smBranchA.pc s = true
      simp [smBranchA, evalBool, evalExpr, h0]
    · change evalSub smBranchA.sub s = s'
      apply smState_ext
      simp only [evalSub, smBranchA, evalExpr]
      rw [hbeh, h0]; decide
  · -- s(0) = 1 → branch B fires
    refine ⟨smBranchB, ?_, ?_, ?_⟩
    · exact Finset.mem_coe.mpr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
    · change evalBool smBranchB.pc s = true
      simp [smBranchB, evalBool, evalExpr, h1]
    · change evalSub smBranchB.sub s = s'
      apply smState_ext
      simp only [evalSub, smBranchB, evalExpr]
      rw [hbeh, h1]; decide

/-- The oracle: returns branch A first, then branch B, then stops. -/
def smQuery (model : Finset (Branch SmSub SmPC)) : Option (Branch SmSub SmPC) :=
  if smBranchA ∉ model then some smBranchA
  else if smBranchB ∉ model then some smBranchB
  else none

theorem smQuery_sound (model : Finset (Branch SmSub SmPC)) (b : Branch SmSub SmPC)
    (hq : smQuery model = some b) :
    ∀ (s : SmState), smISA.satisfies s b.pc → smBehavior s (smISA.eval_sub b.sub s) := by
  unfold smQuery at hq
  split at hq
  · obtain rfl := Option.some_injective _ hq
    intro s hsat
    change evalBool smBranchA.pc s = true at hsat
    simp only [smBranchA, evalBool, evalExpr, beq_iff_eq] at hsat
    change smBehavior s (evalSub smBranchA.sub s)
    simp only [smBehavior, evalSub, evalExpr, smBranchA, hsat]
    decide
  · split at hq
    · obtain rfl := Option.some_injective _ hq
      intro s hsat
      change evalBool smBranchB.pc s = true at hsat
      simp only [smBranchB, evalBool, evalExpr, beq_iff_eq] at hsat
      change smBehavior s (evalSub smBranchB.sub s)
      simp only [smBehavior, evalSub, evalExpr, smBranchB, hsat]
      decide
    · simp at hq

theorem smQuery_new (model : Finset (Branch SmSub SmPC)) (b : Branch SmSub SmPC)
    (hq : smQuery model = some b) : b ∉ model := by
  unfold smQuery at hq
  split at hq
  case isTrue h => exact Option.some_injective _ hq ▸ h
  case isFalse =>
    split at hq
    case isTrue h => exact Option.some_injective _ hq ▸ h
    case isFalse => simp at hq

def smOracle : BranchOracle SmSub SmPC SmState where
  isa := smISA
  behavior := smBehavior
  query := smQuery
  query_sound := smQuery_sound
  query_new := smQuery_new

theorem smOracle_productive : smOracle.Productive smTarget := by
  intro model h_sub h_ne
  show ∃ b, smQuery model = some b
  unfold smQuery
  by_contra h_none
  push_neg at h_none
  have h1 : smBranchA ∈ model := by
    by_contra h; exact absurd (h_none smBranchA (by simp [h])) (by simp)
  have h2 : smBranchB ∈ model := by
    by_contra h; exact absurd (h_none smBranchB (by simp [h, h1])) (by simp)
  exact h_ne (Finset.Subset.antisymm h_sub (by
    intro x hx; simp [smTarget] at hx; rcases hx with rfl | rfl <;> assumption))

theorem smOracle_bounded : smOracle.TargetBounded smTarget := by
  intro model b hq
  change smQuery model = some b at hq
  unfold smQuery at hq
  split at hq
  · exact Option.some_injective _ hq ▸ (by simp [smTarget])
  · split at hq
    · exact Option.some_injective _ hq ▸ (by simp [smTarget])
    · simp at hq

/-- End-to-end: the MachineISA oracle converges to a bisimilar model. -/
theorem smOracle_converges_bisimilar :
    ∃ n, n ≤ smTarget.card ∧
      Bisimilar
        (branchBehavior smISA (↑(oracleSequence smOracle n) : Set (Branch SmSub SmPC)))
        smBehavior :=
  branchAccumulation_bisimilar smOracle smTarget
    smOracle_productive smOracle_bounded smTarget_complete

end SmokeTest

end MachineISA
