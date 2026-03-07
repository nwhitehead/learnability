import Mathlib.Logic.Basic

/-!
# Symbolic ISA

Structure abstracting the algebraic structure of symbolic execution,
ported from the ICTAC-DenotSymbEx Coq mechanization.

The concrete ICTAC development uses:
- `sub = string → Aexpr` (substitutions)
- `Bexpr` (boolean expressions as path conditions)
- `Valuation = string → nat` (concrete states)

We abstract this into a structure parameterized by `Sub`, `PC`, `State`,
with the ICTAC composition laws as fields. This lets the same framework
apply to bitvector substitutions (KLEE), the ICTAC concrete types, or
any future ISA.

## ICTAC Provenance

Each law corresponds to a proved lemma in the Coq mechanization:

| Law | ICTAC source | Coq lemma |
|---|---|---|
| `eval_compose` | Maps.v | `compose_comp` |
| `eval_id` | Maps.v | `comp_id` |
| `compose_id_left` | Maps.v | `compose_subs_id` |
| `compose_id_right` | Maps.v | `compose_subs_id'` |
| `compose_assoc` | Maps.v | `compose_subs_assoc` |
| `sat_true` | (trivial) | — |
| `sat_and` | Maps.v | `denotB_and` + `andb_true_iff` |
| `sat_lift` | Programs.v | `inverse_denotB` |
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Algebraic structure of symbolic execution over an instruction set architecture.

    Abstracts the substitution/path-condition algebra from ICTAC-DenotSymbEx.
    Substitutions form a monoid under `compose_sub` with identity `id_sub`.
    Path conditions form a bounded semilattice under `pc_and` with top `pc_true`.
    `pc_lift` connects the two: lifting a PC through a substitution corresponds
    to ICTAC's `Bapply`. -/
structure SymbolicISA (Sub : Type*) (PC : Type*) (State : Type*) where
  /-- Identity substitution (no state change). ICTAC: `id_sub`. -/
  id_sub : Sub
  /-- Sequential composition of substitutions. ICTAC: `compose_subs`.
      `compose_sub σ₁ σ₂` means "apply σ₁ first, then σ₂". -/
  compose_sub : Sub → Sub → Sub
  /-- Evaluate a substitution on a concrete state. ICTAC: `denot_sub`. -/
  eval_sub : Sub → State → State
  /-- Trivially true path condition. ICTAC: `BTrue`. -/
  pc_true : PC
  /-- Conjunction of path conditions. ICTAC: `BAnd`. -/
  pc_and : PC → PC → PC
  /-- Lift a path condition through a substitution.
      `pc_lift σ φ` is the condition that holds of state `s` iff
      `φ` holds of `eval_sub σ s`. ICTAC: `Bapply`. -/
  pc_lift : Sub → PC → PC
  /-- State satisfies a path condition. ICTAC: `V |= b`. -/
  satisfies : State → PC → Prop
  /-- Evaluating composed substitutions = evaluating sequentially.
      ICTAC: `compose_comp` — `Comp V (compose_subs s s') = Comp (Comp V s) s'`. -/
  eval_compose : ∀ (σ₁ σ₂ : Sub) (s : State),
    eval_sub (compose_sub σ₁ σ₂) s = eval_sub σ₂ (eval_sub σ₁ s)
  /-- Identity substitution is identity on states.
      ICTAC: `comp_id` — `Comp V id_sub = V`. -/
  eval_id : ∀ (s : State), eval_sub id_sub s = s
  /-- `id_sub` is left identity for composition.
      ICTAC: `compose_subs_id`. -/
  compose_id_left : ∀ (σ : Sub), compose_sub id_sub σ = σ
  /-- `id_sub` is right identity for composition.
      ICTAC: `compose_subs_id'`. -/
  compose_id_right : ∀ (σ : Sub), compose_sub σ id_sub = σ
  /-- Composition is associative.
      ICTAC: `compose_subs_assoc`. -/
  compose_assoc : ∀ (σ₁ σ₂ σ₃ : Sub),
    compose_sub σ₁ (compose_sub σ₂ σ₃) = compose_sub (compose_sub σ₁ σ₂) σ₃
  /-- Every state satisfies the trivially true PC.
      Follows from `Beval V BTrue = true`. -/
  sat_true : ∀ (s : State), satisfies s pc_true
  /-- Conjunction of PCs corresponds to conjunction of satisfaction.
      ICTAC: `denotB_and` + `andb_true_iff`. -/
  sat_and : ∀ (s : State) (φ₁ φ₂ : PC),
    satisfies s (pc_and φ₁ φ₂) ↔ satisfies s φ₁ ∧ satisfies s φ₂
  /-- Lifting a PC through a substitution = pre-composing with eval.
      ICTAC: `inverse_denotB` —
      `denot__B (Bapply s b) = inverse_image (denot_sub s) (denot__B b)`.
      This is the key law connecting substitutions and path conditions. -/
  sat_lift : ∀ (s : State) (σ : Sub) (φ : PC),
    satisfies s (pc_lift σ φ) ↔ satisfies (eval_sub σ s) φ
  /-- Negation of a path condition. ICTAC: `BNot`. -/
  pc_not : PC → PC
  /-- Negation semantics: `satisfies s (pc_not φ) ↔ ¬ satisfies s φ`. -/
  sat_not : ∀ (s : State) (φ : PC),
    satisfies s (pc_not φ) ↔ ¬ satisfies s φ

section SymbolicISA_lemmas

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- Lifting through identity preserves the PC's semantics. -/
theorem sat_lift_id (s : State) (φ : PC) :
    isa.satisfies s (isa.pc_lift isa.id_sub φ) ↔ isa.satisfies s φ := by
  constructor
  · intro h
    have h' := (isa.sat_lift s isa.id_sub φ).mp h
    rw [isa.eval_id] at h'
    exact h'
  · intro h
    apply (isa.sat_lift s isa.id_sub φ).mpr
    rw [isa.eval_id]
    exact h

/-- Lifting through composed substitutions = lifting twice.
    Functoriality of `pc_lift` over the substitution monoid. -/
theorem sat_lift_compose (s : State) (σ₁ σ₂ : Sub) (φ : PC) :
    isa.satisfies s (isa.pc_lift (isa.compose_sub σ₁ σ₂) φ) ↔
    isa.satisfies s (isa.pc_lift σ₁ (isa.pc_lift σ₂ φ)) := by
  constructor
  · intro h
    have := (isa.sat_lift s (isa.compose_sub σ₁ σ₂) φ).mp h
    rw [isa.eval_compose] at this
    exact (isa.sat_lift s σ₁ (isa.pc_lift σ₂ φ)).mpr
      ((isa.sat_lift (isa.eval_sub σ₁ s) σ₂ φ).mpr this)
  · intro h
    have := (isa.sat_lift s σ₁ (isa.pc_lift σ₂ φ)).mp h
    have := (isa.sat_lift (isa.eval_sub σ₁ s) σ₂ φ).mp this
    rw [← isa.eval_compose] at this
    exact (isa.sat_lift s (isa.compose_sub σ₁ σ₂) φ).mpr this

end SymbolicISA_lemmas
