import Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Pi

/-!
# Concrete SymbolicISA Instance — Satisfiability Witness

A minimal concrete instance demonstrating that the SymbolicISA axioms,
BranchOracle constraints, and end-to-end convergence hypotheses are
jointly satisfiable.

## The instance

- `State := Fin 3` (3 states: 0, 1, 2)
- `Sub := Fin 3 → Fin 3` (substitutions are endofunctions)
- `PC := Fin 3 → Bool` (path conditions are boolean predicates)

Substitution composition is function composition. Path condition conjunction
is pointwise `&&`. Lifting is precomposition. This is the "standard model" —
the free SymbolicISA on a finite set.

## The system

Two transitions: 0 → 1 and 1 → 2.

Two branches cover this:
- Branch A: sub maps 0↦1 (identity elsewhere), pc = "state is 0"
- Branch B: sub maps 1↦2 (identity elsewhere), pc = "state is 1"

The oracle returns A first, then B, then stops.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## Concrete types -/

abbrev ExSub := Fin 3 → Fin 3
abbrev ExPC := Fin 3 → Bool
abbrev ExState := Fin 3

/-! ## The SymbolicISA instance -/

def exISA : SymbolicISA ExSub ExPC ExState where
  id_sub := id
  compose_sub := fun σ₁ σ₂ => σ₂ ∘ σ₁
  eval_sub := fun σ s => σ s
  pc_true := fun _ => true
  pc_and := fun φ₁ φ₂ s => φ₁ s && φ₂ s
  pc_lift := fun σ φ s => φ (σ s)
  satisfies := fun s φ => φ s = true
  eval_compose := fun _ _ _ => rfl
  eval_id := fun _ => rfl
  compose_id_left := fun _ => rfl
  compose_id_right := fun _ => rfl
  compose_assoc := fun _ _ _ => rfl
  sat_true := fun _ => rfl
  sat_and := fun s φ₁ φ₂ => by
    show (φ₁ s && φ₂ s) = true ↔ φ₁ s = true ∧ φ₂ s = true
    rw [Bool.and_eq_true]
  sat_lift := fun _ _ _ => Iff.rfl

/-! ## The toy system -/

def exBehavior : ExState → ExState → Prop
  | ⟨0, _⟩, s' => s' = (1 : Fin 3)
  | ⟨1, _⟩, s' => s' = (2 : Fin 3)
  | _, _ => False

def branchA : Branch ExSub ExPC where
  sub := fun s => if s = (0 : Fin 3) then (1 : Fin 3) else s
  pc := fun s => s == (0 : Fin 3)

def branchB : Branch ExSub ExPC where
  sub := fun s => if s = (1 : Fin 3) then (2 : Fin 3) else s
  pc := fun s => s == (1 : Fin 3)

/-! ## Soundness and completeness of the target -/

def exTarget : Finset (Branch ExSub ExPC) := {branchA, branchB}

theorem exTarget_sound :
    BranchModel.Sound exISA (↑exTarget : Set (Branch ExSub ExPC)) exBehavior := by
  intro b hb s hsat
  simp only [exTarget, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl
  · simp only [branchA, exISA, beq_iff_eq] at hsat
    subst hsat
    simp [exBehavior, branchA, exISA]
  · simp only [branchB, exISA, beq_iff_eq] at hsat
    subst hsat
    simp [exBehavior, branchB, exISA]

theorem exTarget_complete :
    BranchModel.Complete exISA (↑exTarget : Set (Branch ExSub ExPC)) exBehavior := by
  intro s s' hbeh
  fin_cases s <;> simp only [exBehavior] at hbeh
  · subst hbeh
    exact ⟨branchA,
      by simp [exTarget],
      by simp [branchA, exISA],
      by simp [branchA, exISA]⟩
  · subst hbeh
    exact ⟨branchB,
      by simp [exTarget],
      by simp [branchB, exISA],
      by simp [branchB, exISA]⟩

/-! ## The oracle -/

def exQuery (model : Finset (Branch ExSub ExPC)) : Option (Branch ExSub ExPC) :=
  if branchA ∉ model then some branchA
  else if branchB ∉ model then some branchB
  else none

theorem exQuery_sound (model : Finset (Branch ExSub ExPC)) (b : Branch ExSub ExPC)
    (hq : exQuery model = some b) :
    ∀ (s : ExState), exISA.satisfies s b.pc → exBehavior s (exISA.eval_sub b.sub s) := by
  unfold exQuery at hq
  split at hq
  · obtain rfl := Option.some_injective _ hq
    intro s hsat
    simp only [branchA, exISA, beq_iff_eq] at hsat
    subst hsat; simp [exBehavior, branchA, exISA]
  · split at hq
    · obtain rfl := Option.some_injective _ hq
      intro s hsat
      simp only [branchB, exISA, beq_iff_eq] at hsat
      subst hsat; simp [exBehavior, branchB, exISA]
    · simp at hq

theorem exQuery_new (model : Finset (Branch ExSub ExPC)) (b : Branch ExSub ExPC)
    (hq : exQuery model = some b) : b ∉ model := by
  unfold exQuery at hq
  split at hq
  case isTrue h => exact Option.some_injective _ hq ▸ h
  case isFalse =>
    split at hq
    case isTrue h => exact Option.some_injective _ hq ▸ h
    case isFalse => simp at hq

def exOracle : BranchOracle ExSub ExPC ExState where
  isa := exISA
  behavior := exBehavior
  query := exQuery
  query_sound := exQuery_sound
  query_new := exQuery_new

/-! ## Convergence properties -/

theorem exOracle_productive : exOracle.Productive exTarget := by
  intro model h_sub h_ne
  show ∃ b, exQuery model = some b
  unfold exQuery
  by_contra h_none
  push_neg at h_none
  have h1 : branchA ∈ model := by
    by_contra h; exact absurd (h_none branchA (by simp [h])) (by simp)
  have h2 : branchB ∈ model := by
    by_contra h; exact absurd (h_none branchB (by simp [h, h1])) (by simp)
  exact h_ne (Finset.Subset.antisymm h_sub (by
    intro x hx; simp [exTarget] at hx; rcases hx with rfl | rfl <;> assumption))

theorem exOracle_bounded : exOracle.TargetBounded exTarget := by
  intro model b hq
  change exQuery model = some b at hq
  unfold exQuery at hq
  split at hq
  · exact Option.some_injective _ hq ▸ (by simp [exTarget])
  · split at hq
    · exact Option.some_injective _ hq ▸ (by simp [exTarget])
    · simp at hq

/-! ## End-to-end: the oracle converges to a bisimilar model -/

theorem exOracle_converges_bisimilar :
    ∃ n, n ≤ exTarget.card ∧
      Bisimilar
        (branchBehavior exISA (↑(oracleSequence exOracle n) : Set (Branch ExSub ExPC)))
        exBehavior :=
  branchAccumulation_bisimilar exOracle exTarget
    exOracle_productive exOracle_bounded exTarget_complete


/-! ## Quotient bisimulation smoke test

The end-to-end quotient theorem applies to this concrete instance:
the oracle converges and the quotient yields a finite abstract model
cross-bisimilar to the concrete system. -/

/-- Decidability of `exISA.satisfies` — needed for signature computation and finiteness. -/
instance exSatisfies_decidable : ∀ (s : ExState) (φ : ExPC), Decidable (exISA.satisfies s φ) :=
  fun s φ => inferInstanceAs (Decidable (φ s = true))

instance exOracle_satisfies_decidable :
    ∀ (s : ExState) (φ : ExPC), Decidable (exOracle.isa.satisfies s φ) :=
  exSatisfies_decidable

/-- The oracle converges to a finite model cross-bisimilar to the concrete
    system. Smoke test for the full Phase 4 pipeline including finiteness. -/
theorem exOracle_quotient_bisimulation :
    ∃ n, n ≤ exTarget.card ∧
      CrossBisimulation
        (Quotient.mk (pcSetoid exISA (oracleSequence exOracle n)))
        exBehavior
        (abstractBehavior exISA (oracleSequence exOracle n)) ∧
      Fintype.card (Quotient (pcSetoid exISA (oracleSequence exOracle n))) ≤
        2 ^ (pcClosure exISA (oracleSequence exOracle n)).card :=
  quotientBisimulation exOracle exTarget
    exOracle_productive exOracle_bounded exTarget_complete
