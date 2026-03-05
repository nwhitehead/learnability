import Learnability
import Convergence

/-!
# Bridge: Learnability → Convergence

The same refinement technique is formalized twice in this project:
concretely for LTSes (`Convergence.lean`) and abstractly for any
observable system (`Learnability.lean`). This file connects them.

## Main construction

Any `LearnabilityPreconditions` instance with a designated initial state
gives rise to a `CoRefinementProcess` (`toCoRefinementProcess`), and
the general framework's `extractionDims` is a valid co-refinement fixpoint
(`extractionDims_isCoRefinementFixpoint`).

## The vacuous non-controllability argument

The `CoRefinementProcess` axiom `non_ctrl_at_fixpoint` requires: at a
fixpoint, non-controllable transitions preserve projection. At first
glance this seems like additional content beyond what `Learnability.lean`
proves. But at any fixpoint of `refineStep`, controllability holds for
relevant states (`controllable_at_any_fixpoint`). And controllability
implies that every label available from a relevant state IS controllable —
making the `¬IsXControllable` hypothesis in `non_ctrl_at_fixpoint`
vacuously false. The conclusion holds trivially.

## Bridge hypothesis

The construction requires `h_reach_relevant`: LTS-reachable states are
relevant. In the standard operational semantics instantiation,
`relevant = Reachable` and this is trivial.

## Reverse direction

Not formalized. Not every `CoRefinementProcess` corresponds to a
`LearnabilityPreconditions` instance, because `CoRefinementProcess` uses
abstract `mkProjection` and `mkOracle` functions that don't necessarily
decompose into a fixed `observe` + `project`. The reverse direction
would require additional hypotheses constraining the structure of
`mkProjection`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

section LearnabilityConvergenceBridge

variable {State Label Dim Value : Type*}
  [DecidableEq Dim] [Fintype Dim] [Inhabited Value]

/-! ## Controllability at Any Fixpoint

The controllability argument from `extraction_exists` works at any fixpoint
of `refineStep`, not just the one starting from ∅. The proof only uses
`refineStep X = X`, never the starting point. This generalization is
needed for the `CoRefinementProcess` bridge.
-/

open Classical in
/-- At any fixpoint of `refineStep`, behavior availability is determined
    by projection for relevant states.

    This is the controllability conclusion of `extraction_exists`
    generalized to any fixpoint. The proof is identical — at fixpoint,
    if `d ∉ X` but `s₁` and `s₂` differ at `d` with a controllability
    violation, then `d ∈ refineStep X = X`, contradiction. -/
theorem controllable_at_any_fixpoint
    (lp : LearnabilityPreconditions State Label Dim Value)
    (X : Finset Dim)
    (h_fp : refineStep lp.toObservableSystem X = X) :
    ∀ (s₁ s₂ : State) (ℓ : Label), lp.relevant s₁ →
      project lp.observe X s₁ = project lp.observe X s₂ →
      (∃ s₁', lp.behavior s₁ ℓ s₁') →
      (∃ s₂', lp.behavior s₂ ℓ s₂') := by
  intro s₁ s₂ ℓ h_rel hproj_eq ⟨s₁', hbeh⟩
  by_cases h_can : ∃ s', lp.behavior s₂ ℓ s'
  · exact h_can
  · exfalso; apply h_can
    have h_eq : s₁ = s₂ := by
      apply lp.identifiable _ _ h_rel
      intro d
      by_cases hd : d ∈ X
      · have h_pe : (if d ∈ X then lp.observe s₁ d else (default : Value)) =
            (if d ∈ X then lp.observe s₂ d else default) := congr_fun hproj_eq d
        rw [if_pos hd, if_pos hd] at h_pe
        exact h_pe
      · by_contra h_ne
        have h_mem : d ∈ refineStep lp.toObservableSystem X := by
          apply Finset.mem_union_right
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ d, s₁, s₂, ℓ, h_rel, ⟨s₁', hbeh⟩,
                 hproj_eq.symm, h_can, h_ne⟩
        rw [h_fp] at h_mem
        exact hd h_mem
    subst h_eq; exact ⟨s₁', hbeh⟩

/-! ## LearnabilityPreconditions → CoRefinementProcess -/

open Classical in
/-- Construct a `CoRefinementProcess` from `LearnabilityPreconditions`.

    The projection and oracle at each dimension set X are defined via
    `project observe X` and `projectedOracle oracle observe X` — the same
    functions used throughout `Learnability.lean`.

    The `non_ctrl_at_fixpoint` axiom holds vacuously: at any fixpoint of
    `refineStep`, controllability holds for relevant states (by
    `controllable_at_any_fixpoint`), which means `IsXControllable` holds
    for every reachable state that can take a step. So `¬IsXControllable`
    is never satisfied, and the implication is vacuously true. -/
noncomputable def LearnabilityPreconditions.toCoRefinementProcess
    (lp : LearnabilityPreconditions State Label Dim Value)
    (init : State)
    (h_reach_relevant : ∀ s,
      (LTS.mk init lp.behavior).Reachable s → lp.relevant s) :
    CoRefinementProcess State (Dim → Value) Dim Label where
  H_I := { init := init, step := lp.behavior }
  mkProjection := fun X => project lp.observe X
  mkOracle := fun X ℓ x x' => projectedOracle lp.oracle lp.observe X ℓ x x'
  refineStep := refineStep lp.toObservableSystem
  refine_inflationary := fun _ => Finset.subset_union_left
  sound_at_fixpoint := by
    intro X _ σ σ' ℓ _ h_step
    exact ⟨σ, σ', rfl, lp.sound σ σ' ℓ h_step, rfl⟩
  non_ctrl_at_fixpoint := by
    intro X h_fp σ σ' ℓ h_reach h_step h_not_ctrl
    -- Controllability at fixpoint makes ¬IsXControllable impossible
    exfalso; apply h_not_ctrl
    intro σ₂ h_proj_eq
    exact controllable_at_any_fixpoint lp X h_fp σ σ₂ ℓ
      (h_reach_relevant σ h_reach) h_proj_eq.symm ⟨σ', h_step⟩

/-! ## Fixpoint Agreement

The general framework's `extractionDims` (from `Learnability.lean`) is
a valid co-refinement fixpoint (from `Convergence.lean`). Both use the
same `refineStep` starting from `∅` — the fixpoint is unique because
inflationary iteration on a finset stabilizes to a single value.
-/

open Classical in
/-- The `extractionDims` from `Learnability.lean` is a valid
    co-refinement fixpoint in the sense of `Convergence.lean`.

    Soundness is immediate (every behavior witnesses itself in the
    projected oracle). Non-controllability preservation holds vacuously
    (controllability at the fixpoint makes `¬IsXControllable` impossible
    for reachable states). -/
theorem LearnabilityPreconditions.extractionDims_isCoRefinementFixpoint
    (lp : LearnabilityPreconditions State Label Dim Value)
    (init : State)
    (h_reach_relevant : ∀ s,
      (LTS.mk init lp.behavior).Reachable s → lp.relevant s) :
    IsCoRefinementFixpoint
      (LTS.mk init lp.behavior)
      (project lp.observe lp.extractionDims)
      (fun ℓ x x' =>
        projectedOracle lp.oracle lp.observe lp.extractionDims ℓ x x') where
  sound := by
    intro σ σ' ℓ _ h_step
    exact ⟨σ, σ', rfl, lp.sound σ σ' ℓ h_step, rfl⟩
  non_controllable_preserves := by
    intro σ σ' ℓ h_reach h_step h_not_ctrl
    exfalso; apply h_not_ctrl
    intro σ₂ h_proj_eq
    exact controllable_at_any_fixpoint lp lp.extractionDims
      lp.extractionDims_is_fixpoint σ σ₂ ℓ
      (h_reach_relevant σ h_reach) h_proj_eq.symm ⟨σ', h_step⟩

open Classical in
/-- End-to-end: `extractionDims` yields a forward simulation via the
    `Convergence.lean` machinery.

    This connects the two chains: the general framework's fixpoint
    (`Learnability.lean`) plugs into the LTS simulation theorem
    (`Convergence.lean`). -/
theorem LearnabilityPreconditions.extractionDims_yields_simulation
    (lp : LearnabilityPreconditions State Label Dim Value)
    (init : State)
    (h_reach_relevant : ∀ s,
      (LTS.mk init lp.behavior).Reachable s → lp.relevant s) :
    let H_I : LTS State Label := ⟨init, lp.behavior⟩
    let π := project lp.observe lp.extractionDims
    let R := fun ℓ x x' =>
      projectedOracle lp.oracle lp.observe lp.extractionDims ℓ x x'
    (LTS.ofOracle (π init) R).Simulates H_I
      (fun x σ => π σ = x ∧ H_I.Reachable σ) :=
  simulation_at_coRefinement_fixpoint _ _ _
    (lp.extractionDims_isCoRefinementFixpoint init h_reach_relevant)

end LearnabilityConvergenceBridge
