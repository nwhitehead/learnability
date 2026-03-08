import Instances.ISAs.VexModelEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-- An extensional subsystem region: just the relevant inputs, the observable projection,
    and the observed behavior the subsystem is meant to denote. -/
structure Region (Reg : Type) (Obs : Type) [DecidableEq Reg] [Fintype Reg] where
  Relevant : ConcreteState Reg → Prop
  observe : ConcreteState Reg → Obs
  DenotesObs : ConcreteState Reg → Obs → Prop

/-- A finite family of lifted block paths is a complete witness for a region when the
    path-family concrete denotation agrees exactly with the region's observed behavior. -/
def WitnessComplete
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (R : Region Reg Obs)
    (paths : Finset (List (Block Reg))) : Prop :=
  ∀ s o,
    ExecPathFamilyDenotesObs R.Relevant R.observe paths s o ↔
      R.DenotesObs s o

/-- A complete finite path-family witness yields an adequate extracted symbolic model
    for the region it witnesses. -/
theorem extractedModel_of_witnessComplete
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (R : Region Reg Obs)
    (paths : Finset (List (Block Reg)))
    (hcomplete : WitnessComplete R paths) :
    ∀ s o,
      VexModelDenotesObs R.Relevant R.observe (lowerPathFamilySummaries paths) s o ↔
        R.DenotesObs s o := by
  intro s o
  exact Iff.trans
    (lowerPathFamilySummaries_denotesObs_iff_execPathFamily R.Relevant R.observe paths s o)
    (hcomplete s o)

/-- Any two complete witnesses for the same region induce semantically equivalent
    extracted models. -/
theorem completeWitnesses_modelEq
    {Reg : Type} {Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (R : Region Reg Obs)
    (paths₁ paths₂ : Finset (List (Block Reg)))
    (h₁ : WitnessComplete R paths₁)
    (h₂ : WitnessComplete R paths₂) :
    VexModelEq R.Relevant R.observe
      (lowerPathFamilySummaries paths₁)
      (lowerPathFamilySummaries paths₂) := by
  intro s o
  exact Iff.trans
    (extractedModel_of_witnessComplete R paths₁ h₁ s o)
    (extractedModel_of_witnessComplete R paths₂ h₂ s o).symm

 end VexISA
