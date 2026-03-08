import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexISA
import Instances.ISAs.VexLowering

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

private theorem lowerInit_matches {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg) :
    LowerStateMatches input (input, TempEnv.empty) (SymSub.id, SymTempEnv.empty) := by
  constructor
  · simp
  · intro tmp
    simp [TempEnv.empty, SymTempEnv.empty]

private theorem partialInit_matches {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg) :
    PartialSummaryMatches input (input, TempEnv.empty) PartialSummary.init := by
  constructor
  · simp [PartialSummary.init]
  · intro tmp
    simp [PartialSummary.init, TempEnv.empty, SymTempEnv.empty]

private theorem lowerStmt_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg) (ip_reg : Reg) (stmt : Stmt Reg)
    (concrete : ConcreteState Reg × TempEnv) (symbolic : LowerState Reg)
    (hMatch : LowerStateMatches input concrete symbolic) :
    LowerStateMatches input (execStmt ip_reg concrete stmt) (lowerStmt ip_reg symbolic stmt) := by
  cases stmt with
  | linear stmt =>
      simpa [execStmt, lowerStmt, execLinearStmt, lowerLinearStmt] using
        (linearStmtBridge stmt).sound input concrete symbolic hMatch
  | branch stmt =>
      rcases symbolic with ⟨sub, temps⟩
      let ps : PartialSummary Reg := { sub := sub, pc := .true, temps := temps }
      have hMatch' : PartialSummaryMatches input concrete ps := by
        simpa [ps, LowerStateMatches, PartialSummaryMatches] using hMatch
      simpa [execStmt, lowerStmt, execBranchContinue, lowerBranchContinue, ps,
        LowerStateMatches, PartialSummaryMatches] using
        (branchStmtBridge ip_reg stmt).continue_matches input concrete ps hMatch'

private theorem lowerStmts_sound_from {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg) (ip_reg : Reg)
    (stmts : List (Stmt Reg)) (concrete : ConcreteState Reg × TempEnv) (symbolic : LowerState Reg)
    (hMatch : LowerStateMatches input concrete symbolic) :
    LowerStateMatches input (stmts.foldl (execStmt ip_reg) concrete) (stmts.foldl (lowerStmt ip_reg) symbolic) := by
  induction stmts generalizing concrete symbolic with
  | nil => simpa using hMatch
  | cons stmt stmts ih =>
      simpa [List.foldl] using ih (execStmt ip_reg concrete stmt) (lowerStmt ip_reg symbolic stmt)
        (lowerStmt_sound input ip_reg stmt concrete symbolic hMatch)

/-- Executing a concrete VEX block matches applying its lowered symbolic summary. -/
theorem lowerBlockSub_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) (input : ConcreteState Reg) :
    applySymSub (lowerBlockSub block) input = execBlock block input := by
  rcases hExec : block.stmts.foldl (execStmt block.ip_reg) (input, TempEnv.empty) with ⟨state, temps⟩
  have hMatch :=
    lowerStmts_sound_from input block.ip_reg block.stmts (input, TempEnv.empty) (SymSub.id, SymTempEnv.empty)
      (lowerInit_matches input)
  simp [hExec] at hMatch
  rcases hMatch with ⟨hState, _hTemps⟩
  unfold lowerBlockSub lowerStmts
  rw [applySymSub_write]
  simp [execBlock, hExec, hState]

/-- The lowered summary of a VEX block has the same concrete effect as the block itself. -/
theorem lowerBlock_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) (input : ConcreteState Reg) :
    Summary.apply (lowerBlock block) input = execBlock block input := by
  simpa [lowerBlock, Summary.apply] using lowerBlockSub_sound block input

private theorem lowerSummariesFrom_sound_from {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg) (ip_reg : Reg) (fallthrough : UInt64) :
    ∀ (stmts : List (Stmt Reg)) (concrete : ConcreteState Reg × TempEnv) (ps : PartialSummary Reg),
      PartialSummaryMatches input concrete ps →
      Summary.enabled { sub := ps.sub, pc := ps.pc } input →
      ∀ output, output ∈ execStmtsSuccs ip_reg fallthrough stmts concrete →
        ∃ summary ∈ (lowerSummariesFrom ip_reg ps stmts fallthrough).toFinset,
          Summary.enabled summary input ∧ Summary.apply summary input = output := by
  intro stmts
  induction stmts with
  | nil =>
      intro concrete ps hMatch hPc output hOut
      rcases concrete with ⟨state, temps⟩
      rcases hMatch with ⟨hState, hTemps⟩
      have hOutput : output = state.write ip_reg fallthrough := by
        simpa [execStmtsSuccs] using hOut
      refine ⟨ps.finish ip_reg fallthrough, ?_, ?_, ?_⟩
      · simp [lowerSummariesFrom]
      · simpa [PartialSummary.finish, Summary.enabled] using hPc
      · rw [hOutput]
        calc
          Summary.apply (ps.finish ip_reg fallthrough) input
              = (applySymSub ps.sub input).write ip_reg fallthrough := by
                  simpa [PartialSummary.finish, Summary.apply] using
                    (applySymSub_write ps.sub input ip_reg (.const fallthrough))
          _ = state.write ip_reg fallthrough := by
                exact congrArg (fun st => st.write ip_reg fallthrough) hState.symm
  | cons stmt stmts ih =>
      intro concrete ps hMatch hPc output hOut
      cases stmt with
      | linear stmt =>
          let lowered := lowerLinearStmt (ps.sub, ps.temps) stmt
          let ps' : PartialSummary Reg := { ps with sub := lowered.1, temps := lowered.2 }
          have hMatchLinear : LowerStateMatches input concrete (ps.sub, ps.temps) := hMatch
          have hMatch' : PartialSummaryMatches input (execLinearStmt concrete stmt) ps' := by
            have hStep := (linearStmtBridge stmt).sound input concrete (ps.sub, ps.temps) hMatchLinear
            simpa [ps', lowered, LowerStateMatches, PartialSummaryMatches] using hStep
          simpa [lowerSummariesFrom, lowered, ps', execStmtsSuccs, execLinearStmt] using
            ih (execLinearStmt concrete stmt) ps' hMatch' hPc output hOut
      | branch stmt =>
          let bridge := branchStmtBridge ip_reg stmt
          by_cases hFire : bridge.fires concrete = true
          · have hOutput : output = bridge.taken concrete := by
              simpa [execStmtsSuccs, bridge, hFire] using hOut
            have hGuard : evalSymPC input (bridge.lowerGuard ps) = true := by
              rw [← bridge.fires_iff_guard input concrete ps hMatch]
              exact hFire
            have hEnabled : Summary.enabled (bridge.lowerTaken ps) input := by
              exact (bridge.taken_pc_iff ps input).2 ⟨hPc, hGuard⟩
            refine ⟨bridge.lowerTaken ps, ?_, hEnabled, ?_⟩
            · simp [lowerSummariesFrom, bridge]
            · simpa [hOutput] using bridge.taken_sound input concrete ps hMatch hFire
          · have hFireFalse : bridge.fires concrete = false := by
              cases h : bridge.fires concrete <;> simp [h] at hFire ⊢
            have hGuardFalse : evalSymPC input (bridge.lowerGuard ps) = false := by
              rw [← bridge.fires_iff_guard input concrete ps hMatch]
              exact hFireFalse
            have hPc' : Summary.enabled { sub := (bridge.lowerContinue ps).sub, pc := (bridge.lowerContinue ps).pc } input := by
              exact (bridge.continue_pc_iff ps input).2 ⟨hPc, hGuardFalse⟩
            have hMatch' : PartialSummaryMatches input (bridge.cont concrete) (bridge.lowerContinue ps) := by
              exact bridge.continue_matches input concrete ps hMatch
            have hOut' : output ∈ execStmtsSuccs ip_reg fallthrough stmts (bridge.cont concrete) := by
              simpa [execStmtsSuccs, bridge, hFireFalse] using hOut
            rcases ih (bridge.cont concrete) (bridge.lowerContinue ps) hMatch' hPc' output hOut' with
              ⟨summary, hMem, hEnabled, hApply⟩
            refine ⟨summary, ?_, hEnabled, hApply⟩
            simp [lowerSummariesFrom, bridge, hMem]

/-- Every concrete successor of a guarded VEX block is witnessed by an enabled lowered summary. -/
theorem lowerBlockSummaries_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) (input output : ConcreteState Reg)
    (hOut : output ∈ execBlockSuccs block input) :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = output := by
  have hPc : Summary.enabled { sub := PartialSummary.init.sub, pc := PartialSummary.init.pc } input := by
    simp [PartialSummary.init, Summary.enabled, satisfiesSymPC]
  obtain ⟨summary, hMem, hEnabled, hApply⟩ :=
    lowerSummariesFrom_sound_from input block.ip_reg block.next block.stmts (input, TempEnv.empty)
      PartialSummary.init (partialInit_matches input) hPc output hOut
  refine ⟨summary, ?_, hEnabled, hApply⟩
  simpa [lowerBlockSummaries, lowerBlockSummariesList] using hMem

private theorem lowerSummariesFrom_prefix_enabled {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg) (ip_reg : Reg) (fallthrough : UInt64) :
    ∀ (stmts : List (Stmt Reg)) (ps : PartialSummary Reg) (summary : Summary Reg),
      summary ∈ lowerSummariesFrom ip_reg ps stmts fallthrough →
      Summary.enabled summary input →
      Summary.enabled { sub := ps.sub, pc := ps.pc } input := by
  intro stmts
  induction stmts with
  | nil =>
      intro ps summary hMem hEnabled
      simp [lowerSummariesFrom] at hMem
      rcases hMem with rfl
      simpa [PartialSummary.finish, Summary.enabled] using hEnabled
  | cons stmt stmts ih =>
      intro ps summary hMem hEnabled
      cases stmt with
      | linear stmt =>
          let lowered := lowerLinearStmt (ps.sub, ps.temps) stmt
          let ps' : PartialSummary Reg := { ps with sub := lowered.1, temps := lowered.2 }
          simpa [lowerSummariesFrom, lowered, ps'] using ih ps' summary hMem hEnabled
      | branch stmt =>
          let bridge := branchStmtBridge ip_reg stmt
          simp [lowerSummariesFrom] at hMem
          rcases hMem with rfl | hMem
          · exact (bridge.taken_pc_iff ps input).1 hEnabled |>.1
          · have hChild : Summary.enabled { sub := (bridge.lowerContinue ps).sub, pc := (bridge.lowerContinue ps).pc } input := by
              exact ih (bridge.lowerContinue ps) summary hMem hEnabled
            exact (bridge.continue_pc_iff ps input).1 hChild |>.1

private theorem lowerSummariesFrom_complete_from {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg) (ip_reg : Reg) (fallthrough : UInt64) :
    ∀ (stmts : List (Stmt Reg)) (concrete : ConcreteState Reg × TempEnv) (ps : PartialSummary Reg) (summary : Summary Reg),
      PartialSummaryMatches input concrete ps →
      summary ∈ lowerSummariesFrom ip_reg ps stmts fallthrough →
      Summary.enabled summary input →
      Summary.apply summary input ∈ execStmtsSuccs ip_reg fallthrough stmts concrete := by
  intro stmts
  induction stmts with
  | nil =>
      intro concrete ps summary hMatch hMem hEnabled
      rcases concrete with ⟨state, temps⟩
      rcases hMatch with ⟨hState, hTemps⟩
      simp [lowerSummariesFrom] at hMem
      rcases hMem with rfl
      have hApply :
          Summary.apply (ps.finish ip_reg fallthrough) input = state.write ip_reg fallthrough := by
        calc
          Summary.apply (ps.finish ip_reg fallthrough) input
              = (applySymSub ps.sub input).write ip_reg fallthrough := by
                  simpa [PartialSummary.finish, Summary.apply] using
                    (applySymSub_write ps.sub input ip_reg (.const fallthrough))
          _ = state.write ip_reg fallthrough := by
                exact congrArg (fun st => st.write ip_reg fallthrough) hState.symm
      simp [execStmtsSuccs, hApply]
  | cons stmt stmts ih =>
      intro concrete ps summary hMatch hMem hEnabled
      cases stmt with
      | linear stmt =>
          let lowered := lowerLinearStmt (ps.sub, ps.temps) stmt
          let ps' : PartialSummary Reg := { ps with sub := lowered.1, temps := lowered.2 }
          have hMatchLinear : LowerStateMatches input concrete (ps.sub, ps.temps) := hMatch
          have hMatch' : PartialSummaryMatches input (execLinearStmt concrete stmt) ps' := by
            have hStep := (linearStmtBridge stmt).sound input concrete (ps.sub, ps.temps) hMatchLinear
            simpa [ps', lowered, LowerStateMatches, PartialSummaryMatches] using hStep
          simpa [lowerSummariesFrom, lowered, ps', execStmtsSuccs, execLinearStmt] using
            ih (execLinearStmt concrete stmt) ps' summary hMatch' hMem hEnabled
      | branch stmt =>
          let bridge := branchStmtBridge ip_reg stmt
          simp [lowerSummariesFrom] at hMem
          rcases hMem with rfl | hMem
          · have hTaken : Summary.enabled (bridge.lowerTaken ps) input := hEnabled
            have hGuard : evalSymPC input (bridge.lowerGuard ps) = true := by
              exact (bridge.taken_pc_iff ps input).1 hTaken |>.2
            have hFire : bridge.fires concrete = true := by
              rw [bridge.fires_iff_guard input concrete ps hMatch]
              exact hGuard
            have hApply : Summary.apply (bridge.lowerTaken ps) input = bridge.taken concrete := by
              exact bridge.taken_sound input concrete ps hMatch hFire
            simp [execStmtsSuccs, bridge, hFire, hApply]
          · have hChild : Summary.enabled { sub := (bridge.lowerContinue ps).sub, pc := (bridge.lowerContinue ps).pc } input := by
              exact lowerSummariesFrom_prefix_enabled input ip_reg fallthrough stmts (bridge.lowerContinue ps) summary hMem hEnabled
            have hGuardFalse : evalSymPC input (bridge.lowerGuard ps) = false := by
              exact (bridge.continue_pc_iff ps input).1 hChild |>.2
            have hFireFalse : bridge.fires concrete = false := by
              rw [bridge.fires_iff_guard input concrete ps hMatch]
              exact hGuardFalse
            have hMatch' : PartialSummaryMatches input (bridge.cont concrete) (bridge.lowerContinue ps) := by
              exact bridge.continue_matches input concrete ps hMatch
            have hRec := ih (bridge.cont concrete) (bridge.lowerContinue ps) summary hMatch' hMem hEnabled
            simpa [execStmtsSuccs, bridge, hFireFalse] using hRec

theorem lowerBlockSummaries_complete {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) (input : ConcreteState Reg) (summary : Summary Reg)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input ∈ execBlockSuccs block input := by
  have hMemList : summary ∈ lowerSummariesFrom block.ip_reg PartialSummary.init block.stmts block.next := by
    simpa [lowerBlockSummaries, lowerBlockSummariesList] using hMem
  have hInit : PartialSummaryMatches input (input, TempEnv.empty) PartialSummary.init :=
    partialInit_matches input
  exact lowerSummariesFrom_complete_from input block.ip_reg block.next block.stmts (input, TempEnv.empty)
    PartialSummary.init summary hInit hMemList hEnabled

theorem lowerBlockSummaries_complete_eq_of_unique {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) (input expected : ConcreteState Reg) (summary : Summary Reg)
    (hUnique : execBlockSuccs block input = ({expected} : Finset (ConcreteState Reg)))
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  rw [hUnique] at hSucc
  simpa using hSucc

end VexISA
