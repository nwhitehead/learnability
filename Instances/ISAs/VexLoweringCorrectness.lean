import Instances.ISAs.VexLowering

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

private def LowerStateMatches (input : ConcreteState)
    (concrete : ConcreteState × TempEnv) (symbolic : LowerState) : Prop :=
  concrete.1 = applySymSub symbolic.1 input ∧
    ∀ tmp, concrete.2 tmp = evalSymExpr input (symbolic.2 tmp)

private theorem lowerInit_matches (input : ConcreteState) :
    LowerStateMatches input (input, TempEnv.empty) (SymSub.id, SymTempEnv.empty) := by
  constructor
  · simp
  · intro tmp
    simp [TempEnv.empty, SymTempEnv.empty]

private theorem lowerExpr_sound
    (input state : ConcreteState) (temps : TempEnv) (sub : SymSub) (symTemps : SymTempEnv)
    (hState : state = applySymSub sub input)
    (hTemps : ∀ tmp, temps tmp = evalSymExpr input (symTemps tmp))
    (expr : Expr) :
    evalExpr state temps expr = evalSymExpr input (lowerExpr sub symTemps expr) := by
  induction expr with
  | const value => rfl
  | get reg =>
      rw [hState]
      simpa [lowerExpr] using ConcreteState.read_applySymSub sub input reg
  | tmp tmp => simp [lowerExpr, hTemps]
  | add64 lhs rhs ihL ihR =>
      simp [lowerExpr, ihL, ihR]
  | load64 addr ih =>
      subst state
      simpa [evalExpr, lowerExpr] using
        congrArg (fun value => ByteMem.read64le (applySymSub sub input).mem value) ih

private theorem applySymSub_writeMem (sub : SymSub) (input : ConcreteState) (mem : SymMem) :
    applySymSub (SymSub.writeMem sub mem) input =
      { applySymSub sub input with mem := evalSymMem input mem } := by
  cases input
  rfl

private theorem lowerStmt_sound (input : ConcreteState) (stmt : Stmt)
    (concrete : ConcreteState × TempEnv) (symbolic : LowerState)
    (hMatch : LowerStateMatches input concrete symbolic) :
    LowerStateMatches input (execStmt concrete stmt) (lowerStmt symbolic stmt) := by
  rcases concrete with ⟨state, temps⟩
  rcases symbolic with ⟨sub, symTemps⟩
  rcases hMatch with ⟨hState, hTemps⟩
  cases stmt with
  | wrTmp tmp expr =>
      constructor
      · simpa [execStmt, lowerStmt] using hState
      · intro tmp'
        by_cases h : tmp' = tmp
        · subst h
          have hExpr := lowerExpr_sound input state temps sub symTemps hState hTemps expr
          simp [execStmt, lowerStmt, hExpr]
        · simpa [execStmt, lowerStmt, h] using hTemps tmp'
  | put reg expr =>
      constructor
      · subst hState
        have hExpr := lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps expr
        cases reg <;>
          simpa [execStmt, lowerStmt, applySymSub, SymSub.write] using hExpr
      · intro tmp
        simp [execStmt, lowerStmt, hTemps]
  | store64 addr value =>
      constructor
      · subst hState
        have hAddr := lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps addr
        have hValue := lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps value
        cases hSub : applySymSub sub input with
        | mk rax rcx rdi rip mem =>
            rw [hSub] at hAddr hValue
            simp [applySymSub] at hSub
            rcases hSub with ⟨hRax, hRcx, hRdi, hRip, hMem⟩
            simp [execStmt, lowerStmt, applySymSub, SymSub.writeMem, hAddr, hValue, hRax, hRcx, hRdi, hRip, hMem]
      · intro tmp
        simp [execStmt, lowerStmt, hTemps]
  | exit cond target =>
      constructor
      · simpa [execStmt, lowerStmt] using hState
      · intro tmp
        simp [execStmt, lowerStmt, hTemps]

private theorem lowerStmts_sound_from (input : ConcreteState)
    (stmts : List Stmt) (concrete : ConcreteState × TempEnv) (symbolic : LowerState)
    (hMatch : LowerStateMatches input concrete symbolic) :
    LowerStateMatches input (stmts.foldl execStmt concrete) (stmts.foldl lowerStmt symbolic) := by
  induction stmts generalizing concrete symbolic with
  | nil => simpa using hMatch
  | cons stmt stmts ih =>
      simpa [List.foldl] using ih (execStmt concrete stmt) (lowerStmt symbolic stmt)
        (lowerStmt_sound input stmt concrete symbolic hMatch)

private theorem applySymSub_write (sub : SymSub) (input : ConcreteState) (reg : Reg) (expr : SymExpr) :
    applySymSub (SymSub.write sub reg expr) input =
      (applySymSub sub input).write reg (evalSymExpr input expr) := by
  cases reg <;> cases input <;> rfl

/-- Executing a concrete VEX block matches applying its lowered symbolic summary. -/
theorem lowerBlockSub_sound (block : Block) (input : ConcreteState) :
    applySymSub (lowerBlockSub block) input = execBlock block input := by
  rcases hExec : block.stmts.foldl execStmt (input, TempEnv.empty) with ⟨state, temps⟩
  have hMatch :=
    lowerStmts_sound_from input block.stmts (input, TempEnv.empty) (SymSub.id, SymTempEnv.empty)
      (lowerInit_matches input)
  simp [hExec] at hMatch
  rcases hMatch with ⟨hState, _hTemps⟩
  unfold lowerBlockSub lowerStmts
  rw [applySymSub_write]
  simp [execBlock, hExec, hState]

/-- The lowered summary of a VEX block has the same concrete effect as the block itself. -/
theorem lowerBlock_sound (block : Block) (input : ConcreteState) :
    Summary.apply (lowerBlock block) input = execBlock block input := by
  simpa [lowerBlock, Summary.apply] using lowerBlockSub_sound block input

private def PartialSummaryMatches (input : ConcreteState)
    (concrete : ConcreteState × TempEnv) (ps : PartialSummary) : Prop :=
  concrete.1 = applySymSub ps.sub input ∧
    ∀ tmp, concrete.2 tmp = evalSymExpr input (ps.temps tmp)

private theorem partialInit_matches (input : ConcreteState) :
    PartialSummaryMatches input (input, TempEnv.empty) PartialSummary.init := by
  constructor
  · simp [PartialSummary.init]
  · intro tmp
    simp [PartialSummary.init, TempEnv.empty, SymTempEnv.empty]

private theorem lowerCond_sound
    (input state : ConcreteState) (temps : TempEnv) (sub : SymSub) (symTemps : SymTempEnv)
    (hState : state = applySymSub sub input)
    (hTemps : ∀ tmp, temps tmp = evalSymExpr input (symTemps tmp))
    (cond : Cond) :
    evalCond state temps cond = evalSymPC input (lowerCond sub symTemps cond) := by
  cases cond with
  | eq64 lhs rhs =>
      simp [lowerCond, lowerExpr_sound input state temps sub symTemps hState hTemps lhs,
        lowerExpr_sound input state temps sub symTemps hState hTemps rhs]

private theorem lowerSummariesFrom_sound_from
    (input : ConcreteState) (fallthrough : UInt64) :
    ∀ (stmts : List Stmt) (concrete : ConcreteState × TempEnv) (ps : PartialSummary),
      PartialSummaryMatches input concrete ps →
      Summary.enabled { sub := ps.sub, pc := ps.pc } input →
      ∀ output, output ∈ execStmtsSuccs fallthrough stmts concrete →
        ∃ summary ∈ (lowerSummariesFrom ps stmts fallthrough).toFinset,
          Summary.enabled summary input ∧ Summary.apply summary input = output := by
  intro stmts
  induction stmts with
  | nil =>
      intro concrete ps hMatch hPc output hOut
      rcases concrete with ⟨state, temps⟩
      rcases hMatch with ⟨hState, hTemps⟩
      have hOutput : output = { state with rip := fallthrough } := by
        simpa using hOut
      refine ⟨ps.finish fallthrough, ?_, ?_, ?_⟩
      · simp [lowerSummariesFrom]
      · simpa [PartialSummary.finish, Summary.enabled] using hPc
      · rw [hOutput]
        calc
          Summary.apply (ps.finish fallthrough) input
              = (applySymSub ps.sub input).write .rip fallthrough := by
                  simpa [PartialSummary.finish, Summary.apply, ConcreteState.write] using
                    (applySymSub_write ps.sub input .rip (.const fallthrough))
          _ = { state with rip := fallthrough } := by
                simpa [ConcreteState.write] using congrArg (fun st => st.write .rip fallthrough) hState.symm
  | cons stmt stmts ih =>
      intro concrete ps hMatch hPc output hOut
      rcases concrete with ⟨state, temps⟩
      rcases hMatch with ⟨hState, hTemps⟩
      cases stmt with
      | wrTmp tmp expr =>
          let ps' : PartialSummary :=
            { ps with temps := SymTempEnv.write ps.temps tmp (lowerExpr ps.sub ps.temps expr) }
          have hMatch' : PartialSummaryMatches input (execStmt (state, temps) (.wrTmp tmp expr)) ps' := by
            have hOld : LowerStateMatches input (state, temps) (ps.sub, ps.temps) := ⟨hState, hTemps⟩
            have hOld' := lowerStmt_sound input (.wrTmp tmp expr) (state, temps) (ps.sub, ps.temps) hOld
            simpa [ps', PartialSummaryMatches]
          simpa [execStmtsSuccs, lowerSummariesFrom, ps'] using
            ih (execStmt (state, temps) (.wrTmp tmp expr)) ps' hMatch' hPc output hOut
      | put reg expr =>
          let ps' : PartialSummary :=
            { ps with sub := SymSub.write ps.sub reg (lowerExpr ps.sub ps.temps expr) }
          have hMatch' : PartialSummaryMatches input (execStmt (state, temps) (.put reg expr)) ps' := by
            have hOld : LowerStateMatches input (state, temps) (ps.sub, ps.temps) := ⟨hState, hTemps⟩
            have hOld' := lowerStmt_sound input (.put reg expr) (state, temps) (ps.sub, ps.temps) hOld
            simpa [ps', PartialSummaryMatches]
          simpa [execStmtsSuccs, lowerSummariesFrom, ps'] using
            ih (execStmt (state, temps) (.put reg expr)) ps' hMatch' hPc output hOut
      | store64 addr value =>
          let mem := SymMem.store64 ps.sub.mem (lowerExpr ps.sub ps.temps addr) (lowerExpr ps.sub ps.temps value)
          let ps' : PartialSummary :=
            { ps with sub := SymSub.writeMem ps.sub mem }
          have hMatch' : PartialSummaryMatches input (execStmt (state, temps) (.store64 addr value)) ps' := by
            have hOld : LowerStateMatches input (state, temps) (ps.sub, ps.temps) := ⟨hState, hTemps⟩
            have hOld' := lowerStmt_sound input (.store64 addr value) (state, temps) (ps.sub, ps.temps) hOld
            simpa [ps', PartialSummaryMatches]
          simpa [execStmtsSuccs, lowerSummariesFrom, ps'] using
            ih (execStmt (state, temps) (.store64 addr value)) ps' hMatch' hPc output hOut
      | exit cond target =>
          cases cond with
          | eq64 lhs rhs =>
              let φ := lowerCond ps.sub ps.temps (.eq64 lhs rhs)
              have hCond : (evalExpr state temps lhs == evalExpr state temps rhs) = evalSymPC input φ := by
                simpa [evalCond, φ] using
                  lowerCond_sound input state temps ps.sub ps.temps hState hTemps (.eq64 lhs rhs)
              by_cases hExit : (evalExpr state temps lhs == evalExpr state temps rhs) = true
              · have hOutput : output = { state with rip := target } := by
                  simpa [execStmtsSuccs, evalCond, hExit] using hOut
                have hPhiTrue : evalSymPC input φ = true := by
                  rw [← hCond]
                  exact hExit
                refine ⟨{ sub := SymSub.write ps.sub .rip (.const target), pc := .and ps.pc φ }, ?_, ?_, ?_⟩
                · simp [lowerSummariesFrom, φ]
                · rw [Summary.enabled, satisfiesSymPC, evalSymPC, hPc, hPhiTrue]
                  simp
                · rw [hOutput]
                  calc
                    Summary.apply { sub := SymSub.write ps.sub .rip (.const target), pc := .and ps.pc φ } input
                        = (applySymSub ps.sub input).write .rip target := by
                            simpa [Summary.apply, ConcreteState.write] using
                              (applySymSub_write ps.sub input .rip (.const target))
                    _ = { state with rip := target } := by
                      simpa [ConcreteState.write] using congrArg (fun st => st.write .rip target) hState.symm
              · have hEvalFalse : (evalExpr state temps lhs == evalExpr state temps rhs) = false := by
                  cases hEval : (evalExpr state temps lhs == evalExpr state temps rhs) <;>
                    simp [hEval] at hExit ⊢
                let ps' : PartialSummary := { ps with pc := .and ps.pc (.not φ) }
                have hPhiFalse : evalSymPC input φ = false := by
                  rw [← hCond]
                  exact hEvalFalse
                have hPc' : Summary.enabled { sub := ps'.sub, pc := ps'.pc } input := by
                  rw [Summary.enabled, satisfiesSymPC, evalSymPC, hPc]
                  simp [hPhiFalse]
                have hOut' : output ∈ execStmtsSuccs fallthrough stmts (state, temps) := by
                  simpa [execStmtsSuccs, evalCond, hEvalFalse] using hOut
                have hRec := ih (state, temps) ps' ⟨hState, hTemps⟩ hPc' output hOut'
                rcases hRec with ⟨summary, hMem, hEnabled, hApply⟩
                refine ⟨summary, ?_, hEnabled, hApply⟩
                simp [lowerSummariesFrom, φ, ps', hMem]

/-- Every concrete successor of a guarded VEX block is witnessed by an enabled lowered summary. -/
theorem lowerBlockSummaries_sound (block : Block) (input output : ConcreteState)
    (hOut : output ∈ execBlockSuccs block input) :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = output := by
  have hPc : Summary.enabled { sub := PartialSummary.init.sub, pc := PartialSummary.init.pc } input := by
    simp [PartialSummary.init, Summary.enabled, satisfiesSymPC]
  obtain ⟨summary, hMem, hEnabled, hApply⟩ :=
    lowerSummariesFrom_sound_from input block.next block.stmts (input, TempEnv.empty)
      PartialSummary.init (partialInit_matches input) hPc output hOut
  refine ⟨summary, ?_, hEnabled, hApply⟩
  simpa [lowerBlockSummaries, lowerBlockSummariesList] using hMem

private theorem lowerSummariesFrom_prefix_enabled
    (input : ConcreteState) (fallthrough : UInt64) :
    ∀ (stmts : List Stmt) (ps : PartialSummary) (summary : Summary),
      summary ∈ lowerSummariesFrom ps stmts fallthrough →
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
      | wrTmp tmp expr =>
          let ps' : PartialSummary :=
            { ps with temps := SymTempEnv.write ps.temps tmp (lowerExpr ps.sub ps.temps expr) }
          simpa [lowerSummariesFrom, ps'] using ih ps' summary hMem hEnabled
      | put reg expr =>
          let ps' : PartialSummary :=
            { ps with sub := SymSub.write ps.sub reg (lowerExpr ps.sub ps.temps expr) }
          simpa [lowerSummariesFrom, ps'] using ih ps' summary hMem hEnabled
      | store64 addr value =>
          let mem := SymMem.store64 ps.sub.mem (lowerExpr ps.sub ps.temps addr) (lowerExpr ps.sub ps.temps value)
          let ps' : PartialSummary :=
            { ps with sub := SymSub.writeMem ps.sub mem }
          simpa [lowerSummariesFrom, ps'] using ih ps' summary hMem hEnabled
      | exit cond target =>
          cases cond with
          | eq64 lhs rhs =>
              let φ := lowerCond ps.sub ps.temps (.eq64 lhs rhs)
              simp [lowerSummariesFrom] at hMem
              rcases hMem with rfl | hMem
              · rw [Summary.enabled, satisfiesSymPC, evalSymPC] at hEnabled
                exact (by
                  have hBoth : evalSymPC input ps.pc = true ∧ evalSymPC input φ = true := by
                    simpa [Bool.and_eq_true] using hEnabled
                  simpa [Summary.enabled, satisfiesSymPC] using hBoth.1)
              · let ps' : PartialSummary := { ps with pc := .and ps.pc (.not φ) }
                have hPrefix' := ih ps' summary hMem hEnabled
                have hBoth : evalSymPC input ps.pc = true ∧ evalSymPC input (.not φ) = true := by
                  simpa [ps', Summary.enabled, satisfiesSymPC, Bool.and_eq_true] using hPrefix'
                simpa [Summary.enabled, satisfiesSymPC] using hBoth.1

/-- Every enabled lowered summary of a guarded VEX block corresponds to a concrete successor. -/
theorem lowerBlockSummaries_complete (block : Block) (input : ConcreteState) (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input ∈ execBlockSuccs block input := by
  have hMemList : summary ∈ lowerSummariesFrom PartialSummary.init block.stmts block.next := by
    simpa [lowerBlockSummaries, lowerBlockSummariesList] using hMem
  have hInit : PartialSummaryMatches input (input, TempEnv.empty) PartialSummary.init :=
    partialInit_matches input
  let rec completeFrom (input : ConcreteState) (fallthrough : UInt64) :
      ∀ (stmts : List Stmt) (concrete : ConcreteState × TempEnv) (ps : PartialSummary) (summary : Summary),
        PartialSummaryMatches input concrete ps →
        summary ∈ lowerSummariesFrom ps stmts fallthrough →
        Summary.enabled summary input →
        Summary.apply summary input ∈ execStmtsSuccs fallthrough stmts concrete := by
    intro stmts
    induction stmts with
    | nil =>
        intro concrete ps summary hMatch hMem hEnabled
        rcases concrete with ⟨state, temps⟩
        rcases hMatch with ⟨hState, hTemps⟩
        simp [lowerSummariesFrom] at hMem
        rcases hMem with rfl
        have hApply :
            Summary.apply (ps.finish fallthrough) input = { state with rip := fallthrough } := by
          calc
            Summary.apply (ps.finish fallthrough) input
                = (applySymSub ps.sub input).write .rip fallthrough := by
                    simpa [PartialSummary.finish, Summary.apply, ConcreteState.write] using
                      (applySymSub_write ps.sub input .rip (.const fallthrough))
            _ = { state with rip := fallthrough } := by
                  simpa [ConcreteState.write] using congrArg (fun st => st.write .rip fallthrough) hState.symm
        simp [execStmtsSuccs, hApply]
    | cons stmt stmts ih =>
        intro concrete ps summary hMatch hMem hEnabled
        rcases concrete with ⟨state, temps⟩
        rcases hMatch with ⟨hState, hTemps⟩
        cases stmt with
        | wrTmp tmp expr =>
            let ps' : PartialSummary :=
              { ps with temps := SymTempEnv.write ps.temps tmp (lowerExpr ps.sub ps.temps expr) }
            have hMatch' : PartialSummaryMatches input (execStmt (state, temps) (.wrTmp tmp expr)) ps' := by
              have hOld : LowerStateMatches input (state, temps) (ps.sub, ps.temps) := ⟨hState, hTemps⟩
              have hOld' := lowerStmt_sound input (.wrTmp tmp expr) (state, temps) (ps.sub, ps.temps) hOld
              simpa [ps', PartialSummaryMatches]
            simpa [lowerSummariesFrom, ps'] using
              ih (execStmt (state, temps) (.wrTmp tmp expr)) ps' summary hMatch' hMem hEnabled
        | put reg expr =>
            let ps' : PartialSummary :=
              { ps with sub := SymSub.write ps.sub reg (lowerExpr ps.sub ps.temps expr) }
            have hMatch' : PartialSummaryMatches input (execStmt (state, temps) (.put reg expr)) ps' := by
              have hOld : LowerStateMatches input (state, temps) (ps.sub, ps.temps) := ⟨hState, hTemps⟩
              have hOld' := lowerStmt_sound input (.put reg expr) (state, temps) (ps.sub, ps.temps) hOld
              simpa [ps', PartialSummaryMatches]
            simpa [lowerSummariesFrom, ps'] using
              ih (execStmt (state, temps) (.put reg expr)) ps' summary hMatch' hMem hEnabled
        | store64 addr value =>
            let mem := SymMem.store64 ps.sub.mem (lowerExpr ps.sub ps.temps addr) (lowerExpr ps.sub ps.temps value)
            let ps' : PartialSummary :=
              { ps with sub := SymSub.writeMem ps.sub mem }
            have hMatch' : PartialSummaryMatches input (execStmt (state, temps) (.store64 addr value)) ps' := by
              have hOld : LowerStateMatches input (state, temps) (ps.sub, ps.temps) := ⟨hState, hTemps⟩
              have hOld' := lowerStmt_sound input (.store64 addr value) (state, temps) (ps.sub, ps.temps) hOld
              simpa [ps', PartialSummaryMatches]
            simpa [lowerSummariesFrom, ps'] using
              ih (execStmt (state, temps) (.store64 addr value)) ps' summary hMatch' hMem hEnabled
        | exit cond target =>
            cases cond with
            | eq64 lhs rhs =>
                let φ := lowerCond ps.sub ps.temps (.eq64 lhs rhs)
                have hCond : (evalExpr state temps lhs == evalExpr state temps rhs) = evalSymPC input φ := by
                  simpa [evalCond, φ] using
                    lowerCond_sound input state temps ps.sub ps.temps hState hTemps (.eq64 lhs rhs)
                simp [lowerSummariesFrom] at hMem
                rcases hMem with rfl | hMem
                · have hEnabledTaken : evalSymPC input (SymPC.and ps.pc φ) = true := by
                    simpa [Summary.enabled, satisfiesSymPC] using hEnabled
                  have hParts : evalSymPC input ps.pc = true ∧ evalSymPC input φ = true := by
                    simpa [Bool.and_eq_true] using hEnabledTaken
                  have hEvalTrue : (evalExpr state temps lhs == evalExpr state temps rhs) = true := by
                    rw [hCond]
                    exact hParts.2
                  have hApply :
                      Summary.apply { sub := SymSub.write ps.sub .rip (.const target), pc := .and ps.pc φ } input =
                        { state with rip := target } := by
                    calc
                      Summary.apply { sub := SymSub.write ps.sub .rip (.const target), pc := .and ps.pc φ } input
                          = (applySymSub ps.sub input).write .rip target := by
                              simpa [Summary.apply, ConcreteState.write] using
                                (applySymSub_write ps.sub input .rip (.const target))
                      _ = { state with rip := target } := by
                            simpa [ConcreteState.write] using congrArg (fun st => st.write .rip target) hState.symm
                  simpa [execStmtsSuccs, evalCond, hEvalTrue, hApply]
                · let ps' : PartialSummary := { ps with pc := .and ps.pc (.not φ) }
                  have hPrefix' :
                      Summary.enabled { sub := ps'.sub, pc := ps'.pc } input := by
                    exact lowerSummariesFrom_prefix_enabled input fallthrough stmts ps' summary hMem hEnabled
                  have hEvalFalse : (evalExpr state temps lhs == evalExpr state temps rhs) = false := by
                    have hBoth : evalSymPC input ps.pc = true ∧ evalSymPC input (.not φ) = true := by
                      simpa [ps', Summary.enabled, satisfiesSymPC, Bool.and_eq_true] using hPrefix'
                    have hPhiFalse : evalSymPC input φ = false := by
                      simpa [evalSymPC] using hBoth.2
                    rw [hCond]
                    exact hPhiFalse
                  have hRec := ih (state, temps) ps' summary ⟨hState, hTemps⟩ hMem hEnabled
                  simpa [execStmtsSuccs, evalCond, hEvalFalse] using hRec
  exact completeFrom input block.next block.stmts (input, TempEnv.empty) PartialSummary.init summary hInit hMemList hEnabled

end VexISA
