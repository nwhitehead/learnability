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

end VexISA
