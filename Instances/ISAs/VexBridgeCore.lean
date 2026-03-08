import Instances.ISAs.VexISA
import Instances.ISAs.VexLowering

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-- Public bridge invariant relating a concrete threaded state to symbolic substitutions and temps. -/
def BridgeInvariant (input : ConcreteState)
    (concrete : ConcreteState × TempEnv) (sub : SymSub) (temps : SymTempEnv) : Prop :=
  concrete.1 = applySymSub sub input ∧
    ∀ tmp, concrete.2 tmp = evalSymExpr input (temps tmp)

abbrev LowerStateMatches (input : ConcreteState)
    (concrete : ConcreteState × TempEnv) (symbolic : LowerState) : Prop :=
  BridgeInvariant input concrete symbolic.1 symbolic.2

abbrev PartialSummaryMatches (input : ConcreteState)
    (concrete : ConcreteState × TempEnv) (ps : PartialSummary) : Prop :=
  BridgeInvariant input concrete ps.sub ps.temps

structure LinearStmtBridgeCase (stmt : LinearStmt) where
  exec : ConcreteState × TempEnv → ConcreteState × TempEnv
  lower : LowerState → LowerState
  sound :
    ∀ input concrete symbolic,
      LowerStateMatches input concrete symbolic →
      LowerStateMatches input (exec concrete) (lower symbolic)

structure BranchStmtBridgeCase (stmt : BranchStmt) where
  fires : ConcreteState × TempEnv → Bool
  taken : ConcreteState × TempEnv → ConcreteState
  lowerGuard : PartialSummary → SymPC
  lowerTaken : PartialSummary → Summary
  lowerContinue : PartialSummary → PartialSummary
  fires_iff_guard :
    ∀ input concrete ps,
      PartialSummaryMatches input concrete ps →
      fires concrete = evalSymPC input (lowerGuard ps)
  taken_sound :
    ∀ input concrete ps,
      PartialSummaryMatches input concrete ps →
      fires concrete = true →
      Summary.apply (lowerTaken ps) input = taken concrete
  continue_matches :
    ∀ input concrete ps,
      PartialSummaryMatches input concrete ps →
      fires concrete = false →
      PartialSummaryMatches input concrete (lowerContinue ps)
  taken_pc_implies_parent :
    ∀ ps input,
      Summary.enabled (lowerTaken ps) input →
      Summary.enabled { sub := ps.sub, pc := ps.pc } input
  continue_pc_implies_parent :
    ∀ ps input,
      Summary.enabled { sub := (lowerContinue ps).sub, pc := (lowerContinue ps).pc } input →
      Summary.enabled { sub := ps.sub, pc := ps.pc } input

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

private theorem lowerCond_sound
    (input state : ConcreteState) (temps : TempEnv) (sub : SymSub) (symTemps : SymTempEnv)
    (hState : state = applySymSub sub input)
    (hTemps : ∀ tmp, temps tmp = evalSymExpr input (symTemps tmp))
    (cond : Cond) :
    evalCond state temps cond = evalSymPC input (lowerCond sub symTemps cond) := by
  cases cond with
  | eq64 lhs rhs =>
      simp [lowerCond,
        lowerExpr_sound input state temps sub symTemps hState hTemps lhs,
        lowerExpr_sound input state temps sub symTemps hState hTemps rhs]

private theorem applySymSub_writeMem (sub : SymSub) (input : ConcreteState) (mem : SymMem) :
    applySymSub (SymSub.writeMem sub mem) input =
      { applySymSub sub input with mem := evalSymMem input mem } := by
  cases input
  rfl

private theorem applySymSub_write (sub : SymSub) (input : ConcreteState) (reg : Reg) (expr : SymExpr) :
    applySymSub (SymSub.write sub reg expr) input =
      (applySymSub sub input).write reg (evalSymExpr input expr) := by
  cases reg <;> cases input <;> rfl

@[inline] def linearStmtBridge : (stmt : LinearStmt) → LinearStmtBridgeCase stmt
  | .wrTmp tmp expr =>
      { exec := fun cfg =>
          match cfg with
          | (state, temps) => (state, temps.write tmp (evalExpr state temps expr))
        lower := fun symbolic =>
          match symbolic with
          | (sub, temps) => (sub, SymTempEnv.write temps tmp (lowerExpr sub temps expr))
        sound := by
          intro input concrete symbolic hMatch
          rcases concrete with ⟨state, temps⟩
          rcases symbolic with ⟨sub, symTemps⟩
          rcases hMatch with ⟨hState, hTemps⟩
          constructor
          · simpa using hState
          · intro tmp'
            by_cases h : tmp' = tmp
            · subst h
              have hExpr := lowerExpr_sound input state temps sub symTemps hState hTemps expr
              simp [hExpr]
            · simpa [SymTempEnv.write, TempEnv.write, h] using hTemps tmp' }
  | .put reg expr =>
      { exec := fun cfg =>
          match cfg with
          | (state, temps) => (state.write reg (evalExpr state temps expr), temps)
        lower := fun symbolic =>
          match symbolic with
          | (sub, temps) => (SymSub.write sub reg (lowerExpr sub temps expr), temps)
        sound := by
          intro input concrete symbolic hMatch
          rcases concrete with ⟨state, temps⟩
          rcases symbolic with ⟨sub, symTemps⟩
          rcases hMatch with ⟨hState, hTemps⟩
          constructor
          · subst hState
            have hExpr := lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps expr
            cases reg <;>
              simpa [applySymSub, SymSub.write] using hExpr
          · intro tmp
            simpa using hTemps tmp }
  | .store64 addr value =>
      { exec := fun cfg =>
          match cfg with
          | (state, temps) =>
              ({ state with mem := ByteMem.write64le state.mem (evalExpr state temps addr) (evalExpr state temps value) }, temps)
        lower := fun symbolic =>
          match symbolic with
          | (sub, temps) =>
              let mem := SymMem.store64 sub.mem (lowerExpr sub temps addr) (lowerExpr sub temps value)
              (SymSub.writeMem sub mem, temps)
        sound := by
          intro input concrete symbolic hMatch
          rcases concrete with ⟨state, temps⟩
          rcases symbolic with ⟨sub, symTemps⟩
          rcases hMatch with ⟨hState, hTemps⟩
          constructor
          · subst hState
            have hAddr := lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps addr
            have hValue := lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps value
            cases hSub : applySymSub sub input with
            | mk rax rcx rdi rip mem =>
                rw [hSub] at hAddr hValue
                simp [applySymSub] at hSub
                rcases hSub with ⟨hRax, hRcx, hRdi, hRip, hMem⟩
                simp [applySymSub, SymSub.writeMem, hAddr, hValue, hRax, hRcx, hRdi, hRip, hMem]
          · intro tmp
            simpa using hTemps tmp }

@[inline] def execLinearStmt (cfg : ConcreteState × TempEnv) (stmt : LinearStmt) : ConcreteState × TempEnv :=
  (linearStmtBridge stmt).exec cfg

@[inline] def lowerLinearStmt (state : LowerState) (stmt : LinearStmt) : LowerState :=
  (linearStmtBridge stmt).lower state

@[inline] def branchStmtBridge : (stmt : BranchStmt) → BranchStmtBridgeCase stmt
  | .exit cond target =>
      { fires := fun concrete => evalCond concrete.1 concrete.2 cond
        taken := fun concrete => { concrete.1 with rip := target }
        lowerGuard := fun ps => lowerCond ps.sub ps.temps cond
        lowerTaken := fun ps =>
          { sub := SymSub.write ps.sub .rip (.const target)
          , pc := .and ps.pc (lowerCond ps.sub ps.temps cond) }
        lowerContinue := fun ps =>
          { ps with pc := .and ps.pc (.not (lowerCond ps.sub ps.temps cond)) }
        fires_iff_guard := by
          intro input concrete ps hMatch
          rcases concrete with ⟨state, temps⟩
          rcases hMatch with ⟨hState, hTemps⟩
          simpa using lowerCond_sound input state temps ps.sub ps.temps hState hTemps cond
        taken_sound := by
          intro input concrete ps hMatch hFires
          rcases concrete with ⟨state, temps⟩
          rcases hMatch with ⟨hState, hTemps⟩
          cases cond with
          | eq64 lhs rhs =>
              have hApply :
                  Summary.apply { sub := SymSub.write ps.sub .rip (.const target), pc := .and ps.pc (lowerCond ps.sub ps.temps (.eq64 lhs rhs)) } input =
                    { state with rip := target } := by
                calc
                  Summary.apply { sub := SymSub.write ps.sub .rip (.const target), pc := .and ps.pc (lowerCond ps.sub ps.temps (.eq64 lhs rhs)) } input
                      = (applySymSub ps.sub input).write .rip target := by
                          simpa [Summary.apply, ConcreteState.write] using
                            (applySymSub_write ps.sub input .rip (.const target))
                  _ = { state with rip := target } := by
                        simpa [ConcreteState.write] using congrArg (fun st => st.write .rip target) hState.symm
              simpa using hApply
        continue_matches := by
          intro input concrete ps hMatch _hFires
          simpa [PartialSummaryMatches, BridgeInvariant]
        taken_pc_implies_parent := by
          intro ps input hEnabled
          rw [Summary.enabled, satisfiesSymPC, evalSymPC] at hEnabled
          have hBoth : evalSymPC input ps.pc = true ∧ evalSymPC input (lowerCond ps.sub ps.temps cond) = true := by
            simpa [Bool.and_eq_true] using hEnabled
          simpa [Summary.enabled, satisfiesSymPC] using hBoth.1
        continue_pc_implies_parent := by
          intro ps input hEnabled
          rw [Summary.enabled, satisfiesSymPC, evalSymPC] at hEnabled
          have hBoth : evalSymPC input ps.pc = true ∧ evalSymPC input (.not (lowerCond ps.sub ps.temps cond)) = true := by
            simpa [Bool.and_eq_true] using hEnabled
          simpa [Summary.enabled, satisfiesSymPC] using hBoth.1 }

example :
    (branchStmtBridge (.exit (.eq64 (.get .rcx) (.const 0)) 0x400006)).fires
      ({ rax := 0, rcx := 0, rdi := 0, rip := 0, mem := ByteMem.empty }, TempEnv.empty) = true := by
  native_decide

end VexISA
