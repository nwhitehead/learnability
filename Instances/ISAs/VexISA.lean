import Instances.ISAs.VexConcrete

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

@[simp] def execStmt : ConcreteState × TempEnv → Stmt → ConcreteState × TempEnv
  | (state, temps), .linear (.wrTmp tmp expr) =>
      (state, temps.write tmp (evalExpr state temps expr))
  | (state, temps), .linear (.put reg expr) =>
      (state.write reg (evalExpr state temps expr), temps)
  | (state, temps), .linear (.store64 addr value) =>
      ({ state with mem := ByteMem.write64le state.mem (evalExpr state temps addr) (evalExpr state temps value) }, temps)
  | (state, temps), .branch (.exit _cond _target) =>
      (state, temps)

@[simp] def execBlock (block : Block) (input : ConcreteState) : ConcreteState :=
  let (state, _) := block.stmts.foldl execStmt (input, TempEnv.empty)
  { state with rip := block.next }

/-- Ordered concrete successor semantics for the current VEX block slice.

`Exit` short-circuits: the first enabled exit wins and fallthrough is discarded.
The `Finset` result is for alignment with summary families, not to model
general nondeterministic CFG branching. -/
@[simp] def execStmtsSuccs (fallthrough : UInt64) :
    List Stmt → ConcreteState × TempEnv → Finset ConcreteState
  | [], (state, _) =>
      { { state with rip := fallthrough } }
  | stmt :: stmts, cfg =>
      match stmt with
      | .linear _ =>
          execStmtsSuccs fallthrough stmts (execStmt cfg stmt)
      | .branch (.exit cond target) =>
          let state := cfg.1
          let temps := cfg.2
          if evalCond state temps cond then
            { { state with rip := target } }
          else
            execStmtsSuccs fallthrough stmts cfg

@[simp] def execBlockSuccs (block : Block) (input : ConcreteState) : Finset ConcreteState :=
  execStmtsSuccs block.next block.stmts (input, TempEnv.empty)

end VexISA
