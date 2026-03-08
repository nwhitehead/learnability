import Instances.ISAs.VexBridgeCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

@[simp] def execStmt : ConcreteState × TempEnv → Stmt → ConcreteState × TempEnv
  | cfg, .linear stmt =>
      execLinearStmt cfg stmt
  | cfg, .branch stmt =>
      execBranchContinue cfg stmt

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
      | .linear stmt =>
          execStmtsSuccs fallthrough stmts (execLinearStmt cfg stmt)
      | .branch stmt =>
          let bridge := branchStmtBridge stmt
          if bridge.fires cfg then
            { bridge.taken cfg }
          else
            execStmtsSuccs fallthrough stmts (bridge.cont cfg)

@[simp] def execBlockSuccs (block : Block) (input : ConcreteState) : Finset ConcreteState :=
  execStmtsSuccs block.next block.stmts (input, TempEnv.empty)

end VexISA
