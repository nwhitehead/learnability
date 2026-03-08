import Instances.ISAs.VexBridgeCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

def lowerStmt : LowerState → Stmt → LowerState
  | state, .linear stmt =>
      lowerLinearStmt state stmt
  | state, .branch stmt =>
      lowerBranchContinue state stmt

def lowerStmts (stmts : List Stmt) : LowerState :=
  stmts.foldl lowerStmt (SymSub.id, SymTempEnv.empty)

def lowerBlockSub (block : Block) : SymSub :=
  SymSub.write (lowerStmts block.stmts).1 .rip (.const block.next)

def lowerBlock (block : Block) : Summary :=
  { sub := lowerBlockSub block
  , pc := .true }

def lowerSummariesFrom (ps : PartialSummary) : List Stmt → UInt64 → List Summary
  | [], next =>
      [ps.finish next]
  | .linear stmt :: stmts, next =>
      let lowered := lowerLinearStmt (ps.sub, ps.temps) stmt
      lowerSummariesFrom
        { ps with sub := lowered.1, temps := lowered.2 }
        stmts next
  | .branch stmt :: stmts, next =>
      let bridge := branchStmtBridge stmt
      bridge.lowerTaken ps ::
      lowerSummariesFrom (bridge.lowerContinue ps) stmts next

def lowerBlockSummariesList (block : Block) : List Summary :=
  lowerSummariesFrom PartialSummary.init block.stmts block.next

def lowerBlockSummaries (block : Block) : Finset Summary :=
  (lowerBlockSummariesList block).toFinset

end VexISA
