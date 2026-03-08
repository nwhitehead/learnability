import Instances.ISAs.VexSummary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

structure PartialSummary where
  sub : SymSub
  pc : SymPC
  temps : SymTempEnv

def PartialSummary.init : PartialSummary :=
  { sub := SymSub.id
  , pc := .true
  , temps := SymTempEnv.empty }

def PartialSummary.finish (ps : PartialSummary) (next : UInt64) : Summary :=
  { sub := SymSub.write ps.sub .rip (.const next)
  , pc := ps.pc }

def lowerExpr (sub : SymSub) (temps : SymTempEnv) : Expr → SymExpr
  | .const value => .const value
  | .get reg => sub.regs reg
  | .tmp tmp => temps tmp
  | .add64 lhs rhs => .add64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .load64 addr => .load64 sub.mem (lowerExpr sub temps addr)

def lowerCond (sub : SymSub) (temps : SymTempEnv) : Cond → SymPC
  | .eq64 lhs rhs => .eq (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)

abbrev LowerState := SymSub × SymTempEnv


def lowerStmt : LowerState → Stmt → LowerState
  | (sub, temps), .wrTmp tmp expr =>
      (sub, SymTempEnv.write temps tmp (lowerExpr sub temps expr))
  | (sub, temps), .put reg expr =>
      (SymSub.write sub reg (lowerExpr sub temps expr), temps)
  | (sub, temps), .exit _cond _target =>
      (sub, temps)


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
  | .wrTmp tmp expr :: stmts, next =>
      lowerSummariesFrom
        { ps with temps := SymTempEnv.write ps.temps tmp (lowerExpr ps.sub ps.temps expr) }
        stmts next
  | .put reg expr :: stmts, next =>
      lowerSummariesFrom
        { ps with sub := SymSub.write ps.sub reg (lowerExpr ps.sub ps.temps expr) }
        stmts next
  | .exit cond target :: stmts, next =>
      let φ := lowerCond ps.sub ps.temps cond
      { sub := SymSub.write ps.sub .rip (.const target)
      , pc := .and ps.pc φ } ::
      lowerSummariesFrom
        { ps with pc := .and ps.pc (.not φ) }
        stmts next

def lowerBlockSummariesList (block : Block) : List Summary :=
  lowerSummariesFrom PartialSummary.init block.stmts block.next

def lowerBlockSummaries (block : Block) : Finset Summary :=
  (lowerBlockSummariesList block).toFinset

end VexISA
