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

abbrev LowerState := SymSub × SymTempEnv

def lowerExpr (sub : SymSub) (temps : SymTempEnv) : Expr → SymExpr
  | .const value => .const value
  | .get reg => sub.regs reg
  | .tmp tmp => temps tmp
  | .add64 lhs rhs => .add64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .load64 addr => .load64 sub.mem (lowerExpr sub temps addr)

def lowerCond (sub : SymSub) (temps : SymTempEnv) : Cond → SymPC
  | .eq64 lhs rhs => .eq (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)

end VexISA
