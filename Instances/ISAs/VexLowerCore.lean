import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexSummary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

structure PartialSummary (Reg : Type) where
  sub : SymSub Reg
  pc : SymPC Reg
  temps : SymTempEnv Reg

def PartialSummary.init {Reg : Type} : PartialSummary Reg :=
  { sub := SymSub.id
  , pc := .true
  , temps := SymTempEnv.empty }

def PartialSummary.finish {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ps : PartialSummary Reg) (ip_reg : Reg) (next : UInt64) : Summary Reg :=
  { sub := SymSub.write ps.sub ip_reg (.const next)
  , pc := ps.pc }

abbrev LowerState (Reg : Type) := SymSub Reg × SymTempEnv Reg

def lowerExpr {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (temps : SymTempEnv Reg) : Expr Reg → SymExpr Reg
  | .const value => .const value
  | .get reg => sub.regs reg
  | .tmp tmp => temps tmp
  | .low32 expr => .low32 (lowerExpr sub temps expr)
  | .uext32 expr => .uext32 (lowerExpr sub temps expr)
  | .add64 lhs rhs => .add64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .load64 addr => .load64 sub.mem (lowerExpr sub temps addr)

def lowerCond {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (temps : SymTempEnv Reg) : Cond Reg → SymPC Reg
  | .eq64 lhs rhs => .eq (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)

end VexISA
