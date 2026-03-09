import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexSummary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

def pcOr {Reg : Type} (φ ψ : SymPC Reg) : SymPC Reg :=
  .not (.and (.not φ) (.not ψ))

def lowerAmd64CalculateConditionZero {Reg : Type}
    (ccOp ccDep1 ccDep2 : SymExpr Reg) : SymPC Reg :=
  let addCase : SymPC Reg :=
    .and (.eq ccOp (.const 0x3))
      (.eq (.uext32 (.add64 (.low32 ccDep1) (.low32 ccDep2))) (.const 0))
  let subCase : SymPC Reg :=
    .and (.eq ccOp (.const 0x7))
      (.eq (.low32 ccDep1) (.low32 ccDep2))
  let logicCase : SymPC Reg :=
    .and (.eq ccOp (.const 0x13))
      (.eq (.low32 ccDep1) (.const 0))
  pcOr addCase (pcOr subCase logicCase)

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
  | .narrow32 expr => .low32 (lowerExpr sub temps expr)
  | .zext64 expr => .uext32 (lowerExpr sub temps expr)
  | .add32 lhs rhs => .uext32 (.add64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs))
  | .add64 lhs rhs => .add64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .sub64 lhs rhs => .sub64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .load64 addr => .load64 sub.mem (lowerExpr sub temps addr)

def lowerCond {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (temps : SymTempEnv Reg) : Cond Reg → SymPC Reg
  | .eq64 lhs rhs => .eq (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .lt64 lhs rhs => .lt (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .le64 lhs rhs => .le (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .amd64CalculateCondition code ccOp ccDep1 ccDep2 _ccNdep =>
      if code = 0x4 then
        lowerAmd64CalculateConditionZero
          (lowerExpr sub temps ccOp)
          (lowerExpr sub temps ccDep1)
          (lowerExpr sub temps ccDep2)
      else
        .not .true

end VexISA
