import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexSyntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

def evalAmd64CalculateConditionZero
    (ccOp ccDep1 ccDep2 _ccNdep : UInt64) : Bool :=
  if ccOp = 0x3 then
    mask32 (mask32 ccDep1 + mask32 ccDep2) == 0
  else if ccOp = 0x7 then
    mask32 ccDep1 == mask32 ccDep2
  else if ccOp = 0x13 then
    mask32 ccDep1 == 0
  else
    false

@[simp] def evalExpr {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (temps : TempEnv) : Expr Reg → UInt64
  | .const value => value
  | .get reg => state.read reg
  | .tmp tmp => temps tmp
  | .narrow32 expr => mask32 (evalExpr state temps expr)
  | .zext64 expr => mask32 (evalExpr state temps expr)
  | .add32 lhs rhs => mask32 (evalExpr state temps lhs + evalExpr state temps rhs)
  | .add64 lhs rhs => evalExpr state temps lhs + evalExpr state temps rhs
  | .sub64 lhs rhs => evalExpr state temps lhs - evalExpr state temps rhs
  | .load64 addr => ByteMem.read64le state.mem (evalExpr state temps addr)

@[simp] def evalCond {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (temps : TempEnv) : Cond Reg → Bool
  | .eq64 lhs rhs => evalExpr state temps lhs == evalExpr state temps rhs
  | .lt64 lhs rhs => decide (evalExpr state temps lhs < evalExpr state temps rhs)
  | .le64 lhs rhs => decide (evalExpr state temps lhs ≤ evalExpr state temps rhs)
  | .amd64CalculateCondition code ccOp ccDep1 ccDep2 ccNdep =>
      if code = 0x4 then
        evalAmd64CalculateConditionZero
          (evalExpr state temps ccOp)
          (evalExpr state temps ccDep1)
          (evalExpr state temps ccDep2)
          (evalExpr state temps ccNdep)
      else
        false

end VexISA
