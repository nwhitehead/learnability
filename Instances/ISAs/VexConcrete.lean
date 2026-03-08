import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexSyntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

@[simp] def evalExpr {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (temps : TempEnv) : Expr Reg → UInt64
  | .const value => value
  | .get reg => state.read reg
  | .tmp tmp => temps tmp
  | .low32 expr => mask32 (evalExpr state temps expr)
  | .uext32 expr => mask32 (evalExpr state temps expr)
  | .add64 lhs rhs => evalExpr state temps lhs + evalExpr state temps rhs
  | .load64 addr => ByteMem.read64le state.mem (evalExpr state temps addr)

@[simp] def evalCond {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (temps : TempEnv) : Cond Reg → Bool
  | .eq64 lhs rhs => evalExpr state temps lhs == evalExpr state temps rhs

end VexISA
