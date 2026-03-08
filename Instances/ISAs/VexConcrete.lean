import Instances.ISAs.VexSyntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

@[simp] def evalExpr (state : ConcreteState) (temps : TempEnv) : Expr → UInt64
  | .const value => value
  | .get reg => state.read reg
  | .tmp tmp => temps tmp
  | .add64 lhs rhs => evalExpr state temps lhs + evalExpr state temps rhs
  | .load64 addr => ByteMem.read64le state.mem (evalExpr state temps addr)

@[simp] def evalCond (state : ConcreteState) (temps : TempEnv) : Cond → Bool
  | .eq64 lhs rhs => evalExpr state temps lhs == evalExpr state temps rhs

end VexISA
