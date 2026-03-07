set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

inductive Reg where
  | rax
  | rdi
  | rip
  deriving DecidableEq, Repr

inductive Expr where
  | const : UInt64 → Expr
  | get : Reg → Expr
  | tmp : Nat → Expr
  | add64 : Expr → Expr → Expr
  deriving DecidableEq, Repr

inductive Stmt where
  | wrTmp : Nat → Expr → Stmt
  | put : Reg → Expr → Stmt
  deriving DecidableEq, Repr

structure Block where
  stmts : List Stmt
  next : UInt64
  deriving DecidableEq, Repr

structure ConcreteState where
  rax : UInt64
  rdi : UInt64
  rip : UInt64
  deriving DecidableEq, Repr

abbrev TempEnv := Nat → UInt64

def TempEnv.empty : TempEnv := fun _ => 0

def TempEnv.write (temps : TempEnv) (tmp : Nat) (value : UInt64) : TempEnv :=
  fun tmp' => if tmp' = tmp then value else temps tmp'

@[simp] theorem TempEnv.write_same (temps : TempEnv) (tmp : Nat) (value : UInt64) :
    TempEnv.write temps tmp value tmp = value := by
  simp [TempEnv.write]

@[simp] theorem TempEnv.write_other (temps : TempEnv) {tmp tmp' : Nat} (value : UInt64)
    (h : tmp' ≠ tmp) : TempEnv.write temps tmp value tmp' = temps tmp' := by
  simp [TempEnv.write, h]

@[simp] def ConcreteState.read (state : ConcreteState) : Reg → UInt64
  | .rax => state.rax
  | .rdi => state.rdi
  | .rip => state.rip

@[simp] def ConcreteState.write (state : ConcreteState) (reg : Reg) (value : UInt64) : ConcreteState :=
  match reg with
  | .rax => { state with rax := value }
  | .rdi => { state with rdi := value }
  | .rip => { state with rip := value }

@[simp] theorem ConcreteState.read_write_same (state : ConcreteState) (reg : Reg) (value : UInt64) :
    (state.write reg value).read reg = value := by
  cases reg <;> rfl

@[simp] theorem ConcreteState.read_write_other (state : ConcreteState) {reg reg' : Reg}
    (value : UInt64) (h : reg' ≠ reg) : (state.write reg value).read reg' = state.read reg' := by
  cases reg <;> cases reg' <;> first | cases (h rfl) | rfl

@[simp] def evalExpr (state : ConcreteState) (temps : TempEnv) : Expr → UInt64
  | .const value => value
  | .get reg => state.read reg
  | .tmp tmp => temps tmp
  | .add64 lhs rhs => evalExpr state temps lhs + evalExpr state temps rhs

@[simp] def execStmt : ConcreteState × TempEnv → Stmt → ConcreteState × TempEnv
  | (state, temps), .wrTmp tmp expr => (state, temps.write tmp (evalExpr state temps expr))
  | (state, temps), .put reg expr => (state.write reg (evalExpr state temps expr), temps)

@[simp] def execBlock (block : Block) (input : ConcreteState) : ConcreteState :=
  let (state, _) := block.stmts.foldl execStmt (input, TempEnv.empty)
  { state with rip := block.next }

end VexISA
