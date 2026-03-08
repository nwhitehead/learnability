import Mathlib.Data.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

abbrev ByteCell := UInt64 × UInt8
abbrev ByteMem := List ByteCell

def ByteMem.empty : ByteMem := []

def ByteMem.eraseAddr (mem : ByteMem) (addr : UInt64) : ByteMem :=
  mem.filter (fun cell => cell.1 ≠ addr)

@[simp] def ByteMem.readByte : ByteMem → UInt64 → UInt8
  | [], _ => 0
  | (cellAddr, value) :: rest, addr =>
      if cellAddr = addr then value else ByteMem.readByte rest addr

def ByteMem.writeByte (mem : ByteMem) (addr : UInt64) (value : UInt8) : ByteMem :=
  (addr, value) :: ByteMem.eraseAddr mem addr

private def ByteMem.read64leAux (mem : ByteMem) (addr : UInt64) : Nat → UInt64
  | 0 => 0
  | n + 1 =>
      let rest := ByteMem.read64leAux mem addr n
      let byte := UInt64.ofNat ((ByteMem.readByte mem (addr + UInt64.ofNat n)).toNat)
      rest ||| UInt64.shiftLeft byte (UInt64.ofNat (8 * n))

def ByteMem.read64le (mem : ByteMem) (addr : UInt64) : UInt64 :=
  ByteMem.read64leAux mem addr 8

private def ByteMem.write64leAux (mem : ByteMem) (addr value : UInt64) : Nat → ByteMem
  | 0 => mem
  | n + 1 =>
      let shifted := UInt64.shiftRight value (UInt64.ofNat (8 * n))
      let byte := UInt8.ofNat (UInt64.toNat shifted)
      ByteMem.write64leAux (ByteMem.writeByte mem (addr + UInt64.ofNat n) byte) addr value n

def ByteMem.write64le (mem : ByteMem) (addr value : UInt64) : ByteMem :=
  ByteMem.write64leAux mem addr value 8

inductive Reg where
  | rax
  | rcx
  | rdi
  | rip
  deriving DecidableEq, Repr

inductive Expr where
  | const : UInt64 → Expr
  | get : Reg → Expr
  | tmp : Nat → Expr
  | add64 : Expr → Expr → Expr
  | load64 : Expr → Expr
  deriving DecidableEq, Repr

inductive Cond where
  | eq64 : Expr → Expr → Cond
  deriving DecidableEq, Repr

inductive Stmt where
  | wrTmp : Nat → Expr → Stmt
  | put : Reg → Expr → Stmt
  | store64 : Expr → Expr → Stmt
  | exit : Cond → UInt64 → Stmt
  deriving DecidableEq, Repr

structure Block where
  stmts : List Stmt
  next : UInt64
  deriving DecidableEq, Repr

structure ConcreteState where
  rax : UInt64
  rcx : UInt64
  rdi : UInt64
  rip : UInt64
  mem : ByteMem
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
  | .rcx => state.rcx
  | .rdi => state.rdi
  | .rip => state.rip

@[simp] def ConcreteState.write (state : ConcreteState) (reg : Reg) (value : UInt64) : ConcreteState :=
  match reg with
  | .rax => { state with rax := value }
  | .rcx => { state with rcx := value }
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
  | .load64 addr => ByteMem.read64le state.mem (evalExpr state temps addr)

@[simp] def evalCond (state : ConcreteState) (temps : TempEnv) : Cond → Bool
  | .eq64 lhs rhs => evalExpr state temps lhs == evalExpr state temps rhs

@[simp] def execStmt : ConcreteState × TempEnv → Stmt → ConcreteState × TempEnv
  | (state, temps), .wrTmp tmp expr => (state, temps.write tmp (evalExpr state temps expr))
  | (state, temps), .put reg expr => (state.write reg (evalExpr state temps expr), temps)
  | (state, temps), .store64 addr value =>
      ({ state with mem := ByteMem.write64le state.mem (evalExpr state temps addr) (evalExpr state temps value) }, temps)
  | (state, temps), .exit _cond _target => (state, temps)

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
      | .wrTmp _ _ =>
          execStmtsSuccs fallthrough stmts (execStmt cfg stmt)
      | .put _ _ =>
          execStmtsSuccs fallthrough stmts (execStmt cfg stmt)
      | .store64 _ _ =>
          execStmtsSuccs fallthrough stmts (execStmt cfg stmt)
      | .exit cond target =>
          let state := cfg.1
          let temps := cfg.2
          if evalCond state temps cond then
            { { state with rip := target } }
          else
            execStmtsSuccs fallthrough stmts cfg

@[simp] def execBlockSuccs (block : Block) (input : ConcreteState) : Finset ConcreteState :=
  execStmtsSuccs block.next block.stmts (input, TempEnv.empty)

end VexISA
