import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

inductive SymExpr where
  | const : UInt64 → SymExpr
  | reg : Reg → SymExpr
  | add64 : SymExpr → SymExpr → SymExpr
  deriving DecidableEq, Repr

inductive SymPC where
  | true
  | eq : SymExpr → SymExpr → SymPC
  | and : SymPC → SymPC → SymPC
  | not : SymPC → SymPC
  deriving DecidableEq, Repr

abbrev SymSub := Reg → SymExpr
abbrev SymTempEnv := Nat → SymExpr

structure Summary where
  sub : SymSub
  pc : SymPC


def SymSub.id : SymSub := SymExpr.reg

def SymSub.write (sub : SymSub) (reg : Reg) (expr : SymExpr) : SymSub :=
  fun reg' => if reg' = reg then expr else sub reg'

@[simp] theorem SymSub.write_same (sub : SymSub) (reg : Reg) (expr : SymExpr) :
    SymSub.write sub reg expr reg = expr := by
  simp [SymSub.write]

@[simp] theorem SymSub.write_other (sub : SymSub) {reg reg' : Reg} (expr : SymExpr)
    (h : reg' ≠ reg) : SymSub.write sub reg expr reg' = sub reg' := by
  simp [SymSub.write, h]


def SymTempEnv.empty : SymTempEnv := fun _ => .const 0

def SymTempEnv.write (temps : SymTempEnv) (tmp : Nat) (expr : SymExpr) : SymTempEnv :=
  fun tmp' => if tmp' = tmp then expr else temps tmp'

@[simp] theorem SymTempEnv.write_same (temps : SymTempEnv) (tmp : Nat) (expr : SymExpr) :
    SymTempEnv.write temps tmp expr tmp = expr := by
  simp [SymTempEnv.write]

@[simp] theorem SymTempEnv.write_other (temps : SymTempEnv) {tmp tmp' : Nat} (expr : SymExpr)
    (h : tmp' ≠ tmp) : SymTempEnv.write temps tmp expr tmp' = temps tmp' := by
  simp [SymTempEnv.write, h]

@[simp] def evalSymExpr (state : ConcreteState) : SymExpr → UInt64
  | .const value => value
  | .reg reg => state.read reg
  | .add64 lhs rhs => evalSymExpr state lhs + evalSymExpr state rhs

@[simp] def evalSymPC (state : ConcreteState) : SymPC → Bool
  | .true => true
  | .eq lhs rhs => evalSymExpr state lhs == evalSymExpr state rhs
  | .and φ ψ => evalSymPC state φ && evalSymPC state ψ
  | .not φ => !(evalSymPC state φ)


def satisfiesSymPC (state : ConcreteState) (pc : SymPC) : Prop :=
  evalSymPC state pc = true


def substSymExpr (sub : SymSub) : SymExpr → SymExpr
  | .const value => .const value
  | .reg reg => sub reg
  | .add64 lhs rhs => .add64 (substSymExpr sub lhs) (substSymExpr sub rhs)


def substSymPC (sub : SymSub) : SymPC → SymPC
  | .true => .true
  | .eq lhs rhs => .eq (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .and φ ψ => .and (substSymPC sub φ) (substSymPC sub ψ)
  | .not φ => .not (substSymPC sub φ)


def composeSymSub (sub₁ sub₂ : SymSub) : SymSub :=
  fun reg => substSymExpr sub₁ (sub₂ reg)


def applySymSub (sub : SymSub) (state : ConcreteState) : ConcreteState :=
  { rax := evalSymExpr state (sub .rax)
  , rdi := evalSymExpr state (sub .rdi)
  , rip := evalSymExpr state (sub .rip) }

@[simp] theorem ConcreteState.read_applySymSub (sub : SymSub) (state : ConcreteState) (reg : Reg) :
    (applySymSub sub state).read reg = evalSymExpr state (sub reg) := by
  cases reg <;> rfl


def Summary.id : Summary :=
  { sub := SymSub.id, pc := .true }


def Summary.apply (summary : Summary) (state : ConcreteState) : ConcreteState :=
  applySymSub summary.sub state


def Summary.enabled (summary : Summary) (state : ConcreteState) : Prop :=
  satisfiesSymPC state summary.pc


def Summary.compose (left right : Summary) : Summary :=
  { sub := composeSymSub left.sub right.sub
  , pc := .and left.pc (substSymPC left.sub right.pc) }


theorem evalSymExpr_subst (sub : SymSub) (expr : SymExpr) (state : ConcreteState) :
    evalSymExpr state (substSymExpr sub expr) = evalSymExpr (applySymSub sub state) expr := by
  induction expr with
  | const value => rfl
  | reg reg => cases reg <;> rfl
  | add64 lhs rhs ihL ihR => simp [substSymExpr, ihL, ihR]


theorem evalSymPC_subst (sub : SymSub) (pc : SymPC) (state : ConcreteState) :
    evalSymPC state (substSymPC sub pc) = evalSymPC (applySymSub sub state) pc := by
  induction pc with
  | true => rfl
  | eq lhs rhs => simp [substSymPC, evalSymExpr_subst]
  | and φ ψ ihφ ihψ => simp [substSymPC, ihφ, ihψ]
  | not φ ih => simp [substSymPC, ih]

@[simp] theorem applySymSub_id (state : ConcreteState) :
    applySymSub SymSub.id state = state := by
  cases state
  rfl

@[simp] theorem composeSymSub_apply (sub₁ sub₂ : SymSub) (state : ConcreteState) :
    applySymSub (composeSymSub sub₁ sub₂) state = applySymSub sub₂ (applySymSub sub₁ state) := by
  cases state with
  | mk rax rdi rip =>
      simp [applySymSub, composeSymSub, evalSymExpr_subst]

end VexISA
