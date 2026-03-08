import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexSyntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

mutual
inductive SymExpr (Reg : Type) where
  | const : UInt64 → SymExpr Reg
  | reg : Reg → SymExpr Reg
  | add64 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | load64 : SymMem Reg → SymExpr Reg → SymExpr Reg
  deriving DecidableEq, Repr

inductive SymMem (Reg : Type) where
  | base
  | store64 : SymMem Reg → SymExpr Reg → SymExpr Reg → SymMem Reg
  deriving DecidableEq, Repr
end

inductive SymPC (Reg : Type) where
  | true
  | eq : SymExpr Reg → SymExpr Reg → SymPC Reg
  | and : SymPC Reg → SymPC Reg → SymPC Reg
  | not : SymPC Reg → SymPC Reg
  deriving DecidableEq, Repr

structure SymSub (Reg : Type) where
  regs : Reg → SymExpr Reg
  mem : SymMem Reg

instance {Reg : Type} [DecidableEq Reg] [Fintype Reg] : DecidableEq (SymSub Reg) := by
  intro sub₁ sub₂
  by_cases hRegs : sub₁.regs = sub₂.regs
  · by_cases hMem : sub₁.mem = sub₂.mem
    · cases sub₁
      cases sub₂
      cases hRegs
      cases hMem
      exact isTrue rfl
    · exact isFalse (fun h => hMem (congrArg SymSub.mem h))
  · exact isFalse (fun h => hRegs (congrArg SymSub.regs h))

abbrev SymTempEnv (Reg : Type) := Nat → SymExpr Reg

structure Summary (Reg : Type) where
  sub : SymSub Reg
  pc : SymPC Reg

instance {Reg : Type} [DecidableEq Reg] [Fintype Reg] : DecidableEq (Summary Reg) := by
  intro summary₁ summary₂
  by_cases hSub : summary₁.sub = summary₂.sub
  · by_cases hPc : summary₁.pc = summary₂.pc
    · cases summary₁
      cases summary₂
      cases hSub
      cases hPc
      exact isTrue rfl
    · exact isFalse (fun h => hPc (congrArg Summary.pc h))
  · exact isFalse (fun h => hSub (congrArg Summary.sub h))

@[ext] theorem SymSub.ext {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {sub₁ sub₂ : SymSub Reg}
    (hRegs : sub₁.regs = sub₂.regs) (hMem : sub₁.mem = sub₂.mem) :
    sub₁ = sub₂ := by
  cases sub₁
  cases sub₂
  cases hRegs
  cases hMem
  rfl


def SymSub.id {Reg : Type} : SymSub Reg :=
  { regs := SymExpr.reg
  , mem := .base }


def SymSub.write {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (reg : Reg) (expr : SymExpr Reg) : SymSub Reg :=
  { sub with regs := fun reg' => if reg' = reg then expr else sub.regs reg' }


def SymSub.writeMem {Reg : Type} (sub : SymSub Reg) (mem : SymMem Reg) : SymSub Reg :=
  { sub with mem := mem }

@[simp] theorem SymSub.write_same {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (reg : Reg) (expr : SymExpr Reg) :
    (SymSub.write sub reg expr).regs reg = expr := by
  simp [SymSub.write]

@[simp] theorem SymSub.write_other {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) {reg reg' : Reg} (expr : SymExpr Reg)
    (h : reg' ≠ reg) : (SymSub.write sub reg expr).regs reg' = sub.regs reg' := by
  simp [SymSub.write, h]


def SymTempEnv.empty {Reg : Type} : SymTempEnv Reg := fun _ => .const 0

def SymTempEnv.write {Reg : Type}
    (temps : SymTempEnv Reg) (tmp : Nat) (expr : SymExpr Reg) : SymTempEnv Reg :=
  fun tmp' => if tmp' = tmp then expr else temps tmp'

@[simp] theorem SymTempEnv.write_same {Reg : Type}
    (temps : SymTempEnv Reg) (tmp : Nat) (expr : SymExpr Reg) :
    SymTempEnv.write temps tmp expr tmp = expr := by
  simp [SymTempEnv.write]

@[simp] theorem SymTempEnv.write_other {Reg : Type}
    (temps : SymTempEnv Reg) {tmp tmp' : Nat} (expr : SymExpr Reg)
    (h : tmp' ≠ tmp) : SymTempEnv.write temps tmp expr tmp' = temps tmp' := by
  simp [SymTempEnv.write, h]

mutual
@[simp] def evalSymExpr {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) : SymExpr Reg → UInt64
  | .const value => value
  | .reg reg => state.read reg
  | .add64 lhs rhs => evalSymExpr state lhs + evalSymExpr state rhs
  | .load64 mem addr => ByteMem.read64le (evalSymMem state mem) (evalSymExpr state addr)

@[simp] def evalSymMem {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) : SymMem Reg → ByteMem
  | .base => state.mem
  | .store64 mem addr value =>
      ByteMem.write64le (evalSymMem state mem) (evalSymExpr state addr) (evalSymExpr state value)
end

@[simp] def evalSymPC {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) : SymPC Reg → Bool
  | .true => true
  | .eq lhs rhs => evalSymExpr state lhs == evalSymExpr state rhs
  | .and φ ψ => evalSymPC state φ && evalSymPC state ψ
  | .not φ => !(evalSymPC state φ)


def satisfiesSymPC {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (pc : SymPC Reg) : Prop :=
  evalSymPC state pc = true

mutual
def substSymExpr {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) : SymExpr Reg → SymExpr Reg
  | .const value => .const value
  | .reg reg => sub.regs reg
  | .add64 lhs rhs => .add64 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .load64 mem addr => .load64 (substSymMem sub mem) (substSymExpr sub addr)

def substSymMem {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) : SymMem Reg → SymMem Reg
  | .base => sub.mem
  | .store64 mem addr value => .store64 (substSymMem sub mem) (substSymExpr sub addr) (substSymExpr sub value)
end


def substSymPC {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) : SymPC Reg → SymPC Reg
  | .true => .true
  | .eq lhs rhs => .eq (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .and φ ψ => .and (substSymPC sub φ) (substSymPC sub ψ)
  | .not φ => .not (substSymPC sub φ)


def composeSymSub {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub₁ sub₂ : SymSub Reg) : SymSub Reg :=
  { regs := fun reg => substSymExpr sub₁ (sub₂.regs reg)
  , mem := substSymMem sub₁ sub₂.mem }


def applySymSub {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (state : ConcreteState Reg) : ConcreteState Reg :=
  { regs := fun reg => evalSymExpr state (sub.regs reg)
  , mem := evalSymMem state sub.mem }

theorem applySymSub_write {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (input : ConcreteState Reg) (reg : Reg) (expr : SymExpr Reg) :
    applySymSub (SymSub.write sub reg expr) input =
      (applySymSub sub input).write reg (evalSymExpr input expr) := by
  apply ConcreteState.ext
  · funext reg'
    by_cases h : reg' = reg
    · subst h
      simp [applySymSub, SymSub.write, ConcreteState.write]
    · simp [applySymSub, SymSub.write, ConcreteState.write, h]
  · rfl

@[simp] theorem ConcreteState.read_applySymSub {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (state : ConcreteState Reg) (reg : Reg) :
    (applySymSub sub state).read reg = evalSymExpr state (sub.regs reg) := by
  rfl


def Summary.id {Reg : Type} : Summary Reg :=
  { sub := SymSub.id
  , pc := .true }


def Summary.apply {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : Summary Reg) (state : ConcreteState Reg) : ConcreteState Reg :=
  applySymSub summary.sub state


def Summary.enabled {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : Summary Reg) (state : ConcreteState Reg) : Prop :=
  satisfiesSymPC state summary.pc


def Summary.compose {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (left right : Summary Reg) : Summary Reg :=
  { sub := composeSymSub left.sub right.sub
  , pc := .and left.pc (substSymPC left.sub right.pc) }

mutual
theorem substSymExpr_id {Reg : Type} [DecidableEq Reg] [Fintype Reg] (expr : SymExpr Reg) :
    substSymExpr SymSub.id expr = expr := by
  cases expr with
  | const value => rfl
  | reg reg => rfl
  | add64 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | load64 mem addr =>
      simp [substSymExpr, substSymMem_id, substSymExpr_id]

theorem substSymMem_id {Reg : Type} [DecidableEq Reg] [Fintype Reg] (mem : SymMem Reg) :
    substSymMem SymSub.id mem = mem := by
  cases mem with
  | base => rfl
  | store64 mem addr value =>
      simp [substSymMem, substSymMem_id, substSymExpr_id]
end

mutual
theorem substSymExpr_compose {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub₁ sub₂ : SymSub Reg) (expr : SymExpr Reg) :
    substSymExpr (composeSymSub sub₁ sub₂) expr = substSymExpr sub₁ (substSymExpr sub₂ expr) := by
  cases expr with
  | const value => rfl
  | reg reg => rfl
  | add64 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | load64 mem addr =>
      simp [substSymExpr, substSymMem_compose, substSymExpr_compose]

theorem substSymMem_compose {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub₁ sub₂ : SymSub Reg) (mem : SymMem Reg) :
    substSymMem (composeSymSub sub₁ sub₂) mem = substSymMem sub₁ (substSymMem sub₂ mem) := by
  cases mem with
  | base => rfl
  | store64 mem addr value =>
      simp [substSymMem, substSymMem_compose, substSymExpr_compose]
end

mutual
theorem evalSymExpr_subst {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (expr : SymExpr Reg) (state : ConcreteState Reg) :
    evalSymExpr state (substSymExpr sub expr) = evalSymExpr (applySymSub sub state) expr := by
  cases expr with
  | const value => rfl
  | reg reg => rfl
  | add64 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | load64 mem addr =>
      simp [substSymExpr, evalSymMem_subst, evalSymExpr_subst]

theorem evalSymMem_subst {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (mem : SymMem Reg) (state : ConcreteState Reg) :
    evalSymMem state (substSymMem sub mem) = evalSymMem (applySymSub sub state) mem := by
  cases mem with
  | base => rfl
  | store64 mem addr value =>
      simp [substSymMem, evalSymMem_subst, evalSymExpr_subst]
end

theorem evalSymPC_subst {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (pc : SymPC Reg) (state : ConcreteState Reg) :
    evalSymPC state (substSymPC sub pc) = evalSymPC (applySymSub sub state) pc := by
  induction pc with
  | true => rfl
  | eq lhs rhs => simp [substSymPC, evalSymExpr_subst]
  | and φ ψ ihφ ihψ => simp [substSymPC, ihφ, ihψ]
  | not φ ih => simp [substSymPC, ih]

@[simp] theorem applySymSub_id {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) :
    applySymSub SymSub.id state = state := by
  apply ConcreteState.ext
  · funext reg
    simp [applySymSub, SymSub.id]
  · simp [applySymSub, SymSub.id, evalSymMem]

@[simp] theorem composeSymSub_apply {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub₁ sub₂ : SymSub Reg) (state : ConcreteState Reg) :
    applySymSub (composeSymSub sub₁ sub₂) state = applySymSub sub₂ (applySymSub sub₁ state) := by
  apply ConcreteState.ext
  · funext reg
    simp [applySymSub, composeSymSub, evalSymExpr_subst]
  · simp [applySymSub, composeSymSub, evalSymMem_subst]

end VexISA
