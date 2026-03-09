import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

def mask32 (value : UInt64) : UInt64 :=
  value &&& 0xFFFF_FFFF

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

inductive Expr (Reg : Type) where
  | const : UInt64 → Expr Reg
  | get : Reg → Expr Reg
  | tmp : Nat → Expr Reg
  | narrow32 : Expr Reg → Expr Reg
  | zext64 : Expr Reg → Expr Reg
  | add32 : Expr Reg → Expr Reg → Expr Reg
  | add64 : Expr Reg → Expr Reg → Expr Reg
  | sub64 : Expr Reg → Expr Reg → Expr Reg
  | load64 : Expr Reg → Expr Reg
  deriving DecidableEq, Repr

namespace Expr

@[match_pattern] abbrev low32 {Reg : Type} (expr : Expr Reg) : Expr Reg :=
  .narrow32 expr

@[match_pattern] abbrev uext32 {Reg : Type} (expr : Expr Reg) : Expr Reg :=
  .zext64 expr

end Expr

inductive Cond (Reg : Type) where
  | eq64 : Expr Reg → Expr Reg → Cond Reg
  | lt64 : Expr Reg → Expr Reg → Cond Reg
  | le64 : Expr Reg → Expr Reg → Cond Reg
  | amd64CalculateCondition : UInt64 → Expr Reg → Expr Reg → Expr Reg → Expr Reg → Cond Reg
  deriving DecidableEq, Repr

inductive LinearStmt (Reg : Type) where
  | wrTmp : Nat → Expr Reg → LinearStmt Reg
  | put : Reg → Expr Reg → LinearStmt Reg
  | store64 : Expr Reg → Expr Reg → LinearStmt Reg
  deriving DecidableEq, Repr

inductive BranchStmt (Reg : Type) where
  | exit : Cond Reg → UInt64 → BranchStmt Reg
  deriving DecidableEq, Repr

inductive Stmt (Reg : Type) where
  | linear : LinearStmt Reg → Stmt Reg
  | branch : BranchStmt Reg → Stmt Reg
  deriving DecidableEq, Repr

namespace Stmt

@[match_pattern] abbrev wrTmp {Reg : Type} (tmp : Nat) (expr : Expr Reg) : Stmt Reg :=
  .linear (.wrTmp tmp expr)

@[match_pattern] abbrev put {Reg : Type} (reg : Reg) (expr : Expr Reg) : Stmt Reg :=
  .linear (.put reg expr)

@[match_pattern] abbrev store64 {Reg : Type} (addr value : Expr Reg) : Stmt Reg :=
  .linear (.store64 addr value)

@[match_pattern] abbrev exit {Reg : Type} (cond : Cond Reg) (target : UInt64) : Stmt Reg :=
  .branch (.exit cond target)

end Stmt

structure Block (Reg : Type) where
  stmts : List (Stmt Reg)
  ip_reg : Reg
  next : UInt64
  deriving DecidableEq, Repr

structure ConcreteState (Reg : Type) where
  regs : Reg → UInt64
  mem : ByteMem

instance {Reg : Type} [DecidableEq Reg] [Fintype Reg] : DecidableEq (ConcreteState Reg) := by
  intro state₁ state₂
  by_cases hRegs : state₁.regs = state₂.regs
  · by_cases hMem : state₁.mem = state₂.mem
    · cases state₁
      cases state₂
      cases hRegs
      cases hMem
      exact isTrue rfl
    · exact isFalse (fun h => hMem (congrArg ConcreteState.mem h))
  · exact isFalse (fun h => hRegs (congrArg ConcreteState.regs h))

@[ext] theorem ConcreteState.ext {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {state₁ state₂ : ConcreteState Reg}
    (hRegs : state₁.regs = state₂.regs) (hMem : state₁.mem = state₂.mem) :
    state₁ = state₂ := by
  cases state₁
  cases state₂
  cases hRegs
  cases hMem
  rfl

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

@[simp] def ConcreteState.read {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (reg : Reg) : UInt64 :=
  state.regs reg

@[simp] def ConcreteState.write {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (reg : Reg) (value : UInt64) : ConcreteState Reg :=
  { state with regs := fun reg' => if reg' = reg then value else state.regs reg' }

@[simp] theorem ConcreteState.read_write_same {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (reg : Reg) (value : UInt64) :
    (state.write reg value).read reg = value := by
  simp [ConcreteState.write, ConcreteState.read]

@[simp] theorem ConcreteState.read_write_other {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) {reg reg' : Reg}
    (value : UInt64) (h : reg' ≠ reg) : (state.write reg value).read reg' = state.read reg' := by
  simp [ConcreteState.write, ConcreteState.read, h]

end VexISA
