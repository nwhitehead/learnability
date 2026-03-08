import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexSyntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

inductive Amd64Reg where
  | rax
  | rcx
  | rdi
  | rip
  deriving DecidableEq, Repr

instance : Fintype Amd64Reg :=
  ⟨{.rax, .rcx, .rdi, .rip}, by
    intro reg
    cases reg <;> simp⟩

abbrev Amd64Block := Block Amd64Reg
abbrev Amd64Expr := Expr Amd64Reg
abbrev Amd64Cond := Cond Amd64Reg
abbrev Amd64Stmt := Stmt Amd64Reg
abbrev Amd64LinearStmt := LinearStmt Amd64Reg
abbrev Amd64BranchStmt := BranchStmt Amd64Reg
abbrev Amd64ConcreteState := ConcreteState Amd64Reg

def mkAmd64Block (stmts : List Amd64Stmt) (next : UInt64) : Amd64Block :=
  { stmts := stmts, ip_reg := .rip, next := next }

def mkAmd64State (rax rcx rdi rip : UInt64) (mem : ByteMem) : Amd64ConcreteState :=
  { regs := fun
      | .rax => rax
      | .rcx => rcx
      | .rdi => rdi
      | .rip => rip
  , mem := mem }

instance : Repr Amd64ConcreteState where
  reprPrec state _ :=
    repr (state.read .rax, state.read .rcx, state.read .rdi, state.read .rip, state.mem)

end VexISA
