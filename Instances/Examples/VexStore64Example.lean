import Instances.ISAs.VexLoweringCorrectness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

def storeBlock : Block :=
  { stmts := [
      .store64 (.get .rdi) (.get .rax)
    ],
    next := 0x400003 }

def storeInput : ConcreteState :=
  { rax := 0x1122334455667788,
    rcx := 0x0,
    rdi := 0x20,
    rip := 0x400000,
    mem := ByteMem.write64le ByteMem.empty 0x20 0x0 }

def storeExpected : ConcreteState :=
  { rax := 0x1122334455667788,
    rcx := 0x0,
    rdi := 0x20,
    rip := 0x400003,
    mem := ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788 }

example : execBlock storeBlock storeInput = storeExpected := by
  native_decide

example : Summary.apply (lowerBlock storeBlock) storeInput = storeExpected := by
  rw [VexISA.lowerBlock_sound]
  native_decide
