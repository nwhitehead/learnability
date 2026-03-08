import Instances.ISAs.VexLoweringCorrectness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

def loadBlock : Block :=
  { stmts := [
      .wrTmp 0 (.load64 (.get .rdi)),
      .put .rax (.tmp 0)
    ],
    next := 0x400004 }

def loadInput : ConcreteState :=
  { rax := 0x0,
    rcx := 0x0,
    rdi := 0x20,
    rip := 0x400000,
    mem := ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788 }

def loadExpected : ConcreteState :=
  { rax := 0x1122334455667788,
    rcx := 0x0,
    rdi := 0x20,
    rip := 0x400004,
    mem := ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788 }

example : execBlock loadBlock loadInput = loadExpected := by
  decide

example : Summary.apply (lowerBlock loadBlock) loadInput = loadExpected := by
  rw [VexISA.lowerBlock_sound]
  decide
