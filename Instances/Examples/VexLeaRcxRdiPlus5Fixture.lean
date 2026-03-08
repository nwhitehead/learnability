import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexLeaRcxRdiPlus5Fixture

open VexISA

def bytes : List UInt8 := [0x48, 0x8d, 0x4f, 0x05]

def block : Block :=
  { stmts := [
      .wrTmp 2 (.get .rdi),
      .wrTmp 1 (.add64 (.tmp 2) (.const 0x5)),
      .put .rcx (.tmp 1)
    ],
    next := 0x400004 }

def input : ConcreteState :=
  { rax := 0x0,
    rcx := 0x0,
    rdi := 0x10,
    rip := 0x400000 }

def expected : ConcreteState :=
  { rax := 0x0,
    rcx := 0x15,
    rdi := 0x10,
    rip := 0x400004 }

end Instances.Examples.VexLeaRcxRdiPlus5Fixture
