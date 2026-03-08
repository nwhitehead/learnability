import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexLeaRaxRcxPlus5Fixture

open VexISA

def bytes : List UInt8 := [0x48, 0x8d, 0x41, 0x05]

def block : Block :=
  { stmts := [
      .wrTmp 2 (.get .rcx),
      .wrTmp 1 (.add64 (.tmp 2) (.const 0x5)),
      .put .rax (.tmp 1)
    ],
    next := 0x400004 }

def input : ConcreteState :=
  { rax := 0x0,
    rcx := 0x10,
    rdi := 0x0,
    rip := 0x400000 }

def expected : ConcreteState :=
  { rax := 0x15,
    rcx := 0x10,
    rdi := 0x0,
    rip := 0x400004 }

end Instances.Examples.VexLeaRaxRcxPlus5Fixture
