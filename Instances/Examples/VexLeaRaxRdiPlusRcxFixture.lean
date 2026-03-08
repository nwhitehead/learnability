import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexLeaRaxRdiPlusRcxFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x8d, 0x04, 0x0f]

def block : Block :=
  { stmts := [
      .wrTmp 2 (.get .rdi),
      .wrTmp 4 (.get .rcx),
      .wrTmp 1 (.add64 (.tmp 2) (.tmp 4)),
      .put .rax (.tmp 1)
    ],
    next := 0x400004 }

def input : ConcreteState :=
  { rax := 0x0,
    rcx := 0x3,
    rdi := 0x10,
    rip := 0x400000 }

def expected : ConcreteState :=
  { rax := 0x13,
    rcx := 0x3,
    rdi := 0x10,
    rip := 0x400004 }

end Instances.Examples.VexLeaRaxRdiPlusRcxFixture
