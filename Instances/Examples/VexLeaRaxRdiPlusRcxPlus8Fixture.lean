import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexLeaRaxRdiPlusRcxPlus8Fixture

open VexISA

def bytes : List UInt8 := [0x48, 0x8d, 0x44, 0x0f, 0x08]

def block : Block :=
  { stmts := [
      .wrTmp 3 (.get .rdi),
      .wrTmp 5 (.get .rcx),
      .wrTmp 2 (.add64 (.tmp 3) (.tmp 5)),
      .wrTmp 1 (.add64 (.tmp 2) (.const 0x8)),
      .put .rax (.tmp 1)
    ],
    next := 0x400005 }

def input : ConcreteState :=
  { rax := 0x0,
    rcx := 0x3,
    rdi := 0x10,
    rip := 0x400000 }

def expected : ConcreteState :=
  { rax := 0x1b,
    rcx := 0x3,
    rdi := 0x10,
    rip := 0x400005 }

end Instances.Examples.VexLeaRaxRdiPlusRcxPlus8Fixture
