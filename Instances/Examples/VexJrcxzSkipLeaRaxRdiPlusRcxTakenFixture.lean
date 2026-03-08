import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexJrcxzSkipLeaRaxRdiPlusRcxTakenFixture

open VexISA

def bytes : List UInt8 := [0xe3, 0x04, 0x48, 0x8d, 0x04, 0x0f]

def block : Block :=
  { stmts := [
      .wrTmp 2 (.get .rcx),
      .exit (.eq64 (.tmp 2) (.const 0x0)) 0x400006,
      .wrTmp 4 (.get .rdi),
      .wrTmp 3 (.add64 (.tmp 4) (.tmp 2)),
      .put .rax (.tmp 3)
    ],
    next := 0x400006 }

def input : ConcreteState :=
  { rax := 0x0,
    rcx := 0x0,
    rdi := 0x10,
    rip := 0x400000 }

def expected : ConcreteState :=
  { rax := 0x0,
    rcx := 0x0,
    rdi := 0x10,
    rip := 0x400006 }

end Instances.Examples.VexJrcxzSkipLeaRaxRdiPlusRcxTakenFixture
