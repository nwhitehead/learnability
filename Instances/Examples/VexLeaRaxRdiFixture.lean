import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexLeaRaxRdiFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x8d, 0x07]

def block : Block :=
  { stmts := [
      .wrTmp 0 (.get .rdi),
      .put .rax (.tmp 0)
    ],
    next := 0x400003 }

def input : ConcreteState :=
  { rax := 0x0,
    rcx := 0x0,
    rdi := 0x10,
    rip := 0x400000 }

def expected : ConcreteState :=
  { rax := 0x10,
    rcx := 0x0,
    rdi := 0x10,
    rip := 0x400003 }

end Instances.Examples.VexLeaRaxRdiFixture
