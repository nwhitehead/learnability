import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexJrcxzSkipMovRaxRdiTakenFixture

open VexISA

def bytes : List UInt8 := [0xe3, 0x03, 0x48, 0x89, 0xf8]

def block : Block :=
  { stmts := [
      .wrTmp 1 (.get .rcx),
      .exit (.eq64 (.tmp 1) (.const 0x0)) 0x400005,
      .wrTmp 2 (.get .rdi),
      .put .rax (.tmp 2)
    ],
    next := 0x400005 }

def input : ConcreteState :=
  { rax := 0x0,
    rcx := 0x0,
    rdi := 0x10,
    rip := 0x400000 }

def expected : ConcreteState :=
  { rax := 0x0,
    rcx := 0x0,
    rdi := 0x10,
    rip := 0x400005 }

end Instances.Examples.VexJrcxzSkipMovRaxRdiTakenFixture
