import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexMovRdiRcxFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x89, 0xcf]

def block : Block :=
  { stmts := [
      .wrTmp 0 (.get .rcx),
      .put .rdi (.tmp 0)
    ],
    next := 0x400003 }

def input : ConcreteState :=
  { rax := 0x0,
    rcx := 0x10,
    rdi := 0x0,
    rip := 0x400000 }

def expected : ConcreteState :=
  { rax := 0x0,
    rcx := 0x10,
    rdi := 0x10,
    rip := 0x400003 }

end Instances.Examples.VexMovRdiRcxFixture
