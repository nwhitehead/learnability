import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexMovMemRdiRaxFixture

open VexISA

def bytes : List UInt8 := [0x48, 0x89, 0x07]

def block : Block :=
  { stmts := [
      .wrTmp 0 (.get .rdi),
      .wrTmp 1 (.get .rax),
      .store64 (.tmp 0) (.tmp 1)
    ],
    next := 0x400003 }

def input : ConcreteState :=
  { rax := 0x1122334455667788,
    rcx := 0x0,
    rdi := 0x20,
    rip := 0x400000,
    mem := (ByteMem.write64le ByteMem.empty 0x20 0xdeadbeefcafebabe) }

def expected : ConcreteState :=
  { rax := 0x1122334455667788,
    rcx := 0x0,
    rdi := 0x20,
    rip := 0x400003,
    mem := (ByteMem.write64le ByteMem.empty 0x20 0x1122334455667788) }

end Instances.Examples.VexMovMemRdiRaxFixture
