import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexAddEaxEdiJzTakenFixture

open VexISA

def bytes : List UInt8 := [0x01, 0xf8, 0x74, 0x02]

def block : Amd64Block :=
  mkAmd64Block [
      .wrTmp 4 (.get .rax),
      .wrTmp 17 (.narrow32 (.tmp 4)),
      .wrTmp 3 (.tmp 17),
      .wrTmp 6 (.get .rdi),
      .wrTmp 18 (.narrow32 (.tmp 6)),
      .wrTmp 5 (.tmp 18),
      .wrTmp 0 (.add32 (.tmp 3) (.tmp 5)),
      .put .cc_op (.const 0x3),
      .wrTmp 19 (.zext64 (.tmp 3)),
      .wrTmp 7 (.tmp 19),
      .put .cc_dep1 (.tmp 7),
      .wrTmp 20 (.zext64 (.tmp 5)),
      .wrTmp 8 (.tmp 20),
      .put .cc_dep2 (.tmp 8),
      .wrTmp 21 (.zext64 (.tmp 0)),
      .wrTmp 9 (.tmp 21),
      .put .rax (.tmp 9),
      .put .rip (.const 0x400002),
      .wrTmp 25 (.narrow32 (.tmp 7)),
      .wrTmp 26 (.narrow32 (.tmp 8)),
      .wrTmp 24 (.add32 (.tmp 25) (.tmp 26)),
      .exit (.eq64 (.zext64 (.narrow32 (.tmp 24))) (.zext64 (.narrow32 (.const 0x0)))) 0x400006
    ] 0x400004

def input : Amd64ConcreteState :=
  mkAmd64StateCC
    0xffffffffffffffff
    0x0
    0x1
    0x400000
    0x0
    0x0
    0x0
    0x0
    ByteMem.empty

def expected : Amd64ConcreteState :=
  mkAmd64StateCC
    0x0
    0x0
    0x1
    0x400006
    0x3
    0xffffffff
    0x1
    0x0
    ByteMem.empty

end Instances.Examples.VexAddEaxEdiJzTakenFixture
