import Mathlib.Data.Finset.Basic
import Instances.ISAs.VexLoweringCorrectness
import Instances.Examples.VexAddEaxEdiJzTakenFixture
import Instances.Examples.VexAddEaxEdiJzFallthroughFixture

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples

example :
    execBlockSuccs VexAddEaxEdiJzTakenFixture.block VexAddEaxEdiJzTakenFixture.input =
      ({VexAddEaxEdiJzTakenFixture.expected} : Finset Amd64ConcreteState) := by
  native_decide

example (summary : Summary Amd64Reg)
    (hMem : summary ∈ lowerBlockSummaries VexAddEaxEdiJzTakenFixture.block)
    (hEnabled : Summary.enabled summary VexAddEaxEdiJzTakenFixture.input) :
    Summary.apply summary VexAddEaxEdiJzTakenFixture.input = VexAddEaxEdiJzTakenFixture.expected := by
  exact lowerBlockSummaries_complete_eq_of_unique
    VexAddEaxEdiJzTakenFixture.block
    VexAddEaxEdiJzTakenFixture.input
    VexAddEaxEdiJzTakenFixture.expected
    summary
    (by native_decide)
    hMem
    hEnabled

example :
    execBlockSuccs VexAddEaxEdiJzFallthroughFixture.block VexAddEaxEdiJzFallthroughFixture.input =
      ({VexAddEaxEdiJzFallthroughFixture.expected} : Finset Amd64ConcreteState) := by
  native_decide

example (summary : Summary Amd64Reg)
    (hMem : summary ∈ lowerBlockSummaries VexAddEaxEdiJzFallthroughFixture.block)
    (hEnabled : Summary.enabled summary VexAddEaxEdiJzFallthroughFixture.input) :
    Summary.apply summary VexAddEaxEdiJzFallthroughFixture.input =
      VexAddEaxEdiJzFallthroughFixture.expected := by
  exact lowerBlockSummaries_complete_eq_of_unique
    VexAddEaxEdiJzFallthroughFixture.block
    VexAddEaxEdiJzFallthroughFixture.input
    VexAddEaxEdiJzFallthroughFixture.expected
    summary
    (by native_decide)
    hMem
    hEnabled

end Instances.Examples
