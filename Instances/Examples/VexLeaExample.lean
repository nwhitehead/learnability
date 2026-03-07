import Instances.ISAs.VexISA
import Instances.ISAs.VexLoweringCorrectness
import Instances.Examples.VexLeaRdiPlus5Fixture

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA
open Instances.Examples.VexLeaRdiPlus5Fixture

example : execBlock block input = expected := by
  decide

example : Summary.apply (lowerBlock block) input = expected := by
  rw [VexISA.lowerBlock_sound]
  decide
