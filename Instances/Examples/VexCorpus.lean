/-
The fixture modules imported here are generated from
`tools/vex_ref/corpus_manifest.json`.
Regenerate them from `tools/vex_ref` inside the repo nix shell with:
`uv run --active python extract_fixture.py --manifest corpus_manifest.json`
-/

import Instances.ISAs.VexLoweringCorrectness
import Instances.Examples.VexJrcxzSkipLeaFallthroughFixture
import Instances.Examples.VexJrcxzSkipLeaRaxRdiPlusRcxFallthroughFixture
import Instances.Examples.VexJrcxzSkipLeaRaxRdiPlusRcxTakenFixture
import Instances.Examples.VexJrcxzSkipLeaRcxRdiPlus5FallthroughFixture
import Instances.Examples.VexJrcxzSkipLeaRcxRdiPlus5TakenFixture
import Instances.Examples.VexJrcxzSkipLeaRdiRdiPlus8FallthroughFixture
import Instances.Examples.VexJrcxzSkipLeaRdiRdiPlus8TakenFixture
import Instances.Examples.VexJrcxzSkipLeaTakenFixture
import Instances.Examples.VexJrcxzSkipMovRaxRdiFallthroughFixture
import Instances.Examples.VexJrcxzSkipMovRaxRdiTakenFixture
import Instances.Examples.VexLeaRaxRcxPlus5Fixture
import Instances.Examples.VexLeaRaxRdiFixture
import Instances.Examples.VexLeaRaxRdiPlusRcxFixture
import Instances.Examples.VexLeaRaxRdiPlusRcxPlus8Fixture
import Instances.Examples.VexLeaRcxRdiPlus5Fixture
import Instances.Examples.VexLeaRdiPlus5Fixture
import Instances.Examples.VexMovRcxRdiFixture
import Instances.Examples.VexMovRdiRcxFixture

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.VexLeaRdiPlus5Fixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexLeaRdiPlus5Fixture

namespace Instances.Examples.VexLeaRaxRdiFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexLeaRaxRdiFixture

namespace Instances.Examples.VexLeaRaxRcxPlus5Fixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexLeaRaxRcxPlus5Fixture

namespace Instances.Examples.VexLeaRcxRdiPlus5Fixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexLeaRcxRdiPlus5Fixture

namespace Instances.Examples.VexLeaRaxRdiPlusRcxFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexLeaRaxRdiPlusRcxFixture

namespace Instances.Examples.VexLeaRaxRdiPlusRcxPlus8Fixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexLeaRaxRdiPlusRcxPlus8Fixture

namespace Instances.Examples.VexMovRcxRdiFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexMovRcxRdiFixture

namespace Instances.Examples.VexMovRdiRcxFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexMovRdiRcxFixture

namespace Instances.Examples.VexJrcxzSkipLeaTakenFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipLeaTakenFixture

namespace Instances.Examples.VexJrcxzSkipLeaFallthroughFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipLeaFallthroughFixture

namespace Instances.Examples.VexJrcxzSkipMovRaxRdiTakenFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipMovRaxRdiTakenFixture

namespace Instances.Examples.VexJrcxzSkipMovRaxRdiFallthroughFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipMovRaxRdiFallthroughFixture

namespace Instances.Examples.VexJrcxzSkipLeaRcxRdiPlus5TakenFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipLeaRcxRdiPlus5TakenFixture

namespace Instances.Examples.VexJrcxzSkipLeaRcxRdiPlus5FallthroughFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipLeaRcxRdiPlus5FallthroughFixture

namespace Instances.Examples.VexJrcxzSkipLeaRdiRdiPlus8TakenFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipLeaRdiRdiPlus8TakenFixture

namespace Instances.Examples.VexJrcxzSkipLeaRdiRdiPlus8FallthroughFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipLeaRdiRdiPlus8FallthroughFixture

namespace Instances.Examples.VexJrcxzSkipLeaRaxRdiPlusRcxTakenFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipLeaRaxRdiPlusRcxTakenFixture

namespace Instances.Examples.VexJrcxzSkipLeaRaxRdiPlusRcxFallthroughFixture

example : expected ∈ execBlockSuccs block input := by
  decide

example :
    ∃ summary ∈ lowerBlockSummaries block,
      Summary.enabled summary input ∧ Summary.apply summary input = expected := by
  exact lowerBlockSummaries_sound block input expected (by decide)

example (summary : Summary)
    (hMem : summary ∈ lowerBlockSummaries block)
    (hEnabled : Summary.enabled summary input) :
    Summary.apply summary input = expected := by
  have hSucc := lowerBlockSummaries_complete block input summary hMem hEnabled
  simpa [block, input, expected, execBlockSuccs, execStmtsSuccs, evalCond, evalExpr] using hSucc

end Instances.Examples.VexJrcxzSkipLeaRaxRdiPlusRcxFallthroughFixture
