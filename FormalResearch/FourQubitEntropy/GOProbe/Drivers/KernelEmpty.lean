import FormalResearch.FourQubitEntropy.GOProbe.GOConst
import FormalResearch.FourQubitEntropy.GOProbe.GOData
/-! Fixed cost of the kernel pipeline (no blocks): 17.8 s, 2.1 GB. -/

namespace FormalResearch.FourQubitEntropy.GOProbe
set_option maxRecDepth 100000
def emptyCheck : Bool :=
  let t := totals cons orbitTable (gridC : Int) ((2 : Int) ^ (2 * factorBits)) []
  eqSP t.1 [] && eqSP t.2 []
theorem empty_ok : emptyCheck = true := by decide +kernel
end FormalResearch.FourQubitEntropy.GOProbe
