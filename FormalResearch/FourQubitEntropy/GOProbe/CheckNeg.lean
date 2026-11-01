import FormalResearch.FourQubitEntropy.GOData.GOAll
import FormalResearch.FourQubitEntropy.GOProbe.Block

/-!
# GO certificate: negative regression on the generated data

The checker rejects the generated certificate when the target polynomial `lit` is perturbed by one in its
first coefficient, so `check_all` of `Check.lean` is not vacuous.  Separate module because each full
evaluation takes about five minutes (`native_decide`).
-/

namespace FormalResearch.FourQubitEntropy.GOProbe

set_option maxRecDepth 100000

def badLit : SP := match lit with | (k, c) :: t => (k, c + 1) :: t | [] => []

theorem check_neg :
    check cons perms flips badLit (gridC : Int) ((2 : Int) ^ (2 * factorBits)) (corrDen : Int) allBlocks = false := by
  native_decide

end FormalResearch.FourQubitEntropy.GOProbe
