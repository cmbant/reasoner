import FormalResearch.FourQubitEntropy.GOProbe.GOConst
import FormalResearch.FourQubitEntropy.GOProbe.GOData_0
import FormalResearch.FourQubitEntropy.GOProbe.GOData_1
import FormalResearch.FourQubitEntropy.GOProbe.GOData_2
import FormalResearch.FourQubitEntropy.GOProbe.GOData_3
import FormalResearch.FourQubitEntropy.GOProbe.GOData_4
import FormalResearch.FourQubitEntropy.GOProbe.GOData_5
import FormalResearch.FourQubitEntropy.GOProbe.GOData_6
import FormalResearch.FourQubitEntropy.GOProbe.GOData_7
import FormalResearch.FourQubitEntropy.GOProbe.GOData_8
import FormalResearch.FourQubitEntropy.GOProbe.GOData_9

/-!
# GO certificate probe: the full 277-block check by `native_decide`

Needs the generated modules `GOConst`, `GOData_0 .. GOData_9` (not committed, 22 MB; produce them with
`python3 FormalResearch/FourQubitEntropy/gen_go_cert.py --all`, then compile with `lean -o`, or add them to a
lake build).  The kernel route (`decide +kernel`) is far too slow for the full check (see `Kernel*.lean`
here), so this probe uses `native_decide` as permitted by the owner: `#print axioms` shows
`Lean.ofReduceBool`.  Negative regressions: a perturbed target and a perturbed Gram block are rejected.
-/

namespace FormalResearch.FourQubitEntropy.GOProbe

set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 500

def allBlocks : List GBlock :=
  dataBlocks_0 ++ dataBlocks_1 ++ dataBlocks_2 ++ dataBlocks_3 ++ dataBlocks_4 ++ dataBlocks_5 ++
    dataBlocks_6 ++ dataBlocks_7 ++ dataBlocks_8 ++ dataBlocks_9

def s2 : Int := (2 : Int) ^ (2 * factorBits)

theorem blocks_count : allBlocks.length = 277 := by native_decide

theorem gram_all : allBlocks.all (gramOK corrDen) = true := by native_decide

theorem identity_all : identityOK cons orbitTable expected (gridC : Int) s2 (corrDen : Int) allBlocks = true := by
  native_decide

/-! ### Negative regressions -/

def badExpected : SP := match expected with | (k, c) :: t => (k, c + 1) :: t | [] => []

theorem identity_neg : identityOK cons orbitTable badExpected (gridC : Int) s2 (corrDen : Int) allBlocks = false := by
  native_decide

def badBlock : GBlock :=
  match allBlocks with
  | b :: _ => { b with resid := [0] :: b.resid.tail }
  | [] => ⟨0, 0, 0, [], [], [], []⟩

theorem gram_neg : gramOK corrDen badBlock = false := by native_decide

#print axioms gram_all
#print axioms identity_all
#print axioms identity_neg

end FormalResearch.FourQubitEntropy.GOProbe
