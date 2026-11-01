import FormalResearch.FourQubitEntropy.GOProbe.GOConst
import FormalResearch.FourQubitEntropy.GOProbe.GOData
import FormalResearch.FourQubitEntropy.GOProbe.GORef

/-! Kernel timing of a slice of the identity: the projected expansion of the blocks of `GOData` equals the
Python reference (`gen_go_cert.py --blocks A:B --ref`).  Block 9: 35 s, 3.4 GB (17.8 s of that is the fixed
cost of the 64-constraint pipeline, see `KernelEmpty.lean`); block 0: killed at 10 GB after 107 s. -/

namespace FormalResearch.FourQubitEntropy.GOProbe

set_option maxRecDepth 100000

def sliceCheck : Bool :=
  let t := totals cons orbitTable (gridC : Int) ((2 : Int) ^ (2 * factorBits)) dataBlocks
  eqSP t.1 refBase && eqSP t.2 refCorr

theorem slice_ok : sliceCheck = true := by decide +kernel

end FormalResearch.FourQubitEntropy.GOProbe
