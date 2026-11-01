import FormalResearch.FourQubitEntropy.GOProbe.GOConst
import FormalResearch.FourQubitEntropy.GOProbe.GOData

/-! Kernel (`decide +kernel`) timing of the Gram positivity test on the blocks of `GOData`
(generate with `gen_go_cert.py --blocks 0:1 --suffix ""`).  Block 0: 31 s, 2.7 GB. -/

namespace FormalResearch.FourQubitEntropy.GOProbe

set_option maxRecDepth 100000

theorem gram_ok : dataBlocks.all (gramOK corrDen) = true := by decide +kernel

end FormalResearch.FourQubitEntropy.GOProbe
