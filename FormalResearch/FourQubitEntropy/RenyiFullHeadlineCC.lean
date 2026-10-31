import FormalResearch.FourQubitEntropy.RenyiFullHeadlineSL
import FormalResearch.FourQubitEntropy.RenyiFullCappedCubic

/-!
# Headline with `lem:fqe-cluster-sliver` and `lem:fqe-capped-cubic` discharged

`renyi_envelope_above_one_CC` is `renyi_envelope_above_one` (`RenyiFullHeadline.lean`) with the hypotheses
`ClusterSliver` (`clusterSliver`, `RenyiFullSliverProof.lean`) and `CappedCubic` (`cappedCubic`,
`RenyiFullCappedCubic.lean`) removed.  The remaining hypotheses are `QuadraticVarianceBound` (QK),
`HsSupporting` and `RationalDual`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- **`cor:fqe-renyi-gw` for `q > 1`**, with `lem:fqe-cluster-sliver` and `lem:fqe-capped-cubic` proved. -/
theorem renyi_envelope_above_one_CC (hHZ : HsSupporting) (hL : RationalDual)
    (hQK : QuadraticVarianceBound)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q) :
    meanRenyi q ψ ≤ max (hsRenyi q) (5 / 3) ∧
    (5 / 3 < hsRenyi q → meanRenyi q ψ = hsRenyi q → LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) ∧
    (hsRenyi q < 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q = 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) :=
  renyi_envelope_above_one_SL hHZ hL cappedCubic hQK hψ hq

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.renyi_envelope_above_one_CC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms renyi_envelope_above_one_CC

end FormalResearch.FourQubitEntropy.RenyiFull
