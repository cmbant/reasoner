import FormalResearch.FourQubitEntropy.RenyiFullHeadline
import FormalResearch.FourQubitEntropy.RenyiFullSliverProof

/-!
# Headline with `lem:fqe-cluster-sliver` discharged

`renyi_envelope_above_one_SL` is `renyi_envelope_above_one` (`RenyiFullHeadline.lean`) with the hypothesis
`ClusterSliver` removed: it is proved by `clusterSliver` (`RenyiFullSliverProof.lean`).  The remaining
hypotheses are `QuadraticVarianceBound` (QK), `HsSupporting`, `RationalDual` and `CappedCubic`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- **`cor:fqe-renyi-gw` for `q > 1`**, with `lem:fqe-cluster-sliver` proved. -/
theorem renyi_envelope_above_one_SL (hHZ : HsSupporting) (hL : RationalDual) (hC : CappedCubic)
    (hQK : QuadraticVarianceBound)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q) :
    meanRenyi q ψ ≤ max (hsRenyi q) (5 / 3) ∧
    (5 / 3 < hsRenyi q → meanRenyi q ψ = hsRenyi q → LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) ∧
    (hsRenyi q < 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q = 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) :=
  renyi_envelope_above_one hHZ hL hC clusterSliver hQK hψ hq

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.renyi_envelope_above_one_SL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms renyi_envelope_above_one_SL

end FormalResearch.FourQubitEntropy.RenyiFull
