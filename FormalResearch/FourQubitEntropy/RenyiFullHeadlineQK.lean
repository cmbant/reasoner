import FormalResearch.FourQubitEntropy.RenyiFullHeadline
import FormalResearch.FourQubitEntropy.RenyiFullSliverProof
import FormalResearch.FourQubitEntropy.RenyiFullHsProof
import FormalResearch.FourQubitEntropy.RenyiFullCappedCubic
import FormalResearch.FourQubitEntropy.RenyiFullSmallHead
import FormalResearch.FourQubitEntropy.RenyiFullLargeHead

/-!
# The Rényi envelope above order one, assuming only QK

`renyi_envelope_above_one_QK` is the conditional headline `renyi_envelope_above_one` with every per-spectrum
certificate proved:
* `hsSupporting` (`lem:fqe-hs-polynomial`),
* `rationalDual_of_heads smallHeadDual largeHeadDual` (`lem:fqe-rational-dual`, from `lem:fqe-small-head-dual` and
  `lem:fqe-large-head-dual`),
* `cappedCubic` (`lem:fqe-capped-cubic`),
* `clusterSliver` (`lem:fqe-cluster-sliver`).

The only remaining hypothesis is `QuadraticVarianceBound` (QK, `thm:fqe-quadratic-variance`).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- **`cor:fqe-renyi-gw` for `q > 1`**, assuming only QK. -/
theorem renyi_envelope_above_one_QK (hQK : QuadraticVarianceBound)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q) :
    meanRenyi q ψ ≤ max (hsRenyi q) (5 / 3) ∧
    (5 / 3 < hsRenyi q → meanRenyi q ψ = hsRenyi q → LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) ∧
    (hsRenyi q < 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q = 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) :=
  renyi_envelope_above_one hsSupporting (rationalDual_of_heads smallHeadDual largeHeadDual) cappedCubic
    clusterSliver hQK hψ hq

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.renyi_envelope_above_one_QK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms renyi_envelope_above_one_QK

end FormalResearch.FourQubitEntropy.RenyiFull
