import FormalResearch.FourQubitEntropy.RenyiFullHeadlineSL
import FormalResearch.FourQubitEntropy.RenyiFullHsProof

/-!
# Headline with `lem:fqe-hs-polynomial` and `lem:fqe-cluster-sliver` discharged

`renyi_envelope_above_one_HS` is `renyi_envelope_above_one_SL` (`RenyiFullHeadlineSL.lean`) with the
hypothesis `HsSupporting` removed: it is proved by `hsSupporting` (`RenyiFullHsProof.lean`).  The remaining
hypotheses are `QuadraticVarianceBound` (QK), `RationalDual` and `CappedCubic`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- **`cor:fqe-renyi-gw` for `q > 1`**, with `lem:fqe-cluster-sliver` and `lem:fqe-hs-polynomial` proved. -/
theorem renyi_envelope_above_one_HS (hL : RationalDual) (hC : CappedCubic)
    (hQK : QuadraticVarianceBound)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q) :
    meanRenyi q ψ ≤ max (hsRenyi q) (5 / 3) ∧
    (5 / 3 < hsRenyi q → meanRenyi q ψ = hsRenyi q → LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) ∧
    (hsRenyi q < 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q = 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) :=
  renyi_envelope_above_one_SL hsSupporting hL hC hQK hψ hq

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.renyi_envelope_above_one_HS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms renyi_envelope_above_one_HS

end FormalResearch.FourQubitEntropy.RenyiFull
