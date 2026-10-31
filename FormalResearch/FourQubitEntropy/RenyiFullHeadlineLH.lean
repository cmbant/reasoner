import FormalResearch.FourQubitEntropy.RenyiFullHeadlineRD
import FormalResearch.FourQubitEntropy.RenyiFullSmallHead

/-!
# Headline with only the large-head dual and QK

`renyi_envelope_above_one_LH` is `renyi_envelope_above_one_RD` with `RationalDual` replaced by its two chart bounds:
`SmallHeadDual` is proved (`smallHeadDual`, `lem:fqe-small-head-dual`); the remaining hypotheses are
`LargeHeadDual` (`lem:fqe-large-head-dual`, band `L` at `q_s`, `1/2 ≤ a ≤ 4/5`) and `QuadraticVarianceBound` (QK).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- **`cor:fqe-renyi-gw` for `q > 1`**, assuming only `lem:fqe-large-head-dual` and QK. -/
theorem renyi_envelope_above_one_LH (hLH : LargeHeadDual) (hQK : QuadraticVarianceBound)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q) :
    meanRenyi q ψ ≤ max (hsRenyi q) (5 / 3) ∧
    (5 / 3 < hsRenyi q → meanRenyi q ψ = hsRenyi q → LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) ∧
    (hsRenyi q < 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q = 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) :=
  renyi_envelope_above_one_RD (rationalDual_of_heads smallHeadDual hLH) hQK hψ hq

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.renyi_envelope_above_one_LH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms renyi_envelope_above_one_LH

end FormalResearch.FourQubitEntropy.RenyiFull
