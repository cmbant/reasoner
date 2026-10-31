import FormalResearch.FourQubitEntropy.RenyiFullStateEq
import FormalResearch.FourQubitEntropy.RenyiFullDetChart
import FormalResearch.FourQubitEntropy.RenyiFullNU

/-!
# Headline: the Rényi envelope above one (`cor:fqe-renyi-gw`, `q > 1`)

Paper E, `cor:fqe-renyi-gw` via the anchor-order bounds of `thm:fqe-renyi-classical`.

**Statement** (`renyi_envelope_above_one`).  Let `ψ` be a unit pure four-qubit vector and `q > 1`.
Then `meanRenyi q ψ ≤ max {hsRenyi q, 5/3}` (the HS--cluster envelope).  If `h_q > 5/3`
(`q < q_*`) equality forces the three cut spectra to be HS, and then `ψ` is LU-equivalent to `M₄` or
`conj M₄`; if `h_q < 5/3` (`q > q_*`) equality forces the cut spectra to be the cluster triple
`(c₁, c₂, c₂)`; at `h_q = 5/3` it forces one of the two.

**Hypotheses** (named `Prop`s, each matching a statement of the paper; none is an axiom):

* `QuadraticVarianceBound`: `thm:fqe-quadratic-variance` (QK), the exact-rational certificate QG;
* `HsSupporting`: `lem:fqe-hs-polynomial` (HS supporting inequality at `q_u = 8/5`);
* `RationalDual`: `lem:fqe-rational-dual` (the exact rational certificate RQ, band `L`);
* `CappedCubic`: `lem:fqe-capped-cubic` (CG);
* `ClusterSliver`: `lem:fqe-cluster-sliver` (SL).

`lem:fqe-renyi-determinant` (`DetReduction`, `det_reduction`) and `lem:fqe-near-uniform-dual` (NU, `nearUniformDual`) are proved, as are the dual lemma
`lem:fqe-dual`, the case analysis of `thm:fqe-renyi-classical`, the analytic cubic envelope
`cor:fqe-renyi-high-f` (the case `20ε + 2F ≥ 1`), the order transfer (`RenyiSingleCrossing.lean`) and the
HS--cluster crossing (`RenyiCrossing.lean`).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- `thm:fqe-renyi-classical` from the four remaining per-spectrum certificates
(`DetReduction` and `NearUniformDual` are proved). -/
theorem classical_relaxation (hHZ : HsSupporting) (hL : RationalDual) (hC : CappedCubic)
    (hSL : ClusterSliver) : ClassicalRelaxation :=
  classical_of_certificates det_reduction hHZ hL hC nearUniformDual hSL

/-- **`cor:fqe-renyi-gw` for `q > 1`** (conditional on the named certificates above). -/
theorem renyi_envelope_above_one (hHZ : HsSupporting) (hL : RationalDual) (hC : CappedCubic)
    (hSL : ClusterSliver) (hQK : QuadraticVarianceBound)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q) :
    meanRenyi q ψ ≤ max (hsRenyi q) (5 / 3) ∧
    (5 / 3 < hsRenyi q → meanRenyi q ψ = hsRenyi q → LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) ∧
    (hsRenyi q < 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q = 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) := by
  have hCl := classical_relaxation hHZ hL hC hSL
  obtain ⟨h1, h2, h3, h4⟩ := meanRenyi_envelope hCl hQK hψ hq
  exact ⟨h1, fun hg he => hs_triple_LU hψ (h2 hg he), h3, h4⟩

/-! ### The unconditional high-`F` regime (`cor:fqe-renyi-high-f`) for states -/

/-- **Analytic cubic envelope for states** (no (QK), no certificate): for a unit `ψ` and `q ≥ q_b`
(`q_b < 313/200`), `E_q(ψ) ≤ 5/3 - (20/27)(P-1) - (2/27)(F - 1/2)`; in particular `E_q(ψ) ≤ 5/3` when
`20(P-1) + 2F ≥ 1`. -/
theorem meanRenyi_cubic_envelope {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ}
    (hq : PaperECritical.qb ≤ q) :
    meanRenyi q ψ ≤ 5 / 3 - 20 / 27 * (purity ψ - 1) - 2 / 27 * (sexticF ψ - 1 / 2) := by
  have h := cubic_envelope (l₂ := cutSpec₂ ψ) (l₃ := cutSpec₃ ψ) (l₄ := cutSpec₄ ψ)
    (isProb4_spec4 (isProb12 hψ)) (isProb4_spec4 (isProb13 hψ))
    (isProb4_spec4 (isProb14 hψ)) hq
  rw [← meanRenyi_eq_Em] at h
  have eP := Pm_cutSpec ψ
  have eF := Fm_cutSpec ψ hψ
  rw [eP, eF] at h
  exact h

theorem meanRenyi_high_F {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : PaperECritical.qb ≤ q)
    (hF : 1 ≤ 20 * (purity ψ - 1) + 2 * sexticF ψ) :
    meanRenyi q ψ ≤ 5 / 3 ∧
      (meanRenyi q ψ = 5 / 3 → IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) := by
  have h := cubic_envelope_le_five_thirds (l₂ := cutSpec₂ ψ) (l₃ := cutSpec₃ ψ) (l₄ := cutSpec₄ ψ)
    (isProb4_spec4 (isProb12 hψ)) (isProb4_spec4 (isProb13 hψ))
    (isProb4_spec4 (isProb14 hψ)) hq
    (by rw [Pm_cutSpec, Fm_cutSpec ψ hψ]; exact hF)
  rw [← meanRenyi_eq_Em] at h
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.renyi_envelope_above_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms renyi_envelope_above_one

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.meanRenyi_high_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meanRenyi_high_F

end FormalResearch.FourQubitEntropy.RenyiFull
