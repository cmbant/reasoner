module

public import FormalResearch.FourQubitEntropy.PaperEGenJointPurity

/-!
# The homogenised (QV) defect `𝔇`

Paper E, `sup_renyi.tex`, `sec:sup-qk`: for `z ∈ ℂ¹⁶` put `N = ‖z‖²`, use the unnormalised marginals `P`, `T`,
`U = Σ_j (tr R_{1j}²)²`, and set
`𝔉 = 17 N P - 12 T - 12 N³` (`sexticF`), `𝔇 = 𝔉² + 5 N² P² - 3 N⁴ P - 6 N² U`.
Then `𝔇 (z / √N) · N⁶ = 𝔇 z`, and on unit vectors `𝔇 = F² + 3P(P-1) - 6 V_P`, which is the defect of (QV).

* `defectD`: the homogeneous polynomial `𝔇` on `Psi`.
* `defectD_unit`: for `normSqPsi ψ = 1`, `𝔇 ψ = F² + 3P(P-1) - 6 Σ_j (p_j - P/3)²`, with `p_j = cutPurity1j ψ`
  the cut purities (sums of squared eigenvalues) used in `RenyiFull.SharpQuadraticVarianceBound`.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.QVCert

/-- The unnormalised cut purity `tr R_{12}²` (real part). -/
noncomputable def trCut12 (z : Psi) : ℝ := (Matrix.trace (red12 z * red12 z)).re
/-- The unnormalised cut purity `tr R_{13}²`. -/
noncomputable def trCut13 (z : Psi) : ℝ := (Matrix.trace (red13 z * red13 z)).re
/-- The unnormalised cut purity `tr R_{14}²`. -/
noncomputable def trCut14 (z : Psi) : ℝ := (Matrix.trace (red14 z * red14 z)).re

/-- `U = Σ_j (tr R_{1j}²)²` (unnormalised). -/
noncomputable def sumSqCuts (z : Psi) : ℝ := trCut12 z ^ 2 + trCut13 z ^ 2 + trCut14 z ^ 2

/-- **The homogenised defect** `𝔇 = 𝔉² + 5 N² P² - 3 N⁴ P - 6 N² U` of `sec:sup-qk`, a polynomial of
bidegree `(6,6)` in `z, z̄`, for every `z : Psi` (any norm). -/
noncomputable def defectD (z : Psi) : ℝ :=
  sexticF z ^ 2 + 5 * normSqPsi z ^ 2 * purity z ^ 2 - 3 * normSqPsi z ^ 4 * purity z
    - 6 * normSqPsi z ^ 2 * sumSqCuts z

theorem cutPurity12_eq (z : Psi) : cutPurity12 z = trCut12 z := by
  unfold cutPurity12 trCut12; rw [sum_eigenvalues_pow (red12_herm z) 2, pow_two]

theorem cutPurity13_eq (z : Psi) : cutPurity13 z = trCut13 z := by
  unfold cutPurity13 trCut13; rw [sum_eigenvalues_pow (red13_herm z) 2, pow_two]

theorem cutPurity14_eq (z : Psi) : cutPurity14 z = trCut14 z := by
  unfold cutPurity14 trCut14; rw [sum_eigenvalues_pow (red14_herm z) 2, pow_two]

/-- On unit vectors `𝔇` is the defect of (QV): `𝔇 ψ = F² + 3P(P-1) - 6 V_P`,
`V_P = Σ_j (p_j - P/3)²` (`thm:fqe-sharp-quadratic-variance`). -/
theorem defectD_unit {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    defectD ψ = sexticF ψ ^ 2 + 3 * purity ψ * (purity ψ - 1)
      - 6 * ((cutPurity12 ψ - purity ψ / 3) ^ 2 + (cutPurity13 ψ - purity ψ / 3) ^ 2
        + (cutPurity14 ψ - purity ψ / 3) ^ 2) := by
  have hP : purity ψ = trCut12 ψ + trCut13 ψ + trCut14 ψ := rfl
  unfold defectD sumSqCuts
  rw [hψ, cutPurity12_eq, cutPurity13_eq, cutPurity14_eq]
  rw [hP]
  ring

end FormalResearch.FourQubitEntropy.QVCert
