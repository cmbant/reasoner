import FormalResearch.FourQubitEntropy.Spectral
import FormalResearch.FourQubitEntropy.HermiteBound

/-!
# The four-qubit entropy bound

For a unit vector `ψ`, the mean von Neumann entropy of the three two-qubit marginals containing
qubit `1` is at most `1 + ½ log₂ 3`.

Proof: majorise `-λ ln λ` on each cut's spectrum by the Hermite cubic, sum, and use `P ≥ 1`
(purity identity) and `F ≥ 0` (sextic inequality).
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

/-! ### Reduced matrices are Gram matrices -/

theorem red12_eq (ψ : Psi) :
    red12 ψ = (Matrix.of fun (i : Fin 2 × Fin 2) (j : Fin 2 × Fin 2) => ψ i.1 i.2 j.1 j.2) *
      (Matrix.of fun (i : Fin 2 × Fin 2) (j : Fin 2 × Fin 2) => ψ i.1 i.2 j.1 j.2)ᴴ := by
  ext i j
  simp [red12, Matrix.mul_apply, Fintype.sum_prod_type]

theorem red13_eq (ψ : Psi) :
    red13 ψ = (Matrix.of fun (i : Fin 2 × Fin 2) (j : Fin 2 × Fin 2) => ψ i.1 j.1 i.2 j.2) *
      (Matrix.of fun (i : Fin 2 × Fin 2) (j : Fin 2 × Fin 2) => ψ i.1 j.1 i.2 j.2)ᴴ := by
  ext i j
  simp [red13, Matrix.mul_apply, Fintype.sum_prod_type]

theorem red14_eq (ψ : Psi) :
    red14 ψ = (Matrix.of fun (i : Fin 2 × Fin 2) (j : Fin 2 × Fin 2) => ψ i.1 j.1 j.2 i.2) *
      (Matrix.of fun (i : Fin 2 × Fin 2) (j : Fin 2 × Fin 2) => ψ i.1 j.1 j.2 i.2)ᴴ := by
  ext i j
  simp [red14, Matrix.mul_apply, Fintype.sum_prod_type]

theorem red12_psd (ψ : Psi) : (red12 ψ).PosSemidef := by
  rw [red12_eq]; exact Matrix.posSemidef_self_mul_conjTranspose _
theorem red13_psd (ψ : Psi) : (red13 ψ).PosSemidef := by
  rw [red13_eq]; exact Matrix.posSemidef_self_mul_conjTranspose _
theorem red14_psd (ψ : Psi) : (red14 ψ).PosSemidef := by
  rw [red14_eq]; exact Matrix.posSemidef_self_mul_conjTranspose _

theorem trace_red12 (ψ : Psi) : Matrix.trace (red12 ψ) = (normSqPsi ψ : ℂ) := by
  simp [Matrix.trace, red12, normSqPsi, Fintype.sum_prod_type, Complex.mul_conj, Fin.sum_univ_two]
  try ring
theorem trace_red13 (ψ : Psi) : Matrix.trace (red13 ψ) = (normSqPsi ψ : ℂ) := by
  simp [Matrix.trace, red13, normSqPsi, Fintype.sum_prod_type, Complex.mul_conj, Fin.sum_univ_two]
  try ring
theorem trace_red14 (ψ : Psi) : Matrix.trace (red14 ψ) = (normSqPsi ψ : ℂ) := by
  simp [Matrix.trace, red14, normSqPsi, Fintype.sum_prod_type, Complex.mul_conj, Fin.sum_univ_two]
  try ring

/-! ### Spectral bound on one cut -/

/-- `Σ λ^k = Re tr R^k` for the eigenvalues of a Hermitian `R`. -/
theorem sum_eigenvalues_pow {R : Mat4} (hR : R.IsHermitian) (k : ℕ) :
    ∑ i, hR.eigenvalues i ^ k = (Matrix.trace (R ^ k)).re := by
  rw [trace_pow_eq hR k]
  simp [Complex.re_sum, ← Complex.ofReal_pow]

theorem cut_bound {R : Mat4} (hR : R.IsHermitian) (hp : R.PosSemidef) :
    ∑ i, Real.negMulLog (hR.eigenvalues i)
      ≤ hermA * (Matrix.trace (R * R * R)).re + hermB * (Matrix.trace (R * R)).re
        + hermC * (Matrix.trace R).re + 4 * hermD := by
  have h1 : ∑ i, Real.negMulLog (hR.eigenvalues i) ≤ ∑ i, hermCubic (hR.eigenvalues i) :=
    Finset.sum_le_sum fun i _ => negMulLog_le_hermCubic (hp.eigenvalues_nonneg i)
  have e3 := sum_eigenvalues_pow hR 3
  have e2 := sum_eigenvalues_pow hR 2
  have e1 := sum_eigenvalues_pow hR 1
  rw [pow_succ, pow_two] at e3
  rw [pow_two] at e2
  rw [pow_one] at e1
  simp only [pow_one] at e1
  have : ∑ i, hermCubic (hR.eigenvalues i)
      = hermA * ∑ i, hR.eigenvalues i ^ 3 + hermB * ∑ i, hR.eigenvalues i ^ 2
        + hermC * ∑ i, hR.eigenvalues i + 4 * hermD := by
    simp only [hermCubic, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  rw [this] at h1
  have e3' : ∑ i, hR.eigenvalues i ^ 3 = (Matrix.trace (R * R * R)).re := by
    rw [sum_eigenvalues_pow hR 3, pow_succ, pow_two]
  have e2' : ∑ i, hR.eigenvalues i ^ 2 = (Matrix.trace (R * R)).re := by
    rw [sum_eigenvalues_pow hR 2, pow_two]
  have e1' : ∑ i, hR.eigenvalues i = (Matrix.trace R).re := by
    simpa using sum_eigenvalues_pow hR 1
  rw [e3', e2', e1'] at h1
  exact h1

/-! ### The entropy bound -/

/-- Von Neumann entropy in bits, from the eigenvalues. -/
noncomputable def vnEntropy {R : Mat4} (hR : R.IsHermitian) : ℝ :=
  (∑ i, Real.negMulLog (hR.eigenvalues i)) / Real.log 2

/-- The mean entropy of the three two-qubit marginals containing qubit `1`. -/
noncomputable def meanEntropy (ψ : Psi) : ℝ :=
  (vnEntropy (red12_herm ψ) + vnEntropy (red13_herm ψ) + vnEntropy (red14_herm ψ)) / 3

/-- The entropy of the three marginals is bounded by the Hermite cubic sums. -/
theorem entropy_sum_le (ψ : Psi) :
    (∑ i, Real.negMulLog ((red12_herm ψ).eigenvalues i))
      + (∑ i, Real.negMulLog ((red13_herm ψ).eigenvalues i))
      + (∑ i, Real.negMulLog ((red14_herm ψ).eigenvalues i))
      ≤ hermA * cubicMoment ψ + hermB * purity ψ + 3 * hermC * normSqPsi ψ + 12 * hermD := by
  have b12 := cut_bound (red12_herm ψ) (red12_psd ψ)
  have b13 := cut_bound (red13_herm ψ) (red13_psd ψ)
  have b14 := cut_bound (red14_herm ψ) (red14_psd ψ)
  have t12 : (Matrix.trace (red12 ψ)).re = normSqPsi ψ := by rw [trace_red12]; simp
  have t13 : (Matrix.trace (red13 ψ)).re = normSqPsi ψ := by rw [trace_red13]; simp
  have t14 : (Matrix.trace (red14 ψ)).re = normSqPsi ψ := by rw [trace_red14]; simp
  rw [t12] at b12
  rw [t13] at b13
  rw [t14] at b14
  unfold cubicMoment purity
  linarith

/-- **Four-qubit entropy bound.** For a unit vector, the mean entropy of the three two-qubit
marginals containing qubit `1` is at most `1 + ½ log₂ 3`. -/
theorem meanEntropy_le (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    meanEntropy ψ ≤ 1 + Real.log 3 / (2 * Real.log 2) := by
  have hsum := entropy_sum_le ψ
  have hP := purity_ge ψ
  have hF := sexticF_nonneg ψ
  have hT : sexticF ψ = 17 * purity ψ - 12 * cubicMoment ψ - 12 := by
    unfold sexticF; rw [hψ]; ring
  rw [hψ] at hsum hP
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l3a := lt_log_three
  have l3b := log_three_lt
  have hA := hermA_pos
  have hP' : 0 ≤ purity ψ - 1 := by nlinarith
  have hb : hermB + 17 / 12 * hermA ≤ 0 := by unfold hermB hermA; linarith
  have k1 := mul_nonneg hA.le hF
  have k2 := mul_nonneg (neg_nonneg.2 hb) hP'
  have key : hermA * cubicMoment ψ + hermB * purity ψ + 3 * hermC * 1 + 12 * hermD
      ≤ 3 * Real.log 2 + 3 / 2 * Real.log 3 := by
    have hc : cubicMoment ψ = (17 * purity ψ - 12 - sexticF ψ) / 12 := by linarith
    rw [hc]
    unfold hermA hermB hermC hermD at *
    nlinarith [k1, k2]
  have hfin : (∑ i, Real.negMulLog ((red12_herm ψ).eigenvalues i))
      + (∑ i, Real.negMulLog ((red13_herm ψ).eigenvalues i))
      + (∑ i, Real.negMulLog ((red14_herm ψ).eigenvalues i)) ≤ 3 * Real.log 2 + 3 / 2 * Real.log 3 :=
    le_trans hsum (by linarith)
  unfold meanEntropy vnEntropy
  rw [← add_div, ← add_div, div_div, div_le_iff₀ (by positivity)]
  have : (1 + Real.log 3 / (2 * Real.log 2)) * (Real.log 2 * 3) = 3 * Real.log 2 + 3 / 2 * Real.log 3 := by
    field_simp
  rw [this]
  exact hfin

end FormalResearch.FourQubitEntropy
