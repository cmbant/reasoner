import FormalResearch.FourQubitEntropy.TsallisMajorant
import FormalResearch.FourQubitEntropy.TsallisCoeff

/-!
# Tsallis entropies

For `0 < q < 2`, `q ≠ 1`, the mean Tsallis-`q` entropy of the three cuts is at most
`(1 - 2^{-q} - 3·6^{-q})/(q-1)`, with equality iff `ψ` is local-unitarily equivalent to `M₄` or
`conj M₄`.

Paper: `cor:fqe-tsallis` (spectral_corollaries.tex). The proof is that of the paper: apply the
cubic-majorant criterion (`Majorant.lean`) to the Hermite cubic of `f_q` (`TsallisMajorant.lean`),
whose coefficient condition (T) is `TsallisCoeff.lean`.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-- The Tsallis-`q` entropy `(1 - tr R^q)/(q-1)` of a Hermitian PSD matrix, from its eigenvalues. -/
noncomputable def tsallisCut (q : ℝ) {R : Mat4} (hR : R.IsHermitian) : ℝ :=
  (1 - ∑ i, hR.eigenvalues i ^ q) / (q - 1)

/-- The mean Tsallis-`q` entropy of the three two-qubit marginals containing qubit `1`:
`⅓ Σ_{j=2}^4 (1 - tr ρ_{1j}^q)/(q-1)`. -/
noncomputable def meanTsallis (q : ℝ) (ψ : Psi) : ℝ :=
  (tsallisCut q (red12_herm ψ) + tsallisCut q (red13_herm ψ) + tsallisCut q (red14_herm ψ)) / 3

theorem cutSum_tsallisF (q : ℝ) {R : Mat4} (hR : R.IsHermitian) (htr : (Matrix.trace R).re = 1) :
    cutSum (tsallisF q) hR = tsallisCut q hR := by
  have hs : ∑ i, hR.eigenvalues i = 1 := by rw [sum_eigenvalues_eq_trace, htr]
  unfold cutSum tsallisF tsallisCut
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hs]
  rw [show q - 1 = -(1 - q) by ring, div_neg, ← neg_div]
  ring_nf

theorem meanTsallis_eq_meanSpec (q : ℝ) (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    meanTsallis q ψ = meanSpec (tsallisF q) ψ := by
  have t12 : (Matrix.trace (red12 ψ)).re = 1 := by rw [trace_red12, hψ]; simp
  have t13 : (Matrix.trace (red13 ψ)).re = 1 := by rw [trace_red13, hψ]; simp
  have t14 : (Matrix.trace (red14 ψ)).re = 1 := by rw [trace_red14, hψ]; simp
  unfold meanTsallis meanSpec
  rw [cutSum_tsallisF q _ t12, cutSum_tsallisF q _ t13, cutSum_tsallisF q _ t14]

/-- The ceiling `(1 - 2^{-q} - 3·6^{-q})/(q-1)`. -/
noncomputable def tsallisCeiling (q : ℝ) : ℝ :=
  (1 - (2 : ℝ) ^ (-q) - 3 * (6 : ℝ) ^ (-q)) / (q - 1)

theorem tsallisCeiling_eq (q : ℝ) :
    tsallisCeiling q = tsallisF q (1 / 2) + 3 * tsallisF q (1 / 6) := by
  unfold tsallisCeiling tsallisF
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num),
    ← Real.inv_rpow (by norm_num)]
  rw [show q - 1 = -(1 - q) by ring, div_neg, ← neg_div]
  norm_num
  ring_nf

theorem tsallis_B_eq {q : ℝ} :
    (1 / 2 : ℝ) ^ q = 3 * (3 : ℝ) ^ (q - 1) * (1 / 6 : ℝ) ^ q := by
  have e1 : (1 / 2 : ℝ) = 3 * (1 / 6) := by norm_num
  rw [e1, Real.mul_rpow (by norm_num) (by norm_num), Real.rpow_sub_one (by norm_num)]
  field_simp

/-- The coefficient condition `b + 17a/12 < 0` for the Tsallis Hermite cubic (eq. (T)). -/
theorem tsallis_coeff_neg {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) :
    tsB q + 17 * tsA q / 12 < 0 := by
  have hA : 0 < (1 / 6 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) _
  have eq : tsB q + 17 * tsA q / 12 =
      9 * (1 / 6 : ℝ) ^ q * ((5 + 3 * q) - (15 - 7 * q) * (3 : ℝ) ^ (q - 1)) / (2 * (1 - q)) := by
    have hne : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have hne' : (q - 1) ≠ 0 := sub_ne_zero.2 h1
    unfold tsA tsB
    rw [tsallis_B_eq]
    field_simp
    ring
  rw [eq]
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · have := tsallis_g_gt_one h0 hlt
    apply div_neg_of_neg_of_pos
    · have : (5 + 3 * q) - (15 - 7 * q) * (3 : ℝ) ^ (q - 1) < 0 := by linarith
      exact mul_neg_of_pos_of_neg (by positivity) this
    · linarith
  · have := tsallis_g_lt_one hgt h2
    apply div_neg_of_pos_of_neg
    · have : 0 < (5 + 3 * q) - (15 - 7 * q) * (3 : ℝ) ^ (q - 1) := by linarith
      exact mul_pos (by positivity) this
    · linarith

/-- The Tsallis function is cubically majorized, as required by the criterion. -/
theorem tsallis_majorant {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) :
    Majorant (tsallisF q) (tsA q) (tsB q) (tsC q) (tsD q) := by
  obtain ⟨hpos, -⟩ := tsallis_hermite h0 h2 h1
  obtain ⟨i0, i1, -, -⟩ := tsallis_interpolation h1
  refine ⟨?_, i0, i1⟩
  intro x hx
  by_cases h6 : x = 1 / 6
  · rw [h6, i0]
  by_cases h5 : x = 1 / 2
  · rw [h5, i1]
  exact (hpos x hx.1 h6 h5).le

/-- **Tsallis entropies** (`cor:fqe-tsallis`). For `0 < q < 2`, `q ≠ 1`, the mean Tsallis-`q`
entropy of the three cuts of a unit four-qubit vector is at most
`(1 - 2^{-q} - 3·6^{-q})/(q-1)`. -/
theorem tsallis_le {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) (ψ : Psi)
    (hψ : normSqPsi ψ = 1) : meanTsallis q ψ ≤ tsallisCeiling q := by
  obtain ⟨-, ha⟩ := tsallis_hermite h0 h2 h1
  have := majorant_le (tsallis_majorant h0 h2 h1) ha.le
    (by linarith [tsallis_coeff_neg h0 h2 h1]) ψ hψ
  rw [meanTsallis_eq_meanSpec q ψ hψ, tsallisCeiling_eq, ← meanSpec_M4]
  exact this

/-- **Tsallis entropies, equality** (`cor:fqe-tsallis`): equality holds iff `ψ` is
local-unitarily equivalent to `M₄` or `conj M₄`. -/
theorem tsallis_eq_iff {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) (ψ : Psi)
    (hψ : normSqPsi ψ = 1) :
    meanTsallis q ψ = tsallisCeiling q ↔ LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ := by
  obtain ⟨hpos, ha⟩ := tsallis_hermite h0 h2 h1
  rw [meanTsallis_eq_meanSpec q ψ hψ, tsallisCeiling_eq, ← meanSpec_M4]
  exact majorant_eq_iff (tsallis_majorant h0 h2 h1) ha.le (tsallis_coeff_neg h0 h2 h1)
    (fun x hx h6 h5 => hpos x hx.1 h6 h5) ψ hψ

/-- info: 'FormalResearch.FourQubitEntropy.tsallis_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms tsallis_le

/-- info: 'FormalResearch.FourQubitEntropy.tsallis_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms tsallis_eq_iff

end FormalResearch.FourQubitEntropy
