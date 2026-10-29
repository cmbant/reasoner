import FormalResearch.FourQubitEntropy.Tsallis

/-!
# Rényi entropies below one

For `0 < q < 1`, the mean Rényi-`q` entropy (in bits) of the three cuts is at most
`log₂(2^{-q} + 3·6^{-q})/(1-q)`, with the same equality classes as the Tsallis bound.

Paper: `cor:fqe-renyi` (spectral_corollaries.tex). Proof as in the paper: concavity of `log`
and the Tsallis bound.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-- The Rényi-`q` entropy in bits of a Hermitian PSD matrix: `log₂(tr R^q)/(1-q)`. -/
noncomputable def renyiCut (q : ℝ) {R : Mat4} (hR : R.IsHermitian) : ℝ :=
  Real.logb 2 (∑ i, hR.eigenvalues i ^ q) / (1 - q)

/-- The mean Rényi-`q` entropy of the three cuts containing qubit `1`. -/
noncomputable def meanRenyi (q : ℝ) (ψ : Psi) : ℝ :=
  (renyiCut q (red12_herm ψ) + renyiCut q (red13_herm ψ) + renyiCut q (red14_herm ψ)) / 3

/-- The moment `Σ λ^q` of a cut spectrum. -/
noncomputable def cutMoment (q : ℝ) {R : Mat4} (hR : R.IsHermitian) : ℝ :=
  ∑ i, hR.eigenvalues i ^ q

theorem cutMoment_ge_one {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {R : Mat4} (hR : R.IsHermitian)
    (hp : R.PosSemidef) (htr : (Matrix.trace R).re = 1) : 1 ≤ cutMoment q hR := by
  have hs : ∑ i, hR.eigenvalues i = 1 := by rw [sum_eigenvalues_eq_trace, htr]
  rw [← hs]
  unfold cutMoment
  apply Finset.sum_le_sum
  intro i _
  have hm := eigenvalue_mem_Icc hR hp htr i
  have := Real.rpow_le_rpow_of_exponent_ge' hm.1 hm.2 h0.le h1.le
  simpa using this

/-- Three-point Jensen for `log`. -/
theorem log_add_log_add_log_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.log a + Real.log b + Real.log c ≤ 3 * Real.log ((a + b + c) / 3) := by
  have hy : 0 < (a + b + c) / 3 := by positivity
  set y := (a + b + c) / 3
  have k : ∀ x, 0 < x → Real.log x ≤ Real.log y + x / y - 1 := by
    intro x hx
    have := Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [Real.log_div hx.ne' hy.ne'] at this
    linarith
  have h1 := k a ha
  have h2 := k b hb
  have h3 := k c hc
  have : a / y + b / y + c / y = 3 := by
    rw [← add_div, ← add_div]
    simp only [y]; field_simp
  linarith

theorem meanTsallis_eq_moments (q : ℝ) (ψ : Psi) :
    meanTsallis q ψ = (3 - (cutMoment q (red12_herm ψ) + cutMoment q (red13_herm ψ)
      + cutMoment q (red14_herm ψ))) / (3 * (q - 1)) := by
  unfold meanTsallis tsallisCut cutMoment
  rw [← add_div, ← add_div, div_div]
  congr 1 <;> ring

/-- **Rényi entropies below one** (`cor:fqe-renyi`). -/
theorem renyi_le {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    meanRenyi q ψ ≤ Real.logb 2 ((2 : ℝ) ^ (-q) + 3 * (6 : ℝ) ^ (-q)) / (1 - q) := by
  have t12 : (Matrix.trace (red12 ψ)).re = 1 := by rw [trace_red12, hψ]; simp
  have t13 : (Matrix.trace (red13 ψ)).re = 1 := by rw [trace_red13, hψ]; simp
  have t14 : (Matrix.trace (red14 ψ)).re = 1 := by rw [trace_red14, hψ]; simp
  have m12 := cutMoment_ge_one h0 h1 (red12_herm ψ) (red12_psd ψ) t12
  have m13 := cutMoment_ge_one h0 h1 (red13_herm ψ) (red13_psd ψ) t13
  have m14 := cutMoment_ge_one h0 h1 (red14_herm ψ) (red14_psd ψ) t14
  have ht := tsallis_le h0 (by linarith) h1.ne ψ hψ
  rw [meanTsallis_eq_moments] at ht
  unfold tsallisCeiling at ht
  have hq1 : q - 1 < 0 := by linarith
  set S12 := cutMoment q (red12_herm ψ)
  set S13 := cutMoment q (red13_herm ψ)
  set S14 := cutMoment q (red14_herm ψ)
  set m := (2 : ℝ) ^ (-q) + 3 * (6 : ℝ) ^ (-q) with hm
  have hmean : (S12 + S13 + S14) / 3 ≤ m := by
    rw [div_le_iff_of_neg (by linarith)] at ht
    have e : (1 - (2 : ℝ) ^ (-q) - 3 * (6 : ℝ) ^ (-q)) / (q - 1) * (3 * (q - 1))
        = 3 * (1 - m) := by
      have hq1' : q - 1 ≠ 0 := hq1.ne
      have key : ∀ K : ℝ, K / (q - 1) * (3 * (q - 1)) = 3 * K := fun K => by
        field_simp
      rw [key, hm]; ring
    rw [e] at ht
    linarith
  have hl := log_add_log_add_log_le (by linarith : 0 < S12) (by linarith : 0 < S13)
    (by linarith : 0 < S14)
  have hS : 0 < (S12 + S13 + S14) / 3 := by linarith
  have hlm : Real.log ((S12 + S13 + S14) / 3) ≤ Real.log m := Real.log_le_log hS hmean
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1q : 0 < 1 - q := by linarith
  unfold meanRenyi renyiCut
  change (Real.logb 2 S12 / (1 - q) + Real.logb 2 S13 / (1 - q) + Real.logb 2 S14 / (1 - q)) / 3
    ≤ Real.logb 2 m / (1 - q)
  rw [← add_div, ← add_div, div_div, div_le_div_iff₀ (by positivity) h1q]
  unfold Real.logb
  rw [← add_div, ← add_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right l2]
  nlinarith

theorem moment_const_eq (q : ℝ) :
    (1 / 2 : ℝ) ^ q + 3 * (1 / 6 : ℝ) ^ q = (2 : ℝ) ^ (-q) + 3 * (6 : ℝ) ^ (-q) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num),
    ← Real.inv_rpow (by norm_num)]
  norm_num

theorem CutQuadratics_of_LU {φ ψ : Psi} (hφ : normSqPsi φ = 1) (hq : CutQuadratics φ)
    (h : LUEquiv φ ψ) : normSqPsi ψ = 1 ∧ CutQuadratics ψ := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  exact ⟨by rw [normSqPsi_localApply ha hb hc hd, hφ], hq.localApply ha hb hc hd⟩

theorem cutMoment_of_quadratic (q : ℝ) {R : Mat4} (hR : R.IsHermitian)
    (h : (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0) (htr : (Matrix.trace R).re = 1) :
    cutMoment q hR = (2 : ℝ) ^ (-q) + 3 * (6 : ℝ) ^ (-q) := by
  have := cutSum_of_quadratic (fun x => x ^ q) hR h htr
  rw [moment_const_eq] at *
  simpa [cutSum, cutMoment, add_comm] using this

/-- **Rényi entropies below one, equality** (`cor:fqe-renyi`): equality holds iff `ψ` is
local-unitarily equivalent to `M₄` or `conj M₄`. -/
theorem renyi_eq_iff {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    meanRenyi q ψ = Real.logb 2 ((2 : ℝ) ^ (-q) + 3 * (6 : ℝ) ^ (-q)) / (1 - q) ↔
      LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ := by
  have t12 : (Matrix.trace (red12 ψ)).re = 1 := by rw [trace_red12, hψ]; simp
  have t13 : (Matrix.trace (red13 ψ)).re = 1 := by rw [trace_red13, hψ]; simp
  have t14 : (Matrix.trace (red14 ψ)).re = 1 := by rw [trace_red14, hψ]; simp
  have m12 := cutMoment_ge_one h0 h1 (red12_herm ψ) (red12_psd ψ) t12
  have m13 := cutMoment_ge_one h0 h1 (red13_herm ψ) (red13_psd ψ) t13
  have m14 := cutMoment_ge_one h0 h1 (red14_herm ψ) (red14_psd ψ) t14
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1q : 0 < 1 - q := by linarith
  have hq1 : q - 1 < 0 := by linarith
  set S12 := cutMoment q (red12_herm ψ)
  set S13 := cutMoment q (red13_herm ψ)
  set S14 := cutMoment q (red14_herm ψ)
  set m := (2 : ℝ) ^ (-q) + 3 * (6 : ℝ) ^ (-q) with hm
  have hmpos : 0 < m := by rw [hm]; positivity
  constructor
  · intro heq
    -- the mean moment equals `m`
    have hl := log_add_log_add_log_le (by linarith : 0 < S12) (by linarith : 0 < S13)
      (by linarith : 0 < S14)
    have ht := tsallis_le h0 (by linarith) h1.ne ψ hψ
    rw [meanTsallis_eq_moments] at ht
    unfold tsallisCeiling at ht
    have hmean : (S12 + S13 + S14) / 3 ≤ m := by
      rw [div_le_iff_of_neg (by linarith)] at ht
      have hq1' : q - 1 ≠ 0 := hq1.ne
      have key : ∀ K : ℝ, K / (q - 1) * (3 * (q - 1)) = 3 * K := fun K => by
        field_simp
      rw [key] at ht
      rw [hm]; linarith
    have hS : 0 < (S12 + S13 + S14) / 3 := by linarith
    have hlm : Real.log ((S12 + S13 + S14) / 3) ≤ Real.log m := Real.log_le_log hS hmean
    unfold meanRenyi renyiCut at heq
    change (Real.logb 2 S12 / (1 - q) + Real.logb 2 S13 / (1 - q) + Real.logb 2 S14 / (1 - q)) / 3
      = Real.logb 2 m / (1 - q) at heq
    rw [← add_div, ← add_div, div_div, div_eq_div_iff (by positivity) h1q.ne'] at heq
    unfold Real.logb at heq
    rw [← add_div, ← add_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_left_inj' l2.ne'] at heq
    have hlog : Real.log ((S12 + S13 + S14) / 3) = Real.log m := by
      have : (Real.log S12 + Real.log S13 + Real.log S14) * (1 - q) = Real.log m * ((1 - q) * 3) := by
        linarith
      have h3 : Real.log S12 + Real.log S13 + Real.log S14 = 3 * Real.log m := by
        have := mul_right_cancel₀ h1q.ne' (by linarith : (Real.log S12 + Real.log S13 + Real.log S14) * (1 - q)
          = (3 * Real.log m) * (1 - q))
        exact this
      linarith
    have hmeq : (S12 + S13 + S14) / 3 = m := Real.log_injOn_pos hS hmpos hlog
    have : meanTsallis q ψ = tsallisCeiling q := by
      rw [meanTsallis_eq_moments]
      unfold tsallisCeiling
      have hq1' : q - 1 ≠ 0 := hq1.ne
      have : S12 + S13 + S14 = 3 * m := by linarith
      rw [this, hm]
      field_simp
      ring
    exact (tsallis_eq_iff h0 (by linarith) h1.ne ψ hψ).1 this
  · intro hLU
    have hcq : CutQuadratics ψ := by
      rcases hLU with h | h
      · exact (CutQuadratics_of_LU M4_unit M4_cutQuadratics h).2
      · exact (CutQuadratics_of_LU (by rw [normSqPsi_conj]; exact M4_unit)
          M4_cutQuadratics.conj h).2
    have e12 : S12 = m := cutMoment_of_quadratic q _ hcq.q12 t12
    have e13 : S13 = m := cutMoment_of_quadratic q _ hcq.q13 t13
    have e14 : S14 = m := cutMoment_of_quadratic q _ hcq.q14 t14
    unfold meanRenyi renyiCut
    change (Real.logb 2 S12 / (1 - q) + Real.logb 2 S13 / (1 - q) + Real.logb 2 S14 / (1 - q)) / 3
      = Real.logb 2 m / (1 - q)
    rw [e12, e13, e14]; ring

/-- info: 'FormalResearch.FourQubitEntropy.renyi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_le

/-- info: 'FormalResearch.FourQubitEntropy.renyi_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_eq_iff

end FormalResearch.FourQubitEntropy
