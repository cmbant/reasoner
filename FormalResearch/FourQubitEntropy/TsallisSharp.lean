import FormalResearch.FourQubitEntropy.Stability

/-!
# Sharpness of the Tsallis range

`M₄` is not a maximizer of the mean Tsallis-`q` entropy for any `q > 2`: the cluster state `C₄`
(cut spectra `(1/2,1/2,0,0)`, `(1/4)⁴`, `(1/4)⁴`) has strictly larger mean Tsallis entropy.

Paper: "Sharpness of the Tsallis range" paragraph after `cor:fqe-tsallis`
(spectral_corollaries.tex).
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-! ### The reduced matrices of the cluster state -/

theorem red12_cluster4 : red12 cluster4 = Matrix.diagonal (fun i : Fin 2 × Fin 2 =>
    if i = (0, 0) ∨ i = (1, 1) then (1 / 2 : ℂ) else 0) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [red12, cluster4, Fin.sum_univ_two, Matrix.diagonal_apply, map_ofNat, map_neg, map_div₀, map_one] <;> norm_num

theorem red13_cluster4 : red13 cluster4 = (1 / 4 : ℂ) • (1 : Mat4) := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  fin_cases a <;> fin_cases c <;> fin_cases a' <;> fin_cases c' <;>
    simp [red13, cluster4, Fin.sum_univ_two, Matrix.one_apply, map_ofNat, map_neg, map_div₀, map_one] <;> norm_num

theorem red14_cluster4 : red14 cluster4 = (1 / 4 : ℂ) • (1 : Mat4) := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  fin_cases a <;> fin_cases d <;> fin_cases a' <;> fin_cases d' <;>
    simp [red14, cluster4, Fin.sum_univ_two, Matrix.one_apply, map_ofNat, map_neg, map_div₀, map_one] <;> norm_num

/-! ### Cut moments of the cluster state -/

/-- A Hermitian `R` with `(R - α)(R - β) = 0` (real `α, β`) has eigenvalues in `{α, β}`. -/
theorem eigenvalue_of_quadratic' {R : Mat4} (hR : R.IsHermitian) {α β : ℝ}
    (h : (R - (α : ℂ) • 1) * (R - (β : ℂ) • 1) = 0) (i : Fin 2 × Fin 2) :
    hR.eigenvalues i = α ∨ hR.eigenvalues i = β := by
  have hv0 := hR.mulVec_eigenvectorBasis i
  set v : Fin 2 × Fin 2 → ℂ := ⇑(hR.eigenvectorBasis i) with hvdef
  have hv : R *ᵥ v = ((hR.eigenvalues i : ℝ) : ℂ) • v := by
    rw [hv0]; exact (Complex.coe_smul _ _).symm
  have hne : v ≠ 0 := by
    have := hR.eigenvectorBasis.orthonormal.ne_zero i
    intro h0; apply this; ext j; exact congrFun h0 j
  have key : ((((hR.eigenvalues i : ℝ) : ℂ) - α) * (((hR.eigenvalues i : ℝ) : ℂ) - β)) • v = 0 := by
    have e1 : (R - (β : ℂ) • 1) *ᵥ v = (((hR.eigenvalues i : ℝ) : ℂ) - β) • v := by
      rw [Matrix.sub_mulVec, hv, Matrix.smul_mulVec, Matrix.one_mulVec]; module
    have e2 : (R - (α : ℂ) • 1) *ᵥ ((((hR.eigenvalues i : ℝ) : ℂ) - β) • v)
        = ((((hR.eigenvalues i : ℝ) : ℂ) - α) * (((hR.eigenvalues i : ℝ) : ℂ) - β)) • v := by
      rw [Matrix.mulVec_smul, Matrix.sub_mulVec, hv, Matrix.smul_mulVec, Matrix.one_mulVec]
      module
    rw [← e2, ← e1, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]
  rcases smul_eq_zero.mp key with hz | hz
  · rcases mul_eq_zero.mp hz with h1 | h2
    · left
      have h' : ((hR.eigenvalues i : ℝ) : ℂ) = (α : ℂ) := sub_eq_zero.mp h1
      exact_mod_cast h'
    · right
      have h' : ((hR.eigenvalues i : ℝ) : ℂ) = (β : ℂ) := sub_eq_zero.mp h2
      exact_mod_cast h'
  · exact absurd hz hne

theorem cutMoment_cluster12 {q : ℝ} (h0 : 0 < q) :
    cutMoment q (red12_herm cluster4) = (2 : ℝ) ^ (1 - q) := by
  have hq : (red12 cluster4 - ((0 : ℝ) : ℂ) • 1) * (red12 cluster4 - ((1 / 2 : ℝ) : ℂ) • 1) = 0 := by
    rw [red12_cluster4]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.diagonal_apply,
        Matrix.one_apply] <;> norm_num
  have htr : (Matrix.trace (red12 cluster4)).re = 1 := by
    rw [trace_red12, cluster4_vals.1]; simp
  have hf : ∀ i, (red12_herm cluster4).eigenvalues i ^ q
      = (2 : ℝ) ^ (1 - q) * (red12_herm cluster4).eigenvalues i := by
    intro i
    rcases eigenvalue_of_quadratic' (red12_herm cluster4) hq i with h | h <;> rw [h]
    · rw [Real.zero_rpow h0.ne']; simp
    · rw [Real.rpow_sub (by norm_num), Real.rpow_one, one_div, Real.inv_rpow (by norm_num)]
      field_simp
  have hs : ∑ i, (red12_herm cluster4).eigenvalues i = 1 := by
    rw [sum_eigenvalues_eq_trace, htr]
  unfold cutMoment
  simp only [hf, ← Finset.mul_sum, hs, mul_one]

theorem cutMoment_cluster13 {q : ℝ} :
    cutMoment q (red13_herm cluster4) = 4 * (1 / 4 : ℝ) ^ q := by
  have hq : (red13 cluster4 - (((1 / 4 : ℝ)) : ℂ) • 1) * (red13 cluster4 - (((1 / 4 : ℝ)) : ℂ) • 1) = 0 := by
    rw [red13_cluster4]
    ext i j
    simp
  have hf : ∀ i, (red13_herm cluster4).eigenvalues i = 1 / 4 := by
    intro i
    rcases eigenvalue_of_quadratic' (red13_herm cluster4) hq i with h | h <;> exact h
  unfold cutMoment
  simp [hf]

theorem cutMoment_cluster14 {q : ℝ} :
    cutMoment q (red14_herm cluster4) = 4 * (1 / 4 : ℝ) ^ q := by
  have hq : (red14 cluster4 - (((1 / 4 : ℝ)) : ℂ) • 1) * (red14 cluster4 - (((1 / 4 : ℝ)) : ℂ) • 1) = 0 := by
    rw [red14_cluster4]
    ext i j
    simp
  have hf : ∀ i, (red14_herm cluster4).eigenvalues i = 1 / 4 := by
    intro i
    rcases eigenvalue_of_quadratic' (red14_herm cluster4) hq i with h | h <;> exact h
  unfold cutMoment
  simp [hf]

/-! ### The calculus: `1 + 9·3^{-q} - 8·2^{-q} > 0` for `q > 2` -/

/-- `p(q) = 1 + 9·3^{-q} - 8·2^{-q}`; `m_q - c_q = 2^{-q} p(q) / 3`. -/
noncomputable def sharpP (x : ℝ) : ℝ := 1 + 9 * (3 : ℝ) ^ (-x) - 8 * (2 : ℝ) ^ (-x)

theorem sharpP_two : sharpP 2 = 0 := by
  unfold sharpP
  rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, Real.rpow_intCast]
  norm_num

theorem sharpP_hasDerivAt (x : ℝ) :
    HasDerivAt sharpP (8 * Real.log 2 * (2 : ℝ) ^ (-x) - 9 * Real.log 3 * (3 : ℝ) ^ (-x)) x := by
  have h3 := (HasDerivAt.const_rpow (a := (3 : ℝ)) (by norm_num) (hasDerivAt_neg x))
  have h2 := (HasDerivAt.const_rpow (a := (2 : ℝ)) (by norm_num) (hasDerivAt_neg x))
  have := ((h3.const_mul 9).const_add 1).sub (h2.const_mul 8)
  refine this.congr_deriv ?_
  ring

/-- For `x ≥ 2`: `3^{-x} ≤ (4/9) 2^{-x}`. -/
theorem three_pow_le {x : ℝ} (hx : 2 ≤ x) : (3 : ℝ) ^ (-x) ≤ 4 / 9 * (2 : ℝ) ^ (-x) := by
  have e : (3 : ℝ) ^ (-x) = (2 / 3 : ℝ) ^ x * (2 : ℝ) ^ (-x) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num),
      Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3) x]
    have h2 : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : 0 < (3 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
    field_simp
  have h : (2 / 3 : ℝ) ^ x ≤ (2 / 3 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hx
  rw [e]
  have h2 : (2 / 3 : ℝ) ^ (2 : ℝ) = 4 / 9 := by
    rw [Real.rpow_two]; norm_num
  rw [h2] at h
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (by norm_num) _)

theorem sharpP_deriv_pos {x : ℝ} (hx : 2 ≤ x) :
    0 < 8 * Real.log 2 * (2 : ℝ) ^ (-x) - 9 * Real.log 3 * (3 : ℝ) ^ (-x) := by
  have h := three_pow_le hx
  have l3 : Real.log 3 < 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_lt_log (by norm_num) (by norm_num [Real.rpow_two])
  have l3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have p2 : 0 < (2 : ℝ) ^ (-x) := Real.rpow_pos_of_pos (by norm_num) _
  have : 9 * Real.log 3 * (3 : ℝ) ^ (-x) ≤ 9 * Real.log 3 * (4 / 9 * (2 : ℝ) ^ (-x)) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  nlinarith

theorem sharpP_pos {q : ℝ} (hq : 2 < q) : 0 < sharpP q := by
  have hm : StrictMonoOn sharpP (Set.Icc 2 q) := by
    apply HM.strictMono_of_pos (g' := fun x => 8 * Real.log 2 * (2 : ℝ) ^ (-x)
      - 9 * Real.log 3 * (3 : ℝ) ^ (-x))
    · exact fun x _ => (sharpP_hasDerivAt x).continuousAt.continuousWithinAt
    · exact fun x _ => sharpP_hasDerivAt x
    · exact fun x hx => sharpP_deriv_pos hx.1.le
  have := hm ⟨le_rfl, hq.le⟩ ⟨hq.le, le_rfl⟩ hq
  rwa [sharpP_two] at this

theorem meanTsallis_M4 (q : ℝ) : meanTsallis q M4 = tsallisCeiling q := by
  rw [meanTsallis_eq_meanSpec q M4 M4_unit, tsallisCeiling_eq, meanSpec_M4]

/-- **`M₄` is not a mean Tsallis-`q` maximizer for any `q > 2`**
(sharpness of the range in `cor:fqe-tsallis`): the cluster state `C₄` has strictly larger mean
Tsallis-`q` entropy. -/
theorem tsallis_cluster4_gt {q : ℝ} (hq : 2 < q) :
    meanTsallis q M4 < meanTsallis q cluster4 := by
  have h0 : 0 < q := by linarith
  rw [meanTsallis_M4, meanTsallis_eq_moments, cutMoment_cluster12 h0, cutMoment_cluster13,
    cutMoment_cluster14]
  unfold tsallisCeiling
  set u : ℝ := (2 : ℝ) ^ (-q) with hu
  set v : ℝ := (3 : ℝ) ^ (-q) with hv
  have hup : 0 < u := Real.rpow_pos_of_pos (by norm_num) _
  have e6 : (6 : ℝ) ^ (-q) = u * v := by
    rw [hu, hv, ← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have h2 : (1 / 2 : ℝ) ^ q = u := by
    rw [hu, Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num), one_div]
  have e4 : (1 / 4 : ℝ) ^ q = u * u := by
    rw [show (1 / 4 : ℝ) = (1 / 2) * (1 / 2) by norm_num, Real.mul_rpow (by norm_num) (by norm_num),
      h2]
  have e2 : (2 : ℝ) ^ (1 - q) = 2 * u := by
    rw [hu, sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  have hp := sharpP_pos hq
  unfold sharpP at hp
  rw [← hv, ← hu] at hp
  have hq1 : 0 < q - 1 := by linarith
  rw [e6, e4, e2]
  rw [div_lt_div_iff₀ hq1 (by positivity)]
  have : 0 < u * (1 + 9 * v - 8 * u) := mul_pos hup (by linarith)
  nlinarith

/-- info: 'FormalResearch.FourQubitEntropy.tsallis_cluster4_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tsallis_cluster4_gt

end FormalResearch.FourQubitEntropy
