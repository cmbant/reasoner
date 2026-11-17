module

public import FormalResearch.Special.BarnesGrowth

/-!
# The kernel `cosh πξ + cos θ` of `thm:BG`: zeros, periodicity, bounds

For real `θ` with `|θ| < π`, put `kerD θ ξ = cosh (π ξ) + cos θ` (`ξ ∈ ℂ`) and `zOf ξ = 1/2 + i ξ/2`.
Proved:

* `kerD_periodic : kerD θ (ξ - 2i) = kerD θ ξ` and `zOf (ξ - 2i) = zOf ξ + 1` (the shift
  `ξ ↦ ξ - 2i` of the proof of `thm:BG` moves the Meixner–Pollaczek argument by one);
* the zeros of `kerD θ` in the strip `-2 ≤ Im ξ ≤ 0` are exactly `a₊ = -i(1 - θ/π)` and
  `a₋ = -i(1 + θ/π)`, both simple (`kerD_zero_iff_of_mem_strip`, `hasDerivAt_kerD`);
* on the real line `kerD θ x ≥ c₀ cosh πx` with `c₀ = min 1 (1 + cos θ) > 0`; on `|Re ξ| ≥ 1`,
  `-2 ≤ Im ξ ≤ 0`: `|kerD θ ξ| ≥ e^{π |Re ξ|}/4` (`norm_kerD_ge`).
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex
open scoped Real

/-- `z(ξ) = 1/2 + iξ/2`, the Meixner–Pollaczek argument. -/
noncomputable def zOf (ξ : ℂ) : ℂ := 1 / 2 + I * ξ / 2

/-- The kernel `cosh πξ + cos θ`. -/
noncomputable def kerD (θ : ℝ) (ξ : ℂ) : ℂ := Complex.cosh (π * ξ) + (Real.cos θ : ℂ)

/-- Zero `a₊ = -i(1 - θ/π)` of the kernel, where `z(a₊) = 1 - θ/(2π)`. -/
noncomputable def kerPlus (θ : ℝ) : ℂ := -I * (1 - (θ : ℂ) / π)

/-- Zero `a₋ = -i(1 + θ/π)` of the kernel, where `z(a₋) = 1 + θ/(2π)`. -/
noncomputable def kerMinus (θ : ℝ) : ℂ := -I * (1 + (θ : ℂ) / π)

lemma zOf_sub_two_I (ξ : ℂ) : zOf (ξ - 2 * I) = zOf ξ + 1 := by
  unfold zOf
  have : I * I = -1 := I_mul_I
  linear_combination (-1 : ℂ) * this

lemma kerD_sub_two_I (θ : ℝ) (ξ : ℂ) : kerD θ (ξ - 2 * I) = kerD θ ξ := by
  unfold kerD
  congr 1
  have : (π : ℂ) * (ξ - 2 * I) = π * ξ - 2 * π * I := by ring
  rw [this]
  exact cosh_periodic.sub_eq _

lemma exp_pi_sub_two_I (ξ : ℂ) : Complex.exp (π * (ξ - 2 * I)) = Complex.exp (π * ξ) := by
  have : (π : ℂ) * (ξ - 2 * I) = π * ξ - 2 * π * I := by ring
  rw [this]
  exact Complex.exp_periodic.sub_eq _

lemma I_mul_neg_I_mul (x : ℂ) : I * (-I * x) = x := by
  rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]

lemma zOf_kerPlus (θ : ℝ) : zOf (kerPlus θ) = 1 - ((θ : ℂ) / (2 * π)) := by
  unfold zOf kerPlus
  rw [I_mul_neg_I_mul]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

lemma zOf_kerMinus (θ : ℝ) : zOf (kerMinus θ) = 1 + ((θ : ℂ) / (2 * π)) := by
  unfold zOf kerMinus
  rw [I_mul_neg_I_mul]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

lemma kerD_kerPlus (θ : ℝ) : kerD θ (kerPlus θ) = 0 := by
  unfold kerD kerPlus
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h : (π : ℂ) * (-I * (1 - (θ : ℂ) / π)) = -(((π - θ : ℝ) : ℂ) * I) := by
    push_cast; field_simp
  rw [h, Complex.cosh_neg, Complex.cosh_mul_I]
  push_cast
  rw [Complex.cos_pi_sub]
  ring

lemma kerD_kerMinus (θ : ℝ) : kerD θ (kerMinus θ) = 0 := by
  unfold kerD kerMinus
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h : (π : ℂ) * (-I * (1 + (θ : ℂ) / π)) = -(((π + θ : ℝ) : ℂ) * I) := by
    push_cast; field_simp
  rw [h, Complex.cosh_neg, Complex.cosh_mul_I]
  push_cast
  rw [add_comm (π : ℂ) θ, Complex.cos_add_pi]
  ring


lemma sin_ne_zero_of_abs_lt {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) : Real.sin θ ≠ 0 := by
  rcases lt_or_gt_of_ne h0 with h | h
  · have h1 : 0 < Real.sin (-θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by have := neg_abs_le θ; have := abs_lt.mp hθ; linarith)
    rw [Real.sin_neg] at h1; linarith
  · exact (Real.sin_pos_of_pos_of_lt_pi h (by have := abs_lt.mp hθ; linarith)).ne'

lemma hasDerivAt_kerD (θ : ℝ) (a : ℂ) :
    HasDerivAt (kerD θ) (Complex.sinh (π * a) * π) a := by
  have h := (((hasDerivAt_id a).const_mul (π : ℂ)).ccosh).add_const ((Real.cos θ : ℝ) : ℂ)
  have h2 : HasDerivAt (fun ξ : ℂ => Complex.cosh (π * ξ) + ((Real.cos θ : ℝ) : ℂ))
      (Complex.sinh (π * a) * π) a := by simpa using h
  exact h2

lemma sinh_kerPlus (θ : ℝ) : Complex.sinh (π * kerPlus θ) = -(Real.sin θ : ℂ) * I := by
  unfold kerPlus
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h : (π : ℂ) * (-I * (1 - (θ : ℂ) / π)) = -(((π - θ : ℝ) : ℂ) * I) := by
    push_cast; field_simp
  rw [h, Complex.sinh_neg, Complex.sinh_mul_I]
  push_cast
  rw [Complex.sin_pi_sub]
  ring

lemma sinh_kerMinus (θ : ℝ) : Complex.sinh (π * kerMinus θ) = (Real.sin θ : ℂ) * I := by
  unfold kerMinus
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h : (π : ℂ) * (-I * (1 + (θ : ℂ) / π)) = -(((π + θ : ℝ) : ℂ) * I) := by
    push_cast; field_simp
  rw [h, Complex.sinh_neg, Complex.sinh_mul_I]
  push_cast
  rw [add_comm (π : ℂ) θ, Complex.sin_add_pi]
  ring

lemma deriv_kerD_kerPlus_ne {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) :
    deriv (kerD θ) (kerPlus θ) ≠ 0 := by
  rw [(hasDerivAt_kerD θ _).deriv, sinh_kerPlus]
  have := sin_ne_zero_of_abs_lt h0 hθ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h' : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast this
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h') Complex.I_ne_zero) hπ

lemma deriv_kerD_kerMinus_ne {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| < π) :
    deriv (kerD θ) (kerMinus θ) ≠ 0 := by
  rw [(hasDerivAt_kerD θ _).deriv, sinh_kerMinus]
  have := sin_ne_zero_of_abs_lt h0 hθ
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h' : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast this
  exact mul_ne_zero (mul_ne_zero h' Complex.I_ne_zero) hπ

lemma kerPlus_ne_kerMinus {θ : ℝ} (h0 : θ ≠ 0) : kerPlus θ ≠ kerMinus θ := by
  intro h
  unfold kerPlus kerMinus at h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : (θ : ℂ) / π = 0 := by
    have h2 : (-I) * (1 - (θ : ℂ) / π) = -I * (1 + (θ : ℂ) / π) := h
    have := mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) h2
    linear_combination (-1/2 : ℂ) * this
  have h3 : (θ : ℂ) = 0 := by simpa [hπ] using this
  exact h0 (by exact_mod_cast h3)


/-- Zeros of the kernel in the strip `-2 ≤ Im ξ ≤ 0`: exactly `a₊` and `a₋`. -/
theorem kerD_zero_of_mem_strip {θ : ℝ} (hθ : |θ| < π) {ξ : ℂ} (him1 : -2 ≤ ξ.im)
    (him2 : ξ.im ≤ 0) (hz : kerD θ ξ = 0) : ξ = kerPlus θ ∨ ξ = kerMinus θ := by
  have hθ' := abs_lt.mp hθ
  have hpi := Real.pi_pos
  have hcos : Complex.cos (((π * ξ) * I)) = Complex.cos (((π - θ : ℝ) : ℂ)) := by
    rw [Complex.cos_mul_I]
    push_cast
    rw [Complex.cos_pi_sub]
    unfold kerD at hz
    push_cast at hz
    linear_combination hz
  obtain ⟨k, hk⟩ := Complex.cos_eq_cos_iff.mp hcos
  have hξ : ξ = (ξ.re : ℂ) + (ξ.im : ℂ) * I := (Complex.re_add_im ξ).symm
  rcases hk with hk | hk
  · have hr := congrArg Complex.re hk
    have hi := congrArg Complex.im hk
    simp at hr hi
    have hk1 : (k : ℝ) < 1 := by
      by_contra h; have h := not_lt.mp h
      nlinarith [him1, him2, mul_nonneg hpi.le (sub_nonneg.mpr him1)]
    have hk2 : (-1 : ℝ) < k := by
      by_contra h; have h := not_lt.mp h
      nlinarith [him1, him2, mul_nonneg hpi.le (sub_nonneg.mpr him1)]
    have hk0 : k = 0 := by
      have h1 : k < 1 := by exact_mod_cast hk1
      have h2 : -1 < k := by exact_mod_cast hk2
      omega
    subst hk0
    left
    have hπ : (π : ℝ) ≠ 0 := hpi.ne'
    apply Complex.ext
    · simp [kerPlus, hi]
    · simp [kerPlus]
      field_simp
      push_cast at hr
      linarith
  · have hr := congrArg Complex.re hk
    have hi := congrArg Complex.im hk
    simp at hr hi
    have hk1 : (0 : ℝ) < k := by
      by_contra h; have h := not_lt.mp h
      nlinarith [him1, him2, mul_nonneg hpi.le (sub_nonneg.mpr him1)]
    have hk2 : (k : ℝ) < 2 := by
      by_contra h; have h := not_lt.mp h
      nlinarith [him1, him2, mul_nonneg hpi.le (sub_nonneg.mpr him1)]
    have hk0 : k = 1 := by
      have h1 : 0 < k := by exact_mod_cast hk1
      have h2 : k < 2 := by exact_mod_cast hk2
      omega
    subst hk0
    right
    have hπ : (π : ℝ) ≠ 0 := hpi.ne'
    apply Complex.ext
    · simp [kerMinus, hi]
    · simp [kerMinus]
      field_simp
      push_cast at hr
      linarith


lemma norm_cosh_ge (u : ℂ) :
    (Real.exp |u.re| - Real.exp (-|u.re|)) / 2 ≤ ‖Complex.cosh u‖ := by
  have h : Complex.cosh u = (Complex.exp u + Complex.exp (-u)) / 2 := rfl
  rw [h, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have h3 : |‖Complex.exp u‖ - ‖Complex.exp (-u)‖| ≤ ‖Complex.exp u + Complex.exp (-u)‖ := by
    have := abs_norm_sub_norm_le (Complex.exp u) (-Complex.exp (-u))
    rwa [norm_neg, sub_neg_eq_add] at this
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h3
  have h4 : Real.exp |u.re| - Real.exp (-|u.re|) = |Real.exp u.re - Real.exp (-u.re)| := by
    rcases le_total 0 u.re with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg]
      have : Real.exp (-u.re) ≤ Real.exp u.re := Real.exp_le_exp.mpr (by linarith)
      linarith
    · rw [abs_of_nonpos h, abs_of_nonpos]
      · ring_nf
      · have : Real.exp u.re ≤ Real.exp (-u.re) := Real.exp_le_exp.mpr (by linarith)
        linarith
  rw [h4]
  exact div_le_div_of_nonneg_right h3 (by norm_num)

lemma cos_gt_neg_one {θ : ℝ} (hθ : |θ| < π) : -1 < Real.cos θ := by
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ) le_rfl hθ
  rwa [Real.cos_abs, Real.cos_pi] at this

/-- Lower bound for the kernel away from the imaginary axis, in the strip. -/
theorem norm_kerD_ge (θ : ℝ) {ξ : ℂ} (hX : 1 ≤ |ξ.re|) :
    Real.exp (π * |ξ.re|) / 8 ≤ ‖kerD θ ξ‖ := by
  have h1 := norm_cosh_ge (π * ξ)
  have hre : ((π : ℂ) * ξ).re = π * ξ.re := by simp
  rw [hre, abs_mul, abs_of_pos Real.pi_pos] at h1
  have hc : ‖((Real.cos θ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one θ
  have h2 : ‖Complex.cosh (π * ξ)‖ - 1 ≤ ‖kerD θ ξ‖ := by
    unfold kerD
    have := norm_sub_norm_le (Complex.cosh (π * ξ)) (-((Real.cos θ : ℝ) : ℂ))
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  set t := Real.exp (π * |ξ.re|) with ht
  have ht4 : 4 ≤ t := by
    have h3 : 1 + π * |ξ.re| ≤ t := by
      have := Real.add_one_le_exp (π * |ξ.re|); linarith
    nlinarith [Real.pi_gt_three]
  have : Real.exp (-(π * |ξ.re|)) = t⁻¹ := by rw [ht, Real.exp_neg]
  rw [this] at h1
  have hinv : t⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) ht4
  linarith

/-- Real-axis lower bound for the kernel. -/
theorem kerD_real_ge {θ : ℝ} (hθ : |θ| < π) (x : ℝ) :
    min 1 (1 + Real.cos θ) * Real.cosh (π * x) ≤ Real.cosh (π * x) + Real.cos θ := by
  have hc := cos_gt_neg_one hθ
  have h1 : 1 ≤ Real.cosh (π * x) := Real.one_le_cosh _
  have hm1 : min 1 (1 + Real.cos θ) ≤ 1 := min_le_left _ _
  have hm2 : min 1 (1 + Real.cos θ) ≤ 1 + Real.cos θ := min_le_right _ _
  nlinarith

lemma min_one_cos_pos {θ : ℝ} (hθ : |θ| < π) : 0 < min 1 (1 + Real.cos θ) :=
  lt_min one_pos (by linarith [cos_gt_neg_one hθ])

lemma exp_abs_le_two_cosh (y : ℝ) : Real.exp |y| ≤ 2 * Real.cosh y := by
  rw [Real.cosh_eq]
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-y)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_pos y, Real.exp_neg y]

end FormalResearch.Special.Barnes
