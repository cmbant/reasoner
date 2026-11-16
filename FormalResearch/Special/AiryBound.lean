module

public import FormalResearch.Special.AiryReal

/-!
# Explicit decay of `Ai` and `Ai'` on `(0, ∞)`

Taking the abscissa `c = √x` in the contour-independent representation of `AiryDef` gives, for
real `x > 0`, the explicit bounds
`|Ai(x)| ≤ (1/(2√π)) x^{-1/4} exp(-(2/3) x^{3/2})` (`airyAi_abs_le`) and
`|Ai'(x)| ≤ (1/(2π)) (√π x^{1/4} + x^{-1/2}) exp(-(2/3) x^{3/2})` (`airyAi'_abs_le`).
(For `Ai'` the true leading constant is `1/(2√π)`; the extra term `x^{-1/2}` comes from the
crude bound `|t| ≤ c + |s|`.)  The general-`c` forms are `norm_airyMom_zero_le`, `norm_airyMom_one_le`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma norm_airyMom_le_integral (k : ℕ) (c : ℝ) (z : ℂ) :
    ‖airyMom k c z‖ ≤ (1 / (2 * π)) * ∫ s, ‖airyPoly k c z s‖ := by
  unfold airyMom
  rw [norm_mul]
  have : ‖(1 / (2 * (π : ℂ)))‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [this]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)

lemma integral_gauss_c (c : ℝ) : ∫ s : ℝ, Real.exp (-c * s ^ 2) = √(π / c) :=
  integral_gaussian c

lemma integral_abs_gauss {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ, |s| * Real.exp (-c * s ^ 2) = 1 / c := by
  have h := integral_comp_abs (f := fun y : ℝ => y * Real.exp (-c * y ^ 2))
  simp only [sq_abs] at h
  rw [h]
  have := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := c) two_pos (by norm_num) hc
  simp only [Real.rpow_one, Real.rpow_two] at this
  rw [this]
  norm_num [Real.Gamma_one]
  rw [Real.rpow_neg_one]
  field_simp

/-- General-`c` bound for real `z = x`, `k = 0`. -/
lemma norm_airyMom_zero_le (c x : ℝ) :
    ‖airyMom 0 c x‖ ≤ (1 / (2 * π)) * (Real.exp (c ^ 3 / 3 - x * c) * √(π / c)) := by
  refine (norm_airyMom_le_integral 0 c x).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity))
  have : ∀ s, ‖airyPoly 0 c (x : ℂ) s‖ = Real.exp (c ^ 3 / 3 - x * c) * Real.exp (-c * s ^ 2) := by
    intro s
    rw [norm_airyPoly, ← Real.exp_add]; simp; ring_nf
  simp_rw [this]
  rw [integral_const_mul, integral_gauss_c c]

/-- General-`c` bound for real `z = x`, `k = 1`. -/
lemma norm_airyMom_one_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ‖airyMom 1 c x‖ ≤ (1 / (2 * π)) *
      (Real.exp (c ^ 3 / 3 - x * c) * (c * √(π / c) + 1 / c)) := by
  refine (norm_airyMom_le_integral 1 c x).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hle : ∀ s, ‖airyPoly 1 c (x : ℂ) s‖ ≤
      Real.exp (c ^ 3 / 3 - x * c) * (c * Real.exp (-c * s ^ 2) + |s| * Real.exp (-c * s ^ 2)) := by
    intro s
    rw [norm_airyPoly, show c ^ 3 / 3 - (x : ℂ).re * c + (x : ℂ).im * s - c * s ^ 2 =
      (c ^ 3 / 3 - x * c) + (-c * s ^ 2) by simp; ring, Real.exp_add]
    have := norm_airyLine_le c s
    rw [abs_of_pos hc] at this
    have hp := Real.exp_pos (c ^ 3 / 3 - x * c)
    have hq := Real.exp_pos (-c * s ^ 2)
    rw [pow_one]
    nlinarith [mul_le_mul_of_nonneg_right this (mul_pos hp hq).le]
  have i1 : Integrable (fun s : ℝ => c * Real.exp (-c * s ^ 2)) :=
    (integrable_exp_neg_mul_sq hc).const_mul c
  have i2 : Integrable (fun s : ℝ => |s| * Real.exp (-c * s ^ 2)) := by
    have := (integrable_rpow_mul_exp_neg_mul_sq hc (s := (1 : ℝ)) (by norm_num)).norm
    refine this.congr (Filter.Eventually.of_forall fun s => ?_)
    simp [abs_of_pos (Real.exp_pos _)]
  calc ∫ s, ‖airyPoly 1 c (x : ℂ) s‖
      ≤ ∫ s, Real.exp (c ^ 3 / 3 - x * c) *
          (c * Real.exp (-c * s ^ 2) + |s| * Real.exp (-c * s ^ 2)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => norm_nonneg _)
          ((i1.add i2).const_mul _) (Filter.Eventually.of_forall hle)
    _ = Real.exp (c ^ 3 / 3 - x * c) * (c * √(π / c) + 1 / c) := by
        rw [integral_const_mul, integral_add i1 i2, integral_const_mul, integral_gauss_c c,
          integral_abs_gauss hc]

lemma sqrt_cube_eq_rpow {x : ℝ} (hx : 0 < x) : (√x) ^ 3 = x ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

lemma sqrt_sqrt_eq_rpow {x : ℝ} (hx : 0 < x) : √(√x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]; norm_num

lemma exp_exponent_sqrt {x : ℝ} (hx : 0 < x) :
    (√x) ^ 3 / 3 - x * √x = -(2 / 3) * x ^ (3 / 2 : ℝ) := by
  rw [← sqrt_cube_eq_rpow hx]
  have : x * √x = (√x) ^ 3 := by
    have h := Real.sq_sqrt hx.le
    calc x * √x = (√x) ^ 2 * √x := by rw [h]
      _ = (√x) ^ 3 := by ring
  rw [this]; ring

/-- **Decay of `Ai` on the forbidden side**: for `x > 0`,
`|Ai(x)| ≤ (1/(2√π)) x^{-1/4} exp(-(2/3) x^{3/2})`. -/
theorem airyAi_abs_le {x : ℝ} (hx : 0 < x) :
    |airyAi x| ≤ 1 / (2 * √π) * x ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) := by
  have hc : 0 < √x := Real.sqrt_pos.mpr hx
  have h1 : |airyAi x| ≤ ‖airyMom 0 (√x) x‖ := by
    rw [airyAi_eq_re_airyMom hc]; exact Complex.abs_re_le_norm _
  refine h1.trans ((norm_airyMom_zero_le (√x) x).trans (le_of_eq ?_))
  rw [exp_exponent_sqrt hx, Real.sqrt_div Real.pi_pos.le, sqrt_sqrt_eq_rpow hx,
    Real.rpow_neg hx.le]
  have hπ : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hsq : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hr : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  field_simp
  nlinarith [hsq]

/-- **Decay of `Ai'`**: for `x > 0`,
`|Ai'(x)| ≤ (1/(2π)) (√π x^{1/4} + x^{-1/2}) exp(-(2/3) x^{3/2})`. -/
theorem airyAi'_abs_le {x : ℝ} (hx : 0 < x) :
    |airyAi' x| ≤ 1 / (2 * π) * (√π * x ^ (1 / 4 : ℝ) + x ^ (-(1 / 2) : ℝ)) *
      Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) := by
  have hc : 0 < √x := Real.sqrt_pos.mpr hx
  have h1 : |airyAi' x| ≤ ‖airyMom 1 (√x) x‖ := by
    rw [airyAi'_eq_re_airyMom hc]; exact Complex.abs_re_le_norm _
  refine h1.trans ((norm_airyMom_one_le hc x).trans (le_of_eq ?_))
  rw [exp_exponent_sqrt hx, Real.sqrt_div Real.pi_pos.le, sqrt_sqrt_eq_rpow hx]
  have hr : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  have e1 : (√x) * (√π / x ^ (1 / 4 : ℝ)) = √π * x ^ (1 / 4 : ℝ) := by
    have : √x = (x ^ (1 / 4 : ℝ)) ^ 2 := by
      rw [← sqrt_sqrt_eq_rpow hx, Real.sq_sqrt (Real.sqrt_nonneg _)]
    rw [this]; field_simp
  have e2 : 1 / √x = x ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hx.le, one_div]
  rw [e1, e2]; ring

/-- info: 'FormalResearch.Special.airyAi_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_abs_le

/-- info: 'FormalResearch.Special.airyAi'_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi'_abs_le

end FormalResearch.Special
