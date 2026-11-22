/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Elementary exponential bounds for trigonometric and hyperbolic functions

Growth bounds for the complex sine and cosine, and elementary real inequalities for the
exponential, the hyperbolic cosine and the cosine.

## Main results

* `Complex.norm_sin_le_exp_abs_im`, `Complex.norm_cos_le_exp_abs_im`:
  `‖sin z‖, ‖cos z‖ ≤ e^{|Im z|}`.
* `Complex.sinh_abs_im_le_norm_sin`: the complementary imaginary-direction lower bound.
* `Real.cosh_le_exp_abs`: `cosh t ≤ e^{|t|}`.
* `Complex.norm_cosh_le_cosh_re`: the real hyperbolic cosine bounds its complex modulus.
* `Real.exp_sub_one_le_mul_exp`: `eʸ - 1 ≤ y eʸ` for every real `y`.
* `Real.cos_pos_of_abs_lt_pi_div_two` and its partial converse
  `Real.abs_lt_pi_div_two_of_cos_pos` on `(-3π/2, 3π/2)`.
-/

@[expose] public section
open scoped Real

namespace Complex

/-- `‖e^{-iz}‖ ≤ e^{|Im z|}`. -/
private lemma norm_exp_neg_mul_I_le (z : ℂ) : ‖exp (-z * I)‖ ≤ Real.exp |z.im| := by
  rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [le_abs_self])

/-- `‖e^{iz}‖ ≤ e^{|Im z|}`. -/
private lemma norm_exp_mul_I_le (z : ℂ) : ‖exp (z * I)‖ ≤ Real.exp |z.im| := by
  rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [neg_le_abs])

/-- The complex sine grows at most like `e^{|Im z|}`: `‖sin z‖ ≤ e^{|Im z|}`. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖sin z‖ ≤ Real.exp |z.im| := by
  rw [sin, norm_div, norm_mul, norm_I, mul_one, Complex.norm_two]
  linarith [norm_sub_le (exp (-z * I)) (exp (z * I)), norm_exp_neg_mul_I_le z,
    norm_exp_mul_I_le z]

/-- The hyperbolic sine of the imaginary magnitude bounds the complex sine from below. -/
theorem sinh_abs_im_le_norm_sin (z : ℂ) : Real.sinh |z.im| ≤ ‖sin z‖ := by
  have h (w : ℂ) : Real.sinh w.im ≤ ‖sin w‖ := by
    rw [sin, norm_div, norm_mul, norm_I, mul_one, Complex.norm_two, Real.sinh_eq]
    have hb := norm_sub_norm_le (exp (-w * I)) (exp (w * I))
    simp only [norm_exp, mul_I_re, neg_im, neg_neg] at hb
    linarith
  by_cases hz : 0 ≤ z.im
  · simpa only [abs_of_nonneg hz] using h z
  · simpa only [neg_im, sin_neg, norm_neg, abs_of_neg (lt_of_not_ge hz)] using h (-z)

/-- The complex cosine grows at most like `e^{|Im z|}`: `‖cos z‖ ≤ e^{|Im z|}`. -/
theorem norm_cos_le_exp_abs_im (z : ℂ) : ‖cos z‖ ≤ Real.exp |z.im| := by
  rw [cos, norm_div, Complex.norm_two]
  linarith [norm_add_le (exp (z * I)) (exp (-z * I)), norm_exp_neg_mul_I_le z,
    norm_exp_mul_I_le z]

/-- The hyperbolic cosine of the real part bounds the complex hyperbolic cosine. -/
theorem norm_cosh_le_cosh_re (z : ℂ) : ‖cosh z‖ ≤ Real.cosh z.re := by
  have h := norm_add_le (exp z) (exp (-z))
  simp only [norm_exp, neg_re] at h
  simpa only [cosh, norm_div, Complex.norm_two, Real.cosh_eq] using
    div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)

end Complex

namespace Real

/-- The hyperbolic cosine is bounded by `e^{|t|}`. -/
theorem cosh_le_exp_abs (t : ℝ) : cosh t ≤ exp |t| := by
  rw [cosh_eq]
  linarith [exp_le_exp.mpr (le_abs_self t), exp_le_exp.mpr (neg_le_abs t)]

/-- `eʸ - 1 ≤ y eʸ` for every real `y` (convexity of the exponential at `y`). -/
theorem exp_sub_one_le_mul_exp (y : ℝ) : exp y - 1 ≤ y * exp y := by
  have h := add_one_le_exp (-y)
  have h2 : exp (-y) * exp y = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos y]

/-- The cosine is positive on the open interval `|φ| < π/2`. -/
theorem cos_pos_of_abs_lt_pi_div_two {φ : ℝ} (hφ : |φ| < π / 2) : 0 < cos φ :=
  cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩

/-- On `(-3π/2, 3π/2)` the cosine is positive only on `(-π/2, π/2)`. -/
theorem abs_lt_pi_div_two_of_cos_pos {u : ℝ} (h1 : -(3 * π / 2) < u) (h2 : u < 3 * π / 2)
    (hc : 0 < cos u) : |u| < π / 2 := by
  rw [abs_lt]
  constructor
  · by_contra h
    push Not at h
    have := cos_nonpos_of_pi_div_two_le_of_le (x := -u) (by linarith) (by linarith)
    rw [cos_neg] at this; linarith
  · by_contra h
    push Not at h
    have := cos_nonpos_of_pi_div_two_le_of_le (x := u) h (by linarith)
    linarith

end Real
