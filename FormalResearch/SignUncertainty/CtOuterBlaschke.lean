module

public import FormalResearch.SignUncertainty.CtOuterBoundary

/-!
# The strip Blaschke factor `b_{1/2}(ζ) = tan(π/4 - πζ/2)` (`ct:outer` (1))

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:Gdef` and the end of the proof of (1).  **Proved.**

* `bHalf_oneSub`: `b(1 - ζ) = -b(ζ)`; `bHalf_conj`: `b(ζ̄) = conj b(ζ)`;
* `norm_bHalf_sq`: `‖b(ζ)‖² = (sin²a + sinh²c)/(cos²a + sinh²c)`, `a = π/4 - π Re ζ/2`, `c = -π Im ζ/2`;
  hence `‖b‖ ≤ 1` on `closedStrip` with equality on both edges (`norm_bHalf_le_one`, `norm_bHalf_edge`)
  (the paper uses the maximum principle; here `cos²a - sin²a = sin(π Re ζ) ≥ 0` is exact);
* `bHalf` is holomorphic on `strip` and continuous on `closedStrip`;
* `bHalf_I_mul`: `b(iτ) = exp(-2i arctan(tanh(πτ/2)))`.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- The strip Blaschke factor `b_{1/2}(ζ) = tan(π/4 - πζ/2)`. -/
noncomputable def bHalf (ζ : ℂ) : ℂ := Complex.tan ((π : ℂ) / 4 - π * ζ / 2)

lemma bHalf_oneSub (ζ : ℂ) : bHalf (1 - ζ) = -bHalf ζ := by
  unfold bHalf
  rw [← Complex.tan_neg]
  congr 1
  ring

lemma bHalf_conj (ζ : ℂ) : bHalf (starRingEnd ℂ ζ) = starRingEnd ℂ (bHalf ζ) := by
  unfold bHalf
  rw [← Complex.tan_conj]
  congr 1
  simp [map_div₀, map_mul, map_sub, Complex.conj_ofReal, map_ofNat]

lemma cos_eq_re_im (w : ℂ) :
    Complex.cos w = ((Real.cos w.re * Real.cosh w.im : ℝ) : ℂ) -
      ((Real.sin w.re * Real.sinh w.im : ℝ) : ℂ) * Complex.I := by
  have h := Complex.cos_add_mul_I (w.re : ℂ) (w.im : ℂ)
  rw [Complex.re_add_im] at h
  rw [h]
  push_cast
  ring

lemma norm_cos_sq (w : ℂ) : ‖Complex.cos w‖ ^ 2 = Real.cos w.re ^ 2 + Real.sinh w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, cos_eq_re_im w]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero, Complex.sub_im, Complex.mul_im]
  have h := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  nlinarith [h, h2]

/-- The argument `w = π/4 - πζ/2` of `tan` in `b_{1/2}`. -/
noncomputable def bArg (ζ : ℂ) : ℂ := (π : ℂ) / 4 - π * ζ / 2

lemma bArg_re (ζ : ℂ) : (bArg ζ).re = π / 4 - π * ζ.re / 2 := by
  simp [bArg, Complex.mul_re]

lemma bArg_im (ζ : ℂ) : (bArg ζ).im = -(π * ζ.im / 2) := by
  simp [bArg, Complex.mul_im]

lemma cos_sq_sub_sin_sq (ζ : ℂ) :
    Real.cos (bArg ζ).re ^ 2 - Real.sin (bArg ζ).re ^ 2 = Real.sin (π * ζ.re) := by
  rw [bArg_re, ← Real.cos_two_mul']
  have : 2 * (π / 4 - π * ζ.re / 2) = π / 2 - π * ζ.re := by ring
  rw [this, Real.cos_pi_div_two_sub]

lemma cos_bArg_pos {ζ : ℂ} (hζ : ζ ∈ closedStrip) : 0 < Real.cos (bArg ζ).re := by
  rw [bArg_re]
  apply Real.cos_pos_of_mem_Ioo
  have := hζ.1; have := hζ.2; have := Real.pi_pos
  constructor <;> nlinarith

lemma norm_bHalf_sq (ζ : ℂ) :
    ‖bHalf ζ‖ ^ 2 = (Real.sin (bArg ζ).re ^ 2 + Real.sinh (bArg ζ).im ^ 2) /
      (Real.cos (bArg ζ).re ^ 2 + Real.sinh (bArg ζ).im ^ 2) := by
  unfold bHalf
  rw [Complex.tan, norm_div, div_pow, norm_sin_sq, norm_cos_sq]
  rfl

lemma cos_bArg_ne_zero {ζ : ℂ} (hζ : ζ ∈ closedStrip) : Complex.cos (bArg ζ) ≠ 0 := by
  intro h
  have h1 := norm_cos_sq (bArg ζ)
  rw [h, norm_zero] at h1
  have := cos_bArg_pos hζ
  nlinarith [sq_nonneg (Real.sinh (bArg ζ).im), pow_pos this 2]

lemma norm_bHalf_le_one {ζ : ℂ} (hζ : ζ ∈ closedStrip) : ‖bHalf ζ‖ ≤ 1 := by
  have h := norm_bHalf_sq ζ
  have hc := cos_bArg_pos hζ
  have hs : 0 ≤ Real.sin (π * ζ.re) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · have := hζ.1; have := Real.pi_pos; positivity
    · have := hζ.2; nlinarith [Real.pi_pos]
  have hd := cos_sq_sub_sin_sq ζ
  have hden : 0 < Real.cos (bArg ζ).re ^ 2 + Real.sinh (bArg ζ).im ^ 2 := by positivity
  have : ‖bHalf ζ‖ ^ 2 ≤ 1 := by
    rw [h, div_le_one hden]; nlinarith
  nlinarith [norm_nonneg (bHalf ζ)]

lemma norm_bHalf_edge {ζ : ℂ} (hζ : ζ.re = 0 ∨ ζ.re = 1) : ‖bHalf ζ‖ = 1 := by
  have hcl : ζ ∈ closedStrip := by
    rcases hζ with h | h <;> simp [closedStrip, h]
  have h := norm_bHalf_sq ζ
  have hc := cos_bArg_pos hcl
  have hd := cos_sq_sub_sin_sq ζ
  have hs : Real.sin (π * ζ.re) = 0 := by
    rcases hζ with h | h <;> simp [h]
  have hden : 0 < Real.cos (bArg ζ).re ^ 2 + Real.sinh (bArg ζ).im ^ 2 := by positivity
  have : ‖bHalf ζ‖ ^ 2 = 1 := by
    rw [h, div_eq_one_iff_eq hden.ne']; nlinarith
  nlinarith [norm_nonneg (bHalf ζ)]

lemma differentiableOn_bHalf : DifferentiableOn ℂ bHalf strip := by
  intro ζ hζ
  have hcl := strip_subset_closedStrip hζ
  have hne := cos_bArg_ne_zero hcl
  have hb : DifferentiableAt ℂ (fun ζ : ℂ => (π : ℂ) / 4 - π * ζ / 2) ζ := by fun_prop
  have h1 : DifferentiableAt ℂ Complex.tan (bArg ζ) := (Complex.hasDerivAt_tan hne).differentiableAt
  exact (h1.comp ζ hb).differentiableWithinAt

lemma continuousOn_bHalf : ContinuousOn bHalf closedStrip := by
  intro ζ hζ
  have hne := cos_bArg_ne_zero hζ
  have hb : ContinuousAt (fun ζ : ℂ => (π : ℂ) / 4 - π * ζ / 2) ζ := by fun_prop
  have h1 : ContinuousAt Complex.tan (bArg ζ) := (Complex.hasDerivAt_tan hne).continuousAt
  exact (h1.comp hb).continuousWithinAt

/-- `b_{1/2}(iτ) = exp(-2i arctan(tanh(πτ/2)))`. -/
lemma bHalf_I_mul (τ : ℝ) :
    bHalf (Complex.I * τ) =
      Complex.exp (-(2 * Complex.I * ((Real.arctan (Real.tanh (π * τ / 2)) : ℝ) : ℂ))) := by
  set y : ℝ := π * τ / 2 with hy
  set X : ℝ := Real.arctan (Real.tanh y) with hX
  have hc : 0 < Real.cos X := Real.cos_arctan_pos _
  have htan : Real.tan X = Real.tanh y := Real.tan_arctan _
  have hcosh : 0 < Real.cosh y := Real.cosh_pos y
  have hsinh : Real.sinh y * Real.cos X = Real.cosh y * Real.sin X := by
    rw [Real.tan_eq_sin_div_cos, Real.tanh_eq_sinh_div_cosh] at htan
    field_simp at htan
    linarith
  have harg : (π : ℂ) / 4 - π * (Complex.I * τ) / 2 = (π / 4 : ℝ) - (y : ℂ) * Complex.I := by
    rw [hy]; push_cast; ring
  unfold bHalf
  rw [harg, Complex.tan_eq_sin_div_cos, Complex.sin_sub, Complex.cos_sub, Complex.sin_mul_I,
    Complex.cos_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos, Real.sin_pi_div_four,
    Real.cos_pi_div_four, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  have e2 : Complex.exp (Complex.I * (X : ℂ)) = (Real.cos X : ℂ) + (Real.sin X : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have e3 : Complex.exp (-(Complex.I * (X : ℂ))) = (Real.cos X : ℂ) - (Real.sin X : ℂ) * Complex.I := by
    rw [show -(Complex.I * (X : ℂ)) = ((-X : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have e1 : Complex.exp (-(2 * Complex.I * (X : ℂ))) =
      Complex.exp (-(Complex.I * (X : ℂ))) / Complex.exp (Complex.I * (X : ℂ)) := by
    rw [← Complex.exp_sub]; congr 1; ring
  rw [e1, e2, e3]
  have hre : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).re = a := fun a b => by simp
  have hcoshpos : (Real.cosh y : ℝ) ≠ 0 := hcosh.ne'
  have hden : (Real.cos X : ℂ) + (Real.sin X : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    simp only [Complex.zero_re] at this
    linarith
  have hden2 : (Real.cosh y : ℂ) + (Real.sinh y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    simp only [Complex.zero_re] at this
    linarith
  have hr : ((Real.sqrt 2 / 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
    exact_mod_cast this.ne'
  have hsC : (Real.sinh y : ℂ) * (Real.cos X : ℂ) = (Real.cosh y : ℂ) * (Real.sin X : ℂ) := by
    exact_mod_cast hsinh
  have hd1 : ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (Real.cosh y : ℂ) +
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((Real.sinh y : ℂ) * Complex.I) ≠ 0 := by
    have : ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (Real.cosh y : ℂ) +
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((Real.sinh y : ℂ) * Complex.I) =
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((Real.cosh y : ℂ) + (Real.sinh y : ℂ) * Complex.I) := by ring
    rw [this]; exact mul_ne_zero hr hden2
  rw [div_eq_div_iff hd1 hden]
  linear_combination (-2 * ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I) * hsC

end FormalResearch.SignUncertainty.CtOuter
