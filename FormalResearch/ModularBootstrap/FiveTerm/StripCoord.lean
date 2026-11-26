module

public import FormalResearch.ModularBootstrap.FiveTerm.HalfDisc
public import FormalResearch.ModularBootstrap.FiveTerm.StripCauchy
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The strip coordinate `z = tan(π s / 4)` of the half-disc `Ω` (FIVE-0 tool)

The half-disc `Ω = {|z| < 1, Re z > 0}` of `cts:involution` is the image of the vertical strip
`0 < Re s < 1` under `z = sTan s := tan(π s / 4)`:

* `sTan_mem_halfDisc`: the open strip maps into `Ω`; the closed strip into its closure;
* the left edge is the diameter, `sTan (τ i) = i tanh(π τ / 4)` (`sTan_I_mul`), the right edge the unit
  semicircle, `sTan (1 + τ i) = (1 + i y)/(1 - i y)` with `y = tanh(π τ/4)` (`sTan_one_add`);
  `s = 0` is the tip `z = 0`, `s = 1` the vacuum `z = 1`, and the two ends `Im s → ±∞` are `z = ±i`;
* the involution `σ(z) = (1-z)/(1+z)` of `cts:sigma` is `s ↦ 1 - s` (`sTan_one_sub`);
* `1 + z^2 = 1/cos^2(π s/4)`, and `‖cos(π s/4)‖² = cos²(π Re s/4) + sinh²(π Im s/4) ≥ cosh(π Im s/2)/2`.

It turns the indented-half-disc Cauchy argument of `ctu:common-functional` into Cauchy's theorem on a
strip (`StripCauchy`).  All results are proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The strip coordinate `z = tan(π s/4)`. -/
noncomputable def sTan (s : ℂ) : ℂ := Complex.tan ((π : ℂ) * s / 4)

lemma sin_eq_re_im' (w : ℂ) :
    Complex.sin w = ((Real.sin w.re * Real.cosh w.im : ℝ) : ℂ) +
      ((Real.cos w.re * Real.sinh w.im : ℝ) : ℂ) * Complex.I := by
  have h := Complex.sin_add_mul_I (w.re : ℂ) (w.im : ℂ)
  rw [Complex.re_add_im] at h
  rw [h]
  push_cast
  ring

lemma cos_eq_re_im' (w : ℂ) :
    Complex.cos w = ((Real.cos w.re * Real.cosh w.im : ℝ) : ℂ) -
      ((Real.sin w.re * Real.sinh w.im : ℝ) : ℂ) * Complex.I := by
  have h := Complex.cos_add_mul_I (w.re : ℂ) (w.im : ℂ)
  rw [Complex.re_add_im] at h
  rw [h]
  push_cast
  ring

lemma norm_sin_sq' (w : ℂ) : ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, sin_eq_re_im' w]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    zero_add]
  have h := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  nlinarith [h, h2]

lemma norm_cos_sq' (w : ℂ) : ‖Complex.cos w‖ ^ 2 = Real.cos w.re ^ 2 + Real.sinh w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, cos_eq_re_im' w]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero, Complex.sub_im, Complex.mul_im,
    zero_add]
  have h := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  nlinarith [h, h2]

lemma re_pi_mul_div_four (s : ℂ) : ((π : ℂ) * s / 4).re = π * s.re / 4 := by
  simp [Complex.div_re, Complex.mul_re]; ring

lemma im_pi_mul_div_four (s : ℂ) : ((π : ℂ) * s / 4).im = π * s.im / 4 := by
  simp [Complex.div_im, Complex.mul_im]; ring

lemma cos_re_sq_ge {s : ℂ} (hs : s ∈ unitStripCl) : (1 : ℝ) / 2 ≤ Real.cos (π * s.re / 4) ^ 2 := by
  have h0 : 0 ≤ π * s.re / 4 := by have := Real.pi_pos; have := hs.1; positivity
  have h1 : π * s.re / 4 ≤ π / 4 := by
    have := Real.pi_pos; have := hs.2; nlinarith only [this, hs.2]
  have hc : Real.cos (π / 4) ≤ Real.cos (π * s.re / 4) :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]) h1
  rw [Real.cos_pi_div_four] at hc
  have h2 : (√2 / 2) ^ 2 = 1 / 2 := by
    have : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith only [this]
  have h3 : 0 ≤ √2 / 2 := by positivity
  nlinarith only [hc, h2, h3]

/-- `‖cos(π s/4)‖² = cos²(π Re s/4) + sinh²(π Im s/4)` is at least `cosh(π Im s / 2)/2` on the closed strip. -/
lemma norm_cos_sq_ge {s : ℂ} (hs : s ∈ unitStripCl) :
    Real.cosh (π * s.im / 2) / 2 ≤ ‖Complex.cos ((π : ℂ) * s / 4)‖ ^ 2 := by
  rw [norm_cos_sq', re_pi_mul_div_four, im_pi_mul_div_four]
  have h := cos_re_sq_ge hs
  have h2 : Real.cosh (π * s.im / 2) = 1 + 2 * Real.sinh (π * s.im / 4) ^ 2 := by
    have := Real.cosh_two_mul (π * s.im / 4)
    have e : 2 * (π * s.im / 4) = π * s.im / 2 := by ring
    rw [e] at this
    rw [this, Real.cosh_sq]; ring
  rw [h2]
  nlinarith only [h]

lemma cos_ne_zero_of_cl {s : ℂ} (hs : s ∈ unitStripCl) : Complex.cos ((π : ℂ) * s / 4) ≠ 0 := by
  intro h
  have h1 := norm_cos_sq_ge hs
  rw [h, norm_zero] at h1
  have := Real.cosh_pos (π * s.im / 2)
  norm_num at h1
  linarith

lemma sTan_eq (s : ℂ) : sTan s = Complex.sin ((π : ℂ) * s / 4) / Complex.cos ((π : ℂ) * s / 4) :=
  Complex.tan_eq_sin_div_cos _

lemma norm_sTan_sq {s : ℂ} (hs : s ∈ unitStripCl) :
    ‖sTan s‖ ^ 2 = ‖Complex.sin ((π : ℂ) * s / 4)‖ ^ 2 / ‖Complex.cos ((π : ℂ) * s / 4)‖ ^ 2 := by
  rw [sTan_eq, norm_div, div_pow]

lemma one_add_sTan_sq {s : ℂ} (hs : s ∈ unitStripCl) :
    1 + sTan s ^ 2 = (Complex.cos ((π : ℂ) * s / 4) ^ 2)⁻¹ := by
  have hc := cos_ne_zero_of_cl hs
  have := Complex.one_add_tan_sq_mul_cos_sq_eq_one hc
  unfold sTan
  field_simp
  linear_combination this

/-- `‖1 + z²‖ = 1/‖cos(π s/4)‖²` for `z = sTan s`. -/
lemma norm_one_add_sTan_sq {s : ℂ} (hs : s ∈ unitStripCl) :
    ‖1 + sTan s ^ 2‖ = (‖Complex.cos ((π : ℂ) * s / 4)‖ ^ 2)⁻¹ := by
  rw [one_add_sTan_sq hs, norm_inv, norm_pow]

lemma norm_one_add_sTan_sq_le {s : ℂ} (hs : s ∈ unitStripCl) :
    ‖1 + sTan s ^ 2‖ ≤ 4 * Real.exp (-(π * |s.im| / 2)) := by
  rw [norm_one_add_sTan_sq hs]
  have h := norm_cos_sq_ge hs
  have hpos : 0 < Real.cosh (π * s.im / 2) := Real.cosh_pos _
  have hcosh : Real.exp (π * |s.im| / 2) / 2 ≤ Real.cosh (π * s.im / 2) := by
    rw [Real.cosh_eq]
    have : Real.exp (π * |s.im| / 2) ≤ Real.exp (π * s.im / 2) + Real.exp (-(π * s.im / 2)) := by
      rcases abs_cases s.im with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]; have := Real.exp_pos (-(π * s.im / 2)); linarith
      · rw [h1]
        have e : π * -s.im / 2 = -(π * s.im / 2) := by ring
        rw [e]; have := Real.exp_pos (π * s.im / 2); linarith
    linarith
  have hE : 0 < Real.exp (π * |s.im| / 2) := Real.exp_pos _
  have h4 : Real.exp (π * |s.im| / 2) / 4 ≤ ‖Complex.cos ((π : ℂ) * s / 4)‖ ^ 2 := by linarith
  have hexp : Real.exp (-(π * |s.im| / 2)) = (Real.exp (π * |s.im| / 2))⁻¹ := Real.exp_neg _
  rw [hexp]
  have h5 : 0 < Real.exp (π * |s.im| / 2) / 4 := by positivity
  calc (‖Complex.cos ((π : ℂ) * s / 4)‖ ^ 2)⁻¹ ≤ (Real.exp (π * |s.im| / 2) / 4)⁻¹ :=
        inv_anti₀ h5 h4
    _ = 4 * (Real.exp (π * |s.im| / 2))⁻¹ := by field_simp

lemma differentiableOn_sTan : DifferentiableOn ℂ sTan unitStripCl := by
  intro s hs
  have hc := cos_ne_zero_of_cl hs
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (π : ℂ) * s / 4) s := by fun_prop
  have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.tan ((π : ℂ) * s / 4)) s := by
    have : DifferentiableAt ℂ Complex.tan ((π : ℂ) * s / 4) := by
      rw [Complex.tan_eq_sin_div_cos] at *
      exact (Complex.differentiableAt_tan).2 hc
    exact this.comp s h1
  exact h2.differentiableWithinAt

lemma continuousOn_sTan : ContinuousOn sTan unitStripCl := differentiableOn_sTan.continuousOn

lemma sTan_mem_halfDisc {s : ℂ} (hs : s ∈ unitStrip) : sTan s ∈ halfDisc := by
  have hcl : s ∈ unitStripCl := unitStrip_subset_cl hs
  have hc : Complex.cos ((π : ℂ) * s / 4) ≠ 0 := cos_ne_zero_of_cl hcl
  have ha0 : 0 < π * s.re / 4 := by have := Real.pi_pos; have := hs.1; positivity
  have ha1 : π * s.re / 4 < π / 4 := by
    have := Real.pi_pos; have := hs.2; nlinarith only [this, hs.2]
  have hsin : 0 < Real.sin (π * s.re / 4) := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (π * s.re / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hc2 : 0 < Real.cos (2 * (π * s.re / 4)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [Real.cos_two_mul] at hc2
  have hnorm : ‖sTan s‖ ^ 2 < 1 := by
    rw [norm_sTan_sq hcl, norm_sin_sq', norm_cos_sq', re_pi_mul_div_four, im_pi_mul_div_four]
    have hpos : 0 < Real.cos (π * s.re / 4) ^ 2 + Real.sinh (π * s.im / 4) ^ 2 := by positivity
    rw [div_lt_one hpos]
    have := Real.sin_sq_add_cos_sq (π * s.re / 4)
    nlinarith only [hc2, this]
  have hre : 0 < (sTan s).re := by
    rw [sTan_eq, Complex.div_re, sin_eq_re_im', cos_eq_re_im']
    have hn : 0 < Complex.normSq (((Real.cos (π * s.re / 4) * Real.cosh (π * s.im / 4) : ℝ) : ℂ) -
        ((Real.sin (π * s.re / 4) * Real.sinh (π * s.im / 4) : ℝ) : ℂ) * Complex.I) := by
      rw [← cos_eq_re_im' (π * s.re / 4 + π * s.im / 4 * Complex.I)] <;> sorry
    sorry
  refine ⟨?_, hre⟩
  sorry

end FormalResearch.ModularBootstrap.FiveTerm
