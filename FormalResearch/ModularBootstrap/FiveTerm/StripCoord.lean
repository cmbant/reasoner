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

lemma sin_re' (w : ℂ) : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im := by
  rw [sin_eq_re_im' w]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]

lemma sin_im' (w : ℂ) : (Complex.sin w).im = Real.cos w.re * Real.sinh w.im := by
  rw [sin_eq_re_im' w]
  simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, zero_add, add_zero]

lemma cos_re' (w : ℂ) : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := by
  rw [cos_eq_re_im' w]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero]

lemma cos_im' (w : ℂ) : (Complex.cos w).im = -(Real.sin w.re * Real.sinh w.im) := by
  rw [cos_eq_re_im' w]
  simp only [Complex.sub_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, add_zero, zero_sub]

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
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero, Complex.sub_im, Complex.mul_im]
  have h := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  nlinarith [h, h2]

lemma re_pi_mul_div_four (s : ℂ) : ((π : ℂ) * s / 4).re = π * s.re / 4 := by
  simp

lemma im_pi_mul_div_four (s : ℂ) : ((π : ℂ) * s / 4).im = π * s.im / 4 := by
  simp

lemma cos_re_sq_ge {s : ℂ} (hs : s ∈ unitStripCl) : (1 : ℝ) / 2 ≤ Real.cos (π * s.re / 4) ^ 2 := by
  have h0 : 0 ≤ π * s.re / 4 := by have := Real.pi_pos; have := hs.1; positivity
  have h1 : π * s.re / 4 ≤ π / 4 := by
    nlinarith only [mul_nonneg Real.pi_pos.le (sub_nonneg.2 hs.2)]
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

lemma norm_sTan_sq (s : ℂ) :
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
    have : DifferentiableAt ℂ Complex.tan ((π : ℂ) * s / 4) := Complex.differentiableAt_tan.2 hc
    exact this.comp s h1
  exact h2.differentiableWithinAt

lemma continuousOn_sTan : ContinuousOn sTan unitStripCl := differentiableOn_sTan.continuousOn

lemma sTan_mem_halfDisc {s : ℂ} (hs : s ∈ unitStrip) : sTan s ∈ halfDisc := by
  have hcl : s ∈ unitStripCl := unitStrip_subset_cl hs
  have hc : Complex.cos ((π : ℂ) * s / 4) ≠ 0 := cos_ne_zero_of_cl hcl
  have ha0 : 0 < π * s.re / 4 := by have := Real.pi_pos; have := hs.1; positivity
  have ha1 : π * s.re / 4 < π / 4 := by
    nlinarith only [mul_pos Real.pi_pos (sub_pos.2 hs.2)]
  have hsin : 0 < Real.sin (π * s.re / 4) := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (π * s.re / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hc2 : 0 < Real.cos (2 * (π * s.re / 4)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [Real.cos_two_mul] at hc2
  have hnorm : ‖sTan s‖ ^ 2 < 1 := by
    rw [norm_sTan_sq, norm_sin_sq', norm_cos_sq', re_pi_mul_div_four, im_pi_mul_div_four]
    have hpos : 0 < Real.cos (π * s.re / 4) ^ 2 + Real.sinh (π * s.im / 4) ^ 2 := by positivity
    rw [div_lt_one hpos]
    have := Real.sin_sq_add_cos_sq (π * s.re / 4)
    nlinarith only [hc2, this]
  have hre : 0 < (sTan s).re := by
    set a := π * s.re / 4 with ha
    set b := π * s.im / 4 with hb
    have hw : ((π : ℂ) * s / 4).re = a := re_pi_mul_div_four s
    have hw' : ((π : ℂ) * s / 4).im = b := im_pi_mul_div_four s
    have e1 : (Complex.sin ((π : ℂ) * s / 4)).re = Real.sin a * Real.cosh b := by
      rw [sin_re', hw, hw']
    have e2 : (Complex.sin ((π : ℂ) * s / 4)).im = Real.cos a * Real.sinh b := by
      rw [sin_im', hw, hw']
    have e3 : (Complex.cos ((π : ℂ) * s / 4)).re = Real.cos a * Real.cosh b := by
      rw [cos_re', hw, hw']
    have e4 : (Complex.cos ((π : ℂ) * s / 4)).im = -(Real.sin a * Real.sinh b) := by
      rw [cos_im', hw, hw']
    rw [sTan_eq, Complex.div_re, e1, e2, e3, e4, ← add_div]
    refine div_pos ?_ (Complex.normSq_pos.2 hc)
    have h := Real.cosh_sq b
    have : Real.sin a * Real.cosh b * (Real.cos a * Real.cosh b) +
        Real.cos a * Real.sinh b * -(Real.sin a * Real.sinh b) = Real.sin a * Real.cos a := by
      linear_combination (Real.sin a * Real.cos a) * h
    rw [this]; positivity
  refine ⟨?_, hre⟩
  have h0 : 0 ≤ ‖sTan s‖ := norm_nonneg _
  nlinarith only [hnorm, h0]

lemma sTan_zero : sTan 0 = 0 := by simp [sTan]

lemma sTan_one : sTan 1 = 1 := by
  unfold sTan
  have : (π : ℂ) * 1 / 4 = (π / 4 : ℝ) := by push_cast; ring
  rw [this, ← Complex.ofReal_tan, Real.tan_pi_div_four]; simp

lemma sTan_I_mul (τ : ℝ) : sTan ((τ : ℂ) * Complex.I) = Complex.I * (Real.tanh (π * τ / 4) : ℂ) := by
  unfold sTan
  have : (π : ℂ) * ((τ : ℂ) * Complex.I) / 4 = ((π * τ / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.tan_mul_I, ← Complex.ofReal_tanh]; ring

lemma sTan_one_add (τ : ℝ) :
    sTan (1 + (τ : ℂ) * Complex.I) =
      (1 + Complex.I * (Real.tanh (π * τ / 4) : ℂ)) / (1 - Complex.I * (Real.tanh (π * τ / 4) : ℂ)) := by
  unfold sTan
  set u : ℂ := ((π * τ / 4 : ℝ) : ℂ) * Complex.I with hu
  have h1 : (π : ℂ) * (1 + (τ : ℂ) * Complex.I) / 4 = ((π / 4 : ℝ) : ℂ) + u := by
    rw [hu]; push_cast; ring
  set C : ℂ := (Real.cosh (π * τ / 4) : ℂ) with hC
  set S : ℂ := (Real.sinh (π * τ / 4) : ℂ) with hS
  have hcu : Complex.cos u = C := by
    rw [hu, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  have hsu : Complex.sin u = S * Complex.I := by
    rw [hu, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have hCne : C ≠ 0 := by
    rw [hC]; exact_mod_cast (Real.cosh_pos _).ne'
  have hs2 : Complex.sin ((π / 4 : ℝ) : ℂ) = Complex.cos ((π / 4 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hc2 : Complex.cos ((π / 4 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos, Real.cos_pi_div_four]; push_cast; simp
  have hden : C - S * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hC, hS] at this
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero, Complex.zero_re] at this
    exact (Real.cosh_pos _).ne' this
  have hnum : Complex.sin (((π / 4 : ℝ) : ℂ) + u) =
      Complex.cos ((π / 4 : ℝ) : ℂ) * (C + S * Complex.I) := by
    rw [Complex.sin_add, hs2, hcu, hsu]; ring
  have hdenom : Complex.cos (((π / 4 : ℝ) : ℂ) + u) =
      Complex.cos ((π / 4 : ℝ) : ℂ) * (C - S * Complex.I) := by
    rw [Complex.cos_add, hcu, hsu, hs2]; ring
  have htanh : ((Real.tanh (π * τ / 4) : ℝ) : ℂ) = S / C := by
    rw [Real.tanh_eq_sinh_div_cosh, Complex.ofReal_div]
  rw [h1, Complex.tan_eq_sin_div_cos, hnum, hdenom, mul_div_mul_left _ _ hc2, htanh]
  have hd2 : 1 - Complex.I * (S / C) ≠ 0 := by
    intro h
    apply hden
    have : C - S * Complex.I = C * (1 - Complex.I * (S / C)) := by field_simp
    rw [this, h, mul_zero]
  field_simp

/-- The involution `σ(z) = (1-z)/(1+z)` of `cts:sigma` is `s ↦ 1 - s` in the strip coordinate. -/
lemma sTan_one_sub {s : ℂ} (hs : s ∈ unitStrip) : sTan (1 - s) = sigmaHD (sTan s) := by
  have hcl : s ∈ unitStripCl := unitStrip_subset_cl hs
  have hc : Complex.cos ((π : ℂ) * s / 4) ≠ 0 := cos_ne_zero_of_cl hcl
  have hz := sTan_mem_halfDisc hs
  have h1z : 1 + sTan s ≠ 0 := one_add_ne_zero hz.2
  set w : ℂ := (π : ℂ) * s / 4 with hw
  have hπ : (π : ℂ) * (1 - s) / 4 = ((π / 4 : ℝ) : ℂ) - w := by rw [hw]; push_cast; ring
  have hs2 : Complex.sin ((π / 4 : ℝ) : ℂ) = Complex.cos ((π / 4 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hc2 : Complex.cos ((π / 4 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos, Real.cos_pi_div_four]; push_cast; simp
  have hnum : Complex.sin (((π / 4 : ℝ) : ℂ) - w) =
      Complex.cos ((π / 4 : ℝ) : ℂ) * (Complex.cos w - Complex.sin w) := by
    rw [Complex.sin_sub, hs2]; ring
  have hdenom : Complex.cos (((π / 4 : ℝ) : ℂ) - w) =
      Complex.cos ((π / 4 : ℝ) : ℂ) * (Complex.cos w + Complex.sin w) := by
    rw [Complex.cos_sub, hs2]; ring
  have hsum : Complex.cos w + Complex.sin w ≠ 0 := by
    intro h
    apply h1z
    rw [sTan_eq]
    have : 1 + Complex.sin w / Complex.cos w = (Complex.cos w + Complex.sin w) / Complex.cos w := by
      field_simp
    rw [← hw, this, h, zero_div]
  show Complex.tan ((π : ℂ) * (1 - s) / 4) = _
  rw [hπ, Complex.tan_eq_sin_div_cos, hnum, hdenom, mul_div_mul_left _ _ hc2]
  unfold sigmaHD
  rw [sTan_eq, ← hw]
  field_simp

lemma sTan_eq_zero_iff {s : ℂ} (hs : s ∈ unitStripCl) : sTan s = 0 ↔ s = 0 := by
  constructor
  · intro h
    have hc := cos_ne_zero_of_cl hs
    rw [sTan_eq, div_eq_zero_iff] at h
    rcases h with h | h
    · obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
      have h4 : s = 4 * k := by
        have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
        field_simp at hk
        linear_combination hk
      have hre : s.re = 4 * (k : ℝ) := by rw [h4]; simp
      have hk0 : k = 0 := by
        have h1 : (0 : ℝ) ≤ 4 * k := by rw [← hre]; exact hs.1
        have h2 : 4 * (k : ℝ) ≤ 1 := by rw [← hre]; exact hs.2
        have h3 : (0 : ℤ) ≤ k := by exact_mod_cast (by linarith : (0 : ℝ) ≤ k)
        have h5 : k ≤ 0 := by
          by_contra hh; push Not at hh
          have : (1 : ℝ) ≤ k := by exact_mod_cast hh
          linarith
        omega
      rw [h4, hk0]; simp
    · exact absurd h hc
  · rintro rfl; exact sTan_zero

lemma sTan_eq_one_iff {s : ℂ} (hs : s ∈ unitStripCl) : sTan s = 1 ↔ s = 1 := by
  constructor
  · intro h
    have hc := cos_ne_zero_of_cl hs
    rw [sTan_eq, div_eq_one_iff_eq hc] at h
    set w : ℂ := (π : ℂ) * s / 4 with hw
    have hs2 : Complex.sin ((π / 4 : ℝ) : ℂ) = Complex.cos ((π / 4 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hc2 : Complex.cos ((π / 4 : ℝ) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_cos, Real.cos_pi_div_four]; push_cast; simp
    have hz : Complex.sin (w - ((π / 4 : ℝ) : ℂ)) = 0 := by
      rw [Complex.sin_sub, hs2, h]; ring
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hz
    have h4 : s = 1 + 4 * k := by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      rw [hw] at hk
      push_cast at hk
      field_simp at hk
      linear_combination hk
    have hre : s.re = 1 + 4 * (k : ℝ) := by rw [h4]; simp
    have hk0 : k = 0 := by
      have h1 : (0 : ℝ) ≤ 1 + 4 * k := by rw [← hre]; exact hs.1
      have h2 : 1 + 4 * (k : ℝ) ≤ 1 := by rw [← hre]; exact hs.2
      have h3 : (0 : ℤ) ≤ k := by
        by_contra hh; push Not at hh
        have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
        linarith
      have h5 : k ≤ 0 := by
        by_contra hh; push Not at hh
        have : (1 : ℝ) ≤ k := by exact_mod_cast hh
        linarith
      omega
    rw [h4, hk0]; simp
  · rintro rfl; exact sTan_one

lemma sTan_ne_I (s : ℂ) (hs : s ∈ unitStripCl) : sTan s ≠ Complex.I := by
  intro h
  have hc := cos_ne_zero_of_cl hs
  rw [sTan_eq, div_eq_iff hc] at h
  have h1 := Complex.exp_mul_I ((π : ℂ) * s / 4)
  have h2 : Complex.exp (((π : ℂ) * s / 4) * Complex.I) = 0 := by
    rw [h1, h]
    have : Complex.I * Complex.cos ((π : ℂ) * s / 4) * Complex.I =
        -Complex.cos ((π : ℂ) * s / 4) := by
      have : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination (Complex.cos ((π : ℂ) * s / 4)) * this
    rw [add_comm, this]; ring
  exact Complex.exp_ne_zero _ h2

lemma sTan_ne_neg_I (s : ℂ) (hs : s ∈ unitStripCl) : sTan s ≠ -Complex.I := by
  intro h
  have hc := cos_ne_zero_of_cl hs
  rw [sTan_eq, div_eq_iff hc] at h
  have h1 := Complex.exp_mul_I (-((π : ℂ) * s / 4))
  have h2 : Complex.exp ((-((π : ℂ) * s / 4)) * Complex.I) = 0 := by
    rw [h1, Complex.cos_neg, Complex.sin_neg, h]
    have := Complex.I_mul_I
    linear_combination (Complex.cos ((π : ℂ) * s / 4)) * this
  exact Complex.exp_ne_zero _ h2

lemma differentiableAt_sTan {s : ℂ} (hs : s ∈ unitStripCl) : DifferentiableAt ℂ sTan s := by
  have hc := cos_ne_zero_of_cl hs
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (π : ℂ) * s / 4) s := by fun_prop
  exact (Complex.differentiableAt_tan.2 hc).comp s h1

lemma unitStripCl_subset_closure : unitStripCl ⊆ closure unitStrip := by
  intro s hs
  have hmap : Tendsto (fun δ : ℝ => ((1 - δ : ℝ) : ℂ) * s + (δ / 2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
    have hc : Continuous fun δ : ℝ => ((1 - δ : ℝ) : ℂ) * s + (δ / 2 : ℝ) := by fun_prop
    have := hc.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hmap ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
  have h1 : (0 : ℝ) < 1 - δ := by linarith [hδ.2]
  refine ⟨?_, ?_⟩
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith only [mul_nonneg h1.le hs.1, hδ.1]
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith only [mul_nonneg h1.le (sub_nonneg.2 hs.2), hδ.1, hδ.2]

lemma sTan_mem_closure {s : ℂ} (hs : s ∈ unitStripCl) : sTan s ∈ closure halfDisc := by
  have hne : (𝓝[unitStrip] s).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (unitStripCl_subset_closure hs)
  refine mem_closure_of_tendsto (f := sTan) (b := 𝓝[unitStrip] s) ?_ ?_
  · exact (differentiableAt_sTan hs).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx using sTan_mem_halfDisc hx

end FormalResearch.ModularBootstrap.FiveTerm
