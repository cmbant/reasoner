module

public import FormalResearch.SignUncertainty.CtOuterDeriv

/-!
# Strip integrals with general amplitudes (support for the cubic coefficient of `ct:outer` (2))

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (2), the paragraph on `c_{3,h}`
("differentiating `h(ζ) = ∫ u_r(t) csc(π(ζ - it)) dt` twice via `∂_ζ csc(π(ζ - it)) = i ∂_t csc(π(ζ - it))` and
integrating by parts twice").  **Proved.**

For a continuous amplitude `v` with `|v(t)| ≤ M e^{|t|}`, `genH v ζ = ∫ v(t) / sin(π(ζ - it)) dt` is holomorphic on the
strip with derivative `∫ v(t) kern1`, and for `C¹` amplitudes `∫ v kern1 = -i ∫ v' kern0` (integration by parts).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- The kernel `1/sin(π(ζ - it))`. -/
noncomputable def kern0 (ζ : ℂ) (t : ℝ) : ℂ := 1 / Complex.sin (π * (ζ - Complex.I * t))

/-- Its `ζ`-derivative `-π cos(π(ζ - it)) / sin²(π(ζ - it))`. -/
noncomputable def kern1 (ζ : ℂ) (t : ℝ) : ℂ :=
  -(π : ℂ) * Complex.cos (π * (ζ - Complex.I * t)) / Complex.sin (π * (ζ - Complex.I * t)) ^ 2

/-- The strip integral with amplitude `v`. -/
noncomputable def genH (v : ℝ → ℝ) (ζ : ℂ) : ℂ := ∫ t : ℝ, (v t : ℂ) * kern0 ζ t

/-- Exponential-growth class of amplitudes. -/
def ExpBdd (v : ℝ → ℝ) : Prop := ∃ M : ℝ, ∀ t : ℝ, |v t| ≤ M * Real.exp |t|

lemma outerH_eq_genH : outerH = genH uR := by
  funext ζ
  unfold outerH genH kern0
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp [div_eq_mul_inv]

lemma hasDerivAt_kern0 {ζ : ℂ} (hζ : ζ ∈ strip) (t : ℝ) :
    HasDerivAt (fun z : ℂ => kern0 z t) (kern1 ζ t) ζ := by
  have hne := sin_arg_ne_zero t hζ
  have h1 : HasDerivAt (fun z : ℂ => π * (z - Complex.I * t)) (π : ℂ) ζ := by
    simpa using ((hasDerivAt_id ζ).sub_const (Complex.I * t)).const_mul (π : ℂ)
  have h2 : HasDerivAt (fun z : ℂ => Complex.sin (π * (z - Complex.I * t)))
      (Complex.cos (π * (ζ - Complex.I * t)) * π) ζ := h1.csin
  have h3 := (hasDerivAt_const ζ (1 : ℂ)).div h2 hne
  unfold kern0 kern1
  convert h3 using 1
  ring

lemma hasDerivAt_kern0_t {ζ : ℂ} (hζ : ζ ∈ strip) (t : ℝ) :
    HasDerivAt (fun s : ℝ => kern0 ζ s) (-Complex.I * kern1 ζ t) t := by
  have hne := sin_arg_ne_zero t hζ
  have h1 : HasDerivAt (fun s : ℝ => π * (ζ - Complex.I * s)) (-(π : ℂ) * Complex.I) t := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I).const_sub ζ |>.const_mul (π : ℂ)
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => Complex.sin (π * (ζ - Complex.I * s)))
      (Complex.cos (π * (ζ - Complex.I * t)) * (-(π : ℂ) * Complex.I)) t := by
    have := (Complex.hasDerivAt_sin (π * (ζ - Complex.I * t))).scomp t h1
    exact this.congr_deriv (by simp only [smul_eq_mul]; ring)
  have h3 := (hasDerivAt_const t (1 : ℂ)).div h2 hne
  unfold kern0 kern1
  convert h3 using 1
  ring

lemma continuous_kern0 {ζ : ℂ} (hζ : ζ ∈ strip) : Continuous fun t : ℝ => kern0 ζ t := by
  unfold kern0
  exact Continuous.div continuous_const (by fun_prop) (fun t => sin_arg_ne_zero t hζ)

lemma continuous_kern1 {ζ : ℂ} (hζ : ζ ∈ strip) : Continuous fun t : ℝ => kern1 ζ t := by
  unfold kern1
  exact Continuous.div (by fun_prop) (by fun_prop) (fun t => pow_ne_zero 2 (sin_arg_ne_zero t hζ))

lemma norm_kern0_le {ζ : ℂ} (t : ℝ) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hx : σ ≤ Real.sin (π * ζ.re)) :
    ‖kern0 ζ t‖ ≤ 2 / σ * Real.exp (-(π * |ζ.im - t|)) := by
  unfold kern0
  rw [one_div]
  exact kernel_norm_le t hσ hσ1 hx

lemma norm_kern1_le {ζ : ℂ} (t : ℝ) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hx : σ ≤ Real.sin (π * ζ.re)) :
    ‖kern1 ζ t‖ ≤ 2 * π / σ ^ 2 * Real.exp (-(π * |ζ.im - t|)) := by
  set a : ℝ := π * (ζ.im - t) with ha
  have hs := norm_sin_arg_sq ζ t
  have hc := norm_cos_sq (↑π * (ζ - Complex.I * t))
  rw [re_arg, im_arg] at hc
  rw [← ha] at hs hc
  have hcosh : Real.cosh a ^ 2 = 1 + Real.sinh a ^ 2 := by rw [Real.cosh_sq]; ring
  have hsin_ge : σ * Real.cosh a ≤ ‖Complex.sin (π * (ζ - Complex.I * t))‖ := by
    have : (σ * Real.cosh a) ^ 2 ≤ ‖Complex.sin (π * (ζ - Complex.I * t))‖ ^ 2 := by
      rw [hs, mul_pow, hcosh]
      have : σ ^ 2 ≤ Real.sin (π * ζ.re) ^ 2 := pow_le_pow_left₀ hσ.le hx 2
      have hσ2 : σ ^ 2 ≤ 1 := by nlinarith only [hσ, hσ1]
      nlinarith only [this, mul_nonneg (sub_nonneg.mpr hσ2) (sq_nonneg (Real.sinh a))]
    exact abs_le_of_sq_le_sq' this (norm_nonneg _) |>.2
  have hcos_le : ‖Complex.cos (π * (ζ - Complex.I * t))‖ ≤ Real.cosh a := by
    have : ‖Complex.cos (π * (ζ - Complex.I * t))‖ ^ 2 ≤ Real.cosh a ^ 2 := by
      rw [hc, hcosh]; linarith only [Real.cos_sq_le_one (π * ζ.re)]
    exact abs_le_of_sq_le_sq' this (Real.cosh_pos _).le |>.2
  have hca : 0 < Real.cosh a := Real.cosh_pos a
  have hcabs : Real.cosh a = Real.cosh |a| := by
    rcases abs_cases a with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, Real.cosh_neg]
  have habs : |a| = π * |ζ.im - t| := by
    rw [ha, abs_mul, abs_of_pos Real.pi_pos]
  have hcexp : Real.exp |a| / 2 ≤ Real.cosh a := by
    rw [hcabs, Real.cosh_eq]
    have := Real.exp_pos (-|a|)
    linarith
  unfold kern1
  rw [norm_div, norm_pow, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hsq : (σ * Real.cosh a) ^ 2 ≤ ‖Complex.sin (π * (ζ - Complex.I * t))‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsin_ge 2
  have hpos : 0 < (σ * Real.cosh a) ^ 2 := by positivity
  calc π * ‖Complex.cos (π * (ζ - Complex.I * t))‖ / ‖Complex.sin (π * (ζ - Complex.I * t))‖ ^ 2
      ≤ π * Real.cosh a / (σ * Real.cosh a) ^ 2 := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hcos_le Real.pi_pos.le) hpos hsq
    _ = π / σ ^ 2 * (Real.cosh a)⁻¹ := by field_simp
    _ ≤ π / σ ^ 2 * (2 * Real.exp (-|a|)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 : (Real.cosh a)⁻¹ ≤ (Real.exp |a| / 2)⁻¹ := inv_anti₀ (by positivity) hcexp
        calc (Real.cosh a)⁻¹ ≤ (Real.exp |a| / 2)⁻¹ := h1
          _ = 2 * Real.exp (-|a|) := by rw [Real.exp_neg]; field_simp
    _ = 2 * π / σ ^ 2 * Real.exp (-(π * |ζ.im - t|)) := by rw [habs]; ring


/-- Uniform exponential kernel bounds on a small ball inside the strip. -/
lemma kern_ball_bound {w₀ : ℂ} (hw₀ : w₀ ∈ strip) :
    ∃ r > 0, ∃ C : ℝ, 0 ≤ C ∧ (∀ w ∈ ball w₀ r, w ∈ strip) ∧
      ∀ w ∈ ball w₀ r, ∀ t : ℝ,
        ‖kern0 w t‖ ≤ C * Real.exp (-(π * |t|)) ∧ ‖kern1 w t‖ ≤ C * Real.exp (-(π * |t|)) := by
  set a : ℝ := min w₀.re (1 - w₀.re) / 2 with ha
  have hapos : 0 < a := by
    have := lt_min hw₀.1 (by linarith [hw₀.2] : 0 < 1 - w₀.re)
    rw [ha]; linarith
  have ha2 : a ≤ 1 / 2 := by
    have := min_le_left w₀.re (1 - w₀.re)
    have := min_le_right w₀.re (1 - w₀.re)
    rw [ha]; linarith
  set σ : ℝ := Real.sin (π * a) with hσ
  have hσpos : 0 < σ := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hσ1 : σ ≤ 1 := Real.sin_le_one _
  refine ⟨min a 1, lt_min hapos one_pos, (2 / σ + 2 * π / σ ^ 2) * Real.exp (π * (|w₀.im| + 1)),
    by positivity, ?_, ?_⟩
  · intro w hw
    have hwb : w ∈ ball w₀ a := ball_subset_ball (min_le_left _ _) hw
    obtain ⟨hl, hr⟩ := mem_strip_of_ball hwb
    exact ⟨by linarith, by linarith⟩
  · intro w hw t
    have hwb : w ∈ ball w₀ a := ball_subset_ball (min_le_left _ _) hw
    obtain ⟨hl, hr⟩ := mem_strip_of_ball hwb
    have hσle : σ ≤ Real.sin (π * w.re) := sin_pi_ge hapos ha2 hl hr
    have him : |w.im - w₀.im| ≤ 1 := by
      have := Complex.abs_im_le_norm (w - w₀)
      rw [mem_ball, dist_eq_norm] at hw
      have h1 : ‖w - w₀‖ < min a 1 := hw
      simp only [Complex.sub_im] at this
      linarith [min_le_right a 1]
    have hy : |w.im| ≤ |w₀.im| + 1 := by
      calc |w.im| = |(w.im - w₀.im) + w₀.im| := by ring_nf
        _ ≤ |w.im - w₀.im| + |w₀.im| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hexp : Real.exp (-(π * |w.im - t|)) ≤ Real.exp (π * (|w₀.im| + 1)) * Real.exp (-(π * |t|)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : |t| ≤ |w.im - t| + |w.im| := by
        calc |t| = |w.im - (w.im - t)| := by ring_nf
          _ ≤ |w.im| + |w.im - t| := abs_sub _ _
          _ = _ := by ring
      nlinarith [Real.pi_pos]
    have hE : 0 ≤ Real.exp (π * (|w₀.im| + 1)) * Real.exp (-(π * |t|)) := by positivity
    have h0 := norm_kern0_le (ζ := w) t hσpos hσ1 hσle
    have h1 := norm_kern1_le (ζ := w) t hσpos hσ1 hσle
    constructor
    · calc ‖kern0 w t‖ ≤ 2 / σ * (Real.exp (π * (|w₀.im| + 1)) * Real.exp (-(π * |t|))) :=
            h0.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
        _ ≤ (2 / σ + 2 * π / σ ^ 2) * Real.exp (π * (|w₀.im| + 1)) * Real.exp (-(π * |t|)) := by
            have : 0 ≤ 2 * π / σ ^ 2 := by positivity
            nlinarith [mul_nonneg this hE]
    · calc ‖kern1 w t‖ ≤ 2 * π / σ ^ 2 * (Real.exp (π * (|w₀.im| + 1)) * Real.exp (-(π * |t|))) :=
            h1.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
        _ ≤ (2 / σ + 2 * π / σ ^ 2) * Real.exp (π * (|w₀.im| + 1)) * Real.exp (-(π * |t|)) := by
            have : 0 ≤ 2 / σ := by positivity
            nlinarith [mul_nonneg this hE]

lemma ExpBdd_nonneg_const {v : ℝ → ℝ} (hb : ExpBdd v) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |v t| ≤ M * Real.exp |t| := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨max M 0, le_max_right _ _, fun t => (hM t).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- Integrability of `v(t) · kern` for exponentially bounded `v`, given a kernel bound. -/
lemma integrable_amp_mul_kern {v : ℝ → ℝ} (hv : Continuous v) (hb : ExpBdd v) {k : ℝ → ℂ}
    (hk : Continuous k) {C : ℝ} (hC : ∀ t, ‖k t‖ ≤ C * Real.exp (-(π * |t|))) :
    Integrable fun t : ℝ => (v t : ℂ) * k t := by
  obtain ⟨M, hM0, hM⟩ := ExpBdd_nonneg_const hb
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg (k 0)).trans (hC 0)
    simpa using this
  have hint := (integrable_exp_neg_abs' (c := π - 1) (by linarith [Real.pi_gt_three])).const_mul (M * C)
  refine Integrable.mono' hint ((Complex.continuous_ofReal.comp hv).mul hk).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |v t| * ‖k t‖ ≤ (M * Real.exp |t|) * (C * Real.exp (-(π * |t|))) :=
        mul_le_mul (hM t) (hC t) (norm_nonneg _) (by positivity)
    _ = M * C * Real.exp (-(π - 1) * |t|) := by
        rw [show -(π - 1) * |t| = |t| + -(π * |t|) by ring, Real.exp_add]; ring


/-- Differentiation under the integral sign for `genH`. -/
theorem hasDerivAt_genH {v : ℝ → ℝ} (hv : Continuous v) (hb : ExpBdd v) {w₀ : ℂ} (hw₀ : w₀ ∈ strip) :
    HasDerivAt (genH v) (∫ t : ℝ, (v t : ℂ) * kern1 w₀ t) w₀ := by
  obtain ⟨M, hM0, hM⟩ := ExpBdd_nonneg_const hb
  have h := hasDerivAt_integral_param (μ := volume) (Φ := fun w t => (v t : ℂ) * kern0 w t)
    isOpen_strip ?_ ?_ ?_ hw₀
  · have e : (fun t : ℝ => deriv (fun z : ℂ => (v t : ℂ) * kern0 z t) w₀) =
        fun t : ℝ => (v t : ℂ) * kern1 w₀ t := by
      ext t
      exact (((hasDerivAt_kern0 hw₀ t).const_mul (v t : ℂ)).deriv)
    rw [e] at h
    exact h
  · intro w hw
    exact ((Complex.continuous_ofReal.comp hv).mul (continuous_kern0 hw)).aestronglyMeasurable
  · refine Eventually.of_forall fun t w hw => ?_
    exact ((hasDerivAt_kern0 hw t).differentiableAt.const_mul (v t : ℂ)).differentiableWithinAt
  · intro w₁ hw₁
    obtain ⟨r, hr, C, hC0, hrs, hCb⟩ := kern_ball_bound hw₁
    refine ⟨r, hr, fun t => (M * C) * Real.exp (-(π - 1) * |t|),
      (integrable_exp_neg_abs' (c := π - 1) (by linarith [Real.pi_gt_three])).const_mul (M * C),
      Eventually.of_forall fun t w hw => ?_⟩
    have hk := (hCb w hw t).1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |v t| * ‖kern0 w t‖ ≤ (M * Real.exp |t|) * (C * Real.exp (-(π * |t|))) :=
          mul_le_mul (hM t) hk (norm_nonneg _) (by positivity)
      _ = M * C * Real.exp (-(π - 1) * |t|) := by
          rw [show -(π - 1) * |t| = |t| + -(π * |t|) by ring, Real.exp_add]; ring

/-- **Integration by parts** (`∂_ζ csc(π(ζ - it)) = i ∂_t csc(π(ζ - it))`): for a `C¹` amplitude
`v` with `v, v'` exponentially bounded, `∫ v kern1 = -i ∫ v' kern0`. -/
theorem integral_amp_kern1 {v v' : ℝ → ℝ} (hd : ∀ t, HasDerivAt v (v' t) t) (hv' : Continuous v')
    (hb : ExpBdd v) (hb' : ExpBdd v') {ζ : ℂ} (hζ : ζ ∈ strip) :
    ∫ t : ℝ, (v t : ℂ) * kern1 ζ t = -Complex.I * ∫ t : ℝ, (v' t : ℂ) * kern0 ζ t := by
  have hv : Continuous v := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  obtain ⟨r, hr, C, hC0, hrs, hCb⟩ := kern_ball_bound hζ
  have hk0 : ∀ t, ‖kern0 ζ t‖ ≤ C * Real.exp (-(π * |t|)) := fun t => (hCb ζ (mem_ball_self hr) t).1
  have hk1 : ∀ t, ‖kern1 ζ t‖ ≤ C * Real.exp (-(π * |t|)) := fun t => (hCb ζ (mem_ball_self hr) t).2
  have hu : ∀ t, HasDerivAt (fun s : ℝ => (v s : ℂ)) (v' t : ℂ) t := fun t => (hd t).ofReal_comp
  have hI1 : Integrable fun t : ℝ => (v t : ℂ) * (-Complex.I * kern1 ζ t) := by
    have := (integrable_amp_mul_kern hv hb (continuous_kern1 hζ) hk1).const_mul (-Complex.I)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only; ring
  have hI2 : Integrable fun t : ℝ => (v' t : ℂ) * kern0 ζ t :=
    integrable_amp_mul_kern hv' hb' (continuous_kern0 hζ) hk0
  have hI3 : Integrable fun t : ℝ => (v t : ℂ) * kern0 ζ t :=
    integrable_amp_mul_kern hv hb (continuous_kern0 hζ) hk0
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun s : ℝ => (v s : ℂ)) (v := fun s : ℝ => kern0 ζ s)
    (fun x _ => hu x) (fun t _ => hasDerivAt_kern0_t hζ t) hI1 hI2 hI3
  have e1 : ∫ t : ℝ, (v t : ℂ) * (-Complex.I * kern1 ζ t) = -Complex.I * ∫ t : ℝ, (v t : ℂ) * kern1 ζ t := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)
  rw [e1] at hibp
  linear_combination Complex.I * hibp + (∫ t : ℝ, (v t : ℂ) * kern1 ζ t) * Complex.I_sq


lemma integral_kern1_eq_zero {ζ : ℂ} (hζ : ζ ∈ strip) : ∫ t : ℝ, kern1 ζ t = 0 := by
  have h := integral_amp_kern1 (v := fun _ => (1 : ℝ)) (v' := fun _ => (0 : ℝ)) (fun t => hasDerivAt_const t 1)
    continuous_const ⟨1, fun t => by simp [Real.one_le_exp (abs_nonneg t)]⟩ ⟨0, fun t => by simp⟩ hζ
  simpa using h

/-- The majorant `π cosh(πt)/sinh²(πt)` of `‖kern1 x t‖`. -/
noncomputable def thetaK (t : ℝ) : ℝ := π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2

lemma thetaK_nonneg (t : ℝ) : 0 ≤ thetaK t := by unfold thetaK; positivity

lemma norm_kern1_le_thetaK {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {t : ℝ} (ht : t ≠ 0) :
    ‖kern1 (x : ℂ) t‖ ≤ thetaK t := by
  have hxs : (x : ℂ) ∈ strip := ⟨by simpa using hx0, by simpa using hx1⟩
  have hs1 := norm_sin_arg_sq (x : ℂ) t
  have hc1 := norm_cos_sq (↑π * ((x : ℂ) - Complex.I * t))
  rw [re_arg, im_arg] at hc1
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_sub, mul_neg, Real.sinh_neg, neg_sq] at hs1 hc1
  have hsin2 : Real.sinh (π * t) ^ 2 ≤ ‖Complex.sin (π * ((x : ℂ) - Complex.I * t))‖ ^ 2 := by
    rw [hs1]; linarith only [sq_nonneg (Real.sin (π * x))]
  have hcos : ‖Complex.cos (π * ((x : ℂ) - Complex.I * t))‖ ≤ Real.cosh (π * t) := by
    have : ‖Complex.cos (π * ((x : ℂ) - Complex.I * t))‖ ^ 2 ≤ Real.cosh (π * t) ^ 2 := by
      rw [hc1, Real.cosh_sq]; linarith only [Real.cos_sq_le_one (π * x)]
    exact abs_le_of_sq_le_sq' this (Real.cosh_pos _).le |>.2
  have hsh : Real.sinh (π * t) ≠ 0 := Real.sinh_eq_zero.not.mpr (mul_ne_zero Real.pi_pos.ne' ht)
  have hpos : 0 < Real.sinh (π * t) ^ 2 := by positivity
  unfold kern1 thetaK
  rw [norm_div, norm_pow, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  calc π * ‖Complex.cos (π * ((x : ℂ) - Complex.I * t))‖ / ‖Complex.sin (π * ((x : ℂ) - Complex.I * t))‖ ^ 2
      ≤ π * Real.cosh (π * t) / ‖Complex.sin (π * ((x : ℂ) - Complex.I * t))‖ ^ 2 := by
        gcongr
    _ ≤ π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) hpos hsin2

lemma kern1_zero {t : ℝ} (ht : t ≠ 0) :
    kern1 ((0 : ℝ) : ℂ) t = ((thetaK t : ℝ) : ℂ) := by
  have hsh : Real.sinh (π * t) ≠ 0 := Real.sinh_eq_zero.not.mpr (mul_ne_zero Real.pi_pos.ne' ht)
  have hshC : (Real.sinh (π * t) : ℂ) ≠ 0 := by exact_mod_cast hsh
  have e : (π : ℂ) * (((0 : ℝ) : ℂ) - Complex.I * t) = ((-(π * t) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  unfold kern1 thetaK
  rw [e, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Real.cosh_neg,
    Real.sinh_neg]
  push_cast
  field_simp
  simp [Complex.I_sq]
  ring

lemma integrable_amp_thetaK {w : ℝ → ℝ} (hw : Continuous w) (hb : ExpBdd w)
    (hn : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 / 2 → |w t| ≤ C * t ^ 2) :
    Integrable fun t : ℝ => |w t| * thetaK t := by
  obtain ⟨M, hM0, hM⟩ := ExpBdd_nonneg_const hb
  obtain ⟨C, hC⟩ := hn
  have hpi := Real.pi_pos
  have hC0 : 0 ≤ C := by
    have h1 := hC (1 / 4) (by norm_num [abs_of_pos])
    have h2 : 0 ≤ |w (1 / 4)| := abs_nonneg _
    linarith only [h1, h2]
  set q : ℝ := Real.exp (-(2 * π * (1 / 2))) with hqdef
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hpi])
  have hqpos : 0 < 1 - q := by linarith
  set A : ℝ := 4 * π / (1 - q) ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set B : ℝ := C * Real.cosh (π / 2) / π with hB
  have hB0 : 0 ≤ B := by have := Real.cosh_pos (π / 2); positivity
  set D : ℝ := B * Real.exp ((π - 1) / 2) + M * A with hD
  have hD0 : 0 ≤ D := by positivity
  have hint := (integrable_exp_neg_abs' (c := π - 1) (by linarith [Real.pi_gt_three])).const_mul D
  refine Integrable.mono' hint ?_ (Eventually.of_forall fun t => ?_)
  · have hc : Continuous fun t : ℝ => |w t| * (π * Real.cosh (π * t)) := by fun_prop
    have hd : Continuous fun t : ℝ => Real.sinh (π * t) ^ 2 := by fun_prop
    have := (hc.measurable.div hd.measurable).aestronglyMeasurable (μ := volume)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [thetaK, Pi.div_apply]; ring
  · have hnn : 0 ≤ |w t| * thetaK t := mul_nonneg (abs_nonneg _) (thetaK_nonneg t)
    rw [Real.norm_of_nonneg hnn]
    by_cases ht : t = 0
    · subst ht
      have : |w 0| ≤ 0 := by simpa using hC 0 (by simp)
      have h0 : w 0 = 0 := abs_nonpos_iff.mp this
      simp [h0]
      positivity
    have hsh : Real.sinh (π * t) ≠ 0 := Real.sinh_eq_zero.not.mpr (mul_ne_zero hpi.ne' ht)
    have hsq : Real.sinh (π * t) ^ 2 = Real.sinh (π * |t|) ^ 2 := by
      rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h, mul_neg, Real.sinh_neg, neg_sq]
    have hcos : Real.cosh (π * t) = Real.cosh (π * |t|) := by
      rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h, mul_neg, Real.cosh_neg]
    unfold thetaK
    rw [hsq, hcos]
    have hpos : 0 < |t| := abs_pos.mpr ht
    have hcp : 0 < Real.cosh (π * |t|) := Real.cosh_pos _
    rcases le_or_gt |t| (1 / 2) with hle | hgt
    · have hsinh : π * |t| ≤ Real.sinh (π * |t|) := Real.self_le_sinh_iff.mpr (by positivity)
      have hcosh : Real.cosh (π * |t|) ≤ Real.cosh (π / 2) := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ π * |t|), abs_of_pos (by positivity : (0 : ℝ) < π / 2)]
        linarith only [mul_nonneg hpi.le (sub_nonneg.2 hle)]
      have hu : |w t| ≤ C * t ^ 2 := hC t hle
      have hnear : |w t| * (π * Real.cosh (π * |t|) / Real.sinh (π * |t|) ^ 2) ≤ B := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        calc |w t| * (π * Real.cosh (π * |t|)) ≤ (C * t ^ 2) * (π * Real.cosh (π / 2)) := by gcongr
          _ = B * (π * |t|) ^ 2 := by rw [mul_pow, sq_abs, hB]; field_simp
          _ ≤ B * Real.sinh (π * |t|) ^ 2 := by gcongr
      have hexp1 : 1 ≤ Real.exp ((π - 1) / 2) * Real.exp (-(π - 1) * |t|) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith only [mul_nonneg (by linarith only [Real.pi_gt_three] : (0 : ℝ) ≤ π - 1) (sub_nonneg.2 hle)])
      have : B ≤ D * Real.exp (-(π - 1) * |t|) := by
        have h1 : B ≤ B * (Real.exp ((π - 1) / 2) * Real.exp (-(π - 1) * |t|)) := by
          have := mul_le_mul_of_nonneg_left hexp1 hB0
          linarith only [this]
        have h2 : B * (Real.exp ((π - 1) / 2) * Real.exp (-(π - 1) * |t|)) ≤ D * Real.exp (-(π - 1) * |t|) := by
          rw [hD]
          have : 0 ≤ M * A * Real.exp (-(π - 1) * |t|) := by positivity
          linarith only [this]
        linarith
      linarith
    · set E : ℝ := Real.exp (π * |t|) with hE
      have hEpos : 0 < E := Real.exp_pos _
      have hsl := sinh_pi_lower (m := 1 / 2) (s := |t|) hgt.le
      rw [← hqdef, ← hE] at hsl
      have hcosh : Real.cosh (π * |t|) ≤ E := by
        rw [Real.cosh_eq]
        have : Real.exp (-(π * |t|)) ≤ E := by
          rw [hE]; exact Real.exp_le_exp.mpr (by linarith only [mul_nonneg hpi.le (abs_nonneg t)])
        linarith
      have hs2 : ((1 - q) / 2 * E) ^ 2 ≤ Real.sinh (π * |t|) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsl 2
      have hθ : π * Real.cosh (π * |t|) / Real.sinh (π * |t|) ^ 2 ≤ A * Real.exp (-(π * |t|)) := by
        rw [div_le_iff₀ (by positivity)]
        have hE' : Real.exp (-(π * |t|)) = E⁻¹ := Real.exp_neg _
        calc π * Real.cosh (π * |t|) ≤ π * E := by gcongr
          _ = A * Real.exp (-(π * |t|)) * ((1 - q) / 2 * E) ^ 2 := by
              rw [hE', hA]; field_simp; norm_num
          _ ≤ A * Real.exp (-(π * |t|)) * Real.sinh (π * |t|) ^ 2 := by gcongr
      have hu : |w t| ≤ M * Real.exp |t| := hM t
      calc |w t| * (π * Real.cosh (π * |t|) / Real.sinh (π * |t|) ^ 2)
          ≤ (M * Real.exp |t|) * (A * Real.exp (-(π * |t|))) :=
            mul_le_mul hu hθ (by positivity) (by positivity)
        _ = M * A * Real.exp (-(π - 1) * |t|) := by
            rw [show -(π - 1) * |t| = |t| + -(π * |t|) by ring, Real.exp_add]; ring
        _ ≤ D * Real.exp (-(π - 1) * |t|) := by
            rw [hD]
            have : 0 ≤ B * Real.exp ((π - 1) / 2) * Real.exp (-(π - 1) * |t|) := by positivity
            linarith only [this]


/-- **Limit at the fold.**  For a continuous exponentially bounded amplitude `w = O(t²)` near `0`,
`∫ w kern1(x, ·) → ∫ w π cosh(πt)/sinh²(πt)` as `x ↓ 0` (dominated convergence). -/
theorem tendsto_amp_kern1 {w : ℝ → ℝ} (hw : Continuous w) (hb : ExpBdd w)
    (hn : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 / 2 → |w t| ≤ C * t ^ 2) :
    Tendsto (fun x : ℝ => ∫ t : ℝ, (w t : ℂ) * kern1 (x : ℂ) t) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, ((w t * thetaK t : ℝ) : ℂ))) := by
  obtain ⟨C, hC⟩ := hn
  have hw0 : w 0 = 0 := by
    have : |w 0| ≤ 0 := by simpa using hC 0 (by simp)
    exact abs_nonpos_iff.mp this
  refine tendsto_integral_filter_of_dominated_convergence (fun t => |w t| * thetaK t) ?_ ?_
    (integrable_amp_thetaK hw hb ⟨C, hC⟩) ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hxs : (x : ℂ) ∈ strip := ⟨by simpa using hx.1, by simpa using hx.2⟩
    exact ((Complex.continuous_ofReal.comp hw).mul (continuous_kern1 hxs)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    refine Eventually.of_forall fun t => ?_
    by_cases ht : t = 0
    · subst ht; simp [hw0]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_kern1_le_thetaK hx.1 hx.2 ht) (abs_nonneg _)
  · have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
      simpa using (Set.countable_singleton (0 : ℝ)).ae_notMem volume
    filter_upwards [hne] with t ht
    have hden : Complex.sin (π * (((0 : ℝ) : ℂ) - Complex.I * t)) ≠ 0 := by
      intro h
      have h1 := norm_sin_arg_sq (((0 : ℝ) : ℂ)) t
      rw [h, norm_zero] at h1
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_sub, mul_neg, Real.sinh_neg, neg_sq, mul_zero,
        Real.sin_zero] at h1
      have hsh : Real.sinh (π * t) ≠ 0 := Real.sinh_eq_zero.not.mpr (mul_ne_zero Real.pi_pos.ne' ht)
      have : Real.sinh (π * t) ^ 2 = 0 := by linarith only [h1]
      exact hsh (pow_eq_zero_iff (two_ne_zero) |>.mp this)
    have hc : ContinuousAt (fun x : ℝ => kern1 (x : ℂ) t) 0 := by
      unfold kern1
      refine ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hden)
    have := (hc.tendsto.const_mul ((w t : ℂ))).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [kern1_zero ht] at this
    simpa using this


lemma expBdd_uR : ExpBdd uR := by
  refine ⟨2 + 2 * C0, fun t => ?_⟩
  have h1 := abs_uR_le' t
  have h2 := log_one_add_sq_le t
  have h3 : |t| ≤ Real.exp |t| := by linarith only [Real.add_one_le_exp |t|]
  have h4 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  have h5 := mul_le_mul_of_nonneg_left h4 C0_nonneg
  linarith only [h1, h2, h3, h5]

/-- **Third derivative of `H₀` on the real segment** (two integrations by parts):
`H₀'''(x) = -∫ u_r''(t) kern1(x, t) dt` for `0 < x < 1/2`. -/
theorem deriv3_H0_real {u1 u2 : ℝ → ℝ} (hu1 : ∀ t, HasDerivAt uR (u1 t) t) (hu2 : ∀ t, HasDerivAt u1 (u2 t) t)
    (hc1 : Continuous u1) (hc2 : Continuous u2) (hb1 : ExpBdd u1) (hb2 : ExpBdd u2)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    deriv (deriv (deriv H0)) (x : ℂ) = -∫ t : ℝ, (u2 t : ℂ) * kern1 (x : ℂ) t := by
  have hcu : Continuous uR := continuous_uR
  have hU : IsOpen (strip ∩ ball (0 : ℂ) (1 / 2)) := isOpen_strip.inter isOpen_ball
  have hxU : (x : ℂ) ∈ strip ∩ ball (0 : ℂ) (1 / 2) := by
    refine ⟨⟨by simpa using hx0, by simp; linarith⟩, ?_⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx1
  -- derivatives of the three strip integrals
  have d0 : ∀ z ∈ strip, HasDerivAt (genH uR) (-Complex.I * genH u1 z) z := by
    intro z hz
    have h := hasDerivAt_genH hcu expBdd_uR hz
    rw [integral_amp_kern1 hu1 hc1 expBdd_uR hb1 hz] at h
    exact h
  have d1 : ∀ z ∈ strip, HasDerivAt (genH u1) (-Complex.I * genH u2 z) z := by
    intro z hz
    have h := hasDerivAt_genH hc1 hb1 hz
    rw [integral_amp_kern1 hu2 hc2 hb1 hb2 hz] at h
    exact h
  have d2 : ∀ z ∈ strip, HasDerivAt (genH u2) (∫ t : ℝ, (u2 t : ℂ) * kern1 z t) z :=
    fun z hz => hasDerivAt_genH hc2 hb2 hz
  -- `H₀ = outerH = genH uR` near every point of `U`
  have hev : ∀ z ∈ strip ∩ ball (0 : ℂ) (1 / 2), H0 =ᶠ[𝓝 z] genH uR := by
    intro z hz
    filter_upwards [hU.mem_nhds hz] with y hy
    rw [← outerH_eq_genH]
    exact (outerH_eq_H0 hy.1 hy.2).symm
  have e1 : ∀ z ∈ strip ∩ ball (0 : ℂ) (1 / 2), deriv H0 z = -Complex.I * genH u1 z := by
    intro z hz
    exact ((d0 z hz.1).congr_of_eventuallyEq (hev z hz)).deriv
  have h1 : ∀ z ∈ strip ∩ ball (0 : ℂ) (1 / 2), deriv H0 =ᶠ[𝓝 z] fun y => -Complex.I * genH u1 y := by
    intro z hz
    filter_upwards [hU.mem_nhds hz] with y hy using e1 y hy
  have e2 : ∀ z ∈ strip ∩ ball (0 : ℂ) (1 / 2), deriv (deriv H0) z = -genH u2 z := by
    intro z hz
    have hd : HasDerivAt (fun y => -Complex.I * genH u1 y) (-Complex.I * (-Complex.I * genH u2 z)) z :=
      (d1 z hz.1).const_mul (-Complex.I)
    rw [(hd.congr_of_eventuallyEq (h1 z hz)).deriv]
    linear_combination (genH u2 z) * Complex.I_sq
  have h2 : deriv (deriv H0) =ᶠ[𝓝 (x : ℂ)] fun y => -genH u2 y := by
    filter_upwards [hU.mem_nhds hxU] with y hy using e2 y hy
  have hd3 : HasDerivAt (fun y => -genH u2 y) (-∫ t : ℝ, (u2 t : ℂ) * kern1 (x : ℂ) t) (x : ℂ) :=
    (d2 _ hxU.1).neg
  exact (hd3.congr_of_eventuallyEq h2).deriv


lemma expBdd_sub_const {v : ℝ → ℝ} (hb : ExpBdd v) (c : ℝ) : ExpBdd (fun t => v t - c) := by
  obtain ⟨M, hM0, hM⟩ := ExpBdd_nonneg_const hb
  refine ⟨M + |c|, fun t => ?_⟩
  have h4 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  have h5 := mul_le_mul_of_nonneg_left h4 (abs_nonneg c)
  have := hM t
  have h6 := abs_sub (v t) c
  linarith only [this, h5, h6]

/-- **`ct:outer` (2): the third derivative of `H₀` at `0`.**  If `u_r` is `C²` (`u1 = u_r'`, `u2 = u_r''`
continuous, exponentially bounded) and `u2(t) - u2(0) = O(t²)`, then
`H₀'''(0) = -∫_ℝ (u2(t) - u2(0)) π cosh(πt)/sinh²(πt) dt`. -/
theorem deriv3_H0_zero {u1 u2 : ℝ → ℝ} (hu1 : ∀ t, HasDerivAt uR (u1 t) t) (hu2 : ∀ t, HasDerivAt u1 (u2 t) t)
    (hc1 : Continuous u1) (hc2 : Continuous u2) (hb1 : ExpBdd u1) (hb2 : ExpBdd u2)
    (hn : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 / 2 → |u2 t - u2 0| ≤ C * t ^ 2) :
    deriv (deriv (deriv H0)) 0 = -∫ t : ℝ, (((u2 t - u2 0) * thetaK t : ℝ) : ℂ) := by
  have hb2' := expBdd_sub_const hb2 (u2 0)
  have hlim := tendsto_amp_kern1 (w := fun t => u2 t - u2 0) (hc2.sub continuous_const) hb2' hn
  have hcont : ContinuousAt (deriv (deriv (deriv H0))) 0 := by
    have h1 := differentiableOn_H0.deriv isOpen_ball
    have h2 := h1.deriv isOpen_ball
    have h3 := h2.deriv isOpen_ball
    exact h3.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))
  have h2 : Tendsto (fun x : ℝ => deriv (deriv (deriv H0)) (x : ℂ)) (𝓝[>] 0)
      (𝓝 (deriv (deriv (deriv H0)) 0)) := by
    have := hcont.tendsto.comp (Complex.continuous_ofReal.tendsto 0)
    exact this.mono_left nhdsWithin_le_nhds
  have h3 : ∀ᶠ x : ℝ in 𝓝[>] 0, deriv (deriv (deriv H0)) (x : ℂ) =
      -∫ t : ℝ, ((u2 t - u2 0 : ℝ) : ℂ) * kern1 (x : ℂ) t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    have hxs : (x : ℂ) ∈ strip := ⟨by simpa using hx.1, by simp; linarith [hx.2]⟩
    rw [deriv3_H0_real hu1 hu2 hc1 hc2 hb1 hb2 hx.1 hx.2]
    congr 1
    obtain ⟨r, hr, C, hC0, hrs, hCb⟩ := kern_ball_bound hxs
    have hk1 : ∀ t, ‖kern1 (x : ℂ) t‖ ≤ C * Real.exp (-(π * |t|)) := fun t => (hCb _ (mem_ball_self hr) t).2
    have hk0 : ∀ t, ‖kern0 (x : ℂ) t‖ ≤ C * Real.exp (-(π * |t|)) := fun t => (hCb _ (mem_ball_self hr) t).1
    have i1 := integrable_amp_mul_kern hc2 hb2 (continuous_kern1 hxs) hk1
    have i2 : Integrable fun t : ℝ => kern1 (x : ℂ) t := by
      have := integrable_amp_mul_kern (v := fun _ => (1 : ℝ)) continuous_const
        ⟨1, fun t => by simp [Real.one_le_exp (abs_nonneg t)]⟩ (continuous_kern1 hxs) hk1
      simpa using this
    have : ∀ t : ℝ, ((u2 t - u2 0 : ℝ) : ℂ) * kern1 (x : ℂ) t =
        (u2 t : ℂ) * kern1 (x : ℂ) t - (u2 0 : ℂ) * kern1 (x : ℂ) t := fun t => by push_cast; ring
    simp_rw [this]
    rw [integral_sub i1 (i2.const_mul _), integral_const_mul, integral_kern1_eq_zero hxs]
    simp
  have := hlim
  rw [← neg_neg (deriv (deriv (deriv H0)) 0)]
  have h4 := (h2.congr' h3)
  exact (tendsto_nhds_unique h4 hlim.neg) ▸ by simp

/-- info: 'FormalResearch.SignUncertainty.CtOuter.integral_amp_kern1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_amp_kern1

/-- info: 'FormalResearch.SignUncertainty.CtOuter.hasDerivAt_genH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_genH

/-- info: 'FormalResearch.SignUncertainty.CtOuter.tendsto_amp_kern1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_amp_kern1

/-- info: 'FormalResearch.SignUncertainty.CtOuter.deriv3_H0_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deriv3_H0_real

/-- info: 'FormalResearch.SignUncertainty.CtOuter.deriv3_H0_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deriv3_H0_zero

end FormalResearch.SignUncertainty.CtOuter
