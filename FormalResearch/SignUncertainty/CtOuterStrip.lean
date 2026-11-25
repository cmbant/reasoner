module

public import FormalResearch.SignUncertainty.CtOuterDefs
public import FormalResearch.SignUncertainty.CtOuterParam

/-!
# The strip integral `h` of `ct:outer`: holomorphy, kernel estimates, symmetries

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (1), eq. `ct:Gdef` and the
first half of the proof of (1).  **Proved.**

`outerH ζ = ∫ u_r(t) / sin(π(ζ - i t)) dt` on the strip `S = {0 < Re ζ < 1}`.

* `norm_sin_sq`: `‖sin w‖² = sin²(Re w) + sinh²(Im w)`; `kernel_norm_le`: on `σ ≤ sin(π Re ζ)`,
  `‖1/sin(π(ζ - i t))‖ ≤ (2/σ) e^{-π|Im ζ - t|}`;
* `differentiableOn_outerH`: `h` is holomorphic on `S` (`differentiableOn_integral_param` with the
  integrable majorant `(log(1+t²) + C₀) e^{-π|t|}`);
* `outerH_conj` (real symmetry) and `outerH_one_sub` (`h(1 - ζ) = h(ζ)`), both from the evenness of `u_r`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- The open strip `0 < Re ζ < 1`. -/
def strip : Set ℂ := {ζ | 0 < ζ.re ∧ ζ.re < 1}

lemma isOpen_strip : IsOpen strip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)

/-- The strip integral `h(ζ) = ∫ u_r(t) / sin(π(ζ - i t)) dt` of `ct:Gdef`. -/
noncomputable def outerH (ζ : ℂ) : ℂ :=
  ∫ t : ℝ, (uR t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))

lemma sin_eq_re_im (w : ℂ) :
    Complex.sin w = ((Real.sin w.re * Real.cosh w.im : ℝ) : ℂ) +
      ((Real.cos w.re * Real.sinh w.im : ℝ) : ℂ) * Complex.I := by
  have h := Complex.sin_add_mul_I (w.re : ℂ) (w.im : ℂ)
  rw [Complex.re_add_im] at h
  rw [h]
  push_cast
  ring

lemma norm_sin_sq (w : ℂ) : ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, sin_eq_re_im w]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    zero_add]
  have h := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  nlinarith [h, h2]

lemma re_arg (ζ : ℂ) (t : ℝ) : (↑π * (ζ - Complex.I * t)).re = π * ζ.re := by
  simp [Complex.mul_re]

lemma im_arg (ζ : ℂ) (t : ℝ) : (↑π * (ζ - Complex.I * t)).im = π * (ζ.im - t) := by
  simp [Complex.mul_im]

lemma norm_sin_arg_sq (ζ : ℂ) (t : ℝ) :
    ‖Complex.sin (π * (ζ - Complex.I * t))‖ ^ 2 =
      Real.sin (π * ζ.re) ^ 2 + Real.sinh (π * (ζ.im - t)) ^ 2 := by
  rw [norm_sin_sq, re_arg, im_arg]

lemma norm_sin_arg_ge {ζ : ℂ} (t : ℝ) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hx : σ ≤ Real.sin (π * ζ.re)) :
    σ * (Real.exp (π * |ζ.im - t|) / 2) ≤ ‖Complex.sin (π * (ζ - Complex.I * t))‖ := by
  have h1 := norm_sin_arg_sq ζ t
  have hc : Real.cosh (π * (ζ.im - t)) = Real.cosh (π * |ζ.im - t|) := by
    rcases abs_cases (ζ.im - t) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.cosh_neg]
  have hcosh : Real.exp (π * |ζ.im - t|) / 2 ≤ Real.cosh (π * |ζ.im - t|) := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-(π * |ζ.im - t|))
    linarith
  have h2 : (σ * Real.cosh (π * (ζ.im - t))) ^ 2 ≤ ‖Complex.sin (π * (ζ - Complex.I * t))‖ ^ 2 := by
    rw [h1, mul_pow, Real.cosh_sq]
    have : σ ^ 2 ≤ Real.sin (π * ζ.re) ^ 2 := by
      exact pow_le_pow_left₀ hσ.le hx 2
    nlinarith [sq_nonneg (Real.sinh (π * (ζ.im - t))), mul_nonneg (sub_nonneg.mpr (by nlinarith : σ ^ 2 ≤ 1))
      (sq_nonneg (Real.sinh (π * (ζ.im - t))))]
  have h3 : σ * Real.cosh (π * (ζ.im - t)) ≤ ‖Complex.sin (π * (ζ - Complex.I * t))‖ := by
    refine abs_le_of_sq_le_sq' ?_ (norm_nonneg _) |>.2
    simpa using h2
  calc σ * (Real.exp (π * |ζ.im - t|) / 2) ≤ σ * Real.cosh (π * |ζ.im - t|) := by gcongr
    _ = σ * Real.cosh (π * (ζ.im - t)) := by rw [hc]
    _ ≤ _ := h3

lemma sin_arg_ne_zero {ζ : ℂ} (t : ℝ) (hζ : ζ ∈ strip) :
    Complex.sin (π * (ζ - Complex.I * t)) ≠ 0 := by
  intro h
  have h1 := norm_sin_arg_sq ζ t
  rw [h, norm_zero] at h1
  have hs : 0 < Real.sin (π * ζ.re) := Real.sin_pos_of_pos_of_lt_pi (by have := hζ.1; positivity)
    (by have := hζ.2; nlinarith [Real.pi_pos])
  nlinarith [sq_nonneg (Real.sinh (π * (ζ.im - t))), pow_pos hs 2]

lemma kernel_norm_le {ζ : ℂ} (t : ℝ) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hx : σ ≤ Real.sin (π * ζ.re)) :
    ‖(Complex.sin (π * (ζ - Complex.I * t)))⁻¹‖ ≤ 2 / σ * Real.exp (-(π * |ζ.im - t|)) := by
  have h := norm_sin_arg_ge t hσ hσ1 hx
  have hpos : 0 < σ * (Real.exp (π * |ζ.im - t|) / 2) := by positivity
  rw [norm_inv]
  calc ‖Complex.sin (π * (ζ - Complex.I * t))‖⁻¹ ≤ (σ * (Real.exp (π * |ζ.im - t|) / 2))⁻¹ :=
        inv_anti₀ hpos h
    _ = 2 / σ * Real.exp (-(π * |ζ.im - t|)) := by
        rw [Real.exp_neg]; field_simp

/-- Integrability of `(log (1+t²) + C) e^{-π|t|}`. -/
lemma integrable_exp_neg_abs' {c : ℝ} (hc : 0 < c) :
    Integrable (fun v : ℝ => Real.exp (-c * |v|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · have := integrableOn_exp_mul_Iic hc 0
    refine this.congr_fun (fun v hv => ?_) measurableSet_Iic
    simp only [mem_Iic] at hv
    rw [abs_of_nonpos hv]; ring_nf
  · have := integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
    refine this.congr_fun (fun v hv => ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp hv)]

lemma log_one_add_sq_le (t : ℝ) : Real.log (1 + t ^ 2) ≤ 2 * |t| := by
  have h0 : 0 < 1 + t ^ 2 := by positivity
  rw [Real.log_le_iff_le_exp h0]
  have := Real.quadratic_le_exp_of_nonneg (x := 2 * |t|) (by positivity)
  nlinarith [sq_abs t, abs_nonneg t]

lemma integrable_log_weight {C : ℝ} (hC : 0 ≤ C) :
    Integrable (fun t : ℝ => (Real.log (1 + t ^ 2) + C) * Real.exp (-(π * |t|))) := by
  have hint := (integrable_exp_neg_abs' (c := π / 2) (by positivity)).const_mul (2 + C)
  refine Integrable.mono' hint ?_ (Eventually.of_forall fun t => ?_)
  · have : Continuous fun t : ℝ => (Real.log (1 + t ^ 2) + C) * Real.exp (-(π * |t|)) := by
      have : Continuous fun t : ℝ => Real.log (1 + t ^ 2) :=
        Continuous.log (by fun_prop) (fun t => by positivity)
      fun_prop
    exact this.aestronglyMeasurable
  · have h0 : 0 ≤ Real.log (1 + t ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg t])
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 := log_one_add_sq_le t
    have h2 : (Real.log (1 + t ^ 2) + C) ≤ (2 + C) * Real.exp (|t|) := by
      have e : 1 + |t| ≤ Real.exp |t| := by linarith [Real.add_one_le_exp |t|]
      nlinarith [abs_nonneg t]
    calc (Real.log (1 + t ^ 2) + C) * Real.exp (-(π * |t|))
        ≤ (2 + C) * Real.exp |t| * Real.exp (-(π * |t|)) := by gcongr
      _ ≤ (2 + C) * Real.exp (-(π / 2) * |t|) := by
          rw [mul_assoc, ← Real.exp_add]
          gcongr
          nlinarith [Real.pi_gt_three, abs_nonneg t]

/-- The constant `C₀` in `|u_r(t)| ≤ log(1+t²) + C₀`. -/
noncomputable def C0 : ℝ := |Real.log (6 / π ^ 2)| / 2

lemma C0_nonneg : 0 ≤ C0 := by unfold C0; positivity

lemma abs_uR_le' (t : ℝ) : |uR t| ≤ Real.log (1 + t ^ 2) + 2 * C0 := by
  have := abs_uR_le t
  unfold C0
  linarith [abs_nonneg (Real.log (6 / π ^ 2))]

lemma sin_pi_ge {a x : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (h1 : a ≤ x) (h2 : x ≤ 1 - a) :
    Real.sin (π * a) ≤ Real.sin (π * x) := by
  have hpi := Real.pi_pos
  rcases le_total x (1 / 2) with hx | hx
  · apply Real.sin_le_sin_of_le_of_le_pi_div_two <;> nlinarith
  · have : Real.sin (π * x) = Real.sin (π * (1 - x)) := by
      rw [mul_sub, mul_one, Real.sin_pi_sub]
    rw [this]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two <;> nlinarith

lemma mem_strip_of_ball {ζ₀ ζ : ℂ} (h₀ : ζ₀ ∈ strip) (hζ : ζ ∈ ball ζ₀ (min ζ₀.re (1 - ζ₀.re) / 2)) :
    min ζ₀.re (1 - ζ₀.re) / 2 ≤ ζ.re ∧ ζ.re ≤ 1 - min ζ₀.re (1 - ζ₀.re) / 2 := by
  have hd : |ζ.re - ζ₀.re| < min ζ₀.re (1 - ζ₀.re) / 2 := by
    have := Complex.abs_re_le_norm (ζ - ζ₀)
    rw [mem_ball, dist_eq_norm] at hζ
    simp only [Complex.sub_re] at this
    linarith
  have hm1 : min ζ₀.re (1 - ζ₀.re) ≤ ζ₀.re := min_le_left _ _
  have hm2 : min ζ₀.re (1 - ζ₀.re) ≤ 1 - ζ₀.re := min_le_right _ _
  rw [abs_lt] at hd
  constructor <;> linarith [h₀.1, h₀.2]

lemma differentiableOn_outerH : DifferentiableOn ℂ outerH strip := by
  refine differentiableOn_integral_param (μ := volume)
    (Φ := fun w t => (uR t : ℂ) / Complex.sin (π * (w - Complex.I * t))) isOpen_strip ?_ ?_ ?_
  · intro w hw
    have : Continuous fun t : ℝ => (uR t : ℂ) / Complex.sin (π * (w - Complex.I * t)) := by
      refine Continuous.div (Complex.continuous_ofReal.comp continuous_uR) (by fun_prop) ?_
      exact fun t => sin_arg_ne_zero t hw
    exact this.aestronglyMeasurable
  · refine Eventually.of_forall fun t w hw => ?_
    have hne := sin_arg_ne_zero t hw
    exact ((differentiableAt_const (uR t : ℂ)).div
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => Complex.sin (π * (w - Complex.I * t))) w)
      hne).differentiableWithinAt
  · intro w₀ hw₀
    set a : ℝ := min w₀.re (1 - w₀.re) / 2 with ha
    have hapos : 0 < a := by
      have := hw₀.1; have := hw₀.2
      rw [ha]; have := lt_min hw₀.1 (by linarith [hw₀.2] : 0 < 1 - w₀.re); linarith
    have ha2 : a ≤ 1 / 2 := by
      have := min_le_left w₀.re (1 - w₀.re)
      have := min_le_right w₀.re (1 - w₀.re)
      rw [ha]; linarith
    set σ : ℝ := Real.sin (π * a) with hσ
    have hσpos : 0 < σ := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    have hσ1 : σ ≤ 1 := Real.sin_le_one _
    refine ⟨min a 1, lt_min hapos one_pos, fun t => (Real.log (1 + t ^ 2) + 2 * C0) * (2 / σ) *
      Real.exp (π * (|w₀.im| + 1)) * Real.exp (-(π * |t|)), ?_, ?_⟩
    · have := (integrable_log_weight (C := 2 * C0) (by have := C0_nonneg; positivity)).const_mul
        (2 / σ * Real.exp (π * (|w₀.im| + 1)))
      refine this.congr (Eventually.of_forall fun t => ?_)
      simp only
      ring
    · refine Eventually.of_forall fun t w hw => ?_
      have hwb : w ∈ ball w₀ a := ball_subset_ball (min_le_left _ _) hw
      obtain ⟨hl, hr⟩ := mem_strip_of_ball hw₀ hwb
      have hσle : σ ≤ Real.sin (π * w.re) := sin_pi_ge hapos ha2 hl hr
      have hk := kernel_norm_le (ζ := w) t hσpos hσ1 hσle
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
      simp only
      have hu : ‖(uR t : ℂ)‖ ≤ Real.log (1 + t ^ 2) + 2 * C0 := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_uR_le' t
      rw [norm_div, div_eq_mul_inv, ← norm_inv]
      have h1 : ‖(Complex.sin (π * (w - Complex.I * t)))⁻¹‖ ≤
          2 / σ * (Real.exp (π * (|w₀.im| + 1)) * Real.exp (-(π * |t|))) :=
        hk.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
      calc ‖(uR t : ℂ)‖ * ‖(Complex.sin (π * (w - Complex.I * t)))⁻¹‖
          ≤ (Real.log (1 + t ^ 2) + 2 * C0) * (2 / σ * (Real.exp (π * (|w₀.im| + 1)) *
              Real.exp (-(π * |t|)))) :=
            mul_le_mul hu h1 (norm_nonneg _) ((norm_nonneg _).trans hu)
        _ = _ := by ring

lemma sin_pi_re_pos {ζ : ℂ} (hζ : ζ ∈ strip) : 0 < Real.sin (π * ζ.re) :=
  Real.sin_pos_of_pos_of_lt_pi (by have := hζ.1; positivity) (by have := hζ.2; nlinarith [Real.pi_pos])

lemma continuous_integrand {ζ : ℂ} (hζ : ζ ∈ strip) :
    Continuous fun t : ℝ => (uR t : ℂ) / Complex.sin (π * (ζ - Complex.I * t)) := by
  refine Continuous.div (Complex.continuous_ofReal.comp continuous_uR) (by fun_prop) ?_
  exact fun t => sin_arg_ne_zero t hζ

lemma integrable_integrand {ζ : ℂ} (hζ : ζ ∈ strip) :
    Integrable fun t : ℝ => (uR t : ℂ) / Complex.sin (π * (ζ - Complex.I * t)) := by
  set σ : ℝ := Real.sin (π * ζ.re) with hσ
  have hσpos : 0 < σ := sin_pi_re_pos hζ
  have hσ1 : σ ≤ 1 := Real.sin_le_one _
  have hint := (integrable_log_weight (C := 2 * C0) (by have := C0_nonneg; positivity)).const_mul
    (2 / σ * Real.exp (π * |ζ.im|))
  refine Integrable.mono' hint (continuous_integrand hζ).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hk := kernel_norm_le (ζ := ζ) t hσpos hσ1 le_rfl
  have hexp : Real.exp (-(π * |ζ.im - t|)) ≤ Real.exp (π * |ζ.im|) * Real.exp (-(π * |t|)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : |t| ≤ |ζ.im - t| + |ζ.im| := by
      calc |t| = |ζ.im - (ζ.im - t)| := by ring_nf
        _ ≤ |ζ.im| + |ζ.im - t| := abs_sub _ _
        _ = _ := by ring
    nlinarith [Real.pi_pos]
  have hu : ‖(uR t : ℂ)‖ ≤ Real.log (1 + t ^ 2) + 2 * C0 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_uR_le' t
  rw [norm_div, div_eq_mul_inv, ← norm_inv]
  have h1 : ‖(Complex.sin (π * (ζ - Complex.I * t)))⁻¹‖ ≤
      2 / σ * (Real.exp (π * |ζ.im|) * Real.exp (-(π * |t|))) :=
    hk.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  calc ‖(uR t : ℂ)‖ * ‖(Complex.sin (π * (ζ - Complex.I * t)))⁻¹‖
      ≤ (Real.log (1 + t ^ 2) + 2 * C0) * (2 / σ * (Real.exp (π * |ζ.im|) *
          Real.exp (-(π * |t|)))) :=
        mul_le_mul hu h1 (norm_nonneg _) ((norm_nonneg _).trans hu)
    _ = _ := by ring

/-- Real symmetry of the strip integral: `h(ζ̄) = conj h(ζ)`. -/
lemma outerH_conj (ζ : ℂ) : outerH (starRingEnd ℂ ζ) = starRingEnd ℂ (outerH ζ) := by
  unfold outerH
  rw [← integral_conj]
  set g : ℝ → ℂ := fun t => (starRingEnd ℂ) ((uR t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))) with hg
  calc ∫ t : ℝ, (uR t : ℂ) / Complex.sin (π * (starRingEnd ℂ ζ - Complex.I * t))
      = ∫ t : ℝ, g (-t) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only [hg, uR_neg, Complex.ofReal_neg, map_div₀, Complex.conj_ofReal, mul_neg]
        rw [← Complex.sin_conj]
        congr 2
        simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
    _ = ∫ t : ℝ, g t := integral_neg_eq_self g volume

/-- `h(1 - ζ) = h(ζ)`. -/
lemma outerH_one_sub (ζ : ℂ) : outerH (1 - ζ) = outerH ζ := by
  unfold outerH
  set g : ℝ → ℂ := fun t => (uR t : ℂ) / Complex.sin (π * (ζ - Complex.I * t)) with hg
  calc ∫ t : ℝ, (uR t : ℂ) / Complex.sin (π * (1 - ζ - Complex.I * t))
      = ∫ t : ℝ, g (-t) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only [hg, uR_neg, Complex.ofReal_neg, mul_neg]
        congr 1
        have : (π : ℂ) * (1 - ζ - Complex.I * t) = π - π * (ζ - Complex.I * (-t : ℝ)) := by
          push_cast; ring
        rw [this, Complex.sin_pi_sub]
        congr 2
        push_cast
        ring
    _ = ∫ t : ℝ, g t := integral_neg_eq_self g volume

end FormalResearch.SignUncertainty.CtOuter
