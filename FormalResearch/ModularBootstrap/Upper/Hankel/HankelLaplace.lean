module

public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelDef

/-!
# Rotated Laplace form of `K₀` and the `1/|w|` remainder bound

Source: `CFT/modular_bootstrap/paper/edge_transform_sd.tex`, proof of Lemma `SD_G`
("the standard uniform large-argument Hankel estimate"); plan item A3.

For `Re w > 0`,
`K₀(w) = e^{-w} (2w)^{-1/2} R(w)`, `R(w) = ∫₀^∞ e^{-t} t^{-1/2} (1 + t/(2w))^{-1/2} dt`
(`besselK0_eq`), proved by the substitution `t = ρ (cosh s - 1)` for real `w = ρ` and the identity
theorem (both sides are holomorphic on `Re w > 0`).  On the closed sector `Re w ≥ 0` the factor
`(1 + t/(2w))^{-1/2}` has modulus `≤ 1` and distance `≤ t/(2|w|)` from `1`, whence
`‖R(w) - √π‖ ≤ √π / (4 |w|)` (`norm_hankelR_sub_le`) and `‖R(w)‖ ≤ √π` (`norm_hankelR_le`),
uniformly up to the imaginary axis.  No contour rotation is needed.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Hankel

/-! ### The factor `(1 + q)^{-1/2}` for `Re q ≥ 0` -/

lemma half_pow_aux {q : ℂ} (hq : 0 ≤ q.re) :
    ‖(1 + q) ^ (-(1 / 2 : ℂ))‖ ≤ 1 ∧ ‖(1 + q) ^ (-(1 / 2 : ℂ)) - 1‖ ≤ ‖q‖ := by
  set u : ℂ := 1 + q with hu
  have hu1 : 1 ≤ u.re := by simp [hu]; linarith
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu1; simp at hu1; linarith
  have hun : 1 ≤ ‖u‖ := hu1.trans (Complex.re_le_norm u)
  set p : ℂ := u ^ ((2 : ℂ)⁻¹) with hp
  have hneg : u ^ (-(1 / 2 : ℂ)) = p⁻¹ := by
    rw [show -(1 / 2 : ℂ) = -((2 : ℂ)⁻¹) by norm_num, Complex.cpow_neg]
  have hp2 : p ^ 2 = u := Complex.cpow_ofNat_inv_pow u 2
  have hpn : 1 ≤ ‖p‖ := by
    by_contra hlt
    have hlt := not_le.mp hlt
    have h1 : ‖p‖ ^ 2 = ‖u‖ := by rw [← norm_pow, hp2]
    nlinarith [norm_nonneg p]
  have hpre : 0 ≤ p.re := by
    rw [hp, Complex.cpow_def_of_ne_zero hu0, Complex.exp_re]
    refine mul_nonneg (Real.exp_pos _).le ?_
    have harg : |u.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith))
    have him : (Complex.log u * (2 : ℂ)⁻¹).im = u.arg / 2 := by
      simp [Complex.log_im]
      ring
    rw [him]
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [abs_lt.mp harg]
  have h1p : 1 ≤ ‖1 + p‖ := by
    have : (1 + p).re = 1 + p.re := by simp
    exact (by linarith : 1 ≤ (1 + p).re).trans (Complex.re_le_norm _)
  have hfac : (1 - p) * (1 + p) = -q := by
    have : (1 - p) * (1 + p) = 1 - p ^ 2 := by ring
    rw [this, hp2, hu]; ring
  have h1m : ‖1 - p‖ ≤ ‖q‖ := by
    have := congrArg norm hfac
    rw [norm_mul, norm_neg] at this
    nlinarith [norm_nonneg (1 - p)]
  rw [hneg]
  constructor
  · rw [norm_inv]; exact inv_le_one_of_one_le₀ hpn
  · have hp0 : p ≠ 0 := by
      intro h; rw [h] at hpn; simp at hpn; linarith
    have : p⁻¹ - 1 = (1 - p) / p := by field_simp
    rw [this, norm_div]
    exact (div_le_self (norm_nonneg _) hpn).trans h1m

/-! ### The integral `R(w)` -/

lemma cast_main_integrand {t : ℝ} (ht : 0 ≤ t) :
    Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) =
      ((Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_cpow ht]
  push_cast
  rfl

/-- `R(w) = ∫₀^∞ e^{-t} t^{-1/2} (1 + t/(2w))^{-1/2} dt`. -/
noncomputable def hankelR (w : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
    (1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ))

lemma re_div_two_mul_nonneg {w : ℂ} (hw : 0 ≤ w.re) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ((t : ℂ) / (2 * w)).re := by
  have : (t : ℂ) / (2 * w) = ((t / 2 : ℝ) : ℂ) * w⁻¹ := by push_cast; field_simp
  rw [this, Complex.re_ofReal_mul, Complex.inv_re]
  exact mul_nonneg (by positivity) (div_nonneg hw (Complex.normSq_nonneg _))

lemma norm_cpow_neg_half_ofReal {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (-(1 / 2 : ℂ))‖ = t ^ (-(1 / 2 : ℝ)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

lemma integrableOn_gamma_half :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
  have := Real.GammaIntegral_convergent (s := 1 / 2) (by norm_num)
  convert this using 3
  norm_num

lemma integrableOn_gamma_three_half :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (1 / 2 : ℝ)) (Ioi 0) := by
  have := Real.GammaIntegral_convergent (s := 3 / 2) (by norm_num)
  convert this using 3
  norm_num

lemma integral_gamma_half : ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) = √π := by
  have := Real.Gamma_eq_integral (s := 1 / 2) (by norm_num)
  rw [Real.Gamma_one_half_eq] at this
  rw [this]
  congr 1; ext t; norm_num

lemma integral_gamma_three_half :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (1 / 2 : ℝ) = √π / 2 := by
  have h := Real.Gamma_eq_integral (s := 3 / 2) (by norm_num)
  have h2 : Real.Gamma (3 / 2) = (1 / 2) * Real.Gamma (1 / 2) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  rw [h2, Real.Gamma_one_half_eq] at h
  have : ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (1 / 2 : ℝ) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ ((3 / 2 : ℝ) - 1) := by
    congr 1; ext t; norm_num
  rw [this, ← h]; ring

lemma hankelR_integrand_norm_le {w : ℂ} (hw : 0 ≤ w.re) {t : ℝ} (ht : 0 < t) :
    ‖Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) * (1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ))‖
      ≤ Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) := by
  rw [norm_mul, norm_mul, Complex.norm_exp, norm_cpow_neg_half_ofReal ht]
  have := (half_pow_aux (re_div_two_mul_nonneg hw ht.le)).1
  simp only [neg_re, ofReal_re]
  calc Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * ‖(1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ))‖
      ≤ Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := mul_one _

lemma integrableOn_hankelR_integrand {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ))) (Ioi 0) := by
  refine Integrable.mono' integrableOn_gamma_half ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hankelR_integrand_norm_le hw.le ht

/-- `‖R(w)‖ ≤ √π` on `Re w ≥ 0`. -/
theorem norm_hankelR_le {w : ℂ} (hw : 0 ≤ w.re) : ‖hankelR w‖ ≤ √π := by
  unfold hankelR
  rw [← integral_gamma_half]
  refine norm_integral_le_of_norm_le integrableOn_gamma_half ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hankelR_integrand_norm_le hw ht

/-- The main term: `∫₀^∞ e^{-t} t^{-1/2} dt = √π`. -/
lemma integral_main_term :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) = (√π : ℝ) := by
  have : ∀ t ∈ Ioi (0 : ℝ), Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) =
      ((Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := fun t ht => cast_main_integrand (le_of_lt ht)
  rw [setIntegral_congr_fun measurableSet_Ioi this, integral_complex_ofReal, integral_gamma_half]

/-- `‖R(w) - √π‖ ≤ √π/(4|w|)` uniformly on the closed sector `Re w ≥ 0`, `w ≠ 0`. -/
theorem norm_hankelR_sub_le {w : ℂ} (hw : 0 ≤ w.re) (hw0 : w ≠ 0) :
    ‖hankelR w - (√π : ℝ)‖ ≤ √π / (4 * ‖w‖) := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ))) (Ioi 0) := by
    have := integrableOn_gamma_half.ofReal (𝕜 := ℂ)
    exact this.congr_fun (fun t ht => (cast_main_integrand (le_of_lt ht)).symm) measurableSet_Ioi
  have hint2 : IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ))) (Ioi 0) := by
    refine Integrable.mono' integrableOn_gamma_half ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hankelR_integrand_norm_le hw ht
  have hdiff : hankelR w - (√π : ℝ) = ∫ t in Ioi (0 : ℝ), (Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ)) - Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ))) := by
    rw [integral_sub hint2 hint, integral_main_term]; rfl
  rw [hdiff]
  have hg : IntegrableOn (fun t : ℝ => (1 / (2 * ‖w‖)) * (Real.exp (-t) * t ^ (1 / 2 : ℝ))) (Ioi 0) :=
    integrableOn_gamma_three_half.const_mul _
  calc _ ≤ ∫ t in Ioi (0 : ℝ), (1 / (2 * ‖w‖)) * (Real.exp (-t) * t ^ (1 / 2 : ℝ)) := by
        refine norm_integral_le_of_norm_le hg ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0 : ℝ) < t := ht
        have hb := (half_pow_aux (re_div_two_mul_nonneg hw ht0.le)).2
        have hq : ‖(t : ℂ) / (2 * w)‖ = t / (2 * ‖w‖) := by
          rw [norm_div, Complex.norm_real, norm_mul, Real.norm_of_nonneg ht0.le]
          simp
        rw [hq] at hb
        have : Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
            (1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ)) - Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ))
            = Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
              ((1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ)) - 1) := by ring
        rw [this, norm_mul, norm_mul, Complex.norm_exp, norm_cpow_neg_half_ofReal ht0]
        simp only [neg_re, ofReal_re]
        have e1 : t ^ (1 / 2 : ℝ) = t ^ (-(1 / 2 : ℝ)) * t := by
          rw [← Real.rpow_add_one ht0.ne']; norm_num
        calc Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) *
              ‖(1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ)) - 1‖
            ≤ Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * (t / (2 * ‖w‖)) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = (1 / (2 * ‖w‖)) * (Real.exp (-t) * t ^ (1 / 2 : ℝ)) := by
              rw [e1]; field_simp
    _ = √π / (4 * ‖w‖) := by
        rw [integral_const_mul, integral_gamma_three_half]
        field_simp
        ring

/-! ### Holomorphy of `R` on `Re w > 0` -/

lemma norm_half_pow_sub_one_le {q : ℂ} (hq : 0 ≤ q.re) :
    ‖(1 + q) ^ (-(1 / 2 : ℂ) - 1)‖ ≤ 1 := by
  have hu1 : 1 ≤ (1 + q).re := by simp; linarith
  have hu0 : (1 + q) ≠ 0 := by
    intro h; rw [h] at hu1; simp at hu1; linarith
  have hun : 1 ≤ ‖1 + q‖ := hu1.trans (Complex.re_le_norm _)
  rw [Complex.norm_cpow_of_ne_zero hu0]
  have : (-(1 / 2 : ℂ) - 1).im = 0 := by simp
  rw [this, mul_zero, Real.exp_zero, div_one]
  exact Real.rpow_le_one_of_one_le_of_nonpos hun (by simp; norm_num)

/-- The `w`-derivative of the integrand of `hankelR`. -/
noncomputable def hankelRDeriv (w : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
    ((-(1 / 2 : ℂ)) * (1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ) - 1) * ((t : ℂ) / 2 * (-(w ^ 2)⁻¹)))

lemma hasDerivAt_hankelR_integrand {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun w : ℂ => Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ))) (hankelRDeriv w t) w := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hq : HasDerivAt (fun w : ℂ => (1 : ℂ) + (t : ℂ) / 2 * w⁻¹) ((t : ℂ) / 2 * (-(w ^ 2)⁻¹)) w :=
    ((hasDerivAt_inv hw0).const_mul _).const_add 1
  have hslit : (1 : ℂ) + (t : ℂ) / 2 * w⁻¹ ∈ Complex.slitPlane := by
    have := re_div_two_mul_nonneg hw.le ht
    have e : (t : ℂ) / (2 * w) = (t : ℂ) / 2 * w⁻¹ := by ring
    rw [e] at this
    rw [Complex.mem_slitPlane_iff]
    left; simp only [add_re, one_re]; linarith
  have hc := (hq.cpow_const (c := -(1 / 2 : ℂ)) hslit).const_mul
    (Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)))
  have e2 : (fun w : ℂ => Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ))) = fun w : ℂ => Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (1 + (t : ℂ) / 2 * w⁻¹) ^ (-(1 / 2 : ℂ)) := by
    funext w; congr 3; ring
  rw [e2]
  have e3 : (1 : ℂ) + (t : ℂ) / (2 * w) = 1 + (t : ℂ) / 2 * w⁻¹ := by ring
  unfold hankelRDeriv
  rw [e3]
  exact hc

lemma norm_hankelRDeriv_le {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hw : ρ / 2 ≤ w.re) {t : ℝ} (ht : 0 < t) :
    ‖hankelRDeriv w t‖ ≤ (1 / (ρ / 2) ^ 2) / 4 * (Real.exp (-t) * t ^ (1 / 2 : ℝ)) := by
  have hwre : 0 ≤ w.re := by linarith
  have hwn : ρ / 2 ≤ ‖w‖ := hw.trans (Complex.re_le_norm w)
  have h1 := norm_half_pow_sub_one_le (re_div_two_mul_nonneg hwre ht.le)
  unfold hankelRDeriv
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp, norm_cpow_neg_half_ofReal ht]
  simp only [neg_re, ofReal_re, norm_neg, norm_inv, norm_pow, norm_div, Complex.norm_real,
    Real.norm_of_nonneg ht.le]
  have e1 : t ^ (1 / 2 : ℝ) = t ^ (-(1 / 2 : ℝ)) * t := by
    rw [← Real.rpow_add_one ht.ne']; norm_num
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_one, h3]
  have hρ2 : 0 < ρ / 2 := by positivity
  have h4 : (‖w‖ ^ 2)⁻¹ ≤ (1 / (ρ / 2) ^ 2) := by
    rw [one_div]
    apply inv_anti₀ (by positivity)
    nlinarith
  have hb := Real.exp_pos (-t)
  have hb2 : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  calc Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * (1 / 2 * ‖(1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ) - 1)‖ *
        (t / 2 * (‖w‖ ^ 2)⁻¹))
      ≤ Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * (1 / 2 * 1 * (t / 2 * (1 / (ρ / 2) ^ 2))) := by
        gcongr
    _ = (1 / (ρ / 2) ^ 2) / 4 * (Real.exp (-t) * (t ^ (-(1 / 2 : ℝ)) * t)) := by ring
    _ = _ := by rw [e1]

lemma hasDerivAt_hankelR {w₀ : ℂ} (hw₀ : 0 < w₀.re) :
    HasDerivAt hankelR (∫ t in Ioi (0 : ℝ), hankelRDeriv w₀ t) w₀ := by
  set ρ := w₀.re with hρ
  have hρ2 : 0 < ρ / 2 := by positivity
  have hs : Metric.ball w₀ (ρ / 2) ∈ 𝓝 w₀ := Metric.ball_mem_nhds _ hρ2
  have hball : ∀ w ∈ Metric.ball w₀ (ρ / 2), ρ / 2 ≤ w.re := by
    intro w hw
    have := Complex.abs_re_le_norm (w - w₀)
    have h2 : ‖w - w₀‖ < ρ / 2 := by simpa [Complex.dist_eq] using hw
    have h3 : (w - w₀).re = w.re - ρ := by simp [hρ]
    rw [h3] at this
    have := (abs_le.mp this).1
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (w : ℂ) (t : ℝ) => Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (1 + (t : ℂ) / (2 * w)) ^ (-(1 / 2 : ℂ)))
    (F' := hankelRDeriv)
    (bound := fun t => (1 / (ρ / 2) ^ 2) / 4 * (Real.exp (-t) * t ^ (1 / 2 : ℝ)))
    (x₀ := w₀) hs
    (Filter.Eventually.of_forall fun w => by
      refine Measurable.aestronglyMeasurable ?_
      fun_prop)
    (integrableOn_hankelR_integrand hw₀)
    (by
      refine Measurable.aestronglyMeasurable ?_
      unfold hankelRDeriv
      fun_prop)
    ?_ ?_ ?_
  · exact key.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    exact norm_hankelRDeriv_le hw₀ (hball w hw) ht
  · exact integrableOn_gamma_three_half.const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have : 0 < w.re := by linarith [hball w hw]
    exact hasDerivAt_hankelR_integrand this (le_of_lt ht)

lemma differentiableOn_hankelR : DifferentiableOn ℂ hankelR {w : ℂ | 0 < w.re} := fun _ hw =>
  (hasDerivAt_hankelR hw).differentiableAt.differentiableWithinAt

/-! ### The real case `w = ρ > 0`: substitution `t = ρ (cosh s - 1)` -/

lemma cpow_neg_half_ofReal {y : ℝ} (hy : 0 ≤ y) : (y : ℂ) ^ (-(1 / 2 : ℂ)) = (((√y)⁻¹ : ℝ) : ℂ) := by
  have := Complex.ofReal_cpow hy (-(1 / 2 : ℝ))
  push_cast at this
  rw [← this, Real.rpow_neg hy, Real.sqrt_eq_rpow]

lemma subst_real {ρ x : ℝ} (hρ : 0 < ρ) (hx : 0 < x) :
    ρ * Real.sinh x * ((√(ρ * (Real.cosh x - 1)))⁻¹ *
      (√(1 + ρ * (Real.cosh x - 1) / (2 * ρ)))⁻¹) = √(2 * ρ) := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hc : 1 < Real.cosh x := Real.one_lt_cosh.mpr hx.ne'
  have hcs : Real.cosh x ^ 2 = Real.sinh x ^ 2 + 1 := Real.cosh_sq x
  have hD : √(ρ * (Real.cosh x - 1)) * √(1 + ρ * (Real.cosh x - 1) / (2 * ρ)) =
      Real.sinh x * √(ρ / 2) := by
    rw [← Real.sqrt_mul (by nlinarith)]
    have : ρ * (Real.cosh x - 1) * (1 + ρ * (Real.cosh x - 1) / (2 * ρ)) =
        Real.sinh x ^ 2 * (ρ / 2) := by
      field_simp
      nlinarith
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs.le]
  have hρ2 : √(2 * ρ) * √(ρ / 2) = ρ := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 2 * ρ * (ρ / 2) = ρ ^ 2 by ring, Real.sqrt_sq hρ.le]
  have hpos : 0 < √(ρ / 2) := Real.sqrt_pos.mpr (by positivity)
  rw [← mul_inv, hD, mul_inv_eq_iff_eq_mul₀ (by positivity)]
  linear_combination (-(Real.sinh x)) * hρ2

lemma image_cosh_sub_one {ρ : ℝ} (hρ : 0 < ρ) :
    (fun s : ℝ => ρ * (Real.cosh s - 1)) '' Ioi 0 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    have := Real.one_lt_cosh.mpr (ne_of_gt (mem_Ioi.mp hs))
    exact mul_pos hρ (by linarith)
  · intro hy
    have hy' : 0 < y := hy
    refine ⟨Real.arcosh (1 + y / ρ), ?_, ?_⟩
    · have h1 : 1 < 1 + y / ρ := by have := div_pos hy' hρ; linarith
      exact Real.arcosh_pos h1
    · have h1 : 1 ≤ 1 + y / ρ := by have := div_pos hy' hρ; linarith
      simp only
      rw [Real.cosh_arcosh h1]
      field_simp
      ring

theorem hankelR_real {ρ : ℝ} (hρ : 0 < ρ) :
    hankelR (ρ : ℂ) = ((√(2 * ρ) * Real.exp ρ : ℝ) : ℂ) * besselK0 (ρ : ℂ) := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun s : ℝ => ρ * (Real.cosh s - 1)) (ρ * Real.sinh x) (Ioi 0) x := by
    intro x _
    have := ((Real.hasDerivAt_cosh x).sub_const 1).const_mul ρ
    exact this.hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => ρ * (Real.cosh s - 1)) (Ioi 0) := by
    intro a ha b hb hab
    have hab' : Real.cosh a = Real.cosh b := by
      have := mul_left_cancel₀ hρ.ne' hab
      linarith
    have := Real.cosh_le_cosh.mp hab'.le
    have h2 := Real.cosh_le_cosh.mp hab'.ge
    have ha0 : 0 < a := ha
    have hb0 : 0 < b := hb
    rw [abs_of_pos ha0, abs_of_pos hb0] at this h2
    linarith
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun t : ℝ => Complex.exp (-(t : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (1 + (t : ℂ) / (2 * (ρ : ℂ))) ^ (-(1 / 2 : ℂ)))
  rw [image_cosh_sub_one hρ] at key
  unfold hankelR
  rw [key]
  unfold besselK0
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx0
  have hc : 1 < Real.cosh x := Real.one_lt_cosh.mpr hx0.ne'
  have hA : 0 ≤ ρ * (Real.cosh x - 1) := by nlinarith
  have hB : 0 ≤ 1 + ρ * (Real.cosh x - 1) / (2 * ρ) := by positivity
  rw [abs_of_pos (by positivity : 0 < ρ * Real.sinh x)]
  have e1 : (1 : ℂ) + ((ρ * (Real.cosh x - 1) : ℝ) : ℂ) / (2 * (ρ : ℂ)) =
      ((1 + ρ * (Real.cosh x - 1) / (2 * ρ) : ℝ) : ℂ) := by push_cast; ring
  simp only [Complex.real_smul]
  rw [e1, cpow_neg_half_ofReal hA, cpow_neg_half_ofReal hB]
  have e2 : Complex.exp (-((ρ * (Real.cosh x - 1) : ℝ) : ℂ)) =
      Complex.exp ρ * Complex.exp (-(ρ : ℂ) * (Real.cosh x : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e2]
  have := subst_real hρ hx0
  have e3 : ((ρ * Real.sinh x : ℝ) : ℂ) * (Complex.exp ρ * Complex.exp (-(ρ : ℂ) * (Real.cosh x : ℂ)) *
      (((√(ρ * (Real.cosh x - 1)))⁻¹ : ℝ) : ℂ) *
      (((√(1 + ρ * (Real.cosh x - 1) / (2 * ρ)))⁻¹ : ℝ) : ℂ)) =
      (((ρ * Real.sinh x * ((√(ρ * (Real.cosh x - 1)))⁻¹ *
      (√(1 + ρ * (Real.cosh x - 1) / (2 * ρ)))⁻¹) : ℝ) : ℂ)) *
      (Complex.exp ρ * Complex.exp (-(ρ : ℂ) * (Real.cosh x : ℂ))) := by
    push_cast; ring
  rw [e3, this]
  push_cast
  ring

/-! ### Identity theorem: `K₀(w) = e^{-w} (2w)^{-1/2} R(w)` on `Re w > 0` -/

theorem besselK0_eq {w : ℂ} (hw : 0 < w.re) :
    besselK0 w = Complex.exp (-w) * (2 * w) ^ (-(1 / 2 : ℂ)) * hankelR w := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ besselK0 {w : ℂ | 0 < w.re} :=
    differentiableOn_besselK0.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => Complex.exp (-w) * (2 * w) ^ (-(1 / 2 : ℂ)) * hankelR w)
      {w : ℂ | 0 < w.re} := by
    refine DifferentiableOn.analyticOnNhd ?_ hU
    refine (DifferentiableOn.mul (DifferentiableOn.mul (by fun_prop) ?_) differentiableOn_hankelR)
    intro z hz
    have hz' : (2 * z) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; simp; exact hz
    exact ((differentiableAt_id.const_mul 2).cpow (differentiableAt_const _) hz').differentiableWithinAt
  have hpre : IsPreconnected {w : ℂ | 0 < w.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hreal : ∀ ρ : ℝ, 0 < ρ → besselK0 (ρ : ℂ) =
      Complex.exp (-(ρ : ℂ)) * (2 * (ρ : ℂ)) ^ (-(1 / 2 : ℂ)) * hankelR (ρ : ℂ) := by
    intro ρ hρ
    rw [hankelR_real hρ]
    have e : (2 * (ρ : ℂ)) = ((2 * ρ : ℝ) : ℂ) := by push_cast; ring
    rw [e, cpow_neg_half_ofReal (by positivity)]
    have hq : 0 < √(2 * ρ) := Real.sqrt_pos.mpr (by positivity)
    have hq' : ((√(2 * ρ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have h1 : Complex.exp (-(ρ : ℂ)) * Complex.exp (ρ : ℂ) = 1 := by rw [← Complex.exp_add]; simp
    calc besselK0 (ρ : ℂ) = (Complex.exp (-(ρ : ℂ)) * Complex.exp (ρ : ℂ)) *
          ((((√(2 * ρ) : ℝ) : ℂ))⁻¹ * (((√(2 * ρ) : ℝ) : ℂ))) * besselK0 (ρ : ℂ) := by
          rw [h1, inv_mul_cancel₀ hq']; ring
      _ = _ := by push_cast; ring
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), besselK0 z =
      Complex.exp (-z) * (2 * z) ^ (-(1 / 2 : ℂ)) * hankelR z := by
    rw [frequently_nhdsWithin_iff, Filter.frequently_iff]
    intro U hU'
    obtain ⟨r, hr_pos, hrU⟩ := Metric.mem_nhds_iff.mp hU'
    refine ⟨((1 + r / 2 : ℝ) : ℂ), hrU ?_, ?_, ?_⟩
    · simp only [Metric.mem_ball, Complex.dist_eq]
      rw [show (((1 + r / 2 : ℝ) : ℂ) - 1) = ((r / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      linarith
    · exact hreal _ (by positivity)
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hpre (by simp : (1 : ℂ) ∈ {w : ℂ | 0 < w.re}) hfreq hw

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.besselK0_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselK0_eq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.norm_hankelR_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hankelR_sub_le

end FormalResearch.ModularBootstrap.Upper.Hankel
