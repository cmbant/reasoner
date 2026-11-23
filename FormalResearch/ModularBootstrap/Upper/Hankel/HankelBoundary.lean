module

public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelAsym
public import FormalResearch.ModularBootstrap.ComplexBessel.BesselI0Sector

/-!
# Boundary values of `H₀¹` on the positive real axis, and the relation to `J₀`

Source: `CFT/modular_bootstrap/paper/edge_transform_sd.tex`, proof of Lemma `SD_H`
(`H₀¹(-r + i0) = -H₀²(r)`, `H₀¹ + H₀² = 2 J₀`); plan item A3.

Rotating the Laplace contour `s ↦ s + i y`, `0 ≤ y ≤ π/2` (Cauchy on the rectangle
`[0, R] × [0, π/2]`) gives, for `Re z > 0` and `Im z > 0`,

`H₀¹(z) = hankelP z + hankelQ z`,
`hankelP z = (2/π) ∫₀^{π/2} e^{i z cos y} dy`, `hankelQ z = (2/(π i)) ∫₀^∞ e^{-z sinh t} dt`.

The right-hand side `hankelRay` is continuous on `Re z > 0` (in particular up to the positive real
axis), so it is the boundary value `H₀¹(x + i0)`, `x > 0`.  Since `hankelQ x` is purely imaginary on
`x > 0`, `hankelRay x + conj (hankelRay x) = 2 J₀(x)` (`hankelRay_add_conj`), the order-zero
Mehler–Sonine relation `Re H₀¹(x + i0) = J₀(x)`, where `J₀ = Complex.besselJ 0`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Hankel

/-- `hankelP z = (2/π) ∫₀^{π/2} e^{i z cos y} dy` (entire in `z`). -/
noncomputable def hankelP (z : ℂ) : ℂ :=
  (2 / (π : ℂ)) * ∫ y in (0 : ℝ)..(π / 2), Complex.exp (I * z * (Real.cos y : ℂ))

/-- `hankelQ z = (2/(π i)) ∫₀^∞ e^{-z sinh t} dt` (meaningful for `Re z > 0`). -/
noncomputable def hankelQ (z : ℂ) : ℂ :=
  (2 / ((π : ℂ) * I)) * ∫ t in Ioi (0 : ℝ), Complex.exp (-z * (Real.sinh t : ℂ))

/-- The boundary form `hankelP + hankelQ` of `H₀¹` on the first quadrant and the positive real axis. -/
noncomputable def hankelRay (z : ℂ) : ℂ := hankelP z + hankelQ z

/-! ### Integrability and continuity -/

lemma norm_exp_neg_mul_sinh {z : ℂ} (t : ℝ) :
    ‖Complex.exp (-z * (Real.sinh t : ℂ))‖ = Real.exp (-(z.re * Real.sinh t)) := by
  rw [Complex.norm_exp, Complex.re_mul_ofReal, neg_re]
  congr 1; ring

lemma integrableOn_exp_neg_mul_sinh {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * (Real.sinh t : ℂ))) (Ioi 0) := by
  have hint := integrableOn_exp_mul_Ioi (a := -z.re) (by linarith) 0
  refine Integrable.mono' hint ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (-z * (Real.sinh t : ℂ))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_exp_neg_mul_sinh]
    apply Real.exp_le_exp.mpr
    have : t ≤ Real.sinh t := Real.self_le_sinh_iff.mpr (le_of_lt ht)
    nlinarith

lemma continuous_hankelP : Continuous hankelP := by
  unfold hankelP
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  fun_prop

lemma continuousAt_hankelQ {z₀ : ℂ} (hz₀ : 0 < z₀.re) : ContinuousAt hankelQ z₀ := by
  unfold hankelQ
  refine continuousAt_const.mul ?_
  have hρ : 0 < z₀.re / 2 := by positivity
  refine continuousAt_of_dominated (μ := volume.restrict (Ioi (0 : ℝ)))
    (bound := fun t => Real.exp (-(z₀.re / 2) * t)) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun z =>
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (-z * (Real.sinh t : ℂ))).aestronglyMeasurable
  · have hnb : Metric.ball z₀ (z₀.re / 2) ∈ 𝓝 z₀ := Metric.ball_mem_nhds _ hρ
    filter_upwards [hnb] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hre : z₀.re / 2 ≤ z.re := by
      have := Complex.abs_re_le_norm (z - z₀)
      have h2 : ‖z - z₀‖ < z₀.re / 2 := by simpa [Complex.dist_eq] using hz
      have h3 : (z - z₀).re = z.re - z₀.re := by simp
      rw [h3] at this
      have := (abs_le.mp this).1
      linarith
    rw [norm_exp_neg_mul_sinh]
    apply Real.exp_le_exp.mpr
    have h1 : t ≤ Real.sinh t := Real.self_le_sinh_iff.mpr (le_of_lt ht)
    have h2 : z₀.re / 2 * t ≤ z.re * Real.sinh t :=
      mul_le_mul hre h1 (le_of_lt ht) (by linarith)
    linarith
  · exact integrableOn_exp_mul_Ioi (a := -(z₀.re / 2)) (by linarith) 0
  · exact Filter.Eventually.of_forall fun t => by fun_prop

/-! ### Cauchy on the rectangle `[0, R] × [0, π/2]` -/

lemma cosh_ofReal_add (R y : ℝ) :
    Complex.cosh ((R : ℂ) + (y : ℂ) * I) =
      (Real.cosh R * Real.cos y : ℝ) + I * ((Real.sinh R * Real.sin y : ℝ) : ℂ) := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

lemma re_I_mul_cosh {z : ℂ} (R y : ℝ) :
    (I * z * Complex.cosh ((R : ℂ) + (y : ℂ) * I)).re =
      -(z.im * (Real.cosh R * Real.cos y) + z.re * (Real.sinh R * Real.sin y)) := by
  rw [cosh_ofReal_add]
  generalize Real.cosh R * Real.cos y = a
  generalize Real.sinh R * Real.sin y = b
  simp
  ring

theorem hankel0_eq_ray {z : ℂ} (hre : 0 < z.re) (him : 0 < z.im) : hankel0 z = hankelRay z := by
  set f : ℂ → ℂ := fun s => Complex.exp (I * z * Complex.cosh s) with hf
  have hdiff : Differentiable ℂ f := by
    intro s; simp only [hf]; fun_prop
  have hrect : ∀ R : ℝ,
      (∫ x in (0 : ℝ)..R, f ((x : ℂ) + (0 : ℝ) * I)) -
        (∫ x in (0 : ℝ)..R, f ((x : ℂ) + ((π / 2 : ℝ) : ℂ) * I)) +
        I * (∫ y in (0 : ℝ)..(π / 2), f ((R : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in (0 : ℝ)..(π / 2), f ((0 : ℝ) + (y : ℂ) * I)) = 0 := by
    intro R
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f 0
      ((R : ℂ) + ((π / 2 : ℝ) : ℂ) * I) hdiff.differentiableOn
    have e1 : ((R : ℂ) + ((π / 2 : ℝ) : ℂ) * I).re = R := by simp
    have e2 : ((R : ℂ) + ((π / 2 : ℝ) : ℂ) * I).im = π / 2 := by simp
    rw [e1, e2] at h
    simpa only [Complex.zero_re, Complex.zero_im, smul_eq_mul, Complex.ofReal_zero] using h
  have hw : 0 < (-I * z).re := by rw [neg_I_mul_re]; exact him
  -- evaluation of `f` on the four sides
  have E1 : ∀ x : ℝ, f ((x : ℂ) + ((0 : ℝ) : ℂ) * I) =
      Complex.exp (-(-I * z) * (Real.cosh x : ℂ)) := by
    intro x
    simp only [hf, Complex.ofReal_zero, zero_mul, add_zero, ← Complex.ofReal_cosh]
    congr 1; ring
  have E2 : ∀ x : ℝ, f ((x : ℂ) + ((π / 2 : ℝ) : ℂ) * I) =
      Complex.exp (-z * (Real.sinh x : ℂ)) := by
    intro x
    simp only [hf]
    rw [cosh_ofReal_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    congr 1; push_cast; ring_nf; simp [Complex.I_sq]
  have E3 : ∀ y : ℝ, f (((0 : ℝ) : ℂ) + (y : ℂ) * I) = Complex.exp (I * z * (Real.cos y : ℂ)) := by
    intro y
    simp only [hf]
    rw [cosh_ofReal_add]
    simp
  have hB : Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Complex.exp (-(-I * z) * (Real.cosh x : ℂ)))
      atTop (𝓝 (besselK0 (-I * z))) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_exp_neg_mul_cosh hw) tendsto_id
  have hT : Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Complex.exp (-z * (Real.sinh x : ℂ)))
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), Complex.exp (-z * (Real.sinh t : ℂ)))) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_exp_neg_mul_sinh hre) tendsto_id
  have hF : Tendsto (fun R : ℝ => ∫ y in (0 : ℝ)..(π / 2), f ((R : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (a := 0) (b := π / 2) (l := atTop) (f := fun _ => (0 : ℂ))
      (F := fun (R : ℝ) (y : ℝ) => f ((R : ℂ) + (y : ℂ) * I)) (fun _ => 1) ?_ ?_ ?_ ?_
    · simpa using this
    · refine Filter.Eventually.of_forall fun R => ?_
      refine Continuous.aestronglyMeasurable ?_
      simp only [hf]; fun_prop
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hy' : y ∈ Ioc (0 : ℝ) (π / 2) := by
        rwa [Set.uIoc_of_le (by positivity)] at hy
      simp only [hf, Complex.norm_exp]
      rw [re_I_mul_cosh R y]
      apply Real.exp_le_one_iff.mpr
      have h1 := Real.cosh_pos R
      have h2 : 0 ≤ Real.cos y := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hy'.1, Real.pi_pos], hy'.2⟩
      have h3 : 0 ≤ Real.sinh R := Real.sinh_nonneg_iff.mpr hR
      have h4 : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy'.1.le
        (by linarith [hy'.2, Real.pi_pos])
      have := mul_nonneg him.le (mul_nonneg h1.le h2)
      have := mul_nonneg hre.le (mul_nonneg h3 h4)
      linarith
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun y hy => ?_
      have hy' : y ∈ Ioc (0 : ℝ) (π / 2) := by
        rwa [Set.uIoc_of_le (by positivity)] at hy
      have hsin : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy'.1
        (by linarith [hy'.2, Real.pi_pos])
      have hcos : 0 ≤ Real.cos y := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hy'.1, Real.pi_pos], hy'.2⟩
      have hsinh : Tendsto (fun R : ℝ => Real.sinh R) atTop atTop :=
        tendsto_atTop_mono' atTop ((eventually_ge_atTop (0 : ℝ)).mono fun R hR =>
          Real.self_le_sinh_iff.mpr hR) tendsto_id
      have hg : Tendsto (fun R : ℝ => z.im * (Real.cosh R * Real.cos y) +
          z.re * (Real.sinh R * Real.sin y)) atTop atTop := by
        refine tendsto_atTop_mono' atTop ((eventually_ge_atTop (0 : ℝ)).mono fun R hR => ?_)
          ((hsinh.const_mul_atTop (mul_pos hre hsin)))
        have h3 : 0 ≤ Real.sinh R := Real.sinh_nonneg_iff.mpr hR
        have := mul_nonneg him.le (mul_nonneg (Real.cosh_pos R).le hcos)
        nlinarith
      have hexp : Tendsto (fun R : ℝ => Real.exp (-(z.im * (Real.cosh R * Real.cos y) +
          z.re * (Real.sinh R * Real.sin y)))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hg)
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine hexp.congr fun R => ?_
      simp only [hf, Complex.norm_exp]
      rw [re_I_mul_cosh R y]
  have hlim := ((hB.sub hT).add (hF.const_mul I)).sub (tendsto_const_nhds (x := I * ∫ y in (0 : ℝ)..(π / 2), Complex.exp (I * z * (Real.cos y : ℂ))))
  have hzero : Tendsto (fun R : ℝ =>
      (∫ x in (0 : ℝ)..R, Complex.exp (-(-I * z) * (Real.cosh x : ℂ))) -
        (∫ x in (0 : ℝ)..R, Complex.exp (-z * (Real.sinh x : ℂ))) +
        I * (∫ y in (0 : ℝ)..(π / 2), f ((R : ℂ) + (y : ℂ) * I)) -
        I * ∫ y in (0 : ℝ)..(π / 2), Complex.exp (I * z * (Real.cos y : ℂ))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr fun R => ?_
    have := hrect R
    rw [intervalIntegral.integral_congr (fun x _ => E1 x), intervalIntegral.integral_congr (fun x _ => E2 x),
      intervalIntegral.integral_congr (fun y _ => E3 y)] at this
    exact this.symm
  have hmain := tendsto_nhds_unique hlim hzero
  simp only [mul_zero, add_zero] at hmain
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold hankel0 hankelRay hankelP hankelQ
  have hB' : besselK0 (-I * z) = (∫ t in Ioi (0 : ℝ), Complex.exp (-z * (Real.sinh t : ℂ))) +
      I * ∫ y in (0 : ℝ)..(π / 2), Complex.exp (I * z * (Real.cos y : ℂ)) := by
    linear_combination hmain
  rw [hB']
  field_simp
  ring_nf

/-! ### Relation to `J₀` -/

/-- Bessel's integral for `J₀` through the existing `I₀` bridge:
`J₀(x) = π⁻¹ ∫₀^π e^{-i x cos θ} dθ`. -/
theorem besselJ_zero_eq_integral (x : ℝ) :
    Complex.besselJ 0 (x : ℂ) = (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, Complex.exp (-I * x * (Real.cos θ : ℂ)) := by
  have h1 := ComplexBessel.integration_besselI0C_eq_blowup (-I * (x : ℂ))
  have h2 : ModularBootstrap.besselI0C (-I * (x : ℂ)) = Complex.besselJ 0 (x : ℂ) := by
    unfold ModularBootstrap.besselI0C
    congr 1
    rw [← mul_assoc, show I * -I = 1 by simp, one_mul]
  rw [← h2, ← h1]
  unfold Integration.besselI0C
  congr 3

lemma integral_conj_exp_real (x : ℝ) (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (starRingEnd ℂ) (∫ y in a..b, Complex.exp (I * x * (g y : ℂ))) =
      ∫ y in a..b, Complex.exp (-I * x * (g y : ℂ)) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

/-- **Mehler–Sonine at order `0`**: `H₀¹(x + i0) + conj H₀¹(x + i0) = 2 J₀(x)` for `x > 0`
(so `Re H₀¹(x + i0) = J₀(x)`). -/
theorem hankelRay_add_conj (x : ℝ) :
    hankelRay (x : ℂ) + (starRingEnd ℂ) (hankelRay (x : ℂ)) = 2 * Complex.besselJ 0 (x : ℂ) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- the `hankelQ` part is purely imaginary
  have hQ : hankelQ (x : ℂ) + (starRingEnd ℂ) (hankelQ (x : ℂ)) = 0 := by
    unfold hankelQ
    have hT : (starRingEnd ℂ) (∫ t in Ioi (0 : ℝ), Complex.exp (-(x : ℂ) * (Real.sinh t : ℂ))) =
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(x : ℂ) * (Real.sinh t : ℂ)) := by
      rw [← integral_conj]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [map_mul, hT, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    field_simp
    ring
  -- the `hankelP` part
  have hP : hankelP (x : ℂ) + (starRingEnd ℂ) (hankelP (x : ℂ)) =
      (2 / (π : ℂ)) * ((∫ y in (0 : ℝ)..(π / 2), Complex.exp (I * x * (Real.cos y : ℂ))) +
        ∫ y in (0 : ℝ)..(π / 2), Complex.exp (-I * x * (Real.cos y : ℂ))) := by
    unfold hankelP
    rw [map_mul, map_div₀, Complex.conj_ofReal, map_ofNat, integral_conj_exp_real x Real.cos (by positivity)]
    ring
  have hJ : Complex.besselJ 0 (x : ℂ) = (π : ℂ)⁻¹ *
      ((∫ y in (0 : ℝ)..(π / 2), Complex.exp (-I * x * (Real.cos y : ℂ))) +
        ∫ y in (0 : ℝ)..(π / 2), Complex.exp (I * x * (Real.cos y : ℂ))) := by
    rw [besselJ_zero_eq_integral]
    congr 1
    have hc1 : IntervalIntegrable (fun θ : ℝ => Complex.exp (-I * x * (Real.cos θ : ℂ))) volume 0 (π / 2) :=
      (by fun_prop : Continuous fun θ : ℝ => Complex.exp (-I * x * (Real.cos θ : ℂ))).intervalIntegrable _ _
    have hc2 : IntervalIntegrable (fun θ : ℝ => Complex.exp (-I * x * (Real.cos θ : ℂ))) volume (π / 2) π :=
      (by fun_prop : Continuous fun θ : ℝ => Complex.exp (-I * x * (Real.cos θ : ℂ))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals hc1 hc2]
    congr 1
    have := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => Complex.exp (-I * x * (Real.cos θ : ℂ))) π (a := 0) (b := π / 2)
    rw [show π - π / 2 = π / 2 by ring, sub_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [Real.cos_pi_sub]
    congr 1
    push_cast; ring
  unfold hankelRay
  rw [map_add]
  calc hankelP (x : ℂ) + hankelQ (x : ℂ) + ((starRingEnd ℂ) (hankelP (x : ℂ)) +
        (starRingEnd ℂ) (hankelQ (x : ℂ)))
      = (hankelP (x : ℂ) + (starRingEnd ℂ) (hankelP (x : ℂ))) +
        (hankelQ (x : ℂ) + (starRingEnd ℂ) (hankelQ (x : ℂ))) := by ring
    _ = _ := by
        rw [hP, hQ, hJ]
        field_simp
        ring

/-! ### Continuity and the bound on the positive real axis -/

lemma continuousAt_hankelRay {z₀ : ℂ} (hz₀ : 0 < z₀.re) : ContinuousAt hankelRay z₀ :=
  continuous_hankelP.continuousAt.add (continuousAt_hankelQ hz₀)

/-- The path `η ↦ z + i η` tends to `z` as `η → 0⁺`, staying in `Im > 0` when `Im z ≥ 0`. -/
lemma tendsto_vertical_path (z : ℂ) :
    Tendsto (fun η : ℝ => z + (η : ℂ) * I) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
  have : Continuous fun η : ℝ => z + (η : ℂ) * I := by fun_prop
  simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds

/-- `H₀¹(x + i0) = hankelRay x` is the limit of `H₀¹(x + iη)`, `η → 0⁺` (`x > 0`). -/
theorem tendsto_hankel0_ray {x : ℝ} (hx : 0 < x) :
    Tendsto (fun η : ℝ => hankel0 ((x : ℂ) + (η : ℂ) * I)) (𝓝[>] (0 : ℝ)) (𝓝 (hankelRay (x : ℂ))) := by
  have h1 : Tendsto (fun η : ℝ => hankelRay ((x : ℂ) + (η : ℂ) * I)) (𝓝[>] (0 : ℝ))
      (𝓝 (hankelRay (x : ℂ))) :=
    (continuousAt_hankelRay (by simpa using hx)).tendsto.comp (tendsto_vertical_path (x : ℂ))
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (hankel0_eq_ray (by simpa using hx) (by simpa using hη)).symm

/-- `‖H₀¹(x + i0)‖ ≤ √(2/π) x^{-1/2}` for `x > 0`. -/
theorem norm_hankelRay_le {x : ℝ} (hx : 0 < x) :
    ‖hankelRay (x : ℂ)‖ ≤ √(2 / π) * x ^ (-(1 / 2 : ℝ)) := by
  have hlim := (tendsto_hankel0_ray hx).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hη' : 0 < ((x : ℂ) + (η : ℂ) * I).im := by simpa using hη
  refine (norm_hankel0_le hη').trans ?_
  have hn : x ≤ ‖(x : ℂ) + (η : ℂ) * I‖ := by
    have := Complex.abs_re_le_norm ((x : ℂ) + (η : ℂ) * I)
    simpa [abs_of_pos hx] using this
  have h2 : ‖(x : ℂ) + (η : ℂ) * I‖ ^ (-(1 / 2 : ℝ)) ≤ x ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hx hn (by norm_num)
  have h3 : Real.exp (-((x : ℂ) + (η : ℂ) * I).im) ≤ 1 := by
    rw [Real.exp_le_one_iff]; simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]; linarith [hη.out]
  have := Real.sqrt_nonneg (2 / π)
  calc √(2 / π) * ‖(x : ℂ) + (η : ℂ) * I‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-((x : ℂ) + (η : ℂ) * I).im)
      ≤ √(2 / π) * x ^ (-(1 / 2 : ℝ)) * 1 := by
        gcongr
    _ = _ := mul_one _

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hankel0_eq_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel0_eq_ray

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hankelRay_add_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelRay_add_conj

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.norm_hankelRay_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hankelRay_le

end FormalResearch.ModularBootstrap.Upper.Hankel
