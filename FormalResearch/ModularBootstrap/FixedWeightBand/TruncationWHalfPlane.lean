module

public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWContour

/-!
# Half-plane chart for the two-constants argument (Lemma D', `vlo:Dp`)

Weight-free helper lemmas of the Poisson–Jensen step of Lemma D' (`vlo:Dp`): the map
`z ↦ U₀ (z^{1/2} - 1)/(z^{1/2} + 1)` from the upper half-plane onto the upper half-disc of radius `U₀`, its
boundary behaviour and the Poisson kernel lower bound.  Copied from the private section 6 of
`Contour/TruncationError.lean` (the Virasoro file is unchanged).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval FourierTransform

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special
open FormalResearch.ModularBootstrap.Chart
open FormalResearch.ModularBootstrap.ChartGeometry
open FormalResearch.ModularBootstrap.ComplexBessel
open FormalResearch.ModularBootstrap.StripMultiplier
open FormalResearch.ModularBootstrap.Mellin
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.WeightAxioms

/-! ### 6. Half-plane Poisson–Jensen argument and Lemma D' (`vlo:Dp`) -/

noncomputable def halfUpper (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * ((Real.pi : ℂ) / 4)) * (-Complex.I * z) ^ (1 / 2 : ℂ)

noncomputable def halfPlaneChart (U₀ : ℝ) (z : ℂ) : ℂ :=
  (U₀ : ℂ) * (halfUpper z - 1) / (halfUpper z + 1)

lemma halfUpper_sq_eq {z : ℂ} :
    halfUpper z ^ 2 = z := by
  unfold halfUpper
  rw [mul_pow, ← Complex.exp_nat_mul]
  have h1 : ((2 : ℕ) : ℂ) * (Complex.I * ((Real.pi : ℂ) / 4)) = Complex.I * ((Real.pi : ℂ) / 2) := by
    push_cast; ring
  have h2 : Complex.exp (Complex.I * ((Real.pi : ℂ) / 2)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]; simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  have h3 : ((-Complex.I * z) ^ (1 / 2 : ℂ)) ^ 2 = -Complex.I * z := by
    by_cases h0 : -Complex.I * z = 0
    · rw [h0, Complex.zero_cpow (by norm_num)]; simp
    · rw [Complex.cpow_def_of_ne_zero h0, ← Complex.exp_nat_mul]
      have hmul : ((2 : ℕ) : ℂ) * (Complex.log (-Complex.I * z) * (1 / 2 : ℂ)) =
          Complex.log (-Complex.I * z) := by push_cast; ring
      rw [hmul, Complex.exp_log h0]
  rw [h1, h2, h3]
  calc Complex.I * (-Complex.I * z) = (-(Complex.I * Complex.I)) * z := by ring
    _ = z := by rw [Complex.I_mul_I]; ring

lemma halfUpper_pos_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    0 < (halfUpper z).re ∧ 0 < (halfUpper z).im := by
  set ζ : ℂ := -Complex.I * z
  have hζ_re : 0 < ζ.re := by simp [ζ, hz]
  have hζ_ne : ζ ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hζ_re; linarith
  have hζ_arg : |ζ.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hζ_re)
  have hθ_lo : 0 < Real.pi / 4 + ζ.arg / 2 := by
    linarith [(abs_lt.mp hζ_arg).1]
  have hθ_hi : Real.pi / 4 + ζ.arg / 2 < Real.pi / 2 := by
    linarith [(abs_lt.mp hζ_arg).2]
  have hexp_half : halfUpper z =
      (Real.sqrt ‖ζ‖ : ℂ) * Complex.exp (Complex.I * (((Real.pi / 4 + ζ.arg / 2 : ℝ) : ℂ))) := by
    unfold halfUpper
    have hlog_eq : Complex.log ζ = (Real.log ‖ζ‖ : ℂ) + (ζ.arg : ℂ) * Complex.I := rfl
    have hpow_z : (-Complex.I * z) ^ (1 / 2 : ℂ) =
        Complex.exp (((Real.log ‖ζ‖ / 2 : ℝ) : ℂ) + Complex.I * ((ζ.arg / 2 : ℝ) : ℂ)) := by
      change ζ ^ (1 / 2 : ℂ) = _
      rw [Complex.cpow_def_of_ne_zero hζ_ne, Complex.log]
      congr 1; push_cast; ring
    have hlog_half : Real.exp (Real.log ‖ζ‖ / 2) = Real.sqrt ‖ζ‖ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (norm_pos_iff.mpr hζ_ne)]; ring_nf
    rw [hpow_z, Complex.exp_add, ← Complex.ofReal_exp, hlog_half,
      mul_left_comm, ← Complex.exp_add]
    congr 2; push_cast; ring
  have hexp_eq : Complex.exp (Complex.I * ((Real.pi / 4 + ζ.arg / 2 : ℝ) : ℂ)) =
      (Real.cos (Real.pi / 4 + ζ.arg / 2) : ℂ) +
        (Real.sin (Real.pi / 4 + ζ.arg / 2) : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hexp_half, hexp_eq]
  have hcos_pos : 0 < Real.cos (Real.pi / 4 + ζ.arg / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ_hi⟩
  have hsin_pos : 0 < Real.sin (Real.pi / 4 + ζ.arg / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hθ_lo (by linarith [Real.pi_pos])
  have hsqrt_pos : 0 < Real.sqrt ‖ζ‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hζ_ne)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  constructor <;> nlinarith

lemma halfUpper_eq_cpow_half_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    halfUpper u = u ^ (1 / 2 : ℂ) := by
  have hsq1 : halfUpper u ^ 2 = u := halfUpper_sq_eq
  have hsq2 : (u ^ (1 / 2 : ℂ)) ^ 2 = u := FormalResearch.Special.cpow_half_sq u
  have hdiff : (halfUpper u - u ^ (1 / 2 : ℂ)) * (halfUpper u + u ^ (1 / 2 : ℂ)) = 0 := by
    linear_combination hsq1 - hsq2
  rcases mul_eq_zero.mp hdiff with h0 | h0
  · exact sub_eq_zero.mp h0
  · exfalso
    have hre1 := (halfUpper_pos_of_im_pos hu).1
    have hre2 : 0 ≤ (u ^ (1 / 2 : ℂ)).re := cpow_half_re_nonneg u
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.zero_re] at this
    linarith

lemma halfUpper_analyticAt_upper_or_real {z : ℂ} (hz : 0 ≤ z.im) (hne : z ≠ 0) :
    AnalyticAt ℂ halfUpper z := by
  have hslit : -Complex.I * z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    rcases eq_or_lt_of_le hz with him0 | him_pos
    · right
      have hre0 : z.re ≠ 0 := fun hr => hne (Complex.ext hr him0.symm)
      simp [Complex.mul_im, hre0]
    · left; simp [Complex.mul_re, him_pos]
  have hpow : AnalyticAt ℂ (fun w : ℂ => (-Complex.I * w) ^ (1 / 2 : ℂ)) z := by
    have hlog : AnalyticAt ℂ Complex.log (-Complex.I * z) := analyticAt_clog hslit
    have hlog_comp := hlog.comp (analyticAt_const.mul analyticAt_id)
    exact (hlog_comp.mul analyticAt_const).cexp.congr (by
      filter_upwards [(isOpen_slitPlane.preimage (continuous_const.mul continuous_id)).mem_nhds hslit] with w hw
      exact (Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hw) (1 / 2 : ℂ)).symm)
  exact analyticAt_const.mul hpow

lemma halfUpper_posReal {σ : ℝ} (hσ : 0 < σ) :
    halfUpper (σ : ℂ) = (Real.sqrt σ : ℂ) := by
  have hζ_ne : -Complex.I * (σ : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp [hσ.ne'] at this
  have harg : (-Complex.I * (σ : ℂ)).arg = -(Real.pi / 2) := by
    rw [show -Complex.I * (σ : ℂ) = (0 : ℂ) + (-(σ) : ℝ) * Complex.I by simp; ring]
    exact Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨by simp, by simp [hσ]⟩
  unfold halfUpper
  rw [Complex.cpow_def_of_ne_zero hζ_ne, Complex.log, harg]
  have hnorm : ‖-Complex.I * (σ : ℂ)‖ = σ := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hσ.le]
  rw [hnorm, show ((Real.log σ : ℝ) : ℂ) + (-(Real.pi / 2) : ℝ) * Complex.I =
      ((Real.log σ : ℝ) : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring]
  have hs : Real.exp (Real.log σ / 2) = Real.sqrt σ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hσ]; ring_nf
  have hpow : Complex.exp (((Real.log σ : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (1 / 2 : ℂ)) =
      (Real.sqrt σ : ℂ) * Complex.exp (-(Complex.I * ((Real.pi : ℂ) / 4))) := by
    rw [show ((Real.log σ : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (1 / 2 : ℂ) =
        ((Real.log σ / 2 : ℝ) : ℂ) + (-(Complex.I * ((Real.pi : ℂ) / 4))) by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, hs]
  rw [hpow, mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

lemma halfUpper_negReal {σ : ℝ} (hσ : σ < 0) :
    halfUpper (σ : ℂ) = Complex.I * (Real.sqrt (-σ) : ℂ) := by
  have hns : 0 < -σ := by linarith
  have hζ_ne : -Complex.I * (σ : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp [hσ.ne] at this
  have harg : (-Complex.I * (σ : ℂ)).arg = Real.pi / 2 := by
    rw [show -Complex.I * (σ : ℂ) = (0 : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.arg_eq_pi_div_two_iff.mpr ⟨by simp, by simp [hns]⟩
  unfold halfUpper
  rw [Complex.cpow_def_of_ne_zero hζ_ne, Complex.log, harg]
  have hnorm : ‖-Complex.I * (σ : ℂ)‖ = -σ := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonpos hσ.le]
  rw [hnorm, show ((Real.log (-σ) : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I =
      ((Real.log (-σ) : ℝ) : ℂ) + Complex.I * ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring]
  have hs : Real.exp (Real.log (-σ) / 2) = Real.sqrt (-σ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hns]; ring_nf
  have hpow : Complex.exp (((Real.log (-σ) : ℂ) + Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (1 / 2 : ℂ)) =
      (Real.sqrt (-σ) : ℂ) * Complex.exp (Complex.I * ((Real.pi : ℂ) / 4)) := by
    rw [show ((Real.log (-σ) : ℂ) + Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (1 / 2 : ℂ) =
        ((Real.log (-σ) / 2 : ℝ) : ℂ) + Complex.I * ((Real.pi : ℂ) / 4) by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, hs]
  rw [hpow, mul_left_comm, ← Complex.exp_add]
  have hsum : Complex.I * ((Real.pi : ℂ) / 4) + Complex.I * ((Real.pi : ℂ) / 4) =
      Complex.I * ((Real.pi : ℂ) / 2) := by ring
  have hI : Complex.exp (Complex.I * ((Real.pi : ℂ) / 2)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]; simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  rw [hsum, hI, mul_comm]

lemma halfPlaneChart_mem_upperHalf {U₀ : ℝ} (hU₀ : 0 < U₀) {z : ℂ} (hz : 0 < z.im) :
    ‖halfPlaneChart U₀ z‖ < U₀ ∧ 0 < (halfPlaneChart U₀ z).im := by
  obtain ⟨hw_re, hw_im⟩ := halfUpper_pos_of_im_pos hz
  set w := halfUpper z
  have hw_add_ne : w + 1 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hnorm_lt : ‖w - 1‖ < ‖w + 1‖ := by
    have hsq : ‖w - 1‖ ^ 2 < ‖w + 1‖ ^ 2 := by
      have h1 : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
      have h2 : ‖w + 1‖ ^ 2 = (w.re + 1) ^ 2 + w.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
      nlinarith
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have him_div : 0 < ((w - 1) / (w + 1)).im := by
    have hden_pos : 0 < Complex.normSq (w + 1) := Complex.normSq_pos.mpr hw_add_ne
    rw [Complex.div_im, ← sub_div]
    refine div_pos ?_ hden_pos
    simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.add_re, Complex.one_re,
      Complex.sub_re, Complex.add_im, add_zero]
    linarith [hw_re]
  unfold halfPlaneChart
  rw [mul_div_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hU₀.le, norm_div]
  refine ⟨?_, ?_⟩
  · have hq : ‖w - 1‖ / ‖w + 1‖ < 1 := (div_lt_one (norm_pos_iff.mpr hw_add_ne)).mpr hnorm_lt
    nlinarith
  · rw [Complex.im_ofReal_mul]
    exact mul_pos hU₀ him_div

lemma poissonKernel_Ioi_ge_quarter {x y : ℝ} (hy : 0 < y) (hxy : -y ≤ x) :
    Integrable (poissonKernel x y) ∧
      ∫ σ : ℝ, poissonKernel x y σ = 1 ∧
      (1 / 4 : ℝ) ≤ ∫ σ in Ioi (0 : ℝ), poissonKernel x y σ := by
  let F : ℝ → ℝ := fun σ => (1 / Real.pi) * Real.arctan ((σ - x) / y)
  have hF_deriv : ∀ σ : ℝ, HasDerivAt F (poissonKernel x y σ) σ := fun σ => by
    have h1 : HasDerivAt (fun s : ℝ => (s - x) / y) (1 / y) σ := by
      simpa using ((hasDerivAt_id σ).sub_const x).div_const y
    have h2 := (Real.hasDerivAt_arctan ((σ - x) / y)).comp σ h1
    refine (h2.const_mul (1 / Real.pi)).congr_deriv ?_
    unfold poissonKernel
    have hsq : 1 + ((σ - x) / y) ^ 2 = ((σ - x) ^ 2 + y ^ 2) / y ^ 2 := by
      field_simp [hy.ne']; ring
    rw [hsq]
    field_simp [hy.ne', Real.pi_pos.ne']
  have hF_top : Tendsto F atTop (𝓝 (1 / 2 : ℝ)) := by
    have hlin : Tendsto (fun σ : ℝ => (σ - x) / y) atTop atTop :=
      (tendsto_id.atTop_add tendsto_const_nhds).atTop_div_const hy
    have harctan : Tendsto (fun σ : ℝ => Real.arctan ((σ - x) / y)) atTop (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.comp hlin).mono_right nhdsWithin_le_nhds
    have hhalf : (1 / Real.pi) * (Real.pi / 2) = 1 / 2 := by field_simp [Real.pi_pos.ne']
    exact hhalf ▸ harctan.const_mul (1 / Real.pi)
  have hF_bot : Tendsto F atBot (𝓝 (-(1 / 2) : ℝ)) := by
    have hlin : Tendsto (fun σ : ℝ => (σ - x) / y) atBot atBot :=
      (tendsto_id.atBot_add tendsto_const_nhds).atBot_div_const hy
    have harctan : Tendsto (fun σ : ℝ => Real.arctan ((σ - x) / y)) atBot (𝓝 (-(Real.pi / 2))) :=
      (Real.tendsto_arctan_atBot.comp hlin).mono_right nhdsWithin_le_nhds
    have hnhalf : (1 / Real.pi) * (-(Real.pi / 2)) = -(1 / 2) := by field_simp [Real.pi_pos.ne']
    exact hnhalf ▸ harctan.const_mul (1 / Real.pi)
  have h_nn : ∀ σ : ℝ, 0 ≤ poissonKernel x y σ := fun σ => by
    unfold poissonKernel; positivity
  have hIoi_int : IntegrableOn (poissonKernel x y) (Ioi (0 : ℝ)) :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' (fun σ _ => hF_deriv σ)
      (fun σ _ => h_nn σ) hF_top
  have hIoi_eq : ∫ σ in Ioi (0 : ℝ), poissonKernel x y σ = 1 / 2 - F 0 :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (fun σ _ => hF_deriv σ)
      (fun σ _ => h_nn σ) hF_top
  have hIic : IntegrableOn (poissonKernel x y) (Iic (0 : ℝ)) ∧
      ∫ σ in Iic (0 : ℝ), poissonKernel x y σ = F 0 - (-(1 / 2)) := by
    have hG_deriv : ∀ σ : ℝ, HasDerivAt (fun t : ℝ => (-1 : ℝ) * F (-t)) (poissonKernel x y (-σ)) σ := fun σ => by
      have hc : HasDerivAt (fun t : ℝ => F (-t)) (-poissonKernel x y (-σ)) σ := by
        simpa [Function.comp_def] using (hF_deriv (-σ)).comp σ (hasDerivAt_neg σ)
      simpa using hc.const_mul (-1 : ℝ)
    have hG_top : Tendsto (fun t : ℝ => (-1 : ℝ) * F (-t)) atTop (𝓝 (1 / 2 : ℝ)) := by
      have ht := (hF_bot.comp tendsto_neg_atTop_atBot).const_mul (-1 : ℝ)
      simpa using ht
    have hneg_int : IntegrableOn (fun t : ℝ => poissonKernel x y (-t)) (Ioi (0 : ℝ)) :=
      MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' (fun σ _ => hG_deriv σ)
        (fun σ _ => h_nn (-σ)) hG_top
    have hneg_eq : ∫ t in Ioi (0 : ℝ), poissonKernel x y (-t) = 1 / 2 - ((-1 : ℝ) * F (-0)) :=
      MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (fun σ _ => hG_deriv σ)
        (fun σ _ => h_nn (-σ)) hG_top
    have hIic_int : IntegrableOn (poissonKernel x y) (Iic (0 : ℝ)) := by
      have h1 : IntegrableOn (poissonKernel x y) (Iio (0 : ℝ)) := by simpa using hneg_int.comp_neg
      have h0_int : IntegrableOn (poissonKernel x y) (Icc (-1 : ℝ) 0) := by
        have hcont : Continuous (poissonKernel x y) := by
          unfold poissonKernel
          exact continuous_const.div
            (continuous_const.mul (((continuous_id.sub continuous_const).pow 2).add continuous_const))
            fun σ => (mul_pos Real.pi_pos (by positivity)).ne'
        exact hcont.continuousOn.integrableOn_Icc
      exact (h1.union h0_int).mono_set fun t ht =>
        (lt_or_eq_of_le (mem_Iic.mp ht)).imp mem_Iio.mpr fun h0 => ⟨by linarith only [h0], h0.le⟩
    have hIic_eq : ∫ σ in Iic (0 : ℝ), poissonKernel x y σ = F 0 - (-(1 / 2)) := by
      have hcomp := integral_comp_neg_Ioi (0 : ℝ) (poissonKernel x y)
      rw [neg_zero] at hcomp
      rw [← hcomp, hneg_eq, neg_zero]
      ring
    exact ⟨hIic_int, hIic_eq⟩
  have hInt : Integrable (poissonKernel x y) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hIic.1.union hIoi_int
  have hTot : ∫ σ : ℝ, poissonKernel x y σ = 1 := by
    have hadd := (MeasureTheory.integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hInt).symm
    rw [compl_Iic] at hadd
    rw [hadd, hIic.2, hIoi_eq]
    ring
  have hIoi_lb : (1 / 4 : ℝ) ≤ ∫ σ in Ioi (0 : ℝ), poissonKernel x y σ := by
    rw [hIoi_eq]
    have hle : (0 - x) / y ≤ 1 := by rw [div_le_one hy]; linarith
    have ha_le : Real.arctan ((0 - x) / y) ≤ Real.pi / 4 := by
      calc Real.arctan ((0 - x) / y) ≤ Real.arctan 1 := Real.arctan_mono hle
        _ = Real.pi / 4 := Real.arctan_one
    have hF0_ub : F 0 ≤ 1 / 4 := by
      dsimp [F]
      calc (1 / Real.pi) * Real.arctan ((0 - x) / y) ≤ (1 / Real.pi) * (Real.pi / 4) := by
            gcongr
        _ = 1 / 4 := by field_simp [Real.pi_pos.ne']
    linarith
  exact ⟨hInt, hTot, hIoi_lb⟩

lemma exists_halfPlaneChart_preimage {U₀ : ℝ} (hU₀ : 0 < U₀) {w : ℂ}
    (him : 0 < w.im) (hw : ‖w‖ ≤ U₀ / 2) :
    ∃ z₀ : ℂ, 0 < z₀.im ∧ -z₀.im ≤ z₀.re ∧ halfPlaneChart U₀ z₀ = w := by
  let ζ : ℂ := w / (U₀ : ℂ)
  have hζ_norm : ‖ζ‖ ≤ 1 / 2 := by
    dsimp [ζ]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hU₀.le, div_le_iff₀ hU₀]
    linarith
  have hζ_im : 0 < ζ.im := by
    dsimp [ζ]
    rw [show w / (U₀ : ℂ) = ((U₀⁻¹ : ℝ) : ℂ) * w by push_cast; ring, Complex.im_ofReal_mul]
    exact mul_pos (inv_pos.mpr hU₀) him
  have hsub_ne : 1 - ζ ≠ 0 := by
    intro h0
    have := congrArg norm (eq_of_sub_eq_zero h0)
    rw [norm_one] at this; linarith
  let w₀ : ℂ := (1 + ζ) / (1 - ζ)
  let z₀ : ℂ := w₀ ^ 2
  have hw₀_re : w₀.re = (1 - ‖ζ‖ ^ 2) / ‖1 - ζ‖ ^ 2 := by
    dsimp [w₀]
    have h1 : Complex.normSq (1 - ζ) = ‖1 - ζ‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rw [Complex.div_re, h1, ← add_div]
    have hmul : (1 + ζ).re * (1 - ζ).re + (1 + ζ).im * (1 - ζ).im = 1 - ‖ζ‖ ^ 2 := by
      have hns : Complex.normSq ζ = ‖ζ‖ ^ 2 := Complex.normSq_eq_norm_sq ζ
      rw [Complex.normSq_apply] at hns
      simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
        Complex.sub_im]
      linarith
    rw [hmul]
  have hw₀_im : w₀.im = 2 * ζ.im / ‖1 - ζ‖ ^ 2 := by
    dsimp [w₀]
    have h1 : Complex.normSq (1 - ζ) = ‖1 - ζ‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rw [Complex.div_im, h1, ← sub_div]
    have hmul : (1 + ζ).im * (1 - ζ).re - (1 + ζ).re * (1 - ζ).im = 2 * ζ.im := by
      simp; ring
    rw [hmul]
  have hw₀_re_pos : 0 < w₀.re := by
    rw [hw₀_re]
    exact div_pos (by nlinarith [norm_nonneg ζ]) (sq_pos_of_pos (norm_pos_iff.mpr hsub_ne))
  have hw₀_im_pos : 0 < w₀.im := by
    rw [hw₀_im]
    exact div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hsub_ne))
  have hw₀_ratio : 3 * w₀.im ≤ 4 * w₀.re := by
    rw [hw₀_im, hw₀_re]
    have hden_pos : 0 < ‖1 - ζ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hsub_ne)
    have hζ_im_le : ζ.im ≤ 1 / 2 := (Complex.abs_im_le_norm ζ |>.trans hζ_norm).trans' (le_abs_self _)
    have hnum : 3 * (2 * ζ.im) ≤ 4 * (1 - ‖ζ‖ ^ 2) := by
      nlinarith only [hζ_im_le, hζ_norm, norm_nonneg ζ]
    rw [← mul_div_assoc, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hnum hden_pos.le
  have hz₀_im : 0 < z₀.im := by
    dsimp [z₀]; rw [sq, Complex.mul_im]; nlinarith
  have hz₀_re_lb : -z₀.im ≤ z₀.re := by
    dsimp [z₀]; rw [sq, Complex.mul_re, Complex.mul_im]
    nlinarith
  have hU_z₀ : halfUpper z₀ = w₀ := by
    have hsq1 : halfUpper z₀ ^ 2 = z₀ := halfUpper_sq_eq
    have hsq2 : w₀ ^ 2 = z₀ := rfl
    have hdiff : (halfUpper z₀ - w₀) * (halfUpper z₀ + w₀) = 0 := by
      linear_combination hsq1 - hsq2
    rcases mul_eq_zero.mp hdiff with h0 | h0
    · exact sub_eq_zero.mp h0
    · exfalso
      have hre1 := (halfUpper_pos_of_im_pos hz₀_im).1
      have := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.zero_re] at this
      linarith
  have hchart_z₀ : halfPlaneChart U₀ z₀ = w := by
    unfold halfPlaneChart
    rw [hU_z₀]
    have hw₀_add_ne : w₀ + 1 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have h_id : (w₀ - 1) / (w₀ + 1) = ζ := by
      dsimp [w₀]
      field_simp [hsub_ne]; ring
    rw [mul_div_assoc, h_id]
    dsimp [ζ]; field_simp [hU₀.ne']
  exact ⟨z₀, hz₀_im, hz₀_re_lb, hchart_z₀⟩

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.exists_halfPlaneChart_preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_halfPlaneChart_preimage

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.poissonKernel_Ioi_ge_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms poissonKernel_Ioi_ge_quarter

end FormalResearch.ModularBootstrap.FixedWeightBand
