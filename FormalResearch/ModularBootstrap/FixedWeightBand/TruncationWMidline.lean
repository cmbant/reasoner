module

public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWAnalytic

/-!
# Midline Mellin inversion and tail bound at weight `w` (Lemma D', `vlo:Dp`)

Weight-`w` versions of the real-axis half of `Contour/TruncationError.lean` (section 3): the density integral
along the midline `ζ = 1/2 + iτ` equals the inversion integral on the line `Re z = w/2`, and the tail
of that integral beyond `|η| ≥ c' |ω(1/2 + iT₀)|` is exponentially small.  The new ingredient relative to
weight one is the Stirling^(w) prefactor `|3ω/(2π b²)|^{(w-1)/2} ≲ (1+τ)^{w-1}`.
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

noncomputable def midlineY (τ : ℝ) : ℝ :=
  (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im

lemma midlineY_odd (τ : ℝ) : midlineY (-τ) = -midlineY τ := by
  unfold midlineY
  have hconj : (1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ) =
      starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) := by
    apply Complex.ext <;> simp
  rw [hconj, chartOmega_conj (by norm_num) (by norm_num), Complex.conj_im]

lemma chartOmega_midline_eq_I_mul_midlineY (τ : ℝ) :
    chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) = Complex.I * (midlineY τ : ℂ) := by
  have hre : (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re = 0 := by
    by_cases hτ : τ = 0
    · rw [hτ, Complex.ofReal_zero, mul_zero, add_zero, chartOmega_half, Complex.zero_re]
    · unfold chartOmega
      simp only [show ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)).re ≤ 1 / 2 by simp, ↓reduceIte]
      exact chartOmegaHalf_midline_re_zero hτ
  apply Complex.ext
  · simpa [Complex.mul_re] using hre
  · simp [midlineY]

lemma hasDerivAt_midlineY (τ : ℝ) :
    HasDerivAt midlineY (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re τ := by
  have hom_an : AnalyticAt ℂ chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) :=
    analyticAt_chartOmega (by norm_num) (by norm_num)
  have hom_d := hom_an.differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) Complex.I τ := by
    have h1 := ((hasDerivAt_id τ).ofReal_comp).const_mul Complex.I |>.const_add (1 / 2 : ℂ)
    simpa using h1
  have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ (hom_d.scomp τ hline)
  refine hcomp.congr_deriv ?_
  simp [Complex.imCLM, Complex.mul_im]

lemma midlineY_deriv_neg (τ : ℝ) :
    (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re < 0 := by
  rcases le_or_gt 0 τ with hnn | hneg
  · exact (deriv_chartOmega_midline_real_neg hnn).2
  · have hm_pos : 0 ≤ -τ := by linarith
    have hpos := (deriv_chartOmega_midline_real_neg hm_pos).2
    have hconj_pt : (1 / 2 : ℂ) + Complex.I * (τ : ℂ) =
        starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ)) := by apply Complex.ext <;> simp
    have hconj_d : deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) =
        starRingEnd ℂ (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ))) := by
      rw [hconj_pt]
      exact deriv_chartOmega_conj' (by simp) (by simp; norm_num)
    rw [hconj_d, Complex.conj_re]
    exact hpos

lemma midlineY_norm_le_C_om' :
    ∃ C_om' : ℝ, 0 < C_om' ∧
      ∀ τ : ℝ, ‖deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ≤ C_om' * (1 + |τ|) := by
  obtain ⟨C_om', hC_pos, hbd⟩ := lemma_J7_asymptotics.2.2.2.2.1
  refine ⟨C_om', hC_pos, fun τ => ?_⟩
  simpa using hbd ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) ⟨by simp, by simp; norm_num⟩

lemma midlineY_norm_le_C_om :
    ∃ C_om : ℝ, 0 < C_om ∧
      ∀ τ : ℝ, ‖chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ≤ C_om * (1 + τ ^ 2) := by
  obtain ⟨C_om, hC_pos, hbd⟩ := lemma_J7_asymptotics.2.2.2.1
  refine ⟨C_om, hC_pos, fun τ => ?_⟩
  simpa using hbd ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) ⟨by simp, by simp; norm_num⟩

lemma chartPhiV_midline_conj (τ : ℝ) :
    (chartPhiV ((1 / 2 : ℂ) - Complex.I * (τ : ℂ)) (xiStar : ℂ)).re =
      (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re := by
  have hconj_pt : (1 / 2 : ℂ) - Complex.I * (τ : ℂ) =
      starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) := by apply Complex.ext <;> simp
  have hω_re : 0 ≤ (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re := by
    rw [chartOmega_midline_eq_I_mul_midlineY]; simp
  rw [hconj_pt, chartPhiV_conj (by norm_num) (by norm_num) hω_re xiStar_pos, Complex.conj_re]

lemma real_mellinIntegrand_eq_mellinTransformW (prob : FixedWeightProblem) {c' : ℝ} (_hc' : 24 ≤ c') {g : ℝ → ℝ}
    (_hg : TestClass prob (c' / 12) g) {t : ℝ} (ht : 0 < t) (η : ℝ) :
    Complex.Gamma ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ)) *
        (2 * (Real.pi : ℂ) * (t : ℂ)) ^ (-((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))) *
        mellinMGEntireW prob.w g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ)) =
      (t : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
        mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ)) := by
  set z : ℂ := (prob.w : ℂ) / 2 + Complex.I * (η : ℂ)
  have hz_re : 0 < z.re := by
    have hw1 : (1 : ℝ) ≤ prob.w := by exact_mod_cast prob.hw
    simp [z]; exact prob.hw
  have hGam_ne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz_re
  have ht_pos_c : 0 < ((t : ℂ)).re := by simpa using ht
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h2pi_ne : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr h2pi_pos.ne' |> fun _ =>
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow_mul : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ (-z) =
      (2 * (Real.pi : ℂ)) ^ (-z) * (t : ℂ) ^ (-z) := by
    rw [show (2 * (Real.pi : ℂ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl]
    exact ofReal_mul_cpow h2pi_pos (t : ℂ) (-z)
  have hpow_cancel : (2 * (Real.pi : ℂ)) ^ (-z) * (2 * (Real.pi : ℂ)) ^ z = 1 := by
    rw [← Complex.cpow_add _ _ h2pi_ne, neg_add_cancel, Complex.cpow_zero]
  rw [mellinMGEntireW_of_re_pos prob.w g hz_re]
  unfold mellinMGW
  rw [hpow_mul]
  calc Complex.Gamma z * ((2 * (Real.pi : ℂ)) ^ (-z) * (t : ℂ) ^ (-z)) *
        ((2 * (Real.pi : ℂ)) ^ z * mellinTransformW g z / Complex.Gamma z)
      = (Complex.Gamma z / Complex.Gamma z) *
          ((2 * (Real.pi : ℂ)) ^ (-z) * (2 * (Real.pi : ℂ)) ^ z) *
          (t : ℂ) ^ (-z) * mellinTransformW g z := by ring
    _ = 1 * 1 * (t : ℂ) ^ (-z) * mellinTransformW g z := by
          rw [div_self hGam_ne, hpow_cancel]
    _ = (t : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) * mellinTransformW g z := by
          rw [one_mul, one_mul]; simp only [z]; ring_nf

lemma truncatedMellinPW_real_integral_eq (prob : FixedWeightProblem) {c' : ℝ} (hc' : 24 ≤ c') (T₀ : ℝ) {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) {t : ℝ} (ht : 0 < t) :
    let ω₀ : ℂ := chartOmega ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ))
    let ω₁ : ℂ := chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))
    let η₀ : ℝ := -c' * midlineY T₀
    ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
        ∫ s in (0 : ℝ)..1,
          mellinDensityIntegrandW prob.w c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ η in (-η₀)..η₀,
          (t : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
            mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ)) := by
  intro ω₀ ω₁ η₀
  have hc'_pos : 0 < c' := by linarith
  have hω₀_eq : ω₀ = Complex.I * (midlineY T₀ : ℂ) := chartOmega_midline_eq_I_mul_midlineY T₀
  have hω₁_eq : ω₁ = Complex.I * ((-midlineY T₀ : ℝ) : ℂ) := by
    have h1 : (1 / 2 : ℂ) - Complex.I * (T₀ : ℂ) = (1 / 2 : ℂ) + Complex.I * ((-T₀ : ℝ) : ℂ) := by
      push_cast; ring
    dsimp [ω₁]
    rw [h1, chartOmega_midline_eq_I_mul_midlineY (-T₀), midlineY_odd]
  have hη_pt : ∀ s : ℝ, (1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁ =
      Complex.I * (((((2 * s - 1) * η₀) / c' : ℝ) : ℂ)) := fun s => by
    rw [hω₀_eq, hω₁_eq]
    dsimp [η₀]
    push_cast
    field_simp [hc'_pos.ne']
    ring
  have hω_diff : ω₁ - ω₀ = Complex.I * ((2 * η₀ / c' : ℝ) : ℂ) := by
    rw [hω₀_eq, hω₁_eq]
    dsimp [η₀]
    push_cast
    field_simp [hc'_pos.ne']
    ring
  let F : ℝ → ℂ := fun η =>
    (t : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) * mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))
  have hintegrand_eq : ∀ s : ℝ,
      mellinDensityIntegrandW prob.w c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀) =
        Complex.I * ((2 * η₀ / c' : ℝ) : ℂ) * F ((2 * s - 1) * η₀) := fun s => by
    rw [hη_pt s, hω_diff]
    dsimp [mellinDensityIntegrandW, F]
    have harg_eq : (prob.w : ℂ) / 2 + (c' : ℂ) * (Complex.I * (((((2 * s - 1) * η₀) / c' : ℝ) : ℂ))) =
        (prob.w : ℂ) / 2 + Complex.I * (((2 * s - 1) * η₀ : ℝ) : ℂ) := by
      push_cast; field_simp [hc'_pos.ne']
    rw [harg_eq, real_mellinIntegrand_eq_mellinTransformW prob hc' hg ht ((2 * s - 1) * η₀)]
    ring
  simp_rw [hintegrand_eq]
  rw [intervalIntegral.integral_const_mul]
  by_cases hη₀ : η₀ = 0
  · simp [hη₀]
  · have h2η₀ : 2 * η₀ ≠ 0 := mul_ne_zero two_ne_zero hη₀
    have hsub := intervalIntegral.integral_comp_mul_sub (f := F) h2η₀ η₀ (a := 0) (b := 1)
    have hsub2 : ∫ s in (0 : ℝ)..1, F ((2 * s - 1) * η₀) =
        (2 * η₀)⁻¹ • ∫ η in (-η₀)..η₀, F η := by
      have harg : (fun s : ℝ => F ((2 * s - 1) * η₀)) = fun s => F ((2 * η₀) * s - η₀) := by
        ext s; ring_nf
      rw [harg]
      simpa [mul_zero, zero_sub, mul_one, sub_self, show 2 * η₀ - η₀ = η₀ by ring] using hsub
    rw [hsub2, Complex.real_smul]
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hc'_ne : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc'_pos.ne'
    have hη₀_ne : (η₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη₀
    have hcoef : ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
          (Complex.I * ((2 * η₀ / c' : ℝ) : ℂ)) * (((2 * η₀)⁻¹ : ℝ) : ℂ) =
        1 / (2 * (Real.pi : ℂ)) := by
      push_cast
      field_simp [hpi_ne, hc'_ne, hη₀_ne, Complex.I_ne_zero]
    rw [← mul_assoc, ← mul_assoc, hcoef]

/-- The polynomial bound for the Stirling^(w) prefactor along the midline. -/
lemma norm_stirlingPrefW_midline_le {w : ℕ} (hw : 1 ≤ w) {ω b : ℂ} {C τ β : ℝ} (hC : 0 ≤ C)
    (hτ : 0 ≤ τ) (hω : ‖ω‖ ≤ C * (1 + τ ^ 2)) (hβ : 0 < β) (hb : β ≤ ‖b‖) :
    ‖stirlingPrefW w ω b‖ ≤
      (3 * C / (2 * Real.pi * β ^ 2)) ^ (((w : ℝ) - 1) / 2) * (1 + τ) ^ (w - 1) := by
  have h1 := norm_stirlingPrefW_le hw hβ hω hb
  have hπ := Real.pi_pos
  have hA : 0 ≤ 3 * C / (2 * Real.pi * β ^ 2) := by positivity
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hr : 0 ≤ ((w : ℝ) - 1) / 2 := by linarith
  have hsplit : 3 * (C * (1 + τ ^ 2)) / (2 * Real.pi * β ^ 2) =
      (3 * C / (2 * Real.pi * β ^ 2)) * (1 + τ ^ 2) := by ring
  rw [hsplit, Real.mul_rpow hA (by positivity)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h2 : (1 + τ ^ 2) ≤ (1 + τ) ^ 2 := by nlinarith
  calc (1 + τ ^ 2) ^ (((w : ℝ) - 1) / 2) ≤ ((1 + τ) ^ 2) ^ (((w : ℝ) - 1) / 2) :=
        Real.rpow_le_rpow (by positivity) h2 hr
    _ = (1 + τ) ^ (w - 1) := by
        rw [← Real.rpow_natCast ((1 + τ)) 2, ← Real.rpow_mul (by linarith),
          ← Real.rpow_natCast ((1 + τ)) (w - 1)]
        congr 1
        push_cast [Nat.cast_sub hw]
        ring

/-- Polynomial-times-exponential tail integral. -/
lemma integral_pow_mul_exp_le (w : ℕ) {T₀ T a : ℝ} (hT₀ : 0 ≤ T₀) (hT : T₀ ≤ T) (ha : 0 < a)
    (hwa : 2 * (w : ℝ) ≤ a) :
    ∫ τ in T₀..T, (1 + τ) ^ w * Real.exp (-a * (τ - T₀)) ≤ 2 * (1 + T₀) ^ w / a := by
  have hpt : ∀ τ ∈ Icc T₀ T, (1 + τ) ^ w * Real.exp (-a * (τ - T₀)) ≤
      (1 + T₀) ^ w * Real.exp (-(a / 2) * (τ - T₀)) := fun τ hτ => by
    have hτd : 0 ≤ τ - T₀ := by linarith [hτ.1]
    have h1 : 1 + τ ≤ (1 + T₀) * Real.exp (τ - T₀) := by
      have := Real.add_one_le_exp (τ - T₀)
      nlinarith
    have h2 : (1 + τ) ^ w ≤ (1 + T₀) ^ w * Real.exp ((w : ℝ) * (τ - T₀)) := by
      calc (1 + τ) ^ w ≤ ((1 + T₀) * Real.exp (τ - T₀)) ^ w :=
            pow_le_pow_left₀ (by linarith [hτ.1]) h1 w
        _ = (1 + T₀) ^ w * Real.exp ((w : ℝ) * (τ - T₀)) := by
            rw [mul_pow, ← Real.exp_nat_mul]
    calc (1 + τ) ^ w * Real.exp (-a * (τ - T₀))
        ≤ ((1 + T₀) ^ w * Real.exp ((w : ℝ) * (τ - T₀))) * Real.exp (-a * (τ - T₀)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = (1 + T₀) ^ w * Real.exp (((w : ℝ) - a) * (τ - T₀)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ (1 + T₀) ^ w * Real.exp (-(a / 2) * (τ - T₀)) := by
          gcongr
          nlinarith
  have hcont1 : ContinuousOn (fun τ : ℝ => (1 + τ) ^ w * Real.exp (-a * (τ - T₀))) (Icc T₀ T) := by
    fun_prop
  have hcont2 : ContinuousOn (fun τ : ℝ => (1 + T₀) ^ w * Real.exp (-(a / 2) * (τ - T₀))) (Icc T₀ T) := by
    fun_prop
  refine (intervalIntegral.integral_mono_on hT (hcont1.intervalIntegrable_of_Icc hT)
    (hcont2.intervalIntegrable_of_Icc hT) hpt).trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hF : ∀ τ ∈ uIcc T₀ T, HasDerivAt (fun x : ℝ => -(2 / a) * Real.exp (-(a / 2) * (x - T₀)))
      (Real.exp (-(a / 2) * (τ - T₀))) τ := fun τ _ => by
    have hlin : HasDerivAt (fun x : ℝ => -(a / 2) * (x - T₀)) (-(a / 2)) τ := by
      simpa using ((hasDerivAt_id τ).sub_const T₀).const_mul (-(a / 2))
    have := (hlin.exp).const_mul (-(2 / a))
    refine this.congr_deriv ?_
    field_simp
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun τ : ℝ => Real.exp (-(a / 2) * (τ - T₀))).intervalIntegrable T₀ T)
  rw [hftc]
  have hnn : 0 ≤ -(2 / a) * Real.exp (-(a / 2) * (T - T₀)) * (-1) := by
    have := Real.exp_pos (-(a / 2) * (T - T₀))
    have : 0 < 2 / a := by positivity
    nlinarith
  have hexp_le : Real.exp (-(a / 2) * (T - T₀)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ T - T₀ := by linarith
    nlinarith
  have hval : -(2 / a) * Real.exp (-(a / 2) * (T - T₀)) - -(2 / a) * Real.exp (-(a / 2) * (T₀ - T₀)) ≤ 2 / a := by
    simp only [sub_self, mul_zero, Real.exp_zero]
    have : 0 ≤ 2 / a := by positivity
    have := Real.exp_pos (-(a / 2) * (T - T₀))
    nlinarith
  calc (1 + T₀) ^ w * (-(2 / a) * Real.exp (-(a / 2) * (T - T₀)) -
        -(2 / a) * Real.exp (-(a / 2) * (T₀ - T₀)))
      ≤ (1 + T₀) ^ w * (2 / a) := mul_le_mul_of_nonneg_left hval (by positivity)
    _ = 2 * (1 + T₀) ^ w / a := by ring

lemma mellin_midline_tail_exists_W (prob : FixedWeightProblem)
    {T₀ d₀ d₁ c_mid C_om C_om' C_S4 : ℝ}
    (hT₀ : 4 ≤ T₀) (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hcmid : 0 < c_mid) (hCom : 0 < C_om)
    (hCom' : 0 < C_om') (hCS4 : 0 < C_S4)
    (h_mid_lb : ∀ τ : ℝ, c_mid * τ ^ 2 ≤ ‖chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖)
    (h_om_ub : ∀ τ : ℝ, ‖chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ≤ C_om * (1 + τ ^ 2))
    (h_d_bd : ∀ τ : ℝ, ‖deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ≤ C_om' * (1 + |τ|))
    (h_tail : ∀ τ ≥ T₀, (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re ≤
      -d₀ - d₁ * (τ - T₀)) :
    ∃ c_tail C_tail : ℝ, dpThr prob ≤ c_tail ∧ 0 < C_tail ∧
      ∀ {c' : ℝ}, c_tail ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass prob (c' / 12) g →
        0 < prob.cardyNorm (c' / 12) g →
        (∀ ζ ∈ stripClosed, ‖tildeWW prob.w c' g ζ‖ ≤ C_S4 * prob.cardyNorm (c' / 12) g) →
        let M := prob.cardyNorm (c' / 12) g
        let η₀ := -c' * midlineY T₀
        VerticalIntegrable (mellin fun t : ℝ => (g t : ℂ)) ((prob.w : ℝ) / 2) ∧
        ∀ {b₀ : ℝ}, xiStar / 2 ≤ b₀ → b₀ ≤ 2 * xiStar →
          (2 * Real.pi / 3) * |b₀ - xiStar| ≤ d₀ / 4 →
          let t₀ : ℝ := c' * b₀ ^ 2 / 3
          ∫ η in Ioi η₀,
              ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
                mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖ ≤
            (C_tail / 2) * M * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
              Real.exp (-(3 * d₀ / 4) * c') := by
  let P_w : ℝ := (3 * C_om / (2 * Real.pi * (xiStar / 2) ^ 2)) ^ (((prob.w : ℝ) - 1) / 2)
  have hP_w_nn : 0 ≤ P_w := by
    have := Real.pi_pos
    have := xiStar_pos
    positivity
  let c_tail : ℝ := max (dpThr prob) (max (stirThr prob.w / (c_mid * T₀ ^ 2))
    (max (3 / (xiStar / 2) ^ 2) (2 * (prob.w : ℝ) / d₁)))
  let C_tail : ℝ := 8 * C_S4 * C_om' * P_w * (1 + T₀) ^ prob.w / d₁
  refine ⟨c_tail, C_tail, le_max_left _ _, by
    have := Real.pi_pos
    have := xiStar_pos
    have : 0 < P_w := by
      have : 0 < 3 * C_om / (2 * Real.pi * (xiStar / 2) ^ 2) := by positivity
      exact Real.rpow_pos_of_pos this _
    positivity, fun {c'} hc' {g} hg hM_pos hS4 => ?_⟩
  have hc'_thr : dpThr prob ≤ c' := (le_max_left _ _).trans hc'
  have hc'_10000 : 10000 ≤ c' := (dpThr_ge_10000 prob).trans hc'_thr
  have hc'_48 : stirThr prob.w / (c_mid * T₀ ^ 2) ≤ c' :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_t₀ : 3 / (xiStar / 2) ^ 2 ≤ c' :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hc'
  have hc'_w : 2 * (prob.w : ℝ) / d₁ ≤ c' :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hc'
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  obtain ⟨hS, ha0, -⟩ := shift_le_of_max_le prob (max_one_le_of_dpThr_le prob hc'_thr)
  set M := prob.cardyNorm (c' / 12) g
  set η₀ := -c' * midlineY T₀
  have hT₀_pos : 0 < T₀ := by linarith only [hT₀]
  have hY_T₀_neg : midlineY T₀ < 0 := by
    have h1 := im_chartOmega_midline_strictAnti hT₀_pos
    dsimp only at h1
    rw [Complex.ofReal_zero, mul_zero, add_zero, chartOmega_half, Complex.zero_im] at h1
    exact h1
  have hη₀_pos : 0 < η₀ := by
    dsimp [η₀]
    nlinarith only [hc'_pos, hY_T₀_neg]
  have hm_cont : Continuous fun η : ℝ => mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ)) := by
    let F_m : ℝ → ℝ → ℂ := fun η t =>
      (g t : ℂ) * (t : ℂ) ^ ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ) - 1)
    have hF_meas : ∀ η : ℝ, AEStronglyMeasurable (F_m η) (volume.restrict (Ioi 0)) := fun η => by
      have hg_c : ContinuousOn (fun t : ℝ => (g t : ℂ)) (Ioi 0) :=
        Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)
      have hp_c : ContinuousOn (fun t : ℝ => (t : ℂ) ^ ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ) - 1)) (Ioi 0) := by
        intro t ht
        have ht_slit : (t : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using mem_Ioi.mp ht)
        exact (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const ht_slit).continuousWithinAt
      exact (hg_c.mul hp_c).aestronglyMeasurable measurableSet_Ioi
    have hF_dom : ∀ η : ℝ, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ‖F_m η t‖ ≤ |g t| * t ^ (((prob.w : ℝ) / 2 - 1)) := fun η => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := mem_Ioi.mp ht
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_pos.ne'
      have hre : ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ) - 1).re = ((prob.w : ℝ) / 2 - 1) := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
      have hnorm : ‖(t : ℂ) ^ ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ) - 1)‖ = t ^ (((prob.w : ℝ) / 2 - 1)) := by
        rw [Complex.cpow_def_of_ne_zero ht_ne, Complex.norm_exp,
          show Complex.log (t : ℂ) = (Real.log t : ℂ) from (Complex.ofReal_log ht_pos.le).symm,
          Complex.re_ofReal_mul, hre, Real.rpow_def_of_pos ht_pos]
      dsimp [F_m]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnorm]
    have hbound_int : IntegrableOn (fun t : ℝ => |g t| * t ^ (((prob.w : ℝ) / 2 - 1))) (Ioi 0) :=
      integrableOn_abs_mellinW hg.cont hg.int_cardy (polyDom_cardyV prob hS ha0) (r := (prob.w : ℝ) / 2)
        (by have : (0 : ℝ) < prob.w := by exact_mod_cast prob.hw
            linarith)
    have hF_cont : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), Continuous fun η : ℝ => F_m η t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mem_Ioi.mp ht).ne'
      dsimp [F_m]
      simp_rw [Complex.cpow_def_of_ne_zero ht_ne]
      exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul (by fun_prop)))
    exact MeasureTheory.continuous_of_dominated hF_meas hF_dom hbound_int hF_cont
  -- Helper: pointwise bound along the midline for `τ ≥ T₀`
  have hpt_τ : ∀ (τ : ℝ) (hτ : T₀ ≤ τ) (b₀ : ℝ) (hb₀_lo : xiStar / 2 ≤ b₀),
      let t₀ : ℝ := c' * b₀ ^ 2 / 3
      let η : ℝ := -c' * midlineY τ
      ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
          mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖ ≤
        (2 * C_S4 * M) * (P_w * (1 + τ) ^ (prob.w - 1)) * t₀ ^ (-(1 / 2 : ℝ)) *
          Real.exp (c' * (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re -
            c' * (2 * Real.pi / 3) * b₀) := by
    intro τ hτ b₀ hb₀_lo t₀ η
    have hb₀_pos : 0 < b₀ := by have := xiStar_pos; linarith only [hb₀_lo, this]
    have ht₀_pos : 0 < t₀ := by dsimp [t₀]; have := sq_pos_of_pos hb₀_pos; positivity
    have hτ_nn : 0 ≤ τ := by linarith only [hτ, hT₀]
    set ζ := (1 / 2 : ℂ) + Complex.I * (τ : ℂ)
    set ω := chartOmega ζ
    have hω_eq : ω = Complex.I * (midlineY τ : ℂ) := chartOmega_midline_eq_I_mul_midlineY τ
    have hω_re : ω.re = 0 := by rw [hω_eq]; simp
    have hω_norm : c_mid * τ ^ 2 ≤ ‖ω‖ := h_mid_lb τ
    have hcω_48 : stirThr prob.w ≤ c' * ‖ω‖ := by
      have h1 : stirThr prob.w ≤ c' * (c_mid * T₀ ^ 2) := (div_le_iff₀ (by positivity)).mp hc'_48
      have h2 : c_mid * T₀ ^ 2 ≤ c_mid * τ ^ 2 := by gcongr
      calc stirThr prob.w ≤ c' * (c_mid * T₀ ^ 2) := h1
        _ ≤ c' * (c_mid * τ ^ 2) := by gcongr
        _ ≤ c' * ‖ω‖ := by gcongr
    have hω_ne : ω ≠ 0 := by
      intro h0; rw [h0, norm_zero, mul_zero] at hcω_48
      linarith only [hcω_48, stirThr_pos prob.w]
    have hS_bd : ‖stirlingSW prob.w c' ω‖ ≤ 2 :=
      (norm_stirlingSW_le_two_of_stirThr_le prob.hw hc'_pos hω_re.ge hcω_48).1
    have hb₀_arg : |((b₀ : ℝ) : ℂ).arg| < Real.pi / 4 := by
      rw [Complex.arg_ofReal_of_nonneg hb₀_pos.le, abs_zero]; positivity [Real.pi_pos]
    have hpref : ‖stirlingPrefW prob.w ω (b₀ : ℂ)‖ ≤ P_w * (1 + τ) ^ (prob.w - 1) := by
      refine norm_stirlingPrefW_midline_le prob.hw hCom.le hτ_nn (h_om_ub τ)
        (half_pos xiStar_pos) ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hb₀_pos.le]; exact hb₀_lo
    have h_conj_m : ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
          mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖ =
        ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) + Complex.I * (η : ℂ)) *
          mellinTransformW g ((prob.w : ℂ) / 2 - Complex.I * (η : ℂ))‖ := by
      have h1 : starRingEnd ℂ ((t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
            mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))) =
          (t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) + Complex.I * (η : ℂ)) *
            mellinTransformW g ((prob.w : ℂ) / 2 - Complex.I * (η : ℂ)) := by
        have harg : (t₀ : ℂ).arg ≠ Real.pi := by
          rw [Complex.arg_ofReal_of_nonneg ht₀_pos.le]; exact Real.pi_pos.ne
        have hcp := Complex.cpow_conj (t₀ : ℂ) (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) harg
        rw [Complex.conj_ofReal] at hcp
        rw [map_mul, ← hcp, ← mellinTransformW_conj]
        simp only [map_add, map_sub, map_neg, map_div₀, map_ofNat, map_mul,
          Complex.conj_ofReal, Complex.conj_I, map_natCast]
        congr 2 <;> ring
      rw [← h1, Complex.norm_conj]
    rw [h_conj_m]
    have hz_eq : (prob.w : ℂ) / 2 - Complex.I * (η : ℂ) = (prob.w : ℂ) / 2 + (c' : ℂ) * ω := by
      rw [hω_eq]; dsimp [η]; push_cast; ring
    have h_rel := real_mellinIntegrand_eq_mellinTransformW prob
      (by linarith only [hc'_10000] : 24 ≤ c') hg ht₀_pos (-η)
    have hpow_neg : -((prob.w : ℂ) / 2) - Complex.I * ((-η : ℝ) : ℂ) =
        -((prob.w : ℂ) / 2) + Complex.I * (η : ℂ) := by
      push_cast; ring
    rw [hpow_neg, show (prob.w : ℂ) / 2 + Complex.I * ((-η : ℝ) : ℂ) =
        (prob.w : ℂ) / 2 - Complex.I * (η : ℂ) by push_cast; ring] at h_rel
    rw [← h_rel, hz_eq]
    have ht₀_c : (t₀ : ℂ) = (c' : ℂ) * (b₀ : ℂ) ^ 2 / 3 := by dsimp [t₀]; push_cast; ring
    have h_prod_st : mellinDensityIntegrandW prob.w c' g (t₀ : ℂ) ω =
        stirlingPrefW prob.w ω (b₀ : ℂ) * (t₀ : ℂ) ^ (-(1 / 2 : ℂ)) * stirlingSW prob.w c' ω *
          Complex.exp ((c' : ℂ) * chartPhiV ζ (b₀ : ℂ) - (c' : ℂ) * tipL (b₀ : ℂ)) *
          tildeWW prob.w c' g ζ := by
      rw [ht₀_c]
      exact mellinDensityIntegrandW_strip_eq prob.hw hc'_pos g hω_re.ge hω_ne
        (by simpa using hb₀_pos) hb₀_arg
    change ‖mellinDensityIntegrandW prob.w c' g (t₀ : ℂ) ω‖ ≤ _
    rw [h_prod_st, norm_mul, norm_mul, norm_mul, norm_mul]
    have ht₀_half : ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ))‖ = t₀ ^ (-(1 / 2 : ℝ)) := by
      rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow ht₀_pos.le, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg ht₀_pos.le _)]
    have hζ_cl : ζ ∈ stripClosed := ⟨by simp [ζ], by simp [ζ]; norm_num⟩
    have hWV_bd := hS4 ζ hζ_cl
    have hexp_norm : ‖Complex.exp ((c' : ℂ) * chartPhiV ζ (b₀ : ℂ) - (c' : ℂ) * tipL (b₀ : ℂ))‖ =
        Real.exp (c' * (chartPhiV ζ (b₀ : ℂ)).re - c' * (2 * Real.pi / 3) * b₀) := by
      rw [Complex.norm_exp]
      congr 1
      have htip : (tipL (b₀ : ℂ)).re = (2 * Real.pi / 3) * b₀ := by
        unfold tipL
        rw [Complex.re_ofReal_mul, Complex.ofReal_re]
      simp only [Complex.sub_re, Complex.re_ofReal_mul, htip]
      ring
    rw [ht₀_half, hexp_norm]
    have hP_nn : 0 ≤ P_w * (1 + τ) ^ (prob.w - 1) := by positivity
    calc ‖stirlingPrefW prob.w ω (b₀ : ℂ)‖ * t₀ ^ (-(1 / 2 : ℝ)) * ‖stirlingSW prob.w c' ω‖ *
            Real.exp (c' * (chartPhiV ζ (b₀ : ℂ)).re - c' * (2 * Real.pi / 3) * b₀) *
            ‖tildeWW prob.w c' g ζ‖
        ≤ (P_w * (1 + τ) ^ (prob.w - 1)) * t₀ ^ (-(1 / 2 : ℝ)) * 2 *
            Real.exp (c' * (chartPhiV ζ (b₀ : ℂ)).re - c' * (2 * Real.pi / 3) * b₀) *
            (C_S4 * M) := by
          have := Real.exp_pos (c' * (chartPhiV ζ (b₀ : ℂ)).re - c' * (2 * Real.pi / 3) * b₀)
          have := Real.rpow_nonneg ht₀_pos.le (-(1 / 2 : ℝ))
          have := hM_pos.le
          gcongr
      _ = (2 * C_S4 * M) * (P_w * (1 + τ) ^ (prob.w - 1)) * t₀ ^ (-(1 / 2 : ℝ)) *
            Real.exp (c' * (chartPhiV ζ (b₀ : ℂ)).re - c' * (2 * Real.pi / 3) * b₀) := by ring
  -- Helper: `(chartPhiV (1/2 + I * τ) b₀).re = (chartPhiV (1/2 + I * τ) xiStar).re + (2π/3)(b₀ - xiStar)`
  have hphi_shift : ∀ (τ : ℝ) (b₀ : ℝ), 0 < b₀ →
      (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re =
        (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re +
          (2 * Real.pi / 3) * (b₀ - xiStar) := fun τ b₀ hb₀_pos => by
    unfold chartPhiV ComplexBessel.stirlingJ tipL
    rw [chartOmega_midline_eq_I_mul_midlineY τ]
    have hlog_sub : (Complex.I * (midlineY τ : ℂ) *
          (Complex.log (3 * (Complex.I * (midlineY τ : ℂ)) / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) -
            2 * Complex.log (b₀ : ℂ))).re -
        (Complex.I * (midlineY τ : ℂ) *
          (Complex.log (3 * (Complex.I * (midlineY τ : ℂ)) / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) -
            2 * Complex.log (xiStar : ℂ))).re = 0 := by
      have h1 : Complex.I * (midlineY τ : ℂ) *
            (Complex.log (3 * (Complex.I * (midlineY τ : ℂ)) / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) -
              2 * Complex.log (b₀ : ℂ)) -
          Complex.I * (midlineY τ : ℂ) *
            (Complex.log (3 * (Complex.I * (midlineY τ : ℂ)) / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) -
              2 * Complex.log (xiStar : ℂ)) =
          Complex.I * ((-2 * midlineY τ * (Real.log b₀ - Real.log xiStar) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_log hb₀_pos.le, ← Complex.ofReal_log xiStar_pos.le]
        push_cast; ring
      have hre := congrArg Complex.re h1
      rw [Complex.sub_re] at hre
      rw [hre]; simp
    have hL1 : (((2 * Real.pi / 3 : ℝ) : ℂ) * (b₀ : ℂ)).re = (2 * Real.pi / 3) * b₀ := by
      simp
    have hL2 : (((2 * Real.pi / 3 : ℝ) : ℂ) * (xiStar : ℂ)).re = (2 * Real.pi / 3) * xiStar := by
      simp
    simp only [Complex.add_re, hL1, hL2]
    linarith only [hlog_sub]
  -- Bound the tail integral on `[η₀, -c' * midlineY T]` for any `T ≥ T₀`
  have htail_Icc : ∀ {b₀ : ℝ}, xiStar / 2 ≤ b₀ → b₀ ≤ 2 * xiStar →
      (2 * Real.pi / 3) * |b₀ - xiStar| ≤ d₀ / 4 →
      let t₀ : ℝ := c' * b₀ ^ 2 / 3
      ∀ T ≥ T₀, ∫ η in η₀..(-c' * midlineY T),
          ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
            mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖ ≤
        (C_tail / 2) * M * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
          Real.exp (-(3 * d₀ / 4) * c') := by
    intro b₀ hb₀_lo _ hb₀_gap t₀ T hT
    have hb₀_pos : 0 < b₀ := by have := xiStar_pos; linarith only [hb₀_lo, this]
    have ht₀_pos : 0 < t₀ := by dsimp [t₀]; have := sq_pos_of_pos hb₀_pos; positivity
    have ht₀_ge1 : 1 ≤ t₀ := by
      have hxi := xiStar_pos
      have hsq : (xiStar / 2) ^ 2 ≤ b₀ ^ 2 := by nlinarith only [hb₀_lo, hxi]
      have h3 : 3 ≤ c' * (xiStar / 2) ^ 2 := (div_le_iff₀ (by positivity)).mp hc'_t₀
      dsimp [t₀]
      have hcb : 3 ≤ c' * b₀ ^ 2 := h3.trans (mul_le_mul_of_nonneg_left hsq hc'_pos.le)
      linarith only [hcb]
    have ht₀_half_le : t₀ ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht₀_ge1 (by norm_num)
    let φ : ℝ → ℝ := fun τ => -c' * midlineY τ
    let φ' : ℝ → ℝ := fun τ => -c' * (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re
    have hφ_deriv : ∀ τ ∈ uIcc T₀ T, HasDerivAt φ (φ' τ) τ := fun τ _ => by
      simpa [φ, φ'] using (hasDerivAt_midlineY τ).const_mul (-c')
    have hφ'_cont : ContinuousOn φ' (uIcc T₀ T) := by
      have hom_an : AnalyticOnNhd ℂ chartOmega {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := fun z hz =>
        analyticAt_chartOmega hz.1.le hz.2.le
      have hline_cont : Continuous fun τ : ℝ => (1 / 2 : ℂ) + Complex.I * (τ : ℂ) := by fun_prop
      have hder_cont : Continuous fun τ : ℝ =>
          (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re :=
        Complex.continuous_re.comp ((hom_an.deriv.continuousOn.comp_continuous hline_cont) fun τ =>
          ⟨by simp, by simp; norm_num⟩)
      exact (continuous_const.mul hder_cont).continuousOn
    let ψ : ℝ → ℝ := fun η =>
      ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
        mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖
    have hψ_cont : Continuous ψ := by
      have ht_cont : Continuous fun η : ℝ => (t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) := by
        have ht₀_ne : (t₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₀_pos.ne'
        simp_rw [Complex.cpow_def_of_ne_zero ht₀_ne]
        exact Complex.continuous_exp.comp (continuous_const.mul (by fun_prop))
      exact (ht_cont.mul hm_cont).norm
    have hcomp := intervalIntegral.integral_comp_mul_deriv hφ_deriv hφ'_cont hψ_cont
    change ∫ η in φ T₀..φ T, ψ η ≤ _
    rw [← hcomp]
    let K : ℝ := 2 * C_S4 * M * P_w * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
      Real.exp (-(3 * d₀ / 4) * c') * C_om'
    have hK_nn : 0 ≤ K := by positivity [hM_pos]
    have hpt_bd : ∀ τ ∈ Icc T₀ T,
        ψ (φ τ) * φ' τ ≤ K * (c' * ((1 + τ) ^ prob.w * Real.exp (-c' * d₁ * (τ - T₀)))) := fun τ hτ => by
      have hτ_nn : 0 ≤ τ := by linarith only [hτ.1, hT₀]
      have hψ_bd := hpt_τ τ hτ.1 b₀ hb₀_lo
      have hsh := hphi_shift τ b₀ hb₀_pos
      have htail_bd := h_tail τ hτ.1
      have hre_bd : (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re ≤
          -(3 * d₀ / 4) - d₁ * (τ - T₀) := by
        have h1 : (2 * Real.pi / 3) * (b₀ - xiStar) ≤ (2 * Real.pi / 3) * |b₀ - xiStar| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        linarith only [hsh, htail_bd, h1, hb₀_gap]
      have hexp_ub : Real.exp (c' * (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re -
            c' * (2 * Real.pi / 3) * b₀) ≤
          Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') *
            Real.exp (-c' * d₁ * (τ - T₀)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hmul := mul_le_mul_of_nonneg_left hre_bd hc'_pos.le
        linarith only [hmul]
      have hφ'_nn : 0 ≤ φ' τ := by
        have hmneg := midlineY_deriv_neg τ
        dsimp [φ']; nlinarith only [hmneg, hc'_pos]
      have hφ'_ub : φ' τ ≤ c' * C_om' * (1 + τ) := by
        have h1 := (Complex.abs_re_le_norm _).trans (h_d_bd τ)
        rw [abs_of_neg (midlineY_deriv_neg τ)] at h1
        rw [abs_of_nonneg hτ_nn] at h1
        dsimp [φ']
        nlinarith only [h1, hc'_pos]
      have hQ_nn : 0 ≤ P_w * (1 + τ) ^ (prob.w - 1) := by positivity
      have hψ_ub : ψ (φ τ) ≤ (2 * C_S4 * M) * (P_w * (1 + τ) ^ (prob.w - 1)) *
          (Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') *
            Real.exp (-c' * d₁ * (τ - T₀))) := by
        have h1 : ψ (φ τ) ≤ (2 * C_S4 * M) * (P_w * (1 + τ) ^ (prob.w - 1)) * 1 *
            Real.exp (c' * (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re -
              c' * (2 * Real.pi / 3) * b₀) :=
          hψ_bd.trans (by gcongr)
        calc ψ (φ τ) ≤ (2 * C_S4 * M) * (P_w * (1 + τ) ^ (prob.w - 1)) *
              Real.exp (c' * (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re -
                c' * (2 * Real.pi / 3) * b₀) := by rw [mul_one] at h1; exact h1
          _ ≤ (2 * C_S4 * M) * (P_w * (1 + τ) ^ (prob.w - 1)) * (Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
                Real.exp (-(3 * d₀ / 4) * c') * Real.exp (-c' * d₁ * (τ - T₀))) := by gcongr
      have hpow : (1 + τ) ^ (prob.w - 1) * (1 + τ) = (1 + τ) ^ prob.w := by
        rw [← pow_succ]; congr 1; have := prob.hw; omega
      calc ψ (φ τ) * φ' τ
          ≤ ((2 * C_S4 * M) * (P_w * (1 + τ) ^ (prob.w - 1)) * (Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
              Real.exp (-(3 * d₀ / 4) * c') * Real.exp (-c' * d₁ * (τ - T₀)))) *
              (c' * C_om' * (1 + τ)) := mul_le_mul hψ_ub hφ'_ub hφ'_nn (by positivity [hM_pos])
        _ = K * (c' * ((1 + τ) ^ prob.w * Real.exp (-c' * d₁ * (τ - T₀)))) := by
            rw [← hpow]; dsimp [K]; ring
    have hmid_cont : Continuous midlineY :=
      continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_midlineY τ).continuousAt
    have hcont_l : ContinuousOn (fun τ => ψ (φ τ) * φ' τ) (Icc T₀ T) :=
      ((hψ_cont.comp (continuous_const.mul hmid_cont)).continuousOn).mul
        (hφ'_cont.mono (by rw [uIcc_of_le hT]))
    have hcont_r : ContinuousOn
        (fun τ => K * (c' * ((1 + τ) ^ prob.w * Real.exp (-c' * d₁ * (τ - T₀))))) (Icc T₀ T) := by
      fun_prop
    have hint_le : ∫ τ in T₀..T, ψ (φ τ) * φ' τ ≤
        ∫ τ in T₀..T, K * (c' * ((1 + τ) ^ prob.w * Real.exp (-c' * d₁ * (τ - T₀)))) :=
      intervalIntegral.integral_mono_on hT (hcont_l.intervalIntegrable_of_Icc hT)
        (hcont_r.intervalIntegrable_of_Icc hT) hpt_bd
    have hcd : 2 * (prob.w : ℝ) ≤ c' * d₁ := by
      have := (div_le_iff₀ hd₁).mp hc'_w
      linarith
    have hcd_pos : 0 < c' * d₁ := by positivity
    have hint_exp := integral_pow_mul_exp_le prob.w (by linarith only [hT₀]) hT hcd_pos hcd
    have hint_rhs : ∫ τ in T₀..T, K * (c' * ((1 + τ) ^ prob.w * Real.exp (-c' * d₁ * (τ - T₀)))) ≤
        K * (2 * (1 + T₀) ^ prob.w / d₁) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      have h1 : ∫ τ in T₀..T, (1 + τ) ^ prob.w * Real.exp (-c' * d₁ * (τ - T₀)) ≤
          2 * (1 + T₀) ^ prob.w / (c' * d₁) := by
        have := hint_exp
        simpa [mul_assoc] using this
      calc K * (c' * ∫ τ in T₀..T, (1 + τ) ^ prob.w * Real.exp (-c' * d₁ * (τ - T₀)))
          ≤ K * (c' * (2 * (1 + T₀) ^ prob.w / (c' * d₁))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hc'_pos.le) hK_nn
        _ = K * (2 * (1 + T₀) ^ prob.w / d₁) := by
            field_simp [hc'_pos.ne', hd₁.ne']
    calc ∫ τ in T₀..T, ψ (φ τ) * φ' τ
        ≤ ∫ τ in T₀..T, K * (c' * ((1 + τ) ^ prob.w * Real.exp (-c' * d₁ * (τ - T₀)))) := hint_le
      _ ≤ K * (2 * (1 + T₀) ^ prob.w / d₁) := hint_rhs
      _ = (C_tail / 2) * M * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
            Real.exp (-(3 * d₀ / 4) * c') := by
          dsimp [K, C_tail]; ring
  have htend_top : Tendsto (fun T : ℝ => -c' * midlineY T) atTop atTop := by
    have h1 : Tendsto (fun T : ℝ => -midlineY T) atTop atTop :=
      tendsto_neg_atBot_atTop.comp tendsto_im_chartOmega_midline_atTop
    have h2 := h1.const_mul_atTop hc'_pos
    simpa [show (fun T => c' * (-midlineY T)) = fun T => -c' * midlineY T by ext T; ring] using h2
  have htail_Ioi_of : ∀ {b₀ : ℝ}, xiStar / 2 ≤ b₀ → b₀ ≤ 2 * xiStar →
      (2 * Real.pi / 3) * |b₀ - xiStar| ≤ d₀ / 4 →
      let t₀ : ℝ := c' * b₀ ^ 2 / 3
      IntegrableOn (fun η : ℝ => ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
          mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖) (Ioi η₀) ∧
        ∫ η in Ioi η₀,
            ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
              mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖ ≤
          (C_tail / 2) * M * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
            Real.exp (-(3 * d₀ / 4) * c') := by
    intro b₀ hb₀_lo hb₀_hi hb₀_gap t₀
    have hb₀_pos : 0 < b₀ := by have := xiStar_pos; linarith only [hb₀_lo, this]
    have ht₀_pos : 0 < t₀ := by dsimp [t₀]; have := sq_pos_of_pos hb₀_pos; positivity
    let ψ : ℝ → ℝ := fun η =>
      ‖(t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
        mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖
    have hψ_cont : Continuous ψ := by
      have ht_cont : Continuous fun η : ℝ => (t₀ : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) := by
        have ht₀_ne : (t₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₀_pos.ne'
        simp_rw [Complex.cpow_def_of_ne_zero ht₀_ne]
        exact Complex.continuous_exp.comp (continuous_const.mul (by fun_prop))
      exact (ht_cont.mul hm_cont).norm
    let B := (C_tail / 2) * M * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
      Real.exp (-(3 * d₀ / 4) * c')
    have hbound_ev : ∀ᶠ T in atTop, ∫ η in η₀..(-c' * midlineY T), ‖ψ η‖ ≤ B := by
      filter_upwards [Ici_mem_atTop T₀] with T hT
      have h1 := htail_Icc hb₀_lo hb₀_hi hb₀_gap T (mem_Ici.mp hT)
      have heq_int : ∫ η in η₀..(-c' * midlineY T), ‖ψ η‖ = ∫ η in η₀..(-c' * midlineY T), ψ η :=
        intervalIntegral.integral_congr fun η _ => by simp [ψ]
      exact heq_int ▸ h1
    have hIoi_int : IntegrableOn ψ (Ioi η₀) :=
      integrableOn_Ioi_of_intervalIntegral_norm_bounded B η₀
        (fun T => hψ_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        htend_top hbound_ev
    have htend_int := intervalIntegral_tendsto_integral_Ioi η₀ hIoi_int htend_top
    have hbd_res : ∫ η in Ioi η₀, ψ η ≤ B :=
      le_of_tendsto htend_int (by
        filter_upwards [Ici_mem_atTop T₀] with T hT
        exact htail_Icc hb₀_lo hb₀_hi hb₀_gap T (mem_Ici.mp hT))
    exact ⟨hIoi_int, hbd_res⟩
  refine ⟨?_, fun hb₀_lo hb₀_hi hb₀_gap => (htail_Ioi_of hb₀_lo hb₀_hi hb₀_gap).2⟩
  -- VerticalIntegrable on `Re z = 1 / 2` using `b₀ = xiStar`
  have hxi_pos := xiStar_pos
  have hxi_Ioi := (htail_Ioi_of (b₀ := xiStar) (by linarith only [hxi_pos]) (by linarith only [hxi_pos])
    (by simp [abs_zero]; positivity)).1
  let t_ref := c' * xiStar ^ 2 / 3
  have ht_ref_pos : 0 < t_ref := by positivity [xiStar_pos]
  let ψ_ref : ℝ → ℝ := fun η =>
    ‖(t_ref : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
      mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖
  have hψ_ref_cont : Continuous ψ_ref := by
    have ht_cont : Continuous fun η : ℝ => (t_ref : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) := by
      have ht_ne : (t_ref : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_ref_pos.ne'
      simp_rw [Complex.cpow_def_of_ne_zero ht_ne]
      exact Complex.continuous_exp.comp (continuous_const.mul (by fun_prop))
    exact (ht_cont.mul hm_cont).norm
  have hψ_even : ∀ η : ℝ, ψ_ref (-η) = ψ_ref η := fun η => by
    dsimp [ψ_ref]
    have hconj : starRingEnd ℂ ((t_ref : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) *
          mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))) =
        (t_ref : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * ((-η : ℝ) : ℂ)) *
          mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * ((-η : ℝ) : ℂ)) := by
      have harg : (t_ref : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg ht_ref_pos.le]; exact Real.pi_pos.ne
      have hcp := Complex.cpow_conj (t_ref : ℂ) (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)) harg
      rw [Complex.conj_ofReal] at hcp
      rw [map_mul, ← hcp, ← mellinTransformW_conj]
      simp only [map_add, map_sub, map_neg, map_div₀, map_ofNat, map_mul,
        Complex.conj_ofReal, Complex.conj_I, map_natCast]
      congr 2 <;> push_cast <;> ring
    rw [← hconj, Complex.norm_conj]
  have hψ_Iio : IntegrableOn ψ_ref (Iio (-η₀)) := by
    have hind : Integrable ((Ioi η₀).indicator ψ_ref) :=
      (integrable_indicator_iff measurableSet_Ioi).mpr hxi_Ioi
    have hind_neg : Integrable (fun η : ℝ => (Ioi η₀).indicator ψ_ref (-η)) := hind.comp_neg
    have hind_eq : (fun η : ℝ => (Ioi η₀).indicator ψ_ref (-η)) = (Iio (-η₀)).indicator ψ_ref := by
      ext η
      by_cases h : η < -η₀
      · have h1 : -η ∈ Ioi η₀ := mem_Ioi.mpr (by linarith only [h])
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem (mem_Iio.mpr h), hψ_even]
      · have h1 : -η ∉ Ioi η₀ := fun hm => h (by have := mem_Ioi.mp hm; linarith only [this])
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (by simpa [mem_Iio] using h)]
    rw [hind_eq] at hind_neg
    exact (integrable_indicator_iff measurableSet_Iio).mp hind_neg
  have hψ_Icc : IntegrableOn ψ_ref (Icc (-η₀) η₀) := hψ_ref_cont.continuousOn.integrableOn_Icc
  have hψ_all : Integrable ψ_ref := by
    have huniv : (Iio (-η₀) ∪ Icc (-η₀) η₀) ∪ Ioi η₀ = univ := by
      ext η
      simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
      rcases lt_or_ge η (-η₀) with h1 | h1
      · left; left; exact h1
      · rcases le_or_gt η η₀ with h2 | h2
        · left; right; exact ⟨h1, h2⟩
        · right; exact h2
    rw [← integrableOn_univ, ← huniv]
    exact (hψ_Iio.union hψ_Icc).union hxi_Ioi
  have hm_eq_mellin : ∀ η : ℝ, mellin (fun t : ℝ => (g t : ℂ)) (((prob.w : ℝ) / 2 : ℝ) + (η : ℝ) * Complex.I) =
      mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ)) := fun η => by
    unfold mellin mellinTransformW
    rw [show (((prob.w : ℝ) / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I = (prob.w : ℂ) / 2 + Complex.I * (η : ℂ) by
      push_cast; ring]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [smul_eq_mul, mul_comm]
  have ht_ref_norm : ∀ η : ℝ, ‖(t_ref : ℂ) ^ (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ))‖ =
      t_ref ^ (-((prob.w : ℝ) / 2)) := fun η => by
    have ht_ne : (t_ref : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_ref_pos.ne'
    rw [Complex.cpow_def_of_ne_zero ht_ne, Complex.norm_exp]
    have h12 : (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ)).re = -((prob.w : ℝ) / 2) := by
      simp [Complex.sub_re, Complex.mul_re]
    have hre : (Complex.log (t_ref : ℂ) * (-((prob.w : ℂ) / 2) - Complex.I * (η : ℂ))).re =
        -((prob.w : ℝ) / 2) * Real.log t_ref := by
      rw [← Complex.ofReal_log ht_ref_pos.le, Complex.re_ofReal_mul, h12]; ring
    rw [hre, Real.rpow_def_of_pos ht_ref_pos]; congr 1; ring
  have hm_norm_int : Integrable (fun η : ℝ => t_ref ^ ((prob.w : ℝ) / 2) * ψ_ref η) :=
    hψ_all.const_mul _
  refine hm_norm_int.mono' (Continuous.aestronglyMeasurable (hm_cont.congr fun η => (hm_eq_mellin η).symm)) ?_
  · filter_upwards with η
    rw [hm_eq_mellin η]
    have hnorm_m : ‖mellinTransformW g ((prob.w : ℂ) / 2 + Complex.I * (η : ℂ))‖ =
        t_ref ^ ((prob.w : ℝ) / 2) * ψ_ref η := by
      dsimp [ψ_ref]
      rw [norm_mul, ht_ref_norm η, ← mul_assoc, ← Real.rpow_add ht_ref_pos]
      norm_num
    exact hnorm_m.le


/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.mellin_midline_tail_exists_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellin_midline_tail_exists_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.truncatedMellinPW_real_integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms truncatedMellinPW_real_integral_eq

end FormalResearch.ModularBootstrap.FixedWeightBand
