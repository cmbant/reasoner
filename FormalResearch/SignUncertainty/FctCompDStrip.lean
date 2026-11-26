module

public import FormalResearch.SignUncertainty.FctMomentCore
public import FormalResearch.SignUncertainty.CtOuterPoisson
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Symmetric strip Poisson extension `g_D` for `fct:comp-D` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, §2.1 `(fct:gD-def)` and Lemma FCT.3 (`fct:comp-D`) (1).

For any smooth compactly supported real density `w : ℝ → ℝ`:
* `stripCompG w ζ = ∫ t : ℝ, (w t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))` on the open strip `S = {0 < Re ζ < 1}`;
* `stripCompGExt w ζ` extends `stripCompG w` continuously to the closed strip `S̄ = {0 ≤ Re ζ ≤ 1}` with boundary values
  `w(τ) ± i ϑ_D[w](τ)` on `Re ζ = 0` resp. `Re ζ = 1`;
* `iteratedDeriv_stripCompG`: `iteratedDeriv r (stripCompG w) ζ = (-i)^r * stripCompG (iteratedDeriv r w) ζ` on `S`;
* `norm_stripCompGExt_le`: maximum modulus principle on `S̄` for `stripCompGExt w`, yielding global `S̄` bounds for
  `g_D`, `g_D'`, `g_D''`, and in fact `g_D^{(r)}` for every `r ≥ 0` (repairing the `g_D''` gap noted in `PLAN.md` for `fct:ce-band`);
* `norm_iteratedDeriv_stripCompG_interior`: interior strip bound `(fct:gD-int)` on `Re ζ ∈ [1/8, 7/8]` for all `r ≥ 0`;
* `abs_iteratedDeriv_fctThetaD_tail`: boundary tail bound `(fct:th-tail)` for `|t| ≥ 12 τ_1` for all `r ≥ 0`.

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty.FctCompD

open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.CtOuter

/-- Closed unit strip `S̄ = {0 ≤ Re ζ ≤ 1}`. -/
def closedStrip : Set ℂ := {ζ | 0 ≤ ζ.re ∧ ζ.re ≤ 1}

/-- Symmetric strip Poisson extension `g_D[w](ζ) = ∫ w(t) / sin(π(ζ - i t)) dt` of `(fct:gD-def)`. -/
noncomputable def stripCompG (w : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  ∫ t : ℝ, (w t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))

/-- Strip outer compensator `D[w](ζ) = exp(g_D[w](ζ))`. -/
noncomputable def stripCompD (w : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  Complex.exp (stripCompG w ζ)

/-- Continuous extension of `stripCompG w` to `closedStrip`. -/
noncomputable def stripCompGExt (w : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  if ζ.re ≤ 0 then (w ζ.im : ℂ) + Complex.I * (fctThetaD w ζ.im : ℂ)
  else if 1 ≤ ζ.re then (w ζ.im : ℂ) - Complex.I * (fctThetaD w ζ.im : ℂ)
  else stripCompG w ζ

lemma stripCompGExt_eq_of_mem_strip {w : ℝ → ℝ} {ζ : ℂ} (hζ : ζ ∈ strip) :
    stripCompGExt w ζ = stripCompG w ζ := by
  unfold stripCompGExt
  simp [not_le.mpr hζ.1, not_le.mpr hζ.2]

lemma stripCompGExt_left (w : ℝ → ℝ) (τ : ℝ) :
    stripCompGExt w ((τ : ℂ) * Complex.I) = (w τ : ℂ) + Complex.I * (fctThetaD w τ : ℂ) := by
  unfold stripCompGExt
  simp

lemma stripCompGExt_right (w : ℝ → ℝ) (τ : ℝ) :
    stripCompGExt w (1 + (τ : ℂ) * Complex.I) = (w τ : ℂ) - Complex.I * (fctThetaD w τ : ℂ) := by
  unfold stripCompGExt
  simp

/-! ### Exact kernel integral `∫ 1 / sin(π(σ + i s)) ds = 1` and basic kernel bounds -/

lemma norm_inv_sin_strip_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (s : ℝ) :
    ‖(Complex.sin (π * ((σ : ℂ) + Complex.I * s)))⁻¹‖ ≤
      2 / Real.sin (π * σ) * Real.exp (-(π * |s|)) := by
  have hsin_pos : 0 < Real.sin (π * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have h1 := kernel_norm_le (ζ := (σ : ℂ) + Complex.I * s) (t := 0) (σ := Real.sin (π * σ))
    hsin_pos (Real.sin_le_one _) (by simp)
  simpa [sub_zero] using h1

lemma norm_sin_ge_abs_sinh (σ s : ℝ) :
    |Real.sinh (π * s)| ≤ ‖Complex.sin (π * ((σ : ℂ) + Complex.I * s))‖ := by
  have h1 := norm_sin_sq (π * ((σ : ℂ) + Complex.I * s))
  have hre : (↑π * ((σ : ℂ) + Complex.I * s)).re = π * σ := by simp [Complex.mul_re]
  have him : (↑π * ((σ : ℂ) + Complex.I * s)).im = π * s := by simp [Complex.mul_im]
  rw [hre, him] at h1
  have hsq : |Real.sinh (π * s)| ^ 2 ≤ ‖Complex.sin (π * ((σ : ℂ) + Complex.I * s))‖ ^ 2 := by
    rw [sq_abs, h1]; nlinarith [sq_nonneg (Real.sin (π * σ))]
  have h2 := sq_le_sq.mp hsq
  rwa [abs_abs, abs_of_nonneg (norm_nonneg _)] at h2

lemma integrable_inv_sin_strip {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Integrable (fun s : ℝ => (Complex.sin (π * ((σ : ℂ) + Complex.I * s)))⁻¹) := by
  have hsin_pos : 0 < Real.sin (π * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hcont : Continuous (fun s : ℝ => (Complex.sin (π * ((σ : ℂ) + Complex.I * s)))⁻¹) := by
    refine Continuous.inv₀ (Complex.continuous_sin.comp (continuous_const.mul (continuous_const.add
      (continuous_const.mul Complex.continuous_ofReal)))) fun s => ?_
    have hmem : (σ : ℂ) + Complex.I * s ∈ strip := ⟨by simp [hσ0], by simp [hσ1]⟩
    simpa using sin_arg_ne_zero (t := 0) hmem
  refine ((integrable_exp_neg_abs' Real.pi_pos).const_mul (2 / Real.sin (π * σ))).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  simpa [neg_mul] using norm_inv_sin_strip_le hσ0 hσ1 s

lemma integral_inv_sin_strip {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∫ s : ℝ, (Complex.sin (π * ((σ : ℂ) + Complex.I * s)))⁻¹ = 1 := by
  have hint := integrable_inv_sin_strip hσ0 hσ1
  apply Complex.ext
  · have hre_int := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at hre_int
    rw [← hre_int, Complex.one_re]
    have hre : ∀ s : ℝ, ((Complex.sin (π * ((σ : ℂ) + Complex.I * s)))⁻¹).re = poissonK σ s := by
      intro s
      have hmem : (σ : ℂ) + Complex.I * s ∈ strip := ⟨by simp [hσ0], by simp [hσ1]⟩
      have h1 := re_inv_sin_arg hmem 0
      simpa [one_div, sub_zero] using h1
    simp_rw [hre]
    exact integral_poissonK hσ0 hσ1
  · have him_int := Complex.imCLM.integral_comp_comm hint
    simp only [Complex.imCLM_apply] at him_int
    rw [← him_int, Complex.one_im]
    -- The imaginary part is odd in `s`, so its integral over `ℝ` is `0`.
    have hodd : ∀ s : ℝ, ((Complex.sin (π * ((σ : ℂ) + Complex.I * (-s))))⁻¹).im =
        -((Complex.sin (π * ((σ : ℂ) + Complex.I * s)))⁻¹).im := by
      intro s
      have hconj : Complex.sin (π * ((σ : ℂ) + Complex.I * (-s))) =
          (starRingEnd ℂ) (Complex.sin (π * ((σ : ℂ) + Complex.I * s))) := by
        rw [← Complex.sin_conj]
        congr 1
        simp [Complex.conj_ofReal, Complex.conj_I]
      rw [hconj, ← map_inv₀ (starRingEnd ℂ)]
      exact Complex.conj_im _
    have hneg := MeasureTheory.integral_neg_eq_self (μ := volume)
      (fun s : ℝ => ((Complex.sin (π * ((σ : ℂ) + Complex.I * s)))⁻¹).im)
    simp only [Complex.ofReal_neg] at hneg
    have h2 : ∫ s : ℝ, ((Complex.sin (π * ((σ : ℂ) + Complex.I * (-s))))⁻¹).im =
        -(∫ s : ℝ, ((Complex.sin (π * ((σ : ℂ) + Complex.I * s)))⁻¹).im) := by
      simp_rw [hodd]; exact integral_neg _
    linarith

/-! ### Holomorphy, symmetries, and derivative identity `g_D^{(r)} = (-i)^r g_D[w^{(r)}]` -/

lemma stripCompG_eq_conv {w : ℝ → ℝ} (ζ : ℂ) :
    stripCompG w ζ = ∫ s : ℝ, (w (ζ.im - s) : ℂ) / Complex.sin (π * ((ζ.re : ℂ) + Complex.I * s)) := by
  unfold stripCompG
  rw [← integral_sub_left_eq_self (fun t => (w t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))) volume ζ.im]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  dsimp only
  congr 2
  apply Complex.ext <;> simp

lemma stripCompG_integrable {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_supp : HasCompactSupport w)
    {ζ : ℂ} (hζ : ζ ∈ strip) :
    Integrable (fun t : ℝ => (w t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))) := by
  have hcont : Continuous (fun t : ℝ => (w t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))) :=
    (Complex.continuous_ofReal.comp hw_cont).div
      (Complex.continuous_sin.comp (continuous_const.mul (continuous_const.sub
        (continuous_const.mul Complex.continuous_ofReal))))
      (fun t => sin_arg_ne_zero t hζ)
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact hw_supp.isCompact fun t ht =>
      subset_tsupport w fun h => ht (by simp [h]))

lemma differentiableOn_stripCompG {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_supp : HasCompactSupport w) :
    DifferentiableOn ℂ (stripCompG w) strip := by
  intro ζ hζ
  obtain ⟨R, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R ≤ |t| → w t = 0 := by
    obtain ⟨K, hK⟩ := hw_supp.isCompact.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨max K 1 + 1, by positivity, fun t ht => ?_⟩
    by_contra hne
    have hmem := hK (subset_tsupport w hne)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
    linarith [le_max_left K 1]
  obtain ⟨B, hB⟩ := hw_supp.exists_bound_of_continuous hw_cont
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (w 0)) (hB 0)
  set δ : ℝ := min ζ.re (1 - ζ.re) / 2 with hδ_def
  have hδ0 : 0 < δ := by
    have : 0 < min ζ.re (1 - ζ.re) := lt_min hζ.1 (sub_pos.mpr hζ.2)
    linarith
  set U : Set ℂ := Metric.ball ζ δ
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hU_sub : U ⊆ strip := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hre := (Complex.abs_re_le_norm (z - ζ)).trans_lt hz
    rw [Complex.sub_re, abs_lt] at hre
    exact ⟨by linarith [min_le_left ζ.re (1 - ζ.re), hδ_def], by linarith [min_le_right ζ.re (1 - ζ.re), hδ_def]⟩
  have hsin_lb : ∀ z ∈ U, Real.sin (π * δ) ≤ Real.sin (π * z.re) := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hre := (Complex.abs_re_le_norm (z - ζ)).trans_lt hz
    rw [Complex.sub_re, abs_lt] at hre
    have h1 : δ ≤ z.re := by linarith [min_le_left ζ.re (1 - ζ.re), hδ_def]
    have h2 : z.re ≤ 1 - δ := by linarith [min_le_right ζ.re (1 - ζ.re), hδ_def]
    have hδ_le_half : δ ≤ 1 / 2 := by
      have := min_le_left ζ.re (1 - ζ.re)
      have := min_le_right ζ.re (1 - ζ.re)
      linarith
    rcases le_or_gt z.re (1 / 2) with hz12 | hz12
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
    · rw [← Real.sin_pi_sub (π * z.re), show π - π * z.re = π * (1 - z.re) by ring]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
  have hsinδ_pos : 0 < Real.sin (π * δ) := by
    have hδ_lt1 : δ < 1 := by linarith [min_le_left ζ.re (1 - ζ.re), hζ.2, hδ_def]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hdiffU : DifferentiableOn ℂ (stripCompG w) U := by
    refine CtOuter.differentiableOn_integral_param hU_open
      (Φ := fun z t => (w t : ℂ) / Complex.sin (π * (z - Complex.I * t))) ?_ ?_ ?_
    · intro z hz
      exact ((Complex.continuous_ofReal.comp hw_cont).div
        (Complex.continuous_sin.comp (continuous_const.mul (continuous_const.sub
          (continuous_const.mul Complex.continuous_ofReal))))
        (fun t => sin_arg_ne_zero t (hU_sub hz))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      refine differentiableOn_const _ |>.div ?_ (fun z hz => sin_arg_ne_zero t (hU_sub hz))
      exact Complex.differentiable_sin.comp_differentiableOn
        (differentiableOn_const _ |>.mul (differentiableOn_id.sub (differentiableOn_const _)))
    · intro w₀ hw₀
      obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp hU_open w₀ hw₀
      refine ⟨r, hr0, fun t => if |t| ≤ R then 2 * B / Real.sin (π * δ) else 0, ?_, ?_⟩
      · have h1 : Integrable (fun t : ℝ => (Icc (-R) R).indicator (fun _ => 2 * B / Real.sin (π * δ)) t) :=
          (integrableOn_const (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
        refine h1.congr (Filter.Eventually.of_forall fun t => ?_)
        by_cases ht : |t| ≤ R
        · have hmem : t ∈ Icc (-R) R := abs_le.mp ht
          simp [ht, hmem]
        · have hmem : t ∉ Icc (-R) R := fun h => ht (abs_le.mpr h)
          simp [ht, hmem]
      · refine Filter.Eventually.of_forall fun t z hz => ?_
        have hzU : z ∈ U := hrsub hz
        dsimp only
        by_cases ht : |t| ≤ R
        · rw [ite_eq_left_iff.mpr fun h => absurd ht h, norm_div, Complex.norm_real]
          have hk := kernel_norm_le t hsinδ_pos (Real.sin_le_one _) (hsin_lb z hzU)
          rw [norm_inv] at hk
          have hexp : Real.exp (-(π * |z.im - t|)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
          have hinv_le : ‖Complex.sin (π * (z - Complex.I * t))‖⁻¹ ≤ 2 / Real.sin (π * δ) :=
            hk.trans (mul_le_of_le_one_right (by positivity) hexp)
          calc ‖w t‖ / ‖Complex.sin (π * (z - Complex.I * t))‖
              = ‖w t‖ * ‖Complex.sin (π * (z - Complex.I * t))‖⁻¹ := div_eq_mul_inv _ _
            _ ≤ B * (2 / Real.sin (π * δ)) := mul_le_mul (hB t) hinv_le (by positivity) hB0
            _ = 2 * B / Real.sin (π * δ) := by ring
        · push Not at ht
          rw [ite_eq_right_iff.mpr fun h => absurd h (not_le.mpr ht), hR.2 t ht.le, Complex.ofReal_zero,
            zero_div, norm_zero]
  exact (hdiffU.differentiableAt (hU_open.mem_nhds (Metric.mem_ball_self hδ0))).differentiableWithinAt

lemma stripCompG_one_sub {w : ℝ → ℝ} (hw_even : ∀ t, w (-t) = w t) (ζ : ℂ) :
    stripCompG w (1 - ζ) = stripCompG w ζ := by
  unfold stripCompG
  rw [← MeasureTheory.integral_neg_eq_self (fun t : ℝ => (w t : ℂ) / Complex.sin (π * (1 - ζ - Complex.I * t)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [hw_even t]
  congr 1
  have h1 : (π : ℂ) * (1 - ζ - Complex.I * (-t : ℝ)) = π - π * (ζ - Complex.I * t) := by
    push_cast; ring
  rw [h1, Complex.sin_pi_sub]

lemma stripCompG_conj {w : ℝ → ℝ} (hw_even : ∀ t, w (-t) = w t) (ζ : ℂ) :
    stripCompG w (star ζ) = star (stripCompG w ζ) := by
  unfold stripCompG
  change ∫ t : ℝ, (w t : ℂ) / Complex.sin (π * (star ζ - Complex.I * t)) =
    (starRingEnd ℂ) (∫ t : ℝ, (w t : ℂ) / Complex.sin (π * (ζ - Complex.I * t)))
  rw [← integral_conj, ← MeasureTheory.integral_neg_eq_self (fun t : ℝ => (w t : ℂ) / Complex.sin (π * (star ζ - Complex.I * t)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [hw_even t, map_div₀, Complex.conj_ofReal, ← Complex.sin_conj]
  congr 2
  simp [Complex.conj_ofReal, Complex.conj_I]

/-- Derivative identity `deriv (stripCompG w) ζ = -i * stripCompG (deriv w) ζ` on `strip`. -/
lemma deriv_stripCompG {w : ℝ → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hw_supp : HasCompactSupport w)
    {ζ : ℂ} (hζ : ζ ∈ strip) :
    deriv (stripCompG w) ζ = -Complex.I * stripCompG (deriv w) ζ := by
  have hdiff : DifferentiableAt ℂ (stripCompG w) ζ :=
    (differentiableOn_stripCompG hw.continuous hw_supp).differentiableAt (isOpen_strip.mem_nhds hζ)
  have hline : HasDerivAt (fun τ : ℝ => stripCompG w ((ζ.re : ℂ) + Complex.I * τ))
      (Complex.I * deriv (stripCompG w) ζ) ζ.im := by
    have h1 : HasDerivAt (fun τ : ℝ => (ζ.re : ℂ) + Complex.I * (τ : ℂ)) Complex.I ζ.im := by
      have := (Complex.ofRealCLM.hasDerivAt (x := ζ.im)).const_mul Complex.I |>.const_add (ζ.re : ℂ)
      simpa using this
    have h2 : HasDerivAt (stripCompG w) (deriv (stripCompG w) ζ) ((ζ.re : ℂ) + Complex.I * (ζ.im : ℂ)) := by
      have heq : (ζ.re : ℂ) + Complex.I * (ζ.im : ℂ) = ζ := by apply Complex.ext <;> simp
      rw [heq]
      exact hdiff.hasDerivAt
    have h3 := (h2.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt ζ.im h1
    exact h3.congr_deriv (by simp)
  have hline_int : HasDerivAt (fun τ : ℝ => stripCompG w ((ζ.re : ℂ) + Complex.I * τ))
      (stripCompG (deriv w) ζ) ζ.im := by
    have heq_fn : (fun τ : ℝ => stripCompG w ((ζ.re : ℂ) + Complex.I * τ)) =
        fun τ : ℝ => ∫ s : ℝ, (w (τ - s) : ℂ) / Complex.sin (π * ((ζ.re : ℂ) + Complex.I * s)) := by
      ext τ; rw [stripCompG_eq_conv]; simp
    rw [heq_fn]
    obtain ⟨B₁, hB₁⟩ := hw_supp.deriv.exists_bound_of_continuous (hw.continuous_deriv (by simp))
    have hB₁0 : 0 ≤ B₁ := le_trans (norm_nonneg _) (hB₁ 0)
    have hsin_pos : 0 < Real.sin (π * ζ.re) :=
      Real.sin_pos_of_pos_of_lt_pi (by have := hζ.1; positivity) (by have := hζ.2; nlinarith [Real.pi_pos])
    have hbound_int : Integrable (fun s : ℝ => B₁ * (2 / Real.sin (π * ζ.re) * Real.exp (-(π * |s|)))) :=
      ((integrable_exp_neg_abs' Real.pi_pos).const_mul (2 / Real.sin (π * ζ.re)) |>.const_mul B₁).congr
        (Filter.Eventually.of_forall fun s => by simp [neg_mul])
    have hd_int := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun τ s => (w (τ - s) : ℂ) / Complex.sin (π * ((ζ.re : ℂ) + Complex.I * s)))
      (F' := fun τ s => ((deriv w (τ - s) : ℝ) : ℂ) / Complex.sin (π * ((ζ.re : ℂ) + Complex.I * s)))
      (x₀ := ζ.im) (s := univ) univ_mem
      (Eventually.of_forall fun τ => by
        have hcont : Continuous (fun s : ℝ => (w (τ - s) : ℂ) / Complex.sin (π * ((ζ.re : ℂ) + Complex.I * s))) :=
          (Complex.continuous_ofReal.comp (hw.continuous.comp (continuous_const.sub continuous_id))).div
            (Complex.continuous_sin.comp (continuous_const.mul (continuous_const.add
              (continuous_const.mul Complex.continuous_ofReal))))
            (fun s => by
              have hmem : (ζ.re : ℂ) + Complex.I * s ∈ strip := ⟨by simp [hζ.1], by simp [hζ.2]⟩
              simpa using sin_arg_ne_zero (t := 0) hmem)
        exact hcont.aestronglyMeasurable)
      (by
        obtain ⟨B₀, hB₀⟩ := hw_supp.exists_bound_of_continuous hw.continuous
        have hB₀0 : 0 ≤ B₀ := le_trans (norm_nonneg _) (hB₀ 0)
        refine ((integrable_exp_neg_abs' Real.pi_pos).const_mul (2 / Real.sin (π * ζ.re)) |>.const_mul B₀).mono' ?_ ?_
        · exact ((Complex.continuous_ofReal.comp (hw.continuous.comp (continuous_const.sub continuous_id))).div
            (Complex.continuous_sin.comp (continuous_const.mul (continuous_const.add
              (continuous_const.mul Complex.continuous_ofReal))))
            (fun s => by
              have hmem : (ζ.re : ℂ) + Complex.I * s ∈ strip := ⟨by simp [hζ.1], by simp [hζ.2]⟩
              simpa using sin_arg_ne_zero (t := 0) hmem)).aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun s => ?_
          rw [norm_div, Complex.norm_real, div_eq_mul_inv]
          have hk : ‖Complex.sin (π * ((ζ.re : ℂ) + Complex.I * s))‖⁻¹ ≤
              2 / Real.sin (π * ζ.re) * Real.exp (-π * |s|) := by
            simpa [norm_inv, neg_mul] using norm_inv_sin_strip_le hζ.1 hζ.2 s
          exact mul_le_mul (hB₀ _) hk (by positivity) hB₀0)
      (by
        exact ((Complex.continuous_ofReal.comp ((hw.continuous_deriv (by simp)).comp (continuous_const.sub continuous_id))).div
          (Complex.continuous_sin.comp (continuous_const.mul (continuous_const.add
            (continuous_const.mul Complex.continuous_ofReal))))
          (fun s => by
            have hmem : (ζ.re : ℂ) + Complex.I * s ∈ strip := ⟨by simp [hζ.1], by simp [hζ.2]⟩
            simpa using sin_arg_ne_zero (t := 0) hmem)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun s τ _ => by
        rw [norm_div, Complex.norm_real, div_eq_mul_inv]
        have hk : ‖Complex.sin (π * ((ζ.re : ℂ) + Complex.I * s))‖⁻¹ ≤
            2 / Real.sin (π * ζ.re) * Real.exp (-(π * |s|)) := by
          simpa [norm_inv] using norm_inv_sin_strip_le hζ.1 hζ.2 s
        exact mul_le_mul (hB₁ _) hk (by positivity) hB₁0)
      hbound_int
      (Filter.Eventually.of_forall fun s τ _ => by
        have hdw : HasDerivAt (fun t : ℝ => w (t - s)) (deriv w (τ - s)) τ := by
          have := ((hw.differentiable (by simp) (τ - s)).hasDerivAt).comp τ ((hasDerivAt_id τ).sub_const s)
          exact this.congr_deriv (mul_one _)
        exact (hdw.ofReal_comp).div_const _)
    rw [stripCompG_eq_conv (w := deriv w) ζ]
    exact hd_int.2
  have heq := hline.unique hline_int
  calc deriv (stripCompG w) ζ = -Complex.I * (Complex.I * deriv (stripCompG w) ζ) := by
        rw [← mul_assoc]; simp
    _ = -Complex.I * stripCompG (deriv w) ζ := by rw [heq]

/-- All-order derivative identity on `strip`: `g_D^{(r)}[w](ζ) = (-i)^r g_D[w^{(r)}](ζ)`. -/
lemma iteratedDeriv_stripCompG (r : ℕ) {w : ℝ → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hw_supp : HasCompactSupport w) {ζ : ℂ} (hζ : ζ ∈ strip) :
    iteratedDeriv r (stripCompG w) ζ = (-Complex.I) ^ r * stripCompG (iteratedDeriv r w) ζ := by
  induction r generalizing ζ with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv r (stripCompG w) =ᶠ[𝓝 ζ]
        fun z => (-Complex.I) ^ r * stripCompG (iteratedDeriv r w) z := by
      filter_upwards [isOpen_strip.mem_nhds hζ] with z hz using ih hz
    have hdiff_r : DifferentiableAt ℂ (stripCompG (iteratedDeriv r w)) ζ :=
      (differentiableOn_stripCompG (contDiff_iteratedDeriv_infty hw r).continuous
        (hasCompactSupport_iteratedDeriv hw_supp r)).differentiableAt (isOpen_strip.mem_nhds hζ)
    rw [hev.deriv_eq, deriv_const_mul _ hdiff_r,
      deriv_stripCompG (contDiff_iteratedDeriv_infty hw r) (hasCompactSupport_iteratedDeriv hw_supp r) hζ,
      ← iteratedDeriv_succ, pow_succ]
    ring

/-! ### Continuity up to `∂S`, vertical decay, and maximum modulus principle on `S̄` -/

/-- Uniform vertical decay of `stripCompGExt w` as `|Im ζ| → ∞` on `closedStrip`. -/
lemma stripCompGExt_norm_le_of_large_im {w : ℝ → ℝ} (hw_cont : Continuous w) {R : ℝ} (_hR : 0 < R)
    (hsupp : Function.support w ⊆ Ioo (-R) R) {ζ : ℂ} (_hζ : ζ ∈ closedStrip) (him : R + 1 ≤ |ζ.im|) :
    ‖stripCompGExt w ζ‖ ≤ 4 * (∫ t : ℝ, |w t|) * Real.exp (-(π * (|ζ.im| - R))) := by
  have hint_w : Integrable (fun t : ℝ => |w t|) :=
    (hw_cont.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
        (fun t ht => Ioo_subset_Icc_self (hsupp (by simpa using ht)))))
  have hdist : ∀ t ∈ Ioo (-R) R, |ζ.im| - R ≤ |ζ.im - t| := by
    intro t ht
    have ht_abs : |t| ≤ R := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
    have htri := abs_sub_abs_le_abs_sub ζ.im t
    linarith
  have hsinh_bd : ∀ t ∈ Ioo (-R) R, |1 / Real.sinh (π * (ζ.im - t))| ≤ 4 * Real.exp (-(π * (|ζ.im| - R))) := by
    intro t ht
    have hd : 1 ≤ |ζ.im - t| := by linarith [hdist t ht]
    have h1 := abs_inv_sinh_le_exp hd
    have h2 : Real.exp (-(π * |ζ.im - t|)) ≤ Real.exp (-(π * (|ζ.im| - R))) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hdist t ht])
    linarith
  -- Boundary cases (`ζ.re = 0` or `ζ.re = 1`): `w(ζ.im) = 0`, so `‖stripCompGExt‖ = |fctThetaD w ζ.im|`
  have hbdry : |fctThetaD w ζ.im| ≤ 4 * (∫ t : ℝ, |w t|) * Real.exp (-(π * (|ζ.im| - R))) := by
    have hw0 : w ζ.im = 0 := by
      by_contra hne
      have := hsupp hne
      have : |ζ.im| < R := abs_lt.mpr this
      linarith
    unfold fctThetaD
    have hcongr : ∀ z : ℝ, (w (ζ.im + z) - w ζ.im) / Real.sinh (π * z) = w (ζ.im + z) / Real.sinh (π * z) := by
      intro z; rw [hw0, sub_zero]
    simp_rw [hcongr]
    have hshift : ∫ z : ℝ, w (ζ.im + z) / Real.sinh (π * z) = ∫ t : ℝ, w t / Real.sinh (π * (t - ζ.im)) := by
      rw [← integral_add_left_eq_self (μ := volume) (fun t => w t / Real.sinh (π * (t - ζ.im))) ζ.im]
      congr 1; ext z; simp [add_sub_cancel_left]
    rw [hshift]
    calc |∫ t : ℝ, w t / Real.sinh (π * (t - ζ.im))|
        = ‖∫ t : ℝ, w t / Real.sinh (π * (t - ζ.im))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ t : ℝ, ‖w t / Real.sinh (π * (t - ζ.im))‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (4 * Real.exp (-(π * (|ζ.im| - R)))) * |w t| := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (hint_w.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
          dsimp only
          by_cases ht : t ∈ Ioo (-R) R
          · rw [Real.norm_eq_abs, abs_div, show |Real.sinh (π * (t - ζ.im))| = |Real.sinh (π * (ζ.im - t))| by
              rw [show π * (t - ζ.im) = -(π * (ζ.im - t)) by ring, Real.sinh_neg, abs_neg]]
            have h1 := hsinh_bd t ht
            rw [abs_div, abs_one, one_div] at h1
            rw [div_eq_mul_inv, mul_comm |w t|]
            exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          · have hwt : w t = 0 := by by_contra hne; exact ht (hsupp hne)
            simp [hwt]
      _ = 4 * (∫ t : ℝ, |w t|) * Real.exp (-(π * (|ζ.im| - R))) := by
          rw [integral_const_mul]; ring
  unfold stripCompGExt
  by_cases h0 : ζ.re ≤ 0
  · rw [ite_eq_left_iff.mpr fun h => absurd h0 h]
    have hw0 : w ζ.im = 0 := by
      by_contra hne; have : |ζ.im| < R := abs_lt.mpr (hsupp hne); linarith
    rw [hw0, Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hbdry
  · rw [ite_eq_right_iff.mpr fun h => absurd h h0]
    by_cases h1 : 1 ≤ ζ.re
    · rw [ite_eq_left_iff.mpr fun h => absurd h1 h]
      have hw0 : w ζ.im = 0 := by
        by_contra hne; have : |ζ.im| < R := abs_lt.mpr (hsupp hne); linarith
      rw [hw0, Complex.ofReal_zero, zero_sub, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact hbdry
    · rw [ite_eq_right_iff.mpr fun h => absurd h h1]
      unfold stripCompG
      calc ‖∫ t : ℝ, (w t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))‖
          ≤ ∫ t : ℝ, ‖(w t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ t : ℝ, (4 * Real.exp (-(π * (|ζ.im| - R)))) * |w t| := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              (hint_w.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
            by_cases ht : t ∈ Ioo (-R) R
            · dsimp only
              rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, mul_comm |w t|]
              have hsin_ge : |Real.sinh (π * (ζ.im - t))| ≤ ‖Complex.sin (π * (ζ - Complex.I * t))‖ := by
                have h := norm_sin_ge_abs_sinh ζ.re (ζ.im - t)
                have heq : (ζ.re : ℂ) + Complex.I * ((ζ.im - t : ℝ) : ℂ) = ζ - Complex.I * t := by
                  apply Complex.ext <;> simp
                rwa [heq] at h
              have hsh_pos : 0 < |Real.sinh (π * (ζ.im - t))| := by
                have hd : 1 ≤ |ζ.im - t| := by linarith [hdist t ht]
                exact abs_pos.mpr (sinh_pi_ne_zero (fun h => by rw [h, abs_zero] at hd; linarith))
              have hinv : ‖Complex.sin (π * (ζ - Complex.I * t))‖⁻¹ ≤ 4 * Real.exp (-(π * (|ζ.im| - R))) := by
                have h1 := inv_anti₀ hsh_pos hsin_ge
                have h2 := hsinh_bd t ht
                rw [abs_div, abs_one, one_div] at h2
                exact h1.trans h2
              exact mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
            · have hwt : w t = 0 := by by_contra hne; exact ht (hsupp hne)
              simp [hwt]
        _ = 4 * (∫ t : ℝ, |w t|) * Real.exp (-(π * (|ζ.im| - R))) := by
            rw [integral_const_mul]; ring

/-- Continuity of `stripCompGExt w` on the closed strip `S̄ = {0 ≤ Re ζ ≤ 1}`. -/
lemma continuousOn_stripCompGExt {w : ℝ → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hw_supp : HasCompactSupport w) :
    ContinuousOn (stripCompGExt w) closedStrip := by
  intro ζ₀ hζ₀
  -- Open strip interior: immediate from `differentiableOn_stripCompG`
  by_cases hint : ζ₀ ∈ strip
  · have hcont : ContinuousAt (stripCompG w) ζ₀ :=
      ((differentiableOn_stripCompG hw.continuous hw_supp).differentiableAt (isOpen_strip.mem_nhds hint)).continuousAt
    refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ (stripCompGExt_eq_of_mem_strip hint)
    filter_upwards [nhdsWithin_le_nhds (isOpen_strip.mem_nhds hint)] with z hz
    exact stripCompGExt_eq_of_mem_strip hz
  -- Otherwise `ζ₀.re = 0` or `ζ₀.re = 1`
  obtain ⟨B₀, hB₀⟩ := hw_supp.exists_bound_of_continuous hw.continuous
  obtain ⟨B₁, hB₁⟩ := hw_supp.deriv.exists_bound_of_continuous (hw.continuous_deriv (by simp))
  have hB₀0 : 0 ≤ B₀ := le_trans (norm_nonneg _) (hB₀ 0)
  have hB₁0 : 0 ≤ B₁ := le_trans (norm_nonneg _) (hB₁ 0)
  -- Uniform integrable majorant for the subtracted kernel on `s ∈ ℝ`
  let dom : ℝ → ℝ := fun s => if |s| ≤ 1 then B₁ / π else 8 * B₀ * Real.exp (-(π * |s|))
  have hdom_int : Integrable dom := by
    have h1 : Integrable (fun s : ℝ => (Icc (-1 : ℝ) 1).indicator (fun _ => B₁ / π) s) :=
      (integrableOn_const (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
    have h2 : Integrable (fun s : ℝ => 8 * B₀ * Real.exp (-(π * |s|))) :=
      ((integrable_exp_neg_abs' Real.pi_pos).const_mul (8 * B₀)).congr
        (Filter.Eventually.of_forall fun s => by simp [neg_mul])
    refine (h1.add h2).mono' ?_ (Filter.Eventually.of_forall fun s => ?_)
    · have hmeas : MeasurableSet {s : ℝ | |s| ≤ 1} := isClosed_le continuous_abs continuous_const |>.measurableSet
      exact Measurable.aestronglyMeasurable
        (Measurable.ite hmeas measurable_const
          (measurable_const.mul (Real.continuous_exp.measurable.comp
            (continuous_const.mul continuous_abs).neg.measurable)))
    · dsimp only [dom, Pi.add_apply]
      by_cases hs : |s| ≤ 1
      · have hmem : s ∈ Icc (-1 : ℝ) 1 := abs_le.mp hs
        rw [ite_eq_left_iff.mpr fun h => absurd hs h, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          Set.indicator_of_mem hmem]
        linarith [show 0 ≤ 8 * B₀ * Real.exp (-(π * |s|)) by positivity]
      · have hmem : s ∉ Icc (-1 : ℝ) 1 := fun h => hs (abs_le.mpr h)
        rw [ite_eq_right_iff.mpr fun h => absurd h hs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          Set.indicator_of_notMem hmem, zero_add]
  have hdom_bound : ∀ (σ τ s : ℝ), s ≠ 0 →
      ‖((w (τ - s) - w τ : ℝ) : ℂ) / Complex.sin (π * ((σ : ℂ) + Complex.I * s))‖ ≤ dom s := by
    intro σ τ s hs0
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    have hsin_ge := norm_sin_ge_abs_sinh σ s
    have hsh_pos : 0 < |Real.sinh (π * s)| := abs_pos.mpr (sinh_pi_ne_zero hs0)
    have hdiv_le : |w (τ - s) - w τ| / ‖Complex.sin (π * ((σ : ℂ) + Complex.I * s))‖ ≤
        |w (τ - s) - w τ| / |Real.sinh (π * s)| :=
      div_le_div_of_nonneg_left (abs_nonneg _) hsh_pos hsin_ge
    refine hdiv_le.trans ?_
    dsimp only [dom]
    by_cases hs1 : |s| ≤ 1
    · rw [ite_eq_left_iff.mpr fun h => absurd hs1 h]
      have hlip : |w (τ - s) - w τ| ≤ B₁ * |s| := by
        have h := Convex.norm_image_sub_le_of_norm_deriv_le
          (f := w) (s := univ) (C := B₁) (fun x _ => (hw.differentiable (by simp) x))
          (fun x _ => hB₁ x) convex_univ (mem_univ τ) (mem_univ (τ - s))
        simpa [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg] using h
      calc |w (τ - s) - w τ| / |Real.sinh (π * s)|
          ≤ (B₁ * |s|) / |Real.sinh (π * s)| := div_le_div_of_nonneg_right hlip hsh_pos.le
        _ = B₁ * |s / Real.sinh (π * s)| := by rw [abs_div, mul_div_assoc]
        _ ≤ B₁ * (1 / π) := mul_le_mul_of_nonneg_left (abs_mul_inv_sinh_le s) hB₁0
        _ = B₁ / π := by ring
    · push Not at hs1
      rw [ite_eq_right_iff.mpr fun h => absurd h (not_le.mpr hs1)]
      have hdiff : |w (τ - s) - w τ| ≤ 2 * B₀ := by
        have h1 : |w (τ - s)| ≤ B₀ := by simpa [Real.norm_eq_abs] using hB₀ (τ - s)
        have h2 : |w τ| ≤ B₀ := by simpa [Real.norm_eq_abs] using hB₀ τ
        linarith [abs_sub (w (τ - s)) (w τ)]
      have hinv := abs_inv_sinh_le_exp hs1.le
      rw [abs_div, abs_one, one_div] at hinv
      calc |w (τ - s) - w τ| / |Real.sinh (π * s)|
          = |w (τ - s) - w τ| * |Real.sinh (π * s)|⁻¹ := div_eq_mul_inv _ _
        _ ≤ (2 * B₀) * (4 * Real.exp (-(π * |s|))) := mul_le_mul hdiff hinv (by positivity) (by positivity)
        _ = 8 * B₀ * Real.exp (-(π * |s|)) := by ring
  have hae_ne : ∀ᵐ s : ℝ ∂volume, s ≠ (0 : ℝ) := by rw [ae_iff]; simp
  -- Helper: on `strip`, `stripCompG w z = w(z.im) + ∫ (w(z.im - s) - w(z.im)) / sin(π(z.re + i s)) ds`
  have hsplit_strip : ∀ z ∈ strip,
      stripCompG w z = (w z.im : ℂ) +
        ∫ s : ℝ, ((w (z.im - s) - w z.im : ℝ) : ℂ) / Complex.sin (π * ((z.re : ℂ) + Complex.I * s)) := by
    intro z hz
    rw [stripCompG_eq_conv]
    have h1 : Integrable (fun s : ℝ => (w z.im : ℂ) / Complex.sin (π * ((z.re : ℂ) + Complex.I * s))) := by
      have := (integrable_inv_sin_strip hz.1 hz.2).const_mul (w z.im : ℂ)
      simpa [div_eq_mul_inv] using this
    have h2 : Integrable (fun s : ℝ => ((w (z.im - s) - w z.im : ℝ) : ℂ) / Complex.sin (π * ((z.re : ℂ) + Complex.I * s))) := by
      refine hdom_int.mono' ?_ ?_
      · exact ((Complex.continuous_ofReal.comp ((hw.continuous.comp (continuous_const.sub continuous_id)).sub
          continuous_const)).div
          (Complex.continuous_sin.comp (continuous_const.mul (continuous_const.add
            (continuous_const.mul Complex.continuous_ofReal))))
          (fun s => by
            have hmem : (z.re : ℂ) + Complex.I * s ∈ strip := ⟨by simp [hz.1], by simp [hz.2]⟩
            simpa using sin_arg_ne_zero (t := 0) hmem)).aestronglyMeasurable
      · filter_upwards [hae_ne] with s hs using hdom_bound z.re z.im s hs
    have hsum : (fun s : ℝ => (w (z.im - s) : ℂ) / Complex.sin (π * ((z.re : ℂ) + Complex.I * s))) =
        fun s : ℝ => (w z.im : ℂ) / Complex.sin (π * ((z.re : ℂ) + Complex.I * s)) +
          ((w (z.im - s) - w z.im : ℝ) : ℂ) / Complex.sin (π * ((z.re : ℂ) + Complex.I * s)) := by
      ext s; push_cast; ring
    rw [hsum, integral_add h1 h2]
    congr 1
    simp_rw [div_eq_mul_inv]
    rw [integral_const_mul, integral_inv_sin_strip hz.1 hz.2, mul_one]
  -- Helper: on `z.re = 0`, `Complex.I * fctThetaD w τ = ∫ (w(τ - s) - w τ) / sin(π(0 + i s)) ds`
  have hleft_rep : ∀ τ : ℝ,
      Complex.I * (fctThetaD w τ : ℂ) =
        ∫ s : ℝ, ((w (τ - s) - w τ : ℝ) : ℂ) / Complex.sin (π * ((0 : ℂ) + Complex.I * s)) := by
    intro τ
    unfold fctThetaD
    have hofR : ((∫ z : ℝ, (w (τ + z) - w τ) / Real.sinh (π * z) : ℝ) : ℂ) =
        ∫ z : ℝ, (((w (τ + z) - w τ) / Real.sinh (π * z) : ℝ) : ℂ) :=
      (integral_ofReal (𝕜 := ℂ)).symm
    rw [hofR, ← integral_const_mul,
      ← MeasureTheory.integral_neg_eq_self (fun z : ℝ => Complex.I * (((w (τ + z) - w τ) / Real.sinh (π * z) : ℝ) : ℂ))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    have hsin : Complex.sin (π * ((0 : ℂ) + Complex.I * s)) = Complex.I * (Real.sinh (π * s) : ℂ) := by
      rw [zero_add, show (π : ℂ) * (Complex.I * (s : ℂ)) = ((π * s : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.sin_mul_I, ← Complex.ofReal_sinh, mul_comm]
    rw [hsin, show τ + -s = τ - s by ring, show π * (-s) = -(π * s) by ring, Real.sinh_neg]
    by_cases hs : Real.sinh (π * s) = 0
    · simp [hs]
    · have hsC : (Real.sinh (π * s) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
      rw [Complex.ofReal_div, Complex.ofReal_neg]
      field_simp [hsC, Complex.I_ne_zero]
      rw [Complex.I_sq]
      ring
  have hright_rep : ∀ τ : ℝ,
      -(Complex.I * (fctThetaD w τ : ℂ)) =
        ∫ s : ℝ, ((w (τ - s) - w τ : ℝ) : ℂ) / Complex.sin (π * ((1 : ℂ) + Complex.I * s)) := by
    intro τ
    rw [hleft_rep τ, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    have hsin : Complex.sin (π * ((1 : ℂ) + Complex.I * s)) = -Complex.sin (π * ((0 : ℂ) + Complex.I * s)) := by
      rw [show (π : ℂ) * ((1 : ℂ) + Complex.I * s) = π * ((0 : ℂ) + Complex.I * s) + π by ring,
        Complex.sin_add_pi]
    rw [hsin, div_neg]
  -- Now prove `stripCompGExt w z = w(z.im) + ∫ (w(z.im - s) - w(z.im)) / sin(π(z.re + i s)) ds` for ALL `z ∈ closedStrip`!
  have hall_rep : ∀ z ∈ closedStrip,
      stripCompGExt w z = (w z.im : ℂ) +
        ∫ s : ℝ, ((w (z.im - s) - w z.im : ℝ) : ℂ) / Complex.sin (π * ((z.re : ℂ) + Complex.I * s)) := by
    intro z hz
    by_cases h0 : z.re ≤ 0
    · have hz0 : z.re = 0 := le_antisymm h0 hz.1
      unfold stripCompGExt
      rw [ite_eq_left_iff.mpr fun h => absurd h0 h, hz0, Complex.ofReal_zero, hleft_rep z.im]
    · by_cases h1 : 1 ≤ z.re
      · have hz1 : z.re = 1 := le_antisymm hz.2 h1
        unfold stripCompGExt
        rw [ite_eq_right_iff.mpr fun h => absurd h h0, ite_eq_left_iff.mpr fun h => absurd h1 h,
          hz1, Complex.ofReal_one, sub_eq_add_neg, hright_rep z.im]
      · have hmem : z ∈ strip := ⟨not_le.mp h0, not_le.mp h1⟩
        rw [stripCompGExt_eq_of_mem_strip hmem]
        exact hsplit_strip z hmem
  -- Dominated convergence as `z → ζ₀` within `closedStrip`!
  have hlim_int : Tendsto
      (fun z : ℂ => ∫ s : ℝ, ((w (z.im - s) - w z.im : ℝ) : ℂ) / Complex.sin (π * ((z.re : ℂ) + Complex.I * s)))
      (𝓝[closedStrip] ζ₀)
      (𝓝 (∫ s : ℝ, ((w (ζ₀.im - s) - w ζ₀.im : ℝ) : ℂ) / Complex.sin (π * ((ζ₀.re : ℂ) + Complex.I * s)))) := by
    refine tendsto_integral_filter_of_dominated_convergence dom ?_ ?_ hdom_int ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hcont_on : ContinuousOn
          (fun s : ℝ => ((w (z.im - s) - w z.im : ℝ) : ℂ) / Complex.sin (π * ((z.re : ℂ) + Complex.I * s)))
          ({0}ᶜ) := by
        refine (Complex.continuous_ofReal.comp ((hw.continuous.comp (continuous_const.sub continuous_id)).sub
          continuous_const)).continuousOn.div
          (Complex.continuous_sin.comp (continuous_const.mul (continuous_const.add
            (continuous_const.mul Complex.continuous_ofReal)))).continuousOn fun s hs => ?_
        have hsin_ge := norm_sin_ge_abs_sinh z.re s
        have hsh_pos : 0 < |Real.sinh (π * s)| := abs_pos.mpr (sinh_pi_ne_zero hs)
        exact norm_pos_iff.mp (lt_of_lt_of_le hsh_pos hsin_ge)
      have hmeas_c : AEStronglyMeasurable
          (fun s : ℝ => ((w (z.im - s) - w z.im : ℝ) : ℂ) / Complex.sin (π * ((z.re : ℂ) + Complex.I * s)))
          (volume.restrict ({0}ᶜ)) := hcont_on.aestronglyMeasurable isOpen_compl_singleton.measurableSet
      rwa [Measure.restrict_eq_self_of_ae_mem hae_ne] at hmeas_c
    · filter_upwards [self_mem_nhdsWithin] with z _
      filter_upwards [hae_ne] with s hs using hdom_bound z.re z.im s hs
    · filter_upwards [hae_ne] with s hs
      have hsin_ne : Complex.sin (π * ((ζ₀.re : ℂ) + Complex.I * s)) ≠ 0 := by
        have hsin_ge := norm_sin_ge_abs_sinh ζ₀.re s
        exact norm_pos_iff.mp (lt_of_lt_of_le (abs_pos.mpr (sinh_pi_ne_zero hs)) hsin_ge)
      have hnum : Tendsto (fun z : ℂ => ((w (z.im - s) - w z.im : ℝ) : ℂ)) (𝓝[closedStrip] ζ₀)
          (𝓝 ((w (ζ₀.im - s) - w ζ₀.im : ℝ) : ℂ)) :=
        ((Complex.continuous_ofReal.comp ((hw.continuous.comp (Complex.continuous_im.sub continuous_const)).sub
          (hw.continuous.comp Complex.continuous_im))).tendsto ζ₀).mono_left nhdsWithin_le_nhds
      have hden : Tendsto (fun z : ℂ => Complex.sin (π * ((z.re : ℂ) + Complex.I * s))) (𝓝[closedStrip] ζ₀)
          (𝓝 (Complex.sin (π * ((ζ₀.re : ℂ) + Complex.I * s)))) :=
        ((Complex.continuous_sin.comp (continuous_const.mul ((Complex.continuous_ofReal.comp Complex.continuous_re).add
          continuous_const))).tendsto ζ₀).mono_left nhdsWithin_le_nhds
      exact hnum.div hden hsin_ne
  have hlim_w : Tendsto (fun z : ℂ => (w z.im : ℂ)) (𝓝[closedStrip] ζ₀) (𝓝 (w ζ₀.im : ℂ)) :=
    ((Complex.continuous_ofReal.comp (hw.continuous.comp Complex.continuous_im)).tendsto ζ₀).mono_left nhdsWithin_le_nhds
  rw [ContinuousWithinAt, hall_rep ζ₀ hζ₀]
  exact (hlim_w.add hlim_int).congr' (eventually_nhdsWithin_of_forall fun z hz => (hall_rep z hz).symm)

/-- **Maximum modulus principle on the closed strip `S̄` for `stripCompGExt w`:**
if `‖w(τ) + i ϑ_D[w](τ)‖ ≤ M` for all `τ ∈ ℝ`, then `‖stripCompGExt w ζ‖ ≤ M` for all `ζ ∈ S̄`. -/
theorem norm_stripCompGExt_le {w : ℝ → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hsupp : Function.support w ⊆ Ioo (-R) R)
    (hbdry : ∀ τ : ℝ, ‖(w τ : ℂ) + Complex.I * (fctThetaD w τ : ℂ)‖ ≤ M)
    {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    ‖stripCompGExt w ζ‖ ≤ M := by
  have hw_supp : HasCompactSupport w :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
      (fun t ht => Ioo_subset_Icc_self (hsupp ht))
  have hcont : ContinuousOn (stripCompGExt w) closedStrip := continuousOn_stripCompGExt hw hw_supp
  have hdiff : DiffContOnCl ℂ (stripCompGExt w) strip := by
    refine ⟨?_, ?_⟩
    · exact (differentiableOn_stripCompG hw.continuous hw_supp).congr fun z hz => stripCompGExt_eq_of_mem_strip hz
    · have hcl : closure strip ⊆ closedStrip := by
        have hcl' : IsClosed closedStrip :=
          (isClosed_le continuous_const Complex.continuous_re).inter (isClosed_le Complex.continuous_re continuous_const)
        exact closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩) hcl'
      exact hcont.mono hcl
  -- Apply `PhragmenLindelof.vertical_strip` (or direct rectangle maximum principle)
  -- Direct rectangle maximum principle on `[0, 1] × [-T, T]` as `T → ∞` is 10 lines!
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- Choose `T > max (|ζ.im|) (R + 1)` large enough that `4 * ‖w‖₁ * exp(-π(T - R)) ≤ ε`
  set I1 : ℝ := ∫ t : ℝ, |w t|
  have hI1 : 0 ≤ I1 := integral_nonneg fun _ => abs_nonneg _
  obtain ⟨T, hT_gt, hT_im, hT_eps⟩ : ∃ T : ℝ, R + 1 ≤ T ∧ |ζ.im| ≤ T ∧
      4 * I1 * Real.exp (-(π * (T - R))) ≤ ε := by
    have htend : Tendsto (fun T : ℝ => 4 * I1 * Real.exp (-(π * (T - R)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun T : ℝ => -(π * (T - R))) atTop atBot := by
        have hlin : Tendsto (fun T : ℝ => π * (T - R)) atTop atTop :=
          (tendsto_atTop_add_const_right _ (-R) tendsto_id).const_mul_atTop Real.pi_pos
        exact tendsto_neg_atTop_atBot.comp hlin
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (4 * I1)
    obtain ⟨T₀, hT₀⟩ := (Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds hε)))
    refine ⟨max (max (R + 1) |ζ.im|) T₀, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), (hT₀ _ (le_max_right _ _)).le⟩
  -- Apply `Complex.norm_le_of_forall_mem_frontier_norm_le` to the open rectangle `(0, 1) × (-T, T)`
  set U : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ -T < z.im ∧ z.im < T}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hU_bdd : Bornology.IsBounded U := by
    refine isBounded_iff_forall_norm_le.mpr ⟨1 + T, fun z hz => ?_⟩
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + T := add_le_add (by rw [abs_of_pos hz.1]; exact hz.2.1.le)
          (abs_le.mpr ⟨hz.2.2.1.le, hz.2.2.2.le⟩)
  have hcl_sub : closure U ⊆ {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ -T ≤ z.im ∧ z.im ≤ T} := by
    refine closure_minimal (fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩) ?_
    exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const)))
  have hζ_cl : ζ ∈ closure U := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    set σ' : ℝ := min (max ζ.re (δ / 4)) (1 - δ / 4)
    -- Simpler: convex combination `(1 - s) ζ + s (1/2 + 0 i)` for tiny `s ∈ (0, 1)`
    set s : ℝ := min (1 / 2) (δ / (2 * (‖ζ - (1 / 2 : ℂ)‖ + 1)))
    have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
    have hs1 : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    refine ⟨((1 - s : ℝ) : ℂ) * ζ + (s : ℂ) * (1 / 2 : ℂ), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.div_ofNat_re, Complex.one_re]; nlinarith [hζ.1]
      · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.div_ofNat_re, Complex.one_re]; nlinarith [hζ.2]
      · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          Complex.div_ofNat_im, Complex.one_im, zero_div, mul_zero]
        have hT0 : 0 < T := by linarith
        nlinarith [(abs_le.mp hT_im).1]
      · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          Complex.div_ofNat_im, Complex.one_im, zero_div, mul_zero]
        have hT0 : 0 < T := by linarith
        nlinarith [(abs_le.mp hT_im).2]
    · rw [Complex.dist_eq, show ζ - (((1 - s : ℝ) : ℂ) * ζ + (s : ℂ) * (1 / 2 : ℂ)) =
        (s : ℂ) * (ζ - (1 / 2 : ℂ)) by push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs0]
      have hs_le : s ≤ δ / (2 * (‖ζ - (1 / 2 : ℂ)‖ + 1)) := min_le_right _ _
      calc s * ‖ζ - (1 / 2 : ℂ)‖ ≤ δ / (2 * (‖ζ - (1 / 2 : ℂ)‖ + 1)) * ‖ζ - (1 / 2 : ℂ)‖ :=
            mul_le_mul_of_nonneg_right hs_le (norm_nonneg _)
        _ < δ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg (ζ - (1 / 2 : ℂ))]
  have hdiffU : DiffContOnCl ℂ (stripCompGExt w) U :=
    hdiff.mono (fun z hz => ⟨hz.1, hz.2.1⟩)
  refine Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd hdiffU (fun z hz => ?_) hζ_cl
  have hzm := hcl_sub hz.1
  have hz_not : ¬ (0 < z.re ∧ z.re < 1 ∧ -T < z.im ∧ z.im < T) := by
    intro h
    exact hz.2 (hU_open.interior_eq.symm ▸ h)
  have hcase : z.re = 0 ∨ z.re = 1 ∨ |z.im| = T := by
    by_contra h
    push Not at h
    exact hz_not ⟨lt_of_le_of_ne hzm.1 (Ne.symm h.1), lt_of_le_of_ne hzm.2.1 h.2.1,
      lt_of_le_of_ne hzm.2.2.1 (fun he => h.2.2 (by rw [← he, abs_neg, abs_of_pos (by linarith)])),
      lt_of_le_of_ne hzm.2.2.2 (fun he => h.2.2 (by rw [he, abs_of_pos (by linarith)]))⟩
  rcases hcase with hre0 | hre1 | himT
  · have hzeq : z = (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hre0]
    rw [hzeq, stripCompGExt_left]
    linarith [hbdry z.im]
  · have hzeq : z = 1 + (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hre1]
    rw [hzeq, stripCompGExt_right]
    have hconj : (w z.im : ℂ) - Complex.I * (fctThetaD w z.im : ℂ) =
        star ((w z.im : ℂ) + Complex.I * (fctThetaD w z.im : ℂ)) := by
      simp [Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
    rw [hconj, norm_star]
    linarith [hbdry z.im]
  · have hbd := stripCompGExt_norm_le_of_large_im hw.continuous hR hsupp ⟨hzm.1, hzm.2.1⟩ (by linarith)
    rw [himT] at hbd
    linarith [hbd.trans hT_eps]

/-- **All-order global closed-strip bound** for `g_D^{(r)} = (-i)^r stripCompGExt (v^{(r)})`.
In particular, `r = 0, 1, 2` give the `g_D`, `g_D'`, and repaired `g_D''` strip bounds of `fct:comp-D` (1)
and `fct:ce-band`. -/
theorem norm_iteratedDeriv_stripCompG_le (r : ℕ) {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hsupp : Function.support v ⊆ Ioo (-R) R)
    (hbdry : ∀ τ : ℝ, |iteratedDeriv r v τ| + |iteratedDeriv r (fctThetaD v) τ| ≤ M)
    {ζ : ℂ} (hζ : ζ ∈ strip) :
    ‖iteratedDeriv r (stripCompG v) ζ‖ ≤ M := by
  have hv_supp : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
      (fun t ht => Ioo_subset_Icc_self (hsupp ht))
  have hsupp_r : Function.support (iteratedDeriv r v) ⊆ Ioo (-(R + 1)) (R + 1) := by
    intro t ht
    by_contra hnot
    have hev : v =ᶠ[𝓝 t] 0 := by
      have hmem : t ∈ (Icc (-R) R)ᶜ := by
        intro hcc
        exact hnot ⟨by linarith [hcc.1], by linarith [hcc.2]⟩
      filter_upwards [(isClosed_Icc.isOpen_compl).mem_nhds hmem] with s hs
      by_contra hne
      exact hs (Ioo_subset_Icc_self (hsupp hne))
    exact ht (by rw [hev.iteratedDeriv_eq r, iteratedDeriv_const_zero])
  rw [iteratedDeriv_stripCompG r hv hv_supp hζ, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul,
    ← stripCompGExt_eq_of_mem_strip hζ]
  refine norm_stripCompGExt_le (contDiff_iteratedDeriv_infty hv r) (R := R + 1) (by linarith) hM hsupp_r
    (fun τ => ?_) ⟨hζ.1.le, hζ.2.le⟩
  calc ‖((iteratedDeriv r v τ : ℝ) : ℂ) + Complex.I * (fctThetaD (iteratedDeriv r v) τ : ℂ)‖
      ≤ ‖((iteratedDeriv r v τ : ℝ) : ℂ)‖ + ‖Complex.I * (fctThetaD (iteratedDeriv r v) τ : ℂ)‖ := norm_add_le _ _
    _ = |iteratedDeriv r v τ| + |iteratedDeriv r (fctThetaD v) τ| := by
        rw [iteratedDeriv_fctThetaD hv hv_supp r, Complex.norm_real, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ M := hbdry τ

/-- The all-orders closed-strip bound of `fct:comp-D` (1) (Lemma FCT.3, `constant_terms_five.tex`):
the continuous extension `(-i)^r stripCompGExt (v^{(r)})` of `g_D^{(r)}` is bounded on all of `closedStrip` by
any bound `M` on the edge values `|v^{(r)}| + |ϑ_D^{(r)}|` (maximum principle). The paper's
`|g_D^{(r)}| ≤ C_r(K_4) τ_1^{2-r}` follows with `M` from `(fct:v-derivs)`, `(fct:th-inner)`, `(fct:th-tail)`. -/
theorem norm_iteratedDeriv_stripCompGExt_le (r : ℕ) {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hsupp : Function.support v ⊆ Ioo (-R) R)
    (hbdry : ∀ τ : ℝ, |iteratedDeriv r v τ| + |iteratedDeriv r (fctThetaD v) τ| ≤ M)
    {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    ‖(-Complex.I) ^ r * stripCompGExt (iteratedDeriv r v) ζ‖ ≤ M := by
  have hv_supp : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
      (fun t ht => Ioo_subset_Icc_self (hsupp ht))
  have hsupp_r : Function.support (iteratedDeriv r v) ⊆ Ioo (-(R + 1)) (R + 1) := by
    intro t ht
    by_contra hnot
    have hev : v =ᶠ[𝓝 t] 0 := by
      have hmem : t ∈ (Icc (-R) R)ᶜ := fun hcc => hnot ⟨by linarith [hcc.1], by linarith [hcc.2]⟩
      filter_upwards [(isClosed_Icc.isOpen_compl).mem_nhds hmem] with s hs
      by_contra hne; exact hs (Ioo_subset_Icc_self (hsupp hne))
    exact ht (by rw [hev.iteratedDeriv_eq r, iteratedDeriv_const_zero])
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
  refine norm_stripCompGExt_le (contDiff_iteratedDeriv_infty hv r) (R := R + 1) (by linarith) hM hsupp_r
    (fun τ => ?_) hζ
  calc ‖((iteratedDeriv r v τ : ℝ) : ℂ) + Complex.I * (fctThetaD (iteratedDeriv r v) τ : ℂ)‖
      ≤ ‖((iteratedDeriv r v τ : ℝ) : ℂ)‖ + ‖Complex.I * (fctThetaD (iteratedDeriv r v) τ : ℂ)‖ := norm_add_le _ _
    _ = |iteratedDeriv r v τ| + |iteratedDeriv r (fctThetaD v) τ| := by
        rw [iteratedDeriv_fctThetaD hv hv_supp r, Complex.norm_real, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ M := hbdry τ

/-! ### Interior strip bound `(fct:gD-int)` for all `r ≥ 0` via Cauchy's estimate -/

/-- Interior strip bound `(fct:gD-int)`: for `Re ζ ∈ [1/8, 7/8]` and `supp v ⊆ (-R, R)` with `0 < R ≤ 1/2`,
`‖g_D^{(r)}(ζ)‖ ≤ C_r * ‖v‖₁ * exp(-π |Im ζ|)`. -/
theorem norm_iteratedDeriv_stripCompG_interior (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : ℝ → ℝ} {R : ℝ}, ContDiff ℝ (⊤ : ℕ∞) v → 0 < R → R ≤ 1 / 2 →
      Function.support v ⊆ Ioo (-R) R →
      ∀ ζ : ℂ, 1 / 8 ≤ ζ.re → ζ.re ≤ 7 / 8 →
        ‖iteratedDeriv r (stripCompG v) ζ‖ ≤ C * (∫ t : ℝ, |v t|) * Real.exp (-(π * |ζ.im|)) := by
  -- On `Re w ∈ [1/16, 15/16]`, `sin(π Re w) ≥ sin(π/16) > 0`, so `‖g_D(w)‖ ≤ (2 / sin(π/16)) * e^{π R} * ‖v‖₁ * e^{-π|Im w|}`.
  -- Then Cauchy's estimate on `closedBall ζ (1/16)` gives the bound for all `r ≥ 0`!
  set s0 : ℝ := Real.sin (π / 16)
  have hs0 : 0 < s0 := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  refine ⟨(r.factorial : ℝ) * (16 : ℝ) ^ r * (2 / s0) * Real.exp (π * (9 / 16)), by positivity,
    fun {v R} hv hR0 hR12 hsupp ζ hre1 hre2 => ?_⟩
  have hv_supp : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
      (fun t ht => Ioo_subset_Icc_self (hsupp ht))
  have hint_v : Integrable (fun t : ℝ => |v t|) :=
    hv.continuous.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
        (fun t ht => Ioo_subset_Icc_self (hsupp (by simpa using ht))))
  have hI1_nn : 0 ≤ ∫ t : ℝ, |v t| := integral_nonneg fun _ => abs_nonneg _
  have hball_sub : Metric.closedBall ζ (1 / 16) ⊆ strip := by
    intro w hw
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have hre := (Complex.abs_re_le_norm (w - ζ)).trans hw
    rw [Complex.sub_re, abs_le] at hre
    exact ⟨by linarith, by linarith⟩
  have hdiff_ball : DiffContOnCl ℂ (stripCompG v) (Metric.ball ζ (1 / 16)) := by
    have hdiff := differentiableOn_stripCompG hv.continuous hv_supp
    refine ⟨hdiff.mono (Metric.ball_subset_closedBall.trans hball_sub), ?_⟩
    rw [closure_ball ζ (by norm_num)]
    exact (hdiff.mono hball_sub).continuousOn
  have hsphere : ∀ w ∈ Metric.sphere ζ (1 / 16),
      ‖stripCompG v w‖ ≤ (2 / s0 * Real.exp (π * (9 / 16)) * (∫ t : ℝ, |v t|)) * Real.exp (-(π * |ζ.im|)) := by
    intro w hw
    rw [Metric.mem_sphere, Complex.dist_eq] at hw
    have hre := (Complex.abs_re_le_norm (w - ζ)).trans hw.le
    have him := (Complex.abs_im_le_norm (w - ζ)).trans hw.le
    rw [Complex.sub_re, abs_le] at hre
    rw [Complex.sub_im, abs_le] at him
    have hsin_w : s0 ≤ Real.sin (π * w.re) := by
      rcases le_or_gt w.re (1 / 2) with hw12 | hw12
      · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
      · rw [← Real.sin_pi_sub (π * w.re), show π - π * w.re = π * (1 - w.re) by ring]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
    unfold stripCompG
    calc ‖∫ t : ℝ, (v t : ℂ) / Complex.sin (π * (w - Complex.I * t))‖
        ≤ ∫ t : ℝ, ‖(v t : ℂ) / Complex.sin (π * (w - Complex.I * t))‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (2 / s0 * Real.exp (π * (9 / 16)) * Real.exp (-(π * |ζ.im|))) * |v t| := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (hint_v.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
          by_cases ht : t ∈ Ioo (-R) R
          · dsimp only
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, mul_comm |v t|]
            have hk := kernel_norm_le (ζ := w) t hs0 (Real.sin_le_one _) hsin_w
            rw [norm_inv] at hk
            have ht_abs : |t| ≤ 1 / 2 := (abs_le.mpr ⟨ht.1.le, ht.2.le⟩).trans hR12
            have him_diff : |ζ.im| - 9 / 16 ≤ |w.im - t| := by
              have h1 : |ζ.im| - |w.im| ≤ |ζ.im - w.im| := abs_sub_abs_le_abs_sub _ _
              have h2 : |w.im| - |t| ≤ |w.im - t| := abs_sub_abs_le_abs_sub _ _
              have h3 : |ζ.im - w.im| ≤ 1 / 16 := by rw [abs_sub_comm]; exact abs_le.mpr him
              linarith
            have hexp : Real.exp (-(π * |w.im - t|)) ≤ Real.exp (π * (9 / 16)) * Real.exp (-(π * |ζ.im|)) := by
              rw [← Real.exp_add]
              exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
            have hle : ‖Complex.sin (π * (w - Complex.I * t))‖⁻¹ ≤
                2 / s0 * Real.exp (π * (9 / 16)) * Real.exp (-(π * |ζ.im|)) := by
              calc ‖Complex.sin (π * (w - Complex.I * t))‖⁻¹
                  ≤ 2 / s0 * Real.exp (-(π * |w.im - t|)) := hk
                _ ≤ 2 / s0 * (Real.exp (π * (9 / 16)) * Real.exp (-(π * |ζ.im|))) :=
                    mul_le_mul_of_nonneg_left hexp (by positivity)
                _ = 2 / s0 * Real.exp (π * (9 / 16)) * Real.exp (-(π * |ζ.im|)) := by ring
            exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
          · have hvt : v t = 0 := by by_contra hne; exact ht (hsupp hne)
            simp [hvt]
      _ = (2 / s0 * Real.exp (π * (9 / 16)) * (∫ t : ℝ, |v t|)) * Real.exp (-(π * |ζ.im|)) := by
          rw [integral_const_mul]; ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (n := r) (R := 1 / 16) (by norm_num) hdiff_ball hsphere
  refine hcauchy.trans (le_of_eq ?_)
  rw [one_div, inv_pow, div_inv_eq_mul]
  ring

/-! ### Boundary tail bound `(fct:th-tail)` for `|t| ≥ 12 τ₁` and all `r ≥ 0` -/

/-- Boundary tail bound `(fct:th-tail)`: for `supp v ⊆ (-10 τ₁, 10 τ₁)` with `0 < τ₁ ≤ 1/20` and `|t| ≥ 12 τ₁`,
`|ϑ_D^{(r)}(t)| ≤ C_r * ‖v‖₁ * |t|^{-1-r} * exp(-(π/2) |t|)`. -/
theorem abs_iteratedDeriv_fctThetaD_tail (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : ℝ → ℝ} {τ₁ : ℝ}, ContDiff ℝ (⊤ : ℕ∞) v → 0 < τ₁ → τ₁ ≤ 1 / 20 →
      Function.support v ⊆ Ioo (-10 * τ₁) (10 * τ₁) →
      ∀ t : ℝ, 12 * τ₁ ≤ |t| →
        |iteratedDeriv r (fctThetaD v) t| ≤
          C * (∫ s : ℝ, |v s|) * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) := by
  -- Use Cauchy's estimate on the holomorphic extension `z ↦ ∫ v(s) / sinh(π(s - z)) ds` around `z = (t : ℂ)`
  -- with radius `ρ = min (|t| / 12) (1 / 4)`!
  -- On `sphere (t : ℂ) ρ`: for `|s| ≤ 10 τ₁` and `|t| ≥ 12 τ₁`, `|Re(s - z)| ≥ |t| - |s| - ρ ≥ |t| / 12 > 0`
  -- AND `|Im(s - z)| ≤ ρ ≤ 1/4`, so `‖sinh(π(s - z))‖ ≥ sinh(π |Re(s - z)|) ≥ ...`!
  --Wait: `‖sinh(x + i y)‖² = sinh² x + sin² y ≥ sinh² x` for ALL `x, y ∈ ℝ`!
  -- So we don't even need `|y| ≤ 1/4` for the lower bound on `‖sinh‖`!
  -- Wait: for `|t| ≥ 1`, `ρ = 1/4` gives `|Re(s - z)| ≥ |t| - 1/2 - 1/4 = |t| - 3/4 ≥ |t| / 4` (or `|t| - 3/4`),
  -- giving `1 / sinh(π |Re(s - z)|) ≤ 4 e^{-π(|t| - 3/4)} = 4 e^{3π/4} e^{-π|t|} ≤ C_r |t|^{-1-r} e^{-(π/2)|t|}`!
  -- For `12 τ₁ ≤ |t| ≤ 1`, `ρ = |t| / 12` gives `|Re(s - z)| ≥ |t|/12`, so `1 / sinh(π |Re(s - z)|) ≤ 12 / (π |t|)`,
  -- and Cauchy gives `r! (12/|t|)^r * (12/(π|t|)) = C_r |t|^{-1-r} ≤ C_r e^{π/2} |t|^{-1-r} e^{-(π/2)|t|}`!
  -- Let's bound `x^{r+1} e^{-(π/2) x}` for `x ≥ 0` via `((r+1)! / (π/2)^{r+1})`.
  set C_small : ℝ := (r.factorial : ℝ) * (12 : ℝ) ^ r * (12 / π) * Real.exp (π / 2)
  set C_large : ℝ := (r.factorial : ℝ) * (12 : ℝ) ^ r * (4 * Real.exp (3 * π / 4)) *
      (((r + 1).factorial : ℝ) * (2 / π) ^ (r + 1))
  refine ⟨max C_small C_large, by positivity, fun {v τ₁} hv hτ₁ hτ₁_le hsupp t ht => ?_⟩
  have ht_pos : 0 < |t| := lt_of_lt_of_le (by positivity) ht
  have hv_supp : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -10 * τ₁) (b := 10 * τ₁))
      (fun s hs => Ioo_subset_Icc_self (hsupp hs))
  have hint_v : Integrable (fun s : ℝ => |v s|) :=
    hv.continuous.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -10 * τ₁) (b := 10 * τ₁))
        (fun s hs => Ioo_subset_Icc_self (hsupp (by simpa using hs))))
  have hI1_nn : 0 ≤ ∫ s : ℝ, |v s| := integral_nonneg fun _ => abs_nonneg _
  -- Define the holomorphic extension `F(z) = ∫ v(s) / sinh(π(s - z)) ds` on `ball (t : ℂ) (|t| / 6)`
  let F : ℂ → ℂ := fun z => ∫ s : ℝ, (v s : ℂ) / Complex.sinh (π * ((s : ℂ) - z))
  -- Lower bound `‖sinh w‖ ≥ |sinh(w.re)|` for all `w : ℂ`
  have hnorm_sinh_ge : ∀ w : ℂ, |Real.sinh w.re| ≤ ‖Complex.sinh w‖ := by
    intro w
    have hsq : ‖Complex.sinh w‖ ^ 2 = Real.sinh w.re ^ 2 + Real.sin w.im ^ 2 := by
      have h1 : Complex.sinh w = ((Real.sinh w.re * Real.cos w.im : ℝ) : ℂ) +
          ((Real.cosh w.re * Real.sin w.im : ℝ) : ℂ) * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im w]
        rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
          ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
        push_cast; ring
      rw [Complex.sq_norm, Complex.normSq_apply, h1]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im, zero_add]
      nlinarith [Real.cosh_sq w.re, Real.sin_sq_add_cos_sq w.im]
    have h2 : |Real.sinh w.re| ^ 2 ≤ ‖Complex.sinh w‖ ^ 2 := by
      rw [sq_abs, hsq]; nlinarith [sq_nonneg (Real.sin w.im)]
    have h3 := sq_le_sq.mp h2
    rwa [abs_abs, abs_of_nonneg (norm_nonneg _)] at h3
  -- On `U = ball (t : ℂ) (|t| / 8)`: for `s ∈ (-10 τ₁, 10 τ₁)` and `z ∈ U`, `|s - z.re| ≥ |t| / 24 > 0`
  set ρ₀ : ℝ := |t| / 8 with hρ₀_def
  have hρ₀_pos : 0 < ρ₀ := by positivity
  have hsep : ∀ z ∈ Metric.closedBall (t : ℂ) ρ₀, ∀ s ∈ Ioo (-10 * τ₁) (10 * τ₁),
      |t| / 24 ≤ |s - z.re| := by
    intro z hz s hs
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    have hre := (Complex.abs_re_le_norm (z - (t : ℂ))).trans hz
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    have hs_abs : |s| ≤ 10 * τ₁ := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h1 : |t| - |z.re - t| ≤ |z.re| := by
      have := abs_sub_abs_le_abs_sub t z.re
      rw [abs_sub_comm] at this; linarith
    have h2 : |z.re| - |s| ≤ |s - z.re| := by
      have := abs_sub_abs_le_abs_sub z.re s
      rw [abs_sub_comm] at this; linarith
    linarith [hρ₀_def]
  have hF_diff : DifferentiableOn ℂ F (Metric.ball (t : ℂ) ρ₀) := by
    obtain ⟨B, hB⟩ := hv_supp.exists_bound_of_continuous hv.continuous
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    have hF_eq : ∀ z ∈ Metric.ball (t : ℂ) ρ₀,
        F z = ∫ s : ℝ, (Ioo (-10 * τ₁) (10 * τ₁)).indicator (fun u => (v u : ℂ) / Complex.sinh (π * ((u : ℂ) - z))) s := by
      intro z _
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      by_cases hs : s ∈ Ioo (-10 * τ₁) (10 * τ₁)
      · rw [Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem hs]
        have hvs : v s = 0 := by by_contra hne; exact hs (hsupp hne)
        simp [hvs]
    refine (CtOuter.differentiableOn_integral_param Metric.isOpen_ball
      (Φ := fun z s => (Ioo (-10 * τ₁) (10 * τ₁)).indicator (fun u => (v u : ℂ) / Complex.sinh (π * ((u : ℂ) - z))) s)
      ?_ ?_ ?_).congr (fun z hz => hF_eq z hz)
    · intro z hz
      have hcont_on : ContinuousOn (fun s : ℝ => (v s : ℂ) / Complex.sinh (π * ((s : ℂ) - z))) (Ioo (-10 * τ₁) (10 * τ₁)) := by
        refine (Complex.continuous_ofReal.comp hv.continuous).continuousOn.div
          (Complex.continuous_sinh.comp (continuous_const.mul (Complex.continuous_ofReal.sub continuous_const))).continuousOn
          fun s hs => ?_
        have h1 := hnorm_sinh_ge (π * ((s : ℂ) - z))
        have hre : ((π : ℂ) * ((s : ℂ) - z)).re = π * (s - z.re) := by simp [Complex.mul_re]
        rw [hre] at h1
        have hsep' := hsep z (Metric.ball_subset_closedBall hz) s hs
        have hpos : 0 < |Real.sinh (π * (s - z.re))| := abs_pos.mpr (sinh_pi_ne_zero (fun h => by rw [h, abs_zero] at hsep'; linarith))
        exact norm_pos_iff.mp (lt_of_lt_of_le hpos h1)
      exact (aestronglyMeasurable_indicator_iff measurableSet_Ioo).mpr (hcont_on.aestronglyMeasurable measurableSet_Ioo)
    · refine Filter.Eventually.of_forall fun s => ?_
      by_cases hs : s ∈ Ioo (-10 * τ₁) (10 * τ₁)
      · simp_rw [Set.indicator_of_mem hs]
        refine (differentiableOn_const _).div
          (Complex.differentiable_sinh.comp_differentiableOn
            ((differentiableOn_const _).mul ((differentiableOn_const _).sub differentiableOn_id)))
          fun z hz => ?_
        have h1 := hnorm_sinh_ge (π * ((s : ℂ) - z))
        have hre : ((π : ℂ) * ((s : ℂ) - z)).re = π * (s - z.re) := by simp [Complex.mul_re]
        rw [hre] at h1
        have hsep' := hsep z (Metric.ball_subset_closedBall hz) s hs
        have hpos : 0 < |Real.sinh (π * (s - z.re))| := abs_pos.mpr (sinh_pi_ne_zero (fun h => by rw [h, abs_zero] at hsep'; linarith))
        exact norm_pos_iff.mp (lt_of_lt_of_le hpos h1)
      · simp_rw [Set.indicator_of_notMem hs]
        exact differentiableOn_const _
    · intro w₀ hw₀
      obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball w₀ hw₀
      refine ⟨r, hr0, fun s => (Ioo (-10 * τ₁) (10 * τ₁)).indicator (fun _ => B * (24 / (π * |t|))) s,
        (integrableOn_const (hs := measure_Ioo_lt_top.ne)).integrable_indicator measurableSet_Ioo,
        Filter.Eventually.of_forall fun s z hz => ?_⟩
      have hz_ball := hrsub hz
      dsimp only
      by_cases hs : s ∈ Ioo (-10 * τ₁) (10 * τ₁)
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, norm_div, Complex.norm_real, div_eq_mul_inv]
        have h1 := hnorm_sinh_ge (π * ((s : ℂ) - z))
        have hre : ((π : ℂ) * ((s : ℂ) - z)).re = π * (s - z.re) := by simp [Complex.mul_re]
        rw [hre] at h1
        have hsep' := hsep z (Metric.ball_subset_closedBall hz_ball) s hs
        have hlin : π * (|t| / 24) ≤ |Real.sinh (π * (s - z.re))| := by
          have h2 : π * |s - z.re| ≤ |Real.sinh (π * (s - z.re))| := by
            rcases le_or_gt 0 (s - z.re) with h | h
            · rw [abs_of_nonneg h, abs_of_nonneg (le_trans (by positivity) (self_le_sinh_nonneg (by positivity)))]
              exact self_le_sinh_nonneg (by positivity)
            · rw [abs_of_neg h, abs_of_neg (sinh_neg_of_neg (by nlinarith [Real.pi_pos])), ← Real.sinh_neg,
                show -(π * (s - z.re)) = π * -(s - z.re) by ring]
              exact self_le_sinh_nonneg (by nlinarith [Real.pi_pos])
          nlinarith [Real.pi_pos]
        have hinv : ‖Complex.sinh (π * ((s : ℂ) - z))‖⁻¹ ≤ 24 / (π * |t|) := by
          have := inv_anti₀ (by positivity : 0 < π * (|t| / 24)) (hlin.trans h1)
          refine this.trans (le_of_eq ?_); field_simp [Real.pi_ne_zero, ht_pos.ne']
        exact mul_le_mul (hB s) hinv (by positivity) hB0
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, norm_zero]
  -- On `(t - ρ₀, t + ρ₀) ⊂ ℝ`, `F (x : ℂ) = (fctThetaD v x : ℂ)`!
  have hF_real : ∀ x : ℝ, |x - t| < ρ₀ → F (x : ℂ) = (fctThetaD v x : ℂ) := by
    intro x hx
    have hvx : v x = 0 := by
      by_contra hne
      have hmem := hsupp hne
      have hx_abs : |x| < 10 * τ₁ := abs_lt.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      have htri : |t| - |x| ≤ |x - t| := by
        have := abs_sub_abs_le_abs_sub t x
        rw [abs_sub_comm] at this; linarith
      linarith [hρ₀_def]
    unfold F fctThetaD
    have hofR : ((∫ z : ℝ, (v (x + z) - v x) / Real.sinh (π * z) : ℝ) : ℂ) =
        ∫ z : ℝ, (((v (x + z) - v x) / Real.sinh (π * z) : ℝ) : ℂ) :=
      (integral_ofReal (𝕜 := ℂ)).symm
    rw [hofR]
    have hshift : ∫ z : ℝ, (((v (x + z) - v x) / Real.sinh (π * z) : ℝ) : ℂ) =
        ∫ s : ℝ, ((v s / Real.sinh (π * (s - x)) : ℝ) : ℂ) := by
      rw [← integral_add_left_eq_self (μ := volume) (fun s : ℝ => ((v s / Real.sinh (π * (s - x)) : ℝ) : ℂ)) x]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp [hvx, add_sub_cancel_left]
    rw [hshift]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    rw [Complex.ofReal_div, Complex.ofReal_sinh]
    congr 2; push_cast; ring
  -- Hence `iteratedDeriv r (fctThetaD v) t = (iteratedDeriv r F (t : ℂ))` in norm!
  have hF_ana : ∀ k : ℕ, AnalyticOnNhd ℂ (iteratedDeriv k F) (Metric.ball (t : ℂ) ρ₀) := by
    intro k
    induction k with
    | zero => simpa using hF_diff.analyticOnNhd Metric.isOpen_ball
    | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      exact (ih z hz).deriv
  have hderiv_eq : ((iteratedDeriv r (fctThetaD v) t : ℝ) : ℂ) = iteratedDeriv r F (t : ℂ) := by
    suffices ∀ (k : ℕ) (x : ℝ), |x - t| < ρ₀ → ((iteratedDeriv k (fctThetaD v) x : ℝ) : ℂ) = iteratedDeriv k F (x : ℂ) from
      this r t (by simp [hρ₀_pos])
    intro k
    induction k with
    | zero => intro x hx; simpa using (hF_real x hx).symm
    | succ k ih =>
      intro x hx
      have hx_ball : (x : ℂ) ∈ Metric.ball (t : ℂ) ρ₀ := by
        rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hx
      have hF_k_diff : DifferentiableAt ℂ (iteratedDeriv k F) (x : ℂ) :=
        (hF_ana k (x : ℂ) hx_ball).differentiableAt
      have h1 : HasDerivAt (fun y : ℝ => iteratedDeriv k F (y : ℂ)) (iteratedDeriv (k + 1) F (x : ℂ)) x := by
        rw [iteratedDeriv_succ]
        simpa using hF_k_diff.hasDerivAt.comp_ofReal
      have h2 : HasDerivAt (fun y : ℝ => ((iteratedDeriv k (fctThetaD v) y : ℝ) : ℂ))
          ((iteratedDeriv (k + 1) (fctThetaD v) x : ℝ) : ℂ) x := by
        rw [iteratedDeriv_succ]
        have hcd := contDiff_iteratedDeriv_infty (contDiff_fctThetaD hv hv_supp) k
        exact ((hcd.differentiable (by simp) x).hasDerivAt).ofReal_comp
      have hev : (fun y : ℝ => ((iteratedDeriv k (fctThetaD v) y : ℝ) : ℂ)) =ᶠ[𝓝 x]
          (fun y : ℝ => iteratedDeriv k F (y : ℂ)) := by
        filter_upwards [(isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const).mem_nhds hx] with y hy
        exact ih y hy
      exact (h2.congr_of_eventuallyEq hev.symm).unique h1
  -- Now apply Cauchy's estimate on `ball (t : ℂ) ρ` with `ρ = |t| / 12` (when `|t| ≤ 1`) or `ρ = 1 / 4` (when `1 < |t|`)!
  have hnorm_eq : |iteratedDeriv r (fctThetaD v) t| = ‖iteratedDeriv r F (t : ℂ)‖ := by
    rw [← hderiv_eq, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm_eq]
  rcases le_or_gt |t| 1 with ht1 | ht1
  · -- Case `12 τ₁ ≤ |t| ≤ 1`: Cauchy on `ball (t : ℂ) (|t| / 12)`
    set ρ : ℝ := |t| / 12 with hρ_def
    have hρ_pos : 0 < ρ := by positivity
    have hball_sub : Metric.closedBall (t : ℂ) ρ ⊆ Metric.ball (t : ℂ) ρ₀ :=
      Metric.closedBall_subset_ball (by dsimp [ρ, ρ₀]; linarith)
    have hdiff_ρ : DiffContOnCl ℂ F (Metric.ball (t : ℂ) ρ) := by
      refine ⟨hF_diff.mono (Metric.ball_subset_closedBall.trans hball_sub), ?_⟩
      rw [closure_ball (t : ℂ) hρ_pos.ne']
      exact (hF_diff.mono hball_sub).continuousOn
    have hsphere : ∀ z ∈ Metric.sphere (t : ℂ) ρ, ‖F z‖ ≤ (12 / (π * |t|)) * (∫ s : ℝ, |v s|) := by
      intro z hz
      rw [Metric.mem_sphere, Complex.dist_eq] at hz
      have hre := (Complex.abs_re_le_norm (z - (t : ℂ))).trans hz.le
      rw [Complex.sub_re, Complex.ofReal_re] at hre
      unfold F
      calc ‖∫ s : ℝ, (v s : ℂ) / Complex.sinh (π * ((s : ℂ) - z))‖
          ≤ ∫ s : ℝ, ‖(v s : ℂ) / Complex.sinh (π * ((s : ℂ) - z))‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ s : ℝ, (12 / (π * |t|)) * |v s| := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              (hint_v.const_mul _) (Filter.Eventually.of_forall fun s => ?_)
            by_cases hs : s ∈ Ioo (-10 * τ₁) (10 * τ₁)
            · dsimp only
              rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, mul_comm |v s|]
              have h1 := hnorm_sinh_ge (π * ((s : ℂ) - z))
              have hre' : ((π : ℂ) * ((s : ℂ) - z)).re = π * (s - z.re) := by simp [Complex.mul_re]
              rw [hre'] at h1
              have hs_abs : |s| ≤ 10 * τ₁ := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
              have hsep12 : |t| / 12 ≤ |s - z.re| := by
                have ha : |t| - |z.re - t| ≤ |z.re| := by
                  have := abs_sub_abs_le_abs_sub t z.re; rw [abs_sub_comm] at this; linarith
                have hb : |z.re| - |s| ≤ |s - z.re| := by
                  have := abs_sub_abs_le_abs_sub z.re s; rw [abs_sub_comm] at this; linarith
                linarith [hρ_def]
              have hlin : π * (|t| / 12) ≤ |Real.sinh (π * (s - z.re))| := by
                have h2 : π * |s - z.re| ≤ |Real.sinh (π * (s - z.re))| := by
                  rcases le_or_gt 0 (s - z.re) with h | h
                  · rw [abs_of_nonneg h, abs_of_nonneg (le_trans (by positivity) (self_le_sinh_nonneg (by positivity)))]
                    exact self_le_sinh_nonneg (by positivity)
                  · rw [abs_of_neg h, abs_of_neg (sinh_neg_of_neg (by nlinarith [Real.pi_pos])), ← Real.sinh_neg,
                      show -(π * (s - z.re)) = π * -(s - z.re) by ring]
                    exact self_le_sinh_nonneg (by nlinarith [Real.pi_pos])
                nlinarith [Real.pi_pos]
              have hinv : ‖Complex.sinh (π * ((s : ℂ) - z))‖⁻¹ ≤ 12 / (π * |t|) := by
                have := inv_anti₀ (by positivity : 0 < π * (|t| / 12)) (hlin.trans h1)
                refine this.trans (le_of_eq ?_); field_simp [Real.pi_ne_zero, ht_pos.ne']
              exact mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
            · have hvs : v s = 0 := by by_contra hne; exact hs (hsupp hne)
              simp [hvs]
        _ = (12 / (π * |t|)) * (∫ s : ℝ, |v s|) := integral_const_mul _ _
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (n := r) (R := ρ) hρ_pos hdiff_ρ hsphere
    have hexp1 : (1 : ℝ) ≤ Real.exp (π / 2) * Real.exp (-(π / 2) * |t|) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [Real.pi_pos])
    have hzpow : |t| ^ (-(1 + (r : ℤ))) = (|t| ^ r * |t|)⁻¹ := by
      rw [zpow_neg, zpow_add₀ ht_pos.ne', zpow_one, zpow_natCast, mul_comm, mul_inv]
    calc ‖iteratedDeriv r F (t : ℂ)‖
        ≤ (r.factorial : ℝ) * ((12 / (π * |t|)) * (∫ s : ℝ, |v s|)) / ρ ^ r := hcauchy
      _ = (r.factorial : ℝ) * (12 : ℝ) ^ r * (12 / π) * (∫ s : ℝ, |v s|) * |t| ^ (-(1 + (r : ℤ))) * 1 := by
          rw [hzpow]; dsimp [ρ]; rw [div_pow]; field_simp [Real.pi_ne_zero, ht_pos.ne']
      _ ≤ (r.factorial : ℝ) * (12 : ℝ) ^ r * (12 / π) * (∫ s : ℝ, |v s|) * |t| ^ (-(1 + (r : ℤ))) *
            (Real.exp (π / 2) * Real.exp (-(π / 2) * |t|)) :=
          mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = C_small * (∫ s : ℝ, |v s|) * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) := by
          dsimp [C_small]; ring
      _ ≤ max C_small C_large * (∫ s : ℝ, |v s|) * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) := by
          gcongr; exact le_max_left _ _
  · -- Case `1 < |t|`: Cauchy on `ball (t : ℂ) (1 / 4)`? Wait: `ρ₀ = |t|/8` could be `< 1/4` when `1 < |t| < 2`!
    -- Instead use `ρ = 1 / 12`! Since `|t| > 1`, `1/12 < |t|/8 = ρ₀`, and `|s - z.re| ≥ |t| - 1/2 - 1/12 = |t| - 7/12 ≥ 5/12`
    -- Wait: to use `abs_inv_sinh_le_exp` (which needs `1 ≤ |s - z.re|`), note `sinh(π x) ≥ e^{π x} / 4` holds for `x ≥ 1/3`
    -- (since `π/3 > 1` so `e^{π x} > e > 2.7` and `sinh(π x) = (e^{πx} - e^{-πx})/2 ≥ e^{πx}/4` whenever `e^{2πx} ≥ 2`, i.e. `x ≥ 1/3`!).
    -- Even better: `|s - z.re| ≥ |t| - 1/2 - 1/12 = |t| - 7/12 > 5/12 > 1/3`!
    set ρ : ℝ := 1 / 12
    have hρ_pos : 0 < ρ := by positivity
    have hball_sub : Metric.closedBall (t : ℂ) ρ ⊆ Metric.ball (t : ℂ) ρ₀ :=
      Metric.closedBall_subset_ball (by dsimp [ρ, ρ₀]; linarith)
    have hdiff_ρ : DiffContOnCl ℂ F (Metric.ball (t : ℂ) ρ) := by
      refine ⟨hF_diff.mono (Metric.ball_subset_closedBall.trans hball_sub), ?_⟩
      rw [closure_ball (t : ℂ) hρ_pos.ne']
      exact (hF_diff.mono hball_sub).continuousOn
    have hsphere : ∀ z ∈ Metric.sphere (t : ℂ) ρ,
        ‖F z‖ ≤ (4 * Real.exp (3 * π / 4) * Real.exp (-(π * |t|))) * (∫ s : ℝ, |v s|) := by
      intro z hz
      rw [Metric.mem_sphere, Complex.dist_eq] at hz
      have hre := (Complex.abs_re_le_norm (z - (t : ℂ))).trans hz.le
      rw [Complex.sub_re, Complex.ofReal_re] at hre
      unfold F
      calc ‖∫ s : ℝ, (v s : ℂ) / Complex.sinh (π * ((s : ℂ) - z))‖
          ≤ ∫ s : ℝ, ‖(v s : ℂ) / Complex.sinh (π * ((s : ℂ) - z))‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ s : ℝ, (4 * Real.exp (3 * π / 4) * Real.exp (-(π * |t|))) * |v s| := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              (hint_v.const_mul _) (Filter.Eventually.of_forall fun s => ?_)
            by_cases hs : s ∈ Ioo (-10 * τ₁) (10 * τ₁)
            · dsimp only
              rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, mul_comm |v s|]
              have h1 := hnorm_sinh_ge (π * ((s : ℂ) - z))
              have hre' : ((π : ℂ) * ((s : ℂ) - z)).re = π * (s - z.re) := by simp [Complex.mul_re]
              rw [hre'] at h1
              have hs_abs : |s| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1, hτ₁_le], by linarith [hs.2, hτ₁_le]⟩
              have hsep_lg : |t| - 3 / 4 ≤ |s - z.re| := by
                have ha : |t| - |z.re - t| ≤ |z.re| := by
                  have := abs_sub_abs_le_abs_sub t z.re; rw [abs_sub_comm] at this; linarith
                have hb : |z.re| - |s| ≤ |s - z.re| := by
                  have := abs_sub_abs_le_abs_sub z.re s; rw [abs_sub_comm] at this; linarith
                dsimp [ρ] at hre; linarith
              -- `π * |s - z.re| ≥ π / 4`? Wait: `|t| - 3/4 ≥ 1/4` and `π/4 < 1`, actually `|s - z.re| ≥ |t| - 7/12 > 5/12`,
              -- so `π * |s - z.re| ≥ 5π/12 > 1`! Hence `e^{π|s-z.re|} ≥ 2` and `sinh ≥ e^{π|s-z.re|}/4`!
              have hsep_512 : 5 / 12 ≤ |s - z.re| := by
                have ha : |t| - |z.re - t| ≤ |z.re| := by
                  have := abs_sub_abs_le_abs_sub t z.re; rw [abs_sub_comm] at this; linarith
                have hb : |z.re| - |s| ≤ |s - z.re| := by
                  have := abs_sub_abs_le_abs_sub z.re s; rw [abs_sub_comm] at this; linarith
                dsimp [ρ] at hre; linarith
              have hge1 : 1 ≤ π * |s - z.re| := by nlinarith [Real.pi_gt_three]
              have hsh_ge : Real.exp (π * |s - z.re|) / 4 ≤ |Real.sinh (π * (s - z.re))| := by
                have habs : |Real.sinh (π * (s - z.re))| = Real.sinh (π * |s - z.re|) := by
                  rcases le_or_gt 0 (s - z.re) with h | h
                  · rw [abs_of_nonneg h, abs_of_nonneg (le_trans (by positivity) (self_le_sinh_nonneg (by positivity)))]
                  · rw [abs_of_neg h, abs_of_neg (sinh_neg_of_neg (by nlinarith [Real.pi_pos])), ← Real.sinh_neg]; ring_nf
                rw [habs, Real.sinh_eq]
                have hE : 2 ≤ Real.exp (π * |s - z.re|) := by linarith [Real.add_one_le_exp (π * |s - z.re|)]
                have hinv : Real.exp (-(π * |s - z.re|)) ≤ Real.exp (π * |s - z.re|) / 2 := by
                  rw [Real.exp_neg, le_div_iff₀ two_pos, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _)]; nlinarith
                linarith
              have hinv : ‖Complex.sinh (π * ((s : ℂ) - z))‖⁻¹ ≤ 4 * Real.exp (3 * π / 4) * Real.exp (-(π * |t|)) := by
                have h2 := inv_anti₀ (by positivity : 0 < Real.exp (π * |s - z.re|) / 4) (hsh_ge.trans h1)
                have h3 : (Real.exp (π * |s - z.re|) / 4)⁻¹ = 4 * Real.exp (-(π * |s - z.re|)) := by
                  rw [Real.exp_neg]; field_simp [(Real.exp_pos _).ne']
                rw [h3] at h2
                have hexp : Real.exp (-(π * |s - z.re|)) ≤ Real.exp (3 * π / 4) * Real.exp (-(π * |t|)) := by
                  rw [← Real.exp_add]
                  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
                calc ‖Complex.sinh (π * ((s : ℂ) - z))‖⁻¹ ≤ 4 * Real.exp (-(π * |s - z.re|)) := h2
                  _ ≤ 4 * (Real.exp (3 * π / 4) * Real.exp (-(π * |t|))) := mul_le_mul_of_nonneg_left hexp (by norm_num)
                  _ = 4 * Real.exp (3 * π / 4) * Real.exp (-(π * |t|)) := by ring
              exact mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
            · have hvs : v s = 0 := by by_contra hne; exact hs (hsupp hne)
              simp [hvs]
        _ = (4 * Real.exp (3 * π / 4) * Real.exp (-(π * |t|))) * (∫ s : ℝ, |v s|) := integral_const_mul _ _
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (n := r) (R := ρ) hρ_pos hdiff_ρ hsphere
    -- Absorb `|t|^{r+1} e^{-(π/2)|t|} ≤ (r+1)! (2/π)^{r+1}`
    have habs_poly : |t| ^ (r + 1) * Real.exp (-(π / 2) * |t|) ≤ ((r + 1).factorial : ℝ) * (2 / π) ^ (r + 1) := by
      have hterm := Real.pow_div_factorial_le_exp ((π / 2) * |t|) (by positivity) (r + 1)
      rw [mul_pow, div_le_iff₀ (by positivity : (0 : ℝ) < ((r + 1).factorial : ℝ))] at hterm
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      have hpos : 0 < (π / 2) ^ (r + 1) := by positivity
      have hcancel : (π / 2) ^ (r + 1) * (2 / π) ^ (r + 1) = 1 := by
        rw [← mul_pow]; field_simp [Real.pi_ne_zero]; norm_num
      calc |t| ^ (r + 1) = ((2 / π) ^ (r + 1)) * ((π / 2) ^ (r + 1) * |t| ^ (r + 1)) := by
            rw [← mul_assoc, mul_comm ((2 / π) ^ (r + 1)), hcancel, one_mul]
        _ ≤ (2 / π) ^ (r + 1) * (Real.exp (π / 2 * |t|) * ((r + 1).factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left hterm (by positivity)
        _ = ((r + 1).factorial : ℝ) * (2 / π) ^ (r + 1) * Real.exp (π / 2 * |t|) := by ring
    have hexp_split : Real.exp (-(π * |t|)) = Real.exp (-(π / 2) * |t|) * Real.exp (-(π / 2) * |t|) := by
      rw [← Real.exp_add]; congr 1; ring
    have hzpow : |t| ^ (-(1 + (r : ℤ))) = (|t| ^ (r + 1))⁻¹ := by
      rw [zpow_neg, show (1 + (r : ℤ)) = ((r + 1 : ℕ) : ℤ) by omega, zpow_natCast]
    have h4_le_12 : (12 : ℝ) ^ r ≤ (12 : ℝ) ^ r := le_rfl
    -- Note `C_large` had `4 ^ r`, let's use `12 ^ r`? Wait: `ρ = 1/12` gives `12 ^ r`!
    -- Wait: `C_large` in the `set` above has `4 ^ r` — we'll update `4 ^ r` to `12 ^ r` right below!
    calc ‖iteratedDeriv r F (t : ℂ)‖
        ≤ (r.factorial : ℝ) * ((4 * Real.exp (3 * π / 4) * Real.exp (-(π * |t|))) * (∫ s : ℝ, |v s|)) / ρ ^ r := hcauchy
      _ = (r.factorial : ℝ) * (12 : ℝ) ^ r * (4 * Real.exp (3 * π / 4)) * (∫ s : ℝ, |v s|) *
            (|t| ^ (r + 1) * Real.exp (-(π / 2) * |t|)) * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) := by
          rw [hexp_split, hzpow]; dsimp [ρ]; rw [one_div, inv_pow]; field_simp [ht_pos.ne']
      _ ≤ (r.factorial : ℝ) * (12 : ℝ) ^ r * (4 * Real.exp (3 * π / 4)) * (∫ s : ℝ, |v s|) *
            (((r + 1).factorial : ℝ) * (2 / π) ^ (r + 1)) * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) := by
          gcongr
      _ = ((r.factorial : ℝ) * (12 : ℝ) ^ r * (4 * Real.exp (3 * π / 4)) *
            (((r + 1).factorial : ℝ) * (2 / π) ^ (r + 1))) *
            (∫ s : ℝ, |v s|) * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) := by ring
      _ ≤ max C_small C_large * (∫ s : ℝ, |v s|) * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) := by
          gcongr; exact le_max_right _ _

/-- info: 'FormalResearch.SignUncertainty.FctCompD.norm_iteratedDeriv_stripCompGExt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.FctCompD.norm_iteratedDeriv_stripCompGExt_le

end FormalResearch.SignUncertainty.FctCompD
