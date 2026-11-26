module

public import FormalResearch.CohnElkies.MellinKernel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Lobe Saddle Bounds (`ce_rate.tex` Lemmas P.3, P.5, Proposition P.4, Remark P.4a)

Source: `CFT/sign_uncertainty/paper/ce_rate.tex` (PR 240, commit `c3d8c90fe`).

## Main results
* `integral_cos_sq_ge`: Lemma P.5 (`cel:L7`, `(ce322)`), elementary `cos²` averaging lower bound.
* `stripG_reflection_eq`, `saddle_tan_eq`: Lemma P.3 (`cel:L4`), reflection identity and `(cel:5.6)`.
* `exists_unique_saddleSigma`, `saddle_endpoint_scales`: Lemma P.3(2) (`(cel:5.2)`).
* `saddleEpsL`, `saddleEpsL_bounds`: Lemma P.3(2) (`(cel:5.3)`).
* `deriv2_stripG_norm_le`: Lemma P.3(3) (`(cel:5.4)`), `‖g''(σ + it)‖ ≤ 16 / (1 - σ)²`.
* `LobeSaddleAmp`, `lobeSaddleIntegral`, `lobe_saddle_asymptotic`, `lobeSaddleAmp_nonvacuous`:
  Proposition P.4 (`cel:L5`, `(cel:5.7)`–`(cel:5.9)`) and Remark P.4a (`cel:L5a`).
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Real Topology

namespace FormalResearch.CohnElkies

/-! ### Section 1: Elementary `cos²` averaging (Lemma P.5, `cel:L7`, `(ce322)`) -/

/-- **Lemma P.5 (`cel:L7`, `(ce322)`):** for all `ϑ_a : ℝ` and `L > 0`,
`∫ ϑ in Set.Icc ϑ_a (ϑ_a + L), (Real.cos ϑ)² ≥ (L / 16) * min (L²) 1`. -/
theorem integral_cos_sq_ge (ϑ_a : ℝ) {L : ℝ} (hL : 0 < L) :
    (L / 16) * min (L ^ 2) 1 ≤ ∫ ϑ in Set.Icc ϑ_a (ϑ_a + L), (Real.cos ϑ) ^ 2 := by
  have hle : ϑ_a ≤ ϑ_a + L := by linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hderiv : ∀ ϑ ∈ uIcc ϑ_a (ϑ_a + L),
      HasDerivAt (fun x : ℝ => x / 2 + Real.sin (2 * x) / 4) (Real.cos ϑ ^ 2) ϑ := fun ϑ _ => by
    have h1 := (hasDerivAt_id ϑ).div_const (2 : ℝ)
    have h2 := ((Real.hasDerivAt_sin (2 * ϑ)).comp ϑ ((hasDerivAt_id ϑ).const_mul 2)).div_const 4
    refine (h1.fun_add h2).congr_deriv ?_
    simp only [mul_one]
    linarith [Real.cos_two_mul ϑ]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous (fun ϑ : ℝ => Real.cos ϑ ^ 2)).intervalIntegrable _ _)
  have hsin_diff : Real.sin (2 * (ϑ_a + L)) - Real.sin (2 * ϑ_a) =
      2 * Real.sin L * Real.cos (2 * ϑ_a + L) := by
    rw [Real.sin_sub_sin]; congr 2 <;> ring_nf
  have heval : ∫ ϑ in ϑ_a..(ϑ_a + L), Real.cos ϑ ^ 2 =
      (L + Real.sin L * Real.cos (2 * ϑ_a + L)) / 2 := by
    rw [hftc]; linarith [hsin_diff]
  rw [heval]
  have hcos_abs : |Real.sin L * Real.cos (2 * ϑ_a + L)| ≤ |Real.sin L| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hlow : (L - |Real.sin L|) / 2 ≤ (L + Real.sin L * Real.cos (2 * ϑ_a + L)) / 2 := by
    linarith [(abs_le.mp hcos_abs).1]
  refine le_trans ?_ hlow
  rcases le_or_gt L 2 with hL2 | hL2
  · obtain ⟨hsin_lo, hsin_hi⟩ := sin_taylor_lower_upper hL.le
    rw [abs_of_nonneg (by nlinarith [sq_nonneg L] : 0 ≤ Real.sin L)]
    have hLsq : L ^ 2 ≤ 4 := by nlinarith
    have hL5 : L ^ 5 / 120 ≤ 4 * L ^ 3 / 120 := by nlinarith [pow_nonneg hL.le 3]
    nlinarith [min_le_left (L ^ 2) 1]
  · nlinarith [Real.abs_sin_le_one L, min_le_right (L ^ 2) 1]

/-! ### Section 2: Real strip function, reflection, and saddle scales (Lemma P.3(2)) -/

/-- Real restriction `g(σ) = log(tan(π σ / 2) / (π σ / 2))` (`0` at `σ = 0`). -/
noncomputable def stripGReal (σ : ℝ) : ℝ :=
  if σ = 0 then 0 else Real.log (Real.tan (π * σ / 2) / (π * σ / 2))

/-- Real derivative `g'(σ) = π / sin(π σ) - 1 / σ` for `σ ∈ (0, 1)`. -/
noncomputable def stripGDerivReal (σ : ℝ) : ℝ :=
  π / Real.sin (π * σ) - 1 / σ

lemma rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow]

private lemma rpow_inv_sqrt_strictAnti {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    b ^ (-(1 / 2 : ℝ)) < a ^ (-(1 / 2 : ℝ)) := by
  rw [rpow_neg_half_eq_inv_sqrt ha.le, rpow_neg_half_eq_inv_sqrt (ha.trans hab).le]
  exact inv_strictAnti₀ (Real.sqrt_pos.mpr ha) (Real.sqrt_lt_sqrt ha.le hab)

lemma rpow_one_third_cube {c : ℝ} (hc : 0 < c) : (c ^ (1 / 3 : ℝ)) ^ 3 = c := by
  rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hc.le]; norm_num

lemma stripG_ofReal {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    stripG (σ : ℂ) = (stripGReal σ : ℂ) := by
  have hx0 : 0 < π * σ / 2 := by positivity
  have hxp : π * σ / 2 < π / 2 := by nlinarith [Real.pi_pos]
  have hq : 0 < Real.tan (π * σ / 2) / (π * σ / 2) :=
    div_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hx0 hxp) hx0
  simp only [stripG, Complex.ofReal_ne_zero.mpr hσ0.ne', ↓reduceIte, stripGReal, hσ0.ne']
  have hc : Complex.tan (Real.pi * (σ : ℂ) / 2) / (Real.pi * (σ : ℂ) / 2) =
      ((Real.tan (π * σ / 2) / (π * σ / 2) : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.ofReal_log hq.le]

lemma stripG_ofReal_re {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (stripG (σ : ℂ)).re = stripGReal σ := by
  rw [stripG_ofReal hσ0 hσ1, Complex.ofReal_re]

lemma stripGReal_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) : 0 < stripGReal σ := by
  have hx0 : 0 < π * σ / 2 := by positivity
  have hxp : π * σ / 2 < π / 2 := by nlinarith [Real.pi_pos]
  have hcos : 0 < Real.cos (π * σ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, hxp⟩
  have hmono : StrictMonoOn (fun t : ℝ => Real.sin t - t * Real.cos t) (Icc 0 (π / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 (π / 2)) (by fun_prop) fun t ht => ?_
    rw [interior_Icc] at ht
    have hd : HasDerivAt (fun s : ℝ => Real.sin s - s * Real.cos s) (t * Real.sin t) t := by
      have h1 := (hasDerivAt_id t).fun_mul (Real.hasDerivAt_cos t)
      exact ((Real.hasDerivAt_sin t).fun_sub h1).congr_deriv (by simp)
    rw [hd.deriv]
    exact mul_pos ht.1 (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos]))
  have hgt : 0 < Real.sin (π * σ / 2) - (π * σ / 2) * Real.cos (π * σ / 2) := by
    have := hmono ⟨le_rfl, Real.pi_div_two_pos.le⟩ ⟨hx0.le, hxp.le⟩ hx0
    simpa using this
  have hq : 1 < Real.tan (π * σ / 2) / (π * σ / 2) := by
    rw [one_lt_div hx0, Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos]; linarith
  simp only [stripGReal, hσ0.ne', ↓reduceIte]
  exact Real.log_pos hq

lemma stripGDerivReal_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) : 0 < stripGDerivReal σ :=
  (div_pos (by positivity) (sub_pos.mpr hσ1)).trans (stripG_deriv_bounds hσ0 hσ1).1

lemma hasDerivAt_stripGReal {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    HasDerivAt stripGReal (stripGDerivReal σ) σ := by
  have hx0 : 0 < π * σ / 2 := by positivity
  have hxp : π * σ / 2 < π / 2 := by nlinarith [Real.pi_pos]
  have hcos : Real.cos (π * σ / 2) ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith, hxp⟩).ne'
  have hsin : Real.sin (π * σ / 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)).ne'
  have hq_pos : 0 < Real.tan (π * σ / 2) / (π * σ / 2) :=
    div_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hx0 hxp) hx0
  have harg : HasDerivAt (fun u : ℝ => π * u / 2) (π / 2) σ :=
    (((hasDerivAt_id σ).const_mul π).div_const 2).congr_deriv (by simp)
  have htan0 := (Real.hasDerivAt_tan hcos).comp σ harg
  change HasDerivAt (fun u : ℝ => Real.tan (π * u / 2)) _ σ at htan0
  have htan : HasDerivAt (fun u : ℝ => Real.tan (π * u / 2)) ((π / 2) / Real.cos (π * σ / 2) ^ 2) σ :=
    htan0.congr_deriv (by ring)
  have hlog : HasDerivAt (fun u : ℝ => Real.log (Real.tan (π * u / 2) / (π * u / 2)))
      (stripGDerivReal σ) σ := by
    refine ((htan.fun_div harg hx0.ne').log hq_pos.ne').congr_deriv ?_
    dsimp [stripGDerivReal]
    rw [Real.tan_eq_sin_div_cos]
    have hsin2 : Real.sin (π * σ) = 2 * Real.sin (π * σ / 2) * Real.cos (π * σ / 2) := by
      convert Real.sin_two_mul (π * σ / 2) using 2; ring
    rw [hsin2]
    have hpi : π ≠ 0 := Real.pi_ne_zero
    have hσ : σ ≠ 0 := hσ0.ne'
    field_simp
  refine hlog.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hσ0.ne'] with u hu; simp [stripGReal, hu]

lemma stripGReal_continuousOn : ContinuousOn stripGReal (Ico 0 1) := by
  intro σ hσ
  rcases eq_or_lt_of_le hσ.1 with rfl | hσ0
  · have hmul : Tendsto (fun u : ℝ => π * u / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa using ((by fun_prop : Continuous fun u : ℝ => π * u / 2).continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds,
        by filter_upwards [self_mem_nhdsWithin] with u hu; exact div_pos (mul_pos Real.pi_pos (mem_Ioi.mp hu)) two_pos⟩
    have htan_div : Tendsto (fun x : ℝ => Real.tan x / x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hs := (by simpa using Real.hasDerivAt_tan (by simp : Real.cos 0 ≠ 0) : HasDerivAt Real.tan 1 0).tendsto_slope_zero
      simp only [Real.tan_zero, sub_zero, smul_eq_mul] at hs
      refine (hs.mono_left (nhdsWithin_mono _ fun x (hx : x ∈ Ioi (0 : ℝ)) => (mem_Ioi.mp hx).ne')).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x _
      ring_nf
    have hlog : Tendsto (fun u : ℝ => Real.log (Real.tan (π * u / 2) / (π * u / 2))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc := (Real.continuousAt_log one_ne_zero).tendsto.comp (htan_div.comp hmul)
      simpa [Real.log_one, Function.comp_def] using hc
    have hlim : Tendsto stripGReal (𝓝[>] (0 : ℝ)) (𝓝 (stripGReal 0)) := by
      rw [show stripGReal 0 = 0 by simp [stripGReal]]
      refine hlog.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u); simp [stripGReal, hu.ne']
    rw [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsGE zero_lt_one, tendsto_nhds]
    intro s hs h0s
    obtain ⟨u, hu, hus⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hlim (hs.mem_nhds h0s))
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨u, hu, fun x hx => ?_⟩
    rcases eq_or_lt_of_le hx.2 with rfl | hx0
    · exact h0s
    · exact hus ⟨hx.1, hx0⟩
  · exact (hasDerivAt_stripGReal hσ0 hσ.2).continuousAt.continuousWithinAt

lemma stripGReal_strictMonoOn : StrictMonoOn stripGReal (Ioo 0 1) :=
  strictMonoOn_of_deriv_pos (convex_Ioo 0 1) (stripGReal_continuousOn.mono Ioo_subset_Ico_self) fun σ hσ => by
    rw [interior_Ioo] at hσ; rw [(hasDerivAt_stripGReal hσ.1 hσ.2).deriv]; exact stripGDerivReal_pos hσ.1 hσ.2

/-- **Lemma P.3 (`cel:L4`):** reflection identity
`exp(g(σ) + g(1 - σ)) = 4 / (π² σ (1 - σ))` for `0 < σ < 1`. -/
theorem stripG_reflection_eq {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Real.exp (stripGReal σ + stripGReal (1 - σ)) = 4 / (π ^ 2 * σ * (1 - σ)) := by
  have h1s : 0 < 1 - σ := sub_pos.mpr hσ1
  have htan1 : 0 < Real.tan (π * σ / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by nlinarith [Real.pi_pos])
  have htan2 : 0 < Real.tan (π * (1 - σ) / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by nlinarith [Real.pi_pos])
  have htan_refl : Real.tan (π * (1 - σ) / 2) = (Real.tan (π * σ / 2))⁻¹ := by
    rw [show π * (1 - σ) / 2 = π / 2 - π * σ / 2 by ring, Real.tan_pi_div_two_sub]
  simp only [stripGReal, hσ0.ne', h1s.ne', ↓reduceIte]
  rw [Real.exp_add, Real.exp_log (div_pos htan1 (by positivity)),
    Real.exp_log (div_pos htan2 (by positivity)), htan_refl]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have htn : Real.tan (π * σ / 2) ≠ 0 := htan1.ne'
  field_simp; ring

/-- **Equation `(cel:5.6)`:** at the saddle `g(σ_*) = -log(π² ξ)` with `ξ = Δ / c`,
`σ_* tan(π (1 - σ_*) / 2) = 2 π Δ / c`. -/
theorem saddle_tan_eq {c Δ ξ σ_star : ℝ} (hc : 0 < c) (hΔ : 0 < Δ) (hξ : ξ = Δ / c)
    (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ)) :
    σ_star * Real.tan (π * (1 - σ_star) / 2) = 2 * π * Δ / c := by
  have htan1 : 0 < Real.tan (π * σ_star / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by nlinarith [Real.pi_pos])
  have htan_refl : Real.tan (π * (1 - σ_star) / 2) = (Real.tan (π * σ_star / 2))⁻¹ := by
    rw [show π * (1 - σ_star) / 2 = π / 2 - π * σ_star / 2 by ring, Real.tan_pi_div_two_sub]
  have hexp : Real.tan (π * σ_star / 2) / (π * σ_star / 2) = c / (π ^ 2 * Δ) := by
    have h1 : Real.exp (stripGReal σ_star) = c / (π ^ 2 * Δ) := by
      rw [hσ_eq, Real.exp_neg, Real.exp_log (by rw [hξ]; positivity), hξ]
      have hpi : π ≠ 0 := Real.pi_ne_zero; field_simp
    simp only [stripGReal, hσ0.ne', ↓reduceIte] at h1
    rwa [Real.exp_log (div_pos htan1 (by positivity))] at h1
  rw [htan_refl]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have htn : Real.tan (π * σ_star / 2) ≠ 0 := htan1.ne'
  rw [mul_inv_eq_iff_eq_mul₀ htn]
  have h1 := congrArg (fun z => z * ((π * σ_star / 2) * (π ^ 2 * Δ) / (Real.tan (π * σ_star / 2) * c))) hexp
  have hc0 : c ≠ 0 := hc.ne'
  have hΔ0 : Δ ≠ 0 := hΔ.ne'
  field_simp at h1 ⊢
  nlinarith [h1]

/-- Existence and uniqueness of the real saddle `σ_* ∈ (0, 1)` solving `g(σ_*) = -log(π² ξ)`
whenever `0 < ξ < 1 / π²`. -/
theorem exists_unique_saddleSigma {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : π ^ 2 * ξ < 1) :
    ∃! σ_star : ℝ, σ_star ∈ Ioo 0 1 ∧ stripGReal σ_star = -Real.log (π ^ 2 * ξ) := by
  set target : ℝ := -Real.log (π ^ 2 * ξ)
  have htarget_pos : 0 < target := neg_pos.mpr (Real.log_neg (by positivity) hξ1)
  have htend_top : Tendsto stripGReal (𝓝[<] (1 : ℝ)) atTop := by
    have h_cos : Tendsto (fun σ : ℝ => Real.cos (π * σ / 2)) (𝓝[<] (1 : ℝ)) (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨by
        simpa [show π * (1 : ℝ) / 2 = π / 2 by ring, Real.cos_pi_div_two] using
          ((by fun_prop : Continuous fun σ : ℝ => Real.cos (π * σ / 2)).continuousAt (x := 1)).tendsto.mono_left nhdsWithin_le_nhds,
        by filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with σ hσ
           exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, hσ.1], by nlinarith [Real.pi_pos, hσ.2]⟩⟩
    have h_prod : Tendsto (fun σ : ℝ => Real.sin (π * σ / 2) * (π * σ / 2)⁻¹) (𝓝[<] (1 : ℝ)) (𝓝 (1 * (π / 2)⁻¹)) := by
      refine Tendsto.mul ?_ ?_
      · simpa [show π * (1 : ℝ) / 2 = π / 2 by ring, Real.sin_pi_div_two] using
          ((by fun_prop : Continuous fun σ : ℝ => Real.sin (π * σ / 2)).continuousAt (x := 1)).tendsto.mono_left nhdsWithin_le_nhds
      · have hinv : ContinuousAt (fun σ : ℝ => (π * σ / 2)⁻¹) 1 :=
          ((by fun_prop : Continuous fun σ : ℝ => π * σ / 2).continuousAt (x := 1)).inv₀ (by positivity)
        have ht : Tendsto (fun σ : ℝ => (π * σ / 2)⁻¹) (𝓝[<] (1 : ℝ)) (𝓝 (π * 1 / 2)⁻¹) :=
          hinv.tendsto.mono_left nhdsWithin_le_nhds
        rwa [mul_one] at ht
    have h_q : Tendsto (fun σ : ℝ => Real.tan (π * σ / 2) / (π * σ / 2)) (𝓝[<] (1 : ℝ)) atTop := by
      have heq : (fun σ : ℝ => Real.tan (π * σ / 2) / (π * σ / 2)) =
          fun σ => (Real.sin (π * σ / 2) * (π * σ / 2)⁻¹) * (Real.cos (π * σ / 2))⁻¹ := by
        ext σ; rw [Real.tan_eq_sin_div_cos]; ring
      rw [heq]; exact Filter.Tendsto.pos_mul_atTop (by positivity) h_prod (tendsto_inv_nhdsGT_zero.comp h_cos)
    refine (Real.tendsto_log_atTop.comp h_q).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with σ hσ; simp [stripGReal, hσ.1.ne']
  obtain ⟨b, hb_gt, hb_mem⟩ := ((htend_top.eventually (eventually_gt_atTop target)).and
    (Ioo_mem_nhdsLT zero_lt_one)).exists
  obtain ⟨σ_star, hσ_mem, hσ_eq⟩ := intermediate_value_Ioo hb_mem.1.le
    (stripGReal_continuousOn.mono (Icc_subset_Ico_right hb_mem.2))
    ⟨by simpa [stripGReal] using htarget_pos, hb_gt⟩
  exact ⟨σ_star, ⟨⟨hσ_mem.1, hσ_mem.2.trans hb_mem.2⟩, hσ_eq⟩, fun σ' hσ' =>
    stripGReal_strictMonoOn.injOn hσ'.1 ⟨hσ_mem.1, hσ_mem.2.trans hb_mem.2⟩ (hσ'.2.trans hσ_eq.symm)⟩

private lemma nonneg_of_Ici_deriv_nonneg {f f' : ℝ → ℝ} (hf : Differentiable ℝ f) (h0 : f 0 = 0)
    (hd : ∀ u, HasDerivAt f (f' u) u) (hpos : ∀ u ≥ 0, 0 ≤ f' u) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuous.continuousOn hf.differentiableOn
    fun u hu => by rw [interior_Ici] at hu; rw [(hd u).deriv]; exact hpos u hu.le
  linarith [hm le_rfl hx hx]

private lemma sin_taylor7_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  have d7 : ∀ u ≥ 0, 0 ≤ Real.cos u - (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720) := fun u hu =>
    nonneg_of_Ici_deriv_nonneg
      (Real.differentiable_cos.sub (by fun_prop)) (by simp)
      (fun s => show HasDerivAt _ (-(Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120))) s from
        ((Real.hasDerivAt_cos s).fun_sub ((((hasDerivAt_const s (1 : ℝ)).fun_sub
          ((hasDerivAt_pow 2 s).div_const 2)).fun_add ((hasDerivAt_pow 4 s).div_const 24)).fun_sub
          ((hasDerivAt_pow 6 s).div_const 720))).congr_deriv (by norm_num; ring))
      (fun s hs => by linarith [(sin_taylor_lower_upper hs).2]) hu
  rw [← sub_nonneg]
  exact nonneg_of_Ici_deriv_nonneg (Real.differentiable_sin.sub (by fun_prop)) (by simp)
    (fun s => show HasDerivAt _ (Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) s from
      ((Real.hasDerivAt_sin s).fun_sub ((((hasDerivAt_id s).fun_sub
        ((hasDerivAt_pow 3 s).div_const 6)).fun_add ((hasDerivAt_pow 5 s).div_const 120)).fun_sub
        ((hasDerivAt_pow 7 s).div_const 5040))).congr_deriv (by norm_num; ring)) d7 hx

/-- `g(σ) < (4/3) σ²` on `(0, 1/2]`. -/
lemma stripGReal_lt_four_thirds_sq {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) :
    stripGReal σ < (4 / 3 : ℝ) * σ ^ 2 := by
  have hg'_lt : ∀ {u : ℝ}, 0 < u → u ≤ 1 / 2 → stripGDerivReal u < (8 / 3 : ℝ) * u := by
    intro u hu0 hu1
    have hsin : 0 < Real.sin (π * u) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hu0) (by nlinarith [Real.pi_pos])
    have h1u2 : 0 < 1 - u ^ 2 := by nlinarith only [hu0, hu1]
    have hlt2 : stripGDerivReal u < 2 * u / (1 - u ^ 2) := by
      dsimp [stripGDerivReal]
      rw [div_sub_div _ _ hsin.ne' hu0.ne', div_lt_div_iff₀ (mul_pos hsin hu0) h1u2]
      set y := π * u
      have hy0 : 0 < y := mul_pos Real.pi_pos hu0
      have hy_hi : y < 1.571 := by dsimp [y]; nlinarith [Real.pi_lt_d4]
      have hy2 : y ^ 2 ≤ (2.47 : ℝ) := by nlinarith only [hy0, hy_hi]
      have hy6 : y ^ 6 ≤ (15.1 : ℝ) := by
        calc y ^ 6 = (y ^ 2) ^ 3 := by ring
          _ ≤ (2.47 : ℝ) ^ 3 := pow_le_pow_left₀ (sq_nonneg y) hy2 3
          _ ≤ 15.1 := by norm_num
      have hpi2_lo : (9.869 : ℝ) ≤ π ^ 2 := by nlinarith only [Real.pi_gt_d4]
      have hpi2_hi : π ^ 2 ≤ (9.87 : ℝ) := by nlinarith only [Real.pi_lt_d4, Real.pi_pos]
      have hp : 0 < 5040 * (2 - π ^ 2 / 6) + (42 * π ^ 2 - 840) * y ^ 2 + (42 - π ^ 2) * y ^ 4 - y ^ 6 := by
        have h1 : (-425.55 : ℝ) * y ^ 2 ≤ (42 * π ^ 2 - 840) * y ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hpi2_lo]) (sq_nonneg y)
        have h2 : (-425.55 : ℝ) * (2.47 : ℝ) ≤ (-425.55 : ℝ) * y ^ 2 := by linarith only [hy2]
        have h3 : 0 ≤ (42 - π ^ 2) * y ^ 4 := mul_nonneg (by linarith only [hpi2_hi]) (pow_nonneg hy0.le 4)
        linarith only [hpi2_hi, hy6, h1, h2, h3]
      have hcore : 0 < (1 + u ^ 2) * (y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040) - y * (1 - u ^ 2) := by
        have hfac : 5040 * π ^ 2 * ((1 + u ^ 2) * (y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040) - y * (1 - u ^ 2)) =
            y ^ 3 * (5040 * (2 - π ^ 2 / 6) + (42 * π ^ 2 - 840) * y ^ 2 + (42 - π ^ 2) * y ^ 4 - y ^ 6) := by
          dsimp [y]; ring
        have hmul : 0 < 5040 * π ^ 2 * ((1 + u ^ 2) * (y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040) - y * (1 - u ^ 2)) := by
          rw [hfac]; exact mul_pos (pow_pos hy0 3) hp
        exact pos_of_mul_pos_right hmul (by positivity)
      have hsin_mono := mul_le_mul_of_nonneg_left (sin_taylor7_lower hy0.le) (by positivity : 0 ≤ 1 + u ^ 2)
      linarith only [hcore, hsin_mono, show (1 + u ^ 2) * Real.sin y - y * (1 - u ^ 2) =
        2 * u ^ 2 * Real.sin (π * u) - (1 - u ^ 2) * (π * u - Real.sin (π * u)) by dsimp [y]; ring]
    exact hlt2.trans_le ((div_le_iff₀ h1u2).mpr (by nlinarith))
  let h : ℝ → ℝ := fun u => (4 / 3 : ℝ) * u ^ 2 - stripGReal u
  have hmono : StrictMonoOn h (Icc 0 (1 / 2)) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / 2))
      ((by fun_prop : Continuous fun u : ℝ => (4 / 3 : ℝ) * u ^ 2).continuousOn.sub
        (stripGReal_continuousOn.mono (Icc_subset_Ico_right (by norm_num))))
      fun u hu => by
        rw [interior_Icc] at hu
        have hd : HasDerivAt h ((8 / 3 : ℝ) * u - stripGDerivReal u) u :=
          (((hasDerivAt_pow 2 u).const_mul (4 / 3 : ℝ)).fun_sub
            (hasDerivAt_stripGReal hu.1 (by linarith [hu.2]))).congr_deriv (by ring)
        rw [hd.deriv]; exact sub_pos.mpr (hg'_lt hu.1 hu.2.le)
  have hlt := hmono ⟨le_rfl, by norm_num⟩ ⟨hσ0.le, hσ1⟩ hσ0
  dsimp only [h] at hlt
  simp only [stripGReal, ↓reduceIte, hσ0.ne'] at hlt ⊢
  linarith

private lemma tan_lt_four_div_pi_mul {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < π / 4) :
    Real.tan θ < (4 / π) * θ := by
  let f : ℝ → ℝ := fun t => Real.tan t / t
  have hmono : StrictMonoOn f (Ioc 0 (π / 4)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioc 0 (π / 4)) ?_ ?_
    · intro t ht
      have hcos : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2, Real.pi_pos]⟩).ne'
      exact ((Real.continuousAt_tan.mpr hcos).div continuousAt_id ht.1.ne').continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2, Real.pi_pos]⟩
      have hd := (Real.hasDerivAt_tan hcos.ne').fun_div (hasDerivAt_id t) ht.1.ne'
      change HasDerivAt f _ t at hd
      rw [hd.deriv]
      have hnum : 0 < t - Real.sin t * Real.cos t := by linarith [Real.sin_lt (by linarith [ht.1] : 0 < 2 * t), Real.sin_two_mul t]
      have heq : (1 / Real.cos t ^ 2 * t - Real.tan t * 1) / t ^ 2 =
          (t - Real.sin t * Real.cos t) / (t ^ 2 * Real.cos t ^ 2) := by
        rw [Real.tan_eq_sin_div_cos]; have hc0 := hcos.ne'; have ht0 := ht.1.ne'; field_simp
      simp only [id_eq, heq]; exact div_pos hnum (mul_pos (pow_pos ht.1 2) (pow_pos hcos 2))
  have hlt := hmono ⟨hθ0, hθ1.le⟩ ⟨by positivity, le_rfl⟩ hθ1
  dsimp [f] at hlt; rw [Real.tan_pi_div_four, div_lt_iff₀ hθ0] at hlt
  linarith [show 1 / (π / 4) * θ = (4 / π) * θ by ring]

/-- **Lemma P.3(2) (`cel:L4`, `(cel:5.2)`):** saddle endpoint scales. -/
theorem saddle_endpoint_scales {Δ₁ U c Δ ξ σ_star : ℝ}
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U)
    (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (hΔ_lo : Δ₁ ≤ Δ)
    (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ)) :
    let x_pos := c ^ (1 / 3 : ℝ) * σ_star
    let z_pos := c * (1 - σ_star)
    (σ_star ≤ 1 / 2 → (Real.sqrt 3 * π / 2) * Real.sqrt U < x_pos ∧ (27 / 10 : ℝ) * Real.sqrt U < x_pos) ∧
    (1 / 2 < σ_star → (1 / 2 : ℝ) * c ^ (1 / 3 : ℝ) < x_pos) ∧
    π * Δ₁ < z_pos := by
  dsimp only
  have hc_pos : 0 < c := by linarith [(le_max_left _ _).trans hc]
  have hΔ_pos : 0 < Δ := by linarith
  have hξ_pos : 0 < ξ := by rw [hξ]; positivity
  have hg_ge : π ^ 2 * U * c ^ (-(2 / 3 : ℝ)) ≤ stripGReal σ_star := by
    have h1 : π ^ 2 * ξ ≤ Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) := by
      have hpi : π ≠ 0 := Real.pi_ne_zero
      rw [hξ]; calc π ^ 2 * (Δ / c) ≤ π ^ 2 * ((c / π ^ 2) * Real.exp _ / c) := by gcongr
        _ = Real.exp _ := by field_simp [hc_pos.ne']
    linarith [Real.log_le_log (by positivity) h1, Real.log_exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ))))]
  refine ⟨?_, ?_, ?_⟩
  · intro hh
    have h_sq : (3 / 4 : ℝ) * π ^ 2 * U * c ^ (-(2 / 3 : ℝ)) < σ_star ^ 2 := by
      linarith [stripGReal_lt_four_thirds_sq hσ0 hh]
    have hc13_sq : (c ^ (1 / 3 : ℝ)) ^ 2 = c ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc_pos.le]; norm_num
    have hpow : c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc_pos]; norm_num
    have hmul : ((Real.sqrt 3 * π / 2) * Real.sqrt U) ^ 2 < (c ^ (1 / 3 : ℝ) * σ_star) ^ 2 := by
      have h_lhs : ((Real.sqrt 3 * π / 2) * Real.sqrt U) ^ 2 = 3 / 4 * π ^ 2 * U := by
        rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by linarith)]; ring
      rw [h_lhs, mul_pow, hc13_sq]
      calc 3 / 4 * π ^ 2 * U = (3 / 4 * π ^ 2 * U) * (c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) := by rw [hpow, mul_one]
        _ = c ^ (2 / 3 : ℝ) * (3 / 4 * π ^ 2 * U * c ^ (-(2 / 3 : ℝ))) := by ring
        _ < c ^ (2 / 3 : ℝ) * σ_star ^ 2 := mul_lt_mul_of_pos_left h_sq (Real.rpow_pos_of_pos hc_pos _)
    have h1 : (Real.sqrt 3 * π / 2) * Real.sqrt U < c ^ (1 / 3 : ℝ) * σ_star :=
      lt_of_pow_lt_pow_left₀ 2 (by positivity) hmul
    have h27 : (27 / 10 : ℝ) < Real.sqrt 3 * π / 2 := by
      have hsq : ((27 / 10 : ℝ) * 2 / π) ^ 2 < 3 := by
        have hlt : (27 / 10 : ℝ) * 2 / π < 5.4 / 3.1415 := by
          calc (27 / 10 : ℝ) * 2 / π = 5.4 / π := by ring
            _ < 5.4 / 3.1415 := div_lt_div_of_pos_left (by norm_num) (by norm_num) Real.pi_gt_d4
        nlinarith [show (0 : ℝ) ≤ (27 / 10 : ℝ) * 2 / π by positivity]
      have hlt := (Real.lt_sqrt (by positivity)).mpr hsq
      rw [div_lt_iff₀ Real.pi_pos] at hlt; linarith
    exact ⟨h1, (mul_lt_mul_of_pos_right h27 (Real.sqrt_pos.mpr (by linarith))).trans h1⟩
  · intro hh; simpa [mul_comm] using mul_lt_mul_of_pos_left hh (Real.rpow_pos_of_pos hc_pos (1 / 3 : ℝ))
  · rcases le_or_gt (1 / 2 : ℝ) (1 - σ_star) with h1s | h1s
    · have : 20 * Δ₁ ≤ c := (le_max_left _ _).trans hc
      nlinarith [Real.pi_lt_four]
    · have hθ0 : 0 < π * (1 - σ_star) / 2 := div_pos (mul_pos Real.pi_pos (sub_pos.mpr hσ1)) (by norm_num)
      have htan_ub : Real.tan (π * (1 - σ_star) / 2) < 2 * (1 - σ_star) := by
        calc Real.tan (π * (1 - σ_star) / 2) < (4 / π) * (π * (1 - σ_star) / 2) :=
              tan_lt_four_div_pi_mul hθ0 (by nlinarith [Real.pi_pos])
          _ = 2 * (1 - σ_star) := by field_simp [Real.pi_ne_zero]; ring
      have h1 : 2 * π * Δ₁ / c ≤ σ_star * Real.tan (π * (1 - σ_star) / 2) := by
        rw [saddle_tan_eq hc_pos hΔ_pos hξ hσ0 hσ1 hσ_eq]; gcongr
      have h2 : σ_star * Real.tan (π * (1 - σ_star) / 2) < 2 * (1 - σ_star) := by
        nlinarith [mul_lt_mul' hσ1.le htan_ub (Real.tan_pos_of_pos_of_lt_pi_div_two hθ0
          (by nlinarith [Real.pi_pos])).le zero_lt_one]
      have h3 := (div_lt_iff₀ hc_pos).mp (h1.trans_lt h2)
      linarith

/-- Saddle smallness parameter `ε_L = (c g'(σ_*))^{-1/2} / min(σ_*, 1 - σ_*)`. -/
noncomputable def saddleEpsL (c σ_star : ℝ) : ℝ :=
  (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ)) / min σ_star (1 - σ_star)

lemma saddleEpsL_pos {c σ_star : ℝ} (hc : 0 < c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) :
    0 < saddleEpsL c σ_star :=
  div_pos (Real.rpow_pos_of_pos (mul_pos hc (stripGDerivReal_pos hσ0 hσ1)) _) (lt_min hσ0 (sub_pos.mpr hσ1))

/-- **Lemma P.3(2) (`cel:L4`, `(cel:5.3)`):** bounds on `ε_L`. -/
theorem saddleEpsL_bounds {Δ₁ U c Δ ξ σ_star : ℝ}
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U)
    (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (hΔ_lo : Δ₁ ≤ Δ)
    (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ)) :
    let x_pos := c ^ (1 / 3 : ℝ) * σ_star
    let z_pos := c * (1 - σ_star)
    (1 / Real.sqrt 2) * z_pos ^ (-(1 / 2 : ℝ)) < saddleEpsL c σ_star ∧
    (σ_star ≤ 1 / 2 → (1 / 2 : ℝ) * x_pos ^ (-(3 / 2 : ℝ)) < saddleEpsL c σ_star) ∧
    saddleEpsL c σ_star < max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) := by
  dsimp only
  have hc_pos : 0 < c := by linarith [(le_max_left _ _).trans hc]
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  have hm_pos : 0 < min σ_star (1 - σ_star) := lt_min hσ0 h1s_pos
  obtain ⟨hx_le, _, hz_gt⟩ := saddle_endpoint_scales hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq
  obtain ⟨hg'_lo, hg'_hi⟩ := stripG_deriv_bounds hσ0 hσ1
  change (3 / 4 : ℝ) * σ_star / (1 - σ_star) < stripGDerivReal σ_star at hg'_lo
  change stripGDerivReal σ_star < 2 * σ_star / (1 - σ_star) at hg'_hi
  have hg'_pos : 0 < stripGDerivReal σ_star := stripGDerivReal_pos hσ0 hσ1
  have hdenom_pos : 0 < c * stripGDerivReal σ_star * min σ_star (1 - σ_star) ^ 2 := by positivity
  have h_eps_eq : saddleEpsL c σ_star =
      (c * stripGDerivReal σ_star * min σ_star (1 - σ_star) ^ 2) ^ (-(1 / 2 : ℝ)) := by
    unfold saddleEpsL
    rw [rpow_neg_half_eq_inv_sqrt (by positivity), rpow_neg_half_eq_inv_sqrt hdenom_pos.le,
      Real.sqrt_mul (mul_pos hc_pos hg'_pos).le, Real.sqrt_sq hm_pos.le, div_eq_mul_inv, mul_inv, mul_comm]
  have hz_pos : 0 < c * (1 - σ_star) := mul_pos hc_pos h1s_pos
  have h_z_lb : (1 / Real.sqrt 2) * (c * (1 - σ_star)) ^ (-(1 / 2 : ℝ)) < saddleEpsL c σ_star := by
    have h_mul : c * stripGDerivReal σ_star * min σ_star (1 - σ_star) ^ 2 < 2 * (c * (1 - σ_star)) := by
      rcases le_or_gt σ_star (1 / 2) with hh | hh
      · rw [min_eq_left (by linarith)]
        have h1 := mul_lt_mul_of_pos_right hg'_hi (sq_pos_of_pos hσ0)
        have hid : 2 * σ_star / (1 - σ_star) * σ_star ^ 2 ≤ 2 * (1 - σ_star) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ h1s_pos]; nlinarith [sq_nonneg σ_star]
        nlinarith [h1.trans_le hid]
      · rw [min_eq_right (by linarith)]
        have h1 := mul_lt_mul_of_pos_right hg'_hi (sq_pos_of_pos h1s_pos)
        have hid : 2 * σ_star / (1 - σ_star) * (1 - σ_star) ^ 2 = 2 * σ_star * (1 - σ_star) := by
          field_simp [h1s_pos.ne']
        nlinarith [h1.trans_eq hid]
    have hlt := rpow_inv_sqrt_strictAnti hdenom_pos h_mul
    rw [← h_eps_eq, rpow_neg_half_eq_inv_sqrt (by positivity), Real.sqrt_mul two_pos.le, mul_inv,
      ← rpow_neg_half_eq_inv_sqrt hz_pos.le, ← one_div] at hlt
    exact hlt
  refine ⟨h_z_lb, ?_, ?_⟩
  · intro hh
    rw [h_eps_eq]
    have h_mul : c * stripGDerivReal σ_star * min σ_star (1 - σ_star) ^ 2 <
        4 * (c ^ (1 / 3 : ℝ) * σ_star) ^ 3 := by
      rw [min_eq_left (by linarith), mul_pow, rpow_one_third_cube hc_pos]
      have h1 : stripGDerivReal σ_star < 4 * σ_star :=
        hg'_hi.trans_le ((div_le_iff₀ h1s_pos).mpr (by nlinarith))
      nlinarith [mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h1 (sq_pos_of_pos hσ0)) hc_pos]
    have hlt := rpow_inv_sqrt_strictAnti hdenom_pos h_mul
    rw [rpow_neg_half_eq_inv_sqrt (by positivity), Real.sqrt_mul (by norm_num),
      show Real.sqrt 4 = 2 by norm_num, mul_inv,
      ← rpow_neg_half_eq_inv_sqrt (by positivity),
      ← Real.rpow_natCast (c ^ (1 / 3 : ℝ) * σ_star) 3,
      ← Real.rpow_mul (by positivity)] at hlt
    convert hlt using 1
    norm_num [one_div]
  · rcases le_or_gt σ_star (1 / 2) with hh | hh
    · obtain ⟨_, hx_27⟩ := hx_le hh
      have h_mul : (3 / 4 : ℝ) * (c ^ (1 / 3 : ℝ) * σ_star) ^ 3 <
          c * stripGDerivReal σ_star * min σ_star (1 - σ_star) ^ 2 := by
        rw [min_eq_left (by linarith), mul_pow, rpow_one_third_cube hc_pos]
        have h1 : 3 / 4 * σ_star < stripGDerivReal σ_star :=
          ((le_div_iff₀ h1s_pos).mpr (by nlinarith)).trans_lt hg'_lo
        nlinarith [mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h1 (sq_pos_of_pos hσ0)) hc_pos]
      have hlt1 := rpow_inv_sqrt_strictAnti (by positivity) h_mul
      rw [← h_eps_eq] at hlt1
      have hx_cube := pow_lt_pow_left₀ hx_27 (by positivity) (by decide : 3 ≠ 0)
      have h_rhs : ((100 / 27 : ℝ) * U ^ (3 / 4 : ℝ)) ^ 2 < (3 / 4 : ℝ) * (c ^ (1 / 3 : ℝ) * σ_star) ^ 3 := by
        have hU1 : (Real.sqrt U) ^ 3 = U ^ (3 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ 3, ← Real.rpow_mul (by linarith)]; norm_num
        have hU2 : (U ^ (3 / 4 : ℝ)) ^ 2 = U ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by linarith)]; norm_num
        rw [mul_pow, hU1] at hx_cube; rw [mul_pow, hU2]
        have hnum : (100 / 27 : ℝ) ^ 2 < (3 / 4 : ℝ) * (27 / 10 : ℝ) ^ 3 := by norm_num
        nlinarith [Real.rpow_pos_of_pos (by linarith : 0 < U) (3 / 2 : ℝ)]
      have hlt2 := rpow_inv_sqrt_strictAnti (by positivity) h_rhs
      have hpow_neg : (((100 / 27 : ℝ) * U ^ (3 / 4 : ℝ)) ^ 2) ^ (-(1 / 2 : ℝ)) =
          (27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ)) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
        norm_num [Real.rpow_neg_one, mul_inv, ← Real.rpow_neg (by linarith : 0 ≤ U)]
        ring
      rw [hpow_neg] at hlt2
      exact (hlt1.trans hlt2).trans_le (le_max_left _ _)
    · have h_mul : Δ₁ < c * stripGDerivReal σ_star * min σ_star (1 - σ_star) ^ 2 := by
        rw [min_eq_right (by linarith)]
        have h1 : (3 / 8 : ℝ) / (1 - σ_star) < stripGDerivReal σ_star :=
          (div_lt_div_of_pos_right (by linarith) h1s_pos).trans hg'_lo
        have h2 : (3 / 8 : ℝ) * (1 - σ_star) < stripGDerivReal σ_star * (1 - σ_star) ^ 2 := by
          have := mul_lt_mul_of_pos_right h1 (sq_pos_of_pos h1s_pos)
          have hid : (3 / 8 : ℝ) / (1 - σ_star) * (1 - σ_star) ^ 2 = (3 / 8 : ℝ) * (1 - σ_star) := by
            field_simp [h1s_pos.ne']
          linarith
        nlinarith [Real.pi_gt_three, hc_pos]
      have hlt := rpow_inv_sqrt_strictAnti (by linarith) h_mul
      rw [← h_eps_eq] at hlt
      exact hlt.trans_le (le_max_right _ _)

/-! ### Section 3: Local vertical curvature `‖g''(σ + it)‖ ≤ 16 / (1 - σ)²` (Lemma P.3(3)) -/

private lemma cos_complex_norm_le_cosh (x y : ℝ) :
    ‖Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Real.cosh y := by
  have heq : Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((Real.cos x * Real.cosh y : ℝ) : ℂ) - ((Real.sin x * Real.sinh y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I]; push_cast; ring
  have hns : ‖Complex.cos ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ≤ Real.cosh y ^ 2 := by
    rw [heq, Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, Complex.I_im, sub_zero, Complex.sub_im, Complex.mul_im, mul_one, add_zero, zero_sub]
    nlinarith [Real.cosh_sq_sub_sinh_sq y, Real.cos_sq_add_sin_sq x,
      sq_nonneg (Real.sin x), sq_nonneg (Real.cos x), sq_nonneg (Real.sinh y)]
  exact le_of_sq_le_sq hns (Real.cosh_pos y).le

private lemma sin_complex_norm_sq {x y : ℝ} :
    ‖Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  have heq : Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((Real.sin x * Real.cosh y : ℝ) : ℂ) + ((Real.cos x * Real.sinh y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I]; push_cast; ring
  rw [heq, Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    mul_zero, Complex.I_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one]
  nlinarith [Real.cosh_sq_sub_sinh_sq y, Real.cos_sq_add_sin_sq x]

lemma tan_div_self_re_pos_halfStrip {w : ℂ} (hw0 : 0 ≤ w.re) (hw1 : w.re < 1) (hne : w ≠ 0) :
    0 < (Complex.tan ((π : ℂ) * w / 2) / ((π : ℂ) * w / 2)).re := by
  rcases eq_or_lt_of_le hw0 with hre0 | hre0
  · have him_ne : w.im ≠ 0 := fun h => hne (Complex.ext hre0.symm h)
    have hw_eq : (π : ℂ) * w / 2 = ((π * w.im / 2 : ℝ) : ℂ) * Complex.I := Complex.ext (by simp [← hre0]) (by simp)
    rw [hw_eq, Complex.tan_mul_I, mul_div_mul_right _ _ Complex.I_ne_zero]
    have hcy : Complex.tanh ((π * w.im / 2 : ℝ) : ℂ) = (Real.tanh (π * w.im / 2) : ℂ) := by
      simp [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Complex.ofReal_sinh, Complex.ofReal_cosh]
    rw [hcy, ← Complex.ofReal_div, Complex.ofReal_re]
    set y := π * w.im / 2
    have hpos : ∀ t : ℝ, 0 < t → 0 < Real.tanh t / t := fun t ht =>
      div_pos (by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr ht) (Real.cosh_pos t)) ht
    rcases lt_or_gt_of_ne (div_ne_zero (mul_ne_zero Real.pi_ne_zero him_ne) two_ne_zero) with hy | hy
    · rw [← neg_div_neg_eq, ← Real.tanh_neg]; exact hpos (-y) (neg_pos.mpr hy)
    · exact hpos y hy
  · set x : ℝ := π * w.re / 2; set y : ℝ := π * w.im / 2
    have hx0 : 0 < x := by positivity
    have hxp : x < π / 2 := by dsimp [x]; nlinarith [Real.pi_pos]
    have hw_eq : (Real.pi : ℂ) * w / 2 = (x : ℂ) + (y : ℂ) * Complex.I := Complex.ext (by simp [x]) (by simp [y])
    have hw_ne : (x : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
      rw [← hw_eq]; exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hne) two_ne_zero
    have htan_cond : (∀ k : ℤ, (x : ℂ) ≠ (2 * k + 1) * π / 2) ∧
        ∀ l : ℤ, (y : ℂ) * Complex.I ≠ (2 * l + 1) * π / 2 := by
      refine ⟨fun k hk => ?_, fun l hl => ?_⟩
      · have hre := congrArg (fun z : ℂ => |z.re|) hk; simp at hre
        have hk_int : (1 : ℝ) ≤ |2 * (k : ℝ) + 1| := by exact_mod_cast Int.one_le_abs (by omega)
        have hbd : π / 2 ≤ |(2 * (k : ℝ) + 1) * π / 2| := by
          rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          calc π / 2 = 1 * π / 2 := by ring
            _ ≤ |2 * (k : ℝ) + 1| * π / 2 := by gcongr
        rw [abs_of_pos hx0] at hre; linarith
      · have hre := congrArg Complex.re hl; simp at hre
        have : (2 * (l : ℝ) + 1) ≠ 0 := by exact_mod_cast show (2 * l + 1 : ℤ) ≠ 0 by omega
        exact absurd hre.symm (div_ne_zero (mul_ne_zero this Real.pi_ne_zero) two_ne_zero)
    set a : ℝ := Real.tan x; set b : ℝ := Real.tanh y
    have ha : 0 < a := Real.tan_pos_of_pos_of_lt_pi_div_two hx0 hxp
    have h1b2 : 0 < 1 - b ^ 2 := by
      have : 1 - b ^ 2 = (Real.cosh y)⁻¹ ^ 2 := by
        dsimp [b]; rw [Real.tanh_eq_sinh_div_cosh]
        have := (Real.cosh_pos y).ne'; field_simp; linarith [Real.cosh_sq_sub_sinh_sq y]
      rw [this]; positivity
    have hden_pos : 0 < 1 + a ^ 2 * b ^ 2 := by positivity
    set r1 : ℝ := a * (1 - b ^ 2) / (1 + a ^ 2 * b ^ 2)
    set r2 : ℝ := b * (1 + a ^ 2) / (1 + a ^ 2 * b ^ 2)
    have hw_parts : Complex.tan ((x : ℂ) + (y : ℂ) * Complex.I) = (r1 : ℂ) + (r2 : ℂ) * Complex.I := by
      rw [Complex.tan_add_mul_I (Or.inl htan_cond),
        show Complex.tan (x : ℂ) = (a : ℂ) by simp [a, Complex.ofReal_tan],
        show Complex.tanh (y : ℂ) = (b : ℂ) by
          simp [b, Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Complex.ofReal_sinh, Complex.ofReal_cosh],
        div_eq_iff (fun h => by have := congrArg Complex.re h; simp at this)]
      have hden0 : 1 + a ^ 2 * b ^ 2 ≠ 0 := hden_pos.ne'
      apply Complex.ext <;> simp <;> [dsimp [r1, r2]; dsimp [r1, r2]] <;> field_simp <;> ring
    rw [hw_eq, hw_parts, div_eq_mul_inv, Complex.mul_re, Complex.inv_re, Complex.inv_im]
    have hns : 0 < Complex.normSq ((x : ℂ) + (y : ℂ) * Complex.I) := Complex.normSq_pos.mpr hw_ne
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero,
      Complex.add_im, Complex.mul_I_im, zero_add]
    have hby : 0 ≤ b * y := by
      rcases le_or_gt 0 y with hy | hy
      · exact mul_nonneg (by dsimp [b]; rw [Real.tanh_eq_sinh_div_cosh]; exact div_nonneg (Real.sinh_nonneg_iff.mpr hy) (Real.cosh_pos y).le) hy
      · have : b * y = Real.tanh (-y) * (-y) := by dsimp [b]; rw [Real.tanh_neg]; ring
        rw [this, Real.tanh_eq_sinh_div_cosh]
        exact mul_nonneg (div_nonneg (Real.sinh_nonneg_iff.mpr (neg_pos.mpr hy).le) (Real.cosh_pos _).le) (neg_pos.mpr hy).le
    have hnum : 0 < r1 * x + r2 * y := by
      have h1 : 0 < r1 * x := by dsimp [r1]; positivity
      have h2 : 0 ≤ (1 + a ^ 2) / (1 + a ^ 2 * b ^ 2) * (b * y) := mul_nonneg (by positivity) hby
      have hr2 : r2 * y = (1 + a ^ 2) / (1 + a ^ 2 * b ^ 2) * (b * y) := by dsimp [r2]; ring
      linarith
    have hid : r1 * (x / Complex.normSq ((x : ℂ) + (y : ℂ) * Complex.I)) -
        r2 * (-y / Complex.normSq ((x : ℂ) + (y : ℂ) * Complex.I)) =
        (r1 * x + r2 * y) / Complex.normSq ((x : ℂ) + (y : ℂ) * Complex.I) := by
      field_simp [hns.ne']; ring
    rw [hid]; exact div_pos hnum hns

lemma sin_pi_ne_zero_halfStrip {w : ℂ} (hw0 : 0 ≤ w.re) (hw1 : w.re < 1) (hne : w ≠ 0) :
    Complex.sin ((π : ℂ) * w) ≠ 0 := by
  intro hs
  have hz_eq : (π : ℂ) * w = ((π * w.re : ℝ) : ℂ) + ((π * w.im : ℝ) : ℂ) * Complex.I :=
    Complex.ext (by simp) (by simp)
  have hnorm := congrArg (fun z : ℂ => ‖z‖ ^ 2) hs
  rw [hz_eq, sin_complex_norm_sq, norm_zero, zero_pow two_ne_zero] at hnorm
  have hsh0 : Real.sinh (π * w.im) = 0 := by nlinarith [sq_nonneg (Real.sin (π * w.re))]
  rcases eq_or_lt_of_le hw0 with hre0 | hre0
  · exact hne (Complex.ext hre0.symm ((mul_eq_zero.mp (Real.sinh_eq_zero.mp hsh0)).resolve_left Real.pi_ne_zero))
  · have hsp := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hre0) (by nlinarith [Real.pi_pos, hw1])
    nlinarith [sq_nonneg (Real.sinh (π * w.im))]

lemma hasDerivAt_stripG {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) :
    HasDerivAt stripG ((π : ℂ) / Complex.sin ((π : ℂ) * ζ) - 1 / ζ) ζ := by
  have hζ_ne : ζ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hre_pos := tan_div_self_re_pos_halfStrip h0.le h1 hζ_ne
  have hcos_ne : Complex.cos ((π : ℂ) * ζ / 2) ≠ 0 := fun hc => by
    have := Complex.tan_eq_zero_of_cos_eq_zero hc; rw [this, zero_div, Complex.zero_re] at hre_pos; exact lt_irrefl 0 hre_pos
  have harg : HasDerivAt (fun w : ℂ => (π : ℂ) * w / 2) ((π : ℂ) / 2) ζ :=
    (((hasDerivAt_id ζ).const_mul (π : ℂ)).div_const 2).congr_deriv (by simp)
  have htan0 := (Complex.hasDerivAt_tan hcos_ne).comp ζ harg
  change HasDerivAt (fun w : ℂ => Complex.tan ((π : ℂ) * w / 2)) _ ζ at htan0
  have htan : HasDerivAt (fun w : ℂ => Complex.tan ((π : ℂ) * w / 2))
      (((π : ℂ) / 2) / Complex.cos ((π : ℂ) * ζ / 2) ^ 2) ζ :=
    htan0.congr_deriv (by ring)
  have hq := htan.fun_div harg (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hζ_ne) two_ne_zero)
  have hlog : HasDerivAt (fun w : ℂ => Complex.log (Complex.tan ((π : ℂ) * w / 2) / ((π : ℂ) * w / 2)))
      ((π : ℂ) / Complex.sin ((π : ℂ) * ζ) - 1 / ζ) ζ := by
    have hlog0 := (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl hre_pos))).comp ζ hq
    change HasDerivAt (fun w : ℂ => Complex.log (Complex.tan ((π : ℂ) * w / 2) / ((π : ℂ) * w / 2))) _ ζ at hlog0
    refine hlog0.congr_deriv ?_
    have hsin2 : Complex.sin ((π : ℂ) * ζ) = 2 * Complex.sin ((π : ℂ) * ζ / 2) * Complex.cos ((π : ℂ) * ζ / 2) := by
      convert Complex.sin_two_mul ((π : ℂ) * ζ / 2) using 2; ring
    have hsin_ne : Complex.sin ((π : ℂ) * ζ / 2) ≠ 0 := fun hs => by
      have : Complex.tan ((π : ℂ) * ζ / 2) = 0 := by rw [Complex.tan_eq_sin_div_cos, hs, zero_div]
      rw [this, zero_div, Complex.zero_re] at hre_pos; exact lt_irrefl 0 hre_pos
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [Complex.tan_eq_sin_div_cos, hsin2]; field_simp
  refine hlog.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h0] with w hw
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; exact lt_irrefl 0 hw
  simp [stripG, hw0]

lemma deriv2_stripG_eq {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) :
    deriv^[2] stripG ζ =
      -(π : ℂ) ^ 2 * Complex.cos ((π : ℂ) * ζ) / Complex.sin ((π : ℂ) * ζ) ^ 2 + 1 / ζ ^ 2 := by
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hev : deriv stripG =ᶠ[𝓝 ζ] fun w : ℂ => (π : ℂ) / Complex.sin ((π : ℂ) * w) - 1 / w := by
    filter_upwards [hopen.mem_nhds ⟨h0, h1⟩] with w hw; exact (hasDerivAt_stripG hw.1 hw.2).deriv
  have hζ_ne : ζ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hsin_ne : Complex.sin ((π : ℂ) * ζ) ≠ 0 := sin_pi_ne_zero_halfStrip h0.le h1 hζ_ne
  have hd1 : HasDerivAt (fun w : ℂ => (π : ℂ) / Complex.sin ((π : ℂ) * w))
      (-(π : ℂ) ^ 2 * Complex.cos ((π : ℂ) * ζ) / Complex.sin ((π : ℂ) * ζ) ^ 2) ζ := by
    have hs := (Complex.hasDerivAt_sin ((π : ℂ) * ζ)).comp ζ ((hasDerivAt_id ζ).const_mul (π : ℂ))
    refine ((hs.inv hsin_ne).const_mul (π : ℂ)).congr_deriv ?_
    dsimp; ring
  have hd2 : HasDerivAt (fun w : ℂ => (1 : ℂ) / w) (-(1 / ζ ^ 2)) ζ :=
    ((hasDerivAt_const ζ (1 : ℂ)).div (hasDerivAt_id ζ) hζ_ne).congr_deriv (by simp; ring)
  have hd : HasDerivAt (fun w : ℂ => (π : ℂ) / Complex.sin ((π : ℂ) * w) - 1 / w)
      (-(π : ℂ) ^ 2 * Complex.cos ((π : ℂ) * ζ) / Complex.sin ((π : ℂ) * ζ) ^ 2 + 1 / ζ ^ 2) ζ :=
    (hd1.fun_sub hd2).congr_deriv (by ring)
  change deriv (deriv stripG) ζ = _
  rw [hev.deriv_eq, hd.deriv]

private lemma factorial_two_mul_ge (n₀ k : ℕ) (c₀ r : ℝ) (hr : 0 ≤ r)
    (hbase : c₀ ≤ ((2 * n₀ + k).factorial : ℝ))
    (hstep : ∀ j : ℕ, r ≤ (2 * (n₀ + j : ℝ) + k + 2) * (2 * (n₀ + j : ℝ) + k + 1)) :
    ∀ j : ℕ, c₀ * r ^ j ≤ ((2 * (j + n₀) + k).factorial : ℝ) := by
  intro j; induction j with
  | zero => simpa using hbase
  | succ j ih =>
    have hs : 2 * (j + 1 + n₀) + k = (2 * (j + n₀) + k) + 2 := by omega
    rw [hs, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    calc c₀ * r ^ (j + 1) = (c₀ * r ^ j) * r := by ring
      _ ≤ ((2 * (j + n₀) + k).factorial : ℝ) * ((2 * (n₀ + j : ℝ) + k + 2) * (2 * (n₀ + j : ℝ) + k + 1)) :=
          mul_le_mul ih (hstep j) hr (by positivity)
      _ = _ := by ring

private lemma tsum_shift_norm_le {c : ℕ → ℂ} {n₀ : ℕ} {C r : ℝ} (_hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbd : ∀ j : ℕ, ‖c (j + n₀)‖ ≤ C * r ^ j) :
    Summable c ∧ ‖∑' k : ℕ, c k‖ ≤ (∑ i ∈ Finset.range n₀, ‖c i‖) + C * (1 - r)⁻¹ := by
  have hgs : Summable (fun j : ℕ => C * r ^ j) := (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hsn : Summable (fun k : ℕ => ‖c k‖) :=
    (summable_nat_add_iff n₀).mp (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd hgs)
  refine ⟨hsn.of_norm, ?_⟩
  have hsplit : ∑' k : ℕ, ‖c k‖ = (∑ i ∈ Finset.range n₀, ‖c i‖) + ∑' j : ℕ, ‖c (j + n₀)‖ :=
    (hsn.sum_add_tsum_nat_add n₀).symm
  have htail : ∑' j : ℕ, ‖c (j + n₀)‖ ≤ C * (1 - r)⁻¹ := by
    have h1 := ((summable_nat_add_iff n₀).mpr hsn).tsum_le_tsum hbd hgs
    rwa [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at h1
  exact (norm_tsum_le_tsum_norm hsn).trans (by rw [hsplit]; linarith)

/-- **Lemma P.3(3) (`cel:L4`, `(cel:5.4)`):** local vertical curvature bound
`‖deriv^[2] stripG (σ + i t)‖ ≤ 16 / (1 - σ)²` for `0 < σ < 1` and `|t| ≤ (1 - σ) / 2`. -/
theorem deriv2_stripG_norm_le {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (ht : |t| ≤ (1 - σ) / 2) :
    ‖deriv^[2] stripG ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 16 / (1 - σ) ^ 2 := by
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hz_re : z.re = σ := by simp [z]
  have hz_eq := deriv2_stripG_eq (hz_re ▸ hσ0) (hz_re ▸ hσ1)
  have h1s_pos : 0 < 1 - σ := sub_pos.mpr hσ1
  rcases le_or_gt σ (1 / 2) with hhalf | hhalf
  · have hz_sq : ‖z‖ ^ 2 ≤ (5 / 16 : ℝ) := by
      have hz_ns : ‖z‖ ^ 2 = σ ^ 2 + t ^ 2 := by
        rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]; simp [z, sq]
      have ht_sq : t ^ 2 ≤ (1 - σ) ^ 2 / 4 := by
        have := pow_le_pow_left₀ (abs_nonneg t) ht 2; rw [sq_abs] at this; linarith
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - 2 * σ) (by linarith : 0 ≤ 1 + 10 * σ)]
    set u : ℂ := (π : ℂ) * z
    have hu_ne : u ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (fun h => by have := congrArg Complex.re h; simp [z] at this; linarith)
    have hu_sq : ‖u‖ ^ 2 ≤ (3.09 : ℝ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, mul_pow]
      nlinarith [Real.pi_lt_d4, Real.pi_pos, sq_nonneg ‖z‖]
    have hsinc : (0.399 : ℝ) ≤ ‖Complex.sin u / u‖ := by
      let f : ℕ → ℂ := fun n => (-1) ^ n * u ^ (2 * n) / ((2 * n + 1).factorial : ℂ)
      have hhas : HasSum f (Complex.sin u / u) := by
        refine ((Complex.hasSum_sin u).div_const u).congr_fun fun n => ?_
        dsimp [f]; rw [pow_succ]; field_simp [hu_ne]
      have hfn : ∀ n : ℕ, ‖f n‖ ≤ (3.09 : ℝ) ^ n / ((2 * n + 1).factorial : ℝ) := fun n => by
        dsimp [f]; rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
          Complex.norm_natCast, pow_mul]; gcongr
      have hfac := factorial_two_mul_ge 3 1 5040 72 (by norm_num) (by norm_num : (5040 : ℝ) ≤ _)
        fun j => by push_cast; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have htail := tsum_shift_norm_le (c := fun k => f (k + 1)) (n₀ := 2)
        (C := (3.09 : ℝ) ^ 3 / 5040) (r := 3.09 / 72) (by positivity) (by norm_num) (by norm_num) fun j => by
          calc ‖f (j + 3)‖ ≤ (3.09 : ℝ) ^ (j + 3) / ((2 * (j + 3) + 1).factorial : ℝ) := hfn (j + 3)
            _ ≤ (3.09 : ℝ) ^ (j + 3) / ((5040 : ℝ) * 72 ^ j) := by gcongr; exact hfac j
            _ = ((3.09 : ℝ) ^ 3 / 5040) * (3.09 / 72 : ℝ) ^ j := by rw [pow_add, div_pow]; ring
      have hf_sum : Summable f := (summable_nat_add_iff 1).mp htail.1
      have hsplit : Complex.sin u / u = 1 + ∑' k : ℕ, f (k + 1) := by
        rw [← hhas.tsum_eq, hf_sum.tsum_eq_zero_add]; simp [f]
      have hR : ‖∑' k : ℕ, f (k + 1)‖ ≤ 0.601 := by
        have h1 : ‖f 1‖ ≤ 3.09 / 6 := (hfn 1).trans_eq (by norm_num [Nat.factorial])
        have h2 : ‖f 2‖ ≤ (3.09 : ℝ) ^ 2 / 120 := (hfn 2).trans_eq (by norm_num [Nat.factorial])
        calc ‖∑' k : ℕ, f (k + 1)‖ ≤ (‖f 1‖ + ‖f 2‖) + (3.09 : ℝ) ^ 3 / 5040 * (1 - 3.09 / 72)⁻¹ := by
              simpa [Finset.sum_range_succ] using htail.2
          _ ≤ 3.09 / 6 + (3.09 : ℝ) ^ 2 / 120 + (3.09 : ℝ) ^ 3 / 5040 * (1 - 3.09 / 72)⁻¹ := by gcongr
          _ ≤ 0.601 := by norm_num
      have hrev := norm_sub_norm_le (1 : ℂ) (-(∑' k : ℕ, f (k + 1)))
      rw [sub_neg_eq_add, norm_one, norm_neg, ← hsplit] at hrev; linarith
    have hnum : ‖Complex.sin u ^ 2 - u ^ 2 * Complex.cos u‖ ≤ (0.20 : ℝ) * ‖u‖ ^ 4 := by
      let a : ℕ → ℂ := fun m => (-1) ^ m * (2 : ℂ) ^ (2 * m + 1) * u ^ (2 * m + 2) / ((2 * m + 2).factorial : ℂ)
      let b : ℕ → ℂ := fun m => (-1) ^ m * u ^ (2 * m + 2) / ((2 * m).factorial : ℂ)
      have ha_sum : HasSum a (Complex.sin u ^ 2) := by
        have hsin2 : Complex.sin u ^ 2 = (1 - Complex.cos (2 * u)) / 2 := by
          rw [Complex.cos_two_mul_eq_one_sub]; ring
        have h1 := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_cos (2 * u))
        simp only [Finset.sum_range_one, pow_zero, one_mul, mul_zero, Nat.factorial_zero,
          Nat.cast_one, div_one] at h1
        have h2_val : -((Complex.cos (2 * u) - 1) / 2) = -(Complex.cos (2 * u) - 1) / 2 := by ring
        have h2 : HasSum a (-((Complex.cos (2 * u) - 1) / 2)) := by
          rw [h2_val]; refine (h1.neg.div_const 2).congr_fun fun m => ?_
          dsimp [a]
          rw [show 2 * (m + 1) = 2 * m + 2 by ring, mul_pow (2 : ℂ) u, pow_succ (-1 : ℂ),
            show (2 : ℂ) ^ (2 * m + 2) = 2 * 2 ^ (2 * m + 1) by rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, pow_succ]; ring]
          ring
        convert h2 using 1; rw [hsin2]; ring
      have hb_sum : HasSum b (u ^ 2 * Complex.cos u) :=
        ((Complex.hasSum_cos u).mul_left (u ^ 2)).congr_fun fun m => by simp only [b]; rw [pow_add]; ring
      have hshift : HasSum (fun k => a (k + 1) - b (k + 1)) (Complex.sin u ^ 2 - u ^ 2 * Complex.cos u) := by
        have hs := (hasSum_nat_add_iff' 1).mpr (ha_sum.sub hb_sum)
        have h0 : a 0 - b 0 = 0 := by simp [a, b]
        simpa [Finset.sum_range_one, h0] using hs
      let c : ℕ → ℂ := fun k => (-1) ^ (k + 1) * ((2 : ℂ) ^ (2 * k + 3) / ((2 * k + 4).factorial : ℂ) -
        1 / ((2 * k + 2).factorial : ℂ)) * u ^ (2 * k)
      have hc_bd : ∀ k : ℕ, ‖c k‖ ≤ |((2 : ℝ) ^ (2 * k + 3) / ((2 * k + 4).factorial : ℝ) -
          1 / ((2 * k + 2).factorial : ℝ))| * (3.09 : ℝ) ^ k := fun k => by
        dsimp [c]
        have hr : ((2 : ℂ) ^ (2 * k + 3) / ((2 * k + 4).factorial : ℂ) - 1 / ((2 * k + 2).factorial : ℂ)) =
            (((2 : ℝ) ^ (2 * k + 3) / ((2 * k + 4).factorial : ℝ) - 1 / ((2 * k + 2).factorial : ℝ) : ℝ) : ℂ) := by
          push_cast; rfl
        rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hr,
          Complex.norm_real, Real.norm_eq_abs, norm_pow, pow_mul]; gcongr
      have hfac := factorial_two_mul_ge 3 4 3628800 132 (by norm_num) (by norm_num : (3628800 : ℝ) ≤ _)
        fun j => by push_cast; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have hpow2 : ∀ k : ℕ, 3 ≤ k → (2 * (k : ℝ) + 4) * (2 * (k : ℝ) + 3) ≤ (2 : ℝ) ^ (2 * k + 3) := fun k hk => by
        induction k, hk using Nat.le_induction with
        | base => norm_num
        | succ k hk ih =>
          calc (2 * ((k + 1 : ℕ) : ℝ) + 4) * (2 * ((k + 1 : ℕ) : ℝ) + 3)
              ≤ 4 * ((2 * (k : ℝ) + 4) * (2 * (k : ℝ) + 3)) := by push_cast; nlinarith [show (3 : ℝ) ≤ k by exact_mod_cast hk]
            _ ≤ 4 * (2 : ℝ) ^ (2 * k + 3) := by gcongr
            _ = (2 : ℝ) ^ (2 * (k + 1) + 3) := by rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 by ring, pow_add]; norm_num; ring
      have htail := tsum_shift_norm_le (c := c) (n₀ := 3) (C := (512 : ℝ) * (3.09 : ℝ) ^ 3 / 3628800)
        (r := 4 * 3.09 / 132) (by positivity) (by norm_num) (by norm_num) fun j => by
          have hsub : 1 / ((2 * (j + 3) + 2).factorial : ℝ) ≤ (2 : ℝ) ^ (2 * (j + 3) + 3) / ((2 * (j + 3) + 4).factorial : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul,
              show 2 * (j + 3) + 4 = (2 * (j + 3) + 2) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
            push_cast; rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            convert hpow2 (j + 3) (by omega) using 1; push_cast; ring
          have hab : |((2 : ℝ) ^ (2 * (j + 3) + 3) / ((2 * (j + 3) + 4).factorial : ℝ) -
              1 / ((2 * (j + 3) + 2).factorial : ℝ))| ≤ (2 : ℝ) ^ (2 * (j + 3) + 3) / ((2 * (j + 3) + 4).factorial : ℝ) := by
            rw [abs_of_nonneg (sub_nonneg.mpr hsub)]; linarith [show (0 : ℝ) < 1 / ((2 * (j + 3) + 2).factorial : ℝ) by positivity]
          have hnum_eq : ((2 : ℝ) ^ (2 * (j + 3) + 3)) * (3.09 : ℝ) ^ (j + 3) = 512 * (3.09 : ℝ) ^ 3 * (4 * 3.09) ^ j := by
            rw [show 2 * (j + 3) + 3 = 9 + 2 * j by ring, pow_add, pow_mul, pow_add, mul_pow]; norm_num; ring
          calc ‖c (j + 3)‖ ≤ ((2 : ℝ) ^ (2 * (j + 3) + 3) / ((2 * (j + 3) + 4).factorial : ℝ)) * (3.09 : ℝ) ^ (j + 3) :=
                (hc_bd (j + 3)).trans (mul_le_mul_of_nonneg_right hab (by positivity))
            _ = (512 * (3.09 : ℝ) ^ 3 * (4 * 3.09) ^ j) / ((2 * (j + 3) + 4).factorial : ℝ) := by rw [div_mul_eq_mul_div, hnum_eq]
            _ ≤ (512 * (3.09 : ℝ) ^ 3 * (4 * 3.09) ^ j) / ((3628800 : ℝ) * 132 ^ j) := by gcongr; exact hfac j
            _ = ((512 : ℝ) * (3.09 : ℝ) ^ 3 / 3628800) * ((4 * 3.09 / 132) : ℝ) ^ j := by rw [div_pow]; ring
      have hcs : HasSum (fun k => u ^ 4 * c k) (Complex.sin u ^ 2 - u ^ 2 * Complex.cos u) :=
        hshift.congr_fun fun k => by
          simp only [a, b, c]
          rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, show 2 * (k + 1) + 2 = 2 * k + 4 by ring,
            show 2 * (k + 1) = 2 * k + 2 by ring, show u ^ (2 * k + 4) = u ^ 4 * u ^ (2 * k) by rw [← pow_add]; ring]
          ring
      rw [← hcs.tsum_eq, htail.1.tsum_mul_left, norm_mul, norm_pow]
      have hc0 : ‖c 0‖ ≤ 1 / 6 := by have := hc_bd 0; norm_num at this ⊢; exact this
      have hc1 : ‖c 1‖ ≤ 1 / 360 * 3.09 := by have := hc_bd 1; norm_num at this ⊢; exact this
      have hc2 : ‖c 2‖ ≤ 1 / 560 * (3.09 : ℝ) ^ 2 := by have := hc_bd 2; norm_num at this ⊢; exact this
      have htsum : ‖∑' k : ℕ, c k‖ ≤ 0.20 := by
        have hsum_bd := htail.2; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum_bd
        linarith [show (1 / 6 : ℝ) + 1 / 360 * 3.09 + 1 / 560 * (3.09 : ℝ) ^ 2 +
          ((512 : ℝ) * (3.09 : ℝ) ^ 3 / 3628800) * (1 - 4 * 3.09 / 132)⁻¹ ≤ 0.20 by norm_num]
      calc ‖u‖ ^ 4 * ‖∑' k : ℕ, c k‖ ≤ ‖u‖ ^ 4 * 0.20 := by gcongr
        _ = 0.20 * ‖u‖ ^ 4 := by ring
    have hid : deriv^[2] stripG z =
        (π : ℂ) ^ 2 * ((Complex.sin u ^ 2 - u ^ 2 * Complex.cos u) / (u ^ 4 * (Complex.sin u / u) ^ 2)) := by
      rw [hz_eq]
      have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hsin_ne : Complex.sin u ≠ 0 := sin_pi_ne_zero_halfStrip (by simpa [z] using hσ0.le) (by simpa [z] using hσ1)
        (fun h => by have := congrArg Complex.re h; simp [z] at this; linarith)
      have hz_ne : z ≠ 0 := fun h => by have := congrArg Complex.re h; simp [z] at this; linarith
      have h1z : (1 : ℂ) / z ^ 2 = (π : ℂ) ^ 2 / u ^ 2 := by dsimp [u]; rw [mul_pow]; field_simp [hpi, hz_ne]
      rw [h1z]; field_simp [hu_ne, hsin_ne]; ring
    rw [hid, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, norm_div, norm_mul, norm_pow, norm_pow]
    have hu4 : ‖u‖ ^ 4 ≠ 0 := pow_ne_zero 4 (norm_pos_iff.mpr hu_ne).ne'
    have hdiv_le : ‖Complex.sin u ^ 2 - u ^ 2 * Complex.cos u‖ / (‖u‖ ^ 4 * ‖Complex.sin u / u‖ ^ 2) ≤
        0.20 / (0.399 : ℝ) ^ 2 := by
      calc ‖Complex.sin u ^ 2 - u ^ 2 * Complex.cos u‖ / (‖u‖ ^ 4 * ‖Complex.sin u / u‖ ^ 2)
          ≤ (0.20 * ‖u‖ ^ 4) / (‖u‖ ^ 4 * ‖Complex.sin u / u‖ ^ 2) := by gcongr
        _ = 0.20 / ‖Complex.sin u / u‖ ^ 2 := by field_simp
        _ ≤ 0.20 / (0.399 : ℝ) ^ 2 := by gcongr
    have hpi2 : π ^ 2 ≤ (9.87 : ℝ) := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
    have h16 : π ^ 2 * (‖Complex.sin u ^ 2 - u ^ 2 * Complex.cos u‖ / (‖u‖ ^ 4 * ‖Complex.sin u / u‖ ^ 2)) ≤ 16 :=
      (mul_le_mul hpi2 hdiv_le (by positivity) (by positivity)).trans (by norm_num)
    exact h16.trans ((le_div_iff₀ (pow_pos h1s_pos 2)).mpr (by nlinarith))
  · have hcos_bd : ‖Complex.cos ((π : ℂ) * z)‖ ≤ 2 := by
      have harg : (π : ℂ) * z = ((π * σ : ℝ) : ℂ) + ((π * t : ℝ) : ℂ) * Complex.I := Complex.ext (by simp [z]) (by simp [z])
      rw [harg]
      refine (cos_complex_norm_le_cosh (π * σ) (π * t)).trans ?_
      have hcosh : Real.cosh (π * t) ≤ Real.cosh (π / 4) := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : 0 < π / 4)]; nlinarith [Real.pi_pos]
      have h2 : Real.cosh (π / 4) ≤ 2 := by
        have hpi4 : π / 4 ≤ 1 := by nlinarith [Real.pi_lt_d4]
        have he1 : Real.exp (π / 4) ≤ 2.7183 := (Real.exp_le_exp.mpr hpi4).trans ((Real.exp_one_lt_d9.le).trans (by norm_num))
        have hneg : Real.exp (-(π / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
        rw [Real.cosh_eq]; linarith
      exact hcosh.trans h2
    have hsin_bd : 4 * (1 - σ) ^ 2 ≤ ‖Complex.sin ((π : ℂ) * z)‖ ^ 2 := by
      have harg : (π : ℂ) * z = ((π * σ : ℝ) : ℂ) + ((π * t : ℝ) : ℂ) * Complex.I := Complex.ext (by simp [z]) (by simp [z])
      rw [harg, sin_complex_norm_sq, show π * σ = π - π * (1 - σ) by ring, Real.sin_pi_sub]
      have hjord := Real.mul_le_sin (mul_nonneg Real.pi_pos.le h1s_pos.le) (by nlinarith [Real.pi_pos])
      have hid : 2 / π * (π * (1 - σ)) = 2 * (1 - σ) := by field_simp [Real.pi_ne_zero]
      nlinarith [sq_nonneg (Real.sinh (π * t))]
    have hz_inv : ‖1 / z ^ 2‖ ≤ 4 := by
      have hz_sq : (1 / 4 : ℝ) ≤ ‖z‖ ^ 2 := by
        rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]; simp [z]; nlinarith [sq_nonneg t]
      rw [norm_div, norm_one, norm_pow, div_le_iff₀ (by linarith)]; linarith
    have hpi2 : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
    have hterm1 : π ^ 2 * ‖Complex.cos ((π : ℂ) * z)‖ / ‖Complex.sin ((π : ℂ) * z)‖ ^ 2 ≤ 5 / (1 - σ) ^ 2 := by
      calc π ^ 2 * ‖Complex.cos ((π : ℂ) * z)‖ / ‖Complex.sin ((π : ℂ) * z)‖ ^ 2
          ≤ 10 * 2 / (4 * (1 - σ) ^ 2) := div_le_div₀ (by norm_num) (mul_le_mul hpi2 hcos_bd (norm_nonneg _) (by positivity))
              (by positivity) hsin_bd
        _ = 5 / (1 - σ) ^ 2 := by field_simp; ring
    have h4_le : (4 : ℝ) ≤ 1 / (1 - σ) ^ 2 := (le_div_iff₀ (pow_pos h1s_pos 2)).mpr (by nlinarith)
    rw [hz_eq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, norm_pow]
    have hsum : 5 / (1 - σ) ^ 2 + 1 / (1 - σ) ^ 2 ≤ 16 / (1 - σ) ^ 2 := by rw [← add_div]; gcongr; norm_num
    linarith


/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CohnElkies.integral_cos_sq_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.integral_cos_sq_ge

/-- info: 'FormalResearch.CohnElkies.stripG_reflection_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.stripG_reflection_eq

/-- info: 'FormalResearch.CohnElkies.saddle_tan_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.saddle_tan_eq

/-- info: 'FormalResearch.CohnElkies.exists_unique_saddleSigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.exists_unique_saddleSigma

/-- info: 'FormalResearch.CohnElkies.saddle_endpoint_scales' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.saddle_endpoint_scales

/-- info: 'FormalResearch.CohnElkies.saddleEpsL_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.saddleEpsL_bounds

/-- info: 'FormalResearch.CohnElkies.deriv2_stripG_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.deriv2_stripG_norm_le

end FormalResearch.CohnElkies
