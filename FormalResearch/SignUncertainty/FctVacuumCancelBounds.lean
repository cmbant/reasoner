/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctCompDPart2
public import FormalResearch.SignUncertainty.FctVacuumField

/-!
# `fct:physical-budget` (c): pointwise bounds for the finite-part cancellation in the `t`-variable (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:physical-budget` (c), Lemma `fct:comp-D` (1), `fct:phikill` (1).

Elementary, reusable pointwise bounds for the concrete datum `v = vTotal`, `θ = ϑ_{D₀} = fctThetaD (v0 …)`,
`Δ_curv = stripDeltaCurv c θ`, `F₀(t) = α_osc |H₀(it)| / m(t)`, `ρ(t) = Re φ_kill(it; a)`:

* `uct_m_lower_small`, `uct_m_lower_large`: `m(t) ≥ c t²`, `m'(t) ≥ c t` on `(0, 1/8]`, `m'(t) ≥ c/(1+t)` and `m(t) ≥ m(1/8)` on `[1/8, ∞)`;
* `F0_bounds`: `F₀(t) ≤ K t⁻⁴` on `(0, 1/8]`, `F₀(t) ≤ K e^{-πt}` on `[1/8, ∞)`;
* `phiKill_re_le`: `|ρ(t)| ≤ K min((t/a)⁸, 1)`;
* `vTotal_bounds`: `|v(t)| ≤ M τ₁²` and `v(t) = 0` for `t ≥ 10τ₁`;
* `stripDeltaCurv_bounds`: `|Δ_curv(t)| ≤ C τ₁³` on `(0, 12τ₁]`, `≤ C τ₁⁷ t⁻⁴` on `[12τ₁, 1/8]`, `≤ C τ₁⁷ (1+t) e^{-πt/2}` on `[1/8, ∞)`
  (from `(fct:th-inner)` for `r = 1, 2` and `(fct:th-tail)`).

Class: proved, no hypotheses.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.CohnElkies FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCompD
  FormalResearch.SignUncertainty.FctPhiKill FormalResearch.SignUncertainty.FctMoment

/-! ### Lower bounds for `m` and `m'` -/

/-- `m(t) ≥ c t²` and `m'(t) ≥ c t` on `(0, 1/8]`. -/
lemma uct_m_lower_small : ∃ c > 0, ∀ t ∈ Ioc (0 : ℝ) (1 / 8), c * t ^ 2 ≤ uctM t ∧ c * t ≤ uctMderiv t := by
  obtain ⟨mQ_min, hmQ_min_pos, hmQ_min_bd⟩ : ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) (1 / 8), c ≤ mQ t := by
    have hcont := contDiffOn_mQ.continuousOn.mono (show Icc (0 : ℝ) (1 / 8) ⊆ Ioo (-1 / 4) (1 / 4) from
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMinOn
      ⟨0, le_rfl, by norm_num⟩ hcont
    exact ⟨mQ t₀, mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩), fun t ht => hmin ht⟩
  obtain ⟨mD_min, hmD_min_pos, hmD_min_bd⟩ : ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) (1 / 8), c ≤ mD t := by
    have hcont := contDiffOn_mD.continuousOn.mono (show Icc (0 : ℝ) (1 / 8) ⊆ Ioo (-1 / 4) (1 / 4) from
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMinOn
      ⟨0, le_rfl, by norm_num⟩ hcont
    exact ⟨mD t₀, mD_pos_of_mem (abs_lt.mpr ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩), fun t ht => hmin ht⟩
  refine ⟨min mQ_min mD_min, lt_min hmQ_min_pos hmD_min_pos, fun t ht => ⟨?_, ?_⟩⟩
  · rw [uctM_eq_sq_mul_mQ ht.1, mul_comm (min mQ_min mD_min)]
    exact mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (hmQ_min_bd t ⟨ht.1.le, ht.2⟩)) (sq_nonneg t)
  · rw [uctMderiv_eq_mul_mD ht.1 (by linarith [ht.2]), mul_comm (min mQ_min mD_min)]
    exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (hmD_min_bd t ⟨ht.1.le, ht.2⟩)) ht.1.le

/-- `m(t) ≤ C t²` on `(0, 1/8]`. -/
lemma uct_m_upper_small : ∃ C > 0, ∀ t ∈ Ioc (0 : ℝ) (1 / 8), uctM t ≤ C * t ^ 2 := by
  have hcont := contDiffOn_mQ.continuousOn.mono (show Icc (0 : ℝ) (1 / 8) ⊆ Ioo (-1 / 4) (1 / 4) from
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_bound_of_continuousOn hcont
  refine ⟨max M 1, lt_max_of_lt_right one_pos, fun t ht => ?_⟩
  rw [uctM_eq_sq_mul_mQ ht.1, mul_comm]
  have h1 : mQ t ≤ M := (le_abs_self _).trans (by simpa using hM t ⟨ht.1.le, ht.2⟩)
  exact mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) (sq_nonneg t)

/-- `m'(t) ≥ 1/(50 (1+t))` for `t ≥ 1/8`, and `m(t) ≥ m(1/8)`. -/
lemma uct_m_lower_large : (∀ t : ℝ, 1 / 8 ≤ t → 1 / 50 / (1 + t) ≤ uctMderiv t) ∧
    ∀ t : ℝ, 1 / 8 ≤ t → uctM (1 / 8) ≤ uctM t := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have ht0 : 0 < t := by linarith
    have hu : 0 < π * t := by positivity
    have hsh_ge : π * t + (π * t) ^ 3 / 6 ≤ Real.sinh (π * t) := by
      have h_s : ∀ s : ℝ, 0 ≤ s → s ≤ Real.sinh s := fun s hs => by
        have hd : ∀ x, HasDerivAt (fun y => Real.sinh y - y) (Real.cosh x - 1) x := fun x =>
          (Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)
        have hm := monotoneOn_of_deriv_nonneg (f := fun y => Real.sinh y - y) (convex_Ici 0)
          (Real.continuous_sinh.sub continuous_id).continuousOn
          (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
          (fun x _ => by rw [(hd x).deriv]; linarith [Real.one_le_cosh x])
        have := hm (le_rfl : (0 : ℝ) ∈ Ici 0) hs hs; simp only [Real.sinh_zero, sub_self] at this; linarith
      have h_c : ∀ s : ℝ, 0 ≤ s → 1 + s ^ 2 / 2 ≤ Real.cosh s := fun s hs => by
        have hd : ∀ x, HasDerivAt (fun y => Real.cosh y - 1 - y ^ 2 / 2) (Real.sinh x - x) x := fun x =>
          (((Real.hasDerivAt_cosh x).sub (hasDerivAt_const x 1)).sub ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv (by simp)
        have hm := monotoneOn_of_deriv_nonneg (f := fun y => Real.cosh y - 1 - y ^ 2 / 2) (convex_Ici 0)
          ((Real.continuous_cosh.sub continuous_const).sub ((continuous_id.pow 2).div_const 2)).continuousOn
          (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
          (fun x hx => by
            rw [(hd x).deriv]
            have hx0 : 0 ≤ x := (interior_Ici (a := (0 : ℝ)) ▸ hx).le
            linarith [h_s x hx0])
        have := hm (le_rfl : (0 : ℝ) ∈ Ici 0) hs hs
        simp only [Real.cosh_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_self] at this; linarith
      have hd : ∀ x, HasDerivAt (fun y => Real.sinh y - y - y ^ 3 / 6) (Real.cosh x - 1 - x ^ 2 / 2) x := fun x =>
        (((Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)).sub ((hasDerivAt_pow 3 x).div_const 6)).congr_deriv (by ring)
      have hm := monotoneOn_of_deriv_nonneg (f := fun y => Real.sinh y - y - y ^ 3 / 6) (convex_Ici 0)
        ((Real.continuous_sinh.sub continuous_id).sub ((continuous_id.pow 3).div_const 6)).continuousOn
        (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
        (fun x hx => by
          rw [(hd x).deriv]
          have hx0 : 0 ≤ x := (interior_Ici (a := (0 : ℝ)) ▸ hx).le
          linarith [h_c x hx0])
      have := hm (le_rfl : (0 : ℝ) ∈ Ici 0) hu.le hu.le
      simp only [Real.sinh_zero, zero_pow (by norm_num : 3 ≠ 0), zero_div, sub_self] at this; linarith
    have hmd_eq : uctMderiv t = 1 / t - π / Real.sinh (π * t) := by
      unfold uctMderiv uctEllDeriv; field_simp [Real.pi_ne_zero, ht0.ne']
    rw [hmd_eq]
    have hsh_pos : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr hu
    have h1 : π / Real.sinh (π * t) ≤ π / (π * t + (π * t) ^ 3 / 6) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hsh_ge
    have h2 : 1 / t - π / (π * t + (π * t) ^ 3 / 6) = (π ^ 2 * t / 6) / (1 + (π * t) ^ 2 / 6) := by
      field_simp [ht0.ne', Real.pi_ne_zero]; ring
    have h3 : (1 / 50 : ℝ) / (1 + t) ≤ (π ^ 2 * t / 6) / (1 + (π * t) ^ 2 / 6) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
      nlinarith [sq_nonneg t]
    linarith
  · exact uctM_strictMonoOn.monotoneOn (by norm_num : (0 : ℝ) < 1 / 8) (by simp only [mem_Ioi]; linarith) ht

lemma uctM_continuousOn : ContinuousOn uctM (Ioi 0) := fun _ ht => (hasDerivAt_uctM ht).continuousAt.continuousWithinAt

lemma uctMderiv_continuousOn : ContinuousOn uctMderiv (Ioi 0) := by
  unfold uctMderiv uctEllDeriv
  refine continuousOn_const.mul ((continuousOn_const.div ((continuousOn_const.mul continuousOn_id).div_const 2)
    fun t (ht : t ∈ Ioi (0 : ℝ)) => (div_pos (mul_pos Real.pi_pos ht) two_pos).ne').sub
    (continuousOn_const.div (Real.continuous_sinh.comp (continuous_const.mul ((continuous_const.mul continuous_id).div_const 2))).continuousOn
      fun t (ht : t ∈ Ioi (0 : ℝ)) => (Real.sinh_pos_iff.mpr (mul_pos two_pos (div_pos (mul_pos Real.pi_pos ht) two_pos))).ne'))

/-! ### `F₀`, `ρ` and `v` -/

/-- `F₀(t) = α_osc ‖H₀(it)‖ / m(t)`. -/
noncomputable def vacF0 (kind : StripKernelChoice) (t : ℝ) : ℝ :=
  uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t

lemma uctAlphaOsc_nonneg : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity

lemma vacF0_nonneg (kind : StripKernelChoice) {t : ℝ} (ht : 0 < t) : 0 ≤ vacF0 kind t := by
  unfold vacF0
  have := uctM_pos ht
  have := uctAlphaOsc_nonneg
  positivity

/-- `F₀(t) ≤ K t⁻⁴` on `(0, 1/8]` and `F₀(t) ≤ K e^{-πt}` on `[1/8, ∞)`. -/
lemma vacF0_bounds (kind : StripKernelChoice) : ∃ K ≥ 0, ∀ t : ℝ, 0 < t →
    (t ≤ 1 / 8 → vacF0 kind t ≤ K / t ^ 4) ∧ (1 / 8 ≤ t → vacF0 kind t ≤ K * Real.exp (-(π * t))) := by
  obtain ⟨cm, hcm, hcm_bd⟩ := uct_m_lower_small
  obtain ⟨-, hm_large⟩ := uct_m_lower_large
  have hm18 : 0 < uctM (1 / 8) := uctM_pos (by norm_num)
  have hα := uctAlphaOsc_nonneg
  set B : ℝ := 64 * (1 + π ^ 2 / 4) * Real.exp π + 4 * π ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨max (uctAlphaOsc * (1 + π ^ 2 / 4) / cm) (uctAlphaOsc * B / uctM (1 / 8)), by positivity, fun t ht => ⟨fun ht18 => ?_, fun ht18 => ?_⟩⟩
  · have hH := (norm_stripH0_imag_le kind ht).1
    have hm := (hcm_bd t ⟨ht, ht18⟩).1
    unfold vacF0
    have h1 : uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ≤
        uctAlphaOsc * ((1 + π ^ 2 / 4) / t ^ 2) / (cm * t ^ 2) := by
      gcongr
    refine h1.trans ?_
    rw [show uctAlphaOsc * ((1 + π ^ 2 / 4) / t ^ 2) / (cm * t ^ 2) = (uctAlphaOsc * (1 + π ^ 2 / 4) / cm) / t ^ 4 by
      field_simp]
    gcongr
    exact le_max_left _ _
  · have hH : ‖stripH0 kind ((t : ℂ) * Complex.I)‖ ≤ B * Real.exp (-(π * t)) := by
      rcases le_or_gt 1 t with ht1 | ht1
      · refine ((norm_stripH0_imag_le kind ht).2 ht1).trans ?_
        gcongr
        linarith [show 0 ≤ 64 * (1 + π ^ 2 / 4) * Real.exp π by positivity]
      · have h1 := (norm_stripH0_imag_le kind ht).1
        have ht2 : 1 / 64 ≤ t ^ 2 := by nlinarith
        have h2 : (1 + π ^ 2 / 4) / t ^ 2 ≤ 64 * (1 + π ^ 2 / 4) := by
          rw [div_le_iff₀ (by positivity)]; nlinarith [show 0 ≤ 1 + π ^ 2 / 4 by positivity]
        have h3 : Real.exp π * Real.exp (-(π * t)) ≥ 1 := by
          rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith [Real.pi_pos]
        calc ‖stripH0 kind ((t : ℂ) * Complex.I)‖ ≤ 64 * (1 + π ^ 2 / 4) := h1.trans h2
          _ ≤ 64 * (1 + π ^ 2 / 4) * (Real.exp π * Real.exp (-(π * t))) := le_mul_of_one_le_right (by positivity) h3
          _ ≤ B * Real.exp (-(π * t)) := by
            rw [hB]; nlinarith [Real.exp_pos (-(π * t)), Real.exp_pos π, sq_nonneg π]
    have hm := hm_large t ht18
    unfold vacF0
    have h1 : uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ≤
        uctAlphaOsc * (B * Real.exp (-(π * t))) / uctM (1 / 8) := by
      gcongr
    refine h1.trans ?_
    rw [show uctAlphaOsc * (B * Real.exp (-(π * t))) / uctM (1 / 8) = (uctAlphaOsc * B / uctM (1 / 8)) * Real.exp (-(π * t)) by
      ring]
    gcongr
    exact le_max_right _ _

/-- `|Re φ_kill(it; a)| ≤ K min((t/a)⁸, 1)`. -/
lemma phiKill_re_le : ∃ K ≥ 0, ∀ {a t : ℝ}, 0 < a → 0 < t →
    |(phiKill a ((t : ℂ) * Complex.I)).re| ≤ K * min ((t / a) ^ 8) 1 := by
  obtain ⟨C, hC0, hC⟩ := norm_phiPQ_le 8 8
  refine ⟨C, hC0, fun {a t} ha ht => ?_⟩
  have hz : ‖(t : ℂ) * Complex.I‖ = t := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have := hC (a := a) (z := (t : ℂ) * Complex.I) ha (by simp)
  rw [hz] at this
  exact (Complex.abs_re_le_norm _).trans this

/-- The total compensator `v = vTotal` is continuous, `|v| ≤ M τ₁²`, and `v = 0` for `t ≥ 10 τ₁`. -/
lemma vTotal_bounds (kind : StripKernelChoice) :
    ∃ τ₀ > 0, ∀ K4 : ℝ, 1 ≤ K4 → ∃ M ≥ 0, ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ →
      τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
      Continuous (vTotal kind K4 c α τ₁) ∧ (∀ t, |vTotal kind K4 c α τ₁ t| ≤ M * τ₁ ^ 2) ∧
        ∀ t, 10 * τ₁ ≤ t → vTotal kind K4 c α τ₁ t = 0 := by
  obtain ⟨τ₀, hτ₀, hτ₀20, Cv0b, Cv0m, Cva, Cv1b, Cv1m, _, _, _, _, _, _, _, _, _, _, _, _, hCv_nn, _, _, _, hpart1⟩ :=
    fct_comp_D_part1 kind
  refine ⟨min τ₀ (1 / 20), lt_min hτ₀ (by norm_num), fun K4 hK4 => ?_⟩
  have hK40 : 0 ≤ K4 := by linarith
  obtain ⟨h1, h2, h3, h4, h5⟩ := hCv_nn 0
  refine ⟨Cv0b 0 + K4 * Cv0m 0 + Cv1b 0 + K4 * Cv1m 0 + Cva 0, by positivity, fun {c α τ₁} hc hτ₁ hτ₁_le hc_eq hα_le => ?_⟩
  have hτ₁_p1 : τ₁ ≤ τ₀ := hτ₁_le.trans (min_le_left _ _)
  have hτ₁_20 : τ₁ ≤ 1 / 20 := hτ₁_le.trans (min_le_right _ _)
  have hτ₁_1 : τ₁ ≤ 1 := by linarith
  have hc_inv : c⁻¹ = τ₁ ^ 4 := by
    rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hc_eq ⊢; linarith
  have hα1 : |α| ≤ 1 := hα_le.trans (pow_le_one₀ hτ₁.le hτ₁_1)
  obtain ⟨⟨_, _, _, _, _, hv_cd⟩, _, _, ⟨_, _, _, _, _, hv_s, _⟩, _, _, hderivs, _⟩ :=
    hpart1 hK4 hc hτ₁ hτ₁_p1 hc_eq hα_le
  refine ⟨hv_cd.continuous, fun t => ?_, fun t ht => ?_⟩
  · obtain ⟨d1, d2, d3, d4, d5⟩ := hderivs 0 t
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at d1 d2 d3 d4 d5
    have hτ4 : τ₁ ^ (4 : ℤ) ≤ τ₁ ^ 2 := by
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have h1b : c⁻¹ * τ₁ ^ (-1 : ℤ) ≤ τ₁ ^ 2 := by
      rw [hc_inv, zpow_neg_one, show τ₁ ^ 4 * τ₁⁻¹ = τ₁ ^ 3 by field_simp [hτ₁.ne']]
      exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have h1m : c⁻¹ * τ₁ ^ (1 : ℤ) ≤ τ₁ ^ 2 := by
      rw [hc_inv, zpow_one, ← pow_succ]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have d1' : |v0Base kind τ₁ t| ≤ Cv0b 0 * τ₁ ^ 2 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast] at d1; exact d1
    have d2' : |v0Marg τ₁ t| ≤ Cv0m 0 * τ₁ ^ 2 := d2.trans (mul_le_mul_of_nonneg_left hτ4 (hCv_nn 0).2.1)
    have d3' : |vAlpha α τ₁ t| ≤ Cva 0 * τ₁ ^ 2 := d3.trans (by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
      have := mul_le_mul_of_nonneg_left hα1 (hCv_nn 0).2.2.1; rw [mul_one] at this
      exact mul_le_mul_of_nonneg_right this (sq_nonneg τ₁))
    have d4' : |v1Base kind c τ₁ t| ≤ Cv1b 0 * τ₁ ^ 2 :=
      d4.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1b (hCv_nn 0).2.2.2.1)
    have d5' : |v1Marg c τ₁ t| ≤ Cv1m 0 * τ₁ ^ 2 :=
      d5.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1m (hCv_nn 0).2.2.2.2)
    have htri : |vTotal kind K4 c α τ₁ t| ≤ |v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t| + |v1Base kind c τ₁ t| +
        K4 * |v1Marg c τ₁ t| + |vAlpha α τ₁ t| := by
      unfold vTotal v0 v1
      have a1 := abs_add_le ((v0Base kind τ₁ t + K4 * v0Marg τ₁ t) + (v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t)) (vAlpha α τ₁ t)
      have a2 := abs_add_le (v0Base kind τ₁ t + K4 * v0Marg τ₁ t) (v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t)
      have a3 := abs_add_le (v0Base kind τ₁ t) (K4 * v0Marg τ₁ t)
      have a4 := abs_add_le (v1Base kind c τ₁ t) (K4 * v1Marg c τ₁ t)
      rw [abs_mul, abs_of_nonneg hK40] at a3 a4; linarith
    have hm1 := mul_le_mul_of_nonneg_left d2' hK40
    have hm2 := mul_le_mul_of_nonneg_left d5' hK40
    calc |vTotal kind K4 c α τ₁ t| ≤ |v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t| + |v1Base kind c τ₁ t| +
          K4 * |v1Marg c τ₁ t| + |vAlpha α τ₁ t| := htri
      _ ≤ Cv0b 0 * τ₁ ^ 2 + K4 * (Cv0m 0 * τ₁ ^ 2) + Cv1b 0 * τ₁ ^ 2 + K4 * (Cv1m 0 * τ₁ ^ 2) + Cva 0 * τ₁ ^ 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add d1' hm1) d4') hm2) d3'
      _ = (Cv0b 0 + K4 * Cv0m 0 + Cv1b 0 + K4 * Cv1m 0 + Cva 0) * τ₁ ^ 2 := by ring
  · by_contra hne
    have := (hv_s hne).2
    linarith

/-! ### Pointwise bounds on `Δ_curv` -/

lemma abs_delta_le {c a b m1 m2 : ℝ} (hc : 0 < c) (hm1 : 0 < m1) (hm2 : 0 < m2) :
    |(1 / (2 * c)) * (a / m1 - b / m2)| ≤ (c⁻¹ / 2) * (|a| / m1 + |b| / m2) := by
  rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * c))]
  have h1 : |a / m1 - b / m2| ≤ |a| / m1 + |b| / m2 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_div, abs_of_pos hm1, abs_of_pos hm2]
  calc 1 / (2 * c) * |a / m1 - b / m2| ≤ 1 / (2 * c) * (|a| / m1 + |b| / m2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c⁻¹ / 2 * (|a| / m1 + |b| / m2) := by
        rw [show 1 / (2 * c) = c⁻¹ / 2 by field_simp]

set_option maxHeartbeats 1600000 in
/-- Pointwise bounds on `Δ_curv(t) = (1/2c)(ϑ''(t)/m'(t) - ϑ'(t)/m(t))`, `ϑ = ϑ_{D₀}`, from `(fct:th-inner)` (`r = 1, 2`) and
`(fct:th-tail)`: `≤ C τ₁³` on `(0, 12τ₁]`, `≤ C τ₁⁷ t⁻⁴` on `[12τ₁, 1/8]`, `≤ C τ₁⁷ (1+t) e^{-πt/2}` on `[1/8, ∞)`. -/
lemma stripDeltaCurv_bounds (kind : StripKernelChoice) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 100 ∧ ∀ K4 : ℝ, 1 ≤ K4 → ∃ C ≥ 0, ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ →
      τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
      (∀ t : ℝ, 0 < t → t ≤ 12 * τ₁ → |stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t| ≤ C * τ₁ ^ 3) ∧
      (∀ t : ℝ, 12 * τ₁ ≤ t → t ≤ 1 / 8 → |stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t| ≤ C * τ₁ ^ 7 / t ^ 4) ∧
      (∀ t : ℝ, 1 / 8 ≤ t → |stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t| ≤
          C * τ₁ ^ 7 * ((1 + t) * Real.exp (-(π / 2) * t))) ∧
      ContinuousOn (stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁))) (Ioi 0) := by
  obtain ⟨τ₀_p1, hτ₀_p1_pos, hτ₀_p1_20, Cv0b, Cv0m, Cva, Cv1b, Cv1m, Cth0b, Cth0m, Ctha, Cth1b, Cth1m,
    CL1_0b, CL1_0m, CL1_a, CL1_1b, CL1_1m, C_tail, C_int, hCv_nn, hCth_nn, hCL1_nn, hCti_nn, hpart1⟩ :=
    fct_comp_D_part1 kind
  obtain ⟨cm, hcm, hcm_bd⟩ := uct_m_lower_small
  obtain ⟨hmd_large, hm_large⟩ := uct_m_lower_large
  have hm18 : 0 < uctM (1 / 8) := uctM_pos (by norm_num)
  refine ⟨min τ₀_p1 (1 / 100), lt_min hτ₀_p1_pos (by norm_num), min_le_right _ _, fun K4 hK4 => ?_⟩
  have hK40 : 0 ≤ K4 := by linarith
  set M1 : ℝ := Cth0b 1 + K4 * Cth0m 1 with hM1
  set M2 : ℝ := Cth0b 2 + K4 * Cth0m 2 with hM2
  set T1 : ℝ := C_tail 1 * (CL1_0b + K4 * CL1_0m) with hT1
  set T2 : ℝ := C_tail 2 * (CL1_0b + K4 * CL1_0m) with hT2
  have hM1nn : 0 ≤ M1 := by obtain ⟨h1, h2, _, _, _⟩ := hCth_nn 1; positivity
  have hM2nn : 0 ≤ M2 := by obtain ⟨h1, h2, _, _, _⟩ := hCth_nn 2; positivity
  have hL1nn : 0 ≤ CL1_0b + K4 * CL1_0m := by obtain ⟨h1, h2, _, _, _⟩ := hCL1_nn; positivity
  have hT1nn : 0 ≤ T1 := mul_nonneg (hCti_nn 1).1 hL1nn
  have hT2nn : 0 ≤ T2 := mul_nonneg (hCti_nn 2).1 hL1nn
  set Ci : ℝ := (M1 + M2) * 12 ^ 8 / (2 * cm) with hCi
  set Cm : ℝ := (T1 + T2) / (2 * cm) with hCm
  set Cl : ℝ := (T2 * (512 * 50) + T1 * 64 / uctM (1 / 8)) / 2 with hCl
  have hCinn : 0 ≤ Ci := by positivity
  have hCmnn : 0 ≤ Cm := by positivity
  have hClnn : 0 ≤ Cl := by positivity
  refine ⟨Ci + Cm + Cl, by positivity, fun {c α τ₁} hc hτ₁ hτ₁_le hc_eq hα_le => ?_⟩
  have hτ₁_p1 : τ₁ ≤ τ₀_p1 := hτ₁_le.trans (min_le_left _ _)
  have hτ₁_100 : τ₁ ≤ 1 / 100 := hτ₁_le.trans (min_le_right _ _)
  have hτ₁_1 : τ₁ ≤ 1 := by linarith
  have hc_inv : c⁻¹ = τ₁ ^ 4 := by
    rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hc_eq ⊢; linarith
  obtain ⟨⟨hb0_cd, hm0_cd, _, _, _, hv_cd⟩, _, _, ⟨hb0_s, hm0_s, _, _, _, hv_s, _⟩,
    hmom, hinner, hderivs, _, hth_in, htail, _, _, _⟩ := hpart1 hK4 hc hτ₁ hτ₁_p1 hc_eq hα_le
  have hb0_cs := hasCompactSupport_of_support_Ioo hb0_s
  have hm0_cs := hasCompactSupport_of_support_Ioo hm0_s
  have hθ0b_cd := contDiff_fctThetaD hb0_cd hb0_cs
  have hθ0m_cd := contDiff_fctThetaD hm0_cd hm0_cs
  have hlin : fctThetaD (v0 kind K4 τ₁) = fun s => fctThetaD (v0Base kind τ₁) s + K4 * fctThetaD (v0Marg τ₁) s := by
    ext s; unfold v0
    simpa only [one_mul] using fctThetaD_linear hb0_cd hb0_cs hm0_cd hm0_cs 1 K4 s
  -- inner bounds `|ϑ'| ≤ M₁ τ₁ (t/τ₁)^{10}`, `|ϑ''| ≤ M₂ (t/τ₁)^9` for `0 < t ≤ 12τ₁`
  have hτ3 : τ₁ ^ ((4 : ℤ) - (1 : ℕ)) ≤ τ₁ := by
    rw [show (4 : ℤ) - (1 : ℕ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    simpa using pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num : 1 ≤ 3)
  have hτ2 : τ₁ ^ ((4 : ℤ) - (2 : ℕ)) ≤ 1 := by
    rw [show (4 : ℤ) - (2 : ℕ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact pow_le_one₀ hτ₁.le hτ₁_1
  have hd1_le : ∀ t : ℝ, 0 < t → t ≤ 12 * τ₁ → |deriv (fctThetaD (v0 kind K4 τ₁)) t| ≤ M1 * τ₁ * (t / τ₁) ^ 10 := by
    intro t ht0 ht12
    have h1 := hth_in 1 t (by rw [abs_of_pos ht0]; exact ht12)
    rw [← iteratedDeriv_one, hlin]
    change |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s) t| ≤ _
    rw [iteratedDeriv_add (hθ0b_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
      ((contDiff_const.mul hθ0m_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
      iteratedDeriv_const_mul_field]
    have hmin : min (1 : ℝ) ((|t| / τ₁) ^ 10) ≤ (t / τ₁) ^ 10 := by rw [abs_of_pos ht0]; exact min_le_right _ _
    have d1 : |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 1 * τ₁ * (t / τ₁) ^ 10 := by
      have h1' : |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 1 * τ₁ * min 1 ((|t| / τ₁) ^ 10) := by
        simpa [show (2 : ℤ) - (1 : ℕ) = 1 by norm_num] using h1.1
      exact h1'.trans (mul_le_mul_of_nonneg_left hmin (mul_nonneg (hCth_nn 1).1 hτ₁.le))
    have d2 : |iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t| ≤ Cth0m 1 * τ₁ * (t / τ₁) ^ 10 :=
      h1.2.1.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ3 (hCth_nn 1).2.1)
        (le_min zero_le_one (by positivity))).trans (mul_le_mul_of_nonneg_left hmin (mul_nonneg (hCth_nn 1).2.1 hτ₁.le)))
    calc |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t + K4 * iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t|
        ≤ |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| + K4 * |iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t| :=
          (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hK40])
      _ ≤ Cth0b 1 * τ₁ * (t / τ₁) ^ 10 + K4 * (Cth0m 1 * τ₁ * (t / τ₁) ^ 10) :=
          add_le_add d1 (mul_le_mul_of_nonneg_left d2 hK40)
      _ = M1 * τ₁ * (t / τ₁) ^ 10 := by rw [hM1]; ring
  have hd2_le : ∀ t : ℝ, 0 < t → t ≤ 12 * τ₁ → |iteratedDeriv 2 (fctThetaD (v0 kind K4 τ₁)) t| ≤ M2 * (t / τ₁) ^ 9 := by
    intro t ht0 ht12
    have h2 := hth_in 2 t (by rw [abs_of_pos ht0]; exact ht12)
    rw [hlin]
    change |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s) t| ≤ _
    rw [iteratedDeriv_add (hθ0b_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
      ((contDiff_const.mul hθ0m_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
      iteratedDeriv_const_mul_field]
    have hmin : min (1 : ℝ) ((|t| / τ₁) ^ 9) ≤ (t / τ₁) ^ 9 := by rw [abs_of_pos ht0]; exact min_le_right _ _
    have d1 : |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 2 * (t / τ₁) ^ 9 := by
      have h2' : |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 2 * min 1 ((|t| / τ₁) ^ 9) := by
        simpa [show (2 : ℤ) - (2 : ℕ) = 0 by norm_num] using h2.1
      exact h2'.trans (mul_le_mul_of_nonneg_left hmin (hCth_nn 2).1)
    have d2 : |iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t| ≤ Cth0m 2 * (t / τ₁) ^ 9 := by
      refine h2.2.1.trans ?_
      have := mul_le_mul_of_nonneg_left hτ2 (hCth_nn 2).2.1; rw [mul_one] at this
      exact (mul_le_mul_of_nonneg_right this (le_min zero_le_one (by positivity))).trans
        (mul_le_mul_of_nonneg_left hmin (hCth_nn 2).2.1)
    calc |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t + K4 * iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t|
        ≤ |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| + K4 * |iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t| :=
          (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hK40])
      _ ≤ Cth0b 2 * (t / τ₁) ^ 9 + K4 * (Cth0m 2 * (t / τ₁) ^ 9) :=
          add_le_add d1 (mul_le_mul_of_nonneg_left d2 hK40)
      _ = M2 * (t / τ₁) ^ 9 := by rw [hM2]; ring
  -- tail bounds
  have htail1 : ∀ t : ℝ, 12 * τ₁ ≤ t → |deriv (fctThetaD (v0 kind K4 τ₁)) t| ≤
      T1 * τ₁ ^ 3 * (t ^ 2)⁻¹ * Real.exp (-(π / 2) * t) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have := (htail 1 t (by rw [abs_of_pos ht0]; exact ht)).1
    rw [← iteratedDeriv_one]
    rw [abs_of_pos ht0, show -(1 + ((1 : ℕ) : ℤ)) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast] at this
    simpa only [hT1, mul_assoc] using this
  have htail2 : ∀ t : ℝ, 12 * τ₁ ≤ t → |iteratedDeriv 2 (fctThetaD (v0 kind K4 τ₁)) t| ≤
      T2 * τ₁ ^ 3 * (t ^ 3)⁻¹ * Real.exp (-(π / 2) * t) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have := (htail 2 t (by rw [abs_of_pos ht0]; exact ht)).1
    rw [abs_of_pos ht0, show -(1 + ((2 : ℕ) : ℤ)) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast] at this
    simpa only [hT2, mul_assoc] using this
  refine ⟨fun t ht0 ht12 => ?_, fun t ht12 ht18 => ?_, fun t ht18 => ?_, ?_⟩
  · -- inner region
    have ht18 : t ≤ 1 / 8 := by linarith
    obtain ⟨hm2, hmd⟩ := hcm_bd t ⟨ht0, ht18⟩
    have hmpos : 0 < uctM t := uctM_pos ht0
    have hmdpos : 0 < uctMderiv t := uctMderiv_pos ht0
    unfold stripDeltaCurv
    refine (abs_delta_le hc hmdpos hmpos).trans ?_
    have hx : t / τ₁ ≤ 12 := by rw [div_le_iff₀ hτ₁]; linarith
    have hx0 : 0 ≤ t / τ₁ := by positivity
    have hx8 : (t / τ₁) ^ 8 ≤ 12 ^ 8 := pow_le_pow_left₀ hx0 hx 8
    have hx9 : (t / τ₁) ^ 9 ≤ 12 ^ 8 * (t / τ₁) := by
      calc (t / τ₁) ^ 9 = (t / τ₁) ^ 8 * (t / τ₁) := by ring
        _ ≤ 12 ^ 8 * (t / τ₁) := mul_le_mul_of_nonneg_right hx8 hx0
    have hx10 : (t / τ₁) ^ 10 ≤ 12 ^ 8 * (t / τ₁) ^ 2 := by
      calc (t / τ₁) ^ 10 = (t / τ₁) ^ 8 * (t / τ₁) ^ 2 := by ring
        _ ≤ 12 ^ 8 * (t / τ₁) ^ 2 := mul_le_mul_of_nonneg_right hx8 (sq_nonneg _)
    have hA : |iteratedDeriv 2 (fctThetaD (v0 kind K4 τ₁)) t| / uctMderiv t ≤ M2 * 12 ^ 8 / (cm * τ₁) := by
      calc |iteratedDeriv 2 (fctThetaD (v0 kind K4 τ₁)) t| / uctMderiv t
          ≤ (M2 * (12 ^ 8 * (t / τ₁))) / (cm * t) := by
            refine div_le_div₀ (by positivity) ((hd2_le t ht0 ht12).trans (mul_le_mul_of_nonneg_left hx9 hM2nn)) (by positivity) hmd
        _ = M2 * 12 ^ 8 / (cm * τ₁) := by field_simp
    have hB : |deriv (fctThetaD (v0 kind K4 τ₁)) t| / uctM t ≤ M1 * 12 ^ 8 / (cm * τ₁) := by
      calc |deriv (fctThetaD (v0 kind K4 τ₁)) t| / uctM t
          ≤ (M1 * τ₁ * (12 ^ 8 * (t / τ₁) ^ 2)) / (cm * t ^ 2) := by
            refine div_le_div₀ (by positivity) ((hd1_le t ht0 ht12).trans
              (mul_le_mul_of_nonneg_left hx10 (mul_nonneg hM1nn hτ₁.le))) (by positivity) hm2
        _ = M1 * 12 ^ 8 / (cm * τ₁) := by field_simp
    calc c⁻¹ / 2 * (|iteratedDeriv 2 (fctThetaD (v0 kind K4 τ₁)) t| / uctMderiv t +
          |deriv (fctThetaD (v0 kind K4 τ₁)) t| / uctM t)
        ≤ τ₁ ^ 4 / 2 * (M2 * 12 ^ 8 / (cm * τ₁) + M1 * 12 ^ 8 / (cm * τ₁)) := by
          rw [hc_inv]; gcongr
      _ = Ci * τ₁ ^ 3 := by rw [hCi]; field_simp; ring
      _ ≤ (Ci + Cm + Cl) * τ₁ ^ 3 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · -- middle region
    have ht0 : 0 < t := by linarith
    obtain ⟨hm2, hmd⟩ := hcm_bd t ⟨ht0, ht18⟩
    have hmpos : 0 < uctM t := uctM_pos ht0
    have hmdpos : 0 < uctMderiv t := uctMderiv_pos ht0
    unfold stripDeltaCurv
    refine (abs_delta_le hc hmdpos hmpos).trans ?_
    have hex : Real.exp (-(π / 2) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr; nlinarith [Real.pi_pos]
    have hA : |iteratedDeriv 2 (fctThetaD (v0 kind K4 τ₁)) t| / uctMderiv t ≤ T2 * τ₁ ^ 3 / (cm * t ^ 4) := by
      calc |iteratedDeriv 2 (fctThetaD (v0 kind K4 τ₁)) t| / uctMderiv t
          ≤ (T2 * τ₁ ^ 3 * (t ^ 3)⁻¹ * 1) / (cm * t) := by
            refine div_le_div₀ (by positivity) ((htail2 t ht12).trans ?_) (by positivity) hmd
            gcongr
        _ = T2 * τ₁ ^ 3 / (cm * t ^ 4) := by field_simp
    have hB : |deriv (fctThetaD (v0 kind K4 τ₁)) t| / uctM t ≤ T1 * τ₁ ^ 3 / (cm * t ^ 4) := by
      calc |deriv (fctThetaD (v0 kind K4 τ₁)) t| / uctM t
          ≤ (T1 * τ₁ ^ 3 * (t ^ 2)⁻¹ * 1) / (cm * t ^ 2) := by
            refine div_le_div₀ (by positivity) ((htail1 t ht12).trans ?_) (by positivity) hm2
            gcongr
        _ = T1 * τ₁ ^ 3 / (cm * t ^ 4) := by field_simp
    calc c⁻¹ / 2 * (|iteratedDeriv 2 (fctThetaD (v0 kind K4 τ₁)) t| / uctMderiv t +
          |deriv (fctThetaD (v0 kind K4 τ₁)) t| / uctM t)
        ≤ τ₁ ^ 4 / 2 * (T2 * τ₁ ^ 3 / (cm * t ^ 4) + T1 * τ₁ ^ 3 / (cm * t ^ 4)) := by
          rw [hc_inv]; gcongr
      _ = Cm * τ₁ ^ 7 / t ^ 4 := by rw [hCm]; field_simp; ring
      _ ≤ (Ci + Cm + Cl) * τ₁ ^ 7 / t ^ 4 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
  · -- large region
    have ht0 : 0 < t := by linarith
    have ht12 : 12 * τ₁ ≤ t := by linarith
    have hmpos : 0 < uctM t := uctM_pos ht0
    have hmdpos : 0 < uctMderiv t := uctMderiv_pos ht0
    have hmd := hmd_large t ht18
    have hm := hm_large t ht18
    unfold stripDeltaCurv
    refine (abs_delta_le hc hmdpos hmpos).trans ?_
    set E : ℝ := (1 + t) * Real.exp (-(π / 2) * t) with hE
    have hE0 : 0 ≤ E := by positivity
    have hex1 : Real.exp (-(π / 2) * t) ≤ E := by
      rw [hE]; exact le_mul_of_one_le_left (Real.exp_pos _).le (by linarith)
    have ht3 : (t ^ 3)⁻¹ ≤ 512 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      have : (1 / 8 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht18 3
      norm_num at this ⊢; linarith
    have ht2 : (t ^ 2)⁻¹ ≤ 64 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      have : (1 / 8 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) ht18 2
      norm_num at this ⊢; linarith
    have hA : |iteratedDeriv 2 (fctThetaD (v0 kind K4 τ₁)) t| / uctMderiv t ≤ T2 * τ₁ ^ 3 * (512 * 50) * E := by
      calc |iteratedDeriv 2 (fctThetaD (v0 kind K4 τ₁)) t| / uctMderiv t
          ≤ (T2 * τ₁ ^ 3 * 512 * Real.exp (-(π / 2) * t)) / (1 / 50 / (1 + t)) := by
            refine div_le_div₀ (by positivity) ((htail2 t ht12).trans ?_) (by positivity) hmd
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht3 (by positivity)) (Real.exp_pos _).le
        _ = T2 * τ₁ ^ 3 * (512 * 50) * E := by rw [hE]; field_simp
    have hB : |deriv (fctThetaD (v0 kind K4 τ₁)) t| / uctM t ≤ T1 * τ₁ ^ 3 * 64 / uctM (1 / 8) * E := by
      calc |deriv (fctThetaD (v0 kind K4 τ₁)) t| / uctM t
          ≤ (T1 * τ₁ ^ 3 * 64 * Real.exp (-(π / 2) * t)) / uctM (1 / 8) := by
            refine div_le_div₀ (by positivity) ((htail1 t ht12).trans ?_) hm18 hm
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht2 (by positivity)) (Real.exp_pos _).le
        _ ≤ T1 * τ₁ ^ 3 * 64 * E / uctM (1 / 8) := by
            gcongr
        _ = T1 * τ₁ ^ 3 * 64 / uctM (1 / 8) * E := by ring
    calc c⁻¹ / 2 * (|iteratedDeriv 2 (fctThetaD (v0 kind K4 τ₁)) t| / uctMderiv t +
          |deriv (fctThetaD (v0 kind K4 τ₁)) t| / uctM t)
        ≤ τ₁ ^ 4 / 2 * (T2 * τ₁ ^ 3 * (512 * 50) * E + T1 * τ₁ ^ 3 * 64 / uctM (1 / 8) * E) := by
          rw [hc_inv]; gcongr
      _ = Cl * τ₁ ^ 7 * E := by rw [hCl]; field_simp
      _ ≤ (Ci + Cm + Cl) * τ₁ ^ 7 * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hE0
  · -- continuity on `(0, ∞)`
    have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) (v0 kind K4 τ₁) := hb0_cd.add (contDiff_const.mul hm0_cd)
    have hθ0_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (v0 kind K4 τ₁)) := contDiff_fctThetaD hv0_cd (by
      unfold v0
      exact hb0_cs.add hm0_cs.mul_left)
    exact continuousOn_const.mul (((contDiff_iteratedDeriv_infty hθ0_cd 2).continuous.continuousOn.div
      uctMderiv_continuousOn fun t ht => (uctMderiv_pos ht).ne').sub
      ((hθ0_cd.continuous_deriv (by simp)).continuousOn.div uctM_continuousOn fun t ht => (uctM_pos ht).ne'))

/-- info: 'FormalResearch.SignUncertainty.FctSym.vTotal_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vTotal_bounds

/-- info: 'FormalResearch.SignUncertainty.FctSym.stripDeltaCurv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripDeltaCurv_bounds

end FormalResearch.SignUncertainty.FctSym
