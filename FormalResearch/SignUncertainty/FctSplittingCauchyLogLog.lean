/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingWarp
public import FormalResearch.SignUncertainty.FctSplittingEdgeDeriv

/-!
# `log log` strip bound for the Cauchy splitting `F_±` and reduction of `SplittingRest.loglog`

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.8 (`fct:splitting`) (2),
proof of `|F_±(ζ)| ≤ M c⁻¹ log log(4 + |Im ζ|)` and the `log log` bound for `Φ̂_c` on `S̄`
assuming only the left-strip `Φ_c` bound on `{0 ≤ Re ζ ≤ 5/16}`.

From `FctDescentStmt h` (`‖F(σ + iy)‖ ≤ C c⁻¹ / log(2 + |y|)` on `5/16 ≤ σ ≤ 7/16`) alone:
* `fctCauchy_loglog_line`: for fixed `σ ∈ [3/8, 7/16]` and all `ζ ∈ S̄` with `|Re ζ - σ| ≥ 1/32`,
  `‖fctCauchy ... σ ζ‖ ≤ M c⁻¹ log log(4 + |Im ζ|)`.
* `fctPhiHat_loglog_of_left`: reduces `SplittingRest (fctPhiHat h ε c)` solely to bounding
  `‖fctPhiC ... ζ‖` on `{ζ ∈ S̄ | ζ.re ≤ 5/16}`, using `fctPhiWarp_eq_right` (`σ = 3/8`)
  on `13/32 ≤ Re ζ ≤ 1`, `fctCauchy` (`σ = 7/16`) + `hD` directly on `5/16 ≤ Re ζ ≤ 13/32`,
  `fct_Nc_beta_bounds`, and `fctQ1_deriv_bounds`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-! ### Elementary `log log` lower bound and symmetric `|y|` integral helper -/

lemma log_log_four_pos : 0 < Real.log (Real.log 4) := by
  have hexp : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
  have h1 : 1 < Real.log 4 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp
  exact Real.log_pos h1

lemma log_log_four_le {η : ℝ} : Real.log (Real.log 4) ≤ Real.log (Real.log (4 + |η|)) := by
  have h1 : 1 < Real.log 4 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hlog : Real.log 4 ≤ Real.log (4 + |η|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg η])
  exact Real.log_le_log (by linarith) hlog

private lemma integral_abs_symm {g : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hg : ContinuousOn (fun y => g |y|) (Icc (-A) A)) :
    ∫ y in (-A)..A, g |y| = 2 * ∫ y in (0 : ℝ)..A, g y := by
  have hi_tot : IntervalIntegrable (fun y => g |y|) volume (-A) A :=
    hg.intervalIntegrable_of_Icc (by linarith)
  have hi_neg : IntervalIntegrable (fun y => g |y|) volume (-A) 0 :=
    hi_tot.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, hA⟩))
  have hi_pos : IntervalIntegrable (fun y => g |y|) volume 0 A :=
    hi_tot.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, hA⟩))
  rw [← intervalIntegral.integral_add_adjacent_intervals hi_neg hi_pos]
  have hrefl : ∫ y in (-A)..0, g |y| = ∫ y in (0 : ℝ)..A, g |y| := by
    have hcomp := intervalIntegral.integral_comp_neg (a := 0) (b := A) (f := fun y => g |y|)
    simpa [abs_neg] using hcomp.symm
  have hpos_eq : ∫ y in (0 : ℝ)..A, g |y| = ∫ y in (0 : ℝ)..A, g y :=
    intervalIntegral.integral_congr fun y hy => by
      rw [uIcc_of_le hA] at hy; simp [abs_of_nonneg hy.1]
  rw [hrefl, hpos_eq]
  ring

/-! ### Zone integrals for `|y| ≤ R/2`, `R/2 ≤ |y| ≤ 2R`, and `2R ≤ |y|` -/

private lemma zone1_integral_le {R : ℝ} (hR : 4 ≤ R) :
    ∫ y in (-(R / 2))..(R / 2), 1 / ((2 + |y|) * Real.log (2 + |y|)) ≤
      2 * (Real.log (Real.log (4 + R)) + |Real.log (Real.log 2)|) := by
  set g : ℝ → ℝ := fun u => 1 / ((2 + u) * Real.log (2 + u))
  have hg_cont : ContinuousOn (fun y => g |y|) (Icc (-(R / 2)) (R / 2)) := by
    refine ContinuousOn.div continuousOn_const (ContinuousOn.mul (by fun_prop) ?_) ?_
    · refine Real.continuousOn_log.comp (by fun_prop) fun y _ => ne_of_gt (by linarith [abs_nonneg y])
    · intro y _
      have hl : 0 < Real.log (2 + |y|) := Real.log_pos (by linarith [abs_nonneg y])
      exact mul_ne_zero (by linarith [abs_nonneg y]) hl.ne'
  rw [show (fun y : ℝ => 1 / ((2 + |y|) * Real.log (2 + |y|))) = fun y => g |y| from rfl]
  rw [integral_abs_symm (by linarith) hg_cont]
  have hderiv : ∀ y ∈ uIcc (0 : ℝ) (R / 2),
      HasDerivAt (fun u : ℝ => Real.log (Real.log (2 + u))) (g y) y := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    have h2y : (1 : ℝ) < 2 + y := by linarith [hy.1]
    have hlog_pos : 0 < Real.log (2 + y) := Real.log_pos h2y
    have hd1 : HasDerivAt (fun u : ℝ => Real.log (2 + u)) (1 / (2 + y)) y := by
      have hlin : HasDerivAt (fun u : ℝ => 2 + u) 1 y := (hasDerivAt_id y).const_add 2
      simpa using hlin.log (by linarith)
    refine (hd1.log hlog_pos.ne').congr_deriv ?_
    simp [g, div_eq_mul_inv, mul_comm]
  have hint : IntervalIntegrable g volume 0 (R / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith)]
    exact (hg_cont.mono (fun y (hy : y ∈ Icc 0 (R / 2)) => ⟨by linarith [hy.1], hy.2⟩)).congr
      (fun y (hy : y ∈ Icc 0 (R / 2)) => by simp [abs_of_nonneg hy.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, add_zero]
  have hll_le : Real.log (Real.log (2 + R / 2)) ≤ Real.log (Real.log (4 + R)) := by
    have h1 : 1 < Real.log (2 + R / 2) :=
      (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
    exact Real.log_le_log (by linarith) (Real.log_le_log (by linarith) (by linarith))
  have hsub : Real.log (Real.log (2 + R / 2)) - Real.log (Real.log 2) ≤
      Real.log (Real.log (4 + R)) + |Real.log (Real.log 2)| := by
    linarith [neg_abs_le (Real.log (Real.log 2))]
  linarith

private lemma zone2_norm_integral_le {R η a b : ℝ} (hR : 4 ≤ R) (hη : |η| = R) (hab : a ≤ b)
    (hsub : Icc a b ⊆ Icc (-(2 * R)) (2 * R)) :
    ∫ y in a..b, 1 / (1 / 32 + |y - η|) ≤ 2 * (Real.log 32 + 2 * Real.log (2 + R / 2)) := by
  have hg_cont : Continuous fun u : ℝ => 1 / (1 / 32 + |u|) :=
    Continuous.div continuous_const (continuous_const.add continuous_abs) fun u => by
      linarith [abs_nonneg u]
  have hle_big : ∫ y in a..b, 1 / (1 / 32 + |y - η|) ≤
      ∫ y in (η - 3 * R)..(η + 3 * R), 1 / (1 / 32 + |y - η|) := by
    have hi : IntervalIntegrable (fun y => 1 / (1 / 32 + |y - η|)) volume (η - 3 * R) (η + 3 * R) :=
      (hg_cont.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
    have hη_le := abs_le.mp hη.le
    have ha1 : η - 3 * R ≤ a := by linarith [(hsub (left_mem_Icc.mpr hab)).1, hη_le.2]
    have hb1 : b ≤ η + 3 * R := by linarith [(hsub (right_mem_Icc.mpr hab)).2, hη_le.1]
    exact intervalIntegral.integral_mono_interval ha1 hab hb1 (ae_of_all _ fun y => by positivity) hi
  have hshift : ∫ y in (η - 3 * R)..(η + 3 * R), 1 / (1 / 32 + |y - η|) =
      ∫ u in (-(3 * R))..(3 * R), 1 / (1 / 32 + |u|) := by
    have hcomp := intervalIntegral.integral_comp_sub_right (fun u : ℝ => 1 / (1 / 32 + |u|)) η
      (a := η - 3 * R) (b := η + 3 * R)
    simpa [sub_sub_cancel_left] using hcomp
  have hsym : ∫ u in (-(3 * R))..(3 * R), 1 / (1 / 32 + |u|) =
      2 * ∫ u in (0 : ℝ)..(3 * R), 1 / (1 / 32 + u) :=
    integral_abs_symm (g := fun u => 1 / (1 / 32 + u)) (A := 3 * R) (by linarith) hg_cont.continuousOn
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) (3 * R),
      HasDerivAt (fun x : ℝ => Real.log (1 / 32 + x)) (1 / (1 / 32 + u)) u := fun u hu => by
    rw [uIcc_of_le (by linarith)] at hu
    have hpos : 0 < 1 / 32 + u := by linarith [hu.1]
    have hlin : HasDerivAt (fun x : ℝ => 1 / 32 + x) 1 u := (hasDerivAt_id u).const_add (1 / 32)
    simpa using hlin.log hpos.ne'
  have hint : IntervalIntegrable (fun u : ℝ => 1 / (1 / 32 + u)) volume 0 (3 * R) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun u hu => ?_
    rw [uIcc_of_le (by linarith)] at hu
    linarith [hu.1]
  have hval : ∫ u in (0 : ℝ)..(3 * R), 1 / (1 / 32 + u) = Real.log (1 + 96 * R) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, add_zero,
      ← Real.log_div (by linarith) (by norm_num)]
    congr 1; ring
  have hlog_bd : Real.log (1 + 96 * R) ≤ Real.log 32 + 2 * Real.log (2 + R / 2) := by
    have hpoly : 1 + 96 * R ≤ 32 * (2 + R / 2) ^ 2 := by nlinarith
    have h1 := Real.log_le_log (by linarith) hpoly
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    simpa using h1
  calc ∫ y in a..b, 1 / (1 / 32 + |y - η|)
      ≤ ∫ y in (η - 3 * R)..(η + 3 * R), 1 / (1 / 32 + |y - η|) := hle_big
    _ = 2 * ∫ u in (0 : ℝ)..(3 * R), 1 / (1 / 32 + u) := hshift.trans hsym
    _ = 2 * Real.log (1 + 96 * R) := by rw [hval]
    _ ≤ 2 * (Real.log 32 + 2 * Real.log (2 + R / 2)) := by gcongr

private lemma zone3_pos_integral_le {R T : ℝ} (hR : 4 ≤ R) (hT : 2 * R ≤ T) :
    ∫ y in (2 * R)..T, R / y ^ 2 ≤ 1 / 2 := by
  have hderiv : ∀ y ∈ uIcc (2 * R) T, HasDerivAt (fun x : ℝ => -(R / x)) (R / y ^ 2) y := by
    intro y hy
    rw [uIcc_of_le hT] at hy
    have hypos : 0 < y := by linarith [hy.1]
    refine ((hasDerivAt_const y R).div (hasDerivAt_id y) hypos.ne').neg.congr_deriv ?_
    simp only [zero_mul, zero_sub, mul_one, neg_div, neg_neg, id_eq]
  have hint : IntervalIntegrable (fun y : ℝ => R / y ^ 2) volume (2 * R) T := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun y hy => ?_
    rw [uIcc_of_le hT] at hy
    have : 0 < y := by linarith [hy.1]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hRpos : 0 < R := by linarith
  have hTpos : 0 < T := by linarith
  calc -(R / T) - -(R / (2 * R)) = R / (2 * R) - R / T := by ring
    _ ≤ R / (2 * R) := sub_le_self _ (by positivity)
    _ = 1 / 2 := by field_simp [hRpos.ne']

/-! ### Kernel factorisation and zone-wise estimates for `fctCauchyIntegrand` -/

private lemma norm_zeta_le_norm_zeta_add_one {ζ : ℂ} (hre : 0 ≤ ζ.re) : ‖ζ‖ ≤ ‖ζ + 1‖ := by
  have hsq : Complex.normSq ζ ≤ Complex.normSq (ζ + 1) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      add_zero]
    nlinarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg ζ, norm_nonneg (ζ + 1)]

private lemma fctKsp_div_factor {t ζ : ℂ} (ht : t ≠ 0) (hζ1 : ζ + 1 ≠ 0) (htζ : t - ζ ≠ 0) :
    ‖fctKsp t ζ / (t - ζ)‖ =
      (‖ζ‖ / ‖ζ + 1‖) ^ 2 * (‖ζ‖ / ‖t - ζ‖) * (‖t + 1‖ ^ 2 / ‖t‖ ^ 3) := by
  unfold fctKsp
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_div, norm_div]
  have h1 : ‖ζ + 1‖ ≠ 0 := norm_ne_zero_iff.mpr hζ1
  have h2 : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have h3 : ‖t - ζ‖ ≠ 0 := norm_ne_zero_iff.mpr htζ
  field_simp [h1, h2, h3]

private lemma line_t_props {σ : ℝ} (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16)
    {ζ : ℂ} (hδ : 1 / 32 ≤ |ζ.re - σ|) (y : ℝ) :
    let t : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
    3 / 16 * (1 + |y|) ≤ ‖t‖ ∧ t ≠ 0 ∧ |y| ≤ ‖t‖ ∧ ‖t + 1‖ ≤ 2 + |y| ∧
    1 / 32 ≤ ‖t - ζ‖ ∧ |y - ζ.im| ≤ ‖t - ζ‖ ∧ t - ζ ≠ 0 := by
  intro t
  have ht_ge := norm_line_ge hσ y
  have ht_ne : t ≠ 0 := norm_pos_iff.mp (by linarith [abs_nonneg y])
  have ht_im : |y| ≤ ‖t‖ := by simpa [t] using Complex.abs_im_le_norm t
  have ht_add1 : ‖t + 1‖ ≤ 2 + |y| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (t + 1)
    have hre : |(t + 1).re| ≤ 2 := by simp [t, abs_le]; constructor <;> linarith
    have him : |(t + 1).im| = |y| := by simp [t]
    linarith
  have htz_re : 1 / 32 ≤ ‖t - ζ‖ := by
    have h1 : |(t - ζ).re| = |ζ.re - σ| := by
      simp only [t, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      exact abs_sub_comm σ ζ.re
    exact hδ.trans (h1 ▸ Complex.abs_re_le_norm (t - ζ))
  have htz_im : |y - ζ.im| ≤ ‖t - ζ‖ := by
    have h1 : |(t - ζ).im| = |y - ζ.im| := by simp [t]
    exact h1 ▸ Complex.abs_im_le_norm (t - ζ)
  exact ⟨ht_ge, ht_ne, ht_im, ht_add1, htz_re, htz_im, norm_pos_iff.mp (by linarith)⟩

private lemma fctCauchy_zone2_piece {K4 ε c L1 α C σ : ℝ} (hC : 0 ≤ C)
    (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16)
    (hF : ∀ y : ℝ, ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ C / Real.log (2 + |y|))
    {ζ : ℂ} (hδ : 1 / 32 ≤ |ζ.re - σ|) (hR : 4 ≤ |ζ.im|) (hζ_norm : ‖ζ‖ ≤ 2 * |ζ.im|)
    (hζ1_ge_R : |ζ.im| ≤ ‖ζ + 1‖)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ Icc (-(2 * |ζ.im|)) (2 * |ζ.im|))
    (hlo : ∀ y ∈ Icc a b, |ζ.im| / 2 ≤ |y|)
    (hi_lhs : IntervalIntegrable (fun y : ℝ => ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖) volume a b) :
    ∫ y in a..b, ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤
      (2304 * (Real.log 32 / Real.log 4 + 2) / Real.log (Real.log 4)) * C *
        Real.log (Real.log (4 + |ζ.im|)) := by
  set R : ℝ := |ζ.im|
  have hlog_mid_pos : 0 < Real.log (2 + R / 2) := Real.log_pos (by linarith)
  have hlog4_le_mid : Real.log 4 ≤ Real.log (2 + R / 2) := Real.log_le_log (by norm_num) (by linarith)
  have hll_le : Real.log (Real.log 4) ≤ Real.log (Real.log (4 + R)) := log_log_four_le
  have hll4_pos : 0 < Real.log (Real.log 4) := log_log_four_pos
  have hpt : ∀ y ∈ Icc a b,
      ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤
        (1152 * C / Real.log (2 + R / 2)) * (1 / (1 / 32 + |y - ζ.im|)) := by
    intro y hy
    have hy_abs_hi : |y| ≤ 2 * R := abs_le.mpr (hsub hy)
    have hy_abs_lo : R / 2 ≤ |y| := hlo y hy
    set t : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
    obtain ⟨_, ht_ne, ht_im, ht_add1, htz_re, htz_im, htz_ne⟩ := line_t_props hσ hσ' hδ y
    have hksp : ‖fctKsp t ζ‖ ≤ 576 := by
      unfold fctKsp
      rw [norm_mul, norm_pow, norm_pow, norm_div, norm_div]
      have hzr1 : ‖ζ‖ / ‖t‖ ≤ 4 := by
        rw [div_le_iff₀ (by linarith)]
        calc ‖ζ‖ ≤ 2 * R := hζ_norm
          _ = 4 * (R / 2) := by ring
          _ ≤ 4 * |y| := by gcongr
          _ ≤ 4 * ‖t‖ := by gcongr
      have hzr2 : ‖t + 1‖ / ‖ζ + 1‖ ≤ 3 := by
        rw [div_le_iff₀ (by linarith)]
        calc ‖t + 1‖ ≤ 2 + |y| := ht_add1
          _ ≤ 2 + 2 * R := by linarith
          _ ≤ 3 * R := by linarith
          _ ≤ 3 * ‖ζ + 1‖ := by gcongr
      have h1 : (‖ζ‖ / ‖t‖) ^ 3 ≤ 4 ^ 3 := pow_le_pow_left₀ (by positivity) hzr1 3
      have h2 : (‖t + 1‖ / ‖ζ + 1‖) ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ (by positivity) hzr2 2
      calc (‖ζ‖ / ‖t‖) ^ 3 * (‖t + 1‖ / ‖ζ + 1‖) ^ 2 ≤ 4 ^ 3 * 3 ^ 2 := by gcongr
        _ = 576 := by norm_num
    have hinv_tz : ‖t - ζ‖⁻¹ ≤ 2 / (1 / 32 + |y - ζ.im|) := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by positivity)]
      linarith
    have hf_bd : ‖fctFint K4 ε c L1 α t‖ ≤ C / Real.log (2 + R / 2) :=
      (hF y).trans (div_le_div_of_nonneg_left hC hlog_mid_pos
        (Real.log_le_log (by linarith) (by linarith)))
    unfold fctCauchyIntegrand
    rw [norm_div, norm_mul, div_eq_mul_inv, mul_assoc, mul_comm ‖fctFint _ _ _ _ _ t‖ _,
      ← mul_assoc]
    calc ‖fctKsp t ζ‖ * ‖t - ζ‖⁻¹ * ‖fctFint K4 ε c L1 α t‖
        ≤ 576 * (2 / (1 / 32 + |y - ζ.im|)) * (C / Real.log (2 + R / 2)) := by
          gcongr
      _ = (1152 * C / Real.log (2 + R / 2)) * (1 / (1 / 32 + |y - ζ.im|)) := by ring
  have hi_rhs : IntervalIntegrable (fun y : ℝ =>
      (1152 * C / Real.log (2 + R / 2)) * (1 / (1 / 32 + |y - ζ.im|))) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuous_id.sub continuous_const).abs.continuousOn) ?_)
    intro y _; positivity
  have hint_mono := intervalIntegral.integral_mono_on hab hi_lhs hi_rhs hpt
  rw [intervalIntegral.integral_const_mul] at hint_mono
  have hz2 := zone2_norm_integral_le hR rfl hab hsub
  have hlog32_nn : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  have hdiv_le : (Real.log 32 + 2 * Real.log (2 + R / 2)) / Real.log (2 + R / 2) ≤
      Real.log 32 / Real.log 4 + 2 := by
    rw [add_div, mul_div_cancel_right₀ _ hlog_mid_pos.ne']
    gcongr
  calc ∫ y in a..b, ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖
      ≤ (1152 * C / Real.log (2 + R / 2)) * ∫ y in a..b, 1 / (1 / 32 + |y - ζ.im|) := hint_mono
    _ ≤ (1152 * C / Real.log (2 + R / 2)) * (2 * (Real.log 32 + 2 * Real.log (2 + R / 2))) := by
        gcongr
    _ = 2304 * C * ((Real.log 32 + 2 * Real.log (2 + R / 2)) / Real.log (2 + R / 2)) := by ring
    _ ≤ 2304 * C * (Real.log 32 / Real.log 4 + 2) := by gcongr
    _ = (2304 * (Real.log 32 / Real.log 4 + 2) / Real.log (Real.log 4)) * C * Real.log (Real.log 4) := by
        field_simp [hll4_pos.ne']
    _ ≤ (2304 * (Real.log 32 / Real.log 4 + 2) / Real.log (Real.log 4)) * C *
          Real.log (Real.log (4 + R)) := by gcongr

private lemma fctCauchy_loglog_fixed {K4 ε c L1 α C σ Ksmall : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16)
    (hKsm0 : 0 ≤ Ksmall)
    (hKsm : ∀ ζ : ℂ, ‖ζ‖ ≤ 5 → 1 ≤ ‖ζ + 1‖ → 1 / 32 ≤ |ζ.re - σ| → ∀ y : ℝ,
      ‖fctKsp ((σ : ℂ) + y * Complex.I) ζ / ((σ : ℂ) + y * Complex.I - ζ)‖ ≤ Ksmall / (1 + |y|) ^ 2)
    (hF : ∀ y : ℝ, ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ C / Real.log (2 + |y|)) :
    ∀ ζ ∈ closedStrip, 1 / 32 ≤ |ζ.re - σ| →
      ‖fctCauchy K4 ε c L1 α σ ζ‖ ≤
        max ((1 / (2 * Real.pi)) * (Ksmall / Real.log 2) * (∫ y : ℝ, 1 / (1 + |y|) ^ 2) / Real.log (Real.log 4))
          ((1 / (2 * Real.pi)) *
            ((2 * (32 / (3 / 16 : ℝ) ^ 3) * (1 + |Real.log (Real.log 2)| / Real.log (Real.log 4))) +
              2 * (2304 * (Real.log 32 / Real.log 4 + 2) / Real.log (Real.log 4)) +
              ((16 / Real.log 2) / Real.log (Real.log 4)))) * C * Real.log (Real.log (4 + |ζ.im|)) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hll4_pos : 0 < Real.log (Real.log 4) := log_log_four_pos
  set I_sq : ℝ := ∫ y : ℝ, 1 / (1 + |y|) ^ 2
  have hIsq0 : 0 ≤ I_sq := integral_nonneg fun _ => by positivity
  set M_sm : ℝ := (1 / (2 * Real.pi)) * (Ksmall / Real.log 2) * I_sq / Real.log (Real.log 4)
  set c316 : ℝ := (3 / 16 : ℝ) ^ 3
  have hc316 : 0 < c316 := by positivity
  set M_z1 : ℝ := 2 * (32 / c316) * (1 + |Real.log (Real.log 2)| / Real.log (Real.log 4))
  set M_z2_half : ℝ := 2304 * (Real.log 32 / Real.log 4 + 2) / Real.log (Real.log 4)
  set M_z3 : ℝ := (16 / Real.log 2) / Real.log (Real.log 4)
  have hMz2_nn : 0 ≤ M_z2_half := by
    have : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
    positivity
  set M : ℝ := max M_sm ((1 / (2 * Real.pi)) * (M_z1 + 2 * M_z2_half + M_z3))
  have hM0 : 0 ≤ M := (show 0 ≤ M_sm by positivity).trans (le_max_left _ _)
  intro ζ hζ hδ
  have hll_le : Real.log (Real.log 4) ≤ Real.log (Real.log (4 + |ζ.im|)) := log_log_four_le
  have hll_pos : 0 < Real.log (Real.log (4 + |ζ.im|)) := lt_of_lt_of_le hll4_pos hll_le
  have hζ0 : 0 ≤ ζ.re := hζ.1
  have hζ1 : ζ.re ≤ 1 := hζ.2
  have hζ_add1 : 1 ≤ ‖ζ + 1‖ := by
    have hre : (1 : ℝ) ≤ (ζ + 1).re := by simp; linarith
    exact hre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm (ζ + 1)))
  have hζ_add1_ne : ζ + 1 ≠ 0 := norm_pos_iff.mp (by linarith)
  by_cases him4 : |ζ.im| ≤ 4
  · have hnorm_ζ : ‖ζ‖ ≤ 5 := by
      calc ‖ζ‖ ≤ |ζ.re| + |ζ.im| := Complex.norm_le_abs_re_add_abs_im ζ
        _ ≤ 1 + 4 := by rw [abs_of_nonneg hζ0]; linarith
        _ = 5 := by norm_num
    have hpt : ∀ y : ℝ, ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤
        (Ksmall * C / Real.log 2) * (1 / (1 + |y|) ^ 2) := fun y => by
      unfold fctCauchyIntegrand
      rw [div_eq_mul_inv, mul_assoc, mul_comm (fctFint _ _ _ _ _ _) _, ← mul_assoc, ← div_eq_mul_inv,
        norm_mul]
      have hk := hKsm ζ hnorm_ζ hζ_add1 hδ y
      have hf := hF y
      have hlog : C / Real.log (2 + |y|) ≤ C / Real.log 2 :=
        div_le_div_of_nonneg_left hC hlog2_pos (Real.log_le_log (by norm_num) (by linarith [abs_nonneg y]))
      calc ‖fctKsp ((σ : ℂ) + ↑y * I) ζ / ((σ : ℂ) + ↑y * I - ζ)‖ *
            ‖fctFint K4 ε c L1 α ((σ : ℂ) + ↑y * I)‖
          ≤ (Ksmall / (1 + |y|) ^ 2) * (C / Real.log 2) :=
            mul_le_mul hk (hf.trans hlog) (norm_nonneg _) (by positivity)
        _ = (Ksmall * C / Real.log 2) * (1 / (1 + |y|) ^ 2) := by ring
    have hint_g : Integrable (fun y : ℝ => (Ksmall * C / Real.log 2) * (1 / (1 + |y|) ^ 2)) :=
      integrable_inv_one_add_abs_sq.const_mul _
    have hI : ‖∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤
        (Ksmall * C / Real.log 2) * I_sq := by
      calc ‖∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α σ ζ y‖
          ≤ ∫ y : ℝ, ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ y : ℝ, (Ksmall * C / Real.log 2) * (1 / (1 + |y|) ^ 2) :=
            integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hint_g (ae_of_all _ hpt)
        _ = (Ksmall * C / Real.log 2) * I_sq := integral_const_mul _ _
    unfold fctCauchy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
    calc (1 / (2 * Real.pi)) * ‖∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α σ ζ y‖
        ≤ (1 / (2 * Real.pi)) * ((Ksmall * C / Real.log 2) * I_sq) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = M_sm * C * Real.log (Real.log 4) := by
          simp only [M_sm]; field_simp [hll4_pos.ne']
      _ ≤ M * C * Real.log (Real.log (4 + |ζ.im|)) := by
          gcongr; exact le_max_left _ _
  -- Large `|ζ.im|`: `4 ≤ R := |ζ.im|`
  push Not at him4
  set R : ℝ := |ζ.im|
  have hR : 4 ≤ R := him4.le
  set η : ℝ := ζ.im
  have hζ_norm : ‖ζ‖ ≤ 2 * R := by
    calc ‖ζ‖ ≤ |ζ.re| + |ζ.im| := Complex.norm_le_abs_re_add_abs_im ζ
      _ ≤ 1 + R := by rw [abs_of_nonneg hζ0]; linarith
      _ ≤ 2 * R := by linarith
  have hζ1_ge_R : R ≤ ‖ζ + 1‖ := by
    have h1 : |(ζ + 1).im| = R := by simp [R]
    exact h1 ▸ Complex.abs_im_le_norm (ζ + 1)
  have hratio_zeta : ‖ζ‖ / ‖ζ + 1‖ ≤ 1 :=
    div_le_one_of_le₀ (norm_zeta_le_norm_zeta_add_one hζ0) (norm_nonneg _)
  have hint_f : Integrable (fun y : ℝ => fctCauchyIntegrand K4 ε c L1 α σ ζ y) :=
    fctCauchyIntegrand_integrable hc hDc hσ hσ'
      (fun h => by rw [h, sub_self, abs_zero] at hδ; norm_num at hδ) (B := C / Real.log 2)
      (fun y => (hF y).trans (div_le_div_of_nonneg_left hC hlog2_pos
        (Real.log_le_log (by norm_num) (by linarith [abs_nonneg y]))))
  -- Zone 1 on `[-(R/2), R/2]`
  have hz1_int : ∫ y in (-(R / 2))..(R / 2), ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤
      M_z1 * C * Real.log (Real.log (4 + R)) := by
    have hpt : ∀ y ∈ Icc (-(R / 2)) (R / 2),
        ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤
          (32 / c316) * C * (1 / ((2 + |y|) * Real.log (2 + |y|))) := by
      intro y hy
      have hy_abs : |y| ≤ R / 2 := abs_le.mpr hy
      set t : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
      obtain ⟨ht_ge, ht_ne, _, ht_add1, _, htz_im, htz_ne⟩ := line_t_props hσ hσ' hδ y
      have htz_lo : R / 2 ≤ ‖t - ζ‖ := by
        have htri : R - |y| ≤ |y - η| := by
          have h := abs_add_le y (η - y)
          rw [add_sub_cancel, abs_sub_comm η y] at h
          linarith
        linarith
      have hzr : ‖ζ‖ / ‖t - ζ‖ ≤ 4 := by
        rw [div_le_iff₀ (by linarith)]
        calc ‖ζ‖ ≤ 2 * R := hζ_norm
          _ = 4 * (R / 2) := by ring
          _ ≤ 4 * ‖t - ζ‖ := by gcongr
      have ht_rat : ‖t + 1‖ ^ 2 / ‖t‖ ^ 3 ≤ (8 / c316) / (2 + |y|) := by
        have h1 : ‖t + 1‖ ≤ 2 * (1 + |y|) := by linarith [abs_nonneg y]
        have h2 : ‖t + 1‖ ^ 2 ≤ 4 * (1 + |y|) ^ 2 := by
          have := pow_le_pow_left₀ (norm_nonneg _) h1 2
          linarith
        have h3 : c316 * (1 + |y|) ^ 3 ≤ ‖t‖ ^ 3 := by
          have := pow_le_pow_left₀ (by positivity) ht_ge 3
          simpa [c316, mul_pow] using this
        have hpos1 : 0 < 1 + |y| := by positivity
        have hpos2 : 0 < c316 * (1 + |y|) ^ 3 := by positivity
        have hstep := div_le_div₀ (by positivity) h2 hpos2 h3
        have hsimp : (4 * (1 + |y|) ^ 2) / (c316 * (1 + |y|) ^ 3) = (4 / c316) / (1 + |y|) := by
          field_simp [hpos1.ne', hc316.ne']
        have hstep2 : (4 / c316) / (1 + |y|) ≤ (8 / c316) / (2 + |y|) := by
          rw [div_le_div_iff₀ hpos1 (by linarith [abs_nonneg y])]
          have : 2 + |y| ≤ 2 * (1 + |y|) := by linarith [abs_nonneg y]
          calc (4 / c316) * (2 + |y|) ≤ (4 / c316) * (2 * (1 + |y|)) := by gcongr
            _ = (8 / c316) * (1 + |y|) := by ring
        exact hstep.trans (hsimp.le.trans hstep2)
      have hk_bd : ‖fctKsp t ζ / (t - ζ)‖ ≤ 32 / c316 / (2 + |y|) := by
        rw [fctKsp_div_factor ht_ne hζ_add1_ne htz_ne]
        have hsq : (‖ζ‖ / ‖ζ + 1‖) ^ 2 ≤ 1 :=
          (pow_le_pow_left₀ (by positivity) hratio_zeta 2).trans_eq (one_pow 2)
        calc (‖ζ‖ / ‖ζ + 1‖) ^ 2 * (‖ζ‖ / ‖t - ζ‖) * (‖t + 1‖ ^ 2 / ‖t‖ ^ 3)
            ≤ 1 * 4 * ((8 / c316) / (2 + |y|)) := by gcongr
          _ = 32 / c316 / (2 + |y|) := by ring
      unfold fctCauchyIntegrand
      rw [div_eq_mul_inv, mul_assoc, mul_comm (fctFint _ _ _ _ _ _) _, ← mul_assoc, ← div_eq_mul_inv,
        norm_mul]
      calc ‖fctKsp t ζ / (t - ζ)‖ * ‖fctFint K4 ε c L1 α t‖
          ≤ (32 / c316 / (2 + |y|)) * (C / Real.log (2 + |y|)) :=
            mul_le_mul hk_bd (hF y) (norm_nonneg _) (by positivity)
        _ = (32 / c316) * C * (1 / ((2 + |y|) * Real.log (2 + |y|))) := by
            simp only [div_eq_mul_inv, mul_inv]; ring
    have hi_lhs : IntervalIntegrable (fun y : ℝ => ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖)
        volume (-(R / 2)) (R / 2) := hint_f.norm.intervalIntegrable
    have hi_rhs : IntervalIntegrable (fun y : ℝ =>
        (32 / c316) * C * (1 / ((2 + |y|) * Real.log (2 + |y|)))) volume (-(R / 2)) (R / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le (by linarith)]
      refine continuousOn_const.mul (ContinuousOn.div continuousOn_const (ContinuousOn.mul (by fun_prop) ?_) ?_)
      · refine Real.continuousOn_log.comp (by fun_prop) fun y _ => ne_of_gt (by linarith [abs_nonneg y])
      · intro y _; have : (1 : ℝ) < 2 + |y| := by linarith [abs_nonneg y]
        exact mul_ne_zero (by linarith) (Real.log_pos this).ne'
    have hint_mono := intervalIntegral.integral_mono_on (by linarith) hi_lhs hi_rhs hpt
    rw [intervalIntegral.integral_const_mul] at hint_mono
    have hz1 := zone1_integral_le hR
    have hlog_bd : Real.log (Real.log (4 + R)) + |Real.log (Real.log 2)| ≤
        (1 + |Real.log (Real.log 2)| / Real.log (Real.log 4)) * Real.log (Real.log (4 + R)) := by
      have h1 : |Real.log (Real.log 2)| ≤ (|Real.log (Real.log 2)| / Real.log (Real.log 4)) * Real.log (Real.log (4 + R)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀' hll4_pos]
        exact (mul_comm _ |Real.log (Real.log 2)|).trans_le (mul_le_mul_of_nonneg_left hll_le (abs_nonneg _))
      linarith
    calc ∫ y in (-(R / 2))..(R / 2), ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖
        ≤ (32 / c316) * C * ∫ y in (-(R / 2))..(R / 2), 1 / ((2 + |y|) * Real.log (2 + |y|)) := hint_mono
      _ ≤ (32 / c316) * C * (2 * (Real.log (Real.log (4 + R)) + |Real.log (Real.log 2)|)) := by gcongr
      _ ≤ (32 / c316) * C * (2 * ((1 + |Real.log (Real.log 2)| / Real.log (Real.log 4)) * Real.log (Real.log (4 + R)))) := by
          gcongr
      _ = M_z1 * C * Real.log (Real.log (4 + R)) := by simp only [M_z1]; ring
  -- Zone 3 pointwise bound (`2 * R ≤ |y|`)
  have hz3_pt : ∀ {y : ℝ}, 2 * R ≤ |y| →
      ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤ (16 * C / Real.log 2) * (R / y ^ 2) := by
    intro y hy
    set t : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
    obtain ⟨_, ht_ne, ht_im, ht_add1, _, htz_im, htz_ne⟩ := line_t_props hσ hσ' hδ y
    have hy_pos : 0 < |y| := by linarith
    have htz_lo : |y| / 2 ≤ ‖t - ζ‖ := by
      have htri : |y| - R ≤ |y - η| := by
        have : |y| ≤ |y - η| + |η| := by
          simpa [sub_add_cancel] using abs_add_le (y - η) η
        linarith
      linarith
    have h1 : ‖ζ‖ / ‖t - ζ‖ ≤ 4 * R / |y| := by
      rw [div_le_div_iff₀ (by linarith) hy_pos]
      calc ‖ζ‖ * |y| ≤ (2 * R) * |y| := by gcongr
        _ = 4 * R * (|y| / 2) := by ring
        _ ≤ 4 * R * ‖t - ζ‖ := by gcongr
    have h2 : ‖t + 1‖ ^ 2 / ‖t‖ ^ 3 ≤ 4 / |y| := by
      have ha : ‖t + 1‖ ≤ 2 * |y| := by linarith
      have hb : ‖t + 1‖ ^ 2 ≤ 4 * |y| ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) ha 2
        linarith
      have hc3 : |y| ^ 3 ≤ ‖t‖ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) ht_im 3
      calc ‖t + 1‖ ^ 2 / ‖t‖ ^ 3 ≤ (4 * |y| ^ 2) / |y| ^ 3 :=
            div_le_div₀ (by positivity) hb (pow_pos hy_pos 3) hc3
        _ = 4 / |y| := by field_simp [hy_pos.ne']
    have hk_bd : ‖fctKsp t ζ / (t - ζ)‖ ≤ 16 * (R / y ^ 2) := by
      rw [fctKsp_div_factor ht_ne hζ_add1_ne htz_ne]
      have hsq : (‖ζ‖ / ‖ζ + 1‖) ^ 2 ≤ 1 :=
        (pow_le_pow_left₀ (by positivity) hratio_zeta 2).trans_eq (one_pow 2)
      calc (‖ζ‖ / ‖ζ + 1‖) ^ 2 * (‖ζ‖ / ‖t - ζ‖) * (‖t + 1‖ ^ 2 / ‖t‖ ^ 3)
          ≤ 1 * (4 * R / |y|) * (4 / |y|) := by gcongr
        _ = 16 * (R / |y| ^ 2) := by ring
        _ = 16 * (R / y ^ 2) := by rw [sq_abs]
    have hlog_bd : ‖fctFint K4 ε c L1 α t‖ ≤ C / Real.log 2 :=
      (hF y).trans (div_le_div_of_nonneg_left hC hlog2_pos
        (Real.log_le_log (by norm_num) (by linarith [abs_nonneg y])))
    unfold fctCauchyIntegrand
    rw [div_eq_mul_inv, mul_assoc, mul_comm (fctFint _ _ _ _ _ _) _, ← mul_assoc, ← div_eq_mul_inv,
      norm_mul]
    calc ‖fctKsp t ζ / (t - ζ)‖ * ‖fctFint K4 ε c L1 α t‖
        ≤ (16 * (R / y ^ 2)) * (C / Real.log 2) := mul_le_mul hk_bd hlog_bd (norm_nonneg _) (by positivity)
      _ = (16 * C / Real.log 2) * (R / y ^ 2) := by ring
  -- Integral over `[-T, T]` for all `T ≥ 2 * R`
  have hT_bd : ∀ T : ℝ, 2 * R ≤ T →
      ‖∫ y in (-T)..T, fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤
        (M_z1 + 2 * M_z2_half + M_z3) * C * Real.log (Real.log (4 + R)) := by
    intro T hT
    have hnorm_le := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (a := -T) (b := T) (f := fun y => fctCauchyIntegrand K4 ε c L1 α σ ζ y)
    have hsplit : ∫ y in (-T)..T, ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ =
        (∫ y in (-T)..(-(2 * R)), ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖) +
        (∫ y in (-(2 * R))..(-(R / 2)), ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖) +
        (∫ y in (-(R / 2))..(R / 2), ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖) +
        (∫ y in (R / 2)..(2 * R), ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖) +
        (∫ y in (2 * R)..T, ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖) := by
      have hi : ∀ a b : ℝ, IntervalIntegrable (fun y => ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖) volume a b :=
        fun _ _ => hint_f.norm.intervalIntegrable
      rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-T) (2 * R)) (hi (2 * R) T)]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-T) (R / 2)) (hi (R / 2) (2 * R))]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-T) (-(R / 2))) (hi (-(R / 2)) (R / 2))]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-T) (-(2 * R))) (hi (-(2 * R)) (-(R / 2)))]
    have hz2_neg := fctCauchy_zone2_piece hC hσ hσ' hF hδ hR hζ_norm hζ1_ge_R
      (by linarith : -(2 * R) ≤ -(R / 2)) (fun y hy => ⟨hy.1, by linarith [hy.2]⟩)
      (fun y hy => by change R / 2 ≤ |y|; rw [abs_of_nonpos (by linarith [hy.2])]; linarith [hy.2])
      hint_f.norm.intervalIntegrable
    have hz2_pos := fctCauchy_zone2_piece hC hσ hσ' hF hδ hR hζ_norm hζ1_ge_R
      (by linarith : R / 2 ≤ 2 * R) (fun y hy => ⟨by linarith [hy.1], hy.2⟩)
      (fun y hy => by change R / 2 ≤ |y|; rw [abs_of_nonneg (by linarith [hy.1])]; exact hy.1)
      hint_f.norm.intervalIntegrable
    have hz3_rhs_int : IntervalIntegrable (fun y : ℝ => (16 * C / Real.log 2) * (R / y ^ 2)) volume (2 * R) T := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.mul (ContinuousOn.div continuousOn_const (by fun_prop) fun y hy => ?_)
      rw [uIcc_of_le hT] at hy
      have hy0 : 0 < y := by linarith [hy.1]
      exact pow_ne_zero 2 hy0.ne'
    have hz3_pos : ∫ y in (2 * R)..T, ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤ (8 / Real.log 2) * C := by
      have hm := intervalIntegral.integral_mono_on hT hint_f.norm.intervalIntegrable hz3_rhs_int
        fun y hy => hz3_pt (by rw [abs_of_nonneg (by linarith [hy.1])]; exact hy.1)
      rw [intervalIntegral.integral_const_mul] at hm
      calc ∫ y in (2 * R)..T, ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖
          ≤ (16 * C / Real.log 2) * ∫ y in (2 * R)..T, R / y ^ 2 := hm
        _ ≤ (16 * C / Real.log 2) * (1 / 2) := mul_le_mul_of_nonneg_left (zone3_pos_integral_le hR hT) (by positivity)
        _ = (8 / Real.log 2) * C := by ring
    have hz3_neg_int : IntervalIntegrable (fun y : ℝ => (16 * C / Real.log 2) * (R / y ^ 2)) volume (-T) (-(2 * R)) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.mul (ContinuousOn.div continuousOn_const (by fun_prop) fun y hy => ?_)
      rw [uIcc_of_le (by linarith)] at hy
      have hy0 : y < 0 := by linarith [hy.2]
      exact pow_ne_zero 2 hy0.ne
    have hz3_neg : ∫ y in (-T)..(-(2 * R)), ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤ (8 / Real.log 2) * C := by
      have hm := intervalIntegral.integral_mono_on (by linarith) hint_f.norm.intervalIntegrable hz3_neg_int
        fun y hy => hz3_pt (by rw [abs_of_nonpos (by linarith [hy.2])]; linarith [hy.2])
      rw [intervalIntegral.integral_const_mul] at hm
      have hrefl : ∫ y in (-T)..(-(2 * R)), R / y ^ 2 = ∫ y in (2 * R)..T, R / y ^ 2 := by
        have hcomp := intervalIntegral.integral_comp_neg (a := 2 * R) (b := T) (f := fun y : ℝ => R / y ^ 2)
        simpa [neg_sq] using hcomp.symm
      calc ∫ y in (-T)..(-(2 * R)), ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖
          ≤ (16 * C / Real.log 2) * ∫ y in (-T)..(-(2 * R)), R / y ^ 2 := hm
        _ = (16 * C / Real.log 2) * ∫ y in (2 * R)..T, R / y ^ 2 := by rw [hrefl]
        _ ≤ (16 * C / Real.log 2) * (1 / 2) := mul_le_mul_of_nonneg_left (zone3_pos_integral_le hR hT) (by positivity)
        _ = (8 / Real.log 2) * C := by ring
    have hz3_tot : (∫ y in (-T)..(-(2 * R)), ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖) +
        (∫ y in (2 * R)..T, ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖) ≤
        M_z3 * C * Real.log (Real.log (4 + R)) := by
      calc _ ≤ (8 / Real.log 2) * C + (8 / Real.log 2) * C := add_le_add hz3_neg hz3_pos
        _ = (16 / Real.log 2) * C := by ring
        _ = M_z3 * C * Real.log (Real.log 4) := by simp only [M_z3]; field_simp [hll4_pos.ne']
        _ ≤ M_z3 * C * Real.log (Real.log (4 + R)) := by gcongr
    calc ‖∫ y in (-T)..T, fctCauchyIntegrand K4 ε c L1 α σ ζ y‖
        ≤ ∫ y in (-T)..T, ‖fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ := by
          simpa [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < T)] using hnorm_le (by linarith)
      _ = _ := hsplit
      _ ≤ M_z1 * C * Real.log (Real.log (4 + R)) +
          2 * (M_z2_half * C * Real.log (Real.log (4 + R))) +
          M_z3 * C * Real.log (Real.log (4 + R)) := by linarith
      _ = (M_z1 + 2 * M_z2_half + M_z3) * C * Real.log (Real.log (4 + R)) := by ring
  have hlim : Tendsto (fun T : ℝ => ‖∫ y in (-T)..T, fctCauchyIntegrand K4 ε c L1 α σ ζ y‖)
      atTop (𝓝 ‖∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α σ ζ y‖) :=
    (intervalIntegral_tendsto_integral hint_f tendsto_neg_atTop_atBot tendsto_id).norm
  have hI : ‖∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤
      (M_z1 + 2 * M_z2_half + M_z3) * C * Real.log (Real.log (4 + R)) :=
    le_of_tendsto hlim (eventually_atTop.mpr ⟨2 * R, hT_bd⟩)
  unfold fctCauchy
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  calc (1 / (2 * Real.pi)) * ‖∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α σ ζ y‖
      ≤ (1 / (2 * Real.pi)) * ((M_z1 + 2 * M_z2_half + M_z3) * C * Real.log (Real.log (4 + R))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = ((1 / (2 * Real.pi)) * (M_z1 + 2 * M_z2_half + M_z3)) * C * Real.log (Real.log (4 + R)) := by ring
    _ ≤ M * C * Real.log (Real.log (4 + |ζ.im|)) := by gcongr; exact le_max_right _ _

/-- **Uniform `log log` Cauchy-splitting bound along a line `σ ∈ [3/8, 7/16]`** (`fct:splitting` (2)):
for fixed `σ ∈ [3/8, 7/16]`, there exist `M ≥ 0`, `c₀` such that for all `c ≥ c₀`, `ε = ±1`, and
`ζ ∈ S̄` with `|Re ζ - σ| ≥ 1/32`, `‖fctCauchy ... σ ζ‖ ≤ M * c⁻¹ * log log(4 + |Im ζ|)`. -/
theorem fctCauchy_loglog_line {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h)
    {σ : ℝ} (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16) :
    ∃ M c₀ : ℝ, 0 ≤ M ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ ζ ∈ closedStrip, 1 / 32 ≤ |ζ.re - σ| →
        ‖fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) σ ζ‖ ≤
          M * c⁻¹ * Real.log (Real.log (4 + |ζ.im|)) := by
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨c0D, hcD⟩ := fctDcomp_compData hK4 ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨Cdesc, c0Desc, hDesc⟩ := hD
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ Cdesc := by
    have hnn := (norm_nonneg _).trans (hDesc 1 (max c0Desc 1) (Or.inl rfl) (le_max_left _ _) (3 / 8) 0 (by norm_num) (by norm_num))
    have h1 : 0 ≤ Cdesc * (max c0Desc 1)⁻¹ :=
      (div_nonneg_iff.mp hnn).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr (by simpa using hlog2_pos)))
    exact nonneg_of_mul_nonneg_left h1 (by positivity)
  obtain ⟨Ksmall, hKsm0, hKsm⟩ := fctKsp_div_le_unif hσ hσ' (R := 5) (m := 1) (δ := 1 / 32)
    (by norm_num) one_pos (by norm_num)
  have hIsq0 : 0 ≤ ∫ y : ℝ, (1 : ℝ) / (1 + |y|) ^ 2 := integral_nonneg fun _ => by positivity
  have hll4_pos : 0 < Real.log (Real.log 4) := log_log_four_pos
  have hlog32_nn : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  set M_base : ℝ :=
    max ((1 / (2 * Real.pi)) * (Ksmall / Real.log 2) * (∫ y : ℝ, 1 / (1 + |y|) ^ 2) / Real.log (Real.log 4))
      ((1 / (2 * Real.pi)) *
        ((2 * (32 / (3 / 16 : ℝ) ^ 3) * (1 + |Real.log (Real.log 2)| / Real.log (Real.log 4))) +
          2 * (2304 * (Real.log 32 / Real.log 4 + 2) / Real.log (Real.log 4)) +
          ((16 / Real.log 2) / Real.log (Real.log 4))))
  have hMb0 : 0 ≤ M_base := (show 0 ≤ (1 / (2 * Real.pi)) * (Ksmall / Real.log 2) *
    (∫ y : ℝ, 1 / (1 + |y|) ^ 2) / Real.log (Real.log 4) by positivity).trans (le_max_left _ _)
  refine ⟨M_base * Cdesc, max (max c0D c0Desc) 1, by positivity, fun ε c hε hc ζ hζ hδ => ?_⟩
  have hc1 : 1 ≤ c := hc.trans' (le_max_right _ _)
  have hcpos : 0 < c := by linarith
  have hcD' := hcD ε c hε (hc.trans' ((le_max_left _ _).trans (le_max_left _ _)))
  have hcDesc' := hDesc ε c hε (hc.trans' ((le_max_right _ _).trans (le_max_left _ _)))
  obtain ⟨B, hB⟩ := hcD'.bd
  have hF : ∀ y : ℝ, ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((σ : ℂ) + y * Complex.I)‖ ≤
      (Cdesc * c⁻¹) / Real.log (2 + |y|) :=
    fun y => hcDesc' σ y (by linarith) hσ'
  have hfixed := fctCauchy_loglog_fixed hcpos (by positivity) hcD'.cont ⟨B, hB⟩ hσ hσ' hKsm0 hKsm hF ζ hζ hδ
  calc ‖fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) σ ζ‖
      ≤ M_base * (Cdesc * c⁻¹) * Real.log (Real.log (4 + |ζ.im|)) := hfixed
    _ = M_base * Cdesc * c⁻¹ * Real.log (Real.log (4 + |ζ.im|)) := by ring

/-- **Reduction of `SplittingRest.loglog` to `{ζ ∈ S̄ | ζ.re ≤ 5/16}`**:
from `FctDescentStmt h` alone, the Cauchy-splitting, `N_c⁻¹`, `β_c q₁`, and `5/16 ≤ Re ζ ≤ 1`
pieces all satisfy `O(log log (4 + |Im ζ|))`; only `fctPhiC` on `0 ≤ Re ζ ≤ 5/16` remains. -/
theorem fctPhiHat_loglog_of_left {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h)
    (hleft : ∃ c₀ M : ℝ, 0 ≤ M ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ ζ ∈ closedStrip, ζ.re ≤ 5 / 16 →
        ‖fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ ≤
          M * Real.log (Real.log (4 + |ζ.im|))) :
    ∃ c₀ M : ℝ, 0 ≤ M ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ ζ ∈ closedStrip,
        ‖fctPhiHat h ε c ζ‖ ≤ M * Real.log (Real.log (4 + |ζ.im|)) := by
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨c0D, hcD⟩ := fctDcomp_compData hK4 ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨Kβ, c0B, hKβ0, hNb⟩ := fct_Nc_beta_bounds hK4 hD
  obtain ⟨Mr, c0R, hMr0, hCr⟩ := fctCauchy_loglog_line hK4 hD (σ := 3 / 8) (by norm_num) (by norm_num)
  obtain ⟨Ml, c0L, hMl0, hCl⟩ := fctCauchy_loglog_line hK4 hD (σ := 7 / 16) (by norm_num) (by norm_num)
  obtain ⟨Cdesc, c0Desc, hDesc⟩ := hD
  obtain ⟨c0left, Mleft, hMl_0, hleft_bd⟩ := hleft
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ Cdesc := by
    have hnn := (norm_nonneg _).trans (hDesc 1 (max c0Desc 1) (Or.inl rfl) (le_max_left _ _) (3 / 8) 0 (by norm_num) (by norm_num))
    have h1 : 0 ≤ Cdesc * (max c0Desc 1)⁻¹ :=
      (div_nonneg_iff.mp hnn).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr (by simpa using hlog2_pos)))
    exact nonneg_of_mul_nonneg_left h1 (by positivity)
  have hll4_pos : 0 < Real.log (Real.log 4) := log_log_four_pos
  set c₀ : ℝ := max (max (max c0D c0B) (max c0R c0L)) (max (max c0Desc c0left) 1)
  set M_phi : ℝ := max ((Cdesc / Real.log 2 + 1) / Real.log (Real.log 4) + Ml)
    (max (1 / Real.log (Real.log 4) + Mr) (Mleft + Ml))
  set M : ℝ := 2 * M_phi + 4000 * Kβ / Real.log (Real.log 4)
  refine ⟨c₀, M, by positivity, fun ε c hε hc ζ hζ => ?_⟩
  have hc1 : 1 ≤ c := hc.trans' ((le_max_right _ _).trans (le_max_right _ _))
  have hcpos : 0 < c := by linarith
  have hcD' := hcD ε c hε (hc.trans' (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)))
  have hNb' := hNb ε c hε (hc.trans' (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)))
  have hCr' := hCr ε c hε (hc.trans' (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)))
  have hCl' := hCl ε c hε (hc.trans' (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)))
  have hDesc' := hDesc ε c hε (hc.trans' (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)))
  have hleft' := hleft_bd ε c hε (hc.trans' (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)))
  obtain ⟨B, hB⟩ := hcD'.bd
  set C_mid : ℝ := Cdesc / Real.log 2 + 1
  have hM_phi_eq : M_phi = max (C_mid / Real.log (Real.log 4) + Ml)
      (max (1 / Real.log (Real.log 4) + Mr) (Mleft + Ml)) := rfl
  have hll_le : Real.log (Real.log 4) ≤ Real.log (Real.log (4 + |ζ.im|)) := log_log_four_le
  have hll_nn : 0 ≤ Real.log (Real.log (4 + |ζ.im|)) := (hll4_pos.trans_le hll_le).le
  have h1_le_ll : 1 ≤ Real.log (Real.log (4 + |ζ.im|)) / Real.log (Real.log 4) := by
    rw [one_le_div hll4_pos]; exact hll_le
  have hc_inv_le : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
  have hq1 : ‖fctQ1 ζ‖ ≤ 4000 := (fctQ1_deriv_bounds hζ.1).1
  have hwarp_bd : ‖fctPhiWarp K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ ≤
      M_phi * Real.log (Real.log (4 + |ζ.im|)) := by
    by_cases hright : 13 / 32 ≤ ζ.re
    · have hF_bd : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 →
          ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((σ : ℂ) + y * Complex.I)‖ ≤
            max B (Cdesc / Real.log 2) := fun σ y hσ1 hσ2 => by
        have h1 := hDesc' σ y (by linarith) hσ2
        have h2 : Cdesc * c⁻¹ / Real.log (2 + |y|) ≤ Cdesc / Real.log 2 := by
          have hlog_nn : 0 ≤ Real.log (2 + |y|) := Real.log_nonneg (by linarith [abs_nonneg y])
          calc Cdesc * c⁻¹ / Real.log (2 + |y|)
              ≤ (Cdesc * 1) / Real.log (2 + |y|) :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc_inv_le hC0) hlog_nn
            _ = Cdesc / Real.log (2 + |y|) := by rw [mul_one]
            _ ≤ Cdesc / Real.log 2 := div_le_div_of_nonneg_left hC0 hlog2_pos
                (Real.log_le_log (by norm_num) (by linarith [abs_nonneg y]))
        exact h1.trans (h2.trans (le_max_right _ _))
      have hDb_max : ∀ w ∈ closedStrip, ‖fctDcompAt K4 c (fctWarpAlpha h ε c) w‖ ≤ max B (Cdesc / Real.log 2) :=
        fun w hw => (hB w hw).trans (le_max_left _ _)
      have heq := fctPhiWarp_eq_right (K4 := K4) (ε := ε) (c := c) (L1 := fctWarpL1 h ε c)
        (α := fctWarpAlpha h ε c) hcpos hcD'.hol hcD'.cont ⟨_, hDb_max⟩ hF_bd (by linarith : 3 / 8 < ζ.re)
      rw [heq]
      have hδ : 1 / 32 ≤ |ζ.re - 3 / 8| := by rw [abs_of_nonneg (by linarith)]; linarith
      have hcau : ‖fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8) ζ‖ ≤
          Mr * Real.log (Real.log (4 + |ζ.im|)) := by
        calc ‖fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8) ζ‖
            ≤ Mr * c⁻¹ * Real.log (Real.log (4 + |ζ.im|)) := hCr' ζ hζ hδ
          _ ≤ Mr * 1 * Real.log (Real.log (4 + |ζ.im|)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc_inv_le hMr0) hll_nn
          _ = Mr * Real.log (Real.log (4 + |ζ.im|)) := by ring
      have h1_ll : (1 : ℝ) ≤ (1 / Real.log (Real.log 4)) * Real.log (Real.log (4 + |ζ.im|)) := by
        simpa [div_eq_inv_mul, mul_comm] using h1_le_ll
      calc ‖1 - fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8) ζ‖
          ≤ ‖(1 : ℂ)‖ + ‖fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8) ζ‖ := norm_sub_le _ _
        _ ≤ (1 / Real.log (Real.log 4)) * Real.log (Real.log (4 + |ζ.im|)) +
              Mr * Real.log (Real.log (4 + |ζ.im|)) := by
            simpa only [norm_one] using add_le_add h1_ll hcau
        _ = (1 / Real.log (Real.log 4) + Mr) * Real.log (Real.log (4 + |ζ.im|)) := by ring
        _ ≤ M_phi * Real.log (Real.log (4 + |ζ.im|)) := by
            exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hll_nn
    · push Not at hright
      have hlt : ζ.re < 7 / 16 := by linarith
      have hwarp_eq : fctPhiWarp K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ =
          fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ -
            fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (7 / 16) ζ := by
        unfold fctPhiWarp; simp [hlt]
      rw [hwarp_eq]
      have hδ : 1 / 32 ≤ |ζ.re - 7 / 16| := by rw [abs_of_nonpos (by linarith)]; linarith
      have hcau : ‖fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (7 / 16) ζ‖ ≤
          Ml * Real.log (Real.log (4 + |ζ.im|)) := by
        calc ‖fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (7 / 16) ζ‖
            ≤ Ml * c⁻¹ * Real.log (Real.log (4 + |ζ.im|)) := hCl' ζ hζ hδ
          _ ≤ Ml * 1 * Real.log (Real.log (4 + |ζ.im|)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc_inv_le hMl0) hll_nn
          _ = Ml * Real.log (Real.log (4 + |ζ.im|)) := by ring
      by_cases hmid : 5 / 16 ≤ ζ.re
      · have hfint_bd : ‖fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ ≤ C_mid := by
          have hz_eq : ((ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I) = ζ := by apply Complex.ext <;> simp
          have h1 := hDesc' ζ.re ζ.im hmid (by linarith)
          rw [hz_eq] at h1
          have hlog : Cdesc * c⁻¹ / Real.log (2 + |ζ.im|) ≤ Cdesc / Real.log 2 := by
            have hlog_nn : 0 ≤ Real.log (2 + |ζ.im|) := Real.log_nonneg (by linarith [abs_nonneg ζ.im])
            calc Cdesc * c⁻¹ / Real.log (2 + |ζ.im|)
                ≤ (Cdesc * 1) / Real.log (2 + |ζ.im|) :=
                  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc_inv_le hC0) hlog_nn
              _ = Cdesc / Real.log (2 + |ζ.im|) := by rw [mul_one]
              _ ≤ Cdesc / Real.log 2 := div_le_div_of_nonneg_left hC0 hlog2_pos
                  (Real.log_le_log (by norm_num) (by linarith [abs_nonneg ζ.im]))
          have hphi_eq : fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ =
              fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ + 1 := by
            unfold fctFint; ring
          rw [hphi_eq]
          calc ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ + 1‖
              ≤ ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ + 1 := by
                simpa only [norm_one] using norm_add_le _ (1 : ℂ)
            _ ≤ C_mid := by linarith
        have hCmid_ll : C_mid ≤ (C_mid / Real.log (Real.log 4)) * Real.log (Real.log (4 + |ζ.im|)) := by
          rw [div_mul_eq_mul_div, le_div_iff₀' hll4_pos]
          exact (mul_comm _ C_mid).trans_le (mul_le_mul_of_nonneg_left hll_le (by positivity))
        calc ‖fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ -
              fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (7 / 16) ζ‖
            ≤ ‖fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ +
              ‖fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (7 / 16) ζ‖ := norm_sub_le _ _
          _ ≤ (C_mid / Real.log (Real.log 4) + Ml) * Real.log (Real.log (4 + |ζ.im|)) := by
              linarith
          _ ≤ M_phi * Real.log (Real.log (4 + |ζ.im|)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hll_nn
      · push Not at hmid
        have hphi_bd := hleft' ζ hζ hmid.le
        calc ‖fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ -
              fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (7 / 16) ζ‖
            ≤ ‖fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ +
              ‖fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (7 / 16) ζ‖ := norm_sub_le _ _
          _ ≤ (Mleft + Ml) * Real.log (Real.log (4 + |ζ.im|)) := by linarith
          _ ≤ M_phi * Real.log (Real.log (4 + |ζ.im|)) :=
              mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hll_nn
  show ‖fctPhiHat h ε c ζ‖ ≤ M * Real.log (Real.log (4 + |ζ.im|))
  unfold fctPhiHat fctPhiHatAt
  have hterm1 : ‖fctPhiWarp K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ /
      fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)‖ ≤
      2 * M_phi * Real.log (Real.log (4 + |ζ.im|)) := by
    rw [div_eq_mul_inv, norm_mul, mul_comm _ ‖_⁻¹‖]
    calc ‖(fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c))⁻¹‖ *
          ‖fctPhiWarp K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖
        ≤ 2 * (M_phi * Real.log (Real.log (4 + |ζ.im|))) :=
          mul_le_mul hNb'.1 hwarp_bd (norm_nonneg _) (by norm_num)
      _ = 2 * M_phi * Real.log (Real.log (4 + |ζ.im|)) := by ring
  have hterm2 : ‖fctBetaC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) * fctQ1 ζ‖ ≤
      (4000 * Kβ / Real.log (Real.log 4)) * Real.log (Real.log (4 + |ζ.im|)) := by
    rw [norm_mul]
    have hconst : 4000 * Kβ ≤ (4000 * Kβ / Real.log (Real.log 4)) * Real.log (Real.log (4 + |ζ.im|)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀' hll4_pos]
      exact (mul_comm _ (4000 * Kβ)).trans_le (mul_le_mul_of_nonneg_left hll_le (by positivity))
    calc ‖fctBetaC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)‖ * ‖fctQ1 ζ‖
        ≤ Kβ * 4000 := mul_le_mul hNb'.2.2 hq1 (norm_nonneg _) hKβ0
      _ = 4000 * Kβ := by ring
      _ ≤ _ := hconst
  calc ‖_ + _‖ ≤ _ := norm_add_le _ _
    _ ≤ 2 * M_phi * Real.log (Real.log (4 + |ζ.im|)) +
          (4000 * Kβ / Real.log (Real.log 4)) * Real.log (Real.log (4 + |ζ.im|)) :=
        add_le_add hterm1 hterm2
    _ = M * Real.log (Real.log (4 + |ζ.im|)) := by simp only [M]; ring

/-- info: 'FormalResearch.SignUncertainty.fctPhiHat_loglog_of_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiHat_loglog_of_left

end FormalResearch.SignUncertainty
