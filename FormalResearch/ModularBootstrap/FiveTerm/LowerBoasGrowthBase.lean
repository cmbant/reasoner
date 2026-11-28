module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasSlitEntropy
public import FormalResearch.ModularBootstrap.FiveTerm.LowerEdgeHankel
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.LangerChart
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuadratureBounds

/-!
# Base analytic, reality, and sup properties of `boasH` (`cts:boas` Step 1)

* `zetaMin`: `ζ_min(c') = (2/(3π)) c'^{6/7}`.
* `boasH`: `M[g]⁻¹ G(b(ζ)) exp((2π/3) c' b(ζ))`.
* `differentiableOn_boasH`, `boasH_conj`, `boasH_ofReal_nonneg`, `boasH_strip_sup`,
  `hankelContinuation_bdy_ne_zero_ae_right`.
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb

noncomputable section

/-- Minimum conformal coordinate `ζ_min(c') = (2/(3π)) c'^{6/7}` on the Boas band (`ctl:freeze`). -/
noncomputable def zetaMin (c' : ℝ) : ℝ := (2 / (3 * π)) * c' ^ (6 / 7 : ℝ)

lemma zetaMin_pos {c' : ℝ} (hc' : 0 < c') : 0 < zetaMin c' := by
  unfold zetaMin; positivity

/-- Normalized holomorphic Boas function `H_c(ζ) = M[g]⁻¹ G(b(ζ)) exp((2π/3) c' b(ζ))`. -/
noncomputable def boasH (c' : ℝ) (g : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  ((virasoroProblem.cardyNorm (c' / 12) g : ℝ) : ℂ)⁻¹ *
    hankelContinuation c' g (bOfZeta c' ζ) *
    Complex.exp (((2 * π / 3 : ℝ) : ℂ) * (c' : ℂ) * bOfZeta c' ζ)

lemma two_log_lt_zetaStrip {c' : ℝ} (hc' : 10000 ≤ c') :
    2 * Real.log c' < (c' / 3) * xiStar := by
  have hc0 : 0 < c' := by linarith
  have hlog : Real.log c' ≤ 4 * c' ^ (1 / 4 : ℝ) := by
    have heq : c' = (c' ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    conv_lhs => rw [heq]
    rw [Real.log_pow, Nat.cast_ofNat]
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc0 (1 / 4 : ℝ))
    linarith
  have h34 : (1000 : ℝ) ≤ c' ^ (3 / 4 : ℝ) := by
    rw [show (1000 : ℝ) = (10000 : ℝ) ^ (3 / 4 : ℝ) by
      rw [show (10000 : ℝ) = 10 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num]
    exact Real.rpow_le_rpow (by norm_num) hc' (by norm_num)
  have hc_prod : c' ^ (1 / 4 : ℝ) * c' ^ (3 / 4 : ℝ) = c' := by
    rw [← Real.rpow_add hc0]; norm_num
  have hcr : 1000 * c' ^ (1 / 4 : ℝ) ≤ c' := by
    calc 1000 * c' ^ (1 / 4 : ℝ) ≤ c' ^ (3 / 4 : ℝ) * c' ^ (1 / 4 : ℝ) := by gcongr
      _ = c' := by rw [mul_comm, hc_prod]
  nlinarith [xiStar_gt_005, hlog, hcr]

lemma mem_zetaStrip_of_log_im {c' : ℝ} (hc' : 10000 ≤ c') {ζ : ℂ}
    (hre : 0 < ζ.re) (him : |ζ.im| ≤ 2 * Real.log c') :
    ζ ∈ zetaStrip c' :=
  ⟨hre, him.trans_lt (two_log_lt_zetaStrip hc')⟩

theorem differentiableOn_boasH {c' : ℝ} (hc' : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    DifferentiableOn ℂ (boasH c' g) (zetaStrip c') := by
  have hc0 : 0 < c' := by linarith
  have hG : DifferentiableOn ℂ (hankelContinuation c' g) {b : ℂ | |b.im| < 1 / 2} :=
    differentiableOn_hankelContinuation hc' hg
  have hb : DifferentiableOn ℂ (bOfZeta c') (zetaStrip c') := differentiableOn_bOfZeta hc0
  have hcomp : DifferentiableOn ℂ (fun ζ => hankelContinuation c' g (bOfZeta c' ζ)) (zetaStrip c') :=
    hG.comp hb (fun ζ hζ => (bOfZeta_mem hc0 hζ).2)
  have hexp : DifferentiableOn ℂ
      (fun ζ => Complex.exp (((2 * π / 3 : ℝ) : ℂ) * (c' : ℂ) * bOfZeta c' ζ)) (zetaStrip c') :=
    (hb.const_mul _).cexp
  exact (hcomp.const_mul _).mul hexp

private lemma continuous_besselI0C_local : Continuous Integration.besselI0C := by
  unfold Integration.besselI0C
  have hc_un : Continuous (Function.uncurry fun z (θ : ℝ) => Complex.exp (z * (Real.cos θ : ℂ))) := by
    change Continuous fun p : ℂ × ℝ => Complex.exp (p.1 * (Real.cos p.2 : ℂ))
    fun_prop
  exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc_un 0 π)

private lemma besselI0C_conj (z : ℂ) :
    Integration.besselI0C (starRingEnd ℂ z) = starRingEnd ℂ (Integration.besselI0C z) := by
  unfold Integration.besselI0C
  rw [map_mul, map_inv₀, Complex.conj_ofReal]
  congr 1
  have hfun : (fun θ : ℝ => Complex.exp (starRingEnd ℂ z * (Real.cos θ : ℂ))) =
      fun θ : ℝ => starRingEnd ℂ (Complex.exp (z * (Real.cos θ : ℂ))) := by
    ext θ; rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  rw [hfun]
  have hcomm := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
    (μ := volume) ((by fun_prop : Continuous fun θ : ℝ => Complex.exp (z * (Real.cos θ : ℂ))).intervalIntegrable 0 π)
  simpa [Complex.conjCLE_apply] using hcomm

lemma hankelContinuation_conj {c' : ℝ} (hc : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    hankelContinuation c' g (starRingEnd ℂ b) = starRingEnd ℂ (hankelContinuation c' g b) := by
  have hc0 : 0 < c' := by linarith
  obtain ⟨hint_K, _⟩ := lemmaB_d_integral hc hg
  let f : ℝ → ℂ := fun t =>
    (g t : ℂ) * Integration.besselI0C (4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ))
  have hf_int : IntegrableOn f (Ioi 0) := by
    have hcont : ContinuousOn f (Ioi 0) := by
      have h1 : ContinuousOn (fun t : ℝ => (g t : ℂ)) (Ioi 0) :=
        Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)
      have harg : Continuous fun t : ℝ => 4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ) := by
        fun_prop
      exact h1.mul ((continuous_besselI0C_local.comp harg).continuousOn)
    refine hint_K.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (besselI0C_strip_le hc0 (mem_Ioi.mp ht).le hb) (abs_nonneg _)
  unfold hankelContinuation
  rw [map_mul, map_mul, map_neg, map_ofNat, Complex.conj_ofReal]
  have hfun : (fun t : ℝ => (g t : ℂ) * Integration.besselI0C (4 * (π : ℂ) * Complex.I * starRingEnd ℂ b *
        (Real.sqrt (c' * t / 3) : ℝ))) =
      fun t : ℝ => starRingEnd ℂ (f t) := by
    ext t; dsimp [f]
    rw [map_mul, Complex.conj_ofReal]; congr 1
    have h1 : 4 * (π : ℂ) * Complex.I * starRingEnd ℂ b * (Real.sqrt (c' * t / 3) : ℝ) =
        -(starRingEnd ℂ (4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ))) := by
      simp [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    rw [h1, besselI0C_neg, besselI0C_conj]
  change -2 * (π : ℂ) * ∫ t in Ioi 0, (g t : ℂ) *
      Integration.besselI0C (4 * (π : ℂ) * Complex.I * starRingEnd ℂ b * (Real.sqrt (c' * t / 3) : ℝ)) =
    -2 * (π : ℂ) * starRingEnd ℂ (∫ t in Ioi 0, f t)
  rw [hfun]
  congr 1
  simpa [Complex.conjCLE_apply] using Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hf_int

/-- Conjugation symmetry `boasH c' g (conj ζ) = conj (boasH c' g ζ)` on `zetaStrip c'`. -/
lemma boasH_conj {c' : ℝ} (hc : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {ζ : ℂ} (hζ : ζ ∈ zetaStrip c') :
    boasH c' g (starRingEnd ℂ ζ) = starRingEnd ℂ (boasH c' g ζ) := by
  have hc0 : 0 < c' := by linarith
  have hbim : |(bOfZeta c' ζ).im| ≤ 1 / 2 := (bOfZeta_mem hc0 hζ).2.le
  unfold boasH
  rw [bOfZeta_conj hc0 hζ, hankelContinuation_conj hc hg hbim]
  rw [map_mul, map_mul, map_inv₀, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_mul,
    Complex.conj_ofReal, Complex.conj_ofReal]

lemma bOfZeta_re_bounds {c' : ℝ} (hc' : 0 < c') {ζ : ℂ} (hζ : ζ ∈ zetaStrip c') (hre : 0 ≤ ζ.re) :
    xiStar < (bOfZeta c' ζ).re ∧
      |(bOfZeta c' ζ).re| + 3 / 2 ≤ 4 * ‖1 + ζ / (c' : ℂ)‖ ∧
      (bOfZeta c' ζ).re + 1 ≤ 4 * ‖1 + ζ / (c' : ℂ)‖ ∧
      (bOfZeta c' ζ).re ≤ 2 + Real.sqrt (3 * (ζ.re / c') + 1 / 2) := by
  set b := bOfZeta c' ζ
  have hb := bOfZeta_mem hc' hζ
  have hre_gt : xiStar < b.re := hb.1
  have him_lt : |b.im| < 1 / 2 := hb.2
  have hsub := (cumulN_bOfZeta_re_sub_le hc' hζ).2
  have hsq : (b.re - xiStar) ^ 2 / 3 ≤ cumulN b.re :=
    (cumulN_ge_sq_div_three (sub_nonneg.mpr hre_gt.le)).trans_eq (by rw [add_sub_cancel])
  have hcr : c' * ((b.re - xiStar) ^ 2 / 3) ≤ ζ.re + c' / 6 := by
    calc c' * ((b.re - xiStar) ^ 2 / 3) ≤ c' * cumulN b.re := by gcongr
      _ ≤ ζ.re + (c' / 3) * |b.im| := by linarith only [hsub]
      _ ≤ ζ.re + (c' / 3) * (1 / 2) := by gcongr
      _ = ζ.re + c' / 6 := by ring
  have hdiff_sq : (b.re - xiStar) ^ 2 ≤ 3 * (ζ.re / c') + 1 / 2 := by
    have hdiv := div_le_div_of_nonneg_right hcr hc'.le
    calc (b.re - xiStar) ^ 2 = c' * ((b.re - xiStar) ^ 2 / 3) / c' * 3 := by field_simp [hc'.ne']
      _ ≤ (ζ.re + c' / 6) / c' * 3 := by gcongr
      _ = 3 * (ζ.re / c') + 1 / 2 := by field_simp [hc'.ne']; ring
  have hxi_lt : xiStar < 1 := xiStar_lt_one
  have hre_pos : 0 < b.re := xiStar_pos.trans hre_gt
  have hrhs_rt : b.re ≤ 2 + Real.sqrt (3 * (ζ.re / c') + 1 / 2) := by
    have h1 : b.re - xiStar ≤ Real.sqrt (3 * (ζ.re / c') + 1 / 2) := by
      rw [← Real.sqrt_sq (sub_nonneg.mpr hre_gt.le)]
      exact Real.sqrt_le_sqrt hdiff_sq
    linarith only [h1, hxi_lt]
  have hnorm_re : 1 + ζ.re / c' ≤ ‖1 + ζ / (c' : ℂ)‖ := by
    have h1 : (1 + ζ / (c' : ℂ)).re = 1 + ζ.re / c' := by simp [Complex.div_ofReal_re]
    have h2 := Complex.re_le_norm (1 + ζ / (c' : ℂ))
    linarith only [h1, h2]
  have hy0 : 0 ≤ ζ.re / c' := div_nonneg hre hc'.le
  have hdx : b.re - xiStar ≤ 1.5 + 4 * (ζ.re / c') := by
    by_contra hlt
    have h1 : 1.5 + 4 * (ζ.re / c') < b.re - xiStar := not_le.mp hlt
    have h2 : (1.5 + 4 * (ζ.re / c')) ^ 2 < (b.re - xiStar) ^ 2 := by nlinarith only [h1, hy0]
    nlinarith only [h2, hdiff_sq, hy0]
  have habs_b : |b.re| + 3 / 2 ≤ 4 * ‖1 + ζ / (c' : ℂ)‖ := by
    rw [abs_of_pos hre_pos]
    linarith only [hdx, hxi_lt, hnorm_re]
  exact ⟨hre_gt, habs_b, by linarith only [habs_b, abs_of_pos hre_pos], hrhs_rt⟩

private lemma boasH_band_gt_T {c' T u C_x C_N : ℝ} (hc0 : 0 < c') (hc1 : 1 ≤ c')
    (hCx_pos : 0 < C_x) (hAC : 4 ≤ virasoroAC c' ^ 2)
    (hr1 : 15 * C_x * c' ^ (-(2 / 3 : ℝ)) ≤ 1)
    (hCN : C_N = (1 / 2 : ℝ) * Real.sqrt (9 * kTip ^ 2 + 16 / 9) * (15 * C_x) * Real.sqrt (15 * C_x) + 1)
    (hzeta_gt : C_N < (1 / 4 : ℝ) * zetaMin c') (hu_lo : (1 / 4 : ℝ) * zetaMin c' ≤ u)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr))
    (hAThr_lt : virasoroAThr < 4)
    (hC_x_def : C_x = 2 * (cStar * 4 + chartParams.C_xi * 16 + 1)) :
    T ≤ c' * ((bOfZeta c' (u : ℂ)).re) ^ 2 / 3 := by
  have hCN_pos : 0 < C_N := by rw [hCN]; positivity
  have hu_pos : 0 < u := lt_of_lt_of_le hCN_pos (hzeta_gt.le.trans hu_lo)
  set x := (bOfZeta c' (u : ℂ)).re
  obtain ⟨_, hb_re, hb_cum⟩ := bOfZeta_ofReal hc0 hu_pos
  by_cases hT_small : T ≤ c' * xiStar ^ 2 / 3
  · have hxi_lt : xiStar ^ 2 < x ^ 2 := by nlinarith only [xiStar_pos, hb_re]
    have h1 : c' * xiStar ^ 2 / 3 < c' * x ^ 2 / 3 := by gcongr
    linarith only [hT_small, h1]
  · have hT_gt : c' * xiStar ^ 2 / 3 < T := not_le.mp hT_small
    have hT_pos : 0 < T := lt_of_le_of_lt (by positivity) hT_gt
    have hΔ_err := virasoro_deltaChart_err hc0
      (show |-virasoroAThr| ≤ virasoroAC c' ^ 2 by
        rw [abs_neg, abs_of_pos virasoroAThr_pos]; exact hAThr_lt.le.trans hAC)
    have hΔ_ub : virasoroDeltaChart c' (-virasoroAThr) ≤
        xiBar * c' + cStar * c' ^ (1 / 3 : ℝ) * virasoroAThr +
          chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * virasoroAThr ^ 2 := by
      have := (abs_le.mp hΔ_err).2; linarith only [this]
    have hcm13_le : c' ^ (-(1 / 3 : ℝ)) ≤ c' ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hT_ub : T ≤ xiBar * c' + (C_x / 2) * c' ^ (1 / 3 : ℝ) := by
      have hCxi_nn := chartParams.hCxi_nn
      have hcstar := cStar_pos
      have h1 : cStar * c' ^ (1 / 3 : ℝ) * virasoroAThr ≤ cStar * 4 * c' ^ (1 / 3 : ℝ) := by
        have hc13_nn : 0 ≤ c' ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
        have hcs := cStar_pos
        calc cStar * c' ^ (1 / 3 : ℝ) * virasoroAThr
            ≤ cStar * c' ^ (1 / 3 : ℝ) * 4 := mul_le_mul_of_nonneg_left hAThr_lt.le (mul_nonneg hcs.le hc13_nn)
          _ = cStar * 4 * c' ^ (1 / 3 : ℝ) := by ring
      have h2 : chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * virasoroAThr ^ 2 ≤
          chartParams.C_xi * 16 * c' ^ (1 / 3 : ℝ) := by
        have ha2 : virasoroAThr ^ 2 ≤ 16 := by nlinarith only [virasoroAThr_pos, hAThr_lt]
        calc chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * virasoroAThr ^ 2
            ≤ chartParams.C_xi * c' ^ (1 / 3 : ℝ) * 16 := by gcongr
          _ = chartParams.C_xi * 16 * c' ^ (1 / 3 : ℝ) := by ring
      have h_simp : C_x / 2 * c' ^ (1 / 3 : ℝ) =
          (cStar * 4 + chartParams.C_xi * 16 + 1) * c' ^ (1 / 3 : ℝ) := by
        rw [hC_x_def]; ring
      have hc13_nn : 0 ≤ c' ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
      linarith only [hT_hi, hΔ_ub, h1, h2, h_simp, hc13_nn]
    set xT := Real.sqrt (3 * T / c')
    have hxT_sq : xT ^ 2 = 3 * T / c' := Real.sq_sqrt (by positivity)
    have hxT_gt : xiStar < xT := by
      rw [← Real.sqrt_sq xiStar_pos.le]
      apply Real.sqrt_lt_sqrt (sq_nonneg _)
      rw [lt_div_iff₀ hc0]; linarith only [hT_gt]
    set r := xT - xiStar
    have hr_pos : 0 < r := sub_pos.mpr hxT_gt
    have hxT_ub : xT ^ 2 - xiStar ^ 2 ≤ (3 / 2) * C_x * c' ^ (-(2 / 3 : ℝ)) := by
      have h1 : 3 * T / c' ≤ 3 * (xiBar * c' + (C_x / 2) * c' ^ (1 / 3 : ℝ)) / c' := by gcongr
      have h2 : 3 * xiBar = xiStar ^ 2 := by unfold xiBar; ring
      have h3 : c' ^ (1 / 3 : ℝ) / c' = c' ^ (-(2 / 3 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hc0]; norm_num
      calc xT ^ 2 - xiStar ^ 2 = 3 * T / c' - 3 * xiBar := by rw [hxT_sq, h2]
        _ ≤ 3 * (xiBar * c' + (C_x / 2) * c' ^ (1 / 3 : ℝ)) / c' - 3 * xiBar := by linarith only [h1]
        _ = (3 / 2) * C_x * (c' ^ (1 / 3 : ℝ) / c') := by field_simp [hc0.ne']; ring
        _ = (3 / 2) * C_x * c' ^ (-(2 / 3 : ℝ)) := by rw [h3]
    have hr_ub : r ≤ 15 * C_x * c' ^ (-(2 / 3 : ℝ)) := by
      have hsum : (0.1 : ℝ) ≤ xT + xiStar := by linarith only [xiStar_gt_005, hxT_gt]
      have hfac : (xT - xiStar) * (xT + xiStar) = xT ^ 2 - xiStar ^ 2 := by ring
      nlinarith only [hfac, hr_pos, hsum, hxT_ub]
    have hcum_ub : c' * cumulN xT ≤ C_N := by
      have hxT_eq : xT = xiStar + r := by dsimp [r]; ring
      let K_rho : ℝ := Real.sqrt (9 * kTip ^ 2 + 16 / 9)
      have hrho_ub : ∀ s ∈ Icc (0 : ℝ) r, rhoU (xiStar + s) ≤ K_rho * Real.sqrt r := by
        intro s hs
        have hsq := (rhoU_sq_bounds hs.1).2
        have hs1 : s ≤ 1 := hs.2.trans (hr_ub.trans hr1)
        have h9 : 9 * kTip ^ 2 * s + (16 / 9) * s ^ 2 ≤ (9 * kTip ^ 2 + 16 / 9) * r := by
          have hs2 : s ^ 2 ≤ s := by nlinarith only [hs.1, hs1]
          have hkr : 0 ≤ 9 * kTip ^ 2 := by positivity
          nlinarith only [hs.1, hs.2, hs2, hkr]
        have hnn : 0 ≤ rhoU (xiStar + s) := rhoU_nonneg _
        have hsq_r : (K_rho * Real.sqrt r) ^ 2 = (9 * kTip ^ 2 + 16 / 9) * r := by
          dsimp [K_rho]; rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hr_pos.le]
        have hKr_nn : 0 ≤ K_rho * Real.sqrt r := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg r)
        nlinarith only [hsq, h9, hsq_r, hnn, hKr_nn]
      have hcum_int : cumulN (xiStar + r) ≤ (1 / 2 : ℝ) * K_rho * r * Real.sqrt r := by
        unfold cumulN
        have hsub : ∫ t in xiStar..(xiStar + r), rhoU t = ∫ s in (0 : ℝ)..r, rhoU (xiStar + s) := by
          simp [add_comm]
        rw [hsub]
        have hint1 : IntervalIntegrable (fun s : ℝ => rhoU (xiStar + s)) volume 0 r := by
          refine (continuousOn_rhoU.comp (continuous_const.add continuous_id).continuousOn ?_).intervalIntegrable_of_Icc hr_pos.le
          intro s hs; change xiStar ≤ xiStar + s; linarith [hs.1]
        have hmono := intervalIntegral.integral_mono_on hr_pos.le hint1 intervalIntegrable_const hrho_ub
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
        linarith only [hmono]
      have hrc : r * Real.sqrt r ≤ 15 * C_x * Real.sqrt (15 * C_x) * c'⁻¹ := by
        have hc13_r : Real.sqrt (c' ^ (-(2 / 3 : ℝ))) = c' ^ (-(1 / 3 : ℝ)) := by
          rw [← Real.sqrt_sq (Real.rpow_nonneg hc0.le (-(1 / 3 : ℝ))), ← Real.rpow_natCast,
            ← Real.rpow_mul hc0.le]
          congr 1; ring
        have hrt_ub : Real.sqrt r ≤ Real.sqrt (15 * C_x) * c' ^ (-(1 / 3 : ℝ)) := by
          calc Real.sqrt r ≤ Real.sqrt (15 * C_x * c' ^ (-(2 / 3 : ℝ))) := Real.sqrt_le_sqrt hr_ub
            _ = Real.sqrt (15 * C_x) * Real.sqrt (c' ^ (-(2 / 3 : ℝ))) := Real.sqrt_mul (by positivity) _
            _ = Real.sqrt (15 * C_x) * c' ^ (-(1 / 3 : ℝ)) := by rw [hc13_r]
        have hpow : c' ^ (-(2 / 3 : ℝ)) * c' ^ (-(1 / 3 : ℝ)) = c'⁻¹ := by
          rw [← Real.rpow_add hc0, ← Real.rpow_neg_one]; norm_num
        calc r * Real.sqrt r ≤ (15 * C_x * c' ^ (-(2 / 3 : ℝ))) * (Real.sqrt (15 * C_x) * c' ^ (-(1 / 3 : ℝ))) :=
              mul_le_mul hr_ub hrt_ub (Real.sqrt_nonneg _) (by positivity)
          _ = 15 * C_x * Real.sqrt (15 * C_x) * (c' ^ (-(2 / 3 : ℝ)) * c' ^ (-(1 / 3 : ℝ))) := by ring
          _ = 15 * C_x * Real.sqrt (15 * C_x) * c'⁻¹ := by rw [hpow]
      have hK_nn : 0 ≤ K_rho := Real.sqrt_nonneg _
      have hprod : K_rho * (r * Real.sqrt r) ≤ K_rho * (15 * C_x * Real.sqrt (15 * C_x) * c'⁻¹) :=
        mul_le_mul_of_nonneg_left hrc hK_nn
      calc c' * cumulN xT = c' * cumulN (xiStar + r) := by rw [hxT_eq]
        _ ≤ c' * ((1 / 2 : ℝ) * K_rho * (r * Real.sqrt r)) := by
            have := mul_le_mul_of_nonneg_left hcum_int hc0.le
            linarith only [this]
        _ ≤ c' * ((1 / 2 : ℝ) * K_rho * (15 * C_x * Real.sqrt (15 * C_x) * c'⁻¹)) := by
            gcongr
        _ = (1 / 2 : ℝ) * K_rho * (15 * C_x) * Real.sqrt (15 * C_x) := by field_simp [hc0.ne']
        _ ≤ C_N := by rw [hCN]; dsimp [K_rho]; linarith only
    have hcum_lt : cumulN xT < cumulN x := by
      have h1 : c' * cumulN xT < c' * cumulN x := by linarith only [hcum_ub, hzeta_gt, hu_lo, hb_cum]
      exact lt_of_not_ge fun hle => by nlinarith only [hle, hc0, h1]
    have hxT_lt_x : xT < x := by
      by_contra hle
      exact absurd (cumulN_strictMonoOn.monotoneOn hb_re.le hxT_gt.le (not_lt.mp hle))
        (not_le.mpr hcum_lt)
    calc T = c' * xT ^ 2 / 3 := by rw [hxT_sq]; field_simp [hc0.ne']
      _ ≤ c' * x ^ 2 / 3 := by
          have : xT ^ 2 ≤ x ^ 2 := by nlinarith only [hxT_gt, xiStar_pos, hxT_lt_x]
          gcongr

theorem boasH_ofReal_nonneg :
    ∃ c₀ : ℝ, 10000 ≤ c₀ ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {T : ℝ} {g : ℝ → ℝ},
      virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
      T ≤ virasoroDeltaChart c' (-virasoroAThr) →
      ∀ {u : ℝ}, (1 / 4 : ℝ) * zetaMin c' ≤ u →
        (boasH c' g (u : ℂ)).im = 0 ∧ 0 ≤ (boasH c' g (u : ℂ)).re := by
  have hAThr_lt : virasoroAThr < 4 := by
    unfold virasoroAThr
    have h1 := airyZero_one
    rw [abs_of_neg (by linarith only [h1.2])]
    linarith only [h1.1]
  have hBV_pos : 0 < virasoroBV := virasoroBV_pos
  let C_x : ℝ := 2 * (cStar * 4 + chartParams.C_xi * 16 + 1)
  have hCx_pos : 0 < C_x := by
    have := cStar_pos; have := chartParams.hCxi_nn; dsimp [C_x]; positivity
  let C_N : ℝ := (1 / 2 : ℝ) * Real.sqrt (9 * kTip ^ 2 + 16 / 9) * (15 * C_x) * Real.sqrt (15 * C_x) + 1
  have hCN_pos : 0 < C_N := by dsimp [C_N]; positivity
  have hev_AC : ∀ᶠ c' : ℝ in atTop, (4 : ℝ) ≤ virasoroAC c' ^ 2 := by
    have h1 : Tendsto (fun c' : ℝ => 2 * virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop (by positivity)
    filter_upwards [eventually_ge_atTop (1 : ℝ), h1.eventually_ge_atTop 4] with c' hc1 h4
    rwa [virasoroAC_sq c' (by linarith)]
  have hev_r : ∀ᶠ c' : ℝ in atTop, 15 * C_x * c' ^ (-(2 / 3 : ℝ)) ≤ 1 := by
    have ht : Tendsto (fun c' : ℝ => 15 * C_x * c' ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul (15 * C_x)
    exact ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hev_zeta : ∀ᶠ c' : ℝ in atTop, C_N < (1 / 4 : ℝ) * zetaMin c' := by
    have ht : Tendsto (fun c' : ℝ => (1 / 4 : ℝ) * zetaMin c') atTop atTop := by
      unfold zetaMin
      exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 6 / 7)).const_mul_atTop
        (by positivity)).const_mul_atTop (by norm_num)
    exact ht.eventually_gt_atTop C_N
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.mp (hev_AC.and (hev_r.and hev_zeta))
  refine ⟨max 10000 c₁, le_max_left _ _, fun {c'} hc' {T g} hwf hT_hi {u} hu_lo => ?_⟩
  have hc0 : 0 < c' := by linarith [(le_max_left _ _).trans hc']
  have hc1 : 1 ≤ c' := by linarith [(le_max_left _ _).trans hc']
  obtain ⟨hAC, hr1, hzeta_gt⟩ := hc₁ c' ((le_max_right _ _).trans hc')
  have hu_pos : 0 < u := lt_of_lt_of_le hCN_pos (hzeta_gt.le.trans hu_lo)
  set x := (bOfZeta c' (u : ℂ)).re
  obtain ⟨hb_im, _, _⟩ := bOfZeta_ofReal hc0 hu_pos
  have hb_eq : bOfZeta c' (u : ℂ) = (x : ℂ) := Complex.ext rfl hb_im
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero (by rw [virasoroProblem_totalShift]; linarith [(le_max_left _ _).trans hc'])
      hwf.1 hwf.2.1
  have hg_nonneg : 0 ≤ g (c' * x ^ 2 / 3) :=
    hwf.2.2.2 _ (boasH_band_gt_T hc0 hc1 hCx_pos hAC hr1 rfl hzeta_gt hu_lo hT_hi hAThr_lt rfl)
  unfold boasH
  rw [hb_eq, hankelContinuation_ofReal hc0 hwf.1 x]
  have hreal_eq : ((virasoroProblem.cardyNorm (c' / 12) g : ℝ) : ℂ)⁻¹ *
        (g (c' * x ^ 2 / 3) : ℂ) * Complex.exp (((2 * π / 3 : ℝ) : ℂ) * (c' : ℂ) * (x : ℂ)) =
      (((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * g (c' * x ^ 2 / 3) *
        Real.exp ((2 * π / 3) * c' * x) : ℝ) : ℂ) := by
    rw [show (((2 * π / 3 : ℝ) : ℂ) * (c' : ℂ) * (x : ℂ)) = (((2 * π / 3 * c' * x : ℝ) : ℂ)) by
        push_cast; ring,
      ← Complex.ofReal_exp]
    push_cast; ring
  rw [hreal_eq, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, mul_nonneg (mul_nonneg (inv_nonneg.mpr hM_pos.le) hg_nonneg) (Real.exp_pos _).le⟩

theorem boasH_strip_sup :
    ∃ c₀ C_e : ℝ, 10000 ≤ c₀ ∧ 0 < C_e ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
      TestClass virasoroProblem (c' / 12) g → (∃ t ≥ 0, g t ≠ 0) →
      ∀ {ζ : ℂ}, ζ ∈ zetaStrip c' →
        ‖boasH c' g ζ‖ ≤ C_e * Real.exp ((2 * π / 3) * c' * (bOfZeta c' ζ).re) := by
  obtain ⟨c_e, C_e, _, hc_e, hC_e, _, h_edge⟩ := edge_hankel_one_virasoro
  refine ⟨c_e, C_e, hc_e, hC_e, fun {c'} hc' {g} hg hnz {ζ} hζ => ?_⟩
  have hc0 : 0 < c' := by linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero (by rw [virasoroProblem_totalShift]; linarith) hg hnz
  have hG_sup := (h_edge hc' hg).2.2 (bOfZeta_mem hc0 hζ).2.le
  unfold boasH
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos,
    Complex.norm_exp]
  have hexp_re : (((2 * π / 3 : ℝ) : ℂ) * (c' : ℂ) * bOfZeta c' ζ).re =
      (2 * π / 3) * c' * (bOfZeta c' ζ).re := by
    simp [Complex.mul_re]
  rw [hexp_re]
  calc (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * ‖hankelContinuation c' g (bOfZeta c' ζ)‖ *
        Real.exp ((2 * π / 3) * c' * (bOfZeta c' ζ).re)
      ≤ (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * (C_e * virasoroProblem.cardyNorm (c' / 12) g) *
          Real.exp ((2 * π / 3) * c' * (bOfZeta c' ζ).re) := by gcongr
    _ = C_e * Real.exp ((2 * π / 3) * c' * (bOfZeta c' ζ).re) := by field_simp [hM_pos.ne']

lemma hankelContinuation_bdy_ne_zero_ae_right {c' : ℝ} (hc1000 : 1000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g) {b : ℂ} (hb_im : |b.im| < 1 / 2)
    (hb_ne : hankelContinuation c' g b ≠ 0) :
    ∀ᵐ σ : ℝ ∂(volume.restrict slitPreimage), hankelContinuation c' g (slitBoundaryMap σ : ℂ) ≠ 0 := by
  have han : AnalyticOnNhd ℂ (hankelContinuation c' g) {w : ℂ | |w.im| < 1 / 2} :=
    analyticOnNhd_hankelContinuation hc1000 hg
  have hpre : IsPreconnected {w : ℂ | |w.im| < 1 / 2} := by
    have hconv : Convex ℝ {w : ℂ | |w.im| < 1 / 2} := by
      intro x hx y hy a b ha hb _
      change |x.im| < 1 / 2 at hx; change |y.im| < 1 / 2 at hy; change |(a • x + b • y).im| < 1 / 2
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      calc |a * x.im + b * y.im| ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
        _ = a * |x.im| + b * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ < a * (1 / 2) + b * (1 / 2) := by
          rcases eq_or_lt_of_le ha with rfl | ha'
          · rw [zero_add] at *; subst ‹b = 1›; simpa using hy
          · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx ha')
              (mul_le_mul_of_nonneg_left hy.le hb)
        _ = 1 / 2 := by linarith
    exact hconv.isPreconnected
  have hz_re_cnt : {r : ℝ | hankelContinuation c' g (r : ℂ) = 0}.Countable := by
    have heq : {r : ℝ | hankelContinuation c' g (r : ℂ) = 0} =
        ⋃ n : ℕ, {r : ℝ | r ∈ Icc (-(n : ℝ)) n ∧ hankelContinuation c' g (r : ℂ) = 0} := by
      ext r; simp only [Set.mem_ofPred_eq, mem_iUnion, mem_Icc]
      refine ⟨fun hr => ?_, fun ⟨_, _, hr⟩ => hr⟩
      obtain ⟨n, hn⟩ := exists_nat_ge |r|
      exact ⟨n, ⟨by linarith [abs_le.mp hn], by linarith [abs_le.mp hn]⟩, hr⟩
    rw [heq]
    have hfin : ∀ n : ℕ, {r : ℝ | r ∈ Icc (-(n : ℝ)) n ∧ hankelContinuation c' g (r : ℂ) = 0}.Finite := by
      intro n; by_contra hinf; rw [Set.not_finite] at hinf
      obtain ⟨r₀, _, hacc⟩ := hinf.exists_accPt_of_subset_isCompact isCompact_Icc (fun _ hr => hr.1)
      have hfreq : ∃ᶠ z in 𝓝[≠] (r₀ : ℂ), hankelContinuation c' g z = 0 := by
        rw [Filter.frequently_iff]; intro U hU
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
        obtain ⟨V, hV, hVU⟩ := hU; obtain ⟨ε, hε_pos, hball⟩ := Metric.mem_nhds_iff.mp hV
        rw [accPt_iff_frequently] at hacc
        obtain ⟨r, ⟨hr_ne, hr_mem⟩, hr_ball⟩ := (hacc.and_eventually (Metric.ball_mem_nhds r₀ hε_pos)).exists
        rw [Real.dist_eq] at hr_ball
        have hr_ball' : (r : ℂ) ∈ Metric.ball (r₀ : ℂ) ε := by
          simpa [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs] using hr_ball
        exact ⟨(r : ℂ), hVU ⟨hball hr_ball', fun he => hr_ne (Complex.ofReal_injective he)⟩, hr_mem.2⟩
      have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre (by simp : (r₀ : ℂ) ∈ _) hfreq
      exact hb_ne (hzero hb_im)
    exact Set.countable_iUnion fun n => (hfin n).countable
  have hσ_cnt : {σ : ℝ | σ ∈ slitPreimage ∧ hankelContinuation c' g (slitBoundaryMap σ : ℂ) = 0}.Countable := by
    have hsub : {σ : ℝ | σ ∈ slitPreimage ∧ hankelContinuation c' g (slitBoundaryMap σ : ℂ) = 0} ⊆
        ⋃ r ∈ {r : ℝ | hankelContinuation c' g (r : ℂ) = 0}, {σ : ℝ | σ ∈ slitPreimage ∧ slitBoundaryMap σ = r} :=
      fun σ ⟨hσ, h0⟩ => mem_iUnion₂.mpr ⟨slitBoundaryMap σ, h0, hσ, rfl⟩
    exact (hz_re_cnt.biUnion fun r _ => (slitBoundaryMap_preimage_finite r).countable).mono hsub
  unfold slitPreimage
  rw [ae_restrict_iff' (measurableSet_Ioo.union measurableSet_Ioi)]
  filter_upwards [compl_mem_ae_iff.mpr (hσ_cnt.measure_zero volume)] with σ hσ hmem h0
  exact hσ ⟨hmem, h0⟩

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.differentiableOn_boasH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.differentiableOn_boasH

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.boasH_ofReal_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.boasH_ofReal_nonneg

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.boasH_strip_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.boasH_strip_sup
