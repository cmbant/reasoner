module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerRoscOrth

/-!
# Virasoro Coordinate Mass & Taper Expansion (`cts:rosc-uncond` (3), mass/taper part)

* `virasoro_rosc_mass_expansion`: positive-lobe decay `O(c^{-4/3})`, `∫_{-R}^R Re f + g_vac/(2π M)`
  vs `∫_{Δ(φ(-R))}^∞ g V / M`, and the transferred taper integral `∫_0^R w_R(v) f(-v) dv`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set intervalIntegral Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.FixedWeightBand
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.FineOrderSigned

noncomputable section

private lemma log_mul_rpow_neg_le {c' α : ℝ} (hc' : 1 ≤ c') (hα : 0 < α) :
    c' ^ (-α) * Real.log c' ≤ (2 / α) * c' ^ (-(α / 2)) := by
  have hc'_pos : 0 < c' := by linarith
  have hlog : (α / 2) * Real.log c' ≤ c' ^ (α / 2) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc'_pos (α / 2))
    rw [Real.log_rpow hc'_pos] at h
    linarith
  have hlog_bd : Real.log c' ≤ (2 / α) * c' ^ (α / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / α)
    have h1 : (2 / α) * ((α / 2) * Real.log c') = Real.log c' := by
      field_simp [hα.ne']
    linarith [hmul]
  calc c' ^ (-α) * Real.log c'
      ≤ c' ^ (-α) * ((2 / α) * c' ^ (α / 2)) :=
        mul_le_mul_of_nonneg_left hlog_bd (Real.rpow_nonneg hc'_pos.le _)
    _ = (2 / α) * (c' ^ (-α) * c' ^ (α / 2)) := by ring
    _ = (2 / α) * c' ^ (-(α / 2)) := by
        rw [← Real.rpow_add hc'_pos]; ring_nf
private lemma virasoro_strip_uhat_le_one {c ut : ℝ} (hc10000 : 10000 ≤ c)
    (hc_min : 16 ≤ lowerRmin virasoroC1 c)
    (hc_strip : (2 * betaTip * chartParams.M_ψ + 2) ^ 3 + 1 ≤ c)
    (hut : |ut| ≤ 1 / 2) :
    |virasoroUhat c ut| ≤ 1 := by
  have hc0 : 0 < c := by linarith only [hc10000]
  have hβ := betaTip_pos
  have hc1_pos := virasoroC1_pos
  have hε0 : 0 ≤ c ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le (-2)
  have hε1 : c ^ (-2 : ℝ) ≤ 1 / 4 := by
    rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (c ^ 2)⁻¹ ≤ (10000 ^ 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith only [hc10000])
      _ ≤ 1 / 4 := by norm_num
  have h1_r0 : virasoroC1 ≤ √(chartParams.r_ψ * betaTip / 16) := (min_le_right _ _).trans (min_le_left _ _)
  have hnn_r0 : 0 ≤ chartParams.r_ψ * betaTip / 16 := by
    have := chartParams.hrψ_pos; positivity
  have hsq_r0 : virasoroC1 ^ 2 ≤ chartParams.r_ψ * betaTip / 16 :=
    (pow_le_pow_left₀ hc1_pos.le h1_r0 2).trans_eq (Real.sq_sqrt hnn_r0)
  have h516 : 5 * virasoroC1 ^ 2 * betaTip⁻¹ ≤ chartParams.r_ψ := by
    calc 5 * virasoroC1 ^ 2 * betaTip⁻¹
        ≤ 5 * (chartParams.r_ψ * betaTip / 16) * betaTip⁻¹ := by gcongr
      _ = 5 / 16 * chartParams.r_ψ := by field_simp [hβ.ne']
      _ ≤ chartParams.r_ψ := by linarith only [chartParams.hrψ_pos]
  have hmu_le : |ut| ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by
    unfold lowerRmin at hc_min; linarith only [hut, hc_min]
  have h_mu_le : virasoroMu c * |ut| ≤ chartParams.r_ψ := by
    unfold virasoroMu
    have h1 : betaTip⁻¹ * c ^ (-(2 / 3 : ℝ)) * |ut| ≤
        betaTip⁻¹ * c ^ (-(2 / 3 : ℝ)) * (5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) := by gcongr
    have h2 : betaTip⁻¹ * c ^ (-(2 / 3 : ℝ)) * (5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) =
        5 * virasoroC1 ^ 2 * betaTip⁻¹ := by
      calc betaTip⁻¹ * c ^ (-(2 / 3 : ℝ)) * (5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))
          = 5 * virasoroC1 ^ 2 * betaTip⁻¹ * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) := by ring
        _ = 5 * virasoroC1 ^ 2 * betaTip⁻¹ := by rw [← Real.rpow_add hc0]; norm_num
    exact (h1.trans_eq h2).trans h516
  have hψ_cb : ((virasoroMu c * ut : ℝ) : ℂ) ∈ closedBall (0 : ℂ) chartParams.r_ψ := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by unfold virasoroMu; exact mul_pos (inv_pos.mpr hβ) (Real.rpow_pos_of_pos hc0 _))]
    exact h_mu_le
  have hψ_bd := ((chartParams.hψ_spec (c ^ (-2 : ℝ)) hε0 hε1).2.2.1 _ hψ_cb).1
  have hre_bd : |(virasoroPsiEps (c ^ (-2 : ℝ)) ((virasoroMu c * ut : ℝ) : ℂ)).re| ≤ chartParams.M_ψ :=
    (Complex.abs_re_le_norm _).trans hψ_bd
  have hlam_bd : virasoroLam c * chartParams.M_ψ ≤ 1 / 2 := by
    have hmψ := chartParams.hMψ_nn
    have hc13_pos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have hbase : ((2 * betaTip * chartParams.M_ψ + 2 : ℝ) ^ (3 : ℕ)) ≤ c := by linarith only [hc_strip]
    have hpw := Real.rpow_le_rpow (by positivity) hbase (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at hpw
    norm_num at hpw
    have hbm : 2 * betaTip * chartParams.M_ψ ≤ c ^ (1 / 3 : ℝ) := by linarith only [hpw]
    unfold virasoroLam
    rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv]
    calc betaTip * (c ^ (1 / 3 : ℝ))⁻¹ * chartParams.M_ψ
        = (2 * betaTip * chartParams.M_ψ) / (2 * c ^ (1 / 3 : ℝ)) := by ring
      _ ≤ c ^ (1 / 3 : ℝ) / (2 * c ^ (1 / 3 : ℝ)) := by gcongr
      _ = 1 / 2 := by field_simp [hc13_pos.ne']
  have hlam_nn : 0 ≤ virasoroLam c := by unfold virasoroLam; positivity
  unfold virasoroUhat fjUhat virasoroPsiChart
  calc |ut + virasoroLam c * (virasoroPsiEps (c ^ (-2 : ℝ)) ((virasoroMu c * ut : ℝ) : ℂ)).re|
      ≤ |ut| + |virasoroLam c * (virasoroPsiEps (c ^ (-2 : ℝ)) ((virasoroMu c * ut : ℝ) : ℂ)).re| :=
        abs_add_le _ _
    _ = |ut| + virasoroLam c * |(virasoroPsiEps (c ^ (-2 : ℝ)) ((virasoroMu c * ut : ℝ) : ℂ)).re| := by
        rw [abs_mul, abs_of_nonneg hlam_nn]
    _ ≤ 1 / 2 + virasoroLam c * chartParams.M_ψ := by linarith only [hut, mul_le_mul_of_nonneg_left hre_bd hlam_nn]
    _ ≤ 1 / 2 + 1 / 2 := by linarith only [hlam_bd]
    _ = 1 := by norm_num

private lemma virasoro_strip_wr_le {c R ut : ℝ} (hc10000 : 10000 ≤ c)
    (hc_min : 16 ≤ lowerRmin virasoroC1 c) (hR_min : lowerRmin virasoroC1 c ≤ R)
    (hc_strip : (2 * betaTip * chartParams.M_ψ + 2) ^ 3 + 1 ≤ c)
    (hut : |ut| ≤ 1 / 2) :
    |lowerWR R (-virasoroUhat c ut)| ≤ (2 * virasoroC1 ^ (-24 : ℝ)) * c ^ (-(4 / 3 : ℝ)) := by
  have hc0 : 0 < c := by linarith only [hc10000]
  have hc1 : 1 ≤ c := by linarith only [hc10000]
  have hc1_pos := virasoroC1_pos
  have hR_ge16 : 16 ≤ R := hc_min.trans hR_min
  have hR0 : 0 < R := by linarith only [hR_ge16]
  have hu1 := virasoro_strip_uhat_le_one hc10000 hc_min hc_strip hut
  have h_pow : (virasoroUhat c ut / R) ^ 12 ≤ R ^ (-12 : ℝ) := by
    have h1 : |virasoroUhat c ut / R| ≤ 1 / R := by
      rw [abs_div, abs_of_pos hR0]; exact div_le_div_of_nonneg_right hu1 hR0.le
    have h12 := pow_le_pow_left₀ (abs_nonneg _) h1 12
    rw [(by decide : Even 12).pow_abs, one_div, inv_pow, ← Real.rpow_natCast R 12,
      ← Real.rpow_neg hR0.le] at h12
    exact h12
  have halg : |1 - (1 - (virasoroUhat c ut / R) ^ 12) ^ 2| ≤ 2 * (virasoroUhat c ut / R) ^ 12 := by
    have heq : 1 - (1 - (virasoroUhat c ut / R) ^ 12) ^ 2 =
        (virasoroUhat c ut / R) ^ 12 * (2 - (virasoroUhat c ut / R) ^ 12) := by ring
    have hp0 : 0 ≤ (virasoroUhat c ut / R) ^ 12 := (by decide : Even 12).pow_nonneg _
    have hp1 : (virasoroUhat c ut / R) ^ 12 ≤ 1 := h_pow.trans
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [hR_ge16]) (by norm_num))
    rw [heq, abs_of_nonneg (mul_nonneg hp0 (by linarith only [hp1]))]
    nlinarith only [hp0]
  have hrmin_pos : 0 < lowerRmin virasoroC1 c := by unfold lowerRmin; positivity
  have hR12_le : R ^ (-12 : ℝ) ≤ virasoroC1 ^ (-24 : ℝ) * c ^ (-(4 / 3 : ℝ)) := by
    have h1 := Real.rpow_le_rpow_of_nonpos hrmin_pos hR_min (by norm_num : (-12 : ℝ) ≤ 0)
    have h2 : (lowerRmin virasoroC1 c) ^ (-12 : ℝ) = virasoroC1 ^ (-24 : ℝ) * c ^ (-8 : ℝ) := by
      unfold lowerRmin
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast virasoroC1 2, ← Real.rpow_mul hc1_pos.le,
        ← Real.rpow_mul hc0.le]
      norm_num
    have hc8_le : c ^ (-8 : ℝ) ≤ c ^ (-(4 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc R ^ (-12 : ℝ) ≤ virasoroC1 ^ (-24 : ℝ) * c ^ (-8 : ℝ) := h1.trans_eq h2
      _ ≤ virasoroC1 ^ (-24 : ℝ) * c ^ (-(4 / 3 : ℝ)) := by gcongr
  unfold lowerWR lowerW6
  have hneg : (-(-virasoroUhat c ut) / R) ^ 12 = (virasoroUhat c ut / R) ^ 12 := by
    rw [neg_neg]
  rw [hneg]
  calc |1 - (1 - (virasoroUhat c ut / R) ^ 12) ^ 2|
      ≤ 2 * (virasoroUhat c ut / R) ^ 12 := halg
    _ ≤ 2 * R ^ (-12 : ℝ) := by gcongr
    _ ≤ 2 * (virasoroC1 ^ (-24 : ℝ) * c ^ (-(4 / 3 : ℝ))) := by gcongr
    _ = (2 * virasoroC1 ^ (-24 : ℝ)) * c ^ (-(4 / 3 : ℝ)) := by ring

private lemma virasoro_strip_interval_le {c R a : ℝ} {g : ℝ → ℝ}
    (hc10000 : 10000 ≤ c) (hc_min : 16 ≤ lowerRmin virasoroC1 c)
    (hR_min : lowerRmin virasoroC1 c ≤ R)
    (hc_strip : (2 * betaTip * chartParams.M_ψ + 2) ^ 3 + 1 ≤ c)
    (hA2_ge : 1 / 2 ≤ virasoroAC c ^ 2) (ha_abs : |a| ≤ 1 / 2)
    (h_win_cont : ContinuousOn (fun ut : ℝ => lowerWR R (-virasoroUhat c ut))
      (Icc (-(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) (5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))))
    (hψ_re_cont : ContinuousOn (fun ut : ℝ => (psiTilde virasoroProblem c g (ut : ℂ)).re)
      (Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2)))
    (h_int_A2 : IntervalIntegrable (fun ut : ℝ => ‖psiTilde virasoroProblem c g (ut : ℂ)‖)
      volume (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2))
    (hQ3_L1 : ∫ ut in (-(virasoroAC c ^ 2))..(virasoroAC c ^ 2),
      ‖psiTilde virasoroProblem c g (ut : ℂ)‖ ≤ 1) :
    |∫ ut in (0 : ℝ)..a,
        lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re| ≤
      (2 * virasoroC1 ^ (-24 : ℝ)) * c ^ (-(4 / 3 : ℝ)) := by
  have hc0 : 0 < c := by linarith only [hc10000]
  have hc1p := virasoroC1_pos
  have hA2_pos : 0 < virasoroAC c ^ 2 := by linarith only [hA2_ge]
  let C' : ℝ := (2 * virasoroC1 ^ (-24 : ℝ)) * c ^ (-(4 / 3 : ℝ))
  have hC'_nn : 0 ≤ C' := by dsimp [C']; positivity
  have h_half : ∀ ut ∈ Icc (min 0 a) (max 0 a), |ut| ≤ 1 / 2 := fun ut hut =>
    abs_le.mpr ⟨(le_min (by norm_num) (abs_le.mp ha_abs).1).trans hut.1,
      hut.2.trans (max_le (by norm_num) (abs_le.mp ha_abs).2)⟩
  have hloA2 : -(virasoroAC c ^ 2) ≤ min 0 a :=
    le_min (by linarith only [hA2_pos]) (by linarith only [(abs_le.mp ha_abs).1, hA2_ge])
  have hhiA2 : max 0 a ≤ virasoroAC c ^ 2 :=
    max_le hA2_pos.le ((abs_le.mp ha_abs).2.trans hA2_ge)
  have h_norm_int : IntervalIntegrable (fun ut : ℝ => ‖psiTilde virasoroProblem c g (ut : ℂ)‖)
      volume (min 0 a) (max 0 a) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le min_le_max]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show -(virasoroAC c ^ 2) ≤ virasoroAC c ^ 2 by linarith only [hA2_pos])).mp h_int_A2).mono_set
      (Ioc_subset_Ioc hloA2 hhiA2)
  have h_norm_sub : ∫ ut in (min 0 a)..(max 0 a), ‖psiTilde virasoroProblem c g (ut : ℂ)‖ ≤ 1 := by
    rw [intervalIntegral.integral_of_le min_le_max]
    have h_le : ∫ ut in Ioc (min 0 a) (max 0 a), ‖psiTilde virasoroProblem c g (ut : ℂ)‖ ≤
        ∫ ut in Ioc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2),
          ‖psiTilde virasoroProblem c g (ut : ℂ)‖ :=
      setIntegral_mono_set
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le
          (show -(virasoroAC c ^ 2) ≤ virasoroAC c ^ 2 by linarith only [hA2_pos])).mp h_int_A2)
        (ae_of_all _ fun _ => norm_nonneg _) (Ioc_subset_Ioc hloA2 hhiA2).eventuallySubset
    rw [← intervalIntegral.integral_of_le
      (show -(virasoroAC c ^ 2) ≤ virasoroAC c ^ 2 by linarith only [hA2_pos])] at h_le
    exact h_le.trans hQ3_L1
  have h12 : (1 / 2 : ℝ) ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by
    unfold lowerRmin at hc_min; linarith only [hc_min]
  have hi_lhs : IntervalIntegrable
      (fun ut : ℝ => |lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re|)
      volume (min 0 a) (max 0 a) :=
    (continuous_abs.comp_continuousOn ((h_win_cont.mono fun ut hut =>
      abs_le.mp ((h_half ut hut).trans h12)).mul
      (hψ_re_cont.mono fun ut hut =>
        abs_le.mp ((h_half ut hut).trans hA2_ge)))).intervalIntegrable_of_Icc min_le_max
  have hi_rhs : IntervalIntegrable (fun ut : ℝ => C' * ‖psiTilde virasoroProblem c g (ut : ℂ)‖)
      volume (min 0 a) (max 0 a) :=
    h_norm_int.const_mul C'
  have h_mono : ∫ ut in (min 0 a)..(max 0 a),
        |lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re| ≤
      ∫ ut in (min 0 a)..(max 0 a), C' * ‖psiTilde virasoroProblem c g (ut : ℂ)‖ := by
    refine intervalIntegral.integral_mono_on min_le_max hi_lhs hi_rhs fun ut hut => ?_
    rw [abs_mul]
    exact mul_le_mul (virasoro_strip_wr_le hc10000 hc_min hR_min hc_strip (h_half ut hut))
      (Complex.abs_re_le_norm _) (abs_nonneg _) hC'_nn
  have h_int_re : |∫ ut in (min 0 a)..(max 0 a),
      lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re| ≤ C' :=
    calc |∫ ut in (min 0 a)..(max 0 a),
          lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re|
        ≤ ∫ ut in (min 0 a)..(max 0 a),
            |lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re| :=
          intervalIntegral.abs_integral_le_integral_abs min_le_max
      _ ≤ ∫ ut in (min 0 a)..(max 0 a), C' * ‖psiTilde virasoroProblem c g (ut : ℂ)‖ := h_mono
      _ = C' * ∫ ut in (min 0 a)..(max 0 a), ‖psiTilde virasoroProblem c g (ut : ℂ)‖ :=
          intervalIntegral.integral_const_mul C' _
      _ ≤ C' * 1 := mul_le_mul_of_nonneg_left h_norm_sub hC'_nn
      _ = C' := mul_one C'
  rcases le_total 0 a with h0p | hp0
  · simpa only [min_eq_left h0p, max_eq_right h0p] using h_int_re
  · rw [intervalIntegral.integral_symm a 0, abs_neg]
    simpa only [min_eq_right hp0, max_eq_left hp0] using h_int_re


private noncomputable def virasoroPhiR (c x : ℝ) : ℝ := (virasoroPhi c (x : ℂ)).re

private lemma mass_exp_part1 {c T R R' Cφ : ℝ} {g : ℝ → ℝ}
    (hc0 : 0 < c) (hc1 : 1 ≤ c) (hc10000 : 10000 ≤ c) (hc_Q : virasoroCQEnv ≤ c)
    (hCφ : 0 ≤ Cφ)
    (hwf : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    (hR : LowerRadiusRange virasoroC1 c R)
    (hR0 : 0 < R) (hR_ge16 : 16 ≤ R) (hR_le_rmax : R ≤ lowerRmax virasoroC1 c)
    (hRR' : R < R')
    (hf_diff : DifferentiableOn ℂ (lowerF virasoroProblem virasoroPhi c g) (ball 0 R'))
    (hf_re_cont : ContinuousOn (fun x : ℝ => (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re) (Icc (-R) R))
    (hL1 : ∫ x in (-R)..R, ‖lowerF virasoroProblem virasoroPhi c g (x : ℂ)‖ ≤ 1)
    (hφ_im : ∀ x : ℝ, |x| ≤ lowerRmax virasoroC1 c → (virasoroPhi c (x : ℂ)).im = 0)
    (hφ_real : ∀ x : ℝ, |x| ≤ R →
      |(virasoroPhi c (x : ℂ)).re - x| ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧
        |(virasoroPhi c (x : ℂ)).re| ≤ virasoroAC c ^ 2 * (3 / 4) ∧
        1 / 2 ≤ (deriv (virasoroPhi c) (x : ℂ)).re ∧
        ‖deriv (virasoroPhi c) (x : ℂ) - 1‖ ≤ Cφ * c ^ (-1 : ℝ) ∧
        (deriv (virasoroPhi c) (x : ℂ)).im = 0)
    (hphiR_diff : ∀ x ∈ Icc (-R) R, HasDerivAt (virasoroPhiR c) (deriv (virasoroPhi c) (x : ℂ)).re x)
    (hphiR_deriv_cont : ContinuousOn (fun x : ℝ => (deriv (virasoroPhi c) (x : ℂ)).re) (Icc (-R) R))
    (hphiR_strictMono : StrictMonoOn (virasoroPhiR c) (Icc (-R) R))
    (hphiR_A2 : ∀ x ∈ Icc (-R) R, |virasoroPhiR c x| ≤ virasoroAC c ^ 2)
    (hRmin_ge : 16 + 2 * (Cφ + 2) + 2 ≤ lowerRmin virasoroC1 c)
    (hCφ_c13 : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2)
    (hsig_nn : 0 ≤ virasoroSigma c) (hsig_le : virasoroSigma c ≤ 1 / 2)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c / 12) g)
    (hexp_tail_le : ∀ {A : ℝ}, (1 / 2 : ℝ) * (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ) ≤ A →
      (6 / 5 : ℝ) * virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * A) ≤ c ^ (-(4 / 3 : ℝ))) :
    |∫ v in (0 : ℝ)..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re| ≤
      (2 * virasoroC1 ^ (-18 : ℝ) + 1) * c ^ (-(4 / 3 : ℝ)) := by
  have hc1_pos := virasoroC1_pos
  let u₁ : ℝ := R ^ (1 / 4 : ℝ)
  have hu1_ge2 : 2 ≤ u₁ := by
    have h24 : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by norm_num
    rw [h24]; exact Real.rpow_le_rpow (by norm_num) hR_ge16 (by norm_num)
  have hu1_pos : 0 < u₁ := by linarith only [hu1_ge2]
  have hu1_le_R : u₁ ≤ R := by
    dsimp [u₁]
    calc R ^ (1 / 4 : ℝ) ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hR_ge16]) (by norm_num)
      _ = R := Real.rpow_one R
  have hWR_cont : ContinuousOn (lowerWR R) (Icc 0 R) := by
    unfold lowerWR lowerW6; fun_prop
  have hWR_bd : ∀ v ∈ Icc 0 R, 0 ≤ lowerWR R v ∧ lowerWR R v ≤ 1 ∧ lowerWR R v ≤ 2 * (v / R) ^ 12 := by
    intro v hv
    have hvR0 : 0 ≤ v / R := div_nonneg hv.1 hR0.le
    have hvR1 : v / R ≤ 1 := (div_le_one hR0).mpr hv.2
    have hp12 : 0 ≤ (v / R) ^ 12 := pow_nonneg hvR0 12
    have hp12_le : (v / R) ^ 12 ≤ 1 := pow_le_one₀ hvR0 hvR1
    unfold lowerWR lowerW6
    have hdiv_neg : ((-v) / R) ^ 12 = (v / R) ^ 12 := by
      rw [neg_div, (by decide : Even 12).neg_pow]
    rw [hdiv_neg]
    have halg : 1 - (1 - (v / R) ^ 12) ^ 2 = (v / R) ^ 12 * (2 - (v / R) ^ 12) := by ring
    rw [halg]
    refine ⟨mul_nonneg hp12 (by linarith only [hp12_le]), ?_, ?_⟩
    · have : 1 - (v / R) ^ 12 * (2 - (v / R) ^ 12) = (1 - (v / R) ^ 12) ^ 2 := by ring
      linarith only [sq_nonneg (1 - (v / R) ^ 12), this]
    · nlinarith only [hp12]
  have hi1 : IntervalIntegrable (fun v : ℝ =>
      lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re) volume 0 u₁ :=
    ((hWR_cont.mono (Icc_subset_Icc_right hu1_le_R)).mul
      (hf_re_cont.mono (Icc_subset_Icc (by linarith only [hR0]) hu1_le_R))).intervalIntegrable_of_Icc hu1_pos.le
  have hi2 : IntervalIntegrable (fun v : ℝ =>
      lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re) volume u₁ R :=
    ((hWR_cont.mono (Icc_subset_Icc_left hu1_pos.le)).mul
      (hf_re_cont.mono (Icc_subset_Icc (by linarith only [hR0, hu1_pos]) le_rfl))).intervalIntegrable_of_Icc hu1_le_R
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hnear : |∫ v in (0 : ℝ)..u₁, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re| ≤
      2 * virasoroC1 ^ (-18 : ℝ) * c ^ (-(4 / 3 : ℝ)) := by
    have hf_abs_int : IntervalIntegrable (fun v : ℝ =>
        ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖) volume 0 u₁ :=
      (continuous_norm.comp_continuousOn (hf_diff.continuousOn.comp Complex.continuous_ofReal.continuousOn
        fun v hv => mem_ball_zero_iff.mpr (by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact (abs_le.mpr ⟨by linarith only [hv.1, hR0], hv.2.trans hu1_le_R⟩).trans_lt hRR'))).intervalIntegrable_of_Icc hu1_pos.le
    have hf_abs_R : IntervalIntegrable (fun v : ℝ =>
        ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖) volume (-R) R :=
      (continuous_norm.comp_continuousOn (hf_diff.continuousOn.comp Complex.continuous_ofReal.continuousOn
        fun v hv => mem_ball_zero_iff.mpr (by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact (abs_le.mpr hv).trans_lt hRR'))).intervalIntegrable_of_Icc (by linarith only [hR0])
    have h1 : |∫ v in (0 : ℝ)..u₁, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re| ≤
        ∫ v in (0 : ℝ)..u₁, 2 * (u₁ / R) ^ 12 * ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖ := by
      refine (intervalIntegral.abs_integral_le_integral_abs hu1_pos.le).trans ?_
      refine intervalIntegral.integral_mono_on hu1_pos.le hi1.abs (hf_abs_int.const_mul _) fun v hv => ?_
      rw [abs_mul, abs_of_nonneg (hWR_bd v ⟨hv.1, hv.2.trans hu1_le_R⟩).1]
      have hwr_le := (hWR_bd v ⟨hv.1, hv.2.trans hu1_le_R⟩).2.2
      have hpow_le : (v / R) ^ 12 ≤ (u₁ / R) ^ 12 :=
        pow_le_pow_left₀ (div_nonneg hv.1 hR0.le) (div_le_div_of_nonneg_right hv.2 hR0.le) 12
      have hre_le : |(lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re| ≤
          ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖ := Complex.abs_re_le_norm _
      exact mul_le_mul (hwr_le.trans (by gcongr)) hre_le (abs_nonneg _) (by positivity)
    rw [intervalIntegral.integral_const_mul] at h1
    have hsub_R : ∫ v in (0 : ℝ)..u₁, ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖ ≤ 1 := by
      rw [intervalIntegral.integral_of_le hu1_pos.le]
      have hR_norm : ∫ v in Ioc (-R) R, ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖ ≤ 1 := by
        rw [← intervalIntegral.integral_of_le (by linarith only [hR0])]; exact hL1
      refine (setIntegral_mono_set
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith only [hR0])).mp hf_abs_R)
        (ae_of_all _ fun _ => norm_nonneg _)
        (Ioc_subset_Ioc (by linarith only [hR0]) hu1_le_R).eventuallySubset).trans hR_norm
    have huR12 : 2 * (u₁ / R) ^ 12 ≤ 2 * virasoroC1 ^ (-18 : ℝ) * c ^ (-(4 / 3 : ℝ)) := by
      have hpow_u1R : u₁ / R = R ^ (-(3 / 4 : ℝ)) := by
        dsimp [u₁]
        conv_lhs => rhs; rw [← Real.rpow_one R]
        rw [← Real.rpow_sub hR0]
        norm_num
      have hpow12 : (R ^ (-(3 / 4 : ℝ))) ^ 12 = R ^ (-9 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]; norm_num
      have hrmin_pos : 0 < lowerRmin virasoroC1 c := by unfold lowerRmin; positivity
      have hR9 : R ^ (-9 : ℝ) ≤ virasoroC1 ^ (-18 : ℝ) * c ^ (-6 : ℝ) := by
        have h1 := Real.rpow_le_rpow_of_nonpos hrmin_pos hR.1 (by norm_num : (-9 : ℝ) ≤ 0)
        refine h1.trans_eq ?_
        unfold lowerRmin
        rw [Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_natCast virasoroC1 2, ← Real.rpow_mul hc1_pos.le,
          ← Real.rpow_mul hc0.le]
        norm_num
      have hc6_le : c ^ (-6 : ℝ) ≤ c ^ (-(4 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      calc 2 * (u₁ / R) ^ 12 = 2 * R ^ (-9 : ℝ) := by rw [hpow_u1R, hpow12]
        _ ≤ 2 * (virasoroC1 ^ (-18 : ℝ) * c ^ (-6 : ℝ)) := by gcongr
        _ ≤ 2 * (virasoroC1 ^ (-18 : ℝ) * c ^ (-(4 / 3 : ℝ))) := by gcongr
        _ = 2 * virasoroC1 ^ (-18 : ℝ) * c ^ (-(4 / 3 : ℝ)) := by ring
    calc |∫ v in (0 : ℝ)..u₁, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re|
        ≤ 2 * (u₁ / R) ^ 12 * ∫ v in (0 : ℝ)..u₁, ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖ := h1
      _ ≤ 2 * (u₁ / R) ^ 12 * 1 := by gcongr
      _ = 2 * (u₁ / R) ^ 12 := mul_one _
      _ ≤ 2 * virasoroC1 ^ (-18 : ℝ) * c ^ (-(4 / 3 : ℝ)) := huR12
  have hfar : |∫ v in u₁..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re| ≤
      c ^ (-(4 / 3 : ℝ)) := by
    have hf_abs_int : IntervalIntegrable (fun v : ℝ =>
        ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖) volume u₁ R :=
      (continuous_norm.comp_continuousOn (hf_diff.continuousOn.comp Complex.continuous_ofReal.continuousOn
        fun v hv => mem_ball_zero_iff.mpr (by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact (abs_le.mpr ⟨by linarith only [hv.1, hu1_pos, hR0], hv.2⟩).trans_lt hRR'))).intervalIntegrable_of_Icc hu1_le_R
    have h1 : |∫ v in u₁..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re| ≤
        ∫ v in u₁..R, ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖ := by
      refine (intervalIntegral.abs_integral_le_integral_abs hu1_le_R).trans ?_
      refine intervalIntegral.integral_mono_on hu1_le_R hi2.abs hf_abs_int fun v hv => ?_
      rw [abs_mul, abs_of_nonneg (hWR_bd v ⟨hu1_pos.le.trans hv.1, hv.2⟩).1]
      simpa only [one_mul] using mul_le_mul (hWR_bd v ⟨hu1_pos.le.trans hv.1, hv.2⟩).2.1
        (Complex.abs_re_le_norm _) (abs_nonneg _) zero_le_one
    have hcov_norm : ∫ v in u₁..R, ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖ =
        ∫ ut in ((virasoroPhiR c) u₁)..((virasoroPhiR c) R), ‖virasoroPsiTilde c g (ut : ℂ)‖ := by
      have heq : psiTilde virasoroProblem c g = virasoroPsiTilde c g :=
        funext (psiTilde_virasoroProblem hc0.le g)
      have hfn : EqOn (fun v : ℝ => ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖)
          (fun v : ℝ => ‖virasoroPsiTilde c g (((virasoroPhiR c) v : ℝ) : ℂ)‖ * (deriv (virasoroPhi c) (v : ℂ)).re)
          (uIcc u₁ R) := by
        intro v hv
        rw [uIcc_of_le hu1_le_R] at hv
        have hv_abs : |v| ≤ R := abs_le.mpr ⟨by linarith only [hv.1, hu1_pos, hR0], hv.2⟩
        have himφ : (virasoroPhi c (v : ℂ)).im = 0 := hφ_im v (hv_abs.trans hR_le_rmax)
        have hd_re := (hφ_real v hv_abs).2.2.1
        have hd_im := (hφ_real v hv_abs).2.2.2.2
        have hφ_eq : virasoroPhi c (v : ℂ) = (((virasoroPhiR c) v : ℝ) : ℂ) := Complex.ext rfl himφ
        have hd_eq : deriv (virasoroPhi c) (v : ℂ) = (((deriv (virasoroPhi c) (v : ℂ)).re : ℝ) : ℂ) :=
          Complex.ext rfl hd_im
        unfold lowerF
        dsimp only
        conv_lhs => rw [heq, hφ_eq, hd_eq]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hd_re])]
      rw [intervalIntegral.integral_congr hfn]
      have hcont_ψn : ContinuousOn (fun ut : ℝ => ‖virasoroPsiTilde c g (ut : ℂ)‖) ((virasoroPhiR c) '' uIcc u₁ R) := by
        have hc1000 : 1000 ≤ c := by linarith only [hc10000]
        refine continuous_norm.comp_continuousOn ((virasoroPsiTilde_analyticOnNhd hc1000 hwf.1).continuousOn.comp
          Complex.continuous_ofReal.continuousOn ?_)
        rintro ut ⟨v, hv, rfl⟩
        rw [uIcc_of_le hu1_le_R] at hv
        exact virasoro_closedBall_subset_psiDom hc0 (mem_closedBall_zero_iff.mpr (by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact hphiR_A2 v ⟨by linarith only [hv.1, hu1_pos, hR0], hv.2⟩))
      refine intervalIntegral.integral_comp_mul_deriv'
        (fun v hv => hphiR_diff v (by
          rw [uIcc_of_le hu1_le_R] at hv; exact ⟨by linarith only [hv.1, hu1_pos, hR0], hv.2⟩))
        (hphiR_deriv_cont.mono (by
          rw [uIcc_of_le hu1_le_R]; exact Icc_subset_Icc (by linarith only [hu1_pos, hR0]) le_rfl))
        hcont_ψn
    have hu1_phi_lb : (1 / 2 : ℝ) * (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ) ≤ (virasoroPhiR c) u₁ ∧ 1 ≤ (virasoroPhiR c) u₁ := by
      have hsub := (hφ_real u₁ (by rw [abs_of_pos hu1_pos]; exact hu1_le_R)).1
      change |(virasoroPhiR c u₁) - u₁| ≤ Cφ * c ^ (-(1 / 3 : ℝ)) at hsub
      have h1 : u₁ - 1 / 2 ≤ (virasoroPhiR c) u₁ := by linarith only [(abs_le.mp hsub).1, hCφ_c13]
      have hu1_ge_rmin : (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ) ≤ u₁ :=
        Real.rpow_le_rpow (by unfold lowerRmin; positivity) hR.1 (by norm_num)
      have hu1_ge_1 : (1 / 2 : ℝ) * (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ) ≤ u₁ - 1 / 2 := by
        have h2 : (16 : ℝ) ^ (1 / 4 : ℝ) ≤ (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (by linarith only [hRmin_ge, hCφ]) (by norm_num)
        have h16_eq : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by norm_num
        linarith only [hu1_ge_rmin, hu1_ge2, h2, h16_eq]
      exact ⟨hu1_ge_1.trans h1, by linarith only [hu1_ge2, h1]⟩
    have hphi_le_12 : (virasoroPhiR c) u₁ ≤ (virasoroPhiR c) R :=
      hphiR_strictMono.monotoneOn ⟨by linarith only [hu1_pos, hR0], hu1_le_R⟩
        ⟨by linarith only [hR0], le_rfl⟩ hu1_le_R
    have hphi_R_A2 : (virasoroPhiR c) R ≤ virasoroAC c ^ 2 := by
      have := hphiR_A2 R ⟨by linarith only [hR0], le_rfl⟩
      exact (abs_le.mp this).2
    have htail := virasoro_pos_real_norm_tail_le hc_Q hsig_nn hsig_le hu1_phi_lb.2 hphi_le_12 hphi_R_A2
      hwf.1 hM_pos
    calc |∫ v in u₁..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re|
        ≤ ∫ v in u₁..R, ‖lowerF virasoroProblem virasoroPhi c g (v : ℂ)‖ := h1
      _ = ∫ ut in ((virasoroPhiR c) u₁)..((virasoroPhiR c) R), ‖virasoroPsiTilde c g (ut : ℂ)‖ := hcov_norm
      _ ≤ (6 / 5 : ℝ) * virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * (virasoroPhiR c) u₁) := htail
      _ ≤ c ^ (-(4 / 3 : ℝ)) := hexp_tail_le hu1_phi_lb.1
  calc |∫ v in (0 : ℝ)..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re|
      = |(∫ v in (0 : ℝ)..u₁, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re) +
          ∫ v in u₁..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re| := by
        rw [hsplit]
    _ ≤ |∫ v in (0 : ℝ)..u₁, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re| +
          |∫ v in u₁..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re| :=
        abs_add_le _ _
    _ ≤ 2 * virasoroC1 ^ (-18 : ℝ) * c ^ (-(4 / 3 : ℝ)) + c ^ (-(4 / 3 : ℝ)) := add_le_add hnear hfar
    _ = (2 * virasoroC1 ^ (-18 : ℝ) + 1) * c ^ (-(4 / 3 : ℝ)) := by ring
-- =====================================================================

private lemma mass_exp_part2 {c T R Cφ C_gap κ_gap : ℝ} {g : ℝ → ℝ}
    (hc0 : 0 < c) (hc10000 : 10000 ≤ c) (hc_Q : virasoroCQEnv ≤ c)
    (hwf : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    (hR : LowerRadiusRange virasoroC1 c R)
    (hR0 : 0 < R) (hR_ge16 : 16 ≤ R)
    (hφ_real : ∀ x : ℝ, |x| ≤ R →
      |(virasoroPhi c (x : ℂ)).re - x| ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧
        |(virasoroPhi c (x : ℂ)).re| ≤ virasoroAC c ^ 2 * (3 / 4) ∧
        1 / 2 ≤ (deriv (virasoroPhi c) (x : ℂ)).re ∧
        ‖deriv (virasoroPhi c) (x : ℂ) - 1‖ ≤ Cφ * c ^ (-1 : ℝ) ∧
        (deriv (virasoroPhi c) (x : ℂ)).im = 0)
    (hphiR_diff : ∀ x ∈ Icc (-R) R, HasDerivAt (virasoroPhiR c) (deriv (virasoroPhi c) (x : ℂ)).re x)
    (hphiR_deriv_cont : ContinuousOn (fun x : ℝ => (deriv (virasoroPhi c) (x : ℂ)).re) (Icc (-R) R))
    (hphiR_strictMono : StrictMonoOn (virasoroPhiR c) (Icc (-R) R))
    (hA2_pos : 0 < virasoroAC c ^ 2)
    (hphiR_A2 : ∀ x ∈ Icc (-R) R, |virasoroPhiR c x| ≤ virasoroAC c ^ 2)
    (h_re_f_eq : ∀ x ∈ Icc (-R) R,
      (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re =
        (psiTilde virasoroProblem c g (((virasoroPhiR c) x : ℝ) : ℂ)).re *
          (deriv (virasoroPhi c) (x : ℂ)).re)
    (hψ_re_cont_A2 : ContinuousOn (fun ut : ℝ => (psiTilde virasoroProblem c g (ut : ℂ)).re)
      (Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2)))
    (hCφ_c13 : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2)
    (hsig_nn : 0 ≤ virasoroSigma c) (hsig_le : virasoroSigma c ≤ 1 / 2)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c / 12) g)
    (hdl_bd : virasoroDeltaLobe c g ≤ C_gap * Real.exp (-κ_gap * c))
    (hc_dl_le : C_gap * Real.exp (-κ_gap * c) ≤ c ^ (-(4 / 3 : ℝ)))
    (hexp_tail_le : ∀ {A : ℝ}, (1 / 2 : ℝ) * (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ) ≤ A →
      (6 / 5 : ℝ) * virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * A) ≤ c ^ (-(4 / 3 : ℝ))) :
    |(∫ x in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re) +
        virasoroProblem.gVac (c / 12) g / (2 * π * virasoroProblem.cardyNorm (c / 12) g) +
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in Ioi (virasoroDeltaChart c (virasoroPhi c ((-R : ℝ) : ℂ)).re),
            g t * virasoroProblem.cardyV (c / 12) t| ≤
      2 * c ^ (-(4 / 3 : ℝ)) := by
  change |(∫ x in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re) +
        virasoroProblem.gVac (c / 12) g / (2 * π * virasoroProblem.cardyNorm (c / 12) g) +
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in Ioi (virasoroDeltaChart c ((virasoroPhiR c) (-R))),
            g t * virasoroProblem.cardyV (c / 12) t| ≤
      2 * c ^ (-(4 / 3 : ℝ))
  have ha_shift : virasoroProblem.totalShift ≤ c / 12 := by rw [virasoroProblem_totalShift]; linarith only [hc10000]
  have hV_nn : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ virasoroProblem.cardyV (c / 12) t := fun {t} ht =>
    virasoroProblem.cardyV_nonneg ha_shift ht
  have hgv_int : IntegrableOn (fun t : ℝ => g t * virasoroProblem.cardyV (c / 12) t) (Ioi 0) := by
    refine hwf.1.int_cardy.mono'
      (((hwf.1.cont.mul (continuous_cardyV virasoroProblem (c / 12)).continuousOn).aestronglyMeasurable
        measurableSet_Ici).mono_set Ioi_subset_Ici_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hV_nn ht.le)]
  have hcov_all : ∫ x in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re =
      ∫ ut in ((virasoroPhiR c) (-R))..((virasoroPhiR c) R), (psiTilde virasoroProblem c g (ut : ℂ)).re := by
    have hfun : EqOn (fun x : ℝ => (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re)
        (fun x : ℝ => (psiTilde virasoroProblem c g (((virasoroPhiR c) x : ℝ) : ℂ)).re *
          (deriv (virasoroPhi c) (x : ℂ)).re) (uIcc (-R) R) := by
      intro x hx
      rw [uIcc_of_le (by linarith only [hR0])] at hx
      exact h_re_f_eq x hx
    rw [intervalIntegral.integral_congr hfun]
    refine intervalIntegral.integral_comp_mul_deriv'
      (fun x hx => hphiR_diff x (by rwa [uIcc_of_le (by linarith only [hR0])] at hx))
      (by rwa [uIcc_of_le (by linarith only [hR0])])
      (hψ_re_cont_A2.mono ?_)
    rintro ut ⟨x, hx, rfl⟩
    rw [uIcc_of_le (by linarith only [hR0])] at hx
    exact abs_le.mp (hphiR_A2 x hx)
  have hphi_negR_le_R : (virasoroPhiR c) (-R) ≤ (virasoroPhiR c) R :=
    hphiR_strictMono.monotoneOn ⟨le_rfl, by linarith only [hR0]⟩ ⟨by linarith only [hR0], le_rfl⟩ (by linarith only [hR0])
  have hphi_R_le_A2 : (virasoroPhiR c) R ≤ virasoroAC c ^ 2 :=
    (abs_le.mp (hphiR_A2 R ⟨by linarith only [hR0], le_rfl⟩)).2
  have hphi_negR_ge_A2 : -(virasoroAC c ^ 2) ≤ (virasoroPhiR c) (-R) :=
    (abs_le.mp (hphiR_A2 (-R) ⟨le_rfl, by linarith only [hR0]⟩)).1
  have hψ_split : ∫ ut in ((virasoroPhiR c) (-R))..((virasoroPhiR c) R), (psiTilde virasoroProblem c g (ut : ℂ)).re =
      (∫ ut in ((virasoroPhiR c) (-R))..(virasoroAC c ^ 2), (psiTilde virasoroProblem c g (ut : ℂ)).re) -
        ∫ ut in ((virasoroPhiR c) R)..(virasoroAC c ^ 2), (psiTilde virasoroProblem c g (ut : ℂ)).re := by
    have hi1 : IntervalIntegrable (fun ut : ℝ => (psiTilde virasoroProblem c g (ut : ℂ)).re)
        volume ((virasoroPhiR c) (-R)) ((virasoroPhiR c) R) :=
      (hψ_re_cont_A2.mono (Icc_subset_Icc hphi_negR_ge_A2 hphi_R_le_A2)).intervalIntegrable_of_Icc hphi_negR_le_R
    have hi2 : IntervalIntegrable (fun ut : ℝ => (psiTilde virasoroProblem c g (ut : ℂ)).re)
        volume ((virasoroPhiR c) R) (virasoroAC c ^ 2) :=
      (hψ_re_cont_A2.mono (Icc_subset_Icc (hphi_negR_ge_A2.trans hphi_negR_le_R) le_rfl)).intervalIntegrable_of_Icc hphi_R_le_A2
    linarith only [intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hR_pos_tail : |∫ ut in ((virasoroPhiR c) R)..(virasoroAC c ^ 2), (psiTilde virasoroProblem c g (ut : ℂ)).re| ≤
      c ^ (-(4 / 3 : ℝ)) := by
    have heq : psiTilde virasoroProblem c g = virasoroPsiTilde c g :=
      funext (psiTilde_virasoroProblem hc0.le g)
    have hhi_lb : (1 / 2 : ℝ) * (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ) ≤ (virasoroPhiR c) R ∧ 1 ≤ (virasoroPhiR c) R := by
      have hsub := (hφ_real R (by rw [abs_of_nonneg hR0.le])).1
      change |(virasoroPhiR c R) - R| ≤ Cφ * c ^ (-(1 / 3 : ℝ)) at hsub
      have h1 : R - 1 / 2 ≤ (virasoroPhiR c) R := by linarith only [(abs_le.mp hsub).1, hCφ_c13]
      have hR4_le : (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ) ≤ R := by
        calc (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ) ≤ R ^ (1 / 4 : ℝ) :=
              Real.rpow_le_rpow (by unfold lowerRmin; positivity) hR.1 (by norm_num)
          _ ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hR_ge16]) (by norm_num)
          _ = R := Real.rpow_one R
      exact ⟨by linarith only [hR4_le, h1, hR_ge16], by linarith only [h1, hR_ge16]⟩
    have hi_re : IntervalIntegrable (fun ut : ℝ => (virasoroPsiTilde c g (ut : ℂ)).re)
        volume ((virasoroPhiR c) R) (virasoroAC c ^ 2) := by
      rw [← heq]
      exact (hψ_re_cont_A2.mono (Icc_subset_Icc (hphi_negR_ge_A2.trans hphi_negR_le_R) le_rfl)).intervalIntegrable_of_Icc hphi_R_le_A2
    have hi_norm : IntervalIntegrable (fun ut : ℝ => ‖virasoroPsiTilde c g (ut : ℂ)‖)
        volume ((virasoroPhiR c) R) (virasoroAC c ^ 2) := by
      have hc1000 : 1000 ≤ c := by linarith only [hc10000]
      exact (continuous_norm.comp_continuousOn ((virasoroPsiTilde_analyticOnNhd hc1000 hwf.1).continuousOn.comp
        Complex.continuous_ofReal.continuousOn fun ut hut => virasoro_closedBall_subset_psiDom hc0
          (mem_closedBall_zero_iff.mpr (by
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact abs_le.mpr ⟨(hphi_negR_ge_A2.trans hphi_negR_le_R).trans hut.1, hut.2⟩)))).intervalIntegrable_of_Icc hphi_R_le_A2
    have htail := virasoro_pos_real_norm_tail_le hc_Q hsig_nn hsig_le hhi_lb.2 hphi_R_le_A2 le_rfl hwf.1 hM_pos
    calc |∫ ut in ((virasoroPhiR c) R)..(virasoroAC c ^ 2), (psiTilde virasoroProblem c g (ut : ℂ)).re|
        = |∫ ut in ((virasoroPhiR c) R)..(virasoroAC c ^ 2), (virasoroPsiTilde c g (ut : ℂ)).re| := by rw [heq]
      _ ≤ ∫ ut in ((virasoroPhiR c) R)..(virasoroAC c ^ 2), |(virasoroPsiTilde c g (ut : ℂ)).re| :=
          intervalIntegral.abs_integral_le_integral_abs hphi_R_le_A2
      _ ≤ ∫ ut in ((virasoroPhiR c) R)..(virasoroAC c ^ 2), ‖virasoroPsiTilde c g (ut : ℂ)‖ :=
          intervalIntegral.integral_mono_on hphi_R_le_A2 hi_re.abs hi_norm fun ut _ =>
            Complex.abs_re_le_norm _
      _ ≤ (6 / 5 : ℝ) * virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * (virasoroPhiR c) R) := htail
      _ ≤ c ^ (-(4 / 3 : ℝ)) := hexp_tail_le hhi_lb.1

  have hre_t := psiTilde_re_integral_eq virasoroProblem hc0 hwf.1 hphi_negR_ge_A2 le_rfl
    (hphi_negR_le_R.trans hphi_R_le_A2)
  have hΔA2_pos : 0 < virasoroDeltaChart c (virasoroAC c ^ 2) :=
    virasoroDeltaChart_pos hc0 (by rw [abs_of_nonneg (sq_nonneg _)])
  have hΔnegR_gt : virasoroDeltaChart c (virasoroAC c ^ 2) ≤ virasoroDeltaChart c ((virasoroPhiR c) (-R)) :=
    (virasoroDeltaChart_strictAnti hc0).antitoneOn
      ⟨hphi_negR_ge_A2, hphi_negR_le_R.trans hphi_R_le_A2⟩ ⟨by linarith only [hA2_pos], le_rfl⟩
      (hphi_negR_le_R.trans hphi_R_le_A2)
  have hgvac_eq : virasoroProblem.gVac (c / 12) g / (2 * π * virasoroProblem.cardyNorm (c / 12) g) =
      -((virasoroProblem.cardyNorm (c / 12) g)⁻¹ * ∫ t in Ioi (0 : ℝ), g t * virasoroProblem.cardyV (c / 12) t) := by
    unfold FixedWeightProblem.gVac
    field_simp [Real.pi_ne_zero, hM_pos.ne']
  have hioi_split : ∫ t in Ioi (0 : ℝ), g t * virasoroProblem.cardyV (c / 12) t =
      (∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)), g t * virasoroProblem.cardyV (c / 12) t) +
      (∫ t in (virasoroDeltaChart c (virasoroAC c ^ 2))..(virasoroDeltaChart c ((virasoroPhiR c) (-R))),
        g t * virasoroProblem.cardyV (c / 12) t) +
      ∫ t in Ioi (virasoroDeltaChart c ((virasoroPhiR c) (-R))), g t * virasoroProblem.cardyV (c / 12) t := by
    have hi_ab : ∫ t in Ioc (virasoroDeltaChart c (virasoroAC c ^ 2)) (virasoroDeltaChart c ((virasoroPhiR c) (-R))),
          g t * virasoroProblem.cardyV (c / 12) t =
        ∫ t in (virasoroDeltaChart c (virasoroAC c ^ 2))..(virasoroDeltaChart c ((virasoroPhiR c) (-R))),
          g t * virasoroProblem.cardyV (c / 12) t :=
      (intervalIntegral.integral_of_le hΔnegR_gt).symm
    have h_int1 : IntegrableOn (fun t => g t * virasoroProblem.cardyV (c / 12) t)
        (Ioc 0 (virasoroDeltaChart c (virasoroAC c ^ 2))) :=
      hgv_int.mono_set Ioc_subset_Ioi_self
    have h_int2 : IntegrableOn (fun t => g t * virasoroProblem.cardyV (c / 12) t)
        (Ioi (virasoroDeltaChart c (virasoroAC c ^ 2))) :=
      hgv_int.mono_set (Ioi_subset_Ioi hΔA2_pos.le)
    have hU1 : Ioc 0 (virasoroDeltaChart c (virasoroAC c ^ 2)) ∪
        Ioi (virasoroDeltaChart c (virasoroAC c ^ 2)) = Ioi 0 :=
      Ioc_union_Ioi_eq_Ioi hΔA2_pos.le
    have hs1 := setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi h_int1 h_int2
    rw [hU1] at hs1
    have h_int3 : IntegrableOn (fun t => g t * virasoroProblem.cardyV (c / 12) t)
        (Ioc (virasoroDeltaChart c (virasoroAC c ^ 2)) (virasoroDeltaChart c ((virasoroPhiR c) (-R)))) :=
      h_int2.mono_set Ioc_subset_Ioi_self
    have h_int4 : IntegrableOn (fun t => g t * virasoroProblem.cardyV (c / 12) t)
        (Ioi (virasoroDeltaChart c ((virasoroPhiR c) (-R)))) :=
      h_int2.mono_set (Ioi_subset_Ioi hΔnegR_gt)
    have hU2 : Ioc (virasoroDeltaChart c (virasoroAC c ^ 2)) (virasoroDeltaChart c ((virasoroPhiR c) (-R))) ∪
        Ioi (virasoroDeltaChart c ((virasoroPhiR c) (-R))) = Ioi (virasoroDeltaChart c (virasoroAC c ^ 2)) :=
      Ioc_union_Ioi_eq_Ioi hΔnegR_gt
    have hs2 := setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi h_int3 h_int4
    rw [hU2] at hs2
    rw [hs1, hs2, hi_ab]
    ring
  have hsum_eq : (∫ x in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re) +
        virasoroProblem.gVac (c / 12) g / (2 * π * virasoroProblem.cardyNorm (c / 12) g) +
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in Ioi (virasoroDeltaChart c ((virasoroPhiR c) (-R))), g t * virasoroProblem.cardyV (c / 12) t =
      -(∫ ut in ((virasoroPhiR c) R)..(virasoroAC c ^ 2), (psiTilde virasoroProblem c g (ut : ℂ)).re) -
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
            g t * virasoroProblem.cardyV (c / 12) t := by
    rw [hcov_all, hψ_split, hre_t, hgvac_eq, hioi_split]
    ring
  have hdl_est : |(virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
        ∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
          g t * virasoroProblem.cardyV (c / 12) t| ≤ c ^ (-(4 / 3 : ℝ)) := by
    have h_int_abs : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV (c / 12) t)
        (Ioc 0 (virasoroDeltaChart c (virasoroAC c ^ 2))) :=
      hwf.1.int_cardy.mono_set Ioc_subset_Ioi_self
    have h_int_s : IntegrableOn (fun t => g t * virasoroProblem.cardyV (c / 12) t)
        (Ioc 0 (virasoroDeltaChart c (virasoroAC c ^ 2))) :=
      hgv_int.mono_set Ioc_subset_Ioi_self
    have hnorm : |∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
          g t * virasoroProblem.cardyV (c / 12) t| ≤
        ∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
          |g t| * virasoroProblem.cardyV (c / 12) t := by
      calc |∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
            g t * virasoroProblem.cardyV (c / 12) t|
          ≤ ∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
              |g t * virasoroProblem.cardyV (c / 12) t| := by
            have hni := MeasureTheory.norm_integral_le_integral_norm
              (fun t => g t * virasoroProblem.cardyV (c / 12) t)
              (μ := volume.restrict (Ioc 0 (virasoroDeltaChart c (virasoroAC c ^ 2))))
            simpa only [Real.norm_eq_abs] using hni
        _ = ∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
              |g t| * virasoroProblem.cardyV (c / 12) t := by
            refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
            rw [abs_mul, abs_of_nonneg (hV_nn ht.1.le)]
    have hdl_eq : virasoroDeltaLobe c g = (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
        ∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
          |g t| * virasoroProblem.cardyV (c / 12) t := by
      unfold virasoroDeltaLobe
      rw [intervalIntegral.integral_of_le hΔA2_pos.le]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hM_pos)]
    calc (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          |∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
            g t * virasoroProblem.cardyV (c / 12) t|
        ≤ (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
            ∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
              |g t| * virasoroProblem.cardyV (c / 12) t := by gcongr
      _ = virasoroDeltaLobe c g := hdl_eq.symm
      _ ≤ C_gap * Real.exp (-κ_gap * c) := hdl_bd
      _ ≤ c ^ (-(4 / 3 : ℝ)) := hc_dl_le
  rw [hsum_eq]
  calc |-(∫ ut in ((virasoroPhiR c) R)..(virasoroAC c ^ 2), (psiTilde virasoroProblem c g (ut : ℂ)).re) -
          (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
            ∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
              g t * virasoroProblem.cardyV (c / 12) t|
      ≤ |-(∫ ut in ((virasoroPhiR c) R)..(virasoroAC c ^ 2), (psiTilde virasoroProblem c g (ut : ℂ)).re)| +
          |(virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
            ∫ t in Ioc (0 : ℝ) (virasoroDeltaChart c (virasoroAC c ^ 2)),
              g t * virasoroProblem.cardyV (c / 12) t| := abs_sub _ _
    _ ≤ c ^ (-(4 / 3 : ℝ)) + c ^ (-(4 / 3 : ℝ)) := by rw [abs_neg]; exact add_le_add hR_pos_tail hdl_est
    _ = 2 * c ^ (-(4 / 3 : ℝ)) := by ring

private lemma mass_exp_part3 {c T R Cφ : ℝ} {g : ℝ → ℝ}
    (hc0 : 0 < c) (hc10000 : 10000 ≤ c) (hc_Q : virasoroCQEnv ≤ c)
    (hCφ : 0 ≤ Cφ)
    (hwf : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    (hR : LowerRadiusRange virasoroC1 c R)
    (hR0 : 0 < R) (hR_ge16 : 16 ≤ R) (hR_le_rmax : R ≤ lowerRmax virasoroC1 c)
    (hφ_uhat : ∀ x : ℝ, |x| ≤ lowerRmax virasoroC1 c → virasoroUhat c (virasoroPhi c (x : ℂ)).re = x)
    (hφ_real : ∀ x : ℝ, |x| ≤ R →
      |(virasoroPhi c (x : ℂ)).re - x| ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧
        |(virasoroPhi c (x : ℂ)).re| ≤ virasoroAC c ^ 2 * (3 / 4) ∧
        1 / 2 ≤ (deriv (virasoroPhi c) (x : ℂ)).re ∧
        ‖deriv (virasoroPhi c) (x : ℂ) - 1‖ ≤ Cφ * c ^ (-1 : ℝ) ∧
        (deriv (virasoroPhi c) (x : ℂ)).im = 0)
    (hphiR_diff : ∀ x ∈ Icc (-R) R, HasDerivAt (virasoroPhiR c) (deriv (virasoroPhi c) (x : ℂ)).re x)
    (hphiR_deriv_cont : ContinuousOn (fun x : ℝ => (deriv (virasoroPhi c) (x : ℂ)).re) (Icc (-R) R))
    (hphiR_strictMono : StrictMonoOn (virasoroPhiR c) (Icc (-R) R))
    (hA2_pos : 0 < virasoroAC c ^ 2)
    (hphiR_A2 : ∀ x ∈ Icc (-R) R, |(virasoroPhiR c) x| ≤ virasoroAC c ^ 2)
    (h_re_f_eq : ∀ x ∈ Icc (-R) R,
      (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re =
        (psiTilde virasoroProblem c g (((virasoroPhiR c) x : ℝ) : ℂ)).re *
          (deriv (virasoroPhi c) (x : ℂ)).re)
    (hψ_re_cont_A2 : ContinuousOn (fun ut : ℝ => (psiTilde virasoroProblem c g (ut : ℂ)).re)
      (Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2)))
    (hRmin_ge : 16 + 2 * (Cφ + 2) + 2 ≤ lowerRmin virasoroC1 c)
    (hCφ_c13 : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2)
    (hcc_strip_le : (2 * betaTip * chartParams.M_ψ + 2 * Cφ + 2) ^ 3 + 1 ≤ c)
    (hcc_bv_le : (2 / virasoroBV) ^ 3 + 1 ≤ c) :
    |(∫ v in (0 : ℝ)..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re) -
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (virasoroPhi c ((-R : ℝ) : ℂ)).re),
            lowerTaper virasoroPhi virasoroUhat c R t * (g t * virasoroProblem.cardyV (c / 12) t)| ≤
      (2 * virasoroC1 ^ (-24 : ℝ)) * c ^ (-(4 / 3 : ℝ)) := by
  have hc1_pos := virasoroC1_pos
  have hphi_negR_le_R : (virasoroPhiR c) (-R) ≤ (virasoroPhiR c) R :=
    hphiR_strictMono.monotoneOn ⟨le_rfl, by linarith only [hR0]⟩ ⟨by linarith only [hR0], le_rfl⟩ (by linarith only [hR0])
  have hphi_R_le_A2 : (virasoroPhiR c) R ≤ virasoroAC c ^ 2 :=
    (abs_le.mp (hphiR_A2 R ⟨by linarith only [hR0], le_rfl⟩)).2
  have hphi_negR_ge_A2 : -(virasoroAC c ^ 2) ≤ (virasoroPhiR c) (-R) :=
    (abs_le.mp (hphiR_A2 (-R) ⟨le_rfl, by linarith only [hR0]⟩)).1
  have ha_shift : virasoroProblem.totalShift ≤ c / 12 := by rw [virasoroProblem_totalShift]; linarith only [hc10000]
  have hV_nn : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ virasoroProblem.cardyV (c / 12) t := fun {t} ht =>
    virasoroProblem.cardyV_nonneg ha_shift ht
  have hgv_int : IntegrableOn (fun t : ℝ => g t * virasoroProblem.cardyV (c / 12) t) (Ioi 0) := by
    refine hwf.1.int_cardy.mono'
      (((hwf.1.cont.mul (continuous_cardyV virasoroProblem (c / 12)).continuousOn).aestronglyMeasurable
        measurableSet_Ici).mono_set Ioi_subset_Ici_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hV_nn ht.le)]
  change |(∫ v in (0 : ℝ)..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re) -
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c ((virasoroPhiR c) (-R))),
            lowerTaper virasoroPhi virasoroUhat c R t * (g t * virasoroProblem.cardyV (c / 12) t)| ≤
      (2 * virasoroC1 ^ (-24 : ℝ)) * c ^ (-(4 / 3 : ℝ))
  have h_v_eq_u : ∫ v in (0 : ℝ)..R,
        lowerWR R v * (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re =
      ∫ u in (-R)..0, lowerWR R (-u) * (lowerF virasoroProblem virasoroPhi c g (u : ℂ)).re := by
    have hcomp := intervalIntegral.integral_comp_neg (a := 0) (b := R)
      (fun u : ℝ => lowerWR R (-u) * (lowerF virasoroProblem virasoroPhi c g (u : ℂ)).re)
    simp only [neg_zero, neg_neg] at hcomp
    exact hcomp
  have h_uhat_cont : ContinuousOn (virasoroUhat c)
      (Icc (-(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) (5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) := by
    unfold virasoroUhat fjUhat virasoroPsiChart
    have hε0 : 0 ≤ c ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le (-2)
    have hε1 : c ^ (-2 : ℝ) ≤ 1 / 4 := by
      rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (c ^ 2)⁻¹ ≤ (10000 ^ 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith only [hc10000])
        _ ≤ 1 / 4 := by norm_num
    have hψc := (chartParams.hψ_spec (c ^ (-2 : ℝ)) hε0 hε1).1.continuousOn
    have hc1_r0 : 5 * virasoroC1 ^ 2 * betaTip⁻¹ ≤ chartParams.r_ψ := by
      have h1 : virasoroC1 ≤ √(chartParams.r_ψ * betaTip / 16) := (min_le_right _ _).trans (min_le_left _ _)
      have hnn : 0 ≤ chartParams.r_ψ * betaTip / 16 := by
        have := chartParams.hrψ_pos; have := betaTip_pos; positivity
      have hsq : virasoroC1 ^ 2 ≤ chartParams.r_ψ * betaTip / 16 :=
        (pow_le_pow_left₀ hc1_pos.le h1 2).trans_eq (Real.sq_sqrt hnn)
      have hβ := betaTip_pos
      calc 5 * virasoroC1 ^ 2 * betaTip⁻¹
          ≤ 5 * (chartParams.r_ψ * betaTip / 16) * betaTip⁻¹ := by gcongr
        _ = 5 / 16 * chartParams.r_ψ := by field_simp [hβ.ne']
        _ ≤ chartParams.r_ψ := by linarith only [chartParams.hrψ_pos]
    have hmaps : MapsTo (fun w : ℝ => ((virasoroMu c * w : ℝ) : ℂ))
        (Icc (-(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) (5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)))
        (ball 0 chartParams.ρ_ψ) := by
      intro w hw
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by unfold virasoroMu; have := betaTip_pos; positivity)]
      have hmu_le : virasoroMu c * |w| ≤ 5 * virasoroC1 ^ 2 * betaTip⁻¹ := by
        unfold virasoroMu
        have hβ := betaTip_pos
        have hwabs : |w| ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := abs_le.mpr hw
        calc betaTip⁻¹ * c ^ (-(2 / 3 : ℝ)) * |w|
            ≤ betaTip⁻¹ * c ^ (-(2 / 3 : ℝ)) * (5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) := by gcongr
          _ = 5 * virasoroC1 ^ 2 * betaTip⁻¹ * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) := by ring
          _ = 5 * virasoroC1 ^ 2 * betaTip⁻¹ := by rw [← Real.rpow_add hc0]; norm_num
      exact hmu_le.trans_lt (lt_of_le_of_lt hc1_r0 chartParams.hrψ_lt)
    refine continuousOn_id.add (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (hψc.comp (Complex.continuous_ofReal.continuousOn.comp
        (continuous_const.mul continuous_id).continuousOn (mapsTo_univ _ _)) hmaps)))
  have h_win_cont : ContinuousOn (fun ut : ℝ => lowerWR R (-virasoroUhat c ut))
      (Icc (-(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) (5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) := by
    have hc1 : ContinuousOn (fun ut : ℝ => (1 : ℝ) - ((1 : ℝ) - (virasoroUhat c ut / R) ^ 12) ^ 2)
        (Icc (-(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) (5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) :=
      continuousOn_const.sub ((continuousOn_const.sub ((h_uhat_cont.div_const R).pow 12)).pow 2)
    refine hc1.congr fun ut _ => ?_
    unfold lowerWR lowerW6; simp only [neg_neg]
  have h_R_band : ∀ x ∈ Icc (-R) R,
      |(virasoroPhiR c) x| ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := fun x hx => by
    have h1 := (hφ_real x (abs_le.mpr hx)).1
    change |(virasoroPhiR c x) - x| ≤ Cφ * c ^ (-(1 / 3 : ℝ)) at h1
    have hx_R : |x| ≤ R := abs_le.mpr hx
    have h2 : |(virasoroPhiR c) x| ≤ R + 1 / 2 := by
      linarith only [abs_sub_abs_le_abs_sub ((virasoroPhiR c) x) x, h1, hCφ_c13, hx_R]
    have hrm := hR.2; unfold lowerRmax at hrm
    have h12 : 1 / 2 ≤ virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by
      have hmin : 16 ≤ lowerRmin virasoroC1 c := by linarith only [hRmin_ge, hCφ]
      unfold lowerRmin at hmin; linarith only [hmin]
    linarith only [h2, hrm, h12]
  have h_u_eq_ut : ∫ u in (-R)..0, lowerWR R (-u) * (lowerF virasoroProblem virasoroPhi c g (u : ℂ)).re =
      ∫ ut in ((virasoroPhiR c) (-R))..((virasoroPhiR c) 0),
        lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re := by
    have hfn : EqOn (fun u : ℝ => lowerWR R (-u) * (lowerF virasoroProblem virasoroPhi c g (u : ℂ)).re)
        (fun u : ℝ => (lowerWR R (-virasoroUhat c ((virasoroPhiR c) u)) *
          (psiTilde virasoroProblem c g (((virasoroPhiR c) u : ℝ) : ℂ)).re) *
          (deriv (virasoroPhi c) (u : ℂ)).re)
        (uIcc (-R) 0) := by
      intro u hu
      rw [uIcc_of_le (by linarith only [hR0])] at hu
      have hu_in : u ∈ Icc (-R) R := ⟨hu.1, hu.2.trans hR0.le⟩
      have hu_rm : |u| ≤ lowerRmax virasoroC1 c := (abs_le.mpr hu_in).trans hR_le_rmax
      have hu_eq : virasoroUhat c ((virasoroPhiR c) u) = u := hφ_uhat u hu_rm
      dsimp only
      rw [hu_eq, h_re_f_eq u hu_in]
      ring
    rw [intervalIntegral.integral_congr hfn]
    have hcont_wψ : ContinuousOn
        (fun ut : ℝ => lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re)
        ((virasoroPhiR c) '' uIcc (-R) 0) := by
      refine (h_win_cont.mono ?_).mul (hψ_re_cont_A2.mono ?_)
      · rintro ut ⟨u, hu, rfl⟩
        rw [uIcc_of_le (by linarith only [hR0])] at hu
        exact abs_le.mp (h_R_band u ⟨hu.1, hu.2.trans hR0.le⟩)
      · rintro ut ⟨u, hu, rfl⟩
        rw [uIcc_of_le (by linarith only [hR0])] at hu
        exact abs_le.mp (hphiR_A2 u ⟨hu.1, hu.2.trans hR0.le⟩)
    exact intervalIntegral.integral_comp_mul_deriv'
      (fun u hu => hphiR_diff u (by rw [uIcc_of_le (by linarith only [hR0])] at hu; exact ⟨hu.1, hu.2.trans hR0.le⟩))
      (hphiR_deriv_cont.mono (by
        rw [uIcc_of_le (by linarith only [hR0])]; exact Icc_subset_Icc le_rfl hR0.le))
      hcont_wψ
  have hphi_negR_lt0 : (virasoroPhiR c) (-R) < 0 := by
    have h1 := (hφ_real (-R) (by rw [abs_neg, abs_of_pos hR0])).1
    change |(virasoroPhiR c (-R)) - (-R)| ≤ Cφ * c ^ (-(1 / 3 : ℝ)) at h1
    linarith only [(abs_le.mp h1).2, hCφ_c13, hR_ge16]
  have hphi_0_abs : |(virasoroPhiR c) 0| ≤ 1 / 2 := by
    have h1 := (hφ_real 0 (by rw [abs_zero]; exact hR0.le)).1
    change |(virasoroPhiR c 0) - 0| ≤ Cφ * c ^ (-(1 / 3 : ℝ)) at h1
    simp only [sub_zero] at h1
    exact h1.trans hCφ_c13
  have hlo_0 : (virasoroPhiR c) (-R) ≤ 0 := hphi_negR_lt0.le
  have hhalf_le_A2 : 1 / 2 ≤ virasoroAC c ^ 2 := by
    have hbv := virasoroBV_pos
    have hbase : ((2 / virasoroBV : ℝ) ^ (3 : ℕ)) ≤ c := by linarith only [hcc_bv_le]
    have h1 := Real.rpow_le_rpow (by positivity) hbase (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at h1
    norm_num at h1
    have h2 : 1 ≤ virasoroBV * c ^ (1 / 3 : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left h1 hbv.le
      have hdv : virasoroBV * (2 / virasoroBV) = 2 := by field_simp [hbv.ne']
      linarith only [hm, hdv]
    have hsq := pow_le_pow_left₀ zero_le_one h2 2
    rw [virasoroAC_sq c hc0.le]
    have heq : (virasoroBV * c ^ (1 / 3 : ℝ)) ^ 2 = virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc0.le]; norm_num
    nlinarith only [hsq, heq]
  have h_band_all : ∀ ut ∈ uIcc (min ((virasoroPhiR c) (-R)) 0) (max ((virasoroPhiR c) 0) 0),
      |ut| ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) ∧ |ut| ≤ virasoroAC c ^ 2 := by
    intro ut hut
    rw [uIcc_of_le (le_trans (min_le_right _ _) (le_max_right _ _))] at hut
    have h_b1 : |(virasoroPhiR c) (-R)| ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := h_R_band (-R) ⟨le_rfl, by linarith only [hR0]⟩
    have h_b2 : |(virasoroPhiR c) (-R)| ≤ virasoroAC c ^ 2 := hphiR_A2 (-R) ⟨le_rfl, by linarith only [hR0]⟩
    have h_lo_band : -(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) ≤ ut := by
      have h1 : -(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) ≤ min ((virasoroPhiR c) (-R)) 0 :=
        le_min (abs_le.mp h_b1).1 (neg_nonpos.mpr (by have := virasoroC1_pos; positivity))
      exact h1.trans hut.1
    have h_hi_band : ut ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by
      have h1 : max ((virasoroPhiR c) 0) 0 ≤ 1 / 2 := max_le (abs_le.mp hphi_0_abs).2 (by positivity)
      have h12 : 1 / 2 ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by
        have hmin : 16 ≤ lowerRmin virasoroC1 c := by linarith only [hRmin_ge, hCφ]
        unfold lowerRmin at hmin; linarith only [hmin]
      exact hut.2.trans (h1.trans h12)
    have h_lo_A2 : -(virasoroAC c ^ 2) ≤ ut :=
      (le_min (abs_le.mp h_b2).1 (by linarith only [hA2_pos])).trans hut.1
    have h_hi_A2 : ut ≤ virasoroAC c ^ 2 :=
      hut.2.trans (max_le ((abs_le.mp hphi_0_abs).2.trans hhalf_le_A2) hA2_pos.le)
    exact ⟨abs_le.mpr ⟨h_lo_band, h_hi_band⟩, abs_le.mpr ⟨h_lo_A2, h_hi_A2⟩⟩
  have hcont_all : ContinuousOn
      (fun ut : ℝ => lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re)
      (Icc ((virasoroPhiR c) (-R)) (max ((virasoroPhiR c) 0) 0)) := by
    refine (h_win_cont.mono fun ut hut => ?_).mul (hψ_re_cont_A2.mono fun ut hut => ?_)
    · exact abs_le.mp (h_band_all ut (by
        rw [uIcc_of_le (le_trans (min_le_right _ _) (le_max_right _ _))]
        exact ⟨(min_le_left _ _).trans hut.1, hut.2⟩)).1
    · exact abs_le.mp (h_band_all ut (by
        rw [uIcc_of_le (le_trans (min_le_right _ _) (le_max_right _ _))]
        exact ⟨(min_le_left _ _).trans hut.1, hut.2⟩)).2
  have hi_left : IntervalIntegrable
      (fun ut : ℝ => lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re)
      volume ((virasoroPhiR c) (-R)) 0 :=
    (hcont_all.mono (Icc_subset_Icc_right (le_max_right _ _))).intervalIntegrable_of_Icc hlo_0
  have hi_strip : IntervalIntegrable
      (fun ut : ℝ => lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re)
      volume 0 ((virasoroPhiR c) 0) := by
    rcases le_total 0 ((virasoroPhiR c) 0) with h0p | hp0
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h0p]
      exact (hcont_all.mono (Icc_subset_Icc hlo_0 (le_max_left _ _))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · refine IntervalIntegrable.symm ?_
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hp0]
      have h_phiR_mR : (virasoroPhiR c) (-R) ≤ (virasoroPhiR c) 0 := hphiR_strictMono.monotoneOn
        ⟨le_rfl, by linarith only [hR0]⟩ ⟨by linarith only [hR0], hR0.le⟩ (neg_nonpos.mpr hR0.le)
      exact (hcont_all.mono (Icc_subset_Icc h_phiR_mR (le_max_right _ _))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hsplit_0 := intervalIntegral.integral_add_adjacent_intervals hi_left hi_strip
  -- Substitution `t = virasoroDeltaChart c ut` on `[(virasoroPhiR c) (-R), 0]`:
  have hcov_taper : ∫ ut in ((virasoroPhiR c) (-R))..0,
        lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re =
      (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c ((virasoroPhiR c) (-R))),
          lowerTaper virasoroPhi virasoroUhat c R t * (g t * virasoroProblem.cardyV (c / 12) t) := by
    have hut_A2 : ∀ ut ∈ Icc ((virasoroPhiR c) (-R)) 0, |ut| ≤ virasoroAC c ^ 2 := fun ut hut =>
      abs_le.mpr ⟨hphi_negR_ge_A2.trans hut.1, hut.2.trans hA2_pos.le⟩
    have h1 : ∫ ut in ((virasoroPhiR c) (-R))..0,
          lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re =
        -((virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ ut in ((virasoroPhiR c) (-R))..0,
            (lowerWR R (-virasoroUhat c ut) * g (virasoroDeltaChart c ut) *
              virasoroProblem.cardyV (c / 12) (virasoroDeltaChart c ut)) *
              deriv (virasoroDeltaChart c) ut) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun ut hut => ?_
      rw [uIcc_of_le hlo_0] at hut
      rw [psiTilde_re_ofReal virasoroProblem hc0 hwf.1 (hut_A2 ut hut)]
      ring
    have hΔ_lo_le : virasoroDeltaChart c 0 ≤ virasoroDeltaChart c ((virasoroPhiR c) (-R)) :=
      (virasoroDeltaChart_strictAnti hc0).antitoneOn
        ⟨hphi_negR_ge_A2, hphi_negR_le_R.trans hphi_R_le_A2⟩
        ⟨by linarith only [hA2_pos], hA2_pos.le⟩ hlo_0
    have hsub : ∫ ut in ((virasoroPhiR c) (-R))..0,
          (lowerWR R (-virasoroUhat c ut) * g (virasoroDeltaChart c ut) *
            virasoroProblem.cardyV (c / 12) (virasoroDeltaChart c ut)) *
            deriv (virasoroDeltaChart c) ut =
        ∫ t in (virasoroDeltaChart c ((virasoroPhiR c) (-R)))..(virasoroDeltaChart c 0),
          lowerTaper virasoroPhi virasoroUhat c R t * (g t * virasoroProblem.cardyV (c / 12) t) := by
      have hderiv_at : ∀ ut ∈ uIcc ((virasoroPhiR c) (-R)) 0,
          HasDerivAt (virasoroDeltaChart c) (deriv (virasoroDeltaChart c) ut) ut := fun ut hut => by
        rw [uIcc_of_le hlo_0] at hut
        have hd := virasoroDeltaChart_hasDerivAt hc0 (hut_A2 ut hut)
        exact hd.deriv ▸ hd
      have hcont_der : ContinuousOn (deriv (virasoroDeltaChart c)) (uIcc ((virasoroPhiR c) (-R)) 0) := by
        rw [uIcc_of_le hlo_0]
        let G : ℝ → ℝ := fun ut =>
          c ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((ut * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re
        have hG_cont : ContinuousOn G (Icc ((virasoroPhiR c) (-R)) 0) := fun ut hut => by
          have hw : ((ut * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
            have h1 := virasoro_u_mem_open_ball hc0 (u := (ut : ℂ))
              (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hut_A2 ut hut)
            rwa [show (ut : ℂ) * ((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
              ((ut * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) by push_cast; rfl] at h1
          have hd_an := (virasoroXiInf_an.deriv _ hw).continuousAt
          have hcomp := hd_an.comp_of_eq
            (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).continuousAt rfl
          exact (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hcomp)).continuousWithinAt
        exact hG_cont.congr fun ut hut => (virasoroDeltaChart_hasDerivAt hc0 (hut_A2 ut hut)).deriv
      have himg : virasoroDeltaChart c '' uIcc ((virasoroPhiR c) (-R)) 0 ⊆
          Icc (virasoroDeltaChart c 0) (virasoroDeltaChart c ((virasoroPhiR c) (-R))) := by
        rintro t ⟨ut, hut, rfl⟩
        rw [uIcc_of_le hlo_0] at hut
        exact ⟨(virasoroDeltaChart_strictAnti hc0).antitoneOn
            ⟨hphi_negR_ge_A2.trans hut.1, hut.2.trans hA2_pos.le⟩
            ⟨by linarith only [hA2_pos], hA2_pos.le⟩ hut.2,
          (virasoroDeltaChart_strictAnti hc0).antitoneOn
            ⟨hphi_negR_ge_A2, hlo_0.trans hA2_pos.le⟩
            ⟨hphi_negR_ge_A2.trans hut.1, hut.2.trans hA2_pos.le⟩ hut.1⟩
      have hcont_t : ContinuousOn
          (fun t : ℝ => lowerTaper virasoroPhi virasoroUhat c R t * (g t * virasoroProblem.cardyV (c / 12) t))
          (virasoroDeltaChart c '' uIcc ((virasoroPhiR c) (-R)) 0) := by
        have hu_cont : ContinuousOn (fun t : ℝ => virasoroUChart c (t / c))
            (virasoroDeltaChart c '' uIcc ((virasoroPhiR c) (-R)) 0) := by
          rintro t ⟨ut, hut, rfl⟩
          rw [uIcc_of_le hlo_0] at hut
          have hdiv := virasoroDeltaChart_div_mem hc0 (hut_A2 ut hut)
          have hξ_open : ((virasoroDeltaChart c ut / c : ℝ) : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
            rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            have h1 : |virasoroDeltaChart c ut / c - xiBar| ≤ virasoroChartR0 :=
              abs_le.mpr ⟨by linarith [hdiv.1], by linarith [hdiv.2]⟩
            exact h1.trans_lt (ConcreteBootstrap.chartParams.hr_xi0_le.trans_lt (half_lt_self virasoroRXiInf_pos))
          have hcont_at : ContinuousAt (fun x : ℝ => virasoroUChart c (x / c)) (virasoroDeltaChart c ut) := by
            unfold virasoroUChart
            have hcomp := (virasoroUInf_an _ hξ_open).continuousAt.comp_of_eq
              (Complex.continuous_ofReal.comp (continuous_id.div_const c)).continuousAt rfl
            exact continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hcomp)
          exact hcont_at.continuousWithinAt
        have hu_maps : MapsTo (fun t : ℝ => virasoroUChart c (t / c))
            (virasoroDeltaChart c '' uIcc ((virasoroPhiR c) (-R)) 0)
            (Icc (-(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) (5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ))) := by
          rintro t ⟨ut, hut, rfl⟩
          rw [uIcc_of_le hlo_0] at hut
          dsimp only
          rw [virasoroUChart_deltaChart hc0 (hut_A2 ut hut)]
          exact abs_le.mp (h_band_all ut (by
            rw [uIcc_of_le (le_trans (min_le_right _ _) (le_max_right _ _))]
            exact ⟨(min_le_left _ _).trans hut.1, hut.2.trans (le_max_right _ _)⟩)).1
        have h_taper_cont : ContinuousOn (lowerTaper virasoroPhi virasoroUhat c R)
            (virasoroDeltaChart c '' uIcc ((virasoroPhiR c) (-R)) 0) :=
          (h_win_cont.comp hu_cont hu_maps).congr fun t ht => by
            unfold lowerTaper
            split_ifs with hcond
            · rfl
            · exact False.elim (hcond ⟨(himg ht).1, (himg ht).2⟩)
        have h_pos_set : virasoroDeltaChart c '' uIcc ((virasoroPhiR c) (-R)) 0 ⊆ Ici 0 := by
          rintro t ⟨ut, hut, rfl⟩
          rw [uIcc_of_le hlo_0] at hut
          exact (virasoroDeltaChart_pos hc0 (hut_A2 ut hut)).le
        exact h_taper_cont.mul ((hwf.1.cont.mul (continuous_cardyV virasoroProblem (c / 12)).continuousOn).mono h_pos_set)
      have hfn_sub : EqOn
          (fun ut : ℝ =>
            (lowerWR R (-virasoroUhat c ut) * g (virasoroDeltaChart c ut) *
              virasoroProblem.cardyV (c / 12) (virasoroDeltaChart c ut)) *
              deriv (virasoroDeltaChart c) ut)
          (fun ut : ℝ =>
            (lowerTaper virasoroPhi virasoroUhat c R (virasoroDeltaChart c ut) *
              (g (virasoroDeltaChart c ut) * virasoroProblem.cardyV (c / 12) (virasoroDeltaChart c ut))) *
              deriv (virasoroDeltaChart c) ut)
          (uIcc ((virasoroPhiR c) (-R)) 0) := by
        intro ut hut
        have hmem : virasoroDeltaChart c ut ∈ Icc (virasoroDeltaChart c 0) (virasoroDeltaChart c ((virasoroPhiR c) (-R))) :=
          himg (mem_image_of_mem _ hut)
        rw [uIcc_of_le hlo_0] at hut
        have hut_eq : lowerTaper virasoroPhi virasoroUhat c R (virasoroDeltaChart c ut) = lowerWR R (-virasoroUhat c ut) := by
          unfold lowerTaper
          split_ifs with hcond
          · rw [virasoroUChart_deltaChart hc0 (hut_A2 ut hut)]
          · exact False.elim (hcond ⟨hmem.1, hmem.2⟩)
        dsimp only
        rw [hut_eq]; ring
      rw [intervalIntegral.integral_congr hfn_sub]
      exact intervalIntegral.integral_comp_mul_deriv' hderiv_at hcont_der hcont_t
    rw [h1, hsub, intervalIntegral.integral_symm (virasoroDeltaChart c 0) (virasoroDeltaChart c ((virasoroPhiR c) (-R)))]
    ring
  -- Strip `|∫ ut in 0..((virasoroPhiR c) 0), ...| ≤ 2 virasoroC1^{-24} c^{-4/3}`
  have h_strip : |∫ ut in (0 : ℝ)..((virasoroPhiR c) 0),
        lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re| ≤
      (2 * virasoroC1 ^ (-24 : ℝ)) * c ^ (-(4 / 3 : ℝ)) := by
    have heq : psiTilde virasoroProblem c g = virasoroPsiTilde c g :=
      funext (psiTilde_virasoroProblem hc0.le g)
    have hQ3_L1 : ∫ ut in (-(virasoroAC c ^ 2))..(virasoroAC c ^ 2),
        ‖psiTilde virasoroProblem c g (ut : ℂ)‖ ≤ 1 := by
      rw [heq]; exact (lemmaQ_part3 hc_Q hwf).2.1
    have h_int_A2 : IntervalIntegrable (fun ut : ℝ => ‖psiTilde virasoroProblem c g (ut : ℂ)‖)
        volume (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2) := by
      rw [heq]
      have hc1000 : 1000 ≤ c := by linarith only [hc10000]
      exact (continuous_norm.comp_continuousOn ((virasoroPsiTilde_analyticOnNhd hc1000 hwf.1).continuousOn.comp
        Complex.continuous_ofReal.continuousOn fun ut hut => virasoro_closedBall_subset_psiDom hc0
          (mem_closedBall_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hut)))).intervalIntegrable_of_Icc
        (by linarith only [hA2_pos])
    have hmin16 : 16 ≤ lowerRmin virasoroC1 c := by linarith only [hRmin_ge, hCφ]
    have hc_s : (2 * betaTip * chartParams.M_ψ + 2) ^ 3 + 1 ≤ c := by
      have hbm1 : 0 ≤ 2 * betaTip * chartParams.M_ψ + 2 := by
        have := betaTip_pos; have := chartParams.hMψ_nn; positivity
      have hpow3 : (2 * betaTip * chartParams.M_ψ + 2) ^ 3 ≤ (2 * betaTip * chartParams.M_ψ + 2 * Cφ + 2) ^ 3 :=
        pow_le_pow_left₀ hbm1 (by linarith only [hCφ]) 3
      linarith only [hpow3, hcc_strip_le]
    exact virasoro_strip_interval_le hc10000 hmin16 hR.1 hc_s hhalf_le_A2 hphi_0_abs
      h_win_cont hψ_re_cont_A2 h_int_A2 hQ3_L1
  have hfin : (∫ v in (0 : ℝ)..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re) -
      (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c ((virasoroPhiR c) (-R))),
          lowerTaper virasoroPhi virasoroUhat c R t * (g t * virasoroProblem.cardyV (c / 12) t) =
      ∫ ut in (0 : ℝ)..((virasoroPhiR c) 0), lowerWR R (-virasoroUhat c ut) * (psiTilde virasoroProblem c g (ut : ℂ)).re := by
    rw [h_v_eq_u, h_u_eq_ut, ← hsplit_0, hcov_taper]
    ring
  rw [hfin]
  exact h_strip

/-- **Coordinate mass & taper expansion for `virasoro_rosc`**:
1. Positive lobe: `|∫_0^R w_R(v) (f(v)).re dv| ≤ C c^{-4/3}`.
2. Full diameter mass vs `g_vac / (2π M)` and outer `t`-tail:
   `|∫_{-R}^R (f(x)).re dx + g_vac/(2π M) + M⁻¹ ∫_{Δ(φ(-R))}^∞ g(t) V(t) dt| ≤ C c^{-4/3}`.
3. Negative-side taper substitution:
   `|∫_0^R w_R(v) (f(-v)).re dv - M⁻¹ ∫_{Δ(0)}^{Δ(φ(-R))} lowerTaper * g(t) V(t) dt| ≤ C c^{-4/3}`. -/
theorem virasoro_rosc_mass_expansion :
    ∃ cc C : ℝ, virasoroCQEnv ≤ cc ∧ 0 ≤ C ∧
      ∀ {c T R : ℝ} {g : ℝ → ℝ}, cc ≤ c →
        virasoroProblem.IsWeaklyFeasible (c / 12) T g →
        LowerRadiusRange virasoroC1 c R →
          |∫ v in (0 : ℝ)..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re| ≤
              C * c ^ (-(4 / 3 : ℝ)) ∧
          |(∫ x in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re) +
              virasoroProblem.gVac (c / 12) g / (2 * π * virasoroProblem.cardyNorm (c / 12) g) +
              (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
                ∫ t in Ioi (virasoroDeltaChart c (virasoroPhi c ((-R : ℝ) : ℂ)).re),
                  g t * virasoroProblem.cardyV (c / 12) t| ≤
              C * c ^ (-(4 / 3 : ℝ)) ∧
          |(∫ v in (0 : ℝ)..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re) -
              (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
                ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (virasoroPhi c ((-R : ℝ) : ℂ)).re),
                  lowerTaper virasoroPhi virasoroUhat c R t * (g t * virasoroProblem.cardyV (c / 12) t)| ≤
              C * c ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨cc_h, Cφ, hcc_Q, hCφ, hHolo⟩ := lowerF_virasoro_holo_real
  obtain ⟨cc_ch, C_ch, _, hch⟩ := virasoroChart_holds
  obtain ⟨c_Q1, C_gap, κ_gap, hcQ1, hCgap, hκgap, hQ1⟩ := lemmaQ_part1
  let cc_sig : ℝ := (12 * virasoroEnvC1 + 1) ^ 6
  let α4 : ℝ := (5 / 12 : ℝ) * Real.sqrt virasoroC1
  have hc1_pos := virasoroC1_pos
  have hα4_pos : 0 < α4 := by dsimp [α4]; positivity
  let C_e4 : ℝ := (6 / 5 : ℝ) * virasoroEnvC0 * ((Nat.factorial 12 : ℝ) / α4 ^ 12)
  let cc_e4 : ℝ := (C_e4 + 1) ^ 2 + 1
  let cc_gap : ℝ := 6 * C_gap / κ_gap ^ 3 + 1
  let cc_rmin : ℝ := ((16 + 2 * (Cφ + 2) + 2) / virasoroC1 ^ 2) ^ (3 / 2 : ℝ) + 1
  let cc_strip : ℝ := (2 * betaTip * chartParams.M_ψ + 2 * Cφ + 2) ^ 3 + 1
  let cc_bv : ℝ := (2 / virasoroBV) ^ 3 + 1
  let cc : ℝ := max (max cc_h (max cc_ch c_Q1)) (max (max cc_sig cc_e4) (max (max cc_gap cc_rmin) (max cc_strip (max cc_bv 10000))))
  have hcc_Q' : virasoroCQEnv ≤ cc :=
    hcQ1.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  let C_tot : ℝ := 2 * virasoroC1 ^ (-18 : ℝ) + 2 * virasoroC1 ^ (-24 : ℝ) + 3
  refine ⟨cc, C_tot, hcc_Q', by positivity, fun {c T R g} hc hwf hR => ?_⟩
  have hcc_h : cc_h ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hcc_ch : cc_ch ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc
  have hcc_Q1 : c_Q1 ≤ c := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc
  have hcc_sig : cc_sig ≤ c := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hc
  have hcc_e4 : cc_e4 ≤ c := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hc
  have hcc_gap : cc_gap ≤ c := ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc
  have hcc_rmin : cc_rmin ≤ c := ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc
  have hcc_strip : cc_strip ≤ c := by
    dsimp [cc] at hc
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hc)))
  have hcc_bv : cc_bv ≤ c := by
    dsimp [cc] at hc
    exact le_trans (le_max_left _ 10000) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hc))))
  have hc10000 : 10000 ≤ c := by
    dsimp [cc] at hc
    exact le_trans (le_max_right _ 10000) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hc))))
  have hc0 : 0 < c := by linarith only [hc10000]
  have hc1 : 1 ≤ c := by linarith only [hc10000]
  have hc_Q : virasoroCQEnv ≤ c := hcQ1.trans hcc_Q1
  obtain ⟨⟨R', hRR', hf_diff, _, hf_real, _, hφ_real⟩, hL1⟩ := hHolo hcc_h hwf hR
  obtain ⟨hφ_diff_ball, hφ_im, hφ_bd, hφ_uhat, _⟩ := hch c hcc_ch
  obtain ⟨hM_pos, hdl_bd, _, _⟩ := hQ1 hcc_Q1 hwf
  have hc13_pos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hc23_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hc16_pos : 0 < c ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hc0 _
  -- Rate 1: `0 ≤ virasoroSigma c ≤ 1 / 2`
  have hsig_nn : 0 ≤ virasoroSigma c := virasoroSigma_nonneg hc1
  have hsig_le : virasoroSigma c ≤ 1 / 2 := by
    have h1 := log_mul_rpow_neg_le hc1 (by norm_num : (0 : ℝ) < 1 / 3)
    have h2 : virasoroSigma c ≤ (6 * virasoroEnvC1) * c ^ (-(1 / 6 : ℝ)) := by
      unfold virasoroSigma
      have h1' : c ^ (-(1 / 3 : ℝ)) * Real.log c ≤ 6 * c ^ (-(1 / 6 : ℝ)) := by norm_num at h1; exact h1
      calc virasoroEnvC1 * c ^ (-(1 / 3 : ℝ)) * Real.log c
          = virasoroEnvC1 * (c ^ (-(1 / 3 : ℝ)) * Real.log c) := by ring
        _ ≤ virasoroEnvC1 * (6 * c ^ (-(1 / 6 : ℝ))) := by gcongr; exact virasoroEnvC1_pos.le
        _ = (6 * virasoroEnvC1) * c ^ (-(1 / 6 : ℝ)) := by ring
    have hc16_ge : 12 * virasoroEnvC1 + 1 ≤ c ^ (1 / 6 : ℝ) := by
      have he1 := virasoroEnvC1_pos
      have hbase : ((12 * virasoroEnvC1 + 1 : ℝ) ^ (6 : ℕ)) ≤ c := by
        dsimp [cc_sig] at hcc_sig; exact hcc_sig
      have hpw := Real.rpow_le_rpow (by positivity) hbase (by norm_num : (0 : ℝ) ≤ 1 / 6)
      rw [← Real.rpow_natCast (12 * virasoroEnvC1 + 1) 6, ← Real.rpow_mul (by positivity)] at hpw
      norm_num at hpw; exact hpw
    have hdiv : (6 * virasoroEnvC1) * c ^ (-(1 / 6 : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, div_le_iff₀ hc16_pos]
      linarith only [hc16_ge]
    exact h2.trans hdiv
  -- Rate 2: `R` lower bounds & `Cφ * c^{-1/3} ≤ 1/2`
  have hRmin_ge : 16 + 2 * (Cφ + 2) + 2 ≤ lowerRmin virasoroC1 c := by
    have hbase : (((16 + 2 * (Cφ + 2) + 2) / virasoroC1 ^ 2) ^ (3 / 2 : ℝ)) ≤ c := by
      dsimp [cc_rmin] at hcc_rmin; linarith only [hcc_rmin]
    have hpw := Real.rpow_le_rpow (by positivity) hbase (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [← Real.rpow_mul (by positivity)] at hpw
    norm_num at hpw
    unfold lowerRmin
    calc 16 + 2 * (Cφ + 2) + 2
        = ((16 + 2 * (Cφ + 2) + 2) / virasoroC1 ^ 2) * virasoroC1 ^ 2 := by field_simp [hc1_pos.ne']
      _ ≤ c ^ (2 / 3 : ℝ) * virasoroC1 ^ 2 := by gcongr
      _ = virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by ring
  have hR_ge16 : 16 ≤ R := by linarith only [hRmin_ge, hR.1, hCφ]
  have hR0 : 0 < R := by linarith only [hR_ge16]
  have hR_le_rmax : R ≤ lowerRmax virasoroC1 c := hR.2
  have hCφ_c13 : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 := by
    have hmψ := chartParams.hMψ_nn
    have hbeta := betaTip_pos
    have hbase : ((2 * betaTip * chartParams.M_ψ + 2 * Cφ + 2 : ℝ) ^ (3 : ℕ)) ≤ c := by
      dsimp [cc_strip] at hcc_strip; linarith only [hcc_strip]
    have hpw := Real.rpow_le_rpow (by positivity) hbase (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at hpw
    norm_num at hpw
    have hbm_nn : 0 ≤ 2 * betaTip * chartParams.M_ψ :=
      mul_nonneg (mul_nonneg zero_le_two hbeta.le) hmψ
    rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, div_le_iff₀ hc13_pos]
    linarith only [hpw, hbm_nn]
  -- Rate 3: exponential rates `≤ c^{-(4/3)}`
  have hc_dl_le : C_gap * Real.exp (-κ_gap * c) ≤ c ^ (-(4 / 3 : ℝ)) := by
    have hsum := Real.sum_le_exp_of_nonneg (mul_nonneg hκgap.le hc0.le) 4
    have hterm := Finset.single_le_sum (f := fun i => (κ_gap * c) ^ i / (Nat.factorial i : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (by norm_num : 3 < 4))
    have h3 : (κ_gap * c) ^ 3 / (Nat.factorial 3 : ℝ) ≤ Real.exp (κ_gap * c) := hterm.trans hsum
    have hmul : C_gap * Real.exp (-κ_gap * c) ≤ (6 * C_gap / κ_gap ^ 3) * c ^ (-3 : ℝ) := by
      have hfac3 : (Nat.factorial 3 : ℝ) = 6 := by norm_num
      rw [hfac3, mul_pow, div_le_iff₀ (by norm_num : (0 : ℝ) < 6)] at h3
      have hinv : Real.exp (-κ_gap * c) ≤ 6 / (κ_gap ^ 3 * c ^ 3) := by
        calc Real.exp (-κ_gap * c) = (Real.exp (κ_gap * c))⁻¹ := by
              rw [show -κ_gap * c = -(κ_gap * c) by ring, Real.exp_neg]
          _ ≤ (κ_gap ^ 3 * c ^ 3 / 6)⁻¹ := inv_anti₀ (by positivity) (by linarith only [h3])
          _ = 6 / (κ_gap ^ 3 * c ^ 3) := by ring
      calc C_gap * Real.exp (-κ_gap * c)
          ≤ C_gap * (6 / (κ_gap ^ 3 * c ^ 3)) := by gcongr
        _ = (6 * C_gap / κ_gap ^ 3) * c ^ (-3 : ℝ) := by
            rw [Real.rpow_neg hc0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hccg : 6 * C_gap / κ_gap ^ 3 ≤ c := by dsimp [cc_gap] at hcc_gap; linarith only [hcc_gap]
    have hpow3 : c * c ^ (-3 : ℝ) ≤ c ^ (-(4 / 3 : ℝ)) := by
      calc c * c ^ (-3 : ℝ) = c ^ (1 : ℝ) * c ^ (-3 : ℝ) := by rw [Real.rpow_one]
        _ = c ^ (-2 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
        _ ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc C_gap * Real.exp (-κ_gap * c) ≤ (6 * C_gap / κ_gap ^ 3) * c ^ (-3 : ℝ) := hmul
      _ ≤ c * c ^ (-3 : ℝ) := by gcongr
      _ ≤ c ^ (-(4 / 3 : ℝ)) := hpow3
  have hexp_tail_le : ∀ {A : ℝ}, (1 / 2 : ℝ) * (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ) ≤ A →
      (6 / 5 : ℝ) * virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * A) ≤ c ^ (-(4 / 3 : ℝ)) := by
    intro A hA
    have hr4_eq : (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ) = Real.sqrt virasoroC1 * c ^ (1 / 6 : ℝ) := by
      unfold lowerRmin
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast virasoroC1 2, ← Real.rpow_mul hc1_pos.le,
        ← Real.rpow_mul hc0.le, Real.sqrt_eq_rpow]
      norm_num
    have h56 : α4 * c ^ (1 / 6 : ℝ) ≤ (5 / 6 : ℝ) * A := by
      dsimp [α4]
      calc (5 / 12 : ℝ) * Real.sqrt virasoroC1 * c ^ (1 / 6 : ℝ)
          = (5 / 6 : ℝ) * ((1 / 2 : ℝ) * (lowerRmin virasoroC1 c) ^ (1 / 4 : ℝ)) := by
            rw [hr4_eq]; ring
        _ ≤ (5 / 6 : ℝ) * A := by gcongr
    have harg_nn : 0 ≤ α4 * c ^ (1 / 6 : ℝ) := by positivity
    have hsum := Real.sum_le_exp_of_nonneg harg_nn 13
    have hterm := Finset.single_le_sum (f := fun i => (α4 * c ^ (1 / 6 : ℝ)) ^ i / (Nat.factorial i : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (by norm_num : 12 < 13))
    have h12 : (α4 * c ^ (1 / 6 : ℝ)) ^ 12 / (Nat.factorial 12 : ℝ) ≤ Real.exp (α4 * c ^ (1 / 6 : ℝ)) :=
      hterm.trans hsum
    have hpow12 : (c ^ (1 / 6 : ℝ)) ^ 12 = c ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hfac12_pos : (0 : ℝ) < Nat.factorial 12 := Nat.cast_pos.mpr (Nat.factorial_pos 12)
    have hexp_inv : Real.exp (-(5 / 6 : ℝ) * A) ≤ ((Nat.factorial 12 : ℝ) / α4 ^ 12) * c ^ (-2 : ℝ) := by
      have h1 : Real.exp (-(5 / 6 : ℝ) * A) ≤ Real.exp (-(α4 * c ^ (1 / 6 : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith only [h56])
      have h2 : Real.exp (-(α4 * c ^ (1 / 6 : ℝ))) ≤ (Nat.factorial 12 : ℝ) / (α4 ^ 12 * c ^ (2 : ℝ)) := by
        rw [mul_pow, hpow12] at h12
        calc Real.exp (-(α4 * c ^ (1 / 6 : ℝ))) = (Real.exp (α4 * c ^ (1 / 6 : ℝ)))⁻¹ := Real.exp_neg _
          _ ≤ ((α4 ^ 12 * c ^ (2 : ℝ)) / (Nat.factorial 12 : ℝ))⁻¹ := inv_anti₀ (by positivity) h12
          _ = (Nat.factorial 12 : ℝ) / (α4 ^ 12 * c ^ (2 : ℝ)) := by ring
      refine h1.trans (h2.trans_eq ?_)
      rw [Real.rpow_neg hc0.le]; ring
    have he0 := virasoroEnvC0_pos
    have hCe4_le : C_e4 ≤ c ^ (2 / 3 : ℝ) := by
      have hbase : ((C_e4 + 1 : ℝ) ^ (2 : ℕ)) ≤ c := by
        dsimp [cc_e4] at hcc_e4; linarith only [hcc_e4]
      have hp := Real.rpow_le_rpow (by positivity) hbase (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have hsq : C_e4 ≤ c ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)] at hp
        norm_num at hp; linarith only [hp]
      exact hsq.trans (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num))
    calc (6 / 5 : ℝ) * virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * A)
        ≤ (6 / 5 : ℝ) * virasoroEnvC0 * (((Nat.factorial 12 : ℝ) / α4 ^ 12) * c ^ (-2 : ℝ)) := by
          gcongr
      _ = C_e4 * c ^ (-2 : ℝ) := by dsimp [C_e4]; ring
      _ ≤ c ^ (2 / 3 : ℝ) * c ^ (-2 : ℝ) := by gcongr
      _ = c ^ (-(4 / 3 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
  -- Coordinate function `(virasoroPhiR c) x = (φ c x).re`
  obtain ⟨ρ, hρ_gt, hφ_d⟩ := hφ_diff_ball
  have hphiR_diff : ∀ x ∈ Icc (-R) R, HasDerivAt (virasoroPhiR c) (deriv (virasoroPhi c) (x : ℂ)).re x := fun x hx => by
    have hx_rm : |x| ≤ lowerRmax virasoroC1 c := (abs_le.mpr hx).trans hR_le_rmax
    have hd := (hφ_d.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hx_rm.trans_lt hρ_gt)))).hasDerivAt
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd.comp_ofReal
  have hphiR_cont : ContinuousOn (virasoroPhiR c) (Icc (-R) R) := fun x hx =>
    (hphiR_diff x hx).continuousAt.continuousWithinAt
  have hphiR_deriv_cont : ContinuousOn (fun x : ℝ => (deriv (virasoroPhi c) (x : ℂ)).re) (Icc (-R) R) :=
    Complex.continuous_re.comp_continuousOn
      (((hφ_d.analyticOnNhd isOpen_ball).deriv).continuousOn.comp
        Complex.continuous_ofReal.continuousOn fun x hx => mem_ball_zero_iff.mpr (by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact ((abs_le.mpr hx).trans hR_le_rmax).trans_lt hρ_gt))
  have hphiR_strictMono : StrictMonoOn (virasoroPhiR c) (Icc (-R) R) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc (-R) R) hphiR_cont fun x hx => ?_
    have hx_in : x ∈ Icc (-R) R := interior_subset hx
    rw [(hphiR_diff x hx_in).deriv]
    have hge := (hφ_real x (abs_le.mpr hx_in)).2.2.1
    linarith only [hge]
  have hA2_pos : 0 < virasoroAC c ^ 2 := by
    rw [virasoroAC_sq c hc0.le]; have := virasoroBV_pos; positivity
  have hphiR_A2 : ∀ x ∈ Icc (-R) R, |(virasoroPhiR c) x| ≤ virasoroAC c ^ 2 := fun x hx => by
    have h1 := (hφ_real x (abs_le.mpr hx)).2.1
    change |(virasoroPhi c (x : ℂ)).re| ≤ virasoroAC c ^ 2
    linarith only [h1, hA2_pos]
  have h_re_f_eq : ∀ x ∈ Icc (-R) R,
      (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re =
        (psiTilde virasoroProblem c g (((virasoroPhiR c) x : ℝ) : ℂ)).re * (deriv (virasoroPhi c) (x : ℂ)).re := by
    intro x hx
    have hx_rm : |x| ≤ lowerRmax virasoroC1 c := (abs_le.mpr hx).trans hR_le_rmax
    have himφ : (virasoroPhi c (x : ℂ)).im = 0 := hφ_im x hx_rm
    have hφ_eq : virasoroPhi c (x : ℂ) = (((virasoroPhiR c) x : ℝ) : ℂ) := Complex.ext rfl himφ
    have hψ_im : (psiTilde virasoroProblem c g (((virasoroPhiR c) x : ℝ) : ℂ)).im = 0 :=
      psiTilde_im_ofReal virasoroProblem hc0 hwf.1 (hphiR_A2 x hx)
    unfold lowerF
    rw [hφ_eq, Complex.mul_re, hψ_im, zero_mul, sub_zero]
  have hf_re_cont : ContinuousOn (fun x : ℝ => (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re)
      (Icc (-R) R) :=
    Complex.continuous_re.comp_continuousOn (hf_diff.continuousOn.comp Complex.continuous_ofReal.continuousOn
      fun x hx => mem_ball_zero_iff.mpr (by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact (abs_le.mpr hx).trans_lt hRR'))
  have hψ_re_cont_A2 : ContinuousOn (fun ut : ℝ => (psiTilde virasoroProblem c g (ut : ℂ)).re)
      (Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2)) := by
    have heq : psiTilde virasoroProblem c g = virasoroPsiTilde c g :=
      funext (psiTilde_virasoroProblem hc0.le g)
    rw [heq]
    have hc1000 : 1000 ≤ c := by linarith only [hc10000]
    exact Complex.continuous_re.comp_continuousOn
      ((virasoroPsiTilde_analyticOnNhd hc1000 hwf.1).continuousOn.comp
        Complex.continuous_ofReal.continuousOn fun ut hut =>
          virasoro_closedBall_subset_psiDom hc0 (mem_closedBall_zero_iff.mpr (by
            rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hut)))
  have hc43_nn : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  -- =====================================================================
  have hpart1 : |∫ v in (0 : ℝ)..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g (v : ℂ)).re| ≤
      (2 * virasoroC1 ^ (-18 : ℝ) + 1) * c ^ (-(4 / 3 : ℝ)) :=
    mass_exp_part1 hc0 hc1 hc10000 hc_Q hCφ hwf hR hR0 hR_ge16 hR_le_rmax hRR' hf_diff
      hf_re_cont hL1 hφ_im hφ_real hphiR_diff hphiR_deriv_cont hphiR_strictMono hphiR_A2
      hRmin_ge hCφ_c13 hsig_nn hsig_le hM_pos hexp_tail_le
  have hpart2 : |(∫ x in (-R)..R, (lowerF virasoroProblem virasoroPhi c g (x : ℂ)).re) +
        virasoroProblem.gVac (c / 12) g / (2 * π * virasoroProblem.cardyNorm (c / 12) g) +
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in Ioi (virasoroDeltaChart c (virasoroPhi c ((-R : ℝ) : ℂ)).re),
            g t * virasoroProblem.cardyV (c / 12) t| ≤
      2 * c ^ (-(4 / 3 : ℝ)) :=
    mass_exp_part2 hc0 hc10000 hc_Q hwf hR hR0 hR_ge16 hφ_real hphiR_diff
      hphiR_deriv_cont hphiR_strictMono hA2_pos hphiR_A2 h_re_f_eq hψ_re_cont_A2
      hCφ_c13 hsig_nn hsig_le hM_pos hdl_bd hc_dl_le hexp_tail_le
  have hpart3 : |(∫ v in (0 : ℝ)..R, lowerWR R v * (lowerF virasoroProblem virasoroPhi c g ((-v : ℝ) : ℂ)).re) -
        (virasoroProblem.cardyNorm (c / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c 0)..(virasoroDeltaChart c (virasoroPhi c ((-R : ℝ) : ℂ)).re),
            lowerTaper virasoroPhi virasoroUhat c R t * (g t * virasoroProblem.cardyV (c / 12) t)| ≤
      (2 * virasoroC1 ^ (-24 : ℝ)) * c ^ (-(4 / 3 : ℝ)) :=
    mass_exp_part3 hc0 hc10000 hc_Q hCφ hwf hR hR0 hR_ge16 hR_le_rmax hφ_uhat hφ_real
      hphiR_diff hphiR_deriv_cont hphiR_strictMono hA2_pos hphiR_A2 h_re_f_eq hψ_re_cont_A2
      hRmin_ge hCφ_c13 hcc_strip hcc_bv
  have h18 : 0 ≤ virasoroC1 ^ (-18 : ℝ) := by positivity
  have h24 : 0 ≤ virasoroC1 ^ (-24 : ℝ) := by positivity
  exact ⟨hpart1.trans (mul_le_mul_of_nonneg_right (by dsimp [C_tot]; linarith only [h24]) hc43_nn),
    hpart2.trans (mul_le_mul_of_nonneg_right (by dsimp [C_tot]; linarith only [h18, h24]) hc43_nn),
    hpart3.trans (mul_le_mul_of_nonneg_right (by dsimp [C_tot]; linarith only [h18]) hc43_nn)⟩

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_rosc_mass_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.virasoro_rosc_mass_expansion

end

end FormalResearch.ModularBootstrap.FiveTerm




