/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_6_1_Disc
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.ArcBounds

/-!
# Section 6.1 Shifted Test & Good-Circle Quadrature Bounds (`s4:6.1`)

Defines `spinShiftedFun`, `spinPNodes`, `spinBandB1`, `spinBandB1k`, `spinArcCov` and proves
`spinArcCov_le` and `spin_quad_arc_bound` for `2 * spinPtilde c Φ` on any good Airy circle `R`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real ENNReal Interval
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.Special

section Definitions

/-- Shifted test function `f_{k, ℓ}(u) = 2 \widetilde P(u + ℓ) (1 + u / R)^{k + 1}`. -/
noncomputable def spinShiftedFun (c : ℝ) (Φ : ℝ × ℝ → ℝ) (R ℓ : ℝ) (k : ℕ) (u : ℂ) : ℂ :=
  ((2 : ℝ) : ℂ) * spinPtilde c Φ (u + (ℓ : ℂ)) * (1 + u / (R : ℂ)) ^ (k + 1)

/-- Finite Airy-node sum `P_nodes` for `spinShiftedFun`. -/
noncomputable def spinPNodes (c : ℝ) (Φ : ℝ × ℝ → ℝ) (R ℓ : ℝ) (k N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    (spinShiftedFun c Φ R ℓ k (airyZero m : ℂ)).re / airyAi' (airyZero m) ^ 2

/-- Weighted first-band integral `B₁` for `2 * spinPtilde c Φ` on `[-R, u_T]`. -/
noncomputable def spinBandB1 (c : ℝ) (Φ : ℝ × ℝ → ℝ) (R u_T : ℝ) : ℝ :=
  ∫ u in (-R)..u_T, ((-u) / R) * (((2 : ℝ) : ℂ) * spinPtilde c Φ (u : ℂ)).re

/-- Truncated first-band moment `B₁^{(k)}` on `[-R, u_T]`. -/
noncomputable def spinBandB1k (c : ℝ) (Φ : ℝ × ℝ → ℝ) (R u_T : ℝ) (k : ℕ) : ℝ :=
  ∫ u in (-R)..u_T,
    min 1 (((k : ℝ) + 1) * (-u) / R) * (((2 : ℝ) : ℂ) * spinPtilde c Φ (u : ℂ)).re

/-- Covered-arc factor `C_a(C_env)` in `BootstrapWeakCore.hArc_cov`. -/
noncomputable def spinArcCovConst (C_env : ℝ) : ℝ :=
  15 * √π * 4 * (√2 * (π / 2) * √(π / 2) * C_env)

lemma spinArcCovConst_pos {C_env : ℝ} (hC : 0 < C_env) : 0 < spinArcCovConst C_env := by
  unfold spinArcCovConst; positivity

/-- Uncovered-wedge factor `C_unc(C_env)` in `BootstrapWeakCore.hArc_unc`. -/
noncomputable def spinArcUncConst (C_env : ℝ) : ℝ :=
  15 * √π * 8 * √2 * C_env * Real.exp 1 * (3 * π) ^ (6 : ℕ)

lemma spinArcUncConst_pos {C_env : ℝ} (hC : 0 < C_env) : 0 < spinArcUncConst C_env := by
  unfold spinArcUncConst; positivity

/-- Covered-arc integral piece `Arc_cov k ℓ`. -/
noncomputable def spinArcCov (C_env R L' ℓ : ℝ) (k : ℕ) : ℝ :=
  15 * √π * R * ∫ θ in (-π)..π,
    ((√2 * (π / 2) * √(π / 2) * C_env) * L' * (√R) ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)) *
      ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) *
      Real.exp (-(4 * ℓ * √R / π) * ((π - |θ|) / 2))

end Definitions

section QuadratureAndArc

lemma spinArcCov_le {C_env R L' ℓ : ℝ} (hC : 0 ≤ C_env) (hR : 10 ≤ R) (hL' : 0 ≤ L')
    (hℓ : 0 < ℓ) {k : ℕ} (hk5 : 5 ≤ k) :
    spinArcCov C_env R L' ℓ k ≤
      spinArcCovConst C_env * L' * (√R)⁻¹ *
        ((2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) *
          (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2)) := by
  unfold spinArcCov
  set a : ℝ := √R
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by linarith only [hR])
  have ha_sq : a ^ 2 = R := Real.sq_sqrt (by linarith only [hR])
  set s : ℝ := 4 * ℓ * a / π
  have hs_pos : 0 < s := by dsimp [s]; positivity
  set M_c : ℝ := (√2 * (π / 2) * √(π / 2) * C_env) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)
  have hM_nn : 0 ≤ M_c := by dsimp [M_c]; positivity
  let F : ℝ → ℝ := fun θ => M_c * ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * ((π - |θ|) / 2))
  have hF_even : ∀ θ : ℝ, F (-θ) = F θ := fun θ => by simp [F, abs_neg]
  have hk_half_pos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by
    have : (5 : ℝ) ≤ k := by exact_mod_cast hk5
    linarith only [this]
  have hF_cont : ContinuousOn F (Icc (-π) π) := fun θ _ =>
    Continuous.continuousWithinAt <|
      (continuous_const.mul ((Continuous.rpow_const ((continuous_const.sub continuous_abs).div_const 2)
        (fun _ => Or.inr hk_half_pos.le)))).mul
      (Real.continuous_exp.comp (continuous_const.mul ((continuous_const.sub continuous_abs).div_const 2)))
  have h_symm : ∫ θ in (-π)..π, F θ = 2 * ∫ θ in (0 : ℝ)..π, F θ := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((hF_cont.mono (Icc_subset_Icc_right Real.pi_pos.le)).intervalIntegrable_of_Icc (μ := volume)
        (by linarith only [Real.pi_pos]))
      ((hF_cont.mono (Icc_subset_Icc_left (by linarith only [Real.pi_pos]))).intervalIntegrable_of_Icc
        (μ := volume) Real.pi_pos.le)
    have hneg : ∫ θ in (-π)..(0 : ℝ), F θ = ∫ θ in (0 : ℝ)..π, F θ := by
      have hcomp := intervalIntegral.integral_comp_neg F (a := 0) (b := π)
      simp only [neg_zero] at hcomp
      rw [← hcomp]
      exact intervalIntegral.integral_congr fun θ _ => hF_even θ
    linarith only [hsplit, hneg]
  have h0_pi_eq : ∫ θ in (0 : ℝ)..π, F θ =
      2 * ∫ t in (0 : ℝ)..(π / 2), M_c * t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t) := by
    have h_sub : ∫ t in (0 : ℝ)..(π / 2), F (π - 2 * t) = (1 / 2 : ℝ) * ∫ θ in (0 : ℝ)..π, F θ := by
      have hm := intervalIntegral.integral_comp_mul_left (fun u => F (π - u)) (c := (2 : ℝ))
        two_ne_zero (a := 0) (b := π / 2)
      simp only [mul_zero, smul_eq_mul, show (2 : ℝ) * (π / 2) = π by ring] at hm
      have h2 := intervalIntegral.integral_comp_sub_left F π (a := 0) (b := π)
      simp only [sub_zero, sub_self] at h2
      rw [h2] at hm
      linarith only [hm]
    have h_congr : ∫ t in (0 : ℝ)..(π / 2), F (π - 2 * t) =
        ∫ t in (0 : ℝ)..(π / 2), M_c * t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ π / 2)] at ht
      have h_abs : |π - 2 * t| = π - 2 * t := abs_of_nonneg (by linarith only [ht.2])
      simp only [F, h_abs, show (π - (π - 2 * t)) / 2 = t by ring]
    linarith only [h_sub, h_congr]
  have h_tail_le : ∫ t in (0 : ℝ)..(π / 2), M_c * t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t) ≤
      M_c * ∫ t in Ioi (0 : ℝ), t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t) := by
    have hg := Real.GammaIntegral_convergent (s := (k : ℝ) + 1 / 2) (by positivity)
    have h1 : Integrable ((Ioi (0 : ℝ)).indicator (fun x : ℝ => Real.exp (-x) * x ^ ((k : ℝ) + 1 / 2 - 1))) volume :=
      (integrable_indicator_iff measurableSet_Ioi).mpr hg
    have h2 := h1.comp_mul_left' hs_pos.ne'
    have h_ind : (fun t : ℝ =>
        (Ioi (0 : ℝ)).indicator (fun x : ℝ => Real.exp (-x) * x ^ ((k : ℝ) + 1 / 2 - 1)) (s * t)) =
        (Ioi (0 : ℝ)).indicator (fun t : ℝ => (s * t) ^ ((k : ℝ) + 1 / 2 - 1) * Real.exp (-(s * t))) := by
      ext t
      by_cases ht : 0 < t
      · simp [Set.indicator_of_mem, Set.mem_Ioi, ht, hs_pos, mul_comm]
      · have hst : ¬ (0 < s * t) := fun h => ht (pos_of_mul_pos_right h hs_pos.le)
        simp [Set.indicator_of_notMem, Set.mem_Ioi, ht, hst]
    have h3 : IntegrableOn (fun t : ℝ => (s * t) ^ ((k : ℝ) + 1 / 2 - 1) * Real.exp (-(s * t))) (Ioi 0) :=
      (integrable_indicator_iff measurableSet_Ioi).mp (h_ind ▸ h2)
    have hint_Ioi : IntegrableOn (fun t : ℝ => t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t)) (Ioi 0) := by
      refine IntegrableOn.congr_fun (Integrable.const_mul h3 (s ^ (-((k : ℝ) - 1 / 2))))
        (fun t ht => ?_) measurableSet_Ioi
      rw [Set.mem_Ioi] at ht
      rw [show (k : ℝ) + 1 / 2 - 1 = (k : ℝ) - 1 / 2 by ring, Real.mul_rpow hs_pos.le ht.le,
        show -(s * t) = -s * t by ring, Real.rpow_neg hs_pos.le]
      field_simp [(Real.rpow_pos_of_pos hs_pos _).ne']
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2), ← integral_const_mul]
    have h_eq_fn : (fun t : ℝ => M_c * t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t)) =
        (fun t : ℝ => M_c * (t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t))) := by ext t; ring
    rw [h_eq_fn]
    refine setIntegral_mono_set (hint_Ioi.const_mul M_c) ?_
      (Eventually.of_forall fun _ ht => Ioc_subset_Ioi_self ht)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hM_nn (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
  have h_gam := integral_Ioi_rpow_mul_exp_neg hs_pos k
  have hs_inv : s ^ (-((k : ℝ) + 1 / 2)) = (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2) := by
    have hs_eq : s⁻¹ = π / (4 * ℓ * a) := by dsimp [s]; field_simp
    rw [Real.rpow_neg hs_pos.le, ← Real.inv_rpow hs_pos.le, hs_eq]
  have h_int_le : ∫ θ in (-π)..π, F θ ≤
      4 * M_c * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2) := by
    rw [h_symm, h0_pi_eq]
    calc 2 * (2 * ∫ t in (0 : ℝ)..(π / 2), M_c * t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t))
        = 4 * ∫ t in (0 : ℝ)..(π / 2), M_c * t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t) := by ring
      _ ≤ 4 * (M_c * ∫ t in Ioi (0 : ℝ), t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t)) := by gcongr
      _ = 4 * M_c * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2) := by
          rw [h_gam, hs_inv]; ring
  have ha_pow : R * a ^ (-(3 : ℤ)) = a⁻¹ := by
    rw [← ha_sq, zpow_neg, show (3 : ℤ) = (3 : ℕ) by rfl, zpow_natCast]
    field_simp [ha_pos.ne']
  calc 15 * √π * R * ∫ θ in (-π)..π, F θ
      ≤ 15 * √π * R * (4 * M_c * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2)) := by
        gcongr
    _ = spinArcCovConst C_env * L' * (R * a ^ (-(3 : ℤ))) *
          ((2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2)) := by
        unfold spinArcCovConst; dsimp [M_c]; ring
    _ = spinArcCovConst C_env * L' * a⁻¹ *
          ((2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2)) := by
        rw [ha_pow]

private lemma spin_quad_cov_pt {c R ℓ C_env ς L_exp θ : ℝ}
    {Φ : ℝ × ℝ → ℝ}
    (hC_pos : 0 < C_env) (hς_nn : 0 ≤ ς)
    (hR_10 : 10 ≤ R) (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    (hL_exp : Real.exp (ς * (√R + 1)) ≤ L_exp)
    (hEnv : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ R + 1 → 0 < (u ^ (1 / 2 : ℂ)).re →
      ‖((2 : ℝ) : ℂ) * spinPtilde c Φ u‖ ≤
        C_env * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹)
    {k : ℕ} (_hk5 : 5 ≤ k) (hθ : θ ∈ Icc (-π) π) (h_abs_lt : |θ| < π) :
    ‖spinShiftedFun c Φ R ℓ k (circleMap 0 R θ)‖ ≤
      ((√2 * (π / 2) * √(π / 2) * C_env) * (√R * L_exp) * (√R) ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1) *
        ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) *
        Real.exp (-(4 * ℓ * √R / π) * ((π - |θ|) / 2))) *
      airyEnv (circleMap 0 R θ) := by
  set a : ℝ := √R
  have hR_pos : 0 < R := by linarith only [hR_10]
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hR_pos
  have ha_sq : a ^ 2 = R := Real.sq_sqrt hR_pos.le
  have hθ_Ioo : θ ∈ Ioo (-π) π := abs_lt.mp h_abs_lt
  have hnorm_w : ‖circleMap 0 R θ‖ = R := by simp [norm_circleMap_zero, abs_of_pos hR_pos]
  have h1w : ‖1 + circleMap 0 R θ / (R : ℂ)‖ = 2 * Real.cos (θ / 2) :=
    norm_one_add_circleMap_div hR_pos hθ
  have hcos_nn : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hθ.1], by linarith only [hθ.2]⟩
  have hw_slit : circleMap 0 R θ ∈ Complex.slitPlane := circleMap_mem_slitPlane' hR_pos hθ_Ioo
  have h_re_w : (circleMap 0 R θ ^ (1 / 2 : ℂ)).re = a * Real.cos (θ / 2) :=
    re_cpow_half_circleMap hR_pos hθ_Ioo
  have h_cos_bounds : (π - |θ|) / π ≤ Real.cos (θ / 2) ∧ Real.cos (θ / 2) ≤ (π - |θ|) / 2 := by
    have hcos_eq : Real.cos (θ / 2) = Real.sin ((π - |θ|) / 2) := by
      rw [← Real.cos_abs (θ / 2), abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2),
        ← Real.sin_pi_div_two_sub]
      congr 1; ring
    rw [hcos_eq]
    have hx0 : 0 ≤ (π - |θ|) / 2 := by linarith only [h_abs_lt]
    have hxpi2 : (π - |θ|) / 2 ≤ π / 2 := by linarith only [abs_nonneg θ]
    refine ⟨?_, Real.sin_le hx0⟩
    calc (π - |θ|) / π = (2 / π) * ((π - |θ|) / 2) := by ring
      _ ≤ Real.sin ((π - |θ|) / 2) := Real.mul_le_sin hx0 hxpi2
  set t : ℝ := (π - |θ|) / 2
  have ht_pos : 0 < t := by dsimp [t]; linarith only [h_abs_lt]
  have ht_ub : t ≤ π / 2 := by dsimp [t]; linarith only [abs_nonneg θ]
  have hcos_lb : (2 / π) * t ≤ Real.cos (θ / 2) := by
    calc (2 / π) * t = (π - |θ|) / π := by dsimp [t]; ring
      _ ≤ Real.cos (θ / 2) := h_cos_bounds.1
  have hcos_pos : 0 < Real.cos (θ / 2) := lt_of_lt_of_le (by positivity) hcos_lb
  set u : ℂ := circleMap 0 R θ + (ℓ : ℂ)
  have hu_slit : u ∈ Complex.slitPlane := not_nonpos_add_ofReal hw_slit hℓ_nn
  have hu_ne : u ≠ 0 := Complex.slitPlane_ne_zero hu_slit
  have hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re := re_cpow_half_pos_of_slit hu_slit
  have hu_norm_lo : R / 2 ≤ ‖u‖ := by
    have hsub := norm_sub_le (circleMap 0 R θ + (ℓ : ℂ)) (ℓ : ℂ)
    rw [add_sub_cancel_right, hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ_nn] at hsub
    linarith only [hsub, hR_10, hℓ_half]
  have hu_norm_hi : ‖u‖ ≤ R + 1 := by
    calc ‖u‖ ≤ ‖circleMap 0 R θ‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
      _ = R + ℓ := by rw [hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ_nn]
      _ ≤ R + 1 := by linarith only [hℓ_half]
  have h_re_shift := re_cpow_half_add_real_bounds hw_slit hℓ_nn
  rw [h_re_w] at h_re_shift
  have h_env_shift : airyEnv u ≤ airyEnv (circleMap 0 R θ) * Real.exp (-(4 * ℓ * a / π) * t) := by
    have h1 : airyEnv u ≤ airyEnv (circleMap 0 R θ) * Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) :=
      (airyEnv_add_real_le hw_slit hℓ_nn).trans_eq (by rw [h_re_w])
    have hexp_le : -2 * ℓ * (a * Real.cos (θ / 2)) ≤ -(4 * ℓ * a / π) * t := by
      have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcos_lb ha_pos.le)
        (mul_nonneg two_pos.le hℓ_nn)
      linarith only [hmul, show 2 * ℓ * (a * (2 / π * t)) = (4 * ℓ * a / π) * t by ring]
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (airyEnv_pos _).le)
  have hexp_ς : Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) ≤ L_exp := by
    have hcos_le1 : Real.cos (θ / 2) ≤ 1 := Real.cos_le_one _
    have hℓ1 : √ℓ ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith only [hℓ_half])
    have hre_ub : (u ^ (1 / 2 : ℂ)).re ≤ a + 1 := by
      have h_acos : a * Real.cos (θ / 2) ≤ a := mul_le_of_le_one_right ha_pos.le hcos_le1
      linarith only [h_re_shift.2, h_acos, hℓ1]
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hre_ub hς_nn)).trans hL_exp
  have hu_norm_nh : ‖u‖ ^ (-(1 / 2 : ℝ)) ≤ √2 * a⁻¹ := by
    have h1 : (R / 2) ^ (-(1 / 2 : ℝ)) = √2 * a⁻¹ := by
      rw [← ha_sq, div_eq_mul_inv, Real.mul_rpow (sq_nonneg a) (by norm_num),
        ← Real.rpow_natCast a 2, ← Real.rpow_mul ha_pos.le,
        show ((2 : ℕ) : ℝ) * -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one,
        Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv, ← Real.sqrt_eq_rpow]
      ring
    exact (Real.rpow_le_rpow_of_nonpos (by positivity) hu_norm_lo (by norm_num)).trans_eq h1
  have hu_re_inv : ((u ^ (1 / 2 : ℂ)).re)⁻¹ ≤ (π / 2) * a⁻¹ * t⁻¹ := by
    have h_low : (2 / π) * a * t ≤ (u ^ (1 / 2 : ℂ)).re := by
      have h1 := mul_le_mul_of_nonneg_left hcos_lb ha_pos.le
      linarith only [h_re_shift.1, h1, show a * (2 / π * t) = 2 / π * a * t by ring]
    have hinv := inv_anti₀ (by positivity : 0 < (2 / π) * a * t) h_low
    refine hinv.trans_eq ?_
    field_simp [Real.pi_pos.ne', ha_pos.ne', ht_pos.ne']
  have h1w_le : (2 * Real.cos (θ / 2)) ^ (k + 1) ≤ (2 : ℝ) ^ (k + 1) * t ^ (k + 1) := by
    rw [show (2 : ℝ) ^ (k + 1) * t ^ (k + 1) = (2 * t) ^ (k + 1) by ring]
    exact pow_le_pow_left₀ (mul_nonneg two_pos.le hcos_nn) (by linarith only [h_cos_bounds.2]) _
  have ht_pow_le : t ^ (k + 1) * t⁻¹ ≤ √(π / 2) * t ^ ((k : ℝ) - 1 / 2) := by
    have h_k1 : t ^ (k + 1) * t⁻¹ = t ^ ((k : ℝ) - 1 / 2) * √t := by
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ ht_pos.ne', mul_one,
        ← Real.rpow_natCast t k, Real.sqrt_eq_rpow, ← Real.rpow_add ht_pos,
        show (k : ℝ) - 1 / 2 + 1 / 2 = (k : ℝ) by ring]
    rw [h_k1, mul_comm √(π / 2)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht_ub) (Real.rpow_nonneg ht_pos.le _)
  have ha_pow : a * a ^ (-(3 : ℤ)) = a⁻¹ * a⁻¹ := by
    rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) by rfl, zpow_natCast]
    field_simp [ha_pos.ne']
  have he_nn : 0 ≤ airyEnv (circleMap 0 R θ) := (airyEnv_pos _).le
  have hL_nn : 0 ≤ L_exp := (Real.exp_pos _).le.trans hL_exp
  have hΨ_u := hEnv u hu_ne hu_norm_hi hu_re_pos
  have h_prod : ‖((2 : ℝ) : ℂ) * spinPtilde c Φ u‖ ≤
      C_env * (airyEnv (circleMap 0 R θ) * Real.exp (-(4 * ℓ * a / π) * t)) * L_exp *
        (√2 * a⁻¹) * ((π / 2) * a⁻¹ * t⁻¹) :=
    hΨ_u.trans <| mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h_env_shift hC_pos.le)
      hexp_ς (Real.exp_pos _).le (mul_nonneg hC_pos.le (mul_nonneg he_nn (Real.exp_pos _).le)))
      hu_norm_nh (Real.rpow_nonneg (norm_nonneg _) _) (by positivity [he_nn, hL_nn]))
      hu_re_inv (inv_nonneg.mpr hu_re_pos.le) (by positivity [he_nn, hL_nn])
  dsimp [spinShiftedFun]
  rw [norm_mul, norm_pow, h1w]
  have ha3_nn : 0 ≤ a * a ^ (-(3 : ℤ)) :=
    ha_pow ▸ mul_nonneg (inv_nonneg.mpr ha_pos.le) (inv_nonneg.mpr ha_pos.le)
  have h_mid : ((√2 * (π / 2) * C_env) * L_exp * (a⁻¹ * a⁻¹) * (2 : ℝ) ^ (k + 1) *
        (t ^ (k + 1) * t⁻¹) * Real.exp (-(4 * ℓ * a / π) * t)) * airyEnv (circleMap 0 R θ) ≤
      ((√2 * (π / 2) * C_env) * L_exp * (a * a ^ (-(3 : ℤ))) * (2 : ℝ) ^ (k + 1) *
        (√(π / 2) * t ^ ((k : ℝ) - 1 / 2)) * Real.exp (-(4 * ℓ * a / π) * t)) *
        airyEnv (circleMap 0 R θ) := by
    rw [← ha_pow]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le) he_nn
    exact mul_le_mul_of_nonneg_left ht_pow_le (by positivity [hL_nn, ha3_nn])
  calc ‖((2 : ℝ) : ℂ) * spinPtilde c Φ u‖ * (2 * Real.cos (θ / 2)) ^ (k + 1)
      ≤ (C_env * (airyEnv (circleMap 0 R θ) * Real.exp (-(4 * ℓ * a / π) * t)) * L_exp *
          (√2 * a⁻¹) * ((π / 2) * a⁻¹ * t⁻¹)) * ((2 : ℝ) ^ (k + 1) * t ^ (k + 1)) :=
        mul_le_mul h_prod h1w_le (pow_nonneg (mul_nonneg two_pos.le hcos_nn) _) (by positivity [he_nn, hL_nn])
    _ = ((√2 * (π / 2) * C_env) * L_exp * (a⁻¹ * a⁻¹) * (2 : ℝ) ^ (k + 1) *
          (t ^ (k + 1) * t⁻¹) * Real.exp (-(4 * ℓ * a / π) * t)) * airyEnv (circleMap 0 R θ) := by ring
    _ ≤ ((√2 * (π / 2) * C_env) * L_exp * (a * a ^ (-(3 : ℤ))) * (2 : ℝ) ^ (k + 1) *
          (√(π / 2) * t ^ ((k : ℝ) - 1 / 2)) * Real.exp (-(4 * ℓ * a / π) * t)) *
          airyEnv (circleMap 0 R θ) := h_mid
    _ = ((√2 * (π / 2) * √(π / 2) * C_env) * (a * L_exp) * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1) *
          t ^ ((k : ℝ) - 1 / 2) * Real.exp (-(4 * ℓ * a / π) * t)) * airyEnv (circleMap 0 R θ) := by ring

private lemma spin_quad_unc_pt {c R ℓ C_env ς n θ : ℝ}
    {Φ : ℝ × ℝ → ℝ}
    (hC_pos : 0 < C_env) (hς_nn : 0 ≤ ς) (hn_pos : 0 < n)
    (hς_unc : ς * (3 * π * √R * n ^ (-(1 / 12 : ℝ)) + 1) ≤ 1)
    (hR_10 : 10 ≤ R) (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    (hEnv : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ R + 1 → 0 < (u ^ (1 / 2 : ℂ)).re →
      ‖((2 : ℝ) : ℂ) * spinPtilde c Φ u‖ ≤
        C_env * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹)
    (k : ℕ) (hθ : θ ∈ Icc (-π) π) (h_abs_lt : |θ| < π)
    (hunc : π - 3 * π * n ^ (-(1 / 12 : ℝ)) < |θ|) :
    ‖spinShiftedFun c Φ R ℓ k (circleMap 0 R θ)‖ ≤
      ((2 * √2 * C_env * Real.exp 1) * (√R) ^ (-(2 : ℤ)) * (3 * π * n ^ (-(1 / 12 : ℝ))) ^ k) *
      airyEnv (circleMap 0 R θ) := by
  set a : ℝ := √R
  have hR_pos : 0 < R := by linarith only [hR_10]
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hR_pos
  have ha_sq : a ^ 2 = R := Real.sq_sqrt hR_pos.le
  set δ₀ : ℝ := 3 * π * n ^ (-(1 / 12 : ℝ))
  have hθ_Ioo : θ ∈ Ioo (-π) π := abs_lt.mp h_abs_lt
  have hnorm_w : ‖circleMap 0 R θ‖ = R := by simp [norm_circleMap_zero, abs_of_pos hR_pos]
  have h1w : ‖1 + circleMap 0 R θ / (R : ℂ)‖ = 2 * Real.cos (θ / 2) :=
    norm_one_add_circleMap_div hR_pos hθ
  have hcos_nn : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hθ.1], by linarith only [hθ.2]⟩
  have hw_slit : circleMap 0 R θ ∈ Complex.slitPlane := circleMap_mem_slitPlane' hR_pos hθ_Ioo
  have h_re_w : (circleMap 0 R θ ^ (1 / 2 : ℂ)).re = a * Real.cos (θ / 2) :=
    re_cpow_half_circleMap hR_pos hθ_Ioo
  have h_cos_bounds : (π - |θ|) / π ≤ Real.cos (θ / 2) ∧ Real.cos (θ / 2) ≤ (π - |θ|) / 2 := by
    have hcos_eq : Real.cos (θ / 2) = Real.sin ((π - |θ|) / 2) := by
      rw [← Real.cos_abs (θ / 2), abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2),
        ← Real.sin_pi_div_two_sub]
      congr 1; ring
    rw [hcos_eq]
    have hx0 : 0 ≤ (π - |θ|) / 2 := by linarith only [h_abs_lt]
    have hxpi2 : (π - |θ|) / 2 ≤ π / 2 := by linarith only [abs_nonneg θ]
    refine ⟨?_, Real.sin_le hx0⟩
    calc (π - |θ|) / π = (2 / π) * ((π - |θ|) / 2) := by ring
      _ ≤ Real.sin ((π - |θ|) / 2) := Real.mul_le_sin hx0 hxpi2
  have hcos_ub : Real.cos (θ / 2) ≤ δ₀ / 2 := h_cos_bounds.2.trans (by dsimp [δ₀]; linarith only [hunc])
  have hcos_pos : 0 < Real.cos (θ / 2) :=
    lt_of_lt_of_le (div_pos (by linarith only [h_abs_lt]) Real.pi_pos) h_cos_bounds.1
  set u : ℂ := circleMap 0 R θ + (ℓ : ℂ)
  have hu_slit : u ∈ Complex.slitPlane := not_nonpos_add_ofReal hw_slit hℓ_nn
  have hu_ne : u ≠ 0 := Complex.slitPlane_ne_zero hu_slit
  have hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re := re_cpow_half_pos_of_slit hu_slit
  have hu_norm_lo : R / 2 ≤ ‖u‖ := by
    have hsub := norm_sub_le (circleMap 0 R θ + (ℓ : ℂ)) (ℓ : ℂ)
    rw [add_sub_cancel_right, hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ_nn] at hsub
    linarith only [hsub, hR_10, hℓ_half]
  have hu_norm_hi : ‖u‖ ≤ R + 1 := by
    calc ‖u‖ ≤ ‖circleMap 0 R θ‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
      _ = R + ℓ := by rw [hnorm_w, Complex.norm_real, Real.norm_of_nonneg hℓ_nn]
      _ ≤ R + 1 := by linarith only [hℓ_half]
  have h_re_shift := re_cpow_half_add_real_bounds hw_slit hℓ_nn
  rw [h_re_w] at h_re_shift
  have h_env_le : airyEnv u ≤ airyEnv (circleMap 0 R θ) := by
    have h1 := (airyEnv_add_real_le hw_slit hℓ_nn).trans_eq (by rw [h_re_w])
    have hexp_le1 : Real.exp (-2 * ℓ * (a * Real.cos (θ / 2))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ 2 * ℓ * (a * Real.cos (θ / 2)) :=
        mul_nonneg (mul_nonneg two_pos.le hℓ_nn) (mul_nonneg ha_pos.le hcos_nn)
      linarith only [this]
    exact h1.trans (by simpa using mul_le_mul_of_nonneg_left hexp_le1 (airyEnv_pos _).le)
  have h_exp_ς : ς * (u ^ (1 / 2 : ℂ)).re ≤ 1 := by
    have hℓ1 : √ℓ ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith only [hℓ_half])
    have ha_δ : a * (δ₀ / 2) ≤ 3 * π * a * n ^ (-(1 / 12 : ℝ)) := by
      have hnn : 0 ≤ π * a * n ^ (-(1 / 12 : ℝ)) := by positivity
      dsimp [δ₀]; linarith only [hnn]
    have ha_cos := mul_le_mul_of_nonneg_left hcos_ub ha_pos.le
    have hre_le : (u ^ (1 / 2 : ℂ)).re ≤ 3 * π * a * n ^ (-(1 / 12 : ℝ)) + 1 := by
      linarith only [h_re_shift.2, ha_cos, ha_δ, hℓ1]
    exact (mul_le_mul_of_nonneg_left hre_le hς_nn).trans hς_unc
  have hu_norm_nh : ‖u‖ ^ (-(1 / 2 : ℝ)) ≤ √2 * a⁻¹ := by
    have h1 : (R / 2) ^ (-(1 / 2 : ℝ)) = √2 * a⁻¹ := by
      rw [← ha_sq, div_eq_mul_inv, Real.mul_rpow (sq_nonneg a) (by norm_num),
        ← Real.rpow_natCast a 2, ← Real.rpow_mul ha_pos.le,
        show ((2 : ℕ) : ℝ) * -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one,
        Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv, ← Real.sqrt_eq_rpow]
      ring
    exact (Real.rpow_le_rpow_of_nonpos (by positivity) hu_norm_lo (by norm_num)).trans_eq h1
  have hu_re_inv : ((u ^ (1 / 2 : ℂ)).re)⁻¹ ≤ (a * Real.cos (θ / 2))⁻¹ :=
    inv_anti₀ (mul_pos ha_pos hcos_pos) h_re_shift.1
  have h_2cos_le : (2 * Real.cos (θ / 2)) ^ k ≤ δ₀ ^ k :=
    pow_le_pow_left₀ (mul_nonneg two_pos.le hcos_nn) (by linarith only [hcos_ub]) k
  have ha_inv_sq : a⁻¹ * a⁻¹ = a ^ (-(2 : ℤ)) := by
    rw [zpow_neg, show (2 : ℤ) = (2 : ℕ) by rfl, zpow_natCast]; ring
  have he_nn : 0 ≤ airyEnv (circleMap 0 R θ) := (airyEnv_pos _).le
  have hΨ_u := hEnv u hu_ne hu_norm_hi hu_re_pos
  have h_prod : ‖((2 : ℝ) : ℂ) * spinPtilde c Φ u‖ ≤
      C_env * airyEnv (circleMap 0 R θ) * Real.exp 1 * (√2 * a⁻¹) * (a * Real.cos (θ / 2))⁻¹ :=
    hΨ_u.trans <| mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h_env_le hC_pos.le)
      (Real.exp_le_exp.mpr h_exp_ς) (Real.exp_pos _).le (mul_nonneg hC_pos.le he_nn))
      hu_norm_nh (Real.rpow_nonneg (norm_nonneg _) _) (by positivity [he_nn]))
      hu_re_inv (inv_nonneg.mpr hu_re_pos.le) (by positivity [he_nn])
  dsimp [spinShiftedFun]
  rw [norm_mul, norm_pow, h1w]
  calc ‖((2 : ℝ) : ℂ) * spinPtilde c Φ u‖ * (2 * Real.cos (θ / 2)) ^ (k + 1)
      ≤ (C_env * airyEnv (circleMap 0 R θ) * Real.exp 1 * (√2 * a⁻¹) * (a * Real.cos (θ / 2))⁻¹) *
          (2 * Real.cos (θ / 2) * δ₀ ^ k) := by
        refine mul_le_mul h_prod ?_ (pow_nonneg (mul_nonneg two_pos.le hcos_nn) _) (by positivity [he_nn])
        rw [pow_succ']; exact mul_le_mul_of_nonneg_left h_2cos_le (mul_nonneg two_pos.le hcos_nn)
    _ = ((2 * √2 * C_env * Real.exp 1) * (a⁻¹ * a⁻¹) * δ₀ ^ k) * airyEnv (circleMap 0 R θ) := by
        field_simp [ha_pos.ne', hcos_pos.ne']
    _ = ((2 * √2 * C_env * Real.exp 1) * a ^ (-(2 : ℤ)) * δ₀ ^ k) * airyEnv (circleMap 0 R θ) := by
        rw [ha_inv_sq]

lemma spin_quad_arc_bound {c R ℓ C_env ς L_exp n r_d_dom : ℝ} {N : ℕ}
    {Φ : ℝ × ℝ → ℝ}
    (hC_pos : 0 < C_env) (hς_nn : 0 ≤ ς) (hn_ge : (3 * π) ^ (12 : ℕ) ≤ n)
    (hς_unc : ς * (3 * π * √R * n ^ (-(1 / 12 : ℝ)) + 1) ≤ 1)
    (hR_10 : 10 ≤ R) (hR_an : R + 1 < r_d_dom)
    (hAn : AnalyticOnNhd ℂ (spinPtilde c Φ) (ball (0 : ℂ) r_d_dom))
    (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    (hL_exp : Real.exp (ς * (√R + 1)) ≤ L_exp)
    (hEnv : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ R + 1 → 0 < (u ^ (1 / 2 : ℂ)).re →
      ‖((2 : ℝ) : ℂ) * spinPtilde c Φ u‖ ≤
        C_env * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹)
    (hD : CftCircleData airyAiC (fun m => (airyZero m : ℂ)) (Finset.Icc 1 N) R)
    (hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖(airyBiC w - I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π)
    (hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖(airyBiC w + I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π)
    {k : ℕ} (hk5 : 5 ≤ k) :
    spinPNodes c Φ R ℓ k N ≤
      (∫ x in (-R)..R, (spinShiftedFun c Φ R ℓ k (x : ℂ)).re) +
        spinArcCov C_env R (√R * L_exp) ℓ k + spinArcUncConst C_env * n ^ (-(3 / 8 : ℝ)) := by
  have hn_pos : 0 < n := lt_of_lt_of_le (by positivity) hn_ge
  have hR_pos : 0 < R := by linarith only [hR_10]
  set a : ℝ := √R
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hR_pos
  have ha_sq : a ^ 2 = R := Real.sq_sqrt hR_pos.le
  set f := spinShiftedFun c Φ R ℓ k
  have hf_diff : DifferentiableOn ℂ f (ball (0 : ℂ) (R + 1 / 3)) := fun u hu => by
    have hu_shift : u + (ℓ : ℂ) ∈ ball (0 : ℂ) r_d_dom := by
      rw [mem_ball_zero_iff] at hu ⊢
      calc ‖u + (ℓ : ℂ)‖ ≤ ‖u‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
        _ ≤ (R + 1 / 3) + ℓ := by
            rw [Complex.norm_real, Real.norm_of_nonneg hℓ_nn]; linarith only [hu]
        _ ≤ R + 1 := by linarith only [hℓ_half]
        _ < r_d_dom := hR_an
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((2 : ℝ) : ℂ) * spinPtilde c Φ (z + (ℓ : ℂ))) u :=
      (differentiableAt_const _).mul
        ((hAn _ hu_shift).differentiableAt.comp u ((differentiableAt_id).add (differentiableAt_const _)))
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (1 + z / (R : ℂ)) ^ (k + 1)) u :=
      ((differentiableAt_const _).add (differentiableAt_id.div_const _)).pow _
    exact (h1.mul h2).differentiableWithinAt
  set δ₀ : ℝ := 3 * π * n ^ (-(1 / 12 : ℝ))
  have hδ₀_pos : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ₀_le_1 : δ₀ ≤ 1 := by
    have h_rpow : 3 * π ≤ n ^ (1 / 12 : ℝ) := by
      calc 3 * π = ((3 * π) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) := by
            rw [← Real.rpow_natCast (3 * π) 12, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ n ^ (1 / 12 : ℝ) := Real.rpow_le_rpow (by positivity) hn_ge (by positivity)
    calc δ₀ = 3 * π / n ^ (1 / 12 : ℝ) := by
          dsimp [δ₀]; rw [Real.rpow_neg hn_pos.le, div_eq_mul_inv]; ring
      _ ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hn_pos _)).mpr h_rpow
  set M_c : ℝ := (√2 * (π / 2) * √(π / 2) * C_env) * (a * L_exp) * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)
  have hM_c_nn : 0 ≤ M_c := by
    have : 0 ≤ L_exp := (Real.exp_pos _).le.trans hL_exp
    dsimp [M_c]; positivity
  let B_cov : ℝ → ℝ := fun θ =>
    M_c * ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) * Real.exp (-(4 * ℓ * a / π) * ((π - |θ|) / 2))
  set M_unc : ℝ := (2 * √2 * C_env * Real.exp 1) * a ^ (-(2 : ℤ)) * δ₀ ^ k
  have hM_unc_nn : 0 ≤ M_unc := by dsimp [M_unc]; positivity
  let W_unc : Set ℝ := {θ : ℝ | π - δ₀ < |θ|}
  have hW_meas : MeasurableSet W_unc := measurableSet_lt measurable_const continuous_abs.measurable
  let B_unc : ℝ → ℝ := W_unc.indicator (fun _ => M_unc)
  let B : ℝ → ℝ := fun θ => B_cov θ + B_unc θ
  have hk_half_pos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by
    have : (5 : ℝ) ≤ k := by exact_mod_cast hk5
    linarith only [this]
  have hB_cov_cont : ContinuousOn B_cov (Icc (-π) π) := fun θ _ =>
    Continuous.continuousWithinAt <|
      (continuous_const.mul ((Continuous.rpow_const ((continuous_const.sub continuous_abs).div_const 2)
        (fun _ => Or.inr hk_half_pos.le)))).mul
      (Real.continuous_exp.comp (continuous_const.mul ((continuous_const.sub continuous_abs).div_const 2)))
  have hB_cov_int : IntervalIntegrable B_cov volume (-π) π :=
    hB_cov_cont.intervalIntegrable_of_Icc (by linarith only [Real.pi_pos])
  have hB_unc_int : IntervalIntegrable B_unc volume (-π) π := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith only [Real.pi_pos])]
    exact ((continuousOn_const (c := M_unc)).integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator hW_meas
  have hB_int : IntervalIntegrable B volume (-π) π := hB_cov_int.add hB_unc_int
  have hB_bd : ∀ θ ∈ Icc (-π) π, ‖f (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) ≤ B θ := by
    intro θ hθ
    have hB_cov_nn : 0 ≤ B_cov θ := by
      dsimp [B_cov]
      exact mul_nonneg (mul_nonneg hM_c_nn (Real.rpow_nonneg (by linarith only [abs_le.mpr hθ]) _))
        (Real.exp_pos _).le
    have hB_unc_nn : 0 ≤ B_unc θ := by
      dsimp [B_unc]; by_cases h : θ ∈ W_unc <;> simp [h, hM_unc_nn]
    have he_pos : 0 < airyEnv (circleMap 0 R θ) := airyEnv_pos _
    rw [div_le_iff₀ he_pos]
    have h1w : ‖1 + circleMap 0 R θ / (R : ℂ)‖ = 2 * Real.cos (θ / 2) :=
      norm_one_add_circleMap_div hR_pos hθ
    by_cases hpi : |θ| = π
    · have hcos0 : Real.cos (θ / 2) = 0 := by
        rcases abs_eq Real.pi_pos.le |>.mp hpi with rfl | rfl
        · simp [Real.cos_pi_div_two]
        · simp [neg_div, Real.cos_neg, Real.cos_pi_div_two]
      have hf0 : ‖f (circleMap 0 R θ)‖ = 0 := by
        dsimp [f, spinShiftedFun]
        rw [norm_mul, norm_pow, h1w, hcos0, mul_zero, zero_pow (Nat.succ_ne_zero k), mul_zero]
      rw [hf0]
      exact mul_nonneg (add_nonneg hB_cov_nn hB_unc_nn) he_pos.le
    · have h_abs_lt : |θ| < π := lt_of_le_of_ne (abs_le.mpr hθ) hpi
      by_cases hcov : |θ| ≤ π - δ₀
      · have h_pt := spin_quad_cov_pt hC_pos hς_nn hR_10 hℓ_nn hℓ_half hL_exp hEnv hk5 hθ h_abs_lt
        exact h_pt.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB_unc_nn) he_pos.le)
      · push Not at hcov
        have hB_unc_eq : B_unc θ = M_unc := Set.indicator_of_mem (show θ ∈ W_unc from hcov) _
        have h_pt := spin_quad_unc_pt hC_pos hς_nn hn_pos hς_unc hR_10 hℓ_nn hℓ_half hEnv k hθ h_abs_lt hcov
        have h_le : M_unc * airyEnv (circleMap 0 R θ) ≤ B θ * airyEnv (circleMap 0 R θ) := by
          rw [← hB_unc_eq]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB_cov_nn) he_pos.le
        exact h_pt.trans h_le
  have h_def := airy_defect_ball_split hD (by linarith only [hR_pos] : R < R + 1 / 3) hf_diff hRp hRm hB_int hB_bd
  have h_sum_eq : (∑ m ∈ Finset.Icc 1 N, f (airyZero m : ℂ) / (deriv airyAiC (airyZero m : ℂ)) ^ 2).re =
      spinPNodes c Φ R ℓ k N := by
    unfold spinPNodes
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [deriv_airyAiC_ofReal', ← Complex.ofReal_pow, Complex.div_ofReal_re]
  have h_int_eq : (∫ x in (-R)..R, f (x : ℂ)).re = ∫ x in (-R)..R, (f (x : ℂ)).re := by
    have hf_cont_R : ContinuousOn (fun x : ℝ => f (x : ℂ)) (Icc (-R) R) := by
      refine hf_diff.continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_le.mpr hx).trans_lt (by linarith only [hR_pos])
    exact (Complex.reCLM.intervalIntegral_comp_comm (hf_cont_R.intervalIntegrable_of_Icc (by linarith only [hR_pos]))).symm
  have h_quad_re : spinPNodes c Φ R ℓ k N - (∫ x in (-R)..R, (f (x : ℂ)).re) ≤
      (15 * √π * R) * ∫ θ in (-π)..π, B θ := by
    have hre := (Complex.abs_re_le_norm _).trans h_def
    rw [Complex.sub_re, h_sum_eq, h_int_eq] at hre
    exact (abs_le.mp hre).2
  have h_unc_int : (15 * √π * R) * ∫ θ in (-π)..π, B_unc θ ≤
      spinArcUncConst C_env * n ^ (-(3 / 8 : ℝ)) := by
    have h_meas_le : ∫ θ in (-π)..π, B_unc θ ≤ 4 * δ₀ * M_unc := by
      let J₁ := Icc (-π) (-(π - δ₀))
      let J₂ := Icc (π - δ₀) π
      have h_sub_W : W_unc ∩ Ioc (-π) π ⊆ J₁ ∪ J₂ := by
        intro θ ⟨hW, hIoc⟩
        rcases le_total θ 0 with h0 | h0
        · left; refine ⟨hIoc.1.le, ?_⟩
          have : |θ| = -θ := abs_of_nonpos h0
          rw [Set.mem_ofPred_eq, this] at hW; linarith only [hW]
        · right; refine ⟨?_, hIoc.2⟩
          have : |θ| = θ := abs_of_nonneg h0
          rw [Set.mem_ofPred_eq, this] at hW; linarith only [hW]
      rw [intervalIntegral.integral_of_le (by linarith only [Real.pi_pos])]
      have h_ind_eq : ∫ θ in Ioc (-π) π, B_unc θ = M_unc * (volume (W_unc ∩ Ioc (-π) π)).toReal := by
        dsimp [B_unc]
        rw [setIntegral_indicator hW_meas, setIntegral_const, smul_eq_mul, Measure.real_def, Set.inter_comm]
        ring
      have h_vol : (volume (W_unc ∩ Ioc (-π) π)).toReal ≤ 4 * δ₀ := by
        have hm1 : volume (W_unc ∩ Ioc (-π) π) ≤ volume (J₁ ∪ J₂) := measure_mono h_sub_W
        have hm2 : volume (J₁ ∪ J₂) ≤ volume J₁ + volume J₂ := measure_union_le J₁ J₂
        have hJ1 : volume J₁ = ENNReal.ofReal δ₀ := by dsimp [J₁]; rw [Real.volume_Icc]; congr 1; ring
        have hJ2 : volume J₂ = ENNReal.ofReal δ₀ := by dsimp [J₂]; rw [Real.volume_Icc]; congr 1; ring
        have hlt : volume (W_unc ∩ Ioc (-π) π) ≤ ENNReal.ofReal (4 * δ₀) := by
          calc volume (W_unc ∩ Ioc (-π) π) ≤ ENNReal.ofReal δ₀ + ENNReal.ofReal δ₀ :=
                hm1.trans (hm2.trans_eq (by rw [hJ1, hJ2]))
            _ = ENNReal.ofReal (2 * δ₀) := by
                rw [← ENNReal.ofReal_add hδ₀_pos.le hδ₀_pos.le, two_mul]
            _ ≤ ENNReal.ofReal (4 * δ₀) := ENNReal.ofReal_le_ofReal (by linarith only [hδ₀_pos])
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlt
      rw [h_ind_eq]
      exact (mul_le_mul_of_nonneg_left h_vol hM_unc_nn).trans_eq (by ring)
    have hR_a2 : R * a ^ (-(2 : ℤ)) = 1 := by
      rw [← ha_sq, zpow_neg, show (2 : ℤ) = (2 : ℕ) by rfl, zpow_natCast]
      field_simp [ha_pos.ne']
    have hδ_pow : δ₀ ^ (k + 1) ≤ (3 * π) ^ (6 : ℕ) * n ^ (-(3 / 8 : ℝ)) := by
      have hk6 : 6 ≤ k + 1 := by omega
      have h1 : δ₀ ^ (k + 1) ≤ δ₀ ^ 6 := pow_le_pow_of_le_one hδ₀_pos.le hδ₀_le_1 hk6
      have h2 : δ₀ ^ 6 = (3 * π) ^ (6 : ℕ) * n ^ (-(1 / 2 : ℝ)) := by
        dsimp [δ₀]; rw [mul_pow, ← Real.rpow_natCast (n ^ (-(1 / 12 : ℝ))) 6, ← Real.rpow_mul hn_pos.le]; norm_num
      have h3 : n ^ (-(1 / 2 : ℝ)) ≤ n ^ (-(3 / 8 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le
          ((one_le_pow₀ (by linarith only [Real.pi_gt_three] : (1 : ℝ) ≤ 3 * π)).trans hn_ge)
          (by norm_num)
      calc δ₀ ^ (k + 1) ≤ δ₀ ^ 6 := h1
        _ = (3 * π) ^ (6 : ℕ) * n ^ (-(1 / 2 : ℝ)) := h2
        _ ≤ (3 * π) ^ (6 : ℕ) * n ^ (-(3 / 8 : ℝ)) := by gcongr
    calc (15 * √π * R) * ∫ θ in (-π)..π, B_unc θ
        ≤ (15 * √π * R) * (4 * δ₀ * M_unc) := by gcongr
      _ = 15 * √π * 8 * √2 * C_env * Real.exp 1 * (R * a ^ (-(2 : ℤ))) * δ₀ ^ (k + 1) := by
          dsimp [M_unc]; rw [pow_succ]; ring
      _ = 15 * √π * 8 * √2 * C_env * Real.exp 1 * δ₀ ^ (k + 1) := by rw [hR_a2, mul_one]
      _ ≤ (15 * √π * 8 * √2 * C_env * Real.exp 1) * ((3 * π) ^ (6 : ℕ) * n ^ (-(3 / 8 : ℝ))) :=
          mul_le_mul_of_nonneg_left hδ_pow (by positivity)
      _ = spinArcUncConst C_env * n ^ (-(3 / 8 : ℝ)) := by unfold spinArcUncConst; ring
  have hB_add_int : ∫ θ in (-π)..π, B θ = (∫ θ in (-π)..π, B_cov θ) + ∫ θ in (-π)..π, B_unc θ :=
    intervalIntegral.integral_add hB_cov_int hB_unc_int
  have h_cov_eq : (15 * √π * R) * ∫ θ in (-π)..π, B_cov θ = spinArcCov C_env R (√R * L_exp) ℓ k := by
    unfold spinArcCov; rfl
  rw [hB_add_int, mul_add, h_cov_eq] at h_quad_re
  linarith only [h_quad_re, h_unc_int]

end QuadratureAndArc

end FormalResearch.ModularBootstrap.Spin
