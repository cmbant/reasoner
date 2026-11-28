/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpAsympWin

/-!
# Auxiliary Airy-window comparison lemmas for `fct:physical-positive` (i)

Proves:
* `win_arg_g1_sub_uhat`: the `ctWg1_win_bound` Airy argument differs from `winUhat` by `O_{K4}(c^{-1/2})`
  on the fixed Airy window `L ∈ [fctWarpL1 h ε c, Sw * c^{-2/3}]`;
* `win_vhat_sub_a1_of_delta_ge`: on `Δ ≥ T₁ + (2 K_d / β₁) c^{-3/4}` with `L = log(π² Δ / c) ≤ Sw c^{-2/3}`,
  we have `L > L₁` and `v̂(L) - |a₁| ≥ (7/4) K_d c^{-13/12}`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctSym

namespace FormalResearch.SignUncertainty

private lemma ceBeta1_div_pi_sq : ceBeta1 / π ^ 2 = ceCs⁻¹ := by
  unfold ceBeta1 ceCs
  have hmul : (π ^ 2 * √3) ^ 2 = π ^ 4 * 3 := by
    rw [mul_pow, ← pow_mul, Real.sq_sqrt (by norm_num)]
  have h1 : (π ^ 2 * √3) ^ (2 / 3 : ℝ) = (π ^ 4 * 3) ^ (1 / 3 : ℝ) := by
    rw [show (2 / 3 : ℝ) = (2 : ℝ) * (1 / 3 : ℝ) by norm_num, Real.rpow_mul (by positivity),
      Real.rpow_two, hmul]
  have hpi : π ^ 2 = (π ^ 6) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast π 6, ← Real.rpow_mul Real.pi_pos.le]; norm_num
  rw [h1]
  conv_lhs => rhs; rw [hpi]
  rw [← Real.div_rpow (by positivity) (by positivity),
    show (π ^ 4 * 3) / π ^ 6 = (π ^ 2 / 3)⁻¹ by field_simp [Real.pi_pos.ne'],
    Real.inv_rpow (by positivity)]

private lemma ceCs_mul_hankelBeta1 : ceCs * hankelBeta1 = π ^ 2 := by
  have hhb : hankelBeta1 = ceBeta1 := rfl
  rw [hhb, show ceCs * ceBeta1 = ceCs * (π ^ 2 * (ceBeta1 / π ^ 2)) by field_simp [Real.pi_pos.ne'],
    ceBeta1_div_pi_sq, show ceCs * (π ^ 2 * ceCs⁻¹) = (ceCs * ceCs⁻¹) * π ^ 2 by ring,
    mul_inv_cancel₀ ceCs_pos.ne', one_mul]

/-- Comparison between the unwarped `ctWg1_win_bound` Airy argument and `winUhat` on the fixed Airy window:
their difference is `O_{K4}(c^{-1/2})`. -/
theorem win_arg_g1_sub_uhat {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) (Sw : ℝ) (hSw : 1 ≤ Sw) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 15000 ≤ c₀ ∧ ∀ {ε c L : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c → fctWarpL1 h ε c ≤ L → L ≤ Sw * c ^ (-(2 / 3 : ℝ)) →
      let ξ := fctXi1 L
      let arg_g1 := -(ceBeta1 * hbS c ξ) + ceBeta1 * (deriv (outerTheta ε) 0 / π ^ 2) * liftEps c
      |arg_g1 - winUhat K4 ε c (fctWarpAlpha h ε c) L| ≤ C * c ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨_, C_s, c_κ, _, hCs0, _, hκ_bds⟩ := win_uhat_slope_approx hK4 h hSw
  obtain ⟨C_u, c_u, hCu0, _, hu_err⟩ := win_zero_a1_err hK4 h
  obtain ⟨K_L, c_L, hcL1, hL1_bd⟩ := FctSym.physL1_le (fctWarpT1 h)
    ⟨h.choose, h.choose_spec.choose, fun _ _ hε hc => (fctWarpPair_spec h hε hc).1.2.1⟩
  let K_L' : ℝ := max K_L 0
  have hKL0 : 0 ≤ K_L' := le_max_right _ _
  let C_d5 : ℝ := |h.choose| * π ^ 2 + π ^ 2 * (|ctC1Langer| + |ctD2star 1| + |ctD2star (-1)|) + K_L' ^ 2
  let C_tot : ℝ := C_d5 / ceCs + C_s * (Sw + K_L') + C_u
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (15000 : ℝ) ≤ c ∧ c_κ ≤ c ∧ c_u ≤ c ∧ c_L ≤ c ∧ h.choose_spec.choose ≤ c ∧
      K_L' * c ^ (-(2 / 3 : ℝ)) ≤ 1 / 2 := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
        (Eventually.and (eventually_ge_atTop _) ?_))))
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul K_L'
    rw [mul_zero] at ht; exact ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨C_tot, max 15000 c₀, ?_, le_max_left _ _, fun {ε c L} hε hc hL1_le hL_Sw => ?_⟩
  · have := ceCs_pos; positivity
  obtain ⟨hc15, hck, hcu, hcL, hcpair, hKL_half⟩ := hc₀ c ((le_max_right _ _).trans hc)
  have hc0 : 0 < c := by linarith only [hc15]
  have hc1 : 1 ≤ c := by linarith only [hc15]
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  have hL_ξ : Real.log (Real.pi ^ 2 * fctXi1 L) = L := by
    unfold fctXi1
    rw [show π ^ 2 * (Real.exp L / π ^ 2) = Real.exp L by field_simp [Real.pi_pos.ne'], Real.log_exp]
  have harg_eq : -(ceBeta1 * hbS c (fctXi1 L)) +
      ceBeta1 * (deriv (outerTheta ε) 0 / π ^ 2) * liftEps c =
      -(c ^ (2 / 3 : ℝ) / ceCs) * (L - ctTheta1 ε / c) := by
    rw [deriv_outerTheta_zero_eq_ctTheta1 hε]
    unfold hbS liftEps
    rw [hL_ξ]
    have hc23 : (c ^ (-(1 / 3 : ℝ))) ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hc13_eq : c ^ (-(1 / 3 : ℝ)) = c ^ (2 / 3 : ℝ) * c⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; congr 1; norm_num
    have hinv23 : (c ^ (-(2 / 3 : ℝ)))⁻¹ = c ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_neg hc0.le]; norm_num
    rw [hc23, hc13_eq, div_eq_mul_inv (L : ℝ) _, mul_inv, hinv23]
    calc -(ceBeta1 * (L * ((π ^ 2)⁻¹ * c ^ (2 / 3 : ℝ)))) +
          ceBeta1 * (ctTheta1 ε / π ^ 2) * (c ^ (2 / 3 : ℝ) * c⁻¹)
        = -(ceBeta1 / π ^ 2) * c ^ (2 / 3 : ℝ) * L +
          (ceBeta1 / π ^ 2) * c ^ (2 / 3 : ℝ) * (ctTheta1 ε / c) := by ring
      _ = -(c ^ (2 / 3 : ℝ) / ceCs) * (L - ctTheta1 ε / c) := by
          rw [ceBeta1_div_pi_sq]; ring
  have hL1_23 : |L1| ≤ K_L' * c ^ (-(2 / 3 : ℝ)) := by
    have h1 := hL1_bd ε c hε hcL
    unfold FctSym.physL1 at h1
    rw [physL1_fctWarpT1 h hc0] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hL1_half : |L1| ≤ 1 / 2 := hL1_23.trans hKL_half
  have hT1_err : |fctWarpT1 h ε c - ctDelta5 ε c| ≤ h.choose * c⁻¹ :=
    (fctWarpPair_spec h hε hcpair).1.2.1
  have hexp_L1 : |Real.exp L1 - 1 - L1| ≤ L1 ^ 2 := Real.abs_exp_sub_one_sub_id_le (by linarith only [hL1_half])
  have ha1_neg : airyZero 1 < 0 := airyZero_neg 1
  have h_airy_id : π ^ 2 / ceCs * airyOrderCoeff = -airyZero 1 := by
    unfold airyOrderCoeff
    rw [abs_of_neg ha1_neg]
    have hce_ne : ceCs * hankelBeta1 ≠ 0 := by
      have := ceCs_pos; have := Real.pi_pos; unfold hankelBeta1; positivity
    have hrat : π ^ 2 / (ceCs * hankelBeta1) = 1 := by rw [ceCs_mul_hankelBeta1, div_self (by positivity)]
    calc π ^ 2 / ceCs * (-airyZero 1 / hankelBeta1)
        = (-airyZero 1) * (π ^ 2 / (ceCs * hankelBeta1)) := by ring
      _ = -airyZero 1 := by rw [hrat, mul_one]
  have hL1_diff_eq : L1 - ctTheta1 ε / c - (π ^ 2 * airyOrderCoeff) * c ^ (-(2 / 3 : ℝ)) =
      (L1 - (Real.exp L1 - 1)) +
      (π ^ 2 / c) * (fctWarpT1 h ε c - ctDelta5 ε c) +
      (π ^ 2 / c) * (ctC1Langer * c ^ (-(1 / 3 : ℝ)) + ctD2star ε * c ^ (-(2 / 3 : ℝ))) := by
    unfold fctWarpT1 ctDelta5 ctKappa
    have h13 : c ^ (1 / 3 : ℝ) / c = c ^ (-(2 / 3 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hc0]; congr 1; norm_num
    rw [← h13]
    field_simp [hc0.ne', Real.pi_pos.ne']
    ring
  have hL1_err : |L1 - ctTheta1 ε / c - (π ^ 2 * airyOrderCoeff) * c ^ (-(2 / 3 : ℝ))| ≤
      C_d5 * c ^ (-(4 / 3 : ℝ)) := by
    rw [hL1_diff_eq]
    have hc43 : c⁻¹ * c ^ (-(1 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; congr 1; norm_num
    have hc2_43 : c ^ (-2 : ℝ) ≤ c ^ (-(4 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hc53_43 : c⁻¹ * c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hc23_sq : (c ^ (-(2 / 3 : ℝ))) ^ 2 = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have b1 : |L1 - (Real.exp L1 - 1)| ≤ K_L' ^ 2 * c ^ (-(4 / 3 : ℝ)) := by
      rw [abs_sub_comm]
      calc |Real.exp L1 - 1 - L1| ≤ L1 ^ 2 := hexp_L1
        _ ≤ (K_L' * c ^ (-(2 / 3 : ℝ))) ^ 2 := by rw [← sq_abs L1]; exact pow_le_pow_left₀ (abs_nonneg _) hL1_23 2
        _ = K_L' ^ 2 * c ^ (-(4 / 3 : ℝ)) := by rw [mul_pow, hc23_sq]
    have b2 : |(π ^ 2 / c) * (fctWarpT1 h ε c - ctDelta5 ε c)| ≤ |h.choose| * π ^ 2 * c ^ (-(4 / 3 : ℝ)) := by
      rw [abs_mul, abs_of_pos (div_pos (sq_pos_of_pos Real.pi_pos) hc0)]
      have hcinv2 : c⁻¹ * c⁻¹ = c ^ (-2 : ℝ) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; congr 1; norm_num
      calc (π ^ 2 / c) * |fctWarpT1 h ε c - ctDelta5 ε c| ≤ (π ^ 2 / c) * (h.choose * c⁻¹) := by
            gcongr
        _ ≤ (π ^ 2 / c) * (|h.choose| * c⁻¹) := by gcongr; exact le_abs_self _
        _ = |h.choose| * π ^ 2 * (c⁻¹ * c⁻¹) := by ring
        _ = |h.choose| * π ^ 2 * c ^ (-2 : ℝ) := by rw [hcinv2]
        _ ≤ |h.choose| * π ^ 2 * c ^ (-(4 / 3 : ℝ)) := by gcongr
    have b3 : |(π ^ 2 / c) * (ctC1Langer * c ^ (-(1 / 3 : ℝ)) + ctD2star ε * c ^ (-(2 / 3 : ℝ)))| ≤
        π ^ 2 * (|ctC1Langer| + |ctD2star 1| + |ctD2star (-1)|) * c ^ (-(4 / 3 : ℝ)) := by
      rw [abs_mul, abs_of_pos (div_pos (sq_pos_of_pos Real.pi_pos) hc0)]
      have hc13_nn : 0 ≤ c ^ (-(1 / 3 : ℝ)) := by positivity
      have hc23_nn : 0 ≤ c ^ (-(2 / 3 : ℝ)) := by positivity
      have hD_le : |ctD2star ε| ≤ |ctD2star 1| + |ctD2star (-1)| := by
        rcases hε with rfl | rfl
        · linarith [abs_nonneg (ctD2star (-1))]
        · linarith [abs_nonneg (ctD2star 1)]
      calc (π ^ 2 / c) * |ctC1Langer * c ^ (-(1 / 3 : ℝ)) + ctD2star ε * c ^ (-(2 / 3 : ℝ))|
          ≤ (π ^ 2 / c) * (|ctC1Langer| * c ^ (-(1 / 3 : ℝ)) + (|ctD2star 1| + |ctD2star (-1)|) * c ^ (-(2 / 3 : ℝ))) := by
            gcongr
            calc _ ≤ |ctC1Langer * c ^ (-(1 / 3 : ℝ))| + |ctD2star ε * c ^ (-(2 / 3 : ℝ))| := abs_add_le _ _
              _ = |ctC1Langer| * c ^ (-(1 / 3 : ℝ)) + |ctD2star ε| * c ^ (-(2 / 3 : ℝ)) := by
                  rw [abs_mul, abs_mul, abs_of_nonneg hc13_nn, abs_of_nonneg hc23_nn]
              _ ≤ _ := by gcongr
        _ = π ^ 2 * (|ctC1Langer| * (c⁻¹ * c ^ (-(1 / 3 : ℝ))) +
              (|ctD2star 1| + |ctD2star (-1)|) * (c⁻¹ * c ^ (-(2 / 3 : ℝ)))) := by ring
        _ ≤ π ^ 2 * (|ctC1Langer| * c ^ (-(4 / 3 : ℝ)) +
              (|ctD2star 1| + |ctD2star (-1)|) * c ^ (-(4 / 3 : ℝ))) := by gcongr; rw [hc43]
        _ = π ^ 2 * (|ctC1Langer| + |ctD2star 1| + |ctD2star (-1)|) * c ^ (-(4 / 3 : ℝ)) := by ring
    calc |L1 - (Real.exp L1 - 1) + π ^ 2 / c * (fctWarpT1 h ε c - ctDelta5 ε c) +
          π ^ 2 / c * (ctC1Langer * c ^ (-(1 / 3 : ℝ)) + ctD2star ε * c ^ (-(2 / 3 : ℝ)))|
        ≤ |L1 - (Real.exp L1 - 1)| + |π ^ 2 / c * (fctWarpT1 h ε c - ctDelta5 ε c)| +
          |π ^ 2 / c * (ctC1Langer * c ^ (-(1 / 3 : ℝ)) + ctD2star ε * c ^ (-(2 / 3 : ℝ)))| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add b1 b2) b3
      _ = C_d5 * c ^ (-(4 / 3 : ℝ)) := by dsimp [C_d5]; ring
  have harg_lin : |-(ceBeta1 * hbS c (fctXi1 L)) + ceBeta1 * (deriv (outerTheta ε) 0 / π ^ 2) * liftEps c -
      (airyZero 1 - (c ^ (2 / 3 : ℝ) / ceCs) * (L - L1))| ≤ (C_d5 / ceCs) * c ^ (-(1 / 2 : ℝ)) := by
    rw [harg_eq]
    have h1 : -(c ^ (2 / 3 : ℝ) / ceCs) * (L - ctTheta1 ε / c) - (airyZero 1 - (c ^ (2 / 3 : ℝ) / ceCs) * (L - L1)) =
        -(c ^ (2 / 3 : ℝ) / ceCs) * (L1 - ctTheta1 ε / c - (π ^ 2 * airyOrderCoeff) * c ^ (-(2 / 3 : ℝ))) := by
      have hc_eq : c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) = 1 := by rw [← Real.rpow_add hc0]; norm_num
      calc -(c ^ (2 / 3 : ℝ) / ceCs) * (L - ctTheta1 ε / c) - (airyZero 1 - (c ^ (2 / 3 : ℝ) / ceCs) * (L - L1))
          = -(c ^ (2 / 3 : ℝ) / ceCs) * (L1 - ctTheta1 ε / c) - airyZero 1 := by ring
        _ = -(c ^ (2 / 3 : ℝ) / ceCs) * (L1 - ctTheta1 ε / c) +
              (π ^ 2 / ceCs * airyOrderCoeff) * (c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) := by
            rw [h_airy_id, hc_eq]; ring
        _ = _ := by ring
    rw [h1, abs_mul, abs_neg, abs_of_pos (div_pos (Real.rpow_pos_of_pos hc0 _) ceCs_pos)]
    have hc23_43 : c ^ (2 / 3 : ℝ) * c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hc_div_nn : 0 ≤ c ^ (2 / 3 : ℝ) / ceCs := div_nonneg (Real.rpow_nonneg hc0.le _) ceCs_pos.le
    have hCd5_nn : 0 ≤ C_d5 / ceCs := by
      have := ceCs_pos; dsimp [C_d5]; positivity
    calc (c ^ (2 / 3 : ℝ) / ceCs) * |L1 - ctTheta1 ε / c - π ^ 2 * airyOrderCoeff * c ^ (-(2 / 3 : ℝ))|
        ≤ (c ^ (2 / 3 : ℝ) / ceCs) * (C_d5 * c ^ (-(4 / 3 : ℝ))) := mul_le_mul_of_nonneg_left hL1_err hc_div_nn
      _ = (C_d5 / ceCs) * (c ^ (2 / 3 : ℝ) * c ^ (-(4 / 3 : ℝ))) := by ring
      _ ≤ (C_d5 / ceCs) * c ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hc23_43 hCd5_nn
  have hu1_e := (hu_err hε hcu).1
  have hu1_12 : |winUhat K4 ε c α L1 - airyZero 1| ≤ C_u * c ^ (-(1 / 2 : ℝ)) :=
    hu1_e.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)) hCu0)
  have huL_lin : |winUhat K4 ε c α L - (airyZero 1 - (c ^ (2 / 3 : ℝ) / ceCs) * (L - L1))| ≤
      (C_s * (Sw + K_L') + C_u) * c ^ (-(1 / 2 : ℝ)) := by
    rcases hL1_le.eq_or_lt with heq | hlt
    · rw [← heq]
      simpa using hu1_12.trans (by
        have : 0 ≤ C_s * (Sw + K_L') * c ^ (-(1 / 2 : ℝ)) := by positivity
        linarith)
    · have hslope := (hκ_bds hε hck hlt hL_Sw).2.2.2
      have hL_diff : L - L1 ≤ (Sw + K_L') * c ^ (-(2 / 3 : ℝ)) := by
        have h2 : -L1 ≤ K_L' * c ^ (-(2 / 3 : ℝ)) := (neg_le_abs L1).trans hL1_23
        linarith only [hL_Sw, h2]
      have hc16_23 : c ^ (1 / 6 : ℝ) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have h1 : |winUhat K4 ε c α L1 - winUhat K4 ε c α L - c ^ (2 / 3 : ℝ) / ceCs * (L - L1)| ≤
          C_s * (Sw + K_L') * c ^ (-(1 / 2 : ℝ)) := by
        calc _ ≤ C_s * c ^ (1 / 6 : ℝ) * (L - L1) := hslope
          _ ≤ C_s * c ^ (1 / 6 : ℝ) * ((Sw + K_L') * c ^ (-(2 / 3 : ℝ))) :=
              mul_le_mul_of_nonneg_left hL_diff (by positivity)
          _ = C_s * (Sw + K_L') * (c ^ (1 / 6 : ℝ) * c ^ (-(2 / 3 : ℝ))) := by ring
          _ = C_s * (Sw + K_L') * c ^ (-(1 / 2 : ℝ)) := by rw [hc16_23]
      have heq_u : winUhat K4 ε c α L - (airyZero 1 - c ^ (2 / 3 : ℝ) / ceCs * (L - L1)) =
          (winUhat K4 ε c α L1 - airyZero 1) -
          (winUhat K4 ε c α L1 - winUhat K4 ε c α L - c ^ (2 / 3 : ℝ) / ceCs * (L - L1)) := by ring
      rw [heq_u]
      calc _ ≤ |winUhat K4 ε c α L1 - airyZero 1| +
            |winUhat K4 ε c α L1 - winUhat K4 ε c α L - c ^ (2 / 3 : ℝ) / ceCs * (L - L1)| := abs_sub _ _
        _ ≤ C_u * c ^ (-(1 / 2 : ℝ)) + C_s * (Sw + K_L') * c ^ (-(1 / 2 : ℝ)) := add_le_add hu1_12 h1
        _ = (C_s * (Sw + K_L') + C_u) * c ^ (-(1 / 2 : ℝ)) := by ring
  have heq_fin : -(ceBeta1 * hbS c (fctXi1 L)) + ceBeta1 * (deriv (outerTheta ε) 0 / π ^ 2) * liftEps c -
      winUhat K4 ε c α L =
      (-(ceBeta1 * hbS c (fctXi1 L)) + ceBeta1 * (deriv (outerTheta ε) 0 / π ^ 2) * liftEps c -
        (airyZero 1 - c ^ (2 / 3 : ℝ) / ceCs * (L - L1))) -
      (winUhat K4 ε c α L - (airyZero 1 - c ^ (2 / 3 : ℝ) / ceCs * (L - L1))) := by ring
  dsimp only
  rw [heq_fin]
  calc _ ≤ _ + _ := abs_sub _ _
    _ ≤ (C_d5 / ceCs) * c ^ (-(1 / 2 : ℝ)) + (C_s * (Sw + K_L') + C_u) * c ^ (-(1 / 2 : ℝ)) :=
        add_le_add harg_lin huL_lin
    _ = C_tot * c ^ (-(1 / 2 : ℝ)) := by dsimp [C_tot]; ring

/-- On the physical lower threshold `Δ ≥ T₁ + (2 K_d / β₁) c^{-3/4}` inside the Airy window
`L := log(π² Δ / c) ≤ Sw c^{-2/3}`, we have `L > L₁` and `v̂(L) - |a₁| ≥ (7/4) K_d c^{-13/12}`
(`fct:physical-positive`). -/
theorem win_vhat_sub_a1_of_delta_ge {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4)
    (Sw : ℝ) (hSw : 1 ≤ Sw) {Kd : ℝ} (hKd : 0 < Kd) :
    ∃ c₀ : ℝ, 15000 ≤ c₀ ∧ ∀ {ε c Δ : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      fctWarpT1 h ε c + 2 * Kd / hankelBeta1 * c ^ (-(3 / 4 : ℝ)) ≤ Δ →
      Real.log (π ^ 2 * Δ / c) ≤ Sw * c ^ (-(2 / 3 : ℝ)) →
      let L := Real.log (π ^ 2 * Δ / c)
      fctWarpL1 h ε c < L ∧
        (7 / 4 : ℝ) * Kd * c ^ (-(13 / 12 : ℝ)) ≤ airyZero 1 - winUhat K4 ε c (fctWarpAlpha h ε c) L := by
  obtain ⟨_, C_s, c_κ, _, hCs0, _, hκ_bds⟩ := win_uhat_slope_approx hK4 h hSw
  obtain ⟨C_u, c_u, hCu0, _, hu_err⟩ := win_zero_a1_err hK4 h
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      (15000 : ℝ) ≤ c ∧ c_κ ≤ c ∧ c_u ≤ c ∧
      Real.exp (Sw * c ^ (-(2 / 3 : ℝ))) ≤ 33 / 32 ∧
      C_s * c ^ (-(1 / 2 : ℝ)) ≤ (1 / 33) * (1 / ceCs) ∧
      C_u * c ^ (-(1 / 4 : ℝ)) ≤ (1 / 8) * Kd := by
    refine Eventually.and (eventually_ge_atTop _) (Eventually.and (eventually_ge_atTop _)
      (Eventually.and (eventually_ge_atTop _) (Eventually.and ?_ (Eventually.and ?_ ?_))))
    · have ht := Real.continuous_exp.continuousAt.tendsto.comp
        (by simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul Sw)
      rw [Real.exp_zero] at ht
      exact ht.eventually (Iic_mem_nhds (by norm_num))
    · have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C_s
      rw [mul_zero] at ht; exact ht.eventually (Iic_mem_nhds (by have := ceCs_pos; positivity))
    · have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul C_u
      rw [mul_zero] at ht; exact ht.eventually (Iic_mem_nhds (by positivity))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨max 15000 c₀, le_max_left _ _, fun {ε c Δ} hε hc hΔ hL_Sw => ?_⟩
  obtain ⟨hc15, hck, hcu, hexp_Sw, hCs_sm, hCu_sm⟩ := hc₀ c ((le_max_right _ _).trans hc)
  have hc0 : 0 < c := by linarith only [hc15]
  set L1 := fctWarpL1 h ε c
  set L := Real.log (π ^ 2 * Δ / c)
  have hT1_pos : 0 < fctWarpT1 h ε c := by unfold fctWarpT1; positivity
  have hgap_pos : 0 < 2 * Kd / hankelBeta1 * c ^ (-(3 / 4 : ℝ)) := by
    unfold hankelBeta1; positivity
  have hΔ_gt : fctWarpT1 h ε c < Δ := by linarith only [hΔ, hgap_pos]
  have hΔ_pos : 0 < Δ := lt_trans hT1_pos hΔ_gt
  have hL1_eq : Real.log (π ^ 2 * fctWarpT1 h ε c / c) = L1 := physL1_fctWarpT1 h hc0
  have hL1_lt : L1 < L := by
    rw [← hL1_eq]
    exact Real.log_lt_log (by positivity) (by gcongr)
  refine ⟨hL1_lt, ?_⟩
  have hL_diff_eq : L - L1 = Real.log (Δ / fctWarpT1 h ε c) := by
    rw [← hL1_eq, ← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp [Real.pi_pos.ne', hc0.ne']
  have hlog_lb : (Δ - fctWarpT1 h ε c) / Δ ≤ L - L1 := by
    rw [hL_diff_eq]
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hΔ_pos hT1_pos)
    have heq : 1 - (Δ / fctWarpT1 h ε c)⁻¹ = (Δ - fctWarpT1 h ε c) / Δ := by
      field_simp [hΔ_pos.ne', hT1_pos.ne']
    linarith only [h1, heq]
  have hΔ_ub : Δ ≤ (33 / 32 : ℝ) * (c / π ^ 2) := by
    have he : π ^ 2 * Δ / c = Real.exp L := (Real.exp_log (by positivity)).symm
    have hexp_le : Real.exp L ≤ 33 / 32 := (Real.exp_le_exp.mpr hL_Sw).trans hexp_Sw
    have hΔ_eq : Δ = (c / π ^ 2) * Real.exp L := by
      rw [← he]; field_simp [Real.pi_pos.ne', hc0.ne']
    rw [hΔ_eq]
    calc (c / π ^ 2) * Real.exp L ≤ (c / π ^ 2) * (33 / 32) := by gcongr
      _ = (33 / 32 : ℝ) * (c / π ^ 2) := by ring
  have hL_diff_lb : (32 / 33 : ℝ) * (2 * π ^ 2 * Kd / hankelBeta1) * c ^ (-(7 / 4 : ℝ)) ≤ L - L1 := by
    have hc_m74 : c ^ (-(3 / 4 : ℝ)) / c = c ^ (-(7 / 4 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hc0]; congr 1; norm_num
    have hgap_le : 2 * Kd / hankelBeta1 * c ^ (-(3 / 4 : ℝ)) ≤ Δ - fctWarpT1 h ε c := by linarith only [hΔ]
    calc (32 / 33 : ℝ) * (2 * π ^ 2 * Kd / hankelBeta1) * c ^ (-(7 / 4 : ℝ))
        = (2 * Kd / hankelBeta1 * c ^ (-(3 / 4 : ℝ))) / ((33 / 32 : ℝ) * (c / π ^ 2)) := by
          rw [← hc_m74]; field_simp [Real.pi_pos.ne', hc0.ne']
      _ ≤ (Δ - fctWarpT1 h ε c) / Δ :=
          div_le_div₀ (by positivity) hgap_le (by positivity) hΔ_ub
      _ ≤ L - L1 := hlog_lb
  have hslope := (hκ_bds hε hck hL1_lt hL_Sw).2.2.2
  have hu_diff_lb : (32 / 33 : ℝ) * (c ^ (2 / 3 : ℝ) / ceCs) * (L - L1) ≤
      winUhat K4 ε c (fctWarpAlpha h ε c) L1 - winUhat K4 ε c (fctWarpAlpha h ε c) L := by
    have h1 := (abs_le.mp hslope).1
    have h2 : C_s * c ^ (1 / 6 : ℝ) ≤ (1 / 33) * (c ^ (2 / 3 : ℝ) / ceCs) := by
      have hc23 : c ^ (1 / 6 : ℝ) = c ^ (2 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      rw [hc23, show C_s * (c ^ (2 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ))) = c ^ (2 / 3 : ℝ) * (C_s * c ^ (-(1 / 2 : ℝ))) by ring]
      calc c ^ (2 / 3 : ℝ) * (C_s * c ^ (-(1 / 2 : ℝ)))
          ≤ c ^ (2 / 3 : ℝ) * ((1 / 33) * (1 / ceCs)) := by gcongr
        _ = (1 / 33) * (c ^ (2 / 3 : ℝ) / ceCs) := by ring
    have hL10 : 0 ≤ L - L1 := (sub_pos.mpr hL1_lt).le
    nlinarith only [h1, h2, hL10]
  have hu_step : (15 / 8 : ℝ) * Kd * c ^ (-(13 / 12 : ℝ)) ≤
      winUhat K4 ε c (fctWarpAlpha h ε c) L1 - winUhat K4 ε c (fctWarpAlpha h ε c) L := by
    have hc23_74 : c ^ (2 / 3 : ℝ) * c ^ (-(7 / 4 : ℝ)) = c ^ (-(13 / 12 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hrat_pi : π ^ 2 / (ceCs * hankelBeta1) = 1 := by
      rw [ceCs_mul_hankelBeta1, div_self (by positivity)]
    have hnum : (15 / 8 : ℝ) ≤ (32 / 33) * ((32 / 33) * 2) := by norm_num
    have h32_nn : 0 ≤ (32 / 33 : ℝ) * (c ^ (2 / 3 : ℝ) / ceCs) := by
      have := ceCs_pos; positivity
    have hhb_nn : 0 ≤ (32 / 33 : ℝ) * (2 * π ^ 2 * Kd / hankelBeta1) * c ^ (-(7 / 4 : ℝ)) := by
      unfold hankelBeta1; positivity
    calc (15 / 8 : ℝ) * Kd * c ^ (-(13 / 12 : ℝ))
        ≤ ((32 / 33) * ((32 / 33) * 2)) * Kd * c ^ (-(13 / 12 : ℝ)) := by gcongr
      _ = (32 / 33) * (c ^ (2 / 3 : ℝ) / ceCs) *
            ((32 / 33) * (2 * π ^ 2 * Kd / hankelBeta1) * c ^ (-(7 / 4 : ℝ))) := by
          have : (c ^ (2 / 3 : ℝ) / ceCs) * ((2 * π ^ 2 * Kd / hankelBeta1) * c ^ (-(7 / 4 : ℝ))) =
              2 * Kd * (π ^ 2 / (ceCs * hankelBeta1)) * (c ^ (2 / 3 : ℝ) * c ^ (-(7 / 4 : ℝ))) := by ring
          rw [show (32 / 33 : ℝ) * (c ^ (2 / 3 : ℝ) / ceCs) * ((32 / 33) * (2 * π ^ 2 * Kd / hankelBeta1) *
              c ^ (-(7 / 4 : ℝ))) = (32 / 33) * (32 / 33) * ((c ^ (2 / 3 : ℝ) / ceCs) *
              ((2 * π ^ 2 * Kd / hankelBeta1) * c ^ (-(7 / 4 : ℝ)))) by ring,
            this, hrat_pi, hc23_74]; ring
      _ ≤ (32 / 33) * (c ^ (2 / 3 : ℝ) / ceCs) * (L - L1) :=
          mul_le_mul_of_nonneg_left hL_diff_lb h32_nn
      _ ≤ _ := hu_diff_lb
  have hu1_e := (hu_err hε hcu).1
  have hu1_1312 : |winUhat K4 ε c (fctWarpAlpha h ε c) L1 - airyZero 1| ≤
      (1 / 8 : ℝ) * Kd * c ^ (-(13 / 12 : ℝ)) := by
    have hc43 : c ^ (-(4 / 3 : ℝ)) = c ^ (-(1 / 4 : ℝ)) * c ^ (-(13 / 12 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc |winUhat K4 ε c (fctWarpAlpha h ε c) L1 - airyZero 1|
        ≤ C_u * c ^ (-(4 / 3 : ℝ)) := hu1_e
      _ = (C_u * c ^ (-(1 / 4 : ℝ))) * c ^ (-(13 / 12 : ℝ)) := by rw [hc43]; ring
      _ ≤ ((1 / 8) * Kd) * c ^ (-(13 / 12 : ℝ)) := by gcongr
      _ = (1 / 8 : ℝ) * Kd * c ^ (-(13 / 12 : ℝ)) := by ring
  linarith only [hu_step, (abs_le.mp hu1_1312).2]

/-- info: 'FormalResearch.SignUncertainty.win_arg_g1_sub_uhat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_arg_g1_sub_uhat

/-- info: 'FormalResearch.SignUncertainty.win_vhat_sub_a1_of_delta_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_vhat_sub_a1_of_delta_ge

end FormalResearch.SignUncertainty
