/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpLeftFarIbp

/-!
# Left-tail oscillatory error: Macro and Far bound (`3 * physDelta c ≤ L`, `fct:warp-asymp`)

Leaf module for `FctPhysicalPositive.lean`:
* `warpLeftTailDensity_far_bound`: uniformly for all `c₀ ≤ c`, `ε = ±1`, and `ξ > 0` with
  `3 * FctSym.physDelta c ≤ Real.log (π² * ξ)`,
  `|warpLeftTailDensity h ε c ξ| ≤ C * c ^ (-2 : ℝ) * (Real.log (π² * ξ)) ^ (-(3 / 2 : ℝ))`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff Nat
open FormalResearch.Analysis FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctCuspEdge

namespace FormalResearch.SignUncertainty

private lemma vdc1_Ioi_edgePhi_sign {a L c lam M_bd V_bd σ : ℝ} (ha : 0 < a) (hc : 0 < c) (hlam : 0 < lam)
    (hσ : σ = 1 ∨ σ = -1) {amp : ℝ → ℂ}
    (hCD : ContDiffOn ℝ 1 amp (Ioi 0))
    (hInt : IntegrableOn (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))) (Ioi a))
    (hLam : ∀ x ∈ Ici a, lam ≤ |edgePhiDeriv L x|)
    (hM : ∀ x ∈ Ici a, ‖amp x‖ ≤ M_bd)
    (hV : ∀ T : ℝ, a ≤ T → ∫ x in Icc a T, ‖deriv amp x‖ ≤ V_bd) :
    ‖∫ τ in Ioi a, amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))‖ ≤
      3 * (M_bd + V_bd) / (c * lam) := by
  have htend := intervalIntegral_tendsto_integral_Ioi a hInt tendsto_id
  refine le_of_tendsto htend.norm ?_
  filter_upwards [eventually_ge_atTop a] with T hT
  exact vdc1_Icc_edgePhi_sign hT ha hc hlam hσ hCD (fun x hx => hLam x hx.1)
    (fun x hx => hM x hx.1) (hV T hT)

private lemma norm_sum3_le {a b c : ℂ} : ‖a + (b + c)‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
  ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))).trans_eq (add_assoc _ _ _).symm

private lemma leftTail_Ioi_far_small {K4 : ℝ} {h : FctWarpSolveStmt K4}
    {M0 V0 ε c ξ σ L : ℝ} (hM0 : 0 ≤ M0) (hV0 : 0 ≤ V0) (hc1 : 1 ≤ c) (hcpos : 0 < c) (hσ : σ = 1 ∨ σ = -1)
    (hL_pos : 0 < L) (hL1 : L ≤ 1)
    (hr_s2 : (c * L)⁻¹ ≤ 3 / 4 * tau0 L)
    (hCD_pos : ContDiffOn ℝ 1 (fun τ => warpAmpLeft h ε c ξ (σ * τ)) (Ioi 0))
    (hInt_r : IntegrableOn (fun τ : ℝ => warpAmpLeft h ε c ξ (σ * τ) *
      Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))) (Ioi ((c * L)⁻¹)))
    (hM_sig : ∀ x ∈ Ici ((c * L)⁻¹), ‖warpAmpLeft h ε c ξ (σ * x)‖ ≤ M0 * c⁻¹)
    (hV_sig : ∀ a b : ℝ, (c * L)⁻¹ ≤ a → a ≤ b →
      ∫ x in Icc a b, ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖ ≤ V0 * c⁻¹) :
    ‖∫ τ in Ioi ((c * L)⁻¹),
        warpAmpLeft h ε c ξ (σ * τ) *
          Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))‖ ≤
      ((96 + 96) * (M0 + V0) + 8 * (M0 + V0) / Real.sqrt (3 / 40)) *
        c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
  set r : ℝ := (c * L)⁻¹
  have hr_pos : 0 < r := by positivity
  set s2 : ℝ := 3 / 4 * tau0 L
  set s3 : ℝ := 3 / 2 * tau0 L
  have htau_pos : 0 < tau0 L := tau0_pos hL_pos
  have hs2_pos : 0 < s2 := by positivity
  have hs2_s3 : s2 ≤ s3 := by dsimp [s2, s3]; linarith
  have hs3_pos : 0 < s3 := lt_of_lt_of_le hs2_pos hs2_s3
  set f : ℝ → ℂ := fun τ => warpAmpLeft h ε c ξ (σ * τ) *
    Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))
  have hsplit1 := integral_Ioi_eq_interval_add_Ioi hr_s2 hInt_r
  have hInt_s2 : IntegrableOn f (Ioi s2) := hInt_r.mono_set (Ioi_subset_Ioi hr_s2)
  have hsplit2 := integral_Ioi_eq_interval_add_Ioi hs2_s3 hInt_s2
  have hInt_s3 : IntegrableOn f (Ioi s3) := hInt_s2.mono_set (Ioi_subset_Ioi hs2_s3)
  have hc_2_32 : c ^ (-2 : ℝ) ≤ c ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hL_1_32 : L⁻¹ ≤ L ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one L]
    exact Real.rpow_le_rpow_of_exponent_ge hL_pos hL1 (by norm_num)
  have hc2_simp : c⁻¹ / (c * (1 / 32 * L)) = 32 * c ^ (-2 : ℝ) * L⁻¹ := by
    have hc2 : c⁻¹ / c = c ^ (-2 : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
    calc c⁻¹ / (c * (1 / 32 * L)) = 32 * (c⁻¹ / c) * L⁻¹ := by ring
      _ = 32 * c ^ (-2 : ℝ) * L⁻¹ := by rw [hc2]
  have h_edge_ge : ∀ x : ℝ, 0 ≤ x → L - hankelEdgeM x ≤ |edgePhiDeriv L x| := fun x hx0 => by
    rw [edgePhiDeriv_eq_sub_hankelEdgeM hx0]; exact le_abs_self _
  have h_edge_ge' : ∀ x : ℝ, 0 ≤ x → hankelEdgeM x - L ≤ |edgePhiDeriv L x| := fun x hx0 => by
    rw [edgePhiDeriv_eq_sub_hankelEdgeM hx0, abs_sub_comm]; exact le_abs_self _
  have h1_bd : ‖∫ τ in r..s2, f τ‖ ≤ 96 * (M0 + V0) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have hv := vdc1_Icc_edgePhi_sign hr_s2 hr_pos hcpos (by positivity : 0 < 1 / 32 * L) hσ
      hCD_pos (fun x hx => (hankelEdgeM_diff_small_inner hL_pos hL1 (le_trans hr_pos.le hx.1) hx.2).trans
        (h_edge_ge x (le_trans hr_pos.le hx.1)))
      (fun x hx => hM_sig x hx.1) (hV_sig r s2 le_rfl hr_s2)
    refine hv.trans ?_
    calc 3 * (M0 * c⁻¹ + V0 * c⁻¹) / (c * (1 / 32 * L))
        = 3 * (M0 + V0) * (c⁻¹ / (c * (1 / 32 * L))) := by ring
      _ = 96 * (M0 + V0) * (c ^ (-2 : ℝ) * L⁻¹) := by rw [hc2_simp]; ring
      _ ≤ 96 * (M0 + V0) * (c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = 96 * (M0 + V0) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by ring
  have h3_bd : ‖∫ τ in Ioi s3, f τ‖ ≤ 96 * (M0 + V0) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have hv := vdc1_Ioi_edgePhi_sign hs3_pos hcpos (by positivity : 0 < 1 / 32 * L) hσ
      hCD_pos hInt_s3 (fun x hx => (hankelEdgeM_diff_small_outer hL_pos hL1 hx).2.2.trans
        (h_edge_ge' x (le_trans hs3_pos.le hx)))
      (fun x hx => hM_sig x (hr_s2.trans (hs2_s3.trans hx)))
      (fun T hT => hV_sig s3 T (hr_s2.trans hs2_s3) hT)
    refine hv.trans ?_
    calc 3 * (M0 * c⁻¹ + V0 * c⁻¹) / (c * (1 / 32 * L))
        = 3 * (M0 + V0) * (c⁻¹ / (c * (1 / 32 * L))) := by ring
      _ = 96 * (M0 + V0) * (c ^ (-2 : ℝ) * L⁻¹) := by rw [hc2_simp]; ring
      _ ≤ 96 * (M0 + V0) * (c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = 96 * (M0 + V0) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by ring
  have h2_bd : ‖∫ τ in s2..s3, f τ‖ ≤
      (8 * (M0 + V0) / Real.sqrt (3 / 40)) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have htau_b := tau0_small_bounds hL_pos hL1
    have hLam2 : ∀ x ∈ Icc s2 s3, 3 / 40 * Real.sqrt L ≤ |edgePhiDeriv2 x| := by
      intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le hs2_pos hx.1
      rw [abs_edgePhiDeriv2_eq_hankelEdgeM' hx_pos]
      have hx_lo : 3 / 4 * Real.sqrt L ≤ x :=
        (mul_le_mul_of_nonneg_left htau_b.1 (by norm_num)).trans hx.1
      have hx_hi : x ≤ 3 := hx.2.trans (by dsimp [s3]; linarith [htau_b.2.2])
      have hden : 1 + x ^ 2 ≤ 10 := by nlinarith
      calc 3 / 40 * Real.sqrt L = (3 / 4 * Real.sqrt L) / 10 := by ring
        _ ≤ x / (1 + x ^ 2) := div_le_div₀ (by positivity) hx_lo (by positivity) hden
        _ ≤ hankelEdgeM' x := (hankelEdgeM'_bounds hx_pos).1
    have hlam_pos : 0 < 3 / 40 * Real.sqrt L := mul_pos (by norm_num) (Real.sqrt_pos.mpr hL_pos)
    have hv := vdc2_Icc_edgePhi_sign (L := L) hs2_s3 hs2_pos hcpos hlam_pos hσ hCD_pos hLam2
      (fun x hx => hM_sig x (hr_s2.trans hx.1)) (hV_sig s2 s3 hr_s2 hs2_s3)
    have hrt : Real.sqrt (c * (3 / 40 * Real.sqrt L)) =
        Real.sqrt (3 / 40) * c ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) := by
      rw [mul_left_comm, Real.sqrt_mul (by norm_num), Real.sqrt_mul hcpos.le,
        Real.sqrt_eq_rpow c, Real.sqrt_eq_rpow L, Real.sqrt_eq_rpow (L ^ (1 / 2 : ℝ)),
        ← Real.rpow_mul hL_pos.le, show (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 by norm_num]
      ring
    have hpow : c⁻¹ / (Real.sqrt (3 / 40) * c ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ)) =
        (Real.sqrt (3 / 40))⁻¹ * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ)) := by
      have hc32 : c⁻¹ / c ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_neg hcpos.le, ← Real.rpow_add hcpos]
        congr 1; norm_num
      rw [div_eq_mul_inv, mul_inv, mul_inv, ← Real.rpow_neg hL_pos.le]
      calc c⁻¹ * ((Real.sqrt (3 / 40))⁻¹ * (c ^ (1 / 2 : ℝ))⁻¹ * L ^ (-(1 / 4 : ℝ)))
          = (Real.sqrt (3 / 40))⁻¹ * (c⁻¹ / c ^ (1 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ)) := by
            rw [div_eq_mul_inv]; ring
        _ = (Real.sqrt (3 / 40))⁻¹ * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ)) := by rw [hc32]
    have hL14_le : L ^ (-(1 / 4 : ℝ)) ≤ L ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hL_pos hL1 (by norm_num)
    refine hv.trans ?_
    calc 8 * (M0 * c⁻¹ + V0 * c⁻¹) / Real.sqrt (c * (3 / 40 * Real.sqrt L))
        = 8 * (M0 + V0) * (c⁻¹ / (Real.sqrt (3 / 40) * c ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ))) := by
          rw [hrt]; ring
      _ = (8 * (M0 + V0) / Real.sqrt (3 / 40)) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ)) := by
          rw [hpow, div_eq_mul_inv]; ring
      _ ≤ (8 * (M0 + V0) / Real.sqrt (3 / 40)) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
          gcongr
  rw [hsplit1, hsplit2]
  exact norm_sum3_le.trans ((add_le_add (add_le_add h1_bd h2_bd) h3_bd).trans_eq (by ring))

private lemma leftTail_Ioi_far_mid {K4 : ℝ} {h : FctWarpSolveStmt K4}
    {M0 V0 ε c ξ σ L : ℝ} (hM0 : 0 ≤ M0) (hV0 : 0 ≤ V0) (hc1 : 1 ≤ c) (hcpos : 0 < c) (hσ : σ = 1 ∨ σ = -1)
    (hL1 : 1 ≤ L) (hL2 : L ≤ 2)
    (hr_s2 : (c * L)⁻¹ ≤ 3 / 4 * tau0 L)
    (hCD_pos : ContDiffOn ℝ 1 (fun τ => warpAmpLeft h ε c ξ (σ * τ)) (Ioi 0))
    (hInt_r : IntegrableOn (fun τ : ℝ => warpAmpLeft h ε c ξ (σ * τ) *
      Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))) (Ioi ((c * L)⁻¹)))
    (hM_sig : ∀ x ∈ Ici ((c * L)⁻¹), ‖warpAmpLeft h ε c ξ (σ * x)‖ ≤ M0 * c⁻¹)
    (hV_sig : ∀ a b : ℝ, (c * L)⁻¹ ≤ a → a ≤ b →
      ∫ x in Icc a b, ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖ ≤ V0 * c⁻¹) :
    ‖∫ τ in Ioi ((c * L)⁻¹),
        warpAmpLeft h ε c ξ (σ * τ) *
          Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))‖ ≤
      (((96 + 36) * (M0 + V0) + 8 * (M0 + V0) / Real.sqrt (3 / 656)) * 2 ^ (3 / 2 : ℝ)) *
        c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
  set r : ℝ := (c * L)⁻¹
  have hr_pos : 0 < r := by positivity
  have hL_pos : 0 < L := by linarith
  set s2 : ℝ := 3 / 4 * tau0 L
  set s3 : ℝ := 3 / 2 * tau0 L
  have htau_pos : 0 < tau0 L := tau0_pos hL_pos
  have hs2_pos : 0 < s2 := by positivity
  have hs2_s3 : s2 ≤ s3 := by dsimp [s2, s3]; linarith
  have hs3_pos : 0 < s3 := lt_of_lt_of_le hs2_pos hs2_s3
  set f : ℝ → ℂ := fun τ => warpAmpLeft h ε c ξ (σ * τ) *
    Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))
  have hsplit1 := integral_Ioi_eq_interval_add_Ioi hr_s2 hInt_r
  have hInt_s2 : IntegrableOn f (Ioi s2) := hInt_r.mono_set (Ioi_subset_Ioi hr_s2)
  have hsplit2 := integral_Ioi_eq_interval_add_Ioi hs2_s3 hInt_s2
  have hInt_s3 : IntegrableOn f (Ioi s3) := hInt_s2.mono_set (Ioi_subset_Ioi hs2_s3)
  have hc_2_32 : c ^ (-2 : ℝ) ≤ c ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have h1_L32 : (1 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by
    have h1 : (2 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ L ^ (-(3 / 2 : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_neg hL_pos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hL_pos _) (Real.rpow_le_rpow hL_pos.le hL2 (by norm_num))
    have h2 : (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    calc (1 : ℝ) = 2 ^ (3 / 2 : ℝ) * 2 ^ (-(3 / 2 : ℝ)) := h2.symm
      _ ≤ 2 ^ (3 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by gcongr
  have hc2_eq : c⁻¹ / c = c ^ (-2 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
  have h_edge_ge : ∀ x : ℝ, 0 ≤ x → L - hankelEdgeM x ≤ |edgePhiDeriv L x| := fun x hx0 => by
    rw [edgePhiDeriv_eq_sub_hankelEdgeM hx0]; exact le_abs_self _
  have h_edge_ge' : ∀ x : ℝ, 0 ≤ x → hankelEdgeM x - L ≤ |edgePhiDeriv L x| := fun x hx0 => by
    rw [edgePhiDeriv_eq_sub_hankelEdgeM hx0, abs_sub_comm]; exact le_abs_self _
  have h1_bd : ‖∫ τ in r..s2, f τ‖ ≤
      96 * (M0 + V0) * 2 ^ (3 / 2 : ℝ) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have hv := vdc1_Icc_edgePhi_sign hr_s2 hr_pos hcpos (by norm_num : 0 < (1 / 32 : ℝ)) hσ
      hCD_pos (fun x hx => (hankelEdgeM_diff_large_inner hL1 (le_trans hr_pos.le hx.1) hx.2).trans
        (h_edge_ge x (le_trans hr_pos.le hx.1)))
      (fun x hx => hM_sig x hx.1) (hV_sig r s2 le_rfl hr_s2)
    refine hv.trans ?_
    calc 3 * (M0 * c⁻¹ + V0 * c⁻¹) / (c * (1 / 32))
        = 96 * (M0 + V0) * (c⁻¹ / c) := by ring
      _ = 96 * (M0 + V0) * c ^ (-2 : ℝ) * 1 := by rw [hc2_eq, mul_one]
      _ ≤ 96 * (M0 + V0) * c ^ (-(3 / 2 : ℝ)) * (2 ^ (3 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = 96 * (M0 + V0) * 2 ^ (3 / 2 : ℝ) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by ring
  have h3_bd : ‖∫ τ in Ioi s3, f τ‖ ≤
      36 * (M0 + V0) * 2 ^ (3 / 2 : ℝ) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have hv := vdc1_Ioi_edgePhi_sign hs3_pos hcpos (by norm_num : 0 < (1 / 12 : ℝ)) hσ
      hCD_pos hInt_s3 (fun x hx => (hankelEdgeM_diff_large_outer hL1 hx).trans
        (h_edge_ge' x (le_trans hs3_pos.le hx)))
      (fun x hx => hM_sig x (hr_s2.trans (hs2_s3.trans hx)))
      (fun T hT => hV_sig s3 T (hr_s2.trans hs2_s3) hT)
    refine hv.trans ?_
    calc 3 * (M0 * c⁻¹ + V0 * c⁻¹) / (c * (1 / 12))
        = 36 * (M0 + V0) * (c⁻¹ / c) := by ring
      _ = 36 * (M0 + V0) * c ^ (-2 : ℝ) * 1 := by rw [hc2_eq, mul_one]
      _ ≤ 36 * (M0 + V0) * c ^ (-(3 / 2 : ℝ)) * (2 ^ (3 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = 36 * (M0 + V0) * 2 ^ (3 / 2 : ℝ) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by ring
  have h2_bd : ‖∫ τ in s2..s3, f τ‖ ≤
      (8 * (M0 + V0) / Real.sqrt (3 / 656)) * 2 ^ (3 / 2 : ℝ) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have htau_b := tau0_large_bounds hL1
    have hLam2 : ∀ x ∈ Icc s2 s3, 3 / 656 ≤ |edgePhiDeriv2 x| := by
      intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le hs2_pos hx.1
      rw [abs_edgePhiDeriv2_eq_hankelEdgeM' hx_pos]
      have he_lo : (2 : ℝ) ≤ Real.exp L := by
        have := Real.exp_one_gt_d9; linarith [Real.exp_le_exp.mpr hL1]
      have he_hi : Real.exp L ≤ 9 := by
        have h1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
        have h2 : Real.exp L ≤ Real.exp 2 := Real.exp_le_exp.mpr hL2
        have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 : ℝ)]
      have hpi_lo : (3 : ℝ) ≤ π := Real.pi_gt_three.le
      have hpi_hi : π ≤ 4 := Real.pi_lt_four.le
      have hx_lo : 3 / 8 ≤ x := by
        have h1 : 1 / 2 ≤ tau0 L := by
          calc (1 / 2 : ℝ) = 2 / 4 := by norm_num
            _ ≤ Real.exp L / π := div_le_div₀ (by positivity) he_lo Real.pi_pos hpi_hi
            _ ≤ tau0 L := htau_b.1
        exact (by dsimp [s2]; linarith : (3 / 8 : ℝ) ≤ s2).trans hx.1
      have hx_hi : x ≤ 9 := by
        have h1 : tau0 L ≤ 6 := by
          calc tau0 L ≤ 2 * Real.exp L / π := htau_b.2
            _ ≤ 2 * 9 / 3 := div_le_div₀ (by positivity) (by linarith) (by positivity) hpi_lo
            _ = 6 := by norm_num
        exact hx.2.trans (by dsimp [s3]; linarith)
      have hden : 1 + x ^ 2 ≤ 82 := by nlinarith
      calc (3 / 656 : ℝ) = (3 / 8) / 82 := by norm_num
        _ ≤ x / (1 + x ^ 2) := div_le_div₀ (by positivity) hx_lo (by positivity) hden
        _ ≤ hankelEdgeM' x := (hankelEdgeM'_bounds hx_pos).1
    have hv := vdc2_Icc_edgePhi_sign (L := L) hs2_s3 hs2_pos hcpos (by norm_num : 0 < (3 / 656 : ℝ)) hσ
      hCD_pos hLam2 (fun x hx => hM_sig x (hr_s2.trans hx.1)) (hV_sig s2 s3 hr_s2 hs2_s3)
    have hrt : Real.sqrt (c * (3 / 656)) = Real.sqrt (3 / 656) * c ^ (1 / 2 : ℝ) := by
      rw [mul_comm, Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow c]
    have hc32 : c⁻¹ / c ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_neg hcpos.le, ← Real.rpow_add hcpos]
      congr 1; norm_num
    refine hv.trans ?_
    calc 8 * (M0 * c⁻¹ + V0 * c⁻¹) / Real.sqrt (c * (3 / 656))
        = (8 * (M0 + V0) / Real.sqrt (3 / 656)) * (c⁻¹ / c ^ (1 / 2 : ℝ)) * 1 := by
          rw [hrt]; ring
      _ ≤ (8 * (M0 + V0) / Real.sqrt (3 / 656)) * c ^ (-(3 / 2 : ℝ)) *
            (2 ^ (3 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ))) := by rw [hc32]; gcongr
      _ = (8 * (M0 + V0) / Real.sqrt (3 / 656)) * 2 ^ (3 / 2 : ℝ) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by ring
  rw [hsplit1, hsplit2]
  exact norm_sum3_le.trans ((add_le_add (add_le_add h1_bd h2_bd) h3_bd).trans_eq (by ring))

private lemma leftTail_Ioi_far_large {K4 : ℝ} {h : FctWarpSolveStmt K4}
    {M1 V1 C_ibp ε c ξ σ L : ℝ} (hM1 : 0 ≤ M1) (hV1 : 0 ≤ V1) (hc1 : 1 ≤ c) (hcpos : 0 < c) (hσ : σ = 1 ∨ σ = -1)
    (hL2 : 2 ≤ L)
    (hr16 : (c * L)⁻¹ ≤ 1 / 16)
    (hCD_pos : ContDiffOn ℝ 1 (fun τ => warpAmpLeft h ε c ξ (σ * τ)) (Ioi 0))
    (hInt_r : IntegrableOn (fun τ : ℝ => warpAmpLeft h ε c ξ (σ * τ) *
      Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))) (Ioi ((c * L)⁻¹)))
    (h0_bd : ‖∫ τ in (c * L)⁻¹..(tau0 (L / 2)),
      warpAmpLeft h ε c ξ (σ * τ) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))‖ ≤
      C_ibp * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)))
    (hME : ∀ a : ℝ, 1 / 16 ≤ a →
      (∀ x ∈ Ici a, ‖warpAmpLeft h ε c ξ (σ * x)‖ ≤ M1 * c⁻¹ * Real.exp (-(π / 2 * a))) ∧
      (∀ T : ℝ, a ≤ T → ∫ x in Icc a T, ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖ ≤
        V1 * c⁻¹ * Real.exp (-(π / 2 * a)))) :
    ‖∫ τ in Ioi ((c * L)⁻¹),
        warpAmpLeft h ε c ξ (σ * τ) *
          Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))‖ ≤
      (C_ibp + (96 * 48 + 36 * 48) * (M1 + V1) + 800 * Real.sqrt 3 * (M1 + V1)) *
        c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
  have hL1 : 1 ≤ L := by linarith
  have hL_pos : 0 < L := by linarith
  set r : ℝ := (c * L)⁻¹
  set s1 : ℝ := tau0 (L / 2)
  set s2 : ℝ := 3 / 4 * tau0 L
  set s3 : ℝ := 3 / 2 * tau0 L
  obtain ⟨hs1_16, hs1_s2⟩ := s1_le_s2 hL2
  have hs1_pos : 0 < s1 := lt_of_lt_of_le (by norm_num) hs1_16
  have hr_s1 : r ≤ s1 := hr16.trans hs1_16
  have htau_pos : 0 < tau0 L := tau0_pos hL_pos
  have hs2_pos : 0 < s2 := by positivity
  have hs2_s3 : s2 ≤ s3 := by dsimp [s2, s3]; linarith
  have hs3_pos : 0 < s3 := lt_of_lt_of_le hs2_pos hs2_s3
  have hs1_s3 : s1 ≤ s3 := hs1_s2.trans hs2_s3
  set f : ℝ → ℂ := fun τ => warpAmpLeft h ε c ξ (σ * τ) *
    Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (σ * τ) : ℂ))
  have hsplit_r := integral_Ioi_eq_interval_add_Ioi hr_s1 hInt_r
  have hInt_s1 : IntegrableOn f (Ioi s1) := hInt_r.mono_set (Ioi_subset_Ioi hr_s1)
  have hsplit_1 := integral_Ioi_eq_interval_add_Ioi hs1_s2 hInt_s1
  have hInt_s2 : IntegrableOn f (Ioi s2) := hInt_s1.mono_set (Ioi_subset_Ioi hs1_s2)
  have hsplit_2 := integral_Ioi_eq_interval_add_Ioi hs2_s3 hInt_s2
  have hInt_s3 : IntegrableOn f (Ioi s3) := hInt_s2.mono_set (Ioi_subset_Ioi hs2_s3)
  obtain ⟨hME_s1, hVE_s1⟩ := hME s1 hs1_16
  have hs2_16 : 1 / 16 ≤ s2 := hs1_16.trans hs1_s2
  obtain ⟨hME_s2, hVE_s2⟩ := hME s2 hs2_16
  have hs3_16 : 1 / 16 ≤ s3 := hs2_16.trans hs2_s3
  obtain ⟨hME_s3, hVE_s3⟩ := hME s3 hs3_16
  have hV_exp_sub : ∀ (a0 a b : ℝ) (ha0 : 1 / 16 ≤ a0)
      (hVe : ∀ T, a0 ≤ T → ∫ x in Icc a0 T, ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖ ≤
        V1 * c⁻¹ * Real.exp (-(π / 2 * a0))),
      a0 ≤ a → a ≤ b →
      ∫ x in Icc a b, ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖ ≤
        V1 * c⁻¹ * Real.exp (-(π / 2 * a0)) := by
    intro a0 a b ha0 hVe ha0a hab
    have ha0_pos : 0 < a0 := lt_of_lt_of_le (by norm_num) ha0
    have hIcc_pos : ∀ x ∈ Icc a0 b, 0 < x := fun x hx => lt_of_lt_of_le ha0_pos hx.1
    have hc0' : ContinuousOn (deriv (fun t => warpAmpLeft h ε c ξ (σ * t))) (Ioi 0) :=
      (hCD_pos.derivWithin isOpen_Ioi.uniqueDiffOn (m := 0) (by norm_num)).continuousOn.congr
        fun t ht => (derivWithin_of_isOpen isOpen_Ioi ht).symm
    have hint_a0b : IntegrableOn (fun x => ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖) (Icc a0 b) :=
      (hc0'.norm.mono fun x hx => hIcc_pos x hx).integrableOn_Icc
    exact (setIntegral_mono_set hint_a0b (Eventually.of_forall fun _ => norm_nonneg _)
      (Icc_subset_Icc ha0a le_rfl).eventuallySubset).trans (hVe b (ha0a.trans hab))
  have hc2_eq : c⁻¹ / c = c ^ (-2 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
  have hc_2_32 : c ^ (-2 : ℝ) ≤ c ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hexp_s1 := exp_neg_half_tau0_half_le hL2
  have hexp_s3_s1 : Real.exp (-(π / 2 * s3)) ≤ Real.exp (-(π / 2 * s1)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hs1_s3 (by positivity)))
  have h_edge_ge : ∀ x : ℝ, 0 ≤ x → L - hankelEdgeM x ≤ |edgePhiDeriv L x| := fun x hx0 => by
    rw [edgePhiDeriv_eq_sub_hankelEdgeM hx0]; exact le_abs_self _
  have h_edge_ge' : ∀ x : ℝ, 0 ≤ x → hankelEdgeM x - L ≤ |edgePhiDeriv L x| := fun x hx0 => by
    rw [edgePhiDeriv_eq_sub_hankelEdgeM hx0, abs_sub_comm]; exact le_abs_self _
  have h1_bd : ‖∫ τ in s1..s2, f τ‖ ≤
      96 * 48 * (M1 + V1) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have hv := vdc1_Icc_edgePhi_sign hs1_s2 hs1_pos hcpos (by norm_num : 0 < (1 / 32 : ℝ)) hσ
      hCD_pos (fun x hx => (hankelEdgeM_diff_large_inner hL1 (le_trans hs1_pos.le hx.1) hx.2).trans
        (h_edge_ge x (le_trans hs1_pos.le hx.1)))
      (fun x hx => hME_s1 x hx.1) (hV_exp_sub s1 s1 s2 hs1_16 hVE_s1 le_rfl hs1_s2)
    refine hv.trans ?_
    calc 3 * (M1 * c⁻¹ * Real.exp (-(π / 2 * s1)) + V1 * c⁻¹ * Real.exp (-(π / 2 * s1))) / (c * (1 / 32))
        = 96 * (M1 + V1) * (c⁻¹ / c) * Real.exp (-(π / 2 * s1)) := by ring
      _ ≤ 96 * (M1 + V1) * c ^ (-(3 / 2 : ℝ)) * (48 * L ^ (-(3 / 2 : ℝ))) := by
          rw [hc2_eq]; gcongr
      _ = 96 * 48 * (M1 + V1) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by ring
  have h3_bd : ‖∫ τ in Ioi s3, f τ‖ ≤
      36 * 48 * (M1 + V1) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have hv := vdc1_Ioi_edgePhi_sign hs3_pos hcpos (by norm_num : 0 < (1 / 12 : ℝ)) hσ
      hCD_pos hInt_s3 (fun x hx => (hankelEdgeM_diff_large_outer hL1 hx).trans
        (h_edge_ge' x (le_trans hs3_pos.le hx)))
      hME_s3 (fun T hT => hVE_s3 T hT)
    refine hv.trans ?_
    have hexp_s3_bd : Real.exp (-(π / 2 * s3)) ≤ 48 * L ^ (-(3 / 2 : ℝ)) := hexp_s3_s1.trans hexp_s1
    calc 3 * (M1 * c⁻¹ * Real.exp (-(π / 2 * s3)) + V1 * c⁻¹ * Real.exp (-(π / 2 * s3))) / (c * (1 / 12))
        = 36 * (M1 + V1) * (c⁻¹ / c) * Real.exp (-(π / 2 * s3)) := by ring
      _ ≤ 36 * (M1 + V1) * c ^ (-(3 / 2 : ℝ)) * (48 * L ^ (-(3 / 2 : ℝ))) := by
          rw [hc2_eq]; gcongr
      _ = 36 * 48 * (M1 + V1) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by ring
  have h2_bd : ‖∫ τ in s2..s3, f τ‖ ≤
      800 * Real.sqrt 3 * (M1 + V1) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have htau_b := tau0_large_bounds hL1
    have hLam2 : ∀ x ∈ Icc s2 s3, 1 / (3 * Real.exp L) ≤ |edgePhiDeriv2 x| := by
      intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le hs2_pos hx.1
      rw [abs_edgePhiDeriv2_eq_hankelEdgeM' hx_pos]
      have hx_ge1 : 1 ≤ x := by
        have he2 : (6 : ℝ) ≤ Real.exp L := by
          have h1 : (2.7 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
          have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
          have h3 : (7 : ℝ) ≤ Real.exp 2 := by nlinarith
          exact (by linarith : (6 : ℝ) ≤ 7).trans (h3.trans (Real.exp_le_exp.mpr hL2))
        have hpi_hi : π ≤ 4 := Real.pi_lt_four.le
        have : 1 ≤ s2 := by
          dsimp [s2]
          have : 3 / 4 * (6 / 4) ≤ 3 / 4 * (Real.exp L / π) :=
            mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity) he2 Real.pi_pos hpi_hi) (by norm_num)
          linarith [htau_b.1]
        exact this.trans hx.1
      have hx_hi : x ≤ 3 / 2 * Real.exp L := by
        have htau_hi : tau0 L ≤ Real.exp L := by
          have hpi_lo : 2 ≤ π := by linarith [Real.pi_gt_three]
          calc tau0 L ≤ 2 * Real.exp L / π := htau_b.2
            _ ≤ 2 * Real.exp L / 2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hpi_lo
            _ = Real.exp L := by ring
        exact hx.2.trans (by dsimp [s3]; linarith)
      have h1x2 : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith
      have hx_div : x / (1 + x ^ 2) ≥ x / (2 * x ^ 2) :=
        div_le_div_of_nonneg_left hx_pos.le (by positivity) h1x2
      have h2x : x / (2 * x ^ 2) = (2 * x)⁻¹ := by field_simp [hx_pos.ne']
      have h3exp : (3 * Real.exp L)⁻¹ ≤ (2 * x)⁻¹ :=
        inv_anti₀ (by positivity) (by linarith)
      calc 1 / (3 * Real.exp L) = (3 * Real.exp L)⁻¹ := one_div _
        _ ≤ (2 * x)⁻¹ := h3exp
        _ = x / (2 * x ^ 2) := h2x.symm
        _ ≤ x / (1 + x ^ 2) := hx_div
        _ ≤ hankelEdgeM' x := (hankelEdgeM'_bounds hx_pos).1
    have hlam_pos : 0 < 1 / (3 * Real.exp L) := by positivity
    have hv := vdc2_Icc_edgePhi_sign (L := L) hs2_s3 hs2_pos hcpos hlam_pos hσ hCD_pos hLam2
      (fun x hx => hME_s2 x hx.1) (hV_exp_sub s2 s2 s3 hs2_16 hVE_s2 le_rfl hs2_s3)
    have hrt : (Real.sqrt (c * (1 / (3 * Real.exp L))))⁻¹ =
        Real.sqrt 3 * c ^ (-(1 / 2 : ℝ)) * Real.exp (L / 2) := by
      have hexpL_rt : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
        rw [← Real.sqrt_sq (Real.exp_pos (L / 2)).le, ← Real.exp_nat_mul]; congr 2; ring
      rw [mul_one_div, Real.sqrt_div hcpos.le, Real.sqrt_mul (by norm_num), inv_div,
        Real.sqrt_eq_rpow c, hexpL_rt, div_eq_mul_inv, ← Real.rpow_neg hcpos.le]
      ring
    have hc32 : c⁻¹ * c ^ (-(1 / 2 : ℝ)) = c ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
    have hexp_mul := exp_half_L_mul_exp_s2_le hL2
    refine hv.trans ?_
    calc 8 * (M1 * c⁻¹ * Real.exp (-(π / 2 * s2)) + V1 * c⁻¹ * Real.exp (-(π / 2 * s2))) /
          Real.sqrt (c * (1 / (3 * Real.exp L)))
        = 8 * (M1 + V1) * c⁻¹ * Real.exp (-(π / 2 * s2)) *
            (Real.sqrt (c * (1 / (3 * Real.exp L))))⁻¹ := by rw [div_eq_mul_inv]; ring
      _ = 8 * Real.sqrt 3 * (M1 + V1) * (c⁻¹ * c ^ (-(1 / 2 : ℝ))) *
            (Real.exp (L / 2) * Real.exp (-(π / 2 * s2))) := by rw [hrt]; ring
      _ ≤ 8 * Real.sqrt 3 * (M1 + V1) * c ^ (-(3 / 2 : ℝ)) * (100 * L ^ (-(3 / 2 : ℝ))) := by
          rw [hc32]; gcongr
      _ = 800 * Real.sqrt 3 * (M1 + V1) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by ring
  rw [hsplit_r, hsplit_1, hsplit_2]
  have hsum4 : ‖(∫ τ in r..s1, f τ) + ((∫ τ in s1..s2, f τ) + ((∫ τ in s2..s3, f τ) + ∫ τ in Ioi s3, f τ))‖ ≤
      ‖∫ τ in r..s1, f τ‖ + ‖∫ τ in s1..s2, f τ‖ + ‖∫ τ in s2..s3, f τ‖ + ‖∫ τ in Ioi s3, f τ‖ := by
    calc _ ≤ ‖∫ τ in r..s1, f τ‖ + ‖(∫ τ in s1..s2, f τ) + ((∫ τ in s2..s3, f τ) + ∫ τ in Ioi s3, f τ)‖ :=
          norm_add_le _ _
      _ ≤ ‖∫ τ in r..s1, f τ‖ + (‖∫ τ in s1..s2, f τ‖ + ‖∫ τ in s2..s3, f τ‖ + ‖∫ τ in Ioi s3, f τ‖) :=
          add_le_add le_rfl norm_sum3_le
      _ = _ := by ring
  exact hsum4.trans ((add_le_add (add_le_add (add_le_add h0_bd h1_bd) h2_bd) h3_bd).trans_eq (by ring))

private lemma leftTail_Ioi_far_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 32 ^ 4 ≤ c₀ ∧ ∀ ε c ξ σ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      (σ = 1 ∨ σ = -1) → 0 < ξ → 3 * FctSym.physDelta c ≤ Real.log (π ^ 2 * ξ) →
      IntegrableOn (fun τ : ℝ => warpAmpLeft h ε c ξ (σ * τ) *
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Real.log (π ^ 2 * ξ)) (σ * τ) : ℂ)))
        (Ioi ((c * Real.log (π ^ 2 * ξ))⁻¹)) →
      ‖∫ τ in Ioi ((c * Real.log (π ^ 2 * ξ))⁻¹),
          warpAmpLeft h ε c ξ (σ * τ) *
            Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Real.log (π ^ 2 * ξ)) (σ * τ) : ℂ))‖ ≤
        C * c ^ (-(3 / 2 : ℝ)) * (Real.log (π ^ 2 * ξ)) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨Cw, c0w, hCw0, hc0w, hW⟩ := warpAmpLeft_bounds hK4 h
  obtain ⟨M0, V0, c0MV, hM0_pos, hV0_pos, hc0MV, hMV⟩ := warpAmpLeft_M_V_tail_bounds hK4 h
  obtain ⟨M1, V1, c0E, hM1_pos, hV1_pos, hc0E, hME⟩ := warpAmpLeft_M_V_exp_bounds hK4 h
  obtain ⟨C_ibp, c0Ibp, hCibp0, hc0Ibp, hIbp⟩ := warp_ibp1_vdc1_bound hK4 h
  set c₀ : ℝ := max (max (32 ^ 4) c0w) (max c0MV (max c0E c0Ibp))
  have hc0_32 : 32 ^ 4 ≤ c₀ := le_max_of_le_left (le_max_left _ _)
  set C_sm : ℝ := (96 + 96) * (M0 + V0) + 8 * (M0 + V0) / Real.sqrt (3 / 40)
  set C_md : ℝ := ((96 + 36) * (M0 + V0) + 8 * (M0 + V0) / Real.sqrt (3 / 656)) * 2 ^ (3 / 2 : ℝ)
  set C_lg : ℝ := C_ibp + (96 * 48 + 36 * 48) * (M1 + V1) + 800 * Real.sqrt 3 * (M1 + V1)
  set C : ℝ := max C_sm (max C_md C_lg)
  refine ⟨C, c₀, by positivity, hc0_32, fun ε c ξ σ hε hc hσ hξ hL_low hInt_r => ?_⟩
  have hc32 : (32 : ℝ) ^ 4 ≤ c := hc0_32.trans hc
  have hcw : c0w ≤ c := (le_max_of_le_left (le_max_right _ _)).trans hc
  have hcMV : c0MV ≤ c := (le_max_of_le_right (le_max_left _ _)).trans hc
  have hcE : c0E ≤ c := (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans hc
  have hcIbp : c0Ibp ≤ c := (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))).trans hc
  have hcpos : 0 < c := by positivity
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc32
  set L : ℝ := Real.log (π ^ 2 * ξ)
  have hL_ge : (3 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) ≤ L := by
    have := physDelta_ge hc32; linarith
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_ge
  set r : ℝ := (c * L)⁻¹
  have hr_pos : 0 < r := by positivity
  obtain ⟨hr16, hr_s2⟩ := r_le_three_quarters_tau0 hc32 hL_low
  have hCD_pos : ContDiffOn ℝ 1 (fun τ => warpAmpLeft h ε c ξ (σ * τ)) (Ioi 0) :=
    (warpAmpLeft_sign_CD (hW ε c ξ hε hcw).1 hσ).of_le (by norm_num)
  obtain ⟨hM_all, hV_all⟩ := hMV ε c ξ hε hcMV r hr_pos
  have hM_sig : ∀ x ∈ Ici r, ‖warpAmpLeft h ε c ξ (σ * x)‖ ≤ M0 * c⁻¹ := fun x hx => by
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using (hM_all x hx).1
    · simpa only [neg_one_mul] using (hM_all x hx).2
  have hV_sig : ∀ a b : ℝ, r ≤ a → a ≤ b →
      ∫ x in Icc a b, ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖ ≤ V0 * c⁻¹ := by
    intro a b hra hab
    have hIcc_pos : ∀ x ∈ Icc r b, 0 < x := fun x hx => lt_of_lt_of_le hr_pos hx.1
    have hc0' : ContinuousOn (deriv (fun t => warpAmpLeft h ε c ξ (σ * t))) (Ioi 0) :=
      (hCD_pos.derivWithin isOpen_Ioi.uniqueDiffOn (m := 0) (by norm_num)).continuousOn.congr
        fun t ht => (derivWithin_of_isOpen isOpen_Ioi ht).symm
    have hint_rb : IntegrableOn (fun x => ‖deriv (fun t => warpAmpLeft h ε c ξ (σ * t)) x‖) (Icc r b) :=
      (hc0'.norm.mono fun x hx => hIcc_pos x hx).integrableOn_Icc
    have hmono := setIntegral_mono_set hint_rb (Eventually.of_forall fun _ => norm_nonneg _)
      (Icc_subset_Icc hra le_rfl).eventuallySubset
    refine hmono.trans ?_
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using (hV_all b (hra.trans hab)).1
    · simpa only [neg_one_mul] using (hV_all b (hra.trans hab)).2
  rcases le_or_gt L 1 with hL1 | hL1
  · refine (leftTail_Ioi_far_small hM0_pos.le hV0_pos.le hc1 hcpos hσ hL_pos hL1 hr_s2 hCD_pos hInt_r hM_sig hV_sig).trans ?_
    gcongr; exact le_max_left _ _
  · rcases le_or_gt L 2 with hL2 | hL2
    · refine (leftTail_Ioi_far_mid hM0_pos.le hV0_pos.le hc1 hcpos hσ hL1.le hL2 hr_s2 hCD_pos hInt_r hM_sig hV_sig).trans ?_
      gcongr; exact le_trans (le_max_left _ _) (le_max_right _ _)
    · refine (leftTail_Ioi_far_large hM1_pos.le hV1_pos.le hc1 hcpos hσ hL2.le hr16 hCD_pos hInt_r
        (hIbp ε c ξ σ hε hcIbp hσ L hL2.le)
        (fun a ha => hME ε c ξ hε hcE σ a hσ ha)).trans ?_
      gcongr; exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- On the Macro and Far bands `3 * FctSym.physDelta c ≤ Real.log (π² ξ)`,
the left-tail density satisfies
`|warpLeftTailDensity h ε c ξ| ≤ C * c ^ (-2 : ℝ) * (Real.log (π² ξ)) ^ (-(3 / 2 : ℝ))`.

Ref: `fct:warp-asymp` (3)–(4) left-tail macro/far bound. -/
theorem warpLeftTailDensity_far_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 32 ^ 4 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      3 * FctSym.physDelta c ≤ Real.log (π ^ 2 * ξ) →
      |warpLeftTailDensity h ε c ξ| ≤ C * c ^ (-2 : ℝ) * (Real.log (π ^ 2 * ξ)) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨Cw, c0w, hCw0, hc0w, hW⟩ := warpAmpLeft_bounds hK4 h
  obtain ⟨C_tail, c0T, hCT0, hc0T, hTail⟩ := leftTail_Ioi_far_bound hK4 h
  set c₀ : ℝ := max c0w c0T
  set C_near : ℝ := (4 / 3 : ℝ) * Cw
  set C : ℝ := |uctCAi| / (2 * π) * (C_near + 2 * C_tail)
  refine ⟨C, c₀, by positivity, le_max_of_le_right hc0T, fun ε c ξ hε hc hξ hL_low => ?_⟩
  have hcw : c0w ≤ c := (le_max_left _ _).trans hc
  have hcT : c0T ≤ c := (le_max_right _ _).trans hc
  have hc32 : (32 : ℝ) ^ 4 ≤ c := hc0T.trans hcT
  have hcpos : 0 < c := by positivity
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc32
  set L : ℝ := Real.log (π ^ 2 * ξ)
  have hL_ge : (3 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) ≤ L := by
    have := physDelta_ge hc32; linarith
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_ge
  set r : ℝ := (c * L)⁻¹
  have hr_pos : 0 < r := by positivity
  have hr16 : r ≤ 1 / 16 := (r_le_three_quarters_tau0 hc32 hL_low).1
  set f_full : ℝ → ℂ := fun τ =>
    mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
        fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
        fctDcompAt K4 c (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) *
        ctHG ε ((τ : ℂ) * Complex.I))
  have hf_eq : ∀ τ : ℝ, f_full τ =
      Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) * warpAmpLeft h ε c ξ τ := fun τ =>
    warpAmpLeft_eq_integrand h ε c ξ τ hξ
  obtain ⟨hW_cd, hW_near, hW_outer⟩ := hW ε c ξ hε hcw
  have hInt_full : Integrable f_full := by
    have heq : f_full = fun τ : ℝ =>
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) * warpAmpLeft h ε c ξ τ := by
      ext τ; exact hf_eq τ
    rw [heq]
    have hcont : ContinuousOn (fun τ : ℝ =>
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) * warpAmpLeft h ε c ξ τ) {τ : ℝ | τ ≠ 0} := by
      have hexp_c : Continuous (fun τ : ℝ => Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) :=
        Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (contDiff_edgePhi L).continuous))
      exact hexp_c.continuousOn.mul hW_cd.continuousOn
    have hae : AEStronglyMeasurable (fun τ : ℝ =>
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) * warpAmpLeft h ε c ξ τ) volume := by
      have hm : AEStronglyMeasurable (fun τ : ℝ =>
          Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) * warpAmpLeft h ε c ξ τ)
          (volume.restrict ({(0 : ℝ)}ᶜ)) :=
        hcont.aestronglyMeasurable isOpen_ne.measurableSet
      rwa [MeasureTheory.restrict_compl_singleton (0 : ℝ)] at hm
    set g_near_i : ℝ → ℝ := (Icc (-(1 / 16 : ℝ)) (1 / 16)).indicator (fun _ => Cw * c⁻¹)
    set g_far_i : ℝ → ℝ := fun τ => Cw * c⁻¹ * ((1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)))
    have hg_i : Integrable (fun τ : ℝ => g_near_i τ + g_far_i τ) := by
      have h1 : Integrable g_near_i :=
        (integrableOn_const (C := Cw * c⁻¹) (hs := measure_Icc_lt_top.ne)).integrable_indicator
          measurableSet_Icc
      have h2 : Integrable g_far_i := (integrable_pow_mul_exp_neg_pi 14).const_mul (Cw * c⁻¹)
      exact h1.add h2
    have hae0 : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by rw [ae_iff]; simp
    refine hg_i.mono' hae ?_
    filter_upwards [hae0] with τ hτ
    rw [norm_mul, Complex.norm_exp]
    have hre : (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)).re = 0 := by
      rw [mul_assoc, Complex.I_mul_re, ← Complex.ofReal_mul, Complex.ofReal_im]; norm_num
    rw [hre, Real.exp_zero, one_mul]
    have hg1_nn : 0 ≤ g_near_i τ := Set.indicator_nonneg (fun _ _ => by positivity) τ
    have hg2_nn : 0 ≤ g_far_i τ := by positivity
    rcases le_or_gt |τ| (1 / 16) with h16 | h16
    · have hbd := (hW_near τ hτ h16).1
      have hrp1 : |τ| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg τ) (by linarith) (by norm_num)
      have hmem : τ ∈ Icc (-(1 / 16 : ℝ)) (1 / 16) := abs_le.mp h16
      have hge : g_near_i τ = Cw * c⁻¹ := Set.indicator_of_mem hmem _
      calc ‖warpAmpLeft h ε c ξ τ‖ ≤ Cw * c⁻¹ * |τ| ^ (1 / 2 : ℝ) := hbd
        _ ≤ Cw * c⁻¹ * 1 := by gcongr
        _ = g_near_i τ + 0 := by rw [hge]; ring
        _ ≤ g_near_i τ + g_far_i τ := add_le_add le_rfl hg2_nn
    · have hbd := (hW_outer τ h16.le).1
      calc ‖warpAmpLeft h ε c ξ τ‖ ≤ Cw * c⁻¹ * (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)) := hbd
        _ = 0 + g_far_i τ := by simp only [g_far_i]; ring
        _ ≤ g_near_i τ + g_far_i τ := add_le_add hg1_nn le_rfl
  have hsplit := integral_real_split_two_sides hInt_full hr_pos
  have h_near : ‖∫ τ in Ioc (-r) r, f_full τ‖ ≤ C_near * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    set g_bnd : ℝ → ℝ := fun τ => Cw * c⁻¹ * |τ| ^ (1 / 2 : ℝ)
    have hg_cont : ContinuousOn g_bnd (Icc (-r) r) :=
      (continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num)))).continuousOn
    have hg_int : IntegrableOn g_bnd (Ioc (-r) r) := hg_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hpt_near : ∀ᵐ τ ∂(volume.restrict (Ioc (-r) r)), ‖f_full τ‖ ≤ g_bnd τ := by
      have hae0 : ∀ᵐ τ : ℝ ∂(volume.restrict (Ioc (-r) r)), τ ≠ 0 := by
        rw [ae_restrict_iff' measurableSet_Ioc]
        have : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by rw [ae_iff]; simp
        filter_upwards [this] with τ hτ _; exact hτ
      filter_upwards [ae_restrict_mem measurableSet_Ioc, hae0] with τ hτmem hτne
      have hτr : |τ| ≤ r := abs_le.mpr ⟨(mem_Ioc.mp hτmem).1.le, (mem_Ioc.mp hτmem).2⟩
      rw [hf_eq τ, norm_mul, Complex.norm_exp]
      have hre : (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)).re = 0 := by
        rw [mul_assoc, Complex.I_mul_re, ← Complex.ofReal_mul, Complex.ofReal_im]; norm_num
      rw [hre, Real.exp_zero, one_mul]
      exact (hW_near τ hτne (hτr.trans hr16)).1
    have hnorm_le := norm_integral_le_of_norm_le hg_int hpt_near
    have hg_eval : ∫ τ in Ioc (-r) r, g_bnd τ = (4 / 3 : ℝ) * Cw * c⁻¹ * r ^ (3 / 2 : ℝ) := by
      rw [← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
      dsimp only [g_bnd]
      rw [intervalIntegral.integral_const_mul]
      have heven : ∫ τ in -r..r, |τ| ^ (1 / 2 : ℝ) = 2 * ∫ τ in 0..r, τ ^ (1 / 2 : ℝ) := by
        have hneg0 : ∫ τ in -r..0, |τ| ^ (1 / 2 : ℝ) = ∫ τ in 0..r, |τ| ^ (1 / 2 : ℝ) := by
          have := intervalIntegral.integral_comp_neg (fun τ : ℝ => |τ| ^ (1 / 2 : ℝ)) (a := (0 : ℝ)) (b := r)
          simpa using this.symm
        have hpos0 : ∫ τ in 0..r, |τ| ^ (1 / 2 : ℝ) = ∫ τ in 0..r, τ ^ (1 / 2 : ℝ) :=
          intervalIntegral.integral_congr fun τ hτ => by
            rw [abs_of_nonneg (uIcc_of_le hr_pos.le ▸ hτ).1]
        have hi1 : IntervalIntegrable (fun τ : ℝ => |τ| ^ (1 / 2 : ℝ)) volume (-r) 0 :=
          (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num))).intervalIntegrable _ _
        have hi2 : IntervalIntegrable (fun τ : ℝ => |τ| ^ (1 / 2 : ℝ)) volume 0 r :=
          (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num))).intervalIntegrable _ _
        rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hneg0, hpos0]; ring
      rw [heven, integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num)]
      norm_num; ring
    have hr32 : r ^ (3 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
      dsimp [r]
      rw [Real.inv_rpow (by positivity), Real.mul_rpow hcpos.le hL_pos.le, mul_inv,
        ← Real.rpow_neg hcpos.le, ← Real.rpow_neg hL_pos.le]
    have hc_52_32 : c⁻¹ * c ^ (-(3 / 2 : ℝ)) ≤ c ^ (-(3 / 2 : ℝ)) := by
      have h1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
      calc c⁻¹ * c ^ (-(3 / 2 : ℝ)) ≤ 1 * c ^ (-(3 / 2 : ℝ)) := by gcongr
        _ = c ^ (-(3 / 2 : ℝ)) := one_mul _
    refine hnorm_le.trans ?_
    rw [hg_eval, hr32]
    calc (4 / 3 : ℝ) * Cw * c⁻¹ * (c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)))
        = C_near * (c⁻¹ * c ^ (-(3 / 2 : ℝ))) * L ^ (-(3 / 2 : ℝ)) := by simp only [C_near]; ring
      _ ≤ C_near * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by gcongr
  have hInt_pos : IntegrableOn (fun τ : ℝ => warpAmpLeft h ε c ξ (1 * τ) *
      Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (1 * τ) : ℂ))) (Ioi r) := by
    have heq : (fun τ : ℝ => warpAmpLeft h ε c ξ (1 * τ) *
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (1 * τ) : ℂ))) = f_full := by
      ext τ; simp only [one_mul]; rw [hf_eq τ, mul_comm]
    rw [heq]; exact hInt_full.integrableOn
  have hInt_neg : IntegrableOn (fun τ : ℝ => warpAmpLeft h ε c ξ (-1 * τ) *
      Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (-1 * τ) : ℂ))) (Ioi r) := by
    have heq : (fun τ : ℝ => warpAmpLeft h ε c ξ (-1 * τ) *
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (-1 * τ) : ℂ))) = fun τ => f_full (-τ) := by
      ext τ; simp only [neg_one_mul]; rw [hf_eq (-τ), mul_comm]
    rw [heq]; exact hInt_full.comp_neg.integrableOn
  have hpos_bd : ‖∫ τ in Ioi r, f_full τ‖ ≤ C_tail * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have hv := hTail ε c ξ 1 hε hcT (Or.inl rfl) hξ hL_low hInt_pos
    have hint_eq : ∫ τ in Ioi r, f_full τ = ∫ τ in Ioi r, warpAmpLeft h ε c ξ (1 * τ) *
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (1 * τ) : ℂ)) :=
      setIntegral_congr_fun measurableSet_Ioi fun τ _ => by simp only [one_mul]; rw [hf_eq τ, mul_comm]
    rw [hint_eq]; exact hv
  have hneg_bd : ‖∫ τ in Ioi r, f_full (-τ)‖ ≤ C_tail * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have hv := hTail ε c ξ (-1) hε hcT (Or.inr rfl) hξ hL_low hInt_neg
    have hint_eq : ∫ τ in Ioi r, f_full (-τ) = ∫ τ in Ioi r, warpAmpLeft h ε c ξ (-1 * τ) *
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (-1 * τ) : ℂ)) :=
      setIntegral_congr_fun measurableSet_Ioi fun τ _ => by
        simp only [neg_one_mul]; rw [hf_eq (-τ), mul_comm]
    rw [hint_eq]; exact hv
  have h_full_bd : ‖∫ τ : ℝ, f_full τ‖ ≤ (C_near + 2 * C_tail) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    rw [hsplit]
    calc ‖(∫ τ in Ioc (-r) r, f_full τ) + (∫ τ in Ioi r, f_full τ) + ∫ τ in Ioi r, f_full (-τ)‖
        ≤ ‖∫ τ in Ioc (-r) r, f_full τ‖ + ‖∫ τ in Ioi r, f_full τ‖ + ‖∫ τ in Ioi r, f_full (-τ)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ C_near * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) +
            C_tail * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) +
            C_tail * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) :=
          add_le_add (add_le_add h_near hpos_bd) hneg_bd
      _ = (C_near + 2 * C_tail) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by ring
  have hc_final : c ^ (-(1 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ)) = c ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hcpos]; congr 1; norm_num
  unfold warpLeftTailDensity
  rw [abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * π),
    abs_of_pos (Real.rpow_pos_of_pos hcpos _)]
  calc |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) * |(∫ τ : ℝ, f_full τ).re|
      ≤ |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) * ‖∫ τ : ℝ, f_full τ‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) *
          ((C_near + 2 * C_tail) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h_full_bd (by positivity)
    _ = C * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ))) * L ^ (-(3 / 2 : ℝ)) := by simp only [C]; ring
    _ = C * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by rw [hc_final]

/-- info: 'FormalResearch.SignUncertainty.warpLeftTailDensity_far_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpLeftTailDensity_far_bound

end FormalResearch.SignUncertainty
