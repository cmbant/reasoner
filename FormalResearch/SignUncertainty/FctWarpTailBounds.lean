/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpSplitErrors

/-!
# Splitting identity for `normDensity (ctWwarp ...)` and global/window tail bounds (`fct:warp-asymp` (2))

Proves:
* `fctPhiHat_right_bound`: `‖fctPhiHat h ε c (1 - iτ)‖ ≤ 1 + |τ|` for large `c`.
* `normDensity_ctWwarp_split`:
  `normDensity (ctWwarp (fctPhiHat h) (fctDcomp K4 (fctWarpAlpha h)) ε c) c ξ` equals
  `warpMainDensity h ε c ξ + warpLeftTailDensity h ε c ξ`, and
  `warpMainDensity h ε c ξ = warpMainNoRightDensity h ε c ξ + warpRightTailDensity h ε c ξ`.
* `warpRightTailDensity_bound`: `|warpRightTailDensity h ε c ξ| ≤ C * c^{-(4/3)}` for all `ξ > 0`.
* `warpLeftTailDensity_global_bound`: `|warpLeftTailDensity h ε c ξ| ≤ C * c^{-(3/2)}` for all `ξ > 0`.

Class: proved (depending only on `K4 ≥ 1`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

private lemma integrable_pow_mul_exp_neg_pi (N : ℕ) :
    Integrable (fun τ : ℝ => (1 + |τ|) ^ N * Real.exp (-(π * |τ|))) := by
  obtain ⟨K, hK0, hK⟩ := poly_exp_le_n (N + 2)
  refine (integrable_inv_one_add_abs_sq.const_mul K).mono' ?_ (ae_of_all _ fun τ => ?_)
  · exact (((continuous_const.add continuous_abs).pow N).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg)).aestronglyMeasurable
  · have hx0 : 0 ≤ |τ| := abs_nonneg τ
    have h1x : 0 < 1 + |τ| := by linarith
    have hb := hK |τ| hx0
    have hnn : 0 ≤ (1 + |τ|) ^ N * Real.exp (-(π * |τ|)) := by positivity
    rw [Real.norm_of_nonneg hnn]
    rw [show K * (1 / (1 + |τ|) ^ 2) = K / (1 + |τ|) ^ 2 by ring, le_div_iff₀ (by positivity)]
    calc (1 + |τ|) ^ N * Real.exp (-(π * |τ|)) * (1 + |τ|) ^ 2
        = (1 + |τ|) ^ (N + 2) * Real.exp (-(π * |τ|)) := by ring
      _ ≤ K := hb

lemma fctPhiHat_right_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∀ τ : ℝ,
      ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ ≤ 1 + |τ| := by
  obtain ⟨CR, c0R, _, _, hRT⟩ := fctRightTail_bounds hK4 h
  refine ⟨max c0R (max CR 1), le_max_of_le_right (le_max_right _ _), fun ε c hε hc τ => ?_⟩
  have h1c : max CR 1 ≤ c := (le_max_right _ _).trans hc
  have hcCR : CR ≤ c := (le_max_left _ _).trans h1c
  have hc1 : 1 ≤ c := (le_max_right _ _).trans h1c
  have hbd := ((hRT ε c hε ((le_max_left _ _).trans hc)).2 τ).1
  have hcr : CR * c⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ (by linarith)]; linarith
  have heq : fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) = 1 + fctRightTail h ε c τ := by
    unfold fctRightTail; ring
  rw [heq]
  calc ‖(1 : ℂ) + fctRightTail h ε c τ‖ ≤ ‖(1 : ℂ)‖ + ‖fctRightTail h ε c τ‖ := norm_add_le _ _
    _ ≤ 1 + CR * c⁻¹ * |τ| := by rw [norm_one]; exact add_le_add le_rfl hbd
    _ ≤ 1 + 1 * |τ| := by gcongr
    _ = 1 + |τ| := by ring

private lemma integrand_integrable_piece_near {M : ℝ} (hM : 0 ≤ M) {r : ℝ} (_hr : 0 < r)
    {f : ℝ → ℂ} (hf_cont : ContinuousOn f {τ : ℝ | τ ≠ 0})
    (hf_near : ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ r → ‖f τ‖ ≤ M)
    (hf_far : ∀ τ : ℝ, r < |τ| → ‖f τ‖ ≤ M * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) :
    Integrable f := by
  set g : ℝ → ℝ := fun τ =>
    M * (Icc (-r) r).indicator (fun _ => (1 : ℝ)) τ + M * ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)))
  have hg_int : Integrable g := by
    have h1 : Integrable (fun τ : ℝ => M * (Icc (-r) r).indicator (fun _ => (1 : ℝ)) τ) :=
      ((integrableOn_const (C := (1 : ℝ)) (hs := measure_Icc_lt_top.ne)).integrable_indicator
        measurableSet_Icc).const_mul M
    have h2 : Integrable (fun τ : ℝ => M * ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)))) :=
      (integrable_pow_mul_exp_neg_pi 12).const_mul M
    exact h1.add h2
  have hae : AEStronglyMeasurable f volume := by
    have hm : AEStronglyMeasurable f (volume.restrict ({(0 : ℝ)}ᶜ)) :=
      hf_cont.aestronglyMeasurable isOpen_ne.measurableSet
    rwa [MeasureTheory.restrict_compl_singleton (0 : ℝ)] at hm
  have hae0 : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by rw [ae_iff]; simp
  refine hg_int.mono' hae ?_
  filter_upwards [hae0] with τ hτ
  rcases le_or_gt |τ| r with hle | hgt
  · have hm : τ ∈ Icc (-r) r := abs_le.mp hle
    have h2nn : 0 ≤ M * ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) := by positivity
    calc ‖f τ‖ ≤ M := hf_near τ hτ hle
      _ = M * (Icc (-r) r).indicator (fun _ => (1 : ℝ)) τ + 0 := by simp [Set.indicator_of_mem hm]
      _ ≤ g τ := add_le_add le_rfl h2nn
  · have h1nn : 0 ≤ M * (Icc (-r) r).indicator (fun _ => (1 : ℝ)) τ :=
      mul_nonneg hM (Set.indicator_nonneg (fun _ _ => zero_le_one) τ)
    calc ‖f τ‖ ≤ M * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := hf_far τ hgt
      _ = 0 + M * ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) := by ring
      _ ≤ g τ := add_le_add h1nn le_rfl

private lemma warp_integrands_integrable {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        ((c : ℂ) * fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) /
          (fctNc h ε c : ℂ) * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I))) ∧
      Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
          fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
          fctDcompAt K4 c (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) *
          ctHG ε ((τ : ℂ) * Complex.I))) ∧
      Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        ((c : ℂ) * fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) /
          (fctNc h ε c : ℂ) * fctRightTail h ε c τ)) ∧
      Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        ((c : ℂ) * fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) /
          (fctNc h ε c : ℂ))) := by
  obtain ⟨c0N, _, hNc⟩ := fctNcC_eq_fctNc hK4 h
  obtain ⟨CR, c0R, hCR0, _, hRT⟩ := fctRightTail_bounds hK4 h
  obtain ⟨c0PhiR, _, hPhiR⟩ := fctPhiHat_right_bound hK4 h
  obtain ⟨ML, c0L, hML0, _, hLT⟩ := fctLeftTail_deriv_bounds hK4 h
  obtain ⟨MD, c0D, hMD0, _, hDHG⟩ := dcomp_ctHG_EJ hK4 h
  obtain ⟨Ms, c0s, hMs0, _, hPsi_s⟩ := fctPsi_imag_small_bound hK4 h
  obtain ⟨Mlg, c0lg, hMlg0, _, hPsi_lg⟩ := fctPsi_imag_large_bound hK4 h
  obtain ⟨c0C2, hC2⟩ := fctPhiHat_left_c2 hK4 (fctDescent_uncond hK4 h)
  set c₀ : ℝ := max (max (max c0N c0R) (max c0PhiR c0L)) (max (max c0D c0s) (max c0lg (max c0C2 8)))
  refine ⟨c₀, le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (by norm_num)))),
    fun ε c ξ hε hc hξ => ?_⟩
  have h1 : c0N ≤ c := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hc
  have h2 : c0R ≤ c := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hc
  have h3 : c0PhiR ≤ c := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hc
  have h4 : c0L ≤ c := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hc
  have h5 : c0D ≤ c := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hc
  have h6 : c0s ≤ c := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hc
  have h7 : c0lg ≤ c := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hc
  have h8 : c0C2 ≤ c := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
    (by linarith [le_max_right c0lg (max c0C2 8), le_max_right (max c0D c0s) (max c0lg (max c0C2 8)),
      le_max_right (max (max c0N c0R) (max c0PhiR c0L)) (max (max c0D c0s) (max c0lg (max c0C2 8)))])
  have hc8 : 8 ≤ c := by
    linarith [le_max_right c0C2 8, le_max_right c0lg (max c0C2 8),
      le_max_right (max c0D c0s) (max c0lg (max c0C2 8)),
      le_max_right (max (max c0N c0R) (max c0PhiR c0L)) (max (max c0D c0s) (max c0lg (max c0C2 8)))]
  have hcpos : 0 < c := by linarith
  obtain ⟨hNc_eq, hNc_lo, _, hNc_ne⟩ := hNc ε c hε h1
  obtain ⟨hRT_cd, hRT_bd⟩ := hRT ε c hε h2
  have hPR := hPhiR ε c hε h3
  obtain ⟨hLT_cd, hLT_sm, hLT_gl⟩ := hLT ε c hε h4
  have hEJ := hDHG ε c hε h5
  have hPs := hPsi_s ε c ξ hε h6 hξ
  have hPlg := hPsi_lg ε c ξ hε h7 hξ
  have hc2' := hC2 ε c hε h8
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set Nc := (fctNc h ε c : ℂ)
  have hNc_inv : ‖Nc⁻¹‖ ≤ 2 := by
    change ‖((fctNc h ε c : ℝ) : ℂ)⁻¹‖ ≤ 2
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hm_cont : Continuous (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ) :=
    continuous_mellinK0_imag hcpos hξ
  have hm_le : ∀ τ : ℝ, ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ ≤ 1 := fun τ =>
    (norm_mellinK0_imag_le hcpos hξ τ).2.trans
      (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg τ]) (by norm_num))
  have hPR_cont : Continuous (fun τ : ℝ => fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)) := by
    have : (fun τ : ℝ => fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)) = fun τ => 1 + fctRightTail h ε c τ := by
      funext τ; unfold fctRightTail; ring
    rw [this]; exact continuous_const.add hRT_cd.continuous
  have hDHG_cont : ContinuousOn (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))
      {τ : ℝ | τ ≠ 0} := hEJ.c2.continuousOn
  have hPhiL_cont : ContinuousOn (fun τ : ℝ => fctPhiHat h ε c ((τ : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} :=
    hc2'.continuousOn
  have hMain_eq : ∀ τ : ℝ, τ ≠ 0 →
      (c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc =
        (fctPhiHat h ε c ((τ : ℂ) * Complex.I) - fctLeftTail K4 ε c L1 α τ) *
          (fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) := fun τ hτ => by
    have hd1 : fctDcompAt K4 c α ((τ : ℂ) * Complex.I) ≠ 0 := fctDcompAt_ne_zero _
    have hd2 : ctHG ε ((τ : ℂ) * Complex.I) ≠ 0 :=
      ctHG_ne_zero_of_closed_band ε (by simp) (by simp) (by simp [hτ])
    have hspl : fctPhiHat h ε c ((τ : ℂ) * Complex.I) - fctLeftTail K4 ε c L1 α τ =
        fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc := by
      show fctPhiHatAt K4 ε c L1 α ((τ : ℂ) * Complex.I) - _ = _
      rw [fctPhiHatAt_left_eq_add_tail, hNc_eq]; ring
    rw [hspl]
    unfold fctPhiC
    have hNc0 : Nc ≠ 0 := hNc_ne
    field_simp [hd1, hd2, hNc0]
  set r := c ^ (-(1 / 3 : ℝ))
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hcpos _
  have hr_le1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hI_main : Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I))) := by
    have hcont : ContinuousOn (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)))
        {τ : ℝ | τ ≠ 0} := by
      refine ContinuousOn.congr
        (hm_cont.continuousOn.mul
          (((hPhiL_cont.sub hLT_cd.continuous.continuousOn).mul hDHG_cont).mul hPR_cont.continuousOn))
        fun τ hτ => ?_
      simp only [Pi.mul_apply, Pi.sub_apply]; rw [hMain_eq τ hτ]
    set M := max (4 * Ms * c + 2 * Mlg * 2 ^ 10 * (r ^ (-(5 / 2 : ℝ)))) (2 * Mlg * (max r⁻¹ 1) ^ (5 / 2 : ℝ))
    have hM0 : 0 ≤ M := by positivity
    refine integrand_integrable_piece_near hM0 (r := r) hr_pos hcont (fun τ hτ hτr => ?_) (fun τ hτr => ?_)
    · have hτ1 : 1 + |τ| ≤ 2 := by linarith
      have hPR2 : ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ ≤ 2 := (hPR τ).trans hτ1
      have hPs' := hPs τ hτ hτr
      have hrp1 : |τ| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg τ) (hτr.trans hr_le1) (by norm_num)
      have hnm : ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I))‖ =
          ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ *
          (‖Nc⁻¹‖ * ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖) := by
        rw [div_eq_mul_inv]; simp only [norm_mul]; ring
      rw [hnm]
      have hnn2 : 0 ≤ 2 * Mlg * 2 ^ 10 * (r ^ (-(5 / 2 : ℝ))) := by positivity
      calc ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ *
            (‖Nc⁻¹‖ * ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖)
          ≤ (Ms * c * |τ| ^ (1 / 2 : ℝ)) * (2 * 2) :=
            mul_le_mul hPs' (mul_le_mul hNc_inv hPR2 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
        _ ≤ (Ms * c * 1) * (2 * 2) := by gcongr
        _ ≤ 4 * Ms * c + 2 * Mlg * 2 ^ 10 * (r ^ (-(5 / 2 : ℝ))) := by linarith
        _ ≤ M := le_max_left _ _
    · have hτpos : 0 < |τ| := hr_pos.trans hτr
      have hτne : τ ≠ 0 := abs_pos.mp hτpos
      have hPl := hPlg τ hτne
      have hpow_neg : |τ| ^ (-(5 / 2 : ℝ)) ≤ (max r⁻¹ 1) ^ (5 / 2 : ℝ) := by
        rw [Real.rpow_neg hτpos.le, ← Real.inv_rpow hτpos.le]
        exact Real.rpow_le_rpow (by positivity) ((inv_anti₀ hr_pos hτr.le).trans (le_max_left _ _)) (by norm_num)
      have h1_le : (1 + |τ|) ^ 10 * (1 + |τ|) ≤ (1 + |τ|) ^ 12 := by
        have : (1 + |τ|) ^ 10 * (1 + |τ|) = (1 + |τ|) ^ 11 := by ring
        rw [this]
        exact pow_le_pow_right₀ (by linarith [abs_nonneg τ]) (by norm_num)
      have hexp0 : 0 ≤ Real.exp (-(π * |τ|)) := (Real.exp_pos _).le
      have hnm : ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I))‖ =
          ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ *
          (‖Nc⁻¹‖ * ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖) := by
        rw [div_eq_mul_inv]; simp only [norm_mul]; ring
      rw [hnm]
      calc ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ *
            (‖Nc⁻¹‖ * ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖)
          ≤ (Mlg * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) * (2 * (1 + |τ|)) :=
            mul_le_mul hPl (mul_le_mul hNc_inv (hPR τ) (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
        _ = (2 * Mlg * |τ| ^ (-(5 / 2 : ℝ))) * ((1 + |τ|) ^ 10 * (1 + |τ|)) * Real.exp (-(π * |τ|)) := by ring
        _ ≤ (2 * Mlg * (max r⁻¹ 1) ^ (5 / 2 : ℝ)) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by gcongr
        _ ≤ M * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by gcongr; exact le_max_right _ _
  have hI_left : Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      (fctLeftTail K4 ε c L1 α τ * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
        fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))) := by
    have hcont : ContinuousOn (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        (fctLeftTail K4 ε c L1 α τ * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
          fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))) {τ : ℝ | τ ≠ 0} := by
      refine (hm_cont.continuousOn.mul ((hLT_cd.continuous.continuousOn.mul hPR_cont.continuousOn).mul hDHG_cont)).congr
        fun τ _ => by simp only [Pi.mul_apply]; ring
    set M := max (ML * 2 * (2 ^ 10 * MD)) (ML * 2 * (8 ^ (5 / 2 : ℝ) * MD))
    have hM0 : 0 ≤ M := by positivity
    refine integrand_integrable_piece_near hM0 (r := (1 / 8 : ℝ)) (by norm_num) hcont (fun τ hτ hτ8 => ?_) (fun τ hτ8 => ?_)
    · have hc1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hL := (hLT_sm τ hτ8).1
      have hPR2 : ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ ≤ 2 := (hPR τ).trans (by linarith)
      have hD0 := hEJ.b0 τ hτ
      unfold ejW at hD0
      have hp1 : (1 + |τ|) ^ (10 + 0) ≤ 2 ^ 10 := pow_le_pow_left₀ (by positivity) (by linarith) 10
      have hexp1 : Real.exp (-(π * 1 * |τ|)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg Real.pi_pos.le zero_le_one) (abs_nonneg τ)))
      have hrp : |τ| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg τ) (by linarith) (by norm_num)
      have hpow_m : |τ| ^ 3 * |τ| ^ (-(5 / 2 : ℝ)) = |τ| ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast |τ| 3, ← Real.rpow_add (abs_pos.mpr hτ)]
        congr 1; norm_num
      have hre : ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          (fctLeftTail K4 ε c L1 α τ * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
            fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))‖ =
          ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ *
            (‖fctLeftTail K4 ε c L1 α τ‖ * ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ *
              ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)‖) := by
        simp only [norm_mul, mul_assoc]
      rw [hre]
      calc ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ *
            (‖fctLeftTail K4 ε c L1 α τ‖ * ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ *
              ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)‖)
          ≤ 1 * ((ML * 1 * |τ| ^ 3) * 2 * (MD * (|τ| ^ (-(5 / 2 : ℝ)) * 2 ^ 10 * 1))) := by
            refine mul_le_mul (hm_le τ) (mul_le_mul (mul_le_mul (hL.trans (by gcongr)) hPR2
              (norm_nonneg _) (by positivity)) (hD0.trans (by
                have hsub : (-(5 / 2 : ℝ)) - ((0 : ℕ) : ℝ) = -(5 / 2 : ℝ) := by norm_num
                rw [hsub]
                have := Real.rpow_nonneg (abs_nonneg τ) (-(5 / 2 : ℝ))
                gcongr)) (norm_nonneg _) (by positivity)) (by positivity) zero_le_one
        _ = (ML * 2 * (2 ^ 10 * MD)) * (|τ| ^ 3 * |τ| ^ (-(5 / 2 : ℝ))) := by ring
        _ = (ML * 2 * (2 ^ 10 * MD)) * |τ| ^ (1 / 2 : ℝ) := by rw [hpow_m]
        _ ≤ (ML * 2 * (2 ^ 10 * MD)) * 1 := by gcongr
        _ ≤ M := by rw [mul_one]; exact le_max_left _ _
    · have hc1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hτpos : 0 < |τ| := lt_trans (by norm_num) hτ8
      have hτne : τ ≠ 0 := abs_pos.mp hτpos
      have hL := (hLT_gl τ).1
      have hD0 := hEJ.b0 τ hτne
      unfold ejW at hD0
      have hsub : (-(5 / 2 : ℝ)) - ((0 : ℕ) : ℝ) = -(5 / 2 : ℝ) := by norm_num
      rw [hsub] at hD0
      have hpow_neg : |τ| ^ (-(5 / 2 : ℝ)) ≤ 8 ^ (5 / 2 : ℝ) := by
        rw [Real.rpow_neg hτpos.le, ← Real.inv_rpow hτpos.le]
        exact Real.rpow_le_rpow (by positivity) (inv_le_of_inv_le₀ (by norm_num) (by linarith)) (by norm_num)
      have hpoly : (1 + |τ|) * (1 + |τ|) * (1 + |τ|) ^ (10 + 0) = (1 + |τ|) ^ 12 := by ring
      have hre : ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          (fctLeftTail K4 ε c L1 α τ * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
            fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))‖ =
          ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ *
            (‖fctLeftTail K4 ε c L1 α τ‖ * ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ *
              ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)‖) := by
        simp only [norm_mul, mul_assoc]
      rw [hre]
      have hexp0 : 0 ≤ Real.exp (-(π * 1 * |τ|)) := (Real.exp_pos _).le
      calc ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ *
            (‖fctLeftTail K4 ε c L1 α τ‖ * ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ *
              ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)‖)
          ≤ 1 * ((ML * 1 * (1 + |τ|)) * (1 + |τ|) * (MD * (8 ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (10 + 0) * Real.exp (-(π * |τ|))))) := by
            refine mul_le_mul (hm_le τ) (mul_le_mul (mul_le_mul (hL.trans (by gcongr)) (hPR τ)
              (norm_nonneg _) (by positivity)) (hD0.trans (by
                have h10 : 0 ≤ (1 + |τ|) ^ (10 + 0) := by positivity
                rw [show Real.exp (-(π * 1 * |τ|)) = Real.exp (-(π * |τ|)) by ring_nf]
                gcongr)) (norm_nonneg _) (by positivity)) (by positivity) zero_le_one
        _ = (ML * 1) * (MD * 8 ^ (5 / 2 : ℝ)) * ((1 + |τ|) * (1 + |τ|) * (1 + |τ|) ^ (10 + 0)) * Real.exp (-(π * |τ|)) := by ring
        _ ≤ (ML * 2) * (MD * 8 ^ (5 / 2 : ℝ)) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by
            rw [hpoly]; gcongr; norm_num
        _ = (ML * 2 * (8 ^ (5 / 2 : ℝ) * MD)) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by ring
        _ ≤ M * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by gcongr; exact le_max_right _ _
  have hI_right : Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctRightTail h ε c τ)) := by
    have hcont : ContinuousOn (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctRightTail h ε c τ)) {τ : ℝ | τ ≠ 0} := by
      refine ContinuousOn.congr
        (hm_cont.continuousOn.mul
          (((hPhiL_cont.sub hLT_cd.continuous.continuousOn).mul hDHG_cont).mul hRT_cd.continuous.continuousOn))
        fun τ hτ => ?_
      simp only [Pi.mul_apply, Pi.sub_apply]; rw [hMain_eq τ hτ]
    set M := max (2 * Ms * c * CR * c⁻¹ + 2 * Mlg * CR * c⁻¹) (2 * Mlg * CR * c⁻¹ * (max r⁻¹ 1) ^ (5 / 2 : ℝ))
    have hM0 : 0 ≤ M := by positivity
    refine integrand_integrable_piece_near hM0 (r := r) hr_pos hcont (fun τ hτ hτr => ?_) (fun τ hτr => ?_)
    · have hτ1 : |τ| ≤ 1 := hτr.trans hr_le1
      have hRT_t := (hRT_bd τ).1
      have hPs' := hPs τ hτ hτr
      have hrp1 : |τ| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg τ) hτ1 (by norm_num)
      have hnm : ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctRightTail h ε c τ)‖ =
          ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ *
          (‖Nc⁻¹‖ * ‖fctRightTail h ε c τ‖) := by
        rw [div_eq_mul_inv]; simp only [norm_mul]; ring
      rw [hnm]
      have hnn2 : 0 ≤ 2 * Mlg * CR * c⁻¹ := by positivity
      calc ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ *
            (‖Nc⁻¹‖ * ‖fctRightTail h ε c τ‖)
          ≤ (Ms * c * |τ| ^ (1 / 2 : ℝ)) * (2 * (CR * c⁻¹ * |τ|)) :=
            mul_le_mul hPs' (mul_le_mul hNc_inv hRT_t (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
        _ ≤ (Ms * c * 1) * (2 * (CR * c⁻¹ * 1)) := by gcongr
        _ = 2 * Ms * c * CR * c⁻¹ := by ring
        _ ≤ 2 * Ms * c * CR * c⁻¹ + 2 * Mlg * CR * c⁻¹ := by linarith
        _ ≤ M := le_max_left _ _
    · have hτpos : 0 < |τ| := hr_pos.trans hτr
      have hτne : τ ≠ 0 := abs_pos.mp hτpos
      have hPl := hPlg τ hτne
      have hpow_neg : |τ| ^ (-(5 / 2 : ℝ)) ≤ (max r⁻¹ 1) ^ (5 / 2 : ℝ) := by
        rw [Real.rpow_neg hτpos.le, ← Real.inv_rpow hτpos.le]
        exact Real.rpow_le_rpow (by positivity) ((inv_anti₀ hr_pos hτr.le).trans (le_max_left _ _)) (by norm_num)
      have h1_le : (1 + |τ|) ^ 10 * |τ| ≤ (1 + |τ|) ^ 12 := by
        have h1 : |τ| ≤ 1 + |τ| := by linarith
        have h2 : (1 + |τ|) ^ 10 * (1 + |τ|) = (1 + |τ|) ^ 11 := by ring
        calc (1 + |τ|) ^ 10 * |τ| ≤ (1 + |τ|) ^ 10 * (1 + |τ|) := by gcongr
          _ = (1 + |τ|) ^ 11 := h2
          _ ≤ (1 + |τ|) ^ 12 := pow_le_pow_right₀ (by linarith [abs_nonneg τ]) (by norm_num)
      have hexp0 : 0 ≤ Real.exp (-(π * |τ|)) := (Real.exp_pos _).le
      have hnm : ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctRightTail h ε c τ)‖ =
          ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ *
          (‖Nc⁻¹‖ * ‖fctRightTail h ε c τ‖) := by
        rw [div_eq_mul_inv]; simp only [norm_mul]; ring
      rw [hnm]
      calc ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ *
            (‖Nc⁻¹‖ * ‖fctRightTail h ε c τ‖)
          ≤ (Mlg * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) * (2 * (CR * c⁻¹ * |τ|)) :=
            mul_le_mul hPl (mul_le_mul hNc_inv (hRT_bd τ).1 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
        _ = (2 * Mlg * CR * c⁻¹ * |τ| ^ (-(5 / 2 : ℝ))) * ((1 + |τ|) ^ 10 * |τ|) * Real.exp (-(π * |τ|)) := by ring
        _ ≤ (2 * Mlg * CR * c⁻¹ * (max r⁻¹ 1) ^ (5 / 2 : ℝ)) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by gcongr
        _ ≤ M * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by gcongr; exact le_max_right _ _
  have hI_noR : Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc)) := by
    have hsub_eq : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc)) =
        fun τ : ℝ => (mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I))) -
          (mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctRightTail h ε c τ)) := by
      funext τ; dsimp only [fctRightTail]; ring
    rw [hsub_eq]
    exact hI_main.sub hI_right
  exact ⟨hI_main, hI_left, hI_right, hI_noR⟩

/-- Splitting `normDensity (ctWwarp ...)` into main (`Φ_c/N_c`), left tail (`E_L`), and right tail (`E_R`). -/
theorem normDensity_ctWwarp_split {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      normDensity (ctWwarp (fctPhiHat h) (fctDcomp K4 (fctWarpAlpha h)) ε c) c ξ =
        warpMainDensity h ε c ξ + warpLeftTailDensity h ε c ξ ∧
      warpMainDensity h ε c ξ =
        warpMainNoRightDensity h ε c ξ + warpRightTailDensity h ε c ξ := by
  obtain ⟨c0N, _, hNc⟩ := fctNcC_eq_fctNc hK4 h
  obtain ⟨c0I, hc0I, hInts⟩ := warp_integrands_integrable hK4 h
  refine ⟨max c0N c0I, le_max_of_le_right hc0I, fun ε c ξ hε hc hξ => ?_⟩
  obtain ⟨hNc_eq, hNc_lo, _, _⟩ := hNc ε c hε ((le_max_left _ _).trans hc)
  obtain ⟨hI_main, hI_left, hI_right, hI_noR⟩ := hInts ε c ξ hε ((le_max_right _ _).trans hc) hξ
  have hcpos : 0 < c := by linarith [hc0I.trans ((le_max_right c0N c0I).trans hc)]
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set Nc := (fctNc h ε c : ℂ)
  have hpre : c ^ (1 / 3 : ℝ) / (2 * π) * (uctCAi * c ^ (-(5 / 6 : ℝ))) =
      uctCAi * c ^ (-(1 / 2 : ℝ)) / (2 * π) := by
    have hpow : c ^ (1 / 3 : ℝ) * c ^ (-(5 / 6 : ℝ)) = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hcpos]; congr 1; norm_num
    calc c ^ (1 / 3 : ℝ) / (2 * π) * (uctCAi * c ^ (-(5 / 6 : ℝ)))
        = uctCAi * (c ^ (1 / 3 : ℝ) * c ^ (-(5 / 6 : ℝ))) / (2 * π) := by ring
      _ = uctCAi * c ^ (-(1 / 2 : ℝ)) / (2 * π) := by rw [hpow]
  have hpt_ae : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      ((fctPhiHat h ε c ((τ : ℂ) * Complex.I) * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
        fctDcomp K4 (fctWarpAlpha h) ε c ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)))) =ᶠ[ae volume]
      fun τ : ℝ => (mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I))) +
        (mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          (fctLeftTail K4 ε c L1 α τ * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
            fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))) := by
    have hae0 : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hae0] with τ hτ
    have hden : fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (fctDcompAt_ne_zero _) (ctHG_ne_zero_of_closed_band ε (by simp) (by simp) (by simp [hτ]))
    have hhat : fctPhiHat h ε c ((τ : ℂ) * Complex.I) =
        fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc + fctLeftTail K4 ε c L1 α τ := by
      show fctPhiHatAt K4 ε c L1 α ((τ : ℂ) * Complex.I) = _
      rw [fctPhiHatAt_left_eq_add_tail, hNc_eq]
    have hD_at : fctDcomp K4 (fctWarpAlpha h) ε c ((τ : ℂ) * Complex.I) =
        fctDcompAt K4 c α ((τ : ℂ) * Complex.I) := rfl
    rw [hhat, hD_at]
    have hlhs : fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
        fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I) =
        (c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) := by
      unfold fctPhiC
      calc ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) /
            (fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) / Nc) *
            fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
            fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)
          = ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc *
              fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)) *
              ((fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) /
               (fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))) := by ring
        _ = _ := by rw [div_self hden, mul_one]
    calc mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          ((fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc + fctLeftTail K4 ε c L1 α τ) *
            fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
            fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))
        = mellinK0 c ((τ : ℂ) * Complex.I) ξ *
            (fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
              fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) +
          mellinK0 c ((τ : ℂ) * Complex.I) ξ *
            (fctLeftTail K4 ε c L1 α τ * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
              fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) := by ring
      _ = _ := by rw [hlhs]
  refine ⟨?_, ?_⟩
  · unfold normDensity warpMainDensity warpLeftTailDensity
    have hcongr_w : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        ctWwarp (fctPhiHat h) (fctDcomp K4 (fctWarpAlpha h)) ε c ((τ : ℂ) * Complex.I)) =
        fun τ : ℝ => ((uctCAi * c ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) *
          (mellinK0 c ((τ : ℂ) * Complex.I) ξ *
            (fctPhiHat h ε c ((τ : ℂ) * Complex.I) * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
              fctDcomp K4 (fctWarpAlpha h) ε c ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))) := by
      funext τ; unfold ctWwarp; ring
    rw [hcongr_w, integral_const_mul, Complex.re_ofReal_mul, ← mul_assoc, hpre]
    rw [integral_congr_ae hpt_ae, integral_add hI_main hI_left, Complex.add_re, mul_add]
  · unfold warpMainDensity warpMainNoRightDensity warpRightTailDensity
    have hsplit_r : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I))) =
        fun τ : ℝ => (mellinK0 c ((τ : ℂ) * Complex.I) ξ *
            ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc)) +
          (mellinK0 c ((τ : ℂ) * Complex.I) ξ *
            ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctRightTail h ε c τ)) := by
      funext τ; unfold fctRightTail; ring
    rw [hsplit_r, integral_add hI_noR hI_right, Complex.add_re, mul_add]

/-- Right-tail error bound: `|warpRightTailDensity h ε c ξ| ≤ C c^{-4/3}` uniformly for all `ξ > 0`. -/
theorem warpRightTailDensity_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      |warpRightTailDensity h ε c ξ| ≤ C * c ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨c0N, _, hNc⟩ := fctNcC_eq_fctNc hK4 h
  obtain ⟨CR, c0R, hCR0, _, hRT⟩ := fctRightTail_bounds hK4 h
  obtain ⟨Ms, c0s, hMs0, _, hPsi_s⟩ := fctPsi_imag_small_bound hK4 h
  obtain ⟨Mlg, c0lg, hMlg0, _, hPsi_lg⟩ := fctPsi_imag_large_bound hK4 h
  obtain ⟨c0I, hc0I, hInts⟩ := warp_integrands_integrable hK4 h
  set I12 : ℝ := ∫ τ : ℝ, (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))
  have hI12_nn : 0 ≤ I12 := integral_nonneg fun τ => by positivity
  set K_int : ℝ := (4 / 5 : ℝ) * (2 * Ms * CR) + 4 * 2 ^ 10 * (2 * Mlg * CR) + (2 * Mlg * CR) * I12
  set C : ℝ := |uctCAi| / (2 * π) * K_int
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, max (max c0N c0R) (max (max c0s c0lg) (max c0I 8)), hC0,
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (by norm_num))), fun ε c ξ hε hc hξ => ?_⟩
  have h1 : c0N ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have h2 : c0R ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have h3 : c0s ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _) |>.trans hc
  have h4 : c0lg ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _) |>.trans hc
  have h5 : c0I ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _) |>.trans hc
  have hc8 : 8 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _) |>.trans hc
  have hcpos : 0 < c := by linarith
  obtain ⟨_, _, _, _⟩ := hNc ε c hε h1
  have hNc_inv : ‖((fctNc h ε c : ℝ) : ℂ)⁻¹‖ ≤ 2 := by
    obtain ⟨_, hNc_lo, _, _⟩ := hNc ε c hε h1
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hRT_bd := (hRT ε c hε h2).2
  have hPs := hPsi_s ε c ξ hε h3 hξ
  have hPlg := hPsi_lg ε c ξ hε h4 hξ
  have hI_right := (hInts ε c ξ hε h5 hξ).2.2.1
  set r := c ^ (-(1 / 3 : ℝ))
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hcpos _
  have hr_le1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  set A1 : ℝ := 2 * Ms * CR
  set A2 : ℝ := 2 * Mlg * CR
  set f1 : ℝ → ℝ := fun τ => (Icc (-r) r).indicator (fun t => |t| ^ (3 / 2 : ℝ)) τ
  set f2 : ℝ → ℝ := fun τ => (Icc (-1) (-r) ∪ Icc r 1).indicator (fun t => |t| ^ (-(3 / 2 : ℝ))) τ
  set f3 : ℝ → ℝ := fun τ => (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))
  have hf1_int : Integrable f1 := by
    have hcont : ContinuousOn (fun t : ℝ => |t| ^ (3 / 2 : ℝ)) (Icc (-r) r) :=
      (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))).continuousOn
    exact (hcont.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hf2_neg : IntegrableOn (fun t : ℝ => |t| ^ (-(3 / 2 : ℝ))) (Icc (-1) (-r)) := by
    refine ContinuousOn.integrableOn_Icc (continuous_abs.continuousOn.rpow_const fun t ht => Or.inl ?_)
    have hle : t ≤ -r := (mem_Icc.mp ht).2
    exact (abs_pos.mpr (by linarith [hr_pos])).ne'
  have hf2_pos : IntegrableOn (fun t : ℝ => |t| ^ (-(3 / 2 : ℝ))) (Icc r 1) := by
    refine ContinuousOn.integrableOn_Icc (continuous_abs.continuousOn.rpow_const fun t ht => Or.inl ?_)
    have hge : r ≤ t := (mem_Icc.mp ht).1
    exact (abs_pos.mpr (by linarith [hr_pos])).ne'
  have hf2_int : Integrable f2 := by
    have hdisj : Disjoint (Icc (-1 : ℝ) (-r)) (Icc r 1) := by
      rw [Set.disjoint_iff_forall_ne]
      intro x hx y hy hxy
      subst hxy
      linarith [hx.2, hy.1, hr_pos]
    have h1 : Integrable ((Icc (-1 : ℝ) (-r)).indicator (fun t => |t| ^ (-(3 / 2 : ℝ)))) :=
      hf2_neg.integrable_indicator measurableSet_Icc
    have h2 : Integrable ((Icc r 1).indicator (fun t => |t| ^ (-(3 / 2 : ℝ)))) :=
      hf2_pos.integrable_indicator measurableSet_Icc
    exact (h1.add h2).congr (ae_of_all _ fun t => (congrFun (Set.indicator_union_of_disjoint hdisj _) t).symm)
  have hf3_int : Integrable f3 := integrable_pow_mul_exp_neg_pi 12
  have hf1_val : ∫ τ : ℝ, f1 τ = (4 / 5 : ℝ) * c ^ (-(5 / 6 : ℝ)) := by
    rw [MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
    have hc_fn : Continuous (fun x : ℝ => |x| ^ (3 / 2 : ℝ)) :=
      continuous_abs.rpow_const (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hc_fn.intervalIntegrable (-r) 0 (μ := volume)) (hc_fn.intervalIntegrable 0 r (μ := volume))
    rw [← hsplit]
    have hneg : ∫ x in (-r)..0, |x| ^ (3 / 2 : ℝ) = ∫ x in (0 : ℝ)..r, x ^ (3 / 2 : ℝ) := by
      have hc := intervalIntegral.integral_comp_neg (fun x : ℝ => |x| ^ (3 / 2 : ℝ)) (a := 0) (b := r)
      simp only [neg_zero, abs_neg] at hc
      rw [← hc]
      refine intervalIntegral.integral_congr fun x hx => ?_
      have hx0 : 0 ≤ x := (uIcc_of_le hr_pos.le ▸ hx).1
      rw [abs_of_nonneg hx0]
    have hpos : ∫ x in (0 : ℝ)..r, |x| ^ (3 / 2 : ℝ) = ∫ x in (0 : ℝ)..r, x ^ (3 / 2 : ℝ) :=
      intervalIntegral.integral_congr fun x hx => by rw [abs_of_nonneg (uIcc_of_le hr_pos.le ▸ hx).1]
    have hev : ∫ x in (0 : ℝ)..r, x ^ (3 / 2 : ℝ) = (2 / 5 : ℝ) * c ^ (-(5 / 6 : ℝ)) := by
      rw [integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < (3 / 2 : ℝ)))]
      have hz : (0 : ℝ) ^ ((3 / 2 : ℝ) + 1) = 0 := Real.zero_rpow (by norm_num)
      have hr5 : r ^ ((3 / 2 : ℝ) + 1) = c ^ (-(5 / 6 : ℝ)) := by
        dsimp [r]; rw [← Real.rpow_mul hcpos.le]; congr 1; norm_num
      rw [hz, sub_zero, hr5]; ring
    rw [hneg, hpos, hev]; ring
  have hf2_val : ∫ τ : ℝ, f2 τ ≤ 4 * c ^ (1 / 6 : ℝ) := by
    have hdisj : Disjoint (Icc (-1 : ℝ) (-r)) (Icc r 1) := by
      rw [Set.disjoint_iff_forall_ne]
      intro x hx y hy hxy
      subst hxy
      linarith [hx.2, hy.1, hr_pos]
    rw [MeasureTheory.integral_indicator (measurableSet_Icc.union measurableSet_Icc),
      setIntegral_union hdisj measurableSet_Icc hf2_neg hf2_pos,
      MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (-1 : ℝ) ≤ -r),
      ← intervalIntegral.integral_of_le hr_le1]
    have hneg : ∫ x in (-1 : ℝ)..(-r), |x| ^ (-(3 / 2 : ℝ)) = ∫ x in r..1, x ^ (-(3 / 2 : ℝ)) := by
      have hc := intervalIntegral.integral_comp_neg (fun x : ℝ => |x| ^ (-(3 / 2 : ℝ))) (a := r) (b := 1)
      simp only [abs_neg] at hc
      rw [← hc]
      refine intervalIntegral.integral_congr fun x hx => ?_
      have hx0 : 0 ≤ x := le_trans hr_pos.le (uIcc_of_le hr_le1 ▸ hx).1
      rw [abs_of_nonneg hx0]
    have hpos : ∫ x in r..1, |x| ^ (-(3 / 2 : ℝ)) = ∫ x in r..1, x ^ (-(3 / 2 : ℝ)) :=
      intervalIntegral.integral_congr fun x hx => by
        rw [abs_of_nonneg (le_trans hr_pos.le (uIcc_of_le hr_le1 ▸ hx).1)]
    have hev : ∫ x in r..1, x ^ (-(3 / 2 : ℝ)) ≤ 2 * c ^ (1 / 6 : ℝ) := by
      have hnz : ∀ x ∈ uIcc r (1 : ℝ), x ≠ 0 := fun x hx =>
        (lt_of_lt_of_le hr_pos (uIcc_of_le hr_le1 ▸ hx).1).ne'
      rw [integral_rpow (Or.inr ⟨by norm_num, fun hmem => hnz 0 hmem rfl⟩)]
      have h1p : (1 : ℝ) ^ (-(3 / 2 : ℝ) + 1) = 1 := Real.one_rpow _
      have hrp : r ^ (-(3 / 2 : ℝ) + 1) = c ^ (1 / 6 : ℝ) := by
        dsimp [r]; rw [← Real.rpow_mul hcpos.le]; congr 1; norm_num
      rw [h1p, hrp]
      norm_num
      linarith [Real.rpow_pos_of_pos hcpos (1 / 6 : ℝ)]
    rw [hneg, hpos]; linarith
  have hc_56 : c⁻¹ ≤ c ^ (-(5 / 6 : ℝ)) := by
    rw [← Real.rpow_neg_one c]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  set g_right : ℝ → ℂ := fun τ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
    ((c : ℂ) * fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) /
      (fctNc h ε c : ℂ) * fctRightTail h ε c τ)
  have hpt : ∀ τ : ℝ, τ ≠ 0 → ‖g_right τ‖ ≤ A1 * f1 τ + (2 ^ 10 * A2 * c⁻¹) * f2 τ + (A2 * c⁻¹) * f3 τ := by
    intro τ hτ
    have hf1_nn : 0 ≤ A1 * f1 τ := by
      dsimp only [f1]; exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => by positivity) τ)
    have hf2_nn : 0 ≤ (2 ^ 10 * A2 * c⁻¹) * f2 τ := by
      dsimp only [f2]; exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => by positivity) τ)
    have hf3_nn : 0 ≤ (A2 * c⁻¹) * f3 τ := by positivity
    have hRT_t := (hRT_bd τ).1
    have hnorm_eq : ‖g_right τ‖ =
        ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          ((c : ℂ) * fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I))‖ *
          (‖(fctNc h ε c : ℂ)⁻¹‖ * ‖fctRightTail h ε c τ‖) := by
      dsimp only [g_right]
      simp only [div_eq_mul_inv, norm_mul]; ring
    rw [hnorm_eq]
    rcases le_or_gt |τ| r with hτr | hτr
    · have hm : τ ∈ Icc (-r) r := abs_le.mp hτr
      have hf1_eq : f1 τ = |τ| ^ (3 / 2 : ℝ) := Set.indicator_of_mem hm _
      have hpow : |τ| ^ (1 / 2 : ℝ) * |τ| = |τ| ^ (3 / 2 : ℝ) := by
        nth_rw 2 [← Real.rpow_one |τ|]
        rw [← Real.rpow_add (abs_pos.mpr hτ)]
        congr 1; norm_num
      have h1 : ‖g_right τ‖ ≤ A1 * f1 τ := by
        rw [hnorm_eq, hf1_eq]
        calc _ ≤ (Ms * c * |τ| ^ (1 / 2 : ℝ)) * (2 * (CR * c⁻¹ * |τ|)) :=
              mul_le_mul (hPs τ hτ hτr) (mul_le_mul hNc_inv hRT_t (norm_nonneg _) (by positivity))
                (by positivity) (by positivity)
          _ = A1 * (c * c⁻¹) * (|τ| ^ (1 / 2 : ℝ) * |τ|) := by simp only [A1]; ring
          _ = A1 * 1 * |τ| ^ (3 / 2 : ℝ) := by rw [mul_inv_cancel₀ hcpos.ne', hpow]
          _ = A1 * |τ| ^ (3 / 2 : ℝ) := by ring
      rw [← hnorm_eq]; linarith
    · rcases le_or_gt |τ| 1 with hτ1 | hτ1
      · have hmem2 : τ ∈ Icc (-1 : ℝ) (-r) ∪ Icc r 1 := by
          rcases lt_or_gt_of_ne hτ with hneg | hpos
          · exact Or.inl ⟨by linarith [(abs_le.mp hτ1).1], by linarith [abs_of_neg hneg, hτr]⟩
          · exact Or.inr ⟨by linarith [abs_of_pos hpos, hτr], by linarith [(abs_le.mp hτ1).2]⟩
        have hf2_eq : f2 τ = |τ| ^ (-(3 / 2 : ℝ)) := Set.indicator_of_mem hmem2 _
        have hpow : |τ| ^ (-(5 / 2 : ℝ)) * |τ| = |τ| ^ (-(3 / 2 : ℝ)) := by
          nth_rw 2 [← Real.rpow_one |τ|]
          rw [← Real.rpow_add (abs_pos.mpr hτ)]
          congr 1; norm_num
        have hp1 : (1 + |τ|) ^ 10 ≤ 2 ^ 10 := pow_le_pow_left₀ (by positivity) (by linarith) 10
        have hexp1 : Real.exp (-(π * |τ|)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (abs_nonneg τ)))
        have hrp_nn : 0 ≤ |τ| ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg τ) _
        have h2 : ‖g_right τ‖ ≤ (2 ^ 10 * A2 * c⁻¹) * f2 τ := by
          rw [hnorm_eq, hf2_eq]
          calc _ ≤ (Mlg * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) *
                (2 * (CR * c⁻¹ * |τ|)) :=
                mul_le_mul (hPlg τ hτ) (mul_le_mul hNc_inv hRT_t (norm_nonneg _) (by positivity))
                  (by positivity) (by positivity)
            _ ≤ (Mlg * |τ| ^ (-(5 / 2 : ℝ)) * 2 ^ 10 * 1) * (2 * (CR * c⁻¹ * |τ|)) := by gcongr
            _ = (2 ^ 10 * A2 * c⁻¹) * (|τ| ^ (-(5 / 2 : ℝ)) * |τ|) := by simp only [A2]; ring
            _ = (2 ^ 10 * A2 * c⁻¹) * |τ| ^ (-(3 / 2 : ℝ)) := by rw [hpow]
        rw [← hnorm_eq]; linarith
      · have hτ1' : 1 ≤ |τ| := hτ1.le
        have hrp : |τ| ^ (-(5 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1' (by norm_num)
        have h1_le : (1 + |τ|) ^ 10 * |τ| ≤ (1 + |τ|) ^ 12 := by
          have h1 : |τ| ≤ 1 + |τ| := by linarith
          calc (1 + |τ|) ^ 10 * |τ| ≤ (1 + |τ|) ^ 10 * (1 + |τ|) := by gcongr
            _ = (1 + |τ|) ^ 11 := by ring
            _ ≤ (1 + |τ|) ^ 12 := pow_le_pow_right₀ (by linarith [abs_nonneg τ]) (by norm_num)
        have hexp_nn : 0 ≤ Real.exp (-(π * |τ|)) := (Real.exp_pos _).le
        have h3 : ‖g_right τ‖ ≤ (A2 * c⁻¹) * f3 τ := by
          rw [hnorm_eq]
          calc _ ≤ (Mlg * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) *
                (2 * (CR * c⁻¹ * |τ|)) :=
                mul_le_mul (hPlg τ hτ) (mul_le_mul hNc_inv hRT_t (norm_nonneg _) (by positivity))
                  (by positivity) (by positivity)
            _ ≤ (Mlg * 1 * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) * (2 * (CR * c⁻¹ * |τ|)) := by gcongr
            _ = (A2 * c⁻¹) * ((1 + |τ|) ^ 10 * |τ| * Real.exp (-(π * |τ|))) := by simp only [A2]; ring
            _ ≤ (A2 * c⁻¹) * ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) := by gcongr
        rw [← hnorm_eq]; linarith
  have hdom_int : Integrable (fun τ : ℝ => A1 * f1 τ + (2 ^ 10 * A2 * c⁻¹) * f2 τ + (A2 * c⁻¹) * f3 τ) :=
    ((hf1_int.const_mul A1).add (hf2_int.const_mul (2 ^ 10 * A2 * c⁻¹))).add (hf3_int.const_mul (A2 * c⁻¹))
  have hint_le : ‖∫ τ : ℝ, g_right τ‖ ≤ K_int * c ^ (-(5 / 6 : ℝ)) := by
    have hae0 : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by rw [ae_iff]; simp
    have h1 := norm_integral_le_of_norm_le hdom_int (by filter_upwards [hae0] with τ hτ; exact hpt τ hτ)
    have hint_sum : (∫ τ : ℝ, A1 * f1 τ + (2 ^ 10 * A2 * c⁻¹) * f2 τ + (A2 * c⁻¹) * f3 τ) =
        A1 * (∫ τ : ℝ, f1 τ) + (2 ^ 10 * A2 * c⁻¹) * (∫ τ : ℝ, f2 τ) + (A2 * c⁻¹) * (∫ τ : ℝ, f3 τ) := by
      have ha1 : (∫ τ : ℝ, (A1 * f1 τ + (2 ^ 10 * A2 * c⁻¹) * f2 τ) + (A2 * c⁻¹) * f3 τ) =
          (∫ τ : ℝ, A1 * f1 τ + (2 ^ 10 * A2 * c⁻¹) * f2 τ) + (∫ τ : ℝ, (A2 * c⁻¹) * f3 τ) :=
        MeasureTheory.integral_add ((hf1_int.const_mul A1).add (hf2_int.const_mul _)) (hf3_int.const_mul _)
      have ha2 : (∫ τ : ℝ, A1 * f1 τ + (2 ^ 10 * A2 * c⁻¹) * f2 τ) =
          (∫ τ : ℝ, A1 * f1 τ) + (∫ τ : ℝ, (2 ^ 10 * A2 * c⁻¹) * f2 τ) :=
        MeasureTheory.integral_add (hf1_int.const_mul A1) (hf2_int.const_mul _)
      have hm1 : (∫ τ : ℝ, A1 * f1 τ) = A1 * (∫ τ : ℝ, f1 τ) := integral_const_mul _ _
      have hm2 : (∫ τ : ℝ, (2 ^ 10 * A2 * c⁻¹) * f2 τ) = (2 ^ 10 * A2 * c⁻¹) * (∫ τ : ℝ, f2 τ) :=
        integral_const_mul _ _
      have hm3 : (∫ τ : ℝ, (A2 * c⁻¹) * f3 τ) = (A2 * c⁻¹) * (∫ τ : ℝ, f3 τ) := integral_const_mul _ _
      rw [ha1, ha2, hm1, hm2, hm3]
    rw [hint_sum] at h1
    have hterm1 : A1 * (∫ τ : ℝ, f1 τ) = (4 / 5 : ℝ) * A1 * c ^ (-(5 / 6 : ℝ)) := by rw [hf1_val]; ring
    have hterm2 : (2 ^ 10 * A2 * c⁻¹) * (∫ τ : ℝ, f2 τ) ≤ 4 * 2 ^ 10 * A2 * c ^ (-(5 / 6 : ℝ)) := by
      have hmul : c⁻¹ * c ^ (1 / 6 : ℝ) = c ^ (-(5 / 6 : ℝ)) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hcpos]; congr 1; norm_num
      calc (2 ^ 10 * A2 * c⁻¹) * (∫ τ : ℝ, f2 τ) ≤ (2 ^ 10 * A2 * c⁻¹) * (4 * c ^ (1 / 6 : ℝ)) :=
            mul_le_mul_of_nonneg_left hf2_val (by positivity)
        _ = 4 * 2 ^ 10 * A2 * (c⁻¹ * c ^ (1 / 6 : ℝ)) := by ring
        _ = 4 * 2 ^ 10 * A2 * c ^ (-(5 / 6 : ℝ)) := by rw [hmul]
    have hterm3 : (A2 * c⁻¹) * (∫ τ : ℝ, f3 τ) ≤ A2 * I12 * c ^ (-(5 / 6 : ℝ)) := by
      calc (A2 * c⁻¹) * (∫ τ : ℝ, f3 τ) = (A2 * I12) * c⁻¹ := by show _ = _; ring
        _ ≤ (A2 * I12) * c ^ (-(5 / 6 : ℝ)) := mul_le_mul_of_nonneg_left hc_56 (by positivity)
    calc ‖∫ τ : ℝ, g_right τ‖
        ≤ A1 * (∫ τ : ℝ, f1 τ) + (2 ^ 10 * A2 * c⁻¹) * (∫ τ : ℝ, f2 τ) + (A2 * c⁻¹) * (∫ τ : ℝ, f3 τ) := h1
      _ ≤ (4 / 5 : ℝ) * A1 * c ^ (-(5 / 6 : ℝ)) + 4 * 2 ^ 10 * A2 * c ^ (-(5 / 6 : ℝ)) +
            A2 * I12 * c ^ (-(5 / 6 : ℝ)) := add_le_add (add_le_add hterm1.le hterm2) hterm3
      _ = K_int * c ^ (-(5 / 6 : ℝ)) := by simp only [K_int, A1, A2]; ring
  have hc_pow : c ^ (-(1 / 2 : ℝ)) * c ^ (-(5 / 6 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_add hcpos]; congr 1; norm_num
  unfold warpRightTailDensity
  rw [abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * π),
    abs_of_pos (Real.rpow_pos_of_pos hcpos _)]
  calc |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) * |(∫ τ : ℝ, g_right τ).re|
      ≤ |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) * ‖∫ τ : ℝ, g_right τ‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) * (K_int * c ^ (-(5 / 6 : ℝ))) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = C * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(5 / 6 : ℝ))) := by simp only [C]; ring
    _ = C * c ^ (-(4 / 3 : ℝ)) := by rw [hc_pow]

/-- Global left-tail error bound: `|warpLeftTailDensity h ε c ξ| ≤ C c^{-3/2}` for all `ξ > 0`. -/
theorem warpLeftTailDensity_global_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      |warpLeftTailDensity h ε c ξ| ≤ C * c ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨c0PhiR, hc0PhiR, hPhiR⟩ := fctPhiHat_right_bound hK4 h
  obtain ⟨ML, c0L, hML0, hc0L, hLT⟩ := fctLeftTail_deriv_bounds hK4 h
  obtain ⟨MD, c0D, hMD0, hc0D, hDHG⟩ := dcomp_ctHG_EJ hK4 h
  set I12 : ℝ := ∫ τ : ℝ, (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))
  have hI12_nn : 0 ≤ I12 := integral_nonneg fun τ => by positivity
  set M_near : ℝ := ML * 2 * (2 ^ 10 * MD)
  set M_far : ℝ := ML * 8 ^ (5 / 2 : ℝ) * MD
  set K_int : ℝ := (1 / 4 : ℝ) * M_near + M_far * I12
  set C : ℝ := |uctCAi| / (2 * π) * K_int
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, max (max c0PhiR c0L) (max c0D 1), hC0,
    le_max_of_le_right (le_max_right _ _), fun ε c ξ hε hc hξ => ?_⟩
  have h1 : c0PhiR ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have h2 : c0L ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have h3 : c0D ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc1 : 1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hcpos : 0 < c := by linarith
  have hPR := hPhiR ε c hε h1
  obtain ⟨_, hLT_sm, hLT_gl⟩ := hLT ε c hε h2
  have hEJ := hDHG ε c hε h3
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  have hm_le : ∀ τ : ℝ, ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ ≤ 1 := fun τ =>
    (norm_mellinK0_imag_le hcpos hξ τ).2.trans
      (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg τ]) (by norm_num))
  set g_left : ℝ → ℂ := fun τ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
    (fctLeftTail K4 ε c L1 α τ * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
      fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))
  set f1 : ℝ → ℝ := fun τ => (Icc (-(1 / 8 : ℝ)) (1 / 8)).indicator (fun _ => (1 : ℝ)) τ
  set f3 : ℝ → ℝ := fun τ => (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))
  have hf1_int : Integrable f1 :=
    (integrableOn_const (C := (1 : ℝ)) (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  have hf3_int : Integrable f3 := integrable_pow_mul_exp_neg_pi 12
  have hf1_val : ∫ τ : ℝ, f1 τ = 1 / 4 := by
    rw [MeasureTheory.integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
      Real.volume_real_Icc_of_le (by norm_num)]
    norm_num
  have hpt : ∀ τ : ℝ, τ ≠ 0 → ‖g_left τ‖ ≤ (M_near * c⁻¹) * f1 τ + (M_far * c⁻¹) * f3 τ := by
    intro τ hτ
    have hf1_nn : 0 ≤ (M_near * c⁻¹) * f1 τ := mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) τ)
    have hf3_nn : 0 ≤ (M_far * c⁻¹) * f3 τ := by positivity
    have hre : ‖g_left τ‖ = ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ *
        (‖fctLeftTail K4 ε c L1 α τ‖ * ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ *
          ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)‖) := by
      dsimp only [g_left]; simp only [norm_mul, mul_assoc]
    rw [hre]
    rcases le_or_gt |τ| (1 / 8) with hτ8 | hτ8
    · have hm : τ ∈ Icc (-(1 / 8 : ℝ)) (1 / 8) := abs_le.mp hτ8
      have hf1_eq : f1 τ = 1 := Set.indicator_of_mem hm _
      have hPR2 : ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ ≤ 2 := (hPR τ).trans (by linarith)
      have hD0 := hEJ.b0 τ hτ
      unfold ejW at hD0
      have hp1 : (1 + |τ|) ^ (10 + 0) ≤ 2 ^ 10 := pow_le_pow_left₀ (by positivity) (by linarith) 10
      have hexp1 : Real.exp (-(π * 1 * |τ|)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg Real.pi_pos.le zero_le_one) (abs_nonneg τ)))
      have hsub : (-(5 / 2 : ℝ)) - ((0 : ℕ) : ℝ) = -(5 / 2 : ℝ) := by norm_num
      rw [hsub] at hD0
      have hrp_nn : 0 ≤ |τ| ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg τ) _
      have hpow_m : |τ| ^ 3 * |τ| ^ (-(5 / 2 : ℝ)) = |τ| ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast |τ| 3, ← Real.rpow_add (abs_pos.mpr hτ)]
        congr 1; norm_num
      have hrp1 : |τ| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg τ) (by linarith) (by norm_num)
      have h1 : ‖g_left τ‖ ≤ (M_near * c⁻¹) * f1 τ := by
        rw [hre, hf1_eq, mul_one]
        calc _ ≤ 1 * ((ML * c⁻¹ * |τ| ^ 3) * 2 * (MD * (|τ| ^ (-(5 / 2 : ℝ)) * 2 ^ 10 * 1))) :=
              mul_le_mul (hm_le τ) (mul_le_mul (mul_le_mul (hLT_sm τ hτ8).1 hPR2 (norm_nonneg _) (by positivity))
                (hD0.trans (by gcongr)) (norm_nonneg _) (by positivity)) (by positivity) zero_le_one
          _ = M_near * c⁻¹ * (|τ| ^ 3 * |τ| ^ (-(5 / 2 : ℝ))) := by simp only [M_near]; ring
          _ = M_near * c⁻¹ * |τ| ^ (1 / 2 : ℝ) := by rw [hpow_m]
          _ ≤ M_near * c⁻¹ * 1 := by gcongr
          _ = M_near * c⁻¹ := by ring
      rw [← hre]; linarith
    · have hτpos : 0 < |τ| := lt_trans (by norm_num) hτ8
      have hD0 := hEJ.b0 τ hτ
      unfold ejW at hD0
      have hsub : (-(5 / 2 : ℝ)) - ((0 : ℕ) : ℝ) = -(5 / 2 : ℝ) := by norm_num
      rw [hsub] at hD0
      have hpow_neg : |τ| ^ (-(5 / 2 : ℝ)) ≤ 8 ^ (5 / 2 : ℝ) := by
        rw [Real.rpow_neg hτpos.le, ← Real.inv_rpow hτpos.le]
        exact Real.rpow_le_rpow (by positivity) (inv_le_of_inv_le₀ (by norm_num) (by linarith)) (by norm_num)
      have hpoly : (1 + |τ|) * (1 + |τ|) * (1 + |τ|) ^ (10 + 0) = (1 + |τ|) ^ 12 := by ring
      have h10 : 0 ≤ (1 + |τ|) ^ (10 + 0) := by positivity
      have hexp0 : 0 ≤ Real.exp (-(π * |τ|)) := (Real.exp_pos _).le
      have h3 : ‖g_left τ‖ ≤ (M_far * c⁻¹) * f3 τ := by
        rw [hre]
        calc _ ≤ 1 * ((ML * c⁻¹ * (1 + |τ|)) * (1 + |τ|) *
              (MD * (8 ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (10 + 0) * Real.exp (-(π * |τ|))))) :=
              mul_le_mul (hm_le τ) (mul_le_mul (mul_le_mul (hLT_gl τ).1 (hPR τ) (norm_nonneg _) (by positivity))
                (hD0.trans (by rw [show Real.exp (-(π * 1 * |τ|)) = Real.exp (-(π * |τ|)) by ring_nf]; gcongr))
                (norm_nonneg _) (by positivity)) (by positivity) zero_le_one
          _ = (M_far * c⁻¹) * ((1 + |τ|) * (1 + |τ|) * (1 + |τ|) ^ (10 + 0) * Real.exp (-(π * |τ|))) := by
              simp only [M_far]; ring
          _ = (M_far * c⁻¹) * f3 τ := by simp only [f3, hpoly]
      rw [← hre]; linarith
  have hdom_int : Integrable (fun τ : ℝ => (M_near * c⁻¹) * f1 τ + (M_far * c⁻¹) * f3 τ) :=
    (hf1_int.const_mul (M_near * c⁻¹)).add (hf3_int.const_mul (M_far * c⁻¹))
  have hint_le : ‖∫ τ : ℝ, g_left τ‖ ≤ K_int * c⁻¹ := by
    have hae0 : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by rw [ae_iff]; simp
    have hbd := norm_integral_le_of_norm_le hdom_int (by filter_upwards [hae0] with τ hτ; exact hpt τ hτ)
    rw [integral_add (hf1_int.const_mul _) (hf3_int.const_mul _),
      integral_const_mul, integral_const_mul, hf1_val] at hbd
    calc ‖∫ τ : ℝ, g_left τ‖ ≤ M_near * c⁻¹ * (1 / 4) + M_far * c⁻¹ * I12 := hbd
      _ = K_int * c⁻¹ := by simp only [K_int]; ring
  have hc_pow : c ^ (-(1 / 2 : ℝ)) * c⁻¹ = c ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
  unfold warpLeftTailDensity
  rw [abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * π),
    abs_of_pos (Real.rpow_pos_of_pos hcpos _)]
  calc |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) * |(∫ τ : ℝ, g_left τ).re|
      ≤ |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) * ‖∫ τ : ℝ, g_left τ‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ |uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π) * (K_int * c⁻¹) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = C * (c ^ (-(1 / 2 : ℝ)) * c⁻¹) := by simp only [C]; ring
    _ = C * c ^ (-(3 / 2 : ℝ)) := by rw [hc_pow]

/-- info: 'FormalResearch.SignUncertainty.normDensity_ctWwarp_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normDensity_ctWwarp_split

/-- info: 'FormalResearch.SignUncertainty.warpRightTailDensity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpRightTailDensity_bound

/-- info: 'FormalResearch.SignUncertainty.warpLeftTailDensity_global_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpLeftTailDensity_global_bound

end FormalResearch.SignUncertainty