/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpOuterPhase

/-!
# Outer shoulder phase `edgeW` bounds for `concretePhiTilde` (`fct:warp-asymp` (1))

Leaf module proving `outerPhi_shoulder_bounds`, which verifies all phase hypotheses of
`fct_edge_ibp_shoulder` for `outerPhi K4 ε c L1 α` on `{τ : ℝ | 1.85 * τ₁ < |τ|}`
whenever `(L1, α)` lies in the `concreteEll1 < 2.55`, `|α| ≤ 2 τ₁²` box (`FctPhaseBox`)
and `c` is sufficiently large.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff Nat
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctEdgeIbp FormalResearch.SignUncertainty.FctSym

namespace FormalResearch.SignUncertainty

/-- Even extension of `τ ↦ concretePhiTilde K4 ε c τ (L1, α)` (`τ ≥ 0`), equal to
`concretePhiTilde K4 ε c τ (L1, α)` on `τ > 0` and smooth on `{τ ≠ 0}`. -/
noncomputable def outerPhi (K4 ε c L1 α τ : ℝ) : ℝ :=
  if 0 ≤ τ then concretePhiTilde K4 ε c τ (L1, α) else concretePhiTilde K4 ε c (-τ) (L1, α)

lemma outerPhi_eq_concretePhiTilde {K4 ε c L1 α τ : ℝ} (hτ : 0 < τ) :
    outerPhi K4 ε c L1 α τ = concretePhiTilde K4 ε c τ (L1, α) :=
  ite_eq_left_iff.mpr fun h => absurd hτ.le h

/-! ### 1. Dispersion `m = uctM` lower and `edgeW`-symbol derivative bounds -/

private lemma mQ_ge_point81 :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 8 ∧ ∀ τ : ℝ, 0 ≤ τ → τ ≤ δ₀ → (0.81 : ℝ) ≤ mQ τ := by
  have hmQ_cont : ContinuousAt mQ 0 :=
    contDiffOn_mQ.continuousOn.continuousAt
      (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4)))
  have hmQ_081 : (0.81 : ℝ) < mQ 0 := by
    rw [mQ_zero]
    have hpi : (3.14 : ℝ) < π := Real.pi_gt_d2
    have hpi2 : (9.85 : ℝ) < π ^ 2 := by nlinarith only [hpi]
    linarith only [hpi2]
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hmQ_cont (mQ 0 - 0.81) (by linarith only [hmQ_081])
  refine ⟨min (δ / 2) (1 / 8), by positivity, min_le_right _ _, fun τ hτ0 hτ => ?_⟩
  have hd : dist τ 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hτ0]
    linarith only [hτ, min_le_left (δ / 2) (1 / 8), hδ0]
  have h1 := abs_lt.mp (by simpa [Real.dist_eq] using hδ hd)
  linarith only [h1.1]

private lemma uctM_deriv_edgeW_large :
    ∃ A : ℕ → ℝ, (∀ k, 0 ≤ A k) ∧ ∀ k, 1 ≤ k → ∀ τ : ℝ, 0 < τ →
      |iteratedDeriv k uctM τ| ≤ A k * edgeW τ ^ (-(k : ℤ)) := by
  obtain ⟨K, hK0, hK⟩ := uctM_deriv_symbol
  refine ⟨fun k => K (k - 1), fun k => hK0 (k - 1), fun k hk τ hτ => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  change |iteratedDeriv (m + 1) uctM τ| ≤ K m * edgeW τ ^ (-((m + 1 : ℕ) : ℤ))
  rw [iteratedDeriv_succ']
  have h1 := hK m τ hτ
  have hw_le : edgeW τ ≤ τ := by
    have := edgeW_le_abs τ; rwa [abs_of_pos hτ] at this
  have hpow : (τ ^ (m + 1))⁻¹ ≤ edgeW τ ^ (-((m + 1 : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact inv_anti₀ (pow_pos (edgeW_pos hτ.ne') _) (pow_le_pow_left₀ (edgeW_pos hτ.ne').le hw_le _)
  calc |iteratedDeriv m (deriv uctM) τ|
      ≤ K m * 1 * (τ ^ (m + 1))⁻¹ := h1
    _ = K m * (τ ^ (m + 1))⁻¹ := by rw [mul_one]
    _ ≤ K m * edgeW τ ^ (-((m + 1 : ℕ) : ℤ)) := mul_le_mul_of_nonneg_left hpow (hK0 m)

private lemma sq_iteratedDeriv_bound {t : ℝ} (ht : 0 < t) (j : ℕ) :
    |iteratedDeriv j (fun s : ℝ => s ^ 2) t| ≤ 2 * t ^ 2 * (t ^ j)⁻¹ := by
  have hd1 : deriv (fun s : ℝ => s ^ 2) = fun s => 2 * s := by
    ext s
    simp [(hasDerivAt_pow 2 s).deriv]
  rcases Nat.lt_trichotomy j 1 with hj0 | rfl | hj1
  · obtain rfl : j = 0 := by omega
    simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one, abs_of_nonneg (sq_nonneg t)]
    exact le_mul_of_one_le_left (sq_nonneg t) (by norm_num)
  · rw [iteratedDeriv_one, hd1,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos ht, pow_one]
    have h2eq : 2 * t = 2 * t ^ 2 * t⁻¹ := by field_simp [ht.ne']
    rw [← h2eq]
  · rcases eq_or_lt_of_le (show 2 ≤ j by omega) with rfl | hj2
    · rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ', hd1, iteratedDeriv_one,
        show deriv (fun s : ℝ => (2 : ℝ) * s) t = 2 by simp,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h2eq : (2 : ℝ) = 2 * t ^ 2 * (t ^ 2)⁻¹ := by field_simp [ht.ne']
      exact h2eq.le
    · have h0 : iteratedDeriv j (fun s : ℝ => s ^ 2) t = 0 := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 3 ≤ j)
        have hd2 : deriv (fun s : ℝ => (2 : ℝ) * s) = fun _ => (2 : ℝ) := by
          ext s; simp
        rw [show m + 3 = m + 1 + 1 + 1 by omega, iteratedDeriv_succ', hd1,
          iteratedDeriv_succ', hd2, iteratedDeriv_succ', deriv_const']
        simp
      rw [h0, abs_zero]
      positivity

private lemma uctM_deriv_edgeW_small :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ k, 1 ≤ k → ∀ τ ∈ Ioc (0 : ℝ) (1 / 8),
      |iteratedDeriv k uctM τ| ≤ C k * τ ^ 2 * edgeW τ ^ (-(k : ℤ)) := by
  have hB : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ τ ∈ Icc (0 : ℝ) (1 / 8), |iteratedDeriv j mQ τ| ≤ B := by
    intro j
    have hcd : ContDiffOn ℝ ∞ (iteratedDeriv j mQ) (Set.Ioo (-1 / 4 : ℝ) (1 / 4)) :=
      FctSym.contDiffOn_iteratedDeriv_gen isOpen_Ioo (contDiffOn_mQ.of_le (WithTop.coe_le_coe.mpr le_top)) j
    have hcont : ContinuousOn (iteratedDeriv j mQ) (Icc 0 (1 / 8)) :=
      hcd.continuousOn.mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    exact ⟨max B 0, le_max_right _ _, fun τ hτ => (hB τ hτ).trans (le_max_left _ _)⟩
  choose B hB0 hB using hB
  refine ⟨fun k => ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * 2 * B (k - j),
    fun k => Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) zero_le_two) (hB0 _), ?_⟩
  intro k _ τ hτ
  have hτ_pos : 0 < τ := hτ.1
  have hτ_le : τ ≤ 1 / 8 := hτ.2
  have hmem_Ioo0 : τ ∈ Set.Ioo (0 : ℝ) (1 / 4) := ⟨hτ_pos, by linarith only [hτ_le]⟩
  have hmem_Ioo : τ ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4) :=
    ⟨by linarith only [hτ_pos], by linarith only [hτ_le]⟩
  have hev : uctM =ᶠ[𝓝 τ] fun s => s ^ 2 * mQ s := by
    filter_upwards [isOpen_Ioo.mem_nhds hmem_Ioo0] with s hs
    exact uctM_eq_sq_mul_mQ hs.1
  have hsq_cd : ContDiffAt ℝ k (fun s : ℝ => s ^ 2) τ :=
    ((contDiff_id : ContDiff ℝ ∞ fun x : ℝ => x).pow 2).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hmQ_cd : ContDiffAt ℝ k mQ τ :=
    (contDiffOn_mQ.contDiffAt (isOpen_Ioo.mem_nhds hmem_Ioo)).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [hev.iteratedDeriv_eq k]
  change |iteratedDeriv k ((fun s : ℝ => s ^ 2) * mQ) τ| ≤ _
  rw [iteratedDeriv_mul hsq_cd hmQ_cd]
  have hw_eq : edgeW τ = τ :=
    le_antisymm (by have h := edgeW_le_abs τ; rwa [abs_of_pos hτ_pos] at h)
      (edgeW_ge_r (by linarith only [hτ_le]) (by rw [abs_of_pos hτ_pos]))
  rw [← Real.norm_eq_abs]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hbd_sq := sq_iteratedDeriv_bound hτ_pos j
  have hbd_mQ := hB (k - j) τ ⟨hτ_pos.le, hτ_le⟩
  have hpow_le : (τ ^ j)⁻¹ ≤ τ ^ (-(k : ℤ)) := by
    have hpow_le' : τ ^ k ≤ τ ^ j := pow_le_pow_of_le_one hτ_pos.le (by linarith only [hτ_le]) hj_le
    rw [zpow_neg, zpow_natCast]
    exact inv_anti₀ (pow_pos hτ_pos k) hpow_le'
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), hw_eq]
  calc (k.choose j : ℝ) * |iteratedDeriv j (fun s => s ^ 2) τ| * |iteratedDeriv (k - j) mQ τ|
      ≤ (k.choose j : ℝ) * (2 * τ ^ 2 * (τ ^ j)⁻¹) * B (k - j) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hbd_sq (Nat.cast_nonneg _)) hbd_mQ
            (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by positivity))
    _ = (k.choose j : ℝ) * 2 * B (k - j) * τ ^ 2 * (τ ^ j)⁻¹ := by ring
    _ ≤ (k.choose j : ℝ) * 2 * B (k - j) * τ ^ 2 * τ ^ (-(k : ℤ)) :=
          mul_le_mul_of_nonneg_left hpow_le (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) zero_le_two) (hB0 _)) (sq_nonneg τ))

/-! ### 2. Exact derivatives of `concretePhiTilde` on `Ioi 0` -/

private lemma concretePhiTilde_contDiffOn {K4 ε c L1 α : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ_le : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) :
    ContDiffOn ℝ ∞ (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) (Ioi 0) := by
  have hcd := concretePhiLambda_contDiffOn (ε := ε) (lam := 1) hK4 hc hτ_le
  have hmap : ContDiffOn ℝ ∞ (fun t : ℝ => (t, (L1, α))) (Ioi 0) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  exact (hcd.comp hmap fun t ht => ⟨ht, mem_univ _⟩).congr fun t _ => rfl

private lemma concretePhiTilde_deriv_eq {K4 ε c L1 α τ : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ_le : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (hτ : 0 < τ) :
    deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ =
      (L1 - ctTheta1 ε / c - uctM τ) + c⁻¹ * (ctTheta1 ε - deriv (outerTheta ε) τ) +
        c⁻¹ * deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) τ := by
  have hv_cd : ContDiff ℝ ∞ (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) := by
    have hd := vTotal_data hK4 hc hτ_le α
    exact contDiff_fctThetaD hd.1 hd.2.1
  have hint_hd : HasDerivAt (fun t : ℝ => ∫ u in (0 : ℝ)..t, hankelEdgeM u) (uctM τ) τ := by
    have hint : IntervalIntegrable hankelEdgeM volume 0 τ :=
      (hankelEdgeM_continuousOn.mono fun x hx => by
        rw [Set.uIcc_of_le hτ.le] at hx; exact hx.1).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter hankelEdgeM (𝓝 τ) :=
      (hankelEdgeM_continuousOn.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi τ hτ
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas (hankelEdgeM_hasDerivAt hτ).continuousAt
  have hph_hd : HasDerivAt (fun t : ℝ => concretePhiPh t L1) (L1 - uctM τ) τ := by
    unfold concretePhiPh
    simpa only [mul_one] using ((hasDerivAt_id' τ).const_mul L1).fun_sub hint_hd
  have hth_hd : HasDerivAt (outerTheta ε) (deriv (outerTheta ε) τ) τ :=
    ((contDiff_outerTheta ε).differentiable (by simp) τ).hasDerivAt
  have hv_hd : HasDerivAt (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))))
      (deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) τ) τ :=
    ((hv_cd.differentiable (by simp) τ)).hasDerivAt
  have htot : HasDerivAt (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α))
      ((L1 - uctM τ) - c⁻¹ * deriv (outerTheta ε) τ +
        1 * c⁻¹ * deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) τ) τ := by
    change HasDerivAt (fun t : ℝ => concretePhiPh t L1 - c⁻¹ * outerTheta ε t +
      1 * c⁻¹ * fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) t) _ τ
    exact (hph_hd.fun_sub (hth_hd.const_mul c⁻¹)).fun_add (hv_hd.const_mul (1 * c⁻¹))
  rw [htot.deriv]
  ring

private lemma concretePhiTilde_iteratedDeriv_succ_eq {K4 ε c L1 α τ : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ_le : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (hτ : 0 < τ)
    {k : ℕ} (hk1 : 1 ≤ k) :
    iteratedDeriv (k + 1) (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ =
      -iteratedDeriv k uctM τ - c⁻¹ * iteratedDeriv (k + 1) (outerTheta ε) τ +
        c⁻¹ * iteratedDeriv (k + 1) (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) τ := by
  have hv_cd : ContDiff ℝ ∞ (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) := by
    have hd := vTotal_data hK4 hc hτ_le α
    exact contDiff_fctThetaD hd.1 hd.2.1
  have hph_cd : ContDiffAt ℝ (k + 1) (fun t : ℝ => concretePhiPh t L1) τ := by
    have hcd := concretePhiLambda_contDiffOn (ε := ε) (lam := 0) hK4 hc hτ_le
    have hmap : ContDiffOn ℝ ∞ (fun t : ℝ => (t, (L1, α))) (Ioi 0) :=
      (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => (L1, α))).contDiffOn
    have hph_on : ContDiffOn ℝ ∞ (fun t : ℝ => concretePhiPh t L1 - c⁻¹ * outerTheta ε t) (Ioi 0) :=
      (hcd.comp hmap fun t ht => ⟨ht, mem_univ _⟩).congr fun t _ => by
        dsimp only [Function.comp_def]; unfold concretePhiLambda; ring
    have hth_on : ContDiffOn ℝ ∞ (fun t : ℝ => c⁻¹ * outerTheta ε t) (Ioi 0) :=
      (contDiff_const.mul (contDiff_outerTheta ε)).of_le (by simp) |>.contDiffOn
    have hsum' : ContDiffOn ℝ ∞ (fun t : ℝ => concretePhiPh t L1) (Ioi 0) :=
      (hph_on.add hth_on).congr fun t _ => by
        change concretePhiPh t L1 = (concretePhiPh t L1 - c⁻¹ * outerTheta ε t) + c⁻¹ * outerTheta ε t
        ring
    exact (hsum'.contDiffAt (isOpen_Ioi.mem_nhds hτ)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hth_cd : ContDiffAt ℝ (k + 1) (fun t : ℝ => c⁻¹ * outerTheta ε t) τ :=
    ((contDiff_const.mul (contDiff_outerTheta ε)).contDiffAt).of_le (by simp)
  have hv_cd_at : ContDiffAt ℝ (k + 1) (fun t : ℝ => c⁻¹ * fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) t) τ :=
    ((contDiff_const.mul hv_cd).contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  have hsub_at : ContDiffAt ℝ (k + 1) (fun t : ℝ => concretePhiPh t L1 - c⁻¹ * outerTheta ε t) τ :=
    hph_cd.sub hth_cd
  have hfn_eq : (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) =
      (fun t : ℝ => concretePhiPh t L1 - c⁻¹ * outerTheta ε t) +
        fun t : ℝ => c⁻¹ * fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) t := by
    ext t; dsimp only [Pi.add_apply]; unfold concretePhiTilde concretePhiLambda; ring
  have hsub_eq : (fun t : ℝ => concretePhiPh t L1 - c⁻¹ * outerTheta ε t) =
      (fun t : ℝ => concretePhiPh t L1) - fun t : ℝ => c⁻¹ * outerTheta ε t := rfl
  rw [hfn_eq, iteratedDeriv_add hsub_at hv_cd_at, hsub_eq, iteratedDeriv_sub hph_cd hth_cd,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  have hph_deriv : deriv (fun t : ℝ => concretePhiPh t L1) =ᶠ[𝓝 τ] fun t : ℝ => L1 - uctM t := by
    filter_upwards [isOpen_Ioi.mem_nhds hτ] with s hs
    have hint : IntervalIntegrable hankelEdgeM volume 0 s :=
      (hankelEdgeM_continuousOn.mono fun x hx => by
        rw [Set.uIcc_of_le hs.le] at hx; exact hx.1).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter hankelEdgeM (𝓝 s) :=
      (hankelEdgeM_continuousOn.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi s hs
    have hint_hd := intervalIntegral.integral_hasDerivAt_right hint hmeas (hankelEdgeM_hasDerivAt hs).continuousAt
    have hph_hd : HasDerivAt (fun t : ℝ => concretePhiPh t L1) (L1 - uctM s) s := by
      unfold concretePhiPh
      exact (((hasDerivAt_id' s).const_mul L1).fun_sub hint_hd).congr_deriv (by rw [mul_one]; rfl)
    exact hph_hd.deriv
  have hm_cd : ContDiffAt ℝ k uctM τ :=
    (CtMDeriv.contDiffOn_hankelEdgeM.contDiffAt (isOpen_Ioi.mem_nhds hτ)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hconst_cd : ContDiffAt ℝ k (fun _ : ℝ => L1) τ := contDiff_const.contDiffAt.of_le le_top
  have hph_k : iteratedDeriv (k + 1) (fun t : ℝ => concretePhiPh t L1) τ = -iteratedDeriv k uctM τ := by
    rw [iteratedDeriv_succ', hph_deriv.iteratedDeriv_eq k]
    change iteratedDeriv k ((fun _ : ℝ => L1) - uctM) τ = _
    rw [iteratedDeriv_sub hconst_cd hm_cd]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hL1_zero : iteratedDeriv (m + 1) (fun _ : ℝ => L1) τ = 0 := by
      rw [iteratedDeriv_succ', deriv_const']; simp
    rw [hL1_zero, zero_sub]
  rw [hph_k]

/-! ### 3. Main shoulder theorem for `outerPhi` -/

/-- **`fct:warp-asymp` (1) (outer phase bounds)**:
For every `n ≥ 1`, there exist constants `κ > 0`, `c₀ ≥ 1`, `K : ℕ → ℝ` (nonnegative) such that for all
`K4 ≥ 1`, `ε ∈ {1, -1}`, `c ≥ c₀` with `τ₁ ≤ τD` and `K4 τ₁² ≤ 1`, and `(L1, α)` satisfying
`concreteEll1 ε c L1 < 2.55` and `|α| ≤ 2 c^{-1/2}`, the even phase `outerPhi K4 ε c L1 α` satisfies all
phase hypotheses of `fct_edge_ibp_shoulder` on `{τ : ℝ | 1.85 τ₁ < |τ|}` with scale `u = c^{-1/2}`:
1. `ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Φ {τ | 1.85 τ₁ < |τ|}`;
2. `κ * c^{-1/2} ≤ |deriv Φ τ|`;
3. `|iteratedDeriv (k + 1) Φ τ| ≤ K k * edgeW τ ^ (-k) * |deriv Φ τ|` for all `1 ≤ k ≤ n`. -/
private lemma iteratedDeriv_comp_neg_eq (f : ℝ → ℝ) (m : ℕ) (τ : ℝ) :
    iteratedDeriv m (fun s => f (-s)) τ = (-1 : ℝ) ^ m * iteratedDeriv m f (-τ) := by
  induction m generalizing f τ with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
      have hd : deriv (fun s => f (-s)) = fun s => -deriv f (-s) := by
        ext s; exact deriv_comp_neg f s
      rw [iteratedDeriv_succ', hd, iteratedDeriv_fun_neg, ih (deriv f) τ, iteratedDeriv_succ',
        pow_succ']
      ring

theorem outerPhi_shoulder_bounds (n : ℕ) (_hn : 1 ≤ n) :
    ∃ (κ c₀ : ℝ) (K : ℕ → ℝ),
      0 < κ ∧ 1 ≤ c₀ ∧ (∀ k, 0 ≤ K k) ∧
      ∀ {K4 ε c L1 α : ℝ}, 1 ≤ K4 → (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose →
        K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 →
        concreteEll1 ε c L1 < 2.55 → |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 →
        let τ₁ := c ^ (-(1 / 4 : ℝ))
        let r := 1.85 * τ₁
        let Φ := outerPhi K4 ε c L1 α
        ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Φ {τ : ℝ | r < |τ|} ∧
        (∀ τ : ℝ, r < |τ| → κ * c ^ (-(1 / 2 : ℝ)) ≤ |deriv Φ τ|) ∧
        (∀ k, 1 ≤ k → k ≤ n → ∀ τ : ℝ, r < |τ| →
          |iteratedDeriv (k + 1) Φ τ| ≤ K k * edgeW τ ^ (-(k : ℤ)) * |deriv Φ τ|) := by
  obtain ⟨δ₀, hδ₀_pos, hδ₀_le, hmQ_lb⟩ := mQ_ge_point81
  obtain ⟨Cm_sm, hCm_sm0, hm_sm⟩ := uctM_deriv_edgeW_small
  obtain ⟨Cm_lg, hCm_lg0, hm_lg⟩ := uctM_deriv_edgeW_large
  obtain ⟨Cθ, hCθ0, hθ'⟩ := ct_outer_theta_deriv_bound
  have hθ_poly : ∃ Cθk : ℕ → ℝ, (∀ k, 0 ≤ Cθk k) ∧
      ∀ k, 1 ≤ k → k ≤ n + 1 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ τ : ℝ,
        |iteratedDeriv k (outerTheta ε) τ| ≤ Cθk k := by
    have hex : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        (∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ τ : ℝ, |iteratedDeriv (k + 1) (outerTheta ε) τ| ≤ C) := by
      intro k
      obtain ⟨Cp, hCp⟩ := theta_deriv_poly (ε := 1) (Or.inr rfl) (Nat.succ_pos k)
      obtain ⟨Cm, hCm⟩ := theta_deriv_poly (ε := -1) (Or.inl rfl) (Nat.succ_pos k)
      refine ⟨max (max Cp Cm) 0, le_max_right _ _, fun ε hε τ => ?_⟩
      have hden : (1 : ℝ) ≤ (1 + |τ|) ^ (k + 1 + 1) := one_le_pow₀ (by linarith only [abs_nonneg τ])
      rcases hε with rfl | rfl
      · exact (hCp τ).trans ((div_le_self (le_trans (abs_nonneg _) (by simpa using hCp 0)) hden).trans
          ((le_max_left Cp Cm).trans (le_max_left _ _)))
      · exact (hCm τ).trans ((div_le_self (le_trans (abs_nonneg _) (by simpa using hCm 0)) hden).trans
          ((le_max_right Cp Cm).trans (le_max_left _ _)))
    choose Cθs hCθs0 hCθs using hex
    exact ⟨fun k => Cθs (k - 1), fun k => hCθs0 _, fun k hk1 _ ε hε τ => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact hCθs m ε hε τ⟩
  obtain ⟨Cθk, hCθk0, hθk_bd⟩ := hθ_poly
  obtain ⟨_, _, _, _, C_th_c, _, _, _, _, _, hCthc0, _, hv_th⟩ := vTotal_thetaD_edge_bounds n
  let Mθ : ℝ := max (|ctTheta1 1|) (|ctTheta1 (-1)|) + Cθ
  let C_c₀ : ℝ := max 1 (max ((2.55 + 0.20) / (0.41 * δ₀ ^ 2)) (max (20 * Mθ) (20 * C_th_c 1))) ^ 4
  have hMθ0 : 0 ≤ Mθ := by positivity
  have hδ₀_sq_pos : 0 < δ₀ ^ 2 := sq_pos_of_pos hδ₀_pos
  have hCc₀_ge1 : 1 ≤ C_c₀ := by
    have hb1 : (1 : ℝ) ≤ max 1 (max ((2.55 + 0.20) / (0.41 * δ₀ ^ 2)) (max (20 * Mθ) (20 * C_th_c 1))) :=
      le_max_left _ _
    exact one_le_pow₀ hb1
  let K_fun : ℕ → ℝ := fun k =>
    Cm_sm k / 0.03 + Cm_lg k / (0.20 * δ₀ ^ 2) + 10 * Cθk (k + 1) + 10 * C_th_c (k + 1)
  have hK_nn : ∀ k, 0 ≤ K_fun k := fun k => by
    have h1 := hCm_sm0 k; have h2 := hCm_lg0 k; have h3 := hCθk0 (k + 1); have h4 := hCthc0 (k + 1)
    positivity
  refine ⟨0.10, C_c₀, K_fun, by norm_num, hCc₀_ge1, hK_nn, ?_⟩
  intro K4 ε c L1 α hK4 hε hc_c₀ hτD hK4τ hL1 hα
  dsimp only
  have hc1 : 1 ≤ c := hCc₀_ge1.trans hc_c₀
  have hc0 : 0 < c := by linarith only [hc1]
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_le1 : τ₁ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hcτ : τ₁ ^ 4 * c = 1 := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    rw [Real.rpow_neg_one]; exact inv_mul_cancel₀ hc0.ne'
  have hτ₁2 : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hcinv : c⁻¹ = τ₁ ^ 4 := inv_eq_of_mul_eq_one_right (by rwa [mul_comm])
  have hτ₁_bd : τ₁ ≤ (max 1 (max ((2.55 + 0.20) / (0.41 * δ₀ ^ 2)) (max (20 * Mθ) (20 * C_th_c 1))))⁻¹ := by
    have hb_pos : 0 < max 1 (max ((2.55 + 0.20) / (0.41 * δ₀ ^ 2)) (max (20 * Mθ) (20 * C_th_c 1))) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hpow4 : (max 1 (max ((2.55 + 0.20) / (0.41 * δ₀ ^ 2)) (max (20 * Mθ) (20 * C_th_c 1)))) ^ 4 ≤ c := hc_c₀
    have hpow4' : (c⁻¹) ≤ ((max 1 (max ((2.55 + 0.20) / (0.41 * δ₀ ^ 2)) (max (20 * Mθ) (20 * C_th_c 1))))⁻¹) ^ 4 := by
      rw [inv_pow]; exact inv_anti₀ (pow_pos hb_pos 4) hpow4
    rw [hcinv] at hpow4'
    by_contra hlt
    push Not at hlt
    have h4 : ((max 1 (max ((2.55 + 0.20) / (0.41 * δ₀ ^ 2)) (max (20 * Mθ) (20 * C_th_c 1))))⁻¹) ^ 4 < τ₁ ^ 4 :=
      pow_lt_pow_left₀ hlt (inv_nonneg.mpr hb_pos.le) (by norm_num)
    linarith only [hpow4', h4]
  have hcd_pos : ContDiffOn ℝ ∞ (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) (Ioi 0) :=
    concretePhiTilde_contDiffOn hK4 hc0 hτD
  have hopen_set : IsOpen {τ : ℝ | 1.85 * τ₁ < |τ|} :=
    isOpen_lt continuous_const continuous_abs
  have h_all_pos : ∀ τ : ℝ, 1.85 * τ₁ < τ →
      (0.10 * c ^ (-(1 / 2 : ℝ)) ≤ |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| ∧
       (τ ≤ δ₀ → 0.03 * τ ^ 2 ≤ |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ|) ∧
       (δ₀ < τ → 0.20 * δ₀ ^ 2 ≤ |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ|)) ∧
      (∀ k, 1 ≤ k → k ≤ n →
        |iteratedDeriv (k + 1) (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| ≤
          K_fun k * edgeW τ ^ (-(k : ℤ)) * |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ|) := by
    obtain ⟨_, _, _, _, hv_pt⟩ := hv_th hK4 hc1 hτD hK4τ hα
    intro τ hτr
    have hτ_pos : 0 < τ := lt_trans (by positivity) hτr
    have hτ_ne : τ ≠ 0 := hτ_pos.ne'
    have hpt := hv_pt τ hτr
    -- Perturbation bound on `Φ'`
    have hθ_eps : |ctTheta1 ε| + |deriv (outerTheta ε) τ| ≤ Mθ := by
      have h1 : |ctTheta1 ε| ≤ max (|ctTheta1 1|) (|ctTheta1 (-1)|) := by
        rcases hε with rfl | rfl
        · exact le_max_left _ _
        · exact le_max_right _ _
      have h2 : |deriv (outerTheta ε) τ| ≤ Cθ :=
        (hθ' ε hε.symm τ).trans (div_le_self hCθ0 (one_le_pow₀ (by linarith only [abs_nonneg τ])))
      dsimp only [Mθ]; linarith only [h1, h2]
    have hpert1 : c⁻¹ * |ctTheta1 ε - deriv (outerTheta ε) τ| ≤ 0.05 * c ^ (-(1 / 2 : ℝ)) := by
      have hτ₁_le_M : 20 * Mθ * τ₁ ≤ 1 := by
        by_cases hM : Mθ = 0
        · rw [hM, mul_zero, zero_mul]; norm_num
        · have hMpos : 0 < 20 * Mθ := by linarith only [lt_of_le_of_ne hMθ0 (Ne.symm hM)]
          have hle := hτ₁_bd.trans (inv_anti₀ hMpos ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
          calc 20 * Mθ * τ₁ ≤ 20 * Mθ * (20 * Mθ)⁻¹ := mul_le_mul_of_nonneg_left hle hMpos.le
            _ = 1 := mul_inv_cancel₀ hMpos.ne'
      have hc_eq : c⁻¹ = τ₁ ^ 2 * c ^ (-(1 / 2 : ℝ)) := by rw [hcinv, ← hτ₁2]; ring
      calc c⁻¹ * |ctTheta1 ε - deriv (outerTheta ε) τ|
          ≤ c⁻¹ * (|ctTheta1 ε| + |deriv (outerTheta ε) τ|) :=
              mul_le_mul_of_nonneg_left (abs_sub _ _) (inv_nonneg.mpr hc0.le)
        _ ≤ τ₁ ^ 2 * c ^ (-(1 / 2 : ℝ)) * Mθ := by
              rw [hc_eq]; exact mul_le_mul_of_nonneg_left hθ_eps (by positivity)
        _ ≤ τ₁ * Mθ * c ^ (-(1 / 2 : ℝ)) := by
              have hτ21 : τ₁ ^ 2 ≤ τ₁ := by nlinarith only [hτ₁.le, hτ₁_le1]
              calc τ₁ ^ 2 * c ^ (-(1 / 2 : ℝ)) * Mθ = (τ₁ ^ 2 * Mθ) * c ^ (-(1 / 2 : ℝ)) := by ring
                _ ≤ (τ₁ * Mθ) * c ^ (-(1 / 2 : ℝ)) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hτ21 hMθ0) (Real.rpow_nonneg hc0.le _)
                _ = τ₁ * Mθ * c ^ (-(1 / 2 : ℝ)) := by ring
        _ ≤ 0.05 * c ^ (-(1 / 2 : ℝ)) := by
              have h20 : τ₁ * Mθ ≤ 0.05 := by linarith only [hτ₁_le_M]
              exact mul_le_mul_of_nonneg_right h20 (Real.rpow_nonneg hc0.le _)
    have hpert2 : c⁻¹ * |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤ 0.05 * c ^ (-(1 / 2 : ℝ)) := by
      have h1 := hpt.2.2.2 1 le_rfl (Nat.succ_le_succ (Nat.zero_le _))
      rw [iteratedDeriv_one, Nat.sub_self, Nat.cast_zero, neg_zero, zpow_zero, mul_one,
        show c ^ (-(1 / 4 : ℝ)) = τ₁ from rfl] at h1
      have hτ₁_le_C : C_th_c 1 * τ₁ ≤ 0.05 := by
        by_cases hC0 : C_th_c 1 = 0
        · rw [hC0, zero_mul]; norm_num
        · have hCpos : 0 < 20 * C_th_c 1 := lt_of_le_of_ne (mul_nonneg (by norm_num) (hCthc0 1)) (by
            intro h; apply hC0; linarith only [h])
          have hle := hτ₁_bd.trans (inv_anti₀ hCpos ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
          have h20 : 20 * C_th_c 1 * τ₁ ≤ 1 := by
            calc 20 * C_th_c 1 * τ₁ ≤ 20 * C_th_c 1 * (20 * C_th_c 1)⁻¹ := mul_le_mul_of_nonneg_left hle hCpos.le
              _ = 1 := mul_inv_cancel₀ hCpos.ne'
          linarith only [h20]
      exact h1.trans (by
        calc C_th_c 1 * τ₁ * c ^ (-(1 / 2 : ℝ)) ≤ 0.05 * c ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right hτ₁_le_C (Real.rpow_nonneg hc0.le _))
    have hL1_ub : L1 - ctTheta1 ε / c < 2.55 * τ₁ ^ 2 := by
      have hell : (L1 - ctTheta1 ε / c) / τ₁ ^ 2 < 2.55 := hL1
      exact (div_lt_iff₀ (sq_pos_of_pos hτ₁)).mp hell
    have hmain_sub : ∀ {M : ℝ}, M ≤ uctM τ - (L1 - ctTheta1 ε / c) →
        M - 0.10 * c ^ (-(1 / 2 : ℝ)) ≤ |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| := by
      intro M hM
      rw [concretePhiTilde_deriv_eq hK4 hc0 hτD hτ_pos]
      have htri := abs_sub_abs_le_abs_sub (uctM τ - (L1 - ctTheta1 ε / c))
        (c⁻¹ * (ctTheta1 ε - deriv (outerTheta ε) τ) +
          c⁻¹ * deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ)
      have heq_sub : uctM τ - (L1 - ctTheta1 ε / c) -
          (c⁻¹ * (ctTheta1 ε - deriv (outerTheta ε) τ) +
            c⁻¹ * deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ) =
          -((L1 - ctTheta1 ε / c - uctM τ) + c⁻¹ * (ctTheta1 ε - deriv (outerTheta ε) τ) +
            c⁻¹ * deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ) := by ring
      rw [heq_sub, abs_neg] at htri
      have hpert_tri : |c⁻¹ * (ctTheta1 ε - deriv (outerTheta ε) τ) +
          c⁻¹ * deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤ 0.10 * c ^ (-(1 / 2 : ℝ)) := by
        have ha := abs_add_le (c⁻¹ * (ctTheta1 ε - deriv (outerTheta ε) τ))
          (c⁻¹ * deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ)
        rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hc0)] at ha
        linarith only [ha, hpert1, hpert2]
      linarith only [hM, htri, hpert_tri, le_abs_self (uctM τ - (L1 - ctTheta1 ε / c))]
    have hdiff_lb : 0.20 * c ^ (-(1 / 2 : ℝ)) ≤ uctM τ - (L1 - ctTheta1 ε / c) ∧
        (τ ≤ δ₀ → 0.06 * τ ^ 2 ≤ uctM τ - (L1 - ctTheta1 ε / c)) ∧
        (δ₀ < τ → 0.41 * δ₀ ^ 2 ≤ uctM τ - (L1 - ctTheta1 ε / c)) := by
      have h_lt_sm : τ ≤ δ₀ → 0.06 * τ ^ 2 ≤ uctM τ - (L1 - ctTheta1 ε / c) ∧
          0.20 * c ^ (-(1 / 2 : ℝ)) ≤ uctM τ - (L1 - ctTheta1 ε / c) := by
        intro hτδ
        have hm_eq := uctM_eq_sq_mul_mQ hτ_pos
        have hmQ := hmQ_lb τ hτ_pos.le hτδ
        have hm_lb : 0.81 * τ ^ 2 ≤ uctM τ := by
          rw [hm_eq]; linarith only [mul_le_mul_of_nonneg_left hmQ (sq_nonneg τ)]
        have hτ_sq : (1.85 : ℝ) ^ 2 * τ₁ ^ 2 < τ ^ 2 := by
          have := mul_self_lt_mul_self (by positivity : 0 ≤ 1.85 * τ₁) hτr
          linarith only [this]
        have hL_vs_τ : L1 - ctTheta1 ε / c ≤ 0.75 * τ ^ 2 := by
          have h1 : 2.55 * τ₁ ^ 2 ≤ 0.75 * τ ^ 2 := by nlinarith only [hτ_sq]
          linarith only [hL1_ub, h1]
        have h1 : 0.06 * τ ^ 2 ≤ uctM τ - (L1 - ctTheta1 ε / c) := by linarith only [hm_lb, hL_vs_τ]
        have h2 : 0.20 * c ^ (-(1 / 2 : ℝ)) ≤ 0.06 * τ ^ 2 := by rw [← hτ₁2]; nlinarith only [hτ_sq]
        exact ⟨h1, h2.trans h1⟩
      have h_gt_lg : δ₀ < τ → 0.41 * δ₀ ^ 2 ≤ uctM τ - (L1 - ctTheta1 ε / c) ∧
          0.20 * c ^ (-(1 / 2 : ℝ)) ≤ uctM τ - (L1 - ctTheta1 ε / c) := by
        intro hτδ
        have hm_mono : uctM δ₀ ≤ uctM τ :=
          hankelEdgeM_strictMonoOn.monotoneOn hδ₀_pos.le hτ_pos.le hτδ.le
        have hmδ_lb : 0.81 * δ₀ ^ 2 ≤ uctM δ₀ := by
          rw [uctM_eq_sq_mul_mQ hδ₀_pos]
          linarith only [mul_le_mul_of_nonneg_left (hmQ_lb δ₀ hδ₀_pos.le le_rfl) (sq_nonneg δ₀)]
        have hb_lg : (2.55 + 0.20) / (0.41 * δ₀ ^ 2) ≤ max 1 (max ((2.55 + 0.20) / (0.41 * δ₀ ^ 2)) (max (20 * Mθ) (20 * C_th_c 1))) :=
          (le_max_left _ _).trans (le_max_right _ _)
        have hτ₁_le_lg : τ₁ ≤ ((2.55 + 0.20) / (0.41 * δ₀ ^ 2))⁻¹ :=
          hτ₁_bd.trans (inv_anti₀ (by positivity) hb_lg)
        have hτ₁2_le : 2.75 * τ₁ ^ 2 ≤ 0.41 * δ₀ ^ 2 := by
          have h1 : (2.55 + 0.20) / (0.41 * δ₀ ^ 2) * τ₁ ≤ 1 := by
            calc (2.55 + 0.20) / (0.41 * δ₀ ^ 2) * τ₁
                ≤ (2.55 + 0.20) / (0.41 * δ₀ ^ 2) * ((2.55 + 0.20) / (0.41 * δ₀ ^ 2))⁻¹ :=
                  mul_le_mul_of_nonneg_left hτ₁_le_lg (by positivity)
              _ = 1 := mul_inv_cancel₀ (by positivity)
          have h2 : (2.55 + 0.20) * τ₁ ≤ 0.41 * δ₀ ^ 2 := by
            rwa [div_mul_eq_mul_div, div_le_one (by positivity)] at h1
          have hτ21 : τ₁ ^ 2 ≤ τ₁ := by nlinarith only [hτ₁.le, hτ₁_le1]
          nlinarith only [h2, hτ21]
        have hdiff1 : 0.41 * δ₀ ^ 2 ≤ uctM τ - (L1 - ctTheta1 ε / c) := by
          have : L1 - ctTheta1 ε / c < 0.40 * δ₀ ^ 2 := by
            linarith only [hL1_ub, hτ₁2_le, hδ₀_sq_pos]
          linarith only [hm_mono, hmδ_lb, this]
        have hdiff2 : 0.20 * c ^ (-(1 / 2 : ℝ)) ≤ 0.41 * δ₀ ^ 2 := by
          rw [← hτ₁2]; linarith only [hτ₁2_le, sq_nonneg τ₁]
        exact ⟨hdiff1, hdiff2.trans hdiff1⟩
      rcases le_or_gt τ δ₀ with hle | hgt
      · exact ⟨(h_lt_sm hle).2, fun _ => (h_lt_sm hle).1, fun h => absurd h hle.not_gt⟩
      · exact ⟨(h_gt_lg hgt).2, fun h => absurd h hgt.not_ge, fun _ => (h_gt_lg hgt).1⟩
    have hPhi'_glb : 0.10 * c ^ (-(1 / 2 : ℝ)) ≤ |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| := by
      have h1 := hmain_sub hdiff_lb.1
      linarith only [h1]
    have hPhi'_sm : τ ≤ δ₀ → 0.03 * τ ^ 2 ≤ |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| := fun hle => by
      have h1 := hmain_sub (hdiff_lb.2.1 hle)
      have h2 := hdiff_lb.1
      have h3 : 0.10 * c ^ (-(1 / 2 : ℝ)) ≤ 0.03 * τ ^ 2 := by
        rw [← hτ₁2]
        have hτ_sq : (1.85 : ℝ) ^ 2 * τ₁ ^ 2 < τ ^ 2 := by
          have := mul_self_lt_mul_self (by positivity : 0 ≤ 1.85 * τ₁) hτr
          linarith only [this]
        nlinarith only [hτ_sq]
      linarith only [h1, h3]
    have hPhi'_lg : δ₀ < τ → 0.20 * δ₀ ^ 2 ≤ |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| := fun hgt => by
      have h1 := hmain_sub (hdiff_lb.2.2 hgt)
      have hτ₁_le_lg : τ₁ ≤ ((2.55 + 0.20) / (0.41 * δ₀ ^ 2))⁻¹ :=
        hτ₁_bd.trans (inv_anti₀ (by positivity) ((le_max_left _ _).trans (le_max_right _ _)))
      have h1_mul : (2.55 + 0.20) * τ₁ ≤ 0.41 * δ₀ ^ 2 := by
        have hmul : (2.55 + 0.20) / (0.41 * δ₀ ^ 2) * τ₁ ≤ 1 :=
          (mul_le_mul_of_nonneg_left hτ₁_le_lg (by positivity)).trans (le_of_eq (mul_inv_cancel₀ (by positivity)))
        rwa [div_mul_eq_mul_div, div_le_one (by positivity)] at hmul
      have h2 : 0.10 * c ^ (-(1 / 2 : ℝ)) ≤ 0.21 * δ₀ ^ 2 := by
        rw [← hτ₁2]
        have hτ21 : τ₁ ^ 2 ≤ τ₁ := by nlinarith only [hτ₁.le, hτ₁_le1]
        nlinarith only [h1_mul, hτ21]
      linarith only [h1, h2]
    refine ⟨⟨hPhi'_glb, hPhi'_sm, hPhi'_lg⟩, fun k hk1 hkn => ?_⟩
    rw [concretePhiTilde_iteratedDeriv_succ_eq hK4 hc0 hτD hτ_pos hk1]
    have hw_nn : 0 ≤ edgeW τ ^ (-(k : ℤ)) := zpow_nonneg (edgeW_pos hτ_ne).le _
    have h1_w : 1 ≤ edgeW τ ^ (-(k : ℤ)) := one_le_edgeW_inv hτ_ne k
    have hPhi'_nn : 0 ≤ |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| := abs_nonneg _
    have tm : |iteratedDeriv k uctM τ| ≤
        (Cm_sm k / 0.03 + Cm_lg k / (0.20 * δ₀ ^ 2)) * edgeW τ ^ (-(k : ℤ)) *
          |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| := by
      rcases le_or_gt τ δ₀ with hle | hgt
      · have hm1 := hm_sm k hk1 τ ⟨hτ_pos, hle.trans hδ₀_le⟩
        have hsm := hPhi'_sm hle
        calc |iteratedDeriv k uctM τ|
            ≤ Cm_sm k * τ ^ 2 * edgeW τ ^ (-(k : ℤ)) := hm1
          _ = (Cm_sm k / 0.03) * edgeW τ ^ (-(k : ℤ)) * (0.03 * τ ^ 2) := by ring
          _ ≤ (Cm_sm k / 0.03) * edgeW τ ^ (-(k : ℤ)) * |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| :=
              mul_le_mul_of_nonneg_left hsm (mul_nonneg (div_nonneg (hCm_sm0 k) (by norm_num)) hw_nn)
          _ ≤ (Cm_sm k / 0.03 + Cm_lg k / (0.20 * δ₀ ^ 2)) * edgeW τ ^ (-(k : ℤ)) *
                |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| := by
              have hex : 0 ≤ Cm_lg k / (0.20 * δ₀ ^ 2) := div_nonneg (hCm_lg0 k) (by positivity)
              gcongr; linarith only [hex]
      · have hm1 := hm_lg k hk1 τ hτ_pos
        have hlg := hPhi'_lg hgt
        calc |iteratedDeriv k uctM τ|
            ≤ Cm_lg k * edgeW τ ^ (-(k : ℤ)) := hm1
          _ = (Cm_lg k / (0.20 * δ₀ ^ 2)) * edgeW τ ^ (-(k : ℤ)) * (0.20 * δ₀ ^ 2) := by field_simp [hδ₀_sq_pos.ne']
          _ ≤ (Cm_lg k / (0.20 * δ₀ ^ 2)) * edgeW τ ^ (-(k : ℤ)) * |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| :=
              mul_le_mul_of_nonneg_left hlg (mul_nonneg (div_nonneg (hCm_lg0 k) (by positivity)) hw_nn)
          _ ≤ (Cm_sm k / 0.03 + Cm_lg k / (0.20 * δ₀ ^ 2)) * edgeW τ ^ (-(k : ℤ)) *
                |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| := by
              have hex : 0 ≤ Cm_sm k / 0.03 := div_nonneg (hCm_sm0 k) (by norm_num)
              gcongr; linarith only [hex]
    have tθ : c⁻¹ * |iteratedDeriv (k + 1) (outerTheta ε) τ| ≤
        (10 * Cθk (k + 1)) * edgeW τ ^ (-(k : ℤ)) * |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| := by
      have hb := hθk_bd (k + 1) (by omega) (by omega) ε hε τ
      have hc_le : c⁻¹ ≤ c ^ (-(1 / 2 : ℝ)) := by
        rw [hcinv, ← hτ₁2, show τ₁ ^ 4 = τ₁ ^ 2 * τ₁ ^ 2 by ring]
        exact mul_le_of_le_one_left (sq_nonneg τ₁) (pow_le_one₀ hτ₁.le hτ₁_le1)
      calc c⁻¹ * |iteratedDeriv (k + 1) (outerTheta ε) τ|
          ≤ c ^ (-(1 / 2 : ℝ)) * Cθk (k + 1) := mul_le_mul hc_le hb (abs_nonneg _) (Real.rpow_nonneg hc0.le _)
        _ = (10 * Cθk (k + 1)) * 1 * (0.10 * c ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ (10 * Cθk (k + 1)) * edgeW τ ^ (-(k : ℤ)) * |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1_w (mul_nonneg (by norm_num) (hCθk0 _))) hPhi'_glb
              (by positivity) (mul_nonneg (mul_nonneg (by norm_num) (hCθk0 _)) hw_nn)
    have tv : c⁻¹ * |iteratedDeriv (k + 1) (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤
        (10 * C_th_c (k + 1)) * edgeW τ ^ (-(k : ℤ)) * |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| := by
      have hv := hpt.2.2.2 (k + 1) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at hv
      have hτ₁_C : τ₁ * C_th_c (k + 1) ≤ C_th_c (k + 1) := mul_le_of_le_one_left (hCthc0 _) hτ₁_le1
      calc c⁻¹ * |iteratedDeriv (k + 1) (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ|
          ≤ C_th_c (k + 1) * τ₁ * c ^ (-(1 / 2 : ℝ)) * edgeW τ ^ (-(k : ℤ)) := hv
        _ = (10 * (τ₁ * C_th_c (k + 1))) * edgeW τ ^ (-(k : ℤ)) * (0.10 * c ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ (10 * C_th_c (k + 1)) * edgeW τ ^ (-(k : ℤ)) * |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| :=
            mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ₁_C (by norm_num)) hw_nn) hPhi'_glb
              (by positivity) (mul_nonneg (mul_nonneg (by norm_num) (hCthc0 _)) hw_nn)
    have a1 := abs_add_le (-iteratedDeriv k uctM τ - c⁻¹ * iteratedDeriv (k + 1) (outerTheta ε) τ)
      (c⁻¹ * iteratedDeriv (k + 1) (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ)
    have a2 := abs_sub (-iteratedDeriv k uctM τ) (c⁻¹ * iteratedDeriv (k + 1) (outerTheta ε) τ)
    rw [abs_neg] at a2
    rw [abs_mul, abs_of_pos (inv_pos.mpr hc0)] at a1 a2
    have hsum_eq : (Cm_sm k / 0.03 + Cm_lg k / (0.20 * δ₀ ^ 2)) * edgeW τ ^ (-(k : ℤ)) *
          |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| +
        (10 * Cθk (k + 1)) * edgeW τ ^ (-(k : ℤ)) * |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| +
        (10 * C_th_c (k + 1)) * edgeW τ ^ (-(k : ℤ)) * |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| =
        K_fun k * edgeW τ ^ (-(k : ℤ)) * |deriv (fun t : ℝ => concretePhiTilde K4 ε c t (L1, α)) τ| := by
      dsimp only [K_fun]; ring
    linarith only [a1, a2, tm, tθ, tv, hsum_eq]
  -- Transfer from `τ > r` to `{τ : ℝ | r < |τ|}` by evenness
  have hPhi_cd : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (outerPhi K4 ε c L1 α) {τ : ℝ | 1.85 * τ₁ < |τ|} := by
    intro τ hτ
    rcases lt_or_gt_of_ne (abs_pos.mp (lt_of_le_of_lt (mul_nonneg (by norm_num) hτ₁.le) hτ)) with hneg | hpos
    · have hev : outerPhi K4 ε c L1 α =ᶠ[𝓝 τ] fun s => concretePhiTilde K4 ε c (-s) (L1, α) := by
        filter_upwards [isOpen_Iio.mem_nhds hneg] with s hs
        exact ite_eq_right_iff.mpr fun h => absurd (mem_Iio.mp hs) (not_lt_of_ge h)
      have hcd_neg : ContDiffAt ℝ ∞ (fun s => concretePhiTilde K4 ε c (-s) (L1, α)) τ :=
        (hcd_pos.contDiffAt (isOpen_Ioi.mem_nhds (neg_pos.mpr hneg))).comp τ contDiff_neg.contDiffAt
      exact ((hcd_neg.of_le (WithTop.coe_le_coe.mpr le_top)).congr_of_eventuallyEq hev).contDiffWithinAt
    · have hev : outerPhi K4 ε c L1 α =ᶠ[𝓝 τ] fun s => concretePhiTilde K4 ε c s (L1, α) := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with s hs
        exact ite_eq_left_iff.mpr fun h => absurd (mem_Ioi.mp hs).le h
      exact (((hcd_pos.contDiffAt (isOpen_Ioi.mem_nhds hpos)).of_le
        (WithTop.coe_le_coe.mpr le_top)).congr_of_eventuallyEq hev).contDiffWithinAt
  have h_deriv_abs : ∀ m : ℕ, ∀ τ : ℝ, 1.85 * τ₁ < |τ| →
      |iteratedDeriv m (outerPhi K4 ε c L1 α) τ| =
        abs (iteratedDeriv m (fun s : ℝ => concretePhiTilde K4 ε c s (L1, α)) |τ|) := by
    intro m τ hτ
    rcases lt_or_gt_of_ne (abs_pos.mp (lt_of_le_of_lt (mul_nonneg (by norm_num) hτ₁.le) hτ)) with hneg | hpos
    · have hev : outerPhi K4 ε c L1 α =ᶠ[𝓝 τ] fun s => concretePhiTilde K4 ε c (-s) (L1, α) := by
        filter_upwards [isOpen_Iio.mem_nhds hneg] with s hs
        exact ite_eq_right_iff.mpr fun h => absurd (mem_Iio.mp hs) (not_lt_of_ge h)
      rw [hev.iteratedDeriv_eq m,
        iteratedDeriv_comp_neg_eq (fun s => concretePhiTilde K4 ε c s (L1, α)) m τ,
        abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_neg hneg]
    · have hev : outerPhi K4 ε c L1 α =ᶠ[𝓝 τ] fun s => concretePhiTilde K4 ε c s (L1, α) := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with s hs
        exact ite_eq_left_iff.mpr fun h => absurd (mem_Ioi.mp hs).le h
      rw [hev.iteratedDeriv_eq m, abs_of_pos hpos]
  refine ⟨hPhi_cd, fun τ hτ => ?_, fun k hk1 hkn τ hτ => ?_⟩
  · have h1 := h_deriv_abs 1 τ hτ
    rw [iteratedDeriv_one, iteratedDeriv_one] at h1
    rw [h1]
    exact (h_all_pos |τ| hτ).1.1
  · have h1 := h_deriv_abs 1 τ hτ
    rw [iteratedDeriv_one, iteratedDeriv_one] at h1
    have hw_abs : edgeW |τ| = edgeW τ := by
      rcases le_or_gt 0 τ with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, edgeW_neg]
    rw [h_deriv_abs (k + 1) τ hτ, h1, ← hw_abs]
    exact (h_all_pos |τ| hτ).2 k hk1 hkn

/-- info: 'FormalResearch.SignUncertainty.outerPhi_shoulder_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerPhi_shoulder_bounds

end FormalResearch.SignUncertainty
