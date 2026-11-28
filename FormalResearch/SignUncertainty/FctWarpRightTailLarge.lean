/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpRightTailIbp

/-!
# Right-tail splitting error on `Sw * c^{-2/3} ≤ L` (`fct:main-hankel`)

Paper I, `constant_terms_five.tex` lines 1566–1575: combines the 1-step IBP splitting
`warpRightTail_first_ibp` and `warpRightTail_term2_bounds` from `FctWarpRightTailIbp.lean` with
van der Corput / weighted IBP bounds on `warpRightTailTerm1` to prove
`warpRightTailDensity_large_bound`:
* on `Sw * c^{-2/3} ≤ L ≤ 1`, `|warpRightTailDensity h ε c ξ| ≤ C * c^{-2} * L^{-1}`;
* on `1 ≤ L`, `|warpRightTailDensity h ε c ξ| ≤ C * c^{-2} * L^{-(3/2)}`;
* on `1 / 4 * Real.log c ≤ L`, `|warpRightTailDensity h ε c ξ| ≤ C * c^{-(5/2)} * L^{-2}`.

Class: proved (depending only on `K4 ≥ 1`). Kernel-dependence guard at the end.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real ContDiff
open FormalResearch.Analysis FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctCuspEdge

namespace FormalResearch.SignUncertainty

private lemma norm_sum3_le (a b c : ℂ) : ‖a + (b + c)‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
  ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))).trans_eq (add_assoc _ _ _).symm

private lemma norm_sum4_le (a b c d : ℂ) :
    ‖a + (b + (c + d))‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
  ((norm_add_le _ _).trans (add_le_add le_rfl (norm_sum3_le b c d))).trans_eq (by ring)

/-- `vdc1` on `(0, b]` by taking `δ → 0+` in `vdc1_Icc_edgePhi_sign` (`σ = 1`). -/
private lemma vdc1_Ioc_edgePhi {b L c lam M_bd V_bd : ℝ} (hb : 0 < b) (hc : 0 < c) (hlam : 0 < lam)
    {amp : ℝ → ℂ} (hCD : ContDiffOn ℝ 1 amp (Ioi 0))
    (hInt : IntegrableOn (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) (Ioc 0 b))
    (hLam : ∀ x ∈ Ioc 0 b, lam ≤ |edgePhiDeriv L x|)
    (hM : ∀ x ∈ Ioc 0 b, ‖amp x‖ ≤ M_bd)
    (hV : ∀ a : ℝ, 0 < a → a ≤ b → ∫ x in Icc a b, ‖deriv amp x‖ ≤ V_bd) :
    ‖∫ τ in Ioc 0 b, amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
      3 * (M_bd + V_bd) / (c * lam) := by
  let f : ℝ → ℂ := fun τ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))
  have htend : Tendsto (fun δ : ℝ => ∫ τ in δ..b, f τ) (𝓝[>] 0) (𝓝 (∫ τ in Ioc 0 b, f τ)) := by
    have hlim := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioc (0 : ℝ) b)) (l := 𝓝[>] (0 : ℝ))
      (F := fun (δ : ℝ) (τ : ℝ) => (Ioc δ b).indicator f τ) (f := f)
      (bound := fun τ => ‖f τ‖) ?_ ?_ hInt.norm ?_
    · refine hlim.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT hb] with δ hδ
      rw [intervalIntegral.integral_of_le hδ.2, MeasureTheory.setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_self_of_subset_right (Ioc_subset_Ioc_left hδ.1.le)]
    · filter_upwards [Ioc_mem_nhdsGT hb] with δ _
      exact hInt.aestronglyMeasurable.indicator measurableSet_Ioc
    · filter_upwards [Ioc_mem_nhdsGT hb] with δ _
      exact ae_of_all _ fun τ => by
        by_cases hτ : τ ∈ Ioc δ b
        · simp [Set.indicator_of_mem hτ]
        · simp [Set.indicator_of_notMem hτ]
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun τ (hτ : τ ∈ Ioc 0 b) => ?_
      have hev : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), τ ∈ Ioc δ b := by
        filter_upwards [Ioo_mem_nhdsGT hτ.1] with δ hδ
        exact ⟨hδ.2, hτ.2⟩
      exact tendsto_const_nhds.congr' (hev.mono fun δ hδ => (Set.indicator_of_mem hδ f).symm)
  refine le_of_tendsto htend.norm ?_
  filter_upwards [Ioc_mem_nhdsGT hb] with δ hδ
  have hv := vdc1_Icc_edgePhi_sign (L := L) (σ := 1) hδ.2 hδ.1 hc hlam (Or.inl rfl) hCD
    (fun x hx => hLam x ⟨lt_of_lt_of_le hδ.1 hx.1, hx.2⟩)
    (fun x hx => hM x ⟨lt_of_lt_of_le hδ.1 hx.1, hx.2⟩) (hV δ hδ.1 hδ.2)
  simpa only [one_mul] using hv

/-- `vdc1` on `(a, ∞)` (`σ = 1`). -/
private lemma vdc1_Ioi_edgePhi_pos {a L c lam M_bd V_bd : ℝ} (ha : 0 < a) (hc : 0 < c) (hlam : 0 < lam)
    {amp : ℝ → ℂ} (hCD : ContDiffOn ℝ 1 amp (Ioi 0))
    (hInt : IntegrableOn (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) (Ioi a))
    (hLam : ∀ x ∈ Ici a, lam ≤ |edgePhiDeriv L x|)
    (hM : ∀ x ∈ Ici a, ‖amp x‖ ≤ M_bd)
    (hV : ∀ T : ℝ, a ≤ T → ∫ x in Icc a T, ‖deriv amp x‖ ≤ V_bd) :
    ‖∫ τ in Ioi a, amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
      3 * (M_bd + V_bd) / (c * lam) := by
  have htend := intervalIntegral_tendsto_integral_Ioi a hInt tendsto_id
  refine le_of_tendsto htend.norm ?_
  filter_upwards [eventually_ge_atTop a] with T hT
  have hv := vdc1_Icc_edgePhi_sign (L := L) (σ := 1) hT ha hc hlam (Or.inl rfl) hCD
    (fun x hx => hLam x hx.1) (fun x hx => hM x hx.1) (hV T hT)
  simpa only [one_mul, id_eq] using hv

/-- Global `O(c⁻¹)` and exponentially weighted `O(c⁻¹ e^{-(π/2) a})` bounds on `warpAmpRight` and
`∫ ‖deriv warpAmpRight‖`. -/
private lemma integrableOn_rpow_poly13_exp_rate {a : ℝ} (ha : 0 < a) :
    ∃ I : ℝ, 0 ≤ I ∧
      IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(a * τ))) (Ioi 0) ∧
      ∫ τ in Ioi (0 : ℝ), τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(a * τ)) ≤ I := by
  have h_ae : AEStronglyMeasurable (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(a * τ)))
      (volume.restrict (Ioi 0)) :=
    (ContinuousOn.aestronglyMeasurable
      (((ContinuousOn.rpow_const continuousOn_id fun τ (hτ : 0 < τ) => Or.inl hτ.ne').mul
        ((continuous_const.add continuous_id).pow 13).continuousOn).mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_id : Continuous (fun τ : ℝ => τ))).neg).continuousOn)
      measurableSet_Ioi)
  have hint : IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(a * τ))) (Ioi 0) := by
    have hi1 : IntegrableOn (fun τ : ℝ => (2 : ℝ) ^ 13 * τ ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ))).const_mul _)
    have h1 : IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(a * τ))) (Ioc 0 1) := by
      refine hi1.mono' (h_ae.mono_set Ioc_subset_Ioi_self) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun τ (hτ : τ ∈ Ioc 0 1) => ?_
      have h1τ : (1 + τ) ^ 13 ≤ (2 : ℝ) ^ 13 := pow_le_pow_left₀ (by linarith only [hτ.1]) (by linarith only [hτ.2]) 13
      have hexp : Real.exp (-(a * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [ha, hτ.1])
      have hτn : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ.1.le _
      have h13n : 0 ≤ (1 + τ) ^ 13 := pow_nonneg (by linarith only [hτ.1]) 13
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hτn h13n) (Real.exp_pos _).le)]
      calc τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(a * τ))
          ≤ τ ^ (-(1 / 2 : ℝ)) * 2 ^ 13 * 1 := by gcongr
        _ = (2 : ℝ) ^ 13 * τ ^ (-(1 / 2 : ℝ)) := by ring
    have h2 : IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(a * τ))) (Ioi 1) := by
      have hi_e : IntegrableOn (fun τ : ℝ => (Nat.factorial 15 : ℝ) / (a / 2) ^ 15 * Real.exp (a / 2) *
          Real.exp (-(a / 2 * τ))) (Ioi 1) := by
        have hexp := integrableOn_exp_mul_Ioi (a := -(a / 2)) (by linarith) 1
        exact (hexp.congr_fun (fun τ _ => by show Real.exp (-(a / 2) * τ) = Real.exp (-(a / 2 * τ)); ring)
          measurableSet_Ioi).const_mul _
      refine hi_e.mono' (h_ae.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ (hτ : 1 < τ) => ?_
      have hpow := Real.pow_div_factorial_le_exp (a / 2 * (1 + τ)) (by positivity) 15
      have h15 : (1 + τ) ^ 13 ≤ (1 + τ) ^ 15 := pow_le_pow_right₀ (by linarith only [hτ]) (by norm_num)
      have h15' : (1 + τ) ^ 15 ≤ (Nat.factorial 15 : ℝ) / (a / 2) ^ 15 * Real.exp (a / 2 * (1 + τ)) := by
        have hmul : (a / 2 * (1 + τ)) ^ 15 / (Nat.factorial 15 : ℝ) =
            ((a / 2) ^ 15 / (Nat.factorial 15 : ℝ)) * (1 + τ) ^ 15 := by rw [mul_pow]; ring
        rw [hmul] at hpow
        calc (1 + τ) ^ 15 = ((a / 2) ^ 15 / (Nat.factorial 15 : ℝ))⁻¹ *
              (((a / 2) ^ 15 / (Nat.factorial 15 : ℝ)) * (1 + τ) ^ 15) := by field_simp [ha.ne']
          _ ≤ ((a / 2) ^ 15 / (Nat.factorial 15 : ℝ))⁻¹ * Real.exp (a / 2 * (1 + τ)) := by gcongr
          _ = (Nat.factorial 15 : ℝ) / (a / 2) ^ 15 * Real.exp (a / 2 * (1 + τ)) := by field_simp
      have htp : τ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ.le (by norm_num)
      have hexp0 : 0 ≤ Real.exp (-(a * τ)) := (Real.exp_pos _).le
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (by positivity)) hexp0)]
      calc τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(a * τ))
          ≤ 1 * (1 + τ) ^ 15 * Real.exp (-(a * τ)) := by gcongr
        _ ≤ ((Nat.factorial 15 : ℝ) / (a / 2) ^ 15 * Real.exp (a / 2 * (1 + τ))) * Real.exp (-(a * τ)) := by
            rw [one_mul]; gcongr
        _ = (Nat.factorial 15 : ℝ) / (a / 2) ^ 15 * Real.exp (a / 2) * Real.exp (-(a / 2 * τ)) := by
            rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact h1.union h2
  exact ⟨_, setIntegral_nonneg measurableSet_Ioi fun τ (hτ : 0 < τ) =>
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hτ.le _) (by positivity)) (Real.exp_pos _).le, hint, le_rfl⟩

/-- Global `O(c⁻¹)` and exponentially weighted `O(c⁻¹ e^{-(π/2) a})` bounds on `warpAmpRight` and
`∫ ‖deriv warpAmpRight‖`. -/
private lemma warpAmpRight_mv_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ M0 M_pt M1 c₀ : ℝ, 0 ≤ M0 ∧ 0 ≤ M_pt ∧ 0 ≤ M1 ∧ 32 ^ 4 ≤ c₀ ∧
      ∀ {ε c ξ : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
        let amp := warpAmpRight K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (fctRightTail h ε c)
        ContDiffOn ℝ 1 amp (Ioi 0) ∧
        IntegrableOn (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Real.log (π ^ 2 * ξ)) τ : ℂ))) (Ioi 0) ∧
        (∀ {τ : ℝ}, 0 < τ → ‖amp τ‖ ≤ M_pt * c⁻¹ * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) ∧
        (∀ {τ : ℝ}, 0 < τ → ‖deriv amp τ‖ ≤ M_pt * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) ∧
        (∀ {τ : ℝ}, 0 < τ → ‖amp τ‖ ≤ M0 * c⁻¹) ∧
        (∀ {a b : ℝ}, 0 < a → a ≤ b → ∫ x in Icc a b, ‖deriv amp x‖ ≤ M0 * c⁻¹) ∧
        (∀ {a : ℝ}, 1 / 16 ≤ a →
          (∀ {τ : ℝ}, a ≤ τ → ‖amp τ‖ ≤ M1 * c⁻¹ * Real.exp (-(π / 2 * a))) ∧
          (∀ {T : ℝ}, a ≤ T → ∫ x in Icc a T, ‖deriv amp x‖ ≤ M1 * c⁻¹ * Real.exp (-(π / 2 * a)))) := by
  obtain ⟨CWR, c0WR, hCWR0, hc0WR, hWR⟩ := warpAmpRight_bounds hK4 h
  obtain ⟨I_m12, hIm12_0, hm12_int, hm12_le⟩ := integrableOn_rpow_poly13_exp_rate Real.pi_pos
  obtain ⟨Ih, hIh0, hIh_int, hIh_le⟩ := integrableOn_rpow_poly13_exp_rate (by positivity : 0 < π / 2)
  have h12_pt : ∃ Mp : ℝ, 0 ≤ Mp ∧ ∀ τ : ℝ, 0 ≤ τ → τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) ≤ Mp := by
    refine ⟨(Nat.factorial 14 : ℝ) / π ^ 14 * Real.exp π, by positivity, fun τ hτ => ?_⟩
    have hτ14 : τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 ≤ (1 + τ) ^ 14 := by
      have h12 : τ ^ (1 / 2 : ℝ) ≤ 1 + τ := by
        by_cases h1 : τ ≤ 1
        · exact (Real.rpow_le_one hτ h1 (by norm_num)).trans (by linarith)
        · have h1' : 1 ≤ τ := (not_le.mp h1).le
          exact (Real.rpow_le_rpow_of_exponent_le h1' (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans (by rw [Real.rpow_one]; linarith)
      calc τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 ≤ (1 + τ) * (1 + τ) ^ 13 := by gcongr
        _ = (1 + τ) ^ 14 := by ring
    have hpow := Real.pow_div_factorial_le_exp (π * (1 + τ)) (by positivity) 14
    have h14 : (1 + τ) ^ 14 ≤ (Nat.factorial 14 : ℝ) / π ^ 14 * Real.exp (π * (1 + τ)) := by
      have hmul : (π * (1 + τ)) ^ 14 / (Nat.factorial 14 : ℝ) = (π ^ 14 / (Nat.factorial 14 : ℝ)) * (1 + τ) ^ 14 := by
        rw [mul_pow]; ring
      rw [hmul] at hpow
      calc (1 + τ) ^ 14 = (π ^ 14 / (Nat.factorial 14 : ℝ))⁻¹ * ((π ^ 14 / (Nat.factorial 14 : ℝ)) * (1 + τ) ^ 14) := by
            field_simp [Real.pi_ne_zero]
        _ ≤ (π ^ 14 / (Nat.factorial 14 : ℝ))⁻¹ * Real.exp (π * (1 + τ)) := by gcongr
        _ = (Nat.factorial 14 : ℝ) / π ^ 14 * Real.exp (π * (1 + τ)) := by field_simp
    calc τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ))
        ≤ (1 + τ) ^ 14 * Real.exp (-(π * τ)) := by gcongr
      _ ≤ ((Nat.factorial 14 : ℝ) / π ^ 14 * Real.exp (π * (1 + τ))) * Real.exp (-(π * τ)) := by gcongr
      _ = (Nat.factorial 14 : ℝ) / π ^ 14 * (Real.exp (π * (1 + τ)) * Real.exp (-(π * τ))) := by ring
      _ = (Nat.factorial 14 : ℝ) / π ^ 14 * Real.exp π := by rw [← Real.exp_add]; congr 2; ring
  have h12_half_pt : ∃ Mp2 : ℝ, 0 ≤ Mp2 ∧ ∀ τ : ℝ, 0 ≤ τ →
      τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π / 2 * τ)) ≤ Mp2 := by
    refine ⟨(Nat.factorial 14 : ℝ) / (π / 2) ^ 14 * Real.exp (π / 2), by positivity, fun τ hτ => ?_⟩
    have hτ14 : τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 ≤ (1 + τ) ^ 14 := by
      have h12 : τ ^ (1 / 2 : ℝ) ≤ 1 + τ := by
        by_cases h1 : τ ≤ 1
        · exact (Real.rpow_le_one hτ h1 (by norm_num)).trans (by linarith)
        · have h1' : 1 ≤ τ := (not_le.mp h1).le
          exact (Real.rpow_le_rpow_of_exponent_le h1' (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans (by rw [Real.rpow_one]; linarith)
      calc τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 ≤ (1 + τ) * (1 + τ) ^ 13 := by gcongr
        _ = (1 + τ) ^ 14 := by ring
    have hpow := Real.pow_div_factorial_le_exp (π / 2 * (1 + τ)) (by positivity) 14
    have h14 : (1 + τ) ^ 14 ≤ (Nat.factorial 14 : ℝ) / (π / 2) ^ 14 * Real.exp (π / 2 * (1 + τ)) := by
      have hmul : (π / 2 * (1 + τ)) ^ 14 / (Nat.factorial 14 : ℝ) =
          ((π / 2) ^ 14 / (Nat.factorial 14 : ℝ)) * (1 + τ) ^ 14 := by rw [mul_pow]; ring
      rw [hmul] at hpow
      calc (1 + τ) ^ 14 = ((π / 2) ^ 14 / (Nat.factorial 14 : ℝ))⁻¹ * (((π / 2) ^ 14 / (Nat.factorial 14 : ℝ)) * (1 + τ) ^ 14) := by
            field_simp [Real.pi_ne_zero]
        _ ≤ ((π / 2) ^ 14 / (Nat.factorial 14 : ℝ))⁻¹ * Real.exp (π / 2 * (1 + τ)) := by gcongr
        _ = (Nat.factorial 14 : ℝ) / (π / 2) ^ 14 * Real.exp (π / 2 * (1 + τ)) := by field_simp
    calc τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π / 2 * τ))
        ≤ (1 + τ) ^ 14 * Real.exp (-(π / 2 * τ)) := by gcongr
      _ ≤ ((Nat.factorial 14 : ℝ) / (π / 2) ^ 14 * Real.exp (π / 2 * (1 + τ))) * Real.exp (-(π / 2 * τ)) := by gcongr
      _ = (Nat.factorial 14 : ℝ) / (π / 2) ^ 14 * (Real.exp (π / 2 * (1 + τ)) * Real.exp (-(π / 2 * τ))) := by ring
      _ = (Nat.factorial 14 : ℝ) / (π / 2) ^ 14 * Real.exp (π / 2) := by rw [← Real.exp_add]; congr 2; ring
  obtain ⟨Mp, hMp0, hMp⟩ := h12_pt
  obtain ⟨Mp2, hMp2_0, hMp2⟩ := h12_half_pt
  set M0 : ℝ := CWR * max (max Mp Mp2) (max I_m12 Ih)
  refine ⟨M0, CWR, M0, c0WR, by positivity, hCWR0, by positivity, hc0WR, fun {ε c ξ} hε hc hξ => ?_⟩
  obtain ⟨hcd, hbd⟩ := hWR hε hc
  have hcpos : 0 < c := by linarith [hc0WR.trans hc]
  have hc_inv0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hcpos.le
  set amp := warpAmpRight K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (fctRightTail h ε c)
  have hMp_le : CWR * Mp ≤ M0 := by dsimp only [M0]; gcongr; exact (le_max_left _ _).trans (le_max_left _ _)
  have hMp2_le : CWR * Mp2 ≤ M0 := by dsimp only [M0]; gcongr; exact (le_max_right _ _).trans (le_max_left _ _)
  have hIm_le : CWR * I_m12 ≤ M0 := by dsimp only [M0]; gcongr; exact (le_max_left _ _).trans (le_max_right _ _)
  have hIh_le' : CWR * Ih ≤ M0 := by dsimp only [M0]; gcongr; exact (le_max_right _ _).trans (le_max_right _ _)
  have hM_glob : ∀ {τ : ℝ}, 0 < τ → ‖amp τ‖ ≤ M0 * c⁻¹ := fun {τ} hτ => by
    calc ‖amp τ‖ ≤ CWR * c⁻¹ * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := (hbd hτ).1
      _ = (CWR * c⁻¹) * (τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by ring
      _ ≤ (CWR * c⁻¹) * Mp := by gcongr; exact hMp τ hτ.le
      _ = (CWR * Mp) * c⁻¹ := by ring
      _ ≤ M0 * c⁻¹ := mul_le_mul_of_nonneg_right hMp_le hc_inv0
  have h_deriv_cd : ContinuousOn (fun τ => ‖deriv amp τ‖) (Ioi 0) :=
    ((hcd.derivWithin isOpen_Ioi.uniqueDiffOn (m := 0) (by norm_num)).continuousOn.congr
      (fun t ht => (derivWithin_of_isOpen isOpen_Ioi ht).symm)).norm
  have hV_glob : ∀ {a b : ℝ}, 0 < a → a ≤ b → ∫ x in Icc a b, ‖deriv amp x‖ ≤ M0 * c⁻¹ := by
    intro a b ha hab
    have hint_ab : IntegrableOn (fun x => ‖deriv amp x‖) (Icc a b) :=
      (h_deriv_cd.mono fun (x : ℝ) (hx : x ∈ Icc a b) => lt_of_lt_of_le ha hx.1).integrableOn_Icc
    have hint_dom : IntegrableOn (fun τ : ℝ => (CWR * c⁻¹) * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)))) (Icc a b) :=
      IntegrableOn.mono_set (hm12_int.const_mul (CWR * c⁻¹))
        (fun (x : ℝ) (hx : x ∈ Icc a b) => show x ∈ Ioi 0 from lt_of_lt_of_le ha hx.1)
    calc ∫ x in Icc a b, ‖deriv amp x‖
        ≤ ∫ τ in Icc a b, (CWR * c⁻¹) * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by
          refine setIntegral_mono_on hint_ab hint_dom measurableSet_Icc fun τ hτ => ?_
          calc ‖deriv amp τ‖ ≤ CWR * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) :=
                (hbd (lt_of_lt_of_le ha hτ.1)).2
            _ = _ := by ring
      _ ≤ ∫ τ in Ioi (0 : ℝ), (CWR * c⁻¹) * (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by
          refine setIntegral_mono_set (hm12_int.const_mul (CWR * c⁻¹))
            (ae_restrict_of_forall_mem measurableSet_Ioi fun τ (hτ : 0 < τ) =>
              mul_nonneg (mul_nonneg hCWR0 hc_inv0)
                (mul_nonneg (mul_nonneg (Real.rpow_nonneg hτ.le _) (by positivity)) (Real.exp_pos _).le))
            (Eventually.of_forall fun τ hτ => lt_of_lt_of_le ha hτ.1)
      _ = (CWR * c⁻¹) * ∫ τ in Ioi (0 : ℝ), τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (CWR * c⁻¹) * I_m12 := by gcongr
      _ = (CWR * I_m12) * c⁻¹ := by ring
      _ ≤ M0 * c⁻¹ := mul_le_mul_of_nonneg_right hIm_le hc_inv0
  have hInt_f : IntegrableOn (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Real.log (π ^ 2 * ξ)) τ : ℂ))) (Ioi 0) := by
    set L := Real.log (π ^ 2 * ξ)
    have hae : AEStronglyMeasurable (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)))
        (volume.restrict (Ioi 0)) := by
      have hexp_c : Continuous (fun τ : ℝ => Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) :=
        Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (contDiff_edgePhi L).continuous))
      exact (hcd.continuousOn.mul hexp_c.continuousOn).aestronglyMeasurable measurableSet_Ioi
    have hdom : IntegrableOn (fun τ : ℝ => (CWR * c⁻¹ * Mp2) * Real.exp (-(π / 2 * τ))) (Ioi 0) := by
      have hexp := integrableOn_exp_mul_Ioi (a := -(π / 2)) (by linarith [Real.pi_pos]) 0
      exact (hexp.congr_fun (fun τ _ => by show Real.exp (-(π / 2) * τ) = Real.exp (-(π / 2 * τ)); ring)
        measurableSet_Ioi).const_mul _
    refine hdom.mono' hae ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ (hτ : 0 < τ) => ?_
    rw [norm_mul, Complex.norm_exp]
    have hre : (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)).re = 0 := by
      rw [mul_assoc, Complex.I_mul_re, ← Complex.ofReal_mul, Complex.ofReal_im]; norm_num
    rw [hre, Real.exp_zero, mul_one]
    have hexp_s : Real.exp (-(π * τ)) = Real.exp (-(π / 2 * τ)) * Real.exp (-(π / 2 * τ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp0 : 0 ≤ Real.exp (-(π / 2 * τ)) := (Real.exp_pos _).le
    calc ‖amp τ‖ ≤ CWR * c⁻¹ * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := (hbd hτ).1
      _ = (CWR * c⁻¹) * (τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π / 2 * τ))) * Real.exp (-(π / 2 * τ)) := by
          rw [hexp_s]; ring
      _ ≤ (CWR * c⁻¹) * Mp2 * Real.exp (-(π / 2 * τ)) := by gcongr; exact hMp2 τ hτ.le
      _ = (CWR * c⁻¹ * Mp2) * Real.exp (-(π / 2 * τ)) := by ring
  refine ⟨hcd, hInt_f, fun {τ} hτ => (hbd hτ).1, fun {τ} hτ => (hbd hτ).2, @hM_glob, @hV_glob, fun {a} ha => ⟨?_, ?_⟩⟩
  · have ha_pos : 0 < a := by linarith
    intro τ hτ
    have hτpos : 0 < τ := lt_of_lt_of_le ha_pos hτ
    have hexp_s : Real.exp (-(π * τ)) = Real.exp (-(π / 2 * τ)) * Real.exp (-(π / 2 * τ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp_a : Real.exp (-(π / 2 * τ)) ≤ Real.exp (-(π / 2 * a)) :=
      Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ])
    have hexp0 : 0 ≤ Real.exp (-(π / 2 * τ)) := (Real.exp_pos _).le
    calc ‖amp τ‖ ≤ CWR * c⁻¹ * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := (hbd hτpos).1
      _ = (CWR * c⁻¹) * (τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π / 2 * τ))) * Real.exp (-(π / 2 * τ)) := by
          rw [hexp_s]; ring
      _ ≤ (CWR * c⁻¹) * Mp2 * Real.exp (-(π / 2 * a)) := by gcongr; exact hMp2 τ hτpos.le
      _ = (CWR * Mp2) * c⁻¹ * Real.exp (-(π / 2 * a)) := by ring
      _ ≤ M0 * c⁻¹ * Real.exp (-(π / 2 * a)) := by gcongr
  · have ha_pos : 0 < a := by linarith
    intro T haT
    have hint_ab : IntegrableOn (fun x => ‖deriv amp x‖) (Icc a T) :=
      (h_deriv_cd.mono fun (x : ℝ) (hx : x ∈ Icc a T) => lt_of_lt_of_le ha_pos hx.1).integrableOn_Icc
    have hint_dom : IntegrableOn (fun τ : ℝ => (CWR * c⁻¹ * Real.exp (-(π / 2 * a))) *
        (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π / 2 * τ)))) (Icc a T) :=
      IntegrableOn.mono_set (hIh_int.const_mul _)
        (fun (x : ℝ) (hx : x ∈ Icc a T) => show x ∈ Ioi 0 from lt_of_lt_of_le ha_pos hx.1)
    calc ∫ x in Icc a T, ‖deriv amp x‖
        ≤ ∫ τ in Icc a T, (CWR * c⁻¹ * Real.exp (-(π / 2 * a))) *
            (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π / 2 * τ))) := by
          refine setIntegral_mono_on hint_ab hint_dom measurableSet_Icc fun τ hτ => ?_
          have hτpos : 0 < τ := lt_of_lt_of_le ha_pos hτ.1
          have hexp_s : Real.exp (-(π * τ)) = Real.exp (-(π / 2 * τ)) * Real.exp (-(π / 2 * τ)) := by
            rw [← Real.exp_add]; congr 1; ring
          have hexp_a : Real.exp (-(π / 2 * τ)) ≤ Real.exp (-(π / 2 * a)) :=
            Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hτ.1])
          have h1 : 0 ≤ CWR * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 :=
            mul_nonneg (mul_nonneg (mul_nonneg hCWR0 hc_inv0) (Real.rpow_nonneg hτpos.le _)) (by positivity)
          calc ‖deriv amp τ‖ ≤ CWR * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := (hbd hτpos).2
            _ = (CWR * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π / 2 * τ))) *
                  Real.exp (-(π / 2 * τ)) := by rw [hexp_s]; ring
            _ ≤ (CWR * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π / 2 * τ))) *
                  Real.exp (-(π / 2 * a)) := by gcongr
            _ = _ := by ring
      _ ≤ ∫ τ in Ioi (0 : ℝ), (CWR * c⁻¹ * Real.exp (-(π / 2 * a))) *
            (τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π / 2 * τ))) := by
          refine setIntegral_mono_set (hIh_int.const_mul _)
            (ae_restrict_of_forall_mem measurableSet_Ioi fun τ (hτ : 0 < τ) =>
              mul_nonneg (by positivity)
                (mul_nonneg (mul_nonneg (Real.rpow_nonneg hτ.le _) (by positivity)) (Real.exp_pos _).le))
            (Eventually.of_forall fun τ hτ => lt_of_lt_of_le ha_pos hτ.1)
      _ = (CWR * c⁻¹ * Real.exp (-(π / 2 * a))) *
            ∫ τ in Ioi (0 : ℝ), τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π / 2 * τ)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (CWR * c⁻¹ * Real.exp (-(π / 2 * a))) * Ih := by gcongr
      _ = (CWR * Ih) * c⁻¹ * Real.exp (-(π / 2 * a)) := by ring
      _ ≤ M0 * c⁻¹ * Real.exp (-(π / 2 * a)) := by gcongr

/-- Outer integral `Ioi (0 : ℝ)` bound for `warpAmpRight` in the small-`L` regime (`Sw c^{-2/3} ≤ L ≤ 1`):
`‖∫₀^∞ warpAmpRight * exp(i c edgePhi L)‖ ≤ C * c^{-(3/2)}`. -/
private lemma contDiffOn_hankelEdgeM_2 : ContDiffOn ℝ 2 hankelEdgeM (Ioi 0) :=
  CtMDeriv.contDiffOn_hankelEdgeM.of_le (WithTop.coe_le_coe.mpr le_top)

private lemma continuousOn_hankelEdgeM'_Ioi : ContinuousOn hankelEdgeM' (Ioi 0) := by
  have hc : ContinuousOn (derivWithin hankelEdgeM (Ioi 0)) (Ioi 0) :=
    (contDiffOn_hankelEdgeM_2.derivWithin isOpen_Ioi.uniqueDiffOn (m := 1) (by norm_num)).continuousOn
  exact hc.congr fun t (ht : 0 < t) => by
    rw [derivWithin_of_isOpen isOpen_Ioi ht, (hankelEdgeM_hasDerivAt ht).deriv]

private lemma hankelEdgeM_sub_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    hankelEdgeM a ≤ hankelEdgeM b := by
  have hint : IntervalIntegrable hankelEdgeM' volume a b :=
    (continuousOn_hankelEdgeM'_Ioi.mono fun t ht => by
      rw [uIcc_of_le hab] at ht; exact lt_of_lt_of_le ha ht.1).intervalIntegrable
  have heq : hankelEdgeM b - hankelEdgeM a = ∫ t in a..b, hankelEdgeM' t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => by
      rw [uIcc_of_le hab] at ht; exact hankelEdgeM_hasDerivAt (lt_of_lt_of_le ha ht.1)) hint).symm
  have hnn : 0 ≤ ∫ t in a..b, hankelEdgeM' t := by
    refine intervalIntegral.integral_nonneg hab fun t ht => ?_
    have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
    exact le_trans (by positivity) (hankelEdgeM'_bounds ht_pos).1
  linarith

/-- Quadratic lower bound `x^2 / 64 ≤ hankelEdgeM x - L` on `[3/2 tau0 L, 4]` and
constant lower bound `1 / 4 ≤ hankelEdgeM x - L` on `[4, ∞)` for `0 < L ≤ 1`. -/
private lemma hankelEdgeM_sub_L_ge_sq {L x : ℝ} (hL_pos : 0 < L) (_hL1 : L ≤ 1)
    (hx_lo : 3 / 2 * tau0 L ≤ x) (hx_hi : x ≤ 4) :
    x ^ 2 / 64 ≤ hankelEdgeM x - L := by
  have htau_pos : 0 < tau0 L := tau0_pos hL_pos
  have hx_pos : 0 < x := by linarith
  have h23 : tau0 L ≤ 2 / 3 * x := by linarith
  have h23_le : 2 / 3 * x ≤ x := by linarith
  have h23_pos : 0 < 2 / 3 * x := by positivity
  have hint1 : IntervalIntegrable hankelEdgeM' volume (tau0 L) (2 / 3 * x) :=
    (continuousOn_hankelEdgeM'_Ioi.mono fun t ht => by
      rw [uIcc_of_le h23] at ht; exact lt_of_lt_of_le htau_pos ht.1).intervalIntegrable
  have hint2 : IntervalIntegrable hankelEdgeM' volume (2 / 3 * x) x :=
    (continuousOn_hankelEdgeM'_Ioi.mono fun t ht => by
      rw [uIcc_of_le h23_le] at ht; exact lt_of_lt_of_le h23_pos ht.1).intervalIntegrable
  have hint_all : IntervalIntegrable hankelEdgeM' volume (tau0 L) x := hint1.trans hint2
  have hm_eq : hankelEdgeM x - L = ∫ t in (tau0 L)..x, hankelEdgeM' t := by
    have hL_eq : hankelEdgeM (tau0 L) = L := hankelEdgeM_tau0 hL_pos
    calc hankelEdgeM x - L = hankelEdgeM x - hankelEdgeM (tau0 L) := by rw [hL_eq]
      _ = ∫ t in (tau0 L)..x, hankelEdgeM' t :=
          (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => by
            rw [uIcc_of_le (h23.trans h23_le)] at ht; exact hankelEdgeM_hasDerivAt (lt_of_lt_of_le htau_pos ht.1))
            hint_all).symm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have h1_nn : 0 ≤ ∫ t in (tau0 L)..(2 / 3 * x), hankelEdgeM' t := by
    refine intervalIntegral.integral_nonneg h23 fun t ht => ?_
    have ht_pos : 0 < t := lt_of_lt_of_le htau_pos ht.1
    exact le_trans (by positivity) (hankelEdgeM'_bounds ht_pos).1
  have h2_ge : 5 / 306 * x ^ 2 ≤ ∫ t in (2 / 3 * x)..x, hankelEdgeM' t := by
    have hlin : IntervalIntegrable (fun t : ℝ => t / 17) volume (2 / 3 * x) x :=
      (continuous_id.div_const 17).intervalIntegrable _ _
    have hmono : ∫ t in (2 / 3 * x)..x, t / 17 ≤ ∫ t in (2 / 3 * x)..x, hankelEdgeM' t := by
      refine intervalIntegral.integral_mono_on h23_le hlin hint2 fun t ht => ?_
      have ht_pos : 0 < t := lt_of_lt_of_le h23_pos ht.1
      have hden : 1 + t ^ 2 ≤ 17 := by nlinarith [ht.2, hx_hi]
      calc t / 17 ≤ t / (1 + t ^ 2) := div_le_div_of_nonneg_left ht_pos.le (by positivity) hden
        _ ≤ hankelEdgeM' t := (hankelEdgeM'_bounds ht_pos).1
    have hval : ∫ t in (2 / 3 * x)..x, t / 17 = 5 / 306 * x ^ 2 := by
      rw [intervalIntegral.integral_div, integral_id]; ring
    linarith
  linarith [hm_eq, hsplit, h1_nn, h2_ge, show x ^ 2 / 64 ≤ 5 / 306 * x ^ 2 by nlinarith]

private lemma hankelEdgeM_sub_L_ge_quarter {L x : ℝ} (hL_pos : 0 < L) (hL1 : L ≤ 1) (hx4 : 4 ≤ x) :
    1 / 4 ≤ hankelEdgeM x - L := by
  have hs3 : 3 / 2 * tau0 L ≤ 4 := by
    have ht := (tau0_small_bounds hL_pos hL1).2.2
    linarith
  have h4 := hankelEdgeM_sub_L_ge_sq hL_pos hL1 hs3 le_rfl
  have hm := hankelEdgeM_sub_mono (by norm_num : (0 : ℝ) < 4) hx4
  linarith

/-- Outer integral `Ioi (0 : ℝ)` bound for `warpAmpRight` in the small-`L` regime (`c^{-2/3} ≤ L ≤ 1`):
`‖∫₀^∞ warpAmpRight * exp(i c edgePhi L)‖ ≤ C_sm * c^{-(3/2)}`. -/
private lemma rightTail_I1_small {M0 M_pt : ℝ} (hM0 : 0 ≤ M0) (hMp : 0 ≤ M_pt) :
    ∃ C_sm : ℝ, 0 ≤ C_sm ∧ ∀ {c : ℝ} {L : ℝ} {amp : ℝ → ℂ},
      1 ≤ c → c ^ (-(2 / 3 : ℝ)) ≤ L → L ≤ 1 →
      ContDiffOn ℝ 1 amp (Ioi 0) →
      IntegrableOn (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) (Ioi 0) →
      (∀ {τ : ℝ}, 0 < τ → ‖amp τ‖ ≤ M_pt * c⁻¹ * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) →
      (∀ {τ : ℝ}, 0 < τ → ‖deriv amp τ‖ ≤ M_pt * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) →
      (∀ {τ : ℝ}, 0 < τ → ‖amp τ‖ ≤ M0 * c⁻¹) →
      (∀ {a b : ℝ}, 0 < a → a ≤ b → ∫ x in Icc a b, ‖deriv amp x‖ ≤ M0 * c⁻¹) →
      ‖∫ τ in Ioi (0 : ℝ), amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
        C_sm * c ^ (-(3 / 2 : ℝ)) := by
  set M_pt5 : ℝ := M_pt * 5 ^ 13
  set C1 : ℝ := 288 * M_pt5 * Real.sqrt 3
  set C2 : ℝ := 24 * M_pt5 * Real.sqrt 6 / Real.sqrt (3 / 40)
  set C3 : ℝ := 4 * M0 + (64 + (64 + 8192) * (2 / 3)) * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) + 24 * M0
  refine ⟨C1 + C2 + C3, by positivity, fun {c L amp} hc1 hL_lo hL1 hCD hInt hA0 hA1 hM_glob hV_glob => ?_⟩
  have hcpos : 0 < c := by linarith
  have hL_pos : 0 < L := lt_of_lt_of_le (Real.rpow_pos_of_pos hcpos _) hL_lo
  set f : ℝ → ℂ := fun τ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))
  set s2 : ℝ := 3 / 4 * tau0 L
  set s3 : ℝ := 3 / 2 * tau0 L
  have htau_b := tau0_small_bounds hL_pos hL1
  have hs2_pos : 0 < s2 := by dsimp [s2]; linarith [htau_b.1, Real.sqrt_pos.mpr hL_pos]
  have hs2_s3 : s2 ≤ s3 := by dsimp [s2, s3]; linarith [htau_b.1, Real.sqrt_pos.mpr hL_pos]
  have hs3_pos : 0 < s3 := lt_of_lt_of_le hs2_pos hs2_s3
  have hs3_le3 : s3 ≤ 3 := by dsimp [s3]; linarith [htau_b.2.2]
  have hs3_le4 : s3 ≤ 4 := by linarith
  have hL_pow34 : L ^ (-(3 / 4 : ℝ)) ≤ c ^ (1 / 2 : ℝ) := by
    calc L ^ (-(3 / 4 : ℝ)) ≤ (c ^ (-(2 / 3 : ℝ))) ^ (-(3 / 4 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hcpos _) hL_lo (by norm_num)
      _ = c ^ (1 / 2 : ℝ) := by rw [← Real.rpow_mul hcpos.le]; norm_num
  have hcm2_32 : c ^ (-2 : ℝ) * L ^ (-(3 / 4 : ℝ)) ≤ c ^ (-(3 / 2 : ℝ)) := by
    have hc2_12 : c ^ (-2 : ℝ) * c ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hcpos]; congr 1; norm_num
    calc c ^ (-2 : ℝ) * L ^ (-(3 / 4 : ℝ)) ≤ c ^ (-2 : ℝ) * c ^ (1 / 2 : ℝ) := by gcongr
      _ = c ^ (-(3 / 2 : ℝ)) := hc2_12
  have hc2_32 : c ^ (-2 : ℝ) ≤ c ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have h513 : ∀ {τ : ℝ}, 0 < τ → τ ≤ 4 →
      (1 + τ) ^ 13 * Real.exp (-(π * τ)) ≤ 5 ^ 13 := fun {τ} hτ0 hτ4 => by
    have h1 : (1 + τ) ^ 13 ≤ 5 ^ 13 := pow_le_pow_left₀ (by linarith) (by linarith) 13
    have h2 : Real.exp (-(π * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    calc (1 + τ) ^ 13 * Real.exp (-(π * τ)) ≤ 5 ^ 13 * 1 := by gcongr
      _ = 5 ^ 13 := mul_one _
  have hA0_4 : ∀ {τ : ℝ}, 0 < τ → τ ≤ 4 → ‖amp τ‖ ≤ M_pt5 * c⁻¹ * τ ^ (1 / 2 : ℝ) := fun {τ} hτ0 hτ4 => by
    have hexp0 : 0 ≤ τ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hτ0.le _
    calc ‖amp τ‖ ≤ M_pt * c⁻¹ * τ ^ (1 / 2 : ℝ) * ((1 + τ) ^ 13 * Real.exp (-(π * τ))) := by
          simpa only [mul_assoc] using hA0 hτ0
      _ ≤ M_pt * c⁻¹ * τ ^ (1 / 2 : ℝ) * 5 ^ 13 := by gcongr; exact h513 hτ0 hτ4
      _ = M_pt5 * c⁻¹ * τ ^ (1 / 2 : ℝ) := by dsimp only [M_pt5]; ring
  have hA1_4 : ∀ {τ : ℝ}, 0 < τ → τ ≤ 4 → ‖deriv amp τ‖ ≤ M_pt5 * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) := fun {τ} hτ0 hτ4 => by
    have hexp0 : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ0.le _
    calc ‖deriv amp τ‖ ≤ M_pt * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * ((1 + τ) ^ 13 * Real.exp (-(π * τ))) := by
          simpa only [mul_assoc] using hA1 hτ0
      _ ≤ M_pt * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * 5 ^ 13 := by gcongr; exact h513 hτ0 hτ4
      _ = M_pt5 * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) := by dsimp only [M_pt5]; ring
  have hV_Ioc : ∀ {a b : ℝ}, 0 < a → a ≤ b → b ≤ 4 →
      ∫ x in Icc a b, ‖deriv amp x‖ ≤ 2 * M_pt5 * c⁻¹ * b ^ (1 / 2 : ℝ) := by
    intro a b ha hab hb4
    have h_der_cont : ContinuousOn (fun x => ‖deriv amp x‖) (Icc a b) :=
      ((hCD.derivWithin isOpen_Ioi.uniqueDiffOn (m := 0) (by norm_num)).continuousOn.congr
        (fun t ht => (derivWithin_of_isOpen isOpen_Ioi ht).symm)).mono
        (fun (x : ℝ) (hx : x ∈ Icc a b) => lt_of_lt_of_le ha hx.1) |>.norm
    have hpow : IntegrableOn (fun x : ℝ => M_pt5 * c⁻¹ * x ^ (-(1 / 2 : ℝ))) (Icc a b) :=
      ((ContinuousOn.rpow_const continuousOn_id fun (x : ℝ) (hx : x ∈ Icc a b) =>
        Or.inl (lt_of_lt_of_le ha hx.1).ne').const_mul _).integrableOn_Icc
    calc ∫ x in Icc a b, ‖deriv amp x‖
        ≤ ∫ x in Icc a b, M_pt5 * c⁻¹ * x ^ (-(1 / 2 : ℝ)) :=
          setIntegral_mono_on h_der_cont.integrableOn_Icc hpow measurableSet_Icc fun x hx =>
            hA1_4 (lt_of_lt_of_le ha hx.1) (hx.2.trans hb4)
      _ ≤ ∫ x in Ioc 0 b, M_pt5 * c⁻¹ * x ^ (-(1 / 2 : ℝ)) := by
          rw [integral_Icc_eq_integral_Ioc]
          refine setIntegral_mono_set ?_ (ae_restrict_of_forall_mem measurableSet_Ioc fun x (hx : x ∈ Ioc 0 b) =>
            mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr hcpos.le)) (Real.rpow_nonneg hx.1.le _))
            (Eventually.of_forall (Ioc_subset_Ioc_left ha.le))
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
            ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ))).const_mul _)
      _ = M_pt5 * c⁻¹ * (2 * b ^ (1 / 2 : ℝ)) := by
          rw [← intervalIntegral.integral_of_le (by linarith : 0 ≤ b), intervalIntegral.integral_const_mul,
            _root_.integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ))), Real.zero_rpow (by norm_num)]
          ring
      _ = 2 * M_pt5 * c⁻¹ * b ^ (1 / 2 : ℝ) := by ring
  -- Split `Ioi 0` at `s2`, `s3`, `4`
  have hsplit_s2 : ∫ τ in Ioi (0 : ℝ), f τ =
      (∫ τ in Ioc 0 s2, f τ) + ∫ τ in Ioi s2, f τ := by
    have hU : Ioc (0 : ℝ) s2 ∪ Ioi s2 = Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi hs2_pos.le
    have hdisj : Disjoint (Ioc (0 : ℝ) s2) (Ioi s2) := Set.Ioc_disjoint_Ioi le_rfl
    rw [← setIntegral_union hdisj measurableSet_Ioi (hInt.mono_set Ioc_subset_Ioi_self)
      (hInt.mono_set (Ioi_subset_Ioi hs2_pos.le)), hU]
  have hInt_s2 : IntegrableOn f (Ioi s2) := hInt.mono_set (Ioi_subset_Ioi hs2_pos.le)
  have hsplit_s3 := integral_Ioi_eq_interval_add_Ioi hs2_s3 hInt_s2
  have hInt_s3 : IntegrableOn f (Ioi s3) := hInt_s2.mono_set (Ioi_subset_Ioi hs2_s3)
  have hsplit_4 := integral_Ioi_eq_interval_add_Ioi hs3_le4 hInt_s3
  have hInt_4 : IntegrableOn f (Ioi 4) := hInt_s3.mono_set (Ioi_subset_Ioi hs3_le4)
  have hs2_sqrt : s2 ^ (1 / 2 : ℝ) ≤ Real.sqrt 3 * L ^ (1 / 4 : ℝ) := by
    have hs2_le : s2 ≤ 3 * L ^ (1 / 2 : ℝ) := by
      dsimp only [s2]; rw [← Real.sqrt_eq_rpow]; linarith [htau_b.2.1, Real.sqrt_pos.mpr hL_pos]
    calc s2 ^ (1 / 2 : ℝ) ≤ (3 * L ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hs2_pos.le hs2_le (by norm_num)
      _ = 3 ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hL_pos.le]; norm_num
      _ = Real.sqrt 3 * L ^ (1 / 4 : ℝ) := by rw [← Real.sqrt_eq_rpow]
  have hs3_sqrt : s3 ^ (1 / 2 : ℝ) ≤ Real.sqrt 6 * L ^ (1 / 4 : ℝ) := by
    have hs3_le : s3 ≤ 6 * L ^ (1 / 2 : ℝ) := by
      dsimp only [s3]; rw [← Real.sqrt_eq_rpow]; linarith [htau_b.2.1]
    calc s3 ^ (1 / 2 : ℝ) ≤ (6 * L ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hs3_pos.le hs3_le (by norm_num)
      _ = 6 ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hL_pos.le]; norm_num
      _ = Real.sqrt 6 * L ^ (1 / 4 : ℝ) := by rw [← Real.sqrt_eq_rpow]
  have hs3_m32 : s3 ^ (-(3 / 2 : ℝ)) ≤ (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * L ^ (-(3 / 4 : ℝ)) := by
    have hs3_ge : 3 / 4 * L ^ (1 / 2 : ℝ) ≤ s3 := by
      dsimp only [s3]; rw [← Real.sqrt_eq_rpow]; linarith [htau_b.1, Real.sqrt_nonneg L]
    calc s3 ^ (-(3 / 2 : ℝ)) ≤ (3 / 4 * L ^ (1 / 2 : ℝ)) ^ (-(3 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hs3_ge (by norm_num)
      _ = (3 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * (L ^ (1 / 2 : ℝ)) ^ (-(3 / 2 : ℝ)) :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ = (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * L ^ (-(3 / 4 : ℝ)) := by
          rw [← Real.rpow_mul hL_pos.le, Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num),
            show ((3 / 4 : ℝ))⁻¹ = 4 / 3 by norm_num]; congr 2; norm_num
  have h1_bd : ‖∫ τ in Ioc 0 s2, f τ‖ ≤ C1 * c ^ (-(3 / 2 : ℝ)) := by
    have hv := vdc1_Ioc_edgePhi hs2_pos hcpos (by positivity : 0 < 1 / 32 * L) hCD
      (hInt.mono_set Ioc_subset_Ioi_self)
      (fun x hx => by
        rw [edgePhiDeriv_eq_sub_hankelEdgeM hx.1.le]
        exact (hankelEdgeM_diff_small_inner hL_pos hL1 hx.1.le hx.2).trans (le_abs_self _))
      (fun x hx => by
        have hx12 : x ^ (1 / 2 : ℝ) ≤ Real.sqrt 3 * L ^ (1 / 4 : ℝ) :=
          (Real.rpow_le_rpow hx.1.le hx.2 (by norm_num)).trans hs2_sqrt
        have hxc : x ≤ 4 := hx.2.trans (hs2_s3.trans hs3_le4)
        calc ‖amp x‖ ≤ M_pt5 * c⁻¹ * x ^ (1 / 2 : ℝ) := hA0_4 hx.1 hxc
          _ ≤ M_pt5 * c⁻¹ * (Real.sqrt 3 * L ^ (1 / 4 : ℝ)) := by gcongr
          _ = M_pt5 * Real.sqrt 3 * c⁻¹ * L ^ (1 / 4 : ℝ) := by ring)
      (fun a ha hab => by
        calc ∫ x in Icc a s2, ‖deriv amp x‖
            ≤ 2 * M_pt5 * c⁻¹ * s2 ^ (1 / 2 : ℝ) := hV_Ioc ha hab (hs2_s3.trans hs3_le4)
          _ ≤ 2 * M_pt5 * c⁻¹ * (Real.sqrt 3 * L ^ (1 / 4 : ℝ)) := by gcongr
          _ = 2 * M_pt5 * Real.sqrt 3 * c⁻¹ * L ^ (1 / 4 : ℝ) := by ring)
    have hc2_eq : c⁻¹ / (c * (1 / 32 * L)) = 32 * c ^ (-2 : ℝ) * L⁻¹ := by
      have hc2 : c⁻¹ / c = c ^ (-2 : ℝ) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
      calc c⁻¹ / (c * (1 / 32 * L)) = 32 * (c⁻¹ / c) * L⁻¹ := by ring
        _ = 32 * c ^ (-2 : ℝ) * L⁻¹ := by rw [hc2]
    have hL14 : L ^ (1 / 4 : ℝ) * L⁻¹ = L ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_neg_one L, ← Real.rpow_add hL_pos]; congr 1; norm_num
    refine hv.trans ?_
    calc 3 * (M_pt5 * Real.sqrt 3 * c⁻¹ * L ^ (1 / 4 : ℝ) + 2 * M_pt5 * Real.sqrt 3 * c⁻¹ * L ^ (1 / 4 : ℝ)) /
          (c * (1 / 32 * L))
        = 9 * M_pt5 * Real.sqrt 3 * (c⁻¹ / (c * (1 / 32 * L))) * L ^ (1 / 4 : ℝ) := by ring
      _ = 288 * M_pt5 * Real.sqrt 3 * c ^ (-2 : ℝ) * (L ^ (1 / 4 : ℝ) * L⁻¹) := by rw [hc2_eq]; ring
      _ = C1 * (c ^ (-2 : ℝ) * L ^ (-(3 / 4 : ℝ))) := by dsimp only [C1]; rw [hL14]; ring
      _ ≤ C1 * c ^ (-(3 / 2 : ℝ)) := by gcongr
  have h2_bd : ‖∫ τ in s2..s3, f τ‖ ≤ C2 * c ^ (-(3 / 2 : ℝ)) := by
    have hLam2 : ∀ x ∈ Icc s2 s3, 3 / 40 * Real.sqrt L ≤ |edgePhiDeriv2 x| := by
      intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le hs2_pos hx.1
      rw [abs_edgePhiDeriv2_eq_hankelEdgeM' hx_pos]
      have hx_lo : 3 / 4 * Real.sqrt L ≤ x := (mul_le_mul_of_nonneg_left htau_b.1 (by norm_num)).trans hx.1
      have hx_hi : x ≤ 3 := hx.2.trans hs3_le3
      have hden : 1 + x ^ 2 ≤ 10 := by nlinarith
      calc 3 / 40 * Real.sqrt L = (3 / 4 * Real.sqrt L) / 10 := by ring
        _ ≤ x / (1 + x ^ 2) := div_le_div₀ (by positivity) hx_lo (by positivity) hden
        _ ≤ hankelEdgeM' x := (hankelEdgeM'_bounds hx_pos).1
    have hv := vdc2_Icc_edgePhi_sign (L := L) hs2_s3 hs2_pos hcpos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hL_pos))
      (Or.inl rfl) hCD hLam2
      (fun x hx => by
        have hx12 : x ^ (1 / 2 : ℝ) ≤ Real.sqrt 6 * L ^ (1 / 4 : ℝ) :=
          (Real.rpow_le_rpow (lt_of_lt_of_le hs2_pos hx.1).le hx.2 (by norm_num)).trans hs3_sqrt
        calc ‖amp x‖ ≤ M_pt5 * c⁻¹ * x ^ (1 / 2 : ℝ) := hA0_4 (lt_of_lt_of_le hs2_pos hx.1) (hx.2.trans hs3_le4)
          _ ≤ M_pt5 * c⁻¹ * (Real.sqrt 6 * L ^ (1 / 4 : ℝ)) := by gcongr
          _ = M_pt5 * Real.sqrt 6 * c⁻¹ * L ^ (1 / 4 : ℝ) := by ring)
      (by
        calc ∫ x in Icc s2 s3, ‖deriv amp x‖
            ≤ 2 * M_pt5 * c⁻¹ * s3 ^ (1 / 2 : ℝ) := hV_Ioc hs2_pos hs2_s3 hs3_le4
          _ ≤ 2 * M_pt5 * c⁻¹ * (Real.sqrt 6 * L ^ (1 / 4 : ℝ)) := by gcongr
          _ = 2 * M_pt5 * Real.sqrt 6 * c⁻¹ * L ^ (1 / 4 : ℝ) := by ring)
    have hrt : Real.sqrt (c * (3 / 40 * Real.sqrt L)) = Real.sqrt (3 / 40) * c ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) := by
      rw [mul_left_comm, Real.sqrt_mul (by norm_num), Real.sqrt_mul hcpos.le,
        Real.sqrt_eq_rpow c, Real.sqrt_eq_rpow L, Real.sqrt_eq_rpow (L ^ (1 / 2 : ℝ)),
        ← Real.rpow_mul hL_pos.le, show (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 by norm_num]; ring
    have hc32 : c⁻¹ / c ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_neg hcpos.le, ← Real.rpow_add hcpos]
      congr 1; norm_num
    have hv' : ‖∫ τ in s2..s3, f τ‖ ≤
        8 * (M_pt5 * Real.sqrt 6 * c⁻¹ * L ^ (1 / 4 : ℝ) + 2 * M_pt5 * Real.sqrt 6 * c⁻¹ * L ^ (1 / 4 : ℝ)) /
          Real.sqrt (c * (3 / 40 * Real.sqrt L)) := by
      simpa only [one_mul] using hv
    refine hv'.trans_eq ?_
    calc 8 * (M_pt5 * Real.sqrt 6 * c⁻¹ * L ^ (1 / 4 : ℝ) + 2 * M_pt5 * Real.sqrt 6 * c⁻¹ * L ^ (1 / 4 : ℝ)) /
          Real.sqrt (c * (3 / 40 * Real.sqrt L))
        = (24 * M_pt5 * Real.sqrt 6 / Real.sqrt (3 / 40)) * (c⁻¹ / c ^ (1 / 2 : ℝ)) *
            (L ^ (1 / 4 : ℝ) / L ^ (1 / 4 : ℝ)) := by rw [hrt]; ring
      _ = C2 * c ^ (-(3 / 2 : ℝ)) := by
          rw [hc32, div_self (Real.rpow_pos_of_pos hL_pos _).ne', mul_one]
  have h4_bd : ‖∫ τ in Ioi (4 : ℝ), f τ‖ ≤ 24 * M0 * c ^ (-(3 / 2 : ℝ)) := by
    have hv := vdc1_Ioi_edgePhi_pos (by norm_num : (0 : ℝ) < 4) hcpos (by norm_num : (0 : ℝ) < 1 / 4) hCD hInt_4
      (fun x hx => by
        rw [edgePhiDeriv_eq_sub_hankelEdgeM (by linarith [Set.mem_Ici.mp hx]), abs_sub_comm]
        exact (hankelEdgeM_sub_L_ge_quarter hL_pos hL1 hx).trans (le_abs_self _))
      (fun x hx => hM_glob (by linarith [Set.mem_Ici.mp hx]))
      (fun T hT => hV_glob (by norm_num) hT)
    have hc2_eq : c⁻¹ / c = c ^ (-2 : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
    refine hv.trans ?_
    calc 3 * (M0 * c⁻¹ + M0 * c⁻¹) / (c * (1 / 4)) = 24 * M0 * (c⁻¹ / c) := by ring
      _ = 24 * M0 * c ^ (-2 : ℝ) := by rw [hc2_eq]
      _ ≤ 24 * M0 * c ^ (-(3 / 2 : ℝ)) := by gcongr
  -- Weighted IBP on `[s3, 4]`
  have hs34_bd : ‖∫ τ in s3..4, f τ‖ ≤
      (4 * M0 + (64 + (64 + 8192) * (2 / 3)) * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ)) := by
    let d : ℝ → ℝ := fun τ => hankelEdgeM τ - L
    let u : ℝ → ℂ := fun τ => amp τ / (-Complex.I * (c : ℂ) * (d τ : ℂ))
    let v : ℝ → ℂ := fun τ => Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))
    have hd_pos : ∀ τ ∈ uIcc s3 4, 0 < d τ := fun τ hτ => by
      rw [uIcc_of_le hs3_le4] at hτ
      have hsq := hankelEdgeM_sub_L_ge_sq hL_pos hL1 hτ.1 hτ.2
      have hτ_pos : 0 < τ := lt_of_lt_of_le hs3_pos hτ.1
      linarith [sq_pos_of_pos hτ_pos]
    have hd_ge : ∀ τ ∈ Icc s3 4, τ ^ 2 / 64 ≤ d τ := fun τ hτ =>
      hankelEdgeM_sub_L_ge_sq hL_pos hL1 hτ.1 hτ.2
    have hd_hasD : ∀ τ ∈ uIcc s3 4, HasDerivAt d (hankelEdgeM' τ) τ := fun τ hτ => by
      rw [uIcc_of_le hs3_le4] at hτ
      exact (hankelEdgeM_hasDerivAt (lt_of_lt_of_le hs3_pos hτ.1)).sub_const L
    have hv_hasD : ∀ τ ∈ uIcc s3 4, HasDerivAt v (-Complex.I * (c : ℂ) * (d τ : ℂ) * v τ) τ := fun τ hτ => by
      rw [uIcc_of_le hs3_le4] at hτ
      have hτ0 : 0 ≤ τ := (lt_of_lt_of_le hs3_pos hτ.1).le
      have heq : (Complex.I * (c : ℂ)) * (edgePhiDeriv L τ : ℂ) = -Complex.I * (c : ℂ) * (d τ : ℂ) := by
        rw [edgePhiDeriv_eq_sub_hankelEdgeM hτ0]; dsimp only [d]; push_cast; ring
      have hcomp : HasDerivAt (fun t : ℝ => Complex.I * (c : ℂ) * (edgePhi L t : ℂ))
          (-Complex.I * (c : ℂ) * (d τ : ℂ)) τ := by
        convert (hasDerivAt_edgePhi L τ).ofReal_comp.const_mul (Complex.I * (c : ℂ)) using 1; exact heq.symm
      have hce := hcomp.cexp
      convert hce using 1; ring
    have hden_ne : ∀ τ ∈ uIcc s3 4, -Complex.I * (c : ℂ) * (d τ : ℂ) ≠ 0 := fun τ hτ =>
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hcpos.ne'))
        (Complex.ofReal_ne_zero.mpr (hd_pos τ hτ).ne')
    have hamp_hasD : ∀ τ ∈ uIcc s3 4, HasDerivAt amp (deriv amp τ) τ := fun τ hτ => by
      rw [uIcc_of_le hs3_le4] at hτ
      exact ((hCD.differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds (lt_of_lt_of_le hs3_pos hτ.1))).hasDerivAt
    let u' : ℝ → ℂ := fun τ =>
      (deriv amp τ * (d τ : ℂ) - amp τ * (hankelEdgeM' τ : ℂ)) / (-Complex.I * (c : ℂ) * (d τ : ℂ) ^ 2)
    have hu_hasD : ∀ τ ∈ uIcc s3 4, HasDerivAt u (u' τ) τ := fun τ hτ => by
      have hd_den : HasDerivAt (fun t => -Complex.I * (c : ℂ) * (d t : ℂ))
          (-Complex.I * (c : ℂ) * (hankelEdgeM' τ : ℂ)) τ :=
        ((hd_hasD τ hτ).ofReal_comp).const_mul (-Complex.I * (c : ℂ))
      have hq := (hamp_hasD τ hτ).div hd_den (hden_ne τ hτ)
      convert hq using 1
      have hdτ_ne : (d τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hd_pos τ hτ).ne'
      have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
      dsimp only [u']; field_simp [Complex.I_ne_zero, hc_ne, hdτ_ne]; ring
    have hu'_int : IntervalIntegrable u' volume s3 4 := by
      have hc0 : ContinuousOn u' (Icc s3 4) := by
        have ha1 : ContinuousOn (deriv amp) (Icc s3 4) :=
          ((hCD.derivWithin isOpen_Ioi.uniqueDiffOn (m := 0) (by norm_num)).continuousOn.congr
            (fun t ht => (derivWithin_of_isOpen isOpen_Ioi ht).symm)).mono
            fun (t : ℝ) (ht : t ∈ Icc s3 4) => lt_of_lt_of_le hs3_pos ht.1
        have ha0 : ContinuousOn amp (Icc s3 4) := hCD.continuousOn.mono
          fun (t : ℝ) (ht : t ∈ Icc s3 4) => lt_of_lt_of_le hs3_pos ht.1
        have hd_c : ContinuousOn (fun t => (d t : ℂ)) (Icc s3 4) :=
          Complex.continuous_ofReal.comp_continuousOn ((contDiffOn_hankelEdgeM_2.continuousOn.mono
            fun (t : ℝ) (ht : t ∈ Icc s3 4) => lt_of_lt_of_le hs3_pos ht.1).sub continuousOn_const)
        have hdm_c : ContinuousOn (fun t => (hankelEdgeM' t : ℂ)) (Icc s3 4) :=
          Complex.continuous_ofReal.comp_continuousOn (continuousOn_hankelEdgeM'_Ioi.mono
            fun (t : ℝ) (ht : t ∈ Icc s3 4) => lt_of_lt_of_le hs3_pos ht.1)
        refine ((ha1.mul hd_c).sub (ha0.mul hdm_c)).div (continuousOn_const.mul (hd_c.pow 2)) fun t ht => ?_
        have hdp : d t ≠ 0 := (hd_pos t (by rw [uIcc_of_le hs3_le4]; exact ht)).ne'
        simpa using mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
          (Complex.ofReal_ne_zero.mpr hcpos.ne')) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hdp))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hs3_le4).mpr
        (hc0.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    have hv'_int : IntervalIntegrable (fun τ => -Complex.I * (c : ℂ) * (d τ : ℂ) * v τ) volume s3 4 := by
      have hcont_v : ContinuousOn (fun τ => -Complex.I * (c : ℂ) * (d τ : ℂ) * v τ) (Icc s3 4) := by
        have hd_c : ContinuousOn (fun t => (d t : ℂ)) (Icc s3 4) :=
          Complex.continuous_ofReal.comp_continuousOn ((contDiffOn_hankelEdgeM_2.continuousOn.mono
            fun (t : ℝ) (ht : t ∈ Icc s3 4) => lt_of_lt_of_le hs3_pos ht.1).sub continuousOn_const)
        have hv_c : Continuous v := Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (contDiff_edgePhi L).continuous))
        exact ((continuousOn_const.mul hd_c).mul hv_c.continuousOn)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hs3_le4).mpr
        (hcont_v.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_hasD hv_hasD hu'_int hv'_int
    have h_lhs_eq : (∫ τ in s3..4, u τ * (-Complex.I * (c : ℂ) * (d τ : ℂ) * v τ)) =
        ∫ τ in s3..4, f τ := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
      have hdτ_ne : (d τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hd_pos τ hτ).ne'
      dsimp only [u, v, f]
      field_simp [Complex.I_ne_zero, hc_ne, hdτ_ne]
    rw [h_lhs_eq] at hibp
    have hv_norm : ∀ τ : ℝ, ‖v τ‖ = 1 := fun τ => by
      dsimp only [v]; rw [Complex.norm_exp]
      have : (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)).re = 0 := by
        rw [mul_assoc, Complex.I_mul_re, ← Complex.ofReal_mul, Complex.ofReal_im]; norm_num
      rw [this, Real.exp_zero]
    have hu4_bd : ‖u 4 * v 4‖ ≤ 4 * M0 * c ^ (-2 : ℝ) := by
      have hd4 : (1 / 4 : ℝ) ≤ d 4 := hankelEdgeM_sub_L_ge_quarter hL_pos hL1 le_rfl
      have hamp4 : ‖amp 4‖ ≤ M0 * c⁻¹ := hM_glob (by norm_num)
      rw [norm_mul, hv_norm 4, mul_one]
      dsimp only [u]
      rw [norm_div, norm_mul, norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le,
        Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ d 4)]
      calc ‖amp 4‖ / (c * d 4) ≤ (M0 * c⁻¹) / (c * (1 / 4)) :=
            div_le_div₀ (by positivity) hamp4 (by positivity) (by gcongr)
        _ = 4 * M0 * (c⁻¹ / c) := by ring
        _ = 4 * M0 * c ^ (-2 : ℝ) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
    have hus3_bd : ‖u s3 * v s3‖ ≤ 64 * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-2 : ℝ) * L ^ (-(3 / 4 : ℝ)) := by
      have hds3 : s3 ^ 2 / 64 ≤ d s3 := hd_ge s3 ⟨le_rfl, hs3_le4⟩
      have hds3_pos : 0 < d s3 := hd_pos s3 (by rw [uIcc_of_le hs3_le4]; exact ⟨le_rfl, hs3_le4⟩)
      have hamps3 : ‖amp s3‖ ≤ M_pt5 * c⁻¹ * s3 ^ (1 / 2 : ℝ) := hA0_4 hs3_pos hs3_le4
      rw [norm_mul, hv_norm s3, mul_one]
      dsimp only [u]
      rw [norm_div, norm_mul, norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le,
        Complex.norm_real, Real.norm_of_nonneg hds3_pos.le]
      have hs3_pow_eq : s3 ^ (1 / 2 : ℝ) / s3 ^ 2 = s3 ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast s3 2, ← Real.rpow_sub hs3_pos]; norm_num
      have h12 : (M_pt5 * c⁻¹ * s3 ^ (1 / 2 : ℝ)) / (c * (s3 ^ 2 / 64)) =
          64 * M_pt5 * (c⁻¹ / c) * (s3 ^ (1 / 2 : ℝ) / s3 ^ 2) := by ring
      have hc2_eq : c⁻¹ / c = c ^ (-2 : ℝ) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
      calc ‖amp s3‖ / (c * d s3) ≤ (M_pt5 * c⁻¹ * s3 ^ (1 / 2 : ℝ)) / (c * (s3 ^ 2 / 64)) :=
            div_le_div₀ (by positivity) hamps3 (by positivity) (by gcongr)
        _ = 64 * M_pt5 * c ^ (-2 : ℝ) * s3 ^ (-(3 / 2 : ℝ)) := by rw [h12, hc2_eq, hs3_pow_eq]
        _ ≤ 64 * M_pt5 * c ^ (-2 : ℝ) * ((4 / 3 : ℝ) ^ (3 / 2 : ℝ) * L ^ (-(3 / 4 : ℝ))) := by
            gcongr
        _ = 64 * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-2 : ℝ) * L ^ (-(3 / 4 : ℝ)) := by ring
    have hu'_bd : ‖∫ τ in s3..4, u' τ * v τ‖ ≤
        (64 + 8192) * (2 / 3) * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-2 : ℝ) * L ^ (-(3 / 4 : ℝ)) := by
      let K_u : ℝ := (64 + 8192) * M_pt5 * c ^ (-2 : ℝ)
      have hK_u0 : 0 ≤ K_u := by positivity
      have hint_uv : IntervalIntegrable (fun τ => ‖u' τ * v τ‖) volume s3 4 :=
        (hu'_int.mul_continuousOn (Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (contDiff_edgePhi L).continuous))).continuousOn).norm
      have hint_pow : IntervalIntegrable (fun τ : ℝ => K_u * τ ^ (-(5 / 2 : ℝ))) volume s3 4 := by
        refine (ContinuousOn.intervalIntegrable ?_).const_mul K_u
        rw [uIcc_of_le hs3_le4]
        exact ContinuousOn.rpow_const continuousOn_id fun τ hτ => Or.inl (lt_of_lt_of_le hs3_pos hτ.1).ne'
      have hmono : ∫ τ in s3..4, ‖u' τ * v τ‖ ≤ ∫ τ in s3..4, K_u * τ ^ (-(5 / 2 : ℝ)) := by
        refine intervalIntegral.integral_mono_on hs3_le4 hint_uv hint_pow fun τ hτ => ?_
        have hτ_pos : 0 < τ := lt_of_lt_of_le hs3_pos hτ.1
        have hdm_b := hankelEdgeM'_bounds hτ_pos
        have hdm_nn : 0 ≤ hankelEdgeM' τ := le_trans (by positivity) hdm_b.1
        have hdm_le : hankelEdgeM' τ ≤ 2 * τ := by
          have hpi2 : π ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
          calc hankelEdgeM' τ ≤ π ^ 2 / 6 * τ := hdm_b.2.1
            _ ≤ 2 * τ := by gcongr
        have hd_t : τ ^ 2 / 64 ≤ d τ := hd_ge τ hτ
        have hd_pos_t : 0 < d τ := hd_pos τ (by rwa [uIcc_of_le hs3_le4])
        have ha0_t : ‖amp τ‖ ≤ M_pt5 * c⁻¹ * τ ^ (1 / 2 : ℝ) := hA0_4 hτ_pos hτ.2
        have ha1_t : ‖deriv amp τ‖ ≤ M_pt5 * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) := hA1_4 hτ_pos hτ.2
        rw [norm_mul, hv_norm τ, mul_one]
        dsimp only [u']
        rw [norm_div, norm_mul, norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le,
          norm_pow, Complex.norm_real, Real.norm_of_nonneg hd_pos_t.le]
        have hnum_le : ‖deriv amp τ * (d τ : ℂ) - amp τ * (hankelEdgeM' τ : ℂ)‖ ≤
            ‖deriv amp τ‖ * d τ + ‖amp τ‖ * hankelEdgeM' τ := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd_pos_t.le]
          · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hdm_nn]
        have hsplit_div : (‖deriv amp τ‖ * d τ + ‖amp τ‖ * hankelEdgeM' τ) / (c * d τ ^ 2) =
            ‖deriv amp τ‖ / (c * d τ) + ‖amp τ‖ * hankelEdgeM' τ / (c * d τ ^ 2) := by
          field_simp [hcpos.ne', hd_pos_t.ne']
        have hterm1 : ‖deriv amp τ‖ / (c * d τ) ≤ 64 * M_pt5 * c ^ (-2 : ℝ) * τ ^ (-(5 / 2 : ℝ)) := by
          have hc2_eq : c⁻¹ / c = c ^ (-2 : ℝ) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
          have hpow : τ ^ (-(1 / 2 : ℝ)) / τ ^ 2 = τ ^ (-(5 / 2 : ℝ)) := by
            rw [← Real.rpow_natCast τ 2, ← Real.rpow_sub hτ_pos]; norm_num
          calc ‖deriv amp τ‖ / (c * d τ)
              ≤ (M_pt5 * c⁻¹ * τ ^ (-(1 / 2 : ℝ))) / (c * (τ ^ 2 / 64)) :=
                div_le_div₀ (by positivity) ha1_t (by positivity) (by gcongr)
            _ = 64 * M_pt5 * (c⁻¹ / c) * (τ ^ (-(1 / 2 : ℝ)) / τ ^ 2) := by ring
            _ = 64 * M_pt5 * c ^ (-2 : ℝ) * τ ^ (-(5 / 2 : ℝ)) := by rw [hc2_eq, hpow]
        have hterm2 : ‖amp τ‖ * hankelEdgeM' τ / (c * d τ ^ 2) ≤
            8192 * M_pt5 * c ^ (-2 : ℝ) * τ ^ (-(5 / 2 : ℝ)) := by
          have hc2_eq : c⁻¹ / c = c ^ (-2 : ℝ) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
          have hpow : τ ^ (1 / 2 : ℝ) * τ / τ ^ 4 = τ ^ (-(5 / 2 : ℝ)) := by
            nth_rw 2 [← Real.rpow_one τ]
            rw [← Real.rpow_add hτ_pos, ← Real.rpow_natCast τ 4, ← Real.rpow_sub hτ_pos]
            norm_num
          have hd_sq : (τ ^ 2 / 64) ^ 2 ≤ d τ ^ 2 :=
            pow_le_pow_left₀ (by positivity) hd_t 2
          calc ‖amp τ‖ * hankelEdgeM' τ / (c * d τ ^ 2)
              ≤ (M_pt5 * c⁻¹ * τ ^ (1 / 2 : ℝ)) * (2 * τ) / (c * (τ ^ 2 / 64) ^ 2) :=
                div_le_div₀ (by positivity) (by gcongr) (by positivity) (by gcongr)
            _ = 8192 * M_pt5 * (c⁻¹ / c) * (τ ^ (1 / 2 : ℝ) * τ / τ ^ 4) := by ring
            _ = 8192 * M_pt5 * c ^ (-2 : ℝ) * τ ^ (-(5 / 2 : ℝ)) := by rw [hc2_eq, hpow]
        calc (‖deriv amp τ * (d τ : ℂ) - amp τ * (hankelEdgeM' τ : ℂ)‖) / (c * d τ ^ 2)
            ≤ (‖deriv amp τ‖ * d τ + ‖amp τ‖ * hankelEdgeM' τ) / (c * d τ ^ 2) :=
              div_le_div_of_nonneg_right hnum_le (by positivity)
          _ = ‖deriv amp τ‖ / (c * d τ) + ‖amp τ‖ * hankelEdgeM' τ / (c * d τ ^ 2) := hsplit_div
          _ ≤ 64 * M_pt5 * c ^ (-2 : ℝ) * τ ^ (-(5 / 2 : ℝ)) +
                8192 * M_pt5 * c ^ (-2 : ℝ) * τ ^ (-(5 / 2 : ℝ)) := add_le_add hterm1 hterm2
          _ = K_u * τ ^ (-(5 / 2 : ℝ)) := by dsimp only [K_u]; ring
      have hpow_int : ∫ τ in s3..4, K_u * τ ^ (-(5 / 2 : ℝ)) ≤
          K_u * (2 / 3) * s3 ^ (-(3 / 2 : ℝ)) := by
        rw [intervalIntegral.integral_const_mul,
          _root_.integral_rpow (Or.inr ⟨by norm_num, fun hmem => by
            rw [uIcc_of_le hs3_le4] at hmem; linarith [hmem.1]⟩)]
        have hp1 : -(5 / 2 : ℝ) + 1 = -(3 / 2 : ℝ) := by norm_num
        rw [hp1]
        have h4_pos : 0 ≤ (4 : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
        have hdiff : ((4 : ℝ) ^ (-(3 / 2 : ℝ)) - s3 ^ (-(3 / 2 : ℝ))) / (-(3 / 2 : ℝ)) ≤
            2 / 3 * s3 ^ (-(3 / 2 : ℝ)) := by
          have : ((4 : ℝ) ^ (-(3 / 2 : ℝ)) - s3 ^ (-(3 / 2 : ℝ))) / (-(3 / 2 : ℝ)) =
              2 / 3 * s3 ^ (-(3 / 2 : ℝ)) - 2 / 3 * (4 : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
          linarith
        calc K_u * (((4 : ℝ) ^ (-(3 / 2 : ℝ)) - s3 ^ (-(3 / 2 : ℝ))) / (-(3 / 2 : ℝ)))
            ≤ K_u * (2 / 3 * s3 ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hdiff hK_u0
          _ = K_u * (2 / 3) * s3 ^ (-(3 / 2 : ℝ)) := by ring
      calc ‖∫ τ in s3..4, u' τ * v τ‖ ≤ ∫ τ in s3..4, ‖u' τ * v τ‖ :=
            intervalIntegral.norm_integral_le_integral_norm hs3_le4
        _ ≤ ∫ τ in s3..4, K_u * τ ^ (-(5 / 2 : ℝ)) := hmono
        _ ≤ K_u * (2 / 3) * s3 ^ (-(3 / 2 : ℝ)) := hpow_int
        _ ≤ K_u * (2 / 3) * ((4 / 3 : ℝ) ^ (3 / 2 : ℝ) * L ^ (-(3 / 4 : ℝ))) := by gcongr
        _ = (64 + 8192) * (2 / 3) * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-2 : ℝ) * L ^ (-(3 / 4 : ℝ)) := by
            dsimp only [K_u]; ring
    rw [hibp]
    have htri : ‖u 4 * v 4 - u s3 * v s3 - ∫ τ in s3..4, u' τ * v τ‖ ≤
        ‖u 4 * v 4‖ + ‖u s3 * v s3‖ + ‖∫ τ in s3..4, u' τ * v τ‖ := by
      calc ‖u 4 * v 4 - u s3 * v s3 - ∫ τ in s3..4, u' τ * v τ‖
          ≤ ‖u 4 * v 4 - u s3 * v s3‖ + ‖∫ τ in s3..4, u' τ * v τ‖ := norm_sub_le _ _
        _ ≤ (‖u 4 * v 4‖ + ‖u s3 * v s3‖) + ‖∫ τ in s3..4, u' τ * v τ‖ :=
            add_le_add (norm_sub_le _ _) le_rfl
    refine htri.trans ?_
    have hm_t1 : 4 * M0 * c ^ (-2 : ℝ) ≤ 4 * M0 * c ^ (-(3 / 2 : ℝ)) := by gcongr
    have hm_t2 : 64 * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-2 : ℝ) * L ^ (-(3 / 4 : ℝ)) ≤
        64 * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-(3 / 2 : ℝ)) := by
      rw [mul_assoc (64 * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ))]; gcongr
    have hm_t3 : (64 + 8192) * (2 / 3) * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-2 : ℝ) * L ^ (-(3 / 4 : ℝ)) ≤
        (64 + 8192) * (2 / 3) * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-(3 / 2 : ℝ)) := by
      rw [mul_assoc ((64 + 8192) * (2 / 3) * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ))]; gcongr
    calc ‖u 4 * v 4‖ + ‖u s3 * v s3‖ + ‖∫ τ in s3..4, u' τ * v τ‖
        ≤ 4 * M0 * c ^ (-2 : ℝ) +
            64 * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-2 : ℝ) * L ^ (-(3 / 4 : ℝ)) +
            (64 + 8192) * (2 / 3) * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-2 : ℝ) * L ^ (-(3 / 4 : ℝ)) :=
          add_le_add (add_le_add hu4_bd hus3_bd) hu'_bd
      _ ≤ 4 * M0 * c ^ (-(3 / 2 : ℝ)) +
            64 * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-(3 / 2 : ℝ)) +
            (64 + 8192) * (2 / 3) * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ) * c ^ (-(3 / 2 : ℝ)) :=
          add_le_add (add_le_add hm_t1 hm_t2) hm_t3
      _ = (4 * M0 + (64 + (64 + 8192) * (2 / 3)) * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ)) := by
          ring
  have hcomb : ∫ τ in Ioi (0 : ℝ), f τ =
      (∫ τ in Ioc 0 s2, f τ) + ((∫ τ in s2..s3, f τ) + ((∫ τ in s3..4, f τ) + ∫ τ in Ioi 4, f τ)) := by
    rw [hsplit_s2, hsplit_s3, hsplit_4]
  rw [hcomb]
  refine (norm_sum4_le _ _ _ _).trans ?_
  calc ‖∫ τ in Ioc 0 s2, f τ‖ + ‖∫ τ in s2..s3, f τ‖ + ‖∫ τ in s3..4, f τ‖ + ‖∫ τ in Ioi 4, f τ‖
      ≤ C1 * c ^ (-(3 / 2 : ℝ)) + C2 * c ^ (-(3 / 2 : ℝ)) +
          (4 * M0 + (64 + (64 + 8192) * (2 / 3)) * M_pt5 * (4 / 3 : ℝ) ^ (3 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ)) +
          24 * M0 * c ^ (-(3 / 2 : ℝ)) := by
        exact add_le_add (add_le_add (add_le_add h1_bd h2_bd) hs34_bd) h4_bd
    _ = (C1 + C2 + C3) * c ^ (-(3 / 2 : ℝ)) := by dsimp only [C3]; ring

/-- Exponential decay bound at `tau0 (L / 2)` for `2 ≤ L`: gives both `O(L^{-1/2})` everywhere on
`[2, ∞)` and `O(c⁻¹ * L⁻¹)` whenever `1 / 4 * Real.log c ≤ L`. -/
private lemma exp_neg_half_tau0_half_bounds {L : ℝ} (hL2 : 2 ≤ L) :
    let K9 : ℝ := (Nat.factorial 9 : ℝ) * 2 ^ 9
    Real.exp (-(π / 2 * tau0 (L / 2))) ≤ 4 * K9 * L ^ (-(1 / 2 : ℝ)) ∧
      ∀ {c : ℝ}, 1 ≤ c → 1 / 4 * Real.log c ≤ L →
        Real.exp (-(π / 2 * tau0 (L / 2))) ≤ 2 * K9 * c⁻¹ * L⁻¹ := by
  intro K9
  have hL2_1 : 1 ≤ L / 2 := by linarith
  have hL_pos : 0 < L := by linarith
  have htau_lo : Real.exp (L / 2) / π ≤ tau0 (L / 2) := (tau0_large_bounds hL2_1).1
  set u : ℝ := Real.exp (L / 2)
  have hu_pos : 0 < u := Real.exp_pos _
  have hu_ge_1 : 1 ≤ u := Real.one_le_exp (by linarith)
  have hu_ge_halfL : L / 2 ≤ u := by
    have := Real.add_one_le_exp (L / 2); linarith
  have hpi_s1 : u / 2 ≤ π / 2 * tau0 (L / 2) := by
    have : π / 2 * (u / π) = u / 2 := by field_simp [Real.pi_ne_zero]
    nlinarith [Real.pi_pos]
  have hpow_exp : (u / 2) ^ 9 / (Nat.factorial 9 : ℝ) ≤ Real.exp (u / 2) :=
    Real.pow_div_factorial_le_exp (u / 2) (by positivity) 9
  have hexp_main : Real.exp (-(π / 2 * tau0 (L / 2))) ≤ K9 / u ^ 9 := by
    have h1 : Real.exp (-(π / 2 * tau0 (L / 2))) ≤ Real.exp (-(u / 2)) :=
      Real.exp_le_exp.mpr (neg_le_neg hpi_s1)
    have h2 : Real.exp (-(u / 2)) = (Real.exp (u / 2))⁻¹ := Real.exp_neg _
    have hpow_pos : 0 < (u / 2) ^ 9 / (Nat.factorial 9 : ℝ) := by positivity
    have h3 : (Real.exp (u / 2))⁻¹ ≤ ((u / 2) ^ 9 / (Nat.factorial 9 : ℝ))⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) hpow_pos).mpr hpow_exp
    have h4 : ((u / 2) ^ 9 / (Nat.factorial 9 : ℝ))⁻¹ = K9 / u ^ 9 := by
      dsimp only [K9]; field_simp [hu_pos.ne']
    linarith [h1, h2, h3, h4]
  refine ⟨?_, ?_⟩
  · have hu9_ge : (L / 2) ^ 2 ≤ u ^ 9 := by
      have hu2 : (L / 2) ^ 2 ≤ u ^ 2 := by nlinarith
      calc (L / 2) ^ 2 ≤ u ^ 2 := hu2
        _ = u ^ 2 * 1 := (mul_one _).symm
        _ ≤ u ^ 2 * u ^ 7 := mul_le_mul_of_nonneg_left (one_le_pow₀ hu_ge_1) (by positivity)
        _ = u ^ 9 := by ring
    have hL2_ge : L ^ (1 / 2 : ℝ) ≤ L ^ 2 := by
      rw [← Real.rpow_natCast L 2]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    calc Real.exp (-(π / 2 * tau0 (L / 2))) ≤ K9 / u ^ 9 := hexp_main
      _ ≤ K9 / (L / 2) ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hu9_ge
      _ = 4 * K9 / L ^ 2 := by ring
      _ ≤ 4 * K9 / L ^ (1 / 2 : ℝ) := div_le_div_of_nonneg_left (by positivity) (by positivity) hL2_ge
      _ = 4 * K9 * L ^ (-(1 / 2 : ℝ)) := by rw [div_eq_mul_inv, Real.rpow_neg hL_pos.le]
  · intro c hc1 hLc
    have hcpos : 0 < c := by linarith
    have hc8 : c ^ (1 / 8 : ℝ) ≤ u := by
      rw [show c ^ (1 / 8 : ℝ) = Real.exp (1 / 8 * Real.log c) by
        rw [Real.rpow_def_of_pos hcpos, mul_comm]]
      exact Real.exp_le_exp.mpr (by linarith)
    have hu8_c : c ≤ u ^ 8 := by
      have h8 : (c ^ (1 / 8 : ℝ)) ^ 8 = c := by
        rw [← Real.rpow_natCast (c ^ (1 / 8 : ℝ)) 8, ← Real.rpow_mul hcpos.le]
        norm_num
      calc c = (c ^ (1 / 8 : ℝ)) ^ 8 := h8.symm
        _ ≤ u ^ 8 := pow_le_pow_left₀ (by positivity) hc8 8
    have hu9_ge : c * (L / 2) ≤ u ^ 9 := by
      calc c * (L / 2) ≤ u ^ 8 * u := mul_le_mul hu8_c hu_ge_halfL (by positivity) (by positivity)
        _ = u ^ 9 := by ring
    calc Real.exp (-(π / 2 * tau0 (L / 2))) ≤ K9 / u ^ 9 := hexp_main
      _ ≤ K9 / (c * (L / 2)) := div_le_div_of_nonneg_left (by positivity) (by positivity) hu9_ge
      _ = 2 * K9 * c⁻¹ * L⁻¹ := by field_simp [hcpos.ne', hL_pos.ne']

/-- Outer integral `Ioi (0 : ℝ)` bound for `warpAmpRight` in the moderate regime (`1 ≤ L ≤ 2`):
`‖∫₀^∞ warpAmpRight * exp(i c edgePhi L)‖ ≤ C_mid12 * c^{-(3/2)}`. -/
private lemma rightTail_I1_mid12 {M0 : ℝ} (hM0 : 0 ≤ M0) :
    ∃ C_mid12 : ℝ, 0 ≤ C_mid12 ∧ ∀ {c L : ℝ} {amp : ℝ → ℂ},
      1 ≤ c → 1 ≤ L → L ≤ 2 →
      ContDiffOn ℝ 1 amp (Ioi 0) →
      IntegrableOn (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) (Ioi 0) →
      (∀ {τ : ℝ}, 0 < τ → ‖amp τ‖ ≤ M0 * c⁻¹) →
      (∀ {a b : ℝ}, 0 < a → a ≤ b → ∫ x in Icc a b, ‖deriv amp x‖ ≤ M0 * c⁻¹) →
      ‖∫ τ in Ioi (0 : ℝ), amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
        C_mid12 * c ^ (-(3 / 2 : ℝ)) := by
  set C_mid12 : ℝ := 192 * M0 + 16 * M0 / Real.sqrt (3 / 656) + 72 * M0
  refine ⟨C_mid12, by positivity, fun {c L amp} hc1 hL1 hL2 hCD hInt hM_glob hV_glob => ?_⟩
  have hcpos : 0 < c := by linarith
  have hL_pos : 0 < L := by linarith
  set f : ℝ → ℂ := fun τ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))
  set s2 : ℝ := 3 / 4 * tau0 L
  set s3 : ℝ := 3 / 2 * tau0 L
  have htau_pos : 0 < tau0 L := tau0_pos hL_pos
  have hs2_pos : 0 < s2 := by positivity
  have hs2_s3 : s2 ≤ s3 := by dsimp [s2, s3]; linarith
  have hs3_pos : 0 < s3 := lt_of_lt_of_le hs2_pos hs2_s3
  have hc2_32 : c ^ (-2 : ℝ) ≤ c ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc2_eq : c⁻¹ / c = c ^ (-2 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
  have hsplit_s2 : ∫ τ in Ioi (0 : ℝ), f τ =
      (∫ τ in Ioc 0 s2, f τ) + ∫ τ in Ioi s2, f τ := by
    have hU : Ioc (0 : ℝ) s2 ∪ Ioi s2 = Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi hs2_pos.le
    have hdisj : Disjoint (Ioc (0 : ℝ) s2) (Ioi s2) := Set.Ioc_disjoint_Ioi le_rfl
    rw [← setIntegral_union hdisj measurableSet_Ioi (hInt.mono_set Ioc_subset_Ioi_self)
      (hInt.mono_set (Ioi_subset_Ioi hs2_pos.le)), hU]
  have hInt_s2 : IntegrableOn f (Ioi s2) := hInt.mono_set (Ioi_subset_Ioi hs2_pos.le)
  have hsplit_s3 := integral_Ioi_eq_interval_add_Ioi hs2_s3 hInt_s2
  have hInt_s3 : IntegrableOn f (Ioi s3) := hInt_s2.mono_set (Ioi_subset_Ioi hs2_s3)
  have h1_bd : ‖∫ τ in Ioc 0 s2, f τ‖ ≤ 192 * M0 * c ^ (-(3 / 2 : ℝ)) := by
    have hv := vdc1_Ioc_edgePhi hs2_pos hcpos (by norm_num : (0 : ℝ) < 1 / 32) hCD
      (hInt.mono_set Ioc_subset_Ioi_self)
      (fun x hx => by
        rw [edgePhiDeriv_eq_sub_hankelEdgeM hx.1.le]
        exact (hankelEdgeM_diff_large_inner hL1 hx.1.le hx.2).trans (le_abs_self _))
      (fun x hx => hM_glob hx.1)
      (fun a ha hab => hV_glob ha hab)
    refine hv.trans ?_
    calc 3 * (M0 * c⁻¹ + M0 * c⁻¹) / (c * (1 / 32)) = 192 * M0 * (c⁻¹ / c) := by ring
      _ = 192 * M0 * c ^ (-2 : ℝ) := by rw [hc2_eq]
      _ ≤ 192 * M0 * c ^ (-(3 / 2 : ℝ)) := by gcongr
  have h3_bd : ‖∫ τ in Ioi s3, f τ‖ ≤ 72 * M0 * c ^ (-(3 / 2 : ℝ)) := by
    have hv := vdc1_Ioi_edgePhi_pos hs3_pos hcpos (by norm_num : (0 : ℝ) < 1 / 12) hCD hInt_s3
      (fun x hx => by
        rw [edgePhiDeriv_eq_sub_hankelEdgeM (le_trans hs3_pos.le hx), abs_sub_comm]
        exact (hankelEdgeM_diff_large_outer hL1 hx).trans (le_abs_self _))
      (fun x hx => hM_glob (lt_of_lt_of_le hs3_pos hx))
      (fun T hT => hV_glob hs3_pos hT)
    refine hv.trans ?_
    calc 3 * (M0 * c⁻¹ + M0 * c⁻¹) / (c * (1 / 12)) = 72 * M0 * (c⁻¹ / c) := by ring
      _ = 72 * M0 * c ^ (-2 : ℝ) := by rw [hc2_eq]
      _ ≤ 72 * M0 * c ^ (-(3 / 2 : ℝ)) := by gcongr
  have h2_bd : ‖∫ τ in s2..s3, f τ‖ ≤ (16 * M0 / Real.sqrt (3 / 656)) * c ^ (-(3 / 2 : ℝ)) := by
    have htau_b := tau0_large_bounds hL1
    have he2 : Real.exp L ≤ 8 := by
      have h1 : Real.exp 1 ≤ 2.72 := Real.exp_one_lt_d9.le.trans (by norm_num)
      have h2 : Real.exp L ≤ Real.exp 2 := Real.exp_le_exp.mpr hL2
      have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      nlinarith [(Real.exp_pos 1).le]
    have htau_hi : tau0 L ≤ 16 / 3 := by
      have h3 : (3 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
      calc tau0 L ≤ 2 * Real.exp L / π := htau_b.2
        _ ≤ 2 * 8 / 3 := div_le_div₀ (by positivity) (by linarith) (by norm_num) h3
        _ = 16 / 3 := by norm_num
    have hLam2 : ∀ x ∈ Icc s2 s3, 3 / 656 ≤ |edgePhiDeriv2 x| := fun x hx => by
      have hx_pos : 0 < x := lt_of_lt_of_le hs2_pos hx.1
      rw [abs_edgePhiDeriv2_eq_hankelEdgeM' hx_pos]
      have hx_hi : x ≤ 8 := by dsimp [s3] at hx; linarith [hx.2, htau_hi]
      have hx_lo : 3 / 4 * (Real.exp L / π) ≤ x := by
        have := mul_le_mul_of_nonneg_left htau_b.1 (by norm_num : (0 : ℝ) ≤ 3 / 4)
        exact this.trans hx.1
      have hexp1 : 2 ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
      have hpi4 : π ≤ 4 := Real.pi_lt_four.le
      have hx_ge38 : 3 / 8 ≤ x := by
        have : 3 / 4 * (2 / 4) ≤ 3 / 4 * (Real.exp L / π) :=
          mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity) hexp1 Real.pi_pos hpi4) (by norm_num)
        linarith
      have hden : 1 + x ^ 2 ≤ 656 / 3 * x := by nlinarith [hx_ge38, hx_hi]
      have hdiv : 3 / 656 ≤ x / (1 + x ^ 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
      exact hdiv.trans (hankelEdgeM'_bounds hx_pos).1
    have hv := vdc2_Icc_edgePhi_sign (L := L) hs2_s3 hs2_pos hcpos (by norm_num : (0 : ℝ) < 3 / 656)
      (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
      hCD
      hLam2
      (fun x hx => by simpa only [one_mul] using hM_glob (lt_of_lt_of_le hs2_pos hx.1))
      (by simpa only [one_mul] using hV_glob hs2_pos hs2_s3)
    have hrt : Real.sqrt (c * (3 / 656)) = Real.sqrt (3 / 656) * c ^ (1 / 2 : ℝ) := by
      rw [mul_comm, Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    have hc32 : c⁻¹ / c ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_neg hcpos.le, ← Real.rpow_add hcpos]
      congr 1; norm_num
    have hv' : ‖∫ τ in s2..s3, f τ‖ ≤ 8 * (M0 * c⁻¹ + M0 * c⁻¹) / Real.sqrt (c * (3 / 656)) := by
      simpa only [one_mul] using hv
    refine hv'.trans_eq ?_
    calc 8 * (M0 * c⁻¹ + M0 * c⁻¹) / Real.sqrt (c * (3 / 656))
        = (16 * M0 / Real.sqrt (3 / 656)) * (c⁻¹ / c ^ (1 / 2 : ℝ)) := by rw [hrt]; ring
      _ = (16 * M0 / Real.sqrt (3 / 656)) * c ^ (-(3 / 2 : ℝ)) := by rw [hc32]
  rw [hsplit_s2, hsplit_s3]
  refine (norm_sum3_le _ _ _).trans ?_
  calc ‖∫ τ in Ioc 0 s2, f τ‖ + ‖∫ τ in s2..s3, f τ‖ + ‖∫ τ in Ioi s3, f τ‖
      ≤ 192 * M0 * c ^ (-(3 / 2 : ℝ)) + (16 * M0 / Real.sqrt (3 / 656)) * c ^ (-(3 / 2 : ℝ)) +
          72 * M0 * c ^ (-(3 / 2 : ℝ)) := add_le_add (add_le_add h1_bd h2_bd) h3_bd
    _ = C_mid12 * c ^ (-(3 / 2 : ℝ)) := by dsimp only [C_mid12]; ring

/-- Sub-lemma for `rightTail_I1_large`: `[s2, s3]` `vdc2` bound with `exp(L/2) * exp(-π/2 s2) ≤ 8 * exp(-π/2 s1)`. -/
private lemma rightTail_I1_large_s23 {M1 c L : ℝ} (hM1 : 0 ≤ M1) (hc1 : 1 ≤ c) (hL2 : 2 ≤ L)
    {amp : ℝ → ℂ} (hCD : ContDiffOn ℝ 1 amp (Ioi 0))
    (hME_s2 : ∀ {τ : ℝ}, 3 / 4 * tau0 L ≤ τ →
      ‖amp τ‖ ≤ M1 * c⁻¹ * Real.exp (-(π / 2 * (3 / 4 * tau0 L))))
    (hVE_s2 : ∀ {T : ℝ}, 3 / 4 * tau0 L ≤ T →
      ∫ x in Icc (3 / 4 * tau0 L) T, ‖deriv amp x‖ ≤ M1 * c⁻¹ * Real.exp (-(π / 2 * (3 / 4 * tau0 L)))) :
    ‖∫ τ in (3 / 4 * tau0 L)..(3 / 2 * tau0 L),
        amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
      256 * M1 * Real.sqrt 3 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * tau0 (L / 2))) := by
  have hcpos : 0 < c := by linarith
  have hL_pos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  set s1 : ℝ := tau0 (L / 2)
  set s2 : ℝ := 3 / 4 * tau0 L
  set s3 : ℝ := 3 / 2 * tau0 L
  have htau_pos : 0 < tau0 L := tau0_pos hL_pos
  have hs2_pos : 0 < s2 := by positivity
  have hs2_s3 : s2 ≤ s3 := by dsimp [s2, s3]; linarith
  have htau_b := tau0_large_bounds hL1
  have hLam2 : ∀ x ∈ Icc s2 s3, 1 / (3 * Real.exp L) ≤ |edgePhiDeriv2 x| := fun x hx => by
    have hx_pos : 0 < x := lt_of_lt_of_le hs2_pos hx.1
    rw [abs_edgePhiDeriv2_eq_hankelEdgeM' hx_pos]
    have hx_ge1 : 1 ≤ x := by
      have he2 : (6 : ℝ) ≤ Real.exp L := by
        have h1 : (2.7 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
        have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        have h3 : (7 : ℝ) ≤ Real.exp 2 := by nlinarith only [h1, h2, (Real.exp_pos 1).le]
        exact (by linarith : (6 : ℝ) ≤ 7).trans (h3.trans (Real.exp_le_exp.mpr hL2))
      have hpi_hi : π ≤ 4 := Real.pi_lt_four.le
      have : 1 ≤ s2 := by
        dsimp [s2]
        have : 3 / 4 * (6 / 4) ≤ 3 / 4 * (Real.exp L / π) :=
          mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity) he2 Real.pi_pos hpi_hi) (by norm_num)
        linarith [htau_b.1]
      exact this.trans hx.1
    have hx_hi : x ≤ 3 * Real.exp L / 2 := by
      have htau_hi : tau0 L ≤ Real.exp L := by
        have hpi_lo : 2 ≤ π := by linarith [Real.pi_gt_three]
        calc tau0 L ≤ 2 * Real.exp L / π := htau_b.2
          _ ≤ 2 * Real.exp L / 2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hpi_lo
          _ = Real.exp L := by ring
      dsimp [s3] at hx; linarith [hx.2, htau_hi]
    have hden : 1 + x ^ 2 ≤ 3 * Real.exp L * x := by
      have hx2_le : x ^ 2 ≤ (3 * Real.exp L / 2) * x := by nlinarith
      have h1_le : 1 ≤ (3 / 2 : ℝ) * Real.exp L * x := by
        have hexp1 : 1 ≤ Real.exp L := Real.one_le_exp hL_pos.le
        nlinarith
      linarith
    have hdiv : 1 / (3 * Real.exp L) ≤ x / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    exact hdiv.trans (hankelEdgeM'_bounds hx_pos).1
  have hc0' : ContinuousOn (deriv amp) (Ioi 0) :=
    (hCD.derivWithin isOpen_Ioi.uniqueDiffOn (m := 0) (by norm_num)).continuousOn.congr
      fun t ht => (derivWithin_of_isOpen isOpen_Ioi ht).symm
  have hV_s23 : ∫ x in Icc s2 s3, ‖deriv amp x‖ ≤ M1 * c⁻¹ * Real.exp (-(π / 2 * s2)) := by
    have hint_s23 : IntegrableOn (fun x => ‖deriv amp x‖) (Icc s2 s3) :=
      ((hc0'.norm).mono fun (x : ℝ) (hx : x ∈ Icc s2 s3) => lt_of_lt_of_le hs2_pos hx.1).integrableOn_Icc
    exact (setIntegral_mono_set hint_s23 (Eventually.of_forall fun _ => norm_nonneg _)
      (Icc_subset_Icc le_rfl le_rfl).eventuallySubset).trans (hVE_s2 hs2_s3)
  have hv := vdc2_Icc_edgePhi_sign (L := L) hs2_s3 hs2_pos hcpos (by positivity : 0 < 1 / (3 * Real.exp L))
    (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
    hCD hLam2 (fun x hx => by simpa only [one_mul] using hME_s2 hx.1)
    (by simpa only [one_mul] using hV_s23)
  have hsqrt_rel : Real.exp (L / 2) * Real.exp (-(π / 2 * s2)) ≤ 8 * Real.exp (-(π / 2 * s1)) := by
    have hL2_1 : 1 ≤ L / 2 := by linarith
    have htau_half := (tau0_large_bounds hL2_1).2
    have hs2_ge : 3 / 4 * (Real.exp L / π) ≤ s2 := by dsimp [s2]; linarith [htau_b.1]
    have hs1_le : s1 ≤ 2 * Real.exp (L / 2) / π := htau_half
    have hpi_gap : π / 2 * s2 - π / 2 * s1 ≥ 3 / 8 * Real.exp L - Real.exp (L / 2) := by
      have : π / 2 * (3 / 4 * (Real.exp L / π)) = 3 / 8 * Real.exp L := by field_simp [Real.pi_ne_zero]; ring
      have : π / 2 * (2 * Real.exp (L / 2) / π) = Real.exp (L / 2) := by field_simp [Real.pi_ne_zero]
      nlinarith [Real.pi_pos]
    have hexp_sq : Real.exp L = Real.exp (L / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    have hquad : Real.exp (L / 2) - 1 ≤ 3 / 8 * Real.exp L - Real.exp (L / 2) + 2 := by
      nlinarith only [sq_nonneg (Real.exp (L / 2) - 8 / 3), hexp_sq]
    have : L / 2 ≤ 3 / 8 * Real.exp L - Real.exp (L / 2) + 2 := by
      have := Real.add_one_le_exp (L / 2); linarith
    have hexp2_le8 : Real.exp 2 ≤ 8 := by
      have h1 : Real.exp 1 ≤ 2.72 := Real.exp_one_lt_d9.le.trans (by norm_num)
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      nlinarith only [h1, h2, (Real.exp_pos 1).le]
    have hle_exp : Real.exp (L / 2 + (-(π / 2 * s2))) ≤ Real.exp (2 + (-(π / 2 * s1))) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_add, Real.exp_add] at hle_exp
    calc Real.exp (L / 2) * Real.exp (-(π / 2 * s2)) ≤ Real.exp 2 * Real.exp (-(π / 2 * s1)) := hle_exp
      _ ≤ 8 * Real.exp (-(π / 2 * s1)) := mul_le_mul_of_nonneg_right hexp2_le8 (Real.exp_pos _).le
  have hrt : Real.sqrt (c * (1 / (3 * Real.exp L))) = c ^ (1 / 2 : ℝ) / (Real.sqrt 3 * Real.exp (L / 2)) := by
    have he_eq : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
      rw [Real.sqrt_eq_rpow (Real.exp L), ← Real.exp_mul]; congr 1; ring
    have h3e : Real.sqrt (3 * Real.exp L) = Real.sqrt 3 * Real.exp (L / 2) := by
      rw [Real.sqrt_mul (by norm_num), he_eq]
    rw [Real.sqrt_mul hcpos.le, Real.sqrt_div (by norm_num), Real.sqrt_one, h3e, Real.sqrt_eq_rpow c, mul_one_div]
  have hc32 : c⁻¹ / c ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_neg hcpos.le, ← Real.rpow_add hcpos]
    congr 1; norm_num
  have hv' : ‖∫ τ in s2..s3, amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
      8 * (M1 * c⁻¹ * Real.exp (-(π / 2 * s2)) + M1 * c⁻¹ * Real.exp (-(π / 2 * s2))) /
        Real.sqrt (c * (1 / (3 * Real.exp L))) := by
    simpa only [one_mul] using hv
  have heq_alg : 8 * (M1 * c⁻¹ * Real.exp (-(π / 2 * s2)) + M1 * c⁻¹ * Real.exp (-(π / 2 * s2))) /
        Real.sqrt (c * (1 / (3 * Real.exp L))) =
      16 * M1 * Real.sqrt 3 * (c⁻¹ / c ^ (1 / 2 : ℝ)) * (Real.exp (L / 2) * Real.exp (-(π / 2 * s2))) := by
    rw [hrt]
    have hrt3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have he_ne : Real.exp (L / 2) ≠ 0 := (Real.exp_pos _).ne'
    field_simp [hrt3, he_ne]; ring
  have hle1 : 16 * M1 * Real.sqrt 3 * c ^ (-(3 / 2 : ℝ)) * (Real.exp (L / 2) * Real.exp (-(π / 2 * s2))) ≤
      16 * M1 * Real.sqrt 3 * c ^ (-(3 / 2 : ℝ)) * (8 * Real.exp (-(π / 2 * s1))) :=
    mul_le_mul_of_nonneg_left hsqrt_rel
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM1) (Real.sqrt_nonneg 3)) (Real.rpow_nonneg hcpos.le _))
  have hle2 : 16 * M1 * Real.sqrt 3 * c ^ (-(3 / 2 : ℝ)) * (8 * Real.exp (-(π / 2 * s1))) ≤
      256 * M1 * Real.sqrt 3 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) := by
    have h8 : 16 * 8 * (M1 * Real.sqrt 3 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1))) ≤
        256 * (M1 * Real.sqrt 3 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1))) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    linarith only [h8]
  refine hv'.trans ?_
  rw [heq_alg, hc32]
  exact hle1.trans hle2

/-- Outer integral `Ioi (0 : ℝ)` bound for `warpAmpRight` in the large-`L` regime (`2 ≤ L`):
gives BOTH `C_lg * c^{-(3/2)} * L^{-(1/2)}` globally for `2 ≤ L`, and
`C_far * c^{-2} * L^{-1}` when `1 / 4 * Real.log c ≤ L`. -/
private lemma rightTail_I1_large {M0 M1 : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) :
    ∃ C_lg : ℝ, 0 ≤ C_lg ∧ ∀ {c L : ℝ} {amp : ℝ → ℂ},
      1 ≤ c → 2 ≤ L →
      ContDiffOn ℝ 1 amp (Ioi 0) →
      IntegrableOn (fun τ : ℝ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) (Ioi 0) →
      (∀ {τ : ℝ}, 0 < τ → ‖amp τ‖ ≤ M0 * c⁻¹) →
      (∀ {a b : ℝ}, 0 < a → a ≤ b → ∫ x in Icc a b, ‖deriv amp x‖ ≤ M0 * c⁻¹) →
      (∀ {a : ℝ}, 1 / 16 ≤ a →
        (∀ {τ : ℝ}, a ≤ τ → ‖amp τ‖ ≤ M1 * c⁻¹ * Real.exp (-(π / 2 * a))) ∧
        (∀ {T : ℝ}, a ≤ T → ∫ x in Icc a T, ‖deriv amp x‖ ≤ M1 * c⁻¹ * Real.exp (-(π / 2 * a)))) →
      ‖∫ τ in Ioi (0 : ℝ), amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
        C_lg * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) ∧
      (1 / 4 * Real.log c ≤ L →
        ‖∫ τ in Ioi (0 : ℝ), amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
          C_lg * c ^ (-2 : ℝ) * L⁻¹) := by
  set K9 : ℝ := (Nat.factorial 9 : ℝ) * 2 ^ 9
  have hK9_0 : 0 ≤ K9 := by positivity
  set C_tail : ℝ := 192 * M1 + 72 * M1 + 256 * M1 * Real.sqrt 3
  have hCt_0 : 0 ≤ C_tail := by positivity
  set C_lg : ℝ := max (12 * M0 + C_tail * (4 * K9)) (12 * M0 + C_tail * (2 * K9))
  refine ⟨C_lg, by positivity, fun {c L amp} hc1 hL2 hCD hInt hM_glob hV_glob hME => ?_⟩
  have hcpos : 0 < c := by linarith
  have hL_pos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  set f : ℝ → ℂ := fun τ => amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))
  set s1 : ℝ := tau0 (L / 2)
  set s2 : ℝ := 3 / 4 * tau0 L
  set s3 : ℝ := 3 / 2 * tau0 L
  obtain ⟨hs1_16, hs1_s2⟩ := s1_le_s2 hL2
  have hs1_pos : 0 < s1 := lt_of_lt_of_le (by norm_num) hs1_16
  have hs2_pos : 0 < s2 := lt_of_lt_of_le hs1_pos hs1_s2
  have htau_pos : 0 < tau0 L := tau0_pos hL_pos
  have hs2_s3 : s2 ≤ s3 := by dsimp [s2, s3]; linarith
  have hs3_pos : 0 < s3 := lt_of_lt_of_le hs2_pos hs2_s3
  have hs1_s3 : s1 ≤ s3 := hs1_s2.trans hs2_s3
  have hsplit_s1 : ∫ τ in Ioi (0 : ℝ), f τ =
      (∫ τ in Ioc 0 s1, f τ) + ∫ τ in Ioi s1, f τ := by
    have hU : Ioc (0 : ℝ) s1 ∪ Ioi s1 = Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi hs1_pos.le
    have hdisj : Disjoint (Ioc (0 : ℝ) s1) (Ioi s1) := Set.Ioc_disjoint_Ioi le_rfl
    rw [← setIntegral_union hdisj measurableSet_Ioi (hInt.mono_set Ioc_subset_Ioi_self)
      (hInt.mono_set (Ioi_subset_Ioi hs1_pos.le)), hU]
  have hInt_s1 : IntegrableOn f (Ioi s1) := hInt.mono_set (Ioi_subset_Ioi hs1_pos.le)
  have hsplit_s2 := integral_Ioi_eq_interval_add_Ioi hs1_s2 hInt_s1
  have hInt_s2 : IntegrableOn f (Ioi s2) := hInt_s1.mono_set (Ioi_subset_Ioi hs1_s2)
  have hsplit_s3 := integral_Ioi_eq_interval_add_Ioi hs2_s3 hInt_s2
  have hInt_s3 : IntegrableOn f (Ioi s3) := hInt_s2.mono_set (Ioi_subset_Ioi hs2_s3)
  have hc2_eq : c⁻¹ / c = c ^ (-2 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
  have h0_bd : ‖∫ τ in Ioc 0 s1, f τ‖ ≤ 12 * M0 * c ^ (-2 : ℝ) * L⁻¹ := by
    have hv := vdc1_Ioc_edgePhi hs1_pos hcpos (by linarith : 0 < L / 2) hCD
      (hInt.mono_set Ioc_subset_Ioi_self)
      (fun x hx => by
        rw [edgePhiDeriv_eq_sub_hankelEdgeM hx.1.le]
        have hm_le : hankelEdgeM x ≤ L / 2 := by
          have := hankelEdgeM_strictMonoOn.monotoneOn hx.1.le (mem_Ici.mpr hs1_pos.le) hx.2
          rwa [hankelEdgeM_tau0 (by linarith : 0 < L / 2)] at this
        have : L / 2 ≤ L - hankelEdgeM x := by linarith
        exact this.trans (le_abs_self _))
      (fun x hx => hM_glob hx.1)
      (fun a ha hab => hV_glob ha hab)
    refine hv.trans_eq ?_
    calc 3 * (M0 * c⁻¹ + M0 * c⁻¹) / (c * (L / 2)) = 12 * M0 * (c⁻¹ / c) * L⁻¹ := by
          field_simp [hcpos.ne', hL_pos.ne']; ring
      _ = 12 * M0 * c ^ (-2 : ℝ) * L⁻¹ := by rw [hc2_eq]
  obtain ⟨hME_s1, hVE_s1⟩ := hME hs1_16
  have hs2_16 : 1 / 16 ≤ s2 := hs1_16.trans hs1_s2
  obtain ⟨hME_s2, hVE_s2⟩ := hME hs2_16
  have hs3_16 : 1 / 16 ≤ s3 := hs2_16.trans hs2_s3
  obtain ⟨hME_s3, hVE_s3⟩ := hME hs3_16
  have hexp_s3_s1 : Real.exp (-(π / 2 * s3)) ≤ Real.exp (-(π / 2 * s1)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hs1_s3 (by positivity)))
  have h1_bd : ‖∫ τ in s1..s2, f τ‖ ≤ 192 * M1 * c ^ (-2 : ℝ) * Real.exp (-(π / 2 * s1)) := by
    have hv := vdc1_Icc_edgePhi_sign (L := L) hs1_s2 hs1_pos hcpos (by norm_num : (0 : ℝ) < 1 / 32)
      (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
      hCD
      (fun x hx => by
        simpa only [one_mul, edgePhiDeriv_eq_sub_hankelEdgeM (le_trans hs1_pos.le hx.1)] using
          (hankelEdgeM_diff_large_inner hL1 (le_trans hs1_pos.le hx.1) hx.2).trans (le_abs_self _))
      (fun x hx => by simpa only [one_mul] using hME_s1 hx.1)
      (by simpa only [one_mul] using hVE_s1 hs1_s2)
    have hv' : ‖∫ τ in s1..s2, f τ‖ ≤
        3 * (M1 * c⁻¹ * Real.exp (-(π / 2 * s1)) + M1 * c⁻¹ * Real.exp (-(π / 2 * s1))) / (c * (1 / 32)) := by
      simpa only [one_mul] using hv
    refine hv'.trans_eq ?_
    calc 3 * (M1 * c⁻¹ * Real.exp (-(π / 2 * s1)) + M1 * c⁻¹ * Real.exp (-(π / 2 * s1))) / (c * (1 / 32))
        = 192 * M1 * (c⁻¹ / c) * Real.exp (-(π / 2 * s1)) := by ring
      _ = 192 * M1 * c ^ (-2 : ℝ) * Real.exp (-(π / 2 * s1)) := by rw [hc2_eq]
  have h3_bd : ‖∫ τ in Ioi s3, f τ‖ ≤ 72 * M1 * c ^ (-2 : ℝ) * Real.exp (-(π / 2 * s1)) := by
    have hv := vdc1_Ioi_edgePhi_pos hs3_pos hcpos (by norm_num : (0 : ℝ) < 1 / 12) hCD hInt_s3
      (fun x hx => by
        rw [edgePhiDeriv_eq_sub_hankelEdgeM (le_trans hs3_pos.le hx), abs_sub_comm]
        exact (hankelEdgeM_diff_large_outer hL1 hx).trans (le_abs_self _))
      (fun x hx => hME_s3 hx)
      (fun T hT => hVE_s3 hT)
    refine hv.trans ?_
    calc 3 * (M1 * c⁻¹ * Real.exp (-(π / 2 * s3)) + M1 * c⁻¹ * Real.exp (-(π / 2 * s3))) / (c * (1 / 12))
        = 72 * M1 * (c⁻¹ / c) * Real.exp (-(π / 2 * s3)) := by ring
      _ ≤ 72 * M1 * c ^ (-2 : ℝ) * Real.exp (-(π / 2 * s1)) := by rw [hc2_eq]; gcongr
  have h2_bd : ‖∫ τ in s2..s3, f τ‖ ≤ 256 * M1 * Real.sqrt 3 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) :=
    rightTail_I1_large_s23 hM1 hc1 hL2 hCD hME_s2 hVE_s2
  -- Combine all 4 pieces
  rw [hsplit_s1, hsplit_s2, hsplit_s3]
  have hnorm_total : ‖∫ τ in Ioc 0 s1, f τ‖ + ‖∫ τ in s1..s2, f τ‖ + ‖∫ τ in s2..s3, f τ‖ + ‖∫ τ in Ioi s3, f τ‖ ≤
      12 * M0 * c ^ (-2 : ℝ) * L⁻¹ + C_tail * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) := by
    have hc2_32 : c ^ (-2 : ℝ) ≤ c ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hsum_tail : ‖∫ τ in s1..s2, f τ‖ + ‖∫ τ in s2..s3, f τ‖ + ‖∫ τ in Ioi s3, f τ‖ ≤
        C_tail * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) := by
      calc ‖∫ τ in s1..s2, f τ‖ + ‖∫ τ in s2..s3, f τ‖ + ‖∫ τ in Ioi s3, f τ‖
          ≤ 192 * M1 * c ^ (-2 : ℝ) * Real.exp (-(π / 2 * s1)) +
              256 * M1 * Real.sqrt 3 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) +
              72 * M1 * c ^ (-2 : ℝ) * Real.exp (-(π / 2 * s1)) :=
            add_le_add (add_le_add h1_bd h2_bd) h3_bd
        _ ≤ 192 * M1 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) +
              256 * M1 * Real.sqrt 3 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) +
              72 * M1 * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) := by gcongr
        _ = C_tail * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) := by
            dsimp only [C_tail]; ring
    linarith [h0_bd, hsum_tail]
  have hsum_le : ‖(∫ τ in Ioc 0 s1, f τ) + ((∫ τ in s1..s2, f τ) + ((∫ τ in s2..s3, f τ) + ∫ τ in Ioi s3, f τ))‖ ≤
      12 * M0 * c ^ (-2 : ℝ) * L⁻¹ + C_tail * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) :=
    (norm_sum4_le _ _ _ _).trans hnorm_total
  have hexp_bds := exp_neg_half_tau0_half_bounds hL2
  refine ⟨?_, ?_⟩
  · have hc2_32 : c ^ (-2 : ℝ) ≤ c ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hL_inv_12 : L⁻¹ ≤ L ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one L]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have ht1_m : 12 * M0 * c ^ (-2 : ℝ) * L⁻¹ ≤ 12 * M0 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by
      have h1 : 12 * M0 * c ^ (-2 : ℝ) ≤ 12 * M0 * c ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hc2_32 (by positivity)
      exact mul_le_mul h1 hL_inv_12 (by positivity) (by positivity)
    have ht2_m : C_tail * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) ≤
        C_tail * c ^ (-(3 / 2 : ℝ)) * (4 * K9 * L ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hexp_bds.1 (mul_nonneg hCt_0 (Real.rpow_nonneg hcpos.le _))
    have ht_all : 12 * M0 * c ^ (-2 : ℝ) * L⁻¹ + C_tail * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) ≤
        (12 * M0 + C_tail * (4 * K9)) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by
      calc _ ≤ 12 * M0 * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) +
              C_tail * c ^ (-(3 / 2 : ℝ)) * (4 * K9 * L ^ (-(1 / 2 : ℝ))) := add_le_add ht1_m ht2_m
        _ = (12 * M0 + C_tail * (4 * K9)) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by ring
    refine hsum_le.trans (ht_all.trans ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hcpos.le _))
      (Real.rpow_nonneg hL_pos.le _)
  · intro hLc
    have h_e := hexp_bds.2 hc1 hLc
    have hc32_inv : c ^ (-(3 / 2 : ℝ)) * c⁻¹ = c ^ (-2 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_add hcpos, ← Real.rpow_add hcpos]; congr 1; norm_num
    have hc_m12_1 : c ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    have ht2_m1 : C_tail * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) ≤
        C_tail * c ^ (-(3 / 2 : ℝ)) * (2 * K9 * c⁻¹ * L⁻¹) :=
      mul_le_mul_of_nonneg_left h_e (mul_nonneg hCt_0 (Real.rpow_nonneg hcpos.le _))
    have ht2_m2 : C_tail * (2 * K9) * (c ^ (-2 : ℝ) * c ^ (-(1 / 2 : ℝ))) * L⁻¹ ≤
        C_tail * (2 * K9) * (c ^ (-2 : ℝ) * 1) * L⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hc_m12_1 (Real.rpow_nonneg hcpos.le _)) (mul_nonneg hCt_0 (by positivity)))
        (inv_nonneg.mpr hL_pos.le)
    have ht_all : 12 * M0 * c ^ (-2 : ℝ) * L⁻¹ + C_tail * c ^ (-(3 / 2 : ℝ)) * Real.exp (-(π / 2 * s1)) ≤
        (12 * M0 + C_tail * (2 * K9)) * c ^ (-2 : ℝ) * L⁻¹ := by
      calc _ ≤ 12 * M0 * c ^ (-2 : ℝ) * L⁻¹ + C_tail * c ^ (-(3 / 2 : ℝ)) * (2 * K9 * c⁻¹ * L⁻¹) :=
            add_le_add le_rfl ht2_m1
        _ = 12 * M0 * c ^ (-2 : ℝ) * L⁻¹ + C_tail * (2 * K9) * (c ^ (-(3 / 2 : ℝ)) * c⁻¹) * L⁻¹ := by ring
        _ = 12 * M0 * c ^ (-2 : ℝ) * L⁻¹ + C_tail * (2 * K9) * (c ^ (-2 : ℝ) * c ^ (-(1 / 2 : ℝ))) * L⁻¹ := by
            rw [hc32_inv]
        _ ≤ 12 * M0 * c ^ (-2 : ℝ) * L⁻¹ + C_tail * (2 * K9) * (c ^ (-2 : ℝ) * 1) * L⁻¹ :=
            add_le_add le_rfl ht2_m2
        _ = (12 * M0 + C_tail * (2 * K9)) * c ^ (-2 : ℝ) * L⁻¹ := by ring
    refine hsum_le.trans (ht_all.trans ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hcpos.le _))
      (inv_nonneg.mpr hL_pos.le)

/-- **Right-tail IBP error bound** (`fct:warp-asymp` (2)–(4) right-tail bound):
on `Sw * c ^ (-(2 / 3 : ℝ)) ≤ Real.log (π ^ 2 * ξ)`,
1. `≤ C * c ^ (-2 : ℝ) * (Real.log (π ^ 2 * ξ))⁻¹` for `L ≤ 1`,
2. `≤ C * c ^ (-2 : ℝ) * (Real.log (π ^ 2 * ξ)) ^ (-(3 / 2 : ℝ))` for `1 ≤ L`,
3. `≤ C * c ^ (-2 : ℝ) * (Real.log (π ^ 2 * ξ)) ^ (-2 : ℝ)` for `1 / 4 * Real.log c ≤ L` (with `c ≥ c₀ ≥ 32^4`, where `2 ≤ 1 / 4 * Real.log c`). -/
theorem warpRightTailDensity_large_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C Sw c₀ : ℝ, 0 ≤ C ∧ 1 ≤ Sw ∧ 32 ^ 4 ≤ c₀ ∧
      ∀ {ε c ξ : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
        Sw * c ^ (-(2 / 3 : ℝ)) ≤ Real.log (π ^ 2 * ξ) →
        (Real.log (π ^ 2 * ξ) ≤ 1 →
          |warpRightTailDensity h ε c ξ| ≤ C * c ^ (-2 : ℝ) * (Real.log (π ^ 2 * ξ))⁻¹) ∧
        (1 ≤ Real.log (π ^ 2 * ξ) →
          |warpRightTailDensity h ε c ξ| ≤
            C * c ^ (-2 : ℝ) * (Real.log (π ^ 2 * ξ)) ^ (-(3 / 2 : ℝ))) ∧
        (1 / 4 * Real.log c ≤ Real.log (π ^ 2 * ξ) →
          |warpRightTailDensity h ε c ξ| ≤
            C * c ^ (-2 : ℝ) * (Real.log (π ^ 2 * ξ)) ^ (-2 : ℝ)) := by
  obtain ⟨c0N, _, hNc⟩ := fctNcC_eq_fctNc hK4 h
  obtain ⟨c0Ibp, hc0Ibp32, hIbp⟩ := warpRightTail_first_ibp hK4 h
  obtain ⟨CT2, Sw2, c0T2, hCT2_0, hSw2_1, hc0T2_32, hT2⟩ := warpRightTail_term2_bounds hK4 h
  obtain ⟨M0, M_pt, M1, c0MV, hM0, hMp, hM1, hc0MV32, hMV⟩ := warpAmpRight_mv_bounds hK4 h
  obtain ⟨C_sm, hCsm0, hSm⟩ := rightTail_I1_small hM0 hMp
  obtain ⟨C_mid12, hCmid0, hMid12⟩ := rightTail_I1_mid12 hM0
  obtain ⟨C_lg, hClg0, hLg⟩ := rightTail_I1_large hM0 hM1
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨CL1, cL1, _, hL1_bd⟩ := FctSym.physL1_le (fctWarpT1 h) ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).1⟩
  set C_p : ℝ := 4 * |uctCAi| / π
  set C1 : ℝ := max C_sm (max (Real.sqrt 2 * C_mid12) C_lg)
  set C : ℝ := max (C_p * C1 + CT2) (C_p * C_lg + CT2)
  set Sw : ℝ := max Sw2 (2 * |CL1| + 1)
  set c₀ : ℝ := max (max (max c0N c0Ibp) (max c0T2 c0MV)) (max cz (max cL1 ((2 * |CL1| + 1) ^ (3 / 2 : ℝ))))
  refine ⟨C, Sw, c₀, by positivity, le_trans hSw2_1 (le_max_left _ _),
    hc0Ibp32.trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))), ?_⟩
  intro ε c ξ hε hc hξ hL_sw
  have hcw : c0N ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _) |>.trans hc
  have hcIbp : c0Ibp ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _) |>.trans hc
  have hcT2 : c0T2 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _) |>.trans hc
  have hcMV : c0MV ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _) |>.trans hc
  have hcz : cz ≤ c := (le_max_left _ _).trans (le_max_right _ _) |>.trans hc
  have hcL1 : cL1 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _) |>.trans hc
  have hc_cl1 : (2 * |CL1| + 1) ^ (3 / 2 : ℝ) ≤ c :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _) |>.trans hc
  have hc32 : (32 : ℝ) ^ 4 ≤ c := hc0Ibp32.trans hcIbp
  have hcpos : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  set L : ℝ := Real.log (π ^ 2 * ξ)
  have hSw_1 : 1 ≤ Sw := le_trans hSw2_1 (le_max_left _ _)
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_sw
  have hL_sw2 : Sw2 * c ^ (-(2 / 3 : ℝ)) ≤ L := by
    have : Sw2 ≤ Sw := le_max_left _ _
    exact (mul_le_mul_of_nonneg_right this (by positivity)).trans hL_sw
  have hL1_le : |fctWarpL1 h ε c| ≤ |CL1| * c ^ (-(2 / 3 : ℝ)) := by
    rw [← physL1_fctWarpT1 h hcpos]
    exact (hL1_bd ε c hε hcL1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hL1_halfL : |fctWarpL1 h ε c| ≤ L / 2 := by
    have h2 : 2 * |CL1| + 1 ≤ Sw := le_max_right _ _
    have : 2 * |CL1| * c ^ (-(2 / 3 : ℝ)) ≤ Sw * c ^ (-(2 / 3 : ℝ)) := by
      have : 2 * |CL1| ≤ Sw := by linarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  have hL_diff_pos : L / 2 ≤ L - fctWarpL1 h ε c := by
    linarith [(abs_le.mp hL1_halfL).2]
  have hL_ne : L ≠ fctWarpL1 h ε c := by linarith
  obtain ⟨_, hNc_lo, _, _⟩ := hNc ε c hε hcw
  have hIbp_eq := hIbp hε hcIbp hξ hL_ne
  obtain ⟨hCD, hInt, hA0_pt, hA1_pt, hM_glob, hV_glob, hME⟩ := hMV hε hcMV hξ
  set amp := warpAmpRight K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (fctRightTail h ε c)
  have hpref_bd : |(1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - fctWarpL1 h ε c)) * (c ^ (1 / 3 : ℝ) / π)| ≤
      C_p * c ^ (-(1 / 2 : ℝ)) * L⁻¹ := by
    have hNc_inv : 1 / fctNc h ε c ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hL_inv : (L - fctWarpL1 h ε c)⁻¹ ≤ 2 * L⁻¹ := by
      rw [← one_div (L - fctWarpL1 h ε c), div_le_iff₀ (by linarith)]
      calc 1 = 2 * L⁻¹ * (L / 2) := by field_simp [hL_pos.ne']
        _ ≤ 2 * L⁻¹ * (L - fctWarpL1 h ε c) := mul_le_mul_of_nonneg_left hL_diff_pos (by positivity)
    have hc56_13 : c ^ (-(5 / 6 : ℝ)) * c ^ (1 / 3 : ℝ) = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hcpos]; congr 1; norm_num
    have h_mid_bd : |uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - fctWarpL1 h ε c) ≤
        |uctCAi| * c ^ (-(5 / 6 : ℝ)) * (2 * L⁻¹) := by
      rw [div_eq_mul_inv (|uctCAi| * c ^ (-(5 / 6 : ℝ))) _]
      exact mul_le_mul_of_nonneg_left hL_inv (by positivity)
    rw [abs_mul, abs_mul,
      abs_of_nonneg (div_nonneg zero_le_one (by linarith : 0 ≤ fctNc h ε c)),
      abs_of_nonneg (div_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) (by linarith : 0 ≤ L - fctWarpL1 h ε c)),
      abs_of_nonneg (div_nonneg (by positivity) Real.pi_pos.le)]
    calc (1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - fctWarpL1 h ε c)) * (c ^ (1 / 3 : ℝ) / π)
        ≤ 2 * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) * (2 * L⁻¹)) * (c ^ (1 / 3 : ℝ) / π) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hNc_inv h_mid_bd
              (div_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hcpos.le _)) (by linarith)) (by norm_num))
            (div_nonneg (Real.rpow_nonneg hcpos.le _) Real.pi_pos.le)
      _ = (4 * |uctCAi| / π) * (c ^ (-(5 / 6 : ℝ)) * c ^ (1 / 3 : ℝ)) * L⁻¹ := by ring
      _ = C_p * c ^ (-(1 / 2 : ℝ)) * L⁻¹ := by rw [hc56_13]
  have hI1_eq : ‖∫ τ in Ioi (0 : ℝ), mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        fctWarpA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) * fctRightTail h ε c τ‖ =
      ‖∫ τ in Ioi (0 : ℝ), amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ := by
    congr 1; refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    rw [warpAmpRight_eq_integrand _ _ _ _ _ _ hξ]; dsimp only [amp, L]; push_cast; ring
  have ht1_norm : ∀ {B : ℝ}, 0 ≤ B →
      ‖∫ τ in Ioi (0 : ℝ), amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤ B →
      |warpRightTailTerm1 h ε c ξ| ≤ C_p * c ^ (-(1 / 2 : ℝ)) * L⁻¹ * B := by
    intro B hB0 hB
    have hre_bd : |(∫ τ in Ioi (0 : ℝ), mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        fctWarpA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) * fctRightTail h ε c τ).re| ≤ B :=
      (Complex.abs_re_le_norm _).trans (by rwa [hI1_eq])
    unfold warpRightTailTerm1
    rw [← mul_assoc]
    change |(1 / fctNc h ε c * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - fctWarpL1 h ε c)) * (c ^ (1 / 3 : ℝ) / π)) *
        (∫ τ in Ioi (0 : ℝ), mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          fctWarpA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) * fctRightTail h ε c τ).re| ≤ _
    rw [abs_mul]
    exact mul_le_mul hpref_bd hre_bd (abs_nonneg _) (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hcpos.le _)) (inv_nonneg.mpr hL_pos.le))
  have ht2_bds := hT2 hε hcT2 hξ
  have hL_c23 : c ^ (-(2 / 3 : ℝ)) ≤ L := (le_mul_of_one_le_left (by positivity) hSw_1).trans hL_sw
  refine ⟨fun hL_le1 => ?_, fun hL_ge1 => ?_, fun hLc => ?_⟩
  · have h1 := hSm hc1 hL_c23 hL_le1 hCD hInt hA0_pt hA1_pt hM_glob hV_glob
    have ht1 : |warpRightTailTerm1 h ε c ξ| ≤ C_p * C_sm * c ^ (-2 : ℝ) * L⁻¹ := by
      have hc2 : c ^ (-(1 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ)) = c ^ (-2 : ℝ) := by
        rw [← Real.rpow_add hcpos]; congr 1; norm_num
      calc |warpRightTailTerm1 h ε c ξ| ≤ C_p * c ^ (-(1 / 2 : ℝ)) * L⁻¹ * (C_sm * c ^ (-(3 / 2 : ℝ))) :=
            ht1_norm (by positivity) h1
        _ = C_p * C_sm * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ))) * L⁻¹ := by ring
        _ = C_p * C_sm * c ^ (-2 : ℝ) * L⁻¹ := by rw [hc2]
    have ht2 := ht2_bds.1 hL_sw2
    rw [hIbp_eq.2.2]
    have hCp0 : 0 ≤ C_p := by positivity
    have hsm_le : C_p * C_sm + CT2 ≤ C_p * C1 + CT2 :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left C_sm _) hCp0) le_rfl
    have hfin1 : (C_p * C_sm + CT2) * c ^ (-2 : ℝ) * L⁻¹ ≤ (C_p * C1 + CT2) * c ^ (-2 : ℝ) * L⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsm_le (Real.rpow_nonneg hcpos.le _)) (inv_nonneg.mpr hL_pos.le)
    have hfin2 : (C_p * C1 + CT2) * c ^ (-2 : ℝ) * L⁻¹ ≤ C * c ^ (-2 : ℝ) * L⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hcpos.le _)) (inv_nonneg.mpr hL_pos.le)
    calc |warpRightTailTerm1 h ε c ξ + warpRightTailTerm2 h ε c ξ|
        ≤ |warpRightTailTerm1 h ε c ξ| + |warpRightTailTerm2 h ε c ξ| := abs_add_le _ _
      _ ≤ C_p * C_sm * c ^ (-2 : ℝ) * L⁻¹ + CT2 * c ^ (-2 : ℝ) * L⁻¹ := add_le_add ht1 ht2
      _ = (C_p * C_sm + CT2) * c ^ (-2 : ℝ) * L⁻¹ := by ring
      _ ≤ C * c ^ (-2 : ℝ) * L⁻¹ := hfin1.trans hfin2
  · have hL_pow : L⁻¹ * L ^ (-(1 / 2 : ℝ)) = L ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one L, ← Real.rpow_add hL_pos]; congr 1; norm_num
    have hc2 : c ^ (-(1 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ)) = c ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hcpos]; congr 1; norm_num
    have ht1 : |warpRightTailTerm1 h ε c ξ| ≤ C_p * C1 * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by
      rcases le_or_gt L 2 with hL2 | hL2
      · have hm := hMid12 hc1 hL_ge1 hL2 hCD hInt hM_glob hV_glob
        have h1_le : 1 ≤ Real.sqrt 2 * L ^ (-(1 / 2 : ℝ)) := by
          have hsq : L ^ (1 / 2 : ℝ) ≤ Real.sqrt 2 := by
            rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt hL2
          have hmul : L ^ (1 / 2 : ℝ) * L ^ (-(1 / 2 : ℝ)) = 1 := by
            rw [← Real.rpow_add hL_pos]; norm_num
          nlinarith [Real.rpow_pos_of_pos hL_pos (-(1 / 2 : ℝ))]
        have hm' : ‖∫ τ in Ioi (0 : ℝ), amp τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
            (Real.sqrt 2 * C_mid12) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by
          calc _ ≤ C_mid12 * c ^ (-(3 / 2 : ℝ)) := hm
            _ = (C_mid12 * c ^ (-(3 / 2 : ℝ))) * 1 := (mul_one _).symm
            _ ≤ (C_mid12 * c ^ (-(3 / 2 : ℝ))) * (Real.sqrt 2 * L ^ (-(1 / 2 : ℝ))) :=
                mul_le_mul_of_nonneg_left h1_le (by positivity)
            _ = (Real.sqrt 2 * C_mid12) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) := by ring
        calc |warpRightTailTerm1 h ε c ξ| ≤ C_p * c ^ (-(1 / 2 : ℝ)) * L⁻¹ *
              ((Real.sqrt 2 * C_mid12) * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ))) :=
              ht1_norm (by positivity) hm'
          _ = C_p * (Real.sqrt 2 * C_mid12) * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ))) *
                (L⁻¹ * L ^ (-(1 / 2 : ℝ))) := by ring
          _ = C_p * (Real.sqrt 2 * C_mid12) * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by rw [hc2, hL_pow]
          _ ≤ C_p * C1 * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by
              gcongr; exact le_trans (le_max_left _ _) (le_max_right _ _)
      · have hlg := (hLg hc1 hL2.le hCD hInt hM_glob hV_glob hME).1
        calc |warpRightTailTerm1 h ε c ξ| ≤ C_p * c ^ (-(1 / 2 : ℝ)) * L⁻¹ * (C_lg * c ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ))) :=
              ht1_norm (by positivity) hlg
          _ = C_p * C_lg * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ))) * (L⁻¹ * L ^ (-(1 / 2 : ℝ))) := by ring
          _ = C_p * C_lg * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by rw [hc2, hL_pow]
          _ ≤ C_p * C1 * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (le_trans (le_max_right _ _) (le_max_right _ _)) (by positivity))
                (by positivity)) (by positivity)
    have ht2 : |warpRightTailTerm2 h ε c ξ| ≤ CT2 * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by
      have hc52_2 : c ^ (-(5 / 2 : ℝ)) ≤ c ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      have hL2_32 : L ^ (-2 : ℝ) ≤ L ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL_ge1 (by norm_num)
      calc |warpRightTailTerm2 h ε c ξ| ≤ CT2 * c ^ (-(5 / 2 : ℝ)) * L ^ (-2 : ℝ) := ht2_bds.2 hL_ge1
        _ ≤ CT2 * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hc52_2 hCT2_0) hL2_32 (by positivity) (by positivity)
    rw [hIbp_eq.2.2]
    calc |warpRightTailTerm1 h ε c ξ + warpRightTailTerm2 h ε c ξ|
        ≤ |warpRightTailTerm1 h ε c ξ| + |warpRightTailTerm2 h ε c ξ| := abs_add_le _ _
      _ ≤ C_p * C1 * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) + CT2 * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) :=
          add_le_add ht1 ht2
      _ = (C_p * C1 + CT2) * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ C * c ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  · have hL2 : 2 ≤ L := by
      have hc_e8 : (Real.exp 8 : ℝ) ≤ c := by
        have he1 : Real.exp 1 ≤ 2.72 := Real.exp_one_lt_d9.le.trans (by norm_num)
        have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        have he4 : Real.exp 4 = Real.exp 2 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        have he8 : Real.exp 8 = Real.exp 4 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        have h2 : Real.exp 2 ≤ 7.4 := by nlinarith only [he1, he2, (Real.exp_pos 1).le]
        have h4 : Real.exp 4 ≤ 55 := by nlinarith only [h2, he4, (Real.exp_pos 2).le]
        have h8 : Real.exp 8 ≤ 3025 := by nlinarith only [h4, he8, (Real.exp_pos 4).le]
        have hc32' : (32 : ℝ) ^ 4 = 1048576 := by norm_num
        linarith only [h8, hc32', hc32]
      have hlog8 : 8 ≤ Real.log c := by
        rw [← Real.log_exp 8]
        exact Real.log_le_log (Real.exp_pos 8) hc_e8
      linarith only [hLc, hlog8]
    have hL1 : 1 ≤ L := by linarith
    have hlg := (hLg hc1 hL2 hCD hInt hM_glob hV_glob hME).2 hLc
    have hc52 : c ^ (-(1 / 2 : ℝ)) * c ^ (-2 : ℝ) = c ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_add hcpos]; congr 1; norm_num
    have hc52_2 : c ^ (-(5 / 2 : ℝ)) ≤ c ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hL_m2 : L⁻¹ * L⁻¹ = L ^ (-2 : ℝ) := by
      rw [← Real.rpow_neg_one L, ← Real.rpow_add hL_pos]; congr 1; norm_num
    have ht1 : |warpRightTailTerm1 h ε c ξ| ≤ C_p * C_lg * c ^ (-2 : ℝ) * L ^ (-2 : ℝ) := by
      calc |warpRightTailTerm1 h ε c ξ| ≤ C_p * c ^ (-(1 / 2 : ℝ)) * L⁻¹ * (C_lg * c ^ (-2 : ℝ) * L⁻¹) :=
            ht1_norm (by positivity) hlg
        _ = C_p * C_lg * (c ^ (-(1 / 2 : ℝ)) * c ^ (-2 : ℝ)) * (L⁻¹ * L⁻¹) := by ring
        _ = C_p * C_lg * c ^ (-(5 / 2 : ℝ)) * L ^ (-2 : ℝ) := by rw [hc52, hL_m2]
        _ ≤ C_p * C_lg * c ^ (-2 : ℝ) * L ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc52_2 (by positivity)) (by positivity)
    have ht2 : |warpRightTailTerm2 h ε c ξ| ≤ CT2 * c ^ (-2 : ℝ) * L ^ (-2 : ℝ) := by
      calc |warpRightTailTerm2 h ε c ξ| ≤ CT2 * c ^ (-(5 / 2 : ℝ)) * L ^ (-2 : ℝ) := ht2_bds.2 hL1
        _ ≤ CT2 * c ^ (-2 : ℝ) * L ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc52_2 hCT2_0) (by positivity)
    rw [hIbp_eq.2.2]
    calc |warpRightTailTerm1 h ε c ξ + warpRightTailTerm2 h ε c ξ|
        ≤ |warpRightTailTerm1 h ε c ξ| + |warpRightTailTerm2 h ε c ξ| := abs_add_le _ _
      _ ≤ C_p * C_lg * c ^ (-2 : ℝ) * L ^ (-2 : ℝ) + CT2 * c ^ (-2 : ℝ) * L ^ (-2 : ℝ) := add_le_add ht1 ht2
      _ = (C_p * C_lg + CT2) * c ^ (-2 : ℝ) * L ^ (-2 : ℝ) := by ring
      _ ≤ C * c ^ (-2 : ℝ) * L ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)

/-- info: 'FormalResearch.SignUncertainty.warpRightTailDensity_large_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpRightTailDensity_large_bound

end FormalResearch.SignUncertainty


