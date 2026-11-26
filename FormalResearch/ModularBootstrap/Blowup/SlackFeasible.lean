module

public import FormalResearch.ModularBootstrap.FixedWeightTip.PropositionP
public import FormalResearch.ModularBootstrap.Blowup.NormLimitCore

/-!
# Proposition P / Lemma Q for tests with vacuum slack (sign-independent steps of `ft:PP`)

Source: `CFT/modular_bootstrap/paper/blowup_limit.tex`, proof of Lemma BL-N (`bl:norm`): "Steps 1-3
of the proof of `ft:PP` use only (P0)-(P2), not the vacuum sign".  `FixedWeightTip.proposition_P_of_problem`
and `lemmaQ_general_part3` are stated for weakly feasible tests (`g_vac ≥ 0`).  This file redoes the
three places where the vacuum sign enters (the position `Δ(A²) < T` of the threshold in the chart,
the left-lobe mass `1/2`, the truncated total mass) for a test with *normalised vacuum slack*
`∫₀^∞ g V ≤ η M[g]`, `η ≥ 0`, and packages the output as `DensityHyp` of `NormLimitCore`.

* `IsSlackFeasible prob a T η g`: `TestClass`, `0 < M[g]`, `∫₀^∞ g V ≤ η M[g]`, `g ≥ 0` on `[T, ∞)`
  (`η = 0` is weak feasibility with `M[g] > 0`).
* `neg_mass_ge_slack`: the negative part of `g V` on `[0, T]` has mass `≥ (M - s)/2`.
* `densityHyp_of_slack`: for `c' ≥ c_S`, `η ≤ 1/4` and the interior threshold `T < Δ(-A²)`,
  `psiTilde prob c' g` satisfies `DensityHyp` with `δ = δ_lobe + η`, where `δ_lobe` is the far-lobe
  mass, `≤ C e^{-κ c'}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Blowup

open FormalResearch.ModularBootstrap Crossing PoissonJensen WeightAxioms TipFront ConcreteBootstrap
  FixedWeightTip FormalResearch.Special

/-- A test with normalised vacuum slack `η`: `∫₀^∞ g V ≤ η M[g]`, nonnegative on `[T, ∞)`. -/
def IsSlackFeasible (prob : FixedWeightProblem) (a T η : ℝ) (g : ℝ → ℝ) : Prop :=
  TestClass prob a g ∧ 0 < prob.cardyNorm a g ∧
    (∫ t in Ioi (0 : ℝ), g t * prob.cardyV a t) ≤ η * prob.cardyNorm a g ∧ ∀ t ≥ T, 0 ≤ g t

/-- The negative part of `g V` on `[0, T]` carries at least `(M - s)/2`, when
`∫₀^∞ g V ≤ s` and `g ≥ 0` on `[T, ∞)`. -/
lemma neg_mass_ge_slack {prob : FixedWeightProblem} {a T s : ℝ} {g : ℝ → ℝ}
    (hg : TestClass prob a g) (hT : 0 ≤ T)
    (htail : ∀ t ≥ T, 0 ≤ g t) (hs : (∫ t in Ioi (0 : ℝ), g t * prob.cardyV a t) ≤ s) :
    (prob.cardyNorm a g - s) / 2 ≤ ∫ t in (0 : ℝ)..T, max 0 (-g t) * prob.cardyV a t := by
  have hgv_int : IntegrableOn (fun t => g t * prob.cardyV a t) (Ioi 0) :=
    hg.int_cardy.norm.mono'
      (((hg.cont.mul (continuous_cardyV prob a).continuousOn).mono
        Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
      (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
  have hM_int : IntegrableOn (fun t => |g t| * prob.cardyV a t) (Ioi 0) := hg.int_cardy
  have hgv_int_0T : IntervalIntegrable (fun t => g t * prob.cardyV a t) volume 0 T :=
    ((hg.cont.mul (continuous_cardyV prob a).continuousOn).mono
      Icc_subset_Ici_self).intervalIntegrable_of_Icc hT
  have hM_int_0T : IntervalIntegrable (fun t => |g t| * prob.cardyV a t) volume 0 T :=
    ((hg.cont.abs.mul (continuous_cardyV prob a).continuousOn).mono
      Icc_subset_Ici_self).intervalIntegrable_of_Icc hT
  have htail_tail : ∫ t in Ioi T, g t * prob.cardyV a t =
      ∫ t in Ioi T, |g t| * prob.cardyV a t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      rw [abs_of_nonneg (htail t (mem_Ioi.mp ht).le)]
  have hsplit_g : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV a t =
      (∫ t in (0 : ℝ)..T, g t * prob.cardyV a t) + ∫ t in Ioi T, g t * prob.cardyV a t := by
    rw [intervalIntegral.integral_of_le hT, ← setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hgv_int.mono_set Ioc_subset_Ioi_self)
      (hgv_int.mono_set (Ioi_subset_Ioi hT)), Ioc_union_Ioi_eq_Ioi hT]
  have hsplit_M : prob.cardyNorm a g =
      (∫ t in (0 : ℝ)..T, |g t| * prob.cardyV a t) + ∫ t in Ioi T, |g t| * prob.cardyV a t := by
    rw [intervalIntegral.integral_of_le hT, ← setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi (hM_int.mono_set Ioc_subset_Ioi_self)
      (hM_int.mono_set (Ioi_subset_Ioi hT)), Ioc_union_Ioi_eq_Ioi hT]
    rfl
  have hid_pt : ∀ t ∈ Icc (0 : ℝ) T,
      (|g t| - g t) / 2 * prob.cardyV a t = max 0 (-g t) * prob.cardyV a t := fun t _ => by
    rcases le_total (g t) 0 with h | h
    · rw [max_eq_right (neg_nonneg.mpr h), abs_of_nonpos h]; ring
    · rw [max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h]; ring
  have hid_int : (∫ t in (0 : ℝ)..T, (|g t| * prob.cardyV a t - g t * prob.cardyV a t) / 2) =
      ∫ t in (0 : ℝ)..T, max 0 (-g t) * prob.cardyV a t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hT] at ht
    have := hid_pt t ht
    linarith
  have hid_val : (∫ t in (0 : ℝ)..T, (|g t| * prob.cardyV a t - g t * prob.cardyV a t) / 2) =
      ((∫ t in (0 : ℝ)..T, |g t| * prob.cardyV a t) -
        ∫ t in (0 : ℝ)..T, g t * prob.cardyV a t) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hM_int_0T hgv_int_0T]
  linarith

/-- Interior chart placement of the threshold (copy of the private `chartUT_mem_Icc_of_between`). -/
lemma chartUT_mem_Icc_of_between' {r_1 c' T : ℝ} (hr1 : 0 < r_1) (hc' : 0 < c')
    (hlo : virasoroDeltaChart c' (chartAC r_1 c' ^ 2) ≤ T)
    (hhi : T ≤ virasoroDeltaChart c' (-(chartAC r_1 c' ^ 2))) :
    chartUT c' T ∈ Icc (-(chartAC r_1 c' ^ 2)) (chartAC r_1 c' ^ 2) ∧
      virasoroDeltaChart c' (chartUT c' T) = T := by
  have hanti := virasoroDeltaChart_strictAnti hc'
  have hA2_le := chartAC_sq_le_virasoroAC_sq hr1 hc'.le
  have hsub : Icc (-(chartAC r_1 c' ^ 2)) (chartAC r_1 c' ^ 2) ⊆
      Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) := fun u hu =>
    ⟨by linarith [hu.1], hu.2.trans hA2_le⟩
  have hcont : ContinuousOn (virasoroDeltaChart c')
      (Icc (-(chartAC r_1 c' ^ 2)) (chartAC r_1 c' ^ 2)) := fun u hu =>
    (virasoroDeltaChart_hasDerivAt hc' (abs_le.mpr (hsub hu))).continuousAt.continuousWithinAt
  have himg := intermediate_value_Icc' (show -(chartAC r_1 c' ^ 2) ≤ chartAC r_1 c' ^ 2 by
      linarith [sq_nonneg (chartAC r_1 c')]) hcont ⟨hlo, hhi⟩
  obtain ⟨u, hu_mem, hu_eq⟩ := himg
  have hu_abs : |u| ≤ virasoroAC c' ^ 2 := abs_le.mpr (hsub hu_mem)
  have hu_eq' : chartUT c' T = u := by
    unfold chartUT
    rw [← hu_eq]
    exact virasoroUChart_deltaChart hc' hu_abs
  rw [hu_eq']
  exact ⟨hu_mem, hu_eq⟩

/-- Continuity of `Δ'` on a window (copy of a private lemma of `PropositionP`). -/
lemma continuousOn_deriv_virasoroDeltaChart' {c' a b : ℝ} (hc' : 0 < c')
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b) :
    ContinuousOn (deriv (virasoroDeltaChart c')) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  intro u hu
  let x : ℝ := u * c' ^ (-(2 / 3 : ℝ))
  have hx_open : |x| < virasoroRUInf := by
    have h1 := virasoro_u_mem_open_ball hc' (u := (u : ℂ))
      (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu_mem u hu)
    have hux : ((u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) = ((x : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
    rwa [hux, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at h1
  have hderiv_eq : EqOn (deriv (virasoroDeltaChart c'))
      (fun t : ℝ => c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re)
      (Icc a b) := fun t ht =>
    (virasoroDeltaChart_hasDerivAt hc' (hu_mem t ht)).deriv
  have hcont_rhs : ContinuousOn
      (fun t : ℝ => c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re)
      (Icc a b) := fun t ht => by
    have htu : (((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) ∈ ball (0 : ℂ) virasoroRUInf := by
      have h1 := virasoro_u_mem_open_ball hc' (u := (t : ℂ))
        (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu_mem t ht)
      rwa [← Complex.ofReal_mul] at h1
    have hc_at : ContinuousAt (deriv virasoroXiInf) (((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) :=
      (virasoroXiInf_an.deriv _ htu).continuousAt
    have hlin : Continuous (fun s : ℝ => (((s * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)
    have hcomp : ContinuousAt
        (fun s : ℝ => (deriv virasoroXiInf ((s * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re) t :=
      Complex.continuous_re.continuousAt.comp
        (hc_at.comp (f := fun s : ℝ => (((s * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))) hlin.continuousAt)
    exact (continuousAt_const.mul hcomp).continuousWithinAt
  exact (hcont_rhs.congr hderiv_eq) u hu

/-- **`Proposition P` / Lemma Q for slack tests.**  For `c' ≥ c_S`, a test with normalised vacuum slack
`η ≤ 1/4` and interior threshold `T < Δ(-A²)` has a transported density `psiTilde prob c' g`
satisfying `DensityHyp` with `δ = δ_lobe + η`, where `δ_lobe ≤ C_gap e^{-κ_gap c'}`; moreover
`Δ(A²) < T`, and the sign of `g` at `Δ(u)` is the sign of `Re ψ̃(u)` for `|u| ≤ A²`. -/
theorem densityHyp_of_slack {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ c_S C₀ C_gap κ_gap : ℝ, D.c₀ ≤ c_S ∧ 0 < C₀ ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' T η : ℝ} {g : ℝ → ℝ}, c_S ≤ c' → 0 ≤ η → η ≤ 1 / 4 →
        IsSlackFeasible prob (c' / 12) T η g →
        T < virasoroDeltaChart c' (-(chartAC D.r_1 c' ^ 2)) →
        deltaLobe prob D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
        DensityHyp C₀ (chartAC D.r_1 c' ^ 2) (generalSigma D.p_e c')
          (deltaLobe prob D.r_1 c' g + η) (psiTilde prob c' g) (chartUT c' T) ∧
        virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) < T ∧
        ∀ u : ℝ, |u| ≤ chartAC D.r_1 c' ^ 2 →
          (0 ≤ g (virasoroDeltaChart c' u) ↔ 0 ≤ (psiTilde prob c' g (u : ℂ)).re) := by
  obtain ⟨c_gap, C_gap, κ_gap, hc_gap, hC_gap, hκ_gap, hpart1, -⟩ := deltaLobe_gap_general D
  obtain ⟨c₂, C₀, hc₂, hC₀, hpart2⟩ := lemmaQ_general_part2 D
  let c_S : ℝ := max (max c_gap c₂) ((Real.log (4 * C_gap) + 1) / κ_gap)
  refine ⟨c_S, C₀, C_gap, κ_gap, hc_gap.trans ((le_max_left _ _).trans (le_max_left _ _)), hC₀,
    hC_gap, hκ_gap, ?_⟩
  intro c' T η g hc' hη0 hη hsf hTint
  have hc'_gap : c_gap ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hc'_2 : c₂ ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hlog : (Real.log (4 * C_gap) + 1) / κ_gap ≤ c' := (le_max_right _ _).trans hc'
  have hc'_c₀ : D.c₀ ≤ c' := hc_gap.trans hc'_gap
  have hc'_pos : 0 < c' := D.hc₀_pos.trans_le hc'_c₀
  obtain ⟨hg, hM_pos, hvac, htail⟩ := hsf
  have hV_nonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c' / 12) t := fun ht =>
    D.cardyV_nonneg hc'_c₀ ht
  have hdl : deltaLobe prob D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') :=
    hpart1 hc'_gap hg hM_pos
  have hdl_lt : deltaLobe prob D.r_1 c' g < 1 / 4 := by
    have hmul : Real.log (4 * C_gap) + 1 ≤ κ_gap * c' := by
      linarith [(div_le_iff₀ hκ_gap).mp hlog]
    have hneg : -κ_gap * c' < -Real.log (4 * C_gap) := by linarith
    have hexp : Real.exp (-κ_gap * c') < (4 * C_gap)⁻¹ := by
      calc Real.exp (-κ_gap * c') < Real.exp (-Real.log (4 * C_gap)) := Real.exp_lt_exp.mpr hneg
        _ = (4 * C_gap)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
    calc deltaLobe prob D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') := hdl
      _ < C_gap * (4 * C_gap)⁻¹ := mul_lt_mul_of_pos_left hexp hC_gap
      _ = 1 / 4 := by field_simp [hC_gap.ne']
  have hA2_nn : 0 ≤ chartAC D.r_1 c' ^ 2 := sq_nonneg _
  have hA2_le_vir : chartAC D.r_1 c' ^ 2 ≤ virasoroAC c' ^ 2 :=
    chartAC_sq_le_virasoroAC_sq D.hr1_pos hc'_pos.le
  have hΔ_pos : 0 < virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) :=
    virasoroDeltaChart_pos hc'_pos
      (chart_real_abs_le_virasoro D.hr1_pos hc'_pos (by rw [abs_of_nonneg hA2_nn]))
  -- the threshold lies below the lobe edge in `t`
  have hT_gt : virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) < T := by
    by_contra hle
    push Not at hle
    let T' : ℝ := max 0 T
    have hT'_nn : 0 ≤ T' := le_max_left _ _
    have hT'_le : T' ≤ virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) := max_le hΔ_pos.le hle
    have htail' : ∀ t ≥ T', 0 ≤ g t := fun t ht => htail t ((le_max_right 0 T).trans ht)
    have hhalf := neg_mass_ge_slack hg hT'_nn htail' hvac
    have h1 : ∫ t in (0 : ℝ)..T', max 0 (-g t) * prob.cardyV (c' / 12) t ≤
        ∫ t in (0 : ℝ)..T', |g t| * prob.cardyV (c' / 12) t := by
      have hc1 : ContinuousOn (fun t : ℝ => max 0 (-g t) * prob.cardyV (c' / 12) t) (Icc 0 T') :=
        ((ContinuousOn.sup continuousOn_const hg.cont.neg).mul
          (continuous_cardyV prob (c' / 12)).continuousOn).mono Icc_subset_Ici_self
      have hc2 : ContinuousOn (fun t : ℝ => |g t| * prob.cardyV (c' / 12) t) (Icc 0 T') :=
        (hg.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono Icc_subset_Ici_self
      refine intervalIntegral.integral_mono_on hT'_nn (hc1.intervalIntegrable_of_Icc hT'_nn)
        (hc2.intervalIntegrable_of_Icc hT'_nn) fun t ht => ?_
      exact mul_le_mul_of_nonneg_right (max_le (abs_nonneg _) (neg_le_abs _)) (hV_nonneg ht.1)
    have h2 : ∫ t in (0 : ℝ)..T', |g t| * prob.cardyV (c' / 12) t ≤
        ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2)),
          |g t| * prob.cardyV (c' / 12) t := by
      rw [intervalIntegral.integral_of_le hT'_nn, intervalIntegral.integral_of_le hΔ_pos.le]
      refine setIntegral_mono_set (hg.int_cardy.mono_set Ioc_subset_Ioi_self) ?_
        (Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hT'_le⟩)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (abs_nonneg _) (hV_nonneg ht.1.le)
    have h3 : ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2)),
        |g t| * prob.cardyV (c' / 12) t =
        prob.cardyNorm (c' / 12) g * deltaLobe prob D.r_1 c' g := by
      unfold deltaLobe
      field_simp
    have hM := hM_pos
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hη), hdl_lt, hM]
  obtain ⟨huT_mem, huT_eq⟩ := chartUT_mem_Icc_of_between' D.hr1_pos hc'_pos hT_gt.le hTint.le
  obtain ⟨han, hsign, henv⟩ := hpart2 hc'_2 hg hM_pos
  refine ⟨hdl, ?_, hT_gt, fun u hu => (hsign u hu).2⟩
  have hu_vir : ∀ u : ℝ, |u| ≤ chartAC D.r_1 c' ^ 2 → |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    hu.trans hA2_le_vir
  have hanti := virasoroDeltaChart_strictAnti hc'_pos
  have hnonneg : ∀ x ∈ Icc (-(chartAC D.r_1 c' ^ 2)) (chartAC D.r_1 c' ^ 2),
      x ≤ chartUT c' T → 0 ≤ (psiTilde prob c' g (x : ℂ)).re := by
    intro x hx hxT
    have hT_le : T ≤ virasoroDeltaChart c' x := by
      rw [← huT_eq]
      exact hanti.antitoneOn
        ⟨by linarith [hx.1, hA2_le_vir], (hxT.trans huT_mem.2).trans hA2_le_vir⟩
        ⟨by linarith [huT_mem.1, hA2_le_vir], huT_mem.2.trans hA2_le_vir⟩ hxT
    exact (hsign x (abs_le.mpr hx)).2.mp (htail _ hT_le)
  have hgv_int : IntegrableOn (fun t => g t * prob.cardyV (c' / 12) t) (Ioi 0) :=
    hg.int_cardy.norm.mono'
      (((hg.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
        Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
      (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
  have hT_nn : 0 ≤ T := (hΔ_pos.trans hT_gt).le
  refine ⟨han.mono (closedBall_chartAC_subset_psiDom D.hr1_pos hc'_pos),
    fun x hx => (hsign x (abs_le.mpr hx)).1, fun u hu hcut => henv u hu hcut, hnonneg, ?_, ?_, ?_⟩
  · -- `L¹` mass
    rw [psiTilde_norm_integral_eq prob hc'_pos hV_nonneg hg hM_pos
      (by linarith) hA2_le_vir (by linarith)]
    have hΔ_hi : virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) ≤
        virasoroDeltaChart c' (-(chartAC D.r_1 c' ^ 2)) :=
      hanti.antitoneOn
        (a := -(chartAC D.r_1 c' ^ 2)) (b := chartAC D.r_1 c' ^ 2)
        (Set.mem_Icc.mpr ⟨by linarith [hA2_le_vir, hA2_nn], by linarith [hA2_le_vir, hA2_nn]⟩)
        (Set.mem_Icc.mpr ⟨by linarith [hA2_le_vir, hA2_nn], hA2_le_vir⟩)
        (by linarith [hA2_nn])
    have hint_le : ∫ t in (virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2))..
          (virasoroDeltaChart c' (-(chartAC D.r_1 c' ^ 2))),
          |g t| * prob.cardyV (c' / 12) t ≤ prob.cardyNorm (c' / 12) g := by
      rw [intervalIntegral.integral_of_le hΔ_hi]
      change ∫ t in Ioc (virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2))
          (virasoroDeltaChart c' (-(chartAC D.r_1 c' ^ 2))),
          |g t| * prob.cardyV (c' / 12) t ≤
        ∫ t in Ioi (0 : ℝ), |g t| * prob.cardyV (c' / 12) t
      refine setIntegral_mono_set hg.int_cardy ?_
        (Eventually.of_forall fun t ht => hΔ_pos.trans ht.1)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (abs_nonneg _) (hV_nonneg ht.le)
    calc (prob.cardyNorm (c' / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2))..
            (virasoroDeltaChart c' (-(chartAC D.r_1 c' ^ 2))),
            |g t| * prob.cardyV (c' / 12) t
        ≤ (prob.cardyNorm (c' / 12) g)⁻¹ * prob.cardyNorm (c' / 12) g :=
          mul_le_mul_of_nonneg_left hint_le (inv_nonneg.mpr hM_pos.le)
      _ = 1 := inv_mul_cancel₀ hM_pos.ne'
  · -- left-lobe negative mass
    set t_lo := virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) with ht_lo
    have hu_mem : ∀ u ∈ Icc (chartUT c' T) (chartAC D.r_1 c' ^ 2), |u| ≤ virasoroAC c' ^ 2 :=
      fun u hu => chart_real_abs_le_virasoro D.hr1_pos hc'_pos
        (abs_le.mpr ⟨huT_mem.1.trans hu.1, hu.2⟩)
    have hneg_eq : ∫ u in (chartUT c' T)..(chartAC D.r_1 c' ^ 2),
          max 0 (-(psiTilde prob c' g (u : ℂ)).re) =
        (prob.cardyNorm (c' / 12) g)⁻¹ *
          ∫ t in t_lo..T, max 0 (-g t) * prob.cardyV (c' / 12) t := by
      have h1 : ∫ u in (chartUT c' T)..(chartAC D.r_1 c' ^ 2),
            max 0 (-(psiTilde prob c' g (u : ℂ)).re) =
          -((prob.cardyNorm (c' / 12) g)⁻¹ *
            ∫ u in (chartUT c' T)..(chartAC D.r_1 c' ^ 2),
              (max 0 (-g (virasoroDeltaChart c' u)) *
                prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
              deriv (virasoroDeltaChart c') u) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_congr fun u hu => ?_
        rw [Set.uIcc_of_le huT_mem.2] at hu
        have hua := hu_mem u hu
        have hder_le := virasoroDeltaChart_deriv_le hc'_pos (abs_le.mp hua)
        have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
          have := mul_pos (half_pos cStar_pos) (Real.rpow_pos_of_pos hc'_pos (1 / 3 : ℝ))
          linarith
        have ht_pos : 0 < virasoroDeltaChart c' u := virasoroDeltaChart_pos hc'_pos hua
        have hV_nn : 0 ≤ prob.cardyV (c' / 12) (virasoroDeltaChart c' u) := hV_nonneg ht_pos.le
        have hfac_nn : 0 ≤ (prob.cardyNorm (c' / 12) g)⁻¹ *
            (-(deriv (virasoroDeltaChart c') u)) *
            prob.cardyV (c' / 12) (virasoroDeltaChart c' u) := by positivity
        rw [psiTilde_re_ofReal prob hc'_pos hg hua]
        have hprod : -((prob.cardyNorm (c' / 12) g)⁻¹ *
              (-(deriv (virasoroDeltaChart c') u)) *
              (g (virasoroDeltaChart c' u) *
                prob.cardyV (c' / 12) (virasoroDeltaChart c' u))) =
            ((prob.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
              prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
              (-g (virasoroDeltaChart c' u)) := by ring
        rw [hprod]
        conv_lhs =>
          arg 1
          rw [← mul_zero ((prob.cardyNorm (c' / 12) g)⁻¹ *
            (-(deriv (virasoroDeltaChart c') u)) *
            prob.cardyV (c' / 12) (virasoroDeltaChart c' u))]
        rw [← mul_max_of_nonneg _ _ hfac_nn]
        ring
      have hsub : ∫ u in (chartUT c' T)..(chartAC D.r_1 c' ^ 2),
            (max 0 (-g (virasoroDeltaChart c' u)) *
              prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
            deriv (virasoroDeltaChart c') u =
          ∫ t in T..t_lo, max 0 (-g t) * prob.cardyV (c' / 12) t := by
        have hcont_gV : ContinuousOn
            (fun t : ℝ => max 0 (-g t) * prob.cardyV (c' / 12) t)
            (virasoroDeltaChart c' '' Set.uIcc (chartUT c' T) (chartAC D.r_1 c' ^ 2)) := by
          refine ((ContinuousOn.sup continuousOn_const hg.cont.neg).mul
            (continuous_cardyV prob (c' / 12)).continuousOn).mono ?_
          rintro t ⟨u, hu, rfl⟩
          rw [Set.uIcc_of_le huT_mem.2] at hu
          exact (virasoroDeltaChart_pos hc'_pos (hu_mem u hu)).le
        have hderiv_at : ∀ u ∈ Set.uIcc (chartUT c' T) (chartAC D.r_1 c' ^ 2),
            HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
          rw [Set.uIcc_of_le huT_mem.2] at hu
          have hd := virasoroDeltaChart_hasDerivAt hc'_pos (hu_mem u hu)
          exact hd.deriv ▸ hd
        have hcov := intervalIntegral.integral_comp_mul_deriv' hderiv_at
          (continuousOn_deriv_virasoroDeltaChart' hc'_pos
            (by linarith [huT_mem.1, hA2_le_vir]) hA2_le_vir huT_mem.2)
          hcont_gV
        simpa [huT_eq, t_lo] using hcov
      rw [h1, hsub, intervalIntegral.integral_symm t_lo T]
      ring
    have ht_lo_pos : 0 ≤ t_lo := hΔ_pos.le
    have hM_int_0T : IntervalIntegrable (fun t => |g t| * prob.cardyV (c' / 12) t) volume 0 T :=
      ((hg.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
        Icc_subset_Ici_self).intervalIntegrable_of_Icc hT_nn
    have hhalf_g := neg_mass_ge_slack hg hT_nn htail hvac
    have hneg_0T_split :
        ∫ t in (0 : ℝ)..T, max 0 (-g t) * prob.cardyV (c' / 12) t =
          (∫ t in (0 : ℝ)..t_lo, max 0 (-g t) * prob.cardyV (c' / 12) t) +
          ∫ t in t_lo..T, max 0 (-g t) * prob.cardyV (c' / 12) t := by
      have hcont_neg : ContinuousOn (fun t : ℝ => max 0 (-g t) * prob.cardyV (c' / 12) t) (Ici 0) :=
        (ContinuousOn.sup continuousOn_const hg.cont.neg).mul
          (continuous_cardyV prob (c' / 12)).continuousOn
      exact (intervalIntegral.integral_add_adjacent_intervals
        ((hcont_neg.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos)
        ((hcont_neg.mono (fun t (ht : t ∈ Set.Icc (_ : ℝ) _) => ht_lo_pos.trans ht.1)).intervalIntegrable_of_Icc
          hT_gt.le)).symm
    have hneg_lobe_le : ∫ t in (0 : ℝ)..t_lo, max 0 (-g t) * prob.cardyV (c' / 12) t ≤
        ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t := by
      have hcont_neg : ContinuousOn (fun t : ℝ => max 0 (-g t) * prob.cardyV (c' / 12) t) (Icc 0 t_lo) :=
        ((ContinuousOn.sup continuousOn_const hg.cont.neg).mul
          (continuous_cardyV prob (c' / 12)).continuousOn).mono Icc_subset_Ici_self
      have hcont_abs : ContinuousOn (fun t : ℝ => |g t| * prob.cardyV (c' / 12) t) (Icc 0 t_lo) :=
        (hg.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono Icc_subset_Ici_self
      refine intervalIntegral.integral_mono_on ht_lo_pos
        (hcont_neg.intervalIntegrable_of_Icc ht_lo_pos)
        (hcont_abs.intervalIntegrable_of_Icc ht_lo_pos) fun t ht => ?_
      exact mul_le_mul_of_nonneg_right (max_le (abs_nonneg _) (neg_le_abs _)) (hV_nonneg ht.1)
    have hlobe_eq : ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t =
        prob.cardyNorm (c' / 12) g * deltaLobe prob D.r_1 c' g := by
      rw [deltaLobe, ← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul]
    have hband : (1 / 2 : ℝ) - deltaLobe prob D.r_1 c' g - η / 2 ≤
        ∫ u in (chartUT c' T)..(chartAC D.r_1 c' ^ 2), max 0 (-(psiTilde prob c' g (u : ℂ)).re) := by
      rw [hneg_eq]
      have hmul := mul_le_mul_of_nonneg_left
        (show (prob.cardyNorm (c' / 12) g - η * prob.cardyNorm (c' / 12) g) / 2 -
            prob.cardyNorm (c' / 12) g * deltaLobe prob D.r_1 c' g ≤
          ∫ t in t_lo..T, max 0 (-g t) * prob.cardyV (c' / 12) t by linarith)
        (inv_nonneg.mpr hM_pos.le)
      have hlhs : (prob.cardyNorm (c' / 12) g)⁻¹ *
          ((prob.cardyNorm (c' / 12) g - η * prob.cardyNorm (c' / 12) g) / 2 -
            prob.cardyNorm (c' / 12) g * deltaLobe prob D.r_1 c' g) =
          (1 / 2 : ℝ) - deltaLobe prob D.r_1 c' g - η / 2 := by
        field_simp [hM_pos.ne']
        ring
      linarith
    -- the part below `u_T` contributes nothing
    have hleft : ∫ u in (-(chartAC D.r_1 c' ^ 2))..(chartUT c' T),
        max 0 (-(psiTilde prob c' g (u : ℂ)).re) = 0 := by
      rw [intervalIntegral.integral_of_le huT_mem.1]
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      have := hnonneg x ⟨hx.1.le, hx.2.trans huT_mem.2⟩ hx.2
      exact max_eq_left (by linarith)
    have hcontN : ContinuousOn (fun x : ℝ => max 0 (-(psiTilde prob c' g (x : ℂ)).re))
        (Icc (-(chartAC D.r_1 c' ^ 2)) (chartAC D.r_1 c' ^ 2)) := by
      refine ContinuousOn.sup continuousOn_const
        (Complex.continuous_re.comp_continuousOn ?_).neg
      refine (han.continuousOn.mono (closedBall_chartAC_subset_psiDom D.hr1_pos hc'_pos)).comp
        continuous_ofReal.continuousOn fun x hx => ?_
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr hx
    have hsplit : (∫ u in (-(chartAC D.r_1 c' ^ 2))..(chartUT c' T),
          max 0 (-(psiTilde prob c' g (u : ℂ)).re)) +
        (∫ u in (chartUT c' T)..(chartAC D.r_1 c' ^ 2),
          max 0 (-(psiTilde prob c' g (u : ℂ)).re)) =
        ∫ u in (-(chartAC D.r_1 c' ^ 2))..(chartAC D.r_1 c' ^ 2),
          max 0 (-(psiTilde prob c' g (u : ℂ)).re) :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hcontN.mono (Icc_subset_Icc le_rfl huT_mem.2)).intervalIntegrable_of_Icc huT_mem.1)
        ((hcontN.mono (Icc_subset_Icc huT_mem.1 le_rfl)).intervalIntegrable_of_Icc huT_mem.2)
    linarith
  · -- truncated total mass
    intro R' hR' hR'u
    have hR'_abs : |-R'| ≤ virasoroAC c' ^ 2 := by
      rw [abs_neg, abs_of_nonneg hR'.1]; exact hR'.2.trans hA2_le_vir
    have hre := psiTilde_re_integral_eq prob hc'_pos hg (a := -R') (b := chartAC D.r_1 c' ^ 2)
      (by linarith [hR'.1, hR'.2, hA2_le_vir]) hA2_le_vir (by linarith [hR'.1, hA2_nn])
    rw [hre]
    set t_lo := virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) with ht_lo
    set t_hi := virasoroDeltaChart c' (-R') with ht_hi
    have hT_le_hi : T ≤ t_hi := by
      rw [ht_hi, ← huT_eq]
      exact hanti.antitoneOn
        ⟨by linarith [hR'.1, hR'.2, hA2_le_vir], by linarith [hR'.1, hA2_nn, hA2_le_vir]⟩
        ⟨by linarith [huT_mem.1, hA2_le_vir], huT_mem.2.trans hA2_le_vir⟩ hR'u
    have ht_lo_pos : 0 ≤ t_lo := hΔ_pos.le
    have ht_lo_hi : t_lo ≤ t_hi := (hT_gt.trans_le hT_le_hi).le
    have ht_hi_nn : 0 ≤ t_hi := ht_lo_pos.trans ht_lo_hi
    have hsplit : ∫ t in (0 : ℝ)..t_hi, g t * prob.cardyV (c' / 12) t =
        (∫ t in (0 : ℝ)..t_lo, g t * prob.cardyV (c' / 12) t) +
        ∫ t in t_lo..t_hi, g t * prob.cardyV (c' / 12) t := by
      have hcont : ContinuousOn (fun t => g t * prob.cardyV (c' / 12) t) (Ici 0) :=
        hg.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn
      exact (intervalIntegral.integral_add_adjacent_intervals
        ((hcont.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos)
        ((hcont.mono (fun t (ht : t ∈ Set.Icc (_ : ℝ) _) => ht_lo_pos.trans ht.1)).intervalIntegrable_of_Icc
          ht_lo_hi)).symm
    have hgv_0_hi : ∫ t in (0 : ℝ)..t_hi, g t * prob.cardyV (c' / 12) t ≤
        η * prob.cardyNorm (c' / 12) g := by
      have htot : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t =
          (∫ t in (0 : ℝ)..t_hi, g t * prob.cardyV (c' / 12) t) +
          ∫ t in Ioi t_hi, g t * prob.cardyV (c' / 12) t := by
        rw [intervalIntegral.integral_of_le ht_hi_nn, ← setIntegral_union Ioc_disjoint_Ioi_same
          measurableSet_Ioi (hgv_int.mono_set Ioc_subset_Ioi_self)
          (hgv_int.mono_set (Ioi_subset_Ioi ht_hi_nn)), Ioc_union_Ioi_eq_Ioi ht_hi_nn]
      have htail_nn : 0 ≤ ∫ t in Ioi t_hi, g t * prob.cardyV (c' / 12) t :=
        setIntegral_nonneg measurableSet_Ioi fun t ht =>
          mul_nonneg (htail t (hT_le_hi.trans (mem_Ioi.mp ht).le))
            (hV_nonneg (ht_hi_nn.trans (mem_Ioi.mp ht).le))
      linarith
    have hint_neg : ∫ t in t_lo..t_hi, g t * prob.cardyV (c' / 12) t ≤
        η * prob.cardyNorm (c' / 12) g + prob.cardyNorm (c' / 12) g * deltaLobe prob D.r_1 c' g := by
      have hneg_le : -(∫ t in (0 : ℝ)..t_lo, g t * prob.cardyV (c' / 12) t) ≤
          ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t := by
        rw [← intervalIntegral.integral_neg]
        have hcont1 : ContinuousOn (fun t => -(g t * prob.cardyV (c' / 12) t)) (Icc 0 t_lo) :=
          ((hg.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono Icc_subset_Ici_self).neg
        have hcont2 : ContinuousOn (fun t => |g t| * prob.cardyV (c' / 12) t) (Icc 0 t_lo) :=
          (hg.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono Icc_subset_Ici_self
        refine intervalIntegral.integral_mono_on ht_lo_pos
          (hcont1.intervalIntegrable_of_Icc ht_lo_pos)
          (hcont2.intervalIntegrable_of_Icc ht_lo_pos) fun t ht => ?_
        calc -(g t * prob.cardyV (c' / 12) t) = (-g t) * prob.cardyV (c' / 12) t := by ring
          _ ≤ |g t| * prob.cardyV (c' / 12) t :=
              mul_le_mul_of_nonneg_right (neg_le_abs _) (hV_nonneg ht.1)
      have hlobe_eq : ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t =
          prob.cardyNorm (c' / 12) g * deltaLobe prob D.r_1 c' g := by
        rw [deltaLobe, ← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hint_neg (inv_nonneg.mpr hM_pos.le)
    have hrhs : (prob.cardyNorm (c' / 12) g)⁻¹ *
        (η * prob.cardyNorm (c' / 12) g + prob.cardyNorm (c' / 12) g * deltaLobe prob D.r_1 c' g) =
        deltaLobe prob D.r_1 c' g + η := by
      field_simp [hM_pos.ne']
      ring
    linarith

/-- info: 'FormalResearch.ModularBootstrap.Blowup.densityHyp_of_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms densityHyp_of_slack

end FormalResearch.ModularBootstrap.Blowup
