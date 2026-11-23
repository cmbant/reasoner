module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWArc

/-!
# Band Mass Bounds and Large-`c'` Thresholds for the Concrete Bootstrap at Weight `w`

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Steps 1-2, and
`CFT/common/two_edge_bootstrap.tex` (`teb:bootstrap`, `(B1)`-`(B2)`).

* `LemmaQData.sigma_arc_eventuallyFor`: for fixed `b > 0`, eventually in `c'` the cut-margin rate
  `ς_{c'}` satisfies `ς ≤ 1/2` and `ς (3π√2 b c'^{1/4} + 1) ≤ 1`;
* `band_sums_leW`: unconditional band bounds `B₁ ≤ 1`, `B₂ ≤ 2` from `Lemma Q (3)` (the Virasoro
  `virasoro_band_sums_le`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip

variable {prob : FixedWeightProblem}

private lemma rpow_neg_inv_mul_log_leW {c' α : ℝ} (hc' : 1 ≤ c') (hα : 0 < α) :
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

namespace LemmaQData

variable (Q : LemmaQData prob)

/-- Eventual threshold for the arc estimates at a fixed scale `b > 0`. -/
theorem sigma_arc_eventuallyFor {b : ℝ} (hb : 0 < b) :
    ∀ᶠ c' : ℝ in atTop,
      (3 * π) ^ (12 : ℕ) ≤ c' ∧
      48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) ∧
      Q.sigma c' ≤ 1 / 2 ∧
      Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1 := by
  have h1 : ∀ᶠ c' : ℝ in atTop, (3 * π) ^ (12 : ℕ) ≤ c' :=
    eventually_ge_atTop _
  have h2 : ∀ᶠ c' : ℝ in atTop, 48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) := by
    have ht : Tendsto (fun c' : ℝ => b ^ 2 * c' ^ (2 / 3 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
        (pow_pos hb 2)
    exact ht.eventually_ge_atTop 48
  have h3 : ∀ᶠ c' : ℝ in atTop, Q.sigma c' ≤ 1 / 2 :=
    Q.sigma_tendsto_zero.eventually (Iic_mem_nhds (by norm_num))
  have h4 : ∀ᶠ c' : ℝ in atTop,
      Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1 := by
    let M : ℝ := 24 * generalEnvC1 Q.D.p_e * (3 * π * √2 * b + 1)
    have hM_nn : 0 ≤ M := by
      dsimp [M]; have := generalEnvC1_pos Q.D.hp_e_nn; positivity
    have ht : Tendsto (fun c' : ℝ => M * c' ^ (-(1 / 24 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 24)).const_mul M
    filter_upwards [eventually_ge_atTop (1 : ℝ), ht.eventually (Iic_mem_nhds zero_lt_one)] with
        c' hc' hMc'
    have hc'_pos : 0 < c' := by linarith
    have hlog := rpow_neg_inv_mul_log_leW hc' (by norm_num : (0 : ℝ) < 1 / 12)
    have hrw : (2 / (1 / 12 : ℝ)) * c' ^ (-((1 / 12 : ℝ) / 2)) = 24 * c' ^ (-(1 / 24 : ℝ)) := by
      norm_num
    rw [hrw] at hlog
    have h12 : c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 4 : ℝ) = c' ^ (-(1 / 12 : ℝ)) := by
      rw [← Real.rpow_add hc'_pos]; norm_num
    have hc13_le : c' ^ (-(1 / 3 : ℝ)) ≤ c' ^ (-(1 / 12 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc' (by norm_num)
    have hlog_nn : 0 ≤ Real.log c' := Real.log_nonneg hc'
    have hsig_le : Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤
        generalEnvC1 Q.D.p_e * (3 * π * √2 * b + 1) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := by
      unfold LemmaQData.sigma generalSigma
      have hterm1 : (generalEnvC1 Q.D.p_e * c' ^ (-(1 / 3 : ℝ)) * Real.log c') *
          (3 * π * √2 * b * c' ^ (1 / 4 : ℝ)) =
          generalEnvC1 Q.D.p_e * (3 * π * √2 * b) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := by
        calc (generalEnvC1 Q.D.p_e * c' ^ (-(1 / 3 : ℝ)) * Real.log c') *
              (3 * π * √2 * b * c' ^ (1 / 4 : ℝ))
            = generalEnvC1 Q.D.p_e * (3 * π * √2 * b) *
                ((c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 4 : ℝ)) * Real.log c') := by ring
          _ = generalEnvC1 Q.D.p_e * (3 * π * √2 * b) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := by
              rw [h12]
      have hterm2 : generalEnvC1 Q.D.p_e * c' ^ (-(1 / 3 : ℝ)) * Real.log c' ≤
          generalEnvC1 Q.D.p_e * 1 * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := by
        have := (generalEnvC1_pos Q.D.hp_e_nn).le
        nlinarith [mul_le_mul_of_nonneg_right hc13_le hlog_nn]
      linarith
    have hbound : generalEnvC1 Q.D.p_e * (3 * π * √2 * b + 1) *
        (c' ^ (-(1 / 12 : ℝ)) * Real.log c') ≤ M * c' ^ (-(1 / 24 : ℝ)) := by
      have hpos : 0 ≤ generalEnvC1 Q.D.p_e * (3 * π * √2 * b + 1) := by
        have := generalEnvC1_pos Q.D.hp_e_nn; positivity
      calc generalEnvC1 Q.D.p_e * (3 * π * √2 * b + 1) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c')
          ≤ generalEnvC1 Q.D.p_e * (3 * π * √2 * b + 1) * (24 * c' ^ (-(1 / 24 : ℝ))) :=
            mul_le_mul_of_nonneg_left hlog hpos
        _ = M * c' ^ (-(1 / 24 : ℝ)) := by dsimp [M]; ring
    exact hsig_le.trans (hbound.trans hMc')
  exact h1.and (h2.and (h3.and h4))

end LemmaQData

section Band

variable [Q : LemmaQData prob]

/-- Unconditional band bounds `B₁ ≤ 1` and `B₂ ≤ 2` (hence `B₁ + B₂ ≤ 3`) for any weakly feasible
`g` with `T ∈ [Δ(-R), Δ(-A_thr)]` and `deltaLobe prob Q.D.r_1 c' g < 1 / 2` (from Lemma `Q(3)`). -/
lemma band_sums_leW {c' R T : ℝ} (hc' : Q.cQ ≤ c')
    (hR_thr : virasoroAThr ≤ R) (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hdl : deltaLobe prob Q.D.r_1 c' g < 1 / 2)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr)) :
    bandB1W prob c' R T g ≤ 1 ∧ bandB2W prob c' R g ≤ 2 := by
  have hc'_10000 : 10000 ≤ c' :=
    (Q.hcQ_10000.trans hc')
  have hc'_24 : 24 ≤ c' := by linarith
  have hc'_pos : 0 < c' := by linarith
  have ha : prob.totalShift ≤ c' / 12 := by
    have := Q.hcQ_shift; linarith
  have hM_pos : 0 < prob.cardyNorm (c' / 12) g :=
    Q.cardyNorm_pos hc' hg
  have hM_nn : 0 ≤ (prob.cardyNorm (c' / 12) g)⁻¹ := inv_nonneg.mpr hM_pos.le
  have hR_pos : 0 < R := lt_of_lt_of_le virasoroAThr_pos hR_thr
  have hA2_nn : 0 ≤ Q.AC c' ^ 2 := sq_nonneg _
  have hu_mem := Q.UT_between hc'_pos
    (by linarith : -(Q.AC c' ^ 2) ≤ -R) hA2_nn (by linarith : -R ≤ 0) hT_lo
    (hT_hi.trans ((Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [virasoroAThr_pos]⟩
      (by linarith)))
  set u_T := virasoroUT c' T
  have hΔ_uT : virasoroDeltaChart c' u_T = T := hu_mem.2
  have hRm : -R ∈ Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2) := ⟨by linarith, by linarith⟩
  have hΔ_T_le : T ≤ virasoroDeltaChart c' (-R) := by
    rw [← hΔ_uT]
    exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn hRm
      ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2]⟩ hu_mem.1.1
  have hΨ_cont_all : ContinuousOn (fun v : ℝ => (psiTilde prob c' g (v : ℂ)).re)
      (Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2)) :=
    Complex.continuous_re.comp_continuousOn
      ((Q.analytic (by linarith) hg.1).continuousOn.comp
        continuous_ofReal.continuousOn fun v hv => Q.closedBall_subset_psiDom hc'_pos (by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr hv))
  have hL1_A2 : ∫ u in (-(Q.AC c' ^ 2))..(Q.AC c' ^ 2),
      ‖psiTilde prob c' g (u : ℂ)‖ ≤ 1 := (Q.part3 hc' hg).2.1
  have h_abs_int_le : ∀ {a b : ℝ}, -(Q.AC c' ^ 2) ≤ a → a ≤ b → b ≤ Q.AC c' ^ 2 →
      |∫ u in a..b, (psiTilde prob c' g (u : ℂ)).re| ≤ 1 := by
    intro a b ha0 hab hb0
    have hnorm_cont : ContinuousOn (fun u : ℝ => ‖psiTilde prob c' g (u : ℂ)‖)
        (Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2)) :=
      continuous_norm.comp_continuousOn
        ((Q.analytic (by linarith) hg.1).continuousOn.comp
          continuous_ofReal.continuousOn fun v hv => Q.closedBall_subset_psiDom hc'_pos (by
            rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
            exact abs_le.mpr hv))
    have h1 : |∫ u in a..b, (psiTilde prob c' g (u : ℂ)).re| ≤
        ∫ u in a..b, ‖psiTilde prob c' g (u : ℂ)‖ := by
      calc |∫ u in a..b, (psiTilde prob c' g (u : ℂ)).re|
          ≤ ∫ u in a..b, |(psiTilde prob c' g (u : ℂ)).re| := by
            simpa [Real.norm_eq_abs] using
              intervalIntegral.norm_integral_le_integral_norm
                (f := fun u : ℝ => (psiTilde prob c' g (u : ℂ)).re) (μ := volume) hab
        _ ≤ ∫ u in a..b, ‖psiTilde prob c' g (u : ℂ)‖ :=
            intervalIntegral.integral_mono_on hab
              ((continuous_abs.comp_continuousOn (hΨ_cont_all.mono (Icc_subset_Icc ha0 hb0))).intervalIntegrable_of_Icc hab)
              ((hnorm_cont.mono (Icc_subset_Icc ha0 hb0)).intervalIntegrable_of_Icc hab)
              fun u _ => Complex.abs_re_le_norm _
    have hsub1 : ∫ u in a..b, ‖psiTilde prob c' g (u : ℂ)‖ ≤
        ∫ u in (-(Q.AC c' ^ 2))..(Q.AC c' ^ 2), ‖psiTilde prob c' g (u : ℂ)‖ := by
      have hsp1 := intervalIntegral.integral_add_adjacent_intervals
        ((hnorm_cont.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc (μ := volume) ha0)
        ((hnorm_cont.mono (Icc_subset_Icc ha0 le_rfl)).intervalIntegrable_of_Icc (μ := volume) (by linarith))
      have hsp2 := intervalIntegral.integral_add_adjacent_intervals
        ((hnorm_cont.mono (Icc_subset_Icc ha0 hb0)).intervalIntegrable_of_Icc (μ := volume) hab)
        ((hnorm_cont.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc (μ := volume) hb0)
      have hnn1 : 0 ≤ ∫ u in (-(Q.AC c' ^ 2))..a, ‖psiTilde prob c' g (u : ℂ)‖ :=
        intervalIntegral.integral_nonneg ha0 fun _ _ => norm_nonneg _
      have hnn2 : 0 ≤ ∫ u in b..(Q.AC c' ^ 2), ‖psiTilde prob c' g (u : ℂ)‖ :=
        intervalIntegral.integral_nonneg hb0 fun _ _ => norm_nonneg _
      linarith
    exact h1.trans (hsub1.trans hL1_A2)
  -- Part 1: `B₁ ≤ 1`
  have hB1 : bandB1W prob c' R T g ≤ 1 := by
    have hcont_t : ContinuousOn (fun t : ℝ => g t * prob.cardyV (c' / 12) t)
        (Icc T (virasoroDeltaChart c' (-R))) := by
      have hT_nn : 0 ≤ T :=
        (Q.deltaChart_pos hc'_pos (by rw [abs_zero]; exact hA2_nn)).le.trans hT_lo
      exact (hg.1.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
        (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hT_nn))
    have hi_num : IntervalIntegrable
        (fun t : ℝ => (-virasoroUT c' t) * (g t * prob.cardyV (c' / 12) t))
        volume T (virasoroDeltaChart c' (-R)) := by
      refine ContinuousOn.intervalIntegrable_of_Icc hΔ_T_le ?_
      refine ContinuousOn.mul ?_ hcont_t
      have hcont_u : ContinuousOn (virasoroUT c') (Icc T (virasoroDeltaChart c' (-R))) := by
        intro t ht
        have hΔ0 : virasoroDeltaChart c' 0 ≤ t := hT_lo.trans ht.1
        have hu_t := Q.UT_between hc'_pos (by linarith : -(Q.AC c' ^ 2) ≤ -R)
          hA2_nn (by linarith : -R ≤ 0) hΔ0 ht.2
        have ht_open : ((t / c' : ℝ) : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
          rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have hmem := Q.deltaChart_div_mem hc'_pos (abs_le.mpr ⟨hu_t.1.1.trans' (by linarith), hu_t.1.2.trans (by linarith)⟩)
          rw [hu_t.2] at hmem
          have hmem' : t / c' ∈ Icc (xiBar - chartParams.r_xi0) (xiBar + chartParams.r_xi0) := hmem
          exact (abs_le.mpr ⟨by linarith [hmem'.1], by linarith [hmem'.2]⟩).trans_lt
            (chartParams.hr_xi0_le.trans_lt (half_lt_self virasoroRXiInf_pos))
        have hc_div : ContinuousAt (fun s : ℝ => ((s / c' : ℝ) : ℂ)) t :=
          (Complex.continuous_ofReal.comp (continuous_id.div_const c')).continuousAt
        have huinf_cont : ContinuousAt virasoroUInf ((t / c' : ℝ) : ℂ) :=
          (virasoroUInf_an _ ht_open).continuousAt
        have hcomp : ContinuousAt (fun s : ℝ => c' ^ (2 / 3 : ℝ) * (virasoroUInf ((s / c' : ℝ) : ℂ)).re) t :=
          continuousAt_const.mul (Complex.continuous_re.continuousAt.comp (huinf_cont.comp_of_eq hc_div rfl))
        exact hcomp.continuousWithinAt
      exact hcont_u.neg
    have h_int_mono : ∫ t in T..(virasoroDeltaChart c' (-R)),
        (-virasoroUT c' t) * (g t * prob.cardyV (c' / 12) t) ≤
        ∫ t in T..(virasoroDeltaChart c' (-R)),
          R * (g t * prob.cardyV (c' / 12) t) := by
      refine intervalIntegral.integral_mono_on hΔ_T_le hi_num
        (hcont_t.const_mul R |>.intervalIntegrable_of_Icc hΔ_T_le) fun t ht => ?_
      have hΔ0 : virasoroDeltaChart c' 0 ≤ t := hT_lo.trans ht.1
      have hu_t := Q.UT_between hc'_pos (by linarith : -(Q.AC c' ^ 2) ≤ -R)
        hA2_nn (by linarith : -R ≤ 0) hΔ0 ht.2
      have ht_nn : 0 ≤ t :=
        (Q.deltaChart_pos hc'_pos (by rw [abs_zero]; exact hA2_nn)).le.trans hΔ0
      have hgv_nn : 0 ≤ g t * prob.cardyV (c' / 12) t :=
        mul_nonneg (hg.2.2.2 t ht.1) (prob.cardyV_nonneg ha ht_nn)
      exact mul_le_mul_of_nonneg_right (by linarith [hu_t.1.1]) hgv_nn
    have h_cov := Q.psiTilde_integral_eq hc'_24 hg.1
      (by linarith : -(Q.AC c' ^ 2) ≤ -R) (by linarith [hu_mem.1.2]) hu_mem.1.1
    rw [hΔ_uT] at h_cov
    have h_abs := (abs_le.mp (h_abs_int_le (by linarith) hu_mem.1.1 (by linarith [hu_mem.1.2]))).2
    unfold bandB1W
    calc R⁻¹ * (prob.cardyNorm (c' / 12) g)⁻¹ *
          ∫ t in T..(virasoroDeltaChart c' (-R)),
            (-virasoroUT c' t) * (g t * prob.cardyV (c' / 12) t)
        ≤ R⁻¹ * (prob.cardyNorm (c' / 12) g)⁻¹ *
            ∫ t in T..(virasoroDeltaChart c' (-R)),
              R * (g t * prob.cardyV (c' / 12) t) :=
          mul_le_mul_of_nonneg_left h_int_mono (mul_nonneg (inv_nonneg.mpr hR_pos.le) hM_nn)
      _ = (prob.cardyNorm (c' / 12) g)⁻¹ *
            ∫ t in T..(virasoroDeltaChart c' (-R)),
              g t * prob.cardyV (c' / 12) t := by
          rw [intervalIntegral.integral_const_mul]; field_simp [hR_pos.ne']
      _ = ∫ u in (-R)..u_T, (psiTilde prob c' g (u : ℂ)).re := h_cov.symm
      _ ≤ 1 := h_abs
  -- Part 2: `B₂ ≤ 2`
  have hB2 : bandB2W prob c' R g ≤ 2 := by
    have hgv_int : IntegrableOn (fun t => g t * prob.cardyV (c' / 12) t) (Ioi 0) :=
      hg.1.int_cardy.norm.mono'
        (((hg.1.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
          Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
        (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_abs])
    have h_vac_le : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t ≤ 0 := by
      have hv := hg.2.2.1; unfold FixedWeightProblem.gVac at hv; nlinarith [Real.pi_pos]
    set t_lo := virasoroDeltaChart c' (Q.AC c' ^ 2)
    set t_hi := virasoroDeltaChart c' (-R)
    have ht_lo_pos : 0 < t_lo := Q.deltaChart_pos hc'_pos (abs_of_nonneg hA2_nn).le
    have ht_lo_hi : t_lo ≤ t_hi :=
      (Q.deltaChart_strictAnti hc'_pos).antitoneOn hRm ⟨by linarith, le_rfl⟩ (by linarith)
    have hsp1 : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t =
        (∫ t in Ioc 0 t_lo, g t * prob.cardyV (c' / 12) t) +
          (∫ t in Ioc t_lo t_hi, g t * prob.cardyV (c' / 12) t) +
          ∫ t in Ioi t_hi, g t * prob.cardyV (c' / 12) t := by
      have h1 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hgv_int.mono_set Ioc_subset_Ioi_self) (hgv_int.mono_set (Ioi_subset_Ioi ht_lo_pos.le))
      rw [Ioc_union_Ioi_eq_Ioi ht_lo_pos.le] at h1
      have h2 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((hgv_int.mono_set (Ioi_subset_Ioi ht_lo_pos.le)).mono_set Ioc_subset_Ioi_self)
        (hgv_int.mono_set (Ioi_subset_Ioi (ht_lo_pos.le.trans ht_lo_hi)))
      rw [Ioc_union_Ioi_eq_Ioi ht_lo_hi] at h2
      linarith [h1, h2]
    have h_lobe_eq : -(∫ t in Ioc 0 t_lo, g t * prob.cardyV (c' / 12) t) ≤
        ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t := by
      rw [← intervalIntegral.integral_of_le ht_lo_pos.le, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_mono_on ht_lo_pos.le
        (((hg.1.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).neg.intervalIntegrable_of_Icc ht_lo_pos.le)
        (((hg.1.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos.le)
        fun t ht => ?_
      have hV := prob.cardyV_nonneg ha ht.1
      calc -(g t * prob.cardyV (c' / 12) t) = (-g t) * prob.cardyV (c' / 12) t := by ring
        _ ≤ |g t| * prob.cardyV (c' / 12) t := mul_le_mul_of_nonneg_right (neg_le_abs _) hV
    have hIci_Ioi : ∫ t in Ici t_hi, g t * prob.cardyV (c' / 12) t =
        ∫ t in Ioi t_hi, g t * prob.cardyV (c' / 12) t :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_sum_t : ∫ t in Ici t_hi, g t * prob.cardyV (c' / 12) t ≤
        -(∫ t in t_lo..t_hi, g t * prob.cardyV (c' / 12) t) +
          ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t := by
      rw [intervalIntegral.integral_of_le ht_lo_hi, hIci_Ioi]
      linarith only [h_vac_le, hsp1, h_lobe_eq]
    have hmul := mul_le_mul_of_nonneg_left h_sum_t hM_nn
    have h_cov := Q.psiTilde_integral_eq hc'_24 hg.1
      (by linarith : -(Q.AC c' ^ 2) ≤ -R) le_rfl (by linarith)
    have h_abs := (abs_le.mp (h_abs_int_le (a := -R) (b := Q.AC c' ^ 2)
      (by linarith) (by linarith) le_rfl)).1
    unfold bandB2W
    rw [mul_add, mul_neg] at hmul
    have hdl_eq : (prob.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t =
        deltaLobe prob Q.D.r_1 c' g := rfl
    linarith [hmul, h_cov, h_abs, hdl_eq, hdl]
  exact ⟨hB1, hB2⟩

/-! ### Section 3: Node-Sum Lower Bounds (`hP_nodes_lb_hb` and `P_theta_bound`) -/

end Band

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQData.sigma_arc_eventuallyFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LemmaQData.sigma_arc_eventuallyFor

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.band_sums_leW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms band_sums_leW

end FormalResearch.ModularBootstrap.FixedWeightBand
