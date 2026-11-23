module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWHB

/-!
# Theorem `FT-L.FW` at Every Fixed `(w, Q)` from the Band-Feedback Input (WP10)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Theorem `W1'(1)`
(`wone:genlower`) and Theorem `J` (`vlo:J`) at an arbitrary `prob : FixedWeightProblem`.

* `theoremFTLFW_W_of_YVFor`: Steps 0-5 of Theorem `FT-L.FW` at scale `0 < b ≤ b_V` from `YVInputForW prob b`:
  there are `c₂ ≥ cQ` and `C ≥ 0` with `T ≥ ξ̄ c' + A_opt c'^{1/3} - C` for every weakly feasible test at
  `(c'/12, T)`, `c' ≥ c₂` (the Virasoro `theoremFTLFW_oneZero_of_YVFor`);
* `theoremJ_T_V_W`: `T_V(c̃) ≥ T_*(c̃) - C` from `YVInputForW`;
* `fixedWeightLowerBoundInput_of_YVForW`: the consumer interface
  `FixedWeightLowerBoundInput prob` (Theorem `W1'(1)`) from `YVInputForW prob b` at a scale `b ≤ b_V`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip

variable {prob : FixedWeightProblem}

/-- **Theorem `FT-L.FW` at `(P, Q) = (1, 0)`** (`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`,
`wone:ftlfw`) at scale `0 < b ≤ Q.bV` from `YVInputForW prob b`: Steps 0–5 give
`c₂ ≥ Q.cQ` and `C ≥ 0` such that every weakly feasible Virasoro test `g` at
`(c'/12, T)` with `c' ≥ c₂` obeys `T ≥ ξ̄ c' + A_opt c'^{1/3} - C`. -/
theorem theoremFTLFW_W_of_YVFor (Q : LemmaQData prob) {b : ℝ} (hb_pos : 0 < b)
    (hb_le : b ≤ Q.bV) (hYV : YVInputForW prob b) :
    ∃ c_2 C : ℝ, Q.cQ ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' T : ℝ}, c_2 ≤ c' → ∀ {g : ℝ → ℝ},
        prob.IsWeaklyFeasible (c' / 12) T g →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ T := by
  obtain ⟨C_fb, c_YV, hC_fb, hc_YV, hYVat⟩ := hYV
  obtain ⟨c_Q1, C_gap, κ_gap, hc_Q1, hC_gap, hκ_gap, hQ1⟩ := lemmaQ_general_part1At Q.D hb_pos hb_le
  obtain ⟨c_Q3, hc_Q3, hQ3⟩ := lemmaQ_general_part3At Q.D hb_pos hb_le
  let P := bootstrapParamsForW Q b hb_pos C_fb hC_fb C_gap κ_gap hC_gap hκ_gap
  have hQ_typeII := teb_quant_c1_typeII Q.hC0
    (fun c' => chartACAt b c' ^ 2) Q.sigma (fun c' => C_gap * Real.exp (-κ_gap * c'))
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
      (mul_pos two_pos (pow_pos hb_pos 2)) |>.congr'
        (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c' hc'; rw [chartACAt_sq b c' hc']))
    (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'; exact Q.sigma_nonneg hc')
    Q.sigma_tendsto_zero
    (Eventually.of_forall fun c' => mul_nonneg hC_gap.le (Real.exp_pos _).le)
    (by
      have ht : Tendsto (fun c' : ℝ => -κ_gap * c') atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa only [mul_zero, Function.comp] using (Real.tendsto_exp_atBot.comp ht).const_mul C_gap)
  obtain ⟨c_1, hc_1, hQuant⟩ := hQ_typeII
  have h_asymp : ∀ᶠ c' : ℝ in atTop,
      (3 * π) ^ (12 : ℕ) ≤ c' ∧
      48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) ∧
      Q.sigma c' ≤ 1 / 2 ∧
      Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1 :=
    Q.sigma_arc_eventuallyFor hb_pos
  rw [eventually_atTop] at h_asymp
  obtain ⟨c_asymp, hc_asymp⟩ := h_asymp
  let c_2 : ℝ := max Q.cQ (max c_YV (max c_Q1 (max c_1 (max (tebC2 P) (max c_asymp c_Q3)))))
  let K₀ : ℝ := tebK0HB P 0
  let C : ℝ := cStar * K₀ + chartParams.C_xi * (|airyZero 1| + K₀) ^ 2
  have hK₀_ge1 : 1 ≤ K₀ := by
    dsimp [K₀, tebK0HB]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_nn : 0 ≤ C := by
    dsimp [C]
    have := cStar_pos
    have := chartParams.hCxi_nn
    positivity
  refine ⟨c_2, C, le_max_left _ _, hC_nn, fun {c' T} hc' {g} hg => ?_⟩
  have hc'_Qenv : Q.cQ ≤ c' := (le_max_left _ _).trans hc'
  have hc'_YV : c_YV ≤ c' := ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_Q1 : c_Q1 ≤ c' :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hc'_1 : c_1 ≤ c' :=
    ((le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc'
  have hc'_teb : tebC2 P ≤ c' :=
    ((le_max_left _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))).trans hc'
  have hc'_asymp : c_asymp ≤ c' :=
    ((le_max_left _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))).trans hc'
  have hc'_Q3 : c_Q3 ≤ c' :=
    ((le_max_right _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))).trans hc'
  obtain ⟨h_c12, h_b48, hς_half, hς_arc⟩ := hc_asymp c' hc'_asymp
  have hc'_10000 : 10000 ≤ c' :=
    (Q.hcQ_10000.trans hc'_Qenv)
  have hc'_pos : 0 < c' := by linarith
  have hc'_ge1 : 1 ≤ c' := by linarith
  have hc_m13 : c' ^ (-(1 / 3 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hc'_pos.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hc'_ge1 (by norm_num))
  obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
  have hA2_le : chartACAt b c' ^ 2 ≤ Q.AC c' ^ 2 :=
    Q.ACAt_sq_le hb_pos.le hb_le hc'_pos.le
  have hA2_b48 : 48 ≤ chartACAt b c' ^ 2 := by
    rw [chartACAt_sq b c' hc'_pos.le]; linarith
  have hA2_48 : 48 ≤ Q.AC c' ^ 2 := hA2_b48.trans hA2_le
  have hAopt_eq : Aopt = -cStar * airyZero 1 := by
    unfold Aopt
    rw [abs_of_neg (by linarith)]
    ring
  rcases le_or_gt (virasoroDeltaChart c' (airyZero 1)) T with hT_ge | hT_lt
  · -- Case 1: `T ≥ Δ(a₁)` (no bootstrap needed)
    have hinv := Q.deltaChart_inversion (u := airyZero 1) hc'_pos
      (abs_le.mpr ⟨by linarith, by linarith⟩)
    have herr_bd : chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * airyZero 1 ^ 2 ≤ C := by
      have h1 : airyZero 1 ^ 2 ≤ (|airyZero 1| + K₀) ^ 2 := by
        rw [← sq_abs (airyZero 1)]
        have : |airyZero 1| ≤ |airyZero 1| + K₀ := by linarith
        nlinarith [abs_nonneg (airyZero 1)]
      have h2 : chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * airyZero 1 ^ 2 ≤
          chartParams.C_xi * 1 * (|airyZero 1| + K₀) ^ 2 := by
        have := chartParams.hCxi_nn
        gcongr
      have : 0 ≤ cStar * K₀ := mul_nonneg cStar_pos.le (by linarith)
      dsimp [C]; linarith
    have hmul_a1 : -cStar * c' ^ (1 / 3 : ℝ) * airyZero 1 = Aopt * c' ^ (1 / 3 : ℝ) := by
      rw [hAopt_eq]; ring
    linarith [hT_ge, hinv, hmul_a1, herr_bd]
  · -- Case 2: `T < Δ(a₁)` (Steps 1–5)
    obtain ⟨hM_pos, hdl_bd, hdl_half, hT_A2⟩ := hQ1 hc'_Q1 hg
    have hQ3_b := hQ3 hc'_Q3 hg
    have huT_Ioo : virasoroUT c' T ∈ Ioo (-(chartACAt b c' ^ 2)) (chartACAt b c' ^ 2) :=
      hQ3_b.2.2.1
        (hT_lt.trans ((Q.deltaChart_strictAnti hc'_pos)
          ⟨by linarith [hA2_le], by linarith [sq_nonneg (chartACAt b c'), hA2_le]⟩
          ⟨by linarith, by linarith⟩ (by linarith)))
        hT_A2
    have hu_mem := Q.UT_between hc'_pos
      (a := -(chartACAt b c' ^ 2)) (b := chartACAt b c' ^ 2)
      (by linarith [hA2_le]) hA2_le (by linarith [sq_nonneg (chartACAt b c')])
      hT_A2.le
      (hT_lt.le.trans ((Q.deltaChart_strictAnti hc'_pos).antitoneOn
        ⟨by linarith [hA2_le], by linarith [sq_nonneg (chartACAt b c'), hA2_le]⟩
        ⟨by linarith, by linarith⟩ (by linarith)))
    set u_T := virasoroUT c' T
    have ha1_lt_uT : airyZero 1 < u_T := by
      by_contra hle
      have := (Q.deltaChart_strictAnti hc'_pos).antitoneOn
        ⟨by linarith [huT_Ioo.1, hA2_le], huT_Ioo.2.le.trans hA2_le⟩
        ⟨by linarith, by linarith⟩ (not_lt.mp hle)
      linarith [hu_mem.2]
    have hQ2 := Q.part2 hc'_Qenv hg.1 hM_pos
    have hB2 : QuantC1B2Holds (psiTilde prob c' g) u_T := by
      refine hQuant c' hc'_1 (psiTilde prob c' g) u_T ?_ ?_ ?_ ha1_lt_uT huT_Ioo.2.le ?_
        hQ3_b.2.1 ?_ ?_
      · exact hQ2.1.mono fun z hz => Q.closedBall_subset_psiDom hc'_pos
          (Metric.closedBall_subset_closedBall hA2_le hz)
      · intro x hx
        exact (hQ2.2.1 x ((abs_le.mpr hx).trans hA2_le)).1
      · intro u hu hcut
        exact hQ2.2.2 u (Metric.closedBall_subset_closedBall hA2_le hu) hcut
      · intro x hx
        have hT_le : T ≤ virasoroDeltaChart c' x := by
          rw [← hu_mem.2]
          exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
            ⟨by linarith [hx.1, hA2_le], (hx.2.trans huT_Ioo.2.le).trans hA2_le⟩
            ⟨by linarith [huT_Ioo.1, hA2_le], huT_Ioo.2.le.trans hA2_le⟩ hx.2
        exact hQ3_b.1 x (abs_le.mpr ⟨hx.1, hx.2.trans huT_Ioo.2.le⟩) hT_le
      · have h_half := hQ3_b.2.2.2.1
          (hT_lt.trans ((Q.deltaChart_strictAnti hc'_pos)
            ⟨by linarith [hA2_le], by linarith [sq_nonneg (chartACAt b c'), hA2_le]⟩
            ⟨by linarith, by linarith⟩ (by linarith)))
          hT_A2.le
        rw [chartUT_eq_virasoroUT] at h_half
        linarith [h_half.2.2, hdl_bd]
      · intro R' hR'_mem hR'_uT
        have hT_le_R' : T ≤ virasoroDeltaChart c' (-R') := by
          rw [← hu_mem.2]
          exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
            ⟨by linarith [hR'_mem.2, hA2_le], by linarith [hR'_mem.1, hR'_mem.2, hA2_le]⟩
            ⟨by linarith [huT_Ioo.1, hA2_le], huT_Ioo.2.le.trans hA2_le⟩ hR'_uT
        exact (hQ3_b.2.2.2.2 R' hR'_mem.1 hR'_mem.2 hT_le_R').2.trans hdl_bd
    obtain ⟨I, hB3, hIc, hIx⟩ := bootstrapHB_of_YVForW hb_pos hb_le hC_fb hc_YV hYVat
      hC_gap hκ_gap hc'_Qenv hc'_YV h_c12 h_b48 hς_half hς_arc hg hdl_bd hdl_half hT_A2 hT_lt hB2
    have hboot := (teb_bootstrap_hb P I (by rw [hIc]; exact hc'_teb)).2 hB3
    have hK_le : c' ^ (1 / 3 : ℝ) * (u_T - airyZero 1) ≤ K₀ := by
      simpa only [hIc, hIx] using hboot.2
    have huT_sub_le : u_T - airyZero 1 ≤ K₀ * c' ^ (-(1 / 3 : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hK_le (Real.rpow_nonneg hc'_pos.le (-(1 / 3 : ℝ)))
      have h2 : c' ^ (-(1 / 3 : ℝ)) * (c' ^ (1 / 3 : ℝ) * (u_T - airyZero 1)) =
          u_T - airyZero 1 := by
        rw [← mul_assoc, ← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero, one_mul]
      linarith [h1, h2]
    have huT_sub_K0 : u_T - airyZero 1 ≤ K₀ := by
      have : K₀ * c' ^ (-(1 / 3 : ℝ)) ≤ K₀ * 1 :=
        mul_le_mul_of_nonneg_left hc_m13 (by linarith)
      linarith
    have huT_abs_le : |u_T| ≤ |airyZero 1| + K₀ := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have : -|airyZero 1| = airyZero 1 := by rw [abs_of_neg (by linarith)]; ring
        linarith
      · have : 0 ≤ |airyZero 1| + airyZero 1 := by
          rw [abs_of_neg (by linarith)]; ring_nf; linarith
        linarith
    have hinv := Q.deltaChart_inversion hc'_pos
      ((abs_le.mpr ⟨huT_Ioo.1.le, huT_Ioo.2.le⟩).trans hA2_le)
    rw [hu_mem.2] at hinv
    have herr_bd : chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u_T ^ 2 ≤
        chartParams.C_xi * (|airyZero 1| + K₀) ^ 2 := by
      have hu2 : u_T ^ 2 ≤ (|airyZero 1| + K₀) ^ 2 := by
        rw [← sq_abs u_T, sq, sq]
        exact mul_self_le_mul_self (abs_nonneg u_T) huT_abs_le
      have := chartParams.hCxi_nn
      calc chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u_T ^ 2
          ≤ chartParams.C_xi * 1 * (|airyZero 1| + K₀) ^ 2 := by gcongr
        _ = chartParams.C_xi * (|airyZero 1| + K₀) ^ 2 := by ring
    have h_split_u : xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u_T =
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - cStar * (c' ^ (1 / 3 : ℝ) * (u_T - airyZero 1)) := by
      rw [hAopt_eq]; ring
    have hK_cstar : cStar * (c' ^ (1 / 3 : ℝ) * (u_T - airyZero 1)) ≤ cStar * K₀ :=
      mul_le_mul_of_nonneg_left hK_le cStar_pos.le
    linarith [hinv, herr_bd, h_split_u, hK_cstar]

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.theoremFTLFW_W_of_YVFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremFTLFW_W_of_YVFor

end FormalResearch.ModularBootstrap.FixedWeightBand
