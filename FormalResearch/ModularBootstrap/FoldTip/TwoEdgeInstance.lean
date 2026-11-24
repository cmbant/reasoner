module

public import FormalResearch.ModularBootstrap.FoldTip.TwoEdgeFixedWeight
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWHB

/-!
# The Fixed-Weight Lower Bound as an Instance of Theorem FT-2E

Source: `CFT/modular_bootstrap/paper/fold_tip_two_edge.tex` (Theorem FT-2E, fixed Hermite--Biehler
data), `lower_o1_two_edge.tex` (`wone:ftlfw`, Steps 1--5).

* `twoEdgeInstance_of_YVForW`: from `YVInputForW prob b` at a scale `0 < b ≤ b_V`, bootstrap parameters
  `P` and a threshold `C₁` such that the violator family of `foldChartOfLemmaQ Q`
  (`TwoEdgeViolatorsHB`, `W_top = 0`, `u_* = a₁`) and `ChartCoverage` hold for
  `Feasible c' T := ∃ g, IsWeaklyFeasible (c'/12) T g`.  The violator at `T` is `u = u_T` (Lemma Q
  parts 1 and 3, chart inversion, `bootstrapHB_of_YVForW`).
* `ft_fixedWeight_twoEdge`: Theorem FT-2E (lower bound) for a fixed-weight problem, from the above and
  `ft_twoEdge_lower_hb`: `T ≥ ξ̄ C + A_opt C^{1/3} - K` for every weakly feasible test at `(C/12, T)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip FormalResearch.ModularBootstrap.FixedWeightBand

variable {prob : FixedWeightProblem}

/-- The feasible set of a fixed-weight problem: `T` is a threshold of a weakly feasible test at
`(c'/12, T)`. -/
def FixedWeightFeasible (prob : FixedWeightProblem) (c' T : ℝ) : Prop :=
  ∃ g : ℝ → ℝ, prob.IsWeaklyFeasible (c' / 12) T g

/-- **Violator family and chart coverage of a fixed-weight problem** (the part of
`theoremFTLFW_W_of_YVFor` Case 2 feeding Theorem FT-2E).  At scale `0 < b ≤ b_V`, from
`YVInputForW prob b`, there are bootstrap parameters `P` and `C₁ ≥ c_Q` with `max C₀ (tebC2 P) ≤ C₁`,
`|a₁| ≤ A_{c'}²` for `c' ≥ C₁`, and for the chart `foldChartOfLemmaQ Q` the hypotheses `ChartCoverage`
and `TwoEdgeViolatorsHB` (with `W_top = 0`, `u_* = a₁`) of `FixedWeightFeasible prob`. -/
theorem twoEdgeInstance_of_YVForW (Q : LemmaQData prob) {b : ℝ} (hb_pos : 0 < b)
    (hb_le : b ≤ Q.bV) (hYV : YVInputForW prob b) :
    ∃ (P : BootstrapParams) (C₁ : ℝ), Q.cQ ≤ C₁ ∧
      max (foldChartOfLemmaQ Q).C0 (tebC2 P) ≤ C₁ ∧
      (∀ C : ℝ, C₁ ≤ C → |airyZero 1| ≤ (foldChartOfLemmaQ Q).U C) ∧
      (foldChartOfLemmaQ Q).ChartCoverage (FixedWeightFeasible prob) (airyZero 1) C₁ ∧
      TwoEdgeViolatorsHB (foldChartOfLemmaQ Q) P 0 (FixedWeightFeasible prob) (airyZero 1) C₁ := by
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
  let C₁ : ℝ := max Q.cQ (max c_YV (max c_Q1 (max c_1 (max (tebC2 P) (max c_asymp c_Q3)))))
  have hC1_Q : Q.cQ ≤ C₁ := le_max_left _ _
  have hC1_teb : tebC2 P ≤ C₁ :=
    ((le_max_left _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))).trans le_rfl
  -- the data at scale `c' ≥ C₁`
  have core : ∀ {c' T : ℝ}, C₁ ≤ c' → ∀ {g : ℝ → ℝ}, prob.IsWeaklyFeasible (c' / 12) T g →
      T < virasoroDeltaChart c' (airyZero 1) →
      airyZero 1 < virasoroUT c' T ∧ |virasoroUT c' T| ≤ Q.AC c' ^ 2 ∧
      virasoroDeltaChart c' (virasoroUT c' T) = T ∧
      ∃ I : BootstrapHBInstance P 0, I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) ∧
        I.c = c' ∧ I.x_tilde = virasoroUT c' T - airyZero 1 := by
    intro c' T hc' g hg hT_lt
    have hc'_Qenv : Q.cQ ≤ c' := hC1_Q.trans hc'
    have hc'_YV : c_YV ≤ c' := ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
    have hc'_Q1 : c_Q1 ≤ c' :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
    have hc'_1 : c_1 ≤ c' :=
      ((le_max_left _ _).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc'
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
    have hc'_10000 : 10000 ≤ c' := Q.hcQ_10000.trans hc'_Qenv
    have hc'_pos : 0 < c' := by linarith
    obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
    have hA2_le : chartACAt b c' ^ 2 ≤ Q.AC c' ^ 2 :=
      Q.ACAt_sq_le hb_pos.le hb_le hc'_pos.le
    have hA2_b48 : 48 ≤ chartACAt b c' ^ 2 := by
      rw [chartACAt_sq b c' hc'_pos.le]; linarith
    obtain ⟨hM_pos, hdl_bd, hdl_half, hT_A2⟩ := hQ1 hc'_Q1 hg
    have hQ3_b := hQ3 hc'_Q3 hg
    have hT_lt' : T < virasoroDeltaChart c' (-(chartACAt b c' ^ 2)) :=
      hT_lt.trans ((Q.deltaChart_strictAnti hc'_pos)
        ⟨by linarith [hA2_le], by linarith [sq_nonneg (chartACAt b c'), hA2_le]⟩
        ⟨by linarith, by linarith⟩ (by linarith))
    have huT_Ioo : virasoroUT c' T ∈ Ioo (-(chartACAt b c' ^ 2)) (chartACAt b c' ^ 2) :=
      hQ3_b.2.2.1 hT_lt' hT_A2
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
      · have h_half := hQ3_b.2.2.2.1 hT_lt' hT_A2.le
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
    exact ⟨ha1_lt_uT, abs_le.mpr ⟨by linarith [huT_Ioo.1, hA2_le], huT_Ioo.2.le.trans hA2_le⟩,
      hu_mem.2, I, hB3, hIc, hIx⟩
  -- the radius covers `a₁`
  have hU : ∀ C : ℝ, C₁ ≤ C → |airyZero 1| ≤ (foldChartOfLemmaQ Q).U C := by
    intro C hC
    have hc'_Qenv : Q.cQ ≤ C := hC1_Q.trans hC
    have hc'_asymp : c_asymp ≤ C :=
      ((le_max_left _ _).trans
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans
            ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))).trans hC
    obtain ⟨-, h_b48, -, -⟩ := hc_asymp C hc'_asymp
    have hc'_pos : 0 < C := by linarith [Q.hcQ_10000]
    obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
    have hA2_le : chartACAt b C ^ 2 ≤ Q.AC C ^ 2 :=
      Q.ACAt_sq_le hb_pos.le hb_le hc'_pos.le
    have hA2_b48 : 48 ≤ chartACAt b C ^ 2 := by
      rw [chartACAt_sq b C hc'_pos.le]; linarith
    show |airyZero 1| ≤ Q.AC C ^ 2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨P, C₁, hC1_Q, max_le ?_ hC1_teb, hU, ?_, ?_⟩
  · exact (show (1 : ℝ) ≤ 10000 by norm_num).trans (Q.hcQ_10000.trans hC1_Q)
  · intro C hC T ⟨g, hg⟩ hT
    obtain ⟨h1, h2, h3, -⟩ := core hC hg hT
    exact ⟨virasoroUT C T, ⟨g, hg⟩, h2, h1, h3⟩
  · intro C hC T u hv
    obtain ⟨⟨g, hg⟩, huU, hlt, hΔ⟩ := hv
    have hc_pos : 0 < C := by linarith [Q.hcQ_10000, hC1_Q.trans hC]
    have hIcc : ∀ x : ℝ, |x| ≤ Q.AC C ^ 2 → x ∈ Icc (-(Q.AC C ^ 2)) (Q.AC C ^ 2) :=
      fun x h => abs_le.mp h
    have hT_lt : T < virasoroDeltaChart C (airyZero 1) := by
      rw [← hΔ]
      exact (Q.deltaChart_strictAnti hc_pos) (hIcc _ (hU C hC)) (hIcc _ huU) hlt
    obtain ⟨h1, h2, h3, I, hIL, hIc, hIx⟩ := core hC hg hT_lt
    have hu_eq : u = virasoroUT C T :=
      (Q.deltaChart_strictAnti hc_pos).injOn (hIcc _ huU) (hIcc _ h2) (hΔ.trans h3.symm)
    exact ⟨I, hIc, by rw [hIx, hu_eq], hIL⟩

/-- **Theorem FT-2E (lower bound) for a fixed-weight crossing problem**
(`CFT/modular_bootstrap/paper/fold_tip_two_edge.tex`, `fto1:lower`, fixed Hermite--Biehler data;
`lower_o1_two_edge.tex`, `wone:ftlfw`).  From `YVInputForW prob b` at `0 < b ≤ b_V` there are
`C₁ ≥ c_Q` and `K ≥ 0` with `T ≥ ξ̄ C + A_opt C^{1/3} - K` for every weakly feasible test at
`(C/12, T)`, `C ≥ C₁`. -/
theorem ft_fixedWeight_twoEdge (Q : LemmaQData prob) {b : ℝ} (hb_pos : 0 < b)
    (hb_le : b ≤ Q.bV) (hYV : YVInputForW prob b) :
    ∃ C₁ K : ℝ, Q.cQ ≤ C₁ ∧ 0 ≤ K ∧ ∀ C : ℝ, C₁ ≤ C → ∀ T : ℝ, FixedWeightFeasible prob C T →
      xiBar * C + Aopt * C ^ (1 / 3 : ℝ) - K ≤ T := by
  obtain ⟨P, C₁, hQ, hC1, hU, hcov, hviol⟩ := twoEdgeInstance_of_YVForW Q hb_pos hb_le hYV
  obtain ⟨K, hK, hlow⟩ := ft_twoEdge_lower_hb (foldChartOfLemmaQ Q) P
    (by obtain ⟨h1, h2⟩ := FormalResearch.Special.airyZero_one; linarith) hC1 hU hcov hviol
  refine ⟨C₁, K, hQ, hK, fun C hC T hT => ?_⟩
  have := hlow C hC T hT
  rwa [foldChartOfLemmaQ_slope] at this

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.twoEdgeInstance_of_YVForW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoEdgeInstance_of_YVForW

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_fixedWeight_twoEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ft_fixedWeight_twoEdge

end FormalResearch.ModularBootstrap.FoldTip
