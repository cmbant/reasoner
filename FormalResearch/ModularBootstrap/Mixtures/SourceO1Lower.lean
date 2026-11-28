module

public import FormalResearch.ModularBootstrap.Mixtures.SourceNodes
public import FormalResearch.ModularBootstrap.Mixtures.RampedUpper
public import FormalResearch.ModularBootstrap.Mixtures.Duality
public import FormalResearch.ModularBootstrap.FoldTip.TwoEdgeLower

/-!
# `pmix:o1`, lower half: Two-Edge Fold-Tip Lower Bound for Signed Common Sources

Adapts `FoldTip.TwoEdgeFixedWeight` and `FoldTip.TwoEdgeInstance` to `C : CommonSource` (`C.src`),
proving the unconditional `+O(1)` lower half and two-sided `O(1)` law of Lemma PM.7 (`pmix:o1`)
for every `CommonSource`:

* `foldChartOfLemmaQSrc`: the Virasoro Langer chart on `[-Q.AC c'^2, Q.AC c'^2]` as a `FoldChart`.
* `twoEdgeInstance_of_YVForSrc`: `ChartCoverage` and `TwoEdgeViolatorsHB` for
  `CommonSourceFeasible C.src` at scale `0 < b ≤ Q.bV` from `YVInputForSrc C.src b`.
* `ft_commonSource_twoEdge`: `T ≥ ξ̄ c' + A_opt c'^{1/3} - K` for every weakly feasible test of
  `C.src` at `(c'/12, T)`, unconditionally via `yvInputForSrc_bvChoice`.
* **`pmix_o1_lower_common`**: `T_*(c̃) - D_- ≤ T` for every weakly feasible test of `C.src` at
  `c̃ ≥ c₁` (in particular `T_*(c̃) - D_- ≤ C.src.T_weak c̃ ≤ C.src.T_V c̃`).
* **`pmix_o1_common`**: two-sided `O(1)` law `T_*(c̃) - D_- ≤ C.src.T_weak c̃ ≤ C.src.T_V c̃ ≤ T_*(c̃) + D_+`
  for all `c̃ ≥ c₁`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
open ConcreteBootstrap FixedWeightTip FixedWeightBand FoldTip FixedWeight Chart

/-! ### Section 1: Fold Chart and Asymptotic Sigma Bound -/

/-- The Langer chart of `LemmaQSrcData C` as a `FoldChart` (`β = 1 / c_*`). -/
noncomputable def foldChartOfLemmaQSrc {C : CommonSource} (Q : LemmaQSrcData C) : FoldChart where
  ξs := xiBar
  β := 1 / cStar
  Cξ := chartParams.C_xi
  C0 := 1
  U := fun c' => Q.AC c' ^ 2
  Δ := virasoroDeltaChart
  hβ := one_div_pos.mpr cStar_pos
  hCξ := chartParams.hCxi_nn
  hC0 := le_rfl
  inv_lower := fun C_c hC u hu => by
    have h := virasoro_deltaChart_inversion (by linarith) (Q.abs_le_virasoro (by linarith) hu)
    have h2 : u / (1 / cStar) * C_c ^ (1 / 3 : ℝ) = cStar * C_c ^ (1 / 3 : ℝ) * u := by
      field_simp
    linarith

/-- The chart of `foldChartOfLemmaQSrc` is `virasoroDeltaChart`. -/
theorem foldChartOfLemmaQSrc_Δ {C : CommonSource} (Q : LemmaQSrcData C) :
    (foldChartOfLemmaQSrc Q).Δ = virasoroDeltaChart := rfl

/-- `foldChartOfLemmaQSrc` has slope `|a₁| / β = A_opt`. -/
theorem foldChartOfLemmaQSrc_slope {C : CommonSource} (Q : LemmaQSrcData C) :
    |airyZero 1| / (foldChartOfLemmaQSrc Q).β = Aopt := by
  show |airyZero 1| / (1 / cStar) = Aopt
  unfold Aopt
  field_simp

/-- The feasible set of a `ShiftSource`: `T` is a threshold of a weakly feasible test at `(c'/12, T)`. -/
def CommonSourceFeasible (src : ShiftSource) (c' T : ℝ) : Prop :=
  ∃ g : ℝ → ℝ, src.IsWeaklyFeasible (c' / 12) T g

private lemma sigma_arc_eventuallyFor_src {C : CommonSource} (Q : LemmaQSrcData C)
    {b : ℝ} (hb : 0 < b) :
    ∀ᶠ c' : ℝ in atTop,
      (3 * π) ^ (12 : ℕ) ≤ c' ∧
      48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) ∧
      Q.sigma c' ≤ 1 / 2 ∧
      Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1 := by
  have h1 : ∀ᶠ c' : ℝ in atTop, (3 * π) ^ (12 : ℕ) ≤ c' := eventually_ge_atTop _
  have h2 : ∀ᶠ c' : ℝ in atTop, 48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) := by
    have ht : Tendsto (fun c' : ℝ => b ^ 2 * c' ^ (2 / 3 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop (pow_pos hb 2)
    exact ht.eventually_ge_atTop 48
  have h3 : ∀ᶠ c' : ℝ in atTop, Q.sigma c' ≤ 1 / 2 :=
    Q.sigma_tendsto_zero.eventually (Iic_mem_nhds (by norm_num))
  have h4 : ∀ᶠ c' : ℝ in atTop, Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1 := by
    have h_log_tend : Tendsto (fun c' : ℝ => c' ^ (-(1 / 12 : ℝ)) * Real.log c') atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 24)).const_mul 24)
        ?_ ?_
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
        exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg hc')
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
        have hc'_pos : 0 < c' := by linarith
        have hr_nn : 0 ≤ c' ^ (-(1 / 12 : ℝ)) := Real.rpow_nonneg hc'_pos.le _
        have hlog_le : Real.log c' ≤ 24 * c' ^ (1 / 24 : ℝ) := by
          have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc'_pos (1 / 24 : ℝ))
          rw [Real.log_rpow hc'_pos] at h
          linarith
        calc c' ^ (-(1 / 12 : ℝ)) * Real.log c'
            ≤ c' ^ (-(1 / 12 : ℝ)) * (24 * c' ^ (1 / 24 : ℝ)) :=
              mul_le_mul_of_nonneg_left hlog_le hr_nn
          _ = 24 * (c' ^ (-(1 / 12 : ℝ)) * c' ^ (1 / 24 : ℝ)) := by ring
          _ = 24 * c' ^ (-(1 / 24 : ℝ)) := by rw [← Real.rpow_add hc'_pos]; norm_num
    have h_sig_lim : Tendsto (fun c' : ℝ => Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1))
        atTop (𝓝 0) := by
      have h_eq : (fun c' : ℝ => Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1)) =ᶠ[atTop]
          fun c' : ℝ => (generalEnvC1 Q.D.p_e * (3 * π * √2 * b)) *
            (c' ^ (-(1 / 12 : ℝ)) * Real.log c') + Q.sigma c' := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
        have hc'_pos : 0 < c' := by linarith
        change generalSigma Q.D.p_e c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) = _
        have hpow : c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 4 : ℝ) = c' ^ (-(1 / 12 : ℝ)) := by
          rw [← Real.rpow_add hc'_pos]; norm_num
        unfold generalSigma
        calc (generalEnvC1 Q.D.p_e * c' ^ (-(1 / 3 : ℝ)) * Real.log c') *
                (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1)
            = generalEnvC1 Q.D.p_e * (3 * π * √2 * b) *
                ((c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 4 : ℝ)) * Real.log c') +
              generalEnvC1 Q.D.p_e * c' ^ (-(1 / 3 : ℝ)) * Real.log c' := by ring
          _ = generalEnvC1 Q.D.p_e * (3 * π * √2 * b) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') +
                generalEnvC1 Q.D.p_e * c' ^ (-(1 / 3 : ℝ)) * Real.log c' := by rw [hpow]
      have h_sum := ((h_log_tend.const_mul (generalEnvC1 Q.D.p_e * (3 * π * √2 * b))).add
        Q.sigma_tendsto_zero).congr' h_eq.symm
      simpa only [mul_zero, add_zero] using h_sum
    exact h_sig_lim.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  exact h1.and (h2.and (h3.and h4))

/-! ### Section 2: `TwoEdgeInstance` and Lower Bound for `CommonSource` -/

/-- Violator family and chart coverage of a `CommonSource` at scale `0 < b ≤ Q.bV` from `YVInputForSrc`. -/
theorem twoEdgeInstance_of_YVForSrc {C : CommonSource} (Q : LemmaQSrcData C)
    {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ Q.bV) (hYV : YVInputForSrc C.src b) :
    ∃ (P : BootstrapParams) (C₁ : ℝ), Q.cQ ≤ C₁ ∧
      max (foldChartOfLemmaQSrc Q).C0 (tebC2 P) ≤ C₁ ∧
      (∀ C_c : ℝ, C₁ ≤ C_c → |airyZero 1| ≤ (foldChartOfLemmaQSrc Q).U C_c) ∧
      (foldChartOfLemmaQSrc Q).ChartCoverage (CommonSourceFeasible C.src) (airyZero 1) C₁ ∧
      TwoEdgeViolatorsHB (foldChartOfLemmaQSrc Q) P 0 (CommonSourceFeasible C.src) (airyZero 1) C₁ := by
  obtain ⟨C_fb, c_YV, hC_fb, hc_YV, hYVat⟩ := hYV
  obtain ⟨c_Q1, C_gap, κ_gap, _, _, _, _, hC_gap, hκ_gap, hQ1⟩ :=
    deltaLobeSrc_gap_of_common C Q.D Q.hr1_pos Q.hr1_le
  let P := bootstrapParamsForSrc Q b hb_pos C_fb hC_fb C_gap κ_gap hC_gap hκ_gap
  have hQ_typeII := teb_quant_c1_typeII Q.hC0
    (fun c' => Q.AC c' ^ 2) Q.sigma (fun c' => C_gap * Real.exp (-κ_gap * c'))
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
      (mul_pos two_pos (pow_pos Q.bV_pos 2)) |>.congr'
        (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c' hc'; rw [Q.AC_sq c' hc']))
    (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'; exact Q.sigma_nonneg hc')
    Q.sigma_tendsto_zero
    (Eventually.of_forall fun c' => mul_nonneg hC_gap.le (Real.exp_pos _).le)
    (by
      have ht : Tendsto (fun c' : ℝ => -κ_gap * c') atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa only [mul_zero, Function.comp] using (Real.tendsto_exp_atBot.comp ht).const_mul C_gap)
  obtain ⟨c_1, hc_1, hQuant⟩ := hQ_typeII
  have h_asymp := sigma_arc_eventuallyFor_src Q hb_pos
  rw [eventually_atTop] at h_asymp
  obtain ⟨c_asymp, hc_asymp⟩ := h_asymp
  let C₁ : ℝ := max Q.cQ (max c_YV (max c_Q1 (max c_1 (max (tebC2 P) c_asymp))))
  have hC1_Q : Q.cQ ≤ C₁ := le_max_left _ _
  have hC1_teb : tebC2 P ≤ C₁ :=
    ((le_max_left _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))).trans le_rfl
  have core : ∀ {c' T : ℝ}, C₁ ≤ c' → ∀ {g : ℝ → ℝ}, C.src.IsWeaklyFeasible (c' / 12) T g →
      T < virasoroDeltaChart c' (airyZero 1) →
      airyZero 1 < virasoroUT c' T ∧ |virasoroUT c' T| ≤ Q.AC c' ^ 2 ∧
      virasoroDeltaChart c' (virasoroUT c' T) = T ∧
      ∃ I : BootstrapHBInstance P 0, I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) ∧
        I.c = c' ∧ I.x_tilde = virasoroUT c' T - airyZero 1 := by
    intro c' T hc' g hg hT_lt
    have hc'_Q : Q.cQ ≤ c' := hC1_Q.trans hc'
    have hc'_YV : c_YV ≤ c' := ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
    have hc'_Q1 : c_Q1 ≤ c' :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
    have hc'_1 : c_1 ≤ c' :=
      ((le_max_left _ _).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc'
    have hc'_asymp : c_asymp ≤ c' :=
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))).trans hc'
    obtain ⟨h_c12, h_b48, hς_half, hς_arc⟩ := hc_asymp c' hc'_asymp
    have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'_Q
    obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
    have hA2_le : chartACAt b c' ^ 2 ≤ Q.AC c' ^ 2 := Q.ACAt_sq_le hb_pos.le hb_le hc'_pos.le
    have hA2_b48 : 48 ≤ chartACAt b c' ^ 2 := by
      rw [chartACAt_sq b c' hc'_pos.le]; linarith
    obtain ⟨hM_pos, hdl_bd, hdl_half, hT_A2⟩ := hQ1 hc'_Q1 hg
    have hpart2 := Q.part2 hc'_Q hg.1 hM_pos
    have hpart3 := Q.part3 hc'_Q hg
    have ha1_le_A2 : |airyZero 1| ≤ Q.AC c' ^ 2 := by
      rw [abs_of_neg (by linarith)]; linarith
    have hT_lt_a1_neg : T < virasoroDeltaChart c' (-Q.AC c' ^ 2) := by
      have hΔ_le : virasoroDeltaChart c' (airyZero 1) ≤ virasoroDeltaChart c' (-Q.AC c' ^ 2) :=
        (Q.deltaChart_strictAnti hc'_pos).antitoneOn
          ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
      exact hT_lt.trans_le hΔ_le
    obtain ⟨huT_mem, huT_eq⟩ := Q.UT_between hc'_pos le_rfl le_rfl
      (by linarith [sq_nonneg (Q.AC c')]) hT_A2.le hT_lt_a1_neg.le
    have ha1_lt_uT : airyZero 1 < virasoroUT c' T := by
      by_contra hle
      have hΔ_ge : virasoroDeltaChart c' (airyZero 1) ≤ virasoroDeltaChart c' (virasoroUT c' T) :=
        (Q.deltaChart_strictAnti hc'_pos).antitoneOn
          huT_mem ⟨by linarith, by linarith⟩ (not_lt.mp hle)
      linarith [huT_eq, hT_lt]
    have hB2 : QuantC1B2Holds (psiTildeSrc C.src c' g) (virasoroUT c' T) := by
      refine hQuant c' hc'_1 (psiTildeSrc C.src c' g) (virasoroUT c' T) ?_ ?_ ?_ ha1_lt_uT
        huT_mem.2 ?_ hpart3.2.1 ?_ ?_
      · exact (Q.analytic hc'_Q hg.1).mono fun z hz => Q.closedBall_subset_psiDom hc'_pos hz
      · intro x hx
        have hx' : |x| ≤ Q.AC c' ^ 2 := abs_le.mpr hx
        exact (hpart2.2.1 x hx').1
      · intro u hu hcut
        exact hpart2.2.2 u hu hcut
      · intro x hx
        have hx_abs : |x| ≤ Q.AC c' ^ 2 := abs_le.mpr ⟨hx.1, hx.2.trans huT_mem.2⟩
        have hΔ_le : T ≤ virasoroDeltaChart c' x := by
          rw [← huT_eq]
          exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
            (abs_le.mp hx_abs) huT_mem hx.2
        exact hpart3.1 x hx_abs hΔ_le
      · have hpart3_lo := hpart3.2.2.2.1 hT_lt_a1_neg hT_A2.le
        have hlo := hpart3_lo.2.2
        change 1 / 2 - deltaLobeSrc C.src Q.r_1 c' g ≤
          ∫ (u : ℝ) in virasoroUT c' T..(Q.AC c' ^ 2), max 0 (-(psiTildeSrc C.src c' g ↑u).re) at hlo
        linarith [hlo, hdl_bd]
      · intro R' hR'_mem hR'_uT
        have hT_le_ΔR' : T ≤ virasoroDeltaChart c' (-R') := by
          rw [← huT_eq]
          exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
            ⟨by linarith [hR'_mem.2], by linarith [hR'_mem.1]⟩ huT_mem hR'_uT
        exact (hpart3.2.2.2.2 R' hR'_mem.1 hR'_mem.2 hT_le_ΔR').2.trans hdl_bd
    obtain ⟨I, hI⟩ := bootstrapHB_of_YVForSrc Q hb_pos hb_le hC_fb hc_YV hYVat hC_gap hκ_gap
      hc'_Q hc'_YV h_c12 (by linarith [h_b48]) hς_half hς_arc hg hdl_bd hdl_half hT_A2 hT_lt hB2
    exact ⟨ha1_lt_uT, abs_le.mpr huT_mem, huT_eq, I, hI⟩
  refine ⟨P, C₁, hC1_Q,
    max_le (hC1_Q.trans' (by have := Q.hcQ_10000; show (1 : ℝ) ≤ Q.cQ; linarith)) hC1_teb, ?_, ?_, ?_⟩
  · intro C_c hC_c
    have hc_Q : Q.cQ ≤ C_c := hC1_Q.trans hC_c
    have hc_pos : 0 < C_c := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc_Q
    have hc_asymp' : c_asymp ≤ C_c :=
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))).trans hC_c
    obtain ⟨_, h_b48, _, _⟩ := hc_asymp C_c hc_asymp'
    have hA2_le : chartACAt b C_c ^ 2 ≤ Q.AC C_c ^ 2 := Q.ACAt_sq_le hb_pos.le hb_le hc_pos.le
    have hA2_b48 : 48 ≤ chartACAt b C_c ^ 2 := by rw [chartACAt_sq b C_c hc_pos.le]; linarith
    obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
    dsimp [foldChartOfLemmaQSrc]
    rw [abs_of_neg (by linarith)]
    linarith
  · intro C_c hC_c T ⟨g, hg⟩ hT_lt
    obtain ⟨ha1_lt, hu_bd, hΔ_eq, _⟩ := core hC_c hg hT_lt
    exact ⟨virasoroUT C_c T, ⟨g, hg⟩, hu_bd, ha1_lt, hΔ_eq⟩
  · intro C_c hC_c T u ⟨⟨g, hg⟩, hu_bd, hu_gt, hΔ_eq⟩
    have hc_Q : Q.cQ ≤ C_c := hC1_Q.trans hC_c
    have hc_pos : 0 < C_c := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc_Q
    have hc_asymp' : c_asymp ≤ C_c :=
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))).trans hC_c
    obtain ⟨_, h_b48, _, _⟩ := hc_asymp C_c hc_asymp'
    have hA2_le : chartACAt b C_c ^ 2 ≤ Q.AC C_c ^ 2 := Q.ACAt_sq_le hb_pos.le hb_le hc_pos.le
    have hA2_b48 : 48 ≤ chartACAt b C_c ^ 2 := by rw [chartACAt_sq b C_c hc_pos.le]; linarith
    obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
    have ha1_abs : |airyZero 1| ≤ Q.AC C_c ^ 2 := by rw [abs_of_neg (by linarith)]; linarith
    have hT_lt : T < virasoroDeltaChart C_c (airyZero 1) := by
      rw [← hΔ_eq]
      exact (Q.deltaChart_strictAnti hc_pos) (abs_le.mp ha1_abs) (abs_le.mp hu_bd) hu_gt
    obtain ⟨_, _, _, I, hI⟩ := core hC_c hg hT_lt
    refine ⟨I, hI.2.1, ?_, hI.1⟩
    rw [hI.2.2, ← hΔ_eq, foldChartOfLemmaQSrc_Δ, virasoroUT,
      virasoroUChart_deltaChart hc_pos (Q.abs_le_virasoro hc_pos.le hu_bd)]

/-- **Theorem `FT-L.FW` for `CommonSource`** (via Theorem `FT-2E` with fixed HB data and `yvInputForSrc_bvChoice`):
every weakly feasible test of `C.src` at `(c'/12, T)` with `C₁ ≤ c'` obeys `T ≥ ξ̄ c' + A_opt c'^{1/3} - K`. -/
theorem ft_commonSource_twoEdge {C : CommonSource} (Q : LemmaQSrcData C) :
    ∃ K C₁ : ℝ, Q.cQ ≤ C₁ ∧ 0 ≤ K ∧
      ∀ C_c : ℝ, C₁ ≤ C_c → ∀ T : ℝ, CommonSourceFeasible C.src C_c T →
        xiBar * C_c + Aopt * C_c ^ (1 / 3 : ℝ) - K ≤ T := by
  obtain ⟨P, C₁, hC1_Q, hC1_teb, hU, hcov, hviol⟩ :=
    twoEdgeInstance_of_YVForSrc Q Q.bvChoice_pos Q.bvChoice_le (yvInputForSrc_bvChoice Q)
  obtain ⟨Km, hKm_nn, hlow⟩ := ft_twoEdge_lower_hb (foldChartOfLemmaQSrc Q) P (airyZero_neg 1)
    hC1_teb hU hcov hviol
  refine ⟨Km, C₁, hC1_Q, hKm_nn, fun C_c hC_c T hT => ?_⟩
  have := hlow C_c hC_c T hT
  rwa [foldChartOfLemmaQSrc_slope] at this

/-! ### Section 3: Lemma `PM.7` (`pmix:o1`), Lower Half and Combined `O(1)` Law -/

/-- **`pmix:o1`, lower half, for every `CommonSource`** (`positive_mixtures.tex`, Lemma PM.7):
there exist `D_- ≥ 0` and `c₁ ≥ 12 a₀` such that every weakly feasible test function `g` of `C.src`
at `(c̃/12, T)`, `c̃ ≥ c₁`, satisfies `T ≥ T_*(c̃) - D_-`. -/
theorem pmix_o1_lower_common (C : CommonSource) :
    ∃ c₁ D : ℝ, 0 ≤ D ∧ 12 * C.a₀ ≤ c₁ ∧ ∀ {c T : ℝ} {g : ℝ → ℝ},
      c₁ ≤ c → C.src.IsWeaklyFeasible (c / 12) T g → TStar c - D ≤ T := by
  obtain ⟨Q⟩ := LemmaQSrcData.nonempty C
  obtain ⟨K, C₁, hC1_Q, hK_nn, hlow⟩ := ft_commonSource_twoEdge Q
  have h12_Q : 12 * C.a₀ ≤ Q.cQ := by
    have := Q.hcQ_src_shift
    have := Q.hcQ_10000
    linarith
  refine ⟨C₁, K, hK_nn, h12_Q.trans hC1_Q, fun {c T g} hc hg => ?_⟩
  have := hlow c hc T ⟨g, hg⟩
  simpa only [TStar] using this

/-- **`pmix:o1`, full two-sided `O(1)` law for every `CommonSource`** (`positive_mixtures.tex`, Lemma PM.7):
`T_*(c̃) - D_- ≤ C.src.T_weak c̃ ≤ C.src.T_V c̃ ≤ T_*(c̃) + D_+` for all `c̃ ≥ c₁`
(and every weakly feasible threshold satisfies `T ≥ T_*(c̃) - D_-`). -/
theorem pmix_o1_common (C : CommonSource) :
    ∃ c₁ D_m D_p : ℝ, 0 ≤ D_m ∧ 0 ≤ D_p ∧ 12 * C.a₀ ≤ c₁ ∧
      ∀ {c : ℝ}, c₁ ≤ c →
        TStar c - D_m ≤ C.src.T_weak c ∧
        C.src.T_weak c ≤ C.src.T_V c ∧
        C.src.T_V c ≤ TStar c + D_p ∧
        (∀ {T : ℝ} {g : ℝ → ℝ}, C.src.IsWeaklyFeasible (c / 12) T g → TStar c - D_m ≤ T) := by
  obtain ⟨c_m, D_m, hDm, h12_m, hlow⟩ := pmix_o1_lower_common C
  obtain ⟨c_p, D_p, hDp, hup⟩ := pmix_o1_upper_common C
  obtain ⟨c_f, D_f, h12_f, _, hfeas⟩ := pmix_o1_feasible_common C
  refine ⟨max c_m (max c_p c_f), D_m, D_p, hDm, hDp, h12_m.trans (le_max_left _ _), fun {c} hc => ?_⟩
  have hcm : c_m ≤ c := (le_max_left _ _).trans hc
  have hcp : c_p ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hcf : c_f ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have h12_c : 12 * C.a₀ ≤ c := h12_m.trans hcm
  obtain ⟨hTf, gf, hgf⟩ := hfeas hcf
  have hgf_w : C.src.IsWeaklyFeasible (c / 12) (TStar c + D_f) gf := by
    refine ⟨hgf.1, ?_, hgf.2.1.le, hgf.2.2⟩
    by_contra hall
    push Not at hall
    have h0 : (fun t => gf t * C.src.cardyV (c / 12) t) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp [hall t (mem_Ioi.1 ht).le]
    have hv0 : C.src.gVac (c / 12) gf = 0 := by
      unfold ShiftSource.gVac
      rw [integral_congr_ae h0]; simp
    linarith [hgf.2.1]
  have hne_w : {T : ℝ | 0 < T ∧ ∃ g, C.src.IsWeaklyFeasible (c / 12) T g}.Nonempty :=
    ⟨TStar c + D_f, hTf, gf, hgf_w⟩
  refine ⟨?_, T_weak_le_T_V_of_common C h12_c, hup hcp, fun {T g} hg => hlow hcm hg⟩
  exact le_csInf hne_w fun T ⟨_, g, hg⟩ => hlow hcm hg

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.ft_commonSource_twoEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ft_commonSource_twoEdge

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_o1_lower_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_o1_lower_common

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_o1_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_o1_common

end FormalResearch.ModularBootstrap.Mixtures
