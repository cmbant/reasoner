module

public import FormalResearch.ModularBootstrap.FoldTip.TwoEdgeFixedWeight
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapClarkHB
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWYV

/-!
# The Two-Level Lower Bound as an Instance of Theorem FT-2E (Clark pairs, `m₀ = 2`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`) at
`(P, Q) = (cos α, -sin α)` and Theorem `W1'(2)` (`wone:genlower`(2)); `fold_tip_two_edge.tex`, Theorem FT-2E
(fixed Hermite--Biehler data).

* `YVInputUniformSecond`: the band-feedback input `YVInputAtForWThr` at every cutoff radius `A_thr ≤ secondLevelAThr`
  with common constants (`LemmaQData.yvInputForW_uniform`);
* `TwoLevelFeasible`: the feasible set of the two-level problem: `T` is the threshold of a weakly feasible test
  `g` with `g(t₁) ≥ 0` at some `t₁ = ξ̄ c' + A₁ c'^{1/3} + r`, `|r| ≤ R_off` (`t₁` and `r` may depend on `g`);
* `twoEdgeInstance_of_YVForClark`: for `u₁` in a compact `K ⊂ (a₁, ∞)` (`A₁ = -c_* u₁`), common bootstrap parameters
  `P`, `W_top`, `C₁`, and for each `u₁ ∈ K` the hypotheses `ChartCoverage` and `TwoEdgeViolatorsHB`
  (`u_* = z₂(α(u₁))`) of `TwoLevelFeasible prob (-c_* u₁) R_off`: the violator at `T` is `u = u_T`
  (Lemma Q parts 1 and 3, chart inversion, `teb_quant_c1_clark_typeII_firstLevel`, `bootstrapHB_of_YVForClark`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip FormalResearch.SignUncertainty TwoLevel

/-- The band-feedback input at every cutoff radius `0 < A_thr ≤ secondLevelAThr` at scale `b`, with common constants
(the output of `LemmaQData.yvInputForW_uniform`). -/
def YVInputUniformSecond (prob : FixedWeightProblem) (b : ℝ) : Prop :=
  ∃ C_fb c_YV : ℝ, 1 ≤ C_fb ∧ 10000 ≤ c_YV ∧
    ∀ ⦃A_thr : ℝ⦄, 0 < A_thr → A_thr ≤ secondLevelAThr →
      YVInputAtForWThr prob A_thr b (psiTilde prob) C_fb c_YV

theorem LemmaQData.yvInputUniformSecond_of_scaleCompat {prob : FixedWeightProblem} (Q : LemmaQData prob)
    {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ Q.bV) (hScale : 2 * b ^ 2 ≤ Q.scaleThresh) :
    YVInputUniformSecond prob b := by
  have hpos : 0 < secondLevelAThr := by
    unfold secondLevelAThr; positivity
  exact Q.yvInputForW_uniform hpos hb_pos hb_le hScale

end FormalResearch.ModularBootstrap.FixedWeightBand

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip FormalResearch.SignUncertainty TwoLevel
  FormalResearch.ModularBootstrap.FixedWeightBand

variable {prob : FixedWeightProblem}

/-- The feasible set of the two-level problem (`wone:genlower`(2)): `T` is the threshold of a weakly feasible test `g`
(`g ≥ 0` on `[T, ∞)`) with `g(t₁) ≥ 0` at some `t₁` with `|t₁ - (ξ̄ c' + A₁ c'^{1/3})| ≤ R_off`. -/
def TwoLevelFeasible (prob : FixedWeightProblem) (A₁ R_off c' T : ℝ) : Prop :=
  ∃ (g : ℝ → ℝ) (t₁ : ℝ), |t₁ - (xiBar * c' + A₁ * c' ^ (1 / 3 : ℝ))| ≤ R_off ∧ 0 ≤ g t₁ ∧
    prob.IsWeaklyFeasible (c' / 12) T g

/-- **Violator family and chart coverage of the two-level problem** (Steps 0-4 of `wone:ftlfw` at the Clark pair; the
part of `wone:genlower`(2) feeding Theorem FT-2E).  At scale `0 < b ≤ b_V` with the band-feedback input at every
`A_thr ≤ secondLevelAThr`, for `K ⊂ (a₁, ∞)` compact and `R_off ≥ 0`, there are bootstrap parameters `P`, `W_top` and
`C₁ ≥ c_Q` with `max C₀ (tebC2 P) ≤ C₁` such that for every first level `u₁ ∈ K` (`A₁ = -c_* u₁`) and the chart
`foldChartOfLemmaQ Q`, `|z₂| ≤ U_C` for `C ≥ C₁`, and `ChartCoverage` and `TwoEdgeViolatorsHB` hold for
`TwoLevelFeasible prob (-c_* u₁) R_off` with `u_* = z₂(α(u₁))`. -/
theorem twoEdgeInstance_of_YVForClark (Q : LemmaQData prob) {b : ℝ} (hb_pos : 0 < b)
    (hb_le : b ≤ Q.bV) (hYV : YVInputUniformSecond prob b)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioi (airyZero 1)) {R_off : ℝ} (hR_off : 0 ≤ R_off) :
    ∃ (P : BootstrapParams) (W_top C₁ : ℝ), 0 ≤ W_top ∧ Q.cQ ≤ C₁ ∧
      max (foldChartOfLemmaQ Q).C0 (tebC2 P) ≤ C₁ ∧
      (∀ C : ℝ, C₁ ≤ C → ∀ u₁ ∈ K, |clarkNode (clarkAngle u₁) 2| ≤ (foldChartOfLemmaQ Q).U C) ∧
      ∀ u₁ ∈ K,
        (foldChartOfLemmaQ Q).ChartCoverage (TwoLevelFeasible prob (-cStar * u₁) R_off)
          (clarkNode (clarkAngle u₁) 2) C₁ ∧
        TwoEdgeViolatorsHB (foldChartOfLemmaQ Q) P W_top (TwoLevelFeasible prob (-cStar * u₁) R_off)
          (clarkNode (clarkAngle u₁) 2) C₁ := by
  obtain ⟨C_fb, c_YV, hC_fb, hc_YV, hYVall⟩ := hYV
  obtain ⟨c_Q1, C_gap, κ_gap, hc_Q1, hC_gap, hκ_gap, hQ1⟩ := lemmaQ_general_part1At Q.D hb_pos hb_le
  obtain ⟨c_Q3, hc_Q3, hQ3⟩ := lemmaQ_general_part3At Q.D hb_pos hb_le
  have hcS := cStar_pos
  set D₁ : ℝ := (R_off + 1) / cStar with hD₁_def
  have hD₁ : 0 < D₁ := by rw [hD₁_def]; positivity
  have hR_lim : Tendsto (fun c' : ℝ => chartACAt b c' ^ 2) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
      (mul_pos two_pos (pow_pos hb_pos 2))).congr'
        (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c' hc'; rw [chartACAt_sq b c' hc'])
  have hδ_lim : Tendsto (fun c' : ℝ => C_gap * Real.exp (-κ_gap * c')) atTop (𝓝 0) := by
    have ht : Tendsto (fun c' : ℝ => -κ_gap * c') atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    simpa only [mul_zero, Function.comp] using (Real.tendsto_exp_atBot.comp ht).const_mul C_gap
  have hρ_lim : Tendsto (fun c' : ℝ => D₁ * c' ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul D₁
  have hς_nn : ∀ᶠ c' : ℝ in atTop, 0 ≤ Q.sigma c' := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'; exact Q.sigma_nonneg hc'
  have hδ_nn : ∀ᶠ c' : ℝ in atTop, 0 ≤ C_gap * Real.exp (-κ_gap * c') :=
    Eventually.of_forall fun c' => mul_nonneg hC_gap.le (Real.exp_pos _).le
  obtain ⟨δ, κ, C₁', hδ, hδ_half, hκ, hC₁', c_1, hc_1, hQuant⟩ :=
    teb_quant_c1_clark_typeII_firstLevel Q.hC0 (fun c' => chartACAt b c' ^ 2) Q.sigma
      (fun c' => C_gap * Real.exp (-κ_gap * c')) (fun c' => D₁ * c' ^ (-(1 / 3 : ℝ)))
      hR_lim hς_nn Q.sigma_tendsto_zero hδ_nn hδ_lim hρ_lim hK hKsub
  obtain ⟨Cs, ws, κs, ηs, Ws, Rs, hCs, hws, hκs, hηs, hWs, hnodes⟩ :=
    pnodes_clark_constants_uniform hK hKsub hκ hC₁'
  obtain ⟨c_η, hc_η, hclose⟩ := clark_uT_close_firstLevel Q.hC0 (fun c' => chartACAt b c' ^ 2) Q.sigma
    (fun c' => C_gap * Real.exp (-κ_gap * c')) (fun c' => D₁ * c' ^ (-(1 / 3 : ℝ)))
    hR_lim hς_nn Q.sigma_tendsto_zero hδ_nn hδ_lim hρ_lim hK hKsub hηs
  obtain ⟨σ, hσ, hsin⟩ := exists_sin_lower_clarkAngle hK hKsub
  obtain ⟨μ₀, hμ₀, k₀, hk₀, hArcAll⟩ := clarkArcData_exists (prob := prob) hσ
  let P := bootstrapParamsForClark Q b hb_pos C_fb hC_fb C_gap κ_gap hκ_gap
    (lineCaW secondLevelAThr) μ₀ hμ₀ D₁ δ Cs ws κs ηs hD₁ hδ hCs hws hκs hηs
  have h_asymp := Q.sigma_arc_eventuallyFor hb_pos
  have h_rp : ∀ᶠ c' : ℝ in atTop, (k₀ : ℝ) + Rs + D₁ + 3 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) := by
    have ht : Tendsto (fun c' : ℝ => b ^ 2 * c' ^ (2 / 3 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop (pow_pos hb_pos 2)
    exact ht.eventually_ge_atTop _
  have h_xi : ∀ᶠ c' : ℝ in atTop, chartParams.C_xi * (Rs + D₁) ^ 2 ≤ c' ^ (1 / 3 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_ge_atTop _
  have h_all := h_asymp.and (h_rp.and (h_xi.and (eventually_ge_atTop
    (max Q.cQ (max c_YV (max c_Q1 (max c_Q3 (max c_1 (max c_η (max 1 (tebC2 P)))))))))))
  obtain ⟨C₀', hC₀'⟩ := eventually_atTop.mp h_all
  set Mx : ℝ := max Q.cQ (max c_YV (max c_Q1 (max c_Q3 (max c_1 (max c_η (max 1 (tebC2 P))))))) with hMx_def
  set C₁ : ℝ := max C₀' Mx with hC₁_def
  have hMx : Mx ≤ C₁ := le_max_right _ _
  have hC1_Q : Q.cQ ≤ C₁ := (le_max_left _ _).trans hMx
  have hC1_teb : tebC2 P ≤ C₁ := by
    refine le_trans ?_ hMx
    simp only [hMx_def, le_max_iff, le_refl, or_true]
  have hbig : ∀ {c' : ℝ}, C₁ ≤ c' →
      ((3 * π) ^ (12 : ℕ) ≤ c' ∧ 48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) ∧ Q.sigma c' ≤ 1 / 2 ∧
        Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1) ∧
      ((k₀ : ℝ) + Rs + D₁ + 3 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ)) ∧
      (chartParams.C_xi * (Rs + D₁) ^ 2 ≤ c' ^ (1 / 3 : ℝ)) ∧
      (Mx ≤ c') := by
    intro c' hc'
    exact hC₀' c' ((le_max_left _ _).trans hc')
  have hMx_parts : ∀ {c' : ℝ}, Mx ≤ c' → Q.cQ ≤ c' ∧ c_YV ≤ c' ∧ c_Q1 ≤ c' ∧ c_Q3 ≤ c' ∧ c_1 ≤ c' ∧
      c_η ≤ c' ∧ 1 ≤ c' ∧ tebC2 P ≤ c' := by
    intro c' h
    simpa only [hMx_def, max_le_iff, and_assoc] using h
  have hnodes_Rs_nn : ∀ u ∈ K, |clarkNode (clarkAngle u) 1| + 1 ≤ Rs := fun u hu => (hnodes u hu).2.2.2.2.2
  have hAC_big : ∀ {c' : ℝ}, C₁ ≤ c' → 48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) →
      chartACAt b c' ^ 2 ≤ Q.AC c' ^ 2 ∧ 96 ≤ chartACAt b c' ^ 2 := by
    intro c' hc' h48
    have hc'_pos : 0 < c' := by
      have := Q.hcQ_10000
      linarith [hC1_Q.trans hc']
    refine ⟨Q.ACAt_sq_le hb_pos.le hb_le hc'_pos.le, ?_⟩
    rw [chartACAt_sq b c' hc'_pos.le]; linarith
  -- the data at scale `c' ≥ C₁`
  have core : ∀ {c' T : ℝ}, C₁ ≤ c' → ∀ u₁ ∈ K, ∀ {g : ℝ → ℝ} {t₁ : ℝ},
      |t₁ - (xiBar * c' + (-cStar * u₁) * c' ^ (1 / 3 : ℝ))| ≤ R_off → 0 ≤ g t₁ →
      prob.IsWeaklyFeasible (c' / 12) T g →
      T < virasoroDeltaChart c' (clarkNode (clarkAngle u₁) 2) →
      clarkNode (clarkAngle u₁) 2 < virasoroUT c' T ∧ |virasoroUT c' T| ≤ Q.AC c' ^ 2 ∧
      virasoroDeltaChart c' (virasoroUT c' T) = T ∧
      ∃ I : BootstrapHBInstance P Ws, I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) ∧
        I.c = c' ∧ I.x_tilde = virasoroUT c' T - clarkNode (clarkAngle u₁) 2 := by
    intro c' T hc' u₁ hu₁K g t₁ ht₁ hgt₁ hg hT_lt
    obtain ⟨⟨h_c12, h_b48, hς_half, hς_arc⟩, h_rp', h_xi', hMx'⟩ := hbig hc'
    obtain ⟨hc'_Qenv, hc'_YV, hc'_Q1, hc'_Q3, hc'_1, hc'_η, hc'_one, hc'_teb⟩ := hMx_parts hMx'
    have hu₁ : airyZero 1 < u₁ := hKsub hu₁K
    obtain ⟨hCs₁, hws₁, hκs₁, hηs₁, hW₁, hRs₁⟩ := hnodes u₁ hu₁K
    have hc'_10000 : 10000 ≤ c' := Q.hcQ_10000.trans hc'_Qenv
    have hc'_pos : 0 < c' := by linarith
    obtain ⟨hz2_lo, hz2_hi⟩ := airyZero_two_lt_clarkNode_two hu₁
    obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
    obtain ⟨ha2_lo, ha2_hi⟩ := airyZero_two
    have hz1 : clarkNode (clarkAngle u₁) 1 = u₁ := (clarkAngle_spec hu₁).2
    have hz2_neg : clarkNode (clarkAngle u₁) 2 < 0 := by linarith
    obtain ⟨hA2_le, hA2_96⟩ := hAC_big hc' h_b48
    have hRs_ge := hRs₁
    have hRs_nn : 0 ≤ Rs := by linarith [abs_nonneg (clarkNode (clarkAngle u₁) 1)]
    have hk₀_nn : (0 : ℝ) ≤ (k₀ : ℝ) := Nat.cast_nonneg _
    have hRs_bd : Rs ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) := by linarith
    have hk₀_le : (k₀ : ℝ) ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) := by linarith
    have hz1_b : |clarkNode (clarkAngle u₁) 1| + 1 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) := hRs₁.trans hRs_bd
    have hu₁_abs : |u₁| + 1 ≤ Rs := by rw [← hz1]; exact hRs₁
    -- scale `b` facts
    obtain ⟨hM_pos, hdl_bd, hdl_half, hT_A2⟩ := hQ1 hc'_Q1 hg
    have hQ3_b := hQ3 hc'_Q3 hg
    set A2b : ℝ := chartACAt b c' ^ 2 with hA2b
    have hz2_a2 : -(A2b) < clarkNode (clarkAngle u₁) 2 := by linarith
    have hT_lt' : T < virasoroDeltaChart c' (-A2b) :=
      hT_lt.trans ((Q.deltaChart_strictAnti hc'_pos)
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hz2_a2)
    have huT_Ioo : virasoroUT c' T ∈ Ioo (-A2b) A2b := hQ3_b.2.2.1 hT_lt' hT_A2
    have hu_mem := Q.UT_between hc'_pos (a := -A2b) (b := A2b) (by linarith) hA2_le
      (by linarith) hT_A2.le
      (hT_lt.le.trans ((Q.deltaChart_strictAnti hc'_pos).antitoneOn
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hz2_a2.le))
    set u_T := virasoroUT c' T with hu_T
    have hz2_lt_uT : clarkNode (clarkAngle u₁) 2 < u_T := by
      by_contra hle
      have := (Q.deltaChart_strictAnti hc'_pos).antitoneOn
        ⟨by linarith [huT_Ioo.1], huT_Ioo.2.le.trans hA2_le⟩
        ⟨by linarith, by linarith⟩ (not_lt.mp hle)
      linarith [hu_mem.2]
    have hQ2 := Q.part2 hc'_Qenv hg.1 hM_pos
    -- the prescribed point
    have hu₁_pos_s : 0 ≤ D₁ * c' ^ (-(1 / 3 : ℝ)) := by positivity
    have hc13 : 1 ≤ c' ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hcm_le : c' ^ (-(1 / 3 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg hc'_pos.le]; exact inv_le_one_of_one_le₀ hc13
    have hs_le : D₁ * c' ^ (-(1 / 3 : ℝ)) ≤ D₁ := by
      calc D₁ * c' ^ (-(1 / 3 : ℝ)) ≤ D₁ * 1 := by gcongr
        _ = D₁ := mul_one _
    have hwin : |u₁| + D₁ * c' ^ (-(1 / 3 : ℝ)) ≤ Rs + D₁ := by linarith
    have hA2b_eq : A2b = 2 * (b ^ 2 * c' ^ (2 / 3 : ℝ)) := by
      rw [hA2b, chartACAt_sq b c' hc'_pos.le]; ring
    have hwin_AC : |u₁| + D₁ * c' ^ (-(1 / 3 : ℝ)) ≤ Q.AC c' ^ 2 := by
      have := abs_nonneg u₁
      linarith
    have hwin_err : chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) *
        (|u₁| + D₁ * c' ^ (-(1 / 3 : ℝ))) ^ 2 ≤ 1 := by
      have hCξ := chartParams.hCxi_nn
      have hp : 0 < c' ^ (1 / 3 : ℝ) := by linarith
      have h1 : (|u₁| + D₁ * c' ^ (-(1 / 3 : ℝ))) ^ 2 ≤ (Rs + D₁) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hwin 2
      have h2 : c' ^ (-(1 / 3 : ℝ)) * (c' ^ (1 / 3 : ℝ)) = 1 := by
        rw [mul_comm]; exact rpow_third_mul_rpow_neg_third hc'_pos
      calc chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * (|u₁| + D₁ * c' ^ (-(1 / 3 : ℝ))) ^ 2
          ≤ chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * (Rs + D₁) ^ 2 := by gcongr
        _ = c' ^ (-(1 / 3 : ℝ)) * (chartParams.C_xi * (Rs + D₁) ^ 2) := by ring
        _ ≤ c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ) := by gcongr
        _ = 1 := h2
    have ht₁' : |t₁ - (xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u₁)| ≤ R_off := by
      have e : xiBar * c' + (-cStar * u₁) * c' ^ (1 / 3 : ℝ) = xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u₁ := by
        ring
      rwa [e] at ht₁
    obtain ⟨ũ, hũ_near, hũ_Δ⟩ := Q.exists_chartPoint_near hc'_pos hR_off hD₁_def hwin_AC hwin_err ht₁'
    have hũ_abs : |ũ| ≤ Q.AC c' ^ 2 := by
      have : |ũ| ≤ |u₁| + D₁ * c' ^ (-(1 / 3 : ℝ)) := by
        calc |ũ| = |(ũ - u₁) + u₁| := by ring_nf
          _ ≤ |ũ - u₁| + |u₁| := abs_add_le _ _
          _ ≤ _ := by linarith
      exact this.trans hwin_AC
    have hũ_nn : 0 ≤ (psiTilde prob c' g (ũ : ℂ)).re := by
      have := (hQ2.2.1 ũ hũ_abs).2
      exact this.mp (by rw [hũ_Δ]; exact hgt₁)
    -- the `TE.0'` hypotheses
    have hnode1 : airyClarkNode (airyRatio u₁) 1 = u₁ := airyClarkNode_airyRatio_one hu₁
    have hnode2 : airyClarkNode (airyRatio u₁) 2 = clarkNode (clarkAngle u₁) 2 :=
      airyClarkNode_airyRatio_two hu₁
    have hh_half := hQ3_b.2.2.2.1 hT_lt' hT_A2.le
    rw [chartUT_eq_virasoroUT] at hh_half
    have hyp : QuantC1ClarkHyp Q.C0 A2b (Q.sigma c') (C_gap * Real.exp (-κ_gap * c'))
        (D₁ * c' ^ (-(1 / 3 : ℝ))) (airyRatio u₁) (psiTilde prob c' g) u_T ũ := by
      refine ⟨?_, ?_, ?_, ?_, huT_Ioo.2.le, ?_, ?_, ?_, ?_, ?_, hũ_nn⟩
      · exact hQ2.1.mono fun z hz => Q.closedBall_subset_psiDom hc'_pos
          (Metric.closedBall_subset_closedBall hA2_le hz)
      · intro x hx
        exact (hQ2.2.1 x ((abs_le.mpr hx).trans hA2_le)).1
      · intro u hu hcut
        exact hQ2.2.2 u (Metric.closedBall_subset_closedBall hA2_le hu) hcut
      · rw [hnode2]; exact hz2_lt_uT
      · intro x hx
        have hT_le : T ≤ virasoroDeltaChart c' x := by
          rw [← hu_mem.2]
          exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
            ⟨by linarith [hx.1, hA2_le], (hx.2.trans huT_Ioo.2.le).trans hA2_le⟩
            ⟨by linarith [huT_Ioo.1, hA2_le], huT_Ioo.2.le.trans hA2_le⟩ hx.2
        exact hQ3_b.1 x (abs_le.mpr ⟨hx.1, hx.2.trans huT_Ioo.2.le⟩) hT_le
      · have h0 : 0 ≤ C_gap * Real.exp (-κ_gap * c') := mul_nonneg hC_gap.le (Real.exp_pos _).le
        linarith [hQ3_b.2.1]
      · linarith [hh_half.2.2, hdl_bd]
      · intro R' hR'_mem hR'_uT
        have hT_le_R' : T ≤ virasoroDeltaChart c' (-R') := by
          rw [← hu_mem.2]
          exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
            ⟨by linarith [hR'_mem.2, hA2_le], by linarith [hR'_mem.1, hR'_mem.2, hA2_le]⟩
            ⟨by linarith [huT_Ioo.1, hA2_le], huT_Ioo.2.le.trans hA2_le⟩ hR'_uT
        exact (hQ3_b.2.2.2.2 R' hR'_mem.1 hR'_mem.2 hT_le_R').2.trans hdl_bd
      · rw [hnode1]; exact hũ_near
    have hB2 : QuantC1B2HoldsClark (airyRatio u₁) δ κ C₁' (psiTilde prob c' g) u_T :=
      hQuant c' hc'_1 u₁ hu₁K _ u_T ũ hyp
    have hx_eta : u_T - clarkNode (clarkAngle u₁) 2 ≤ ηs := by
      have := hclose c' hc'_η u₁ hu₁K _ u_T ũ hyp
      rwa [hnode2] at this
    have hA_le : |clarkNode (clarkAngle u₁) 2| + 1 ≤ secondLevelAThr := by
      unfold secondLevelAThr
      rw [abs_of_neg hz2_neg, abs_of_neg (by linarith : airyZero 2 < 0)]
      linarith
    have hYVat := hYVall (by positivity : 0 < |clarkNode (clarkAngle u₁) 2| + 1) hA_le
    have hC_line : lineCaW (|clarkNode (clarkAngle u₁) 2| + 1) ≤ lineCaW secondLevelAThr :=
      lineCaW_mono (by positivity) hA_le
    obtain ⟨I, hIL, hIc, hIx⟩ := bootstrapHB_of_YVForClark (u₁ := u₁) (b := b) (C_fb := C_fb) (c_YV := c_YV)
      (C_gap := C_gap) (κ_gap := κ_gap) (C_line := lineCaW secondLevelAThr) (μ₀ := μ₀) (D_1 := D₁)
      (δ := δ) (κ := κ) (C₁ := C₁') (Cs := Cs) (ws := ws) (κs := κs) (ηs := ηs) (W_top := Ws) (k₀ := k₀)
      hu₁ hC_line hb_pos hb_le hC_fb hC_gap hκ_gap hμ₀ hD₁ hδ hδ_half hκ hC₁' hCs hws hκs hηs hYVat
      hCs₁ hws₁ hκs₁ hηs₁ hW₁ (hArcAll _ (hsin u₁ hu₁K)) hc'_Qenv hc'_YV h_c12 h_b48 hk₀_le hz1_b
      hς_half hς_arc hg hdl_bd hdl_half hT_A2 hT_lt hB2 hx_eta hũ_near hũ_nn
    exact ⟨hz2_lt_uT, abs_le.mpr ⟨by linarith [huT_Ioo.1, hA2_le], huT_Ioo.2.le.trans hA2_le⟩,
      hu_mem.2, I, hIL, hIc, hIx⟩
  have hU : ∀ C : ℝ, C₁ ≤ C → ∀ u₁ ∈ K,
      |clarkNode (clarkAngle u₁) 2| ≤ (foldChartOfLemmaQ Q).U C := by
    intro C hC u₁ hu₁K
    obtain ⟨⟨-, h_b48, -, -⟩, -, -, -⟩ := hbig hC
    obtain ⟨hA2_le, hA2_96⟩ := hAC_big hC h_b48
    obtain ⟨hz2_lo, hz2_hi⟩ := airyZero_two_lt_clarkNode_two (hKsub hu₁K)
    obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
    obtain ⟨ha2_lo, ha2_hi⟩ := airyZero_two
    show |clarkNode (clarkAngle u₁) 2| ≤ Q.AC C ^ 2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hone : (1 : ℝ) ≤ C₁ := (hMx_parts hMx).2.2.2.2.2.2.1
  refine ⟨P, Ws, C₁, hWs, hC1_Q, max_le hone hC1_teb, hU, fun u₁ hu₁K => ⟨?_, ?_⟩⟩
  · intro C hC T hfeas hT
    obtain ⟨g, t₁, ht₁, hgt₁, hg⟩ := hfeas
    obtain ⟨h1, h2, h3, -⟩ := core hC u₁ hu₁K ht₁ hgt₁ hg hT
    exact ⟨virasoroUT C T, ⟨g, t₁, ht₁, hgt₁, hg⟩, h2, h1, h3⟩
  · intro C hC T u hv
    obtain ⟨⟨g, t₁, ht₁, hgt₁, hg⟩, huU, hlt, hΔ⟩ := hv
    have hc_pos : 0 < C := by
      have := Q.hcQ_10000
      linarith [hC1_Q.trans hC]
    have hIcc : ∀ x : ℝ, |x| ≤ Q.AC C ^ 2 → x ∈ Icc (-(Q.AC C ^ 2)) (Q.AC C ^ 2) :=
      fun x h => abs_le.mp h
    have hT_lt : T < virasoroDeltaChart C (clarkNode (clarkAngle u₁) 2) := by
      rw [← hΔ]
      exact (Q.deltaChart_strictAnti hc_pos) (hIcc _ (hU C hC u₁ hu₁K)) (hIcc _ huU) hlt
    obtain ⟨h1, h2, h3, I, hIL, hIc, hIx⟩ := core hC u₁ hu₁K ht₁ hgt₁ hg hT_lt
    have hu_eq : u = virasoroUT C T :=
      (Q.deltaChart_strictAnti hc_pos).injOn (hIcc _ huU) (hIcc _ h2) (hΔ.trans h3.symm)
    exact ⟨I, hIc, by rw [hIx, hu_eq], hIL⟩

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.twoEdgeInstance_of_YVForClark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoEdgeInstance_of_YVForClark

end FormalResearch.ModularBootstrap.FoldTip
