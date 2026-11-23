module

public import FormalResearch.TwoEdgeBootstrap.Bootstrap
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.ArcBounds

/-!
# Concrete Virasoro `BootstrapHBInstance` and Theorem `FT-L.FW` at `(P, Q) = (1, 0)`

Formalizes Steps 0–5 of Theorem `FT-L.FW` (`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`,
`wone:ftlfw`) at `(P, Q) = (1, 0)` (`N = Ai`, `m₀ = 1`, `t₁ = a₁`) from Lemma `Q` (`LemmaQ.lean`),
Proposition `TE.0'` (`QuantC1Airy.lean`), good-circle Airy quadrature (`ArcBounds.lean`), Theorem
`TE.2(4)` (`Bootstrap.lean`), and the unproved band bound Proposition `Y_V` (`vlo:YV`) packaged as
`YVInput` (`QuadratureBounds.lean`).

## Main definitions and results
* `virasoroBootstrapParams`: concrete `BootstrapParams` for `(P, Q) = (1, 0)` on Virasoro.
* `virasoro_band_sums_le`: unconditional mass/tail bounds `B₁ ≤ 1`, `B₂ ≤ 2` from Lemma `Q(1),(3)`.
* `virasoro_bootstrapHB_of_YV`: builds `BootstrapHBInstance (virasoroBootstrapParams ...) 0`
  together with `(B3)` from `YVInputAt`, Lemma `Q`, `QuantC1B2Holds`, and `ArcBounds`.
* `theoremFTLFW_oneZero_of_YV`: Theorem `FT-L.FW` at `(P, Q) = (1, 0)` assuming `YVInput`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.Special
open FormalResearch.TwoEdgeBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.TipFront

/-! ### Section 1: Concrete `BootstrapParams` and Large-`c'` Asymptotic Thresholds -/

/-- Concrete `BootstrapParams` for `(P, Q) = (1, 0)` on Virasoro at scale `b > 0`. -/
noncomputable def virasoroBootstrapParamsFor
    (b : ℝ) (hb : 0 < b)
    (C_fb : ℝ) (hC_fb : 1 ≤ C_fb)
    (C_gap κ_gap : ℝ) (_hC_gap : 0 < C_gap) (hκ_gap : 0 < κ_gap) :
    BootstrapParams where
  b := b
  C_a := max virasoroArcCovConst (4 * Real.exp (6 / 5) + 3 * virasoroEnvC0)
  C_unc := virasoroArcUncConst
  C_1 := quantC1C1
  w_star := quantC1WStar
  κ_star := quantC1KappaStar
  C_α := 0
  C_fb := C_fb
  D_1 := 1
  η_0 := quantC1Eta0
  δ_star := quantC1DeltaStar
  κ := κ_gap
  C_0 := max 1 C_gap
  C_L := 4 * C_fb
  γ := 1
  k_0 := 5
  hb := hb
  hCa := le_trans virasoroArcCovConst_pos.le (le_max_left _ _)
  hCunc := virasoroArcUncConst_pos.le
  hC1 := quantC1C1_pos
  hw_star := quantC1WStar_pos
  hκ_star := quantC1KappaStar_pos
  hCα := le_rfl
  hCfb := hC_fb
  hD1 := zero_le_one
  hη0 := quantC1Eta0_pos
  hδ_star := quantC1DeltaStar_pos
  hκ := hκ_gap
  hC0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  hCL := by linarith
  hγ := zero_le_one
  hk0 := by omega

/-- Concrete `BootstrapParams` for `(P, Q) = (1, 0)` on Virasoro (`N = Ai`, `m₀ = 1`, `k₀ = 5`). -/
noncomputable def virasoroBootstrapParams
    (C_fb : ℝ) (hC_fb : 1 ≤ C_fb)
    (C_gap κ_gap : ℝ) (hC_gap : 0 < C_gap) (hκ_gap : 0 < κ_gap) :
    BootstrapParams :=
  virasoroBootstrapParamsFor virasoroBV virasoroBV_pos C_fb hC_fb C_gap κ_gap hC_gap hκ_gap

private lemma rpow_neg_inv_mul_log_le {c' α : ℝ} (hc' : 1 ≤ c') (hα : 0 < α) :
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

private lemma virasoroSigma_tendsto_zero :
    Tendsto virasoroSigma atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := virasoroSigma) (g := fun _ => (0 : ℝ))
    (h := fun c' => (6 * virasoroEnvC1) * c' ^ (-(1 / 6 : ℝ))) tendsto_const_nhds ?_ ?_ ?_
  · have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul
      (6 * virasoroEnvC1)
    simpa only [mul_zero] using h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
    exact virasoroSigma_nonneg hc'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
    unfold virasoroSigma
    have hbd := rpow_neg_inv_mul_log_le hc' (by norm_num : (0 : ℝ) < 1 / 3)
    have hrw : (2 / (1 / 3 : ℝ)) * c' ^ (-((1 / 3 : ℝ) / 2)) =
        6 * c' ^ (-(1 / 6 : ℝ)) := by norm_num
    rw [hrw] at hbd
    calc virasoroEnvC1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c'
        = virasoroEnvC1 * (c' ^ (-(1 / 3 : ℝ)) * Real.log c') := by ring
      _ ≤ virasoroEnvC1 * (6 * c' ^ (-(1 / 6 : ℝ))) :=
          mul_le_mul_of_nonneg_left hbd virasoroEnvC1_pos.le
      _ = (6 * virasoroEnvC1) * c' ^ (-(1 / 6 : ℝ)) := by ring

private lemma virasoroSigma_arc_eventuallyFor {b : ℝ} (hb : 0 < b) :
    ∀ᶠ c' : ℝ in atTop,
      (3 * π) ^ (12 : ℕ) ≤ c' ∧
      48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) ∧
      virasoroSigma c' ≤ 1 / 2 ∧
      virasoroSigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1 := by
  have h1 : ∀ᶠ c' : ℝ in atTop, (3 * π) ^ (12 : ℕ) ≤ c' :=
    eventually_ge_atTop _
  have h2 : ∀ᶠ c' : ℝ in atTop, 48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) := by
    have ht : Tendsto (fun c' : ℝ => b ^ 2 * c' ^ (2 / 3 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
        (pow_pos hb 2)
    exact ht.eventually_ge_atTop 48
  have h3 : ∀ᶠ c' : ℝ in atTop, virasoroSigma c' ≤ 1 / 2 :=
    virasoroSigma_tendsto_zero.eventually (Iic_mem_nhds (by norm_num))
  have h4 : ∀ᶠ c' : ℝ in atTop,
      virasoroSigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1 := by
    let M : ℝ := 24 * virasoroEnvC1 * (3 * π * √2 * b + 1)
    have hM_nn : 0 ≤ M := by
      dsimp [M]; have := virasoroEnvC1_pos; positivity
    have ht : Tendsto (fun c' : ℝ => M * c' ^ (-(1 / 24 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 24)).const_mul M
    filter_upwards [eventually_ge_atTop (1 : ℝ), ht.eventually (Iic_mem_nhds zero_lt_one)] with
        c' hc' hMc'
    have hc'_pos : 0 < c' := by linarith
    have hlog := rpow_neg_inv_mul_log_le hc' (by norm_num : (0 : ℝ) < 1 / 12)
    have hrw : (2 / (1 / 12 : ℝ)) * c' ^ (-((1 / 12 : ℝ) / 2)) = 24 * c' ^ (-(1 / 24 : ℝ)) := by
      norm_num
    rw [hrw] at hlog
    have h12 : c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 4 : ℝ) = c' ^ (-(1 / 12 : ℝ)) := by
      rw [← Real.rpow_add hc'_pos]; norm_num
    have hc13_le : c' ^ (-(1 / 3 : ℝ)) ≤ c' ^ (-(1 / 12 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc' (by norm_num)
    have hlog_nn : 0 ≤ Real.log c' := Real.log_nonneg hc'
    have hsig_le : virasoroSigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤
        virasoroEnvC1 * (3 * π * √2 * b + 1) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := by
      unfold virasoroSigma
      have hterm1 : (virasoroEnvC1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c') *
          (3 * π * √2 * b * c' ^ (1 / 4 : ℝ)) =
          virasoroEnvC1 * (3 * π * √2 * b) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := by
        calc (virasoroEnvC1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c') *
              (3 * π * √2 * b * c' ^ (1 / 4 : ℝ))
            = virasoroEnvC1 * (3 * π * √2 * b) *
                ((c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 4 : ℝ)) * Real.log c') := by ring
          _ = virasoroEnvC1 * (3 * π * √2 * b) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := by
              rw [h12]
      have hterm2 : virasoroEnvC1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c' ≤
          virasoroEnvC1 * 1 * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := by
        have := virasoroEnvC1_pos.le
        nlinarith [mul_le_mul_of_nonneg_right hc13_le hlog_nn]
      linarith
    have hbound : virasoroEnvC1 * (3 * π * √2 * b + 1) *
        (c' ^ (-(1 / 12 : ℝ)) * Real.log c') ≤ M * c' ^ (-(1 / 24 : ℝ)) := by
      have hpos : 0 ≤ virasoroEnvC1 * (3 * π * √2 * b + 1) := by
        have := virasoroEnvC1_pos; positivity
      calc virasoroEnvC1 * (3 * π * √2 * b + 1) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c')
          ≤ virasoroEnvC1 * (3 * π * √2 * b + 1) * (24 * c' ^ (-(1 / 24 : ℝ))) :=
            mul_le_mul_of_nonneg_left hlog hpos
        _ = M * c' ^ (-(1 / 24 : ℝ)) := by dsimp [M]; ring
    exact hsig_le.trans (hbound.trans hMc')
  exact h1.and (h2.and (h3.and h4))

private lemma virasoroSigma_arc_eventually :
    ∀ᶠ c' : ℝ in atTop,
      (3 * π) ^ (12 : ℕ) ≤ c' ∧
      48 ≤ virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ) ∧
      virasoroSigma c' ≤ 1 / 2 ∧
      virasoroSigma c' * (3 * π * √2 * virasoroBV * c' ^ (1 / 4 : ℝ) + 1) ≤ 1 :=
  virasoroSigma_arc_eventuallyFor virasoroBV_pos

/-! ### Section 2: Unconditional Band-Moment Bounds `B₁ ≤ 1`, `B₂ ≤ 2` -/

/-- Unconditional band bounds `B₁ ≤ 1` and `B₂ ≤ 2` (hence `B₁ + B₂ ≤ 3`) for any weakly feasible
`g` with `T ∈ [Δ(-R), Δ(-A_thr)]` and `virasoroDeltaLobe c' g < 1 / 2` (from Lemma `Q(3)`). -/
lemma virasoro_band_sums_le {c' R T : ℝ} (hc' : virasoroCQEnv ≤ c')
    (hR_thr : virasoroAThr ≤ R) (hR_ub : R + 1 ≤ virasoroAC c' ^ 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hdl : virasoroDeltaLobe c' g < 1 / 2)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr)) :
    virasoroBandB1 c' R T g ≤ 1 ∧ virasoroBandB2 c' R g ≤ 2 := by
  have hc'_10000 : 10000 ≤ c' :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans hc')
  have hc'_24 : 24 ≤ c' := by linarith
  have hc'_pos : 0 < c' := by linarith
  have ha : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero ha hg.1 hg.2.1
  have hM_nn : 0 ≤ (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ := inv_nonneg.mpr hM_pos.le
  have hR_pos : 0 < R := lt_of_lt_of_le virasoroAThr_pos hR_thr
  have hA2_nn : 0 ≤ virasoroAC c' ^ 2 := sq_nonneg _
  have hu_mem := virasoroUT_between hc'_pos
    (by linarith : -(virasoroAC c' ^ 2) ≤ -R) hA2_nn (by linarith : -R ≤ 0) hT_lo
    (hT_hi.trans ((virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [virasoroAThr_pos]⟩
      (by linarith)))
  set u_T := virasoroUT c' T
  have hΔ_uT : virasoroDeltaChart c' u_T = T := hu_mem.2
  have hRm : -R ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) := ⟨by linarith, by linarith⟩
  have hΔ_T_le : T ≤ virasoroDeltaChart c' (-R) := by
    rw [← hΔ_uT]
    exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn hRm
      ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2]⟩ hu_mem.1.1
  have hΨ_cont_all : ContinuousOn (fun v : ℝ => (virasoroPsiTilde c' g (v : ℂ)).re)
      (Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2)) :=
    Complex.continuous_re.comp_continuousOn
      ((virasoroPsiTilde_analyticOnNhd (by linarith) hg.1).continuousOn.comp
        continuous_ofReal.continuousOn fun v hv => virasoro_closedBall_subset_psiDom hc'_pos (by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr hv))
  have hL1_A2 : ∫ u in (-(virasoroAC c' ^ 2))..(virasoroAC c' ^ 2),
      ‖virasoroPsiTilde c' g (u : ℂ)‖ ≤ 1 := (lemmaQ_part3 hc' hg).2.1
  have h_abs_int_le : ∀ {a b : ℝ}, -(virasoroAC c' ^ 2) ≤ a → a ≤ b → b ≤ virasoroAC c' ^ 2 →
      |∫ u in a..b, (virasoroPsiTilde c' g (u : ℂ)).re| ≤ 1 := by
    intro a b ha0 hab hb0
    have hnorm_cont : ContinuousOn (fun u : ℝ => ‖virasoroPsiTilde c' g (u : ℂ)‖)
        (Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2)) :=
      continuous_norm.comp_continuousOn
        ((virasoroPsiTilde_analyticOnNhd (by linarith) hg.1).continuousOn.comp
          continuous_ofReal.continuousOn fun v hv => virasoro_closedBall_subset_psiDom hc'_pos (by
            rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
            exact abs_le.mpr hv))
    have h1 : |∫ u in a..b, (virasoroPsiTilde c' g (u : ℂ)).re| ≤
        ∫ u in a..b, ‖virasoroPsiTilde c' g (u : ℂ)‖ := by
      calc |∫ u in a..b, (virasoroPsiTilde c' g (u : ℂ)).re|
          ≤ ∫ u in a..b, |(virasoroPsiTilde c' g (u : ℂ)).re| := by
            simpa [Real.norm_eq_abs] using
              intervalIntegral.norm_integral_le_integral_norm
                (f := fun u : ℝ => (virasoroPsiTilde c' g (u : ℂ)).re) (μ := volume) hab
        _ ≤ ∫ u in a..b, ‖virasoroPsiTilde c' g (u : ℂ)‖ :=
            intervalIntegral.integral_mono_on hab
              ((continuous_abs.comp_continuousOn (hΨ_cont_all.mono (Icc_subset_Icc ha0 hb0))).intervalIntegrable_of_Icc hab)
              ((hnorm_cont.mono (Icc_subset_Icc ha0 hb0)).intervalIntegrable_of_Icc hab)
              fun u _ => Complex.abs_re_le_norm _
    have hsub1 : ∫ u in a..b, ‖virasoroPsiTilde c' g (u : ℂ)‖ ≤
        ∫ u in (-(virasoroAC c' ^ 2))..(virasoroAC c' ^ 2), ‖virasoroPsiTilde c' g (u : ℂ)‖ := by
      have hsp1 := intervalIntegral.integral_add_adjacent_intervals
        ((hnorm_cont.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc (μ := volume) ha0)
        ((hnorm_cont.mono (Icc_subset_Icc ha0 le_rfl)).intervalIntegrable_of_Icc (μ := volume) (by linarith))
      have hsp2 := intervalIntegral.integral_add_adjacent_intervals
        ((hnorm_cont.mono (Icc_subset_Icc ha0 hb0)).intervalIntegrable_of_Icc (μ := volume) hab)
        ((hnorm_cont.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc (μ := volume) hb0)
      have hnn1 : 0 ≤ ∫ u in (-(virasoroAC c' ^ 2))..a, ‖virasoroPsiTilde c' g (u : ℂ)‖ :=
        intervalIntegral.integral_nonneg ha0 fun _ _ => norm_nonneg _
      have hnn2 : 0 ≤ ∫ u in b..(virasoroAC c' ^ 2), ‖virasoroPsiTilde c' g (u : ℂ)‖ :=
        intervalIntegral.integral_nonneg hb0 fun _ _ => norm_nonneg _
      linarith
    exact h1.trans (hsub1.trans hL1_A2)
  -- Part 1: `B₁ ≤ 1`
  have hB1 : virasoroBandB1 c' R T g ≤ 1 := by
    have hcont_t : ContinuousOn (fun t : ℝ => g t * virasoroProblem.cardyV (c' / 12) t)
        (Icc T (virasoroDeltaChart c' (-R))) := by
      have hT_nn : 0 ≤ T :=
        (virasoroDeltaChart_pos hc'_pos (by rw [abs_zero]; exact hA2_nn)).le.trans hT_lo
      exact (hg.1.cont.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
        (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hT_nn))
    have hi_num : IntervalIntegrable
        (fun t : ℝ => (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t))
        volume T (virasoroDeltaChart c' (-R)) := by
      refine ContinuousOn.intervalIntegrable_of_Icc hΔ_T_le ?_
      refine ContinuousOn.mul ?_ hcont_t
      have hcont_u : ContinuousOn (virasoroUT c') (Icc T (virasoroDeltaChart c' (-R))) := by
        intro t ht
        have hΔ0 : virasoroDeltaChart c' 0 ≤ t := hT_lo.trans ht.1
        have hu_t := virasoroUT_between hc'_pos (by linarith : -(virasoroAC c' ^ 2) ≤ -R)
          hA2_nn (by linarith : -R ≤ 0) hΔ0 ht.2
        have ht_open : ((t / c' : ℝ) : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
          rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have hmem := virasoroDeltaChart_div_mem hc'_pos (abs_le.mpr ⟨hu_t.1.1.trans' (by linarith), hu_t.1.2.trans (by linarith)⟩)
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
        (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t) ≤
        ∫ t in T..(virasoroDeltaChart c' (-R)),
          R * (g t * virasoroProblem.cardyV (c' / 12) t) := by
      refine intervalIntegral.integral_mono_on hΔ_T_le hi_num
        (hcont_t.const_mul R |>.intervalIntegrable_of_Icc hΔ_T_le) fun t ht => ?_
      have hΔ0 : virasoroDeltaChart c' 0 ≤ t := hT_lo.trans ht.1
      have hu_t := virasoroUT_between hc'_pos (by linarith : -(virasoroAC c' ^ 2) ≤ -R)
        hA2_nn (by linarith : -R ≤ 0) hΔ0 ht.2
      have ht_nn : 0 ≤ t :=
        (virasoroDeltaChart_pos hc'_pos (by rw [abs_zero]; exact hA2_nn)).le.trans hΔ0
      have hgv_nn : 0 ≤ g t * virasoroProblem.cardyV (c' / 12) t :=
        mul_nonneg (hg.2.2.2 t ht.1) (virasoroProblem.cardyV_nonneg ha ht_nn)
      exact mul_le_mul_of_nonneg_right (by linarith [hu_t.1.1]) hgv_nn
    have h_cov := virasoroPsiTilde_integral_eq hc'_24 hg.1
      (by linarith : -(virasoroAC c' ^ 2) ≤ -R) (by linarith [hu_mem.1.2]) hu_mem.1.1
    rw [hΔ_uT] at h_cov
    have h_abs := (abs_le.mp (h_abs_int_le (by linarith) hu_mem.1.1 (by linarith [hu_mem.1.2]))).2
    unfold virasoroBandB1
    calc R⁻¹ * (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
          ∫ t in T..(virasoroDeltaChart c' (-R)),
            (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t)
        ≤ R⁻¹ * (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
            ∫ t in T..(virasoroDeltaChart c' (-R)),
              R * (g t * virasoroProblem.cardyV (c' / 12) t) :=
          mul_le_mul_of_nonneg_left h_int_mono (mul_nonneg (inv_nonneg.mpr hR_pos.le) hM_nn)
      _ = (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
            ∫ t in T..(virasoroDeltaChart c' (-R)),
              g t * virasoroProblem.cardyV (c' / 12) t := by
          rw [intervalIntegral.integral_const_mul]; field_simp [hR_pos.ne']
      _ = ∫ u in (-R)..u_T, (virasoroPsiTilde c' g (u : ℂ)).re := h_cov.symm
      _ ≤ 1 := h_abs
  -- Part 2: `B₂ ≤ 2`
  have hB2 : virasoroBandB2 c' R g ≤ 2 := by
    have hgv_int : IntegrableOn (fun t => g t * virasoroProblem.cardyV (c' / 12) t) (Ioi 0) :=
      hg.1.int_cardy.norm.mono'
        (((hg.1.cont.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
          Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
        (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_abs])
    have h_vac_le : ∫ t in Ioi (0 : ℝ), g t * virasoroProblem.cardyV (c' / 12) t ≤ 0 := by
      have hv := hg.2.2.1; unfold FixedWeightProblem.gVac at hv; nlinarith [Real.pi_pos]
    set t_lo := virasoroDeltaChart c' (virasoroAC c' ^ 2)
    set t_hi := virasoroDeltaChart c' (-R)
    have ht_lo_pos : 0 < t_lo := virasoroDeltaChart_pos hc'_pos (abs_of_nonneg hA2_nn).le
    have ht_lo_hi : t_lo ≤ t_hi :=
      (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn hRm ⟨by linarith, le_rfl⟩ (by linarith)
    have hsp1 : ∫ t in Ioi (0 : ℝ), g t * virasoroProblem.cardyV (c' / 12) t =
        (∫ t in Ioc 0 t_lo, g t * virasoroProblem.cardyV (c' / 12) t) +
          (∫ t in Ioc t_lo t_hi, g t * virasoroProblem.cardyV (c' / 12) t) +
          ∫ t in Ioi t_hi, g t * virasoroProblem.cardyV (c' / 12) t := by
      have h1 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hgv_int.mono_set Ioc_subset_Ioi_self) (hgv_int.mono_set (Ioi_subset_Ioi ht_lo_pos.le))
      rw [Ioc_union_Ioi_eq_Ioi ht_lo_pos.le] at h1
      have h2 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((hgv_int.mono_set (Ioi_subset_Ioi ht_lo_pos.le)).mono_set Ioc_subset_Ioi_self)
        (hgv_int.mono_set (Ioi_subset_Ioi (ht_lo_pos.le.trans ht_lo_hi)))
      rw [Ioc_union_Ioi_eq_Ioi ht_lo_hi] at h2
      linarith [h1, h2]
    have h_lobe_eq : -(∫ t in Ioc 0 t_lo, g t * virasoroProblem.cardyV (c' / 12) t) ≤
        ∫ t in (0 : ℝ)..t_lo, |g t| * virasoroProblem.cardyV (c' / 12) t := by
      rw [← intervalIntegral.integral_of_le ht_lo_pos.le, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_mono_on ht_lo_pos.le
        (((hg.1.cont.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).neg.intervalIntegrable_of_Icc ht_lo_pos.le)
        (((hg.1.cont.abs.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos.le)
        fun t ht => ?_
      have hV := virasoroProblem.cardyV_nonneg ha ht.1
      calc -(g t * virasoroProblem.cardyV (c' / 12) t) = (-g t) * virasoroProblem.cardyV (c' / 12) t := by ring
        _ ≤ |g t| * virasoroProblem.cardyV (c' / 12) t := mul_le_mul_of_nonneg_right (neg_le_abs _) hV
    have hIci_Ioi : ∫ t in Ici t_hi, g t * virasoroProblem.cardyV (c' / 12) t =
        ∫ t in Ioi t_hi, g t * virasoroProblem.cardyV (c' / 12) t :=
      setIntegral_congr_set Ioi_ae_eq_Ici.symm
    have h_sum_t : ∫ t in Ici t_hi, g t * virasoroProblem.cardyV (c' / 12) t ≤
        -(∫ t in t_lo..t_hi, g t * virasoroProblem.cardyV (c' / 12) t) +
          ∫ t in (0 : ℝ)..t_lo, |g t| * virasoroProblem.cardyV (c' / 12) t := by
      rw [intervalIntegral.integral_of_le ht_lo_hi, hIci_Ioi]
      linarith only [h_vac_le, hsp1, h_lobe_eq]
    have hmul := mul_le_mul_of_nonneg_left h_sum_t hM_nn
    have h_cov := virasoroPsiTilde_integral_eq hc'_24 hg.1
      (by linarith : -(virasoroAC c' ^ 2) ≤ -R) le_rfl (by linarith)
    have h_abs := (abs_le.mp (h_abs_int_le (a := -R) (b := virasoroAC c' ^ 2)
      (by linarith) (by linarith) le_rfl)).1
    unfold virasoroBandB2
    rw [mul_add, mul_neg] at hmul
    have hdl_eq : (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (0 : ℝ)..t_lo, |g t| * virasoroProblem.cardyV (c' / 12) t =
        virasoroDeltaLobe c' g := rfl
    linarith [hmul, h_cov, h_abs, hdl_eq, hdl]
  exact ⟨hB1, hB2⟩

/-! ### Section 3: Node-Sum Lower Bounds (`hP_nodes_lb_hb` and `P_theta_bound`) -/

private lemma psiTilde_real_mv_sub {c' R_dom : ℝ} {g : ℝ → ℝ}
    (hΨ_an : AnalyticOnNhd ℂ (virasoroPsiTilde c' g) (closedBall (0 : ℂ) R_dom))
    (_hΨ_real : ∀ x ∈ Icc (-R_dom) R_dom, (virasoroPsiTilde c' g (x : ℂ)).im = 0)
    {a b : ℝ} (hab : a ≤ b) (ha : -R_dom ≤ a) (hb : b ≤ R_dom) (C₁ : ℝ) (_hC1_nn : 0 ≤ C₁)
    (hder : ∀ x ∈ Icc a b, ‖deriv (virasoroPsiTilde c' g) (x : ℂ)‖ ≤ C₁) :
    |(virasoroPsiTilde c' g (b : ℂ)).re - (virasoroPsiTilde c' g (a : ℂ)).re| ≤ C₁ * (b - a) := by
  have hΨ_diff : ∀ t ∈ Icc a b,
      HasDerivAt (fun x : ℝ => (virasoroPsiTilde c' g (x : ℂ)).re)
        ((deriv (virasoroPsiTilde c' g) (t : ℂ)).re) t := by
    intro t ht
    have ht_ball : (t : ℂ) ∈ closedBall (0 : ℂ) R_dom := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hc : HasDerivAt (virasoroPsiTilde c' g) (deriv (virasoroPsiTilde c' g) (t : ℂ)) (t : ℂ) :=
      (hΨ_an (t : ℂ) ht_ball).differentiableAt.hasDerivAt
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc.comp_ofReal
  have hcont_der : ContinuousOn (fun t : ℝ => (deriv (virasoroPsiTilde c' g) (t : ℂ)).re) (Icc a b) := by
    refine Complex.continuous_re.comp_continuousOn ?_
    refine hΨ_an.deriv.continuousOn.comp continuous_ofReal.continuousOn fun t ht => ?_
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hftc : (virasoroPsiTilde c' g (b : ℂ)).re - (virasoroPsiTilde c' g (a : ℂ)).re =
      ∫ t in a..b, (deriv (virasoroPsiTilde c' g) (t : ℂ)).re :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hΨ_diff t (Set.uIcc_of_le hab ▸ ht))
      (hcont_der.intervalIntegrable_of_Icc hab)).symm
  have h_norm := intervalIntegral.norm_integral_le_integral_norm
    (f := fun t : ℝ => (deriv (virasoroPsiTilde c' g) (t : ℂ)).re) (μ := volume) hab
  rw [← hftc, Real.norm_eq_abs] at h_norm
  have hint_bd : ∫ t in a..b, ‖(deriv (virasoroPsiTilde c' g) (t : ℂ)).re‖ ≤
      ∫ _ in a..b, C₁ := by
    refine intervalIntegral.integral_mono_on hab
      ((continuous_norm.comp_continuousOn hcont_der).intervalIntegrable_of_Icc hab)
      (intervalIntegrable_const) fun t ht => ?_
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hder t ht)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint_bd
  have hle : |(virasoroPsiTilde c' g (b : ℂ)).re - (virasoroPsiTilde c' g (a : ℂ)).re| ≤
      (b - a) * C₁ := h_norm.trans hint_bd
  linarith [hle]

private lemma virasoro_pnodes_lower_aux {c' R T ℓ : ℝ} {N : ℕ}
    (hc' : virasoroCQEnv ≤ c') (hR_48 : 48 ≤ R) (hR_ub : R + 1 ≤ virasoroAC c' ^ 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr))
    (hT_A2 : virasoroDeltaChart c' (virasoroAC c' ^ 2) ≤ T)
    (hT_a1 : T < virasoroDeltaChart c' (airyZero 1))
    (hB2 : QuantC1B2Holds (virasoroPsiTilde c' g) (virasoroUT c' T))
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R))
    (hℓ_nn : 0 ≤ ℓ) (hℓ_le : ℓ ≤ min quantC1DeltaStar (min quantC1Eta0 1))
    (k : ℕ) (_hk_ub : (k : ℝ) ≤ R / 5) :
    (1 + airyZero 1 / R) ^ (k + 1) *
        (virasoroPsiTilde c' g ((airyZero 1 + ℓ : ℝ) : ℂ)).re / quantC1WStar ≤
      virasoroPNodes c' R ℓ g k N := by
  have hc'_10000 : 10000 ≤ c' :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans hc')
  have hc'_pos : 0 < c' := by linarith
  have hR_pos : 0 < R := by linarith
  have hA2_nn : 0 ≤ virasoroAC c' ^ 2 := sq_nonneg _
  obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
  obtain ⟨ha2_lo, ha2_hi⟩ := airyZero_two
  have hAThr_eq : virasoroAThr = -airyZero 1 + 1 := by
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]
  have hu_mem := virasoroUT_between hc'_pos
    (by linarith : -(virasoroAC c' ^ 2) ≤ -virasoroAThr)
    (le_rfl : virasoroAC c' ^ 2 ≤ virasoroAC c' ^ 2)
    (by linarith : -virasoroAThr ≤ virasoroAC c' ^ 2) hT_A2 hT_hi
  set u_T := virasoroUT c' T
  have ha1_lt_uT : airyZero 1 < u_T := by
    by_contra hle
    have := (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [hu_mem.1.1], hu_mem.1.2⟩ ⟨by linarith, by linarith⟩ (not_lt.mp hle)
    linarith [hT_a1, hu_mem.2]
  have huT_le_a1_half : u_T ≤ airyZero 1 + 1 / 2 := by
    have h1 := hB2.1
    have h2 : min quantC1DeltaStar (min quantC1Eta0 1) ≤ 1 / 2 :=
      (min_le_left _ _).trans quantC1DeltaStar_le
    linarith
  have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 N := by
    rw [Finset.mem_Icc]
    refine ⟨le_rfl, (hN 1 le_rfl).mpr (by linarith)⟩
  have h_sum_split : virasoroPNodes c' R ℓ g k N =
      (virasoroShiftedFun c' R ℓ g k (airyZero 1 : ℂ)).re / airyAi' (airyZero 1) ^ 2 +
      ∑ n ∈ (Finset.Icc 1 N).erase 1,
        (virasoroShiftedFun c' R ℓ g k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2 := by
    unfold virasoroPNodes
    exact (Finset.add_sum_erase _ _ h1_mem).symm
  have h_tail_nn : 0 ≤ ∑ n ∈ (Finset.Icc 1 N).erase 1,
      (virasoroShiftedFun c' R ℓ g k (airyZero n : ℂ)).re / airyAi' (airyZero n) ^ 2 := by
    refine Finset.sum_nonneg fun n hn => ?_
    rw [Finset.mem_erase, Finset.mem_Icc] at hn
    have hn2 : 2 ≤ n := by omega
    have han_negR : -R < airyZero n := by
      have := (hN n hn.2.1).mp hn.2.2; linarith
    have han_le_a2 : airyZero n ≤ airyZero 2 :=
      airyZero_anti (by omega) (by omega : 2 ≤ n)
    have hℓ_half : ℓ ≤ 1 / 2 := hℓ_le.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
    have harg_le : airyZero n + ℓ ≤ u_T := by linarith
    have harg_abs : |airyZero n + ℓ| ≤ virasoroAC c' ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hT_le_Δ : T ≤ virasoroDeltaChart c' (airyZero n + ℓ) := by
      rw [← hu_mem.2]
      exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
        (abs_le.mp harg_abs) ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2]⟩ harg_le
    have hΨ_nn : 0 ≤ (virasoroPsiTilde c' g ((airyZero n + ℓ : ℝ) : ℂ)).re :=
      (lemmaQ_part3 hc' hg).1 (airyZero n + ℓ) harg_abs hT_le_Δ
    have hpow_nn : 0 ≤ (1 + airyZero n / R) ^ (k + 1) := by
      refine pow_nonneg ?_ _
      rw [show (1 : ℝ) + airyZero n / R = (R + airyZero n) / R by field_simp [hR_pos.ne'] ]
      exact div_nonneg (by linarith) hR_pos.le
    have hrew : (virasoroShiftedFun c' R ℓ g k (airyZero n : ℂ)).re =
        (1 + airyZero n / R) ^ (k + 1) *
          (virasoroPsiTilde c' g ((airyZero n + ℓ : ℝ) : ℂ)).re := by
      unfold virasoroShiftedFun
      have h1 : ((1 + (airyZero n : ℂ) / (R : ℂ)) ^ (k + 1)) =
          (((1 + airyZero n / R) ^ (k + 1) : ℝ) : ℂ) := by push_cast; ring
      rw [h1, show (airyZero n : ℂ) + (ℓ : ℂ) = ((airyZero n + ℓ : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [hrew]
    exact div_nonneg (mul_nonneg hpow_nn hΨ_nn) (sq_nonneg _)
  have h1_rew : (virasoroShiftedFun c' R ℓ g k (airyZero 1 : ℂ)).re / airyAi' (airyZero 1) ^ 2 =
      (1 + airyZero 1 / R) ^ (k + 1) *
        (virasoroPsiTilde c' g ((airyZero 1 + ℓ : ℝ) : ℂ)).re / quantC1WStar := by
    unfold virasoroShiftedFun quantC1WStar
    have h1 : ((1 + (airyZero 1 : ℂ) / (R : ℂ)) ^ (k + 1)) =
        (((1 + airyZero 1 / R) ^ (k + 1) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, show (airyZero 1 : ℂ) + (ℓ : ℂ) = ((airyZero 1 + ℓ : ℝ) : ℂ) by push_cast; ring,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  linarith [h_sum_split, h_tail_nn, h1_rew]

lemma virasoro_pnodes_lb_and_theta {c' R T : ℝ} {N : ℕ}
    (hc' : virasoroCQEnv ≤ c') (hR_48 : 48 ≤ R) (hR_ub : R + 1 ≤ virasoroAC c' ^ 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr))
    (hT_A2 : virasoroDeltaChart c' (virasoroAC c' ^ 2) ≤ T)
    (hT_a1 : T < virasoroDeltaChart c' (airyZero 1))
    (hB2 : QuantC1B2Holds (virasoroPsiTilde c' g) (virasoroUT c' T))
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R))
    (P : BootstrapParams)
    (hP_C1 : P.C_1 = quantC1C1) (hP_w : P.w_star = quantC1WStar)
    (hP_κ : P.κ_star = quantC1KappaStar) (hP_δ : P.δ_star = quantC1DeltaStar)
    (hP_η : P.η_0 = quantC1Eta0) (hP_k0 : P.k_0 = 5) :
    (∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
      ℓ ∈ Icc (P.D_1 * c' ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      -tebLambdaN P 0 * ℓ - P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤ virasoroPNodes c' R ℓ g k N) ∧
    ((P.k_0 : ℝ) ≤ R / 5 →
      tebThetaHB P 0 * (virasoroUT c' T - airyZero 1) ∈
        Icc (P.D_1 * c' ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      (P.κ_star / (4 * P.w_star)) * (virasoroUT c' T - airyZero 1) -
        P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤
        virasoroPNodes c' R (tebThetaHB P 0 * (virasoroUT c' T - airyZero 1)) g P.k_0 N) := by
  have hc'_10000 : 10000 ≤ c' :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans hc')
  have hc'_pos : 0 < c' := by linarith
  have hR_pos : 0 < R := by linarith
  obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
  have hAThr_eq : virasoroAThr = -airyZero 1 + 1 := by
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]
  have hu_mem := virasoroUT_between hc'_pos
    (by linarith : -(virasoroAC c' ^ 2) ≤ -virasoroAThr)
    (le_rfl : virasoroAC c' ^ 2 ≤ virasoroAC c' ^ 2)
    (by linarith : -virasoroAThr ≤ virasoroAC c' ^ 2) hT_A2 hT_hi
  set u_T := virasoroUT c' T
  have ha1_lt_uT : airyZero 1 < u_T := by
    by_contra hle
    have := (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [hu_mem.1.1], hu_mem.1.2⟩ ⟨by linarith, by linarith⟩ (not_lt.mp hle)
    linarith [hT_a1, hu_mem.2]
  have hbase_nn : 0 ≤ 1 + airyZero 1 / R := by
    rw [show (1 : ℝ) + airyZero 1 / R = (R + airyZero 1) / R by field_simp [hR_pos.ne'] ]
    exact div_nonneg (by linarith) hR_pos.le
  have hbase_le1 : 1 + airyZero 1 / R ≤ 1 := by
    have : airyZero 1 / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hR_pos.le
    linarith
  have hΨ_an_R : AnalyticOnNhd ℂ (virasoroPsiTilde c' g) (closedBall (0 : ℂ) (virasoroAC c' ^ 2)) :=
    (virasoroPsiTilde_analyticOnNhd (by linarith) hg.1).mono fun z hz =>
      virasoro_closedBall_subset_psiDom hc'_pos hz
  have hΨ_real_R : ∀ x ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2),
      (virasoroPsiTilde c' g (x : ℂ)).im = 0 :=
    fun x hx => (lemmaQ_part2 hc' hg.1 (cardyNorm_pos_of_nonzero
      (by rw [virasoroProblem_totalShift]; linarith) hg.1 hg.2.1)).2.1 x (abs_le.mpr hx) |>.1
  have ha1_abs : |airyZero 1| ≤ virasoroAC c' ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hT_le_Δa1 : T ≤ virasoroDeltaChart c' (airyZero 1) := hT_a1.le
  have hΨ_a1_nn : 0 ≤ (virasoroPsiTilde c' g (airyZero 1 : ℂ)).re :=
    (lemmaQ_part3 hc' hg).1 (airyZero 1) ha1_abs hT_le_Δa1
  refine ⟨?_, ?_⟩
  · -- `hP_nodes_lb_hb`
    intro k ℓ _ hkR hℓ_mem
    have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
    have hℓ_le' : ℓ ≤ min quantC1DeltaStar (min quantC1Eta0 1) := by
      simpa only [hP_δ, hP_η] using hℓ_mem.2
    have hℓ_δ : ℓ ≤ quantC1DeltaStar := hℓ_le'.trans (min_le_left _ _)
    have h_mv := psiTilde_real_mv_sub hΨ_an_R hΨ_real_R (a := airyZero 1) (b := airyZero 1 + ℓ)
      (by linarith) (by linarith) (by linarith [quantC1DeltaStar_le]) quantC1C1 quantC1C1_pos.le
      fun x hx => (hB2.2 x ⟨by linarith [hx.1, quantC1DeltaStar_pos], by linarith [hx.2]⟩).1
    have hΨ_lb : -quantC1C1 * ℓ ≤ (virasoroPsiTilde c' g ((airyZero 1 + ℓ : ℝ) : ℂ)).re := by
      have h1 := (abs_le.mp h_mv).1
      linarith
    have hpow_le1 : (1 + airyZero 1 / R) ^ (k + 1) ≤ 1 := pow_le_one₀ hbase_nn hbase_le1
    have hw_pos : 0 < quantC1WStar := quantC1WStar_pos
    have hterm_lb : -(quantC1C1 / quantC1WStar) * ℓ ≤
        (1 + airyZero 1 / R) ^ (k + 1) *
          (virasoroPsiTilde c' g ((airyZero 1 + ℓ : ℝ) : ℂ)).re / quantC1WStar := by
      have hmul : (1 + airyZero 1 / R) ^ (k + 1) * (-quantC1C1 * ℓ) ≤
          (1 + airyZero 1 / R) ^ (k + 1) *
            (virasoroPsiTilde c' g ((airyZero 1 + ℓ : ℝ) : ℂ)).re :=
        mul_le_mul_of_nonneg_left hΨ_lb (pow_nonneg hbase_nn _)
      have h2 : -(quantC1C1 * ℓ) ≤ (1 + airyZero 1 / R) ^ (k + 1) * (-quantC1C1 * ℓ) := by
        have h3 : 0 ≤ quantC1C1 * ℓ := mul_nonneg quantC1C1_pos.le hℓ_nn
        nlinarith [hpow_le1]
      have h4 : -(quantC1C1 * ℓ) / quantC1WStar = -(quantC1C1 / quantC1WStar) * ℓ := by ring
      rw [← h4]
      exact div_le_div_of_nonneg_right (h2.trans hmul) hw_pos.le
    have hΛ_ge : quantC1C1 / quantC1WStar ≤ tebLambdaN P 0 := by
      unfold tebLambdaN
      rw [hP_C1, hP_w, add_zero]
      have : 0 ≤ quantC1C1 / quantC1WStar := div_nonneg quantC1C1_pos.le hw_pos.le
      linarith [show 2 * quantC1C1 * (1 / quantC1WStar) = 2 * (quantC1C1 / quantC1WStar) by ring]
    have h_main := virasoro_pnodes_lower_aux hc' hR_48 hR_ub hg hT_hi hT_A2 hT_a1 hB2 hN hℓ_nn hℓ_le' k hkR
    have hΛ_mul : -tebLambdaN P 0 * ℓ ≤ -(quantC1C1 / quantC1WStar) * ℓ := by nlinarith
    linarith [hΛ_mul, hterm_lb, h_main]
  · -- `P_theta_bound`
    intro hk0_R hℓ_mem
    set θ := tebThetaHB P 0
    have hθ_pos : 0 < θ := tebThetaHB_pos P le_rfl
    have hθ_half : θ ≤ 1 / 2 := tebThetaHB_le_half P 0
    have hθ_le1 : θ ≤ 1 := hθ_half.trans (by norm_num)
    have hℓ_nn : 0 ≤ θ * (u_T - airyZero 1) :=
      (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
    have hℓ_le' : θ * (u_T - airyZero 1) ≤ min quantC1DeltaStar (min quantC1Eta0 1) := by
      simpa only [hP_δ, hP_η] using hℓ_mem.2
    have hsec := quantC1B2_secant_lower (R_dom := virasoroAC c' ^ 2)
      (by rw [abs_of_neg (by linarith)]; linarith) hΨ_an_R ha1_lt_uT
      ((lemmaQ_part3 hc' hg).1 u_T (abs_le.mpr ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2]⟩)
        (by rw [hu_mem.2]))
      hB2 hθ_pos.le hθ_le1
    have h1θ : (1 / 2 : ℝ) ≤ 1 - θ := by linarith
    have h_psi_lb : quantC1KappaStar * (u_T - airyZero 1) ≤
        (virasoroPsiTilde c' g ((airyZero 1 + θ * (u_T - airyZero 1) : ℝ) : ℂ)).re := by
      have h1 : quantC1KappaStar * (u_T - airyZero 1) ≤ 2 * quantC1KappaStar * (1 - θ) * (u_T - airyZero 1) := by
        have hk := quantC1KappaStar_pos.le
        have hx : 0 ≤ u_T - airyZero 1 := by linarith
        nlinarith [mul_nonneg hk hx]
      exact h1.trans hsec
    have h_pow_lb : (1 / 2 : ℝ) ≤ (1 + airyZero 1 / R) ^ (P.k_0 + 1) := by
      rw [hP_k0]
      have h1 : (1 - 2.35 / 48 : ℝ) ≤ 1 + airyZero 1 / R := by
        have hdiv : -2.35 / 48 ≤ airyZero 1 / R := by
          calc -2.35 / 48 ≤ -2.35 / R := by
                rw [neg_div, neg_div, neg_le_neg_iff]
                exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR_48
            _ ≤ airyZero 1 / R := div_le_div_of_nonneg_right (by linarith) hR_pos.le
        linarith
      have h2 : (1 / 2 : ℝ) ≤ (1 - 2.35 / 48 : ℝ) ^ (5 + 1) := by norm_num
      exact h2.trans (pow_le_pow_left₀ (by norm_num) h1 _)
    have hterm_lb : (P.κ_star / (4 * P.w_star)) * (u_T - airyZero 1) ≤
        (1 + airyZero 1 / R) ^ (P.k_0 + 1) *
          (virasoroPsiTilde c' g ((airyZero 1 + θ * (u_T - airyZero 1) : ℝ) : ℂ)).re /
          quantC1WStar := by
      rw [hP_κ, hP_w]
      have hkn : 0 ≤ quantC1KappaStar * (u_T - airyZero 1) :=
        mul_nonneg quantC1KappaStar_pos.le (by linarith)
      have h1 : (1 / 2 : ℝ) * (quantC1KappaStar * (u_T - airyZero 1)) ≤
          (1 + airyZero 1 / R) ^ (P.k_0 + 1) *
            (virasoroPsiTilde c' g ((airyZero 1 + θ * (u_T - airyZero 1) : ℝ) : ℂ)).re :=
        mul_le_mul h_pow_lb h_psi_lb hkn (pow_nonneg hbase_nn _)
      have h2 : (quantC1KappaStar / (4 * quantC1WStar)) * (u_T - airyZero 1) ≤
          ((1 / 2 : ℝ) * (quantC1KappaStar * (u_T - airyZero 1))) / quantC1WStar := by
        have hw := quantC1WStar_pos.le
        have : ((1 / 2 : ℝ) * (quantC1KappaStar * (u_T - airyZero 1))) / quantC1WStar =
            (quantC1KappaStar / (2 * quantC1WStar)) * (u_T - airyZero 1) := by ring
        rw [this]
        have : quantC1KappaStar / (4 * quantC1WStar) ≤ quantC1KappaStar / (2 * quantC1WStar) :=
          div_le_div_of_nonneg_left quantC1KappaStar_pos.le (mul_pos two_pos quantC1WStar_pos)
            (by linarith [quantC1WStar_pos])
        exact mul_le_mul_of_nonneg_right this (by linarith)
      exact h2.trans (div_le_div_of_nonneg_right h1 quantC1WStar_pos.le)
    have h_main := virasoro_pnodes_lower_aux hc' hR_48 hR_ub hg hT_hi hT_A2 hT_a1 hB2 hN hℓ_nn hℓ_le'
      P.k_0 hk0_R
    linarith [hterm_lb, h_main]

/-! ### Section 4: Building `BootstrapHBInstance` and Theorem `FT-L.FW` at `(1, 0)` -/

lemma virasoro_lobe_scale_down {b C_gap κ_gap c' T : ℝ}
    (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV) (hc'_Qenv : virasoroCQEnv ≤ c')
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hdl_bd : virasoroDeltaLobeAt b c' g ≤ C_gap * Real.exp (-κ_gap * c'))
    (hdl_half : virasoroDeltaLobeAt b c' g < 1 / 2)
    (hT_A2 : virasoroDeltaChart c' (virasoroACAt b c' ^ 2) < T) :
    virasoroACAt b c' ^ 2 ≤ virasoroAC c' ^ 2 ∧
    virasoroDeltaLobe c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
    virasoroDeltaLobe c' g < 1 / 2 ∧
    virasoroDeltaChart c' (virasoroAC c' ^ 2) < T := by
  have hc'_10000 : 10000 ≤ c' :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans hc'_Qenv)
  have hc'_24 : 24 ≤ c' := by linarith
  have hc'_pos : 0 < c' := by linarith
  have ha : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero ha hg.1 hg.2.1
  have hA2_le : virasoroACAt b c' ^ 2 ≤ virasoroAC c' ^ 2 :=
    virasoroACAt_sq_le hb_pos.le hb_le hc'_pos.le
  have hdl_le_at : virasoroDeltaLobe c' g ≤ virasoroDeltaLobeAt b c' g :=
    virasoroDeltaLobe_le_virasoroDeltaLobeAt hb_pos hb_le hc'_24 hg.1 hM_pos
  have hT_A2_full : virasoroDeltaChart c' (virasoroAC c' ^ 2) < T := by
    have hΔ_le : virasoroDeltaChart c' (virasoroAC c' ^ 2) ≤
        virasoroDeltaChart c' (virasoroACAt b c' ^ 2) :=
      (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
        ⟨by linarith [sq_nonneg (virasoroACAt b c')], hA2_le⟩
        ⟨by linarith [sq_nonneg (virasoroAC c')], le_rfl⟩ hA2_le
    exact hΔ_le.trans_lt hT_A2
  exact ⟨hA2_le, hdl_le_at.trans hdl_bd, hdl_le_at.trans_lt hdl_half, hT_A2_full⟩

lemma virasoro_uT_range_of_violator {c' R T : ℝ}
    (hc'_Qenv : virasoroCQEnv ≤ c') (hR_thr : virasoroAThr ≤ R)
    (hR_ub : R + 1 ≤ virasoroAC c' ^ 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hT_A2 : virasoroDeltaChart c' (virasoroAC c' ^ 2) < T)
    (hT_a1 : T < virasoroDeltaChart c' (airyZero 1))
    (hB2 : QuantC1B2Holds (virasoroPsiTilde c' g) (virasoroUT c' T)) :
    airyZero 1 < virasoroUT c' T ∧
    virasoroUT c' T ≤ -1 ∧
    virasoroDeltaChart c' (-1) ≤ T ∧
    virasoroDeltaChart c' 0 ≤ T ∧
    T ≤ virasoroDeltaChart c' (-virasoroAThr) ∧
    T ≤ virasoroDeltaChart c' (-R) := by
  have hc'_10000 : 10000 ≤ c' :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans hc'_Qenv)
  have hc'_pos : 0 < c' := by linarith
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  have hR_pos : 0 < R := lt_of_lt_of_le virasoroAThr_pos hR_thr
  have hA2_ge4 : 4 ≤ virasoroAC c' ^ 2 := by linarith [virasoroAThr_gt_two]
  have huT_Ioo : virasoroUT c' T ∈ Ioo (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    (lemmaQ_part3 hc'_Qenv hg).2.2.1
      (hT_a1.trans ((virasoroDeltaChart_strictAnti hc'_pos)
        ⟨le_rfl, by linarith⟩
        ⟨by linarith [airyZero_one.1], by linarith [airyZero_one.2]⟩
        (by linarith [airyZero_one.1])))
      hT_A2
  have hu_mem := virasoroUT_between hc'_pos
    (by linarith [huT_Ioo.1]) (by linarith [huT_Ioo.2])
    (by linarith [huT_Ioo.1, huT_Ioo.2] : -(virasoroAC c' ^ 2) ≤ virasoroAC c' ^ 2)
    hT_A2.le
    (hT_a1.le.trans ((virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith⟩
      ⟨by linarith [airyZero_one.1], by linarith [airyZero_one.2]⟩
      (by linarith [airyZero_one.1])))
  set u_T := virasoroUT c' T
  have hΔ_uT : virasoroDeltaChart c' u_T = T := hu_mem.2
  have ha1_lt_uT : airyZero 1 < u_T := by
    by_contra hle
    have := (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨huT_Ioo.1.le, huT_Ioo.2.le⟩
      ⟨by linarith [airyZero_one.1], by linarith [airyZero_one.2]⟩
      (not_lt.mp hle)
    linarith [hΔ_uT]
  have huT_le_m1 : u_T ≤ -1 := by
    have := (hB2.1).trans ((min_le_left _ _).trans quantC1DeltaStar_le)
    linarith [airyZero_one.2]
  have hT_lo_m1 : virasoroDeltaChart c' (-1) ≤ T := by
    rw [← hΔ_uT]
    exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨huT_Ioo.1.le, huT_Ioo.2.le⟩ ⟨by linarith, by linarith⟩ huT_le_m1
  have hT_lo_0 : virasoroDeltaChart c' 0 ≤ T := by
    rw [← hΔ_uT]
    exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨huT_Ioo.1.le, huT_Ioo.2.le⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hT_hi_AThr : T ≤ virasoroDeltaChart c' (-virasoroAThr) := by
    rw [← hΔ_uT]
    have hAThr_eq : virasoroAThr = -airyZero 1 + 1 := by
      unfold virasoroAThr; rw [abs_of_neg (by linarith [airyZero_one.2])]
    exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith [virasoroAThr_pos]⟩ ⟨huT_Ioo.1.le, huT_Ioo.2.le⟩
      (by linarith [ha1_lt_uT, hAThr_eq])
  have hT_hi_R : T ≤ virasoroDeltaChart c' (-R) :=
    hT_hi_AThr.trans ((virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [virasoroAThr_pos]⟩ (by linarith))
  exact ⟨ha1_lt_uT, huT_le_m1, hT_lo_m1, hT_lo_0, hT_hi_AThr, hT_hi_R⟩

lemma virasoro_sigma_arc_of_scale {b c' R : ℝ} (hb_pos : 0 < b) (hc'_ge1 : 1 ≤ c')
    (hR_ub_b : R + 1 ≤ virasoroACAt b c' ^ 2)
    (hς_arc : virasoroSigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1) :
    virasoroSigma c' * (3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1) ≤ 1 := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le zero_lt_one hc'_ge1
  have hsig_nn := virasoroSigma_nonneg hc'_ge1
  have hR_le_ac : R ≤ 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) := by
    rw [← virasoroACAt_sq b c' hc'_pos.le]; linarith [hR_ub_b]
  have hsqrtR : √R ≤ √2 * b * c' ^ (1 / 3 : ℝ) := by
    calc √R ≤ √(2 * b ^ 2 * c' ^ (2 / 3 : ℝ)) := Real.sqrt_le_sqrt hR_le_ac
      _ = √(virasoroACAt b c' ^ 2) := by rw [virasoroACAt_sq b c' hc'_pos.le]
      _ = virasoroACAt b c' := Real.sqrt_sq (virasoroACAt_pos hb_pos hc'_pos).le
      _ = √2 * b * c' ^ (1 / 3 : ℝ) := rfl
  have hc14 : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 12 : ℝ)) = c' ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hc'_pos]; norm_num
  have h3pi : 3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1 ≤
      3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1 := by
    calc 3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1
        ≤ 3 * π * (√2 * b * c' ^ (1 / 3 : ℝ)) * c' ^ (-(1 / 12 : ℝ)) + 1 := by gcongr
      _ = 3 * π * √2 * b * (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 12 : ℝ))) + 1 := by ring
      _ = 3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1 := by rw [hc14]
  exact (mul_le_mul_of_nonneg_left h3pi hsig_nn).trans hς_arc

/-- Construct the concrete `BootstrapHBInstance P 0` (together with `(B3)`) at scale
`0 < b ≤ virasoroBV` for any Virasoro violator `T < Δ(a₁)` at sufficiently large `c'`,
assuming `YVInputAtFor b`. -/
noncomputable def virasoro_bootstrapHB_of_YVFor
    {b C_fb c_YV C_gap κ_gap : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV)
    (hC_fb : 1 ≤ C_fb) (_hc_YV : virasoroCQEnv ≤ c_YV)
    (hYVat : YVInputAtFor b virasoroPsiTilde C_fb c_YV)
    (hC_gap : 0 < C_gap) (hκ_gap : 0 < κ_gap)
    {c' T : ℝ} (hc'_Qenv : virasoroCQEnv ≤ c') (hc'_YV : c_YV ≤ c')
    (h_c12 : (3 * π) ^ (12 : ℕ) ≤ c')
    (h_b48 : 48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ))
    (hς_half : virasoroSigma c' ≤ 1 / 2)
    (hς_arc : virasoroSigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hdl_bd : virasoroDeltaLobeAt b c' g ≤ C_gap * Real.exp (-κ_gap * c'))
    (hdl_half : virasoroDeltaLobeAt b c' g < 1 / 2)
    (hT_A2 : virasoroDeltaChart c' (virasoroACAt b c' ^ 2) < T)
    (hT_a1 : T < virasoroDeltaChart c' (airyZero 1))
    (hB2 : QuantC1B2Holds (virasoroPsiTilde c' g) (virasoroUT c' T)) :
    let P := virasoroBootstrapParamsFor b hb_pos C_fb hC_fb C_gap κ_gap hC_gap hκ_gap
    { I : BootstrapHBInstance P 0 //
      I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) ∧
      I.c = c' ∧ I.x_tilde = virasoroUT c' T - airyZero 1 } := by
  intro P
  have hc'_10000 : 10000 ≤ c' :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans hc'_Qenv)
  have hc'_pos : 0 < c' := by linarith
  have hc'_ge1 : 1 ≤ c' := by linarith
  obtain ⟨hA2_le, hdl_bd_full, hdl_half_full, hT_A2_full⟩ :=
    virasoro_lobe_scale_down hb_pos hb_le hc'_Qenv hg hdl_bd hdl_half hT_A2
  let k₀ : ℕ := ⌈b ^ 2 * c' ^ (2 / 3 : ℝ)⌉₊
  have hk₀_ge48 : 48 ≤ k₀ := by
    dsimp [k₀]
    have : (48 : ℝ) ≤ (⌈b ^ 2 * c' ^ (2 / 3 : ℝ)⌉₊ : ℝ) :=
      h_b48.trans (Nat.le_ceil _)
    exact_mod_cast this
  have h_circ := good_circle_exists k₀ (by omega : 10 ≤ k₀)
  let R : ℝ := Classical.choose h_circ
  have hR_spec := Classical.choose_spec h_circ
  have hR_lb : (k₀ : ℝ) ≤ R := hR_spec.1
  have hR_le_k : R ≤ (k₀ : ℝ) + 1 := hR_spec.2.1
  have hR_low := hR_spec.2.2
  have hR_48 : 48 ≤ R := (by exact_mod_cast hk₀_ge48 : (48 : ℝ) ≤ k₀).trans hR_lb
  have hR_pos : 0 < R := by linarith
  have hR_bv : b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R := (Nat.le_ceil _).trans hR_lb
  have hR_ub_ceil : R ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) + 2 := by
    have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ))
    linarith
  have hR_ub_2b : R ≤ 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 := by linarith
  have hR_ub_b : R + 1 ≤ virasoroACAt b c' ^ 2 := by
    rw [virasoroACAt_sq b c' hc'_pos.le]; linarith
  have hR_ub : R + 1 ≤ virasoroAC c' ^ 2 := hR_ub_b.trans hA2_le
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  have hR_thr : virasoroAThr ≤ R := by linarith
  have h_good_ai : ∀ u : ℂ, ‖u‖ = R → airyAiC u ≠ 0 := by
    intro u hu h0
    have h1 := hR_low u hu
    rw [h0, norm_zero] at h1
    have h2 : 0 < 1 / (25 * π) * (1 + R) ^ (-(1 / 2 : ℝ)) * airyEnv u := by
      have := airyEnv_pos u
      have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + R) (-(1 / 2 : ℝ))
      positivity
    linarith
  have hN_ex := airy_circleData hR_pos h_good_ai
  let N : ℕ := Classical.choose hN_ex
  have hN_spec := Classical.choose_spec hN_ex
  have hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R) := hN_spec.1
  have hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R := hN_spec.2
  have hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖(airyBiC w - I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π :=
    fun w hw him => airy_Rplus_bound him (hw ▸ hR_low w hw)
  have hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖(airyBiC w + I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π :=
    fun w hw him => airy_Rminus_bound him (hw ▸ hR_low w hw)
  obtain ⟨ha1_lt_uT, huT_le_m1, hT_lo_m1, hT_lo_0, hT_hi_AThr, hT_hi_R⟩ :=
    virasoro_uT_range_of_violator hc'_Qenv hR_thr hR_ub hg hT_A2_full hT_a1 hB2
  set u_T := virasoroUT c' T
  have hB_sums := virasoro_band_sums_le hc'_Qenv hR_thr hR_ub hg hdl_half_full hT_lo_0 hT_hi_AThr
  have hB1_nn : 0 ≤ virasoroBandB1 c' R T g :=
    virasoroBandB1_nonneg hc'_Qenv hR_thr (by linarith) hg hT_lo_0 hT_hi_AThr
  have hB2_nn : 0 ≤ virasoroBandB2 c' R g :=
    virasoroBandB2_nonneg hc'_Qenv hR_thr (by linarith) hg hT_hi_AThr
  set B_1 := virasoroBandB1 c' R T g
  set B_2 := virasoroBandB2 c' R g
  set L := C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1)
  have hL_lb : 1 ≤ L := by
    have h1 : 1 ≤ c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 := by
      have : 0 ≤ c' ^ (1 / 3 : ℝ) * (B_1 + B_2) :=
        mul_nonneg (Real.rpow_nonneg hc'_pos.le _) (by linarith)
      linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1) := mul_le_mul hC_fb h1 zero_le_one (by linarith)
  have hL_ub : L ≤ P.C_L * c' ^ P.γ := by
    have hc13_le : c' ^ (1 / 3 : ℝ) ≤ c' := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hc'_ge1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
    have h1 : c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 ≤ 4 * c' := by
      have hB3_le : B_1 + B_2 ≤ 3 := by linarith [hB_sums.1, hB_sums.2]
      calc c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1
          ≤ c' * 3 + c' := add_le_add
              (mul_le_mul hc13_le hB3_le (by linarith) hc'_pos.le) hc'_ge1
        _ = 4 * c' := by ring
    dsimp [L, P, virasoroBootstrapParamsFor]
    rw [Real.rpow_one]
    calc C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1)
        ≤ C_fb * (4 * c') := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 4 * C_fb * c' := by ring
  have hς_arc' := virasoro_sigma_arc_of_scale hb_pos hc'_ge1 hR_ub_b hς_arc
  have hYV_env : YVEnvBound (virasoroPsiTilde c' g) c' R L :=
    hYVat hc'_YV hR_thr hR_bv hR_ub_b hg hT_lo_0 hT_hi_AThr
  have hPN := virasoro_pnodes_lb_and_theta hc'_Qenv hR_48 hR_ub hg hT_hi_AThr hT_A2_full.le hT_a1 hB2 hN
    P rfl rfl rfl rfl rfl rfl
  refine ⟨{
    c := c'
    R := R
    a := √R
    B_1 := B_1
    B_2 := B_2
    L := L
    x_tilde := u_T - airyZero 1
    r_inf := 0
    C_err := C_gap
    hc := by linarith
    ha_lb := by
      calc P.b * c' ^ (1 / 3 : ℝ)
          = √(b ^ 2 * c' ^ (2 / 3 : ℝ)) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb_pos.le,
              show c' ^ (2 / 3 : ℝ) = (c' ^ (1 / 3 : ℝ)) ^ 2 by
                rw [← Real.rpow_natCast (c' ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc'_pos.le]; norm_num,
              Real.sqrt_sq (Real.rpow_nonneg hc'_pos.le _)]
            rfl
        _ ≤ √R := Real.sqrt_le_sqrt hR_bv
    ha_sq := Real.sq_sqrt hR_pos.le
    hR_ub := hR_ub_2b
    hB1 := hB1_nn
    hB2 := hB2_nn
    hL_lb := hL_lb
    hL_ub := hL_ub
    hx_pos := by linarith
    hx_ub := hB2.1
    hr_inf_nn := le_rfl
    hr_inf_ub := by have := P.hC0; positivity
    hC_err_nn := hC_gap.le
    hC_err_ub := le_max_right _ _
    B_1k := fun k => virasoroBandB1k c' R T g k
    B_2' := fun _ => B_2
    P_nodes := fun k ℓ => virasoroPNodes c' R ℓ g k N
    I_line := fun k ℓ => ∫ x in (-R)..R, (virasoroShiftedFun c' R ℓ g k (x : ℂ)).re
    Arc_cov := fun k ℓ => virasoroArcCov c' R T L ℓ g k
    Arc_unc := virasoroArcUncConst * c' ^ (-(3 / 8 : ℝ))
    hB1k_nn := fun k _ _ => virasoroBandB1k_nonneg hc'_Qenv hR_pos.le (by linarith) hg hT_A2_full.le
      hT_hi_R (by linarith [huT_le_m1]) k
    hB2'_nn := fun _ _ _ => hB2_nn
    hB_sum := fun k _ _ => by
      have := virasoroBandB1_le_B1k hc'_Qenv hR_pos (by linarith) hg hT_lo_0 hT_hi_R k
      linarith
    hP_le := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 := hℓ_mem.2.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
      exact virasoro_quad_arc_bound hc'_Qenv h_c12 hς_arc'
        ((by norm_num : (10 : ℝ) ≤ 48).trans hR_48) hR_ub (zero_le_one.trans hL_lb)
        hℓ_nn hℓ_half hg hYV_env hD hRp hRm hk0
    hArc_cov := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_pos : 0 < ℓ := by
        have hpos : 0 < P.D_1 * c' ^ (-(1 / 3 : ℝ)) := by
          have : P.D_1 = 1 := rfl
          rw [this]; positivity
        exact lt_of_lt_of_le hpos hℓ_mem.1
      have hle := virasoroArcCov_le (c' := c') (T := T)
        ((by norm_num : (10 : ℝ) ≤ 48).trans hR_48) (zero_le_one.trans hL_lb) hℓ_pos g hk0
      have hCa : virasoroArcCovConst ≤ P.C_a := le_max_left _ _
      refine hle.trans ?_
      gcongr
    hArc_unc := le_rfl
    hI_line := fun k ℓ hk0 hkR hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 := hℓ_mem.2.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
      have hlb := virasoro_line_bound hc'_Qenv (virasoroSigma_nonneg hc'_ge1) hς_half
        (by linarith) hR_ub hℓ_nn hℓ_half hg hT_lo_m1 hT_hi_AThr hk0 hkR
      have hCa : 4 * Real.exp (6 / 5) + 3 * virasoroEnvC0 ≤ P.C_a := le_max_right _ _
      have h_ca_term : (4 * Real.exp (6 / 5) + 3 * virasoroEnvC0) * ((k : ℝ) + 1) / R ≤
          P.C_a * ((k : ℝ) + 1) / R := by gcongr
      have h_exp_le : virasoroDeltaLobe c' g ≤ C_gap * c' * Real.exp (-P.κ * c') := by
        have hκ_eq : P.κ = κ_gap := rfl
        rw [hκ_eq]
        calc virasoroDeltaLobe c' g ≤ C_gap * Real.exp (-κ_gap * c') := hdl_bd_full
          _ = 1 * (C_gap * Real.exp (-κ_gap * c')) := (one_mul _).symm
          _ ≤ c' * (C_gap * Real.exp (-κ_gap * c')) :=
              mul_le_mul_of_nonneg_right hc'_ge1 (mul_nonneg hC_gap.le (Real.exp_pos _).le)
          _ = C_gap * c' * Real.exp (-κ_gap * c') := by ring
      linarith
    hW_top := le_rfl
    hP_nodes_lb_hb := fun k ℓ hk0 hkR hℓ_mem => by
      simpa using hPN.1 k ℓ hk0 hkR hℓ_mem
    P_theta_bound := fun hk0_R hℓ_mem => by
      simpa using hPN.2 hk0_R hℓ_mem
  }, le_rfl, rfl, rfl⟩

/-- Construct the concrete `BootstrapHBInstance P 0` (together with `(B3)`) for any Virasoro
violator `T < Δ(a₁)` at sufficiently large `c'`, assuming `YVInputAt`. -/
noncomputable def virasoro_bootstrapHB_of_YV
    {C_fb c_YV C_gap κ_gap : ℝ} (hC_fb : 1 ≤ C_fb) (hc_YV : virasoroCQEnv ≤ c_YV)
    (hYVat : YVInputAt virasoroPsiTilde C_fb c_YV)
    (hC_gap : 0 < C_gap) (hκ_gap : 0 < κ_gap)
    {c' T : ℝ} (hc'_Qenv : virasoroCQEnv ≤ c') (hc'_YV : c_YV ≤ c')
    (h_c12 : (3 * π) ^ (12 : ℕ) ≤ c')
    (h_b48 : 48 ≤ virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ))
    (hς_half : virasoroSigma c' ≤ 1 / 2)
    (hς_arc : virasoroSigma c' * (3 * π * √2 * virasoroBV * c' ^ (1 / 4 : ℝ) + 1) ≤ 1)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hdl_bd : virasoroDeltaLobe c' g ≤ C_gap * Real.exp (-κ_gap * c'))
    (hdl_half : virasoroDeltaLobe c' g < 1 / 2)
    (hT_A2 : virasoroDeltaChart c' (virasoroAC c' ^ 2) < T)
    (hT_a1 : T < virasoroDeltaChart c' (airyZero 1))
    (hB2 : QuantC1B2Holds (virasoroPsiTilde c' g) (virasoroUT c' T)) :
    let P := virasoroBootstrapParams C_fb hC_fb C_gap κ_gap hC_gap hκ_gap
    { I : BootstrapHBInstance P 0 //
      I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) ∧
      I.c = c' ∧ I.x_tilde = virasoroUT c' T - airyZero 1 } :=
  virasoro_bootstrapHB_of_YVFor virasoroBV_pos le_rfl hC_fb hc_YV hYVat hC_gap hκ_gap
    hc'_Qenv hc'_YV h_c12 h_b48 hς_half hς_arc hg hdl_bd hdl_half hT_A2 hT_a1 hB2

/-- **Theorem `FT-L.FW` at `(P, Q) = (1, 0)`** (`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`,
`wone:ftlfw`) at scale `0 < b ≤ virasoroBV` from `YVInputFor b`: Steps 0–5 give
`c₂ ≥ virasoroCQEnv` and `C ≥ 0` such that every weakly feasible Virasoro test `g` at
`(c'/12, T)` with `c' ≥ c₂` obeys `T ≥ ξ̄ c' + A_opt c'^{1/3} - C`. -/
theorem theoremFTLFW_oneZero_of_YVFor {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV)
    (hYV : YVInputFor b) :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' T : ℝ}, c_2 ≤ c' → ∀ {g : ℝ → ℝ},
        virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ T := by
  obtain ⟨C_fb, c_YV, hC_fb, hc_YV, hYVat⟩ := hYV
  obtain ⟨c_Q1, C_gap, κ_gap, hc_Q1, hC_gap, hκ_gap, hQ1⟩ := lemmaQ_part1At hb_pos hb_le
  let P := virasoroBootstrapParamsFor b hb_pos C_fb hC_fb C_gap κ_gap hC_gap hκ_gap
  have hQ_typeII := teb_quant_c1_typeII virasoroEnvC0_pos
    (fun c' => virasoroACAt b c' ^ 2) virasoroSigma (fun c' => C_gap * Real.exp (-κ_gap * c'))
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
      (mul_pos two_pos (pow_pos hb_pos 2)) |>.congr'
        (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c' hc'; rw [virasoroACAt_sq b c' hc']))
    (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'; exact virasoroSigma_nonneg hc')
    virasoroSigma_tendsto_zero
    (Eventually.of_forall fun c' => mul_nonneg hC_gap.le (Real.exp_pos _).le)
    (by
      have ht : Tendsto (fun c' : ℝ => -κ_gap * c') atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa only [mul_zero, Function.comp] using (Real.tendsto_exp_atBot.comp ht).const_mul C_gap)
  obtain ⟨c_1, hc_1, hQuant⟩ := hQ_typeII
  have h_asymp : ∀ᶠ c' : ℝ in atTop,
      (3 * π) ^ (12 : ℕ) ≤ c' ∧
      48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) ∧
      virasoroSigma c' ≤ 1 / 2 ∧
      virasoroSigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1 :=
    virasoroSigma_arc_eventuallyFor hb_pos
  rw [eventually_atTop] at h_asymp
  obtain ⟨c_asymp, hc_asymp⟩ := h_asymp
  let c_2 : ℝ := max virasoroCQEnv (max c_YV (max c_Q1 (max c_1 (max (tebC2 P) c_asymp))))
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
  have hc'_Qenv : virasoroCQEnv ≤ c' := (le_max_left _ _).trans hc'
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
    ((le_max_right _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))).trans hc'
  obtain ⟨h_c12, h_b48, hς_half, hς_arc⟩ := hc_asymp c' hc'_asymp
  have hc'_10000 : 10000 ≤ c' :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans hc'_Qenv)
  have hc'_pos : 0 < c' := by linarith
  have hc'_ge1 : 1 ≤ c' := by linarith
  have hc_m13 : c' ^ (-(1 / 3 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hc'_pos.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hc'_ge1 (by norm_num))
  obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
  have hA2_le : virasoroACAt b c' ^ 2 ≤ virasoroAC c' ^ 2 :=
    virasoroACAt_sq_le hb_pos.le hb_le hc'_pos.le
  have hA2_b48 : 48 ≤ virasoroACAt b c' ^ 2 := by
    rw [virasoroACAt_sq b c' hc'_pos.le]; linarith
  have hA2_48 : 48 ≤ virasoroAC c' ^ 2 := hA2_b48.trans hA2_le
  have hAopt_eq : Aopt = -cStar * airyZero 1 := by
    unfold Aopt
    rw [abs_of_neg (by linarith)]
    ring
  rcases le_or_gt (virasoroDeltaChart c' (airyZero 1)) T with hT_ge | hT_lt
  · -- Case 1: `T ≥ Δ(a₁)` (no bootstrap needed)
    have hinv := virasoro_deltaChart_inversion (u := airyZero 1) hc'_pos
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
    have hQ3_b := lemmaQ_part3At hb_pos hb_le hc'_Qenv hg
    have huT_Ioo : virasoroUT c' T ∈ Ioo (-(virasoroACAt b c' ^ 2)) (virasoroACAt b c' ^ 2) :=
      hQ3_b.2.2.1
        (hT_lt.trans ((virasoroDeltaChart_strictAnti hc'_pos)
          ⟨by linarith [hA2_le], by linarith [sq_nonneg (virasoroACAt b c'), hA2_le]⟩
          ⟨by linarith, by linarith⟩ (by linarith)))
        hT_A2
    have hu_mem := virasoroUT_between hc'_pos
      (a := -(virasoroACAt b c' ^ 2)) (b := virasoroACAt b c' ^ 2)
      (by linarith [hA2_le]) hA2_le (by linarith [sq_nonneg (virasoroACAt b c')])
      hT_A2.le
      (hT_lt.le.trans ((virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
        ⟨by linarith [hA2_le], by linarith [sq_nonneg (virasoroACAt b c'), hA2_le]⟩
        ⟨by linarith, by linarith⟩ (by linarith)))
    set u_T := virasoroUT c' T
    have ha1_lt_uT : airyZero 1 < u_T := by
      by_contra hle
      have := (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
        ⟨by linarith [huT_Ioo.1, hA2_le], huT_Ioo.2.le.trans hA2_le⟩
        ⟨by linarith, by linarith⟩ (not_lt.mp hle)
      linarith [hu_mem.2]
    have hQ2 := lemmaQ_part2 hc'_Qenv hg.1 hM_pos
    have hB2 : QuantC1B2Holds (virasoroPsiTilde c' g) u_T := by
      refine hQuant c' hc'_1 (virasoroPsiTilde c' g) u_T ?_ ?_ ?_ ha1_lt_uT huT_Ioo.2.le ?_
        hQ3_b.2.1 ?_ ?_
      · exact hQ2.1.mono fun z hz => virasoro_closedBall_subset_psiDom hc'_pos
          (Metric.closedBall_subset_closedBall hA2_le hz)
      · intro x hx
        exact (hQ2.2.1 x ((abs_le.mpr hx).trans hA2_le)).1
      · intro u hu hcut
        exact hQ2.2.2 u (Metric.closedBall_subset_closedBall hA2_le hu) hcut
      · intro x hx
        have hT_le : T ≤ virasoroDeltaChart c' x := by
          rw [← hu_mem.2]
          exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
            ⟨by linarith [hx.1, hA2_le], (hx.2.trans huT_Ioo.2.le).trans hA2_le⟩
            ⟨by linarith [huT_Ioo.1, hA2_le], huT_Ioo.2.le.trans hA2_le⟩ hx.2
        exact hQ3_b.1 x (abs_le.mpr ⟨hx.1, hx.2.trans huT_Ioo.2.le⟩) hT_le
      · have h_half := hQ3_b.2.2.2.1
          (hT_lt.trans ((virasoroDeltaChart_strictAnti hc'_pos)
            ⟨by linarith [hA2_le], by linarith [sq_nonneg (virasoroACAt b c'), hA2_le]⟩
            ⟨by linarith, by linarith⟩ (by linarith)))
          hT_A2.le
        linarith [h_half.2.2, hdl_bd]
      · intro R' hR'_mem hR'_uT
        have hT_le_R' : T ≤ virasoroDeltaChart c' (-R') := by
          rw [← hu_mem.2]
          exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
            ⟨by linarith [hR'_mem.2, hA2_le], by linarith [hR'_mem.1, hR'_mem.2, hA2_le]⟩
            ⟨by linarith [huT_Ioo.1, hA2_le], huT_Ioo.2.le.trans hA2_le⟩ hR'_uT
        exact (hQ3_b.2.2.2.2 R' hR'_mem.1 hR'_mem.2 hT_le_R').2.trans hdl_bd
    obtain ⟨I, hB3, hIc, hIx⟩ := virasoro_bootstrapHB_of_YVFor hb_pos hb_le hC_fb hc_YV hYVat
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
    have hinv := virasoro_deltaChart_inversion hc'_pos
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

/-- **Theorem `FT-L.FW` at `(P, Q) = (1, 0)`** (`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`,
`wone:ftlfw`) from `YVInput`: Steps 0–5 give `c₂ ≥ virasoroCQEnv` and `C ≥ 0` such that every
weakly feasible Virasoro test `g` at `(c'/12, T)` with `c' ≥ c₂` obeys
`T ≥ ξ̄ c' + A_opt c'^{1/3} - C`. -/
theorem theoremFTLFW_oneZero_of_YV (hYV : YVInput) :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' T : ℝ}, c_2 ≤ c' → ∀ {g : ℝ → ℝ},
        virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ T :=
  theoremFTLFW_oneZero_of_YVFor virasoroBV_pos le_rfl hYV

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.virasoro_bootstrapHB_of_YVFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_bootstrapHB_of_YVFor

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.theoremFTLFW_oneZero_of_YVFor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremFTLFW_oneZero_of_YVFor

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.virasoro_bootstrapHB_of_YV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_bootstrapHB_of_YV

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.theoremFTLFW_oneZero_of_YV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremFTLFW_oneZero_of_YV

end FormalResearch.ModularBootstrap.ConcreteBootstrap
