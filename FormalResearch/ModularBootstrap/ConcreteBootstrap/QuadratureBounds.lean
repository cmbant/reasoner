module

public import FormalResearch.TwoEdgeBootstrap.Bootstrap
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1Airy

/-!
# Proposition `Y_V` (`YVInput`), Schwarz Reflection, and Shifted-Weight Quadrature Bounds

Packages the unproved band bound Proposition `Y_V` (`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`,
`vlo:YV`) together with `TE.3(2)-(3)` as `YVInput`, proves non-vacuity (`yvInputAt_nonvacuous`),
and establishes the analytic `Arc` (`hArc_cov`, `hArc_unc`) and `Line` (`hI_line`) estimates
for `f_{k, ℓ}(u) = (1 + u / R)^{k + 1} \widetilde\Psi_V(u + ℓ)` needed to assemble
`BootstrapHBInstance` in `BootstrapHB.lean`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.Special
open FormalResearch.TwoEdgeBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.TipFront

lemma virasoroCQEnv_ge : (10000 : ℝ) ≤ virasoroCQEnv :=
  (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
    c_PJ_complex_le_virasoroCQEnv

/-! ### Section 1: `YVInput` (`vlo:YV`) and Non-Vacuity -/

/-- Threshold cutoff `A_thr := |a₁| + 1` for `(P, Q) = (1, 0)` in Step 3 of Theorem `FT-L.FW`. -/
noncomputable def virasoroAThr : ℝ := |airyZero 1| + 1

lemma virasoroAThr_pos : 0 < virasoroAThr := by
  unfold virasoroAThr; positivity

lemma virasoroAThr_gt_two : 3 < virasoroAThr := by
  unfold virasoroAThr
  have := airyZero_one
  rw [abs_of_neg (by linarith)]
  linarith

/-- First band moment `B₁ := R⁻¹ ∫_T^{Δ(-R)} (-ũ(t/c')) dm(t)` (`TE.2` / `vlo:YV`). -/
noncomputable def virasoroBandB1 (c' R T : ℝ) (g : ℝ → ℝ) : ℝ :=
  R⁻¹ * (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
    ∫ t in T..(virasoroDeltaChart c' (-R)),
      (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t)

/-- Second band moment `B₂ := ∫_{Δ(-R)}^∞ dm(t)` (`TE.2` / `vlo:YV`). -/
noncomputable def virasoroBandB2 (c' R : ℝ) (g : ℝ → ℝ) : ℝ :=
  (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
    ∫ t in Ici (virasoroDeltaChart c' (-R)),
      g t * virasoroProblem.cardyV (c' / 12) t

/-- Envelope `(Env_{L'})` (`two_edge_bootstrap.tex` `TE.3` / `TE.3(2)`): on the upper-half
annular sector `R - 1 ≤ ‖u‖ ≤ R + 1`, `Im u ≥ 0`, `sin φ' = (Re √u) / √‖u‖ ≥ 2 c'^{-1/12}`,
`‖Ψ(u)‖ ≤ L' |e(u)| (Re √u)^{-3/2} |u|^{-3/4}`. -/
def YVEnvBound (Ψ : ℂ → ℂ) (c' R L' : ℝ) : Prop :=
  ∀ u : ℂ, 0 ≤ u.im → R - 1 ≤ ‖u‖ → ‖u‖ ≤ R + 1 →
    2 * c' ^ (-(1 / 12 : ℝ)) * √‖u‖ ≤ (u ^ (1 / 2 : ℂ)).re →
    ‖Ψ u‖ ≤ L' * airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) *
      ‖u‖ ^ (-(3 / 4 : ℝ))

/-- Chart inversion helper on `[-A_{c'}^2, A_{c'}^2]`. -/
lemma virasoroUT_between {c' a b T : ℝ} (hc' : 0 < c')
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b)
    (hT_lo : virasoroDeltaChart c' b ≤ T) (hT_hi : T ≤ virasoroDeltaChart c' a) :
    virasoroUT c' T ∈ Icc a b ∧ virasoroDeltaChart c' (virasoroUT c' T) = T := by
  have hA2_nn : 0 ≤ virasoroAC c' ^ 2 := sq_nonneg _
  have ha_abs : |a| ≤ virasoroAC c' ^ 2 := abs_le.mpr ⟨ha_bd, hab.trans hb_bd⟩
  have hb_abs : |b| ≤ virasoroAC c' ^ 2 := abs_le.mpr ⟨ha_bd.trans hab, hb_bd⟩
  have hmem_a : a ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) := abs_le.mp ha_abs
  have hmem_b : b ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) := abs_le.mp hb_abs
  have hdiv_A2_lo := virasoroDeltaChart_div_mem hc' (abs_of_nonneg hA2_nn).le
  have hdiv_A2_hi := virasoroDeltaChart_div_mem hc' (by rw [abs_neg, abs_of_nonneg hA2_nn])
  have hΔ_lo : virasoroDeltaChart c' (virasoroAC c' ^ 2) ≤ virasoroDeltaChart c' b :=
    (virasoroDeltaChart_strictAnti hc').antitoneOn hmem_b ⟨by linarith, le_rfl⟩ hb_bd
  have hΔ_hi : virasoroDeltaChart c' a ≤ virasoroDeltaChart c' (-(virasoroAC c' ^ 2)) :=
    (virasoroDeltaChart_strictAnti hc').antitoneOn ⟨le_rfl, by linarith⟩ hmem_a ha_bd
  have hξ_lo : virasoroDeltaChart c' (virasoroAC c' ^ 2) / c' ≤ T / c' :=
    div_le_div_of_nonneg_right (hΔ_lo.trans hT_lo) hc'.le
  have hξ_hi : T / c' ≤ virasoroDeltaChart c' (-(virasoroAC c' ^ 2)) / c' :=
    div_le_div_of_nonneg_right (hT_hi.trans hΔ_hi) hc'.le
  have hΔ_uT : virasoroDeltaChart c' (virasoroUT c' T) = T := by
    unfold virasoroUT
    rw [virasoroDeltaChart_uChart hc' hξ_lo hξ_hi]
    field_simp [hc'.ne']
  have hdiv_T : T / c' ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) :=
    ⟨hdiv_A2_lo.1.trans hξ_lo, hξ_hi.trans hdiv_A2_hi.2⟩
  have hdiv_a := virasoroDeltaChart_div_mem hc' ha_abs
  have hdiv_b := virasoroDeltaChart_div_mem hc' hb_abs
  have hu_lo : a ≤ virasoroUT c' T := by
    rw [← virasoroUChart_deltaChart hc' ha_abs]
    exact (virasoroUChart_strictAnti hc').antitoneOn hdiv_T hdiv_a
      (div_le_div_of_nonneg_right hT_hi hc'.le)
  have hu_hi : virasoroUT c' T ≤ b := by
    rw [← virasoroUChart_deltaChart hc' hb_abs]
    exact (virasoroUChart_strictAnti hc').antitoneOn hdiv_b hdiv_T
      (div_le_div_of_nonneg_right hT_lo hc'.le)
  exact ⟨⟨hu_lo, hu_hi⟩, hΔ_uT⟩

lemma virasoroBandB1_nonneg {c' R T : ℝ} (hc' : virasoroCQEnv ≤ c')
    (hR_thr : virasoroAThr ≤ R) (hR_ub : R ≤ virasoroAC c' ^ 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr)) :
    0 ≤ virasoroBandB1 c' R T g := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc'
  have ha : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; have := virasoroCQEnv_ge; linarith
  have hR_pos : 0 < R := lt_of_lt_of_le virasoroAThr_pos hR_thr
  have hM_nn : 0 ≤ (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ :=
    inv_nonneg.mpr (cardyNorm_pos_of_nonzero ha hg.1 hg.2.1).le
  have hRm : -R ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨by linarith, by linarith [virasoroAThr_pos, sq_nonneg (virasoroAC c')]⟩
  have hAThr_m : -virasoroAThr ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨by linarith, by linarith [virasoroAThr_pos, sq_nonneg (virasoroAC c')]⟩
  have hΔ_T_le : T ≤ virasoroDeltaChart c' (-R) :=
    hT_hi.trans ((virasoroDeltaChart_strictAnti hc'_pos).antitoneOn hRm hAThr_m (by linarith))
  refine mul_nonneg (mul_nonneg (inv_nonneg.mpr hR_pos.le) hM_nn) ?_
  refine intervalIntegral.integral_nonneg hΔ_T_le fun t ht => ?_
  have hΔ_0_le : virasoroDeltaChart c' 0 ≤ t := hT_lo.trans ht.1
  have hu_t := virasoroUT_between hc'_pos (by linarith : -(virasoroAC c' ^ 2) ≤ -R)
    (sq_nonneg _) (by linarith : -R ≤ 0) hΔ_0_le ht.2
  have ht_pos : 0 ≤ t :=
    (virasoroDeltaChart_pos hc'_pos (by rw [abs_zero]; exact sq_nonneg _)).le.trans hΔ_0_le
  exact mul_nonneg (by linarith [hu_t.1.2])
    (mul_nonneg (hg.2.2.2 t ht.1) (virasoroProblem.cardyV_nonneg ha ht_pos))

lemma virasoroBandB2_nonneg {c' R T : ℝ} (hc' : virasoroCQEnv ≤ c')
    (hR_thr : virasoroAThr ≤ R) (hR_ub : R ≤ virasoroAC c' ^ 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr)) :
    0 ≤ virasoroBandB2 c' R g := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc'
  have ha : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; have := virasoroCQEnv_ge; linarith
  have hM_nn : 0 ≤ (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ :=
    inv_nonneg.mpr (cardyNorm_pos_of_nonzero ha hg.1 hg.2.1).le
  have hRm : -R ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨by linarith, by linarith [virasoroAThr_pos, sq_nonneg (virasoroAC c')]⟩
  have hAThr_m : -virasoroAThr ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨by linarith, by linarith [virasoroAThr_pos, sq_nonneg (virasoroAC c')]⟩
  have hΔ_T_le : T ≤ virasoroDeltaChart c' (-R) :=
    hT_hi.trans ((virasoroDeltaChart_strictAnti hc'_pos).antitoneOn hRm hAThr_m (by linarith))
  have hΔ_nn : 0 ≤ virasoroDeltaChart c' (-R) :=
    (virasoroDeltaChart_pos hc'_pos (abs_le.mpr hRm)).le
  refine mul_nonneg hM_nn (setIntegral_nonneg measurableSet_Ici fun t ht => ?_)
  exact mul_nonneg (hg.2.2.2 t (hΔ_T_le.trans ht)) (virasoroProblem.cardyV_nonneg ha (hΔ_nn.trans ht))

/-- Abstracted `(P, Q) = (1, 0)` band-feedback conclusion `vlo:YV` + `TE.3(2)-(3)` for a family
`Ψ c' g`, at fixed feedback factor `C_fb ≥ 1` and threshold `c_YV ≥ virasoroCQEnv`.
When `Ψ = virasoroPsiTilde`, this is the unproved analytic input `YVInput`. -/
def YVInputAt (Ψ : ℝ → (ℝ → ℝ) → ℂ → ℂ) (C_fb c_YV : ℝ) : Prop :=
  ∀ ⦃c' T R : ℝ⦄, c_YV ≤ c' →
    virasoroAThr ≤ R →
    virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R →
    R + 1 ≤ virasoroAC c' ^ 2 →
    ∀ ⦃g : ℝ → ℝ⦄, virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
    virasoroDeltaChart c' 0 ≤ T →
    T ≤ virasoroDeltaChart c' (-virasoroAThr) →
    YVEnvBound (Ψ c' g) c' R
      (C_fb * (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1))

/-- **Unproved analytic input (Proposition `Y_V`, `lower_o1_two_edge.tex` `vlo:YV`, together with
`TE.3(2)-(3)`)** at threshold `A_thr = |a₁| + 1`: existence of `C_fb ≥ 1` and `c_YV ≥ virasoroCQEnv`
such that every weakly feasible test `g` with `T ∈ [Δ(0), Δ(-A_thr)]` (equivalently
`-A_thr ≤ u_T ≤ 0` in the chart) satisfies `(Env_{L'})` with `L' = C_fb (c'^{1/3}(B₁ + B₂) + 1)`. -/
def YVInput : Prop :=
  ∃ C_fb c_YV : ℝ, 1 ≤ C_fb ∧ virasoroCQEnv ≤ c_YV ∧ YVInputAt virasoroPsiTilde C_fb c_YV

/-- Non-vacuity of `YVInputAt`: the feedback specification and envelope domain are consistent. -/
theorem yvInputAt_nonvacuous :
    ∃ (Ψ : ℝ → (ℝ → ℝ) → ℂ → ℂ) (C_fb c_YV : ℝ),
      1 ≤ C_fb ∧ virasoroCQEnv ≤ c_YV ∧ YVInputAt Ψ C_fb c_YV := by
  refine ⟨fun _ _ _ => 0, 1, virasoroCQEnv, le_rfl, le_rfl, ?_⟩
  intro c' T R hc' hR_thr _ hR_ub g hg hT_lo hT_hi u _ hRl _ hsin
  have hR_pos : 2 ≤ R := by linarith [virasoroAThr_gt_two]
  have hu_pos : 0 < ‖u‖ := by linarith
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc'
  have hre_pos : 0 < (u ^ (1 / 2 : ℂ)).re := by
    have : 0 < 2 * c' ^ (-(1 / 12 : ℝ)) * √‖u‖ := by positivity
    linarith
  have hB1 := virasoroBandB1_nonneg hc' hR_thr (by linarith) hg hT_lo hT_hi
  have hB2 := virasoroBandB2_nonneg hc' hR_thr (by linarith) hg hT_hi
  have henv : 0 < airyEnv u := airyEnv_pos u
  have hL'_nn : 0 ≤ 1 * (c' ^ (1 / 3 : ℝ) * (virasoroBandB1 c' R T g + virasoroBandB2 c' R g) + 1) := by
    positivity
  rw [norm_zero]
  exact mul_nonneg (mul_nonneg (mul_nonneg hL'_nn henv.le) (Real.rpow_nonneg hre_pos.le _))
    (Real.rpow_nonneg (norm_nonneg _) _)

/-! ### Section 2: Schwarz Reflection & Shifted-Square-Root Envelope Lemmas -/

/-- Schwarz reflection for `virasoroPsiTilde c' g` on `closedBall 0 (virasoroAC c'^2)`. -/
lemma virasoroPsiTilde_conj {c' : ℝ} (hc' : virasoroCQEnv ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2)) :
    virasoroPsiTilde c' g (star u) = star (virasoroPsiTilde c' g u) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc'
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
        (c_PJ_complex_le_virasoroCQEnv.trans hc'))
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := (isCompact_closedBall (0 : ℂ) (virasoroAC c' ^ 2)).exists_thickening_subset_open
    (virasoroPsiDom_isOpen hc'_pos) (virasoro_closedBall_subset_psiDom hc'_pos)
  let r_ball : ℝ := virasoroAC c' ^ 2 + δ
  have hr_sub : ball (0 : ℂ) r_ball ⊆ virasoroPsiDom c' := fun z hz => by
    apply hδ_sub
    rw [Metric.mem_thickening_iff]
    by_cases hz0 : ‖z‖ ≤ virasoroAC c' ^ 2
    · exact ⟨z, mem_closedBall_zero_iff.mpr hz0, by simpa⟩
    · push Not at hz0
      have hA2_nn : 0 ≤ virasoroAC c' ^ 2 := sq_nonneg _
      have hz_pos : 0 < ‖z‖ := hA2_nn.trans_lt hz0
      let w : ℂ := (((virasoroAC c' ^ 2 / ‖z‖ : ℝ)) : ℂ) * z
      have hw_mem : w ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2) := by
        rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hA2_nn hz_pos.le)]
        rw [div_mul_cancel₀ _ hz_pos.ne']
      have hw_dist : dist z w < δ := by
        rw [dist_eq_norm]
        have hdiff : z - w = ((1 - virasoroAC c' ^ 2 / ‖z‖ : ℝ) : ℂ) * z := by
          dsimp [w]; push_cast; ring
        rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg]
        · rw [sub_mul, one_mul, div_mul_cancel₀ _ hz_pos.ne']
          rw [mem_ball_zero_iff] at hz; linarith
        · rw [sub_nonneg, div_le_one hz_pos]; exact hz0.le
      exact ⟨w, hw_mem, hw_dist⟩
  have hF1_an : AnalyticOnNhd ℂ (virasoroPsiTilde c' g) (ball (0 : ℂ) r_ball) :=
    (virasoroPsiTilde_analyticOnNhd hc'_1000 hg).mono hr_sub
  let F2 : ℂ → ℂ := fun z => star (virasoroPsiTilde c' g (star z))
  have hF2_diff : DifferentiableOn ℂ F2 (ball (0 : ℂ) r_ball) := by
    intro z hz
    have hsz : star z ∈ ball (0 : ℂ) r_ball := by simpa [mem_ball_zero_iff] using hz
    have hda := (hF1_an (star z) hsz).differentiableAt.hasDerivAt
    have hd_conj : HasDerivAt F2 (star (deriv (virasoroPsiTilde c' g) (star z))) z := by
      rw [hasDerivAt_iff_tendsto_slope_zero]
      have ht_f := hda.tendsto_slope_zero
      have hstar_t : Tendsto (fun h : ℂ => star h) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · simpa using (continuous_star.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with h hh
          simpa using hh
      have ht_star := continuous_star.continuousAt.tendsto.comp (ht_f.comp hstar_t)
      refine ht_star.congr' (Eventually.of_forall fun h => ?_)
      simp only [Function.comp_apply, smul_eq_mul, F2, star_add, star_mul, star_inv₀, star_sub,
        star_star]
      ring
    exact hd_conj.differentiableAt.differentiableWithinAt
  have hF2_an : AnalyticOnNhd ℂ F2 (ball (0 : ℂ) r_ball) :=
    (analyticOnNhd_iff_differentiableOn isOpen_ball).mpr hF2_diff
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F2 z = virasoroPsiTilde c' g z := by
    rw [frequently_nhdsWithin_iff, nhds_basis_ball.frequently_iff]
    intro ε hε
    have hA2_pos : 0 < virasoroAC c' ^ 2 := by
      rw [virasoroAC_sq _ hc'_pos.le]; have := virasoroBV_pos; positivity
    let x : ℝ := min (ε / 2) (virasoroAC c' ^ 2 / 2)
    have hx_pos : 0 < x := lt_min (half_pos hε) (by linarith)
    have hx_mem : |x| ≤ virasoroAC c' ^ 2 := by
      rw [abs_of_pos hx_pos]
      exact (min_le_right _ _).trans (by linarith)
    have him : (virasoroPsiTilde c' g (x : ℂ)).im = 0 :=
      (lemmaQ_part2 hc' hg hM_pos).2.1 x hx_mem |>.1
    refine ⟨(x : ℂ), ?_, ?_, Complex.ofReal_ne_zero.mpr hx_pos.ne'⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]
      exact (min_le_left _ _).trans_lt (half_lt_self hε)
    · simp only [F2, Complex.star_def, Complex.conj_ofReal, Complex.conj_eq_iff_im.mpr him]
  have h0_mem : (0 : ℂ) ∈ ball (0 : ℂ) r_ball := mem_ball_self (by positivity [sq_nonneg (virasoroAC c')])
  have hu_ball : u ∈ ball (0 : ℂ) r_ball :=
    closedBall_subset_ball (by linarith : virasoroAC c' ^ 2 < r_ball) hu
  have heq := hF2_an.eqOn_of_preconnected_of_frequently_eq hF1_an
    (convex_ball (0 : ℂ) r_ball).isPreconnected h0_mem hfreq hu_ball
  calc virasoroPsiTilde c' g (star u) = star (F2 u) := by simp [F2]
    _ = star (virasoroPsiTilde c' g u) := by rw [heq]

/-- For `w ∉ (-∞, 0]`, `Re(w^{1/2}) > 0`. -/
lemma re_cpow_half_pos_of_slit {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    0 < (w ^ (1 / 2 : ℂ)).re := by
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  rw [Complex.cpow_def_of_ne_zero hw0, Complex.exp_re]
  have him : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by
    simp [Complex.log_im]; ring
  rw [him]
  have harg_ne : w.arg ≠ π := (Complex.mem_slitPlane_iff_arg.mp hw).1
  have hcos : 0 < Real.cos (w.arg / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Complex.neg_pi_lt_arg w],
      by linarith [lt_of_le_of_ne (Complex.arg_le_pi w) harg_ne]⟩
  exact mul_pos (Real.exp_pos _) hcos

private lemma cpow_half_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  by_cases hw : w = 0
  · rw [hw, Complex.zero_cpow (by norm_num)]; simp
  · rw [Complex.cpow_def_of_ne_zero hw, ← Complex.exp_nat_mul]
    have hmul : ((2 : ℕ) : ℂ) * (Complex.log w * (1 / 2 : ℂ)) = Complex.log w := by
      push_cast; ring
    rw [hmul, Complex.exp_log hw]

lemma not_nonpos_add_ofReal {w : ℂ} (hw : w ∈ Complex.slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    w + (t : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hw ⊢
  rcases hw with hre | him
  · left; simpa using add_pos_of_pos_of_nonneg hre ht
  · right; simpa using him

/-- For `w ∈ slitPlane` and `ℓ ≥ 0`, `Re(w^{1/2}) ≤ Re((w + ℓ)^{1/2})` and
`Re((w + ℓ)^{1/2}) ≤ Re(w^{1/2}) + √ℓ`. -/
lemma re_cpow_half_add_real_bounds {w : ℂ} (hw : w ∈ Complex.slitPlane) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ((w ^ (1 / 2 : ℂ)).re ≤ ((w + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re) ∧
    (((w + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ≤ (w ^ (1 / 2 : ℂ)).re + √ℓ) := by
  set z₁ : ℂ := w ^ (1 / 2 : ℂ)
  set z₂ : ℂ := (w + (ℓ : ℂ)) ^ (1 / 2 : ℂ)
  have hx₁ : 0 < z₁.re := re_cpow_half_pos_of_slit hw
  have hx₂ : 0 < z₂.re := re_cpow_half_pos_of_slit (not_nonpos_add_ofReal hw hℓ)
  have hz1_sq : z₁ ^ 2 = w := cpow_half_sq w
  have hz2_sq : z₂ ^ 2 = w + (ℓ : ℂ) := cpow_half_sq (w + (ℓ : ℂ))
  have hre : z₂.re ^ 2 - z₂.im ^ 2 = z₁.re ^ 2 - z₁.im ^ 2 + ℓ := by
    have h1 := congrArg Complex.re hz1_sq
    have h2 := congrArg Complex.re hz2_sq
    simp only [sq, Complex.mul_re, Complex.add_re, Complex.ofReal_re] at h1 h2
    linarith
  have him : z₂.re * z₂.im = z₁.re * z₁.im := by
    have h1 := congrArg Complex.im hz1_sq
    have h2 := congrArg Complex.im hz2_sq
    simp only [sq, Complex.mul_im, Complex.add_im, Complex.ofReal_im, add_zero] at h1 h2
    linarith
  have hid : (z₂.re ^ 2 - z₁.re ^ 2) * (z₂.re ^ 2 + z₁.im ^ 2) = z₂.re ^ 2 * ℓ := by
    have him2 : z₂.re ^ 2 * z₂.im ^ 2 = z₁.re ^ 2 * z₁.im ^ 2 := by
      calc z₂.re ^ 2 * z₂.im ^ 2 = (z₂.re * z₂.im) ^ 2 := by ring
        _ = (z₁.re * z₁.im) ^ 2 := by rw [him]
        _ = z₁.re ^ 2 * z₁.im ^ 2 := by ring
    linear_combination z₂.re ^ 2 * hre + him2
  have hden_pos : 0 < z₂.re ^ 2 + z₁.im ^ 2 := by positivity
  have hdiff_nn : 0 ≤ z₂.re ^ 2 - z₁.re ^ 2 := by
    have hmul_nn : 0 ≤ (z₂.re ^ 2 - z₁.re ^ 2) * (z₂.re ^ 2 + z₁.im ^ 2) := by
      rw [hid]; positivity
    exact nonneg_of_mul_nonneg_left hmul_nn hden_pos
  have hdiff_le : z₂.re ^ 2 - z₁.re ^ 2 ≤ ℓ := by
    have hmul_le : (z₂.re ^ 2 - z₁.re ^ 2) * (z₂.re ^ 2 + z₁.im ^ 2) ≤
        ℓ * (z₂.re ^ 2 + z₁.im ^ 2) := by
      rw [hid]; nlinarith [sq_nonneg z₁.im]
    exact le_of_mul_le_mul_right hmul_le hden_pos
  refine ⟨?_, ?_⟩
  · nlinarith
  · have hsq_le : z₂.re ^ 2 ≤ (z₁.re + √ℓ) ^ 2 := by
      have h1 : z₁.re ^ 2 + ℓ ≤ z₁.re ^ 2 + 2 * z₁.re * √ℓ + √ℓ ^ 2 := by
        rw [Real.sq_sqrt hℓ]
        linarith [mul_nonneg (mul_nonneg zero_le_two hx₁.le) (Real.sqrt_nonneg ℓ)]
      linarith
    nlinarith [Real.sqrt_nonneg ℓ]

/-- Exponential shift decay for `airyEnv` along `w + ℓ`: for `w ∈ slitPlane` and `ℓ ≥ 0`,
`airyEnv (w + ℓ) ≤ airyEnv w * exp (-2 * ℓ * Re(w^{1/2}))`. -/
lemma airyEnv_add_real_le {w : ℂ} (hw : w ∈ Complex.slitPlane) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    airyEnv (w + (ℓ : ℂ)) ≤ airyEnv w * Real.exp (-2 * ℓ * (w ^ (1 / 2 : ℂ)).re) := by
  let φ : ℝ → ℝ := fun t => ((w + (t : ℂ)) ^ (3 / 2 : ℂ)).re
  have hderiv_all : ∀ t ∈ Icc 0 ℓ,
      HasDerivAt φ ((3 / 2 : ℝ) * ((w + (t : ℂ)) ^ (1 / 2 : ℂ)).re) t := by
    intro t ht
    have hsp := not_nonpos_add_ofReal hw ht.1
    have hcp := (hasDerivAt_id (w + (t : ℂ))).cpow_const (c := (3 / 2 : ℂ)) hsp
    have hcomp := hcp.comp t ((hasDerivAt_id t).ofReal_comp.const_add w)
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp
    refine hre.congr_deriv ?_
    rw [Complex.reCLM_apply]
    dsimp only [id]
    have hpow_sub : (3 / 2 : ℂ) - 1 = (1 / 2 : ℂ) := by norm_num
    have h32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by norm_num
    rw [mul_one, Complex.ofReal_one, mul_one, hpow_sub, h32, Complex.re_ofReal_mul]
  have hcont : ContinuousOn φ (Icc 0 ℓ) :=
    fun t ht => (hderiv_all t ht).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ioo 0 ℓ, HasDerivAt φ ((3 / 2 : ℝ) * ((w + (t : ℂ)) ^ (1 / 2 : ℂ)).re) t :=
    fun t ht => hderiv_all t (Ioo_subset_Icc_self ht)
  have hmv : (3 / 2 : ℝ) * (w ^ (1 / 2 : ℂ)).re * ℓ ≤ φ ℓ - φ 0 := by
    rcases hℓ.eq_or_lt with rfl | hℓ_pos
    · simp
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope φ _ hℓ_pos hcont hderiv
      have hc_ge : (w ^ (1 / 2 : ℂ)).re ≤ ((w + (c : ℂ)) ^ (1 / 2 : ℂ)).re :=
        (re_cpow_half_add_real_bounds hw hc.1.le).1
      rw [eq_div_iff (by linarith)] at hslope
      nlinarith
  have hφ0 : φ 0 = (w ^ (3 / 2 : ℂ)).re := by simp [φ]
  have hexp : -(4 / 3 : ℝ) * φ ℓ ≤ -(4 / 3 : ℝ) * (w ^ (3 / 2 : ℂ)).re - 2 * ℓ * (w ^ (1 / 2 : ℂ)).re := by
    linarith [hφ0]
  unfold airyEnv
  calc Real.exp (-(4 / 3 : ℝ) * φ ℓ)
      ≤ Real.exp (-(4 / 3 : ℝ) * (w ^ (3 / 2 : ℂ)).re + (-2 * ℓ * (w ^ (1 / 2 : ℂ)).re)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(4 / 3 : ℝ) * (w ^ (3 / 2 : ℂ)).re) * Real.exp (-2 * ℓ * (w ^ (1 / 2 : ℂ)).re) :=
        Real.exp_add _ _

/-- On `circleMap 0 R θ` (`0 < R`, `θ ∈ (-π, π)`), `Re((circleMap 0 R θ)^{1/2}) = √R cos(θ / 2)`. -/
lemma re_cpow_half_circleMap {R θ : ℝ} (hR : 0 < R) (hθ : θ ∈ Ioo (-π) π) :
    ((circleMap 0 R θ ^ (1 / 2 : ℂ)).re) = √R * Real.cos (θ / 2) := by
  have hnorm : ‖circleMap 0 R θ‖ = R := by simp [norm_circleMap_zero, abs_of_pos hR]
  have hnz : circleMap 0 R θ ≠ 0 := by intro h0; rw [h0, norm_zero] at hnorm; linarith
  have harg : (circleMap 0 R θ).arg = θ := by
    rw [circleMap, zero_add, Complex.exp_mul_I]
    exact Complex.arg_mul_cos_add_sin_mul_I hR ⟨hθ.1, hθ.2.le⟩
  rw [Complex.cpow_def_of_ne_zero hnz, Complex.exp_re]
  have hre : (Complex.log (circleMap 0 R θ) * (1 / 2 : ℂ)).re = Real.log R / 2 := by
    simp [Complex.log_re, hnorm]; ring
  have him : (Complex.log (circleMap 0 R θ) * (1 / 2 : ℂ)).im = θ / 2 := by
    simp [Complex.log_im, harg]; ring
  rw [hre, him, show Real.log R / 2 = Real.log R * (1 / 2 : ℝ) by ring,
    ← Real.rpow_def_of_pos hR, ← Real.sqrt_eq_rpow]

/-- `‖1 + circleMap 0 R θ / R‖ = 2 * cos(θ / 2)` for `0 < R` and `θ ∈ [-π, π]`. -/
lemma norm_one_add_circleMap_div {R θ : ℝ} (hR : 0 < R) (hθ : θ ∈ Icc (-π) π) :
    ‖1 + circleMap 0 R θ / (R : ℂ)‖ = 2 * Real.cos (θ / 2) := by
  have hcos_nn : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have h_eq : 1 + circleMap 0 R θ / (R : ℂ) =
      (((1 + Real.cos θ : ℝ) : ℂ) + (Real.sin θ : ℂ) * I) := by
    have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    rw [circleMap, zero_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    field_simp [hRc]
    push_cast; ring
  have hsq : (1 + Real.cos θ) ^ 2 + Real.sin θ ^ 2 = (2 * Real.cos (θ / 2)) ^ 2 := by
    have h1 := Real.cos_sq_add_sin_sq θ
    have h2 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
      have := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at this
      exact this
    nlinarith
  rw [h_eq, Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
    zero_add]
  rw [← sq, ← sq, hsq, Real.sqrt_sq (by linarith)]

/-! ### Section 3: Covered-Arc Gamma Integral & Elementary Line Bounds -/

/-- Gamma scaling identity: `∫ t in Ioi 0, t ^ (k - 1 / 2) * exp (-s * t) = Γ(k + 1 / 2) * s ^ (-(k + 1 / 2))`
for `s > 0` and `k : ℕ`. -/
lemma integral_Ioi_rpow_mul_exp_neg {s : ℝ} (hs : 0 < s) (k : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t) =
      Real.Gamma ((k : ℝ) + 1 / 2) * s ^ (-((k : ℝ) + 1 / 2)) := by
  have hp_pos : 0 < (k : ℝ) + 1 / 2 := by positivity
  have hG := Real.Gamma_eq_integral hp_pos
  have h_sub : ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ ((k : ℝ) - 1 / 2) =
      s * ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (s * t) ^ ((k : ℝ) - 1 / 2) := by
    have hm := MeasureTheory.integral_comp_mul_left_Ioi
      (fun u : ℝ => Real.exp (-u) * u ^ ((k : ℝ) - 1 / 2)) 0 hs
    rw [mul_zero] at hm
    have h2 := (inv_smul_eq_iff₀ hs.ne').mp hm.symm
    simpa [smul_eq_mul] using h2
  have hpull : ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (s * t) ^ ((k : ℝ) - 1 / 2) =
      s ^ ((k : ℝ) - 1 / 2) * ∫ t in Ioi (0 : ℝ), t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [Real.mul_rpow hs.le ht.le, show -(s * t) = -s * t by ring]; ring
  have hG' : Real.Gamma ((k : ℝ) + 1 / 2) =
      ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ ((k : ℝ) - 1 / 2) := by
    rw [hG]; congr 2; ext u; ring_nf
  have h_pow : s * s ^ ((k : ℝ) - 1 / 2) = s ^ ((k : ℝ) + 1 / 2) := by
    conv_lhs => arg 1; rw [← Real.rpow_one s]
    rw [← Real.rpow_add hs]; congr 1; ring
  have h_neg : (s ^ ((k : ℝ) + 1 / 2))⁻¹ = s ^ (-((k : ℝ) + 1 / 2)) :=
    (Real.rpow_neg hs.le _).symm
  have h_prod : Real.Gamma ((k : ℝ) + 1 / 2) =
      s ^ ((k : ℝ) + 1 / 2) * ∫ t in Ioi (0 : ℝ), t ^ ((k : ℝ) - 1 / 2) * Real.exp (-s * t) := by
    rw [hG', h_sub, hpull, ← mul_assoc, h_pow]
  have hsp_nz : s ^ ((k : ℝ) + 1 / 2) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
  rw [h_prod, mul_assoc, mul_comm (∫ t in Ioi (0 : ℝ), _), ← mul_assoc, ← h_neg,
    mul_inv_cancel₀ hsp_nz, one_mul]

/-- Concavity lower bound: `(63 / 100) * min 1 y ≤ 1 - exp (-y)` for all `y ≥ 0`. -/
lemma sixtythree_hundredths_min_le_one_sub_exp {y : ℝ} (hy : 0 ≤ y) :
    (63 / 100 : ℝ) * min 1 y ≤ 1 - Real.exp (-y) := by
  have he1 : (2.71828 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h63 : (63 / 100 : ℝ) ≤ 1 - Real.exp (-1) := by
    rw [Real.exp_neg]
    have hinv : (Real.exp 1)⁻¹ < (2.71828 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num) he1
    linarith
  rcases le_total 1 y with hy1 | hy1
  · rw [min_eq_left hy1]
    have hexp_le : Real.exp (-y) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    linarith
  · rw [min_eq_right hy1]
    have hexp_conv : Real.exp (-y) ≤ (1 - y) * Real.exp 0 + y * Real.exp (-1) := by
      have hconv := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (-1 : ℝ))
        (show 0 ≤ 1 - y by linarith) hy (by ring)
      simpa only [smul_eq_mul, mul_zero, add_zero, mul_neg, mul_one, zero_add] using hconv
    rw [Real.exp_zero] at hexp_conv
    have h_line : (1 - Real.exp (-1)) * y ≤ 1 - Real.exp (-y) := by nlinarith
    exact le_trans (mul_le_mul_of_nonneg_right h63 hy) h_line

/-- Power perturbation bound: `|(1 + t)^m - 1| ≤ m * |t| * exp (m * |t|)` for all `t : ℝ`, `m : ℕ`. -/
lemma abs_one_add_pow_sub_one_le (t : ℝ) (m : ℕ) :
    |(1 + t) ^ m - 1| ≤ (m : ℝ) * |t| * Real.exp ((m : ℝ) * |t|) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h_diff : (1 + t) ^ (k + 1) - 1 = ((1 + t) ^ k - 1) * (1 + t) + t := by ring
    have h1t : |1 + t| ≤ Real.exp |t| := by
      have ha : |(1 : ℝ) + t| ≤ 1 + |t| := by
        simpa [abs_one] using abs_add_le (1 : ℝ) t
      linarith [Real.add_one_le_exp |t|]
    have hexp1 : (1 : ℝ) ≤ Real.exp ((k : ℝ) * |t|) :=
      Real.one_le_exp (mul_nonneg (Nat.cast_nonneg k) (abs_nonneg t))
    calc |(1 + t) ^ (k + 1) - 1|
        = |((1 + t) ^ k - 1) * (1 + t) + t| := by rw [h_diff]
      _ ≤ |((1 + t) ^ k - 1) * (1 + t)| + |t| := abs_add_le _ _
      _ = |(1 + t) ^ k - 1| * |1 + t| + |t| := by rw [abs_mul]
      _ ≤ ((k : ℝ) * |t| * Real.exp ((k : ℝ) * |t|)) * Real.exp |t| + |t| :=
          add_le_add (mul_le_mul ih h1t (abs_nonneg _) (by positivity)) le_rfl
      _ = (k : ℝ) * |t| * Real.exp (((k : ℝ) + 1) * |t|) + |t| := by
          rw [mul_assoc, ← Real.exp_add, show (k : ℝ) * |t| + |t| = ((k : ℝ) + 1) * |t| by ring]
      _ ≤ (k : ℝ) * |t| * Real.exp (((k : ℝ) + 1) * |t|) +
            1 * |t| * Real.exp (((k : ℝ) + 1) * |t|) := by
          have hexp2 : 1 ≤ Real.exp (((k : ℝ) + 1) * |t|) :=
            Real.one_le_exp (by positivity)
          nlinarith [abs_nonneg t]
      _ = ((k + 1 : ℕ) : ℝ) * |t| * Real.exp (((k + 1 : ℕ) : ℝ) * |t|) := by
          push_cast; ring

/-- Exponential tail bound for `virasoroPsiTilde` on `[A, B] ⊆ [1, A_{c'}^2]` (`ς ≤ 1/2`). -/
lemma virasoro_pos_real_norm_tail_le {c' A B : ℝ}
    (hc' : virasoroCQEnv ≤ c') (hς_nn : 0 ≤ virasoroSigma c') (hς_half : virasoroSigma c' ≤ 1 / 2)
    (hA1 : 1 ≤ A) (hAB : A ≤ B) (hB : B ≤ virasoroAC c' ^ 2)
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g) :
    ∫ x in A..B, ‖virasoroPsiTilde c' g (x : ℂ)‖ ≤
      (6 / 5 : ℝ) * virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * A) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc'
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
        (c_PJ_complex_le_virasoroCQEnv.trans hc'))
  have hΨ_cont : ContinuousOn (fun x : ℝ => virasoroPsiTilde c' g (x : ℂ)) (Icc A B) := by
    refine (virasoroPsiTilde_analyticOnNhd hc'_1000 hg).continuousOn.comp
      continuous_ofReal.continuousOn fun x hx => ?_
    exact virasoro_closedBall_subset_psiDom hc'_pos
      (by rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hx.1])]; exact hx.2.trans hB)
  have hi_l : IntervalIntegrable (fun x : ℝ => ‖virasoroPsiTilde c' g (x : ℂ)‖) volume A B :=
    (continuous_norm.comp_continuousOn hΨ_cont).intervalIntegrable_of_Icc hAB
  have hi_r : IntervalIntegrable (fun x : ℝ => virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * x)) volume A B :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable A B
  have h_pt : ∀ x ∈ Icc A B,
      ‖virasoroPsiTilde c' g (x : ℂ)‖ ≤ virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * x) := by
    intro x hx
    have hx1 : 1 ≤ x := hA1.trans hx.1
    have hx_pos : 0 < x := by linarith
    have hx_ball : (x : ℂ) ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]
      exact hx.2.trans hB
    have hcut : ¬ ((x : ℂ).im = 0 ∧ (x : ℂ).re ≤ 0) := fun h0 => by
      simp only [Complex.ofReal_re] at h0; linarith
    have h_env := (lemmaQ_part2 hc' hg hM_pos).2.2 (x : ℂ) hx_ball hcut
    have h_re_sqrt : ((x : ℂ) ^ (1 / 2 : ℂ)).re = √x := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx_pos.le,
        Complex.ofReal_re, Real.sqrt_eq_rpow]
    have h_env_val : airyEnv (x : ℂ) = Real.exp (-(4 / 3 : ℝ) * (x ^ (3 / 2 : ℝ))) := by
      unfold airyEnv
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx_pos.le,
        Complex.ofReal_re]
    have hx32 : x ≤ x ^ (3 / 2 : ℝ) := by
      conv_lhs => rw [← Real.rpow_one x]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hsqrt_le : √x ≤ x := by
      rw [Real.sqrt_eq_rpow]
      conv_rhs => rw [← Real.rpow_one x]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h_exp : -(4 / 3 : ℝ) * (x ^ (3 / 2 : ℝ)) + virasoroSigma c' * √x ≤ -(5 / 6 : ℝ) * x := by
      nlinarith
    have h_inv_le1 : ‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos, h_re_sqrt,
        Real.rpow_neg hx_pos.le, ← Real.sqrt_eq_rpow, ← mul_inv, Real.mul_self_sqrt hx_pos.le]
      exact inv_le_one_of_one_le₀ hx1
    calc ‖virasoroPsiTilde c' g (x : ℂ)‖
        ≤ virasoroEnvC0 * Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
            Real.exp (virasoroSigma c' * √x) * (‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹) := by
          simpa only [h_re_sqrt, h_env_val, mul_assoc] using h_env
      _ ≤ virasoroEnvC0 * (Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
            Real.exp (virasoroSigma c' * √x)) * 1 := by
          have hnn : 0 ≤ virasoroEnvC0 * Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
              Real.exp (virasoroSigma c' * √x) := by
            have := virasoroEnvC0_pos; positivity
          exact (mul_le_mul_of_nonneg_left h_inv_le1 hnn).trans_eq (by ring)
      _ = virasoroEnvC0 * Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) + virasoroSigma c' * √x) := by
          rw [mul_one, ← Real.exp_add]
      _ ≤ virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * x) := by
          gcongr; exact virasoroEnvC0_pos.le
  have hmono := intervalIntegral.integral_mono_on hAB hi_l hi_r h_pt
  have hderiv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => -((6 / 5 : ℝ) * virasoroEnvC0) * Real.exp (-(5 / 6 : ℝ) * t))
        (virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -(5 / 6 : ℝ) * t) (-(5 / 6 : ℝ)) x := by
      simpa using (hasDerivAt_id x).const_mul (-(5 / 6 : ℝ))
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(5 / 6 : ℝ) * t))
        (Real.exp (-(5 / 6 : ℝ) * x) * (-(5 / 6 : ℝ))) x :=
      (Real.hasDerivAt_exp _).comp x h1
    exact (h2.const_mul (-((6 / 5 : ℝ) * virasoroEnvC0))).congr_deriv (by ring)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi_r
  have hexpB_nn : 0 ≤ (6 / 5 : ℝ) * virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * B) := by
    have := virasoroEnvC0_pos; positivity
  linarith

/-- Moment identity in `u`-coordinates on `[a, b] ⊆ [-A_{c'}^2, A_{c'}^2]`:
`∫ u in a..b, (-u) * (virasoroPsiTilde c' g (u : ℂ)).re = M⁻¹ * ∫ t in Δ(b)..Δ(a), (-u_T(t)) * g(t) * V(t)`. -/
lemma virasoroPsiTilde_moment_integral_eq {c' a b : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g)
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b) :
    ∫ u in a..b, (-u) * (virasoroPsiTilde c' g (u : ℂ)).re =
      (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c' b)..(virasoroDeltaChart c' a),
          (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t) := by
  have hc'_pos : 0 < c' := by linarith
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h1 : ∫ u in a..b, (-u) * (virasoroPsiTilde c' g (u : ℂ)).re =
      -((virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
        ∫ u in a..b, ((-u) * (g (virasoroDeltaChart c' u) *
          virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
          deriv (virasoroDeltaChart c') u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    rw [virasoroPsiTilde_re_ofReal hc'_pos hg (hu_mem u hu)]
    ring
  have hsub : ∫ u in a..b, ((-u) * (g (virasoroDeltaChart c' u) *
        virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
        deriv (virasoroDeltaChart c') u =
      ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
        (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t) := by
    have hcont_t : ContinuousOn
        (fun t : ℝ => (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t))
        (virasoroDeltaChart c' '' Set.uIcc a b) := by
      have h_ut_cont : ContinuousOn (fun t : ℝ => -virasoroUT c' t)
          (virasoroDeltaChart c' '' Set.uIcc a b) := by
        intro t ht
        rcases ht with ⟨u, hu, rfl⟩
        rw [Set.uIcc_of_le hab] at hu
        have hdiv := virasoroDeltaChart_div_mem hc'_pos (hu_mem u hu)
        have hξ_open : ((virasoroDeltaChart c' u / c' : ℝ) : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
          rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have h1 : |virasoroDeltaChart c' u / c' - xiBar| ≤ virasoroChartR0 :=
            abs_le.mpr ⟨by linarith [hdiv.1], by linarith [hdiv.2]⟩
          exact h1.trans_lt (chartParams.hr_xi0_le.trans_lt (half_lt_self virasoroRXiInf_pos))
        have hcont_at : ContinuousAt (fun x : ℝ => virasoroUChart c' (x / c')) (virasoroDeltaChart c' u) := by
          unfold virasoroUChart
          have hcomp := (virasoroUInf_an _ hξ_open).continuousAt.comp_of_eq
            (Complex.continuous_ofReal.comp (continuous_id.div_const c')).continuousAt rfl
          exact (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hcomp))
        exact hcont_at.neg.continuousWithinAt
      refine h_ut_cont.mul ((hg.cont.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono ?_)
      rintro t ⟨u, hu, rfl⟩
      rw [Set.uIcc_of_le hab] at hu
      exact (virasoroDeltaChart_pos hc'_pos (hu_mem u hu)).le
    have hderiv_at : ∀ u ∈ Set.uIcc a b,
        HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
      rw [Set.uIcc_of_le hab] at hu
      have hd := virasoroDeltaChart_hasDerivAt hc'_pos (hu_mem u hu)
      exact hd.deriv ▸ hd
    -- Use `continuousOn_deriv_virasoroDeltaChart` logic directly via `virasoroDeltaChart_hasDerivAt`
    have hcont_der : ContinuousOn (deriv (virasoroDeltaChart c')) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      let G : ℝ → ℝ := fun u =>
        c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re
      have hG_cont : ContinuousOn G (Icc a b) := by
        intro u hu
        have hw : ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
          have h1 := virasoro_u_mem_open_ball hc'_pos (u := (u : ℂ))
            (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu_mem u hu)
          rwa [show (u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
            ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) by push_cast; rfl] at h1
        have hd_an := (virasoroXiInf_an.deriv _ hw).continuousAt
        have hcomp := hd_an.comp_of_eq
          (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).continuousAt rfl
        exact (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hcomp)).continuousWithinAt
      exact hG_cont.congr fun u hu => (virasoroDeltaChart_hasDerivAt hc'_pos (hu_mem u hu)).deriv
    have hcov := intervalIntegral.integral_comp_mul_deriv' hderiv_at hcont_der hcont_t
    calc ∫ u in a..b, ((-u) * (g (virasoroDeltaChart c' u) *
            virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
            deriv (virasoroDeltaChart c') u
        = ∫ u in a..b, ((-virasoroUT c' (virasoroDeltaChart c' u)) *
            (g (virasoroDeltaChart c' u) *
              virasoroProblem.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
            deriv (virasoroDeltaChart c') u := by
          refine intervalIntegral.integral_congr fun u hu => ?_
          rw [Set.uIcc_of_le hab] at hu
          have huc : virasoroUT c' (virasoroDeltaChart c' u) = u := by
            unfold virasoroUT
            exact virasoroUChart_deltaChart hc'_pos (hu_mem u hu)
          rw [huc]
      _ = ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
            (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t) := hcov
  rw [h1, hsub, intervalIntegral.integral_symm (virasoroDeltaChart c' b) (virasoroDeltaChart c' a)]
  ring

/-! ### Section 4: Shifted Test Function, Line Estimate (`hI_line`), and Arc Estimate (`hArc_cov`, `hArc_unc`) -/

/-- Shifted quadrature test `f_{k, ℓ}(u) := \widetilde\Psi_V(u + ℓ) (1 + u / R)^{k + 1}`. -/
noncomputable def virasoroShiftedFun (c' R ℓ : ℝ) (g : ℝ → ℝ) (k : ℕ) (u : ℂ) : ℂ :=
  virasoroPsiTilde c' g (u + (ℓ : ℂ)) * (1 + u / (R : ℂ)) ^ (k + 1)

/-- Truncated first band moment `B_1^{(k)} := ∫_{-R}^{u_T} min(1, (k+1)(-u)/R) \widetilde\Psi_V(u) du`. -/
noncomputable def virasoroBandB1k (c' R T : ℝ) (g : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ u in (-R)..(virasoroUT c' T),
    min 1 (((k : ℝ) + 1) * (-u) / R) * (virasoroPsiTilde c' g (u : ℂ)).re

lemma virasoroBandB1k_nonneg {c' R T : ℝ} (hc' : virasoroCQEnv ≤ c')
    (hR_nn : 0 ≤ R) (hR_ub : R ≤ virasoroAC c' ^ 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' (virasoroAC c' ^ 2) ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-R)) (huT_hi : virasoroUT c' T ≤ 0) (k : ℕ) :
    0 ≤ virasoroBandB1k c' R T g k := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc'
  have hu_mem := virasoroUT_between hc'_pos (by linarith : -(virasoroAC c' ^ 2) ≤ -R) le_rfl
    (by linarith [hR_nn, hR_ub] : -R ≤ virasoroAC c' ^ 2) hT_lo hT_hi
  refine intervalIntegral.integral_nonneg hu_mem.1.1 fun u hu => ?_
  have hΨ_nn : 0 ≤ (virasoroPsiTilde c' g (u : ℂ)).re := by
    refine (lemmaQ_part3 hc' hg).1 u (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (virasoroAC c')]⟩) ?_
    rw [← hu_mem.2]
    exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (virasoroAC c')]⟩
      ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2, sq_nonneg (virasoroAC c')]⟩ hu.2
  have hmin_nn : 0 ≤ min (1 : ℝ) (((k : ℝ) + 1) * (-u) / R) :=
    le_min zero_le_one (div_nonneg (mul_nonneg (by positivity) (by linarith [hu.2, huT_hi])) hR_nn)
  exact mul_nonneg hmin_nn hΨ_nn

lemma virasoroBandB1_le_B1k {c' R T : ℝ} (hc' : virasoroCQEnv ≤ c')
    (hR_pos : 0 < R) (hR_ub : R ≤ virasoroAC c' ^ 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-R)) (k : ℕ) :
    virasoroBandB1 c' R T g ≤ virasoroBandB1k c' R T g k := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc'
  have hc'_24 : 24 ≤ c' := by have := virasoroCQEnv_ge; linarith
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
        (c_PJ_complex_le_virasoroCQEnv.trans hc'))
  have hΔ_lo : virasoroDeltaChart c' (virasoroAC c' ^ 2) ≤ virasoroDeltaChart c' 0 :=
    (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [sq_nonneg (virasoroAC c')], sq_nonneg _⟩
      ⟨by linarith [sq_nonneg (virasoroAC c')], le_rfl⟩ (sq_nonneg _)
  have hu_mem := virasoroUT_between hc'_pos (by linarith : -(virasoroAC c' ^ 2) ≤ -R)
    (sq_nonneg _) (by linarith : -R ≤ 0) hT_lo hT_hi
  have hmom := virasoroPsiTilde_moment_integral_eq hc'_24 hg.1
    (by linarith : -(virasoroAC c' ^ 2) ≤ -R) (by linarith [hu_mem.1.2, sq_nonneg (virasoroAC c')])
    hu_mem.1.1
  rw [hu_mem.2] at hmom
  have hB1_eq : virasoroBandB1 c' R T g =
      ∫ u in (-R)..(virasoroUT c' T), ((-u) / R) * (virasoroPsiTilde c' g (u : ℂ)).re := by
    unfold virasoroBandB1
    rw [mul_assoc, ← hmom, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => by ring
  rw [hB1_eq]
  unfold virasoroBandB1k
  have hΨ_cont : ContinuousOn (fun u : ℝ => (virasoroPsiTilde c' g (u : ℂ)).re)
      (Icc (-R) (virasoroUT c' T)) := by
    refine Complex.continuous_re.comp_continuousOn
      ((virasoroPsiTilde_analyticOnNhd hc'_1000 hg.1).continuousOn.comp
        continuous_ofReal.continuousOn fun u hu => ?_)
    exact virasoro_closedBall_subset_psiDom hc'_pos (by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (virasoroAC c')]⟩)
  have hi_l : IntervalIntegrable
      (fun u : ℝ => (-u / R) * (virasoroPsiTilde c' g (u : ℂ)).re) volume (-R) (virasoroUT c' T) :=
    (((continuousOn_id.neg.div_const R).mul hΨ_cont)).intervalIntegrable_of_Icc hu_mem.1.1
  have hi_r : IntervalIntegrable
      (fun u : ℝ => min 1 (((k : ℝ) + 1) * (-u) / R) * (virasoroPsiTilde c' g (u : ℂ)).re)
      volume (-R) (virasoroUT c' T) :=
    ((ContinuousOn.inf continuousOn_const ((continuousOn_const.mul continuousOn_id.neg).div_const R)).mul
      hΨ_cont).intervalIntegrable_of_Icc hu_mem.1.1
  refine intervalIntegral.integral_mono_on hu_mem.1.1 hi_l hi_r fun u hu => ?_
  have hΨ_nn : 0 ≤ (virasoroPsiTilde c' g (u : ℂ)).re := by
    refine (lemmaQ_part3 hc' hg).1 u (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (virasoroAC c')]⟩) ?_
    rw [← hu_mem.2]
    exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (virasoroAC c')]⟩
      ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2, sq_nonneg (virasoroAC c')]⟩ hu.2
  have hu_le1 : (-u) / R ≤ 1 := (div_le_one hR_pos).mpr (by linarith [hu.1])
  have hu_le_k : (-u) / R ≤ ((k : ℝ) + 1) * (-u) / R := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (by linarith [hu.2, hu_mem.1.2]) hk1) hR_pos.le
  exact mul_le_mul_of_nonneg_right (le_min hu_le1 hu_le_k) hΨ_nn

private lemma virasoro_line_top_bound {c' R T ℓ : ℝ}
    (hc' : virasoroCQEnv ≤ c') (hς_nn : 0 ≤ virasoroSigma c') (hς_half : virasoroSigma c' ≤ 1 / 2)
    (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ virasoroAC c' ^ 2)
    (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    (_hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr))
    (huT_ge : -virasoroAThr ≤ virasoroUT c' T) (hΔ_uT : virasoroDeltaChart c' (virasoroUT c' T) = T)
    (huT_le_1 : virasoroUT c' T ≤ -1)
    (hΨ_cont_all : ContinuousOn (fun v : ℝ => (virasoroPsiTilde c' g (v : ℂ)).re)
      (Icc (-R) (virasoroAC c' ^ 2)))
    {k : ℕ} (hk5 : 5 ≤ k) :
    ∫ v in (-R + ℓ)..(R + ℓ), (virasoroPsiTilde c' g (v : ℂ)).re ≤
      -(∫ v in (-R)..(-R + ℓ), (virasoroPsiTilde c' g (v : ℂ)).re) - virasoroBandB2 c' R g +
        virasoroEnvC0 * ((k : ℝ) + 1) / R + virasoroDeltaLobe c' g := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc'
  have hc'_24 : 24 ≤ c' := by have := virasoroCQEnv_ge; linarith
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
        (c_PJ_complex_le_virasoroCQEnv.trans hc'))
  have ha : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; have := virasoroCQEnv_ge; linarith
  have hR_pos : 0 < R := by linarith
  have hA2_nn : 0 ≤ virasoroAC c' ^ 2 := sq_nonneg _
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  have hi_Ψ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ virasoroAC c' ^ 2 →
      IntervalIntegrable (fun v : ℝ => (virasoroPsiTilde c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 => (hΨ_cont_all.mono (Icc_subset_Icc ha0 hb0)).intervalIntegrable_of_Icc hab
  have h_int_full : ∫ v in (-R + ℓ)..(R + ℓ), (virasoroPsiTilde c' g (v : ℂ)).re =
      (∫ v in (-R + ℓ)..(virasoroAC c' ^ 2), (virasoroPsiTilde c' g (v : ℂ)).re) -
        ∫ v in (R + ℓ)..(virasoroAC c' ^ 2), (virasoroPsiTilde c' g (v : ℂ)).re := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hi_Ψ (-R + ℓ) (R + ℓ) (by linarith) (by linarith) (by linarith))
      (hi_Ψ (R + ℓ) (virasoroAC c' ^ 2) (by linarith) (by linarith) le_rfl)
    linarith only [hadd]
  have h_top_bound : ∫ v in (-R + ℓ)..(virasoroAC c' ^ 2), (virasoroPsiTilde c' g (v : ℂ)).re ≤
      -(∫ v in (-R)..(-R + ℓ), (virasoroPsiTilde c' g (v : ℂ)).re) - virasoroBandB2 c' R g +
        virasoroDeltaLobe c' g := by
    have hR'_nn : 0 ≤ R - ℓ := by linarith
    have hR'_le : R - ℓ ≤ virasoroAC c' ^ 2 := by linarith
    have hneg_R' : -R + ℓ = -(R - ℓ) := by ring
    have huT_ge' : -(R - ℓ) ≤ virasoroUT c' T := by linarith
    have hT_le_ΔR' : T ≤ virasoroDeltaChart c' (-(R - ℓ)) := by
      rw [← hΔ_uT]
      exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ huT_ge'
    have hQ_eq := ((lemmaQ_part3 hc' hg).2.2.2.2 (R - ℓ) hR'_nn hR'_le hT_le_ΔR').1
    rw [← hneg_R'] at hQ_eq
    have h_band_cov := virasoroPsiTilde_integral_eq hc'_24 hg.1
      (by linarith : -(virasoroAC c' ^ 2) ≤ -R) (by linarith) (by linarith : -R ≤ -R + ℓ)
    have h_vac_le : ∫ t in Ioi (0 : ℝ), g t * virasoroProblem.cardyV (c' / 12) t ≤ 0 := by
      have hv := hg.2.2.1; unfold FixedWeightProblem.gVac at hv; nlinarith [Real.pi_pos]
    set t_lo := virasoroDeltaChart c' (virasoroAC c' ^ 2)
    set t_mid := virasoroDeltaChart c' (-R + ℓ)
    set t_hi := virasoroDeltaChart c' (-R)
    have ht_lo_pos : 0 < t_lo := virasoroDeltaChart_pos hc'_pos (abs_of_nonneg hA2_nn).le
    have ht_lo_mid : t_lo ≤ t_mid :=
      (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn ⟨by linarith, by linarith⟩
        ⟨by linarith, le_rfl⟩ (by linarith)
    have ht_mid_hi : t_mid ≤ t_hi :=
      (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ (by linarith)
    have hgv_int : IntegrableOn (fun t => g t * virasoroProblem.cardyV (c' / 12) t) (Ioi 0) :=
      hg.1.int_cardy.norm.mono'
        (((hg.1.cont.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
          Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
        (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_abs])
    have hsp1 : ∫ t in Ioi (0 : ℝ), g t * virasoroProblem.cardyV (c' / 12) t =
        (∫ t in Ioc 0 t_lo, g t * virasoroProblem.cardyV (c' / 12) t) +
          ∫ t in Ioi t_lo, g t * virasoroProblem.cardyV (c' / 12) t := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hgv_int.mono_set Ioc_subset_Ioi_self) (hgv_int.mono_set (Ioi_subset_Ioi ht_lo_pos.le)),
        Ioc_union_Ioi_eq_Ioi ht_lo_pos.le]
    have hsp2 : ∫ t in Ioi t_lo, g t * virasoroProblem.cardyV (c' / 12) t =
        (∫ t in Ioc t_lo t_mid, g t * virasoroProblem.cardyV (c' / 12) t) +
          ∫ t in Ioi t_mid, g t * virasoroProblem.cardyV (c' / 12) t := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((hgv_int.mono_set (Ioi_subset_Ioi ht_lo_pos.le)).mono_set Ioc_subset_Ioi_self)
        (hgv_int.mono_set (Ioi_subset_Ioi (ht_lo_pos.le.trans ht_lo_mid))),
        Ioc_union_Ioi_eq_Ioi ht_lo_mid]
    have hsp3 : ∫ t in Ioi t_mid, g t * virasoroProblem.cardyV (c' / 12) t =
        (∫ t in Ioc t_mid t_hi, g t * virasoroProblem.cardyV (c' / 12) t) +
          ∫ t in Ioi t_hi, g t * virasoroProblem.cardyV (c' / 12) t := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((hgv_int.mono_set (Ioi_subset_Ioi (ht_lo_pos.le.trans ht_lo_mid))).mono_set Ioc_subset_Ioi_self)
        (hgv_int.mono_set (Ioi_subset_Ioi ((ht_lo_pos.le.trans ht_lo_mid).trans ht_mid_hi))),
        Ioc_union_Ioi_eq_Ioi ht_mid_hi]
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
    have h_sum_t : ∫ t in t_lo..t_mid, g t * virasoroProblem.cardyV (c' / 12) t ≤
        -(∫ t in t_mid..t_hi, g t * virasoroProblem.cardyV (c' / 12) t) -
          (∫ t in Ici t_hi, g t * virasoroProblem.cardyV (c' / 12) t) +
          ∫ t in (0 : ℝ)..t_lo, |g t| * virasoroProblem.cardyV (c' / 12) t := by
      rw [intervalIntegral.integral_of_le ht_lo_mid, intervalIntegral.integral_of_le ht_mid_hi, hIci_Ioi]
      linarith only [h_vac_le, hsp1, hsp2, hsp3, h_lobe_eq]
    have hM_nn : 0 ≤ (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ := inv_nonneg.mpr hM_pos.le
    have hmul := mul_le_mul_of_nonneg_left h_sum_t hM_nn
    rw [← hQ_eq, mul_add, mul_sub, mul_neg] at hmul
    unfold virasoroBandB2 virasoroDeltaLobe
    linarith only [hmul, h_band_cov]
  have h_pos_tail : -(∫ v in (R + ℓ)..(virasoroAC c' ^ 2), (virasoroPsiTilde c' g (v : ℂ)).re) ≤
      (6 / 5 : ℝ) * virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * R) := by
    have h_norm : |∫ v in (R + ℓ)..(virasoroAC c' ^ 2), (virasoroPsiTilde c' g (v : ℂ)).re| ≤
        ∫ v in (R + ℓ)..(virasoroAC c' ^ 2), ‖virasoroPsiTilde c' g (v : ℂ)‖ := by
      calc |∫ v in (R + ℓ)..(virasoroAC c' ^ 2), (virasoroPsiTilde c' g (v : ℂ)).re|
          ≤ ∫ v in (R + ℓ)..(virasoroAC c' ^ 2), |(virasoroPsiTilde c' g (v : ℂ)).re| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun v : ℝ => (virasoroPsiTilde c' g (v : ℂ)).re) (μ := volume)
              (by linarith : R + ℓ ≤ virasoroAC c' ^ 2)
        _ ≤ ∫ v in (R + ℓ)..(virasoroAC c' ^ 2), ‖virasoroPsiTilde c' g (v : ℂ)‖ := by
            refine intervalIntegral.integral_mono_on (by linarith)
              ((continuous_abs.comp_continuousOn (hΨ_cont_all.mono (Icc_subset_Icc (by linarith) le_rfl))).intervalIntegrable_of_Icc (by linarith))
              ((continuous_norm.comp_continuousOn ((virasoroPsiTilde_analyticOnNhd hc'_1000 hg.1).continuousOn.comp continuous_ofReal.continuousOn fun v hv =>
                virasoro_closedBall_subset_psiDom hc'_pos (by rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith [hv.1], hv.2⟩))).intervalIntegrable_of_Icc (by linarith))
              fun v _ => Complex.abs_re_le_norm _
    have ht_le := @virasoro_pos_real_norm_tail_le c' (R + ℓ) (virasoroAC c' ^ 2) hc' hς_nn hς_half
      (by linarith) (by linarith) le_rfl g hg.1 hM_pos
    have hexp_mon : Real.exp (-(5 / 6 : ℝ) * (R + ℓ)) ≤ Real.exp (-(5 / 6 : ℝ) * R) :=
      Real.exp_le_exp.mpr (by linarith)
    have h1 := (abs_le.mp h_norm).1
    have hpos65 : (0 : ℝ) ≤ (6 / 5 : ℝ) * virasoroEnvC0 := by have := virasoroEnvC0_pos; positivity
    have := mul_le_mul_of_nonneg_left hexp_mon hpos65
    linarith only [h1, ht_le, this]
  have h_pos_tail_R : (6 / 5 : ℝ) * virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * R) ≤
      virasoroEnvC0 * ((k : ℝ) + 1) / R := by
    have h_xe : (5 / 6 : ℝ) * R * Real.exp (-(5 / 6 : ℝ) * R) ≤ 1 := by
      have := Real.add_one_le_exp ((5 / 6 : ℝ) * R)
      rw [show -(5 / 6 : ℝ) * R = -((5 / 6 : ℝ) * R) by ring, Real.exp_neg,
        mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    have hk6 : (6 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (by omega : 6 ≤ k + 1)
    have h_exp_R : Real.exp (-(5 / 6 : ℝ) * R) ≤ (6 / 5 : ℝ) / R := by
      rw [le_div_iff₀ hR_pos]; linarith
    have hC0_nn := virasoroEnvC0_pos.le
    calc (6 / 5 : ℝ) * virasoroEnvC0 * Real.exp (-(5 / 6 : ℝ) * R)
        ≤ (6 / 5 : ℝ) * virasoroEnvC0 * ((6 / 5 : ℝ) / R) := by gcongr
      _ = ((36 / 25 : ℝ) * virasoroEnvC0) / R := by ring
      _ ≤ (virasoroEnvC0 * 6) / R := div_le_div_of_nonneg_right (by nlinarith [virasoroEnvC0_pos]) hR_pos.le
      _ ≤ (virasoroEnvC0 * ((k : ℝ) + 1)) / R := by gcongr
      _ = virasoroEnvC0 * ((k : ℝ) + 1) / R := by ring
  linarith only [h_int_full, h_top_bound, h_pos_tail, h_pos_tail_R]

private lemma virasoro_line_band_piece {c' R T ℓ : ℝ}
    (hc' : virasoroCQEnv ≤ c') (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ virasoroAC c' ^ 2)
    (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (huT_Icc : virasoroUT c' T ∈ Icc (-virasoroAThr) (-1))
    (hΔ_uT : virasoroDeltaChart c' (virasoroUT c' T) = T)
    (hΨ_cont_all : ContinuousOn (fun v : ℝ => (virasoroPsiTilde c' g (v : ℂ)).re)
      (Icc (-R) (virasoroAC c' ^ 2)))
    (k : ℕ) :
    -(∫ v in (-R + ℓ)..(virasoroUT c' T),
        (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * (virasoroPsiTilde c' g (v : ℂ)).re) -
      (∫ v in (-R)..(-R + ℓ), (virasoroPsiTilde c' g (v : ℂ)).re) ≤
      -(63 / 100 : ℝ) * virasoroBandB1k c' R T g k := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc'
  have hR_pos : 0 < R := by linarith
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  set u_T := virasoroUT c' T
  let W : ℝ → ℝ := fun v => (1 + (v - ℓ) / R) ^ (k + 1)
  have hW_cont : Continuous W :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hnegRl_le_uT : -R + ℓ ≤ u_T := by linarith [huT_Icc.1]
  have huT_le_R : u_T ≤ R + ℓ := by linarith [huT_Icc.2]
  have h_mem_sub : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      Icc a b ⊆ Icc (-R) (virasoroAC c' ^ 2) := fun ha0 _ hb0 => Icc_subset_Icc ha0 (by linarith)
  have hi_Ψ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (virasoroPsiTilde c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 => (hΨ_cont_all.mono (h_mem_sub ha0 hab hb0)).intervalIntegrable_of_Icc hab
  have hi_WΨ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 =>
      ((continuousOn_const.sub hW_cont.continuousOn).mul
        (hΨ_cont_all.mono (h_mem_sub ha0 hab hb0))).intervalIntegrable_of_Icc hab
  have hi_B1k : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ =>
        min 1 (((k : ℝ) + 1) * (-v) / R) * (virasoroPsiTilde c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 =>
      (((continuous_const.min ((continuous_const.mul continuous_neg).div_const R)).continuousOn).mul
        (hΨ_cont_all.mono (h_mem_sub ha0 hab hb0))).intervalIntegrable_of_Icc hab
  have hΨ_nn_band : ∀ v : ℝ, -R ≤ v → v ≤ u_T → 0 ≤ (virasoroPsiTilde c' g (v : ℂ)).re := by
    intro v hv1 hv2
    refine (lemmaQ_part3 hc' hg).1 v (abs_le.mpr ⟨by linarith, by linarith [huT_Icc.2]⟩) ?_
    rw [← hΔ_uT]
    exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith [huT_Icc.2]⟩ ⟨by linarith [huT_Icc.1], by linarith [huT_Icc.2]⟩ hv2
  have h_low_left : (63 / 100 : ℝ) * ∫ v in (-R)..(-R + ℓ),
        min 1 (((k : ℝ) + 1) * (-v) / R) * (virasoroPsiTilde c' g (v : ℂ)).re ≤
      ∫ v in (-R)..(-R + ℓ), (virasoroPsiTilde c' g (v : ℂ)).re := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith)
      ((hi_B1k (-R) (-R + ℓ) le_rfl (by linarith) (by linarith)).const_mul _)
      (hi_Ψ (-R) (-R + ℓ) le_rfl (by linarith) (by linarith)) fun v hv => ?_
    have hΨ_nn := hΨ_nn_band v hv.1 (by linarith [hv.2, hnegRl_le_uT])
    have hm1 : (63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R) ≤ 1 := by
      linarith [min_le_left (1 : ℝ) (((k : ℝ) + 1) * (-v) / R)]
    calc (63 / 100 : ℝ) * (min 1 (((k : ℝ) + 1) * (-v) / R) * (virasoroPsiTilde c' g (v : ℂ)).re)
        = ((63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R)) * (virasoroPsiTilde c' g (v : ℂ)).re := by ring
      _ ≤ 1 * (virasoroPsiTilde c' g (v : ℂ)).re := mul_le_mul_of_nonneg_right hm1 hΨ_nn
      _ = (virasoroPsiTilde c' g (v : ℂ)).re := one_mul _
  have h_main_band : (63 / 100 : ℝ) * ∫ v in (-R + ℓ)..u_T,
        min 1 (((k : ℝ) + 1) * (-v) / R) * (virasoroPsiTilde c' g (v : ℂ)).re ≤
      ∫ v in (-R + ℓ)..u_T, (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hnegRl_le_uT
      ((hi_B1k (-R + ℓ) u_T (by linarith) hnegRl_le_uT huT_le_R).const_mul _)
      (hi_WΨ (-R + ℓ) u_T (by linarith) hnegRl_le_uT huT_le_R) fun v hv => ?_
    have hΨ_nn := hΨ_nn_band v (by linarith [hv.1]) hv.2
    have hbase_nn : 0 ≤ 1 + (v - ℓ) / R := by
      have hnum : 0 ≤ R + (v - ℓ) := by linarith [hv.1]
      have heq : 1 + (v - ℓ) / R = (R + (v - ℓ)) / R := by field_simp [hR_pos.ne']
      rw [heq]; exact div_nonneg hnum hR_pos.le
    have hbase_le : 1 + (v - ℓ) / R ≤ Real.exp (-(-v / R)) := by
      have hv_div : (v - ℓ) / R ≤ v / R := div_le_div_of_nonneg_right (by linarith) hR_pos.le
      have hexp1 : 1 + v / R ≤ Real.exp (v / R) := by linarith [Real.add_one_le_exp (v / R)]
      rw [show -(-v / R) = v / R by ring]
      linarith only [hv_div, hexp1]
    have hW_le : W v ≤ Real.exp (-(((k : ℝ) + 1) * (-v) / R)) := by
      dsimp [W]
      calc (1 + (v - ℓ) / R) ^ (k + 1)
          ≤ (Real.exp (-(-v / R))) ^ (k + 1) := pow_le_pow_left₀ hbase_nn hbase_le _
        _ = Real.exp (((k + 1 : ℕ) : ℝ) * (-(-v / R))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(((k : ℝ) + 1) * (-v) / R)) := by push_cast; ring_nf
    have h_min : (63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R) ≤ 1 - W v :=
      (sixtythree_hundredths_min_le_one_sub_exp
        (div_nonneg (mul_nonneg (by positivity) (by linarith [hv.2, huT_Icc.2])) hR_pos.le)).trans
        (sub_le_sub_left hW_le 1)
    calc (63 / 100 : ℝ) * (min 1 (((k : ℝ) + 1) * (-v) / R) * (virasoroPsiTilde c' g (v : ℂ)).re)
        = ((63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R)) * (virasoroPsiTilde c' g (v : ℂ)).re := by ring
      _ ≤ (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re := mul_le_mul_of_nonneg_right h_min hΨ_nn
  have hsplit_B1k := intervalIntegral.integral_add_adjacent_intervals
    (hi_B1k (-R) (-R + ℓ) le_rfl (by linarith) (by linarith))
    (hi_B1k (-R + ℓ) u_T (by linarith) hnegRl_le_uT huT_le_R)
  have hB1k_eq : virasoroBandB1k c' R T g k =
      (∫ v in (-R)..(-R + ℓ), min 1 (((k : ℝ) + 1) * (-v) / R) * (virasoroPsiTilde c' g (v : ℂ)).re) +
        (∫ v in (-R + ℓ)..u_T, min 1 (((k : ℝ) + 1) * (-v) / R) * (virasoroPsiTilde c' g (v : ℂ)).re) := by
    unfold virasoroBandB1k; rw [← hsplit_B1k]
  linarith only [h_low_left, h_main_band, hB1k_eq]

private lemma virasoro_line_mid_and_right {c' R T ℓ : ℝ}
    (hc' : virasoroCQEnv ≤ c') (hς_half : virasoroSigma c' ≤ 1 / 2)
    (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ virasoroAC c' ^ 2)
    (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    (huT_Icc : virasoroUT c' T ∈ Icc (-virasoroAThr) (-1))
    (hΨ_cont_all : ContinuousOn (fun v : ℝ => (virasoroPsiTilde c' g (v : ℂ)).re)
      (Icc (-R) (virasoroAC c' ^ 2)))
    {k : ℕ} (hkR : (k : ℝ) ≤ R / 5) :
    -(∫ v in (virasoroUT c' T)..(1 : ℝ),
        (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * (virasoroPsiTilde c' g (v : ℂ)).re) ≤
      4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R ∧
    -(∫ v in (1 : ℝ)..(R + ℓ),
        (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * (virasoroPsiTilde c' g (v : ℂ)).re) ≤
      2 * virasoroEnvC0 * ((k : ℝ) + 1) / R := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc'
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
        (c_PJ_complex_le_virasoroCQEnv.trans hc'))
  have hR_pos : 0 < R := by linarith
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  set u_T := virasoroUT c' T
  let W : ℝ → ℝ := fun v => (1 + (v - ℓ) / R) ^ (k + 1)
  have hW_cont : Continuous W :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hnegRl_le_uT : -R + ℓ ≤ u_T := by linarith [huT_Icc.1]
  have huT_le1 : u_T ≤ 1 := by linarith [huT_Icc.2]
  have h_mem_sub : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      Icc a b ⊆ Icc (-R) (virasoroAC c' ^ 2) := fun ha0 _ hb0 => Icc_subset_Icc ha0 (by linarith)
  have hi_WΨ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 =>
      ((continuousOn_const.sub hW_cont.continuousOn).mul
        (hΨ_cont_all.mono (h_mem_sub ha0 hab hb0))).intervalIntegrable_of_Icc hab
  refine ⟨?_, ?_⟩
  · have hi1 := hi_WΨ u_T 1 (by linarith [hnegRl_le_uT]) huT_le1 (by linarith)
    have hΨ_norm_int1 : IntervalIntegrable (fun v : ℝ => ‖virasoroPsiTilde c' g (v : ℂ)‖) volume u_T 1 :=
      (continuous_norm.comp_continuousOn ((virasoroPsiTilde_analyticOnNhd hc'_1000 hg.1).continuousOn.comp
        continuous_ofReal.continuousOn fun v hv => virasoro_closedBall_subset_psiDom hc'_pos (by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [hv.1, hnegRl_le_uT], by linarith [hv.2, hR_ub]⟩))).intervalIntegrable_of_Icc huT_le1
    have h_abs : |∫ v in u_T..1, (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re| ≤
        (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) *
          ∫ v in u_T..1, ‖virasoroPsiTilde c' g (v : ℂ)‖ := by
      calc |∫ v in u_T..1, (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re|
          ≤ ∫ v in u_T..1, |(1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun v : ℝ => (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re) (μ := volume) huT_le1
        _ ≤ ∫ v in u_T..1, (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) * ‖virasoroPsiTilde c' g (v : ℂ)‖ := by
            refine intervalIntegral.integral_mono_on huT_le1 hi1.abs
              (hΨ_norm_int1.const_mul _) fun v hv => ?_
            have hvl4 : |v - ℓ| ≤ 4 := by
              have hv_lo : -3.4 ≤ v := by linarith [huT_Icc.1, hv.1, hAThr_lt]
              exact abs_le.mpr ⟨by linarith, by linarith [hv.2]⟩
            have hpow := abs_one_add_pow_sub_one_le ((v - ℓ) / R) (k + 1)
            have h_abs_sub : |1 - W v| = |(1 + (v - ℓ) / R) ^ (k + 1) - 1| := by
              dsimp [W]; rw [abs_sub_comm]
            have h_exp_65 : ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| ≤ 6 / 5 := by
              rw [abs_div, abs_of_pos hR_pos]
              have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ R / 5 + 1 := by push_cast; linarith
              calc ((k + 1 : ℕ) : ℝ) * (|v - ℓ| / R) ≤ (R / 5 + 1) * (4 / R) := by gcongr
                _ = 4 / 5 + 4 / R := by field_simp [hR_pos.ne']
                _ ≤ 4 / 5 + 4 / 10 := by gcongr
                _ = 6 / 5 := by norm_num
            have hW_bd : |1 - W v| ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by
              rw [h_abs_sub]
              calc |(1 + (v - ℓ) / R) ^ (k + 1) - 1|
                  ≤ ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| *
                      Real.exp (((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R|) := hpow
                _ ≤ ((k + 1 : ℕ) : ℝ) * (4 / R) * Real.exp (6 / 5) := by
                    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity))
                      (Real.exp_le_exp.mpr h_exp_65) (Real.exp_pos _).le (by positivity)
                    rw [abs_div, abs_of_pos hR_pos]
                    exact div_le_div_of_nonneg_right hvl4 hR_pos.le
                _ = 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by push_cast; ring
            calc |(1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re|
                = |1 - W v| * |(virasoroPsiTilde c' g (v : ℂ)).re| := abs_mul _ _
              _ ≤ (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) * ‖virasoroPsiTilde c' g (v : ℂ)‖ :=
                  mul_le_mul hW_bd (Complex.abs_re_le_norm _) (abs_nonneg _) (by positivity)
        _ = (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) *
              ∫ v in u_T..1, ‖virasoroPsiTilde c' g (v : ℂ)‖ := intervalIntegral.integral_const_mul _ _
    have hL1_le1 : ∫ v in u_T..1, ‖virasoroPsiTilde c' g (v : ℂ)‖ ≤ 1 := by
      have hΨ_norm_all : ContinuousOn (fun v : ℝ => ‖virasoroPsiTilde c' g (v : ℂ)‖)
          (Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2)) :=
        continuous_norm.comp_continuousOn ((virasoroPsiTilde_analyticOnNhd hc'_1000 hg.1).continuousOn.comp
          continuous_ofReal.continuousOn fun v hv => virasoro_closedBall_subset_psiDom hc'_pos (by
            rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hv))
      have h_sub_le : ∫ v in u_T..1, ‖virasoroPsiTilde c' g (v : ℂ)‖ ≤
          ∫ v in (-(virasoroAC c' ^ 2))..(virasoroAC c' ^ 2), ‖virasoroPsiTilde c' g (v : ℂ)‖ := by
        rw [intervalIntegral.integral_of_le huT_le1, intervalIntegral.integral_of_le (by linarith)]
        refine setIntegral_mono_set
          ((hΨ_norm_all.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self)
          (Eventually.of_forall fun _ => norm_nonneg _)
          (Eventually.of_forall (Ioc_subset_Ioc (by linarith [hnegRl_le_uT]) (by linarith)))
      exact h_sub_le.trans (lemmaQ_part3 hc' hg).2.1
    have h_c_nn : 0 ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by positivity
    have h1 := (abs_le.mp h_abs).1
    nlinarith only [h1, hL1_le1, h_c_nn]
  · have h1R : (1 : ℝ) ≤ R + ℓ := by linarith
    have hi_r := hi_WΨ 1 (R + ℓ) (by linarith) h1R le_rfl
    let C_exp : ℝ := virasoroEnvC0 * ((k : ℝ) + 1) / R
    have hC_exp_nn : 0 ≤ C_exp := by dsimp [C_exp]; have := virasoroEnvC0_pos; positivity
    have h_abs : |∫ v in (1 : ℝ)..(R + ℓ), (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re| ≤
        ∫ v in (1 : ℝ)..(R + ℓ), C_exp * Real.exp (-(8 / 15 : ℝ) * v) := by
      calc |∫ v in (1 : ℝ)..(R + ℓ), (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re|
          ≤ ∫ v in (1 : ℝ)..(R + ℓ), |(1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun v : ℝ => (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re) (μ := volume) h1R
        _ ≤ ∫ v in (1 : ℝ)..(R + ℓ), C_exp * Real.exp (-(8 / 15 : ℝ) * v) := by
            refine intervalIntegral.integral_mono_on h1R hi_r.abs
              ((continuous_const.mul (Real.continuous_exp.comp
                (continuous_const.mul continuous_id))).intervalIntegrable 1 (R + ℓ))
              fun v hv => ?_
            have hv1 : 1 ≤ v := hv.1
            have hv_pos : 0 < v := by linarith
            have hvl : |v - ℓ| ≤ v := abs_le.mpr ⟨by linarith, by linarith⟩
            have hpow := abs_one_add_pow_sub_one_le ((v - ℓ) / R) (k + 1)
            have h_abs_sub : |1 - W v| = |(1 + (v - ℓ) / R) ^ (k + 1) - 1| := by
              dsimp [W]; rw [abs_sub_comm]
            have h_exp_310 : ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| ≤ (3 / 10 : ℝ) * v := by
              rw [abs_div, abs_of_pos hR_pos]
              have hk1R : ((k + 1 : ℕ) : ℝ) / R ≤ 3 / 10 := by
                push_cast; rw [div_le_iff₀ hR_pos]; linarith
              calc ((k + 1 : ℕ) : ℝ) * (|v - ℓ| / R) = (((k + 1 : ℕ) : ℝ) / R) * |v - ℓ| := by ring
                _ ≤ (3 / 10 : ℝ) * v := mul_le_mul hk1R hvl (abs_nonneg _) (by norm_num)
            have hW_bd : |1 - W v| ≤ (((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v) := by
              rw [h_abs_sub]
              calc |(1 + (v - ℓ) / R) ^ (k + 1) - 1|
                  ≤ ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| *
                      Real.exp (((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R|) := hpow
                _ ≤ (((k + 1 : ℕ) : ℝ) * (v / R)) * Real.exp ((3 / 10 : ℝ) * v) := by
                    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity))
                      (Real.exp_le_exp.mpr h_exp_310) (Real.exp_pos _).le (by positivity)
                    rw [abs_div, abs_of_pos hR_pos]; exact div_le_div_of_nonneg_right hvl hR_pos.le
                _ = (((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v) := by push_cast; ring
            have hv_ball : (v : ℂ) ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2) := by
              rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos]
              linarith [hv.2]
            have hcut : ¬ ((v : ℂ).im = 0 ∧ (v : ℂ).re ≤ 0) := fun h0 => by
              simp only [Complex.ofReal_re] at h0; linarith
            have h_env := (lemmaQ_part2 hc' hg.1 hM_pos).2.2 (v : ℂ) hv_ball hcut
            have h_re_sqrt : ((v : ℂ) ^ (1 / 2 : ℂ)).re = √v := by
              rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hv_pos.le,
                Complex.ofReal_re, Real.sqrt_eq_rpow]
            have h_env_val : airyEnv (v : ℂ) = Real.exp (-(4 / 3 : ℝ) * (v ^ (3 / 2 : ℝ))) := by
              unfold airyEnv
              rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hv_pos.le,
                Complex.ofReal_re]
            have h_inv_eq : ‖(v : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((v : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹ = v⁻¹ := by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos, h_re_sqrt,
                Real.rpow_neg hv_pos.le, ← Real.sqrt_eq_rpow, ← mul_inv, Real.mul_self_sqrt hv_pos.le]
            have hΨ_bd : |(virasoroPsiTilde c' g (v : ℂ)).re| ≤
                virasoroEnvC0 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + virasoroSigma c' * √v) * v⁻¹ := by
              calc |(virasoroPsiTilde c' g (v : ℂ)).re| ≤ ‖virasoroPsiTilde c' g (v : ℂ)‖ :=
                    Complex.abs_re_le_norm _
                _ ≤ virasoroEnvC0 * airyEnv (v : ℂ) * Real.exp (virasoroSigma c' * ((v : ℂ) ^ (1 / 2 : ℂ)).re) *
                      ‖(v : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((v : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹ := h_env
                _ = virasoroEnvC0 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + virasoroSigma c' * √v) * v⁻¹ := by
                    rw [mul_assoc (virasoroEnvC0 * airyEnv (v : ℂ) * _), h_inv_eq, h_re_sqrt, h_env_val,
                      mul_assoc virasoroEnvC0, ← Real.exp_add]
            have hv32 : v ≤ v ^ (3 / 2 : ℝ) := by
              conv_lhs => rw [← Real.rpow_one v]
              exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
            have hsqrt_le : √v ≤ v := by
              rw [Real.sqrt_eq_rpow]
              conv_rhs => rw [← Real.rpow_one v]
              exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
            have hexp_sum : -(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + virasoroSigma c' * √v + (3 / 10 : ℝ) * v ≤
                -(8 / 15 : ℝ) * v := by
              have hsqrt_nn : 0 ≤ √v := Real.sqrt_nonneg v
              nlinarith only [hv32, hsqrt_le, hς_half, hv1, hsqrt_nn]
            have hexp_prod : Real.exp ((3 / 10 : ℝ) * v) *
                  Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + virasoroSigma c' * √v) =
                Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + virasoroSigma c' * √v + (3 / 10 : ℝ) * v) := by
              rw [← Real.exp_add]; ring_nf
            calc |(1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re|
                = |1 - W v| * |(virasoroPsiTilde c' g (v : ℂ)).re| := abs_mul _ _
              _ ≤ ((((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v)) *
                    (virasoroEnvC0 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + virasoroSigma c' * √v) * v⁻¹) :=
                  mul_le_mul hW_bd hΨ_bd (abs_nonneg _) (by positivity)
              _ = C_exp * (Real.exp ((3 / 10 : ℝ) * v) *
                    Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + virasoroSigma c' * √v)) * (v * v⁻¹) := by
                  dsimp [C_exp]; ring
              _ = C_exp * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + virasoroSigma c' * √v + (3 / 10 : ℝ) * v) := by
                  rw [hexp_prod, mul_inv_cancel₀ hv_pos.ne', mul_one]
              _ ≤ C_exp * Real.exp (-(8 / 15 : ℝ) * v) :=
                  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_sum) hC_exp_nn
    have h_ftc_r : ∫ v in (1 : ℝ)..(R + ℓ), C_exp * Real.exp (-(8 / 15 : ℝ) * v) ≤ 2 * C_exp := by
      have hderiv : ∀ v ∈ Set.uIcc 1 (R + ℓ),
          HasDerivAt (fun t : ℝ => -((15 / 8 : ℝ) * C_exp) * Real.exp (-(8 / 15 : ℝ) * t))
            (C_exp * Real.exp (-(8 / 15 : ℝ) * v)) v := fun v _ => by
        have h1 : HasDerivAt (fun t : ℝ => -(8 / 15 : ℝ) * t) (-(8 / 15 : ℝ)) v := by
          simpa using (hasDerivAt_id v).const_mul (-(8 / 15 : ℝ))
        refine (h1.exp.const_mul (-((15 / 8 : ℝ) * C_exp))).congr_deriv ?_
        ring
      have h_eq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable 1 (R + ℓ))
      have hR_nn : 0 ≤ ((15 / 8 : ℝ) * C_exp) * Real.exp (-(8 / 15 : ℝ) * (R + ℓ)) := by positivity
      have h1_le : Real.exp (-(8 / 15 : ℝ) * 1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      nlinarith only [h_eq, hR_nn, h1_le, hC_exp_nn]
    have h1 := (abs_le.mp h_abs).1
    have h2 : 2 * C_exp = 2 * virasoroEnvC0 * ((k : ℝ) + 1) / R := by dsimp [C_exp]; ring
    linarith only [h1, h_ftc_r, h2]

/-- **Line Estimate (`TE.5` / `BootstrapCore.hI_line`)**:
For `c' ≥ virasoroCQEnv` with `virasoroSigma c' ≤ 1/2`, `R ≥ 10` (`R + 1 ≤ virasoroAC c'^2`),
`T ∈ [Δ(-1), Δ(-A_thr)]` (`u_T ∈ [-A_thr, -1]`), `ℓ ∈ [0, 1/2]`, and `5 ≤ k ≤ R/5`,
`∫_{-R}^R (f_{k, ℓ} x).re ≤ -(63/100) B_1^{(k)} - B_2 + (4 exp(6/5) + 3 C₀)(k+1)/R + Δ_lobe`. -/
theorem virasoro_line_bound {c' R T ℓ : ℝ}
    (hc' : virasoroCQEnv ≤ c') (hς_nn : 0 ≤ virasoroSigma c') (hς_half : virasoroSigma c' ≤ 1 / 2)
    (hR_10 : 10 ≤ R) (hR_ub : R + 1 ≤ virasoroAC c' ^ 2)
    (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' (-1) ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr))
    {k : ℕ} (hk5 : 5 ≤ k) (hkR : (k : ℝ) ≤ R / 5) :
    ∫ x in (-R)..R, (virasoroShiftedFun c' R ℓ g k (x : ℂ)).re ≤
      -(63 / 100 : ℝ) * virasoroBandB1k c' R T g k - virasoroBandB2 c' R g +
        (4 * Real.exp (6 / 5) + 3 * virasoroEnvC0) * ((k : ℝ) + 1) / R +
        virasoroDeltaLobe c' g := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc'
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
        (c_PJ_complex_le_virasoroCQEnv.trans hc'))
  have ha : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; have := virasoroCQEnv_ge; linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero ha hg.1 hg.2.1
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  have hu_mem := virasoroUT_between hc'_pos
    (by linarith : -(virasoroAC c' ^ 2) ≤ -virasoroAThr)
    (by linarith [sq_nonneg (virasoroAC c')]) (by linarith [virasoroAThr_gt_two] : -virasoroAThr ≤ -1)
    hT_lo hT_hi
  set u_T := virasoroUT c' T
  have huT_Icc : u_T ∈ Icc (-virasoroAThr) (-1) := hu_mem.1
  have hΔ_uT : virasoroDeltaChart c' u_T = T := hu_mem.2
  have h_shift_eq : ∫ x in (-R)..R, (virasoroShiftedFun c' R ℓ g k (x : ℂ)).re =
      ∫ v in (-R + ℓ)..(R + ℓ),
        (1 + (v - ℓ) / R) ^ (k + 1) * (virasoroPsiTilde c' g (v : ℂ)).re := by
    have hrew : (fun x : ℝ => (virasoroShiftedFun c' R ℓ g k (x : ℂ)).re) =
        fun x : ℝ => (1 + x / R) ^ (k + 1) * (virasoroPsiTilde c' g (((x + ℓ : ℝ) : ℂ))).re := by
      ext x; unfold virasoroShiftedFun
      have hreal_pow : ((1 + (x : ℂ) / (R : ℂ)) ^ (k + 1)) =
          (((1 + x / R) ^ (k + 1) : ℝ) : ℂ) := by push_cast; ring
      rw [hreal_pow, show (x : ℂ) + (ℓ : ℂ) = ((x + ℓ : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; ring
    rw [hrew]
    simpa [add_sub_cancel_right] using
      intervalIntegral.integral_comp_add_right
        (fun v : ℝ => (1 + (v - ℓ) / R) ^ (k + 1) * (virasoroPsiTilde c' g (v : ℂ)).re) ℓ
        (a := -R) (b := R)
  rw [h_shift_eq]
  have hΨ_cont_all : ContinuousOn (fun v : ℝ => (virasoroPsiTilde c' g (v : ℂ)).re)
      (Icc (-R) (virasoroAC c' ^ 2)) := by
    refine Complex.continuous_re.comp_continuousOn
      ((virasoroPsiTilde_analyticOnNhd hc'_1000 hg.1).continuousOn.comp
        continuous_ofReal.continuousOn fun v hv => virasoro_closedBall_subset_psiDom hc'_pos (by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [hv.1], hv.2⟩))
  have h_mem_sub : ∀ {a b : ℝ}, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      Icc a b ⊆ Icc (-R) (virasoroAC c' ^ 2) := fun ha0 _ hb0 => Icc_subset_Icc ha0 (by linarith)
  let W : ℝ → ℝ := fun v => (1 + (v - ℓ) / R) ^ (k + 1)
  have hW_cont : Continuous W :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hi_Ψ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ virasoroAC c' ^ 2 →
      IntervalIntegrable (fun v : ℝ => (virasoroPsiTilde c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 => (hΨ_cont_all.mono (Icc_subset_Icc ha0 hb0)).intervalIntegrable_of_Icc hab
  have hi_WΨ : ∀ (a b : ℝ), -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v : ℝ => (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re) volume a b :=
    fun a b ha0 hab hb0 =>
      ((continuousOn_const.sub hW_cont.continuousOn).mul
        (hΨ_cont_all.mono (h_mem_sub ha0 hab hb0))).intervalIntegrable_of_Icc hab
  have h_split_W : ∫ v in (-R + ℓ)..(R + ℓ), W v * (virasoroPsiTilde c' g (v : ℂ)).re =
      (∫ v in (-R + ℓ)..(R + ℓ), (virasoroPsiTilde c' g (v : ℂ)).re) -
        ∫ v in (-R + ℓ)..(R + ℓ), (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re := by
    rw [← intervalIntegral.integral_sub
      (hi_Ψ (-R + ℓ) (R + ℓ) (by linarith) (by linarith) (by linarith))
      (hi_WΨ (-R + ℓ) (R + ℓ) (by linarith) (by linarith) le_rfl)]
    refine intervalIntegral.integral_congr fun v _ => by ring
  have hnegRl_le_uT : -R + ℓ ≤ u_T := by linarith [huT_Icc.1]
  have huT_le_R : u_T ≤ R + ℓ := by linarith [huT_Icc.2]
  have h_split_W1 : ∫ v in (-R + ℓ)..(R + ℓ), (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re =
      (∫ v in (-R + ℓ)..u_T, (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re) +
        (∫ v in u_T..1, (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re) +
        (∫ v in (1 : ℝ)..(R + ℓ), (1 - W v) * (virasoroPsiTilde c' g (v : ℂ)).re) := by
    have h12 := intervalIntegral.integral_add_adjacent_intervals
      (hi_WΨ (-R + ℓ) u_T (by linarith) hnegRl_le_uT huT_le_R)
      (hi_WΨ u_T 1 (by linarith [hnegRl_le_uT]) (by linarith [huT_Icc.2]) (by linarith))
    have h23 := intervalIntegral.integral_add_adjacent_intervals
      (hi_WΨ (-R + ℓ) 1 (by linarith) (by linarith) (by linarith))
      (hi_WΨ 1 (R + ℓ) (by linarith) (by linarith) le_rfl)
    linarith only [h12, h23]
  have h_top := virasoro_line_top_bound hc' hς_nn hς_half hR_10 hR_ub hℓ_nn hℓ_half hg hM_pos hT_hi
    huT_Icc.1 hΔ_uT huT_Icc.2 hΨ_cont_all hk5
  have h_band := virasoro_line_band_piece hc' hR_10 hR_ub hℓ_nn hℓ_half hg huT_Icc hΔ_uT hΨ_cont_all k
  obtain ⟨h_mid, h_right⟩ := virasoro_line_mid_and_right hc' hς_half hR_10 hR_ub hℓ_nn hℓ_half hg
    hM_pos huT_Icc hΨ_cont_all hkR
  have h_sum_coeff :
      virasoroEnvC0 * ((k : ℝ) + 1) / R + 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R +
        2 * virasoroEnvC0 * ((k : ℝ) + 1) / R =
      (4 * Real.exp (6 / 5) + 3 * virasoroEnvC0) * ((k : ℝ) + 1) / R := by ring
  linarith only [h_split_W, h_split_W1, h_top, h_band, h_mid, h_right, h_sum_coeff]

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.yvInputAt_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yvInputAt_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.virasoro_line_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_line_bound


end FormalResearch.ModularBootstrap.ConcreteBootstrap
