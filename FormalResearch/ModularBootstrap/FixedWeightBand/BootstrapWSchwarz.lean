module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWData

/-!
# Band Moments and Schwarz Reflection of `psiTilde` at Every Fixed `(w, Q)`

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma `Q` (`wone:Q`), Proposition `Y_V`
(`vlo:YV`) and the band moments `B₁`, `B₂` of `teb:bootstrap`.

* `LemmaQData.UT_between`: chart inversion `u_T ∈ [a, b]`, `Δ(u_T) = T` on the shrunk disc.
* `bandB1W_nonneg`, `bandB2W_nonneg`: positivity of the band moments `B₁`, `B₂` of a weakly feasible test.
* `yvInputAtW_nonvacuous`: non-vacuity of the band-feedback hypothesis `YVInputAtForW`.
* `LemmaQData.psiTilde_conj`: general Schwarz reflection `Ψ̃(ū) = conj Ψ̃(u)` on `closedBall 0 (A_{c'}²)`
  (the Virasoro `virasoroPsiTilde_conj`; the identity theorem on the real segment uses `(H2+)`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing PoissonJensen TipFront ConcreteBootstrap FixedWeightTip FormalResearch.Special

variable {prob : FixedWeightProblem}

namespace LemmaQData

variable (Q : LemmaQData prob)

/-- Chart inversion helper on `[-A_{c'}^2, A_{c'}^2]`. -/
lemma UT_between {c' a b T : ℝ} (hc' : 0 < c')
    (ha_bd : -(Q.AC c' ^ 2) ≤ a) (hb_bd : b ≤ Q.AC c' ^ 2) (hab : a ≤ b)
    (hT_lo : virasoroDeltaChart c' b ≤ T) (hT_hi : T ≤ virasoroDeltaChart c' a) :
    virasoroUT c' T ∈ Icc a b ∧ virasoroDeltaChart c' (virasoroUT c' T) = T := by
  have hle := Q.AC_sq_le_virasoro hc'.le
  exact virasoroUT_between hc' (by linarith) (by linarith) hab hT_lo hT_hi

end LemmaQData

section Band

variable [Q : LemmaQData prob]

lemma bandB1W_nonneg {c' R T : ℝ} (hc' : Q.cQ ≤ c')
    (hR_thr : virasoroAThr ≤ R) (hR_ub : R ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr)) :
    0 ≤ bandB1W prob c' R T g := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have ha : prob.totalShift ≤ c' / 12 := by
    have := Q.hcQ_shift; have := Q.hcQ_10000; linarith
  have hR_pos : 0 < R := lt_of_lt_of_le virasoroAThr_pos hR_thr
  have hM_nn : 0 ≤ (prob.cardyNorm (c' / 12) g)⁻¹ :=
    inv_nonneg.mpr (Q.cardyNorm_pos hc' hg).le
  have hRm : -R ∈ Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2) :=
    ⟨by linarith, by linarith [virasoroAThr_pos, sq_nonneg (Q.AC c')]⟩
  have hAThr_m : -virasoroAThr ∈ Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2) :=
    ⟨by linarith, by linarith [virasoroAThr_pos, sq_nonneg (Q.AC c')]⟩
  have hΔ_T_le : T ≤ virasoroDeltaChart c' (-R) :=
    hT_hi.trans ((Q.deltaChart_strictAnti hc'_pos).antitoneOn hRm hAThr_m (by linarith))
  refine mul_nonneg (mul_nonneg (inv_nonneg.mpr hR_pos.le) hM_nn) ?_
  refine intervalIntegral.integral_nonneg hΔ_T_le fun t ht => ?_
  have hΔ_0_le : virasoroDeltaChart c' 0 ≤ t := hT_lo.trans ht.1
  have hu_t := Q.UT_between hc'_pos (by linarith : -(Q.AC c' ^ 2) ≤ -R)
    (sq_nonneg _) (by linarith : -R ≤ 0) hΔ_0_le ht.2
  have ht_pos : 0 ≤ t :=
    (Q.deltaChart_pos hc'_pos (by rw [abs_zero]; exact sq_nonneg _)).le.trans hΔ_0_le
  exact mul_nonneg (by linarith [hu_t.1.2])
    (mul_nonneg (hg.2.2.2 t ht.1) (prob.cardyV_nonneg ha ht_pos))

lemma bandB2W_nonneg {c' R T : ℝ} (hc' : Q.cQ ≤ c')
    (hR_thr : virasoroAThr ≤ R) (hR_ub : R ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_hi : T ≤ virasoroDeltaChart c' (-virasoroAThr)) :
    0 ≤ bandB2W prob c' R g := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have ha : prob.totalShift ≤ c' / 12 := by
    have := Q.hcQ_shift; have := Q.hcQ_10000; linarith
  have hM_nn : 0 ≤ (prob.cardyNorm (c' / 12) g)⁻¹ :=
    inv_nonneg.mpr (Q.cardyNorm_pos hc' hg).le
  have hRm : -R ∈ Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2) :=
    ⟨by linarith, by linarith [virasoroAThr_pos, sq_nonneg (Q.AC c')]⟩
  have hAThr_m : -virasoroAThr ∈ Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2) :=
    ⟨by linarith, by linarith [virasoroAThr_pos, sq_nonneg (Q.AC c')]⟩
  have hΔ_T_le : T ≤ virasoroDeltaChart c' (-R) :=
    hT_hi.trans ((Q.deltaChart_strictAnti hc'_pos).antitoneOn hRm hAThr_m (by linarith))
  have hΔ_nn : 0 ≤ virasoroDeltaChart c' (-R) :=
    (Q.deltaChart_pos hc'_pos (abs_le.mpr hRm)).le
  refine mul_nonneg hM_nn (setIntegral_nonneg measurableSet_Ici fun t ht => ?_)
  exact mul_nonneg (hg.2.2.2 t (hΔ_T_le.trans ht)) (prob.cardyV_nonneg ha (hΔ_nn.trans ht))

/-- Non-vacuity of `YVInputAtForW`: the feedback specification and the envelope domain are consistent
(witness `Ψ = 0`), at every scale `0 < b ≤ b_V`. -/
theorem yvInputAtW_nonvacuous {b : ℝ} (hb : 0 < b) (hb_le : b ≤ Q.bV) :
    ∃ (Ψ : ℝ → (ℝ → ℝ) → ℂ → ℂ) (C_fb c_YV : ℝ),
      1 ≤ C_fb ∧ Q.cQ ≤ c_YV ∧ YVInputAtForW prob b Ψ C_fb c_YV := by
  refine ⟨fun _ _ _ => 0, 1, Q.cQ, le_rfl, le_rfl, ?_⟩
  intro c' T R hc' hR_thr _ hR_ub g hg hT_lo hT_hi u _ hRl _ hsin
  have hR_pos : 2 ≤ R := by linarith [virasoroAThr_gt_two]
  have hu_pos : 0 < ‖u‖ := by linarith
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hle := Q.ACAt_sq_le hb.le hb_le hc'_pos.le
  have hre_pos : 0 < (u ^ (1 / 2 : ℂ)).re := by
    have : 0 < 2 * c' ^ (-(1 / 12 : ℝ)) * √‖u‖ := by positivity
    linarith
  have hB1 := bandB1W_nonneg hc' hR_thr (by linarith) hg hT_lo hT_hi
  have hB2 := bandB2W_nonneg hc' hR_thr (by linarith) hg hT_hi
  have henv : 0 < airyEnv u := airyEnv_pos u
  have hL'_nn : 0 ≤ 1 * (c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) + 1) := by
    positivity
  rw [norm_zero]
  exact mul_nonneg (mul_nonneg (mul_nonneg hL'_nn henv.le) (Real.rpow_nonneg hre_pos.le _))
    (Real.rpow_nonneg (norm_nonneg _) _)

/-! ### Section 2: Schwarz Reflection & Shifted-Square-Root Envelope Lemmas -/


end Band

namespace LemmaQData

variable (Q : LemmaQData prob)

/-- Schwarz reflection for `psiTilde prob c' g` on `closedBall 0 (Q.AC c'^2)`. -/
lemma psiTilde_conj {c' : ℝ} (hc' : Q.cQ ≤ c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2)) :
    psiTilde prob c' g (star u) = star (psiTilde prob c' g u) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hc'_1000 : 1000 ≤ c' :=
    (by norm_num : (1000 : ℝ) ≤ 10000).trans
      ((Q.hcQ_10000.trans hc'))
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := (isCompact_closedBall (0 : ℂ) (Q.AC c' ^ 2)).exists_thickening_subset_open
    (psiDom_isOpen hc'_pos) (Q.closedBall_subset_psiDom hc'_pos)
  let r_ball : ℝ := Q.AC c' ^ 2 + δ
  have hr_sub : ball (0 : ℂ) r_ball ⊆ psiDom c' := fun z hz => by
    apply hδ_sub
    rw [Metric.mem_thickening_iff]
    by_cases hz0 : ‖z‖ ≤ Q.AC c' ^ 2
    · exact ⟨z, mem_closedBall_zero_iff.mpr hz0, by simpa⟩
    · push Not at hz0
      have hA2_nn : 0 ≤ Q.AC c' ^ 2 := sq_nonneg _
      have hz_pos : 0 < ‖z‖ := hA2_nn.trans_lt hz0
      let w : ℂ := (((Q.AC c' ^ 2 / ‖z‖ : ℝ)) : ℂ) * z
      have hw_mem : w ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2) := by
        rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hA2_nn hz_pos.le)]
        rw [div_mul_cancel₀ _ hz_pos.ne']
      have hw_dist : dist z w < δ := by
        rw [dist_eq_norm]
        have hdiff : z - w = ((1 - Q.AC c' ^ 2 / ‖z‖ : ℝ) : ℂ) * z := by
          dsimp [w]; push_cast; ring
        rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg]
        · rw [sub_mul, one_mul, div_mul_cancel₀ _ hz_pos.ne']
          rw [mem_ball_zero_iff] at hz; linarith
        · rw [sub_nonneg, div_le_one hz_pos]; exact hz0.le
      exact ⟨w, hw_mem, hw_dist⟩
  have hF1_an : AnalyticOnNhd ℂ (psiTilde prob c' g) (ball (0 : ℂ) r_ball) :=
    (Q.analytic hc' hg).mono hr_sub
  let F2 : ℂ → ℂ := fun z => star (psiTilde prob c' g (star z))
  have hF2_diff : DifferentiableOn ℂ F2 (ball (0 : ℂ) r_ball) := by
    intro z hz
    have hsz : star z ∈ ball (0 : ℂ) r_ball := by simpa [mem_ball_zero_iff] using hz
    have hda := (hF1_an (star z) hsz).differentiableAt.hasDerivAt
    have hd_conj : HasDerivAt F2 (star (deriv (psiTilde prob c' g) (star z))) z := by
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
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F2 z = psiTilde prob c' g z := by
    rw [frequently_nhdsWithin_iff, nhds_basis_ball.frequently_iff]
    intro ε hε
    have hA2_pos : 0 < Q.AC c' ^ 2 := by
      rw [Q.AC_sq _ hc'_pos.le]; have := Q.bV_pos; positivity
    let x : ℝ := min (ε / 2) (Q.AC c' ^ 2 / 2)
    have hx_pos : 0 < x := lt_min (half_pos hε) (by linarith)
    have hx_mem : |x| ≤ Q.AC c' ^ 2 := by
      rw [abs_of_pos hx_pos]
      exact (min_le_right _ _).trans (by linarith)
    have him : (psiTilde prob c' g (x : ℂ)).im = 0 :=
      (Q.part2 hc' hg hM_pos).2.1 x hx_mem |>.1
    refine ⟨(x : ℂ), ?_, ?_, Complex.ofReal_ne_zero.mpr hx_pos.ne'⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]
      exact (min_le_left _ _).trans_lt (half_lt_self hε)
    · simp only [F2, Complex.star_def, Complex.conj_ofReal, Complex.conj_eq_iff_im.mpr him]
  have h0_mem : (0 : ℂ) ∈ ball (0 : ℂ) r_ball := mem_ball_self (by positivity [sq_nonneg (Q.AC c')])
  have hu_ball : u ∈ ball (0 : ℂ) r_ball :=
    closedBall_subset_ball (by linarith : Q.AC c' ^ 2 < r_ball) hu
  have heq := hF2_an.eqOn_of_preconnected_of_frequently_eq hF1_an
    (convex_ball (0 : ℂ) r_ball).isPreconnected h0_mem hfreq hu_ball
  calc psiTilde prob c' g (star u) = star (F2 u) := by simp [F2]
    _ = star (psiTilde prob c' g u) := by rw [heq]

end LemmaQData

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQData.UT_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LemmaQData.UT_between

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.bandB1W_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bandB1W_nonneg

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.bandB2W_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bandB2W_nonneg

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.yvInputAtW_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yvInputAtW_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQData.psiTilde_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LemmaQData.psiTilde_conj

end FormalResearch.ModularBootstrap.FixedWeightBand
