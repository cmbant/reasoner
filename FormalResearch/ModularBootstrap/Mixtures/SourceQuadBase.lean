module

public import FormalResearch.ModularBootstrap.Mixtures.SourceLemmaZ

/-!
# Quadrature Base Lemmas for Signed Common Sources

Adapts Schwarz reflection, the first-moment identity, positive real tail decay, and the shifted
quadrature test `f_{k,ℓ}` / `B_1^{(k)}` from `ConcreteBootstrap.QuadratureBounds` /
`FixedWeightBand.BootstrapWSchwarz` to `C : CommonSource` (`C.src`) with `Q : LemmaQSrcData C`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.Special FormalResearch.TwoEdgeBootstrap
open Crossing PoissonJensen TipFront ConcreteBootstrap FixedWeightTip FixedWeightBand WeightAxioms
open FormalResearch.ModularBootstrap.Chart

/-! ### Section 1: Schwarz Reflection, Moment Identity, and Real Tail Decay -/

namespace LemmaQSrcData

variable {C : CommonSource} (Q : LemmaQSrcData C)

/-- Schwarz reflection for `psiTildeSrc C.src c' g` on `closedBall 0 (Q.AC c' ^ 2)`. -/
lemma psiTildeSrc_conj {c' : ℝ} (hc' : Q.cQ ≤ c') {g : ℝ → ℝ}
    (hg : TestClass C.src (c' / 12) g)
    (hM_pos : 0 < C.src.cardyNorm (c' / 12) g)
    {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2)) :
    psiTildeSrc C.src c' g (star u) = star (psiTildeSrc C.src c' g u) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
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
      let w : ℂ := ((Q.AC c' ^ 2 / ‖z‖ : ℝ) : ℂ) * z
      have hw_mem : w ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2) := by
        rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (div_nonneg hA2_nn hz_pos.le), div_mul_cancel₀ _ hz_pos.ne']
      have hw_dist : dist z w < δ := by
        rw [dist_eq_norm]
        have hdiff : z - w = ((1 - Q.AC c' ^ 2 / ‖z‖ : ℝ) : ℂ) * z := by
          dsimp [w]; push_cast; ring
        rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg]
        · rw [sub_mul, one_mul, div_mul_cancel₀ _ hz_pos.ne']
          rw [mem_ball_zero_iff] at hz; linarith
        · rw [sub_nonneg, div_le_one hz_pos]; exact hz0.le
      exact ⟨w, hw_mem, hw_dist⟩
  have hF1_an : AnalyticOnNhd ℂ (psiTildeSrc C.src c' g) (ball (0 : ℂ) r_ball) :=
    (Q.analytic hc' hg).mono hr_sub
  let F2 : ℂ → ℂ := fun z => star (psiTildeSrc C.src c' g (star z))
  have hF2_diff : DifferentiableOn ℂ F2 (ball (0 : ℂ) r_ball) := by
    intro z hz
    have hsz : star z ∈ ball (0 : ℂ) r_ball := by simpa [mem_ball_zero_iff] using hz
    have hda := (hF1_an (star z) hsz).differentiableAt.hasDerivAt
    have hd_conj : HasDerivAt F2 (star (deriv (psiTildeSrc C.src c' g) (star z))) z := by
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
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F2 z = psiTildeSrc C.src c' g z := by
    rw [frequently_nhdsWithin_iff, nhds_basis_ball.frequently_iff]
    intro ε hε
    have hA2_pos : 0 < Q.AC c' ^ 2 := by
      rw [Q.AC_sq _ hc'_pos.le]; have := Q.bV_pos; positivity
    let x : ℝ := min (ε / 2) (Q.AC c' ^ 2 / 2)
    have hx_pos : 0 < x := lt_min (half_pos hε) (by linarith)
    have hx_mem : |x| ≤ Q.AC c' ^ 2 := by
      rw [abs_of_pos hx_pos]
      exact (min_le_right _ _).trans (by linarith)
    have him : (psiTildeSrc C.src c' g (x : ℂ)).im = 0 :=
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
  calc psiTildeSrc C.src c' g (star u) = star (F2 u) := by simp [F2]
    _ = star (psiTildeSrc C.src c' g u) := by rw [heq]

/-- Moment identity in `u`-coordinates on `[a, b] ⊆ [-Q.AC c'^2, Q.AC c'^2]`. -/
lemma psiTildeSrc_moment_integral_eq {c' a b : ℝ} (hc' : Q.cQ ≤ c') {g : ℝ → ℝ}
    (hg : TestClass C.src (c' / 12) g)
    (ha_bd : -(Q.AC c' ^ 2) ≤ a) (hb_bd : b ≤ Q.AC c' ^ 2) (hab : a ≤ b) :
    ∫ u in a..b, (-u) * (psiTildeSrc C.src c' g (u : ℂ)).re =
      (C.src.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c' b)..(virasoroDeltaChart c' a),
          (-virasoroUT c' t) * (g t * C.src.cardyV (c' / 12) t) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    Q.abs_le_virasoro hc'_pos.le (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have h1 : ∫ u in a..b, (-u) * (psiTildeSrc C.src c' g (u : ℂ)).re =
      -((C.src.cardyNorm (c' / 12) g)⁻¹ *
        ∫ u in a..b, ((-u) * (g (virasoroDeltaChart c' u) *
          C.src.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
          deriv (virasoroDeltaChart c') u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    rw [psiTildeSrc_re_ofReal C.src hc'_pos hg (hu_mem u hu)]
    ring
  have hsub : ∫ u in a..b, ((-u) * (g (virasoroDeltaChart c' u) *
        C.src.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
        deriv (virasoroDeltaChart c') u =
      ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
        (-virasoroUT c' t) * (g t * C.src.cardyV (c' / 12) t) := by
    have hcont_t : ContinuousOn
        (fun t : ℝ => (-virasoroUT c' t) * (g t * C.src.cardyV (c' / 12) t))
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
      refine h_ut_cont.mul ((hg.cont.mul (C.src.continuous_cardyV (c' / 12)).continuousOn).mono ?_)
      rintro t ⟨u, hu, rfl⟩
      rw [Set.uIcc_of_le hab] at hu
      exact (virasoroDeltaChart_pos hc'_pos (hu_mem u hu)).le
    have hderiv_at : ∀ u ∈ Set.uIcc a b,
        HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
      rw [Set.uIcc_of_le hab] at hu
      have hd := virasoroDeltaChart_hasDerivAt hc'_pos (hu_mem u hu)
      exact hd.deriv ▸ hd
    have hcont_der := continuousOn_deriv_virasoroDeltaChart_src hc'_pos
      (by linarith [Q.AC_sq_le_virasoro hc'_pos.le]) (hb_bd.trans (Q.AC_sq_le_virasoro hc'_pos.le)) hab
    have hcov := intervalIntegral.integral_comp_mul_deriv' hderiv_at hcont_der hcont_t
    calc ∫ u in a..b, ((-u) * (g (virasoroDeltaChart c' u) *
            C.src.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
            deriv (virasoroDeltaChart c') u
        = ∫ u in a..b, ((-virasoroUT c' (virasoroDeltaChart c' u)) *
            (g (virasoroDeltaChart c' u) *
              C.src.cardyV (c' / 12) (virasoroDeltaChart c' u))) *
            deriv (virasoroDeltaChart c') u := by
          refine intervalIntegral.integral_congr fun u hu => ?_
          rw [Set.uIcc_of_le hab] at hu
          have huc : virasoroUT c' (virasoroDeltaChart c' u) = u := by
            unfold virasoroUT
            exact virasoroUChart_deltaChart hc'_pos (hu_mem u hu)
          rw [huc]
      _ = ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
            (-virasoroUT c' t) * (g t * C.src.cardyV (c' / 12) t) := hcov
  rw [h1, hsub, intervalIntegral.integral_symm (virasoroDeltaChart c' b) (virasoroDeltaChart c' a)]
  ring

/-- Tail `L^1` decay on `[A, B] ⊆ [1, Q.AC c'^2]` for `psiTildeSrc`. -/
lemma pos_real_norm_tail_le_src {c' A B : ℝ}
    (hc' : Q.cQ ≤ c') (hς_nn : 0 ≤ Q.sigma c') (hς_half : Q.sigma c' ≤ 1 / 2)
    (hA1 : 1 ≤ A) (hAB : A ≤ B) (hB : B ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : TestClass C.src (c' / 12) g)
    (hM_pos : 0 < C.src.cardyNorm (c' / 12) g) :
    ∫ x in A..B, ‖psiTildeSrc C.src c' g (x : ℂ)‖ ≤
      (6 / 5 : ℝ) * Q.C0 * Real.exp (-(5 / 6 : ℝ) * A) := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hΨ_cont : ContinuousOn (fun x : ℝ => psiTildeSrc C.src c' g (x : ℂ)) (Icc A B) := by
    refine (Q.analytic hc' hg).continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
    exact Q.closedBall_subset_psiDom hc'_pos
      (by rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith [hx.1])]; exact hx.2.trans hB)
  have hi_l : IntervalIntegrable (fun x : ℝ => ‖psiTildeSrc C.src c' g (x : ℂ)‖) volume A B :=
    (continuous_norm.comp_continuousOn hΨ_cont).intervalIntegrable_of_Icc hAB
  have hi_r : IntervalIntegrable (fun x : ℝ => Q.C0 * Real.exp (-(5 / 6 : ℝ) * x)) volume A B :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable A B
  have h_pt : ∀ x ∈ Icc A B,
      ‖psiTildeSrc C.src c' g (x : ℂ)‖ ≤ Q.C0 * Real.exp (-(5 / 6 : ℝ) * x) := by
    intro x hx
    have hx1 : 1 ≤ x := hA1.trans hx.1
    have hx_pos : 0 < x := by linarith
    have hx_ball : (x : ℂ) ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]
      exact hx.2.trans hB
    have hcut : ¬ ((x : ℂ).im = 0 ∧ (x : ℂ).re ≤ 0) := fun h0 => by
      simp only [Complex.ofReal_re] at h0; linarith
    have h_env := (Q.part2 hc' hg hM_pos).2.2 (x : ℂ) hx_ball hcut
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
    have h_exp : -(4 / 3 : ℝ) * (x ^ (3 / 2 : ℝ)) + Q.sigma c' * √x ≤ -(5 / 6 : ℝ) * x := by
      nlinarith
    have h_inv_le1 : ‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos, h_re_sqrt,
        Real.rpow_neg hx_pos.le, ← Real.sqrt_eq_rpow, ← mul_inv, Real.mul_self_sqrt hx_pos.le]
      exact inv_le_one_of_one_le₀ hx1
    calc ‖psiTildeSrc C.src c' g (x : ℂ)‖
        ≤ Q.C0 * Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
            Real.exp (Q.sigma c' * √x) * (‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹) := by
          simpa only [h_re_sqrt, h_env_val, mul_assoc] using h_env
      _ ≤ Q.C0 * (Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
            Real.exp (Q.sigma c' * √x)) * 1 := by
          have hnn : 0 ≤ Q.C0 * Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) *
              Real.exp (Q.sigma c' * √x) := by
            have := Q.hC0; positivity
          exact (mul_le_mul_of_nonneg_left h_inv_le1 hnn).trans_eq (by ring)
      _ = Q.C0 * Real.exp (-(4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) + Q.sigma c' * √x) := by
          rw [mul_one, ← Real.exp_add]
      _ ≤ Q.C0 * Real.exp (-(5 / 6 : ℝ) * x) := by
          gcongr; exact Q.hC0.le
  have hmono := intervalIntegral.integral_mono_on hAB hi_l hi_r h_pt
  have hderiv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => -((6 / 5 : ℝ) * Q.C0) * Real.exp (-(5 / 6 : ℝ) * t))
        (Q.C0 * Real.exp (-(5 / 6 : ℝ) * x)) x := fun x _ => by
    have h1 : HasDerivAt (fun t : ℝ => -(5 / 6 : ℝ) * t) (-(5 / 6 : ℝ)) x := by
      simpa using (hasDerivAt_id x).const_mul (-(5 / 6 : ℝ))
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(5 / 6 : ℝ) * t))
        (Real.exp (-(5 / 6 : ℝ) * x) * (-(5 / 6 : ℝ))) x :=
      (Real.hasDerivAt_exp _).comp x h1
    exact (h2.const_mul (-((6 / 5 : ℝ) * Q.C0))).congr_deriv (by ring)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi_r
  have hexpB_nn : 0 ≤ (6 / 5 : ℝ) * Q.C0 * Real.exp (-(5 / 6 : ℝ) * B) := by
    have := Q.hC0; positivity
  linarith

end LemmaQSrcData

/-! ### Section 2: Shifted Quadrature Test and Truncated Band Moment -/

/-- Shifted quadrature test `f_{k, ℓ}(u) := psiTildeSrc src c' g (u + ℓ) * (1 + u / R)^{k + 1}`. -/
noncomputable def shiftedFunSrc (src : ShiftSource) (c' R ℓ : ℝ) (g : ℝ → ℝ) (k : ℕ) (u : ℂ) : ℂ :=
  psiTildeSrc src c' g (u + (ℓ : ℂ)) * (1 + u / (R : ℂ)) ^ (k + 1)

/-- Truncated first band moment `B_1^{(k)}`. -/
noncomputable def bandB1kSrc (src : ShiftSource) (c' R T : ℝ) (g : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ u in (-R)..(virasoroUT c' T),
    min 1 (((k : ℝ) + 1) * (-u) / R) * (psiTildeSrc src c' g (u : ℂ)).re

lemma bandB1kSrc_nonneg {C : CommonSource} (Q : LemmaQSrcData C) {c' R T : ℝ}
    (hc' : Q.cQ ≤ c') (hR_nn : 0 ≤ R) (hR_ub : R ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : C.src.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' (Q.AC c' ^ 2) ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-R)) (huT_hi : virasoroUT c' T ≤ 0) (k : ℕ) :
    0 ≤ bandB1kSrc C.src c' R T g k := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hu_mem := Q.UT_between hc'_pos (by linarith : -(Q.AC c' ^ 2) ≤ -R) le_rfl
    (by linarith [hR_nn, hR_ub] : -R ≤ Q.AC c' ^ 2) hT_lo hT_hi
  refine intervalIntegral.integral_nonneg hu_mem.1.1 fun u hu => ?_
  have hΨ_nn : 0 ≤ (psiTildeSrc C.src c' g (u : ℂ)).re := by
    refine (Q.part3 hc' hg).1 u (abs_le.mpr ⟨by linarith [hu.1],
      by linarith [hu.2, hu_mem.1.2, sq_nonneg (Q.AC c')]⟩) ?_
    rw [← hu_mem.2]
    exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (Q.AC c')]⟩
      ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2, sq_nonneg (Q.AC c')]⟩ hu.2
  have hmin_nn : 0 ≤ min (1 : ℝ) (((k : ℝ) + 1) * (-u) / R) :=
    le_min zero_le_one (div_nonneg (mul_nonneg (by positivity) (by linarith [hu.2, huT_hi])) hR_nn)
  exact mul_nonneg hmin_nn hΨ_nn

lemma bandB1Src_le_B1k {C : CommonSource} (Q : LemmaQSrcData C) {c' R T : ℝ}
    (hc' : Q.cQ ≤ c') (hR_pos : 0 < R) (hR_ub : R ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : C.src.IsWeaklyFeasible (c' / 12) T g)
    (hT_lo : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi : T ≤ virasoroDeltaChart c' (-R)) (k : ℕ) :
    bandB1Src C.src c' R T g ≤ bandB1kSrc C.src c' R T g k := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by have := Q.hcQ_10000; linarith) hc'
  have hΔ_lo : virasoroDeltaChart c' (Q.AC c' ^ 2) ≤ virasoroDeltaChart c' 0 :=
    (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [sq_nonneg (Q.AC c')], sq_nonneg _⟩
      ⟨by linarith [sq_nonneg (Q.AC c')], le_rfl⟩ (sq_nonneg _)
  have hu_mem := Q.UT_between hc'_pos (by linarith : -(Q.AC c' ^ 2) ≤ -R)
    (sq_nonneg _) (by linarith : -R ≤ 0) hT_lo hT_hi
  have hmom := Q.psiTildeSrc_moment_integral_eq hc' hg.1
    (by linarith : -(Q.AC c' ^ 2) ≤ -R) (by linarith [hu_mem.1.2, sq_nonneg (Q.AC c')])
    hu_mem.1.1
  rw [hu_mem.2] at hmom
  have hB1_eq : bandB1Src C.src c' R T g =
      ∫ u in (-R)..(virasoroUT c' T), ((-u) / R) * (psiTildeSrc C.src c' g (u : ℂ)).re := by
    unfold bandB1Src
    rw [mul_assoc, ← hmom, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => by ring
  rw [hB1_eq]
  unfold bandB1kSrc
  have hΨ_cont : ContinuousOn (fun u : ℝ => (psiTildeSrc C.src c' g (u : ℂ)).re)
      (Icc (-R) (virasoroUT c' T)) := by
    refine Complex.continuous_re.comp_continuousOn
      ((Q.analytic hc' hg.1).continuousOn.comp continuous_ofReal.continuousOn fun u hu => ?_)
    exact Q.closedBall_subset_psiDom hc'_pos (by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (Q.AC c')]⟩)
  have hi_l : IntervalIntegrable
      (fun u : ℝ => (-u / R) * (psiTildeSrc C.src c' g (u : ℂ)).re) volume (-R) (virasoroUT c' T) :=
    ((continuousOn_id.neg.div_const R).mul hΨ_cont).intervalIntegrable_of_Icc hu_mem.1.1
  have hi_r : IntervalIntegrable
      (fun u : ℝ => min 1 (((k : ℝ) + 1) * (-u) / R) * (psiTildeSrc C.src c' g (u : ℂ)).re)
      volume (-R) (virasoroUT c' T) :=
    ((ContinuousOn.inf continuousOn_const ((continuousOn_const.mul continuousOn_id.neg).div_const R)).mul
      hΨ_cont).intervalIntegrable_of_Icc hu_mem.1.1
  refine intervalIntegral.integral_mono_on hu_mem.1.1 hi_l hi_r fun u hu => ?_
  have hΨ_nn : 0 ≤ (psiTildeSrc C.src c' g (u : ℂ)).re := by
    refine (Q.part3 hc' hg).1 u (abs_le.mpr ⟨by linarith [hu.1],
      by linarith [hu.2, hu_mem.1.2, sq_nonneg (Q.AC c')]⟩) ?_
    rw [← hu_mem.2]
    exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith [hu.1], by linarith [hu.2, hu_mem.1.2, sq_nonneg (Q.AC c')]⟩
      ⟨by linarith [hu_mem.1.1], by linarith [hu_mem.1.2, sq_nonneg (Q.AC c')]⟩ hu.2
  have hu_le1 : (-u) / R ≤ 1 := (div_le_one hR_pos).mpr (by linarith [hu.1])
  have hu_le_k : (-u) / R ≤ ((k : ℝ) + 1) * (-u) / R := by
    have h1k : (1 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    exact div_le_div_of_nonneg_right
      (le_mul_of_one_le_left (by linarith [hu.2, hu_mem.1.2]) h1k) hR_pos.le
  exact mul_le_mul_of_nonneg_right (le_min hu_le1 hu_le_k) hΨ_nn

end FormalResearch.ModularBootstrap.Mixtures
