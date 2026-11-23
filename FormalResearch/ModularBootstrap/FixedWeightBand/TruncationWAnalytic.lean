module

public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWDefs

/-!
# Truncated Mellin density at weight `w`: holomorphy, conjugation, reality (Lemma D', `vlo:Dp`)

Weight-`w` versions of `Contour.truncatedMellinP_analyticOnNhd`, `truncatedMellinP_conj` and
`truncatedMellinP_inner_im_ofReal` for `truncatedMellinPW prob`, together with the conjugation lemmas
for the Mellin density `m_g` at weight `w`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval FourierTransform

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special
open FormalResearch.ModularBootstrap.Chart
open FormalResearch.ModularBootstrap.ChartGeometry
open FormalResearch.ModularBootstrap.ComplexBessel
open FormalResearch.ModularBootstrap.StripMultiplier
open FormalResearch.ModularBootstrap.Mellin
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.WeightAxioms

private lemma holomorphic_conj_eq_of_real_nhds {f : ℂ → ℂ} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (_hδ_le : δ ≤ r)
    (hf_an : AnalyticOnNhd ℂ f (ball (0 : ℂ) r))
    (hf_real : ∀ x : ℝ, |x| < δ → (f (x : ℂ)).im = 0) :
    ∀ u ∈ ball (0 : ℂ) r, f (starRingEnd ℂ u) = starRingEnd ℂ (f u) := by
  let g : ℂ → ℂ := fun u => starRingEnd ℂ (f (starRingEnd ℂ u))
  have hg_an : AnalyticOnNhd ℂ g (ball (0 : ℂ) r) := fun u hu => by
    have hu_c : starRingEnd ℂ u ∈ ball (0 : ℂ) r := by
      simpa [mem_ball_zero_iff, Complex.norm_conj] using hu
    have hd := (hf_an _ hu_c).differentiableAt.conj_conj
    rw [Complex.conj_conj] at hd
    have heq_fn : (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) =
        (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) := rfl
    have hg_diff : DifferentiableOn ℂ g (ball (0 : ℂ) r) := fun w hw => by
      have hw_c : starRingEnd ℂ w ∈ ball (0 : ℂ) r := by
        simpa [mem_ball_zero_iff, Complex.norm_conj] using hw
      have hdw := (hf_an _ hw_c).differentiableAt.conj_conj
      rw [Complex.conj_conj] at hdw
      change DifferentiableWithinAt ℂ (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) (ball (0 : ℂ) r) w
      exact hdw.differentiableWithinAt
    exact (hg_diff.analyticOnNhd isOpen_ball) u hu
  have hfreq : ∃ᶠ u in 𝓝[≠] (0 : ℂ), f u = g u := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp hV
    let x : ℝ := min (ε / 2) (δ / 2)
    have hx_pos : 0 < x := lt_min (half_pos hε_pos) (half_pos hδ)
    refine ⟨(x : ℂ), hVU ⟨hε_ball ?_, Complex.ofReal_ne_zero.mpr hx_pos.ne'⟩, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hx_pos.le]
      exact (min_le_left _ _).trans_lt (half_lt_self hε_pos)
    · dsimp [g]
      rw [Complex.conj_ofReal]
      exact (Complex.conj_eq_iff_im.mpr (hf_real x
        (by rw [abs_of_pos hx_pos]; exact (min_le_right _ _).trans_lt (half_lt_self hδ)))).symm
  have heqOn := hf_an.eqOn_of_preconnected_of_frequently_eq hg_an
    (convex_ball (0 : ℂ) r).isPreconnected (mem_ball_self hr) hfreq
  intro u hu
  have hu_c : starRingEnd ℂ u ∈ ball (0 : ℂ) r := by
    simpa [mem_ball_zero_iff, Complex.norm_conj] using hu
  have h1 := heqOn hu_c
  dsimp [g] at h1
  rw [Complex.conj_conj] at h1
  exact h1

private lemma hasDerivWithinAt_mellinDensity_u (prob : FixedWeightProblem) {c' : ℝ} (_hc' : 0 < c') (g : ℝ → ℝ) {t₀ ω : ℂ}
    (ht₀ : 0 < t₀.re) :
    HasDerivAt (fun t : ℂ => mellinDensityIntegrandW prob.w c' g t ω)
      (Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * ω) * mellinMGEntireW prob.w g ((prob.w : ℂ) / 2 + (c' : ℂ) * ω) *
        (-((prob.w : ℂ) / 2 + (c' : ℂ) * ω) * (t₀)⁻¹ * (2 * (Real.pi : ℂ) * t₀) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ω)))) t₀ := by
  set z : ℂ := (prob.w : ℂ) / 2 + (c' : ℂ) * ω
  have h2pit_slit : 2 * (Real.pi : ℂ) * t₀ ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left
    have h1 : (2 * (Real.pi : ℂ) * t₀).re = 2 * Real.pi * t₀.re := by
      have : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.re_ofReal_mul]
    rw [h1]; exact mul_pos (mul_pos two_pos Real.pi_pos) ht₀
  have hd_lin : HasDerivAt (fun t : ℂ => 2 * (Real.pi : ℂ) * t) (2 * (Real.pi : ℂ)) t₀ := by
    simpa using (hasDerivAt_id t₀).const_mul (2 * (Real.pi : ℂ))
  have hd_cpow : HasDerivAt (fun t : ℂ => (2 * (Real.pi : ℂ) * t) ^ (-z))
      ((2 * (Real.pi : ℂ) * t₀) ^ (-z) * (-z * (2 * (Real.pi : ℂ) / (2 * (Real.pi : ℂ) * t₀)))) t₀ := by
    have hc := hd_lin.clog h2pit_slit
    have hce := (hc.const_mul (-z)).cexp
    refine (hce.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [(isOpen_slitPlane.preimage (continuous_const.mul continuous_id)).mem_nhds h2pit_slit] with t ht
      have ht' : 2 * (Real.pi : ℂ) * t ∈ Complex.slitPlane := ht
      change (2 * (Real.pi : ℂ) * t) ^ (-z) = Complex.exp (-z * Complex.log (2 * (Real.pi : ℂ) * t))
      rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero ht'), mul_comm]
    · rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero h2pit_slit), mul_comm (-z)]
  have hprod := (hd_cpow.const_mul (Complex.Gamma z)).mul_const (mellinMGEntireW prob.w g z)
  refine hprod.congr_deriv ?_
  have ht₀_ne : t₀ ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at ht₀; exact lt_irrefl 0 ht₀
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp [ht₀_ne, hpi_ne]

theorem truncatedMellinPW_analyticOnNhd (prob : FixedWeightProblem) {c' : ℝ} (hc' : dpThr prob ≤ c') (T₀ : ℝ) {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) :
    AnalyticOnNhd ℂ (truncatedMellinPW prob c' T₀ g)
      (ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) := by
  have hc'_10000 : 10000 ≤ c' := (dpThr_ge_10000 prob).trans hc'
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hcmax : max 1 (24 * prob.totalShift) ≤ c' := max_one_le_of_dpThr_le prob hc'
  set R : ℝ := innerChartRadius * c' ^ (2 / 3 : ℝ)
  refine DifferentiableOn.analyticOnNhd (fun u₀ hu₀ => ?_) isOpen_ball
  have hopen_u : u₀ ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) :=
    (virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hu₀)).1
  have hΔ_an : AnalyticAt ℂ (virasoroDeltaChartC c') u₀ :=
    virasoroDeltaChartC_analyticOnNhd hc'_pos u₀ hopen_u
  have hdΔ_an : AnalyticAt ℂ (deriv (virasoroDeltaChartC c')) u₀ :=
    (virasoroDeltaChartC_analyticOnNhd hc'_pos).deriv u₀ hopen_u
  have hV_an : AnalyticAt ℂ (fun u => cardyVC prob (c' / 12) (virasoroDeltaChartC c' u)) u₀ :=
    ((cardyVC_entire prob (c' / 12)).analyticAt _).comp_of_eq hΔ_an rfl
  set ω₀ : ℂ := chartOmega ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ))
  set ω₁ : ℂ := chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))
  set ωs : ℝ → ℂ := fun s => (1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁
  set F : ℂ → ℝ → ℂ := fun u s =>
    mellinDensityIntegrandW prob.w c' g (virasoroDeltaChartC c' u) (ωs s) * (ω₁ - ω₀)
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp (isOpen_ball (x := (0 : ℂ)) (ε := R)) u₀ hu₀
  have hcb_ball : closedBall u₀ (δ / 2) ⊆ ball (0 : ℂ) R := by
    intro w hw
    exact hδ_sub (mem_ball_iff_norm.mpr (lt_of_le_of_lt (mem_closedBall_iff_norm.mp hw) (half_lt_self hδ_pos)))
  have hΔ_cont : ContinuousOn (virasoroDeltaChartC c') (closedBall u₀ (δ / 2)) :=
    ((virasoroDeltaChartC_analyticOnNhd hc'_pos).continuousOn).mono (fun w hw =>
      (virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall (hcb_ball hw))).1)
  have ht_pos_on : ∀ w ∈ closedBall u₀ (δ / 2), 0 < (virasoroDeltaChartC c' w).re := by
    intro w hw
    exact (virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall (hcb_ball hw))).2.2.2.2.2
  have hre_cont : ContinuousOn (fun w => (virasoroDeltaChartC c' w).re) (closedBall u₀ (δ / 2)) :=
    Complex.continuous_re.comp_continuousOn hΔ_cont
  obtain ⟨w_min, hw_min_mem, hw_min⟩ := (isCompact_closedBall u₀ (δ / 2)).exists_isMinOn
    ⟨u₀, mem_closedBall_self (half_pos hδ_pos).le⟩ hre_cont
  set t_re_min : ℝ := (virasoroDeltaChartC c' w_min).re
  have ht_re_min_pos : 0 < t_re_min := ht_pos_on w_min hw_min_mem
  have hω_cont : Continuous ωs := by dsimp [ωs]; fun_prop
  have hz_cont : Continuous (fun s : ℝ => (prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) := by fun_prop
  have hmg_cont : Continuous (mellinMGEntireW prob.w g) := (testClass_differentiable_mellinMGEntireW prob hcmax hg).continuous
  have hω_re_zero : ∀ s : ℝ, (ωs s).re = 0 := fun s => by
    have h0 : ω₀.re = 0 := by
      by_cases hT : T₀ = 0
      · dsimp [ω₀]; rw [hT, Complex.ofReal_zero, mul_zero, add_zero, chartOmega_half, Complex.zero_re]
      · unfold ω₀ chartOmega; simp only [show ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ)).re ≤ 1 / 2 by simp, ↓reduceIte]
        exact chartOmegaHalf_midline_re_zero hT
    have h1 : ω₁.re = 0 := by
      have hconj : ω₁ = starRingEnd ℂ ω₀ := by
        dsimp [ω₀, ω₁]
        rw [show (1 / 2 : ℂ) - Complex.I * (T₀ : ℂ) = starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ)) by
          apply Complex.ext <;> simp, chartOmega_conj (by norm_num) (by norm_num)]
      rw [hconj, Complex.conj_re, h0]
    dsimp [ωs]
    simp [Complex.mul_re, h0, h1]
  have hGam_cont : Continuous (fun s : ℝ => Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s)) := by
    refine continuous_iff_continuousAt.mpr fun s => ?_
    have hre : 0 < ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s).re :=
      re_wHalf_add_mul_of_re_zero_pos prob.hw c' (hω_re_zero s)
    exact (Complex.differentiableAt_Gamma _ (fun m hm => by
      have hm_re := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at hm_re
      linarith only [hre, hm_re, Nat.cast_nonneg (α := ℝ) m])).continuousAt.comp
        (hz_cont.continuousAt)
  have hF_diff : ∀ w ∈ ball u₀ (δ / 2), ∀ s : ℝ,
      HasDerivAt (fun u => F u s)
        (Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) * mellinMGEntireW prob.w g ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) *
          (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) * (virasoroDeltaChartC c' w)⁻¹ *
            (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s))) *
          deriv (virasoroDeltaChartC c') w * (ω₁ - ω₀)) w := fun w hw s => by
    have hw_cb := Metric.ball_subset_closedBall hw
    have hw_ball := hcb_ball hw_cb
    have hopen_w := (virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hw_ball)).1
    have hdΔ_w : HasDerivAt (virasoroDeltaChartC c') (deriv (virasoroDeltaChartC c') w) w :=
      (virasoroDeltaChartC_analyticOnNhd hc'_pos w hopen_w).differentiableAt.hasDerivAt
    have hd_m := (hasDerivWithinAt_mellinDensity_u prob hc'_pos g (ω := ωs s) (ht_pos_on w hw_cb)).comp w hdΔ_w
    exact hd_m.mul_const (ω₁ - ω₀)
  have hF_meas : ∀ w ∈ ball u₀ (δ / 2), AEStronglyMeasurable (F w) (volume.restrict (Ι 0 1)) := fun w hw => by
    have hw_cb := Metric.ball_subset_closedBall hw
    have ht_re := ht_pos_on w hw_cb
    have h2pit_slit : 2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      have : (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).re =
          2 * Real.pi * (virasoroDeltaChartC c' w).re := by
        have hp : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
        rw [hp, Complex.re_ofReal_mul]
      rw [this]; exact mul_pos (mul_pos two_pos Real.pi_pos) ht_re
    have h2pit_ne := Complex.slitPlane_ne_zero h2pit_slit
    have hcont_s : Continuous (F w) := by
      dsimp [F, mellinDensityIntegrand]
      refine ((hGam_cont.mul ?_).mul (hmg_cont.comp hz_cont)).mul continuous_const
      simp_rw [Complex.cpow_def_of_ne_zero h2pit_ne]
      exact Complex.continuous_exp.comp (continuous_const.mul (hz_cont.neg))
    exact (hcont_s.continuousOn.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  set F' : ℂ → ℝ → ℂ := fun w s =>
    Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) * mellinMGEntireW prob.w g ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) *
      (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) * (virasoroDeltaChartC c' w)⁻¹ *
        (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s))) *
      deriv (virasoroDeltaChartC c') w * (ω₁ - ω₀)
  have hF_int : IntervalIntegrable (F u₀) volume 0 1 := by
    have ht_re := ht_pos_on u₀ (mem_closedBall_self (half_pos hδ_pos).le)
    have h2pit_slit : 2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u₀ ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      have hp : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
      have hre_2p : (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u₀).re =
          2 * Real.pi * (virasoroDeltaChartC c' u₀).re := by rw [hp, Complex.re_ofReal_mul]
      rw [hre_2p]
      exact mul_pos (mul_pos two_pos Real.pi_pos) ht_re
    have hcont_s : Continuous (F u₀) := by
      dsimp [F, mellinDensityIntegrand]
      refine ((hGam_cont.mul ?_).mul (hmg_cont.comp hz_cont)).mul continuous_const
      simp_rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero h2pit_slit)]
      exact Complex.continuous_exp.comp (continuous_const.mul (hz_cont.neg))
    exact hcont_s.continuousOn.intervalIntegrable_of_Icc zero_le_one
  have hF'_meas : AEStronglyMeasurable (F' u₀) (volume.restrict (Ι 0 1)) := by
    have ht_re := ht_pos_on u₀ (mem_closedBall_self (half_pos hδ_pos).le)
    have h2pit_slit : 2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u₀ ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      have hp : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
      have hre_2p : (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u₀).re =
          2 * Real.pi * (virasoroDeltaChartC c' u₀).re := by rw [hp, Complex.re_ofReal_mul]
      rw [hre_2p]
      exact mul_pos (mul_pos two_pos Real.pi_pos) ht_re
    have hcont_s : Continuous (F' u₀) := by
      dsimp [F']
      have hpow_c : Continuous fun s : ℝ =>
          (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u₀) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s)) := by
        simp_rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero h2pit_slit)]
        exact Complex.continuous_exp.comp (continuous_const.mul hz_cont.neg)
      exact (((hGam_cont.mul (hmg_cont.comp hz_cont)).mul
        ((hz_cont.neg.mul continuous_const).mul hpow_c)).mul continuous_const).mul continuous_const
    exact hcont_s.aestronglyMeasurable
  have hK_cpow : ∃ M_s : ℝ, 0 ≤ M_s ∧ ∀ s ∈ Icc (0 : ℝ) 1,
      ‖Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) * mellinMGEntireW prob.w g ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) *
        (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s))‖ ≤ M_s := by
    have hcont_g : Continuous fun s : ℝ =>
        ‖Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) * mellinMGEntireW prob.w g ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) *
          (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s))‖ :=
      ((hGam_cont.mul (hmg_cont.comp hz_cont)).mul hz_cont.neg).norm
    obtain ⟨s₀, _, hs₀_max⟩ := isCompact_Icc.exists_isMaxOn ⟨0, left_mem_Icc.mpr zero_le_one⟩ hcont_g.continuousOn
    exact ⟨‖_‖, norm_nonneg _, fun s hs => hs₀_max hs⟩
  obtain ⟨M_s, _, hM_s⟩ := hK_cpow
  have hhd_cont : ContinuousOn (deriv (virasoroDeltaChartC c')) (closedBall u₀ (δ / 2)) :=
    ((virasoroDeltaChartC_analyticOnNhd hc'_pos).deriv.continuousOn).mono (fun w hw =>
      (virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall (hcb_ball hw))).1)
  obtain ⟨w_d, _, hw_d⟩ := (isCompact_closedBall u₀ (δ / 2)).exists_isMaxOn
    ⟨u₀, mem_closedBall_self (half_pos hδ_pos).le⟩ hhd_cont.norm
  set M_d : ℝ := ‖deriv (virasoroDeltaChartC c') w_d‖
  obtain ⟨s₁, _, hs₁_max⟩ := isCompact_Icc.exists_isMaxOn ⟨0, left_mem_Icc.mpr zero_le_one⟩
    (continuous_norm.comp hz_cont).continuousOn
  set M_z : ℝ := ‖(prob.w : ℂ) / 2 + (c' : ℂ) * ωs s₁‖
  have hcpow_max : ∃ M_c : ℝ, 0 ≤ M_c ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ w ∈ closedBall u₀ (δ / 2),
      ‖(2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s))‖ ≤ M_c := by
    set C_base : ℝ := Real.exp (-((prob.w : ℝ) / 2) * Real.log (2 * Real.pi * t_re_min) + Real.pi * M_z)
    refine ⟨C_base, (Real.exp_pos _).le, fun s hs w hw => ?_⟩
    have ht_re := ht_pos_on w hw
    have ht_ge : t_re_min ≤ (virasoroDeltaChartC c' w).re := hw_min hw
    have h2p_norm : 2 * Real.pi * t_re_min ≤ ‖2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w‖ := by
      calc 2 * Real.pi * t_re_min ≤ 2 * Real.pi * (virasoroDeltaChartC c' w).re := by gcongr
        _ = (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).re := by
            have hp : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
            rw [hp, Complex.re_ofReal_mul]
        _ ≤ ‖2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w‖ := Complex.re_le_norm _
    have h2p_ne : 2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h2p_norm
      have := mul_pos (mul_pos two_pos Real.pi_pos) ht_re_min_pos
      linarith only [h2p_norm, this]
    rw [Complex.cpow_def_of_ne_zero h2p_ne, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hz_re : (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s)).re = -((prob.w : ℝ) / 2) := by
      rw [Complex.neg_re, re_wHalf_add_mul_of_re_zero prob.w c' (hω_re_zero s)]
    have hz_im_bd : |(-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s)).im| ≤ M_z := by
      rw [Complex.neg_im, abs_neg]
      calc |((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s).im| ≤ ‖(prob.w : ℂ) / 2 + (c' : ℂ) * ωs s‖ := Complex.abs_im_le_norm _
        _ ≤ M_z := hs₁_max hs
    have hprod_re : (Complex.log (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) *
        (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s))).re =
        Real.log ‖2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w‖ * (-((prob.w : ℝ) / 2)) -
          (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).arg *
            (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s)).im := by
      rw [Complex.mul_re, Complex.log_re, Complex.log_im, hz_re]
    rw [hprod_re]
    have hlog_bd : Real.log (2 * Real.pi * t_re_min) ≤
        Real.log ‖2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w‖ :=
      Real.log_le_log (mul_pos (mul_pos two_pos Real.pi_pos) ht_re_min_pos) h2p_norm
    have harg_bd : -((2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).arg *
        (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s)).im) ≤ Real.pi * M_z := by
      calc -((2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).arg *
            (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s)).im)
          ≤ |(2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).arg *
            (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s)).im| := neg_le_abs _
        _ = |(2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).arg| *
            |(-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s)).im| := abs_mul _ _
        _ ≤ Real.pi * M_z := mul_le_mul (Complex.abs_arg_le_pi _) hz_im_bd (abs_nonneg _) Real.pi_pos.le
    have h_lin_ineq : Real.log ‖2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w‖ * (-((prob.w : ℝ) / 2)) ≤
        -((prob.w : ℝ) / 2) * Real.log (2 * Real.pi * t_re_min) := by
      have hneg : -((prob.w : ℝ) / 2) ≤ 0 := by
        have : (0 : ℝ) ≤ (prob.w : ℝ) := Nat.cast_nonneg _
        linarith
      have := mul_le_mul_of_nonpos_left hlog_bd hneg
      linarith only [this]
    linarith only [h_lin_ineq, harg_bd]
  obtain ⟨M_c, _, hM_c⟩ := hcpow_max
  set M_bd : ℝ := M_s * t_re_min⁻¹ * M_c * M_d * ‖ω₁ - ω₀‖
  have h_bound : ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) 1 → ∀ w ∈ ball u₀ (δ / 2), ‖F' w s‖ ≤ M_bd := by
    refine Eventually.of_forall fun s hs w hw => ?_
    rw [Set.uIoc_of_le zero_le_one] at hs
    have hs' := Ioc_subset_Icc_self hs
    have hw' := Metric.ball_subset_closedBall hw
    have ht_inv : ‖(virasoroDeltaChartC c' w)⁻¹‖ ≤ t_re_min⁻¹ := by
      rw [norm_inv]
      exact inv_anti₀ ht_re_min_pos ((hw_min hw').trans (Complex.re_le_norm _))
    dsimp [F']
    have hreord : Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) * mellinMGEntireW prob.w g ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) *
        (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) * (virasoroDeltaChartC c' w)⁻¹ *
          (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s))) *
        deriv (virasoroDeltaChartC c') w * (ω₁ - ω₀) =
        (Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) * mellinMGEntireW prob.w g ((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s) *
          (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s))) *
          (virasoroDeltaChartC c' w)⁻¹ *
          (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ωs s)) *
          deriv (virasoroDeltaChartC c') w * (ω₁ - ω₀) := by ring
    rw [hreord, norm_mul, norm_mul, norm_mul, norm_mul]
    dsimp only [M_bd]
    gcongr
    · exact hM_s s hs'
    · exact hM_c s hs' w hw'
    · exact hw_d hw'
  have hF_meas_nhds : ∀ᶠ w in 𝓝 u₀, AEStronglyMeasurable (F w) (volume.restrict (Ι 0 1)) := by
    filter_upwards [Metric.ball_mem_nhds u₀ (half_pos hδ_pos)] with w hw
    exact hF_meas w hw
  have h_diff_ev : ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) 1 → ∀ w ∈ ball u₀ (δ / 2),
      HasDerivAt (fun u => F u s) (F' w s) w := by
    exact Eventually.of_forall fun s _ w hw => hF_diff w hw s
  have hderiv_int : DifferentiableAt ℂ (fun u => ∫ s in (0 : ℝ)..1, F u s) u₀ := by
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds u₀ (half_pos hδ_pos))
      hF_meas_nhds hF_int hF'_meas h_bound intervalIntegrable_const h_diff_ev).2.differentiableAt
  have hpre_diff : DifferentiableAt ℂ
      (fun u => -(deriv (virasoroDeltaChartC c') u / (prob.cardyNorm (c' / 12) g : ℂ)) *
        cardyVC prob (c' / 12) (virasoroDeltaChartC c' u) * ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I))) u₀ := by
    exact ((hdΔ_an.differentiableAt.div_const _).neg.mul hV_an.differentiableAt).mul_const _
  exact (hpre_diff.mul hderiv_int).differentiableWithinAt

lemma mellinTransformW_conj (g : ℝ → ℝ) (z : ℂ) :
    mellinTransformW g (starRingEnd ℂ z) = starRingEnd ℂ (mellinTransformW g z) := by
  unfold mellinTransformW
  have hcongr : EqOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (starRingEnd ℂ z - 1))
      (fun t : ℝ => starRingEnd ℂ ((g t : ℂ) * (t : ℂ) ^ (z - 1))) (Ioi 0) := by
    intro t ht
    have ht_pos : 0 < t := mem_Ioi.mp ht
    have hsub : starRingEnd ℂ z - 1 = starRingEnd ℂ (z - 1) := by simp
    have harg : (t : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg ht_pos.le]
      exact Real.pi_pos.ne
    have hcp := Complex.cpow_conj (t : ℂ) (z - 1) harg
    rw [Complex.conj_ofReal] at hcp
    simp only [map_mul, Complex.conj_ofReal, hsub, ← hcp]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_conj]

lemma mellinMGW_conj (g : ℝ → ℝ) (z : ℂ) :
    mellinMGW g (starRingEnd ℂ z) = starRingEnd ℂ (mellinMGW g z) := by
  unfold mellinMGW
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have h2pi : (2 * (Real.pi : ℂ)).arg ≠ Real.pi := by
    have hp : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    rw [hp, Complex.arg_ofReal_of_nonneg h2pi_pos.le]
    exact Real.pi_pos.ne
  have hcp := Complex.cpow_conj (2 * (Real.pi : ℂ)) z h2pi
  have h2pi_c : starRingEnd ℂ (2 * (Real.pi : ℂ)) = 2 * (Real.pi : ℂ) := by
    simp only [map_mul, map_ofNat, Complex.conj_ofReal]
  rw [h2pi_c] at hcp
  rw [hcp, mellinTransformW_conj, Complex.Gamma_conj, map_div₀, map_mul]

lemma mellinMGEntireW_conj (prob : FixedWeightProblem) (g : ℝ → ℝ) {z : ℂ} (hz : 0 < z.re) :
    mellinMGEntireW prob.w g (starRingEnd ℂ z) = starRingEnd ℂ (mellinMGEntireW prob.w g z) := by
  have hzc : 0 < (starRingEnd ℂ z).re := by simpa using hz
  rw [mellinMGEntireW_of_re_pos prob.w g hzc, mellinMGEntireW_of_re_pos prob.w g hz, mellinMGW_conj]

lemma mellinDensityIntegrandW_conj (prob : FixedWeightProblem) {c' : ℝ} (hc' : 0 < c') (g : ℝ → ℝ) {t ω : ℂ}
    (ht : 0 < t.re) (hω : 0 ≤ ω.re) :
    mellinDensityIntegrandW prob.w c' g (starRingEnd ℂ t) (starRingEnd ℂ ω) =
      starRingEnd ℂ (mellinDensityIntegrandW prob.w c' g t ω) := by
  unfold mellinDensityIntegrandW
  dsimp only
  set z : ℂ := (prob.w : ℂ) / 2 + (c' : ℂ) * ω
  have hz_re : 0 < z.re := re_wHalf_add_mul_pos prob.hw hc'.le hω
  have hzc_eq : (prob.w : ℂ) / 2 + (c' : ℂ) * starRingEnd ℂ ω = starRingEnd ℂ z := by
    dsimp [z]; simp only [map_add, map_div₀, map_ofNat, map_mul, Complex.conj_ofReal, map_natCast]
  have hgam_eq : Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * starRingEnd ℂ ω) =
      starRingEnd ℂ (Complex.Gamma z) := by
    rw [hzc_eq, Complex.Gamma_conj]
  rw [hgam_eq, hzc_eq, mellinMGEntireW_conj prob g hz_re]
  set w : ℂ := 2 * (Real.pi : ℂ) * starRingEnd ℂ t
  have harg : w.arg ≠ Real.pi := by
    have hre : 0 < w.re := by
      dsimp [w]
      have hp : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
      rw [hp, Complex.re_ofReal_mul, Complex.conj_re]
      exact mul_pos (mul_pos two_pos Real.pi_pos) ht
    exact (Complex.mem_slitPlane_iff_arg.mp (Complex.mem_slitPlane_iff.mpr (Or.inl hre))).1
  have hcp := Complex.cpow_conj w (-z) harg
  have hwc : starRingEnd ℂ w = 2 * (Real.pi : ℂ) * t := by
    dsimp [w]; simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_conj]
  rw [hwc] at hcp
  rw [show -starRingEnd ℂ z = starRingEnd ℂ (-z) by simp, hcp]
  simp only [map_mul]

lemma truncatedMellinPW_conj (prob : FixedWeightProblem) {c' : ℝ} (hc' : dpThr prob ≤ c') (T₀ : ℝ) {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    truncatedMellinPW prob c' T₀ g (starRingEnd ℂ u) =
      starRingEnd ℂ (truncatedMellinPW prob c' T₀ g u) := by
  have hc'_10000 : 10000 ≤ c' := (dpThr_ge_10000 prob).trans hc'
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hr_pos : 0 < innerChartRadius * c' ^ (2 / 3 : ℝ) :=
    mul_pos innerChartRadius_pos (Real.rpow_pos_of_pos hc'_pos _)
  refine holomorphic_conj_eq_of_real_nhds hr_pos hr_pos le_rfl
    (truncatedMellinPW_analyticOnNhd prob hc' T₀ hg) (fun x hx => ?_) u hu
  have hx_lt : |x| < innerChartRadius * c' ^ (2 / 3 : ℝ) := hx
  have hx_cb : (x : ℂ) ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx_lt.le
  have hreal := virasoroBChart_inner_real hc'_pos hx_lt.le
  let t : ℝ := (virasoroDeltaChartC c' (x : ℂ)).re
  have ht_pos : 0 < t := hreal.2.2.1
  have ht_eq : virasoroDeltaChartC c' (x : ℂ) = (t : ℂ) := Complex.ext rfl hreal.2.2.2
  have hd_im : (deriv (virasoroDeltaChartC c') (x : ℂ)).im = 0 := by
    have h_open : AnalyticOnNhd ℂ (virasoroDeltaChartC c')
        (ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :=
      (virasoroDeltaChartC_analyticOnNhd hc'_pos).mono (fun w hw =>
        (virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hw)).1)
    have hx_ball : (x : ℂ) ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx_lt
    have hd_r : HasDerivAt (fun s : ℝ => virasoroDeltaChartC c' (s : ℂ))
        (deriv (virasoroDeltaChartC c') (x : ℂ)) x :=
      (h_open _ hx_ball).differentiableAt.hasDerivAt.comp_ofReal
    have hd_im_f : HasDerivAt (fun s : ℝ => (virasoroDeltaChartC c' (s : ℂ)).im)
        (deriv (virasoroDeltaChartC c') (x : ℂ)).im x :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd_r
    have hev0 : (fun s : ℝ => (virasoroDeltaChartC c' (s : ℂ)).im) =ᶠ[𝓝 x] 0 := by
      filter_upwards [Metric.ball_mem_nhds x (sub_pos.mpr hx_lt)] with s hs
      have hs_in : |s| ≤ innerChartRadius * c' ^ (2 / 3 : ℝ) := by
        have h1 : |s - x| < innerChartRadius * c' ^ (2 / 3 : ℝ) - |x| := by
          simpa [Real.dist_eq] using hs
        have h2 := abs_add_le (s - x) x
        rw [sub_add_cancel] at h2
        linarith
      exact (virasoroBChart_inner_real hc'_pos hs_in).2.2.2
    exact (hd_im_f.congr_of_eventuallyEq hev0.symm).deriv.symm.trans (by simp)
  have hV_eq : cardyVC prob (c' / 12) (virasoroDeltaChartC c' (x : ℂ)) =
      (prob.cardyV (c' / 12) t : ℂ) := by
    rw [ht_eq, cardyVC_ofReal]
  let ω₀ : ℂ := chartOmega ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ))
  let ω₁ : ℂ := chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))
  have hω₀_re : ω₀.re = 0 := by
    by_cases hT : T₀ = 0
    · dsimp [ω₀]; rw [hT, Complex.ofReal_zero, mul_zero, add_zero, chartOmega_half, Complex.zero_re]
    · unfold ω₀ chartOmega; simp only [show ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ)).re ≤ 1 / 2 by simp, ↓reduceIte]
      exact chartOmegaHalf_midline_re_zero hT
  have hω₁_eq : ω₁ = starRingEnd ℂ ω₀ := by
    dsimp [ω₀, ω₁]
    rw [show (1 / 2 : ℂ) - Complex.I * (T₀ : ℂ) = starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ)) by
      apply Complex.ext <;> simp, chartOmega_conj (by norm_num) (by norm_num)]
  have hω_sub_conj : starRingEnd ℂ (ω₁ - ω₀) = -(ω₁ - ω₀) := by
    rw [map_sub, hω₁_eq, Complex.conj_conj]; ring
  have hint_conj :
      starRingEnd ℂ (((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
        ∫ s in (0 : ℝ)..1,
          mellinDensityIntegrandW prob.w c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)) =
      ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
        ∫ s in (0 : ℝ)..1,
          mellinDensityIntegrandW prob.w c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀) := by
    rw [map_mul, show starRingEnd ℂ ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) =
        -((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) by
        simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]; ring]
    have hω₁_re : ω₁.re = 0 := by rw [hω₁_eq, Complex.conj_re, hω₀_re]
    have hint_seg : IntervalIntegrable
        (fun s : ℝ => mellinDensityIntegrandW prob.w c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀))
        volume 0 1 := by
      have hωs_c : Continuous fun s : ℝ => (1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁ := by fun_prop
      have hz_c : Continuous fun s : ℝ => (prob.w : ℂ) / 2 + (c' : ℂ) * ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) := by
        fun_prop
      have hre_pt : ∀ s : ℝ, 0 < ((prob.w : ℂ) / 2 + (c' : ℂ) * ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁)).re := by
        intro s
        have hωs_re : ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁).re = 0 := by
          simp [Complex.add_re, Complex.mul_re, hω₀_re, hω₁_re]
        exact re_wHalf_add_mul_of_re_zero_pos prob.hw c' hωs_re
      have hGam_c : Continuous fun s : ℝ =>
          Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁)) := by
        refine continuous_iff_continuousAt.mpr fun s => ?_
        exact (Complex.differentiableAt_Gamma _ (fun m hm => by
          have hm_re := congrArg Complex.re hm
          simp only [Complex.neg_re, Complex.natCast_re] at hm_re
          linarith [hre_pt s, Nat.cast_nonneg (α := ℝ) m])).continuousAt.comp
            (hz_c.continuousAt)
      have hm_c : Continuous fun s : ℝ =>
          mellinMGEntireW prob.w g ((prob.w : ℂ) / 2 + (c' : ℂ) * ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁)) :=
        (testClass_differentiable_mellinMGEntireW prob (max_one_le_of_dpThr_le prob hc') hg).continuous.comp hz_c
      have h2pit_ne : (2 * (Real.pi : ℂ) * (t : ℂ)) ≠ 0 := by
        have : 0 < 2 * Real.pi * t := by positivity
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hp_c : Continuous fun s : ℝ =>
          (2 * (Real.pi : ℂ) * (t : ℂ)) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁))) := by
        simp_rw [Complex.cpow_def_of_ne_zero h2pit_ne]
        exact Complex.continuous_exp.comp (continuous_const.mul hz_c.neg)
      have htot_c : Continuous fun s : ℝ =>
          mellinDensityIntegrandW prob.w c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀) :=
        ((hGam_c.mul hp_c).mul hm_c).mul continuous_const
      exact htot_c.intervalIntegrable 0 1
    have hconj_int : starRingEnd ℂ (∫ s in (0 : ℝ)..1,
          mellinDensityIntegrandW prob.w c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)) =
        ∫ s in (0 : ℝ)..1,
          starRingEnd ℂ (mellinDensityIntegrandW prob.w c' g (t : ℂ)
            ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)) :=
      (Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint_seg).symm
    rw [hconj_int]
    have hsub : (fun s : ℝ => starRingEnd ℂ (mellinDensityIntegrandW prob.w c' g (t : ℂ)
          ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀))) =
        fun s : ℝ => -(mellinDensityIntegrandW prob.w c' g (t : ℂ)
          ((1 - ((1 - s : ℝ) : ℂ)) * ω₀ + ((1 - s : ℝ) : ℂ) * ω₁) * (ω₁ - ω₀)) := by
      ext s
      rw [map_mul, hω_sub_conj]
      have hre_pt : ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁).re = 0 := by
        simp [Complex.add_re, Complex.mul_re, hω₀_re, hω₁_re]
      have hm_c := mellinDensityIntegrandW_conj prob hc'_pos g (t := (t : ℂ)) (by simpa using ht_pos) hre_pt.ge
      rw [Complex.conj_ofReal] at hm_c
      have hpt_conj : starRingEnd ℂ ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) =
          (1 - ((1 - s : ℝ) : ℂ)) * ω₀ + ((1 - s : ℝ) : ℂ) * ω₁ := by
        simp only [map_add, map_mul, map_sub, map_one, Complex.conj_ofReal, ← hω₁_eq]
        rw [hω₁_eq, Complex.conj_conj]
        push_cast; ring
      rw [← hm_c, hpt_conj]
      ring
    rw [hsub, intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left
      (fun s : ℝ => mellinDensityIntegrandW prob.w c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)) 1]
    simp only [sub_zero, sub_self]
    ring
  have h_all_real : truncatedMellinPW prob c' T₀ g (x : ℂ) =
      starRingEnd ℂ (truncatedMellinPW prob c' T₀ g (x : ℂ)) := by
    unfold truncatedMellinPW
    dsimp only
    rw [hV_eq, ht_eq]
    set A_pre : ℂ := -(deriv (virasoroDeltaChartC c') (x : ℂ) / (prob.cardyNorm (c' / 12) g : ℂ)) *
      (prob.cardyV (c' / 12) t : ℂ)
    set B_int : ℂ := ∫ s in (0 : ℝ)..1,
      mellinDensityIntegrandW prob.w c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)
    change A_pre * ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) * B_int =
      starRingEnd ℂ (A_pre * ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) * B_int)
    rw [mul_assoc A_pre, map_mul, hint_conj]
    congr 1
    dsimp [A_pre]
    rw [map_mul, map_neg, map_div₀, Complex.conj_eq_iff_im.mpr hd_im,
      Complex.conj_ofReal, Complex.conj_ofReal]
  exact Complex.conj_eq_iff_im.mp h_all_real.symm

lemma truncatedMellinPW_inner_im_ofReal (prob : FixedWeightProblem) {c' : ℝ} (hc' : dpThr prob ≤ c') (T₀ : ℝ) {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) {x : ℝ}
    (hx : |x| < innerChartRadius * c' ^ (2 / 3 : ℝ)) :
    (truncatedMellinPW prob c' T₀ g (x : ℂ)).im = 0 := by
  have hx_ball : (x : ℂ) ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx
  have h1 := truncatedMellinPW_conj prob hc' T₀ hg hx_ball
  rw [Complex.conj_ofReal] at h1
  exact Complex.conj_eq_iff_im.mp h1.symm


/-- Conjugation symmetry of the exact density `Ψ̃ = psiTilde prob` on the inner disc, given its
holomorphy on `psiDom c'` (`psiTilde_analyticOnNhd`). -/
lemma psiTilde_inner_conj (prob : FixedWeightProblem) {c' : ℝ} (hc'_pos : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g)
    (hAn : AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c')) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    psiTilde prob c' g (starRingEnd ℂ u) = starRingEnd ℂ (psiTilde prob c' g u) := by
  have hr_pos : 0 < innerChartRadius * c' ^ (2 / 3 : ℝ) :=
    mul_pos innerChartRadius_pos (Real.rpow_pos_of_pos hc'_pos _)
  have hac_pos : 0 < virasoroAC c' ^ 2 := sq_pos_of_pos (virasoroAC_pos hc'_pos)
  have hsub : ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) ⊆ psiDom c' := fun w hw => by
    have hb := virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hw)
    exact ⟨hb.1, hb.2.2.2.2.1⟩
  refine holomorphic_conj_eq_of_real_nhds hr_pos (lt_min hr_pos hac_pos) (min_le_left _ _)
    (hAn.mono hsub) (fun x hx => ?_) u hu
  exact psiTilde_im_ofReal prob hc'_pos hg (hx.le.trans (min_le_right _ _))

lemma psiTilde_inner_im_ofReal (prob : FixedWeightProblem) {c' : ℝ} (hc'_pos : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g)
    (hAn : AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c')) {x : ℝ}
    (hx : |x| < innerChartRadius * c' ^ (2 / 3 : ℝ)) :
    (psiTilde prob c' g (x : ℂ)).im = 0 := by
  have hx_ball : (x : ℂ) ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx
  have h1 := psiTilde_inner_conj prob hc'_pos hg hAn hx_ball
  rw [Complex.conj_ofReal] at h1
  exact Complex.conj_eq_iff_im.mp h1.symm

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.truncatedMellinPW_analyticOnNhd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms truncatedMellinPW_analyticOnNhd

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.truncatedMellinPW_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms truncatedMellinPW_conj

end FormalResearch.ModularBootstrap.FixedWeightBand
