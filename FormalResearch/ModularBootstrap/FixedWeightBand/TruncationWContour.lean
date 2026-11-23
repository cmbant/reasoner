module

public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWReal

/-!
# Contour deformation and the inner-disc bound at weight `w` (Lemma D', `vlo:Dp`)

Weight-`w` versions of `Contour.truncatedMellinP_eq_contourIntegral`, `truncatedMellinP_deform` and
`truncatedMellinP_inner_bound`: on the inner chart disc, `truncatedMellinPW prob` equals the contour integral
of `mellinDensityIntegrandW` along the saddle contour `dpConfig_spec`, and `‖P‖ ≤ C_P c'^{1/3} airyEnv`.
New relative to weight one: the Stirling^(w) prefactor `|3ω/(2π b²)|^{(w-1)/2}`, bounded on the contour by
`|ω| ≤ C_Γ`, `|b| ≥ ξ_*/2`.
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

lemma contourChained_endpointsW {ω₀ ω₁ : ℂ} (hne : ω₀ ≠ ω₁) {segs : List ContourSeg}
    (hchain : ContourChained ω₀ ω₁ segs) :
    (∃ S ∈ segs, S.a ∈ Icc S.a S.b ∧ S.ω S.a = ω₀) ∧
      (∃ S ∈ segs, S.b ∈ Icc S.a S.b ∧ S.ω S.b = ω₁) := by
  induction segs generalizing ω₀ with
  | nil => exact absurd hchain hne
  | cons S rest ih =>
    rcases hchain with ⟨hhead, hrest⟩
    refine ⟨⟨S, by simp, ⟨le_rfl, S.hab⟩, hhead⟩, ?_⟩
    cases rest with
    | nil =>
      exact ⟨S, by simp, ⟨S.hab, le_rfl⟩, hrest⟩
    | cons S' rest' =>
      by_cases hne' : S.ω S.b = ω₁
      · exact ⟨S, by simp, ⟨S.hab, le_rfl⟩, hne'⟩
      · obtain ⟨_, Sl, hSl, hSlb, hSl_eq⟩ := ih hne' hrest
        exact ⟨Sl, by simp [hSl], hSlb, hSl_eq⟩

lemma norm_contourIntegral_leW (f : ℂ → ℂ) (segs : List ContourSeg) (M : ℝ) (_hM : 0 ≤ M)
    (hf : ∀ S ∈ segs, ContinuousOn (fun τ => f (S.ω τ)) (Icc S.a S.b))
    (hbd : ∀ S ∈ segs, ∀ τ ∈ Icc S.a S.b, ‖f (S.ω τ)‖ ≤ M) :
    ‖contourIntegral f segs‖ ≤ M * contourLength segs := by
  induction segs with
  | nil => simp [contourIntegral, contourLength]
  | cons S rest ih =>
    have hfS : ContinuousOn (fun τ => f (S.ω τ)) (Icc S.a S.b) := hf S (by simp)
    have hf_rest : ∀ S' ∈ rest, ContinuousOn (fun τ => f (S'.ω τ)) (Icc S'.a S'.b) :=
      fun S' hS' => hf S' (by simp [hS'])
    have hS : ∀ τ ∈ Icc S.a S.b, ‖f (S.ω τ)‖ ≤ M := hbd S (by simp)
    have hrest : ∀ S' ∈ rest, ∀ τ ∈ Icc S'.a S'.b, ‖f (S'.ω τ)‖ ≤ M :=
      fun S' hS' => hbd S' (by simp [hS'])
    have hseg_le : ‖∫ τ in S.a..S.b, f (S.ω τ) * S.ω' τ‖ ≤ M * ∫ τ in S.a..S.b, ‖S.ω' τ‖ := by
      have h1 : ‖∫ τ in S.a..S.b, f (S.ω τ) * S.ω' τ‖ ≤ ∫ τ in S.a..S.b, ‖f (S.ω τ) * S.ω' τ‖ :=
        intervalIntegral.norm_integral_le_integral_norm S.hab
      have h2 : ∫ τ in S.a..S.b, ‖f (S.ω τ) * S.ω' τ‖ ≤ ∫ τ in S.a..S.b, M * ‖S.ω' τ‖ := by
        refine intervalIntegral.integral_mono_on S.hab ?_ ?_ fun τ hτ => ?_
        · exact (hfS.mul S.hω'_cont).norm.intervalIntegrable_of_Icc S.hab
        · exact (continuousOn_const.mul (S.hω'_cont.norm)).intervalIntegrable_of_Icc S.hab
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hS τ hτ) (norm_nonneg _)
      simpa [intervalIntegral.integral_const_mul] using h1.trans h2
    have hrest_le := ih hf_rest hrest
    change ‖(∫ τ in S.a..S.b, f (S.ω τ) * S.ω' τ) + contourIntegral f rest‖ ≤
      M * ((∫ τ in S.a..S.b, ‖S.ω' τ‖) + contourLength rest)
    calc ‖(∫ τ in S.a..S.b, f (S.ω τ) * S.ω' τ) + contourIntegral f rest‖
        ≤ ‖∫ τ in S.a..S.b, f (S.ω τ) * S.ω' τ‖ + ‖contourIntegral f rest‖ := norm_add_le _ _
      _ ≤ M * (∫ τ in S.a..S.b, ‖S.ω' τ‖) + M * contourLength rest := add_le_add hseg_le hrest_le
      _ = _ := by ring

lemma truncatedMellinPW_eq_contourIntegral (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : dpThr prob ≤ c')
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)))
    {segs : List ContourSeg}
    (hchain : ContourChained (chartOmega ((1 / 2 : ℂ) + Complex.I * (dpT0 : ℂ)))
      (chartOmega ((1 / 2 : ℂ) - Complex.I * (dpT0 : ℂ))) segs)
    (hω_bd : ∀ S ∈ segs, ∀ τ ∈ Icc S.a S.b,
      0 ≤ (S.ω τ).re ∧ dpConfig.c_Γ ≤ ‖S.ω τ‖ ∧
        ‖S.ω τ‖ ≤ dpConfig.C_Γ ∧ ‖S.ω' τ‖ ≤ dpConfig.C_d) :
    truncatedMellinPW prob c' dpT0 g u =
      -(deriv (virasoroDeltaChartC c') u / (prob.cardyNorm (c' / 12) g : ℂ)) *
        cardyVC prob (c' / 12) (virasoroDeltaChartC c' u) *
        ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
        contourIntegral (mellinDensityIntegrandW prob.w c' g (virasoroDeltaChartC c' u)) segs := by
  have hc'_10000 : 10000 ≤ c' := (dpThr_ge_10000 prob).trans hc'
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hcmax : max 1 (24 * prob.totalShift) ≤ c' := max_one_le_of_dpThr_le prob hc'
  set B_r : ℝ := 4 * c' * dpConfig.C_Γ ^ 2 + 1
  set B : ℂ := (B_r : ℂ)
  set R : ℝ := B_r + 1 / (8 * c')
  have hB_pos : 0 < B_r := by positivity
  have hR_pos : 0 < R := by positivity
  have hmem_of : ∀ ω : ℂ, 0 ≤ ω.re → ‖ω‖ ≤ dpConfig.C_Γ → ω ∈ ball B R := fun ω hre hnorm => by
    rw [mem_ball_iff_norm]
    have hsq : ‖ω - B‖ ^ 2 < R ^ 2 := by
      have h1 : ‖ω - B‖ ^ 2 = (ω.re - B_r) ^ 2 + ω.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [B, sq]
      have h2 : ω.re ^ 2 + ω.im ^ 2 ≤ dpConfig.C_Γ ^ 2 := by
        have h3 := Complex.normSq_eq_norm_sq ω
        rw [Complex.normSq_apply] at h3
        have hn := norm_nonneg ω
        have hcG := lt_of_lt_of_le dpConfig.hc_Γ_pos dpConfig.hc_Γ_le
        have hsq_le : ‖ω‖ ^ 2 ≤ dpConfig.C_Γ ^ 2 := pow_le_pow_left₀ hn hnorm 2
        linarith only [h3, hsq_le]
      have h3 : (ω.re - B_r) ^ 2 + ω.im ^ 2 ≤ B_r ^ 2 + dpConfig.C_Γ ^ 2 := by
        have hprod : 0 ≤ 2 * B_r * ω.re := by positivity
        nlinarith only [h2, hprod]
      have hR_sq : R ^ 2 = B_r ^ 2 + (dpConfig.C_Γ ^ 2 + 1 / (4 * c')) + (1 / (8 * c')) ^ 2 := by
        dsimp [R, B_r]; field_simp [hc'_pos.ne']; ring
      have hpos : 0 < 1 / (4 * c') + (1 / (8 * c')) ^ 2 := by positivity
      linarith only [h1, h3, hR_sq, hpos]
    exact (sq_lt_sq₀ (norm_nonneg _) hR_pos.le).mp hsq
  have hdiff : DifferentiableOn ℂ (mellinDensityIntegrandW prob.w c' g (virasoroDeltaChartC c' u)) (ball B R) := by
    intro ω hω
    have hω_re_gt : -(1 / (8 * c')) < ω.re := by
      have h1 := (Complex.abs_re_le_norm (ω - B)).trans_lt (mem_ball_iff_norm.mp hω)
      simp only [Complex.sub_re, B, Complex.ofReal_re, abs_lt] at h1
      have hR_def : R = B_r + 1 / (8 * c') := rfl
      linarith only [h1.1, hR_def]
    have hz_re : 0 < ((prob.w : ℂ) / 2 + (c' : ℂ) * ω).re := by
      rw [re_wHalf_add_mul]
      have hw1 : (1 : ℝ) ≤ prob.w := by exact_mod_cast prob.hw
      have hcw : -(1 / 8 : ℝ) < c' * ω.re := by
        calc -(1 / 8 : ℝ) = c' * (-(1 / (8 * c'))) := by field_simp [hc'_pos.ne']
          _ < c' * ω.re := mul_lt_mul_of_pos_left hω_re_gt hc'_pos
      linarith only [hcw, hw1]
    have hm_diff : DifferentiableAt ℂ (fun w => mellinMGEntireW prob.w g ((prob.w : ℂ) / 2 + (c' : ℂ) * w)) ω := by
      have hc'_lin : DifferentiableAt ℂ (fun w : ℂ => (prob.w : ℂ) / 2 + (c' : ℂ) * w) ω := by fun_prop
      exact (testClass_differentiable_mellinMGEntireW prob hcmax hg _).comp ω hc'_lin
    have hGam_diff : DifferentiableAt ℂ (fun w => Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * w)) ω := by
      have hc'_lin : DifferentiableAt ℂ (fun w : ℂ => (prob.w : ℂ) / 2 + (c' : ℂ) * w) ω := by fun_prop
      exact (Complex.differentiableAt_Gamma _ (fun m hm => by
        have hre_m := congrArg Complex.re hm
        simp only [Complex.neg_re, Complex.natCast_re] at hre_m
        linarith only [hz_re, hre_m, Nat.cast_nonneg (α := ℝ) m])).comp ω hc'_lin
    have ht_slit : 2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u ∈ Complex.slitPlane := by
      left
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
      exact mul_pos (by positivity) (virasoroBChart_inner_bounds hc'_pos hu).2.2.2.2.2
    have hpow_diff : DifferentiableAt ℂ
        (fun w => (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * w))) ω := by
      have hexp : (fun w : ℂ => (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u) ^
            (-((prob.w : ℂ) / 2 + (c' : ℂ) * w))) =
          fun w => Complex.exp (Complex.log (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u) *
            (-((prob.w : ℂ) / 2 + (c' : ℂ) * w))) := by
        ext w; rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero ht_slit)]
      rw [hexp]; fun_prop
    exact ((hGam_diff.mul hpow_diff).mul hm_diff).differentiableWithinAt
  set ω₀ : ℂ := chartOmega ((1 / 2 : ℂ) + Complex.I * (dpT0 : ℂ))
  set ω₁ : ℂ := chartOmega ((1 / 2 : ℂ) - Complex.I * (dpT0 : ℂ))
  have hT₀_pos : 0 < dpT0 := by unfold dpT0; linarith only [dpConfig.hT₀_ge]
  have hY_neg : midlineY dpT0 < 0 := by
    have h1 := im_chartOmega_midline_strictAnti hT₀_pos
    dsimp only at h1
    rw [Complex.ofReal_zero, mul_zero, add_zero, chartOmega_half, Complex.zero_im] at h1
    exact h1
  have hω₀_ne_ω₁ : ω₀ ≠ ω₁ := by
    intro h0
    have h1 : (1 / 2 : ℂ) - Complex.I * (dpT0 : ℂ) =
        starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (dpT0 : ℂ)) := by apply Complex.ext <;> simp
    have him1 : ω₁.im = -ω₀.im := by
      dsimp [ω₁]; rw [h1, chartOmega_conj (by norm_num) (by norm_num), Complex.conj_im]
    have him_eq := congrArg Complex.im h0
    rw [him1] at him_eq
    change midlineY dpT0 = -midlineY dpT0 at him_eq
    linarith only [him_eq, hY_neg]
  obtain ⟨⟨S₀, hS₀, hτ₀, hω₀_eq⟩, ⟨S₁, hS₁, hτ₁, hω₁_eq⟩⟩ :=
    contourChained_endpointsW hω₀_ne_ω₁ hchain
  have hω₀_mem : ω₀ ∈ ball B R := by
    have hbd₀ := hω_bd S₀ hS₀ S₀.a hτ₀
    rw [hω₀_eq] at hbd₀
    exact hmem_of ω₀ hbd₀.1 hbd₀.2.2.1
  have hω₁_mem : ω₁ ∈ ball B R := by
    have hbd₁ := hω_bd S₁ hS₁ S₁.b hτ₁
    rw [hω₁_eq] at hbd₁
    exact hmem_of ω₁ hbd₁.1 hbd₁.2.2.1
  have hmem_segs : ∀ S ∈ segs, ∀ τ ∈ Icc S.a S.b, S.ω τ ∈ ball B R := fun S hS τ hτ =>
    hmem_of (S.ω τ) (hω_bd S hS τ hτ).1 (hω_bd S hS τ hτ).2.2.1
  have hdef := contourIntegral_eq_segment_of_ball hdiff segs hchain hmem_segs hω₀_mem hω₁_mem
  unfold truncatedMellinPW
  change _ = -(deriv (virasoroDeltaChartC c') u / (prob.cardyNorm (c' / 12) g : ℂ)) *
      cardyVC prob (c' / 12) (virasoroDeltaChartC c' u) *
      ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
      contourIntegral (mellinDensityIntegrandW prob.w c' g (virasoroDeltaChartC c' u)) segs
  rw [hdef]

lemma truncatedMellinPW_deform (prob : FixedWeightProblem) {c' ρ φ' : ℝ} (hc' : dpThr prob ≤ c')
    (hρ₀ : 0 ≤ ρ) (hρ : ρ ≤ dpConfig.ρ₀) (hφ₀ : 0 ≤ φ') (hφ : φ' ≤ Real.pi / 2)
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    let s : ℂ := (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ))
    let b : ℂ := chartB s
    ∃ segs : List ContourSeg,
      ContourChained (chartOmega ((1 / 2 : ℂ) + Complex.I * (dpT0 : ℂ)))
        (chartOmega ((1 / 2 : ℂ) - Complex.I * (dpT0 : ℂ))) segs ∧
      contourLength segs ≤ dpConfig.C_len ∧
      (∀ S ∈ segs, ∀ τ ∈ Icc S.a S.b,
        0 ≤ (S.ω τ).re ∧ dpConfig.c_Γ ≤ ‖S.ω τ‖ ∧
          ‖S.ω τ‖ ≤ dpConfig.C_Γ ∧ ‖S.ω' τ‖ ≤ dpConfig.C_d) ∧
      (∀ S ∈ segs, S.isStrip = true → ∀ τ ∈ Icc S.a S.b,
        ‖S.ζ' τ‖ ≤ dpConfig.C_d ∧ (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re) ∧
      (∀ S ∈ segs, S.isStrip = false →
        ∀ τ ∈ Icc S.a S.b,
          dpConfig.μ₀ ≤ (S.ω τ).re ∧
            crudeExponentEc (S.ω τ) b ≤ (chartPhiV s b).re - dpConfig.c_γ * ρ * s.re ^ 2) ∧
      truncatedMellinPW prob c' dpT0 g u =
        -(deriv (virasoroDeltaChartC c') u / (prob.cardyNorm (c' / 12) g : ℂ)) *
          cardyVC prob (c' / 12) (virasoroDeltaChartC c' u) *
          ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
          contourIntegral (mellinDensityIntegrandW prob.w c' g (virasoroDeltaChartC c' u)) segs := by
  obtain ⟨_, _, _, segs, hchain, hlen, hω_bd, hstrip, _, _, _, _, hnonstrip, _, _, _⟩ :=
    dpConfig_spec hρ₀ hρ hφ₀ hφ
  exact ⟨segs, hchain, hlen, hω_bd, hstrip, hnonstrip,
    truncatedMellinPW_eq_contourIntegral prob hc' hg hu hchain hω_bd⟩

lemma airyEnv_conjW (u : ℂ) : airyEnv (starRingEnd ℂ u) = airyEnv u := by
  unfold airyEnv
  by_cases hu : u = 0
  · simp [hu]
  · have hu_re_im : (starRingEnd ℂ u ^ (3 / 2 : ℂ)).re = (u ^ (3 / 2 : ℂ)).re := by
      have hpow : starRingEnd ℂ (u ^ (3 / 2 : ℂ)) = (starRingEnd ℂ u) ^ (3 / 2 : ℂ) ∨ u.im = 0 ∧ u.re ≤ 0 := by
        by_cases hneg : u.im = 0 ∧ u.re ≤ 0
        · exact Or.inr hneg
        · left
          have harg : u.arg ≠ Real.pi := by
            intro hpi
            exact hneg (Complex.arg_eq_pi_iff.mp hpi |>.2 |> fun him => ⟨him, (Complex.arg_eq_pi_iff.mp hpi).1.le⟩)
          have hc := Complex.cpow_conj u (3 / 2 : ℂ) harg
          have h32c : starRingEnd ℂ (3 / 2 : ℂ) = (3 / 2 : ℂ) := by simp only [map_div₀, map_ofNat]
          rw [h32c] at hc
          have hc2 := congrArg (starRingEnd ℂ) hc
          rw [Complex.conj_conj] at hc2
          exact hc2
      rcases hpow with h | h
      · rw [← h, Complex.conj_re]
      · have hcu : starRingEnd ℂ u = u := Complex.ext (by simp) (by simp [h.1])
        rw [hcu]
    rw [hu_re_im]


theorem truncatedMellinPW_inner_bound {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ c_P C_P c₀_P : ℝ, dpThr prob ≤ c_P ∧ 0 < C_P ∧ 0 < c₀_P ∧ c₀_P ≤ innerChartRadius / 2 ∧
      c₀_P ≤ 2 * chartBV D.r_1 ^ 2 ∧
      ∀ {c' : ℝ}, c_P ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass prob (c' / 12) g →
        0 < prob.cardyNorm (c' / 12) g →
        ∀ {u : ℂ}, u ∈ closedBall (0 : ℂ) (c₀_P * c' ^ (2 / 3 : ℝ)) →
          ¬ (u.im = 0 ∧ u.re ≤ 0) →
          ‖truncatedMellinPW prob c' dpT0 g u‖ ≤ C_P * c' ^ (1 / 3 : ℝ) * airyEnv u := by
  obtain ⟨_, q_V, c₀_max, hc₀_max_pos, C₁, hC₁, C₂, hC₂, C₃, hC₃, _, _, _, _, hS6_main, _⟩ :=
    lemma_S6 langerChartSpec_virasoro
  obtain ⟨r_φ, hr_φ_pos, _, hφ_pot⟩ := chartPhiV_saddle_eq_potential
  obtain ⟨C_S4, c_S4, hCS4_pos, hcS4_thr, hS4⟩ := lemma_S4_W prob
  obtain ⟨C_S2, c_S2, hCS2_pos, hcS2_thr, hS2⟩ := lemma_S2_W prob dpConfig.hμ₀_gt
  obtain ⟨c_V, C_V, hcV_c0, hc_V_39, hCV_pos, hV_fn⟩ := cardyVC_inner_bound D
  let P_Γ : ℝ := (3 * dpConfig.C_Γ / (2 * Real.pi * (xiStar / 2) ^ 2)) ^ (((prob.w : ℝ) - 1) / 2)
  have hPΓ_pos : 0 < P_Γ := by
    have := Real.pi_pos
    have := xiStar_pos
    have := lt_of_lt_of_le dpConfig.hc_Γ_pos dpConfig.hc_Γ_le
    exact Real.rpow_pos_of_pos (by positivity) _
  let c₀_use : ℝ := min (c₀_max / 2) (1 / (2 * (C₁ + 1)))
  have hc₀_use_pos : 0 < c₀_use := by positivity
  have hc₀_use_mem : c₀_use ∈ Ioo 0 c₀_max :=
    ⟨hc₀_use_pos, (min_le_left _ _).trans_lt (half_lt_self hc₀_max_pos)⟩
  let ρ_cap : ℝ := min dpConfig.ρ₀ (min r_φ (1 / (2 * (C₂ + 1))))
  have hρ_cap_pos : 0 < ρ_cap := by
    have := dpConfig.hρ₀_pos; positivity
  let c₀_P : ℝ := min (min (innerChartRadius / 2) (2 * chartBV D.r_1 ^ 2)) (min c₀_use
    ((ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1)) ^ 2))
  have hc₀_P_pos : 0 < c₀_P := by
    have := innerChartRadius_pos; have := kappaV_pos; have := chartBV_pos D.hr1_pos; positivity
  have hc₀_P_le_half : c₀_P ≤ innerChartRadius / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hc₀_P_le_V : c₀_P ≤ 2 * chartBV D.r_1 ^ 2 := (min_le_left _ _).trans (min_le_right _ _)
  let c_P : ℝ := max (max c_S4 c_S2) (max c_V (max (dpThr prob) (stirThr prob.w / dpConfig.c_Γ)))
  let C_mid_bd : ℝ := 2 * (2 * Real.sqrt 3 / xiStar) * max C_S4 C_S2 * P_Γ
  let C_P : ℝ := (innerCDxi * C_V * dpConfig.C_len / (2 * Real.pi)) * C_mid_bd + 1
  refine ⟨c_P, C_P, c₀_P, (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    ?_, hc₀_P_pos, hc₀_P_le_half, hc₀_P_le_V, ?_⟩
  · have := innerCDxi_pos; have := dpConfig.hC_len_pos; have := xiStar_pos; positivity
  intro c' hc' g hg hM_pos u hu hcut
  have hc'_S4 : c_S4 ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hc'_S2 : c_S2 ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hc'_V : c_V ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  have hc'_thr : dpThr prob ≤ c' :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  have hc'_10000 : 10000 ≤ c' := (dpThr_ge_10000 prob).trans hc'_thr
  have hc'_stir : stirThr prob.w / dpConfig.c_Γ ≤ c' :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hc'_24 : 24 ≤ c' := by linarith only [hc'_10000]
  have hc'_1000 : 1000 ≤ c' := by linarith only [hc'_10000]
  have hS4_bd := hS4 hc'_S4 hg
  have hhalf : ∀ w : ℂ, 0 ≤ w.im → w ∈ closedBall (0 : ℂ) (c₀_P * c' ^ (2 / 3 : ℝ)) →
      ¬ (w.im = 0 ∧ w.re ≤ 0) →
      ‖truncatedMellinPW prob c' dpT0 g w‖ ≤ C_P * c' ^ (1 / 3 : ℝ) * airyEnv w := by
    intro w hw_im hw_cb hw_cut
    have hw_ne : w ≠ 0 := fun h0 => hw_cut (by simp [h0])
    have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
    let a' : ℝ := Real.sqrt ‖w‖
    have ha'_pos : 0 < a' := Real.sqrt_pos.mpr hw_norm_pos
    have ha'_sq : a' ^ 2 = ‖w‖ := Real.sq_sqrt hw_norm_pos.le
    have hw_arg_lt : w.arg < Real.pi := by
      rcases lt_or_ge w.arg Real.pi with hlt | hge
      · exact hlt
      · exfalso
        have hpi : w.arg = Real.pi := le_antisymm (Complex.arg_le_pi w) hge
        have hp := Complex.arg_eq_pi_iff.mp hpi
        exact hw_cut ⟨hp.2, hp.1.le⟩
    have hw_arg_nn : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hw_im
    let φ : ℝ := (Real.pi - w.arg) / 2
    have hφ_pos : 0 < φ := by dsimp [φ]; linarith only [hw_arg_lt]
    have hφ_le : φ ≤ Real.pi / 2 := by dsimp [φ]; linarith only [hw_arg_nn]
    have hw_polar : w = ((a' ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * φ : ℝ) : ℂ)) := by
      have hp := (Complex.norm_mul_exp_arg_mul_I w).symm
      rw [← ha'_sq] at hp
      conv_lhs => rw [hp]
      congr 1; congr 1
      dsimp [φ]; push_cast; ring
    have ha'_le : a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) ≤ c₀_use := by
      rw [ha'_sq]
      have h1 : ‖w‖ ≤ c₀_P * c' ^ (2 / 3 : ℝ) := mem_closedBall_zero_iff.mp hw_cb
      have h2 : c₀_P ≤ c₀_use := (min_le_right _ _).trans (min_le_left _ _)
      calc ‖w‖ * c' ^ (-(2 / 3 : ℝ))
          ≤ (c₀_P * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by gcongr
        _ = c₀_P := by rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
        _ ≤ c₀_use := h2
    have hS6w := hS6_main c₀_use hc₀_use_mem c' a' φ hc'_pos ha'_pos.le hφ_pos.le hφ_le ha'_le
    dsimp only at hS6w
    rw [← hw_polar] at hS6w
    set z_w : ℂ := w * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
    set ζp : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * w ^ (1 / 2 : ℂ) * q_V z_w
    obtain ⟨_, hchartB_eq, hσp_nn, hτp_nn, hρ_rel, hσp_rel, _, _⟩ := hS6w
    have hb_eq_chartB : chartB ζp = virasoroBChart c' w :=
      hchartB_eq.trans (langerChartSpec_virasoro_bL_eq c' w)
    let ρ : ℝ := ‖ζp‖
    have hsqrt_le : Real.sqrt c₀_P ≤ ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1) := by
      have hc₀_sq : c₀_P ≤ (ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1)) ^ 2 :=
        (min_le_right _ _).trans (min_le_right _ _)
      calc Real.sqrt c₀_P ≤ Real.sqrt ((ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1)) ^ 2) :=
            Real.sqrt_le_sqrt hc₀_sq
        _ = ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1) :=
            Real.sqrt_sq (div_nonneg hρ_cap_pos.le (by have := kappaV_pos; positivity))
    have ha_sq2 : c' ^ (-(1 / 3 : ℝ)) * a' ≤ Real.sqrt c₀_P := by
      have hsq : (c' ^ (-(1 / 3 : ℝ)) * a') ^ 2 ≤ c₀_P := by
        rw [mul_pow, ← Real.rpow_natCast (c' ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hc'_pos.le]
        calc c' ^ (-(1 / 3 : ℝ) * (2 : ℕ)) * a' ^ 2 = a' ^ 2 * c' ^ (-(2 / 3 : ℝ)) := by
              push_cast; ring_nf
          _ ≤ c₀_P := by
              rw [ha'_sq]
              have h1' : ‖w‖ ≤ c₀_P * c' ^ (2 / 3 : ℝ) := mem_closedBall_zero_iff.mp hw_cb
              calc ‖w‖ * c' ^ (-(2 / 3 : ℝ))
                  ≤ (c₀_P * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by gcongr
                _ = c₀_P := by
                    rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
      exact Real.le_sqrt_of_sq_le hsq
    have hρ_half : ρ ≤ ρ_cap / 2 := by
      have h1 : ρ ≤ (1 + C₁ * c₀_use) * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a') := by
        have h_abs := (abs_le.mp hρ_rel).2
        change ρ - kappaV * c' ^ (-(1 / 3 : ℝ)) * a' ≤ _ at h_abs
        linarith only [h_abs]
      have hden2 : (1 + C₁ * c₀_use) * kappaV ≤ (2 * kappaV * (1 + C₁ * c₀_use) + 1) / 2 := by
        linarith only []
      calc ρ ≤ (1 + C₁ * c₀_use) * kappaV * (c' ^ (-(1 / 3 : ℝ)) * a') := by
            linarith only [h1]
        _ ≤ (1 + C₁ * c₀_use) * kappaV * (ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1)) := by
            gcongr; · have := kappaV_pos; positivity
            · exact ha_sq2.trans hsqrt_le
        _ ≤ ((2 * kappaV * (1 + C₁ * c₀_use) + 1) / 2) *
              (ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1)) :=
            mul_le_mul_of_nonneg_right hden2 (div_nonneg hρ_cap_pos.le (by have := kappaV_pos; positivity))
        _ = ρ_cap / 2 := by
            have hne : 2 * kappaV * (1 + C₁ * c₀_use) + 1 ≠ 0 := by have := kappaV_pos; positivity
            field_simp [hne]
    have hρ_ub : ρ ≤ ρ_cap := hρ_half.trans (half_le_self hρ_cap_pos.le)
    have hρ_le_ρ₀ : ρ ≤ dpConfig.ρ₀ := hρ_ub.trans (min_le_left _ _)
    have hρ_lt_rφ : ρ < r_φ :=
      hρ_half.trans_lt ((div_two_lt_of_pos hρ_cap_pos).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have hρ_pos : 0 < ρ := by
      have h_lo := (abs_le.mp hρ_rel).1
      change -(C₁ * c₀_use * (kappaV * c' ^ (-(1 / 3 : ℝ)) * a')) ≤
        ρ - kappaV * c' ^ (-(1 / 3 : ℝ)) * a' at h_lo
      have hc0_ub : C₁ * c₀_use ≤ 1 / 2 := by
        have h1 : c₀_use ≤ 1 / (2 * (C₁ + 1)) := min_le_right _ _
        have hne : C₁ + 1 ≠ 0 := by linarith only [hC₁]
        calc C₁ * c₀_use ≤ C₁ * (1 / (2 * (C₁ + 1))) := mul_le_mul_of_nonneg_left h1 hC₁
          _ = (C₁ / (C₁ + 1)) * (1 / 2) := by field_simp [hne]
          _ ≤ 1 * (1 / 2) := by
              gcongr; exact (div_le_one (by linarith only [hC₁])).mpr (by linarith only [])
          _ = 1 / 2 := one_mul _
      have hkap_pos : 0 < kappaV * c' ^ (-(1 / 3 : ℝ)) * a' := by have := kappaV_pos; positivity
      nlinarith only [h_lo, hc0_ub, hkap_pos]
    have hσp_pos : 0 < ζp.re := by
      have hρ_le_1 : ρ ≤ 1 := by
        have h1 : ρ_cap ≤ 1 / (2 * (C₂ + 1)) := (min_le_right _ _).trans (min_le_right _ _)
        have h2 : 1 / (2 * (C₂ + 1)) ≤ 1 := by
          rw [div_le_one (by linarith only [hC₂])]; linarith only [hC₂]
        exact hρ_ub.trans (h1.trans h2)
      have hC2_le : C₂ * ρ ^ 2 ≤ 1 / 2 := by
        have h1 : ρ ^ 2 ≤ ρ := by nlinarith only [hρ_pos, hρ_le_1]
        have h2 : ρ ≤ 1 / (2 * (C₂ + 1)) := hρ_ub.trans ((min_le_right _ _).trans (min_le_right _ _))
        have hne2 : C₂ + 1 ≠ 0 := by linarith only [hC₂]
        calc C₂ * ρ ^ 2 ≤ C₂ * ρ := mul_le_mul_of_nonneg_left h1 hC₂
          _ ≤ C₂ * (1 / (2 * (C₂ + 1))) := mul_le_mul_of_nonneg_left h2 hC₂
          _ = (C₂ / (C₂ + 1)) * (1 / 2) := by field_simp [hne2]
          _ ≤ 1 * (1 / 2) := by
              gcongr; exact (div_le_one (by linarith only [hC₂])).mpr (by linarith only [])
          _ = 1 / 2 := one_mul _
      have hsin_pos : 0 < Real.sin φ :=
        Real.sin_pos_of_pos_of_lt_pi hφ_pos (by linarith only [hφ_le, Real.pi_pos])
      have h_lo := (abs_le.mp hσp_rel).1
      change -(C₂ * ρ ^ 2 * (ρ * Real.sin φ)) ≤ ζp.re - ρ * Real.sin φ at h_lo
      have hprod_pos : 0 < ρ * Real.sin φ := mul_pos hρ_pos hsin_pos
      nlinarith only [h_lo, hC2_le, hprod_pos]
    let φ' : ℝ := Real.pi / 2 - ζp.arg
    have hζ_arg_nn : 0 ≤ ζp.arg := Complex.arg_nonneg_iff.mpr hτp_nn
    have hζ_arg_le : ζp.arg ≤ Real.pi / 2 := by
      have h_im_pos_or := eq_or_lt_of_le hτp_nn
      rcases h_im_pos_or with him0 | him_pos
      · have hzero : ζp.arg = 0 := Complex.arg_eq_zero_iff.mpr ⟨hσp_pos.le, him0.symm⟩
        rw [hzero]; positivity [Real.pi_pos]
      · exact (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hσp_pos)).le
    have hφ'_nn : 0 ≤ φ' := by dsimp [φ']; linarith only [hζ_arg_le]
    have hφ'_le : φ' ≤ Real.pi / 2 := by dsimp [φ']; linarith only [hζ_arg_nn]
    have hζp_polar : ζp = (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ)) := by
      have hp := (Complex.norm_mul_exp_arg_mul_I ζp).symm
      have harg_eq : Real.pi / 2 - φ' = ζp.arg := by dsimp [φ']; ring
      rw [harg_eq]
      simpa [ρ, mul_comm (ζp.arg : ℂ) Complex.I] using hp
    have hw_in : w ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
      have hin_pos := innerChartRadius_pos
      have h1 : c₀_P ≤ innerChartRadius :=
        hc₀_P_le_half.trans (by linarith only [hin_pos])
      exact closedBall_subset_closedBall (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hc'_pos.le _)) hw_cb
    have hw_in2 : w ∈ closedBall (0 : ℂ) (chartAC D.r_1 c' ^ 2) := by
      rw [chartAC_sq D.r_1 c' hc'_pos.le]
      refine closedBall_subset_closedBall ?_ hw_cb
      calc c₀_P * c' ^ (2 / 3 : ℝ) ≤ (2 * chartBV D.r_1 ^ 2) * c' ^ (2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right hc₀_P_le_V (Real.rpow_nonneg hc'_pos.le _)
        _ = _ := rfl
    obtain ⟨segs, hchain, hlen, hω_bd, hstrip, hnonstrip, hdeform⟩ :=
      truncatedMellinPW_deform prob hc'_thr hρ_pos.le hρ_le_ρ₀ hφ'_nn hφ'_le hg hw_in
    rw [← hζp_polar, hb_eq_chartB] at hstrip hnonstrip
    have hζp_ball : ζp ∈ ball (0 : ℂ) r_φ := by rwa [mem_ball_zero_iff]
    have hpot_saddle := (hφ_pot ζp hζp_ball hσp_pos).2
    rw [hb_eq_chartB] at hpot_saddle
    have hpot_u := virasoro_inner_potential_eq hc'_pos hw_in hw_cut
    have hc_phi_eq : c' * (chartPhiV ζp (virasoroBChart c' w)).re =
        -(4 / 3 : ℝ) * (w ^ (3 / 2 : ℂ)).re := by
      rw [hpot_saddle]; simpa [add_comm] using hpot_u
    have hair_eq : Real.exp (c' * (chartPhiV ζp (virasoroBChart c' w)).re) = airyEnv w := by
      rw [hc_phi_eq]; rfl
    set b := virasoroBChart c' w
    set t := virasoroDeltaChartC c' w
    have hbd_in := virasoroBChart_inner_bounds hc'_pos hw_in
    have hb_re_pos : 0 < b.re := lt_of_lt_of_le (half_pos xiStar_pos) hbd_in.2.2.1
    have ht_eq : t = (c' : ℂ) * b ^ 2 / 3 := virasoroDeltaChartC_eq_bChart_sq w
    have ht_norm_lb : c' * (xiStar / 2) ^ 2 / 3 ≤ ‖t‖ := by
      rw [ht_eq, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc'_pos.le,
        Complex.norm_ofNat]
      have h1 : xiStar / 2 ≤ ‖b‖ := hbd_in.2.2.1.trans (Complex.re_le_norm _)
      have h2 : (xiStar / 2) ^ 2 ≤ ‖b‖ ^ 2 :=
        pow_le_pow_left₀ (by have := xiStar_pos; positivity) h1 2
      gcongr
    have ht_half_ub : ‖t ^ (-(1 / 2 : ℂ))‖ ≤ (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)) := by
      have ht_pos : 0 < ‖t‖ := lt_of_lt_of_le (by have := xiStar_pos; positivity) ht_norm_lb
      have ht_ne : t ≠ 0 := norm_pos_iff.mp ht_pos
      have hnorm_cpow : ‖t ^ (-(1 / 2 : ℂ))‖ = ‖t‖ ^ (-(1 / 2 : ℝ)) := by
        rw [Complex.cpow_def_of_ne_zero ht_ne, Complex.norm_exp]
        have hre : (Complex.log t * (-(1 / 2 : ℂ))).re = -(1 / 2 : ℝ) * Real.log ‖t‖ := by
          have : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
          rw [this, mul_comm, Complex.re_ofReal_mul, Complex.log_re]
        rw [hre, Real.rpow_def_of_pos ht_pos]
        congr 1; ring
      rw [hnorm_cpow]
      have hbase_pos : 0 < c' * (xiStar / 2) ^ 2 / 3 := by have := xiStar_pos; positivity
      have hpow_le : ‖t‖ ^ (-(1 / 2 : ℝ)) ≤ (c' * (xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hbase_pos ht_norm_lb (by norm_num)
      have hrhs_eq : (c' * (xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) =
          (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)) := by
        have h1 : c' * (xiStar / 2) ^ 2 / 3 = c' * ((xiStar / 2) ^ 2 / 3) := by ring
        rw [h1, Real.mul_rpow hc'_pos.le (by positivity)]
        have h2 : ((xiStar / 2) ^ 2 / 3) ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt 3 / xiStar := by
          rw [Real.rpow_neg (by positivity), Real.div_rpow (by positivity) (by norm_num),
            ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity [xiStar_pos])]
          field_simp [xiStar_pos.ne']
        rw [h2, mul_comm]
      exact hpow_le.trans_eq hrhs_eq
    let M_int : ℝ := C_mid_bd * prob.cardyNorm (c' / 12) g *
      c' ^ (-(1 / 2 : ℝ)) * Real.exp (-(c' * (tipL b).re)) * airyEnv w
    have hM_int_nn : 0 ≤ M_int := by
      have := hM_pos.le; have := airyEnv_pos w; have := xiStar_pos
      dsimp [M_int, C_mid_bd]; positivity
    have hcont_seg : ∀ S ∈ segs,
        ContinuousOn (fun τ => mellinDensityIntegrandW prob.w c' g t (S.ω τ)) (Icc S.a S.b) := fun S hS => by
      intro τ hτ
      have hω_re_nn := (hω_bd S hS τ hτ).1
      have hz_re : 0 < ((prob.w : ℂ) / 2 + (c' : ℂ) * S.ω τ).re :=
        re_wHalf_add_mul_pos prob.hw hc'_pos.le hω_re_nn
      have hGam_d : DifferentiableAt ℂ Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * S.ω τ) :=
        Complex.differentiableAt_Gamma _ (fun m hm => by
          have hrm := congrArg Complex.re hm
          simp only [Complex.neg_re, Complex.natCast_re] at hrm
          linarith only [hz_re, hrm, Nat.cast_nonneg (α := ℝ) m])
      have h_an_w : DifferentiableAt ℂ (mellinDensityIntegrandW prob.w c' g t) (S.ω τ) := by
        have hm_d := (testClass_differentiable_mellinMGEntireW prob (max_one_le_of_dpThr_le prob hc'_thr) hg).differentiableAt
          (x := (prob.w : ℂ) / 2 + (c' : ℂ) * S.ω τ)
        have ht_ne : (2 * (Real.pi : ℂ) * t) ≠ 0 := by
          have htre : 0 < t.re := hbd_in.2.2.2.2.2
          have ht0 : t ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at htre; exact lt_irrefl 0 htre
          exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) ht0
        have hlin : DifferentiableAt ℂ (fun ω : ℂ => (prob.w : ℂ) / 2 + (c' : ℂ) * ω) (S.ω τ) := by fun_prop
        have hp_d : DifferentiableAt ℂ (fun ω : ℂ => (2 * (Real.pi : ℂ) * t) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ω))) (S.ω τ) := by
          have hex : (fun ω : ℂ => (2 * (Real.pi : ℂ) * t) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ω))) =
              fun ω => Complex.exp (Complex.log (2 * (Real.pi : ℂ) * t) * (-((prob.w : ℂ) / 2 + (c' : ℂ) * ω))) := by
            ext ω; rw [Complex.cpow_def_of_ne_zero ht_ne]
          rw [hex]; fun_prop
        have h1 := DifferentiableAt.comp (g := Complex.Gamma) (S.ω τ) hGam_d hlin
        have h2 := DifferentiableAt.comp (g := mellinMGEntireW prob.w g) (S.ω τ) hm_d hlin
        exact (h1.mul hp_d).mul h2
      exact (h_an_w.continuousAt.comp_continuousWithinAt (S.hω_cont τ hτ))
    have hpt_seg : ∀ S ∈ segs, ∀ τ ∈ Icc S.a S.b,
        ‖mellinDensityIntegrandW prob.w c' g t (S.ω τ)‖ ≤ M_int := fun S hS τ hτ => by
      have hω_re_nn := (hω_bd S hS τ hτ).1
      have hω_norm_lb := (hω_bd S hS τ hτ).2.1
      have hω_norm_ub := (hω_bd S hS τ hτ).2.2.1
      have hcω_stir : stirThr prob.w ≤ c' * ‖S.ω τ‖ := by
        calc stirThr prob.w ≤ c' * dpConfig.c_Γ := (div_le_iff₀ dpConfig.hc_Γ_pos).mp hc'_stir
          _ ≤ c' * ‖S.ω τ‖ := mul_le_mul_of_nonneg_left hω_norm_lb hc'_pos.le
      have hω_ne : S.ω τ ≠ 0 := by
        intro h0; rw [h0, norm_zero, mul_zero] at hcω_stir
        linarith only [hcω_stir, stirThr_pos prob.w]
      have hS_bd : ‖stirlingSW prob.w c' (S.ω τ)‖ ≤ 2 :=
        (norm_stirlingSW_le_two_of_stirThr_le prob.hw hc'_pos hω_re_nn hcω_stir).1
      have hpref : ‖stirlingPrefW prob.w (S.ω τ) b‖ ≤ P_Γ :=
        norm_stirlingPrefW_le prob.hw (half_pos xiStar_pos) hω_norm_ub
          (hbd_in.2.2.1.trans (Complex.re_le_norm _))
      have hb_arg : |b.arg| < Real.pi / 4 := (inner_chart_arg_lt hc'_pos hw_in).2.2
      have hP_nn : 0 ≤ P_Γ := hPΓ_pos.le
      have ht_half_nn : 0 ≤ (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)) := by
        have := xiStar_pos; positivity
      cases hstrip_b : S.isStrip
      · -- `S.isStrip = false`: use `lemma_S2_W` + `crudeExponentEc`
        obtain ⟨hμ₀_le, hEc_le⟩ := hnonstrip S hS hstrip_b τ hτ
        have hS2_bd := (hS2 hc'_S2 hμ₀_le hg).2
        have hmel_eq : mellinDensityIntegrandW prob.w c' g t (S.ω τ) =
            stirlingPrefW prob.w (S.ω τ) b * t ^ (-(1 / 2 : ℂ)) * stirlingSW prob.w c' (S.ω τ) *
              Complex.exp ((c' : ℂ) * ComplexBessel.stirlingJ (S.ω τ) b) *
              mellinMGW g ((prob.w : ℂ) / 2 + (c' : ℂ) * S.ω τ) := by
          have h1 := mellinDensityIntegrandW_crude_eq prob.hw hc'_pos g hω_re_nn hω_ne hb_re_pos hb_arg
          rw [← ht_eq] at h1
          exact h1
        rw [hmel_eq, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
        have hexp_ec : Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
            Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ)) ≤
            Real.exp (-(c' * (tipL b).re)) * airyEnv w := by
          rw [← hair_eq, ← Real.exp_add, ← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have hEc_def : crudeExponentEc (S.ω τ) b =
              ComplexBessel.crudeExponentB (S.ω τ) + (ComplexBessel.stirlingJ (S.ω τ) b).re +
                (tipL b).re := rfl
          have h1 : c' * crudeExponentEc (S.ω τ) b ≤ c' * (chartPhiV ζp b).re := by
            refine mul_le_mul_of_nonneg_left ?_ hc'_pos.le
            have hnn : 0 ≤ dpConfig.c_γ * ρ * ζp.re ^ 2 := by positivity [dpConfig.hc_γ_pos]
            linarith only [hEc_le, hnn]
          rw [hEc_def, mul_add, mul_add] at h1
          linarith only [h1]
        calc ‖stirlingPrefW prob.w (S.ω τ) b‖ * ‖t ^ (-(1 / 2 : ℂ))‖ * ‖stirlingSW prob.w c' (S.ω τ)‖ *
                Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
                ‖mellinMGW g ((prob.w : ℂ) / 2 + (c' : ℂ) * S.ω τ)‖
            ≤ P_Γ * ((2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ))) * 2 *
                Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
                (C_S2 * Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ)) *
                  prob.cardyNorm (c' / 12) g) := by
              have := xiStar_pos; gcongr
          _ = 2 * (2 * Real.sqrt 3 / xiStar) * C_S2 * P_Γ * prob.cardyNorm (c' / 12) g *
                c' ^ (-(1 / 2 : ℝ)) *
                (Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
                  Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ))) := by ring
          _ ≤ C_mid_bd * prob.cardyNorm (c' / 12) g *
                c' ^ (-(1 / 2 : ℝ)) * (Real.exp (-(c' * (tipL b).re)) * airyEnv w) := by
              dsimp only [C_mid_bd]
              have hCS_le : C_S2 ≤ max C_S4 C_S2 := le_max_right _ _
              have := xiStar_pos; have := hM_pos.le
              gcongr
          _ = M_int := by dsimp [M_int]; ring
      · -- `S.isStrip = true`: use `lemma_S4_W` + `(chartPhiV (S.ζ τ) b).re ≤ (chartPhiV ζp b).re`
        obtain ⟨_, hΦ_le⟩ := hstrip S hS hstrip_b τ hτ
        have hζ_data := S.hζ_strip hstrip_b τ hτ
        have hζ_cl : S.ζ τ ∈ stripClosed := ⟨hζ_data.1, hζ_data.2.1.trans (by norm_num)⟩
        have hω_eq_ζ : S.ω τ = chartOmega (S.ζ τ) := hζ_data.2.2.1
        have hWV_bd := hS4_bd.2.2.2 (S.ζ τ) hζ_cl
        have hmel_eq : mellinDensityIntegrandW prob.w c' g t (S.ω τ) =
            stirlingPrefW prob.w (S.ω τ) b * t ^ (-(1 / 2 : ℂ)) * stirlingSW prob.w c' (S.ω τ) *
              Complex.exp ((c' : ℂ) * chartPhiV (S.ζ τ) b - (c' : ℂ) * tipL b) *
              tildeWW prob.w c' g (S.ζ τ) := by
          have hre' : 0 ≤ (chartOmega (S.ζ τ)).re := hω_eq_ζ ▸ hω_re_nn
          have hne' : chartOmega (S.ζ τ) ≠ 0 := hω_eq_ζ ▸ hω_ne
          have h1 := mellinDensityIntegrandW_strip_eq prob.hw hc'_pos g hre' hne' hb_re_pos hb_arg
          rw [← ht_eq, ← hω_eq_ζ] at h1
          exact h1
        rw [hmel_eq, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp]
        have hre_exp : ((c' : ℂ) * chartPhiV (S.ζ τ) b - (c' : ℂ) * tipL b).re =
            c' * (chartPhiV (S.ζ τ) b).re - c' * (tipL b).re := by
          simp only [Complex.sub_re, Complex.re_ofReal_mul]
        rw [hre_exp]
        have hexp_le : Real.exp (c' * (chartPhiV (S.ζ τ) b).re - c' * (tipL b).re) ≤
            Real.exp (-(c' * (tipL b).re)) * airyEnv w := by
          rw [← hair_eq, ← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have h1 : c' * (chartPhiV (S.ζ τ) b).re ≤ c' * (chartPhiV ζp b).re :=
            mul_le_mul_of_nonneg_left hΦ_le hc'_pos.le
          linarith only [h1]
        calc ‖stirlingPrefW prob.w (S.ω τ) b‖ * ‖t ^ (-(1 / 2 : ℂ))‖ * ‖stirlingSW prob.w c' (S.ω τ)‖ *
                Real.exp (c' * (chartPhiV (S.ζ τ) b).re - c' * (tipL b).re) *
                ‖tildeWW prob.w c' g (S.ζ τ)‖
            ≤ P_Γ * ((2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ))) * 2 *
                (Real.exp (-(c' * (tipL b).re)) * airyEnv w) *
                (C_S4 * prob.cardyNorm (c' / 12) g) := by
              have := xiStar_pos; have := airyEnv_pos w; gcongr
          _ = 2 * (2 * Real.sqrt 3 / xiStar) * C_S4 * P_Γ * prob.cardyNorm (c' / 12) g *
                c' ^ (-(1 / 2 : ℝ)) * Real.exp (-(c' * (tipL b).re)) * airyEnv w := by ring
          _ ≤ M_int := by
              have hCS_le : C_S4 ≤ max C_S4 C_S2 := le_max_left _ _
              have := xiStar_pos; have := hM_pos.le; have := airyEnv_pos w
              dsimp only [M_int, C_mid_bd]
              gcongr
    have hint_bd := norm_contourIntegral_leW (mellinDensityIntegrandW prob.w c' g t) segs M_int hM_int_nn
      hcont_seg hpt_seg
    have hV_bd := hV_fn hc'_V hw_in2
    have hd_bd := virasoroDeltaChartC_inner_deriv_bound hc'_pos hw_in
    rw [hdeform, norm_mul, norm_mul, norm_mul, norm_neg, norm_div, norm_div]
    have hM_norm : ‖(prob.cardyNorm (c' / 12) g : ℂ)‖ =
        prob.cardyNorm (c' / 12) g := by
      rw [Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
    have hc_2pi : ‖(c' : ℂ)‖ / ‖2 * (Real.pi : ℂ) * Complex.I‖ = c' / (2 * Real.pi) := by
      rw [Complex.norm_real, Real.norm_of_nonneg hc'_pos.le, norm_mul, norm_mul,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
        Complex.norm_I, mul_one]
    rw [hM_norm, hc_2pi]
    have hexp_cancel : Real.exp (c' * (tipL b).re) * Real.exp (-(c' * (tipL b).re)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hc_pow_eq : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ)) =
        c' ^ (1 / 3 : ℝ) := by
      calc c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ))
          = c' ^ (1 / 3 : ℝ) * (c' * (c' ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ)))) := by ring
        _ = c' ^ (1 / 3 : ℝ) * (c' * c' ^ (-1 : ℝ)) := by
            rw [← Real.rpow_add hc'_pos]; norm_num
        _ = c' ^ (1 / 3 : ℝ) * 1 := by
            rw [Real.rpow_neg_one, mul_inv_cancel₀ hc'_pos.ne']
        _ = c' ^ (1 / 3 : ℝ) := mul_one _
    have hhint : ‖contourIntegral (mellinDensityIntegrandW prob.w c' g t) segs‖ ≤ M_int * dpConfig.C_len :=
      hint_bd.trans (mul_le_mul_of_nonneg_left hlen hM_int_nn)
    calc (‖deriv (virasoroDeltaChartC c') w‖ / prob.cardyNorm (c' / 12) g) *
            ‖cardyVC prob (c' / 12) t‖ * (c' / (2 * Real.pi)) *
            ‖contourIntegral (mellinDensityIntegrandW prob.w c' g t) segs‖
        ≤ ((innerCDxi * c' ^ (1 / 3 : ℝ)) / prob.cardyNorm (c' / 12) g) *
            (C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (tipL b).re)) *
            (c' / (2 * Real.pi)) * (M_int * dpConfig.C_len) := by
          have := innerCDxi_pos; have := hCV_pos
          gcongr
      _ = (innerCDxi * C_V * dpConfig.C_len / (2 * Real.pi)) * C_mid_bd *
            (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * c' * c' ^ (-(1 / 2 : ℝ))) *
            (Real.exp (c' * (tipL b).re) * Real.exp (-(c' * (tipL b).re))) * airyEnv w := by
          dsimp [M_int]
          field_simp [hM_pos.ne', Real.pi_pos.ne']
      _ = (innerCDxi * C_V * dpConfig.C_len / (2 * Real.pi)) * C_mid_bd *
            c' ^ (1 / 3 : ℝ) * airyEnv w := by
          rw [hc_pow_eq, hexp_cancel, mul_one]
      _ ≤ C_P * c' ^ (1 / 3 : ℝ) * airyEnv w := by
          have hair_nn := (airyEnv_pos w).le
          have hc13_nn := Real.rpow_nonneg hc'_pos.le (1 / 3 : ℝ)
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hc13_nn) hair_nn
          dsimp [C_P]; linarith only []
  rcases le_or_gt 0 u.im with him_nn | him_neg
  · exact hhalf u him_nn hu hcut
  · have hu_c : starRingEnd ℂ u ∈ closedBall (0 : ℂ) (c₀_P * c' ^ (2 / 3 : ℝ)) := by
      simpa [mem_closedBall_zero_iff, Complex.norm_conj] using hu
    have hu_in_ball : u ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
      have h1 : c₀_P * c' ^ (2 / 3 : ℝ) < innerChartRadius * c' ^ (2 / 3 : ℝ) :=
        mul_lt_mul_of_pos_right (hc₀_P_le_half.trans_lt (half_lt_self innerChartRadius_pos))
          (Real.rpow_pos_of_pos hc'_pos _)
      exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hu).trans_lt h1)
    have hc_cut : ¬ ((starRingEnd ℂ u).im = 0 ∧ (starRingEnd ℂ u).re ≤ 0) := by
      intro ⟨him0, _⟩; simp at him0; linarith only [him0, him_neg]
    have hbd_c := hhalf (starRingEnd ℂ u) (by simp; linarith only [him_neg]) hu_c hc_cut
    rw [truncatedMellinPW_conj prob hc'_thr dpT0 hg hu_in_ball, Complex.norm_conj, airyEnv_conjW] at hbd_c
    exact hbd_c

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.truncatedMellinPW_inner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms truncatedMellinPW_inner_bound

end FormalResearch.ModularBootstrap.FixedWeightBand
