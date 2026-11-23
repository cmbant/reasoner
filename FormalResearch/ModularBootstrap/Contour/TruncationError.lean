module

public import FormalResearch.ModularBootstrap.Contour.InnerTipBounds
public import FormalResearch.ModularBootstrap.ChartGeometry.MidlineAndJunction
public import FormalResearch.ModularBootstrap.PoissonJensen.HalfPlaneJensen
public import FormalResearch.ModularBootstrap.StripMultiplier.LemmaS4
public import FormalResearch.ModularBootstrap.Mellin.MellinConvergence
public import FormalResearch.ModularBootstrap.Mellin.HankelMellin
public import FormalResearch.ModularBootstrap.TipFront.ConcreteBlowup
public import Mathlib.Analysis.MellinInversion

/-!
# Truncated Mellin Density and Lemma D' (`lower_o1_two_edge.tex`, `vlo:Dp`)

Formalizes **Lemma D'** (`vlo:Dp`, `lower_o1_two_edge.tex`, lines 731–760):

* `dpConfig`, `dpT0`: fixed `ZPConfig` witness from `lemma_Zp` and its cutoff `T₀ ≥ 4`.
* `mellinDensityIntegrand` and `truncatedMellinP`: the truncated Mellin density
  `P(ũ) = (-Δ'(ũ) / M[g]) V(Δ(ũ)) (c' / (2πi)) ∫_{ω(1/2 + iT₀)}^{ω(1/2 - iT₀)} Γ(z)(2π t)^{-z} m_g(z) dω`.
* `truncatedMellinP_analyticOnNhd` and `truncatedMellinP_conj`: holomorphy and conjugation
  symmetry on `ball 0 (innerChartRadius * c'^(2/3))`.
* `mellin_inversion_real` and `truncatedMellinP_real_err`: Fourier–Mellin inversion on `ℝ_{>0}` and
  exponential truncation error along the real chart diameter `|x| ≤ c₀ * c'^(2/3)`.
* `truncatedMellinP_deform` and `truncatedMellinP_inner_bound`: contour deformation of `P(ũ)` onto
  the `lemma_Zp` saddle contour, yielding `‖P(ũ)‖ ≤ C_P c'^{1/3} airyEnv ũ` on
  `closedBall 0 (c₀ * c'^(2/3)) \ (-∞, 0]`.
* `lemma_Dp`: half-plane Poisson–Jensen argument via `z ↦ U₀ (z^{1/2} - 1)/(z^{1/2} + 1)`, proving
  `‖Ψ̃(ũ) - P(ũ)‖ ≤ C_D exp(-d_D c')` on `closedBall 0 (c₀_D * c'^(2/3))`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval FourierTransform

namespace FormalResearch.ModularBootstrap.Contour

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

/-! ### 1. Fixed saddle-contour configuration and `truncatedMellinP` -/

/-- Canonical `ZPConfig` extracted from `lemma_Zp`. -/
noncomputable def dpConfig : ZPConfig := Classical.choose lemma_Zp

lemma dpConfig_spec :
    ∀ {ρ φ' : ℝ}, 0 ≤ ρ → ρ ≤ dpConfig.ρ₀ → 0 ≤ φ' → φ' ≤ Real.pi / 2 →
      let s : ℂ := (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 - φ' : ℝ) : ℂ))
      let b : ℂ := chartB s
      b.im ≤ 0 ∧ xiStar / 2 ≤ b.re ∧ ‖b‖ ≤ 2 * xiStar ∧
      ∃ segs : List ContourSeg,
        ContourChained (chartOmega ((1 / 2 : ℂ) + Complex.I * (dpConfig.T₀ : ℂ)))
          (chartOmega ((1 / 2 : ℂ) - Complex.I * (dpConfig.T₀ : ℂ))) segs ∧
        contourLength segs ≤ dpConfig.C_len ∧
        (∀ S ∈ segs, ∀ t ∈ Icc S.a S.b,
          0 ≤ (S.ω t).re ∧ dpConfig.c_Γ ≤ ‖S.ω t‖ ∧
            ‖S.ω t‖ ≤ dpConfig.C_Γ ∧ ‖S.ω' t‖ ≤ dpConfig.C_d) ∧
        (∀ S ∈ segs, S.isStrip = true → ∀ t ∈ Icc S.a S.b,
          ‖S.ζ' t‖ ≤ dpConfig.C_d ∧ (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re) ∧
        (∀ S ∈ segs, S.isStrip = true → S.kind = .upperRay →
          ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
            ∀ t ∈ Icc 0 t_max, ‖S.ζ t - s‖ = t_max - t ∧ ‖S.ζ' t‖ = 1 ∧
              (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - dpConfig.c_γ * ρ * (t_max - t) ^ 2) ∧
        (∀ S ∈ segs, S.isStrip = true → S.kind = .lowerRay →
          ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
            ∀ t ∈ Icc 0 t_max, ‖S.ζ t - s‖ = t ∧ ‖S.ζ' t‖ = 1 ∧
              (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - dpConfig.c_γ * ρ * t ^ 2) ∧
        (∀ S ∈ segs, S.isStrip = true → S.kind = .arcRadial →
          ∀ t ∈ Icc S.a S.b, (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - dpConfig.κ_arc * ρ ^ 3) ∧
        (∀ S ∈ segs, S.isStrip = true → S.kind = .fixedStrip →
          ∀ t ∈ Icc S.a S.b, (chartPhiV (S.ζ t) b).re ≤ (chartPhiV s b).re - dpConfig.κ_strip) ∧
        (∀ S ∈ segs, S.isStrip = false →
          ∀ t ∈ Icc S.a S.b,
            dpConfig.μ₀ ≤ (S.ω t).re ∧
              crudeExponentEc (S.ω t) b ≤ (chartPhiV s b).re - dpConfig.c_γ * ρ * s.re ^ 2) ∧
        segs.length ≤ 12 ∧
        (∀ S ∈ segs, S.b - S.a ≤ 1) ∧
        (∀ S ∈ segs, S.isStrip = true → S.kind ≠ .crudeEdge) :=
  Classical.choose_spec lemma_Zp

/-- Fixed midline truncation cutoff `T₀ ≥ 4` shared by `Lemma D'` and `Lemma Z`. -/
noncomputable def dpT0 : ℝ := dpConfig.T₀

lemma dpT0_ge_four : 4 ≤ dpT0 := dpConfig.hT₀_ge

/-- Mellin integrand `ω ↦ Γ(1/2 + c' ω) (2π t)^{-(1/2 + c' ω)} m_g(1/2 + c' ω)`. -/
noncomputable def mellinDensityIntegrand (c' : ℝ) (g : ℝ → ℝ) (t ω : ℂ) : ℂ :=
  let z : ℂ := 1 / 2 + (c' : ℂ) * ω
  Complex.Gamma z * (2 * (Real.pi : ℂ) * t) ^ (-z) * mellinMGEntire g z

/-- Truncated Mellin density `P(ũ)` on the inner chart disc (`lower_o1_two_edge.tex`, Lemma D' `vlo:Dp`):
`P(ũ) = (-Δ'(ũ) / M[g]) V_C(c', Δ(ũ)) (c' / (2πi)) ∫_{ω(1/2 + iT₀)}^{ω(1/2 - iT₀)} Γ(z)(2π t)^{-z} m_g(z) dω`. -/
noncomputable def truncatedMellinP (c' T₀ : ℝ) (g : ℝ → ℝ) (u : ℂ) : ℂ :=
  let M : ℂ := (virasoroProblem.cardyNorm (c' / 12) g : ℂ);
  let t : ℂ := virasoroDeltaChartC c' u;
  let ω₀ : ℂ := chartOmega ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ));
  let ω₁ : ℂ := chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ));
  -(deriv (virasoroDeltaChartC c') u / M) * V_C (c' : ℂ) t *
    ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
    ∫ s in (0 : ℝ)..(1 : ℝ),
      mellinDensityIntegrand c' g t ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)

/-! ### 2. Analyticity, conjugation symmetry, and inner-disc chart Lipschitz bounds -/

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

lemma virasoroBChart_inner_conj {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    virasoroBChart c' (starRingEnd ℂ u) = starRingEnd ℂ (virasoroBChart c' u) := by
  have hr_pos : 0 < innerChartRadius * c' ^ (2 / 3 : ℝ) :=
    mul_pos innerChartRadius_pos (Real.rpow_pos_of_pos hc' _)
  have hac_pos : 0 < virasoroAC c' ^ 2 := sq_pos_of_pos (virasoroAC_pos hc')
  let δ : ℝ := min (innerChartRadius * c' ^ (2 / 3 : ℝ)) (virasoroAC c' ^ 2)
  have hδ_pos : 0 < δ := lt_min hr_pos hac_pos
  have hsub : ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) ⊆
      ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) := by
    apply ball_subset_ball
    gcongr
    exact innerChartRadius_lt_open_cap.le.trans chartParams.hr_open_cap_lt_u.le
  refine holomorphic_conj_eq_of_real_nhds hr_pos hδ_pos (min_le_left _ _)
    ((virasoroBChart_analyticOnNhd hc').mono hsub) (fun x hx => ?_) u hu
  have hx_ac : |x| ≤ virasoroAC c' ^ 2 := hx.le.trans (min_le_right _ _)
  exact (virasoroBChart_ofReal hc' hx_ac).1

lemma virasoroDeltaChartC_inner_conj {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    virasoroDeltaChartC c' (starRingEnd ℂ u) = starRingEnd ℂ (virasoroDeltaChartC c' u) := by
  rw [virasoroDeltaChartC_eq_bChart_sq, virasoroDeltaChartC_eq_bChart_sq,
    virasoroBChart_inner_conj hc' hu]
  simp only [map_div₀, map_mul, map_pow, Complex.conj_ofReal, map_ofNat]

lemma virasoroPsiTilde_inner_conj {c' : ℝ} (hc' : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    virasoroPsiTilde c' g (starRingEnd ℂ u) = starRingEnd ℂ (virasoroPsiTilde c' g u) := by
  have hc'_pos : 0 < c' := by linarith
  have hr_pos : 0 < innerChartRadius * c' ^ (2 / 3 : ℝ) :=
    mul_pos innerChartRadius_pos (Real.rpow_pos_of_pos hc'_pos _)
  have hac_pos : 0 < virasoroAC c' ^ 2 := sq_pos_of_pos (virasoroAC_pos hc'_pos)
  let δ : ℝ := min (innerChartRadius * c' ^ (2 / 3 : ℝ)) (virasoroAC c' ^ 2)
  have hsub : ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) ⊆ virasoroPsiDom c' := fun w hw => by
    have hb := virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hw)
    exact ⟨hb.1, hb.2.2.2.2.1⟩
  refine holomorphic_conj_eq_of_real_nhds hr_pos (lt_min hr_pos hac_pos) (min_le_left _ _)
    ((virasoroPsiTilde_analyticOnNhd hc' hg).mono hsub) (fun x hx => ?_) u hu
  exact virasoroPsiTilde_im_ofReal hc'_pos hg (hx.le.trans (min_le_right _ _))

lemma virasoroBChart_inner_real {c' : ℝ} (hc' : 0 < c') {x : ℝ}
    (hx : |x| ≤ innerChartRadius * c' ^ (2 / 3 : ℝ)) :
    (virasoroBChart c' (x : ℂ)).im = 0 ∧ xiStar / 2 ≤ (virasoroBChart c' (x : ℂ)).re ∧
    0 < (virasoroDeltaChartC c' (x : ℂ)).re ∧ (virasoroDeltaChartC c' (x : ℂ)).im = 0 := by
  have hx_cb : (x : ℂ) ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx
  have hbd := virasoroBChart_inner_bounds hc' hx_cb
  have him : (virasoroBChart c' (x : ℂ)).im = 0 := by
    have hr_pos : 0 < innerChartRadius * c' ^ (2 / 3 : ℝ) :=
      mul_pos innerChartRadius_pos (Real.rpow_pos_of_pos hc' _)
    have hb_conj : ContinuousOn (fun w => virasoroBChart c' (starRingEnd ℂ w) -
        starRingEnd ℂ (virasoroBChart c' w))
        (closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) := by
      have hopen : closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) ⊆
          ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) := by
        apply closedBall_subset_ball
        exact mul_lt_mul_of_pos_right
          (innerChartRadius_lt_open_cap.trans chartParams.hr_open_cap_lt_u)
          (Real.rpow_pos_of_pos hc' _)
      have hc1 : ContinuousOn (virasoroBChart c')
          (closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :=
        ((virasoroBChart_analyticOnNhd hc').mono hopen).continuousOn
      have hmap : MapsTo (starRingEnd ℂ)
          (closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)))
          (closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) := fun w hw => by
        simpa [mem_closedBall_zero_iff, Complex.norm_conj] using hw
      exact (hc1.comp Complex.continuous_conj.continuousOn hmap).sub
        (Complex.continuous_conj.comp_continuousOn hc1)
    have h0_seq : ∀ w ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)),
        virasoroBChart c' (starRingEnd ℂ w) - starRingEnd ℂ (virasoroBChart c' w) = 0 := fun w hw =>
      sub_eq_zero.mpr (virasoroBChart_inner_conj hc' hw)
    have hx_eq : virasoroBChart c' (starRingEnd ℂ (x : ℂ)) -
        starRingEnd ℂ (virasoroBChart c' (x : ℂ)) = 0 := by
      rcases eq_or_lt_of_le hx with heq | hlt
      · let f : ℝ → ℂ := fun t => virasoroBChart c' (starRingEnd ℂ ((t : ℝ) : ℂ)) -
          starRingEnd ℂ (virasoroBChart c' ((t : ℝ) : ℂ))
        have ht_tend : Tendsto (fun n : ℕ => ((1 - 1 / ((n : ℝ) + 2)) * x : ℝ)) atTop (𝓝 x) := by
          have h0 : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 1) := by
            have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
              tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
            simpa using tendsto_const_nhds.sub h1
          simpa using h0.mul_const x
        have hmem_cb : ∀ n : ℕ, (((1 - 1 / ((n : ℝ) + 2)) * x : ℝ) : ℂ) ∈
            closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := fun n => by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_mul]
          have h12 : 0 ≤ 1 - 1 / ((n : ℝ) + 2) := by
            have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
            linarith
          have hlt1 : 1 - 1 / ((n : ℝ) + 2) ≤ 1 := by
            have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
            linarith
          calc |1 - 1 / ((n : ℝ) + 2)| * |x| = (1 - 1 / ((n : ℝ) + 2)) * |x| := by
                rw [abs_of_nonneg h12]
            _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right hlt1 (abs_nonneg x)
            _ = |x| := one_mul _
            _ ≤ innerChartRadius * c' ^ (2 / 3 : ℝ) := hx
        have hmem_b : ∀ n : ℕ, (((1 - 1 / ((n : ℝ) + 2)) * x : ℝ) : ℂ) ∈
            ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := fun n => by
          rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_mul]
          have h12 : 0 ≤ 1 - 1 / ((n : ℝ) + 2) := by
            have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
            linarith
          have hlt1 : 1 - 1 / ((n : ℝ) + 2) < 1 := by
            have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
            linarith
          have hx_pos : 0 < |x| := by rw [heq]; exact hr_pos
          calc |1 - 1 / ((n : ℝ) + 2)| * |x| = (1 - 1 / ((n : ℝ) + 2)) * |x| := by
                rw [abs_of_nonneg h12]
            _ < 1 * |x| := mul_lt_mul_of_pos_right hlt1 hx_pos
            _ = |x| := one_mul _
            _ = innerChartRadius * c' ^ (2 / 3 : ℝ) := heq
        have ht_lim : Tendsto (fun n : ℕ =>
            virasoroBChart c' (starRingEnd ℂ (((1 - 1 / ((n : ℝ) + 2)) * x : ℝ) : ℂ)) -
              starRingEnd ℂ (virasoroBChart c' (((1 - 1 / ((n : ℝ) + 2)) * x : ℝ) : ℂ)))
            atTop (𝓝 (virasoroBChart c' (starRingEnd ℂ (x : ℂ)) -
              starRingEnd ℂ (virasoroBChart c' (x : ℂ)))) := by
          refine (hb_conj _ hx_cb).tendsto.comp ?_
          exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (Complex.continuous_ofReal.continuousAt.tendsto.comp ht_tend)
            (Eventually.of_forall hmem_cb)
        exact tendsto_nhds_unique (ht_lim.congr (fun n => h0_seq _ (hmem_b n))) tendsto_const_nhds
      · exact h0_seq (x : ℂ) (by rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hlt)
    have hconj_eq : virasoroBChart c' (x : ℂ) = starRingEnd ℂ (virasoroBChart c' (x : ℂ)) := by
      have h1 := sub_eq_zero.mp hx_eq
      simpa [Complex.conj_ofReal] using h1
    exact Complex.conj_eq_iff_im.mp hconj_eq.symm
  have hΔ_im : (virasoroDeltaChartC c' (x : ℂ)).im = 0 := by
    have hb_eq : virasoroBChart c' (x : ℂ) = ((virasoroBChart c' (x : ℂ)).re : ℂ) :=
      Complex.ext rfl him
    rw [virasoroDeltaChartC_eq_bChart_sq, hb_eq]
    have hre : (c' : ℂ) * ((virasoroBChart c' (x : ℂ)).re : ℂ) ^ 2 / 3 =
        (((c' * (virasoroBChart c' (x : ℂ)).re ^ 2 / 3 : ℝ) : ℂ)) := by push_cast; ring
    rw [hre, Complex.ofReal_im]
  exact ⟨him, hbd.2.2.1, hbd.2.2.2.2.2, hΔ_im⟩

lemma virasoroBChart_inner_lip {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤
      ((3 / xiStar) * innerCDxi) * (‖u‖ * c' ^ (-(2 / 3 : ℝ))) := by
  let R := innerChartRadius * c' ^ (2 / 3 : ℝ)
  have hdiff : ∀ w ∈ closedBall (0 : ℂ) R, DifferentiableAt ℂ (virasoroBChart c') w := fun w hw =>
    ((virasoroBChart_analyticOnNhd hc') w (virasoroBChart_inner_bounds hc' hw).1).differentiableAt
  have hder_bd : ∀ w ∈ closedBall (0 : ℂ) R,
      ‖deriv (virasoroBChart c') w‖ ≤ ((3 / xiStar) * innerCDxi) * tipEps c' := fun w hw => by
    have hε_pos : 0 < tipEps c' := tipEps_pos hc'
    have h1 : ‖deriv (virasoroBChart c') w / ((tipEps c' : ℝ) : ℂ)‖ ≤ (3 / xiStar) * innerCDxi := by
      have hb_lb := (virasoroBChart_inner_bounds hc' hw).2.2.1
      have hb_norm_lb : xiStar / 2 ≤ ‖virasoroBChart c' w‖ := hb_lb.trans (Complex.re_le_norm _)
      have hb_pos : 0 < ‖virasoroBChart c' w‖ := lt_of_lt_of_le (div_pos xiStar_pos two_pos) hb_norm_lb
      have hb_ne : virasoroBChart c' w ≠ 0 := norm_pos_iff.mp hb_pos
      have hw_open := (virasoroBChart_inner_bounds hc' hw).1
      have h23_ne : ((2 * c' / 3 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      have hb_an : AnalyticAt ℂ (virasoroBChart c') w := virasoroBChart_analyticOnNhd hc' w hw_open
      have hsq : HasDerivAt (fun z => ((c' : ℂ) / 3) * virasoroBChart c' z ^ 2)
          (((c' : ℂ) / 3) * ((2 : ℂ) * virasoroBChart c' w ^ (2 - 1) * deriv (virasoroBChart c') w)) w :=
        (hb_an.differentiableAt.hasDerivAt.pow 2).const_mul ((c' : ℂ) / 3)
      have heq_f : (fun z => ((c' : ℂ) / 3) * virasoroBChart c' z ^ 2) = virasoroDeltaChartC c' := by
        ext z; rw [virasoroDeltaChartC_eq_bChart_sq]; ring
      rw [heq_f] at hsq
      have hdΔ_eq : deriv (virasoroDeltaChartC c') w =
          ((2 * c' / 3 : ℝ) : ℂ) * virasoroBChart c' w * deriv (virasoroBChart c') w := by
        rw [hsq.deriv]; simp only [Nat.reduceSub, pow_one]; push_cast; ring
      have hdB_eq : deriv (virasoroBChart c') w =
          deriv (virasoroDeltaChartC c') w / (((2 * c' / 3 : ℝ) : ℂ) * virasoroBChart c' w) := by
        rw [hdΔ_eq]; field_simp [h23_ne, hb_ne]
      have hdΔ_bd := virasoroDeltaChartC_inner_deriv_bound hc' hw
      have hprod_norm : ‖((2 * c' / 3 : ℝ) : ℂ) * virasoroBChart c' w‖ =
          (2 * c' / 3) * ‖virasoroBChart c' w‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hε_eq : tipEps c' * (2 * c' / 3) = (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) := by
        unfold tipEps
        calc c' ^ (-(2 / 3 : ℝ)) * (2 * c' / 3)
            = (2 / 3 : ℝ) * (c' * c' ^ (-(2 / 3 : ℝ))) := by ring
          _ = (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) := by
              rw [← Real.rpow_one_add' hc'.le (by norm_num : (1 : ℝ) + -(2 / 3 : ℝ) ≠ 0)]; norm_num
      rw [hdB_eq, div_div, norm_div, norm_mul, hprod_norm]
      have hdenom_eq : (2 * c' / 3) * ‖virasoroBChart c' w‖ * ‖((tipEps c' : ℝ) : ℂ)‖ =
          (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖virasoroBChart c' w‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hε_pos.le]
        calc (2 * c' / 3) * ‖virasoroBChart c' w‖ * tipEps c'
            = (tipEps c' * (2 * c' / 3)) * ‖virasoroBChart c' w‖ := by ring
          _ = (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖virasoroBChart c' w‖ := by rw [hε_eq]
      rw [hdenom_eq]
      have hc13_pos : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc' _
      have := innerCDxi_pos; have := xiStar_pos
      calc ‖deriv (virasoroDeltaChartC c') w‖ /
              ((2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖virasoroBChart c' w‖)
          ≤ (innerCDxi * c' ^ (1 / 3 : ℝ)) /
              ((2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * (xiStar / 2)) := by gcongr
        _ = (3 / xiStar) * innerCDxi := by field_simp [hc13_pos.ne', xiStar_pos.ne']
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hε_pos.le, div_le_iff₀ hε_pos] at h1
    exact h1
  have hmvt := (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => hdiff w (closedBall_subset_closedBall (by simp) hw))
    (fun w hw => hder_bd w (closedBall_subset_closedBall (by simp) hw))
    (mem_closedBall_self (mul_nonneg innerChartRadius_pos.le (Real.rpow_nonneg hc'.le _)))
    hu
  have hmvt2 : ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤
      ((3 / xiStar) * innerCDxi) * tipEps c' * ‖u‖ := by
    have h0 : virasoroBChart c' 0 = (xiStar : ℂ) := by
      unfold virasoroBChart virasoroXiChartC virasoroBOfXi
      simp only [zero_mul, virasoroXiInf_zero]
      have h3 : (3 : ℂ) * (xiBar : ℂ) = ((xiStar : ℝ) : ℂ) ^ 2 := by
        unfold xiBar; push_cast; ring
      rw [h3, Complex.cpow_def_of_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr xiStar_pos.ne'))]
      rw [show Complex.log ((xiStar : ℂ) ^ 2) = ((2 * Real.log xiStar : ℝ) : ℂ) by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_log (sq_nonneg xiStar), Real.log_pow]; push_cast; ring]
      rw [show ((2 * Real.log xiStar : ℝ) : ℂ) * (1 / 2 : ℂ) = ((Real.log xiStar : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp, Real.exp_log xiStar_pos]
    rw [h0, sub_zero] at hmvt
    exact hmvt
  calc ‖virasoroBChart c' u - (xiStar : ℂ)‖
      ≤ ((3 / xiStar) * innerCDxi) * tipEps c' * ‖u‖ := hmvt2
    _ = ((3 / xiStar) * innerCDxi) * (‖u‖ * c' ^ (-(2 / 3 : ℝ))) := by
        unfold tipEps; ring

private lemma hasDerivWithinAt_mellinDensity_u {c' : ℝ} (_hc' : 0 < c') (g : ℝ → ℝ) {t₀ ω : ℂ}
    (ht₀ : 0 < t₀.re) :
    HasDerivAt (fun t : ℂ => mellinDensityIntegrand c' g t ω)
      (Complex.Gamma (1 / 2 + (c' : ℂ) * ω) * mellinMGEntire g (1 / 2 + (c' : ℂ) * ω) *
        (-(1 / 2 + (c' : ℂ) * ω) * (t₀)⁻¹ * (2 * (Real.pi : ℂ) * t₀) ^ (-(1 / 2 + (c' : ℂ) * ω)))) t₀ := by
  set z : ℂ := 1 / 2 + (c' : ℂ) * ω
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
  have hprod := (hd_cpow.const_mul (Complex.Gamma z)).mul_const (mellinMGEntire g z)
  refine hprod.congr_deriv ?_
  have ht₀_ne : t₀ ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at ht₀; exact lt_irrefl 0 ht₀
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp [ht₀_ne, hpi_ne]

theorem truncatedMellinP_analyticOnNhd {c' : ℝ} (hc' : 1000 ≤ c') (T₀ : ℝ) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    AnalyticOnNhd ℂ (truncatedMellinP c' T₀ g)
      (ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) := by
  have hc'_pos : 0 < c' := by linarith only [hc']
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith only [hc']
  set R : ℝ := innerChartRadius * c' ^ (2 / 3 : ℝ)
  refine DifferentiableOn.analyticOnNhd (fun u₀ hu₀ => ?_) isOpen_ball
  have hopen_u : u₀ ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) :=
    (virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hu₀)).1
  have hΔ_an : AnalyticAt ℂ (virasoroDeltaChartC c') u₀ :=
    virasoroDeltaChartC_analyticOnNhd hc'_pos u₀ hopen_u
  have hdΔ_an : AnalyticAt ℂ (deriv (virasoroDeltaChartC c')) u₀ :=
    (virasoroDeltaChartC_analyticOnNhd hc'_pos).deriv u₀ hopen_u
  have hV_an : AnalyticAt ℂ (fun u => V_C (c' : ℂ) (virasoroDeltaChartC c' u)) u₀ :=
    ((V_C_entire (c' : ℂ)).analyticAt _).comp_of_eq hΔ_an rfl
  set ω₀ : ℂ := chartOmega ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ))
  set ω₁ : ℂ := chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))
  set ωs : ℝ → ℂ := fun s => (1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁
  set F : ℂ → ℝ → ℂ := fun u s =>
    mellinDensityIntegrand c' g (virasoroDeltaChartC c' u) (ωs s) * (ω₁ - ω₀)
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
  have hz_cont : Continuous (fun s : ℝ => (1 / 2 : ℂ) + (c' : ℂ) * ωs s) := by fun_prop
  have hmg_cont : Continuous (mellinMGEntire g) := (differentiable_mellinMGEntire ha hg).continuous
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
  have hGam_cont : Continuous (fun s : ℝ => Complex.Gamma (1 / 2 + (c' : ℂ) * ωs s)) := by
    refine continuous_iff_continuousAt.mpr fun s => ?_
    have hre : 0 < ((1 / 2 : ℂ) + (c' : ℂ) * ωs s).re := by
      have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
      rw [Complex.add_re, h12, Complex.re_ofReal_mul, hω_re_zero s, mul_zero, add_zero]
      norm_num
    exact (Complex.differentiableAt_Gamma _ (fun m hm => by
      have hm_re := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at hm_re
      linarith only [hre, hm_re, Nat.cast_nonneg (α := ℝ) m])).continuousAt.comp
        (hz_cont.continuousAt)
  have hF_diff : ∀ w ∈ ball u₀ (δ / 2), ∀ s : ℝ,
      HasDerivAt (fun u => F u s)
        (Complex.Gamma (1 / 2 + (c' : ℂ) * ωs s) * mellinMGEntire g (1 / 2 + (c' : ℂ) * ωs s) *
          (-(1 / 2 + (c' : ℂ) * ωs s) * (virasoroDeltaChartC c' w)⁻¹ *
            (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) ^ (-(1 / 2 + (c' : ℂ) * ωs s))) *
          deriv (virasoroDeltaChartC c') w * (ω₁ - ω₀)) w := fun w hw s => by
    have hw_cb := Metric.ball_subset_closedBall hw
    have hw_ball := hcb_ball hw_cb
    have hopen_w := (virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hw_ball)).1
    have hdΔ_w : HasDerivAt (virasoroDeltaChartC c') (deriv (virasoroDeltaChartC c') w) w :=
      (virasoroDeltaChartC_analyticOnNhd hc'_pos w hopen_w).differentiableAt.hasDerivAt
    have hd_m := (hasDerivWithinAt_mellinDensity_u hc'_pos g (ω := ωs s) (ht_pos_on w hw_cb)).comp w hdΔ_w
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
    Complex.Gamma (1 / 2 + (c' : ℂ) * ωs s) * mellinMGEntire g (1 / 2 + (c' : ℂ) * ωs s) *
      (-(1 / 2 + (c' : ℂ) * ωs s) * (virasoroDeltaChartC c' w)⁻¹ *
        (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) ^ (-(1 / 2 + (c' : ℂ) * ωs s))) *
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
          (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u₀) ^ (-(1 / 2 + (c' : ℂ) * ωs s)) := by
        simp_rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero h2pit_slit)]
        exact Complex.continuous_exp.comp (continuous_const.mul hz_cont.neg)
      exact (((hGam_cont.mul (hmg_cont.comp hz_cont)).mul
        ((hz_cont.neg.mul continuous_const).mul hpow_c)).mul continuous_const).mul continuous_const
    exact hcont_s.aestronglyMeasurable
  have hK_cpow : ∃ M_s : ℝ, 0 ≤ M_s ∧ ∀ s ∈ Icc (0 : ℝ) 1,
      ‖Complex.Gamma (1 / 2 + (c' : ℂ) * ωs s) * mellinMGEntire g (1 / 2 + (c' : ℂ) * ωs s) *
        (-(1 / 2 + (c' : ℂ) * ωs s))‖ ≤ M_s := by
    have hcont_g : Continuous fun s : ℝ =>
        ‖Complex.Gamma (1 / 2 + (c' : ℂ) * ωs s) * mellinMGEntire g (1 / 2 + (c' : ℂ) * ωs s) *
          (-(1 / 2 + (c' : ℂ) * ωs s))‖ :=
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
  set M_z : ℝ := ‖(1 / 2 : ℂ) + (c' : ℂ) * ωs s₁‖
  have hcpow_max : ∃ M_c : ℝ, 0 ≤ M_c ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ w ∈ closedBall u₀ (δ / 2),
      ‖(2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) ^ (-(1 / 2 + (c' : ℂ) * ωs s))‖ ≤ M_c := by
    set C_base : ℝ := Real.exp (-(1 / 2 : ℝ) * Real.log (2 * Real.pi * t_re_min) + Real.pi * M_z)
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
    have hz_re : (-(1 / 2 + (c' : ℂ) * ωs s)).re = -(1 / 2 : ℝ) := by
      have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
      rw [Complex.neg_re, Complex.add_re, h12, Complex.re_ofReal_mul, hω_re_zero s, mul_zero, add_zero]
    have hz_im_bd : |(-(1 / 2 + (c' : ℂ) * ωs s)).im| ≤ M_z := by
      rw [Complex.neg_im, abs_neg]
      calc |((1 / 2 : ℂ) + (c' : ℂ) * ωs s).im| ≤ ‖(1 / 2 : ℂ) + (c' : ℂ) * ωs s‖ := Complex.abs_im_le_norm _
        _ ≤ M_z := hs₁_max hs
    have hprod_re : (Complex.log (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) *
        (-(1 / 2 + (c' : ℂ) * ωs s))).re =
        Real.log ‖2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w‖ * (-(1 / 2 : ℝ)) -
          (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).arg *
            (-(1 / 2 + (c' : ℂ) * ωs s)).im := by
      rw [Complex.mul_re, Complex.log_re, Complex.log_im, hz_re]
    rw [hprod_re]
    have hlog_bd : Real.log (2 * Real.pi * t_re_min) ≤
        Real.log ‖2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w‖ :=
      Real.log_le_log (mul_pos (mul_pos two_pos Real.pi_pos) ht_re_min_pos) h2p_norm
    have harg_bd : -((2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).arg *
        (-(1 / 2 + (c' : ℂ) * ωs s)).im) ≤ Real.pi * M_z := by
      calc -((2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).arg *
            (-(1 / 2 + (c' : ℂ) * ωs s)).im)
          ≤ |(2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).arg *
            (-(1 / 2 + (c' : ℂ) * ωs s)).im| := neg_le_abs _
        _ = |(2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w).arg| *
            |(-(1 / 2 + (c' : ℂ) * ωs s)).im| := abs_mul _ _
        _ ≤ Real.pi * M_z := mul_le_mul (Complex.abs_arg_le_pi _) hz_im_bd (abs_nonneg _) Real.pi_pos.le
    have h_lin_ineq : Real.log ‖2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w‖ * (-(1 / 2 : ℝ)) ≤
        -(1 / 2 : ℝ) * Real.log (2 * Real.pi * t_re_min) := by linarith only [hlog_bd]
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
    have hreord : Complex.Gamma (1 / 2 + (c' : ℂ) * ωs s) * mellinMGEntire g (1 / 2 + (c' : ℂ) * ωs s) *
        (-(1 / 2 + (c' : ℂ) * ωs s) * (virasoroDeltaChartC c' w)⁻¹ *
          (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) ^ (-(1 / 2 + (c' : ℂ) * ωs s))) *
        deriv (virasoroDeltaChartC c') w * (ω₁ - ω₀) =
        (Complex.Gamma (1 / 2 + (c' : ℂ) * ωs s) * mellinMGEntire g (1 / 2 + (c' : ℂ) * ωs s) *
          (-(1 / 2 + (c' : ℂ) * ωs s))) *
          (virasoroDeltaChartC c' w)⁻¹ *
          (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' w) ^ (-(1 / 2 + (c' : ℂ) * ωs s)) *
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
      (fun u => -(deriv (virasoroDeltaChartC c') u / (virasoroProblem.cardyNorm (c' / 12) g : ℂ)) *
        V_C (c' : ℂ) (virasoroDeltaChartC c' u) * ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I))) u₀ := by
    exact ((hdΔ_an.differentiableAt.div_const _).neg.mul hV_an.differentiableAt).mul_const _
  exact (hpre_diff.mul hderiv_int).differentiableWithinAt

private lemma mellinTransformG_conj (g : ℝ → ℝ) (z : ℂ) :
    mellinTransformG g (starRingEnd ℂ z) = starRingEnd ℂ (mellinTransformG g z) := by
  unfold mellinTransformG
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

private lemma mellinMG_conj (g : ℝ → ℝ) (z : ℂ) :
    mellinMG g (starRingEnd ℂ z) = starRingEnd ℂ (mellinMG g z) := by
  unfold mellinMG
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have h2pi : (2 * (Real.pi : ℂ)).arg ≠ Real.pi := by
    have hp : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    rw [hp, Complex.arg_ofReal_of_nonneg h2pi_pos.le]
    exact Real.pi_pos.ne
  have hcp := Complex.cpow_conj (2 * (Real.pi : ℂ)) z h2pi
  have h2pi_c : starRingEnd ℂ (2 * (Real.pi : ℂ)) = 2 * (Real.pi : ℂ) := by
    simp only [map_mul, map_ofNat, Complex.conj_ofReal]
  rw [h2pi_c] at hcp
  rw [hcp, mellinTransformG_conj, Complex.Gamma_conj, map_div₀, map_mul]

private lemma mellinMGEntire_conj (g : ℝ → ℝ) {z : ℂ} (hz : 0 < z.re) :
    mellinMGEntire g (starRingEnd ℂ z) = starRingEnd ℂ (mellinMGEntire g z) := by
  have hzc : 0 < (starRingEnd ℂ z).re := by simpa using hz
  rw [mellinMGEntire_of_re_pos g hzc, mellinMGEntire_of_re_pos g hz, mellinMG_conj]

private lemma mellinDensityIntegrand_conj {c' : ℝ} (hc' : 0 < c') (g : ℝ → ℝ) {t ω : ℂ}
    (ht : 0 < t.re) (hω : 0 ≤ ω.re) :
    mellinDensityIntegrand c' g (starRingEnd ℂ t) (starRingEnd ℂ ω) =
      starRingEnd ℂ (mellinDensityIntegrand c' g t ω) := by
  unfold mellinDensityIntegrand
  dsimp only
  set z : ℂ := 1 / 2 + (c' : ℂ) * ω
  have hz_re : 0 < z.re := by
    rw [show z = 1 / 2 + (c' : ℂ) * ω from rfl, Complex.add_re, Complex.re_ofReal_mul]
    have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    have hcw : 0 ≤ c' * ω.re := mul_nonneg hc'.le hω
    linarith only [h12, hcw]
  have hzc_eq : 1 / 2 + (c' : ℂ) * starRingEnd ℂ ω = starRingEnd ℂ z := by
    dsimp [z]; simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_ofReal]
  have hgam_eq : Complex.Gamma (1 / 2 + (c' : ℂ) * starRingEnd ℂ ω) =
      starRingEnd ℂ (Complex.Gamma z) := by
    rw [hzc_eq, Complex.Gamma_conj]
  rw [hgam_eq, hzc_eq, mellinMGEntire_conj g hz_re]
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

lemma truncatedMellinP_conj {c' : ℝ} (hc' : 1000 ≤ c') (T₀ : ℝ) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    truncatedMellinP c' T₀ g (starRingEnd ℂ u) =
      starRingEnd ℂ (truncatedMellinP c' T₀ g u) := by
  have hc'_pos : 0 < c' := by linarith
  have hr_pos : 0 < innerChartRadius * c' ^ (2 / 3 : ℝ) :=
    mul_pos innerChartRadius_pos (Real.rpow_pos_of_pos hc'_pos _)
  refine holomorphic_conj_eq_of_real_nhds hr_pos hr_pos le_rfl
    (truncatedMellinP_analyticOnNhd hc' T₀ hg) (fun x hx => ?_) u hu
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
  have hV_eq : V_C (c' : ℂ) (virasoroDeltaChartC c' (x : ℂ)) =
      (virasoroProblem.cardyV (c' / 12) t : ℂ) := by
    rw [ht_eq, ← virasoro_cardyV_eq_V_C]
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
          mellinDensityIntegrand c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)) =
      ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
        ∫ s in (0 : ℝ)..1,
          mellinDensityIntegrand c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀) := by
    rw [map_mul, show starRingEnd ℂ ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) =
        -((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) by
        simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]; ring]
    have hω₁_re : ω₁.re = 0 := by rw [hω₁_eq, Complex.conj_re, hω₀_re]
    have hint_seg : IntervalIntegrable
        (fun s : ℝ => mellinDensityIntegrand c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀))
        volume 0 1 := by
      have hωs_c : Continuous fun s : ℝ => (1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁ := by fun_prop
      have hz_c : Continuous fun s : ℝ => (1 / 2 : ℂ) + (c' : ℂ) * ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) := by
        fun_prop
      have hre_pt : ∀ s : ℝ, 0 < ((1 / 2 : ℂ) + (c' : ℂ) * ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁)).re := by
        intro s
        have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
        have hωs_re : ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁).re = 0 := by
          simp [Complex.add_re, Complex.mul_re, hω₀_re, hω₁_re]
        rw [Complex.add_re, h12, Complex.re_ofReal_mul, hωs_re, mul_zero, add_zero]
        norm_num
      have hGam_c : Continuous fun s : ℝ =>
          Complex.Gamma (1 / 2 + (c' : ℂ) * ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁)) := by
        refine continuous_iff_continuousAt.mpr fun s => ?_
        exact (Complex.differentiableAt_Gamma _ (fun m hm => by
          have hm_re := congrArg Complex.re hm
          simp only [Complex.neg_re, Complex.natCast_re] at hm_re
          linarith [hre_pt s, Nat.cast_nonneg (α := ℝ) m])).continuousAt.comp
            (hz_c.continuousAt)
      have hm_c : Continuous fun s : ℝ =>
          mellinMGEntire g (1 / 2 + (c' : ℂ) * ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁)) :=
        (differentiable_mellinMGEntire (by linarith : 2 ≤ c' / 12) hg).continuous.comp hz_c
      have h2pit_ne : (2 * (Real.pi : ℂ) * (t : ℂ)) ≠ 0 := by
        have : 0 < 2 * Real.pi * t := by positivity
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hp_c : Continuous fun s : ℝ =>
          (2 * (Real.pi : ℂ) * (t : ℂ)) ^ (-(1 / 2 + (c' : ℂ) * ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁))) := by
        simp_rw [Complex.cpow_def_of_ne_zero h2pit_ne]
        exact Complex.continuous_exp.comp (continuous_const.mul hz_c.neg)
      have htot_c : Continuous fun s : ℝ =>
          mellinDensityIntegrand c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀) :=
        ((hGam_c.mul hp_c).mul hm_c).mul continuous_const
      exact htot_c.intervalIntegrable 0 1
    have hconj_int : starRingEnd ℂ (∫ s in (0 : ℝ)..1,
          mellinDensityIntegrand c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)) =
        ∫ s in (0 : ℝ)..1,
          starRingEnd ℂ (mellinDensityIntegrand c' g (t : ℂ)
            ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)) :=
      (Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint_seg).symm
    rw [hconj_int]
    have hsub : (fun s : ℝ => starRingEnd ℂ (mellinDensityIntegrand c' g (t : ℂ)
          ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀))) =
        fun s : ℝ => -(mellinDensityIntegrand c' g (t : ℂ)
          ((1 - ((1 - s : ℝ) : ℂ)) * ω₀ + ((1 - s : ℝ) : ℂ) * ω₁) * (ω₁ - ω₀)) := by
      ext s
      rw [map_mul, hω_sub_conj]
      have hre_pt : ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁).re = 0 := by
        simp [Complex.add_re, Complex.mul_re, hω₀_re, hω₁_re]
      have hm_c := mellinDensityIntegrand_conj hc'_pos g (t := (t : ℂ)) (by simpa using ht_pos) hre_pt.ge
      rw [Complex.conj_ofReal] at hm_c
      have hpt_conj : starRingEnd ℂ ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) =
          (1 - ((1 - s : ℝ) : ℂ)) * ω₀ + ((1 - s : ℝ) : ℂ) * ω₁ := by
        simp only [map_add, map_mul, map_sub, map_one, Complex.conj_ofReal, ← hω₁_eq]
        rw [hω₁_eq, Complex.conj_conj]
        push_cast; ring
      rw [← hm_c, hpt_conj]
      ring
    rw [hsub, intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left
      (fun s : ℝ => mellinDensityIntegrand c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)) 1]
    simp only [sub_zero, sub_self]
    ring
  have h_all_real : truncatedMellinP c' T₀ g (x : ℂ) =
      starRingEnd ℂ (truncatedMellinP c' T₀ g (x : ℂ)) := by
    unfold truncatedMellinP
    dsimp only
    rw [hV_eq, ht_eq]
    set A_pre : ℂ := -(deriv (virasoroDeltaChartC c') (x : ℂ) / (virasoroProblem.cardyNorm (c' / 12) g : ℂ)) *
      (virasoroProblem.cardyV (c' / 12) t : ℂ)
    set B_int : ℂ := ∫ s in (0 : ℝ)..1,
      mellinDensityIntegrand c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)
    change A_pre * ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) * B_int =
      starRingEnd ℂ (A_pre * ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) * B_int)
    rw [mul_assoc A_pre, map_mul, hint_conj]
    congr 1
    dsimp [A_pre]
    rw [map_mul, map_neg, map_div₀, Complex.conj_eq_iff_im.mpr hd_im,
      Complex.conj_ofReal, Complex.conj_ofReal]
  exact Complex.conj_eq_iff_im.mp h_all_real.symm

lemma virasoroPsiTilde_inner_im_ofReal {c' : ℝ} (hc' : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {x : ℝ}
    (hx : |x| < innerChartRadius * c' ^ (2 / 3 : ℝ)) :
    (virasoroPsiTilde c' g (x : ℂ)).im = 0 := by
  have hx_ball : (x : ℂ) ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx
  have h1 := virasoroPsiTilde_inner_conj hc' hg hx_ball
  rw [Complex.conj_ofReal] at h1
  exact Complex.conj_eq_iff_im.mp h1.symm

lemma truncatedMellinP_inner_im_ofReal {c' : ℝ} (hc' : 1000 ≤ c') (T₀ : ℝ) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {x : ℝ}
    (hx : |x| < innerChartRadius * c' ^ (2 / 3 : ℝ)) :
    (truncatedMellinP c' T₀ g (x : ℂ)).im = 0 := by
  have hx_ball : (x : ℂ) ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx
  have h1 := truncatedMellinP_conj hc' T₀ hg hx_ball
  rw [Complex.conj_ofReal] at h1
  exact Complex.conj_eq_iff_im.mp h1.symm

/-! ### 3. Midline Mellin inversion and real-axis truncation bound -/

private noncomputable def midlineY (τ : ℝ) : ℝ :=
  (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).im

private lemma midlineY_odd (τ : ℝ) : midlineY (-τ) = -midlineY τ := by
  unfold midlineY
  have hconj : (1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ) =
      starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) := by
    apply Complex.ext <;> simp
  rw [hconj, chartOmega_conj (by norm_num) (by norm_num), Complex.conj_im]

private lemma chartOmega_midline_eq_I_mul_midlineY (τ : ℝ) :
    chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) = Complex.I * (midlineY τ : ℂ) := by
  have hre : (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re = 0 := by
    by_cases hτ : τ = 0
    · rw [hτ, Complex.ofReal_zero, mul_zero, add_zero, chartOmega_half, Complex.zero_re]
    · unfold chartOmega
      simp only [show ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)).re ≤ 1 / 2 by simp, ↓reduceIte]
      exact chartOmegaHalf_midline_re_zero hτ
  apply Complex.ext
  · simpa [Complex.mul_re] using hre
  · simp [midlineY]

private lemma hasDerivAt_midlineY (τ : ℝ) :
    HasDerivAt midlineY (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re τ := by
  have hom_an : AnalyticAt ℂ chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) :=
    analyticAt_chartOmega (by norm_num) (by norm_num)
  have hom_d := hom_an.differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) Complex.I τ := by
    have h1 := ((hasDerivAt_id τ).ofReal_comp).const_mul Complex.I |>.const_add (1 / 2 : ℂ)
    simpa using h1
  have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ (hom_d.scomp τ hline)
  refine hcomp.congr_deriv ?_
  simp [Complex.imCLM, Complex.mul_im]

private lemma midlineY_deriv_neg (τ : ℝ) :
    (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re < 0 := by
  rcases le_or_gt 0 τ with hnn | hneg
  · exact (deriv_chartOmega_midline_real_neg hnn).2
  · have hm_pos : 0 ≤ -τ := by linarith
    have hpos := (deriv_chartOmega_midline_real_neg hm_pos).2
    have hconj_pt : (1 / 2 : ℂ) + Complex.I * (τ : ℂ) =
        starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ)) := by apply Complex.ext <;> simp
    have hconj_d : deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) =
        starRingEnd ℂ (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * ((-τ : ℝ) : ℂ))) := by
      rw [hconj_pt]
      exact deriv_chartOmega_conj' (by simp) (by simp; norm_num)
    rw [hconj_d, Complex.conj_re]
    exact hpos

private lemma midlineY_norm_le_C_om' :
    ∃ C_om' : ℝ, 0 < C_om' ∧
      ∀ τ : ℝ, ‖deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ≤ C_om' * (1 + |τ|) := by
  obtain ⟨C_om', hC_pos, hbd⟩ := lemma_J7_asymptotics.2.2.2.2.1
  refine ⟨C_om', hC_pos, fun τ => ?_⟩
  simpa using hbd ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) ⟨by simp, by simp; norm_num⟩

private lemma chartPhiV_midline_conj (τ : ℝ) :
    (chartPhiV ((1 / 2 : ℂ) - Complex.I * (τ : ℂ)) (xiStar : ℂ)).re =
      (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re := by
  have hconj_pt : (1 / 2 : ℂ) - Complex.I * (τ : ℂ) =
      starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) := by apply Complex.ext <;> simp
  have hω_re : 0 ≤ (chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re := by
    rw [chartOmega_midline_eq_I_mul_midlineY]; simp
  rw [hconj_pt, chartPhiV_conj (by norm_num) (by norm_num) hω_re xiStar_pos, Complex.conj_re]

private lemma real_mellinIntegrand_eq_mellinTransformG {c' : ℝ} (_hc' : 24 ≤ c') {g : ℝ → ℝ}
    (_hg : TestClass virasoroProblem (c' / 12) g) {t : ℝ} (ht : 0 < t) (η : ℝ) :
    Complex.Gamma (1 / 2 + Complex.I * (η : ℂ)) *
        (2 * (Real.pi : ℂ) * (t : ℂ)) ^ (-(1 / 2 + Complex.I * (η : ℂ))) *
        mellinMGEntire g (1 / 2 + Complex.I * (η : ℂ)) =
      (t : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
        mellinTransformG g (1 / 2 + Complex.I * (η : ℂ)) := by
  set z : ℂ := 1 / 2 + Complex.I * (η : ℂ)
  have hz_re : 0 < z.re := by simp [z]
  have hGam_ne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz_re
  have ht_pos_c : 0 < ((t : ℂ)).re := by simpa using ht
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h2pi_ne : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr h2pi_pos.ne' |> fun _ =>
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow_mul : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ (-z) =
      (2 * (Real.pi : ℂ)) ^ (-z) * (t : ℂ) ^ (-z) := by
    rw [show (2 * (Real.pi : ℂ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl]
    exact ofReal_mul_cpow h2pi_pos (t : ℂ) (-z)
  have hpow_cancel : (2 * (Real.pi : ℂ)) ^ (-z) * (2 * (Real.pi : ℂ)) ^ z = 1 := by
    rw [← Complex.cpow_add _ _ h2pi_ne, neg_add_cancel, Complex.cpow_zero]
  rw [mellinMGEntire_of_re_pos g hz_re]
  unfold mellinMG
  rw [hpow_mul]
  calc Complex.Gamma z * ((2 * (Real.pi : ℂ)) ^ (-z) * (t : ℂ) ^ (-z)) *
        ((2 * (Real.pi : ℂ)) ^ z * mellinTransformG g z / Complex.Gamma z)
      = (Complex.Gamma z / Complex.Gamma z) *
          ((2 * (Real.pi : ℂ)) ^ (-z) * (2 * (Real.pi : ℂ)) ^ z) *
          (t : ℂ) ^ (-z) * mellinTransformG g z := by ring
    _ = 1 * 1 * (t : ℂ) ^ (-z) * mellinTransformG g z := by
          rw [div_self hGam_ne, hpow_cancel]
    _ = (t : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) * mellinTransformG g z := by
          rw [one_mul, one_mul]; simp only [z]; ring_nf

private lemma truncatedMellinP_real_integral_eq {c' : ℝ} (hc' : 24 ≤ c') (T₀ : ℝ) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {t : ℝ} (ht : 0 < t) :
    let ω₀ : ℂ := chartOmega ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ))
    let ω₁ : ℂ := chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ))
    let η₀ : ℝ := -c' * midlineY T₀
    ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
        ∫ s in (0 : ℝ)..1,
          mellinDensityIntegrand c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ η in (-η₀)..η₀,
          (t : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
            mellinTransformG g (1 / 2 + Complex.I * (η : ℂ)) := by
  intro ω₀ ω₁ η₀
  have hc'_pos : 0 < c' := by linarith
  have hω₀_eq : ω₀ = Complex.I * (midlineY T₀ : ℂ) := chartOmega_midline_eq_I_mul_midlineY T₀
  have hω₁_eq : ω₁ = Complex.I * ((-midlineY T₀ : ℝ) : ℂ) := by
    have h1 : (1 / 2 : ℂ) - Complex.I * (T₀ : ℂ) = (1 / 2 : ℂ) + Complex.I * ((-T₀ : ℝ) : ℂ) := by
      push_cast; ring
    dsimp [ω₁]
    rw [h1, chartOmega_midline_eq_I_mul_midlineY (-T₀), midlineY_odd]
  have hη_pt : ∀ s : ℝ, (1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁ =
      Complex.I * (((((2 * s - 1) * η₀) / c' : ℝ) : ℂ)) := fun s => by
    rw [hω₀_eq, hω₁_eq]
    dsimp [η₀]
    push_cast
    field_simp [hc'_pos.ne']
    ring
  have hω_diff : ω₁ - ω₀ = Complex.I * ((2 * η₀ / c' : ℝ) : ℂ) := by
    rw [hω₀_eq, hω₁_eq]
    dsimp [η₀]
    push_cast
    field_simp [hc'_pos.ne']
    ring
  let F : ℝ → ℂ := fun η =>
    (t : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) * mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))
  have hintegrand_eq : ∀ s : ℝ,
      mellinDensityIntegrand c' g (t : ℂ) ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀) =
        Complex.I * ((2 * η₀ / c' : ℝ) : ℂ) * F ((2 * s - 1) * η₀) := fun s => by
    rw [hη_pt s, hω_diff]
    dsimp [mellinDensityIntegrand, F]
    have harg_eq : 1 / 2 + (c' : ℂ) * (Complex.I * (((((2 * s - 1) * η₀) / c' : ℝ) : ℂ))) =
        1 / 2 + Complex.I * (((2 * s - 1) * η₀ : ℝ) : ℂ) := by
      push_cast; field_simp [hc'_pos.ne']
    rw [harg_eq, real_mellinIntegrand_eq_mellinTransformG hc' hg ht ((2 * s - 1) * η₀)]
    ring
  simp_rw [hintegrand_eq]
  rw [intervalIntegral.integral_const_mul]
  by_cases hη₀ : η₀ = 0
  · simp [hη₀]
  · have h2η₀ : 2 * η₀ ≠ 0 := mul_ne_zero two_ne_zero hη₀
    have hsub := intervalIntegral.integral_comp_mul_sub (f := F) h2η₀ η₀ (a := 0) (b := 1)
    have hsub2 : ∫ s in (0 : ℝ)..1, F ((2 * s - 1) * η₀) =
        (2 * η₀)⁻¹ • ∫ η in (-η₀)..η₀, F η := by
      have harg : (fun s : ℝ => F ((2 * s - 1) * η₀)) = fun s => F ((2 * η₀) * s - η₀) := by
        ext s; ring_nf
      rw [harg]
      simpa [mul_zero, zero_sub, mul_one, sub_self, show 2 * η₀ - η₀ = η₀ by ring] using hsub
    rw [hsub2, Complex.real_smul]
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hc'_ne : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc'_pos.ne'
    have hη₀_ne : (η₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη₀
    have hcoef : ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
          (Complex.I * ((2 * η₀ / c' : ℝ) : ℂ)) * (((2 * η₀)⁻¹ : ℝ) : ℂ) =
        1 / (2 * (Real.pi : ℂ)) := by
      push_cast
      field_simp [hpi_ne, hc'_ne, hη₀_ne, Complex.I_ne_zero]
    rw [← mul_assoc, ← mul_assoc, hcoef]

private lemma mellin_midline_tail_exists {T₀ d₀ d₁ c_mid C_om' C_S4 : ℝ}
    (hT₀ : 4 ≤ T₀) (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hcmid : 0 < c_mid) (hCom' : 0 < C_om')
    (hCS4 : 0 < C_S4)
    (h_mid_lb : ∀ τ : ℝ, c_mid * τ ^ 2 ≤ ‖chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖)
    (h_d_bd : ∀ τ : ℝ, ‖deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))‖ ≤ C_om' * (1 + |τ|))
    (h_tail : ∀ τ ≥ T₀, (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re ≤
      -d₀ - d₁ * (τ - T₀)) :
    ∃ c_tail C_tail : ℝ, 10000 ≤ c_tail ∧ 0 < C_tail ∧
      ∀ {c' : ℝ}, c_tail ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass virasoroProblem (c' / 12) g →
        0 < virasoroProblem.cardyNorm (c' / 12) g →
        (∀ ζ ∈ stripClosed, ‖tildeWV c' g ζ‖ ≤ C_S4 * virasoroProblem.cardyNorm (c' / 12) g) →
        let M := virasoroProblem.cardyNorm (c' / 12) g
        let η₀ := -c' * midlineY T₀
        VerticalIntegrable (mellin fun t : ℝ => (g t : ℂ)) (1 / 2) ∧
        ∀ {b₀ : ℝ}, xiStar / 2 ≤ b₀ → b₀ ≤ 2 * xiStar →
          (2 * Real.pi / 3) * |b₀ - xiStar| ≤ d₀ / 4 →
          let t₀ : ℝ := c' * b₀ ^ 2 / 3
          ∫ η in Ioi η₀,
              ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
                mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖ ≤
            (C_tail / 2) * M * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
              Real.exp (-(3 * d₀ / 4) * c') := by
  let c_tail : ℝ := max 10000 (max (48 / (c_mid * T₀ ^ 2)) (3 / (xiStar / 2) ^ 2))
  let C_tail : ℝ := 4 * C_S4 * C_om' * (1 + T₀ + 1 / d₁) / d₁
  refine ⟨c_tail, C_tail, le_max_left _ _, by positivity, fun {c'} hc' {g} hg hM_pos hS4 => ?_⟩
  have hc'_10000 : 10000 ≤ c' := (le_max_left _ _).trans hc'
  have hc'_48 : 48 / (c_mid * T₀ ^ 2) ≤ c' :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_t₀ : 3 / (xiStar / 2) ^ 2 ≤ c' :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hc'
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith only [hc'_10000]
  set M := virasoroProblem.cardyNorm (c' / 12) g
  set η₀ := -c' * midlineY T₀
  have hT₀_pos : 0 < T₀ := by linarith only [hT₀]
  have hY_T₀_neg : midlineY T₀ < 0 := by
    have h1 := im_chartOmega_midline_strictAnti hT₀_pos
    dsimp only at h1
    rw [Complex.ofReal_zero, mul_zero, add_zero, chartOmega_half, Complex.zero_im] at h1
    exact h1
  have hη₀_pos : 0 < η₀ := by
    dsimp [η₀]
    nlinarith only [hc'_pos, hY_T₀_neg]
  have hm_cont : Continuous fun η : ℝ => mellinTransformG g (1 / 2 + Complex.I * (η : ℂ)) := by
    let F_m : ℝ → ℝ → ℂ := fun η t =>
      (g t : ℂ) * (t : ℂ) ^ ((1 / 2 : ℂ) + Complex.I * (η : ℂ) - 1)
    have hF_meas : ∀ η : ℝ, AEStronglyMeasurable (F_m η) (volume.restrict (Ioi 0)) := fun η => by
      have hg_c : ContinuousOn (fun t : ℝ => (g t : ℂ)) (Ioi 0) :=
        Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)
      have hp_c : ContinuousOn (fun t : ℝ => (t : ℂ) ^ ((1 / 2 : ℂ) + Complex.I * (η : ℂ) - 1)) (Ioi 0) := by
        intro t ht
        have ht_slit : (t : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using mem_Ioi.mp ht)
        exact (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const ht_slit).continuousWithinAt
      exact (hg_c.mul hp_c).aestronglyMeasurable measurableSet_Ioi
    have hF_dom : ∀ η : ℝ, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ‖F_m η t‖ ≤ |g t| * t ^ ((1 / 2 : ℝ) - 1) := fun η => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := mem_Ioi.mp ht
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_pos.ne'
      have hre : ((1 / 2 : ℂ) + Complex.I * (η : ℂ) - 1).re = (1 / 2 : ℝ) - 1 := by
        have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
        simp only [Complex.sub_re, Complex.add_re, h12, Complex.one_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
      have hnorm : ‖(t : ℂ) ^ ((1 / 2 : ℂ) + Complex.I * (η : ℂ) - 1)‖ = t ^ ((1 / 2 : ℝ) - 1) := by
        rw [Complex.cpow_def_of_ne_zero ht_ne, Complex.norm_exp,
          show Complex.log (t : ℂ) = (Real.log t : ℂ) from (Complex.ofReal_log ht_pos.le).symm,
          Complex.re_ofReal_mul, hre, Real.rpow_def_of_pos ht_pos]
      dsimp [F_m]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnorm]
    have hbound_int : IntegrableOn (fun t : ℝ => |g t| * t ^ ((1 / 2 : ℝ) - 1)) (Ioi 0) :=
      integrableOn_abs_mellinTransformG ha hg (by norm_num : (0 : ℝ) < 1 / 2)
    have hF_cont : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), Continuous fun η : ℝ => F_m η t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mem_Ioi.mp ht).ne'
      dsimp [F_m]
      simp_rw [Complex.cpow_def_of_ne_zero ht_ne]
      exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul (by fun_prop)))
    exact MeasureTheory.continuous_of_dominated hF_meas hF_dom hbound_int hF_cont
  -- Helper: bound for `‖(t₀ : ℂ)^(-(1/2) - I η) * mellinTransformG g (1/2 + I η)‖` via `τ ≥ T₀`
  have hpt_τ : ∀ (τ : ℝ) (hτ : T₀ ≤ τ) (b₀ : ℝ) (hb₀_pos : 0 < b₀),
      let t₀ : ℝ := c' * b₀ ^ 2 / 3
      let η : ℝ := -c' * midlineY τ
      ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
          mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖ ≤
        (2 * C_S4 * M) * t₀ ^ (-(1 / 2 : ℝ)) *
          Real.exp (c' * (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re -
            c' * (2 * Real.pi / 3) * b₀) := by
    intro τ hτ b₀ hb₀_pos t₀ η
    have ht₀_pos : 0 < t₀ := by dsimp [t₀]; have := sq_pos_of_pos hb₀_pos; positivity
    set ζ := (1 / 2 : ℂ) + Complex.I * (τ : ℂ)
    set ω := chartOmega ζ
    have hω_eq : ω = Complex.I * (midlineY τ : ℂ) := chartOmega_midline_eq_I_mul_midlineY τ
    have hω_re : ω.re = 0 := by rw [hω_eq]; simp
    have hω_norm : c_mid * τ ^ 2 ≤ ‖ω‖ := h_mid_lb τ
    have hcω_48 : 48 ≤ c' * ‖ω‖ := by
      have h1 : 48 ≤ c' * (c_mid * T₀ ^ 2) := (div_le_iff₀ (by positivity)).mp hc'_48
      have h2 : c_mid * T₀ ^ 2 ≤ c_mid * τ ^ 2 := by gcongr
      calc (48 : ℝ) ≤ c' * (c_mid * T₀ ^ 2) := h1
        _ ≤ c' * (c_mid * τ ^ 2) := by gcongr
        _ ≤ c' * ‖ω‖ := by gcongr
    have hω_ne : ω ≠ 0 := by
      intro h0; rw [h0, norm_zero, mul_zero] at hcω_48; linarith only [hcω_48]
    have hS_bd : ‖stirlingS c' ω‖ ≤ 2 := by
      have h1 : 1 ≤ c' * ‖ω‖ := by linarith only [hcω_48]
      have hsub := norm_stirlingS_sub_one_le hc'_pos hω_re.ge h1
      have hle : 24 / (c' * ‖ω‖) ≤ 1 / 2 := by
        calc 24 / (c' * ‖ω‖) ≤ 24 / 48 := by gcongr
          _ = 1 / 2 := by norm_num
      have htr : ‖stirlingS c' ω‖ ≤ ‖stirlingS c' ω - 1‖ + ‖(1 : ℂ)‖ := by
        calc ‖stirlingS c' ω‖ = ‖(stirlingS c' ω - 1) + 1‖ := by ring_nf
          _ ≤ ‖stirlingS c' ω - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      rw [norm_one] at htr
      linarith only [htr, hsub, hle]
    have h_conj_m : ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
          mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖ =
        ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) + Complex.I * (η : ℂ)) *
          mellinTransformG g (1 / 2 - Complex.I * (η : ℂ))‖ := by
      have h1 : starRingEnd ℂ ((t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
            mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))) =
          (t₀ : ℂ) ^ (-(1 / 2 : ℂ) + Complex.I * (η : ℂ)) *
            mellinTransformG g (1 / 2 - Complex.I * (η : ℂ)) := by
        have harg : (t₀ : ℂ).arg ≠ Real.pi := by
          rw [Complex.arg_ofReal_of_nonneg ht₀_pos.le]; exact Real.pi_pos.ne
        have hcp := Complex.cpow_conj (t₀ : ℂ) (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) harg
        rw [Complex.conj_ofReal] at hcp
        rw [map_mul, ← hcp, ← mellinTransformG_conj]
        simp only [map_add, map_sub, map_neg, map_div₀, map_one, map_ofNat, map_mul,
          Complex.conj_ofReal, Complex.conj_I]
        congr 2 <;> ring
      rw [← h1, Complex.norm_conj]
    rw [h_conj_m]
    have hz_eq : (1 / 2 : ℂ) - Complex.I * (η : ℂ) = 1 / 2 + (c' : ℂ) * ω := by
      rw [hω_eq]; dsimp [η]; push_cast; ring
    have h_st := gamma_mul_two_pi_t_cpow_neg hc'_pos (ω := ω) (b := (b₀ : ℂ)) hω_re.ge hω_ne
      (by simpa using hb₀_pos)
    have h_rel := real_mellinIntegrand_eq_mellinTransformG (by linarith only [hc'_10000] : 24 ≤ c') hg ht₀_pos (-η)
    have hpow_neg : -(1 / 2 : ℂ) - Complex.I * ((-η : ℝ) : ℂ) = -(1 / 2 : ℂ) + Complex.I * (η : ℂ) := by
      push_cast; ring
    rw [hpow_neg, show (1 / 2 : ℂ) + Complex.I * ((-η : ℝ) : ℂ) = 1 / 2 - Complex.I * (η : ℂ) by
      push_cast; ring] at h_rel
    rw [← h_rel, hz_eq]
    have h_prod_st : Complex.Gamma (1 / 2 + (c' : ℂ) * ω) *
          (2 * (Real.pi : ℂ) * (t₀ : ℂ)) ^ (-(1 / 2 + (c' : ℂ) * ω)) *
          mellinMGEntire g (1 / 2 + (c' : ℂ) * ω) =
        (t₀ : ℂ) ^ (-(1 / 2 : ℂ)) * stirlingS c' ω *
          Complex.exp ((c' : ℂ) * chartPhiV ζ (b₀ : ℂ) - (c' : ℂ) * tipL (b₀ : ℂ)) *
          tildeWV c' g ζ := by
      have ht₀_c : (t₀ : ℂ) = (c' : ℂ) * (b₀ : ℂ) ^ 2 / 3 := by dsimp [t₀]; push_cast; ring
      rw [← ht₀_c] at h_st
      rw [h_st]
      unfold tildeWV chartPhiV
      have hexp1 : Complex.exp ((c' : ℂ) * stirlingJ ω (b₀ : ℂ)) =
          Complex.exp ((c' : ℂ) * (chartUpsilon ζ + stirlingJ ω (b₀ : ℂ) + tipL (b₀ : ℂ)) -
            (c' : ℂ) * tipL (b₀ : ℂ)) * Complex.exp (-(c' : ℂ) * chartUpsilon ζ) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [hexp1]
      ring
    rw [h_prod_st, norm_mul, norm_mul, norm_mul]
    have ht₀_half : ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ))‖ = t₀ ^ (-(1 / 2 : ℝ)) := by
      rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow ht₀_pos.le, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg ht₀_pos.le _)]
    have hζ_cl : ζ ∈ stripClosed := ⟨by simp [ζ], by simp [ζ]; norm_num⟩
    have hWV_bd := hS4 ζ hζ_cl
    have hexp_norm : ‖Complex.exp ((c' : ℂ) * chartPhiV ζ (b₀ : ℂ) - (c' : ℂ) * tipL (b₀ : ℂ))‖ =
        Real.exp (c' * (chartPhiV ζ (b₀ : ℂ)).re - c' * (2 * Real.pi / 3) * b₀) := by
      rw [Complex.norm_exp]
      congr 1
      have htip : (tipL (b₀ : ℂ)).re = (2 * Real.pi / 3) * b₀ := by
        unfold tipL
        rw [Complex.re_ofReal_mul, Complex.ofReal_re]
      simp only [Complex.sub_re, Complex.re_ofReal_mul, htip]
      ring
    rw [ht₀_half, hexp_norm]
    calc t₀ ^ (-(1 / 2 : ℝ)) * ‖stirlingS c' ω‖ *
            Real.exp (c' * (chartPhiV ζ (b₀ : ℂ)).re - c' * (2 * Real.pi / 3) * b₀) *
            ‖tildeWV c' g ζ‖
        ≤ t₀ ^ (-(1 / 2 : ℝ)) * 2 *
            Real.exp (c' * (chartPhiV ζ (b₀ : ℂ)).re - c' * (2 * Real.pi / 3) * b₀) *
            (C_S4 * M) := by gcongr
      _ = (2 * C_S4 * M) * t₀ ^ (-(1 / 2 : ℝ)) *
            Real.exp (c' * (chartPhiV ζ (b₀ : ℂ)).re - c' * (2 * Real.pi / 3) * b₀) := by ring
  -- Helper: `(chartPhiV (1/2 + I * τ) b₀).re = (chartPhiV (1/2 + I * τ) xiStar).re + (2π/3)(b₀ - xiStar)`
  have hphi_shift : ∀ (τ : ℝ) (b₀ : ℝ), 0 < b₀ →
      (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re =
        (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (xiStar : ℂ)).re +
          (2 * Real.pi / 3) * (b₀ - xiStar) := fun τ b₀ hb₀_pos => by
    unfold chartPhiV ComplexBessel.stirlingJ tipL
    rw [chartOmega_midline_eq_I_mul_midlineY τ]
    have hlog_sub : (Complex.I * (midlineY τ : ℂ) *
          (Complex.log (3 * (Complex.I * (midlineY τ : ℂ)) / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) -
            2 * Complex.log (b₀ : ℂ))).re -
        (Complex.I * (midlineY τ : ℂ) *
          (Complex.log (3 * (Complex.I * (midlineY τ : ℂ)) / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) -
            2 * Complex.log (xiStar : ℂ))).re = 0 := by
      have h1 : Complex.I * (midlineY τ : ℂ) *
            (Complex.log (3 * (Complex.I * (midlineY τ : ℂ)) / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) -
              2 * Complex.log (b₀ : ℂ)) -
          Complex.I * (midlineY τ : ℂ) *
            (Complex.log (3 * (Complex.I * (midlineY τ : ℂ)) / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) -
              2 * Complex.log (xiStar : ℂ)) =
          Complex.I * ((-2 * midlineY τ * (Real.log b₀ - Real.log xiStar) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_log hb₀_pos.le, ← Complex.ofReal_log xiStar_pos.le]
        push_cast; ring
      have hre := congrArg Complex.re h1
      rw [Complex.sub_re] at hre
      rw [hre]; simp
    have hL1 : (((2 * Real.pi / 3 : ℝ) : ℂ) * (b₀ : ℂ)).re = (2 * Real.pi / 3) * b₀ := by
      simp
    have hL2 : (((2 * Real.pi / 3 : ℝ) : ℂ) * (xiStar : ℂ)).re = (2 * Real.pi / 3) * xiStar := by
      simp
    simp only [Complex.add_re, hL1, hL2]
    linarith only [hlog_sub]
  -- Bound the tail integral on `[η₀, -c' * midlineY T]` for any `T ≥ T₀`
  have htail_Icc : ∀ {b₀ : ℝ}, xiStar / 2 ≤ b₀ → b₀ ≤ 2 * xiStar →
      (2 * Real.pi / 3) * |b₀ - xiStar| ≤ d₀ / 4 →
      let t₀ : ℝ := c' * b₀ ^ 2 / 3
      ∀ T ≥ T₀, ∫ η in η₀..(-c' * midlineY T),
          ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
            mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖ ≤
        (C_tail / 2) * M * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
          Real.exp (-(3 * d₀ / 4) * c') := by
    intro b₀ hb₀_lo _ hb₀_gap t₀ T hT
    have hb₀_pos : 0 < b₀ := by have := xiStar_pos; linarith only [hb₀_lo, this]
    have ht₀_pos : 0 < t₀ := by dsimp [t₀]; have := sq_pos_of_pos hb₀_pos; positivity
    have ht₀_ge1 : 1 ≤ t₀ := by
      have hxi := xiStar_pos
      have hsq : (xiStar / 2) ^ 2 ≤ b₀ ^ 2 := by nlinarith only [hb₀_lo, hxi]
      have h3 : 3 ≤ c' * (xiStar / 2) ^ 2 := (div_le_iff₀ (by positivity)).mp hc'_t₀
      dsimp [t₀]
      have hcb : 3 ≤ c' * b₀ ^ 2 := h3.trans (mul_le_mul_of_nonneg_left hsq hc'_pos.le)
      linarith only [hcb]
    have ht₀_half_le : t₀ ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht₀_ge1 (by norm_num)
    let φ : ℝ → ℝ := fun τ => -c' * midlineY τ
    let φ' : ℝ → ℝ := fun τ => -c' * (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re
    have hφ_deriv : ∀ τ ∈ uIcc T₀ T, HasDerivAt φ (φ' τ) τ := fun τ _ => by
      simpa [φ, φ'] using (hasDerivAt_midlineY τ).const_mul (-c')
    have hφ'_cont : ContinuousOn φ' (uIcc T₀ T) := by
      have hom_an : AnalyticOnNhd ℂ chartOmega {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := fun z hz =>
        analyticAt_chartOmega hz.1.le hz.2.le
      have hline_cont : Continuous fun τ : ℝ => (1 / 2 : ℂ) + Complex.I * (τ : ℂ) := by fun_prop
      have hder_cont : Continuous fun τ : ℝ =>
          (deriv chartOmega ((1 / 2 : ℂ) + Complex.I * (τ : ℂ))).re :=
        Complex.continuous_re.comp ((hom_an.deriv.continuousOn.comp_continuous hline_cont) fun τ =>
          ⟨by simp, by simp; norm_num⟩)
      exact (continuous_const.mul hder_cont).continuousOn
    let ψ : ℝ → ℝ := fun η =>
      ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
        mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖
    have hψ_cont : Continuous ψ := by
      have ht_cont : Continuous fun η : ℝ => (t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) := by
        have ht₀_ne : (t₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₀_pos.ne'
        simp_rw [Complex.cpow_def_of_ne_zero ht₀_ne]
        exact Complex.continuous_exp.comp (continuous_const.mul (by fun_prop))
      exact (ht_cont.mul hm_cont).norm
    have hcomp := intervalIntegral.integral_comp_mul_deriv hφ_deriv hφ'_cont hψ_cont
    change ∫ η in φ T₀..φ T, ψ η ≤ _
    rw [← hcomp]
    let K : ℝ := 2 * C_S4 * M * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
      Real.exp (-(3 * d₀ / 4) * c') * C_om'
    have hK_nn : 0 ≤ K := by positivity [hM_pos]
    have hpt_bd : ∀ τ ∈ Icc T₀ T,
        ψ (φ τ) * φ' τ ≤ K * (c' * ((1 + τ) * Real.exp (-c' * d₁ * (τ - T₀)))) := fun τ hτ => by
      have hτ_nn : 0 ≤ τ := by linarith only [hτ.1, hT₀]
      have hψ_bd := hpt_τ τ hτ.1 b₀ hb₀_pos
      have hsh := hphi_shift τ b₀ hb₀_pos
      have htail_bd := h_tail τ hτ.1
      have hre_bd : (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re ≤
          -(3 * d₀ / 4) - d₁ * (τ - T₀) := by
        have h1 : (2 * Real.pi / 3) * (b₀ - xiStar) ≤ (2 * Real.pi / 3) * |b₀ - xiStar| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        linarith only [hsh, htail_bd, h1, hb₀_gap]
      have hexp_ub : Real.exp (c' * (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re -
            c' * (2 * Real.pi / 3) * b₀) ≤
          Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') *
            Real.exp (-c' * d₁ * (τ - T₀)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hmul := mul_le_mul_of_nonneg_left hre_bd hc'_pos.le
        linarith only [hmul]
      have hφ'_nn : 0 ≤ φ' τ := by
        have hmneg := midlineY_deriv_neg τ
        dsimp [φ']; nlinarith only [hmneg, hc'_pos]
      have hφ'_ub : φ' τ ≤ c' * C_om' * (1 + τ) := by
        have h1 := (Complex.abs_re_le_norm _).trans (h_d_bd τ)
        rw [abs_of_neg (midlineY_deriv_neg τ)] at h1
        rw [abs_of_nonneg hτ_nn] at h1
        dsimp [φ']
        nlinarith only [h1, hc'_pos]
      have hψ_ub : ψ (φ τ) ≤ (2 * C_S4 * M) *
          (Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') *
            Real.exp (-c' * d₁ * (τ - T₀))) := by
        have h1 : ψ (φ τ) ≤ (2 * C_S4 * M) * 1 *
            Real.exp (c' * (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re -
              c' * (2 * Real.pi / 3) * b₀) :=
          hψ_bd.trans (by gcongr)
        calc ψ (φ τ) ≤ (2 * C_S4 * M) *
              Real.exp (c' * (chartPhiV ((1 / 2 : ℂ) + Complex.I * (τ : ℂ)) (b₀ : ℂ)).re -
                c' * (2 * Real.pi / 3) * b₀) := by rw [mul_one] at h1; exact h1
          _ ≤ (2 * C_S4 * M) * (Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
                Real.exp (-(3 * d₀ / 4) * c') * Real.exp (-c' * d₁ * (τ - T₀))) := by gcongr
      calc ψ (φ τ) * φ' τ
          ≤ ((2 * C_S4 * M) * (Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
              Real.exp (-(3 * d₀ / 4) * c') * Real.exp (-c' * d₁ * (τ - T₀)))) *
              (c' * C_om' * (1 + τ)) := mul_le_mul hψ_ub hφ'_ub hφ'_nn (by positivity [hM_pos])
        _ = K * (c' * ((1 + τ) * Real.exp (-c' * d₁ * (τ - T₀)))) := by
            dsimp [K]; ring
    have hmid_cont : Continuous midlineY :=
      continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_midlineY τ).continuousAt
    have hcont_l : ContinuousOn (fun τ => ψ (φ τ) * φ' τ) (Icc T₀ T) :=
      ((hψ_cont.comp (continuous_const.mul hmid_cont)).continuousOn).mul
        (hφ'_cont.mono (by rw [uIcc_of_le hT]))
    have hcont_r : ContinuousOn (fun τ => K * (c' * ((1 + τ) * Real.exp (-c' * d₁ * (τ - T₀)))))
        (Icc T₀ T) := by fun_prop
    have hint_le : ∫ τ in T₀..T, ψ (φ τ) * φ' τ ≤
        ∫ τ in T₀..T, K * (c' * ((1 + τ) * Real.exp (-c' * d₁ * (τ - T₀)))) :=
      intervalIntegral.integral_mono_on hT (hcont_l.intervalIntegrable_of_Icc hT)
        (hcont_r.intervalIntegrable_of_Icc hT) hpt_bd
    let F_ant : ℝ → ℝ := fun τ =>
      -((1 + τ) / (c' * d₁) + 1 / (c' * d₁) ^ 2) * Real.exp (-c' * d₁ * (τ - T₀))
    have hF_deriv : ∀ τ ∈ uIcc T₀ T,
        HasDerivAt F_ant ((1 + τ) * Real.exp (-c' * d₁ * (τ - T₀))) τ := fun τ _ => by
      have hcd_ne : c' * d₁ ≠ 0 := by positivity
      have ha1 : HasDerivAt (fun x : ℝ => -((1 + x) / (c' * d₁) + 1 / (c' * d₁) ^ 2))
          (-(1 / (c' * d₁))) τ := by
        have h1 := ((hasDerivAt_const τ (1 : ℝ)).add (hasDerivAt_id τ)).div_const (c' * d₁)
        exact (h1.add (hasDerivAt_const τ _)).neg.congr_deriv (by ring)
      have he1 : HasDerivAt (fun x : ℝ => Real.exp (-c' * d₁ * (x - T₀)))
          ((-c' * d₁) * Real.exp (-c' * d₁ * (τ - T₀))) τ := by
        have hlin : HasDerivAt (fun x : ℝ => -c' * d₁ * (x - T₀)) (-c' * d₁) τ := by
          simpa using ((hasDerivAt_id τ).sub_const T₀).const_mul (-c' * d₁)
        simpa [mul_comm] using hlin.exp
      have hmul := ha1.mul he1
      refine hmul.congr_deriv ?_
      field_simp [hcd_ne]
      ring
    have hcont_exp : ContinuousOn (fun τ => (1 + τ) * Real.exp (-c' * d₁ * (τ - T₀))) (uIcc T₀ T) := by
      fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv hcont_exp.intervalIntegrable
    have hFT_le : F_ant T ≤ 0 := by
      dsimp [F_ant]
      have h1 : 0 ≤ (1 + T) / (c' * d₁) + 1 / (c' * d₁) ^ 2 := by
        have : 0 ≤ 1 + T := by linarith only [hT, hT₀]
        positivity
      have h2 : 0 ≤ Real.exp (-c' * d₁ * (T - T₀)) := (Real.exp_pos _).le
      nlinarith only [h1, h2]
    have hF0_eq : -F_ant T₀ = (1 + T₀) / (c' * d₁) + 1 / (c' * d₁) ^ 2 := by
      simp [F_ant]
    have hF0_ub : c' * (-F_ant T₀) ≤ (1 + T₀ + 1 / d₁) / d₁ := by
      rw [hF0_eq]
      have hinv : 1 / (c' * d₁ ^ 2) ≤ 1 / d₁ ^ 2 := by
        have h1 : d₁ ^ 2 ≤ c' * d₁ ^ 2 := le_mul_of_one_le_left (sq_nonneg d₁) (by linarith only [hc'_10000])
        exact one_div_le_one_div_of_le (sq_pos_of_pos hd₁) h1
      calc c' * ((1 + T₀) / (c' * d₁) + 1 / (c' * d₁) ^ 2)
          = (1 + T₀) / d₁ + 1 / (c' * d₁ ^ 2) := by
            field_simp [hc'_pos.ne', hd₁.ne']
        _ ≤ (1 + T₀) / d₁ + 1 / d₁ ^ 2 := by linarith only [hinv]
        _ = (1 + T₀ + 1 / d₁) / d₁ := by field_simp [hd₁.ne']
    have hint_rhs : ∫ τ in T₀..T, K * (c' * ((1 + τ) * Real.exp (-c' * d₁ * (τ - T₀)))) ≤
        K * ((1 + T₀ + 1 / d₁) / d₁) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hftc]
      have hle : F_ant T - F_ant T₀ ≤ -F_ant T₀ := by linarith only [hFT_le]
      calc K * (c' * (F_ant T - F_ant T₀))
          ≤ K * (c' * (-F_ant T₀)) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hle hc'_pos.le) hK_nn
        _ ≤ K * ((1 + T₀ + 1 / d₁) / d₁) := mul_le_mul_of_nonneg_left hF0_ub hK_nn
    calc ∫ τ in T₀..T, ψ (φ τ) * φ' τ
        ≤ ∫ τ in T₀..T, K * (c' * ((1 + τ) * Real.exp (-c' * d₁ * (τ - T₀)))) := hint_le
      _ ≤ K * ((1 + T₀ + 1 / d₁) / d₁) := hint_rhs
      _ = (C_tail / 2) * M * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
            Real.exp (-(3 * d₀ / 4) * c') := by
          dsimp [K, C_tail]; ring
  have htend_top : Tendsto (fun T : ℝ => -c' * midlineY T) atTop atTop := by
    have h1 : Tendsto (fun T : ℝ => -midlineY T) atTop atTop :=
      tendsto_neg_atBot_atTop.comp tendsto_im_chartOmega_midline_atTop
    have h2 := h1.const_mul_atTop hc'_pos
    simpa [show (fun T => c' * (-midlineY T)) = fun T => -c' * midlineY T by ext T; ring] using h2
  have htail_Ioi_of : ∀ {b₀ : ℝ}, xiStar / 2 ≤ b₀ → b₀ ≤ 2 * xiStar →
      (2 * Real.pi / 3) * |b₀ - xiStar| ≤ d₀ / 4 →
      let t₀ : ℝ := c' * b₀ ^ 2 / 3
      IntegrableOn (fun η : ℝ => ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
          mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖) (Ioi η₀) ∧
        ∫ η in Ioi η₀,
            ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
              mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖ ≤
          (C_tail / 2) * M * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
            Real.exp (-(3 * d₀ / 4) * c') := by
    intro b₀ hb₀_lo hb₀_hi hb₀_gap t₀
    have hb₀_pos : 0 < b₀ := by have := xiStar_pos; linarith only [hb₀_lo, this]
    have ht₀_pos : 0 < t₀ := by dsimp [t₀]; have := sq_pos_of_pos hb₀_pos; positivity
    let ψ : ℝ → ℝ := fun η =>
      ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
        mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖
    have hψ_cont : Continuous ψ := by
      have ht_cont : Continuous fun η : ℝ => (t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) := by
        have ht₀_ne : (t₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₀_pos.ne'
        simp_rw [Complex.cpow_def_of_ne_zero ht₀_ne]
        exact Complex.continuous_exp.comp (continuous_const.mul (by fun_prop))
      exact (ht_cont.mul hm_cont).norm
    let B := (C_tail / 2) * M * Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) *
      Real.exp (-(3 * d₀ / 4) * c')
    have hbound_ev : ∀ᶠ T in atTop, ∫ η in η₀..(-c' * midlineY T), ‖ψ η‖ ≤ B := by
      filter_upwards [Ici_mem_atTop T₀] with T hT
      have h1 := htail_Icc hb₀_lo hb₀_hi hb₀_gap T (mem_Ici.mp hT)
      have heq_int : ∫ η in η₀..(-c' * midlineY T), ‖ψ η‖ = ∫ η in η₀..(-c' * midlineY T), ψ η :=
        intervalIntegral.integral_congr fun η _ => by simp [ψ]
      exact heq_int ▸ h1
    have hIoi_int : IntegrableOn ψ (Ioi η₀) :=
      integrableOn_Ioi_of_intervalIntegral_norm_bounded B η₀
        (fun T => hψ_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        htend_top hbound_ev
    have htend_int := intervalIntegral_tendsto_integral_Ioi η₀ hIoi_int htend_top
    have hbd_res : ∫ η in Ioi η₀, ψ η ≤ B :=
      le_of_tendsto htend_int (by
        filter_upwards [Ici_mem_atTop T₀] with T hT
        exact htail_Icc hb₀_lo hb₀_hi hb₀_gap T (mem_Ici.mp hT))
    exact ⟨hIoi_int, hbd_res⟩
  refine ⟨?_, fun hb₀_lo hb₀_hi hb₀_gap => (htail_Ioi_of hb₀_lo hb₀_hi hb₀_gap).2⟩
  -- VerticalIntegrable on `Re z = 1 / 2` using `b₀ = xiStar`
  have hxi_pos := xiStar_pos
  have hxi_Ioi := (htail_Ioi_of (b₀ := xiStar) (by linarith only [hxi_pos]) (by linarith only [hxi_pos])
    (by simp [abs_zero]; positivity)).1
  let t_ref := c' * xiStar ^ 2 / 3
  have ht_ref_pos : 0 < t_ref := by positivity [xiStar_pos]
  let ψ_ref : ℝ → ℝ := fun η =>
    ‖(t_ref : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
      mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖
  have hψ_ref_cont : Continuous ψ_ref := by
    have ht_cont : Continuous fun η : ℝ => (t_ref : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) := by
      have ht_ne : (t_ref : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_ref_pos.ne'
      simp_rw [Complex.cpow_def_of_ne_zero ht_ne]
      exact Complex.continuous_exp.comp (continuous_const.mul (by fun_prop))
    exact (ht_cont.mul hm_cont).norm
  have hψ_even : ∀ η : ℝ, ψ_ref (-η) = ψ_ref η := fun η => by
    dsimp [ψ_ref]
    have hconj : starRingEnd ℂ ((t_ref : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
          mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))) =
        (t_ref : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * ((-η : ℝ) : ℂ)) *
          mellinTransformG g (1 / 2 + Complex.I * ((-η : ℝ) : ℂ)) := by
      have harg : (t_ref : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg ht_ref_pos.le]; exact Real.pi_pos.ne
      have hcp := Complex.cpow_conj (t_ref : ℂ) (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) harg
      rw [Complex.conj_ofReal] at hcp
      rw [map_mul, ← hcp, ← mellinTransformG_conj]
      simp only [map_add, map_sub, map_neg, map_div₀, map_one, map_ofNat, map_mul,
        Complex.conj_ofReal, Complex.conj_I]
      congr 2 <;> push_cast <;> ring
    rw [← hconj, Complex.norm_conj]
  have hψ_Iio : IntegrableOn ψ_ref (Iio (-η₀)) := by
    have hind : Integrable ((Ioi η₀).indicator ψ_ref) :=
      (integrable_indicator_iff measurableSet_Ioi).mpr hxi_Ioi
    have hind_neg : Integrable (fun η : ℝ => (Ioi η₀).indicator ψ_ref (-η)) := hind.comp_neg
    have hind_eq : (fun η : ℝ => (Ioi η₀).indicator ψ_ref (-η)) = (Iio (-η₀)).indicator ψ_ref := by
      ext η
      by_cases h : η < -η₀
      · have h1 : -η ∈ Ioi η₀ := mem_Ioi.mpr (by linarith only [h])
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem (mem_Iio.mpr h), hψ_even]
      · have h1 : -η ∉ Ioi η₀ := fun hm => h (by have := mem_Ioi.mp hm; linarith only [this])
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (by simpa [mem_Iio] using h)]
    rw [hind_eq] at hind_neg
    exact (integrable_indicator_iff measurableSet_Iio).mp hind_neg
  have hψ_Icc : IntegrableOn ψ_ref (Icc (-η₀) η₀) := hψ_ref_cont.continuousOn.integrableOn_Icc
  have hψ_all : Integrable ψ_ref := by
    have huniv : (Iio (-η₀) ∪ Icc (-η₀) η₀) ∪ Ioi η₀ = univ := by
      ext η
      simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
      rcases lt_or_ge η (-η₀) with h1 | h1
      · left; left; exact h1
      · rcases le_or_gt η η₀ with h2 | h2
        · left; right; exact ⟨h1, h2⟩
        · right; exact h2
    rw [← integrableOn_univ, ← huniv]
    exact (hψ_Iio.union hψ_Icc).union hxi_Ioi
  have hm_eq_mellin : ∀ η : ℝ, mellin (fun t : ℝ => (g t : ℂ)) ((1 / 2 : ℝ) + (η : ℝ) * Complex.I) =
      mellinTransformG g (1 / 2 + Complex.I * (η : ℂ)) := fun η => by
    unfold mellin mellinTransformG
    rw [show ((1 / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I = 1 / 2 + Complex.I * (η : ℂ) by
      push_cast; ring]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [smul_eq_mul, mul_comm]
  have ht_ref_norm : ∀ η : ℝ, ‖(t_ref : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ))‖ =
      t_ref ^ (-(1 / 2 : ℝ)) := fun η => by
    have ht_ne : (t_ref : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_ref_pos.ne'
    rw [Complex.cpow_def_of_ne_zero ht_ne, Complex.norm_exp]
    have h12 : (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)).re = -(1 / 2 : ℝ) := by
      simp [Complex.sub_re, Complex.mul_re]
    have hre : (Complex.log (t_ref : ℂ) * (-(1 / 2 : ℂ) - Complex.I * (η : ℂ))).re =
        -(1 / 2 : ℝ) * Real.log t_ref := by
      rw [← Complex.ofReal_log ht_ref_pos.le, Complex.re_ofReal_mul, h12]; ring
    rw [hre, Real.rpow_def_of_pos ht_ref_pos]; congr 1; ring
  have hm_norm_int : Integrable (fun η : ℝ => t_ref ^ (1 / 2 : ℝ) * ψ_ref η) :=
    hψ_all.const_mul _
  refine hm_norm_int.mono' (Continuous.aestronglyMeasurable (hm_cont.congr fun η => (hm_eq_mellin η).symm)) ?_
  · filter_upwards with η
    rw [hm_eq_mellin η]
    have hnorm_m : ‖mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖ =
        t_ref ^ (1 / 2 : ℝ) * ψ_ref η := by
      dsimp [ψ_ref]
      rw [norm_mul, ht_ref_norm η, ← mul_assoc, ← Real.rpow_add ht_ref_pos]
      norm_num
    exact hnorm_m.le

/-! ### 4. Mellin inversion and real-axis truncation error -/

private lemma mellinTransformG_conj_line {g : ℝ → ℝ} (η : ℝ) :
    ‖mellinTransformG g (1 / 2 + Complex.I * ((-η : ℝ) : ℂ))‖ =
      ‖mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖ := by
  have h1 : starRingEnd ℂ (mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))) =
      mellinTransformG g (1 / 2 + Complex.I * ((-η : ℝ) : ℂ)) := by
    rw [← mellinTransformG_conj]
    congr 1
    apply Complex.ext <;> simp
  rw [← h1, Complex.norm_conj]

lemma virasoroV_C_inner_bound :
    ∃ c_V C_V : ℝ, 39 ≤ c_V ∧ 0 < C_V ∧
      ∀ {c' : ℝ}, c_V ≤ c' → ∀ {u : ℂ},
        u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) →
        let b := virasoroBChart c' u
        ‖V_C (c' : ℂ) (virasoroDeltaChartC c' u)‖ ≤
          C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (tipL b).re) := by
  let c_V : ℝ := max 39 ((6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ))
  let C_V : ℝ := 9 * kappa0 / (2 * xiStar)
  refine ⟨c_V, C_V, le_max_left _ _, by have := kappa0_pos; have := xiStar_pos; positivity,
    fun {c'} hc' {u} hu => ?_⟩
  let b : ℂ := virasoroBChart c' u
  have hc'_39 : 39 ≤ c' := (le_max_left _ _).trans hc'
  have hc'_pos : 0 < c' := by linarith
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hbd := virasoroBChart_inner_bounds hc'_pos hu
  let ζ : ℂ := ((tipEps c')⁻¹ : ℝ) * (b - (xiStar : ℂ))
  have hb_sc : bScale c' ζ = b := by
    unfold bScale ζ
    have h1 : ((tipEps c' : ℝ) : ℂ) * (((tipEps c')⁻¹ : ℝ) : ℂ) = 1 := by
      push_cast; exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hε_pos.ne')
    calc (xiStar : ℂ) + ((tipEps c' : ℝ) : ℂ) * ((((tipEps c')⁻¹ : ℝ) : ℂ) * (b - (xiStar : ℂ)))
        = (xiStar : ℂ) + (((tipEps c' : ℝ) : ℂ) * (((tipEps c')⁻¹ : ℝ) : ℂ)) * (b - (xiStar : ℂ)) := by ring
      _ = b := by rw [h1, one_mul]; ring
  have hεζ_eq : tipEps c' * ‖ζ‖ = ‖b - (xiStar : ℂ)‖ := by
    dsimp [ζ]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hε_pos.le)]
    field_simp [hε_pos.ne']
  have hεζ_3 : tipEps c' * ‖ζ‖ ≤ chartParams.ρ₃_tip := by
    rw [hεζ_eq]; exact hbd.2.1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hTW := virasoro_lemma_T3_W hc'_39 hεζ_3
  rw [hb_sc] at hTW
  have h6_pos : (0 : ℝ) < 6 * (chartParams.C_W_tip + 1) := by linarith [chartParams.hCW_tip_nn]
  have hpow_le : (6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ) ≤ c' := (le_max_right _ _).trans hc'
  have h23 : 6 * (chartParams.C_W_tip + 1) ≤ c' ^ (2 / 3 : ℝ) := by
    calc 6 * (chartParams.C_W_tip + 1)
        = ((6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_mul h6_pos.le]; norm_num
      _ ≤ c' ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hpow_le (by norm_num)
  have hε_le : tipEps c' ≤ 1 / (6 * (chartParams.C_W_tip + 1)) := by
    unfold tipEps; rw [Real.rpow_neg hc'_pos.le, ← one_div]
    exact one_div_le_one_div_of_le h6_pos h23
  have hinv_le : 1 / c' ≤ 1 / (6 * (chartParams.C_W_tip + 1)) := by
    have h1 : (1 : ℝ) ≤ 6 * (chartParams.C_W_tip + 1) := by linarith [chartParams.hCW_tip_nn]
    have h2 : 6 * (chartParams.C_W_tip + 1) ≤ (6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ) := by
      calc 6 * (chartParams.C_W_tip + 1) = (6 * (chartParams.C_W_tip + 1)) ^ (1 : ℝ) :=
            (Real.rpow_one _).symm
        _ ≤ (6 * (chartParams.C_W_tip + 1)) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    exact one_div_le_one_div_of_le h6_pos (h2.trans hpow_le)
  have hεζ_W : tipEps c' * ‖ζ‖ ≤ 1 / (6 * (chartParams.C_W_tip + 1)) := by
    rw [hεζ_eq]
    exact hbd.2.1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hrel_half : chartParams.C_W_tip * (tipEps c' * (1 + ‖ζ‖) + 1 / c') ≤ 1 / 2 := by
    have hsum : tipEps c' * (1 + ‖ζ‖) + 1 / c' ≤ 3 * (1 / (6 * (chartParams.C_W_tip + 1))) := by
      have : tipEps c' * (1 + ‖ζ‖) = tipEps c' + tipEps c' * ‖ζ‖ := by ring
      linarith
    calc chartParams.C_W_tip * (tipEps c' * (1 + ‖ζ‖) + 1 / c')
        ≤ chartParams.C_W_tip * (3 * (1 / (6 * (chartParams.C_W_tip + 1)))) :=
          mul_le_mul_of_nonneg_left hsum chartParams.hCW_tip_nn
      _ = (chartParams.C_W_tip / (chartParams.C_W_tip + 1)) * (1 / 2) := by
          have hp : chartParams.C_W_tip + 1 ≠ 0 := by linarith [chartParams.hCW_tip_nn]
          field_simp [hp]; ring
      _ ≤ 1 * (1 / 2) := by
          gcongr; exact (div_le_one (by linarith [chartParams.hCW_tip_nn])).mpr (by linarith)
      _ = 1 / 2 := one_mul _
  have hkap_norm : ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ =
      kappa0 * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
    have hkap_pos : 0 < kappaC c' := mul_pos (Real.rpow_pos_of_pos hc'_pos _) kappa0_pos
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkap_pos, Complex.norm_exp,
      Complex.re_ofReal_mul]
    unfold kappaC; ring
  have hW_ub : ‖W_C c' b‖ ≤
      (3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
    have htri := norm_sub_norm_le (W_C c' b) ((kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b))
    dsimp only at hTW
    have hmul := mul_le_mul_of_nonneg_right hrel_half
      (norm_nonneg ((kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)))
    have h1 : ‖W_C c' b‖ ≤ (3 / 2 : ℝ) * ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ := by
      linarith only [htri, hTW, hmul]
    calc ‖W_C c' b‖ ≤ (3 / 2 : ℝ) * (kappa0 * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) := by
          rwa [hkap_norm] at h1
      _ = (3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by ring
  have hW_rel : W_C c' b = ((tipEps c' * (2 * c' / 3) : ℝ) : ℂ) * b * V_C (c' : ℂ) (virasoroDeltaChartC c' u) := by
    unfold W_C
    rw [virasoroDeltaChartC_eq_bChart_sq u]
    push_cast; ring
  have hb_norm_lb : xiStar / 2 ≤ ‖b‖ := hbd.2.2.1.trans (Complex.re_le_norm _)
  have hb_pos : 0 < ‖b‖ := lt_of_lt_of_le (half_pos xiStar_pos) hb_norm_lb
  have hcoef_eq : tipEps c' * (2 * c' / 3) = (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) := by
    unfold tipEps
    calc c' ^ (-(2 / 3 : ℝ)) * (2 * c' / 3) = (2 / 3 : ℝ) * (c' * c' ^ (-(2 / 3 : ℝ))) := by ring
      _ = (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_one_add' hc'_pos.le (by norm_num : (1 : ℝ) + -(2 / 3 : ℝ) ≠ 0)]; norm_num
  have hcoef_pos : 0 < (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖b‖ := by positivity
  have hnorm_V : ‖W_C c' b‖ = ((2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖b‖) * ‖V_C (c' : ℂ) (virasoroDeltaChartC c' u)‖ := by
    rw [hW_rel, norm_mul, norm_mul, Complex.norm_real, hcoef_eq,
      Real.norm_of_nonneg (by positivity)]
  have hV_div := div_le_div_of_nonneg_right (hnorm_V ▸ hW_ub) hcoef_pos.le
  rw [mul_div_cancel_left₀ _ hcoef_pos.ne'] at hV_div
  have hc_pow : c' ^ (-(1 / 6 : ℝ)) / c' ^ (1 / 3 : ℝ) = c' ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_sub hc'_pos]; norm_num
  have hcoef_lb : (xiStar / 3) * c' ^ (1 / 3 : ℝ) ≤ (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖b‖ := by
    calc (xiStar / 3) * c' ^ (1 / 3 : ℝ) = (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * (xiStar / 2) := by ring
      _ ≤ (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖b‖ := by gcongr
  have hxi_pos := xiStar_pos
  have hkap0_pos := kappa0_pos
  calc ‖V_C (c' : ℂ) (virasoroDeltaChartC c' u)‖
      ≤ ((3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) /
          ((2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖b‖) := hV_div
    _ ≤ ((3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) /
          ((xiStar / 3) * c' ^ (1 / 3 : ℝ)) := by
        gcongr
    _ = C_V * (c' ^ (-(1 / 6 : ℝ)) / c' ^ (1 / 3 : ℝ)) * Real.exp (c' * (tipL b).re) := by
        dsimp [C_V]; field_simp [hxi_pos.ne']; ring
    _ = _ := by rw [hc_pow]

private lemma real_mellin_truncation_bound
    {c' T₀ d₀ C_tail C_V C_dxi x b₀ t₀ : ℝ}
    (hc'_10000 : 10000 ≤ c') (hT₀_pos : 0 < T₀)
    (hC_tail_pos : 0 < C_tail) (hCV_pos : 0 < C_V) (hCdxi_pos : 0 < C_dxi)
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    (hb_eq : virasoroBChart c' (x : ℂ) = (b₀ : ℂ))
    (ht_eq : virasoroDeltaChartC c' (x : ℂ) = (t₀ : ℂ))
    (ht₀_pos : 0 < t₀)
    (ht₀_eq : t₀ = c' * b₀ ^ 2 / 3)
    (hVI : VerticalIntegrable (mellin fun t : ℝ => (g t : ℂ)) (1 / 2))
    (htail_Ioi_bd : ∫ η in Ioi (-c' * midlineY T₀),
        ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
          mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖ ≤
      (C_tail / 2) * virasoroProblem.cardyNorm (c' / 12) g *
        Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c'))
    (hV_bd : ‖V_C (c' : ℂ) (t₀ : ℂ)‖ ≤
      C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (2 * Real.pi / 3) * b₀))
    (hd_bd : ‖deriv (virasoroDeltaChartC c') (x : ℂ)‖ ≤ C_dxi * c' ^ (1 / 3 : ℝ)) :
    ‖virasoroPsiTilde c' g (x : ℂ) - truncatedMellinP c' T₀ g (x : ℂ)‖ ≤
      (C_V * C_dxi * C_tail / (2 * Real.pi)) * Real.exp (-(3 * d₀ / 4) * c') := by
  have hc'_24 : 24 ≤ c' := by linarith only [hc'_10000]
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith only [hc'_10000]
  have h12_eq : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  have hf_conv : MellinConvergent (fun t : ℝ => (g t : ℂ)) ((1 / 2 : ℝ) : ℂ) := by
    unfold MellinConvergent
    rw [h12_eq]
    refine (integrableOn_mellinTransformG ha hg (z := (1 / 2 : ℂ)) (by norm_num)).congr_fun
      (fun t _ => by rw [smul_eq_mul, mul_comm]) measurableSet_Ioi
  have hfx_cont : ContinuousAt (fun t : ℝ => (g t : ℂ)) t₀ :=
    Complex.continuous_ofReal.continuousAt.comp
      ((hg.cont.continuousWithinAt (mem_Ici.mpr ht₀_pos.le)).continuousAt (Ici_mem_nhds ht₀_pos))
  have hm_inv := mellinInv_mellin_eq (1 / 2 : ℝ) (fun t : ℝ => (g t : ℂ)) ht₀_pos hf_conv hVI hfx_cont
  have hgt_eq : (g t₀ : ℂ) = (1 / (2 * (Real.pi : ℂ))) *
      ∫ η : ℝ, (t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
        mellinTransformG g (1 / 2 + Complex.I * (η : ℂ)) := by
    rw [← hm_inv]
    unfold mellinInv
    rw [Complex.real_smul]
    have h12pi : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by push_cast; rfl
    rw [h12pi]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    dsimp only
    rw [smul_eq_mul]
    have harg_eq : ((1 / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I = 1 / 2 + Complex.I * (η : ℂ) := by
      push_cast; ring
    have hpow_eq : -(((1 / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I) =
        -(1 / 2 : ℂ) - Complex.I * (η : ℂ) := by
      push_cast; ring
    rw [hpow_eq, harg_eq]
    congr 1
    unfold mellin mellinTransformG
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [smul_eq_mul, mul_comm]
  have hPsi_eq : virasoroPsiTilde c' g (x : ℂ) =
      -(deriv (virasoroDeltaChartC c') (x : ℂ) / (virasoroProblem.cardyNorm (c' / 12) g : ℂ)) *
        V_C (c' : ℂ) (t₀ : ℂ) * ((1 / (2 * (Real.pi : ℂ))) *
        ∫ η : ℝ, (t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
          mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))) := by
    unfold virasoroPsiTilde
    rw [hb_eq, ht_eq, hankelContinuation_ofReal hc'_pos hg b₀, ← ht₀_eq, hgt_eq]
    ring
  have hP_eq : truncatedMellinP c' T₀ g (x : ℂ) =
      -(deriv (virasoroDeltaChartC c') (x : ℂ) / (virasoroProblem.cardyNorm (c' / 12) g : ℂ)) *
        V_C (c' : ℂ) (t₀ : ℂ) * ((1 / (2 * (Real.pi : ℂ))) *
        ∫ η in (-(-c' * midlineY T₀))..(-c' * midlineY T₀),
          (t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
            mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))) := by
    unfold truncatedMellinP
    dsimp only
    rw [ht_eq, mul_assoc]
    exact congrArg _ (truncatedMellinP_real_integral_eq hc'_24 T₀ hg ht₀_pos)
  set η₀ := -c' * midlineY T₀
  have hY_T₀_neg : midlineY T₀ < 0 := by
    have h1 := im_chartOmega_midline_strictAnti hT₀_pos
    dsimp only at h1
    rw [Complex.ofReal_zero, mul_zero, add_zero, chartOmega_half, Complex.zero_im] at h1
    exact h1
  have hη₀_pos : 0 < η₀ := by dsimp [η₀]; nlinarith only [hc'_pos, hY_T₀_neg]
  let G : ℝ → ℂ := fun η =>
    (t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
      mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))
  have hG_int : Integrable G := by
    have ht_eq_m : ∀ η : ℝ, G η = (t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
        mellin (fun s : ℝ => (g s : ℂ)) (((1 / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I) := fun η => by
      dsimp [G]; congr 1; unfold mellin mellinTransformG
      rw [show ((1 / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I = 1 / 2 + Complex.I * (η : ℂ) by
        push_cast; ring]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [smul_eq_mul, mul_comm]
    have ht₀_norm : ∀ η : ℝ, ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ))‖ =
        t₀ ^ (-(1 / 2 : ℝ)) := fun η => by
      have ht_ne : (t₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₀_pos.ne'
      rw [Complex.cpow_def_of_ne_zero ht_ne, Complex.norm_exp]
      have hre : (Complex.log (t₀ : ℂ) * (-(1 / 2 : ℂ) - Complex.I * (η : ℂ))).re =
          -(1 / 2 : ℝ) * Real.log t₀ := by
        rw [← Complex.ofReal_log ht₀_pos.le]; simp [Complex.mul_re]; ring
      rw [hre, Real.rpow_def_of_pos ht₀_pos]; congr 1; ring
    have ht_cont : Continuous fun η : ℝ => (t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) := by
      have ht_ne : (t₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₀_pos.ne'
      simp_rw [Complex.cpow_def_of_ne_zero ht_ne]
      have hexp_arg_cont : Continuous fun η : ℝ => -(1 / 2 : ℂ) - Complex.I * (η : ℂ) := by
        fun_prop
      exact Complex.continuous_exp.comp (continuous_const.mul hexp_arg_cont)
    have hmeas : AEStronglyMeasurable G volume := by
      rw [show G = fun η : ℝ => (t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
          mellin (fun s : ℝ => (g s : ℂ)) (((1 / 2 : ℝ) : ℂ) + (η : ℂ) * Complex.I) from funext ht_eq_m]
      exact ht_cont.aestronglyMeasurable.mul hVI.aestronglyMeasurable
    refine (hVI.norm.const_mul (t₀ ^ (-(1 / 2 : ℝ)))).mono' hmeas ?_
    filter_upwards with η
    change ‖G η‖ ≤ _
    rw [ht_eq_m η, norm_mul, ht₀_norm η]
  have hdiff_eq : (∫ η : ℝ, G η) - ∫ η in (-η₀)..η₀, G η =
      (∫ η in Ioi η₀, G η) + ∫ η in Iic (-η₀), G η := by
    have hint_Iic : IntegrableOn G (Iic (-η₀)) := hG_int.integrableOn
    have hint_Ioc : IntegrableOn G (Ioc (-η₀) η₀) := hG_int.integrableOn
    have h_univ : ∫ η : ℝ, G η = (∫ η in Iic η₀, G η) + ∫ η in Ioi η₀, G η := by
      have hu := (MeasureTheory.integral_add_compl (s := Iic η₀) measurableSet_Iic hG_int).symm
      rwa [compl_Iic] at hu
    have h_split : ∫ η in Iic η₀, G η =
        (∫ η in Iic (-η₀), G η) + ∫ η in Ioc (-η₀) η₀, G η := by
      have hdisj : Disjoint (Iic (-η₀)) (Ioc (-η₀) η₀) :=
        Set.disjoint_left.mpr fun s hs1 hs2 => by
          have h1 := mem_Iic.mp hs1; have h2 := (mem_Ioc.mp hs2).1; linarith only [h1, h2]
      have hunion : Iic (-η₀) ∪ Ioc (-η₀) η₀ = Iic η₀ :=
        Set.Iic_union_Ioc_eq_Iic (by linarith only [hη₀_pos])
      rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint_Iic hint_Ioc]
    have hioc_eq : ∫ η in (-η₀)..η₀, G η = ∫ η in Ioc (-η₀) η₀, G η :=
      intervalIntegral.integral_of_le (by linarith only [hη₀_pos])
    rw [h_univ, h_split, hioc_eq]
    ring
  have htail_symm : ∫ η in Iic (-η₀), ‖G η‖ = ∫ η in Ioi η₀, ‖G η‖ := by
    have hcomp : ∫ η in Iic (-η₀), ‖G η‖ = ∫ η in Ioi η₀, ‖G (-η)‖ := by
      have h1 := integral_comp_neg_Iic (-η₀) (fun η : ℝ => ‖G (-η)‖)
      simpa only [neg_neg] using h1
    rw [hcomp]
    refine setIntegral_congr_fun measurableSet_Ioi fun η _ => ?_
    have hconj : starRingEnd ℂ (G η) = G (-η) := by
      dsimp [G]
      have harg : (t₀ : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg ht₀_pos.le]; exact Real.pi_pos.ne
      have hcp := Complex.cpow_conj (t₀ : ℂ) (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) harg
      rw [Complex.conj_ofReal] at hcp
      have hc1 : starRingEnd ℂ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) =
          -(1 / 2 : ℂ) - Complex.I * ((-η : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      have hc2 : starRingEnd ℂ (1 / 2 + Complex.I * (η : ℂ)) =
          1 / 2 + Complex.I * ((-η : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [map_mul, ← hcp, ← mellinTransformG_conj, hc1, hc2]
    rw [← hconj, Complex.norm_conj]
  have htail_Ioi_norm : ‖∫ η in Ioi η₀, G η‖ ≤
      (C_tail / 2) * virasoroProblem.cardyNorm (c' / 12) g *
        Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') :=
    (norm_integral_le_integral_norm _).trans htail_Ioi_bd
  have htail_Iic_norm : ‖∫ η in Iic (-η₀), G η‖ ≤
      (C_tail / 2) * virasoroProblem.cardyNorm (c' / 12) g *
        Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') := by
    calc ‖∫ η in Iic (-η₀), G η‖ ≤ ∫ η in Iic (-η₀), ‖G η‖ := norm_integral_le_integral_norm _
      _ = ∫ η in Ioi η₀, ‖G η‖ := htail_symm
      _ ≤ _ := htail_Ioi_bd
  have hdiff_norm : ‖(∫ η : ℝ, G η) - ∫ η in (-η₀)..η₀, G η‖ ≤
      C_tail * virasoroProblem.cardyNorm (c' / 12) g *
        Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') := by
    rw [hdiff_eq]
    calc ‖(∫ η in Ioi η₀, G η) + ∫ η in Iic (-η₀), G η‖
        ≤ ‖∫ η in Ioi η₀, G η‖ + ‖∫ η in Iic (-η₀), G η‖ := norm_add_le _ _
      _ ≤ _ := by linarith only [htail_Ioi_norm, htail_Iic_norm]
  have hsub_eq : virasoroPsiTilde c' g (x : ℂ) - truncatedMellinP c' T₀ g (x : ℂ) =
      -(deriv (virasoroDeltaChartC c') (x : ℂ) / (virasoroProblem.cardyNorm (c' / 12) g : ℂ)) *
        V_C (c' : ℂ) (t₀ : ℂ) * (1 / (2 * (Real.pi : ℂ))) *
        ((∫ η : ℝ, G η) - ∫ η in (-η₀)..η₀, G η) := by
    rw [hPsi_eq, hP_eq]; ring
  rw [hsub_eq, norm_mul, norm_mul, norm_mul, norm_neg, norm_div]
  have hM_norm : ‖(virasoroProblem.cardyNorm (c' / 12) g : ℂ)‖ =
      virasoroProblem.cardyNorm (c' / 12) g := by
    rw [Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
  have h2pi_norm : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hM_norm, h2pi_norm]
  have hc_pow_le1 : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    rw [← Real.rpow_add hc'_pos]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [hc'_10000]) (by norm_num)
  have hexp_cancel : Real.exp (c' * (2 * Real.pi / 3) * b₀) *
      Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc (‖deriv (virasoroDeltaChartC c') (x : ℂ)‖ / virasoroProblem.cardyNorm (c' / 12) g) *
          ‖V_C (c' : ℂ) (t₀ : ℂ)‖ * (1 / (2 * Real.pi)) *
          ‖(∫ η : ℝ, G η) - ∫ η in (-η₀)..η₀, G η‖
      ≤ ((C_dxi * c' ^ (1 / 3 : ℝ)) / virasoroProblem.cardyNorm (c' / 12) g) *
          (C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (2 * Real.pi / 3) * b₀)) *
          (1 / (2 * Real.pi)) *
          (C_tail * virasoroProblem.cardyNorm (c' / 12) g *
            Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c')) := by
        gcongr
    _ = (C_V * C_dxi * C_tail / (2 * Real.pi)) *
          (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ))) *
          (Real.exp (c' * (2 * Real.pi / 3) * b₀) * Real.exp (-(c' * (2 * Real.pi / 3) * b₀))) *
          Real.exp (-(3 * d₀ / 4) * c') := by
        field_simp [hM_pos.ne', Real.pi_pos.ne']
    _ = (C_V * C_dxi * C_tail / (2 * Real.pi)) *
          (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(3 * d₀ / 4) * c') := by
        rw [hexp_cancel, mul_one]
    _ ≤ (C_V * C_dxi * C_tail / (2 * Real.pi)) * 1 *
          Real.exp (-(3 * d₀ / 4) * c') := by
        gcongr
    _ = (C_V * C_dxi * C_tail / (2 * Real.pi)) * Real.exp (-(3 * d₀ / 4) * c') := by ring

lemma truncatedMellinP_real_err :
    ∃ c_real C_real c₀_real : ℝ,
      10000 ≤ c_real ∧ 0 < C_real ∧ 0 < c₀_real ∧ c₀_real ≤ innerChartRadius / 2 ∧
        ∀ {c' : ℝ}, c_real ≤ c' → ∀ {g : ℝ → ℝ},
          TestClass virasoroProblem (c' / 12) g →
          0 < virasoroProblem.cardyNorm (c' / 12) g →
          ∀ x : ℝ, |x| ≤ c₀_real * c' ^ (2 / 3 : ℝ) →
            ‖virasoroPsiTilde c' g (x : ℂ) - truncatedMellinP c' dpT0 g (x : ℂ)‖ ≤
              C_real * Real.exp (-(3 * dpConfig.d₀ / 4) * c') := by
  obtain ⟨C_S4, c_S4, hCS4_pos, _hcS4_10000, hS4⟩ := lemma_S4
  obtain ⟨C_om', hCom'_pos, h_d_bd⟩ := midlineY_norm_le_C_om'
  obtain ⟨c_mid, hcmid_pos, h_mid_lb⟩ := norm_chartOmega_midline_ge
  obtain ⟨c_tail, C_tail, hc_tail_10000, hC_tail_pos, htail_fn⟩ :=
    mellin_midline_tail_exists dpConfig.hT₀_ge dpConfig.hd₀_pos dpConfig.hd₁_pos hcmid_pos
      hCom'_pos hCS4_pos h_mid_lb h_d_bd dpConfig.hmid_tail
  obtain ⟨r_in, hr_in⟩ : ∃ x : ℝ, x = innerChartRadius := ⟨_, rfl⟩
  obtain ⟨C_dxi, hC_dxi⟩ : ∃ x : ℝ, x = innerCDxi := ⟨_, rfl⟩
  obtain ⟨d₀, hd₀⟩ : ∃ x : ℝ, x = dpConfig.d₀ := ⟨_, rfl⟩
  obtain ⟨xi_s, hxi_s⟩ : ∃ x : ℝ, x = xiStar := ⟨_, rfl⟩
  have hr_in_pos : 0 < r_in := hr_in ▸ innerChartRadius_pos
  have hC_dxi_pos : 0 < C_dxi := hC_dxi ▸ innerCDxi_pos
  have hd₀_pos : 0 < d₀ := hd₀ ▸ dpConfig.hd₀_pos
  have hxi_s_pos : 0 < xi_s := hxi_s ▸ xiStar_pos
  have hden_pos : 0 < (3 / xi_s) * C_dxi + 1 :=
    add_pos (mul_pos (div_pos (by norm_num) hxi_s_pos) hC_dxi_pos) zero_lt_one
  obtain ⟨c₀_real, hc₀_real_eq⟩ : ∃ x : ℝ,
      x = min (r_in / 2) ((3 * d₀ / (8 * Real.pi)) / ((3 / xi_s) * C_dxi + 1)) := ⟨_, rfl⟩
  have hc₀_real_pos : 0 < c₀_real := by
    rw [hc₀_real_eq]
    exact lt_min (half_pos hr_in_pos)
      (div_pos (div_pos (mul_pos (by norm_num) hd₀_pos) (mul_pos (by norm_num) Real.pi_pos)) hden_pos)
  have hc₀_real_le_in : c₀_real ≤ r_in / 2 := hc₀_real_eq ▸ min_le_left _ _
  have hc₀_real_le_b : c₀_real ≤ (3 * d₀ / (8 * Real.pi)) / ((3 / xi_s) * C_dxi + 1) :=
    hc₀_real_eq ▸ min_le_right _ _
  obtain ⟨c_V, C_V, _, hCV_pos, hV_inner⟩ := virasoroV_C_inner_bound
  obtain ⟨c_real, hc_real_eq⟩ : ∃ x : ℝ, x = max (max c_tail c_S4) c_V := ⟨_, rfl⟩
  obtain ⟨C_real, hC_real_eq⟩ : ∃ x : ℝ, x = C_V * C_dxi * C_tail / (2 * Real.pi) := ⟨_, rfl⟩
  refine ⟨c_real, C_real, c₀_real, ?_, ?_, hc₀_real_pos, hr_in ▸ hc₀_real_le_in, ?_⟩
  · rw [hc_real_eq]; exact le_trans hc_tail_10000 (le_trans (le_max_left _ _) (le_max_left _ _))
  · rw [hC_real_eq]
    exact div_pos (mul_pos (mul_pos hCV_pos hC_dxi_pos) hC_tail_pos) (mul_pos two_pos Real.pi_pos)
  intro c' hc' g hg hM_pos x hx
  have hc'_tail : c_tail ≤ c' := (hc_real_eq ▸ (le_max_left _ _).trans (le_max_left _ _)).trans hc'
  have hc'_S4 : c_S4 ≤ c' := (hc_real_eq ▸ (le_max_right _ _).trans (le_max_left _ _)).trans hc'
  have hc'_V : c_V ≤ c' := (hc_real_eq ▸ le_max_right _ _).trans hc'
  have hc'_10000 : 10000 ≤ c' := hc_tail_10000.trans hc'_tail
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hS4_bd := hS4 hc'_S4 hg
  obtain ⟨hVI, htail_b⟩ := htail_fn hc'_tail hg hM_pos hS4_bd.2.2.2
  have hx_in : |x| ≤ innerChartRadius * c' ^ (2 / 3 : ℝ) := by
    rw [← hr_in]
    calc |x| ≤ c₀_real * c' ^ (2 / 3 : ℝ) := hx
      _ ≤ (r_in / 2) * c' ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right hc₀_real_le_in (Real.rpow_nonneg hc'_pos.le _)
      _ ≤ r_in * c' ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right (half_le_self hr_in_pos.le) (Real.rpow_nonneg hc'_pos.le _)
  have hx_cb : (x : ℂ) ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx_in
  obtain ⟨hb_im, hb_lo, ht₀_re_pos, ht₀_im⟩ := virasoroBChart_inner_real hc'_pos hx_in
  have hbd_inner := virasoroBChart_inner_bounds hc'_pos hx_cb
  obtain ⟨b₀, hb₀_def⟩ : ∃ y : ℝ, y = (virasoroBChart c' (x : ℂ)).re := ⟨_, rfl⟩
  obtain ⟨t₀, ht₀_def⟩ : ∃ y : ℝ, y = (virasoroDeltaChartC c' (x : ℂ)).re := ⟨_, rfl⟩
  have hb_eq : virasoroBChart c' (x : ℂ) = (b₀ : ℂ) := Complex.ext hb₀_def.symm hb_im
  have ht_eq : virasoroDeltaChartC c' (x : ℂ) = (t₀ : ℂ) := Complex.ext ht₀_def.symm ht₀_im
  have hb_lo' : xiStar / 2 ≤ b₀ := hb₀_def ▸ hb_lo
  have ht₀_pos : 0 < t₀ := ht₀_def ▸ ht₀_re_pos
  have hb₀_hi : b₀ ≤ 2 * xiStar :=
    (hb₀_def ▸ Complex.re_le_norm _).trans hbd_inner.2.2.2.1
  have ht₀_eq : t₀ = c' * b₀ ^ 2 / 3 := by
    have h1 := virasoroDeltaChartC_eq_bChart_sq (c' := c') (u := (x : ℂ))
    rw [ht_eq, hb_eq] at h1
    have h1c : (c' : ℂ) * (b₀ : ℂ) ^ 2 / 3 = ((c' * b₀ ^ 2 / 3 : ℝ) : ℂ) := by push_cast; ring
    have hre := congrArg Complex.re h1
    rw [h1c, Complex.ofReal_re, Complex.ofReal_re] at hre
    exact hre
  have hb₀_gap : (2 * Real.pi / 3) * |b₀ - xiStar| ≤ dpConfig.d₀ / 4 := by
    have hlip := virasoroBChart_inner_lip hc'_pos hx_cb
    rw [hb_eq, ← hxi_s, ← hC_dxi, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hlip
    rw [← hxi_s, ← hd₀]
    have hnorm_x : ‖(x : ℂ)‖ * c' ^ (-(2 / 3 : ℝ)) ≤ c₀_real := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc |x| * c' ^ (-(2 / 3 : ℝ))
          ≤ (c₀_real * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hc'_pos.le _)
        _ = c₀_real := by
            rw [mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero, mul_one]
    have h1 : |b₀ - xi_s| ≤ 3 * d₀ / (8 * Real.pi) := by
      calc |b₀ - xi_s| ≤ ((3 / xi_s) * C_dxi) * c₀_real :=
            hlip.trans (mul_le_mul_of_nonneg_left hnorm_x
              (mul_nonneg (div_nonneg (by norm_num) hxi_s_pos.le) hC_dxi_pos.le))
        _ ≤ ((3 / xi_s) * C_dxi + 1) * c₀_real :=
            mul_le_mul_of_nonneg_right (by linarith only []) hc₀_real_pos.le
        _ ≤ 3 * d₀ / (8 * Real.pi) := (le_div_iff₀' hden_pos).mp hc₀_real_le_b
    calc (2 * Real.pi / 3) * |b₀ - xi_s|
        ≤ (2 * Real.pi / 3) * (3 * d₀ / (8 * Real.pi)) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) (by norm_num))
      _ = d₀ / 4 := by field_simp [Real.pi_pos.ne']; ring
  have htail_Ioi_bd : ∫ η in Ioi (-c' * midlineY dpT0),
      ‖(t₀ : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (η : ℂ)) *
        mellinTransformG g (1 / 2 + Complex.I * (η : ℂ))‖ ≤
      (C_tail / 2) * virasoroProblem.cardyNorm (c' / 12) g *
        Real.exp (-(c' * (2 * Real.pi / 3) * b₀)) * Real.exp (-(3 * d₀ / 4) * c') := by
    have h1 := htail_b hb_lo' hb₀_hi hb₀_gap
    dsimp only at h1
    rw [← ht₀_eq, ← hd₀] at h1
    exact h1
  have hV_bd : ‖V_C (c' : ℂ) (t₀ : ℂ)‖ ≤
      C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (2 * Real.pi / 3) * b₀) := by
    have h1 := hV_inner hc'_V hx_cb
    dsimp only at h1
    rw [ht_eq, hb_eq] at h1
    have htip : (tipL (b₀ : ℂ)).re = (2 * Real.pi / 3) * b₀ := by
      unfold tipL; rw [Complex.re_ofReal_mul, Complex.ofReal_re]
    rw [htip] at h1
    simpa [mul_assoc] using h1
  have hd_bd : ‖deriv (virasoroDeltaChartC c') (x : ℂ)‖ ≤ C_dxi * c' ^ (1 / 3 : ℝ) :=
    hC_dxi ▸ virasoroDeltaChartC_inner_deriv_bound hc'_pos hx_cb
  have hT₀_pos : 0 < dpT0 := by unfold dpT0; have := dpConfig.hT₀_ge; linarith only [this]
  rw [← hd₀, hC_real_eq]
  exact real_mellin_truncation_bound hc'_10000 hT₀_pos hC_tail_pos hCV_pos hC_dxi_pos
    hg hM_pos hb_eq ht_eq ht₀_pos ht₀_eq hVI htail_Ioi_bd hV_bd hd_bd

/-! ### 5. Contour deformation and inner-disc bound for `truncatedMellinP` -/

private lemma contourChained_endpoints {ω₀ ω₁ : ℂ} (hne : ω₀ ≠ ω₁) {segs : List ContourSeg}
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

private lemma norm_contourIntegral_le (f : ℂ → ℂ) (segs : List ContourSeg) (M : ℝ) (_hM : 0 ≤ M)
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

lemma truncatedMellinP_eq_contourIntegral {c' : ℝ} (hc' : 24 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)))
    {segs : List ContourSeg}
    (hchain : ContourChained (chartOmega ((1 / 2 : ℂ) + Complex.I * (dpT0 : ℂ)))
      (chartOmega ((1 / 2 : ℂ) - Complex.I * (dpT0 : ℂ))) segs)
    (hω_bd : ∀ S ∈ segs, ∀ τ ∈ Icc S.a S.b,
      0 ≤ (S.ω τ).re ∧ dpConfig.c_Γ ≤ ‖S.ω τ‖ ∧
        ‖S.ω τ‖ ≤ dpConfig.C_Γ ∧ ‖S.ω' τ‖ ≤ dpConfig.C_d) :
    truncatedMellinP c' dpT0 g u =
      -(deriv (virasoroDeltaChartC c') u / (virasoroProblem.cardyNorm (c' / 12) g : ℂ)) *
        V_C (c' : ℂ) (virasoroDeltaChartC c' u) *
        ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
        contourIntegral (mellinDensityIntegrand c' g (virasoroDeltaChartC c' u)) segs := by
  have hc'_pos : 0 < c' := by linarith only [hc']
  have ha : 2 ≤ c' / 12 := by linarith only [hc']
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
  have hdiff : DifferentiableOn ℂ (mellinDensityIntegrand c' g (virasoroDeltaChartC c' u)) (ball B R) := by
    intro ω hω
    have hω_re_gt : -(1 / (8 * c')) < ω.re := by
      have h1 := (Complex.abs_re_le_norm (ω - B)).trans_lt (mem_ball_iff_norm.mp hω)
      simp only [Complex.sub_re, B, Complex.ofReal_re, abs_lt] at h1
      have hR_def : R = B_r + 1 / (8 * c') := rfl
      linarith only [h1.1, hR_def]
    have hz_re : 0 < (1 / 2 + (c' : ℂ) * ω).re := by
      have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
      simp only [Complex.add_re, h12, Complex.re_ofReal_mul]
      have hcw : -(1 / 8 : ℝ) < c' * ω.re := by
        calc -(1 / 8 : ℝ) = c' * (-(1 / (8 * c'))) := by field_simp [hc'_pos.ne']
          _ < c' * ω.re := mul_lt_mul_of_pos_left hω_re_gt hc'_pos
      linarith only [hcw]
    have hm_diff : DifferentiableAt ℂ (fun w => mellinMGEntire g (1 / 2 + (c' : ℂ) * w)) ω := by
      have hc'_lin : DifferentiableAt ℂ (fun w : ℂ => 1 / 2 + (c' : ℂ) * w) ω := by fun_prop
      exact (differentiable_mellinMGEntire ha hg _).comp ω hc'_lin
    have hGam_diff : DifferentiableAt ℂ (fun w => Complex.Gamma (1 / 2 + (c' : ℂ) * w)) ω := by
      have hc'_lin : DifferentiableAt ℂ (fun w : ℂ => 1 / 2 + (c' : ℂ) * w) ω := by fun_prop
      exact (Complex.differentiableAt_Gamma _ (fun m hm => by
        have hre_m := congrArg Complex.re hm
        simp only [Complex.neg_re, Complex.natCast_re] at hre_m
        linarith only [hz_re, hre_m, Nat.cast_nonneg (α := ℝ) m])).comp ω hc'_lin
    have ht_slit : 2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u ∈ Complex.slitPlane := by
      left
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
      exact mul_pos (by positivity) (virasoroBChart_inner_bounds hc'_pos hu).2.2.2.2.2
    have hpow_diff : DifferentiableAt ℂ
        (fun w => (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u) ^ (-(1 / 2 + (c' : ℂ) * w))) ω := by
      have hexp : (fun w : ℂ => (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u) ^
            (-(1 / 2 + (c' : ℂ) * w))) =
          fun w => Complex.exp (Complex.log (2 * (Real.pi : ℂ) * virasoroDeltaChartC c' u) *
            (-(1 / 2 + (c' : ℂ) * w))) := by
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
    contourChained_endpoints hω₀_ne_ω₁ hchain
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
  unfold truncatedMellinP
  change _ = -(deriv (virasoroDeltaChartC c') u / (virasoroProblem.cardyNorm (c' / 12) g : ℂ)) *
      V_C (c' : ℂ) (virasoroDeltaChartC c' u) *
      ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
      contourIntegral (mellinDensityIntegrand c' g (virasoroDeltaChartC c' u)) segs
  rw [hdef]

lemma truncatedMellinP_deform {c' ρ φ' : ℝ} (hc' : 24 ≤ c')
    (hρ₀ : 0 ≤ ρ) (hρ : ρ ≤ dpConfig.ρ₀) (hφ₀ : 0 ≤ φ') (hφ : φ' ≤ Real.pi / 2)
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
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
      truncatedMellinP c' dpT0 g u =
        -(deriv (virasoroDeltaChartC c') u / (virasoroProblem.cardyNorm (c' / 12) g : ℂ)) *
          V_C (c' : ℂ) (virasoroDeltaChartC c' u) *
          ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
          contourIntegral (mellinDensityIntegrand c' g (virasoroDeltaChartC c' u)) segs := by
  obtain ⟨_, _, _, segs, hchain, hlen, hω_bd, hstrip, _, _, _, _, hnonstrip, _, _, _⟩ :=
    dpConfig_spec hρ₀ hρ hφ₀ hφ
  exact ⟨segs, hchain, hlen, hω_bd, hstrip, hnonstrip,
    truncatedMellinP_eq_contourIntegral hc' hg hu hchain hω_bd⟩

private lemma airyEnv_conj (u : ℂ) : airyEnv (starRingEnd ℂ u) = airyEnv u := by
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

lemma truncatedMellinP_inner_bound :
    ∃ c_P C_P c₀_P : ℝ, 10000 ≤ c_P ∧ 0 < C_P ∧ 0 < c₀_P ∧ c₀_P ≤ innerChartRadius / 2 ∧
      ∀ {c' : ℝ}, c_P ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass virasoroProblem (c' / 12) g →
        0 < virasoroProblem.cardyNorm (c' / 12) g →
        ∀ {u : ℂ}, u ∈ closedBall (0 : ℂ) (c₀_P * c' ^ (2 / 3 : ℝ)) →
          ¬ (u.im = 0 ∧ u.re ≤ 0) →
          ‖truncatedMellinP c' dpT0 g u‖ ≤ C_P * c' ^ (1 / 3 : ℝ) * airyEnv u := by
  obtain ⟨_, q_V, c₀_max, hc₀_max_pos, C₁, hC₁, C₂, hC₂, C₃, hC₃, _, _, _, _, hS6_main, _⟩ :=
    lemma_S6 langerChartSpec_virasoro
  obtain ⟨r_φ, hr_φ_pos, _, hφ_pot⟩ := chartPhiV_saddle_eq_potential
  obtain ⟨C_S4, c_S4, hCS4_pos, hcS4_10000, hS4⟩ := lemma_S4
  obtain ⟨C_S2, c_S2, hCS2_pos, hcS2_10000, hS2⟩ := lemma_S2 dpConfig.hμ₀_gt
  obtain ⟨c_V, C_V, hc_V_39, hCV_pos, hV_fn⟩ := virasoroV_C_inner_bound
  let c₀_use : ℝ := min (c₀_max / 2) (1 / (2 * (C₁ + 1)))
  have hc₀_use_pos : 0 < c₀_use := by positivity
  have hc₀_use_mem : c₀_use ∈ Ioo 0 c₀_max :=
    ⟨hc₀_use_pos, (min_le_left _ _).trans_lt (half_lt_self hc₀_max_pos)⟩
  let ρ_cap : ℝ := min dpConfig.ρ₀ (min r_φ (1 / (2 * (C₂ + 1))))
  have hρ_cap_pos : 0 < ρ_cap := by
    have := dpConfig.hρ₀_pos; positivity
  let c₀_P : ℝ := min (innerChartRadius / 2) (min c₀_use
    ((ρ_cap / (2 * kappaV * (1 + C₁ * c₀_use) + 1)) ^ 2))
  have hc₀_P_pos : 0 < c₀_P := by
    have := innerChartRadius_pos; have := kappaV_pos; positivity
  have hc₀_P_le_half : c₀_P ≤ innerChartRadius / 2 := min_le_left _ _
  let c_P : ℝ := max (max c_S4 c_S2) (max c_V (max 10000 (48 / dpConfig.c_Γ)))
  let C_mid_bd : ℝ := 2 * (2 * Real.sqrt 3 / xiStar) * max C_S4 C_S2
  let C_P : ℝ := (innerCDxi * C_V * dpConfig.C_len / (2 * Real.pi)) * C_mid_bd + 1
  refine ⟨c_P, C_P, c₀_P, (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    ?_, hc₀_P_pos, hc₀_P_le_half, ?_⟩
  · have := innerCDxi_pos; have := dpConfig.hC_len_pos; have := xiStar_pos; positivity
  intro c' hc' g hg hM_pos u hu hcut
  have hc'_S4 : c_S4 ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hc'_S2 : c_S2 ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hc'_V : c_V ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  have hc'_10000 : 10000 ≤ c' :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  have hc'_48 : 48 / dpConfig.c_Γ ≤ c' :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  have hc'_24 : 24 ≤ c' := by linarith only [hc'_10000]
  have hc'_1000 : 1000 ≤ c' := by linarith only [hc'_10000]
  have hS4_bd := hS4 hc'_S4 hg
  have hhalf : ∀ w : ℂ, 0 ≤ w.im → w ∈ closedBall (0 : ℂ) (c₀_P * c' ^ (2 / 3 : ℝ)) →
      ¬ (w.im = 0 ∧ w.re ≤ 0) →
      ‖truncatedMellinP c' dpT0 g w‖ ≤ C_P * c' ^ (1 / 3 : ℝ) * airyEnv w := by
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
    obtain ⟨segs, hchain, hlen, hω_bd, hstrip, hnonstrip, hdeform⟩ :=
      truncatedMellinP_deform hc'_24 hρ_pos.le hρ_le_ρ₀ hφ'_nn hφ'_le hg hw_in
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
    let M_int : ℝ := C_mid_bd * virasoroProblem.cardyNorm (c' / 12) g *
      c' ^ (-(1 / 2 : ℝ)) * Real.exp (-(c' * (tipL b).re)) * airyEnv w
    have hM_int_nn : 0 ≤ M_int := by
      have := hM_pos.le; have := airyEnv_pos w; have := xiStar_pos
      dsimp [M_int, C_mid_bd]; positivity
    have hcont_seg : ∀ S ∈ segs,
        ContinuousOn (fun τ => mellinDensityIntegrand c' g t (S.ω τ)) (Icc S.a S.b) := fun S hS => by
      intro τ hτ
      have hω_re_nn := (hω_bd S hS τ hτ).1
      have hz_re : 0 < (1 / 2 + (c' : ℂ) * S.ω τ).re := by
        have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
        simp only [Complex.add_re, h12, Complex.re_ofReal_mul]
        have hcw := mul_nonneg hc'_pos.le hω_re_nn
        linarith only [hcw]
      have hGam_d : DifferentiableAt ℂ Complex.Gamma (1 / 2 + (c' : ℂ) * S.ω τ) :=
        Complex.differentiableAt_Gamma _ (fun m hm => by
          have hrm := congrArg Complex.re hm
          simp only [Complex.neg_re, Complex.natCast_re] at hrm
          linarith only [hz_re, hrm, Nat.cast_nonneg (α := ℝ) m])
      have h_an_w : DifferentiableAt ℂ (mellinDensityIntegrand c' g t) (S.ω τ) := by
        have hm_d := (differentiable_mellinMGEntire (by linarith only [hc'_24] : 2 ≤ c' / 12) hg).differentiableAt
          (x := 1 / 2 + (c' : ℂ) * S.ω τ)
        have ht_ne : (2 * (Real.pi : ℂ) * t) ≠ 0 := by
          have htre : 0 < t.re := hbd_in.2.2.2.2.2
          have ht0 : t ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at htre; exact lt_irrefl 0 htre
          exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) ht0
        have hlin : DifferentiableAt ℂ (fun ω : ℂ => 1 / 2 + (c' : ℂ) * ω) (S.ω τ) := by fun_prop
        have hp_d : DifferentiableAt ℂ (fun ω : ℂ => (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * ω))) (S.ω τ) := by
          have hex : (fun ω : ℂ => (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * ω))) =
              fun ω => Complex.exp (Complex.log (2 * (Real.pi : ℂ) * t) * (-(1 / 2 + (c' : ℂ) * ω))) := by
            ext ω; rw [Complex.cpow_def_of_ne_zero ht_ne]
          rw [hex]; fun_prop
        have h1 := DifferentiableAt.comp (g := Complex.Gamma) (S.ω τ) hGam_d hlin
        have h2 := DifferentiableAt.comp (g := mellinMGEntire g) (S.ω τ) hm_d hlin
        exact (h1.mul hp_d).mul h2
      exact (h_an_w.continuousAt.comp_continuousWithinAt (S.hω_cont τ hτ))
    have hpt_seg : ∀ S ∈ segs, ∀ τ ∈ Icc S.a S.b,
        ‖mellinDensityIntegrand c' g t (S.ω τ)‖ ≤ M_int := fun S hS τ hτ => by
      have hω_re_nn := (hω_bd S hS τ hτ).1
      have hω_norm_lb := (hω_bd S hS τ hτ).2.1
      have hcω_48 : 48 ≤ c' * ‖S.ω τ‖ := by
        calc (48 : ℝ) ≤ c' * dpConfig.c_Γ := (div_le_iff₀ dpConfig.hc_Γ_pos).mp hc'_48
          _ ≤ c' * ‖S.ω τ‖ := mul_le_mul_of_nonneg_left hω_norm_lb hc'_pos.le
      have hω_ne : S.ω τ ≠ 0 := by intro h0; rw [h0, norm_zero, mul_zero] at hcω_48; linarith only [hcω_48]
      have hS_bd : ‖stirlingS c' (S.ω τ)‖ ≤ 2 := by
        have h1 : 1 ≤ c' * ‖S.ω τ‖ := by linarith only [hcω_48]
        have hsub := norm_stirlingS_sub_one_le hc'_pos hω_re_nn h1
        have hle : 24 / (c' * ‖S.ω τ‖) ≤ 1 / 2 := by
          calc 24 / (c' * ‖S.ω τ‖) ≤ 24 / 48 := by gcongr
            _ = 1 / 2 := by norm_num
        have htr : ‖stirlingS c' (S.ω τ)‖ ≤ ‖stirlingS c' (S.ω τ) - 1‖ + ‖(1 : ℂ)‖ := by
          calc ‖stirlingS c' (S.ω τ)‖ = ‖(stirlingS c' (S.ω τ) - 1) + 1‖ := by ring_nf
            _ ≤ ‖stirlingS c' (S.ω τ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        rw [norm_one] at htr; linarith only [htr, hsub, hle]
      have hz_re : 0 < (1 / 2 + (c' : ℂ) * S.ω τ).re := by
        have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
        simp only [Complex.add_re, h12, Complex.re_ofReal_mul]
        have hcw := mul_nonneg hc'_pos.le hω_re_nn
        linarith only [hcw]
      have h_st := gamma_mul_two_pi_t_cpow_neg hc'_pos (ω := S.ω τ) (b := b) hω_re_nn hω_ne hb_re_pos
      rw [← ht_eq] at h_st
      cases hstrip_b : S.isStrip
      · -- `S.isStrip = false`: use `lemma_S2` + `crudeExponentEc`
        obtain ⟨hμ₀_le, hEc_le⟩ := hnonstrip S hS hstrip_b τ hτ
        have hS2_bd := (hS2 hc'_S2 hμ₀_le hg).2
        have hmel_eq : mellinDensityIntegrand c' g t (S.ω τ) =
            t ^ (-(1 / 2 : ℂ)) * stirlingS c' (S.ω τ) *
              Complex.exp ((c' : ℂ) * ComplexBessel.stirlingJ (S.ω τ) b) *
              mellinMG g (1 / 2 + (c' : ℂ) * S.ω τ) := by
          unfold mellinDensityIntegrand
          dsimp only
          rw [mellinMGEntire_of_re_pos g hz_re]
          calc Complex.Gamma (1 / 2 + (c' : ℂ) * S.ω τ) *
                (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * S.ω τ)) *
                mellinMG g (1 / 2 + (c' : ℂ) * S.ω τ)
              = (Complex.Gamma (1 / 2 + (c' : ℂ) * S.ω τ) *
                  (2 * (Real.pi : ℂ) * t) ^ (-(1 / 2 + (c' : ℂ) * S.ω τ))) *
                  mellinMG g (1 / 2 + (c' : ℂ) * S.ω τ) := rfl
            _ = _ := by rw [h_st]; ring
        rw [hmel_eq, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
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
        calc ‖t ^ (-(1 / 2 : ℂ))‖ * ‖stirlingS c' (S.ω τ)‖ *
                Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
                ‖mellinMG g (1 / 2 + (c' : ℂ) * S.ω τ)‖
            ≤ ((2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ))) * 2 *
                Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
                (C_S2 * Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ)) *
                  virasoroProblem.cardyNorm (c' / 12) g) := by
              have := xiStar_pos; gcongr
          _ = 2 * (2 * Real.sqrt 3 / xiStar) * C_S2 * virasoroProblem.cardyNorm (c' / 12) g *
                c' ^ (-(1 / 2 : ℝ)) *
                (Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
                  Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ))) := by ring
          _ ≤ C_mid_bd * virasoroProblem.cardyNorm (c' / 12) g *
                c' ^ (-(1 / 2 : ℝ)) * (Real.exp (-(c' * (tipL b).re)) * airyEnv w) := by
              dsimp only [C_mid_bd]
              have hCS_le : C_S2 ≤ max C_S4 C_S2 := le_max_right _ _
              have := xiStar_pos; have := hM_pos.le
              gcongr
          _ = M_int := by dsimp [M_int]; ring
      · -- `S.isStrip = true`: use `lemma_S4` + `(chartPhiV (S.ζ τ) b).re ≤ (chartPhiV ζp b).re`
        obtain ⟨_, hΦ_le⟩ := hstrip S hS hstrip_b τ hτ
        have hζ_data := S.hζ_strip hstrip_b τ hτ
        have hζ_cl : S.ζ τ ∈ stripClosed := ⟨hζ_data.1, hζ_data.2.1.trans (by norm_num)⟩
        have hω_eq_ζ : S.ω τ = chartOmega (S.ζ τ) := hζ_data.2.2.1
        have hWV_bd := hS4_bd.2.2.2 (S.ζ τ) hζ_cl
        have hmel_eq : mellinDensityIntegrand c' g t (S.ω τ) =
            t ^ (-(1 / 2 : ℂ)) * stirlingS c' (S.ω τ) *
              Complex.exp ((c' : ℂ) * chartPhiV (S.ζ τ) b - (c' : ℂ) * tipL b) *
              tildeWV c' g (S.ζ τ) := by
          unfold mellinDensityIntegrand tildeWV chartPhiV
          dsimp only
          rw [h_st, ← hω_eq_ζ]
          have hex : Complex.exp ((c' : ℂ) * ComplexBessel.stirlingJ (S.ω τ) b) =
              Complex.exp ((c' : ℂ) * (chartUpsilon (S.ζ τ) +
                  ComplexBessel.stirlingJ (S.ω τ) b + tipL b) - (c' : ℂ) * tipL b) *
                Complex.exp (-(c' : ℂ) * chartUpsilon (S.ζ τ)) := by
            rw [← Complex.exp_add]; congr 1; ring
          rw [hex]; ring
        rw [hmel_eq, norm_mul, norm_mul, norm_mul, Complex.norm_exp]
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
        calc ‖t ^ (-(1 / 2 : ℂ))‖ * ‖stirlingS c' (S.ω τ)‖ *
                Real.exp (c' * (chartPhiV (S.ζ τ) b).re - c' * (tipL b).re) *
                ‖tildeWV c' g (S.ζ τ)‖
            ≤ ((2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ))) * 2 *
                (Real.exp (-(c' * (tipL b).re)) * airyEnv w) *
                (C_S4 * virasoroProblem.cardyNorm (c' / 12) g) := by
              have := xiStar_pos; have := airyEnv_pos w; gcongr
          _ = 2 * (2 * Real.sqrt 3 / xiStar) * C_S4 * virasoroProblem.cardyNorm (c' / 12) g *
                c' ^ (-(1 / 2 : ℝ)) * Real.exp (-(c' * (tipL b).re)) * airyEnv w := by ring
          _ ≤ M_int := by
              have hCS_le : C_S4 ≤ max C_S4 C_S2 := le_max_left _ _
              have := xiStar_pos; have := hM_pos.le; have := airyEnv_pos w
              dsimp only [M_int, C_mid_bd]
              gcongr
    have hint_bd := norm_contourIntegral_le (mellinDensityIntegrand c' g t) segs M_int hM_int_nn
      hcont_seg hpt_seg
    have hV_bd := hV_fn hc'_V hw_in
    have hd_bd := virasoroDeltaChartC_inner_deriv_bound hc'_pos hw_in
    rw [hdeform, norm_mul, norm_mul, norm_mul, norm_neg, norm_div, norm_div]
    have hM_norm : ‖(virasoroProblem.cardyNorm (c' / 12) g : ℂ)‖ =
        virasoroProblem.cardyNorm (c' / 12) g := by
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
    have hhint : ‖contourIntegral (mellinDensityIntegrand c' g t) segs‖ ≤ M_int * dpConfig.C_len :=
      hint_bd.trans (mul_le_mul_of_nonneg_left hlen hM_int_nn)
    calc (‖deriv (virasoroDeltaChartC c') w‖ / virasoroProblem.cardyNorm (c' / 12) g) *
            ‖V_C (c' : ℂ) t‖ * (c' / (2 * Real.pi)) *
            ‖contourIntegral (mellinDensityIntegrand c' g t) segs‖
        ≤ ((innerCDxi * c' ^ (1 / 3 : ℝ)) / virasoroProblem.cardyNorm (c' / 12) g) *
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
    rw [truncatedMellinP_conj hc'_1000 dpT0 hg hu_in_ball, Complex.norm_conj, airyEnv_conj] at hbd_c
    exact hbd_c

/-! ### 6. Half-plane Poisson–Jensen argument and Lemma D' (`vlo:Dp`) -/

private noncomputable def halfUpper (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * ((Real.pi : ℂ) / 4)) * (-Complex.I * z) ^ (1 / 2 : ℂ)

private noncomputable def halfPlaneChart (U₀ : ℝ) (z : ℂ) : ℂ :=
  (U₀ : ℂ) * (halfUpper z - 1) / (halfUpper z + 1)

private lemma halfUpper_sq_eq {z : ℂ} :
    halfUpper z ^ 2 = z := by
  unfold halfUpper
  rw [mul_pow, ← Complex.exp_nat_mul]
  have h1 : ((2 : ℕ) : ℂ) * (Complex.I * ((Real.pi : ℂ) / 4)) = Complex.I * ((Real.pi : ℂ) / 2) := by
    push_cast; ring
  have h2 : Complex.exp (Complex.I * ((Real.pi : ℂ) / 2)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]; simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  have h3 : ((-Complex.I * z) ^ (1 / 2 : ℂ)) ^ 2 = -Complex.I * z := by
    by_cases h0 : -Complex.I * z = 0
    · rw [h0, Complex.zero_cpow (by norm_num)]; simp
    · rw [Complex.cpow_def_of_ne_zero h0, ← Complex.exp_nat_mul]
      have hmul : ((2 : ℕ) : ℂ) * (Complex.log (-Complex.I * z) * (1 / 2 : ℂ)) =
          Complex.log (-Complex.I * z) := by push_cast; ring
      rw [hmul, Complex.exp_log h0]
  rw [h1, h2, h3]
  calc Complex.I * (-Complex.I * z) = (-(Complex.I * Complex.I)) * z := by ring
    _ = z := by rw [Complex.I_mul_I]; ring

private lemma halfUpper_pos_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    0 < (halfUpper z).re ∧ 0 < (halfUpper z).im := by
  set ζ : ℂ := -Complex.I * z
  have hζ_re : 0 < ζ.re := by simp [ζ, hz]
  have hζ_ne : ζ ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hζ_re; linarith
  have hζ_arg : |ζ.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hζ_re)
  have hθ_lo : 0 < Real.pi / 4 + ζ.arg / 2 := by
    linarith [(abs_lt.mp hζ_arg).1]
  have hθ_hi : Real.pi / 4 + ζ.arg / 2 < Real.pi / 2 := by
    linarith [(abs_lt.mp hζ_arg).2]
  have hexp_half : halfUpper z =
      (Real.sqrt ‖ζ‖ : ℂ) * Complex.exp (Complex.I * (((Real.pi / 4 + ζ.arg / 2 : ℝ) : ℂ))) := by
    unfold halfUpper
    have hlog_eq : Complex.log ζ = (Real.log ‖ζ‖ : ℂ) + (ζ.arg : ℂ) * Complex.I := rfl
    have hpow_z : (-Complex.I * z) ^ (1 / 2 : ℂ) =
        Complex.exp (((Real.log ‖ζ‖ / 2 : ℝ) : ℂ) + Complex.I * ((ζ.arg / 2 : ℝ) : ℂ)) := by
      change ζ ^ (1 / 2 : ℂ) = _
      rw [Complex.cpow_def_of_ne_zero hζ_ne, Complex.log]
      congr 1; push_cast; ring
    have hlog_half : Real.exp (Real.log ‖ζ‖ / 2) = Real.sqrt ‖ζ‖ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (norm_pos_iff.mpr hζ_ne)]; ring_nf
    rw [hpow_z, Complex.exp_add, ← Complex.ofReal_exp, hlog_half,
      mul_left_comm, ← Complex.exp_add]
    congr 2; push_cast; ring
  have hexp_eq : Complex.exp (Complex.I * ((Real.pi / 4 + ζ.arg / 2 : ℝ) : ℂ)) =
      (Real.cos (Real.pi / 4 + ζ.arg / 2) : ℂ) +
        (Real.sin (Real.pi / 4 + ζ.arg / 2) : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hexp_half, hexp_eq]
  have hcos_pos : 0 < Real.cos (Real.pi / 4 + ζ.arg / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ_hi⟩
  have hsin_pos : 0 < Real.sin (Real.pi / 4 + ζ.arg / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hθ_lo (by linarith [Real.pi_pos])
  have hsqrt_pos : 0 < Real.sqrt ‖ζ‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hζ_ne)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  constructor <;> nlinarith

private lemma halfUpper_eq_cpow_half_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    halfUpper u = u ^ (1 / 2 : ℂ) := by
  have hsq1 : halfUpper u ^ 2 = u := halfUpper_sq_eq
  have hsq2 : (u ^ (1 / 2 : ℂ)) ^ 2 = u := FormalResearch.Special.cpow_half_sq u
  have hdiff : (halfUpper u - u ^ (1 / 2 : ℂ)) * (halfUpper u + u ^ (1 / 2 : ℂ)) = 0 := by
    linear_combination hsq1 - hsq2
  rcases mul_eq_zero.mp hdiff with h0 | h0
  · exact sub_eq_zero.mp h0
  · exfalso
    have hre1 := (halfUpper_pos_of_im_pos hu).1
    have hre2 : 0 ≤ (u ^ (1 / 2 : ℂ)).re := cpow_half_re_nonneg u
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.zero_re] at this
    linarith

private lemma halfUpper_analyticAt_upper_or_real {z : ℂ} (hz : 0 ≤ z.im) (hne : z ≠ 0) :
    AnalyticAt ℂ halfUpper z := by
  have hslit : -Complex.I * z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    rcases eq_or_lt_of_le hz with him0 | him_pos
    · right
      have hre0 : z.re ≠ 0 := fun hr => hne (Complex.ext hr him0.symm)
      simp [Complex.mul_im, hre0]
    · left; simp [Complex.mul_re, him_pos]
  have hpow : AnalyticAt ℂ (fun w : ℂ => (-Complex.I * w) ^ (1 / 2 : ℂ)) z := by
    have hlog : AnalyticAt ℂ Complex.log (-Complex.I * z) := analyticAt_clog hslit
    have hlog_comp := hlog.comp (analyticAt_const.mul analyticAt_id)
    exact (hlog_comp.mul analyticAt_const).cexp.congr (by
      filter_upwards [(isOpen_slitPlane.preimage (continuous_const.mul continuous_id)).mem_nhds hslit] with w hw
      exact (Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hw) (1 / 2 : ℂ)).symm)
  exact analyticAt_const.mul hpow

private lemma halfUpper_posReal {σ : ℝ} (hσ : 0 < σ) :
    halfUpper (σ : ℂ) = (Real.sqrt σ : ℂ) := by
  have hζ_ne : -Complex.I * (σ : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp [hσ.ne'] at this
  have harg : (-Complex.I * (σ : ℂ)).arg = -(Real.pi / 2) := by
    rw [show -Complex.I * (σ : ℂ) = (0 : ℂ) + (-(σ) : ℝ) * Complex.I by simp; ring]
    exact Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨by simp, by simp [hσ]⟩
  unfold halfUpper
  rw [Complex.cpow_def_of_ne_zero hζ_ne, Complex.log, harg]
  have hnorm : ‖-Complex.I * (σ : ℂ)‖ = σ := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hσ.le]
  rw [hnorm, show ((Real.log σ : ℝ) : ℂ) + (-(Real.pi / 2) : ℝ) * Complex.I =
      ((Real.log σ : ℝ) : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring]
  have hs : Real.exp (Real.log σ / 2) = Real.sqrt σ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hσ]; ring_nf
  have hpow : Complex.exp (((Real.log σ : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (1 / 2 : ℂ)) =
      (Real.sqrt σ : ℂ) * Complex.exp (-(Complex.I * ((Real.pi : ℂ) / 4))) := by
    rw [show ((Real.log σ : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (1 / 2 : ℂ) =
        ((Real.log σ / 2 : ℝ) : ℂ) + (-(Complex.I * ((Real.pi : ℂ) / 4))) by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, hs]
  rw [hpow, mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

private lemma halfUpper_negReal {σ : ℝ} (hσ : σ < 0) :
    halfUpper (σ : ℂ) = Complex.I * (Real.sqrt (-σ) : ℂ) := by
  have hns : 0 < -σ := by linarith
  have hζ_ne : -Complex.I * (σ : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp [hσ.ne] at this
  have harg : (-Complex.I * (σ : ℂ)).arg = Real.pi / 2 := by
    rw [show -Complex.I * (σ : ℂ) = (0 : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.arg_eq_pi_div_two_iff.mpr ⟨by simp, by simp [hns]⟩
  unfold halfUpper
  rw [Complex.cpow_def_of_ne_zero hζ_ne, Complex.log, harg]
  have hnorm : ‖-Complex.I * (σ : ℂ)‖ = -σ := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonpos hσ.le]
  rw [hnorm, show ((Real.log (-σ) : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I =
      ((Real.log (-σ) : ℝ) : ℂ) + Complex.I * ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring]
  have hs : Real.exp (Real.log (-σ) / 2) = Real.sqrt (-σ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hns]; ring_nf
  have hpow : Complex.exp (((Real.log (-σ) : ℂ) + Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (1 / 2 : ℂ)) =
      (Real.sqrt (-σ) : ℂ) * Complex.exp (Complex.I * ((Real.pi : ℂ) / 4)) := by
    rw [show ((Real.log (-σ) : ℂ) + Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (1 / 2 : ℂ) =
        ((Real.log (-σ) / 2 : ℝ) : ℂ) + Complex.I * ((Real.pi : ℂ) / 4) by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, hs]
  rw [hpow, mul_left_comm, ← Complex.exp_add]
  have hsum : Complex.I * ((Real.pi : ℂ) / 4) + Complex.I * ((Real.pi : ℂ) / 4) =
      Complex.I * ((Real.pi : ℂ) / 2) := by ring
  have hI : Complex.exp (Complex.I * ((Real.pi : ℂ) / 2)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]; simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  rw [hsum, hI, mul_comm]

private lemma halfPlaneChart_mem_upperHalf {U₀ : ℝ} (hU₀ : 0 < U₀) {z : ℂ} (hz : 0 < z.im) :
    ‖halfPlaneChart U₀ z‖ < U₀ ∧ 0 < (halfPlaneChart U₀ z).im := by
  obtain ⟨hw_re, hw_im⟩ := halfUpper_pos_of_im_pos hz
  set w := halfUpper z
  have hw_add_ne : w + 1 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hnorm_lt : ‖w - 1‖ < ‖w + 1‖ := by
    have hsq : ‖w - 1‖ ^ 2 < ‖w + 1‖ ^ 2 := by
      have h1 : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
      have h2 : ‖w + 1‖ ^ 2 = (w.re + 1) ^ 2 + w.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
      nlinarith
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have him_div : 0 < ((w - 1) / (w + 1)).im := by
    have hden_pos : 0 < Complex.normSq (w + 1) := Complex.normSq_pos.mpr hw_add_ne
    rw [Complex.div_im, ← sub_div]
    refine div_pos ?_ hden_pos
    simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.add_re, Complex.one_re,
      Complex.sub_re, Complex.add_im, add_zero]
    linarith [hw_re]
  unfold halfPlaneChart
  rw [mul_div_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hU₀.le, norm_div]
  refine ⟨?_, ?_⟩
  · have hq : ‖w - 1‖ / ‖w + 1‖ < 1 := (div_lt_one (norm_pos_iff.mpr hw_add_ne)).mpr hnorm_lt
    nlinarith
  · rw [Complex.im_ofReal_mul]
    exact mul_pos hU₀ him_div

private lemma poissonKernel_Ioi_ge_quarter {x y : ℝ} (hy : 0 < y) (hxy : -y ≤ x) :
    Integrable (poissonKernel x y) ∧
      ∫ σ : ℝ, poissonKernel x y σ = 1 ∧
      (1 / 4 : ℝ) ≤ ∫ σ in Ioi (0 : ℝ), poissonKernel x y σ := by
  let F : ℝ → ℝ := fun σ => (1 / Real.pi) * Real.arctan ((σ - x) / y)
  have hF_deriv : ∀ σ : ℝ, HasDerivAt F (poissonKernel x y σ) σ := fun σ => by
    have h1 : HasDerivAt (fun s : ℝ => (s - x) / y) (1 / y) σ := by
      simpa using ((hasDerivAt_id σ).sub_const x).div_const y
    have h2 := (Real.hasDerivAt_arctan ((σ - x) / y)).comp σ h1
    refine (h2.const_mul (1 / Real.pi)).congr_deriv ?_
    unfold poissonKernel
    have hsq : 1 + ((σ - x) / y) ^ 2 = ((σ - x) ^ 2 + y ^ 2) / y ^ 2 := by
      field_simp [hy.ne']; ring
    rw [hsq]
    field_simp [hy.ne', Real.pi_pos.ne']
  have hF_top : Tendsto F atTop (𝓝 (1 / 2 : ℝ)) := by
    have hlin : Tendsto (fun σ : ℝ => (σ - x) / y) atTop atTop :=
      (tendsto_id.atTop_add tendsto_const_nhds).atTop_div_const hy
    have harctan : Tendsto (fun σ : ℝ => Real.arctan ((σ - x) / y)) atTop (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.comp hlin).mono_right nhdsWithin_le_nhds
    have hhalf : (1 / Real.pi) * (Real.pi / 2) = 1 / 2 := by field_simp [Real.pi_pos.ne']
    exact hhalf ▸ harctan.const_mul (1 / Real.pi)
  have hF_bot : Tendsto F atBot (𝓝 (-(1 / 2) : ℝ)) := by
    have hlin : Tendsto (fun σ : ℝ => (σ - x) / y) atBot atBot :=
      (tendsto_id.atBot_add tendsto_const_nhds).atBot_div_const hy
    have harctan : Tendsto (fun σ : ℝ => Real.arctan ((σ - x) / y)) atBot (𝓝 (-(Real.pi / 2))) :=
      (Real.tendsto_arctan_atBot.comp hlin).mono_right nhdsWithin_le_nhds
    have hnhalf : (1 / Real.pi) * (-(Real.pi / 2)) = -(1 / 2) := by field_simp [Real.pi_pos.ne']
    exact hnhalf ▸ harctan.const_mul (1 / Real.pi)
  have h_nn : ∀ σ : ℝ, 0 ≤ poissonKernel x y σ := fun σ => by
    unfold poissonKernel; positivity
  have hIoi_int : IntegrableOn (poissonKernel x y) (Ioi (0 : ℝ)) :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' (fun σ _ => hF_deriv σ)
      (fun σ _ => h_nn σ) hF_top
  have hIoi_eq : ∫ σ in Ioi (0 : ℝ), poissonKernel x y σ = 1 / 2 - F 0 :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (fun σ _ => hF_deriv σ)
      (fun σ _ => h_nn σ) hF_top
  have hIic : IntegrableOn (poissonKernel x y) (Iic (0 : ℝ)) ∧
      ∫ σ in Iic (0 : ℝ), poissonKernel x y σ = F 0 - (-(1 / 2)) := by
    have hG_deriv : ∀ σ : ℝ, HasDerivAt (fun t : ℝ => (-1 : ℝ) * F (-t)) (poissonKernel x y (-σ)) σ := fun σ => by
      have hc : HasDerivAt (fun t : ℝ => F (-t)) (-poissonKernel x y (-σ)) σ := by
        simpa [Function.comp_def] using (hF_deriv (-σ)).comp σ (hasDerivAt_neg σ)
      simpa using hc.const_mul (-1 : ℝ)
    have hG_top : Tendsto (fun t : ℝ => (-1 : ℝ) * F (-t)) atTop (𝓝 (1 / 2 : ℝ)) := by
      have ht := (hF_bot.comp tendsto_neg_atTop_atBot).const_mul (-1 : ℝ)
      simpa using ht
    have hneg_int : IntegrableOn (fun t : ℝ => poissonKernel x y (-t)) (Ioi (0 : ℝ)) :=
      MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' (fun σ _ => hG_deriv σ)
        (fun σ _ => h_nn (-σ)) hG_top
    have hneg_eq : ∫ t in Ioi (0 : ℝ), poissonKernel x y (-t) = 1 / 2 - ((-1 : ℝ) * F (-0)) :=
      MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (fun σ _ => hG_deriv σ)
        (fun σ _ => h_nn (-σ)) hG_top
    have hIic_int : IntegrableOn (poissonKernel x y) (Iic (0 : ℝ)) := by
      have h1 : IntegrableOn (poissonKernel x y) (Iio (0 : ℝ)) := by simpa using hneg_int.comp_neg
      have h0_int : IntegrableOn (poissonKernel x y) (Icc (-1 : ℝ) 0) := by
        have hcont : Continuous (poissonKernel x y) := by
          unfold poissonKernel
          exact continuous_const.div
            (continuous_const.mul (((continuous_id.sub continuous_const).pow 2).add continuous_const))
            fun σ => (mul_pos Real.pi_pos (by positivity)).ne'
        exact hcont.continuousOn.integrableOn_Icc
      exact (h1.union h0_int).mono_set fun t ht =>
        (lt_or_eq_of_le (mem_Iic.mp ht)).imp mem_Iio.mpr fun h0 => ⟨by linarith only [h0], h0.le⟩
    have hIic_eq : ∫ σ in Iic (0 : ℝ), poissonKernel x y σ = F 0 - (-(1 / 2)) := by
      have hcomp := integral_comp_neg_Ioi (0 : ℝ) (poissonKernel x y)
      rw [neg_zero] at hcomp
      rw [← hcomp, hneg_eq, neg_zero]
      ring
    exact ⟨hIic_int, hIic_eq⟩
  have hInt : Integrable (poissonKernel x y) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hIic.1.union hIoi_int
  have hTot : ∫ σ : ℝ, poissonKernel x y σ = 1 := by
    have hadd := (MeasureTheory.integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hInt).symm
    rw [compl_Iic] at hadd
    rw [hadd, hIic.2, hIoi_eq]
    ring
  have hIoi_lb : (1 / 4 : ℝ) ≤ ∫ σ in Ioi (0 : ℝ), poissonKernel x y σ := by
    rw [hIoi_eq]
    have hle : (0 - x) / y ≤ 1 := by rw [div_le_one hy]; linarith
    have ha_le : Real.arctan ((0 - x) / y) ≤ Real.pi / 4 := by
      calc Real.arctan ((0 - x) / y) ≤ Real.arctan 1 := Real.arctan_mono hle
        _ = Real.pi / 4 := Real.arctan_one
    have hF0_ub : F 0 ≤ 1 / 4 := by
      dsimp [F]
      calc (1 / Real.pi) * Real.arctan ((0 - x) / y) ≤ (1 / Real.pi) * (Real.pi / 4) := by
            gcongr
        _ = 1 / 4 := by field_simp [Real.pi_pos.ne']
    linarith
  exact ⟨hInt, hTot, hIoi_lb⟩

private lemma exists_halfPlaneChart_preimage {U₀ : ℝ} (hU₀ : 0 < U₀) {w : ℂ}
    (him : 0 < w.im) (hw : ‖w‖ ≤ U₀ / 2) :
    ∃ z₀ : ℂ, 0 < z₀.im ∧ -z₀.im ≤ z₀.re ∧ halfPlaneChart U₀ z₀ = w := by
  let ζ : ℂ := w / (U₀ : ℂ)
  have hζ_norm : ‖ζ‖ ≤ 1 / 2 := by
    dsimp [ζ]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hU₀.le, div_le_iff₀ hU₀]
    linarith
  have hζ_im : 0 < ζ.im := by
    dsimp [ζ]
    rw [show w / (U₀ : ℂ) = ((U₀⁻¹ : ℝ) : ℂ) * w by push_cast; ring, Complex.im_ofReal_mul]
    exact mul_pos (inv_pos.mpr hU₀) him
  have hsub_ne : 1 - ζ ≠ 0 := by
    intro h0
    have := congrArg norm (eq_of_sub_eq_zero h0)
    rw [norm_one] at this; linarith
  let w₀ : ℂ := (1 + ζ) / (1 - ζ)
  let z₀ : ℂ := w₀ ^ 2
  have hw₀_re : w₀.re = (1 - ‖ζ‖ ^ 2) / ‖1 - ζ‖ ^ 2 := by
    dsimp [w₀]
    have h1 : Complex.normSq (1 - ζ) = ‖1 - ζ‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rw [Complex.div_re, h1, ← add_div]
    have hmul : (1 + ζ).re * (1 - ζ).re + (1 + ζ).im * (1 - ζ).im = 1 - ‖ζ‖ ^ 2 := by
      have hns : Complex.normSq ζ = ‖ζ‖ ^ 2 := Complex.normSq_eq_norm_sq ζ
      rw [Complex.normSq_apply] at hns
      simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
        Complex.sub_im]
      linarith
    rw [hmul]
  have hw₀_im : w₀.im = 2 * ζ.im / ‖1 - ζ‖ ^ 2 := by
    dsimp [w₀]
    have h1 : Complex.normSq (1 - ζ) = ‖1 - ζ‖ ^ 2 := Complex.normSq_eq_norm_sq _
    rw [Complex.div_im, h1, ← sub_div]
    have hmul : (1 + ζ).im * (1 - ζ).re - (1 + ζ).re * (1 - ζ).im = 2 * ζ.im := by
      simp; ring
    rw [hmul]
  have hw₀_re_pos : 0 < w₀.re := by
    rw [hw₀_re]
    exact div_pos (by nlinarith [norm_nonneg ζ]) (sq_pos_of_pos (norm_pos_iff.mpr hsub_ne))
  have hw₀_im_pos : 0 < w₀.im := by
    rw [hw₀_im]
    exact div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hsub_ne))
  have hw₀_ratio : 3 * w₀.im ≤ 4 * w₀.re := by
    rw [hw₀_im, hw₀_re]
    have hden_pos : 0 < ‖1 - ζ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hsub_ne)
    have hζ_im_le : ζ.im ≤ 1 / 2 := (Complex.abs_im_le_norm ζ |>.trans hζ_norm).trans' (le_abs_self _)
    have hnum : 3 * (2 * ζ.im) ≤ 4 * (1 - ‖ζ‖ ^ 2) := by
      nlinarith only [hζ_im_le, hζ_norm, norm_nonneg ζ]
    rw [← mul_div_assoc, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hnum hden_pos.le
  have hz₀_im : 0 < z₀.im := by
    dsimp [z₀]; rw [sq, Complex.mul_im]; nlinarith
  have hz₀_re_lb : -z₀.im ≤ z₀.re := by
    dsimp [z₀]; rw [sq, Complex.mul_re, Complex.mul_im]
    nlinarith
  have hU_z₀ : halfUpper z₀ = w₀ := by
    have hsq1 : halfUpper z₀ ^ 2 = z₀ := halfUpper_sq_eq
    have hsq2 : w₀ ^ 2 = z₀ := rfl
    have hdiff : (halfUpper z₀ - w₀) * (halfUpper z₀ + w₀) = 0 := by
      linear_combination hsq1 - hsq2
    rcases mul_eq_zero.mp hdiff with h0 | h0
    · exact sub_eq_zero.mp h0
    · exfalso
      have hre1 := (halfUpper_pos_of_im_pos hz₀_im).1
      have := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.zero_re] at this
      linarith
  have hchart_z₀ : halfPlaneChart U₀ z₀ = w := by
    unfold halfPlaneChart
    rw [hU_z₀]
    have hw₀_add_ne : w₀ + 1 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have h_id : (w₀ - 1) / (w₀ + 1) = ζ := by
      dsimp [w₀]
      field_simp [hsub_ne]; ring
    rw [mul_div_assoc, h_id]
    dsimp [ζ]; field_simp [hU₀.ne']
  exact ⟨z₀, hz₀_im, hz₀_re_lb, hchart_z₀⟩

/-- **Lemma D'** (`lower_o1_two_edge.tex`, `vlo:Dp`, lines 731–760):
for `c' ≥ c_D`, on the inner Langer disc `closedBall 0 (c₀_D * c'^(2/3))`, the truncated
Mellin density `truncatedMellinP c' dpT0 g` approximates `virasoroPsiTilde c' g` with
exponential accuracy `C_D exp(-d_D c') airyEnv u`. -/
theorem lemma_Dp :
    ∃ c_D C_D d_D c₀_D : ℝ,
      10000 ≤ c_D ∧ 0 < C_D ∧ 0 < d_D ∧ 0 < c₀_D ∧ c₀_D ≤ innerChartRadius / 4 ∧
        ∀ {c' : ℝ}, c_D ≤ c' → ∀ {g : ℝ → ℝ},
          TestClass virasoroProblem (c' / 12) g →
          0 < virasoroProblem.cardyNorm (c' / 12) g →
          ∀ {u : ℂ}, u ∈ closedBall (0 : ℂ) (c₀_D * c' ^ (2 / 3 : ℝ)) →
            ‖truncatedMellinP c' dpT0 g u - virasoroPsiTilde c' g u‖ ≤
              C_D * Real.exp (-d_D * c') * airyEnv u := by
  obtain ⟨c_real, C_real, c₀_real, hc_real_10000, hC_real_pos, hc₀_real_pos, hc₀_real_le, hreal_fn⟩ :=
    truncatedMellinP_real_err
  obtain ⟨c_P, C_P, c₀_P, hc_P_10000, hC_P_pos, hc₀_P_pos, hc₀_P_le, hP_fn⟩ :=
    truncatedMellinP_inner_bound
  have hc_Q_1000 : 1000 ≤ virasoroCQEnv := by
    have h1 := c_PJ_complex_le_virasoroCQEnv
    have h2 : (10000 : ℝ) = c_PJ_complex := by unfold c_PJ_complex; rfl
    linarith only [h1, h2]
  obtain ⟨d₀, hd₀_eq⟩ : ∃ x : ℝ, x = dpConfig.d₀ := ⟨_, rfl⟩
  have hd₀_pos : 0 < d₀ := hd₀_eq ▸ dpConfig.hd₀_pos
  -- Choose `c₀_D` small so `2 c₀_D ≤ min c₀_real c₀_P`, `c₀_D ≤ innerChartRadius / 4`,
  -- and `(4/3) (2 c₀_D)^(3/2) ≤ 3 d₀ / 32`.
  let c₀_D_ang : ℝ := (9 * d₀ / 128) ^ (2 / 3 : ℝ) / 2
  obtain ⟨c₀_D, hc₀_D_eq⟩ : ∃ x : ℝ,
      x = min (innerChartRadius / 4) (min (min (c₀_real / 2) (c₀_P / 2)) c₀_D_ang) := ⟨_, rfl⟩
  have hc₀_D_pos : 0 < c₀_D := by
    rw [hc₀_D_eq]; have := innerChartRadius_pos; positivity
  have hc₀_D_le4 : c₀_D ≤ innerChartRadius / 4 := hc₀_D_eq ▸ min_le_left _ _
  have h2c₀_real : 2 * c₀_D ≤ c₀_real := by
    have h1 : c₀_D ≤ c₀_real / 2 :=
      hc₀_D_eq ▸ (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    linarith only [h1]
  have h2c₀_P : 2 * c₀_D ≤ c₀_P := by
    have h1 : c₀_D ≤ c₀_P / 2 :=
      hc₀_D_eq ▸ (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    linarith only [h1]
  have h2c₀_ang : (4 / 3 : ℝ) * (2 * c₀_D) ^ (3 / 2 : ℝ) ≤ 3 * d₀ / 32 := by
    have h1 : 2 * c₀_D ≤ (9 * d₀ / 128) ^ (2 / 3 : ℝ) := by
      have hle : c₀_D ≤ c₀_D_ang := hc₀_D_eq ▸ (min_le_right _ _).trans (min_le_right _ _)
      dsimp [c₀_D_ang] at hle; linarith only [hle]
    have h2 : (2 * c₀_D) ^ (3 / 2 : ℝ) ≤ ((9 * d₀ / 128) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : ((9 * d₀ / 128) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = 9 * d₀ / 128 := by
      rw [← Real.rpow_mul (by positivity)]; norm_num
    rw [h3] at h2
    linarith only [h2]
  let d_D : ℝ := 3 * d₀ / 32
  have hd_D_pos : 0 < d_D := by positivity
  let α : ℝ := 9 * d₀ / 128
  have hα_pos : 0 < α := by positivity
  let A_sig : ℝ := virasoroEnvC1 * Real.sqrt (2 * c₀_D)
  have hA_sig_nn : 0 ≤ A_sig := by positivity [virasoroEnvC1_pos]
  let C_arc0 : ℝ := 2 * virasoroInnerEnvC0 / (2 * c₀_D) + 2 * C_P + 1
  have hC_arc0_gt1 : 1 < C_arc0 := by
    dsimp [C_arc0]
    exact lt_add_of_pos_left 1 (by positivity [virasoroInnerEnvC0_pos])
  let B_log : ℝ := 2 * A_sig + 2 / 3
  have hB_log_nn : 0 ≤ B_log := by positivity
  let C_const_log : ℝ := Real.log C_arc0 + (1 / 4 : ℝ) * Real.log (2 * C_real)
  let c_thr_exp : ℝ := ((max 0 C_const_log + B_log + 1) / α) ^ 2 + 1
  let c_thr_diam : ℝ := (max 0 (Real.log (2 * C_real))) / (21 * d₀ / 32) + 1
  obtain ⟨c_D, hc_D_eq⟩ : ∃ x : ℝ,
      x = max (max c_real c_P) (max virasoroCQEnv (max c_thr_exp c_thr_diam)) := ⟨_, rfl⟩
  obtain ⟨C_D, hC_D_eq⟩ : ∃ x : ℝ, x = max (2 * C_real) 2 := ⟨_, rfl⟩
  have hC_D_pos : 0 < C_D := by rw [hC_D_eq]; positivity
  refine ⟨c_D, C_D, d_D, c₀_D, ?_, hC_D_pos, hd_D_pos, hc₀_D_pos, hc₀_D_le4, ?_⟩
  · rw [hc_D_eq]; exact hc_real_10000.trans ((le_max_left _ _).trans (le_max_left _ _))
  intro c' hc' g hg hM_pos u hu
  have hc'_real : c_real ≤ c' := (hc_D_eq ▸ (le_max_left _ _).trans (le_max_left _ _)).trans hc'
  have hc'_P : c_P ≤ c' := (hc_D_eq ▸ (le_max_right _ _).trans (le_max_left _ _)).trans hc'
  have hc'_Q : virasoroCQEnv ≤ c' := (hc_D_eq ▸ (le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hc'_exp : c_thr_exp ≤ c' :=
    (hc_D_eq ▸ (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hc'_diam : c_thr_diam ≤ c' :=
    (hc_D_eq ▸ (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hc'_10000 : 10000 ≤ c' := hc_real_10000.trans hc'_real
  have hc'_1000 : 1000 ≤ c' := by linarith only [hc'_10000]
  have hc'_pos : 0 < c' := by linarith only [hc'_10000]
  let U₀ : ℝ := 2 * c₀_D * c' ^ (2 / 3 : ℝ)
  have hU₀_pos : 0 < U₀ := by positivity
  have hU₀_le_in : U₀ ≤ (innerChartRadius / 2) * c' ^ (2 / 3 : ℝ) := by
    have h2 : 2 * c₀_D ≤ innerChartRadius / 2 := by linarith only [hc₀_D_le4]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hc'_pos.le _)
  have hU₀_lt_rad : U₀ < innerChartRadius * c' ^ (2 / 3 : ℝ) := by
    refine hU₀_le_in.trans_lt (mul_lt_mul_of_pos_right (half_lt_self innerChartRadius_pos)
      (Real.rpow_pos_of_pos hc'_pos _))
  have hU₀_ang : (4 / 3 : ℝ) * U₀ ^ (3 / 2 : ℝ) ≤ (3 * d₀ / 32) * c' := by
    have hpow : U₀ ^ (3 / 2 : ℝ) = (2 * c₀_D) ^ (3 / 2 : ℝ) * c' := by
      dsimp [U₀]
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hc'_pos.le _),
        ← Real.rpow_mul hc'_pos.le]
      norm_num
    rw [hpow]
    calc (4 / 3 : ℝ) * ((2 * c₀_D) ^ (3 / 2 : ℝ) * c')
        = ((4 / 3 : ℝ) * (2 * c₀_D) ^ (3 / 2 : ℝ)) * c' := by ring
      _ ≤ (3 * d₀ / 32) * c' := mul_le_mul_of_nonneg_right h2c₀_ang hc'_pos.le
  have hreal_U₀ : ∀ x : ℝ, |x| ≤ U₀ →
      ‖virasoroPsiTilde c' g (x : ℂ) - truncatedMellinP c' dpT0 g (x : ℂ)‖ ≤
        C_real * Real.exp (-(3 * d₀ / 4) * c') := fun x hx => by
    have hx' : |x| ≤ c₀_real * c' ^ (2 / 3 : ℝ) :=
      hx.trans (mul_le_mul_of_nonneg_right h2c₀_real (Real.rpow_nonneg hc'_pos.le _))
    rw [hd₀_eq]
    exact hreal_fn hc'_real hg hM_pos x hx'
  have hP_U₀ : ∀ w ∈ closedBall (0 : ℂ) U₀, ¬ (w.im = 0 ∧ w.re ≤ 0) →
      ‖truncatedMellinP c' dpT0 g w‖ ≤ C_P * c' ^ (1 / 3 : ℝ) * airyEnv w := fun w hw hcut => by
    have hw' : w ∈ closedBall (0 : ℂ) (c₀_P * c' ^ (2 / 3 : ℝ)) :=
      closedBall_subset_closedBall (mul_le_mul_of_nonneg_right h2c₀_P (Real.rpow_nonneg hc'_pos.le _)) hw
    exact hP_fn hc'_P hg hM_pos hw' hcut
  have hPsi_U₀ : ∀ w ∈ closedBall (0 : ℂ) U₀, ¬ (w.im = 0 ∧ w.re ≤ 0) →
      ‖virasoroPsiTilde c' g w‖ ≤
        virasoroInnerEnvC0 * airyEnv w * Real.exp (virasoroSigma c' * (w ^ (1 / 2 : ℂ)).re) *
          ‖w‖ ^ (-(1 / 2 : ℝ)) * ((w ^ (1 / 2 : ℂ)).re)⁻¹ := fun w hw hcut => by
    have hw' : w ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) :=
      closedBall_subset_closedBall hU₀_lt_rad.le hw
    exact virasoroPsiTilde_inner_typeII_envelope hc'_Q hg hM_pos hw' hcut
  let F_u : ℂ → ℂ := fun w =>
    (1 + w / (U₀ : ℂ)) * (truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w) *
      Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)
  have hF_norm_real_u0 : ∀ x : ℝ, |x| ≤ U₀ →
      ‖Complex.exp ((4 / 3 : ℂ) * (x : ℂ) * halfUpper (x : ℂ))‖ ≤
        Real.exp ((4 / 3 : ℝ) * U₀ ^ (3 / 2 : ℝ)) := fun x hx => by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    rcases lt_trichotomy x 0 with hx_neg | rfl | hx_pos
    · rw [halfUpper_negReal hx_neg]
      have : ((4 / 3 : ℂ) * (x : ℂ) * (Complex.I * (Real.sqrt (-x) : ℂ))).re = 0 := by
        have h1 : (4 / 3 : ℂ) * (x : ℂ) * (Complex.I * (Real.sqrt (-x) : ℂ)) =
            Complex.I * ((4 / 3 * x * Real.sqrt (-x) : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.I_mul_re, Complex.ofReal_im, neg_zero]
      rw [this]; positivity
    · simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.zero_re]; positivity
    · rw [halfUpper_posReal hx_pos]
      have h1 : ((4 / 3 : ℂ) * (x : ℂ) * (Real.sqrt x : ℂ)).re = (4 / 3 : ℝ) * x * Real.sqrt x := by
        have : (4 / 3 : ℂ) * (x : ℂ) * (Real.sqrt x : ℂ) = ((4 / 3 * x * Real.sqrt x : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, Complex.ofReal_re]
      rw [h1]
      have hxr : x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx_pos.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]
        norm_num
      rw [mul_assoc, hxr]
      have hx_le : x ≤ U₀ := le_trans (le_abs_self x) hx
      gcongr
  let M_diam : ℝ := 2 * C_real * Real.exp (-(3 * d₀ / 4 - 3 * d₀ / 32) * c')
  have hM_diam_pos : 0 < M_diam := by positivity
  have hM_diam_le_one : M_diam ≤ 1 := by
    have hlog_bd : Real.log (2 * C_real) ≤ (21 * d₀ / 32) * c' := by
      have h1 : max 0 (Real.log (2 * C_real)) ≤ (21 * d₀ / 32) * c' := by
        have h_den : 0 < 21 * d₀ / 32 := by positivity
        have h_c : (max 0 (Real.log (2 * C_real))) / (21 * d₀ / 32) ≤ c' := by
          have hc_def : c_thr_diam = (max 0 (Real.log (2 * C_real))) / (21 * d₀ / 32) + 1 := rfl
          linarith only [hc'_diam, hc_def]
        calc max 0 (Real.log (2 * C_real))
            = (21 * d₀ / 32) * ((max 0 (Real.log (2 * C_real))) / (21 * d₀ / 32)) := by
              field_simp [h_den.ne']
          _ ≤ (21 * d₀ / 32) * c' := by gcongr
      exact (le_max_right _ _).trans h1
    dsimp [M_diam]
    rw [← Real.exp_log (by positivity : 0 < 2 * C_real), ← Real.exp_add]
    rw [Real.exp_le_one_iff]
    linarith only [hlog_bd]
  let M_PJ : ℝ := 2 * virasoroInnerEnvC0 / U₀ * Real.exp (virasoroSigma c' * Real.sqrt U₀) +
    2 * C_P * c' ^ (1 / 3 : ℝ) + 1
  have hM_PJ_gt_one : 1 < M_PJ := by
    dsimp [M_PJ]
    exact lt_add_of_pos_left 1 (by positivity [virasoroInnerEnvC0_pos])
  have hM_PJ_ge_diam : M_diam ≤ M_PJ := hM_diam_le_one.trans hM_PJ_gt_one.le
  have hhalf_F_bd : ∀ w : ℂ, w ∈ ball (0 : ℂ) U₀ ∩ {z : ℂ | 0 < z.im} →
      ‖F_u w‖ ≤ M_PJ := by
    let U_set : Set ℂ := ball (0 : ℂ) U₀ ∩ {z : ℂ | 0 < z.im}
    have hU_bdd : Bornology.IsBounded U_set := Metric.isBounded_ball.subset inter_subset_left
    have hU_open : IsOpen U_set := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
    have hcl_sub : closure U_set ⊆ closedBall (0 : ℂ) U₀ ∩ {z : ℂ | 0 ≤ z.im} := by
      refine closure_minimal (fun z hz => ⟨ball_subset_closedBall hz.1, show 0 ≤ z.im from le_of_lt hz.2⟩)
        (isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im))
    have hw_half_cont : ContinuousOn (fun w : ℂ => w * halfUpper w) (closure U_set) := by
      intro w hw
      have hw_im : 0 ≤ w.im := (hcl_sub hw).2
      by_cases hw0 : w = 0
      · subst hw0
        refine ContinuousAt.continuousWithinAt ?_
        rw [ContinuousAt, zero_mul, tendsto_iff_norm_sub_tendsto_zero]
        have h_le : ∀ z : ℂ, ‖z * halfUpper z - 0‖ ≤ ‖z‖ * Real.sqrt ‖z‖ := fun z => by
          rw [sub_zero, norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have hsq : ‖halfUpper z‖ ^ 2 = ‖z‖ := by
            calc ‖halfUpper z‖ ^ 2 = ‖halfUpper z ^ 2‖ := (norm_pow _ 2).symm
              _ = ‖z‖ := by rw [halfUpper_sq_eq]
          rw [← Real.sqrt_sq (norm_nonneg (halfUpper z)), hsq]
        refine squeeze_zero (fun _ => norm_nonneg _) h_le ?_
        have ht : Tendsto (fun z : ℂ => ‖z‖ * Real.sqrt ‖z‖) (𝓝 0) (𝓝 (‖(0 : ℂ)‖ * Real.sqrt ‖(0 : ℂ)‖)) :=
          (continuous_norm.mul (Real.continuous_sqrt.comp continuous_norm)).continuousAt.tendsto
        simpa using ht
      · exact (continuousAt_id.mul (halfUpper_analyticAt_upper_or_real hw_im hw0).continuousAt).continuousWithinAt
    have hcl_ball : closure U_set ⊆ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) :=
      fun w hw => mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp (hcl_sub hw).1).trans_lt hU₀_lt_rad)
    have hcl_psi : closure U_set ⊆ virasoroPsiDom c' := fun w hw => by
      have hb := virasoroBChart_inner_bounds hc'_pos (hcl_ball hw |> ball_subset_closedBall)
      exact ⟨hb.1, hb.2.2.2.2.1⟩
    have hF_diffOn : DifferentiableOn ℂ F_u U_set := fun w hw => by
      have hw_rad := hcl_ball (subset_closure hw)
      have hw_psi := hcl_psi (subset_closure hw)
      have hP_d := (truncatedMellinP_analyticOnNhd hc'_1000 dpT0 hg w hw_rad).differentiableAt
      have hPsi_d := (virasoroPsiTilde_analyticOnNhd hc'_1000 hg w hw_psi).differentiableAt
      have hw_ne : w ≠ 0 := fun h0 => by have := hw.2; simp [h0] at this
      have hU_d := (halfUpper_analyticAt_upper_or_real hw.2.le hw_ne).differentiableAt
      have hlin : DifferentiableAt ℂ (fun z : ℂ => 1 + z / (U₀ : ℂ)) w := by fun_prop
      have hexp : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((4 / 3 : ℂ) * z * halfUpper z)) w :=
        ((differentiableAt_const _ |>.mul differentiableAt_id).mul hU_d).cexp
      exact ((hlin.mul (hP_d.sub hPsi_d)).mul hexp).differentiableWithinAt
    have hF_contOn : ContinuousOn F_u (closure U_set) := by
      have hlin : ContinuousOn (fun w : ℂ => 1 + w / (U₀ : ℂ)) (closure U_set) := by fun_prop
      have hP_c : ContinuousOn (truncatedMellinP c' dpT0 g) (closure U_set) :=
        (truncatedMellinP_analyticOnNhd hc'_1000 dpT0 hg).continuousOn.mono hcl_ball
      have hPsi_c : ContinuousOn (virasoroPsiTilde c' g) (closure U_set) :=
        (virasoroPsiTilde_analyticOnNhd hc'_1000 hg).continuousOn.mono hcl_psi
      have hexp_c : ContinuousOn (fun w : ℂ => Complex.exp ((4 / 3 : ℂ) * w * halfUpper w))
          (closure U_set) := by
        have hmul_c : ContinuousOn (fun w : ℂ => (4 / 3 : ℂ) * (w * halfUpper w)) (closure U_set) :=
          continuousOn_const.mul hw_half_cont
        exact hmul_c.cexp.congr fun w _ => congrArg Complex.exp (mul_assoc _ _ _)
      exact (hlin.mul (hP_c.sub hPsi_c)).mul hexp_c
    have hF_front : ∀ w ∈ frontier U_set, ‖F_u w‖ ≤ M_PJ := fun w hw => by
      have hw_cl := hw.1
      have hw_not_in : w ∉ U_set := (hU_open.frontier_eq ▸ hw).2
      have hw_cb := (hcl_sub hw_cl).1
      have hw_im_nn : 0 ≤ w.im := (hcl_sub hw_cl).2
      have hnorm_le := mem_closedBall_zero_iff.mp hw_cb
      rcases eq_or_lt_of_le hw_im_nn with him0 | him_pos
      · -- `w` is real with `|w.re| ≤ U₀`
        have hw_real : w = (w.re : ℂ) := Complex.ext rfl him0.symm
        have hxw : |w.re| ≤ U₀ := by
          have hnw : ‖w‖ = |w.re| := by
            conv_lhs => rw [hw_real]
            rw [Complex.norm_real, Real.norm_eq_abs]
          linarith only [hnorm_le, hnw]
        have hlin_bd : ‖1 + w / (U₀ : ℂ)‖ ≤ 2 := by
          calc ‖1 + w / (U₀ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖w / (U₀ : ℂ)‖ := norm_add_le _ _
            _ = 1 + ‖w‖ / U₀ := by
                rw [norm_one, norm_div, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le]
            _ ≤ 1 + U₀ / U₀ := by gcongr
            _ = 2 := by rw [div_self hU₀_pos.ne']; norm_num
        have hdiff_bd := hreal_U₀ w.re hxw
        rw [← hw_real] at hdiff_bd
        have hdiff_bd' : ‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖ ≤
            C_real * Real.exp (-(3 * d₀ / 4) * c') := by
          simpa [norm_sub_rev] using hdiff_bd
        have hexp_bd : ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ ≤
            Real.exp ((3 * d₀ / 32) * c') := by
          rw [hw_real]
          exact (hF_norm_real_u0 w.re hxw).trans (Real.exp_le_exp.mpr hU₀_ang)
        have hF_bd_diam : ‖F_u w‖ ≤ M_diam := by
          dsimp [F_u, M_diam]
          rw [norm_mul, norm_mul]
          calc ‖1 + w / (U₀ : ℂ)‖ * ‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖ *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖
              ≤ 2 * (C_real * Real.exp (-(3 * d₀ / 4) * c')) * Real.exp ((3 * d₀ / 32) * c') := by
                gcongr
            _ = 2 * C_real * (Real.exp (-(3 * d₀ / 4) * c') * Real.exp ((3 * d₀ / 32) * c')) := by
                ring
            _ = 2 * C_real * Real.exp (-(3 * d₀ / 4 - 3 * d₀ / 32) * c') := by
                rw [← Real.exp_add]; congr 2; ring
        exact hF_bd_diam.trans hM_PJ_ge_diam
      · -- `0 < w.im` and `‖w‖ = U₀`
        have hw_norm_eq : ‖w‖ = U₀ := by
          by_contra hne
          exact hw_not_in ⟨mem_ball_zero_iff.mpr (lt_of_le_of_ne hnorm_le hne), him_pos⟩
        have hw_cut : ¬ (w.im = 0 ∧ w.re ≤ 0) := fun ⟨him0, _⟩ => by linarith only [him0, him_pos]
        have hw_exp_eq : (4 / 3 : ℂ) * w * halfUpper w = (4 / 3 : ℂ) * w ^ (3 / 2 : ℂ) := by
          rw [halfUpper_eq_cpow_half_of_im_pos him_pos]
          have hpow3 : w * w ^ (1 / 2 : ℂ) = w ^ (3 / 2 : ℂ) := by
            have hw_ne : w ≠ 0 := fun h0 => by simp [h0] at him_pos
            conv_lhs => arg 1; rw [← Complex.cpow_one w]
            rw [← Complex.cpow_add _ _ hw_ne]
            congr 1; norm_num
          rw [mul_assoc, hpow3]
        have hexp_air : ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ * airyEnv w = 1 := by
          rw [hw_exp_eq, Complex.norm_exp]
          have hre : ((4 / 3 : ℂ) * w ^ (3 / 2 : ℂ)).re = (4 / 3 : ℝ) * (w ^ (3 / 2 : ℂ)).re := by
            rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
          rw [hre]; unfold airyEnv; rw [← Real.exp_add]; simp
        have hlin_exact : ‖1 + w / (U₀ : ℂ)‖ = 2 * (w ^ (1 / 2 : ℂ)).re / Real.sqrt U₀ := by
          set v : ℂ := w ^ (1 / 2 : ℂ)
          have hv2 : v ^ 2 = w := FormalResearch.Special.cpow_half_sq w
          have hv_norm : ‖v‖ = Real.sqrt U₀ := by
            have hsq : ‖v‖ ^ 2 = U₀ := by
              calc ‖v‖ ^ 2 = ‖v ^ 2‖ := (norm_pow _ 2).symm
                _ = ‖w‖ := by rw [hv2]
                _ = U₀ := hw_norm_eq
            rw [← Real.sqrt_sq (norm_nonneg v), hsq]
          have hv_conj : v * starRingEnd ℂ v = (U₀ : ℂ) := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv_norm, Real.sq_sqrt hU₀_pos.le]
          have hrew : 1 + w / (U₀ : ℂ) = (v / (U₀ : ℂ)) * ((2 * v.re : ℝ) : ℂ) := by
            have hv_sum : v + starRingEnd ℂ v = ((2 * v.re : ℝ) : ℂ) := by
              apply Complex.ext
              · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]; ring
              · simp only [Complex.add_im, Complex.conj_im, Complex.ofReal_im]; ring
            have hU_ne : (U₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU₀_pos.ne'
            calc 1 + w / (U₀ : ℂ) = (v * starRingEnd ℂ v + v ^ 2) / (U₀ : ℂ) := by
                  rw [hv_conj, hv2, add_div, div_self hU_ne]
              _ = (v / (U₀ : ℂ)) * (starRingEnd ℂ v + v) := by ring
              _ = (v / (U₀ : ℂ)) * ((2 * v.re : ℝ) : ℂ) := by rw [add_comm, hv_sum]
          have hv_re_nn : 0 ≤ v.re := cpow_half_re_nonneg w
          rw [hrew, norm_mul, norm_div, hv_norm, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le,
            Complex.norm_real, Real.norm_of_nonneg (by linarith only [hv_re_nn])]
          rw [show Real.sqrt U₀ / U₀ * (2 * v.re) = 2 * v.re / Real.sqrt U₀ * (Real.sqrt U₀ ^ 2 / U₀) by
              field_simp [hU₀_pos.ne'],
            Real.sq_sqrt hU₀_pos.le, div_self hU₀_pos.ne', mul_one]
        have hlin_le2 : ‖1 + w / (U₀ : ℂ)‖ ≤ 2 := by
          calc ‖1 + w / (U₀ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖w / (U₀ : ℂ)‖ := norm_add_le _ _
            _ = 1 + U₀ / U₀ := by
                rw [norm_one, norm_div, hw_norm_eq, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le]
            _ = 2 := by rw [div_self hU₀_pos.ne']; norm_num
        have hP_term : ‖(1 + w / (U₀ : ℂ)) * truncatedMellinP c' dpT0 g w *
            Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ ≤ 2 * C_P * c' ^ (1 / 3 : ℝ) := by
          have hP_w := hP_U₀ w hw_cb hw_cut
          rw [norm_mul, norm_mul]
          calc ‖1 + w / (U₀ : ℂ)‖ * ‖truncatedMellinP c' dpT0 g w‖ *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖
              ≤ 2 * (C_P * c' ^ (1 / 3 : ℝ) * airyEnv w) *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ := by gcongr
            _ = 2 * C_P * c' ^ (1 / 3 : ℝ) * (‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ * airyEnv w) := by
                ring
            _ = 2 * C_P * c' ^ (1 / 3 : ℝ) := by rw [hexp_air, mul_one]
        have hPsi_term : ‖(1 + w / (U₀ : ℂ)) * virasoroPsiTilde c' g w *
            Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ ≤
            2 * virasoroInnerEnvC0 / U₀ * Real.exp (virasoroSigma c' * Real.sqrt U₀) := by
          have hPsi_w := hPsi_U₀ w hw_cb hw_cut
          have hv_re_pos : 0 < (w ^ (1 / 2 : ℂ)).re := by
            by_contra hle
            have hre0 : (w ^ (1 / 2 : ℂ)).re = 0 :=
              le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg w)
            have him_w := congrArg Complex.im (FormalResearch.Special.cpow_half_sq w)
            rw [sq, Complex.mul_im, hre0, zero_mul, mul_zero, add_zero] at him_w
            linarith only [him_w, him_pos]
          have hv_re_le : (w ^ (1 / 2 : ℂ)).re ≤ Real.sqrt U₀ := by
            have h1 : (w ^ (1 / 2 : ℂ)).re ≤ ‖w ^ (1 / 2 : ℂ)‖ := Complex.re_le_norm _
            have hsq : ‖w ^ (1 / 2 : ℂ)‖ ^ 2 = U₀ := by
              rw [← norm_pow, FormalResearch.Special.cpow_half_sq, hw_norm_eq]
            have hn : ‖w ^ (1 / 2 : ℂ)‖ = Real.sqrt U₀ := by
              rw [← Real.sqrt_sq (norm_nonneg _), hsq]
            linarith only [h1, hn]
          have hsig_le : Real.exp (virasoroSigma c' * (w ^ (1 / 2 : ℂ)).re) ≤
              Real.exp (virasoroSigma c' * Real.sqrt U₀) := by
            refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv_re_le ?_)
            exact virasoroSigma_nonneg (by linarith only [hc'_10000])
          have hnorm_half : ‖w‖ ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt U₀ := by
            rw [hw_norm_eq, Real.rpow_neg hU₀_pos.le, ← Real.sqrt_eq_rpow, one_div]
          rw [norm_mul, norm_mul, hlin_exact]
          calc (2 * (w ^ (1 / 2 : ℂ)).re / Real.sqrt U₀) * ‖virasoroPsiTilde c' g w‖ *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖
              ≤ (2 * (w ^ (1 / 2 : ℂ)).re / Real.sqrt U₀) *
                  (virasoroInnerEnvC0 * airyEnv w * Real.exp (virasoroSigma c' * (w ^ (1 / 2 : ℂ)).re) *
                    (1 / Real.sqrt U₀) * ((w ^ (1 / 2 : ℂ)).re)⁻¹) *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ := by
                gcongr
                · exact (hPsi_w.trans_eq (by rw [hnorm_half]))
            _ = (2 * virasoroInnerEnvC0 / (Real.sqrt U₀ ^ 2)) *
                  ((w ^ (1 / 2 : ℂ)).re * ((w ^ (1 / 2 : ℂ)).re)⁻¹) *
                  (‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ * airyEnv w) *
                  Real.exp (virasoroSigma c' * (w ^ (1 / 2 : ℂ)).re) := by ring
            _ = (2 * virasoroInnerEnvC0 / U₀) * 1 * 1 *
                  Real.exp (virasoroSigma c' * (w ^ (1 / 2 : ℂ)).re) := by
                rw [Real.sq_sqrt hU₀_pos.le, mul_inv_cancel₀ hv_re_pos.ne', hexp_air]
            _ ≤ 2 * virasoroInnerEnvC0 / U₀ * Real.exp (virasoroSigma c' * Real.sqrt U₀) := by
                rw [mul_one, mul_one]
                exact mul_le_mul_of_nonneg_left hsig_le (by have := virasoroInnerEnvC0_pos; positivity)
        have hF_split : F_u w =
            (1 + w / (U₀ : ℂ)) * truncatedMellinP c' dpT0 g w *
              Complex.exp ((4 / 3 : ℂ) * w * halfUpper w) -
            (1 + w / (U₀ : ℂ)) * virasoroPsiTilde c' g w *
              Complex.exp ((4 / 3 : ℂ) * w * halfUpper w) := by
          dsimp [F_u]; ring
        rw [hF_split]
        calc ‖_ - _‖ ≤ ‖(1 + w / (U₀ : ℂ)) * truncatedMellinP c' dpT0 g w *
                Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ +
              ‖(1 + w / (U₀ : ℂ)) * virasoroPsiTilde c' g w *
                Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ := norm_sub_le _ _
          _ ≤ 2 * C_P * c' ^ (1 / 3 : ℝ) +
              2 * virasoroInnerEnvC0 / U₀ * Real.exp (virasoroSigma c' * Real.sqrt U₀) :=
              add_le_add hP_term hPsi_term
          _ ≤ M_PJ := by
              have hdef : M_PJ = 2 * virasoroInnerEnvC0 / U₀ * Real.exp (virasoroSigma c' * Real.sqrt U₀) +
                2 * C_P * c' ^ (1 / 3 : ℝ) + 1 := rfl
              linarith only [hdef]
    exact fun w hw => Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd ⟨hF_diffOn, hF_contOn⟩
      hF_front (subset_closure hw)
  -- Helper: handle `u ∈ closedBall 0 (c₀_D * c'^(2/3))` with `0 ≤ u.im`
  have hDp_upper : ∀ w : ℂ, 0 ≤ w.im → w ∈ closedBall (0 : ℂ) (c₀_D * c' ^ (2 / 3 : ℝ)) →
      ‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖ ≤
        C_D * Real.exp (-d_D * c') * airyEnv w := fun w hw_im hw_cb => by
    rcases eq_or_lt_of_le hw_im with him0 | him_pos
    · have hw_real : w = (w.re : ℂ) := Complex.ext rfl him0.symm
      have hx_le : |w.re| ≤ U₀ := by
        have h1 : ‖w‖ ≤ c₀_D * c' ^ (2 / 3 : ℝ) := mem_closedBall_zero_iff.mp hw_cb
        have h2 : c₀_D * c' ^ (2 / 3 : ℝ) ≤ U₀ := by
          have hp := mul_pos hc₀_D_pos (Real.rpow_pos_of_pos hc'_pos (2 / 3 : ℝ))
          have hU_def : U₀ = 2 * c₀_D * c' ^ (2 / 3 : ℝ) := rfl
          linarith only [hp, hU_def]
        have hnw : ‖w‖ = |w.re| := by
          conv_lhs => rw [hw_real]
          rw [Complex.norm_real, Real.norm_eq_abs]
        linarith only [h1, h2, hnw]
      have hreal_bd : ‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖ ≤
          C_real * Real.exp (-(3 * d₀ / 4) * c') := by
        rw [hw_real, norm_sub_rev]
        exact hreal_U₀ w.re hx_le
      have hair_lb : Real.exp (-(3 * d₀ / 32) * c') ≤ airyEnv w := by
        unfold airyEnv
        refine Real.exp_le_exp.mpr ?_
        have h_re_le : (w ^ (3 / 2 : ℂ)).re ≤ U₀ ^ (3 / 2 : ℝ) := by
          have h1 : (w ^ (3 / 2 : ℂ)).re ≤ ‖w ^ (3 / 2 : ℂ)‖ := Complex.re_le_norm _
          have h2 : ‖w ^ (3 / 2 : ℂ)‖ ≤ U₀ ^ (3 / 2 : ℝ) := by
            by_cases hw0 : w = 0
            · subst hw0; simp; positivity
            · rw [Complex.cpow_def_of_ne_zero hw0, Complex.norm_exp]
              have hre : (Complex.log w * (3 / 2 : ℂ)).re = (3 / 2 : ℝ) * Real.log ‖w‖ := by
                have h32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by push_cast; rfl
                rw [h32, mul_comm, Complex.re_ofReal_mul, Complex.log_re]
              rw [hre, mul_comm (3 / 2 : ℝ) (Real.log ‖w‖), ← Real.rpow_def_of_pos (norm_pos_iff.mpr hw0)]
              have hle_U₀ : ‖w‖ ≤ U₀ := by
                have h1' := mem_closedBall_zero_iff.mp hw_cb
                have hp := mul_pos hc₀_D_pos (Real.rpow_pos_of_pos hc'_pos (2 / 3 : ℝ))
                have hU_def : U₀ = 2 * c₀_D * c' ^ (2 / 3 : ℝ) := rfl
                linarith only [h1', hp, hU_def]
              exact Real.rpow_le_rpow (norm_nonneg _) hle_U₀ (by norm_num)
          linarith only [h1, h2]
        linarith only [h_re_le, hU₀_ang]
      calc ‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖
          ≤ C_real * Real.exp (-(3 * d₀ / 4) * c') := hreal_bd
        _ = C_real * Real.exp (-(21 * d₀ / 32) * c') * Real.exp (-(3 * d₀ / 32) * c') := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ C_D * Real.exp (-d_D * c') * airyEnv w := by
            have hC_le : C_real ≤ C_D :=
              (by linarith only [hC_real_pos] : C_real ≤ 2 * C_real).trans (hC_D_eq ▸ le_max_left _ _)
            have hexp_le : Real.exp (-(21 * d₀ / 32) * c') ≤ Real.exp (-d_D * c') :=
              Real.exp_le_exp.mpr (by have hd_def : d_D = 3 * d₀ / 32 := rfl; nlinarith only [hd₀_pos, hc'_pos, hd_def])
            gcongr
    · -- `0 < w.im` via `halfPlane_poissonJensen`
      by_cases hFw0 : F_u w = 0
      · have hlin_ne : 1 + w / (U₀ : ℂ) ≠ 0 := by
          intro h0
          have hnorm : ‖w / (U₀ : ℂ)‖ = 1 := by
            have := eq_neg_of_add_eq_zero_right h0
            rw [this, norm_neg, norm_one]
          have hw_le : ‖w‖ ≤ U₀ / 2 := by
            have h1 := mem_closedBall_zero_iff.mp hw_cb
            have hU_def : U₀ = 2 * c₀_D * c' ^ (2 / 3 : ℝ) := rfl
            linarith only [h1, hU_def]
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le] at hnorm
          have hdiv_le : ‖w‖ / U₀ ≤ (U₀ / 2) / U₀ := div_le_div_of_nonneg_right hw_le hU₀_pos.le
          have hdiv_half : (U₀ / 2) / U₀ = 1 / 2 := by field_simp [hU₀_pos.ne']
          linarith only [hnorm, hdiv_le, hdiv_half]
        have hexp_ne : Complex.exp ((4 / 3 : ℂ) * w * halfUpper w) ≠ 0 := Complex.exp_ne_zero _
        have hsub0 : truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w = 0 := by
          dsimp [F_u] at hFw0
          rcases mul_eq_zero.mp hFw0 with h12 | h3
          · rcases mul_eq_zero.mp h12 with h1 | h2
            · exact absurd h1 hlin_ne
            · exact h2
          · exact absurd h3 hexp_ne
        rw [hsub0, norm_zero]
        have := airyEnv_pos w
        positivity
      · let F_z : ℂ → ℂ := fun z => F_u (halfPlaneChart U₀ z)
        let F_bdy : ℝ → ℂ := fun σ => if σ = 0 then 0 else F_u (halfPlaneChart U₀ (σ : ℂ))
        have hFz_diff : DifferentiableOn ℂ F_z {z : ℂ | 0 < z.im} := fun z hz => by
          obtain ⟨hw_norm, hw_im_z⟩ := halfPlaneChart_mem_upperHalf hU₀_pos hz
          have hz_ne : z ≠ 0 := fun h0 => by simp [h0] at hz
          have hw_rad : halfPlaneChart U₀ z ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) :=
            mem_ball_zero_iff.mpr (hw_norm.trans hU₀_lt_rad)
          have hw_psi : halfPlaneChart U₀ z ∈ virasoroPsiDom c' := by
            have hb := virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hw_rad)
            exact ⟨hb.1, hb.2.2.2.2.1⟩
          have hw_ne : halfPlaneChart U₀ z ≠ 0 := fun h0 => by simp [h0] at hw_im_z
          have hFu_d : DifferentiableAt ℂ F_u (halfPlaneChart U₀ z) := by
            have hP_d := (truncatedMellinP_analyticOnNhd hc'_1000 dpT0 hg _ hw_rad).differentiableAt
            have hPsi_d := (virasoroPsiTilde_analyticOnNhd hc'_1000 hg _ hw_psi).differentiableAt
            have hU_d := (halfUpper_analyticAt_upper_or_real hw_im_z.le hw_ne).differentiableAt
            have hlin : DifferentiableAt ℂ (fun x : ℂ => 1 + x / (U₀ : ℂ)) (halfPlaneChart U₀ z) := by fun_prop
            have hexp : DifferentiableAt ℂ (fun x : ℂ => Complex.exp ((4 / 3 : ℂ) * x * halfUpper x))
                (halfPlaneChart U₀ z) :=
              ((differentiableAt_const _ |>.mul differentiableAt_id).mul hU_d).cexp
            exact (hlin.mul (hP_d.sub hPsi_d)).mul hexp
          have hc_d : DifferentiableAt ℂ (halfPlaneChart U₀) z := by
            have hU_d := (halfUpper_analyticAt_upper_or_real (le_of_lt hz) hz_ne).differentiableAt
            have hw_add_ne : halfUpper z + 1 ≠ 0 := by
              have hre1 := (halfUpper_pos_of_im_pos hz).1
              intro h0; have hre0 := congrArg Complex.re h0; simp at hre0; linarith only [hre1, hre0]
            unfold halfPlaneChart
            exact ((differentiableAt_const _ |>.mul (hU_d.sub_const _)).div (hU_d.add_const _) hw_add_ne)
          exact (hFu_d.comp z hc_d).differentiableWithinAt
        have hFz_bd : ∀ z : ℂ, 0 < z.im → ‖F_z z‖ ≤ M_PJ := fun z hz => by
          obtain ⟨h1, h2⟩ := halfPlaneChart_mem_upperHalf hU₀_pos hz
          exact hhalf_F_bd _ ⟨mem_ball_zero_iff.mpr h1, h2⟩
        have hFz_bdy : ∀ᵐ σ : ℝ ∂volume,
            Tendsto F_z (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ)) (𝓝 (F_bdy σ)) := by
          have hne0 : ∀ᵐ σ : ℝ ∂volume, σ ≠ 0 := by
            rw [ae_iff]
            simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, Real.volume_singleton]
          filter_upwards [hne0] with σ hσ0
          have hF_eq_bdy : F_bdy σ = F_u (halfPlaneChart U₀ (σ : ℂ)) := by simp [F_bdy, hσ0]
          rw [hF_eq_bdy]
          have hσ_ne : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ0
          have hU_an := halfUpper_analyticAt_upper_or_real (by simp) hσ_ne
          have hadd_ne : halfUpper (σ : ℂ) + 1 ≠ 0 := by
            rcases lt_trichotomy σ 0 with hneg | rfl | hpos
            · rw [halfUpper_negReal hneg]
              intro h0; have := congrArg Complex.re h0; simp at this
            · exact absurd rfl hσ0
            · rw [halfUpper_posReal hpos]
              intro h0; have hre0 := congrArg Complex.re h0; simp at hre0
              have hsnn := Real.sqrt_nonneg σ
              linarith only [hre0, hsnn]
          have hc_cont : ContinuousAt (halfPlaneChart U₀) (σ : ℂ) := by
            unfold halfPlaneChart
            exact (continuousAt_const.mul (hU_an.continuousAt.sub continuousAt_const)).div
              (hU_an.continuousAt.add continuousAt_const) hadd_ne
          have hchart_im_nn : 0 ≤ (halfPlaneChart U₀ (σ : ℂ)).im ∧
              ‖halfPlaneChart U₀ (σ : ℂ)‖ ≤ U₀ := by
            rcases lt_trichotomy σ 0 with hneg | rfl | hpos
            · rw [halfPlaneChart, halfUpper_negReal hneg]
              set s := Real.sqrt (-σ)
              have hs_pos : 0 < s := Real.sqrt_pos.mpr (by linarith only [hneg])
              have hdiv_im : ((Complex.I * (s : ℂ) - 1) / (Complex.I * (s : ℂ) + 1)).im =
                  2 * s / (1 + s ^ 2) := by
                rw [Complex.div_im, Complex.normSq_apply]
                simp [sq]; ring
              have hdiv_norm : ‖(Complex.I * (s : ℂ) - 1) / (Complex.I * (s : ℂ) + 1)‖ = 1 := by
                rw [norm_div]
                have hsq1 : ‖Complex.I * (s : ℂ) - 1‖ ^ 2 = 1 + s ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
                have hsq2 : ‖Complex.I * (s : ℂ) + 1‖ ^ 2 = 1 + s ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
                have heq : ‖Complex.I * (s : ℂ) - 1‖ = ‖Complex.I * (s : ℂ) + 1‖ :=
                  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hsq1.trans hsq2.symm)
                rw [heq, div_self (norm_ne_zero_iff.mpr (by
                  intro h0; rw [h0, norm_zero] at hsq2; have := sq_nonneg s; nlinarith only [hsq2, this]))]
              constructor
              · rw [mul_div_assoc, Complex.im_ofReal_mul, hdiv_im]; positivity
              · rw [mul_div_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le,
                  hdiv_norm, mul_one]
            · exact absurd rfl hσ0
            · rw [halfPlaneChart, halfUpper_posReal hpos]
              have hr : (U₀ : ℂ) * ((Real.sqrt σ : ℂ) - 1) / ((Real.sqrt σ : ℂ) + 1) =
                  ((U₀ * (Real.sqrt σ - 1) / (Real.sqrt σ + 1) : ℝ) : ℂ) := by
                push_cast; ring
              rw [hr, Complex.ofReal_im, Complex.norm_real, Real.norm_eq_abs]
              refine ⟨le_rfl, ?_⟩
              have hs_nn : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg σ
              have hq_le : |Real.sqrt σ - 1| ≤ Real.sqrt σ + 1 :=
                abs_le.mpr ⟨by linarith only [hs_nn], by linarith only [hs_nn]⟩
              rw [abs_div, abs_mul, abs_of_pos hU₀_pos, abs_of_pos (by linarith only [hs_nn] : 0 < Real.sqrt σ + 1)]
              calc U₀ * |Real.sqrt σ - 1| / (Real.sqrt σ + 1)
                  ≤ U₀ * (Real.sqrt σ + 1) / (Real.sqrt σ + 1) := by gcongr
                _ = U₀ := by field_simp [show Real.sqrt σ + 1 ≠ 0 by linarith only [hs_nn] ]
          have hFu_cont_pt : ContinuousAt F_u (halfPlaneChart U₀ (σ : ℂ)) := by
            have hpt_rad : halfPlaneChart U₀ (σ : ℂ) ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) :=
              mem_ball_zero_iff.mpr (hchart_im_nn.2.trans_lt hU₀_lt_rad)
            have hpt_psi : halfPlaneChart U₀ (σ : ℂ) ∈ virasoroPsiDom c' := by
              have hb := virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hpt_rad)
              exact ⟨hb.1, hb.2.2.2.2.1⟩
            have hP_c := (truncatedMellinP_analyticOnNhd hc'_1000 dpT0 hg _ hpt_rad).continuousAt
            have hPsi_c := (virasoroPsiTilde_analyticOnNhd hc'_1000 hg _ hpt_psi).continuousAt
            have hlin_c : ContinuousAt (fun x : ℂ => 1 + x / (U₀ : ℂ)) (halfPlaneChart U₀ (σ : ℂ)) := by fun_prop
            have h_half_c : ContinuousAt (fun x : ℂ => x * halfUpper x) (halfPlaneChart U₀ (σ : ℂ)) := by
              by_cases h0 : halfPlaneChart U₀ (σ : ℂ) = 0
              · rw [h0, ContinuousAt, zero_mul, tendsto_iff_norm_sub_tendsto_zero]
                have h_le : ∀ z : ℂ, ‖z * halfUpper z - 0‖ ≤ ‖z‖ * Real.sqrt ‖z‖ := fun z => by
                  rw [sub_zero, norm_mul]
                  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
                  have hsq : ‖halfUpper z‖ ^ 2 = ‖z‖ := by
                    calc ‖halfUpper z‖ ^ 2 = ‖halfUpper z ^ 2‖ := (norm_pow _ 2).symm
                      _ = ‖z‖ := by rw [halfUpper_sq_eq]
                  rw [← Real.sqrt_sq (norm_nonneg (halfUpper z)), hsq]
                refine squeeze_zero (fun _ => norm_nonneg _) h_le ?_
                have ht : Tendsto (fun z : ℂ => ‖z‖ * Real.sqrt ‖z‖) (𝓝 0)
                    (𝓝 (‖(0 : ℂ)‖ * Real.sqrt ‖(0 : ℂ)‖)) :=
                  (continuous_norm.mul (Real.continuous_sqrt.comp continuous_norm)).continuousAt.tendsto
                simpa using ht
              · exact continuousAt_id.mul (halfUpper_analyticAt_upper_or_real hchart_im_nn.1 h0).continuousAt
            have hexp_c : ContinuousAt (fun x : ℂ => Complex.exp ((4 / 3 : ℂ) * x * halfUpper x))
                (halfPlaneChart U₀ (σ : ℂ)) := by
              have hEq : (fun x : ℂ => Complex.exp ((4 / 3 : ℂ) * x * halfUpper x)) =
                  fun x => Complex.exp ((4 / 3 : ℂ) * (x * halfUpper x)) := by
                ext x; exact congrArg Complex.exp (mul_assoc _ _ _)
              rw [hEq]
              exact (continuousAt_const.mul h_half_c).cexp
            exact (hlin_c.mul (hP_c.sub hPsi_c)).mul hexp_c
          exact (hFu_cont_pt.comp hc_cont).tendsto.mono_left nhdsWithin_le_nhds
        -- Construct `z₀` with `halfPlaneChart U₀ z₀ = w`, `0 < z₀.im`, `-z₀.im ≤ z₀.re`
        have hw_half_U₀ : ‖w‖ ≤ U₀ / 2 := by
          have h1 := mem_closedBall_zero_iff.mp hw_cb
          have hU_def : U₀ = 2 * c₀_D * c' ^ (2 / 3 : ℝ) := rfl
          linarith only [h1, hU_def]
        obtain ⟨z₀, hz₀_im, hz₀_re_lb, hchart_z₀⟩ :=
          exists_halfPlaneChart_preimage hU₀_pos him_pos hw_half_U₀
        have hζ_norm : ‖w / (U₀ : ℂ)‖ ≤ 1 / 2 := by
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le, div_le_iff₀ hU₀_pos]
          linarith only [hw_half_U₀]
        have hFz₀_ne : F_z z₀ ≠ 0 := by
          dsimp [F_z]; rw [hchart_z₀]; exact hFw0
        have hPJ := halfPlane_poissonJensen (zero_lt_one.trans hM_PJ_gt_one)
          hFz_diff hFz_bd hFz_bdy hz₀_im hFz₀_ne
        have hpk := poissonKernel_Ioi_ge_quarter hz₀_im hz₀_re_lb
        have hlog_diam_bd : ∀ᵐ σ : ℝ ∂volume,
            0 < σ → Real.log ‖F_bdy σ‖ ≤ Real.log M_diam := by
          let D : ℂ → ℂ := fun z => truncatedMellinP c' dpT0 g z - virasoroPsiTilde c' g z
          have hD_an : AnalyticOnNhd ℂ D (ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :=
            (truncatedMellinP_analyticOnNhd hc'_1000 dpT0 hg).sub
              ((virasoroPsiTilde_analyticOnNhd hc'_1000 hg).mono fun z hz => by
                have hb := virasoroBChart_inner_bounds hc'_pos (ball_subset_closedBall hz)
                exact ⟨hb.1, hb.2.2.2.2.1⟩)
          have hDw_ne : D w ≠ 0 := by
            intro h0
            apply hFw0
            dsimp [F_u, D] at *; rw [h0, mul_zero, zero_mul]
          have hw_ball : w ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) :=
            mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw_cb).trans_lt (by
              have hin_pos := innerChartRadius_pos
              exact mul_lt_mul_of_pos_right (hc₀_D_le4.trans_lt (by linarith only [hin_pos]))
                (Real.rpow_pos_of_pos hc'_pos (2 / 3 : ℝ))))
          let S_zero : Set ℝ := {x : ℝ | |x| < U₀ ∧ D (x : ℂ) = 0}
          have hS_fin : S_zero.Finite := by
            by_contra hinf
            rw [Set.not_finite] at hinf
            obtain ⟨r₀, hr₀_Icc, hacc⟩ :=
              hinf.exists_accPt_of_subset_isCompact (isCompact_Icc (a := -U₀) (b := U₀))
                (fun x hx => ⟨(abs_lt.mp hx.1).1.le, (abs_lt.mp hx.1).2.le⟩)
            have hr₀_abs : |r₀| ≤ U₀ := abs_le.mpr hr₀_Icc
            have hr₀_ball : (r₀ : ℂ) ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) :=
              mem_ball_zero_iff.mpr (by
                rw [Complex.norm_real, Real.norm_eq_abs]; exact hr₀_abs.trans_lt hU₀_lt_rad)
            have hfreq : ∃ᶠ z in 𝓝[≠] (r₀ : ℂ), D z = 0 := by
              rw [Filter.frequently_iff]
              intro U hU
              rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
              obtain ⟨V, hV, hVU⟩ := hU
              obtain ⟨ε, hε_pos, hball⟩ := Metric.mem_nhds_iff.mp hV
              rw [accPt_iff_frequently] at hacc
              obtain ⟨r, ⟨hr_ne, hr_mem⟩, hr_ball⟩ :=
                (hacc.and_eventually (Metric.ball_mem_nhds r₀ hε_pos)).exists
              have hrC_ne : (r : ℂ) ≠ (r₀ : ℂ) := fun he => hr_ne (Complex.ofReal_injective he)
              have hrC_ball : (r : ℂ) ∈ Metric.ball (r₀ : ℂ) ε := by
                rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
                  Real.norm_eq_abs]
                simpa [Metric.mem_ball, Real.dist_eq] using hr_ball
              exact ⟨(r : ℂ), hVU ⟨hball hrC_ball, hrC_ne⟩, hr_mem.2⟩
            have hzero := hD_an.eqOn_zero_of_preconnected_of_frequently_eq_zero
              (convex_ball _ _).isPreconnected hr₀_ball hfreq
            exact hDw_ne (hzero hw_ball)
          let g_inv : ℝ → ℝ := fun x => ((U₀ + x) / (U₀ - x)) ^ 2
          have hg_zero_sub : {σ : ℝ | 0 < σ ∧ D (halfPlaneChart U₀ (σ : ℂ)) = 0} ⊆ g_inv '' S_zero := by
            intro σ ⟨hσ, hDσ⟩
            set s := Real.sqrt σ
            have hs_pos : 0 < s := Real.sqrt_pos.mpr hσ
            have hc_eq : halfPlaneChart U₀ (σ : ℂ) = ((U₀ * (s - 1) / (s + 1) : ℝ) : ℂ) := by
              unfold halfPlaneChart; rw [halfUpper_posReal hσ]; push_cast; ring
            set x := U₀ * (s - 1) / (s + 1)
            have hx_lt : |x| < U₀ := by
              have h1 : |s - 1| < s + 1 := abs_lt.mpr ⟨by linarith only [hs_pos], by linarith only [hs_pos]⟩
              dsimp [x]
              rw [abs_div, abs_mul, abs_of_pos hU₀_pos, abs_of_pos (by linarith only [hs_pos] : 0 < s + 1),
                div_lt_iff₀ (by linarith only [hs_pos] : 0 < s + 1)]
              exact mul_lt_mul_of_pos_left h1 hU₀_pos
            refine ⟨x, ⟨hx_lt, by simpa [hc_eq] using hDσ⟩, ?_⟩
            dsimp [g_inv, x]
            have hsp_ne : s + 1 ≠ 0 := by linarith only [hs_pos]
            have hUx : U₀ + U₀ * (s - 1) / (s + 1) = (2 * U₀ * s) / (s + 1) := by
              field_simp [hsp_ne]; ring
            have hDx : U₀ - U₀ * (s - 1) / (s + 1) = (2 * U₀) / (s + 1) := by
              field_simp [hsp_ne]; ring
            rw [hUx, hDx, div_div_div_cancel_right₀ hsp_ne,
              mul_div_cancel_left₀ _ (by positivity), Real.sq_sqrt hσ.le]
          have hzero_ae : ∀ᵐ σ : ℝ ∂volume, ¬ (0 < σ ∧ D (halfPlaneChart U₀ (σ : ℂ)) = 0) := by
            have hm0 : volume {σ : ℝ | 0 < σ ∧ D (halfPlaneChart U₀ (σ : ℂ)) = 0} = 0 :=
              measure_mono_null hg_zero_sub ((hS_fin.image g_inv).measure_zero volume)
            exact ae_iff.mpr (by simpa [not_not] using hm0)
          filter_upwards [hzero_ae] with σ hσ_nz hσ
          have hσ0 : σ ≠ 0 := hσ.ne'
          simp only [F_bdy, hσ0, ↓reduceIte]
          have hc_eq : halfPlaneChart U₀ (σ : ℂ) =
              ((U₀ * (Real.sqrt σ - 1) / (Real.sqrt σ + 1) : ℝ) : ℂ) := by
            unfold halfPlaneChart; rw [halfUpper_posReal hσ]; push_cast; ring
          set xσ : ℝ := U₀ * (Real.sqrt σ - 1) / (Real.sqrt σ + 1)
          have h_xσ_le : |xσ| ≤ U₀ := by
            have hs_nn : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg σ
            have hq_le : |Real.sqrt σ - 1| ≤ Real.sqrt σ + 1 :=
              abs_le.mpr ⟨by linarith only [hs_nn], by linarith only [hs_nn]⟩
            dsimp [xσ]
            rw [abs_div, abs_mul, abs_of_pos hU₀_pos, abs_of_pos (by linarith only [hs_nn] : 0 < Real.sqrt σ + 1)]
            calc U₀ * |Real.sqrt σ - 1| / (Real.sqrt σ + 1)
                ≤ U₀ * (Real.sqrt σ + 1) / (Real.sqrt σ + 1) := by gcongr
              _ = U₀ := by field_simp [show Real.sqrt σ + 1 ≠ 0 by linarith only [hs_nn] ]
          have h_xσ_lt : |xσ| < U₀ := by
            have hs_pos : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
            have hq_lt : |Real.sqrt σ - 1| < Real.sqrt σ + 1 :=
              abs_lt.mpr ⟨by linarith only [hs_pos], by linarith only [hs_pos]⟩
            dsimp [xσ]
            rw [abs_div, abs_mul, abs_of_pos hU₀_pos, abs_of_pos (by linarith only [hs_pos] : 0 < Real.sqrt σ + 1),
              div_lt_iff₀ (by linarith only [hs_pos] : 0 < Real.sqrt σ + 1)]
            exact mul_lt_mul_of_pos_left hq_lt hU₀_pos
          have hF_x_le : ‖F_u (xσ : ℂ)‖ ≤ M_diam := by
            have hlin_bd : ‖1 + (xσ : ℂ) / (U₀ : ℂ)‖ ≤ 2 := by
              calc ‖1 + (xσ : ℂ) / (U₀ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(xσ : ℂ) / (U₀ : ℂ)‖ := norm_add_le _ _
                _ = 1 + |xσ| / U₀ := by
                    rw [norm_one, norm_div, Complex.norm_real, Complex.norm_real,
                      Real.norm_eq_abs, Real.norm_of_nonneg hU₀_pos.le]
                _ ≤ 1 + U₀ / U₀ := by gcongr
                _ = 2 := by rw [div_self hU₀_pos.ne']; norm_num
            have hdiff_bd : ‖truncatedMellinP c' dpT0 g (xσ : ℂ) - virasoroPsiTilde c' g (xσ : ℂ)‖ ≤
                C_real * Real.exp (-(3 * d₀ / 4) * c') := by
              rw [norm_sub_rev]; exact hreal_U₀ xσ h_xσ_le
            have hexp_bd : ‖Complex.exp ((4 / 3 : ℂ) * (xσ : ℂ) * halfUpper (xσ : ℂ))‖ ≤
                Real.exp ((3 * d₀ / 32) * c') :=
              (hF_norm_real_u0 xσ h_xσ_le).trans (Real.exp_le_exp.mpr hU₀_ang)
            dsimp [F_u, M_diam]
            rw [norm_mul, norm_mul]
            calc ‖1 + (xσ : ℂ) / (U₀ : ℂ)‖ *
                    ‖truncatedMellinP c' dpT0 g (xσ : ℂ) - virasoroPsiTilde c' g (xσ : ℂ)‖ *
                    ‖Complex.exp ((4 / 3 : ℂ) * (xσ : ℂ) * halfUpper (xσ : ℂ))‖
                ≤ 2 * (C_real * Real.exp (-(3 * d₀ / 4) * c')) * Real.exp ((3 * d₀ / 32) * c') := by
                  gcongr
              _ = 2 * C_real * (Real.exp (-(3 * d₀ / 4) * c') * Real.exp ((3 * d₀ / 32) * c')) := by
                  ring
              _ = 2 * C_real * Real.exp (-(3 * d₀ / 4 - 3 * d₀ / 32) * c') := by
                  rw [← Real.exp_add]; congr 2; ring
          have hFx_ne : F_u (xσ : ℂ) ≠ 0 := by
            have hD_ne : D (xσ : ℂ) ≠ 0 := fun h0 => hσ_nz ⟨hσ, by simpa [hc_eq] using h0⟩
            have hlin_ne : 1 + (xσ : ℂ) / (U₀ : ℂ) ≠ 0 := by
              intro h0
              have hn : ‖(xσ : ℂ) / (U₀ : ℂ)‖ = 1 := by
                have := eq_neg_of_add_eq_zero_right h0; rw [this, norm_neg, norm_one]
              rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_of_nonneg hU₀_pos.le, div_eq_one_iff_eq hU₀_pos.ne'] at hn
              linarith only [hn, h_xσ_lt]
            dsimp [F_u]
            exact mul_ne_zero (mul_ne_zero hlin_ne hD_ne) (Complex.exp_ne_zero _)
          rw [hc_eq]
          exact Real.log_le_log (norm_pos_iff.mpr hFx_ne) hF_x_le
        have hlog_arc_bd : ∀ σ : ℝ, σ ≤ 0 → Real.log ‖F_bdy σ‖ ≤ Real.log M_PJ := fun σ hσ => by
          by_cases hσ0 : σ = 0
          · subst hσ0
            simp only [F_bdy, ↓reduceIte, norm_zero, Real.log_zero]
            exact Real.log_nonneg hM_PJ_gt_one.le
          · simp only [F_bdy, hσ0, ↓reduceIte]
            have hσ_neg : σ < 0 := lt_of_le_of_ne hσ hσ0
            have hnorm_arc : ‖halfPlaneChart U₀ (σ : ℂ)‖ = U₀ ∧
                0 < (halfPlaneChart U₀ (σ : ℂ)).im := by
              rw [halfPlaneChart, halfUpper_negReal hσ_neg]
              set s := Real.sqrt (-σ)
              have hs_pos : 0 < s := Real.sqrt_pos.mpr (by linarith only [hσ_neg])
              have hdiv_im : ((Complex.I * (s : ℂ) - 1) / (Complex.I * (s : ℂ) + 1)).im =
                  2 * s / (1 + s ^ 2) := by
                rw [Complex.div_im, Complex.normSq_apply]
                simp [sq]; ring
              have hdiv_norm : ‖(Complex.I * (s : ℂ) - 1) / (Complex.I * (s : ℂ) + 1)‖ = 1 := by
                rw [norm_div]
                have hsq1 : ‖Complex.I * (s : ℂ) - 1‖ ^ 2 = 1 + s ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
                have hsq2 : ‖Complex.I * (s : ℂ) + 1‖ ^ 2 = 1 + s ^ 2 := by
                  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
                have heq : ‖Complex.I * (s : ℂ) - 1‖ = ‖Complex.I * (s : ℂ) + 1‖ :=
                  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hsq1.trans hsq2.symm)
                rw [heq, div_self (norm_ne_zero_iff.mpr (by
                  intro h0; rw [h0, norm_zero] at hsq2; have := sq_nonneg s; nlinarith only [hsq2, this]))]
              constructor
              · rw [mul_div_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le,
                  hdiv_norm, mul_one]
              · rw [mul_div_assoc, Complex.im_ofReal_mul, hdiv_im]; positivity
            have hFu_bd : ‖F_u (halfPlaneChart U₀ (σ : ℂ))‖ ≤ M_PJ := by
              have hw_cb' : halfPlaneChart U₀ (σ : ℂ) ∈ closedBall (0 : ℂ) U₀ :=
                mem_closedBall_zero_iff.mpr hnorm_arc.1.le
              have hw_cut' : ¬ ((halfPlaneChart U₀ (σ : ℂ)).im = 0 ∧ (halfPlaneChart U₀ (σ : ℂ)).re ≤ 0) :=
                fun ⟨h0, _⟩ => by have hi := hnorm_arc.2; linarith only [h0, hi]
              have hw_exp_eq : (4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) * halfUpper (halfPlaneChart U₀ (σ : ℂ)) =
                  (4 / 3 : ℂ) * (halfPlaneChart U₀ (σ : ℂ)) ^ (3 / 2 : ℂ) := by
                rw [halfUpper_eq_cpow_half_of_im_pos hnorm_arc.2]
                have hpow3 : halfPlaneChart U₀ (σ : ℂ) * (halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ) =
                    (halfPlaneChart U₀ (σ : ℂ)) ^ (3 / 2 : ℂ) := by
                  have hne : halfPlaneChart U₀ (σ : ℂ) ≠ 0 := fun h0 => by simp [h0] at hnorm_arc
                  conv_lhs => arg 1; rw [← Complex.cpow_one (halfPlaneChart U₀ (σ : ℂ))]
                  rw [← Complex.cpow_add _ _ hne]; congr 1; norm_num
                rw [mul_assoc, hpow3]
              have hexp_air : ‖Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                  halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ * airyEnv (halfPlaneChart U₀ (σ : ℂ)) = 1 := by
                rw [hw_exp_eq, Complex.norm_exp]
                have hre : ((4 / 3 : ℂ) * (halfPlaneChart U₀ (σ : ℂ)) ^ (3 / 2 : ℂ)).re =
                    (4 / 3 : ℝ) * ((halfPlaneChart U₀ (σ : ℂ)) ^ (3 / 2 : ℂ)).re := by
                  rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
                rw [hre]; unfold airyEnv; rw [← Real.exp_add]; simp
              have hP_w := hP_U₀ (halfPlaneChart U₀ (σ : ℂ)) hw_cb' hw_cut'
              have hPsi_w := hPsi_U₀ (halfPlaneChart U₀ (σ : ℂ)) hw_cb' hw_cut'
              have hlin_le2 : ‖1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)‖ ≤ 2 := by
                calc ‖1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)‖
                    ≤ ‖(1 : ℂ)‖ + ‖halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)‖ := norm_add_le _ _
                  _ = 1 + U₀ / U₀ := by
                      rw [norm_one, norm_div, hnorm_arc.1, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le]
                  _ = 2 := by rw [div_self hU₀_pos.ne']; norm_num
              have hlin_exact : ‖1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)‖ =
                  2 * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re / Real.sqrt U₀ := by
                set v := (halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)
                have hv2 : v ^ 2 = halfPlaneChart U₀ (σ : ℂ) := FormalResearch.Special.cpow_half_sq _
                have hv_norm : ‖v‖ = Real.sqrt U₀ := by
                  have hsq : ‖v‖ ^ 2 = U₀ := by
                    calc ‖v‖ ^ 2 = ‖v ^ 2‖ := (norm_pow _ 2).symm
                      _ = ‖halfPlaneChart U₀ (σ : ℂ)‖ := by rw [hv2]
                      _ = U₀ := hnorm_arc.1
                  rw [← Real.sqrt_sq (norm_nonneg v), hsq]
                have hv_conj : v * starRingEnd ℂ v = (U₀ : ℂ) := by
                  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv_norm, Real.sq_sqrt hU₀_pos.le]
                have hrew : 1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ) =
                    (v / (U₀ : ℂ)) * ((2 * v.re : ℝ) : ℂ) := by
                  have hv_sum : v + starRingEnd ℂ v = ((2 * v.re : ℝ) : ℂ) := by
                    apply Complex.ext
                    · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]; ring
                    · simp only [Complex.add_im, Complex.conj_im, Complex.ofReal_im]; ring
                  have hU_ne : (U₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU₀_pos.ne'
                  calc 1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)
                        = (v * starRingEnd ℂ v + v ^ 2) / (U₀ : ℂ) := by
                          rw [hv_conj, hv2, add_div, div_self hU_ne]
                    _ = (v / (U₀ : ℂ)) * (starRingEnd ℂ v + v) := by ring
                    _ = (v / (U₀ : ℂ)) * ((2 * v.re : ℝ) : ℂ) := by rw [add_comm, hv_sum]
                have hv_nn := cpow_half_re_nonneg (halfPlaneChart U₀ (σ : ℂ))
                rw [hrew, norm_mul, norm_div, hv_norm, Complex.norm_real, Real.norm_of_nonneg hU₀_pos.le,
                  Complex.norm_real, Real.norm_of_nonneg (by linarith only [hv_nn])]
                rw [show Real.sqrt U₀ / U₀ * (2 * v.re) = 2 * v.re / Real.sqrt U₀ * (Real.sqrt U₀ ^ 2 / U₀) by
                    field_simp [hU₀_pos.ne'],
                  Real.sq_sqrt hU₀_pos.le, div_self hU₀_pos.ne', mul_one]
              have hv_re_pos : 0 < ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re := by
                by_contra hle
                have hre0 : ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re = 0 :=
                  le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg _)
                have him_w := congrArg Complex.im (FormalResearch.Special.cpow_half_sq (halfPlaneChart U₀ (σ : ℂ)))
                rw [sq, Complex.mul_im, hre0, zero_mul, mul_zero, add_zero] at him_w
                have hi := hnorm_arc.2
                linarith only [him_w, hi]
              have hv_re_le : ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re ≤ Real.sqrt U₀ := by
                have h1 := Complex.re_le_norm ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ))
                have hsq : ‖(halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)‖ ^ 2 = U₀ := by
                  rw [← norm_pow, FormalResearch.Special.cpow_half_sq, hnorm_arc.1]
                have hn : ‖(halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)‖ = Real.sqrt U₀ := by
                  rw [← Real.sqrt_sq (norm_nonneg _), hsq]
                linarith only [h1, hn]
              have hsig_le : Real.exp (virasoroSigma c' * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re) ≤
                  Real.exp (virasoroSigma c' * Real.sqrt U₀) :=
                Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv_re_le (virasoroSigma_nonneg (by linarith only [hc'_10000])))
              have hnorm_half : ‖halfPlaneChart U₀ (σ : ℂ)‖ ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt U₀ := by
                rw [hnorm_arc.1, Real.rpow_neg hU₀_pos.le, ← Real.sqrt_eq_rpow, one_div]
              have hP_t : ‖(1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)) *
                  truncatedMellinP c' dpT0 g (halfPlaneChart U₀ (σ : ℂ)) *
                  Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                    halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ ≤ 2 * C_P * c' ^ (1 / 3 : ℝ) := by
                rw [norm_mul, norm_mul]
                calc _ ≤ 2 * (C_P * c' ^ (1 / 3 : ℝ) * airyEnv (halfPlaneChart U₀ (σ : ℂ))) *
                      ‖Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                        halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ := by gcongr
                  _ = 2 * C_P * c' ^ (1 / 3 : ℝ) * (‖Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                        halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ * airyEnv (halfPlaneChart U₀ (σ : ℂ))) := by ring
                  _ = 2 * C_P * c' ^ (1 / 3 : ℝ) := by rw [hexp_air, mul_one]
              have hPsi_t : ‖(1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)) *
                  virasoroPsiTilde c' g (halfPlaneChart U₀ (σ : ℂ)) *
                  Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                    halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ ≤
                  2 * virasoroInnerEnvC0 / U₀ * Real.exp (virasoroSigma c' * Real.sqrt U₀) := by
                rw [norm_mul, norm_mul, hlin_exact]
                calc _ ≤ (2 * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re / Real.sqrt U₀) *
                      (virasoroInnerEnvC0 * airyEnv (halfPlaneChart U₀ (σ : ℂ)) *
                        Real.exp (virasoroSigma c' * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re) *
                        (1 / Real.sqrt U₀) * (((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re)⁻¹) *
                      ‖Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                        halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ := by
                      gcongr; exact (hPsi_w.trans_eq (by rw [hnorm_half]))
                  _ = (2 * virasoroInnerEnvC0 / (Real.sqrt U₀ ^ 2)) *
                        (((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re *
                          (((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re)⁻¹) *
                        (‖Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                          halfUpper (halfPlaneChart U₀ (σ : ℂ)))‖ * airyEnv (halfPlaneChart U₀ (σ : ℂ))) *
                        Real.exp (virasoroSigma c' * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re) := by ring
                  _ = (2 * virasoroInnerEnvC0 / U₀) *
                        Real.exp (virasoroSigma c' * ((halfPlaneChart U₀ (σ : ℂ)) ^ (1 / 2 : ℂ)).re) := by
                      rw [Real.sq_sqrt hU₀_pos.le, mul_inv_cancel₀ hv_re_pos.ne', hexp_air]; ring
                  _ ≤ _ := mul_le_mul_of_nonneg_left hsig_le (by have := virasoroInnerEnvC0_pos; positivity)
              have hF_split : F_u (halfPlaneChart U₀ (σ : ℂ)) =
                  (1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)) *
                    truncatedMellinP c' dpT0 g (halfPlaneChart U₀ (σ : ℂ)) *
                    Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                      halfUpper (halfPlaneChart U₀ (σ : ℂ))) -
                  (1 + halfPlaneChart U₀ (σ : ℂ) / (U₀ : ℂ)) *
                    virasoroPsiTilde c' g (halfPlaneChart U₀ (σ : ℂ)) *
                    Complex.exp ((4 / 3 : ℂ) * halfPlaneChart U₀ (σ : ℂ) *
                      halfUpper (halfPlaneChart U₀ (σ : ℂ))) := by dsimp [F_u]; ring
              rw [hF_split]
              calc ‖_ - _‖ ≤ _ + _ := norm_sub_le _ _
                _ ≤ _ := add_le_add hP_t hPsi_t
                _ ≤ M_PJ := by
                    have hdef : M_PJ = 2 * virasoroInnerEnvC0 / U₀ * Real.exp (virasoroSigma c' * Real.sqrt U₀) +
                      2 * C_P * c' ^ (1 / 3 : ℝ) + 1 := rfl
                    linarith only [hdef]
            by_cases hFx0 : F_u (halfPlaneChart U₀ (σ : ℂ)) = 0
            · rw [hFx0, norm_zero, Real.log_zero]; exact Real.log_nonneg hM_PJ_gt_one.le
            · exact Real.log_le_log (norm_pos_iff.mpr hFx0) hFu_bd
        have hstep_piecewise : ∀ᵐ σ : ℝ ∂volume,
            Real.log ‖F_bdy σ‖ * poissonKernel z₀.re z₀.im σ ≤
              (if 0 < σ then Real.log M_diam else Real.log M_PJ) * poissonKernel z₀.re z₀.im σ := by
          filter_upwards [hlog_diam_bd] with σ hdiam
          have hpk_nn : 0 ≤ poissonKernel z₀.re z₀.im σ := by unfold poissonKernel; positivity
          refine mul_le_mul_of_nonneg_right ?_ hpk_nn
          split_ifs with hpos
          · exact hdiam hpos
          · exact hlog_arc_bd σ (not_lt.mp hpos)
        let maj_fn : ℝ → ℝ := fun σ =>
          (if 0 < σ then Real.log M_diam else Real.log M_PJ) * poissonKernel z₀.re z₀.im σ
        have hmaj_int : Integrable maj_fn := by
          have hp_Ioi : IntegrableOn (fun σ => Real.log M_diam * poissonKernel z₀.re z₀.im σ) (Ioi 0) :=
            (hpk.1.const_mul _).integrableOn
          have hp_Iic : IntegrableOn (fun σ => Real.log M_PJ * poissonKernel z₀.re z₀.im σ) (Iic 0) :=
            (hpk.1.const_mul _).integrableOn
          rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
          refine (hp_Iic.congr_fun (fun σ hσ => ?_) measurableSet_Iic).union
            (hp_Ioi.congr_fun (fun σ hσ => ?_) measurableSet_Ioi)
          · simp [maj_fn, not_lt.mpr (mem_Iic.mp hσ)]
          · simp [maj_fn, mem_Ioi.mp hσ]
        have hint_le_maj := MeasureTheory.integral_mono_ae hPJ.1 hmaj_int hstep_piecewise
        have hmaj_eq : ∫ σ : ℝ, maj_fn σ =
            Real.log M_diam * (∫ σ in Ioi (0 : ℝ), poissonKernel z₀.re z₀.im σ) +
            Real.log M_PJ * (∫ σ in Iic (0 : ℝ), poissonKernel z₀.re z₀.im σ) := by
          have hsplit := (MeasureTheory.integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hmaj_int).symm
          rw [compl_Iic] at hsplit
          rw [hsplit]
          have h1 : ∫ σ in Iic (0 : ℝ), maj_fn σ =
              Real.log M_PJ * ∫ σ in Iic (0 : ℝ), poissonKernel z₀.re z₀.im σ := by
            rw [← integral_const_mul]
            refine setIntegral_congr_fun measurableSet_Iic fun σ hσ => ?_
            simp [maj_fn, not_lt.mpr (mem_Iic.mp hσ)]
          have h2 : ∫ σ in Ioi (0 : ℝ), maj_fn σ =
              Real.log M_diam * ∫ σ in Ioi (0 : ℝ), poissonKernel z₀.re z₀.im σ := by
            rw [← integral_const_mul]
            refine setIntegral_congr_fun measurableSet_Ioi fun σ hσ => ?_
            simp [maj_fn, mem_Ioi.mp hσ]
          rw [h1, h2]; ring
        have hIic_le1 : ∫ σ in Iic (0 : ℝ), poissonKernel z₀.re z₀.im σ ≤ 1 := by
          have hadd := (MeasureTheory.integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hpk.1).symm
          rw [compl_Iic] at hadd
          have h_nn : 0 ≤ ∫ σ in Ioi (0 : ℝ), poissonKernel z₀.re z₀.im σ :=
            MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun _ _ => by
              unfold poissonKernel; positivity
          have htot := hpk.2.1
          linarith only [hadd, h_nn, htot]
        have hlog_diam_neg : Real.log M_diam ≤ 0 := Real.log_nonpos hM_diam_pos.le hM_diam_le_one
        have hlog_PJ_nn : 0 ≤ Real.log M_PJ := Real.log_nonneg hM_PJ_gt_one.le
        have hsum_maj_ub :
            Real.log M_diam * (∫ σ in Ioi (0 : ℝ), poissonKernel z₀.re z₀.im σ) +
            Real.log M_PJ * (∫ σ in Iic (0 : ℝ), poissonKernel z₀.re z₀.im σ) ≤
            (1 / 4 : ℝ) * Real.log M_diam + Real.log M_PJ := by
          have hterm1 : Real.log M_diam * (∫ σ in Ioi (0 : ℝ), poissonKernel z₀.re z₀.im σ) ≤
              Real.log M_diam * (1 / 4 : ℝ) :=
            mul_le_mul_of_nonpos_left hpk.2.2 hlog_diam_neg
          have hterm2 : Real.log M_PJ * (∫ σ in Iic (0 : ℝ), poissonKernel z₀.re z₀.im σ) ≤
              Real.log M_PJ * 1 :=
            mul_le_mul_of_nonneg_left hIic_le1 hlog_PJ_nn
          linarith only [hterm1, hterm2]
        have hM_PJ_ub : M_PJ ≤ C_arc0 * c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c') := by
          have hc_ge1 : 1 ≤ c' := by linarith only [hc'_10000]
          have hc13_ge1 : 1 ≤ c' ^ (1 / 3 : ℝ) := Real.one_le_rpow hc_ge1 (by norm_num)
          have hsig_prod : virasoroSigma c' * Real.sqrt U₀ = A_sig * Real.log c' := by
            have hsqrt_U₀ : Real.sqrt U₀ = Real.sqrt (2 * c₀_D) * c' ^ (1 / 3 : ℝ) := by
              dsimp [U₀]
              rw [Real.sqrt_mul (by positivity)]
              congr 1
              rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc'_pos.le]; norm_num
            have hc_cancel : c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ) = 1 := by
              rw [← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero]
            unfold virasoroSigma
            rw [hsqrt_U₀]
            calc virasoroEnvC1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c' *
                  (Real.sqrt (2 * c₀_D) * c' ^ (1 / 3 : ℝ))
                = (virasoroEnvC1 * Real.sqrt (2 * c₀_D)) *
                    (c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ)) * Real.log c' := by ring
              _ = A_sig * 1 * Real.log c' := by rw [hc_cancel]
              _ = A_sig * Real.log c' := by ring
          have hexp_ge1 : 1 ≤ Real.exp (A_sig * Real.log c') :=
            Real.one_le_exp (mul_nonneg hA_sig_nn (Real.log_nonneg hc_ge1))
          have h2U0_le : 2 * virasoroInnerEnvC0 / U₀ ≤ 2 * virasoroInnerEnvC0 / (2 * c₀_D) := by
            have hc23_ge1 : 1 ≤ c' ^ (2 / 3 : ℝ) := Real.one_le_rpow hc_ge1 (by norm_num)
            have hU0_ge : 2 * c₀_D ≤ U₀ := by
              dsimp [U₀]; exact le_mul_of_one_le_right (by positivity) hc23_ge1
            have := virasoroInnerEnvC0_pos
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hU0_ge
          have h1_le : (1 : ℝ) ≤ c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c') :=
            one_le_mul_of_one_le_of_one_le hc13_ge1 hexp_ge1
          have h2_le : 2 * virasoroInnerEnvC0 / U₀ * Real.exp (virasoroSigma c' * Real.sqrt U₀) ≤
              (2 * virasoroInnerEnvC0 / (2 * c₀_D)) * (c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) := by
            rw [hsig_prod]
            calc 2 * virasoroInnerEnvC0 / U₀ * Real.exp (A_sig * Real.log c')
                ≤ (2 * virasoroInnerEnvC0 / (2 * c₀_D)) * Real.exp (A_sig * Real.log c') := by gcongr
              _ ≤ (2 * virasoroInnerEnvC0 / (2 * c₀_D)) *
                    (c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) := by
                  refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le hc13_ge1)
                    (by have := virasoroInnerEnvC0_pos; positivity)
          have h3_le : 2 * C_P * c' ^ (1 / 3 : ℝ) ≤
              2 * C_P * (c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Real.rpow_nonneg hc'_pos.le _) hexp_ge1)
              (by positivity)
          have hM_def : M_PJ = 2 * virasoroInnerEnvC0 / U₀ * Real.exp (virasoroSigma c' * Real.sqrt U₀) +
              2 * C_P * c' ^ (1 / 3 : ℝ) + 1 := rfl
          have hC_def : C_arc0 = 2 * virasoroInnerEnvC0 / (2 * c₀_D) + 2 * C_P + 1 := rfl
          have hrhs_eq : C_arc0 * c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c') =
              (2 * virasoroInnerEnvC0 / (2 * c₀_D)) * (c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) +
              2 * C_P * (c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) +
              c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c') := by
            rw [hC_def]; ring
          linarith only [hM_def, hrhs_eq, h1_le, h2_le, h3_le]
        have hlog_final : (1 / 4 : ℝ) * Real.log M_diam + Real.log M_PJ ≤ -d_D * c' := by
          have hlog_diam_eq : Real.log M_diam =
              Real.log (2 * C_real) - (21 * d₀ / 32) * c' := by
            dsimp [M_diam]
            rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
            ring
          have hlog_PJ_le : Real.log M_PJ ≤
              Real.log C_arc0 + (1 / 3 + A_sig) * Real.log c' := by
            have hMPJ_pos : 0 < M_PJ := lt_trans zero_lt_one hM_PJ_gt_one
            have hC_pos : 0 < C_arc0 := lt_trans zero_lt_one hC_arc0_gt1
            have h1 : Real.log M_PJ ≤ Real.log (C_arc0 * c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) :=
              Real.log_le_log hMPJ_pos hM_PJ_ub
            have h2 : Real.log (C_arc0 * c' ^ (1 / 3 : ℝ) * Real.exp (A_sig * Real.log c')) =
                Real.log C_arc0 + (1 / 3 + A_sig) * Real.log c' := by
              rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
                Real.log_mul hC_pos.ne' (Real.rpow_pos_of_pos hc'_pos _).ne',
                Real.log_rpow hc'_pos, Real.log_exp]
              ring
            linarith only [h1, h2]
          have hlog_sqrt : Real.log c' ≤ 2 * Real.sqrt c' := by
            have h1 : Real.log (Real.sqrt c') ≤ Real.sqrt c' - 1 :=
              Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hc'_pos)
            have h2 : Real.log c' = 2 * Real.log (Real.sqrt c') := by
              rw [Real.sqrt_eq_rpow, Real.log_rpow hc'_pos]; ring
            linarith only [h1, h2]
          have hc_sqrt_bd : max 0 C_const_log + B_log * Real.sqrt c' ≤ α * c' := by
            have hc_sq : ((max 0 C_const_log + B_log + 1) / α) ^ 2 ≤ c' := by
              have hc_def : c_thr_exp = ((max 0 C_const_log + B_log + 1) / α) ^ 2 + 1 := rfl
              linarith only [hc'_exp, hc_def]
            have hrt : (max 0 C_const_log + B_log + 1) / α ≤ Real.sqrt c' :=
              Real.le_sqrt_of_sq_le hc_sq
            have hrt_mul : max 0 C_const_log + B_log + 1 ≤ α * Real.sqrt c' :=
              ((div_le_iff₀ hα_pos).mp hrt).trans_eq (mul_comm _ _)
            have hge1 : 1 ≤ Real.sqrt c' := by
              rw [Real.one_le_sqrt]; linarith only [hc'_10000]
            calc max 0 C_const_log + B_log * Real.sqrt c'
                ≤ max 0 C_const_log * Real.sqrt c' + B_log * Real.sqrt c' := by
                  gcongr; exact le_mul_of_one_le_right (le_max_left _ _) hge1
              _ = (max 0 C_const_log + B_log) * Real.sqrt c' := by ring
              _ ≤ (α * Real.sqrt c') * Real.sqrt c' :=
                  mul_le_mul_of_nonneg_right (by linarith only [hrt_mul]) (Real.sqrt_nonneg _)
              _ = α * (Real.sqrt c' ^ 2) := by ring
              _ = α * c' := by rw [Real.sq_sqrt hc'_pos.le]
          have hA13 : (1 / 3 + A_sig) * Real.log c' ≤ B_log * Real.sqrt c' := by
            calc (1 / 3 + A_sig) * Real.log c' ≤ (1 / 3 + A_sig) * (2 * Real.sqrt c') := by gcongr
              _ = B_log * Real.sqrt c' := by dsimp [B_log]; ring
          have hC_comb : (1 / 4 : ℝ) * Real.log (2 * C_real) + Real.log C_arc0 ≤ max 0 C_const_log := by
            have hC_def : C_const_log = Real.log C_arc0 + (1 / 4 : ℝ) * Real.log (2 * C_real) := rfl
            exact le_max_of_le_right (by linarith only [hC_def])
          calc (1 / 4 : ℝ) * Real.log M_diam + Real.log M_PJ
              ≤ (1 / 4 : ℝ) * (Real.log (2 * C_real) - (21 * d₀ / 32) * c') +
                  (Real.log C_arc0 + (1 / 3 + A_sig) * Real.log c') := by
                rw [hlog_diam_eq]; linarith only [hlog_PJ_le]
            _ ≤ (max 0 C_const_log + B_log * Real.sqrt c') - (21 * d₀ / 128) * c' := by
                linarith only [hA13, hC_comb]
            _ ≤ α * c' - (21 * d₀ / 128) * c' := by linarith only [hc_sqrt_bd]
            _ = -d_D * c' := by dsimp [α, d_D]; ring
        have hFz_log : Real.log ‖F_z z₀‖ ≤ -d_D * c' := by
          have h1 : Real.log ‖F_z z₀‖ ≤ ∫ σ : ℝ, Real.log ‖F_bdy σ‖ * poissonKernel z₀.re z₀.im σ :=
            hPJ.2
          linarith only [h1, hint_le_maj, hmaj_eq, hsum_maj_ub, hlog_final]
        have hFu_exp_bd : ‖F_u w‖ ≤ Real.exp (-d_D * c') := by
          have hFz_pos : 0 < ‖F_z z₀‖ := norm_pos_iff.mpr hFz₀_ne
          have h1 := Real.exp_le_exp.mpr hFz_log
          rw [Real.exp_log hFz_pos] at h1
          simpa [F_z, hchart_z₀] using h1
        have hlin_lb : (1 / 2 : ℝ) ≤ ‖1 + w / (U₀ : ℂ)‖ := by
          have hw_U : ‖w / (U₀ : ℂ)‖ ≤ 1 / 2 := hζ_norm
          have htri := norm_sub_norm_le (1 : ℂ) (-(w / (U₀ : ℂ)))
          rw [norm_one, norm_neg, sub_neg_eq_add] at htri
          linarith only [hw_U, htri]
        have hw_exp_eq : (4 / 3 : ℂ) * w * halfUpper w = (4 / 3 : ℂ) * w ^ (3 / 2 : ℂ) := by
          rw [halfUpper_eq_cpow_half_of_im_pos him_pos]
          have hpow3 : w * w ^ (1 / 2 : ℂ) = w ^ (3 / 2 : ℂ) := by
            have hw_ne : w ≠ 0 := fun h0 => by simp [h0] at him_pos
            conv_lhs => arg 1; rw [← Complex.cpow_one w]
            rw [← Complex.cpow_add _ _ hw_ne]; congr 1; norm_num
          rw [mul_assoc, hpow3]
        have hexp_air : ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ * airyEnv w = 1 := by
          rw [hw_exp_eq, Complex.norm_exp]
          have hre : ((4 / 3 : ℂ) * w ^ (3 / 2 : ℂ)).re = (4 / 3 : ℝ) * (w ^ (3 / 2 : ℂ)).re := by
            rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
          rw [hre]; unfold airyEnv; rw [← Real.exp_add]; simp
        have hprod_split : ‖1 + w / (U₀ : ℂ)‖ *
            ‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖ *
            ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ = ‖F_u w‖ := by
          dsimp [F_u]; rw [norm_mul, norm_mul]
        have h_half_mul : (1 / 2 : ℝ) * (‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖ *
            ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖) ≤ Real.exp (-d_D * c') := by
          calc (1 / 2 : ℝ) * (‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖ *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖)
              ≤ ‖1 + w / (U₀ : ℂ)‖ * (‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖ *
                  ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖) := by gcongr
            _ = ‖F_u w‖ := by rw [← mul_assoc]; exact hprod_split
            _ ≤ Real.exp (-d_D * c') := hFu_exp_bd
        have hmul2 : ‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖ *
            ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖ ≤ 2 * Real.exp (-d_D * c') := by
          linarith only [h_half_mul]
        have h2_le_CD : (2 : ℝ) ≤ C_D := hC_D_eq ▸ le_max_right _ _
        calc ‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖
            = (‖truncatedMellinP c' dpT0 g w - virasoroPsiTilde c' g w‖ *
                ‖Complex.exp ((4 / 3 : ℂ) * w * halfUpper w)‖) * airyEnv w := by
              rw [mul_assoc, hexp_air, mul_one]
          _ ≤ (2 * Real.exp (-d_D * c')) * airyEnv w := by
              gcongr; exact (airyEnv_pos w).le
          _ ≤ C_D * Real.exp (-d_D * c') * airyEnv w := by
              have := airyEnv_pos w; gcongr
  rcases le_or_gt 0 u.im with him_nn | him_neg
  · exact hDp_upper u him_nn hu
  · have hu_c : starRingEnd ℂ u ∈ closedBall (0 : ℂ) (c₀_D * c' ^ (2 / 3 : ℝ)) := by
      simpa [mem_closedBall_zero_iff, Complex.norm_conj] using hu
    have hu_rad : u ∈ ball (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ)) := by
      have hin_pos := innerChartRadius_pos
      have h1 : c₀_D * c' ^ (2 / 3 : ℝ) < innerChartRadius * c' ^ (2 / 3 : ℝ) :=
        mul_lt_mul_of_pos_right (hc₀_D_le4.trans_lt (by linarith only [hin_pos]))
          (Real.rpow_pos_of_pos hc'_pos _)
      exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hu).trans_lt h1)
    have hbd_c := hDp_upper (starRingEnd ℂ u) (by simp; linarith only [him_neg]) hu_c
    rw [truncatedMellinP_conj hc'_1000 dpT0 hg hu_rad, virasoroPsiTilde_inner_conj hc'_1000 hg hu_rad,
      ← map_sub, Complex.norm_conj, airyEnv_conj] at hbd_c
    exact hbd_c

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.Contour.lemma_Dp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Dp

end FormalResearch.ModularBootstrap.Contour


