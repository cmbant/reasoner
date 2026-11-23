module

public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWZ
public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaS4WBridge
public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQScaleBridge

/-!
# Bridge: Lemma D' and Lemma Z at weight `w` versus the Virasoro versions

At `prob = virasoroProblem` (`w = 1`) the weight-`w` objects are the Virasoro ones:

* `truncatedMellinPW_virasoroProblem`: `truncatedMellinPW virasoroProblem = truncatedMellinP`;
* `lemma_Dp_of_W`: the Virasoro statement of Lemma D' (`vlo:Dp`) from `lemma_Dp_W`;
* `lemma_Z_of_W`: the Virasoro statement of Lemma Z (`vlo:Z`) from `lemma_Z_W`, with scale cap `zScaleCapW D`;
* `lemma_Z_W_band`: Lemma Z at weight `w` on the annulus `R ∈ [b² c'^{2/3}, 2 b² c'^{2/3} - 1]` whenever
  `2 b² ≤ zScaleCapW D` (the form consumed by the band-feedback bridge), and its non-vacuity
  `zScaleCapW_band_nonvacuous`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special
open FormalResearch.ModularBootstrap.Chart
open Crossing WeightAxioms ConcreteBootstrap FixedWeightTip Contour StripMultiplier

lemma truncatedMellinPW_virasoroProblem (c' T₀ : ℝ) (g : ℝ → ℝ) (u : ℂ) :
    truncatedMellinPW virasoroProblem c' T₀ g u = truncatedMellinP c' T₀ g u := by
  unfold truncatedMellinPW truncatedMellinP
  simp only [cardyVC_virasoro_eq, show virasoroProblem.w = 1 from rfl,
    mellinDensityIntegrandW_one]

/-- The Virasoro Lemma D' (`Contour.lemma_Dp`) from `lemma_Dp_W`, for any
`D : UniformPropositionPData virasoroProblem`. -/
theorem lemma_Dp_of_W (D : UniformPropositionPData virasoroProblem) :
    ∃ c_D C_D d_D c₀_D : ℝ,
      10000 ≤ c_D ∧ 0 < C_D ∧ 0 < d_D ∧ 0 < c₀_D ∧ c₀_D ≤ innerChartRadius / 4 ∧
        ∀ {c' : ℝ}, c_D ≤ c' → ∀ {g : ℝ → ℝ},
          TestClass virasoroProblem (c' / 12) g →
          0 < virasoroProblem.cardyNorm (c' / 12) g →
          ∀ {u : ℂ}, u ∈ closedBall (0 : ℂ) (c₀_D * c' ^ (2 / 3 : ℝ)) →
            ‖truncatedMellinP c' dpT0 g u - virasoroPsiTilde c' g u‖ ≤
              C_D * Real.exp (-d_D * c') * airyEnv u := by
  obtain ⟨c_D, C_D, d_D, c₀_D, hc_D, hC_D, hd_D, hc₀_D, hle4, _, h⟩ := lemma_Dp_W D
  refine ⟨c_D, C_D, d_D, c₀_D, (dpThr_ge_10000 virasoroProblem).trans hc_D, hC_D, hd_D, hc₀_D,
    hle4, fun {c'} hc' {g} hg hM {u} hu => ?_⟩
  have hc'0 : 0 ≤ c' := by
    linarith only [(dpThr_ge_10000 virasoroProblem).trans (hc_D.trans hc')]
  have := h hc' hg hM hu
  rwa [truncatedMellinPW_virasoroProblem, psiTilde_virasoroProblem hc'0] at this

/-- The Virasoro Lemma Z (`Contour.lemma_Z`) from `lemma_Z_W`, with the scale cap `zScaleCapW D`. -/
theorem lemma_Z_of_W (D : UniformPropositionPData virasoroProblem) {b_lo b_hi : ℝ}
    (hb_lo : 0 < b_lo) (hb_le : b_lo ≤ b_hi) (hb_cap : b_hi ^ 2 ≤ zScaleCapW D) :
    ∃ c_Z C_B : ℝ, 10000 ≤ c_Z ∧ 1 ≤ C_B ∧
      ∀ {c' R Λ : ℝ}, c_Z ≤ c' → 1 ≤ Λ →
        b_lo ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R →
        R + 1 ≤ b_hi ^ 2 * c' ^ (2 / 3 : ℝ) →
        ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
          0 < virasoroProblem.cardyNorm (c' / 12) g →
          (∀ ζ ∈ stripClosed,
            kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R / 3 ≤ ‖ζ‖ →
            ‖ζ‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R) →
            c' ^ (-(1 / 12 : ℝ)) * ‖ζ‖ ≤ ζ.re →
            ‖tildeWV c' g ζ‖ ≤
              virasoroProblem.cardyNorm (c' / 12) g *
                (Λ * c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re)) →
          YVEnvBound (virasoroPsiTilde c' g) c' R (C_B * Λ) := by
  obtain ⟨c_Z, C_B, hc_Z, hC_B, h⟩ := lemma_Z_W D hb_lo hb_le hb_cap
  refine ⟨c_Z, C_B, (dpThr_ge_10000 virasoroProblem).trans hc_Z, hC_B,
    fun {c' R Λ} hc' hΛ hR_lo hR_hi {g} hg hM hsec => ?_⟩
  have hc'0 : 0 ≤ c' := by
    linarith only [(dpThr_ge_10000 virasoroProblem).trans (hc_Z.trans hc')]
  have hfun : psiTilde virasoroProblem c' g = virasoroPsiTilde c' g := by
    funext u
    exact psiTilde_virasoroProblem hc'0 g u
  rw [← hfun]
  refine h hc' hΛ hR_lo hR_hi hg hM ?_
  intro ζ hζ h1 h2 h3
  have := hsec ζ hζ h1 h2 h3
  rwa [← tildeWW_one_eq c' g ζ] at this

/-- Lemma Z at weight `w` on the annulus `R ∈ [b² c'^{2/3}, 2 b² c'^{2/3} - 1]`, for every scale `b > 0`
with `2 b² ≤ zScaleCapW D`. -/
theorem lemma_Z_W_band {prob : FixedWeightProblem} (D : UniformPropositionPData prob) {b : ℝ}
    (hb : 0 < b) (hScale : 2 * b ^ 2 ≤ zScaleCapW D) :
    ∃ c_Z C_B : ℝ, dpThr prob ≤ c_Z ∧ 1 ≤ C_B ∧
      ∀ {c' R Λ : ℝ}, c_Z ≤ c' → 1 ≤ Λ →
        b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R →
        R + 1 ≤ 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) →
        ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
          0 < prob.cardyNorm (c' / 12) g →
          (∀ ζ ∈ stripClosed,
            kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R / 3 ≤ ‖ζ‖ →
            ‖ζ‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * Real.sqrt R) →
            c' ^ (-(1 / 12 : ℝ)) * ‖ζ‖ ≤ ζ.re →
            ‖tildeWW prob.w c' g ζ‖ ≤
              prob.cardyNorm (c' / 12) g * (Λ * c' ^ (-(5 / 6 : ℝ)) * ‖ζ‖ / ζ.re)) →
          YVEnvBound (psiTilde prob c' g) c' R (C_B * Λ) := by
  have hb_sqrt2 : b ≤ Real.sqrt 2 * b :=
    le_mul_of_one_le_left hb.le (by rw [Real.one_le_sqrt]; norm_num)
  have hb_hi_sq : (Real.sqrt 2 * b) ^ 2 = 2 * b ^ 2 := by
    rw [mul_pow, Real.sq_sqrt zero_le_two]
  obtain ⟨c_Z, C_B, hc_Z, hC_B, h⟩ := lemma_Z_W D hb hb_sqrt2 (hb_hi_sq.le.trans hScale)
  refine ⟨c_Z, C_B, hc_Z, hC_B, fun {c' R Λ} hc' hΛ hR_lo hR_hi {g} hg hM hsec => ?_⟩
  refine h hc' hΛ hR_lo ?_ hg hM hsec
  rw [hb_hi_sq]
  linarith only [hR_hi]

/-- Non-vacuity of the scale hypothesis of `lemma_Z_W_band`: some `b > 0` has `2 b² ≤ zScaleCapW D`. -/
theorem zScaleCapW_band_nonvacuous {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ b : ℝ, 0 < b ∧ 2 * b ^ 2 ≤ zScaleCapW D := by
  have hpos := zScaleCapW_pos D
  refine ⟨Real.sqrt (zScaleCapW D / 4), Real.sqrt_pos.mpr (div_pos hpos (by norm_num)), ?_⟩
  rw [Real.sq_sqrt (div_nonneg hpos.le (by norm_num))]
  linarith only [hpos]

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.truncatedMellinPW_virasoroProblem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms truncatedMellinPW_virasoroProblem

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_Dp_of_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Dp_of_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_Z_of_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Z_of_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_Z_W_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Z_W_band

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.zScaleCapW_band_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zScaleCapW_band_nonvacuous

end FormalResearch.ModularBootstrap.FixedWeightBand
