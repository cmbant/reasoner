module

public import FormalResearch.ModularBootstrap.FixedWeightBand.EdgeKernelW
public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaS4WBridge
public import FormalResearch.ModularBootstrap.StripMultiplier.EdgeKernel

/-!
# Bridge: Lemmas J4.1 and J4.2 at Weight `w` versus the Spinless Virasoro Versions

* `edgeKernelKW_one_eq`, `edgeA1W_one_eq`, `edgeA2W_one_eq`, `edgeHVW_one_eq`: at `virasoroProblem`
  (`w = 1`) the weight-`w` kernel, amplitudes and damped multiplier are the Virasoro
  `StripMultiplier.edgeKernelK`, `edgeA1`, `edgeA2`, `edgeHV` (the `ω`-factor `(2π/(3ω))^{(w-1)/2}` and
  `x^{w-1}` are `1`).
* `lemma_J4_1_of_W`, `lemma_J4_2_of_W`: the Virasoro `StripMultiplier.lemma_J4_1` and `lemma_J4_2`
  (`virasoroProblem`, `c₀ ≥ 10000`, `|A₁'| ≤ C/(c'(1+|τ|)³)`) are the `w = 1` instances of
  `lemma_J4_1_W`, `lemma_J4_2_W` (sharp form of the derivative bound: `edgeA1W_bounds`).
* `lemma_J4_1_W_thermalDiff`: non-vacuity, the hypotheses of `lemma_J4_1_W` are met by every thermal
  difference `Ξ_β` at every weight and every `Q`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing Chart StripBand
open FormalResearch.StripPoisson

theorem edgeKernelKW_one_eq (c' τ t : ℝ) :
    edgeKernelKW virasoroProblem c' τ t = StripMultiplier.edgeKernelK c' τ t := by
  unfold edgeKernelKW StripMultiplier.edgeKernelK
  simp

theorem edgeA1W_one_eq (c' τ : ℝ) :
    edgeA1W 1 c' τ = StripMultiplier.edgeA1 c' τ := by
  unfold edgeA1W edgeA1SW StripMultiplier.edgeA1 StripMultiplier.wFactor
  rw [stirlingSW_one]
  simp

theorem edgeA2W_one_eq (c' t : ℝ) :
    edgeA2W virasoroProblem c' t = StripMultiplier.edgeA2 c' t := by
  unfold edgeA2W StripMultiplier.edgeA2
  simp

theorem edgeHVW_one_eq (c' : ℝ) (g : ℝ → ℝ) (ζ : ℂ) :
    edgeHVW 1 c' g ζ = StripMultiplier.edgeHV c' g ζ := by
  unfold edgeHVW StripMultiplier.edgeHV
  rw [tildeWW_one_eq]

/-- The Virasoro Lemma J4.1 (`StripMultiplier.lemma_J4_1`) is the `w = 1` instance of
`lemma_J4_1_W`. -/
theorem lemma_J4_1_of_W :
    ∃ C c₀ : ℝ, 0 < C ∧ 10000 ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass virasoroProblem (c' / 12) g →
        (∀ τ : ℝ, StripMultiplier.tildeWV c' g (Complex.I * (τ : ℂ)) =
          ∫ t in Ioi (0 : ℝ),
            StripMultiplier.edgeKernelK c' τ t *
              ((g t * virasoroProblem.cardyV (c' / 12) t : ℝ) : ℂ)) ∧
        (∀ τ : ℝ, StripMultiplier.edgeHV c' g ((τ : ℂ) * Complex.I) =
          tebAmp0 c' τ * StripMultiplier.tildeWV c' g ((τ : ℂ) * Complex.I)) ∧
        (∀ {ζ₀ : ℂ}, 0 < ζ₀.re → ζ₀.re < 1 →
          StripMultiplier.edgeHV c' g ζ₀ =
            ∫ τ : ℝ, (stripPoissonQ ζ₀.re ζ₀.im (-1) τ : ℂ) *
              StripMultiplier.edgeHV c' g ((τ : ℂ) * Complex.I)) ∧
        (∀ {ζ₀ : ℂ}, 0 < ζ₀.re → ζ₀.re ≤ 0.04 →
          (∫ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im (-1) τ| ≤ 1) ∧
          (∀ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im (-1) τ| +
            (eVariationOn (stripPoissonQ ζ₀.re ζ₀.im (-1)) univ).toReal ≤ 2 / ζ₀.re)) := by
  obtain ⟨c₀, hc₀, h⟩ := lemma_J4_1_W virasoroProblem
  refine ⟨1, max c₀ 10000, one_pos, le_max_right _ _, fun {c'} hc' {g} hg => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h ((le_max_left _ _).trans hc') hg
  have hK : edgeKernelKW virasoroProblem c' = StripMultiplier.edgeKernelK c' := by
    funext τ t; exact edgeKernelKW_one_eq c' τ t
  have hW : tildeWW virasoroProblem.w c' g = StripMultiplier.tildeWV c' g := by
    funext ζ; exact tildeWW_one_eq c' g ζ
  have hH : edgeHVW virasoroProblem.w c' g = StripMultiplier.edgeHV c' g := by
    funext ζ; exact edgeHVW_one_eq c' g ζ
  rw [hK, hW] at h1
  rw [hH, hW] at h2
  rw [hH] at h3
  exact ⟨h1, h2, h3, h4⟩

/-- The Virasoro Lemma J4.2 (`StripMultiplier.lemma_J4_2`) is the `w = 1` instance of
`lemma_J4_2_W` (with the sharp weight-one bound `|A₁'| ≤ C/(c'(1+|τ|)³)` from `edgeA1W_bounds`). -/
theorem lemma_J4_2_of_W :
    ∃ C_A1 C_A1' C_A2 C_sub κ_sub c₀ : ℝ,
      0 < C_A1 ∧ 0 < C_A1' ∧ 0 < C_A2 ∧ 0 < C_sub ∧ 0 < κ_sub ∧ 10000 ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' →
        (∀ τ : ℝ, ‖StripMultiplier.edgeA1 c' τ‖ ≤ C_A1 ∧
          ∃ d : ℂ, HasDerivAt (StripMultiplier.edgeA1 c') d τ ∧
            ‖d‖ ≤ C_A1' / (c' * (1 + |τ|) ^ 3)) ∧
        (∀ {t : ℝ}, 0 < t → xiStar / 2 ≤ √(3 * t / c') →
          0 ≤ StripMultiplier.edgeA2 c' t ∧ StripMultiplier.edgeA2 c' t ≤ C_A2) ∧
        (∀ {t : ℝ}, 0 < t → √(3 * t / c') ≤ xiStar / 2 →
          ∀ τ : ℝ, ‖StripMultiplier.edgeKernelK c' τ t‖ ≤ C_sub * Real.exp (-κ_sub * c')) ∧
        (∀ {t : ℝ}, 0 < t → ∀ τ : ℝ,
          StripMultiplier.edgeKernelK c' τ t = StripMultiplier.edgeA1 c' τ *
              (StripMultiplier.edgeA2 c' t : ℂ) *
            Complex.exp ((c' : ℂ) * ((StripMultiplier.edgeRV c' τ t : ℂ) +
              Complex.I * (StripMultiplier.edgeTheta c' τ t : ℂ))) ∧
          StripMultiplier.edgeRV c' τ t ≤ 0 ∧
          StripMultiplier.edgeRV c' (-τ) t = StripMultiplier.edgeRV c' τ t ∧
          StripMultiplier.edgeTheta c' (-τ) t = -StripMultiplier.edgeTheta c' τ t ∧
          HasDerivAt (fun s => StripMultiplier.edgeTheta c' s t)
            (2 * edgeNuDeriv τ * Real.log (edgeX0 τ / √(3 * t / c'))) τ) ∧
        (∀ {t : ℝ}, 0 < t →
          MonotoneOn (fun τ => StripMultiplier.edgeRV c' τ t)
            (Ioi 0 ∩ Iic (StripMultiplier.edgeTau0 c' t)) ∧
          AntitoneOn (fun τ => StripMultiplier.edgeRV c' τ t)
            (Ioi 0 ∩ Ici (StripMultiplier.edgeTau0 c' t))) := by
  obtain ⟨C_A1, C_A1', C_A2, C_sub, κ_sub, c₀, hC_A1, hC_A1', hC_A2, hC_sub, hκ_sub, hc₀, h⟩ :=
    lemma_J4_2_W virasoroProblem
  obtain ⟨C_A1b, C_S, C_F, hC_A1b, hC_S, hC_F, hb⟩ := edgeA1W_bounds (w := 1) le_rfl
  have hK : edgeKernelKW virasoroProblem = StripMultiplier.edgeKernelK := by
    funext c' τ t; exact edgeKernelKW_one_eq c' τ t
  have hA1 : edgeA1W virasoroProblem.w = StripMultiplier.edgeA1 := by
    funext c' τ; exact edgeA1W_one_eq c' τ
  have hA2 : edgeA2W virasoroProblem = StripMultiplier.edgeA2 := by
    funext c' t; exact edgeA2W_one_eq c' t
  refine ⟨C_A1b, C_S, C_A2, C_sub, κ_sub, max 10000 (max c₀ (1 / muStar)), hC_A1b, hC_S, hC_A2,
    hC_sub, hκ_sub, le_max_left _ _, fun {c'} hc' => ?_⟩
  have hc₀' : c₀ ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  have hmu : 1 / muStar ≤ c' := (le_max_right _ _).trans ((le_max_right _ _).trans hc')
  obtain ⟨-, h2, h3, h4, h5⟩ := h hc₀'
  rw [hA2] at h2
  rw [hK] at h3
  rw [hK, hA1, hA2] at h4
  refine ⟨fun τ => ?_, h2, h3, h4, h5⟩
  obtain ⟨hn, d, hd, hdn⟩ := hb hmu τ
  rw [show edgeA1W 1 = StripMultiplier.edgeA1 from hA1] at hn hd
  refine ⟨hn, d, hd, ?_⟩
  simpa using hdn

/-- Non-vacuity of `lemma_J4_1_W`: for every weight and every `Q`, thermal differences `Ξ_β` are test
functions, so the representation, the strip Poisson identity and the `Q`-bounds hold for them. -/
theorem lemma_J4_1_W_thermalDiff (prob : FixedWeightProblem) :
    ∃ c₀ : ℝ, max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {β : ℝ}, 0 < β →
        (∀ τ : ℝ, tildeWW prob.w c' (thermalDiff prob.w β) (Complex.I * (τ : ℂ)) =
          ∫ t in Ioi (0 : ℝ),
            edgeKernelKW prob c' τ t *
              ((thermalDiff prob.w β t * prob.cardyV (c' / 12) t : ℝ) : ℂ)) ∧
        (∀ {ζ₀ : ℂ}, 0 < ζ₀.re → ζ₀.re < 1 →
          edgeHVW prob.w c' (thermalDiff prob.w β) ζ₀ =
            ∫ τ : ℝ, (stripPoissonQ ζ₀.re ζ₀.im (-1) τ : ℂ) *
              edgeHVW prob.w c' (thermalDiff prob.w β) ((τ : ℂ) * Complex.I)) := by
  obtain ⟨c₀, hc₀, h⟩ := lemma_J4_1_W prob
  refine ⟨c₀, hc₀, fun {c'} hc' {β} hβ => ?_⟩
  obtain ⟨hS, -, -⟩ := shift_le_of_max_le prob (hc₀.trans hc')
  obtain ⟨h1, -, h3, -⟩ := h hc' (thermalDiff_mem_TestClass prob hS hβ)
  exact ⟨h1, h3⟩

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_J4_1_of_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_J4_1_of_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_J4_2_of_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_J4_2_of_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_J4_1_W_thermalDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_J4_1_W_thermalDiff

end FormalResearch.ModularBootstrap.FixedWeightBand
