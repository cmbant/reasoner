module

public import FormalResearch.ModularBootstrap.Duality.VagueCompactness

/-!
# A reserve survives a vague limit

If `c_j σ ≤ μ_j` for every `j` (with `c_j ≥ 0`, `c_j → c`) and `ν` is a vague limit of `μ_j`, then
`c σ ≤ ν` (`IsVagueLimitAlong.smul_le`).  This is the last step of the attainment clause of
`ds:E`(c) (`dual_spectrum.tex`): "a crossing measure dominating `R_X(σ) σ` by vague convergence
against nonnegative compactly supported tests".

The proof compares integrals against nonnegative `C_c` functions, passes to open sets by
Urysohn functions and inner regularity of `σ`, and to Borel sets by outer regularity of `ν`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace FormalResearch.ModularBootstrap.Duality

section Generic

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {𝒥 : Type*}
  {l : Filter 𝒥} {μ : 𝒥 → Measure Y} {ν : Measure Y}

/-- **Domination passes to vague limits**: if `ofReal (c j) • σ ≤ μ j` for all `j` (with `c j ≥ 0`),
`c j → c₀` and `ν` is a vague limit of `μ j` along `l`, then `ofReal c₀ • σ ≤ ν`. -/
theorem IsVagueLimitAlong.smul_le [l.NeBot] [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    [IsFiniteMeasureOnCompacts ν] (hν : IsVagueLimitAlong l μ ν) {σ : Measure Y}
    [IsFiniteMeasureOnCompacts σ] {c : 𝒥 → ℝ} {c₀ : ℝ} (hc : Tendsto c l (𝓝 c₀))
    (hc0j : ∀ j, 0 ≤ c j) (hdom : ∀ j, ENNReal.ofReal (c j) • σ ≤ μ j) :
    ENNReal.ofReal c₀ • σ ≤ ν := by
  have hc0 : 0 ≤ c₀ := ge_of_tendsto hc (Eventually.of_forall hc0j)
  -- Step 1: nonnegative compactly supported test functions.
  have step1 : ∀ g : Y → ℝ, Continuous g → HasCompactSupport g → (∀ y, 0 ≤ g y) →
      c₀ * ∫ y, g y ∂σ ≤ ∫ y, g y ∂ν := by
    intro g hg hgcs hg0
    have hlim := hν g hg hgcs
    have hle : ∀ j, c j * ∫ y, g y ∂σ ≤ ∫ y, g y ∂(μ j) := fun j => by
      have h1 := integral_mono_measure (hdom j) (Eventually.of_forall hg0)
        (integrable_of_cs' (μ := μ j) hg hgcs)
      rwa [integral_smul_measure, ENNReal.toReal_ofReal (hc0j j), smul_eq_mul] at h1
    exact le_of_tendsto_of_tendsto (hc.mul_const _) hlim (Eventually.of_forall hle)
  -- Step 2: open sets.
  have step2 : ∀ U : Set Y, IsOpen U → ENNReal.ofReal c₀ * σ U ≤ ν U := by
    intro U hU
    rw [hU.measure_eq_iSup_isCompact σ, ENNReal.mul_iSup]
    refine iSup_le fun K => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hKU => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hK => ?_
    obtain ⟨f, hfK, hfU, hfcs, hf01⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hKU)
    have hint_σ := integrable_of_cs' (μ := σ) f.continuous hfcs
    have hint_ν := integrable_of_cs' (μ := ν) f.continuous hfcs
    have h1 : σ K ≤ ENNReal.ofReal (∫ u, f u ∂σ) :=
      hint_σ.measure_le_integral (Eventually.of_forall fun x => (hf01 x).1)
        (fun x hx => by simp [hfK hx])
    have h2 := step1 f f.continuous hfcs fun y => (hf01 y).1
    have h3 : ENNReal.ofReal (∫ u, f u ∂ν) ≤ ν U := by
      rw [ofReal_integral_eq_lintegral_ofReal hint_ν (Eventually.of_forall fun x => (hf01 x).1)]
      calc ∫⁻ u, ENNReal.ofReal (f u) ∂ν ≤ ∫⁻ u, U.indicator 1 u ∂ν := by
            refine lintegral_mono fun u => ?_
            by_cases hu : u ∈ U
            · simpa [hu] using (hf01 u).2
            · have : f u = 0 := hfU (by simpa using hu)
              simp [hu, this]
        _ = ν U := lintegral_indicator_one hU.measurableSet
    calc ENNReal.ofReal c₀ * σ K ≤ ENNReal.ofReal c₀ * ENNReal.ofReal (∫ u, f u ∂σ) :=
          mul_le_mul_right h1 _
      _ = ENNReal.ofReal (c₀ * ∫ u, f u ∂σ) := (ENNReal.ofReal_mul hc0).symm
      _ ≤ ENNReal.ofReal (∫ u, f u ∂ν) := ENNReal.ofReal_le_ofReal h2
      _ ≤ ν U := h3
  -- Step 3: Borel sets, by outer regularity of `ν`.
  refine Measure.le_iff.2 fun s hs => ?_
  rw [smul_apply, smul_eq_mul, Set.measure_eq_iInf_isOpen s ν]
  refine le_iInf fun U => le_iInf fun hsU => le_iInf fun hU => ?_
  exact (mul_le_mul_right (measure_mono hsU) _).trans (step2 U hU)

end Generic

end FormalResearch.ModularBootstrap.Duality
