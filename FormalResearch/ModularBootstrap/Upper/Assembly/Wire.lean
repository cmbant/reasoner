module

public import FormalResearch.ModularBootstrap.Upper.Assembly.DesignWindow

/-!
# Wiring: Theorems `Σ₀`, `Σ` at Virasoro with Property `sr:P` discharged

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (`sr:Sigma0`, `sr:Sigma`),
`dual_spectrum.tex` (`ds:E1`).

* `virasoro_sigmaZero_of_threshold`: for every Virasoro crossing sequence with `T_V(c_j) ≤ τ_j`
  (`(Gap)` from the lower bound, `gapCondition_of_lowerBound`), the conclusion of `Σ₀` follows from the
  window algebra `SameSiteFamily designClass` alone: Property `sr:P` is `designPropertyP_virasoro`.
* `virasoro_sigmaZero`: the same for the extremal measures `ν_*(c_j)` of `corollary_E1_exact_gap`
  (`virasoro_exists_optimalCrossingSequence`).
* `virasoro_sigma_of_threshold`, `virasoro_sigma`: `Σ` with the designs outside the Lean class
  (`f ≥ 2` omitted sites, displaced sites) carried by an explicit class `𝒟x` with the hypotheses
  `∀ S, DesignPropertyP S.μS 𝒟x` and the displaced/omitted families on `designClass ∪ 𝒟x`.
* `SameSiteFamily.mono`, `DisplacedFamily.mono`, `OmittedFamily.mono`, `designPropertyP_union`.

The input `ThresholdUpperLittleOAt` is not used by `Σ₀`, `Σ` (as in the paper: the proof of
`Σ₀(a)` obtains `u(τ_j) → a_1` from the designs).  It is discharged for Virasoro in
`Assembly.Feasible` (`virasoro_thresholdUpperLittleO`), which gives `(Gap)` also through
`gapCondition_of_littleO`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Rigidity

/-! ### Monotonicity in the class -/

def SameSiteFamily.mono {𝒟 𝒟' : Set Window} (h : 𝒟 ⊆ 𝒟') (F : SameSiteFamily 𝒟) :
    SameSiteFamily 𝒟' :=
  { F with mem := fun k d hd => h (F.mem k d hd) }

def DisplacedFamily.mono {𝒟 𝒟' : Set Window} (h : 𝒟 ⊆ 𝒟') (F : DisplacedFamily 𝒟) :
    DisplacedFamily 𝒟' :=
  { F with mem := fun n k hn => h (F.mem n k hn) }

def OmittedFamily.mono {𝒟 𝒟' : Set Window} (h : 𝒟 ⊆ 𝒟') (F : OmittedFamily 𝒟) :
    OmittedFamily 𝒟' :=
  { F with mem := fun f k hf => h (F.mem f k hf) }

lemma designPropertyP_union {μ : ℕ → Measure ℝ} {𝒟 𝒟' : Set Window} (h : DesignPropertyP μ 𝒟)
    (h' : DesignPropertyP μ 𝒟') : DesignPropertyP μ (𝒟 ∪ 𝒟') := fun D hD =>
  hD.elim (fun hD => h D hD) (fun hD => h' D hD)

/-! ### `Σ₀` -/

/-- **`Σ₀` at Virasoro** for every crossing sequence with `T_V(c_j) ≤ τ_j`: only the window algebra
`SameSiteFamily designClass` is assumed. -/
theorem virasoro_sigmaZero_of_threshold (S : CrossingSequence virasoroProblem)
    (hτ : ∀ j, virasoroProblem.T_V (S.c j) ≤ S.τ j) (F : SameSiteFamily designClass) :
    SigmaZeroConclusion S.c S.τ S.μS :=
  theorem_sigma_zero_crossing S
    (gapCondition_of_lowerBound virasoro_lowerBoundInput S.tendsto_c hτ)
    (designPropertyP_virasoro S) F

/-- **`Σ₀` at Virasoro for the extremal measures** `ν_*(c_j)` (`T_V(c_j) = τ_j`, gap exactly
`T_V(c_j)`), for every `c_j → ∞`, `c_j ≥ c₀`. -/
theorem virasoro_sigmaZero (F : SameSiteFamily designClass) :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence virasoroProblem, S.c = cSeq ∧
        (∀ j, S.τ j = virasoroProblem.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        SigmaZeroConclusion S.c S.τ S.μS := by
  obtain ⟨c₀, h⟩ := virasoro_exists_optimalCrossingSequence
  refine ⟨c₀, fun cSeq hc hge => ?_⟩
  obtain ⟨S, hS, hτ, hchg, -⟩ := h cSeq hc hge
  exact ⟨S, hS, hτ, hchg,
    virasoro_sigmaZero_of_threshold S (fun j => by rw [hS, hτ j]) F⟩

/-! ### `Σ` -/

/-- **`Σ` at Virasoro** for every crossing sequence with `T_V(c_j) ≤ τ_j`.  `𝒟x` is the class of the
designs outside the Lean class (`f ≥ 2` omitted sites, displaced sites); the hypotheses are Property
`sr:P` for `𝒟x` and the window algebra on `designClass ∪ 𝒟x`. -/
theorem virasoro_sigma_of_threshold (S : CrossingSequence virasoroProblem)
    (hτ : ∀ j, virasoroProblem.T_V (S.c j) ≤ S.τ j) {𝒟x : Set Window}
    (hPx : DesignPropertyP S.μS 𝒟x) (F : SameSiteFamily designClass)
    (Dis : DisplacedFamily (designClass ∪ 𝒟x)) (Om : OmittedFamily (designClass ∪ 𝒟x)) :
    SigmaConclusion S.μS :=
  theorem_sigma_crossing S (gapCondition_of_lowerBound virasoro_lowerBoundInput S.tendsto_c hτ)
    (designPropertyP_union (designPropertyP_virasoro S) hPx)
    (SameSiteFamily.mono Set.subset_union_left F) Dis Om

/-- **`Σ` at Virasoro for the extremal measures** `ν_*(c_j)`. -/
theorem virasoro_sigma {𝒟x : Set Window}
    (hPx : ∀ S : CrossingSequence virasoroProblem, DesignPropertyP S.μS 𝒟x)
    (F : SameSiteFamily designClass)
    (Dis : DisplacedFamily (designClass ∪ 𝒟x)) (Om : OmittedFamily (designClass ∪ 𝒟x)) :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence virasoroProblem, S.c = cSeq ∧
        (∀ j, S.τ j = virasoroProblem.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        SigmaConclusion S.μS := by
  obtain ⟨c₀, h⟩ := virasoro_exists_optimalCrossingSequence
  refine ⟨c₀, fun cSeq hc hge => ?_⟩
  obtain ⟨S, hS, hτ, hchg, -⟩ := h cSeq hc hge
  exact ⟨S, hS, hτ, hchg,
    virasoro_sigma_of_threshold S (fun j => by rw [hS, hτ j]) (hPx S) F Dis Om⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.virasoro_sigmaZero_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_sigmaZero_of_threshold

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.virasoro_sigmaZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_sigmaZero

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.virasoro_sigma_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_sigma_of_threshold

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.virasoro_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_sigma

end FormalResearch.ModularBootstrap.Upper.Assembly
