module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.CrossingDictionary
public import FormalResearch.ModularBootstrap.Upper.Rigidity.Sigma
public import FormalResearch.ModularBootstrap.FixedWeight.LittleOUpper

/-!
# Spectral rigidity for crossing measures: wiring `μ_S` into `Theorem Σ₀`, `Theorem Σ`

This module connects the dictionary `CrossingDictionary` (the spectral measure `μ_S` of a crossing
measure and Proposition `sr:P1`) with the abstract measure-level rigidity theorems of
`Upper.Rigidity` (`SpectralData`, `theorem_sigma_zero_*`, `theorem_sigma`).

* `CrossingSequence prob`: admissible crossing measures `ν_j` at `c_j → ∞` (`a_j = c_j / 12`) supported
  on `[τ_j, ∞)`, `τ_j > 0`; `CrossingSequence.μS` are their spectral measures `μ_j = μ_{S_j}`, which
  are locally finite and live on `u ≤ u(τ_j)` (`CrossingSequence.isLocallyFinite`,
  `CrossingSequence.supp`), so that `CrossingSequence.spectralData` is an instance of `SpectralData`
  once (Gap) holds.
* (Gap) from the lower bound alone: `gapCondition_of_lowerBound` (`FixedWeightLowerBoundInput`, i.e.
  Theorem J at Virasoro, and `τ_j ≥ T_V(c_j)`); `gapCondition_of_littleO` is the route through
  `corollary_E1_littleO` and `gapCondition_of_tendsto`.
* `exists_optimalCrossingSequence`: for every `c_j → ∞` (`c_j ≥ c₀`) the extremal crossing measures
  `ν_*(c_j)` of `corollary_E1_exact_gap` (`ν_*` at gap exactly `T_V(c_j)`) form a `CrossingSequence`
  satisfying (Gap); at Virasoro unconditionally (`virasoro_exists_optimalCrossingSequence`).
* **`theorem_sigma_crossing`** (`sr:Sigma`) and **`theorem_sigma_zero_crossing`** (`sr:Sigma0`):
  the abstract theorems for `μ_S`.  Inputs: (Gap); Property `sr:P` as the named hypothesis
  `DesignPropertyP` (not formalised); the window algebra `SameSiteFamily` (`Σ₀`, `Σ`),
  `DisplacedFamily`, `OmittedFamily` (`Σ`, not formalised).  The upper threshold bound
  `ThresholdUpperLittleOAt` is **not** used: the proof of `Σ₀(a)` obtains `u(τ_j) → a₁`
  from the designs, and (Gap) needs only the lower bound.
  `theorem_sigma_crossing_optimal` / `theorem_sigma_zero_crossing_optimal` state both for the
  extremal measures `ν_*(c_j)`.
* `CombDesignData`: the comb data `(P1)`–`(P4)` of one design for `μ_S`, with the summation part of
  `(P1)` discharged by `sr:P1` (`spectral_poisson_summation_comb`); `CombDesignData.toDesignTest`,
  `designPropertyP_of_comb`: Property `sr:P` for `μ_S` follows from comb data alone, and
  `crossingSequence_nonempty` shows the setting is non-vacuous (Virasoro).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight

/-- A sequence of admissible crossing measures `ν_j` at `c_j → ∞` (`a_j = c_j/12`) supported on
`[τ_j, ∞)` with `τ_j > 0` (`τ_j` is a lower bound for the spectrum, `= min_n t_n` for the
spectrum of the measure). -/
structure CrossingSequence (prob : FixedWeightProblem) where
  c : ℕ → ℝ
  τ : ℕ → ℝ
  meas : ∀ j, AdmissibleCrossingMeasure prob (c j / 12)
  tendsto_c : Tendsto c atTop atTop
  c_pos : ∀ j, 0 < c j
  shift_le : ∀ j, prob.totalShift ≤ c j / 12
  τ_pos : ∀ j, 0 < τ j
  atGap : ∀ j, IsAtGap (meas j) (τ j)

namespace CrossingSequence

variable {prob : FixedWeightProblem} (S : CrossingSequence prob)

/-- The spectral measures `μ_j = μ_{S_j}` in the Airy variable. -/
noncomputable def μS (j : ℕ) : Measure ℝ := spectralMeasure prob (S.c j) (S.meas j).ν

lemma isLocallyFinite (j : ℕ) : IsLocallyFiniteMeasure (S.μS j) :=
  isLocallyFiniteMeasure_spectralMeasure prob (S.c_pos j) (S.shift_le j) (S.meas j) (S.τ_pos j)
    (S.atGap j)

instance (j : ℕ) : IsLocallyFiniteMeasure (S.μS j) := S.isLocallyFinite j

/-- `μ_j` lives on `u ≤ u(τ_j)`. -/
lemma supp (j : ℕ) : S.μS j (Ioi (uAiry (S.c j) (S.τ j))) = 0 :=
  spectralMeasure_Ioi_eq_zero prob (S.c_pos j) (S.meas j) (S.atGap j)

/-- A crossing sequence with (Gap) is `SpectralData` (`μ_j` supported on `u ≤ u(τ_j)`, `s_j = u(τ_j)`
with `limsup s_j ≤ a₁`). -/
noncomputable def spectralData (hgap : GapCondition S.c S.τ) : SpectralData :=
  SpectralData.ofGap S.tendsto_c hgap S.μS S.supp

@[simp] lemma spectralData_μ (hgap : GapCondition S.c S.τ) : (S.spectralData hgap).μ = S.μS := rfl

@[simp] lemma spectralData_s (hgap : GapCondition S.c S.τ) (j : ℕ) :
    (S.spectralData hgap).s j = uAiry (S.c j) (S.τ j) := rfl

end CrossingSequence

/-! ### (Gap) -/

/-- (Gap) of `sr:Sigma0`, `sr:Sigma` from the threshold lower bound alone (Theorem J at Virasoro):
if `T_V(c_j) ≤ τ_j` (in particular for the extremal measures with `τ_j = T_V(c_j)`), then
`liminf (τ_j - T_*(c_j)) / c_j^{1/3} ≥ 0`. -/
theorem gapCondition_of_lowerBound {prob : FixedWeightProblem}
    (hLo : FixedWeightLowerBoundInput prob) {c τ : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (hτ : ∀ j, prob.T_V (c j) ≤ τ j) : GapCondition c τ := by
  obtain ⟨c₁, D, -, hD, hlo⟩ := hLo
  intro δ hδ
  have hr : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 3)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hc3 : Tendsto (fun j => (c j) ^ ((1 : ℝ) / 3)) atTop atTop := hr.comp hc
  have hD' : ∀ᶠ j in atTop, D / (c j) ^ ((1 : ℝ) / 3) < δ :=
    (tendsto_const_nhds.div_atTop hc3).eventually (gt_mem_nhds hδ)
  filter_upwards [hD', hc.eventually (eventually_ge_atTop c₁), hc3.eventually_gt_atTop 0]
    with j h1 h2 h3
  rw [div_lt_iff₀ h3] at h1
  have := hlo h2
  have := hτ j
  linarith

/-- (Gap) through `corollary_E1_littleO` and `gapCondition_of_tendsto`: with both threshold bounds,
`(T_V(c_j) - T_*(c_j)) / c_j^{1/3} → 0` for every `c_j → ∞`, so (Gap) holds for `τ_j = T_V(c_j)`. -/
theorem gapCondition_of_littleO (prob : FixedWeightProblem)
    (hLo : FixedWeightLowerBoundInput prob)
    (hHi : ThresholdUpperLittleOAt prob.T_V prob.totalShift) {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) : GapCondition c (fun j => prob.T_V (c j)) := by
  obtain ⟨-, -, -, -, -, -, hlim⟩ := corollary_E1_littleO prob hLo hHi
  exact gapCondition_of_tendsto hc (hlim c hc)

/-! ### The extremal crossing measures `ν_*(c_j)` -/

private lemma TStar_sub_pos' {D : ℝ} {c : ℝ} (hc : max 1 (D / xiBar + 1) ≤ c) :
    0 < TStar c - D := by
  have hxi : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hc2 : D / xiBar + 1 ≤ c := (le_max_right _ _).trans hc
  have h0 : D < xiBar * c := by
    have hlt : D / xiBar < c := by linarith
    rwa [div_lt_iff₀ hxi, mul_comm] at hlt
  have hA : 0 ≤ Aopt * c ^ ((1 : ℝ) / 3) := by
    have hAopt : 0 ≤ Aopt := by unfold Aopt; exact mul_nonneg cStar_pos.le (abs_nonneg _)
    positivity
  unfold TStar
  linarith

/-- **The extremal crossing measures form a crossing sequence with (Gap)**
(`corollary_E1_exact_gap` + the lower bound): there is `c₀` such that for every `c_j → ∞` with
`c_j ≥ c₀` there are admissible crossing measures `ν_*(c_j)` supported on `[T_V(c_j), ∞)` and
charging every `[T_V(c_j), T_V(c_j) + ε)` (so `τ_j = T_V(c_j) = min supp`), forming a
`CrossingSequence` with (Gap).  Only `FixedWeightLowerBoundInput` is used. -/
theorem exists_optimalCrossingSequence (prob : FixedWeightProblem)
    (hLo : FixedWeightLowerBoundInput prob) :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence prob, S.c = cSeq ∧ (∀ j, S.τ j = prob.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        GapCondition S.c S.τ := by
  obtain ⟨c₁, D, hc₁, hD, hlo⟩ := hLo
  refine ⟨max c₁ (D / xiBar + 1), fun cSeq hcSeq hge => ?_⟩
  have h1 : ∀ j, c₁ ≤ cSeq j := fun j => (le_max_left _ _).trans (hge j)
  have hc1 : ∀ j, 1 ≤ cSeq j := fun j => (le_max_left _ _).trans (hc₁.trans (h1 j))
  have hpos : ∀ j, 0 < cSeq j := fun j => lt_of_lt_of_le zero_lt_one (hc1 j)
  have hshift : ∀ j, 12 * prob.totalShift ≤ cSeq j :=
    fun j => (le_max_right _ _).trans (hc₁.trans (h1 j))
  have hTV : ∀ j, 0 < prob.T_V (cSeq j) := fun j =>
    lt_of_lt_of_le (TStar_sub_pos' (max_le (hc1 j) ((le_max_right _ _).trans (hge j))))
      (hlo (h1 j))
  have hex := fun j => corollary_E1_exact_gap prob (hpos j) (hshift j) (hTV j)
  choose meas hat hchg _ using hex
  have hsh : ∀ j, prob.totalShift ≤ cSeq j / 12 := fun j => by linarith [hshift j]
  refine ⟨⟨cSeq, fun j => prob.T_V (cSeq j), meas, hcSeq, hpos, hsh, hTV, hat⟩, rfl,
    fun _ => rfl, hchg, ?_⟩
  exact gapCondition_of_lowerBound ⟨c₁, D, hc₁, hD, hlo⟩ hcSeq fun _ => le_rfl

/-- Virasoro: the extremal crossing measures exist for every `c_j → ∞` (`c_j ≥ c₀`) and satisfy
(Gap), unconditionally (Theorem J, `virasoro_lowerBoundInput`). -/
theorem virasoro_exists_optimalCrossingSequence :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence virasoroProblem, S.c = cSeq ∧
        (∀ j, S.τ j = virasoroProblem.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        GapCondition S.c S.τ :=
  exists_optimalCrossingSequence virasoroProblem virasoro_lowerBoundInput

/-- Non-vacuity: crossing sequences exist (at Virasoro, unconditionally). -/
theorem crossingSequence_nonempty : Nonempty (CrossingSequence virasoroProblem) := by
  obtain ⟨c₀, h⟩ := virasoro_exists_optimalCrossingSequence
  obtain ⟨S, -⟩ := h (fun j => c₀ + j) (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
    (fun j => by simp)
  exact ⟨S⟩

/-! ### `Theorem Σ₀` and `Theorem Σ` for the spectral measures of crossing measures -/

/-- The conclusion of `Theorem Σ` (`sr:Sigma`) for spectral measures `μ_j` (as in `theorem_sigma`). -/
def SigmaConclusion (μ : ℕ → Measure ℝ) : Prop :=
  LocallyBounded μ ∧
    (∀ 𝒰 : Ultrafilter ℕ, (𝒰 : Filter ℕ) ≤ atTop → ∃ ν : Measure ℝ, IsLocallyFiniteMeasure ν ∧
      IsVagueLimit 𝒰 μ ν ∧ ν (Ioi (airyZero 1)) = 0) ∧
    (∀ 𝒰 : Ultrafilter ℕ, (𝒰 : Filter ℕ) ≤ atTop → ∀ ν : Measure ℝ, IsLocallyFiniteMeasure ν →
      IsVagueLimit 𝒰 μ ν → ν (Set.range airyNode)ᶜ = 0 ∧
        (∀ i, atomWeight ν i ≤ 1) ∧ ∀ i, atomWeight ν i = 1) ∧
    IsVagueLimit atTop μ airyMeasure ∧
    (∀ D : Window, ∀ T : DesignTest μ D, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ᶠ j in atTop, ∫ u in Iio (-R), T.Ψ j u ∂(μ j) ≤ ε)

/-- The conclusion of `Theorem Σ₀` (`sr:Sigma0`) for spectral measures `μ_j` with first levels
`τ_j` at `c_j`. -/
def SigmaZeroConclusion (c τ : ℕ → ℝ) (μ : ℕ → Measure ℝ) : Prop :=
  ((∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, |τ j - TStar (c j)| ≤ δ * (c j) ^ ((1 : ℝ) / 3)) ∧
    Tendsto (fun j => uAiry (c j) (τ j)) atTop (𝓝 (airyZero 1))) ∧
  ∀ ρ : ℝ, 0 < ρ →
    ENNReal.ofReal (1 / (airyAi' (airyZero 1)) ^ 2) ≤
      liminf (fun j => μ j (Icc (airyZero 1 - ρ) (airyZero 1 + ρ))) atTop

/-- **Theorem `Σ`** (`sr:Sigma`) for the spectral measures `μ_S` of a crossing sequence with (Gap).
Hypotheses: (Gap) (`gapCondition_of_lowerBound`); Property `sr:P` for `μ_S` (`DesignPropertyP`; it
follows from comb data by `designPropertyP_of_comb`); the window algebra `SameSiteFamily`,
`DisplacedFamily`, `OmittedFamily`.  The upper threshold bound is not used. -/
theorem theorem_sigma_crossing {prob : FixedWeightProblem} (S : CrossingSequence prob)
    (hgap : GapCondition S.c S.τ) {𝒟 : Set Window} (hP : DesignPropertyP S.μS 𝒟)
    (F : SameSiteFamily 𝒟) (Dis : DisplacedFamily 𝒟) (Om : OmittedFamily 𝒟) :
    SigmaConclusion S.μS :=
  theorem_sigma S.tendsto_c hgap S.μS S.supp hP F Dis Om

/-- **Theorem `Σ₀`** (`sr:Sigma0`(a), (b)) for the spectral measures `μ_S` of a crossing sequence
with (Gap): inputs `DesignPropertyP` and `SameSiteFamily` only. -/
theorem theorem_sigma_zero_crossing {prob : FixedWeightProblem} (S : CrossingSequence prob)
    (hgap : GapCondition S.c S.τ) {𝒟 : Set Window} (hP : DesignPropertyP S.μS 𝒟)
    (F : SameSiteFamily 𝒟) : SigmaZeroConclusion S.c S.τ S.μS :=
  ⟨theorem_sigma_zero_a S.tendsto_c hgap S.μS S.supp hP F,
    fun _ hρ => theorem_sigma_zero_b S.tendsto_c hgap S.μS S.supp hP F hρ⟩

/-- **`Σ` for the extremal measures `ν_*(c_j)`**: for every `c_j → ∞` (`c_j ≥ c₀`) the extremal
crossing measures of `corollary_E1_exact_gap` form a crossing sequence with `τ_j = T_V(c_j)` and
(Gap), and for it the conclusion of `Σ` follows from `DesignPropertyP` and the window algebra.
The only input beyond those is `FixedWeightLowerBoundInput` (unconditional at Virasoro). -/
theorem theorem_sigma_crossing_optimal (prob : FixedWeightProblem)
    (hLo : FixedWeightLowerBoundInput prob) :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence prob, S.c = cSeq ∧ (∀ j, S.τ j = prob.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        ∀ {𝒟 : Set Window}, DesignPropertyP S.μS 𝒟 → SameSiteFamily 𝒟 → DisplacedFamily 𝒟 →
          OmittedFamily 𝒟 → SigmaConclusion S.μS := by
  obtain ⟨c₀, h⟩ := exists_optimalCrossingSequence prob hLo
  refine ⟨c₀, fun cSeq hc hge => ?_⟩
  obtain ⟨S, hS, hτ, hchg, hgap⟩ := h cSeq hc hge
  exact ⟨S, hS, hτ, hchg, fun hP F Dis Om => theorem_sigma_crossing S hgap hP F Dis Om⟩

/-- **`Σ₀` for the extremal measures `ν_*(c_j)`** (see `theorem_sigma_crossing_optimal`). -/
theorem theorem_sigma_zero_crossing_optimal (prob : FixedWeightProblem)
    (hLo : FixedWeightLowerBoundInput prob) :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence prob, S.c = cSeq ∧ (∀ j, S.τ j = prob.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        ∀ {𝒟 : Set Window}, DesignPropertyP S.μS 𝒟 → SameSiteFamily 𝒟 →
          SigmaZeroConclusion S.c S.τ S.μS := by
  obtain ⟨c₀, h⟩ := exists_optimalCrossingSequence prob hLo
  refine ⟨c₀, fun cSeq hc hge => ?_⟩
  obtain ⟨S, hS, hτ, hchg, hgap⟩ := h cSeq hc hge
  exact ⟨S, hS, hτ, hchg, fun hP F => theorem_sigma_zero_crossing S hgap hP F⟩

/-- Virasoro: `Σ` for the extremal measures `ν_*(c_j)`, unconditionally except for Property `sr:P`
and the window algebra. -/
theorem virasoro_theorem_sigma_crossing_optimal :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence virasoroProblem, S.c = cSeq ∧
        (∀ j, S.τ j = virasoroProblem.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        ∀ {𝒟 : Set Window}, DesignPropertyP S.μS 𝒟 → SameSiteFamily 𝒟 → DisplacedFamily 𝒟 →
          OmittedFamily 𝒟 → SigmaConclusion S.μS :=
  theorem_sigma_crossing_optimal virasoroProblem virasoro_lowerBoundInput

/-- Virasoro: `Σ₀` for the extremal measures `ν_*(c_j)`. -/
theorem virasoro_theorem_sigma_zero_crossing_optimal :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence virasoroProblem, S.c = cSeq ∧
        (∀ j, S.τ j = virasoroProblem.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        ∀ {𝒟 : Set Window}, DesignPropertyP S.μS 𝒟 → SameSiteFamily 𝒟 →
          SigmaZeroConclusion S.c S.τ S.μS :=
  theorem_sigma_zero_crossing_optimal virasoroProblem virasoro_lowerBoundInput

/-! ### Property `sr:P` for `μ_S` from comb data: `(P1)` by `sr:P1` -/

/-- The data of one design `D` for the crossing sequence `S`: comb functionals `g_j ∈ Ā_{w}` at
`c = c_j` with comb decay (`(P1)`, `|g| ≤ C e^{-c'L - πx}`), scalings `2/(C_* FK_c) > 0`,
positivity of `g_j` on `[t_f + 1, ∞)` (`(P2)`, with `θ_j = u(t_f(j) + 1) → u_f`), the local uniform
window limit (`(P3)`) and the limsup bound for `∫ Ψ du` (`(P4)`).  The summation identity part of
`(P1)` (`∫ Ψ dμ_j = ∫ Ψ du`, integrability) is not a field: it is `sr:P1`. -/
structure CombDesignData {prob : FixedWeightProblem} (S : CrossingSequence prob) (D : Window) where
  g : ℕ → ℝ → ℝ
  scale : ℕ → ℝ
  tf : ℕ → ℝ
  scale_pos : ∀ j, 0 < scale j
  testClass : ∀ j, TestClass prob (S.c j / 12) (g j)
  decay : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
    |g j t| ≤ C * Real.exp (-4 * π * Real.sqrt ((S.c j / 12) * t) - π * Real.sqrt (3 * t / S.c j))
  tf_nonneg : ∀ j, 0 ≤ tf j + 1
  g_nonneg : ∀ j t, tf j + 1 ≤ t → 0 ≤ g j t
  theta_tendsto : Tendsto (fun j => uAiry (S.c j) (tf j + 1)) atTop (𝓝 D.uF)
  window_limit : TendstoLocallyUniformly (fun j u => scale j * psiAiry prob (S.c j) (g j) u) D.W atTop
  limsup_le : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
    ∫ u, scale j * psiAiry prob (S.c j) (g j) u ≤ D.V + ε

/-- Comb data gives a `DesignTest` for `μ_S`: `(P1)` is `sr:P1`. -/
noncomputable def CombDesignData.toDesignTest {prob : FixedWeightProblem}
    {S : CrossingSequence prob} {D : Window} (X : CombDesignData S D) : DesignTest S.μS D where
  Ψ := fun j u => X.scale j * psiAiry prob (S.c j) (X.g j) u
  θ := fun j => uAiry (S.c j) (X.tf j + 1)
  continuous := fun j =>
    continuous_const.mul (continuous_psiAiry (S.c_pos j) (X.testClass j).cont)
  integrable_mu := fun j => by
    obtain ⟨C, hC, hdec⟩ := X.decay j
    exact (spectral_poisson_summation_comb prob (S.c_pos j) (S.shift_le j) (S.meas j)
      (nu_zero_eq_zero (S.τ_pos j) (S.atGap j)) (X.testClass j) hC hdec).1.const_mul _
  integrable_vol := fun j =>
    (integrable_psiAiry_of_testClass prob (S.c_pos j) (S.shift_le j) (X.testClass j)).const_mul _
  crossing := fun j => by
    obtain ⟨C, hC, hdec⟩ := X.decay j
    have := (spectral_poisson_summation_comb prob (S.c_pos j) (S.shift_le j) (S.meas j)
      (nu_zero_eq_zero (S.τ_pos j) (S.atGap j)) (X.testClass j) hC hdec).2.2
    rw [integral_const_mul, integral_const_mul]
    exact congrArg _ this
  nonneg := fun j u hu => by
    have := psiAiry_nonneg (prob := prob) (S.c_pos j) (S.shift_le j) (X.tf_nonneg j)
      (X.g_nonneg j) hu
    exact mul_nonneg (X.scale_pos j).le this
  theta_tendsto := X.theta_tendsto
  window_limit := X.window_limit
  limsup_le := X.limsup_le

/-- Property `sr:P` for the spectral measures `μ_S` of a crossing sequence follows from comb data
for every design of the class (the content of `sr:P` that is not formalised is the construction
of the comb data). -/
theorem designPropertyP_of_comb {prob : FixedWeightProblem} (S : CrossingSequence prob)
    {𝒟 : Set Window} (h : ∀ D ∈ 𝒟, Nonempty (CombDesignData S D)) : DesignPropertyP S.μS 𝒟 :=
  fun D hD => (h D hD).elim fun X => ⟨X.toDesignTest⟩

/-- The zero window `W = 0` with `u_f = 0` (a degenerate design). -/
noncomputable def zeroWindow : Window where
  W := fun _ => 0
  uF := 0
  continuous := continuous_const
  integrable := integrable_zero _ _ _
  nonneg_left := fun _ _ => le_rfl
  hasSum := by simp

lemma uAiry_xiBar_mul {c : ℝ} (hc : 0 < c) : uAiry c (xiBar * c) = 0 := by
  unfold uAiry
  have : 3 * (xiBar * c) / c = xiStar ^ 2 := by
    unfold xiBar; field_simp
  rw [this, Real.sqrt_sq xiStar_pos.le]; ring

/-- Non-vacuity of `CombDesignData`: the degenerate design (`g_j = 0`, `W = 0`, `u_f = 0`,
`t_f(j) + 1 = ξ̄ c_j`, so that `u(t_f + 1) = 0`) satisfies every field for every crossing sequence.
(The real content of Property `sr:P`, non-trivial combs with window `W_𝔇`, is not formalised.) -/
theorem combDesignData_nonvacuous {prob : FixedWeightProblem} (S : CrossingSequence prob) :
    Nonempty (CombDesignData S zeroWindow) := by
  have hxi : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  refine ⟨{
    g := fun _ _ => 0
    scale := fun _ => 1
    tf := fun j => xiBar * S.c j - 1
    scale_pos := fun _ => one_pos
    testClass := fun j => by
      simpa using (thermalDiff_mem_TestClass prob (S.shift_le j)
        (by norm_num : (0 : ℝ) < 1 / 2)).smul 0
    decay := fun j => ⟨0, le_rfl, fun t _ => by simp⟩
    tf_nonneg := fun j => by have := S.c_pos j; simp; positivity
    g_nonneg := fun _ _ _ => le_rfl
    theta_tendsto := by
      refine tendsto_const_nhds.congr fun j => ?_
      show (0 : ℝ) = uAiry (S.c j) (xiBar * S.c j - 1 + 1)
      rw [sub_add_cancel, uAiry_xiBar_mul (S.c_pos j)]
    window_limit := (Metric.tendstoUniformly_iff.2 fun ε hε =>
      Eventually.of_forall fun j x => by
        simpa [psiAiry, zeroWindow] using hε).tendstoLocallyUniformly
    limsup_le := fun ε hε => Eventually.of_forall fun j => by
      simp [psiAiry, Window.V, zeroWindow]; exact hε.le }⟩


/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.gapCondition_of_lowerBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.gapCondition_of_lowerBound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.gapCondition_of_littleO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.gapCondition_of_littleO

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.exists_optimalCrossingSequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.exists_optimalCrossingSequence

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.virasoro_exists_optimalCrossingSequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.virasoro_exists_optimalCrossingSequence

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.crossingSequence_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.crossingSequence_nonempty

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_crossing

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_zero_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_zero_crossing

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_crossing_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_crossing_optimal

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_zero_crossing_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_zero_crossing_optimal

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.virasoro_theorem_sigma_crossing_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.virasoro_theorem_sigma_crossing_optimal

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.virasoro_theorem_sigma_zero_crossing_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.virasoro_theorem_sigma_zero_crossing_optimal

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.designPropertyP_of_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.designPropertyP_of_comb

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.CombDesignData.toDesignTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.CombDesignData.toDesignTest

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.combDesignData_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.combDesignData_nonvacuous

end FormalResearch.ModularBootstrap.Upper.Rigidity
