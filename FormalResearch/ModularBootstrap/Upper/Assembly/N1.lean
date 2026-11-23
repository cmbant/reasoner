module

public import FormalResearch.ModularBootstrap.Upper.Assembly.FarFirstSite
public import FormalResearch.ModularBootstrap.Upper.Assembly.Feasible
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedFinal
public import FormalResearch.ModularBootstrap.FixedWeightBand.N1Lower

/-!
# `N = 1` super-Virasoro: the upper/design side and the two-sided laws, unconditional

Source: `CFT/modular_bootstrap/paper/n1_super_virasoro.tex` (Setting `(H_w)`, `n1:T3`, `n1:L4`), with the
design side of `upper_transfer.tex`, `spectral_rigidity.tex` and `n2_ramped_comb.tex` (Lemma `U*`).

The design, vacuum, window, tail and ramped-comb arguments are formalised for every `FixedWeightProblem` with
`prob.w = 1` (`Upper.Window.Cardy.cardyWindowBound_prob`, `Upper.Window.Tail.lemma_T_prob`,
`Upper.Positivity.vacuum_core`, `designPropertyP_prob`, `thresholdUpperLittleO_prob`, `sigmaZero_unconditional_prob`,
`sigma_unconditional_prob`, `Upper.Ramped.theoremC15UpperInput_prob`); the Cardy ratio is the uniform
asymptotic `cardyV_asymptotic_real` (`n1:L4`(f)) and the window scale is `FK_c = FKc (qProb prob) 1 c'`,
`𝔮 = Q(e^{-4πξ_*}) / (1 - e^{-4πξ_*})²`.  The lower bound is `FixedWeightBand.n1_lowerBoundInput`.  This module
instantiates them at `n1SuperVirasoroProblem` (`w = 1`, `Q(q) = (1 - q^{1/2})²`).

* `n1_designPropertyP`: Property `sr:P` for the designs `D(N, η_*, d)`;
* `n1_thresholdUpperLittleO`: `T_V(c) ≤ T_*(c) + δ c^{1/3}` (FW-C);
* `n1_theoremC15UpperInput`: `T_V(c) ≤ T_*(c) + D_+` (Lemma `U*`, `rem:thmU`);
* `n1_corollary_E1_littleO_unconditional`, `n1_corollary_E1_unconditional`: the `o(c^{1/3})` and `O(1)`
  two-term laws `Δ_best = c/Λ_V + A_opt c^{1/3} + o(c^{1/3})`, resp. `+ O(1)`;
* `n1_sigmaZero_unconditional`, `n1_sigma_unconditional`: Theorems `Σ₀`, `Σ` for the extremal measures;
* `n1_rampedVacuum`: the vacuum step of Lemma `U*`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.FixedWeightBand
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Membership FormalResearch.ModularBootstrap.Upper.Hankel

lemma n1SuperVirasoroProblem_w : n1SuperVirasoroProblem.w = 1 := rfl

/-- **Property `sr:P` for the designs `D(N, η_*, d)` at `N = 1` super-Virasoro.** -/
theorem n1_designPropertyP (S : CrossingSequence n1SuperVirasoroProblem) :
    DesignPropertyP S.μS designClass :=
  designPropertyP_prob n1SuperVirasoroProblem rfl S

/-- **FW-C at `N = 1` super-Virasoro**: `T_V(c) ≤ T_*(c) + δ c^{1/3}` for every `δ > 0` and `c` large. -/
theorem n1_thresholdUpperLittleO :
    ThresholdUpperLittleOAt n1SuperVirasoroProblem.T_V n1SuperVirasoroProblem.totalShift :=
  thresholdUpperLittleO_prob n1SuperVirasoroProblem rfl

/-- **Lemma `U*` at `N = 1` super-Virasoro**: `T_V(c̃) ≤ T_*(c̃) + D_+` for `c̃` large. -/
theorem n1_theoremC15UpperInput : TheoremC15UpperInput n1SuperVirasoroProblem :=
  Upper.Ramped.theoremC15UpperInput_prob n1SuperVirasoroProblem rfl

/-- **`N = 1` super-Virasoro, Corollary E1 with the `o(c^{1/3})` upper bound, unconditional.** -/
theorem n1_corollary_E1_littleO_unconditional :
    ∃ c₀ D : ℝ, max 1 (12 * n1SuperVirasoroProblem.totalShift) ≤ c₀ ∧ 0 ≤ D ∧
      (∀ {c : ℝ}, c₀ ≤ c →
        0 < n1SuperVirasoroProblem.T_V c ∧
        ∃ meas : AdmissibleCrossingMeasure n1SuperVirasoroProblem (c / 12),
          meas.ν (Iio (n1SuperVirasoroProblem.T_V c)) = 0 ∧
          (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (n1SuperVirasoroProblem.T_V c + ε))) ∧
          n1SuperVirasoroProblem.Delta_best c = c / 12 + n1SuperVirasoroProblem.T_V c) ∧
      (∀ δ : ℝ, 0 < δ → ∃ c₁ : ℝ, ∀ {c : ℝ}, c₁ ≤ c →
        |n1SuperVirasoroProblem.T_V c - TStar c| ≤ D + δ * c ^ ((1 : ℝ) / 3) ∧
        |n1SuperVirasoroProblem.Delta_best c - (c / lambdaV + Aopt * c ^ ((1 : ℝ) / 3))| ≤
          D + δ * c ^ ((1 : ℝ) / 3)) ∧
      (∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop →
        Tendsto (fun j => (n1SuperVirasoroProblem.T_V (cSeq j) - TStar (cSeq j)) /
          (cSeq j) ^ ((1 : ℝ) / 3)) atTop (𝓝 0)) :=
  corollary_E1_littleO n1SuperVirasoroProblem n1_lowerBoundInput n1_thresholdUpperLittleO

/-- **`N = 1` super-Virasoro, Corollary E1, unconditional**: the two-sided `O(1)` law
`Δ_best = c/Λ_V + A_opt c^{1/3} + O(1)`, `T_V = T_* + O(1)`, with the extremal measure and the `(Gap)`
clause. -/
theorem n1_corollary_E1_unconditional :
    ∃ c₀ C : ℝ, max 1 (12 * n1SuperVirasoroProblem.totalShift) ≤ c₀ ∧ 0 ≤ C ∧
      (∀ {c : ℝ}, c₀ ≤ c →
        0 < n1SuperVirasoroProblem.T_V c ∧
        |n1SuperVirasoroProblem.T_V c - TStar c| ≤ C ∧
        |n1SuperVirasoroProblem.Delta_best c - (c / lambdaV + Aopt * c ^ ((1 : ℝ) / 3))| ≤ C ∧
        ∃ meas : AdmissibleCrossingMeasure n1SuperVirasoroProblem (c / 12),
          meas.ν (Iio (n1SuperVirasoroProblem.T_V c)) = 0 ∧
          (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (n1SuperVirasoroProblem.T_V c + ε))) ∧
          n1SuperVirasoroProblem.Delta_best c = c / 12 + n1SuperVirasoroProblem.T_V c) ∧
      (∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop →
        Tendsto (fun j => (n1SuperVirasoroProblem.T_V (cSeq j) - TStar (cSeq j)) /
          (cSeq j) ^ ((1 : ℝ) / 3)) atTop (𝓝 0)) :=
  corollary_E1 n1SuperVirasoroProblem n1_lowerBoundInput n1_theoremC15UpperInput

/-- **Theorem `Σ₀` at `N = 1` super-Virasoro for the extremal measures, no hypothesis.** -/
theorem n1_sigmaZero_unconditional :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence n1SuperVirasoroProblem, S.c = cSeq ∧
        (∀ j, S.τ j = n1SuperVirasoroProblem.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Set.Iio (S.τ j + ε))) ∧
        SigmaZeroConclusion S.c S.τ S.μS :=
  sigmaZero_unconditional_prob n1SuperVirasoroProblem rfl n1_lowerBoundInput

/-- **Theorem `Σ` at `N = 1` super-Virasoro for the extremal measures, no hypothesis.** -/
theorem n1_sigma_unconditional :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence n1SuperVirasoroProblem, S.c = cSeq ∧
        (∀ j, S.τ j = n1SuperVirasoroProblem.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Iio (S.τ j + ε))) ∧
        SigmaConclusion S.μS :=
  sigma_unconditional_prob n1SuperVirasoroProblem rfl n1_lowerBoundInput

/-- **The vacuum step of Lemma `U*` at `N = 1` super-Virasoro** (`rampedVacuum_prob`). -/
theorem n1_rampedVacuum (CI Cmid : ℝ) (hCI : 1 ≤ CI) (hCmid : 1 ≤ Cmid) :
    ∃ M0 : ℝ, 0 < M0 ∧ ∀ P : Ramped.RampedParams, P.CI = CI → P.Cmid = Cmid → P.M0 = M0 →
      ∀ᶠ c' : ℝ in atTop, 0 < n1SuperVirasoroProblem.gVac (c' / 12)
        (pairOdd (combProfile c' (Ramped.rampedComb P (Ramped.rampedD P c') c'))
          (hankelTransform 1 (combProfile c' (Ramped.rampedComb P (Ramped.rampedD P c') c')))) :=
  Ramped.rampedVacuum_prob n1SuperVirasoroProblem rfl CI Cmid hCI hCmid

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.n1_designPropertyP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n1_designPropertyP

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.n1_thresholdUpperLittleO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n1_thresholdUpperLittleO

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.n1_theoremC15UpperInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n1_theoremC15UpperInput

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.n1_corollary_E1_littleO_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n1_corollary_E1_littleO_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.n1_corollary_E1_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n1_corollary_E1_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.n1_sigmaZero_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n1_sigmaZero_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.n1_sigma_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n1_sigma_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.n1_rampedVacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n1_rampedVacuum

end FormalResearch.ModularBootstrap.Upper.Assembly
