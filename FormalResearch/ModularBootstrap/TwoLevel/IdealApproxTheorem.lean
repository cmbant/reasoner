module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidity
public import FormalResearch.ModularBootstrap.TwoLevel.IdealApprox

/-!
# Theorem 2.6 from the two-simple-zero transfer alone (`virasoro_two_level.tex`, `gt:2.6`)

`TwoZeroIdealApprox` is proved (`twoZeroIdealApprox`), so `theorem_two_six` and `tendsto_atom_weight` have
`TwoSimpleZeroTransfer prob` (`ut:T2`) as their only hypothesis:

* `theorem_two_six_of_T2`: **Theorem 2.6** (`gt:2.6`): `μ_j → Σ_n δ_{z_n}/K(z_n, z_n)` vaguely along the whole sequence;
* `tendsto_atom_weight_of_T2`: the weight of the atom of `μ_j` at `s₁^{(j)}` tends to `1/K(u₁, u₁)`.

All results are proved unconditionally from `ut:T2`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.Upper.Rigidity

/-- **Theorem 2.6** (`gt:2.6`), conditional only on the two-simple-zero transfer `ut:T2`: the Cardy-normalised spectral
measures of a two-level sequence converge vaguely to the Clark measure `μ_α = Σ_n δ_{z_n}/K_n`,
`α = α(-A₁/c_*)`. -/
theorem theorem_two_six_of_T2 {prob : FixedWeightProblem} (hT : TwoSimpleZeroTransfer prob) {A₁ : ℝ}
    (hA : A₁ < Aopt) (S : TwoLevelSequence prob A₁) :
    IsVagueLimit atTop S.μ (clarkMeasure (clarkAngle (-A₁ / cStar))) :=
  theorem_two_six hT twoZeroIdealApprox hA S

/-- **Corollary of Theorem 2.6**: the weight of the atom of `μ_j` at `s₁^{(j)} = u(t₁^{(j)})` tends to `1/K(u₁, u₁)`,
`K(u₁, u₁) = Ai'(u₁)² - u₁ Ai(u₁)²`, conditional only on `ut:T2`. -/
theorem tendsto_atom_weight_of_T2 {prob : FixedWeightProblem} (hT : TwoSimpleZeroTransfer prob) {A₁ : ℝ}
    (hA : A₁ < Aopt) (S : TwoLevelSequence prob A₁) :
    Tendsto (fun j => (S.μ j {uAiry (S.c j) (S.t₁ j)}).toReal) atTop
      (𝓝 (clarkKernel (clarkAngle (-A₁ / cStar)) 1)⁻¹) :=
  tendsto_atom_weight hT twoZeroIdealApprox hA S

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_two_six_of_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_two_six_of_T2

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tendsto_atom_weight_of_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_atom_weight_of_T2

end FormalResearch.ModularBootstrap.TwoLevel
