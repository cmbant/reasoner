module

public import FormalResearch.ModularBootstrap.TwoLevel.IdealApproxTheorem
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransferProof

/-!
# Theorem 2.6 at weight one, unconditional

`virasoro_two_level.tex`, Theorem 2.6 (`gt:2.6`): for every weight-one problem the Cardy-normalised window
measures of two-level crossing sequences converge vaguely to the Clark measure `Σ_n δ_{z_n}/K_n`.  Theorem T2 at
weight one (`twoSimpleZeroTransfer_of_w1`) discharges the only hypothesis of `theorem_two_six_of_T2`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Rigidity

/-- **Theorem 2.6** (`gt:2.6`) at every weight-one problem, unconditional. -/
theorem theorem_two_six_w1_unconditional {prob : FixedWeightProblem} (hw : prob.w = 1) {A₁ : ℝ}
    (hA : A₁ < Aopt) (S : TwoLevelSequence prob A₁) :
    IsVagueLimit atTop S.μ (clarkMeasure (clarkAngle (-A₁ / cStar))) :=
  theorem_two_six_of_T2 (twoSimpleZeroTransfer_of_w1 prob hw) hA S

end FormalResearch.ModularBootstrap.TwoLevel

/--
info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_two_six_w1_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.theorem_two_six_w1_unconditional
