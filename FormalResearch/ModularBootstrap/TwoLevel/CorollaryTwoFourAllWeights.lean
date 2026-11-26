module

public import FormalResearch.ModularBootstrap.TwoLevel.CorollaryTwoFour
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpFinal

/-!
# Corollary 2.4 at every weight, unconditionally (`virasoro_two_level.tex`, `gt:2.4`)

`corollary_two_four_of_upper` with `TheoremC15UpperInput prob` discharged at every weight by
`Upper.Ramped.theoremC15UpperInput_probW` (Lemma `U*(w)`, `fw:Ustar`); `corollary_two_four` is the case `prob.w = 1`.

All results are proved unconditionally.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Duality FormalResearch.ModularBootstrap.FixedWeight
  FormalResearch.ModularBootstrap.TipFront

/-- **Corollary 2.4, unconditional at every fixed weight `(w, Q)`** (`gt:2.4`(a) at `w > 1`). -/
theorem corollary_two_four_all (prob : FixedWeightProblem) {A₁ A₂ : ℝ} (hA₁ : A₁ < Aopt)
    (hA₂ : A₂ < A2star A₁) :
    ∀ᶠ c' : ℝ in atTop, ∃ meas : AdmissibleCrossingMeasure prob (c' / 12),
      meas.ν ({levelTime A₁ c'} ∪ Ici (levelTime A₂ c'))ᶜ = 0 ∧ 0 < meas.ν {levelTime A₁ c'} ∧
      Integrable (wStar (c' / 12) (1 / 2)) meas.ν ∧
      ∫ t, wStar (c' / 12) (1 / 2) t ∂meas.ν ≤ dualC0 prob (c' / 12) (1 / 2) :=
  corollary_two_four_of_upper prob (Upper.Ramped.theoremC15UpperInput_probW prob) hA₁ hA₂

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.corollary_two_four_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corollary_two_four_all

end FormalResearch.ModularBootstrap.TwoLevel
