module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCExact
public import FormalResearch.JacobiEigenvectors.Charts.PCSmooth
public import FormalResearch.JacobiEigenvectors.Charts.PCPhase

/-!
# Paper J, Layer 4: `ParabolicCylinderFacts` for the actual `pcU, pcV` from the envelope facts alone

`ParabolicCylinderFacts.ofEnvelope`: `PCEnvelopeFacts pcU pcV cPC CPC -> ParabolicCylinderFacts pcU pcV cPC CPC`.  The other three parts are proved:
`pcExactFacts` (`PCExact.lean`: DLMF 12.2.2, 12.2.10, 12.2.15-16, 12.8.2-3, 12.8.6-7), `pcSmoothFacts` (`PCSmooth.lean`: slice smoothness, joint continuity),
`pcPhaseFact` (`PCPhase.lean`: DLMF 12.10.18 on the lattice `mu^2 = 2n+1`).  So for a `ChartInputs F K Kidx t0 m q pcU pcV cPC CPC`, its field `pc` is
`ParabolicCylinderFacts.ofEnvelope he` for a single remaining special-function premise `he : PCEnvelopeFacts pcU pcV cPC CPC` (Olver's envelope estimates).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

/-- **`ParabolicCylinderFacts` for the actual functions needs only the envelope facts.** -/
theorem ParabolicCylinderFacts.ofEnvelope {cPC CPC : ℝ} (he : PCEnvelopeFacts pcU pcV cPC CPC) :
    ParabolicCylinderFacts pcU pcV cPC CPC :=
  { pcExactFacts, pcSmoothFacts, pcPhaseFact, he with }

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinderFacts.ofEnvelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ParabolicCylinderFacts.ofEnvelope

end FormalResearch.JacobiEigenvectors.Charts
