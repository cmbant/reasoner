module

public import FormalResearch.CohnElkies.ResolventAverage
public import FormalResearch.CohnElkies.FourierL1Interp
public import FormalResearch.CohnElkies.CardinalTruncation

/-!
# Cohn–Elkies elementary lemmas (umbrella)

Three elementary lemmas from the Cohn–Elkies / CFT modular-bootstrap material, formalised in Mathlib
(queue rows CEQ18, CEQ20, CEQ22 of `CFT/modular_bootstrap/notes/CE_MISSING_QUEUE.md`):

* `FormalResearch.CohnElkies.ResolventAverage`: the scalar identity (CR.18), product of two resolvent factors as an
  average of squared resolvents.
* `FormalResearch.CohnElkies.FourierL1Interp`: `∫|f̂| ≤ 2π (‖g‖₂‖g'‖₂)^{1/2}` for Schwartz `g` (FG.3, PF.2).
* `FormalResearch.CohnElkies.CardinalTruncation`: `‖H_N² − H²‖₁ ≤ (‖H_N‖₂ + ‖H‖₂)‖H_N − H‖₂` and its limit form (GT.0).

This umbrella is deliberately not imported by `FormalResearch.lean`.
-/
