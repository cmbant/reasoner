module

public import FormalResearch.CohnElkies.ResolventAverage
public import FormalResearch.CohnElkies.FourierL1Interp
public import FormalResearch.CohnElkies.CardinalTruncation
public import FormalResearch.CohnElkies.ClosedResolvent

/-!
# Cohn–Elkies elementary lemmas (umbrella)

Elementary lemmas from the Cohn–Elkies / CFT modular-bootstrap material, formalised in Mathlib and the Airy library
(queue rows CEQ18, CEQ19, CEQ20, CEQ22 of `CFT/modular_bootstrap/notes/CE_MISSING_QUEUE.md`):

* `FormalResearch.CohnElkies.ResolventAverage`: the scalar identity (CR.18), product of two resolvent factors as an
  average of squared resolvents.
* `FormalResearch.CohnElkies.FourierL1Interp`: `∫|f̂| ≤ 2π (‖g‖₂‖g'‖₂)^{1/2}` for Schwartz `g` (FG.3, PF.2).
* `FormalResearch.CohnElkies.CardinalTruncation`: `‖H_N² − H²‖₁ ≤ (‖H_N‖₂ + ‖H‖₂)‖H_N − H‖₂` and its limit form (GT.0).
* `FormalResearch.CohnElkies.ClosedResolvent`: Theorem CR.1 (closed diagonal Airy resolvent, eq. CR.2, with the Riccati
  equation, CR.4 and the diagonal derivative step, CR.3 and the removable case `z = a`), from the library's
  Mittag-Leffler expansion of `Ai'/Ai`; no hypothesis beyond the displayed ones.

This umbrella is deliberately not imported by `FormalResearch.lean`.
-/
