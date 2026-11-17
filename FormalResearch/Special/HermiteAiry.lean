module

public import FormalResearch.Special.HermiteFunction
public import FormalResearch.Special.HermiteNorm
public import FormalResearch.Special.HermiteAiryDatum
public import FormalResearch.Special.HermiteAiryEdge

/-!
# Hermite functions and their Airy edge (umbrella module)

* `HermiteFunction`: orthonormal Hermite functions `hermitePhi`, exact recurrence, ladder relations, parity.
* `HermiteNorm`: `∫ φ_n² = 1`, polynomial sup bound `φ_n² ≤ 2n+2`.
* `HermiteAiryDatum`: the Hermite chain is an exact simple-turn datum (`DunDatum`), `hermite_row`, Langer data.
* `HermiteAiryEdge`: `hermite_airy_edge`, the Plancherel–Rotach Airy edge (relative error `O(1/n)`, `κ` unidentified).
-/

@[expose] public section
