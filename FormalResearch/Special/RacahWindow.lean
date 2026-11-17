module

public import FormalResearch.Special.RacahWindowGeom
public import FormalResearch.Special.RacahWindowSetup
public import FormalResearch.Special.RacahWindowChain
public import FormalResearch.Special.RacahWindowBulk
public import FormalResearch.Special.RacahWindowTail
public import FormalResearch.Special.RacahWindowIndex
public import FormalResearch.Special.RacahWindowPhys
public import FormalResearch.Special.RacahWindowNodes
public import FormalResearch.Special.RacahWindowNodesNeg
public import FormalResearch.Special.RacahWindowZero
public import FormalResearch.Special.RacahWindowZeroNeg

/-!
# Racah window: zero counting of the integer `6j` chains (`τ = ±1`)

Umbrella of the `RacahWindow*` modules: the Racah counterpart of `BulkWindow*` (`3j` chain).  The proof is written once for the data `RwData` (`τ = ±1`, sign twist `u`), then specialised.

* `RacahWindowGeom`, `RacahWindowSetup`: geometry of `hrU` (`RwGeo`) and the Airy window setup.
* `RacahWindowChain`: `RwData`, `rwn_racah_window` (window count).  `RacahWindowBulk`: `rwn_racah_bulk`.  `RacahWindowTail`: `rwn_racah_tail`.
* `RacahWindowIndex`: `rwn_chain_window_count`, `rwn_chain_rightcount` (literal threshold `1/2 < |cos θ|`).  `RacahWindowPhys`: `racah_chain_window_count`, `bix_racah_rightcount` (`τ = +1`),
  `racah_chain_window_count_neg`, `bix_racah_rightcount_neg` (`τ = -1`).
* `RacahWindowNodes`, `RacahWindowNodesNeg`: total node count `l`, resp. `D' - l`.  `RacahWindowZero`, `RacahWindowZeroNeg`: zero index from the left and Bohr-Sommerfeld index of a node bond.

**Not formalised:** the half-integer lattice (`racah6jYH`), `kmin = 0`, uniformity of `ε` in `(α, β, x, m, n)`, resonant sites `|cos θ| ≤ 1/2`.
-/
