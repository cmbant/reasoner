module

public import FormalResearch.Special.RacahWindowGeom
public import FormalResearch.Special.RacahWindowSetup
public import FormalResearch.Special.RacahWindowChain
public import FormalResearch.Special.RacahWindowBulk
public import FormalResearch.Special.RacahWindowTail
public import FormalResearch.Special.RacahWindowIndex

/-!
# Racah window (umbrella)

Zero counting of the physical integer `6j` chain (`τ = +1`), the Racah counterpart of the `3j` modules `BulkWindow*`:

* `RacahWindowGeom`: `RwGeo`, the phase `Φ`, `0 < u < 1`, phase steps;
* `RacahWindowSetup`: `RwnSetup.count`, the node count of an Airy window for general centred Racah data;
* `RacahWindowChain`: `rwn_window_of_out` (any family with a `BkOut` window), `rwn_racah_window`;
* `RacahWindowBulk`: `rwn_bulk_count_of_form`, `rwn_racah_bulk`;
* `RacahWindowTail`: `rw_last_ne_zero`, `rwn_racah_tail` (no node beyond the turn);
* `RacahWindowIndex`: **`racah_chain_window_count`**, **`bix_racah_rightcount`** (the Bohr-Sommerfeld integer of `racah_chain_bulk_zeros` is the number of nodes at or to the right of the site,
  threshold `1/2 < |cos θ|`).

**Claim class: proved.**  **Not formalised:** `τ = -1`, the half-integer lattice, the total node count (zero index from the left), `kmin = 0`.
-/
