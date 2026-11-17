module

public import FormalResearch.Special.BulkIndexPhase
public import FormalResearch.Special.BulkIndexCount
public import FormalResearch.Special.BulkIndexSteps
public import FormalResearch.Special.BulkIndexHahn
public import FormalResearch.Special.BulkIndexZero

/-!
# Bulk index of the physical `3j` chain: umbrella

* `BulkIndexPhase`, `BulkIndexCount`: the sign changes of a sequence in amplitude-phase form equal the drop of `⌊θ/π + 1/2⌋`
  (`bix_count`), and the composition with a right-end count and a total node count (`bix_count_right`, `bix_count_left`).
* `BulkIndexSteps`: phase steps of the Hahn phase (`bix_phase_step`).
* `BulkIndexHahn`: step (i), exactly one node per Bohr-Sommerfeld window in the bulk (`bix_hahn_count`).
* `BulkIndexZero`: the conditional zero index (`bix_hahn_zero_index`, `bix_hahn_bs_index`) under the explicit right-end count
  `BixRightCount`.

**Not formalised:** the right-end count `BixRightCount` itself (nodes of the chain in `[b/h, N)`: the Airy window around `q_*` and the
absence of nodes beyond `q_*`), the left edge `q → 0`, `τ = -1`, the half-integer lattice, and the Racah chains.
-/
