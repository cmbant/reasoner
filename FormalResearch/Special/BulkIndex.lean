module

public import FormalResearch.Special.BulkIndexPhase
public import FormalResearch.Special.BulkIndexCount
public import FormalResearch.Special.BulkIndexSteps
public import FormalResearch.Special.BulkIndexHahn
public import FormalResearch.Special.BulkIndexZero
public import FormalResearch.Special.BulkIndexRight

/-!
# Bulk index of the physical `3j` chain: umbrella

* `BulkIndexPhase`, `BulkIndexCount`: the sign changes of a sequence in amplitude-phase form equal the drop of `⌊θ/π + 1/2⌋`
  (`bix_count`), and the composition with a right-end count and a total node count (`bix_count_right`, `bix_count_left`).
* `BulkIndexSteps`: phase steps of the Hahn phase (`bix_phase_step`).
* `BulkIndexHahn`: step (i), exactly one node per Bohr-Sommerfeld window in the bulk (`bix_hahn_count`).
* `BulkIndexZero`: the conditional zero index (`bix_hahn_zero_index`, `bix_hahn_bs_index`) under the explicit right-end count
  `BixRightCount`.
* `BulkIndexRight`: no nodes beyond the turning point (`bix_hahn_tail`, sign constancy of the recessive tail), and the reduction of
  `BixRightCount` to the node count of the Airy window (`bix_rightcount_of_window`).

**Not formalised:** the node count of the Airy window (the bonds between the bulk site `i_R` and the first site beyond `q_*`), the left edge `q → 0`, `τ = -1`, the half-integer lattice, and the Racah chains.
-/
