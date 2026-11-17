module

public import FormalResearch.Special.BulkWindowAiry
public import FormalResearch.Special.BulkWindowZeros
public import FormalResearch.Special.BulkWindowCount
public import FormalResearch.Special.BulkWindowChart
public import FormalResearch.Special.BulkWindowRk
public import FormalResearch.Special.BulkWindowHahn
public import FormalResearch.Special.BulkWindowIndex

/-!
# Bulk window of the physical `3j` chain: umbrella

* `BulkWindowAiry`: local facts on `Ai` (second-order Taylor, the energy `Ai'^2 - x Ai^2`, `bwn_nz`: near-zero sites are isolated with neighbours of opposite sign).
* `BulkWindowZeros`: the zero count of `Ai` (`bwn_sign`, `bwn_count_step`, `bwn_count_floor`: `#zeros in (-v, 0] = ⌊(2/3) v^{3/2}/π + 1/4⌋` at non-resonant `v`).
* `BulkWindowCount`: abstract node count of a noisy lattice sampling of a function with counted sign changes (`BwnWin.count`).
* `BulkWindowChart`, `BulkWindowRk`: chart arithmetic and the node count of the Airy window (`BwnSetup.count`).
* `BulkWindowHahn`: the node count of the Airy window of the `3j` chain (`bwn_hahn_window`).
* `BulkWindowIndex`: junction with the bulk count and the tail: `hahn_chain_window_count`, `bix_hahn_rightcount`, `hahn_chain_zero_index`, `hahn_chain_bs_index`
  (the zero index of the integer `3j` chain, unconditional).
-/
