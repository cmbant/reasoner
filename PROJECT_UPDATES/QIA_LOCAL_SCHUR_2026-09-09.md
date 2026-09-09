# QI-A three-copy local-Schur Lean update — 2026-09-09

## Source authority

Audited against `cmbant/QIprojects:main` at

`a32a35809edd12b7d7cb7c23b332edad36efa5bc`.

The exact source certificate is

`QI-A/scripts/verify_local_schur_d3_overhead.py`

with committed output

`QI-A/verification/verify_local_schur_d3_overhead.txt`.

The source character sums are `(3,1,0)` for a qubit site and `(4,0,1)` for a local dimension at least three. If `r` of `m` parties have local dimension at least three, the locally retained dimension is

`L = 4^r 3^(m-r)`.

The source conclusions are:

- `0 < r < m`: `L/K = 6` exactly;
- `r = 0`: `L/K = 6/(1+3^(1-m))`;
- `r = m`: `L/K = 6/(1+2*4^(-m))`.

## Lean module

Added:

`FormalResearch/QIA/ThreeCopyLocalSchurOverhead.lean`.

It reuses the existing `S3` character infrastructure and proves the exact denominator-free character identities:

- mixed architecture: `6 K = L`;
- all-qubit endpoint: `6 K = L + 3`;
- all-high-dimensional endpoint: `6 K = L + 2`.

The integer character numerators are proved first, followed by the rational memory identities.

This is intentionally a finite character-algebra formalization. It does not by itself formalize the full Schur-Weyl operational interpretation of the retained register or the general arbitrary-copy heterogeneous memory theorem.

## Exact Lean validation

Exact verified Lean source head:

`2e15ff34467c5de1a2432c6d6bd7c5c7ddad19ed`.

GitHub Actions run:

`34339736666`.

On that exact head the run passed:

1. placeholder rejection;
2. `lake build FormalResearch.QIA.ThreeCopyLocalSchurOverhead`;
3. `lake build FormalResearch`.

Therefore the new module is **MODULE-GREEN** and the exact tested source tree is **AGGREGATE-GREEN**.

A later branch commit removes the temporary validation workflow and adds this status note; no `.lean` source changed after the verified head.

## QI-A/QI-C boundary

The live QI-A paper now contains several additional strengthened results. In particular, the exact reversible coherent-width theorem `w_min=max_alpha dim M_alpha` has a recovery/Schmidt-number lower-bound argument and should be treated as a separate, higher-level formalization problem rather than as arithmetic fallout from this module.

The QI-C restructuring does not change the canonical all-`m` tail source used by the existing Endpoint14 chain: `QI-C/code/verify_qubit_ci_tail_proof.py` remains Git blob `e5d44a1733ce0520bebd37a9172348b1476f7463`.
