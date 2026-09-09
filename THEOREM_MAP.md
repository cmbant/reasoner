# Theorem map and trust boundary

> **Live status — 2026-09-09.** This file is a high-level trust map, not a complete index of every imported module. The authoritative maintained Lean branch is `formal-research-lean`; exact-head hard Lake builds and theorem-local source audits control promotion.
>
> Historical workflow-level green badges from before the repaired hard Lake gates are not verification evidence. Current promoted claims below cite exact module/aggregate runs recorded in `PROJECT_UPDATES/HANDOFF_2026-09-09.md` and QIprojects `docs/lean_status.md`.

## Current maintained baseline

Maintained reasoner head after PR #14:

`29c4d5946f427dfdfd5b9adccca242f0118f6742`.

Latest promoted Lean source verification head:

`df4466a9e5b773db105bb1fcbd14945129d2a33b`.

GitHub Actions run `34390385283` passed placeholder rejection, the three QI-D nested-upper modules and full `lake build FormalResearch` on that exact source tree before merge.

## Status vocabulary

- `FORMALIZED`: Lean source exists.
- `MODULE-GREEN`: the theorem-local hard Lake build passed at an exact source head.
- `AGGREGATE-GREEN`: full `lake build FormalResearch` passed at an exact source head containing the theorem.
- `MERGED`: reviewed source is on `formal-research-lean`.
- `EXTERNAL`: a named mathematical/source premise remains intentionally outside current Lean coverage.

Compilation is not by itself a specification audit. A checked theorem may be narrower than, conditional relative to, or semantically different from the surrounding source theorem.

## Blaschke quartic charge gap

Lean files:

- `FormalResearch/Blaschke/QuarticChargeGapAlgebra.lean`;
- `FormalResearch/Blaschke/QuarticChargeGapReconstructionBridge.lean`.

Current formal core includes the corrected quartic conic/factor algebra, sign chain, squared-gap defect, exact scalar reconstruction prefactor and final unsquaring to the `1/2` gap under explicit reconstruction/analytic hypotheses.

PR #8 hard verification: head `1dc24e93c1483782dd80b162c9b48cd26707fc41`, run `34336956345`, module and full aggregate green; merged.

Status: **FORMALIZED / MODULE-GREEN / AGGREGATE-GREEN / MERGED** for the conditional scalar bridge.

External boundary: raw CAS reconstruction derivation, Bessel/Gram input, Schur-domain theorem, Möbius normalization, residue/Hilbert-metric construction and confluent continuity. Do not describe the complete analytic quartic proof as internally Lean-derived.

## QI-A

The maintained aggregate contains the older four-qubit/chirality/three-copy infrastructure plus the new exact certificate layers:

### Three-copy local-Schur overhead

Lean file: `FormalResearch/QIA/ThreeCopyLocalSchurOverhead.lean`.

PR #9 verification head `2e15ff34467c5de1a2432c6d6bd7c5c7ddad19ed`, run `34339736666`, module and aggregate green; merged.

Lean proves the finite `S3` character identities `6K=L`, `6K=L+3`, and `6K=L+2` in the source regimes.

### Information hierarchy coefficients

Lean file: `FormalResearch/QIA/InformationHierarchyCoefficients.lean`.

PR #10 verification head `3591192788ae917bb43c1f8e7102e95270258efb`, run `34347204321`, aggregate green; merged.

Lean proves the exact scalar coefficient/exponent ordering including `Q_meas,full=21/22` and `xi_meas=log(22/21)`.

External QI-A boundary: operational POVM/recovery/data-processing statements, T07 coding/query architecture, reversible coherent-width Schmidt-number/recovery lower bound and other manuscript-level theorems not represented by these scalar/character modules.

## QI-B

### Symmetric U(1) exponent gap

Lean file: `FormalResearch/QIB/U1InvariantExponentGap.lean`.

PR #11 verification head `297231d4be4780b1d091092a7d841bbbe62edb85`, run `34348733331`, aggregate green; merged.

Lean proves the exact scalar factor-two exponent relation for the source family; the twirl/binomial/operational Chernoff derivation remains external.

### B4 late source status

QIprojects T34 supplies an exact Fierz/Pluecker reformulation and an exact counterexample to a proposed stronger spectral route, but leaves the flagship B4 inequality/equality open. There is therefore no current Lean-completion claim for that flagship. Any B4 formalization must match a proved local identity/certificate and must not promote the open conjecture.

## QI-C

The maintained aggregate contains the finite-field, Gaussian and all-`L` qubit-tail chain, including:

- `FormalResearch/QIC/QubitTailDeterminants.lean`;
- `FormalResearch/QIC/GaussianNonvanishing.lean`;
- `FormalResearch/QIC/QubitTailAllLNonvanishing.lean`;
- Endpoint14/Gaussian endpoint reconstruction modules.

The canonical QI-C all-`m` tail certificate has remained source-stable through the latest audit, and these modules compile in the current aggregate.

Trust boundary: this is the determinant/nonvanishing/certificate layer. The full Jacobian/orbit-identifiability statement behind `d_loc=3` is a separate semantic theorem and must not be inferred merely from aggregate compilation.

## QI-D

### D4 finite doubly-stochastic separation certificate

Lean files:

- `FormalResearch/QID/D4DoublyStochasticCertificate.lean`;
- `FormalResearch/QID/D4DoublyStochasticDualCertificate.lean`.

PR #12 clean verification head `8a95d5ba7fb0b200dfbfb2efb4c97e3710ead8be`, run `34374566836`, both modules and full aggregate green; merged.

Internally checked finite data include `|W(D4)|=192`, orbit sizes `(8,24,8,8)`, witness value `7/6`, Weyl support, exactly `2304` finite coweight constraints with zero violations, and the exact 14-term rational dual.

External boundary: the finite-coweight characterization of semantic `DS(W(D4))` membership and the surrounding generalized-Birkhoff/convex-geometric theorem.

### Nested all-rank lower witness

Lean file: `FormalResearch/QID/NestedLowerWitness.lean`.

PR #13 promoted head `a8d883584eb235fa2f1c4af0c01ec309cedfc0ac`, run `34378799353`, module and aggregate green; merged.

For `n=k+4`, Lean defines the actual block witness and proves `<N_n,A_n>=n+2/3`.

External boundary: generalized-Birkhoff nesting / semantic `A_n in DS(W(D_n))`.

### Nested all-rank upper decomposition

Lean files:

- `FormalResearch/QID/NestedUpperAtomicCore.lean`;
- `FormalResearch/QID/NestedUpperRankOneSums.lean`;
- `FormalResearch/QID/NestedUpperSupportBridge.lean`.

PR #14 module head `15ce8208c11f73b77fc2adbc4ad859f958cd031a`, run `34389943505`; promoted head `df4466a9e5b773db105bb1fcbd14945129d2a33b`, run `34390385283`; all modules and full aggregate green; merged.

Lean proves the exact source identity

`6N_n = 2R_n + 2C_n + sum_a s_a t_a^T`,

its explicit individual row/column rank-one expansion, the four opposite-parity sign atoms and the implication `<N_n,T><=n+2/3` from the individual sharp support bounds.

External boundary: the arbitrary-real type-D rearrangement / determinant-constrained Procrustes theorem supplying those sharp per-atom bounds. Together with the lower-witness boundary above, this is why the complete semantic `DS(W(D_n))` extremal theorem is not yet wholly internal Lean.

### D5 certificate chain

The maintained aggregate imports the D5 rank, enumeration, affine-rank, supporting-facet and full-facet certificate modules. The old theorem-map text saying these pieces were still pending is obsolete. For theorem semantics, consult the source-local QI-D certificate and module statements; aggregate compilation alone does not upgrade their external convex-geometric premises.

## Gaudin, Racah and bridge modules

The maintained aggregate also imports the current Gaudin metric/rank chain, Racah Weyl-cell modules and B2/Blaschke bridge modules. They are compiled as part of the current aggregate. This high-level map does not attempt to restate every theorem in those families; use the Lean source and theorem-local project updates for exact scope.

## Next source-authorized finite targets

At the current handoff, the cleanest exact candidates are:

1. QI-D T33 exceptional F4 facet representative certificate;
2. QI-D T33 E6/F4 A2 envelope-to-quartic reduction;
3. QI-A T07 finite coding/guessing lemmas with faithful operational hypotheses;
4. the general type-D support/Procrustes bridge if sufficient real-linear-algebra infrastructure is developed.

QI-D T48 and the QI-B B4 flagship remain open research problems, not current theorem-completion targets.
