# QI-D nested all-rank lower witness — 2026-09-09

Source authority was re-audited against `cmbant/QIprojects:main` at `d9c4c3f4f0fd948daaefe186394dc3921c15dafe`.

The source theorem is recorded in:

- `QI-D/notes/HADAMARD_NESTED_DS_ALL_N.md`;
- `QI-D/code/verify_hadamard_nested_ds_all_n.py`;
- `QI-D/verification/verify_hadamard_nested_ds_all_n.txt`.

## Lean scope

The new module is:

`FormalResearch.QID.NestedLowerWitness`.

For rank `n=k+4`, Lean defines a canonical block index `Fin k ⊕ Fin 4`, the full nested exceptional normal `N_n`, and the block witness

`A_n = I_k direct_sum A_*`,

where `A_*` is the exact D4 witness already formalized in `D4DoublyStochasticCertificate`.

Lean proves:

- the block index has cardinality `k+4`;
- the D4 core normal is exactly the source integer matrix `N_4=4F`;
- `<N_4,A_*>=14/3`;
- the full block-diagonal Frobenius reduction;
- `<N_{k+4},A_{k+4}> = k+14/3 = (k+4)+2/3` for every `k`;
- an explicit bridge theorem combining the exact pairing with externally supplied membership in an abstract `DS` predicate.

This is real all-rank matrix structure, not merely the scalar simplification `k+14/3=(k+4)+2/3`.

## Claim boundary

The source proves `A_n in DS(W(D_n))` by a generalized-Birkhoff nesting lemma. That semantic DS-nesting theorem is not yet represented internally in this module. The Lean theorem therefore keeps `DS (A_n)` as an explicit bridge input rather than silently claiming the whole generalized-Birkhoff layer.

The all-rank upper bound from the source's positive rank-one decomposition is also outside this module and remains a separate future target.

## Validation

Module-only validation head `623587c85de371bd0970ab76a87f27670e5ef76d`, GitHub Actions run `34378369462`, passed placeholder rejection and `lake build FormalResearch.QID.NestedLowerWitness`.

The module has now been imported into `FormalResearch.lean`; a full aggregate gate on the promoted branch is required before merge.