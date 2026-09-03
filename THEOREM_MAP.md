# Theorem map and trust boundary

## Status vocabulary

- `LEAN-CHECKED`: compiled by Lean/mathlib CI with no `sorry` in the theorem.
- `FORMALIZED-UNCOMPILED`: Lean source exists but has not passed a kernel build.
- `SPEC`: paper/source statement recorded, formal proof not yet written.
- `EXTERNAL`: intentionally relies on a substantial theorem not currently formalized here.

## QI-C: finite-field certificate lift

Source claim: exact computational statements are over F_101; a nonzero full-rank integer minor modulo 101 is a nonzero characteristic-zero integer minor.

Lean file: `FormalResearch/Certificates/FiniteField.lean`.

Current formal core: `int_ne_zero_of_zmod_ne_zero`.

Boundary: this does not yet verify that the large qutrit matrices emitted by the Python generators are the Jacobians claimed in the paper, nor the reported large ranks. Those require certificate extraction plus a formally specified matrix generator.

## QI-A: four-qubit three-copy chirality block

Source claim: on the unique 3-dimensional noncommutative multiplicity block, the Hermitian chirality compression has eigenvalues -3/4, 0, 3/4.

After changing from the orthonormal paper basis back to the natural pairing-tensor basis, the matrix is similar to `(3 i / 8) K` with

```
K = [-1 -1 -2
      1  1  2
      1 -1  0].
```

Lean file: `FormalResearch/QIA/FourQubitMatrix.lean`.

Current formal core: `K^3 = -4 K` and `K != 0`.

Still to formalize: the exact basis-change relation to the paper's matrix A0, enough rank/nondegeneracy to identify all three roots, and the exact state expectation giving the discrimination value.

## QI-D: explicit D5 exceptional facet

Source claim: the displayed integer numerator N5 has matrix rank 4; exact Weyl-group enumeration gives support 5 and affine active-vertex rank 24, so N5/5 is a facet normal of conv W(D5).

Lean file: `FormalResearch/QID/D5RankWitness.lean`.

Current formal core verifies `det N5 = 0` and a specific 4x4 minor has determinant 8. Together these certify matrix rank exactly four over characteristic zero once the standard rank/minor lemma is connected.

Still to formalize: signed-permutation enumeration, support bound, active-vertex affine rank, and then the all-Dn constructive induction.
