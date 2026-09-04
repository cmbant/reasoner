# Theorem map and trust boundary

> **Live-status warning (2026-09-04).** This file began as an early theorem map and is not a complete current index of `FormalResearch.lean`. Treat the code plus exact-head CI as authoritative. Author-facing paper/genealogy corrections are maintained under `PROJECT_UPDATES/`. A workflow-level green result is insufficient when a compile step is marked `continue-on-error`; inspect the relevant exact-head step itself.

## Status vocabulary

- `LEAN-CHECKED`: exact imported source compiled by Lean/mathlib CI with no `sorry`/`admit`, and the relevant exact-head build/aggregate step passed.
- `FORMALIZED-UNCOMPILED`: Lean source exists but has not passed the relevant kernel build.
- `SPEC`: paper/source statement recorded, formal proof not yet written.
- `EXTERNAL`: intentionally relies on a substantial theorem/input not currently formalized here.

Compilation is not by itself a specification audit: a checked theorem may still be narrower than, conditional relative to, or semantically different from the current paper claim.

## AUX-BV: quartic charge-gap algebra

Current source archive: `Blaschke_Virasoro_Handoff_2026-09-03_v13.zip`.

Paper correction found during formal audit: the sign-sensitive quartic variable used in the factorization is

`U = (Re p)^2`, `V = (Im p)^2`,

not the v13 prose identification `U = (Re s)^2`. The critical and numerator coordinates are related by

`Re p = 2 q (1+t)/(t(q+3)) Re s`,

`Im p = 2 q (1-t)/(t(3-q)) Im s`.

Lean file: `FormalResearch/Blaschke/QuarticChargeGapAlgebra.lean`.

Current formal core in that module:

- exact `epsilon`, `L_-`, `L_+`, `F1`, `F2`, `F3` polynomial definitions;
- corrected denominator-free critical conic in `U=(Re p)^2`, `V=(Im p)^2`;
- exact `L_±` epsilon identities and positivity from `0<t<1`, `epsilon>=0`;
- arithmetic identity behind the Bessel/Gram scalar reduction;
- `F1<=0`, Schur-ellipse `F2>0`, conic `F3>=0`;
- nonnegative factor-product certificate;
- exact squared-gap factorization;
- final unsquaring from the degree-four Gate-A energy input.

Trust boundary: the model-space Bessel inequality supplying `epsilon>=0`, the raw residue/Hilbert-metric construction of the charge singular values, and the raw-matrix-to-factorized-defect bridge are not formalized in this module. Do not describe the full analytic quartic theorem as Lean-checked solely from this algebra module.

Status at source creation: `FORMALIZED-UNCOMPILED`. Promote only after the exact source is imported by `FormalResearch.lean` and the exact-head dedicated/aggregate CI steps pass.

See `PROJECT_UPDATES/AUX-BV_2026-09-04.md` for the manuscript edits and proof-status recommendation.

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

This section is historical and incomplete relative to the much larger current QI-A aggregate; inspect `FormalResearch/QIA/` and exact-head CI for the live frontier.

## QI-D: explicit D5 exceptional facet

Source claim: the displayed integer numerator N5 has matrix rank 4; exact Weyl-group enumeration gives support 5 and affine active-vertex rank 24, so N5/5 is a facet normal of conv W(D5).

Lean starts at `FormalResearch/QID/D5RankWitness.lean` and now includes later enumeration, affine-rank, supporting-face, and full-facet certificate modules imported by the aggregate.

The old sentence that these later pieces were “still to formalize” is superseded. As always, inspect the exact modules and exact-head aggregate CI rather than relying on this historical summary.
