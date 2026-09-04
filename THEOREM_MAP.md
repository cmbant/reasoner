# Theorem map and trust boundary

> **Live-status warning (2026-09-04).** This file began as an early theorem map and is not a complete current index of `FormalResearch.lean`. Treat the code plus exact-head CI as authoritative. Author-facing paper/genealogy corrections are maintained under `PROJECT_UPDATES/`.
>
> **CI correction:** historical workflow-level green badges are not sufficient verification evidence. A decoded-log audit found that the old workflow's direct `lake env lean ...` calls could fail with `unknown module prefix 'FormalResearch'`, while `continue-on-error` masked the failures; the old QI-B2 Krawtchouk diagnostic also had a genuine tactic failure. Earlier `LEAN-CHECKED` labels based only on those badges are provisionally withdrawn until re-certified by the repaired hard Lake build.

## Status vocabulary

- `LEAN-CHECKED`: exact imported source passed the placeholder scan and the relevant hard Lake module/library build at the exact head.
- `FORMALIZED-UNCOMPILED`: Lean source exists but has not passed the relevant hard kernel build.
- `SPEC`: paper/source statement recorded, formal proof not yet written.
- `EXTERNAL`: intentionally relies on a substantial theorem/input not currently formalized here.

Compilation is not by itself a specification audit: a checked theorem may still be narrower than, conditional relative to, or semantically different from the current paper claim.

## Current CI gate

The repaired trust path is:

1. reject `sorry`/`admit`;
2. hard-build the new AUX-BV module with Lake;
3. hard-build the `FormalResearch` library/aggregate with Lake;
4. use direct source invocations only as secondary diagnostics.

Do not infer `LEAN-CHECKED` from a workflow-level conclusion if the relevant hard build did not pass.

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

Current status: `FORMALIZED-UNCOMPILED`. The first CI attempt failed before theorem elaboration because the old direct-source invocation could not resolve project imports. Promote only after the repaired hard Lake module and aggregate builds pass at the exact head.

See `PROJECT_UPDATES/AUX-BV_2026-09-04.md` for the manuscript edits and proof-status recommendation.

## QI-C: finite-field certificate lift

Source claim: exact computational statements are over F_101; a nonzero full-rank integer minor modulo 101 is a nonzero characteristic-zero integer minor.

Lean file: `FormalResearch/Certificates/FiniteField.lean`.

Current formal core: `int_ne_zero_of_zmod_ne_zero`.

Boundary: this does not yet verify that the large qutrit matrices emitted by the Python generators are the Jacobians claimed in the paper, nor the reported large ranks. Those require certificate extraction plus a formally specified matrix generator.

Verification status: re-certification pending under the repaired hard aggregate build.

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

This section is historical and incomplete relative to the much larger current QI-A aggregate. Verification status is being re-certified under the repaired hard aggregate build.

## QI-B2: Krawtchouk diagnostic

The 2026-09-04 CI audit found a genuine current-source tactic failure in `FormalResearch/QIB2/KrawtchoukEigenvalue.lean` at the antidiagonal-to-range rewrite. This is a compatibility/proof-maintenance issue to repair before QI-B2 can be re-certified. It does not by itself falsify the manuscript's coefficient identity.

## QI-D: explicit D5 exceptional facet

Source claim: the displayed integer numerator N5 has matrix rank 4; exact Weyl-group enumeration gives support 5 and affine active-vertex rank 24, so N5/5 is a facet normal of conv W(D5).

Lean starts at `FormalResearch/QID/D5RankWitness.lean` and now includes later enumeration, affine-rank, supporting-face, and full-facet certificate modules imported by the aggregate.

The old sentence that these later pieces were “still to formalize” is superseded. Verification status is being re-certified under the repaired hard aggregate build; do not reuse the old workflow badge as proof of compilation.
