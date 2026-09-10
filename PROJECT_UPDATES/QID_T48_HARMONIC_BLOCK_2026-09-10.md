# QI-D T48 harmonic-block Lean status — 2026-09-10

## Source authority

Research/certificate authority is `cmbant/QIprojects:main`.

The implementation was audited against QIprojects `6080f36ddd7a3c85015416b793e0562caf685e5a` and re-audited through current source head `1835b62a5ea6577c0ca685101276419cab04e671`. The 23-commit delta between those pins contains no changes to the T48 source files used here.

Canonical source:

- `QI-D/code/certify_E6_F4_endpoint_locus_reduction.py`;
- `QI-D/notes/T48_REPORT.md`.

The exact source statement formalized is the one-sector harmonic factorization with

`Z_s=[K_s,iP_s]`,

`B_j=(1/2) Z_{L,j}^* Z_{R,j}`.

## Lean content

Module:

`FormalResearch/QID/E6F4HarmonicBlockFactorization.lean`.

It proves abstractly for finite complex matrices:

1. the exact four-block expansion of `Z_L^* Z_R`;
2. the source factorization `B=(1/2) Z_L^* Z_R`;
3. positive semidefiniteness of the same-side Gram matrix `Z^* Z`.

Exact module blob:

`16be62fa3115b09f64261a58e77abf0a740974f5`.

Exact aggregate-import blob:

`70f4a73100f02e3aad3be8ddd18bc931085024d2`.

## Verification

Exact promoted Lean tree:

`257422bb2796d8a1bae6d139a32fc53bf2153979`.

GitHub Actions run:

`34470566235`.

That run passed:

1. rejection of `sorry` / `admit`;
2. `lake build FormalResearch.QID.E6F4HarmonicBlockFactorization`;
3. full `lake build FormalResearch`.

The temporary validation workflow was removed after this run. No Lean theorem/module or `FormalResearch.lean` bytes were changed by cleanup.

## Scope boundary

This is the exact harmonic-block algebra only. It does not formalize the full E6 restricted-root enumeration, identify the three multiplicity-eight triality modules `8_v,8_s,8_c`, prove the T48 PSD/rank outer locus exact, derive common-F4/triality compatibility for genuine interior endpoints, establish the T33 quartic on genuine endpoints, or prove compact-E6 simultaneous Weyl convexity.

T49 remains source-side research and is not converted into a Lean completion theorem by this result.
