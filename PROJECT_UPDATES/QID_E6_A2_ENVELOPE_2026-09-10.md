# QI-D E6/F4 A2 envelope-to-quartic Lean status — 2026-09-10

## Source authority

Research/certificate authority is `cmbant/QIprojects:main`.

The Lean module was implemented from `QI-D/code/certify_E6_A2_phase_envelope.py` at source pin `acfb127df5cc5998fb91cd00ea6e5311d1462e39` and re-audited after QIprojects advanced to `82bfb80d717c4ab0282b4e1573db24c915ac3aad`. The intervening source delta does not change `certify_E6_A2_phase_envelope.py` or `certify_E6_F4_endpoint_locus_reduction.py`, so the exact algebraic source match remains valid.

## Lean result

Module: `FormalResearch/QID/E6A2PhaseEnvelopeQuartic.lean`.

Exact promoted Lean-content verification head:

`8108be5de50e40a6daa05b6004d63a87c388ba95`

GitHub Actions promotion run:

`34406631515`

The run passed:

1. placeholder rejection;
2. `lake build FormalResearch.QID.E6A2PhaseEnvelopeQuartic`;
3. full `lake build FormalResearch`.

Status: **formalized, module-green, aggregate-green**.

## What Lean proves

Lean checks the exact rational algebraic layer of the T33 E6/F4 `A2` phase reduction:

- determinant `3` and the displayed rational inverse of the `A2` phase map;
- the tangent-half-angle denominator and cleared numerator identities;
- exact equality between the finite-`t` unit-circle defect and the cleared quartic after multiplication by `(1+t^2)^2`;
- equivalence of finite-`t` defect nonnegativity and quartic nonnegativity because the denominator is strictly positive;
- the exact quartic coefficient expansion;
- equality of the leading coefficient with the separate `t = infinity` defect;
- the source equality regression and its global finite-`t` nonnegativity;
- the source lowered-target failure regression.

## Scope boundary

This is **not** a Lean proof of compact-E6 simultaneous Weyl convexity.

Still external/source-side are:

- the analytic one-phase maximization `max_v Re(z v)=|z|` used to eliminate one phase;
- the identification of `(c0,a,b,c)` from genuine compact-F4 endpoint data;
- the claim that every genuine compact-F4 endpoint tuple satisfies the resulting quartic positivity condition;
- the T48/T49 triality-compatible interior endpoint-locus theorem.

T48 has since reached an exact reduced-locus stop condition on the source side: Spin(8) centralizer/triality blocks and the four exact zero-sector boundary certificates are established, while the interior triality-compatibility problem remains open and is owned by T49.
