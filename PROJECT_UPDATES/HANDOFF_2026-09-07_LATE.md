# Formal research handoff — 2026-09-07 late update

This file supersedes only the restart/status portion of `PROJECT_UPDATES/HANDOFF_2026-09-07.md`. Keep the earlier handoff for the detailed source-audit and Endpoint14 history.

## Exact heads before this trigger commit

- Research/source authority: `cmbant/QIprojects:main`
  - `afe15bdbe01b1c8c7b194695ae2991af49210bfd`
  - latest commit: `Log-reproduction audit before the main merge: two defects fixed`
- Lean canonical branch after PR #4:
  - `cmbant/reasoner:formal-research-lean`
  - `9d745a4d7eb8d3a0d1b1be779082270e63300bdd`

Since the prior source pin `eae4a5a48aa2b2e29303d18352a508efe3f35a38`, QIprojects advanced 103 commits. For this aggregate-maintenance lane, the compare contains no Gaudin changes and only one Blaschke path change, `Blaschke/verification/t09_transverse_counterfamily_exact.txt`; it does not revise the retained Walsh/Wronskian formal target.

## Aggregate-maintenance status

Authoritative Endpoint14/full-corpus run `34162318028` at canonical head `f01cc26b139a7f52fb275ace7fd13b6e591ac57d` passed:

- placeholder rejection;
- `FormalResearch.QIC.Endpoint14ReducedPolynomialIdentity`;
- the full Endpoint14 determinant/adjugate bridge.

The full `timeout 1200 lake build FormalResearch` then failed/timed out. Its completed compiler log showed all seven prior frontier modules building successfully, including `FormalResearch.Blaschke.WronskianAtomNonvanishing`, and exposed the next concrete blocker:

- `FormalResearch/Blaschke/WronskianAtomUnitDisk.lean`
  - bare `conj` was not in scope under Lean 4.34/current mathlib;
  - after opening `ComplexConjugate`, the two `sub_eq_zero` uses required reversing the resulting equality with `.symm`.

These are compatibility/proof-elaboration repairs only. No theorem statement or research claim changed.

The hard frontier gate is now eight modules:

- `FormalResearch.Blaschke.WalshBasis`
- `FormalResearch.Blaschke.WalshWronskianExactRank`
- `FormalResearch.Gaudin.MatrixTreeHammingTriangle`
- `FormalResearch.Blaschke.WalshWronskianKernelBasis`
- `FormalResearch.Gaudin.MatrixWeightedMetricBridge`
- `FormalResearch.Blaschke.WronskianAtomIndependence`
- `FormalResearch.Blaschke.WronskianAtomNonvanishing`
- `FormalResearch.Blaschke.WronskianAtomUnitDisk`

Actions run `34190004169` passed at maintenance head `a5381f534cca75333aa8908b5abc392ab8a93e43`, including placeholder rejection and all eight modules.

PR #4 merged that exact tested delta into canonical with merge commit `9d745a4d7eb8d3a0d1b1be779082270e63300bdd`.

## Current action

This documentation-only commit carries the `[endpoint14-identity]` marker solely to trigger the next authoritative exact-head workflow. It does not change Lean source.

The required gate is:

1. placeholder rejection;
2. `FormalResearch.QIC.Endpoint14ReducedPolynomialIdentity`;
3. the full Endpoint14 determinant/adjugate bridge;
4. `timeout 1200 lake build FormalResearch`.

If the aggregate passes, record `AGGREGATE-GREEN` at the resulting exact head and stop aggregate maintenance unless source semantics have moved.

If it fails, use only the completed compiler log to identify the next concrete module frontier, repair that frontier on an agent branch, add it to the narrow hard gate, and re-run before touching canonical again.

## Claim discipline

- Endpoint14 remains module-green through the full Gaussian bridge; global `LEAN-CHECKED` still requires aggregate green under current project discipline.
- The repaired Wronskian modules are conditional/algebraic infrastructure and do not promote any new source-side Blaschke theorem.
- Do not promote B4 `F_C = 1/2`, the full Blaschke quartic reconstruction chain, degree-five Hodge stability, or q-Weyl analytic results to Lean-checked without dedicated semantic/formal evidence.
