# Formal research handoff — 2026-09-07 late update

This file supersedes only the restart/status portion of `PROJECT_UPDATES/HANDOFF_2026-09-07.md`. Keep the earlier handoff for the detailed source-audit and Endpoint14 history.

## Exact heads before this trigger commit

- Research/source authority: `cmbant/QIprojects:main`
  - `8e270db4ccc9dc4fdd62d31bbe7140de688873e4`
  - latest commit: `Merge PR 39 follow-up: all-rank type-D relaxation gap as a paper proposition`
- Lean canonical branch after PR #5:
  - `cmbant/reasoner:formal-research-lean`
  - `f544ce24e440c5bb798fb5a45cca86190c66a7bf`

Since the prior source pin `afe15bdbe01b1c8c7b194695ae2991af49210bfd`, QIprojects advanced 23 commits. That compare touches QI-B/B4 and QI-D only, with no Blaschke or Gaudin paths, so it does not revise the retained Walsh/Wronskian or Gaudin formal targets in this maintenance lane.

## Aggregate-maintenance status

Authoritative Endpoint14/full-corpus run `34190239339` at canonical head `25c68882cacaabcb1952682177d878b1de40cdaf` passed:

- placeholder rejection;
- `FormalResearch.QIC.Endpoint14ReducedPolynomialIdentity`;
- the full Endpoint14 determinant/adjugate bridge.

The full `timeout 1200 lake build FormalResearch` then failed/timed out. Its completed compiler log showed all eight prior frontier modules building successfully, including `FormalResearch.Blaschke.WronskianAtomUnitDisk`, and exposed the next concrete blocker:

- `FormalResearch/Blaschke/SingletonWalshSynthesis.lean`
  - polynomial atom synthesis needed to be marked `noncomputable`;
  - the current `fintypeLinearCombination_injective` alias required ordinary projection syntax;
  - the singleton commuting-diagram proof needed explicit finite-sum scalar distribution;
  - the final injectivity proof needed the lambda applications exposed with `change` before rewriting.

These are Lean/mathlib compatibility and proof-elaboration repairs only. No theorem statement or research claim changed.

The hard frontier gate is now nine modules:

- `FormalResearch.Blaschke.WalshBasis`
- `FormalResearch.Blaschke.WalshWronskianExactRank`
- `FormalResearch.Gaudin.MatrixTreeHammingTriangle`
- `FormalResearch.Blaschke.WalshWronskianKernelBasis`
- `FormalResearch.Gaudin.MatrixWeightedMetricBridge`
- `FormalResearch.Blaschke.WronskianAtomIndependence`
- `FormalResearch.Blaschke.WronskianAtomNonvanishing`
- `FormalResearch.Blaschke.WronskianAtomUnitDisk`
- `FormalResearch.Blaschke.SingletonWalshSynthesis`

Actions run `34192212060` passed at maintenance head `ee566828a09c1762a72a22d906d208116f3ed864`, including placeholder rejection and all nine modules.

PR #5 merged that exact tested delta into canonical with merge commit `f544ce24e440c5bb798fb5a45cca86190c66a7bf`.

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
- The repaired Wronskian/Walsh modules are conditional/algebraic infrastructure and do not promote any new source-side Blaschke theorem.
- Do not promote B4 `F_C = 1/2`, the full Blaschke quartic reconstruction chain, degree-five Hodge stability, or q-Weyl analytic results to Lean-checked without dedicated semantic/formal evidence.
