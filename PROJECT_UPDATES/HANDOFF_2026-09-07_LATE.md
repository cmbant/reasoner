# Formal research handoff — 2026-09-07 late update

This file supersedes only the restart/status portion of `PROJECT_UPDATES/HANDOFF_2026-09-07.md`. Keep the earlier handoff for the detailed source-audit and Endpoint14 history.

## Exact heads before this trigger commit

- Research/source authority: `cmbant/QIprojects:main`
  - `8e270db4ccc9dc4fdd62d31bbe7140de688873e4`
  - latest commit: `Merge PR 39 follow-up: all-rank type-D relaxation gap as a paper proposition`
- Lean canonical branch after PR #6:
  - `cmbant/reasoner:formal-research-lean`
  - `cc7d33ac6470acdd423b5338927f7d3031f47989`

Since the prior source pin `afe15bdbe01b1c8c7b194695ae2991af49210bfd`, QIprojects advanced 23 commits. That compare touches QI-B/B4 and QI-D only, with no Blaschke or Gaudin paths, so it does not revise the retained Walsh/Wronskian or Gaudin formal targets in this maintenance lane.

## Aggregate-maintenance status

Authoritative Endpoint14/full-corpus run `34192491593` at canonical head `cae9bc242aba035b35e71ad1d3085d35dbbf5bd7` passed:

- placeholder rejection;
- `FormalResearch.QIC.Endpoint14ReducedPolynomialIdentity`;
- the full Endpoint14 determinant/adjugate bridge.

The full `timeout 1200 lake build FormalResearch` then failed/timed out. Its completed compiler log showed all nine prior frontier modules building successfully, including `FormalResearch.Blaschke.SingletonWalshSynthesis`, and exposed two concrete blockers before the timeout tail:

- `FormalResearch/Blaschke/SingletonKernelDirectSum.lean`
  - current `walshBasis` coercions are propositionally, not definitionally, the underlying `walshVector` family;
  - the singleton and non-singleton span witnesses now rewrite explicitly with the current basis coercion theorem through `simpa [walshBasis]`.
- `FormalResearch/Bridges/B2BlaschkeRangeEquiv.lean`
  - polynomial notation `ℂ[X]` needed the `Polynomial` scope open;
  - the composed singleton Wronskian map needed to be explicitly `noncomputable`;
  - the later injectivity/range theorem-name failures were downstream consequences of that first definition failing to elaborate.

These are Lean/mathlib compatibility and proof-elaboration repairs only. No theorem statement or research claim changed.

The hard frontier gate is now eleven modules:

- `FormalResearch.Blaschke.WalshBasis`
- `FormalResearch.Blaschke.WalshWronskianExactRank`
- `FormalResearch.Gaudin.MatrixTreeHammingTriangle`
- `FormalResearch.Blaschke.WalshWronskianKernelBasis`
- `FormalResearch.Gaudin.MatrixWeightedMetricBridge`
- `FormalResearch.Blaschke.WronskianAtomIndependence`
- `FormalResearch.Blaschke.WronskianAtomNonvanishing`
- `FormalResearch.Blaschke.WronskianAtomUnitDisk`
- `FormalResearch.Blaschke.SingletonWalshSynthesis`
- `FormalResearch.Blaschke.SingletonKernelDirectSum`
- `FormalResearch.Bridges.B2BlaschkeRangeEquiv`

Actions run `34202143050` passed at maintenance head `8e87ab8a59eba8bda9e2a6c7cca024723e288b02`, including placeholder rejection and all eleven modules.

PR #6 merged that exact tested delta into canonical with merge commit `cc7d33ac6470acdd423b5338927f7d3031f47989`.

## Current action

This documentation-only commit carries the `[endpoint14-identity]` marker solely to trigger the next authoritative exact-head workflow. It does not change Lean source.

The required gate is:

1. placeholder rejection;
2. `FormalResearch.QIC.Endpoint14ReducedPolynomialIdentity`;
3. the full Endpoint14 determinant/adjugate bridge;
4. `timeout 1200 lake build FormalResearch`.

If the aggregate passes, record `AGGREGATE-GREEN` at the resulting exact head and stop aggregate maintenance unless source semantics have moved.

If it fails, use only the completed compiler log to identify the next concrete module frontier. If the log contains no compiler errors and only exit 124 after all imported modules are built, treat that separately as a validation-runtime issue rather than inventing a theorem repair.

## Claim discipline

- Endpoint14 remains module-green through the full Gaussian bridge; global `LEAN-CHECKED` still requires aggregate green under current project discipline.
- The repaired Wronskian/Walsh modules are conditional/algebraic infrastructure and do not promote any new source-side Blaschke theorem.
- Do not promote B4 `F_C = 1/2`, the full Blaschke quartic reconstruction chain, degree-five Hodge stability, or q-Weyl analytic results to Lean-checked without dedicated semantic/formal evidence.
