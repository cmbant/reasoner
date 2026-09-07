# Formal research handoff — 2026-09-07 late update

This file supersedes only the restart/status portion of `PROJECT_UPDATES/HANDOFF_2026-09-07.md`. Keep the earlier handoff for the detailed source-audit and Endpoint14 history.

## Exact heads before this trigger commit

- Research/source authority: `cmbant/QIprojects:main`
  - `eae4a5a48aa2b2e29303d18352a508efe3f35a38`
  - latest commit: `Merge PR #34: T17 revive free-fermion Racah entanglement note`
- Lean canonical branch after PR #2:
  - `cmbant/reasoner:formal-research-lean`
  - `963c2bdc2f052f5b88793ccc65b6722092b686cd`

The source pin is unchanged during the aggregate-maintenance cycle. Relative to the old handoff pin `f7bb9cabb277515b8597150e06ec0b30fb049861`, current `QIprojects/main` is 56 commits ahead; relative to the older `4160942c260c2a2bdcd480c2cfa5ae5eca810721` snapshot it is 437 commits ahead.

## Aggregate-maintenance status

The previous full Endpoint14 + aggregate run at canonical head `4d2b3af0d8e5147bad044fad20f09262a877c43b` kept Endpoint14 and placeholder rejection green, then exposed the next concrete full-corpus blocker in `FormalResearch/Blaschke/WronskianAtomIndependence.lean` before the monolithic build timed out.

That module was repaired on `agents/lean-aggregate-maintenance`. The compatibility changes are proof/API migration only: explicit polynomial evaluation rewrites through finite sums/scalar multiplication and an explicit erased-finset zero-factor witness. No new research claim was promoted.

The hard frontier gate was expanded to six modules:

- `FormalResearch.Blaschke.WalshBasis`
- `FormalResearch.Blaschke.WalshWronskianExactRank`
- `FormalResearch.Gaudin.MatrixTreeHammingTriangle`
- `FormalResearch.Blaschke.WalshWronskianKernelBasis`
- `FormalResearch.Gaudin.MatrixWeightedMetricBridge`
- `FormalResearch.Blaschke.WronskianAtomIndependence`

Actions run `34158964511` passed at maintenance head `ce8ee39813d545e67eddcb62bc9644eb2c75385c`, including placeholder rejection and all six modules.

PR #2 merged that tested delta into canonical with merge commit `963c2bdc2f052f5b88793ccc65b6722092b686cd`.

## Current action

This documentation-only commit carries the `[endpoint14-identity]` marker solely to trigger the authoritative exact-head workflow. It does not change Lean source.

The required next gate is:

1. placeholder rejection;
2. `FormalResearch.QIC.Endpoint14ReducedPolynomialIdentity`;
3. the full Endpoint14 determinant/adjugate bridge;
4. `timeout 1200 lake build FormalResearch`.

If the aggregate passes, record `AGGREGATE-GREEN` at the resulting exact head and stop aggregate maintenance unless source semantics have moved.

If it fails, use only the completed compiler log to identify the next concrete module frontier, repair that frontier on an agent branch, add it to the narrow hard gate, and re-run before touching canonical again.

## Claim discipline

- Endpoint14 remains source-aligned to the unchanged QI-C certificate source and is module-green through the full Gaussian bridge.
- The repaired Wronskian atom-independence theorem is conditional infrastructure under its stated nonvanishing hypothesis; it does not establish a new source-side Blaschke theorem by itself.
- Do not promote B4 `F_C = 1/2`, the full Blaschke quartic reconstruction chain, degree-five Hodge stability, or the new q-Weyl analytic T2 results to Lean-checked without dedicated semantic/formal evidence.
