# Vendored: math-lab (PPT criterion for 2 x 3)

- Upstream: https://github.com/SproutSeeds/math-lab
- Commit: 48d14da643ec5f6e40ea0e2ed9f2a5eb9c8d5fda
- Licence: Apache-2.0 (`LICENSE`; the nested PSI sources carry their own `ThirdParty/PSI/LICENSE`,
  `NOTICE` and `PROVENANCE.md`).

Only the 56-file import closure of `ChainPPT.pptSeparable23`
(`MathLab/ChainTheory/PPTCriterion.lean`) is included: 11 files under `MathLab/` and 45 files under
`ThirdParty/PSI/ThreeCopyQutritWerner/`. Nothing else from upstream is vendored.

Used by `FormalResearch/PPTThreeQubit/PPTSeparable23.lean`, which derives
`FormalResearch.PPTThreeQubit.PPTSeparable23` from `ChainPPT.pptSeparable23`.

## Patches (the only modifications to upstream files)

1. `ThirdParty/PSI/ThreeCopyQutritWerner/Imports.lean`: deleted the line
   `public import Mathlib.Tactic.Basify.Attr` (the module is not in the pinned Mathlib and is unused).
2. `MathLab/Convex/CompactHull.lean`: `Finset.sum_extend_zero_of_injective` is newer than the pinned
   Mathlib. A proof was inserted after `@[expose] public section` as
   `MathLab.Compat.sum_extend_zero_of_injective`, and its two call sites were updated to that name.
