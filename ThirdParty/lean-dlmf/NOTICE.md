# Vendored: bjbraams/lean-DLMF (Liouville–Green, Sturm comparison and oscillation; Mathlib-only closure)

- Upstream: https://github.com/bjbraams/lean-DLMF
- Commit: 7edc630dca27f090c62d93fa8976b017cd6e92f9 (`main`, 2026; upstream pins Lean `v4.36.0-rc2` and Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`)
- Licence: Apache-2.0 (`LICENSE`, copied verbatim from upstream; upstream has no separate `NOTICE` file). The file headers (copyright lines, authors) are unchanged.

Only the import closure of the seven modules `DLMFMathlib.Analysis.ODE.{LiouvilleGreen, LiouvilleGreenReal, LiouvilleGreenExpansion, LiouvilleGreenFinite, SturmComparison, SturmCount, SturmOscillation}` is included: 15 files, 6808 lines. Every file imports only Mathlib (no other upstream module, no TauCeti, no sibling repository). Nothing else from upstream is vendored.

Files (all under `DLMFMathlib/`):
`Analysis/ODE/LinearGlobal.lean`, `Analysis/ODE/LiouvilleGreen.lean`, `Analysis/ODE/LiouvilleGreenExpansion.lean`,
`Analysis/ODE/LiouvilleGreenFinite.lean`, `Analysis/ODE/LiouvilleGreenReal.lean`, `Analysis/ODE/LiouvilleGreenVolterra.lean`,
`Analysis/ODE/ParamHolomorphic.lean`, `Analysis/ODE/PowerSeriesUniqueness.lean`, `Analysis/ODE/SturmComparison.lean`,
`Analysis/ODE/SturmCount.lean`, `Analysis/ODE/SturmDeformation.lean`, `Analysis/ODE/SturmLiouville.lean`,
`Analysis/ODE/SturmOscillation.lean`, `Analysis/SpecialFunctions/Trigonometric/Bounds.lean`, `Topology/Order/ZeroEnumeration.lean`.

Used by `FormalResearch/Special/VendoredDlmfSmoke.lean` (headline axiom pins only; not imported by `FormalResearch.lean`).

## Patches

Patched for Lean v4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (this repository's pins). Every patch is marked `-- PATCH`:

1. `DLMFMathlib/Analysis/ODE/SturmDeformation.lean`, proof of `SturmDeformation.local`: the two arguments
   `(by simpa [Function.uncurry_def] using hcY.neg)` and `(by simpa [Function.uncurry_def] using hcY'.neg)` are
   replaced by `hcY.neg hcY'.neg`. Under Mathlib v4.35 the simp normal forms of the two sides differ, so `simpa`
   no longer closes them; the terms are definitionally equal. No statement changed.
2. `DLMFMathlib/Analysis/ODE/LiouvilleGreenFinite.lean`, line 830: `private lemma exists_solution_expansion_oscillatory_finite_endpoint`
   made public (`lemma`), so that it is usable from other modules (Olver, Ch. 6, Thm 2.2, from a finite endpoint).
   The proof is unchanged.

Build setup (not a source change): the `[[lean_lib]] DLMFMathlib` stanza in `lakefile.toml` sets
`leanOptions = {autoImplicit = false, relaxedAutoImplicit = false}`, as upstream's `lakefile.toml` does.

## Checks

- `lake build DLMFMathlib` builds all 15 files on the pins. Only linter warnings remain (for example unused `simp`
  arguments, `ParamHolomorphic.lean` line 240); no errors.
- No placeholder-proof token (CI scan word), no `axiom` and no `native_decide` appears in the vendored files.
- `FormalResearch/Special/VendoredDlmfSmoke.lean` pins the axioms of `ODE.sturm_comparison` and of
  `LiouvilleGreen.exists_solution_expansion_oscillatory_finite_endpoint` to `[propext, Classical.choice, Quot.sound]`.

## Not vendored (blocked)

The parabolic-cylinder closure of `DLMF.ParabolicCylinder.Basic.Wronskians` (upstream `DLMF/` modules and three further
`DLMFMathlib/` modules, 14 in total) is not in this tree. Three TauCeti imports in it are unused and can be removed
(`DLMF/Confluent/Basic/KummerM.lean` and `DLMF/Confluent/Basic/Tricomi.lean`: `TauCeti.Analysis.SpecialFunctions.Erf`;
`DLMF/ParabolicCylinder/Basic/Functions.lean`: `TauCeti.RingTheory.Polynomial.Hermite.Derivative`). These removals were
checked by build but are not committed, and `DLMF/ParabolicCylinder/Basic/WeberEquation.lean` also needs Mathlib's
`Mathlib.RingTheory.Polynomial.Hermite.Basic` (`hermite`, `hermite_zero`, `hermite_one`). All other modules of that closure
build, but `WeberEquation.lean` fails on one name:
`hermite_add_two` (induction step of `parabolicCylinderD_nat`, DLMF 12.7.2). That name is provided only by
`TauCeti.RingTheory.Polynomial.Hermite.Derivative` (TauCeti, Apache-2.0, not vendored); Mathlib v4.35 has no
`hermite_add_two`. `Wronskians.lean` and every module that imports `WeberEquation.lean` are therefore not built.
Vendoring TauCeti's module, or proving the recurrence locally, is an owner decision and has not been done.

Not attempted: the Step 3 targets (`DLMF/Confluent/ParabolicCylinder/WronskiansAndConnections.lean`,
`DLMF/ParabolicCylinder/ElementaryProperties.lean`, `DLMF/ParabolicCylinder/Hermite.lean`,
`DLMF/ParabolicCylinder/Integrals/Representations.lean`), which are conditional on the parabolic-cylinder closure.
