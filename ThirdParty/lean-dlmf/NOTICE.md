# Vendored: bjbraams/lean-DLMF (Liouville–Green, Sturm comparison, and parabolic cylinder functions; Mathlib-only closures)

- Upstream: https://github.com/bjbraams/lean-DLMF
- Commit: 7edc630dca27f090c62d93fa8976b017cd6e92f9 (`main`, 2026; upstream pins Lean `v4.36.0-rc2` and Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`)
- Licence: Apache-2.0 (`LICENSE`, copied verbatim from upstream; upstream has no separate `NOTICE` file). The file headers (copyright lines, authors) are unchanged, except where a patch below says otherwise.

Two closures are included, nothing else from upstream:

1. **Liouville–Green and Sturm** (`DLMFMathlib`): the import closure of the seven modules `DLMFMathlib.Analysis.ODE.{LiouvilleGreen, LiouvilleGreenReal, LiouvilleGreenExpansion, LiouvilleGreenFinite, SturmComparison, SturmCount, SturmOscillation}`, 15 files.
2. **Parabolic cylinder functions** (`DLMF` and three further `DLMFMathlib` files): the import closure of `DLMF.ParabolicCylinder.Basic.Wronskians`, 14 files.

Every file imports only Mathlib or other vendored modules: no TauCeti, no sibling repository.

## Files and line counts

Total 29 files, 9974 lines (as vendored, after patches).

`DLMFMathlib/` (18 files, 7112 lines; library `DLMFMathlib`, glob `DLMFMathlib.+`):

| lines | file |
|---:|---|
| 182 | `Analysis/ODE/LinearGlobal.lean` |
| 216 | `Analysis/ODE/LiouvilleGreen.lean` |
| 448 | `Analysis/ODE/LiouvilleGreenExpansion.lean` |
| 985 | `Analysis/ODE/LiouvilleGreenFinite.lean` |
| 370 | `Analysis/ODE/LiouvilleGreenReal.lean` |
| 402 | `Analysis/ODE/LiouvilleGreenVolterra.lean` |
| 373 | `Analysis/ODE/ParamHolomorphic.lean` |
| 522 | `Analysis/ODE/PowerSeriesUniqueness.lean` |
| 333 | `Analysis/ODE/SturmComparison.lean` |
| 569 | `Analysis/ODE/SturmCount.lean` |
| 248 | `Analysis/ODE/SturmDeformation.lean` |
| 837 | `Analysis/ODE/SturmLiouville.lean` |
| 1119 | `Analysis/ODE/SturmOscillation.lean` |
| 105 | `Analysis/SpecialFunctions/Trigonometric/Bounds.lean` |
| 99 | `Topology/Order/ZeroEnumeration.lean` |
| 112 | `Analysis/Analytic/OfScalarsDeriv.lean` |
| 107 | `Analysis/Complex/NonInteger.lean` |
| 85 | `Analysis/Complex/SegmentPrimitive.lean` |

`DLMF/` (11 files, 2862 lines; library `DLMF`, explicit module globs, so that only this closure is in it):

| lines | file |
|---:|---|
| 410 | `Confluent/Basic/KummerContiguous.lean` |
| 81 | `Confluent/Basic/KummerM.lean` |
| 363 | `Confluent/Basic/KummerProperties.lean` |
| 96 | `Confluent/Basic/Tricomi.lean` |
| 238 | `Core/Basic.lean` |
| 46 | `Hypergeometric/Basic/GaussCoefficients.lean` |
| 347 | `Hypergeometric/Basic/GaussSeries.lean` |
| 204 | `Hypergeometric/Basic/Pochhammer.lean` |
| 129 | `ParabolicCylinder/Basic/Functions.lean` |
| 456 | `ParabolicCylinder/Basic/WeberEquation.lean` |
| 492 | `ParabolicCylinder/Basic/Wronskians.lean` |

Used by `FormalResearch/Special/VendoredDlmfSmoke.lean` (headline axiom pins only; not imported by `FormalResearch.lean`).

## Patches

Patched for Lean v4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (this repository's pins). Every patch is marked `-- PATCH` in the source. Seven patch sites in six files:

1. `DLMFMathlib/Analysis/ODE/SturmDeformation.lean`, proof of `SturmDeformation.local`: the two arguments
   `(by simpa [Function.uncurry_def] using hcY.neg)` and `(by simpa [Function.uncurry_def] using hcY'.neg)` are
   replaced by `hcY.neg hcY'.neg`. Under Mathlib v4.35 the simp normal forms of the two sides differ, so `simpa`
   no longer closes them; the terms are definitionally equal. No statement changed.
2. `DLMFMathlib/Analysis/ODE/LiouvilleGreenFinite.lean`, line 830: `private lemma exists_solution_expansion_oscillatory_finite_endpoint`
   made public (`lemma`), so that it is usable from other modules (Olver, Ch. 6, Thm 2.2, from a finite endpoint).
   The proof is unchanged.
3. `DLMF/Confluent/Basic/KummerM.lean`, line 10: removed `public import TauCeti.Analysis.SpecialFunctions.Erf`.
   The file does not use it (no `erf` occurs in the file).
4. `DLMF/Confluent/Basic/Tricomi.lean`, line 9: removed `public import TauCeti.Analysis.SpecialFunctions.Erf`.
   The file does not use it.
5. `DLMF/ParabolicCylinder/Basic/Functions.lean`, line 9: removed `public import TauCeti.RingTheory.Polynomial.Hermite.Derivative`.
   The file does not use it.
6. `DLMF/ParabolicCylinder/Basic/WeberEquation.lean`, line 10: added `public import Mathlib.RingTheory.Polynomial.Hermite.Basic`,
   which provides `hermite`, `hermite_zero` and `hermite_one` (previously reached through the TauCeti import of item 5).
7. `DLMF/ParabolicCylinder/Basic/WeberEquation.lean`, lines 403–422 (section `Hermite`): two local proofs that replace the
   two lemmas of `TauCeti.RingTheory.Polynomial.Hermite.Derivative` (TauCeti, Apache-2.0, not vendored):
   - `hermite_derivative_succ (n : ℕ) : derivative (hermite (n + 1)) = (n + 1) • hermite n`, by induction on `n`,
     from Mathlib's `hermite_succ` (`He_{n+1} = X He_n - He_n'`); the successor step uses only `hermite_succ` at
     `n` and `n + 1` and the induction hypothesis.
   - `hermite_add_two (n : ℕ) : hermite (n + 1 + 1) = X * hermite (n + 1) - (n + 1) • hermite n`, from `hermite_succ (n + 1)`
     and `hermite_derivative_succ n`. The statement is the one `parabolicCylinderD_nat` uses (`rw [h, hermite_add_two]`);
     it was not compared with TauCeti's original text, which is not available here. The name is not in Mathlib v4.35.

   These are new proofs in vendored code, not upstream proofs. They are verified only by this repository's build.

## Checks

- `lake build DLMFMathlib` builds all 18 files on the pins: no errors, no warnings from the vendored files apart from
  upstream linter warnings that were already present (`ParamHolomorphic.lean` line 240, unused `simp` argument).
- `lake build DLMF` (clean rebuild of the 11 files) builds on the pins: no errors and no warnings.
- `lake build FormalResearch.Special.VendoredDlmfSmoke` builds and the seven axiom pins match. Each of the following
  depends on exactly `[propext, Classical.choice, Quot.sound]`:
  - `ODE.sturm_comparison`;
  - `LiouvilleGreen.exists_solution_expansion_oscillatory_finite_endpoint`;
  - `DLMF.Confluent.parabolicCylinderV_wronskian` (DLMF 12.2.10, `𝒲{U, V} = √(2/π)`);
  - `DLMF.Confluent.isWeberSolution_parabolicCylinderU` and `DLMF.Confluent.isWeberSolution_parabolicCylinderV`
    (Weber's equation `f'' = (z²/4 + a) f` for `U` and `V`, DLMF 12.2.2);
  - `DLMF.Confluent.parabolicCylinderD_nat` (DLMF 12.7.2, `D_n(z) = e^{-z²/4} He_n(z)`);
  - `DLMF.Confluent.hermite_add_two` (patch 7).
- No placeholder-proof token (CI scan word), no `axiom` and no `native_decide` appears in any vendored `.lean` file.
- Every import in the vendored files is Mathlib or a vendored module.

## Build setup (not a source change)

`lakefile.toml` has two `[[lean_lib]]` stanzas for this tree, both not default targets, both with
`leanOptions = {autoImplicit = false, relaxedAutoImplicit = false}`, as upstream's `lakefile.toml` does:
`DLMFMathlib` (`globs = ["DLMFMathlib.+"]`) and `DLMF` (the 11 module names listed above, explicitly).

## Not attempted

Step 3 targets (`DLMF/Confluent/ParabolicCylinder/WronskiansAndConnections.lean`, `DLMF/ParabolicCylinder/ElementaryProperties.lean`,
`DLMF/ParabolicCylinder/Hermite.lean`, `DLMF/ParabolicCylinder/Integrals/Representations.lean`) are not vendored. Their closures
are much larger (hundreds of modules) and contain unproved declarations; the import structure is being scoped separately.
