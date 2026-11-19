# Vendored: bjbraams/lean-DLMF with lean-codes and TauCeti modules (Liouville–Green, Sturm, parabolic cylinder functions, and the import closure of `DLMF.Confluent.Regularized`)

## Sources

- **lean-DLMF** (upstream): https://github.com/bjbraams/lean-DLMF, commit `7edc630dca27f090c62d93fa8976b017cd6e92f9` (`main`, 2026). Upstream pins Lean `v4.36.0-rc2` and Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`. Licence: Apache-2.0, `LICENSE` (copied verbatim; upstream has no separate `NOTICE` file).
- **lean-codes**: https://github.com/bjbraams/lean-codes, commit `39ce9533bc1cbd313ebe939dd4c8f91d95debcc2` (short `39ce953`; default-branch HEAD at vendoring, commit of 2026-11-15). Upstream's `lake-manifest.json` has no pin for it (a path dependency `../lean-codes`), so this commit is the provenance used. Licence: Apache-2.0, `licenses/lean-codes/LICENSE` (copied verbatim).
- **TauCeti**: https://github.com/TauCetiProject/TauCeti, commit `396c3bd971e9722aa8656231760e710fe641d8cf` (the rev in upstream `lake-manifest.json`). Licence: Apache-2.0, `licenses/TauCeti/LICENSE` (copied verbatim).

The file headers (copyright lines, authors) are unchanged, except where a patch below says otherwise.

## Scope

1. **Import closure of `DLMF.Confluent.Regularized`** after the cuts of §Patches: 42 modules (35 `DLMF`, 7 `DLMFMathlib`). It supplies `differentiable_regularizedConfluent_comp`.
2. **Parabolic cylinder functions** (earlier steps): the import closure of `DLMF.ParabolicCylinder.Basic.Wronskians`, `DLMF.Confluent.ParabolicCylinder.WronskiansAndConnections`, and `DLMF.ParabolicCylinder.ElementaryPropertiesCore` (an extraction; see §Extraction).
3. **Liouville–Green and Sturm** (`DLMFMathlib`): the import closure of seven modules `DLMFMathlib.Analysis.ODE.{LiouvilleGreen, LiouvilleGreenReal, LiouvilleGreenExpansion, LiouvilleGreenFinite, SturmComparison, SturmCount, SturmOscillation}`.
4. **Four external modules** from two sibling repositories, needed by the closure of 1 (lean-codes is upstream's `../lean-codes` dependency):
   - `ComplexAnalysis.HalfPlane` and `ComplexAnalysis.Pow` (lean-codes), with `Complex.mul_cpow_of_re_pos` used by `DLMF.Hypergeometric.Transformations`;
   - `TauCeti.Analysis.Complex.SlitPlane` (TauCeti), imported by `ComplexAnalysis.HalfPlane`;
   - `TauCeti.Analysis.SpecialFunctions.Erf` (TauCeti), used by `DLMF.ErrorFunctions.Basic.Properties` (`erf_ofReal`, `erfc_ofReal`).

Total: 66 `.lean` files, 18584 lines (after patches): `DLMF` 40 files, 10221 lines; `DLMFMathlib` 22 files, 7492 lines; `ComplexAnalysis` 2 files, 187 lines; `TauCeti` 2 files, 684 lines. Every import in the vendored files is Mathlib or a vendored module.

## Files and line counts

`DLMF/` (40 files, 10221 lines; library `DLMF`, explicit module list):

| lines | file | patch sites |
|---:|---|---|
| 32 | `Confluent/Basic.lean` | |
| 54 | `Confluent/Basic/Buchholz.lean` | |
| 93 | `Confluent/Basic/ErrorFunctions.lean` | |
| 47 | `Confluent/Basic/ExpansionData.lean` | |
| 211 | `Confluent/Basic/ExponentialIntegralSeries.lean` | 11 |
| 70 | `Confluent/Basic/ExponentialIntegrals.lean` | |
| 39 | `Confluent/Basic/IncompleteGamma.lean` | |
| 410 | `Confluent/Basic/KummerContiguous.lean` | |
| 81 | `Confluent/Basic/KummerM.lean` | 3 |
| 363 | `Confluent/Basic/KummerProperties.lean` | |
| 96 | `Confluent/Basic/Tricomi.lean` | 4 |
| 64 | `Confluent/Basic/TricomiLogarithmic.lean` | |
| 262 | `Confluent/Basic/Whittaker.lean` | |
| 77 | `Confluent/Basic/WhittakerLogarithmic.lean` | |
| 533 | `Confluent/KummerProperties.lean` | 10 |
| 476 | `Confluent/ParabolicCylinder/WronskiansAndConnections.lean` | 8 |
| 267 | `Confluent/Regularized.lean` | |
| 238 | `Core/Basic.lean` | |
| 162 | `ErrorFunctions/Basic/Functions.lean` | |
| 271 | `ErrorFunctions/Basic/Properties.lean` | |
| 60 | `Hypergeometric/Basic/AppellF4.lean` | |
| 585 | `Hypergeometric/Basic/CutPlane.lean` | |
| 46 | `Hypergeometric/Basic/GaussCoefficients.lean` | |
| 688 | `Hypergeometric/Basic/GaussEquation.lean` | |
| 347 | `Hypergeometric/Basic/GaussSeries.lean` | |
| 701 | `Hypergeometric/Basic/ParameterAnalyticity.lean` | |
| 204 | `Hypergeometric/Basic/Pochhammer.lean` | |
| 178 | `Hypergeometric/Basic/PrincipalBranch.lean` | |
| 43 | `Hypergeometric/Basic/RealPochhammer.lean` | |
| 198 | `Hypergeometric/Basic/SpecialValues.lean` | |
| 227 | `Hypergeometric/Contiguous.lean` | |
| 415 | `Hypergeometric/Continuation.lean` | 13 |
| 854 | `Hypergeometric/Derivatives.lean` | |
| 172 | `Hypergeometric/DiffEq.lean` | |
| 218 | `Hypergeometric/EulerIntegral.lean` | 12 |
| 227 | `Hypergeometric/Transformations.lean` | 14 |
| 129 | `ParabolicCylinder/Basic/Functions.lean` | 5 |
| 456 | `ParabolicCylinder/Basic/WeberEquation.lean` | 6, 7 |
| 492 | `ParabolicCylinder/Basic/Wronskians.lean` | |
| 135 | `ParabolicCylinder/ElementaryPropertiesCore.lean` | 9 (extraction) |

`DLMFMathlib/` (22 files, 7492 lines; library `DLMFMathlib`, glob `DLMFMathlib.+`):

| lines | file | patch sites |
|---:|---|---|
| 112 | `Analysis/Analytic/OfScalarsDeriv.lean` | |
| 52 | `Analysis/Calculus/DifferentialOperators.lean` | |
| 107 | `Analysis/Complex/NonInteger.lean` | |
| 169 | `Analysis/Complex/ParameterContinuity.lean` | |
| 85 | `Analysis/Complex/SegmentPrimitive.lean` | |
| 182 | `Analysis/ODE/LinearGlobal.lean` | |
| 216 | `Analysis/ODE/LiouvilleGreen.lean` | |
| 448 | `Analysis/ODE/LiouvilleGreenExpansion.lean` | |
| 985 | `Analysis/ODE/LiouvilleGreenFinite.lean` | 2 |
| 370 | `Analysis/ODE/LiouvilleGreenReal.lean` | |
| 402 | `Analysis/ODE/LiouvilleGreenVolterra.lean` | |
| 373 | `Analysis/ODE/ParamHolomorphic.lean` | |
| 522 | `Analysis/ODE/PowerSeriesUniqueness.lean` | |
| 333 | `Analysis/ODE/SturmComparison.lean` | |
| 569 | `Analysis/ODE/SturmCount.lean` | |
| 248 | `Analysis/ODE/SturmDeformation.lean` | 1 |
| 837 | `Analysis/ODE/SturmLiouville.lean` | |
| 1119 | `Analysis/ODE/SturmOscillation.lean` | |
| 70 | `Analysis/ODE/Wronskian.lean` | |
| 89 | `Analysis/SpecialFunctions/Gamma/Bounds.lean` | |
| 105 | `Analysis/SpecialFunctions/Trigonometric/Bounds.lean` | |
| 99 | `Topology/Order/ZeroEnumeration.lean` | |

`ComplexAnalysis/` (2 files, 187 lines; lean-codes, library `DLMF`):

| lines | file | patch sites |
|---:|---|---|
| 110 | `ComplexAnalysis/HalfPlane.lean` | none |
| 77 | `ComplexAnalysis/Pow.lean` | none |

`TauCeti/` (2 files, 684 lines; TauCeti, library `DLMF`):

| lines | file | patch sites |
|---:|---|---|
| 304 | `TauCeti/Analysis/Complex/SlitPlane.lean` | none |
| 380 | `TauCeti/Analysis/SpecialFunctions/Erf.lean` | none |

## Patches

Every change is marked `-- PATCH` in the source, except that the removed module-doc bullets are not marked (they are listed here). The numbers in the table above refer to the items below.

1. `DLMFMathlib/Analysis/ODE/SturmDeformation.lean`, proof of `SturmDeformation.local`: the two arguments `(by simpa [Function.uncurry_def] using hcY.neg)` and `(by simpa [Function.uncurry_def] using hcY'.neg)` are replaced by `hcY.neg hcY'.neg`. Under Mathlib v4.35 the simp normal forms of the two sides differ, so `simpa` no longer closes them; the terms are definitionally equal. No statement changed.
2. `DLMFMathlib/Analysis/ODE/LiouvilleGreenFinite.lean`, line 830: `private lemma exists_solution_expansion_oscillatory_finite_endpoint` made public (`lemma`), so that it is usable from other modules. The proof is unchanged.
3. `DLMF/Confluent/Basic/KummerM.lean`, line 10: removed `public import TauCeti.Analysis.SpecialFunctions.Erf`. The file does not use it.
4. `DLMF/Confluent/Basic/Tricomi.lean`, line 9: removed `public import TauCeti.Analysis.SpecialFunctions.Erf`. The file does not use it.
5. `DLMF/ParabolicCylinder/Basic/Functions.lean`, line 9: removed `public import TauCeti.RingTheory.Polynomial.Hermite.Derivative`. The file does not use it.
6. `DLMF/ParabolicCylinder/Basic/WeberEquation.lean`, line 10: added `public import Mathlib.RingTheory.Polynomial.Hermite.Basic`, which provides `hermite`, `hermite_zero` and `hermite_one` (previously reached through the TauCeti import of item 5).
7. `DLMF/ParabolicCylinder/Basic/WeberEquation.lean`, lines 403–422 (section `Hermite`): local proofs `hermite_derivative_succ` and `hermite_add_two`, replacing the two lemmas of `TauCeti.RingTheory.Polynomial.Hermite.Derivative` (TauCeti, not vendored). They are new proofs in vendored code, verified only by this repository's build. The statement of `hermite_add_two` was not compared with TauCeti's original text, which is not available here.
8. `DLMF/Confluent/ParabolicCylinder/WronskiansAndConnections.lean`, lines 10–11: removed `public import DLMF.Confluent.ParabolicCylinder.EquationAndIntegrals` (upstream, not vendored). None of its 13 declarations is used in the file.
9. `DLMF/ParabolicCylinder/ElementaryPropertiesCore.lean`: an extraction, see §Extraction.
10. `DLMF/Confluent/KummerProperties.lean`, line 15: removed `public import TauCeti.Analysis.SpecialFunctions.Erf`. The file uses none of the 59 declarations of that module (name search); the build passes. (`DLMF.ErrorFunctions.Basic.Properties` does use that module, and gets it through `DLMF.Confluent.Basic.ErrorFunctions`, whose import is unchanged.)
11. `DLMF/Confluent/Basic/ExponentialIntegralSeries.lean`: removed line 9, `public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral`; removed the declaration `Real.tendsto_sinIntegral_atTop` (upstream lines 107–110, `Si(x) → π/2`) and its module-doc bullet (upstream lines 25–26). The declaration is unused by the target and by any other vendored declaration (conservative token-level reachability from `DLMF.Confluent.differentiable_regularizedConfluent_comp` does not reach it). Its import's closure is 106 TauCeti modules, 22935 lines, sorry-free, which was judged too large for one leaf declaration.
12. `DLMF/Hypergeometric/EulerIntegral.lean`: removed line 12, `public import Carlson.TwoVariable.GaussHypergeometric` (closure 142 modules, 29624 lines, sorry-free; lean-codes); removed the declaration `gauss_summation` (upstream lines 75–81; its proof is `Carlson.ordinaryHypergeometric_one`) and its module-doc bullet (upstream lines 27–28). The helper lemmas of the same section, `ordinaryHypergeometric_one_eq_tsum` and `pochhammer_eval_re_le_norm_pochhammer`, are kept; they do not use Carlson.
13. `DLMF/Hypergeometric/Continuation.lean`: removed the declaration `tendsto_ordinaryHypergeometric_nhdsWithin_one` (upstream lines 335–367; it calls the removed `gauss_summation` at upstream line 346) and its module-doc bullet (upstream lines 33–34).
14. `DLMF/Hypergeometric/Transformations.lean`: removed line 10, `public import Carlson.RPolynomial.GeneratingIdentities` (closure 110 modules, 22564 lines, sorry-free). The use at upstream line 84 of `Carlson.mul_cpow_of_re_pos` is replaced by `Complex.mul_cpow_of_re_pos` (`ComplexAnalysis/Pow.lean`, line 49). The two statements, checked against the sources before the substitution, are identical up to renaming:
    - lean-codes `Carlson/RPolynomial/GeneratingIdentities.lean` line 109: `theorem mul_cpow_of_re_pos {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (b : ℂ) : (u * v) ^ b = u ^ b * v ^ b`;
    - lean-codes `ComplexAnalysis/Pow.lean` line 49: `theorem mul_cpow_of_re_pos {a w : ℂ} (ha : 0 < a.re) (hw : 0 < w.re) (t : ℂ) : (a * w) ^ t = a ^ t * w ^ t`.

    The import `ComplexAnalysis.Pow` (upstream line 9) is now used. No declaration of that name exists in Mathlib at v4.35.
Note (no patch): `DLMF/Confluent/Basic/ErrorFunctions.lean` is unchanged. It keeps its import of TauCeti's `Erf`, which `DLMF.ErrorFunctions.Basic.Properties` uses transitively; a first build without that import failed on `TauCeti.Real.erf` in `Properties.lean`.

Upstream `TauCeti-4.36.patch` (shipped in upstream's root) changes only `TauCeti/MeasureTheory/Measure/FiniteMeasureExt.lean` (a `simp` lemma rename for Mathlib 4.36). That file is in none of the closures vendored here, so the patch is not applied. The two vendored TauCeti files and the lean-codes files compile on v4.35 without it.

Upstream linter warnings present in vendored code (not patched): `DLMF/ErrorFunctions/Basic/Properties.lean` line 140 (unused simp argument `Nat.add_zero`); `DLMF/Confluent/KummerProperties.lean` line 256 (unused `congr 1`); `DLMFMathlib/Analysis/ODE/ParamHolomorphic.lean` line 240 (unused simp argument, from an earlier step).

## Extraction: `ElementaryPropertiesCore`

Upstream `DLMF/ParabolicCylinder/ElementaryProperties.lean` (697 lines) imports `DLMF.Confluent.Coulomb` and `DLMF.Confluent.ParabolicCylinder`, which are not vendored. The following 13 declarations are copied verbatim, proofs included, from upstream lines 103–107, 109–137, 139–144, 146–149, 151–154, 156–160, 162–167, 169–172, 174–178, 180–194 and 196–199 (namespace `DLMF.Confluent`):

- argument-entire: `parabolicCylinderU_entire` (103–107), `parabolicCylinderV_entire` (174–178);
- parameter-entire: `differentiable_parabolicCylinderEven_order` and `differentiable_parabolicCylinderOdd_order` (109–121), `parabolicCylinderU_entire_order` (123–137), `parabolicCylinderV_entire_order` (180–194); these use `differentiable_regularizedConfluent_comp` (`DLMF.Confluent.Regularized`, `@[fun_prop]`);
- conjugation: `conj_two_cpow`, `conj_parabolicCylinderEven`, `conj_parabolicCylinderOdd`, `conj_parabolicCylinderU`, `conj_parabolicCylinderV`;
- reality: `parabolicCylinderU_real` and `parabolicCylinderV_real`.

The extracted file imports `DLMF.ParabolicCylinder.Basic.Wronskians`, `DLMF.Confluent.Basic.KummerContiguous` and `DLMF.Confluent.Regularized`.

Not extracted: the derivative conjugation lemmas (upstream lines 201–224), `parabolicCylinderD_ode`, the modulus–phase, rotated-connection and series results, and `ElementaryProperties.lean` as a whole. `DLMF/ParabolicCylinder/Hermite.lean` and `DLMF/ParabolicCylinder/Integrals/Representations.lean` are not vendored (their closures are larger, see the earlier scoping).

Joint smoothness of `(a, z) ↦ U(a, z)` is not derived: the results above give entireness in each variable separately.

## Checks

- `lake build DLMF` (the 44 modules of the explicit list in `lakefile.toml`) builds on the pins (Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`): no errors. Warnings are listed under the patches above.
- `lake build FormalResearch.Special.VendoredDlmfSmoke` builds. Fifteen axiom pins match `[propext, Classical.choice, Quot.sound]`: the thirteen listed in the smoke module (`ODE.sturm_comparison`; `LiouvilleGreen.exists_solution_expansion_oscillatory_finite_endpoint`; `DLMF.Confluent.parabolicCylinderV_wronskian`; `isWeberSolution_parabolicCylinder{U,V}`; `parabolicCylinderD_nat`; `hermite_add_two`; `parabolicCylinder{U,V}_neg_eq`; `parabolicCylinderV_recurrence_{add,sub}`; `parabolicCylinder{U,V}_real`) and the two new ones, `DLMF.Confluent.parabolicCylinderU_entire_order` and `parabolicCylinderV_entire_order`.
- Sorry and banned-token scan: `grep -rnwE "sorry|admit|axiom|native_decide" ThirdParty/lean-dlmf --include=*.lean` prints nothing.
- Reachability: every vendored `DLMF.*` module (40) is in the import closure of `DLMF.Confluent.Regularized` or of `DLMF.ParabolicCylinder.ElementaryPropertiesCore`; the closure of `Regularized` alone reaches 35 `DLMF` and 7 `DLMFMathlib` modules. Every import is Mathlib or vendored.
- Removed declarations: a name search over the whole vendored tree (`gauss_summation`, `tendsto_ordinaryHypergeometric_nhdsWithin_one`, `tendsto_sinIntegral_atTop`, `Carlson`, `GaussHypergeometric`, `GeneratingIdentities`, `HalfDisc`) finds no use outside the patch comments.

## Build setup (not a source change)

`lakefile.toml`: the `DLMFMathlib` library (`globs = ["DLMFMathlib.+"]`) is unchanged. The `DLMF` library (`srcDir = "ThirdParty/lean-dlmf"`) lists its 44 modules explicitly, including `ComplexAnalysis.HalfPlane`, `ComplexAnalysis.Pow`, `TauCeti.Analysis.Complex.SlitPlane` and `TauCeti.Analysis.SpecialFunctions.Erf`. Both libraries are optional, not default targets.

## Not attempted

- The removed declarations (items 11–13). If the owner later wants them, their vendored closures are 106 TauCeti modules (`HalfDisc.SineIntegral`), 142 modules (`Carlson.TwoVariable.GaussHypergeometric`), and the 110-module `Carlson.RPolynomial.GeneratingIdentities` route, which item 14 avoids.
- `DLMF/ParabolicCylinder/Hermite.lean`, `DLMF/ParabolicCylinder/Integrals/Representations.lean` and `DLMF/ParabolicCylinder/ElementaryProperties.lean` as a whole.
