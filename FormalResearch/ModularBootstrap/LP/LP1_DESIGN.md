# LP1: Paper II infinite-order derivative limit (`ds:LP` and supports)

Paper: `QIprojects/CFT/modular_bootstrap/paper/dual_spectrum.tex` and `dual_spectrum_limit.tex`.
Statements are indexed once, as `Prop`s, in `LP/Statements.lean` (`DsMom`, ..., `DsLPiii`, each with a
`*_holds` theorem). Everything is axiom-guarded to `[propext, Classical.choice, Quot.sound]`; no `sorry`;
every file builds with `lake build`; every module is under 800 lines.

## Status

Declarations are in namespace `FormalResearch.ModularBootstrap.LP`.

| paper label | Lean declaration (module) | status |
|---|---|---|
| (engine) positive extension of a positive functional on polynomial-growth functions to a Radon measure, also finite-group-invariant | `Measure.exists_measure_of_positive_polyGrowth`, `exists_invariant_measure_of_positive_polyGrowth` (`Measure/PolyGrowthExtension`) | proved |
| Laguerre bounds, generating function, Cayley expansion | `lagP_lower`, `abs_lagP_le` (`Laguerre`); `abs_lagPsi_le`, `hasSum_cayley` (`LaguerreGen`) | proved |
| `ds:mom`, abstract odd family `OddFam C p` | `ds_mom` (`Moments`) | proved |
| `ds:mom`, Laguerre instance | `lagP_oddFam`, `ds_mom_laguerre` (`Moments`) | proved |
| `ds:mom`, mass bound | `ds_mom_mass` (`Moments`) | proved |
| `dsl:poly-compact`, abstract family, with majorant `p_0`, `e^{εt}` moment | `poly_compact` (`PolyCompact`) | proved |
| `dsl:poly-compact`, finite-group clause | `poly_compact_invariant` (`PolyCompact`) | proved |
| `ds:cay` | `ds_cay_series`, `ds_cay_iff` (`Cayley`) | proved |
| `ds:cont` | `ds_cont` (real-analytic `v`), `ds_cont_complex` (holomorphic `v`) (`Continuation`) | proved |
| `dsl:positive-ray` | `positive_ray` (`PositiveRay`) | proved |
| `ds:LP`(i) | `ds_LP_i`, `ds_LP_b_imp_a` (`DerivLimit`; via `exists_crossingMeasure_of_not_oddFeasible` in `DerivLimitII`, `not_oddFeasible_of_crossingMeasure` in `DerivLimitI`) | proved |
| `ds:LP`(ii), closed `F` | `ds_LP_ii` (`DerivLimit`) | proved |
| `ds:LP`(iii) | `ds_LP_iii` (`DerivLimit`) | proved |
| `sd:LP` (SPIN-D) | not in LP1 | open: SPIN-D's job; it consumes `ds_LP_*` and `ds_cont_complex` |

Module order: `PolyGrowthExtension` -> `Laguerre` -> `LaguerreGen` -> `Moments` -> `PolyCompact` ->
`Cayley` -> `Continuation` -> `Tilt` -> `PositiveRay` -> `Reference` -> `DerivLimitI` -> `OddFunctional`
-> `DerivLimitII` -> `DerivLimit` -> `Statements`.

## Design

* `ds:mom` and `dsl:poly-compact` are theorems about an abstract odd family `p : ℕ → C(ℝ, ℝ)` with
  `OddFam C p` (upper bound `|p_k(t)| ≤ (t + Ck)^k` for `t ≥ 0`, lower bound `(t/2)^k ≤ p_k(t)` for
  `t ≥ 2Ck`); Laguerre is the instance `lagP_oddFam`, with `C = (1+w)/π` (the plan change from the
  coordinator, PR 301: no parallel Laguerre copy). The positive-ray lemma uses `pc (lagPC w)`.
* `ds:LP` needs no membership of `e^{-2πt} O_N` in the test class `Ā_w`. (i) is an
  exact pairing of a crossing measure with `e^{-2πt} p` (`ds:cay`, `ds_cay_iff`), plus the
  functional/measure construction of `OddFunctional` and `DerivLimitII`. (ii) feeds (i) into the
  existing `noSpanFeasible_of_crossingMeasure` and `theorem_E_a_decreasing`. (iii) combines the crossing
  measure at gap `T_V` from `theorem_E_b_compact` with `proposition_D1`.
* Thresholds are `ℝ≥0∞`-valued infima (`thrN`, `thrInf`; `inf ∅ = ∞`), so the finiteness hypothesis of
  (ii) is explicit and (iii) needs none.
* The restriction `p ↦ p∘t` to a closed support set can fail to be injective (e.g. finite `X`); the
  functional on `⋃ O_N ∘ t` is built through `LinearMap.quotKerEquivRange` and `Submodule.liftQ`; the
  kernel condition is positivity applied to `±p` (no feasible odd test on `X`).

## Findings on the paper

1. `ds:cont` needs only real-analyticity of `v` on `(0,∞)` (Landau argument for the boundary of
   finiteness of the Laplace transform, then the identity theorem on `(0,∞)`), not holomorphy on
   `Re > 0`; the complex case is recovered (`ds_cont_complex`).
2. `ds:mom`: the Lean constant for the Laguerre family is `C = (1+w)/π` because `lagP_lower` is stated for
   `t ≥ 2(k+w)/π`. The hypotheses are weaker for larger `C`, and `(1+w)/π > (2+w)/(2π)`, so this does **not**
   prove the paper's clause that the Laguerre family satisfies them with `C_w = (2+w)/(2π)`; that clause (via the
   Gershgorin zero bound `z_j ≤ (2k+w)/(2π)` in the `t` variable) is not formalised, and `ds:mom` is partial for it.
   The conclusions of `ds:mom` for the Laguerre family hold (`ds_mom_laguerre`); only the constant differs.
3. `dsl:positive-ray`: the sum `ℝ + ⋃ O_N` need not be shown direct. `1 ∉ ⋃ O_N` is the contradiction
   hypothesis, and a functional vanishing on `⋃ O_N` with `L 1 = 1` exists by
   `Submodule.exists_dual_map_eq_bot_of_notMem`.
4. `ds:LP`(i), (b) ⇒ (a) holds for every `X`, not only closed `X ⊂ (0,∞)`.
5. `ds:LP`(ii) and (iii) never use `e^{-2πt} O_N ⊂ Ā_w`.
6. The functional `L` must descend through the (possibly non-injective) restriction `p ↦ p∘t|_X`;
   Lean does this with a quotient (`LinearMap.quotKerEquivRange`, `Submodule.liftQ`). The paper already
   says it (`dual_spectrum_limit.tex`, Section `dsl:moment-common`: a `p` vanishing on `X` has `L(p) = 0`
   by positivity applied to both signs), so no TeX change is needed.

## Next steps

* `sd:LP` (SPIN-D): use `ds_LP_i/ii/iii` at the charge-dependent fixed weight and `ds_cont_complex`
  for the spin-dependent source.
* Optional corollary not formalised: for compact `F ⊂ (0,∞)` with `T_V > 0`,
  `T_F^{[∞]} = constrainedThreshold prob cTilde F` (from `theorem_E_b_compact`, `ds_LP_i` and
  `ds_LP_b_imp_a`).
