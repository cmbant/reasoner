# Vendored: girving/interval (Euler-Maclaurin formula and Stirling series for `log Gamma`)

- Upstream: https://github.com/girving/interval
- Commit: 2c89204b806f4acd9b8530a38e656369d0a4d7f3 (Lean `v4.34.1`, `module` system; still upstream `HEAD` when checked for the 4.35 upgrade, so no 4.35-compatible upstream version exists to re-vendor)
- Licence: Apache-2.0 (`LICENSE`, copied verbatim from upstream; upstream has no separate `NOTICE`).

Only the import closure of `Interval.EulerMaclaurin.Gamma` is included: the ten files of
`Interval/EulerMaclaurin/` (2261 lines). They import no other `Interval.*` module, only Mathlib.
Nothing else from upstream is vendored.

Files (all under `Interval/EulerMaclaurin/`): `Bernoulli.lean`, `DerivUnderIntegral.lean`,
`EulerMaclaurin.lean`, `Formula.lean`, `Gamma.lean`, `IteratedDerivArith.lean`, `LHopital.lean`,
`PartialDerivCommute.lean`, `PeriodizedBernoulli.lean`, `RemainderBound.lean`.

Used by `FormalResearch/Special/GammaRatio.lean`, which uses `log_gamma_em` (the Stirling series for
`log Gamma` with an exact remainder `rem`), `const_eq` and `abs_rem_le'`.

## Patches

Patched for Lean 4.35 / Mathlib v4.35.0 (`56a005855ea17e0b0958f73ec801ae140b0a1679`; upstream pins the `v4.34.1` tag,
`d13f23b723b8a846827a245b89c10fc7d3f11612`). One file, one line, marked with a `-- PATCH` comment:

- `Interval/EulerMaclaurin/RemainderBound.lean`: added `public import Mathlib.Analysis.PSeries`. Under the module
  system this file used `Real.summable_one_div_nat_pow` without importing it, and under Mathlib v4.35.0 it is no longer
  in the transitive imports of `Mathlib.Analysis.Real.Pi.Bounds`. No statement or proof changed. (This file is not in the
  import closure of `Interval.EulerMaclaurin.Gamma`; only `lake build Interval` builds it.)

The other nine files are byte-identical to upstream and build unchanged.

Build setup (not a source change): the `[[lean_lib]] Interval` entry in `lakefile.toml` sets
`leanOptions = {autoImplicit = false, relaxedAutoImplicit = false}`, as upstream's `lakefile.toml`
does for its package.

## Checks

- `lake build Interval` (all ten files) and `lake build Interval.EulerMaclaurin.Gamma` succeed.
- No `sorry`, `native_decide` or `axiom` appears anywhere in the vendored files.

## Caveat

Upstream declares its definitions in the root namespace (`term`, `sum`, `rem`, `const`, `pre_n`, ...,
and lemmas such as `log_gamma_em`). Importing `Interval.EulerMaclaurin.Gamma` therefore puts these
names in the root namespace; refer to `_root_.sum` / `_root_.rem` where they could be confused with
`Finset.sum`, `Nat.rem`-style names.
