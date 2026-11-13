# Vendored: girving/interval (Euler-Maclaurin formula and Stirling series for `log Gamma`)

- Upstream: https://github.com/girving/interval
- Commit: 2c89204b806f4acd9b8530a38e656369d0a4d7f3 (Lean `v4.34.1`, `module` system)
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

None. The sources build unmodified against the pinned Mathlib
(`5ed2965256430c3649e86755f9576b54eca72435`; upstream pins the `v4.34.1` tag,
`d13f23b723b8a846827a245b89c10fc7d3f11612`).

Build setup (not a source change): the `[[lean_lib]] Interval` entry in `lakefile.toml` sets
`leanOptions = {autoImplicit = false, relaxedAutoImplicit = false}`, as upstream's `lakefile.toml`
does for its package.

## Checks

- `lake build Interval.EulerMaclaurin.Gamma` succeeds.
- No `sorry`, `native_decide` or `axiom` appears anywhere in the vendored files.

## Caveat

Upstream declares its definitions in the root namespace (`term`, `sum`, `rem`, `const`, `pre_n`, ...,
and lemmas such as `log_gamma_em`). Importing `Interval.EulerMaclaurin.Gamma` therefore puts these
names in the root namespace; refer to `_root_.sum` / `_root_.rem` where they could be confused with
`Finset.sum`, `Nat.rem`-style names.
