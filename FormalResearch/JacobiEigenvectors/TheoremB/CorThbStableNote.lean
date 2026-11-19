module

public import Mathlib

/-!
# Paper J, Theorem B, L3.D: statement and Mathlib gap report for `cor:thb-stable` (not formalised)

This module contains no declarations.  It records the exact statement and the missing inputs, so
that L3.D can start from here.  Source: Paper J, `thmB.tex`, Section `sec:thb-stable`
(`cor:thb-stable`), after Bhatia-Davis-McIntosh (1983).

## Statement (`cor:thb-stable`)

Assume the hypotheses of Theorem B (`ThmB`), let `K >= 0`, and let `J'_h` be any Hermitian
`(N+1) x (N+1)` matrix with `‖J'_h - J_h‖ <= K h^(m+1)` (neither tridiagonal nor real is needed).
For `0 < h <= h'_m(K)`, with `h'_m(K) <= h_m` and below the threshold of `cor:eigen (c)` (gaps
`X_{k} - X_{k+1} >= c h`), the eigenvalues `X'_0 > ... > X'_N` of `J'_h` are simple, and for every
unitary eigenvector matrix `U'_h` of `J'_h` (columns ordered as the eigenvalues) there is a diagonal
unitary `Δ` with `‖Ĝ_m - U'_h Δ‖_op <= (C_m + C_* K) h^m`, where `C_*` depends only on the gap
constant `c`.  If `J'_h` is a real Jacobi matrix with positive off-diagonal entries and `U'_h` is
taken in the gauge `(Ψ'_k)_0 > 0` (`IsEigenSystem`), then `Δ = I`.

## Proof outline (all steps are elementary but none is in Mathlib)

Put `γ = c h`, `ε = ‖J' - J‖ <= K h^(m+1)`, and take `h` so small that `ε <= γ/8`, `η <= 1/2`.

1. **Weyl**: `|X'_k - X_k| <= ε` (sorted eigenvalues of Hermitian matrices); hence the `X'_k` are simple
   and `|X_j - X'_k| >= γ - ε > γ/2` for `j ≠ k`.
2. **Fourier-Schur multiplier**: fix an even `χ ∈ C^∞` with `χ = 0` on `[-1/4, 1/4]`, `χ = 1` outside
   `(-1/2, 1/2)`; `f(x) = χ(x)/x`, so `f, f' ∈ L²` and `f̂ ∈ L¹`; `f_γ(x) = γ^(-1) f(x/γ)`,
   `‖f̂_γ‖_1 = γ^(-1) ‖f̂‖_1`.  With `Λ = diag X`, `Λ' = diag X'`, `V = U^* U'`, `E = U^*(J - J')U'`:
   `Λ V - V Λ' = E`, `‖E‖ <= ε`, and since `f_γ(X_j - X'_k) = 1/(X_j - X'_k)` (`j ≠ k`), `0` (`j = k`),
   `V - diag V = (f_γ(X_j - X'_k) E_jk) = (1/2π) ∫ f̂_γ(t) e^{itΛ} E e^{-itΛ'} dt`,
   so `‖V - diag V‖ <= η := c_f ε / γ`, `c_f = ‖f̂‖_1/(2π)`.
3. **Columns**: each column of `V` is a unit vector, so `|V_kk| >= (1 - η²)^(1/2)`; with
   `Δ* = diag(V_kk/|V_kk|)`, `‖VΔ - I‖ <= η + 1 - (1-η²)^(1/2) <= 2η`.  Hence
   `‖U'Δ - U‖ <= 2 c_f K h^m / c` and the claim follows from `ThmB` with `C_* = 2 c_f / c`.
4. **Jacobi gauge**: `J(t) = (1-t) J + t J'` is a real Jacobi matrix with positive off-diagonals and
   `‖J(t) - J‖ <= ε`; the eigenvectors with positive first entry are continuous in `t` (simple
   eigenvalues, first entry nonzero by the recurrence), `V(t)_kk` is real, continuous,
   `|V(t)_kk| >= (1-η²)^(1/2) > 0`, equal to `1` at `t = 0`, hence positive at `t = 1`: `Δ = I`.

## Mathlib audit (grep of `.lake/packages/mathlib`, current pin)

Missing, to be built for L3.D:
* **Weyl's inequality** for sorted eigenvalues of Hermitian matrices (`|λ_k(A) - λ_k(B)| <= ‖A - B‖`):
  no `Weyl`/min-max/Courant-Fischer eigenvalue-perturbation statement exists (only
  `Analysis/InnerProductSpace/Rayleigh.lean`: Rayleigh quotient extrema, and
  `Analysis/Matrix/Spectrum.lean`: `eigenvalues`, `trace_eq_sum_eigenvalues`).  Step 1 can instead be
  done through the Rayleigh/min-max characterisation by hand, or avoided: for the *given* gap
  structure only `|X_j - X'_k| >= γ/2` for `j ≠ k` and simplicity are needed, which Weyl provides.
* **Davis-Kahan / sin-Theta / Sylvester-equation bounds**: none (`grep Sylvester` only hits unrelated
  algebra: resultants, Monge point, echelon tactic).  The Fourier-Schur argument of step 2 replaces
  them; it needs `f̂ ∈ L¹` for `f = χ/x` (Fourier transform on `ℝ`: `Analysis/Fourier/FourierTransform.lean`,
  `FourierTransformDeriv.lean`, `Inversion.lean`: Fourier inversion and `L¹` of the transform of an
  `L²` function with `L²` derivative are NOT directly available; a smooth-cutoff construction or a
  finite-difference decomposition of the multiplier would be needed), and the unitary-conjugation
  identity `e^{itΛ} E e^{-itΛ'}` entrywise (`Complex.exp` of a diagonal, no Mathlib lemma for the
  entrywise integral of a matrix-valued function against `f̂_γ`, but Bochner integral commutes with
  entry projection).
* **Continuity of eigenvectors in the Jacobi gauge** (step 4): `Charts`-free; Paper J's own
  `Spectral`/`Jacobi` setting has `IsEigenSystem` (orth, eig, strict antitone, positive first entry)
  but no continuity/uniqueness of the gauge; this needs a uniqueness lemma (a simple eigenvalue's unit
  eigenvector with positive first entry is unique) plus a continuity-of-projection argument.

Order of work recommended: Weyl (Rayleigh), Schur-multiplier bound `‖(f(X_j - X'_k) E_jk)‖ <= ‖f̂‖_1/(2π) ‖E‖`
(any `f` with `f̂ ∈ L¹`; abstract lemma), `f̂_γ ∈ L¹` for the concrete `f`, assembly `cor:thb-stable`,
then the Jacobi-gauge continuity.  `CorThbDm` (`TheoremB/Statements.lean`, F-B6) uses this corollary
with `J_h := J̃_h` (the `(D_m)` jet-truncated matrix) and `J'_h := J_h`; it is not started (L3.Dm
waits for L3.5c).
-/
