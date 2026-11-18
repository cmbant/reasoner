module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryStatements

/-!
# Paper J, Layer 2: statement freeze for the eigenvalue location (Step 0) and cor:eigen (a)--(d)

Source: Paper J `app_thmA.tex` (Step 0 of Section "The soft edges: proof of Proposition prop:tha-W2"), `main_results.tex` `cor:eigen`, `thmA.tex` Section "Inverse quantisation, gaps and counting" (its proof),
`thmA.tex` `def:tha-Psihat` and its proof of thm:A (ii) ("the three cases exhaust `0 <= k <= N`").
**Every statement is a Prop-valued `def`; nothing is proved here (no placeholder proofs, no added axioms).**  Plan items L2.C8 (Step 0) and L2.E (cor:eigen) of `PLAN.md`; they use `ThmAi` / `EigenRule` of
`Statements.lean` (thm:smo-spec) and `GeometryStatements.lean` (lem:tha-geom).

## Dictionary

| Lean | paper | content |
|---|---|---|
| `StepZero` | app_thmA Step 0 | under `StdAssump` (compact `K`, `(E_Kd)`, (H1)--(H3)) every eigenvalue of `J_h(mu)` lies in `[X_s^- - C h^2, X_s^+ + C h^2]` |
| `StepZeroD0` | cor:eigen proof, Step 4/6 ("within `C h` of the band") | the same under `(D_0)` only, with `C h` |
| `SpectrumCovered` | proof of thm:A (ii) ("Step 0 ... so the three cases exhaust `0 <= k <= N`") | every eigenvalue falls in a bulk block, or above `J_hi` within the window `delta_0` of the upper soft chart, or below `J_lo` within the window of the lower soft chart |
| `CorEigenS1` | cor:eigen (a) | `S_1 = d_t S_0^{(t)}|_{t=0} = int_{u_-}^{u_+} (B_1 + (X - B_0) G_1/(2 G_0)) T^{-1/2} du` |
| `CorEigenInverse`, `InvExpansion` | cor:eigen (b) | `S_0' < 0`, the soft-edge values, `F_M(., h)` strictly decreasing, unique inverse `hat X_{k,M}`, `|X_k - hat X_{k,M}| <= C h^{M+1}`, the expansion `x_r`, `x_1`, `x_2` |
| `CorEigenGap1`, `CorEigenGapM` | cor:eigen (c) | `X_k - X_{k+1} = pi h/(-S_0'(x_0(y_k))) + O(h^2)`, `c h <= X_k - X_{k+1} <= C h`; and the expansion in `d_p` |
| `CorEigenCount` | cor:eigen (d) | `|#{k : X_k > X} - S_0(X)/(pi h)| <= C` and the Lipschitz density-of-states bound |

## Conventions (what the statements fix)

* Eigen-systems are universally quantified (`IsEigenSystem`: eigenvalues `X_0 > ... > X_N`, gauge `(Psi_k)_0 > 0`); `y_k := pi h (k + 1/2)`; `h = F.step N`; every statement is for all `N` with `h <= h_*`.
* **Constants before `mu`** (`C, c, h_*, delta'` do not depend on `mu in K`, `X`, `N`, `k`), as in `Statements.lean`.
* `S` is *any* family with `SmoothExt` and `EigenRule` and `ActionFormula` (the functions of thm:A (i) and their extensions; they are unique on the band, `ThmSmoSpec`); the statements are then about this `S`, so
  no existence claim is repeated (that is `ThmAi`).  The extension to `[X_s^- - delta, X_s^+ + delta]` is used only in (b) (the interval `I'`).
* `S_1` in (a) is evaluated on the **open** band; the integral formula is asserted together with its interval integrability (the integrand has an integrable `T^{-1/2}` singularity at `u_pm`, also at collision
  energies where `u_- = 0` or `u_+ = L`).  Continuity of `S_1` on the closed band is part of `SmoothExt` (`C^{M+1}` on a neighbourhood).
* Step 0 is stated for a *family* (parameter set `P`): applied to `frozenFamily F Kidx` on `paramSet K t0` it covers `J_h^{(t)}` for every `|t| <= t0` and, at `t = h`, `J_h` itself
  (`frozenFamily_jacobiMat_at_step`); the band is then that of the frozen principal symbols (`SpectrumCovered`).

## FINDINGS

* **F-E1 (Step 0 is relative to the frozen band)**: `J_h = J_h^{(h)}`, whose principal symbols are `G_0 + h G_1`, `B_0 + h B_1`; so the eigenvalues are within `C h^2` of `[X_s^-(h), X_s^+(h)]`, which is `O(h)` from the band of `J_h`'s own
  principal symbols.  Hence "`X_k` in `[X_s^- - C h^2, X_s^+ + C h^2]`" (as written in the proof of thm:A (ii)) is true for the *frozen* band and only `O(h)` for the plain band; `StepZero` is stated for any family (take the
  frozen one) and `StepZeroD0` records the `O(h)` statement for the plain band that cor:eigen (b), (d) use.
* **F-E2 (cor:eigen (b), the interval `I'`)**: `F_M(., h)` is only claimed strictly decreasing on `I' = [X_s^- - delta', X_s^+ + delta']`; the eigenvalues lie in `I'` by `StepZeroD0` (`C h < delta'` for `h` small).  The statement `exactly one solution in I'`
  needs `delta' <= delta` (the domain of the extensions); that is part of the quantifier `exists delta'`.
* **F-E3 (cor:eigen (d), counting)**: the paper states the density-of-states bound for "every Lipschitz function on a fixed neighbourhood"; the sum `sum_k g(X_k)` needs `X_k` inside it, which is `StepZeroD0`; the Lean statement
  quantifies the neighbourhood radius `delta'` before `g` and the Lipschitz constant `Lg` explicitly.
* **F-E4 (cor:eigen (c) under `(D_1)` only)**: `x_0 in C^2`, `x_1 in C^1` are used; the first part needs only `x_0`, so `CorEigenGap1` quantifies an arbitrary inverse `x_0` of `S_0` and does not mention `x_1`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-! ### Step 0: where the eigenvalues are -/

/-- **Step 0** (app_thmA, statement): under the standing assumptions `StdAssump F P Kd r` (compact parameter set, `(E_Kd)`, (H1)--(H3)) there are `C, h_0` such that every eigenvalue of `J_h(p)`, `p in P`, `h <= h_0`, lies in
`[X_s^-(p) - C h^2, X_s^+(p) + C h^2]`.  (The upper bound is the quadratic-form estimate `<v, J_h v> <= sum (B_n + sqrt E_n + sqrt E_{n-1}) v_n^2` with the symmetric samples; the lower bound is the same in the gauge `(-1)^n`.) -/
def StepZero (F : SymbolFamily Par) (P : Set Par) (Kd r : ℕ) : Prop :=
  StdAssump F P Kd r →
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, F.step N ≤ h0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat p N) X Um →
        ∀ k : Fin (N + 1), F.bandLo p - C * F.step N ^ 2 ≤ X k ∧ X k ≤ F.bandHi p + C * F.step N ^ 2

/-- **Step 0 under `(D_0)` only** (used in cor:eigen (b), (d) and thm:smo-BSr): the eigenvalues lie within `C h` of the band of the principal symbols (`J_h - J^{[0]}_h` has operator norm `O(h)`,
`J^{[0]}_h` the samples of `G_0, B_0`, to which `StepZero` applies). -/
def StepZeroD0 (F : SymbolFamily Par) (K : Set Par) : Prop :=
  IsCompact K → HypOn F K → DM F K 0 →
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), F.bandLo μ - C * F.step N ≤ X k ∧ X k ≤ F.bandHi μ + C * F.step N

/-- **The three cases of `def:tha-Psihat` exhaust the spectrum, each inside its chart's range** (the use of Step 0 in the proof of thm:A (ii)): for the charts `CI` (at `t = h`, frozen band), every eigenvalue
`X_k` of `J_h` lies in some bulk block, or (not in a block and) above `J_hi` within the window `delta_0` of the upper soft chart's band edge, or (not in a block, not above `J_hi`) within the window of the lower soft chart.
This matches the case split of `psiHatVec` / `envVec` (first block, then upper, then lower) and is what lets `ThmAii` apply `PropThaW`/`PropThaW2` at `X = X_k`. -/
def SpectrumCovered {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) : Prop :=
  Kidx = (m + 1) / 2 → IsCompact K → HypOn F K → DM F K (2 * Kidx + 1) →
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1),
          (∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) ∨
          ((¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) ∧ CI.Jhi < X k ∧
            |X k - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CI.softUpL.δ0) ∨
          ((¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) ∧ ¬ CI.Jhi < X k ∧
            |-X k - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0)

/-! ### cor:eigen -/

/-- **cor:eigen (a)** (statement): under `(D_1)`, for the `S_j` of thm:A (i) at `M = 1`: on the open band `S_1(X) = d/dt S_0^{(t)}(X)|_{t=0}` (`S_0^{(t)}` = the action of the principal symbols `G_0 + t G_1`, `B_0 + t B_1`, i.e.
`actionS0 (frozenFamily F 0) (mu, t) X`) and `S_1(X) = int_{u_-}^{u_+} (B_1 + (X - B_0) G_1/(2 G_0)) T^{-1/2} du`, an absolutely convergent integral (also at the collision energies). -/
def CorEigenS1 (F : SymbolFamily Par) (K : Set Par) : Prop :=
  IsCompact K → HypOn F K → DM F K 1 →
    ∀ (S : ℕ → Par → ℝ → ℝ) (δ Cn hM C : ℝ), SmoothExt F K 1 S δ Cn → EigenRule F K 1 S hM C → ActionFormula F K S →
      ∀ μ ∈ K, ∀ X ∈ Ioo (F.bandLo μ) (F.bandHi μ),
        HasDerivAt (fun t : ℝ => actionS0 (frozenFamily F 0) (μ, t) X) (S 1 μ X) 0 ∧
        IntervalIntegrable (fun u => (F.B 1 μ u + (X - F.B 0 μ u) * F.G 1 μ u / (2 * F.G 0 μ u)) /
          Real.sqrt (Tfun F.L (F.G 0 μ) (F.B 0 μ) X u)) MeasureTheory.volume (F.uMinus μ X) (F.uPlus μ X) ∧
        S 1 μ X = ∫ u in (F.uMinus μ X)..(F.uPlus μ X), (F.B 1 μ u + (X - F.B 0 μ u) * F.G 1 μ u / (2 * F.G 0 μ u)) /
          Real.sqrt (Tfun F.L (F.G 0 μ) (F.B 0 μ) X u)

/-- The expansion data of the inverse quantisation (cor:eigen (b)): `x_r(mu; .) in C^{M+1-r}([0, pi L])`, `x_0` an inverse of `S_0` (`x_0(y) in [X_s^-, X_s^+]`, `S_0(x_0(y)) = y`), and the
eigenvalues `X_k = sum_{r <= M} h^r x_r(y_k) + O(h^{M+1})` uniformly in `mu in K`, `k`, `h <= h_0`, `y_k = pi h (k + 1/2)`.  (Such `x` is unique: the `y_k` become dense in `[0, pi L]`.) -/
def InvExpansion (F : SymbolFamily Par) (K : Set Par) (M : ℕ) (S : ℕ → Par → ℝ → ℝ) (x : ℕ → Par → ℝ → ℝ) : Prop :=
  (∀ μ ∈ K, ∀ r ≤ M, ContDiffOn ℝ ((M + 1 - r : ℕ) : WithTop ℕ∞) (x r μ) (Icc 0 (Real.pi * F.L))) ∧
  (∀ μ ∈ K, ∀ y ∈ Icc 0 (Real.pi * F.L), x 0 μ y ∈ Icc (F.bandLo μ) (F.bandHi μ) ∧ S 0 μ (x 0 μ y) = y) ∧
  ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
    ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
      ∀ k : Fin (N + 1),
        |X k - ∑ r ∈ range (M + 1), F.step N ^ r * x r μ (Real.pi * F.step N * ((k : ℕ) + 1 / 2))| ≤ C * F.step N ^ (M + 1)

/-- Part (i) of cor:eigen (b): `S_0' < 0` uniformly on the band and the soft-edge values `-S_0'(X_s^pm) = pi sqrt(2/(kappa_pm d_pm))`, `kappa_+ = -f_+''(u_c^+)`, `kappa_- = f_-''(u_c^-)`, `d_pm = 4 sqrt(E_0(u_c^pm))`. -/
def InvS0 (F : SymbolFamily Par) (K : Set Par) (S : ℕ → Par → ℝ → ℝ) : Prop :=
  (∃ c0 : ℝ, 0 < c0 ∧ ∀ μ ∈ K, ∀ X ∈ Set.Icc (F.bandLo μ) (F.bandHi μ), 2 * c0 ≤ -deriv (S 0 μ) X) ∧
  (∀ μ ∈ K, ∀ uc : ℝ, 0 < uc → uc < F.L → fPlus F.L (F.G 0 μ) (F.B 0 μ) uc = F.bandHi μ →
    deriv (S 0 μ) (F.bandHi μ) = -(Real.pi * Real.sqrt (2 / ((-deriv (deriv (fPlus F.L (F.G 0 μ) (F.B 0 μ))) uc) *
      (4 * Real.sqrt (E0 F.L (F.G 0 μ) uc)))))) ∧
  (∀ μ ∈ K, ∀ uc : ℝ, 0 < uc → uc < F.L → fMinus F.L (F.G 0 μ) (F.B 0 μ) uc = F.bandLo μ →
    deriv (S 0 μ) (F.bandLo μ) = -(Real.pi * Real.sqrt (2 / ((deriv (deriv (fMinus F.L (F.G 0 μ) (F.B 0 μ))) uc) *
      (4 * Real.sqrt (E0 F.L (F.G 0 μ) uc))))))

/-- Part (ii) of cor:eigen (b): the truncated action `F_M(., h)` is strictly decreasing on `I'` and its level equation at `y_k` has a unique solution in `I'`, within `C h^{M+1}` of `X_k`. -/
def InvLevel (F : SymbolFamily Par) (K : Set Par) (M : ℕ) (S : ℕ → Par → ℝ → ℝ) (δ : ℝ) : Prop :=
  ∃ δ' c Cc hs : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ 0 < c ∧ 0 < hs ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hs →
    (∀ X ∈ Set.Icc (F.bandLo μ - δ') (F.bandHi μ + δ'),
      c ≤ -∑ j ∈ range (M + 1), F.step N ^ j * deriv (S j μ) X) ∧
    ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
      ∀ k : Fin (N + 1), ∃ Xh ∈ Set.Icc (F.bandLo μ - δ') (F.bandHi μ + δ'),
        (∑ j ∈ range (M + 1), F.step N ^ j * S j μ Xh = Real.pi * F.step N * ((k : ℕ) + 1 / 2) ∧
          ∀ Y ∈ Set.Icc (F.bandLo μ - δ') (F.bandHi μ + δ'),
            ∑ j ∈ range (M + 1), F.step N ^ j * S j μ Y = Real.pi * F.step N * ((k : ℕ) + 1 / 2) → Y = Xh) ∧
        |Xs k - Xh| ≤ Cc * F.step N ^ (M + 1)

/-- Part (iii) of cor:eigen (b): the expansion data and the formulas for `x_1`, `x_2`. -/
def InvCoeffs (F : SymbolFamily Par) (K : Set Par) (M : ℕ) (S : ℕ → Par → ℝ → ℝ) : Prop :=
  ∃ x : ℕ → Par → ℝ → ℝ, InvExpansion F K M S x ∧
    (∀ μ ∈ K, ∀ y ∈ Set.Icc 0 (Real.pi * F.L),
      x 1 μ y = -S 1 μ (x 0 μ y) / deriv (S 0 μ) (x 0 μ y)) ∧
    (2 ≤ M → ∀ μ ∈ K, ∀ y ∈ Set.Icc 0 (Real.pi * F.L),
      x 2 μ y = -(S 2 μ (x 0 μ y) + deriv (S 1 μ) (x 0 μ y) * x 1 μ y +
        (1 / 2) * deriv (deriv (S 0 μ)) (x 0 μ y) * x 1 μ y ^ 2) / deriv (S 0 μ) (x 0 μ y))

/-- **cor:eigen (b)** (statement), `M >= 1`, `(D_M)`, for the `S` of thm:A (i): (i) `InvS0`; (ii) `InvLevel`; (iii) `InvCoeffs`. -/
def CorEigenInverse (F : SymbolFamily Par) (K : Set Par) (M : ℕ) : Prop :=
  1 ≤ M → IsCompact K → HypOn F K → DM F K M →
    ∀ (S : ℕ → Par → ℝ → ℝ) (δ Cn hM C : ℝ), SmoothExt F K M S δ Cn → EigenRule F K M S hM C → ActionFormula F K S →
      InvS0 F K S ∧ InvLevel F K M S δ ∧ InvCoeffs F K M S

/-- **cor:eigen (c), first part** (statement), `(D_1)`: for any inverse `x_0` of `S_0` on `[0, pi L]`, `X_k - X_{k+1} = pi h/(-S_0'(x_0(y_k))) + O(h^2)` and `c h <= X_k - X_{k+1} <= C h`,
uniformly in `mu in K`, `0 <= k < N`. -/
def CorEigenGap1 (F : SymbolFamily Par) (K : Set Par) : Prop :=
  IsCompact K → HypOn F K → DM F K 1 →
    ∀ (S : ℕ → Par → ℝ → ℝ) (δ Cn hM C : ℝ), SmoothExt F K 1 S δ Cn → EigenRule F K 1 S hM C → ActionFormula F K S →
      ∀ x0 : Par → ℝ → ℝ, (∀ μ ∈ K, ∀ y ∈ Icc 0 (Real.pi * F.L), x0 μ y ∈ Icc (F.bandLo μ) (F.bandHi μ) ∧ S 0 μ (x0 μ y) = y) →
        ∃ C1 c1 C2 h0 : ℝ, 0 < h0 ∧ 0 < c1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
          ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
            ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 →
              |(X i - X j) - Real.pi * F.step N / (-deriv (S 0 μ) (x0 μ (Real.pi * F.step N * ((i : ℕ) + 1 / 2))))| ≤ C1 * F.step N ^ 2 ∧
              c1 * F.step N ≤ X i - X j ∧ X i - X j ≤ C2 * F.step N

/-- **cor:eigen (c), general order** (statement), `M >= 1`, `(D_M)`: for the expansion data `x` of (b), `X_k - X_{k+1} = sum_{p=1}^M h^p d_p(y_k) + O(h^{M+1})` with
`d_p := - sum_{r=0}^{p-1} pi^{p-r}/(p-r)! x_r^{(p-r)} in C^{M+1-p}([0, pi L])`. -/
def CorEigenGapM (F : SymbolFamily Par) (K : Set Par) (M : ℕ) : Prop :=
  1 ≤ M → IsCompact K → HypOn F K → DM F K M →
    ∀ (S : ℕ → Par → ℝ → ℝ) (δ Cn hM C : ℝ), SmoothExt F K M S δ Cn → EigenRule F K M S hM C → ActionFormula F K S →
      ∀ x : ℕ → Par → ℝ → ℝ, InvExpansion F K M S x →
        ∃ d : ℕ → Par → ℝ → ℝ,
          (∀ μ ∈ K, ∀ p ∈ Finset.Icc 1 M, ContDiffOn ℝ ((M + 1 - p : ℕ) : WithTop ℕ∞) (d p μ) (Set.Icc 0 (Real.pi * F.L)) ∧
            ∀ y ∈ Icc 0 (Real.pi * F.L), d p μ y =
              -∑ r ∈ range p, Real.pi ^ (p - r) / ((p - r).factorial : ℝ) * iteratedDerivWithin (p - r) (x r μ) (Icc 0 (Real.pi * F.L)) y) ∧
          ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
            ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
              ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 →
                |(X i - X j) - ∑ p ∈ Finset.Icc 1 M, F.step N ^ p * d p μ (Real.pi * F.step N * ((i : ℕ) + 1 / 2))| ≤ Cc * F.step N ^ (M + 1)

/-- **cor:eigen (d)** (statement), `(D_0)` only: uniformly in `Y in [X_s^-, X_s^+]`, `|#{k : X_k > Y} - S_0(Y)/(pi h)| <= C`; and there is `delta' > 0` such that for every `g` Lipschitz
(constant `Lg >= 0`) on `[X_s^- - delta', X_s^+ + delta']`, `|(h/L) sum_k g(X_k) - (1/(pi L)) int_{X_s^-}^{X_s^+} g(X) (-S_0'(X)) dX| <= C h Lg`. -/
def CorEigenCount (F : SymbolFamily Par) (K : Set Par) : Prop :=
  IsCompact K → HypOn F K → DM F K 0 →
    ∀ (S : ℕ → Par → ℝ → ℝ) (δ Cn hM C : ℝ), SmoothExt F K 0 S δ Cn → EigenRule F K 0 S hM C → ActionFormula F K S →
      (∃ C1 h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
        ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
          ∀ Y ∈ Icc (F.bandLo μ) (F.bandHi μ),
            |(Set.ncard {k : Fin (N + 1) | Y < X k} : ℝ) - S 0 μ Y / (Real.pi * F.step N)| ≤ C1) ∧
      (∃ δ' : ℝ, 0 < δ' ∧ ∃ C1 h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
        ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
          ∀ (g : ℝ → ℝ) (Lg : ℝ), 0 ≤ Lg →
            (∀ a ∈ Icc (F.bandLo μ - δ') (F.bandHi μ + δ'), ∀ b ∈ Icc (F.bandLo μ - δ') (F.bandHi μ + δ'), |g a - g b| ≤ Lg * |a - b|) →
              |F.step N / F.L * ∑ k : Fin (N + 1), g (X k) -
                1 / (Real.pi * F.L) * ∫ Y in (F.bandLo μ)..(F.bandHi μ), g Y * (-deriv (S 0 μ) Y)| ≤ C1 * F.step N * Lg)

/-- cor:eigen as a whole, for a family on `K` (`Mmax` the largest order used). -/
def CorEigen (F : SymbolFamily Par) (K : Set Par) (M : ℕ) : Prop :=
  CorEigenS1 F K ∧ CorEigenInverse F K M ∧ CorEigenGap1 F K ∧ CorEigenGapM F K M ∧ CorEigenCount F K

end FormalResearch.JacobiEigenvectors.TheoremA
