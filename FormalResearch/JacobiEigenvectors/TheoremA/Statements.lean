module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Comparison

/-!
# Paper J, Layer 2: statement freeze for Theorem A and its propositions

Source: Paper J `main_results.tex` (thm:A, thm:B hypotheses, lem:hyp-morse), `thmA.tex` (lem:tha-geom, prop:tha-W, prop:tha-W2, prop:l2jets,
thm:smo-spec, thm:tha-BS), `app_thmA.tex` (lem:tha-win, lem:tha-M, lem:tha-count, lem:smo-bulkphase, thm:smo-BSr).

**Every statement is a Prop-valued `def`; nothing is proved, and there are no placeholder proofs and no added axioms.**  Each is to be proved later from the engine
(`LadderData.Stability`) and the chart hypotheses (`ChartInputs`); the hypotheses of a statement are its arguments (charts) and, as the premise of the
implication, the setting hypotheses (`StdAssump`: compactness, `(E_K)`, `(H1)`--`(H3)`).  The proof obligations and dependency DAG are in `PLAN.md`.

## Dictionary

| Lean | paper | hypotheses |
|---|---|---|
| `StdAssump` | "Assume (E_K) and (H1)--(H3)", compact parameter set | -- |
| `FrozenStandard` | sec:tha-standing: frozen family satisfies `(E_K)`, (H1)--(H3) uniformly in `|t| <= t0` | `DM F K (2 Kidx+1)` |
| `HypMorseEquiv`, `HypOpen` | lem:hyp-morse | `C^2` symbols |
| `ThmAi` | thm:A (i) | `DM F K M` |
| `ThmAii` | thm:A (ii) | `ChartInputs` at `(m, q = 2 ceil(m/2))`, `DM F K (2 ceil(m/2)+1)` |
| `BulkSolutionBound`, `PropThaW` | prop:tha-W (1), (2) | bulk charts, `EK (floor(m/2))` |
| `PropThaW2` | prop:tha-W2 (1)--(4) (`Lm = 1`, or `Lm h = log(1/h)` for item (4)) | soft charts, `EK (q/2)` |
| `PropThaWin` | lem:tha-win (1), (2), (3), (5) | soft chart |
| `PropThaM` | lem:tha-M | soft chart |
| `PropThaCount` | lem:tha-count | none (Jacobi recurrence only) |
| `PropL2Jets` | prop:l2jets | `ChartInputs` for the truncated family, `DM F K m` |
| `ThmSmoSpec` | thm:smo-spec (existence, uniqueness, extensions) | `ChartInputs` at order `max M 1`, `BulkPhaseInputs` |

## Quantifier structure (what constants depend on, uniformity in what)

In every statement the constants `C, h_0, ...` are chosen **after** the chart data and **before** `mu in K` (or `p in P`), `X`, `N`, `k`, `n`:
`exists C h0, forall p in P, forall X, forall N >= N0, step N <= h0 -> ...`.  They may depend on `m`, `q`, the margins fixed by the chart structures (the chart
constants are fields) and the norms in `EK`/`DM`; not on `p`, `X`, `N`, `k`, `n`.  The collar statement of prop:tha-W is the exception: its constant depends on the
collar width `delta`.  For `ThmAii`, `delta`, `t0` are chart data.  Eigen-systems are universally quantified (`IsEigenSystem`).

## FINDINGS (paper statements made precise or corrected here; recorded in `PLAN.md` too)

* **F-A1 (index conventions, thm:A(i))**: eq:BS holds for the *labels* `k` counted from the top, with `S_j` given on a `delta`-neighbourhood: `ThmAi` fixes that the
  extension, its `C^{M+1}` norm and `delta` are uniform in `mu`, as the paper says; but the rule is only claimed for `h <= h_M` -- here `exists h_M`, and `N` ranges over *all*
  `N` with `L/(N+1) <= h_M`.
* **F-A2 (quantifiers of thm:A(ii))**: "there are explicit vectors" is vacuous unless the vector is a specific function of the charts; `ThmAii` is stated for the
  specific `psiHatVec`/`envVec` of `Comparison.lean` (not an existential), and the relative error on collars is a separate conjunct with `delta`-dependent constant (`PropThaW`).
* **F-geom (lem:tha-geom (c), single overlap)**: the lemma asserts one pair `c' < c` with `u_-(X) + delta_1 <= c' < c <= u_+(X) - delta_1` for *all* `X` in a compact `J`; this is false in general
  (if `u_c^+ < u_c^-`, `sup_J u_- > inf_J u_+`).  It is true per energy, hence on each interval of a finite cover (as Lemma smo-bulkphase and Section thb-matrices already do).  The Lean
  statements use bulk *blocks* (`ChartInputs.nb, lo, hi`, one `BulkWeberChart` per block, each with its own overlap `[c', c]`); prop:tha-W and thm:A(ii) are stated per block / for the vector of a block containing `X_k`.
* **F-A3 (def:tha-Psihat, case split)**: the three cases are decided by the *value* of `X_k` (`[Jlo,Jhi]`, `> Jhi`, `< Jlo`); that they exhaust the eigenvalues is Step 0 of app_thmA
  (`ChartInputs.cover` plus eigenvalue location `|X_k - [X_s^-, X_s^+]| <= C h^2`), a separate obligation (`StepZero` in `PLAN.md`), not part of `ThmAii`'s statement.
* **F-A4 (prop:tha-W2 (3))**: "for some integer `k >= 0`" and "the `k`-th eigenvalue counted from the top is the one in window `k`" are merged into one clause
  (`label`): the label equals the eigenvalue index.  The converse (each window with nominal point inside `delta_0/2` contains an eigenvalue) is stated as existence of the
  eigenvalue of index `k`.
* **F-A5 (prop:tha-splice (c) / (I1) at order `m+1`)**: see `TheoremB/Statements.lean`.
* **F-A6 (thm:smo-spec, the `S_j` are `C^{M+1}` "through the collisions")**: `ThmAi` states `C^{M+1}` on a *closed interval containing* the collision energies, uniformly in `mu`
  (no separate statement at the collisions).
* **F-A7 (lem:tha-count)**: the paper's lemma says "`I` an interval"; `PropThaCount` needs `I.OrdConnected`, and (ii)/(iii) quantified over all real `kappa'` with `p = kappa' q`
  (unique if `q` is not identically zero).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-- The standing assumptions of Sections 4.2--4.5: compact parameter set, `(E_K)` (which contains the jet regularity and the remainder), and (H1)--(H3). -/
def StdAssump (F : SymbolFamily Par) (P : Set Par) (Kd r : ℕ) : Prop :=
  IsCompact P ∧ EK F P Kd r ∧ HypOn F P

/-- The action `S_0(X) = int_0^L Re arccos((X - B_0)/(2 sqrt E_0)) du` (eq:S0). -/
def actionS0 (F : SymbolFamily Par) (μ : Par) (X : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..F.L, Real.arccos ((X - F.B 0 μ u) / (2 * Real.sqrt (E0 F.L (F.G 0 μ) u)))

/-! ### Hypotheses: Morse form, openness, freezing -/

/-- **lem:hyp-morse** (statement): for `C^2` symbols with `(H1)`, `(H2) & (H3)` hold iff `(M)`: `f_+` has exactly one critical point in `(0,L)`, with `f_+'' < 0`, and `f_-` exactly one,
with `f_-'' > 0`. -/
def HypMorseEquiv : Prop :=
  ∀ (L : ℝ) (G0 B0 : ℝ → ℝ) (g : ℝ), 0 < L → 0 < g → (∀ u ∈ Set.Icc 0 L, g ≤ G0 u) →
    ContDiffOn ℝ 2 G0 (Set.Icc 0 L) → ContDiffOn ℝ 2 B0 (Set.Icc 0 L) →
    ((∃ uc ∈ Set.Ioo 0 L, {u ∈ Set.Ioo 0 L | deriv (fPlus L G0 B0) u = 0} = {uc} ∧ deriv (deriv (fPlus L G0 B0)) uc < 0) ∧
      (∃ uc ∈ Set.Ioo 0 L, {u ∈ Set.Ioo 0 L | deriv (fMinus L G0 B0) u = 0} = {uc} ∧ 0 < deriv (deriv (fMinus L G0 B0)) uc)
      ↔ ((∀ X, Xsm L G0 B0 < X → X < Xsp L G0 B0 →
            ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ L ∧ (Set.Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u}) = Set.Icc a b ∧
              (0 < a → deriv (Tfun L G0 B0 X) a ≠ 0) ∧ (b < L → deriv (Tfun L G0 B0 X) b ≠ 0) ∧
              (a = 0 → X = B0 0) ∧ (b = L → X = B0 L)) ∧
          (∃ uc, 0 < uc ∧ uc < L ∧ (∀ u ∈ Set.Icc 0 L, fPlus L G0 B0 u = Xsp L G0 B0 ↔ u = uc) ∧ deriv (deriv (fPlus L G0 B0)) uc < 0) ∧
          (∃ uc, 0 < uc ∧ uc < L ∧ (∀ u ∈ Set.Icc 0 L, fMinus L G0 B0 u = Xsm L G0 B0 ↔ u = uc) ∧ 0 < deriv (deriv (fMinus L G0 B0)) uc)))

/-- **lem:hyp-morse, openness** (statement): `(H1)` with `g` together with `(H2)`, `(H3)` persists, with lower bound `g/2`, under every change of `(G_0, B_0)` that is small in `C^2([0,L])`. -/
def HypOpen : Prop :=
  ∀ (L : ℝ) (G0 B0 : ℝ → ℝ) (g : ℝ), Hyp L G0 B0 g → ContDiffOn ℝ 2 G0 (Set.Icc 0 L) → ContDiffOn ℝ 2 B0 (Set.Icc 0 L) →
    ∃ ε > 0, ∀ G0' B0' : ℝ → ℝ, ContDiffOn ℝ 2 G0' (Set.Icc 0 L) → ContDiffOn ℝ 2 B0' (Set.Icc 0 L) →
      (∀ i ≤ 2, ∀ u ∈ Set.Icc 0 L, |iteratedDerivWithin i G0' (Set.Icc 0 L) u - iteratedDerivWithin i G0 (Set.Icc 0 L) u| ≤ ε ∧
        |iteratedDerivWithin i B0' (Set.Icc 0 L) u - iteratedDerivWithin i B0 (Set.Icc 0 L) u| ≤ ε) →
      Hyp L G0' B0' (g / 2)

/-- **sec:tha-standing** (statement): if `(D_{2 Kidx+1})` and (H1)--(H3) hold on a compact `K`, there is `t0 > 0` such that the frozen family satisfies `(E_Kidx)`, (H1)--(H3), with
uniform margins on `K x [-t0,t0]`. -/
def FrozenStandard (F : SymbolFamily Par) (K : Set Par) (Kidx : ℕ) : Prop :=
  IsCompact K → HypOn F K → DM F K (2 * Kidx + 1) →
    ∃ t0 : ℝ, 0 < t0 ∧ ∃ r : ℕ, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r

/-! ### thm:smo-spec and thm:A (i): the eigenvalue rule -/

/-- The rule eq:smo-specBS for a candidate family `S` of coefficient functions: `sum_{j<=M} h^j S_j(X_k) = pi h (k + 1/2) + O(h^{M+1})`, uniformly in `mu in K`, `k`, and all `N` with `h <= hM`. -/
def EigenRule (F : SymbolFamily Par) (K : Set Par) (M : ℕ) (S : ℕ → Par → ℝ → ℝ) (hM C : ℝ) : Prop :=
  0 < hM ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hM → ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
    IsEigenSystem (F.jacobiMat μ N) X Um → ∀ k : Fin (N + 1),
      |∑ j ∈ range (M + 1), F.step N ^ j * S j μ (X k) - Real.pi * F.step N * ((k : ℕ) + 1 / 2)| ≤ C * F.step N ^ (M + 1)

/-- `S_j(mu; .)` is `C^{M+1}` on `[X_s^- - delta, X_s^+ + delta]` with `C^{M+1}` norm `<= Cn`, for `j <= M`, `mu in K`. -/
def SmoothExt (F : SymbolFamily Par) (K : Set Par) (M : ℕ) (S : ℕ → Par → ℝ → ℝ) (δ Cn : ℝ) : Prop :=
  ∀ μ ∈ K, ∀ j ≤ M, ContDiffOn ℝ (M + 1 : ℕ) (S j μ) (Set.Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) ∧
    ∀ i ≤ M + 1, ∀ x ∈ Set.Icc (F.bandLo μ - δ) (F.bandHi μ + δ),
      |iteratedDerivWithin i (S j μ) (Set.Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) x| ≤ Cn

/-- `S_0 = ` eq:S0 on `[X_s^-, X_s^+]`. -/
def ActionFormula (F : SymbolFamily Par) (K : Set Par) (S : ℕ → Par → ℝ → ℝ) : Prop :=
  ∀ μ ∈ K, ∀ X ∈ Set.Icc (F.bandLo μ) (F.bandHi μ), S 0 μ X = actionS0 F μ X

/-- **Theorem A (i)** (= thm:smo-spec, existence part): `(H1)`--`(H3)` and `(D_M)` give `delta, h_M > 0` independent of `mu` and `C^{M+1}` functions `S_0, ..., S_M`
with `C^{M+1}` norms bounded uniformly in `mu`, `S_0` the action, with the rule for every `k` and every eigen-system, uniformly in `mu`. -/
def ThmAi (F : SymbolFamily Par) (K : Set Par) (M : ℕ) : Prop :=
  IsCompact K → HypOn F K → DM F K M →
    ∃ (δ Cn C hM : ℝ) (S : ℕ → Par → ℝ → ℝ), 0 < δ ∧ SmoothExt F K M S δ Cn ∧ ActionFormula F K S ∧ EigenRule F K M S hM C

/-- **thm:smo-spec** (statement, existence, uniqueness and extension independence), derived from the charts at order `max M 1` and the phase inputs (`q = 2 ceil(M/2)`):
besides `ThmAi`, (b) two families `S, S'` with `SmoothExt` and the rule agree on `[X_s^-, X_s^+]`; (c) a family that agrees with `S` on the band and has `SmoothExt` (any other
`C^{M+1}` extension) also satisfies the rule, with other constants.  (The statements "`S_j` depends only on jets of order `<= j`" and "`C^infty` if the jets are" are in `PLAN.md`, items L2.S7, L2.S8.) -/
def ThmSmoSpec (F : SymbolFamily Par) (K : Set Par) (M Kidx : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    (CI : ChartInputs F K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC)
    (_PI : ∀ ν, BulkPhaseInputs (frozenFamily F Kidx) (paramSet K t0) K t0 (CI.lo ν) (CI.hi ν) M U V (CI.bulkL ν) (CI.bulkR ν)) : Prop :=
  Kidx = (M + 1) / 2 → ThmAi F K M ∧
  (IsCompact K → HypOn F K → DM F K M →
    ∀ (S S' : ℕ → Par → ℝ → ℝ) (δ δ' Cn Cn' hM hM' C C' : ℝ),
      SmoothExt F K M S δ Cn → EigenRule F K M S hM C → SmoothExt F K M S' δ' Cn' → EigenRule F K M S' hM' C' →
        ∀ μ ∈ K, ∀ j ≤ M, ∀ X ∈ Set.Icc (F.bandLo μ) (F.bandHi μ), S j μ X = S' j μ X) ∧
  (IsCompact K → HypOn F K → DM F K M →
    ∀ (S S' : ℕ → Par → ℝ → ℝ) (δ δ' Cn Cn' hM C : ℝ),
      SmoothExt F K M S δ Cn → EigenRule F K M S hM C → SmoothExt F K M S' δ' Cn' →
        (∀ μ ∈ K, ∀ j ≤ M, ∀ X ∈ Set.Icc (F.bandLo μ) (F.bandHi μ), S' j μ X = S j μ X) →
          ∃ hM' C' : ℝ, EigenRule F K M S' hM' C')

/-! ### Comparison pairs of the soft edge -/

/-- The `+` pair `(y_1, y_2)` of lem:cha-PCenv: `a <= 0`: `(u~(a,Z), v~(a,Z))`; `a > 0`: `(u~_+, w~_+) = (kappa U(a,Z), kappa U(a,-Z))`. -/
def pcPlus (U V : ℝ → ℝ → ℝ) (a : ℝ) : Fin 2 → ℝ → ℝ
  | 0 => fun z => if a ≤ 0 then ut U a z else kappaBal a * U a z
  | 1 => fun z => if a ≤ 0 then vt V a z else kappaBal a * U a (-z)

/-! ### prop:tha-W (bulk) -/

/-- **prop:tha-W (1)** for one Weber chart `C` (apply to `CL` for the left solution and to the chart of the mirror family for the right one): the exact solution of the recurrence on rows
`0..N_R` seeded by `psi_0 = psi-hat_0` obeys `|psi_n - psi-hat_n| <= C h^m E_Web M_Web`. -/
def BulkSolutionBound {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (C : BulkWeberChart Fz P Jlo Jhi m U V) : Prop :=
  ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 → ∀ ψ : ℤ → ℝ,
    JacSol Fz p N X (C.NRL p X N) ψ → ψ 0 = C.psiHatL p X N 0 →
      ∀ k ∈ Finset.Icc (0 : ℤ) (C.NRL p X N), |ψ k - C.psiHatL p X N k| ≤ Cc * Fz.step N ^ m * C.envL p X N k

/-- **prop:tha-W**: (1) left and right solutions, (2) normalised eigenvectors: `hat N ~ h^{-1/4}`, `|hat kappa| ~ 1`, `|Psi_n - hat Psi_n| <= C h^m V_n / hat N` for every row, and the relative form
on the forbidden collars `u_n <= u_- - delta`, `u_n >= u_+ + delta` (constant depending on `delta`).  Hypotheses: `(E_{floor(m/2)})` and (H1)--(H3) on `P`. -/
def PropThaW (Fz : SymbolFamily (Par × ℝ)) (P : Set (Par × ℝ)) (Jlo Jhi : ℝ) (m : ℕ) (U V : ℝ → ℝ → ℝ)
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V) : Prop :=
  ∀ r, StdAssump Fz P (m / 2) r →
    BulkSolutionBound CL ∧ BulkSolutionBound CR ∧
    (∃ Cc h0 cN CN cκ Cκ : ℝ, 0 < h0 ∧ 0 < cN ∧ 0 < cκ ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 →
      0 < bulkNorm CL CR p X N ∧
      cN * Fz.step N ^ (-(1 : ℝ) / 4) ≤ bulkNorm CL CR p X N ∧ bulkNorm CL CR p X N ≤ CN * Fz.step N ^ (-(1 : ℝ) / 4) ∧
      cκ ≤ |bulkKappa CL CR p X N| ∧ |bulkKappa CL CR p X N| ≤ Cκ ∧
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), Xs k = X → ∀ n ∈ rowsOf N,
          |eigVec Um k n - bulkVec CL CR p X N n| ≤ Cc * Fz.step N ^ m * bulkEnv CL CR p X N n) ∧
    (∀ δ : ℝ, 0 < δ → ∃ Cδ h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 →
      ∀ n ∈ rowsOf N, (uNode (Fz.step N) n ≤ Fz.uMinus p X - δ ∨ Fz.uPlus p X + δ ≤ uNode (Fz.step N) n) →
        bulkEnv CL CR p X N n ≤ Cδ * |bulkVec CL CR p X N n|)

/-! ### prop:tha-W2 (soft edge) -/

/-- **prop:tha-W2** (soft edge, upper end).  `Lm = 1` for items (1)--(3); `Lm h = log(1/h)` for the "one shift short" item (4) (`m` odd, `q = m - 1`).
(1) the left solution through the soft edge: Weber bound on `u_n <= u_c - eta/2`, PC bound `|psi - lambda_L psi-hat^{PC,-}| <= C h^m |lambda_L| M_Olv(a,-Z_n)` on `u_c - eta/2 <= u_n <= u_c + 2 eta`, and
`|lambda_L| ~ lambda kappa_bal(a)`; (2) eigenvectors `|Psi_n - hat Psi_n| <= C h^m V_n/hat N`, `sum V^2/hat N^2 <= C`; (3) quantisation: the label of an eigenvalue in the window is its index and
`mu_0 + sum_{r=1}^{q/2} h^{2r} mu_{2r} = (k + 1/2) h + O(h^{m+1})`; conversely the eigenvalue of index `k` exists whenever the nominal point lies in `|X - X_s^+| <= delta_0/2`.
Hypotheses: `(E_{q/2})`, (H1)--(H3) on `P`. -/
def PropThaW2 (Fz : SymbolFamily (Par × ℝ)) (P : Set (Par × ℝ)) (m q : ℕ) (U V : ℝ → ℝ → ℝ)
    (CL : SoftEdgeChart Fz P m q U V) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V) (Lm : ℝ → ℝ) : Prop :=
  ∀ r, StdAssump Fz P (q / 2) r →
    ∃ Cc h0 clam Clam : ℝ, 0 < h0 ∧ 0 < clam ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 →
      (∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
        (∀ ψ : ℤ → ℝ, JacSol Fz p N X (CL.chain p X N).NR ψ → ψ 0 = CL.psiHatL p X N 0 →
          (∀ k ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR, uNode (Fz.step N) k ≤ CL.uc p - CL.η / 2 →
              |ψ k - CL.psiHatL p X N k| ≤ Cc * Fz.step N ^ m * Lm (Fz.step N) * softEnvWeb CL p X N k) ∧
          (∀ k ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR, CL.uc p - CL.η / 2 ≤ uNode (Fz.step N) k → uNode (Fz.step N) k ≤ CL.uc p + 2 * CL.η →
              |ψ k - CL.psiHatL p X N k| ≤ Cc * Fz.step N ^ m * Lm (Fz.step N) * |CL.lamL p X N| * Molv U V (CL.aOf p X N) (-(CL.Zof p X N k)))) ∧
        clam * (softLam CL p X N * kappaBal (CL.aOf p X N)) ≤ |CL.lamL p X N| ∧ |CL.lamL p X N| ≤ Clam * (softLam CL p X N * kappaBal (CL.aOf p X N)) ∧
        (∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
          ∀ k : Fin (N + 1), Xs k = X →
            (∀ n ∈ rowsOf N, |eigVec Um k n - softVec CL CR p X N n| ≤ Cc * Fz.step N ^ m * Lm (Fz.step N) * softEnv CL CR p X N n) ∧
            ∑ n ∈ rowsOf N, softEnv CL CR p X N n ^ 2 ≤ Cc)) ∧
      (∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ i : Fin (N + 1), |Xs i - Fz.bandHi p| ≤ CL.δ0 →
          |(CL.muS 0 p (Fz.bandHi p - Xs i) + ∑ s ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * s) * CL.muS s p (Fz.bandHi p - Xs i))
              - ((i : ℕ) + 1 / 2) * Fz.step N| ≤ Cc * Fz.step N ^ (m + 1) * Lm (Fz.step N)) ∧
      (∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : ℕ, k ≤ N → (∃ X, |X - Fz.bandHi p| ≤ CL.δ0 / 2 ∧
            CL.muS 0 p (Fz.bandHi p - X) + ∑ s ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * s) * CL.muS s p (Fz.bandHi p - X)
              = ((k : ℝ) + 1 / 2) * Fz.step N) →
          ∃ i : Fin (N + 1), (i : ℕ) = k ∧ |Xs i - Fz.bandHi p| ≤ CL.δ0)

/-- **lem:tha-win** (statement, items (1), (2), (3), (5)): for `a <= a_+`, `|alpha| <= delta_0`: the lattice facts (`d_- sqrt h <= Z_{n+1} - Z_n <= d_+ sqrt h`, `h k_2 <= C_Lambda^2`, `M_bal` comparable
at neighbours), the weight bounds `e^{-5/2} <= E_well <= 1` (`a <= 0`) / `E_bar` bounded (`0 < a <= a_+`) on `|Z| <= rho'`, the envelope bounds `|y_i| <= C_1 M_bal`, `|y_i'| <= C_1 k_2^{1/2} M_bal`
for both pairs, and the window sum `m_0/(2 d_+) h^{-1/2} <= sum_Omega M_bal^2 <= 11/d_- h^{-1/2}`. -/
def PropThaWin (Fz : SymbolFamily (Par × ℝ)) (P : Set (Par × ℝ)) (m q : ℕ) (U V : ℝ → ℝ → ℝ)
    (CL : SoftEdgeChart Fz P m q U V) (aplus : ℝ) : Prop :=
  ∀ r, StdAssump Fz P (q / 2) r →
    ∃ h0 CΛ Cnb C1 m0 : ℝ, 0 < h0 ∧ 0 < m0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 →
      CL.aOf p X N ≤ aplus →
      (∀ n ∈ rowsOf N, |uNode (Fz.step N) n - CL.uc p| ≤ 2 * CL.η →
        CL.dm * Real.sqrt (Fz.step N) ≤ CL.Zof p X N (n + 1) - CL.Zof p X N n ∧
        CL.Zof p X N (n + 1) - CL.Zof p X N n ≤ CL.dp * Real.sqrt (Fz.step N) ∧
        Fz.step N * k2 (CL.aOf p X N) (CL.Zof p X N n) ≤ CΛ ^ 2 ∧
        Mbal (CL.aOf p X N) (CL.Zof p X N (n + 1)) ≤ Cnb * Mbal (CL.aOf p X N) (CL.Zof p X N n) ∧
        Mbal (CL.aOf p X N) (CL.Zof p X N (n - 1)) ≤ Cnb * Mbal (CL.aOf p X N) (CL.Zof p X N n) ∧
        (|CL.Zof p X N n| ≤ rhoWin (CL.aOf p X N) + (1 + max (-CL.aOf p X N) 0) ^ (-(1 : ℝ) / 6) →
          |uNode (Fz.step N) n - CL.uc p| < CL.η / 4)) ∧
      (∀ z : ℝ, |z| ≤ rhoWin (CL.aOf p X N) + (1 + max (-CL.aOf p X N) 0) ^ (-(1 : ℝ) / 6) →
        (CL.aOf p X N ≤ 0 → Real.exp (-(5 : ℝ) / 2) ≤ Ewell (CL.aOf p X N) |z| ∧ Ewell (CL.aOf p X N) |z| ≤ 1) ∧
        (0 < CL.aOf p X N → Real.exp (-(2 * Real.sqrt (1 + aplus))) ≤ Ebar (CL.aOf p X N) z ∧
          Ebar (CL.aOf p X N) z ≤ Real.exp (2 * Real.sqrt (1 + aplus))) ∧
        (∀ i : Fin 2, (|pcPlus U V (CL.aOf p X N) i z| ≤ C1 * Mbal (CL.aOf p X N) z ∧
            |deriv (pcPlus U V (CL.aOf p X N) i) z| ≤ C1 * Real.sqrt (k2 (CL.aOf p X N) z) * Mbal (CL.aOf p X N) z) ∧
          (|pcMinus U V (CL.aOf p X N) i z| ≤ C1 * Mbal (CL.aOf p X N) z ∧
            |deriv (pcMinus U V (CL.aOf p X N) i) z| ≤ C1 * Real.sqrt (k2 (CL.aOf p X N) z) * Mbal (CL.aOf p X N) z))) ∧
      m0 / (2 * CL.dp) * Fz.step N ^ (-(1 : ℝ) / 2) ≤ ∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2 ∧
      ∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2 ≤ 11 / CL.dm * Fz.step N ^ (-(1 : ℝ) / 2)

/-- **lem:tha-M** (statement): for `a <= a_+` and every cut `|s| <= s_A = sqrt A + l_A/4` (`A = max(-a,0)`, `l_A = (1+A)^{-1/6}`) each half-window carries a fixed fraction of the mass:
`sum_{Omega, Z_n > s} U(a,Z_n)^2 >= c kappa_bal^{-2} sum_Omega M_bal^2`, and the same for `U(a,-Z_n)` on `Z_n <= s`, and for the corrected `-` sequence `phi^{(1)}_2 / kappa_bal`. -/
def PropThaM (Fz : SymbolFamily (Par × ℝ)) (P : Set (Par × ℝ)) (m q : ℕ) (U V : ℝ → ℝ → ℝ)
    (CL : SoftEdgeChart Fz P m q U V) (aplus : ℝ) : Prop :=
  ∀ r, StdAssump Fz P (q / 2) r →
    ∃ c h0 : ℝ, 0 < c ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 →
      CL.aOf p X N ≤ aplus → ∀ s : ℝ, |s| ≤ Real.sqrt (max (-CL.aOf p X N) 0) + (1 + max (-CL.aOf p X N) 0) ^ (-(1 : ℝ) / 6) / 4 →
        c * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * ∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2
            ≤ ∑ n ∈ (softWindow CL p X N).filter (fun n => s < CL.Zof p X N n), U (CL.aOf p X N) (CL.Zof p X N n) ^ 2 ∧
        c * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * ∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2
            ≤ ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ s), U (CL.aOf p X N) (-(CL.Zof p X N n)) ^ 2 ∧
        c * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * ∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2
            ≤ ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ s),
                ((CL.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (CL.aOf p X N)) ^ 2

/-! ### lem:tha-count -/

/-- The solution `p_n(X)` of the recurrence with `p_{-1} = 0`, `p_0 = 1` (eq:tha-rec). -/
def pSol (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => (X - F.entryB μ N 0) / F.bondA μ N 0
  | n + 2 => ((X - F.entryB μ N ((n : ℤ) + 1)) * pSol F μ N X (n + 1) - F.bondA μ N (n : ℤ) * pSol F μ N X n)
      / F.bondA μ N ((n : ℤ) + 1)

/-- The solution `q_n(X)` with `q_{N+1} = 0`, `q_N = 1`, indexed by `j = N - n` (so `qSol .. j = q_{N-j}`). -/
def qSol (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => (X - F.entryB μ N (N : ℤ)) / F.bondA μ N ((N : ℤ) - 1)
  | j + 2 => ((X - F.entryB μ N ((N : ℤ) - j - 1)) * qSol F μ N X (j + 1) - F.bondA μ N ((N : ℤ) - j - 1) * qSol F μ N X j)
      / F.bondA μ N ((N : ℤ) - j - 2)

/-- `D(X) = W(p, q)` (constant in `n`), evaluated at the bond `(0,1)`: `a_0 (p_1 q_0 - p_0 q_1)`, `q_0 = qSol N`, `q_1 = qSol (N-1)`. -/
def casD (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : ℝ) : ℝ :=
  F.bondA μ N 0 * (pSol F μ N X 1 * qSol F μ N X N - pSol F μ N X 0 * qSol F μ N X (N - 1))

/-- **lem:tha-count** (statement): `I` an interval, `Phi` continuous and strictly monotone on `I`, `0 < eps < pi h/4`, windows `w_k = {X in I : |Phi(X) - pi h (k+1/2)| <= eps}`.
(i) every zero of `D` in `I` lies in some window; (ii) `sign D = sigma (-1)^k` where `Phi = pi h k`; (iii) at a zero in `w_k`, `p = kappa' q` has `sign kappa' = sigma' (-1)^k`.
Then each window contains at most one zero of `D`, and each `w_k` with `[pi h k, pi h (k+1)] subset Phi(I)` contains exactly one (at least one, together with the at-most-one). -/
def PropThaCount (F : SymbolFamily Par) (μ : Par) (N : ℕ) : Prop :=
  ∀ (I : Set ℝ) (Φ : ℝ → ℝ) (ε : ℝ), I.OrdConnected → ContinuousOn Φ I → (StrictMonoOn Φ I ∨ StrictAntiOn Φ I) →
    0 < ε → ε < Real.pi * F.step N / 4 →
    (∀ X ∈ I, casD F μ N X = 0 → ∃ k : ℕ, |Φ X - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ ε) →
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ X ∈ I, ∀ k : ℕ, Φ X = Real.pi * F.step N * k →
        SignType.sign (casD F μ N X) = SignType.sign (σ * (-1) ^ k)) →
    (∃ σ' : ℝ, (σ' = 1 ∨ σ' = -1) ∧ ∀ X ∈ I, ∀ k : ℕ, casD F μ N X = 0 →
        |Φ X - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ ε → ∀ κ' : ℝ, (∀ n ≤ N, pSol F μ N X n = κ' * qSol F μ N X (N - n)) →
          SignType.sign κ' = SignType.sign (σ' * (-1) ^ k)) →
    (∀ k : ℕ, ∀ X ∈ I, ∀ X' ∈ I, casD F μ N X = 0 → casD F μ N X' = 0 →
        |Φ X - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ ε → |Φ X' - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ ε → X = X') ∧
    (∀ k : ℕ, Set.Icc (Real.pi * F.step N * k) (Real.pi * F.step N * (k + 1)) ⊆ Φ '' I →
        ∃ X ∈ I, casD F μ N X = 0 ∧ |Φ X - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ ε)

/-! ### prop:l2jets -/

/-- The truncated family `tilde J_h` of eq:l2-tilde: `tilde E_n = s_n(L-s_n) sum_{j<=m} h^j G_j(s_n)`, `tilde B_n = sum_{j<=m} h^j B_j(u_n)`, jets completed by zero beyond `m`. -/
def truncFamily (F : SymbolFamily Par) (m : ℕ) : SymbolFamily Par where
  L := F.L
  L_pos := F.L_pos
  Gh := fun μ h s => ∑ j ∈ range (m + 1), h ^ j * F.G j μ s
  Bh := fun μ h u => ∑ j ∈ range (m + 1), h ^ j * F.B j μ u
  G := fun j μ s => if j ≤ m then F.G j μ s else 0
  B := fun j μ s => if j ≤ m then F.B j μ s else 0

/-- **prop:l2jets** (statement): under (H1)--(H3) and only `(D_m)`, the comparison vectors `P^{(m)}_k` built (def:tha-Psihat) for the truncated family at its own eigenvalues `tilde X_k`
satisfy `sup_k ||Psi_k - P^{(m)}_k||_2 <= C h^m`.  The charts `CI` are those of the truncated family (frozen at `Kidx = ceil(m/2)`, `q = 2 Kidx`), which satisfies `(E_Kidx)` with no remainder. -/
def PropL2Jets (F : SymbolFamily Par) (K : Set Par) (m : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    (CI : ChartInputs (truncFamily F m) K ((m + 1) / 2) t0 m (2 * ((m + 1) / 2)) U V cPC CPC) : Prop :=
  1 ≤ m → IsCompact K → HypOn F K → DM F K m →
    ∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
      ∀ (Xt : Fin (N + 1) → ℝ) (Ut : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem ((truncFamily F m).jacobiMat μ N) Xt Ut →
        ∀ k : Fin (N + 1),
          Real.sqrt (∑ n ∈ rowsOf N, (eigVec Um k n - psiHatVec CI μ N (Xt k) n) ^ 2) ≤ C * F.step N ^ m

/-! ### thm:A (ii) -/

/-- **Theorem A (ii)**: for `m >= 1`, `q = 2 ceil(m/2)` (admissible), under `(D_{2 ceil(m/2) + 1})` and (H1)--(H3) and the charts `CI`: for `h <= h_m`, all `k, n`,
`|(Psi_k)_n - (hat Psi^{(m)}_k)_n| <= C_m h^m V_{k,n}` and `sum_n V_{k,n}^2 <= C`, with the explicit `psiHatVec`, `envVec` (def:tha-Psihat) evaluated at `X = X_k`.
(`sum V^2 <= C` gives `||Psi_k - hat Psi_k||_2 <= C_m h^m`.)  The frozen family and the choice `t = h` are in `psiHatVec` (`atStep`). -/
def ThmAii (F : SymbolFamily Par) (K : Set Par) (m Kidx : ℕ) (t0 : ℝ) (U V : ℝ → ℝ → ℝ) (cPC CPC : ℝ)
    (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) : Prop :=
  1 ≤ m → Kidx = (m + 1) / 2 → IsCompact K → HypOn F K → DM F K (2 * ((m + 1) / 2) + 1) →
    ∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (∀ n ∈ rowsOf N, |eigVec Um k n - psiHatVec CI μ N (X k) n| ≤ C * F.step N ^ m * envVec CI μ N (X k) n) ∧
          ∑ n ∈ rowsOf N, envVec CI μ N (X k) n ^ 2 ≤ C

end FormalResearch.JacobiEigenvectors.TheoremA
