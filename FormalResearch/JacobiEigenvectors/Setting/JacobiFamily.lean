module

public import Mathlib
public import FormalResearch.JB.JBThmB
public import FormalResearch.JE.JECasoratian

/-!
# Paper J, the setting (statement freeze): Jacobi family, hypotheses (H1)--(H3), freezing, gauges

Source: Paper J (`Weyl/jacobi_eigenvectors/paper/parts/main_results.tex`, `thmA.tex` Section 4.1, branch
`agents/m7-m1-global-racah` of QIprojects).  Definitions and Prop-valued hypothesis structures only; no theorem of
the paper is proved here.  The proved lemmas are the exact algebraic identities of the setting
(`frozenFamily_at_step`, `mirrorFamily_*`, `negFamily_*`).

## Dictionary: Lean to paper

| Lean | paper |
|---|---|
| `SymbolFamily Par` (`L`, `Gh`, `Bh`, `G j`, `B j`) | `L`, `G_h`, `B_h`, jets `G_j`, `B_j` (def:symbols); `Par` is the parameter `μ` |
| `SymbolFamily.step N` = `JB.stepSize L N` | `h = L/(N+1)` |
| `sNode h n`, `uNode h n` | `s_n = (n+1)h`, `u_n = (n+1/2)h` |
| `entryE`, `bondA`, `entryB`, `diagQ` | `E_n = s_n(L-s_n)G_h(s_n)`, `a_n = sqrt E_n` (`a_{-1} = a_N = 0`), `B_n = B_h(u_n)`, `X - B_n` |
| `jacobiMat` | `J_h` (eq:J) as a `Matrix (Fin (N+1)) (Fin (N+1)) ℝ` |
| `IsEigenSystem J X U` | eigenvalues `X_0 > ... > X_N`, orthogonal `U_h = (Psi_0..Psi_N)`, gauge `(Psi_k)_0 > 0` |
| `JacSol` | the three-term recurrence (eq:tha-rec) on rows `0 <= n < NR`, any energy `X` |
| `regBudget M` = `9M+22` | `r(M)` of lem:smo-budget |
| `JetReg` | `G_j in C^r([0,L])` depending continuously on `mu` in these norms |
| `DM F K M` | `(D_M)` of def:symbols (jets `C^{r(M)-10 floor(j/2)}`, remainder `O(h^{M+1})`) |
| `EK F K Kidx r` | `(E_K)` of eq:tha-AK (even jets only, `r >= r(max(2K-1,0))`) |
| `E0, Tfun, fPlus, fMinus, Xsp, Xsm` | `E_0, T, f_+, f_-, X_s^+, X_s^-` (eq:T) |
| `Hyp L G0 B0 g` (`H1`, `H2`, `H3`) | (H1)--(H3) of sec:hypotheses, for one pair of principal symbols |
| `HypOn F K` | `(H1)--(H3)` for all `mu` in `K` with one `g_*` |
| `frozenFamily F K` (parameter `Par x R`, `t` = second component) | `J_h^{(t)}` of eq:smo-freeze/eq:smo-frozen |
| `mirrorFamily F` | the mirror `n -> N-n`, `s -> L-s` (right-edge charts) |
| `negFamily F` | the gauge `-(-1)^n J (-1)^n` (diagonal `-B_n`; lower soft edge) |

## Design points and deliberate differences

* **Uniformity in `mu`.**  A family is a function of `mu : Par`; `K : Set Par` is the compact set `K` of the paper.
  Statements quantify `forall mu in K` after the constants.  Compactness of `K` is *not* a field here: it is a
  hypothesis of the statements that need it (`IsCompact K`).
* **Remainders (eq:remainders).**  The paper has `sup|R^G| + sup|R^B| <= C h^{M+1}`; here each sup is bounded
  separately (equivalent up to the factor 2 in `C`), for `h = L/(N+1)`, all `N` (small `N` is absorbed in `C`).
* **Only samples enter.**  `Gh`, `Bh` are arbitrary real functions of `(mu, h, s)`; only the values `Gh mu h (s_n)`,
  `Bh mu h (u_n)` enter `jacobiMat`.  (D_M) bounds the remainder on all of `[0,L]` as in the paper (pointwise on
  `[0,L]`, which contains the samples).
* **`Hyp` is pointwise in `mu`.**  Uniform margins follow from compactness and continuity of the jets in `mu` (the paper's
  "localisation"); only `g_*` is uniform.  Whether this is enough is item F-loc of `PLAN.md`.
* **Simple zero (H2).**  "Simple zero of `T(.;X)` at an endpoint in `(0,L)`" is `T = 0` and `deriv (T(.;X)) <> 0` there.
  `deriv` is the junk value `0` at non-differentiable points, so the hypothesis cannot hold vacuously.

## Not here

The statements (`TheoremA/Statements.lean`), the chart hypotheses (`Charts/`).  The engine is `FormalResearch.JE`
(it will be moved to `FormalResearch.JacobiEigenvectors.Engine`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Setting

open Set Finset
open scoped Matrix

/-- The derivative budget `r(M) = 9M + 22` of lem:smo-budget (sufficient, unoptimised). -/
def regBudget (M : ℕ) : ℕ := 9 * M + 22

/-- Lattice nodes `s_n = (n+1) h` (the bond sites). -/
def sNode (h : ℝ) (n : ℤ) : ℝ := ((n : ℝ) + 1) * h

/-- Lattice nodes `u_n = (n+1/2) h` (the diagonal sites). -/
def uNode (h : ℝ) (n : ℤ) : ℝ := ((n : ℝ) + 1 / 2) * h

/-- The data of a family of symbols `G_h, B_h` with jets `G_j, B_j`, depending on a parameter `mu : Par`, with `L` fixed. -/
structure SymbolFamily (Par : Type*) where
  L : ℝ
  L_pos : 0 < L
  /-- `G_h(s)` at `(mu, h, s)`. -/
  Gh : Par → ℝ → ℝ → ℝ
  /-- `B_h(u)` at `(mu, h, u)`. -/
  Bh : Par → ℝ → ℝ → ℝ
  /-- the jets `G_j(s)` at `(j, mu, s)`. -/
  G : ℕ → Par → ℝ → ℝ
  B : ℕ → Par → ℝ → ℝ

namespace SymbolFamily

variable {Par : Type*} (F : SymbolFamily Par)

/-- `h = L/(N+1)`. -/
def step (N : ℕ) : ℝ := FormalResearch.JB.stepSize F.L N

/-- `E_n = s_n (L - s_n) G_h(s_n)` (def:symbols, eq:symbols). -/
def entryE (μ : Par) (N : ℕ) (n : ℤ) : ℝ :=
  sNode (F.step N) n * (F.L - sNode (F.step N) n) * F.Gh μ (F.step N) (sNode (F.step N) n)

/-- `B_n = B_h(u_n)`. -/
def entryB (μ : Par) (N : ℕ) (n : ℤ) : ℝ := F.Bh μ (F.step N) (uNode (F.step N) n)

/-- The bond `a_n = sqrt E_n` for `0 <= n < N`, and `a_n = 0` otherwise (`a_{-1} = a_N = 0`: the two hard edges). -/
def bondA (μ : Par) (N : ℕ) (n : ℤ) : ℝ :=
  if 0 ≤ n ∧ n < (N : ℤ) then Real.sqrt (F.entryE μ N n) else 0

/-- The diagonal coefficient `X - B_n` of the recurrence at energy `X`. -/
def diagQ (μ : Par) (N : ℕ) (X : ℝ) (n : ℤ) : ℝ := X - F.entryB μ N n

/-- The Jacobi matrix `J_h` (eq:J) on `{0,...,N}`. -/
def jacobiMat (μ : Par) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j =>
    if i = j then F.entryB μ N (i.val : ℤ)
    else if j.val = i.val + 1 then F.bondA μ N (i.val : ℤ)
    else if i.val = j.val + 1 then F.bondA μ N (j.val : ℤ)
    else 0

end SymbolFamily

/-- `f` solves the three-term recurrence (eq:tha-rec) at energy `X` on the rows `0 <= n < NR`.  The ghost value
`f_{-1}` never enters (`a_{-1} = 0`). -/
def JacSol {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : ℝ) (NR : ℤ) (f : ℤ → ℝ) : Prop :=
  ∀ n : ℤ, 0 ≤ n → n < NR → FormalResearch.JE.Lop (F.bondA μ N) (F.diagQ μ N X) f n = 0

/-- Eigenvalues `X_0 > ... > X_N` and the orthogonal eigenvector matrix `U = (Psi_0, ..., Psi_N)` in the gauge
`(Psi_k)_0 > 0` (the setting of main_results.tex, Section 1.1).  Statements quantify over such pairs, so no existence
or uniqueness theorem is needed in them (both hold for a Jacobi matrix with positive bonds). -/
structure IsEigenSystem {N : ℕ} (J : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (X : Fin (N + 1) → ℝ)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : Prop where
  orth : Uᵀ * U = 1
  eig : J * U = U * Matrix.diagonal X
  anti : StrictAnti X
  pos : ∀ k, 0 < U 0 k

/-- The column `Psi_k` of `U` as a sequence on `ℤ` (zero outside `0..N`). -/
def eigVec {N : ℕ} (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : Fin (N + 1)) : ℤ → ℝ :=
  fun n => if hn : 0 ≤ n ∧ n ≤ (N : ℤ) then U ⟨n.toNat, by omega⟩ k else 0

/-! ### Regularity of jets: (D_M) and (E_K) -/

/-- The family `f` is of class `C^r` on `[0,L]` for each `mu in K`, and its derivatives up to order `r` are jointly
continuous on `K x [0,L]` (so `mu -> f mu` is continuous into `C^r([0,L])`). -/
def JetReg {Par : Type*} [TopologicalSpace Par] (f : Par → ℝ → ℝ) (K : Set Par) (L : ℝ) (r : ℕ) : Prop :=
  (∀ μ ∈ K, ContDiffOn ℝ (r : WithTop ℕ∞) (f μ) (Icc 0 L)) ∧
  ∀ i ≤ r, ContinuousOn (fun p : Par × ℝ => iteratedDerivWithin i (f p.1) (Icc 0 L) p.2) (K ×ˢ Icc 0 L)

/-- `(D_M)` of def:symbols: jets `G_j, B_j in C^{r(M) - 10 floor(j/2)}` depending continuously on `mu`, and the
remainders (eq:remainders) `G_h - sum_{j<=M} h^j G_j`, `B_h - sum_{j<=M} h^j B_j` are `<= C h^{M+1}` on `[0,L]`, for `h = L/(N+1)`. -/
structure DM {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (M : ℕ) : Prop where
  reg : ∀ j ≤ M, JetReg (F.G j) K F.L (regBudget M - 10 * (j / 2)) ∧ JetReg (F.B j) K F.L (regBudget M - 10 * (j / 2))
  rem : ∃ C : ℝ, ∀ μ ∈ K, ∀ N : ℕ, ∀ s ∈ Icc 0 F.L,
    |F.Gh μ (F.step N) s - ∑ j ∈ range (M + 1), F.step N ^ j * F.G j μ s| ≤ C * F.step N ^ (M + 1) ∧
    |F.Bh μ (F.step N) s - ∑ j ∈ range (M + 1), F.step N ^ j * F.B j μ s| ≤ C * F.step N ^ (M + 1)

/-- `(E_K)` of eq:tha-AK, without `(H1)` (kept in `Hyp`): only the even jets `G_{2j}, B_{2j}`, `j <= K`, of class
`C^{r - 10 j}` with `r >= r(max(2K-1, 0))`, and `G_h - sum_{j<=K} h^{2j} G_{2j} = O(h^{2K+2})` on `[0,L]`. -/
structure EK {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (Kidx r : ℕ) : Prop where
  budget : regBudget (max (2 * Kidx - 1) 0) ≤ r
  reg : ∀ j ≤ Kidx, JetReg (F.G (2 * j)) K F.L (r - 10 * j) ∧ JetReg (F.B (2 * j)) K F.L (r - 10 * j)
  rem : ∃ C : ℝ, ∀ μ ∈ K, ∀ N : ℕ, ∀ s ∈ Icc 0 F.L,
    |F.Gh μ (F.step N) s - ∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s|
        ≤ C * F.step N ^ (2 * Kidx + 2) ∧
    |F.Bh μ (F.step N) s - ∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.B (2 * j) μ s|
        ≤ C * F.step N ^ (2 * Kidx + 2)

/-! ### The hypotheses (H1)--(H3) on one pair of principal symbols -/

section Principal

variable (L : ℝ) (G0 B0 : ℝ → ℝ)

/-- `E_0(s) = s (L - s) G_0(s)`. -/
def E0 (s : ℝ) : ℝ := s * (L - s) * G0 s

/-- `T(u; X) = 4 E_0(u) - (X - B_0(u))^2` (eq:T). -/
def Tfun (X u : ℝ) : ℝ := 4 * E0 L G0 u - (X - B0 u) ^ 2

/-- `f_+ = B_0 + 2 sqrt E_0`. -/
def fPlus (u : ℝ) : ℝ := B0 u + 2 * Real.sqrt (E0 L G0 u)

/-- `f_- = B_0 - 2 sqrt E_0`. -/
def fMinus (u : ℝ) : ℝ := B0 u - 2 * Real.sqrt (E0 L G0 u)

/-- `X_s^+ = max_{[0,L]} f_+`. -/
def Xsp : ℝ := sSup (fPlus L G0 B0 '' Icc 0 L)

/-- `X_s^- = min_{[0,L]} f_-`. -/
def Xsm : ℝ := sInf (fMinus L G0 B0 '' Icc 0 L)

/-- The hypotheses (H1)--(H3) of sec:hypotheses for the principal symbols `G_0, B_0`, with lower bound `g_*` in (H1).
(H1)'s regularity part (`(D_0)`) is `DM` / `EK`; here only `G_0 >= g_* > 0`. -/
structure Hyp (gstar : ℝ) : Prop where
  /-- (H1) `g_* > 0`. -/
  gstar_pos : 0 < gstar
  /-- (H1) `G_0 >= g_*` on `[0,L]`. -/
  G0_lb : ∀ u ∈ Icc 0 L, gstar ≤ G0 u
  /-- (H2) one well: for `X` in the open band the allowed set is one interval `[a,b]`; an endpoint in `(0,L)` is a simple
  zero of `T(.;X)`; an endpoint at `0` (resp. `L`) forces the collision `Q_0(0;X) = 0`, i.e. `X = B_0(0)` (resp. `B_0(L)`). -/
  H2 : ∀ X, Xsm L G0 B0 < X → X < Xsp L G0 B0 →
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ L ∧
      (Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u}) = Icc a b ∧
      (0 < a → Tfun L G0 B0 X a = 0 ∧ deriv (Tfun L G0 B0 X) a ≠ 0) ∧
      (b < L → Tfun L G0 B0 X b = 0 ∧ deriv (Tfun L G0 B0 X) b ≠ 0) ∧
      (a = 0 → X = B0 0) ∧ (b = L → X = B0 L)
  /-- (H3) `f_+` attains `X_s^+` at a single interior point `u_c^+`, with `f_+'' < 0` there. -/
  H3p : ∃ uc, 0 < uc ∧ uc < L ∧ (∀ u ∈ Icc 0 L, fPlus L G0 B0 u = Xsp L G0 B0 ↔ u = uc) ∧
    deriv (deriv (fPlus L G0 B0)) uc < 0
  /-- (H3) `f_-` attains `X_s^-` at a single interior point `u_c^-`, with `f_-'' > 0` there. -/
  H3m : ∃ uc, 0 < uc ∧ uc < L ∧ (∀ u ∈ Icc 0 L, fMinus L G0 B0 u = Xsm L G0 B0 ↔ u = uc) ∧
    0 < deriv (deriv (fMinus L G0 B0)) uc

end Principal

/-- (H1)--(H3) for the principal symbols `G_0(mu), B_0(mu)` of the family, for every `mu in K`, with one `g_*`. -/
def HypOn {Par : Type*} (F : SymbolFamily Par) (K : Set Par) : Prop :=
  ∃ g : ℝ, ∀ μ ∈ K, Hyp F.L (F.G 0 μ) (F.B 0 μ) g

/-- The band ends of the principal symbols of `mu`. -/
def SymbolFamily.bandHi {Par : Type*} (F : SymbolFamily Par) (μ : Par) : ℝ := Xsp F.L (F.G 0 μ) (F.B 0 μ)

def SymbolFamily.bandLo {Par : Type*} (F : SymbolFamily Par) (μ : Par) : ℝ := Xsm F.L (F.G 0 μ) (F.B 0 μ)

/-- The left end `u_-(X)` of the allowed set `{T(.;X) >= 0}` (`inf`; the allowed set is `[u_-, u_+]` under (H2)). -/
def SymbolFamily.uMinus {Par : Type*} (F : SymbolFamily Par) (μ : Par) (X : ℝ) : ℝ :=
  sInf (Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u})

/-- The right end `u_+(X)`. -/
def SymbolFamily.uPlus {Par : Type*} (F : SymbolFamily Par) (μ : Par) (X : ℝ) : ℝ :=
  sSup (Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u})

/-! ### Derived families: parity freezing, mirror, gauge -/

/-- Parity freezing (eq:smo-freeze) through the jets of order `2 Kidx + 1`: the parameter is `(mu, t)`, `t : ℝ`.
`G_h^{(t)}(s) = G_h(s) + (t - h) sum_{j<=K} h^{2j} G_{2j+1}(s)` (the factor `s(L-s)` is in `entryE`), likewise `B`.  The jets are the
even jets `G_{2j} + t G_{2j+1}` (`j <= K`) and `0` for the others, so `EK (frozenFamily F K) .. K ..` is the paper's
claim "the frozen matrices satisfy `(E_K)` with jets `G_{2j} + t G_{2j+1}`" (statement `FrozenStatements` in TheoremA). -/
def frozenFamily {Par : Type*} (F : SymbolFamily Par) (Kidx : ℕ) : SymbolFamily (Par × ℝ) where
  L := F.L
  L_pos := F.L_pos
  Gh := fun p h s => F.Gh p.1 h s + (p.2 - h) * ∑ j ∈ range (Kidx + 1), h ^ (2 * j) * F.G (2 * j + 1) p.1 s
  Bh := fun p h u => F.Bh p.1 h u + (p.2 - h) * ∑ j ∈ range (Kidx + 1), h ^ (2 * j) * F.B (2 * j + 1) p.1 u
  G := fun i p s => if i % 2 = 0 ∧ i ≤ 2 * Kidx then F.G i p.1 s + p.2 * F.G (i + 1) p.1 s else 0
  B := fun i p s => if i % 2 = 0 ∧ i ≤ 2 * Kidx then F.B i p.1 s + p.2 * F.B (i + 1) p.1 s else 0

/-- **Exact identity** `J_h^{(h)} = J_h` (eq:smo-freeze): at `t = h` the frozen symbols are the original ones. -/
theorem frozenFamily_Gh_at_step {Par : Type*} (F : SymbolFamily Par) (Kidx : ℕ) (μ : Par) (h s : ℝ) :
    (frozenFamily F Kidx).Gh (μ, h) h s = F.Gh μ h s := by
  simp [frozenFamily]

theorem frozenFamily_Bh_at_step {Par : Type*} (F : SymbolFamily Par) (Kidx : ℕ) (μ : Par) (h u : ℝ) :
    (frozenFamily F Kidx).Bh (μ, h) h u = F.Bh μ h u := by
  simp [frozenFamily]

/-- The frozen Jacobi matrix at `t = h = step N` is `J_h` itself (entrywise, hence as matrices). -/
theorem frozenFamily_jacobiMat_at_step {Par : Type*} (F : SymbolFamily Par) (Kidx : ℕ) (μ : Par) (N : ℕ) :
    (frozenFamily F Kidx).jacobiMat (μ, F.step N) N = F.jacobiMat μ N := by
  have hE : ∀ n : ℤ, (frozenFamily F Kidx).entryE (μ, F.step N) N n = F.entryE μ N n := by
    intro n
    simp [SymbolFamily.entryE, SymbolFamily.step, frozenFamily]
  have hB : ∀ n : ℤ, (frozenFamily F Kidx).entryB (μ, F.step N) N n = F.entryB μ N n := by
    intro n
    simp [SymbolFamily.entryB, SymbolFamily.step, frozenFamily]
  have hA : ∀ n : ℤ, (frozenFamily F Kidx).bondA (μ, F.step N) N n = F.bondA μ N n := by
    intro n
    simp only [SymbolFamily.bondA, hE]
  ext i j
  simp only [SymbolFamily.jacobiMat, Matrix.of_apply, hB, hA]

/-- The mirror family `n -> N - n`, `s -> L - s` (used for the right-edge charts). -/
def mirrorFamily {Par : Type*} (F : SymbolFamily Par) : SymbolFamily Par where
  L := F.L
  L_pos := F.L_pos
  Gh := fun μ h s => F.Gh μ h (F.L - s)
  Bh := fun μ h u => F.Bh μ h (F.L - u)
  G := fun j μ s => F.G j μ (F.L - s)
  B := fun j μ s => F.B j μ (F.L - s)

/-- The gauge family `-(-1)^n J (-1)^n`: same bonds, diagonal `-B_n` (the lower soft edge of `J` is the upper soft edge of
this family; the spectrum is `-X`). -/
def negFamily {Par : Type*} (F : SymbolFamily Par) : SymbolFamily Par where
  L := F.L
  L_pos := F.L_pos
  Gh := F.Gh
  Bh := fun μ h u => -F.Bh μ h u
  G := F.G
  B := fun j μ s => -F.B j μ s

theorem negFamily_bondA {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (n : ℤ) :
    (negFamily F).bondA μ N n = F.bondA μ N n := rfl

theorem negFamily_diagQ {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : ℝ) (n : ℤ) :
    (negFamily F).diagQ μ N (-X) n = -F.diagQ μ N X n := by
  simp [SymbolFamily.diagQ, SymbolFamily.entryB, SymbolFamily.step, negFamily]; ring

/-- Gauge invariance of the recurrence: if `f` solves it for `(F, X)` then `(-1)^n f_n` solves it for `(negFamily F, -X)`. -/
theorem negFamily_JacSol {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : ℝ) (NR : ℤ) (f : ℤ → ℝ)
    (hf : JacSol F μ N X NR f) :
    JacSol (negFamily F) μ N (-X) NR (fun n => (-1 : ℝ) ^ n * f n) := by
  intro n hn hnR
  have h0 := hf n hn hnR
  unfold FormalResearch.JE.Lop at h0 ⊢
  simp only [negFamily_bondA, negFamily_diagQ]
  have e1 : (-1 : ℝ) ^ (n + 1) = -(-1 : ℝ) ^ n := by
    rw [zpow_add_one₀ (by norm_num)]; ring
  have e2 : (-1 : ℝ) ^ (n - 1) = -(-1 : ℝ) ^ n := by
    rw [zpow_sub_one₀ (by norm_num)]; norm_num
  simp only [e1, e2]
  linear_combination (-(-1 : ℝ) ^ n) * h0

end FormalResearch.JacobiEigenvectors.Setting
