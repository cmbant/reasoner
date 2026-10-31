import FormalResearch.FourQubitEntropy.RenyiFullDual

/-!
# The per-spectrum certificates behind `thm:fqe-renyi-classical`

Paper E, `sup_renyi.tex` and `renyi_dual_tables.tex`.  The proof of the classical relaxation theorem
(anchor orders `q_s = 1587/1000`, `q_u = 8/5`) consists of an outer case analysis on the triple
`(ε, F)` and of *per-spectrum* supporting inequalities for four-point probability vectors.  Each
per-spectrum statement of the paper is stated here as a `def … : Prop` that matches the paper's
lemma; the case analysis (`RenyiFullClassical.lean`) is proved from them.  The statements are:

| Prop | paper label | statement |
|---|---|---|
| `DetReduction` | `lem:fqe-renyi-determinant` | chart reduction `(a,b,c,c)` / `(a,a,b,c)` at fixed `p, t` for `1<q<2` |
| `HsSupporting` | `lem:fqe-hs-polynomial` | `Λ_θ(λ;8/5) ≤ h_{8/5}` for `p ≤ 9/16`, equality only HS |
| `RationalDual` | `lem:fqe-rational-dual` (exact rational certificate RQ) | `Λ_θ ≤ W - 10⁻⁵` for `p ≤ 49/75`, band `L` |
| `CappedCubic` | `lem:fqe-capped-cubic` | capped cubic slack for `p ≤ 47/100` |
| `NearUniformDual` | `lem:fqe-near-uniform-dual` | `Λ_θ(c₂) - Λ_θ(λ) ≥ (p - 1/4)/125` for `p ≤ 29/100` |
| `ClusterSliver` | `lem:fqe-cluster-sliver` | `G_± ≥ 0` on the two ordered charts |

None of these is an axiom; they are hypotheses of the downstream theorems.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-! ### Charts: the two determinant patterns -/

/-- A spectrum of one of the two patterns `(a,b,c,c)` or `(a,a,b,c)`, `a ≥ b ≥ c ≥ 0` (DM). -/
def IsChart (μ : Fin 4 → ℝ) : Prop :=
  IsProb4 μ ∧ ∃ a b c : ℝ, 0 ≤ c ∧ c ≤ b ∧ b ≤ a ∧ (μ = ![a, b, c, c] ∨ μ = ![a, a, b, c])

/-- **`lem:fqe-renyi-determinant`** (consequence used by the classical relaxation): for `1 < q < 2`
every four-point spectrum has a chart spectrum with the same `p` and `t` and no smaller `H_q`. -/
def DetReduction : Prop :=
  ∀ q : ℝ, 1 < q → q < 2 → ∀ l : Fin 4 → ℝ, IsProb4 l →
    ∃ μ : Fin 4 → ℝ, IsChart μ ∧ pur μ = pur l ∧ cub μ = cub l ∧ renyiSpec q l ≤ renyiSpec q μ

/-! ### Multiplier rows (Table `tab:fqe-dual-co` and `lem:fqe-hs-polynomial`) -/

/-- Row `L` (CZ band): `θ = (3.98, 0.15, 1.59)`. -/
noncomputable def aL : ℝ := 39800 / 10000
noncomputable def bL : ℝ := 1500 / 10000
noncomputable def gL : ℝ := 15900 / 10000

/-- Row `HT` (cluster sliver): `θ = (3.5425, 0.1872, 1.1235)`. -/
noncomputable def aH : ℝ := 35425 / 10000
noncomputable def bH : ℝ := 1872 / 10000
noncomputable def gH : ℝ := 11235 / 10000

/-- `L = ln 2`, `u = 3^{3/5}`, `k = (16/(3L)) (u-1)/(u+1)`. -/
noncomputable def kU : ℝ :=
  16 / (3 * Real.log 2) * (((3 : ℝ) ^ (3 / 5 : ℝ) - 1) / ((3 : ℝ) ^ (3 / 5 : ℝ) + 1))

/-- The HS multiplier at `q_u = 8/5`: `α = (3/2)k + 65/36`, `β = 1/12`, `γ = 10/3`. -/
noncomputable def aU : ℝ := 3 / 2 * kU + 65 / 36
noncomputable def bU : ℝ := 1 / 12
noncomputable def gU : ℝ := 10 / 3

/-- The target `W` of the rational dual: `5/3 + (1/3) min_corners ℓ_θ` on `[0,1/9] × [3/20, 11/25]`
(`ε × F`) for the row `L`. -/
noncomputable def WL : ℝ :=
  5 / 3 + (1 / 3) * min (min (ell aL bL gL 0 (3 / 20)) (ell aL bL gL 0 (11 / 25)))
    (min (ell aL bL gL (1 / 9) (3 / 20)) (ell aL bL gL (1 / 9) (11 / 25)))

/-! ### The per-spectrum certificates -/

/-- **`lem:fqe-hs-polynomial`**: at `q_u = 8/5`, every four-point probability vector with `p ≤ 9/16`
satisfies `Λ_{(α,β,γ)}(λ) ≤ h_{8/5}`, with equality only at HS. -/
def HsSupporting : Prop :=
  ∀ l : Fin 4 → ℝ, IsProb4 l → pur l ≤ 9 / 16 →
    Lam qU aU bU gU l ≤ renyiSpec qU hsSpec ∧
      (Lam qU aU bU gU l = renyiSpec qU hsSpec → IsHsPerm l)

/-- **`lem:fqe-rational-dual`** (exact rational certificate RQ): for the band `L`, every four-point
spectrum with `p ≤ 49/75` satisfies `Λ_θ(λ; q_s) ≤ W - 10⁻⁵`. -/
def RationalDual : Prop :=
  ∀ l : Fin 4 → ℝ, IsProb4 l → pur l ≤ 49 / 75 →
    Lam qS aL bL gL l ≤ WL - 1 / 100000

/-- **`lem:fqe-capped-cubic`**: every four-point probability vector with `p ≤ 47/100` satisfies
`H_{q_s}(λ) ≤ 10/3 - 6p + (8/3)t - (11/10)(p - 1/4)(1/2 - p)`. -/
def CappedCubic : Prop :=
  ∀ l : Fin 4 → ℝ, IsProb4 l → pur l ≤ 47 / 100 →
    renyiSpec qS l ≤
      10 / 3 - 6 * pur l + 8 / 3 * cub l - 11 / 10 * (pur l - 1 / 4) * (1 / 2 - pur l)

/-- **`lem:fqe-near-uniform-dual`**: with the HT row at `q_s`, every four-point spectrum with
`p ≤ 29/100` satisfies `Λ_θ(c₂) - Λ_θ(λ) ≥ (p - 1/4)/125`. -/
def NearUniformDual : Prop :=
  ∀ l : Fin 4 → ℝ, IsProb4 l → pur l ≤ 29 / 100 →
    (pur l - 1 / 4) / 125 ≤ Lam qS aH bH gH c2 - Lam qS aH bH gH l

/-- `κ = 4√3/5`. -/
noncomputable def kappaSL : ℝ := 4 * Real.sqrt 3 / 5

/-- `F_c = -1 + 8ε + 9p - 12t`. -/
noncomputable def Fc (ε p t : ℝ) : ℝ := -1 + 8 * ε + 9 * p - 12 * t

/-- `X = 1/2 + ε - p`. -/
noncomputable def Xs (ε p : ℝ) : ℝ := 1 / 2 + ε - p

/-- `G_± = Λ(c₁) - Λ(λ) + ℓ(ε, F_c ± κX) - ℓ(0, 1/2)` (the HT row, order `q_s`);
`s = ±1` is the sign. -/
noncomputable def Gsl (s ε : ℝ) (μ : Fin 4 → ℝ) : ℝ :=
  Lam qS aH bH gH c1 - Lam qS aH bH gH μ
    + ell aH bH gH ε (Fc ε (pur μ) (cub μ) + s * kappaSL * Xs ε (pur μ)) - ell aH bH gH 0 (1 / 2)

/-- **`lem:fqe-cluster-sliver`**: on either ordered chart, if `p ≥ 47/100`, `X ≥ 0`,
`0 ≤ ε ≤ 1/100` and `[F_c - κX, F_c + κX] ∩ [11/25, 1/2] ≠ ∅`, then `G_± ≥ 0`, with equality only at
`λ = c₁`, `ε = 0`. -/
def ClusterSliver : Prop :=
  ∀ μ : Fin 4 → ℝ, IsChart μ → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 100 → 47 / 100 ≤ pur μ →
    0 ≤ Xs ε (pur μ) →
    (∃ F : ℝ, Fc ε (pur μ) (cub μ) - kappaSL * Xs ε (pur μ) ≤ F ∧
        F ≤ Fc ε (pur μ) (cub μ) + kappaSL * Xs ε (pur μ) ∧ 11 / 25 ≤ F ∧ F ≤ 1 / 2) →
    ∀ s : ℝ, (s = 1 ∨ s = -1) → 0 ≤ Gsl s ε μ ∧ (Gsl s ε μ = 0 → μ = c1 ∧ ε = 0)

end FormalResearch.FourQubitEntropy.RenyiFull
