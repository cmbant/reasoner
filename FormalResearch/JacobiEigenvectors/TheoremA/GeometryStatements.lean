module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily

/-!
# Paper J, Layer 2: statement freeze for the geometry of the hypotheses (lem:tha-geom (a)--(d))

Source: Paper J `thmA.tex` Section 4.2, `lem:tha-geom`; `main_results.tex` (H1)--(H3), `lem:hyp-morse`; `charts.tex` (HW1)--(HW4), (HI1)--(HI4), `rem:cha-HI3`.
**Every statement is a Prop-valued `def`; nothing is proved here (no placeholder proofs, no added axioms).**  They are the inputs of the chart structures that
cannot be left as fields of `BulkWeberChart` / `SoftEdgeChart` forever: `overlap_in_well` (c), `uc_spec`, `geom_far`, `ucη_in`, `zeta_far` (d), the collision data (b).
Plan item L2.G4 of `PLAN.md` (hypothesis: `HypMorseEquiv` = L2.G1, to be proved first).

## Dictionary

| Lean | paper | content |
|---|---|---|
| `GeomBulk` | lem:tha-geom (a) | for one pair of principal symbols satisfying `Hyp` and `C^2`: `T > 0` exactly on `(u_-, u_+)`, simple endpoint zeros, `u_- = 0 <-> X = B_0(0)`, `u_+ = L <-> X = B_0(L)` |
| `GeomCollision` | lem:tha-geom (b) | uniform in `mu`: at a hard-edge collision energy `T` has `T(0) = 0`, `T'(0) = 4 L G_0(0) > 0`, and for `delta = X - B_0(0) != 0` small exactly one turning point `u_*(delta)` in `(0, U_0)` with the signs of (HW4); the right end is the same statement for `mirrorFamily F` |
| `GeomMargins` | lem:tha-geom (c), **corrected** (finding F-geom) | per energy block **and per parameter neighbourhood**: fixed `c' < c` in the oscillatory well with margin `delta_1`; `|T'(u_pm)|` bounded below away from the collisions |
| `GeomSoft`, `GeomSoftLower` | lem:tha-geom (d) | the soft edge at `X_s^+` (resp. `X_s^-`, through `negFamily`): `delta_0, eta`, the fold `u_c`, the Morse coordinate `t(x)` of `f_+`, the normal form (HI3), (HI1)--(HI4) |

## FINDINGS (paper statements made precise or corrected)

* **F-geom (single overlap, lem:tha-geom (c), as in the freeze)**: the paper states one pair `c' < c` with `u_-(X) + delta_1 <= c' < c <= u_+(X) - delta_1` for *all* `X` in a compact `J` inside the band.  This is **false** when
  `u_c^+ < u_c^-`: for `X` near `X_s^+` the allowed set is near `u_c^+`, for `X` near `X_s^-` it is near `u_c^-`, so `sup_J u_- > inf_J u_+`.  It is true on each interval of a finite cover of `J` (as `lem:smo-bulkphase`
  and Section `thb-matrices` already use).  `GeomMargins` is the corrected statement.
* **F-geom2 (uniformity in `mu` needs a localisation, not only a finite energy cover)**: even for one energy block the pair `(c', c)` cannot be chosen for all `mu in K` at once: `max_mu u_-(mu, X) < min_mu u_+(mu, X)` can fail
  for a compact `K` (two parameter values with `u_c^+(mu_1) < u_c^-(mu_2)` after a shift).  The paper's "Localisation in the parameter" paragraph (thmA.tex, sec:tha-standing) supplies the fix: every `mu_0 in K` has a
  compact neighbourhood `K'` on which one choice of blocks serves, and finitely many `K'` cover `K`.  `GeomMargins` is therefore stated around each `mu_0 in K`.  Consequence for the freeze: `ChartInputs F K ...` (one block
  family for the whole `K`) is a hypothesis that is satisfiable only for localised `K`; `ThmAii` etc. remain *true as stated* (they take the charts as an argument) and the global theorem follows by a finite cover
  (`GeomMargins` + the restriction `DM F K' M` of `DM F K M`); the combination (one explicit `Psi-hat` per `k`) is a bookkeeping step recorded in `PLAN.md`.
* **F-geom3 (lem:tha-geom (d), `delta_0` against `eta`)**: the paper chooses `eta` first and then `delta_0 < nu/2`; the freeze left `(delta_0, eta)` free in `SoftEdgeChart`.  `GeomSoft` quantifies
  "for every `eta <= eta_0` there is `delta_* > 0` such that every `delta_0 <= delta_*` works" and the chart structure records the consequence (`SoftEdgeChart.geom_far`, `zeta_far`, ...).
* **F-geom4**: (b) is stated for the *principal* symbols only (the jets' regularity beyond `C^2` is not needed); `deriv` of `T(.;X)` at the endpoints `0, L` is the one-sided `derivWithin ... (Icc 0 L)`.
* `r`-dependence: (d) asserts the Morse coordinate `t` of class `C^{r-2}` where `G_0, B_0 in C^r`; (a)--(c) use `r = 2`.

## Not here

`lem:hyp-morse` (`HypMorseEquiv`, `HypOpen` in `Statements.lean`), the freezing statement (`FrozenStandard`), the chart constructions (Layer 4).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set Finset Filter Topology FormalResearch.JacobiEigenvectors.Setting

variable {Par : Type*} [TopologicalSpace Par]

/-- The allowed set `{u in [0, L] : T(u; X) >= 0}` of principal symbols `G_0, B_0`. -/
def allowedSet (L : ℝ) (G0 B0 : ℝ → ℝ) (X : ℝ) : Set ℝ := Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u}

/-- Its left end `u_-(X)` (`inf`). -/
def uMinusS (L : ℝ) (G0 B0 : ℝ → ℝ) (X : ℝ) : ℝ := sInf (allowedSet L G0 B0 X)

/-- Its right end `u_+(X)` (`sup`). -/
def uPlusS (L : ℝ) (G0 B0 : ℝ → ℝ) (X : ℝ) : ℝ := sSup (allowedSet L G0 B0 X)

/-- `SymbolFamily.uMinus` is `uMinusS` at the principal symbols of `mu` (definitional). -/
theorem uMinus_eq_uMinusS (F : SymbolFamily Par) (μ : Par) (X : ℝ) :
    F.uMinus μ X = uMinusS F.L (F.G 0 μ) (F.B 0 μ) X := rfl

theorem uPlus_eq_uPlusS (F : SymbolFamily Par) (μ : Par) (X : ℝ) :
    F.uPlus μ X = uPlusS F.L (F.G 0 μ) (F.B 0 μ) X := rfl

/-- Standing regularity of the principal symbols of a family on `K`: `G_0, B_0 in C^r([0, L])`, jointly continuous derivatives in `mu in K`
(the principal part of `(D_M)`; `r >= 2`).  Without joint continuity "uniform margins by compactness and continuity" (finding F-loc) has no content. -/
def PrincipalReg (F : SymbolFamily Par) (K : Set Par) (r : ℕ) : Prop :=
  JetReg (F.G 0) K F.L r ∧ JetReg (F.B 0) K F.L r

/-! ### (a) bulk -/

/-- **lem:tha-geom (a)** (statement): for principal symbols with `(H1)--(H3)` (`Hyp`) of class `C^2`, and `X` in the open band: `T(.;X) > 0` exactly on `(u_-, u_+)`, `u_- < u_+`,
`T < 0` on `[0, L]` outside `[u_-, u_+]`, the only zeros of `T` in `[0, L]` are `u_-, u_+`, both simple when interior (`T' != 0`), `u_- = 0` iff `X = B_0(0)`, `u_+ = L` iff `X = B_0(L)`.
(In particular `Q_0(0) Q_0(L) != 0` unless `X` is a collision energy.) -/
def GeomBulk : Prop :=
  ∀ (L : ℝ) (G0 B0 : ℝ → ℝ) (g : ℝ), 0 < L → Hyp L G0 B0 g → ContDiffOn ℝ 2 G0 (Icc 0 L) → ContDiffOn ℝ 2 B0 (Icc 0 L) →
    ∀ X : ℝ, Xsm L G0 B0 < X → X < Xsp L G0 B0 →
      uMinusS L G0 B0 X < uPlusS L G0 B0 X ∧
      (∀ u ∈ Icc 0 L, 0 < Tfun L G0 B0 X u ↔ uMinusS L G0 B0 X < u ∧ u < uPlusS L G0 B0 X) ∧
      (∀ u ∈ Icc 0 L, u ∉ Icc (uMinusS L G0 B0 X) (uPlusS L G0 B0 X) → Tfun L G0 B0 X u < 0) ∧
      (∀ u ∈ Icc 0 L, Tfun L G0 B0 X u = 0 ↔ u = uMinusS L G0 B0 X ∨ u = uPlusS L G0 B0 X) ∧
      (0 < uMinusS L G0 B0 X → deriv (Tfun L G0 B0 X) (uMinusS L G0 B0 X) ≠ 0) ∧
      (uPlusS L G0 B0 X < L → deriv (Tfun L G0 B0 X) (uPlusS L G0 B0 X) ≠ 0) ∧
      (uMinusS L G0 B0 X = 0 ↔ X = B0 0) ∧ (uPlusS L G0 B0 X = L ↔ X = B0 L)

/-! ### (b) collisions -/

/-- The conclusion of lem:tha-geom (b) at the **left** end for the family `F` on `K`, uniform in `mu`: there are `U_0, delta_1, p_min > 0` such that for every `mu in K`:
`P_0 = sqrt((L - u) G_0) >= p_min` on `[0, U_0]` (HW2); at the collision energy `X_c = B_0(0)`: `T(0) = 0`, `T'(0) = 4 L G_0(0) > 0` (one-sided) and `T > 0` on `(0, U_0]`; for
`delta = X - X_c`, `0 < |delta| <= delta_1`, `T(.; X)` has exactly one zero `u_*(delta) in (0, U_0)` with `T < 0` on `[0, u_*)` and `T > 0` on `(u_*, U_0]` (HW3, HW4; `Q_0 = delta + B_0(0) - B_0(u)` is affine
in `delta`, `Q_0(0;0) = 0`, `d_delta Q_0 = 1`, so those are not restated). -/
def GeomCollisionLeftConcl (F : SymbolFamily Par) (K : Set Par) : Prop :=
  ∃ U0 δ1 pmin : ℝ, 0 < U0 ∧ U0 < F.L ∧ 0 < δ1 ∧ 0 < pmin ∧ ∀ μ ∈ K,
    (∀ u ∈ Icc 0 U0, pmin ≤ Real.sqrt ((F.L - u) * F.G 0 μ u)) ∧
    Tfun F.L (F.G 0 μ) (F.B 0 μ) (F.B 0 μ 0) 0 = 0 ∧
    derivWithin (Tfun F.L (F.G 0 μ) (F.B 0 μ) (F.B 0 μ 0)) (Icc 0 F.L) 0 = 4 * F.L * F.G 0 μ 0 ∧
    0 < 4 * F.L * F.G 0 μ 0 ∧
    (∀ u ∈ Ioc 0 U0, 0 < Tfun F.L (F.G 0 μ) (F.B 0 μ) (F.B 0 μ 0) u) ∧
    ∀ X : ℝ, X ≠ F.B 0 μ 0 → |X - F.B 0 μ 0| ≤ δ1 →
      ∃ us ∈ Ioo 0 U0, Tfun F.L (F.G 0 μ) (F.B 0 μ) X us = 0 ∧
        (∀ u ∈ Ico 0 us, Tfun F.L (F.G 0 μ) (F.B 0 μ) X u < 0) ∧ (∀ u ∈ Ioc us U0, 0 < Tfun F.L (F.G 0 μ) (F.B 0 μ) X u)

/-- **lem:tha-geom (b)** (statement): under compactness of `K`, `(H1)--(H3)` on `K` and `C^2` principal symbols, the collisions at both hard edges are transverse, uniformly in `mu in K`
(the right end is the left end of `mirrorFamily F`). -/
def GeomCollision (F : SymbolFamily Par) (K : Set Par) : Prop :=
  IsCompact K → HypOn F K → PrincipalReg F K 2 →
    GeomCollisionLeftConcl F K ∧ GeomCollisionLeftConcl (mirrorFamily F) K

/-! ### (c) margins, per energy block and per parameter neighbourhood (finding F-geom, F-geom2) -/

/-- **lem:tha-geom (c)**, corrected (finding F-geom, F-geom2).  Let `J` be compact with `J subset (X_s^-, X_s^+)` for all `mu in K`.  For every `mu_0 in K` there is a neighbourhood `N` of `mu_0` in `K`, finitely many
closed energy intervals `J_nu` covering `J`, numbers `c'_nu < c_nu` and `delta_1 > 0` such that for **all `mu in N`** and `X in J_nu`: `u_-(X) + delta_1 <= c'_nu < c_nu <= u_+(X) - delta_1`.  Moreover (uniformly on
`K x J`) `|T'(u_pm)|` is bounded below at every non-collision energy: for every `epsilon > 0` there is `c_T > 0` with `|T'(u_-)|, |T'(u_+)| >= c_T` whenever `|X - B_0(0)|, |X - B_0(L)| >= epsilon`. -/
def GeomMargins (F : SymbolFamily Par) (K : Set Par) : Prop :=
  IsCompact K → HypOn F K → PrincipalReg F K 2 →
    ∀ J : Set ℝ, IsCompact J → (∀ μ ∈ K, ∀ X ∈ J, F.bandLo μ < X ∧ X < F.bandHi μ) →
      (∀ μ0 ∈ K, ∃ N ∈ 𝓝[K] μ0, ∃ (n : ℕ) (Jν : Fin n → Set ℝ) (c' c : Fin n → ℝ) (δ1 : ℝ), 0 < δ1 ∧
        (∀ X ∈ J, ∃ ν, X ∈ Jν ν) ∧ (∀ ν, IsClosed (Jν ν) ∧ Jν ν ⊆ J) ∧ (∀ ν, c' ν < c ν) ∧
        ∀ ν, ∀ μ ∈ N, μ ∈ K → ∀ X ∈ Jν ν, F.uMinus μ X + δ1 ≤ c' ν ∧ c ν ≤ F.uPlus μ X - δ1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ cT : ℝ, 0 < cT ∧ ∀ μ ∈ K, ∀ X ∈ J, ε ≤ |X - F.B 0 μ 0| → ε ≤ |X - F.B 0 μ F.L| →
        cT ≤ |deriv (Tfun F.L (F.G 0 μ) (F.B 0 μ) X) (F.uMinus μ X)| ∧ cT ≤ |deriv (Tfun F.L (F.G 0 μ) (F.B 0 μ) X) (F.uPlus μ X)|)

/-! ### (d) soft edges -/

/-- The conclusion of lem:tha-geom (d) at the **upper** soft edge of `F` on `K` (uniform in `mu`).  There is `eta_0 > 0` such that for every `eta in (0, eta_0]` there are `delta_* > 0`, a fold `u_c(mu)`
(the maximiser of `f_+`), the real Morse coordinate `t(x; mu)` of `f_+` at `u_c` (`f_+(u_c + x) = X_s^+ - t(x)^2`, of class `C^{r-2}`, `t(0) = 0`, `t' >= c_t > 0` on `|x| <= 2 eta`), and constants `a_min, eta_1 > 0` with:
`E_0 >= a_min^2` on the collar `|u - u_c| <= 2 eta` (HI2), `Q_0 > 0` at the two ends `0, L` at `X = X_s^+` (a soft edge never meets a collision), `sqrt(delta_*) < min(|t(-2 eta)|, t(2 eta))/2` (HI4), and for every `delta_0 <= delta_*`
and `|X - X_s^+| <= delta_0`: `{T >= 0} subset (u_c - eta/4, u_c + eta/4)`; `T < 0` and `Q_0 > 0` on `|u - u_c| >= eta/4`; the normal form (HI3) `(X - B_0)/(2 sqrt E_0) = 1 + (t^2 - alpha) G/2`, `G = 1/sqrt E_0`,
`alpha = X_s^+ - X`, on `|x| <= 2 eta`; `Upsilon_0 > -1` on the collar and `Upsilon_0 >= 1 + eta_1` at its two ends (HI4). -/
def GeomSoftConcl (F : SymbolFamily Par) (K : Set Par) (r : ℕ) : Prop :=
  ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η ≤ η0 → ∃ δs : ℝ, 0 < δs ∧
    ∃ (uc : Par → ℝ) (tf : Par → ℝ → ℝ) (ct aMin η1 : ℝ), 0 < ct ∧ 0 < aMin ∧ 0 < η1 ∧ ∀ μ ∈ K,
      (0 < uc μ - 2 * η ∧ uc μ + 2 * η < F.L ∧ fPlus F.L (F.G 0 μ) (F.B 0 μ) (uc μ) = F.bandHi μ) ∧
      ContDiffOn ℝ ((r - 2 : ℕ) : WithTop ℕ∞) (tf μ) (Icc (-2 * η) (2 * η)) ∧ tf μ 0 = 0 ∧
      (∀ x ∈ Icc (-2 * η) (2 * η), ct ≤ deriv (tf μ) x ∧
        fPlus F.L (F.G 0 μ) (F.B 0 μ) (uc μ + x) = F.bandHi μ - tf μ x ^ 2) ∧
      (∀ x ∈ Icc (-2 * η) (2 * η), aMin ≤ Real.sqrt (E0 F.L (F.G 0 μ) (uc μ + x))) ∧
      (0 < F.bandHi μ - F.B 0 μ 0 ∧ 0 < F.bandHi μ - F.B 0 μ F.L) ∧
      Real.sqrt δs < min |tf μ (-2 * η)| (tf μ (2 * η)) / 2 ∧
      ∀ δ0 : ℝ, 0 < δ0 → δ0 ≤ δs → ∀ X : ℝ, |X - F.bandHi μ| ≤ δ0 →
        (∀ u ∈ Icc 0 F.L, 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u → uc μ - η / 4 < u ∧ u < uc μ + η / 4) ∧
        (∀ u ∈ Icc 0 F.L, η / 4 ≤ |u - uc μ| → Tfun F.L (F.G 0 μ) (F.B 0 μ) X u < 0 ∧ 0 < X - F.B 0 μ u) ∧
        (∀ x ∈ Icc (-2 * η) (2 * η),
          (X - F.B 0 μ (uc μ + x)) / (2 * Real.sqrt (E0 F.L (F.G 0 μ) (uc μ + x)))
            = 1 + (tf μ x ^ 2 - (F.bandHi μ - X)) / (2 * Real.sqrt (E0 F.L (F.G 0 μ) (uc μ + x)))) ∧
        (∀ x ∈ Icc (-2 * η) (2 * η), -1 < (X - F.B 0 μ (uc μ + x)) / (2 * Real.sqrt (E0 F.L (F.G 0 μ) (uc μ + x)))) ∧
        (1 + η1 ≤ (X - F.B 0 μ (uc μ - 2 * η)) / (2 * Real.sqrt (E0 F.L (F.G 0 μ) (uc μ - 2 * η))) ∧
          1 + η1 ≤ (X - F.B 0 μ (uc μ + 2 * η)) / (2 * Real.sqrt (E0 F.L (F.G 0 μ) (uc μ + 2 * η))))

/-- **lem:tha-geom (d)** (statement), upper soft edge: compactness of `K`, `(H1)--(H3)` on `K`, `G_0, B_0 in C^r` (`r >= 2`), jointly continuous in `mu`, give `GeomSoftConcl`. -/
def GeomSoft (F : SymbolFamily Par) (K : Set Par) (r : ℕ) : Prop :=
  2 ≤ r → IsCompact K → HypOn F K → PrincipalReg F K r → GeomSoftConcl F K r

/-- **lem:tha-geom (d)**, lower soft edge: the same for the gauge family `negFamily F` (diagonal `-B_n`; its upper edge is `-X_s^-` of `F`; the fold is `u_c^-`). -/
def GeomSoftLower (F : SymbolFamily Par) (K : Set Par) (r : ℕ) : Prop :=
  2 ≤ r → IsCompact K → HypOn F K → PrincipalReg F K r → GeomSoftConcl (negFamily F) K r

/-- The whole of lem:tha-geom for a family (the `r` is the regularity of the principal symbols). -/
def TheGeometry (F : SymbolFamily Par) (K : Set Par) (r : ℕ) : Prop :=
  GeomBulk ∧ GeomCollision F K ∧ GeomMargins F K ∧ GeomSoft F K r ∧ GeomSoftLower F K r

end FormalResearch.JacobiEigenvectors.TheoremA
