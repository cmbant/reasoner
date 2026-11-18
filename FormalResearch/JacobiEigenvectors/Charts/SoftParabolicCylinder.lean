module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily
public import FormalResearch.JacobiEigenvectors.Charts.LadderChain
public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.Regularity
public import FormalResearch.JacobiEigenvectors.Charts.BulkWeber
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftRescale

/-!
# Paper J, charts: the soft-edge (parabolic-cylinder) chart

Source: Paper J `charts.tex`: `lem:cha-PCcoord` (coordinate `zeta`, quantised shifts `mu_{2r}`), `thm:cha-PC` (comparison through coalescence;
**derived** in Layer 2 from this structure and the engine), `lem:cha-PCenv` (in `ParabolicCylinderFacts`); `thmA.tex` Sections "The comparison
sequences" (eq:tha-weber-seq, eq:tha-aPC, eq:tha-PCseq), "The soft edges" (eq:tha-YLsoft), `lem:tha-geom` (d), `prop:tha-W2`;
`app_thmA.tex` "The soft edges: proof of Proposition prop:tha-W2" Steps 1--3.

`SoftEdgeChart F P m q U V` is the hypothesis that the *left* soft-edge chart exists at the upper band edge `X_s^+` for all `mu in P`, all
`X` with `|X - X_s^+| <= delta_0`, all `N >= N0`.  It consists of **two** ladder chains (corrected in round 3, findings F-W2-1..3):

* `chainW` (Step 1): the single-patch, turning-point-free Weber chart on `[0, u_c - eta/2]` (coordinate `Y`, eq:tha-YLsoft), with weights `E_Web, M_Web`;
  its comparison sequence `phi^{(1)}_1` is the `psi-hat^{L,Web}` of `prop:tha-W2`.
* `chain` (Step 3): the march (Weber patch) -> (PC patch on `Z <= 0`) -> (PC patch on `Z >= 0`), **three patches**, hard-edge seed.  Patch 1 is the Weber patch of `chainW` up to the overlap bond
  `j_1` (`u_{j_1} <= u_c - eta < u_{j_1+1}`, **forbidden** for both charts); patch 2 carries the `-` pair `(u~(a,-Z), -v~(a,-Z))` with weight `E_-(a,Z) = E_well(a,|Z|)`
  (`a <= 0`) resp. `E_bar(a,Z)^{-1}` (`a > 0`); patch 3 the *swapped* pair `(v~, -u~)` (dominant member first) with weight `E_well(a,Z)^{-1}` resp. `E_bar^{-1}`, the switch at the bond `j_2`
  with `Z_{j_2} <= 0 < Z_{j_2+1}` (the transfer matrix there is `(M_-(a) S)^{-1}`, bounded: `pcSwap_eq_pcMinus`).  For `a > 0` the paper uses one PC pair; here patch 3 carries the **same** pair
  and weight as patch 2 (so `M_2 = 1`), which makes the chain uniform (`P = 3` for every `a`).  Patches 2 and 3 share the ladder and the corrector rows (`shared_PC`), as in the paper (one chart `A^{[m]}, B^{[m]}`).

`zeta` is the coordinate `Z_n = h^{-1/2} zeta(u_n - u_c; alpha)`, `a = a^{[q]}_PC` (eq:tha-aPC).  The *right* chart is `SoftEdgeChart (mirrorFamily F)`; the lower edge is `SoftEdgeChart (negFamily F)` (gauge `(-1)^n`, energy `-X`).

## Fields, with statement and discharging result

* `valid` (**corrected, F-W2-1; round 4: `PreValid`**): the engine hypotheses *without (S3)* for the three-patch chain **with its first pair rescaled by `(lam^{-1}, lam)`**, `lam = softLamVal` (`LadderData.rescale1`, `SoftRescale.lean`):
  (SM1)--(SM3) for the Weber ladder (`lem:cha-weber-ladder`) and the PC ladder (`T_pm`, `thm:cha-PC` proof), defect bounds `eq:eng-UC1` (`thm:eng-corr`; Layer-1 output),
  `env` (`lem:cha-weber-env`, `lem:cha-PCenv`), `W_mono`.  **(S3) is derived** (`TheoremA/SoftTransfer.lean`, `soft_valid`): at `j_1` (forbidden overlap, `PreValid.transferAt_forbidden`) from `bondA_le`, the margin `k_2 >= c/h`
  (`Y_forb`, `zeta_far`, `muS_bd`) and the one-step comparison of `E_-`; at `j_2` (bounded overlap) from `pcSwap_eq_pcMinus`.
* `validW` etc.: the same for `chainW` (`P = 1`, no (S3)); `patch1_eq`: the first patch of `chain` is that of `chainW` (same ladder, pair and corrector rows).
* `zeta_*`, `muS_*`, `mu0_*`: `lem:cha-PCcoord` (the real two-turn Moser coordinate `zeta` and the shifts `mu_{2r}`; `thm:smo-MPS`, `thm:smo-TPC`, `thm:smo-WT2`); Layer 4.
* `Y_*`, `matchF_soft`: the turning-point-free Weber coordinate `Y_L` (`prop:cha-halfrow`(b)), eq:tha-YLsoft.
* `wfW_eq`, `wf2_eq`, `wf3_eq`: the model pairs are the Weber / PC functions of `ParabolicCylinderFacts` (both members of each pair).
* `W1_def`, `W2_def`, `W3_def`, `M1_def`, `M2_def`: the global weights of `chain` are `E_Web/lam`, `E_-`, `E_swap = E_well(a,.)^{-1}` and `M_Web`, `M_bal`; `lam = E_Web(j_1)/E_-(j_1)` is *derived* (`softLamVal`), not a field.
  `W_defW`, `M_defW`: `E_Web`, `M_Web` for `chainW`.

## Round 3 (first proof attempt of `PropThaW2` (1), `TheoremA/SoftProof.lean`): verdicts on the findings F-W2-1..7 (each checked against `app_thmA` Steps 1--3, `charts.tex` `thm:cha-PC`, `engine.tex` after `thm:eng-volterra`)

* **F-W2-1 confirmed, fixed.**  The frozen `valid` asked `Valid` for the unrescaled chain whose patch-1 weight is `E_Web/lam`; `Valid.env` then forces `lam ~ 1`, but the paper (Step 3, (W2)) says `lam` "may be exponentially large or
  small" and rescales the Weber pair by `(lam^{-1}, lam)`.  `valid` is now about `(chain).rescale1 lam`; `wfW_eq`, `lamL`, `psiHatL`, `PropThaW2` still refer to the unrescaled pair.
* **F-W2-2 confirmed (paper: Step 2), fixed.**  For `a <= 0` the pair `(u_-, v_-)` is recessive-first only for `Z <= 0`; the weight `E_well(a,|Z|)` is not non-decreasing for `Z > 0`, so `env`/`W_mono` fail for a genuine chart with two patches.
  The paper uses three patches for `a <= 0` and the swapped pair with `E_well^{-1}` for `Z >= 0`.  Fixed uniformly: `P = 3` always (for `a > 0` patch 3 = patch 2), the new weight `Eswap`, the new pair `pcSwap`,
  the bond `j_2`, and `W2_def/W3_def/wf2_eq/wf3_eq` split accordingly.  `pcSwap_eq_pcMinus` proves `(v~, -u~) = (u_-, v_-) M_-(a) S` from `ParabolicCylinderFacts.reflect, reflect_V`.
* **F-W2-3 confirmed (paper: Step 1 is a separate chart, `cor:cha-I-general`), fixed.**  `chainW` (`P = 1`) with the Weber `Valid` and the weights `E_Web, M_Web`; `psiHatL` takes its Weber part from `chainW` on all of `u <= u_c - eta/2`
  (the chain `chain` has the Weber patch only up to `j_1`).  `patch1_eq` makes the two Weber patches one.
* **F-W2-4, F-W2-5 confirmed** (paper: "Fix `m >= 1`", `Lm = 1` or `log(1/h)`): `PropThaW2` now assumes `1 <= m` and `forall h in (0,1], 1 <= Lm h` (`TheoremA/Statements.lean`).
* **F-W2-6 refined.**  (i) the absorption `Lambda h^{-m} (E_{j_1}/E_n)^2 <= e^{-c/h}` follows from the chart fields (`zeta_deriv`, `zeta_far`, `muS_bd`) and the definition of `Ewell`: **not** added;
  (ii) `eq:cha-MolvEquiv` (two-sided `M_Olv ~ kappa^{-1} W_well M_bal`, lower bound inside the well) and (iii) the growth of the dominant member (`r_2 < 1`) are classical (Olver, Riccati) and were added to
  `ParabolicCylinderFacts` (`molv_well`, `molv_bar`, `V_growth`, plus `reflect_V` for `M_-(a)`), numerically checked (see there).
* **F-W2-7 resolved (round 4).**  `LadderData.Valid` is split into `PreValid` (everything but (S3)) and `Valid` (adds `transfer`); `SoftEdgeChart.valid` is `PreValid` and (S3) is *derived* in `TheoremA/SoftTransfer.lean` (`soft_valid`) with the explicit
  `Lambda = softLamC`.  The chart-level inputs that this needed and that were not fields are now fields: `bondA_le` (`a_n <= C_A`) and `muS_bd` for `r = 0` (`|mu_0| <= C_mu`, so that `a h = -tilde mu` is bounded); everything else
  (`k_2 >= c/h`, the one-step ratio of `E_-`, `E_- ~ 1` at `j_2`) is derived from `Y_forb`, `zeta_deriv`, `zeta_far`, `muS_bd`, the definition of `Ewell`/`Ebar` and `pcSwap_eq_pcMinus`.
* **F-W2-8 (item (4), `rho_one`/`theta_le`) applied (round 6).**  For odd `m` and `q = m - 1` (one shift short) the paper has `Theta <= C log(1/h)` with defect weights `rho_k` not identically `1`; the old structure fixed `rho = rho~ = 1`
  and `Theta <= Csum`.  Now `SoftEdgeChart F P m q U V Lm` has the parameter `Lm : ℝ → ℝ` (`1` for items (1)--(3), `1 + log(1/h)` for item (4)), `theta_le`/`theta_leW` read `Theta <= Csum * Lm(h)`, and `rho_one`/`rho_oneW` are deleted
  (they were used only for the soft chart's own `Theta` bound; the bulk chart keeps its own).  **Two chart fields about `Lm` were needed that the proposal in `PLAN.md` did not list**: `Lm_one` (`1 <= Lm` on `(0,1]`, the hypothesis already of `PropThaW2`) and
  `Lm_small` (`h Lm(h) -> 0`), without which the engine smallness `2 K_D K_w h^m Theta <= c_*` has no threshold for `h` (for `Lm = h^{-10}` the conclusion of `PropThaW2` is false).  `ChartInputs` uses `Lm = fun _ => 1` (Theorem A needs `q >= m`).
* **New, F-W2-11 (round 5, R4: the lower half of (c)).**  The lower bound `|lambda_L| >= c lambda kappa_bal` (`TheoremA/SoftLower.lean`) uses the paper's Step 3 (i)--(iii); of its inputs `grow_gap` (growth margin of the exact solution, `eq:tha-S4grow`),
  `collar_lbW` (lem:cha-W0 for the Weber chart) and `ratio2` (`r_2 = e^{-theta}(1+O(h))`) were fields of round 4, and the comparison `M_{j_1+1} <= C_M M_{j_1}` ("`M^2_Web ~ h^{1/2}` there") is the new field `ratioM`
  (it needs an upper bound `k_2 <= C/h` at the two rows, which `Y_forb` does not give: `Y` is only bounded below there).  Nothing else was needed: `r_W >= 1 + gamma/2` is *derived* from the exact solution (`growth_ratio`) and the engine bound.
* **New, F-W2-9 (endpoint).**  `prop:tha-W2` (1) displays the PC range as `u_c - eta/2 <= u_n`, `psi-hat^L` is Weber for `u_n <= u_c - eta/2` (item (2)); the two ranges overlap at one row.  `PropThaW2` now has the strict `u_c - eta/2 < u_n` in the PC bound.
* **New, F-W2-10 (wf 1 1).**  The second member of the Weber pair was not pinned in the soft chart (only `wf 1 0`); `wfW_eq` pins both (as `BulkWeberChart.wf_eq`).

## Satisfiability

As for `BulkWeberChart`: no toy instance (the fields mention the actual parabolic-cylinder functions); the engine hypotheses are non-vacuous (`JE.volterra_multi_instance`); rescaling preserves (SM1)--(SM3) and the Casoratians (`SoftRescale.lean`),
and the new `shared_PC`, `patch1_eq` are the paper's identifications (one corrector row for one chart).  `lam` may be any positive number: `W_mono` and `env` for the rescaled chain are the paper's.

## Round 2 audit: `SoftEdgeChart` (verdict: fixed, four fields added)

* **(a) fields vs. the paper.**  `zeta_deriv, zeta_zero, zeta_alpha, mu0_*` are lem:cha-PCcoord (1) with `x = u - u_c`; `mu0_S0` is eq:cha-mu0 (`pi mu_0 = ` the well action `S_0 = int_0^L Re arccos`;
  the `Real.arccos` clamp reproduces `pi |{Q_0 < -2 sqrt E_0}|`, and `geom_far` shows that near `X_s^+` the clamp is `0` outside the well); `Y_forb, matchF_soft` are eq:tha-YLsoft (`arccoshR` is applied
  to arguments `>= 1`, guaranteed by `geom_far`); `pcMinus`: `(u~(a,-Z), -v~(a,-Z))` for `a <= 0`,
  `(w~_+, -u~_+)` for `a > 0`, so that `phi^{(1)}_2 / kappa_bal = A U(a,-Z) + h B h^{1/2} (U(a,-.))'` is `psi-hat^{PC,-}`.
* **FIX (b) `geom_far`, `ucη_in`.**  `delta_0, eta` are chart *data*; lem:tha-geom (d) holds only for a pair with `delta_0` small against `eta` (the paper: "`eta` first, then `delta_0 < nu/2`").
  Nothing in the freeze forced that, so `PropThaW2`, `PropThaMflat`, `PropThaCollar` (which use `T < 0, Q_0 > 0` outside the collar for the growth bound (S4grow) and the forbidden margin)
  would have been *false* for charts with a large `delta_0`: a hypothesis that is too weak, not a conclusion smuggled in.  Now `geom_far` records that pair, and `ucη_in` that the collar `[u_c - 2 eta, u_c + 2 eta]` lies in `(0, L)`.
* **FIX (b) `zeta_far`, `muS_bd`, `Cmu`, `cz1`.**  `PropThaWin`'s last item of (1) (`|Z_n| <= rho' => |u_n - u_c| < eta/4`) and the exponential smallness of the weight at `n_1 + 1` (Step 4 (d) (ii)) need that
  the turning points `+-2 sqrt(mu_0)` of `zeta` are inside `|x| < eta/4` with a margin, and that `mu~ = mu_0 + sum h^{2r} mu_{2r}` stays within `O(h^2)` of `mu_0`; both are `delta_0` small / lem:cha-PCcoord (2) and
  were not in the freeze.  Consistency of the new fields with the old ones: at `alpha = 0`, `zeta' >= d_-` gives `zeta(x)^2 >= d_-^2 eta^2/16`, so `cz1 <= d_-^2 eta^2 / 16` is needed; for `|alpha| <= delta_0` small it persists by `zeta_alpha`.
* **(b) vacuity check.**  No field mentions an eigenvalue/eigenvector; fields are pairwise consistent for the genuine chart (e.g. the soft edge of the exactly solvable spin family `G_h = 1, B_h = 0`, `L = 1`, fold `u_c = 1/2`).
  `mu0_deriv` asks `ContDiff 1` on all of `R` for `muS 0 mu` (the paper has it on `[-alpha_0, alpha_0]`; any `C^1` extension serves).
* **(c) redundancy.**  `uc_spec` partly overlaps `ucη_in`/`geom_far` (the fold is the unique maximiser of `f_+`); `zeta_zero` follows from `zeta_alpha` at `alpha = 0`.

## Honest differences

* `thm:cha-PC` in the paper states one comparison with the two-pair weights; here the same content is the three-patch chain.  The conclusion in terms of
  `lambda_L`, `M_Olv` (prop:tha-W2 (1)) is the *Layer-2* statement `TheoremA.PropThaW2`, derived from `LadderData.Stability`.
* for `a > 0` the chain has a dummy third patch (same pair and weight as patch 2); the engine bound for it is the paper's two-patch bound with `P = 3` in the constant `mvC`.
* the lower edge is obtained by `negFamily`; no separate structure.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Engine

/-- The `-` pair `(y_1, y_2)` of lem:cha-PCenv (via `ParabolicCylinderFacts`), as functions of `Z`:
`a <= 0`: `(u~(a,-Z), -v~(a,-Z))`; `a > 0`: `(w~_+, -u~_+) = (kappa U(a,-Z), -kappa U(a,Z))`. -/
def pcMinus (U V : ℝ → ℝ → ℝ) (a : ℝ) : Fin 2 → ℝ → ℝ
  | 0 => fun z => if a ≤ 0 then ut U a (-z) else kappaBal a * U a (-z)
  | 1 => fun z => if a ≤ 0 then -vt V a (-z) else -(kappaBal a * U a z)

/-- The swapped pair of patch 3 (`Z >= 0`, dominant member first): `a <= 0`: `(v~(a,Z), -u~(a,Z))` (app_thmA Step 2);
`a > 0`: the same pair as `pcMinus` (`(w~_+, -u~_+)` serves on the whole chart). -/
def pcSwap (U V : ℝ → ℝ → ℝ) (a : ℝ) : Fin 2 → ℝ → ℝ
  | 0 => fun z => if a ≤ 0 then vt V a z else kappaBal a * U a (-z)
  | 1 => fun z => if a ≤ 0 then -ut U a z else -(kappaBal a * U a z)

/-- The recessive weight of the `-` pair (patch 2): `E_well(a,|Z|)` (`a <= 0`) or `E_bar(a,Z)^{-1}` (`a > 0`). -/
def Eminus (a z : ℝ) : ℝ := if a ≤ 0 then Ewell a |z| else (Ebar a z)⁻¹

/-- The weight of the swapped pair (patch 3): `E_well(a,Z)^{-1}` (`a <= 0`, `Z >= 0`) or `E_bar(a,Z)^{-1}` (`a > 0`, so `Eswap = Eminus` there). -/
def Eswap (a z : ℝ) : ℝ := if a ≤ 0 then (Ewell a |z|)⁻¹ else (Ebar a z)⁻¹

/-- The soft-edge PC parameter `a^{[q]}_PC = -(1/h)(mu_0(alpha) + sum_{r=1}^{q/2} h^{2r} mu_{2r}(alpha))` (eq:tha-aPC), `muS r` = `mu_{2r}`. -/
def aPC (muS : ℕ → ℝ → ℝ) (q : ℕ) (h α : ℝ) : ℝ :=
  -(1 / h) * (muS 0 α + ∑ r ∈ Icc 1 (q / 2), h ^ (2 * r) * muS r α)

/-- `lambda = E_Web(j_1)/E_-(j_1)` (app_thmA Step 3 (W2)): the ratio of the Weber barrier weight to that of the PC pair entering from `Z < 0`, at the overlap bond `j_1`
(`step` the step `h`, `Yj, zj` the coordinates `Y(u_{j_1}), zeta(u_{j_1} - u_c)`, `a` the PC parameter). -/
def softLamVal (step : ℝ) (j1 : ℤ) (Yj a zj : ℝ) : ℝ :=
  Ewell (-((j1 : ℝ) + 1 / 2)) |Yj / Real.sqrt step| / Eminus a (zj / Real.sqrt step)

/-- **The left soft-edge chart at the upper edge, order `m`, shift index `q`** (see the module docstring). -/
structure SoftEdgeChart {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (P : Set Par) (m q : ℕ)
    (U V : ℝ → ℝ → ℝ) (Lm : ℝ → ℝ) where
  cs : ChainConsts
  N0 : ℕ
  /-- the energy window `|X - X_s^+| <= delta_0`, the collar half-width `eta`, the PC-chart bounds `d_- <= d_zeta/dx <= d_+`, constants. -/
  δ0 : ℝ
  η : ℝ
  dm : ℝ
  dp : ℝ
  Fstar : ℝ
  cF : ℝ
  Csum : ℝ
  cZ : ℝ
  consts_pos : 0 < δ0 ∧ 0 < η ∧ 0 < dm ∧ dm ≤ dp ∧ 0 < Fstar ∧ 0 < cF ∧ 0 ≤ Csum ∧ 0 < cZ
  /-- **(round 2 audit, added)** a bound `Cmu` for the shifts `mu_{2r}`, `r = 1..q/2`, and the margin `cz1` of `zeta_far`. -/
  Cmu : ℝ
  cz1 : ℝ
  consts_pos2 : 0 ≤ Cmu ∧ 0 < cz1
  /-- **(round 4)** the bond bound `CA`, the growth margin `nu1`, the collar lower-bound constant `c3W`, the ratio constant `C2`, the envelope ratio constant `CM` (fields `bondA_le`, `grow_gap`, `collar_lbW`, `ratio2`, `ratioM`). -/
  CA : ℝ
  nu1 : ℝ
  c3W : ℝ
  C2 : ℝ
  CM : ℝ
  consts_pos3 : 0 ≤ CA ∧ 0 < nu1 ∧ 0 < c3W ∧ 0 ≤ C2 ∧ 0 < CM
  /-- the fold `u_c = u_c^+` (the unique maximiser of `f_+`, (H3)). -/
  uc : Par → ℝ
  /-- the coordinate `zeta(x; alpha)` at `(mu, alpha, x)` and the shifts `mu_{2r}(alpha)` at `(r, mu, alpha)` (`muS 0 = mu_0`). -/
  zeta : Par → ℝ → ℝ → ℝ
  muS : ℕ → Par → ℝ → ℝ
  /-- the turning-point-free Weber coordinate `Y_L(u; X)` (eq:tha-YLsoft) on `[0, u_c - eta/2]`. -/
  Y : Par → ℝ → ℝ → ℝ
  /-- **(round 3, F-W2-3)** the Step-1 chain: one Weber patch on `[0, u_c - eta/2]`. -/
  chainW : Par → ℝ → ℕ → LadderData
  /-- the three-patch march of Step 3 (Weber, PC on `Z <= 0`, PC on `Z >= 0`). -/
  chain : Par → ℝ → ℕ → LadderData
  uc_spec : ∀ μ ∈ P, 0 < uc μ ∧ uc μ < F.L ∧ fPlus F.L (F.G 0 μ) (F.B 0 μ) (uc μ) = F.bandHi μ
  /-- **(round 2 audit, added; lem:tha-geom (d))** the collar `[u_c - 2 eta, u_c + 2 eta]` lies in `(0, L)`. -/
  ucη_in : ∀ μ ∈ P, 0 < uc μ - 2 * η ∧ uc μ + 2 * η < F.L
  /-- **(round 2 audit, added; lem:tha-geom (d), the smallness of `delta_0` against `eta`)**: for `|X - X_s^+| <= delta_0`, outside the collar
  `|u - u_c| < eta/4`, `T(.;X) < 0` and `Q_0 = X - B_0 > 0` on `[0, L]`.  The paper obtains `eta` first (so that `X_s^+ - f_+ >= nu` outside `(u_c - eta/4, u_c + eta/4)`)
  and then `delta_0 < nu/2`; the chart constants `(delta_0, eta)` of this structure are such a pair.  Needed for `matchF_soft` (arccosh of an argument `>= 1`),
  the growth bound `psi^L_{n+1} >= (1 + gamma) psi^L_n` (eq:tha-S4grow) and the forbidden margin of lem:tha-collar; without it `PropThaW2`, `PropThaMflat`,
  `PropThaCollar` fail for a chart with `delta_0` large against `eta`. -/
  geom_far : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ u ∈ Set.Icc 0 F.L, η / 4 ≤ |u - uc μ| →
    Tfun F.L (F.G 0 μ) (F.B 0 μ) X u < 0 ∧ 0 < X - F.B 0 μ u
  /-- lem:cha-PCcoord (1): `d_- <= d_x zeta <= d_+` on `|x| <= 2 eta`, `zeta(0;0) = 0`, `|zeta(0;alpha)| <= c_Z |alpha|`. -/
  zeta_deriv : ∀ μ ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, |x| ≤ 2 * η → dm ≤ deriv (zeta μ α) x ∧ deriv (zeta μ α) x ≤ dp
  zeta_zero : ∀ μ ∈ P, zeta μ 0 0 = 0
  zeta_alpha : ∀ μ ∈ P, ∀ α, |α| ≤ δ0 → |zeta μ α 0| ≤ cZ * |α|
  /-- **(round 2 audit, added; lem:cha-PCcoord (2); round 4: also `r = 0`)** the shifts `mu_{2r}`, `0 <= r <= q/2`, are bounded on `|alpha| <= delta_0` (they are `C^{nu_r + 1}` on a compact set; `mu_0 <= C delta_0`
  is used in app_thmA Step 3 for `a h = -tilde mu`); used for `hA = max(mu~, 0)`, `mu~ = mu_0 + O(h^2)` in lem:tha-win (1) and for the bounds `|Z^2/4 + a| h`, `a h <= C` of the overlaps (`SoftTransfer.lean`). -/
  muS_bd : ∀ r ∈ Finset.Icc 0 (q / 2), ∀ μ ∈ P, ∀ α, |α| ≤ δ0 → |muS r μ α| ≤ Cmu
  /-- **(round 2 audit, added; lem:tha-win (1), app_thmA Step 4 (d) (ii))** the turning points `+-2 sqrt(mu_0)` of `zeta` lie inside `|x| < eta/4` with margin:
  `zeta(x;alpha)^2 >= 4 max(mu_0(alpha), 0) + cz1` for `eta/4 <= |x| <= 2 eta`.  This is `delta_0` small (`|zeta(0;alpha)| <= c_Z |alpha|`, `mu_0 <= C |alpha|`,
  `zeta' >= d_-`); it gives `|u_n - u_c| < eta/4` on `|Z_n| <= rho'` and the exponential smallness `E(a, Z_{n_1+1}) <= e^{-c/h}`. -/
  zeta_far : ∀ μ ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, |x| ≤ 2 * η → η / 4 ≤ |x| →
    4 * max (muS 0 μ α) 0 + cz1 ≤ zeta μ α x ^ 2
  /-- **(round 7, F-PW5; lem:cha-PCcoord (1))** the same margin on the rest of the lattice interval, `2 eta <= |x|`, `0 <= u_c + x <= L`.  The paper's `zeta` is defined on all of
  `[x_min, x_max]` with `partial_x zeta > 0` and sends the turning points `+-sqrt(alpha)` to `+-2 sqrt(mu_0)`, so `|zeta|` only grows beyond the collar; the freeze constrained `zeta`
  only on `|x| <= 2 eta`, and a `zeta` vanishing outside the collar made the upper window mass bound of `PropThaWin` (5) false (rows beyond the collar sit in `Omega`).  This field gives
  `|Z_n| > rho(a)` there. -/
  zeta_far_out : ∀ μ ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, 2 * η ≤ |x| → 0 ≤ uc μ + x → uc μ + x ≤ F.L →
    4 * max (muS 0 μ α) 0 + cz1 ≤ zeta μ α x ^ 2
  /-- `mu_0(0) = 0`, `mu_0` is `C^1` with `mu_0'(0) > 0` (so `sgn mu_0 = sgn alpha`), and `pi mu_0(alpha) = S_0(X)` for `alpha >= 0`, `alpha = X_s^+ - X`
  (the physical well action, eq:cha-mu0: `S_0 = pi mu_0` near `X_s^+`). -/
  mu0_zero : ∀ μ ∈ P, muS 0 μ 0 = 0
  mu0_deriv : ∀ μ ∈ P, ContDiff ℝ 1 (muS 0 μ) ∧ 0 < deriv (muS 0 μ) 0
  mu0_S0 : ∀ μ ∈ P, ∀ X, X ≤ F.bandHi μ → F.bandHi μ - X ≤ δ0 →
    Real.pi * muS 0 μ (F.bandHi μ - X) =
      ∫ u in (0 : ℝ)..F.L, Real.arccos ((X - F.B 0 μ u) / (2 * Real.sqrt (E0 F.L (F.G 0 μ) u)))
  /-- (soft Weber coordinate) `Y^2 - 4u >= c_F` on `[0, u_c - eta/2]` and the action identity eq:tha-YLsoft. -/
  Y_forb : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ u ∈ Set.Icc 0 (uc μ - η / 2), 4 * u + cF ≤ Y μ X u ^ 2 ∧ 0 < Y μ X u
  matchF_soft : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ u ∈ Set.Icc 0 (uc μ - η / 2),
    (∫ v in u..(Y μ X u ^ 2 / 4), arccoshR (Y μ X u / (2 * Real.sqrt v)))
      = Fstar + ∫ v in u..(uc μ - η / 2), arccoshR ((X - F.B 0 μ v) / (2 * Real.sqrt (E0 F.L (F.G 0 μ) v)))
  -- Step 1: the Weber chart `chainW` on `[0, u_c - eta/2]` (single patch, hard-edge seed)
  /-- shape of `chainW`: one patch, hard-edge seed, last row `N_W` with `u_{N_W} <= u_c - eta/2 < u_{N_W+1}`. -/
  shapeW : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    (chainW μ X N).P = 1 ∧ (chainW μ X N).s0 = 0 ∧ 0 ≤ (chainW μ X N).NR ∧
      uNode (F.step N) (chainW μ X N).NR ≤ uc μ - η / 2 ∧ uc μ - η / 2 < uNode (F.step N) ((chainW μ X N).NR + 1)
  /-- the engine hypotheses of the Weber chart (`eq:eng-UC1`, (SM1)--(SM3), envelopes; no transfer for `P = 1`). -/
  validW : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → (chainW μ X N).Valid cs (F.step N) m
  A_bondW : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (-1 : ℤ) (chainW μ X N).NR,
    (chainW μ X N).A k = F.bondA μ N k
  Q_diagW : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chainW μ X N).NR,
    (chainW μ X N).Q k = F.diagQ μ N X k
  /-- Weber ladder: `D = sqrt s`, `omega_mod = h^{1/2}`. -/
  dd_sqrtW : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ s h', (chainW μ X N).dd 1 s h' = Real.sqrt s
  omega_sqrtW : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → (chainW μ X N).ω 1 (F.step N) = Real.sqrt (F.step N)
  /-- the model pair of `chainW`: both Weber functions at `Z = h^{-1/2} Y(u_k)`, `a = -(k+1/2)` (cha-weberPC). -/
  wfW_eq : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) ((chainW μ X N).NR + 1),
    (chainW μ X N).wf 1 0 (uNode (F.step N) k) (F.step N) =
      ![ut U (-((k : ℝ) + 1 / 2)) (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)),
        Real.sqrt (F.step N) * (kappaBal (-((k : ℝ) + 1 / 2)) * deriv (U (-((k : ℝ) + 1 / 2)))
          (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)))] ∧
    (chainW μ X N).wf 1 1 (uNode (F.step N) k) (F.step N) =
      ![vt V (-((k : ℝ) + 1 / 2)) (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)),
        Real.sqrt (F.step N) * (Real.sqrt (Real.pi / 2) * (kappaBal (-((k : ℝ) + 1 / 2)))⁻¹
          * deriv (V (-((k : ℝ) + 1 / 2))) (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)))]
  /-- **(F-W2-8)** the modulus sum of the Weber chart: `Theta <= C_sum Lm(h)` (`Lm = 1` for `q >= m`; `Lm = log(1/h)` in the one-shift-short case, the defect weights `rho` being free). -/
  theta_leW : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → (chainW μ X N).theta (F.step N) ≤ Csum * Lm (F.step N)
  /-- the weights of `chainW`: `W_k = E_Web = E_well(-(k+1/2), |Z_k|)`, `M_k = M_Web = M_bal(-(k+1/2), Z_k)` (lem:cha-weber-env). -/
  W_defW : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chainW μ X N).NR,
    (chainW μ X N).W k = Ewell (-((k : ℝ) + 1 / 2)) |Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)|
  M_defW : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chainW μ X N).NR,
    (chainW μ X N).M k = Mbal (-((k : ℝ) + 1 / 2)) (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N))
  /-- `psi-hat_0 > 0` (Weber seed). -/
  seed_posW : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → 0 < (chainW μ X N).phi (F.step N) 0 1 0
  /-- **the first patch of the soft chain is the Weber patch of `chainW`** (the same corrected Weber pair, one corrector row `A^{[m]}, B^{[m]}`; the model pair, ladder and `omega` are fixed by `wfW_eq`,
  `dd_sqrtW`, `omega_sqrtW`). -/
  patch1_eq : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    (chain μ X N).dd 1 = (chainW μ X N).dd 1 ∧ (chain μ X N).pp 1 = (chainW μ X N).pp 1 ∧ (chain μ X N).qq 1 = (chainW μ X N).qq 1 ∧
    (chain μ X N).PiP 1 = (chainW μ X N).PiP 1 ∧ (chain μ X N).PiM 1 = (chainW μ X N).PiM 1 ∧ (chain μ X N).ω 1 = (chainW μ X N).ω 1 ∧
    (chain μ X N).wf 1 = (chainW μ X N).wf 1 ∧ (chain μ X N).AA 1 = (chainW μ X N).AA 1 ∧ (chain μ X N).BB 1 = (chainW μ X N).BB 1
  -- Step 3: the three-patch chain
  /-- the shape of the chain: hard-edge seed, three patches, overlap bond `j_1` with `u_{j_1} <= u_c - eta < u_{j_1+1}` (forbidden for both charts), the switch bond `j_2` with
  `Z_{j_2} <= 0 < Z_{j_2+1}`, last row `N_R` with `u_{N_R} <= u_c + 2 eta < u_{N_R+1}`. -/
  shape : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    (chain μ X N).P = 3 ∧ (chain μ X N).s0 = 0 ∧
      uNode (F.step N) ((chain μ X N).jj 1) ≤ uc μ - η ∧ uc μ - η < uNode (F.step N) ((chain μ X N).jj 1 + 1) ∧
      zeta μ (F.bandHi μ - X) (uNode (F.step N) ((chain μ X N).jj 2) - uc μ) / Real.sqrt (F.step N) ≤ 0 ∧
      0 < zeta μ (F.bandHi μ - X) (uNode (F.step N) ((chain μ X N).jj 2 + 1) - uc μ) / Real.sqrt (F.step N) ∧
      uNode (F.step N) (chain μ X N).NR ≤ uc μ + 2 * η ∧ uc μ + 2 * η < uNode (F.step N) ((chain μ X N).NR + 1)
  /-- **(F-PW4, from the `PropThaWin` attempt)** the switch bond `j_2` and the next row are rows of the lattice, inside the collar: `0 <= j_2`, `j_2 + 1 <= N`, `|u_{j_2} - u_c|, |u_{j_2+1} - u_c| <= 2 eta`
  (the switch `Z = 0` of thm:cha-PC / app_thmA Step 2 is inside the collar; this is what makes the window `Omega = {|Z_n| <= rho}` non-empty). -/
  switch_in : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    0 ≤ (chain μ X N).jj 2 ∧ (chain μ X N).jj 2 + 1 ≤ (N : ℤ) ∧
      |uNode (F.step N) ((chain μ X N).jj 2) - uc μ| ≤ 2 * η ∧ |uNode (F.step N) ((chain μ X N).jj 2 + 1) - uc μ| ≤ 2 * η
  /-- **(round 3, F-W2-1; round 4: `PreValid`)** the engine hypotheses *without (S3)* for the chain with its first pair rescaled by `(lam^{-1}, lam)`, `lam = E_Web(j_1)/E_-(j_1)` (`softLamVal`): the rescaling of
  `engine.tex` after `thm:eng-volterra`; `lam` may be exponentially large or small.  (S3) at `j_1` (forbidden overlap) and at `j_2` (bounded overlap, `M_-(a)`) is **derived** in `TheoremA/SoftTransfer.lean`
  from `bondA_le`, `zeta_*`, `muS_bd`, `Y_forb`, `pcSwap_eq_pcMinus`. -/
  valid : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    ((chain μ X N).rescale1 (softLamVal (F.step N) ((chain μ X N).jj 1) (Y μ X (uNode (F.step N) ((chain μ X N).jj 1)))
      (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X))
      (zeta μ (F.bandHi μ - X) (uNode (F.step N) ((chain μ X N).jj 1) - uc μ)))).PreValid cs (F.step N) m
  A_bond : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (-1 : ℤ) (chain μ X N).NR,
    (chain μ X N).A k = F.bondA μ N k
  Q_diag : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chain μ X N).NR,
    (chain μ X N).Q k = F.diagQ μ N X k
  /-- the PC patches: `D = 1` (interior lattice), `omega_mod = h^{1/2}`; patches 2 and 3 are **one ladder with one corrector row** (the pair changes at `Z = 0`, nothing else). -/
  shared_PC : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    (∀ s h', (chain μ X N).dd 2 s h' = 1) ∧ (chain μ X N).ω 2 (F.step N) = Real.sqrt (F.step N) ∧
    (chain μ X N).dd 3 = (chain μ X N).dd 2 ∧ (chain μ X N).pp 3 = (chain μ X N).pp 2 ∧ (chain μ X N).qq 3 = (chain μ X N).qq 2 ∧
    (chain μ X N).PiP 3 = (chain μ X N).PiP 2 ∧ (chain μ X N).PiM 3 = (chain μ X N).PiM 2 ∧ (chain μ X N).ω 3 = (chain μ X N).ω 2 ∧
    (chain μ X N).AA 3 = (chain μ X N).AA 2 ∧ (chain μ X N).BB 3 = (chain μ X N).BB 2
  /-- patch 2 model pair: the `-` pair of `U, V` at `a = a^{[q]}_PC`, `Z = h^{-1/2} zeta(u_k - u_c; alpha)`, `alpha = X_s^+ - X`, on all rows `j_1 .. N_R + 1` (the comparison sequence
  `psi-hat^{PC,-}` lives on the whole collar). -/
  wf2_eq : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    ∀ k ∈ Finset.Icc ((chain μ X N).jj 1) ((chain μ X N).NR + 1), ∀ α : Fin 2,
    (chain μ X N).wf 2 α (uNode (F.step N) k) (F.step N) =
      ![pcMinus U V (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X)) α
          (zeta μ (F.bandHi μ - X) (uNode (F.step N) k - uc μ) / Real.sqrt (F.step N)),
        Real.sqrt (F.step N) * deriv (pcMinus U V (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X)) α)
          (zeta μ (F.bandHi μ - X) (uNode (F.step N) k - uc μ) / Real.sqrt (F.step N))]
  /-- patch 3 model pair: the swapped pair `pcSwap` (`(v~, -u~)` for `a <= 0`) on the rows `j_2 .. N_R + 1`. -/
  wf3_eq : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    ∀ k ∈ Finset.Icc ((chain μ X N).jj 2) ((chain μ X N).NR + 1), ∀ α : Fin 2,
    (chain μ X N).wf 3 α (uNode (F.step N) k) (F.step N) =
      ![pcSwap U V (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X)) α
          (zeta μ (F.bandHi μ - X) (uNode (F.step N) k - uc μ) / Real.sqrt (F.step N)),
        Real.sqrt (F.step N) * deriv (pcSwap U V (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X)) α)
          (zeta μ (F.bandHi μ - X) (uNode (F.step N) k - uc μ) / Real.sqrt (F.step N))]
  /-- the global weights: patch 1: `W = E_Web / lambda`, `M = M_Web` (`lambda = E_Web(j_1)/E_minus(j_1)`, so the weight is continuous at the overlap);
  patch 2: `W = E_minus(a, Z)`; patch 3: `W = E_swap(a, Z)`; patches 2, 3: `M = M_bal(a,Z)`. -/
  W1_def : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) ((chain μ X N).jj 1),
    (chain μ X N).W k =
      Ewell (-((k : ℝ) + 1 / 2)) |Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)|
        / softLamVal (F.step N) ((chain μ X N).jj 1) (Y μ X (uNode (F.step N) ((chain μ X N).jj 1)))
            (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X))
            (zeta μ (F.bandHi μ - X) (uNode (F.step N) ((chain μ X N).jj 1) - uc μ))
  M1_def : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) ((chain μ X N).jj 1),
    (chain μ X N).M k = Mbal (-((k : ℝ) + 1 / 2)) (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N))
  W2_def : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    ∀ k ∈ Finset.Icc ((chain μ X N).jj 1 + 1) ((chain μ X N).jj 2),
    (chain μ X N).W k = Eminus (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X))
      (zeta μ (F.bandHi μ - X) (uNode (F.step N) k - uc μ) / Real.sqrt (F.step N))
  W3_def : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    ∀ k ∈ Finset.Icc ((chain μ X N).jj 2 + 1) (chain μ X N).NR,
    (chain μ X N).W k = Eswap (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X))
      (zeta μ (F.bandHi μ - X) (uNode (F.step N) k - uc μ) / Real.sqrt (F.step N))
  M2_def : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    ∀ k ∈ Finset.Icc ((chain μ X N).jj 1 + 1) (chain μ X N).NR,
    (chain μ X N).M k = Mbal (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X))
      (zeta μ (F.bandHi μ - X) (uNode (F.step N) k - uc μ) / Real.sqrt (F.step N))
  /-- **(F-W2-8)** the modulus sum is bounded by `C_sum Lm(h)` (the powers of `h` cancel, as in the bulk; `Lm = 1` for `q >= m`, `Lm = log(1/h)` for `q = m - 1`, where the defect
  weights `rho_k` are not identically `1`: app_thmA Step 5 / prop:tha-W2 (4)). -/
  theta_le : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → (chain μ X N).theta (F.step N) ≤ Csum * Lm (F.step N)
  /-- **(F-W2-8)** `1 <= Lm h` on `(0, 1]` (the same hypothesis as in `PropThaW2`; for `Lm = 0` items (1)--(3) are false). -/
  Lm_one : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h
  /-- **(F-W2-8)** `Lm` grows slower than `1/h`: `h Lm(h) -> 0` (true for `Lm = 1` and `Lm = 1 + log(1/h)`); it makes the engine smallness `h^m C_sum Lm(h) <= c_*` hold for small `h`. -/
  Lm_small : ∀ ε : ℝ, 0 < ε → ∃ h1 : ℝ, 0 < h1 ∧ ∀ h : ℝ, 0 < h → h ≤ h1 → h * Lm h ≤ ε
  /-- **(round 4)** the bonds are bounded, `a_n <= C_A` (`a_n = sqrt(s_n (L - s_n) G_h(s_n))`, `G_h` bounded: (E_{q/2}); the paper uses `a_n <= C` throughout, e.g. `A M M ~ omega_*` at a forbidden overlap). -/
  bondA_le : ∀ μ ∈ P, ∀ N, N0 ≤ N → ∀ k : ℤ, F.bondA μ N k ≤ CA
  /-- **(round 4; app_thmA Step 3 (i), eq:tha-S4grow)** the growth margin of the exact solution on the left forbidden side: `X - B_n >= a_n + a_{n-1} + nu_1` for `u_n <= u_c - eta/4`
  (lem:tha-geom (d): `Q_0 - 2 sqrt(E_0) >= nu_1'` there, uniformly by compactness; `|B_n - B_0(u_n)| <= C h^2`, `a_n + a_{n-1} <= 2 sqrt(E_0(u_n)) + C sqrt h`; `h` small is `N >= N_0`). -/
  grow_gap : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ n : ℤ, 0 ≤ n → uNode (F.step N) n ≤ uc μ - η / 4 →
    F.bondA μ N n + F.bondA μ N (n - 1) + nu1 ≤ F.diagQ μ N X n
  /-- **(round 4; lem:cha-W0 for the turning-point-free Weber chart, app_thmA Step 3 (i))** relative lower bound of the Weber comparison sequence on `[0, u_c - eta/2]`: `|psi-hat^{Web}_k| >= c_3 E_Web M_Web`
  (the analogue of `BulkWeberChart.collar_lb`: lem:cha-W0 with the corrector bound `O(h E M)` and `A^{[m]} >= (1/2) min g_0`; the whole range is forbidden since `Y^2 - 4u >= c_F`). -/
  collar_lbW : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chainW μ X N).NR,
    uNode (F.step N) k ≤ uc μ - η / 2 →
      c3W * (chainW μ X N).W k * (chainW μ X N).M k ≤ |(chainW μ X N).phi (F.step N) 0 1 k|
  /-- **(round 4; app_thmA Step 3 (ii))** the forward ratio of the dominant (second) member of the first PC pair across the overlap bond: `|phi^{(2)}_{2,j_1+1}| <= (1 + C_2 h) |phi^{(2)}_{2,j_1}|`
  (`r_2 = e^{-theta}(1 + O(h))`: the explicit function `v~(a,|Z|)` (resp. `U(a,Z)`) decreases as `|Z|` decreases in its Liouville--Green zone, `V_growth`, with the corrector bound `O(h)`; a statement about the
  model comparison member only). -/
  ratio2 : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    |(chain μ X N).phi (F.step N) 1 2 ((chain μ X N).jj 1 + 1)| ≤
      (1 + C2 * F.step N) * |(chain μ X N).phi (F.step N) 1 2 ((chain μ X N).jj 1)|
  /-- **(round 5; app_thmA Step 3 (i), "`M^2_Web ≍ h^{1/2}` there")** the amplitude weight is comparable across the overlap bond: `M_{j_1+1} <= C_M M_{j_1}` (both `M_Web(j_1)` and `M_bal(a, Z_{j_1+1})` are
  `k_2^{-1/4}` with `k_2 ≍ h^{-1}` at the two rows). -/
  ratioM : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    (chain μ X N).M ((chain μ X N).jj 1 + 1) ≤ CM * (chain μ X N).M ((chain μ X N).jj 1)
  /-- **(round 7, F-PW6 of `lem:tha-M`; thmA.tex "the corrector" and `lem:cha-PCcoord`)** the constants `g_- / 2` and `C_B` of the PC corrector rows `A^{[m]}, B^{[m]}` of the collar. -/
  gm : ℝ
  CBc : ℝ
  consts_pos4 : 0 < gm ∧ 0 ≤ CBc
  /-- **(round 7, F-PW6)** on the rows of the PC patches (`|u_k - u_c| <= 2 eta`) the corrector amplitude is bounded below and the corrector `B` above:
  `g_- / 2 <= A^{[m]} = g_0 + O(h^2)` (`g_0 = V_0^{-1/2} >= g_- > 0`; the upper bound `A^{[m]} <= 2 g_+` is `A_bd`) and `|B^{[m]}| <= C_B`.  Neither follows from `cas_lb`, `A_bd`, `B_bd`
  (`Fcas` involves the free ladder data `pp`, `PiM`; `B_bd` is weighted by the free `rho/rho~`); `TheoremA/WindowMass2.lean` (`lem:tha-M`, third conjunct, and the corrector step) needs them. -/
  corr_PC : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k : ℤ, 0 ≤ k → k ≤ (N : ℤ) →
    |uNode (F.step N) k - uc μ| ≤ 2 * η →
      gm ≤ (chain μ X N).AA 2 (uNode (F.step N) k) (F.step N) ∧
        |(chain μ X N).BB 2 (uNode (F.step N) k) (F.step N)| ≤ CBc

namespace SoftEdgeChart

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart F P m q U V Lm)

/-- The PC parameter `a_k = a^{[q]}_PC` at `(mu, X, N)`. -/
def aOf (μ : Par) (X : ℝ) (N : ℕ) : ℝ := aPC (fun r α' => C.muS r μ α') q (F.step N) (F.bandHi μ - X)

/-- The PC coordinate `Z_n = h^{-1/2} zeta(u_n - u_c; alpha)`. -/
def Zof (μ : Par) (X : ℝ) (N : ℕ) (n : ℤ) : ℝ :=
  C.zeta μ (F.bandHi μ - X) (uNode (F.step N) n - C.uc μ) / Real.sqrt (F.step N)

/-- The overlap bond `j_1` (Weber -> PC). -/
def j1 (μ : Par) (X : ℝ) (N : ℕ) : ℤ := (C.chain μ X N).jj 1

/-- The switch bond `j_2` (`Z_{j_2} <= 0 < Z_{j_2+1}`). -/
def j2 (μ : Par) (X : ℝ) (N : ℕ) : ℤ := (C.chain μ X N).jj 2

/-- `lambda_L := W_{j_1}(psi-hat^{L,Web}, psi-hat^{(2)}) / W_{j_1}(psi-hat^{PC,-}, psi-hat^{(2)})` (prop:tha-W2 (1)); `psi-hat^{PC,-} = phi^{(1)}_2 / kappa_bal`
and `psi-hat^{(2)} = phi^{(2)}_2` is the second-branch sequence.  (`cas` is the paper's Casoratian `W` with the same sign.) -/
def lamL (μ : Par) (X : ℝ) (N : ℕ) : ℝ :=
  cas (C.chain μ X N).A ((C.chain μ X N).phi (F.step N) 0 1) ((C.chain μ X N).phi (F.step N) 1 2) (C.j1 μ X N) /
    cas (C.chain μ X N).A (fun n => (C.chain μ X N).phi (F.step N) 0 2 n / kappaBal (C.aOf μ X N))
      ((C.chain μ X N).phi (F.step N) 1 2) (C.j1 μ X N)

/-- The left sequence through the soft edge (the vector `psi-hat^L` of prop:tha-W2 (2)): the Weber comparison sequence of `chainW` on `u_n <= u_c - eta/2`,
`lambda_L psi-hat^{PC,-}` on the collar. -/
def psiHatL (μ : Par) (X : ℝ) (N : ℕ) (n : ℤ) : ℝ :=
  if uNode (F.step N) n ≤ C.uc μ - C.η / 2 then (C.chainW μ X N).phi (F.step N) 0 1 n
  else C.lamL μ X N * ((C.chain μ X N).phi (F.step N) 0 2 n / kappaBal (C.aOf μ X N))

end SoftEdgeChart

/-- **The right chart is the mirror image of the left one** (F-W2-12; the clause `ChartInputs.mirror_up`): `u_c^R = L - u_c`, `zeta_R(-x) = -zeta(x)`, the same shifts `mu_{2r}`, the same `eta`, `delta_0`, `N_0`
(so that `Z_R(N-n) = -Z(n)` and `a_R = a`; the matching `psi-hat^L - kappa psi-hat^R` on `Omega` needs it; the paper uses it silently, "the mirror statement"). -/
def SoftMirror {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
    (CL : SoftEdgeChart F P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily F) P m q U V Lm) : Prop :=
  (∀ p ∈ P, CR.uc p = F.L - CL.uc p) ∧ (∀ p ∈ P, ∀ α x, CR.zeta p α (-x) = -CL.zeta p α x) ∧
    (∀ r, ∀ p ∈ P, ∀ α, CR.muS r p α = CL.muS r p α) ∧ CR.η = CL.η ∧ CR.δ0 = CL.δ0 ∧ CR.N0 = CL.N0

/-! ### The connection matrix `M_-(a)` at the switch `Z = 0` -/

/-- the algebra of `pcSwap_eq_pcMinus` over `R` (`k = kappa_bal`, `G = Gamma(1/2 - a)`, `s, c` the sine and cosine of `pi a`, `r q = 1`). -/
lemma swap_alg (k G s c U V r q : ℝ) (hG : 0 < G) (hkkG : k * k * G = 1) (hs : s ^ 2 + c ^ 2 = 1) (hrq : r * q = 1) :
    r * k⁻¹ * V = r * c * (k * (-s * U + c * G * V)) - s * -(r * k⁻¹ * (c / G * U + s * V)) ∧
    -(k * U) = s * (k * (-s * U + c * G * V)) + q * c * -(r * k⁻¹ * (c / G * U + s * V)) := by
  have hk0 : k * k ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hkkG
    exact zero_ne_one hkkG
  have hk : k ≠ 0 := fun h0 => hk0 (by rw [h0, zero_mul])
  have hG' : G = (k * k)⁻¹ := by
    field_simp
    linarith
  subst hG'
  constructor
  · field_simp
    linear_combination (-(r * V)) * hs
  · field_simp
    linear_combination (k ^ 2 * U) * hs + (k ^ 2 * U * c ^ 2 + s * c * V) * hrq

/-- **The swapped pair is the `-` pair times `M_-(a) S`** (app_thmA Step 2, `lem:cha-PCenv` (1a), eq:cha-Mminus): for `a <= 0`, from the connection formulas of `ParabolicCylinderFacts`,
`pcSwap = (sqrt(pi/2) cos(pi a) y_1 - sin(pi a) y_2, sin(pi a) y_1 + sqrt(2/pi) cos(pi a) y_2)` with `(y_1, y_2) = pcMinus`.  The matrix has determinant `1`
and entries bounded by `1 + sqrt(pi/2) < 2.26`. -/
theorem pcSwap_eq_pcMinus {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) {a : ℝ} (ha : a ≤ 0) (z : ℝ) :
    pcSwap U V a 0 z = Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * a) * pcMinus U V a 0 z - Real.sin (Real.pi * a) * pcMinus U V a 1 z ∧
    pcSwap U V a 1 z = Real.sin (Real.pi * a) * pcMinus U V a 0 z + Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * a) * pcMinus U V a 1 z := by
  have hG : 0 < Real.Gamma (1 / 2 - a) := Real.Gamma_pos_of_pos (by linarith)
  have hkdef : kappaBal a = Real.Gamma (1 / 2 - a) ^ (-(1 : ℝ) / 2) := by
    unfold kappaBal
    simp [ha]
  have hkkG : kappaBal a * kappaBal a * Real.Gamma (1 / 2 - a) = 1 := by
    rw [hkdef, ← Real.rpow_add hG]
    have : -(1 : ℝ) / 2 + -(1 : ℝ) / 2 = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
    exact inv_mul_cancel₀ hG.ne'
  have hs := Real.sin_sq_add_cos_sq (Real.pi * a)
  have hsq1 : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    have : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
    rw [this, Real.sqrt_one]
  simp only [pcSwap, pcMinus, ha, ite_true, ut, vt]
  rw [hf.reflect a ha z, hf.reflect_V a ha z]
  exact swap_alg _ _ _ _ _ _ _ _ hG hkkG hs hsq1

end FormalResearch.JacobiEigenvectors.Charts
