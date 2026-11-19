module

public import Mathlib
public import FormalResearch.JB.JBThmB
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.TheoremB.ComparisonMatrix
public import FormalResearch.JacobiEigenvectors.TheoremB.StdDM
public import FormalResearch.JB.JBFermion

/-!
# Paper J, Layer 3: statement freeze for Theorem B from the chart hypotheses

Source: Paper J `thmB.tex` (prop:tha-splice, lem:tha-Mflat, lem:tha-collar, def:thb-inputs, prop:thb-inputs, thm:B), `app_thmB.tex`
(proof of prop:thb-inputs and of the three splice statements).  Consumer: `FormalResearch.JB` (`OneStepInputs`, `jb_onestep`, `thm_B_conditional`).
Prop-valued definitions only; no placeholder proofs, no added axioms.  (`FormalResearch.JB` will be folded into `TheoremB/` later.)

## Dictionary

| Lean | paper | hypotheses |
|---|---|---|
| `ChartPair` | the two orders `r in {m, m+1}` with the **same** shift `q`, blocks, fold (sec. thb-matrices "Orders, shift, profiles") | -- |
| `TransferBundle` | the inputs (I2) and the changed coefficient (`TransferInputs` of every chart) | Layer 4 |
| `PropThaSpliceBulk`, `PropThaSpliceSoft`, `PropThaSpliceTwoOrders` | prop:tha-splice (a), (b), (c) | `PropThaW`, `PropThaW2` (Layer 2) |
| `PropThaMflat` | lem:tha-Mflat | soft chart |
| `PropThaCollar` | lem:tha-collar (1), bound `C e^{-c/h}` (item (2) is `TransferInputs.t12_lb`/`reg_*`, a chart field) | soft chart |
| `PropThbInputs` | prop:thb-inputs: the conclusion is `JB.OneStepInputs` for the explicit matrices (`compMatrix`) | `ChartPair`, `TransferBundle`, `StdDM F K Kidx` (the consequences of `(D_{q_m+1})` that the proof uses; `stdDM_of_dm`) |
| `ThmB` | thm:B in the form consumed by `JB.jb_onestep` / `thm_B_conditional` | same |
| `CorFermions` | cor:fermions (`JB.FermionConcl` for `hat G_m`) | same as `ThmB` |
| `CorThbDm` | cor:thb-Dm (operator norm under `(D_m)` only, chart pair of `truncFamily F m`, with the fermion part) | `DM F K m`; proof needs cor:thb-stable (F-B6) |
| `etaR` | `eta_m = h^m`, `eta_{m+1} = h^{m+1} log(1/h)` (`m` even) / `h^{m+1}` (`m` odd) | -- |

## FINDINGS

* **F-B1 (def:thb-inputs is incomplete)**, as found in the previous round and kept: (I1)--(I5) must be accompanied by (a) the *host / submatrix structure* (`H_c` is a submatrix of the host `hat G^{[r]}(n_s)`
  of the extreme splices, and `hat G^{[m]} - hat G^{[m+1]}` restricted to a chart is that of `H`), (b) the *parity identity* `eq:thb-parity`, (c) the matching of `hat G` with `H` on the used rows, (d) both orders use the same `q`.
  They hold *by construction* (`compMatrix`, `TransferInputs.parity_*`, `ChartPair`), and appear in `OneStepInputs` (`host*_eq`, `match*`, `parity_*`): `PropThbInputs` asserts that `OneStepInputs` exists with `G0, G1 = compMatrix`.
* **F-B2 (uniformity in `mu`, thm:B)**: `JB.thm_B_conditional` is an existence statement for *one* family of inputs; the paper's constants are uniform in `mu in K`.  `ThmB` quantifies the constants before `mu`;
  the bridge from `PropThbInputs` (constants `cs, C_eps, c_eps` before `mu`) is `jb_onestep cs m` + `small_scalars` (their constants depend only on `cs, m, L, C_eps, c_eps`; `K_eps = 0`), not the conditional theorem as stated (item L3.B).
* **F-B3 (the index range)**: the family of inputs is over `N >= N0` with `h <= t0` (`F.step N <= t0`: the freezing parameter `t = h` must lie in `[-t0, t0]`), cf. the remark in `JBThmB`.
* **F-B4 (prop:tha-splice (c), even `m`)**: the order-`(m+1)` column bound carries `log(1/h)` (the shift `q = m` is one short at order `m+1`); (I1) for the *final* `hat G^{[m+1]}` is stated in `OneStepInputs.G1_col` with `C h^{m+1} log(1/h)` for both parities
  (weaker than `h^{m+1}` for odd `m`, which is all the criterion uses): `PropThaSpliceTwoOrders` states the sharper `etaR`.
* **F-B6 (cor:thb-Dm)**: see `CorThbDm`: needs the perturbation lemma cor:thb-stable; the DM budget `r(2K+1) > r(m)` means it is not an instance of `ThmB` for `F`.
* **F-DD1 (the hypothesis `(D_{q_m+1})` of prop:tha-splice (c), prop:thb-inputs, thm:B; applied)**: the proofs use `(D_{2 Kidx+1})` only through `FrozenReg` (the paper's `(E_Kidx)` of the frozen matrices with budget `r >= r(max(2 Kidx-1, 0))`) and `(D_1)`; these are the premise `StdDM F K Kidx` (`TheoremB/StdDM.lean`) of `PropThaSpliceTwoOrders`, `PropThbInputs` and `ThmB`, which follows from `DM F K (2 Kidx + 1)` (`stdDM_of_dm`, so the statements are the paper's, strengthened) and, for the truncated family `truncFamily F m`, from `DM F K m` (`stdDM_trunc`, `CorThbDm.lean`), whereas `DM (truncFamily F m) K (2 Kidx + 1)` does not follow (`regBudget`).
* **F-B7 (reconciliation with the paper of PR 250, round 4)**.  Changes of the paper since the freeze that touch Layer 3, and what was done:
  (i) lem:tha-collar (1) now has the bound `C e^{-c/h}` *without* `h^{-K}`: `PropThaCollar` has no `Kx`, `PropThbInputs` has no `K_eps` (`I.eps5 <= C_eps e^{-c_eps/h}`; `jb`'s `thm_B_conditional` is applied with `K_eps = 0`);
  (ii) (I5) is now "remaining rows" (`||Q_{0,Sigma}(G^[m] - G^[m+1]) P_Sigma|| <= C h^m`, vacuous for bulk blocks; outside the collar the column *coincides* with `hat Psi`, so the entries are `O(e^{-c/h})` by lem:tha-collar (1)).
  `JB.OneStepInputs.outside` (entries of `G0`, `G1`, `U` outside all used chart rows are `<= eps5`) is *stronger* than the new (I5) and is still discharged by lem:tha-collar (1) (`|Psi_n| + |hat Psi_n| <= C e^{-c/h}` outside the collar), so `OneStepInputs` needs no change;
  (iii) (S1) "blocks, rows of a block in no `I_c` are its remaining rows": the block decomposition is `OneStepInputs.cols/ch/outside`; (iv) (I1) is "columns and reference": `||(G^[m] - U) e_k|| <= C h^m` and the *operator* bound `||G^[m+1] - U|| <= C h^m`;
  the latter follows from the column bounds of `G^[m+1]` (`OneStepInputs.G1_col`: `C h^{m+1} log(1/h)` per column) by the Frobenius estimate, which `jb_onestep` performs (`sqrt D * C h^{m+1} log(1/h) <= 2 C sqrt(L) h^m`), so the Lean input is the paper's *stronger form* and no field changes;
  (v) `K` of the paper's constants is now `K_S` (Schur bound; `OneStepConsts.K`); (vi) the lower soft edge: a column of `Sigma^-` is `D_- = diag((-1)^n)` times the upper-edge column of `-D_- J D_-` (= `negFamily`) at the eigenvalue `-X_k` (`compColumn`), the model pair carries the factor
  `(-1)^n`, so the transfer coefficients are `(-t_11, -t_12)` and the quotients `1/t_12`, `B/(t_12 alpha)` change sign while `alpha`, `t_11/t_12` and all Schur norms are unchanged: `TransferBundle.softLoL/softLoR` (the transfer inputs of the chart of `negFamily` itself) and
  `JB.Chart.Ok` (`|t_12| >= c`, `IsSchurBdd` is invariant under `M -> -M`) therefore need no change, and `eq:thb-parity` is unchanged; (vii) `a = -(k + 1/2) + O(h^m log(1/h))` (the logarithm only for prop:tha-W2 (4)) enters the proof of `PropThaMflat` (flat2) only.
  `OneStepInputs` field `G1_col` has `log(1/h)` for both parities (weaker than the paper for odd `m`, harmless; F-B-eps5).
* **F-B9 (prop:tha-splice (a), (b): `1 <= m`, coupling of the two charts; applied, same pattern as `PropThaW` / `PropThaW2`)**.  The bulk statement relied silently on `m >= 1` (the engine smallness `h^m Theta <= c_*` is unavailable for `m = 0`) and on the
  mirror overlap `CR.c = L - CL.c'`, `CR.c' = L - CL.c` (the two charts are independent data, but the glue `bulkKappa`, `bulkNorm`, `bulkVec` needs the right sequence on all rows `u_n > c`, and the window of `CL` must be the mirror image of that of `CR`).
  Both are now the first premises of `PropThaSpliceBulk` (the relation is the one `ChartInputs.overlap_match` provides).  Verified against the paper: prop:tha-splice (a) is stated "in the setting of Proposition prop:tha-W", whose hypotheses are `r >= 1` and
  the two edge charts being the left and the mirrored right chart of one block; confirmed, no refinement.  `PropThaSpliceSoft` has the same two gaps (`m >= 1`; the right soft chart must be the mirror image of the left, `SoftMirror CL CR`, the
  `ChartInputs.mirror_up` clause, as in F-W2-12) and got the same premises `1 <= m -> SoftMirror CL CR`; the Step-0 premise of `PropThaW2` is not needed in the statement since `a <= 1` is a hypothesis of (b) and `StepZero` is proved.
* **F-B10 (prop:tha-splice (c): the splices must lie in the window; applied)**.  `PropThaSpliceTwoOrders` was stated for an arbitrary `spl : Fin nb -> R`, but the column error `<= C eta_r` is false for a splice outside the overlap
  (the paper says "uniformly in the splice `n_nu in [n_nu^-, n_nu^+]`", and the order-`(m+1)` clause needs the splice in the window of the order-`(m+1)` chart).  New premise `ChartPair.SplicesInWindow CP spl`: `spl nu` lies in the open overlap `(c', c)` of
  `CI0.bulkL nu` and (via `spl1`) of `CI1.bulkL nu`.  **Refinement of the paper**: strict inequalities, since the splice row is `nearestRow h (spl nu)` and for `spl nu = c'` the row can lie half a step outside the window `{c' <= u_n <= c}`.  `ThmB`, `PropThbInputs`, `CorThbDm`
  take the same `spl` and need the same premise (not yet changed: their proofs go through `PropThaSpliceTwoOrders`, L3.5c).
* **F-B5 (lem:tha-Mflat, `delta_0` small; applied, round 10)**: "choose `delta_0` so small" is a constraint on the chart constants, now the chart field `SoftEdgeChart.delta0_small` (`2 cZ^2 Cmu0 delta_0 <= cmu0^2`); the statement is for the given chart and `a <= 1`, which covers every eigenvalue (Step 0).
* **F-B14 (lem:tha-Mflat: `1 <= m`, `SoftMirror`, `ParabolicCylinderFacts`; applied, round 10)** and **F-B15 (lem:tha-collar (1): same three premises; applied)**: flat2 and the collar estimate are about `softVec CL CR` (the mirror chart) and use the engine smallness `h^m Theta <= c_*` and the Olver
  envelopes of `U, V`; they are false for `m = 0`, for an unrelated `CR`, or for arbitrary `U, V`.  `PropThaMflat`, `PropThaCollar` (and `PropThaSpliceSoft`, which had `1 <= m`, `SoftMirror` already) now start `ParabolicCylinderFacts U V cPC CPC -> 1 <= m -> SoftMirror CL CR ->`, as `PropThaW2`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix

variable {Par : Type*} [TopologicalSpace Par]

/-- `eta_m = h^m` and `eta_{m+1} = h^{m+1} log(1/h)` for even `m` (`h^{m+1}` for odd `m`): the column accuracy of orders `m` and `m+1` with the common shift `q_m`. -/
def etaR (m r : ℕ) (h : ℝ) : ℝ :=
  if r = m then h ^ m else if m % 2 = 0 then h ^ (m + 1) * Real.log (1 / h) else h ^ (m + 1)

/-- The vector of `prop:tha-splice`: `psi-hat^L / hat N(n_s)` for `n <= n_s`, `hat kappa psi-hat^R / hat N(n_s)` beyond. -/
def splicedVec (ψL ψR : ℤ → ℝ) (Ω rows : Finset ℤ) (ns n : ℤ) : ℝ :=
  (if n ≤ ns then ψL n else glueKappa ψL ψR Ω * ψR n) / glueNormAt ψL ψR Ω rows ns

/-! ### prop:tha-splice -/

/-- **prop:tha-splice (a)** (bulk), error function `eta` in place of `h^r`.  **Corrected in the second pass (finding F-B8, same pattern as F-C3 of `PropThaW`)**: the matching relation `psi^L = kappa psi^R`
holds *at an eigenvalue*, so the glue-norm clause and the window-matching clause are stated inside the eigen-system clause (as in the paper's proof, which works "at the eigenvalue `X`"); off the spectrum, in a gap between quantisation levels, they fail.  Same for (b). Statement: for every splice `n_s` in the window, `|hat N(n_s)/hat N - 1| <= C eta`, `|psi-hat^L - hat kappa psi-hat^R| <= C eta M_Web` on the window,
`|Psi_n - hat Psi^{(n_s)}_n| <= C eta V_n / hat N` for all `n`, with `C` independent of `n_s`. -/
def PropThaSpliceBulk {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V) (η : ℝ → ℝ) : Prop :=
  1 ≤ m → (CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) →
  ∀ r, StdAssump Fz P (m / 2) r →
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 →
      ∀ ns ∈ bulkWindow CL N,
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
          ∀ k : Fin (N + 1), Xs k = X →
            (|glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns / bulkNorm CL CR p X N - 1| ≤ C * η (Fz.step N) ∧
              (∀ n ∈ bulkWindow CL N, |CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n| ≤ C * η (Fz.step N) * (CL.chain p X N).M n)) ∧
            ∀ n ∈ rowsOf N,
              |eigVec Um k n - splicedVec (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns n|
                ≤ C * η (Fz.step N) * bulkEnv CL CR p X N n

/-- **prop:tha-splice (b)** (soft edge): the same for every `n_s` in the window `Omega`, and the fold row `n_c = nearestRow u_c` is an admissible splice for every column of the edge. -/
def PropThaSpliceSoft {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1)) (η : ℝ → ℝ) (cPC CPC : ℝ) : Prop :=
  ParabolicCylinderFacts U V cPC CPC → 1 ≤ m → SoftMirror CL CR →
  ∀ r, StdAssump Fz P (q / 2) r →
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 → CL.aOf p X N ≤ 1 →
      nearestRow (Fz.step N) (CL.uc p) ∈ softWindow CL p X N ∧
      ∀ ns ∈ softWindow CL p X N,
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
          ∀ k : Fin (N + 1), Xs k = X →
            (|glueNormAt (CL.psiHatL p X N) (softSeqR CR p X N) (softWindow CL p X N) (rowsOf N) ns / softNorm CL CR p X N - 1| ≤ C * η (Fz.step N) ∧
              (∀ n ∈ softWindow CL p X N, |CL.psiHatL p X N n - softKappa CL CR p X N * softSeqR CR p X N n|
                ≤ C * η (Fz.step N) * |CL.lamL p X N| * (kappaBal (CL.aOf p X N))⁻¹ * Mbal (CL.aOf p X N) (CL.Zof p X N n))) ∧
            ∀ n ∈ rowsOf N,
              |eigVec Um k n - splicedVec (CL.psiHatL p X N) (softSeqR CR p X N) (softWindow CL p X N) (rowsOf N) ns n|
                ≤ C * η (Fz.step N) * softEnv CL CR p X N n

/-- Two chart bundles at orders `m` and `m+1` with the same shift `q`, the same blocks and the same soft data (the correctors and the coordinate do not depend on the order). -/
structure ChartPair {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ} where
  CI0 : ChartInputs F K Kidx t0 m q U V cPC CPC
  CI1 : ChartInputs F K Kidx t0 (m + 1) q U V cPC CPC
  nb_eq : CI1.nb = CI0.nb
  lo_eq : ∀ ν, CI1.lo ν = CI0.lo (Fin.cast nb_eq ν)
  hi_eq : ∀ ν, CI1.hi ν = CI0.hi (Fin.cast nb_eq ν)
  J_eq : CI1.Jlo = CI0.Jlo ∧ CI1.Jhi = CI0.Jhi
  soft_up_eq : CI1.softUpL.uc = CI0.softUpL.uc ∧ CI1.softUpL.δ0 = CI0.softUpL.δ0 ∧ CI1.softUpL.η = CI0.softUpL.η ∧
    CI1.softUpL.zeta = CI0.softUpL.zeta ∧ CI1.softUpL.muS = CI0.softUpL.muS
  soft_lo_eq : CI1.softLoL.uc = CI0.softLoL.uc ∧ CI1.softLoL.δ0 = CI0.softLoL.δ0 ∧ CI1.softLoL.η = CI0.softLoL.η ∧
    CI1.softLoL.zeta = CI0.softLoL.zeta ∧ CI1.softLoL.muS = CI0.softLoL.muS

/-- Splice positions of the order-`m` bundle transported to the order-`(m+1)` bundle (the same fixed splices for both orders). -/
def ChartPair.spl1 {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) : Fin CP.CI1.nb → ℝ := fun ν => spl (Fin.cast CP.nb_eq ν)

/-- **The splices lie in the bulk overlap of both orders** (finding F-B10): for every block `nu` the fixed splice position `spl nu` lies in the open overlap `(c', c)` of the block's bulk chart,
at order `m` (`CI0`) and, transported by `spl1`, at order `m + 1` (`CI1`).  Strict inequalities, because the splice row is `nearestRow h (spl nu)`, which lies within `h/2` of `spl nu`: for `spl nu = c'` the row can lie outside the
window `{c' <= u_n <= c}` of `PropThaSpliceBulk`, and then the splice is not controlled. -/
def ChartPair.SplicesInWindow {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  (∀ ν, (CP.CI0.bulkL ν).c' < spl ν ∧ spl ν < (CP.CI0.bulkL ν).c) ∧
  (∀ ν, (CP.CI1.bulkL ν).c' < CP.spl1 spl ν ∧ CP.spl1 spl ν < (CP.CI1.bulkL ν).c)

section Splice2

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **prop:tha-splice (c)** (two orders, one shift) in matrix form: with the same `q = 2 ceil(m/2)`, for every spectrum and every column `j`,
`||(hat G^{[m]} - U) e_j||_2 <= C eta_m` and `||(hat G^{[m+1]} - U) e_j||_2 <= C eta_{m+1}` (the splices of `hat G` are the fixed ones `spl`).
**Corrected (finding F-B10, applied)**: the paper's constants are "uniformly in the splice `n_nu in [n^-_nu, n^+_nu]`", so the splice positions must lie in the bulk overlap of both orders (`ChartPair.SplicesInWindow`, a premise: for a
splice outside the window the column is not close to the eigenvector).  (`ThmB`, `PropThbInputs`, `CorThbDm` take the same `spl` and now carry the same premise `CP.SplicesInWindow spl`: F-B10 applied to them as well.) -/
def PropThaSpliceTwoOrders (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  1 ≤ m → Kidx = (m + 1) / 2 → q = 2 * Kidx → IsCompact K → HypOn F K → StdDM F K Kidx → CP.SplicesInWindow spl →
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ j : Fin (N + 1),
          FormalResearch.JB.jbL2 Finset.univ (fun i => compMatrix CP.CI0 spl μ N Xs i j - Um i j) ≤ C * etaR m m (F.step N) ∧
          FormalResearch.JB.jbL2 Finset.univ (fun i => compMatrix CP.CI1 (CP.spl1 spl) μ N Xs i j - Um i j) ≤ C * etaR m (m + 1) (F.step N)

end Splice2

/-! ### lem:tha-Mflat and lem:tha-collar -/

/-- **lem:tha-Mflat** (statement): with `n_c = nearestRow u_c` and `Omega_- = Omega cap {n <= n_c}`, `Omega_+ = Omega cap {n > n_c}`, for `a <= 1`:
(flat0) `|Z_{n_c}| <= sqrt(max(-a,0)) + C sqrt h`; (flat1) each half carries a fixed fraction of the window mass, for `U(a,-Z)` on `Omega_-`, `U(a,Z)` on `Omega_+` and for the corrected sequences;
(flat2) at an eigenvalue of index `k`, `|hat Psi_{n_c}|^2 + |hat Psi_{n_c+1}|^2 <= C sqrt h (1+k)^{-1/2}`. -/
def PropThaMflat {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1)) (cPC CPC : ℝ) : Prop :=
  ParabolicCylinderFacts U V cPC CPC → 1 ≤ m → SoftMirror CL CR →
  ∀ r, StdAssump Fz P (q / 2) r →
    ∃ c C h0 : ℝ, 0 < c ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 → CL.aOf p X N ≤ 1 →
      |CL.Zof p X N (nearestRow (Fz.step N) (CL.uc p))| ≤ Real.sqrt (max (-CL.aOf p X N) 0) + C * Real.sqrt (Fz.step N) ∧
      c * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * ∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2
          ≤ ∑ n ∈ (softWindow CL p X N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)), U (CL.aOf p X N) (-(CL.Zof p X N n)) ^ 2 ∧
      c * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * ∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2
          ≤ ∑ n ∈ (softWindow CL p X N).filter (fun n => nearestRow (Fz.step N) (CL.uc p) < n), U (CL.aOf p X N) (CL.Zof p X N n) ^ 2 ∧
      c * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * ∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2
          ≤ ∑ n ∈ (softWindow CL p X N).filter (fun n => n ≤ nearestRow (Fz.step N) (CL.uc p)),
              ((CL.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (CL.aOf p X N)) ^ 2 ∧
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), Xs k = X →
          softVec CL CR p X N (nearestRow (Fz.step N) (CL.uc p)) ^ 2 + softVec CL CR p X N (nearestRow (Fz.step N) (CL.uc p) + 1) ^ 2
            ≤ C * Real.sqrt (Fz.step N) * (1 + ((k : ℕ) : ℝ)) ^ (-(1 : ℝ) / 2)

/-- **lem:tha-collar (1)** (statement): outside the collar `|u_n - u_c| < eta/2`, `|Psi_n| + |hat Psi_n| <= C e^{-c/h}` (**no power `h^{-K}`**: the paper's current form; the earlier freeze carried `h^{-K}`);
and the normalised matching-weighted recessive PC profile and its scaled derivative at the exterior neighbours `n_1` (the last row with `u <= u_c - eta/2`, i.e. the last row below the collar)
and `n_4` (the first row with `u >= u_c + eta/2`, the first row above it) obey the same bound, with fixed `c, C > 0`, uniformly in the eigenvalue and its index.  The lower soft edge is the statement for the
chart of `negFamily` (the factor `D_- = diag((-1)^n)` does not change moduli).  (Item (2) of the paper is `TransferInputs.t12_lb` and `reg_*` of the soft charts.) -/
def PropThaCollar {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1)) (cPC CPC : ℝ) : Prop :=
  ParabolicCylinderFacts U V cPC CPC → 1 ≤ m → SoftMirror CL CR →
  ∀ r, StdAssump Fz P (q / 2) r →
    ∃ C c h0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 → CL.aOf p X N ≤ 1 →
      (∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), Xs k = X → ∀ n ∈ rowsOf N, CL.η / 2 ≤ |uNode (Fz.step N) n - CL.uc p| →
          |eigVec Um k n| + |softVec CL CR p X N n| ≤ C * Real.exp (-c / Fz.step N)) ∧
      (|CL.lamL p X N| / softNorm CL CR p X N *
          |(CL.chain p X N).phi (Fz.step N) 0 2 ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋ / kappaBal (CL.aOf p X N)|
          ≤ C * Real.exp (-c / Fz.step N)) ∧
      (|CL.lamL p X N| / softNorm CL CR p X N *
          |(CL.chain p X N).wf 2 0 (uNode (Fz.step N) ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋) (Fz.step N) 1| / kappaBal (CL.aOf p X N)
          ≤ C * Real.exp (-c / Fz.step N)) ∧
      (|softKappa CL CR p X N * CR.lamL p X N| / softNorm CL CR p X N *
          |(CR.chain p X N).phi (Fz.step N) 0 2 ((N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉) / kappaBal (CL.aOf p X N)|
          ≤ C * Real.exp (-c / Fz.step N))

/-! ### The transfer inputs of all charts, and prop:thb-inputs -/

section Inputs

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- The transfer inputs (I2) of **every** chart of `hat G^{[m]}, hat G^{[m+1]}`: the left and right Weber charts of each bulk block (patch 1; the exact transfer is `Pi_+` of the Weber ladder, `omega_n = sqrt(s_n)`),
and the left and right PC halves of each soft edge (patch 2 of the soft chain on the collar, `omega = 1`; the right half is the left half of the mirror family).  Layer 4: `lem:smo-budget`, `lem:cha-weber-coord`, `lem:cha-PCcoord`, `lem:tha-collar` (2).
**Corrected (finding F-B16, applied)**: the soft halves have direction `tau = -1` (left, exterior row `n_L - 1`) and `+1` (right, exterior row `n_R + 1`), both in the forbidden region (`thmB.tex`, table of charts), i.e. they step *down* in the index of the chain of the half;
their transfer data are those of `Pi_-` (`TransferInputsDn`), not of `Pi_+` (`TransferInputs`, which describes an upward chart with its exterior row at the edge, where `y_ext` is not exponentially small and (I3) fails).  The bulk fields stay `TransferInputs`. -/
structure TransferBundle (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC)) where
  bulkL : ∀ ν, TransferInputs (frozenFamily F Kidx) (paramSet K t0) (fun _ => CP.CI0.lo ν) (fun _ => CP.CI0.hi ν) m
    (CP.CI0.bulkL ν).chain ((CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν))).chain 1
    (fun _ => 0) (fun _ => (CP.CI0.bulkL ν).c + (CP.CI0.bulkL ν).σ / 2)
  bulkR : ∀ ν, TransferInputs (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) (fun _ => CP.CI0.lo ν) (fun _ => CP.CI0.hi ν) m
    (CP.CI0.bulkR ν).chain ((CP.CI1.bulkR (Fin.cast CP.nb_eq.symm ν))).chain 1
    (fun _ => 0) (fun _ => (CP.CI0.bulkR ν).c + (CP.CI0.bulkR ν).σ / 2)
  softUpL : TransferInputsDn (frozenFamily F Kidx) (paramSet K t0) (fun p => (frozenFamily F Kidx).bandHi p - CP.CI0.softUpL.δ0)
    (fun p => (frozenFamily F Kidx).bandHi p + CP.CI0.softUpL.δ0) m CP.CI0.softUpL.chain CP.CI1.softUpL.chain 2
    (fun p => CP.CI0.softUpL.uc p - CP.CI0.softUpL.η / 2) (fun p => CP.CI0.softUpL.uc p + CP.CI0.softUpL.η / 2)
  softUpR : TransferInputsDn (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) (fun p => (frozenFamily F Kidx).bandHi p - CP.CI0.softUpL.δ0)
    (fun p => (frozenFamily F Kidx).bandHi p + CP.CI0.softUpL.δ0) m CP.CI0.softUpR.chain CP.CI1.softUpR.chain 2
    (fun p => CP.CI0.softUpR.uc p - CP.CI0.softUpR.η / 2) (fun p => CP.CI0.softUpR.uc p + CP.CI0.softUpR.η / 2)
  softLoL : TransferInputsDn (negFamily (frozenFamily F Kidx)) (paramSet K t0) (fun p => (negFamily (frozenFamily F Kidx)).bandHi p - CP.CI0.softLoL.δ0)
    (fun p => (negFamily (frozenFamily F Kidx)).bandHi p + CP.CI0.softLoL.δ0) m CP.CI0.softLoL.chain CP.CI1.softLoL.chain 2
    (fun p => CP.CI0.softLoL.uc p - CP.CI0.softLoL.η / 2) (fun p => CP.CI0.softLoL.uc p + CP.CI0.softLoL.η / 2)
  softLoR : TransferInputsDn (mirrorFamily (negFamily (frozenFamily F Kidx))) (paramSet K t0) (fun p => (negFamily (frozenFamily F Kidx)).bandHi p - CP.CI0.softLoL.δ0)
    (fun p => (negFamily (frozenFamily F Kidx)).bandHi p + CP.CI0.softLoL.δ0) m CP.CI0.softLoR.chain CP.CI1.softLoR.chain 2
    (fun p => CP.CI0.softLoR.uc p - CP.CI0.softLoR.η / 2) (fun p => CP.CI0.softLoR.uc p + CP.CI0.softLoR.η / 2)

/-- **prop:thb-inputs** (statement, the Layer-3 target): under `(D_{q_m+1})` and (H1)--(H3), with the charts and transfer inputs, there are constants `cs` (number of blocks and `C, K, omega_max, c_T, c_alpha, c_0, C_4, C_E`),
`N_0, C_eps, c_eps` such that, for every `mu in K`, `N >= N_0` (with `h <= t0`) and every eigen-system `(X, U)` of `J_h`, there is a `JB.OneStepInputs cs (N+1) m h` whose `U` is `U`, whose `G0, G1` are the explicit
`hat G^{[m]}, hat G^{[m+1]}` (`compMatrix`, fixed splices `spl`), and whose exterior bound `eps5` satisfies `eps5 <= C_eps e^{-c_eps/h}` (no power of `h`, as lem:tha-collar (1) in the current paper).  All of (I1)--(I5), the host/submatrix structure (F3 (a), (d)), the
parity identity (F3 (b)) and the matching on the used rows are fields of `OneStepInputs`.  The constants are fixed before `mu` (F-B2). -/
def PropThbInputs (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (_TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  1 ≤ m → Kidx = (m + 1) / 2 → q = 2 * Kidx → IsCompact K → HypOn F K → StdDM F K Kidx → CP.SplicesInWindow spl →
    ∃ (cs : FormalResearch.JB.OneStepConsts) (N0 : ℕ) (Cε cε : ℝ), 0 < cε ∧ ∀ μ ∈ K, ∀ N : ℕ, N0 ≤ N → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∃ I : FormalResearch.JB.OneStepInputs cs (N + 1) m (F.step N),
          I.U = Um ∧ I.G0 = compMatrix CP.CI0 spl μ N Xs ∧ I.G1 = compMatrix CP.CI1 (CP.spl1 spl) μ N Xs ∧
          I.ε5 ≤ Cε * Real.exp (-cε / F.step N)

/-- **Theorem B** (statement, the form consumed by `JB.jb_onestep` / `thm_B_conditional`): there are `C` and `h_m` with `C h_m^m < 1` such that for `h <= h_m`, all `mu in K` and every eigen-system,
`||hat G_m - U_h|| <= C h^m`, and the polar factor of `hat G_m` is orthogonal and within `2 C h^m` of `U_h`.  `hat G_m` is `compMatrix` for the order-`m` bundle. -/
def ThmB (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  1 ≤ m → Kidx = (m + 1) / 2 → q = 2 * Kidx → IsCompact K → HypOn F K → StdDM F K Kidx → CP.SplicesInWindow spl →
    ∃ C hm : ℝ, 0 < hm ∧ C * hm ^ m < 1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ‖compMatrix CP.CI0 spl μ N Xs - Um‖ ≤ C * F.step N ^ m ∧
        (compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹)ᵀ *
            (compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹) = 1 ∧
        ‖compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹ - Um‖
          ≤ 2 * C * F.step N ^ m

/-- **cor:fermions** (statement; main_results.tex, proof in thmB.tex, "Free-fermion correlation matrices"): under the hypotheses of `ThmB` there are `C, h_m` with `C h_m^m < 1` such that for `h <= h_m`, `mu in K` and every eigen-system `(X, U)` of `J_h`,
`JB.FermionConcl hat G_m U (C h^m)`: for every `F` with `||F|| <= 1` and every orthogonal projection `P`, `||P (hat G_m F hat G_m^T - U F U^T) P|| <= 3 C h^m` (`4 C h^m` for the polar factor `tilde U_m`), the `k`-th eigenvalues of the
compressions to the range of `P` of `U F U^T`, `hat G_m F hat G_m^T` differ by at most `3 C h^m`, and the entanglement energies by at most `8 C h^m / tau` (`6 C h^m <= tau <= 1/2`, `nu_k in [tau, 1 - tau]`).  Real matrices only (`JBFermion.lean`). -/
def CorFermions (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  1 ≤ m → Kidx = (m + 1) / 2 → q = 2 * Kidx → IsCompact K → HypOn F K → StdDM F K Kidx → CP.SplicesInWindow spl →
    ∃ C hm : ℝ, 0 < hm ∧ C * hm ^ m < 1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        FormalResearch.JB.FermionConcl (compMatrix CP.CI0 spl μ N Xs) Um (C * F.step N ^ m)

/-- **cor:thb-Dm** (statement; thmB.tex, "Stability under perturbation", on `origin/agents/m7-m1-global-racah`): under (H1)--(H3) and **only** `(D_m)`, `m >= 1`, let `CP` be the chart pair of the *truncated* family
`truncFamily F m` (`tilde J_h` of eq:l2-tilde; `G_j = B_j := 0` for `m < j <= q_m + 1`), frozen at `Kidx = ceil(m/2)`, `q = 2 Kidx`.  Then there are `C, h_m` with `C h_m^m < 1` such that for `h <= h_m`, `mu in K` and every
pair of eigen-systems `(tilde X, tilde U)` of `tilde J_h` and `(X, U)` of `J_h`: `||compMatrix CP.CI0 spl mu N tilde X - U|| <= C h^m` (so `hat G^{jet}_m` is built from `tilde X`, the eigenvalues of the truncated matrix, and no eigenvector),
the polar factor of `hat G^{jet}_m` is orthogonal and within `2 C h^m` of `U`, and Corollary cor:fermions holds with `hat G^{jet}_m` and its polar factor in place of `hat G_m` and `tilde U_m`: `JB.FermionConcl hat G^{jet}_m U (C h^m)`
(`JBFermion.lean`: the compression bounds `3 C h^m` and `4 C h^m`, the eigenvalue comparison `3 C h^m` and the entanglement energies `8 C h^m / tau`; it follows from the two bounds alone, `JB.jb_fermions`).

**Proof route** (`corThbDm_of_thmB`, `corThbDm_proved`, `TheoremB/CorThbDm.lean`, `CorThbFinal.lean`).  `tilde J_h` satisfies `(E_Kidx)` with no remainder and (H1)--(H3), so `ThmB` / `PropThbInputs` for `truncFamily F m` give
`||hat G^{jet}_m - tilde U|| <= C h^m`; `tilde J_h` satisfies `(D_1)` and (H1)--(H3), so its gaps are `>= c h` (`CorEigenGap1`); `||J_h - tilde J_h|| <= C' h^{m+1}` (`DM F K m`); and the Fourier--Schur argument of cor:thb-stable
(`ThbStable.lean`) gives `||U - tilde U|| <= C_* C' h^m` in the gauge `(Psi_k)_0 > 0`.  Polar: lemma `lem:thb-polar` (`JB`).

**Differences from the paper**: the paper states the hypotheses (H1)--(H3), (D_m) for `F` and builds `hat G^{jet}_m` from the truncated matrix; the Lean statement takes the chart pair of `truncFamily F m` as data (`CP`).  `ThmB` for `truncFamily F m`
needs `StdDM (truncFamily F m) K Kidx` (finding F-DD1), which follows from `DM F K m` (`stdDM_trunc`) although `DM (truncFamily F m) K (2 Kidx + 1)` does not (the truncated jets vanish beyond `m` and keep the regularity `r(m)` of `F`, less than the
`r(2 Kidx + 1)` of `DM` at order `2 Kidx + 1`).  **Finding F-B6**: `cor:thb-Dm` is **not** an instance of `ThmB`
applied to `truncFamily F m` alone, because the conclusion compares with the eigenvectors of `J_h`, not of `tilde J_h`; it needs cor:thb-stable (perturbation of the matrix, at the level of `U`), which is also what gives
`ThmB` for matrices within `O(h^{m+1})`.  **Finding F-t0**: `t0` is chart data; the passage to the truncated chart needs a `ChartInputs.restrict` step.  The fermion part is the last conjunct (`JB.FermionConcl`, whose restrictions to real `F`, `P` are listed in `JBFermion.lean`). -/
def CorThbDm {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CP : ChartPair (F := truncFamily F m) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  1 ≤ m → Kidx = (m + 1) / 2 → q = 2 * Kidx → IsCompact K → HypOn F K → DM F K m → CP.SplicesInWindow spl →
    ∃ C hm : ℝ, 0 < hm ∧ C * hm ^ m < 1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (Xt : Fin (N + 1) → ℝ) (Ut : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem ((truncFamily F m).jacobiMat μ N) Xt Ut →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ‖compMatrix CP.CI0 spl μ N Xt - Um‖ ≤ C * F.step N ^ m ∧
        (compMatrix CP.CI0 spl μ N Xt * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xt)ᵀ * compMatrix CP.CI0 spl μ N Xt))⁻¹)ᵀ *
            (compMatrix CP.CI0 spl μ N Xt * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xt)ᵀ * compMatrix CP.CI0 spl μ N Xt))⁻¹) = 1 ∧
        ‖compMatrix CP.CI0 spl μ N Xt * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xt)ᵀ * compMatrix CP.CI0 spl μ N Xt))⁻¹ - Um‖
          ≤ 2 * C * F.step N ^ m ∧
        FormalResearch.JB.FermionConcl (compMatrix CP.CI0 spl μ N Xt) Um (C * F.step N ^ m)

end Inputs

end FormalResearch.JacobiEigenvectors.TheoremB
