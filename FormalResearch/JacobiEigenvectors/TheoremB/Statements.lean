module

public import Mathlib
public import FormalResearch.JB.JBThmB
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.TheoremB.ComparisonMatrix

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
| `PropThaCollar` | lem:tha-collar (1) (item (2) is `TransferInputs.t12_lb`/`reg_*`, a chart field) | soft chart |
| `PropThbInputs` | prop:thb-inputs: the conclusion is `JB.OneStepInputs` for the explicit matrices (`compMatrix`) | `ChartPair`, `TransferBundle`, `DM F K (q_m+1)` |
| `ThmB` | thm:B in the form consumed by `JB.jb_onestep` / `thm_B_conditional` | same |
| `etaR` | `eta_m = h^m`, `eta_{m+1} = h^{m+1} log(1/h)` (`m` even) / `h^{m+1}` (`m` odd) | -- |

## FINDINGS

* **F-B1 (def:thb-inputs is incomplete)**, as found in the previous round and kept: (I1)--(I5) must be accompanied by (a) the *host / submatrix structure* (`H_c` is a submatrix of the host `hat G^{[r]}(n_s)`
  of the extreme splices, and `hat G^{[m]} - hat G^{[m+1]}` restricted to a chart is that of `H`), (b) the *parity identity* `eq:thb-parity`, (c) the matching of `hat G` with `H` on the used rows, (d) both orders use the same `q`.
  They hold *by construction* (`compMatrix`, `TransferInputs.parity_*`, `ChartPair`), and appear in `OneStepInputs` (`host*_eq`, `match*`, `parity_*`): `PropThbInputs` asserts that `OneStepInputs` exists with `G0, G1 = compMatrix`.
* **F-B2 (uniformity in `mu`, thm:B)**: `JB.thm_B_conditional` is an existence statement for *one* family of inputs; the paper's constants are uniform in `mu in K`.  `ThmB` quantifies the constants before `mu`;
  the bridge from `PropThbInputs` (constants `cs, C_eps, c_eps, K_eps` before `mu`) is `jb_onestep cs m` + `small_scalars` (their constants depend only on `cs, m, L, C_eps, c_eps, K_eps`), not the conditional theorem as stated (item L3.B).
* **F-B3 (the index range)**: the family of inputs is over `N >= N0` with `h <= t0` (`F.step N <= t0`: the freezing parameter `t = h` must lie in `[-t0, t0]`), cf. the remark in `JBThmB`.
* **F-B4 (prop:tha-splice (c), even `m`)**: the order-`(m+1)` column bound carries `log(1/h)` (the shift `q = m` is one short at order `m+1`); (I1) for the *final* `hat G^{[m+1]}` is stated in `OneStepInputs.G1_col` with `C h^{m+1} log(1/h)` for both parities
  (weaker than `h^{m+1}` for odd `m`, which is all the criterion uses): `PropThaSpliceTwoOrders` states the sharper `etaR`.
* **F-B5 (lem:tha-Mflat, `delta_0` small)**: "choose `delta_0` so small" is a constraint on the chart constants (`SoftEdgeChart.delta0`), not part of the conclusion; the statement is for the given chart and `a <= 1`, which covers every eigenvalue (Step 0).
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

/-- **prop:tha-splice (a)** (bulk), error function `eta` in place of `h^r`: for every splice `n_s` in the window, `|hat N(n_s)/hat N - 1| <= C eta`, `|psi-hat^L - hat kappa psi-hat^R| <= C eta M_Web` on the window,
`|Psi_n - hat Psi^{(n_s)}_n| <= C eta V_n / hat N` for all `n`, with `C` independent of `n_s`. -/
def PropThaSpliceBulk {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V) (η : ℝ → ℝ) : Prop :=
  ∀ r, StdAssump Fz P (m / 2) r →
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 →
      ∀ ns ∈ bulkWindow CL N,
        |glueNormAt (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns / bulkNorm CL CR p X N - 1| ≤ C * η (Fz.step N) ∧
        (∀ n ∈ bulkWindow CL N, |CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n| ≤ C * η (Fz.step N) * (CL.chain p X N).M n) ∧
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
          ∀ k : Fin (N + 1), Xs k = X → ∀ n ∈ rowsOf N,
            |eigVec Um k n - splicedVec (CL.psiHatL p X N) (bulkSeqR CR p X N) (bulkWindow CL N) (rowsOf N) ns n|
              ≤ C * η (Fz.step N) * bulkEnv CL CR p X N n

/-- **prop:tha-splice (b)** (soft edge): the same for every `n_s` in the window `Omega`, and the fold row `n_c = nearestRow u_c` is an admissible splice for every column of the edge. -/
def PropThaSpliceSoft {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : SoftEdgeChart Fz P m q U V) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V) (η : ℝ → ℝ) : Prop :=
  ∀ r, StdAssump Fz P (q / 2) r →
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 → CL.aOf p X N ≤ 1 →
      nearestRow (Fz.step N) (CL.uc p) ∈ softWindow CL p X N ∧
      ∀ ns ∈ softWindow CL p X N,
        |glueNormAt (CL.psiHatL p X N) (softSeqR CR p X N) (softWindow CL p X N) (rowsOf N) ns / softNorm CL CR p X N - 1| ≤ C * η (Fz.step N) ∧
        (∀ n ∈ softWindow CL p X N, |CL.psiHatL p X N n - softKappa CL CR p X N * softSeqR CR p X N n|
            ≤ C * η (Fz.step N) * |CL.lamL p X N| * (kappaBal (CL.aOf p X N))⁻¹ * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ∧
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
          ∀ k : Fin (N + 1), Xs k = X → ∀ n ∈ rowsOf N,
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

section Splice2

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **prop:tha-splice (c)** (two orders, one shift) in matrix form: with the same `q = 2 ceil(m/2)`, for every spectrum and every column `j`,
`||(hat G^{[m]} - U) e_j||_2 <= C eta_m` and `||(hat G^{[m+1]} - U) e_j||_2 <= C eta_{m+1}` (the splices of `hat G` are the fixed ones `spl`). -/
def PropThaSpliceTwoOrders (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  1 ≤ m → Kidx = (m + 1) / 2 → q = 2 * Kidx → IsCompact K → HypOn F K → DM F K (2 * Kidx + 1) →
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
    (CL : SoftEdgeChart Fz P m q U V) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V) : Prop :=
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

/-- **lem:tha-collar (1)** (statement): outside the collar `|u_n - u_c| < eta/2`, `|Psi_n| + |hat Psi_n| <= C h^{-K} e^{-c/h}`; and the normalised matching-weighted recessive PC profile
and its scaled derivative at the exterior neighbours `n_1` (last row with `u <= u_c - eta/2`) and `n_4` (first with `u >= u_c + eta/2`) obey the same bound, with fixed `c, C, K > 0`, uniformly in the
eigenvalue and its index.  (Item (2) of the paper is `TransferInputs.t12_lb` and `reg_*` of the soft charts.) -/
def PropThaCollar {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : SoftEdgeChart Fz P m q U V) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V) : Prop :=
  ∀ r, StdAssump Fz P (q / 2) r →
    ∃ C c Kx h0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 → CL.aOf p X N ≤ 1 →
      (∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), Xs k = X → ∀ n ∈ rowsOf N, CL.η / 2 ≤ |uNode (Fz.step N) n - CL.uc p| →
          |eigVec Um k n| + |softVec CL CR p X N n| ≤ C * Fz.step N ^ (-Kx) * Real.exp (-c / Fz.step N)) ∧
      (|CL.lamL p X N| / softNorm CL CR p X N *
          |(CL.chain p X N).phi (Fz.step N) 0 2 ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋ / kappaBal (CL.aOf p X N)|
          ≤ C * Fz.step N ^ (-Kx) * Real.exp (-c / Fz.step N)) ∧
      (|CL.lamL p X N| / softNorm CL CR p X N *
          |(CL.chain p X N).wf 2 0 (uNode (Fz.step N) ⌊(CL.uc p - CL.η / 2) / Fz.step N - 1 / 2⌋) (Fz.step N) 1| / kappaBal (CL.aOf p X N)
          ≤ C * Fz.step N ^ (-Kx) * Real.exp (-c / Fz.step N)) ∧
      (|softKappa CL CR p X N * CR.lamL p X N| / softNorm CL CR p X N *
          |(CR.chain p X N).phi (Fz.step N) 0 2 ((N : ℤ) - ⌈(CL.uc p + CL.η / 2) / Fz.step N - 1 / 2⌉) / kappaBal (CL.aOf p X N)|
          ≤ C * Fz.step N ^ (-Kx) * Real.exp (-c / Fz.step N))

/-! ### The transfer inputs of all charts, and prop:thb-inputs -/

section Inputs

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- The transfer inputs (I2) of **every** chart of `hat G^{[m]}, hat G^{[m+1]}`: the left and right Weber charts of each bulk block (patch 1; the exact transfer is `Pi_+` of the Weber ladder, `omega_n = sqrt(s_n)`),
and the left and right PC halves of each soft edge (patch 2 of the soft chain on the collar, `omega = 1`; the right half is the left half of the mirror family).  Layer 4: `lem:smo-budget`, `lem:cha-weber-coord`, `lem:cha-PCcoord`, `lem:tha-collar` (2). -/
structure TransferBundle (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC)) where
  bulkL : ∀ ν, TransferInputs (frozenFamily F Kidx) (paramSet K t0) (fun _ => CP.CI0.lo ν) (fun _ => CP.CI0.hi ν) m
    (CP.CI0.bulkL ν).chain ((CP.CI1.bulkL (Fin.cast CP.nb_eq.symm ν))).chain 1
  bulkR : ∀ ν, TransferInputs (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) (fun _ => CP.CI0.lo ν) (fun _ => CP.CI0.hi ν) m
    (CP.CI0.bulkR ν).chain ((CP.CI1.bulkR (Fin.cast CP.nb_eq.symm ν))).chain 1
  softUpL : TransferInputs (frozenFamily F Kidx) (paramSet K t0) (fun p => (frozenFamily F Kidx).bandHi p - CP.CI0.softUpL.δ0)
    (fun p => (frozenFamily F Kidx).bandHi p + CP.CI0.softUpL.δ0) m CP.CI0.softUpL.chain CP.CI1.softUpL.chain 2
  softUpR : TransferInputs (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) (fun p => (frozenFamily F Kidx).bandHi p - CP.CI0.softUpL.δ0)
    (fun p => (frozenFamily F Kidx).bandHi p + CP.CI0.softUpL.δ0) m CP.CI0.softUpR.chain CP.CI1.softUpR.chain 2
  softLoL : TransferInputs (negFamily (frozenFamily F Kidx)) (paramSet K t0) (fun p => (negFamily (frozenFamily F Kidx)).bandHi p - CP.CI0.softLoL.δ0)
    (fun p => (negFamily (frozenFamily F Kidx)).bandHi p + CP.CI0.softLoL.δ0) m CP.CI0.softLoL.chain CP.CI1.softLoL.chain 2
  softLoR : TransferInputs (mirrorFamily (negFamily (frozenFamily F Kidx))) (paramSet K t0) (fun p => (negFamily (frozenFamily F Kidx)).bandHi p - CP.CI0.softLoL.δ0)
    (fun p => (negFamily (frozenFamily F Kidx)).bandHi p + CP.CI0.softLoL.δ0) m CP.CI0.softLoR.chain CP.CI1.softLoR.chain 2

/-- **prop:thb-inputs** (statement, the Layer-3 target): under `(D_{q_m+1})` and (H1)--(H3), with the charts and transfer inputs, there are constants `cs` (number of blocks and `C, K, omega_max, c_T, c_alpha, c_0, C_4, C_E`),
`N_0, C_eps, c_eps, K_eps` such that, for every `mu in K`, `N >= N_0` (with `h <= t0`) and every eigen-system `(X, U)` of `J_h`, there is a `JB.OneStepInputs cs (N+1) m h` whose `U` is `U`, whose `G0, G1` are the explicit
`hat G^{[m]}, hat G^{[m+1]}` (`compMatrix`, fixed splices `spl`), and whose exterior bound `eps5` satisfies `eps5 <= C_eps h^{-K_eps} e^{-c_eps/h}`.  All of (I1)--(I5), the host/submatrix structure (F3 (a), (d)), the
parity identity (F3 (b)) and the matching on the used rows are fields of `OneStepInputs`.  The constants are fixed before `mu` (F-B2). -/
def PropThbInputs (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (_TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  1 ≤ m → Kidx = (m + 1) / 2 → q = 2 * Kidx → IsCompact K → HypOn F K → DM F K (2 * Kidx + 1) →
    ∃ (cs : FormalResearch.JB.OneStepConsts) (N0 : ℕ) (Cε cε : ℝ) (Kε : ℕ), 0 < cε ∧ ∀ μ ∈ K, ∀ N : ℕ, N0 ≤ N → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∃ I : FormalResearch.JB.OneStepInputs cs (N + 1) m (F.step N),
          I.U = Um ∧ I.G0 = compMatrix CP.CI0 spl μ N Xs ∧ I.G1 = compMatrix CP.CI1 (CP.spl1 spl) μ N Xs ∧
          I.ε5 ≤ Cε * (1 / F.step N) ^ Kε * Real.exp (-cε / F.step N)

/-- **Theorem B** (statement, the form consumed by `JB.jb_onestep` / `thm_B_conditional`): there are `C` and `h_m` with `C h_m^m < 1` such that for `h <= h_m`, all `mu in K` and every eigen-system,
`||hat G_m - U_h|| <= C h^m`, and the polar factor of `hat G_m` is orthogonal and within `2 C h^m` of `U_h`.  `hat G_m` is `compMatrix` for the order-`m` bundle. -/
def ThmB (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  1 ≤ m → Kidx = (m + 1) / 2 → q = 2 * Kidx → IsCompact K → HypOn F K → DM F K (2 * Kidx + 1) →
    ∃ C hm : ℝ, 0 < hm ∧ C * hm ^ m < 1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ‖compMatrix CP.CI0 spl μ N Xs - Um‖ ≤ C * F.step N ^ m ∧
        (compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹)ᵀ *
            (compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹) = 1 ∧
        ‖compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹ - Um‖
          ≤ 2 * C * F.step N ^ m

end Inputs

end FormalResearch.JacobiEigenvectors.TheoremB
