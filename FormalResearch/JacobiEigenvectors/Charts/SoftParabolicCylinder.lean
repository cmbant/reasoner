module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily
public import FormalResearch.JacobiEigenvectors.Charts.LadderChain
public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.Regularity
public import FormalResearch.JacobiEigenvectors.Charts.BulkWeber

/-!
# Paper J, charts: the soft-edge (parabolic-cylinder) chart

Source: Paper J `charts.tex`: `lem:cha-PCcoord` (coordinate `zeta`, quantised shifts `mu_{2r}`), `thm:cha-PC` (comparison through coalescence;
**derived** in Layer 2 from this structure and the engine), `lem:cha-PCenv` (in `ParabolicCylinderFacts`); `thmA.tex` Sections "The comparison
sequences" (eq:tha-weber-seq, eq:tha-aPC, eq:tha-PCseq), "The soft edges" (eq:tha-YLsoft), `lem:tha-geom` (d), `prop:tha-W2`.

`SoftEdgeChart F P m q U V` is the hypothesis that the *left* soft-edge chart exists at the upper band edge `X_s^+` for all `mu in P`, all
`X` with `|X - X_s^+| <= delta_0`, all `N >= N0`: a ladder chain with **two patches** -- patch 1 the turning-point-free Weber ladder
on `[0, u_c - eta/2]` (coordinate `Y`, eq:tha-YLsoft), patch 2 the parabolic-cylinder ladder `-pair` on `[u_c - 2 eta, u_c + 2 eta]` with parameter
`a = a^{[q]}_PC` (eq:tha-aPC) and coordinate `Z_n = h^{-1/2} zeta(u_n - u_c; alpha)` -- overlapping at the bond `j_1`, `u_{j_1} <= u_c - eta < u_{j_1+1}`.
The *right* chart is `SoftEdgeChart (mirrorFamily F)`; the lower edge is `SoftEdgeChart (negFamily F)` (gauge `(-1)^n`, energy `-X`).

## Fields, with statement and discharging result

* `valid`: engine hypotheses for the two-patch chain: (SM1)--(SM3) for the Weber ladder (`lem:cha-weber-ladder`) and for the PC ladder (`SM` for the ODE translation
  `T_pm`, `thm:cha-PC` proof); defect bounds `eq:eng-UC1` of both patches (`thm:eng-corr` with the quantised shifts solving the solvability condition:
  **the corrector/defect output**, later Layer-1 module); `env` (`lem:cha-weber-env`, `lem:cha-PCenv`); `W_mono` and `transfer` (S3) (the forbidden-overlap argument after `thm:eng-volterra`).
* `zeta_*`, `muS_*`, `mu0_*`: `lem:cha-PCcoord` (the real two-turn Moser coordinate `zeta` and the shifts `mu_{2r}` of the quantisation condition; `thm:smo-MPS`, `thm:smo-TPC`, `thm:smo-WT2`); Layer 4.
* `Y_*`, `matchF_soft`: the turning-point-free Weber coordinate `Y_L` (`prop:cha-halfrow`(b)), defined by eq:tha-YLsoft.
* `W1_def`, `W2_def`, `M1_def`, `M2_def`: the global weights of the chain are the Weber weights (patch 1, rescaled by `lambda^{-1}`) and the PC recessive weights
  (patch 2) -- the rescaling convention of `thm:eng-volterra` (remark after (S3)); `lam` is derived, not a field.
* `wf1_eq`, `wf2_eq`: the model pairs are the Weber / PC functions of `ParabolicCylinderFacts`.

## Satisfiability

As for `BulkWeberChart`: no toy instance (the fields mention the actual parabolic-cylinder functions); the engine hypotheses are non-vacuous (`JE.volterra_multi_instance`).

## Honest differences

* `thm:cha-PC` in the paper states one comparison with the two-pair weights; here the same content is the two-patch chain.  The conclusion in terms of
  `lambda_L`, `M_Olv` (prop:tha-W2 (1)) is the *Layer-2* statement `TheoremA.PropThaW2`, derived from `LadderData.Stability`.
* the lower edge is obtained by `negFamily`; no separate structure.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JE

/-- The `-` pair `(y_1, y_2)` of lem:cha-PCenv (via `ParabolicCylinderFacts`), as functions of `Z`:
`a <= 0`: `(u~(a,-Z), -v~(a,-Z))`; `a > 0`: `(w~_+, -u~_+) = (kappa U(a,-Z), -kappa U(a,Z))`. -/
def pcMinus (U V : ℝ → ℝ → ℝ) (a : ℝ) : Fin 2 → ℝ → ℝ
  | 0 => fun z => if a ≤ 0 then ut U a (-z) else kappaBal a * U a (-z)
  | 1 => fun z => if a ≤ 0 then -vt V a (-z) else -(kappaBal a * U a z)

/-- The recessive weight of the `-` pair: `E_well(a,|Z|)` (`a <= 0`) or `E_bar(a,Z)^{-1}` (`a > 0`). -/
def Eminus (a z : ℝ) : ℝ := if a ≤ 0 then Ewell a |z| else (Ebar a z)⁻¹

/-- The soft-edge PC parameter `a^{[q]}_PC = -(1/h)(mu_0(alpha) + sum_{r=1}^{q/2} h^{2r} mu_{2r}(alpha))` (eq:tha-aPC), `muS r` = `mu_{2r}`. -/
def aPC (muS : ℕ → ℝ → ℝ) (q : ℕ) (h α : ℝ) : ℝ :=
  -(1 / h) * (muS 0 α + ∑ r ∈ Icc 1 (q / 2), h ^ (2 * r) * muS r α)

/-- **The left soft-edge chart at the upper edge, order `m`, shift index `q`** (see the module docstring). -/
structure SoftEdgeChart {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (P : Set Par) (m q : ℕ)
    (U V : ℝ → ℝ → ℝ) where
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
  /-- the fold `u_c = u_c^+` (the unique maximiser of `f_+`, (H3)). -/
  uc : Par → ℝ
  /-- the coordinate `zeta(x; alpha)` at `(mu, alpha, x)` and the shifts `mu_{2r}(alpha)` at `(r, mu, alpha)` (`muS 0 = mu_0`). -/
  zeta : Par → ℝ → ℝ → ℝ
  muS : ℕ → Par → ℝ → ℝ
  /-- the turning-point-free Weber coordinate `Y_L(u; X)` (eq:tha-YLsoft) on `[0, u_c - eta/2]`. -/
  Y : Par → ℝ → ℝ → ℝ
  chain : Par → ℝ → ℕ → LadderData
  uc_spec : ∀ μ ∈ P, 0 < uc μ ∧ uc μ < F.L ∧ fPlus F.L (F.G 0 μ) (F.B 0 μ) (uc μ) = F.bandHi μ
  /-- lem:cha-PCcoord (1): `d_- <= d_x zeta <= d_+` on `|x| <= 2 eta`, `zeta(0;0) = 0`, `|zeta(0;alpha)| <= c_Z |alpha|`. -/
  zeta_deriv : ∀ μ ∈ P, ∀ α, |α| ≤ δ0 → ∀ x, |x| ≤ 2 * η → dm ≤ deriv (zeta μ α) x ∧ deriv (zeta μ α) x ≤ dp
  zeta_zero : ∀ μ ∈ P, zeta μ 0 0 = 0
  zeta_alpha : ∀ μ ∈ P, ∀ α, |α| ≤ δ0 → |zeta μ α 0| ≤ cZ * |α|
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
  /-- the shape of the two-patch chain: hard-edge seed, overlap bond `j_1` with `u_{j_1} <= u_c - eta < u_{j_1+1}`, last row `N_R` with `u_{N_R} <= u_c + 2 eta < u_{N_R+1}`. -/
  shape : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    (chain μ X N).P = 2 ∧ (chain μ X N).s0 = 0 ∧
      uNode (F.step N) ((chain μ X N).jj 1) ≤ uc μ - η ∧ uc μ - η < uNode (F.step N) ((chain μ X N).jj 1 + 1) ∧
      uNode (F.step N) (chain μ X N).NR ≤ uc μ + 2 * η ∧ uc μ + 2 * η < uNode (F.step N) ((chain μ X N).NR + 1)
  valid : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → (chain μ X N).Valid cs (F.step N) m
  A_bond : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (-1 : ℤ) (chain μ X N).NR,
    (chain μ X N).A k = F.bondA μ N k
  Q_diag : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chain μ X N).NR,
    (chain μ X N).Q k = F.diagQ μ N X k
  /-- patch 1: `D = sqrt s` (hard edge); patch 2: `D = 1` (interior lattice); `omega_mod = h^{1/2}` for both. -/
  dd_one : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    (∀ s h', (chain μ X N).dd 1 s h' = Real.sqrt s) ∧ (∀ s h', (chain μ X N).dd 2 s h' = 1)
  omega_sqrt : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ p ∈ Finset.Icc 1 2,
    (chain μ X N).ω p (F.step N) = Real.sqrt (F.step N)
  /-- patch 1 model pair: Weber functions at `Z = h^{-1/2} Y(u_k)`, `a = -(k+1/2)`. -/
  wf1_eq : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) ((chain μ X N).jj 1 + 1),
    (chain μ X N).wf 1 0 (uNode (F.step N) k) (F.step N) =
      ![ut U (-((k : ℝ) + 1 / 2)) (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)),
        Real.sqrt (F.step N) * (kappaBal (-((k : ℝ) + 1 / 2)) * deriv (U (-((k : ℝ) + 1 / 2)))
          (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)))]
  /-- patch 2 model pair: the `-` pair of `U, V` at `a = a^{[q]}_PC`, `Z = h^{-1/2} zeta(u_k - u_c; alpha)`, `alpha = X_s^+ - X`. -/
  wf2_eq : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    ∀ k ∈ Finset.Icc ((chain μ X N).jj 1) ((chain μ X N).NR + 1), ∀ α : Fin 2,
    (chain μ X N).wf 2 α (uNode (F.step N) k) (F.step N) =
      ![pcMinus U V (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X)) α
          (zeta μ (F.bandHi μ - X) (uNode (F.step N) k - uc μ) / Real.sqrt (F.step N)),
        Real.sqrt (F.step N) * deriv (pcMinus U V (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X)) α)
          (zeta μ (F.bandHi μ - X) (uNode (F.step N) k - uc μ) / Real.sqrt (F.step N))]
  /-- the global weights: `W = E_Web / lambda`, `M = M_Web` on patch 1; `W = E_minus(a, Z)`, `M = M_bal(a,Z)` on patch 2
  (`lambda = E_Web(j_1)/E_minus(j_1)`, so the weight is continuous at the overlap). -/
  W1_def : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) ((chain μ X N).jj 1),
    (chain μ X N).W k =
      Ewell (-((k : ℝ) + 1 / 2)) |Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)|
        / (Ewell (-(((chain μ X N).jj 1 : ℝ) + 1 / 2)) |Y μ X (uNode (F.step N) ((chain μ X N).jj 1)) / Real.sqrt (F.step N)|
          / Eminus (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X))
              (zeta μ (F.bandHi μ - X) (uNode (F.step N) ((chain μ X N).jj 1) - uc μ) / Real.sqrt (F.step N)))
  M1_def : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) ((chain μ X N).jj 1),
    (chain μ X N).M k = Mbal (-((k : ℝ) + 1 / 2)) (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N))
  W2_def : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    ∀ k ∈ Finset.Icc ((chain μ X N).jj 1 + 1) (chain μ X N).NR,
    (chain μ X N).W k = Eminus (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X))
      (zeta μ (F.bandHi μ - X) (uNode (F.step N) k - uc μ) / Real.sqrt (F.step N))
  M2_def : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N →
    ∀ k ∈ Finset.Icc ((chain μ X N).jj 1 + 1) (chain μ X N).NR,
    (chain μ X N).M k = Mbal (aPC (fun r α' => muS r μ α') q (F.step N) (F.bandHi μ - X))
      (zeta μ (F.bandHi μ - X) (uNode (F.step N) k - uc μ) / Real.sqrt (F.step N))
  /-- the modulus sum is bounded: `Theta_h <= C_sum` (the powers of `h` cancel, as in the bulk). -/
  theta_le : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → (chain μ X N).theta (F.step N) ≤ Csum
  /-- `rho = rho~ = 1`. -/
  rho_one : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chain μ X N).NR,
    (chain μ X N).ρ k = 1 ∧ (chain μ X N).ρt k = 1
  /-- `psi-hat_0 > 0` (Weber seed). -/
  seed_pos : ∀ μ ∈ P, ∀ X, |X - F.bandHi μ| ≤ δ0 → ∀ N, N0 ≤ N → 0 < (chain μ X N).phi (F.step N) 0 1 0

namespace SoftEdgeChart

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
  (C : SoftEdgeChart F P m q U V)


/-- The PC parameter `a_k = a^{[q]}_PC` at `(mu, X, N)`. -/
def aOf (μ : Par) (X : ℝ) (N : ℕ) : ℝ := aPC (fun r α' => C.muS r μ α') q (F.step N) (F.bandHi μ - X)

/-- The PC coordinate `Z_n = h^{-1/2} zeta(u_n - u_c; alpha)`. -/
def Zof (μ : Par) (X : ℝ) (N : ℕ) (n : ℤ) : ℝ :=
  C.zeta μ (F.bandHi μ - X) (uNode (F.step N) n - C.uc μ) / Real.sqrt (F.step N)

/-- The overlap bond `j_1`. -/
def j1 (μ : Par) (X : ℝ) (N : ℕ) : ℤ := (C.chain μ X N).jj 1

/-- `lambda_L := W_{j_1}(psi-hat^{L,Web}, psi-hat^{(2)}) / W_{j_1}(psi-hat^{PC,-}, psi-hat^{(2)})` (prop:tha-W2 (1)); `psi-hat^{PC,-} = phi^{(1)}_2 / kappa_bal`
and `psi-hat^{(2)} = phi^{(2)}_2` is the second-branch sequence.  (`cas` is the paper's Casoratian `W` with the same sign.) -/
def lamL (μ : Par) (X : ℝ) (N : ℕ) : ℝ :=
  cas (C.chain μ X N).A ((C.chain μ X N).phi (F.step N) 0 1) ((C.chain μ X N).phi (F.step N) 1 2) (C.j1 μ X N) /
    cas (C.chain μ X N).A (fun n => (C.chain μ X N).phi (F.step N) 0 2 n / kappaBal (C.aOf μ X N))
      ((C.chain μ X N).phi (F.step N) 1 2) (C.j1 μ X N)

/-- The left sequence through the soft edge (the vector `psi-hat^L` of prop:tha-W2 (2)): Weber on `u_n <= u_c - eta/2`,
`lambda_L psi-hat^{PC,-}` on the collar. -/
def psiHatL (μ : Par) (X : ℝ) (N : ℕ) (n : ℤ) : ℝ :=
  if uNode (F.step N) n ≤ C.uc μ - C.η / 2 then (C.chain μ X N).phi (F.step N) 0 1 n
  else C.lamL μ X N * ((C.chain μ X N).phi (F.step N) 0 2 n / kappaBal (C.aOf μ X N))

end SoftEdgeChart

end FormalResearch.JacobiEigenvectors.Charts
