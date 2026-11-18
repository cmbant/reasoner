module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily
public import FormalResearch.JacobiEigenvectors.Charts.LadderChain
public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.Regularity

/-!
# Paper J, charts: the bulk Weber (hard-edge) chart and the phase inputs

Source: Paper J `charts.tex`: `lem:cha-weber-ladder`, `lem:cha-weber-env`, `lem:cha-W0`, `lem:cha-weber-coord`, `prop:cha-halfrow`
(coordinate, correctors), `thm:cha-I`/`cor:cha-I-general` (the comparison theorem: **derived** in Layer 2 from this structure and the engine);
`thmA.tex` Section "The Weber--Langer coordinate" (eq:tha-matchF, eq:tha-matchO), `lem:tha-geom`(a)--(c); `app_thmA.tex`
`lem:smo-bulkphase`.

`BulkWeberChart F P Jlo Jhi m U V` is the hypothesis that the left (hard-edge) Weber charts exist at order `m` for every parameter
`mu in P` (a set of parameters of the family `F`; for the frozen family this includes `t`), every energy `X in [Jlo, Jhi]` and
every `N >= N0`.  The right chart is the same structure for `mirrorFamily F`.  The chart gives, for each `(mu, X, N)`, a `LadderData` with
`P = 1` patch and a hard-edge seed (`s0 = 0`): the Weber ladder `w^{(alpha)}_j(Z_j)`, `Z_j = h^{-1/2} Y(u_j; X)`, the corrector row `(A^{[m]}, h B^{[m]})`,
and the envelopes `W = E_Web`, `M = M_Web`.

## Fields, the paper statement each stands for, the Layer-4 result that discharges it

* `valid` (all hypotheses of the engine, `LadderChain`): (SM1)--(SM3) = `lem:cha-weber-ladder` (DLMF 12.8 + ODE transfer in `SL_2`);
  `env` = `lem:cha-weber-env` (1) via `lem:cha-PCenv` (Olver); `cas_lb`, `defect*`, `A_bd`, `B_bd` = `eq:eng-UC1` from `thm:eng-corr` and
  `prop:cha-halfrow`/`lem:cha-weber-coord` (3) (**the corrector/defect output**, a later Layer-1 module); `W_mono` = `lem:cha-weber-env` (2).
  The fields that the paper *derives* in Layer 2 from `ParabolicCylinderFacts` (e.g. `env` from `env_well`) stay fields so that Layer 2 does not redo the
  special-function work; discharge = prove them from `pc` (item L4.W of `PLAN.md`).
* `turn_eq`, `Hz_lb`, `matchF`, `matchO`, `Y_reg`: the matched Weber coordinate (`prop:cha-halfrow`(a), `lem:cha-weber-coord`, eq:tha-matchF/O): `matchF`/`matchO`
  *define* `Y` (they are its action identities); existence, uniqueness and regularity (`C^{r-2}`, `lem:smo-budget`(b)) are Layer 4 (`app_smooth.tex`).
* `wf_eq`: the model pair is the Weber function `u~(-(j+1/2), .)` of `ParabolicCylinderFacts` at `Z_j` (`cha-weberPC`).
* `theta_le`: `lem:cha-weber-env` (3), the modulus sum `Theta_h = h^{1/2} sum M^2 <= C_sum`.
* `W_osc`, `M_osc`: `W = 1` and `M ~ h^{1/4}` on the oscillatory overlap (the Airy argument is `<= -c_*` there; app_thmA Step 2).
* `seed_pos`, `collar_lb`: `psi-hat_0 > 0` (`w_0 = e^{-z^2/4}`) and the relative lower bound on the forbidden collar `|psi-hat| >= c E M`
  (`lem:cha-W0` plus smallness of the corrector term).

None of the fields is an estimate of an exact solution of the recurrence or of an eigenvector: all fields concern the model functions,
the coordinate, the corrector row and the *defect* of the comparison sequence.

## Satisfiability

`BulkWeberChart` mentions the actual parabolic-cylinder functions (via `wf_eq` and `valid`), so no toy instance exists without them
(`ParabolicCylinderFacts` has none either).  What *is* satisfiable, and checked here, is the engine part: `JE.volterra_multi_instance` and
`JE.constant_ladder` are instances of the hypotheses of `LadderData.Valid` modulo the lattice normalisation; no new instance is claimed.

## Honest differences

* the paper's `Y_L` for energies at which `X` is a collision energy `B_0(0)`, where `u_- = 0`, is covered by the same fields (`uMinus = 0`).
* the oscillatory overlap `[c', c]` and the margin `sigma` are chart constants (paper: `Lemma tha-geom`(c)); the chart extends beyond `c` by `sigma`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Engine

/-- `arccosh x = log(x + sqrt(x^2 - 1))`, `x >= 1`. -/
def arccoshR (x : ℝ) : ℝ := Real.log (x + Real.sqrt (x ^ 2 - 1))

/-- The one-sided oscillatory action `Theta_L(u) = int_0^u Re arccos(Q_0/(2 sqrt E_0)) dv` (eq:tha-matchO). -/
def thetaL (L : ℝ) (G0 B0 : ℝ → ℝ) (X u : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..u, Real.arccos ((X - B0 v) / (2 * Real.sqrt (E0 L G0 v)))

/-- **The left Weber chart at order `m`** (see the module docstring). -/
structure BulkWeberChart {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (P : Set Par)
    (Jlo Jhi : ℝ) (m : ℕ) (U V : ℝ → ℝ → ℝ) where
  cs : ChainConsts
  N0 : ℕ
  /-- the oscillatory overlap `[c', c]`, the margin `sigma` and the other chart constants. -/
  c' : ℝ
  c : ℝ
  σ : ℝ
  Csum : ℝ
  cM : ℝ
  CM : ℝ
  cH : ℝ
  c3 : ℝ
  /-- the matched Weber coordinate `Y(u; X)` and the factor `H_Z` in `4u - Y^2 = (u - u_-) H_Z`. -/
  Y : Par → ℝ → ℝ → ℝ
  Hz : Par → ℝ → ℝ → ℝ
  /-- the ladder data (total functions; `valid` etc. below hold on the parameter set). -/
  chain : Par → ℝ → ℕ → LadderData
  /-- constants. -/
  consts_pos : 0 < c' ∧ c' < c ∧ 0 < σ ∧ c + σ < F.L ∧ 0 < cH ∧ 0 < cM ∧ cM ≤ CM ∧ 0 < c3 ∧ 0 ≤ Csum ∧ Jlo ≤ Jhi
  /-- `lem:tha-geom` (c): the overlap lies in the oscillatory well `[u_- + sigma, u_+ - sigma]` for all `(mu, X)`. -/
  overlap_in_well : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, F.uMinus μ X + σ ≤ c' ∧ c ≤ F.uPlus μ X - σ
  /-- `prop:cha-halfrow` (a): one simple turning point, `4u - Y^2 = (u - u_-) H_Z`, `H_Z >= c_H`. -/
  turn_eq : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ u ∈ Set.Icc 0 (c + σ), 4 * u - Y μ X u ^ 2 = (u - F.uMinus μ X) * Hz μ X u
  Hz_lb : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ u ∈ Set.Icc 0 (c + σ), cH ≤ Hz μ X u
  /-- eq:tha-matchF: the forbidden-collar action identity, `eps Y >= 2 sqrt u`, `eps = sgn Q_0(0;X)`. -/
  matchF : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ u ∈ Set.Icc 0 (F.uMinus μ X),
    (∫ v in u..(Y μ X u ^ 2 / 4), arccoshR (|Y μ X u| / (2 * Real.sqrt v)))
      = ∫ v in u..(F.uMinus μ X),
          arccoshR (SignType.sign (X - F.B 0 μ 0) * (X - F.B 0 μ v) / (2 * Real.sqrt (E0 F.L (F.G 0 μ) v)))
  /-- eq:tha-matchO: the oscillatory action identity on `[u_-, c]`, `|Y| <= 2 sqrt u`. -/
  matchO : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ u ∈ Set.Icc (F.uMinus μ X) c,
    (∫ t in (Y μ X u)..(2 * Real.sqrt u), Real.sqrt (u - t ^ 2 / 4)) = thetaL F.L (F.G 0 μ) (F.B 0 μ) X u
  /-- the coordinate is bounded `C^2` in `(u, X)` on `[0, c + sigma] x [Jlo, Jhi]` (`lem:smo-budget` (b): `C^{r-2}`, `r >= 5` suffices). -/
  Y_bound : ∃ S : ℝ, ∀ μ ∈ P, BoundedC2 (fun u X => Y μ X u) 0 (c + σ) Jlo Jhi S
  /-- the shape of the chain: one patch, hard-edge seed, rows `0..N_R` with `u_{N_R} <= c < u_{N_R+1}`. -/
  shape : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N →
    (chain μ X N).P = 1 ∧ (chain μ X N).s0 = 0 ∧ 0 ≤ (chain μ X N).NR ∧
      uNode (F.step N) (chain μ X N).NR ≤ c ∧ c < uNode (F.step N) ((chain μ X N).NR + 1)
  /-- the engine hypotheses (`eq:eng-UC1`, (SM1)--(SM3), envelopes, transfer: none for `P = 1`). -/
  valid : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → (chain μ X N).Valid cs (F.step N) m
  /-- the chain's operator is the Jacobi operator of the family at energy `X`. -/
  A_bond : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (-1 : ℤ) (chain μ X N).NR, (chain μ X N).A k = F.bondA μ N k
  Q_diag : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chain μ X N).NR, (chain μ X N).Q k = F.diagQ μ N X k
  /-- the Weber ladder: `D(s,h) = sqrt s` (exact square-root hard edge) and `omega_mod(h) = h^{1/2}`. -/
  dd_sqrt : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → ∀ s h', (chain μ X N).dd 1 s h' = Real.sqrt s
  omega_sqrt : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → (chain μ X N).ω 1 (F.step N) = Real.sqrt (F.step N)
  /-- the model pair is the Weber functions of `ParabolicCylinderFacts` at `a = -(k + 1/2)`, `Z = h^{-1/2} Y(u_k)` (cha-weberPC). -/
  wf_eq : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) ((chain μ X N).NR + 1),
    (chain μ X N).wf 1 0 (uNode (F.step N) k) (F.step N) =
      ![ut U (-((k : ℝ) + 1 / 2)) (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)),
        Real.sqrt (F.step N) * (kappaBal (-((k : ℝ) + 1 / 2)) * deriv (U (-((k : ℝ) + 1 / 2)))
          (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)))] ∧
    (chain μ X N).wf 1 1 (uNode (F.step N) k) (F.step N) =
      ![vt V (-((k : ℝ) + 1 / 2)) (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)),
        Real.sqrt (F.step N) * (Real.sqrt (Real.pi / 2) * (kappaBal (-((k : ℝ) + 1 / 2)))⁻¹
          * deriv (V (-((k : ℝ) + 1 / 2))) (Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)))]
  /-- `rho = rho~ = 1`: the defect is uniformly `O(h^{m+1})`. -/
  rho_one : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chain μ X N).NR,
    (chain μ X N).ρ k = 1 ∧ (chain μ X N).ρt k = 1
  /-- lem:cha-weber-env (3): `Theta_h <= C_sum`. -/
  theta_le : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → (chain μ X N).theta (F.step N) ≤ Csum
  /-- on the overlap `W = 1` (no barrier) and `M ~ h^{1/4}`. -/
  W_osc : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chain μ X N).NR,
    c' ≤ uNode (F.step N) k → (chain μ X N).W k = 1
  M_osc : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chain μ X N).NR,
    c' ≤ uNode (F.step N) k →
      cM * (F.step N) ^ ((1 : ℝ) / 4) ≤ (chain μ X N).M k ∧ (chain μ X N).M k ≤ CM * (F.step N) ^ ((1 : ℝ) / 4)
  /-- `psi-hat_0 > 0`. -/
  seed_pos : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → 0 < (chain μ X N).phi (F.step N) 0 1 0
  /-- relative lower bound on the forbidden collar `u_k <= u_-` (lem:cha-W0). -/
  collar_lb : ∀ μ ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N, N0 ≤ N → ∀ k ∈ Finset.Icc (0 : ℤ) (chain μ X N).NR,
    uNode (F.step N) k ≤ F.uMinus μ X →
      c3 * (chain μ X N).W k * (chain μ X N).M k ≤ |(chain μ X N).phi (F.step N) 0 1 k|

namespace BulkWeberChart

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {Jlo Jhi : ℝ} {m : ℕ}
  {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart F P Jlo Jhi m U V)

/-- The left comparison sequence `psi-hat^{L,[m]}_n` (eq:tha-weber-seq) of the chart at `(mu, X, N)`. -/
def psiHatL (μ : Par) (X : ℝ) (N : ℕ) : ℤ → ℝ := (C.chain μ X N).psiHat (F.step N) 1

/-- The envelope `E_Web M_Web` (the product `W M`) along the lattice. -/
def envL (μ : Par) (X : ℝ) (N : ℕ) (k : ℤ) : ℝ := (C.chain μ X N).W k * (C.chain μ X N).M k

/-- The last row of the left patch (`u_{N_R} <= c`). -/
def NRL (μ : Par) (X : ℝ) (N : ℕ) : ℤ := (C.chain μ X N).NR

end BulkWeberChart

/-- **The all-order phase inputs of the bulk charts** (`lem:smo-bulkphase` (4) and `lem:smo-S0`, `thm:smo-BSr`): for each interval `J_nu` of a finite cover,
functions `Sigma_{nu,j}(mu; X)` (`j = 0, 2..M`; `Sigma_0 = S_0`, `Sigma_1 = 0`), jointly `C^{2M+1}` in `(X, t)` through the hard-edge collision energies, such that the
**Casoratian of the two comparison sequences** (left chart and mirror chart) on the overlap is `pi [sin(Sigma/h - pi/2) + O(h^m)]` with a
positive prefactor.  This concerns the comparison sequences built from Weber functions and charts only (not eigenvalues or eigenvectors);
Layer 4: DLMF 12.10.35 (Olver 1959), Stirling's series, and the smooth collision charts.  The parameter set is `P = K x [-t0,t0]` for a frozen
family, so `t` is the second component of `mu`.  `S0 mu X` is the action (eq:S0), defined from the principal symbols. -/
structure BulkPhaseInputs {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily (Par × ℝ)) (P : Set (Par × ℝ)) (K : Set Par) (t0 : ℝ)
    (Jlo Jhi : ℝ) (M : ℕ) (U V : ℝ → ℝ → ℝ) (CL : BulkWeberChart F P Jlo Jhi (max M 1) U V) (CR : BulkWeberChart (mirrorFamily F) P Jlo Jhi (max M 1) U V) where
  /-- `Sigma_{nu,j}(X, t)` at `(mu, j, X, t)`. -/
  Sigma : Par → ℕ → ℝ → ℝ → ℝ
  /-- regularity: `Sigma_j(mu; ., .)` is `C^{2M+1}` on `[Jlo,Jhi] x [-t0,t0]` (`thm:smo-BSr`). -/
  Sigma_reg : ∀ μ ∈ K, ∀ j ≤ M, JetRegJ (Sigma μ j) (Set.Icc Jlo Jhi) t0 (2 * M + 1)
  /-- `Sigma_0 = S_0^{(t)}`: the action of the principal symbols at `t`. -/
  Sigma_zero : ∀ μ ∈ K, ∀ X ∈ Set.Icc Jlo Jhi, ∀ t ∈ Set.Icc (-t0) t0,
    Sigma μ 0 X t = ∫ u in (0 : ℝ)..F.L, Real.arccos ((X - F.B 0 (μ, t) u) / (2 * Real.sqrt (E0 F.L (F.G 0 (μ, t)) u)))
  /-- `Sigma_1 = 0` (the phase of the left/right comparison sequences has no term of order `h`). -/
  Sigma_one : ∀ μ ∈ K, ∀ X ∈ Set.Icc Jlo Jhi, ∀ t ∈ Set.Icc (-t0) t0, Sigma μ 1 X t = 0
  /-- the Casoratian of the comparison sequences: `|C_n(psi-hat^L, psi-hat^R) - pi [sin(Sigma/h - pi/2)]| <= Ccas h^m pi` with `pi > 0`
  (the prefactor), at every overlap row `n`.  `psi-hat^R_n` is the mirror chart sequence at row `N - n`. -/
  casoratian : ∃ Ccas N0 : ℝ, ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, N0 ≤ N →
    ∃ pre : ℝ, 0 < pre ∧ ∀ n : ℤ, 0 ≤ n → n < N → CL.c' ≤ uNode (F.step N) n → uNode (F.step N) n ≤ CL.c →
      |F.bondA (μ, t) N n * (CL.psiHatL (μ, t) X N n * (CR.psiHatL (μ, t) X N ((N : ℤ) - (n + 1))) -
          CL.psiHatL (μ, t) X N (n + 1) * (CR.psiHatL (μ, t) X N ((N : ℤ) - n)))
        - pre * Real.sin ((∑ j ∈ range (M + 1), F.step N ^ j * Sigma μ j X t) / F.step N - Real.pi / 2)|
        ≤ Ccas * F.step N ^ (max M 1) * pre

end FormalResearch.JacobiEigenvectors.Charts
