module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Engine.VolterraLadder
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily

/-!
# Paper J, charts: the engine interface (chains of ladder pairs)

Source: Paper J `engine.tex`, `thm:eng-volterra` (a) (multi-patch Casoratian--Volterra stability), (b) (ladder pairs) and
`thm:eng-defect`; the engine is formalised in `FormalResearch.JacobiEigenvectors.Engine` (to be moved to `FormalResearch.JacobiEigenvectors.Engine`).

A **ladder chain** is the data and the hypotheses with which the engine is applied to one edge solution of the Jacobi
recurrence: `P` patches, each with its own symplectic model ladder (`SymplecticLadder`: (SM1)--(SM3)), its own
corrector row `v = (A^{[m]}, h B^{[m]})`, and common envelopes `(M, W)`, residual weights `(rho, rho~)` and constants.
The fields are exactly the hypotheses of `FormalResearch.JacobiEigenvectors.Engine.ladder_pair_stability`, with the ladder `(D, P, Q, Pi, omega, w)`
and the row `v` allowed to depend on the patch (the Weber patch and the parabolic-cylinder patch of a soft edge have
different ladders); (S1) is the Casoratian lower bound `|F_cas| >= c_-`, (S2) the envelopes and bounds on the row, (R) the
**defect bounds `eq:eng-UC1`** (the output of `thm:eng-corr`, a hypothesis here: it is proved in a later Layer-1 module), (S3) the transfer-matrix bounds.

* `LadderData` is the data only (total functions); `LadderData.Valid cs h m` is the conjunction of the hypotheses for step `h` and
  order `m`.  This split lets a chart be a total function of `(mu, X, N)` whose `Valid` holds on the parameter set.
* `LadderData.Concl cs h m psi`: the conclusion of `volterra_multi` (constants `mvC`, `volTheta`), as a Prop.
* `LadderData.Stability cs h m`: "Valid implies, for every solution `psi` with the seed of patch 1 and `eps*Theta` small, `Concl`":
  the statement of `thm:eng-volterra` for per-patch ladders.  A Prop-valued definition, **proved later** (Layer 1, item L1.1 of `PLAN.md`):
  for one shared ladder it is `ladder_pair_stability`; for per-patch ladders the same proof applies, since `ladder_S1`, `ladder_S2`,
  `ladder_residual_interior/hard` are patchwise and only the final call is `volterra_multi`.

## `PreValid` and `Valid` (round 4, finding F-W2-7 resolved)

`Valid` = `PreValid` (all hypotheses of `thm:eng-volterra` except the transfer condition (S3)) plus `transfer` (`TransferAt` at every overlap).  `LadderData.stability` needs the full `Valid`; a chart whose overlaps are
*forbidden* (case (ii) after `thm:eng-volterra`) or bounded (case (i)) can state only `PreValid` and derive (S3) from chart-level inputs (`Engine.transfer_of_forbidden_overlap`,
`TheoremA/SoftTransfer.lean`).  `PreValid` does not mention `cs.Λ`, so a derived (S3) may use a larger `Λ` (`PreValid.toValid`).  Charts with one patch (`BulkWeberChart`) keep `Valid` (`transfer` is vacuous for `P = 1`).

## Differences from `ladder_pair_stability` (all fields are what the proofs use)

1. per-patch ladders and rows (see above); one common operator `(A, Q)`, tied to every patch ladder on the window by `A_eq`, `Q_eq`.
2. the hypotheses (UC1), `|F_cas| >= c_-`, bounds on `A`, `h B rho/rho~`, are required on the window of each patch, not at all `k >= 0`.
3. the seed is `s0 in {0,1}` (`0`: hard edge; `1`: two-node seed), as in `volterra_multi`.

Satisfiability: see `Charts/BulkWeber.lean` (non-vacuity of the underlying `volterra_multi` hypotheses is `JE.volterra_multi_instance`).

## Round 2 audit: `LadderData.Valid` (verdict: sound; one quantifier remark)

* **(a) fields vs. the paper.**  Every field is one of the hypotheses of `volterra_multi` / `ladder_pair_stability` (thm:eng-volterra (a),(b)) per patch window
  (S1 `cas_lb`, S2 `env`, `A_bd`, `B_bd`, S3 `transfer`, R `defect*`), or a lattice-normalisation fact of the setting (`jj*`, `shape` of the patches, `A_eq`, `Q_eq`, `A_hard`, `D_hard`,
  `annih`).  `A_eq` at `k = -1` reads `ladderA(-1) = pp(0) dd(0) = A_{-1} = 0`, so the hard edge is enforced by `dd 1 s = sqrt s` (BulkWeberChart `dd_sqrt`).
* **`SymplecticLadder` is required for all `h > 0` and all lattice points `j in N`**, not only the sampled ones (`wronsk`, `shift_up`, `shift_dn`, `det_*`, `prod`, `par_*` are
  `forall h`, `forall u`, `forall j`).  This is satisfiable for a genuine chart: `wf` is then the Weber / PC model pair at every `(u, h)` (`a = -u/h`, resp. `a(h)`), the coordinate `Y`, `zeta`
  being extended off the sampled range by any monotone extension (the structure constrains them only where the chart lives); `PiP, PiM` are determined on the lattice by (SM2) and
  completed off it by `PiP = D_+ I`, `PiM = D_- I`, `prod` and `par_*` then hold identically.  This is the content of lem:cha-weber-ladder / the ODE translation `T_pm` (all `h`), so no
  field is stronger than what the paper proves; but note that the `LadderData` of `chain mu X N` is built for the *fixed* `h = step N` and must nevertheless satisfy the ladder axioms for all `h`.
* **(b) no conclusion in the hypotheses.**  `defect0/1` bound the residual of the *comparison* sequence (not of an exact solution); `cas_lb` and `seed_pos` (in the chart structures) force the
  corrector row to be non-zero (a zero row has zero defect but `Fcas = 0`).  `Valid` does not mention an eigenvalue or eigenvector.  Consistency of the numerical constants
  (`K_D`, `c_-`, `K_A`, `K_B`, `K_w`, `Lambda`) is that of `volterra_multi_instance` (the rotation ladder, `A = 1`, `Q = 2 cos theta`, `Fcas = sin theta`).
* **(c) redundancy.**  `h_pos`, `P_pos`, `jj0`, `jj_mono`, `jj_last`, `s0_cases` are bookkeeping; `omega_eq` is `|omega_p| = |omega_1|`; none is derivable from the others.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Finset FormalResearch.JacobiEigenvectors.Engine

/-- The constants of an engine application (uniform in `h`, `X`, `mu`). -/
structure ChainConsts where
  Λ : ℝ
  CE : ℝ
  cm : ℝ
  KD : ℝ
  Kw : ℝ
  KA : ℝ
  KB : ℝ
  Λ_ge : 1 ≤ Λ
  cm_pos : 0 < cm
  KD_nonneg : 0 ≤ KD
  Kw_nonneg : 0 ≤ Kw
  KA_nonneg : 0 ≤ KA
  KB_nonneg : 0 ≤ KB

/-- The data of a ladder chain; sites are `u_k = (k + 1/2) h`, bonds `s_k = (k+1) h` (`gamma = 1/2`). -/
structure LadderData where
  P : ℕ
  /-- the last row `N_R` of the chain (patch `P` ends at `jj P = NR - 1`, its window at `NR`). -/
  NR : ℤ
  /-- `s0 = 0`: hard-edge seed; `s0 = 1`: two-node seed. -/
  s0 : ℤ
  jj : ℕ → ℤ
  /-- the bonds `A_k = a_k` and diagonal `Q_k = X - B_k` of the operator. -/
  A : ℤ → ℝ
  Q : ℤ → ℝ
  dd : ℕ → ℝ → ℝ → ℝ
  pp : ℕ → ℝ → ℝ → ℝ
  qq : ℕ → ℝ → ℝ → ℝ
  PiP : ℕ → ℝ → ℝ → M2
  PiM : ℕ → ℝ → ℝ → M2
  ω : ℕ → ℝ → ℝ
  wf : ℕ → Fin 2 → ℝ → ℝ → V2
  /-- the corrector rows `A^{[m]}(u,h^2)`, `B^{[m]}(u,h^2)` of each patch. -/
  AA : ℕ → ℝ → ℝ → ℝ
  BB : ℕ → ℝ → ℝ → ℝ
  ρ : ℤ → ℝ
  ρt : ℤ → ℝ
  W : ℤ → ℝ
  M : ℤ → ℝ

namespace LadderData

variable (D : LadderData)

/-- The comparison pair of patch `p`: `phi^{(alpha)}_p(k) = v_p(u_k, h) . w^{(alpha)}_p(u_k)`. -/
def phi (h : ℝ) (α : Fin 2) : ℕ → ℤ → ℝ :=
  fun p k => ladderSeq (D.AA p) (D.BB p) (D.wf p) (1 / 2) h α k

/-- The modulus sum `Theta_h = (h/omega_*) sum rho M^2` (`omega_* = |omega_mod(h)|` of patch 1). -/
def theta (h : ℝ) : ℝ := volTheta h |D.ω 1 h| D.s0 D.jj D.P D.ρ D.M

/-- The single-valued comparison sequence `psi-hat` of the chain (`psiHat` of `VolterraMulti`) on patch `p`. -/
def psiHat (h : ℝ) (p : ℕ) (j : ℤ) : ℝ := FormalResearch.JacobiEigenvectors.Engine.psiHat (D.phi h 0) (D.phi h 1) D.jj p j

/-- The hypotheses of `thm:eng-volterra` for the chain **without the transfer condition (S3)**, at step `h` and order `m` (see the module docstring).  Everything in `Valid` except `Valid.transfer`;
(S3) is then either assumed (`Valid`) or derived at a forbidden or bounded overlap (`TheoremA/SoftTransfer.lean`).  Nothing in `PreValid` mentions the constant `cs.Λ`. -/
structure PreValid (cs : ChainConsts) (h : ℝ) (m : ℕ) : Prop where
  h_pos : 0 < h
  P_pos : 1 ≤ D.P
  jj0 : D.jj 0 = 0
  jj_mono : ∀ p < D.P, D.jj p < D.jj (p + 1)
  jj_last : D.jj D.P = D.NR - 1
  s0_cases : D.s0 = 0 ∨ D.s0 = 1
  /-- (SM1)--(SM3) for the model ladder of every patch (`def:eng-ladder`). -/
  ladder : ∀ p ∈ Icc 1 D.P, SymplecticLadder (1 / 2) (D.dd p) (D.pp p) (D.qq p) (D.PiP p) (D.PiM p) (D.wf p) (D.ω p)
  /-- all patches have the same Wronskian modulus `omega_*`. -/
  omega_eq : ∀ p ∈ Icc 1 D.P, |D.ω p h| = |D.ω 1 h|
  /-- the common operator: bond and diagonal of every patch ladder agree with `A, Q` on the window. -/
  A_eq : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (-1 : ℤ) D.NR, ladderA (D.dd p) (D.pp p) (1 / 2) h k = D.A k
  Q_eq : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (0 : ℤ) D.NR, ladderQ (D.qq p) (1 / 2) h k = D.Q k
  /-- hard edge (`s0 = 0`): `A_{-1} = 0`, `D_-(u_0) = 0`, annihilation `Pi_-(u_0) w^{(1)}_0 = 0` (eq:eng-annih). -/
  A_hard : D.s0 = 0 → D.A (-1) = 0
  D_hard : D.s0 = 0 → Dm (D.dd 1) (1 / 2 * h) h = 0
  annih : D.s0 = 0 → colMul (D.PiM 1 (1 / 2 * h) h) (D.wf 1 0 (1 / 2 * h) h) = 0
  /-- positivity and monotonicity of the envelopes (`W` non-decreasing up to `C_E`). -/
  M_pos : ∀ j ∈ Icc (0 : ℤ) D.NR, 0 < D.M j
  W_pos : ∀ j ∈ Icc (0 : ℤ) D.NR, 0 < D.W j
  W_mono : ∀ k ∈ Icc (0 : ℤ) D.NR, ∀ j ∈ Icc (0 : ℤ) D.NR, k ≤ j → D.W k ≤ cs.CE * D.W j
  ρ_nonneg : ∀ k, 0 ≤ D.ρ k
  ρt_pos : ∀ k : ℤ, 0 ≤ k → 0 < D.ρt k
  /-- (S1) via `eq:eng-UC1`: `|F_cas| >= c_-` on the window of each patch. -/
  cas_lb : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (max (D.jj (p - 1)) 0) (D.jj p + 1),
    cs.cm ≤ |Fcas (D.pp p) (D.AA p) (D.BB p) (D.PiM p) (((k : ℝ) + 1 / 2) * h + h / 2) h|
  /-- (R) `eq:eng-UC1`: the defect bounds `|A^tot| <= K_D h^{m+1} rho`, `|B^tot| <= K_D h^{m+1} rho~` (output of `thm:eng-corr`). -/
  defect0 : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (eqLo D.s0 D.jj p) (D.jj p),
    |defectRow (D.pp p) (D.qq p) (D.AA p) (D.BB p) (D.PiP p) (D.PiM p) (((k : ℝ) + 1 / 2) * h) h 0|
      ≤ cs.KD * h ^ (m + 1) * D.ρ k
  defect1 : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (eqLo D.s0 D.jj p) (D.jj p),
    |defectRow (D.pp p) (D.qq p) (D.AA p) (D.BB p) (D.PiP p) (D.PiM p) (((k : ℝ) + 1 / 2) * h) h 1|
      ≤ cs.KD * h ^ (m + 1) * D.ρt k
  /-- (S2) bounds on the corrector rows: `|A| <= K_A`, `|h B rho/rho~| <= K_B`. -/
  A_bd : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (max (D.jj (p - 1)) 0) (D.jj p + 1),
    |D.AA p (((k : ℝ) + 1 / 2) * h) h| ≤ cs.KA
  B_bd : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (max (D.jj (p - 1)) 0) (D.jj p + 1),
    |h * D.BB p (((k : ℝ) + 1 / 2) * h) h| * (D.ρ k / D.ρt k) ≤ cs.KB
  /-- (S2) envelopes of the model pairs: `|w^{(1)}| <= K_w W M`, `|w^{(2)}| <= K_w W^{-1} M`, and the scaled derivative
  components `rho~ |w~^{(alpha)}| <= K_w rho W^{+-1} M`. -/
  env : ∀ p ∈ Icc 1 D.P, ∀ k ∈ Icc (max (D.jj (p - 1)) 0) (D.jj p + 1),
    |D.wf p 0 (((k : ℝ) + 1 / 2) * h) h 0| ≤ cs.Kw * D.W k * D.M k ∧
    |D.wf p 1 (((k : ℝ) + 1 / 2) * h) h 0| ≤ cs.Kw * (D.W k)⁻¹ * D.M k ∧
    D.ρt k * |D.wf p 0 (((k : ℝ) + 1 / 2) * h) h 1| ≤ cs.Kw * D.ρ k * D.W k * D.M k ∧
    D.ρt k * |D.wf p 1 (((k : ℝ) + 1 / 2) * h) h 1| ≤ cs.Kw * D.ρ k * (D.W k)⁻¹ * D.M k

/-- **(S3)** at the overlap bond `j_p` with constant `Λ`: the transfer matrix `M_p = transMat p` of the overlap `p, p+1` is `Λ`-bounded and its off-diagonal entries are weighted by `W(j_p)^{±2}`. -/
def TransferAtΛ (Λ h : ℝ) (p : ℕ) : Prop :=
  Λ⁻¹ ≤ |(transMat (D.phi h 0) (D.phi h 1) D.jj p).det| ∧
    |transMat (D.phi h 0) (D.phi h 1) D.jj p 0 0| ≤ Λ ∧
    |transMat (D.phi h 0) (D.phi h 1) D.jj p 1 1| ≤ Λ ∧
    |transMat (D.phi h 0) (D.phi h 1) D.jj p 0 1| ≤ Λ * (D.W (D.jj p) ^ 2)⁻¹ ∧
    |transMat (D.phi h 0) (D.phi h 1) D.jj p 1 0| ≤ Λ * D.W (D.jj p) ^ 2

/-- (S3) at the overlap `p` with the constant `cs.Λ`. -/
def TransferAt (cs : ChainConsts) (h : ℝ) (p : ℕ) : Prop := D.TransferAtΛ cs.Λ h p

/-- The hypotheses of `thm:eng-volterra` for the chain, at step `h` and order `m`: `PreValid` and the transfer condition (S3) at every overlap
(`transfer`: `Lambda`-bounded, weighted by `W^{+-2}`; derived from chart-level inputs at the overlaps of a soft-edge chain in `TheoremA/SoftTransfer.lean`). -/
structure Valid (cs : ChainConsts) (h : ℝ) (m : ℕ) : Prop extends D.PreValid cs h m where
  /-- (S3) transfer matrices of the overlaps (`Lambda`-bounded, weighted by `W^{+-2}`). -/
  transfer : ∀ p, 1 ≤ p → p < D.P → D.TransferAt cs h p

/-- The conclusion of `thm:eng-volterra` for the chain (as in `volterra_multi`, with `K = (K_A+K_B) K_w`, `eps = 2 K_D K_w h^m`):
the global bound `|psi_j - psi-hat_{p,j}| <= C eps Theta W_j M_j` on every patch window, single-valuedness on overlaps,
and every row covered by some patch. -/
def Concl (cs : ChainConsts) (h : ℝ) (m : ℕ) (ψ : ℤ → ℝ) : Prop :=
  (∀ p ∈ Icc 1 D.P, ∀ j ∈ Icc (eqLo D.s0 D.jj p) (D.jj p + 1),
    |ψ j - D.psiHat h p j| ≤ mvC cs.cm cs.CE ((cs.KA + cs.KB) * cs.Kw) cs.Λ D.P
      * (2 * cs.KD * cs.Kw * h ^ m * D.theta h) * D.W j * D.M j) ∧
  (∀ p, 1 ≤ p → p < D.P → ∀ j ∈ Icc (D.jj p) (D.jj p + 1), D.psiHat h p j = D.psiHat h (p + 1) j) ∧
  (∀ j ∈ Icc (0 : ℤ) D.NR, ∃ p ∈ Icc 1 D.P,
    |ψ j - D.psiHat h p j| ≤ mvC cs.cm cs.CE ((cs.KA + cs.KB) * cs.Kw) cs.Λ D.P
      * (2 * cs.KD * cs.Kw * h ^ m * D.theta h) * D.W j * D.M j)

/-- **Statement of the engine for the chain** (`thm:eng-volterra`(a)+(b)): for every solution `psi` of the Jacobi recurrence on
`[s0, NR-1]` with the seed of the first comparison pair and `eps Theta <= c_*`, the conclusion `Concl` holds.  Proved later (Layer 1, L1.1);
the shared-ladder case is `JE.ladder_pair_stability`. -/
def Stability (cs : ChainConsts) (h : ℝ) (m : ℕ) : Prop :=
  D.Valid cs h m → ∀ ψ : ℤ → ℝ,
    (∀ k ∈ Icc D.s0 (D.NR - 1), Lh h D.A D.Q ψ k = 0) →
    (∀ j ∈ Icc (0 : ℤ) D.s0, ψ j = D.phi h 0 1 j) →
    2 * cs.KD * cs.Kw * h ^ m * D.theta h ≤ mvCstar cs.cm cs.CE ((cs.KA + cs.KB) * cs.Kw) →
    D.Concl cs h m ψ

end LadderData

end FormalResearch.JacobiEigenvectors.Charts
