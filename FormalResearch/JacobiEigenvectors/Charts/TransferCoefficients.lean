module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily
public import FormalResearch.JacobiEigenvectors.Charts.LadderChain
public import FormalResearch.JacobiEigenvectors.Charts.Regularity

/-!
# Paper J, charts: the transfer coefficients of a chart (inputs (I2) of the one-step criterion)

Source: Paper J `app_thmB.tex`, "(I2) and the changed coefficient: bulk charts" and "(I2): soft charts"; `thmB.tex` `def:thb-inputs` (I2),
`eq:thb-parity`.  Consumer: `JB.Chart.Ok` (`transfer`, `t12_lb`, `α_lb`, `schur_*`) via `TheoremB.PropThbInputs`.

For one chart (a patch of a ladder chain), at orders `m` and `m+1` on the **same** ladder, `TransferInputs` records the facts about the
*coefficients* that the one-step criterion needs and Layer 2 does not provide:

* the sampled transfer coefficients are the entries of `Pi_+` of the patch: `t_{11} = Pi_{+,00}`, `t_{12} = Pi_{+,01}`, `omega_n = D_+(u_n)`
  (the exact one-step transfer `omega_n y_{n+1} = t_11 y_n + t_12 y~_n` is then the first row of (SM2), `SymplecticLadder.shift_up`: Layer 3, easy);
* jointly `C^2` in `(u, X)` with all of `phi, d_u phi, d_X phi, d_u d_X phi` bounded, uniformly in `h` and `mu` (`reg_*`; Layer 4: `lem:smo-budget` (b)--(e), `lem:cha-weber-coord`, `lem:cha-PCcoord`),
  for `t_11, t_12`, the order-`(m+1)` corrector row `A^{[m+1]}, B^{[m+1]}` and the changed coefficient `kappa_m`;
* `|t_12| >= c_T` (`Pi_{+,12} = -V_0/P_0 + O(h)`, `V_0 > 0`; `lem:tha-collar` (2) for the soft halves) and `alpha = A^{[m+1]} - h B^{[m+1]} t_11/t_12 >= c_alpha` (`alpha = g_0 + O(h)`);
* the parity identity `eq:thb-parity` between the rows of orders `m` and `m+1` (`parity_A`, `parity_B`): the structural fact that `def:thb-inputs` omitted
  (finding F3 of the previous round, restated in `PLAN.md`);
* `0 < omega <= omega_max` (`omega_n = sqrt(s_n) <= sqrt L` in the bulk, `1` at a soft edge).

The paper states the five Schur-multiplier bounds (for `1/alpha`, `B/(t_12 alpha)`, `1/t_12`, `t_11/t_12`, `kappa_m`) as the hypothesis; here the *primitive* `C^2` facts are the
hypothesis and the five Schur bounds are derived in Layer 3 (`jb_schur_of_C2`, `jb_schur_inv`, `jb_schur_div`; closure of `FullC2` under products and quotients is the only new analysis).
This is *weaker* than the paper's (I2) hypothesis in form but the same in content, and makes the structure minimal.

Satisfiability: as `BulkWeberChart` (no toy: the coefficients are those of a Weber / PC ladder).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Engine

/-- `epsilon_m = m mod 2`. -/
def epsM (m : ℕ) : ℝ := ((m % 2 : ℕ) : ℝ)

/-- Transfer coefficients of patch `patch` of the chains `chain0` (order `m`) and `chain1` (order `m+1`) on the rectangle `[ulo mu, uhi mu] x [Jlo mu, Jhi mu]` (the rectangle may depend on `mu`, e.g. the soft collar). -/
structure TransferInputs {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (P : Set Par) (Jlo Jhi : Par → ℝ) (m : ℕ)
    (chain0 chain1 : Par → ℝ → ℕ → LadderData) (patch : ℕ) where
  N0 : ℕ
  ulo : Par → ℝ
  uhi : Par → ℝ
  cT : ℝ
  cα : ℝ
  S : ℝ
  ωmax : ℝ
  /-- the changed coefficient `kappa_m(u; mu, X, N)` (`g_m` for even `m`, `B_m` for odd `m`). -/
  κ : Par → ℝ → ℕ → ℝ → ℝ
  consts_pos : (∀ μ ∈ P, ulo μ ≤ uhi μ ∧ Jlo μ ≤ Jhi μ) ∧ 0 < cT ∧ 0 < cα ∧ 0 ≤ S ∧ 0 < ωmax
  /-- the two orders live on the same ladder (same `Pi_+`, same model pair): only the corrector rows differ. -/
  same_ladder : ∀ μ ∈ P, ∀ X ∈ Set.Icc (Jlo μ) (Jhi μ), ∀ N, N0 ≤ N →
    (chain0 μ X N).PiP patch = (chain1 μ X N).PiP patch ∧ (chain0 μ X N).wf patch = (chain1 μ X N).wf patch ∧
      (chain0 μ X N).dd patch = (chain1 μ X N).dd patch
  /-- `eq:thb-parity`: `A^{[m+1]} - A^{[m]} = (1 - eps_m) h^m kappa_m`, `h (B^{[m+1]} - B^{[m]}) = eps_m h^m kappa_m` on the rectangle. -/
  parity_A : ∀ μ ∈ P, ∀ X ∈ Set.Icc (Jlo μ) (Jhi μ), ∀ N, N0 ≤ N → ∀ u ∈ Set.Icc (ulo μ) (uhi μ),
    (chain1 μ X N).AA patch u (F.step N) - (chain0 μ X N).AA patch u (F.step N)
      = (1 - epsM m) * F.step N ^ m * κ μ X N u
  parity_B : ∀ μ ∈ P, ∀ X ∈ Set.Icc (Jlo μ) (Jhi μ), ∀ N, N0 ≤ N → ∀ u ∈ Set.Icc (ulo μ) (uhi μ),
    F.step N * ((chain1 μ X N).BB patch u (F.step N) - (chain0 μ X N).BB patch u (F.step N))
      = epsM m * F.step N ^ m * κ μ X N u
  /-- `C^2` bounds (Layer 4): `t_11, t_12`, `A^{[m+1]}`, `B^{[m+1]}`, `kappa_m`. -/
  reg_t11 : ∀ μ ∈ P, ∀ N, N0 ≤ N →
    BoundedC2 (fun u X => (chain1 μ X N).PiP patch u (F.step N) 0 0) (ulo μ) (uhi μ) (Jlo μ) (Jhi μ) S
  reg_t12 : ∀ μ ∈ P, ∀ N, N0 ≤ N →
    BoundedC2 (fun u X => (chain1 μ X N).PiP patch u (F.step N) 0 1) (ulo μ) (uhi μ) (Jlo μ) (Jhi μ) S
  reg_A1 : ∀ μ ∈ P, ∀ N, N0 ≤ N → BoundedC2 (fun u X => (chain1 μ X N).AA patch u (F.step N)) (ulo μ) (uhi μ) (Jlo μ) (Jhi μ) S
  reg_B1 : ∀ μ ∈ P, ∀ N, N0 ≤ N → BoundedC2 (fun u X => (chain1 μ X N).BB patch u (F.step N)) (ulo μ) (uhi μ) (Jlo μ) (Jhi μ) S
  reg_κ : ∀ μ ∈ P, ∀ N, N0 ≤ N → BoundedC2 (fun u X => κ μ X N u) (ulo μ) (uhi μ) (Jlo μ) (Jhi μ) S
  /-- `|t_12| >= c_T` and `alpha >= c_alpha` on the rectangle. -/
  t12_lb : ∀ μ ∈ P, ∀ X ∈ Set.Icc (Jlo μ) (Jhi μ), ∀ N, N0 ≤ N → ∀ u ∈ Set.Icc (ulo μ) (uhi μ),
    cT ≤ |(chain1 μ X N).PiP patch u (F.step N) 0 1|
  alpha_lb : ∀ μ ∈ P, ∀ X ∈ Set.Icc (Jlo μ) (Jhi μ), ∀ N, N0 ≤ N → ∀ u ∈ Set.Icc (ulo μ) (uhi μ),
    cα ≤ (chain1 μ X N).AA patch u (F.step N) - F.step N * (chain1 μ X N).BB patch u (F.step N)
      * (chain1 μ X N).PiP patch u (F.step N) 0 0 / (chain1 μ X N).PiP patch u (F.step N) 0 1
  /-- `0 < omega_n = D_+(u_n) <= omega_max` at the sampled rows. -/
  omega_pos_le : ∀ μ ∈ P, ∀ X ∈ Set.Icc (Jlo μ) (Jhi μ), ∀ N, N0 ≤ N → ∀ k : ℤ, ulo μ ≤ uNode (F.step N) k → uNode (F.step N) k ≤ uhi μ →
    0 < Dp ((chain1 μ X N).dd patch) (uNode (F.step N) k) (F.step N) ∧
      Dp ((chain1 μ X N).dd patch) (uNode (F.step N) k) (F.step N) ≤ ωmax

end FormalResearch.JacobiEigenvectors.Charts
