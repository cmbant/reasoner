module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkPhase
public import FormalResearch.JacobiEigenvectors.TheoremA.Count
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkPhasesKappa
public import FormalResearch.JacobiEigenvectors.TheoremA.MonotoneAction

/-!
# Paper J, Layer 2: the bulk windows (`lem:smo-bulkphase` (2)--(3), L2.S1; what is proved and what is not)

Source: Paper J `app_thmA.tex`, `lem:smo-bulkphase` ((1) phases, (2) Casoratian, (3) windows, (4) all orders) and `lem:tha-count`
(`propThaCount`, `TheoremA/Count.lean`); `thm:smo-BSr`, "Location and labels".

## The chain of lemmas of `lem:smo-bulkphase` and its status (checked step by step against the paper)

`[P]` proved in Lean here or in a cited module, `[F]` the frozen field `BulkPhaseInputs.casoratian` (resp. a replacement by it), `[X]` blocked by a missing input, named.

* **(4) all orders** `[F]`: the Casoratian of the two *comparison* sequences is `pre [sin(Sigma/h - pi/2) + O(h^m)]`, `pre >= c0 h^{1/2}` (corrected field, round 5).
  **`bulk_exact_cas`** `[P]` (here, from `bulk_cas_core` of `BulkPhase.lean`, `bulkSolutionBound_of_one_le` = `prop:tha-W` (1), and the engine): the same for the *exact* Casoratian
  `C(X) = -a b D(X)` of the exact left and right edge solutions `psi^L = a p`, `psi^R = b q` (`a = psi-hat^L_0`, `b = psi-hat^R_0`, `D = casD`), for **every** `X` of the block
  (the paper's "by `prop:tha-W` (1), as in (2), `C(X)` has the same form", `eq:smo-bulkphase`).
* **(3), first half: every zero of `D` (in particular every eigenvalue) is in a window** `[P]` `bulk_zero_window`: `|S_0(X) - pi h (j + 1/2)| <= C h^2` for some integer `j >= 0`
  (the paper's (i) of `lem:tha-count`; proof: `bulk_exact_cas` at a zero, `exists_int_near`, `Sigma - S_0 = O(h^2)` from `Sigma_one`, `Sigma_zero`, `Sigma_bdd`).
* **(3), (ii) the sign of `D` at the nodes** `[P]` `bulk_node_sign`: at `S_0(X) = pi h k` one has `sign D = (-1)^k` (so `sigma = +1` in the frozen (ii); `D = -C(p,q)` is minus the
  `C`-Casoratian, `C = pre sin(Sigma/h - pi/2) = -pre (-1)^k cos(O(h))`).
* **(3) counting** `[P]` `bulk_count`: `propThaCount` on `I = [Jlo, Jhi]`, `Phi = S_0^{(t)}`, `eps = C h^2`: at most one zero of `D` per window, exactly one when the bracketing interval
  lies in `S_0(I)`.  No unproved hypothesis remains besides the named structures (`BulkPhaseInputs`, the chart fields, `ParabolicCylinderFacts`, `StdAssump`): the two former inputs are
  **(a) `S_0^{(t)}` strictly decreasing on the block**, `bulk_actionS0_strictAnti` (`TheoremA/MonotoneAction.lean`: the integrand is pointwise antitone in `X` and strictly so on a set of positive
  measure; no differentiation under the integral), and **(b) the sign of `kappa'` at a zero in a window** (`(iii)` of `lem:tha-count`), `bulk_kappa_sign` (below).
* **(1) phases** `[P]` `bulk_phase_left` (`TheoremA/BulkPhases.lean`, with `TheoremA/BulkPhasesPC.lean`): `psi-hat^L_n = rho [cos(Theta_L(u_n)/h - pi/4) + O(h)]`, `rho >= c1 h^{1/4}`, on every
  row of the overlap; the right chart is the mirror chart, so the same theorem gives the right phase.  `exact_phase_row` (`TheoremA/BulkPhasesKappa.lean`) transfers it to the exact edge solution
  (`prop:tha-W` (1)).  Two chart fields were added (findings F-S1-1, F-S1-4 below); the derivative of `phase_osc` (F-S1-2) is derived, not assumed.
* **(3)(iii) the sign of `kappa'`** `[P]` `bulk_kappa_sign`: for every `Cw`, for `N` large, positive bonds, `|S_0(X) - pi h (k + 1/2)| <= Cw h^2` and `p_n = kappa' q_n` for all `n`:
  `sign kappa' = sign (-1)^k`.  Proof: (1) for the exact left and mirror solutions at two consecutive overlap rows `n, n+1`; `Theta_L(u) + Theta_R(L - u) = S_0` (`thetaL_add_mirror`) gives
  `alpha_n + beta_{N-n} = pi k + O(h)`, hence `cos beta = (-1)^k cos alpha + O(h)`; `theta_margin` makes `Theta_L` advance by an angle in `[theta_1, pi - theta_1]` per step, so
  `cos^2 alpha_n + cos^2 alpha_{n+1} >= 1 - cos theta_1`; at a row with `cos^2 alpha >= eps/2`, `(-1)^k psi^L_n psi^R_n = rho_L rho_R (cos^2 alpha + O(h)) > 0`, and `psi^L_n psi^R_n = kappa' a b q_n^2`.
* **(3), the labels `k' = k`** `[X]`: `BulkWindowLabels` (`BulkPhase.lean`).  The windows of a block fix `k'` only up to a constant shift (the counting gives a contiguous range); the
  anchor is the soft-edge window `0` (`PropThaW2` (3), (4); `L2.C7`) together with the count "no eigenvalue above window `0` of the upper soft edge".  `bulk_kappa_sign` is stated with the
  *window* label `k` of `S_0`, which is what `propThaCount` uses; it does not identify `k` with the eigenvalue index.
* **(2) Casoratian with `sin theta`** `[not needed]`: `a rho_L rho_R [sin theta sin(S_0/h - pi/2) + O(h)]` is replaced in the formalisation by (4) with the positive prefactor `pre` (which absorbs
  `a rho_L rho_R sin theta (1 + O(h))`).  The ratio `rho(u_{n+1}) = rho(u_n)(1 + O(h))` and the continuity of `rho` in `X` (used only in the `sin theta` form) are not proved.

## Findings (round 6; the frozen statements are not edited here)

* **F-S1-1 confirmed and refined** (`BulkWeberChart` lacks the leading corrector, so the phase of `psi-hat` is not determined): added the field `corr_lead` (`Charts/BulkWeber.lean`): on the overlap rows
  the row `(A^{[m]}(u_k, h^2), h B)` equals `(g_0(u_k) + O(h^2), O(h))` with `g_0 = sqrt(E_0) / u` bounded below, and `hB = O(h)` (the paper's `lem:smo-bulkphase` (1) uses both).
* **F-S1-2 refined (no field)**: the derivative of `phase_osc` (DLMF 12.10.19) is not needed as an input: the envelope bound `E_Web M_Web = O(h^{1/4})` and the phase are obtained from the value expansion
  `phase_osc` by Landau interpolation on a window of length `1/mu` (`TheoremA/BulkPhasesPC.lean`: `landau_deriv`, `Env2`, `wronsk_le_Env2`, `phase_pack`), together with the Wronskian.
* **F-S1-3 (Sturm alternative)**: a Sturm oscillation theorem for Jacobi matrices is not in Mathlib; the paper's route via (1) was taken instead and gives `bulk_kappa_sign`.
* **F-S1-4 (new)**: (iii) needs a *uniform* margin `theta_1 > 0` of the phase increment per step on the overlap, i.e. `|X - B_0| <= (1 - eps) 2 sqrt(E_0)` on `[c', c]` uniformly in `(mu, X)`.  It is not derivable
  from `overlap_in_well` (which only says `T > 0` with margin `sigma` in the endpoints); added as the field `theta_margin`, a statement of `lem:tha-geom`/`prop:cha-halfrow` (compactness of the block).

## Differences from the paper

The window width is `C h^2` with `C` explicit from the constants of `BulkPhaseInputs`; the integer window index is `j : N` (the paper's `k >= 0`); positive bonds are a hypothesis (as in `bulk_eigen_sin`).
The paper's `I` is the interval `J_nu`; here `I = [Jlo, Jhi]` of the block.  `lem:smo-bulkphase` (3) is for all `h <= h_0`; here for `N >= N_1` and `h <= h_0`.

## Not formalised

(2) in the form with `sin theta`, (3) the labels `k' = k` (soft-edge window `0` anchor): see above.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.Engine

/-- The chain of a bulk chart has at most `N` rows (its last row lies below `c < L`, while `u_{N+1} = L + h/2`). -/
lemma chain_NR_le_N {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P)
    (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N) :
    (C.chain p X N).NR ≤ (N : ℤ) := by
  obtain ⟨-, -, -, hNRc, -⟩ := C.shape p hp X hX N hN
  obtain ⟨-, -, -, hcσ, -, -, -, -, -, -⟩ := C.consts_pos
  have hst : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  have hL : G.step N * ((N : ℝ) + 1) = G.L := step_mul_succ G N
  by_contra hcon
  rw [not_le] at hcon
  have h1 : uNode (G.step N) ((N : ℤ) + 1) ≤ uNode (G.step N) ((C.chain p X N).NR) :=
    uNode_le_of_le hst.le (by omega)
  have e : uNode (G.step N) ((N : ℤ) + 1) = G.L + G.step N / 2 := by
    unfold uNode
    push_cast
    linear_combination hL
  have hσpos : 0 < C.σ := C.consts_pos.2.2.1
  linarith

/-- Reflection of a solution on the rows `1 .. N` (the backward solution `q` of `lem:tha-count`): `k ↦ f (N - k)` solves the mirror recurrence on the rows `0 .. N-1`. -/
lemma lop_mirror_part {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : ℝ) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j ≤ (N : ℤ) → Lop (F.bondA μ N) (F.diagQ μ N X) f j = 0)
    (k : ℤ) (hk0 : 0 ≤ k) (hkN : k < (N : ℤ)) :
    Lop ((mirrorFamily F).bondA μ N) ((mirrorFamily F).diagQ μ N X) (fun i => f ((N : ℤ) - i)) k = 0 := by
  have h := hf ((N : ℤ) - k) (by omega) (by omega)
  unfold Lop at h ⊢
  simp only [bondA_mirror, diagQ_mirror]
  have e1 : (N : ℤ) - 1 - k = (N : ℤ) - k - 1 := by ring
  have e2 : (N : ℤ) - 1 - (k - 1) = (N : ℤ) - k := by ring
  have e3 : (N : ℤ) - (k + 1) = (N : ℤ) - k - 1 := by ring
  have e4 : (N : ℤ) - (k - 1) = (N : ℤ) - k + 1 := by ring
  rw [e1, e2, e3, e4]
  linarith [h]

section Windows

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {K : Set Par} {t0 : ℝ}
  {Jlo Jhi : ℝ} {M : ℕ} {U V : ℝ → ℝ → ℝ}
  {CL : BulkWeberChart F P Jlo Jhi (max M 1) U V} {CR : BulkWeberChart (mirrorFamily F) P Jlo Jhi (max M 1) U V}

/-- **The exact Casoratian of the exact edge solutions at every energy of the block** (`lem:smo-bulkphase` (4) for `C(X)`, by `prop:tha-W` (1) as in (2)):
with `a = psi-hat^L_0 > 0`, `b = psi-hat^R_0 > 0` and `D = casD` (`D = -C(p, q)`, `p`, `q` the normalised forward and backward solutions), `-a b D(X) = pre sin(Sigma/h - pi/2) + O(h^m) pre`,
`pre >= c0 h^{1/2}`. -/
theorem bulk_exact_cas (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR)
    (hP : ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, (μ, t) ∈ P)
    (hcoup : CR.c = F.L - CL.c' ∧ CR.c' = F.L - CL.c) (r : ℕ) (hr : StdAssump F P (max M 1 / 2) r) :
    ∃ Kc c0 h0 : ℝ, 0 < c0 ∧ 0 < h0 ∧ ∃ N1 : ℕ, 1 ≤ N1 ∧ ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, ∀ N : ℕ, N1 ≤ N → F.step N ≤ h0 →
      (∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA (μ, t) N n) → ∀ X ∈ Set.Icc Jlo Jhi,
        0 < CL.psiHatL (μ, t) X N 0 * CR.psiHatL (μ, t) X N 0 ∧
        ∃ pre : ℝ, c0 * Real.sqrt (F.step N) ≤ pre ∧
          |CL.psiHatL (μ, t) X N 0 * CR.psiHatL (μ, t) X N 0 * casD F (μ, t) N X
            + pre * Real.sin (bulkPhaseSum PI μ t X N / F.step N - Real.pi / 2)| ≤ Kc * F.step N ^ (max M 1) * pre := by
  classical
  obtain ⟨Kc, c0, h0, hc0, hh0, N1, hN1L, hN1R, hcore⟩ := bulk_cas_core PI hP hcoup r hr
  refine ⟨Kc, c0, h0, hc0, hh0, max N1 1, le_max_right _ _, ?_⟩
  intro μ hμ t ht N hN hstep hpos X hX
  have hNN1 : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hN1' : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hp : (μ, t) ∈ P := hP μ hμ t ht
  have hCN1 : CL.N0 ≤ N := le_trans hN1L hNN1
  have hCN2 : CR.N0 ≤ N := le_trans hN1R hNN1
  have hα : 0 < CL.psiHatL (μ, t) X N 0 := by
    rw [show CL.psiHatL (μ, t) X N 0 = (CL.chain (μ, t) X N).phi (F.step N) 0 1 0 from
      psiHat_one_eq (CL.chain (μ, t) X N) (F.step N) 0]
    exact CL.seed_pos _ hp X hX N hCN1
  have hβ : 0 < CR.psiHatL (μ, t) X N 0 := by
    rw [show CR.psiHatL (μ, t) X N 0 = (CR.chain (μ, t) X N).phi ((mirrorFamily F).step N) 0 1 0 from
      psiHat_one_eq (CR.chain (μ, t) X N) ((mirrorFamily F).step N) 0]
    exact CR.seed_pos _ hp X hX N hCN2
  refine ⟨mul_pos hα hβ, ?_⟩
  set α := CL.psiHatL (μ, t) X N 0 with hαdef
  set β := CR.psiHatL (μ, t) X N 0 with hβdef
  have hNRL := chain_NR_le_N CL (μ, t) hp X hX N hCN1
  have hNRR := chain_NR_le_N CR (μ, t) hp X hX N hCN2
  have hJL : JacSol F (μ, t) N X (CL.chain (μ, t) X N).NR (fun n => α * pZ F (μ, t) N X n) := by
    intro n hn0 hn1
    have h := Lop_pZ hpos hN1' X n hn0 (by omega)
    rw [Lop_smul]
    exact mul_eq_zero_of_right _ h
  have hJR : JacSol (mirrorFamily F) (μ, t) N X (CR.chain (μ, t) X N).NR (fun i => β * qZ F (μ, t) N X ((N : ℤ) - i)) := by
    intro n hn0 hn1
    rw [show (fun i => β * qZ F (μ, t) N X ((N : ℤ) - i)) = fun i => β * (fun j => qZ F (μ, t) N X j) ((N : ℤ) - i) from rfl,
      Lop_smul, lop_mirror_part F (μ, t) N X (qZ F (μ, t) N X)
        (fun j hj1 hjN => Lop_qZ hpos hN1' X j hj1 hjN) n hn0 (by omega), mul_zero]
  have hseedL : (fun n => α * pZ F (μ, t) N X n) 0 = α := by
    show α * pZ F (μ, t) N X 0 = α
    rw [pZ_zero, mul_one]
  have hseedR : (fun i => β * qZ F (μ, t) N X ((N : ℤ) - i)) 0 = β := by
    show β * qZ F (μ, t) N X ((N : ℤ) - 0) = β
    rw [sub_zero, qZ_N, mul_one]
  obtain ⟨pre, hpre1, n, hn0, hn1, hcn⟩ := hcore μ hμ t ht N hNN1 hstep X hX _ _ hJL hseedL hJR hseedR
  refine ⟨pre, hpre1, ?_⟩
  beta_reduce at hcn
  -- the exact Casoratian at the row `n` is `-a b` times `cas p q n = cas p q 0 = D`
  have hcas := green_cas_const (F.bondA (μ, t) N) (F.entryB (μ, t) N) X (N : ℤ) (pZ F (μ, t) N X) (qZ F (μ, t) N X)
    (fun i hi => Lop_pZ hpos hN1' X i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2)
    (fun i hi => Lop_qZ hpos hN1' X i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2)
  have hcn' : cas (F.bondA (μ, t) N) (pZ F (μ, t) N X) (qZ F (μ, t) N X) n = casD F (μ, t) N X := by
    rw [casD_eq_cas]
    exact hcas n (Finset.mem_Icc.2 ⟨hn0, by omega⟩)
  have e1 : (N : ℤ) - ((N : ℤ) - (n + 1)) = n + 1 := by ring
  have e0 : (N : ℤ) - ((N : ℤ) - n) = n := by ring
  rw [e1, e0] at hcn
  have hexp : F.bondA (μ, t) N n * (α * pZ F (μ, t) N X n * (β * qZ F (μ, t) N X (n + 1))
        - α * pZ F (μ, t) N X (n + 1) * (β * qZ F (μ, t) N X n))
      = -(α * β * casD F (μ, t) N X) := by
    rw [← hcn']
    unfold cas
    ring
  rw [hexp] at hcn
  have : |α * β * casD F (μ, t) N X + pre * Real.sin (bulkPhaseSum PI μ t X N / F.step N - Real.pi / 2)|
      = |-(α * β * casD F (μ, t) N X) - pre * Real.sin (bulkPhaseSum PI μ t X N / F.step N - Real.pi / 2)| := by
    rw [← abs_neg]; congr 1; ring
  rw [this]
  exact hcn

/-- `S_0^{(t)}(X) >= 0` (the integrand `arccos` is nonnegative). -/
lemma actionS0_nonneg (F : SymbolFamily Par) (μ : Par) (X : ℝ) : 0 ≤ actionS0 F μ X := by
  unfold actionS0
  exact intervalIntegral.integral_nonneg F.L_pos.le (fun u _ => Real.arccos_nonneg _)

/-- `Sigma - S_0 = O(h^2)` on the block, from the field `Sigma_bdd` (`i = 0`) and `Sigma_one`, `Sigma_zero`. -/
lemma phase_sub_S0 (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR) :
    ∃ Cσ : ℝ, 0 ≤ Cσ ∧ ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, F.step N ≤ 1 →
      |bulkPhaseSum PI μ t X N - actionS0 F (μ, t) X| ≤ Cσ * F.step N ^ 2 := by
  obtain ⟨Cσ, hC0, hC⟩ := bulkSigmaBdd PI
  refine ⟨M * Cσ, by positivity, fun μ hμ t ht X hX N hh1 => ?_⟩
  have h := phaseSum_sub_zero PI Cσ hC0 μ hμ t ht X hX N (fun j hj => hC μ hμ t ht X hX j hj) hh1
  rw [PI.Sigma_zero μ hμ X hX t ht] at h
  exact h

/-- **(3), first half**: every zero of `D = casD` in the block (in particular every eigenvalue, `D` vanishes there) lies in a window: `|S_0(X) - pi h (j + 1/2)| <= C h^2`, `j in N`. -/
theorem bulk_zero_window (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR)
    (hP : ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, (μ, t) ∈ P)
    (hcoup : CR.c = F.L - CL.c' ∧ CR.c' = F.L - CL.c) (r : ℕ) (hr : StdAssump F P (max M 1 / 2) r) :
    ∃ C h0 : ℝ, 0 < C ∧ 0 < h0 ∧ ∃ N1 : ℕ, 1 ≤ N1 ∧ ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, ∀ N : ℕ, N1 ≤ N → F.step N ≤ h0 →
      (∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA (μ, t) N n) → ∀ X ∈ Set.Icc Jlo Jhi, casD F (μ, t) N X = 0 →
        ∃ j : ℕ, |actionS0 F (μ, t) X - Real.pi * F.step N * ((j : ℝ) + 1 / 2)| ≤ C * F.step N ^ 2 := by
  obtain ⟨Kc, c0, h0, hc0, hh0, N1, hN1, hmain⟩ := bulk_exact_cas PI hP hcoup r hr
  obtain ⟨Cσ, hCσ, hσ⟩ := phase_sub_S0 PI
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = Cσ + Real.pi / 2 * |Kc| + 1 := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hC]; have := Real.pi_pos; positivity
  refine ⟨C, min (min h0 1) (Real.pi / (4 * C)), hCpos, lt_min (lt_min hh0 one_pos) (div_pos Real.pi_pos (by positivity)),
    N1, hN1, ?_⟩
  intro μ hμ t ht N hN hstep hpos X hX hD0
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hh0' : F.step N ≤ h0 := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh1 : F.step N ≤ 1 := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhC : F.step N ≤ Real.pi / (4 * C) := hstep.trans (min_le_right _ _)
  obtain ⟨-, pre, hpre, hcas⟩ := hmain μ hμ t ht N hN hh0' hpos X hX
  rw [hD0, mul_zero, zero_add, abs_mul] at hcas
  have hprepos : 0 < pre := lt_of_lt_of_le (mul_pos hc0 (Real.sqrt_pos.mpr hst)) hpre
  rw [abs_of_pos hprepos] at hcas
  have hsin : |Real.sin (bulkPhaseSum PI μ t X N / F.step N - Real.pi / 2)| ≤ Kc * F.step N ^ (max M 1) := by
    have : pre * |Real.sin (bulkPhaseSum PI μ t X N / F.step N - Real.pi / 2)| ≤ pre * (Kc * F.step N ^ (max M 1)) := by
      nlinarith [hcas]
    exact le_of_mul_le_mul_left this hprepos
  have hsin' : |Real.sin (bulkPhaseSum PI μ t X N / F.step N - Real.pi / 2)| ≤ |Kc| * F.step N ^ (max M 1) :=
    hsin.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hst.le _))
  obtain ⟨j, hj⟩ := exists_int_near _ _ hsin'
  have hSig := hσ μ hμ t ht X hX N hh1
  -- `Sigma - pi h (j + 1/2) = h (Sigma/h - pi/2 - pi j)`
  have e : bulkPhaseSum PI μ t X N - Real.pi * F.step N * ((j : ℝ) + 1 / 2)
      = F.step N * (bulkPhaseSum PI μ t X N / F.step N - Real.pi / 2 - Real.pi * j) := by
    field_simp
    ring
  have hm1 : 1 ≤ max M 1 := le_max_right _ _
  have hpow : F.step N ^ (max M 1 + 1) ≤ F.step N ^ 2 := pow_le_pow_of_le_one hst.le hh1 (by omega)
  have hphase : |bulkPhaseSum PI μ t X N - Real.pi * F.step N * ((j : ℝ) + 1 / 2)| ≤ Real.pi / 2 * |Kc| * F.step N ^ 2 := by
    rw [e, abs_mul, abs_of_pos hst]
    calc F.step N * |bulkPhaseSum PI μ t X N / F.step N - Real.pi / 2 - Real.pi * j|
        ≤ F.step N * (Real.pi / 2 * (|Kc| * F.step N ^ (max M 1))) := mul_le_mul_of_nonneg_left hj hst.le
      _ = Real.pi / 2 * |Kc| * F.step N ^ (max M 1 + 1) := by ring
      _ ≤ Real.pi / 2 * |Kc| * F.step N ^ 2 :=
          mul_le_mul_of_nonneg_left hpow (by have := Real.pi_pos; positivity)
  have hS0 : |actionS0 F (μ, t) X - Real.pi * F.step N * ((j : ℝ) + 1 / 2)| ≤ C * F.step N ^ 2 := by
    calc _ = |(actionS0 F (μ, t) X - bulkPhaseSum PI μ t X N)
            + (bulkPhaseSum PI μ t X N - Real.pi * F.step N * ((j : ℝ) + 1 / 2))| := by ring_nf
      _ ≤ |actionS0 F (μ, t) X - bulkPhaseSum PI μ t X N|
            + |bulkPhaseSum PI μ t X N - Real.pi * F.step N * ((j : ℝ) + 1 / 2)| := abs_add_le _ _
      _ ≤ Cσ * F.step N ^ 2 + Real.pi / 2 * |Kc| * F.step N ^ 2 := by
          refine add_le_add ?_ hphase
          rw [abs_sub_comm]; exact hSig
      _ ≤ C * F.step N ^ 2 := by rw [hC]; nlinarith [sq_nonneg (F.step N)]
  -- `j >= 0`
  have hj0 : 0 ≤ j := by
    by_contra hneg
    rw [not_le] at hneg
    have hj1 : (j : ℝ) ≤ -1 := by exact_mod_cast (by omega : j ≤ -1)
    have hS := actionS0_nonneg F (μ, t) X
    have h1 : Real.pi * F.step N / 2 ≤ |actionS0 F (μ, t) X - Real.pi * F.step N * ((j : ℝ) + 1 / 2)| := by
      rw [abs_of_nonneg (by nlinarith [mul_pos Real.pi_pos hst])]
      nlinarith [mul_pos Real.pi_pos hst]
    have h2 : C * F.step N ≤ Real.pi / 4 := by
      have := mul_le_mul_of_nonneg_left hhC hCpos.le
      rw [mul_div_assoc'] at this
      calc C * F.step N ≤ C * (Real.pi / (4 * C)) := mul_le_mul_of_nonneg_left hhC hCpos.le
        _ = Real.pi / 4 := by field_simp
    have h3 : C * F.step N ^ 2 ≤ Real.pi * F.step N / 4 := by nlinarith [h2, hst]
    nlinarith [h1, hS0, h3, mul_pos Real.pi_pos hst]
  refine ⟨j.toNat, ?_⟩
  have hjc : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj0
  rw [hjc]
  exact hS0

/-- **(3), (ii)**: at a node `S_0(X) = pi h k` the sign of `D = casD` is `(-1)^k` (`sigma = +1`). -/
theorem bulk_node_sign (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR)
    (hP : ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, (μ, t) ∈ P)
    (hcoup : CR.c = F.L - CL.c' ∧ CR.c' = F.L - CL.c) (r : ℕ) (hr : StdAssump F P (max M 1 / 2) r) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ N1 : ℕ, 1 ≤ N1 ∧ ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, ∀ N : ℕ, N1 ≤ N → F.step N ≤ h0 →
      (∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA (μ, t) N n) → ∀ X ∈ Set.Icc Jlo Jhi, ∀ k : ℕ,
        actionS0 F (μ, t) X = Real.pi * F.step N * k → 0 < (-1 : ℝ) ^ k * casD F (μ, t) N X := by
  obtain ⟨Kc, c0, h0, hc0, hh0, N1, hN1, hmain⟩ := bulk_exact_cas PI hP hcoup r hr
  obtain ⟨Cσ, hCσ, hσ⟩ := phase_sub_S0 PI
  refine ⟨min (min (min h0 1) (1 / (Cσ + 1))) (1 / (4 * (|Kc| + 1))), lt_min (lt_min (lt_min hh0 one_pos) (by positivity))
    (by positivity), N1, hN1, ?_⟩
  intro μ hμ t ht N hN hstep hpos X hX k hk
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hh0' : F.step N ≤ h0 := hstep.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hh1 : F.step N ≤ 1 := hstep.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hhC : F.step N ≤ 1 / (Cσ + 1) := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhK : F.step N ≤ 1 / (4 * (|Kc| + 1)) := hstep.trans (min_le_right _ _)
  obtain ⟨hab, pre, hpre, hcas⟩ := hmain μ hμ t ht N hN hh0' hpos X hX
  have hprepos : 0 < pre := lt_of_lt_of_le (mul_pos hc0 (Real.sqrt_pos.mpr hst)) hpre
  have hSig := hσ μ hμ t ht X hX N hh1
  -- `x = (Sigma - S_0)/h`, `|x| <= Cσ h <= 1`
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (bulkPhaseSum PI μ t X N - actionS0 F (μ, t) X) / F.step N := ⟨_, rfl⟩
  have hxabs : |x| ≤ 1 := by
    rw [hx, abs_div, abs_of_pos hst, div_le_one hst]
    have h1 : Cσ * F.step N ^ 2 ≤ F.step N := by
      have h2 : Cσ * F.step N ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hhC hCσ
        calc Cσ * F.step N ≤ Cσ * (1 / (Cσ + 1)) := this
          _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; linarith
      nlinarith [hst]
    exact hSig.trans h1
  have hcos : 1 / 2 ≤ Real.cos x := by
    have := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
    linarith
  have hphase : bulkPhaseSum PI μ t X N / F.step N - Real.pi / 2 = Real.pi * k + x - Real.pi / 2 := by
    rw [hx]
    have : bulkPhaseSum PI μ t X N = actionS0 F (μ, t) X + (bulkPhaseSum PI μ t X N - actionS0 F (μ, t) X) := by ring
    rw [this, hk]
    field_simp
    ring
  have hsin : Real.sin (bulkPhaseSum PI μ t X N / F.step N - Real.pi / 2) = -((-1 : ℝ) ^ k * Real.cos x) := by
    rw [hphase]
    have : Real.pi * k + x - Real.pi / 2 = (x - Real.pi / 2) + k * Real.pi := by ring
    rw [this, Real.sin_add_nat_mul_pi, Real.sin_sub_pi_div_two]
    ring
  rw [hsin] at hcas
  -- `a b D = pre (-1)^k cos x + E`, `|E| <= Kc h^m pre`
  set hm : ℝ := F.step N ^ (max M 1) with hhm
  have hm1 : 1 ≤ max M 1 := le_max_right _ _
  have hmle : hm ≤ F.step N := by
    rw [hhm]
    calc F.step N ^ (max M 1) ≤ F.step N ^ 1 := pow_le_pow_of_le_one hst.le hh1 hm1
      _ = F.step N := pow_one _
  have hm0 : 0 ≤ hm := pow_nonneg hst.le _
  have hKh : |Kc| * hm ≤ 1 / 4 := by
    have h1 : |Kc| * hm ≤ |Kc| * F.step N := mul_le_mul_of_nonneg_left hmle (abs_nonneg _)
    have h2 : |Kc| * F.step N ≤ |Kc| * (1 / (4 * (|Kc| + 1))) := mul_le_mul_of_nonneg_left hhK (abs_nonneg _)
    have h3 : |Kc| * (1 / (4 * (|Kc| + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg Kc]
    linarith
  set Dv := casD F (μ, t) N X with hDv
  set ab := CL.psiHatL (μ, t) X N 0 * CR.psiHatL (μ, t) X N 0 with hab'
  have hE : |ab * Dv - pre * ((-1 : ℝ) ^ k * Real.cos x)| ≤ Kc * hm * pre := by
    have : ab * Dv + pre * -((-1 : ℝ) ^ k * Real.cos x) = ab * Dv - pre * ((-1 : ℝ) ^ k * Real.cos x) := by ring
    rw [← this]
    exact hcas
  -- multiply by `(-1)^k`
  have hsq : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  have habs1 : |(-1 : ℝ) ^ k| = 1 := by simp
  have hE2 : |(-1 : ℝ) ^ k * (ab * Dv) - pre * Real.cos x| ≤ Kc * hm * pre := by
    have e : (-1 : ℝ) ^ k * (ab * Dv) - pre * Real.cos x = (-1 : ℝ) ^ k * (ab * Dv - pre * ((-1 : ℝ) ^ k * Real.cos x)) := by
      have : (-1 : ℝ) ^ k * (pre * ((-1 : ℝ) ^ k * Real.cos x)) = pre * Real.cos x := by
        calc (-1 : ℝ) ^ k * (pre * ((-1 : ℝ) ^ k * Real.cos x)) = ((-1 : ℝ) ^ k * (-1) ^ k) * (pre * Real.cos x) := by ring
          _ = pre * Real.cos x := by rw [hsq, one_mul]
      linear_combination this
    rw [e, abs_mul, habs1, one_mul]
    exact hE
  have hpos2 : 0 < (-1 : ℝ) ^ k * (ab * Dv) := by
    have h1 := (abs_le.mp hE2).1
    have h2 : pre * (1 / 2) ≤ pre * Real.cos x := mul_le_mul_of_nonneg_left hcos hprepos.le
    have h3 : |Kc| * hm * pre ≤ pre * (1 / 4) := by
      have := mul_le_mul_of_nonneg_right hKh hprepos.le
      linarith
    have h4 : Kc * hm * pre ≤ |Kc| * hm * pre := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hm0) hprepos.le
    linarith [h1, h2, h3, h4, hprepos]
  have : (-1 : ℝ) ^ k * (ab * Dv) = ab * ((-1 : ℝ) ^ k * Dv) := by ring
  rw [this] at hpos2
  exact (mul_pos_iff_of_pos_left hab).mp hpos2


lemma sign_eq_of_pos_mul {k : ℕ} {D : ℝ} (h : 0 < (-1 : ℝ) ^ k * D) : SignType.sign D = SignType.sign ((-1 : ℝ) ^ k) := by
  rcases neg_one_pow_eq_or ℝ k with hk | hk
  · rw [hk] at h ⊢
    rw [one_mul] at h
    rw [sign_pos h, sign_pos one_pos]
  · rw [hk] at h ⊢
    have : D < 0 := by linarith
    rw [sign_neg this, sign_neg (by norm_num : (-1 : ℝ) < 0)]

/-- `S_0^{(t)}` is continuous on the block (it is `Sigma_0`, `C^{2M+1}` by `Sigma_reg`). -/
lemma actionS0_continuousOn (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR) {μ : Par} (hμ : μ ∈ K) {t : ℝ}
    (ht : t ∈ Set.Icc (-t0) t0) :
    ContinuousOn (fun X => actionS0 F (μ, t) X) (Set.Icc Jlo Jhi) := by
  have h : ContDiffOn ℝ ((2 * M + 1 : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => PI.Sigma μ 0 p.1 p.2)
      (Set.Icc Jlo Jhi ×ˢ Set.Icc (-t0) t0) := PI.Sigma_reg μ hμ 0 (Nat.zero_le _)
  have hc : ContinuousOn (fun X => PI.Sigma μ 0 X t) (Set.Icc Jlo Jhi) :=
    h.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun X hX => ⟨hX, ht⟩)
  exact hc.congr (fun X hX => (PI.Sigma_zero μ hμ X hX t ht).symm)

set_option maxHeartbeats 4000000 in
/-- **(3) (iii), the sign of `kappa'` at an eigenvalue of a window** (`lem:smo-bulkphase` (3) (iii)): for every window constant `Cw` there is `h0` such that for `X` with
`|S_0(X) - pi h (k + 1/2)| <= Cw h^2` and `p_n = kappa' q_n` for all rows (`D(X) = 0`), `sign kappa' = sign (-1)^k` (`sigma' = 1`).
Proof as in the paper: `kappa' = psi^L_n psi^R_n / (psi^R_n)^2 * (positive seeds)`, the exact edge solutions have the phases `Theta_L/h - pi/4`, `Theta_R/h - pi/4`
(`exact_phase_row`, from `bulk_phase_left` and `prop:tha-W` (1)); at a window `alpha + beta = pi k + O(h)`, so `cos beta = (-1)^k cos alpha + O(h)` and
`(-1)^k psi^L_n psi^R_n = rho_L rho_R (cos^2 alpha + O(h)) > 0` at a row of the overlap with `cos^2 alpha >= eps/2`; two consecutive rows exist and
`cos^2 alpha_n + cos^2 alpha_{n+1} >= 1 - cos(theta_1) = eps` (`cos_sq_pair`, from the margin `theta_margin` and `thetaL_incr`). -/
theorem bulk_kappa_sign {cPC CPC : ℝ} (PC : ParabolicCylinderFacts U V cPC CPC)
    (hcoup : CR.c = F.L - CL.c' ∧ CR.c' = F.L - CL.c) {Kd r : ℕ} (hr : StdAssump F P Kd r) (Cw : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ N1 : ℕ, 1 ≤ N1 ∧ ∀ p ∈ P, ∀ N : ℕ, N1 ≤ N → F.step N ≤ h0 →
      (∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA p N n) → ∀ X ∈ Set.Icc Jlo Jhi, ∀ k : ℕ,
        |actionS0 F p X - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ Cw * F.step N ^ 2 → ∀ κ' : ℝ,
        (∀ n ≤ N, pSol F p N X n = κ' * qSol F p N X (N - n)) →
          SignType.sign κ' = SignType.sign ((-1 : ℝ) ^ k) := by
  classical
  have hm1 : 1 ≤ max M 1 := le_max_right _ _
  obtain ⟨EL, h0L, hEL, hh0L, hLex⟩ := exact_phase_row CL hm1 PC
  obtain ⟨ER, h0R, hER, hh0R, hRex⟩ := exact_phase_row CR hm1 PC
  obtain ⟨ε, hε0, hε1, hmarg⟩ := CL.theta_margin
  obtain ⟨hc'L, hc'cL, hσL, hcσL, -, -, -, -, -, -⟩ := CL.consts_pos
  obtain ⟨Cw', hCw'⟩ : ∃ x : ℝ, x = max Cw 0 := ⟨_, rfl⟩
  have hCw'0 : 0 ≤ Cw' := by rw [hCw']; exact le_max_right _ _
  have hCwle : Cw ≤ Cw' := by rw [hCw']; exact le_max_left _ _
  obtain ⟨K1, hK1⟩ : ∃ x : ℝ, x = EL + ER + Cw' + EL * (Cw' + ER) := ⟨_, rfl⟩
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  refine ⟨min (min (min h0L h0R) 1) (min (min ((CL.c - CL.c') / 6) CL.σ) ((ε / 2) / (2 * (K1 + 1)))),
    lt_min (lt_min (lt_min hh0L hh0R) one_pos) (lt_min (lt_min (by linarith) hσL) (by positivity)),
    max (max CL.N0 CR.N0) 1, le_max_right _ _, ?_⟩
  intro p hp N hN hstep hpos X hX k hwin κ' hκ'
  have hN1 : CL.N0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : CR.N0 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNone : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hstepR : (mirrorFamily F).step N = F.step N := rfl
  have hhL : F.step N ≤ h0L := hstep.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hhR : F.step N ≤ h0R := hstep.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hh1 : F.step N ≤ 1 := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhd : F.step N ≤ (CL.c - CL.c') / 6 := hstep.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hhσ : F.step N ≤ CL.σ := hstep.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hhK : F.step N ≤ (ε / 2) / (2 * (K1 + 1)) := hstep.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLs : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ F N
  obtain ⟨g, hyp, hG2, hB2⟩ := stdAssump_hyp_C2 hr hp
  -- exact solutions
  have hα : 0 < CL.psiHatL p X N 0 := by
    rw [show CL.psiHatL p X N 0 = (CL.chain p X N).phi (F.step N) 0 1 0 from psiHat_one_eq (CL.chain p X N) (F.step N) 0]
    exact CL.seed_pos _ hp X hX N hN1
  have hβ : 0 < CR.psiHatL p X N 0 := by
    rw [show CR.psiHatL p X N 0 = (CR.chain p X N).phi ((mirrorFamily F).step N) 0 1 0 from psiHat_one_eq (CR.chain p X N) ((mirrorFamily F).step N) 0]
    exact CR.seed_pos _ hp X hX N hN2
  set α0 := CL.psiHatL p X N 0 with hα0
  set β0 := CR.psiHatL p X N 0 with hβ0
  have hJL : JacSol F p N X (CL.chain p X N).NR (fun n => α0 * pZ F p N X n) := by
    intro n hn0 hn1
    have h := Lop_pZ hpos hNone X n hn0 (by have := chain_NR_le_N CL p hp X hX N hN1; omega)
    rw [Lop_smul]
    exact mul_eq_zero_of_right _ h
  have hJR : JacSol (mirrorFamily F) p N X (CR.chain p X N).NR (fun i => β0 * qZ F p N X ((N : ℤ) - i)) := by
    intro n hn0 hn1
    rw [show (fun i => β0 * qZ F p N X ((N : ℤ) - i)) = fun i => β0 * (fun j => qZ F p N X j) ((N : ℤ) - i) from rfl,
      Lop_smul, lop_mirror_part F p N X (qZ F p N X)
        (fun j hj1 hjN => Lop_qZ hpos hNone X j hj1 hjN) n hn0 (by have := chain_NR_le_N CR p hp X hX N hN2; omega), mul_zero]
  have hseedL : (fun n => α0 * pZ F p N X n) 0 = CL.psiHatL p X N 0 := by
    show α0 * pZ F p N X 0 = α0
    rw [pZ_zero, mul_one]
  have hseedR : (fun i => β0 * qZ F p N X ((N : ℤ) - i)) 0 = CR.psiHatL p X N 0 := by
    show β0 * qZ F p N X ((N : ℤ) - 0) = β0
    rw [sub_zero, qZ_N, mul_one]
  -- two consecutive overlap rows
  obtain ⟨S, hS, hScard⟩ := count_pairs (F.step N) F.L CL.c' CL.c N hst hLs hc'L hc'cL (by linarith)
  have h6 : 6 ≤ (CL.c - CL.c') / F.step N := by
    rw [le_div_iff₀ hst]; linarith
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℝ) < (S.card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨n, hnS⟩ := hSne
  obtain ⟨hn0, hn1, hc1, hc2⟩ := hS n hnS
  have hsucc : uNode (F.step N) (n + 1) = uNode (F.step N) n + F.step N := by
    unfold uNode; push_cast; ring
  -- the margin and the phase increment
  have hmargin := hmarg p hp X hX
  have hε1pos : 0 < Real.arccos (1 - ε) := Real.arccos_pos.mpr (by linarith)
  have hε1le : Real.arccos (1 - ε) ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by linarith)
  have hcosε1 : Real.cos (Real.arccos (1 - ε)) = 1 - ε := Real.cos_arccos (by linarith) (by linarith)
  have hcL : CL.c < F.L := by linarith
  have hinc := thetaL_incr (L := F.L) F.L_pos hyp hG2 hB2 X hc'L hcL hε1 hmargin hc1
    (show uNode (F.step N) n ≤ uNode (F.step N) (n + 1) by rw [hsucc]; linarith) hc2
  rw [hsucc] at hinc
  have hh' : uNode (F.step N) n + F.step N - uNode (F.step N) n = F.step N := by ring
  rw [hh'] at hinc
  obtain ⟨θb, hθb⟩ : ∃ θb : ℝ, θb = (thetaL F.L (F.G 0 p) (F.B 0 p) X (uNode (F.step N) (n + 1)) -
      thetaL F.L (F.G 0 p) (F.B 0 p) X (uNode (F.step N) n)) / F.step N := ⟨_, rfl⟩
  have hθ1 : Real.arccos (1 - ε) ≤ θb := by
    rw [hθb, le_div_iff₀ hst]; rw [hsucc]; linarith [hinc.1]
  have hθ2 : θb ≤ Real.pi - Real.arccos (1 - ε) := by
    rw [hθb, div_le_iff₀ hst]; rw [hsucc]; linarith [hinc.2]
  obtain ⟨αn, hαn⟩ : ∃ a : ℝ, a = thetaL F.L (F.G 0 p) (F.B 0 p) X (uNode (F.step N) n) / F.step N - Real.pi / 4 := ⟨_, rfl⟩
  have hαn1 : thetaL F.L (F.G 0 p) (F.B 0 p) X (uNode (F.step N) (n + 1)) / F.step N - Real.pi / 4 = αn + θb := by
    rw [hαn, hθb]; field_simp; ring
  have hpair := cos_sq_pair αn θb (Real.arccos (1 - ε)) hε1pos hε1le hθ1 hθ2
  rw [hcosε1] at hpair
  have hpair' : ε ≤ Real.cos αn ^ 2 + Real.cos (αn + θb) ^ 2 := by linarith
  have hS0 : actionS0 F p X = ∫ v in (0 : ℝ)..F.L, actInt F.L (F.G 0 p) (F.B 0 p) X v := rfl
  have hpq : ∀ r : ℤ, 0 ≤ r → r ≤ (N : ℤ) → pZ F p N X r = κ' * qZ F p N X r := by
    intro r hr0 hrN
    have h1 := hκ' r.toNat (by omega)
    have e : ((N : ℤ) - r).toNat = N - r.toNat := by omega
    unfold pZ qZ
    rw [h1, e]
  -- the sign at one row
  have key : ∀ r : ℤ, 0 ≤ r → r ≤ (N : ℤ) → CL.c' ≤ uNode (F.step N) r → uNode (F.step N) r ≤ CL.c →
      ε / 2 ≤ Real.cos (thetaL F.L (F.G 0 p) (F.B 0 p) X (uNode (F.step N) r) / F.step N - Real.pi / 4) ^ 2 →
      0 < (-1 : ℝ) ^ k * (α0 * pZ F p N X r * (β0 * qZ F p N X r)) := by
    intro r hr0 hrN hr1 hr2 hcos2
    have hrNR : r ≤ (CL.chain p X N).NR := by
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨-, -, -, -, hlt⟩ := CL.shape p hp X hX N hN1
      have := uNode_le_of_le hst.le (show (CL.chain p X N).NR + 1 ≤ r by omega)
      linarith
    have hum : uNode ((mirrorFamily F).step N) ((N : ℤ) - r) = F.L - uNode (F.step N) r := by
      show uNode (F.step N) ((N : ℤ) - r) = _
      unfold uNode; push_cast; linear_combination hLs
    have hmNR : (N : ℤ) - r ≤ (CR.chain p X N).NR := by
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨-, -, -, -, hlt⟩ := CR.shape p hp X hX N hN2
      have h1 := uNode_le_of_le (h := (mirrorFamily F).step N) hst.le (show (CR.chain p X N).NR + 1 ≤ (N : ℤ) - r by omega)
      rw [hum] at h1
      rw [hcoup.1] at hlt
      linarith
    have hmov : CR.c' ≤ uNode ((mirrorFamily F).step N) ((N : ℤ) - r) := by
      rw [hum, hcoup.2]; linarith
    obtain ⟨ρL, hρL, hL1⟩ := hLex p hp X hX N hN1 hhL (fun n => α0 * pZ F p N X n) hJL hseedL r hr0 hrNR hr1
    obtain ⟨ρR, hρR, hR1⟩ := hRex p hp X hX N hN2 hhR (fun i => β0 * qZ F p N X ((N : ℤ) - i)) hJR hseedR ((N : ℤ) - r) (by omega) hmNR hmov
    have hL1' : |α0 * pZ F p N X r - ρL * Real.cos (thetaL F.L (F.G 0 p) (F.B 0 p) X (uNode (F.step N) r) / F.step N - Real.pi / 4)|
        ≤ EL * F.step N * ρL := hL1
    have e : (N : ℤ) - ((N : ℤ) - r) = r := by ring
    have hψ : (fun i : ℤ => β0 * qZ F p N X ((N : ℤ) - i)) ((N : ℤ) - r) = β0 * qZ F p N X r := by
      show β0 * qZ F p N X ((N : ℤ) - ((N : ℤ) - r)) = _
      rw [e]
    have hR1' : |β0 * qZ F p N X r - ρR * Real.cos (thetaL F.L (fun s => F.G 0 p (F.L - s)) (fun s => F.B 0 p (F.L - s)) X
        (F.L - uNode (F.step N) r) / F.step N - Real.pi / 4)| ≤ ER * F.step N * ρR := by
      have h := hR1
      rw [e, hum] at h
      exact h
    have hrL : uNode (F.step N) r ∈ Set.Icc 0 F.L := ⟨by linarith, by linarith⟩
    have hadd := thetaL_add_mirror F.L_pos hyp hG2 hB2 X hrL
    rw [← hS0] at hadd
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (actionS0 F p X - Real.pi * F.step N * ((k : ℝ) + 1 / 2)) / F.step N := ⟨_, rfl⟩
    have hδb : |δ| ≤ Cw' * F.step N := by
      rw [hδ, abs_div, abs_of_pos hst, div_le_iff₀ hst]
      calc |actionS0 F p X - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ Cw * F.step N ^ 2 := hwin
        _ ≤ Cw' * F.step N ^ 2 := mul_le_mul_of_nonneg_right hCwle (by positivity)
        _ = Cw' * F.step N * F.step N := by ring
    have hsum : (thetaL F.L (F.G 0 p) (F.B 0 p) X (uNode (F.step N) r) / F.step N - Real.pi / 4) +
        (thetaL F.L (fun s => F.G 0 p (F.L - s)) (fun s => F.B 0 p (F.L - s)) X (F.L - uNode (F.step N) r) / F.step N - Real.pi / 4)
        = Real.pi * k + δ := by
      rw [hδ]
      have : thetaL F.L (F.G 0 p) (F.B 0 p) X (uNode (F.step N) r) +
          thetaL F.L (fun s => F.G 0 p (F.L - s)) (fun s => F.B 0 p (F.L - s)) X (F.L - uNode (F.step N) r) = actionS0 F p X := hadd
      have e1 : ∀ a b : ℝ, (a / F.step N - Real.pi / 4) + (b / F.step N - Real.pi / 4) = (a + b) / F.step N - Real.pi / 2 := fun a b => by ring
      rw [e1, this]
      field_simp
      ring
    have hrel := cos_beta_rel _ _ δ k hsum
    have hsmall : F.step N * (EL + ER + Cw' + EL * (Cw' + ER)) < ε / 2 := by
      rw [← hK1]
      have h1 : F.step N * K1 ≤ F.step N * (K1 + 1) := by nlinarith
      have h2 : F.step N * (K1 + 1) ≤ ε / 4 := by
        have := mul_le_mul_of_nonneg_right hhK (show 0 ≤ 2 * (K1 + 1) by positivity)
        have e2 : (ε / 2) / (2 * (K1 + 1)) * (2 * (K1 + 1)) = ε / 2 := by field_simp
        nlinarith
      linarith
    refine row_product_pos (s := (-1 : ℝ) ^ k)
      (y := Real.cos (thetaL F.L (fun s => F.G 0 p (F.L - s)) (fun s => F.B 0 p (F.L - s)) X (F.L - uNode (F.step N) r) / F.step N - Real.pi / 4)) (by rw [← pow_mul, mul_comm, pow_mul]; simp) hρL hρR hL1' ?_ ?_
      (Real.abs_cos_le_one _) hcos2 hst hh1 hEL hER hCw'0 hsmall
    · exact hR1'
    · exact hrel.trans hδb
  have hfin : ∀ r : ℤ, 0 ≤ r → r ≤ (N : ℤ) → CL.c' ≤ uNode (F.step N) r → uNode (F.step N) r ≤ CL.c →
      ε / 2 ≤ Real.cos (thetaL F.L (F.G 0 p) (F.B 0 p) X (uNode (F.step N) r) / F.step N - Real.pi / 4) ^ 2 →
      0 < (-1 : ℝ) ^ k * κ' := by
    intro r hr0 hrN hr1 hr2 hcos2
    have h := key r hr0 hrN hr1 hr2 hcos2
    rw [hpq r hr0 hrN] at h
    have hA : 0 ≤ α0 * β0 * qZ F p N X r ^ 2 := by positivity
    have e : (-1 : ℝ) ^ k * (α0 * (κ' * qZ F p N X r) * (β0 * qZ F p N X r)) = (α0 * β0 * qZ F p N X r ^ 2) * ((-1 : ℝ) ^ k * κ') := by ring
    rw [e] at h
    by_contra hD
    push_neg at hD
    have := mul_nonpos_of_nonneg_of_nonpos hA hD
    linarith
  have hcase : ε / 2 ≤ Real.cos αn ^ 2 ∨ ε / 2 ≤ Real.cos (αn + θb) ^ 2 := by
    by_contra hcon
    push_neg at hcon
    linarith [hcon.1, hcon.2]
  have hD : 0 < (-1 : ℝ) ^ k * κ' := by
    rcases hcase with h1 | h1
    · refine hfin n hn0 (by omega) hc1 (by rw [hsucc] at hc2; linarith) ?_
      rw [← hαn]; exact h1
    · refine hfin (n + 1) (by omega) hn1 (by rw [hsucc]; linarith) hc2 ?_
      rw [hαn1]; exact h1
  exact sign_eq_of_pos_mul hD

/-- **(3), counting** (`lem:smo-bulkphase` (3)): `propThaCount` for the block `I = [Jlo, Jhi]`, `Phi = S_0^{(t)}`, `eps = C h^2`.  At most one zero of `D` in each window and exactly one in each window whose
bracketing interval lies in `S_0(I)`.  Both former inputs are now proved: `S_0^{(t)}` strictly decreasing on the block (`bulk_actionS0_strictAnti`, `TheoremA/MonotoneAction.lean`) and the sign `(iii)` of
`kappa'` at the zeros in the windows (`bulk_kappa_sign`, with `sigma' = 1`).  (i) and (ii) of `lem:tha-count` are `bulk_zero_window`, `bulk_node_sign`. -/
theorem bulk_count (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR) {cPC CPC : ℝ} (PC : ParabolicCylinderFacts U V cPC CPC)
    (hP : ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, (μ, t) ∈ P)
    (hcoup : CR.c = F.L - CL.c' ∧ CR.c' = F.L - CL.c) (r : ℕ) (hr : StdAssump F P (max M 1 / 2) r) :
    ∃ C h0 : ℝ, 0 < C ∧ 0 < h0 ∧ ∃ N1 : ℕ, 1 ≤ N1 ∧ ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, ∀ N : ℕ, N1 ≤ N → F.step N ≤ h0 →
      (∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA (μ, t) N n) →
      (∀ k : ℕ, ∀ X ∈ Set.Icc Jlo Jhi, ∀ X' ∈ Set.Icc Jlo Jhi, casD F (μ, t) N X = 0 → casD F (μ, t) N X' = 0 →
        |actionS0 F (μ, t) X - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ C * F.step N ^ 2 →
        |actionS0 F (μ, t) X' - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ C * F.step N ^ 2 → X = X') ∧
      (∀ k : ℕ, Set.Icc (Real.pi * F.step N * k) (Real.pi * F.step N * (k + 1)) ⊆
          (fun X => actionS0 F (μ, t) X) '' Set.Icc Jlo Jhi →
        ∃ X ∈ Set.Icc Jlo Jhi, casD F (μ, t) N X = 0 ∧
          |actionS0 F (μ, t) X - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ C * F.step N ^ 2) := by
  obtain ⟨C1, h1, hC1, hh1, N1, hN1, hwin⟩ := bulk_zero_window PI hP hcoup r hr
  obtain ⟨h2, hh2, N2, hN2, hnode⟩ := bulk_node_sign PI hP hcoup r hr
  obtain ⟨h3, hh3, N3, hN3, hkap⟩ := bulk_kappa_sign (CL := CL) (CR := CR) PC hcoup hr C1
  have hmono := bulk_actionS0_strictAnti CL hP hr
  refine ⟨C1, min (min (min h1 h2) h3) (Real.pi / (8 * C1)), hC1,
    lt_min (lt_min (lt_min hh1 hh2) hh3) (div_pos Real.pi_pos (by positivity)), max (max N1 N2) N3,
    le_trans hN1 ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro μ hμ t ht N hN hstep hpos
  have hN1' : N1 ≤ N := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hN
  have hN2' : N2 ≤ N := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hN
  have hN3' : N3 ≤ N := le_trans (le_max_right _ _) hN
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hs1 : F.step N ≤ h1 := hstep.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hs2 : F.step N ≤ h2 := hstep.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hs3k : F.step N ≤ h3 := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : F.step N ≤ Real.pi / (8 * C1) := hstep.trans (min_le_right _ _)
  have hN1one : 1 ≤ N := le_trans hN1 hN1'
  have hε1 : C1 * F.step N ^ 2 < Real.pi * F.step N / 4 := by
    have h2' : C1 * F.step N ≤ Real.pi / 8 := by
      calc C1 * F.step N ≤ C1 * (Real.pi / (8 * C1)) := mul_le_mul_of_nonneg_left hs3 hC1.le
        _ = Real.pi / 8 := by field_simp
    nlinarith [mul_pos Real.pi_pos hst]
  have hε0 : 0 < C1 * F.step N ^ 2 := by positivity
  have hp : (μ, t) ∈ P := hP μ hμ t ht
  have hcount := propThaCount F (μ, t) N hN1one hpos (Set.Icc Jlo Jhi) (fun X => actionS0 F (μ, t) X) (C1 * F.step N ^ 2)
    Set.ordConnected_Icc (actionS0_continuousOn PI hμ ht) (Or.inr (hmono μ hμ t ht)) hε0 hε1
    (fun X hX hD => by
      obtain ⟨j, hj⟩ := hwin μ hμ t ht N hN1' hs1 hpos X hX hD
      exact ⟨j, hj⟩)
    ⟨1, Or.inl rfl, fun X hX k hk => by
      have := hnode μ hμ t ht N hN2' hs2 hpos X hX k hk
      rw [one_mul]
      exact sign_eq_of_pos_mul this⟩
  refine hcount ⟨1, Or.inl rfl, fun X hX k _ hwk κ' hκ' => ?_⟩
  rw [one_mul]
  exact hkap (μ, t) hp N hN3' hs3k hpos X hX k hwk κ' hκ'

end Windows

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_exact_cas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_exact_cas

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_zero_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_zero_window

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_node_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_node_sign

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_kappa_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_kappa_sign

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_count

end FormalResearch.JacobiEigenvectors.TheoremA
