module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftRescale

/-!
# Paper J, Layer 2 (L2.C6): the solution through the soft edge, `prop:tha-W2` item (1) -- what is proved and why the frozen statement cannot be proved as it stands

Source: Paper J `thmA.tex` `prop:tha-W2` (1); `app_thmA.tex` "The soft edges: proof of Proposition prop:tha-W2", Steps 1--3; `charts.tex` `thm:cha-PC`; `engine.tex` `thm:eng-volterra` and the
paragraph on the forbidden overlap.  Statement being proved: `TheoremA.PropThaW2` (item (1)); structure: `Charts.SoftEdgeChart`.

## Chain of lemmas planned (and status)

1. (engine) rescaling `(lam^{-1}, lam)` of patch 1 and `stability_rescale1`: **proved** (`SoftRescale.lean`).
2. (engine) `(M_1)_{11}` as a Casoratian ratio, `psi-hat_2 = (M_1)_{11} phi^{(1)}_2 + (M_1)_{21} phi^{(2)}_2`: **proved** (`SoftRescale.lean`).
3. `softLam_pos`, `kappaBal_pos`, the weights `W_k = E_Web(k)/lambda` and `W(j_1) = E_-(j_1)` of the chain: **proved** (below).
4. `lamL_eq_kappa_mul_transMat`: `lambda_L = kappa_bal (M_1^{orig})_{11}`: **proved** (below).
5. `soft_through_edge` (below): from the engine hypotheses of the **rescaled** chain (`hVal`) and `1 <= m`,
   (a) the Weber bound `|psi_k - psi-hat^L_k| <= C h^m E_Web M_Web` on the rows `0 <= k <= j_1` (the rows where the chain's patch 1 carries the Weber weights),
   (b') the pre-absorption collar bound on `u_k > u_c - eta/2`: `|psi_k - psi-hat^L_k| <= lambda M_bal (C h^m E_-(k) + Lambda K E_-(j_1)^2 / E_-(k))`,
   (c-upper) `0 < lambda` and `|lambda_L| <= Lambda lambda kappa_bal`.
6. Not proved: see the findings below.

## FINDINGS: the frozen statement `PropThaW2` (1) and the frozen `SoftEdgeChart` do not suffice

* **F-W2-1 (the chain is not the rescaled chain).**  `SoftEdgeChart.valid` asks `(chain mu X N).Valid`, with weights `W = E_Web/lambda` on patch 1 (`W1_def`, the rescaled weight) but the model
  pair `wf 1` the *unrescaled* Weber pair (`wf1_eq`).  `Valid.env` then needs `|wf^{(1)}| <= K E_Web M / lambda` and `|wf^{(2)}| <= K lambda E_Web^{-1} M`, with `|wf^{(1)}| ~ E_Web M`, `|wf^{(2)}| ~ E_Web^{-1} M`
  (the Wronskian is `sqrt h` by `omega_sqrt` and `wronsk`): this forces `lambda ~ 1`, while the paper says `lambda` "may be exponentially large or small".  Minimal correction: `SoftEdgeChart.valid` should read
  `((chain mu X N).rescale1 lam).Valid cs (step N) m` with `lam = softLam`, i.e. the engine hypotheses are for the chain whose first pair is rescaled by `(lam^{-1}, lam)` (`LadderData.rescale1`,
  `SoftRescale.lean`); `wf1_eq` and `lamL`, `psiHatL`, `PropThaW2` then stay as they are (they refer to the unrescaled pair).  `soft_through_edge` takes exactly this as the hypothesis `hVal`.
* **F-W2-2 (the weight of the second patch for `a <= 0`).**  `W2_def` gives the second patch the weight `Eminus = E_well(a, |Z|)` on *all* of `[j_1+1, N_R]`, which reaches `Z >> 0` (`zeta_far`), and the chain
  has `P = 2`.  The first member of the `-` pair, `u~(a,-Z)`, grows like `E_well^{-1}` for `Z > 0` (it is the dominant member there), and `E_well(a,|Z|)` is not non-decreasing in `Z` on `Z > 0`:
  `Valid.env` (S2) and `Valid.W_mono` fail for a genuine chart with `a <= 0`.  The paper uses *three* patches for `a <= 0` (Weber, `-` pair on `Z <= 0` with `E_well`, swapped pair `(v~, -u~)` on `Z >= 0`
  with `E_well^{-1}`, the transfer matrix at `Z = 0` being `(M_-(a) S)^{-1}`, bounded: Step 2); only `a > 0` has two patches.  Minimal correction: `shape` should read `P = 3` for `a <= 0` (the third patch
  `(vt a, -ut a)` with weight `(Ewell a |Z|)^{-1}` from the bond `j_2`, `Z_{j_2} <= 0 < Z_{j_2+1}`) and `W2_def`, `wf2_eq`, `M2_def` be split accordingly; `Eminus` is then the weight of the middle patch only.
  `soft_through_edge` and the bounds below are for the chain as frozen (`P = 2`), i.e. they are about the case where the frozen chain is valid (`a > 0`), and cannot be transferred to `a <= 0` without this correction.
* **F-W2-3 (Step 1 is a separate chart).**  The Weber bound on `uc - eta <  u_n <= uc - eta/2` (the first bound of item (1)) is Step 1 of the paper, a *single-patch* Weber chain on all of `[0, u_c - eta/2]`
  (Corollary `cor:cha-I-general`, like `BulkWeberChart`).  The chain of `SoftEdgeChart` has patch 1 only up to the overlap bond `j_1` (`u_{j_1} <= u_c - eta`) and its row `j_1+1` already carries the second
  patch's weights; between `u_c - eta` and `u_c - eta/2` the engine bound is against the PC pair, whose weight is not comparable to `E_Web/lambda` over that stretch (exponentially different), so (a) cannot
  be obtained there from the chain.  Minimal correction: add to `SoftEdgeChart` the Step-1 chart `chainW : Par -> R -> N -> LadderData` (`P = 1`, hard-edge seed, window up to `u_c - eta/2`, the Weber
  `Valid` of `BulkWeberChart` with `W = E_Web`), and state (a) from `bulkSolutionBound_of_one_le`-style application of `LadderData.stability` to it.  `soft_through_edge` (a) is therefore stated for `0 <= k <= j_1` only.
* **F-W2-4 (`m >= 1`).**  As for the bulk (F-C1), `2 K_D K_w h^m Theta <= c_*` is unavailable for `m = 0`: `PropThaW2` needs the hypothesis `1 <= m` (the paper: "Fix `m >= 1`").
* **F-W2-5 (`Lm`).**  `PropThaW2` quantifies over an arbitrary `Lm : R -> R`; the claims (a), (b), (c), the eigenvector bound and the quantisation are false for `Lm = 0`.  It needs `forall h in (0,1], 1 <= Lm h`
  (the paper: `Lm = 1` or `log(1/h)`).
* **F-W2-6 (analytic facts missing from `ParabolicCylinderFacts`).**  (b) of item (1) and the lower bound `|lambda_L| >= c lambda kappa_bal` are *derived* in the paper from (i) the absorption
  `Lambda h^{-m} (E_{j_1}/E_n)^2 <= e^{-c/h}` (Step 3, needs `zeta_far`, the action integral in `Ewell`), (ii) the equivalence `lambda W M ~ |lambda_L| M_Olv(a,-Z)` (`eq:cha-MolvEquiv`: a *lower* bound
  `M_Olv >= c E M_bal / kappa_bal` inside the well, where `ParabolicCylinderFacts.beyond` only gives it for `Z >= 2 sqrt A`), and (iii) the ratio `r_2 = e^{-theta}(1+O(h)) < 1` of the dominant PC member
  between `j_1` and `j_1+1` (Liouville--Green; no field gives it).  None is derivable from the frozen structure; they are Layer-4 facts (`lem:cha-PCenv` lower bounds, `eq:cha-MolvEquiv`) that must be added to
  `ParabolicCylinderFacts` (resp. be proved from `ode_U`, `wronsk`) before (b) and the lower half of (c) can be formalised.
* **F-W2-7 (the derivation of (S3)).**  `Valid.transfer` is a *field*, i.e. (S3) is assumed, not derived from the forbidden overlap.  The derivation is `Engine.transfer_of_forbidden_overlap` (one application),
  whose hypotheses at `j_1` are: `A_{j_1} M_{j_1} M_{j_1+1} <= C_omega omega` (needs `M^2 <= C h^{1/2}` from `k_2 >= c/h`: `Y_forb` for Weber, `zeta_far` and `muS_bd` for PC, and `A <= C`), `W_{j_1+1} <= C_w W_{j_1}`
  (needs the log-derivative bound of `Ewell` on a step), the envelope bounds and (S1) (`Valid.phi_bd`, `Valid.cas_lb_site`, exported in `SoftRescale.lean`).  It is not done: the three inputs are
  chart-level estimates (`bondA` bound, `Ewell` ratio, `k2` lower bound), and with the correction of F-W2-1 the field `transfer` could be dropped from the structure in favour of them.

## What `soft_through_edge` proves, exactly

Hypotheses: `C : SoftEdgeChart` (frozen), `1 <= m`, and `hVal`: for every `(p, X, N)` of the chart, the chain with its first pair rescaled by `(lam^{-1}, lam)`, `lam = softLam`, satisfies `Valid` (this is the corrected
`valid` of F-W1; for `lam = 1` it is the frozen `valid`).  Conclusion: there are `Cc, h0` (depending only on `cs`, `Csum`, `eta`, `m`) such that for `h <= h0` (constants uniform in `(p, X, N, psi)`), the exact solution `psi`
of the recurrence on rows `0..N_R` seeded by `psi_0 = psi-hat^L_0` satisfies the three statements above.

## Differences from the paper

* `hVal` replaces `SoftEdgeChart.valid` (F-W2-1); `lambda` is positive here (a ratio of positive weights), as in the paper.
* The bound (b') is the paper's before the absorption step; the conversion to `|lambda_L| M_Olv` is not done (F-W2-6).

## Not formalised

(a) on `u_c - eta < u_k <= u_c - eta/2` (F-W2-3); (b) in the form of `PropThaW2` (F-W2-6, F-W2-2 for `a <= 0`); the lower bound of (c) (F-W2-6); the derivation of (S3) from the forbidden overlap (F-W2-7);
items (2)--(4) of `PropThaW2` (L2.C7).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

lemma uNode_mono' {h : ℝ} (hh : 0 ≤ h) {a b : ℤ} (hab : a ≤ b) : uNode h a ≤ uNode h b := by
  unfold uNode
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  nlinarith

lemma kappaBal_pos (a : ℝ) : 0 < kappaBal a := by
  unfold kappaBal
  split_ifs with h
  · apply Real.rpow_pos_of_pos
    apply Real.Gamma_pos_of_pos
    linarith
  · apply mul_pos
    · apply Real.rpow_pos_of_pos
      positivity
    · apply Real.sqrt_pos.mpr
      apply Real.Gamma_pos_of_pos
      linarith [not_le.mp h]

lemma Ewell_pos (a z : ℝ) : 0 < Ewell a z := by
  unfold Ewell
  split_ifs
  · exact Real.exp_pos _
  · exact one_pos

lemma Eminus_pos (a z : ℝ) : 0 < Eminus a z := by
  unfold Eminus
  split_ifs
  · exact Ewell_pos _ _
  · exact inv_pos.mpr (Real.exp_pos _)

section SoftChain

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V)

lemma softEnvWebW_pos (p : Par × ℝ) (X : ℝ) (N : ℕ) (k : ℤ) : 0 < softEnvWebW C p X N k :=
  Ewell_pos _ _

lemma softLam_pos (p : Par × ℝ) (X : ℝ) (N : ℕ) : 0 < softLam C p X N :=
  div_pos (softEnvWebW_pos C p X N _) (Eminus_pos _ _)

/-- On patch 1 the chain weight is the Weber barrier weight divided by `lambda` (`W1_def`). -/
lemma chain_W_one {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
    {k : ℤ} (hk : k ∈ Finset.Icc (0 : ℤ) ((C.chain p X N).jj 1)) :
    (C.chain p X N).W k = softEnvWebW C p X N k / softLam C p X N := by
  rw [C.W1_def p hp X hX N hN k hk]
  rfl

/-- The chain weight at the overlap bond is the parabolic-cylinder weight `E_-(j_1)`. -/
lemma chain_W_j1 {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
    (hjj : 0 ≤ (C.chain p X N).jj 1) :
    (C.chain p X N).W ((C.chain p X N).jj 1) = Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)) := by
  rw [chain_W_one C hp hX hN (Finset.mem_Icc.mpr ⟨hjj, le_rfl⟩)]
  have h1 := softEnvWebW_pos C p X N (C.j1 p X N)
  have h2 := Eminus_pos (C.aOf p X N) (C.Zof p X N (C.j1 p X N))
  unfold softLam
  show softEnvWebW C p X N (C.j1 p X N) / (softEnvWebW C p X N (C.j1 p X N) / Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)))
    = _
  field_simp

/-- `lambda_L = kappa_bal (M_1^{orig})_{11}`: the Casoratian definition of `lambda_L` is `kappa_bal` times the `(0,0)` entry of the first transfer matrix of the (unrescaled) chain,
provided `A_{j_1} != 0`. -/
lemma lamL_eq_kappa_mul_transMat (p : Par × ℝ) (X : ℝ) (N : ℕ) (hA : (C.chain p X N).A (C.j1 p X N) ≠ 0) :
    C.lamL p X N = kappaBal (C.aOf p X N) *
      transMat ((C.chain p X N).phi (Fz.step N) 0) ((C.chain p X N).phi (Fz.step N) 1) (C.chain p X N).jj 1 0 0 := by
  rw [LadderData.transMat_zero_zero_eq_cas_div ((C.chain p X N).phi (Fz.step N) 0) ((C.chain p X N).phi (Fz.step N) 1)
    (C.chain p X N).jj 1 (C.chain p X N).A hA]
  unfold SoftEdgeChart.lamL
  simp only [SoftEdgeChart.j1]
  have e : cas (C.chain p X N).A (fun n => (C.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (C.aOf p X N))
        ((C.chain p X N).phi (Fz.step N) 1 2) ((C.chain p X N).jj 1)
      = cas (C.chain p X N).A ((C.chain p X N).phi (Fz.step N) 0 2) ((C.chain p X N).phi (Fz.step N) 1 2) ((C.chain p X N).jj 1)
          / kappaBal (C.aOf p X N) := by
    unfold cas
    ring
  rw [e, div_div_eq_mul_div]
  show _ = kappaBal (C.aOf p X N) * (_ / _)
  ring

end SoftChain

/-! ### The theorem -/

/-- **L2.C6 (partial): the solution through the soft edge** (`prop:tha-W2` (1), `thm:cha-PC`, `app_thmA` Steps 1--3), see the module docstring for what is and is not covered.
`hVal` is the corrected validity of the chain (`rescale1`, finding F-W2-1). -/
theorem soft_through_edge {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
    (C : SoftEdgeChart Fz P m q U V) (hm : 1 ≤ m)
    (hVal : ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ C.δ0 → ∀ N : ℕ, C.N0 ≤ N →
      ((C.chain p X N).rescale1 (softLam C p X N)).Valid C.cs (Fz.step N) m) :
    ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ C.δ0 → ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 →
      0 < softLam C p X N ∧
      |C.lamL p X N| ≤ C.cs.Λ * (softLam C p X N * kappaBal (C.aOf p X N)) ∧
      ∀ ψ : ℤ → ℝ, JacSol Fz p N X (C.chain p X N).NR ψ → ψ 0 = C.psiHatL p X N 0 →
        (∀ k ∈ Finset.Icc (0 : ℤ) (C.j1 p X N),
          |ψ k - C.psiHatL p X N k| ≤ Cc * Fz.step N ^ m * softEnvWeb C p X N k) ∧
        (∀ k ∈ Finset.Icc (C.j1 p X N + 1) (C.chain p X N).NR, C.uc p - C.η / 2 < uNode (Fz.step N) k →
          |ψ k - C.psiHatL p X N k| ≤ softLam C p X N * Mbal (C.aOf p X N) (C.Zof p X N k) *
            (Cc * Fz.step N ^ m * Eminus (C.aOf p X N) (C.Zof p X N k)
              + C.cs.Λ * ((C.cs.KA + C.cs.KB) * C.cs.Kw) * Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)) ^ 2
                / Eminus (C.aOf p X N) (C.Zof p X N k))) := by
  obtain ⟨-, hη, -, -, -, -, hCsum, -⟩ := C.consts_pos
  set cs := C.cs with hcs
  set K : ℝ := (cs.KA + cs.KB) * cs.Kw with hK
  have hKnn : 0 ≤ K := mul_nonneg (add_nonneg cs.KA_nonneg cs.KB_nonneg) cs.Kw_nonneg
  have hE : 0 ≤ 2 * cs.KD * cs.Kw := mul_nonneg (mul_nonneg (by norm_num) cs.KD_nonneg) cs.Kw_nonneg
  have hq : 0 ≤ 1 + cs.CE ^ 2 := by positivity
  have hcmq : 0 ≤ (1 + cs.CE ^ 2) / cs.cm := div_nonneg hq cs.cm_pos.le
  have hDst : 0 < mvCstar cs.cm cs.CE K := by
    unfold mvCstar
    have h1 : 0 ≤ 2 * ((1 + cs.CE ^ 2) / cs.cm) * K :=
      mul_nonneg (mul_nonneg (by norm_num) hcmq) hKnn
    exact div_pos one_pos (by linarith)
  set M0 : ℝ := 2 * cs.KD * cs.Kw * C.Csum with hM0
  have hM0nn : 0 ≤ M0 := mul_nonneg hE hCsum
  have hden : 0 < M0 + 1 := by linarith
  set h0 : ℝ := min C.η (min 1 (mvCstar cs.cm cs.CE K / (M0 + 1))) with hh0
  have hh0pos : 0 < h0 := lt_min hη (lt_min one_pos (div_pos hDst hden))
  have hmvC : 0 ≤ mvC cs.cm cs.CE K cs.Λ 2 := by
    unfold mvC mvCrStar mvKappa
    have hΛ : 0 ≤ cs.Λ := by linarith [cs.Λ_ge]
    have hR : 0 ≤ (cs.Λ * (1 + cs.CE ^ 2)) ^ 2 * (1 + cs.CE ^ 2) :=
      mul_nonneg (pow_nonneg (mul_nonneg hΛ hq) 2) hq
    have hκ : 0 ≤ (2 * cs.Λ ^ 2 * (1 + cs.CE ^ 2) + 1) ^ 2 + 1 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcmq) hKnn)
      (mul_nonneg (mul_nonneg hKnn hR) hκ)
  refine ⟨mvC cs.cm cs.CE K cs.Λ 2 * (2 * cs.KD * cs.Kw * C.Csum), h0, hh0pos, ?_⟩
  intro p hp X hX N hN hstep
  have hV : ((C.chain p X N).rescale1 (softLam C p X N)).Valid cs (Fz.step N) m := hVal p hp X hX N hN
  obtain ⟨hP2, hs0, hj1u, hj1v, hNRu, hNRv⟩ := C.shape p hp X hX N hN
  have hθ : (C.chain p X N).theta (Fz.step N) ≤ C.Csum := C.theta_le p hp X hX N hN
  have hstep_pos : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hstepη : Fz.step N ≤ C.η := le_trans hstep (min_le_left _ _)
  have hstep1 : Fz.step N ≤ 1 := le_trans hstep (le_trans (min_le_right _ _) (min_le_left _ _))
  have hsmall_h : Fz.step N ≤ mvCstar cs.cm cs.CE K / (M0 + 1) :=
    le_trans hstep (le_trans (min_le_right _ _) (min_le_right _ _))
  have hpowle : (Fz.step N) ^ m ≤ Fz.step N := pow_le_of_le_one hstep_pos.le hstep1 (by omega)
  have hlam : 0 < softLam C p X N := softLam_pos C p X N
  -- smallness
  have hsmall : 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * (C.chain p X N).theta (Fz.step N)
      ≤ mvCstar cs.cm cs.CE K := by
    have hpow0 : 0 ≤ (Fz.step N) ^ m := pow_nonneg hstep_pos.le m
    have h1 : 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * (C.chain p X N).theta (Fz.step N)
        ≤ 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * C.Csum :=
      mul_le_mul_of_nonneg_left hθ (mul_nonneg hE hpow0)
    have h2 : 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * C.Csum ≤ Fz.step N * M0 := by
      calc 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * C.Csum = M0 * (Fz.step N) ^ m := by rw [hM0]; ring
        _ ≤ M0 * Fz.step N := mul_le_mul_of_nonneg_left hpowle hM0nn
        _ = Fz.step N * M0 := by ring
    have h3 : Fz.step N * M0 ≤ mvCstar cs.cm cs.CE K := by
      have hs := mul_le_mul_of_nonneg_right hsmall_h hM0nn
      have hfrac : mvCstar cs.cm cs.CE K / (M0 + 1) * M0 ≤ mvCstar cs.cm cs.CE K := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        nlinarith [hDst]
      linarith
    linarith
  set D := C.chain p X N with hD
  set lam := softLam C p X N with hlamdef
  have hNRD : (C.chain p X N).NR = D.NR := rfl
  have hj1D : C.j1 p X N = D.jj 1 := rfl
  have hjj0' : 0 ≤ D.jj 1 := hV.jj_nonneg (by show 1 ≤ D.P; omega)
  have hjj12 : D.jj 1 < D.jj 2 := hV.jj_mono 1 (by show 1 < D.P; omega)
  have hphi2 : ∀ α : Fin 2, (D.rescale1 lam).phi (Fz.step N) α 2 = D.phi (Fz.step N) α 2 :=
    fun α => funext (LadderData.phi_rescale1_of_ne D lam _ α (by norm_num))
  -- `A_{j_1} != 0` from the Casoratian of the second pair
  have hcas := hV.cas_lb_site (p := 2) (mem_Icc.mpr ⟨by norm_num, by show 2 ≤ D.P; omega⟩)
    (j := D.jj 1) (mem_Icc.mpr ⟨le_of_eq rfl, hjj12.le⟩)
  simp only [hphi2] at hcas
  have hωpos : 0 < |D.ω 1 (Fz.step N)| :=
    abs_pos.mpr ((hV.ladder 1 (mem_Icc.mpr ⟨le_rfl, by show 1 ≤ D.P; omega⟩)).wronsk_ne _ hV.h_pos)
  have hAne : D.A (D.jj 1) ≠ 0 := by
    intro h0
    have hc0 : cas D.A (D.phi (Fz.step N) 0 2) (D.phi (Fz.step N) 1 2) (D.jj 1) = 0 := by
      unfold cas
      rw [h0]
      ring
    have h1 : cs.cm * |D.ω 1 (Fz.step N)| ≤ |cas D.A (D.phi (Fz.step N) 0 2) (D.phi (Fz.step N) 1 2) (D.jj 1)| := hcas
    rw [hc0, abs_zero] at h1
    exact absurd h1 (not_le.mpr (mul_pos cs.cm_pos hωpos))
  -- the transfer matrix and its rescaling
  obtain ⟨-, t00, -, -, t10⟩ := hV.transfer 1 le_rfl (by show 1 < D.P; omega)
  have t00' : |transMat ((D.rescale1 lam).phi (Fz.step N) 0) ((D.rescale1 lam).phi (Fz.step N) 1) D.jj 1 0 0| ≤ cs.Λ := t00
  have t10' : |transMat ((D.rescale1 lam).phi (Fz.step N) 0) ((D.rescale1 lam).phi (Fz.step N) 1) D.jj 1 1 0|
      ≤ cs.Λ * D.W (D.jj 1) ^ 2 := t10
  obtain ⟨r00, r10, -, -⟩ := LadderData.transMat_rescale1_one D lam (Fz.step N)
  have hM00 : transMat (D.phi (Fz.step N) 0) (D.phi (Fz.step N) 1) D.jj 1 0 0
      = lam * transMat ((D.rescale1 lam).phi (Fz.step N) 0) ((D.rescale1 lam).phi (Fz.step N) 1) D.jj 1 0 0 := by
    rw [r00]
    field_simp
  have hM10 : transMat (D.phi (Fz.step N) 0) (D.phi (Fz.step N) 1) D.jj 1 1 0
      = lam * transMat ((D.rescale1 lam).phi (Fz.step N) 0) ((D.rescale1 lam).phi (Fz.step N) 1) D.jj 1 1 0 := by
    rw [r10]
    field_simp
  have hlamL : C.lamL p X N = kappaBal (C.aOf p X N) *
      transMat (D.phi (Fz.step N) 0) (D.phi (Fz.step N) 1) D.jj 1 0 0 :=
    lamL_eq_kappa_mul_transMat C p X N hAne
  have hκ := kappaBal_pos (C.aOf p X N)
  have hup : |C.lamL p X N| ≤ cs.Λ * (lam * kappaBal (C.aOf p X N)) := by
    rw [hlamL, hM00, abs_mul, abs_mul, abs_of_pos hκ, abs_of_pos hlam]
    calc kappaBal (C.aOf p X N) * (lam * |transMat ((D.rescale1 lam).phi (Fz.step N) 0)
            ((D.rescale1 lam).phi (Fz.step N) 1) D.jj 1 0 0|)
        = (kappaBal (C.aOf p X N) * lam) * |transMat ((D.rescale1 lam).phi (Fz.step N) 0)
            ((D.rescale1 lam).phi (Fz.step N) 1) D.jj 1 0 0| := by ring
      _ ≤ (kappaBal (C.aOf p X N) * lam) * cs.Λ := mul_le_mul_of_nonneg_left t00' (by positivity)
      _ = cs.Λ * (lam * kappaBal (C.aOf p X N)) := by ring
  refine ⟨hlam, hup, ?_⟩
  intro ψ hJ0 hseed0
  have hJ : JacSol Fz p N X D.NR ψ := hJ0
  -- the exact solution satisfies the engine's equations
  have hsol : ∀ j ∈ Icc D.s0 (D.NR - 1), Lh (Fz.step N) D.A D.Q ψ j = 0 := by
    intro j hj
    rw [hs0] at hj
    obtain ⟨hj0, hj1⟩ := mem_Icc.mp hj
    have hL : Lop (Fz.bondA p N) (Fz.diagQ p N X) ψ j = 0 :=
      hJ j hj0 (by show j < D.NR; omega)
    have hA0 : D.A j = Fz.bondA p N j :=
      C.A_bond p hp X hX N hN j (mem_Icc.mpr ⟨by omega, by omega⟩)
    have hA1 : D.A (j - 1) = Fz.bondA p N (j - 1) :=
      C.A_bond p hp X hX N hN (j - 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
    have hQ0 : D.Q j = Fz.diagQ p N X j :=
      C.Q_diag p hp X hX N hN j (mem_Icc.mpr ⟨hj0, by omega⟩)
    rw [Lh_congr_site hA0 hA1 hQ0]
    unfold Lh
    rw [hL, mul_zero]
  -- the seed
  have huc := (C.ucη_in p hp).1
  have hu0 : uNode (Fz.step N) 0 ≤ C.uc p - C.η / 2 := by
    unfold uNode
    simp only [Int.cast_zero, zero_add]
    linarith
  have hseed : ∀ j ∈ Icc (0 : ℤ) D.s0, ψ j = D.phi (Fz.step N) 0 1 j := by
    intro j hj
    rw [hs0] at hj
    have hj0 : j = 0 := by
      obtain ⟨h1, h2⟩ := mem_Icc.mp hj
      omega
    subst hj0
    rw [hseed0]
    unfold SoftEdgeChart.psiHatL
    simp only [hu0, ↓reduceIte]
    rfl
  have hst := LadderData.stability_rescale1 D cs (Fz.step N) m lam hlam.ne' hV ψ hsol hseed hsmall
  obtain ⟨c1, -, -⟩ := hst
  have hTT : 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N) ≤ 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * C.Csum :=
    mul_le_mul_of_nonneg_left hθ (mul_nonneg hE (pow_nonneg hstep_pos.le m))
  have hBT : mvC cs.cm cs.CE K cs.Λ 2 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N))
      ≤ mvC cs.cm cs.CE K cs.Λ 2 * (2 * cs.KD * cs.Kw * C.Csum) * (Fz.step N) ^ m := by
    calc _ ≤ mvC cs.cm cs.CE K cs.Λ 2 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * C.Csum) :=
          mul_le_mul_of_nonneg_left hTT hmvC
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · -- (a): Weber bound on the rows `0 <= k <= j_1`
    intro k hk
    obtain ⟨hk0, hkj⟩ := mem_Icc.mp hk
    have hkw : k ∈ Icc (eqLo D.s0 D.jj 1) (D.jj 1 + 1) := by
      rw [eqLo_one, hs0]
      exact mem_Icc.mpr ⟨hk0, by show k ≤ D.jj 1 + 1; omega⟩
    have h1 := c1 1 (mem_Icc.mpr ⟨le_rfl, by show 1 ≤ D.P; omega⟩) k hkw
    rw [hP2] at h1
    have hukk : uNode (Fz.step N) k ≤ C.uc p - C.η / 2 := by
      have hkj' : k ≤ D.jj 1 := hkj
      have := uNode_mono' hstep_pos.le hkj'
      linarith
    have hψL : C.psiHatL p X N k = D.phi (Fz.step N) 0 1 k := by
      unfold SoftEdgeChart.psiHatL
      simp only [hukk, ↓reduceIte]
      rfl
    have hpsi1 : D.psiHat (Fz.step N) 1 k = D.phi (Fz.step N) 0 1 k := by
      unfold LadderData.psiHat Engine.psiHat
      rw [cvec_one]
      simp
    have hkw1 : k ∈ Finset.Icc (0 : ℤ) ((C.chain p X N).jj 1) := mem_Icc.mpr ⟨hk0, hkj⟩
    have hW := chain_W_one C hp hX hN hkw1
    have hM := C.M1_def p hp X hX N hN k hkw1
    have hEk := softEnvWebW_pos C p X N k
    have hjjle1 : D.jj 1 ≤ D.NR - 1 := hV.jj_le (p := 1) (by show 1 ≤ D.P; omega)
    have hkj'' : k ≤ D.jj 1 := hkj
    have hMk : 0 < D.M k := hV.M_pos k (mem_Icc.mpr ⟨hk0, by show k ≤ D.NR; omega⟩)
    have hSE : softEnvWeb C p X N k = softEnvWebW C p X N k *
        Mbal (-((k : ℝ) + 1 / 2)) (C.Y p X (uNode (Fz.step N) k) / Real.sqrt (Fz.step N)) := rfl
    rw [hψL]
    rw [← hpsi1]
    refine le_trans h1 ?_
    rw [abs_of_pos hlam, hW, hSE, ← hM]
    have key : lam * (mvC cs.cm cs.CE K cs.Λ 2 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N))
        * (softEnvWebW C p X N k / lam) * D.M k)
        = (mvC cs.cm cs.CE K cs.Λ 2 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N)))
          * (softEnvWebW C p X N k * D.M k) := by
      field_simp
    rw [key]
    exact mul_le_mul hBT le_rfl (mul_nonneg hEk.le hMk.le)
      (mul_nonneg (mul_nonneg hmvC (mul_nonneg hE hCsum)) (pow_nonneg hstep_pos.le m))
  · -- (b'): the collar bound before absorption
    intro k hk hkuc
    obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
    have e1 : eqLo D.s0 D.jj 2 = D.jj 1 + 1 := eqLo_succ D.s0 D.jj 1 le_rfl
    have e2 : D.jj 2 + 1 = D.NR := by
      have := hV.jj_last
      change D.jj D.P = D.NR - 1 at this
      rw [hP2] at this
      omega
    have hkw : k ∈ Icc (eqLo D.s0 D.jj 2) (D.jj 2 + 1) := by
      rw [e1, e2]
      exact mem_Icc.mpr ⟨hk1, hk2⟩
    have hp2 : 2 ∈ Icc 1 D.P := mem_Icc.mpr ⟨by norm_num, by omega⟩
    have h1 := c1 2 hp2 k hkw
    rw [hP2] at h1
    have hkNR : k ∈ Finset.Icc (D.jj 1 + 1) (C.chain p X N).NR := mem_Icc.mpr ⟨hk1, hk2⟩
    have hW : D.W k = Eminus (C.aOf p X N) (C.Zof p X N k) := C.W2_def p hp X hX N hN k hkNR
    have hM : D.M k = Mbal (C.aOf p X N) (C.Zof p X N k) := C.M2_def p hp X hX N hN k hkNR
    have hk0 : 0 ≤ k := by omega
    have hWk : 0 < D.W k := hV.W_pos k (mem_Icc.mpr ⟨hk0, hk2⟩)
    have hMk : 0 < D.M k := hV.M_pos k (mem_Icc.mpr ⟨hk0, hk2⟩)
    have hψL : C.psiHatL p X N k = C.lamL p X N * (D.phi (Fz.step N) 0 2 k / kappaBal (C.aOf p X N)) := by
      unfold SoftEdgeChart.psiHatL
      simp only [not_le.mpr hkuc, ↓reduceIte]
      rfl
    have hpsi2 := LadderData.psiHat_two D (Fz.step N) k
    have hdecomp : ψ k - C.psiHatL p X N k
        = (ψ k - D.psiHat (Fz.step N) 2 k)
          + transMat (D.phi (Fz.step N) 0) (D.phi (Fz.step N) 1) D.jj 1 1 0 * D.phi (Fz.step N) 1 2 k := by
      rw [hψL, hpsi2, hlamL]
      field_simp
      ring
    -- the envelope of the second member of the second pair
    have hwin : k ∈ Icc (D.jj (2 - 1)) (D.jj 2 + 1) := by
      rw [e2]
      exact mem_Icc.mpr ⟨by show D.jj 1 ≤ k; omega, hk2⟩
    have hb := (hV.phi_bd (p := 2) hp2 hwin).2
    rw [hphi2] at hb
    have hb' : |D.phi (Fz.step N) 1 2 k| ≤ K * (D.W k)⁻¹ * D.M k := hb
    have hWj := chain_W_j1 C hp hX hN hjj0'
    have hbM : |transMat (D.phi (Fz.step N) 0) (D.phi (Fz.step N) 1) D.jj 1 1 0| ≤ lam * (cs.Λ * D.W (D.jj 1) ^ 2) := by
      rw [hM10, abs_mul, abs_of_pos hlam]
      exact mul_le_mul_of_nonneg_left t10' hlam.le
    have hterm : |transMat (D.phi (Fz.step N) 0) (D.phi (Fz.step N) 1) D.jj 1 1 0 * D.phi (Fz.step N) 1 2 k|
        ≤ lam * (cs.Λ * D.W (D.jj 1) ^ 2) * (K * (D.W k)⁻¹ * D.M k) := by
      rw [abs_mul]
      exact mul_le_mul hbM hb' (abs_nonneg _) (mul_nonneg hlam.le (mul_nonneg (by linarith [cs.Λ_ge]) (sq_nonneg _)))
    rw [abs_of_pos hlam, hW, hM] at h1
    rw [hdecomp]
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add h1 hterm) ?_
    rw [hW, hM, hWj]
    have hE := Eminus_pos (C.aOf p X N) (C.Zof p X N k)
    have hMb : 0 < Mbal (C.aOf p X N) (C.Zof p X N k) := hM ▸ hMk
    have e1 : lam * (mvC cs.cm cs.CE K cs.Λ 2 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N))
          * Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))
        ≤ lam * Mbal (C.aOf p X N) (C.Zof p X N k)
          * (mvC cs.cm cs.CE K cs.Λ 2 * (2 * cs.KD * cs.Kw * C.Csum) * (Fz.step N) ^ m
              * Eminus (C.aOf p X N) (C.Zof p X N k)) := by
      calc _ = lam * Mbal (C.aOf p X N) (C.Zof p X N k)
              * ((mvC cs.cm cs.CE K cs.Λ 2 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N)))
                  * Eminus (C.aOf p X N) (C.Zof p X N k)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBT hE.le) (by positivity)
    have e2 : lam * (cs.Λ * Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)) ^ 2)
          * (K * (Eminus (C.aOf p X N) (C.Zof p X N k))⁻¹ * Mbal (C.aOf p X N) (C.Zof p X N k))
        = lam * Mbal (C.aOf p X N) (C.Zof p X N k)
          * (cs.Λ * K * Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)) ^ 2 / Eminus (C.aOf p X N) (C.Zof p X N k)) := by
      field_simp
    calc _ ≤ _ := add_le_add e1 e2.le
      _ = _ := by ring

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_through_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.soft_through_edge

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.lamL_eq_kappa_mul_transMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.lamL_eq_kappa_mul_transMat

end FormalResearch.JacobiEigenvectors.TheoremA
