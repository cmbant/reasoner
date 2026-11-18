module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.LadderChain
public import FormalResearch.JacobiEigenvectors.Engine.LadderStability
public import FormalResearch.JacobiEigenvectors.Engine.VolterraMulti

/-!
# Paper J, Layer 2 (L2.C6, engine part): the reciprocal rescaling `(lambda^{-1}, lambda)` of the first patch

Source: Paper J `engine.tex`, `thm:eng-volterra` and the paragraph after it ("The comparability of the weights at a forbidden overlap is
arranged by rescaling the pairs of the earlier patches by `(lambda^{-1}, lambda)` ... the conclusion for the original seed is the rescaled one multiplied
by `lambda`"); `app_thmA.tex`, "The soft edges: proof of Proposition prop:tha-W2", Step 3 (`eq:tha-connect`).

## Proved here (all unconditional statements about `LadderData`, no chart hypothesis)

* `LadderData.rescale1 D lam`: the chain `D` with the model pair of **patch 1** replaced by `(lam^{-1} w^{(1)}, lam w^{(2)})`; operator, corrector rows,
  envelopes, breakpoints unchanged.
* `phi_rescale1`, `transMat_rescale1_one`, `cvec_rescale1`, `psiHat_rescale1`: the comparison pairs, the transfer matrix `M_1 = M_1^{orig} diag(lam^{-1}, lam)`, the coefficient
  vectors `c_p = lam^{-1} c_p^{orig}` (`p >= 2`) and the comparison sequences `psi-hat_p = lam^{-1} psi-hat_p^{orig}` (`p >= 1`).
* `stability_rescale1` (**the rescaling theorem**): if the *rescaled* chain satisfies the engine hypotheses (`Valid`), then for every solution `psi` with the *original* seed
  `psi_j = phi^{(1)}_{1,j}` the multi-patch bound holds for the original comparison sequence with the constant multiplied by `|lam|`
  (`|psi_j - psi-hat_{p,j}| <= |lam| C eps Theta W_j M_j`).  The proof applies `LadderData.stability` (L1.1) to `psi / lam`.
* `Valid.cas_lb_site`, `Valid.phi_bd`: the (S1) Casoratian bound and the (S2) envelopes of the pairs (the two derived facts of the proof of `LadderData.stability`, exported).
* `transMat_zero_zero_eq_cas_div`, `cvec_two`, `psiHat_two`: `(M_p)_{11} = W(phi^{(1)}_p, phi^{(2)}_{p+1}) / W(phi^{(1)}_{p+1}, phi^{(2)}_{p+1})` at the overlap bond (the identity
  behind `lambda_L = kappa (M_1)_{11}` in `app_thmA`), and `psi-hat_2 = (M_1)_{11} phi^{(1)}_2 + (M_1)_{21} phi^{(2)}_2`.

## Differences from the paper

* The paper rescales "the pairs of the earlier patches"; here exactly patch 1 (the only earlier patch of the two-patch soft-edge chain).  For a chain of more patches the later overlaps
  would need the same lemma at their patch.
* No hypothesis on the weights at the overlap is *used* by `stability_rescale1`: the hypotheses are the whole `Valid` of the rescaled chain, which contains (S3).  The paper's derivation of (S3) at a forbidden
  overlap from the comparability `W_{j+1} <= C_w W_j`, `A M M <= C_omega omega`, the envelope bounds and (S1) is `Engine.transfer_of_forbidden_overlap`
  (one application to `D.phi`); verifying its hypotheses for the Weber and parabolic-cylinder pairs is the chart-level part (not done, see `SoftProof.lean`).

## Not formalised

Several rescalings (more than one forbidden overlap); the preservation of `Valid` fields other than `env` and `transfer` is not stated (they are fields of the hypothesis).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Finset FormalResearch.JacobiEigenvectors.Engine

namespace LadderData

/-- The scalar by which the model member `alpha` of patch `p` is multiplied: `(lam^{-1}, lam)` on patch `1`, `1` elsewhere. -/
def rescaleFactor (lam : ℝ) (p : ℕ) (α : Fin 2) : ℝ :=
  if p = 1 then (if α = 0 then lam⁻¹ else lam) else 1

/-- The chain with the model pair of patch `1` rescaled reciprocally by `(lam^{-1}, lam)`. -/
def rescale1 (D : LadderData) (lam : ℝ) : LadderData :=
  { D with wf := fun p α u h => rescaleFactor lam p α • D.wf p α u h }

lemma dot_smul (v x : V2) (c : ℝ) : dot v (c • x) = c * dot v x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  ring

/-- The comparison pairs of the rescaled chain. -/
lemma phi_rescale1 (D : LadderData) (lam h : ℝ) (α : Fin 2) (p : ℕ) (k : ℤ) :
    (D.rescale1 lam).phi h α p k = rescaleFactor lam p α * D.phi h α p k := by
  unfold LadderData.phi ladderSeq
  show dot (vrow (D.AA p) (D.BB p) (((k : ℝ) + 1 / 2) * h) h) (rescaleFactor lam p α • D.wf p α (((k : ℝ) + 1 / 2) * h) h) = _
  rw [dot_smul]

lemma phi_rescale1_of_ne (D : LadderData) (lam h : ℝ) (α : Fin 2) {p : ℕ} (hp : p ≠ 1) (k : ℤ) :
    (D.rescale1 lam).phi h α p k = D.phi h α p k := by
  rw [phi_rescale1]
  simp [rescaleFactor, hp]

lemma phi_rescale1_one_zero (D : LadderData) (lam h : ℝ) (k : ℤ) :
    (D.rescale1 lam).phi h 0 1 k = lam⁻¹ * D.phi h 0 1 k := by
  rw [phi_rescale1]
  simp [rescaleFactor]

lemma phi_rescale1_one_one (D : LadderData) (lam h : ℝ) (k : ℤ) :
    (D.rescale1 lam).phi h 1 1 k = lam * D.phi h 1 1 k := by
  rw [phi_rescale1]
  simp [rescaleFactor]

/-- The data of the rescaled chain other than `wf` are those of `D`. -/
lemma rescale1_jj (D : LadderData) (lam : ℝ) : (D.rescale1 lam).jj = D.jj := rfl

lemma rescale1_theta (D : LadderData) (lam h : ℝ) : (D.rescale1 lam).theta h = D.theta h := rfl

/-- The transfer matrix of the first overlap of the rescaled chain: the original one times `diag(lam^{-1}, lam)` (columns). -/
lemma transMat_rescale1_one (D : LadderData) (lam h : ℝ) :
    transMat ((D.rescale1 lam).phi h 0) ((D.rescale1 lam).phi h 1) D.jj 1 0 0
        = transMat (D.phi h 0) (D.phi h 1) D.jj 1 0 0 * lam⁻¹ ∧
    transMat ((D.rescale1 lam).phi h 0) ((D.rescale1 lam).phi h 1) D.jj 1 1 0
        = transMat (D.phi h 0) (D.phi h 1) D.jj 1 1 0 * lam⁻¹ ∧
    transMat ((D.rescale1 lam).phi h 0) ((D.rescale1 lam).phi h 1) D.jj 1 0 1
        = transMat (D.phi h 0) (D.phi h 1) D.jj 1 0 1 * lam ∧
    transMat ((D.rescale1 lam).phi h 0) ((D.rescale1 lam).phi h 1) D.jj 1 1 1
        = transMat (D.phi h 0) (D.phi h 1) D.jj 1 1 1 * lam := by
  obtain ⟨a00, a01, a10, a11, -⟩ := transMat_entries ((D.rescale1 lam).phi h 0) ((D.rescale1 lam).phi h 1) D.jj 1
  obtain ⟨b00, b01, b10, b11, -⟩ := transMat_entries (D.phi h 0) (D.phi h 1) D.jj 1
  have e2 : ∀ (α : Fin 2) (k : ℤ), (D.rescale1 lam).phi h α (1 + 1) k = D.phi h α (1 + 1) k :=
    fun α k => phi_rescale1_of_ne D lam h α (by norm_num) k
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [a00, b00]
    simp only [e2, phi_rescale1_one_zero]
    ring
  · rw [a10, b10]
    simp only [e2, phi_rescale1_one_zero]
    ring
  · rw [a01, b01]
    simp only [e2, phi_rescale1_one_one]
    ring
  · rw [a11, b11]
    simp only [e2, phi_rescale1_one_one]
    ring

/-- `bondMat` only sees the values of the pair of its own patch. -/
lemma bondMat_congr (φ1 φ2 ψ1 ψ2 : ℕ → ℤ → ℝ) (p : ℕ) (j : ℤ) (h1 : ∀ k, ψ1 p k = φ1 p k) (h2 : ∀ k, ψ2 p k = φ2 p k) :
    bondMat ψ1 ψ2 p j = bondMat φ1 φ2 p j := by
  unfold bondMat
  simp only [h1, h2]

/-- For `p >= 2` the transfer matrix is that of the original chain (patches `p`, `p+1` are not rescaled). -/
lemma transMat_rescale1_of_two_le (D : LadderData) (lam h : ℝ) {p : ℕ} (hp : 2 ≤ p) :
    transMat ((D.rescale1 lam).phi h 0) ((D.rescale1 lam).phi h 1) D.jj p = transMat (D.phi h 0) (D.phi h 1) D.jj p := by
  unfold transMat
  rw [bondMat_congr (D.phi h 0) (D.phi h 1) ((D.rescale1 lam).phi h 0) ((D.rescale1 lam).phi h 1) (p + 1) (D.jj p)
      (fun k => phi_rescale1_of_ne D lam h 0 (by omega) k) (fun k => phi_rescale1_of_ne D lam h 1 (by omega) k),
    bondMat_congr (D.phi h 0) (D.phi h 1) ((D.rescale1 lam).phi h 0) ((D.rescale1 lam).phi h 1) p (D.jj p)
      (fun k => phi_rescale1_of_ne D lam h 0 (by omega) k) (fun k => phi_rescale1_of_ne D lam h 1 (by omega) k)]

lemma cvec_two (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) :
    cvec φ1 φ2 jj 2 = ![transMat φ1 φ2 jj 1 0 0, transMat φ1 φ2 jj 1 1 0] := by
  show mulMV (transMat φ1 φ2 jj 1) ![1, 0] = _
  simp [mulMV]

/-- The coefficient vectors of the rescaled chain: `c_p = lam^{-1} c_p^{orig}` for `p >= 2`. -/
lemma cvec_rescale1 (D : LadderData) (lam h : ℝ) :
    ∀ (p : ℕ), 2 ≤ p → ∀ i : Fin 2,
      cvec ((D.rescale1 lam).phi h 0) ((D.rescale1 lam).phi h 1) D.jj p i
        = lam⁻¹ * cvec (D.phi h 0) (D.phi h 1) D.jj p i := by
  intro p hp
  induction p, hp using Nat.le_induction with
  | base =>
    intro i
    obtain ⟨t00, t10, -, -⟩ := transMat_rescale1_one D lam h
    rw [cvec_two, cvec_two]
    fin_cases i
    · simp [t00]; ring
    · simp [t10]; ring
  | succ n hn ih =>
    intro i
    rw [show n + 1 = (n - 1) + 2 by omega, cvec_succ_succ, cvec_succ_succ,
      show (n - 1) + 1 = n by omega, transMat_rescale1_of_two_le D lam h hn]
    have ih0 := ih 0
    have ih1 := ih 1
    fin_cases i
    · simp [mulMV, ih0, ih1]
      ring
    · simp [mulMV, ih0, ih1]
      ring

/-- The comparison sequences of the rescaled chain: `psi-hat_p = lam^{-1} psi-hat_p^{orig}` for every patch `p >= 1`. -/
lemma psiHat_rescale1 (D : LadderData) (lam h : ℝ) {p : ℕ} (hp : 1 ≤ p) (j : ℤ) :
    (D.rescale1 lam).psiHat h p j = lam⁻¹ * D.psiHat h p j := by
  unfold LadderData.psiHat Engine.psiHat
  rw [rescale1_jj]
  by_cases h1 : p = 1
  · subst h1
    rw [cvec_one, cvec_one]
    simp [phi_rescale1_one_zero]
  · have h2 : 2 ≤ p := by omega
    rw [cvec_rescale1 D lam h p h2 0, cvec_rescale1 D lam h p h2 1,
      phi_rescale1_of_ne D lam h 0 h1, phi_rescale1_of_ne D lam h 1 h1]
    ring

/-- `psi-hat_2 = (M_1)_{11} phi^{(1)}_2 + (M_1)_{21} phi^{(2)}_2` (entries `(0,0)`, `(1,0)` of `M_1`). -/
lemma psiHat_two (D : LadderData) (h : ℝ) (j : ℤ) :
    D.psiHat h 2 j = transMat (D.phi h 0) (D.phi h 1) D.jj 1 0 0 * D.phi h 0 2 j
      + transMat (D.phi h 0) (D.phi h 1) D.jj 1 1 0 * D.phi h 1 2 j := by
  unfold LadderData.psiHat Engine.psiHat
  rw [cvec_two]
  simp

/-- `(M_p)_{11} = W(phi^{(1)}_p, phi^{(2)}_{p+1}) / W(phi^{(1)}_{p+1}, phi^{(2)}_{p+1})` at the overlap bond `j_p` (Casoratians, `A_{j_p} != 0`). -/
lemma transMat_zero_zero_eq_cas_div (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (p : ℕ) (A : ℤ → ℝ) (hA : A (jj p) ≠ 0) :
    transMat φ1 φ2 jj p 0 0 = cas A (φ1 p) (φ2 (p + 1)) (jj p) / cas A (φ1 (p + 1)) (φ2 (p + 1)) (jj p) := by
  obtain ⟨e00, -, -, -, -⟩ := transMat_entries φ1 φ2 jj p
  rw [e00]
  unfold cas
  have n1 : A (jj p) * (φ1 p (jj p + 1) * φ2 (p + 1) (jj p) - φ1 p (jj p) * φ2 (p + 1) (jj p + 1))
      = A (jj p) * (-(φ2 (p + 1) (jj p + 1) * φ1 p (jj p) - φ2 (p + 1) (jj p) * φ1 p (jj p + 1))) := by ring
  have n2 : A (jj p) * (φ1 (p + 1) (jj p + 1) * φ2 (p + 1) (jj p) - φ1 (p + 1) (jj p) * φ2 (p + 1) (jj p + 1))
      = A (jj p) * (-(φ1 (p + 1) (jj p) * φ2 (p + 1) (jj p + 1) - φ2 (p + 1) (jj p) * φ1 (p + 1) (jj p + 1))) := by ring
  rw [n1, n2, mul_div_mul_left _ _ hA, neg_div_neg_eq]

/-! ### The engine hypotheses, exported: (S1) and (S2) of the pairs -/

lemma Valid.jj_nonneg {D : LadderData} {cs : ChainConsts} {h : ℝ} {m : ℕ} (hV : D.Valid cs h m) {p : ℕ} (hp : p ≤ D.P) :
    0 ≤ D.jj p := by
  have := jj_mono_le D.jj D.P hV.jj_mono 0 p (Nat.zero_le _) hp
  rw [hV.jj0] at this
  exact this

lemma Valid.jj_le {D : LadderData} {cs : ChainConsts} {h : ℝ} {m : ℕ} (hV : D.Valid cs h m) {p : ℕ} (hp : p ≤ D.P) :
    D.jj p ≤ D.NR - 1 := by
  have := jj_mono_le D.jj D.P hV.jj_mono p D.P hp le_rfl
  rw [hV.jj_last] at this
  exact this

/-- **(S1)** of the pair of patch `p` on its bonds: `c_- omega_* <= |W_j(phi^{(1)}_p, phi^{(2)}_p)|`. -/
lemma Valid.cas_lb_site {D : LadderData} {cs : ChainConsts} {h : ℝ} {m : ℕ} (hV : D.Valid cs h m) {p : ℕ}
    (hp : p ∈ Icc 1 D.P) {j : ℤ} (hj : j ∈ Icc (D.jj (p - 1)) (D.jj p)) :
    cs.cm * |D.ω 1 h| ≤ |cas D.A (D.phi h 0 p) (D.phi h 1 p) j| := by
  have hpP := mem_Icc.mp hp
  have hjm := mem_Icc.mp hj
  have hl : 0 ≤ D.jj (p - 1) := hV.jj_nonneg (by omega)
  have hj0 : 0 ≤ j := le_trans hl hjm.1
  have hjN : j ≤ D.NR - 1 := le_trans hjm.2 (hV.jj_le hpP.2)
  have hwj : j ∈ Icc (max (D.jj (p - 1)) 0) (D.jj p + 1) := by
    rw [max_eq_left hl]
    exact mem_Icc.mpr ⟨hjm.1, by omega⟩
  have hS := ladder_S1 (hV.ladder p hp) (D.AA p) (D.BB p) hV.h_pos j hj0 (hV.cas_lb p hp j hwj)
  have hc := cas_congr_site (f := D.phi h 0 p) (g := D.phi h 1 p)
    (hV.A_eq p hp j (mem_Icc.mpr ⟨by omega, by omega⟩))
  have hω := hV.omega_eq p hp
  rw [← hω, ← hc, mul_comm]
  exact hS

/-- **(S2)** envelopes of the pair of patch `p` on its window: `|phi^{(1)}| <= K W M`, `|phi^{(2)}| <= K W^{-1} M`, `K = (K_A+K_B) K_w`. -/
lemma Valid.phi_bd {D : LadderData} {cs : ChainConsts} {h : ℝ} {m : ℕ} (hV : D.Valid cs h m) {p : ℕ}
    (hp : p ∈ Icc 1 D.P) {j : ℤ} (hj : j ∈ Icc (D.jj (p - 1)) (D.jj p + 1)) :
    |D.phi h 0 p j| ≤ (cs.KA + cs.KB) * cs.Kw * D.W j * D.M j ∧
    |D.phi h 1 p j| ≤ (cs.KA + cs.KB) * cs.Kw * (D.W j)⁻¹ * D.M j := by
  have hpP := mem_Icc.mp hp
  have hjm := mem_Icc.mp hj
  have hl : 0 ≤ D.jj (p - 1) := hV.jj_nonneg (by omega)
  have hj0 : 0 ≤ j := le_trans hl hjm.1
  have hjN : j ≤ D.NR := by
    have := hV.jj_le hpP.2
    omega
  have hWj := hV.W_pos j (mem_Icc.mpr ⟨hj0, hjN⟩)
  have hMj := hV.M_pos j (mem_Icc.mpr ⟨hj0, hjN⟩)
  have hwj : j ∈ Icc (max (D.jj (p - 1)) 0) (D.jj p + 1) := by
    rw [max_eq_left hl]
    exact hj
  obtain ⟨e0, e1, e2, e3⟩ := hV.env p hp j hwj
  refine ⟨?_, ?_⟩
  · exact ladder_S2 (D.AA p) (D.BB p) (D.wf p) (1 / 2) h 0 j cs.KA cs.KB cs.Kw (D.W j) (D.M j) (D.ρ j) (D.ρt j)
      cs.Kw_nonneg hWj.le hMj.le (hV.ρ_nonneg j) (hV.ρt_pos j hj0)
      (hV.A_bd p hp j hwj) (hV.B_bd p hp j hwj) e0 e2
  · exact ladder_S2 (D.AA p) (D.BB p) (D.wf p) (1 / 2) h 1 j cs.KA cs.KB cs.Kw ((D.W j)⁻¹) (D.M j) (D.ρ j) (D.ρt j)
      cs.Kw_nonneg (inv_nonneg.mpr hWj.le) hMj.le (hV.ρ_nonneg j) (hV.ρt_pos j hj0)
      (hV.A_bd p hp j hwj) (hV.B_bd p hp j hwj) e1 e3

/-- The residual operator is linear. -/
lemma Lh_smul (h c : ℝ) (A Q f : ℤ → ℝ) (j : ℤ) : Lh h A Q (fun n => c * f n) j = c * Lh h A Q f j := by
  unfold Lh Lop
  ring

/-- **The rescaling theorem** (`thm:eng-volterra` with the reciprocal rescaling `(lam^{-1}, lam)` of the first patch; `app_thmA` Step 3, `eq:tha-connect`):
if the chain `D` with its first pair rescaled by `(lam^{-1}, lam)` satisfies the engine hypotheses, then a solution with the *original* seed `psi = phi^{(1)}_1`
obeys the multi-patch bound against the *original* comparison sequence with the constant multiplied by `|lam|`. -/
theorem stability_rescale1 (D : LadderData) (cs : ChainConsts) (h : ℝ) (m : ℕ) (lam : ℝ) (hlam : lam ≠ 0)
    (hV : (D.rescale1 lam).Valid cs h m) (ψ : ℤ → ℝ)
    (hsol : ∀ k ∈ Icc D.s0 (D.NR - 1), Lh h D.A D.Q ψ k = 0)
    (hseed : ∀ j ∈ Icc (0 : ℤ) D.s0, ψ j = D.phi h 0 1 j)
    (hsmall : 2 * cs.KD * cs.Kw * h ^ m * D.theta h ≤ mvCstar cs.cm cs.CE ((cs.KA + cs.KB) * cs.Kw)) :
    (∀ p ∈ Icc 1 D.P, ∀ j ∈ Icc (eqLo D.s0 D.jj p) (D.jj p + 1),
      |ψ j - D.psiHat h p j| ≤ |lam| * (mvC cs.cm cs.CE ((cs.KA + cs.KB) * cs.Kw) cs.Λ D.P
        * (2 * cs.KD * cs.Kw * h ^ m * D.theta h) * D.W j * D.M j)) ∧
    (∀ p, 1 ≤ p → p < D.P → ∀ j ∈ Icc (D.jj p) (D.jj p + 1), D.psiHat h p j = D.psiHat h (p + 1) j) ∧
    (∀ j ∈ Icc (0 : ℤ) D.NR, ∃ p ∈ Icc 1 D.P,
      |ψ j - D.psiHat h p j| ≤ |lam| * (mvC cs.cm cs.CE ((cs.KA + cs.KB) * cs.Kw) cs.Λ D.P
        * (2 * cs.KD * cs.Kw * h ^ m * D.theta h) * D.W j * D.M j)) := by
  have hrA : (D.rescale1 lam).A = D.A := rfl
  have hrQ : (D.rescale1 lam).Q = D.Q := rfl
  have hrs0 : (D.rescale1 lam).s0 = D.s0 := rfl
  have hrNR : (D.rescale1 lam).NR = D.NR := rfl
  have hrP : (D.rescale1 lam).P = D.P := rfl
  have hrW : (D.rescale1 lam).W = D.W := rfl
  have hrM : (D.rescale1 lam).M = D.M := rfl
  have hst := LadderData.stability (D.rescale1 lam) cs h m hV (fun n => lam⁻¹ * ψ n)
    (by
      intro k hk
      rw [hrA, hrQ, Lh_smul, hsol k (by rw [hrs0, hrNR] at hk; exact hk), mul_zero])
    (by
      intro j hj
      rw [hrs0] at hj
      rw [phi_rescale1_one_zero, hseed j hj])
    (by rw [rescale1_theta]; exact hsmall)
  obtain ⟨c1, c2, c3⟩ := hst
  have hconv : ∀ (p : ℕ), 1 ≤ p → ∀ j : ℤ, ∀ B : ℝ,
      |lam⁻¹ * ψ j - (D.rescale1 lam).psiHat h p j| ≤ B → |ψ j - D.psiHat h p j| ≤ |lam| * B := by
    intro p hp j B hB
    rw [psiHat_rescale1 D lam h hp, ← mul_sub, abs_mul, abs_inv] at hB
    have hpos : 0 < |lam| := abs_pos.mpr hlam
    have := mul_le_mul_of_nonneg_left hB hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · intro p hp j hj
    have := c1 p (by rw [hrP]; exact hp) j (by simpa [eqLo, rescale1_jj, hrs0] using hj)
    simp only [hrP, hrW, hrM, rescale1_theta] at this
    exact hconv p (mem_Icc.mp hp).1 j _ this
  · intro p hp1 hpP j hj
    have h1 := c2 p hp1 (by rw [hrP]; exact hpP) j (by rw [rescale1_jj]; exact hj)
    rw [psiHat_rescale1 D lam h hp1, psiHat_rescale1 D lam h (by omega)] at h1
    exact mul_left_cancel₀ (inv_ne_zero hlam) h1
  · intro j hj
    obtain ⟨p, hp, hb⟩ := c3 j (by rw [hrNR]; exact hj)
    refine ⟨p, by rw [hrP] at hp; exact hp, ?_⟩
    simp only [hrP, hrW, hrM, rescale1_theta] at hb
    exact hconv p (mem_Icc.mp (by rw [hrP] at hp; exact hp)).1 j _ hb

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.LadderData.stability_rescale1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.LadderData.stability_rescale1

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.LadderData.psiHat_rescale1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.LadderData.psiHat_rescale1

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.LadderData.transMat_zero_zero_eq_cas_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.LadderData.transMat_zero_zero_eq_cas_div

end LadderData

end FormalResearch.JacobiEigenvectors.Charts
