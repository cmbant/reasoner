module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftRescale
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftWeights
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftTransfer

/-!
# Paper J, Layer 2 (L2.C6): the solution through the soft edge, `prop:tha-W2` item (1) -- what is proved

Source: Paper J `thmA.tex` `prop:tha-W2` (1); `app_thmA.tex` "The soft edges: proof of Proposition prop:tha-W2", Steps 1--3; `charts.tex` `thm:cha-PC`; `engine.tex` `thm:eng-volterra` and the
paragraph on the forbidden overlap.  Statement being proved: `TheoremA.PropThaW2` (item (1)); structure: `Charts.SoftEdgeChart` (**corrected in round 3**, see its docstring for the verdicts on the findings
F-W2-1..7 of the first attempt: the chain is now three patches, the validity hypothesis is for the *rescaled* chain, there is a separate Step-1 Weber chart `chainW`).

## What is proved (all in this file unless stated)

1. (engine, `SoftRescale.lean`) the reciprocal rescaling `(lam^{-1}, lam)` of the first patch and `stability_rescale1`.
2. `softLam_pos`, `kappaBal_pos`, the weights `W_k = E_Web(k)/lambda` and `W(j_1) = E_-(j_1)` of the chain; `lamL_eq_kappa_mul_transMat`: `lambda_L = kappa_bal (M_1^{orig})_{11}`;
   `psiHatL_of_le`, `psiHatL_of_gt`, `chain_phi_one_eq` (the Weber part of `psi-hat^L` is the first patch of the chain).
3. `soft_through_edge` (**the corrected L2.C6, engine part**): from `SoftEdgeChart.valid` (the rescaled chain) and `validW` and `1 <= m`, there are `Cc, h0` (depending on `cs`, `Csum`, `eta`, `m` only) such that for `h <= h0`, uniformly in `(p, X, N, psi)`,
   `0 < lambda`, `|lambda_L| <= Lambda lambda kappa_bal`, and the exact solution `psi` seeded by `psi-hat^L_0` satisfies
   (a) **the Weber bound on all rows `u_k <= u_c - eta/2`** (first bound of `eq:tha-W2-1`: `Cc h^m E_Web M_Web`; Step 1, through `chainW`);
   (b') the **pre-absorption** bound on the PC rows of patch 2 (`j_1 < k <= j_2`, `u_k > u_c - eta/2`): `|psi_k - psi-hat^L_k| <= lambda M_bal (Cc h^m E_-(k) + Lambda K E_-(j_1)^2 / E_-(k))`;
   (b'') the engine bound on the rows of patch 3 (`j_2 < k <= N_R`, `Z > 0`) against the patch-3 comparison sequence `psi-hat_3`: `|psi_k - psi-hat_3(k)| <= lambda M_bal Cc h^m E_swap(k)`.

## What was left for `PropThaW2` (1) after this file, and where it is now

* **(R1) absorption** `E_-(Z_{j_1}) <= exp(-c_E/h) E_-(Z)` on `hat Z <= Z <= 0`: `SoftAbsorb.lean` (`Eminus_j1_decay`, `Eminus_j1_small`).
* **(R2) patch 3 against `psi-hat^{PC,-}`**: `SoftOverlap.lean` (`psiHat_three_of_linear`) and `SoftPC.lean` (`soft_tail3`).
* **(R3) `M_Olv` form**: `SoftWeights.lean` (`molv_lower`) and `SoftPC.lean` (`soft_pc_bound`).
* **(R4) lower bound of (c)**: `SoftGrowth.lean` and `SoftLower.lean` (`soft_lamL_lower`).
* **(R5) the derivation of (S3)**: `SoftTransfer.lean` (`soft_valid`).
* The assembled item (1): `SoftItem1.lean` (`propThaW2_item1`).

## Differences from the paper

* `lambda` is a ratio of positive weights (`softLam_pos`), as in the paper.  The conclusion (b'), (b'') is the paper's bound *before* the absorption step and in terms of the engine weights; the conversion to `|lambda_L| M_Olv(a,-Z)` is (R1), (R3).
* (a) is stated on every row `0 <= k <= N_R` with `u_k <= u_c - eta/2` (all of them are rows of `chainW`).
* the three-patch chain has `P = 3` for every `a` (for `a > 0` patch 3 duplicates patch 2); the engine constant is `mvC ... 3`.

## Not formalised

Items (2)--(4) of `PropThaW2` (L2.C7).
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

lemma k2_nonneg (a z : ℝ) : 0 ≤ k2 a z := le_max_of_le_left (abs_nonneg _)

lemma Mbal_nonneg (a z : ℝ) : 0 ≤ Mbal a z := Real.rpow_nonneg (k2_nonneg a z) _

section SoftChain

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

lemma softEnvWebW_pos (p : Par × ℝ) (X : ℝ) (N : ℕ) (k : ℤ) : 0 < softEnvWebW C p X N k :=
  Ewell_pos _ _

lemma softEnvWeb_nonneg (p : Par × ℝ) (X : ℝ) (N : ℕ) (k : ℤ) : 0 ≤ softEnvWeb C p X N k :=
  mul_nonneg (Ewell_pos _ _).le (Mbal_nonneg _ _)

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

/-- The first patch of the soft chain is the Weber patch of `chainW`: the comparison pairs agree on all rows (`patch1_eq`). -/
lemma chain_phi_one_eq {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
    (α : Fin 2) (k : ℤ) :
    (C.chain p X N).phi (Fz.step N) α 1 k = (C.chainW p X N).phi (Fz.step N) α 1 k := by
  obtain ⟨-, -, -, -, -, -, hwf, hAA, hBB⟩ := C.patch1_eq p hp X hX N hN
  unfold LadderData.phi
  rw [hwf, hAA, hBB]

lemma psiHatL_of_le (p : Par × ℝ) (X : ℝ) (N : ℕ) {n : ℤ} (hn : uNode (Fz.step N) n ≤ C.uc p - C.η / 2) :
    C.psiHatL p X N n = (C.chainW p X N).phi (Fz.step N) 0 1 n := by
  unfold SoftEdgeChart.psiHatL
  simp only [hn, ↓reduceIte]

lemma psiHatL_of_gt (p : Par × ℝ) (X : ℝ) (N : ℕ) {n : ℤ} (hn : C.uc p - C.η / 2 < uNode (Fz.step N) n) :
    C.psiHatL p X N n = C.lamL p X N * ((C.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (C.aOf p X N)) := by
  unfold SoftEdgeChart.psiHatL
  simp only [not_le.mpr hn, ↓reduceIte]

/-- `lambda_L = kappa_bal (M_1^{orig})_{11}`: the Casoratian definition of `lambda_L` is `kappa_bal` times the `(0,0)` entry of the first transfer matrix of the (unrescaled) chain,
provided `A_{j_1} != 0`. -/
lemma lamL_eq_kappa_mul_transMat (p : Par × ℝ) (X : ℝ) (N : ℕ) (hA : (C.chain p X N).A (C.j1 p X N) ≠ 0) :
    C.lamL p X N = kappaBal (C.aOf p X N) *
      transMat ((C.chain p X N).phi (Fz.step N) 0) ((C.chain p X N).phi (Fz.step N) 1) (C.chain p X N).jj 1 0 0 := by
  rw [LadderData.transMat_zero_zero_eq_cas_div ((C.chain p X N).phi (Fz.step N) 0) ((C.chain p X N).phi (Fz.step N) 1)
    (C.chain p X N).jj 1 (C.chain p X N).A hA]
  unfold SoftEdgeChart.lamL
  simp only [SoftEdgeCore.j1]
  have e : cas (C.chain p X N).A (fun n => (C.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (C.aOf p X N))
        ((C.chain p X N).phi (Fz.step N) 1 2) ((C.chain p X N).jj 1)
      = cas (C.chain p X N).A ((C.chain p X N).phi (Fz.step N) 0 2) ((C.chain p X N).phi (Fz.step N) 1 2) ((C.chain p X N).jj 1)
          / kappaBal (C.aOf p X N) := by
    unfold cas
    ring
  rw [e, div_div_eq_mul_div]
  show _ = kappaBal (C.aOf p X N) * (_ / _)
  ring

/-! ### Smallness and constants (common to the Weber chart and the soft chain) -/

/-- the engine constant `K = (K_A + K_B) K_w`. -/
def softK : ℝ := (C.cs.KA + C.cs.KB) * C.cs.Kw

/-- `M_0 = 2 K_D K_w C_sum`: the smallness `2 K_D K_w h^m Theta <= M_0 h^m`. -/
def softM0 : ℝ := 2 * C.cs.KD * C.cs.Kw * C.Csum

/-- the engine constant of the chain with `P` patches, `mvC * (2 K_D K_w C_sum)`, with the derived transfer constant `softLamC`. -/
def softC (P : ℕ) : ℝ := mvC C.cs.cm C.cs.CE (softK C) C.softLamC P * softM0 C

/-- a threshold `h_1(eps)` with `h Lm(h) <= eps` for `0 < h <= h_1` (from the chart field `Lm_small`; `1` if `eps <= 0`). -/
def softHL (ε : ℝ) : ℝ := if hε : 0 < ε then Classical.choose (C.Lm_small ε hε) else 1

lemma softHL_pos (ε : ℝ) : 0 < softHL C ε := by
  unfold softHL
  split_ifs with hε
  · exact (Classical.choose_spec (C.Lm_small ε hε)).1
  · exact one_pos

lemma softHL_spec {ε : ℝ} (hε : 0 < ε) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ softHL C ε) : h * Lm h ≤ ε := by
  unfold softHL at hh1
  rw [dif_pos hε] at hh1
  exact (Classical.choose_spec (C.Lm_small ε hε)).2 h hh hh1

/-- the engine smallness level `c_*/(M_0 + 1)` for `h Lm(h)`. -/
def softE0 : ℝ := mvCstar C.cs.cm C.cs.CE (softK C) / (softM0 C + 1)

/-- the smallness threshold `h_0 = min(eta, 1, h_1(c_*/(M_0 + 1)))` (so that `h Lm(h) <= c_*/(M_0 + 1)`). -/
def softH0 : ℝ := min C.η (min 1 (softHL C (softE0 C)))

lemma softK_nonneg : 0 ≤ softK C := mul_nonneg (add_nonneg C.cs.KA_nonneg C.cs.KB_nonneg) C.cs.Kw_nonneg

lemma softM0_nonneg : 0 ≤ softM0 C :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) C.cs.KD_nonneg) C.cs.Kw_nonneg) C.consts_pos.2.2.2.2.2.2.1

lemma mvCstar_pos' : 0 < mvCstar C.cs.cm C.cs.CE (softK C) := by
  have hq : 0 ≤ 1 + C.cs.CE ^ 2 := by positivity
  have hcmq : 0 ≤ (1 + C.cs.CE ^ 2) / C.cs.cm := div_nonneg hq C.cs.cm_pos.le
  unfold mvCstar
  have h1 : 0 ≤ 2 * ((1 + C.cs.CE ^ 2) / C.cs.cm) * softK C :=
    mul_nonneg (mul_nonneg (by norm_num) hcmq) (softK_nonneg C)
  exact div_pos one_pos (by linarith)

lemma softE0_pos : 0 < softE0 C := div_pos (mvCstar_pos' C) (by linarith [softM0_nonneg C])

lemma softH0_pos : 0 < softH0 C :=
  lt_min C.consts_pos.2.1 (lt_min one_pos (softHL_pos C _))

include C in
lemma Lm_nonneg {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) : 0 ≤ Lm h := by linarith [C.Lm_one h hh hh1]

include C in
/-- `h^m Lm(h) <= h Lm(h)` for `h <= 1`, `m >= 1`. -/
lemma pow_Lm_le {h : ℝ} (hm : 1 ≤ m) (hh : 0 < h) (hh1 : h ≤ 1) : h ^ m * Lm h ≤ h * Lm h :=
  mul_le_mul_of_nonneg_right (pow_le_of_le_one hh.le hh1 (by omega)) (Lm_nonneg C hh hh1)

lemma mvC_nonneg' (n : ℕ) : 0 ≤ mvC C.cs.cm C.cs.CE (softK C) C.softLamC n := by
  have hq : 0 ≤ 1 + C.cs.CE ^ 2 := by positivity
  have hcmq : 0 ≤ (1 + C.cs.CE ^ 2) / C.cs.cm := div_nonneg hq C.cs.cm_pos.le
  have hΛ : 0 ≤ C.softLamC := by linarith [C.softLamC_ge]
  unfold mvC mvCrStar mvKappa
  have hR : 0 ≤ (C.softLamC * (1 + C.cs.CE ^ 2)) ^ n * (1 + C.cs.CE ^ 2) :=
    mul_nonneg (pow_nonneg (mul_nonneg hΛ hq) n) hq
  have hκ : 0 ≤ (2 * C.softLamC ^ 2 * (1 + C.cs.CE ^ 2) + 1) ^ n + 1 := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcmq) (softK_nonneg C))
    (mul_nonneg (mul_nonneg (softK_nonneg C) hR) hκ)

lemma softC_nonneg (n : ℕ) : 0 ≤ softC C n := mul_nonneg (mvC_nonneg' C n) (softM0_nonneg C)

/-- the engine smallness `2 K_D K_w h^m Theta <= c_*` for `h <= h_0`, `Theta <= C_sum Lm(h)`, `m >= 1`. -/
lemma soft_small (hm : 1 ≤ m) {h θ : ℝ} (hh : 0 < h) (hh0 : h ≤ softH0 C) (hθ : θ ≤ C.Csum * Lm h) :
    2 * C.cs.KD * C.cs.Kw * h ^ m * θ ≤ mvCstar C.cs.cm C.cs.CE (softK C) := by
  have hE : 0 ≤ 2 * C.cs.KD * C.cs.Kw := mul_nonneg (mul_nonneg (by norm_num) C.cs.KD_nonneg) C.cs.Kw_nonneg
  have hM0 := softM0_nonneg C
  have hDst := mvCstar_pos' C
  have hh1 : h ≤ 1 := le_trans hh0 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hLs : h * Lm h ≤ softE0 C := softHL_spec C (softE0_pos C) hh (le_trans hh0 (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hden : 0 < softM0 C + 1 := by linarith
  have h1 : 2 * C.cs.KD * C.cs.Kw * h ^ m * θ ≤ 2 * C.cs.KD * C.cs.Kw * h ^ m * (C.Csum * Lm h) :=
    mul_le_mul_of_nonneg_left hθ (mul_nonneg hE (pow_nonneg hh.le m))
  have h2 : 2 * C.cs.KD * C.cs.Kw * h ^ m * (C.Csum * Lm h) ≤ softM0 C * (h * Lm h) := by
    calc 2 * C.cs.KD * C.cs.Kw * h ^ m * (C.Csum * Lm h) = softM0 C * (h ^ m * Lm h) := by unfold softM0; ring
      _ ≤ softM0 C * (h * Lm h) := mul_le_mul_of_nonneg_left (pow_Lm_le C hm hh hh1) hM0
  have h3 : softM0 C * (h * Lm h) ≤ mvCstar C.cs.cm C.cs.CE (softK C) := by
    have hs := mul_le_mul_of_nonneg_left hLs hM0
    have hfrac : softM0 C * softE0 C ≤ mvCstar C.cs.cm C.cs.CE (softK C) := by
      unfold softE0
      rw [mul_div_assoc', div_le_iff₀ hden]
      nlinarith [hDst]
    linarith
  linarith

/-- `h_0 <= eta` and `h_0 <= 1`. -/
lemma softH0_le_eta : softH0 C ≤ C.η := min_le_left _ _

lemma softH0_le_one : softH0 C ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)

/-- the exact solution with the Weber seed is a solution of the chain's recurrence on the rows `s_0 .. N_R - 1` of any chain whose operator is the family's. -/
lemma sol_chain_rows {p : Par × ℝ} {X : ℝ} {N : ℕ} (D : LadderData) (hs0 : D.s0 = 0)
    (hA : ∀ k ∈ Finset.Icc (-1 : ℤ) D.NR, D.A k = Fz.bondA p N k)
    (hQ : ∀ k ∈ Finset.Icc (0 : ℤ) D.NR, D.Q k = Fz.diagQ p N X k)
    {NR : ℤ} (hle : D.NR ≤ NR) {ψ : ℤ → ℝ} (hJ : JacSol Fz p N X NR ψ) :
    ∀ j ∈ Icc D.s0 (D.NR - 1), Lh (Fz.step N) D.A D.Q ψ j = 0 := by
  intro j hj
  rw [hs0] at hj
  obtain ⟨hj0, hj1⟩ := mem_Icc.mp hj
  have hL : Lop (Fz.bondA p N) (Fz.diagQ p N X) ψ j = 0 := hJ j hj0 (by omega)
  have hA0 : D.A j = Fz.bondA p N j := hA j (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hA1 : D.A (j - 1) = Fz.bondA p N (j - 1) := hA (j - 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hQ0 : D.Q j = Fz.diagQ p N X j := hQ j (mem_Icc.mpr ⟨hj0, by omega⟩)
  rw [Lh_congr_site hA0 hA1 hQ0]
  unfold Lh
  rw [hL, mul_zero]

/-- the engine constant times the smallness factor is at most `softC * (h^m Lm(h))`. -/
lemma soft_engine_le (n : ℕ) {h θ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hθ : θ ≤ C.Csum * Lm h) :
    mvC C.cs.cm C.cs.CE (softK C) C.softLamC n * (2 * C.cs.KD * C.cs.Kw * h ^ m * θ) ≤ softC C n * (h ^ m * Lm h) := by
  have hE : 0 ≤ 2 * C.cs.KD * C.cs.Kw := mul_nonneg (mul_nonneg (by norm_num) C.cs.KD_nonneg) C.cs.Kw_nonneg
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hθ (mul_nonneg hE (pow_nonneg hh.le m)))
    (mvC_nonneg' C n)
  calc _ ≤ mvC C.cs.cm C.cs.CE (softK C) C.softLamC n * (2 * C.cs.KD * C.cs.Kw * h ^ m * (C.Csum * Lm h)) := this
    _ = softC C n * (h ^ m * Lm h) := by unfold softC softM0; ring

include C in
/-- `0 <= h^m Lm(h)` for `0 < h <= 1`. -/
lemma powLm_nonneg {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) : 0 ≤ h ^ m * Lm h :=
  mul_nonneg (pow_nonneg hh.le m) (Lm_nonneg C hh hh1)

end SoftChain

/-! ### Step 1: the Weber bound on all rows `u_k <= u_c - eta/2` -/

section Step1

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- the first row of the lattice is inside the Weber region: `u_0 <= u_c - eta/2` once `h <= eta`. -/
lemma uNode_zero_le {p : Par × ℝ} (hp : p ∈ P) {N : ℕ} (hstep : Fz.step N ≤ C.η) :
    uNode (Fz.step N) 0 ≤ C.uc p - C.η / 2 := by
  have huc := (C.ucη_in p hp).1
  have hη := C.consts_pos.2.1
  unfold uNode
  simp only [Int.cast_zero, zero_add]
  linarith

/-- **Step 1** (`app_thmA` Step 1, `cor:cha-I-general`): the exact solution seeded by `psi-hat^L_0` obeys `|psi_k - psi-hat^L_k| <= C h^m E_Web M_Web` on every row `0 <= k <= N_R` with `u_k <= u_c - eta/2`. -/
theorem soft_weber_bound (hm : 1 ≤ m) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ}
    (hN : C.N0 ≤ N) (hstep : Fz.step N ≤ softH0 C) (ψ : ℤ → ℝ) (hJ : JacSol Fz p N X (C.chain p X N).NR ψ)
    (hseed0 : ψ 0 = C.psiHatL p X N 0) :
    ∀ k ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, uNode (Fz.step N) k ≤ C.uc p - C.η / 2 →
      |ψ k - C.psiHatL p X N k| ≤ softC C 1 * (Fz.step N ^ m * Lm (Fz.step N)) * softEnvWeb C p X N k := by
  intro k hk hku
  obtain ⟨hk0, hkNR⟩ := mem_Icc.mp hk
  have hstep_pos : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hη := C.consts_pos.2.1
  have hVW := C.validW p hp X hX N hN
  obtain ⟨hP1, hs0, hNR0, hNRu, hNRv⟩ := C.shapeW p hp X hX N hN
  obtain ⟨-, -, -, -, -, -, hNRmu, hNRmv⟩ := C.shape p hp X hX N hN
  set DW := C.chainW p X N with hDW
  have hkW : k ≤ DW.NR := by
    by_contra hcon
    have h1 : DW.NR + 1 ≤ k := by omega
    have := uNode_mono' hstep_pos.le h1
    linarith
  have hNRle : DW.NR ≤ (C.chain p X N).NR := by
    by_contra hcon
    have h1 : (C.chain p X N).NR + 1 ≤ DW.NR := by omega
    have := uNode_mono' hstep_pos.le h1
    linarith
  have hsol := sol_chain_rows DW hs0 (C.A_bondW p hp X hX N hN) (C.Q_diagW p hp X hX N hN) hNRle hJ
  have hseed : ∀ j ∈ Icc (0 : ℤ) DW.s0, ψ j = DW.phi (Fz.step N) 0 1 j := by
    intro j hj
    rw [hs0] at hj
    have hj0 : j = 0 := by
      obtain ⟨h1, h2⟩ := mem_Icc.mp hj
      omega
    subst hj0
    rw [hseed0, psiHatL_of_le C p X N (uNode_zero_le C hp (le_trans hstep (softH0_le_eta C)))]
  have hθ : DW.theta (Fz.step N) ≤ C.Csum * Lm (Fz.step N) := C.theta_leW p hp X hX N hN
  have hstep1' : Fz.step N ≤ 1 := hstep.trans (softH0_le_one C)
  have hsmall := soft_small C hm hstep_pos hstep hθ
  have hVW' : DW.Valid C.csT (Fz.step N) m :=
    hVW.toPreValid.toValid C.softLamC C.softLamC_ge (fun p hp1 hp2 => by
      have hl := hVW.jj_last
      rw [hP1] at hp2
      omega)
  have hst := LadderData.stability DW C.csT (Fz.step N) m hVW' ψ hsol hseed hsmall
  obtain ⟨c1, -, -⟩ := hst
  have hkw : k ∈ Icc (eqLo DW.s0 DW.jj 1) (DW.jj 1 + 1) := by
    have hl : DW.jj DW.P = DW.NR - 1 := hVW.jj_last
    rw [hP1] at hl
    rw [eqLo_one, hs0]
    exact mem_Icc.mpr ⟨hk0, by omega⟩
  have h1 := c1 1 (mem_Icc.mpr ⟨le_rfl, by show 1 ≤ DW.P; omega⟩) k hkw
  rw [hP1] at h1
  have hpsi1 : DW.psiHat (Fz.step N) 1 k = DW.phi (Fz.step N) 0 1 k := by
    unfold LadderData.psiHat Engine.psiHat
    rw [cvec_one]
    simp
  have hψL := psiHatL_of_le C p X N hku
  have hkk : k ∈ Finset.Icc (0 : ℤ) DW.NR := mem_Icc.mpr ⟨hk0, hkW⟩
  have hW := C.W_defW p hp X hX N hN k hkk
  have hM := C.M_defW p hp X hX N hN k hkk
  rw [hψL, ← hpsi1]
  refine le_trans h1 ?_
  rw [hW, hM]
  have hEM : 0 ≤ softEnvWeb C p X N k := softEnvWeb_nonneg C p X N k
  have hEM' : softEnvWeb C p X N k = Ewell (-((k : ℝ) + 1 / 2)) |C.Y p X (uNode (Fz.step N) k) / Real.sqrt (Fz.step N)| *
      Mbal (-((k : ℝ) + 1 / 2)) (C.Y p X (uNode (Fz.step N) k) / Real.sqrt (Fz.step N)) := rfl
  have hA : mvC C.cs.cm C.cs.CE (softK C) C.softLamC 1 * (2 * C.cs.KD * C.cs.Kw * Fz.step N ^ m * DW.theta (Fz.step N))
      ≤ softC C 1 * (Fz.step N ^ m * Lm (Fz.step N)) := soft_engine_le C 1 hstep_pos hstep1' hθ
  rw [mul_assoc, ← hEM']
  exact mul_le_mul_of_nonneg_right hA hEM

end Step1

/-! ### Step 3: through the soft edge (engine part) -/

section Step3

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- **L2.C6 (engine part): the solution through the soft edge** (`prop:tha-W2` (1), `thm:cha-PC`, `app_thmA` Steps 1--3), see the module docstring for what is and is not covered. -/
theorem soft_through_edge {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m) :
    ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ C.δ0 → ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 →
      0 < softLam C p X N ∧
      |C.lamL p X N| ≤ C.softLamC * (softLam C p X N * kappaBal (C.aOf p X N)) ∧
      ∀ ψ : ℤ → ℝ, JacSol Fz p N X (C.chain p X N).NR ψ → ψ 0 = C.psiHatL p X N 0 →
        (∀ k ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, uNode (Fz.step N) k ≤ C.uc p - C.η / 2 →
          |ψ k - C.psiHatL p X N k| ≤ Cc * Fz.step N ^ m * Lm (Fz.step N) * softEnvWeb C p X N k) ∧
        (∀ k ∈ Finset.Icc (C.j1 p X N + 1) (C.j2 p X N), C.uc p - C.η / 2 < uNode (Fz.step N) k →
          |ψ k - C.psiHatL p X N k| ≤ softLam C p X N * Mbal (C.aOf p X N) (C.Zof p X N k) *
            (Cc * Fz.step N ^ m * Lm (Fz.step N) * Eminus (C.aOf p X N) (C.Zof p X N k)
              + C.softLamC * softK C * Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)) ^ 2
                / Eminus (C.aOf p X N) (C.Zof p X N k))) ∧
        (∀ k ∈ Finset.Icc (C.j2 p X N + 1) (C.chain p X N).NR,
          |ψ k - (C.chain p X N).psiHat (Fz.step N) 3 k| ≤ softLam C p X N * Mbal (C.aOf p X N) (C.Zof p X N k) *
            (Cc * Fz.step N ^ m * Lm (Fz.step N) * Eswap (C.aOf p X N) (C.Zof p X N k))) := by
  obtain ⟨-, hη, -, -, -, -, hCsum, -⟩ := C.consts_pos
  set cs := C.csT with hcs
  refine ⟨softC C 1 + softC C 3, min (softH0 C) C.softH1, lt_min (softH0_pos C) C.softH1_pos, ?_⟩
  intro p hp X hX N hN hstep'
  have hstep : Fz.step N ≤ softH0 C := hstep'.trans (min_le_left _ _)
  have hstep1 : Fz.step N ≤ C.softH1 := hstep'.trans (min_le_right _ _)
  have hVpre : ((C.chain p X N).rescale1 (softLam C p X N)).PreValid C.cs (Fz.step N) m := C.valid p hp X hX N hN
  have hV : ((C.chain p X N).rescale1 (softLam C p X N)).Valid cs (Fz.step N) m := C.soft_valid hf hp hX hN hstep1 hVpre
  obtain ⟨hP3, hs0, hj1u, hj1v, hZa, hZb, hNRu, hNRv⟩ := C.shape p hp X hX N hN
  have hθ : (C.chain p X N).theta (Fz.step N) ≤ C.Csum * Lm (Fz.step N) := C.theta_le p hp X hX N hN
  have hstep_pos : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hstep1' : Fz.step N ≤ 1 := hstep.trans (softH0_le_one C)
  have hsmall := soft_small C hm hstep_pos hstep hθ
  have hlam : 0 < softLam C p X N := softLam_pos C p X N
  have hC1 := softC_nonneg C 1
  have hC3 := softC_nonneg C 3
  set D := C.chain p X N with hD
  set lam := softLam C p X N with hlamdef
  have hj1D : C.j1 p X N = D.jj 1 := rfl
  have hj2D : C.j2 p X N = D.jj 2 := rfl
  have hjj0' : 0 ≤ D.jj 1 := hV.jj_nonneg (by show 1 ≤ D.P; omega)
  have hjj12 : D.jj 1 < D.jj 2 := hV.jj_mono 1 (by show 1 < D.P; omega)
  have hjj23 : D.jj 2 < D.jj 3 := hV.jj_mono 2 (by show 2 < D.P; omega)
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
  intro ψ hJ hseed0
  have hCc : softC C 1 ≤ softC C 1 + softC C 3 := le_add_of_nonneg_right hC3
  have hCc3 : softC C 3 ≤ softC C 1 + softC C 3 := le_add_of_nonneg_left hC1
  have hpow := powLm_nonneg C hstep_pos hstep1'
  -- the exact solution satisfies the engine's equations
  have hsol := sol_chain_rows D hs0 (C.A_bond p hp X hX N hN) (C.Q_diag p hp X hX N hN) le_rfl hJ
  have hseed : ∀ j ∈ Icc (0 : ℤ) D.s0, ψ j = D.phi (Fz.step N) 0 1 j := by
    intro j hj
    rw [hs0] at hj
    have hj0 : j = 0 := by
      obtain ⟨h1, h2⟩ := mem_Icc.mp hj
      omega
    subst hj0
    rw [hseed0, psiHatL_of_le C p X N (uNode_zero_le C hp (le_trans hstep (softH0_le_eta C))),
      chain_phi_one_eq C hp hX hN]
  have hst := LadderData.stability_rescale1 D cs (Fz.step N) m lam hlam.ne' hV ψ hsol hseed hsmall
  obtain ⟨c1, -, -⟩ := hst
  have hjl : D.jj 3 = D.NR - 1 := by
    have := hV.jj_last
    change D.jj D.P = D.NR - 1 at this
    rw [hP3] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · -- (a): Weber bound on all rows `u_k <= u_c - eta/2`
    intro k hk hku
    refine le_trans (soft_weber_bound C hm hp hX hN hstep ψ hJ hseed0 k hk hku) ?_
    have h1 : softC C 1 * (Fz.step N ^ m * Lm (Fz.step N)) ≤ (softC C 1 + softC C 3) * Fz.step N ^ m * Lm (Fz.step N) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hCc hpow
    exact mul_le_mul_of_nonneg_right h1 (softEnvWeb_nonneg C p X N k)
  · -- (b'): the collar bound before absorption, patch 2
    intro k hk hkuc
    obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
    rw [hj1D] at hk1
    rw [hj2D] at hk2
    have e1 : eqLo D.s0 D.jj 2 = D.jj 1 + 1 := eqLo_succ D.s0 D.jj 1 le_rfl
    have hkw : k ∈ Icc (eqLo D.s0 D.jj 2) (D.jj 2 + 1) := by
      rw [e1]
      exact mem_Icc.mpr ⟨hk1, by omega⟩
    have hp2 : 2 ∈ Icc 1 D.P := mem_Icc.mpr ⟨by norm_num, by omega⟩
    have h1 := c1 2 hp2 k hkw
    rw [hP3] at h1
    have hkNR : k ∈ Finset.Icc (D.jj 1 + 1) D.NR := mem_Icc.mpr ⟨hk1, by omega⟩
    have hkW2 : k ∈ Finset.Icc (D.jj 1 + 1) (D.jj 2) := mem_Icc.mpr ⟨hk1, hk2⟩
    have hW : D.W k = Eminus (C.aOf p X N) (C.Zof p X N k) := C.W2_def p hp X hX N hN k hkW2
    have hM : D.M k = Mbal (C.aOf p X N) (C.Zof p X N k) := C.M2_def p hp X hX N hN k hkNR
    have hk0 : 0 ≤ k := by omega
    have hWk : 0 < D.W k := hV.W_pos k (mem_Icc.mpr ⟨hk0, by show k ≤ D.NR; omega⟩)
    have hMk : 0 < D.M k := hV.M_pos k (mem_Icc.mpr ⟨hk0, by show k ≤ D.NR; omega⟩)
    have hψL := psiHatL_of_gt C p X N hkuc
    have hpsi2 := LadderData.psiHat_two D (Fz.step N) k
    have hdecomp : ψ k - C.psiHatL p X N k
        = (ψ k - D.psiHat (Fz.step N) 2 k)
          + transMat (D.phi (Fz.step N) 0) (D.phi (Fz.step N) 1) D.jj 1 1 0 * D.phi (Fz.step N) 1 2 k := by
      rw [hψL, hpsi2, hlamL]
      field_simp
      ring
    -- the envelope of the second member of the second pair
    have hwin : k ∈ Icc (D.jj (2 - 1)) (D.jj 2 + 1) := by
      exact mem_Icc.mpr ⟨by show D.jj 1 ≤ k; omega, by omega⟩
    have hb := (hV.phi_bd (p := 2) hp2 hwin).2
    rw [hphi2] at hb
    have hb' : |D.phi (Fz.step N) 1 2 k| ≤ softK C * (D.W k)⁻¹ * D.M k := hb
    have hWj := chain_W_j1 C hp hX hN hjj0'
    have hbM : |transMat (D.phi (Fz.step N) 0) (D.phi (Fz.step N) 1) D.jj 1 1 0| ≤ lam * (cs.Λ * D.W (D.jj 1) ^ 2) := by
      rw [hM10, abs_mul, abs_of_pos hlam]
      exact mul_le_mul_of_nonneg_left t10' hlam.le
    have hterm : |transMat (D.phi (Fz.step N) 0) (D.phi (Fz.step N) 1) D.jj 1 1 0 * D.phi (Fz.step N) 1 2 k|
        ≤ lam * (cs.Λ * D.W (D.jj 1) ^ 2) * (softK C * (D.W k)⁻¹ * D.M k) := by
      rw [abs_mul]
      exact mul_le_mul hbM hb' (abs_nonneg _) (mul_nonneg hlam.le (mul_nonneg (by linarith [cs.Λ_ge]) (sq_nonneg _)))
    rw [abs_of_pos hlam, hW, hM] at h1
    rw [hdecomp]
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add h1 hterm) ?_
    rw [hW, hM, hWj]
    have hE := Eminus_pos (C.aOf p X N) (C.Zof p X N k)
    have hMb : 0 < Mbal (C.aOf p X N) (C.Zof p X N k) := hM ▸ hMk
    have hBT := soft_engine_le C 3 hstep_pos hstep1' hθ
    have hBT' : mvC cs.cm cs.CE (softK C) cs.Λ 3 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N))
        ≤ (softC C 1 + softC C 3) * ((Fz.step N) ^ m * Lm (Fz.step N)) :=
      le_trans hBT (mul_le_mul_of_nonneg_right hCc3 hpow)
    have e1' : lam * (mvC cs.cm cs.CE (softK C) cs.Λ 3 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N))
          * Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))
        ≤ lam * Mbal (C.aOf p X N) (C.Zof p X N k)
          * ((softC C 1 + softC C 3) * ((Fz.step N) ^ m * Lm (Fz.step N)) * Eminus (C.aOf p X N) (C.Zof p X N k)) := by
      calc _ = lam * Mbal (C.aOf p X N) (C.Zof p X N k)
              * ((mvC cs.cm cs.CE (softK C) cs.Λ 3 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N)))
                  * Eminus (C.aOf p X N) (C.Zof p X N k)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBT' hE.le) (by positivity)
    have e2' : lam * (cs.Λ * Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)) ^ 2)
          * (softK C * (Eminus (C.aOf p X N) (C.Zof p X N k))⁻¹ * Mbal (C.aOf p X N) (C.Zof p X N k))
        = lam * Mbal (C.aOf p X N) (C.Zof p X N k)
          * (cs.Λ * softK C * Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)) ^ 2 / Eminus (C.aOf p X N) (C.Zof p X N k)) := by
      field_simp
    have hΛcs : cs.Λ = C.softLamC := rfl
    calc _ ≤ _ := add_le_add e1' e2'.le
      _ = _ := by rw [hΛcs]; ring
  · -- (b''): the engine bound on the rows of patch 3
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
    rw [hj2D] at hk1
    have e1 : eqLo D.s0 D.jj 3 = D.jj 2 + 1 := eqLo_succ D.s0 D.jj 2 (by norm_num)
    have hkw : k ∈ Icc (eqLo D.s0 D.jj 3) (D.jj 3 + 1) := by
      rw [e1]
      exact mem_Icc.mpr ⟨hk1, by omega⟩
    have hp3 : 3 ∈ Icc 1 D.P := mem_Icc.mpr ⟨by norm_num, by omega⟩
    have h1 := c1 3 hp3 k hkw
    rw [hP3] at h1
    have hkW3 : k ∈ Finset.Icc (D.jj 2 + 1) D.NR := mem_Icc.mpr ⟨hk1, hk2⟩
    have hkM : k ∈ Finset.Icc (D.jj 1 + 1) D.NR := mem_Icc.mpr ⟨by omega, hk2⟩
    have hW : D.W k = Eswap (C.aOf p X N) (C.Zof p X N k) := C.W3_def p hp X hX N hN k hkW3
    have hM : D.M k = Mbal (C.aOf p X N) (C.Zof p X N k) := C.M2_def p hp X hX N hN k hkM
    rw [abs_of_pos hlam, hW, hM] at h1
    refine le_trans h1 ?_
    have hE := Eswap_pos (C.aOf p X N) (C.Zof p X N k)
    have hMb := Mbal_nonneg (C.aOf p X N) (C.Zof p X N k)
    have hBT := soft_engine_le C 3 hstep_pos hstep1' hθ
    have hBT' : mvC cs.cm cs.CE (softK C) cs.Λ 3 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N))
        ≤ (softC C 1 + softC C 3) * ((Fz.step N) ^ m * Lm (Fz.step N)) :=
      le_trans hBT (mul_le_mul_of_nonneg_right hCc3 hpow)
    calc lam * (mvC cs.cm cs.CE (softK C) cs.Λ 3 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N))
          * Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))
        = lam * Mbal (C.aOf p X N) (C.Zof p X N k)
          * ((mvC cs.cm cs.CE (softK C) cs.Λ 3 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * D.theta (Fz.step N)))
              * Eswap (C.aOf p X N) (C.Zof p X N k)) := by ring
      _ ≤ lam * Mbal (C.aOf p X N) (C.Zof p X N k)
          * ((softC C 1 + softC C 3) * ((Fz.step N) ^ m * Lm (Fz.step N)) * Eswap (C.aOf p X N) (C.Zof p X N k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBT' hE.le) (by positivity)
      _ = _ := by ring

end Step3

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_through_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.soft_through_edge

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_weber_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.soft_weber_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.lamL_eq_kappa_mul_transMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.lamL_eq_kappa_mul_transMat

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcSwap_eq_pcMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.pcSwap_eq_pcMinus

end FormalResearch.JacobiEigenvectors.TheoremA
