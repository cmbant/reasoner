module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftSigns
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftCountHyps
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly6

/-!
# Paper J, Layer 2 (L2.C7): the sign analysis of app_thmA Step 6, part 2: hypothesis (ii) of `lem:tha-count` on the soft chart

Source: `app_thmA.tex`, proof of prop:tha-W2, Step 6, item "(ii)": at `a = -k` evaluate the Casoratian `W(psi^L, psi^R)` at a site with `Z_n ~ c eta h^{-1/2}`, using the connection
formula `eq:tha-connectPC` for `psi^L` and item (1) for `psi^R`; the growing term has the sign `cos(pi a) = (-1)^k` times a constant sign.

## What is proved (all axiom-pinned)

* `soft_row_data`: at a row `j` of patch 3 on the right forbidden side (`Z_j > 0`, `u_c + 3 eta/8 <= u_j < u_c + eta/2`) the exact left solution `psi^L` (seeded by `psi-hat^L_0`) satisfies
  `psi-hat^L_j = mu (cc f_j + sc g_j)` (`mu = lambda_L/kappa_b`, `cc = sqrt(2/pi) cos(pi a)` or `1`, `sc = sin(pi a)` or `0`, `f = phi^{(1)}_3`, `g = phi^{(2)}_3` the swapped pair, `phi_swap_rel`),
  `|g_j| <= K e_j M_j` and `|psi^L_j - psi-hat^L_j| <= |mu| C_h e_j^{-1} M_j` (item (1)) -- the rows facts of `soft_quant`, extracted.
* `soft_qZ_decay`: the exact right solution `psi^R_n = c_0' q_n` is positive and decaying on the right forbidden side: `0 < q_{k+1}`, `(1 + nu') q_{k+1} <= q_k` at a bond `(k, k+1)` with `u_{k+1} >= u_c + eta/4`
  (`growth_ratio` for the mirror chart `CR` and `CR.grow_gap`; this is the paper's "item (1) for `psi^R`", used only for its sign and ratio).
* `sign_cc`: `(-1)^k cc(a) >= 1/4` for `|a + k| <= 1/pi`.
* `soft_sign_at`: for `|a + k| <= C' h` (`C' = (q/2) C_mu`), `sign casD(X) = sign (lambda_L(X) (-1)^k)`.
* `soft_sign_D` (= hypothesis (ii) of `SoftCountHyps`, as a stand-alone statement): there is `sigma = +-1` (the constant sign of `lambda_L` on the energy window: `lamL_cont`, `soft_lamL_lower`, `sign_const_of_cont`)
  with `sign casD(X) = sign (sigma (-1)^k)` whenever `|X - bandHi| <= delta_0` and `pi mu_0(bandHi - X) = pi h k`.

## Differences from the paper

* The paper compares the growing term `sqrt(2/pi) cos(pi a) lambda_L lambda_R kappa_b^{-2} W(A v~ + .., A u~ + ..)` with the recessive-recessive terms and the errors, using the corrected pair of *both* charts.
  Here the right solution enters only through its exact sign and decay (`growth_ratio` of the mirror family: `psi^R_k > 0`, `psi^R_{k+1} <= psi^R_k/(1+nu')`), and the left one through `f` (the chart field `grow3`:
  positivity, lower bound `c_gr W M` and monotonicity `f_k <= (1 + C_gr h) f_{k+1}`).  The Casoratian `W(psi^L, psi^R)(k, k+1) = A_k (psi^L_{k+1} psi^R_k - psi^L_k psi^R_{k+1})` then has the sign of
  `psi^L_k`.  This avoids the cross-chart comparison of the correctors `A^{[m]}, B^{[m]}` of the two charts.
* `Phi = pi mu_0` and `a = -k + O(h)` (`|a + k| <= C' h`, `|mu-tilde - mu_0| <= C' h^2`), not `a = -k` exactly (`sin(pi a) = O(h)` is absorbed by `f >> g`).
* The sign `sigma` is the constant sign of `lambda_L` on the window (not `+1`), which depends on `(p, N)`; that is all `lem:tha-count` needs.

## Not formalised

Nothing of Step 6 (ii).  (The chart fields `lamL_cont`, `grow3` are new inputs: F-W2-19, F-W2-20.)
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

/-- the coefficient of `f` in `psi-hat^L` on patch 3: `sqrt(2/pi) cos(pi a)` (`a <= 0`) or `1`. -/
def ccOf (a : ℝ) : ℝ := if a ≤ 0 then Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * a) else 1

/-- the coefficient of `g` in `psi-hat^L` on patch 3: `sin(pi a)` (`a <= 0`) or `0`. -/
def scOf (a : ℝ) : ℝ := if a ≤ 0 then Real.sin (Real.pi * a) else 0

lemma abs_scOf_le {a : ℝ} {k : ℕ} {t : ℝ} (h : |a + k| ≤ t) : |scOf a| ≤ Real.pi * t := by
  unfold scOf
  split_ifs with ha
  · have e : Real.sin (Real.pi * a) = (-1) ^ k * Real.sin (Real.pi * (a + k)) := by
      have : Real.pi * a = Real.pi * (a + k) - (k : ℝ) * Real.pi := by ring
      rw [this, Real.sin_sub_nat_mul_pi]
    rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    calc |Real.sin (Real.pi * (a + k))| ≤ |Real.pi * (a + k)| := Real.abs_sin_le_abs
      _ = Real.pi * |a + k| := by rw [abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ Real.pi * t := mul_le_mul_of_nonneg_left h Real.pi_pos.le
  · rw [abs_zero]
    have : 0 ≤ t := le_trans (abs_nonneg _) h
    positivity

/-- `(-1)^k cc(a) >= 1/4` for `|a + k| <= 1/pi` (`k` a natural number). -/
lemma sign_cc {a : ℝ} {k : ℕ} (h : |a + k| ≤ 1 / Real.pi) : 1 / 4 ≤ (-1 : ℝ) ^ k * ccOf a := by
  have hpi := Real.pi_pos
  unfold ccOf
  split_ifs with ha
  · have e : Real.cos (Real.pi * a) = (-1) ^ k * Real.cos (Real.pi * (a + k)) := by
      have : Real.pi * a = Real.pi * (a + k) - (k : ℝ) * Real.pi := by ring
      rw [this, Real.cos_sub_nat_mul_pi]
    have hsq : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    have hcos : 1 / 2 ≤ Real.cos (Real.pi * (a + k)) := by
      have h1 := Real.one_sub_sq_div_two_le_cos (x := Real.pi * (a + k))
      have h2 : |Real.pi * (a + k)| ≤ 1 := by
        rw [abs_mul, abs_of_pos hpi]
        calc Real.pi * |a + k| ≤ Real.pi * (1 / Real.pi) := mul_le_mul_of_nonneg_left h hpi.le
          _ = 1 := by field_simp
      have h3 : (Real.pi * (a + k)) ^ 2 ≤ 1 := by
        have := sq_abs (Real.pi * (a + k))
        nlinarith [abs_nonneg (Real.pi * (a + k))]
      linarith
    have hs : 1 / 2 ≤ Real.sqrt (2 / Real.pi) := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt
      rw [le_div_iff₀ hpi]
      nlinarith [Real.pi_le_four]
    calc (1 : ℝ) / 4 = 1 / 2 * (1 / 2) := by norm_num
      _ ≤ Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * (a + k)) :=
          mul_le_mul hs hcos (by norm_num) (Real.sqrt_nonneg _)
      _ = (-1) ^ k * (Real.sqrt (2 / Real.pi) * ((-1) ^ k * Real.cos (Real.pi * (a + k)))) := by
          rw [← mul_assoc, mul_comm ((-1 : ℝ) ^ k), mul_assoc, ← mul_assoc ((-1 : ℝ) ^ k), hsq, one_mul]
      _ = _ := by rw [e]
  · have hk : k = 0 := by
      by_contra hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have h1 : |a + k| = a + k := abs_of_pos (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith [not_le.mp ha])
      have h2 : a + k ≤ 1 / Real.pi := by rw [← h1]; exact h
      have h3 : 1 / Real.pi < 1 := by
        rw [div_lt_one hpi]; exact Real.pi_gt_three.trans' (by norm_num)
      linarith [not_le.mp ha]
    subst hk
    norm_num

/-! ### The rows `k_0, k_0 + 1` of the left solution -/

section Rows

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- **The row facts of `soft_quant`, extracted** (item (1), the connection formula, the recessive bound on `g`). -/
theorem soft_row_data {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) :
    ∃ Ch0 h0 : ℝ, 0 < h0 ∧ 0 ≤ Ch0 ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      ∀ ψL : ℤ → ℝ, JacSol Fz p N X (CL.chain p X N).NR ψL → ψL 0 = CL.psiHatL p X N 0 →
      ∀ j : ℤ, (CL.chain p X N).jj 2 + 1 ≤ j → j + 1 ≤ (CL.chain p X N).NR + 1 → 0 < CL.Zof p X N j →
        CL.uc p + 3 * CL.η / 8 ≤ uNode (Fz.step N) j → uNode (Fz.step N) j < CL.uc p + CL.η / 2 →
        |(CL.chain p X N).phi (Fz.step N) 1 3 j| ≤
            softK CL * (Eminus (CL.aOf p X N) (-(CL.Zof p X N j)) * Mbal (CL.aOf p X N) (CL.Zof p X N j)) ∧
        |ψL j - CL.psiHatL p X N j| ≤ |CL.lamL p X N / kappaBal (CL.aOf p X N)| * (Ch0 * (Fz.step N ^ m * Lm (Fz.step N))) *
            ((Eminus (CL.aOf p X N) (-(CL.Zof p X N j)))⁻¹ * Mbal (CL.aOf p X N) (CL.Zof p X N j)) ∧
        CL.psiHatL p X N j = CL.lamL p X N / kappaBal (CL.aOf p X N) *
            (ccOf (CL.aOf p X N) * (CL.chain p X N).phi (Fz.step N) 0 3 j + scOf (CL.aOf p X N) * (CL.chain p X N).phi (Fz.step N) 1 3 j) := by
  obtain ⟨Cc, h0a, clam, Clam, h0apos, hclam, Ha⟩ := propThaW2_item1 CL hf hm hLm
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  refine ⟨|Cc| * CPC, min h0a CL.softH2, lt_min h0apos CL.softH2_pos, by positivity, ?_⟩
  intro p hp N hN hstep X hX ψL hJL hseedL j hj1 hj2 hZ hu1 hu2
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs0a : Fz.step N ≤ h0a := hstep.trans (min_le_left _ _)
  have hs2 : Fz.step N ≤ CL.softH2 := hstep.trans (min_le_right _ _)
  have hhH1 : Fz.step N ≤ CL.softH1 := hs2.trans CL.softH2_le_H1
  have hh1 : Fz.step N ≤ 1 := hhH1.trans CL.softH1_le_one
  have hVpre : ((CL.chain p X N).rescale1 (softLam CL p X N)).PreValid CL.cs (Fz.step N) m := CL.valid p hp X hX N hN
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := CL.soft_pos hp hX hN hhH1 hVpre
  obtain ⟨-, hη, -⟩ := CL.consts_pos
  obtain ⟨-, -, -, -, -, -, hNRu, hNRv⟩ := CL.shape p hp X hX N hN
  have hP3' : ((CL.chain p X N).rescale1 (softLam CL p X N)).P = 3 := hP3
  have hj3 : (CL.chain p X N).jj 3 = (CL.chain p X N).NR - 1 := by
    have := hVpre.jj_last
    rwa [hP3'] at this
  have hκ := kappaBal_pos (CL.aOf p X N)
  obtain ⟨hmainA, -, -⟩ := Ha p hp N hN hs0a X hX
  obtain ⟨-, hPCA⟩ := hmainA ψL hJL hseedL
  set a := CL.aOf p X N with ha_def
  set κb := kappaBal a with hκb
  set μ : ℝ := CL.lamL p X N / κb with hμdef
  have hμabs : |μ| = |CL.lamL p X N| / κb := by rw [hμdef, abs_div, abs_of_pos hκ]
  have hpow0 : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) := powLm_nonneg CL hh0 hh1
  have hjNR : j ≤ (CL.chain p X N).NR := by omega
  have hu_c : CL.uc p - CL.η / 2 < uNode (Fz.step N) j := by linarith
  have hu_hi : uNode (Fz.step N) j ≤ CL.uc p + 2 * CL.η := by linarith
  have hj0' : 0 ≤ j := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- the recessive member of the swapped pair
    have hpb := hVpre.phi_bd (p := 3) (mem_Icc.mpr ⟨by norm_num, by rw [hP3']⟩) (j := j)
      (mem_Icc.mpr ⟨by show (CL.chain p X N).jj 2 ≤ j; omega, by show j ≤ (CL.chain p X N).jj 3 + 1; omega⟩)
    have hphi : ((CL.chain p X N).rescale1 (softLam CL p X N)).phi (Fz.step N) 1 3 j = (CL.chain p X N).phi (Fz.step N) 1 3 j :=
      LadderData.phi_rescale1_of_ne _ _ _ 1 (by norm_num) j
    rw [hphi] at hpb
    have hW : (CL.chain p X N).W j = Eswap a (CL.Zof p X N j) :=
      CL.W3_def p hp X hX N hN j (mem_Icc.mpr ⟨hj1, hjNR⟩)
    have hMj : (CL.chain p X N).M j = Mbal a (CL.Zof p X N j) :=
      CL.M2_def p hp X hX N hN j (mem_Icc.mpr ⟨by omega, hjNR⟩)
    have := hpb.2
    calc |(CL.chain p X N).phi (Fz.step N) 1 3 j| ≤ (CL.cs.KA + CL.cs.KB) * CL.cs.Kw * ((CL.chain p X N).W j)⁻¹ * (CL.chain p X N).M j := this
      _ = _ := by rw [hW, hMj, Eswap_inv_eq]; unfold softK; ring
  · -- item (1) on patch 3, growing weight
    have hbd := hPCA j (mem_Icc.mpr ⟨hj0', hjNR⟩) hu_c hu_hi
    have hmo := molv_upper hf a (-(CL.Zof p X N j))
    rw [Wmol_neg_of_pos a hZ, Mbal_neg] at hmo
    have hEs : Eswap a (CL.Zof p X N j) = (Eminus a (-(CL.Zof p X N j)))⁻¹ := by
      rw [← Eswap_inv_eq, inv_inv]
    rw [hEs] at hmo
    refine hbd.trans ?_
    have hM0 := molv_nonneg hf a (-(CL.Zof p X N j))
    calc Cc * Fz.step N ^ m * Lm (Fz.step N) * |CL.lamL p X N| * Molv U V a (-(CL.Zof p X N j))
        = (Cc * (Fz.step N ^ m * Lm (Fz.step N))) * (|CL.lamL p X N| * Molv U V a (-(CL.Zof p X N j))) := by ring
      _ ≤ (|Cc| * (Fz.step N ^ m * Lm (Fz.step N))) * (|CL.lamL p X N| * (CPC * κb⁻¹ * (Eminus a (-(CL.Zof p X N j)))⁻¹ * Mbal a (CL.Zof p X N j))) := by
          apply mul_le_mul _ (mul_le_mul_of_nonneg_left hmo (abs_nonneg _)) (mul_nonneg (abs_nonneg _) hM0) (by positivity)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hpow0
      _ = |μ| * (|Cc| * CPC * (Fz.step N ^ m * Lm (Fz.step N))) * ((Eminus a (-(CL.Zof p X N j)))⁻¹ * Mbal a (CL.Zof p X N j)) := by
          rw [hμabs, div_eq_mul_inv]; ring
  · -- the comparison sequence in terms of the swapped pair
    rw [psiHatL_of_gt CL p X N hu_c]
    have hjj12 : (CL.chain p X N).jj 1 ≤ (CL.chain p X N).jj 2 := hj12.le
    have hrel2 := CL.phi_swap_rel hf hp hX hN (k := j) hjj12 (by omega) (by omega)
    by_cases ha : a ≤ 0
    · obtain ⟨hr1, hr2⟩ := hrel2.1 ha
      have hrr : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
        rw [← Real.sqrt_mul (by positivity)]
        have : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
        rw [this, Real.sqrt_one]
      have hsc := Real.sin_sq_add_cos_sq (Real.pi * a)
      have key : (CL.chain p X N).phi (Fz.step N) 0 2 j = Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * a) *
          (CL.chain p X N).phi (Fz.step N) 0 3 j + Real.sin (Real.pi * a) * (CL.chain p X N).phi (Fz.step N) 1 3 j := by
        rw [hr1, hr2]
        linear_combination (-((CL.chain p X N).phi (Fz.step N) 0 2 j * Real.cos (Real.pi * a) ^ 2)) * hrr - (CL.chain p X N).phi (Fz.step N) 0 2 j * hsc
      have e1 : ccOf a = Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * a) := by unfold ccOf; rw [if_pos ha]
      have e2 : scOf a = Real.sin (Real.pi * a) := by unfold scOf; rw [if_pos ha]
      rw [e1, e2, key, hμdef]; ring
    · obtain ⟨hr1, hr2⟩ := hrel2.2 (not_le.mp ha)
      have e1 : ccOf a = 1 := by unfold ccOf; rw [if_neg ha]
      have e2 : scOf a = 0 := by unfold scOf; rw [if_neg ha]
      rw [e1, e2, hr1, hμdef]; ring

/-! ### The exact right solution is positive and decaying on the right forbidden side -/

/-- **`psi^R` decays on the right forbidden side** (the paper's "item (1) for `psi^R`", used for its sign and ratio only): for `u_{k+1} >= u_c + eta/4`,
`0 < q_{k+1}` and `(1 + nu') q_{k+1} <= q_k` with `nu' = nu_1/(C_A + 1)` (`growth_ratio` for the mirror chart on the rows `m = N - j <= N - k - 1`, `CR.grow_gap`). -/
theorem soft_qZ_decay (hM : SoftMirror CL CR) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ}
    (hN : CL.N0 ≤ N) (hs : Fz.step N ≤ CL.softH1) (hsR : Fz.step N ≤ CR.softH1) {k : ℤ} (hk0 : 0 ≤ k) (hk1 : k + 1 ≤ N)
    (hlo : CL.uc p + CL.η / 4 ≤ uNode (Fz.step N) (k + 1)) :
    0 < qZ Fz p N X (k + 1) ∧ (1 + CR.nu1 / (CR.CA + 1)) * qZ Fz p N X (k + 1) ≤ qZ Fz p N X k := by
  obtain ⟨hNR, hXR⟩ := mirror_ctx hM hp hX hN
  have hpos := bondA_pos_all CL CR hM hp hX hN hs hsR
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hCA, hnu, -⟩ := CR.consts_pos3
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  obtain ⟨huc, -, -, hη, -, -⟩ := hM
  set n1 : ℤ := (N : ℤ) - k - 1 with hn1
  have hmirror : ∀ n : ℤ, uNode (Fz.step N) ((N : ℤ) - n) = Fz.L - uNode (Fz.step N) n :=
    fun n => uNode_mirror Fz.L (Fz.step N) N n (step_mul_succ Fz N)
  have hgr := growth_ratio ((mirrorFamily Fz).bondA p N) ((mirrorFamily Fz).diagQ p N X) (fun m => qZ Fz p N X ((N : ℤ) - m)) n1
    (CR.CA + 1) CR.nu1
    (by unfold SymbolFamily.bondA; simp)
    (fun n hn0 hn1' => by
      rw [bondA_mirror]
      exact hpos _ (by omega) (by omega))
    (fun n _ _ => by
      have := CR.bondA_le p hp N hNR n
      linarith)
    hnu
    (fun n hn0 hn1' => by
      have hu : uNode (Fz.step N) n ≤ CR.uc p - CR.η / 4 := by
        have h1 : uNode (Fz.step N) n ≤ uNode (Fz.step N) n1 := SoftEdgeChart.uNode_mono_le hh0.le hn1'
        have h2 : uNode (Fz.step N) n1 = Fz.L - uNode (Fz.step N) (k + 1) := by
          rw [← hmirror (k + 1)]; congr 1; omega
        rw [huc p hp, hη]
        linarith
      exact CR.grow_gap p hp X hXR N hNR n hn0 hu)
    (fun n hn0 hn1' => by
      have := lop_mirror_qZ Fz p N hpos hN1 X 1 n hn0 (by omega)
      simpa using this)
    (by simp [qZ_N])
  have hend := hgr n1 (by omega) le_rfl
  have e1 : (N : ℤ) - n1 = k + 1 := by omega
  have e2 : (N : ℤ) - (n1 + 1) = k := by omega
  simp only [e1, e2] at hend
  exact hend

/-! ### The core: `sign casD = sign (lambda_L (-1)^k)` at `a = -k + O(h)` -/

lemma small_alg (ν θ G : ℝ) (hν : 0 < ν) (hθ0 : 0 ≤ θ) (hG0 : 0 ≤ G) (hθ : θ ≤ min ν 1 / 8) (hG : G ≤ min ν 1 / 8) :
    (1 + θ) * (1 + G) < (1 - θ) * (1 + ν) := by
  have h1 : min ν 1 ≤ ν := min_le_left _ _
  have h2 : min ν 1 ≤ 1 := min_le_right _ _
  have h3 : 0 < min ν 1 := lt_min hν one_pos
  set d := min ν 1 / 8 with hd
  have hd0 : 0 < d := by positivity
  have hd1 : d ≤ 1 / 8 := by linarith
  have hd2 : 8 * d ≤ ν := by linarith
  nlinarith [mul_nonneg hθ0 hG0, mul_le_mul hθ hG hG0 hd0.le]

lemma aux_a (x δ c : ℝ) (hx : 0 ≤ x) (hδ : 0 < δ) (hc : 0 < c) : x * (δ * c / (8 * (x + 1))) ≤ δ * c / 8 := by
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hδ hc]

lemma aux_c (A δ c cc : ℝ) (hA : 0 ≤ A) (hAδ : A ≤ δ * c / 4) (hcc : 1 / 4 ≤ cc) (hc : 0 < c) (hδ : 0 < δ) :
    A / (c * cc) ≤ δ := by
  have hcc0 : 0 < cc := by linarith
  rw [div_le_iff₀ (by positivity)]
  have : δ * c * (1 / 4) ≤ δ * c * cc := mul_le_mul_of_nonneg_left hcc (by positivity)
  nlinarith

lemma aux_d (x δ : ℝ) (hx : 0 ≤ x) (hδ : 0 < δ) : x * (δ / (x + 1)) ≤ δ := by
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- the muTilde correction: `|mu-tilde - mu_0| <= (q/2) C_mu h^2` (`h <= 1`). -/
lemma ss_muTilde_sub_le {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
    (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ}
    (hh1 : Fz.step N ≤ 1) :
    |CL.muTilde p X N - CL.muS 0 p (Fz.bandHi p - X)| ≤ ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 := by
  have hh := SoftEdgeChart.step_pos (F := Fz) N
  have hα := CL.abs_alpha_le hX
  unfold SoftEdgeChart.muTilde
  rw [add_sub_cancel_left]
  have hterm : ∀ r ∈ Finset.Icc 1 (q / 2), |Fz.step N ^ (2 * r) * CL.muS r p (Fz.bandHi p - X)| ≤ Fz.step N ^ 2 * CL.Cmu := by
    intro r hr
    have hr1 := (Finset.mem_Icc.mp hr).1
    rw [abs_mul, abs_of_nonneg (pow_nonneg hh.le _)]
    have h1 : Fz.step N ^ (2 * r) ≤ Fz.step N ^ 2 := pow_le_pow_of_le_one hh.le hh1 (by omega)
    have h2 : |CL.muS r p (Fz.bandHi p - X)| ≤ CL.Cmu :=
      CL.muS_bd r (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hr).2⟩) p hp _ hα
    exact mul_le_mul h1 h2 (abs_nonneg _) (by have := CL.consts_pos2.1; positivity)
  calc |∑ r ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * r) * CL.muS r p (Fz.bandHi p - X)|
      ≤ ∑ r ∈ Finset.Icc 1 (q / 2), |Fz.step N ^ (2 * r) * CL.muS r p (Fz.bandHi p - X)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 (q / 2), Fz.step N ^ 2 * CL.Cmu := Finset.sum_le_sum hterm
    _ = ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 := by
      rw [Finset.sum_const, Nat.card_Icc]; simp; ring

/-- `a = -k + O(h)` at the points `pi mu_0 = pi h k`. -/
lemma abs_aOf_add_le {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ}
    (hh1 : Fz.step N ≤ 1) {k : ℕ} (hk : Real.pi * softMu0 CL p X = Real.pi * Fz.step N * k) :
    |CL.aOf p X N + k| ≤ ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N := by
  have hh := SoftEdgeChart.step_pos (F := Fz) N
  have hμ : CL.muS 0 p (Fz.bandHi p - X) = Fz.step N * k := by
    have h := hk
    unfold softMu0 at h
    have hpi := Real.pi_pos
    have : Real.pi * (CL.muS 0 p (Fz.bandHi p - X) - Fz.step N * k) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hpi.ne'
    · linarith
  have hmt := ss_muTilde_sub_le CL hp hX hh1
  rw [hμ] at hmt
  have e : CL.aOf p X N + k = -(CL.muTilde p X N - Fz.step N * k) / Fz.step N := by
    rw [SoftEdgeChart.aOf_eq]; field_simp; ring
  rw [e, abs_div, abs_neg, abs_of_pos hh, div_le_iff₀ hh]
  calc |CL.muTilde p X N - Fz.step N * k| ≤ ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N ^ 2 := hmt
    _ = ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N * Fz.step N := by ring

/-- **Step 6 (ii) at a point**: for `|a + k| <= C' h`, `sign casD(X) = sign (lambda_L(X) (-1)^k)`. -/
theorem soft_sign_at (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) :
    ∃ h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      ∀ k : ℕ, |CL.aOf p X N + k| ≤ ((q / 2 : ℕ) : ℝ) * CL.Cmu * Fz.step N →
        SignType.sign (casD Fz p N X) = SignType.sign (CL.lamL p X N * (-1) ^ k) := by
  obtain ⟨Ch0, h0r, h0rpos, hCh0, Hrow⟩ := soft_row_data CL hf hm hLm
  obtain ⟨Cc1, h0a, clam, Clam, h0apos, hclam, Ha⟩ := propThaW2_item1 CL hf hm hLm
  obtain ⟨hCA, hnu, -⟩ := CR.consts_pos3
  obtain ⟨hcgr, hCgr⟩ := CL.consts_pos6
  have hCmu := CL.consts_pos2.1
  have hK0 := softK_nonneg CL
  set ν : ℝ := CR.nu1 / (CR.CA + 1) with hνdef
  have hν : 0 < ν := by positivity
  set C' : ℝ := ((q / 2 : ℕ) : ℝ) * CL.Cmu with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set K : ℝ := softK CL with hKdef
  set δ : ℝ := min ν 1 / 8 with hδdef
  have hδ0 : 0 < δ := by have := lt_min hν one_pos; positivity
  set ε1 : ℝ := δ * CL.cgr / (8 * (Ch0 + 1)) with hε1
  have hε1pos : 0 < ε1 := by positivity
  set h2 : ℝ := δ * CL.cgr / (8 * (Real.pi * C' * K + 1)) with hh2
  have hh2pos : 0 < h2 := by have := Real.pi_pos; positivity
  set h3 : ℝ := δ / (CL.Cgr + 1) with hh3
  have hh3pos : 0 < h3 := by positivity
  set h4 : ℝ := 1 / (Real.pi * (C' + 1)) with hh4
  have hh4pos : 0 < h4 := by have := Real.pi_pos; positivity
  refine ⟨min h0r (min h0a (min CL.softH2 (min (CL.η / 16) (min CR.softH1 (min CR.η (min CL.η (min (softHL CL ε1)
    (min h2 (min h3 h4))))))))), ?_, ?_⟩
  · refine lt_min h0rpos (lt_min h0apos (lt_min CL.softH2_pos (lt_min (by have := CL.consts_pos.2.1; positivity)
      (lt_min CR.softH1_pos (lt_min CR.consts_pos.2.1 (lt_min CL.consts_pos.2.1 (lt_min (softHL_pos CL ε1)
        (lt_min hh2pos (lt_min hh3pos hh4pos)))))))))
  intro p hp N hN hstep X hX k hak
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN2 : CR.N0 ≤ N := (le_max_right _ _).trans hN
  have s0r : Fz.step N ≤ h0r := hstep.trans (min_le_left _ _)
  have s0a : Fz.step N ≤ h0a := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have s2 : Fz.step N ≤ CL.softH2 := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have s16 : Fz.step N ≤ CL.η / 16 :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have s1R : Fz.step N ≤ CR.softH1 :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have sηR : Fz.step N ≤ CR.η :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))))
  have sη : Fz.step N ≤ CL.η :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))
  have sL : Fz.step N ≤ softHL CL ε1 :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))))
  have s2' : Fz.step N ≤ h2 :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))))
  have s3' : Fz.step N ≤ h3 :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))))))))
  have s4' : Fz.step N ≤ h4 :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))))))))))
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hhH1 : Fz.step N ≤ CL.softH1 := s2.trans CL.softH2_le_H1
  have hh1 : Fz.step N ≤ 1 := hhH1.trans CL.softH1_le_one
  obtain ⟨hNR, hXR⟩ := mirror_ctx hM hp hX hN1
  have hpos := bondA_pos_all CL CR hM hp hX hN1 hhH1 s1R
  -- the rows `k_0`, `k_0 + 1`
  obtain ⟨huc0, huc1⟩ := CL.ucη_in p hp
  have hηpos := CL.consts_pos.2.1
  obtain ⟨k0, hk0, hlo, hhi⟩ := exists_row (Fz.step N) (CL.uc p + 3 * CL.η / 8) hh0 (by linarith)
  obtain ⟨hjj2, hk0NR, hZ0, hZ1⟩ := quant_rows CL hp hX hN1 s2 s16 hk0 hlo hhi
  have hsucc := uNode_succ_sub' (Fz.step N) k0
  -- `N_R <= N` on both charts
  have hNRL : (CL.chain p X N).NR ≤ N := by
    have := row_le_N Fz N (j := (CL.chain p X N).NR) (by
      obtain ⟨-, -, -, -, -, -, hNRu, -⟩ := CL.shape p hp X hX N hN1
      linarith)
    exact_mod_cast this
  have hNRR : (CR.chain p X N).NR ≤ N := by
    have := row_le_N (mirrorFamily Fz) N (j := (CR.chain p X N).NR) (by
      obtain ⟨-, -, -, -, -, -, hNRu, -⟩ := CR.shape p hp X hXR N hNR
      have := (CR.ucη_in p hp).2
      have hη := CR.consts_pos.2.1
      linarith)
    exact_mod_cast this
  have hN1' : 1 ≤ N := by have : k0 + 1 ≤ (CL.chain p X N).NR := hk0NR; omega
  have hc0 : 0 < CL.psiHatL p X N 0 := psiHatL_zero_pos CL hp hX hN1 sη
  have hc0' : 0 < CR.psiHatL p X N 0 := psiHatL_zero_pos CR hp hXR hNR sηR
  obtain ⟨hJL, hseedL', -, -⟩ := pq_exact Fz p N hpos hN1' X (CL.psiHatL p X N 0) (CR.psiHatL p X N 0)
    (CL.chain p X N).NR (CR.chain p X N).NR hNRL hNRR
  set ψL : ℤ → ℝ := fun n => CL.psiHatL p X N 0 * pZ Fz p N X n with hψL
  have hseedL : ψL 0 = CL.psiHatL p X N 0 := hseedL'
  -- the left rows
  have hk0u2 : uNode (Fz.step N) (k0 + 1) < CL.uc p + CL.η / 2 := by linarith
  obtain ⟨g0, E0, I0⟩ := Hrow p hp N hN1 s0r X hX ψL hJL hseedL k0 (by omega) (by omega) hZ0 hlo (by linarith)
  obtain ⟨g1, E1, I1⟩ := Hrow p hp N hN1 s0r X hX ψL hJL hseedL (k0 + 1) (by omega) (by omega) hZ1 (by linarith) hk0u2
  -- `a` is small
  set a := CL.aOf p X N with ha_def
  have hπ := Real.pi_pos
  have hC'h : C' * Fz.step N ≤ 1 / Real.pi := by
    have h1 : Fz.step N ≤ 1 / (Real.pi * (C' + 1)) := s4'
    rw [le_div_iff₀ hπ]
    have h2 : Fz.step N * (Real.pi * (C' + 1)) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at h1
    have h3 := mul_nonneg hh0.le hπ.le
    linarith [h3, h2]
  have hak' : |a + k| ≤ 1 / Real.pi := hak.trans hC'h
  have hcc := sign_cc hak'
  have hapl : a ≤ ((q / 2 : ℕ) : ℝ) * CL.Cmu + 1 := by
    have h1 := (abs_le.mp hak).2
    have h2 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h3 : C' * Fz.step N ≤ C' := by
      calc C' * Fz.step N ≤ C' * 1 := mul_le_mul_of_nonneg_left hh1 hC'0
        _ = C' := mul_one _
    linarith
  have hVpre : ((CL.chain p X N).rescale1 (softLam CL p X N)).PreValid CL.cs (Fz.step N) m := CL.valid p hp X hX N hN1
  obtain ⟨-, -, hj12, -⟩ := CL.soft_pos hp hX hN1 hhH1 hVpre
  -- `grow3`
  obtain ⟨gr0, gr1, grR⟩ := CL.grow3 p hp X hX N hN1 hapl k0 (by omega) hk0NR (by linarith)
  have hW0 : (CL.chain p X N).W k0 = Eswap a (CL.Zof p X N k0) :=
    CL.W3_def p hp X hX N hN1 k0 (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hW1 : (CL.chain p X N).W (k0 + 1) = Eswap a (CL.Zof p X N (k0 + 1)) :=
    CL.W3_def p hp X hX N hN1 (k0 + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hM0 : (CL.chain p X N).M k0 = Mbal a (CL.Zof p X N k0) :=
    CL.M2_def p hp X hX N hN1 k0 (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hM1 : (CL.chain p X N).M (k0 + 1) = Mbal a (CL.Zof p X N (k0 + 1)) :=
    CL.M2_def p hp X hX N hN1 (k0 + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hEs0 : Eswap a (CL.Zof p X N k0) = (Eminus a (-(CL.Zof p X N k0)))⁻¹ := by rw [← Eswap_inv_eq, inv_inv]
  have hEs1 : Eswap a (CL.Zof p X N (k0 + 1)) = (Eminus a (-(CL.Zof p X N (k0 + 1))))⁻¹ := by rw [← Eswap_inv_eq, inv_inv]
  rw [hW0, hM0, hEs0] at gr0
  rw [hW1, hM1, hEs1] at gr1
  -- the pieces
  set f0 := (CL.chain p X N).phi (Fz.step N) 0 3 k0 with hf0def
  set f1 := (CL.chain p X N).phi (Fz.step N) 0 3 (k0 + 1) with hf1def
  have hlamlow : clam * (softLam CL p X N * kappaBal a) ≤ |CL.lamL p X N| := (Ha p hp N hN1 s0a X hX).2.1
  have hκ := kappaBal_pos a
  have hlam0 : 0 < |CL.lamL p X N| := by
    have h1 : 0 < clam * (softLam CL p X N * kappaBal a) := by
      have := softLam_pos CL p X N
      positivity
    exact lt_of_lt_of_le h1 hlamlow
  set μ : ℝ := CL.lamL p X N / kappaBal a with hμdef
  have hμ : 0 < |μ| := by rw [hμdef, abs_div, abs_of_pos hκ]; positivity
  set cc := ccOf a with hccdef
  set sc := scOf a with hscdef
  have hcc4 : 1 / 4 ≤ |cc| := by
    have : 1 / 4 ≤ (-1 : ℝ) ^ k * cc := hcc
    calc (1 : ℝ) / 4 ≤ (-1 : ℝ) ^ k * cc := this
      _ ≤ |(-1 : ℝ) ^ k * cc| := le_abs_self _
      _ = |cc| := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hccne : cc ≠ 0 := by intro h0; rw [h0, abs_zero] at hcc4; linarith
  have hsc : |sc| ≤ Real.pi * (C' * Fz.step N) := abs_scOf_le hak
  set eps0 : ℝ := Fz.step N ^ m * Lm (Fz.step N) with heps0
  have hLm1 := hLm (Fz.step N) hh0 hh1
  have hpowle : eps0 ≤ ε1 := by
    have h1 : Fz.step N ^ m ≤ Fz.step N := pow_le_of_le_one hh0.le hh1 (by omega)
    have h2 : Fz.step N * Lm (Fz.step N) ≤ ε1 := softHL_spec CL hε1pos hh0 sL
    exact (mul_le_mul_of_nonneg_right h1 (by linarith)).trans h2
  have hpow0 : 0 ≤ eps0 := powLm_nonneg CL hh0 hh1
  -- relative error `theta`
  set θ : ℝ := (Ch0 * eps0 + |sc| * K) / (CL.cgr * |cc|) with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hChε : Ch0 * eps0 ≤ δ * CL.cgr / 8 :=
    (mul_le_mul_of_nonneg_left hpowle hCh0).trans (aux_a Ch0 δ CL.cgr hCh0 hδ0 hcgr)
  have hscK : |sc| * K ≤ δ * CL.cgr / 8 := by
    have hq1 : |sc| * K ≤ Real.pi * (C' * Fz.step N) * K := mul_le_mul_of_nonneg_right hsc hK0
    have hq2 : Real.pi * (C' * Fz.step N) * K ≤ Real.pi * C' * K * h2 := by
      have : Real.pi * (C' * Fz.step N) * K = Real.pi * C' * K * Fz.step N := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left s2' (by positivity)
    exact hq1.trans (hq2.trans (aux_a (Real.pi * C' * K) δ CL.cgr (by positivity) hδ0 hcgr))
  have hθδ : θ ≤ δ := by
    rw [hθdef]
    exact aux_c _ δ CL.cgr |cc| (by positivity) (by linarith) hcc4 hcgr hδ0
  have hGδ : CL.Cgr * Fz.step N ≤ δ :=
    (mul_le_mul_of_nonneg_left s3' hCgr).trans (aux_d CL.Cgr δ hCgr hδ0)
  have hsmall := small_alg ν θ (CL.Cgr * Fz.step N) hν hθ0 (mul_nonneg hCgr hh0.le) hθδ hGδ
  -- positivity of the weights
  have hMpos0 := Mbal_pos a (CL.Zof p X N k0)
  have hMpos1 := Mbal_pos a (CL.Zof p X N (k0 + 1))
  have hepos0 := Eminus_pos a (-(CL.Zof p X N k0))
  have hepos1 := Eminus_pos a (-(CL.Zof p X N (k0 + 1)))
  have hf0pos : 0 < f0 := lt_of_lt_of_le (by positivity) gr0
  have hf1pos : 0 < f1 := lt_of_lt_of_le (by positivity) gr1
  -- error of `psi^L` against `c f`
  have hrow : ∀ (j : ℤ) (fj : ℝ), fj = (CL.chain p X N).phi (Fz.step N) 0 3 j →
      CL.cgr * ((Eminus a (-(CL.Zof p X N j)))⁻¹ * Mbal a (CL.Zof p X N j)) ≤ fj →
      |(CL.chain p X N).phi (Fz.step N) 1 3 j| ≤ K * (Eminus a (-(CL.Zof p X N j)) * Mbal a (CL.Zof p X N j)) →
      |ψL j - CL.psiHatL p X N j| ≤ |μ| * (Ch0 * eps0) * ((Eminus a (-(CL.Zof p X N j)))⁻¹ * Mbal a (CL.Zof p X N j)) →
      CL.psiHatL p X N j = μ * (cc * fj + sc * (CL.chain p X N).phi (Fz.step N) 1 3 j) →
      0 < CL.Zof p X N j →
      |ψL j - (μ * cc) * fj| ≤ θ * |μ * cc| * fj := by
    intro j fj hfj hlb hg hE hI hZj
    set e := Eminus a (-(CL.Zof p X N j)) with he
    set Mj := Mbal a (CL.Zof p X N j) with hMj
    set gj := (CL.chain p X N).phi (Fz.step N) 1 3 j with hgj
    have he0 : 0 < e := Eminus_pos _ _
    have hMj0 : 0 < Mj := Mbal_pos _ _
    have he1 : e ≤ 1 := Eminus_le_one a (by linarith)
    have hee : e ≤ e⁻¹ := le_trans he1 ((one_le_inv₀ he0).mpr he1)
    have hfj' : e⁻¹ * Mj ≤ fj / CL.cgr := by
      rw [le_div_iff₀ hcgr]; linarith [hlb]
    have hgj' : |gj| ≤ K * (e⁻¹ * Mj) :=
      hg.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hee hMj0.le) hK0)
    have h1 : ψL j - (μ * cc) * fj = (ψL j - CL.psiHatL p X N j) + μ * sc * gj := by rw [hI]; ring
    have hbd : |ψL j - (μ * cc) * fj| ≤ |μ| * (Ch0 * eps0 + |sc| * K) * (e⁻¹ * Mj) := by
      rw [h1]
      refine (abs_add_le _ _).trans ?_
      have h2 : |μ * sc * gj| = |μ| * |sc| * |gj| := by rw [abs_mul, abs_mul]
      rw [h2]
      have h3 : |μ| * |sc| * |gj| ≤ |μ| * |sc| * (K * (e⁻¹ * Mj)) :=
        mul_le_mul_of_nonneg_left hgj' (by positivity)
      have hrw : |μ| * (Ch0 * eps0 + |sc| * K) * (e⁻¹ * Mj) = |μ| * (Ch0 * eps0) * (e⁻¹ * Mj) + |μ| * |sc| * (K * (e⁻¹ * Mj)) := by ring
      rw [hrw]
      exact add_le_add hE h3
    have hcc0 : 0 < |cc| := abs_pos.mpr hccne
    calc |ψL j - (μ * cc) * fj| ≤ |μ| * (Ch0 * eps0 + |sc| * K) * (e⁻¹ * Mj) := hbd
      _ ≤ |μ| * (Ch0 * eps0 + |sc| * K) * (fj / CL.cgr) :=
          mul_le_mul_of_nonneg_left hfj' (by positivity)
      _ = θ * |μ * cc| * fj := by
          rw [hθdef, abs_mul]
          field_simp
  have hL0 := hrow k0 f0 rfl gr0 g0 E0 I0 hZ0
  have hL1 := hrow (k0 + 1) f1 rfl gr1 g1 E1 I1 hZ1
  -- the right solution
  have hlo1 : CL.uc p + CL.η / 4 ≤ uNode (Fz.step N) (k0 + 1) := by linarith
  have hk0N : k0 + 1 ≤ (N : ℤ) := by have := hk0NR; omega
  obtain ⟨hq1, hqr⟩ := soft_qZ_decay CL CR hM hp hX hN1 hhH1 s1R (k := k0) (by omega) hk0N hlo1
  have hq0 : 0 < qZ Fz p N X k0 := lt_of_lt_of_le (by positivity) hqr
  have hR0 : 0 < CR.psiHatL p X N 0 * qZ Fz p N X k0 := mul_pos hc0' hq0
  have hR1 : 0 < CR.psiHatL p X N 0 * qZ Fz p N X (k0 + 1) := mul_pos hc0' hq1
  have hR : (1 + ν) * (CR.psiHatL p X N 0 * qZ Fz p N X (k0 + 1)) ≤ CR.psiHatL p X N 0 * qZ Fz p N X k0 := by
    calc (1 + ν) * (CR.psiHatL p X N 0 * qZ Fz p N X (k0 + 1)) = CR.psiHatL p X N 0 * ((1 + ν) * qZ Fz p N X (k0 + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hqr hc0'.le
  have hc : μ * cc ≠ 0 := mul_ne_zero (div_ne_zero (fun h0 => by rw [h0, abs_zero] at hlam0; exact lt_irrefl _ hlam0) hκ.ne') hccne
  have hsign := casD_sign_of_rows Fz p N hpos hN1' X (CL.psiHatL p X N 0) (CR.psiHatL p X N 0) hc0 hc0' k0 (by omega)
    (by omega) (μ * cc) f0 f1 θ (CL.Cgr * Fz.step N) ν hf0pos hf1pos grR hθ0 (mul_nonneg hCgr hh0.le) hL0 hL1 hR0 hR1 hR hν hsmall hc
  rw [hsign]
  have hw : 0 < ((-1 : ℝ) ^ k * cc) / kappaBal a := div_pos (by linarith [hcc]) hκ
  have hsq : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  have heq : μ * cc = (CL.lamL p X N * (-1) ^ k) * (((-1 : ℝ) ^ k * cc) / kappaBal a) := by
    rw [hμdef]
    calc CL.lamL p X N / kappaBal a * cc = CL.lamL p X N * cc / kappaBal a * 1 := by ring
      _ = CL.lamL p X N * cc / kappaBal a * ((-1 : ℝ) ^ k * (-1) ^ k) := by rw [hsq]
      _ = _ := by ring
  rw [heq, sign_mul, sign_pos hw, mul_one]

/-- **Hypothesis (ii) of `lem:tha-count` on the soft chart** (app_thmA Step 6 (ii)): there is a constant sign `sigma` (that of `lambda_L` on the energy window) with
`sign casD(X) = sign (sigma (-1)^k)` whenever `|X - bandHi| <= delta_0` and `pi mu_0(bandHi - X) = pi h k`. -/
theorem soft_sign_D (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) :
    ∃ h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ X : ℝ, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ k : ℕ,
        Real.pi * softMu0 CL p X = Real.pi * Fz.step N * k →
          SignType.sign (casD Fz p N X) = SignType.sign (σ * (-1) ^ k) := by
  obtain ⟨h1', h1pos, H⟩ := soft_sign_at CL CR hM hf hm hLm
  obtain ⟨Cc1, h0a, clam, Clam, h0apos, hclam, Ha⟩ := propThaW2_item1 CL hf hm hLm
  refine ⟨min (min h1' h0a) 1, lt_min (lt_min h1pos h0apos) one_pos, ?_⟩
  intro p hp N hN hstep
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have s1 : Fz.step N ≤ h1' := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have s0a : Fz.step N ≤ h0a := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have sone : Fz.step N ≤ 1 := hstep.trans (min_le_right _ _)
  have hset : {X : ℝ | |X - Fz.bandHi p| ≤ CL.δ0} = Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0) := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hcont : ContinuousOn (fun X => CL.lamL p X N) (Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0)) := by
    rw [← hset]; exact CL.lamL_continuousOn p hp N hN1
  have hne : ∀ X ∈ Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0), CL.lamL p X N ≠ 0 := by
    intro X hX0
    have hX : |X - Fz.bandHi p| ≤ CL.δ0 := by
      rw [abs_le]; constructor <;> linarith [hX0.1, hX0.2]
    have hlow := (Ha p hp N hN1 s0a X hX).2.1
    have h1 : 0 < clam * (softLam CL p X N * kappaBal (CL.aOf p X N)) := by
      have := softLam_pos CL p X N
      have := kappaBal_pos (CL.aOf p X N)
      positivity
    intro h0
    rw [h0, abs_zero] at hlow
    linarith
  have hsc := sign_const_of_cont (Set.ordConnected_Icc) hcont hne
  have hmem : ∀ X : ℝ, |X - Fz.bandHi p| ≤ CL.δ0 → X ∈ Set.Icc (Fz.bandHi p - CL.δ0) (Fz.bandHi p + CL.δ0) := by
    intro X hX
    rw [← hset]; exact hX
  rcases hsc with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro X hX k hk
    have hak := abs_aOf_add_le CL hp hX sone hk
    rw [H p hp N hN (hstep.trans ((min_le_left _ _).trans (min_le_left _ _))) X hX k hak]
    have hl := hpos X (hmem X hX)
    have hk0 : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [sign_mul, sign_pos hl, one_mul, one_mul]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro X hX k hk
    have hak := abs_aOf_add_le CL hp hX sone hk
    rw [H p hp N hN (hstep.trans ((min_le_left _ _).trans (min_le_left _ _))) X hX k hak]
    have hl := hneg X (hmem X hX)
    rw [sign_mul, sign_neg hl, sign_mul, sign_neg (by norm_num : (-1 : ℝ) < 0)]

end Rows

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_row_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_row_data

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_qZ_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_qZ_decay

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_sign_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_sign_at

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_sign_D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_sign_D

end FormalResearch.JacobiEigenvectors.TheoremA

end
