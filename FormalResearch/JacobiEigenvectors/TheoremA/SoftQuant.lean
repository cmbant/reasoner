module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftEigen

/-!
# Paper J, Layer 2 (L2.C7): quantisation at the soft edge (chain step E8 of `PLAN.md`), `prop:tha-W2` (3) first half

Source: `app_thmA.tex` "The soft edges: proof of Proposition prop:tha-W2", Step 5 (quantisation) with its inputs Step 4 (b) (`|kappa lambda_R| <= C |lambda_L|`) and item (1) for `psi^L` and, by the mirror, for `psi^R`.

## The exact chain of lemmas (written before the proofs; every hypothesis is listed)

Notation: `CL`, `CR` mirror charts (`SoftMirror CL CR`), `a = aOf`, `kappa_b = kappa_bal(a)`, `Z_n`, `lam_L = CL.lamL`, `lam_R = CR.lamL`, `e_n := E_-(a, -Z_n) = E_swap(a, Z_n)^{-1}`
(`Eswap_inv_eq`), `psi^L` the exact left solution seeded by `psi-hat^L_0`, `psi'` the exact solution of the mirror recurrence seeded by `psi-hat^{L,R}_0`, `psi^R_n := psi'_{N-n}`, `kappa` the glue constant with `psi^L_n = kappa psi^R_n`.

* **Q0 (weights, `M_Olv` from above).**  `Eswap_inv_eq`, `Wmol_pos_eq` (`W_mol(a,Z) = E_-(a,-Z)` for `Z >= 0`), `molv_upper` (`M_Olv(a,z) <= c_PC^{-1}`-free upper half of `molv_well/molv_bar`: `<= C_PC kappa_b^{-1} W_mol M_bal`).
* **Q1 (positions on the chart), hypotheses: `mu in P`, `|X - X_s^+| <= delta_0`, `N >= N_0`, `h <= softH2`, the rescaled chain `PreValid`.**
  `zeta_abs_le` (`|zeta(x)| <= c_Z delta_0 + 2 d_+ eta` on `|x| <= 2 eta`), `j2_lt` (`x_{j_2} < eta/4`; with `j2_ge` the switch bond is inside `|x| < eta/4`: `zeta_far` and `d_+ h <= sqrt(c_{z1})/2`),
  `Zof_nonpos_of_le` (`k <= j_2` and `x_k >= -2 eta` give `Z_k <= 0`; with `Zof_pos_of_gt` the sign of `Z_k` is the side of `j_2`), `exists_quant_row` (a row `k_0` with `x_{k_0} in [3 eta/8, 3 eta/8 + h)`).
* **Q2 (patch-2 envelope of `psi-hat`).**  `psiHatL_env2`: for a row `k` with `u_c - eta/2 < u_k <= u_c + 2 eta`, `Z_k <= 0`: `|psi-hat^L_k| <= K |lam_L| kappa_b^{-1} E_-(a,Z_k) M_bal(a,Z_k)` (`phi_bd` on patch 2 and `W2_def`, `M2_def`),
  `K = (K_A + K_B) K_w`.  (Also feeds E6.)
* **Q3 (right-recessive bound, item (1) for `psi^R`).**  `soft_right_recessive`: at the rows `k_0, k_0 + 1` of Q1, `|psi^R_k| <= C_R |lam_R| kappa_b^{-1} e_k M_bal(a,Z_k)`.  Inputs: `propThaW2_item1` for `CR` (a chart of the mirror family),
  `Zof_mirror`, `aOf_mirror`, `uNode_mirror`, `psiHatL_env2` for `CR` at the mirror row `N - k`, `molv_upper`.
* **Q4 (Casoratian core).**  `quant_core`: with `f = phi^{(1)}_3`, `g = phi^{(2)}_3` (swapped pair of patch 3), `cas_lb_site` (`c_- sqrt h <= |W_{k_0}(f,g)|`), `phi_swap_rel`
  (`phi^{(1)}_2 = sqrt(2/pi) cos(pi a) f + sin(pi a) g` for `a <= 0`, `phi^{(1)}_2 = f` for `a > 0`) and `W(g,g) = 0`:
  `|c_a| c_- sqrt h (|lam_L|/kappa_b) <= |W_{k_0}(psi^L, g)| + |W_{k_0}(psi^L - psi-hat^L, g)|`, `c_a = sqrt(2/pi) cos(pi a)` (`a <= 0`), `1` (`a > 0`).
* **Q5 (smallness).**  `e_{k_0} <= exp(-c/h)` (`Eminus_decay` on `[-Z_{k_0}, -zeta(5 eta/16)/sqrt h]`, margin `Zq_lb`), one-step weight ratio `e_{k_0} <= w_bar e_{k_0+1}`, `M_{k_0} M_{k_0+1} <= C sqrt h` (`Mbal_prod_le`).
* **Q6 (E8).**  `soft_quant` (**proved**): premise (the output of Step 4 (b), chain step E5): `|kappa| |lam_R| <= C_k |lam_L|` (`hkap`).  Conclusion: `a <= 0` (no eigenvalue has `a > 0`) and `|cos(pi a)| <= C_q h^m Lm(h)`.
  `cos_label`: `|cos(pi a)| <= eps` and `a <= 0` give an integer `k >= 0` with `|a + k + 1/2| <= eps/2`.

## Differences from the paper

* **The quantisation is run through the Casoratian of the swapped pair of patch 3 instead of the Liouville--Green lower bound of the growing part.**  The paper compares the growing parts of `psi^L` and `psi^R` using
  `|A^{[m]} v~ + h B^{[m]} h^{1/2} v~'| >= c E^{-1} M` (a lower bound on the corrector row `A^{[m]}` and on `v~`, not among the chart fields).  The Casoratian `W(psi, g)` against the *recessive* member `g` of the swapped pair
  needs only the fields that are already in `PreValid` (`cas_lb`, `env`, `A_bd`, `B_bd`).  The result is the same inequality `|cos(pi a)| <= C(e^2 + h^m Lm)`.
* **The exclusion of `0 < a <= C h` is the same inequality with `c_a = 1`**: for `a > 0` patch 3 carries the pair of patch 2, the first member of which is purely growing, so the left-hand side does not
  contain `cos(pi a)`; convexity of `U(a,-Z)` and Step 0 are not used (only `hkap`, which needs `a <= a_+` through `PropThaM`).  So `soft_quant` gives `a <= 0` and the bound at once.
* `hkap` is a premise: Step 4 (b) (`|kappa| ~ |lam_L/lam_R|`) needs the envelopes on `Omega` (E3) and the half-window masses `PropThaM` (E4, `hmass`).  It is *the paper's own intermediate statement*; it is not proved here.

## Proved here (all axiom-pinned, `[propext, Classical.choice, Quot.sound]`)

`Eswap_inv_eq`, `Wmol_pos_eq`, `molv_upper`, `zeta_abs_le`, `j2_lt`, `Zof_nonpos_of_le`, `exists_row`, `psiHatL_env2`, `soft_env_psi`, `quant_rows`, `Eminus_quant_small`, `Eminus_quant_ratio`, `soft_right_recessive`,
`cas_le`, `quant_combine`, `row_le_N`, `soft_quant`, `cos_label`.  Hypotheses of `soft_quant`: `ParabolicCylinderFacts U V cPC CPC`, `1 <= m`, `1 <= Lm` on `(0,1]`, `SoftMirror CL CR`, and the **premise `hkap`** (see above);
the constants `C_q, h_0` depend on the chart constants, `cPC, CPC`, `C_k` only.

## Not formalised

E3 (envelopes on `Omega`), E4 (`PropThaM`), E5 as an instance (`hkap`), E6 tails (`SoftTails.lean`), E9 (counting).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

/-! ### Q0: weights -/

lemma Eswap_inv_eq (a z : ℝ) : (Eswap a z)⁻¹ = Eminus a (-z) := by
  unfold Eswap Eminus
  by_cases ha : a ≤ 0
  · simp [ha, abs_neg]
  · simp [ha, Ebar_neg]

lemma Wmol_pos_eq (a : ℝ) {z : ℝ} (hz : 0 ≤ z) : Wmol a z = Eminus a (-z) := by
  have := Wmol_neg_of_nonpos a (z := -z) (by linarith)
  rwa [neg_neg] at this

/-- `M_Olv` from above (the upper halves of `molv_well`, `molv_bar`). -/
lemma molv_upper {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (a z : ℝ) :
    Molv U V a z ≤ CPC * (kappaBal a)⁻¹ * Wmol a z * Mbal a z := by
  unfold Wmol
  by_cases ha : a ≤ 0
  · rw [ite_eq_left ha]; exact (hf.molv_well a ha z).2
  · rw [ite_eq_right ha]; exact (hf.molv_bar a (not_le.mp ha) z).2

/-! ### Q1: positions on the chart -/

lemma uNode_succ_sub' (h : ℝ) (j : ℤ) : uNode h (j + 1) - uNode h j = h := by
  unfold uNode; push_cast; ring

section Pos

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- `|zeta(x; alpha)| <= c_Z delta_0 + 2 d_+ eta` on `|x| <= 2 eta`. -/
lemma zeta_abs_le {μ : Par × ℝ} (hμ : μ ∈ P) {α : ℝ} (hα : |α| ≤ C.δ0) {x : ℝ} (hx : |x| ≤ 2 * C.η) :
    |C.zeta μ α x| ≤ C.cZ * C.δ0 + 2 * C.dp * C.η := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, hcZ⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hz0 : |C.zeta μ α 0| ≤ C.cZ * C.δ0 := by
    have := C.zeta_alpha μ hμ α hα
    have h2 : C.cZ * |α| ≤ C.cZ * C.δ0 := mul_le_mul_of_nonneg_left hα hcZ.le
    linarith
  have hx' := abs_le.mp hx
  rcases le_total 0 x with hx0 | hx0
  · have hm := C.zeta_mvt hμ hα (by linarith : -(2 * C.η) ≤ 0) hx0 (by linarith)
    have h1 := abs_le.mp hz0
    have h2 : C.dp * (x - 0) ≤ C.dp * (2 * C.η) := mul_le_mul_of_nonneg_left (by linarith) hdp.le
    have h3 := mul_nonneg hdm.le (by linarith : (0 : ℝ) ≤ x - 0)
    rw [abs_le]; constructor <;> nlinarith [hm.1, hm.2]
  · have hm := C.zeta_mvt hμ hα (by linarith : -(2 * C.η) ≤ x) hx0 (by linarith)
    have h1 := abs_le.mp hz0
    have h2 : C.dp * (0 - x) ≤ C.dp * (2 * C.η) := mul_le_mul_of_nonneg_left (by linarith) hdp.le
    have h3 := mul_nonneg hdm.le (by linarith : (0 : ℝ) ≤ 0 - x)
    rw [abs_le]; constructor <;> nlinarith [hm.1, hm.2]

section PosChain

variable {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
  (hh : Fz.step N ≤ C.softH2) {lam : ℝ}
  (hV : ((C.chain μ X N).rescale1 lam).PreValid C.cs (Fz.step N) m)

include hμ hX hN hh hV

/-- **The switch bond is inside the fold collar**: `x_{j_2} < eta/4` (the other half of `j2_ge`). -/
lemma j2_lt : uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ < C.η / 4 := by
  have hhH1 : Fz.step N ≤ C.softH1 := hh.trans C.softH2_le_H1
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hhH1 hV
  obtain ⟨-, hη, hdm, hdmp, -⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hα := C.abs_alpha_le hX
  by_contra hcon
  have hge : C.η / 4 ≤ uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ := not_lt.mp hcon
  have hx12 := uNode_succ_sub' (Fz.step N) ((C.chain μ X N).jj 2)
  have hx2d : uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ ≤ 2 * C.η := by linarith
  have hx2lo : -(2 * C.η) ≤ uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ := by linarith
  have hmvt := C.zeta_mvt hμ hα hx2lo (by linarith : uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ
      ≤ uNode (Fz.step N) ((C.chain μ X N).jj 2 + 1) - C.uc μ) hx3
  have hsub : uNode (Fz.step N) ((C.chain μ X N).jj 2 + 1) - C.uc μ - (uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ)
      = Fz.step N := by linarith
  rw [hsub] at hmvt
  have hfar := C.zeta_far μ hμ _ hα (uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_of_pos (by linarith)]; exact hge)
  have hz := C.consts_pos2.2
  have hzsq : C.cz1 ≤ C.zeta μ (Fz.bandHi μ - X) (uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ) ^ 2 := by
    have : 0 ≤ max (C.muS 0 μ (Fz.bandHi μ - X)) 0 := le_max_right _ _
    linarith
  have hzneg : C.zeta μ (Fz.bandHi μ - X) (uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ) ≤ -Real.sqrt C.cz1 := by
    have h1 : Real.sqrt C.cz1 ≤ |C.zeta μ (Fz.bandHi μ - X) (uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ)| := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hzsq
    rw [abs_of_nonpos hza] at h1
    linarith
  have h2 := C.softH2_le_dp
  have hhH2 : C.dp * Fz.step N ≤ C.dp * C.softH2 := mul_le_mul_of_nonneg_left hh hdp.le
  have hsq : 0 < Real.sqrt C.cz1 := Real.sqrt_pos.mpr hz
  have hzb' : C.zeta μ (Fz.bandHi μ - X) (uNode (Fz.step N) ((C.chain μ X N).jj 2 + 1) - C.uc μ) ≤ 0 := by
    linarith [hmvt.2]
  linarith

/-- the sign of `Z_k` is the side of `j_2`: `k <= j_2` and `x_k >= -2 eta` give `Z_k <= 0`. -/
lemma Zof_nonpos_of_le {k : ℤ} (hk : k ≤ (C.chain μ X N).jj 2) (hxk : -(2 * C.η) ≤ uNode (Fz.step N) k - C.uc μ) :
    C.Zof μ X N k ≤ 0 := by
  have hhH1 : Fz.step N ≤ C.softH1 := hh.trans C.softH2_le_H1
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hhH1 hV
  obtain ⟨-, hη, hdm, hdmp, -⟩ := C.consts_pos
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hα := C.abs_alpha_le hX
  have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hm1 : uNode (Fz.step N) k ≤ uNode (Fz.step N) ((C.chain μ X N).jj 2) := SoftEdgeChart.uNode_mono_le hh0.le hk
  have hm2 : uNode (Fz.step N) ((C.chain μ X N).jj 2) ≤ uNode (Fz.step N) ((C.chain μ X N).jj 2 + 1) :=
    SoftEdgeChart.uNode_mono_le hh0.le (by omega)
  have hmvt := C.zeta_mvt hμ hα hxk (by linarith : uNode (Fz.step N) k - C.uc μ ≤ uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ)
    (by linarith)
  have : C.zeta μ (Fz.bandHi μ - X) (uNode (Fz.step N) k - C.uc μ) ≤ 0 := by
    have := mul_nonneg hdm.le (sub_nonneg.mpr (by linarith : uNode (Fz.step N) k - C.uc μ ≤ uNode (Fz.step N) ((C.chain μ X N).jj 2) - C.uc μ))
    linarith [hmvt.1]
  rw [SoftEdgeCore.Zof_eq]
  exact div_nonpos_of_nonpos_of_nonneg this hs.le

end PosChain

end Pos

/-- a lattice row with `t <= u_k < t + h` for `t > 0`. -/
lemma exists_row (h t : ℝ) (hh : 0 < h) (ht : 0 < t) : ∃ k : ℤ, 0 ≤ k ∧ t ≤ uNode h k ∧ uNode h k < t + h := by
  refine ⟨⌈t / h - 1 / 2⌉, ?_, ?_, ?_⟩
  · have h1 : t / h - 1 / 2 ≤ (⌈t / h - 1 / 2⌉ : ℝ) := Int.le_ceil _
    have h2 : (0 : ℝ) < t / h := div_pos ht hh
    have : (-1 : ℝ) < (⌈t / h - 1 / 2⌉ : ℝ) := by linarith
    have : (-1 : ℤ) < ⌈t / h - 1 / 2⌉ := by exact_mod_cast this
    omega
  · have h1 : t / h - 1 / 2 ≤ (⌈t / h - 1 / 2⌉ : ℝ) := Int.le_ceil _
    unfold uNode
    have : t / h ≤ (⌈t / h - 1 / 2⌉ : ℝ) + 1 / 2 := by linarith
    rw [div_le_iff₀ hh] at this
    linarith
  · have h1 : (⌈t / h - 1 / 2⌉ : ℝ) < t / h - 1 / 2 + 1 := Int.ceil_lt_add_one _
    unfold uNode
    have : ((⌈t / h - 1 / 2⌉ : ℝ) + 1 / 2) < t / h + 1 := by linarith
    have h3 : (((⌈t / h - 1 / 2⌉ : ℝ) + 1 / 2) * h) < (t / h + 1) * h := mul_lt_mul_of_pos_right this hh
    have h4 : (t / h + 1) * h = t + h := by field_simp
    linarith

/-! ### Q2: the patch-2 envelope of `psi-hat^L`, and of the exact solution -/

section Env2

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- **Q2.**  For a row `k` with `u_c - eta/2 < u_k <= u_c + 2 eta` and `Z_k <= 0`:
`|psi-hat^L_k| <= K (|lam_L| / kappa_b) E_-(a,Z_k) M_bal(a,Z_k)` (`phi_bd` on patch 2). -/
lemma psiHatL_env2 {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
    (hh : Fz.step N ≤ C.softH2) {k : ℤ} (hk0 : 0 ≤ k) (hku : C.uc μ - C.η / 2 < uNode (Fz.step N) k)
    (hku2 : uNode (Fz.step N) k ≤ C.uc μ + 2 * C.η) (hZ : C.Zof μ X N k ≤ 0) :
    |C.psiHatL μ X N k| ≤ softK C * (|C.lamL μ X N| / kappaBal (C.aOf μ X N)) *
      (Eminus (C.aOf μ X N) (C.Zof μ X N k) * Mbal (C.aOf μ X N) (C.Zof μ X N k)) := by
  have hhH1 : Fz.step N ≤ C.softH1 := hh.trans C.softH2_le_H1
  have hVpre : ((C.chain μ X N).rescale1 (softLam C μ X N)).PreValid C.cs (Fz.step N) m := C.valid μ hμ X hX N hN
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hhH1 hVpre
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  obtain ⟨-, hη, -⟩ := C.consts_pos
  obtain ⟨-, -, -, -, -, -, hNRu, hNRv⟩ := C.shape μ hμ X hX N hN
  have hP3' : ((C.chain μ X N).rescale1 (softLam C μ X N)).P = 3 := hP3
  have hk1 : (C.chain μ X N).jj 1 < k := by
    by_contra hcon
    have := SoftEdgeChart.uNode_mono_le hh0.le (not_lt.mp hcon)
    linarith
  have hkNR : k ≤ (C.chain μ X N).NR := by
    by_contra h2
    have := SoftEdgeChart.uNode_mono_le hh0.le (show (C.chain μ X N).NR + 1 ≤ k by omega)
    linarith
  have hk2 : k ≤ (C.chain μ X N).jj 2 := by
    by_contra hcon
    have hpos := Zof_pos_of_gt C hμ hX hN hhH1 hVpre (k := k) (mem_Icc.mpr ⟨by omega, hkNR⟩) hku2
    linarith
  have hpb := hVpre.phi_bd (p := 2) (mem_Icc.mpr ⟨by norm_num, by rw [hP3']; norm_num⟩) (j := k)
    (mem_Icc.mpr ⟨by simp only [Nat.add_one_sub_one] ; show (C.chain μ X N).jj 1 ≤ k; omega, by show k ≤ (C.chain μ X N).jj 2 + 1; omega⟩)
  have hphi : ((C.chain μ X N).rescale1 (softLam C μ X N)).phi (Fz.step N) 0 2 k = (C.chain μ X N).phi (Fz.step N) 0 2 k :=
    LadderData.phi_rescale1_of_ne _ _ _ 0 (by norm_num) k
  rw [hphi] at hpb
  have hW : (C.chain μ X N).W k = Eminus (C.aOf μ X N) (C.Zof μ X N k) :=
    C.W2_def μ hμ X hX N hN k (mem_Icc.mpr ⟨by omega, hk2⟩)
  have hM : (C.chain μ X N).M k = Mbal (C.aOf μ X N) (C.Zof μ X N k) :=
    C.M2_def μ hμ X hX N hN k (mem_Icc.mpr ⟨by omega, hkNR⟩)
  have hb : |(C.chain μ X N).phi (Fz.step N) 0 2 k| ≤ softK C * (Eminus (C.aOf μ X N) (C.Zof μ X N k) * Mbal (C.aOf μ X N) (C.Zof μ X N k)) := by
    have := hpb.1
    show _ ≤ _
    calc |(C.chain μ X N).phi (Fz.step N) 0 2 k| ≤ (C.cs.KA + C.cs.KB) * C.cs.Kw * (C.chain μ X N).W k * (C.chain μ X N).M k := this
      _ = _ := by rw [hW, hM]; unfold softK; ring
  have hκ := kappaBal_pos (C.aOf μ X N)
  rw [psiHatL_of_gt C μ X N hku, abs_mul, abs_div, abs_of_pos hκ]
  calc |C.lamL μ X N| * (|(C.chain μ X N).phi (Fz.step N) 0 2 k| / kappaBal (C.aOf μ X N))
      ≤ |C.lamL μ X N| * (softK C * (Eminus (C.aOf μ X N) (C.Zof μ X N k) * Mbal (C.aOf μ X N) (C.Zof μ X N k)) / kappaBal (C.aOf μ X N)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact div_le_div_of_nonneg_right hb hκ.le
    _ = _ := by ring

/-- **Q2' (the exact solution on the patch-2 rows).**  From item (1) (`propThaW2_item1`) and Q2: on a row `k <= N_R` with `u_c - eta/2 < u_k <= u_c + 2 eta`, `Z_k <= 0`,
`|psi_k| <= C_E (|lam_L|/kappa_b) E_-(a,Z_k) M_bal(a,Z_k)` (for `psi` the exact solution seeded by `psi-hat^L_0`). -/
theorem soft_env_psi {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) :
    ∃ CE h0 : ℝ, 0 < h0 ∧ 0 ≤ CE ∧ ∀ p ∈ P, ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ C.δ0 →
      ∀ ψ : ℤ → ℝ, JacSol Fz p N X (C.chain p X N).NR ψ → ψ 0 = C.psiHatL p X N 0 →
        ∀ k ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, C.uc p - C.η / 2 < uNode (Fz.step N) k →
          uNode (Fz.step N) k ≤ C.uc p + 2 * C.η → C.Zof p X N k ≤ 0 →
            |ψ k| ≤ CE * (|C.lamL p X N| / kappaBal (C.aOf p X N)) * (Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k)) := by
  obtain ⟨Cc, h0, clam, Clam, h0pos, hclam, H⟩ := propThaW2_item1 C hf hm hLm
  have hK0 := softK_nonneg C
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  refine ⟨softK C + |Cc| * CPC, min h0 (min C.softH2 (softHL C 1)),
    lt_min h0pos (lt_min C.softH2_pos (softHL_pos C 1)), by positivity, ?_⟩
  intro p hp N hN hstep X hX ψ hJ hseed k hk hku1 hku2 hZ
  have hs0 : Fz.step N ≤ h0 := hstep.trans (min_le_left _ _)
  have hs2 : Fz.step N ≤ C.softH2 := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsL : Fz.step N ≤ softHL C 1 := hstep.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := hs2.trans (C.softH2_le_H1.trans C.softH1_le_one)
  have hpow : Fz.step N ^ m * Lm (Fz.step N) ≤ 1 := by
    have h1 : Fz.step N ^ m ≤ Fz.step N := pow_le_of_le_one hh0.le hh1 (by omega)
    have h2 : Fz.step N * Lm (Fz.step N) ≤ 1 := softHL_spec C one_pos hh0 hsL
    have h3 := Lm_nonneg C hh0 hh1
    calc Fz.step N ^ m * Lm (Fz.step N) ≤ Fz.step N * Lm (Fz.step N) := mul_le_mul_of_nonneg_right h1 h3
      _ ≤ 1 := h2
  have hpow0 : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) := powLm_nonneg C hh0 hh1
  obtain ⟨hmain, -, -⟩ := H p hp N hN hs0 X hX
  obtain ⟨-, hPC⟩ := hmain ψ hJ hseed
  have hk' := mem_Icc.mp hk
  have herr := hPC k hk hku1 hku2
  have henv := psiHatL_env2 C hp hX hN hs2 hk'.1 hku1 hku2 hZ
  have hκ := kappaBal_pos (C.aOf p X N)
  have hmo := molv_upper hf (C.aOf p X N) (-(C.Zof p X N k))
  have hW : Wmol (C.aOf p X N) (-(C.Zof p X N k)) = Eminus (C.aOf p X N) (C.Zof p X N k) := Wmol_neg_of_nonpos _ hZ
  rw [hW, Mbal_neg] at hmo
  have hEM : 0 ≤ Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k) :=
    mul_nonneg (Eminus_pos _ _).le (Mbal_pos _ _).le
  have hlam0 : 0 ≤ |C.lamL p X N| / kappaBal (C.aOf p X N) := div_nonneg (abs_nonneg _) hκ.le
  -- the error term
  have herr2 : |ψ k - C.psiHatL p X N k| ≤ |Cc| * CPC * (|C.lamL p X N| / kappaBal (C.aOf p X N) *
      (Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))) := by
    refine herr.trans ?_
    have hmo' : Molv U V (C.aOf p X N) (-(C.Zof p X N k)) ≤ CPC * ((kappaBal (C.aOf p X N))⁻¹ *
        (Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))) := by
      refine hmo.trans (le_of_eq ?_); ring
    calc Cc * Fz.step N ^ m * Lm (Fz.step N) * |C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k))
        = (Cc * (Fz.step N ^ m * Lm (Fz.step N))) * (|C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) := by ring
      _ ≤ |Cc| * (|C.lamL p X N| * (CPC * ((kappaBal (C.aOf p X N))⁻¹ * (Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))))) := by
          apply mul_le_mul _ (mul_le_mul_of_nonneg_left hmo' (abs_nonneg _)) (mul_nonneg (abs_nonneg _) (molv_nonneg hf _ _)) (abs_nonneg _)
          calc Cc * (Fz.step N ^ m * Lm (Fz.step N)) ≤ |Cc * (Fz.step N ^ m * Lm (Fz.step N))| := le_abs_self _
            _ = |Cc| * (Fz.step N ^ m * Lm (Fz.step N)) := by rw [abs_mul, abs_of_nonneg hpow0]
            _ ≤ |Cc| * 1 := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
            _ = |Cc| := mul_one _
      _ = |Cc| * CPC * (|C.lamL p X N| / kappaBal (C.aOf p X N) * (Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))) := by
          field_simp
  calc |ψ k| = |C.psiHatL p X N k + (ψ k - C.psiHatL p X N k)| := by ring_nf
    _ ≤ |C.psiHatL p X N k| + |ψ k - C.psiHatL p X N k| := abs_add_le _ _
    _ ≤ softK C * (|C.lamL p X N| / kappaBal (C.aOf p X N)) * (Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))
        + |Cc| * CPC * (|C.lamL p X N| / kappaBal (C.aOf p X N) * (Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))) :=
        add_le_add henv herr2
    _ = _ := by ring

end Env2

/-! ### Q1/Q5: the rows `k_0, k_0 + 1`, the smallness `e_{k_0} <= exp(-c_Q/h)` and the one-step ratio -/

section Rows

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- the decay exponent `c_Q = sqrt(c_{z1}/8) d_- eta / 16`. -/
def softCQ : ℝ := Real.sqrt (C.cz1 / 8) * C.dm * C.η / 16

lemma softCQ_pos : 0 < softCQ C := by
  obtain ⟨-, hη, hdm, -⟩ := C.consts_pos
  have hz := C.consts_pos2.2
  unfold softCQ
  have : 0 < Real.sqrt (C.cz1 / 8) := Real.sqrt_pos.mpr (by positivity)
  positivity

section RowsAt

variable {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
  (hh : Fz.step N ≤ C.softH2) (hh16 : Fz.step N ≤ C.η / 16)
  {k0 : ℤ} (hk0 : 0 ≤ k0) (hlo : C.uc μ + 3 * C.η / 8 ≤ uNode (Fz.step N) k0)
  (hhi : uNode (Fz.step N) k0 < C.uc μ + 3 * C.η / 8 + Fz.step N)

include hμ hX hN hh hh16 hk0 hlo hhi

/-- **Q1.**  The rows `k_0, k_0 + 1` are on patch 3 (`j_2 + 1 <= k_0`, `k_0 + 1 <= N_R`) and `Z > 0` there. -/
lemma quant_rows :
    (C.chain μ X N).jj 2 + 1 ≤ k0 ∧ k0 + 1 ≤ (C.chain μ X N).NR ∧ 0 < C.Zof μ X N k0 ∧ 0 < C.Zof μ X N (k0 + 1) := by
  have hhH1 : Fz.step N ≤ C.softH1 := hh.trans C.softH2_le_H1
  have hVpre : ((C.chain μ X N).rescale1 (softLam C μ X N)).PreValid C.cs (Fz.step N) m := C.valid μ hμ X hX N hN
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hhH1 hVpre
  obtain ⟨-, hη, -⟩ := C.consts_pos
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  obtain ⟨-, -, -, -, -, -, hNRu, hNRv⟩ := C.shape μ hμ X hX N hN
  have hj2lt := j2_lt C hμ hX hN hh hVpre
  have hsucc := uNode_succ_sub' (Fz.step N) k0
  have h1 : (C.chain μ X N).jj 2 + 1 ≤ k0 := by
    by_contra hcon
    have := SoftEdgeChart.uNode_mono_le hh0.le (show k0 ≤ (C.chain μ X N).jj 2 by omega)
    linarith
  have h2 : k0 + 1 ≤ (C.chain μ X N).NR := by
    by_contra hcon
    have := SoftEdgeChart.uNode_mono_le hh0.le (show (C.chain μ X N).NR + 1 ≤ k0 + 1 by omega)
    linarith
  refine ⟨h1, h2, ?_, ?_⟩
  · exact Zof_pos_of_gt C hμ hX hN hhH1 hVpre (k := k0) (mem_Icc.mpr ⟨h1, by omega⟩) (by linarith)
  · exact Zof_pos_of_gt C hμ hX hN hhH1 hVpre (k := k0 + 1) (mem_Icc.mpr ⟨by omega, h2⟩) (by linarith)

/-- **Q5.**  `e_{k_0} = E_-(a, -Z_{k_0}) <= exp(-c_Q/h)` (`Eminus_decay` from `-Z_{k_0}` to `-zeta(5 eta/16)/sqrt h`, where the Liouville--Green margin `c_{z1}/(8h)` holds). -/
lemma Eminus_quant_small :
    Eminus (C.aOf μ X N) (-(C.Zof μ X N k0)) ≤ Real.exp (-(softCQ C / Fz.step N)) := by
  have hhH1 : Fz.step N ≤ C.softH1 := hh.trans C.softH2_le_H1
  have hVpre : ((C.chain μ X N).rescale1 (softLam C μ X N)).PreValid C.cs (Fz.step N) m := C.valid μ hμ X hX N hN
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hμ hX hN hhH1 hVpre
  obtain ⟨-, hη, hdm, hdmp, -⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hz1 := C.consts_pos2.2
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hs2 : Real.sqrt (Fz.step N) ^ 2 = Fz.step N := Real.sq_sqrt hh0.le
  have hα := C.abs_alpha_le hX
  obtain ⟨-, hj2lt', -, -⟩ := quant_rows C hμ hX hN hh hh16 hk0 hlo hhi
  have hj2lt := j2_lt C hμ hX hN hh hVpre
  have hsucc := uNode_succ_sub' (Fz.step N) ((C.chain μ X N).jj 2)
  have hxlo : -(2 * C.η) ≤ uNode (Fz.step N) ((C.chain μ X N).jj 2 + 1) - C.uc μ := by
    have : uNode (Fz.step N) ((C.chain μ X N).jj 1 + 1) ≤ uNode (Fz.step N) ((C.chain μ X N).jj 2 + 1) :=
      SoftEdgeChart.uNode_mono_le hh0.le (by omega)
    linarith
  have hxhat : uNode (Fz.step N) ((C.chain μ X N).jj 2 + 1) - C.uc μ ≤ 5 * C.η / 16 := by linarith
  have hmv1 := C.zeta_mvt hμ hα hxlo hxhat (by linarith : 5 * C.η / 16 ≤ 2 * C.η)
  have hζhat : 0 < C.zeta μ (Fz.bandHi μ - X) (5 * C.η / 16) := by
    have := mul_nonneg hdm.le (sub_nonneg.mpr hxhat)
    linarith [hmv1.1]
  have hxk0 : 5 * C.η / 16 ≤ uNode (Fz.step N) k0 - C.uc μ := by linarith
  have hxk0' : uNode (Fz.step N) k0 - C.uc μ ≤ 2 * C.η := by linarith
  have hmv2 := C.zeta_mvt hμ hα (by linarith : -(2 * C.η) ≤ 5 * C.η / 16) hxk0 hxk0'
  have hgap : C.dm * (C.η / 16) ≤ C.zeta μ (Fz.bandHi μ - X) (uNode (Fz.step N) k0 - C.uc μ) - C.zeta μ (Fz.bandHi μ - X) (5 * C.η / 16) := by
    have : C.dm * (C.η / 16) ≤ C.dm * (uNode (Fz.step N) k0 - C.uc μ - 5 * C.η / 16) :=
      mul_le_mul_of_nonneg_left (by linarith) hdm.le
    linarith [hmv2.1]
  set zh : ℝ := C.zeta μ (Fz.bandHi μ - X) (5 * C.η / 16) / Real.sqrt (Fz.step N) with hzh
  have hzhpos : 0 < zh := div_pos hζhat hs
  have hZk : C.Zof μ X N k0 = C.zeta μ (Fz.bandHi μ - X) (uNode (Fz.step N) k0 - C.uc μ) / Real.sqrt (Fz.step N) := rfl
  have hz12 : -(C.Zof μ X N k0) ≤ -zh := by
    rw [neg_le_neg_iff, hZk, hzh]
    apply div_le_div_of_nonneg_right _ hs.le
    have : 0 ≤ C.dm * (C.η / 16) := by positivity
    linarith
  have hmar : (Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N)) ^ 2 ≤ (-zh) ^ 2 / 4 + C.aOf μ X N := by
    have hq := C.Zq_lb hμ hX hhH1 (x := 5 * C.η / 16) (by rw [abs_of_pos (by linarith)]; linarith)
      (by rw [abs_of_pos (by linarith)]; linarith)
    have e : (-zh) ^ 2 / 4 + C.aOf μ X N = (C.zeta μ (Fz.bandHi μ - X) (5 * C.η / 16) ^ 2 / 4 - C.muTilde μ X N) / Fz.step N := by
      rw [neg_sq, hzh, SoftEdgeCore.aOf_eq, div_pow, hs2]; field_simp; ring
    rw [e, div_pow, Real.sq_sqrt (by positivity), hs2]
    exact div_le_div_of_nonneg_right hq hh0.le
  have hdec := Eminus_decay (C.aOf μ X N) (Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N)) hz12 (by linarith) (by positivity) hmar
  have hexp : softCQ C / Fz.step N ≤ Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N) * (-zh - -(C.Zof μ X N k0)) := by
    have hdiff : C.dm * (C.η / 16) / Real.sqrt (Fz.step N) ≤ -zh - -(C.Zof μ X N k0) := by
      rw [hZk, hzh]
      have : -(C.zeta μ (Fz.bandHi μ - X) (5 * C.η / 16) / Real.sqrt (Fz.step N)) - -(C.zeta μ (Fz.bandHi μ - X) (uNode (Fz.step N) k0 - C.uc μ) / Real.sqrt (Fz.step N))
          = (C.zeta μ (Fz.bandHi μ - X) (uNode (Fz.step N) k0 - C.uc μ) - C.zeta μ (Fz.bandHi μ - X) (5 * C.η / 16)) / Real.sqrt (Fz.step N) := by ring
      rw [this]
      exact div_le_div_of_nonneg_right hgap hs.le
    have hq0 : 0 ≤ Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N) := by positivity
    calc softCQ C / Fz.step N = Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N) * (C.dm * (C.η / 16) / Real.sqrt (Fz.step N)) := by
          rw [div_mul_div_comm, Real.mul_self_sqrt hh0.le]; unfold softCQ; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiff hq0
  have hone := Eminus_le_one (C.aOf μ X N) (show -zh ≤ 0 by linarith)
  calc Eminus (C.aOf μ X N) (-(C.Zof μ X N k0))
      ≤ Real.exp (-(Real.sqrt (C.cz1 / 8) / Real.sqrt (Fz.step N) * (-zh - -(C.Zof μ X N k0)))) * Eminus (C.aOf μ X N) (-zh) := hdec
    _ ≤ Real.exp (-(softCQ C / Fz.step N)) * 1 :=
        mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hone (Eminus_pos _ _).le (Real.exp_pos _).le
    _ = _ := mul_one _

/-- **Q5 (ratio).**  `e_{k_0} <= w_bar e_{k_0+1}` and `e_{k_0+1} <= e_{k_0}` (one-step comparison of `E_-`, `w_bar = C.tCw`). -/
lemma Eminus_quant_ratio :
    Eminus (C.aOf μ X N) (-(C.Zof μ X N (k0 + 1))) ≤ Eminus (C.aOf μ X N) (-(C.Zof μ X N k0)) ∧
    Eminus (C.aOf μ X N) (-(C.Zof μ X N k0)) ≤ C.tCw * Eminus (C.aOf μ X N) (-(C.Zof μ X N (k0 + 1))) := by
  have hhH1 : Fz.step N ≤ C.softH1 := hh.trans C.softH2_le_H1
  obtain ⟨-, hη, hdm, hdmp, -, hcF, -, hcZ⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := hhH1.trans C.softH1_le_one
  have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hs2 : Real.sqrt (Fz.step N) ^ 2 = Fz.step N := Real.sq_sqrt hh0.le
  have hα := C.abs_alpha_le hX
  obtain ⟨-, -, hZ0, hZ1⟩ := quant_rows C hμ hX hN hh hh16 hk0 hlo hhi
  have hsucc := uNode_succ_sub' (Fz.step N) k0
  have hx0 : uNode (Fz.step N) k0 - C.uc μ ≤ 2 * C.η := by linarith
  have hx1 : uNode (Fz.step N) (k0 + 1) - C.uc μ ≤ 2 * C.η := by linarith
  have hmvt := C.zeta_mvt hμ hα (by linarith : -(2 * C.η) ≤ uNode (Fz.step N) k0 - C.uc μ)
    (by linarith : uNode (Fz.step N) k0 - C.uc μ ≤ uNode (Fz.step N) (k0 + 1) - C.uc μ) hx1
  have hsub : uNode (Fz.step N) (k0 + 1) - C.uc μ - (uNode (Fz.step N) k0 - C.uc μ) = Fz.step N := by linarith
  rw [hsub] at hmvt
  have hZ01 : C.Zof μ X N k0 ≤ C.Zof μ X N (k0 + 1) := by
    rw [SoftEdgeCore.Zof_eq, SoftEdgeCore.Zof_eq]
    apply div_le_div_of_nonneg_right _ hs.le
    have := mul_nonneg hdm.le hh0.le
    linarith [hmvt.1]
  refine ⟨Eminus_mono _ (by linarith) (by linarith), ?_⟩
  have hdiffZ : C.Zof μ X N (k0 + 1) - C.Zof μ X N k0 ≤ C.dp * Real.sqrt (Fz.step N) := by
    rw [SoftEdgeCore.Zof_eq, SoftEdgeCore.Zof_eq, ← sub_div, div_le_iff₀ hs]
    have : C.dp * Real.sqrt (Fz.step N) * Real.sqrt (Fz.step N) = C.dp * Fz.step N := by rw [mul_assoc, ← sq, hs2]
    rw [this]; exact hmvt.2
  have hzb1 := zeta_abs_le C hμ hα (x := uNode (Fz.step N) (k0 + 1) - C.uc μ) (by rw [abs_le]; constructor <;> linarith)
  have hZ1abs : |C.Zof μ X N (k0 + 1)| ≤ (C.cZ * C.δ0 + 2 * C.dp * C.η) / Real.sqrt (Fz.step N) := by
    rw [SoftEdgeCore.Zof_eq, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right hzb1 hs.le
  have hamax : Real.sqrt (max (C.aOf μ X N) 0) ≤ Real.sqrt (C.Cmu * (1 + ((q / 2 : ℕ) : ℝ))) / Real.sqrt (Fz.step N) := by
    rw [← Real.sqrt_div (by have := C.consts_pos2.1; positivity)]
    apply Real.sqrt_le_sqrt
    have hmu := C.muTilde_abs_le hμ hX hh1
    rw [SoftEdgeCore.aOf_eq]
    apply max_le
    · have : -(1 / Fz.step N) * C.muTilde μ X N ≤ C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)) / Fz.step N := by
        have h1 : -(1 / Fz.step N) * C.muTilde μ X N = (-C.muTilde μ X N) / Fz.step N := by ring
        rw [h1]
        exact div_le_div_of_nonneg_right (by linarith [abs_le.mp hmu]) hh0.le
      exact this
    · exact div_nonneg (mul_nonneg C.consts_pos2.1 (by positivity)) hh0.le
  have hexp : (C.Zof μ X N (k0 + 1) - C.Zof μ X N k0) * (|C.Zof μ X N (k0 + 1)| / 2 + Real.sqrt (max (C.aOf μ X N) 0)) ≤ C.tDw := by
    have hfac : |C.Zof μ X N (k0 + 1)| / 2 + Real.sqrt (max (C.aOf μ X N) 0) ≤
        ((C.cZ * C.δ0 + 2 * C.dp * C.η) / 2 + Real.sqrt (C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)))) / Real.sqrt (Fz.step N) := by
      have := add_le_add (div_le_div_of_nonneg_right hZ1abs (by norm_num : (0 : ℝ) ≤ 2)) hamax
      calc _ ≤ _ := this
        _ = _ := by field_simp
    have hnn : 0 ≤ |C.Zof μ X N (k0 + 1)| / 2 + Real.sqrt (max (C.aOf μ X N) 0) := by positivity
    have hd0 : 0 ≤ C.Zof μ X N (k0 + 1) - C.Zof μ X N k0 := sub_nonneg.mpr hZ01
    calc _ ≤ (C.dp * Real.sqrt (Fz.step N)) * (((C.cZ * C.δ0 + 2 * C.dp * C.η) / 2 + Real.sqrt (C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)))) / Real.sqrt (Fz.step N)) :=
          mul_le_mul hdiffZ hfac hnn (by positivity)
      _ = C.tDw := by unfold SoftEdgeChart.tDw; field_simp
  have hr := Eminus_ratio (C.aOf μ X N) (z1 := -(C.Zof μ X N (k0 + 1))) (z2 := -(C.Zof μ X N k0)) (by linarith) (by linarith)
  refine le_trans hr ?_
  have e1 : -(C.Zof μ X N k0) - -(C.Zof μ X N (k0 + 1)) = C.Zof μ X N (k0 + 1) - C.Zof μ X N k0 := by ring
  rw [e1, abs_neg]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (Eminus_pos _ _).le

end RowsAt

end Rows

/-! ### Q3: the exact right solution is recessive on the right forbidden side (item (1) for `psi^R`, mirror transport) -/

section RightRecessive

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- **Q3.**  For `psi'` the exact solution of the mirror recurrence seeded by `psi-hat^{L,R}_0` and a row `k` with `u_c - 2 eta <= u_k < u_c + eta/2`, `Z_k >= 0`:
`|psi'_{N-k}| <= C_E (|lam_R|/kappa_b) E_-(a,-Z_k) M_bal(a,Z_k)` (`psi^R_k = psi'_{N-k}`; the mirror row `N - k` is a patch-2 row of `CR`). -/
theorem soft_right_recessive {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (hM : SoftMirror CL CR) :
    ∃ CE h0 : ℝ, 0 < h0 ∧ 0 ≤ CE ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      ∀ ψ' : ℤ → ℝ, JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR ψ' → ψ' 0 = CR.psiHatL p X N 0 →
        ∀ k : ℤ, 0 ≤ k → k ≤ N → CL.uc p - 2 * CL.η ≤ uNode (Fz.step N) k → uNode (Fz.step N) k < CL.uc p + CL.η / 2 →
          0 ≤ CL.Zof p X N k →
            |ψ' ((N : ℤ) - k)| ≤ CE * (|CR.lamL p X N| / kappaBal (CL.aOf p X N)) *
              (Eminus (CL.aOf p X N) (-(CL.Zof p X N k)) * Mbal (CL.aOf p X N) (CL.Zof p X N k)) := by
  obtain ⟨CE, h0, h0pos, hCE, H⟩ := soft_env_psi CR hf hm hLm
  refine ⟨CE, h0, h0pos, hCE, ?_⟩
  intro p hp N hN hstep X hX ψ' hJ hseed k hk0 hkN hlo hhi hZ
  obtain ⟨huc, hz, hmu, hη, hδ, hN0⟩ := hM
  have hN' : CR.N0 ≤ N := by rw [hN0]; exact hN
  have hX' : |X - (mirrorFamily Fz).bandHi p| ≤ CR.δ0 := by rw [bandHi_mirror, hδ]; exact hX
  have hmir : uNode (Fz.step N) ((N : ℤ) - k) = Fz.L - uNode (Fz.step N) k := uNode_mirror Fz.L (Fz.step N) N k (step_mul_succ Fz N)
  have hucR := huc p hp
  have hηR := hη
  have hhh : (mirrorFamily Fz).step N = Fz.step N := rfl
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  obtain ⟨-, -, -, -, -, -, hNRu, hNRv⟩ := CR.shape p hp X hX' N hN'
  have hjNR : (N : ℤ) - k ≤ (CR.chain p X N).NR := by
    by_contra hcon
    have := SoftEdgeChart.uNode_mono_le hh0.le (show (CR.chain p X N).NR + 1 ≤ (N : ℤ) - k by omega)
    have hNRv' : CR.uc p + 2 * CR.η < uNode (Fz.step N) ((CR.chain p X N).NR + 1) := hNRv
    rw [hmir] at this
    rw [hucR, hηR] at hNRv'
    linarith
  have hZR : CR.Zof p X N ((N : ℤ) - k) ≤ 0 := by
    rw [Zof_mirror ⟨huc, hz, hmu, hη, hδ, hN0⟩ hp X N k]; linarith
  have hbd := H p hp N hN' (by rw [hhh]; exact hstep) X hX' ψ' hJ hseed ((N : ℤ) - k)
    (mem_Icc.mpr ⟨by omega, hjNR⟩) (by rw [hhh, hmir, hucR, hηR]; linarith) (by rw [hhh, hmir, hucR, hηR]; linarith) hZR
  rw [Zof_mirror ⟨huc, hz, hmu, hη, hδ, hN0⟩ hp X N k, aOf_mirror ⟨huc, hz, hmu, hη, hδ, hN0⟩ hp X N,
    Mbal_neg] at hbd
  exact hbd

end RightRecessive

/-! ### Q4: the abstract Casoratian inequality -/

/-- `|W_k(F,G)| <= |A_k| (|F_{k+1}| |G_k| + |F_k| |G_{k+1}|)`. -/
lemma cas_le (A F G : ℤ → ℝ) (k : ℤ) :
    |cas A F G k| ≤ |A k| * (|F (k + 1)| * |G k| + |F k| * |G (k + 1)|) := by
  unfold cas
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc |F (k + 1) * G k - F k * G (k + 1)| ≤ |F (k + 1) * G k| + |F k * G (k + 1)| := abs_sub _ _
    _ = _ := by rw [abs_mul, abs_mul]

lemma cas_psih (A f g ψh : ℤ → ℝ) (k : ℤ) (μ cc s : ℝ) (h0 : ψh k = μ * (cc * f k + s * g k))
    (h1 : ψh (k + 1) = μ * (cc * f (k + 1) + s * g (k + 1))) :
    cas A ψh g k = μ * cc * cas A f g k := by
  unfold cas; rw [h0, h1]; ring

lemma cas_sub_left (A F G H : ℤ → ℝ) (k : ℤ) : cas A (fun n => F n - H n) G k = cas A F G k - cas A H G k := by
  unfold cas; ring

/-- **Q4: the Casoratian core of the quantisation.**  Abstract form (all hypotheses are pointwise bounds at the two rows `k, k+1`): `psi-hat = mu (cc f + s g)` there, `|W_k(f,g)| >= cm omega`,
`|g_j| <= K e_j M_j` (recessive member), `|psi^L_j| <= |mu| C_r e_j M_j` (recessive exact solution), `|psi^L_j - psi-hat_j| <= |mu| C_h e_j^{-1} M_j` (item (1), growing weight), `e_{k+1} <= e_k <= w_b e_{k+1}`,
`M_k M_{k+1} <= C_M omega`.  Then `|cc| cm <= C_A K C_M (2 C_r e_k^2 + C_h (w_b + 1))`. -/
lemma quant_combine (A f g ψL ψh : ℤ → ℝ) (k : ℤ) (μ cc s cm ω CA K Cm Cr Ch wb e0 e1 M0 M1 : ℝ)
    (hμ : 0 < |μ|) (hω : 0 < ω)
    (h0 : ψh k = μ * (cc * f k + s * g k)) (h1 : ψh (k + 1) = μ * (cc * f (k + 1) + s * g (k + 1)))
    (hcas : cm * ω ≤ |cas A f g k|) (hA : |A k| ≤ CA) (hCA : 0 ≤ CA) (hK : 0 ≤ K)
    (he0 : 0 < e0) (he1 : 0 < e1) (hMono : e1 ≤ e0) (hRat : e0 ≤ wb * e1) (hwb : 0 ≤ wb) (hCr : 0 ≤ Cr) (hCh : 0 ≤ Ch)
    (hM0 : 0 < M0) (hM1 : 0 < M1) (hMM : M0 * M1 ≤ Cm * ω)
    (hg0 : |g k| ≤ K * (e0 * M0)) (hg1 : |g (k + 1)| ≤ K * (e1 * M1))
    (hL0 : |ψL k| ≤ |μ| * Cr * (e0 * M0)) (hL1 : |ψL (k + 1)| ≤ |μ| * Cr * (e1 * M1))
    (hE0 : |ψL k - ψh k| ≤ |μ| * Ch * (e0⁻¹ * M0)) (hE1 : |ψL (k + 1) - ψh (k + 1)| ≤ |μ| * Ch * (e1⁻¹ * M1)) :
    |cc| * cm ≤ CA * K * Cm * (2 * Cr * e0 ^ 2 + Ch * (wb + 1)) := by
  have hmain : |μ| * |cc| * (cm * ω) ≤ |cas A ψL g k| + |cas A (fun n => ψL n - ψh n) g k| := by
    have e1' := cas_psih A f g ψh k μ cc s h0 h1
    have e2 := cas_sub_left A ψL g ψh k
    have : cas A ψh g k = cas A ψL g k - cas A (fun n => ψL n - ψh n) g k := by rw [e2]; ring
    have h3 : |μ * cc * cas A f g k| = |μ| * |cc| * |cas A f g k| := by rw [abs_mul, abs_mul]
    have h4 : |μ| * |cc| * (cm * ω) ≤ |μ| * |cc| * |cas A f g k| :=
      mul_le_mul_of_nonneg_left hcas (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    calc |μ| * |cc| * (cm * ω) ≤ |μ| * |cc| * |cas A f g k| := h4
      _ = |cas A ψh g k| := by rw [e1', h3]
      _ ≤ _ := by rw [this]; exact abs_sub _ _
  have hc1 : |cas A ψL g k| ≤ CA * (|μ| * Cr * (e1 * M1) * (K * (e0 * M0)) + |μ| * Cr * (e0 * M0) * (K * (e1 * M1))) := by
    refine (cas_le A ψL g k).trans ?_
    apply mul_le_mul hA _ (by positivity) hCA
    apply add_le_add
    · exact mul_le_mul hL1 hg0 (abs_nonneg _) (by positivity)
    · exact mul_le_mul hL0 hg1 (abs_nonneg _) (by positivity)
  have hc2 : |cas A (fun n => ψL n - ψh n) g k| ≤
      CA * (|μ| * Ch * (e1⁻¹ * M1) * (K * (e0 * M0)) + |μ| * Ch * (e0⁻¹ * M0) * (K * (e1 * M1))) := by
    refine (cas_le A (fun n => ψL n - ψh n) g k).trans ?_
    apply mul_le_mul hA _ (by positivity) hCA
    apply add_le_add
    · exact mul_le_mul hE1 hg0 (abs_nonneg _) (by positivity)
    · exact mul_le_mul hE0 hg1 (abs_nonneg _) (by positivity)
  have hMM' : 0 ≤ M0 * M1 := by positivity
  have s1 : |μ| * Cr * (e1 * M1) * (K * (e0 * M0)) + |μ| * Cr * (e0 * M0) * (K * (e1 * M1))
      = 2 * |μ| * Cr * K * (e0 * e1) * (M0 * M1) := by ring
  have s2 : |μ| * Ch * (e1⁻¹ * M1) * (K * (e0 * M0)) + |μ| * Ch * (e0⁻¹ * M0) * (K * (e1 * M1))
      = |μ| * Ch * K * (e0 / e1 + e1 / e0) * (M0 * M1) := by field_simp
  have hr1 : e0 / e1 ≤ wb := by rw [div_le_iff₀ he1]; exact hRat
  have hr2 : e1 / e0 ≤ 1 := by rw [div_le_one he0]; exact hMono
  have he01 : e0 * e1 ≤ e0 ^ 2 := by nlinarith
  have hsum : e0 / e1 + e1 / e0 ≤ wb + 1 := by linarith
  have hfin : |μ| * |cc| * (cm * ω) ≤ CA * (2 * |μ| * Cr * K * (e0 * e1) * (M0 * M1) + |μ| * Ch * K * (e0 / e1 + e1 / e0) * (M0 * M1)) := by
    refine hmain.trans ?_
    refine (add_le_add hc1 hc2).trans ?_
    rw [← mul_add, s1, s2]
  have hB : CA * (2 * |μ| * Cr * K * (e0 * e1) * (M0 * M1) + |μ| * Ch * K * (e0 / e1 + e1 / e0) * (M0 * M1))
      ≤ CA * (2 * |μ| * Cr * K * e0 ^ 2 * (Cm * ω) + |μ| * Ch * K * (wb + 1) * (Cm * ω)) := by
    apply mul_le_mul_of_nonneg_left _ hCA
    apply add_le_add
    · calc 2 * |μ| * Cr * K * (e0 * e1) * (M0 * M1) ≤ 2 * |μ| * Cr * K * e0 ^ 2 * (M0 * M1) := by
            apply mul_le_mul_of_nonneg_right _ hMM'
            apply mul_le_mul_of_nonneg_left he01; positivity
        _ ≤ _ := mul_le_mul_of_nonneg_left hMM (by positivity)
    · calc |μ| * Ch * K * (e0 / e1 + e1 / e0) * (M0 * M1) ≤ |μ| * Ch * K * (wb + 1) * (M0 * M1) := by
            apply mul_le_mul_of_nonneg_right _ hMM'
            apply mul_le_mul_of_nonneg_left hsum; positivity
        _ ≤ _ := mul_le_mul_of_nonneg_left hMM (by positivity)
  have hfin2 := hfin.trans hB
  have hpos : 0 < |μ| * ω := mul_pos hμ hω
  have : (|cc| * cm) * (|μ| * ω) ≤ (CA * K * Cm * (2 * Cr * e0 ^ 2 + Ch * (wb + 1))) * (|μ| * ω) := by
    calc (|cc| * cm) * (|μ| * ω) = |μ| * |cc| * (cm * ω) := by ring
      _ ≤ _ := hfin2
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hpos

/-! ### Q6: quantisation -/

lemma row_le_N {Par : Type*} (F : SymbolFamily Par) (N : ℕ) {j : ℤ} (hj : uNode (F.step N) j < F.L) : j ≤ N := by
  have hL := step_mul_succ F N
  have hh : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  unfold uNode at hj
  by_contra hcon
  have h1 : (N : ℤ) + 1 ≤ j := by omega
  have h2 : ((N : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast h1
  nlinarith

section Quant

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- **Q6 = E8: quantisation at the soft edge** (app_thmA Step 5; `prop:tha-W2` (3), the condition `|cos(pi a)| <= C h^m Lm` and the absence of eigenvalues with `a > 0`).
Let `psi^L` be the exact solution seeded by `psi-hat^L_0` and `psi'` that of the mirror recurrence seeded by `psi-hat^{L,R}_0`, with `psi^L_n = kappa psi'_{N-n}` (an eigenvalue: `psiL_eq_kappa_psiR`).
**Premise `hkap`** (Step 4 (b), chain step E5, not proved here): `|kappa| |lam_R| <= C_k |lam_L|`.  Then `a <= 0` and `|cos(pi a)| <= C_q h^m Lm(h)`. -/
theorem soft_quant {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (hM : SoftMirror CL CR) (Ck : ℝ) :
    ∃ Cq h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      ∀ (ψL ψ' : ℤ → ℝ) (κ : ℝ),
        JacSol Fz p N X (CL.chain p X N).NR ψL → ψL 0 = CL.psiHatL p X N 0 →
        JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR ψ' → ψ' 0 = CR.psiHatL p X N 0 →
        (∀ n ∈ rowsOf N, ψL n = κ * ψ' ((N : ℤ) - n)) →
        |κ| * |CR.lamL p X N| ≤ Ck * |CL.lamL p X N| →
        CL.aOf p X N ≤ 0 ∧ |Real.cos (Real.pi * CL.aOf p X N)| ≤ Cq * Fz.step N ^ m * Lm (Fz.step N) := by
  obtain ⟨Cc, h0a, clam, Clam, h0apos, hclam, Ha⟩ := propThaW2_item1 CL hf hm hLm
  obtain ⟨CE, h0b, h0bpos, hCE, Hb⟩ := soft_right_recessive CL CR hf hm hLm hM
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  have hK0 := softK_nonneg CL
  obtain ⟨-, hη, hdm, hdmp, -⟩ := CL.consts_pos
  have hcz1 := CL.consts_pos2.2
  have hcm := CL.cs.cm_pos
  have hCA0 : 0 ≤ CL.CA := CL.consts_pos3.1
  set Ck' : ℝ := max Ck 0 with hCk'
  have hCk'0 : 0 ≤ Ck' := le_max_right _ _
  set Cm : ℝ := ((CL.cz1 / 8) * (CL.cz1 / 8)) ^ (-(1 : ℝ) / 4) with hCm
  have hCm0 : 0 ≤ Cm := Real.rpow_nonneg (by positivity) _
  set wb : ℝ := CL.tCw with hwb
  have hwb0 : 0 ≤ wb := (Real.exp_pos _).le
  set Fexp : ℝ := (Nat.factorial (m + 1) : ℝ) / (2 * softCQ CL) ^ (m + 1) with hFexp
  have hcQ := softCQ_pos CL
  have hFexp0 : 0 ≤ Fexp := by positivity
  set Cq0 : ℝ := CL.CA * softK CL * Cm / CL.cs.cm * (2 * CE * Ck' * Fexp + |Cc| * CPC * (wb + 1)) with hCq0
  have hCq00 : 0 ≤ Cq0 := by positivity
  set eps : ℝ := 1 / (Cq0 + 1) with heps
  have hepspos : 0 < eps := by positivity
  refine ⟨Cq0 * Real.sqrt (Real.pi / 2),
    min h0a (min h0b (min CL.softH2 (min (CL.η / 16) (min (softHL CL 1) (softHL CL eps))))),
    lt_min h0apos (lt_min h0bpos (lt_min CL.softH2_pos (lt_min (by positivity) (lt_min (softHL_pos CL 1) (softHL_pos CL eps))))), ?_⟩
  intro p hp N hN hstep X hX ψL ψ' κ hJL hseedL hJR hseedR hrel hkap
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs0a : Fz.step N ≤ h0a := hstep.trans (min_le_left _ _)
  have hs0b : Fz.step N ≤ h0b := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs2 : Fz.step N ≤ CL.softH2 := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs16 : Fz.step N ≤ CL.η / 16 :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hsL1 : Fz.step N ≤ softHL CL 1 :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hsLe : Fz.step N ≤ softHL CL eps :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hhH1 : Fz.step N ≤ CL.softH1 := hs2.trans CL.softH2_le_H1
  have hh1 : Fz.step N ≤ 1 := hhH1.trans CL.softH1_le_one
  have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hα := CL.abs_alpha_le hX
  obtain ⟨huc0, huc1⟩ := CL.ucη_in p hp
  obtain ⟨k0, hk0, hlo, hhi⟩ := exists_row (Fz.step N) (CL.uc p + 3 * CL.η / 8) hh0 (by linarith)
  obtain ⟨hjj2, hk0NR, hZ0, hZ1⟩ := quant_rows CL hp hX hN hs2 hs16 hk0 hlo hhi
  have hsmall := Eminus_quant_small CL hp hX hN hs2 hs16 hk0 hlo hhi
  obtain ⟨hMono, hRat⟩ := Eminus_quant_ratio CL hp hX hN hs2 hs16 hk0 hlo hhi
  have hsucc := uNode_succ_sub' (Fz.step N) k0
  have hVpre : ((CL.chain p X N).rescale1 (softLam CL p X N)).PreValid CL.cs (Fz.step N) m := CL.valid p hp X hX N hN
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := CL.soft_pos hp hX hN hhH1 hVpre
  obtain ⟨-, -, -, -, -, -, hNRu, hNRv⟩ := CL.shape p hp X hX N hN
  have hP3' : ((CL.chain p X N).rescale1 (softLam CL p X N)).P = 3 := hP3
  have hj3 : (CL.chain p X N).jj 3 = (CL.chain p X N).NR - 1 := by
    have := hVpre.jj_last
    rwa [hP3'] at this
  have hκ := kappaBal_pos (CL.aOf p X N)
  obtain ⟨hmainA, hlowA, -⟩ := Ha p hp N hN hs0a X hX
  obtain ⟨-, hPCA⟩ := hmainA ψL hJL hseedL
  have hlam0 : 0 < |CL.lamL p X N| := by
    have h1 : 0 < clam * (softLam CL p X N * kappaBal (CL.aOf p X N)) := by
      have := softLam_pos CL p X N
      positivity
    exact lt_of_lt_of_le h1 hlowA
  set a := CL.aOf p X N with ha_def
  set κb := kappaBal a with hκb
  set μ : ℝ := CL.lamL p X N / κb with hμdef
  have hμ : 0 < |μ| := by
    rw [hμdef, abs_div, abs_of_pos hκ]; positivity
  have hμabs : |μ| = |CL.lamL p X N| / κb := by rw [hμdef, abs_div, abs_of_pos hκ]
  set cc : ℝ := if a ≤ 0 then Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * a) else 1 with hccdef
  set sc : ℝ := if a ≤ 0 then Real.sin (Real.pi * a) else 0 with hscdef
  set Ch : ℝ := |Cc| * CPC * (Fz.step N ^ m * Lm (Fz.step N)) with hCh
  have hpow0 : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) := powLm_nonneg CL hh0 hh1
  have hCh0 : 0 ≤ Ch := by positivity
  -- per-row facts
  have rowfacts : ∀ j : ℤ, (CL.chain p X N).jj 2 + 1 ≤ j → j + 1 ≤ (CL.chain p X N).NR + 1 →
      0 < CL.Zof p X N j → CL.uc p + 3 * CL.η / 8 ≤ uNode (Fz.step N) j → uNode (Fz.step N) j < CL.uc p + CL.η / 2 →
      |(CL.chain p X N).phi (Fz.step N) 1 3 j| ≤ softK CL * (Eminus a (-(CL.Zof p X N j)) * Mbal a (CL.Zof p X N j)) ∧
      |ψL j| ≤ |μ| * (CE * Ck') * (Eminus a (-(CL.Zof p X N j)) * Mbal a (CL.Zof p X N j)) ∧
      |ψL j - CL.psiHatL p X N j| ≤ |μ| * Ch * ((Eminus a (-(CL.Zof p X N j)))⁻¹ * Mbal a (CL.Zof p X N j)) ∧
      CL.psiHatL p X N j = μ * (cc * (CL.chain p X N).phi (Fz.step N) 0 3 j + sc * (CL.chain p X N).phi (Fz.step N) 1 3 j) := by
    intro j hj1 hj2 hZ hu1 hu2
    have hjNR : j ≤ (CL.chain p X N).NR := by omega
    have hu_c : CL.uc p - CL.η / 2 < uNode (Fz.step N) j := by linarith
    have hu_hi : uNode (Fz.step N) j ≤ CL.uc p + 2 * CL.η := by linarith
    have hj0' : 0 ≤ j := by omega
    have hjN : j ≤ N := row_le_N Fz N (by linarith)
    refine ⟨?_, ?_, ?_, ?_⟩
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
    · -- the exact right solution is recessive
      have hb := Hb p hp N hN hs0b X hX ψ' hJR hseedR j hj0' hjN (by linarith) hu2 hZ.le
      rw [hrel j (mem_Icc.mpr ⟨hj0', hjN⟩), abs_mul]
      have hEM : 0 ≤ Eminus a (-(CL.Zof p X N j)) * Mbal a (CL.Zof p X N j) := mul_nonneg (Eminus_pos _ _).le (Mbal_pos _ _).le
      calc |κ| * |ψ' ((N : ℤ) - j)| ≤ |κ| * (CE * (|CR.lamL p X N| / κb) * (Eminus a (-(CL.Zof p X N j)) * Mbal a (CL.Zof p X N j))) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = CE * (|κ| * |CR.lamL p X N|) / κb * (Eminus a (-(CL.Zof p X N j)) * Mbal a (CL.Zof p X N j)) := by ring
        _ ≤ CE * (Ck' * |CL.lamL p X N|) / κb * (Eminus a (-(CL.Zof p X N j)) * Mbal a (CL.Zof p X N j)) := by
            apply mul_le_mul_of_nonneg_right _ hEM
            apply div_le_div_of_nonneg_right _ hκ.le
            apply mul_le_mul_of_nonneg_left _ hCE
            exact hkap.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
        _ = |μ| * (CE * Ck') * (Eminus a (-(CL.Zof p X N j)) * Mbal a (CL.Zof p X N j)) := by rw [hμabs]; ring
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
        _ = |μ| * Ch * ((Eminus a (-(CL.Zof p X N j)))⁻¹ * Mbal a (CL.Zof p X N j)) := by
            rw [hμabs, hCh]; field_simp
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
        have e1 : cc = Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * a) := by rw [hccdef, ite_eq_left ha]
        have e2 : sc = Real.sin (Real.pi * a) := by rw [hscdef, ite_eq_left ha]
        rw [e1, e2, key, hμdef]; ring
      · obtain ⟨hr1, hr2⟩ := hrel2.2 (not_le.mp ha)
        have e1 : cc = 1 := by rw [hccdef, ite_eq_right ha]
        have e2 : sc = 0 := by rw [hscdef, ite_eq_right ha]
        rw [e1, e2, hr1, hμdef]; ring
  -- the two rows
  have hk0u1 : uNode (Fz.step N) (k0 + 1) < CL.uc p + CL.η / 2 := by linarith
  obtain ⟨g0, L0, E0, I0⟩ := rowfacts k0 (by omega) (by omega) hZ0 hlo (by linarith)
  obtain ⟨g1, L1, E1, I1⟩ := rowfacts (k0 + 1) (by omega) (by omega) hZ1 (by linarith) hk0u1
  -- margins for M_bal
  have hmar : ∀ j : ℤ, CL.η / 4 ≤ |uNode (Fz.step N) j - CL.uc p| → |uNode (Fz.step N) j - CL.uc p| ≤ 2 * CL.η →
      (CL.cz1 / 8) / Fz.step N ≤ |CL.Zof p X N j ^ 2 / 4 + a| := by
    intro j h1 h2
    rw [CL.Z2_add_a p X N j]
    have := CL.Zq_lb hp hX hhH1 h1 h2
    exact le_trans (div_le_div_of_nonneg_right this hh0.le) (le_abs_self _)
  have hMM := Mbal_prod_le a (CL.Zof p X N k0) a (CL.Zof p X N (k0 + 1)) (CL.cz1 / 8) (CL.cz1 / 8) (Fz.step N)
    (by positivity) (by positivity) hh0
    (hmar k0 (by rw [abs_of_pos (by linarith)]; linarith) (by rw [abs_of_pos (by linarith)]; linarith))
    (hmar (k0 + 1) (by rw [abs_of_pos (by linarith)]; linarith) (by rw [abs_of_pos (by linarith)]; linarith))
  -- the Casoratian lower bound for the swapped pair
  have hcas0 := hVpre.cas_lb_site (p := 3) (mem_Icc.mpr ⟨by norm_num, by rw [hP3']⟩) (j := k0)
    (mem_Icc.mpr ⟨by show (CL.chain p X N).jj 2 ≤ k0; omega, by show k0 ≤ (CL.chain p X N).jj 3; omega⟩)
  have hf3 : ((CL.chain p X N).rescale1 (softLam CL p X N)).phi (Fz.step N) 0 3 = (CL.chain p X N).phi (Fz.step N) 0 3 :=
    funext (fun k => LadderData.phi_rescale1_of_ne _ _ _ 0 (by norm_num) k)
  have hg3 : ((CL.chain p X N).rescale1 (softLam CL p X N)).phi (Fz.step N) 1 3 = (CL.chain p X N).phi (Fz.step N) 1 3 :=
    funext (fun k => LadderData.phi_rescale1_of_ne _ _ _ 1 (by norm_num) k)
  rw [hf3, hg3] at hcas0
  have hom : ((CL.chain p X N).rescale1 (softLam CL p X N)).ω 1 (Fz.step N) = Real.sqrt (Fz.step N) := by
    obtain ⟨-, -, -, -, -, hω, -, -, -⟩ := CL.patch1_eq p hp X hX N hN
    show (CL.chain p X N).ω 1 (Fz.step N) = _
    rw [hω]; exact CL.omega_sqrtW p hp X hX N hN
  rw [hom, abs_of_pos hs] at hcas0
  have hcas : CL.cs.cm * Real.sqrt (Fz.step N) ≤ |cas (CL.chain p X N).A ((CL.chain p X N).phi (Fz.step N) 0 3)
      ((CL.chain p X N).phi (Fz.step N) 1 3) k0| := hcas0
  have hA : |(CL.chain p X N).A k0| ≤ CL.CA := by
    have h1 := CL.A_bond p hp X hX N hN k0 (mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [h1, abs_of_nonneg (bondA_nonneg' Fz p N k0)]
    exact CL.bondA_le p hp N hN k0
  have hcomb := quant_combine (CL.chain p X N).A ((CL.chain p X N).phi (Fz.step N) 0 3) ((CL.chain p X N).phi (Fz.step N) 1 3)
    ψL (CL.psiHatL p X N) k0 μ cc sc CL.cs.cm (Real.sqrt (Fz.step N)) CL.CA (softK CL) Cm (CE * Ck') Ch wb
    (Eminus a (-(CL.Zof p X N k0))) (Eminus a (-(CL.Zof p X N (k0 + 1)))) (Mbal a (CL.Zof p X N k0)) (Mbal a (CL.Zof p X N (k0 + 1)))
    hμ hs I0 I1 hcas hA hCA0 hK0 (Eminus_pos _ _) (Eminus_pos _ _) hMono hRat hwb0 (mul_nonneg hCE hCk'0) hCh0
    (Mbal_pos _ _) (Mbal_pos _ _) hMM g0 g1 L0 L1 E0 E1
  -- smallness of `e_{k_0}^2`
  have he0sq : Eminus a (-(CL.Zof p X N k0)) ^ 2 ≤ Fexp * Fz.step N ^ m := by
    have h1 : Eminus a (-(CL.Zof p X N k0)) ^ 2 ≤ Real.exp (-(softCQ CL / Fz.step N)) ^ 2 :=
      pow_le_pow_left₀ (Eminus_pos _ _).le hsmall 2
    have h2 : Real.exp (-(softCQ CL / Fz.step N)) ^ 2 = Real.exp (-((2 * softCQ CL) / Fz.step N)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have h3 := exp_neg_div_le (2 * softCQ CL) (Fz.step N) (by positivity) hh0 m
    have h4 : Fz.step N ^ (m + 1) ≤ Fz.step N ^ m := pow_le_pow_of_le_one hh0.le hh1 (by omega)
    calc Eminus a (-(CL.Zof p X N k0)) ^ 2 ≤ _ := h1
      _ = _ := h2
      _ ≤ (Nat.factorial (m + 1) : ℝ) / (2 * softCQ CL) ^ (m + 1) * Fz.step N ^ (m + 1) := h3
      _ ≤ Fexp * Fz.step N ^ m := mul_le_mul_of_nonneg_left h4 hFexp0
  have hLm1 : 1 ≤ Lm (Fz.step N) := hLm _ hh0 hh1
  have hpm0 : 0 ≤ Fz.step N ^ m := pow_nonneg hh0.le m
  have hpm_le : Fz.step N ^ m ≤ Fz.step N ^ m * Lm (Fz.step N) := le_mul_of_one_le_right hpm0 hLm1
  have hccb : |cc| ≤ Cq0 * (Fz.step N ^ m * Lm (Fz.step N)) := by
    have h1 : |cc| * CL.cs.cm ≤ CL.CA * softK CL * Cm * (2 * (CE * Ck') * Fexp + |Cc| * CPC * (wb + 1)) * (Fz.step N ^ m * Lm (Fz.step N)) := by
      refine hcomb.trans ?_
      have hbr : 2 * (CE * Ck') * Eminus a (-(CL.Zof p X N k0)) ^ 2 + Ch * (wb + 1)
          ≤ (2 * (CE * Ck') * Fexp + |Cc| * CPC * (wb + 1)) * (Fz.step N ^ m * Lm (Fz.step N)) := by
        have hh1' : 2 * (CE * Ck') * Eminus a (-(CL.Zof p X N k0)) ^ 2 ≤ 2 * (CE * Ck') * Fexp * (Fz.step N ^ m * Lm (Fz.step N)) := by
          calc 2 * (CE * Ck') * Eminus a (-(CL.Zof p X N k0)) ^ 2 ≤ 2 * (CE * Ck') * (Fexp * Fz.step N ^ m) :=
                mul_le_mul_of_nonneg_left he0sq (by positivity)
            _ ≤ 2 * (CE * Ck') * (Fexp * (Fz.step N ^ m * Lm (Fz.step N))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpm_le hFexp0) (by positivity)
            _ = _ := by ring
        have hh2' : Ch * (wb + 1) = |Cc| * CPC * (wb + 1) * (Fz.step N ^ m * Lm (Fz.step N)) := by rw [hCh]; ring
        linarith
      have hpre : 0 ≤ CL.CA * softK CL * Cm := by positivity
      calc CL.CA * softK CL * Cm * (2 * (CE * Ck') * Eminus a (-(CL.Zof p X N k0)) ^ 2 + Ch * (wb + 1))
          ≤ CL.CA * softK CL * Cm * ((2 * (CE * Ck') * Fexp + |Cc| * CPC * (wb + 1)) * (Fz.step N ^ m * Lm (Fz.step N))) :=
            mul_le_mul_of_nonneg_left hbr hpre
        _ = _ := by ring
    have h2 : |cc| ≤ CL.CA * softK CL * Cm * (2 * (CE * Ck') * Fexp + |Cc| * CPC * (wb + 1)) * (Fz.step N ^ m * Lm (Fz.step N)) / CL.cs.cm := by
      rw [le_div_iff₀ hcm]; exact h1
    refine h2.trans (le_of_eq ?_)
    rw [hCq0]; field_simp
  have hTle : Fz.step N ^ m * Lm (Fz.step N) ≤ eps := by
    have h1 : Fz.step N ^ m ≤ Fz.step N := pow_le_of_le_one hh0.le hh1 (by omega)
    have h2 : Fz.step N * Lm (Fz.step N) ≤ eps := softHL_spec CL hepspos hh0 hsLe
    exact (mul_le_mul_of_nonneg_right h1 (by linarith)).trans h2
  have hapos : a ≤ 0 := by
    by_contra hcon
    have e1 : cc = 1 := by rw [hccdef, ite_eq_right hcon]
    rw [e1, abs_one] at hccb
    have h3 : Cq0 * (Fz.step N ^ m * Lm (Fz.step N)) ≤ Cq0 * eps := mul_le_mul_of_nonneg_left hTle hCq00
    have h4 : Cq0 * eps < 1 := by
      rw [heps, mul_one_div, div_lt_one (by positivity)]; linarith
    linarith
  refine ⟨hapos, ?_⟩
  have e1 : cc = Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * a) := by rw [hccdef, ite_eq_left hapos]
  rw [e1, abs_mul, abs_of_pos (Real.sqrt_pos.mpr (by positivity))] at hccb
  have hrr : Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    have : 2 / Real.pi * (Real.pi / 2) = 1 := by field_simp
    rw [this, Real.sqrt_one]
  have hcos : |Real.cos (Real.pi * a)| = Real.sqrt (Real.pi / 2) * (Real.sqrt (2 / Real.pi) * |Real.cos (Real.pi * a)|) := by
    rw [← mul_assoc, mul_comm (Real.sqrt (Real.pi / 2)), hrr, one_mul]
  rw [hcos]
  calc Real.sqrt (Real.pi / 2) * (Real.sqrt (2 / Real.pi) * |Real.cos (Real.pi * a)|)
      ≤ Real.sqrt (Real.pi / 2) * (Cq0 * (Fz.step N ^ m * Lm (Fz.step N))) :=
        mul_le_mul_of_nonneg_left hccb (Real.sqrt_nonneg _)
    _ = Cq0 * Real.sqrt (Real.pi / 2) * Fz.step N ^ m * Lm (Fz.step N) := by ring

end Quant


/-- `a <= 0` and `|cos(pi a)| <= eps` give a label `k >= 0` with `|a + (k + 1/2)| <= eps/2` (Jordan's inequality; the step from `soft_quant` to `a = -(k + 1/2) + O(h^m Lm)`). -/
lemma cos_label {a ε : ℝ} (ha : a ≤ 0) (h : |Real.cos (Real.pi * a)| ≤ ε) :
    ∃ k : ℕ, |a + ((k : ℝ) + 1 / 2)| ≤ ε / 2 := by
  set t : ℝ := -a with ht
  have ht0 : 0 ≤ t := by linarith
  refine ⟨⌊t⌋₊, ?_⟩
  set k : ℕ := ⌊t⌋₊ with hk
  have h1 : (k : ℝ) ≤ t := Nat.floor_le ht0
  have h2 : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
  set δ : ℝ := t - ((k : ℝ) + 1 / 2) with hδ
  have hδ1 : -(1 / 2) ≤ δ := by linarith
  have hδ2 : δ ≤ 1 / 2 := by linarith
  have hcos : Real.cos (Real.pi * a) = (-1) ^ k * (-Real.sin (Real.pi * δ)) := by
    have e0 : Real.cos (Real.pi * a) = Real.cos (Real.pi * t) := by
      rw [← Real.cos_neg]; congr 1; rw [ht]; ring
    have e : Real.pi * t = (Real.pi * δ + Real.pi / 2) + (k : ℝ) * Real.pi := by
      rw [hδ]; ring
    rw [e0, e, Real.cos_add_nat_mul_pi, Real.cos_add_pi_div_two]
  have habs : |Real.cos (Real.pi * a)| = |Real.sin (Real.pi * δ)| := by
    rw [hcos, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hsin : 2 * |δ| ≤ |Real.sin (Real.pi * δ)| := by
    have hd0 : 0 ≤ |δ| := abs_nonneg _
    have hd1 : |δ| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    have hs : 2 / Real.pi * (Real.pi * |δ|) ≤ Real.sin (Real.pi * |δ|) :=
      Real.mul_le_sin (by positivity) (by nlinarith [Real.pi_pos])
    have e : 2 / Real.pi * (Real.pi * |δ|) = 2 * |δ| := by field_simp
    rw [e] at hs
    have e2 : |Real.sin (Real.pi * δ)| = Real.sin (Real.pi * |δ|) := by
      rcases le_total 0 δ with hd | hd
      · rw [abs_of_nonneg hd]
        exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos]))
      · rw [abs_of_nonpos hd, ← abs_neg, ← Real.sin_neg]
        have e3 : -(Real.pi * δ) = Real.pi * (-δ) := by ring
        rw [e3]
        exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))
    rw [e2]; exact hs
  have : |a + ((k : ℝ) + 1 / 2)| = |δ| := by
    rw [hδ, ht]; rw [← abs_neg]; congr 1; ring
  rw [this]
  linarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_quant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_quant

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_right_recessive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_right_recessive

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_env_psi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_env_psi

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.cos_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cos_label

end FormalResearch.JacobiEigenvectors.TheoremA

end
