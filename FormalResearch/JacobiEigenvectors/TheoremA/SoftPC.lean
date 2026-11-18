module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftProof
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAbsorb

/-!
# Paper J, Layer 2 (L2.C6): the parabolic-cylinder bound of `prop:tha-W2` (1) in terms of `lambda_L M_Olv` (R1 + R2 + R3)

Source: Paper J `app_thmA.tex` "The soft edges: proof of Proposition prop:tha-W2", Steps 2--3 (the absorption of the connection term; `psi-hat_3 = psi-hat_2` through `M_-(a)`; the conversion
`lambda W M ~ lambda kappa_bal M_Olv(a,-Z)` by `eq:cha-MolvEquiv`, `eq:cha-envbar`).

## Proved here

* `soft_tail3` (**R2**): on the rows `j_2 < k <= N_R` of patch 3, `psi-hat_3(k) = psi-hat_2(k)` (the pair of patch 3 is `M_-(a) S` times the pair of patch 2, `pcSwap_eq_pcMinus`) and
  `|psi-hat_3(k) - lambda_L phi^{(1)}_{2,k}/kappa_bal| = |(M_1)_{21} phi^{(2)}_{2,k}| <= lambda Lambda E_-(Z_{j_1})^2 * 3 K E_swap M_bal`.
* `soft_pc_bound` (**R1 + R3**): there are `C_b, h_0` with, for every `k` with `u_c - eta/2 < u_k <= u_c + 2 eta`, `|psi_k - psi-hat^L_k| <= C_b h^m (lambda kappa_bal) M_Olv(a,-Z_k)` (before the lower bound
  `|lambda_L| >= c lambda kappa_bal`, which converts `lambda kappa_bal` into `|lambda_L|`).

## Differences from the paper

The absorption constant is `exp(-2 c_E/h) <= (m+1)!/(2 c_E)^{m+1} h^{m+1}` (`exp_neg_div_le`), not the paper's `e^{-c eta^2/h}`; `h^{-m} e^{-c/h}` is bounded either way.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Tail

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V)

/-- `Z_k > 0` on the rows `k > j_2`. -/
lemma Zof_pos_of_gt {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
    (hh : Fz.step N ≤ C.softH1) {lam : ℝ} (hV : ((C.chain p X N).rescale1 lam).PreValid C.cs (Fz.step N) m)
    {k : ℤ} (hk : k ∈ Finset.Icc ((C.chain p X N).jj 2 + 1) (C.chain p X N).NR) (hku : uNode (Fz.step N) k ≤ C.uc p + 2 * C.η) :
    0 < C.Zof p X N k := by
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hp hX hN hh hV
  obtain ⟨-, hη, hdm, hdmp, -⟩ := C.consts_pos
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hα := C.abs_alpha_le hX
  have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hk1 := (mem_Icc.mp hk).1
  have hmono : uNode (Fz.step N) ((C.chain p X N).jj 2 + 1) ≤ uNode (Fz.step N) k := SoftEdgeChart.uNode_mono_le hh0.le hk1
  have hx1lo : -(2 * C.η) ≤ uNode (Fz.step N) ((C.chain p X N).jj 2 + 1) - C.uc p := by
    have : uNode (Fz.step N) ((C.chain p X N).jj 1 + 1) ≤ uNode (Fz.step N) ((C.chain p X N).jj 2 + 1) :=
      SoftEdgeChart.uNode_mono_le hh0.le (by omega)
    have hhη : Fz.step N ≤ C.η / 2 := hh.trans C.softH1_le_eta
    linarith
  have hmvt := C.zeta_mvt (x1 := uNode (Fz.step N) ((C.chain p X N).jj 2 + 1) - C.uc p)
    (x2 := uNode (Fz.step N) k - C.uc p) hp hα hx1lo (by linarith) (by linarith)
  have hz : 0 < C.zeta p (Fz.bandHi p - X) (uNode (Fz.step N) k - C.uc p) := by
    have := mul_nonneg hdm.le (sub_nonneg.mpr (by linarith : uNode (Fz.step N) ((C.chain p X N).jj 2 + 1) - C.uc p ≤ uNode (Fz.step N) k - C.uc p))
    linarith [hmvt.1, hzb]
  rw [SoftEdgeChart.Zof_eq]
  exact div_pos hz hs

/-- **(R2) the tail of patch 3**: `|psi-hat_3(k) - lambda_L phi^{(1)}_{2,k}/kappa_bal| <= lambda Lambda E_-(Z_{j_1})^2 * 3 K E_swap(Z_k) M_bal(Z_k)` for `j_2 < k <= N_R`, `u_k <= u_c + 2 eta`. -/
theorem soft_tail3 {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N) (hh : Fz.step N ≤ C.softH1)
    {k : ℤ} (hk : k ∈ Finset.Icc ((C.chain p X N).jj 2 + 1) (C.chain p X N).NR) (hku : uNode (Fz.step N) k ≤ C.uc p + 2 * C.η) :
    |(C.chain p X N).psiHat (Fz.step N) 3 k - C.lamL p X N * ((C.chain p X N).phi (Fz.step N) 0 2 k / kappaBal (C.aOf p X N))|
      ≤ softLam C p X N * C.softLamC * Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)) ^ 2 *
          (3 * softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))) := by
  have hVpre : ((C.chain p X N).rescale1 (softLam C p X N)).PreValid C.cs (Fz.step N) m := C.valid p hp X hX N hN
  have hV : ((C.chain p X N).rescale1 (softLam C p X N)).Valid C.csT (Fz.step N) m := C.soft_valid hf hp hX hN hh hVpre
  obtain ⟨hP3, hj0, hj12, hj2NR, hx1, hx2, hx3, hza, hzb⟩ := C.soft_pos hp hX hN hh hVpre
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hlam : 0 < softLam C p X N := softLam_pos C p X N
  obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
  have hZk := Zof_pos_of_gt C hp hX hN hh hVpre hk hku
  have hP3' : ((C.chain p X N).rescale1 (softLam C p X N)).P = 3 := hP3
  have hphi2 : ∀ (α : Fin 2) (k : ℤ), ((C.chain p X N).rescale1 (softLam C p X N)).phi (Fz.step N) α 2 k = (C.chain p X N).phi (Fz.step N) α 2 k :=
    fun α k => LadderData.phi_rescale1_of_ne _ _ _ α (by norm_num) k
  have hphi3 : ∀ (α : Fin 2) (k : ℤ), ((C.chain p X N).rescale1 (softLam C p X N)).phi (Fz.step N) α 3 k = (C.chain p X N).phi (Fz.step N) α 3 k :=
    fun α k => LadderData.phi_rescale1_of_ne _ _ _ α (by norm_num) k
  -- the matrix relation at the rows j2, j2+1 and k
  have hr0 := C.phi_swap_rel hf hp hX hN (k := (C.chain p X N).jj 2) hj12.le le_rfl (by omega)
  have hr1 := C.phi_swap_rel hf hp hX hN (k := (C.chain p X N).jj 2 + 1) hj12.le (by omega) (by omega)
  have hrk := C.phi_swap_rel hf hp hX hN (k := k) hj12.le (by omega) (by omega)
  have hne := hV.det_ne_zero (p := 2) (mem_Icc.mpr ⟨by norm_num, by rw [hP3']; norm_num⟩) (j := (C.chain p X N).jj 2)
    (mem_Icc.mpr ⟨hj12.le, le_rfl⟩)
  rw [hphi2, hphi2, hphi2, hphi2] at hne
  -- the transfer matrix entry
  have hAne : (C.chain p X N).A (C.j1 p X N) ≠ 0 :=
    hV.A_ne_zero (p := 2) (mem_Icc.mpr ⟨by norm_num, by rw [hP3']; norm_num⟩) (j := C.j1 p X N) (mem_Icc.mpr ⟨le_rfl, hj12.le⟩)
  have hlamL := lamL_eq_kappa_mul_transMat C p X N hAne
  have hκ := kappaBal_pos (C.aOf p X N)
  obtain ⟨-, -, -, -, t10⟩ := hV.transfer 1 le_rfl (by rw [hP3']; norm_num)
  obtain ⟨r00, r10, -, -⟩ := LadderData.transMat_rescale1_one (C.chain p X N) (softLam C p X N) (Fz.step N)
  have hM10 : transMat ((C.chain p X N).phi (Fz.step N) 0) ((C.chain p X N).phi (Fz.step N) 1) (C.chain p X N).jj 1 1 0
      = softLam C p X N * transMat (((C.chain p X N).rescale1 (softLam C p X N)).phi (Fz.step N) 0)
          (((C.chain p X N).rescale1 (softLam C p X N)).phi (Fz.step N) 1) (C.chain p X N).jj 1 1 0 := by
    rw [r10]; field_simp
  have t10' : |transMat (((C.chain p X N).rescale1 (softLam C p X N)).phi (Fz.step N) 0)
      (((C.chain p X N).rescale1 (softLam C p X N)).phi (Fz.step N) 1) (C.chain p X N).jj 1 1 0|
        ≤ C.softLamC * (C.chain p X N).W ((C.chain p X N).jj 1) ^ 2 := t10
  have hWj1 : (C.chain p X N).W ((C.chain p X N).jj 1) = Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)) :=
    chain_W_j1 C hp hX hN hj0
  -- psi-hat_3 = psi-hat_2 = M11 phi1 + M21 phi2
  have hpsi : (C.chain p X N).psiHat (Fz.step N) 3 k = (C.chain p X N).psiHat (Fz.step N) 2 k := by
    by_cases hale : C.aOf p X N ≤ 0
    · obtain ⟨hr0a, hr0b⟩ := hr0.1 hale
      obtain ⟨hr1a, hr1b⟩ := hr1.1 hale
      obtain ⟨hka, hkb⟩ := hrk.1 hale
      have hsq1 : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
        rw [← Real.sqrt_mul (by positivity)]
        have : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
        rw [this, Real.sqrt_one]
      have hs1 := Real.sin_sq_add_cos_sq (Real.pi * C.aOf p X N)
      have hdet : Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * C.aOf p X N) * (Real.sqrt (2 / Real.pi) * Real.cos (Real.pi * C.aOf p X N))
          - Real.sin (Real.pi * C.aOf p X N) * (-Real.sin (Real.pi * C.aOf p X N)) = 1 := by
        linear_combination (Real.cos (Real.pi * C.aOf p X N) ^ 2) * hsq1 + hs1
      exact LadderData.psiHat_three_of_linear ((C.chain p X N).phi (Fz.step N) 0) ((C.chain p X N).phi (Fz.step N) 1)
        (C.chain p X N).jj _ _ _ _ hdet hr0a hr1a hr0b hr1b hne k hka hkb
    · have hapos : 0 < C.aOf p X N := not_le.mp hale
      obtain ⟨hr0a, hr0b⟩ := hr0.2 hapos
      obtain ⟨hr1a, hr1b⟩ := hr1.2 hapos
      obtain ⟨hka, hkb⟩ := hrk.2 hapos
      exact LadderData.psiHat_three_of_linear ((C.chain p X N).phi (Fz.step N) 0) ((C.chain p X N).phi (Fz.step N) 1)
        (C.chain p X N).jj 1 0 0 1 (by norm_num)
        (by rw [hr0a]; ring) (by rw [hr1a]; ring) (by rw [hr0b]; ring) (by rw [hr1b]; ring) hne k
        (by rw [hka]; ring) (by rw [hkb]; ring)
  have hpsi2 := LadderData.psiHat_two (C.chain p X N) (Fz.step N) k
  -- the difference is M21 phi2
  have hdiff : (C.chain p X N).psiHat (Fz.step N) 3 k - C.lamL p X N * ((C.chain p X N).phi (Fz.step N) 0 2 k / kappaBal (C.aOf p X N))
      = transMat ((C.chain p X N).phi (Fz.step N) 0) ((C.chain p X N).phi (Fz.step N) 1) (C.chain p X N).jj 1 1 0 *
          (C.chain p X N).phi (Fz.step N) 1 2 k := by
    rw [hpsi, hpsi2, hlamL]
    field_simp
    ring
  -- bound on phi2^{(2)}(k)
  have hp3 : 3 ∈ Finset.Icc 1 ((C.chain p X N).rescale1 (softLam C p X N)).P := mem_Icc.mpr ⟨by norm_num, by rw [hP3']⟩
  have hkwin : k ∈ Finset.Icc (((C.chain p X N).rescale1 (softLam C p X N)).jj (3 - 1))
      (((C.chain p X N).rescale1 (softLam C p X N)).jj 3 + 1) := by
    have hjl : (C.chain p X N).jj 3 = (C.chain p X N).NR - 1 := by
      have := hV.jj_last
      change (C.chain p X N).jj (C.chain p X N).P = (C.chain p X N).NR - 1 at this
      rw [hP3] at this; exact this
    exact mem_Icc.mpr ⟨by show (C.chain p X N).jj 2 ≤ k; omega, by show k ≤ (C.chain p X N).jj 3 + 1; omega⟩
  obtain ⟨hb0, hb1⟩ := hV.phi_bd hp3 hkwin
  rw [hphi3] at hb0 hb1
  have hWk : (C.chain p X N).W k = Eswap (C.aOf p X N) (C.Zof p X N k) := C.W3_def p hp X hX N hN k hk
  have hMk : (C.chain p X N).M k = Mbal (C.aOf p X N) (C.Zof p X N k) :=
    C.M2_def p hp X hX N hN k (mem_Icc.mpr ⟨by omega, hk2⟩)
  have hEsw1 := Eswap_ge_one (C.aOf p X N) hZk.le
  have hMpos := Mbal_pos (C.aOf p X N) (C.Zof p X N k)
  have hK0 : 0 ≤ softK C := softK_nonneg C
  have hWr : ((C.chain p X N).rescale1 (softLam C p X N)).W k = (C.chain p X N).W k := rfl
  have hMr : ((C.chain p X N).rescale1 (softLam C p X N)).M k = (C.chain p X N).M k := rfl
  rw [hWr, hMr, hWk, hMk] at hb0 hb1
  have hb0' : |(C.chain p X N).phi (Fz.step N) 0 3 k| ≤ softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k)) := by
    have e : (C.csT.KA + C.csT.KB) * C.csT.Kw = softK C := rfl
    rw [e] at hb0
    linarith [hb0]
  have hb1' : |(C.chain p X N).phi (Fz.step N) 1 3 k| ≤ softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k)) := by
    have e : (C.csT.KA + C.csT.KB) * C.csT.Kw = softK C := rfl
    rw [e] at hb1
    have hinv : (Eswap (C.aOf p X N) (C.Zof p X N k))⁻¹ ≤ Eswap (C.aOf p X N) (C.Zof p X N k) :=
      le_trans (inv_le_one_of_one_le₀ hEsw1) hEsw1
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hK0) hMpos.le
    calc _ ≤ _ := hb1
      _ ≤ _ := this
      _ = _ := by ring
  have hphi2bd : |(C.chain p X N).phi (Fz.step N) 1 2 k| ≤
      3 * softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k)) := by
    by_cases hale : C.aOf p X N ≤ 0
    · obtain ⟨hka, hkb⟩ := hrk.1 hale
      -- phi2^{(2)} = a phi3^{(2)} - b phi3^{(1)}
      have hsq1 : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
        rw [← Real.sqrt_mul (by positivity)]
        have : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
        rw [this, Real.sqrt_one]
      have hs1 := Real.sin_sq_add_cos_sq (Real.pi * C.aOf p X N)
      have hinv : (C.chain p X N).phi (Fz.step N) 1 2 k =
          Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * C.aOf p X N) * (C.chain p X N).phi (Fz.step N) 1 3 k
            - Real.sin (Real.pi * C.aOf p X N) * (C.chain p X N).phi (Fz.step N) 0 3 k := by
        rw [hka, hkb]
        linear_combination (-((C.chain p X N).phi (Fz.step N) 1 2 k) * (Real.cos (Real.pi * C.aOf p X N)) ^ 2) * hsq1
          - ((C.chain p X N).phi (Fz.step N) 1 2 k) * hs1
      have hsqa : Real.sqrt (Real.pi / 2) ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]
        linarith [Real.pi_le_four]
      have hcos := Real.abs_cos_le_one (Real.pi * C.aOf p X N)
      have hsin := Real.abs_sin_le_one (Real.pi * C.aOf p X N)
      have hE : 0 ≤ softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k)) :=
        mul_nonneg hK0 (mul_nonneg (Eswap_pos _ _).le hMpos.le)
      rw [hinv]
      have h1 : |Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * C.aOf p X N) * (C.chain p X N).phi (Fz.step N) 1 3 k|
          ≤ 2 * (softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        calc _ ≤ 2 * 1 * (softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))) :=
              mul_le_mul (mul_le_mul hsqa hcos (abs_nonneg _) (by norm_num)) hb1' (abs_nonneg _) (by norm_num)
          _ = _ := by ring
      have h2 : |Real.sin (Real.pi * C.aOf p X N) * (C.chain p X N).phi (Fz.step N) 0 3 k|
          ≤ 1 * (softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))) := by
        rw [abs_mul]
        exact mul_le_mul hsin hb0' (abs_nonneg _) (by norm_num)
      calc _ ≤ |Real.sqrt (Real.pi / 2) * Real.cos (Real.pi * C.aOf p X N) * (C.chain p X N).phi (Fz.step N) 1 3 k|
            + |Real.sin (Real.pi * C.aOf p X N) * (C.chain p X N).phi (Fz.step N) 0 3 k| := abs_sub _ _
        _ ≤ 2 * (softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k)))
            + 1 * (softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))) := add_le_add h1 h2
        _ = _ := by ring
    · have hapos : 0 < C.aOf p X N := not_le.mp hale
      obtain ⟨hka, hkb⟩ := hrk.2 hapos
      rw [← hkb]
      calc _ ≤ softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k)) := hb1'
        _ ≤ 3 * softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k)) := by
          have : 0 ≤ softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k)) :=
            mul_nonneg hK0 (mul_nonneg (Eswap_pos _ _).le hMpos.le)
          linarith
  -- assemble
  rw [hdiff, abs_mul]
  have hM10b : |transMat ((C.chain p X N).phi (Fz.step N) 0) ((C.chain p X N).phi (Fz.step N) 1) (C.chain p X N).jj 1 1 0|
      ≤ softLam C p X N * (C.softLamC * Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)) ^ 2) := by
    rw [hM10, abs_mul, abs_of_pos hlam]
    refine mul_le_mul_of_nonneg_left ?_ hlam.le
    rw [hWj1] at t10'
    exact t10'
  calc _ ≤ (softLam C p X N * (C.softLamC * Eminus (C.aOf p X N) (C.Zof p X N (C.j1 p X N)) ^ 2)) *
        (3 * softK C * (Eswap (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))) :=
        mul_le_mul hM10b hphi2bd (abs_nonneg _) (by have := C.softLamC_ge; positivity)
    _ = _ := by ring

end Tail

end FormalResearch.JacobiEigenvectors.TheoremA

end
