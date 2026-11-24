module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly3

/-!
# Soft-edge assembly, part D: envelopes of `psi-hat`, the row-wise comparison and the eigen-system clauses of `PropThaW2` (2)

Source: app_thmA, proof of prop:tha-W2, Step 4 (c)-(e).

Proved here (all axiom-pinned):
* `psiHatL_envW` (F-W2-16): `|psi-hat^L_k| <= K E_Web M_Web` on the Weber rows (`phi_bd` of `chainW`, `W_defW`, `M_defW`).
* `left_pw`: for one chart, on the Weber rows and the left PC rows: the error of the exact solution and the envelope of `psi-hat`, both with the constants of `PropThaW2` (1); `LeftFacts` packages it.
* `soft_row`: the four-branch row comparison `|psi^L_n - hat Psi_n numerator| <= C eps V_n`, `|numerator| <= C V_n` (mirror transport of the right branches, `right_alg`).
* `vec_err_core`, `soft_vec_err`: `|psi^L_n/||psi^L|| - hat Psi_n| <= C h^m Lm V_n/hat N` (`normalised_error`, with `soft_env_sum` and the normalisation lower bound).
* `soft_eigen_main`: at an eigenvalue satisfying the Step-0 premise, `|Psi_n - hat Psi_n| <= Cc h^m Lm softEnv_n` on every row and `sum softEnv^2 <= Cc` (exact solutions from `exists_seeded`,
  `psiL_eq_kappa_psiR`, `bondA_pos_all`, `aOf_le_of_step0`, the seed `seed_posW`).  These are the first two conjuncts of the eigen-system clause of `PropThaW2` (2).

Differences from the paper: `ParabolicCylinderFacts` is a hypothesis (as in `propThaW2_item1`); the constants are not explicit.

Not formalised: the off-window relative clause (R2), the counting and labels (E9), the assembly of `PropThaW2`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section WeberEnv

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- **F-W2-16: the Weber envelope of `psi-hat^L`.**  On the Weber rows `u_k <= u_c - eta/2`: `|psi-hat^L_k| <= K E_Web M_Web` (`phi_bd` of `chainW` on its single patch, `W_defW`, `M_defW`). -/
lemma psiHatL_envW {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N)
    {k : ℤ} (hk0 : 0 ≤ k) (hku : uNode (Fz.step N) k ≤ C.uc μ - C.η / 2) :
    |C.psiHatL μ X N k| ≤ softK C * softEnvWeb C μ X N k := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hVW := C.validW μ hμ X hX N hN
  obtain ⟨hP1, hs0, hNR0, hNRu, hNRv⟩ := C.shapeW μ hμ X hX N hN
  set DW := C.chainW μ X N with hDW
  have hkW : k ≤ DW.NR := by
    by_contra hcon
    have := SoftEdgeChart.uNode_mono_le hh0.le (show DW.NR + 1 ≤ k by omega)
    linarith
  have hkw : k ∈ Icc (DW.jj (1 - 1)) (DW.jj 1 + 1) := by
    have hl : DW.jj DW.P = DW.NR - 1 := hVW.jj_last
    rw [hP1] at hl
    have hz : DW.jj 0 = 0 := hVW.jj0
    simp only [Nat.sub_self, hz]
    exact mem_Icc.mpr ⟨hk0, by omega⟩
  have hpb := hVW.toPreValid.phi_bd (p := 1) (mem_Icc.mpr ⟨le_rfl, by show 1 ≤ DW.P; omega⟩) (j := k) hkw
  have hkk : k ∈ Finset.Icc (0 : ℤ) DW.NR := mem_Icc.mpr ⟨hk0, hkW⟩
  have hW := C.W_defW μ hμ X hX N hN k hkk
  have hM := C.M_defW μ hμ X hX N hN k hkk
  rw [psiHatL_of_le C μ X N hku]
  have h1 := hpb.1
  refine h1.trans (le_of_eq ?_)
  rw [hW, hM]
  unfold softK softEnvWeb
  ring

end WeberEnv

section LeftPW

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- a row with `u_k <= u_c + 2 eta` is at most `N_R` (the chain covers it). -/
lemma row_le_chainNR {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N) {k : ℤ}
    (hk : uNode (Fz.step N) k ≤ C.uc μ + 2 * C.η) : k ≤ (C.chain μ X N).NR := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  obtain ⟨-, -, -, -, -, -, hNRu, hNRv⟩ := C.shape μ hμ X hX N hN
  by_contra h2
  have := SoftEdgeChart.uNode_mono_le hh0.le (show (C.chain μ X N).NR + 1 ≤ k by omega)
  linarith

/-- `x_k <= -eta/4` forces `Z_k <= 0` (`zeta_sign_out`). -/
lemma Zof_nonpos_of_near {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ C.δ0) {N : ℕ} {k : ℤ} (hk : k ∈ rowsOf N)
    (hx : uNode (Fz.step N) k - C.uc μ ≤ -(C.η / 4)) : C.Zof μ X N k ≤ 0 := by
  have hα := C.abs_alpha_le hX
  have hη := C.consts_pos.2.1
  obtain ⟨hk0, hkL⟩ := uNode_row_mem (Fz := Fz) hk
  have hxabs : C.η / 4 ≤ |uNode (Fz.step N) k - C.uc μ| := by
    rw [abs_of_neg (by linarith)]; linarith
  have h := (C.zeta_sign_out μ hμ _ hα _ hxabs (by linarith) (by linarith)).1 (by linarith)
  unfold SoftEdgeCore.Zof
  exact div_nonpos_of_nonpos_of_nonneg h (Real.sqrt_nonneg _)

/-- **the left pointwise facts of one chart**: error of the exact solution and envelope of `psi-hat` on the Weber rows and on the left PC rows. -/
theorem left_pw {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) :
    ∃ Cc Kenv h0 : ℝ, 0 < h0 ∧ 0 ≤ Cc ∧ 0 ≤ Kenv ∧ ∀ p ∈ P, ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ C.δ0 →
      ∀ ψ : ℤ → ℝ, JacSol Fz p N X (C.chain p X N).NR ψ → ψ 0 = C.psiHatL p X N 0 → ∀ k ∈ rowsOf N,
        (uNode (Fz.step N) k ≤ C.uc p - C.η / 2 →
          |ψ k - C.psiHatL p X N k| ≤ Cc * (Fz.step N ^ m * Lm (Fz.step N)) * softEnvWeb C p X N k ∧
          |C.psiHatL p X N k| ≤ Kenv * softEnvWeb C p X N k) ∧
        (C.uc p - C.η / 2 < uNode (Fz.step N) k → C.Zof p X N k ≤ 0 →
          |ψ k - C.psiHatL p X N k| ≤ Cc * (Fz.step N ^ m * Lm (Fz.step N)) * (|C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) ∧
          |C.psiHatL p X N k| ≤ Kenv * (|C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k)))) := by
  obtain ⟨Cc, h0, clam, Clam, h0p, hclam, H⟩ := propThaW2_item1 C hf hm hLm
  have hK0 := softK_nonneg C
  have hcP := hf.cPC_pos
  refine ⟨|Cc|, softK C + softK C / cPC, min h0 C.softH2, lt_min h0p C.softH2_pos, abs_nonneg _, by positivity, ?_⟩
  intro p hp N hN hstep X hX ψ hJ hseed k hk
  have hs0 : Fz.step N ≤ h0 := hstep.trans (min_le_left _ _)
  have hs2 : Fz.step N ≤ C.softH2 := hstep.trans (min_le_right _ _)
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := hs2.trans (C.softH2_le_H1.trans C.softH1_le_one)
  have hp0 : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) := powLm_nonneg C hh0 hh1
  obtain ⟨hmain, -, -⟩ := H p hp N hN hs0 X hX
  obtain ⟨hWb, hPC⟩ := hmain ψ hJ hseed
  have hk' := mem_Icc.mp hk
  have hη := C.consts_pos.2.1
  constructor
  · intro hku
    have hkNR := row_le_chainNR C hp hX hN (k := k) (by linarith)
    have h1 := hWb k (mem_Icc.mpr ⟨hk'.1, hkNR⟩) hku
    have hE := softEnvWeb_nonneg C p X N k
    refine ⟨?_, ?_⟩
    · refine h1.trans ?_
      calc Cc * Fz.step N ^ m * Lm (Fz.step N) * softEnvWeb C p X N k = Cc * (Fz.step N ^ m * Lm (Fz.step N)) * softEnvWeb C p X N k := by ring
        _ ≤ |Cc| * (Fz.step N ^ m * Lm (Fz.step N)) * softEnvWeb C p X N k :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hp0) hE
    · refine (psiHatL_envW C hp hX hN hk'.1 hku).trans ?_
      exact mul_le_mul_of_nonneg_right (by have : 0 ≤ softK C / cPC := by positivity
                                           linarith) hE
  · intro hku hZ
    have hu4 := lt_of_Zof_nonpos C hp hX hk hZ
    have hkNR := row_le_chainNR C hp hX hN (k := k) (by linarith)
    have hku2 : uNode (Fz.step N) k ≤ C.uc p + 2 * C.η := by linarith
    have h1 := hPC k (mem_Icc.mpr ⟨hk'.1, hkNR⟩) hku hku2
    have hmol0 := molv_nonneg hf (C.aOf p X N) (-(C.Zof p X N k))
    refine ⟨?_, ?_⟩
    · refine h1.trans ?_
      calc Cc * Fz.step N ^ m * Lm (Fz.step N) * |C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k))
          = Cc * (Fz.step N ^ m * Lm (Fz.step N)) * (|C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) := by ring
        _ ≤ |Cc| * (Fz.step N ^ m * Lm (Fz.step N)) * (|C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hp0) (mul_nonneg (abs_nonneg _) hmol0)
    · have he := psiHatL_env2 C hp hX hN hs2 hk'.1 hku (by linarith) hZ
      have hml := molv_lower hf (C.aOf p X N) (-(C.Zof p X N k))
      rw [Wmol_neg_of_nonpos _ hZ, Mbal_neg] at hml
      have hκ := kappaBal_pos (C.aOf p X N)
      have hEM : cPC * (kappaBal (C.aOf p X N))⁻¹ * Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k) ≤
          Molv U V (C.aOf p X N) (-(C.Zof p X N k)) := hml
      have hEM' : (kappaBal (C.aOf p X N))⁻¹ * (Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k)) ≤
          Molv U V (C.aOf p X N) (-(C.Zof p X N k)) / cPC := by
        rw [le_div_iff₀ hcP]; nlinarith [hEM]
      refine he.trans ?_
      have hl0 := abs_nonneg (C.lamL p X N)
      calc softK C * (|C.lamL p X N| / kappaBal (C.aOf p X N)) * (Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))
          = softK C * |C.lamL p X N| * ((kappaBal (C.aOf p X N))⁻¹ * (Eminus (C.aOf p X N) (C.Zof p X N k) * Mbal (C.aOf p X N) (C.Zof p X N k))) := by
            rw [div_eq_mul_inv]; ring
        _ ≤ softK C * |C.lamL p X N| * (Molv U V (C.aOf p X N) (-(C.Zof p X N k)) / cPC) :=
            mul_le_mul_of_nonneg_left hEM' (mul_nonneg hK0 hl0)
        _ = (softK C / cPC) * (|C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) := by ring
        _ ≤ (softK C + softK C / cPC) * (|C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hl0 hmol0)

end LeftPW

section RowErr

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}

/-- the left facts of one chart (`left_pw` conclusion). -/
def LeftFacts {F : SymbolFamily (Par × ℝ)} (C : SoftEdgeChart F P m q U V Lm) (p : Par × ℝ) (X : ℝ) (N : ℕ) (ψ : ℤ → ℝ) (Cc Kenv : ℝ) : Prop :=
  ∀ k ∈ rowsOf N,
    (uNode (F.step N) k ≤ C.uc p - C.η / 2 →
      |ψ k - C.psiHatL p X N k| ≤ Cc * (F.step N ^ m * Lm (F.step N)) * softEnvWeb C p X N k ∧
      |C.psiHatL p X N k| ≤ Kenv * softEnvWeb C p X N k) ∧
    (C.uc p - C.η / 2 < uNode (F.step N) k → C.Zof p X N k ≤ 0 →
      |ψ k - C.psiHatL p X N k| ≤ Cc * (F.step N ^ m * Lm (F.step N)) * (|C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k))) ∧
      |C.psiHatL p X N k| ≤ Kenv * (|C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N k))))

/-- the numerator of `softVec`. -/
def softNum (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm) (p : Par × ℝ) (X : ℝ) (N : ℕ) (n : ℤ) : ℝ :=
  if CL.Zof p X N n ≤ 0 then CL.psiHatL p X N n else softKappa CL CR p X N * softSeqR CR p X N n

lemma right_alg (κ κh ψ ψh A ε Cc Ke Dk : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε) (hCc : 0 ≤ Cc) (hKe : 0 ≤ Ke) (hDk : 0 ≤ Dk)
    (hsm : Dk * ε ≤ 1 / 2) (hk : |κh - κ| ≤ Dk * ε * |κ|) (he : |ψ - ψh| ≤ Cc * ε * A) (hb : |ψh| ≤ Ke * A) :
    |κ * ψ - κh * ψh| ≤ (2 * Cc + 2 * Dk * Ke) * ε * (|κh| * A) := by
  have h1 : |κ| ≤ 2 * |κh| := by
    have := abs_sub_abs_le_abs_sub κ κh
    rw [abs_sub_comm] at this
    have h2 : Dk * ε * |κ| ≤ (1 / 2) * |κ| := mul_le_mul_of_nonneg_right hsm (abs_nonneg _)
    linarith [abs_nonneg κ]
  have e : κ * ψ - κh * ψh = κ * (ψ - ψh) + (κ - κh) * ψh := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have t1 : |κ| * |ψ - ψh| ≤ (2 * |κh|) * (Cc * ε * A) :=
    mul_le_mul h1 he (abs_nonneg _) (by positivity)
  have t2 : |κ - κh| * |ψh| ≤ (Dk * ε * |κ|) * (Ke * A) := by
    rw [abs_sub_comm]; exact mul_le_mul hk hb (abs_nonneg _) (by positivity)
  have t3 : (Dk * ε * |κ|) * (Ke * A) ≤ (Dk * ε * (2 * |κh|)) * (Ke * A) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
  nlinarith [t1, t2, t3]

lemma softEnvNum_nonneg {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V Lm)
    (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm) (p : Par × ℝ) (X : ℝ) (N : ℕ) (n : ℤ) :
    0 ≤ softEnvNum CL CR p X N n := by
  unfold softEnvNum
  split_ifs
  · exact softEnvWeb_nonneg _ _ _ _ _
  · exact mul_nonneg (abs_nonneg _) (molv_nonneg hf _ _)
  · exact mul_nonneg (abs_nonneg _) (molv_nonneg hf _ _)
  · exact mul_nonneg (abs_nonneg _) (softEnvWeb_nonneg _ _ _ _ _)

end RowErr

section Row

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- **the per-row comparison** `|psi^L_n - hat Psi_n numerator| <= C eps V_n`, `|hat Psi_n numerator| <= C V_n`, in the four branches of `softEnv`. -/
theorem soft_row (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (ψL ψ' : ℤ → ℝ) (κ : ℝ) (CcL KeL CcR KeR Dk ε Cerr Cenv : ℝ)
    (hrel : ∀ n ∈ rowsOf N, ψL n = κ * ψ' ((N : ℤ) - n))
    (FL : LeftFacts CL p X N ψL CcL KeL) (FR : LeftFacts CR p X N ψ' CcR KeR)
    (hCcL : 0 ≤ CcL) (hKeL : 0 ≤ KeL) (hCcR : 0 ≤ CcR) (hKeR : 0 ≤ KeR) (hDk : 0 ≤ Dk) (hε : 0 ≤ ε)
    (hsm : Dk * ε ≤ 1 / 2) (hk : |softKappa CL CR p X N - κ| ≤ Dk * ε * |κ|)
    (hC1 : CcL ≤ Cerr) (hC2 : 2 * CcR + 2 * Dk * KeR ≤ Cerr) (hE1 : KeL ≤ Cenv) (hE2 : KeR ≤ Cenv)
    (hεe : ε = Fz.step N ^ m * Lm (Fz.step N)) {n : ℤ} (hn : n ∈ rowsOf N) :
    |ψL n - softNum CL CR p X N n| ≤ Cerr * ε * softEnvNum CL CR p X N n ∧ |softNum CL CR p X N n| ≤ Cenv * softEnvNum CL CR p X N n := by
  have hV0 := softEnvNum_nonneg hf CL CR p X N n
  have hη := CL.consts_pos.2.1
  have hε' : ε = Fz.step N ^ m * Lm (Fz.step N) := hεe
  unfold softNum softEnvNum
  by_cases hZ : CL.Zof p X N n ≤ 0
  · rw [if_pos hZ]
    by_cases b1 : uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2
    · rw [if_pos b1]
      obtain ⟨h1, h2⟩ := (FL n hn).1 b1
      have hE := softEnvWeb_nonneg CL p X N n
      refine ⟨?_, ?_⟩
      · rw [← hε'] at h1
        refine h1.trans ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hε) hE
      · exact h2.trans (mul_le_mul_of_nonneg_right hE1 hE)
    · rw [if_neg b1, if_pos hZ]
      obtain ⟨h1, h2⟩ := (FL n hn).2 (not_le.mp b1) hZ
      have hmo := molv_nonneg hf (CL.aOf p X N) (-(CL.Zof p X N n))
      have hA : 0 ≤ |CL.lamL p X N| * Molv U V (CL.aOf p X N) (-(CL.Zof p X N n)) := mul_nonneg (abs_nonneg _) hmo
      refine ⟨?_, ?_⟩
      · rw [← hε'] at h1
        refine h1.trans ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hε) hA
      · exact h2.trans (mul_le_mul_of_nonneg_right hE1 hA)
  · rw [if_neg hZ]
    push_neg at hZ
    have hn' := mem_Icc.mp hn
    have hnear : CL.uc p - CL.η / 4 < uNode (Fz.step N) n := by
      by_contra h
      have := Zof_nonpos_of_near CL hp hX hn (by linarith [not_lt.mp h])
      linarith
    have b1 : ¬ uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2 := by intro h; linarith
    rw [if_neg b1, if_neg (not_le.mpr hZ)]
    -- the mirror row
    have hstepR : (mirrorFamily Fz).step N = Fz.step N := rfl
    have hL := step_mul_succ Fz N
    have hrefl : uNode (Fz.step N) ((N : ℤ) - n) = Fz.L - uNode (Fz.step N) n := uNode_mirror Fz.L (Fz.step N) N n hL
    have huc : CR.uc p = Fz.L - CL.uc p := hM.1 p hp
    have hηe : CR.η = CL.η := hM.2.2.2.1
    have hkR : (N : ℤ) - n ∈ rowsOf N := by
      simp only [rowsOf, Finset.mem_Icc] at hn ⊢; omega
    have hZR : CR.Zof p X N ((N : ℤ) - n) = -CL.Zof p X N n := Zof_mirror hM hp X N n
    have haR : CR.aOf p X N = CL.aOf p X N := aOf_mirror hM hp X N
    have hψ : ψL n = κ * ψ' ((N : ℤ) - n) := hrel n hn
    have hsr : softSeqR CR p X N n = CR.psiHatL p X N ((N : ℤ) - n) := rfl
    rw [hsr, hψ]
    have hamp : (0 : ℝ) ≤ 2 * CcR + 2 * Dk * KeR := by positivity
    by_cases b3 : uNode (Fz.step N) n < CL.uc p + CL.η / 2
    · rw [if_pos b3]
      have hc1 : CR.uc p - CR.η / 2 < uNode (Fz.step N) ((N : ℤ) - n) := by
        rw [hrefl, huc, hηe]; linarith
      have hc2 : CR.Zof p X N ((N : ℤ) - n) ≤ 0 := by rw [hZR]; linarith
      obtain ⟨h1, h2⟩ := (FR ((N : ℤ) - n) hkR).2 (by rw [hstepR]; exact hc1) hc2
      rw [haR, hZR, neg_neg] at h1 h2
      have hmo := molv_nonneg hf (CL.aOf p X N) (CL.Zof p X N n)
      have hA : 0 ≤ |CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n) := mul_nonneg (abs_nonneg _) hmo
      have h1' : |ψ' ((N : ℤ) - n) - CR.psiHatL p X N ((N : ℤ) - n)| ≤ CcR * ε * (|CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n)) := by
        rw [hε']; exact h1
      have key := right_alg κ (softKappa CL CR p X N) _ _ _ ε CcR KeR Dk hA hε hCcR hKeR hDk hsm hk h1' h2
      have eV : |softKappa CL CR p X N * CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n) =
          |softKappa CL CR p X N| * (|CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n)) := by rw [abs_mul]; ring
      rw [eV]
      refine ⟨key.trans ?_, ?_⟩
      · have : 0 ≤ ε * (|softKappa CL CR p X N| * (|CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n))) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right (by linarith : 2 * CcR + 2 * Dk * KeR ≤ Cerr) this]
      · rw [abs_mul]
        calc |softKappa CL CR p X N| * |CR.psiHatL p X N ((N : ℤ) - n)| ≤ |softKappa CL CR p X N| * (KeR * (|CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n))) :=
              mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          _ ≤ |softKappa CL CR p X N| * (Cenv * (|CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE2 hA) (abs_nonneg _)
          _ = _ := by ring
    · rw [if_neg b3]
      have hc1 : uNode (Fz.step N) ((N : ℤ) - n) ≤ CR.uc p - CR.η / 2 := by
        rw [hrefl, huc, hηe]; linarith [not_lt.mp b3]
      obtain ⟨h1, h2⟩ := (FR ((N : ℤ) - n) hkR).1 (by rw [hstepR]; exact hc1)
      have hE := softEnvWeb_nonneg CR p X N ((N : ℤ) - n)
      have h1' : |ψ' ((N : ℤ) - n) - CR.psiHatL p X N ((N : ℤ) - n)| ≤ CcR * ε * softEnvWeb CR p X N ((N : ℤ) - n) := by
        rw [hε']; exact h1
      have key := right_alg κ (softKappa CL CR p X N) _ _ _ ε CcR KeR Dk hE hε hCcR hKeR hDk hsm hk h1' h2
      refine ⟨key.trans ?_, ?_⟩
      · have : 0 ≤ ε * (|softKappa CL CR p X N| * softEnvWeb CR p X N ((N : ℤ) - n)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right (by linarith : 2 * CcR + 2 * Dk * KeR ≤ Cerr) this]
      · rw [abs_mul]
        calc |softKappa CL CR p X N| * |CR.psiHatL p X N ((N : ℤ) - n)| ≤ |softKappa CL CR p X N| * (KeR * softEnvWeb CR p X N ((N : ℤ) - n)) :=
              mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          _ ≤ |softKappa CL CR p X N| * (Cenv * softEnvWeb CR p X N ((N : ℤ) - n)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE2 hE) (abs_nonneg _)
          _ = _ := by ring

end Row

section VecErr

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- `hat N^2 = sum (numerator)^2`. -/
lemma softNorm_sq (p : Par × ℝ) (X : ℝ) (N : ℕ) :
    softNorm CL CR p X N ^ 2 = ∑ n ∈ rowsOf N, softNum CL CR p X N n ^ 2 := by
  unfold softNorm glueNorm
  rw [Real.sq_sqrt (add_nonneg (Finset.sum_nonneg (fun n _ => sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun n _ => sq_nonneg _))))]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hz : CL.Zof p X N n ≤ 0
  · simp [softNum, hz]
  · simp [softNum, hz]
    unfold softKappa
    ring

lemma softVec_eq (p : Par × ℝ) (X : ℝ) (N : ℕ) (n : ℤ) :
    softVec CL CR p X N n = softNum CL CR p X N n / softNorm CL CR p X N := by
  unfold softVec glueVec softNum softNorm
  by_cases hz : CL.Zof p X N n ≤ 0
  · simp [hz]
  · simp [hz]
    rfl

/-- **the first clause of `PropThaW2` (2)**, core: `normalised_error` on the glued vector, from the per-row bounds, the envelope sum and the small parameter. -/
theorem vec_err_core {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (p : Par × ℝ) (X : ℝ) (N : ℕ) (ψL : ℤ → ℝ)
    (Cerr Cenv Cs ε : ℝ) (hCerr : 0 ≤ Cerr) (hCenv : 0 ≤ Cenv) (hCs : 0 ≤ Cs) (hε : 0 ≤ ε)
    (hnorm : 0 < softNorm CL CR p X N)
    (hrow : ∀ n ∈ rowsOf N, |ψL n - softNum CL CR p X N n| ≤ Cerr * ε * softEnvNum CL CR p X N n ∧
      |softNum CL CR p X N n| ≤ Cenv * softEnvNum CL CR p X N n)
    (hsum : ∑ n ∈ rowsOf N, softEnvNum CL CR p X N n ^ 2 ≤ Cs * ∑ n ∈ rowsOf N, softNum CL CR p X N n ^ 2)
    (hsmall : Cerr * ε * Real.sqrt Cs ≤ 1 / 2) :
    ∀ n ∈ rowsOf N, |ψL n / Real.sqrt (∑ n ∈ rowsOf N, ψL n ^ 2) - softVec CL CR p X N n| ≤
      (2 + 2 * Cenv * Real.sqrt Cs) * Cerr * ε * softEnv CL CR p X N n := by
  have hsq := softNorm_sq CL CR p X N
  have hpos : 0 < ∑ n ∈ rowsOf N, softNum CL CR p X N n ^ 2 := by rw [← hsq]; positivity
  have hne := normalised_error (rowsOf N) ψL (softNum CL CR p X N) (softEnvNum CL CR p X N) (Cerr * ε) Cenv Cs
    (by positivity) hCenv hCs hpos (fun n _ => softEnvNum_nonneg hf CL CR p X N n)
    (fun n hn => (hrow n hn).1) (fun n hn => (hrow n hn).2) hsum hsmall
  have hsn : Real.sqrt (∑ n ∈ rowsOf N, softNum CL CR p X N n ^ 2) = softNorm CL CR p X N := by
    rw [← hsq, Real.sqrt_sq hnorm.le]
  intro n hn
  have h1 := hne n hn
  rw [hsn] at h1
  rw [softVec_eq, softEnv_eq]
  refine h1.trans (le_of_eq ?_)
  field_simp

end VecErr

section VecMain

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

lemma small_aux (a : ℝ) (ha : 0 ≤ a) : a * (1 / (2 * (a + 1))) ≤ 1 / 2 := by
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  linarith

/-- **`prop:tha-W2` (2), first clause, for the exact solutions**: for `psi^L = kappa psi^R` with the seeds `psi-hat_0`,
`|psi^L_n / ||psi^L|| - hat Psi_n| <= C h^m Lm V_n / hat N` on every row. -/
theorem soft_vec_err (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (aplus : ℝ) :
    ∃ Ce h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      CL.aOf p X N ≤ aplus →
      ∀ (ψL ψ' : ℤ → ℝ) (κ : ℝ),
        JacSol Fz p N X (CL.chain p X N).NR ψL → ψL 0 = CL.psiHatL p X N 0 →
        JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR ψ' → ψ' 0 = CR.psiHatL p X N 0 →
        (∀ n ∈ rowsOf N, ψL n = κ * ψ' ((N : ℤ) - n)) →
        ∀ n ∈ rowsOf N, |ψL n / Real.sqrt (∑ n ∈ rowsOf N, ψL n ^ 2) - softVec CL CR p X N n| ≤
          Ce * (Fz.step N ^ m * Lm (Fz.step N)) * softEnv CL CR p X N n := by
  obtain ⟨Ck, Dk, cn, h0a, h0ap, hCk, hDk, hcn, Hm⟩ := soft_match CL CR hf hm hLm hM aplus
  obtain ⟨C0, C1, h0b, h0bp, hC0, hC1, Hs⟩ := soft_env_sum CL CR hM hf hm hLm aplus
  obtain ⟨CcL, KeL, h0c, h0cp, hCcL, hKeL, HL⟩ := left_pw CL hf hm hLm
  obtain ⟨CcR, KeR, h0d, h0dp, hCcR, hKeR, HR⟩ := left_pw CR hf hm hLm
  obtain ⟨Cc1, h0e, clam, Clam, h0ep, hclam, H1⟩ := propThaW2_item1 CL hf hm hLm
  set Cerr : ℝ := max CcL (2 * CcR + 2 * Dk * KeR) with hCerr
  set Cenv : ℝ := max KeL KeR with hCenv
  set Cs : ℝ := (C0 + C1 * ((1 + Dk) * Ck) ^ 2) / cn with hCs
  have hCerr0 : 0 ≤ Cerr := le_trans hCcL (le_max_left _ _)
  have hCenv0 : 0 ≤ Cenv := le_trans hKeL (le_max_left _ _)
  have hCs0 : 0 ≤ Cs := by positivity
  set e0 : ℝ := 1 / (2 * (Cerr * Real.sqrt Cs + Dk + 1)) with he0
  have he0p : 0 < e0 := by positivity
  refine ⟨(2 + 2 * Cenv * Real.sqrt Cs) * Cerr, min (min (min h0a h0b) (min h0c h0d)) (min (min h0e CL.softH2) (softHL CL e0)),
    lt_min (lt_min (lt_min h0ap h0bp) (lt_min h0cp h0dp)) (lt_min (lt_min h0ep CL.softH2_pos) (softHL_pos CL e0)), ?_⟩
  intro p hp N hN hstep X hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  have hsa : Fz.step N ≤ h0a := (((hstep.trans (min_le_left _ _)).trans (min_le_left _ _))).trans (min_le_left _ _)
  have hsb : Fz.step N ≤ h0b := (((hstep.trans (min_le_left _ _)).trans (min_le_left _ _))).trans (min_le_right _ _)
  have hsc : Fz.step N ≤ h0c := (((hstep.trans (min_le_left _ _)).trans (min_le_right _ _))).trans (min_le_left _ _)
  have hsd : Fz.step N ≤ h0d := (((hstep.trans (min_le_left _ _)).trans (min_le_right _ _))).trans (min_le_right _ _)
  have hse : Fz.step N ≤ h0e := ((hstep.trans (min_le_right _ _)).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hs2 : Fz.step N ≤ CL.softH2 := ((hstep.trans (min_le_right _ _)).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hsf : Fz.step N ≤ softHL CL e0 := (hstep.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := hs2.trans (CL.softH2_le_H1.trans CL.softH1_le_one)
  obtain ⟨hNR, hXR⟩ := mirror_ctx hM hp hX hN
  have FL : LeftFacts CL p X N ψL CcL KeL := HL p hp N hN hsc X hX ψL hJL hsL
  have FR : LeftFacts CR p X N ψ' CcR KeR := HR p hp N hNR hsd X hXR ψ' hJR hsR
  obtain ⟨-, -, h3, h4, h5⟩ := Hm p hp N hN hsa X hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  have hε0 : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) := powLm_nonneg CL hh0 hh1
  have hεe0 : Fz.step N ^ m * Lm (Fz.step N) ≤ e0 := (pow_Lm_le CL hm hh0 hh1).trans (softHL_spec CL he0p hh0 hsf)
  have hkey : (Cerr * Real.sqrt Cs + Dk) * e0 ≤ 1 / 2 := small_aux _ (by positivity)
  have hsq0 : 0 ≤ Cerr * Real.sqrt Cs := mul_nonneg hCerr0 (Real.sqrt_nonneg _)
  have hsm : Dk * (Fz.step N ^ m * Lm (Fz.step N)) ≤ 1 / 2 := by
    calc Dk * (Fz.step N ^ m * Lm (Fz.step N)) ≤ Dk * e0 := mul_le_mul_of_nonneg_left hεe0 hDk
      _ ≤ (Cerr * Real.sqrt Cs + Dk) * e0 := mul_le_mul_of_nonneg_right (by simp only [le_add_iff_nonneg_left, le_add_iff_nonneg_right]; first | exact hsq0 | exact hDk) he0p.le
      _ ≤ 1 / 2 := hkey
  have hsmall : Cerr * (Fz.step N ^ m * Lm (Fz.step N)) * Real.sqrt Cs ≤ 1 / 2 := by
    calc Cerr * (Fz.step N ^ m * Lm (Fz.step N)) * Real.sqrt Cs = (Cerr * Real.sqrt Cs) * (Fz.step N ^ m * Lm (Fz.step N)) := by ring
      _ ≤ (Cerr * Real.sqrt Cs) * e0 := mul_le_mul_of_nonneg_left hεe0 hsq0
      _ ≤ (Cerr * Real.sqrt Cs + Dk) * e0 := mul_le_mul_of_nonneg_right (by simp only [le_add_iff_nonneg_left, le_add_iff_nonneg_right]; first | exact hsq0 | exact hDk) he0p.le
      _ ≤ 1 / 2 := hkey
  have hrow : ∀ n ∈ rowsOf N, |ψL n - softNum CL CR p X N n| ≤ Cerr * (Fz.step N ^ m * Lm (Fz.step N)) * softEnvNum CL CR p X N n ∧
      |softNum CL CR p X N n| ≤ Cenv * softEnvNum CL CR p X N n := fun n hn =>
    soft_row CL CR hM hf hp hX ψL ψ' κ CcL KeL CcR KeR Dk _ Cerr Cenv hrel FL FR hCcL hKeL hCcR hKeR hDk hε0 hsm h3
      (le_max_left _ _) (le_max_right _ _) (le_max_left _ _) (le_max_right _ _) rfl hn
  -- the envelope sum and the normalisation
  have hk : |softKappa CL CR p X N * CR.lamL p X N| ≤ ((1 + Dk) * Ck) * |CL.lamL p X N| := by
    rw [abs_mul]; exact h4
  have hCk' : 0 ≤ (1 + Dk) * Ck := by positivity
  have hSum := Hs p hp N hN hsb X hX ha ((1 + Dk) * Ck) hCk' ψL ψ' hJL hsL hJR hsR hk
  obtain ⟨-, hlow, -⟩ := H1 p hp N hN hse X hX
  have hκ := kappaBal_pos (CL.aOf p X N)
  have hlam : 0 < |CL.lamL p X N| := by
    have h1 := softLam_pos CL p X N
    have : 0 < clam * (softLam CL p X N * kappaBal (CL.aOf p X N)) := by positivity
    linarith
  have hT : 0 < |CL.lamL p X N| / kappaBal (CL.aOf p X N) := div_pos hlam hκ
  have hE : 0 < Fz.step N ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hh0 _
  set T := |CL.lamL p X N| / kappaBal (CL.aOf p X N) with hTdef
  set E := Fz.step N ^ (-(1 : ℝ) / 2) with hEdef
  have hTE : 0 < T ^ 2 * E := by positivity
  have hnsq : 0 < softNorm CL CR p X N ^ 2 := lt_of_lt_of_le (mul_pos hcn hTE) h5
  have hnorm : 0 < softNorm CL CR p X N := by
    have hnn : 0 ≤ softNorm CL CR p X N := Real.sqrt_nonneg _
    refine lt_of_le_of_ne hnn (fun h => ?_)
    rw [← h] at hnsq
    simp at hnsq
  have hsum : ∑ n ∈ rowsOf N, softEnvNum CL CR p X N n ^ 2 ≤ Cs * ∑ n ∈ rowsOf N, softNum CL CR p X N n ^ 2 := by
    rw [← softNorm_sq]
    calc ∑ n ∈ rowsOf N, softEnvNum CL CR p X N n ^ 2 ≤ (C0 + C1 * ((1 + Dk) * Ck) ^ 2) * T ^ 2 * E := hSum
      _ = Cs * (cn * (T ^ 2 * E)) := by rw [hCs]; field_simp
      _ ≤ Cs * softNorm CL CR p X N ^ 2 := mul_le_mul_of_nonneg_left h5 hCs0
  exact vec_err_core CL CR hf p X N ψL Cerr Cenv Cs _ hCerr0 hCenv0 hCs0 hε0 hnorm hrow hsum hsmall

end VecMain

section Eigen

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- the Weber seed of `psi-hat^L` is positive. -/
lemma psiHatL_zero_pos {F : SymbolFamily (Par × ℝ)} (C : SoftEdgeChart F P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - F.bandHi p| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N) (hstep : F.step N ≤ C.η) : 0 < C.psiHatL p X N 0 := by
  rw [psiHatL_of_le C p X N (uNode_zero_le C hp hstep)]
  exact C.seed_posW p hp X hX N hN

lemma softEnv_nonneg {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (p : Par × ℝ) (X : ℝ) (N : ℕ) (n : ℤ) :
    0 ≤ softEnv CL CR p X N n := by
  rw [softEnv_eq]
  exact div_nonneg (softEnvNum_nonneg hf CL CR p X N n) (Real.sqrt_nonneg _)

/-- **`prop:tha-W2` (2), the eigen-system clauses (first two)**: at an eigenvalue satisfying Step 0 the eigenvector is `C h^m Lm V/hat N`-close to `hat Psi` on every row, and `sum V^2/hat N^2 <= C`. -/
theorem soft_eigen_main (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (Cs0 : ℝ) :
    ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        (∀ i, Xs i ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2) → ∀ k : Fin (N + 1), |Xs k - Fz.bandHi p| ≤ CL.δ0 →
          (∀ n ∈ rowsOf N, |eigVec Um k n - softVec CL CR p (Xs k) N n| ≤ Cc * (Fz.step N ^ m * Lm (Fz.step N)) * softEnv CL CR p (Xs k) N n) ∧
          ∑ n ∈ rowsOf N, softEnv CL CR p (Xs k) N n ^ 2 ≤ Cc := by
  obtain ⟨ha0, h0a, h0ap, Ha⟩ : ∃ _ : True, ∃ h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      X ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2 → CL.aOf p X N ≤ asmAplus CL := by
    obtain ⟨h0, h0p, H⟩ := aOf_le_of_step0 CL Cs0
    exact ⟨trivial, h0, h0p, fun p hp N hs X hX hx => H p hp N hs X hX hx⟩
  obtain ⟨Ce, h0b, h0bp, Hb⟩ := soft_vec_err CL CR hM hf hm hLm (asmAplus CL)
  obtain ⟨Cl, h0c, h0cp, Hc⟩ := soft_env_l2 CL CR hM hf hm hLm (asmAplus CL)
  refine ⟨max Ce (max Cl 0), min (min h0a h0b) (min h0c (min CL.softH1 (min CR.softH1 (min CL.η CR.η)))),
    lt_min (lt_min h0ap h0bp) (lt_min h0cp (lt_min CL.softH1_pos (lt_min CR.softH1_pos (lt_min CL.consts_pos.2.1 CR.consts_pos.2.1)))), ?_⟩
  intro p hp N hN hstep Xs Um hE hs0 k hX
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN2 : CR.N0 ≤ N := (le_max_right _ _).trans hN
  have hsa : Fz.step N ≤ h0a := (hstep.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hsb : Fz.step N ≤ h0b := (hstep.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hsc : Fz.step N ≤ h0c := (hstep.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs1 : Fz.step N ≤ CL.softH1 := ((hstep.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs1R : Fz.step N ≤ CR.softH1 := (((hstep.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsη : Fz.step N ≤ CL.η := (((hstep.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsηR : Fz.step N ≤ CR.η := (((hstep.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans ((min_le_right _ _).trans (min_le_right _ _))
  set X := Xs k with hXk
  obtain ⟨hNR, hXR⟩ := mirror_ctx hM hp hX hN1
  have ha := Ha p hp N (hstep.trans ((min_le_left _ _).trans (min_le_left _ _))) X hX (hs0 k)
  have hpos := bondA_pos_all CL CR hM hp hX hN1 hs1 hs1R
  -- exact solutions
  have hLpos : ∀ n : ℤ, 0 ≤ n → n < N → Fz.bondA p N n ≠ 0 := fun n h0 h1 => (hpos n h0 h1).ne'
  have hRpos : ∀ n : ℤ, 0 ≤ n → n < N → (mirrorFamily Fz).bondA p N n ≠ 0 := by
    intro n h0 h1
    rw [bondA_mirror]
    exact (hpos _ (by omega) (by omega)).ne'
  obtain ⟨ψL, hψL0, hψL⟩ := exists_seeded (Fz.bondA p N) (Fz.diagQ p N X) N hLpos (CL.psiHatL p X N 0)
  obtain ⟨ψ', hψ'0, hψ'⟩ := exists_seeded ((mirrorFamily Fz).bondA p N) ((mirrorFamily Fz).diagQ p N X) N hRpos (CR.psiHatL p X N 0)
  have hJL : JacSol Fz p N X N ψL := hψL
  have hJR : JacSol (mirrorFamily Fz) p N X N ψ' := hψ'
  have hLp : 0 < ψL 0 := by rw [hψL0]; exact psiHatL_zero_pos CL hp hX hN1 hsη
  have hRp : ψ' 0 ≠ 0 := by rw [hψ'0]; exact (psiHatL_zero_pos CR hp hXR hNR hsηR).ne'
  obtain ⟨hrel0, hev⟩ := psiL_eq_kappa_psiR Fz p N hpos Xs Um hE k ψL hJL hLp ψ' hJR hRp
  have hNRL : (CL.chain p X N).NR ≤ N := by
    have := row_le_N Fz N (j := (CL.chain p X N).NR) (by
      obtain ⟨-, -, -, -, -, -, hNRu, -⟩ := CL.shape p hp X hX N hN1
      have := (CL.ucη_in p hp).2
      have hη := CL.consts_pos.2.1
      linarith)
    exact_mod_cast this
  have hNRR : (CR.chain p X N).NR ≤ N := by
    have := row_le_N (mirrorFamily Fz) N (j := (CR.chain p X N).NR) (by
      obtain ⟨-, -, -, -, -, -, hNRu, -⟩ := CR.shape p hp X hXR N hNR
      have := (CR.ucη_in p hp).2
      have hη := CR.consts_pos.2.1
      linarith)
    exact_mod_cast this
  have hJL' : JacSol Fz p N X (CL.chain p X N).NR ψL := fun n h0 h1 => hJL n h0 (lt_of_lt_of_le h1 (by exact_mod_cast hNRL))
  have hJR' : JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR ψ' := fun n h0 h1 => hJR n h0 (lt_of_lt_of_le h1 (by exact_mod_cast hNRR))
  have hrel : ∀ n ∈ rowsOf N, ψL n = (ψL N / ψ' 0) * ψ' ((N : ℤ) - n) := hrel0
  refine ⟨?_, ?_⟩
  · intro n hn
    have h1 := Hb p hp N hN1 hsb X hX ha ψL ψ' _ hJL' hψL0 hJR' hψ'0 hrel n hn
    rw [hev n hn]
    have hε : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) := by
      have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
      exact powLm_nonneg CL hh0 (hs1.trans (CL.softH1_le_one))
    have hV := softEnv_nonneg CL CR hf p X N n
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hε) hV
  · have h2 := Hc p hp N hN1 hsc X hX ha ψL ψ' _ hJL' hψL0 hJR' hψ'0 hrel
    exact h2.trans ((le_max_left _ _).trans (le_max_right _ _))

end Eigen

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.psiHatL_envW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psiHatL_envW

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.left_pw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms left_pw

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_row

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.vec_err_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vec_err_core

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_vec_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_vec_err

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_eigen_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_eigen_main

end FormalResearch.JacobiEigenvectors.TheoremA

end
