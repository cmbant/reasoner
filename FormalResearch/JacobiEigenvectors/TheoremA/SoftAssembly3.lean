module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly2
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftQuant
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftTails

/-!
# Soft-edge assembly, part C: the envelope sum (T4) for `PropThaW2` (2)

Source: app_thmA, proof of prop:tha-W2, Step 4 (d) (the four tail blocks) and (e) (the sum of the envelope).

Proved here:
* `softEnvNum`: the numerator of `softEnv` (`softEnv = softEnvNum / softNorm`, `softEnv_eq`).
* `soft_env_pw`: pointwise, `softEnvNum_n^2` is at most the sum of five indicator terms (left Weber, window, left PC tail, right PC tail, right Weber).
* `soft_env_sum` (T4): `sum_n softEnvNum_n^2 <= (C0 + C1 Ck^2) (|lam_L|/kappa_bal)^2 h^{-1/2}`, from `weber_tail`, `weber_tail_right`, `pc_tail_left/right`, `soft_win_massw`, `molv_win_two`, `molv_upper`
  and the sign fact `Zof_pos_of_far` (`zeta_sign_out`).

Differences from the paper: the window rows use `molv_win_two` (both `a <= 0` and `0 < a <= a_+` at once); the right-hand data enter through the premise `|kappa-hat lam_R| <= Ck |lam_L|`
(the conclusion of `soft_match`), as in `weber_tail_right`.

* `soft_env_l2`: `sum_n softEnv_n^2 <= Cc` (the second clause of the eigen-system part of `PropThaW2` (2)), from `soft_env_sum` and the normalisation lower bound
  `hat N^2 >= cn (|lam_L|/kappa_b)^2 h^{-1/2}` that is the fifth conjunct of `soft_match` (`SoftAssembly.lean`, `norm_lower_alg`).  Hypotheses: `ParabolicCylinderFacts`, `1 <= m`, `1 <= Lm`, `SoftMirror`,
  `a <= a_+`, and exact solutions `psi^L`, `psi'` with `psi^L = kappa psi^R` (which `psiL_eq_kappa_psiR` gives at an eigenvalue).

Not formalised: the pointwise comparison `|Psi - hat Psi| <= C h^m Lm V` (E7, first clause), the off-window relative bound (R2: needs a lower bound of `|psi-hat|` by `V`), counting (E9), the assembly of `PropThaW2`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section EnvNum

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- the numerator `V_n` of `softEnv = V_n / hat N`. -/
def softEnvNum (p : Par × ℝ) (X : ℝ) (N : ℕ) (n : ℤ) : ℝ :=
  if uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2 then softEnvWeb CL p X N n
  else if CL.Zof p X N n ≤ 0 then |CL.lamL p X N| * Molv U V (CL.aOf p X N) (-(CL.Zof p X N n))
  else if uNode (Fz.step N) n < CL.uc p + CL.η / 2 then
    |softKappa CL CR p X N * CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n)
  else |softKappa CL CR p X N| * softEnvWeb CR p X N ((N : ℤ) - n)

lemma softEnv_eq (p : Par × ℝ) (X : ℝ) (N : ℕ) (n : ℤ) :
    softEnv CL CR p X N n = softEnvNum CL CR p X N n / softNorm CL CR p X N := rfl

end EnvNum

section Pointwise

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- **pointwise bound of the envelope numerator**: every row falls in one of the four branches of `softEnv`, and the square of the numerator is at most the sum of five nonnegative indicator terms. -/
lemma soft_env_pw {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (aplus : ℝ) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (ha : CL.aOf p X N ≤ aplus) {n : ℤ} (hn : n ∈ rowsOf N) {Ck : ℝ} (hCk : 0 ≤ Ck)
    (hk : |softKappa CL CR p X N * CR.lamL p X N| ≤ Ck * |CL.lamL p X N|) :
    softEnvNum CL CR p X N n ^ 2 ≤
      (if uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2 then softEnvWeb CL p X N n ^ 2 else 0) +
      (if n ∈ softWindow CL p X N then
        ((1 + Ck) * (CPC * Real.exp (cWt aplus)) * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ^ 2 else 0) +
      (if |uNode (Fz.step N) n - CL.uc p| < CL.η / 2 ∧ CL.Zof p X N n < -rhoWin (CL.aOf p X N) then
        (CPC * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) *
          (Eminus (CL.aOf p X N) (CL.Zof p X N n) * Mbal (CL.aOf p X N) (CL.Zof p X N n))) ^ 2 else 0) +
      (if |uNode (Fz.step N) n - CL.uc p| < CL.η / 2 ∧ rhoWin (CL.aOf p X N) < CL.Zof p X N n then
        (Ck * CPC * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) *
          (Eminus (CL.aOf p X N) (-CL.Zof p X N n) * Mbal (CL.aOf p X N) (CL.Zof p X N n))) ^ 2 else 0) +
      (if CL.uc p + CL.η / 2 ≤ uNode (Fz.step N) n then
        (|softKappa CL CR p X N| * softEnvWeb CR p X N ((N : ℤ) - n)) ^ 2 else 0) := by
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  have hκ := kappaBal_pos (CL.aOf p X N)
  have hη := CL.consts_pos.2.1
  have hκne : kappaBal (CL.aOf p X N) ≠ 0 := hκ.ne'
  set a := CL.aOf p X N with ha_def
  set Tw := |CL.lamL p X N| / kappaBal a with hTwdef
  have hTw0 : 0 ≤ Tw := div_nonneg (abs_nonneg _) hκ.le
  set Z := CL.Zof p X N n with hZ
  set ρ := rhoWin a with hρ
  set u := uNode (Fz.step N) n with hu
  have hMb := Mbal_pos a Z
  have hwin : n ∈ softWindow CL p X N ↔ |Z| ≤ ρ := by
    unfold softWindow; simp [hn, hZ, hρ, ha_def]
  have hEM : ∀ w : ℝ, 0 ≤ Eminus a w * Mbal a w := fun w => mul_nonneg (Eminus_pos _ _).le (Mbal_pos _ _).le
  have hexp := Real.exp_pos (cWt aplus)
  have n1 : 0 ≤ (if uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2 then softEnvWeb CL p X N n ^ 2 else 0) := by split_ifs <;> positivity
  have n2 : 0 ≤ (if n ∈ softWindow CL p X N then
        ((1 + Ck) * (CPC * Real.exp (cWt aplus)) * Tw * Mbal a Z) ^ 2 else 0) := by split_ifs <;> positivity
  have n3 : 0 ≤ (if |u - CL.uc p| < CL.η / 2 ∧ Z < -ρ then (CPC * Tw * (Eminus a Z * Mbal a Z)) ^ 2 else 0) := by split_ifs <;> positivity
  have n4 : 0 ≤ (if |u - CL.uc p| < CL.η / 2 ∧ ρ < Z then (Ck * CPC * Tw * (Eminus a (-Z) * Mbal a Z)) ^ 2 else 0) := by split_ifs <;> positivity
  have n5 : 0 ≤ (if CL.uc p + CL.η / 2 ≤ u then (|softKappa CL CR p X N| * softEnvWeb CR p X N ((N : ℤ) - n)) ^ 2 else 0) := by
    split_ifs <;> positivity
  unfold softEnvNum
  by_cases b1 : uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2
  · rw [if_pos b1, if_pos b1]; linarith
  · rw [if_neg b1, if_neg b1]
    by_cases b2 : CL.Zof p X N n ≤ 0
    · rw [if_pos b2]
      have hu4 := lt_of_Zof_nonpos CL hp hX hn b2
      have hmol0 := molv_nonneg hf a (-Z)
      have hfm0 : 0 ≤ |CL.lamL p X N| * Molv U V a (-Z) := mul_nonneg (abs_nonneg _) hmol0
      by_cases hz : |Z| ≤ ρ
      · have h1 := (hwin.mpr hz)
        have hmw := (molv_win_two hf aplus a (-Z) ha (by rwa [abs_neg])).2
        rw [Mbal_neg] at hmw
        have hle : |CL.lamL p X N| * Molv U V a (-Z) ≤ (1 + Ck) * (CPC * Real.exp (cWt aplus)) * Tw * Mbal a Z := by
          calc |CL.lamL p X N| * Molv U V a (-Z) ≤ |CL.lamL p X N| * (CPC * Real.exp (cWt aplus) * ((kappaBal a)⁻¹ * Mbal a Z)) :=
                mul_le_mul_of_nonneg_left hmw (abs_nonneg _)
            _ = Tw * (CPC * Real.exp (cWt aplus)) * Mbal a Z := by rw [hTwdef]; field_simp
            _ ≤ (1 + Ck) * (CPC * Real.exp (cWt aplus)) * Tw * Mbal a Z := by
                have : 0 ≤ CPC * Real.exp (cWt aplus) * Tw * Mbal a Z := by positivity
                nlinarith
        have := pow_le_pow_left₀ hfm0 hle 2
        rw [if_pos h1]; linarith
      · push_neg at hz
        have hZneg : Z < -ρ := by
          have := abs_of_nonpos b2
          rw [this] at hz; linarith
        have hcond : |u - CL.uc p| < CL.η / 2 ∧ Z < -ρ := by
          refine ⟨?_, hZneg⟩
          rw [abs_lt]; constructor <;> [linarith [not_le.mp b1]; linarith]
        have hmu := molv_upper hf a (-Z)
        rw [Wmol_neg_of_nonpos a b2, Mbal_neg] at hmu
        have hle : |CL.lamL p X N| * Molv U V a (-Z) ≤ CPC * Tw * (Eminus a Z * Mbal a Z) := by
          calc |CL.lamL p X N| * Molv U V a (-Z) ≤ |CL.lamL p X N| * (CPC * (kappaBal a)⁻¹ * Eminus a Z * Mbal a Z) :=
                mul_le_mul_of_nonneg_left hmu (abs_nonneg _)
            _ = CPC * Tw * (Eminus a Z * Mbal a Z) := by rw [hTwdef]; field_simp
        have := pow_le_pow_left₀ hfm0 hle 2
        rw [if_pos hcond]; linarith
    · rw [if_neg b2]
      push_neg at b2
      by_cases b3 : uNode (Fz.step N) n < CL.uc p + CL.η / 2
      · rw [if_pos b3]
        have hmol0 := molv_nonneg hf a Z
        have hfm0 : 0 ≤ |softKappa CL CR p X N * CR.lamL p X N| * Molv U V a Z := mul_nonneg (abs_nonneg _) hmol0
        by_cases hz : Z ≤ ρ
        · have h1 := (hwin.mpr (by rw [abs_of_pos b2]; exact hz))
          have hmw := (molv_win_two hf aplus a Z ha (by rw [abs_of_pos b2]; exact hz)).2
          have hle : |softKappa CL CR p X N * CR.lamL p X N| * Molv U V a Z ≤ (1 + Ck) * (CPC * Real.exp (cWt aplus)) * Tw * Mbal a Z := by
            calc |softKappa CL CR p X N * CR.lamL p X N| * Molv U V a Z ≤ (Ck * |CL.lamL p X N|) * (CPC * Real.exp (cWt aplus) * ((kappaBal a)⁻¹ * Mbal a Z)) :=
                  mul_le_mul hk hmw hmol0 (by positivity)
              _ = Ck * Tw * (CPC * Real.exp (cWt aplus)) * Mbal a Z := by rw [hTwdef]; field_simp
              _ ≤ (1 + Ck) * (CPC * Real.exp (cWt aplus)) * Tw * Mbal a Z := by
                  have : 0 ≤ CPC * Real.exp (cWt aplus) * Tw * Mbal a Z := by positivity
                  nlinarith
          have := pow_le_pow_left₀ hfm0 hle 2
          rw [if_pos h1]; linarith
        · push_neg at hz
          have hcond : |u - CL.uc p| < CL.η / 2 ∧ ρ < Z := by
            refine ⟨?_, hz⟩
            rw [abs_lt]; constructor <;> [linarith [not_le.mp b1]; linarith]
          have hmu := molv_upper hf a Z
          rw [Wmol_pos_eq a b2.le] at hmu
          have hle : |softKappa CL CR p X N * CR.lamL p X N| * Molv U V a Z ≤ Ck * CPC * Tw * (Eminus a (-Z) * Mbal a Z) := by
            calc |softKappa CL CR p X N * CR.lamL p X N| * Molv U V a Z ≤ (Ck * |CL.lamL p X N|) * (CPC * (kappaBal a)⁻¹ * Eminus a (-Z) * Mbal a Z) :=
                  mul_le_mul hk hmu hmol0 (by positivity)
              _ = Ck * CPC * Tw * (Eminus a (-Z) * Mbal a Z) := by rw [hTwdef]; field_simp
          have := pow_le_pow_left₀ hfm0 hle 2
          rw [if_pos hcond]; linarith
      · rw [if_neg b3]
        have hb : CL.uc p + CL.η / 2 ≤ uNode (Fz.step N) n := not_lt.mp b3
        rw [if_pos hb]; linarith

end Pointwise

section Sum

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

lemma real_tail (dm r s : ℝ) (hdm : 0 < dm) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) :
    3 + 4 / dm * r / s ≤ (3 + 4 / dm) * s⁻¹ := by
  have hinv : 1 ≤ s⁻¹ := one_le_inv₀ hs |>.mpr hs1
  have h1 : 4 / dm * r / s ≤ 4 / dm * s⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) hr1) (by positivity)
  have h2 : (3 + 4 / dm) * s⁻¹ = 3 * s⁻¹ + 4 / dm * s⁻¹ := by ring
  have h3 : 3 + 4 / dm * r / s = 3 + 4 / dm * r / s := rfl
  have h4 : 4 / dm * r / s = 4 / dm * r / s := rfl
  rw [h2]
  have : 3 + 4 / dm * r / s = 3 + (4 / dm * r) / s := by ring
  linarith

lemma cube_inv_le_one (a : ℝ) : ((1 + max (-a) 0) ^ ((1 : ℝ) / 3))⁻¹ ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact Real.one_le_rpow (by have := le_max_right (-a) 0; linarith) (by norm_num)

lemma rpow_half_eq {h : ℝ} (hh : 0 < h) : h ^ (-(1 : ℝ) / 2) = (Real.sqrt h)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hh.le]; congr 1; ring

/-- (S1) the left Weber block. -/
lemma env_sum_weberL {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) :
    ∃ A h0 : ℝ, 0 < h0 ∧ 0 ≤ A ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      ∀ ψL : ℤ → ℝ, JacSol Fz p N X (CL.chain p X N).NR ψL → ψL 0 = CL.psiHatL p X N 0 →
        ∑ n ∈ rowsOf N, (if uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2 then softEnvWeb CL p X N n ^ 2 else 0) ≤
          A * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2) := by
  obtain ⟨Cw1, cw1, h1, h1p, hcw1, W1⟩ := weber_tail CL hf hm hLm
  refine ⟨max Cw1 0, min h1 1, lt_min h1p one_pos, le_max_right _ _, ?_⟩
  intro p hp N hN hstep X hX ψL hJL hsL
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs4 : Fz.step N ≤ 1 := hstep.trans (min_le_right _ _)
  have hone : 1 ≤ Fz.step N ^ (-(1 : ℝ) / 2) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh0 hs4 (by norm_num)
  rw [← Finset.sum_filter]
  have hsh := CL.shapeW p hp X hX N hN
  obtain ⟨-, -, hNR0, hA, hB⟩ := hsh
  have hsub : (rowsOf N).filter (fun n => uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2) ⊆ Finset.Icc (0 : ℤ) (CL.chainW p X N).NR := by
    intro n hn
    simp only [rowsOf, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    refine ⟨hn.1.1, ?_⟩
    by_contra hlt
    have h4 := SoftEdgeChart.uNode_mono_le hh0.le (show (CL.chainW p X N).NR + 1 ≤ n by omega)
    linarith [hn.2]
  have h5 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg (softEnvWeb CL p X N n))
  have h6 := W1 p hp N hN (hstep.trans (min_le_left _ _)) X hX ψL hJL hsL
  refine h5.trans (h6.trans ?_)
  have hex : Real.exp (-(cw1 / Fz.step N)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ cw1 / Fz.step N := div_nonneg hcw1.le hh0.le
    linarith)
  have hex0 := Real.exp_pos (-(cw1 / Fz.step N))
  have hT2 := sq_nonneg (|CL.lamL p X N| / kappaBal (CL.aOf p X N))
  calc Cw1 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Real.exp (-(cw1 / Fz.step N))
      ≤ max Cw1 0 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hT2) hex hex0.le
        exact mul_nonneg (le_max_right _ _) hT2
    _ ≤ _ := by
        rw [mul_one]
        exact le_mul_of_one_le_right (mul_nonneg (le_max_right _ _) hT2) hone

/-- (S2) the window block. -/
lemma env_sum_window {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (aplus : ℝ) :
    ∃ A h0 : ℝ, 0 < h0 ∧ 0 ≤ A ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      CL.aOf p X N ≤ aplus → ∀ Ck : ℝ, 0 ≤ Ck →
        ∑ n ∈ rowsOf N, (if n ∈ softWindow CL p X N then
          ((1 + Ck) * (CPC * Real.exp (cWt aplus)) * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ^ 2 else 0) ≤
          A * (1 + Ck ^ 2) * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2) := by
  obtain ⟨cM, CM, h3, hcM, h3p, Hm⟩ := soft_win_massw CL hf aplus
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  refine ⟨2 * (CPC * Real.exp (cWt aplus)) ^ 2 * max CM 0, h3, h3p, by positivity, ?_⟩
  intro p hp N hN hstep X hX ha Ck hCk
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  rw [← Finset.sum_filter]
  have hsub : (rowsOf N).filter (fun n => n ∈ softWindow CL p X N) ⊆ softWindow CL p X N := fun n hn => (Finset.mem_filter.mp hn).2
  set Kw : ℝ := CPC * Real.exp (cWt aplus) with hKw
  set T := |CL.lamL p X N| / kappaBal (CL.aOf p X N) with hT
  have h5 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg ((1 + Ck) * Kw * T * Mbal (CL.aOf p X N) (CL.Zof p X N n)))
  refine h5.trans ?_
  have e1 : ∑ n ∈ softWindow CL p X N, ((1 + Ck) * Kw * T * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ^ 2 =
      ((1 + Ck) * Kw * T) ^ 2 * wmMass CL p X N := by
    unfold wmMass; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [e1]
  have hmm := (Hm p hp N hN hstep X hX ha).2
  have hE0 : 0 ≤ Fz.step N ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hh0.le _
  have hmm' : wmMass CL p X N ≤ max CM 0 * Fz.step N ^ (-(1 : ℝ) / 2) := hmm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0)
  have hA3 : 0 ≤ max CM 0 := le_max_right _ _
  have hnn : 0 ≤ Kw ^ 2 * max CM 0 * T ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hA3) (sq_nonneg _)) hE0
  calc ((1 + Ck) * Kw * T) ^ 2 * wmMass CL p X N ≤ ((1 + Ck) * Kw * T) ^ 2 * (max CM 0 * Fz.step N ^ (-(1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hmm' (sq_nonneg _)
    _ = (1 + Ck) ^ 2 * (Kw ^ 2 * max CM 0 * T ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) := by ring
    _ ≤ (2 * (1 + Ck ^ 2)) * (Kw ^ 2 * max CM 0 * T ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) := by
        apply mul_le_mul_of_nonneg_right _ hnn
        nlinarith [sq_nonneg (1 - Ck)]
    _ = 2 * Kw ^ 2 * max CM 0 * (1 + Ck ^ 2) * T ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2) := by ring

/-- (S3) the left PC tail block. -/
lemma env_sum_tailL {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) (N : ℕ) (hs : Fz.step N ≤ 1) :
    ∑ n ∈ rowsOf N, (if |uNode (Fz.step N) n - CL.uc p| < CL.η / 2 ∧ CL.Zof p X N n < -rhoWin (CL.aOf p X N) then
        (CPC * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) *
          (Eminus (CL.aOf p X N) (CL.Zof p X N n) * Mbal (CL.aOf p X N) (CL.Zof p X N n))) ^ 2 else 0) ≤
      CPC ^ 2 * (3 + 4 / CL.dm) * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2) := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hdm := CL.consts_pos.2.2.1
  rw [← Finset.sum_filter, rpow_half_eq hh0]
  set T := |CL.lamL p X N| / kappaBal (CL.aOf p X N) with hT
  have e1 : ∑ n ∈ (rowsOf N).filter (fun n => |uNode (Fz.step N) n - CL.uc p| < CL.η / 2 ∧ CL.Zof p X N n < -rhoWin (CL.aOf p X N)),
      (CPC * T * (Eminus (CL.aOf p X N) (CL.Zof p X N n) * Mbal (CL.aOf p X N) (CL.Zof p X N n))) ^ 2 =
      (CPC * T) ^ 2 * ∑ n ∈ (rowsOf N).filter (fun n => |uNode (Fz.step N) n - CL.uc p| < CL.η / 2 ∧ CL.Zof p X N n < -rhoWin (CL.aOf p X N)),
        (Eminus (CL.aOf p X N) (CL.Zof p X N n) * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [e1]
  have h6 := pc_tail_left CL hp hX N
  have hsq : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hs1 : Real.sqrt (Fz.step N) ≤ 1 := Real.sqrt_le_one.mpr hs
  have h7 := real_tail CL.dm _ _ hdm (by positivity) (cube_inv_le_one (CL.aOf p X N)) hsq hs1
  calc (CPC * T) ^ 2 * _ ≤ (CPC * T) ^ 2 * ((3 + 4 / CL.dm) * (Real.sqrt (Fz.step N))⁻¹) :=
        mul_le_mul_of_nonneg_left (h6.trans h7) (sq_nonneg _)
    _ = CPC ^ 2 * (3 + 4 / CL.dm) * T ^ 2 * (Real.sqrt (Fz.step N))⁻¹ := by ring

/-- (S4) the right PC tail block. -/
lemma env_sum_tailR (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) (N : ℕ) (hs : Fz.step N ≤ 1) (Ck : ℝ) :
    ∑ n ∈ rowsOf N, (if |uNode (Fz.step N) n - CL.uc p| < CL.η / 2 ∧ rhoWin (CL.aOf p X N) < CL.Zof p X N n then
        (Ck * CPC * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) *
          (Eminus (CL.aOf p X N) (-CL.Zof p X N n) * Mbal (CL.aOf p X N) (CL.Zof p X N n))) ^ 2 else 0) ≤
      Ck ^ 2 * (CPC ^ 2 * (3 + 4 / CR.dm)) * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2) := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hdm := CR.consts_pos.2.2.1
  rw [← Finset.sum_filter, rpow_half_eq hh0]
  set T := |CL.lamL p X N| / kappaBal (CL.aOf p X N) with hT
  have e1 : ∑ n ∈ (rowsOf N).filter (fun n => |uNode (Fz.step N) n - CL.uc p| < CL.η / 2 ∧ rhoWin (CL.aOf p X N) < CL.Zof p X N n),
      (Ck * CPC * T * (Eminus (CL.aOf p X N) (-CL.Zof p X N n) * Mbal (CL.aOf p X N) (CL.Zof p X N n))) ^ 2 =
      (Ck * CPC * T) ^ 2 * ∑ n ∈ (rowsOf N).filter (fun n => |uNode (Fz.step N) n - CL.uc p| < CL.η / 2 ∧ rhoWin (CL.aOf p X N) < CL.Zof p X N n),
        (Eminus (CL.aOf p X N) (-CL.Zof p X N n) * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [e1]
  have h6 := pc_tail_right hM hp hX N
  have hsq : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hs1 : Real.sqrt (Fz.step N) ≤ 1 := Real.sqrt_le_one.mpr hs
  have h7 := real_tail CR.dm _ _ hdm (by positivity) (cube_inv_le_one (CL.aOf p X N)) hsq hs1
  calc (Ck * CPC * T) ^ 2 * _ ≤ (Ck * CPC * T) ^ 2 * ((3 + 4 / CR.dm) * (Real.sqrt (Fz.step N))⁻¹) :=
        mul_le_mul_of_nonneg_left (h6.trans h7) (sq_nonneg _)
    _ = Ck ^ 2 * (CPC ^ 2 * (3 + 4 / CR.dm)) * T ^ 2 * (Real.sqrt (Fz.step N))⁻¹ := by ring

/-- (S5) the right Weber block. -/
lemma env_sum_weberR (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) :
    ∃ A h0 : ℝ, 0 < h0 ∧ 0 ≤ A ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ Ck : ℝ,
      ∀ ψ' : ℤ → ℝ, JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR ψ' → ψ' 0 = CR.psiHatL p X N 0 →
        |softKappa CL CR p X N * CR.lamL p X N| ≤ Ck * |CL.lamL p X N| →
        ∑ n ∈ rowsOf N, (if CL.uc p + CL.η / 2 ≤ uNode (Fz.step N) n then
          (|softKappa CL CR p X N| * softEnvWeb CR p X N ((N : ℤ) - n)) ^ 2 else 0) ≤
          A * Ck ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2) := by
  obtain ⟨Cw2, cw2, h2, h2p, hcw2, W2⟩ := weber_tail_right hM hf hm hLm
  refine ⟨max Cw2 0, min h2 1, lt_min h2p one_pos, le_max_right _ _, ?_⟩
  intro p hp N hN hstep X hX Ck ψ' hJR hsR hk
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs4 : Fz.step N ≤ 1 := hstep.trans (min_le_right _ _)
  have hone : 1 ≤ Fz.step N ^ (-(1 : ℝ) / 2) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh0 hs4 (by norm_num)
  rw [← Finset.sum_filter]
  have h6 := W2 p hp N hN (hstep.trans (min_le_left _ _)) X hX Ck ψ' hJR hsR hk
  refine h6.trans ?_
  have hex : Real.exp (-(cw2 / Fz.step N)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ cw2 / Fz.step N := div_nonneg hcw2.le hh0.le
    linarith)
  have hex0 := Real.exp_pos (-(cw2 / Fz.step N))
  have hT2 := sq_nonneg (|CL.lamL p X N| / kappaBal (CL.aOf p X N))
  have hC2 := sq_nonneg Ck
  have hB : 0 ≤ max Cw2 0 * Ck ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 :=
    mul_nonneg (mul_nonneg (le_max_right _ _) hC2) hT2
  calc Cw2 * Ck ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Real.exp (-(cw2 / Fz.step N))
      ≤ max Cw2 0 * Ck ^ 2 * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hC2) hT2) hex hex0.le hB
    _ ≤ _ := by
        rw [mul_one]
        exact le_mul_of_one_le_right hB hone

/-- **T4: the envelope sum** (`app_thmA` Step 4 (d)): `sum V_n^2 <= (C_0 + C_1 C_k^2) (|lam_L|/kappa_b)^2 h^{-1/2}`. -/
theorem soft_env_sum (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (aplus : ℝ) :
    ∃ C0 C1 h0 : ℝ, 0 < h0 ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      CL.aOf p X N ≤ aplus → ∀ Ck : ℝ, 0 ≤ Ck →
      ∀ ψL ψ' : ℤ → ℝ, JacSol Fz p N X (CL.chain p X N).NR ψL → ψL 0 = CL.psiHatL p X N 0 →
        JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR ψ' → ψ' 0 = CR.psiHatL p X N 0 →
        |softKappa CL CR p X N * CR.lamL p X N| ≤ Ck * |CL.lamL p X N| →
        ∑ n ∈ rowsOf N, softEnvNum CL CR p X N n ^ 2 ≤
          (C0 + C1 * Ck ^ 2) * (|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2) := by
  obtain ⟨A1, h1, h1p, hA1, S1⟩ := env_sum_weberL CL hf hm hLm
  obtain ⟨A2, h2, h2p, hA2, S2⟩ := env_sum_window CL hf aplus
  obtain ⟨A5, h5, h5p, hA5, S5⟩ := env_sum_weberR CL CR hM hf hm hLm
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  have hdm := CL.consts_pos.2.2.1
  have hdmR := CR.consts_pos.2.2.1
  refine ⟨A1 + A2 + CPC ^ 2 * (3 + 4 / CL.dm), A2 + CPC ^ 2 * (3 + 4 / CR.dm) + A5,
    min (min h1 h2) (min h5 1), lt_min (lt_min h1p h2p) (lt_min h5p one_pos), by positivity,
    by positivity, ?_⟩
  intro p hp N hN hstep X hX ha Ck hCk ψL ψ' hJL hsL hJR hsR hk
  have hs1 : Fz.step N ≤ h1 := (hstep.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hs2 : Fz.step N ≤ h2 := (hstep.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hs5 : Fz.step N ≤ h5 := (hstep.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs4 : Fz.step N ≤ 1 := (hstep.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hpwsum := Finset.sum_le_sum (s := rowsOf N) (fun n hn => soft_env_pw CL CR hf aplus hp hX ha hn hCk hk)
  simp only [Finset.sum_add_distrib] at hpwsum
  refine hpwsum.trans ?_
  have b1 := S1 p hp N hN hs1 X hX ψL hJL hsL
  have b2 := S2 p hp N hN hs2 X hX ha Ck hCk
  have b3 := env_sum_tailL CL hf hp hX N hs4
  have b4 := env_sum_tailR CL CR hM hf hp hX N hs4 Ck
  have b5 := S5 p hp N hN hs5 X hX Ck ψ' hJR hsR hk
  set T := |CL.lamL p X N| / kappaBal (CL.aOf p X N) with hT
  set E := Fz.step N ^ (-(1 : ℝ) / 2) with hE
  have hfin : (A1 + A2 + CPC ^ 2 * (3 + 4 / CL.dm) + (A2 + CPC ^ 2 * (3 + 4 / CR.dm) + A5) * Ck ^ 2) * T ^ 2 * E =
      A1 * T ^ 2 * E + A2 * (1 + Ck ^ 2) * T ^ 2 * E + CPC ^ 2 * (3 + 4 / CL.dm) * T ^ 2 * E +
        Ck ^ 2 * (CPC ^ 2 * (3 + 4 / CR.dm)) * T ^ 2 * E + A5 * Ck ^ 2 * T ^ 2 * E := by ring
  rw [hfin]
  linarith

end Sum

section L2

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- **`prop:tha-W2` (2), the `l^2` bound `sum V_n^2 / hat N^2 <= C`** (T4 divided by the window-mass lower bound for `hat N`). -/
theorem soft_env_l2 (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (aplus : ℝ) :
    ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      CL.aOf p X N ≤ aplus →
      ∀ (ψL ψ' : ℤ → ℝ) (κ : ℝ),
        JacSol Fz p N X (CL.chain p X N).NR ψL → ψL 0 = CL.psiHatL p X N 0 →
        JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR ψ' → ψ' 0 = CR.psiHatL p X N 0 →
        (∀ n ∈ rowsOf N, ψL n = κ * ψ' ((N : ℤ) - n)) →
        ∑ n ∈ rowsOf N, softEnv CL CR p X N n ^ 2 ≤ Cc := by
  obtain ⟨Ck, Dk, cn, h0a, h0ap, hCk, hDk, hcn, Hm⟩ := soft_match CL CR hf hm hLm hM aplus
  obtain ⟨C0, C1, h0b, h0bp, hC0, hC1, Hs⟩ := soft_env_sum CL CR hM hf hm hLm aplus
  obtain ⟨Cc1, h0c, clam, Clam, h0cp, hclam, H1⟩ := propThaW2_item1 CL hf hm hLm
  refine ⟨(C0 + C1 * ((1 + Dk) * Ck) ^ 2) / cn, min (min h0a h0b) h0c, lt_min (lt_min h0ap h0bp) h0cp, ?_⟩
  intro p hp N hN hstep X hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  have hsa : Fz.step N ≤ h0a := (hstep.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hsb : Fz.step N ≤ h0b := (hstep.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hsc : Fz.step N ≤ h0c := hstep.trans (min_le_right _ _)
  obtain ⟨-, -, -, h4, h5⟩ := Hm p hp N hN hsa X hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  have hk : |softKappa CL CR p X N * CR.lamL p X N| ≤ ((1 + Dk) * Ck) * |CL.lamL p X N| := by
    rw [abs_mul]; exact h4
  have hCk' : 0 ≤ (1 + Dk) * Ck := by positivity
  have hSum := Hs p hp N hN hsb X hX ha ((1 + Dk) * Ck) hCk' ψL ψ' hJL hsL hJR hsR hk
  -- `lam_L ≠ 0`
  obtain ⟨-, hlow, -⟩ := H1 p hp N hN hsc X hX
  have hκ := kappaBal_pos (CL.aOf p X N)
  have hlam : 0 < |CL.lamL p X N| := by
    have h1 := softLam_pos CL p X N
    have : 0 < clam * (softLam CL p X N * kappaBal (CL.aOf p X N)) := by positivity
    linarith
  have hT : 0 < |CL.lamL p X N| / kappaBal (CL.aOf p X N) := div_pos hlam hκ
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hE : 0 < Fz.step N ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hh0 _
  set T := |CL.lamL p X N| / kappaBal (CL.aOf p X N) with hTdef
  set E := Fz.step N ^ (-(1 : ℝ) / 2) with hEdef
  have hTE : 0 < T ^ 2 * E := by positivity
  have hnorm : 0 < softNorm CL CR p X N ^ 2 := lt_of_lt_of_le (mul_pos hcn hTE) h5
  have e1 : ∑ n ∈ rowsOf N, softEnv CL CR p X N n ^ 2 = (∑ n ∈ rowsOf N, softEnvNum CL CR p X N n ^ 2) / softNorm CL CR p X N ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun n _ => by rw [softEnv_eq, div_pow])
  rw [e1, div_le_iff₀ hnorm]
  calc ∑ n ∈ rowsOf N, softEnvNum CL CR p X N n ^ 2 ≤ (C0 + C1 * ((1 + Dk) * Ck) ^ 2) * T ^ 2 * E := hSum
    _ = ((C0 + C1 * ((1 + Dk) * Ck) ^ 2) / cn) * (cn * (T ^ 2 * E)) := by field_simp
    _ ≤ ((C0 + C1 * ((1 + Dk) * Ck) ^ 2) / cn) * softNorm CL CR p X N ^ 2 := by
        apply mul_le_mul_of_nonneg_left h5 (by positivity)

end L2

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_env_pw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_env_pw

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_env_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_env_sum

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_env_l2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_env_l2

end FormalResearch.JacobiEigenvectors.TheoremA

end
