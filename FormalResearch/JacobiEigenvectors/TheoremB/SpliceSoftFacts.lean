module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftMflat
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly6

/-!
# Paper J, Theorem B, L3.1 soft (part 1): the window and row facts of one soft edge at exact solutions

Source: Paper J `app_thmB.tex`, proof of `prop:tha-splice` (b), the estimates `eq:tha-spl1`, `eq:tha-spl2` (with `eq:tha-S4env`, `eq:tha-S4mass`, Step 4 (a)--(b) of `app_thmA`).

`soft_splice_facts`: for `a <= 1`, the exact solutions `psi^L = kappa psi'(N - .)` seeded by `psi-hat_0` (data of an eigenvalue) and `T = |lambda_L| / kappa_bal(a)`, `eps = h^m Lm(h)`:
* `|softNum_n| <= C_env softEnvNum_n` on every row (the numerator of `hat Psi` against the numerator `V_n` of its envelope; `soft_row`),
* on the window `Omega`: `|psi-hat^L - hat kappa psi-hat^R| <= C_m eps T M_bal` (`eq:tha-spl1`), `|psi-hat^L| + |hat kappa||psi-hat^R| <= K T M_bal`, and `c_lb T M_bal <= softEnvNum` (both branches of the PC envelope),
* `m_Omega <= C_M h^{-1/2}`, `c_n T^2 h^{-1/2} <= hat N^2`, `T > 0`.

All from `soft_match`, `soft_win_err`/`soft_win_psihat` for both charts (mirror reflection of the window), `soft_row`, `soft_win_massw`, `molv_win_two`; no new chart hypothesis.

## Not formalised

The splice statement itself (`SpliceSoft.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Facts

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

theorem soft_splice_facts (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) :
    ∃ Cenv Cm K CM cn clb h0 : ℝ, 0 ≤ Cenv ∧ 0 ≤ Cm ∧ 0 ≤ K ∧ 0 < CM ∧ 0 < cn ∧ 0 < clb ∧ 0 < h0 ∧
      ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → CL.aOf p X N ≤ 1 →
        ∀ (ψL ψ' : ℤ → ℝ) (κ : ℝ), JacSol Fz p N X (CL.chain p X N).NR ψL → ψL 0 = CL.psiHatL p X N 0 →
          JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR ψ' → ψ' 0 = CR.psiHatL p X N 0 →
          (∀ n ∈ rowsOf N, ψL n = κ * ψ' ((N : ℤ) - n)) →
          0 < |CL.lamL p X N| / kappaBal (CL.aOf p X N) ∧
          (∀ n ∈ rowsOf N, |softNum CL CR p X N n| ≤ Cenv * softEnvNum CL CR p X N n) ∧
          (∀ n ∈ softWindow CL p X N, |CL.psiHatL p X N n - softKappa CL CR p X N * softSeqR CR p X N n| ≤
              Cm * (Fz.step N ^ m * Lm (Fz.step N)) *
                ((|CL.lamL p X N| / kappaBal (CL.aOf p X N)) * Mbal (CL.aOf p X N) (CL.Zof p X N n))) ∧
          (∀ n ∈ softWindow CL p X N, |CL.psiHatL p X N n| + |softKappa CL CR p X N| * |softSeqR CR p X N n| ≤
              K * ((|CL.lamL p X N| / kappaBal (CL.aOf p X N)) * Mbal (CL.aOf p X N) (CL.Zof p X N n))) ∧
          wmMass CL p X N ≤ CM * Fz.step N ^ (-(1 : ℝ) / 2) ∧
          cn * ((|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) ≤ softNorm CL CR p X N ^ 2 ∧
          (∀ n ∈ softWindow CL p X N, clb * ((|CL.lamL p X N| / kappaBal (CL.aOf p X N)) * Mbal (CL.aOf p X N) (CL.Zof p X N n)) ≤
              softEnvNum CL CR p X N n) := by
  obtain ⟨Ck, Dk, cn, h0a, h0ap, hCk, hDk, hcn, Hm⟩ := soft_match CL CR hf hm hLm hM 1
  obtain ⟨CcL, KeL, h0c, h0cp, hCcL, hKeL, HL⟩ := left_pw CL hf hm hLm
  obtain ⟨CcR, KeR, h0d, h0dp, hCcR, hKeR, HR⟩ := left_pw CR hf hm hLm
  obtain ⟨Cc1, h0e, clam, Clam, h0ep, hclam, H1⟩ := propThaW2_item1 CL hf hm hLm
  obtain ⟨KL, hKL, HpL⟩ := soft_win_psihat CL hf 1
  obtain ⟨KR, hKR, HpR⟩ := soft_win_psihat CR hf 1
  obtain ⟨KEL, h0f, h0fp, hKEL, HeL⟩ := soft_win_err CL hf hm hLm 1
  obtain ⟨KER, h0g, h0gp, hKER, HeR⟩ := soft_win_err CR hf hm hLm 1
  obtain ⟨cM, CM, h0h, hcM, h0hp, HM⟩ := soft_win_massw CL hf 1
  have hcPC := hf.cPC_pos
  set Cerr : ℝ := max CcL (2 * CcR + 2 * Dk * KeR) with hCerr
  set Cenv : ℝ := max KeL KeR with hCenv
  set e0 : ℝ := 1 / (2 * (Dk + 1)) with he0
  have he0p : 0 < e0 := by positivity
  set Cm : ℝ := KEL + (2 * KER + 2 * Dk * KR) * ((1 + Dk) * Ck) with hCm
  set Kk : ℝ := KL + KR * ((1 + Dk) * Ck) with hKk
  set clb : ℝ := cPC * Real.exp (-cWt 1) / (2 * Ck + 1) with hclb
  have hCm0 : 0 ≤ Cm := by positivity
  have hKk0 : 0 ≤ Kk := by positivity
  have hclb0 : 0 < clb := by positivity
  refine ⟨Cenv, Cm, Kk, |CM| + 1, cn, clb,
    min (min (min h0a h0c) (min h0d h0e)) (min (min (min (asmH0 CL) (asmH0 CR)) (min h0f h0g)) (min (min h0h CL.softH2) (softHL CL e0))),
    le_trans hKeL (le_max_left _ _), hCm0, hKk0, by positivity, hcn, hclb0,
    lt_min (lt_min (lt_min h0ap h0cp) (lt_min h0dp h0ep))
      (lt_min (lt_min (lt_min (asmH0_pos CL) (asmH0_pos CR)) (lt_min h0fp h0gp)) (lt_min (lt_min h0hp CL.softH2_pos) (softHL_pos CL e0))), ?_⟩
  intro p hp N hN hstep X hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  have hA1 := hstep.trans (min_le_left _ _)
  have hA2 := hstep.trans (min_le_right _ _)
  have sa : Fz.step N ≤ h0a := hA1.trans ((min_le_left _ _).trans (min_le_left _ _))
  have sc : Fz.step N ≤ h0c := hA1.trans ((min_le_left _ _).trans (min_le_right _ _))
  have sd : Fz.step N ≤ h0d := hA1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have se : Fz.step N ≤ h0e := hA1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have saL : Fz.step N ≤ asmH0 CL := hA2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have saR : Fz.step N ≤ asmH0 CR := hA2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have sf : Fz.step N ≤ h0f := hA2.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have sg : Fz.step N ≤ h0g := hA2.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have sh : Fz.step N ≤ h0h := hA2.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have s2 : Fz.step N ≤ CL.softH2 := hA2.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have sL : Fz.step N ≤ softHL CL e0 := hA2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN2 : CR.N0 ≤ N := (le_max_right _ _).trans hN
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := s2.trans (CL.softH2_le_H1.trans CL.softH1_le_one)
  obtain ⟨hNR, hXR⟩ := mirror_ctx hM hp hX hN1
  have haR : CR.aOf p X N = CL.aOf p X N := aOf_mirror hM hp X N
  have FL : LeftFacts CL p X N ψL CcL KeL := HL p hp N hN1 sc X hX ψL hJL hsL
  have FR : LeftFacts CR p X N ψ' CcR KeR := HR p hp N hNR sd X hXR ψ' hJR hsR
  obtain ⟨h1, h2, h3, h4, h5⟩ := Hm p hp N hN1 sa X hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  have hε0 : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) := powLm_nonneg CL hh0 hh1
  have hεe0 : Fz.step N ^ m * Lm (Fz.step N) ≤ e0 := (pow_Lm_le CL hm hh0 hh1).trans (softHL_spec CL he0p hh0 sL)
  have hsm : Dk * (Fz.step N ^ m * Lm (Fz.step N)) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hεe0 hDk).trans (small_aux Dk hDk)
  -- positivity of T
  obtain ⟨-, hlow, -⟩ := H1 p hp N hN1 se X hX
  have hκ := kappaBal_pos (CL.aOf p X N)
  have hlam : 0 < |CL.lamL p X N| := by
    have h1' := softLam_pos CL p X N
    have : 0 < clam * (softLam CL p X N * kappaBal (CL.aOf p X N)) := by positivity
    linarith
  have hT : 0 < |CL.lamL p X N| / kappaBal (CL.aOf p X N) := div_pos hlam hκ
  set a := CL.aOf p X N with hadef
  set T := |CL.lamL p X N| / kappaBal a with hTdef
  set TR := |CR.lamL p X N| / kappaBal a with hTRdef
  set ε := Fz.step N ^ m * Lm (Fz.step N) with hεdef
  set κh := softKappa CL CR p X N with hκhdef
  have hT0 : 0 ≤ T := hT.le
  have hTR0 : 0 ≤ TR := div_nonneg (abs_nonneg _) hκ.le
  -- |kappa-hat| T_R <= (1 + Dk) Ck T
  have hk4 : |κh| * TR ≤ (1 + Dk) * Ck * T := by
    have e1 : |κh| * TR = (|κh| * |CR.lamL p X N|) / kappaBal a := by rw [hTRdef]; ring
    have e2 : (1 + Dk) * Ck * T = ((1 + Dk) * Ck * |CL.lamL p X N|) / kappaBal a := by rw [hTdef]; ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (by linarith [h4, (by ring : (1 + Dk) * Ck * |CL.lamL p X N| = (1 + Dk) * Ck * |CL.lamL p X N|)]) hκ.le
  refine ⟨hT, ?_, ?_, ?_, ?_, h5, ?_⟩
  · intro n hn
    exact (soft_row CL CR hM hf hp hX ψL ψ' κ CcL KeL CcR KeR Dk _ Cerr Cenv hrel FL FR hCcL hKeL hCcR hKeR hDk hε0 hsm h3
      (le_max_left _ _) (le_max_right _ _) (le_max_left _ _) (le_max_right _ _) rfl hn).2
  · intro n hn
    have hnrows : n ∈ rowsOf N := (Finset.mem_filter.mp hn).1
    have hnR : (N : ℤ) - n ∈ softWindow CR p X N := (window_reflect hM hp X N n).mp hn
    have hZR : CR.Zof p X N ((N : ℤ) - n) = -CL.Zof p X N n := Zof_mirror hM hp X N n
    have hLerr := HeL p hp N hN1 sf X hX ha ψL hJL hsL n hn
    have hRerr := HeR p hp N hNR sg X hXR (by rw [haR]; exact ha) ψ' hJR hsR _ hnR
    have hmst : (mirrorFamily Fz).step N = Fz.step N := rfl
    rw [haR, hZR, TheoremA.Mbal_neg, hmst] at hRerr
    rw [← hεdef] at hRerr hLerr
    have hRpsi := HpR p hp N hNR saR X hXR (by rw [haR]; exact ha) _ hnR
    rw [haR, hZR, TheoremA.Mbal_neg] at hRpsi
    have hMn0 : 0 ≤ Mbal a (CL.Zof p X N n) := Mbal_nonneg' _ _
    have he : |ψ' ((N : ℤ) - n) - CR.psiHatL p X N ((N : ℤ) - n)| ≤ KER * ε * (TR * Mbal a (CL.Zof p X N n)) :=
      le_of_le_of_eq hRerr (by ring)
    have hb : |CR.psiHatL p X N ((N : ℤ) - n)| ≤ KR * (TR * Mbal a (CL.Zof p X N n)) :=
      le_of_le_of_eq hRpsi (by ring)
    have hRA := right_alg κ κh (ψ' ((N : ℤ) - n)) (CR.psiHatL p X N ((N : ℤ) - n)) (TR * Mbal a (CL.Zof p X N n)) ε KER KR Dk
      (mul_nonneg hTR0 hMn0) hε0 hKER hKR hDk hsm h3 he hb
    have hd3 : |κh| * (TR * Mbal a (CL.Zof p X N n)) ≤ ((1 + Dk) * Ck * T) * Mbal a (CL.Zof p X N n) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hk4 hMn0
    have hfac : 0 ≤ (2 * KER + 2 * Dk * KR) * ε := by positivity
    have hd2 : |κ * ψ' ((N : ℤ) - n) - κh * CR.psiHatL p X N ((N : ℤ) - n)| ≤
        (2 * KER + 2 * Dk * KR) * ε * (((1 + Dk) * Ck * T) * Mbal a (CL.Zof p X N n)) :=
      hRA.trans (mul_le_mul_of_nonneg_left hd3 hfac)
    have hid : CL.psiHatL p X N n - κh * softSeqR CR p X N n =
        (κ * ψ' ((N : ℤ) - n) - κh * CR.psiHatL p X N ((N : ℤ) - n)) - (ψL n - CL.psiHatL p X N n) := by
      have := hrel n hnrows
      show CL.psiHatL p X N n - κh * CR.psiHatL p X N ((N : ℤ) - n) = _
      rw [this]; ring
    rw [hid]
    refine (abs_sub _ _).trans ?_
    have hLe : |ψL n - CL.psiHatL p X N n| ≤ KEL * ε * (T * Mbal a (CL.Zof p X N n)) := le_of_le_of_eq hLerr (by ring)
    calc _ ≤ (2 * KER + 2 * Dk * KR) * ε * (((1 + Dk) * Ck * T) * Mbal a (CL.Zof p X N n)) +
          KEL * ε * (T * Mbal a (CL.Zof p X N n)) := add_le_add hd2 hLe
      _ = Cm * ε * (T * Mbal a (CL.Zof p X N n)) := by rw [hCm]; ring
  · intro n hn
    have hnR : (N : ℤ) - n ∈ softWindow CR p X N := (window_reflect hM hp X N n).mp hn
    have hZR : CR.Zof p X N ((N : ℤ) - n) = -CL.Zof p X N n := Zof_mirror hM hp X N n
    have hRpsi := HpR p hp N hNR saR X hXR (by rw [haR]; exact ha) _ hnR
    rw [haR, hZR, TheoremA.Mbal_neg] at hRpsi
    have hLpsi := HpL p hp N hN1 saL X hX ha n hn
    have hMn0 : 0 ≤ Mbal a (CL.Zof p X N n) := Mbal_nonneg' _ _
    have hb : |softSeqR CR p X N n| ≤ KR * (TR * Mbal a (CL.Zof p X N n)) := le_of_le_of_eq hRpsi (by ring)
    have h1' : |κh| * |softSeqR CR p X N n| ≤ |κh| * (KR * (TR * Mbal a (CL.Zof p X N n))) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    have hd3 : |κh| * (TR * Mbal a (CL.Zof p X N n)) ≤ ((1 + Dk) * Ck * T) * Mbal a (CL.Zof p X N n) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hk4 hMn0
    calc |CL.psiHatL p X N n| + |κh| * |softSeqR CR p X N n|
        ≤ KL * T * Mbal a (CL.Zof p X N n) + |κh| * (KR * (TR * Mbal a (CL.Zof p X N n))) := add_le_add hLpsi h1'
      _ = KL * T * Mbal a (CL.Zof p X N n) + KR * (|κh| * (TR * Mbal a (CL.Zof p X N n))) := by ring
      _ ≤ KL * T * Mbal a (CL.Zof p X N n) + KR * (((1 + Dk) * Ck * T) * Mbal a (CL.Zof p X N n)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hd3 hKR)
      _ = Kk * (T * Mbal a (CL.Zof p X N n)) := by rw [hKk]; ring
  · have := (HM p hp N hN1 sh X hX ha).2
    refine this.trans ?_
    have h0 : 0 ≤ Fz.step N ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hh0.le _
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self CM]) h0
  · intro n hn
    have hcol := soft_win_loc CL hp hX saL hn
    have hη := CL.consts_pos.2.1
    have hnabs : |CL.Zof p X N n| ≤ rhoWin a := (Finset.mem_filter.mp hn).2
    have hb1 : ¬ (uNode (Fz.step N) n ≤ CL.uc p - CL.η / 2) := by
      intro h; have := abs_lt.mp hcol; linarith
    have hMn0 : 0 ≤ Mbal a (CL.Zof p X N n) := Mbal_nonneg' _ _
    have hc1 : (2 * Ck + 1) ≥ 1 := by linarith
    have hclbT : clb * (T * Mbal a (CL.Zof p X N n)) =
        (cPC * Real.exp (-cWt 1) * (|CL.lamL p X N| / (2 * Ck + 1))) * ((kappaBal a)⁻¹ * Mbal a (CL.Zof p X N n)) := by
      rw [hclb, hTdef]; field_simp
    unfold softEnvNum
    rw [if_neg hb1]
    by_cases hZ : CL.Zof p X N n ≤ 0
    · rw [if_pos hZ]
      have hmo := (molv_win_two hf 1 a (-(CL.Zof p X N n)) ha (by rw [abs_neg]; exact hnabs)).1
      rw [TheoremA.Mbal_neg] at hmo
      rw [hclbT]
      have hK0 : 0 ≤ (kappaBal a)⁻¹ * Mbal a (CL.Zof p X N n) := mul_nonneg (inv_nonneg.mpr hκ.le) hMn0
      calc (cPC * Real.exp (-cWt 1) * (|CL.lamL p X N| / (2 * Ck + 1))) * ((kappaBal a)⁻¹ * Mbal a (CL.Zof p X N n))
          ≤ (cPC * Real.exp (-cWt 1) * |CL.lamL p X N|) * ((kappaBal a)⁻¹ * Mbal a (CL.Zof p X N n)) := by
            apply mul_le_mul_of_nonneg_right _ hK0
            have : |CL.lamL p X N| / (2 * Ck + 1) ≤ |CL.lamL p X N| := div_le_self (abs_nonneg _) hc1
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ = |CL.lamL p X N| * (cPC * Real.exp (-cWt 1) * ((kappaBal a)⁻¹ * Mbal a (CL.Zof p X N n))) := by ring
        _ ≤ |CL.lamL p X N| * Molv U V a (-(CL.Zof p X N n)) := mul_le_mul_of_nonneg_left hmo (abs_nonneg _)
    · push_neg at hZ
      have hb3 : uNode (Fz.step N) n < CL.uc p + CL.η / 2 := by have := abs_lt.mp hcol; linarith
      rw [if_neg (not_le.mpr hZ), if_pos hb3]
      have hmo := (molv_win_two hf 1 a (CL.Zof p X N n) ha hnabs).1
      -- |lam_L| <= (2 Ck + 1) |kappa-hat| |lam_R|
      have hκ2 : |κ| ≤ 2 * |κh| := by
        have hh2 : Dk * ε * |κ| ≤ (1 / 2) * |κ| := mul_le_mul_of_nonneg_right hsm (abs_nonneg _)
        have := abs_sub_abs_le_abs_sub κ κh
        rw [abs_sub_comm] at this
        linarith [abs_nonneg κ]
      have hlk : |CL.lamL p X N| ≤ (2 * Ck + 1) * (|κh| * |CR.lamL p X N|) := by
        have h0 : 0 ≤ |κh| * |CR.lamL p X N| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have : Ck * (|κ| * |CR.lamL p X N|) ≤ Ck * (2 * |κh| * |CR.lamL p X N|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hκ2 (abs_nonneg _)) hCk
        calc |CL.lamL p X N| ≤ Ck * (|κ| * |CR.lamL p X N|) := h2
          _ ≤ Ck * (2 * |κh| * |CR.lamL p X N|) := this
          _ = (2 * Ck) * (|κh| * |CR.lamL p X N|) := by ring
          _ ≤ (2 * Ck + 1) * (|κh| * |CR.lamL p X N|) := mul_le_mul_of_nonneg_right (by linarith) h0
      rw [hclbT, abs_mul]
      have hK0 : 0 ≤ (kappaBal a)⁻¹ * Mbal a (CL.Zof p X N n) := mul_nonneg (inv_nonneg.mpr hκ.le) hMn0
      have hdiv : |CL.lamL p X N| / (2 * Ck + 1) ≤ |κh| * |CR.lamL p X N| := by
        rw [div_le_iff₀ (by positivity), mul_comm]; exact hlk
      calc (cPC * Real.exp (-cWt 1) * (|CL.lamL p X N| / (2 * Ck + 1))) * ((kappaBal a)⁻¹ * Mbal a (CL.Zof p X N n))
          ≤ (cPC * Real.exp (-cWt 1) * (|κh| * |CR.lamL p X N|)) * ((kappaBal a)⁻¹ * Mbal a (CL.Zof p X N n)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv (by positivity)) hK0
        _ = (|κh| * |CR.lamL p X N|) * (cPC * Real.exp (-cWt 1) * ((kappaBal a)⁻¹ * Mbal a (CL.Zof p X N n))) := by ring
        _ ≤ (|κh| * |CR.lamL p X N|) * Molv U V a (CL.Zof p X N n) :=
            mul_le_mul_of_nonneg_left hmo (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_splice_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_splice_facts

end Facts

end FormalResearch.JacobiEigenvectors.TheoremB

end
