module

public import FormalResearch.SignUncertainty.CeHbDualPrep

/-!
# Tuned Mellin–Hankel eigenfunction pair for general `ShellHBData` (`thm:ce-hb-lift`)

Second half of the dual-pair construction using `CeHbDualScales` (`CeHbDualPrep.lean`):

* `ceHbFseed`, `ceHbSsrc`: the physical-side seed `F_c` and scaled convolution source `S_c = M_K S_c^{(0)}`.
* `ceHb_preEdge_pos`: pre-edge Fourier positivity `0 < fhat K c Δ` for `0 ≤ Δ ≤ (c / π²) e^{-π² U_pre ε²}`
  at any fixed `K ≥ 1`, via `ce_dual_line`, `convSource_preEdge_bounds`, `pe3OriginData_of_twoEdge`, and
  `preEdge_tangency_pos`.
* `CeHbDualSystem D` and `ce_hb_dual_system_exists`: for any `D : ShellHBData` with weak Laplace
  positivity `∀ y > 0, 0 ≤ airyLaplace (-D.G) y`, constructs the Hankel eigenfunction family
  `(fp K c, fm K c)` (`K ≥ K_post`, `c ≥ c_min K`) with `fm K c 0 = 0 < fp K c 0`, `0 < (fp - fm)/2`,
  and exact physical-side identity `c^{1/3} ρ₀(c ξ) (-(fp + fm)/2) = I_main[F_c] + I_dual[-S_c]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

noncomputable def ceHbDlift {D : ShellHBData} (ds : CeHbDualScales D) (K c u : ℝ) : ℝ :=
  -(D.G (u : ℂ)).re + (K * liftEps c) * (ds.γ₁ * ds.S.H_N u - ds.γ₂ * ceSb ds.b u) +
    ds.r_eta K c * (airySeedG 0 (u : ℂ)).re

noncomputable def ceHbSsrc {D : ShellHBData} (ds : CeHbDualScales D) (K c u : ℝ) : ℝ :=
  ds.M_K K c * convSourceFamily (3 / 4) 1 1 1 c u

noncomputable def ceHbFseed {D : ShellHBData} (ds : CeHbDualScales D) (K c u : ℝ) : ℝ :=
  ds.S.G_N u - ds.γ₁ * (K * liftEps c) * ds.S.H_N u + ds.γ₂ * (K * liftEps c) * ceSb ds.b u +
    (-ds.r_eta K c) * (airySeedG 0 (u : ℂ)).re

private noncomputable def ceHbFhat {D : ShellHBData} (ds : CeHbDualScales D) (K c Δ : ℝ) : ℝ :=
  let δ₀ := ceBeta1 * K * liftEps c / 2
  if Δ = 0 then
    (liftSymbol (ceHbSsrc ds K c) δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
      liftSymbol (ceHbDlift ds K c) δ₀ 4 0).re
  else
    admissLift c (fun ζ => liftSymbol (ceHbSsrc ds K c) δ₀ 4 (ζ / (liftEps c : ℂ)) +
      liftSymbol (ceHbDlift ds K c) δ₀ 4 ((1 - ζ) / (liftEps c : ℂ))) Δ

private lemma ceHb_GN_eq {D : ShellHBData} (ds : CeHbDualScales D) :
    ds.S.G_N = fun u : ℝ => (D.G (u : ℂ)).re := by rw [ds.hS_eq]; rfl

private lemma ceHb_HN_eq {D : ShellHBData} (ds : CeHbDualScales D) :
    ds.S.H_N = fun u : ℝ => (dslope (fun z => -D.G z) (D.tm : ℂ) (u : ℂ)).re := by rw [ds.hS_eq]; rfl

lemma ceHb_Fseed_neg_Dlift {D : ShellHBData} (ds : CeHbDualScales D) (K c : ℝ) :
    ceHbFseed ds K c = fun u => -(ceHbDlift ds K c u) := by
  ext u
  have hGN := congr_fun (ceHb_GN_eq ds) u
  dsimp [ceHbFseed, ceHbDlift]
  rw [hGN]; ring

private lemma ceHb_HasU2_Ssrc {D : ShellHBData} (ds : CeHbDualScales D) {K c : ℝ} (hc : 0 < c) :
    HasU2 (ceHbSsrc ds K c) :=
  (hasU2_convSource (by norm_num) (by norm_num) (by have := liftEps_pos hc; positivity)).smul _

private lemma ceHb_HasU2_Dlift {D : ShellHBData} (ds : CeHbDualScales D) (K c : ℝ) :
    HasU2 (ceHbDlift ds K c) := by
  have hUX : HasU2 (fun u : ℝ => -(D.G (u : ℂ)).re) := by
    simpa only [Complex.neg_re] using hasU2_of_genRational (hasGenRationalAiryCoeffs_shellHBData_negG D ds.hOdd)
  have hUH : HasU2 (fun u : ℝ => ds.S.H_N u) := by
    rw [ceHb_HN_eq ds]; exact hasU2_of_genRational (hasGenRationalAiryCoeffs_terminal_cardinal D ds.hOdd)
  have hUSb : HasU2 (ceSb ds.b) := by
    simpa only [airySbC_re] using hasU2_of_genRational (hasGenRationalAiryCoeffs_airySbC ds.b)
  have hUg : HasU2 (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) := by
    rw [airySeedG0_eq_ceG1]; exact hasU2_ceG1
  have h1 := ((hUH.smul ((K * liftEps c) * ds.γ₁)).add (hUSb.smul (-((K * liftEps c) * ds.γ₂)))).add
    (hUg.smul (ds.r_eta K c))
  convert hUX.add h1 using 1
  ext u; dsimp [ceHbDlift]; ring

private lemma ceHb_int_Dlift {D : ShellHBData} (ds : CeHbDualScales D) {K c : ℝ}
    (hK : 1 ≤ K) (hc : ds.c_η ≤ c) (hcK : 8 * K ^ 3 ≤ c) (hcδ : (K / ds.δ₁) ^ 3 ≤ c) :
    ∫ u : ℝ, ceHbDlift ds K c u = ds.v₀ * (K * liftEps c) + ds.r_eta K c := by
  have hF := (ds.hF_mass_floor hK hc hcK hcδ).1
  have hfeq : ceHbDlift ds K c = fun u => -(ds.S.G_N u - ds.γ₁ * (K * liftEps c) * ds.S.H_N u +
      ds.γ₂ * (K * liftEps c) * ceSb ds.b u + (-ds.r_eta K c) * (airySeedG 0 (u : ℂ)).re) := by
    ext u
    have hGN := congr_fun (ceHb_GN_eq ds) u
    dsimp [ceHbDlift]; rw [hGN]; ring
  rw [hfeq, integral_neg, hF.2]; ring

private lemma ceHb_tail_bound {D : ShellHBData} (ds : CeHbDualScales D) {K c : ℝ}
    (hK : 1 ≤ K) (hc2k : 2000 ≤ c) (hcK : 8 * K ^ 3 ≤ c) {σ σ' : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    let Y : ℝ → ℝ := fun u => ceHbDlift ds K c u + σ' * ceHbSsrc ds K c u
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ ξ →
      ‖iMain Y (ceBeta1 * K * liftEps c / 2) 4 c ξ +
          (σ : ℂ) * iDual Y (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ ≤
        C * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
  dsimp only
  have hc0 : 0 < c := by linarith
  have hc8 : 8 ≤ c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  set δ₀ : ℝ := ceBeta1 * K * liftEps c / 2
  have hδ0 : 0 ≤ δ₀ := by have := ceBeta1_pos; positivity
  have hδ2 : δ₀ ≤ 2 := by
    have h1 := liftEps_mul_le_half (by linarith) hcK
    have h2 := ceBeta1_lt_eight
    have hKε0 : 0 ≤ K * liftEps c := by positivity
    calc δ₀ = ceBeta1 * (K * liftEps c) / 2 := by dsimp [δ₀]; ring
      _ ≤ 8 * (1 / 2) / 2 := by gcongr
      _ = 2 := by norm_num
  have hUX : HasU2 (fun u : ℝ => -(D.G (u : ℂ)).re) := by
    simpa only [Complex.neg_re] using hasU2_of_genRational (hasGenRationalAiryCoeffs_shellHBData_negG D ds.hOdd)
  have hUH : HasU2 (fun u : ℝ => ds.S.H_N u) := by
    rw [ceHb_HN_eq ds]; exact hasU2_of_genRational (hasGenRationalAiryCoeffs_terminal_cardinal D ds.hOdd)
  have hUSb : HasU2 (ceSb ds.b) := by
    simpa only [airySbC_re] using hasU2_of_genRational (hasGenRationalAiryCoeffs_airySbC ds.b)
  have hUg : HasU2 (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) := by
    rw [airySeedG0_eq_ceG1]; exact hasU2_ceG1
  have hUS0 : HasU2 (convSourceFamily (3 / 4) 1 1 1 c) :=
    hasU2_convSource (by norm_num) (by norm_num) (by positivity)
  have htX := convTailData_of_genRational (hasGenRationalAiryCoeffs_shellHBData_negG D ds.hOdd)
    (by norm_num : 3 ≤ 4) ⟨hδ0, hδ2⟩ hc8
  have htH := convTailData_of_genRational (hasGenRationalAiryCoeffs_terminal_cardinal D ds.hOdd)
    (by norm_num : 3 ≤ 4) ⟨hδ0, hδ2⟩ hc8
  have htSb := convTailData_of_genRational (hasGenRationalAiryCoeffs_airySbC ds.b)
    (by norm_num : 3 ≤ 4) ⟨hδ0, hδ2⟩ hc8
  have htG := convTailData_of_genRational (hasGenRationalAiryCoeffs_airySeedG 0)
    (by norm_num : 3 ≤ 4) ⟨hδ0, hδ2⟩ hc8
  have htS0 : ConvTailData (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c := by
    unfold convSourceFamily
    exact convTailData_convSource (by norm_num) (by norm_num) (by positivity : 0 < (1 : ℝ) * liftEps c ^ 2)
      (by norm_num : 3 ≤ 4) hK hc2k hcK
  obtain ⟨CXm, _, ξXm, hξXm, hmX⟩ := htX.main
  obtain ⟨CXd, _, ξXd, hξXd, hdX⟩ := htX.dual
  obtain ⟨CHm, _, ξHm, hξHm, hmH⟩ := htH.main
  obtain ⟨CHd, _, ξHd, hξHd, hdH⟩ := htH.dual
  obtain ⟨CSbm, _, ξSbm, hξSbm, hmSb⟩ := htSb.main
  obtain ⟨CSbd, _, ξSbd, hξSbd, hdSb⟩ := htSb.dual
  obtain ⟨CGm, _, ξGm, hξGm, hmG⟩ := htG.main
  obtain ⟨CGd, _, ξGd, hξGd, hdG⟩ := htG.dual
  obtain ⟨CS0m, _, ξS0m, hξS0m, hmS0⟩ := htS0.main
  obtain ⟨CS0d, _, ξS0d, hξS0d, hdS0⟩ := htS0.dual
  let αH : ℝ := K * liftEps c * ds.γ₁
  let αSb : ℝ := -(K * liftEps c * ds.γ₂)
  let αG : ℝ := ds.r_eta K c
  let αS0 : ℝ := σ' * ds.M_K K c
  let C_tot : ℝ := (CXm + CXd) + |αH| * (CHm + CHd) + |αSb| * (CSbm + CSbd) +
    |αG| * (CGm + CGd) + |αS0| * (CS0m + CS0d)
  let ξ_tot : ℝ := max (max (max ξXm ξXd) (max ξHm ξHd))
    (max (max ξSbm ξSbd) (max (max ξGm ξGd) (max ξS0m ξS0d)))
  have hξ_tot : 0 < ξ_tot := lt_max_of_lt_left (lt_max_of_lt_left (lt_max_of_lt_left hξXm))
  refine ⟨C_tot, by positivity, ξ_tot, hξ_tot, fun ξ hξ => ?_⟩
  have hξ0 : 0 < ξ := lt_of_lt_of_le hξ_tot hξ
  have hσ1 : ‖(σ : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; rcases hσ with rfl | rfl <;> simp
  have hHN_eq := ceHb_HN_eq ds
  have hY_eq : (fun u => ceHbDlift ds K c u + σ' * ceHbSsrc ds K c u) = fun u =>
      (-(D.G (u : ℂ)).re + (αH * ds.S.H_N u + (αSb * ceSb ds.b u + αG * (airySeedG 0 (u : ℂ)).re))) +
        αS0 * convSourceFamily (3 / 4) 1 1 1 c u := by
    ext u; dsimp [ceHbDlift, ceHbSsrc, αH, αSb, αG, αS0]; ring
  rw [hY_eq]
  have hU123 : HasU2 (fun u => αH * ds.S.H_N u + (αSb * ceSb ds.b u + αG * (airySeedG 0 (u : ℂ)).re)) :=
    (hUH.smul _).add ((hUSb.smul _).add (hUg.smul _))
  have hiM := iMain_add (hUX.add hU123) (hUS0.smul αS0) hδ0 4 hc0 hξ0
  rw [iMain_add hUX hU123 hδ0 4 hc0 hξ0, iMain_add (hUH.smul _) ((hUSb.smul _).add (hUg.smul _)) hδ0 4 hc0 hξ0,
    iMain_add (hUSb.smul _) (hUg.smul _) hδ0 4 hc0 hξ0] at hiM
  simp only [iMain_const_mul] at hiM
  have hiD := iDual_add (hUX.add hU123) (hUS0.smul αS0) hδ0 4 hc0 hξ0
  rw [iDual_add hUX hU123 hδ0 4 hc0 hξ0, iDual_add (hUH.smul _) ((hUSb.smul _).add (hUg.smul _)) hδ0 4 hc0 hξ0,
    iDual_add (hUSb.smul _) (hUg.smul _) hδ0 4 hc0 hξ0] at hiD
  simp only [iDual_const_mul] at hiD
  rw [hiM, hiD]
  have bX : ‖iMain (fun u => -(D.G (u : ℂ)).re) δ₀ 4 c ξ + (σ : ℂ) * iDual (fun u => -(D.G (u : ℂ)).re) δ₀ 4 c ξ‖ ≤
      (CXm + CXd) * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    have hm := hmX ξ ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hξ)))
    have hd := hdX ξ ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hξ)))
    simpa only [Complex.neg_re, add_mul] using (norm_add_le _ _).trans
      (add_le_add hm (by rw [norm_mul, hσ1, one_mul]; exact hd))
  have bH : ‖(αH : ℂ) * (iMain (fun u => ds.S.H_N u) δ₀ 4 c ξ + (σ : ℂ) * iDual (fun u => ds.S.H_N u) δ₀ 4 c ξ)‖ ≤
      |αH| * (CHm + CHd) * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    have hm := hmH ξ ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hξ)))
    have hd := hdH ξ ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hξ)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hHN_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by
      rw [norm_mul, hσ1, one_mul, ← add_mul]; exact add_le_add hm hd)) (abs_nonneg _)
  have bSb : ‖(αSb : ℂ) * (iMain (ceSb ds.b) δ₀ 4 c ξ + (σ : ℂ) * iDual (ceSb ds.b) δ₀ 4 c ξ)‖ ≤
      |αSb| * (CSbm + CSbd) * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    have hm := hmSb ξ ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hξ)))
    have hd := hdSb ξ ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hξ)))
    simp_rw [airySbC_re] at hm hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by
      rw [norm_mul, hσ1, one_mul, ← add_mul]; exact add_le_add hm hd)) (abs_nonneg _)
  have bG : ‖(αG : ℂ) * (iMain (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ +
        (σ : ℂ) * iDual (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ)‖ ≤
      |αG| * (CGm + CGd) * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    have hm := hmG ξ ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hξ))))
    have hd := hdG ξ ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hξ))))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by
      rw [norm_mul, hσ1, one_mul, ← add_mul]; exact add_le_add hm hd)) (abs_nonneg _)
  have bS0 : ‖(αS0 : ℂ) * (iMain (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c ξ +
        (σ : ℂ) * iDual (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c ξ)‖ ≤
      |αS0| * (CS0m + CS0d) * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    have hm := hmS0 ξ ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hξ))))
    have hd := hdS0 ξ ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hξ))))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by
      rw [norm_mul, hσ1, one_mul, ← add_mul]; exact add_le_add hm hd)) (abs_nonneg _)
  have hre_grp : (iMain (fun u => -(D.G (u : ℂ)).re) δ₀ 4 c ξ +
        (αH : ℂ) * iMain (fun u => ds.S.H_N u) δ₀ 4 c ξ +
        ((αSb : ℂ) * iMain (ceSb ds.b) δ₀ 4 c ξ + (αG : ℂ) * iMain (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ) +
        (αS0 : ℂ) * iMain (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c ξ) +
      (σ : ℂ) * (iDual (fun u => -(D.G (u : ℂ)).re) δ₀ 4 c ξ +
        (αH : ℂ) * iDual (fun u => ds.S.H_N u) δ₀ 4 c ξ +
        ((αSb : ℂ) * iDual (ceSb ds.b) δ₀ 4 c ξ + (αG : ℂ) * iDual (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ) +
        (αS0 : ℂ) * iDual (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c ξ) =
      (iMain (fun u => -(D.G (u : ℂ)).re) δ₀ 4 c ξ + (σ : ℂ) * iDual (fun u => -(D.G (u : ℂ)).re) δ₀ 4 c ξ) +
      (αH : ℂ) * (iMain (fun u => ds.S.H_N u) δ₀ 4 c ξ + (σ : ℂ) * iDual (fun u => ds.S.H_N u) δ₀ 4 c ξ) +
      (αSb : ℂ) * (iMain (ceSb ds.b) δ₀ 4 c ξ + (σ : ℂ) * iDual (ceSb ds.b) δ₀ 4 c ξ) +
      (αG : ℂ) * (iMain (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ +
        (σ : ℂ) * iDual (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ) +
      (αS0 : ℂ) * (iMain (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c ξ +
        (σ : ℂ) * iDual (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c ξ) := by ring
  rw [hre_grp]
  have htri := (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  calc ‖_‖ ≤ _ := htri
    _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add bX bH) bSb) bG) bS0
    _ = C_tot * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by dsimp [C_tot]; ring

private lemma ceHb_preEdge_pos {D : ShellHBData} (ds : CeHbDualScales D)
    (hL : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y)
    {K : ℝ} (hK1 : 1 ≤ K) :
    ∃ U_pre c_pre : ℝ, 1 ≤ U_pre ∧ 2000 ≤ c_pre ∧ 8 * K ^ 3 ≤ c_pre ∧
      ds.c_η ≤ c_pre ∧ (K / ds.δ₁) ^ 3 ≤ c_pre ∧
      ∀ {c Δ : ℝ}, c_pre ≤ c → 0 ≤ Δ →
        Δ ≤ (c / π ^ 2) * Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ))) →
        0 < ceHbFhat ds K c Δ := by
  classical
  have hnegG_cl := hasGenRationalAiryCoeffs_shellHBData_negG D ds.hOdd
  have hHC_cl := hasGenRationalAiryCoeffs_terminal_cardinal D ds.hOdd
  have hSb_cl := hasGenRationalAiryCoeffs_airySbC ds.b
  have hg_cl := hasGenRationalAiryCoeffs_airySeedG 0
  have hUX : HasU2 (fun u : ℝ => -(D.G (u : ℂ)).re) := by
    simpa only [Complex.neg_re] using hasU2_of_genRational hnegG_cl
  have hG_int0 : ∫ u : ℝ, -(D.G (u : ℂ)).re = 0 := by
    have h1 := ds.S.integral_G; rw [ceHb_GN_eq ds] at h1; rw [integral_neg, h1, neg_zero]
  let M_r : ℝ := max (2 * ds.C_η * K) (max (2 * ds.C_η * K / ds.v₀) (2 * ds.C_η * K * (2 * ds.Cg + 1))) + 1
  have hMr_nn : 0 ≤ M_r := by have := ds.hC_η; have := ds.hv₀; have := ds.hCg_pos; positivity
  let c_dl_in : ℝ := max (max ds.c_η (8 * K ^ 3)) (max ((K / ds.δ₁) ^ 3) (M_r ^ 2))
  have hc_dl_2k : 2000 ≤ c_dl_in := ds.hc_η.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hc_dl_2 : 2 ≤ c_dl_in := by linarith
  have hr_div_le : ∀ {c : ℝ}, c_dl_in ≤ c →
      |ds.r_eta K c / liftEps c| ≤ min (1 / 2) (min (ds.v₀ / 2) (1 / (2 * ds.Cg + 1))) := by
    intro c hc
    have hc_η : ds.c_η ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
    have hc8K : 8 * K ^ 3 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
    have hc0 : 0 < c := by linarith [ds.hc_η.trans hc_η]
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    have hc_mr : M_r ^ 2 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
    have hsqrt : M_r ≤ √c := by rw [← Real.sqrt_sq hMr_nn]; exact Real.sqrt_le_sqrt hc_mr
    have hc56 : c ^ (-(5 / 6 : ℝ)) = liftEps c * c ^ (-(1 / 2 : ℝ)) := by
      unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
    have hdiv_bd : |ds.r_eta K c / liftEps c| ≤ ds.C_η * K * c ^ (-(1 / 2 : ℝ)) := by
      rw [abs_div, abs_of_pos hε0, div_le_iff₀ hε0]
      calc |ds.r_eta K c| ≤ ds.C_η * K * c ^ (-(5 / 6 : ℝ)) := ds.hr_eta_bd hK1 hc_η hc8K
        _ = (ds.C_η * K * c ^ (-(1 / 2 : ℝ))) * liftEps c := by rw [hc56]; ring
    have h_inv_s : c ^ (-(1 / 2 : ℝ)) = (√c)⁻¹ := by rw [Real.sqrt_eq_rpow, Real.rpow_neg hc0.le]
    have hsqrt_pos : 0 < √c := Real.sqrt_pos.mpr hc0
    have h12 : ds.C_η * K * c ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
      rw [h_inv_s, ← div_eq_mul_inv, div_le_iff₀ hsqrt_pos]
      have h1 : 2 * ds.C_η * K ≤ M_r := by linarith [le_max_left (2 * ds.C_η * K)
        (max (2 * ds.C_η * K / ds.v₀) (2 * ds.C_η * K * (2 * ds.Cg + 1)))]
      nlinarith [h1.trans hsqrt]
    have hv : ds.C_η * K * c ^ (-(1 / 2 : ℝ)) ≤ ds.v₀ / 2 := by
      rw [h_inv_s, ← div_eq_mul_inv, div_le_iff₀ hsqrt_pos]
      have hv_pos : 0 < ds.v₀ := by linarith [ds.hv₀]
      have h1 : 2 * ds.C_η * K / ds.v₀ ≤ M_r := by
        linarith [(le_max_left _ _).trans (le_max_right (2 * ds.C_η * K) _)]
      calc ds.C_η * K = (ds.v₀ / 2) * (2 * ds.C_η * K / ds.v₀) := by field_simp [hv_pos.ne']
        _ ≤ (ds.v₀ / 2) * √c := mul_le_mul_of_nonneg_left (h1.trans hsqrt) (by positivity)
    have hCg_le : ds.C_η * K * c ^ (-(1 / 2 : ℝ)) ≤ 1 / (2 * ds.Cg + 1) := by
      rw [h_inv_s, ← div_eq_mul_inv, div_le_iff₀ hsqrt_pos]
      have hcg_pos : 0 < 2 * ds.Cg + 1 := by linarith [ds.hCg_pos]
      have h1 : 2 * ds.C_η * K * (2 * ds.Cg + 1) ≤ M_r := by
        linarith [(le_max_right _ _).trans (le_max_right (2 * ds.C_η * K) _)]
      calc ds.C_η * K ≤ 2 * ds.C_η * K := by have := ds.hC_η; nlinarith
        _ = (1 / (2 * ds.Cg + 1)) * (2 * ds.C_η * K * (2 * ds.Cg + 1)) := by field_simp [hcg_pos.ne']
        _ ≤ (1 / (2 * ds.Cg + 1)) * √c := mul_le_mul_of_nonneg_left (h1.trans hsqrt) (by positivity)
    exact hdiv_bd.trans (le_min h12 (le_min hv hCg_le))
  let s3 : Finset (Fin 3) := Finset.univ
  let H_C : ℂ → ℂ := dslope (fun z => -D.G z) (D.tm : ℂ)
  let B3 : Fin 3 → ℂ → ℂ := ![H_C, airySbC ds.b, airySeedG 0]
  let b3₀ : Fin 3 → ℝ := ![0, ds.b, 0]
  let b3₁ : Fin 3 → ℝ := ![0, 1, 0]
  have hB3 : ∀ i ∈ s3, HasGenRationalAiryCoeffs (B3 i) (b3₀ i) (b3₁ i) := fun i _ => by
    fin_cases i <;> [exact hHC_cl; exact hSb_cl; exact hg_cl]
  let α3 : Fin 3 → ℝ → ℝ := fun i c => match i with
    | ⟨0, _⟩ => K * ds.γ₁
    | ⟨1, _⟩ => -(K * ds.γ₂)
    | ⟨2, _⟩ => ds.r_eta K c / liftEps c
  let R3 : ℝ := max (K * ds.γ₁) (max (K * ds.γ₂) 1)
  have hR3 : 0 ≤ R3 := by positivity
  have hα3 : ∀ i ∈ s3, ∀ c : ℝ, c_dl_in ≤ c → |α3 i c| ≤ R3 := fun i _ c hc => by
    fin_cases i
    · dsimp [α3]; rw [abs_of_nonneg (mul_nonneg (by linarith) ds.hγ₁.le)]; exact le_max_left _ _
    · dsimp [α3]; rw [abs_neg, abs_of_nonneg (mul_nonneg (by linarith) ds.hγ₂.le)]
      exact (le_max_left _ _).trans (le_max_right _ _)
    · dsimp [α3]
      exact ((hr_div_le hc).trans (min_le_left _ _)).trans
        ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hZ3_mass : ∀ c : ℝ, c_dl_in ≤ c →
      ds.v₀ / 2 ≤ ∫ u : ℝ, ∑ i ∈ s3, α3 i c * (B3 i (u : ℂ)).re := by
    intro c hc
    have hHN_eq := ceHb_HN_eq ds
    have hUH : HasU2 (fun u : ℝ => ds.S.H_N u) := by rw [hHN_eq]; exact hasU2_of_genRational hHC_cl
    have hUSb : HasU2 (ceSb ds.b) := by simpa only [airySbC_re] using hasU2_of_genRational hSb_cl
    have hUg : HasU2 (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) := by rw [airySeedG0_eq_ceG1]; exact hasU2_ceG1
    have intH : Integrable (fun u : ℝ => ds.S.H_N u) :=
      (Complex.reCLM.integrable_comp (hUH.integrable 0 le_rfl)).congr (ae_of_all _ fun _ => by simp)
    have intSb : Integrable (ceSb ds.b) :=
      (Complex.reCLM.integrable_comp (hUSb.integrable 0 le_rfl)).congr (ae_of_all _ fun _ => by simp)
    have intG : Integrable (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) :=
      (Complex.reCLM.integrable_comp (hUg.integrable 0 le_rfl)).congr (ae_of_all _ fun _ => by simp)
    have hsum : (fun u : ℝ => ∑ i ∈ s3, α3 i c * (B3 i (u : ℂ)).re) = fun u =>
        (K * ds.γ₁) * ds.S.H_N u + (-(K * ds.γ₂) * ceSb ds.b u +
          (ds.r_eta K c / liftEps c) * (airySeedG 0 (u : ℂ)).re) := by
      ext u; simp only [s3, Fin.sum_univ_three, B3, α3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [← congr_fun hHN_eq u, airySbC_re]; ring
    rw [hsum, integral_add (intH.const_mul _) ((intSb.const_mul _).add (intG.const_mul _)),
      integral_add (intSb.const_mul _) (intG.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul,
      ds.S.integral_H, ceSb_integral ds.b, integral_airySeedG 0]
    have hγ₁_val : ds.γ₁ * ds.S.I_N - ds.γ₂ * (1 + |airyDerivFirstZero|) = ds.v₀ := by
      rw [ds.hγ₁_eq, div_mul_cancel₀ _ ds.S.I_N_pos.ne']; ring
    have hKv : ds.v₀ ≤ K * ds.v₀ := le_mul_of_one_le_left (by linarith [ds.hv₀]) hK1
    have hrv : -(ds.v₀ / 2) ≤ ds.r_eta K c / liftEps c :=
      (abs_le.mp ((hr_div_le hc).trans ((min_le_right _ _).trans (min_le_left _ _)))).1
    linarith [show (K * ds.γ₁) * ds.S.I_N + (-(K * ds.γ₂) * (1 + |airyDerivFirstZero|)) =
      K * (ds.γ₁ * ds.S.I_N - ds.γ₂ * (1 + |airyDerivFirstZero|)) from by ring, hγ₁_val]
  have hZ3_J : ∀ c : ℝ, c_dl_in ≤ c → ∀ x ∈ Icc (ds.x₀ / 3) (2 * ds.B₀),
      1 / 2 ≤ (airyTwistedLaplaceC (fun u => ∑ i ∈ s3, α3 i c * (B3 i (u : ℂ)).re)
        ((ceCs * x : ℝ) : ℂ)).re := by
    intro c hc x hx
    have hHN_eq := ceHb_HN_eq ds
    have hx_nn : 0 ≤ x := by linarith [ds.hx₀, hx.1]
    have hre : 0 ≤ (x : ℂ).re := by simp [hx_nn]
    have hsp := airyTwistedLaplaceC_finset_sum s3 B3 b3₀ b3₁ hB3 (fun i => α3 i c) hre
    rw [show ((ceCs * x : ℝ) : ℂ) = (ceCs : ℂ) * (x : ℂ) by push_cast; ring, hsp]
    simp only [s3, Fin.sum_univ_three, B3, α3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hH_rew : airyTwistedLaplaceC (fun u : ℝ => (H_C (u : ℂ)).re) ((ceCs : ℂ) * (x : ℂ)) =
        airyTwistedLaplaceC (fun u => ds.S.H_N u) ((ceCs * x : ℝ) : ℂ) := by
      rw [hHN_eq]; push_cast; rfl
    have hSb_rew : airyTwistedLaplaceC (fun u : ℝ => (airySbC ds.b (u : ℂ)).re) ((ceCs : ℂ) * (x : ℂ)) =
        airyTwistedLaplaceC (ceSb ds.b) ((ceCs * x : ℝ) : ℂ) := by
      simp_rw [airySbC_re]; push_cast; rfl
    rw [hH_rew, hSb_rew]
    have h1 := ds.hZ0_lap x ⟨hx_nn, hx.2⟩
    have hK1_lin : 1 ≤ K * (ds.γ₁ * (airyTwistedLaplaceC (fun u => ds.S.H_N u) ((ceCs * x : ℝ) : ℂ)).re -
        ds.γ₂ * (airyTwistedLaplaceC (ceSb ds.b) ((ceCs * x : ℝ) : ℂ)).re) :=
      one_le_mul_of_one_le_of_one_le hK1 h1
    have hg_bd : |(airyTwistedLaplaceC (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) ((ceCs : ℂ) * (x : ℂ))).re| ≤
        ds.Cg := by
      have hgn := (Complex.abs_re_le_norm _).trans (ds.hCg (x : ℂ) hre)
      have hnorm : ‖1 + (x : ℂ)‖ ^ (-(5 / 2 : ℝ)) ≤ 1 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      exact hgn.trans (mul_le_of_le_one_right ds.hCg_pos.le hnorm)
    have hr_bd : |ds.r_eta K c / liftEps c| ≤ 1 / (2 * ds.Cg + 1) :=
      (hr_div_le hc).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hmul_abs : |(ds.r_eta K c / liftEps c) *
        (airyTwistedLaplaceC (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) ((ceCs : ℂ) * (x : ℂ))).re| ≤ 1 / 2 := by
      rw [abs_mul]
      calc |ds.r_eta K c / liftEps c| * |_ | ≤ (1 / (2 * ds.Cg + 1)) * ds.Cg :=
            mul_le_mul hr_bd hg_bd (abs_nonneg _) (by positivity)
        _ ≤ 1 / 2 := by
            have hcg_pos : 0 < 2 * ds.Cg + 1 := by linarith [ds.hCg_pos]
            rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hcg_pos (by norm_num : (0 : ℝ) < 2)]
            linarith [ds.hCg_pos]
    linarith [(abs_le.mp hmul_abs).1]
  have hdl := ce_dual_line hnegG_cl (by simpa only [Complex.neg_re] using hG_int0)
    (fun y hy => by simpa using hL y hy) s3 B3 b3₀ b3₁ hB3 α3 R3 c_dl_in (ds.v₀ / 2) (1 / 2)
    hR3 hc_dl_2 (by linarith [ds.hv₀]) (by norm_num) hα3 hZ3_mass
    ds.hx₀ ds.hx₀B ds.hc₁' ds.hd₀
    (fun x hx => by simpa only [Complex.neg_re] using ds.hX_small x hx)
    (fun x hx => by simpa only [Complex.neg_re] using ds.hX_tail x hx)
    hZ3_J hK1 (m := 4) (by norm_num)
  obtain ⟨c_D0, M_D, Λ_D, Λ_add_D, b_D, c_J, d_tail, K_D,
    hc_D0_ge, hM_D, hΛ_D, hΛ_add_D, hb_D, hc_J, hd_tail, hK_D,
    hWD_diff, hWD_real, hWD_nn, hWD_floor, _, hWD_tan_floor, hWD_A1, hWD_A2, hWD_bd⟩ := hdl
  obtain ⟨C_S0, M_S, Λ_S, hCS0, hM_S, hΛ_S,
    hWS0_diff, hWS0_real, hWS0_bd_full, hWS0_A1, hWS0_A2⟩ :=
    convSource_preEdge_bounds (p := 3 / 4) (γ := 1) (θ := 1) (lam := 1)
      (by norm_num) (by norm_num) one_pos zero_le_one one_pos (m := 4) (by norm_num) hK1
  let δ₀_fn : ℝ → ℝ := fun c => ceBeta1 * K * liftEps c / 2
  let M : ℝ := max M_S M_D
  let Λ : ℝ := max Λ_S Λ_D
  let Δ₁ : ℝ := preEdgeDelta1 M Λ Λ_add_D b_D
  have hM1 : 1 ≤ M := hM_S.trans (le_max_left _ _)
  have hΛ1 : 1 ≤ Λ := hΛ_S.trans (le_max_left _ _)
  have hΔ₁_pos : 0 < Δ₁ := by positivity [one_le_preEdgeDelta1 M Λ Λ_add_D b_D]
  let fhat_tang : ℝ → ℝ → ℝ := fun c Δ =>
    if Δ < Δ₁ then ceHbFhat ds K c Δ else hankelRho0 c Δ * ceHbFhat ds K c Δ
  let w_cut : ℝ := D.tm - 1
  have hw_cut : w_cut ≤ 0 := by linarith [D.tm_le_airyZero_one, airyZero_one.2]
  have hc_D0_η : ds.c_η ≤ c_D0 := ((le_max_left _ _).trans (le_max_left _ _)).trans hc_D0_ge
  have hc_D0_2k : 2000 ≤ c_D0 := ds.hc_η.trans hc_D0_η
  have hc_D0_K : 8 * K ^ 3 ≤ c_D0 := ((le_max_right _ _).trans (le_max_left _ _)).trans hc_D0_ge
  have hc_D0_δ : (K / ds.δ₁) ^ 3 ≤ c_D0 := ((le_max_left _ _).trans (le_max_right _ _)).trans hc_D0_ge
  have hMK_pos : ∀ {c : ℝ}, c_D0 ≤ c → 0 < ds.M_K K c := fun {c} hc => by
    have := (ds.hM_K_bd hK1 (hc_D0_2k.trans hc)).1
    have := ds.hv₀; have := ds.hm₀.trans_le ds.hM₀
    linarith [show 0 < ds.v₀ * K / ds.M₀ by positivity]
  let C_S_K : ℝ := (ds.v₀ * K / ds.m₀) * C_S0
  have hCS_K_pos : 0 < C_S_K := by have := ds.hv₀; have := ds.hm₀; positivity
  let W_S_scaled : ℝ → ℂ → ℂ := fun c w => liftSymbol (ceHbSsrc ds K c) (δ₀_fn c) 4 w
  have hWS_scaled_eq : ∀ c w, W_S_scaled c w =
      (ds.M_K K c : ℂ) * liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 w := fun c w => by
    dsimp [W_S_scaled, ceHbSsrc]; rw [liftSymbol_const_mul_seed]
  have hWS_bd_unif : ∀ {c : ℝ} {w : ℂ}, c_D0 ≤ c → 0 ≤ w.re → ‖W_S_scaled c w‖ ≤ C_S_K := by
    intro c w hc hw
    have hc0 : 0 < c := by linarith
    have hc8K : max 8 (8 * K ^ 3) ≤ c := max_le (by linarith) (hc_D0_K.trans hc)
    rw [hWS_scaled_eq c w, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hMK_pos hc).le]
    have h1 := hWS0_bd_full hc8K hw
    have h2 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
    have h3 : (1 + w.re) ^ (-(9 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h0 : ‖liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 w‖ ≤ C_S0 := calc
      _ ≤ C_S0 * liftEps c * (1 + w.re) ^ (-(9 / 2 : ℝ)) := h1
      _ ≤ C_S0 * 1 * 1 := by gcongr
      _ = C_S0 := by ring
    exact mul_le_mul (ds.hM_K_bd hK1 (hc_D0_2k.trans hc)).2 h0 (norm_nonneg _) (by have := ds.hv₀; have := ds.hm₀; positivity)
  have hJ₀_pos : ∀ {c : ℝ}, c_D0 ≤ c →
      (ceK * ds.v₀ / 2) * liftEps c ≤
        (liftSymbol (ceHbSsrc ds K c) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
          liftSymbol (ceHbDlift ds K c) (δ₀_fn c) 4 0).re := by
    intro c hc
    have hc0 : 0 < c := by linarith
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    have hc8K : max 8 (8 * K ^ 3) ≤ c := max_le (by linarith) (hc_D0_K.trans hc)
    have hUD := ceHb_HasU2_Dlift ds K c
    have hWD0 : liftSymbol (ceHbDlift ds K c) (δ₀_fn c) 4 0 =
        ((ceK * (ds.v₀ * (K * liftEps c) + ds.r_eta K c) : ℝ) : ℂ) := by
      rw [liftSymbol_zero_eq hUD (δ₀_fn c) 4, ceHb_int_Dlift ds hK1 (hc_D0_η.trans hc) (hc_D0_K.trans hc) (hc_D0_δ.trans hc)]
    have hWS_pos : 0 < (liftSymbol (ceHbSsrc ds K c) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)).re := by
      have h1 := (hWS0_real hc8K (Real.rpow_pos_of_pos hc0 _)).2
      rw [show ceHbSsrc ds K c = fun u => ds.M_K K c * convSourceFamily (3 / 4) 1 1 1 c u from rfl,
        liftSymbol_const_mul_seed, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_pos (hMK_pos hc) h1
    rw [Complex.add_re, hWD0, Complex.ofReal_re]
    have hr_lo : -(ds.v₀ / 2) * liftEps c ≤ ds.r_eta K c := by
      have h1 := (abs_le.mp ((hr_div_le (hc_D0_ge.trans hc)).trans ((min_le_right _ _).trans (min_le_left _ _)))).1
      rw [le_div_iff₀ hε0] at h1; linarith
    have hk0 : 0 < ceK := ceK_pos
    have hKv : ds.v₀ * liftEps c ≤ ds.v₀ * (K * liftEps c) := by
      nlinarith [mul_nonneg (show 0 ≤ ds.v₀ by linarith [ds.hv₀]) hε0.le]
    nlinarith
  let s4 : Finset (Fin 4) := Finset.univ
  let negG_C : ℂ → ℂ := fun z => -D.G z
  let B4 : Fin 4 → ℂ → ℂ := ![negG_C, H_C, airySbC ds.b, airySeedG 0]
  let b4₀ : Fin 4 → ℝ := ![-(D.P.leadingCoeff ^ 2), 0, ds.b, 0]
  let b4₁ : Fin 4 → ℝ := ![0, 0, 1, 0]
  have hB4 : ∀ i ∈ s4, HasGenRationalAiryCoeffs (B4 i) (b4₀ i) (b4₁ i) := fun i _ => by
    fin_cases i <;> [exact hnegG_cl; exact hHC_cl; exact hSb_cl; exact hg_cl]
  let α4 : Fin 4 → ℝ → ℝ := fun i c => match i with
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => (K * liftEps c) * ds.γ₁
    | ⟨2, _⟩ => -((K * liftEps c) * ds.γ₂)
    | ⟨3, _⟩ => ds.r_eta K c
  let R4 : ℝ := max 1 (max (ds.γ₁ / 2 + 1) (ds.γ₂ / 2 + 1))
  have hD4_eq : ∀ {c u : ℝ}, ceHbDlift ds K c u = ∑ i ∈ s4, α4 i c * (B4 i (u : ℂ)).re := by
    intro c u
    have hHN_eq := ceHb_HN_eq ds
    simp only [s4, Fin.sum_univ_four, B4, α4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      negG_C, Complex.neg_re]
    rw [← congr_fun hHN_eq u, airySbC_re]; dsimp [ceHbDlift]; ring
  have hα4_bd : ∀ i ∈ s4, ∀ c : ℝ, c_D0 ≤ c → |α4 i c| ≤ R4 := fun i _ c hc => by
    have hc8K := hc_D0_K.trans hc
    have hc_η := hc_D0_η.trans hc
    have hc0 : 0 < c := by linarith [ds.hc_η.trans hc_η]
    have hKeps : K * liftEps c ≤ 1 / 2 := liftEps_mul_le_half (by linarith) hc8K
    have hKε0 : 0 ≤ K * liftEps c := by have := liftEps_pos hc0; positivity
    fin_cases i
    · dsimp [α4, R4]; rw [abs_one]; exact le_max_left _ _
    · dsimp [α4, R4]; rw [abs_of_nonneg (mul_nonneg hKε0 ds.hγ₁.le)]
      exact (le_trans (by nlinarith [ds.hγ₁]) (le_max_left _ _)).trans (le_max_right _ _)
    · dsimp [α4, R4]; rw [abs_neg, abs_of_nonneg (mul_nonneg hKε0 ds.hγ₂.le)]
      exact (le_trans (by nlinarith [ds.hγ₂]) (le_max_right _ _)).trans (le_max_right _ _)
    · dsimp [α4, R4]
      exact ((ds.hr_eta_eps hK1 hc_η hc8K).trans hKeps).trans ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans (le_max_left _ _))
  have horig_raw : Nonempty (PE3OriginData (ceHbFhat ds K) (Icc 0 Δ₁)) :=
    pe3OriginData_of_twoEdge s4 B4 b4₀ b4₁ hB4 α4 (R := R4) (c_min := c_D0) (w_cut := w_cut)
      (b_J := ceK * ds.v₀ / 2) (C_S := C_S_K) (C_δ := ceBeta1 * K / 2) (Δ₁ := Δ₁)
      (by dsimp [R4]; positivity) (by linarith) hw_cut (by have := ceK_pos; have := ds.hv₀; positivity)
      hCS_K_pos.le (by have := ceBeta1_pos; positivity) hΔ₁_pos 4 (by norm_num) δ₀_fn
      (fun {c} hc => by have := ceBeta1_pos; have := liftEps_pos (by linarith : 0 < c); positivity)
      (fun {c} _ => by dsimp [δ₀_fn]; exact le_of_eq (by ring))
      (ceHbSsrc ds K) (fun {c} hc => ceHb_HasU2_Ssrc ds (by linarith))
      (fun {c w} hc hw => hWS_bd_unif hc hw)
      (ceHbDlift ds K) (fun {c u} => hD4_eq) hα4_bd
      (fun {c u} hc hu => ds.hD_neg_left hK1 (hc_D0_η.trans hc) (hc_D0_K.trans hc) (hc_D0_δ.trans hc) u hu)
      (fun {c} hc => hJ₀_pos hc) (ceHbFhat ds K) (fun {c} _ => by simp [ceHbFhat])
      (fun {c Δ} _ hΔ0 _ => by simp [ceHbFhat, hΔ0.ne'])
  obtain ⟨d_orig⟩ := horig_raw
  let d_orig_tang : PE3OriginData fhat_tang (Ico 0 Δ₁) :=
    { (d_orig.mono Ico_subset_Icc_self) with
      hat0 := fun hc _ => by dsimp [fhat_tang]; simp only [hΔ₁_pos, ↓reduceIte]; exact d_orig.hat0 hc ⟨le_rfl, hΔ₁_pos.le⟩
      h_mellin := fun hc hΔ hΔ0 => by
        dsimp [fhat_tang]; simp only [hΔ.2, ↓reduceIte]; exact d_orig.h_mellin hc ⟨hΔ.1, hΔ.2.le⟩ hΔ0 }
  have hWD_eq : ∀ {c : ℝ}, c_D0 ≤ c →
      liftSymbol (fun u => -(D.G (u : ℂ)).re + liftEps c * ∑ i ∈ s3, α3 i c * (B3 i (u : ℂ)).re)
        (ceBeta1 * K * liftEps c / 2) 4 = liftSymbol (ceHbDlift ds K c) (δ₀_fn c) 4 := by
    intro c hc
    have hε0 : (liftEps c) ≠ 0 := (liftEps_pos (by linarith [hc_D0_2k.trans hc])).ne'
    ext w
    congr 1; ext u
    simp only [s3, Fin.sum_univ_three, B3, α3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [← congr_fun (ceHb_HN_eq ds) u, airySbC_re]
    dsimp [ceHbDlift]; rw [mul_add, mul_add, mul_div_cancel₀ _ hε0]; ring
  have hd_tan : Nonempty (PreEdgeTangencyData fhat_tang) := by
    refine ⟨{
      W_S := W_S_scaled
      W_D := fun c => liftSymbol (ceHbDlift ds K c) (δ₀_fn c) 4
      c_min := c_D0
      M := M, Λ := Λ, Λ_add_max := Λ_add_D
      x₀ := ds.x₀, b := b_D, a_tan := ds.x₀ / 3, b_tan := 2 * ds.B₀
      c_J := c_J, C_S := C_S_K, K_D := K_D
      hc_min := by linarith, hM := hM1, hΛ := hΛ1, hΛ_add := hΛ_add_D
      hx₀ := ds.hx₀, hb := hb_D, ha_tan := by positivity [ds.hx₀], hab_tan := by linarith [ds.hx₀B]
      hc_J := hc_J, hCS := hCS_K_pos.le, hKD := hK_D
      hW_S_diff := fun {c} hc => by
        have hc8K : max 8 (8 * K ^ 3) ≤ c := max_le (by linarith) (hc_D0_K.trans hc)
        have hfun : W_S_scaled c = fun w => (ds.M_K K c : ℂ) * liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 w :=
          funext (hWS_scaled_eq c)
        rw [hfun]; exact (hWS0_diff hc8K).const_mul _
      hW_D_diff := fun {c} hc => by rw [← hWD_eq hc]; exact hWD_diff hc
      hW_S_real := fun {c x} hc hx => by
        have hc8K : max 8 (8 * K ^ 3) ≤ c := max_le (by linarith) (hc_D0_K.trans hc)
        rw [hWS_scaled_eq c (x : ℂ), Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          (hWS0_real hc8K hx).1]; ring
      hW_D_real := fun {c x} hc hx => by rw [← hWD_eq hc]; exact hWD_real hc hx
      hW_S_nonneg := fun {c x} hc hx _ => by
        have hc8K : max 8 (8 * K ^ 3) ≤ c := max_le (by linarith) (hc_D0_K.trans hc)
        rw [hWS_scaled_eq c (x : ℂ), Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact mul_nonneg (hMK_pos hc).le (hWS0_real hc8K hx).2.le
      hW_D_nonneg := fun {c x} hc hx hx_c => by rw [← hWD_eq hc]; exact hWD_nn hc hx hx_c
      hW0_pos := fun {c x_pos x_neg} hc hxp _ hxn hxn_c _ => by
        have hc8K : max 8 (8 * K ^ 3) ≤ c := max_le (by linarith) (hc_D0_K.trans hc)
        have hSpos : 0 < (W_S_scaled c (x_pos : ℂ)).re := by
          rw [hWS_scaled_eq c (x_pos : ℂ), Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          exact mul_pos (hMK_pos hc) (hWS0_real hc8K hxp).2
        have hDnn : 0 ≤ (liftSymbol (ceHbDlift ds K c) (δ₀_fn c) 4 (x_neg : ℂ)).re := by
          rw [← hWD_eq hc]; exact hWD_nn hc hxn hxn_c
        linarith
      hD_floor := fun {c x} hc hx hx0 hxtan => by rw [← hWD_eq hc]; exact hWD_floor hc hx hx0 hxtan
      hA1_S := fun {c x y} hc hx hx_c hy => by
        have hc8K : max 8 (8 * K ^ 3) ≤ c := max_le (by linarith) (hc_D0_K.trans hc)
        have hMK := hMK_pos hc
        have h1 := hWS0_A1 hc8K hx hx_c hy
        have hSn : 0 ≤ (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re :=
          (hWS0_real hc8K hx).2.le
        rw [hWS_scaled_eq, hWS_scaled_eq, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hMK.le,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        have hM_le : M_S ≤ M := le_max_left _ _
        calc ds.M_K K c * ‖liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 ((x : ℂ) + (y : ℂ) * Complex.I) -
              liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)‖
            ≤ ds.M_K K c * (4 * M_S * (|y| / x) * (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re) :=
              mul_le_mul_of_nonneg_left h1 hMK.le
          _ ≤ 4 * M * (|y| / x) * (ds.M_K K c * (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re) := by
              nlinarith [div_nonneg (abs_nonneg y) hx.le, mul_nonneg hMK.le hSn]
      hA1_D := fun {c x y} hc hx hx_c hxtan hy => by
        rw [← hWD_eq hc]
        have h1 := hWD_A1 hc hx hx_c hxtan hy
        have hDn := hWD_nn hc hx hx_c
        exact h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right M_S M_D) (by norm_num)) (div_nonneg (abs_nonneg y) hx.le)) hDn)
      hA2_S := fun {c x y} hc hx hx_c => by
        have hc8K : max 8 (8 * K ^ 3) ≤ c := max_le (by linarith) (hc_D0_K.trans hc)
        have hMK := hMK_pos hc
        have h1 := hWS0_A2 hc8K hx hx_c
        have hSn : 0 ≤ (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re :=
          (hWS0_real hc8K hx).2.le
        rw [hWS_scaled_eq, hWS_scaled_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hMK.le,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        have hΛ_le : Λ_S ≤ Λ := le_max_left _ _
        calc ds.M_K K c * ‖liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 ((x : ℂ) + (y : ℂ) * Complex.I)‖
            ≤ ds.M_K K c * (Λ_S * (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re) :=
              mul_le_mul_of_nonneg_left h1 hMK.le
          _ ≤ Λ * (ds.M_K K c * (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re) := by
              nlinarith [mul_nonneg hMK.le hSn]
      hA2_D := fun {c x y} hc hx hx_c hxtan => by
        rw [← hWD_eq hc]
        have h1 := hWD_A2 hc hx hx_c hxtan
        have hDn := hWD_nn hc hx hx_c
        exact h1.trans (add_le_add (mul_le_mul_of_nonneg_right (le_max_right Λ_S Λ_D) hDn) le_rfl)
      hD_tan_floor := fun {c x} hc hxtan hx_c => by rw [← hWD_eq hc]; exact hWD_tan_floor hc hxtan hx_c
      hW_S_bd := fun {c w} hc hw => hWS_bd_unif hc hw.le
      hW_D_bd := fun {c w} hc hw => by rw [← hWD_eq hc]; exact hWD_bd hc hw
      orig := d_orig_tang
      h_saddle := fun {c Δ ξ σ_star} hc hΔ1 _ hξ hσ0 hσ1 _ => by
        have hnot : ¬ (Δ < Δ₁) := not_lt.mpr hΔ1
        have hΔ0 : 0 < Δ := lt_of_lt_of_le hΔ₁_pos hΔ1
        have hc4 : 4 ≤ c := by linarith [hc_D0_2k.trans hc]
        have hc0 : 0 < c := by linarith
        have hξ0 : 0 < ξ := by rw [hξ]; exact div_pos hΔ0 hc0
        have hcξ : c * ξ = Δ := by rw [hξ]; field_simp [hc0.ne']
        have hUS_c := ceHb_HasU2_Ssrc ds hc0
        have hUD_c := ceHb_HasU2_Dlift ds K c
        have hδ0_c : 0 ≤ δ₀_fn c := by unfold δ₀_fn; have := liftEps_pos hc0; have := ceBeta1_pos; positivity
        have hsm := twoEdge_W_tilde_stripM1 (S := fun _ => ceHbSsrc ds K c) (D := fun _ => ceHbDlift ds K c)
          (δ₀ := fun _ => δ₀_fn c) (m := 4) hc4 hUS_c hUD_c hδ0_c
        have hrep := admiss_vert_rep (by linarith : 1 ≤ c) hsm hσ0.le hσ1 hξ0
        simp only [fhat_tang, ceHbFhat, hnot, hΔ0.ne', ↓reduceIte]; rw [← hcξ]
        have hre := congrArg Complex.re hrep
        rw [Complex.ofReal_re] at hre
        rw [hre]
        unfold lobeSaddleIntegral W_S_scaled
        have hε_eq : (c ^ (-(1 / 3 : ℝ)) : ℝ) = liftEps c := rfl
        simp_rw [hε_eq] }⟩
  obtain ⟨d_tan⟩ := hd_tan
  obtain ⟨U_pre, hU_pre, c_pre, hc_pre2, hpre_pos⟩ := preEdge_tangency_pos d_tan
  refine ⟨U_pre, max c_D0 c_pre, hU_pre, hc_D0_2k.trans (le_max_left _ _), hc_D0_K.trans (le_max_left _ _),
    hc_D0_η.trans (le_max_left _ _), hc_D0_δ.trans (le_max_left _ _), fun {c Δ} hc hΔ hΔ_le => ?_⟩
  have hpos_t := hpre_pos c ((le_max_right _ _).trans hc) Δ ⟨hΔ, hΔ_le⟩
  have hc0 : 0 < c := by linarith [hc_D0_2k.trans ((le_max_left _ _).trans hc)]
  dsimp [fhat_tang] at hpos_t
  by_cases hlt : Δ < Δ₁
  · simpa [hlt] using hpos_t
  · simp only [hlt, ↓reduceIte] at hpos_t
    have hΔ0 : 0 < Δ := lt_of_lt_of_le hΔ₁_pos (not_lt.mp hlt)
    exact pos_of_mul_pos_right hpos_t (hankelRho0_pos hc0 hΔ0).le

/-- Bundled dual system witness for `CeHbLift D`. -/
structure CeHbDualSystem (D : ShellHBData) where
  scales : CeHbDualScales D
  K_post : ℝ
  hK_post : 1 ≤ K_post
  c_min : ℝ → ℝ
  hc_min_2k : ∀ {K : ℝ}, K_post ≤ K → 2000 ≤ c_min K
  hc_min_K : ∀ {K : ℝ}, K_post ≤ K → 8 * K ^ 3 ≤ c_min K
  hc_min_δ : ∀ {K : ℝ}, K_post ≤ K → (K / scales.δ₁) ^ 3 ≤ c_min K
  hc_min_η : ∀ {K : ℝ}, K_post ≤ K → scales.c_η ≤ c_min K
  fp : ℝ → ℝ → ℝ → ℝ
  fm : ℝ → ℝ → ℝ → ℝ
  hp : ∀ {K c : ℝ}, K_post ≤ K → c_min K ≤ c → IsHankelEigenfn c 1 (fp K c)
  hm : ∀ {K c : ℝ}, K_post ≤ K → c_min K ≤ c → IsHankelEigenfn c (-1) (fm K c)
  hfm0 : ∀ {K c : ℝ}, K_post ≤ K → c_min K ≤ c → fm K c 0 = 0
  hfp0 : ∀ {K c : ℝ}, K_post ≤ K → c_min K ≤ c → 0 < fp K c 0
  hhat_pos : ∀ {K c Δ : ℝ}, K_post ≤ K → c_min K ≤ c → 0 ≤ Δ → 0 < (fp K c Δ - fm K c Δ) / 2
  hphys_neg_eq : ∀ {K c ξ : ℝ}, K_post ≤ K → c_min K ≤ c → 0 < ξ →
    ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * (-(fp K c (c * ξ) + fm K c (c * ξ)) / 2) : ℝ) : ℂ) =
      iMain (ceHbFseed scales K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
        iDual (fun u => -(ceHbSsrc scales K c u)) (ceBeta1 * K * liftEps c / 2) 4 c ξ

/-- Constructs `CeHbDualSystem D` from weak Laplace positivity. -/
theorem ce_hb_dual_system_exists (D : ShellHBData)
    (hL : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y) :
    Nonempty (CeHbDualSystem D) := by
  classical
  obtain ⟨ds⟩ := ceHbDualScales_exists D hL
  let CD_post : ℝ := (ds.M₀ / ds.v₀) * (ds.CX_negG + ds.γ₁ * ds.CH_N + ds.γ₂ * ds.CSb + ds.C_η * ds.Cg) + 1
  have hCD_post : 0 ≤ CD_post := by
    have := ds.hm₀.trans_le ds.hM₀; have := ds.hv₀
    have := ds.hCX_negG_pos; have := ds.hCH_N_pos; have := ds.hCSb_pos; have := ds.hC_η; have := ds.hCg_pos
    positivity
  obtain ⟨κ₀, hκ₀, hpost_unif⟩ :=
    ce_post_edge_convSource_unif (p := 3 / 4) (γ := 1) (θ := 1) (lam := 1)
      (by norm_num) (by norm_num) one_pos one_pos one_pos (m := 4) (by norm_num) hCD_post
  let K_post : ℝ := max 1 (2 * κ₀ / ceBeta1)
  have hK_post : 1 ≤ K_post := le_max_left _ _
  have hperK : ∀ K : ℝ, K_post ≤ K → ∃ (c_K : ℝ) (fp_K fm_K : ℝ → ℝ → ℝ),
      2000 ≤ c_K ∧ 8 * K ^ 3 ≤ c_K ∧ (K / ds.δ₁) ^ 3 ≤ c_K ∧ ds.c_η ≤ c_K ∧
      (∀ {c : ℝ}, c_K ≤ c → IsHankelEigenfn c 1 (fp_K c)) ∧
      (∀ {c : ℝ}, c_K ≤ c → IsHankelEigenfn c (-1) (fm_K c)) ∧
      (∀ {c : ℝ}, c_K ≤ c → fm_K c 0 = 0) ∧
      (∀ {c : ℝ}, c_K ≤ c → 0 < fp_K c 0) ∧
      (∀ {c Δ : ℝ}, c_K ≤ c → 0 ≤ Δ → 0 < (fp_K c Δ - fm_K c Δ) / 2) ∧
      (∀ {c ξ : ℝ}, c_K ≤ c → 0 < ξ →
        ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * (-(fp_K c (c * ξ) + fm_K c (c * ξ)) / 2) : ℝ) : ℂ) =
          iMain (ceHbFseed ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
            iDual (fun u => -(ceHbSsrc ds K c u)) (ceBeta1 * K * liftEps c / 2) 4 c ξ) := by
    intro K hK
    have hK1 : 1 ≤ K := hK_post.trans hK
    have hβ0 : 0 < ceBeta1 := ceBeta1_pos
    have hκ_ge : κ₀ ≤ ceBeta1 * K / 2 := by
      have hK2 : 2 * κ₀ / ceBeta1 ≤ K := (le_max_right _ _).trans hK
      calc κ₀ = ceBeta1 * (2 * κ₀ / ceBeta1) / 2 := by field_simp [hβ0.ne']
        _ ≤ ceBeta1 * K / 2 := by gcongr
    obtain ⟨U_pre, c_pre, hU_pre, hc_pre_2k, hc_pre_K, hc_pre_η, hc_pre_δ, hpre_pos⟩ :=
      ceHb_preEdge_pos ds hL hK1
    let D_post : ℝ → ℝ → ℝ := fun c u =>
      if ds.c_η ≤ c ∧ 8 * K ^ 3 ≤ c then (ds.M_K K c)⁻¹ * ceHbDlift ds K c u else 0
    have hdiff_post : ∀ {c : ℝ}, 2 ≤ c → DifferentiableOn ℂ (airyTwistedLaplaceC (D_post c)) {y : ℂ | 0 < y.re} := by
      intro c _
      by_cases hcond : ds.c_η ≤ c ∧ 8 * K ^ 3 ≤ c
      · have hfn : D_post c = fun u => (ds.M_K K c)⁻¹ * ceHbDlift ds K c u := by ext u; simp [D_post, hcond]
        rw [hfn]; exact ((ceHb_HasU2_Dlift ds K c).smul _).differentiable
      · have hfn : D_post c = fun _ => 0 := by ext u; simp [D_post, hcond]
        rw [hfn, show (fun _ : ℝ => (0 : ℝ)) = airySeedU2 0 0 0 from funext fun _ => by simp [airySeedU2]]
        exact (hasU2_airySeedU2 0 0 0).differentiable
    have hbd_post : ∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
        ‖airyTwistedLaplaceC (D_post c) ((ceCs : ℂ) * w)‖ ≤ CD_post * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
      intro c w hc hw
      have hT : 0 ≤ ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      by_cases hcond : ds.c_η ≤ c ∧ 8 * K ^ 3 ≤ c
      · have hc2k : 2000 ≤ c := ds.hc_η.trans hcond.1
        have hc0 : 0 < c := by linarith
        have hc1 : 1 ≤ c := by linarith
        have hε0 : 0 < liftEps c := liftEps_pos hc0
        have hMK_bd := ds.hM_K_bd hK1 hc2k
        have hv₀pos : 0 < ds.v₀ := by linarith [ds.hv₀]
        have hM₀pos : 0 < ds.M₀ := ds.hm₀.trans_le ds.hM₀
        have hMK_pos : 0 < ds.M_K K c := lt_of_lt_of_le (by positivity) hMK_bd.1
        have hinv_le : (ds.M_K K c)⁻¹ ≤ ds.M₀ / ds.v₀ := by
          rw [inv_le_div₀ hMK_pos]
          have h1 : ds.v₀ * 1 / ds.M₀ ≤ ds.v₀ * K / ds.M₀ := by gcongr
          calc ds.v₀ = (ds.v₀ * 1 / ds.M₀) * ds.M₀ := by field_simp [hM₀pos.ne']
            _ ≤ ds.M_K K c * ds.M₀ := mul_le_mul_of_nonneg_right (h1.trans hMK_bd.1) hM₀pos.le
        have hKeps : K * liftEps c ≤ 1 / 2 := liftEps_mul_le_half (by linarith) hcond.2
        have hr_le : |ds.r_eta K c| ≤ ds.C_η * K := by
          have hc56 : c ^ (-(5 / 6 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
          exact (ds.hr_eta_bd hK1 hcond.1 hcond.2).trans (mul_le_of_le_one_right (by have := ds.hC_η; positivity) hc56)
        have hcKinv_le : (ds.M_K K c)⁻¹ * (K * liftEps c) ≤ ds.M₀ / ds.v₀ := by
          calc (ds.M_K K c)⁻¹ * (K * liftEps c) ≤ (ds.M₀ / ds.v₀) * (1 / 2) :=
                mul_le_mul hinv_le hKeps (by positivity) (by positivity)
            _ ≤ ds.M₀ / ds.v₀ := by linarith [show 0 ≤ ds.M₀ / ds.v₀ by positivity]
        have hcr_le : (ds.M_K K c)⁻¹ * |ds.r_eta K c| ≤ (ds.M₀ / ds.v₀) * ds.C_η := by
          calc (ds.M_K K c)⁻¹ * |ds.r_eta K c|
              ≤ (ds.M₀ / (ds.v₀ * K)) * (ds.C_η * K) := by
                refine mul_le_mul ((inv_anti₀ (by positivity) hMK_bd.1).trans_eq ?_) hr_le (abs_nonneg _) (by positivity)
                rw [inv_div]
            _ = (ds.M₀ / ds.v₀) * ds.C_η := by field_simp [(by linarith : (K : ℝ) ≠ 0)]
        have hUX : HasU2 (fun u : ℝ => -(D.G (u : ℂ)).re) := by
          simpa only [Complex.neg_re] using hasU2_of_genRational (hasGenRationalAiryCoeffs_shellHBData_negG D ds.hOdd)
        have hUH : HasU2 (fun u : ℝ => ds.S.H_N u) := by
          rw [ceHb_HN_eq ds]; exact hasU2_of_genRational (hasGenRationalAiryCoeffs_terminal_cardinal D ds.hOdd)
        have hUSb : HasU2 (ceSb ds.b) := by
          simpa only [airySbC_re] using hasU2_of_genRational (hasGenRationalAiryCoeffs_airySbC ds.b)
        have hUg : HasU2 (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) := by
          rw [airySeedG0_eq_ceG1]; exact hasU2_ceG1
        have hre : 0 ≤ ((ceCs : ℂ) * w).re := by simpa [Complex.mul_re] using mul_nonneg ceCs_pos.le hw
        have hfn : D_post c = fun u => (ds.M_K K c)⁻¹ * (-(D.G (u : ℂ)).re +
            ((K * liftEps c * ds.γ₁) * ds.S.H_N u + ((-(K * liftEps c * ds.γ₂)) * ceSb ds.b u +
              ds.r_eta K c * (airySeedG 0 (u : ℂ)).re))) := by
          ext u; dsimp [D_post, ceHbDlift]; simp only [hcond, ↓reduceIte]; ring
        rw [hfn, airyTwistedLaplaceC_const_mul,
          airyTwistedLaplaceC_add (hUX.integrable _ hre) (((hUH.smul _).add ((hUSb.smul _).add (hUg.smul _))).integrable _ hre),
          airyTwistedLaplaceC_add ((hUH.smul _).integrable _ hre) (((hUSb.smul _).add (hUg.smul _)).integrable _ hre),
          airyTwistedLaplaceC_add ((hUSb.smul _).integrable _ hre) ((hUg.smul _).integrable _ hre),
          airyTwistedLaplaceC_const_mul, airyTwistedLaplaceC_const_mul, airyTwistedLaplaceC_const_mul]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hMK_pos.le)]
        have hsum := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        have hsum2 := (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        have hnorm4 : ‖airyTwistedLaplaceC (fun u => -(D.G (u : ℂ)).re) ((ceCs : ℂ) * w) +
              (((K * liftEps c * ds.γ₁ : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => ds.S.H_N u) ((ceCs : ℂ) * w) +
              (((-(K * liftEps c * ds.γ₂) : ℝ) : ℂ) * airyTwistedLaplaceC (ceSb ds.b) ((ceCs : ℂ) * w) +
              ((ds.r_eta K c : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => (airySeedG 0 (u : ℂ)).re) ((ceCs : ℂ) * w)))‖ ≤
            (ds.CX_negG + (K * liftEps c) * (ds.γ₁ * ds.CH_N + ds.γ₂ * ds.CSb) +
              |ds.r_eta K c| * ds.Cg) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
          have b1 := ds.hCX_negG w hw
          have b2 := ds.hCH_N w hw
          have b3 := ds.hCSb w hw
          have b4 := ds.hCg w hw
          have hn2 : ‖((K * liftEps c * ds.γ₁ : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => ds.S.H_N u) ((ceCs : ℂ) * w)‖ ≤
              (K * liftEps c) * ds.γ₁ * (ds.CH_N * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left b2 (by positivity)
          have hn3 : ‖((-(K * liftEps c * ds.γ₂) : ℝ) : ℂ) * airyTwistedLaplaceC (ceSb ds.b) ((ceCs : ℂ) * w)‖ ≤
              (K * liftEps c) * ds.γ₂ * (ds.CSb * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
            rw [norm_mul, Complex.norm_real, abs_neg, Real.norm_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left b3 (by positivity)
          have hn4 : ‖((ds.r_eta K c : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => (airySeedG 0 (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤
              |ds.r_eta K c| * (ds.Cg * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left b4 (abs_nonneg _)
          have htri : ‖_‖ ≤ ‖airyTwistedLaplaceC (fun u => -(D.G (u : ℂ)).re) ((ceCs : ℂ) * w)‖ +
              (‖((K * liftEps c * ds.γ₁ : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => ds.S.H_N u) ((ceCs : ℂ) * w)‖ +
              (‖((-(K * liftEps c * ds.γ₂) : ℝ) : ℂ) * airyTwistedLaplaceC (ceSb ds.b) ((ceCs : ℂ) * w)‖ +
              ‖((ds.r_eta K c : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => (airySeedG 0 (u : ℂ)).re) ((ceCs : ℂ) * w)‖)) :=
            (norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))))
          calc ‖_‖ ≤ _ := htri
            _ ≤ _ := add_le_add b1 (add_le_add hn2 (add_le_add hn3 hn4))
            _ = _ := by ring
        calc (ds.M_K K c)⁻¹ * ‖_‖
            ≤ (ds.M_K K c)⁻¹ * ((ds.CX_negG + (K * liftEps c) * (ds.γ₁ * ds.CH_N + ds.γ₂ * ds.CSb) +
                |ds.r_eta K c| * ds.Cg) * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hnorm4 (by positivity)
          _ = ((ds.M_K K c)⁻¹ * ds.CX_negG + ((ds.M_K K c)⁻¹ * (K * liftEps c)) * (ds.γ₁ * ds.CH_N + ds.γ₂ * ds.CSb) +
                ((ds.M_K K c)⁻¹ * |ds.r_eta K c|) * ds.Cg) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by ring
          _ ≤ ((ds.M₀ / ds.v₀) * ds.CX_negG + (ds.M₀ / ds.v₀) * (ds.γ₁ * ds.CH_N + ds.γ₂ * ds.CSb) +
                ((ds.M₀ / ds.v₀) * ds.C_η) * ds.Cg) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
              gcongr; positivity
          _ ≤ CD_post * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
              refine mul_le_mul_of_nonneg_right ?_ hT; dsimp [CD_post]; linarith
      · have hfn : D_post c = fun _ => 0 := by ext u; simp [D_post, hcond]
        rw [hfn, show airyTwistedLaplaceC (fun _ : ℝ => (0 : ℝ)) ((ceCs : ℂ) * w) = 0 by
          unfold airyTwistedLaplaceC; simp, norm_zero]
        exact mul_nonneg hCD_post hT
    obtain ⟨c_post, _, hpost⟩ := hpost_unif hκ_ge (by linarith : 0 ≤ U_pre) hdiff_post hbd_post
    let c_min : ℝ := max c_pre c_post
    have hc_min_2k : 2000 ≤ c_min := hc_pre_2k.trans (le_max_left _ _)
    have hc_min_K : 8 * K ^ 3 ≤ c_min := hc_pre_K.trans (le_max_left _ _)
    have hc_min_δ : (K / ds.δ₁) ^ 3 ≤ c_min := hc_pre_δ.trans (le_max_left _ _)
    have hc_min_η : ds.c_η ≤ c_min := hc_pre_η.trans (le_max_left _ _)
    have hfhat_pos : ∀ {c Δ : ℝ}, c_min ≤ c → 0 ≤ Δ → 0 < ceHbFhat ds K c Δ := by
      intro c Δ hc hΔ
      have hc_pre : c_pre ≤ c := (le_max_left _ _).trans hc
      have hc_post : c_post ≤ c := (le_max_right _ _).trans hc
      have hc2k : 2000 ≤ c := hc_min_2k.trans hc
      have hc8K : 8 * K ^ 3 ≤ c := hc_min_K.trans hc
      have hc_η : ds.c_η ≤ c := hc_min_η.trans hc
      have hc4 : 4 ≤ c := by linarith
      have hc0 : 0 < c := by linarith
      let Δ_cut : ℝ := (c / π ^ 2) * Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ)))
      rcases le_or_gt Δ Δ_cut with hΔ_le | hΔ_gt
      · exact hpre_pos hc_pre hΔ hΔ_le
      · have hΔ_cut0 : 0 ≤ Δ_cut := by dsimp [Δ_cut]; positivity
        have hΔ0 : 0 < Δ := lt_of_le_of_lt hΔ_cut0 hΔ_gt
        let ξ : ℝ := Δ / c
        have hξ0 : 0 < ξ := div_pos hΔ0 hc0
        have hcξ : c * ξ = Δ := by dsimp [ξ]; field_simp [hc0.ne']
        have hexp : Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ))) < π ^ 2 * ξ := by
          have h1 : Δ_cut * (π ^ 2 / c) = Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ))) := by
            dsimp [Δ_cut]; field_simp [hc0.ne', Real.pi_pos.ne']
          have h2 : Δ * (π ^ 2 / c) = π ^ 2 * ξ := by dsimp [ξ]; field_simp [hc0.ne']
          calc Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ))) = Δ_cut * (π ^ 2 / c) := h1.symm
            _ < Δ * (π ^ 2 / c) := mul_lt_mul_of_pos_right hΔ_gt (by positivity)
            _ = π ^ 2 * ξ := h2
        have hlog_gt : -π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ)) < Real.log (π ^ 2 * ξ) := by
          calc -π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ)) = Real.log (Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ)))) :=
                (Real.log_exp _).symm
            _ < Real.log (π ^ 2 * ξ) := Real.log_lt_log (Real.exp_pos _) hexp
        have hc23_eq : c ^ (-(2 / 3 : ℝ)) = liftEps c ^ 2 := by
          unfold liftEps; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc0.le]; norm_num
        have hUlo : -U_pre ≤ hbS c ξ := by
          rw [log_eq_hbS hc0, hc23_eq] at hlog_gt
          have hden : 0 < π ^ 2 * liftEps c ^ 2 := by positivity
          exact le_of_lt (lt_of_mul_lt_mul_right (by linarith : (-U_pre) * (π ^ 2 * liftEps c ^ 2) < (hbS c ξ) * (π ^ 2 * liftEps c ^ 2)) hden.le)
        have hpost_pos := hpost hc_post hξ0 hUlo
        have hδ0_c : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
        rw [show (ceBeta1 * K / 2) * liftEps c = ceBeta1 * K * liftEps c / 2 from by ring] at hpost_pos
        have hMK_bd := ds.hM_K_bd hK1 hc2k
        have hMK_pos : 0 < ds.M_K K c := lt_of_lt_of_le (by have := ds.hv₀; have := ds.hm₀.trans_le ds.hM₀; positivity) hMK_bd.1
        have hUS0 : HasU2 (convSourceFamily (3 / 4) 1 1 1 c) :=
          hasU2_convSource (by norm_num) (by norm_num) (by have := liftEps_pos hc0; positivity)
        have hUD_c := ceHb_HasU2_Dlift ds K c
        have hDp_eq : D_post c = fun u => (ds.M_K K c)⁻¹ * ceHbDlift ds K c u := by
          ext u; simp [D_post, hc_η, hc8K]
        have hpost_scaled : 0 < (iMain (ceHbSsrc ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
            iDual (ceHbDlift ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ).re := by
          rw [hDp_eq, iDual_const_mul] at hpost_pos
          have h1 := mul_pos hMK_pos hpost_pos
          have hS_eq : ceHbSsrc ds K c = fun u => ds.M_K K c * convSourceFamily (3 / 4) 1 1 1 c u := rfl
          have hD_inv : ceHbDlift ds K c = fun u => ds.M_K K c * ((ds.M_K K c)⁻¹ * ceHbDlift ds K c u) := by
            ext u; field_simp [hMK_pos.ne']
          have hre_mul : ds.M_K K c * (iMain (convSourceFamily (3 / 4) 1 1 1 c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
                (((ds.M_K K c)⁻¹ : ℝ) : ℂ) * iDual (ceHbDlift ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ).re =
              (iMain (ceHbSsrc ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
                iDual (ceHbDlift ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ).re := by
            rw [hS_eq, iMain_const_mul, ← Complex.re_ofReal_mul]
            congr 1; push_cast; rw [mul_add]; congr 1
            rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hMK_pos.ne', Complex.ofReal_one, one_mul]
          linarith
        have hUS_c := ceHb_HasU2_Ssrc ds hc0
        have heq := congrArg Complex.re (admissLift_twoEdge_eq hUS_c hUD_c hδ0_c 4 hc4 hξ0)
        rw [Complex.ofReal_re] at heq
        simp only [ceHbFhat, hΔ0.ne', ↓reduceIte]; rw [← hcξ]
        have hmul : 0 < c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) *
            admissLift c (fun ζ => liftSymbol (ceHbSsrc ds K c) (ceBeta1 * K * liftEps c / 2) 4 (ζ / (liftEps c : ℂ)) +
              liftSymbol (ceHbDlift ds K c) (ceBeta1 * K * liftEps c / 2) 4 ((1 - ζ) / (liftEps c : ℂ))) (c * ξ) := by
          rw [heq]; exact hpost_scaled
        exact pos_of_mul_pos_right hmul (mul_pos (Real.rpow_pos_of_pos hc0 _) (hankelRho0_pos hc0 (by positivity))).le
    have hp_ex : ∀ c : ℝ, c_min ≤ c →
        ∃ f : ℝ → ℝ, IsHankelEigenfn c 1 f ∧
          (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) : ℝ) : ℂ) =
            iMain (fun u => ceHbDlift ds K c u + ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
              (1 : ℂ) * iDual (fun u => ceHbDlift ds K c u + ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ) ∧
          ((f 0 : ℝ) : ℂ) =
            liftSymbol (fun u => ceHbDlift ds K c u + ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
              (1 : ℂ) * liftSymbol (fun u => ceHbDlift ds K c u + ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 0 := by
      intro c hc
      have hc0 : 0 < c := by linarith [hc_min_2k.trans hc]
      have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
      have htail := ceHb_tail_bound ds hK1 (hc_min_2k.trans hc) (hc_min_K.trans hc) (σ := 1) (σ' := 1) (Or.inl rfl)
      obtain ⟨f, hf, hfeq, _, hf0⟩ := exists_hankelEigenfn_lift_general
        ((ceHb_HasU2_Dlift ds K c).add (ceHb_HasU2_Ssrc ds hc0)) hδ0 4 (c := c) (by linarith) (Or.inl rfl)
        (by simpa [one_mul] using htail)
      exact ⟨f, hf, by simpa using hfeq, by simpa using hf0⟩
    have hm_ex : ∀ c : ℝ, c_min ≤ c →
        ∃ f : ℝ → ℝ, IsHankelEigenfn c (-1) f ∧
          (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) : ℝ) : ℂ) =
            iMain (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
              (-1 : ℂ) * iDual (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ) ∧
          ((f 0 : ℝ) : ℂ) =
            liftSymbol (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
              (-1 : ℂ) * liftSymbol (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 0 := by
      intro c hc
      have hc0 : 0 < c := by linarith [hc_min_2k.trans hc]
      have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
      have htail := ceHb_tail_bound ds hK1 (hc_min_2k.trans hc) (hc_min_K.trans hc) (σ := -1) (σ' := -1) (Or.inr rfl)
      have hfn : (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) = fun u => ceHbDlift ds K c u + (-1) * ceHbSsrc ds K c u := by
        ext u; ring
      obtain ⟨f, hf, hfeq, _, hf0⟩ := exists_hankelEigenfn_lift_general
        (X := fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (by rw [hfn]; exact (ceHb_HasU2_Dlift ds K c).add ((ceHb_HasU2_Ssrc ds hc0).smul (-1)))
        hδ0 4 (c := c) (by linarith) (Or.inr rfl) (by simpa [sub_eq_add_neg] using htail)
      exact ⟨f, hf, by simpa using hfeq, by simpa using hf0⟩
    let fp : ℝ → ℝ → ℝ := fun c => if hc : c_min ≤ c then Classical.choose (hp_ex c hc) else fun _ => 0
    let fm : ℝ → ℝ → ℝ := fun c => if hc : c_min ≤ c then Classical.choose (hm_ex c hc) else fun _ => 0
    have hfp_spec : ∀ {c : ℝ}, c_min ≤ c → _ := fun {c} hc => by
      have h1 : fp c = Classical.choose (hp_ex c hc) := by dsimp [fp]; exact dite_eq_left.mpr fun h => absurd hc h
      rw [h1]; exact Classical.choose_spec (hp_ex c hc)
    have hfm_spec : ∀ {c : ℝ}, c_min ≤ c → _ := fun {c} hc => by
      have h1 : fm c = Classical.choose (hm_ex c hc) := by dsimp [fm]; exact dite_eq_left.mpr fun h => absurd hc h
      rw [h1]; exact Classical.choose_spec (hm_ex c hc)
    have hm0 : ∀ {c : ℝ}, c_min ≤ c → fm c 0 = 0 := fun {c} hc => by
      have hfm0 := (hfm_spec hc).2.2
      have hzero : liftSymbol (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4
            (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
          (-1 : ℂ) * liftSymbol (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 0 = 0 := by
        have h1 := ds.hr_eta_eq hK1 (hc_min_η.trans hc) (hc_min_K.trans hc)
        convert h1 using 2 <;> ext u <;> dsimp [ceHbDlift, ceHbSsrc] <;> ring
      rw [hzero] at hfm0
      exact_mod_cast hfm0
    have heq_fhat : ∀ {c Δ : ℝ}, c_min ≤ c → 0 ≤ Δ → (fp c Δ - fm c Δ) / 2 = ceHbFhat ds K c Δ := by
      intro c Δ hc hΔ
      have hc0 : 0 < c := by linarith [hc_min_2k.trans hc]
      have hUD := ceHb_HasU2_Dlift ds K c
      have hUS := ceHb_HasU2_Ssrc ds hc0
      have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
      rcases eq_or_lt_of_le hΔ with rfl | hΔ0
      · have hfp0 := (hfp_spec hc).2.2
        have hfm0 := (hfm_spec hc).2.2
        have hxw : 0 ≤ (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ).re := by simp [(Real.rpow_pos_of_pos hc0 _).le]
        have hxm : (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) = fun u => ceHbDlift ds K c u + (-1) * ceHbSsrc ds K c u := by
          ext u; ring
        rw [liftSymbol_add_seed hUD hUS _ 4 hxw, liftSymbol_add_seed hUD hUS _ 4 le_rfl] at hfp0
        rw [hxm, liftSymbol_add_seed hUD (hUS.smul (-1)) _ 4 hxw, liftSymbol_add_seed hUD (hUS.smul (-1)) _ 4 le_rfl,
          liftSymbol_const_mul_seed, liftSymbol_const_mul_seed] at hfm0
        have hsub : (((fp c 0 - fm c 0 : ℝ)) : ℂ) =
            (2 : ℂ) * (liftSymbol (ceHbSsrc ds K c) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
              liftSymbol (ceHbDlift ds K c) (ceBeta1 * K * liftEps c / 2) 4 0) := by
          rw [Complex.ofReal_sub, hfp0, hfm0]; push_cast; ring
        have hre := congrArg Complex.re hsub
        simp only [Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
        simp only [ceHbFhat, ↓reduceIte]; linarith
      · let ξ : ℝ := Δ / c
        have hξ0 : 0 < ξ := div_pos hΔ0 hc0
        have hcξ : c * ξ = Δ := by dsimp [ξ]; field_simp [hc0.ne']
        have hfpeq := (hfp_spec hc).2.1 ξ hξ0
        have hfmeq := (hfm_spec hc).2.1 ξ hξ0
        have hxm : (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) = fun u => ceHbDlift ds K c u + (-1) * ceHbSsrc ds K c u := by
          ext u; ring
        rw [iMain_add hUD hUS hδ0 4 hc0 hξ0, iDual_add hUD hUS hδ0 4 hc0 hξ0] at hfpeq
        rw [hxm, iMain_add hUD (hUS.smul (-1)) hδ0 4 hc0 hξ0, iDual_add hUD (hUS.smul (-1)) hδ0 4 hc0 hξ0,
          iMain_const_mul, iDual_const_mul] at hfmeq
        have hdiff_c : (((c ^ (1 / 3 : ℝ) * hankelRho0 c Δ * ((fp c Δ - fm c Δ) / 2) : ℝ)) : ℂ) =
            iMain (ceHbSsrc ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
              iDual (ceHbDlift ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ := by
          have hL' : (((c ^ (1 / 3 : ℝ) * hankelRho0 c Δ * ((fp c Δ - fm c Δ) / 2) : ℝ)) : ℂ) =
              ((1 / 2 : ℝ) : ℂ) * ((((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fp c (c * ξ) : ℝ)) : ℂ) -
                (((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fm c (c * ξ) : ℝ)) : ℂ)) := by
            rw [hcξ]; push_cast; ring
          rw [hL', hfpeq, hfmeq]; push_cast; ring
        rw [← hcξ, ← admissLift_twoEdge_eq hUS hUD hδ0 4 (by linarith [hc_min_2k.trans hc]) hξ0] at hdiff_c
        have hre := congrArg Complex.re hdiff_c
        simp only [Complex.ofReal_re] at hre
        have hpos : c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) ≠ 0 :=
          (mul_pos (Real.rpow_pos_of_pos hc0 _) (hankelRho0_pos hc0 (by positivity))).ne'
        simp only [ceHbFhat, hΔ0.ne', ↓reduceIte]; rw [← hcξ]; exact mul_left_cancel₀ hpos hre
    refine ⟨c_min, fp, fm, hc_min_2k, hc_min_K, hc_min_δ, hc_min_η,
      fun hc => (hfp_spec hc).1, fun hc => (hfm_spec hc).1, hm0,
      fun {c} hc => by
        have h1 := heq_fhat hc le_rfl
        have h2 := hfhat_pos hc le_rfl
        have h3 := hm0 hc
        linarith,
      fun {c Δ} hc hΔ => by rw [heq_fhat hc hΔ]; exact hfhat_pos hc hΔ,
      fun {c ξ} hc hξ => ?_⟩
    have hc0 : 0 < c := by linarith [hc_min_2k.trans hc]
    have hUD := ceHb_HasU2_Dlift ds K c
    have hUS := ceHb_HasU2_Ssrc ds hc0
    have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    have hfpeq := (hfp_spec hc).2.1 ξ hξ
    have hfmeq := (hfm_spec hc).2.1 ξ hξ
    have hxm : (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) = fun u => ceHbDlift ds K c u + (-1) * ceHbSsrc ds K c u := by
      ext u; ring
    rw [iMain_add hUD hUS hδ0 4 hc0 hξ, iDual_add hUD hUS hδ0 4 hc0 hξ] at hfpeq
    rw [hxm, iMain_add hUD (hUS.smul (-1)) hδ0 4 hc0 hξ, iDual_add hUD (hUS.smul (-1)) hδ0 4 hc0 hξ,
      iMain_const_mul, iDual_const_mul] at hfmeq
    have hneg_F : ceHbFseed ds K c = fun u => (-1) * ceHbDlift ds K c u := by
      rw [ceHb_Fseed_neg_Dlift ds K c]; ext u; ring
    have hneg_S : (fun u => -(ceHbSsrc ds K c u)) = fun u => (-1) * ceHbSsrc ds K c u := by ext u; ring
    rw [hneg_F, hneg_S, iMain_const_mul, iDual_const_mul]
    have hL' : (((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * (-(fp c (c * ξ) + fm c (c * ξ)) / 2) : ℝ)) : ℂ) =
        ((-1 / 2 : ℝ) : ℂ) * ((((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fp c (c * ξ) : ℝ)) : ℂ) +
          (((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fm c (c * ξ) : ℝ)) : ℂ)) := by
      push_cast; ring
    rw [hL', hfpeq, hfmeq]; push_cast; ring
  let c_min_fn : ℝ → ℝ := fun K => if hK : K_post ≤ K then (hperK K hK).choose else 2000
  let fp_fn : ℝ → ℝ → ℝ → ℝ := fun K => if hK : K_post ≤ K then (hperK K hK).choose_spec.choose else fun _ _ => 0
  let fm_fn : ℝ → ℝ → ℝ → ℝ := fun K => if hK : K_post ≤ K then (hperK K hK).choose_spec.choose_spec.choose else fun _ _ => 0
  have hspec : ∀ {K : ℝ} (hK : K_post ≤ K),
      c_min_fn K = (hperK K hK).choose ∧
      fp_fn K = (hperK K hK).choose_spec.choose ∧
      fm_fn K = (hperK K hK).choose_spec.choose_spec.choose := fun hK =>
    ⟨by dsimp [c_min_fn]; exact dite_eq_left.mpr fun h => absurd hK h,
     by dsimp [fp_fn]; exact dite_eq_left.mpr fun h => absurd hK h,
     by dsimp [fm_fn]; exact dite_eq_left.mpr fun h => absurd hK h⟩
  exact ⟨{
    scales := ds
    K_post := K_post
    hK_post := hK_post
    c_min := c_min_fn
    hc_min_2k := fun hK => by rw [(hspec hK).1]; exact (hperK _ hK).choose_spec.choose_spec.choose_spec.1
    hc_min_K := fun hK => by rw [(hspec hK).1]; exact (hperK _ hK).choose_spec.choose_spec.choose_spec.2.1
    hc_min_δ := fun hK => by rw [(hspec hK).1]; exact (hperK _ hK).choose_spec.choose_spec.choose_spec.2.2.1
    hc_min_η := fun hK => by rw [(hspec hK).1]; exact (hperK _ hK).choose_spec.choose_spec.choose_spec.2.2.2.1
    fp := fp_fn
    fm := fm_fn
    hp := fun hK hc => by
      rw [(hspec hK).2.1]; rw [(hspec hK).1] at hc
      exact (hperK _ hK).choose_spec.choose_spec.choose_spec.2.2.2.2.1 hc
    hm := fun hK hc => by
      rw [(hspec hK).2.2]; rw [(hspec hK).1] at hc
      exact (hperK _ hK).choose_spec.choose_spec.choose_spec.2.2.2.2.2.1 hc
    hfm0 := fun hK hc => by
      rw [(hspec hK).2.2]; rw [(hspec hK).1] at hc
      exact (hperK _ hK).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.1 hc
    hfp0 := fun hK hc => by
      rw [(hspec hK).2.1]; rw [(hspec hK).1] at hc
      exact (hperK _ hK).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.1 hc
    hhat_pos := fun hK hc hΔ => by
      rw [(hspec hK).2.1, (hspec hK).2.2]; rw [(hspec hK).1] at hc
      exact (hperK _ hK).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2.1 hc hΔ
    hphys_neg_eq := fun hK hc hξ => by
      rw [(hspec hK).2.1, (hspec hK).2.2]; rw [(hspec hK).1] at hc
      exact (hperK _ hK).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2 hc hξ }⟩

/-- info: 'FormalResearch.SignUncertainty.ce_hb_dual_system_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ce_hb_dual_system_exists

end FormalResearch.SignUncertainty
