module

public import FormalResearch.SignUncertainty.CeHbPreEdge

/-!
# Tuned Mellin–Hankel eigenfunction pair for general `ShellHBData` (`thm:ce-hb-lift`)

Second half of the dual-pair construction building on `CeHbPreEdge.lean`:

* `ceHb_tail_bound`: tail decay `O(ξ⁻¹ (log π² ξ)^{-3/2})` for `ceHbDlift ± ceHbSsrc`.
* `CeHbDualSystem D` and `ce_hb_dual_system_exists`: constructs the Hankel eigenfunction family
  `(fp K c, fm K c)` (`K ≥ K_post`, `c ≥ c_min K`) with `fm K c 0 = 0 < fp K c 0`, `0 < (fp - fm)/2`
  for all `Δ ≥ 0` (from `ceHb_preEdge_pos` + `ce_post_edge_convSource_unif` via `M_K⁻¹ * D_lift` scaling),
  and exact physical-side identity `c^{1/3} ρ₀(c ξ) (-(fp + fm)/2) = I_main[F_c] + I_dual[-S_c]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

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
  have hY_eq : (fun u : ℝ => ceHbDlift ds K c u + σ' * ceHbSsrc ds K c u) = fun u : ℝ =>
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
    have hd' : ‖(σ : ℂ) * iDual (fun u => (-(D.G (u : ℂ))).re) δ₀ 4 c ξ‖ ≤
        CXd * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
      rw [norm_mul, hσ1, one_mul]; exact hd
    simp only [Complex.neg_re] at hm hd'
    exact (norm_add_le _ _).trans ((add_le_add hm hd').trans_eq (by ring))
  have bH : ‖(αH : ℂ) * (iMain ds.S.H_N δ₀ 4 c ξ + (σ : ℂ) * iDual ds.S.H_N δ₀ 4 c ξ)‖ ≤
      |αH| * (CHm + CHd) * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    have hm := hmH ξ ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hξ)))
    have hd := hdH ξ ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hξ)))
    have hm' : ‖iMain ds.S.H_N δ₀ 4 c ξ‖ ≤ CHm * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
      rw [hHN_eq]; exact hm
    have hd' : ‖(σ : ℂ) * iDual ds.S.H_N δ₀ 4 c ξ‖ ≤ CHd * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
      rw [norm_mul, hσ1, one_mul, hHN_eq]; exact hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ((add_le_add hm' hd').trans_eq (by ring))) (abs_nonneg _)
  have bSb : ‖(αSb : ℂ) * (iMain (ceSb ds.b) δ₀ 4 c ξ + (σ : ℂ) * iDual (ceSb ds.b) δ₀ 4 c ξ)‖ ≤
      |αSb| * (CSbm + CSbd) * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    have hm := hmSb ξ ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hξ)))
    have hd := hdSb ξ ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hξ)))
    simp_rw [airySbC_re] at hm hd
    have hd' : ‖(σ : ℂ) * iDual (ceSb ds.b) δ₀ 4 c ξ‖ ≤ CSbd * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
      rw [norm_mul, hσ1, one_mul]; exact hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ((add_le_add hm hd').trans_eq (by ring))) (abs_nonneg _)
  have bG : ‖(αG : ℂ) * (iMain (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ +
        (σ : ℂ) * iDual (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ)‖ ≤
      |αG| * (CGm + CGd) * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    have hm := hmG ξ ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hξ))))
    have hd := hdG ξ ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hξ))))
    have hd' : ‖(σ : ℂ) * iDual (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ‖ ≤
        CGd * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
      rw [norm_mul, hσ1, one_mul]; exact hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ((add_le_add hm hd').trans_eq (by ring))) (abs_nonneg _)
  have bS0 : ‖(αS0 : ℂ) * (iMain (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c ξ +
        (σ : ℂ) * iDual (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c ξ)‖ ≤
      |αS0| * (CS0m + CS0d) * (ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    have hm := hmS0 ξ ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hξ))))
    have hd := hdS0 ξ ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hξ))))
    have hd' : ‖(σ : ℂ) * iDual (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c ξ‖ ≤
        CS0d * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
      rw [norm_mul, hσ1, one_mul]; exact hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ((add_le_add hm hd').trans_eq (by ring))) (abs_nonneg _)
  calc ‖_‖ = ‖(iMain (fun u => -(D.G (u : ℂ)).re) δ₀ 4 c ξ + (σ : ℂ) * iDual (fun u => -(D.G (u : ℂ)).re) δ₀ 4 c ξ) +
        (αH : ℂ) * (iMain ds.S.H_N δ₀ 4 c ξ + (σ : ℂ) * iDual ds.S.H_N δ₀ 4 c ξ) +
        (αSb : ℂ) * (iMain (ceSb ds.b) δ₀ 4 c ξ + (σ : ℂ) * iDual (ceSb ds.b) δ₀ 4 c ξ) +
        (αG : ℂ) * (iMain (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ +
          (σ : ℂ) * iDual (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ) +
        (αS0 : ℂ) * (iMain (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c ξ +
          (σ : ℂ) * iDual (convSourceFamily (3 / 4) 1 1 1 c) δ₀ 4 c ξ)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add bX bH) bSb) bG) bS0
    _ = C_tot * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by dsimp [C_tot]; ring

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
    have := ds.hm₀.trans_le ds.hM₀; have := ds.hv₀; have := ds.hγ₁; have := ds.hγ₂
    have := ds.hCX_negG_pos; have := ds.hCH_N_pos; have := ds.hCSb_pos; have := ds.hC_η; have := ds.hCg_pos
    positivity
  obtain ⟨κ₀, _, hpost_unif⟩ :=
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
    obtain ⟨U_pre, c_pre, _, hc_pre_2k, hc_pre_K, hc_pre_η, hc_pre_δ, hpre_pos⟩ :=
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
      intro c w _ hw
      have hT : 0 ≤ ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      by_cases hcond : ds.c_η ≤ c ∧ 8 * K ^ 3 ≤ c
      · have hc2k : 2000 ≤ c := ds.hc_η.trans hcond.1
        have hc0 : 0 < c := by linarith
        have hc1 : 1 ≤ c := by linarith
        have hMK_bd := ds.hM_K_bd hK1 hc2k
        have hv₀pos : 0 < ds.v₀ := by linarith [ds.hv₀]
        have hM₀pos : 0 < ds.M₀ := ds.hm₀.trans_le ds.hM₀
        have hMK_pos : 0 < ds.M_K K c := lt_of_lt_of_le (by positivity) hMK_bd.1
        have hinv_le : (ds.M_K K c)⁻¹ ≤ ds.M₀ / ds.v₀ := by
          rw [inv_eq_one_div, div_le_div_iff₀ hMK_pos hv₀pos, one_mul]
          have h1 : ds.v₀ * 1 / ds.M₀ ≤ ds.v₀ * K / ds.M₀ := by gcongr
          calc ds.v₀ = (ds.v₀ * 1 / ds.M₀) * ds.M₀ := by field_simp [hM₀pos.ne']
            _ ≤ ds.M_K K c * ds.M₀ := mul_le_mul_of_nonneg_right (h1.trans hMK_bd.1) hM₀pos.le
            _ = ds.M₀ * ds.M_K K c := mul_comm _ _
        have hKeps : K * liftEps c ≤ 1 / 2 := liftEps_mul_le_half (by linarith) hcond.2
        have hr_le : |ds.r_eta K c| ≤ ds.C_η * K := by
          have hc56 : c ^ (-(5 / 6 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
          exact (ds.hr_eta_bd hK1 hcond.1 hcond.2).trans (mul_le_of_le_one_right (by have := ds.hC_η; positivity) hc56)
        have hcKinv_le : (ds.M_K K c)⁻¹ * (K * liftEps c) ≤ ds.M₀ / ds.v₀ := by
          calc (ds.M_K K c)⁻¹ * (K * liftEps c) ≤ (ds.M₀ / ds.v₀) * (1 / 2) :=
                mul_le_mul hinv_le hKeps (by have := liftEps_pos hc0; positivity) (by positivity)
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
        have hfn : D_post c = fun u : ℝ => (ds.M_K K c)⁻¹ * (-(D.G (u : ℂ)).re +
            ((K * liftEps c * ds.γ₁) * ds.S.H_N u + ((-(K * liftEps c * ds.γ₂)) * ceSb ds.b u +
              ds.r_eta K c * (airySeedG 0 (u : ℂ)).re))) := by
          ext u; dsimp [D_post, ceHbDlift]; split_ifs; ring
        rw [hfn, airyTwistedLaplaceC_const_mul,
          airyTwistedLaplaceC_add (hUX.integrable _ hre) (((hUH.smul _).add ((hUSb.smul _).add (hUg.smul _))).integrable _ hre),
          airyTwistedLaplaceC_add ((hUH.smul _).integrable _ hre) (((hUSb.smul _).add (hUg.smul _)).integrable _ hre),
          airyTwistedLaplaceC_add ((hUSb.smul _).integrable _ hre) ((hUg.smul _).integrable _ hre),
          airyTwistedLaplaceC_const_mul, airyTwistedLaplaceC_const_mul, airyTwistedLaplaceC_const_mul,
          norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hMK_pos.le)]
        have hnorm4 : ‖airyTwistedLaplaceC (fun u => -(D.G (u : ℂ)).re) ((ceCs : ℂ) * w) +
              (((K * liftEps c * ds.γ₁ : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => ds.S.H_N u) ((ceCs : ℂ) * w) +
              (((-(K * liftEps c * ds.γ₂) : ℝ) : ℂ) * airyTwistedLaplaceC (ceSb ds.b) ((ceCs : ℂ) * w) +
              ((ds.r_eta K c : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => (airySeedG 0 (u : ℂ)).re) ((ceCs : ℂ) * w)))‖ ≤
            (ds.CX_negG + (K * liftEps c) * (ds.γ₁ * ds.CH_N + ds.γ₂ * ds.CSb) +
              |ds.r_eta K c| * ds.Cg) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
          have hKεnn : 0 ≤ K * liftEps c := by have := liftEps_pos hc0; positivity
          have hn2 : ‖((K * liftEps c * ds.γ₁ : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => ds.S.H_N u) ((ceCs : ℂ) * w)‖ ≤
              (K * liftEps c) * ds.γ₁ * (ds.CH_N * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hKεnn ds.hγ₁.le)]
            exact mul_le_mul_of_nonneg_left (ds.hCH_N w hw) (mul_nonneg hKεnn ds.hγ₁.le)
          have hn3 : ‖((-(K * liftEps c * ds.γ₂) : ℝ) : ℂ) * airyTwistedLaplaceC (ceSb ds.b) ((ceCs : ℂ) * w)‖ ≤
              (K * liftEps c) * ds.γ₂ * (ds.CSb * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (mul_nonneg hKεnn ds.hγ₂.le)]
            exact mul_le_mul_of_nonneg_left (ds.hCSb w hw) (mul_nonneg hKεnn ds.hγ₂.le)
          have hn4 : ‖((ds.r_eta K c : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => (airySeedG 0 (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤
              |ds.r_eta K c| * (ds.Cg * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (ds.hCg w hw) (abs_nonneg _)
          have htri : ‖_‖ ≤ ‖airyTwistedLaplaceC (fun u => -(D.G (u : ℂ)).re) ((ceCs : ℂ) * w)‖ +
              (‖((K * liftEps c * ds.γ₁ : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => ds.S.H_N u) ((ceCs : ℂ) * w)‖ +
              (‖((-(K * liftEps c * ds.γ₂) : ℝ) : ℂ) * airyTwistedLaplaceC (ceSb ds.b) ((ceCs : ℂ) * w)‖ +
              ‖((ds.r_eta K c : ℝ) : ℂ) * airyTwistedLaplaceC (fun u => (airySeedG 0 (u : ℂ)).re) ((ceCs : ℂ) * w)‖)) :=
            (norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))))
          calc ‖_‖ ≤ _ := htri
            _ ≤ _ := add_le_add (ds.hCX_negG w hw) (add_le_add hn2 (add_le_add hn3 hn4))
            _ = _ := by ring
        calc (ds.M_K K c)⁻¹ * ‖_‖
            ≤ (ds.M_K K c)⁻¹ * ((ds.CX_negG + (K * liftEps c) * (ds.γ₁ * ds.CH_N + ds.γ₂ * ds.CSb) +
                |ds.r_eta K c| * ds.Cg) * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hnorm4 (by positivity)
          _ = ((ds.M_K K c)⁻¹ * ds.CX_negG + ((ds.M_K K c)⁻¹ * (K * liftEps c)) * (ds.γ₁ * ds.CH_N + ds.γ₂ * ds.CSb) +
                ((ds.M_K K c)⁻¹ * |ds.r_eta K c|) * ds.Cg) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by ring
          _ ≤ ((ds.M₀ / ds.v₀) * ds.CX_negG + (ds.M₀ / ds.v₀) * (ds.γ₁ * ds.CH_N + ds.γ₂ * ds.CSb) +
                ((ds.M₀ / ds.v₀) * ds.C_η) * ds.Cg) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
              have := ds.hγ₁; have := ds.hγ₂; have := ds.hCH_N_pos; have := ds.hCSb_pos; have := ds.hCX_negG_pos; have := ds.hCg_pos
              gcongr
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
          have hε_pos := liftEps_pos hc0
          have hden : 0 < π ^ 2 * liftEps c ^ 2 := by positivity
          exact le_of_lt (lt_of_mul_lt_mul_right (by linarith : (-U_pre) * (π ^ 2 * liftEps c ^ 2) < (hbS c ξ) * (π ^ 2 * liftEps c ^ 2)) hden.le)
        have hpost_pos := hpost hc_post hξ0 hUlo
        have hδ0_c : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
        rw [show (ceBeta1 * K / 2) * liftEps c = ceBeta1 * K * liftEps c / 2 from by ring] at hpost_pos
        have hMK_bd := ds.hM_K_bd hK1 hc2k
        have hMK_pos : 0 < ds.M_K K c := lt_of_lt_of_le (by have := ds.hv₀; have := ds.hm₀.trans_le ds.hM₀; positivity) hMK_bd.1
        have hUD_c := ceHb_HasU2_Dlift ds K c
        have hDp_eq : D_post c = fun u => (ds.M_K K c)⁻¹ * ceHbDlift ds K c u := by
          ext u; simp [D_post, hc_η, hc8K]
        have hpost_scaled : 0 < (iMain (ceHbSsrc ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
            iDual (ceHbDlift ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ).re := by
          rw [hDp_eq, iDual_const_mul] at hpost_pos
          have h1 := mul_pos hMK_pos hpost_pos
          have hS_eq : ceHbSsrc ds K c = fun u => ds.M_K K c * convSourceFamily (3 / 4) 1 1 1 c u := rfl
          have hre_mul : ds.M_K K c * (iMain (convSourceFamily (3 / 4) 1 1 1 c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
                (((ds.M_K K c)⁻¹ : ℝ) : ℂ) * iDual (ceHbDlift ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ).re =
              (iMain (ceHbSsrc ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
                iDual (ceHbDlift ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ).re := by
            rw [hS_eq, iMain_const_mul, ← Complex.re_ofReal_mul]
            congr 1; push_cast; rw [mul_add]; congr 1
            have hne : (ds.M_K K c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hMK_pos.ne'
            rw [mul_inv_cancel_left₀ hne]
          linarith
        have hUS_c : HasU2 (ceHbSsrc ds K c) := ceHb_HasU2_Ssrc ds hc0
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
    have hfp_spec : ∀ {c : ℝ}, c_min ≤ c →
        IsHankelEigenfn c 1 (fp c) ∧
          (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fp c (c * ξ) : ℝ) : ℂ) =
            iMain (fun u => ceHbDlift ds K c u + ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
              (1 : ℂ) * iDual (fun u => ceHbDlift ds K c u + ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ) ∧
          ((fp c 0 : ℝ) : ℂ) =
            liftSymbol (fun u => ceHbDlift ds K c u + ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
              (1 : ℂ) * liftSymbol (fun u => ceHbDlift ds K c u + ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 0 :=
      fun {c} hc => by
        have h1 : fp c = Classical.choose (hp_ex c hc) := by dsimp [fp]; split_ifs; rfl
        rw [h1]; exact Classical.choose_spec (hp_ex c hc)
    have hfm_spec : ∀ {c : ℝ}, c_min ≤ c →
        IsHankelEigenfn c (-1) (fm c) ∧
          (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fm c (c * ξ) : ℝ) : ℂ) =
            iMain (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
              (-1 : ℂ) * iDual (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 c ξ) ∧
          ((fm c 0 : ℝ) : ℂ) =
            liftSymbol (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
              (-1 : ℂ) * liftSymbol (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 0 :=
      fun {c} hc => by
        have h1 : fm c = Classical.choose (hm_ex c hc) := by dsimp [fm]; split_ifs; rfl
        rw [h1]; exact Classical.choose_spec (hm_ex c hc)
    have hm0 : ∀ {c : ℝ}, c_min ≤ c → fm c 0 = 0 := fun {c} hc => by
      have hfm0 := (hfm_spec hc).2.2
      have hzero : liftSymbol (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4
            (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
          (-1 : ℂ) * liftSymbol (fun u => ceHbDlift ds K c u - ceHbSsrc ds K c u) (ceBeta1 * K * liftEps c / 2) 4 0 = 0 := by
        have h1 := ds.hr_eta_eq hK1 (hc_min_η.trans hc) (hc_min_K.trans hc)
        dsimp only at h1
        have hfn : (fun u : ℝ => ceHbDlift ds K c u - ceHbSsrc ds K c u) =
            fun u : ℝ => -(D.G (u : ℂ)).re + (K * liftEps c) * (ds.γ₁ * ds.S.H_N u - ds.γ₂ * ceSb ds.b u) -
              ds.M_K K c * convSourceFamily (3 / 4) 1 1 1 c u + ds.r_eta K c * (airySeedG 0 (u : ℂ)).re := by
          ext u; dsimp [ceHbDlift, ceHbSsrc]; ring
        rw [hfn, neg_one_mul, ← sub_eq_add_neg]
        exact h1
      rw [hzero] at hfm0
      exact_mod_cast hfm0
    have heq_fhat : ∀ {c Δ : ℝ}, c_min ≤ c → 0 ≤ Δ → (fp c Δ - fm c Δ) / 2 = ceHbFhat ds K c Δ := by
      intro c Δ hc hΔ
      have hc0 : 0 < c := by linarith [hc_min_2k.trans hc]
      have hUD := ceHb_HasU2_Dlift ds K c
      have hUS : HasU2 (ceHbSsrc ds K c) := ceHb_HasU2_Ssrc ds hc0
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
    have hUS : HasU2 (ceHbSsrc ds K c) := ceHb_HasU2_Ssrc ds hc0
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
    ⟨by dsimp [c_min_fn]; split_ifs; rfl, by dsimp [fp_fn]; split_ifs; rfl, by dsimp [fm_fn]; split_ifs; rfl⟩
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
