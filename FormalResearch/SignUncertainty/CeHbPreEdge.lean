module

public import FormalResearch.SignUncertainty.CeHbDualPrep

/-!
# Pre-edge positivity for general `ShellHBData` (`thm:ce-hb-lift`)

First half of the eigenfunction lift assembly using `CeHbDualScales` (`CeHbDualPrep.lean`):

* `ceHbDlift`, `ceHbSsrc`, `ceHbFseed`, `ceHbFhat`: the dual/physical seeds and two-edge Fourier seed.
* `ceHb_preEdge_pos`: pre-edge Fourier positivity `0 < ceHbFhat ds K c Δ` on
  `0 ≤ Δ ≤ (c / π²) e^{-π² U_pre ε²}` for any fixed `K ≥ 1`, via `ce_dual_line`,
  `convSource_preEdge_bounds`, `pe3OriginData_of_twoEdge`, and `preEdge_tangency_pos`.
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

noncomputable def ceHbFhat {D : ShellHBData} (ds : CeHbDualScales D) (K c Δ : ℝ) : ℝ :=
  let δ₀ := ceBeta1 * K * liftEps c / 2
  if Δ = 0 then
    (liftSymbol (ceHbSsrc ds K c) δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
      liftSymbol (ceHbDlift ds K c) δ₀ 4 0).re
  else
    admissLift c (fun ζ => liftSymbol (ceHbSsrc ds K c) δ₀ 4 (ζ / (liftEps c : ℂ)) +
      liftSymbol (ceHbDlift ds K c) δ₀ 4 ((1 - ζ) / (liftEps c : ℂ))) Δ

lemma ceHb_GN_eq {D : ShellHBData} (ds : CeHbDualScales D) :
    ds.S.G_N = fun u : ℝ => (D.G (u : ℂ)).re := by rw [ds.hS_eq]; rfl

lemma ceHb_HN_eq {D : ShellHBData} (ds : CeHbDualScales D) :
    ds.S.H_N = fun u : ℝ => (dslope (fun z => -D.G z) (D.tm : ℂ) (u : ℂ)).re := by rw [ds.hS_eq]; rfl

lemma ceHb_Fseed_neg_Dlift {D : ShellHBData} (ds : CeHbDualScales D) (K c : ℝ) :
    ceHbFseed ds K c = fun u => -(ceHbDlift ds K c u) := by
  ext u
  have hGN := congr_fun (ceHb_GN_eq ds) u
  dsimp [ceHbFseed, ceHbDlift]
  rw [hGN]; ring

lemma ceHb_HasU2_Ssrc {D : ShellHBData} (ds : CeHbDualScales D) {K c : ℝ} (hc : 0 < c) :
    HasU2 (ceHbSsrc ds K c) :=
  (hasU2_convSource (by norm_num) (by norm_num) (by have := liftEps_pos hc; positivity)).smul _

lemma ceHb_HasU2_Dlift {D : ShellHBData} (ds : CeHbDualScales D) (K c : ℝ) :
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

lemma ceHb_int_Dlift {D : ShellHBData} (ds : CeHbDualScales D) {K c : ℝ}
    (hK : 1 ≤ K) (hc : ds.c_η ≤ c) (hcK : 8 * K ^ 3 ≤ c) (hcδ : (K / ds.δ₁) ^ 3 ≤ c) :
    ∫ u : ℝ, ceHbDlift ds K c u = ds.v₀ * (K * liftEps c) + ds.r_eta K c := by
  have hF := (ds.hF_mass_floor hK hc hcK hcδ).1
  have hfeq : ceHbDlift ds K c = fun u => -(ds.S.G_N u - ds.γ₁ * (K * liftEps c) * ds.S.H_N u +
      ds.γ₂ * (K * liftEps c) * ceSb ds.b u + (-ds.r_eta K c) * (airySeedG 0 (u : ℂ)).re) := by
    ext u
    have hGN := congr_fun (ceHb_GN_eq ds) u
    dsimp [ceHbDlift]; rw [hGN]; ring
  rw [hfeq, integral_neg, hF.2]; ring

/-- Pre-edge Fourier positivity `0 < ceHbFhat ds K c Δ` for fixed `K ≥ 1`. -/
theorem ceHb_preEdge_pos {D : ShellHBData} (ds : CeHbDualScales D)
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
      have h1 : 2 * ds.C_η * K ≤ M_r :=
        (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
      calc ds.C_η * K = (1 / 2) * (2 * ds.C_η * K) := by ring
        _ ≤ (1 / 2) * √c := mul_le_mul_of_nonneg_left (h1.trans hsqrt) (by norm_num)
    have hv : ds.C_η * K * c ^ (-(1 / 2 : ℝ)) ≤ ds.v₀ / 2 := by
      rw [h_inv_s, ← div_eq_mul_inv, div_le_iff₀ hsqrt_pos]
      have hv_pos : 0 < ds.v₀ := by linarith [ds.hv₀]
      have h1 : 2 * ds.C_η * K / ds.v₀ ≤ M_r :=
        ((le_max_left _ _).trans (le_max_right _ _)).trans (le_add_of_nonneg_right zero_le_one)
      calc ds.C_η * K = (ds.v₀ / 2) * (2 * ds.C_η * K / ds.v₀) := by field_simp [hv_pos.ne']
        _ ≤ (ds.v₀ / 2) * √c := mul_le_mul_of_nonneg_left (h1.trans hsqrt) (by positivity)
    have hCg_le : ds.C_η * K * c ^ (-(1 / 2 : ℝ)) ≤ 1 / (2 * ds.Cg + 1) := by
      rw [h_inv_s, ← div_eq_mul_inv, div_le_iff₀ hsqrt_pos]
      have hcg_pos : 0 < 2 * ds.Cg + 1 := by linarith [ds.hCg_pos]
      have h1 : 2 * ds.C_η * K * (2 * ds.Cg + 1) ≤ M_r :=
        ((le_max_right _ _).trans (le_max_right _ _)).trans (le_add_of_nonneg_right zero_le_one)
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
    have hintH' : Integrable (fun u : ℝ => (K * ds.γ₁) * ds.S.H_N u) := intH.const_mul _
    have hintSb' : Integrable (fun u : ℝ => -(K * ds.γ₂) * ceSb ds.b u) := intSb.const_mul _
    have hintG' : Integrable (fun u : ℝ => (ds.r_eta K c / liftEps c) * (airySeedG 0 (u : ℂ)).re) :=
      intG.const_mul _
    have hadd1 : ∫ u : ℝ, ((K * ds.γ₁) * ds.S.H_N u + (-(K * ds.γ₂) * ceSb ds.b u +
          (ds.r_eta K c / liftEps c) * (airySeedG 0 (u : ℂ)).re)) =
        (∫ u : ℝ, (K * ds.γ₁) * ds.S.H_N u) +
          ∫ u : ℝ, (-(K * ds.γ₂) * ceSb ds.b u + (ds.r_eta K c / liftEps c) * (airySeedG 0 (u : ℂ)).re) :=
      integral_add hintH' (hintSb'.add hintG')
    have hadd2 : ∫ u : ℝ, (-(K * ds.γ₂) * ceSb ds.b u + (ds.r_eta K c / liftEps c) * (airySeedG 0 (u : ℂ)).re) =
        (∫ u : ℝ, -(K * ds.γ₂) * ceSb ds.b u) + ∫ u : ℝ, (ds.r_eta K c / liftEps c) * (airySeedG 0 (u : ℂ)).re :=
      integral_add hintSb' hintG'
    rw [hsum, hadd1, hadd2,
      integral_const_mul, integral_const_mul, integral_const_mul,
      ds.S.integral_H, ceSb_integral ds.b, integral_airySeedG 0]
    have hγ₁_val : ds.γ₁ * ds.S.I_N - ds.γ₂ * (1 + |airyDerivFirstZero|) = ds.v₀ := by
      rw [ds.hγ₁_eq, div_mul_cancel₀ _ ds.S.I_N_pos.ne']; ring
    have hKv : ds.v₀ ≤ K * ds.v₀ := le_mul_of_one_le_left (by linarith [ds.hv₀]) hK1
    have hrv : -(ds.v₀ / 2) ≤ ds.r_eta K c / liftEps c :=
      (abs_le.mp ((hr_div_le hc).trans ((min_le_right _ _).trans (min_le_left _ _)))).1
    have hlin : (K * ds.γ₁) * ds.S.I_N + (-(K * ds.γ₂) * (1 + |airyDerivFirstZero|)) = K * ds.v₀ := by
      calc (K * ds.γ₁) * ds.S.I_N + (-(K * ds.γ₂) * (1 + |airyDerivFirstZero|))
          = K * (ds.γ₁ * ds.S.I_N - ds.γ₂ * (1 + |airyDerivFirstZero|)) := by ring
        _ = K * ds.v₀ := by rw [hγ₁_val]
    linarith
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
    have hg_bd : |(airyTwistedLaplaceC (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re| ≤
        ds.Cg := by
      have hgn := (Complex.abs_re_le_norm _).trans (ds.hCg (x : ℂ) hre)
      rw [← Complex.ofReal_mul] at hgn
      have hnorm : ‖1 + (x : ℂ)‖ ^ (-(5 / 2 : ℝ)) ≤ 1 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      exact hgn.trans (mul_le_of_le_one_right ds.hCg_pos.le hnorm)
    have hr_bd : |ds.r_eta K c / liftEps c| ≤ 1 / (2 * ds.Cg + 1) :=
      (hr_div_le hc).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hmul_abs : |(ds.r_eta K c / liftEps c) *
        (airyTwistedLaplaceC (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re| ≤ 1 / 2 := by
      rw [abs_mul]
      refine (mul_le_mul hr_bd hg_bd (abs_nonneg _) (by have := ds.hCg_pos; positivity)).trans ?_
      have hcg_pos : 0 < 2 * ds.Cg + 1 := by linarith [ds.hCg_pos]
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hcg_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [ds.hCg_pos]
    have hcx_eq : (ceCs : ℂ) * (x : ℂ) = ((ceCs * x : ℝ) : ℂ) := by push_cast; ring
    rw [hcx_eq]
    have hK_exp : K * (ds.γ₁ * (airyTwistedLaplaceC (fun u => ds.S.H_N u) ((ceCs * x : ℝ) : ℂ)).re -
          ds.γ₂ * (airyTwistedLaplaceC (ceSb ds.b) ((ceCs * x : ℝ) : ℂ)).re) =
        K * ds.γ₁ * (airyTwistedLaplaceC (fun u => ds.S.H_N u) ((ceCs * x : ℝ) : ℂ)).re +
          -(K * ds.γ₂) * (airyTwistedLaplaceC (ceSb ds.b) ((ceCs * x : ℝ) : ℂ)).re := by ring
    linarith [hK1_lin, hK_exp, (abs_le.mp hmul_abs).1]
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
    dsimp [W_S_scaled, ceHbSsrc]; exact liftSymbol_const_mul_seed _ _ _ _ _
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
      have h1 := (hWS0_real hc8K (Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ))).2
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
      (fun {c} hc => hJ₀_pos hc)
      (ceHbFhat ds K) (fun {c} _ => by simp only [ceHbFhat, δ₀_fn, ↓reduceIte])
      (fun {c Δ} _ hΔ0 _ => by simp only [ceHbFhat, δ₀_fn, hΔ0.ne', ↓reduceIte])
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
    ext w; congr 1; ext u
    simp only [s3, Fin.sum_univ_three, B3, α3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [← congr_fun (ceHb_HN_eq ds) u, airySbC_re]
    dsimp [ceHbDlift]; field_simp [hε0]; ring
  have hd_tan : Nonempty (PreEdgeTangencyData fhat_tang) := by
    refine ⟨{
      W_S := W_S_scaled
      W_D := fun c => liftSymbol (ceHbDlift ds K c) (δ₀_fn c) 4
      c_min := c_D0, M := M, Λ := Λ, Λ_add_max := Λ_add_D
      x₀ := ds.x₀, b := b_D, a_tan := ds.x₀ / 3, b_tan := 2 * ds.B₀
      c_J := c_J, C_S := C_S_K, K_D := K_D
      hc_min := by linarith, hM := hM1, hΛ := hΛ1, hΛ_add := hΛ_add_D
      hx₀ := ds.hx₀, hb := hb_D, ha_tan := by have := ds.hx₀; positivity,
      hc_J := hc_J, hCS := hCS_K_pos.le, hKD := hK_D, hab_tan := by linarith [ds.hx₀, ds.hx₀B]
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
        have hxy0 : 0 ≤ |y| / x := div_nonneg (abs_nonneg y) hx.le
        calc ds.M_K K c * ‖liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 ((x : ℂ) + (y : ℂ) * Complex.I) -
              liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)‖
            ≤ ds.M_K K c * (4 * M_S * (|y| / x) * (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re) :=
              mul_le_mul_of_nonneg_left h1 hMK.le
          _ = 4 * M_S * (|y| / x) * (ds.M_K K c * (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re) := by ring
          _ ≤ 4 * M * (|y| / x) * (ds.M_K K c * (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re) := by
              have : 0 ≤ ds.M_K K c * (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re := mul_nonneg hMK.le hSn
              gcongr
      hA1_D := fun {c x y} hc hx hx_c hxtan hy => by
        rw [← hWD_eq hc]
        have h1 := hWD_A1 hc hx hx_c hxtan hy
        have hDn := hWD_nn hc hx hx_c
        have hM_le : M_D ≤ M := le_max_right _ _
        have hxy0 : 0 ≤ |y| / x := div_nonneg (abs_nonneg y) hx.le
        exact h1.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM_le (by norm_num)) hxy0) hDn)
      hA2_S := fun {c x y} hc hx hx_c => by
        have hc8K : max 8 (8 * K ^ 3) ≤ c := max_le (by linarith) (hc_D0_K.trans hc)
        have hMK := hMK_pos hc
        have h1 := hWS0_A2 (y := y) hc8K hx hx_c
        have hSn : 0 ≤ (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re :=
          (hWS0_real hc8K hx).2.le
        rw [hWS_scaled_eq, hWS_scaled_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hMK.le,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        have hΛ_le : Λ_S ≤ Λ := le_max_left _ _
        calc ds.M_K K c * ‖liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 ((x : ℂ) + (y : ℂ) * Complex.I)‖
            ≤ ds.M_K K c * (Λ_S * (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re) :=
              mul_le_mul_of_nonneg_left h1 hMK.le
          _ = Λ_S * (ds.M_K K c * (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re) := by ring
          _ ≤ Λ * (ds.M_K K c * (liftSymbol (convSourceFamily (3 / 4) 1 1 1 c) (δ₀_fn c) 4 (x : ℂ)).re) :=
              mul_le_mul_of_nonneg_right hΛ_le (mul_nonneg hMK.le hSn)
      hA2_D := fun {c x y} hc hx hx_c hxtan => by
        rw [← hWD_eq hc]
        have h1 := hWD_A2 (y := y) hc hx hx_c hxtan
        have hDn := hWD_nn hc hx hx_c
        have hΛ_le : Λ_D ≤ Λ := le_max_right _ _
        exact h1.trans (add_le_add (mul_le_mul_of_nonneg_right hΛ_le hDn) le_rfl)
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
        have hUS_c : HasU2 (ceHbSsrc ds K c) := ceHb_HasU2_Ssrc ds hc0
        have hUD_c := ceHb_HasU2_Dlift ds K c
        have hδ0_c : 0 ≤ δ₀_fn c := by unfold δ₀_fn; have := liftEps_pos hc0; have := ceBeta1_pos; positivity
        have hsm := twoEdge_W_tilde_stripM1 (S := fun _ => ceHbSsrc ds K c) (D := fun _ => ceHbDlift ds K c)
          (δ₀ := fun _ => δ₀_fn c) (m := 4) hc4 hUS_c hUD_c hδ0_c
        have hrep := admiss_vert_rep (by linarith : 1 ≤ c) hsm hσ0.le hσ1 hξ0
        simp only [fhat_tang, ceHbFhat, δ₀_fn, hnot, hΔ0.ne', ↓reduceIte]
        rw [← hcξ]
        have hre := congrArg Complex.re hrep
        rw [Complex.ofReal_re] at hre; rw [hre]
        dsimp only [lobeSaddleIntegral, W_S_scaled, δ₀_fn, liftEps] }⟩
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

end FormalResearch.SignUncertainty
