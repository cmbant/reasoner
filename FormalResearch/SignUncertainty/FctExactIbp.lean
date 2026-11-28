/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpSplitErrors
public import FormalResearch.SignUncertainty.FctWarpIntegrand
public import FormalResearch.SignUncertainty.FctWarpLeftMidBand

/-!
# Exact IBP identity `(fct:exact-ibp)` for `warpMainNoRightDensity` (`fct:warp-asymp` (1))

Proves the exact integration-by-parts identity `(fct:exact-ibp)` of `CFT/sign_uncertainty/paper/constant_terms_five.tex`
(lines 600–601) at the solved zero pair `(L₁, α) = (fctWarpL1 h ε c, fctWarpAlpha h ε c)`:

For all large `c`, `ε = ±1`, `ξ > 0`, and `L = log(π² ξ) ≠ L₁`:
`warpMainNoRightDensity h ε c ξ = (1 / fctNc h ε c) * (|uctCAi| * c^{-5/6} / (L - L₁)) * warpSqDensity K4 ε c L1 α ξ`,
where
`warpSqDensity K4 ε c L1 α ξ = (c^{1/3} / π) * (∫ τ in Ioi 0, mellinK0 c (τ * I) ξ * fctWarpA K4 ε c L1 α (τ * I)).re`.

Class: proved (depending only on `K4 ≥ 1`). Kernel-dependence guard at the end.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty
open FctMoment

/-- `P(τ) = K₀(iτ, ξ₁) Ψ_c(iτ)` along the imaginary axis (`(fct:exact-ibp)`). -/
noncomputable def warpP (K4 ε c L1 α τ : ℝ) : ℂ :=
  mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)

/-- Half-line real-part normalization of `h_sq(L)`:
`(c^{1/3} / π) Re ∫₀^∞ K₀(iτ, ξ) A_ε(iτ) dτ` (`(fct:hsq-hwarp)` + real symmetry). -/
noncomputable def warpSqDensity (K4 ε c L1 α ξ : ℝ) : ℝ :=
  (c ^ (1 / 3 : ℝ) / π) *
    (∫ τ in Ioi (0 : ℝ), mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)).re

/-- Phase shift relating `mellinK0 c (iτ) ξ` and `mellinK0 c (iτ) (fctXi1 L1)`. -/
lemma mellinK0_imag_shift {c L1 ξ τ : ℝ} (hξ : 0 < ξ) :
    mellinK0 c ((τ : ℂ) * Complex.I) ξ =
      Complex.exp (Complex.I * ((c * (Real.log (π ^ 2 * ξ) - L1) * τ : ℝ) : ℂ)) *
        mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) := by
  have hlog : Complex.log ((π : ℂ) ^ 2 * (fctXi1 L1 : ℂ)) = (L1 : ℂ) := by
    have hp : Real.log (π ^ 2 * fctXi1 L1) = L1 := by
      unfold fctXi1
      rw [mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_exp]
    have hxi1 : 0 < fctXi1 L1 := fctXi1_pos L1
    rw [show (π : ℂ) ^ 2 * (fctXi1 L1 : ℂ) = ((π ^ 2 * fctXi1 L1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), hp]
  have hlogξ : Complex.log ((π : ℂ) ^ 2 * (ξ : ℂ)) = (Real.log (π ^ 2 * ξ) : ℂ) := by
    rw [show (π : ℂ) ^ 2 * (ξ : ℂ) = ((π ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  have hphi_dif : (c : ℂ) * mellinPhi ((τ : ℂ) * Complex.I) ξ =
      (c : ℂ) * mellinPhi ((τ : ℂ) * Complex.I) (fctXi1 L1) +
        Complex.I * ((c * (Real.log (π ^ 2 * ξ) - L1) * τ : ℝ) : ℂ) := by
    unfold mellinPhi
    rw [hlog, hlogξ]; push_cast; ring
  unfold mellinK0
  rw [hphi_dif, Complex.exp_add]
  ring

private lemma warpP_eq_integral_pos {K4 ε c L1 α τ : ℝ} (hτ : 0 < τ) :
    warpP K4 ε c L1 α τ = Complex.I * ∫ t in (0 : ℝ)..τ, fctWarpIntegrand K4 ε c L1 α t := by
  unfold warpP fctPsi
  have hne := mellinK0_ne_zero c (by simp : ((τ : ℂ) * Complex.I).re < 1) (fctXi1 L1)
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have hcomp := intervalIntegral.integral_comp_mul_right
    (fun t : ℝ => fctWarpIntegrand K4 ε c L1 α t) hτ.ne' (a := (0 : ℝ)) (b := (1 : ℝ))
  simp only [zero_mul, one_mul] at hcomp
  have hint_eq : (∫ s in (0 : ℝ)..1, mellinK0 c ((s : ℂ) * ((τ : ℂ) * Complex.I)) (fctXi1 L1) *
      fctWarpA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I))) =
      ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * τ) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    unfold fctWarpIntegrand
    have hst : (s : ℂ) * ((τ : ℂ) * Complex.I) = ((s * τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hst]
  rw [hint_eq, show ((τ : ℂ) * Complex.I) * ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * τ) =
      Complex.I * ((τ : ℝ) • ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * τ)) by
    rw [Complex.real_smul]; ring, hcomp, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]

private lemma integrable_near_exp {f : ℝ → ℂ} {M r : ℝ} (_hM : 0 ≤ M) (_hr : 0 < r)
    (hcont : ContinuousOn f {τ : ℝ | τ ≠ 0})
    (hnear : ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ r → ‖f τ‖ ≤ M)
    (hfar : ∀ τ : ℝ, r < |τ| → ‖f τ‖ ≤ M * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) :
    Integrable f := by
  have h_ae : AEStronglyMeasurable f volume := by
    have hcomp0 : ∀ᵐ τ : ℝ, τ ∈ {τ : ℝ | τ ≠ 0} := by
      rw [ae_iff]; simp only [Set.mem_ofPred_eq, ne_eq, not_not]; exact Real.volume_singleton
    have hreq : volume.restrict {τ : ℝ | τ ≠ 0} = volume := Measure.restrict_eq_self_of_ae_mem hcomp0
    exact hreq ▸ hcont.aestronglyMeasurable isOpen_ne.measurableSet
  let g : ℝ → ℝ :=
    (Icc (-r) r).indicator (fun _ => M) +
      (Icc (-r) r)ᶜ.indicator (fun τ => M * ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))))
  have hg1 : Integrable ((Icc (-r) r).indicator (fun _ : ℝ => M)) :=
    (integrableOn_const (hs := measure_Icc_lt_top.ne) (C := M)).integrable_indicator measurableSet_Icc
  have hg2 : Integrable ((Icc (-r) r)ᶜ.indicator (fun τ : ℝ => M * ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))))) :=
    ((integrable_pow_mul_exp_neg_pi 12).const_mul M).indicator measurableSet_Icc.compl
  refine (hg1.add hg2).mono' h_ae ?_
  have hcomp0 : ∀ᵐ τ : ℝ, τ ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not]; exact Real.volume_singleton
  filter_upwards [hcomp0] with τ hτ
  by_cases hτr : |τ| ≤ r
  · have hτmem : τ ∈ Icc (-r) r := abs_le.mp hτr
    have h1 : (Icc (-r) r).indicator (fun _ : ℝ => M) τ = M := Set.indicator_of_mem hτmem _
    have h2 : (Icc (-r) r)ᶜ.indicator (fun t : ℝ => M * ((1 + |t|) ^ 12 * Real.exp (-(π * |t|)))) τ = 0 :=
      Set.indicator_of_notMem (by simp [hτmem]) _
    change ‖f τ‖ ≤ (Icc (-r) r).indicator (fun _ : ℝ => M) τ +
      (Icc (-r) r)ᶜ.indicator (fun t : ℝ => M * ((1 + |t|) ^ 12 * Real.exp (-(π * |t|)))) τ
    rw [h1, h2, add_zero]
    exact hnear τ hτ hτr
  · have hlt : r < |τ| := lt_of_not_ge hτr
    have hτnot : τ ∉ Icc (-r) r := fun h => hτr (abs_le.mpr h)
    have h1 : (Icc (-r) r).indicator (fun _ : ℝ => M) τ = 0 := Set.indicator_of_notMem hτnot _
    have h2 : (Icc (-r) r)ᶜ.indicator (fun t : ℝ => M * ((1 + |t|) ^ 12 * Real.exp (-(π * |t|)))) τ =
        M * ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) :=
      Set.indicator_of_mem hτnot _
    change ‖f τ‖ ≤ (Icc (-r) r).indicator (fun _ : ℝ => M) τ +
      (Icc (-r) r)ᶜ.indicator (fun t : ℝ => M * ((1 + |t|) ^ 12 * Real.exp (-(π * |t|)))) τ
    rw [h1, h2, zero_add]
    calc ‖f τ‖ ≤ M * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := hfar τ hlt
      _ = M * ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) := by ring

private lemma integrable_warpMainNoRight {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ : ℝ, 8 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        ((c : ℂ) * fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) /
          (fctNc h ε c : ℂ))) := by
  obtain ⟨c0N, _, hNc⟩ := fctNcC_eq_fctNc hK4 h
  obtain ⟨ML, c0L, hML0, _, hLT⟩ := fctLeftTail_deriv_bounds hK4 h
  obtain ⟨MD, c0D, hMD0, _, hDHG⟩ := dcomp_ctHG_EJ hK4 h
  obtain ⟨Ms, c0s, hMs0, _, hPsi_s⟩ := fctPsi_imag_small_bound hK4 h
  obtain ⟨Mlg, c0lg, hMlg0, _, hPsi_lg⟩ := fctPsi_imag_large_bound hK4 h
  obtain ⟨c0C2, hC2⟩ := fctPhiHat_left_c2 hK4 (fctDescent_uncond hK4 h)
  set c₀ : ℝ := max (max (max c0N c0L) (max c0D c0s)) (max c0lg (max c0C2 8))
  refine ⟨c₀, le_max_of_le_right (le_max_of_le_right (le_max_right _ _)), fun ε c ξ hε hc hξ => ?_⟩
  have h1 : c0N ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _) |>.trans hc
  have h4 : c0L ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _) |>.trans hc
  have h5 : c0D ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _) |>.trans hc
  have h6 : c0s ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _) |>.trans hc
  have h7 : c0lg ≤ c := (le_max_left _ _).trans (le_max_right _ _) |>.trans hc
  have h8 : c0C2 ≤ c := (le_max_left _ _).trans (le_max_right _ _) |>.trans (le_max_right _ _) |>.trans hc
  have hc8 : 8 ≤ c := (le_max_right _ _).trans (le_max_right _ _) |>.trans (le_max_right _ _) |>.trans hc
  have hcpos : 0 < c := by linarith
  obtain ⟨hNc_eq, hNc_lo, _, hNc_ne⟩ := hNc ε c hε h1
  obtain ⟨hLT_cd, _, _⟩ := hLT ε c hε h4
  have hEJ := hDHG ε c hε h5
  have hPs := hPsi_s ε c ξ hε h6 hξ
  have hPlg := hPsi_lg ε c ξ hε h7 hξ
  have hc2' := hC2 ε c hε h8
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set Nc := (fctNc h ε c : ℂ)
  have hNc_inv : ‖Nc⁻¹‖ ≤ 2 := by
    change ‖((fctNc h ε c : ℝ) : ℂ)⁻¹‖ ≤ 2
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hm_cont : Continuous (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ) :=
    continuous_mellinK0_imag hcpos hξ
  have hMain_eq : ∀ τ : ℝ, τ ≠ 0 →
      (c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc =
        (fctPhiHat h ε c ((τ : ℂ) * Complex.I) - fctLeftTail K4 ε c L1 α τ) *
          (fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) := fun τ hτ => by
    have hd1 : fctDcompAt K4 c α ((τ : ℂ) * Complex.I) ≠ 0 := fctDcompAt_ne_zero _
    have hd2 : ctHG ε ((τ : ℂ) * Complex.I) ≠ 0 :=
      ctHG_ne_zero_of_closed_band ε (by simp) (by simp) (by simp [hτ])
    have hspl : fctPhiHat h ε c ((τ : ℂ) * Complex.I) - fctLeftTail K4 ε c L1 α τ =
        fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc := by
      show fctPhiHatAt K4 ε c L1 α ((τ : ℂ) * Complex.I) - _ = _
      rw [fctPhiHatAt_left_eq_add_tail, hNc_eq]; ring
    rw [hspl]; unfold fctPhiC; field_simp [hd1, hd2, hNc_ne]
  have hcont : ContinuousOn (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc)) {τ : ℝ | τ ≠ 0} := by
    refine ContinuousOn.congr
      (hm_cont.continuousOn.mul ((hc2'.continuousOn.sub hLT_cd.continuous.continuousOn).mul hEJ.c2.continuousOn))
      fun τ hτ => ?_
    simp only [Pi.mul_apply, Pi.sub_apply]; rw [hMain_eq τ hτ]
  set r := c ^ (-(1 / 3 : ℝ))
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hcpos _
  have hr_le1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  set M := max (2 * Ms * c) (2 * Mlg * (max r⁻¹ 1) ^ (5 / 2 : ℝ))
  refine integrable_near_exp (M := M) (by positivity) hr_pos hcont (fun τ hτ hτr => ?_) (fun τ hτr => ?_)
  · have hnm : ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc)‖ =
        ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ * ‖Nc⁻¹‖ := by
      rw [show mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc) =
          (mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))) * Nc⁻¹ by ring,
        norm_mul]
    have hrp1 : |τ| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg τ) (hτr.trans hr_le1) (by norm_num)
    rw [hnm]
    calc _ ≤ (Ms * c * |τ| ^ (1 / 2 : ℝ)) * 2 :=
          mul_le_mul (hPs τ hτ hτr) hNc_inv (norm_nonneg _) (by positivity)
      _ ≤ (Ms * c * 1) * 2 := by gcongr
      _ = 2 * Ms * c := by ring
      _ ≤ M := le_max_left _ _
  · have hτpos : 0 < |τ| := hr_pos.trans hτr
    have hτne : τ ≠ 0 := abs_pos.mp hτpos
    have hpow_neg : |τ| ^ (-(5 / 2 : ℝ)) ≤ (max r⁻¹ 1) ^ (5 / 2 : ℝ) := by
      rw [Real.rpow_neg hτpos.le, ← Real.inv_rpow hτpos.le]
      exact Real.rpow_le_rpow (by positivity) ((inv_anti₀ hr_pos hτr.le).trans (le_max_left _ _)) (by norm_num)
    have h10_12 : (1 + |τ|) ^ 10 ≤ (1 + |τ|) ^ 12 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg τ]) (by norm_num)
    have hnm : ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc)‖ =
        ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ * ‖Nc⁻¹‖ := by
      rw [show mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc) =
          (mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))) * Nc⁻¹ by ring,
        norm_mul]
    rw [hnm]
    calc _ ≤ (Mlg * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) * 2 :=
          mul_le_mul (hPlg τ hτne) hNc_inv (norm_nonneg _) (by positivity)
      _ ≤ (2 * Mlg * (max r⁻¹ 1) ^ (5 / 2 : ℝ)) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by
          have : 0 ≤ Real.exp (-(π * |τ|)) := (Real.exp_pos _).le
          calc (Mlg * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) * 2
              = (2 * Mlg * |τ| ^ (-(5 / 2 : ℝ))) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|)) := by ring
            _ ≤ (2 * Mlg * (max r⁻¹ 1) ^ (5 / 2 : ℝ)) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by gcongr
      _ ≤ M * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by gcongr; exact le_max_right _ _

private lemma warp_ibp_limit {P g : ℝ → ℂ} {ω : ℝ} (hω : ω ≠ 0)
    (hg_int : IntegrableOn g (Ioi 0))
    (hP_exp_int : IntegrableOn (fun τ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P τ) (Ioi 0))
    (hG_exp_int : IntegrableOn (fun τ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g τ) (Ioi 0))
    (hP_deriv : ∀ τ : ℝ, 0 < τ → HasDerivAt P (Complex.I * g τ) τ)
    (hP_lim0 : Tendsto P (𝓝[>] 0) (𝓝 0))
    (hP_limTop : Tendsto P atTop (𝓝 0)) :
    ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P τ =
      -((ω : ℂ)⁻¹ * ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g τ) := by
  have hωc_ne : Complex.I * (ω : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hω)
  let v : ℝ → ℂ := fun τ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) / (Complex.I * (ω : ℂ))
  have hv_deriv : ∀ τ : ℝ, HasDerivAt v (Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) τ := fun τ => by
    have h0 : (fun t : ℝ => Complex.I * ((ω * t : ℝ) : ℂ)) = fun t : ℝ => (Complex.I * (ω : ℂ)) * (t : ℂ) := by
      ext t; push_cast; ring
    have hlin : HasDerivAt (fun t : ℝ => Complex.I * ((ω * t : ℝ) : ℂ)) (Complex.I * (ω : ℂ)) τ := by
      rw [h0]
      simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).const_mul (Complex.I * (ω : ℂ))
    have hdiv := hlin.cexp.div_const (Complex.I * (ω : ℂ))
    rwa [mul_div_cancel_right₀ _ hωc_ne] at hdiv
  have hibp_R : ∀ R : ℝ, 2 ≤ R →
      ∫ τ in R⁻¹..R, Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P τ =
        P R * v R - P R⁻¹ * v R⁻¹ -
          ((ω : ℂ)⁻¹) * ∫ τ in R⁻¹..R, Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g τ := by
    intro R hR
    have ha0 : 0 < R⁻¹ := inv_pos.mpr (by linarith)
    have haR : R⁻¹ ≤ R := by rw [inv_le_iff_one_le_mul₀ (by linarith)]; nlinarith
    have hu_deriv : ∀ τ ∈ uIcc R⁻¹ R, HasDerivAt P (Complex.I * g τ) τ := fun τ hτ => by
      rw [uIcc_of_le haR] at hτ
      exact hP_deriv τ (lt_of_lt_of_le ha0 hτ.1)
    have hu_int : IntervalIntegrable (fun τ => Complex.I * g τ) volume R⁻¹ R := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le haR]
      exact (hg_int.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha0.le))).const_mul Complex.I
    have hv_int : IntervalIntegrable (fun τ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) volume R⁻¹ R :=
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_id)))).intervalIntegrable _ _
    have hmul_ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_deriv
      (fun τ _ => hv_deriv τ) hu_int hv_int
    have hlhs : ∫ τ in R⁻¹..R, Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P τ =
        ∫ τ in R⁻¹..R, P τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) :=
      intervalIntegral.integral_congr fun _ _ => mul_comm _ _
    have hrhs : ∫ τ in R⁻¹..R, Complex.I * g τ * v τ =
        (ω : ℂ)⁻¹ * ∫ τ in R⁻¹..R, Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g τ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun τ _ => ?_
      dsimp only [v]; field_simp [Complex.I_ne_zero]
    rw [hlhs, hmul_ibp, hrhs]
  have h_ind_lim : ∀ {h : ℝ → ℂ}, IntegrableOn h (Ioi 0) →
      Tendsto (fun R : ℝ => ∫ τ in R⁻¹..R, h τ) atTop (𝓝 (∫ τ in Ioi (0 : ℝ), h τ)) := by
    intro h hh
    have hlim := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ))) (l := (atTop : Filter ℝ))
      (F := fun (R : ℝ) (τ : ℝ) => (Ioc R⁻¹ R).indicator h τ) (f := h)
      (bound := fun τ => ‖h τ‖)
      ?_ ?_ hh.norm ?_
    · refine hlim.congr' ?_
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
      have haR : R⁻¹ ≤ R := by rw [inv_le_iff_one_le_mul₀ (by linarith)]; nlinarith
      have ha0 : 0 < R⁻¹ := inv_pos.mpr (by linarith)
      rw [intervalIntegral.integral_of_le haR, MeasureTheory.setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_self_of_subset_right (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha0.le))]
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R _
      exact hh.aestronglyMeasurable.indicator measurableSet_Ioc
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R _
      exact ae_of_all _ fun τ => by
        by_cases ht : τ ∈ Ioc R⁻¹ R
        · simp [Set.indicator_of_mem ht]
        · simp [Set.indicator_of_notMem ht]
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ (hτ : 0 < τ) => ?_
      have hev : ∀ᶠ R : ℝ in atTop, τ ∈ Ioc R⁻¹ R := by
        filter_upwards [eventually_gt_atTop τ⁻¹, eventually_ge_atTop τ] with R hR1 hR2
        exact ⟨inv_lt_of_inv_lt₀ hτ hR1, hR2⟩
      exact tendsto_const_nhds.congr' (hev.mono fun R hR => (Set.indicator_of_mem hR h).symm)
  have hv_bd : ∀ τ : ℝ, ‖v τ‖ = |ω|⁻¹ := fun τ => by
    dsimp only [v]
    rw [norm_div, show ‖Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ = 1 by
      rw [Complex.norm_exp]; simp [Complex.mul_re], norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, one_div]
  have hbd1 : Tendsto (fun R : ℝ => P R * v R) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn : Tendsto (fun R : ℝ => ‖P R‖ * |ω|⁻¹) atTop (𝓝 0) := by
      simpa using (hP_limTop.norm).mul_const |ω|⁻¹
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hn
      (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun R => by
        rw [norm_mul, hv_bd])
  have hbd0 : Tendsto (fun R : ℝ => P R⁻¹ * v R⁻¹) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hPinv : Tendsto (fun R : ℝ => ‖P R⁻¹‖) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (hP_lim0.norm).comp tendsto_inv_atTop_nhdsGT_zero
    have hn : Tendsto (fun R : ℝ => ‖P R⁻¹‖ * |ω|⁻¹) atTop (𝓝 0) := by
      simpa using hPinv.mul_const |ω|⁻¹
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hn
      (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun R => by
        rw [norm_mul, hv_bd])
  have hRHS_lim := by
    simpa only [sub_zero, zero_sub] using (hbd1.sub hbd0).sub ((h_ind_lim hG_exp_int).const_mul (ω : ℂ)⁻¹)
  have hLHS_lim := h_ind_lim hP_exp_int
  have h_ev : (fun R : ℝ => ∫ τ in R⁻¹..R, Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P τ) =ᶠ[atTop]
      (fun R : ℝ => P R * v R - P R⁻¹ * v R⁻¹ -
        ((ω : ℂ)⁻¹) * ∫ τ in R⁻¹..R, Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g τ) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    exact hibp_R R hR
  exact tendsto_nhds_unique (hLHS_lim.congr' h_ev) hRHS_lim

/-- **`(fct:exact-ibp)`** of Paper I (`constant_terms_five.tex`, lines 600–601):
at the zero pair `(L₁, α) = (fctWarpL1 h ε c, fctWarpAlpha h ε c)` of `h : FctWarpSolveStmt K4`, for `L = log(π² ξ) ≠ L₁`,
`warpMainNoRightDensity h ε c ξ = (1 / fctNc h ε c) * (|uctCAi| * c^{-5/6} / (L - L₁)) * warpSqDensity K4 ε c L1 α ξ`. -/
theorem warpMainNoRightDensity_exact_ibp {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ : ℝ, 8 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      Real.log (π ^ 2 * ξ) ≠ fctWarpL1 h ε c →
      IntegrableOn (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          fctWarpA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I)) (Ioi 0) ∧
      warpMainNoRightDensity h ε c ξ =
        (1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (Real.log (π ^ 2 * ξ) - fctWarpL1 h ε c)) *
          warpSqDensity K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ξ := by
  obtain ⟨c0N, _, hNc⟩ := fctNcC_eq_fctNc hK4 h
  obtain ⟨c0I, hc0I, hint_main⟩ := integrable_warpMainNoRight hK4 h
  obtain ⟨c0s, _, hSetup⟩ := fctSplitting_setup hK4 (fctDescent_uncond hK4 h)
  obtain ⟨Ms, c0Ps, hMs0, _, hPsi_s⟩ := fctPsi_imag_small_bound hK4 h
  have hτD_pos : 0 < (FctCompD.fct_comp_D_part1 FctCompD.StripKernelChoice.star).choose :=
    (FctCompD.fct_comp_D_part1 FctCompD.StripKernelChoice.star).choose_spec.1
  have hτ₁_ev : ∃ cτ : ℝ, 1 ≤ cτ ∧ ∀ c : ℝ, cτ ≤ c →
      c ^ (-(1 / 4 : ℝ)) ≤ (FctCompD.fct_comp_D_part1 FctCompD.StripKernelChoice.star).choose := by
    obtain ⟨cτ, hcτ⟩ := eventually_atTop.mp
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually (Iic_mem_nhds hτD_pos))
    exact ⟨max cτ 1, le_max_right _ _, fun c hc => hcτ c ((le_max_left _ _).trans hc)⟩
  obtain ⟨cτ, _, hcτ⟩ := hτ₁_ev
  set c0W := h.choose_spec.choose
  set c₀ : ℝ := max (max (max c0N c0I) (max c0s c0Ps)) (max cτ c0W)
  refine ⟨c₀, le_trans hc0I ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))),
    fun ε c ξ hε hc hξ hLne => ?_⟩
  have hcN : c0N ≤ c := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hc
  have hcI : c0I ≤ c := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hc
  have hcS : c0s ≤ c := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hc
  have hcPs : c0Ps ≤ c := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hc
  have hcTau : cτ ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hcW : c0W ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hc8 : 8 ≤ c := hc0I.trans hcI
  have hcpos : 0 < c := by linarith
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set L := Real.log (π ^ 2 * ξ)
  have hpair := fctWarpPair_spec h hε hcW
  have hzero_int : IntegrableOn (fctWarpIntegrand K4 ε c L1 α) (Ioi 0) := hpair.2.1
  have hzero_eq : ∫ τ in Ioi (0 : ℝ), fctWarpIntegrand K4 ε c L1 α τ = 0 := by
    have hI := hpair.2.2
    unfold fctWarpI at hI
    exact (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero
  -- (1) Integrability of shifted edge integrand on `Ioi 0`
  have hshift_eq : ∀ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)) * fctWarpIntegrand K4 ε c L1 α τ := fun τ => by
    unfold fctWarpIntegrand
    rw [mellinK0_imag_shift hξ]
    ring
  have hshift_int : IntegrableOn (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) (Ioi 0) := by
    have hm : AEStronglyMeasurable (fun τ : ℝ => Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)))
        (volume.restrict (Ioi 0)) :=
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_id)))).aestronglyMeasurable
    have hmul_int : IntegrableOn (fun τ : ℝ => Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)) *
        fctWarpIntegrand K4 ε c L1 α τ) (Ioi 0) := by
      refine Integrable.mono hzero_int (hm.mul hzero_int.aestronglyMeasurable) (ae_of_all _ fun τ => ?_)
      rw [norm_mul, show ‖Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ))‖ = 1 by
        rw [Complex.norm_exp]; simp [Complex.mul_re], one_mul]
    exact hmul_int.congr_fun (fun τ _ => (hshift_eq τ).symm) measurableSet_Ioi
  refine ⟨hshift_int, ?_⟩
  -- (2) Real symmetry collapses `∫ ℝ` to `2 Re ∫ (Ioi 0)`
  have hconj_D := (hSetup ε c hε hcS).2.2.2.2.2
  set F : ℝ → ℂ := fun τ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
    ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / (fctNc h ε c : ℂ))
  have hF_int : Integrable F volume := hint_main ε c ξ hε hcI hξ
  have hF_conj : ∀ τ : ℝ, F (-τ) = starRingEnd ℂ (F τ) := fun τ => by
    dsimp only [F]
    have hci : ((-τ : ℝ) : ℂ) * Complex.I = starRingEnd ℂ ((τ : ℂ) * Complex.I) := by simp
    have hconj_D' : ∀ ζ ∈ CtOuter.closedStrip,
        fctDcompAt K4 c α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcompAt K4 c α ζ) := hconj_D
    rw [hci, mellinK0_conj c hξ (by simp), fctPsi_conj hconj_D' (by simp) (by simp)]
    simp only [map_mul, map_div₀, Complex.conj_ofReal]
  have hF_even : ∀ τ : ℝ, (F (-τ)).re = (F τ).re := fun τ => by
    rw [hF_conj τ, Complex.conj_re]
  have hRe_int : (∫ (τ : ℝ), F τ).re = 2 * (∫ (τ : ℝ) in Ioi (0 : ℝ), F τ).re := by
    have hre1 : (∫ (τ : ℝ), F τ).re = ∫ (τ : ℝ), (F τ).re :=
      Complex.reCLM.integral_comp_comm hF_int |>.symm
    have hre2 : (∫ (τ : ℝ) in Ioi (0 : ℝ), F τ).re = ∫ (τ : ℝ) in Ioi (0 : ℝ), (F τ).re :=
      Complex.reCLM.integral_comp_comm hF_int.integrableOn |>.symm
    have hF_re_int : Integrable (fun τ : ℝ => (F τ).re) volume := Complex.reCLM.integrable_comp hF_int
    have hsplit_zero := MeasureTheory.integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hF_re_int
    have hiic : ∫ τ in (Ioi (0 : ℝ))ᶜ, (F τ).re = ∫ τ in Ioi (0 : ℝ), (F τ).re := by
      have hneg := integral_comp_neg_Ioi (f := fun τ : ℝ => (F (-τ)).re) (0 : ℝ)
      rw [neg_zero] at hneg
      have hc_eq : (Ioi (0 : ℝ))ᶜ = Iic (0 : ℝ) := by ext τ; simp
      rw [hc_eq]
      simpa only [hF_even] using hneg.symm
    rw [hre1, hre2, ← hsplit_zero, hiic]; ring
  -- (3) Integrate by parts on `Ioi 0`: `∫ Ioi 0, exp(ic(L-L1)τ) * P τ dτ`
  set ω : ℝ := c * (L - L1)
  have hω_ne : ω ≠ 0 := mul_ne_zero hcpos.ne' (sub_ne_zero.mpr hLne)
  have hωc_ne : Complex.I * (ω : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hω_ne)
  have hF_eq_P : ∀ τ : ℝ, F τ =
      ((c / fctNc h ε c : ℝ) : ℂ) * (Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * warpP K4 ε c L1 α τ) :=
    fun τ => by
      dsimp only [F, warpP]
      rw [mellinK0_imag_shift hξ]
      push_cast [ω]; ring
  have hP_exp_int : IntegrableOn
      (fun τ : ℝ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * warpP K4 ε c L1 α τ) (Ioi 0) := by
    have hNc_pos : (0 : ℝ) < fctNc h ε c := by linarith [(hNc ε c hε hcN).2.1]
    have hcn : c / fctNc h ε c ≠ 0 := div_ne_zero hcpos.ne' hNc_pos.ne'
    have hmul : IntegrableOn (fun τ => ((c / fctNc h ε c : ℝ) : ℂ)⁻¹ * F τ) (Ioi 0) :=
      (hF_int.integrableOn (s := Ioi (0 : ℝ))).const_mul ((c / fctNc h ε c : ℝ) : ℂ)⁻¹
    refine hmul.congr_fun (fun τ _ => ?_) measurableSet_Ioi
    dsimp only
    rw [hF_eq_P τ, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hcn), one_mul]
  have hI_cont : ContinuousOn (fctWarpIntegrand K4 ε c L1 α) (Ioi 0) :=
    fctWarpIntegrand_continuousOn hK4 hcpos (hcτ c hcTau)
  have hP_hasDeriv : ∀ τ : ℝ, 0 < τ →
      HasDerivAt (warpP K4 ε c L1 α) (Complex.I * fctWarpIntegrand K4 ε c L1 α τ) τ := fun τ hτ => by
    have ha0 : 0 < τ / 2 := half_pos hτ
    have hIoc_sub : Ioc 0 (τ / 2) ⊆ Ioi 0 := fun t ht => ht.1
    have hInt0 : IntervalIntegrable (fctWarpIntegrand K4 ε c L1 α) volume 0 (τ / 2) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha0.le).mpr (hzero_int.mono_set hIoc_sub)
    let C0 := ∫ t in (0 : ℝ)..(τ / 2), fctWarpIntegrand K4 ε c L1 α t
    have hloc : (fun t => Complex.I * (C0 + ∫ s in (τ / 2)..t, fctWarpIntegrand K4 ε c L1 α s)) =ᶠ[𝓝 τ]
        warpP K4 ε c L1 α := by
      filter_upwards [eventually_gt_nhds (by linarith : τ / 2 < τ)] with t ht
      have ht_i0 : IntervalIntegrable (fctWarpIntegrand K4 ε c L1 α) volume (τ / 2) t :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr
          (hzero_int.mono_set (fun u hu => lt_trans ha0 hu.1))
      have hsum := intervalIntegral.integral_add_adjacent_intervals hInt0 ht_i0
      rw [warpP_eq_integral_pos (by linarith : 0 < t), ← hsum]
    have hcont_at : ContinuousAt (fctWarpIntegrand K4 ε c L1 α) τ :=
      (hI_cont τ hτ).continuousAt (isOpen_Ioi.mem_nhds hτ)
    have hmeas : StronglyMeasurableAtFilter (fctWarpIntegrand K4 ε c L1 α) (𝓝 τ) := by
      refine ⟨Ioi 0, isOpen_Ioi.mem_nhds hτ, ?_⟩
      exact hI_cont.aestronglyMeasurable measurableSet_Ioi
    have hInt_τ : IntervalIntegrable (fctWarpIntegrand K4 ε c L1 α) volume (τ / 2) τ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
        (hzero_int.mono_set (fun u hu => lt_trans ha0 hu.1))
    have hderiv_int : HasDerivAt (fun t => ∫ s in (τ / 2)..t, fctWarpIntegrand K4 ε c L1 α s)
        (fctWarpIntegrand K4 ε c L1 α τ) τ :=
      intervalIntegral.integral_hasDerivAt_right hInt_τ hmeas hcont_at
    exact ((hderiv_int.const_add C0).const_mul Complex.I).congr_of_eventuallyEq hloc.symm
  -- Limits of `warpP` at `0⁺` and `∞`
  have hP_lim0 : Tendsto (warpP K4 ε c L1 α) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hPs := hPsi_s ε c (fctXi1 L1) hε hcPs (fctXi1_pos L1)
    have hsq : Tendsto (fun τ : ℝ => Ms * τ ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun τ : ℝ => τ ^ (1 / 2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ (1 / 2 : ℝ))) :=
        (Real.continuous_rpow_const (by norm_num)).continuousWithinAt
      rw [Real.zero_rpow (by norm_num)] at h0
      simpa [mul_zero] using h0.const_mul Ms
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq ?_ ?_
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · filter_upwards [Ioc_mem_nhdsGT (Real.rpow_pos_of_pos hcpos (-(1 / 3 : ℝ)))] with τ hτ
      have hτ_pos : 0 < τ := hτ.1
      have hτ_le : |τ| ≤ c ^ (-(1 / 3 : ℝ)) := by rw [abs_of_pos hτ_pos]; exact hτ.2
      have hbd := hPs τ hτ_pos.ne' hτ_le
      have hnorm : ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
          ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ =
          c * ‖warpP K4 ε c L1 α τ‖ := by
        unfold warpP
        rw [show mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)) =
            (c : ℂ) * (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)) by ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
      rw [hnorm, abs_of_pos hτ_pos] at hbd
      exact le_of_mul_le_mul_left (by linarith [hbd]) hcpos
  have hP_limTop : Tendsto (warpP K4 ε c L1 α) atTop (𝓝 0) := by
    have hint_lim : Tendsto (fun τ : ℝ => ∫ t in (0 : ℝ)..τ, fctWarpIntegrand K4 ε c L1 α t) atTop
        (𝓝 (∫ t in Ioi (0 : ℝ), fctWarpIntegrand K4 ε c L1 α t)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hzero_int tendsto_id
    rw [hzero_eq] at hint_lim
    have hmul := hint_lim.const_mul Complex.I
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
    exact (warpP_eq_integral_pos hτ).symm
  have hG_exp_int : IntegrableOn (fun τ : ℝ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) *
      fctWarpIntegrand K4 ε c L1 α τ) (Ioi 0) :=
    hshift_int.congr_fun (fun τ _ => hshift_eq τ) measurableSet_Ioi
  have hLHS_eq_RHS : ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * warpP K4 ε c L1 α τ =
      -((ω : ℂ)⁻¹ * ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) *
        fctWarpIntegrand K4 ε c L1 α τ) :=
    warp_ibp_limit hω_ne hzero_int hP_exp_int hG_exp_int hP_hasDeriv hP_lim0 hP_limTop
  -- (4) Assemble prefactor: `uctCAi < 0` cancels the minus sign
  have huctCAi_neg : uctCAi < 0 := by
    unfold uctCAi
    have := ceCs_pos
    have := Real.pi_pos
    rw [neg_div]
    exact neg_neg_iff_pos.mpr (by positivity)
  have huctCAi_eq : uctCAi = -|uctCAi| := by rw [abs_of_neg huctCAi_neg, neg_neg]
  have hc_56 : c ^ (-(1 / 2 : ℝ)) * c * c⁻¹ = c ^ (-(5 / 6 : ℝ)) * c ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_neg_one c]
    conv_lhs => arg 1; arg 2; rw [← Real.rpow_one c]
    rw [← Real.rpow_add hcpos, ← Real.rpow_add hcpos, ← Real.rpow_add hcpos]
    congr 1; norm_num
  have h_half_F : ∫ τ in Ioi (0 : ℝ), F τ =
      ((c / fctNc h ε c : ℝ) : ℂ) * (-((ω : ℂ)⁻¹) * ∫ τ in Ioi (0 : ℝ),
        mellinK0 c ((τ : ℂ) * Complex.I) ξ * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) := by
    have h1 : ∫ τ in Ioi (0 : ℝ), F τ =
        ((c / fctNc h ε c : ℝ) : ℂ) * ∫ τ in Ioi (0 : ℝ),
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * warpP K4 ε c L1 α τ := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun τ _ => hF_eq_P τ
    rw [h1, hLHS_eq_RHS]
    congr 1
    rw [neg_mul]
    congr 1
    congr 1
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun τ _ => (hshift_eq τ).symm
  have h_real_pref :
      ((c / fctNc h ε c : ℝ) : ℂ) * (-((ω : ℂ)⁻¹) * ∫ τ in Ioi (0 : ℝ),
        mellinK0 c ((τ : ℂ) * Complex.I) ξ * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) =
      ((-(c / fctNc h ε c * ω⁻¹) : ℝ) : ℂ) * ∫ τ in Ioi (0 : ℝ),
        mellinK0 c ((τ : ℂ) * Complex.I) ξ * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) := by
    push_cast; ring
  have h_half_re : (∫ τ in Ioi (0 : ℝ), F τ).re =
      -(c / fctNc h ε c * ω⁻¹) * (∫ τ in Ioi (0 : ℝ),
        mellinK0 c ((τ : ℂ) * Complex.I) ξ * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)).re := by
    rw [h_half_F, h_real_pref, Complex.re_ofReal_mul]
  change (uctCAi * c ^ (-(1 / 2 : ℝ)) / (2 * π)) * (∫ τ : ℝ, F τ).re = _
  rw [hRe_int, h_half_re]
  unfold warpSqDensity
  dsimp only [ω]
  have hω_sub : (c * (L - L1))⁻¹ = c⁻¹ * (L - L1)⁻¹ := by rw [mul_inv_rev, mul_comm]
  rw [hω_sub]
  conv_lhs => rw [huctCAi_eq]
  set I_re : ℝ := (∫ τ in Ioi (0 : ℝ),
    mellinK0 c ((τ : ℂ) * Complex.I) ξ * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)).re
  change (-|uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π)) * (2 * (-(c / fctNc h ε c * (c⁻¹ * (L - L1)⁻¹)) * I_re)) =
    (1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - L1)) * ((c ^ (1 / 3 : ℝ) / π) * I_re)
  calc (-|uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π)) * (2 * (-(c / fctNc h ε c * (c⁻¹ * (L - L1)⁻¹)) * I_re))
      = (1 / fctNc h ε c) * (|uctCAi| * (c ^ (-(1 / 2 : ℝ)) * c * c⁻¹) / (L - L1)) * ((1 / π) * I_re) := by
        ring
    _ = (1 / fctNc h ε c) * (|uctCAi| * (c ^ (-(5 / 6 : ℝ)) * c ^ (1 / 3 : ℝ)) / (L - L1)) * ((1 / π) * I_re) := by
        rw [hc_56]
    _ = (1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - L1)) * ((c ^ (1 / 3 : ℝ) / π) * I_re) := by
        ring

/-- info: 'FormalResearch.SignUncertainty.warpMainNoRightDensity_exact_ibp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpMainNoRightDensity_exact_ibp

end FormalResearch.SignUncertainty
