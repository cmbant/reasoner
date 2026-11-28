/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctExactIbp
public import FormalResearch.SignUncertainty.FctWarpLeftTailFar
public import FormalResearch.SignUncertainty.FctPhiKillSymbol

/-!
# IBP reduction and amplitude bounds for `warpRightTailDensity` (`L ≥ π² 100 c^{-2/3}`)

Prepares the right-tail error estimate needed on the middle, macroscopic, and far bands for
`fct:physical-positive` (`constant_terms_five.tex`, lines 1566–1575):
* `warpAmpBase_bounds` & `warpAmpRight_bounds`: `C¹` cusp-type amplitude bounds on `(0, ∞)`
  for `term1`'s amplitude with phase `edgePhi L`.
* `warpP_integrableOn_and_deriv` & `warpP_abs_integral_le`: `∫₀^∞ ‖warpP τ‖ dτ ≤ C c^{-1/2}`.
* `warpRightTail_first_ibp`: 1-step IBP splitting `warpRightTailDensity` into the `P' R` edge
  oscillatory integral (`term1`) and the `P R'` integral (`term2`).
* `warpRightTail_term2_bounds`: `O(c^{-2} L^{-1})` globally for `L ≥ π² 100 c^{-2/3}` and
  `O(c^{-5/2} L^{-2})` for `L ≥ 1` (via a second IBP using `ContDiff ℝ 2 (fctRightTail)`).

Class: proved (depending only on `K4 ≥ 1`). Kernel-dependence guard at the end.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

/-- Edge amplitude of `K₀(iτ, ξ) A_ε(iτ)` relative to `exp(i c · edgePhi L τ)`. -/
noncomputable def warpAmpBase (K4 ε c L1 α : ℝ) (τ : ℝ) : ℂ :=
  oneSubITauInvSqrt τ * expBinetImag c τ *
    (fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) *
    (stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I))

/-- Edge amplitude for the `P' R` piece of `warpRightTailDensity` relative to phase `edgePhi L`. -/
noncomputable def warpAmpRight (K4 ε c L1 α : ℝ) (R : ℝ → ℂ) (τ : ℝ) : ℂ :=
  warpAmpBase K4 ε c L1 α τ * R τ

/-- `fctWarpIntegrand K4 ε c L1 α τ = exp(I * c * edgePhi L1 τ) * warpAmpBase ... τ`. -/
lemma fctWarpIntegrand_eq_edgePhi (K4 ε c L1 α τ : ℝ) :
    fctWarpIntegrand K4 ε c L1 α τ =
      Complex.exp (Complex.I * ((c * edgePhi L1 τ : ℝ) : ℂ)) * warpAmpBase K4 ε c L1 α τ := by
  have hm := FormalResearch.CohnElkies.mellinK0_imag_eq c (fctXi1 L1) τ (fctXi1_pos L1)
  have hlog : Real.log (π ^ 2 * fctXi1 L1) = L1 := by
    unfold fctXi1; rw [mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_exp]
  rw [hlog] at hm
  have hexp_eq : Complex.exp (Complex.I * (c : ℂ) * ((L1 * τ - π ^ 2 / 36 * τ ^ 3 + CohnElkies.edgeR τ : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((c * edgePhi L1 τ : ℝ) : ℂ)) := by
    congr 1; rw [edgePhi_eq_cubic_add_ceHth]; unfold CohnElkies.edgeR; push_cast; ring
  unfold fctWarpIntegrand fctWarpA warpAmpBase oneSubITauInvSqrt expBinetImag
  rw [hm]
  calc (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
          Complex.exp (Complex.I * (c : ℂ) * ((L1 * τ - π ^ 2 / 36 * τ ^ 3 + CohnElkies.edgeR τ : ℝ) : ℂ)) *
        ((stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)) *
          fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))
      = Complex.exp (Complex.I * (c : ℂ) * ((L1 * τ - π ^ 2 / 36 * τ ^ 3 + CohnElkies.edgeR τ : ℝ) : ℂ)) *
          ((1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
            (fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) *
            (stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I))) := by ring
    _ = _ := by rw [hexp_eq]

/-- `mellinK0 c (iτ) ξ * fctWarpA K4 ε c L1 α (iτ) * R τ = exp(I * c * edgePhi L τ) * warpAmpRight ... τ`. -/
lemma warpAmpRight_eq_integrand (K4 ε c L1 α : ℝ) (R : ℝ → ℂ) {ξ τ : ℝ} (hξ : 0 < ξ) :
    mellinK0 c ((τ : ℂ) * Complex.I) ξ * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) * R τ =
      Complex.exp (Complex.I * ((c * edgePhi (Real.log (π ^ 2 * ξ)) τ : ℝ) : ℂ)) *
        warpAmpRight K4 ε c L1 α R τ := by
  have hm := FormalResearch.CohnElkies.mellinK0_imag_eq c ξ τ hξ
  have hexp_eq : Complex.exp (Complex.I * (c : ℂ) * ((Real.log (π ^ 2 * ξ) * τ - π ^ 2 / 36 * τ ^ 3 + CohnElkies.edgeR τ : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((c * edgePhi (Real.log (π ^ 2 * ξ)) τ : ℝ) : ℂ)) := by
    congr 1; rw [edgePhi_eq_cubic_add_ceHth]; unfold CohnElkies.edgeR; push_cast; ring
  unfold fctWarpA warpAmpRight warpAmpBase oneSubITauInvSqrt expBinetImag
  rw [hm]
  calc (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
          Complex.exp (Complex.I * (c : ℂ) * ((Real.log (π ^ 2 * ξ) * τ - π ^ 2 / 36 * τ ^ 3 + CohnElkies.edgeR τ : ℝ) : ℂ)) *
        ((stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)) *
          fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) * R τ
      = Complex.exp (Complex.I * (c : ℂ) * ((Real.log (π ^ 2 * ξ) * τ - π ^ 2 / 36 * τ ^ 3 + CohnElkies.edgeR τ : ℝ) : ℂ)) *
          ((1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
            (fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) *
            (stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)) * R τ) := by ring
    _ = _ := by rw [hexp_eq]

/-- `C¹` cusp bounds on `Ioi 0` for `warpAmpBase`:
`‖warpAmpBase‖ ≤ C τ^{-1/2} (1+τ)^{12} e^{-πτ}`, `‖deriv warpAmpBase‖ ≤ C τ^{-3/2} (1+τ)^{13} e^{-πτ}`. -/
lemma warpAmpBase_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 32 ^ 4 ≤ c₀ ∧ ∀ {ε c : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ContDiffOn ℝ 1 (warpAmpBase K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)) (Ioi 0) ∧
      ∀ {τ : ℝ}, 0 < τ →
        ‖warpAmpBase K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ‖ ≤
          C * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 12 * Real.exp (-(π * τ)) ∧
        ‖deriv (warpAmpBase K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)) τ‖ ≤
          C * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by
  obtain ⟨MD, c0D, hMD0, hc0D, hDHG⟩ := dcomp_ctHG_EJ hK4 h
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨CL1, cL1, _, hL1_bd⟩ := FctSym.physL1_le (fctWarpT1 h) ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).1⟩
  obtain ⟨Cpk0, hCpk0, hpk0⟩ : ∃ C ≥ (0 : ℝ), ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re →
      ‖FctPhiKill.phiKill a z‖ ≤ C * min ((‖z‖ / a) ^ 8) 1 :=
    (FctPhiKill.fct_phikill).2.2.2.2.2.1
  obtain ⟨Cpk1, hCpk1, hpk1⟩ := FctSym.phiKill_deriv_ge_one 1 le_rfl
  set c₀ : ℝ := max (max c0D cL1) (32 ^ 4)
  set C_k0 : ℝ := 1 + |CL1| * Cpk0
  set C_k1 : ℝ := 2 + |CL1| * Cpk1
  set C_tot : ℝ := 6 * MD * (C_k0 + C_k1)
  refine ⟨C_tot, c₀, by positivity, le_max_right _ _, fun {ε c} hε hc => ?_⟩
  have hcD : c0D ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hcL : cL1 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hc32 : (32 : ℝ) ^ 4 ≤ c := (le_max_right _ _).trans hc
  have hcpos : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have ha0 : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hcpos _
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set a := c ^ (-(1 / 12 : ℝ))
  have hEJ := hDHG ε c hε hcD
  have hL1c' : |L1| ≤ |CL1| * c ^ (-(2 / 3 : ℝ)) := by
    have h1 := hL1_bd ε c hε hcL
    unfold FctSym.physL1 at h1
    rw [physL1_fctWarpT1 h hcpos] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have h1sub := oneSubITauInvSqrt_bounds
  have hbin := expBinetImag_bounds hc1
  let B0 : ℝ → ℂ := fun τ => oneSubITauInvSqrt τ * expBinetImag c τ
  have hB0_cd : ContDiff ℝ 1 B0 := (h1sub.1.mul hbin.1).of_le (by norm_num)
  have hB0_bd : ∀ τ : ℝ, ‖B0 τ‖ ≤ 2 ∧ ‖deriv B0 τ‖ ≤ 4 := fun τ => by
    have h1 := h1sub.2 τ
    have h2 := hbin.2 τ
    refine ⟨?_, ?_⟩
    · dsimp only [B0]; rw [norm_mul]; linarith [mul_le_mul h1.1 h2.1 (norm_nonneg _) zero_le_one]
    · have hd := (h1sub.1.differentiable (by norm_num) τ).hasDerivAt.mul (hbin.1.differentiable (by norm_num) τ).hasDerivAt
      change ‖deriv (oneSubITauInvSqrt * expBinetImag c) τ‖ ≤ 4
      rw [hd.deriv]
      calc ‖deriv oneSubITauInvSqrt τ * expBinetImag c τ + oneSubITauInvSqrt τ * deriv (expBinetImag c) τ‖
          ≤ ‖deriv oneSubITauInvSqrt τ‖ * ‖expBinetImag c τ‖ + ‖oneSubITauInvSqrt τ‖ * ‖deriv (expBinetImag c) τ‖ :=
            (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
        _ ≤ 1 * 2 + 1 * 2 := add_le_add (mul_le_mul h1.2.1 h2.1 (norm_nonneg _) zero_le_one)
            (mul_le_mul h1.1 h2.2.1 (norm_nonneg _) zero_le_one)
        _ = 4 := by norm_num
  let K0 : ℝ → ℂ := fun τ => stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ) * FctPhiKill.phiKill a ((τ : ℂ) * Complex.I)
  have hsg_cd : ContDiffOn ℝ 1 (fun τ : ℝ => stripG ((τ : ℂ) * Complex.I)) (Ioi 0) := by
    have hhank : ContDiffOn ℝ 1 (fun τ : ℝ => -((hankelEdgeM τ : ℝ) : ℂ)) (Ioi 0) :=
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn (CtMDeriv.contDiffOn_hankelEdgeM.of_le (by norm_num)))).neg
    exact hhank.congr fun τ (hτ : 0 < τ) => by rw [stripG_imag_eq_neg_m hτ.ne', abs_of_pos hτ]
  have hpk_cd : ContDiff ℝ 1 (fun τ : ℝ => (L1 : ℂ) * FctPhiKill.phiKill a ((τ : ℂ) * Complex.I)) :=
    contDiff_const.mul ((FctSym.contDiff_phiKill_imag ha0).of_le (by norm_num))
  have hK0_cd : ContDiffOn ℝ 1 K0 (Ioi 0) := hsg_cd.add hpk_cd.contDiffOn
  have hDHG_cd : ContDiffOn ℝ 1 (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) (Ioi 0) :=
    (hEJ.c2.mono fun t (ht : t ∈ Ioi (0 : ℝ)) => (Set.mem_Ioi.mp ht).ne').of_le (by norm_num)
  refine ⟨((hB0_cd.contDiffOn.mul hDHG_cd).mul hK0_cd).congr (fun _ _ => by dsimp only [warpAmpBase, B0, K0]),
    fun {τ} hτ => ?_⟩
  -- Bounds on `K0` and `deriv K0` on `Ioi 0`
  have hsg_bd : ‖stripG ((τ : ℂ) * Complex.I)‖ ≤ τ ^ 2 := by
    rw [stripG_imag_eq_neg_m hτ.ne', abs_of_pos hτ, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hankelEdgeM_nonneg hτ.le)]
    have hπ : π ^ 2 / 12 ≤ 1 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    calc hankelEdgeM τ ≤ π ^ 2 / 12 * τ ^ 2 := hankelEdgeM_le_sq hτ.le
      _ ≤ 1 * τ ^ 2 := by gcongr
      _ = τ ^ 2 := one_mul _
  have ha8 : c ^ (-(2 / 3 : ℝ)) = a ^ 8 := by
    dsimp only [a]; rw [← Real.rpow_natCast, ← Real.rpow_mul hcpos.le]; congr 1; norm_num
  have hpk0_bd : ‖(L1 : ℂ) * FctPhiKill.phiKill a ((τ : ℂ) * Complex.I)‖ ≤ |CL1| * Cpk0 * τ ^ 2 := by
    have hp := hpk0 ha0 (by simp : 0 ≤ ((τ : ℂ) * Complex.I).re)
    rw [show ‖(τ : ℂ) * Complex.I‖ = τ by simp [abs_of_pos hτ]] at hp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hτ1 : τ ≤ 1
    · have hm : min ((τ / a) ^ 8) 1 ≤ (τ / a) ^ 8 := min_le_left _ _
      have h82 : τ ^ 8 ≤ τ ^ 2 := by
        rw [show τ ^ 8 = τ ^ 2 * τ ^ 6 by ring]
        exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hτ.le hτ1)
      have heq : c ^ (-(2 / 3 : ℝ)) * (τ / a) ^ 8 = τ ^ 8 := by rw [ha8, div_pow]; field_simp [ha0.ne']
      calc |L1| * ‖FctPhiKill.phiKill a ((τ : ℂ) * Complex.I)‖
          ≤ (|CL1| * c ^ (-(2 / 3 : ℝ))) * (Cpk0 * (τ / a) ^ 8) :=
            mul_le_mul hL1c' (hp.trans (mul_le_mul_of_nonneg_left hm hCpk0)) (norm_nonneg _) (by positivity)
        _ = |CL1| * Cpk0 * (c ^ (-(2 / 3 : ℝ)) * (τ / a) ^ 8) := by ring
        _ = |CL1| * Cpk0 * τ ^ 8 := by rw [heq]
        _ ≤ |CL1| * Cpk0 * τ ^ 2 := mul_le_mul_of_nonneg_left h82 (by positivity)
    · have hτ1' : 1 ≤ τ := (not_le.mp hτ1).le
      have hm : min ((τ / a) ^ 8) 1 ≤ 1 := min_le_right _ _
      have hc23 : c ^ (-(2 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      have h12 : (1 : ℝ) ≤ τ ^ 2 := by nlinarith
      calc |L1| * ‖FctPhiKill.phiKill a ((τ : ℂ) * Complex.I)‖
          ≤ (|CL1| * 1) * (Cpk0 * 1) :=
            mul_le_mul (hL1c'.trans (by gcongr)) (hp.trans (by gcongr)) (norm_nonneg _) (by positivity)
        _ = |CL1| * Cpk0 * 1 := by ring
        _ ≤ |CL1| * Cpk0 * τ ^ 2 := mul_le_mul_of_nonneg_left h12 (by positivity)
  have hK0_bd : ‖K0 τ‖ ≤ C_k0 * τ ^ 2 := by
    dsimp only [K0, C_k0]
    calc ‖stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ) * FctPhiKill.phiKill a ((τ : ℂ) * Complex.I)‖
        ≤ ‖stripG ((τ : ℂ) * Complex.I)‖ + ‖(L1 : ℂ) * FctPhiKill.phiKill a ((τ : ℂ) * Complex.I)‖ :=
          norm_add_le _ _
      _ ≤ τ ^ 2 + |CL1| * Cpk0 * τ ^ 2 := add_le_add hsg_bd hpk0_bd
      _ = (1 + |CL1| * Cpk0) * τ ^ 2 := by ring
  have hsg_hasD : HasDerivAt (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) (-((hankelEdgeM' τ : ℝ) : ℂ)) τ := by
    have hloc : (fun t : ℝ => -((hankelEdgeM t : ℝ) : ℂ)) =ᶠ[𝓝 τ] fun t : ℝ => stripG ((t : ℂ) * Complex.I) := by
      filter_upwards [isOpen_Ioi.mem_nhds hτ] with t (ht : 0 < t)
      rw [stripG_imag_eq_neg_m ht.ne', abs_of_pos ht]
    exact ((hankelEdgeM_hasDerivAt hτ).ofReal_comp.neg).congr_of_eventuallyEq hloc.symm
  have hpk_hasD : HasDerivAt (fun t : ℝ => (L1 : ℂ) * FctPhiKill.phiKill a ((t : ℂ) * Complex.I))
      ((L1 : ℂ) * deriv (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ) τ :=
    (((FctSym.contDiff_phiKill_imag ha0).differentiable (by simp) τ).hasDerivAt).const_mul _
  have hK0_deriv_bd : ‖deriv K0 τ‖ ≤ C_k1 * τ := by
    have hdK : HasDerivAt K0
        (-((hankelEdgeM' τ : ℝ) : ℂ) + (L1 : ℂ) * deriv (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ) τ :=
      hsg_hasD.add hpk_hasD
    rw [hdK.deriv]
    have h1_sg : ‖-((hankelEdgeM' τ : ℝ) : ℂ)‖ ≤ 2 * τ := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
      have hb := (FctCuspEdge.hankelEdgeM'_bounds hτ)
      have hnn : 0 ≤ hankelEdgeM' τ := le_trans (by positivity) hb.1
      have hπ6 : π ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      rw [abs_of_nonneg hnn]
      calc hankelEdgeM' τ ≤ π ^ 2 / 6 * τ := hb.2.1
        _ ≤ 2 * τ := by gcongr
    have h1_pk : ‖(L1 : ℂ) * deriv (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ‖ ≤ |CL1| * Cpk1 * τ := by
      have hid := FctSym.iteratedDeriv_phiKill_imag ha0 1 τ
      rw [iteratedDeriv_one, iteratedDeriv_one] at hid
      have hpk1' := hpk1 a τ ha0 hτ
      rw [iteratedDeriv_one] at hpk1'
      have hn : ‖deriv (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ‖ =
          ‖deriv (FctPhiKill.phiKill a) ((τ : ℂ) * Complex.I)‖ := by
        rw [hid, norm_mul, pow_one, Complex.norm_I, one_mul]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hn]
      have hmin : c ^ (-(2 / 3 : ℝ)) / τ * min ((τ / a) ^ 8) ((a / τ) ^ 8) ≤ τ := by
        by_cases hτa : τ ≤ a
        · have hm : min ((τ / a) ^ 8) ((a / τ) ^ 8) ≤ (τ / a) ^ 8 := min_le_left _ _
          have ha_le1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
          have hτ1 : τ ≤ 1 := hτa.trans ha_le1
          have h7 : τ ^ 7 ≤ τ := by
            rw [show τ ^ 7 = τ * τ ^ 6 by ring]
            exact mul_le_of_le_one_right hτ.le (pow_le_one₀ hτ.le hτ1)
          calc c ^ (-(2 / 3 : ℝ)) / τ * min ((τ / a) ^ 8) ((a / τ) ^ 8)
              ≤ a ^ 8 / τ * (τ / a) ^ 8 := by rw [ha8]; gcongr
            _ = τ ^ 7 := by rw [div_pow]; field_simp [ha0.ne', hτ.ne']
            _ ≤ τ := h7
        · have haτ : a < τ := lt_of_not_ge hτa
          have hm : min ((τ / a) ^ 8) ((a / τ) ^ 8) ≤ (a / τ) ^ 8 := min_le_right _ _
          have ha_le1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
          have hpow9 : a ^ 16 / τ ^ 9 ≤ τ := by
            have hlt : a ^ 16 / τ ^ 9 < a ^ 7 := by
              have : a ^ 16 / τ ^ 9 < a ^ 16 / a ^ 9 := by gcongr
              refine this.trans_eq ?_; field_simp [ha0.ne']
            have ha7 : a ^ 7 ≤ a := by
              rw [show a ^ 7 = a * a ^ 6 by ring]
              exact mul_le_of_le_one_right ha0.le (pow_le_one₀ ha0.le ha_le1)
            linarith
          calc c ^ (-(2 / 3 : ℝ)) / τ * min ((τ / a) ^ 8) ((a / τ) ^ 8)
              ≤ a ^ 8 / τ * (a / τ) ^ 8 := by rw [ha8]; gcongr
            _ = a ^ 16 / τ ^ 9 := by rw [div_pow]; ring
            _ ≤ τ := hpow9
      have hpk1'' : ‖deriv (FctPhiKill.phiKill a) ((τ : ℂ) * Complex.I)‖ ≤
          Cpk1 / τ * min ((τ / a) ^ 8) ((a / τ) ^ 8) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hτ, mul_comm]; rwa [pow_one] at hpk1'
      calc |L1| * ‖deriv (FctPhiKill.phiKill a) ((τ : ℂ) * Complex.I)‖
          ≤ (|CL1| * c ^ (-(2 / 3 : ℝ))) * (Cpk1 / τ * min ((τ / a) ^ 8) ((a / τ) ^ 8)) :=
            mul_le_mul hL1c' hpk1'' (norm_nonneg _) (by positivity)
        _ = |CL1| * Cpk1 * (c ^ (-(2 / 3 : ℝ)) / τ * min ((τ / a) ^ 8) ((a / τ) ^ 8)) := by ring
        _ ≤ |CL1| * Cpk1 * τ := mul_le_mul_of_nonneg_left hmin (by positivity)
    calc ‖-((hankelEdgeM' τ : ℝ) : ℂ) + (L1 : ℂ) * deriv (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ‖
        ≤ ‖-((hankelEdgeM' τ : ℝ) : ℂ)‖ + ‖(L1 : ℂ) * deriv (fun t : ℝ => FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) τ‖ :=
          norm_add_le _ _
      _ ≤ 2 * τ + |CL1| * Cpk1 * τ := add_le_add h1_sg h1_pk
      _ = C_k1 * τ := by dsimp only [C_k1]; ring
  -- Combine `B0`, `DHG`, `K0`
  have hbD0 := hEJ.b0 τ hτ.ne'
  have hbD1 := hEJ.b1 τ hτ.ne'
  unfold ejW at hbD0 hbD1
  rw [abs_of_pos hτ] at hbD0 hbD1
  simp only [Nat.cast_zero, sub_zero, add_zero, mul_one, Nat.cast_one] at hbD0 hbD1
  have hbB0 := hB0_bd τ
  have hτp2 : τ ^ (-(5 / 2 : ℝ)) * τ ^ 2 = τ ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast τ 2, ← Real.rpow_add hτ]; norm_num
  have hτp1 : τ ^ (-(5 / 2 : ℝ)) * τ = τ ^ (-(3 / 2 : ℝ)) := by
    conv_lhs => arg 2; rw [← Real.rpow_one τ]
    rw [← Real.rpow_add hτ]; norm_num
  have hτp3 : τ ^ (-(5 / 2 : ℝ) - 1) * τ ^ 2 = τ ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast τ 2, ← Real.rpow_add hτ]; norm_num
  have hexp0 : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
  have h10_12 : (1 + τ) ^ 10 ≤ (1 + τ) ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h10_13 : (1 + τ) ^ 10 ≤ (1 + τ) ^ 13 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h11_13 : (1 + τ) ^ (10 + 1) ≤ (1 + τ) ^ 13 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h11τ : τ ^ 2 ≤ (1 + τ) ^ 2 := pow_le_pow_left₀ hτ.le (by linarith) 2
  have hCk01 : C_k0 ≤ C_k0 + C_k1 := by linarith [show 0 ≤ C_k1 by positivity]
  refine ⟨?_, ?_⟩
  · dsimp only [warpAmpBase, B0, K0]
    rw [norm_mul, norm_mul]
    calc ‖oneSubITauInvSqrt τ * expBinetImag c τ‖ *
          ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)‖ * ‖K0 τ‖
        ≤ 2 * (MD * (τ ^ (-(5 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)))) * (C_k0 * τ ^ 2) :=
          mul_le_mul (mul_le_mul hbB0.1 hbD0 (norm_nonneg _) zero_le_two) hK0_bd (norm_nonneg _) (by positivity)
      _ = 2 * MD * C_k0 * (τ ^ (-(5 / 2 : ℝ)) * τ ^ 2) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := by ring
      _ ≤ 6 * MD * (C_k0 + C_k1) * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 12 * Real.exp (-(π * τ)) := by
          rw [hτp2]; gcongr; norm_num
  · -- `deriv warpAmpBase = B0' DHG K0 + B0 DHG' K0 + B0 DHG K0'`
    set DHG := fun t : ℝ => fctDcompAt K4 c α ((t : ℂ) * Complex.I) * ctHG ε ((t : ℂ) * Complex.I)
    have hDHG_da : DifferentiableAt ℝ DHG τ :=
      (hDHG_cd.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hτ)
    have hK0_da : DifferentiableAt ℝ K0 τ :=
      (hK0_cd.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hτ)
    have hB0_da : DifferentiableAt ℝ B0 τ := hB0_cd.differentiable (by simp) τ
    have hder := ((hB0_da.hasDerivAt.mul hDHG_da.hasDerivAt).mul hK0_da.hasDerivAt).deriv
    change ‖deriv (B0 * DHG * K0) τ‖ ≤ _
    rw [hder]
    have hnorm3 : ‖(deriv B0 τ * DHG τ + B0 τ * deriv DHG τ) * K0 τ + B0 τ * DHG τ * deriv K0 τ‖ ≤
        ‖deriv B0 τ‖ * ‖DHG τ‖ * ‖K0 τ‖ + ‖B0 τ‖ * ‖deriv DHG τ‖ * ‖K0 τ‖ + ‖B0 τ‖ * ‖DHG τ‖ * ‖deriv K0 τ‖ := by
      calc ‖(deriv B0 τ * DHG τ + B0 τ * deriv DHG τ) * K0 τ + B0 τ * DHG τ * deriv K0 τ‖
          ≤ ‖(deriv B0 τ * DHG τ + B0 τ * deriv DHG τ) * K0 τ‖ + ‖B0 τ * DHG τ * deriv K0 τ‖ := norm_add_le _ _
        _ = ‖deriv B0 τ * DHG τ + B0 τ * deriv DHG τ‖ * ‖K0 τ‖ + ‖B0 τ‖ * ‖DHG τ‖ * ‖deriv K0 τ‖ := by
            rw [norm_mul, norm_mul, norm_mul]
        _ ≤ (‖deriv B0 τ‖ * ‖DHG τ‖ + ‖B0 τ‖ * ‖deriv DHG τ‖) * ‖K0 τ‖ + ‖B0 τ‖ * ‖DHG τ‖ * ‖deriv K0 τ‖ := by
            have h12 : ‖deriv B0 τ * DHG τ + B0 τ * deriv DHG τ‖ ≤ ‖deriv B0 τ‖ * ‖DHG τ‖ + ‖B0 τ‖ * ‖deriv DHG τ‖ :=
              (norm_add_le _ _).trans (add_le_add (norm_mul _ _).le (norm_mul _ _).le)
            exact add_le_add (mul_le_mul_of_nonneg_right h12 (norm_nonneg _)) le_rfl
        _ = _ := by ring
    have hτ_inv_le : τ ^ (-(1 / 2 : ℝ)) ≤ τ ^ (-(3 / 2 : ℝ)) * (1 + τ) := by
      have : τ ^ (-(1 / 2 : ℝ)) = τ ^ (-(3 / 2 : ℝ)) * τ := by
        conv_rhs => arg 2; rw [← Real.rpow_one τ]
        rw [← Real.rpow_add hτ]; norm_num
      rw [this]; gcongr; linarith
    have ht1 : ‖deriv B0 τ‖ * ‖DHG τ‖ * ‖K0 τ‖ ≤ 4 * MD * C_k0 * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by
      calc ‖deriv B0 τ‖ * ‖DHG τ‖ * ‖K0 τ‖
          ≤ 4 * (MD * (τ ^ (-(5 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)))) * (C_k0 * τ ^ 2) :=
            mul_le_mul (mul_le_mul hbB0.2 hbD0 (norm_nonneg _) (by norm_num)) hK0_bd (norm_nonneg _) (by positivity)
        _ = 4 * MD * C_k0 * (τ ^ (-(5 / 2 : ℝ)) * τ ^ 2) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := by ring
        _ = 4 * MD * C_k0 * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := by rw [hτp2]
        _ ≤ 4 * MD * C_k0 * (τ ^ (-(3 / 2 : ℝ)) * (1 + τ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := by gcongr
        _ = 4 * MD * C_k0 * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 11 * Real.exp (-(π * τ)) := by ring
        _ ≤ 4 * MD * C_k0 * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by gcongr
    have ht2 : ‖B0 τ‖ * ‖deriv DHG τ‖ * ‖K0 τ‖ ≤ 2 * MD * C_k0 * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by
      calc ‖B0 τ‖ * ‖deriv DHG τ‖ * ‖K0 τ‖
          ≤ 2 * (MD * (τ ^ (-(5 / 2 : ℝ) - 1) * (1 + τ) ^ (10 + 1) * Real.exp (-(π * τ)))) * (C_k0 * τ ^ 2) :=
            mul_le_mul (mul_le_mul hbB0.1 hbD1 (norm_nonneg _) zero_le_two) hK0_bd (norm_nonneg _) (by positivity)
        _ = 2 * MD * C_k0 * (τ ^ (-(5 / 2 : ℝ) - 1) * τ ^ 2) * (1 + τ) ^ (10 + 1) * Real.exp (-(π * τ)) := by ring
        _ = 2 * MD * C_k0 * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ (10 + 1) * Real.exp (-(π * τ)) := by rw [hτp3]
        _ ≤ 2 * MD * C_k0 * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by gcongr
    have ht3 : ‖B0 τ‖ * ‖DHG τ‖ * ‖deriv K0 τ‖ ≤ 2 * MD * C_k1 * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by
      calc ‖B0 τ‖ * ‖DHG τ‖ * ‖deriv K0 τ‖
          ≤ 2 * (MD * (τ ^ (-(5 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)))) * (C_k1 * τ) :=
            mul_le_mul (mul_le_mul hbB0.1 hbD0 (norm_nonneg _) zero_le_two) hK0_deriv_bd (norm_nonneg _) (by positivity)
        _ = 2 * MD * C_k1 * (τ ^ (-(5 / 2 : ℝ)) * τ) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := by ring
        _ = 2 * MD * C_k1 * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := by rw [hτp1]
        _ ≤ 2 * MD * C_k1 * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by gcongr
    calc _ ≤ _ := hnorm3
      _ ≤ (4 * MD * C_k0 + 2 * MD * C_k0 + 2 * MD * C_k1) * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by
          linarith [ht1, ht2, ht3]
      _ ≤ C_tot * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by
          dsimp only [C_tot]
          have hnn : 0 ≤ τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by positivity
          have hcc : 4 * MD * C_k0 + 2 * MD * C_k0 + 2 * MD * C_k1 ≤ 6 * MD * (C_k0 + C_k1) := by
            have hmdk : 0 ≤ MD * C_k1 := mul_nonneg hMD0 (by positivity)
            linarith only [hmdk]
          calc (4 * MD * C_k0 + 2 * MD * C_k0 + 2 * MD * C_k1) * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ))
              = (4 * MD * C_k0 + 2 * MD * C_k0 + 2 * MD * C_k1) * (τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by ring
            _ ≤ (6 * MD * (C_k0 + C_k1)) * (τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by gcongr
            _ = _ := by ring

/-- `C¹` cusp bounds on `Ioi 0` for `warpAmpRight` (`term1` amplitude):
`‖warpAmpRight‖ ≤ C c⁻¹ τ^{1/2} (1+τ)^{13} e^{-πτ}`, `‖deriv warpAmpRight‖ ≤ C c⁻¹ τ^{-1/2} (1+τ)^{13} e^{-πτ}`. -/
lemma warpAmpRight_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 32 ^ 4 ≤ c₀ ∧ ∀ {ε c : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ContDiffOn ℝ 1 (warpAmpRight K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (fctRightTail h ε c)) (Ioi 0) ∧
      ∀ {τ : ℝ}, 0 < τ →
        ‖warpAmpRight K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (fctRightTail h ε c) τ‖ ≤
          C * c⁻¹ * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) ∧
        ‖deriv (warpAmpRight K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (fctRightTail h ε c)) τ‖ ≤
          C * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by
  obtain ⟨CB, c0B, hCB0, hc0B, hB⟩ := warpAmpBase_bounds hK4 h
  obtain ⟨CR, c0R, hCR0, _, hRT⟩ := fctRightTail_bounds hK4 h
  refine ⟨2 * CB * CR, max c0B c0R, by positivity, hc0B.trans (le_max_left _ _), fun {ε c} hε hc => ?_⟩
  obtain ⟨hB_cd, hB_bd⟩ := hB hε ((le_max_left _ _).trans hc)
  obtain ⟨hR_cd, hR_bd⟩ := hRT ε c hε ((le_max_right _ _).trans hc)
  have hcpos : 0 < c := by linarith [hc0B.trans ((le_max_left _ _).trans hc)]
  refine ⟨hB_cd.mul (hR_cd.of_le (by norm_num)).contDiffOn, fun {τ} hτ => ?_⟩
  obtain ⟨hB0, hB1⟩ := hB_bd hτ
  obtain ⟨hR0, hR1, _⟩ := hR_bd τ
  rw [abs_of_pos hτ] at hR0
  have hτ_12 : τ ^ (-(1 / 2 : ℝ)) * τ = τ ^ (1 / 2 : ℝ) := by
    conv_lhs => arg 2; rw [← Real.rpow_one τ]
    rw [← Real.rpow_add hτ]; norm_num
  have hτ_32 : τ ^ (-(3 / 2 : ℝ)) * τ = τ ^ (-(1 / 2 : ℝ)) := by
    conv_lhs => arg 2; rw [← Real.rpow_one τ]
    rw [← Real.rpow_add hτ]; norm_num
  have hexp0 : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
  have h12_13 : (1 + τ) ^ 12 ≤ (1 + τ) ^ 13 := pow_le_pow_right₀ (by linarith) (by norm_num)
  refine ⟨?_, ?_⟩
  · dsimp only [warpAmpRight]
    rw [norm_mul]
    calc _ ≤ (CB * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 12 * Real.exp (-(π * τ))) * (CR * c⁻¹ * τ) :=
          mul_le_mul hB0 hR0 (norm_nonneg _) (by positivity)
      _ = CB * CR * c⁻¹ * (τ ^ (-(1 / 2 : ℝ)) * τ) * (1 + τ) ^ 12 * Real.exp (-(π * τ)) := by ring
      _ ≤ 2 * CB * CR * c⁻¹ * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by
          rw [hτ_12]; gcongr; linarith
  · have hda : DifferentiableAt ℝ (warpAmpBase K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)) τ :=
      (hB_cd.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hτ)
    have hdr : DifferentiableAt ℝ (fctRightTail h ε c) τ := hR_cd.differentiable (by norm_num) τ
    have hder := (hda.hasDerivAt.mul hdr.hasDerivAt).deriv
    change ‖deriv (warpAmpBase K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) * fctRightTail h ε c) τ‖ ≤ _
    rw [hder]
    have ht1 : ‖deriv (warpAmpBase K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)) τ‖ * ‖fctRightTail h ε c τ‖ ≤
        CB * CR * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by
      calc _ ≤ (CB * τ ^ (-(3 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) * (CR * c⁻¹ * τ) :=
            mul_le_mul hB1 hR0 (norm_nonneg _) (by positivity)
        _ = CB * CR * c⁻¹ * (τ ^ (-(3 / 2 : ℝ)) * τ) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by ring
        _ = _ := by rw [hτ_32]
    have ht2 : ‖warpAmpBase K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ‖ * ‖deriv (fctRightTail h ε c) τ‖ ≤
        CB * CR * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by
      calc _ ≤ (CB * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 12 * Real.exp (-(π * τ))) * (CR * c⁻¹) :=
            mul_le_mul hB0 hR1 (norm_nonneg _) (by positivity)
        _ = CB * CR * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 12 * Real.exp (-(π * τ)) := by ring
        _ ≤ CB * CR * c⁻¹ * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by gcongr
    calc ‖deriv _ τ * fctRightTail h ε c τ + warpAmpBase _ _ _ _ _ τ * deriv (fctRightTail h ε c) τ‖
        ≤ ‖deriv _ τ‖ * ‖fctRightTail h ε c τ‖ + ‖warpAmpBase _ _ _ _ _ τ‖ * ‖deriv (fctRightTail h ε c) τ‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ _ := by linarith

private lemma integrableOn_rpow_poly13_exp (s : ℝ) (hs : -1 < s) (cM : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧
      IntegrableOn (fun τ : ℝ => cM * τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ))) (Ioi 0) ∧
      ∫ τ in Ioi (0 : ℝ), cM * τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ)) ≤ |cM| * M := by
  have h_ae : AEStronglyMeasurable (fun τ : ℝ => τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ)))
      (volume.restrict (Ioi 0)) :=
    (ContinuousOn.aestronglyMeasurable
      (((ContinuousOn.rpow_const continuousOn_id fun τ (hτ : 0 < τ) => Or.inl hτ.ne').mul
        ((continuous_const.add continuous_id).pow 13).continuousOn).mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_id : Continuous (fun τ : ℝ => τ))).neg).continuousOn)
      measurableSet_Ioi)
  have i1 : IntegrableOn (fun τ : ℝ => (2 : ℝ) ^ 13 * τ ^ s) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      ((intervalIntegral.intervalIntegrable_rpow' hs).const_mul ((2 : ℝ) ^ 13))
  have i2 : IntegrableOn (fun τ : ℝ => τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ))) (Ioi 1) := by
    rcases le_or_gt s 0 with hs0 | hs0
    · have hi13 := (integrable_pow_mul_exp_neg_pi 13).integrableOn (s := Ioi (1 : ℝ))
      refine hi13.mono' (h_ae.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ (hτ : 1 < τ) => ?_
      have hτs : τ ^ s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ.le hs0
      have hτsn : 0 ≤ τ ^ s := Real.rpow_nonneg (by linarith) _
      have hexp : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hτsn (by positivity)) hexp), abs_of_pos (by linarith)]
      calc τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ))
          ≤ 1 * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by gcongr
        _ = (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by ring
    · obtain ⟨k, hk⟩ := exists_nat_gt s
      have hk_int := (integrable_pow_mul_exp_neg_pi (k + 13)).integrableOn (s := Ioi (1 : ℝ))
      refine hk_int.mono' (h_ae.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ (hτ : 1 < τ) => ?_
      have hτsk : τ ^ s ≤ (1 + τ) ^ k := by
        calc τ ^ s ≤ τ ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hτ.le hk.le
          _ = τ ^ k := Real.rpow_natCast τ k
          _ ≤ (1 + τ) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      have hτsn : 0 ≤ τ ^ s := Real.rpow_nonneg (by linarith) _
      have hexp : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hτsn (by positivity)) hexp), abs_of_pos (by linarith)]
      calc τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ))
          ≤ (1 + τ) ^ k * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by gcongr
        _ = (1 + τ) ^ (k + 13) * Real.exp (-(π * τ)) := by rw [pow_add]
  have hbase_int : IntegrableOn (fun τ : ℝ => τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ))) (Ioi 0) := by
    have h1 : IntegrableOn (fun τ : ℝ => τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ))) (Ioc 0 1) := by
      refine i1.mono' (h_ae.mono_set Ioc_subset_Ioi_self) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun τ (hτ : τ ∈ Ioc 0 1) => ?_
      have h1τ : (1 + τ) ^ 13 ≤ (2 : ℝ) ^ 13 := pow_le_pow_left₀ (by linarith [hτ.1]) (by linarith [hτ.2]) 13
      have hexp : Real.exp (-(π * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hτ.1])
      have hτn : 0 ≤ τ ^ s := Real.rpow_nonneg hτ.1.le _
      have hexp0 : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
      have h13_nn : 0 ≤ (1 + τ) ^ 13 := pow_nonneg (by linarith [hτ.1]) 13
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hτn h13_nn) hexp0)]
      calc τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ))
          ≤ τ ^ s * 2 ^ 13 * 1 := by gcongr
        _ = (2 : ℝ) ^ 13 * τ ^ s := by ring
    have hU : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi zero_le_one
    rw [← hU]
    exact h1.union i2
  refine ⟨∫ τ in Ioi (0 : ℝ), τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ)),
    setIntegral_nonneg measurableSet_Ioi fun τ (hτ : 0 < τ) =>
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hτ.le _) (by positivity)) (Real.exp_pos _).le, ?_, ?_⟩
  · exact MeasureTheory.IntegrableOn.congr_fun (hbase_int.const_mul cM) (fun _ _ => by ring) measurableSet_Ioi
  · have heq : ∫ τ in Ioi (0 : ℝ), cM * τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ)) =
        cM * ∫ τ in Ioi (0 : ℝ), τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by
      rw [← MeasureTheory.integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun τ _ => by ring
    rw [heq]
    have hnn : 0 ≤ ∫ τ in Ioi (0 : ℝ), τ ^ s * (1 + τ) ^ 13 * Real.exp (-(π * τ)) :=
      setIntegral_nonneg measurableSet_Ioi fun τ (hτ : 0 < τ) =>
        mul_nonneg (mul_nonneg (Real.rpow_nonneg hτ.le _) (by positivity)) (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right (le_abs_self cM) hnn

private lemma right_ibp_limit {P g : ℝ → ℂ} {ω : ℝ} (hω : ω ≠ 0)
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

/-- Integrability, `O(c^{-1/2})` `L^1`-norm, derivative, and decay bounds for `warpP`. -/
lemma warpP_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ CP c₀ : ℝ, 0 ≤ CP ∧ 32 ^ 4 ≤ c₀ ∧ ∀ {ε c : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      let L1 := fctWarpL1 h ε c
      let α := fctWarpAlpha h ε c
      IntegrableOn (fctWarpIntegrand K4 ε c L1 α) (Ioi 0) ∧
      IntegrableOn (warpP K4 ε c L1 α) (Ioi 0) ∧
      (∫ τ in Ioi (0 : ℝ), ‖warpP K4 ε c L1 α τ‖) ≤ CP * c ^ (-(1 / 2 : ℝ)) ∧
      (∀ {τ : ℝ}, 0 < τ → ‖warpP K4 ε c L1 α τ‖ ≤ CP) ∧
      (∀ {τ : ℝ}, 1 ≤ τ → ‖warpP K4 ε c L1 α τ‖ ≤ CP * c⁻¹ * (1 + τ) ^ 10 * Real.exp (-(π * τ))) ∧
      (∀ {τ : ℝ}, 0 < τ → HasDerivAt (warpP K4 ε c L1 α) (Complex.I * fctWarpIntegrand K4 ε c L1 α τ) τ) ∧
      Tendsto (warpP K4 ε c L1 α) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (warpP K4 ε c L1 α) atTop (𝓝 0) := by
  obtain ⟨Ms, c0Ps, hMs0, _, hPsi_s⟩ := fctPsi_imag_small_bound hK4 h
  obtain ⟨Mlg, c0lg, hMlg0, _, hPsi_lg⟩ := fctPsi_imag_large_bound hK4 h
  have hτD_pos : 0 < (FctCompD.fct_comp_D_part1 FctCompD.StripKernelChoice.star).choose :=
    (FctCompD.fct_comp_D_part1 FctCompD.StripKernelChoice.star).choose_spec.1
  obtain ⟨cτ, hcτ⟩ := eventually_atTop.mp
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually (Iic_mem_nhds hτD_pos))
  set c0W := h.choose_spec.choose
  obtain ⟨M10_int, _, h10_int, h10_le⟩ := integrableOn_rpow_poly13_exp 0 (by norm_num) 1
  have hexp10_bd : ∃ M10_pt : ℝ, 0 ≤ M10_pt ∧ ∀ τ : ℝ, 0 ≤ τ →
      (1 + τ) ^ 10 * Real.exp (-(π * τ)) ≤ M10_pt := by
    refine ⟨(Nat.factorial 10 : ℝ) / π ^ 10 * Real.exp π, by positivity, fun τ hτ => ?_⟩
    have hu : 0 ≤ π * (1 + τ) := by positivity
    have hpow := Real.pow_div_factorial_le_exp (π * (1 + τ)) hu 10
    have h10 : (1 + τ) ^ 10 ≤ (Nat.factorial 10 : ℝ) / π ^ 10 * Real.exp (π * (1 + τ)) := by
      have hmul : (π * (1 + τ)) ^ 10 / (Nat.factorial 10 : ℝ) =
          (π ^ 10 / (Nat.factorial 10 : ℝ)) * (1 + τ) ^ 10 := by rw [mul_pow]; ring
      rw [hmul] at hpow
      calc (1 + τ) ^ 10 = (π ^ 10 / (Nat.factorial 10 : ℝ))⁻¹ * ((π ^ 10 / (Nat.factorial 10 : ℝ)) * (1 + τ) ^ 10) := by
            field_simp [Real.pi_ne_zero]
        _ ≤ (π ^ 10 / (Nat.factorial 10 : ℝ))⁻¹ * Real.exp (π * (1 + τ)) := by gcongr
        _ = ((Nat.factorial 10 : ℝ) / π ^ 10) * Real.exp (π * (1 + τ)) := by field_simp
    calc (1 + τ) ^ 10 * Real.exp (-(π * τ))
        ≤ ((Nat.factorial 10 : ℝ) / π ^ 10 * Real.exp (π * (1 + τ))) * Real.exp (-(π * τ)) := by gcongr
      _ = (Nat.factorial 10 : ℝ) / π ^ 10 * (Real.exp (π * (1 + τ)) * Real.exp (-(π * τ))) := by ring
      _ = (Nat.factorial 10 : ℝ) / π ^ 10 * Real.exp π := by
          rw [← Real.exp_add]; congr 2; ring
  obtain ⟨M10_pt, hM10_pt0, hM10_pt⟩ := hexp10_bd
  set CP : ℝ := Ms + 2048 * Mlg + M10_int * Mlg + M10_pt * Mlg + 1
  set c₀ : ℝ := max (max c0Ps c0lg) (max (max cτ c0W) (32 ^ 4))
  refine ⟨CP, c₀, by positivity, le_max_of_le_right (le_max_right _ _), fun {ε c} hε hc => ?_⟩
  have hcPs : c0Ps ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hclg : c0lg ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hcTau : cτ ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
  have hcW : c0W ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
  have hc32 : (32 : ℝ) ^ 4 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hcpos : 0 < c := by linarith only [hc32]
  have hc1 : 1 ≤ c := by linarith only [hc32]
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set r : ℝ := c ^ (-(1 / 3 : ℝ))
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hcpos _
  have hr_le1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hpair := fctWarpPair_spec h hε hcW
  have hzero_int : IntegrableOn (fctWarpIntegrand K4 ε c L1 α) (Ioi 0) := hpair.2.1
  have hzero_eq : ∫ τ in Ioi (0 : ℝ), fctWarpIntegrand K4 ε c L1 α τ = 0 := by
    have hI0 : Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrand K4 ε c L1 α τ = 0 := hpair.2.2
    exact (mul_eq_zero.mp hI0).resolve_left Complex.I_ne_zero
  have hI_cont : ContinuousOn (fctWarpIntegrand K4 ε c L1 α) (Ioi 0) :=
    fctWarpIntegrand_continuousOn hK4 hcpos (hcτ c hcTau)
  have hP_hasDeriv : ∀ {τ : ℝ}, 0 < τ →
      HasDerivAt (warpP K4 ε c L1 α) (Complex.I * fctWarpIntegrand K4 ε c L1 α τ) τ := fun {τ} hτ => by
    have ha0 : 0 < τ / 2 := half_pos hτ
    have hInt0 : IntervalIntegrable (fctWarpIntegrand K4 ε c L1 α) volume 0 (τ / 2) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha0.le).mpr (hzero_int.mono_set fun _ ht => ht.1)
    let C0 := ∫ t in (0 : ℝ)..(τ / 2), fctWarpIntegrand K4 ε c L1 α t
    have hP_eq_int : ∀ {t : ℝ}, 0 < t → warpP K4 ε c L1 α t = Complex.I * ∫ s in (0 : ℝ)..t, fctWarpIntegrand K4 ε c L1 α s := by
      intro t ht
      unfold warpP fctPsi
      have hne := mellinK0_ne_zero c (by simp : ((t : ℂ) * Complex.I).re < 1) (fctXi1 L1)
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      have hcomp := intervalIntegral.integral_comp_mul_right
        (fun s : ℝ => fctWarpIntegrand K4 ε c L1 α s) ht.ne' (a := (0 : ℝ)) (b := (1 : ℝ))
      simp only [zero_mul, one_mul] at hcomp
      have hint_eq : (∫ s in (0 : ℝ)..1, mellinK0 c ((s : ℂ) * ((t : ℂ) * Complex.I)) (fctXi1 L1) *
          fctWarpA K4 ε c L1 α ((s : ℂ) * ((t : ℂ) * Complex.I))) =
          ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * t) := by
        refine intervalIntegral.integral_congr fun s _ => ?_
        unfold fctWarpIntegrand
        rw [show (s : ℂ) * ((t : ℂ) * Complex.I) = ((s * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [hint_eq, show ((t : ℂ) * Complex.I) * ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * t) =
          Complex.I * ((t : ℝ) • ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * t)) by
        rw [Complex.real_smul]; ring, hcomp, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hloc : (fun t => Complex.I * (C0 + ∫ s in (τ / 2)..t, fctWarpIntegrand K4 ε c L1 α s)) =ᶠ[𝓝 τ]
        warpP K4 ε c L1 α := by
      filter_upwards [eventually_gt_nhds (by linarith : τ / 2 < τ)] with t ht
      have ht_i0 : IntervalIntegrable (fctWarpIntegrand K4 ε c L1 α) volume (τ / 2) t :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr
          (hzero_int.mono_set (fun u hu => lt_trans ha0 hu.1))
      rw [hP_eq_int (by linarith : 0 < t), ← intervalIntegral.integral_add_adjacent_intervals hInt0 ht_i0]
    have hInt_τ : IntervalIntegrable (fctWarpIntegrand K4 ε c L1 α) volume (τ / 2) τ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
        (hzero_int.mono_set (fun u hu => lt_trans ha0 hu.1))
    have hderiv_int := intervalIntegral.integral_hasDerivAt_right hInt_τ
      ⟨Ioi 0, isOpen_Ioi.mem_nhds hτ, hI_cont.aestronglyMeasurable measurableSet_Ioi⟩
      ((hI_cont τ hτ).continuousAt (isOpen_Ioi.mem_nhds hτ))
    exact ((hderiv_int.const_add C0).const_mul Complex.I).congr_of_eventuallyEq hloc.symm
  have hP_cont : ContinuousOn (warpP K4 ε c L1 α) (Ioi 0) := fun τ hτ =>
    (hP_hasDeriv hτ).continuousAt.continuousWithinAt
  have hPs := hPsi_s ε c (fctXi1 L1) hε hcPs (fctXi1_pos L1)
  have hPlg := hPsi_lg ε c (fctXi1 L1) hε hclg (fctXi1_pos L1)
  have hP_sm : ∀ {τ : ℝ}, 0 < τ → τ ≤ r → ‖warpP K4 ε c L1 α τ‖ ≤ Ms * τ ^ (1 / 2 : ℝ) := by
    intro τ hτ hτr
    have hbd := hPs τ hτ.ne' (by rwa [abs_of_pos hτ])
    have hnorm : ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
        ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ = c * ‖warpP K4 ε c L1 α τ‖ := by
      unfold warpP
      rw [show mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)) =
          (c : ℂ) * (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
    rw [hnorm, abs_of_pos hτ] at hbd
    exact le_of_mul_le_mul_left (by linarith [hbd]) hcpos
  have hP_lg : ∀ {τ : ℝ}, r < τ →
      ‖warpP K4 ε c L1 α τ‖ ≤ Mlg * c⁻¹ * τ ^ (-(5 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := by
    intro τ hτr
    have hτ : 0 < τ := hr_pos.trans hτr
    have hbd := hPlg τ hτ.ne'
    have hnorm : ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
        ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ = c * ‖warpP K4 ε c L1 α τ‖ := by
      unfold warpP
      rw [show mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)) =
          (c : ℂ) * (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
    rw [hnorm, abs_of_pos hτ] at hbd
    have hdiv := div_le_div_of_nonneg_right hbd hcpos.le
    rw [mul_div_cancel_left₀ _ hcpos.ne'] at hdiv
    exact hdiv.trans_eq (by ring)
  have hP_ge1 : ∀ {τ : ℝ}, 1 ≤ τ → ‖warpP K4 ε c L1 α τ‖ ≤ CP * c⁻¹ * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := by
    intro τ hτ1
    have hc_gt1 : (1 : ℝ) < c := by linarith only [hc32]
    have hr_lt1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hc_gt1 (by norm_num)
    have hlt : r < τ := lt_of_lt_of_le hr_lt1 hτ1
    have hτp : τ ^ (-(5 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)
    have hexp0 : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
    have hMC : Mlg ≤ CP := by
      have h10p : 0 ≤ M10_pt * Mlg := mul_nonneg hM10_pt0 hMlg0
      have h10i : 0 ≤ M10_int * Mlg := mul_nonneg (by positivity) hMlg0
      dsimp only [CP]; linarith only [hMs0, hMlg0, h10p, h10i]
    have h1p : 0 ≤ (1 + τ) ^ 10 := pow_nonneg (by linarith only [hτ1]) 10
    have hc_inv0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hcpos.le
    calc ‖warpP K4 ε c L1 α τ‖
        ≤ Mlg * c⁻¹ * τ ^ (-(5 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := hP_lg hlt
      _ ≤ Mlg * c⁻¹ * 1 * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := by gcongr
      _ = Mlg * c⁻¹ * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := by ring
      _ ≤ CP * c⁻¹ * (1 + τ) ^ 10 * Real.exp (-(π * τ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hMC hc_inv0) h1p) hexp0
  have hP_bd : ∀ {τ : ℝ}, 0 < τ → ‖warpP K4 ε c L1 α τ‖ ≤ CP := fun {τ} hτ => by
    have h10p : 0 ≤ M10_pt * Mlg := mul_nonneg hM10_pt0 hMlg0
    have h10i : 0 ≤ M10_int * Mlg := mul_nonneg (by positivity) hMlg0
    by_cases hτr : τ ≤ r
    · have hrp : τ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hτ.le (hτr.trans hr_le1) (by norm_num)
      have hMs_le : Ms ≤ CP := by dsimp only [CP]; linarith only [hMlg0, h10p, h10i]
      calc ‖warpP K4 ε c L1 α τ‖ ≤ Ms * τ ^ (1 / 2 : ℝ) := hP_sm hτ hτr
        _ ≤ Ms * 1 := by gcongr
        _ = Ms := mul_one _
        _ ≤ CP := hMs_le
    · have hlt : r < τ := lt_of_not_ge hτr
      by_cases hτ1 : τ ≤ 1
      · have h52 : τ ^ (-(5 / 2 : ℝ)) ≤ c ^ (5 / 6 : ℝ) := by
          rw [show (c ^ (5 / 6 : ℝ)) = r ^ (-(5 / 2 : ℝ)) by
            dsimp only [r]; rw [← Real.rpow_mul hcpos.le]; congr 1; norm_num]
          exact Real.rpow_le_rpow_of_nonpos hr_pos hlt.le (by norm_num)
        have h1τ : (1 + τ) ^ 10 ≤ 2 ^ 10 := pow_le_pow_left₀ (by linarith only [hτ]) (by linarith only [hτ1]) 10
        have hexp : Real.exp (-(π * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [Real.pi_pos, hτ])
        have hc56 : c⁻¹ * c ^ (5 / 6 : ℝ) ≤ 1 := by
          rw [← Real.rpow_neg_one c, ← Real.rpow_add hcpos]
          exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
        have h210 : Mlg * 2 ^ 10 ≤ CP := by
          have h2p10 : (2 : ℝ) ^ 10 = 1024 := by norm_num
          rw [h2p10]; dsimp only [CP]; linarith only [hMs0, hMlg0, h10p, h10i]
        calc ‖warpP K4 ε c L1 α τ‖
            ≤ Mlg * c⁻¹ * τ ^ (-(5 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := hP_lg hlt
          _ ≤ Mlg * c⁻¹ * c ^ (5 / 6 : ℝ) * 2 ^ 10 * 1 := by gcongr
          _ = Mlg * 2 ^ 10 * (c⁻¹ * c ^ (5 / 6 : ℝ)) := by ring
          _ ≤ Mlg * 2 ^ 10 * 1 := by gcongr
          _ = Mlg * 2 ^ 10 := mul_one _
          _ ≤ CP := h210
      · have h1τ : 1 ≤ τ := (not_le.mp hτ1).le
        have hexp0 : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
        have hM10_le : Mlg * M10_pt ≤ CP := by
          rw [mul_comm Mlg M10_pt]; dsimp only [CP]; linarith only [hMs0, hMlg0, h10i]
        calc ‖warpP K4 ε c L1 α τ‖
            ≤ Mlg * c⁻¹ * τ ^ (-(5 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := hP_lg hlt
          _ ≤ Mlg * 1 * 1 * ((1 + τ) ^ 10 * Real.exp (-(π * τ))) := by
              have hinv1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
              have htp : τ ^ (-(5 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1τ (by norm_num)
              have h1p : 0 ≤ (1 + τ) ^ 10 := pow_nonneg (by linarith only [h1τ]) 10
              rw [mul_assoc (Mlg * c⁻¹ * τ ^ (-(5 / 2 : ℝ))) ((1 + τ) ^ 10) _]
              gcongr
          _ ≤ Mlg * 1 * 1 * M10_pt := by gcongr; exact hM10_pt τ hτ.le
          _ = Mlg * M10_pt := by ring
          _ ≤ CP := hM10_le
  -- Dominate `warpP` by 3-piece integrable majorant on `Ioi 0`
  let g_dom : ℝ → ℝ := fun τ =>
    (Ioc 0 r).indicator (fun _ => Ms * r ^ (1 / 2 : ℝ)) τ +
    (Ioc r 1).indicator (fun t => Mlg * c⁻¹ * 2 ^ 10 * t ^ (-(5 / 2 : ℝ))) τ +
    (Ioi 1).indicator (fun t => Mlg * c⁻¹ * (1 + t) ^ 10 * Real.exp (-(π * t))) τ
  have hg1 : IntegrableOn (fun _ : ℝ => Ms * r ^ (1 / 2 : ℝ)) (Ioc 0 r) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hg2 : IntegrableOn (fun t : ℝ => Mlg * c⁻¹ * 2 ^ 10 * t ^ (-(5 / 2 : ℝ))) (Ioc r 1) := by
    have hpow : IntegrableOn (fun t : ℝ => t ^ (-(5 / 2 : ℝ))) (Ioc r 1) := by
      refine (ContinuousOn.integrableOn_Icc (ContinuousOn.rpow_const continuousOn_id fun t ht =>
        Or.inl (lt_of_lt_of_le hr_pos ht.1).ne')).mono_set Ioc_subset_Icc_self
    exact hpow.const_mul (Mlg * c⁻¹ * 2 ^ 10)
  have hg3 : IntegrableOn (fun t : ℝ => Mlg * c⁻¹ * (1 + t) ^ 10 * Real.exp (-(π * t))) (Ioi 1) :=
    MeasureTheory.IntegrableOn.congr_fun
      (((integrable_pow_mul_exp_neg_pi 10).integrableOn (s := Ioi (1 : ℝ))).const_mul (Mlg * c⁻¹))
      (fun t (ht : 1 < t) => by rw [abs_of_pos (by linarith only [ht])]; ring) measurableSet_Ioi
  have h1i : IntegrableOn (fun τ => (Ioc 0 r).indicator (fun _ => Ms * r ^ (1 / 2 : ℝ)) τ) (Ioi 0) :=
    (hg1.integrable_indicator measurableSet_Ioc).integrableOn
  have h2i : IntegrableOn (fun τ => (Ioc r 1).indicator (fun t => Mlg * c⁻¹ * 2 ^ 10 * t ^ (-(5 / 2 : ℝ))) τ) (Ioi 0) :=
    (hg2.integrable_indicator measurableSet_Ioc).integrableOn
  have h3i : IntegrableOn (fun τ => (Ioi 1).indicator (fun t => Mlg * c⁻¹ * (1 + t) ^ 10 * Real.exp (-(π * t))) τ) (Ioi 0) :=
    (hg3.integrable_indicator measurableSet_Ioi).integrableOn
  have hg_dom_int : IntegrableOn g_dom (Ioi 0) := (h1i.add h2i).add h3i
  have hP_dom : ∀ τ ∈ Ioi (0 : ℝ), ‖warpP K4 ε c L1 α τ‖ ≤ g_dom τ := fun τ (hτ : 0 < τ) => by
    dsimp only [g_dom]
    by_cases h1 : τ ≤ r
    · have hm : τ ∈ Ioc 0 r := ⟨hτ, h1⟩
      have hnot2 : τ ∉ Ioc r 1 := fun h => not_lt_of_ge h1 h.1
      have hnot3 : τ ∉ Ioi 1 := fun h => not_lt_of_ge (h1.trans hr_le1) h
      simp only [Set.indicator_of_mem hm, Set.indicator_of_notMem hnot2, Set.indicator_of_notMem hnot3, add_zero]
      exact (hP_sm hτ h1).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hτ.le h1 (by norm_num)) hMs0)
    · have hrlt : r < τ := lt_of_not_ge h1
      by_cases h2 : τ ≤ 1
      · have hm : τ ∈ Ioc r 1 := ⟨hrlt, h2⟩
        have hnot1 : τ ∉ Ioc 0 r := fun h => h1 h.2
        have hnot3 : τ ∉ Ioi 1 := fun h => not_lt_of_ge h2 h
        simp only [Set.indicator_of_notMem hnot1, Set.indicator_of_mem hm, Set.indicator_of_notMem hnot3, zero_add, add_zero]
        have h1τ : (1 + τ) ^ 10 ≤ 2 ^ 10 := pow_le_pow_left₀ (by linarith only [hτ]) (by linarith only [h2]) 10
        have hexp : Real.exp (-(π * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [Real.pi_pos, hτ])
        calc ‖warpP K4 ε c L1 α τ‖
            ≤ Mlg * c⁻¹ * τ ^ (-(5 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := hP_lg hrlt
          _ ≤ Mlg * c⁻¹ * τ ^ (-(5 / 2 : ℝ)) * 2 ^ 10 * 1 := by gcongr
          _ = Mlg * c⁻¹ * 2 ^ 10 * τ ^ (-(5 / 2 : ℝ)) := by ring
      · have h1lt : 1 < τ := lt_of_not_ge h2
        have hnot1 : τ ∉ Ioc 0 r := fun h => not_lt_of_ge (h.2.trans hr_le1) h1lt
        have hnot2 : τ ∉ Ioc r 1 := fun h => h2 h.2
        have hm3 : τ ∈ Ioi (1 : ℝ) := h1lt
        simp only [Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot2,
          Set.indicator_of_mem hm3, zero_add]
        have htp : τ ^ (-(5 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1lt.le (by norm_num)
        have hexp0 : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
        have h1p : 0 ≤ (1 + τ) ^ 10 := pow_nonneg (by linarith only [h1lt]) 10
        have hc_inv0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hcpos.le
        calc ‖warpP K4 ε c L1 α τ‖
            ≤ Mlg * c⁻¹ * τ ^ (-(5 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := hP_lg hrlt
          _ ≤ Mlg * c⁻¹ * 1 * (1 + τ) ^ 10 * Real.exp (-(π * τ)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left htp (mul_nonneg hMlg0 hc_inv0)) h1p) hexp0
          _ = Mlg * c⁻¹ * (1 + τ) ^ 10 * Real.exp (-(π * τ)) := by ring
  have hP_int : IntegrableOn (warpP K4 ε c L1 α) (Ioi 0) :=
    hg_dom_int.mono' (hP_cont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => hP_dom τ hτ)
  have hP_L1_le : (∫ τ in Ioi (0 : ℝ), ‖warpP K4 ε c L1 α τ‖) ≤ CP * c ^ (-(1 / 2 : ℝ)) := by
    have h1 := setIntegral_mono_on hP_int.norm hg_dom_int measurableSet_Ioi fun τ hτ => hP_dom τ hτ
    have hi1 : ∫ τ in Ioi (0 : ℝ), (Ioc 0 r).indicator (fun _ => Ms * r ^ (1 / 2 : ℝ)) τ =
        Ms * c ^ (-(1 / 2 : ℝ)) := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_self_of_subset_right (show Ioc 0 r ⊆ Ioi 0 from fun _ h => h.1),
        setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hr_pos.le, sub_zero]
      have hrr : r * r ^ (1 / 2 : ℝ) = c ^ (-(1 / 2 : ℝ)) := by
        dsimp only [r]
        conv_lhs => arg 1; rw [← Real.rpow_one (c ^ (-(1 / 3 : ℝ)))]
        rw [← Real.rpow_add hr_pos, ← Real.rpow_mul hcpos.le]; congr 1; norm_num
      calc r * (Ms * r ^ (1 / 2 : ℝ)) = Ms * (r * r ^ (1 / 2 : ℝ)) := by ring
        _ = Ms * c ^ (-(1 / 2 : ℝ)) := by rw [hrr]
    have hi2 : ∫ τ in Ioi (0 : ℝ), (Ioc r 1).indicator (fun t => Mlg * c⁻¹ * 2 ^ 10 * t ^ (-(5 / 2 : ℝ))) τ ≤
        2 ^ 11 * Mlg * c ^ (-(1 / 2 : ℝ)) := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_self_of_subset_right (show Ioc r 1 ⊆ Ioi 0 from fun _ h => hr_pos.trans h.1),
        ← intervalIntegral.integral_of_le hr_le1, intervalIntegral.integral_const_mul]
      have hnot0 : (0 : ℝ) ∉ uIcc r 1 := by
        rw [uIcc_of_le hr_le1]; exact fun h => (hr_pos.trans_le h.1).false
      have hint := _root_.integral_rpow (a := r) (b := 1) (r := -(5 / 2 : ℝ)) (Or.inr ⟨by norm_num, hnot0⟩)
      rw [hint, Real.one_rpow]
      have hr32 : r ^ (-(5 / 2 : ℝ) + 1) = c ^ (1 / 2 : ℝ) := by
        dsimp only [r]; rw [← Real.rpow_mul hcpos.le]; congr 1; norm_num
      rw [hr32]
      have hval : (1 - c ^ (1 / 2 : ℝ)) / (-(5 / 2 : ℝ) + 1) ≤ (2 / 3 : ℝ) * c ^ (1 / 2 : ℝ) := by
        have hEq : (1 - c ^ (1 / 2 : ℝ)) / (-(5 / 2 : ℝ) + 1) = (2 / 3 : ℝ) * c ^ (1 / 2 : ℝ) - 2 / 3 := by ring
        linarith only [hEq]
      have hcc : c⁻¹ * c ^ (1 / 2 : ℝ) = c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
      calc Mlg * c⁻¹ * 2 ^ 10 * ((1 - c ^ (1 / 2 : ℝ)) / (-(5 / 2 : ℝ) + 1))
          ≤ Mlg * c⁻¹ * 2 ^ 10 * ((2 / 3 : ℝ) * c ^ (1 / 2 : ℝ)) := by gcongr
        _ = (2 / 3 : ℝ) * 2 ^ 10 * Mlg * (c⁻¹ * c ^ (1 / 2 : ℝ)) := by ring
        _ ≤ 2 ^ 11 * Mlg * c ^ (-(1 / 2 : ℝ)) := by rw [hcc]; gcongr; norm_num
    have hi3 : ∫ τ in Ioi (0 : ℝ), (Ioi 1).indicator (fun t => Mlg * c⁻¹ * (1 + t) ^ 10 * Real.exp (-(π * t))) τ ≤
        M10_int * Mlg * c ^ (-(1 / 2 : ℝ)) := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi,
        Set.inter_eq_self_of_subset_right (Ioi_subset_Ioi zero_le_one)]
      have hdom0 : ∫ τ in Ioi (1 : ℝ), Mlg * c⁻¹ * (1 + τ) ^ 10 * Real.exp (-(π * τ)) ≤
          ∫ τ in Ioi (0 : ℝ), (Mlg * c⁻¹) * (1 * τ ^ (0 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by
        calc ∫ τ in Ioi (1 : ℝ), Mlg * c⁻¹ * (1 + τ) ^ 10 * Real.exp (-(π * τ))
            ≤ ∫ τ in Ioi (1 : ℝ), (Mlg * c⁻¹) * (1 * τ ^ (0 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by
              refine setIntegral_mono_on hg3 ((h10_int.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul (Mlg * c⁻¹))
                measurableSet_Ioi fun τ (hτ : 1 < τ) => ?_
              have hexp0 : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
              have h13 : (1 + τ) ^ 10 ≤ (1 + τ) ^ 13 := pow_le_pow_right₀ (by linarith only [hτ]) (by norm_num)
              rw [Real.rpow_zero]
              calc Mlg * c⁻¹ * (1 + τ) ^ 10 * Real.exp (-(π * τ))
                  ≤ Mlg * c⁻¹ * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := by gcongr
                _ = (Mlg * c⁻¹) * (1 * 1 * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by ring
          _ ≤ ∫ τ in Ioi (0 : ℝ), (Mlg * c⁻¹) * (1 * τ ^ (0 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by
              refine setIntegral_mono_set (h10_int.const_mul (Mlg * c⁻¹))
                (ae_restrict_of_forall_mem measurableSet_Ioi fun τ (hτ : 0 < τ) => ?_)
                (Eventually.of_forall (Ioi_subset_Ioi zero_le_one))
              have hτ0 : 0 ≤ τ ^ (0 : ℝ) := Real.rpow_nonneg hτ.le _
              have h1τ : 0 ≤ (1 + τ) ^ 13 := pow_nonneg (by linarith only [hτ]) 13
              have hexp : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
              exact mul_nonneg (mul_nonneg hMlg0 (inv_nonneg.mpr hcpos.le))
                (mul_nonneg (mul_nonneg (mul_nonneg zero_le_one hτ0) h1τ) hexp)
      have hc_12 : c⁻¹ ≤ c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_neg_one c]
        exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      calc ∫ τ in Ioi (1 : ℝ), Mlg * c⁻¹ * (1 + τ) ^ 10 * Real.exp (-(π * τ))
          ≤ ∫ τ in Ioi (0 : ℝ), (Mlg * c⁻¹) * (1 * τ ^ (0 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := hdom0
        _ = (Mlg * c⁻¹) * ∫ τ in Ioi (0 : ℝ), 1 * τ ^ (0 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ (Mlg * c⁻¹) * (|1| * M10_int) := by gcongr
        _ = M10_int * Mlg * c⁻¹ := by norm_num; ring
        _ ≤ M10_int * Mlg * c ^ (-(1 / 2 : ℝ)) := by gcongr
    have hsum : ∫ τ in Ioi (0 : ℝ), g_dom τ =
        (∫ τ in Ioi (0 : ℝ), (Ioc 0 r).indicator (fun _ => Ms * r ^ (1 / 2 : ℝ)) τ) +
        (∫ τ in Ioi (0 : ℝ), (Ioc r 1).indicator (fun t => Mlg * c⁻¹ * 2 ^ 10 * t ^ (-(5 / 2 : ℝ))) τ) +
        (∫ τ in Ioi (0 : ℝ), (Ioi 1).indicator (fun t => Mlg * c⁻¹ * (1 + t) ^ 10 * Real.exp (-(π * t))) τ) := by
      have ha : ∫ τ in Ioi (0 : ℝ),
          ((Ioc 0 r).indicator (fun _ => Ms * r ^ (1 / 2 : ℝ)) τ +
            (Ioc r 1).indicator (fun t => Mlg * c⁻¹ * 2 ^ 10 * t ^ (-(5 / 2 : ℝ))) τ) =
          (∫ τ in Ioi (0 : ℝ), (Ioc 0 r).indicator (fun _ => Ms * r ^ (1 / 2 : ℝ)) τ) +
          (∫ τ in Ioi (0 : ℝ), (Ioc r 1).indicator (fun t => Mlg * c⁻¹ * 2 ^ 10 * t ^ (-(5 / 2 : ℝ))) τ) :=
        integral_add h1i h2i
      have hb : ∫ τ in Ioi (0 : ℝ), g_dom τ =
          (∫ τ in Ioi (0 : ℝ),
            ((Ioc 0 r).indicator (fun _ => Ms * r ^ (1 / 2 : ℝ)) τ +
              (Ioc r 1).indicator (fun t => Mlg * c⁻¹ * 2 ^ 10 * t ^ (-(5 / 2 : ℝ))) τ)) +
          (∫ τ in Ioi (0 : ℝ), (Ioi 1).indicator (fun t => Mlg * c⁻¹ * (1 + t) ^ 10 * Real.exp (-(π * t))) τ) :=
        integral_add (h1i.add h2i) h3i
      rw [hb, ha]
    have hMC_L1 : Ms + 2048 * Mlg + M10_int * Mlg ≤ CP := by
      have h10p : 0 ≤ M10_pt * Mlg := mul_nonneg hM10_pt0 hMlg0
      dsimp only [CP]; linarith only [h10p]
    have hc12nn : 0 ≤ c ^ (-(1 / 2 : ℝ)) := by positivity
    calc ∫ τ in Ioi (0 : ℝ), ‖warpP K4 ε c L1 α τ‖
        ≤ ∫ τ in Ioi (0 : ℝ), g_dom τ := h1
      _ = _ := hsum
      _ ≤ Ms * c ^ (-(1 / 2 : ℝ)) + 2 ^ 11 * Mlg * c ^ (-(1 / 2 : ℝ)) + M10_int * Mlg * c ^ (-(1 / 2 : ℝ)) := by
          linarith only [hi1, hi2, hi3]
      _ = (Ms + 2048 * Mlg + M10_int * Mlg) * c ^ (-(1 / 2 : ℝ)) := by norm_num; ring
      _ ≤ CP * c ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hMC_L1 hc12nn
  have hP_lim0 : Tendsto (warpP K4 ε c L1 α) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hsq : Tendsto (fun τ : ℝ => Ms * τ ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun τ : ℝ => τ ^ (1 / 2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ (1 / 2 : ℝ))) :=
        (Real.continuous_rpow_const (by norm_num)).continuousWithinAt
      rw [Real.zero_rpow (by norm_num)] at h0
      simpa [mul_zero] using h0.const_mul Ms
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [Ioc_mem_nhdsGT hr_pos] with τ hτ
    exact hP_sm hτ.1 hτ.2
  have hP_limTop : Tendsto (warpP K4 ε c L1 α) atTop (𝓝 0) := by
    have hint_lim : Tendsto (fun τ : ℝ => ∫ t in (0 : ℝ)..τ, fctWarpIntegrand K4 ε c L1 α t) atTop
        (𝓝 (∫ t in Ioi (0 : ℝ), fctWarpIntegrand K4 ε c L1 α t)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hzero_int tendsto_id
    rw [hzero_eq] at hint_lim
    have hmul := hint_lim.const_mul Complex.I
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ (hτ : 0 < τ)
    unfold warpP fctPsi
    have hne := mellinK0_ne_zero c (by simp : ((τ : ℂ) * Complex.I).re < 1) (fctXi1 L1)
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    have hcomp := intervalIntegral.integral_comp_mul_right
      (fun s : ℝ => fctWarpIntegrand K4 ε c L1 α s) hτ.ne' (a := (0 : ℝ)) (b := (1 : ℝ))
    simp only [zero_mul, one_mul] at hcomp
    have hint_eq : (∫ s in (0 : ℝ)..1, mellinK0 c ((s : ℂ) * ((τ : ℂ) * Complex.I)) (fctXi1 L1) *
        fctWarpA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I))) =
        ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * τ) := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      unfold fctWarpIntegrand
      rw [show (s : ℂ) * ((τ : ℂ) * Complex.I) = ((s * τ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [hint_eq, show ((τ : ℂ) * Complex.I) * ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * τ) =
        Complex.I * ((τ : ℝ) • ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * τ)) by
      rw [Complex.real_smul]; ring, hcomp, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  exact ⟨hzero_int, hP_int, hP_L1_le, fun {τ} hτ => hP_bd hτ, fun {τ} hτ => hP_ge1 hτ,
    fun {τ} hτ => hP_hasDeriv hτ, hP_lim0, hP_limTop⟩

/-- First term (`P' R`) after 1-step IBP of `warpRightTailDensity`. -/
noncomputable def warpRightTailTerm1 {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c ξ : ℝ) : ℝ :=
  (1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (Real.log (π ^ 2 * ξ) - fctWarpL1 h ε c)) *
    ((c ^ (1 / 3 : ℝ) / π) *
      (∫ τ in Ioi (0 : ℝ), mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        fctWarpA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) *
        fctRightTail h ε c τ).re)

/-- Second term (`P R'`) after 1-step IBP of `warpRightTailDensity`. -/
noncomputable def warpRightTailTerm2 {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c ξ : ℝ) : ℝ :=
  -((1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (Real.log (π ^ 2 * ξ) - fctWarpL1 h ε c)) *
    ((c ^ (1 / 3 : ℝ) / π) *
      (Complex.I * ∫ τ in Ioi (0 : ℝ),
        Complex.exp (Complex.I * ((c * (Real.log (π ^ 2 * ξ) - fctWarpL1 h ε c) * τ : ℝ) : ℂ)) *
          warpP K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
          deriv (fctRightTail h ε c) τ).re))

/-- 1-step IBP splitting of `warpRightTailDensity` for `L = log(π² ξ) ≠ L₁`:
`warpRightTailDensity h ε c ξ = warpRightTailTerm1 h ε c ξ + warpRightTailTerm2 h ε c ξ`. -/
lemma warpRightTail_first_ibp {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ : ℝ, 32 ^ 4 ≤ c₀ ∧ ∀ {ε c ξ : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      Real.log (π ^ 2 * ξ) ≠ fctWarpL1 h ε c →
      IntegrableOn (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          fctWarpA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) *
          fctRightTail h ε c τ) (Ioi 0) ∧
      IntegrableOn (fun τ : ℝ => Complex.exp (Complex.I * ((c * (Real.log (π ^ 2 * ξ) - fctWarpL1 h ε c) * τ : ℝ) : ℂ)) *
          warpP K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
          deriv (fctRightTail h ε c) τ) (Ioi 0) ∧
      warpRightTailDensity h ε c ξ = warpRightTailTerm1 h ε c ξ + warpRightTailTerm2 h ε c ξ := by
  obtain ⟨c0N, _, hNc⟩ := fctNcC_eq_fctNc hK4 h
  obtain ⟨CR, c0R, hCR0, _, hRT⟩ := fctRightTail_bounds hK4 h
  obtain ⟨CP, c0P, hCP0, hc0P, hP_main⟩ := warpP_bounds hK4 h
  obtain ⟨CWR, c0WR, hCWR0, hc0WR, hWR⟩ := warpAmpRight_bounds hK4 h
  obtain ⟨c0s, _, hSetup⟩ := fctSplitting_setup hK4 (fctDescent_uncond hK4 h)
  obtain ⟨c0C, hConj⟩ := fctPhiHat_conj hK4 (fctDescent_uncond hK4 h)
  obtain ⟨Ms, c0Ps, hMs0, _, hPsi_s⟩ := fctPsi_imag_small_bound hK4 h
  obtain ⟨Mlg, c0lg, hMlg0, _, hPsi_lg⟩ := fctPsi_imag_large_bound hK4 h
  obtain ⟨c0C2, hC2⟩ := fctPhiHat_left_c2 hK4 (fctDescent_uncond hK4 h)
  obtain ⟨ML, c0L, _, _, hLT⟩ := fctLeftTail_deriv_bounds hK4 h
  obtain ⟨MD, c0D, _, _, hDHG⟩ := dcomp_ctHG_EJ hK4 h
  obtain ⟨M_12, _, hI_12, _⟩ := integrableOn_rpow_poly13_exp (1 / 2) (by norm_num) 1
  set c₀ : ℝ := max (max (max c0N c0R) (max c0P c0WR))
    (max (max c0s c0C) (max (max c0Ps c0lg) (max c0C2 (max c0L c0D))))
  refine ⟨c₀, le_trans hc0P ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))),
    fun {ε c ξ} hε hc hξ hLne => ?_⟩
  have hcN : c0N ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hc))
  have hcR : c0R ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hc))
  have hcP : c0P ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc))
  have hcWR : c0WR ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc))
  have hcs : c0s ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
  have hcC : c0C ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
  have hcPs : c0Ps ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hclg : c0lg ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hcC2 : c0C2 ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc)))
  have hcL : c0L ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))))
  have hcD : c0D ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))))
  have hc32 : 32 ^ 4 ≤ c := hc0P.trans hcP
  have hcpos : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set L := Real.log (π ^ 2 * ξ)
  set ω := c * (L - L1)
  have hω_ne : ω ≠ 0 := mul_ne_zero hcpos.ne' (sub_ne_zero.mpr hLne)
  obtain ⟨hzero_int, hP_int, _, hP_bd, hP_ge1, hP_deriv, hP_lim0, hP_limTop⟩ := hP_main hε hcP
  obtain ⟨hR_cd, hR_bd⟩ := hRT ε c hε hcR
  obtain ⟨hWR_cd, hWR_bd⟩ := hWR hε hcWR
  obtain ⟨hNc_eq, hNc_lo, _, hNc_ne⟩ := hNc ε c hε hcN
  have hNc_pos : 0 < fctNc h ε c := by linarith
  have hNc_inv : ‖(fctNc h ε c : ℂ)⁻¹‖ ≤ 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNc_pos]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith [hNc_lo])
  have hD_conj := (hSetup ε c hε hcs).2.2.2.2.2
  have hPsi_s' := hPsi_s ε c ξ hε hcPs hξ
  have hPsi_lg' := hPsi_lg ε c ξ hε hclg hξ
  have hc2' := hC2 ε c hε hcC2
  obtain ⟨hLT_cd, _, _⟩ := hLT ε c hε hcL
  have hEJ := hDHG ε c hε hcD
  set Nc : ℂ := (fctNc h ε c : ℂ)
  set F_R : ℝ → ℂ := fun τ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
    ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctRightTail h ε c τ)
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
  have hm_cont : Continuous (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ) :=
    continuous_mellinK0_imag hcpos hξ
  have hF_R_cont : ContinuousOn F_R {τ : ℝ | τ ≠ 0} := by
    refine ContinuousOn.congr
      ((hm_cont.continuousOn.mul ((hc2'.continuousOn.sub hLT_cd.continuous.continuousOn).mul hEJ.c2.continuousOn)).mul
        hR_cd.continuous.continuousOn)
      fun τ hτ => ?_
    simp only [Pi.mul_apply, Pi.sub_apply, F_R]; rw [← hMain_eq τ hτ]; ring
  have hF_R_int : Integrable F_R := by
    set r := c ^ (-(1 / 3 : ℝ))
    have hr_pos : 0 < r := Real.rpow_pos_of_pos hcpos _
    have hr_le1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    set M := max (2 * Ms * c * (CR * c⁻¹ * r)) (2 * Mlg * (max r⁻¹ 1) ^ (5 / 2 : ℝ) * (CR * c⁻¹))
    have hM0 : 0 ≤ M := by positivity
    have h_ae : AEStronglyMeasurable F_R volume := by
      have hcomp0 : ∀ᵐ τ : ℝ, τ ∈ {τ : ℝ | τ ≠ 0} := by
        rw [ae_iff]; simp only [Set.mem_ofPred_eq, ne_eq, not_not]; exact Real.volume_singleton
      exact (Measure.restrict_eq_self_of_ae_mem hcomp0) ▸ hF_R_cont.aestronglyMeasurable isOpen_ne.measurableSet
    have hg1 : Integrable (fun τ : ℝ => (Icc (-r) r).indicator (fun _ => M) τ) :=
      (integrableOn_const (hs := measure_Icc_lt_top.ne) (C := M)).integrable_indicator measurableSet_Icc
    have hg2 : Integrable (fun τ : ℝ =>
        (Icc (-r) r)ᶜ.indicator (fun t => M * ((1 + |t|) ^ 12 * Real.exp (-(π * |t|)))) τ) :=
      ((integrable_pow_mul_exp_neg_pi 12).const_mul M).indicator measurableSet_Icc.compl
    refine (hg1.add hg2).mono' h_ae ?_
    have hcomp0 : ∀ᵐ τ : ℝ, τ ≠ 0 := by
      rw [ae_iff]; simp only [ne_eq, not_not]; exact Real.volume_singleton
    filter_upwards [hcomp0] with τ hτ
    have hFnorm : ‖F_R τ‖ = ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))‖ *
        (‖Nc⁻¹‖ * ‖fctRightTail h ε c τ‖) := by
      dsimp only [F_R]
      rw [show mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc * fctRightTail h ε c τ) =
          (mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))) * (Nc⁻¹ * fctRightTail h ε c τ) by ring,
        norm_mul, norm_mul Nc⁻¹ _]
    by_cases hτr : |τ| ≤ r
    · have hτmem : τ ∈ Icc (-r) r := abs_le.mp hτr
      have h1 : (Icc (-r) r).indicator (fun _ : ℝ => M) τ = M := Set.indicator_of_mem hτmem _
      have h2 : (Icc (-r) r)ᶜ.indicator (fun t : ℝ => M * ((1 + |t|) ^ 12 * Real.exp (-(π * |t|)))) τ = 0 :=
        Set.indicator_of_notMem (by simp [hτmem]) _
      change ‖F_R τ‖ ≤ (Icc (-r) r).indicator (fun _ => M) τ +
        (Icc (-r) r)ᶜ.indicator (fun t => M * ((1 + |t|) ^ 12 * Real.exp (-(π * |t|)))) τ
      rw [h1, h2, add_zero, hFnorm]
      have hrp1 : |τ| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg τ) (hτr.trans hr_le1) (by norm_num)
      calc _ ≤ (Ms * c * |τ| ^ (1 / 2 : ℝ)) * (2 * (CR * c⁻¹ * |τ|)) :=
            mul_le_mul (hPsi_s' τ hτ hτr) (mul_le_mul hNc_inv (hR_bd τ).1 (norm_nonneg _) (by positivity))
              (by positivity) (by positivity)
        _ ≤ (Ms * c * 1) * (2 * (CR * c⁻¹ * r)) := by gcongr
        _ = 2 * Ms * c * (CR * c⁻¹ * r) := by ring
        _ ≤ M := le_max_left _ _
    · have hlt : r < |τ| := lt_of_not_ge hτr
      have hτpos : 0 < |τ| := hr_pos.trans hlt
      have hτnot : τ ∉ Icc (-r) r := fun h => hτr (abs_le.mpr h)
      have h1 : (Icc (-r) r).indicator (fun _ : ℝ => M) τ = 0 := Set.indicator_of_notMem hτnot _
      have h2 : (Icc (-r) r)ᶜ.indicator (fun t : ℝ => M * ((1 + |t|) ^ 12 * Real.exp (-(π * |t|)))) τ =
          M * ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) := Set.indicator_of_mem hτnot _
      change ‖F_R τ‖ ≤ (Icc (-r) r).indicator (fun _ => M) τ +
        (Icc (-r) r)ᶜ.indicator (fun t => M * ((1 + |t|) ^ 12 * Real.exp (-(π * |t|)))) τ
      rw [h1, h2, zero_add, hFnorm]
      have hpow_neg : |τ| ^ (-(5 / 2 : ℝ)) ≤ (max r⁻¹ 1) ^ (5 / 2 : ℝ) := by
        rw [Real.rpow_neg hτpos.le, ← Real.inv_rpow hτpos.le]
        exact Real.rpow_le_rpow (by positivity) ((inv_anti₀ hr_pos hlt.le).trans (le_max_left _ _)) (by norm_num)
      have h10_12 : (1 + |τ|) ^ 10 * |τ| ≤ (1 + |τ|) ^ 12 := by
        have h1 : |τ| ≤ 1 + |τ| := by linarith
        have h2 : (1 + |τ|) ^ 10 * (1 + |τ|) = (1 + |τ|) ^ 11 := by ring
        calc (1 + |τ|) ^ 10 * |τ| ≤ (1 + |τ|) ^ 10 * (1 + |τ|) := by gcongr
          _ = (1 + |τ|) ^ 11 := h2
          _ ≤ (1 + |τ|) ^ 12 := pow_le_pow_right₀ (by linarith [abs_nonneg τ]) (by norm_num)
      have hexp0 : 0 ≤ Real.exp (-(π * |τ|)) := (Real.exp_pos _).le
      calc _ ≤ (Mlg * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) * (2 * (CR * c⁻¹ * |τ|)) :=
            mul_le_mul (hPsi_lg' τ hτ) (mul_le_mul hNc_inv (hR_bd τ).1 (norm_nonneg _) (by positivity))
              (by positivity) (by positivity)
        _ = (2 * Mlg * |τ| ^ (-(5 / 2 : ℝ)) * (CR * c⁻¹)) * ((1 + |τ|) ^ 10 * |τ|) * Real.exp (-(π * |τ|)) := by ring
        _ ≤ (2 * Mlg * (max r⁻¹ 1) ^ (5 / 2 : ℝ) * (CR * c⁻¹)) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by gcongr
        _ ≤ M * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by gcongr; exact le_max_right _ _
        _ = M * ((1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) := by ring
  have hFR_conj : ∀ τ : ℝ, F_R (-τ) = starRingEnd ℂ (F_R τ) := fun τ => by
    dsimp only [F_R]
    have hci : ((-τ : ℝ) : ℂ) * Complex.I = starRingEnd ℂ ((τ : ℂ) * Complex.I) := by simp
    have h1ci : 1 - ((-τ : ℝ) : ℂ) * Complex.I = starRingEnd ℂ (1 - (τ : ℂ) * Complex.I) := by simp
    have hRconj : fctRightTail h ε c (-τ) = starRingEnd ℂ (fctRightTail h ε c τ) := by
      unfold fctRightTail
      rw [h1ci, hConj ε c hε hcC _ (by simp [CtOuter.closedStrip]), map_sub, map_one]
    rw [hci, mellinK0_conj c hξ (by simp), fctPsi_conj hD_conj (by simp) (by simp), hRconj]
    dsimp only [Nc, α]
    simp only [map_mul, map_div₀, Complex.conj_ofReal]
  have hRe_int : (∫ τ : ℝ, F_R τ).re = 2 * (∫ τ in Ioi (0 : ℝ), F_R τ).re := by
    have hre1 : (∫ τ : ℝ, F_R τ).re = ∫ τ : ℝ, (F_R τ).re := Complex.reCLM.integral_comp_comm hF_R_int |>.symm
    have hre2 : (∫ τ in Ioi (0 : ℝ), F_R τ).re = ∫ τ in Ioi (0 : ℝ), (F_R τ).re :=
      Complex.reCLM.integral_comp_comm hF_R_int.integrableOn |>.symm
    have hF_re_int : Integrable (fun τ : ℝ => (F_R τ).re) volume := Complex.reCLM.integrable_comp hF_R_int
    have hsplit_zero := MeasureTheory.integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hF_re_int
    have hiic : ∫ τ in (Ioi (0 : ℝ))ᶜ, (F_R τ).re = ∫ τ in Ioi (0 : ℝ), (F_R τ).re := by
      have hneg := integral_comp_neg_Ioi (f := fun τ : ℝ => (F_R (-τ)).re) (0 : ℝ)
      rw [neg_zero] at hneg
      have hc_eq : (Ioi (0 : ℝ))ᶜ = Iic (0 : ℝ) := by ext τ; simp
      rw [hc_eq]
      simpa only [hFR_conj, Complex.conj_re] using hneg.symm
    rw [hre1, hre2, ← hsplit_zero, hiic]; ring
  have hexp_cont : Continuous (fun τ : ℝ => Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul (edgePhi_contDiff' L).continuous)))
  have hexp_ω_cont : Continuous (fun τ : ℝ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  have hterm1_int : IntegrableOn (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) * fctRightTail h ε c τ) (Ioi 0) := by
    have h_ae : AEStronglyMeasurable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) * fctRightTail h ε c τ) (volume.restrict (Ioi 0)) := by
      refine (ContinuousOn.congr (hexp_cont.continuousOn.mul hWR_cd.continuousOn) fun τ _ => ?_).aestronglyMeasurable
        measurableSet_Ioi
      simp only [Pi.mul_apply]
      simpa only [L, L1, α] using warpAmpRight_eq_integrand K4 ε c L1 α (fctRightTail h ε c) hξ
    refine (hI_12.const_mul (CWR * c⁻¹)).mono' h_ae ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ (hτ : 0 < τ) => ?_
    rw [warpAmpRight_eq_integrand K4 ε c L1 α (fctRightTail h ε c) hξ, norm_mul,
      show ‖Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ))‖ = 1 by
        rw [Complex.norm_exp]; simp [Complex.mul_re], one_mul]
    calc ‖warpAmpRight K4 ε c L1 α (fctRightTail h ε c) τ‖
        ≤ CWR * c⁻¹ * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) := (hWR_bd hτ).1
      _ = CWR * c⁻¹ * (1 * τ ^ (1 / 2 : ℝ) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by ring
  have hP_cont : ContinuousOn (warpP K4 ε c L1 α) (Ioi 0) := fun τ hτ =>
    (hP_deriv hτ).continuousAt.continuousWithinAt
  have hterm2_int : IntegrableOn (fun τ : ℝ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) *
      warpP K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ) (Ioi 0) := by
    have h_ae : AEStronglyMeasurable (fun τ : ℝ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) *
        warpP K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ) (volume.restrict (Ioi 0)) :=
      ((hexp_ω_cont.continuousOn.mul hP_cont).mul (hR_cd.continuous_deriv (by norm_num)).continuousOn).aestronglyMeasurable
        measurableSet_Ioi
    refine (hP_int.norm.const_mul (CR * c⁻¹)).mono' h_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ _
    have hexp1 : ‖Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp [Complex.mul_re]
    rw [norm_mul, norm_mul, hexp1, one_mul]
    calc ‖warpP K4 ε c L1 α τ‖ * ‖deriv (fctRightTail h ε c) τ‖
        ≤ ‖warpP K4 ε c L1 α τ‖ * (CR * c⁻¹) := mul_le_mul_of_nonneg_left (hR_bd τ).2.1 (norm_nonneg _)
      _ = (CR * c⁻¹) * ‖warpP K4 ε c L1 α τ‖ := by ring
  refine ⟨hterm1_int, hterm2_int, ?_⟩
  let P_R : ℝ → ℂ := fun τ => warpP K4 ε c L1 α τ * fctRightTail h ε c τ
  let g_R : ℝ → ℂ := fun τ => fctWarpIntegrand K4 ε c L1 α τ * fctRightTail h ε c τ -
    Complex.I * warpP K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ
  have hgR_int : IntegrableOn g_R (Ioi 0) := by
    have h1 : IntegrableOn (fun τ => fctWarpIntegrand K4 ε c L1 α τ * fctRightTail h ε c τ) (Ioi 0) := by
      have hm_exp : IntegrableOn (fun τ => (Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)))⁻¹ *
          (mellinK0 c ((τ : ℂ) * Complex.I) ξ * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) *
            fctRightTail h ε c τ)) (Ioi 0) :=
        Integrable.mono hterm1_int
          (((hexp_ω_cont.continuousOn.inv₀ fun τ _ => Complex.exp_ne_zero _).aestronglyMeasurable
            measurableSet_Ioi).mul hterm1_int.aestronglyMeasurable)
          (ae_of_all _ fun τ => by
            rw [norm_mul, norm_inv, show ‖Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ = 1 by
              rw [Complex.norm_exp]; simp [Complex.mul_re], inv_one, one_mul])
      refine hm_exp.congr_fun (fun τ _ => ?_) measurableSet_Ioi
      dsimp only; unfold fctWarpIntegrand
      rw [mellinK0_imag_shift (L1 := L1) hξ]
      have hexp0 : Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
      change (Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)))⁻¹ * _ = _
      dsimp only [ω, L]; push_cast; field_simp [hexp0]
    have h2 : IntegrableOn (fun τ => Complex.I * warpP K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ) (Ioi 0) := by
      have h_ae : AEStronglyMeasurable (fun τ => Complex.I * warpP K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ)
          (volume.restrict (Ioi 0)) :=
        ((continuous_const.continuousOn.mul hP_cont).mul
          (hR_cd.continuous_deriv (by norm_num)).continuousOn).aestronglyMeasurable measurableSet_Ioi
      refine (hP_int.norm.const_mul (CR * c⁻¹)).mono' h_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ _
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
      calc ‖warpP K4 ε c L1 α τ‖ * ‖deriv (fctRightTail h ε c) τ‖
          ≤ ‖warpP K4 ε c L1 α τ‖ * (CR * c⁻¹) := mul_le_mul_of_nonneg_left (hR_bd τ).2.1 (norm_nonneg _)
        _ = (CR * c⁻¹) * ‖warpP K4 ε c L1 α τ‖ := by ring
    exact h1.sub h2
  have hPR_exp_int : IntegrableOn (fun τ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P_R τ) (Ioi 0) := by
    have hcn : c / fctNc h ε c ≠ 0 := div_ne_zero hcpos.ne' hNc_pos.ne'
    have hmul : IntegrableOn (fun τ => ((c / fctNc h ε c : ℝ) : ℂ)⁻¹ * F_R τ) (Ioi 0) :=
      (hF_R_int.integrableOn (s := Ioi (0 : ℝ))).const_mul _
    refine hmul.congr_fun (fun τ _ => ?_) measurableSet_Ioi
    dsimp only [F_R, P_R, warpP]
    rw [mellinK0_imag_shift (L1 := L1) hξ]
    have hne : ((c / fctNc h ε c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcn
    have hc_ne_C : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
    have hNcC_ne : (fctNc h ε c : ℂ) ≠ 0 := hNc_ne
    dsimp only [Nc, ω, L]; push_cast; field_simp [hne, hc_ne_C, hNcC_ne]
  have hGR_exp_int : IntegrableOn (fun τ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g_R τ) (Ioi 0) := by
    have hdiff := hterm1_int.sub (hterm2_int.const_mul Complex.I)
    refine hdiff.congr_fun (fun τ _ => ?_) measurableSet_Ioi
    dsimp only [g_R, Pi.sub_apply]; unfold fctWarpIntegrand
    rw [mellinK0_imag_shift (L1 := L1) hξ]
    dsimp only [ω]; push_cast; ring
  have hPR_deriv : ∀ τ : ℝ, 0 < τ → HasDerivAt P_R (Complex.I * g_R τ) τ := fun τ hτ => by
    have hp := hP_deriv hτ
    have hr := (hR_cd.differentiable (by norm_num) τ).hasDerivAt
    have hmul := hp.mul hr
    convert hmul using 1
    dsimp only [g_R]; ring_nf; rw [Complex.I_sq]; ring
  have hPR_lim0 : Tendsto P_R (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h0 : Tendsto (fun τ : ℝ => ‖warpP K4 ε c L1 α τ‖ * (CR * c⁻¹ * |τ|)) (𝓝[>] 0) (𝓝 0) := by
      have ha : Tendsto (fun τ : ℝ => ‖warpP K4 ε c L1 α τ‖) (𝓝[>] 0) (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mp hP_lim0
      have hb : Tendsto (fun τ : ℝ => CR * c⁻¹ * |τ|) (𝓝[>] 0) (𝓝 0) := by
        simpa [mul_zero, abs_zero] using ((continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).const_mul (CR * c⁻¹)
      simpa using ha.mul hb
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
      (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun τ => ?_)
    dsimp only [P_R]; rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hR_bd τ).1 (norm_nonneg _)
  have hPR_limTop : Tendsto P_R atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hexp_lim : Tendsto (fun τ : ℝ => (CP * c⁻¹ * (CR * c⁻¹)) * ((2 ^ 11 / π ^ 11) * ((π * τ) ^ 11 * Real.exp (-(π * τ))))) atTop (𝓝 0) := by
      have ht : Tendsto (fun τ : ℝ => (π * τ) ^ 11 * Real.exp (-(π * τ))) atTop (𝓝 0) :=
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 11).comp (tendsto_id.const_mul_atTop Real.pi_pos)
      simpa using (ht.const_mul (2 ^ 11 / π ^ 11)).const_mul (CP * c⁻¹ * (CR * c⁻¹))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp_lim
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with τ (hτ : 1 ≤ τ)
    dsimp only [P_R]; rw [norm_mul]
    have hP1 := hP_ge1 hτ
    have hR1 := (hR_bd τ).1
    rw [abs_of_pos (by linarith)] at hR1
    have h10_11 : (1 + τ) ^ 10 * τ ≤ (2 ^ 11 / π ^ 11) * (π * τ) ^ 11 := by
      have h12 : 1 + τ ≤ 2 * τ := by linarith
      have h10_11' : (1 + τ) ^ 10 * τ ≤ (2 * τ) ^ 10 * (2 * τ) := by
        have h1 : τ ≤ 2 * τ := by linarith
        exact mul_le_mul (pow_le_pow_left₀ (by linarith) h12 10) h1 (by linarith) (by positivity)
      calc (1 + τ) ^ 10 * τ ≤ (2 * τ) ^ 10 * (2 * τ) := h10_11'
        _ = (2 ^ 11 / π ^ 11) * (π * τ) ^ 11 := by rw [mul_pow, mul_pow]; field_simp [Real.pi_ne_zero]
    have hexp0 : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
    calc ‖warpP K4 ε c L1 α τ‖ * ‖fctRightTail h ε c τ‖
        ≤ (CP * c⁻¹ * (1 + τ) ^ 10 * Real.exp (-(π * τ))) * (CR * c⁻¹ * τ) :=
          mul_le_mul hP1 hR1 (norm_nonneg _) (by positivity)
      _ = (CP * c⁻¹ * (CR * c⁻¹)) * ((1 + τ) ^ 10 * τ * Real.exp (-(π * τ))) := by ring
      _ ≤ (CP * c⁻¹ * (CR * c⁻¹)) * ((2 ^ 11 / π ^ 11) * ((π * τ) ^ 11 * Real.exp (-(π * τ)))) := by
          have := mul_le_mul_of_nonneg_right h10_11 hexp0
          calc (CP * c⁻¹ * (CR * c⁻¹)) * ((1 + τ) ^ 10 * τ * Real.exp (-(π * τ)))
              ≤ (CP * c⁻¹ * (CR * c⁻¹)) * ((2 ^ 11 / π ^ 11) * (π * τ) ^ 11 * Real.exp (-(π * τ))) := by gcongr
            _ = _ := by ring
  have hibp := right_ibp_limit hω_ne hgR_int hPR_exp_int hGR_exp_int hPR_deriv hPR_lim0 hPR_limTop
  have huctCAi_neg : uctCAi < 0 := by
    unfold uctCAi; have := ceCs_pos; have := Real.pi_pos; rw [neg_div]; exact neg_neg_iff_pos.mpr (by positivity)
  have huctCAi_eq : uctCAi = -|uctCAi| := by rw [abs_of_neg huctCAi_neg, neg_neg]
  have hF_eq_P : ∀ τ : ℝ, F_R τ =
      ((c / fctNc h ε c : ℝ) : ℂ) * (Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P_R τ) := fun τ => by
    dsimp only [F_R, P_R, warpP]; rw [mellinK0_imag_shift (L1 := L1) hξ]; dsimp only [Nc, ω]; push_cast; ring
  have h_half_F : (∫ τ in Ioi (0 : ℝ), F_R τ).re =
      -(c / fctNc h ε c * ω⁻¹) *
        ((∫ τ in Ioi (0 : ℝ), mellinK0 c ((τ : ℂ) * Complex.I) ξ *
            fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) * fctRightTail h ε c τ).re -
          (Complex.I * ∫ τ in Ioi (0 : ℝ),
            Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * warpP K4 ε c L1 α τ *
              deriv (fctRightTail h ε c) τ).re) := by
    have h1 : ∫ τ in Ioi (0 : ℝ), F_R τ =
        ((c / fctNc h ε c : ℝ) : ℂ) * ∫ τ in Ioi (0 : ℝ),
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P_R τ := by
      rw [← MeasureTheory.integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun τ _ => hF_eq_P τ
    have hG_split : ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g_R τ =
        (∫ τ in Ioi (0 : ℝ), mellinK0 c ((τ : ℂ) * Complex.I) ξ *
            fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) * fctRightTail h ε c τ) -
          Complex.I * ∫ τ in Ioi (0 : ℝ),
            Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * warpP K4 ε c L1 α τ *
              deriv (fctRightTail h ε c) τ := by
      have hsub := integral_sub hterm1_int (hterm2_int.const_mul Complex.I)
      rw [MeasureTheory.integral_const_mul] at hsub
      rw [← hsub]
      refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
      dsimp only [g_R]; unfold fctWarpIntegrand
      rw [mellinK0_imag_shift (L1 := L1) hξ]; dsimp only [ω]; push_cast; ring
    have h_pref : ((c / fctNc h ε c : ℝ) : ℂ) * (-((ω : ℂ)⁻¹ *
          ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g_R τ)) =
        ((-(c / fctNc h ε c * ω⁻¹) : ℝ) : ℂ) *
          ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g_R τ := by
      push_cast; ring
    rw [h1, hibp, h_pref, Complex.re_ofReal_mul, hG_split, Complex.sub_re]
  change (uctCAi * c ^ (-(1 / 2 : ℝ)) / (2 * π)) * (∫ τ : ℝ, F_R τ).re = _
  rw [hRe_int, h_half_F]
  unfold warpRightTailTerm1 warpRightTailTerm2
  dsimp only [ω, L1, α, L]
  rw [mul_inv_rev, huctCAi_eq]
  simp only [abs_neg, abs_abs]
  have h56' : c ^ (-(1 / 2 : ℝ)) = c ^ (-(5 / 6 : ℝ)) * c ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hcpos]; congr 1; norm_num
  set I1 : ℝ := (∫ τ in Ioi (0 : ℝ), mellinK0 c ((τ : ℂ) * Complex.I) ξ *
    fctWarpA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) *
    fctRightTail h ε c τ).re
  set I2 : ℝ := (Complex.I * ∫ τ in Ioi (0 : ℝ),
    Complex.exp (Complex.I * ((c * (Real.log (π ^ 2 * ξ) - fctWarpL1 h ε c) * τ : ℝ) : ℂ)) *
      warpP K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
      deriv (fctRightTail h ε c) τ).re
  calc (-|uctCAi| * c ^ (-(1 / 2 : ℝ)) / (2 * π)) *
          (2 * (-(c / fctNc h ε c * ((Real.log (π ^ 2 * ξ) - fctWarpL1 h ε c)⁻¹ * c⁻¹)) * (I1 - I2)))
      = (1 / fctNc h ε c) * (|uctCAi| * (c ^ (-(1 / 2 : ℝ)) * (c * c⁻¹)) /
          (Real.log (π ^ 2 * ξ) - fctWarpL1 h ε c)) * ((1 / π) * (I1 - I2)) := by ring
    _ = (1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) /
          (Real.log (π ^ 2 * ξ) - fctWarpL1 h ε c)) * ((c ^ (1 / 3 : ℝ) / π) * I1) +
        -((1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) /
          (Real.log (π ^ 2 * ξ) - fctWarpL1 h ε c)) * ((c ^ (1 / 3 : ℝ) / π) * I2)) := by
        rw [mul_inv_cancel₀ hcpos.ne', mul_one, h56']; ring

/-- Bounds on `warpRightTailTerm2`:
* `O(c^{-2} L^{-1})` for `Sw * c^{-2/3} ≤ L`,
* `O(c^{-5/2} L^{-2})` for `1 ≤ L` (via a second IBP using `ContDiff ℝ 2 (fctRightTail)`). -/
lemma warpRightTail_term2_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ CT2 Sw c₀ : ℝ, 0 ≤ CT2 ∧ 1 ≤ Sw ∧ 32 ^ 4 ≤ c₀ ∧
      ∀ {ε c ξ : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
        (Sw * c ^ (-(2 / 3 : ℝ)) ≤ Real.log (π ^ 2 * ξ) →
          |warpRightTailTerm2 h ε c ξ| ≤ CT2 * c ^ (-2 : ℝ) * (Real.log (π ^ 2 * ξ))⁻¹) ∧
        (1 ≤ Real.log (π ^ 2 * ξ) →
          |warpRightTailTerm2 h ε c ξ| ≤ CT2 * c ^ (-(5 / 2 : ℝ)) * (Real.log (π ^ 2 * ξ)) ^ (-2 : ℝ)) := by
  obtain ⟨c0N, _, hNc⟩ := fctNcC_eq_fctNc hK4 h
  obtain ⟨CR, c0R, hCR0, _, hRT⟩ := fctRightTail_bounds hK4 h
  obtain ⟨CP, c0P, hCP0, hc0P, hP_main⟩ := warpP_bounds hK4 h
  obtain ⟨CB, c0B, hCB0, hc0B, hB⟩ := warpAmpBase_bounds hK4 h
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨CL1, cL1, _, hL1_bd⟩ := FctSym.physL1_le (fctWarpT1 h) ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).1⟩
  obtain ⟨M_m12, hMm12_0, hI_m12, hI_m12_le⟩ := integrableOn_rpow_poly13_exp (-(1 / 2 : ℝ)) (by norm_num) 1
  set Sw : ℝ := max (π ^ 2 * 100) (2 * |CL1| + 1)
  have hSw1 : 1 ≤ Sw := le_max_of_le_right (by linarith [abs_nonneg CL1])
  set C_p : ℝ := 4 * |uctCAi| / π
  set CT2 : ℝ := max (C_p * CP * CR) (2 * C_p * (CB * M_m12 * CR + CP * CR))
  set c₀ : ℝ := max (max (max c0N c0R) (max c0P c0B)) (max cL1 (max ((2 * |CL1| + 1) ^ (3 / 2 : ℝ)) (32 ^ 4)))
  refine ⟨CT2, Sw, c₀, by positivity, hSw1, le_max_of_le_right (le_max_of_le_right (le_max_right _ _)),
    fun {ε c ξ} hε hc _ => ?_⟩
  have hcN : c0N ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hc))
  have hcR : c0R ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hc))
  have hcP : c0P ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc))
  have hcB : c0B ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc))
  have hcL1 : cL1 ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hcSw : (2 * |CL1| + 1) ^ (3 / 2 : ℝ) ≤ c :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
  have hc32 : (32 : ℝ) ^ 4 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
  have hcpos : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set L := Real.log (π ^ 2 * ξ)
  obtain ⟨_, hNc_lo, _, _⟩ := hNc ε c hε hcN
  have hNc_pos : 0 < fctNc h ε c := by linarith
  obtain ⟨hR_cd, hR_bd⟩ := hRT ε c hε hcR
  obtain ⟨hzero_int, hP_int, hP_L1, hP_bd, _, hP_deriv, hP_lim0, hP_limTop⟩ := hP_main hε hcP
  obtain ⟨_, hB_bd⟩ := hB hε hcB
  have hL1_le : |L1| ≤ |CL1| * c ^ (-(2 / 3 : ℝ)) := by
    have h1 := hL1_bd ε c hε hcL1
    unfold FctSym.physL1 at h1
    rw [physL1_fctWarpT1 h hcpos] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hL1_half : |L1| ≤ (1 / 2 : ℝ) := by
    have h23 : c ^ (-(2 / 3 : ℝ)) ≤ (2 * |CL1| + 1)⁻¹ := by
      have hpow : 2 * |CL1| + 1 ≤ c ^ (2 / 3 : ℝ) := by
        calc 2 * |CL1| + 1 = ((2 * |CL1| + 1) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
              rw [← Real.rpow_mul (by positivity)]; norm_num
          _ ≤ c ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hcSw (by norm_num)
      rw [Real.rpow_neg hcpos.le]
      exact inv_anti₀ (by positivity) hpow
    calc |L1| ≤ |CL1| * c ^ (-(2 / 3 : ℝ)) := hL1_le
      _ ≤ |CL1| * (2 * |CL1| + 1)⁻¹ := mul_le_mul_of_nonneg_left h23 (abs_nonneg _)
      _ ≤ 1 / 2 := by rw [mul_inv_le_iff₀ (by positivity)]; linarith [abs_nonneg CL1]
  have hpref_bd : ∀ {L_lo : ℝ}, 0 < L_lo → L_lo ≤ L → 2 * |L1| ≤ L →
      |(1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - L1)) * (c ^ (1 / 3 : ℝ) / π)| ≤
        C_p * c ^ (-(1 / 2 : ℝ)) * L⁻¹ := by
    intro L_lo hLlo hLLo h2L1
    have hLpos : 0 < L := lt_of_lt_of_le hLlo hLLo
    have hL1_hL : |L1| ≤ L / 2 := by linarith
    have hsub_lo : L / 2 ≤ L - L1 := by linarith [(abs_le.mp hL1_hL).2]
    have hsub_pos : 0 < L - L1 := by linarith
    have hNc_inv : |1 / fctNc h ε c| ≤ 2 := by
      rw [one_div, abs_inv, abs_of_pos hNc_pos]
      exact inv_le_of_inv_le₀ (by norm_num) (by linarith [hNc_lo])
    have hc56 : c ^ (-(5 / 6 : ℝ)) * c ^ (1 / 3 : ℝ) = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hcpos]; congr 1; norm_num
    have hnum_nn : 0 ≤ |uctCAi| * c ^ (-(5 / 6 : ℝ)) := by positivity
    rw [abs_mul, abs_mul, abs_div (|uctCAi| * _), abs_div (c ^ _), abs_of_nonneg hnum_nn,
      abs_of_pos (Real.rpow_pos_of_pos hcpos _), abs_of_pos Real.pi_pos, abs_of_pos hsub_pos]
    have hinv_L : (L - L1)⁻¹ ≤ 2 * L⁻¹ := by
      calc (L - L1)⁻¹ ≤ (L / 2)⁻¹ := inv_anti₀ (by linarith) hsub_lo
        _ = 2 * L⁻¹ := by ring
    calc |1 / fctNc h ε c| * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - L1)) * (c ^ (1 / 3 : ℝ) / π)
        = |1 / fctNc h ε c| * ((|uctCAi| / π) * (c ^ (-(5 / 6 : ℝ)) * c ^ (1 / 3 : ℝ)) * (L - L1)⁻¹) := by ring
      _ ≤ 2 * ((|uctCAi| / π) * c ^ (-(1 / 2 : ℝ)) * (2 * L⁻¹)) := by
          rw [hc56]; have : 0 ≤ (|uctCAi| / π) * c ^ (-(1 / 2 : ℝ)) := by positivity
          gcongr
      _ = C_p * c ^ (-(1 / 2 : ℝ)) * L⁻¹ := by dsimp only [C_p]; ring
  constructor
  · intro hSwL
    have h2L1 : 2 * |L1| ≤ L := by
      calc 2 * |L1| ≤ 2 * (|CL1| * c ^ (-(2 / 3 : ℝ))) := mul_le_mul_of_nonneg_left hL1_le zero_le_two
        _ = (2 * |CL1|) * c ^ (-(2 / 3 : ℝ)) := by ring
        _ ≤ (2 * |CL1| + 1) * c ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ Sw * c ^ (-(2 / 3 : ℝ)) := by gcongr; exact le_max_right _ _
        _ ≤ L := hSwL
    have hLlo : 0 < Sw * c ^ (-(2 / 3 : ℝ)) := by positivity
    have hpref := hpref_bd hLlo hSwL h2L1
    set I2 := ∫ τ in Ioi (0 : ℝ),
      Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)) * warpP K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ
    have hI2_norm : ‖I2‖ ≤ CP * CR * c ^ (-(3 / 2 : ℝ)) := by
      have h_ae : AEStronglyMeasurable (fun τ : ℝ => Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)) *
          warpP K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ) (volume.restrict (Ioi 0)) := by
        have hP_cont : ContinuousOn (warpP K4 ε c L1 α) (Ioi 0) := fun τ hτ =>
          (hP_deriv hτ).continuousAt.continuousWithinAt
        have hexp_cont : Continuous (fun τ : ℝ => Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ))) :=
          Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
            (continuous_const.mul continuous_id)))
        exact ((hexp_cont.continuousOn.mul hP_cont).mul
          (hR_cd.continuous_deriv (by norm_num)).continuousOn).aestronglyMeasurable measurableSet_Ioi
      have hint_2 : IntegrableOn (fun τ : ℝ => Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)) *
          warpP K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ) (Ioi 0) := by
        refine (hP_int.norm.const_mul (CR * c⁻¹)).mono' h_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ _
        have hexp1 : ‖Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ))‖ = 1 := by
          rw [Complex.norm_exp]; simp [Complex.mul_re]
        rw [norm_mul, norm_mul, hexp1, one_mul]
        calc ‖warpP K4 ε c L1 α τ‖ * ‖deriv (fctRightTail h ε c) τ‖
            ≤ ‖warpP K4 ε c L1 α τ‖ * (CR * c⁻¹) := mul_le_mul_of_nonneg_left (hR_bd τ).2.1 (norm_nonneg _)
          _ = (CR * c⁻¹) * ‖warpP K4 ε c L1 α τ‖ := by ring
      calc ‖I2‖ ≤ ∫ τ in Ioi (0 : ℝ), ‖Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)) *
            warpP K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ τ in Ioi (0 : ℝ), (CR * c⁻¹) * ‖warpP K4 ε c L1 α τ‖ := by
            refine setIntegral_mono_on hint_2.norm (hP_int.norm.const_mul _) measurableSet_Ioi fun τ _ => ?_
            have hexp1 : ‖Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ))‖ = 1 := by
              rw [Complex.norm_exp]; simp [Complex.mul_re]
            rw [norm_mul, norm_mul, hexp1, one_mul]
            calc ‖warpP K4 ε c L1 α τ‖ * ‖deriv (fctRightTail h ε c) τ‖
                ≤ ‖warpP K4 ε c L1 α τ‖ * (CR * c⁻¹) := mul_le_mul_of_nonneg_left (hR_bd τ).2.1 (norm_nonneg _)
              _ = (CR * c⁻¹) * ‖warpP K4 ε c L1 α τ‖ := by ring
        _ = (CR * c⁻¹) * ∫ τ in Ioi (0 : ℝ), ‖warpP K4 ε c L1 α τ‖ := MeasureTheory.integral_const_mul _ _
        _ ≤ (CR * c⁻¹) * (CP * c ^ (-(1 / 2 : ℝ))) := by gcongr
        _ = CP * CR * (c⁻¹ * c ^ (-(1 / 2 : ℝ))) := by ring
        _ = CP * CR * c ^ (-(3 / 2 : ℝ)) := by
            rw [← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 2; norm_num
    have hre_bd : |(Complex.I * I2).re| ≤ CP * CR * c ^ (-(3 / 2 : ℝ)) :=
      (Complex.abs_re_le_norm _).trans (by simpa [norm_mul, Complex.norm_I] using hI2_norm)
    have hc2_eq : c ^ (-(1 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ)) = c ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hcpos]; congr 1; norm_num
    change |warpRightTailTerm2 h ε c ξ| ≤ CT2 * c ^ (-2 : ℝ) * L⁻¹
    unfold warpRightTailTerm2
    rw [abs_neg, abs_mul, abs_mul (c ^ (1 / 3 : ℝ) / π), ← mul_assoc, ← abs_mul]
    have hc2_nn : 0 ≤ c ^ (-2 : ℝ) := by positivity
    have hLinv_nn : 0 ≤ L⁻¹ := inv_nonneg.mpr (lt_of_lt_of_le hLlo hSwL).le
    calc |(1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - L1)) * (c ^ (1 / 3 : ℝ) / π)| *
          |(Complex.I * I2).re|
        ≤ (C_p * c ^ (-(1 / 2 : ℝ)) * L⁻¹) * (CP * CR * c ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul hpref hre_bd (abs_nonneg _) (mul_nonneg (by positivity) hLinv_nn)
      _ = (C_p * CP * CR) * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ))) * L⁻¹ := by ring
      _ = (C_p * CP * CR) * c ^ (-2 : ℝ) * L⁻¹ := by rw [hc2_eq]
      _ ≤ CT2 * c ^ (-2 : ℝ) * L⁻¹ := by gcongr; exact le_max_left _ _
  · intro hL1
    have h2L1 : 2 * |L1| ≤ L := by linarith
    have hpref := hpref_bd zero_lt_one hL1 h2L1
    have hL1_hL : |L1| ≤ L / 2 := by linarith
    have hsub_lo : L / 2 ≤ L - L1 := by linarith [(abs_le.mp hL1_hL).2]
    have hsub_pos : 0 < L - L1 := by linarith
    set ω := c * (L - L1)
    have hω_pos : 0 < ω := mul_pos hcpos hsub_pos
    have hω_ne : ω ≠ 0 := hω_pos.ne'
    let P2 : ℝ → ℂ := fun τ => warpP K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ
    let g2 : ℝ → ℂ := fun τ => fctWarpIntegrand K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ -
      Complex.I * warpP K4 ε c L1 α τ * deriv (deriv (fctRightTail h ε c)) τ
    have hexp_cont : Continuous (fun τ : ℝ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
    have hP_cont : ContinuousOn (warpP K4 ε c L1 α) (Ioi 0) := fun τ hτ =>
      (hP_deriv hτ).continuousAt.continuousWithinAt
    have hR1_cd : ContDiff ℝ 1 (deriv (fctRightTail h ε c)) :=
      (contDiff_succ_iff_deriv.mp hR_cd).2.2
    have h1_int : IntegrableOn (fun τ => fctWarpIntegrand K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ) (Ioi 0) := by
      have h_ae : AEStronglyMeasurable (fun τ => fctWarpIntegrand K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ)
          (volume.restrict (Ioi 0)) :=
        (hzero_int.aestronglyMeasurable.mul (hR1_cd.continuous.continuousOn.aestronglyMeasurable measurableSet_Ioi))
      exact (hzero_int.norm.const_mul (CR * c⁻¹)).mono' h_ae (ae_of_all _ fun τ => by
        rw [norm_mul]; calc ‖fctWarpIntegrand K4 ε c L1 α τ‖ * ‖deriv (fctRightTail h ε c) τ‖
            ≤ ‖fctWarpIntegrand K4 ε c L1 α τ‖ * (CR * c⁻¹) :=
              mul_le_mul_of_nonneg_left (hR_bd τ).2.1 (norm_nonneg _)
          _ = (CR * c⁻¹) * ‖fctWarpIntegrand K4 ε c L1 α τ‖ := by ring)
    have h2_int : IntegrableOn (fun τ => Complex.I * warpP K4 ε c L1 α τ * deriv (deriv (fctRightTail h ε c)) τ) (Ioi 0) := by
      have h_ae : AEStronglyMeasurable (fun τ => Complex.I * warpP K4 ε c L1 α τ * deriv (deriv (fctRightTail h ε c)) τ)
          (volume.restrict (Ioi 0)) :=
        ((continuous_const.continuousOn.mul hP_cont).mul
          (hR1_cd.continuous_deriv (by norm_num)).continuousOn).aestronglyMeasurable measurableSet_Ioi
      exact (hP_int.norm.const_mul (CR * c⁻¹)).mono' h_ae (ae_of_all _ fun τ => by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
        calc ‖warpP K4 ε c L1 α τ‖ * ‖deriv (deriv (fctRightTail h ε c)) τ‖
            ≤ ‖warpP K4 ε c L1 α τ‖ * (CR * c⁻¹) := mul_le_mul_of_nonneg_left (hR_bd τ).2.2 (norm_nonneg _)
          _ = (CR * c⁻¹) * ‖warpP K4 ε c L1 α τ‖ := by ring)
    have hg2_int : IntegrableOn g2 (Ioi 0) := h1_int.sub h2_int
    have hP2_exp_int : IntegrableOn (fun τ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P2 τ) (Ioi 0) := by
      have h_ae : AEStronglyMeasurable (fun τ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P2 τ)
          (volume.restrict (Ioi 0)) :=
        (hexp_cont.continuousOn.mul (hP_cont.mul hR1_cd.continuous.continuousOn)).aestronglyMeasurable measurableSet_Ioi
      exact (hP_int.norm.const_mul (CR * c⁻¹)).mono' h_ae (ae_of_all _ fun τ => by
        dsimp only [P2]; rw [norm_mul, norm_mul, show ‖Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ = 1 by
          rw [Complex.norm_exp]; simp [Complex.mul_re], one_mul]
        calc ‖warpP K4 ε c L1 α τ‖ * ‖deriv (fctRightTail h ε c) τ‖
            ≤ ‖warpP K4 ε c L1 α τ‖ * (CR * c⁻¹) := mul_le_mul_of_nonneg_left (hR_bd τ).2.1 (norm_nonneg _)
          _ = (CR * c⁻¹) * ‖warpP K4 ε c L1 α τ‖ := by ring)
    have hg2_exp_int : IntegrableOn (fun τ => Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g2 τ) (Ioi 0) :=
      Integrable.mono hg2_int
        ((hexp_cont.continuousOn.aestronglyMeasurable measurableSet_Ioi).mul hg2_int.aestronglyMeasurable)
        (ae_of_all _ fun τ => by
          rw [norm_mul, show ‖Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ = 1 by
            rw [Complex.norm_exp]; simp [Complex.mul_re], one_mul])
    have hP2_deriv : ∀ τ : ℝ, 0 < τ → HasDerivAt P2 (Complex.I * g2 τ) τ := fun τ hτ => by
      have hp := hP_deriv hτ
      have hr := (hR1_cd.differentiable (by norm_num) τ).hasDerivAt
      convert hp.mul hr using 1
      dsimp only [g2]; ring_nf; rw [Complex.I_sq]; ring
    have hP2_lim0 : Tendsto P2 (𝓝[>] 0) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h0 : Tendsto (fun τ : ℝ => ‖warpP K4 ε c L1 α τ‖ * (CR * c⁻¹)) (𝓝[>] 0) (𝓝 0) := by
        simpa [zero_mul] using (tendsto_zero_iff_norm_tendsto_zero.mp hP_lim0).mul_const (CR * c⁻¹)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
        (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun τ => by
          dsimp only [P2]; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hR_bd τ).2.1 (norm_nonneg _))
    have hP2_limTop : Tendsto P2 atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h0 : Tendsto (fun τ : ℝ => ‖warpP K4 ε c L1 α τ‖ * (CR * c⁻¹)) atTop (𝓝 0) := by
        simpa [zero_mul] using (tendsto_zero_iff_norm_tendsto_zero.mp hP_limTop).mul_const (CR * c⁻¹)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
        (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun τ => by
          dsimp only [P2]; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hR_bd τ).2.1 (norm_nonneg _))
    have hibp2 := right_ibp_limit hω_ne hg2_int hP2_exp_int hg2_exp_int hP2_deriv hP2_lim0 hP2_limTop
    have hg2_L1 : ∫ τ in Ioi (0 : ℝ), ‖g2 τ‖ ≤ (CB * M_m12 * CR + CP * CR) * c⁻¹ := by
      have h1_L1 : ∫ τ in Ioi (0 : ℝ), ‖fctWarpIntegrand K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ‖ ≤
          CB * M_m12 * CR * c⁻¹ := by
        calc ∫ τ in Ioi (0 : ℝ), ‖fctWarpIntegrand K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ‖
            ≤ ∫ τ in Ioi (0 : ℝ), (CB * CR * c⁻¹) * (1 * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by
              refine setIntegral_mono_on h1_int.norm (hI_m12.const_mul _) measurableSet_Ioi fun τ (hτ : 0 < τ) => ?_
              have hI_eq : ‖fctWarpIntegrand K4 ε c L1 α τ‖ = ‖warpAmpBase K4 ε c L1 α τ‖ := by
                rw [fctWarpIntegrand_eq_edgePhi, norm_mul, show ‖Complex.exp (Complex.I * ((c * edgePhi L1 τ : ℝ) : ℂ))‖ = 1 by
                  rw [Complex.norm_exp]; simp [Complex.mul_re], one_mul]
              have hexp0 : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
              have h12_13 : (1 + τ) ^ 12 ≤ (1 + τ) ^ 13 := pow_le_pow_right₀ (by linarith) (by norm_num)
              rw [norm_mul, hI_eq]
              calc ‖warpAmpBase K4 ε c L1 α τ‖ * ‖deriv (fctRightTail h ε c) τ‖
                  ≤ (CB * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 12 * Real.exp (-(π * τ))) * (CR * c⁻¹) :=
                    mul_le_mul (hB_bd hτ).1 (hR_bd τ).2.1 (norm_nonneg _) (by positivity)
                _ ≤ (CB * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) * (CR * c⁻¹) := by gcongr
                _ = (CB * CR * c⁻¹) * (1 * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ))) := by ring
          _ = (CB * CR * c⁻¹) * ∫ τ in Ioi (0 : ℝ), 1 * τ ^ (-(1 / 2 : ℝ)) * (1 + τ) ^ 13 * Real.exp (-(π * τ)) :=
              MeasureTheory.integral_const_mul _ _
          _ ≤ (CB * CR * c⁻¹) * (|1| * M_m12) := by gcongr
          _ = CB * M_m12 * CR * c⁻¹ := by norm_num; ring
      have h2_L1 : ∫ τ in Ioi (0 : ℝ), ‖Complex.I * warpP K4 ε c L1 α τ * deriv (deriv (fctRightTail h ε c)) τ‖ ≤
          CP * CR * c⁻¹ := by
        calc ∫ τ in Ioi (0 : ℝ), ‖Complex.I * warpP K4 ε c L1 α τ * deriv (deriv (fctRightTail h ε c)) τ‖
            ≤ ∫ τ in Ioi (0 : ℝ), (CR * c⁻¹) * ‖warpP K4 ε c L1 α τ‖ := by
              refine setIntegral_mono_on h2_int.norm (hP_int.norm.const_mul _) measurableSet_Ioi fun τ _ => ?_
              rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
              calc ‖warpP K4 ε c L1 α τ‖ * ‖deriv (deriv (fctRightTail h ε c)) τ‖
                  ≤ ‖warpP K4 ε c L1 α τ‖ * (CR * c⁻¹) := mul_le_mul_of_nonneg_left (hR_bd τ).2.2 (norm_nonneg _)
                _ = (CR * c⁻¹) * ‖warpP K4 ε c L1 α τ‖ := by ring
          _ = (CR * c⁻¹) * ∫ τ in Ioi (0 : ℝ), ‖warpP K4 ε c L1 α τ‖ := MeasureTheory.integral_const_mul _ _
          _ ≤ (CR * c⁻¹) * (CP * c ^ (-(1 / 2 : ℝ))) := by gcongr
          _ ≤ (CR * c⁻¹) * (CP * 1) := by
              gcongr; exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
          _ = CP * CR * c⁻¹ := by ring
      calc ∫ τ in Ioi (0 : ℝ), ‖g2 τ‖
          ≤ ∫ τ in Ioi (0 : ℝ), (‖fctWarpIntegrand K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ‖ +
              ‖Complex.I * warpP K4 ε c L1 α τ * deriv (deriv (fctRightTail h ε c)) τ‖) := by
            refine setIntegral_mono_on hg2_int.norm (h1_int.norm.add h2_int.norm) measurableSet_Ioi fun τ _ =>
              norm_sub_le _ _
        _ = (∫ τ in Ioi (0 : ℝ), ‖fctWarpIntegrand K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ‖) +
              (∫ τ in Ioi (0 : ℝ), ‖Complex.I * warpP K4 ε c L1 α τ * deriv (deriv (fctRightTail h ε c)) τ‖) :=
            integral_add h1_int.norm h2_int.norm
        _ ≤ CB * M_m12 * CR * c⁻¹ + CP * CR * c⁻¹ := add_le_add h1_L1 h2_L1
        _ = (CB * M_m12 * CR + CP * CR) * c⁻¹ := by ring
    have hP2_norm : ‖∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P2 τ‖ ≤
        2 * (CB * M_m12 * CR + CP * CR) * c ^ (-2 : ℝ) * L⁻¹ := by
      have hint_g2 : ‖∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g2 τ‖ ≤
          (CB * M_m12 * CR + CP * CR) * c⁻¹ := by
        calc ‖∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g2 τ‖
            ≤ ∫ τ in Ioi (0 : ℝ), ‖Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g2 τ‖ :=
              norm_integral_le_integral_norm _
          _ = ∫ τ in Ioi (0 : ℝ), ‖g2 τ‖ := by
              refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
              rw [norm_mul, show ‖Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ = 1 by
                rw [Complex.norm_exp]; simp [Complex.mul_re], one_mul]
          _ ≤ (CB * M_m12 * CR + CP * CR) * c⁻¹ := hg2_L1
      have hω_inv : ‖(ω : ℂ)⁻¹‖ ≤ 2 * c⁻¹ * L⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω_pos]
        dsimp only [ω]; rw [mul_inv_rev]
        have hsub : (L - L1)⁻¹ ≤ 2 * L⁻¹ := by
          calc (L - L1)⁻¹ ≤ (L / 2)⁻¹ := inv_anti₀ (by linarith) hsub_lo
            _ = 2 * L⁻¹ := by ring
        calc (L - L1)⁻¹ * c⁻¹ ≤ (2 * L⁻¹) * c⁻¹ := by gcongr
          _ = 2 * c⁻¹ * L⁻¹ := by ring
      have hc2_eq : c⁻¹ * c⁻¹ = c ^ (-2 : ℝ) := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hcpos]; congr 1; norm_num
      rw [hibp2, norm_neg, norm_mul]
      calc ‖(ω : ℂ)⁻¹‖ * ‖∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * g2 τ‖
          ≤ (2 * c⁻¹ * L⁻¹) * ((CB * M_m12 * CR + CP * CR) * c⁻¹) :=
            mul_le_mul hω_inv hint_g2 (norm_nonneg _) (by positivity)
        _ = 2 * (CB * M_m12 * CR + CP * CR) * (c⁻¹ * c⁻¹) * L⁻¹ := by ring
        _ = 2 * (CB * M_m12 * CR + CP * CR) * c ^ (-2 : ℝ) * L⁻¹ := by rw [hc2_eq]
    have hre_bd : |(Complex.I * ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P2 τ).re| ≤
        2 * (CB * M_m12 * CR + CP * CR) * c ^ (-2 : ℝ) * L⁻¹ :=
      (Complex.abs_re_le_norm _).trans (by simpa [norm_mul, Complex.norm_I] using hP2_norm)
    have hc52 : c ^ (-(1 / 2 : ℝ)) * c ^ (-2 : ℝ) = c ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_add hcpos]; congr 1; norm_num
    have hLm2 : L⁻¹ * L⁻¹ = L ^ (-2 : ℝ) := by
      rw [← Real.rpow_neg_one L, ← Real.rpow_add (by linarith)]; congr 1; norm_num
    change |warpRightTailTerm2 h ε c ξ| ≤ CT2 * c ^ (-(5 / 2 : ℝ)) * L ^ (-2 : ℝ)
    unfold warpRightTailTerm2
    rw [abs_neg, abs_mul, abs_mul (c ^ (1 / 3 : ℝ) / π), ← mul_assoc, ← abs_mul]
    have hP2_unfold : ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * (L - L1) * τ : ℝ) : ℂ)) *
          warpP K4 ε c L1 α τ * deriv (fctRightTail h ε c) τ =
        ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P2 τ :=
      setIntegral_congr_fun measurableSet_Ioi fun τ _ => by dsimp only [ω, P2]; ring
    rw [hP2_unfold]
    have hLinv_nn : 0 ≤ L⁻¹ := inv_nonneg.mpr (by linarith)
    calc |(1 / fctNc h ε c) * (|uctCAi| * c ^ (-(5 / 6 : ℝ)) / (L - L1)) * (c ^ (1 / 3 : ℝ) / π)| *
          |(Complex.I * ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) * P2 τ).re|
        ≤ (C_p * c ^ (-(1 / 2 : ℝ)) * L⁻¹) * (2 * (CB * M_m12 * CR + CP * CR) * c ^ (-2 : ℝ) * L⁻¹) :=
          mul_le_mul hpref hre_bd (abs_nonneg _) (mul_nonneg (by positivity) hLinv_nn)
      _ = (2 * C_p * (CB * M_m12 * CR + CP * CR)) *
            (c ^ (-(1 / 2 : ℝ)) * c ^ (-2 : ℝ)) * (L⁻¹ * L⁻¹) := by ring
      _ = (2 * C_p * (CB * M_m12 * CR + CP * CR)) * c ^ (-(5 / 2 : ℝ)) * L ^ (-2 : ℝ) := by rw [hc52, hLm2]
      _ ≤ CT2 * c ^ (-(5 / 2 : ℝ)) * L ^ (-2 : ℝ) := by
          have hnn1 : 0 ≤ c ^ (-(5 / 2 : ℝ)) := by positivity
          have hnn2 : 0 ≤ L ^ (-2 : ℝ) := by positivity
          gcongr; exact le_max_right _ _

/-- info: 'FormalResearch.SignUncertainty.warpRightTail_first_ibp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpRightTail_first_ibp

/-- info: 'FormalResearch.SignUncertainty.warpRightTail_term2_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpRightTail_term2_bounds

end FormalResearch.SignUncertainty