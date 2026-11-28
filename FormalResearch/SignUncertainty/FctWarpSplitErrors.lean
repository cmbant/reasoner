/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctTotSplit
public import FormalResearch.SignUncertainty.FctSplittingRest
public import FormalResearch.SignUncertainty.FctSplittingLogLog
public import FormalResearch.SignUncertainty.FctLeftEdgeBound

/-!
# Splitting identities and edge-tail error bounds for `ctWwarp` (`fct:warp-asymp` (2)-(3))

For `K4 ≥ 1`, let `(L₁, α) = (fctWarpL1, fctWarpAlpha)` be the unconditional zero pair of
`h := fctWarpSolve_uncond hK4`, with `Nc := fctNc h`.
We split `normDensity (ctWwarp (fctPhiHat h) (fctDcomp K4 (fctWarpAlpha h)) ε c) c ξ` into:
* `warpMainDensity h ε c ξ`: the `Φ_c(iτ)/Nc` main piece keeping `Φ̂_c(1 - iτ)` inside;
* `warpMainNoRightDensity h ε c ξ`: the same piece with `Φ̂_c(1 - iτ)` replaced by `1`;
* `warpLeftTailDensity h ε c ξ`: the left-edge tail `fctLeftTail`;
* `warpRightTailDensity h ε c ξ`: the right-edge error `fctRightTail τ := Φ̂_c(1 - iτ) - 1`.

Main bounds proved here (all unconditional in `K4 ≥ 1`):
* `fctPhiHat_one_eq_one` and `fctRightTail_bounds`: `Φ̂_c(1) = 1`, `‖fctRightTail‖ ≤ C c⁻¹ min |τ| 1`,
  and `‖∂_τ^k fctRightTail‖ ≤ C c⁻¹` for `k = 1, 2`.
* `fctPsi_imag_small_bound` & `fctPsi_imag_large_bound`: near-zero and far bounds on `c K₀(iτ, ξ) Ψ_c(iτ)`.
* `warpRightTailDensity_bound`: `|warpRightTailDensity h ε c ξ| ≤ C c^{-4/3}` for all `ξ > 0`.
* `fctLeftTail_cubic_deriv_bounds` & `fctLeftTail_global_deriv_bounds`: `O(c⁻¹ |τ|^{3-k})` on
  `|τ| ≤ 1/8` and `O(c⁻¹ (1 + |τ|))` globally (`k = 0, 1, 2`).
* `warpLeftTailDensity_global_bound`: `|warpLeftTailDensity h ε c ξ| ≤ C c^{-3/2}` for all `ξ > 0`.

Class: proved (depending only on `K4 ≥ 1`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty
open FctMoment FctCompD CtOuter

/-! ### 1. Definitions -/

/-- Right-edge perturbation `Φ̂_c(1 - iτ) - 1`. -/
noncomputable def fctRightTail {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c τ : ℝ) : ℂ :=
  fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) - 1

/-- Normalized density of the `Φ_c/N_c` main term (keeping `Φ̂_c(1 - iτ)` inside). -/
noncomputable def warpMainDensity {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c ξ : ℝ) : ℝ :=
  (uctCAi * c ^ (-(1 / 2 : ℝ)) / (2 * π)) *
    (∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      ((c : ℂ) * fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) /
        (fctNc h ε c : ℂ) * fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I))).re

/-- Normalized density of the `Φ_c/N_c` main term with `Φ̂_c(1 - iτ)` replaced by `1`. -/
noncomputable def warpMainNoRightDensity {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c ξ : ℝ) : ℝ :=
  (uctCAi * c ^ (-(1 / 2 : ℝ)) / (2 * π)) *
    (∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      ((c : ℂ) * fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) /
        (fctNc h ε c : ℂ))).re

/-- Normalized density of the left-edge tail `fctLeftTail`. -/
noncomputable def warpLeftTailDensity {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c ξ : ℝ) : ℝ :=
  (uctCAi * c ^ (-(1 / 2 : ℝ)) / (2 * π)) *
    (∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
        fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
        fctDcompAt K4 c (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) *
        ctHG ε ((τ : ℂ) * Complex.I))).re

/-- Normalized density of the right-edge perturbation `fctRightTail`. -/
noncomputable def warpRightTailDensity {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c ξ : ℝ) : ℝ :=
  (uctCAi * c ^ (-(1 / 2 : ℝ)) / (2 * π)) *
    (∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      ((c : ℂ) * fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) /
        (fctNc h ε c : ℂ) * fctRightTail h ε c τ)).re

/-! ### 2. `N_c` reality, `Φ̂_c(1) = 1`, and `fctRightTail` bounds -/

private lemma line_derivs {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (a b : ℂ) (hb : ‖b‖ = 1) (hm : ∀ t : ℝ, a + (t : ℂ) * b ∈ U) (τ : ℝ) :
    ContDiff ℝ 2 (fun t : ℝ => f (a + (t : ℂ) * b)) ∧
    ‖deriv (fun t : ℝ => f (a + (t : ℂ) * b)) τ‖ = ‖deriv f (a + (τ : ℂ) * b)‖ ∧
    ‖deriv (deriv (fun t : ℝ => f (a + (t : ℂ) * b))) τ‖ = ‖deriv (deriv f) (a + (τ : ℂ) * b)‖ := by
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => a + (s : ℂ) * b) b t := fun t => by
    have h1 := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const b).const_add a
    simpa using h1
  have hcomp_cd : ContDiff ℝ 2 (fun t : ℝ => f (a + (t : ℂ) * b)) := by
    have hcd : ContDiffOn ℝ 2 f U := (hf.contDiffOn hU).restrict_scalars ℝ
    have hlin : ContDiff ℝ 2 (fun t : ℝ => a + (t : ℂ) * b) :=
      contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
    exact contDiffOn_univ.mp (hcd.comp hlin.contDiffOn fun t _ => hm t)
  have hf1 : DifferentiableOn ℂ (deriv f) U := hf.deriv hU
  have hd1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (a + (s : ℂ) * b))
      (deriv f (a + (t : ℂ) * b) * b) t := fun t => by
    have hfa := (hf.differentiableAt (hU.mem_nhds (hm t))).hasDerivAt.hasFDerivAt.restrictScalars ℝ
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using hfa.comp_hasDerivAt t (hg t)
  have hd2 : HasDerivAt (fun t : ℝ => deriv f (a + (t : ℂ) * b) * b)
      (deriv (deriv f) (a + (τ : ℂ) * b) * b * b) τ := by
    have hfa := (hf1.differentiableAt (hU.mem_nhds (hm τ))).hasDerivAt.hasFDerivAt.restrictScalars ℝ
    simpa [Function.comp_def, smul_eq_mul, mul_comm, mul_assoc] using (hfa.comp_hasDerivAt τ (hg τ)).mul_const b
  have hev : deriv (fun t : ℝ => f (a + (t : ℂ) * b)) = fun t : ℝ => deriv f (a + (t : ℂ) * b) * b :=
    funext fun t => (hd1 t).deriv
  refine ⟨hcomp_cd, ?_, ?_⟩
  · rw [hev, norm_mul, hb, mul_one]
  · rw [hev, hd2.deriv, norm_mul, norm_mul, hb, mul_one, mul_one]

lemma fctNcC_eq_fctNc {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) = (fctNc h ε c : ℂ) ∧
        1 / 2 ≤ fctNc h ε c ∧ fctNc h ε c ≤ 3 / 2 ∧ (fctNc h ε c : ℂ) ≠ 0 := by
  let hD : FctDescentStmt h := fctDescent_uncond hK4 h
  obtain ⟨c0s, _, hSetup⟩ := fctSplitting_setup hK4 hD
  obtain ⟨KN, c0N, hNc_norm⟩ := fctSplittingNorm_of_descent hD
  refine ⟨max (max c0s c0N) (max (4 * |KN|) 2),
    le_max_of_le_right (le_max_of_le_right (by norm_num)), fun ε c hε hc => ?_⟩
  obtain ⟨_, _, _, _, _, hDconj⟩ :=
    hSetup ε c hε (((le_max_left _ _).trans (le_max_left _ _)).trans hc)
  have hNc_bd := hNc_norm ε c hε (((le_max_right _ _).trans (le_max_left _ _)).trans hc)
  have hc_ge : max (4 * |KN|) 2 ≤ c := (le_max_right _ _).trans hc
  have hNc_im : (fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)).im = 0 := by
    have hconj := fctPhiWarp_conj (K4 := K4) (ε := ε) (c := c)
      (L1 := fctWarpL1 h ε c) (α := fctWarpAlpha h ε c) hDconj (ζ := 1) (by simp)
    rw [map_one] at hconj
    unfold fctNcC
    exact Complex.conj_eq_iff_im.mp hconj.symm
  have hNc_eq : fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) = (fctNc h ε c : ℂ) := by
    apply Complex.ext
    · rfl
    · simp [hNc_im]
  have hcpos : 0 < c := by
    have : (2 : ℝ) ≤ c := (le_max_right _ _).trans hc_ge
    linarith
  have h4KN : 4 * |KN| ≤ c := (le_max_left _ _).trans hc_ge
  have hdiff : |fctNc h ε c - 1| ≤ 1 / 4 := by
    calc |fctNc h ε c - 1| ≤ KN * c⁻¹ := hNc_bd
      _ ≤ |KN| * c⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = |KN| / c := (div_eq_mul_inv _ _).symm
      _ ≤ 1 / 4 := by rw [div_le_div_iff₀ hcpos (by norm_num)]; linarith
  have hlo : 1 / 2 ≤ fctNc h ε c := by linarith [(abs_le.mp hdiff).1]
  have hhi : fctNc h ε c ≤ 3 / 2 := by linarith [(abs_le.mp hdiff).2]
  exact ⟨hNc_eq, hlo, hhi, Complex.ofReal_ne_zero.mpr (by linarith)⟩

/-- `Φ̂_c(1) = 1` for `c ≥ c₀`. -/
theorem fctPhiHat_one_eq_one {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      fctPhiHat h ε c 1 = 1 := by
  obtain ⟨c₀, hc01, hNc⟩ := fctNcC_eq_fctNc hK4 h
  refine ⟨c₀, hc01, fun ε c hε hc => ?_⟩
  obtain ⟨hNc_eq, _, _, hne⟩ := hNc ε c hε hc
  show fctPhiHatAt K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) 1 = 1
  unfold fctPhiHatAt
  have hq1 : fctQ1 1 = 0 := by unfold fctQ1; simp
  have hNc0 : fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ≠ 0 := by
    rw [hNc_eq]; exact hne
  change fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) /
      fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) +
      fctBetaC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) * fctQ1 1 = 1
  rw [hq1, mul_zero, add_zero, div_self hNc0]

/-- `fctRightTail`: `O(c⁻¹ |τ|)` value bound and `O(c⁻¹)` first/second derivative bounds. -/
theorem fctRightTail_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ContDiff ℝ 2 (fctRightTail h ε c) ∧
      ∀ τ : ℝ,
        ‖fctRightTail h ε c τ‖ ≤ C * c⁻¹ * |τ| ∧
        ‖deriv (fctRightTail h ε c) τ‖ ≤ C * c⁻¹ ∧
        ‖deriv (deriv (fctRightTail h ε c)) τ‖ ≤ C * c⁻¹ := by
  obtain ⟨Cdesc, c0Desc, hDesc⟩ := fctDescent_uncond hK4 h
  obtain ⟨c0s, _, hSetup⟩ := fctSplitting_setup hK4 (fctDescent_uncond hK4 h)
  obtain ⟨Kβ, c0b, hKβ, hNb⟩ := fct_Nc_beta_bounds hK4 (fctDescent_uncond hK4 h)
  obtain ⟨c01, hc01, hOne⟩ := fctPhiHat_one_eq_one hK4 h
  obtain ⟨K0, K1, K2, hK0, hK1, hK2, hCau⟩ :=
    fctCauchy_line_deriv_bounds (σ := 3 / 8) (σζ := 1) le_rfl (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C' : ℝ := |Cdesc| / Real.log 2
  have hC'0 : 0 ≤ C' := by positivity
  set C : ℝ := 4 * max K0 (max K1 K2) * C' + 4000 * Kβ
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, max (max c0Desc c0s) (max c0b c01), hC0,
    le_max_of_le_right (le_max_of_le_right hc01), fun ε c hε hc => ?_⟩
  have hcDesc := hDesc ε c hε (((le_max_left _ _).trans (le_max_left _ _)).trans hc)
  obtain ⟨hcpos, _, hDc, _, _, _⟩ :=
    hSetup ε c hε (((le_max_right _ _).trans (le_max_left _ _)).trans hc)
  obtain ⟨hNc_inv, hβ_c, _⟩ :=
    hNb ε c hε (((le_max_left _ _).trans (le_max_right _ _)).trans hc)
  have hphi1 := hOne ε c hε (((le_max_right _ _).trans (le_max_right _ _)).trans hc)
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set Nc := fctNcC K4 ε c L1 α
  set β := fctBetaC K4 ε c L1 α
  have hFc : ∀ y : ℝ, ‖fctFint K4 ε c L1 α (((3 / 8 : ℝ) : ℂ) + y * Complex.I)‖ ≤ C' * c⁻¹ := fun y => by
    have hb := hcDesc (3 / 8) y (by norm_num) (by norm_num)
    have hl : Real.log 2 ≤ Real.log (2 + |y|) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg y])
    calc ‖fctFint K4 ε c L1 α (((3 / 8 : ℝ) : ℂ) + y * Complex.I)‖
        ≤ Cdesc * c⁻¹ / Real.log (2 + |y|) := hb
      _ ≤ |Cdesc| * c⁻¹ / Real.log (2 + |y|) := by
          gcongr
          · exact (Real.log_pos (by linarith [abs_nonneg y])).le
          · exact le_abs_self _
      _ ≤ |Cdesc| * c⁻¹ / Real.log 2 := by gcongr
      _ = C' * c⁻¹ := by simp only [C']; ring
  have hU : IsOpen {z : ℂ | 7 / 16 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hC_hol : DifferentiableOn ℂ (fctCauchy K4 ε c L1 α (3 / 8)) {z : ℂ | 7 / 16 < z.re} :=
    fctCauchy_differentiableOn hcpos hDc le_rfl (by norm_num) hFc hU fun w hw => by
      have hw' : 7 / 16 < w.re := hw
      exact ⟨by linarith, by linarith⟩
  have hQ_hol : DifferentiableOn ℂ fctQ1 {z : ℂ | 7 / 16 < z.re} :=
    fctQ1_differentiableOn_rhp.mono fun z hz => by
      have hz' : 7 / 16 < z.re := hz
      change -1 / 2 < z.re
      linarith
  have hmem : ∀ t : ℝ, (1 : ℂ) + (t : ℂ) * (-Complex.I) ∈ {z : ℂ | 7 / 16 < z.re} := fun t => by
    change (7 / 16 : ℝ) < ((1 : ℂ) + (t : ℂ) * (-Complex.I)).re
    simp; norm_num
  have hNc_def : Nc = 1 - fctCauchy K4 ε c L1 α (3 / 8) 1 := by
    unfold Nc fctNcC fctPhiWarp
    simp only [show ¬ ((1 : ℂ).re < 7 / 16) by norm_num, ite_false]
  have hNc0 : Nc ≠ 0 := by
    intro h0
    have hb0 : fctPhiHat h ε c 1 = 0 := by
      show fctPhiHatAt K4 ε c L1 α 1 = 0
      unfold fctPhiHatAt
      change Nc / Nc + β * fctQ1 1 = 0
      rw [h0, div_zero, zero_add, show fctQ1 1 = 0 by unfold fctQ1; simp, mul_zero]
    rw [hb0] at hphi1
    exact zero_ne_one hphi1
  have h1_eq : (Nc⁻¹ : ℂ) - 1 = Nc⁻¹ * fctCauchy K4 ε c L1 α (3 / 8) 1 := by
    have : Nc⁻¹ * (Nc + fctCauchy K4 ε c L1 α (3 / 8) 1) = Nc⁻¹ := by rw [hNc_def]; ring_nf
    calc Nc⁻¹ - 1 = Nc⁻¹ - Nc⁻¹ * Nc := by rw [inv_mul_cancel₀ hNc0]
      _ = Nc⁻¹ * (1 - Nc) := by ring
      _ = Nc⁻¹ * fctCauchy K4 ε c L1 α (3 / 8) 1 := by rw [hNc_def]; ring
  have hfn_eq : ∀ t : ℝ, fctRightTail h ε c t =
      Nc⁻¹ * (fctCauchy K4 ε c L1 α (3 / 8) 1 -
        fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (t : ℂ) * (-Complex.I))) +
        β * fctQ1 ((1 : ℂ) + (t : ℂ) * (-Complex.I)) := fun t => by
    show fctPhiHatAt K4 ε c L1 α (1 - (t : ℂ) * Complex.I) - 1 = _
    unfold fctPhiHatAt fctPhiWarp
    have hnot : ¬ ((1 - (t : ℂ) * Complex.I).re < 7 / 16) := by simp; norm_num
    simp only [hnot, ite_false]
    rw [show (1 : ℂ) + (t : ℂ) * (-Complex.I) = 1 - (t : ℂ) * Complex.I by ring]
    have hinv := h1_eq
    calc (1 - fctCauchy K4 ε c L1 α (3 / 8) (1 - (t : ℂ) * Complex.I)) / Nc +
          β * fctQ1 (1 - (t : ℂ) * Complex.I) - 1
        = (Nc⁻¹ - 1) - Nc⁻¹ * fctCauchy K4 ε c L1 α (3 / 8) (1 - (t : ℂ) * Complex.I) +
            β * fctQ1 (1 - (t : ℂ) * Complex.I) := by rw [div_eq_mul_inv]; ring
      _ = _ := by rw [hinv]; ring
  have hC_cd : ContDiff ℝ 2 (fun t : ℝ => fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (t : ℂ) * (-Complex.I))) :=
    (line_derivs hU hC_hol 1 (-Complex.I) (by simp) hmem 0).1
  have hQ_cd : ContDiff ℝ 2 (fun t : ℝ => fctQ1 ((1 : ℂ) + (t : ℂ) * (-Complex.I))) :=
    (line_derivs hU hQ_hol 1 (-Complex.I) (by simp) hmem 0).1
  have hcd : ContDiff ℝ 2 (fctRightTail h ε c) := by
    rw [funext hfn_eq]
    exact (contDiff_const.mul (contDiff_const.sub hC_cd)).add (contDiff_const.mul hQ_cd)
  have hderiv_unif : ∀ τ : ℝ,
      ‖deriv (fctRightTail h ε c) τ‖ ≤ C * c⁻¹ ∧
      ‖deriv (deriv (fctRightTail h ε c)) τ‖ ≤ C * c⁻¹ := fun τ => by
    obtain ⟨_, hC_d1, hC_d2⟩ := line_derivs hU hC_hol 1 (-Complex.I) (by simp) hmem τ
    obtain ⟨_, hQ_d1, hQ_d2⟩ := line_derivs hU hQ_hol 1 (-Complex.I) (by simp) hmem τ
    have hCauτ := hCau K4 ε c L1 α (C' * c⁻¹) hcpos hDc (by positivity) hFc (-τ)
    dsimp only at hCauτ
    have hw0 : ((1 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I = (1 : ℂ) + (τ : ℂ) * (-Complex.I) := by
      push_cast; ring
    rw [hw0] at hCauτ
    have hQ_bd := fctQ1_deriv_bounds (ζ := (1 : ℂ) + (τ : ℂ) * (-Complex.I)) (by simp)
    have hd1_eq : ∀ t : ℝ, deriv (fctRightTail h ε c) t =
        -(Nc⁻¹ * deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I))) t) +
          β * deriv (fun s : ℝ => fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I))) t := fun t => by
      rw [funext hfn_eq]
      have h1 : DifferentiableAt ℝ
          (fun s : ℝ => fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I))) t :=
        (hC_cd.differentiable (by norm_num)) t
      have h2 : DifferentiableAt ℝ (fun s : ℝ => fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I))) t :=
        (hQ_cd.differentiable (by norm_num)) t
      have ha := (((hasDerivAt_const t (fctCauchy K4 ε c L1 α (3 / 8) 1)).sub h1.hasDerivAt).const_mul Nc⁻¹).add
        (h2.hasDerivAt.const_mul β)
      exact ha.deriv.trans (by ring)
    have hd2_eq : deriv (deriv (fctRightTail h ε c)) τ =
        -(Nc⁻¹ * deriv (deriv (fun s : ℝ =>
            fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) τ) +
          β * deriv (deriv (fun s : ℝ => fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) τ := by
      rw [funext hd1_eq]
      have hC1 : ContDiff ℝ 1
          (deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) :=
        hC_cd.iterate_deriv' 1 1
      have hQ1 : ContDiff ℝ 1 (deriv (fun s : ℝ => fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) :=
        hQ_cd.iterate_deriv' 1 1
      have h1 : DifferentiableAt ℝ
          (deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (3 / 8) ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) τ :=
        (hC1.differentiable one_ne_zero) τ
      have h2 : DifferentiableAt ℝ (deriv (fun s : ℝ => fctQ1 ((1 : ℂ) + (s : ℂ) * (-Complex.I)))) τ :=
        (hQ1.differentiable one_ne_zero) τ
      exact (((h1.hasDerivAt.const_mul Nc⁻¹).neg).add (h2.hasDerivAt.const_mul β)).deriv
    have hK1le : K1 ≤ max K0 (max K1 K2) := (le_max_left _ _).trans (le_max_right _ _)
    have hK2le : K2 ≤ max K0 (max K1 K2) := (le_max_right _ _).trans (le_max_right _ _)
    have hmax0 : 0 ≤ max K0 (max K1 K2) := le_trans hK0 (le_max_left _ _)
    have hc_inv0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hcpos.le
    refine ⟨?_, ?_⟩
    · rw [hd1_eq τ]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_mul, norm_mul, hC_d1, hQ_d1]
      calc ‖Nc⁻¹‖ * ‖deriv (fctCauchy K4 ε c L1 α (3 / 8)) _‖ + ‖β‖ * ‖deriv fctQ1 _‖
          ≤ 2 * (K1 * (C' * c⁻¹)) + (Kβ * c⁻¹) * 4000 :=
            add_le_add (mul_le_mul hNc_inv hCauτ.2.1 (norm_nonneg _) (by positivity))
              (mul_le_mul hβ_c hQ_bd.2.1 (norm_nonneg _) (by positivity))
        _ = (2 * K1 * C' + 4000 * Kβ) * c⁻¹ := by ring
        _ ≤ (4 * max K0 (max K1 K2) * C' + 4000 * Kβ) * c⁻¹ := by
            gcongr; nlinarith
        _ = C * c⁻¹ := rfl
    · rw [hd2_eq]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_mul, norm_mul, hC_d2, hQ_d2]
      calc ‖Nc⁻¹‖ * ‖deriv (deriv (fctCauchy K4 ε c L1 α (3 / 8))) _‖ + ‖β‖ * ‖deriv (deriv fctQ1) _‖
          ≤ 2 * (K2 * (C' * c⁻¹)) + (Kβ * c⁻¹) * 4000 :=
            add_le_add (mul_le_mul hNc_inv hCauτ.2.2 (norm_nonneg _) (by positivity))
              (mul_le_mul hβ_c hQ_bd.2.2 (norm_nonneg _) (by positivity))
        _ = (2 * K2 * C' + 4000 * Kβ) * c⁻¹ := by ring
        _ ≤ (4 * max K0 (max K1 K2) * C' + 4000 * Kβ) * c⁻¹ := by
            gcongr; nlinarith
        _ = C * c⁻¹ := rfl
  refine ⟨hcd, fun τ => ?_⟩
  have h0_val : fctRightTail h ε c 0 = 0 := by
    unfold fctRightTail
    simp only [Complex.ofReal_zero, zero_mul, sub_zero]
    rw [hphi1, sub_self]
  have hmvt : ‖fctRightTail h ε c τ‖ ≤ C * c⁻¹ * |τ| := by
    have hdiff : ∀ x : ℝ, DifferentiableAt ℝ (fctRightTail h ε c) x :=
      fun x => (hcd.differentiable (by norm_num)) x
    have hbound : ∀ x ∈ segment ℝ (0 : ℝ) τ, ‖deriv (fctRightTail h ε c) x‖ ≤ C * c⁻¹ :=
      fun x _ => (hderiv_unif x).1
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hdiff x)
      (fun x hx => hbound x hx) (convex_segment 0 τ) (left_mem_segment ℝ 0 τ) (right_mem_segment ℝ 0 τ)
    rw [h0_val, sub_zero, Real.norm_eq_abs, sub_zero] at hmv
    exact hmv
  exact ⟨hmvt, (hderiv_unif τ).1, (hderiv_unif τ).2⟩

/-! ### 3. `fctLeftTail` sharp cubic + global `c⁻¹` derivative bounds -/

private lemma hol_cubic_edge_deriv_on_eighth {F : ℂ → ℂ} {M3 : ℝ} (hM3 : 0 ≤ M3)
    (hF : DifferentiableOn ℂ F {ζ : ℂ | |ζ.re| < 3 / 8})
    (hcub : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 / 4 → ‖F ζ‖ ≤ M3 * ‖ζ‖ ^ 3) :
    ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ 1 / 8 →
      ‖F ((τ : ℂ) * Complex.I)‖ ≤ M3 * |τ| ^ 3 ∧
      ‖deriv (fun t : ℝ => F ((t : ℂ) * Complex.I)) τ‖ ≤ (27 / 4 : ℝ) * M3 * |τ| ^ 2 ∧
      ‖deriv (deriv (fun t : ℝ => F ((t : ℂ) * Complex.I))) τ‖ ≤ 27 * M3 * |τ| := by
  intro τ hτ hτ8
  have hnorm : ‖(τ : ℂ) * Complex.I‖ = |τ| := by simp
  have hb0 : ‖F ((τ : ℂ) * Complex.I)‖ ≤ M3 * |τ| ^ 3 := by
    have := hcub ((τ : ℂ) * Complex.I) (by rw [hnorm]; linarith)
    rwa [hnorm] at this
  set r : ℝ := |τ| / 2
  have hr : 0 < r := half_pos (abs_pos.mpr hτ)
  have hU : IsOpen {ζ : ℂ | |ζ.re| < 3 / 8} := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hball : closedBall ((τ : ℂ) * Complex.I) r ⊆ {ζ : ℂ | |ζ.re| < 3 / 8} := fun z hz => by
    have hz' : ‖z - (τ : ℂ) * Complex.I‖ ≤ r := by simpa [dist_eq_norm] using hz
    have hre : |z.re| ≤ r := by
      have : (z - (τ : ℂ) * Complex.I).re = z.re := by simp
      rw [← this]; exact (Complex.abs_re_le_norm _).trans hz'
    show |z.re| < 3 / 8
    exact lt_of_le_of_lt hre (by dsimp [r]; linarith)
  have hsphere : ∀ z ∈ sphere ((τ : ℂ) * Complex.I) r, ‖F z‖ ≤ (27 / 8 : ℝ) * M3 * |τ| ^ 3 := fun z hz => by
    have hz' : ‖z - (τ : ℂ) * Complex.I‖ = r := by simpa [mem_sphere_iff_norm] using hz
    have hzn : ‖z‖ ≤ 3 / 2 * |τ| := by
      calc ‖z‖ = ‖(z - (τ : ℂ) * Complex.I) + (τ : ℂ) * Complex.I‖ := by congr 1; ring
        _ ≤ ‖z - (τ : ℂ) * Complex.I‖ + ‖(τ : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = r + |τ| := by rw [hz', hnorm]
        _ = 3 / 2 * |τ| := by simp [r]; ring
    have hz14 : ‖z‖ ≤ 1 / 4 := by linarith
    calc ‖F z‖ ≤ M3 * ‖z‖ ^ 3 := hcub z hz14
      _ ≤ M3 * (3 / 2 * |τ|) ^ 3 := by gcongr
      _ = (27 / 8 : ℝ) * M3 * |τ| ^ 3 := by ring
  have hc := cauchy_deriv_two hr (hF.mono hball) hsphere
  have hmem : ∀ t : ℝ, 0 + (t : ℂ) * Complex.I ∈ {ζ : ℂ | |ζ.re| < 3 / 8} := fun t => by
    show |((0 : ℂ) + (t : ℂ) * Complex.I).re| < 3 / 8; simp
  obtain ⟨_, hd1, hd2⟩ := line_derivs hU hF 0 Complex.I (by simp) hmem τ
  simp only [zero_add] at hd1 hd2
  refine ⟨hb0, ?_, ?_⟩
  · rw [hd1]
    calc ‖deriv F ((τ : ℂ) * Complex.I)‖
        ≤ ((27 / 8 : ℝ) * M3 * |τ| ^ 3) / r := hc.1
      _ = (27 / 4 : ℝ) * M3 * |τ| ^ 2 := by
          dsimp [r]; have := (abs_pos.mpr hτ).ne'; field_simp; ring
  · rw [hd2]
    calc ‖deriv (deriv F) ((τ : ℂ) * Complex.I)‖
        ≤ 2 * ((27 / 8 : ℝ) * M3 * |τ| ^ 3) / r ^ 2 := hc.2
      _ = 27 * M3 * |τ| := by
          dsimp [r]; have := (abs_pos.mpr hτ).ne'; field_simp; ring

/-- Sharp `O(c⁻¹ |τ|^{3-k})` (`|τ| ≤ 1/8`) and `O(c⁻¹ (1 + |τ|))` (all `τ`) bounds for `fctLeftTail`. -/
theorem fctLeftTail_deriv_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ M c₀ : ℝ, 0 ≤ M ∧ 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ContDiff ℝ 2 (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)) ∧
      (∀ τ : ℝ, |τ| ≤ 1 / 8 →
        ‖fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ‖ ≤ M * c⁻¹ * |τ| ^ 3 ∧
        ‖deriv (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)) τ‖ ≤ M * c⁻¹ * |τ| ^ 2 ∧
        ‖deriv (deriv (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c))) τ‖ ≤ M * c⁻¹ * |τ|) ∧
      (∀ τ : ℝ,
        ‖fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ‖ ≤ M * c⁻¹ * (1 + |τ|) ∧
        ‖deriv (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)) τ‖ ≤ M * c⁻¹ ∧
        ‖deriv (deriv (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c))) τ‖ ≤ M * c⁻¹) := by
  obtain ⟨Cdesc, c0Desc, hDesc⟩ := fctDescent_uncond hK4 h
  obtain ⟨c0s, _, hSetup⟩ := fctSplitting_setup hK4 (fctDescent_uncond hK4 h)
  obtain ⟨Kβ, c0b, hKβ, hNb⟩ := fct_Nc_beta_bounds hK4 (fctDescent_uncond hK4 h)
  obtain ⟨K0, K1, K2, hK0, hK1, hK2, hCau⟩ :=
    fctCauchy_line_deriv_bounds (σ := 7 / 16) (σζ := 0) (by norm_num) le_rfl
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨K3, hK30, hK3⟩ := fctCauchy_norm_le_cubic (σ := 7 / 16) (by norm_num) le_rfl
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C' : ℝ := |Cdesc| / Real.log 2
  have hC'0 : 0 ≤ C' := by positivity
  set M3_c : ℝ := 2 * K3 * C' + 64 * Kβ
  set Mg : ℝ := 2 * max K0 (max K1 K2) * C' + 4000 * Kβ
  set M : ℝ := max (27 * M3_c) Mg
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M, max (max c0Desc c0s) (max c0b 1), hM0,
    le_max_of_le_right (le_max_right _ _), fun ε c hε hc => ?_⟩
  have hc1 : 1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hcDesc := hDesc ε c hε (((le_max_left _ _).trans (le_max_left _ _)).trans hc)
  obtain ⟨hcpos, _, hDc, _, _, _⟩ :=
    hSetup ε c hε (((le_max_right _ _).trans (le_max_left _ _)).trans hc)
  obtain ⟨hNc_inv, hβ_c, _⟩ :=
    hNb ε c hε (((le_max_left _ _).trans (le_max_right _ _)).trans hc)
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set Nc := fctNcC K4 ε c L1 α
  set β := fctBetaC K4 ε c L1 α
  have hFc : ∀ y : ℝ, ‖fctFint K4 ε c L1 α (((7 / 16 : ℝ) : ℂ) + y * Complex.I)‖ ≤ C' * c⁻¹ := fun y => by
    have hb := hcDesc (7 / 16) y (by norm_num) (by norm_num)
    have hly : 0 < Real.log (2 + |y|) := Real.log_pos (by linarith [abs_nonneg y])
    have hl : Real.log 2 ≤ Real.log (2 + |y|) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg y])
    calc ‖fctFint K4 ε c L1 α (((7 / 16 : ℝ) : ℂ) + y * Complex.I)‖
        ≤ Cdesc * c⁻¹ / Real.log (2 + |y|) := hb
      _ ≤ |Cdesc| * c⁻¹ / Real.log (2 + |y|) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) hly.le
      _ ≤ |Cdesc| * c⁻¹ / Real.log 2 :=
          div_le_div_of_nonneg_left (by positivity) hlog2_pos hl
      _ = C' * c⁻¹ := by simp only [C']; ring
  set U : Set ℂ := {ζ : ℂ | |ζ.re| < 3 / 8}
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hC_hol : DifferentiableOn ℂ (fctCauchy K4 ε c L1 α (7 / 16)) U :=
    fctCauchy_differentiableOn hcpos hDc (by norm_num) le_rfl hFc hU fun w hw => by
      have hw' : |w.re| < 3 / 8 := hw
      have ha := abs_lt.mp hw'
      exact ⟨by linarith, by linarith⟩
  have hQ_hol : DifferentiableOn ℂ fctQ1 U :=
    fctQ1_differentiableOn_rhp.mono fun z hz => by
      have hz' : |z.re| < 3 / 8 := hz
      change -1 / 2 < z.re
      linarith [(abs_lt.mp hz').1]
  set G : ℂ → ℂ := fun ζ => -(Nc⁻¹ * fctCauchy K4 ε c L1 α (7 / 16) ζ) + β * fctQ1 ζ
  have hG_hol : DifferentiableOn ℂ G U :=
    ((differentiableOn_const _).mul hC_hol).neg.add ((differentiableOn_const _).mul hQ_hol)
  have hG_eq : fctLeftTail K4 ε c L1 α = fun t : ℝ => G ((t : ℂ) * Complex.I) := by
    funext t; unfold fctLeftTail; simp only [G, div_eq_mul_inv]; ring
  have hmem : ∀ t : ℝ, 0 + (t : ℂ) * Complex.I ∈ U := fun t => by
    show |((0 : ℂ) + (t : ℂ) * Complex.I).re| < 3 / 8; simp
  have hC_cd : ContDiff ℝ 2 (fun t : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (t : ℂ) * Complex.I)) :=
    (line_derivs hU hC_hol 0 Complex.I (by simp) hmem 0).1
  have hQ_cd : ContDiff ℝ 2 (fun t : ℝ => fctQ1 ((0 : ℂ) + (t : ℂ) * Complex.I)) :=
    (line_derivs hU hQ_hol 0 Complex.I (by simp) hmem 0).1
  have hcd : ContDiff ℝ 2 (fctLeftTail K4 ε c L1 α) := by
    rw [hG_eq]
    have : (fun t : ℝ => G ((t : ℂ) * Complex.I)) = fun t : ℝ =>
        -(Nc⁻¹ * fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (t : ℂ) * Complex.I)) +
          β * fctQ1 ((0 : ℂ) + (t : ℂ) * Complex.I) := funext fun t => by simp [G]
    rw [this]
    exact (contDiff_const.mul hC_cd).neg.add (contDiff_const.mul hQ_cd)
  have hG_cub : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 / 4 → ‖G ζ‖ ≤ (M3_c * c⁻¹) * ‖ζ‖ ^ 3 := fun ζ hζ => by
    have hC3 := hK3 K4 ε c L1 α (C' * c⁻¹) (by positivity) hFc ζ hζ
    have hQ3 : ‖fctQ1 ζ‖ ≤ 64 * ‖ζ‖ ^ 3 := by
      unfold fctQ1
      have h1 : ‖1 - ζ‖ ≤ 5 / 4 := (norm_sub_le 1 ζ).trans (by norm_num; linarith)
      have h2 : 3 / 4 ≤ ‖ζ + 1‖ := by
        have := norm_sub_norm_le (1 : ℂ) (-ζ)
        rw [norm_one, norm_neg, sub_neg_eq_add, add_comm] at this
        linarith
      rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
      have hn16 : ‖(16 : ℂ)‖ = 16 := by simp
      rw [hn16]
      calc 16 * ‖ζ‖ ^ 3 * ‖1 - ζ‖ / ‖ζ + 1‖ ^ 4
          ≤ 16 * ‖ζ‖ ^ 3 * (5 / 4) / (3 / 4) ^ 4 := by gcongr
        _ = (16 * (5 / 4) / (3 / 4) ^ 4) * ‖ζ‖ ^ 3 := by ring
        _ ≤ 64 * ‖ζ‖ ^ 3 := by gcongr; norm_num
    dsimp only [G]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_mul]
    calc ‖Nc⁻¹‖ * ‖fctCauchy K4 ε c L1 α (7 / 16) ζ‖ + ‖β‖ * ‖fctQ1 ζ‖
        ≤ 2 * (K3 * (C' * c⁻¹) * ‖ζ‖ ^ 3) + (Kβ * c⁻¹) * (64 * ‖ζ‖ ^ 3) :=
          add_le_add (mul_le_mul hNc_inv hC3 (norm_nonneg _) (by positivity))
            (mul_le_mul hβ_c hQ3 (norm_nonneg _) (by positivity))
      _ = (M3_c * c⁻¹) * ‖ζ‖ ^ 3 := by simp only [M3_c]; ring
  have hsmall_nz := hol_cubic_edge_deriv_on_eighth (M3 := M3_c * c⁻¹) (by positivity) hG_hol hG_cub
  have hG0 : fctLeftTail K4 ε c L1 α 0 = 0 := by
    rw [hG_eq]; exact norm_le_zero_iff.mp (by simpa using hG_cub 0 (by norm_num))
  have hG1_0 : deriv (fctLeftTail K4 ε c L1 α) 0 = 0 := by
    have hcont : Continuous (deriv (fctLeftTail K4 ε c L1 α)) :=
      hcd.continuous_deriv (by norm_num)
    have htend : Tendsto (deriv (fctLeftTail K4 ε c L1 α)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero'
        (g := fun t : ℝ => (27 / 4 : ℝ) * (M3_c * c⁻¹) * |t| ^ 2)
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_)
      · filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-(1 / 8 : ℝ)) < 0)
            (by norm_num : (0 : ℝ) < 1 / 8)), self_mem_nhdsWithin] with t ht (hne : t ≠ 0)
        have hab : |t| ≤ 1 / 8 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
        have hb := (hsmall_nz t hne hab).2.1
        rwa [← hG_eq] at hb
      · have hlim : Tendsto (fun t : ℝ => (27 / 4 : ℝ) * (M3_c * c⁻¹) * |t| ^ 2) (𝓝 0) (𝓝 0) := by
          have hc : Continuous (fun t : ℝ => (27 / 4 : ℝ) * (M3_c * c⁻¹) * |t| ^ 2) := by fun_prop
          convert hc.tendsto 0 using 2; simp
        exact hlim.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) htend
  have hG2_0 : deriv (deriv (fctLeftTail K4 ε c L1 α)) 0 = 0 := by
    have hcont : Continuous (deriv (deriv (fctLeftTail K4 ε c L1 α))) :=
      (hcd.iterate_deriv' 1 1).continuous_deriv (by norm_num)
    have htend : Tendsto (deriv (deriv (fctLeftTail K4 ε c L1 α))) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero'
        (g := fun t : ℝ => 27 * (M3_c * c⁻¹) * |t|)
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_)
      · filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-(1 / 8 : ℝ)) < 0)
            (by norm_num : (0 : ℝ) < 1 / 8)), self_mem_nhdsWithin] with t ht (hne : t ≠ 0)
        have hab : |t| ≤ 1 / 8 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
        have hb := (hsmall_nz t hne hab).2.2
        rwa [← hG_eq] at hb
      · have hlim : Tendsto (fun t : ℝ => 27 * (M3_c * c⁻¹) * |t|) (𝓝 0) (𝓝 0) := by
          have hc : Continuous (fun t : ℝ => 27 * (M3_c * c⁻¹) * |t|) := by fun_prop
          convert hc.tendsto 0 using 2; simp
        exact hlim.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) htend
  refine ⟨hcd, fun τ hτ => ?_, fun τ => ?_⟩
  · by_cases h0 : τ = 0
    · subst h0; simp [hG0, hG1_0, hG2_0]
    · obtain ⟨hb0, hb1, hb2⟩ := hsmall_nz τ h0 hτ
      have hb0' : ‖fctLeftTail K4 ε c L1 α τ‖ ≤ M3_c * c⁻¹ * |τ| ^ 3 := by
        rw [hG_eq]; exact hb0
      rw [← hG_eq] at hb1 hb2
      have hM3_le : 27 * M3_c ≤ M := le_max_left _ _
      refine ⟨hb0'.trans ?_, hb1.trans ?_, hb2.trans ?_⟩
      · have : M3_c ≤ M := by linarith [show 0 ≤ M3_c by positivity]
        gcongr
      · have : 27 / 4 * M3_c ≤ M := by linarith [show 0 ≤ M3_c by positivity]
        calc 27 / 4 * (M3_c * c⁻¹) * |τ| ^ 2 = (27 / 4 * M3_c) * c⁻¹ * |τ| ^ 2 := by ring
          _ ≤ M * c⁻¹ * |τ| ^ 2 := by gcongr
      · calc 27 * (M3_c * c⁻¹) * |τ| = (27 * M3_c) * c⁻¹ * |τ| := by ring
          _ ≤ M * c⁻¹ * |τ| := by gcongr
  · obtain ⟨_, hC_d1, hC_d2⟩ := line_derivs hU hC_hol 0 Complex.I (by simp) hmem τ
    obtain ⟨_, hQ_d1, hQ_d2⟩ := line_derivs hU hQ_hol 0 Complex.I (by simp) hmem τ
    have hCau_bd := hCau K4 ε c L1 α (C' * c⁻¹) hcpos hDc (by positivity) hFc τ
    dsimp only at hCau_bd
    simp only [Complex.ofReal_zero, zero_add] at hCau_bd
    have hQ_bd := fctQ1_deriv_bounds (ζ := (τ : ℂ) * Complex.I) (by simp)
    have hK0le : K0 ≤ max K0 (max K1 K2) := le_max_left _ _
    have hK1le : K1 ≤ max K0 (max K1 K2) := (le_max_left _ _).trans (le_max_right _ _)
    have hK2le : K2 ≤ max K0 (max K1 K2) := (le_max_right _ _).trans (le_max_right _ _)
    have hMg_le : Mg ≤ M := le_max_right _ _
    have hfn_c : fctLeftTail K4 ε c L1 α = fun t : ℝ =>
        -(Nc⁻¹ * fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (t : ℂ) * Complex.I)) +
          β * fctQ1 ((0 : ℂ) + (t : ℂ) * Complex.I) := by
      funext t; unfold fctLeftTail; simp [div_eq_mul_inv]; ring
    have hd1_eq : ∀ t : ℝ, deriv (fctLeftTail K4 ε c L1 α) t =
        -(Nc⁻¹ * deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I)) t) +
          β * deriv (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I)) t := fun t => by
      rw [hfn_c]
      have h1 : DifferentiableAt ℝ
          (fun s : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I)) t :=
        (hC_cd.differentiable (by norm_num)) t
      have h2 : DifferentiableAt ℝ (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I)) t :=
        (hQ_cd.differentiable (by norm_num)) t
      exact (((h1.hasDerivAt.const_mul Nc⁻¹).neg).add (h2.hasDerivAt.const_mul β)).deriv
    have hd2_eq : deriv (deriv (fctLeftTail K4 ε c L1 α)) τ =
        -(Nc⁻¹ * deriv (deriv (fun s : ℝ =>
            fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I))) τ) +
          β * deriv (deriv (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I))) τ := by
      rw [funext hd1_eq]
      have hC1 : ContDiff ℝ 1
          (deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I))) :=
        hC_cd.iterate_deriv' 1 1
      have hQ1 : ContDiff ℝ 1 (deriv (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I))) :=
        hQ_cd.iterate_deriv' 1 1
      have h1 : DifferentiableAt ℝ
          (deriv (fun s : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((0 : ℂ) + (s : ℂ) * Complex.I))) τ :=
        (hC1.differentiable one_ne_zero) τ
      have h2 : DifferentiableAt ℝ (deriv (fun s : ℝ => fctQ1 ((0 : ℂ) + (s : ℂ) * Complex.I))) τ :=
        (hQ1.differentiable one_ne_zero) τ
      exact (((h1.hasDerivAt.const_mul Nc⁻¹).neg).add (h2.hasDerivAt.const_mul β)).deriv
    refine ⟨?_, ?_, ?_⟩
    · unfold fctLeftTail
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, div_eq_mul_inv, norm_mul, norm_mul]
      have hq1_le : ‖fctQ1 ((τ : ℂ) * Complex.I)‖ ≤ 4000 * (1 + |τ|) :=
        hQ_bd.1.trans (by nlinarith [abs_nonneg τ])
      calc ‖fctCauchy K4 ε c L1 α (7 / 16) ((τ : ℂ) * Complex.I)‖ * ‖Nc⁻¹‖ +
            ‖β‖ * ‖fctQ1 ((τ : ℂ) * Complex.I)‖
          ≤ (K0 * (C' * c⁻¹) * (1 + |τ|)) * 2 + (Kβ * c⁻¹) * (4000 * (1 + |τ|)) :=
            add_le_add (mul_le_mul hCau_bd.1 hNc_inv (norm_nonneg _) (by positivity))
              (mul_le_mul hβ_c hq1_le (norm_nonneg _) (by positivity))
        _ = (2 * K0 * C' + 4000 * Kβ) * c⁻¹ * (1 + |τ|) := by ring
        _ ≤ Mg * c⁻¹ * (1 + |τ|) := by simp only [Mg]; gcongr
        _ ≤ M * c⁻¹ * (1 + |τ|) := by gcongr
    · rw [hd1_eq τ]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_mul, norm_mul, hC_d1, hQ_d1]
      simp only [zero_add]
      calc ‖Nc⁻¹‖ * ‖deriv (fctCauchy K4 ε c L1 α (7 / 16)) ((τ : ℂ) * Complex.I)‖ +
            ‖β‖ * ‖deriv fctQ1 ((τ : ℂ) * Complex.I)‖
          ≤ 2 * (K1 * (C' * c⁻¹)) + (Kβ * c⁻¹) * 4000 :=
            add_le_add (mul_le_mul hNc_inv hCau_bd.2.1 (norm_nonneg _) (by positivity))
              (mul_le_mul hβ_c hQ_bd.2.1 (norm_nonneg _) (by positivity))
        _ = (2 * K1 * C' + 4000 * Kβ) * c⁻¹ := by ring
        _ ≤ Mg * c⁻¹ := by simp only [Mg]; gcongr
        _ ≤ M * c⁻¹ := by gcongr
    · rw [hd2_eq]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_mul, norm_mul, hC_d2, hQ_d2]
      simp only [zero_add]
      calc ‖Nc⁻¹‖ * ‖deriv (deriv (fctCauchy K4 ε c L1 α (7 / 16))) ((τ : ℂ) * Complex.I)‖ +
            ‖β‖ * ‖deriv (deriv fctQ1) ((τ : ℂ) * Complex.I)‖
          ≤ 2 * (K2 * (C' * c⁻¹)) + (Kβ * c⁻¹) * 4000 :=
            add_le_add (mul_le_mul hNc_inv hCau_bd.2.2 (norm_nonneg _) (by positivity))
              (mul_le_mul hβ_c hQ_bd.2.2 (norm_nonneg _) (by positivity))
        _ = (2 * K2 * C' + 4000 * Kβ) * c⁻¹ := by ring
        _ ≤ Mg * c⁻¹ := by simp only [Mg]; gcongr
        _ ≤ M * c⁻¹ := by gcongr

/-! ### 4. Shared `D * ctHG` and `c K₀ Ψ_c` bounds on the left edge -/

lemma dcomp_ctHG_EJ {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ M c₀ : ℝ, 0 ≤ M ∧ 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      EJ (fun τ : ℝ => fctDcompAt K4 c (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) *
        ctHG ε ((τ : ℂ) * Complex.I)) (-(5 / 2)) 10 1 M := by
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨B, c0D, hvdata⟩ := fctDcomp_vdata hK4 ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨v1, -, -, -, hvB1, -⟩ := hvdata 1 (max c0D 1) (Or.inl rfl) (le_max_left _ _)
  have hB0 : 0 ≤ B 0 := (norm_nonneg _).trans (by simpa using hvB1 0 (by norm_num) 0 ⟨le_rfl, zero_le_one⟩)
  have hB1 : 0 ≤ B 1 := (norm_nonneg _).trans (by simpa using hvB1 1 (by norm_num) 0 ⟨le_rfl, zero_le_one⟩)
  have hB2 : 0 ≤ B 2 := (norm_nonneg _).trans (by simpa using hvB1 2 (by norm_num) 0 ⟨le_rfl, zero_le_one⟩)
  set P : ℝ := Real.exp (B 0) * max 1 (max (B 1) (B 2 + B 1 ^ 2)) with hPdef
  have hP0 : 0 ≤ P := by positivity
  obtain ⟨MZ1, hZE1⟩ := ejZE 1
  obtain ⟨MZm1, hZEm1⟩ := ejZE (-1)
  set MZ : ℝ := max MZ1 MZm1
  have hMZ0 : 0 ≤ MZ := le_max_of_le_left hZE1.hM
  set M : ℝ := 4 * (4 * (4 * P * MZ) * 9) * 9
  refine ⟨M, max c0D 1, by positivity, le_max_right _ _, fun ε c hε hc => ?_⟩
  obtain ⟨v, hv, hs, -, hb, hD_eq⟩ := hvdata ε c hε ((le_max_left _ _).trans hc)
  have hθ : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD v) := contDiff_fctThetaD hv hs
  set G : ℝ → ℂ := fun τ => (v τ : ℂ) + Complex.I * ((fctThetaD v τ : ℝ) : ℂ)
  set G1 : ℝ → ℂ := fun τ =>
    ((iteratedDeriv 1 v τ : ℝ) : ℂ) + Complex.I * ((iteratedDeriv 1 (fctThetaD v) τ : ℝ) : ℂ)
  set G2 : ℝ → ℂ := fun τ =>
    ((iteratedDeriv 2 v τ : ℝ) : ℂ) + Complex.I * ((iteratedDeriv 2 (fctThetaD v) τ : ℝ) : ℂ)
  have hg_eq : ∀ τ : ℝ, stripCompGExt v ((τ : ℂ) * Complex.I) = G τ := fun τ => by
    rw [stripCompGExt_left]
  have hG0_bd : ∀ τ : ℝ, ‖G τ‖ ≤ B 0 := fun τ => by
    have := hb 0 (by norm_num) ((τ : ℂ) * Complex.I) ⟨by simp, by simp⟩
    simpa [iteratedDeriv_zero, hg_eq] using this
  have hG1_bd : ∀ τ : ℝ, ‖G1 τ‖ ≤ B 1 := fun τ => by
    have := hb 1 (by norm_num) ((τ : ℂ) * Complex.I) ⟨by simp, by simp⟩
    rw [stripCompGExt_left, ← iteratedDeriv_fctThetaD hv hs 1] at this
    exact this
  have hG2_bd : ∀ τ : ℝ, ‖G2 τ‖ ≤ B 2 := fun τ => by
    have := hb 2 (by norm_num) ((τ : ℂ) * Complex.I) ⟨by simp, by simp⟩
    rw [stripCompGExt_left, ← iteratedDeriv_fctThetaD hv hs 2] at this
    exact this
  have hG_cd : ContDiff ℝ 2 G :=
    (Complex.ofRealCLM.contDiff.comp (hv.of_le (by norm_num))).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hθ.of_le (by norm_num))))
  have hG1_deriv : ∀ τ : ℝ, HasDerivAt G (G1 τ) τ := fun τ => by
    have h1 : HasDerivAt (fun t : ℝ => (v t : ℂ)) ((iteratedDeriv 1 v τ : ℝ) : ℂ) τ := by
      have hd := (hv.differentiable (by norm_num) τ).hasDerivAt
      simpa [Function.comp_def, iteratedDeriv_one] using (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt τ hd)
    have h2 : HasDerivAt (fun t : ℝ => (fctThetaD v t : ℂ))
        ((iteratedDeriv 1 (fctThetaD v) τ : ℝ) : ℂ) τ := by
      have hd := (hθ.differentiable (by norm_num) τ).hasDerivAt
      simpa [Function.comp_def, iteratedDeriv_one] using (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt τ hd)
    exact h1.add (h2.const_mul Complex.I)
  have hG2_deriv : ∀ τ : ℝ, HasDerivAt G1 (G2 τ) τ := fun τ => by
    have hle : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
    have hv1 : ContDiff ℝ 1 (iteratedDeriv 1 v) := by
      simpa [iteratedDeriv_one] using (hv.of_le hle).iterate_deriv' 1 1
    have hθ1 : ContDiff ℝ 1 (iteratedDeriv 1 (fctThetaD v)) := by
      simpa [iteratedDeriv_one] using (hθ.of_le hle).iterate_deriv' 1 1
    have h1 : HasDerivAt (fun t : ℝ => ((iteratedDeriv 1 v t : ℝ) : ℂ))
        ((iteratedDeriv 2 v τ : ℝ) : ℂ) τ := by
      have hd := (hv1.differentiable one_ne_zero τ).hasDerivAt
      rw [show iteratedDeriv 2 v τ = deriv (iteratedDeriv 1 v) τ from
        congrFun (iteratedDeriv_succ (f := v) (n := 1)) τ]
      simpa [Function.comp_def] using (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt τ hd)
    have h2 : HasDerivAt (fun t : ℝ => ((iteratedDeriv 1 (fctThetaD v) t : ℝ) : ℂ))
        ((iteratedDeriv 2 (fctThetaD v) τ : ℝ) : ℂ) τ := by
      have hd := (hθ1.differentiable one_ne_zero τ).hasDerivAt
      rw [show iteratedDeriv 2 (fctThetaD v) τ = deriv (iteratedDeriv 1 (fctThetaD v)) τ from
        congrFun (iteratedDeriv_succ (f := fctThetaD v) (n := 1)) τ]
      simpa [Function.comp_def] using (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt τ hd)
    exact h1.add (h2.const_mul Complex.I)
  set Dtrace : ℝ → ℂ := fun τ => Complex.exp (G τ)
  have hD_cd : ContDiff ℝ 2 Dtrace := hG_cd.cexp
  have hD0 : ∀ τ : ℝ, ‖Dtrace τ‖ ≤ Real.exp (B 0) := fun τ => by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hG0_bd τ))
  have hD1_eq : ∀ τ : ℝ, deriv Dtrace τ = G1 τ * Dtrace τ := fun τ => by
    have := (hG1_deriv τ).cexp
    simpa [Dtrace, mul_comm] using this.deriv
  have hD2_eq : ∀ τ : ℝ, deriv (deriv Dtrace) τ = (G2 τ + G1 τ ^ 2) * Dtrace τ := fun τ => by
    rw [funext hD1_eq]
    have hd := (hG2_deriv τ).mul ((hG1_deriv τ).cexp)
    have hrw : G2 τ * Dtrace τ + G1 τ * (Dtrace τ * G1 τ) = (G2 τ + G1 τ ^ 2) * Dtrace τ := by
      dsimp [Dtrace]; ring
    exact hd.deriv.trans hrw
  have hDe : EJ Dtrace 0 0 0 P := by
    refine ⟨hP0, hD_cd.contDiffOn, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩
    · have e0 : ejW 0 0 0 0 τ = 1 := by unfold ejW; simp
      rw [e0, mul_one]
      calc ‖Dtrace τ‖ ≤ Real.exp (B 0) := hD0 τ
        _ ≤ Real.exp (B 0) * max 1 (max (B 1) (B 2 + B 1 ^ 2)) :=
            le_mul_of_one_le_right (Real.exp_pos _).le (le_max_left _ _)
    · have e1 : 1 ≤ ejW 0 0 0 1 τ := by
        unfold ejW; simp
        have h0 : 0 < |τ| := abs_pos.mpr hτ
        rw [Real.rpow_neg_one, ← div_eq_inv_mul, le_div_iff₀ h0]
        linarith
      rw [hD1_eq τ, norm_mul]
      calc ‖G1 τ‖ * ‖Dtrace τ‖ ≤ B 1 * Real.exp (B 0) :=
            mul_le_mul (hG1_bd τ) (hD0 τ) (norm_nonneg _) hB1
        _ = Real.exp (B 0) * B 1 := by ring
        _ ≤ P * 1 := by
            rw [mul_one, hPdef]; gcongr
            exact (le_max_left _ _).trans (le_max_right _ _)
        _ ≤ P * ejW 0 0 0 1 τ := mul_le_mul_of_nonneg_left e1 hP0
    · have e2 : 1 ≤ ejW 0 0 0 2 τ := by
        unfold ejW; simp
        have h0 : 0 < τ ^ 2 := sq_pos_of_ne_zero hτ
        rw [← div_eq_inv_mul, le_div_iff₀ h0]
        nlinarith [sq_abs τ, abs_nonneg τ]
      rw [hD2_eq τ, norm_mul]
      have hG21 : ‖G2 τ + G1 τ ^ 2‖ ≤ B 2 + B 1 ^ 2 := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_pow]
        exact add_le_add (hG2_bd τ) (pow_le_pow_left₀ (norm_nonneg _) (hG1_bd τ) 2)
      calc ‖G2 τ + G1 τ ^ 2‖ * ‖Dtrace τ‖ ≤ (B 2 + B 1 ^ 2) * Real.exp (B 0) :=
            mul_le_mul hG21 (hD0 τ) (norm_nonneg _) (by positivity)
        _ = Real.exp (B 0) * (B 2 + B 1 ^ 2) := by ring
        _ ≤ P * 1 := by
            rw [mul_one, hPdef]; gcongr
            exact (le_max_right _ _).trans (le_max_right _ _)
        _ ≤ P * ejW 0 0 0 2 τ := mul_le_mul_of_nonneg_left e2 hP0
  have hZE_u : EJ (fun τ : ℝ => uctSeedZ ε ((τ : ℂ) * Complex.I) *
      Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))) 0 10 1 MZ := by
    rcases hε with rfl | rfl
    · refine ⟨hMZ0, hZE1.c2, ?_, ?_, ?_⟩ <;> intro τ hτ
      · exact (hZE1.b0 τ hτ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (ejW_pos hτ).le)
      · exact (hZE1.b1 τ hτ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (ejW_pos hτ).le)
      · exact (hZE1.b2 τ hτ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (ejW_pos hτ).le)
    · refine ⟨hMZ0, hZEm1.c2, ?_, ?_, ?_⟩ <;> intro τ hτ
      · exact (hZEm1.b0 τ hτ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (ejW_pos hτ).le)
      · exact (hZEm1.b1 τ hτ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (ejW_pos hτ).le)
      · exact (hZEm1.b2 τ hτ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (ejW_pos hτ).le)
  have hbase := (((hDe.mul hZE_u).mul edgeR_EJ).mul edgeS_EJ).cast (a' := -(5 / 2)) (b' := 1)
    (by norm_num) (by norm_num)
  have heq : (fun τ : ℝ => fctDcompAt K4 c (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) *
      ctHG ε ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ => Dtrace τ * (uctSeedZ ε ((τ : ℂ) * Complex.I) *
        Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))) * edgeR τ * edgeS τ := by
    funext τ
    have hd : fctDcompAt K4 c (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) = Dtrace τ := by
      have := hD_eq ((τ : ℂ) * Complex.I)
      change fctDcomp K4 (fctWarpAlpha h) ε c ((τ : ℂ) * Complex.I) = Dtrace τ
      rw [this, hg_eq]
    rw [hd, ctHG_edge]; ring
  rw [heq]
  exact hbase

lemma fctPsi_imag_small_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ c ^ (-(1 / 3 : ℝ)) →
        ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          ((c : ℂ) * fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I))‖ ≤
          C * c * |τ| ^ (1 / 2 : ℝ) := by
  obtain ⟨MD, c0D, hMD0, hc0D, hDHG⟩ := dcomp_ctHG_EJ hK4 h
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨B, c0Dv, hvdata⟩ := fctDcomp_vdata hK4 ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨CL1, c0L1, hCL10, hc0L1, hL1_bd⟩ := abs_fctWarpL1_le h
  obtain ⟨Cpk, hCpk0, hCpk⟩ := FctPhiKill.norm_phiPQ_le 8 8
  set c₀ : ℝ := max (max c0D (max c0L1 c0Dv)) 8
  set M_A : ℝ := (1 + |CL1| * Cpk) * (2 ^ 10 * MD)
  set C : ℝ := 2 * M_A
  refine ⟨C, c₀, by positivity, by linarith [le_max_right (max c0D (max c0L1 c0Dv)) (8 : ℝ)], fun ε c ξ hε hc hξ τ hτ hτc => ?_⟩
  have hc8 : 8 ≤ c := (le_max_right _ _).trans hc
  have hcpos : 0 < c := by linarith
  have hL1c := hL1_bd ε c hε (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _) |>.trans hc)
  have hEJ := hDHG ε c hε (((le_max_left _ _).trans (le_max_left _ _)).trans hc)
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  have hK_eq : mellinK0 c ((τ : ℂ) * Complex.I) ξ * ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)) =
      (c : ℂ) * Complex.exp ((c : ℂ) * ((τ : ℂ) * Complex.I) * ((Real.log (π ^ 2 * ξ) - L1 : ℝ) : ℂ)) *
        (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)) := by
    have hphi_dif : (c : ℂ) * mellinPhi ((τ : ℂ) * Complex.I) ξ =
        (c : ℂ) * mellinPhi ((τ : ℂ) * Complex.I) (fctXi1 L1) +
        (c : ℂ) * ((τ : ℂ) * Complex.I) * ((Real.log (π ^ 2 * ξ) - L1 : ℝ) : ℂ) := by
      unfold mellinPhi
      have hxi1 : 0 < fctXi1 L1 := fctXi1_pos L1
      have hlog : Complex.log ((π : ℂ) ^ 2 * (fctXi1 L1 : ℂ)) = (L1 : ℂ) := by
        have hp : Real.log (π ^ 2 * fctXi1 L1) = L1 := by
          unfold fctXi1
          rw [mul_div_cancel₀ _ (by positivity : π ^ 2 ≠ 0), Real.log_exp]
        rw [show (π : ℂ) ^ 2 * (fctXi1 L1 : ℂ) = ((π ^ 2 * fctXi1 L1 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_log (by positivity), hp]
      have hlogξ : Complex.log ((π : ℂ) ^ 2 * (ξ : ℂ)) = (Real.log (π ^ 2 * ξ) : ℂ) := by
        rw [show (π : ℂ) ^ 2 * (ξ : ℂ) = ((π ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_log (by positivity)]
      rw [hlog, hlogξ]; push_cast; ring
    have hm_rel : mellinK0 c ((τ : ℂ) * Complex.I) ξ =
        Complex.exp ((c : ℂ) * ((τ : ℂ) * Complex.I) * ((Real.log (π ^ 2 * ξ) - L1 : ℝ) : ℂ)) *
          mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) := by
      unfold mellinK0
      rw [hphi_dif, Complex.exp_add]
      ring
    rw [hm_rel]; ring
  have hexp_norm : ‖Complex.exp ((c : ℂ) * ((τ : ℂ) * Complex.I) * ((Real.log (π ^ 2 * ξ) - L1 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : ((c : ℂ) * ((τ : ℂ) * Complex.I) * ((Real.log (π ^ 2 * ξ) - L1 : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  have hpsi_eq : mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      ((τ : ℂ) * Complex.I) * ∫ s in (0 : ℝ)..1, fctWarpKA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I)) := by
    unfold fctPsi fctWarpKA
    have hne := mellinK0_ne_zero c (by simp : ((τ : ℂ) * Complex.I).re < 1) (fctXi1 L1)
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have ha_pos : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hcpos _
  have hKA_bd : ∀ s ∈ uIoc (0 : ℝ) 1,
      ‖fctWarpKA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I))‖ ≤ M_A * (|τ| ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) := by
    intro s hs
    have hs_mem : s ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc_of_le zero_le_one] using hs
    have hs0 : 0 < s := hs_mem.1
    have hs1 : s ≤ 1 := hs_mem.2
    set t : ℝ := s * τ
    have ht_ne : t ≠ 0 := mul_ne_zero hs0.ne' hτ
    have ht_eq : (s : ℂ) * ((τ : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by push_cast [t]; ring
    rw [ht_eq]
    have ht_abs : |t| ≤ c ^ (-(1 / 3 : ℝ)) := by
      rw [abs_mul, abs_of_pos hs0]
      calc s * |τ| ≤ 1 * |τ| := by gcongr
        _ = |τ| := one_mul _
        _ ≤ _ := hτc
    have ht_le1 : |t| ≤ 1 := ht_abs.trans (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num))
    unfold fctWarpKA fctWarpA
    have hm_le : ‖mellinK0 c ((t : ℂ) * Complex.I) (fctXi1 L1)‖ ≤ 1 :=
      (norm_mellinK0_imag_le hcpos (fctXi1_pos L1) t).2.trans
        (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg t]) (by norm_num))
    have hg_bd : ‖stripG ((t : ℂ) * Complex.I)‖ ≤ t ^ 2 := by
      rw [stripG_imag_eq_neg_m ht_ne, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hankelEdgeM_nonneg (abs_nonneg t))]
      have hsq := hankelEdgeM_le_sq (abs_nonneg t)
      have hπ : Real.pi ^ 2 / 12 ≤ 1 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      calc hankelEdgeM |t| ≤ Real.pi ^ 2 / 12 * |t| ^ 2 := hsq
        _ ≤ 1 * |t| ^ 2 := by gcongr
        _ = t ^ 2 := by simp [sq_abs]
    have hpk_bd : ‖(L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I)‖ ≤ |CL1| * Cpk * t ^ 2 := by
      have hp := hCpk ha_pos (by simp : 0 ≤ ((t : ℂ) * Complex.I).re)
      rw [show ‖(t : ℂ) * Complex.I‖ = |t| by simp] at hp
      have hm1 : min ((|t| / c ^ (-(1 / 12 : ℝ))) ^ 8) 1 ≤ (|t| / c ^ (-(1 / 12 : ℝ))) ^ 8 := min_le_left _ _
      have hdiv : c ^ (-(2 / 3 : ℝ)) * (|t| / c ^ (-(1 / 12 : ℝ))) ^ 8 = |t| ^ 8 := by
        rw [div_pow, ← Real.rpow_natCast (c ^ (-(1 / 12 : ℝ))) 8, ← Real.rpow_mul hcpos.le]
        have hpow_eq : (-(1 / 12 : ℝ)) * (8 : ℕ) = -(2 / 3 : ℝ) := by norm_num
        rw [hpow_eq]
        field_simp [(Real.rpow_pos_of_pos hcpos (-(2 / 3 : ℝ))).ne']
      have h82 : |t| ^ 8 ≤ t ^ 2 := by
        rw [← sq_abs t]
        have : |t| ^ 8 = |t| ^ 2 * |t| ^ 6 := by ring
        rw [this]
        exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (abs_nonneg _) ht_le1)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hL1c' : |L1| ≤ |CL1| * c ^ (-(2 / 3 : ℝ)) :=
        hL1c.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      calc |L1| * ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I)‖
          ≤ (|CL1| * c ^ (-(2 / 3 : ℝ))) * (Cpk * (|t| / c ^ (-(1 / 12 : ℝ))) ^ 8) :=
            mul_le_mul hL1c' (hp.trans (mul_le_mul_of_nonneg_left hm1 hCpk0)) (norm_nonneg _) (by positivity)
        _ = |CL1| * Cpk * (c ^ (-(2 / 3 : ℝ)) * (|t| / c ^ (-(1 / 12 : ℝ))) ^ 8) := by ring
        _ = |CL1| * Cpk * |t| ^ 8 := by rw [hdiv]
        _ ≤ |CL1| * Cpk * t ^ 2 := mul_le_mul_of_nonneg_left h82 (by positivity)
    have hdhg_bd : ‖fctDcompAt K4 c α ((t : ℂ) * Complex.I) * ctHG ε ((t : ℂ) * Complex.I)‖ ≤
        2 ^ 10 * MD * |t| ^ (-(5 / 2 : ℝ)) := by
      have hb := hEJ.b0 t ht_ne
      unfold ejW at hb
      have hexp1 : Real.exp (-(π * 1 * |t|)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg Real.pi_pos.le zero_le_one) (abs_nonneg t)))
      have hp1 : (1 + |t|) ^ (10 + 0) ≤ 2 ^ 10 := pow_le_pow_left₀ (by positivity) (by linarith) 10
      have hsub : (-(5 / 2 : ℝ)) - ((0 : ℕ) : ℝ) = -(5 / 2 : ℝ) := by norm_num
      rw [hsub] at hb
      have hrp_nn : 0 ≤ |t| ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg t) _
      calc _ ≤ MD * (|t| ^ (-(5 / 2 : ℝ)) * (1 + |t|) ^ (10 + 0) * Real.exp (-(π * 1 * |t|))) := hb
        _ ≤ MD * (|t| ^ (-(5 / 2 : ℝ)) * 2 ^ 10 * 1) := by gcongr
        _ = 2 ^ 10 * MD * |t| ^ (-(5 / 2 : ℝ)) := by ring
    have hpow_simp : t ^ 2 * |t| ^ (-(5 / 2 : ℝ)) = |t| ^ (-(1 / 2 : ℝ)) := by
      rw [← sq_abs t, ← Real.rpow_natCast |t| 2, ← Real.rpow_add (abs_pos.mpr ht_ne)]
      congr 1; norm_num
    have hsplit_t : |t| ^ (-(1 / 2 : ℝ)) = |τ| ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) := by
      rw [show |t| = s * |τ| by rw [abs_mul, abs_of_pos hs0],
        Real.mul_rpow hs0.le (abs_nonneg τ), mul_comm]
    rw [mul_assoc, norm_mul, norm_mul]
    calc ‖mellinK0 c ((t : ℂ) * Complex.I) (fctXi1 L1)‖ *
          (‖stripG ((t : ℂ) * Complex.I) + (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I)‖ *
          ‖fctDcompAt K4 c α ((t : ℂ) * Complex.I) * ctHG ε ((t : ℂ) * Complex.I)‖)
        ≤ 1 * (((1 + |CL1| * Cpk) * t ^ 2) * (2 ^ 10 * MD * |t| ^ (-(5 / 2 : ℝ)))) := by
          refine mul_le_mul hm_le (mul_le_mul ((norm_add_le _ _).trans (by linarith)) hdhg_bd
            (norm_nonneg _) (by positivity)) (by positivity) zero_le_one
      _ = M_A * (t ^ 2 * |t| ^ (-(5 / 2 : ℝ))) := by simp only [M_A]; ring
      _ = M_A * (|τ| ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) := by rw [hpow_simp, hsplit_t]
  have hint_s : IntervalIntegrable (fun s : ℝ => M_A * (|τ| ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)))) volume 0 1 :=
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ))).const_mul
      (M_A * |τ| ^ (-(1 / 2 : ℝ)))).congr_ae (Filter.Eventually.of_forall fun s => by ring)
  have hint_KA : IntervalIntegrable (fun s : ℝ => fctWarpKA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I))) volume 0 1 := by
    have hcont : ContinuousOn (fun s : ℝ => fctWarpKA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I))) (Ioc 0 1) := by
      have hsub : ContinuousOn (fctWarpKA K4 ε c L1 α) {z : ℂ | 0 ≤ z.re ∧ z.re < 1 ∧ z ≠ 0} :=
        fctWarpKA_continuousOn hcpos (by
          obtain ⟨v, hv, hs, -, -, hD_eq⟩ := hvdata ε c hε (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _) |>.trans hc)
          exact (stripCompD_cont hv hs).congr fun z _ => by
            change fctDcomp K4 (fctWarpAlpha h) ε c z = _
            exact hD_eq z)
      refine hsub.comp ((Complex.ofRealCLM.continuous.mul continuous_const).continuousOn) fun s hs => ?_
      have hs0 : 0 < s := hs.1
      refine ⟨by simp, by simp, ?_⟩
      simp [hs0.ne', hτ]
    have hcont' : ContinuousOn (fun s : ℝ => fctWarpKA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I))) (uIoc 0 1) := by
      simpa [uIoc_of_le zero_le_one] using hcont
    exact IntervalIntegrable.mono_fun hint_s (hcont'.aestronglyMeasurable measurableSet_uIoc)
      (ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => by
        have hs_mem : s ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc_of_le zero_le_one] using hs
        have hs0 : 0 ≤ s := hs_mem.1.le
        calc ‖fctWarpKA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I))‖
            ≤ M_A * (|τ| ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) := hKA_bd s hs
          _ ≤ ‖M_A * (|τ| ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)))‖ := le_abs_self _)
  have hint_norm : ‖∫ s in (0 : ℝ)..1, fctWarpKA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I))‖ ≤
      C * |τ| ^ (-(1 / 2 : ℝ)) := by
    have hbd := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (ae_of_all _ fun s hs => hKA_bd s (by rwa [uIoc_of_le zero_le_one])) hint_s
    have hval : ∫ s in (0 : ℝ)..1, s ^ (-(1 / 2 : ℝ)) = 2 := by
      rw [integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -(1 / 2 : ℝ)))]
      norm_num
    have hcomp : ∫ s in (0 : ℝ)..1, M_A * (|τ| ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) =
        (2 * M_A) * |τ| ^ (-(1 / 2 : ℝ)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hval]; ring
    exact hbd.trans_eq hcomp
  rw [hK_eq, norm_mul, norm_mul, hexp_norm, mul_one, hpsi_eq, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos, show ‖(τ : ℂ) * Complex.I‖ = |τ| by simp]
  calc c * (|τ| * ‖∫ s in (0 : ℝ)..1, fctWarpKA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I))‖)
      ≤ c * (|τ| * (C * |τ| ^ (-(1 / 2 : ℝ)))) := by gcongr
    _ = C * c * (|τ| * |τ| ^ (-(1 / 2 : ℝ))) := by ring
    _ = C * c * |τ| ^ (1 / 2 : ℝ) := by
        congr 1
        rw [show |τ| * |τ| ^ (-(1 / 2 : ℝ)) = |τ| ^ (1 : ℝ) * |τ| ^ (-(1 / 2 : ℝ)) by simp,
          ← Real.rpow_add (abs_pos.mpr hτ)]
        congr 1; norm_num

lemma fctPsi_imag_large_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      ∀ τ : ℝ, τ ≠ 0 →
        ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ *
          ((c : ℂ) * fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I))‖ ≤
          C * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|)) := by
  obtain ⟨MD, c0D, hMD0, hc0D, hDHG⟩ := dcomp_ctHG_EJ hK4 h
  obtain ⟨c0P, MP, _, hPhiC⟩ := fctPhiC_left_edge_bound hK4 h
  refine ⟨max MP 0 * MD, max c0D (max c0P 1), by positivity, le_max_of_le_right (le_max_right _ _),
    fun ε c ξ hε hc hξ τ hτ => ?_⟩
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  have hEJ := hDHG ε c hε ((le_max_left _ _).trans hc)
  have hPC : ‖fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I)‖ ≤ max MP 0 :=
    (hPhiC ε c hε (((le_max_left c0P 1).trans (le_max_right c0D _)).trans hc) τ).trans (le_max_left MP 0)
  have hc1 : 1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hcpos : 0 < c := by linarith
  have hden_ne : fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (fctDcompAt_ne_zero _) (ctHG_ne_zero_of_closed_band ε (by simp) (by simp) (by simp [hτ]))
  have hpsi_eq : (c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I) *
        (fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) := by
    unfold fctPhiC
    rw [div_mul_cancel₀ _ hden_ne]
  have hm_le : ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ ≤ 1 :=
    (norm_mellinK0_imag_le hcpos hξ τ).2.trans
      (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg τ]) (by norm_num))
  have hb0 := hEJ.b0 τ hτ
  unfold ejW at hb0
  rw [hpsi_eq, norm_mul, norm_mul]
  calc ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ *
        (‖fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I)‖ *
        ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)‖)
      ≤ 1 * (max MP 0 * (MD * (|τ| ^ (-(5 / 2 : ℝ) - ((0 : ℕ) : ℝ)) * (1 + |τ|) ^ (10 + 0) * Real.exp (-(π * 1 * |τ|))))) :=
        mul_le_mul hm_le (mul_le_mul hPC hb0 (norm_nonneg _) (le_max_right _ _)) (by positivity) zero_le_one
    _ = max MP 0 * MD * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|)) := by
        simp only [Nat.cast_zero, sub_zero, add_zero, mul_one]; ring

/-- info: 'FormalResearch.SignUncertainty.fctRightTail_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctRightTail_bounds

/-- info: 'FormalResearch.SignUncertainty.fctLeftTail_deriv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctLeftTail_deriv_bounds

/-- info: 'FormalResearch.SignUncertainty.fctPsi_imag_small_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPsi_imag_small_bound

/-- info: 'FormalResearch.SignUncertainty.fctPsi_imag_large_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPsi_imag_large_bound

end FormalResearch.SignUncertainty
