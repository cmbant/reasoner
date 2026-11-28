/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerConcreteSetup
public import FormalResearch.SignUncertainty.FctLeftEdgeBound
public import FormalResearch.SignUncertainty.FctWarpAdmiss
public import FormalResearch.SignUncertainty.FctVacuumPointwise

/-!
# Integrability and parametric derivatives of `fctWarpI` (`fct:warp-asymp` (1))

Leaf module proving:
* `integrableOn_fctWarpIntegrand`: for `1 ≤ K4`, `ε = ±1`, large `c`, and arbitrary `(L₁, α)`,
  `τ ↦ fctWarpIntegrand K4 ε c L1 α τ` is integrable on `Ioi 0` (`O(τ^{-1/2})` near `0`,
  `O((1+τ)^{-2})` on `[1, ∞)`).
* `hasDerivAt_fctWarpI_L`, `hasDerivAt_fctWarpI_alpha`: parametric derivatives of `fctWarpI` with
  respect to `L₁` and `α` via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
* `fctWarpIntegrandDerivL_eq_edge`, `fctWarpIntegrandDerivAlpha_eq_edge`: exact imaginary-axis
  factorizations matching `concreteEdgeAmp` and `(1 - L₁ φ_kill / m)`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real ContDiff Interval
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-! ### Exact `α`-linearity and regularity of `vTotal` -/

lemma vTotal_eq_zero_add_smul (K4 c α τ₁ t : ℝ) :
    vTotal StripKernelChoice.star K4 c α τ₁ t =
      vTotal StripKernelChoice.star K4 c 0 τ₁ t + α * vAlpha 1 τ₁ t := by
  unfold vTotal
  have h0 : vAlpha (0 : ℝ) τ₁ t = 0 := by rw [vAlpha_eq_smul]; ring
  rw [h0, add_zero, vAlpha_eq_smul α τ₁ t]

lemma vTotal_data {K4 c : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (α : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) ∧
      HasCompactSupport (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) ∧
      (∀ t, vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) (-t) =
        vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) t) := by
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmain⟩ :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  have h0 := hmain hK4 hc hτ₁_pos hτ₁ hcτ (show |(0 : ℝ)| ≤ τ₁ ^ 2 by simp; positivity)
  have h1 := fctThetaD_vAlpha_eq hK4 hc hτ₁_pos hτ₁ hcτ α 0
  obtain ⟨⟨-, -, -, -, -, hv0_cd⟩, ⟨-, -, -, -, -, hv0_even⟩, -,
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv0_cs⟩, -⟩ := h0
  have hvev1 : ∀ t, vAlpha 1 τ₁ (-t) = vAlpha 1 τ₁ t := by
    intro t
    have h1' := hmain hK4 hc hτ₁_pos hτ₁ hcτ (show |τ₁ ^ 2| ≤ τ₁ ^ 2 by rw [abs_of_nonneg (sq_nonneg _)])
    obtain ⟨-, ⟨-, -, hev_a, -⟩, -⟩ := h1'
    rw [vAlpha_eq_inv_mul (τ₁ ^ 2) τ₁ (-t) (pow_ne_zero 2 hτ₁_pos.ne'),
      vAlpha_eq_inv_mul (τ₁ ^ 2) τ₁ t (pow_ne_zero 2 hτ₁_pos.ne'), hev_a t]
  have heq : vTotal StripKernelChoice.star K4 c α τ₁ =
      fun t => vTotal StripKernelChoice.star K4 c 0 τ₁ t + α * vAlpha 1 τ₁ t :=
    funext (vTotal_eq_zero_add_smul K4 c α τ₁)
  rw [heq]
  refine ⟨hv0_cd.add (contDiff_const.mul h1.2.1), ?_, fun t => by dsimp only; rw [hv0_even t, hvev1 t]⟩
  exact hv0_cs.add (h1.2.2.comp_left (mul_zero _))

lemma vTotal_thetaD_eq_zero_add_smul {K4 c : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (α τ : ℝ) :
    fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) τ =
      fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ)))) τ +
        α * fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ := by
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  have h0d := vTotal_data hK4 hc hτ₁ 0
  have h1 := fctThetaD_vAlpha_eq hK4 hc hτ₁_pos hτ₁ hcτ α τ
  have heq : vTotal StripKernelChoice.star K4 c α τ₁ =
      fun t => vTotal StripKernelChoice.star K4 c 0 τ₁ t + α * vAlpha 1 τ₁ t :=
    funext (vTotal_eq_zero_add_smul K4 c α τ₁)
  rw [heq]
  have hlin := fctThetaD_linear h0d.1 h0d.2.1 h1.2.1 h1.2.2 1 α τ
  simpa only [one_mul, Pi.add_apply] using hlin

lemma fctDcompAt_alpha_decomp {K4 c : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (α τ : ℝ) :
    fctDcompAt K4 c α ((τ : ℂ) * Complex.I) =
      fctDcompAt K4 c 0 ((τ : ℂ) * Complex.I) *
        Complex.exp ((α : ℂ) * ((vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
          Complex.I * ((α : ℂ) * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ))) := by
  unfold fctDcompAt
  rw [stripCompGExt_left, stripCompGExt_left, ← Complex.exp_add]
  congr 1
  rw [vTotal_eq_zero_add_smul, vTotal_thetaD_eq_zero_add_smul hK4 hc hτ₁]
  push_cast
  ring

lemma fctThetaD_vAlpha_one_bounds {K4 c : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) :
    ∃ (B0 Bα : ℕ → ℝ), (∀ r, 0 ≤ B0 r) ∧ (∀ r, 0 ≤ Bα r) ∧
      (∀ r : ℕ, r ≤ 2 → ∀ τ : ℝ,
        ‖((iteratedDeriv r (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ) +
          Complex.I * ((iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))))) τ : ℝ) : ℂ)‖ ≤ B0 r) ∧
      (∀ r : ℕ, r ≤ 2 → ∀ τ : ℝ,
        ‖((iteratedDeriv r (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ) +
          Complex.I * ((iteratedDeriv r (fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ))))) τ : ℝ) : ℂ)‖ ≤ Bα r) := by
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  obtain ⟨_, _, Cv0b, Cv0m, Cva, Cv1b, Cv1m, Cth0b, Cth0m, Ctha, Cth1b, Cth1m, CL0b, CL0m, CLa, CL1b, CL1m,
    Ctail, Cint, -, -, -, -, hmain⟩ := (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  have h0 := hmain hK4 hc hτ₁_pos hτ₁ hcτ (show |(0 : ℝ)| ≤ τ₁ ^ 2 by simp; positivity)
  have hsq := hmain hK4 hc hτ₁_pos hτ₁ hcτ (show |τ₁ ^ 2| ≤ τ₁ ^ 2 by rw [abs_of_nonneg (sq_nonneg _)])
  obtain ⟨⟨-, -, -, -, -, hcd_0⟩, -, -, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcs_0⟩,
    -, -, -, -, -, -, -, hglob0, -⟩ := h0
  obtain ⟨⟨-, -, -, -, -, hcd_sq⟩, -, -, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcs_sq⟩,
    -, -, -, -, -, -, -, hglobsq, -⟩ := hsq
  let B0 : ℕ → ℝ := fun r =>
    (Cv0b r + K4 * Cv0m r + Cv1b r + K4 * Cv1m r + Cva r +
      max (Cth0b r + K4 * Cth0m r + Cth1b r + K4 * Cth1m r + Ctha r)
        (Ctail r * (CL0b + K4 * CL0m + (CL1b + K4 * CL1m) + CLa) * 12 ^ (-(1 + (r : ℤ))))) *
      τ₁ ^ ((2 : ℤ) - (r : ℤ))
  have hB0_nn : ∀ r : ℕ, 0 ≤ B0 r := fun r =>
    (norm_nonneg _).trans (hglob0 r 0 ⟨by simp, by simp⟩)
  have hB0 : ∀ r : ℕ, r ≤ 2 → ∀ τ : ℝ,
      ‖((iteratedDeriv r (vTotal StripKernelChoice.star K4 c 0 τ₁) τ : ℝ) : ℂ) +
        Complex.I * ((iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) τ : ℝ) : ℂ)‖ ≤ B0 r := by
    intro r _ τ
    have hcl : ((τ : ℂ) * Complex.I) ∈ closedStrip := ⟨by simp, by simp⟩
    have hst := hglob0 r ((τ : ℂ) * Complex.I) hcl
    rw [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul,
      stripCompGExt_left, ← iteratedDeriv_fctThetaD hcd_0 hcs_0 r] at hst
    exact hst
  have hBsq : ∀ r : ℕ, ∀ τ : ℝ,
      ‖((iteratedDeriv r (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁) τ : ℝ) : ℂ) +
        Complex.I * ((iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁)) τ : ℝ) : ℂ)‖ ≤ B0 r := by
    intro r τ
    have hcl : ((τ : ℂ) * Complex.I) ∈ closedStrip := ⟨by simp, by simp⟩
    have hst := hglobsq r ((τ : ℂ) * Complex.I) hcl
    rw [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul,
      stripCompGExt_left, ← iteratedDeriv_fctThetaD hcd_sq hcs_sq r] at hst
    exact hst
  let C_inv := (τ₁ ^ 2)⁻¹
  have hCinv_nn : 0 ≤ C_inv := by dsimp only [C_inv]; positivity
  refine ⟨B0, fun r => C_inv * (B0 r + B0 r), hB0_nn, fun r => mul_nonneg hCinv_nn (add_nonneg (hB0_nn r) (hB0_nn r)),
    hB0, fun r hr τ => ?_⟩
  have hv1_eq : vAlpha 1 τ₁ = fun s => C_inv * vAlpha (τ₁ ^ 2) τ₁ s :=
    funext fun s => vAlpha_eq_inv_mul (τ₁ ^ 2) τ₁ s (pow_ne_zero 2 hτ₁_pos.ne')
  have h1 := fun s => (fctThetaD_vAlpha_eq hK4 hc hτ₁_pos hτ₁ hcτ (τ₁ ^ 2) s).1
  have hth_eq : fctThetaD (vAlpha 1 τ₁) = fun s => C_inv * fctThetaD (vAlpha (τ₁ ^ 2) τ₁) s := by
    ext s; rw [h1 s]; dsimp only [C_inv]; field_simp [pow_ne_zero 2 hτ₁_pos.ne']
  have hva_eq : vAlpha (τ₁ ^ 2) τ₁ =
      fun s => vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁ s - vTotal StripKernelChoice.star K4 c 0 τ₁ s := by
    ext s; rw [vTotal_eq_zero_add_smul K4 c (τ₁ ^ 2) τ₁ s, vAlpha_eq_smul]; ring
  have hth_diff : fctThetaD (vAlpha (τ₁ ^ 2) τ₁) =
      fun s => fctThetaD (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁) s -
        fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁) s := by
    ext s; rw [vTotal_thetaD_eq_zero_add_smul hK4 hc hτ₁ (τ₁ ^ 2) s, h1 s]; ring
  have hth_cd_sq : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁)) :=
    contDiff_fctThetaD hcd_sq hcs_sq
  have hth_cd_0 : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) :=
    contDiff_fctThetaD hcd_0 hcs_0
  have hd_v : iteratedDeriv r (vAlpha 1 τ₁) τ =
      C_inv * (iteratedDeriv r (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁) τ -
        iteratedDeriv r (vTotal StripKernelChoice.star K4 c 0 τ₁) τ) := by
    rw [hv1_eq, iteratedDeriv_const_mul_field, hva_eq]
    rw [show (fun s => vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁ s -
        vTotal StripKernelChoice.star K4 c 0 τ₁ s) =
        vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁ - vTotal StripKernelChoice.star K4 c 0 τ₁ from rfl]
    rw [iteratedDeriv_sub (hcd_sq.contDiffAt.of_le (by simp)) (hcd_0.contDiffAt.of_le (by simp))]
  have hd_th : iteratedDeriv r (fctThetaD (vAlpha 1 τ₁)) τ =
      C_inv * (iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁)) τ -
        iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) τ) := by
    rw [hth_eq, iteratedDeriv_const_mul_field, hth_diff]
    rw [show (fun s => fctThetaD (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁) s -
        fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁) s) =
        fctThetaD (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁) -
        fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁) from rfl]
    rw [iteratedDeriv_sub (hth_cd_sq.contDiffAt.of_le (by simp)) (hth_cd_0.contDiffAt.of_le (by simp))]
  rw [hd_v, hd_th]
  have hmul : ((C_inv * (iteratedDeriv r (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁) τ -
        iteratedDeriv r (vTotal StripKernelChoice.star K4 c 0 τ₁) τ) : ℝ) : ℂ) +
      Complex.I * ((C_inv * (iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁)) τ -
        iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) τ) : ℝ) : ℂ) =
      (C_inv : ℂ) * (((iteratedDeriv r (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁) τ : ℝ) : ℂ) +
        Complex.I * ((iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c (τ₁ ^ 2) τ₁)) τ : ℝ) : ℂ) -
        (((iteratedDeriv r (vTotal StripKernelChoice.star K4 c 0 τ₁) τ : ℝ) : ℂ) +
          Complex.I * ((iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) τ : ℝ) : ℂ))) := by
    push_cast; ring
  rw [hmul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hCinv_nn]
  exact mul_le_mul_of_nonneg_left
    ((norm_sub_le _ _).trans (add_le_add (hBsq r τ) (hB0 r hr τ))) hCinv_nn

lemma fctDcompAt_uniform_bound {K4 c : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    {α_max : ℝ} (hαm : 0 ≤ α_max) :
    ∃ PD Bα0 : ℝ, 0 ≤ PD ∧ 0 ≤ Bα0 ∧
      (∀ α : ℝ, |α| ≤ α_max → ∀ τ : ℝ, ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I)‖ ≤ PD) ∧
      (∀ τ : ℝ, ‖((vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
        Complex.I * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ)‖ ≤ Bα0) := by
  obtain ⟨B0, Bα, _, hBα_nn, hB0, hBα⟩ := fctThetaD_vAlpha_one_bounds hK4 hc hτ₁
  refine ⟨Real.exp (B0 0 + α_max * Bα 0), Bα 0, by positivity, hBα_nn 0, ?_, ?_⟩
  · intro α hα τ
    unfold fctDcompAt
    rw [stripCompGExt_left, vTotal_eq_zero_add_smul, vTotal_thetaD_eq_zero_add_smul hK4 hc hτ₁, Complex.norm_exp]
    have hre : (((vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))) τ +
        α * vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
        Complex.I * ((fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ)))) τ +
          α * fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ)).re =
        vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))) τ + α * vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ := by
      simp
    rw [hre]
    have hb0_re : |vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))) τ| ≤ B0 0 := by
      have h := hB0 0 (by norm_num) τ
      simp only [iteratedDeriv_zero] at h
      have hre0 : (((vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
          Complex.I * ((fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ)).re =
          vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))) τ := by simp
      calc |vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))) τ|
          = |(((vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
              Complex.I * ((fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ)).re| := by rw [hre0]
        _ ≤ _ := (Complex.abs_re_le_norm _).trans h
    have hba_re : |vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ| ≤ Bα 0 := by
      have h := hBα 0 (by norm_num) τ
      simp only [iteratedDeriv_zero] at h
      have hre1 : (((vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
          Complex.I * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ)).re =
          vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ := by simp
      calc |vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ|
          = |(((vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
              Complex.I * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ)).re| := by rw [hre1]
        _ ≤ _ := (Complex.abs_re_le_norm _).trans h
    apply Real.exp_le_exp.mpr
    calc vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))) τ + α * vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ
        ≤ |vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))) τ| +
            |α| * |vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ| :=
          add_le_add (le_abs_self _) (by rw [← abs_mul]; exact le_abs_self _)
      _ ≤ B0 0 + α_max * Bα 0 :=
          add_le_add hb0_re (mul_le_mul hα hba_re (abs_nonneg _) hαm)
  · intro τ
    simpa only [iteratedDeriv_zero] using hBα 0 (by norm_num) τ

/-! ### Continuity and dominating function for `fctWarpIntegrand` and its partial derivatives -/

noncomputable def fctWarpIntegrandDerivL (K4 ε c L1 α τ : ℝ) : ℂ :=
  Complex.I * ((c * τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 α τ +
    mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
      FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) *
      fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)

noncomputable def fctWarpIntegrandDerivAlpha (K4 ε c L1 α τ : ℝ) : ℂ :=
  fctWarpIntegrand K4 ε c L1 α τ *
    (((vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
      Complex.I * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ))

lemma fctWarpIntegrand_continuousOn {K4 ε c L1 α : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) :
    ContinuousOn (fctWarpIntegrand K4 ε c L1 α) (Ioi 0) := by
  have hξ : 0 < fctXi1 L1 := by unfold fctXi1; positivity
  have hm : Continuous fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) :=
    continuous_mellinK0_imag hc hξ
  have ha : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hc _
  have hpk : Continuous fun τ : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) :=
    (FctSym.contDiff_phiKill_imag ha).continuous
  have hvd := vTotal_data hK4 hc hτ₁ α
  have hD : Continuous fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I) := by
    have heq : (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) =
        fun τ => Complex.exp (((vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
          Complex.I * ((fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ)) := by
      ext τ; unfold fctDcompAt; rw [stripCompGExt_left]
    rw [heq]
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp hvd.1.continuous).add
        (continuous_const.mul (Complex.continuous_ofReal.comp (contDiff_fctThetaD hvd.1 hvd.2.1).continuous)))
  have hg_cont : ContinuousOn (fun τ : ℝ => stripG ((τ : ℂ) * Complex.I)) (Ioi 0) := by
    have heq : EqOn (fun τ : ℝ => stripG ((τ : ℂ) * Complex.I))
        (fun τ : ℝ => (-(uctM τ : ℝ) : ℂ)) (Ioi 0) := by
      intro τ hτ
      have hτ0 : (τ : ℝ) > 0 := hτ
      dsimp only
      rw [stripG_imag_eq_neg_m hτ0.ne', abs_of_pos hτ0]
      rfl
    exact ((Complex.continuous_ofReal.comp_continuousOn CtMDeriv.contDiffOn_hankelEdgeM.continuousOn).neg).congr heq
  have hHG : ContinuousOn (fun τ : ℝ => ctHG ε ((τ : ℂ) * Complex.I)) (Ioi 0) := by
    refine (ctHG_continuousOn ε).comp (by fun_prop) fun τ hτ => ?_
    have hτ0 : (0 : ℝ) < τ := hτ
    refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
    · intro h0; have := congrArg Complex.im h0; simp at this; linarith
    · intro h1; have := congrArg Complex.re h1; simp at this
  unfold fctWarpIntegrand fctWarpA
  exact hm.continuousOn.mul (((hg_cont.add (continuousOn_const.mul hpk.continuousOn)).mul hD.continuousOn).mul hHG)

lemma fctWarpIntegrandDerivL_continuousOn {K4 ε c L1 α : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) :
    ContinuousOn (fctWarpIntegrandDerivL K4 ε c L1 α) (Ioi 0) := by
  have hξ : 0 < fctXi1 L1 := by unfold fctXi1; positivity
  have hm : Continuous fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) :=
    continuous_mellinK0_imag hc hξ
  have ha : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hc _
  have hpk : Continuous fun τ : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) :=
    (FctSym.contDiff_phiKill_imag ha).continuous
  have hvd := vTotal_data hK4 hc hτ₁ α
  have hD : Continuous fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I) := by
    have heq : (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) =
        fun τ => Complex.exp (((vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
          Complex.I * ((fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ)) := by
      ext τ; unfold fctDcompAt; rw [stripCompGExt_left]
    rw [heq]
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp hvd.1.continuous).add
        (continuous_const.mul (Complex.continuous_ofReal.comp (contDiff_fctThetaD hvd.1 hvd.2.1).continuous)))
  have hHG : ContinuousOn (fun τ : ℝ => ctHG ε ((τ : ℂ) * Complex.I)) (Ioi 0) := by
    refine (ctHG_continuousOn ε).comp (by fun_prop) fun τ hτ => ?_
    have hτ0 : (0 : ℝ) < τ := hτ
    refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
    · intro h0; have := congrArg Complex.im h0; simp at this; linarith
    · intro h1; have := congrArg Complex.re h1; simp at this
  have h1 : ContinuousOn (fun τ : ℝ => Complex.I * ((c * τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 α τ) (Ioi 0) :=
    ((continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))).continuousOn).mul
      (fctWarpIntegrand_continuousOn hK4 hc hτ₁)
  have h2 : ContinuousOn (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
      FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) *
      fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) (Ioi 0) :=
    ((hm.continuousOn.mul hpk.continuousOn).mul hD.continuousOn).mul hHG
  exact h1.add h2

lemma fctWarpIntegrandDerivAlpha_continuousOn {K4 ε c L1 α : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) :
    ContinuousOn (fctWarpIntegrandDerivAlpha K4 ε c L1 α) (Ioi 0) := by
  have hτ₁_pos : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc _
  have hcτ : (c ^ (-(1 / 4 : ℝ))) ^ 4 * c = 1 := by
    have : (c ^ (-(1 / 4 : ℝ))) ^ 4 = c⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  have hva := fctThetaD_vAlpha_eq hK4 hc hτ₁_pos hτ₁ hcτ 0 0
  have hcd_v : Continuous fun τ : ℝ => ((vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hva.2.1.continuous
  have hcd_th : Continuous fun τ : ℝ => Complex.I * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (contDiff_fctThetaD hva.2.1 hva.2.2).continuous)
  exact (fctWarpIntegrand_continuousOn hK4 hc hτ₁).mul (hcd_v.continuousOn.add hcd_th.continuousOn)

lemma fctWarpIntegrand_dom {K4 ε c : ℝ} (hK4 : 1 ≤ K4) (_hε : ε = 1 ∨ ε = -1) (hc1 : 1 ≤ c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    {L_max α_max : ℝ} (hLm : 0 ≤ L_max) (hαm : 0 ≤ α_max) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧ (∀ τ, 0 ≤ g τ) ∧
      ∀ {L1 α : ℝ}, |L1| ≤ L_max → |α| ≤ α_max → ∀ τ ∈ Ioi (0 : ℝ),
        ‖fctWarpIntegrand K4 ε c L1 α τ‖ ≤ g τ ∧
        ‖fctWarpIntegrandDerivL K4 ε c L1 α τ‖ ≤ g τ ∧
        ‖fctWarpIntegrandDerivAlpha K4 ε c L1 α τ‖ ≤ g τ := by
  have hc0 : 0 < c := by linarith
  have ha_pos : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  obtain ⟨PD, Bα0, hPD_nn, hBα_nn, hD_bd, hA1_bd⟩ := fctDcompAt_uniform_bound hK4 hc0 hτ₁ hαm
  obtain ⟨Cpk, hCpk_nn, hCpk⟩ := FctSym.phiKill_tsymbol
  obtain ⟨Cn, _, hCn_nn, _, hHG_near⟩ := ctHG_imag_near_bounds ε
  obtain ⟨Khg, hKhg_nn, hHG_far⟩ := ctHG_far ε
  obtain ⟨M10, hM10_nn, hM10⟩ := poly_exp_le_n 10
  set C_pk := 2 * Cpk 0
  have hCpk0 : 0 ≤ C_pk := by have := hCpk_nn 0; positivity
  have hpk_le : ∀ {τ : ℝ}, 0 < τ → ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ ≤
      C_pk * min 1 ((τ / c ^ (-(1 / 12 : ℝ))) ^ 8) := fun {τ} hτ => by
    have hre := (hCpk (c ^ (-(1 / 12 : ℝ))) τ ha_pos hτ Complex.reCLM (fun z => Complex.abs_re_le_norm z) 0).1
    have him := (hCpk (c ^ (-(1 / 12 : ℝ))) τ ha_pos hτ Complex.imCLM (fun z => Complex.abs_im_le_norm z) 0).1
    simp only [pow_zero, one_mul, iteratedDeriv_zero, Complex.reCLM_apply, Complex.imCLM_apply] at hre him
    have htri : ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ ≤
        |(FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)).re| +
          |(FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    calc ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖
        ≤ Cpk 0 * min 1 ((τ / c ^ (-(1 / 12 : ℝ))) ^ 8) +
            Cpk 0 * min 1 ((τ / c ^ (-(1 / 12 : ℝ))) ^ 8) := htri.trans (add_le_add hre him)
      _ = C_pk * min 1 ((τ / c ^ (-(1 / 12 : ℝ))) ^ 8) := by dsimp only [C_pk]; ring
  let a8inv : ℝ := ((c ^ (-(1 / 12 : ℝ))) ^ 8)⁻¹
  have ha8inv_nn : 0 ≤ a8inv := by positivity
  let A_near : ℝ := Real.exp (1 / 6) * (π ^ 2 / 12 + L_max * (C_pk * a8inv) +
      C_pk * a8inv) * PD * Cn
  have hAnear_nn : 0 ≤ A_near := by positivity
  let C_near : ℝ := (1 + c) * A_near * (1 + Bα0)
  have hCnear_nn : 0 ≤ C_near := by positivity
  let A_far : ℝ := Real.exp (1 / 6) * (2 + L_max * C_pk + C_pk) * PD * Khg * M10
  have hAfar_nn : 0 ≤ A_far := by positivity
  let C_far : ℝ := (1 + c) * A_far * (1 + Bα0)
  have hCfar_nn : 0 ≤ C_far := by positivity
  let C_dom : ℝ := max C_near C_far
  have hCdom_nn : 0 ≤ C_dom := le_max_of_le_left hCnear_nn
  let g : ℝ → ℝ := fun τ =>
    if 0 < τ then C_dom * (if τ ≤ 1 then τ ^ (-(1 / 2 : ℝ)) else (1 + τ) ^ (-2 : ℝ)) else 0
  have hg_nn : ∀ τ, 0 ≤ g τ := fun τ => by
    dsimp only [g]
    split_ifs with h1 h2
    · exact mul_nonneg hCdom_nn (Real.rpow_nonneg h1.le _)
    · exact mul_nonneg hCdom_nn (by positivity)
    · exact le_rfl
  have hg_int_Ioc : IntegrableOn g (Ioc 0 1) := by
    have hrpow : IntegrableOn (fun τ : ℝ => C_dom * τ ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
      ((intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ)) (by norm_num)).1).const_mul C_dom
    refine hrpow.congr_fun (fun τ hτ => ?_) measurableSet_Ioc
    dsimp only [g]
    have h1 : 0 < τ := hτ.1
    have h2 : τ ≤ 1 := hτ.2
    simp only [h1, h2, ↓reduceIte]
  have hg_int_Ioi1 : IntegrableOn g (Ioi 1) := by
    have hrpow : IntegrableOn (fun τ : ℝ => C_dom * τ ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)).const_mul C_dom
    have hcont : ContinuousOn g (Ioi 1) := by
      have h_eq : EqOn g (fun τ : ℝ => C_dom * (1 + τ) ^ (-2 : ℝ)) (Ioi 1) := fun τ (hτ : 1 < τ) => by
        have h1 : 0 < τ := by linarith only [hτ]
        have h2 : ¬ τ ≤ 1 := not_le.mpr hτ
        dsimp only [g]; simp only [h1, h2, ↓reduceIte]
      refine (ContinuousOn.const_mul ?_ C_dom).congr h_eq
      exact (continuousOn_const.add continuousOn_id).rpow_const fun τ (hτ : 1 < τ) =>
        Or.inl (show (1 : ℝ) + τ ≠ 0 by positivity)
    refine hrpow.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun τ (hτ : 1 < τ) => ?_)
    have hτ_pos : (0 : ℝ) < τ := by linarith only [hτ]
    have h2 : ¬ τ ≤ 1 := not_le.mpr hτ
    rw [Real.norm_of_nonneg (hg_nn τ)]
    dsimp only [g]; simp only [hτ_pos, h2, ↓reduceIte]
    refine mul_le_mul_of_nonneg_left ?_ hCdom_nn
    exact Real.rpow_le_rpow_of_nonpos hτ_pos (by linarith only [hτ_pos]) (by norm_num)
  have hg_int : IntegrableOn g (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact hg_int_Ioc.union hg_int_Ioi1
  refine ⟨g, hg_int, hg_nn, fun {L1 α} hL1 hα τ hτ => ?_⟩
  have hτ_pos : (0 : ℝ) < τ := hτ
  have hK0_bd : ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖ ≤ Real.exp (1 / 6) :=
    (mellinK0_imag_bounds hc1 L1 τ).2
  have hD_τ : ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I)‖ ≤ PD := hD_bd α hα τ
  have hA1_τ := hA1_bd τ
  rcases le_or_gt τ 1 with hle1 | hgt1
  · have hg_eq : g τ = C_dom * τ ^ (-(1 / 2 : ℝ)) := by
      dsimp only [g]; simp only [hτ_pos, hle1, ↓reduceIte]
    have hHG_τ : ‖ctHG ε ((τ : ℂ) * Complex.I)‖ ≤ Cn * τ ^ (-(5 / 2 : ℝ)) :=
      (hHG_near τ hτ_pos (hle1.trans (by norm_num))).1
    have hpk_τ : ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ ≤
        C_pk * a8inv * τ ^ 2 := by
      have hm := (hpk_le hτ_pos).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hCpk0)
      have hτ8 : τ ^ 8 ≤ τ ^ 2 := pow_le_pow_of_le_one hτ_pos.le hle1 (by norm_num)
      calc ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖
          ≤ C_pk * ((τ / c ^ (-(1 / 12 : ℝ))) ^ 8) := hm
        _ = C_pk * a8inv * τ ^ 8 := by dsimp only [a8inv]; rw [div_pow]; ring
        _ ≤ C_pk * a8inv * τ ^ 2 := mul_le_mul_of_nonneg_left hτ8 (mul_nonneg hCpk0 ha8inv_nn)
    have hsg_τ : ‖stripG ((τ : ℂ) * Complex.I)‖ ≤ π ^ 2 / 12 * τ ^ 2 := by
      rw [stripG_imag_eq_neg_m hτ_pos.ne', abs_of_pos hτ_pos, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      have hm_pos : 0 < hankelEdgeM τ := hankelEdgeM_pos hτ_pos
      rw [abs_of_pos hm_pos]
      exact hankelEdgeM_le_sq hτ_pos.le
    have hsum_τ : ‖stripG ((τ : ℂ) * Complex.I) +
        (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ ≤
        (π ^ 2 / 12 + L_max * (C_pk * a8inv)) * τ ^ 2 := by
      have h1 := norm_add_le (stripG ((τ : ℂ) * Complex.I))
        ((L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
      calc ‖stripG ((τ : ℂ) * Complex.I) +
            (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖
          ≤ π ^ 2 / 12 * τ ^ 2 + L_max * (C_pk * a8inv * τ ^ 2) :=
            h1.trans (add_le_add hsg_τ (mul_le_mul hL1 hpk_τ (norm_nonneg _) hLm))
        _ = _ := by ring
    have hpow25 : τ ^ 2 * τ ^ (-(5 / 2 : ℝ)) = τ ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast τ 2, ← Real.rpow_add hτ_pos]; norm_num
    have hI_bd : ‖fctWarpIntegrand K4 ε c L1 α τ‖ ≤ A_near * τ ^ (-(1 / 2 : ℝ)) := by
      unfold fctWarpIntegrand fctWarpA
      simp only [norm_mul]
      have hmid : ‖stripG ((τ : ℂ) * Complex.I) +
            (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ *
          ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I)‖ * ‖ctHG ε ((τ : ℂ) * Complex.I)‖ ≤
          ((π ^ 2 / 12 + L_max * (C_pk * a8inv)) * τ ^ 2) * PD * (Cn * τ ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul (mul_le_mul hsum_τ hD_τ (norm_nonneg _) (by positivity)) hHG_τ (norm_nonneg _) (by positivity)
      calc ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖ *
            (‖stripG ((τ : ℂ) * Complex.I) +
                (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ *
              ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I)‖ * ‖ctHG ε ((τ : ℂ) * Complex.I)‖)
          ≤ Real.exp (1 / 6) *
              (((π ^ 2 / 12 + L_max * (C_pk * a8inv)) * τ ^ 2) * PD * (Cn * τ ^ (-(5 / 2 : ℝ)))) :=
            mul_le_mul hK0_bd hmid (by positivity) (Real.exp_pos _).le
        _ ≤ Real.exp (1 / 6) * (π ^ 2 / 12 + L_max * (C_pk * a8inv) + C_pk * a8inv) *
              PD * Cn * (τ ^ 2 * τ ^ (-(5 / 2 : ℝ))) := by
              have hτ25 : 0 ≤ τ ^ 2 * τ ^ (-(5 / 2 : ℝ)) := by positivity
              have hpk_nn : 0 ≤ C_pk * a8inv := mul_nonneg hCpk0 ha8inv_nn
              have hcst : 0 ≤ Real.exp (1 / 6) * PD * Cn * (τ ^ 2 * τ ^ (-(5 / 2 : ℝ))) := by positivity
              nlinarith only [hpk_nn, hcst]
        _ = A_near * τ ^ (-(1 / 2 : ℝ)) := by rw [hpow25]
    have hpk_term_bd : ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
        FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) *
        fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)‖ ≤
        A_near * τ ^ (-(1 / 2 : ℝ)) := by
      simp only [norm_mul]
      have hmid1 : ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖ *
            ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ ≤
          Real.exp (1 / 6) * (C_pk * a8inv * τ ^ 2) :=
        mul_le_mul hK0_bd hpk_τ (norm_nonneg _) (Real.exp_pos _).le
      have hmid2 : ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖ *
            ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ *
            ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I)‖ * ‖ctHG ε ((τ : ℂ) * Complex.I)‖ ≤
          Real.exp (1 / 6) * (C_pk * a8inv * τ ^ 2) * PD * (Cn * τ ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul (mul_le_mul hmid1 hD_τ (norm_nonneg _) (by positivity)) hHG_τ (norm_nonneg _) (by positivity)
      calc ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖ *
            ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ *
            ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I)‖ * ‖ctHG ε ((τ : ℂ) * Complex.I)‖
          ≤ Real.exp (1 / 6) * (C_pk * a8inv * τ ^ 2) * PD * (Cn * τ ^ (-(5 / 2 : ℝ))) := hmid2
        _ ≤ A_near * (τ ^ 2 * τ ^ (-(5 / 2 : ℝ))) := by
              have hτ25 : 0 ≤ τ ^ 2 * τ ^ (-(5 / 2 : ℝ)) := by positivity
              have hbase_nn : 0 ≤ π ^ 2 / 12 + L_max * (C_pk * a8inv) := by positivity
              dsimp only [A_near]
              nlinarith only [mul_nonneg (mul_nonneg (Real.exp_pos (1 / 6)).le (mul_nonneg hPD_nn hCn_nn)) hτ25, hbase_nn]
        _ = A_near * τ ^ (-(1 / 2 : ℝ)) := by rw [hpow25]
    have hI_g : A_near * τ ^ (-(1 / 2 : ℝ)) ≤ g τ := by
      rw [hg_eq]
      have hAC : A_near ≤ C_dom := by
        refine le_trans ?_ (le_max_left _ _)
        dsimp only [C_near]
        nlinarith only [mul_nonneg hAnear_nn hBα_nn, hc0, hAnear_nn]
      exact mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg hτ_pos.le _)
    refine ⟨hI_bd.trans hI_g, ?_, ?_⟩
    · have hci : ‖Complex.I * ((c * τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 α τ‖ ≤
          c * (A_near * τ ^ (-(1 / 2 : ℝ))) := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        calc c * τ * ‖fctWarpIntegrand K4 ε c L1 α τ‖
            ≤ c * 1 * (A_near * τ ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hle1 hc0.le) hI_bd (norm_nonneg _) (by positivity)
          _ = c * (A_near * τ ^ (-(1 / 2 : ℝ))) := by ring
      refine (norm_add_le _ _).trans ((add_le_add hci hpk_term_bd).trans ?_)
      rw [hg_eq]
      have hAC : (1 + c) * A_near ≤ C_dom := by
        refine le_trans ?_ (le_max_left _ _)
        dsimp only [C_near]
        nlinarith only [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 1 + c) hAnear_nn) hBα_nn]
      calc c * (A_near * τ ^ (-(1 / 2 : ℝ))) + A_near * τ ^ (-(1 / 2 : ℝ))
          = (1 + c) * A_near * τ ^ (-(1 / 2 : ℝ)) := by ring
        _ ≤ C_dom * τ ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg hτ_pos.le _)
    · unfold fctWarpIntegrandDerivAlpha
      rw [norm_mul]
      calc ‖fctWarpIntegrand K4 ε c L1 α τ‖ * _
          ≤ (A_near * τ ^ (-(1 / 2 : ℝ))) * Bα0 := mul_le_mul hI_bd hA1_τ (norm_nonneg _) (by positivity)
        _ ≤ C_near * τ ^ (-(1 / 2 : ℝ)) := by
            have hτ12 : 0 ≤ τ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ_pos.le _
            calc (A_near * τ ^ (-(1 / 2 : ℝ))) * Bα0
                ≤ (1 + c) * (A_near * τ ^ (-(1 / 2 : ℝ))) * (1 + Bα0) := by
                  have h1c : A_near * τ ^ (-(1 / 2 : ℝ)) ≤ (1 + c) * (A_near * τ ^ (-(1 / 2 : ℝ))) :=
                    le_mul_of_one_le_left (mul_nonneg hAnear_nn hτ12) (by linarith only [hc0])
                  exact mul_le_mul h1c (by linarith only [hBα_nn]) hBα_nn (by positivity)
              _ = C_near * τ ^ (-(1 / 2 : ℝ)) := by dsimp only [C_near]; ring
        _ ≤ g τ := by rw [hg_eq]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hτ_pos.le _)
  · have hg_eq : g τ = C_dom * (1 + τ) ^ (-2 : ℝ) := by
      have h2 : ¬ τ ≤ 1 := not_le.mpr hgt1
      dsimp only [g]; simp only [hτ_pos, h2, ↓reduceIte]
    have h1τ : (1 : ℝ) ≤ 1 + τ := by linarith only [hτ_pos]
    have hτ_im : (1 / 2 : ℝ) ≤ |((τ : ℂ) * Complex.I).im| := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, abs_of_pos hτ_pos]
      linarith only [hgt1]
    have hcl : ((τ : ℂ) * Complex.I) ∈ closedStrip := ⟨by simp, by simp⟩
    have hHG_τ : ‖ctHG ε ((τ : ℂ) * Complex.I)‖ ≤ Khg * (1 + τ) ^ 6 * Real.exp (-(π * τ)) := by
      simpa [abs_of_pos hτ_pos, mul_assoc] using hHG_far ((τ : ℂ) * Complex.I) hcl hτ_im
    have hpk_τ : ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ ≤ C_pk :=
      (hpk_le hτ_pos).trans (mul_le_of_le_one_right hCpk0 (min_le_left _ _))
    have hsg_τ : ‖stripG ((τ : ℂ) * Complex.I)‖ ≤ 2 * (1 + τ) := by
      rw [stripG_imag_eq_neg_m hτ_pos.ne', abs_of_pos hτ_pos, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (hankelEdgeM_pos hτ_pos)]
      have hl : hankelEdgeM τ ≤ π * τ / 2 := FctSym.uctM_le_linear hτ_pos
      nlinarith only [hl, Real.pi_lt_four, hτ_pos]
    have hsum_τ : ‖stripG ((τ : ℂ) * Complex.I) +
        (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ ≤
        (2 + L_max * C_pk) * (1 + τ) := by
      have h1 := norm_add_le (stripG ((τ : ℂ) * Complex.I))
        ((L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
      calc ‖stripG ((τ : ℂ) * Complex.I) +
            (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖
          ≤ 2 * (1 + τ) + L_max * C_pk := h1.trans (add_le_add hsg_τ (mul_le_mul hL1 hpk_τ (norm_nonneg _) hLm))
        _ ≤ 2 * (1 + τ) + (L_max * C_pk) * (1 + τ) := by
            have hLC : L_max * C_pk ≤ (L_max * C_pk) * (1 + τ) :=
              le_mul_of_one_le_right (mul_nonneg hLm hCpk0) h1τ
            linarith only [hLC]
        _ = (2 + L_max * C_pk) * (1 + τ) := by ring
    have hexp10 : ∀ (k : ℕ), k ≤ 8 →
        (1 + τ) ^ k * Real.exp (-(π * τ)) ≤ M10 * (1 + τ) ^ (-2 : ℝ) := by
      intro k hk
      have h1 : (1 + τ) ^ (k + 2) ≤ (1 + τ) ^ 10 := pow_le_pow_right₀ h1τ (by omega)
      have h2 : (1 + τ) ^ (k + 2) * Real.exp (-(π * τ)) ≤ M10 :=
        (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le).trans (hM10 τ hτ_pos.le)
      have hpos : 0 < (1 + τ) ^ 2 := by positivity
      have hr : (1 + τ) ^ (-2 : ℝ) = ((1 + τ) ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith only [hτ_pos]), Real.rpow_natCast]
      rw [hr, ← div_eq_mul_inv, le_div_iff₀ hpos]
      calc (1 + τ) ^ k * Real.exp (-(π * τ)) * (1 + τ) ^ 2
          = (1 + τ) ^ (k + 2) * Real.exp (-(π * τ)) := by ring
        _ ≤ M10 := h2
    have hI_bd : ‖fctWarpIntegrand K4 ε c L1 α τ‖ ≤ A_far * (1 + τ) ^ (-2 : ℝ) := by
      unfold fctWarpIntegrand fctWarpA
      simp only [norm_mul]
      have hmid : ‖stripG ((τ : ℂ) * Complex.I) +
            (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ *
          ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I)‖ * ‖ctHG ε ((τ : ℂ) * Complex.I)‖ ≤
          ((2 + L_max * C_pk) * (1 + τ)) * PD * (Khg * (1 + τ) ^ 6 * Real.exp (-(π * τ))) :=
        mul_le_mul (mul_le_mul hsum_τ hD_τ (norm_nonneg _) (by positivity)) hHG_τ (norm_nonneg _) (by positivity)
      calc ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖ *
            (‖stripG ((τ : ℂ) * Complex.I) +
                (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ *
              ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I)‖ * ‖ctHG ε ((τ : ℂ) * Complex.I)‖)
          ≤ Real.exp (1 / 6) *
              (((2 + L_max * C_pk) * (1 + τ)) * PD * (Khg * (1 + τ) ^ 6 * Real.exp (-(π * τ)))) :=
            mul_le_mul hK0_bd hmid (by positivity) (Real.exp_pos _).le
        _ = Real.exp (1 / 6) * (2 + L_max * C_pk) * PD * Khg * ((1 + τ) ^ 7 * Real.exp (-(π * τ))) := by ring
        _ ≤ Real.exp (1 / 6) * (2 + L_max * C_pk + C_pk) * PD * Khg * (M10 * (1 + τ) ^ (-2 : ℝ)) := by
              have hpe := hexp10 7 (by norm_num)
              have hbase : Real.exp (1 / 6) * (2 + L_max * C_pk) * PD * Khg ≤
                  Real.exp (1 / 6) * (2 + L_max * C_pk + C_pk) * PD * Khg := by
                have h1p : 0 ≤ Real.exp (1 / 6) := (Real.exp_pos _).le
                nlinarith only [mul_nonneg (mul_nonneg h1p hPD_nn) hKhg_nn, hCpk0]
              exact mul_le_mul hbase hpe (by positivity) (by positivity)
        _ = A_far * (1 + τ) ^ (-2 : ℝ) := by dsimp only [A_far]; ring
    have hI_g : A_far * (1 + τ) ^ (-2 : ℝ) ≤ g τ := by
      rw [hg_eq]
      have hAC : A_far ≤ C_dom := by
        refine le_trans ?_ (le_max_right _ _)
        dsimp only [C_far]
        nlinarith only [mul_nonneg hAfar_nn hBα_nn, hc0, hAfar_nn]
      exact mul_le_mul_of_nonneg_right hAC (by positivity)
    refine ⟨hI_bd.trans hI_g, ?_, ?_⟩
    · have hci : ‖Complex.I * ((c * τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 α τ‖ ≤
          c * A_far * (1 + τ) ^ (-2 : ℝ) := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        unfold fctWarpIntegrand fctWarpA
        simp only [norm_mul]
        have hmid : ‖stripG ((τ : ℂ) * Complex.I) +
              (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ *
            ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I)‖ * ‖ctHG ε ((τ : ℂ) * Complex.I)‖ ≤
            ((2 + L_max * C_pk) * (1 + τ)) * PD * (Khg * (1 + τ) ^ 6 * Real.exp (-(π * τ))) :=
          mul_le_mul (mul_le_mul hsum_τ hD_τ (norm_nonneg _) (by positivity)) hHG_τ (norm_nonneg _) (by positivity)
        have hKmid := mul_le_mul hK0_bd hmid (by positivity) (Real.exp_pos _).le
        have hct : c * τ ≤ c * (1 + τ) := mul_le_mul_of_nonneg_left (by linarith only [hτ_pos]) hc0.le
        calc c * τ * (‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖ *
              (‖stripG ((τ : ℂ) * Complex.I) +
                  (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ *
                ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I)‖ * ‖ctHG ε ((τ : ℂ) * Complex.I)‖))
            ≤ c * (1 + τ) * (Real.exp (1 / 6) * (((2 + L_max * C_pk) * (1 + τ)) * PD *
                (Khg * (1 + τ) ^ 6 * Real.exp (-(π * τ))))) :=
              mul_le_mul hct hKmid (by positivity) (by positivity)
          _ = c * (Real.exp (1 / 6) * (2 + L_max * C_pk) * PD * Khg) *
                ((1 + τ) ^ 8 * Real.exp (-(π * τ))) := by ring
          _ ≤ c * (Real.exp (1 / 6) * (2 + L_max * C_pk + C_pk) * PD * Khg) *
                (M10 * (1 + τ) ^ (-2 : ℝ)) := by
              have hpe := hexp10 8 (by norm_num)
              have hbase : c * (Real.exp (1 / 6) * (2 + L_max * C_pk) * PD * Khg) ≤
                  c * (Real.exp (1 / 6) * (2 + L_max * C_pk + C_pk) * PD * Khg) := by
                have h1p : 0 ≤ Real.exp (1 / 6) := (Real.exp_pos _).le
                nlinarith only [mul_nonneg hc0.le (mul_nonneg (mul_nonneg h1p hPD_nn) hKhg_nn), hCpk0]
              exact mul_le_mul hbase hpe (by positivity) (by positivity)
          _ = c * A_far * (1 + τ) ^ (-2 : ℝ) := by dsimp only [A_far]; ring
      have hpk_term_bd : ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
          FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) *
          fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)‖ ≤
          A_far * (1 + τ) ^ (-2 : ℝ) := by
        simp only [norm_mul]
        have hm1 := mul_le_mul hK0_bd hpk_τ (norm_nonneg _) (Real.exp_pos _).le
        have hm2 := mul_le_mul (mul_le_mul hm1 hD_τ (norm_nonneg _) (by positivity)) hHG_τ (norm_nonneg _) (by positivity)
        calc ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖ *
              ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)‖ *
              ‖fctDcompAt K4 c α ((τ : ℂ) * Complex.I)‖ * ‖ctHG ε ((τ : ℂ) * Complex.I)‖
            ≤ Real.exp (1 / 6) * C_pk * PD * (Khg * (1 + τ) ^ 6 * Real.exp (-(π * τ))) := hm2
          _ = Real.exp (1 / 6) * C_pk * PD * Khg * ((1 + τ) ^ 6 * Real.exp (-(π * τ))) := by ring
          _ ≤ Real.exp (1 / 6) * (2 + L_max * C_pk + C_pk) * PD * Khg * (M10 * (1 + τ) ^ (-2 : ℝ)) := by
              have hpe := hexp10 6 (by norm_num)
              have hbase : Real.exp (1 / 6) * C_pk * PD * Khg ≤
                  Real.exp (1 / 6) * (2 + L_max * C_pk + C_pk) * PD * Khg := by
                have h1p : 0 ≤ Real.exp (1 / 6) := (Real.exp_pos _).le
                have h2L : 0 ≤ 2 + L_max * C_pk := by positivity
                nlinarith only [mul_nonneg (mul_nonneg h1p hPD_nn) hKhg_nn, h2L, hCpk0]
              exact mul_le_mul hbase hpe (by positivity) (by positivity)
          _ = A_far * (1 + τ) ^ (-2 : ℝ) := by dsimp only [A_far]; ring
      refine (norm_add_le _ _).trans ((add_le_add hci hpk_term_bd).trans ?_)
      rw [hg_eq]
      have hAC : (1 + c) * A_far ≤ C_dom := by
        refine le_trans ?_ (le_max_right _ _)
        dsimp only [C_far]
        nlinarith only [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 1 + c) hAfar_nn) hBα_nn]
      calc c * A_far * (1 + τ) ^ (-2 : ℝ) + A_far * (1 + τ) ^ (-2 : ℝ)
          = (1 + c) * A_far * (1 + τ) ^ (-2 : ℝ) := by ring
        _ ≤ C_dom * (1 + τ) ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right hAC (by positivity)
    · unfold fctWarpIntegrandDerivAlpha
      rw [norm_mul]
      calc ‖fctWarpIntegrand K4 ε c L1 α τ‖ * _
          ≤ (A_far * (1 + τ) ^ (-2 : ℝ)) * Bα0 := mul_le_mul hI_bd hA1_τ (norm_nonneg _) (by positivity)
        _ ≤ C_far * (1 + τ) ^ (-2 : ℝ) := by
            have hτ2 : 0 ≤ (1 + τ) ^ (-2 : ℝ) := by positivity
            calc (A_far * (1 + τ) ^ (-2 : ℝ)) * Bα0
                ≤ (1 + c) * (A_far * (1 + τ) ^ (-2 : ℝ)) * (1 + Bα0) := by
                  have h1c : A_far * (1 + τ) ^ (-2 : ℝ) ≤ (1 + c) * (A_far * (1 + τ) ^ (-2 : ℝ)) :=
                    le_mul_of_one_le_left (mul_nonneg hAfar_nn hτ2) (by linarith only [hc0])
                  exact mul_le_mul h1c (by linarith only [hBα_nn]) hBα_nn (by positivity)
              _ = C_far * (1 + τ) ^ (-2 : ℝ) := by dsimp only [C_far]; ring
        _ ≤ g τ := by rw [hg_eq]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ### Integrability and parametric differentiation of `fctWarpI` -/

theorem integrableOn_fctWarpIntegrand {K4 ε c : ℝ} (hK4 : 1 ≤ K4) (hε : ε = 1 ∨ ε = -1) (hc1 : 1 ≤ c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (L1 α : ℝ) :
    IntegrableOn (fctWarpIntegrand K4 ε c L1 α) (Ioi (0 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨g, hg_int, _, hg_bd⟩ := fctWarpIntegrand_dom hK4 hε hc1 hτ₁ (abs_nonneg L1) (abs_nonneg α)
  exact hg_int.mono' ((fctWarpIntegrand_continuousOn hK4 hc0 hτ₁).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => (hg_bd le_rfl le_rfl τ hτ).1)

theorem integrableOn_fctWarpIntegrandDerivL {K4 ε c : ℝ} (hK4 : 1 ≤ K4) (hε : ε = 1 ∨ ε = -1) (hc1 : 1 ≤ c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (L1 α : ℝ) :
    IntegrableOn (fctWarpIntegrandDerivL K4 ε c L1 α) (Ioi (0 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨g, hg_int, _, hg_bd⟩ := fctWarpIntegrand_dom hK4 hε hc1 hτ₁ (abs_nonneg L1) (abs_nonneg α)
  exact hg_int.mono' ((fctWarpIntegrandDerivL_continuousOn hK4 hc0 hτ₁).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => (hg_bd le_rfl le_rfl τ hτ).2.1)

theorem integrableOn_fctWarpIntegrandDerivAlpha {K4 ε c : ℝ} (hK4 : 1 ≤ K4) (hε : ε = 1 ∨ ε = -1) (hc1 : 1 ≤ c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (L1 α : ℝ) :
    IntegrableOn (fctWarpIntegrandDerivAlpha K4 ε c L1 α) (Ioi (0 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨g, hg_int, _, hg_bd⟩ := fctWarpIntegrand_dom hK4 hε hc1 hτ₁ (abs_nonneg L1) (abs_nonneg α)
  exact hg_int.mono' ((fctWarpIntegrandDerivAlpha_continuousOn hK4 hc0 hτ₁).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => (hg_bd le_rfl le_rfl τ hτ).2.2)

theorem hasDerivAt_fctWarpI_L {K4 ε c : ℝ} (hK4 : 1 ≤ K4) (hε : ε = 1 ∨ ε = -1) (hc1 : 1 ≤ c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (L1 α : ℝ) :
    HasDerivAt (fun x : ℝ => fctWarpI K4 ε c x α)
      (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivL K4 ε c L1 α τ) L1 := by
  have hc0 : 0 < c := by linarith
  obtain ⟨g, hg_int, _, hg_bd⟩ :=
    fctWarpIntegrand_dom hK4 hε hc1 hτ₁ (L_max := |L1| + 1) (α_max := |α|) (by positivity) (abs_nonneg α)
  have hd_int : HasDerivAt (fun x : ℝ => ∫ τ in Ioi (0 : ℝ), fctWarpIntegrand K4 ε c x α τ)
      (∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivL K4 ε c L1 α τ) L1 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
      (F := fun x τ => fctWarpIntegrand K4 ε c x α τ)
      (F' := fun x τ => fctWarpIntegrandDerivL K4 ε c x α τ)
      (x₀ := L1) (s := Metric.ball L1 1) (bound := g) (Metric.ball_mem_nhds L1 one_pos)
      ?_ ?_ ?_ ?_ hg_int ?_).2
    · exact Eventually.of_forall fun x =>
        (fctWarpIntegrand_continuousOn hK4 hc0 hτ₁).aestronglyMeasurable measurableSet_Ioi
    · exact integrableOn_fctWarpIntegrand hK4 hε hc1 hτ₁ L1 α
    · exact (fctWarpIntegrandDerivL_continuousOn hK4 hc0 hτ₁).aestronglyMeasurable measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ x hx => ?_
      have hx_bd : |x| ≤ |L1| + 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hx
        linarith [abs_sub_abs_le_abs_sub x L1]
      exact (hg_bd hx_bd le_rfl τ hτ).2.1
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ _ x _ => ?_
      have hξ : ∀ y : ℝ, 0 < fctXi1 y := fun y => by unfold fctXi1; positivity
      have hlog : ∀ y : ℝ, Real.log (π ^ 2 * fctXi1 y) = y := fun y => by
        unfold fctXi1; rw [mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_exp]
      set K_m : ℂ := (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
        Complex.exp (Complex.I * (c : ℂ) * ((-Real.pi ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ))
      have hm_eq : ∀ y : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 y) =
          K_m * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (y : ℂ)) := fun y => by
        rw [FormalResearch.CohnElkies.mellinK0_imag_eq c (fctXi1 y) τ (hξ y), hlog y]
        dsimp only [K_m]
        have hex : Complex.I * (c : ℂ) * ((y * τ - Real.pi ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) =
            Complex.I * (c : ℂ) * ((-Real.pi ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) +
              Complex.I * ((c * τ : ℝ) : ℂ) * (y : ℂ) := by push_cast; ring
        rw [hex, Complex.exp_add]; ring
      have hdm : HasDerivAt (fun y : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 y))
          (Complex.I * ((c * τ : ℝ) : ℂ) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 x)) x := by
        have hfun : (fun y : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 y)) =
            fun y : ℝ => K_m * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (y : ℂ)) :=
          funext hm_eq
        rw [hfun]
        have he1 : HasDerivAt (fun y : ℝ => Complex.I * ((c * τ : ℝ) : ℂ) * (y : ℂ))
            (Complex.I * ((c * τ : ℝ) : ℂ)) x := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (Complex.I * ((c * τ : ℝ) : ℂ))
        have he2 := (he1.cexp).const_mul K_m
        refine he2.congr_deriv ?_
        rw [hm_eq x]; ring
      have hds : HasDerivAt (fun y : ℝ => stripG ((τ : ℂ) * Complex.I) +
          (y : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I))
          (FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)) x := by
        have hy := ((hasDerivAt_id x).ofReal_comp).mul_const
          (FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I))
        exact ((hasDerivAt_const x (stripG ((τ : ℂ) * Complex.I))).add hy).congr_deriv (by simp)
      have hd_prod := hdm.mul ((hds.mul_const (fctDcompAt K4 c α ((τ : ℂ) * Complex.I))).mul_const
        (ctHG ε ((τ : ℂ) * Complex.I)))
      refine hd_prod.congr_deriv ?_
      unfold fctWarpIntegrandDerivL fctWarpIntegrand fctWarpA
      ring
  exact hd_int.const_mul Complex.I

theorem hasDerivAt_fctWarpI_alpha {K4 ε c : ℝ} (hK4 : 1 ≤ K4) (hε : ε = 1 ∨ ε = -1) (hc1 : 1 ≤ c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (L1 α : ℝ) :
    HasDerivAt (fun x : ℝ => fctWarpI K4 ε c L1 x)
      (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 α τ) α := by
  have hc0 : 0 < c := by linarith
  obtain ⟨g, hg_int, _, hg_bd⟩ :=
    fctWarpIntegrand_dom hK4 hε hc1 hτ₁ (L_max := |L1|) (α_max := |α| + 1) (abs_nonneg L1) (by positivity)
  have hd_int : HasDerivAt (fun x : ℝ => ∫ τ in Ioi (0 : ℝ), fctWarpIntegrand K4 ε c L1 x τ)
      (∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 α τ) α := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
      (F := fun x τ => fctWarpIntegrand K4 ε c L1 x τ)
      (F' := fun x τ => fctWarpIntegrandDerivAlpha K4 ε c L1 x τ)
      (x₀ := α) (s := Metric.ball α 1) (bound := g) (Metric.ball_mem_nhds α one_pos)
      ?_ ?_ ?_ ?_ hg_int ?_).2
    · exact Eventually.of_forall fun x =>
        (fctWarpIntegrand_continuousOn hK4 hc0 hτ₁).aestronglyMeasurable measurableSet_Ioi
    · exact integrableOn_fctWarpIntegrand hK4 hε hc1 hτ₁ L1 α
    · exact (fctWarpIntegrandDerivAlpha_continuousOn hK4 hc0 hτ₁).aestronglyMeasurable measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ x hx => ?_
      have hx_bd : |x| ≤ |α| + 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hx
        linarith [abs_sub_abs_le_abs_sub x α]
      exact (hg_bd le_rfl hx_bd τ hτ).2.2
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ _ x _ => ?_
      set wτ : ℂ := ((vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
        Complex.I * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ)
      have hD_eq : ∀ y : ℝ, fctDcompAt K4 c y ((τ : ℂ) * Complex.I) =
          fctDcompAt K4 c 0 ((τ : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * wτ) := fun y => by
        rw [fctDcompAt_alpha_decomp hK4 hc0 hτ₁ y τ]
        congr 2; dsimp only [wτ]; ring
      have hd_D : HasDerivAt (fun y : ℝ => fctDcompAt K4 c y ((τ : ℂ) * Complex.I))
          (fctDcompAt K4 c x ((τ : ℂ) * Complex.I) * wτ) x := by
        have hfun : (fun y : ℝ => fctDcompAt K4 c y ((τ : ℂ) * Complex.I)) =
            fun y : ℝ => fctDcompAt K4 c 0 ((τ : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * wτ) :=
          funext hD_eq
        rw [hfun]
        have he1 : HasDerivAt (fun y : ℝ => (y : ℂ) * wτ) wτ x := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const wτ
        refine ((he1.cexp).const_mul _).congr_deriv ?_
        rw [hD_eq x]; ring
      have hd_A := ((hasDerivAt_const x (stripG ((τ : ℂ) * Complex.I) +
        (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I))).mul hd_D).mul_const
          (ctHG ε ((τ : ℂ) * Complex.I))
      have hd_all := hd_A.const_mul (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))
      refine hd_all.congr_deriv ?_
      unfold fctWarpIntegrandDerivAlpha fctWarpIntegrand fctWarpA
      dsimp only [wτ]; ring
  exact hd_int.const_mul Complex.I

/-! ### Edge factorizations for the partial-derivative integrands -/

noncomputable def concreteEdgeAmpBase (K4 c α τ : ℝ) : ℂ :=
  let v := vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))
  Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ)) + (v τ : ℂ)) *
    ((uctM τ * ‖uctHstar (Complex.I * (τ : ℂ))‖ / Real.sqrt (6 / π ^ 2 * uctMderiv τ) : ℝ) : ℂ)

lemma concreteEdgeAmp_eq_base_mul (K4 c L1 α τ : ℝ) :
    concreteEdgeAmp K4 c L1 α τ =
      concreteEdgeAmpBase K4 c α τ *
        ((1 : ℂ) - (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) / (uctM τ : ℂ)) :=
  rfl

lemma fctWarpIntegrandDerivL_eq_edge {K4 ε c L1 α τ : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : 0 < c) (hτ : 0 < τ) :
    fctWarpIntegrandDerivL K4 ε c L1 α τ =
      Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (L1, α) - π / 4 : ℝ) : ℂ)) *
        concreteEdgeAmpBase K4 c α τ *
        (Complex.I * ((c * τ : ℝ) : ℂ) *
            ((1 : ℂ) - (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) / (uctM τ : ℂ)) -
          FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) / (uctM τ : ℂ)) := by
  have h1 := fctWarpIntegrand_eq_edge (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α) (τ := τ) hε hc hτ
  have hdiff := fctWarpIntegrand_eq_edge (K4 := K4) (ε := ε) (c := c) (L1 := L1 - 1) (α := α) (τ := τ) hε hc hτ
  --Wait: let's relate the `φ_kill` term directly via `L1 = 0` vs `L1 = 1` difference!
  have h0 := fctWarpIntegrand_eq_edge (K4 := K4) (ε := ε) (c := c) (L1 := 0) (α := α) (τ := τ) hε hc hτ
  have hξ0 : 0 < fctXi1 0 := by unfold fctXi1; positivity
  have hξL : 0 < fctXi1 L1 := by unfold fctXi1; positivity
  have hrat_K : mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) =
      Complex.exp (Complex.I * ((c * L1 * τ : ℝ) : ℂ)) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 0) := by
    rw [FormalResearch.CohnElkies.mellinK0_imag_eq c (fctXi1 L1) τ hξL,
      FormalResearch.CohnElkies.mellinK0_imag_eq c (fctXi1 0) τ hξ0]
    have hlogL : Real.log (π ^ 2 * fctXi1 L1) = L1 := by
      unfold fctXi1; rw [mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_exp]
    have hlog0 : Real.log (π ^ 2 * fctXi1 0) = 0 := by
      unfold fctXi1; rw [Real.exp_zero, mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_one]
    rw [hlogL, hlog0]
    have hex : Complex.I * (c : ℂ) * ((L1 * τ - π ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) =
        Complex.I * ((c * L1 * τ : ℝ) : ℂ) +
          Complex.I * (c : ℂ) * ((0 * τ - π ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) := by
      push_cast; ring
    rw [hex, Complex.exp_add]; ring
  have hrat_Phi : concretePhiTilde K4 ε c τ (L1, α) =
      concretePhiTilde K4 ε c τ (0, α) + L1 * τ := by
    simp only [concretePhiTilde, concretePhiLambda, concretePhiPh]; ring
  have h0_sub : fctWarpIntegrand K4 ε c 0 α τ - fctWarpIntegrand K4 ε c L1 α τ =
      mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 0) * (stripG ((τ : ℂ) * Complex.I) *
        fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) -
      fctWarpIntegrand K4 ε c L1 α τ := by
    unfold fctWarpIntegrand fctWarpA; simp
  -- Direct factor comparison via `L1 = 0` vs `L1 = 1` at `ξ₁(0)`
  have hdiff1 := fctWarpIntegrand_eq_edge (K4 := K4) (ε := ε) (c := c) (L1 := 1) (α := α) (τ := τ) hε hc hτ
  have h_pk_0 : mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 0) *
      FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) *
      fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (0, α) - π / 4 : ℝ) : ℂ)) *
        concreteEdgeAmpBase K4 c α τ *
        (-(FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) / (uctM τ : ℂ))) := by
    have hrat1 : mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 1) =
        Complex.exp (Complex.I * ((c * 1 * τ : ℝ) : ℂ)) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 0) := by
      rw [FormalResearch.CohnElkies.mellinK0_imag_eq c (fctXi1 1) τ (by unfold fctXi1; positivity),
        FormalResearch.CohnElkies.mellinK0_imag_eq c (fctXi1 0) τ hξ0]
      have hlog1 : Real.log (π ^ 2 * fctXi1 1) = 1 := by
        unfold fctXi1; rw [mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_exp]
      have hlog0 : Real.log (π ^ 2 * fctXi1 0) = 0 := by
        unfold fctXi1; rw [Real.exp_zero, mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_one]
      rw [hlog1, hlog0]
      have hex : Complex.I * (c : ℂ) * ((1 * τ - π ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) =
          Complex.I * ((c * 1 * τ : ℝ) : ℂ) +
            Complex.I * (c : ℂ) * ((0 * τ - π ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) := by
        push_cast; ring
      rw [hex, Complex.exp_add]; ring
    have hPhi1 : concretePhiTilde K4 ε c τ (1, α) = concretePhiTilde K4 ε c τ (0, α) + 1 * τ := by
      simp only [concretePhiTilde, concretePhiLambda, concretePhiPh]; ring
    have hexp1 : Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (1, α) - π / 4 : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((c * 1 * τ : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (0, α) - π / 4 : ℝ) : ℂ)) := by
      rw [hPhi1, ← Complex.exp_add]; congr 1; push_cast; ring
    have hne : Complex.exp (Complex.I * ((c * 1 * τ : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hs1 : fctWarpIntegrand K4 ε c 1 α τ =
        Complex.exp (Complex.I * ((c * 1 * τ : ℝ) : ℂ)) *
          (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 0) *
            (stripG ((τ : ℂ) * Complex.I) + (1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I)) *
            fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) := by
      unfold fctWarpIntegrand fctWarpA; rw [hrat1]; simp only [Complex.ofReal_one]; ring
    have hs0 : fctWarpIntegrand K4 ε c 0 α τ =
        mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 0) * stripG ((τ : ℂ) * Complex.I) *
          fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I) := by
      unfold fctWarpIntegrand fctWarpA; simp [mul_assoc]
    have hdiff_id : mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 0) *
        FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) *
        fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I) =
        Complex.exp (-(Complex.I * ((c * 1 * τ : ℝ) : ℂ))) * fctWarpIntegrand K4 ε c 1 α τ -
          fctWarpIntegrand K4 ε c 0 α τ := by
      rw [hs1, hs0, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
      ring
    rw [hdiff_id, hdiff1, h0, hexp1]
    have hcancel : Complex.exp (-(Complex.I * ((c * 1 * τ : ℝ) : ℂ))) *
        (Complex.exp (Complex.I * ((c * 1 * τ : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (0, α) - π / 4 : ℝ) : ℂ))) =
        Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (0, α) - π / 4 : ℝ) : ℂ)) := by
      rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
    calc Complex.exp (-(Complex.I * ((c * 1 * τ : ℝ) : ℂ))) *
          (Complex.exp (Complex.I * ((c * 1 * τ : ℝ) : ℂ)) *
              Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (0, α) - π / 4 : ℝ) : ℂ)) *
            concreteEdgeAmp K4 c 1 α τ) -
          Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (0, α) - π / 4 : ℝ) : ℂ)) *
            concreteEdgeAmp K4 c 0 α τ
        = Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (0, α) - π / 4 : ℝ) : ℂ)) *
            concreteEdgeAmp K4 c 1 α τ -
          Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (0, α) - π / 4 : ℝ) : ℂ)) *
            concreteEdgeAmp K4 c 0 α τ := by
              rw [← mul_assoc, hcancel]
      _ = Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (0, α) - π / 4 : ℝ) : ℂ)) *
            (concreteEdgeAmp K4 c 1 α τ - concreteEdgeAmp K4 c 0 α τ) := by ring
      _ = _ := by
            rw [concreteEdgeAmp_eq_base_mul, concreteEdgeAmp_eq_base_mul]
            simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, zero_div, sub_zero, mul_one]
            ring
  have hexpL : Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (L1, α) - π / 4 : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((c * L1 * τ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (0, α) - π / 4 : ℝ) : ℂ)) := by
    rw [hrat_Phi, ← Complex.exp_add]; congr 1; push_cast; ring
  have h_pk_L : mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
      FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) *
      fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (L1, α) - π / 4 : ℝ) : ℂ)) *
        concreteEdgeAmpBase K4 c α τ *
        (-(FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) / (uctM τ : ℂ))) := by
    rw [hrat_K]
    calc Complex.exp (Complex.I * ((c * L1 * τ : ℝ) : ℂ)) * mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 0) *
          FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) *
          fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)
        = Complex.exp (Complex.I * ((c * L1 * τ : ℝ) : ℂ)) *
            (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 0) *
              FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) *
              fctDcompAt K4 c α ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) := by ring
      _ = _ := by rw [h_pk_0, hexpL]; ring
  unfold fctWarpIntegrandDerivL
  rw [h1, h_pk_L, concreteEdgeAmp_eq_base_mul]
  ring

lemma fctWarpIntegrandDerivAlpha_eq_edge {K4 ε c L1 α τ : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : 0 < c) (hτ : 0 < τ) :
    fctWarpIntegrandDerivAlpha K4 ε c L1 α τ =
      Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (L1, α) - π / 4 : ℝ) : ℂ)) *
        concreteEdgeAmp K4 c L1 α τ *
        (((vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
          Complex.I * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ)) := by
  unfold fctWarpIntegrandDerivAlpha
  rw [fctWarpIntegrand_eq_edge hε hc hτ]

/-- info: 'FormalResearch.SignUncertainty.integrableOn_fctWarpIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrableOn_fctWarpIntegrand

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_fctWarpI_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_fctWarpI_L

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_fctWarpI_alpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_fctWarpI_alpha

end FormalResearch.SignUncertainty
