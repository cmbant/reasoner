/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctEVSymbol

/-!
# All-order bounds for the boundary phase `ϑ_{D₀} = fctThetaD (v₀)` (`fct:comp-D` (1), `(fct:th-inner)`, `(fct:th-tail)`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.3 (`fct:comp-D`) (1).

`theta_bounds`: for `θ = fctThetaD (v0 kind K4 τ₁)` (`τ₁ ≤ τ_c`, `τ₁⁴ c = 1`, `|α| ≤ τ₁²`), `θ` is `C^∞` and, with constants independent of `c, α, τ₁`,

* (inner) `|θ^{(r)}(x)| ≤ M_r τ₁² (τ₁^r)⁻¹` for `0 < x ≤ 12τ₁`;
* (tail) `|θ^{(r)}(x)| ≤ T_r τ₁³ (x^{r+1})⁻¹ e^{-πx/2}` for `x ≥ 12τ₁`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
  FormalResearch.SignUncertainty.FctMoment

theorem theta_bounds (kind : StripKernelChoice) (K4 : ℝ) (hK4 : 1 ≤ K4) :
    ∃ (τc : ℝ) (Mi Tt : ℕ → ℝ), 0 < τc ∧ τc ≤ 1 / 20 ∧ (∀ r, 0 ≤ Mi r ∧ 0 ≤ Tt r) ∧
      ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τc → τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
        ContDiff ℝ ∞ (fctThetaD (v0 kind K4 τ₁)) ∧
        (∀ (r : ℕ) (x : ℝ), 0 < x → x ≤ 12 * τ₁ →
          |iteratedDeriv r (fctThetaD (v0 kind K4 τ₁)) x| ≤ Mi r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹)) ∧
        (∀ (r : ℕ) (x : ℝ), 12 * τ₁ ≤ x →
          |iteratedDeriv r (fctThetaD (v0 kind K4 τ₁)) x| ≤
            Tt r * (τ₁ ^ 3 * ((x ^ (r + 1))⁻¹ * Real.exp (-(π * x / 2))))) := by
  obtain ⟨τ₀, hτ₀, hτ₀20, Cv0b, Cv0m, Cva, Cv1b, Cv1m, Cth0b, Cth0m, Ctha, Cth1b, Cth1m,
    CL1_0b, CL1_0m, CL1_a, CL1_1b, CL1_1m, C_tail, C_int, hCv_nn, hCth_nn, hCL1_nn, hCti_nn, hpart1⟩ :=
    fct_comp_D_part1 kind
  have hK40 : 0 ≤ K4 := by linarith
  have hL1nn : 0 ≤ CL1_0b + K4 * CL1_0m := by obtain ⟨h1, h2, _, _, _⟩ := hCL1_nn; positivity
  refine ⟨τ₀, fun r => Cth0b r + K4 * Cth0m r, fun r => C_tail r * (CL1_0b + K4 * CL1_0m), hτ₀, hτ₀20,
    fun r => ⟨by obtain ⟨h1, h2, _, _, _⟩ := hCth_nn r; positivity, mul_nonneg (hCti_nn r).1 hL1nn⟩, ?_⟩
  intro c α τ₁ hc hτ₁ hτ₁_le hc_eq hα_le
  have hτ₁_1 : τ₁ ≤ 1 := by linarith
  obtain ⟨⟨hb0_cd, hm0_cd, _, _, _, _⟩, _, _, ⟨hb0_s, hm0_s, _, _, _, _, _⟩,
    _, _, _, _, hth_in, htail, _, _, _⟩ := hpart1 hK4 hc hτ₁ hτ₁_le hc_eq hα_le
  have hb0_cs := hasCompactSupport_of_support_Ioo hb0_s
  have hm0_cs := hasCompactSupport_of_support_Ioo hm0_s
  have hθb_cd := contDiff_fctThetaD hb0_cd hb0_cs
  have hθm_cd := contDiff_fctThetaD hm0_cd hm0_cs
  have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) (v0 kind K4 τ₁) := hb0_cd.add (contDiff_const.mul hm0_cd)
  have hθ_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (v0 kind K4 τ₁)) := contDiff_fctThetaD hv0_cd (by
    unfold v0
    exact hb0_cs.add hm0_cs.mul_left)
  have hlin : fctThetaD (v0 kind K4 τ₁) = fun s => fctThetaD (v0Base kind τ₁) s + K4 * fctThetaD (v0Marg τ₁) s := by
    ext s; unfold v0
    simpa only [one_mul] using fctThetaD_linear hb0_cd hb0_cs hm0_cd hm0_cs 1 K4 s
  refine ⟨hθ_cd, fun r x hx0 hx12 => ?_, fun r x hx => ?_⟩
  · have h := hth_in r x (by rw [abs_of_pos hx0]; exact hx12)
    rw [hlin, iteratedDeriv_add_cd hθb_cd (contDiff_const.mul hθm_cd), iteratedDeriv_const_mul_field]
    have hq : 0 < (τ₁ ^ r)⁻¹ := inv_pos.mpr (pow_pos hτ₁ r)
    have hτ2 : τ₁ ^ 4 ≤ τ₁ ^ 2 := pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have hmin : ∀ y : ℝ, min (1 : ℝ) y ≤ 1 := fun y => min_le_left _ _
    have d1 : |iteratedDeriv r (fctThetaD (v0Base kind τ₁)) x| ≤ Cth0b r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) := by
      refine h.1.trans ?_
      rw [zpow_sub_nat' hτ₁.ne']
      simp only [zpow_ofNat]
      calc Cth0b r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) * min 1 ((|x| / τ₁) ^ (11 - r)) ≤ Cth0b r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) * 1 := by
            exact mul_le_mul_of_nonneg_left (hmin _) (by have := (hCth_nn r).1; positivity)
        _ = _ := mul_one _
    have d2 : |iteratedDeriv r (fctThetaD (v0Marg τ₁)) x| ≤ Cth0m r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) := by
      refine h.2.1.trans ?_
      rw [zpow_sub_nat' hτ₁.ne']
      simp only [zpow_ofNat]
      calc Cth0m r * (τ₁ ^ 4 * (τ₁ ^ r)⁻¹) * min 1 ((|x| / τ₁) ^ (11 - r)) ≤ Cth0m r * (τ₁ ^ 4 * (τ₁ ^ r)⁻¹) * 1 := by
            exact mul_le_mul_of_nonneg_left (hmin _) (by have := (hCth_nn r).2.1; positivity)
        _ ≤ Cth0m r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) := by
            rw [mul_one]; have := (hCth_nn r).2.1; gcongr
    obtain ⟨hc1, hc2, _, _, _⟩ := hCth_nn r
    calc |iteratedDeriv r (fctThetaD (v0Base kind τ₁)) x + K4 * iteratedDeriv r (fctThetaD (v0Marg τ₁)) x|
        ≤ |iteratedDeriv r (fctThetaD (v0Base kind τ₁)) x| + K4 * |iteratedDeriv r (fctThetaD (v0Marg τ₁)) x| :=
          (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hK40])
      _ ≤ Cth0b r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) + K4 * (Cth0m r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹)) := add_le_add d1 (by gcongr)
      _ = _ := by ring
  · have hx0 : 0 < x := by linarith
    have h := (htail r x (by rw [abs_of_pos hx0]; exact hx)).1
    rw [abs_of_pos hx0, show -(1 + (r : ℤ)) = -((r + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast] at h
    refine h.trans (le_of_eq ?_)
    rw [show -(π / 2) * x = -(π * x / 2) by ring]
    ring

end FormalResearch.SignUncertainty.FctSym
