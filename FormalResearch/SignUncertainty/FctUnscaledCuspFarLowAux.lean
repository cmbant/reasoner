/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspFarIbp
public import FormalResearch.SignUncertainty.FctUnscaledCuspFarPhase
public import FormalResearch.SignUncertainty.FctUnscaledCuspMidFar

/-!
# `fct:unscaled-cusp`, regime `u ≥ 1`: algebra and elementary integrals for the low piece (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`, third estimate.

For the piece `[(cu)^{-1}, t₀/2]` of the half-line integral, two integrations by parts with amplitude majorants
`B_j = K x^{1/2-j} e^{-ηx/2}`, `P₂ = cκ₃/x`, `P₃ = cC₂` and `P₁ = c g` (`g` the lower bound of the gap `u - 𝔪`):
`ibpF_far_eq` is the closed form `K e c^{-2}[(g^{-2}+3κ₃g^{-3}+3κ₃²g^{-4}) x^{-3/2} + C₂ g^{-3} x^{1/2}]` of the majorant
expression, `ibpEnd_mono` the monotonicity of the endpoint term in `P₁`, and the elementary integrals
`∫_α^β x^{-3/2} ≤ 2/√α`, `∫_α^β x^{1/2} e^{-ηx/4} ≤ Γ'_η`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

lemma rpow_sq_neg_three_half {y : ℝ} (hy : 0 < y) : (y ^ 2) ^ (-(3 : ℝ) / 2) = (y ^ 3)⁻¹ := by
  rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg (by positivity),
    ← Real.rpow_natCast y 2, ← Real.rpow_mul hy.le,
    show ((2 : ℕ) : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The closed form of the majorant expression for `P₁ = c g`, `P₂ = cκ₃/x`, `P₃ = cC₂`. -/
lemma ibpF_far_eq {K E c g k3 C2 x : ℝ} (hx : 0 < x) (hc : 0 < c) (hg : 0 < g) :
    ibpF (K * (x ^ ((1 : ℝ) / 2) * E)) (K * (x ^ (-(1 : ℝ) / 2) * E)) (K * (x ^ (-(3 : ℝ) / 2) * E)) (c * g)
        (c * k3 / x) (c * C2) =
      K * E * (c ^ 2)⁻¹ * (((g ^ 2)⁻¹ + 3 * k3 * (g ^ 3)⁻¹ + 3 * k3 ^ 2 * (g ^ 4)⁻¹) * x ^ (-(3 : ℝ) / 2) +
        C2 * (g ^ 3)⁻¹ * x ^ ((1 : ℝ) / 2)) := by
  obtain ⟨y, hy, rfl⟩ : ∃ y, 0 < y ∧ x = y ^ 2 := ⟨Real.sqrt x, Real.sqrt_pos.2 hx, (Real.sq_sqrt hx.le).symm⟩
  rw [rpow_sq_half hy, rpow_sq_neg_half hy, rpow_sq_neg_three_half hy]
  unfold ibpF
  field_simp
  ring

/-- Monotonicity of the endpoint term in `P₁`. -/
lemma ibpEnd_mono {b0 b1 p1 p1' p2 : ℝ} (hp1' : 0 < p1') (hp : p1' ≤ p1) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hp2 : 0 ≤ p2) : ibpEnd b0 b1 p1 p2 ≤ ibpEnd b0 b1 p1' p2 := by
  have hp1 : 0 < p1 := lt_of_lt_of_le hp1' hp
  unfold ibpEnd
  have e1 : b0 / p1 ≤ b0 / p1' := div_le_div_of_nonneg_left hb0 hp1' hp
  have e2 : b1 / p1 ≤ b1 / p1' := div_le_div_of_nonneg_left hb1 hp1' hp
  have e3 : b0 * p2 / p1 ^ 2 ≤ b0 * p2 / p1' ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
  have e4 : (b1 / p1 + b0 * p2 / p1 ^ 2) / p1 ≤ (b1 / p1' + b0 * p2 / p1' ^ 2) / p1' := by
    have : (b1 / p1 + b0 * p2 / p1 ^ 2) / p1 ≤ (b1 / p1' + b0 * p2 / p1' ^ 2) / p1 :=
      div_le_div_of_nonneg_right (add_le_add e2 e3) hp1.le
    refine this.trans ?_
    exact div_le_div_of_nonneg_left (by positivity) hp1' hp
  linarith

/-- `∫_α^β x^{-3/2} ≤ 2/√α`. -/
lemma integral_rpow_neg_three_half_le {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∫ x in α..β, x ^ (-(3 : ℝ) / 2) ≤ 2 * (Real.sqrt α)⁻¹ := by
  rw [integral_rpow (Or.inr ⟨by norm_num, by
    rw [uIcc_of_le hαβ]; intro hm; exact absurd hm.1 (not_le.2 hα)⟩)]
  have key : ∀ y : ℝ, 0 < y → y ^ (-(3 : ℝ) / 2 + 1) = (Real.sqrt y)⁻¹ := by
    intro y hy
    rw [show -(3 : ℝ) / 2 + 1 = -(1 / 2) by norm_num, Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow]
  rw [key α hα, key β (hα.trans_le hαβ)]
  have : 0 ≤ (Real.sqrt β)⁻¹ := by positivity
  rw [show -(3 : ℝ) / 2 + 1 = -(1 / 2) by norm_num]
  rw [div_le_iff_of_neg (by norm_num)]
  linarith

/-- The constant `Γ'_η = ∫_0^∞ x^{1/2} e^{-ηx/4}`. -/
noncomputable def cuspGamB (η : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * x)

lemma cuspGamB_integrableOn {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun x : ℝ => x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * x)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (1 : ℝ) / 2) (b := η / 4) (by norm_num)
    one_pos (by positivity)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp

lemma cuspGamB_nonneg (η : ℝ) : 0 ≤ cuspGamB η :=
  setIntegral_nonneg measurableSet_Ioi fun x hx => by
    have : 0 < x := hx
    positivity

/-- `∫_α^β x^{1/2} e^{-ηx/4} ≤ Γ'_η`. -/
lemma integral_sqrt_exp_le {η α β : ℝ} (hη : 0 < η) (hα : 0 < α) (hαβ : α ≤ β) :
    ∫ x in α..β, x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * x) ≤ cuspGamB η := by
  rw [intervalIntegral.integral_of_le hαβ]
  unfold cuspGamB
  refine setIntegral_mono_set (cuspGamB_integrableOn hη) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have : 0 < x := hx
    positivity
  · exact ae_of_all _ (fun x hx => Ioi_subset_Ioi hα.le (Ioc_subset_Ioi_self hx))

/-- `x^{1/2} ≤ 1 + x`. -/
lemma rpow_half_le_one_add {x : ℝ} (hx : 0 < x) : x ^ ((1 : ℝ) / 2) ≤ 1 + x := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
  exact ⟨by positivity, by nlinarith [sq_nonneg (x - 1)]⟩

/-- `x^{-1/2} ≤ 1 + x⁻¹`. -/
lemma rpow_neg_half_le_one_add {x : ℝ} (hx : 0 < x) : x ^ (-(1 : ℝ) / 2) ≤ 1 + x⁻¹ := by
  have e : x ^ (-(1 : ℝ) / 2) = (x⁻¹) ^ ((1 : ℝ) / 2) := by
    rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]; norm_num
  rw [e]
  have := rpow_half_le_one_add (inv_pos.2 hx)
  linarith

end FormalResearch.SignUncertainty.FctUnscaledCusp
