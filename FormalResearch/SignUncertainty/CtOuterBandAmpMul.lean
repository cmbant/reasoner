module

public import FormalResearch.SignUncertainty.CtOuterBandSqrt

/-!
# Amplitude bounds for a product `f · G` (real weight times a smooth decaying factor)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4 (`ct:A-derivs`).  **Proved.**
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtOsc

/-- Product of a real weight with `|f^{(k)}| ≤ K_F τ^{1/2-k}/(1+τ)` and a complex factor with `|G| ≤ K_G`,
`|G'| ≤ K'/(1+τ)²`, `|G''| ≤ K''/(1+τ)³` is an `AmpBd`. -/
theorem ampBd_mul {KF KG K' K'' : ℝ} {f f1 f2 : ℝ → ℝ} {G G1 G2 : ℝ → ℂ} (hKF : 0 ≤ KF)
    (hKG : 0 ≤ KG) (hK' : 0 ≤ K') (hK'' : 0 ≤ K'')
    (hf : ∀ τ : ℝ, 0 < τ → HasDerivAt f (f1 τ) τ) (hf1 : ∀ τ : ℝ, 0 < τ → HasDerivAt f1 (f2 τ) τ)
    (hf2c : ContinuousOn f2 (Ioi 0))
    (hfb0 : ∀ τ : ℝ, 0 < τ → |f τ| ≤ KF * τ ^ (1 / 2 : ℝ) / (1 + τ))
    (hfb1 : ∀ τ : ℝ, 0 < τ → |f1 τ| ≤ KF * τ ^ (-1 / 2 : ℝ) / (1 + τ))
    (hfb2 : ∀ τ : ℝ, 0 < τ → |f2 τ| ≤ KF * τ ^ (-3 / 2 : ℝ) / (1 + τ))
    (hG : ∀ τ : ℝ, 0 < τ → HasDerivAt G (G1 τ) τ) (hG1 : ∀ τ : ℝ, 0 < τ → HasDerivAt G1 (G2 τ) τ)
    (hG2c : ContinuousOn G2 (Ioi 0))
    (hGb0 : ∀ τ : ℝ, 0 < τ → ‖G τ‖ ≤ KG) (hGb1 : ∀ τ : ℝ, 0 < τ → ‖G1 τ‖ ≤ K' / (1 + τ) ^ 2)
    (hGb2 : ∀ τ : ℝ, 0 < τ → ‖G2 τ‖ ≤ K'' / (1 + τ) ^ 3) :
    AmpBd (KF * (KG + 2 * K' + K'')) (fun τ => (f τ : ℂ) * G τ)
      (fun τ => (f1 τ : ℂ) * G τ + (f τ : ℂ) * G1 τ)
      (fun τ => (f2 τ : ℂ) * G τ + (f1 τ : ℂ) * G1 τ + ((f1 τ : ℂ) * G1 τ + (f τ : ℂ) * G2 τ)) where
  CA0 := by positivity
  d1 τ hτ := (hf τ hτ).ofReal_comp.mul (hG τ hτ)
  d2 τ hτ := (((hf1 τ hτ).ofReal_comp.mul (hG τ hτ)).add ((hf τ hτ).ofReal_comp.mul (hG1 τ hτ))).congr_deriv (by ring)
  c2 := by
    have cf : ContinuousOn f (Ioi 0) := fun τ hτ => (hf τ hτ).continuousAt.continuousWithinAt
    have cf1 : ContinuousOn f1 (Ioi 0) := fun τ hτ => (hf1 τ hτ).continuousAt.continuousWithinAt
    have cG : ContinuousOn G (Ioi 0) := fun τ hτ => (hG τ hτ).continuousAt.continuousWithinAt
    have cG1 : ContinuousOn G1 (Ioi 0) := fun τ hτ => (hG1 τ hτ).continuousAt.continuousWithinAt
    have r0 := Complex.continuous_ofReal.comp_continuousOn cf
    have r1 := Complex.continuous_ofReal.comp_continuousOn cf1
    have r2 := Complex.continuous_ofReal.comp_continuousOn hf2c
    exact ((r2.mul cG).add (r1.mul cG1)).add ((r1.mul cG1).add (r0.mul hG2c))
  b0 τ hτ := by
    have hu := wt_pos hτ
    have e0 : (KF * (KG + 2 * K' + K'')) * τ ^ (1 / 2 : ℝ) / (1 + τ) = (KF * (KG + 2 * K' + K'')) * τ ^ 2 * wt τ := by
      rw [rpow_half_eq hτ]; unfold wt; ring
    rw [e0]
    have h1 := hfb0 τ hτ
    have e1 : KF * τ ^ (1 / 2 : ℝ) / (1 + τ) = KF * τ ^ 2 * wt τ := by
      rw [rpow_half_eq hτ]; unfold wt; ring
    rw [e1] at h1
    have : ‖(f τ : ℂ) * G τ‖ ≤ KF * τ ^ 2 * wt τ * KG := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h1 (hGb0 τ hτ) (norm_nonneg _) (by positivity)
    refine this.trans ?_
    have hw : 0 ≤ KF * τ ^ 2 * wt τ := by positivity
    calc KF * τ ^ 2 * wt τ * KG = (KF * τ ^ 2 * wt τ) * KG := rfl
      _ ≤ (KF * τ ^ 2 * wt τ) * (KG + 2 * K' + K'') := mul_le_mul_of_nonneg_left (by linarith) hw
      _ = _ := by ring
  b1 τ hτ := by
    have hu := wt_pos hτ
    have hc1 : τ / (1 + τ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg τ]
    have e0 : KF * τ ^ (1 / 2 : ℝ) / (1 + τ) = KF * τ ^ 2 * wt τ := by
      rw [rpow_half_eq hτ]; unfold wt; ring
    have e1 : KF * τ ^ (-1 / 2 : ℝ) / (1 + τ) = KF * τ * wt τ := by
      rw [rpow_neg_half_eq hτ]; unfold wt; ring
    have e2 : (KF * (KG + 2 * K' + K'')) * τ ^ (-1 / 2 : ℝ) / (1 + τ) = (KF * (KG + 2 * K' + K'')) * τ * wt τ := by
      rw [rpow_neg_half_eq hτ]; unfold wt; ring
    rw [e2]
    have h0 := hfb0 τ hτ; rw [e0] at h0
    have h1 := hfb1 τ hτ; rw [e1] at h1
    have t1 : ‖(f1 τ : ℂ) * G τ‖ ≤ KF * τ * wt τ * KG := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h1 (hGb0 τ hτ) (norm_nonneg _) (by positivity)
    have t2 : ‖(f τ : ℂ) * G1 τ‖ ≤ KF * τ * wt τ * K' := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := mul_le_mul h0 (hGb1 τ hτ) (norm_nonneg _) (by positivity)
      refine this.trans ?_
      calc KF * τ ^ 2 * wt τ * (K' / (1 + τ) ^ 2) = (KF * τ * wt τ * K') * (τ / (1 + τ) ^ 2) := by
            field_simp
        _ ≤ (KF * τ * wt τ * K') * 1 := mul_le_mul_of_nonneg_left hc1 (by positivity)
        _ = _ := by ring
    have hw : 0 ≤ KF * τ * wt τ := by positivity
    calc ‖(f1 τ : ℂ) * G τ + (f τ : ℂ) * G1 τ‖ ≤ ‖(f1 τ : ℂ) * G τ‖ + ‖(f τ : ℂ) * G1 τ‖ := norm_add_le _ _
      _ ≤ KF * τ * wt τ * KG + KF * τ * wt τ * K' := add_le_add t1 t2
      _ = (KF * τ * wt τ) * (KG + K') := by ring
      _ ≤ (KF * τ * wt τ) * (KG + 2 * K' + K'') := mul_le_mul_of_nonneg_left (by linarith) hw
      _ = _ := by ring
  b2 τ hτ := by
    have hu := wt_pos hτ
    have hc1 : τ / (1 + τ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg τ]
    have hc2 : τ ^ 2 / (1 + τ) ^ 3 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg τ, pow_pos hτ 3]
    have e0 : KF * τ ^ (1 / 2 : ℝ) / (1 + τ) = KF * τ ^ 2 * wt τ := by
      rw [rpow_half_eq hτ]; unfold wt; ring
    have e1 : KF * τ ^ (-1 / 2 : ℝ) / (1 + τ) = KF * τ * wt τ := by
      rw [rpow_neg_half_eq hτ]; unfold wt; ring
    have e2 : KF * τ ^ (-3 / 2 : ℝ) / (1 + τ) = KF * wt τ := by unfold wt; ring
    have e3 : (KF * (KG + 2 * K' + K'')) * τ ^ (-3 / 2 : ℝ) / (1 + τ) = (KF * (KG + 2 * K' + K'')) * wt τ := by
      unfold wt; ring
    rw [e3]
    have h0 := hfb0 τ hτ; rw [e0] at h0
    have h1 := hfb1 τ hτ; rw [e1] at h1
    have h2 := hfb2 τ hτ; rw [e2] at h2
    have s1 : ‖(f2 τ : ℂ) * G τ‖ ≤ KF * wt τ * KG := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h2 (hGb0 τ hτ) (norm_nonneg _) (by positivity)
    have s2 : ‖(f1 τ : ℂ) * G1 τ‖ ≤ KF * wt τ * K' := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := mul_le_mul h1 (hGb1 τ hτ) (norm_nonneg _) (by positivity)
      refine this.trans ?_
      calc KF * τ * wt τ * (K' / (1 + τ) ^ 2) = (KF * wt τ * K') * (τ / (1 + τ) ^ 2) := by field_simp
        _ ≤ (KF * wt τ * K') * 1 := mul_le_mul_of_nonneg_left hc1 (by positivity)
        _ = _ := by ring
    have s3 : ‖(f τ : ℂ) * G2 τ‖ ≤ KF * wt τ * K'' := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := mul_le_mul h0 (hGb2 τ hτ) (norm_nonneg _) (by positivity)
      refine this.trans ?_
      calc KF * τ ^ 2 * wt τ * (K'' / (1 + τ) ^ 3) = (KF * wt τ * K'') * (τ ^ 2 / (1 + τ) ^ 3) := by field_simp
        _ ≤ (KF * wt τ * K'') * 1 := mul_le_mul_of_nonneg_left hc2 (by positivity)
        _ = _ := by ring
    have a1 := norm_add_le ((f2 τ : ℂ) * G τ + (f1 τ : ℂ) * G1 τ) ((f1 τ : ℂ) * G1 τ + (f τ : ℂ) * G2 τ)
    have a2 := norm_add_le ((f2 τ : ℂ) * G τ) ((f1 τ : ℂ) * G1 τ)
    have a3 := norm_add_le ((f1 τ : ℂ) * G1 τ) ((f τ : ℂ) * G2 τ)
    have hw : 0 ≤ KF * wt τ := by positivity
    have : KF * wt τ * KG + KF * wt τ * K' + (KF * wt τ * K' + KF * wt τ * K'') =
        (KF * wt τ) * (KG + 2 * K' + K'') := by ring
    have hfin : (KF * wt τ) * (KG + 2 * K' + K'') = (KF * (KG + 2 * K' + K'')) * wt τ := by ring
    linarith

end FormalResearch.SignUncertainty.CtOsc
