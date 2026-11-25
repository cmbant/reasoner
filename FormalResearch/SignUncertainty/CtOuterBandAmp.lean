module

public import FormalResearch.SignUncertainty.CtOuterBandReg
public import FormalResearch.SignUncertainty.CtOuterBandCut

/-!
# Amplitude bounds and cutoff products

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4, (`ct:A-derivs`):
`|A^{(k)}(τ)| ≤ C_k min(τ^{1/2-k}, τ^{-1/2-k})`, here in the form `C τ^{1/2-k}/(1+τ)`.  **Proved.**

`AmpBd CA A A₁ A₂`; `prodB`: the cutoff product `B = X A` satisfies the same bounds with `K_B = C_A(1+2ρ₁+ρ₂)` when
`|X'| ≤ ρ₁/τ`, `|X''| ≤ ρ₂/τ²`.
-/

@[expose] public section

open Set MeasureTheory
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtOsc

/-- Amplitude bounds `‖A^{(k)}(τ)‖ ≤ C_A τ^{1/2-k}/(1+τ)`, `k = 0,1,2`. -/
structure AmpBd (CA : ℝ) (A A1 A2 : ℝ → ℂ) : Prop where
  CA0 : 0 ≤ CA
  d1 : ∀ τ : ℝ, 0 < τ → HasDerivAt A (A1 τ) τ
  d2 : ∀ τ : ℝ, 0 < τ → HasDerivAt A1 (A2 τ) τ
  c2 : ContinuousOn A2 (Ioi 0)
  b0 : ∀ τ : ℝ, 0 < τ → ‖A τ‖ ≤ CA * τ ^ (1 / 2 : ℝ) / (1 + τ)
  b1 : ∀ τ : ℝ, 0 < τ → ‖A1 τ‖ ≤ CA * τ ^ (-1 / 2 : ℝ) / (1 + τ)
  b2 : ∀ τ : ℝ, 0 < τ → ‖A2 τ‖ ≤ CA * τ ^ (-3 / 2 : ℝ) / (1 + τ)

lemma rpow_half_div {τ : ℝ} (hτ : 0 < τ) : τ ^ (1 / 2 : ℝ) / τ = τ ^ (-1 / 2 : ℝ) := by
  rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub_one hτ.ne']

lemma rpow_neg_half_div {τ : ℝ} (hτ : 0 < τ) : τ ^ (-1 / 2 : ℝ) / τ = τ ^ (-3 / 2 : ℝ) := by
  rw [show (-3 / 2 : ℝ) = -1 / 2 - 1 by norm_num, Real.rpow_sub_one hτ.ne']

/-- The cutoff product `B = X A`. -/
lemma prodB {CA ρ1 ρ2 : ℝ} {A A1 A2 : ℝ → ℂ} (hA : AmpBd CA A A1 A2) {X X1 X2 : ℝ → ℝ}
    (hX : ∀ τ, HasDerivAt X (X1 τ) τ) (hX1 : ∀ τ, HasDerivAt X1 (X2 τ) τ) (hX2 : Continuous X2)
    (hX01 : ∀ τ, 0 ≤ X τ ∧ X τ ≤ 1) (hρ1 : 0 ≤ ρ1) (hρ2 : 0 ≤ ρ2)
    (hb1 : ∀ τ : ℝ, 0 < τ → |X1 τ| ≤ ρ1 / τ) (hb2 : ∀ τ : ℝ, 0 < τ → |X2 τ| ≤ ρ2 / τ ^ 2) :
    (∀ τ : ℝ, 0 < τ → HasDerivAt (fun τ => (X τ : ℂ) * A τ) ((X1 τ : ℂ) * A τ + (X τ : ℂ) * A1 τ) τ) ∧
    (∀ τ : ℝ, 0 < τ → HasDerivAt (fun τ => (X1 τ : ℂ) * A τ + (X τ : ℂ) * A1 τ)
      ((X2 τ : ℂ) * A τ + (X1 τ : ℂ) * A1 τ + ((X1 τ : ℂ) * A1 τ + (X τ : ℂ) * A2 τ)) τ) ∧
    ContinuousOn (fun τ => (X2 τ : ℂ) * A τ + (X1 τ : ℂ) * A1 τ + ((X1 τ : ℂ) * A1 τ + (X τ : ℂ) * A2 τ)) (Ioi 0) ∧
    (∀ τ : ℝ, 0 < τ → ‖(X τ : ℂ) * A τ‖ ≤ CA * (1 + 2 * ρ1 + ρ2) * τ ^ (1 / 2 : ℝ) / (1 + τ)) ∧
    (∀ τ : ℝ, 0 < τ → ‖(X1 τ : ℂ) * A τ + (X τ : ℂ) * A1 τ‖ ≤
      CA * (1 + 2 * ρ1 + ρ2) * τ ^ (-1 / 2 : ℝ) / (1 + τ)) ∧
    (∀ τ : ℝ, 0 < τ → ‖(X2 τ : ℂ) * A τ + (X1 τ : ℂ) * A1 τ + ((X1 τ : ℂ) * A1 τ + (X τ : ℂ) * A2 τ)‖ ≤
      CA * (1 + 2 * ρ1 + ρ2) * τ ^ (-3 / 2 : ℝ) / (1 + τ)) := by
  have hCA := hA.CA0
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_, ?_, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · exact (hX τ).ofReal_comp.mul (hA.d1 τ hτ)
  · exact ((hX1 τ).ofReal_comp.mul (hA.d1 τ hτ)).add ((hX τ).ofReal_comp.mul (hA.d2 τ hτ)) |>.congr_deriv (by ring)
  · have hXc : Continuous X := continuous_iff_continuousAt.2 fun τ => (hX τ).continuousAt
    have hX1c : Continuous X1 := continuous_iff_continuousAt.2 fun τ => (hX1 τ).continuousAt
    have cA : ContinuousOn A (Ioi 0) := fun τ hτ => (hA.d1 τ hτ).continuousAt.continuousWithinAt
    have cA1 : ContinuousOn A1 (Ioi 0) := fun τ hτ => (hA.d2 τ hτ).continuousAt.continuousWithinAt
    have c1 := Complex.continuous_ofReal.comp hXc |>.continuousOn (s := Ioi 0)
    have c2 := Complex.continuous_ofReal.comp hX1c |>.continuousOn (s := Ioi 0)
    have c3 := Complex.continuous_ofReal.comp hX2 |>.continuousOn (s := Ioi 0)
    exact ((c3.mul cA).add (c2.mul cA1)).add ((c2.mul cA1).add (c1.mul hA.c2))
  · have h0 := hA.b0 τ hτ
    have : ‖(X τ : ℂ) * A τ‖ ≤ ‖A τ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hX01 τ).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hX01 τ).2
    refine this.trans (h0.trans ?_)
    have hw : 0 ≤ τ ^ (1 / 2 : ℝ) / (1 + τ) := by positivity
    calc CA * τ ^ (1 / 2 : ℝ) / (1 + τ) = CA * (τ ^ (1 / 2 : ℝ) / (1 + τ)) := by ring
      _ ≤ CA * (1 + 2 * ρ1 + ρ2) * (τ ^ (1 / 2 : ℝ) / (1 + τ)) := by
          apply mul_le_mul_of_nonneg_right _ hw
          nlinarith
      _ = _ := by ring
  · have e1 := rpow_half_div hτ
    have hn : ∀ x : ℝ, ‖(x : ℂ)‖ = |x| := fun x => by rw [Complex.norm_real, Real.norm_eq_abs]
    have a0 := hA.b0 τ hτ
    have a1 := hA.b1 τ hτ
    have t1 : ‖(X1 τ : ℂ) * A τ‖ ≤ ρ1 * CA * τ ^ (-1 / 2 : ℝ) / (1 + τ) := by
      rw [norm_mul, hn]
      calc |X1 τ| * ‖A τ‖ ≤ (ρ1 / τ) * (CA * τ ^ (1 / 2 : ℝ) / (1 + τ)) :=
            mul_le_mul (hb1 τ hτ) a0 (norm_nonneg _) (by positivity)
        _ = ρ1 * CA * (τ ^ (1 / 2 : ℝ) / τ) / (1 + τ) := by field_simp
        _ = _ := by rw [e1]
    have t2 : ‖(X τ : ℂ) * A1 τ‖ ≤ CA * τ ^ (-1 / 2 : ℝ) / (1 + τ) := by
      rw [norm_mul, hn, abs_of_nonneg (hX01 τ).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hX01 τ).2).trans a1
    have hw : 0 ≤ τ ^ (-1 / 2 : ℝ) / (1 + τ) := by positivity
    refine (norm_add_le _ _).trans ?_
    have : ρ1 * CA * τ ^ (-1 / 2 : ℝ) / (1 + τ) + CA * τ ^ (-1 / 2 : ℝ) / (1 + τ) =
        CA * (1 + ρ1) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) := by ring
    have h5 : CA * (1 + ρ1) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) ≤
        CA * (1 + 2 * ρ1 + ρ2) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCA) hw
    calc _ ≤ ρ1 * CA * τ ^ (-1 / 2 : ℝ) / (1 + τ) + CA * τ ^ (-1 / 2 : ℝ) / (1 + τ) := add_le_add t1 t2
      _ ≤ _ := by rw [this]; refine h5.trans (le_of_eq (by ring))
  · have e1 := rpow_half_div hτ
    have e2 := rpow_neg_half_div hτ
    have hn : ∀ x : ℝ, ‖(x : ℂ)‖ = |x| := fun x => by rw [Complex.norm_real, Real.norm_eq_abs]
    have a0 := hA.b0 τ hτ
    have a1 := hA.b1 τ hτ
    have a2 := hA.b2 τ hτ
    have t1 : ‖(X2 τ : ℂ) * A τ‖ ≤ ρ2 * CA * τ ^ (-3 / 2 : ℝ) / (1 + τ) := by
      rw [norm_mul, hn]
      calc |X2 τ| * ‖A τ‖ ≤ (ρ2 / τ ^ 2) * (CA * τ ^ (1 / 2 : ℝ) / (1 + τ)) :=
            mul_le_mul (hb2 τ hτ) a0 (norm_nonneg _) (by positivity)
        _ = ρ2 * CA * ((τ ^ (1 / 2 : ℝ) / τ) / τ) / (1 + τ) := by field_simp
        _ = _ := by rw [e1, e2]
    have t2 : ‖(X1 τ : ℂ) * A1 τ‖ ≤ ρ1 * CA * τ ^ (-3 / 2 : ℝ) / (1 + τ) := by
      rw [norm_mul, hn]
      calc |X1 τ| * ‖A1 τ‖ ≤ (ρ1 / τ) * (CA * τ ^ (-1 / 2 : ℝ) / (1 + τ)) :=
            mul_le_mul (hb1 τ hτ) a1 (norm_nonneg _) (by positivity)
        _ = ρ1 * CA * (τ ^ (-1 / 2 : ℝ) / τ) / (1 + τ) := by field_simp
        _ = _ := by rw [e2]
    have t3 : ‖(X τ : ℂ) * A2 τ‖ ≤ CA * τ ^ (-3 / 2 : ℝ) / (1 + τ) := by
      rw [norm_mul, hn, abs_of_nonneg (hX01 τ).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hX01 τ).2).trans a2
    have hw : 0 ≤ τ ^ (-3 / 2 : ℝ) / (1 + τ) := by positivity
    have h5 : CA * (ρ2 + 2 * ρ1 + 1) * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) =
        CA * (1 + 2 * ρ1 + ρ2) * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) := by ring
    refine (norm_add_le _ _).trans ?_
    have e5 := norm_add_le ((X2 τ : ℂ) * A τ) ((X1 τ : ℂ) * A1 τ)
    have e6 := norm_add_le ((X1 τ : ℂ) * A1 τ) ((X τ : ℂ) * A2 τ)
    have : CA * (1 + 2 * ρ1 + ρ2) * τ ^ (-3 / 2 : ℝ) / (1 + τ) =
        CA * (ρ2 + 2 * ρ1 + 1) * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) := by ring
    rw [this]
    have : ρ2 * CA * τ ^ (-3 / 2 : ℝ) / (1 + τ) + ρ1 * CA * τ ^ (-3 / 2 : ℝ) / (1 + τ) +
        (ρ1 * CA * τ ^ (-3 / 2 : ℝ) / (1 + τ) + CA * τ ^ (-3 / 2 : ℝ) / (1 + τ)) =
        CA * (ρ2 + 2 * ρ1 + 1) * (τ ^ (-3 / 2 : ℝ) / (1 + τ)) := by ring
    linarith [t1, t2, t3, e5, e6]

end FormalResearch.SignUncertainty.CtOsc
