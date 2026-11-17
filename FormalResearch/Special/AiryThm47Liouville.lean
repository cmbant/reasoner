module

public import FormalResearch.Complex.EntireDivSq

/-!
# Liouville input for Theorem 4.7

This file proves the bounded-growth base case of the circle Liouville step in `SOFT_EDGE_THEOREMS.md`, Theorem 4.7.
The general polynomial-growth conclusion (degree at most a real exponent `s`) is not yet formalised here.
-/

@[expose] public section

open Complex

namespace FormalResearch.Special

/-- An entire function bounded by one fixed constant on arbitrarily large circles is constant. -/
theorem at47_entire_constant_of_circle_bound {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {C : ℝ} (hC : 0 ≤ C)
    (hr : ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ ∀ z : ℂ, ‖z‖ = r → ‖g z‖ ≤ C) :
    ∃ c : ℂ, ∀ z, g z = c := by
  have hlinear : ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ ∀ z : ℂ, ‖z‖ = r → ‖g z‖ ≤ C * (1 + r) := by
    intro R
    obtain ⟨r, hrR, hb⟩ := hr (max R 0)
    refine ⟨r, (le_max_left _ _).trans hrR, fun z hz => ?_⟩
    have hr0 : 0 ≤ r := (le_max_right _ _).trans hrR
    calc ‖g z‖ ≤ C := hb z hz
      _ ≤ C * (1 + r) := by nlinarith
  obtain ⟨a, b, hab⟩ := EntireDiv.entire_affine_of_circle_bound hg hC hlinear
  by_cases hb0 : b = 0
  · exact ⟨a, fun z => by rw [hab z, hb0]; simp⟩
  · have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
    let R : ℝ := (C + ‖a‖ + 1) / ‖b‖
    obtain ⟨r, hrR, hbound⟩ := hr (R + 1)
    have hRnonneg : 0 ≤ R := by dsimp [R]; positivity
    have hrpos : 0 ≤ r := by linarith
    have hval : ‖g (r : ℂ)‖ ≤ C := hbound (r : ℂ) (by simp [Real.norm_of_nonneg hrpos])
    have hrev : ‖b‖ * r ≤ ‖a + b * (r : ℂ)‖ + ‖a‖ := by
      have ht := norm_sub_le (a + b * (r : ℂ)) a
      have ht' : ‖b * (r : ℂ)‖ ≤ ‖a + b * (r : ℂ)‖ + ‖a‖ := by
        simpa [sub_eq_add_neg, add_assoc] using ht
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hrpos] at ht'
      simpa [mul_comm] using ht'
    have hlin := hab (r : ℂ)
    have : ‖a + b * (r : ℂ)‖ = ‖g (r : ℂ)‖ := by rw [← hlin]
    rw [this] at hrev
    have hrR' : R + 1 ≤ r := hrR
    have hReq : ‖b‖ * R = C + ‖a‖ + 1 := by dsimp [R]; field_simp
    have hprod := mul_le_mul_of_nonneg_left hrR' hbpos.le
    rw [mul_add, hReq] at hprod
    have : ‖b‖ * 0 < ‖b‖ * 1 := mul_lt_mul_of_pos_left zero_lt_one hbpos
    nlinarith

/-- info: 'FormalResearch.Special.at47_entire_constant_of_circle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_entire_constant_of_circle_bound

end FormalResearch.Special
