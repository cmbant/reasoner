module

public import FormalResearch.Complex.EntireDivSq

/-!
# Liouville input for Theorem 4.7

This file proves the bounded-growth base case of the circle Liouville step in `SOFT_EDGE_THEOREMS.md`, Theorem 4.7.
The polynomial-growth version (degree at most a natural exponent `n`) is proved by induction.
-/

@[expose] public section

open Complex Polynomial

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

/-- **Liouville step of Theorem 4.7.**  An entire function with `‖g z‖ ≤ C (1 + r)^n` on circles `‖z‖ = r` of
arbitrarily large radii (`n` natural) is a polynomial of degree at most `n`.  Proved by induction on `n`
through `dslope g 0` and the maximum modulus principle (base case `at47_entire_constant_of_circle_bound`).
A real growth exponent `s` is covered by `n = ⌈s⌉`; the sharper degree `≤ ⌊s⌋` is not proved. -/
theorem at47_entire_polynomial_of_circle_bound (n : ℕ) :
    ∀ {g : ℂ → ℂ}, Differentiable ℂ g → ∀ {C : ℝ}, 0 ≤ C →
    (∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ ∀ z : ℂ, ‖z‖ = r → ‖g z‖ ≤ C * (1 + r) ^ n) →
    ∃ p : ℂ[X], p.natDegree ≤ n ∧ ∀ z, g z = p.eval z := by
  induction n with
  | zero =>
    intro g hg C hC hr
    obtain ⟨c, hc⟩ := at47_entire_constant_of_circle_bound hg hC (by
      intro R; obtain ⟨r, h1, h2⟩ := hr R
      exact ⟨r, h1, fun z hz => by simpa using h2 z hz⟩)
    exact ⟨Polynomial.C c, by simp, fun z => by simp [hc z]⟩
  | succ n ih =>
    intro g hg C hC hr
    have dh := EntireDiv.differentiable_dslope_entire hg 0
    have hb : ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ ∀ z : ℂ, ‖z‖ = r →
        ‖dslope g 0 z‖ ≤ (2 * C + ‖g 0‖) * (1 + r) ^ n := by
      intro R
      obtain ⟨r, hrR, hb⟩ := hr (max R 1)
      have hr1 : 1 ≤ r := (le_max_right _ _).trans hrR
      refine ⟨r, (le_max_left _ _).trans hrR, fun z hz => ?_⟩
      have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
      rw [dslope_of_ne _ hz0, slope_def_field, sub_zero, norm_div, hz]
      have hrpos : 0 < r := by linarith
      rw [div_le_iff₀ hrpos]
      have hp : 0 ≤ (1 + r) ^ n := by positivity
      have h1 : ‖g z - g 0‖ ≤ C * (1 + r) ^ (n + 1) + ‖g 0‖ :=
        (norm_sub_le _ _).trans (by linarith [hb z hz])
      have h2 : (1 + r) ^ (n + 1) ≤ 2 * r * (1 + r) ^ n := by
        rw [pow_succ]; nlinarith
      have h3 : ‖g 0‖ ≤ ‖g 0‖ * (1 + r) ^ n * r := by
        have : 1 ≤ (1 + r) ^ n := one_le_pow₀ (by linarith)
        have h4 : 1 ≤ (1 + r) ^ n * r := by nlinarith
        nlinarith [norm_nonneg (g 0), mul_le_mul_of_nonneg_left h4 (norm_nonneg (g 0))]
      calc ‖g z - g 0‖ ≤ C * (1 + r) ^ (n + 1) + ‖g 0‖ := h1
        _ ≤ C * (2 * r * (1 + r) ^ n) + ‖g 0‖ * (1 + r) ^ n * r := by
          nlinarith [mul_le_mul_of_nonneg_left h2 hC]
        _ = _ := by ring
    obtain ⟨q, hq, hqe⟩ := ih dh (by positivity) hb
    refine ⟨Polynomial.C (g 0) + Polynomial.X * q, ?_, fun z => ?_⟩
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
      refine (Polynomial.natDegree_mul_le).trans ?_
      simp only [Polynomial.natDegree_X]; omega
    · have e := sub_smul_dslope g 0 z
      simp only [smul_eq_mul] at e
      simp [← hqe z]
      linear_combination -e

/-- info: 'FormalResearch.Special.at47_entire_polynomial_of_circle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_entire_polynomial_of_circle_bound

end FormalResearch.Special
