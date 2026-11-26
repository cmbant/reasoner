module

public import FormalResearch.SignUncertainty.MiddleBandE6

/-!
# Scalar helpers for the positivity bands of `O.6`

Elementary real-variable lemmas used by `MiddleBandPositivity.lean`: tails of negative powers, the relations between `ε = c^{-1/3}`, `S = S_eff`,
`L = log(π² ξ)` and `y = ε² S`, and the closing inequality of the middle band.

Status: proved, unconditional.
-/

@[expose] public section

open Set

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- Negative powers are eventually small. -/
theorem exists_rpow_neg_le {p : ℝ} (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x : ℝ, M ≤ x → x ^ (-p) ≤ ε := by
  refine ⟨max 1 ((ε⁻¹) ^ (1 / p)), le_max_left _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have h : ε⁻¹ ≤ x ^ p := by
    have h1 : (ε⁻¹) ^ (1 / p) ≤ x := (le_max_right _ _).trans hx
    calc ε⁻¹ = ((ε⁻¹) ^ (1 / p)) ^ p := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp.ne', Real.rpow_one]
      _ ≤ x ^ p := Real.rpow_le_rpow (by positivity) h1 hp.le
  rw [Real.rpow_neg hx0.le]
  calc (x ^ p)⁻¹ ≤ (ε⁻¹)⁻¹ := inv_anti₀ (by positivity) h
    _ = ε := inv_inv ε

/-- Closing inequality of the middle band. -/
theorem middle_scalar {κ c₂ Cm M₁ K y : ℝ} (hκ : 0 < κ) (hc₂ : 0 < c₂) (hCm : 0 ≤ Cm) (hM₁ : 1 ≤ M₁) (hK : 1 ≤ K)
    (hbig : 2 * Cm * M₁ < κ * c₂ * K ^ 2) (hy0 : 0 < y) (hy : y ≤ M₁ / K ^ 2) :
    2 * (Cm * y) < κ * (c₂ * min 1 (K ^ 2 * y)) := by
  have hK2 : 0 < K ^ 2 := by positivity
  rcases le_total (K ^ 2 * y) 1 with h | h
  · rw [min_eq_right h]
    have : 2 * (Cm * y) ≤ 2 * Cm * M₁ * y := by nlinarith [mul_nonneg hCm hy0.le]
    nlinarith [mul_pos hκ hc₂, mul_lt_mul_of_pos_right hbig hy0]
  · rw [min_eq_left h]
    have h1 : y * K ^ 2 ≤ M₁ := by rwa [le_div_iff₀ hK2] at hy
    have : 2 * (Cm * y) * K ^ 2 ≤ 2 * Cm * M₁ := by nlinarith [mul_nonneg hCm (by linarith : (0 : ℝ) ≤ 2)]
    have h2 : 2 * (Cm * y) * K ^ 2 < κ * c₂ * K ^ 2 := by linarith
    have := lt_of_mul_lt_mul_right h2 hK2.le
    linarith

/-- `L = π² ε² S`. -/
theorem log_eq_hbS {c ξ : ℝ} (hc : 0 < c) :
    Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * liftEps c ^ 2 * hbS c ξ := by
  have hε := liftEps_pos hc
  unfold hbS
  field_simp

/-- `c⁻¹ L^{-3/2} = (π² S)^{-3/2}`. -/
theorem inv_mul_log_rpow {c ξ : ℝ} (hc : 0 < c) (hS : 0 < hbS c ξ) :
    c⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) = (Real.pi ^ 2 * hbS c ξ) ^ (-(3 / 2 : ℝ)) := by
  have hε := liftEps_pos hc
  have hcube := liftEps_cube_mul hc
  rw [log_eq_hbS hc, show Real.pi ^ 2 * liftEps c ^ 2 * hbS c ξ = liftEps c ^ 2 * (Real.pi ^ 2 * hbS c ξ) by ring,
    Real.mul_rpow (by positivity) (by positivity)]
  have h2 : (liftEps c ^ 2) ^ (-(3 / 2 : ℝ)) = c := by
    rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast (liftEps c) 2, ← Real.rpow_mul hε.le]
    norm_num
    field_simp
    linarith
  rw [h2]
  have : c⁻¹ * (c * (Real.pi ^ 2 * hbS c ξ) ^ (-(3 / 2 : ℝ))) = (Real.pi ^ 2 * hbS c ξ) ^ (-(3 / 2 : ℝ)) := by
    field_simp
  exact this

/-- A complex number within `A` of the positive real `A` has positive real part. -/
theorem re_pos_of_norm_lt {Z : ℂ} {A : ℝ} (h : ‖Z - (A : ℂ)‖ < A) : 0 < Z.re := by
  have h1 : |(Z - (A : ℂ)).re| ≤ ‖Z - (A : ℂ)‖ := Complex.abs_re_le_norm _
  have h2 : (Z - (A : ℂ)).re = Z.re - A := by simp
  rw [h2] at h1
  have := (abs_le.mp h1).1
  linarith

theorem ceBeta1_gt_two : 2 < ceBeta1 := by
  have h3 := ceBeta1_cube
  have hpi := Real.pi_gt_three
  have hb := ceBeta1_pos
  by_contra hcon
  push Not at hcon
  have : ceBeta1 ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hb.le hcon 3
  have h4 : (3 : ℝ) ^ 4 ≤ Real.pi ^ 4 := pow_le_pow_left₀ (by norm_num) hpi.le 4
  nlinarith

theorem one_le_ceBeta1_cube_div : 1 ≤ ceBeta1 ^ 3 / 4 := by
  have h3 := ceBeta1_cube
  have h4 : (3 : ℝ) ^ 4 ≤ Real.pi ^ 4 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 4
  rw [h3]; nlinarith

/-- `c⁻¹ S^{3/2} = y^{3/2}` with `y = ε² S`. -/
theorem inv_mul_rpow_three_halves {c S : ℝ} (hc : 0 < c) (hS : 0 < S) :
    c⁻¹ * S ^ (3 / 2 : ℝ) = (liftEps c ^ 2 * S) ^ (3 / 2 : ℝ) := by
  have hε := liftEps_pos hc
  have hcube := liftEps_cube_mul hc
  rw [Real.mul_rpow (by positivity) hS.le]
  have h2 : (liftEps c ^ 2) ^ (3 / 2 : ℝ) = liftEps c ^ 3 := by
    rw [← Real.rpow_natCast (liftEps c) 2, ← Real.rpow_mul hε.le]
    norm_num
  rw [h2]
  have : c⁻¹ = liftEps c ^ 3 := by field_simp; linarith
  rw [this]

/-- `c^{-5/2} S^{3/2} ≤ y` for `y = ε² S ≤ 1`, `c ≥ 1`. -/
theorem c_rpow_mul_S_le {c S : ℝ} (hc : 1 ≤ c) (hS : 0 < S) (hy : liftEps c ^ 2 * S ≤ 1) :
    c ^ (-(5 / 2 : ℝ)) * S ^ (3 / 2 : ℝ) ≤ liftEps c ^ 2 * S := by
  have hc0 : 0 < c := by linarith
  have hy0 : 0 < liftEps c ^ 2 * S := by have := liftEps_pos hc0; positivity
  have h1 : c ^ (-(5 / 2 : ℝ)) * S ^ (3 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) * (c⁻¹ * S ^ (3 / 2 : ℝ)) := by
    have : c ^ (-(5 / 2 : ℝ)) = c ^ (-(3 / 2 : ℝ)) * c⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; norm_num
    rw [this]; ring
  rw [h1, inv_mul_rpow_three_halves hc0 hS]
  have h2 : c ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num)
  have h3 : (liftEps c ^ 2 * S) ^ (3 / 2 : ℝ) ≤ liftEps c ^ 2 * S := by
    calc (liftEps c ^ 2 * S) ^ (3 / 2 : ℝ) ≤ (liftEps c ^ 2 * S) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hy0 hy (by norm_num)
      _ = _ := Real.rpow_one _
  have h4 : 0 ≤ (liftEps c ^ 2 * S) ^ (3 / 2 : ℝ) := by positivity
  calc c ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) ^ (3 / 2 : ℝ) ≤ 1 * (liftEps c ^ 2 * S) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right h2 h4
    _ ≤ _ := by linarith

/-- `c⁻¹ L^{-1/4} ≤ S^{-3/2} y` for `y = ε² S ≤ 1`, `L = π² y`. -/
theorem inv_mul_log_quarter_le {c S : ℝ} (hc : 0 < c) (hS : 0 < S) (hy : liftEps c ^ 2 * S ≤ 1) :
    c⁻¹ * (Real.pi ^ 2 * (liftEps c ^ 2 * S)) ^ (-(1 / 4 : ℝ)) ≤ S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) := by
  have hε := liftEps_pos hc
  set y := liftEps c ^ 2 * S with hydef
  have hy0 : 0 < y := by positivity
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have h1 : (Real.pi ^ 2 * y) ^ (-(1 / 4 : ℝ)) ≤ y ^ (-(1 / 4 : ℝ)) := by
    rw [Real.mul_rpow (by positivity) hy0.le]
    have : (Real.pi ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hpi (by norm_num)
    have h' : 0 ≤ y ^ (-(1 / 4 : ℝ)) := by positivity
    nlinarith
  have hS32 : 0 < S ^ (3 / 2 : ℝ) := by positivity
  have h2 : c⁻¹ * S ^ (3 / 2 : ℝ) = y ^ (3 / 2 : ℝ) := inv_mul_rpow_three_halves hc hS
  have h3 : S ^ (-(3 / 2 : ℝ)) = (S ^ (3 / 2 : ℝ))⁻¹ := Real.rpow_neg hS.le _
  have h4 : c⁻¹ * y ^ (-(1 / 4 : ℝ)) * S ^ (3 / 2 : ℝ) ≤ y := by
    calc c⁻¹ * y ^ (-(1 / 4 : ℝ)) * S ^ (3 / 2 : ℝ) = y ^ (3 / 2 : ℝ) * y ^ (-(1 / 4 : ℝ)) := by rw [← h2]; ring
      _ = y ^ (5 / 4 : ℝ) := by rw [← Real.rpow_add hy0]; norm_num
      _ ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy0 hy (by norm_num)
      _ = y := Real.rpow_one y
  rw [h3, show (S ^ (3 / 2 : ℝ))⁻¹ * y = y / S ^ (3 / 2 : ℝ) by ring, le_div_iff₀ hS32]
  calc c⁻¹ * (Real.pi ^ 2 * y) ^ (-(1 / 4 : ℝ)) * S ^ (3 / 2 : ℝ)
      ≤ c⁻¹ * y ^ (-(1 / 4 : ℝ)) * S ^ (3 / 2 : ℝ) := by gcongr
    _ ≤ y := h4

theorem norm_sub_split (I D σ A : ℂ) (hσ : ‖σ‖ = 1) : ‖I + σ * D - A‖ ≤ ‖I - A‖ + ‖D‖ := by
  have : I + σ * D - A = (I - A) + σ * D := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hσ, one_mul]

/-- info: 'FormalResearch.SignUncertainty.exists_rpow_neg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_rpow_neg_le
/-- info: 'FormalResearch.SignUncertainty.middle_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms middle_scalar
/-- info: 'FormalResearch.SignUncertainty.log_eq_hbS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms log_eq_hbS
/-- info: 'FormalResearch.SignUncertainty.inv_mul_log_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inv_mul_log_rpow
/-- info: 'FormalResearch.SignUncertainty.re_pos_of_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms re_pos_of_norm_lt
/-- info: 'FormalResearch.SignUncertainty.ceBeta1_gt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ceBeta1_gt_two
/-- info: 'FormalResearch.SignUncertainty.one_le_ceBeta1_cube_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms one_le_ceBeta1_cube_div
/-- info: 'FormalResearch.SignUncertainty.inv_mul_rpow_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inv_mul_rpow_three_halves
/-- info: 'FormalResearch.SignUncertainty.c_rpow_mul_S_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms c_rpow_mul_S_le
/-- info: 'FormalResearch.SignUncertainty.inv_mul_log_quarter_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inv_mul_log_quarter_le
/-- info: 'FormalResearch.SignUncertainty.norm_sub_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms norm_sub_split

end FormalResearch.SignUncertainty
