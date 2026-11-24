module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Auxiliary numerics for the Hankel window lemma (M5-S6b)

`hankel_window_cnum` (powers of `c ≥ 10¹⁴` through `t = c^{1/12} ≥ 14`), `hankel_window_slit` (`Re u^{1/2} > 0`
excludes the cut), `hankel_window_L1`, `hankel_window_L2` (the exponent bookkeeping of `YVEnvBound`).
-/

@[expose] public section

open Complex
open scoped Real

namespace FormalResearch.SignUncertainty

lemma hankel_window_cnum {c : ℝ} (hc : 1e14 ≤ c) :
    ∃ t : ℝ, 14 ≤ t ∧ c = t ^ 12 ∧ c ^ (1 / 3 : ℝ) = t ^ 4 ∧ c ^ (2 / 3 : ℝ) = t ^ 8 ∧
      c ^ (-(1 / 12 : ℝ)) = t⁻¹ ∧ c ^ (-(5 / 6 : ℝ)) = (t ^ 10)⁻¹ ∧ Real.log c ≤ 12 * t := by
  have hc0 : 0 < c := by linarith
  set t : ℝ := c ^ (1 / 12 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hc0 _
  have hpow : ∀ (a : ℝ) (n : ℕ), a = n / 12 → c ^ a = t ^ n := by
    intro a n ha
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ha]
    congr 1; ring
  have h12 : c = t ^ 12 := by
    have := hpow 1 12 (by norm_num)
    rwa [Real.rpow_one] at this
  have h14 : 14 ≤ t := by
    by_contra hlt
    push Not at hlt
    have : t ^ 12 < (14 : ℝ) ^ 12 := pow_lt_pow_left₀ hlt ht0.le (by norm_num)
    rw [← h12] at this
    norm_num at this
    linarith
  refine ⟨t, h14, h12, hpow _ 4 (by norm_num), hpow _ 8 (by norm_num), ?_, ?_, ?_⟩
  · rw [Real.rpow_neg hc0.le, ht]
  · rw [Real.rpow_neg hc0.le, hpow (5 / 6) 10 (by norm_num)]
  · have h1 : Real.log c = 12 * Real.log t := by rw [h12, Real.log_pow]; norm_num
    rw [h1]
    have := Real.log_le_sub_one_of_pos ht0
    linarith

/-- `Re u^{1/2} > 0` and `u ≠ 0` exclude the cut `u ≤ 0`. -/
lemma hankel_window_slit {u : ℂ} (hu0 : u ≠ 0) (h : 0 < (u ^ (1 / 2 : ℂ)).re) :
    ¬ (u.im = 0 ∧ u.re ≤ 0) := by
  rintro ⟨him, hre⟩
  have hre' : u.re < 0 := by
    refine lt_of_le_of_ne hre ?_
    intro h0
    apply hu0
    apply Complex.ext <;> simp [h0, him]
  have harg : Complex.arg u = Real.pi := Complex.arg_eq_pi_iff.2 ⟨hre', him⟩
  rw [Complex.cpow_def_of_ne_zero hu0, Complex.exp_re] at h
  have : (Complex.log u * (1 / 2 : ℂ)).im = Real.pi / 2 := by
    rw [Complex.mul_im]
    simp [Complex.log_im, harg]
    ring
  rw [this, Real.cos_pi_div_two, mul_zero] at h
  exact lt_irrefl _ h

/-- `‖u‖^{1/2} c^{-5/6} ≤ ‖u‖^{-3/4}` for `‖u‖ ≤ c^{2/3}`. -/
lemma hankel_window_L1 {c N : ℝ} (hc : 0 < c) (hN : 0 < N) (hNc : N ≤ c ^ (2 / 3 : ℝ)) :
    N ^ (1 / 2 : ℝ) * c ^ (-(5 / 6 : ℝ)) ≤ N ^ (-(3 / 4 : ℝ)) := by
  have h1 : N ^ (-(3 / 4 : ℝ)) = N ^ (1 / 2 : ℝ) * N ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_add hN]; norm_num
  have h2 : c ^ (-(5 / 6 : ℝ)) = (c ^ (2 / 3 : ℝ)) ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_mul hc.le]; norm_num
  have h3 : (c ^ (2 / 3 : ℝ)) ^ (-(5 / 4 : ℝ)) ≤ N ^ (-(5 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hN hNc (by norm_num)
  rw [h1, h2]
  have : 0 ≤ N ^ (1 / 2 : ℝ) := Real.rpow_nonneg hN.le _
  exact mul_le_mul_of_nonneg_left h3 this

/-- `c⁻¹ ≤ ‖u‖^{-3/4} / (X √X)` for `0 < X ≤ ‖u‖^{1/2}`, `‖u‖ ≤ c^{2/3}`. -/
lemma hankel_window_L2 {c N X : ℝ} (hc : 0 < c) (hN : 0 < N) (hNc : N ≤ c ^ (2 / 3 : ℝ)) (hX : 0 < X)
    (hXN : X ≤ N ^ (1 / 2 : ℝ)) : c⁻¹ ≤ N ^ (-(3 / 4 : ℝ)) / (X * Real.sqrt X) := by
  set a : ℝ := N ^ (1 / 4 : ℝ) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hN _
  have hpow : ∀ (b : ℝ) (n : ℕ), b = n / 4 → N ^ b = a ^ n := by
    intro b n hb
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hN.le, hb]
    congr 1; ring
  have h2 : N ^ (1 / 2 : ℝ) = a ^ 2 := hpow _ 2 (by norm_num)
  have h6 : N ^ (3 / 2 : ℝ) = a ^ 6 := by
    have : N ^ (3 / 2 : ℝ) = N ^ ((6 : ℕ) / 4 : ℝ) := by norm_num
    rw [this]; exact hpow _ 6 rfl
  have h3 : N ^ (-(3 / 4 : ℝ)) = (a ^ 3)⁻¹ := by
    rw [Real.rpow_neg hN.le, hpow (3 / 4) 3 (by norm_num)]
  have ha6 : a ^ 6 ≤ c := by
    rw [← h6]
    calc N ^ (3 / 2 : ℝ) ≤ (c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hN.le hNc (by norm_num)
      _ = c := by rw [← Real.rpow_mul hc.le]; norm_num
  have hXa : X ≤ a ^ 2 := h2 ▸ hXN
  have hsq : Real.sqrt X ≤ a := by
    rw [Real.sqrt_le_left ha0.le]; exact hXa
  have hsq0 : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hprod : X * Real.sqrt X ≤ a ^ 2 * a := mul_le_mul hXa hsq hsq0.le (by positivity)
  rw [h3]
  calc c⁻¹ ≤ (a ^ 6)⁻¹ := inv_anti₀ (by positivity) ha6
    _ = (a ^ 3)⁻¹ / (a ^ 2 * a) := by field_simp
    _ ≤ (a ^ 3)⁻¹ / (X * Real.sqrt X) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hprod

end FormalResearch.SignUncertainty
