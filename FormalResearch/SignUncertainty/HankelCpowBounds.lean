module

public import Mathlib

/-!
# Elementary bounds for `(1 + x)^α` near `x = 0`

For `‖x‖ ≤ t < 1` and `0 < α ≤ 1`: `‖(1+x)^α - 1‖ ≤ α t/(1-t)` and `‖(1+x)^{-γ}‖ ≤ 1/(1-t)` (`0 ≤ γ ≤ 1`).
These are the (slightly weaker, mean-value) form of the binomial bound in the proof of `gt:7.7b`
(`CFT/sign_uncertainty/paper/langer_transport.tex`) and suffice for the constants `|h'-1| ≤ 1.2·10⁻³`,
`|𝗆'-1| ≤ 9·10⁻⁴`.
-/

@[expose] public section

open Complex Set Metric
open scoped Real

namespace FormalResearch.SignUncertainty

lemma one_add_mem_slitPlane_of_norm_lt {y : ℂ} (hy : ‖y‖ < 1) : (1 + y) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  have : |y.re| ≤ ‖y‖ := Complex.abs_re_le_norm y
  have h2 := abs_le.1 this
  simp only [Complex.add_re, Complex.one_re]
  linarith [h2.1]

lemma norm_one_add_ge {y : ℂ} {t : ℝ} (hy : ‖y‖ ≤ t) : 1 - t ≤ ‖1 + y‖ := by
  have := norm_sub_norm_le (1 : ℂ) (-y)
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

lemma norm_one_add_cpow_neg_le {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) {y : ℂ} {t : ℝ}
    (hy : ‖y‖ ≤ t) (ht : t < 1) : ‖(1 + y) ^ (((-γ : ℝ) : ℂ))‖ ≤ 1 / (1 - t) := by
  have h1 : 0 < 1 - t := by linarith
  have ht0 : 0 ≤ t := (norm_nonneg y).trans hy
  have hge := norm_one_add_ge hy
  have hpos : 0 < ‖1 + y‖ := lt_of_lt_of_le h1 hge
  rw [Complex.norm_cpow_real, Real.rpow_neg hpos.le]
  have h2 : (1 - t) ^ γ ≤ ‖1 + y‖ ^ γ := Real.rpow_le_rpow h1.le hge hγ
  have h3 : (1 - t) ≤ (1 - t) ^ γ := by
    have := Real.rpow_le_rpow_of_exponent_ge h1 (by linarith) hγ1
    simpa using this
  rw [one_div]
  exact inv_anti₀ h1 (h3.trans h2)

lemma norm_one_add_cpow_sub_one_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {x : ℂ} {t : ℝ}
    (hx : ‖x‖ ≤ t) (ht : t < 1) : ‖(1 + x) ^ ((α : ℂ)) - 1‖ ≤ α * t / (1 - t) := by
  have h1 : 0 < 1 - t := by linarith
  have ht0 : 0 ≤ t := (norm_nonneg x).trans hx
  have hd : ∀ y ∈ closedBall (0 : ℂ) t,
      HasDerivAt (fun y : ℂ => (1 + y) ^ (α : ℂ)) ((α : ℂ) * (1 + y) ^ ((α : ℂ) - 1) * 1) y := by
    intro y hy
    have hy1 : ‖y‖ < 1 := lt_of_le_of_lt (by simpa using mem_closedBall_zero_iff.1 hy) ht
    have := ((hasDerivAt_id y).const_add (1 : ℂ)).cpow_const (c := (α : ℂ)) (one_add_mem_slitPlane_of_norm_lt hy1)
    simpa using this
  have hb : ∀ y ∈ closedBall (0 : ℂ) t, ‖(α : ℂ) * (1 + y) ^ ((α : ℂ) - 1) * 1‖ ≤ α / (1 - t) := by
    intro y hy
    have hyt : ‖y‖ ≤ t := by simpa using mem_closedBall_zero_iff.1 hy
    have := norm_one_add_cpow_neg_le (γ := 1 - α) (by linarith) (by linarith) hyt ht
    have e : (((-(1 - α) : ℝ)) : ℂ) = (α : ℂ) - 1 := by push_cast; ring
    rw [e] at this
    rw [mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
    calc α * ‖(1 + y) ^ ((α : ℂ) - 1)‖ ≤ α * (1 / (1 - t)) := mul_le_mul_of_nonneg_left this hα.le
      _ = α / (1 - t) := by ring
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℂ => (1 + y) ^ (α : ℂ)) (s := closedBall (0 : ℂ) t) (x := 0) (y := x)
    (fun y hy => (hd y hy).hasDerivWithinAt) hb (convex_closedBall _ _)
    (mem_closedBall_self ht0) (by simpa using hx)
  simp only [add_zero, Complex.one_cpow, sub_zero] at hmv
  calc ‖(1 + x) ^ (α : ℂ) - 1‖ ≤ α / (1 - t) * ‖x‖ := hmv
    _ ≤ α / (1 - t) * t := mul_le_mul_of_nonneg_left hx (by positivity)
    _ = α * t / (1 - t) := by ring

/-- info: 'FormalResearch.SignUncertainty.norm_one_add_cpow_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_one_add_cpow_sub_one_le

/-- info: 'FormalResearch.SignUncertainty.norm_one_add_cpow_neg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_one_add_cpow_neg_le

end FormalResearch.SignUncertainty
