module

public import Mathlib

/-!
# The Jacobi weight for real parameters and its Beta integral

For real `α β > -1` the Jacobi weight of DLMF 18.3.1 is
`w(x) = (1-x)^α (1+x)^β` (real powers, `Real.rpow`). This file proves

* `jacobiW_intervalIntegrable`: `w` is integrable on `[-1,1]`, and so is `w · r` for a continuous `r`;
* `real_betaIntegral`: the real Beta integral `∫_0^1 u^(a-1) (1-u)^(b-1) du = Γ(a)Γ(b)/Γ(a+b)`
  for `a, b > 0`, from `Complex.betaIntegral_eq_Gamma_mul_div`;
* `jacobi_beta_integral`: `∫_{-1}^1 (1-x)^α (1+x)^β dx = 2^(α+β+1) Γ(α+1)Γ(β+1)/Γ(α+β+2)`
  (the case `n = 0` of DLMF 18.3, table 18.3.1).
-/

@[expose] public section

namespace FormalResearch.Special

open MeasureTheory intervalIntegral Set

/-- The Jacobi weight `(1-x)^α (1+x)^β` for real parameters (DLMF 18.3.1). -/
noncomputable def jacobiW (α β : ℝ) (x : ℝ) : ℝ := (1 - x) ^ α * (1 + x) ^ β

/-- The weight is integrable on `[-1,1]` for `α, β > -1`. -/
theorem jacobiW_intervalIntegrable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IntervalIntegrable (jacobiW α β) volume (-1 : ℝ) 1 := by
  have hL : IntervalIntegrable (jacobiW α β) volume (-1 : ℝ) 0 := by
    have h1 : IntervalIntegrable (fun x : ℝ => (1 + x) ^ β) volume (-1 : ℝ) 0 := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) hβ).comp_add_left 1
      simpa using this
    have hc : ContinuousOn (fun x : ℝ => (1 - x) ^ α) (uIcc (-1 : ℝ) 0) := by
      refine ContinuousOn.rpow_const (by fun_prop) (fun x hx => Or.inl ?_)
      rw [uIcc_of_le (by norm_num)] at hx
      linarith [hx.2]
    exact h1.continuousOn_mul hc
  have hR : IntervalIntegrable (jacobiW α β) volume (0 : ℝ) 1 := by
    have h1 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ α) volume (0 : ℝ) 1 := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) hα).comp_sub_left 1
      simpa using this.symm
    have hc : ContinuousOn (fun x : ℝ => (1 + x) ^ β) (uIcc (0 : ℝ) 1) := by
      refine ContinuousOn.rpow_const (by fun_prop) (fun x hx => Or.inl ?_)
      rw [uIcc_of_le (by norm_num)] at hx
      linarith [hx.1]
    exact h1.mul_continuousOn hc
  exact hL.trans hR

/-- `w · r` is integrable on `[-1,1]` for a function `r` continuous on `[-1,1]`. -/
theorem jacobiW_mul_intervalIntegrable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {r : ℝ → ℝ}
    (hr : ContinuousOn r (uIcc (-1 : ℝ) 1)) :
    IntervalIntegrable (fun x => jacobiW α β x * r x) volume (-1 : ℝ) 1 :=
  (jacobiW_intervalIntegrable hα hβ).mul_continuousOn hr

/-- The real Beta integral: `∫_0^1 u^(a-1) (1-u)^(b-1) du = Γ(a) Γ(b) / Γ(a+b)` for `a, b > 0`. -/
theorem real_betaIntegral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (b - 1) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div (a : ℂ) (b : ℂ) (by simpa using ha)
    (by simpa using hb)
  unfold Complex.betaIntegral at h
  have e : ∀ u ∈ uIcc (0 : ℝ) 1, ((u : ℂ) ^ ((a : ℂ) - 1) * (1 - (u : ℂ)) ^ ((b : ℂ) - 1)) =
      ((u ^ (a - 1) * (1 - u) ^ (b - 1) : ℝ) : ℂ) := by
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    push_cast
    rw [Complex.ofReal_cpow hu.1, Complex.ofReal_cpow (by linarith [hu.2])]
    push_cast
    rfl
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_ofReal] at h
  rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  exact_mod_cast h

/-- **Beta integral for the Jacobi weight** (DLMF 18.3, table 18.3.1 at `n = 0`):
`∫_{-1}^1 (1-x)^α (1+x)^β dx = 2^(α+β+1) Γ(α+1) Γ(β+1) / Γ(α+β+2)` for `α, β > -1`. -/
theorem jacobi_beta_integral {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    ∫ x in (-1 : ℝ)..1, (1 - x) ^ α * (1 + x) ^ β =
      2 ^ (α + β + 1) * (Real.Gamma (α + 1) * Real.Gamma (β + 1)) / Real.Gamma (α + β + 2) := by
  have hb := real_betaIntegral (a := β + 1) (b := α + 1) (by linarith) (by linarith)
  simp only [add_sub_cancel_right] at hb
  have h := intervalIntegral.integral_comp_mul_sub (a := (0 : ℝ)) (b := 1) (c := 2)
    (fun x : ℝ => (1 - x) ^ α * (1 + x) ^ β) (by norm_num) 1
  have e : ∀ u : ℝ, 0 ≤ u → 0 ≤ 1 - u →
      (1 - (2 * u - 1)) ^ α * (1 + (2 * u - 1)) ^ β =
        2 ^ (α + β) * (u ^ β * (1 - u) ^ α) := by
    intro u hu hu'
    have h1 : 1 - (2 * u - 1) = 2 * (1 - u) := by ring
    have h2 : 1 + (2 * u - 1) = 2 * u := by ring
    rw [h1, h2, Real.mul_rpow (by norm_num) hu', Real.mul_rpow (by norm_num) hu,
      Real.rpow_add (by norm_num)]
    ring
  have h3 : ∫ u in (0 : ℝ)..1, (1 - (2 * u - 1)) ^ α * (1 + (2 * u - 1)) ^ β =
      2 ^ (α + β) * ∫ u in (0 : ℝ)..1, u ^ β * (1 - u) ^ α := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [uIcc_of_le (by norm_num)] at hu
    exact e u hu.1 (by linarith [hu.2])
  simp only [smul_eq_mul] at h
  rw [show (2 : ℝ) * 0 - 1 = -1 by norm_num, show (2 : ℝ) * 1 - 1 = 1 by norm_num] at h
  rw [h3, hb] at h
  have h4 : ∫ x in (-1 : ℝ)..1, (1 - x) ^ α * (1 + x) ^ β =
      2 * (2 ^ (α + β) * (Real.Gamma (β + 1) * Real.Gamma (α + 1) /
        Real.Gamma (β + 1 + (α + 1)))) := by
    linarith
  rw [h4, show β + 1 + (α + 1) = α + β + 2 by ring, Real.rpow_add (by norm_num) (α + β) 1,
    Real.rpow_one]
  ring

/-- info: 'FormalResearch.Special.jacobi_beta_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_beta_integral

/-- info: 'FormalResearch.Special.jacobiW_intervalIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobiW_intervalIntegrable

end FormalResearch.Special
