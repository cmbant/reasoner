module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Scalar inequalities for the deep lobe (`lem:radial-compactness`, Step 2)

With `g(σ) < (4/3) σ²` the exponent is `(4/9) σ³ - π² a σ`; the constants below are what it gives.
-/

@[expose] public section

open scoped Real

namespace FormalResearch.SignUncertainty

/-- `σ = 2 √(3a)`: `(4/9) σ³ - π² a σ ≤ -15 a √a`. -/
theorem deep_lobe_num1 {a : ℝ} (ha : 0 < a) :
    (4 / 9 : ℝ) * (2 * Real.sqrt (3 * a)) ^ 3 - Real.pi ^ 2 * a * (2 * Real.sqrt (3 * a)) ≤
      -15 * (a * Real.sqrt a) := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hra : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have h3 : Real.sqrt (3 * a) = Real.sqrt 3 * Real.sqrt a := Real.sqrt_mul (by norm_num) a
  have hs3 : 1.732 < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs3' : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hpi : 9.869 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_d4, Real.pi_pos]
  rw [h3]
  set r := Real.sqrt a with hrdef
  set q := Real.sqrt 3 with hqdef
  have hq0 : 0 < q := by linarith
  have key : 15 ≤ q * (2 * Real.pi ^ 2 - 32 / 3) := by nlinarith
  have hr3 : 0 < r ^ 3 := by positivity
  have e1 : (4 / 9 : ℝ) * (2 * (q * r)) ^ 3 - Real.pi ^ 2 * a * (2 * (q * r)) =
      -(r ^ 3) * (q * (2 * Real.pi ^ 2 - 32 / 3)) := by
    rw [← hra]
    have : q ^ 3 = 3 * q := by nlinarith [hs3']
    linear_combination ((32 : ℝ) / 9 * r ^ 3) * this
  have e2 : a * r = r ^ 3 := by rw [← hra]; ring
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left key hr3.le]

/-- `s = 1/2`, `a ≥ 1/48`: `1/18 - π²/96 ≤ -1/25`. -/
theorem deep_lobe_num3 : (1 / 18 : ℝ) - Real.pi ^ 2 / 96 ≤ -(1 / 25) := by
  nlinarith [Real.pi_gt_d4]

end FormalResearch.SignUncertainty
