module

public import ThreeCopyQutritWerner.Basic

@[expose] public section


/-!
# Exact continuation from the endpoint to the interval

Manuscript Section 3, Proposition 3.1 (eq. (9)): the polynomial identity that
expresses `q_α - f(α) N` through the endpoint form `q`, and the forms `R` and `S`.

`sharpCurve_mul_invN_le_energy` is an implication whose three positivity
hypotheses are explicit; the endpoint inequality `0 ≤ q(C)` for rank-at-most-two
qutrit matrices is `x2_qutritEndpointInequality`.
-/

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Manuscript Proposition 3.1 (exact continuation), for every matrix `C` and
every real `α`, in arbitrary finite local dimensions. -/
theorem energy_sub_sharpCurve_mul_invN (C : Matrix (a × b × c) (a × b × c) ℂ) (α : ℝ) :
    energy α C - sharpCurve α * invN C =
      4 * α * (1 + α) / 3 * endpointEnergy C +
        α * (1 - 2 * α) * (2 / 3 - α) * formR C + 2 * α * (1 - 2 * α) * formS C := by
  unfold endpointEnergy energy sharpCurve formR formS
  ring

/-- `S` is the average of the three grouped cut forms (manuscript Section 3, eq. (8)). -/
theorem formS_eq_cutForm_average (C : Matrix (a × b × c) (a × b × c) ℂ) :
    formS C = (cutForm₁ C + cutForm₂ C + cutForm₃ C) / 3 := by
  unfold formS cutForm₁ cutForm₂ cutForm₃ invA invB
  ring

/-- The three continuation coefficients are nonnegative on `[0, 1/2]`, so
nonnegativity of `q`, `R` and `S` at one matrix gives `f(α) N ≤ q_α` there. -/
theorem sharpCurve_mul_invN_le_energy (C : Matrix (a × b × c) (a × b × c) ℂ) {α : ℝ}
    (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) (hq : 0 ≤ endpointEnergy C) (hR : 0 ≤ formR C)
    (hS : 0 ≤ formS C) : sharpCurve α * invN C ≤ energy α C := by
  have key := energy_sub_sharpCurve_mul_invN C α
  have h2 : (0 : ℝ) ≤ 1 - 2 * α := by linarith
  have c1 : 0 ≤ 4 * α * (1 + α) / 3 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) h0) (by linarith)) (by norm_num)
  have c2 : 0 ≤ α * (1 - 2 * α) * (2 / 3 - α) :=
    mul_nonneg (mul_nonneg h0 h2) (by linarith)
  have c3 : 0 ≤ 2 * α * (1 - 2 * α) :=
    mul_nonneg (mul_nonneg (by norm_num) h0) h2
  have t1 := mul_nonneg c1 hq
  have t2 := mul_nonneg c2 hR
  have t3 := mul_nonneg c3 hS
  linarith

/-- The sharp curve is the cubic `1 - 4α + 5α² - 2α³`, i.e. `q_α` at
`(N, A, B, T₀) = (1, 4, 5, 2)` (manuscript Section 3, the matrix of eq. (5)). -/
theorem sharpCurve_eq_cubic (α : ℝ) :
    sharpCurve α = 1 - α * 4 + α ^ 2 * 5 - α ^ 3 * 2 := by
  unfold sharpCurve
  ring

end ThreeCopyQutritWerner
