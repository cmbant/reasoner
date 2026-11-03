module

public import ThreeCopyQutritWerner.TwoQubitPolygon

@[expose] public section


/-! Scalar sign step linking the spin determinant polynomial to the polygon
inequalities. This uses all four nonnegative weights and includes degeneracies. -/
noncomputable section
open scoped BigOperators
namespace ThreeCopyQutritWerner

theorem four_spin_polynomial_factors (a b c d : ℝ) :
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 -
        2 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) + 8 * a * b * c * d =
      (-a + b + c + d) * (a - b + c + d) *
        (a + b - c + d) * (a + b + c - d) := by ring

private theorem first_polygon_of_product_nonneg (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hp : 0 ≤ (-a + b + c + d) * (a - b + c + d) *
      (a + b - c + d) * (a + b + c - d)) : a ≤ b + c + d := by
  by_contra h
  have hA : -a + b + c + d < 0 := by linarith
  have hB : 0 < a - b + c + d := by linarith
  have hC : 0 < a + b - c + d := by linarith
  have hD : 0 < a + b + c - d := by linarith
  have := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos hA hB) hC) hD
  linarith

/-- Nonnegativity of the exact spin determinant polynomial rules out any
one weight exceeding the sum of the other three. -/
theorem four_polygon_of_spin_polynomial_nonneg (a : Fin 4 → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (h : 0 ≤ (∑ i, (a i) ^ 2) ^ 2 - 2 * (∑ i, (a i) ^ 4) +
      8 * ∏ i, a i) : ∀ i, 2 * a i ≤ ∑ j, a j := by
  have hs : ∑ i, a i = a 0 + a 1 + a 2 + a 3 := by
    simp only [Fin.sum_univ_succ, Fin.reduceSucc, Fin.sum_univ_zero, add_zero]
    ring
  have hp : 0 ≤ (-a 0 + a 1 + a 2 + a 3) *
      (a 0 - a 1 + a 2 + a 3) * (a 0 + a 1 - a 2 + a 3) *
      (a 0 + a 1 + a 2 - a 3) := by
    rw [← four_spin_polynomial_factors]
    convert h using 1 <;>
      simp only [Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.reduceSucc,
        Fin.sum_univ_zero, Fin.prod_univ_zero, add_zero, mul_one] <;> ring
  have h0 := first_polygon_of_product_nonneg (a 0) (a 1) (a 2) (a 3)
    (ha 0) (ha 1) (ha 2) (ha 3) hp
  have h1 : a 1 ≤ a 0 + a 2 + a 3 := by
    apply first_polygon_of_product_nonneg (a 1) (a 0) (a 2) (a 3)
      (ha 1) (ha 0) (ha 2) (ha 3)
    convert hp using 1 <;> ring
  have h2 : a 2 ≤ a 1 + a 0 + a 3 := by
    apply first_polygon_of_product_nonneg (a 2) (a 1) (a 0) (a 3)
      (ha 2) (ha 1) (ha 0) (ha 3)
    convert hp using 1 <;> ring
  have h3 : a 3 ≤ a 1 + a 2 + a 0 := by
    apply first_polygon_of_product_nonneg (a 3) (a 1) (a 2) (a 0)
      (ha 3) (ha 1) (ha 2) (ha 0)
    convert hp using 1 <;> ring
  intro i
  rw [hs]
  fin_cases i
  · change 2 * a 0 ≤ a 0 + a 1 + a 2 + a 3
    linarith
  · change 2 * a 1 ≤ a 0 + a 1 + a 2 + a 3
    linarith
  · change 2 * a 2 ≤ a 0 + a 1 + a 2 + a 3
    linarith
  · change 2 * a 3 ≤ a 0 + a 1 + a 2 + a 3
    linarith

end ThreeCopyQutritWerner
