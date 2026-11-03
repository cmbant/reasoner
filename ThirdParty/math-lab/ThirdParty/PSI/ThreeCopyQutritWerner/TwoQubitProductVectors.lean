module

public import ThreeCopyQutritWerner.TwoQubitSpinDeterminant
public import ThreeCopyQutritWerner.QubitEndpoint

@[expose] public section


/-! A zero spin quadratic form is exactly the product-vector condition on
the literal two-qubit coefficient matrix, including the zero vector. Finite
ensembles of such vectors give the existing finite separability predicate. -/
noncomputable section
open scoped BigOperators Matrix Kronecker
namespace ThreeCopyQutritWerner

theorem twoQubitVector_product_of_det_zero (v : Fin 2 × Fin 2 → ℂ)
    (h : (Matrix.of (fun i j : Fin 2 => v (i, j))).det = 0) :
    ∃ a b : Fin 2 → ℂ, v = fun p => a p.1 * b p.2 := by
  have hd : v (0, 0) * v (1, 1) - v (0, 1) * v (1, 0) = 0 := by
    simpa only [Matrix.det_fin_two, Matrix.of_apply] using h
  by_cases h00 : v (0, 0) = 0
  · by_cases h01 : v (0, 1) = 0
    · refine ⟨![0, 1], ![v (1, 0), v (1, 1)], ?_⟩
      funext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp [h00, h01]
    · have hz : v (1, 0) = 0 := by
        have hp : v (0, 1) * v (1, 0) = 0 := by
          simpa only [h00, zero_mul, zero_sub, neg_eq_zero] using hd
        exact (mul_eq_zero.mp hp).resolve_left h01
      refine ⟨![v (0, 1), v (1, 1)], ![0, 1], ?_⟩
      funext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp [h00, hz]
  · refine ⟨![v (0, 0), v (1, 0)], ![1, v (0, 1) / v (0, 0)], ?_⟩
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> norm_num <;>
      field_simp [h00] <;> linear_combination hd

theorem twoQubitVector_product_of_spin_zero (v : Fin 2 × Fin 2 → ℂ)
    (h : (∑ i, ∑ j, v i * twoQubitSpinMatrix i j * v j) = 0) :
    ∃ a b : Fin 2 → ℂ, v = fun p => a p.1 * b p.2 := by
  apply twoQubitVector_product_of_det_zero v
  rw [twoQubitSpinMatrix_quadratic] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

theorem ketBra_product_eq_kronecker (a b : Fin 2 → ℂ) :
    ketBra (fun p : Fin 2 × Fin 2 => a p.1 * b p.2)
      (fun p : Fin 2 × Fin 2 => a p.1 * b p.2) = ketBra a a ⊗ₖ ketBra b b := by
  ext p q
  simp only [ketBra, Matrix.kroneckerMap_apply, map_mul]
  ring

/-- The output is a literal finite sum of positive product operators with
nonnegative weights, as required by the pre-existing separability definition. -/
theorem isBipartiteSeparable_of_spin_zero_ensemble {N : ℕ}
    (v : Fin N → Fin 2 × Fin 2 → ℂ)
    (h : ∀ k, (∑ i, ∑ j, v k i * twoQubitSpinMatrix i j * v k j) = 0) :
    IsBipartiteSeparable (∑ k, ketBra (v k) (v k)) := by
  classical
  choose a b hab using fun k => twoQubitVector_product_of_spin_zero (v k) (h k)
  refine ⟨N, fun _ => 1, fun k => ketBra (a k) (a k), fun k => ketBra (b k) (b k),
    fun _ => by norm_num, fun k => ketBra_self_posSemidef _,
    fun k => ketBra_self_posSemidef _, ?_⟩
  apply Finset.sum_congr rfl
  intro k _
  rw [hab k, ketBra_product_eq_kronecker]
  simp

end ThreeCopyQutritWerner
