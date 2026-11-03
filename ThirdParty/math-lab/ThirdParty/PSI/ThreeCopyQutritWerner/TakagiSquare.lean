module

public import ThreeCopyQutritWerner.TakagiFamily
public import ThreeCopyQutritWerner.OrthonormalMatrixCompletion

@[expose] public section


/-! Complete the existing positive Takagi family by actual orthonormal zero
columns. The resulting square unitary factorization covers singular matrices,
including the zero matrix, without a supplied spectral decomposition. -/
noncomputable section
open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

theorem exists_square_takagi {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : Xᵀ = X) :
    ∃ (U : Matrix n n ℂ) (a : n → ℝ), Uᴴ * U = 1 ∧
      (∀ i, 0 ≤ a i) ∧ X = U * Matrix.diagonal (fun i => (a i : ℂ)) * Uᵀ := by
  classical
  obtain ⟨U, e, hU, he⟩ := orthonormal_matrix_completion (takagiFrame X hX)
    (takagiFrame_gram X hX)
  let a : n → ℝ := fun i => ∑ k : TakagiPositiveIndex X hX,
    if e k = i then takagiWeight X hX k else 0
  refine ⟨U, a, hU, ?_, ?_⟩
  · intro i
    apply Finset.sum_nonneg
    intro k _
    split_ifs
    · exact (takagiWeight_pos X hX k).le
    · exact le_rfl
  · ext i j
    rw [takagiVector_reconstruct X hX]
    symm
    calc
      (U * Matrix.diagonal (fun i => (a i : ℂ)) * Uᵀ) i j =
          ∑ s, ∑ k : TakagiPositiveIndex X hX,
            if e k = s then (takagiWeight X hX k : ℂ) * U i s * U j s else 0 := by
        rw [Matrix.mul_apply]
        simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
        apply Finset.sum_congr rfl
        intro s _
        have hcast : (a s : ℂ) = ∑ k : TakagiPositiveIndex X hX,
            if e k = s then (takagiWeight X hX k : ℂ) else 0 := by
          simp only [a, Complex.ofReal_sum]
          apply Finset.sum_congr rfl
          intro k _
          split_ifs <;> simp
        rw [hcast, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> ring
      _ = ∑ k : TakagiPositiveIndex X hX,
          (takagiWeight X hX k : ℂ) * U i (e k) * U j (e k) := by
        rw [Finset.sum_comm]
        simp
      _ = ∑ k : TakagiPositiveIndex X hX,
          (takagiWeight X hX k : ℂ) * takagiVector X hX k i *
            takagiVector X hX k j := by
        simp only [he, takagiFrame]

end ThreeCopyQutritWerner
