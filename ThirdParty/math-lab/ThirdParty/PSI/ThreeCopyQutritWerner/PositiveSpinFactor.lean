module

public import ThreeCopyQutritWerner.TakagiSquare

@[expose] public section


/-! Construct a positive Gram ensemble with diagonal nonnegative symmetric
pairings. Both the Gram factor and its Takagi change of columns are derived from
the original positive matrix; no spectral data are additional hypotheses. -/
noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder
namespace ThreeCopyQutritWerner

theorem exists_psd_symmetric_congruence_factor {n : Type*}
    [Fintype n] [DecidableEq n] (ρ S : Matrix n n ℂ)
    (hρ : ρ.PosSemidef) (hS : Sᵀ = S) :
    ∃ (A : Matrix n n ℂ) (a : n → ℝ),
      ρ = A * Aᴴ ∧ (∀ i, 0 ≤ a i) ∧
        Aᵀ * S * A = Matrix.diagonal (fun i => (a i : ℂ)) := by
  classical
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  let B := Cᴴ
  have hB : B * Bᴴ = ρ := by
    simpa [B, Matrix.star_eq_conjTranspose] using hC.symm
  let X := Bᵀ * S * B
  have hX : Xᵀ = X := by
    simp only [X, Matrix.transpose_mul, Matrix.transpose_transpose, hS,
      Matrix.mul_assoc]
  obtain ⟨U, a, hU, ha, hfactor⟩ := exists_square_takagi X hX
  let Q := Uᴴᵀ
  have hQt : Qᵀ = Uᴴ := by simp [Q]
  have hQa : Qᴴ = Uᵀ := by
    ext i j
    simp [Q, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hUQ : Uᵀ * Q = 1 := by
    have h := congrArg Matrix.transpose hU
    simpa only [Matrix.transpose_mul, Matrix.transpose_one, Q] using h
  have hQU : Q * Uᵀ = 1 := mul_eq_one_comm.mp hUQ
  let A := B * Q
  refine ⟨A, a, ?_, ha, ?_⟩
  · calc
      ρ = B * Bᴴ := hB.symm
      _ = B * (Q * Uᵀ) * Bᴴ := by rw [hQU]; simp
      _ = A * Aᴴ := by
        simp only [A, Matrix.conjTranspose_mul, hQa, Matrix.mul_assoc]
  · calc
      Aᵀ * S * A = Uᴴ * X * Q := by
        simp only [A, X, Matrix.transpose_mul, hQt, Matrix.mul_assoc]
      _ = Uᴴ * (U * Matrix.diagonal (fun i => (a i : ℂ)) * Uᵀ) * Q := by
        rw [hfactor]
      _ = Matrix.diagonal (fun i => (a i : ℂ)) := by
        calc
          _ = (Uᴴ * U) * Matrix.diagonal (fun i => (a i : ℂ)) * (Uᵀ * Q) := by
            simp only [Matrix.mul_assoc]
          _ = _ := by rw [hU, hUQ]; simp

end ThreeCopyQutritWerner
