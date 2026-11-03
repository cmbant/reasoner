module

public import ThreeCopyQutritWerner.TwoQubitSpinDeterminant
public import ThreeCopyQutritWerner.PositiveSpinFactor
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section


/-! Exact determinant and cyclic trace invariants of an actual spin-diagonal
Gram factor. No invertibility is assumed, so singular positive matrices are
included. The ordinary spin transpose is distinct from the ensemble adjoint. -/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
namespace ThreeCopyQutritWerner

theorem twoQubitSpinMatrix_det : twoQubitSpinMatrix.det = 1 := by
  norm_num [twoQubitSpinMatrix, Matrix.det_kronecker, twoQubitAlternating,
    Matrix.det_fin_two]

theorem twoQubitGram_det_of_spin_diagonal
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (a : Fin 2 × Fin 2 → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hA : Aᵀ * twoQubitSpinMatrix * A = Matrix.diagonal (fun i => (a i : ℂ))) :
    (A * Aᴴ).det = ((∏ i, a i : ℝ) : ℂ) := by
  have hdet : A.det ^ 2 = ((∏ i, a i : ℝ) : ℂ) := by
    have h := congrArg Matrix.det hA
    simpa [Matrix.det_mul, Matrix.det_transpose, twoQubitSpinMatrix_det,
      Matrix.det_diagonal, pow_two] using h
  have hp : 0 ≤ ∏ i, a i := Finset.prod_nonneg (fun i _ => ha i)
  have hs := congrArg Complex.normSq hdet
  simp only [map_pow, Complex.normSq_ofReal] at hs
  have hn : Complex.normSq A.det = ∏ i, a i := by
    nlinarith [Complex.normSq_nonneg A.det]
  rw [Matrix.det_mul, Matrix.det_conjTranspose]
  simpa only [Complex.star_def, Complex.mul_conj, hn]

theorem twoQubitSpin_traces_of_diagonal
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (a : Fin 2 × Fin 2 → ℝ)
    (hA : Aᵀ * twoQubitSpinMatrix * A = Matrix.diagonal (fun i => (a i : ℂ))) :
    (twoQubitSpinProduct (A * Aᴴ)).trace = ((∑ i, (a i) ^ 2 : ℝ) : ℂ) ∧
      (twoQubitSpinProduct (A * Aᴴ) * twoQubitSpinProduct (A * Aᴴ)).trace =
        ((∑ i, (a i) ^ 4 : ℝ) : ℂ) := by
  let D := Matrix.diagonal (fun i => (a i : ℂ))
  have hD : Dᴴ = D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.conjTranspose_apply, Complex.star_def]
    · simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
        hij, Ne.symm hij, Complex.star_def]
  have hAdj : Aᴴ * twoQubitSpinMatrix * Aᴴᵀ = D := by
    calc
      Aᴴ * twoQubitSpinMatrix * Aᴴᵀ = (Aᵀ * twoQubitSpinMatrix * A)ᴴ := by
        simp only [Matrix.conjTranspose_mul, twoQubitSpinMatrix_conjTranspose,
          Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose,
          Matrix.mul_assoc]
      _ = Dᴴ := congrArg Matrix.conjTranspose hA
      _ = D := hD
  let C := D * Aᵀ * twoQubitSpinMatrix
  have hM : twoQubitSpinProduct (A * Aᴴ) = A * C := by
    calc
      twoQubitSpinProduct (A * Aᴴ) =
          A * (Aᴴ * twoQubitSpinMatrix * Aᴴᵀ) * Aᵀ * twoQubitSpinMatrix := by
        simp only [twoQubitSpinProduct, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = A * C := by rw [hAdj]; simp only [C, Matrix.mul_assoc]
  have hCA : C * A = D * D := by
    calc
      C * A = D * (Aᵀ * twoQubitSpinMatrix * A) := by
        simp only [C, Matrix.mul_assoc]
      _ = D * D := by rw [hA]
  constructor
  · rw [hM, Matrix.trace_mul_comm, hCA]
    simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace, Matrix.diag_apply,
      Matrix.diagonal_apply_eq, Complex.ofReal_sum, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [hM]
    calc
      (A * C * (A * C)).trace = (A * (C * A * C)).trace := by
        simp only [Matrix.mul_assoc]
      _ = (C * A * C * A).trace := Matrix.trace_mul_comm _ _
      _ = ((C * A) * (C * A)).trace := by simp only [Matrix.mul_assoc]
      _ = ((D * D) * (D * D)).trace := by rw [hCA]
      _ = ((∑ i, (a i) ^ 4 : ℝ) : ℂ) := by
        simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace, Matrix.diag_apply,
          Matrix.diagonal_apply_eq, Complex.ofReal_sum, Complex.ofReal_pow]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- The actual PPT determinant supplies the nonnegative scalar polynomial
of the actual spin weights, with no determinant-sign surrogate assumption. -/
theorem twoQubitSpin_polynomial_nonneg_of_ppt
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (a : Fin 2 × Fin 2 → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hA : Aᵀ * twoQubitSpinMatrix * A = Matrix.diagonal (fun i => (a i : ℂ)))
    (hpt : (partialTranspose (A * Aᴴ)).PosSemidef) :
    0 ≤ (∑ i, (a i) ^ 2) ^ 2 - 2 * (∑ i, (a i) ^ 4) + 8 * ∏ i, a i := by
  obtain ⟨htr, htr2⟩ := twoQubitSpin_traces_of_diagonal A a hA
  have h := twoQubitPartialTranspose_det_identity (A * Aᴴ)
  rw [htr, htr2, twoQubitGram_det_of_spin_diagonal A a ha hA] at h
  have hcast : (((∑ i, (a i) ^ 2) ^ 2 - 2 * (∑ i, (a i) ^ 4) +
      8 * ∏ i, a i : ℝ) : ℂ) =
      (((∑ i, (a i) ^ 2 : ℝ) : ℂ)) ^ 2 -
        2 * ((∑ i, (a i) ^ 4 : ℝ) : ℂ) + 8 * ((∏ i, a i : ℝ) : ℂ) := by
    push_cast <;> ring
  rw [← hcast] at h
  have hre := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, Complex.ofReal_re] at hre
  have hnonneg := (Complex.nonneg_iff.mp hpt.det_nonneg).1
  nlinarith

end ThreeCopyQutritWerner
