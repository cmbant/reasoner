module

public import ThreeCopyQutritWerner.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section


/-! Literal two-qubit spin form and its partial-transpose determinant
identity. The polynomial identity holds for every complex matrix, before
positivity or normalization. These are ingredients for PPT sufficiency;
no separability conclusion is assumed or asserted in this module. -/
noncomputable section
open scoped BigOperators Matrix Kronecker
namespace ThreeCopyQutritWerner
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def twoQubitAlternating : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The sign of both local alternating forms cancels in their tensor product. -/
def twoQubitSpinMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  twoQubitAlternating ⊗ₖ twoQubitAlternating

def twoQubitSpinProduct (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ρ * twoQubitSpinMatrix * ρᵀ * twoQubitSpinMatrix

theorem twoQubitSpinMatrix_transpose : twoQubitSpinMatrixᵀ = twoQubitSpinMatrix := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [twoQubitSpinMatrix, twoQubitAlternating, Matrix.kroneckerMap_apply]

theorem twoQubitSpinMatrix_conjTranspose : twoQubitSpinMatrixᴴ = twoQubitSpinMatrix := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [twoQubitSpinMatrix, twoQubitAlternating, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply]

theorem twoQubitSpinMatrix_mul_self : twoQubitSpinMatrix * twoQubitSpinMatrix = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [twoQubitSpinMatrix, twoQubitAlternating, Matrix.kroneckerMap_apply,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

/-- Its quadratic form is twice the determinant of the actual two-qubit
coefficient matrix, hence detects product vectors without conjugating them. -/
theorem twoQubitSpinMatrix_quadratic (v : Fin 2 × Fin 2 → ℂ) :
    (∑ i, ∑ j, v i * twoQubitSpinMatrix i j * v j) =
      2 * (Matrix.of (fun i j : Fin 2 => v (i, j))).det := by
  norm_num [twoQubitSpinMatrix, twoQubitAlternating, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- The exact degree-four polynomial uses the original partial transpose
and the actual spin product; no eigenvalue or spectral premise is supplied. -/
theorem twoQubitPartialTranspose_det_identity
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    16 * (partialTranspose ρ).det = (twoQubitSpinProduct ρ).trace ^ 2 -
      2 * (twoQubitSpinProduct ρ * twoQubitSpinProduct ρ).trace + 8 * ρ.det := by
  rw [← Matrix.det_submatrix_equiv_self finProdFinEquiv.symm (partialTranspose ρ),
    ← Matrix.det_submatrix_equiv_self finProdFinEquiv.symm ρ]
  norm_num [Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.det_fin_one, Matrix.det_fin_zero, Matrix.submatrix_apply, partialTranspose,
    twoQubitSpinProduct, twoQubitSpinMatrix, twoQubitAlternating,
    Matrix.mul_apply, Matrix.trace, Matrix.diag_apply, Matrix.transpose_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
    finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.succAbove]
  ring

end ThreeCopyQutritWerner
