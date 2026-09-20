import Mathlib

namespace FormalResearch.Gaudin

/-- Finite truncation of the universal Bernoulli--Chebyshev path matrix
`C_{rj} = binom(r, 2(r-j)+1)`, using zero-based Lean indices. -/
def bernoulliPathMatrix (N : Nat) : Matrix (Fin N) (Fin N) Int :=
  fun r j =>
    if j.val ≤ r.val then
      (Nat.choose (r.val + 1) (2 * (r.val - j.val) + 1) : Int)
    else 0

/-- Entries above the diagonal vanish. -/
theorem bernoulliPathMatrix_lower (N : Nat) :
    (bernoulliPathMatrix N).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  have hv : i.val < j.val := hij
  simp [bernoulliPathMatrix, Nat.not_le_of_lt hv]

/-- The one-indexed diagonal is `1,2,...,N`. -/
theorem bernoulliPathMatrix_diag (N : Nat) (i : Fin N) :
    bernoulliPathMatrix N i i = (i.val + 1 : Int) := by
  simp [bernoulliPathMatrix, Nat.choose_one_right]

/-- Exact determinant of every finite truncation of the universal path matrix. -/
theorem bernoulliPathMatrix_det (N : Nat) :
    (bernoulliPathMatrix N).det =
      ∏ i : Fin N, (i.val + 1 : Int) := by
  rw [Matrix.det_of_isLowerTriangular _ (bernoulliPathMatrix_lower N)]
  apply Finset.prod_congr rfl
  intro i hi
  exact bernoulliPathMatrix_diag N i

/-- Every finite truncation is nonsingular over the integers (and hence over
`Q`), providing the finite algebraic foundation for the inverse recurrence. -/
theorem bernoulliPathMatrix_det_ne_zero (N : Nat) :
    (bernoulliPathMatrix N).det ≠ 0 := by
  rw [bernoulliPathMatrix_det]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact_mod_cast Nat.succ_ne_zero i.val

end FormalResearch.Gaudin
