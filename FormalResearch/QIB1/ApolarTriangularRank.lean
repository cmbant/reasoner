import Mathlib
import FormalResearch.QIB1.ApolarPivot

namespace FormalResearch.QIB1

/-- Square submatrix of `D_F = 3 ∂ₓ²∂ᵧ - ∂ᵧ³`, obtained by selecting input
monomials of `y`-degree `1,...,d-2` and all output monomials.  The diagonal is
the positive `3 ∂ₓ²∂ᵧ` pivot; the `-∂ᵧ³` term sits two columns above it. -/
def apolarSquare (d : Nat) : Matrix (Fin (d - 2)) (Fin (d - 2)) Int :=
  fun r c =>
    if r = c then (apolarPivot d c.val : Int)
    else if r.val + 2 = c.val then -((c.val + 1 : Int) * c.val * (c.val - 1))
    else 0

/-- The selected apolar matrix is upper triangular. -/
theorem apolarSquare_upper (d : Nat) : (apolarSquare d).IsUpperTriangular := by
  intro i j hij
  simp only [apolarSquare]
  have hne : i ≠ j := by
    intro h
    subst j
    exact (lt_irrefl i) hij
  rw [if_neg hne]
  have hijv : j.val < i.val := hij
  have h2 : i.val + 2 ≠ j.val := by omega
  rw [if_neg h2]

/-- Its diagonal entries are exactly the pivots isolated in `ApolarPivot.lean`. -/
theorem apolarSquare_diag (d : Nat) (i : Fin (d - 2)) :
    apolarSquare d i i = (apolarPivot d i.val : Int) := by
  simp [apolarSquare]

/-- For every `d≥3`, every diagonal entry in the selected square matrix is
strictly positive. -/
theorem apolarSquare_diag_pos {d : Nat} (hd : 3 ≤ d) (i : Fin (d - 2)) :
    0 < apolarSquare d i i := by
  rw [apolarSquare_diag]
  have hi : i.val + 3 ≤ d := by omega
  exact_mod_cast apolarPivot_pos hi

/-- Exact all-degree determinant certificate: the selected `(d-2)×(d-2)`
minor has positive determinant, hence is nonzero.  This is the finite linear
algebra core of the statement that `D_F` has full row rank. -/
theorem apolarSquare_det_pos {d : Nat} (hd : 3 ≤ d) :
    0 < (apolarSquare d).det := by
  rw [Matrix.det_of_isUpperTriangular (apolarSquare_upper d)]
  exact Finset.prod_pos fun i _ => apolarSquare_diag_pos hd i

/-- In particular the canonical apolar square minor never vanishes. -/
theorem apolarSquare_det_ne_zero {d : Nat} (hd : 3 ≤ d) :
    (apolarSquare d).det ≠ 0 := ne_of_gt (apolarSquare_det_pos hd)

end FormalResearch.QIB1
