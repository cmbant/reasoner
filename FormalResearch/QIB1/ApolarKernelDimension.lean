import Mathlib
import FormalResearch.QIB1.ApolarFullRank

namespace FormalResearch.QIB1

/-- Rational form of the full apolar differential matrix.  Passing to a field
lets us state rank-nullity and kernel dimension directly. -/
def apolarFullQ (d : Nat) : Matrix (Fin (d - 2)) (Fin (d + 1)) ℚ :=
  fun r k => (apolarFull d r k : ℚ)

/-- Rational form of the canonical square pivot block. -/
def apolarSquareQ (d : Nat) : Matrix (Fin (d - 2)) (Fin (d - 2)) ℚ :=
  fun r c => (apolarSquare d r c : ℚ)

/-- The rational full matrix contains the same certified square block. -/
theorem apolarFullQ_selected (d : Nat) :
    (apolarFullQ d).submatrix id (@apolarSelectedCol d) = apolarSquareQ d := by
  ext r c
  change (apolarFull d r (apolarSelectedCol c) : ℚ) = (apolarSquare d r c : ℚ)
  exact_mod_cast congrFun (congrFun (apolarFull_selected d) r) c

/-- The rational pivot block remains upper triangular. -/
theorem apolarSquareQ_upper (d : Nat) : (apolarSquareQ d).IsUpperTriangular := by
  intro i j hij
  change (apolarSquare d i j : ℚ) = 0
  exact_mod_cast apolarSquare_upper d hij

/-- Its diagonal entries are the positive integer pivots. -/
theorem apolarSquareQ_diag (d : Nat) (i : Fin (d - 2)) :
    apolarSquareQ d i i = (apolarPivot d i.val : ℚ) := by
  exact_mod_cast apolarSquare_diag d i

/-- Hence the rational pivot determinant is strictly positive. -/
theorem apolarSquareQ_det_pos {d : Nat} (hd : 3 ≤ d) :
    0 < (apolarSquareQ d).det := by
  rw [Matrix.det_of_isUpperTriangular (apolarSquareQ d) (apolarSquareQ_upper d)]
  apply Finset.prod_pos
  intro i hi
  rw [apolarSquareQ_diag]
  exact_mod_cast apolarPivot_pos (by omega : i.val + 3 ≤ d)

/-- The actual apolar differential has maximal row rank over Q. -/
theorem apolarFullQ_rank {d : Nat} (hd : 3 ≤ d) :
    (apolarFullQ d).rank = d - 2 := by
  apply Nat.le_antisymm
  · simpa using Matrix.rank_le_card_height (apolarFullQ d)
  · have hsq : (apolarSquareQ d).rank = d - 2 := by
      rw [Matrix.rank_of_det_ne_zero (ne_of_gt (apolarSquareQ_det_pos hd)), Fintype.card_fin]
    calc
      d - 2 = (apolarSquareQ d).rank := hsq.symm
      _ = ((apolarFullQ d).submatrix id (@apolarSelectedCol d)).rank := by
        rw [apolarFullQ_selected]
      _ ≤ (apolarFullQ d).rank :=
        Matrix.rank_submatrix_le (apolarFullQ d) id (@apolarSelectedCol d)

/-- Rank-nullity now gives the manuscript's structural dimension count:
`D_F : Sym^d(Q²) → Sym^(d-3)(Q²)` has a three-dimensional kernel for every
`d≥3`.  Identifying those three dimensions with the valence powers is a
separate geometric/kernel-vector theorem. -/
theorem apolarFullQ_kernel_finrank {d : Nat} (hd : 3 ≤ d) :
    Module.finrank ℚ (LinearMap.ker (apolarFullQ d).mulVecLin) = 3 := by
  have hnull := (apolarFullQ d).mulVecLin.finrank_range_add_finrank_ker
  have hrange :
      Module.finrank ℚ (LinearMap.range (apolarFullQ d).mulVecLin) = d - 2 := by
    change (apolarFullQ d).rank = d - 2
    exact apolarFullQ_rank hd
  rw [hrange, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hnull
  omega

end FormalResearch.QIB1
