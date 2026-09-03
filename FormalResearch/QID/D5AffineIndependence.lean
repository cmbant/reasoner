import Mathlib
import FormalResearch.QID.D5CharacteristicZeroCertificate

namespace FormalResearch.QID

/-- The 24 retained rational coordinates of one selected active Type-D5 Weyl
vertex.  Dropping the ambient `(0,0)` coordinate is the same projection used by
the determinant certificate. -/
def selectedD5ProjectedQ (k : Fin25V) : Fin24V → ℚ :=
  fun q => (selectedCoord24 (selectedD5Vertex k) q : ℚ)

/-- Relative to vertex zero, the projected difference vectors are literally
the columns of the certified 24x24 rational difference matrix. -/
theorem selectedD5ProjectedQ_succ_sub_zero (j : Fin24V) :
    selectedD5ProjectedQ j.succ - selectedD5ProjectedQ 0 =
      selectedD5Diff24Q.col j := by
  ext i
  simp [selectedD5ProjectedQ, selectedD5Diff24Q, selectedD5Diff24,
    Matrix.col_apply]

/-- The 25 selected active vertices are affinely independent after projection
to the 24 retained coordinates.  Thus the active supporting set has the full
24 affine dimensions available inside a codimension-one hyperplane. -/
theorem selectedD5ProjectedQ_affineIndependent :
    AffineIndependent ℚ selectedD5ProjectedQ := by
  rw [affineIndependent_iff_linearIndependent_vsub ℚ selectedD5ProjectedQ
    (0 : Fin25V)]
  rw [← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin25V))]
  simpa [Function.comp_def, Fin.zero_succAbove,
    selectedD5ProjectedQ_succ_sub_zero] using
      selectedD5Diff24Q_cols_linearIndependent

/-- Dimension-level geometric form of the same certificate: the affine span
of the 25 projected active vertices has vector dimension exactly 24. -/
theorem selectedD5ProjectedQ_vectorSpan_finrank :
    Module.finrank ℚ (vectorSpan ℚ (Set.range selectedD5ProjectedQ)) = 24 := by
  exact selectedD5ProjectedQ_affineIndependent.finrank_vectorSpan
    (by simp [Fin25V])

end FormalResearch.QID
