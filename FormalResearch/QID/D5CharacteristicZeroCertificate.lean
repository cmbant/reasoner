import Mathlib
import FormalResearch.QID.D5ActiveAffineCertificate

namespace FormalResearch.QID

/-- Rational realization of the 24 active-vertex difference matrix. -/
def selectedD5Diff24Q : Matrix Fin24V Fin24V ℚ :=
  (Int.castRingHom ℚ).mapMatrix selectedD5Diff24

/-- The explicit mod-3 right inverse forces the mod-3 determinant to be
nonzero. -/
theorem selectedD5Diff24Mod3_det_ne_zero : selectedD5Diff24Mod3.det ≠ 0 := by
  intro hdet
  have h := congrArg Matrix.det selectedD5Diff24_right_inverse
  rw [Matrix.det_mul, Matrix.det_one, hdet, zero_mul] at h
  exact zero_ne_one h

/-- Therefore the original integer difference determinant is nonzero.  This
promotes the finite-field audit to characteristic-zero linear algebra. -/
theorem selectedD5Diff24_det_ne_zero : selectedD5Diff24.det ≠ 0 := by
  intro hdet
  apply selectedD5Diff24Mod3_det_ne_zero
  have hmap :
      ((Int.castRingHom (ZMod 3)).mapMatrix selectedD5Diff24).det = 0 := by
    rw [← RingHom.map_det, hdet, map_zero]
  simpa [selectedD5Diff24Mod3, Matrix.mapMatrix_apply] using hmap

/-- The rational difference matrix has nonzero determinant. -/
theorem selectedD5Diff24Q_det_ne_zero : selectedD5Diff24Q.det ≠ 0 := by
  have hcast : (selectedD5Diff24.det : ℚ) ≠ 0 := by
    exact_mod_cast selectedD5Diff24_det_ne_zero
  simpa [selectedD5Diff24Q, ← RingHom.map_det] using hcast

/-- Hence the selected active differences have full rational rank 24. -/
theorem selectedD5Diff24Q_rank : selectedD5Diff24Q.rank = 24 := by
  rw [Matrix.rank_of_det_ne_zero selectedD5Diff24Q_det_ne_zero, Fintype.card_fin]

/-- Equivalently, the 24 active-vertex difference columns are genuinely
linearly independent over `ℚ`, not merely independent modulo three. -/
theorem selectedD5Diff24Q_cols_linearIndependent :
    LinearIndependent ℚ selectedD5Diff24Q.col := by
  exact Matrix.linearIndependent_cols_of_det_ne_zero selectedD5Diff24Q_det_ne_zero

end FormalResearch.QID
