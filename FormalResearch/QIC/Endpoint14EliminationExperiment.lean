import Mathlib
import FormalResearch.QIC.Endpoint14ReducedData

namespace FormalResearch.QIC

open Matrix Equiv.Perm

def endpointElimPerm3To : Fin14 → Fin14 :=
  ![1, 12, 2, 3, 4, 5, 6, 7, 8, 10, 9, 11, 0, 13]

def endpointElimPerm3Inv : Fin14 → Fin14 :=
  ![12, 0, 2, 3, 4, 5, 6, 7, 8, 10, 9, 11, 1, 13]

def endpointElimPerm3 : Equiv.Perm Fin14 where
  toFun := endpointElimPerm3To
  invFun := endpointElimPerm3Inv
  left_inv := by native_decide
  right_inv := by native_decide

def endpointElimLower3 : Matrix Fin14 Fin14 ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, ((-4) / 3 : ℚ), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, ((-2) / 3 : ℚ), 3, ((-5) / 6 : ℚ), 1, 0, 0, 0, 0, 0, 0, 0, 0;
    (5 / 2 : ℚ), 0, ((-5) / 3 : ℚ), (15 / 2 : ℚ), ((-29) / 12 : ℚ), (5 / 2 : ℚ), 1, 0, 0, 0, 0, 0, 0, 0;
    (24 / 121 : ℚ), 0, ((-16) / 121 : ℚ), (72 / 121 : ℚ), (122 / 121 : ℚ), (24 / 121 : ℚ), ((-184) / 121 : ℚ), 1, 0, 0, 0, 0, 0, 0;
    0, 0, ((-11) / 3 : ℚ), (-10), ((-587) / 24 : ℚ), (-5), (161 / 4 : ℚ), ((-405) / 16 : ℚ), 1, 0, 0, 0, 0, 0;
    0, 0, ((-4) / 25 : ℚ), (6 / 5 : ℚ), (4 / 25 : ℚ), (3 / 5 : ℚ), (3 / 25 : ℚ), (3 / 5 : ℚ), ((-33) / 25 : ℚ), 1, 0, 0, 0, 0;
    0, 0, (6 / 5 : ℚ), 0, ((-6) / 5 : ℚ), 0, (8 / 5 : ℚ), (-1), ((-8) / 5 : ℚ), 0, 1, 0, 0, 0;
    2, 0, (2095 / 84 : ℚ), 3, ((-508) / 21 : ℚ), (9 / 2 : ℚ), (703 / 21 : ℚ), ((-1453) / 84 : ℚ), ((-1721) / 42 : ℚ), (7 / 2 : ℚ), (3473 / 168 : ℚ), 1, 0, 0;
    ((-27) / 52 : ℚ), 0, ((-1505) / 416 : ℚ), ((-81) / 104 : ℚ), (89 / 26 : ℚ), ((-243) / 208 : ℚ), ((-265) / 104 : ℚ), (531 / 416 : ℚ), (935 / 208 : ℚ), (19 / 208 : ℚ), ((-1791) / 832 : ℚ), ((-27) / 104 : ℚ), 1, 0;
    (575 / 599 : ℚ), (-1), ((-9901) / 12579 : ℚ), (563 / 599 : ℚ), (9712 / 12579 : ℚ), ((-653) / 599 : ℚ), (3916 / 12579 : ℚ), (1425 / 8386 : ℚ), ((-2026) / 12579 : ℚ), ((-1385) / 1797 : ℚ), ((-996) / 4193 : ℚ), (575 / 1198 : ℚ), ((-1259) / 1797 : ℚ), 1]

def endpointElimUpper3 : Matrix Fin14 Fin14 ℚ :=
  endpointElimLower3 * endpointElimPerm3.permMatrix ℚ * endpointReducedAtRat 3

lemma endpointElimLower3_tri : endpointElimLower3.IsLowerTriangular := by
  native_decide

lemma endpointElimLower3_det : Matrix.det endpointElimLower3 = 1 := by
  rw [Matrix.det_of_isLowerTriangular endpointElimLower3_tri]
  native_decide

lemma endpointElimPerm3_sign : Equiv.Perm.sign endpointElimPerm3 = -1 := by
  native_decide

lemma endpointElimUpper3_tri : endpointElimUpper3.IsUpperTriangular := by
  native_decide

lemma endpointElimUpper3_det :
    Matrix.det endpointElimUpper3 = -(expectedReducedEndpointDet 3 : ℚ) := by
  rw [Matrix.det_of_isUpperTriangular endpointElimUpper3_tri]
  native_decide

theorem endpointReduced_det_at_three :
    Matrix.det (endpointReducedAt 3) = expectedReducedEndpointDet 3 := by
  have hmap :
      Matrix.det (endpointReducedAtRat 3) =
        (Matrix.det (endpointReducedAt 3) : ℚ) := by
    simpa [endpointReducedAtRat] using
      (RingHom.map_det (Int.castRingHom ℚ) (endpointReducedAt 3))
  have hmul :
      Matrix.det endpointElimUpper3 =
        Matrix.det endpointElimLower3 *
          Matrix.det (endpointElimPerm3.permMatrix ℚ) *
            Matrix.det (endpointReducedAtRat 3) := by
    simp [endpointElimUpper3, Matrix.det_mul, mul_assoc]
  rw [endpointElimUpper3_det, endpointElimLower3_det,
      Matrix.det_permutation, endpointElimPerm3_sign, hmap] at hmul
  have hq : (Matrix.det (endpointReducedAt 3) : ℚ) =
      (expectedReducedEndpointDet 3 : ℚ) := by
    linarith
  exact_mod_cast hq

end FormalResearch.QIC
