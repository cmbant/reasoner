import Mathlib
import FormalResearch.QIC.Endpoint14EliminationData

namespace FormalResearch.QIC

open Matrix Equiv.Perm

/-- The interpolation sample set `0,3,4,...,30` has no repetitions. -/
lemma endpointSample_injective : Function.Injective endpointSample := by
  native_decide

/-- Closed finite verification of the exact Gaussian-elimination certificates.
The determinant itself is not evaluated here: only triangularity, unit diagonal,
permutation sign, and the diagonal product of the resulting upper matrix.
The finite sample index is split first so each native check compiles separately. -/
lemma endpointElim_certificate :
    ∀ k : EndpointSampleIndex,
      (endpointElimLower k).IsLowerTriangular ∧
      (∏ i : Fin14, endpointElimLower k i i) = 1 ∧
      Equiv.Perm.sign (endpointElimPerm k) = -1 ∧
      (endpointElimUpper k).IsUpperTriangular ∧
      (∏ i : Fin14, endpointElimUpper k i i) =
        -(expectedReducedEndpointDet (endpointSample k) : ℚ) := by
  intro k
  fin_cases k <;> native_decide

lemma endpointElimLower_det (k : EndpointSampleIndex) :
    Matrix.det (endpointElimLower k) = 1 := by
  rw [Matrix.det_of_isLowerTriangular (endpointElimLower k)
      (endpointElim_certificate k).1]
  exact (endpointElim_certificate k).2.1

lemma endpointElimPerm_sign (k : EndpointSampleIndex) :
    Equiv.Perm.sign (endpointElimPerm k) = -1 :=
  (endpointElim_certificate k).2.2.1

lemma endpointElimUpper_det (k : EndpointSampleIndex) :
    Matrix.det (endpointElimUpper k) =
      -(expectedReducedEndpointDet (endpointSample k) : ℚ) := by
  rw [Matrix.det_of_isUpperTriangular (endpointElimUpper k)
      (endpointElim_certificate k).2.2.2.1]
  exact (endpointElim_certificate k).2.2.2.2

/-- Each of the 29 reduced determinant values follows from determinant
multiplicativity and one checked triangular elimination certificate. -/
theorem endpointReduced_det_at_sample (k : EndpointSampleIndex) :
    Matrix.det (endpointReducedAt (endpointSample k)) =
      expectedReducedEndpointDet (endpointSample k) := by
  have hraw :
      (Int.castRingHom ℚ)
          (Matrix.det (endpointReducedAt (endpointSample k))) =
        Matrix.det ((Int.castRingHom ℚ).mapMatrix
          (endpointReducedAt (endpointSample k))) :=
    RingHom.map_det (Int.castRingHom ℚ)
      (endpointReducedAt (endpointSample k))
  have hmap :
      Matrix.det (endpointReducedAtRat (endpointSample k)) =
        ((Matrix.det (endpointReducedAt (endpointSample k)) : Int) : ℚ) := by
    simpa [endpointReducedAtRat] using hraw.symm
  have hmul :
      Matrix.det (endpointElimUpper k) =
        Matrix.det (endpointElimLower k) *
          Matrix.det ((endpointElimPerm k).permMatrix ℚ) *
            Matrix.det (endpointReducedAtRat (endpointSample k)) := by
    simp [endpointElimUpper, Matrix.det_mul, mul_assoc]
  rw [endpointElimUpper_det k, endpointElimLower_det k,
      Matrix.det_permutation, endpointElimPerm_sign k, hmap] at hmul
  norm_num at hmul
  exact hmul.symm

end FormalResearch.QIC
