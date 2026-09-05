import Mathlib
import FormalResearch.QIC.Endpoint14EliminationCertificate0
import FormalResearch.QIC.Endpoint14EliminationCertificate1
import FormalResearch.QIC.Endpoint14EliminationCertificate2
import FormalResearch.QIC.Endpoint14EliminationCertificate3
import FormalResearch.QIC.Endpoint14EliminationCertificate4
import FormalResearch.QIC.Endpoint14EliminationCertificate5

namespace FormalResearch.QIC

open Matrix Equiv.Perm

/-- The interpolation sample set `0,3,4,...,30` has no repetitions. -/
lemma endpointSample_injective : Function.Injective endpointSample := by
  native_decide

/-- Assemble the six independently compiled exact elimination-certificate chunks. -/
lemma endpointElim_certificate (k : EndpointSampleIndex) :
    endpointElimCertificateAt k := by
  fin_cases k <;>
    first
    | exact endpointElim_certificate_0
    | exact endpointElim_certificate_1
    | exact endpointElim_certificate_2
    | exact endpointElim_certificate_3
    | exact endpointElim_certificate_4
    | exact endpointElim_certificate_5
    | exact endpointElim_certificate_6
    | exact endpointElim_certificate_7
    | exact endpointElim_certificate_8
    | exact endpointElim_certificate_9
    | exact endpointElim_certificate_10
    | exact endpointElim_certificate_11
    | exact endpointElim_certificate_12
    | exact endpointElim_certificate_13
    | exact endpointElim_certificate_14
    | exact endpointElim_certificate_15
    | exact endpointElim_certificate_16
    | exact endpointElim_certificate_17
    | exact endpointElim_certificate_18
    | exact endpointElim_certificate_19
    | exact endpointElim_certificate_20
    | exact endpointElim_certificate_21
    | exact endpointElim_certificate_22
    | exact endpointElim_certificate_23
    | exact endpointElim_certificate_24
    | exact endpointElim_certificate_25
    | exact endpointElim_certificate_26
    | exact endpointElim_certificate_27
    | exact endpointElim_certificate_28

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
