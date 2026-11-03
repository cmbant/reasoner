module

public import Mathlib
public import FormalResearch.QIC.Endpoint14EliminationCertificate0
meta import FormalResearch.QIC.Endpoint14EliminationCertificate0
public import FormalResearch.QIC.Endpoint14EliminationCertificate1
meta import FormalResearch.QIC.Endpoint14EliminationCertificate1
public import FormalResearch.QIC.Endpoint14EliminationCertificate2
meta import FormalResearch.QIC.Endpoint14EliminationCertificate2
public import FormalResearch.QIC.Endpoint14EliminationCertificate3
meta import FormalResearch.QIC.Endpoint14EliminationCertificate3
public import FormalResearch.QIC.Endpoint14EliminationCertificate4
meta import FormalResearch.QIC.Endpoint14EliminationCertificate4
public import FormalResearch.QIC.Endpoint14EliminationCertificate5
meta import FormalResearch.QIC.Endpoint14EliminationCertificate5
public import FormalResearch.QIC.Endpoint14EliminationCertificate6
meta import FormalResearch.QIC.Endpoint14EliminationCertificate6
public import FormalResearch.QIC.Endpoint14EliminationCertificate7
meta import FormalResearch.QIC.Endpoint14EliminationCertificate7
public import FormalResearch.QIC.Endpoint14EliminationCertificate8
meta import FormalResearch.QIC.Endpoint14EliminationCertificate8
public import FormalResearch.QIC.Endpoint14EliminationCertificate9
meta import FormalResearch.QIC.Endpoint14EliminationCertificate9
public import FormalResearch.QIC.Endpoint14EliminationCertificate10
meta import FormalResearch.QIC.Endpoint14EliminationCertificate10
public import FormalResearch.QIC.Endpoint14EliminationCertificate11
meta import FormalResearch.QIC.Endpoint14EliminationCertificate11
public import FormalResearch.QIC.Endpoint14EliminationCertificate12
meta import FormalResearch.QIC.Endpoint14EliminationCertificate12
public import FormalResearch.QIC.Endpoint14EliminationCertificate13
meta import FormalResearch.QIC.Endpoint14EliminationCertificate13
public import FormalResearch.QIC.Endpoint14EliminationCertificate14
meta import FormalResearch.QIC.Endpoint14EliminationCertificate14
public import FormalResearch.QIC.Endpoint14EliminationCertificate15
meta import FormalResearch.QIC.Endpoint14EliminationCertificate15
public import FormalResearch.QIC.Endpoint14EliminationCertificate16
meta import FormalResearch.QIC.Endpoint14EliminationCertificate16
public import FormalResearch.QIC.Endpoint14EliminationCertificate17
meta import FormalResearch.QIC.Endpoint14EliminationCertificate17
public import FormalResearch.QIC.Endpoint14EliminationCertificate18
meta import FormalResearch.QIC.Endpoint14EliminationCertificate18
public import FormalResearch.QIC.Endpoint14EliminationCertificate19
meta import FormalResearch.QIC.Endpoint14EliminationCertificate19
public import FormalResearch.QIC.Endpoint14EliminationCertificate20
meta import FormalResearch.QIC.Endpoint14EliminationCertificate20
public import FormalResearch.QIC.Endpoint14EliminationCertificate21
meta import FormalResearch.QIC.Endpoint14EliminationCertificate21
public import FormalResearch.QIC.Endpoint14EliminationCertificate22
meta import FormalResearch.QIC.Endpoint14EliminationCertificate22
public import FormalResearch.QIC.Endpoint14EliminationCertificate23
meta import FormalResearch.QIC.Endpoint14EliminationCertificate23
public import FormalResearch.QIC.Endpoint14EliminationCertificate24
meta import FormalResearch.QIC.Endpoint14EliminationCertificate24
public import FormalResearch.QIC.Endpoint14EliminationCertificate25
meta import FormalResearch.QIC.Endpoint14EliminationCertificate25
public import FormalResearch.QIC.Endpoint14EliminationCertificate26
meta import FormalResearch.QIC.Endpoint14EliminationCertificate26
public import FormalResearch.QIC.Endpoint14EliminationCertificate27
meta import FormalResearch.QIC.Endpoint14EliminationCertificate27
public import FormalResearch.QIC.Endpoint14EliminationCertificate28
meta import FormalResearch.QIC.Endpoint14EliminationCertificate28


@[expose] public section

namespace FormalResearch.QIC

open Matrix Equiv.Perm

/-- The 29 interpolation samples have no repetitions. -/
lemma endpointSample_injective : Function.Injective endpointSample := by
  native_decide

/-- Assemble the independently compiled exact elimination certificates. -/
lemma endpointElim_certificate (k : EndpointSampleIndex) :
    endpointElimCertificateAt k := by
  fin_cases k
  · exact endpointElim_certificate_0
  · exact endpointElim_certificate_1
  · exact endpointElim_certificate_2
  · exact endpointElim_certificate_3
  · exact endpointElim_certificate_4
  · exact endpointElim_certificate_5
  · exact endpointElim_certificate_6
  · exact endpointElim_certificate_7
  · exact endpointElim_certificate_8
  · exact endpointElim_certificate_9
  · exact endpointElim_certificate_10
  · exact endpointElim_certificate_11
  · exact endpointElim_certificate_12
  · exact endpointElim_certificate_13
  · exact endpointElim_certificate_14
  · exact endpointElim_certificate_15
  · exact endpointElim_certificate_16
  · exact endpointElim_certificate_17
  · exact endpointElim_certificate_18
  · exact endpointElim_certificate_19
  · exact endpointElim_certificate20_single
  · exact endpointElim_certificate21_single
  · exact endpointElim_certificate22_single
  · exact endpointElim_certificate23_single
  · exact endpointElim_certificate24_single
  · exact endpointElim_certificate25_single
  · exact endpointElim_certificate26_single
  · exact endpointElim_certificate27_single
  · exact endpointElim_certificate28_single

lemma endpointElimLower_det (k : EndpointSampleIndex) :
    Matrix.det (endpointElimLower k) = 1 := by
  rw [Matrix.det_of_isLowerTriangular (endpointElimLower k) (endpointElim_certificate k).1]
  exact (endpointElim_certificate k).2.1

lemma endpointElimPerm_sign (k : EndpointSampleIndex) :
    Equiv.Perm.sign (endpointElimPerm k) = -1 :=
  (endpointElim_certificate k).2.2.1

lemma endpointElimUpper_det (k : EndpointSampleIndex) :
    Matrix.det (endpointElimUpper k) =
      -(expectedReducedEndpointDet (endpointSample k) : ℚ) := by
  rw [Matrix.det_of_isUpperTriangular (endpointElim_certificate k).2.2.2.1]
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
