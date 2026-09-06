import FormalResearch.QIC.Endpoint14EliminationCertificateBase

namespace FormalResearch.QIC

lemma endpointElimLower25_tri :
    (endpointElimLower (25 : EndpointSampleIndex)).IsLowerTriangular := by
  native_decide

lemma endpointElimLower25_diag :
    (∏ i : Fin14, endpointElimLower (25 : EndpointSampleIndex) i i) = 1 := by
  native_decide

lemma endpointElimPerm25_sign :
    Equiv.Perm.sign (endpointElimPerm (25 : EndpointSampleIndex)) = -1 := by
  native_decide

lemma endpointElimUpper25_tri :
    (endpointElimUpper (25 : EndpointSampleIndex)).IsUpperTriangular := by
  native_decide

lemma endpointElimUpper25_diag :
    (∏ i : Fin14, endpointElimUpper (25 : EndpointSampleIndex) i i) =
      -(expectedReducedEndpointDet (endpointSample (25 : EndpointSampleIndex)) : ℚ) := by
  native_decide

lemma endpointElim_certificate25_single :
    endpointElimCertificateAt (25 : EndpointSampleIndex) := by
  exact ⟨endpointElimLower25_tri, endpointElimLower25_diag,
    endpointElimPerm25_sign, endpointElimUpper25_tri, endpointElimUpper25_diag⟩

end FormalResearch.QIC
