import FormalResearch.QIC.Endpoint14EliminationCertificateBase

namespace FormalResearch.QIC

lemma endpointElimLower24_tri :
    (endpointElimLower (24 : EndpointSampleIndex)).IsLowerTriangular := by
  native_decide

lemma endpointElimLower24_diag :
    (∏ i : Fin14, endpointElimLower (24 : EndpointSampleIndex) i i) = 1 := by
  native_decide

lemma endpointElimPerm24_sign :
    Equiv.Perm.sign (endpointElimPerm (24 : EndpointSampleIndex)) = -1 := by
  native_decide

lemma endpointElimUpper24_tri :
    (endpointElimUpper (24 : EndpointSampleIndex)).IsUpperTriangular := by
  native_decide

lemma endpointElimUpper24_diag :
    (∏ i : Fin14, endpointElimUpper (24 : EndpointSampleIndex) i i) =
      -(expectedReducedEndpointDet (endpointSample (24 : EndpointSampleIndex)) : ℚ) := by
  native_decide

lemma endpointElim_certificate24_single :
    endpointElimCertificateAt (24 : EndpointSampleIndex) := by
  exact ⟨endpointElimLower24_tri, endpointElimLower24_diag,
    endpointElimPerm24_sign, endpointElimUpper24_tri, endpointElimUpper24_diag⟩

end FormalResearch.QIC
