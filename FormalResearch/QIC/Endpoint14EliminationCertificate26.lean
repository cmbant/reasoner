import FormalResearch.QIC.Endpoint14EliminationCertificateBase

namespace FormalResearch.QIC

lemma endpointElimLower26_tri :
    (endpointElimLower (26 : EndpointSampleIndex)).IsLowerTriangular := by
  native_decide

lemma endpointElimLower26_diag :
    (∏ i : Fin14, endpointElimLower (26 : EndpointSampleIndex) i i) = 1 := by
  native_decide

lemma endpointElimPerm26_sign :
    Equiv.Perm.sign (endpointElimPerm (26 : EndpointSampleIndex)) = -1 := by
  native_decide

lemma endpointElimUpper26_tri :
    (endpointElimUpper (26 : EndpointSampleIndex)).IsUpperTriangular := by
  native_decide

lemma endpointElimUpper26_diag :
    (∏ i : Fin14, endpointElimUpper (26 : EndpointSampleIndex) i i) =
      -(expectedReducedEndpointDet (endpointSample (26 : EndpointSampleIndex)) : ℚ) := by
  native_decide

lemma endpointElim_certificate26_single :
    endpointElimCertificateAt (26 : EndpointSampleIndex) := by
  exact ⟨endpointElimLower26_tri, endpointElimLower26_diag,
    endpointElimPerm26_sign, endpointElimUpper26_tri, endpointElimUpper26_diag⟩

end FormalResearch.QIC
