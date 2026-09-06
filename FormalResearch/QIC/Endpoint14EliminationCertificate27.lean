import FormalResearch.QIC.Endpoint14EliminationCertificateBase

namespace FormalResearch.QIC

lemma endpointElimLower27_tri :
    (endpointElimLower (27 : EndpointSampleIndex)).IsLowerTriangular := by
  native_decide

lemma endpointElimLower27_diag :
    (∏ i : Fin14, endpointElimLower (27 : EndpointSampleIndex) i i) = 1 := by
  native_decide

lemma endpointElimPerm27_sign :
    Equiv.Perm.sign (endpointElimPerm (27 : EndpointSampleIndex)) = -1 := by
  native_decide

lemma endpointElimUpper27_tri :
    (endpointElimUpper (27 : EndpointSampleIndex)).IsUpperTriangular := by
  native_decide

lemma endpointElimUpper27_diag :
    (∏ i : Fin14, endpointElimUpper (27 : EndpointSampleIndex) i i) =
      -(expectedReducedEndpointDet (endpointSample (27 : EndpointSampleIndex)) : ℚ) := by
  native_decide

lemma endpointElim_certificate27_single :
    endpointElimCertificateAt (27 : EndpointSampleIndex) := by
  exact ⟨endpointElimLower27_tri, endpointElimLower27_diag,
    endpointElimPerm27_sign, endpointElimUpper27_tri, endpointElimUpper27_diag⟩

end FormalResearch.QIC
