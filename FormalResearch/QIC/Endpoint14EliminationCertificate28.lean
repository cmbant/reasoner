import FormalResearch.QIC.Endpoint14EliminationCertificateBase

namespace FormalResearch.QIC

lemma endpointElimLower28_tri :
    (endpointElimLower (28 : EndpointSampleIndex)).IsLowerTriangular := by
  native_decide

lemma endpointElimLower28_diag :
    (∏ i : Fin14, endpointElimLower (28 : EndpointSampleIndex) i i) = 1 := by
  native_decide

lemma endpointElimPerm28_sign :
    Equiv.Perm.sign (endpointElimPerm (28 : EndpointSampleIndex)) = -1 := by
  native_decide

lemma endpointElimUpper28_tri :
    (endpointElimUpper (28 : EndpointSampleIndex)).IsUpperTriangular := by
  native_decide

lemma endpointElimUpper28_diag :
    (∏ i : Fin14, endpointElimUpper (28 : EndpointSampleIndex) i i) =
      -(expectedReducedEndpointDet (endpointSample (28 : EndpointSampleIndex)) : ℚ) := by
  native_decide

lemma endpointElim_certificate28_single :
    endpointElimCertificateAt (28 : EndpointSampleIndex) := by
  exact ⟨endpointElimLower28_tri, endpointElimLower28_diag,
    endpointElimPerm28_sign, endpointElimUpper28_tri, endpointElimUpper28_diag⟩

end FormalResearch.QIC
