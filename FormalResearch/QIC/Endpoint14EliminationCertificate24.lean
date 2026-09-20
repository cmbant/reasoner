import FormalResearch.QIC.Endpoint14EliminationCertificateBase

namespace FormalResearch.QIC

def endpointElimUpper24Small : Matrix Fin14 Fin14 ℚ :=
  endpointElimLower24Small * endpointElimPermGeneric.permMatrix ℚ *
    endpointReducedAtRat (-1)

lemma endpointElimLower24_tri :
    endpointElimLower24Small.IsLowerTriangular := by
  native_decide

lemma endpointElimLower24_diag :
    (∏ i : Fin14, endpointElimLower24Small i i) = 1 := by
  native_decide

lemma endpointElimPerm24_sign :
    Equiv.Perm.sign endpointElimPermGeneric = -1 := by
  native_decide

lemma endpointElimUpper24_tri :
    endpointElimUpper24Small.IsUpperTriangular := by
  native_decide

lemma endpointElimUpper24_diag :
    (∏ i : Fin14, endpointElimUpper24Small i i) =
      -(expectedReducedEndpointDet (-1) : ℚ) := by
  native_decide

lemma endpointElim_certificate24_single :
    endpointElimCertificateAt (24 : EndpointSampleIndex) := by
  change endpointElimLower24Small.IsLowerTriangular ∧
    (∏ i : Fin14, endpointElimLower24Small i i) = 1 ∧
    Equiv.Perm.sign endpointElimPermGeneric = -1 ∧
    endpointElimUpper24Small.IsUpperTriangular ∧
    (∏ i : Fin14, endpointElimUpper24Small i i) =
      -(expectedReducedEndpointDet (-1) : ℚ)
  exact ⟨endpointElimLower24_tri, endpointElimLower24_diag,
    endpointElimPerm24_sign, endpointElimUpper24_tri, endpointElimUpper24_diag⟩

end FormalResearch.QIC
