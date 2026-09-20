import FormalResearch.QIC.Endpoint14EliminationCertificateBase

namespace FormalResearch.QIC

def endpointElimUpper27Small : Matrix Fin14 Fin14 ℚ :=
  endpointElimLower27Small * endpointElimPermGeneric.permMatrix ℚ *
    endpointReducedAtRat (-4)

lemma endpointElimLower27_tri :
    endpointElimLower27Small.IsLowerTriangular := by
  native_decide

lemma endpointElimLower27_diag :
    (∏ i : Fin14, endpointElimLower27Small i i) = 1 := by
  native_decide

lemma endpointElimPerm27_sign :
    Equiv.Perm.sign endpointElimPermGeneric = -1 := by
  native_decide

lemma endpointElimUpper27_tri :
    endpointElimUpper27Small.IsUpperTriangular := by
  native_decide

lemma endpointElimUpper27_diag :
    (∏ i : Fin14, endpointElimUpper27Small i i) =
      -(expectedReducedEndpointDet (-4) : ℚ) := by
  native_decide

lemma endpointElim_certificate27_single :
    endpointElimCertificateAt (27 : EndpointSampleIndex) := by
  change endpointElimLower27Small.IsLowerTriangular ∧
    (∏ i : Fin14, endpointElimLower27Small i i) = 1 ∧
    Equiv.Perm.sign endpointElimPermGeneric = -1 ∧
    endpointElimUpper27Small.IsUpperTriangular ∧
    (∏ i : Fin14, endpointElimUpper27Small i i) =
      -(expectedReducedEndpointDet (-4) : ℚ)
  exact ⟨endpointElimLower27_tri, endpointElimLower27_diag,
    endpointElimPerm27_sign, endpointElimUpper27_tri, endpointElimUpper27_diag⟩

end FormalResearch.QIC
