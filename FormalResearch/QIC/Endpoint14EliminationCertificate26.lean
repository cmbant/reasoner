import FormalResearch.QIC.Endpoint14EliminationCertificateBase

namespace FormalResearch.QIC

def endpointElimUpper26Small : Matrix Fin14 Fin14 ℚ :=
  endpointElimLower26Small * endpointElimPermGeneric.permMatrix ℚ *
    endpointReducedAtRat (-3)

lemma endpointElimLower26_tri :
    endpointElimLower26Small.IsLowerTriangular := by
  native_decide

lemma endpointElimLower26_diag :
    (∏ i : Fin14, endpointElimLower26Small i i) = 1 := by
  native_decide

lemma endpointElimPerm26_sign :
    Equiv.Perm.sign endpointElimPermGeneric = -1 := by
  native_decide

lemma endpointElimUpper26_tri :
    endpointElimUpper26Small.IsUpperTriangular := by
  native_decide

lemma endpointElimUpper26_diag :
    (∏ i : Fin14, endpointElimUpper26Small i i) =
      -(expectedReducedEndpointDet (-3) : ℚ) := by
  native_decide

lemma endpointElim_certificate26_single :
    endpointElimCertificateAt (26 : EndpointSampleIndex) := by
  change endpointElimLower26Small.IsLowerTriangular ∧
    (∏ i : Fin14, endpointElimLower26Small i i) = 1 ∧
    Equiv.Perm.sign endpointElimPermGeneric = -1 ∧
    endpointElimUpper26Small.IsUpperTriangular ∧
    (∏ i : Fin14, endpointElimUpper26Small i i) =
      -(expectedReducedEndpointDet (-3) : ℚ)
  exact ⟨endpointElimLower26_tri, endpointElimLower26_diag,
    endpointElimPerm26_sign, endpointElimUpper26_tri, endpointElimUpper26_diag⟩

end FormalResearch.QIC
