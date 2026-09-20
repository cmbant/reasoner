import FormalResearch.QIC.Endpoint14EliminationCertificateBase

namespace FormalResearch.QIC

def endpointElimUpper28Small : Matrix Fin14 Fin14 ℚ :=
  endpointElimLower28Small * endpointElimPermGeneric.permMatrix ℚ *
    endpointReducedAtRat (-5)

lemma endpointElimLower28_tri :
    endpointElimLower28Small.IsLowerTriangular := by
  native_decide

lemma endpointElimLower28_diag :
    (∏ i : Fin14, endpointElimLower28Small i i) = 1 := by
  native_decide

lemma endpointElimPerm28_sign :
    Equiv.Perm.sign endpointElimPermGeneric = -1 := by
  native_decide

lemma endpointElimUpper28_tri :
    endpointElimUpper28Small.IsUpperTriangular := by
  native_decide

lemma endpointElimUpper28_diag :
    (∏ i : Fin14, endpointElimUpper28Small i i) =
      -(expectedReducedEndpointDet (-5) : ℚ) := by
  native_decide

lemma endpointElim_certificate28_single :
    endpointElimCertificateAt (28 : EndpointSampleIndex) := by
  change endpointElimLower28Small.IsLowerTriangular ∧
    (∏ i : Fin14, endpointElimLower28Small i i) = 1 ∧
    Equiv.Perm.sign endpointElimPermGeneric = -1 ∧
    endpointElimUpper28Small.IsUpperTriangular ∧
    (∏ i : Fin14, endpointElimUpper28Small i i) =
      -(expectedReducedEndpointDet (-5) : ℚ)
  exact ⟨endpointElimLower28_tri, endpointElimLower28_diag,
    endpointElimPerm28_sign, endpointElimUpper28_tri, endpointElimUpper28_diag⟩

end FormalResearch.QIC
