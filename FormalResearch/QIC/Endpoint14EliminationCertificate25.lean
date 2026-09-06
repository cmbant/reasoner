import FormalResearch.QIC.Endpoint14EliminationCertificateBase

namespace FormalResearch.QIC

def endpointElimUpper25Small : Matrix Fin14 Fin14 ℚ :=
  endpointElimLower25Small * endpointElimPermGeneric.permMatrix ℚ *
    endpointReducedAtRat (-2)

lemma endpointElimLower25_tri :
    endpointElimLower25Small.IsLowerTriangular := by
  native_decide

lemma endpointElimLower25_diag :
    (∏ i : Fin14, endpointElimLower25Small i i) = 1 := by
  native_decide

lemma endpointElimPerm25_sign :
    Equiv.Perm.sign endpointElimPermGeneric = -1 := by
  native_decide

lemma endpointElimUpper25_tri :
    endpointElimUpper25Small.IsUpperTriangular := by
  native_decide

lemma endpointElimUpper25_diag :
    (∏ i : Fin14, endpointElimUpper25Small i i) =
      -(expectedReducedEndpointDet (-2) : ℚ) := by
  native_decide

lemma endpointElim_certificate25_single :
    endpointElimCertificateAt (25 : EndpointSampleIndex) := by
  change endpointElimLower25Small.IsLowerTriangular ∧
    (∏ i : Fin14, endpointElimLower25Small i i) = 1 ∧
    Equiv.Perm.sign endpointElimPermGeneric = -1 ∧
    endpointElimUpper25Small.IsUpperTriangular ∧
    (∏ i : Fin14, endpointElimUpper25Small i i) =
      -(expectedReducedEndpointDet (-2) : ℚ)
  exact ⟨endpointElimLower25_tri, endpointElimLower25_diag,
    endpointElimPerm25_sign, endpointElimUpper25_tri, endpointElimUpper25_diag⟩

end FormalResearch.QIC
