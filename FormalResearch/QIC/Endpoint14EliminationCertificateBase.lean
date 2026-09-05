import Mathlib
import FormalResearch.QIC.Endpoint14EliminationData

namespace FormalResearch.QIC

open Matrix Equiv.Perm

/-- The finite proposition checked at one interpolation sample.  Keeping the
statement separate lets the six certificate chunks compile independently. -/
abbrev endpointElimCertificateAt (k : EndpointSampleIndex) : Prop :=
  (endpointElimLower k).IsLowerTriangular ∧
    (∏ i : Fin14, endpointElimLower k i i) = 1 ∧
    Equiv.Perm.sign (endpointElimPerm k) = -1 ∧
    (endpointElimUpper k).IsUpperTriangular ∧
    (∏ i : Fin14, endpointElimUpper k i i) =
      -(expectedReducedEndpointDet (endpointSample k) : ℚ)

end FormalResearch.QIC
