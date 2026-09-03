import Mathlib
import FormalResearch.QID.D5SupportingFacet
import FormalResearch.QID.D5AffineIndependence

namespace FormalResearch.QID

/-- Fully geometric Type-D5 support certificate.  Besides exhaustive support,
sharp attainment, and the active-set count, the selected score-five vertices
form an affine-independent 25-point family whose affine span has vector
dimension 24. -/
theorem D5_full_geometric_facet_certificate :
    (∀ ps ∈ allD5, signedPermutationScore ps.1 ps.2 ≤ 5) ∧
    (∃ ps ∈ allD5, signedPermutationScore ps.1 ps.2 = 5) ∧
    activeD5.card = 68 ∧
    (∀ k : Fin25V, selectedD5Valid k ∧ selectedD5Score k = 5) ∧
    AffineIndependent ℚ selectedD5ProjectedQ ∧
    Module.finrank ℚ (vectorSpan ℚ (Set.range selectedD5ProjectedQ)) = 24 := by
  refine ⟨D5_support_is_sharp.1, D5_support_is_sharp.2, activeD5_card,
    selectedD5_all_active, selectedD5ProjectedQ_affineIndependent,
    selectedD5ProjectedQ_vectorSpan_finrank⟩

end FormalResearch.QID
