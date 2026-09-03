import FormalResearch.QID.D5WeylEnumeration
import FormalResearch.QID.D5ActiveAffineCertificate

namespace FormalResearch.QID

/-- Complete finite certificate for the exceptional D5 supporting facet used in
the Type-D Weyl-convexity project: all 1920 Type-D5 Weyl vertices have score
at most five, the bound is attained, exactly 68 vertices are active, and 25
explicit active vertices contain 24 independent affine differences. -/
theorem D5_complete_facet_certificate :
    supportUpperCheck = true ∧
    signedPermutationScore (Equiv.refl Fin5) supportWitnessSigns = 5 ∧
    allD5.card = 1920 ∧
    activeD5.card = 68 ∧
    ((∀ k : Fin25V, selectedD5Valid k ∧ selectedD5Score k = 5) ∧
      selectedD5Diff24Mod3 * selectedD5Diff24InvMod3 = 1) := by
  exact ⟨supportUpperCheck_passes, supportWitness_score, allD5_card,
    activeD5_card, D5_active_affine_certificate⟩

end FormalResearch.QID
