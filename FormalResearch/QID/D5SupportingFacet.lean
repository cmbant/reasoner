import Mathlib
import FormalResearch.QID.D5WeylEnumeration
import FormalResearch.QID.D5CharacteristicZeroCertificate

namespace FormalResearch.QID

/-- Proposition-level version of the exhaustive Type-D5 support audit: every
one of the 1920 even signed permutations has support score at most five. -/
theorem D5_support_upper (ps : SignedPerm5) (hps : ps ∈ allD5) :
    signedPermutationScore ps.1 ps.2 ≤ 5 := by
  native_decide

/-- The displayed signed identity permutation is an actual Type-D5 Weyl
vertex attaining the support value five. -/
theorem D5_support_witness_mem :
    (Equiv.refl Fin5, supportWitnessSigns) ∈ allD5 := by
  native_decide

/-- Hence the exact maximum of the support score on the finite D5 Weyl orbit
is five, in the order-theoretic sense needed for a supporting hyperplane. -/
theorem D5_support_is_sharp :
    (∀ ps ∈ allD5, signedPermutationScore ps.1 ps.2 ≤ 5) ∧
      ∃ ps ∈ allD5, signedPermutationScore ps.1 ps.2 = 5 := by
  refine ⟨?_, ?_⟩
  · intro ps hps
    exact D5_support_upper ps hps
  · exact ⟨(Equiv.refl Fin5, supportWitnessSigns), D5_support_witness_mem,
      supportWitness_score⟩

/-- Full proposition-level D5 facet certificate.  It combines exhaustive
support, sharp attainment, the exact active-vertex count, and 24 genuinely
independent rational active differences. -/
theorem D5_supporting_facet_proposition_certificate :
    (∀ ps ∈ allD5, signedPermutationScore ps.1 ps.2 ≤ 5) ∧
    (∃ ps ∈ allD5, signedPermutationScore ps.1 ps.2 = 5) ∧
    activeD5.card = 68 ∧
    (∀ k : Fin25V, selectedD5Valid k ∧ selectedD5Score k = 5) ∧
    LinearIndependent ℚ selectedD5Diff24Q.col := by
  refine ⟨D5_support_is_sharp.1, D5_support_is_sharp.2, activeD5_card,
    selectedD5_all_active, selectedD5Diff24Q_cols_linearIndependent⟩

end FormalResearch.QID
