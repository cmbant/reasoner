import Mathlib
import FormalResearch.QID.D5RankWitness

namespace FormalResearch.QID

abbrev Fin5 := Fin 5
abbrev SignedPerm5 := Equiv.Perm Fin5 × (Fin5 → Bool)

def negCount (s : Fin5 → Bool) : Nat :=
  ∑ i : Fin5, if s i then 1 else 0

def evenSignB (s : Fin5 → Bool) : Bool := decide (negCount s % 2 = 0)

def signedPermutationScore (σ : Equiv.Perm Fin5) (s : Fin5 → Bool) : Int :=
  ∑ i : Fin5, if s i then -N5 i (σ i) else N5 i (σ i)

/-- The full finite Type-D5 Weyl enumeration: arbitrary permutation and an even number of row signs. -/
def allD5 : Finset SignedPerm5 :=
  Finset.univ.filter (fun ps => evenSignB ps.2 = true)

/-- Closed exhaustive audit that every Type-D5 Weyl score is at most five. -/
def supportUpperCheck : Bool :=
  allD5.toList.all (fun ps => decide (signedPermutationScore ps.1 ps.2 ≤ 5))

theorem supportUpperCheck_passes : supportUpperCheck = true := by
  native_decide

def supportWitnessSigns : Fin5 → Bool :=
  ![false, true, true, false, false]

theorem supportWitness_even : evenSignB supportWitnessSigns = true := by
  native_decide

theorem supportWitness_score :
    signedPermutationScore (Equiv.refl Fin5) supportWitnessSigns = 5 := by
  native_decide

/-- Active vertices of the supporting hyperplane at score five. -/
def activeD5 : Finset SignedPerm5 :=
  allD5.filter (fun ps => signedPermutationScore ps.1 ps.2 = 5)

/-- The exact enumeration contains 5! * 2^4 = 1920 Type-D5 Weyl elements. -/
theorem allD5_card : allD5.card = 1920 := by
  native_decide

/-- The handoff reports 68 active Type-D5 signed permutations; this checks that count exactly. -/
theorem activeD5_card : activeD5.card = 68 := by
  native_decide

end FormalResearch.QID
