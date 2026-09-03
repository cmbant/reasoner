import Mathlib
import FormalResearch.QID.D5RankWitness

namespace FormalResearch.QID

abbrev Fin5 := Fin 5

def negCount (s : Fin5 → Bool) : Nat :=
  ∑ i : Fin5, if s i then 1 else 0

/-- `true` denotes a negative row sign. Type D means an even number of negatives. -/
def evenSign (s : Fin5 → Bool) : Prop := negCount s % 2 = 0

def signedPermutationScore (σ : Equiv.Perm Fin5) (s : Fin5 → Bool) : Int :=
  ∑ i : Fin5, if s i then -N5 i (σ i) else N5 i (σ i)

/-- Exact support upper bound for the displayed D5 normal, by exhaustive finite computation. -/
theorem N5_support_upper :
    ∀ (σ : Equiv.Perm Fin5) (s : Fin5 → Bool),
      evenSign s → signedPermutationScore σ s ≤ 5 := by
  native_decide

def supportWitnessSigns : Fin5 → Bool :=
  ![false, true, true, false, false]

theorem supportWitness_even : evenSign supportWitnessSigns := by
  native_decide

theorem supportWitness_score :
    signedPermutationScore (Equiv.refl Fin5) supportWitnessSigns = 5 := by
  native_decide

/-- The exact Type-D5 support statement, with an explicit attaining signed permutation. -/
theorem N5_support_exact :
    (∀ (σ : Equiv.Perm Fin5) (s : Fin5 → Bool),
        evenSign s → signedPermutationScore σ s ≤ 5) ∧
    (∃ (σ : Equiv.Perm Fin5) (s : Fin5 → Bool),
        evenSign s ∧ signedPermutationScore σ s = 5) := by
  refine ⟨N5_support_upper, ?_⟩
  exact ⟨Equiv.refl Fin5, supportWitnessSigns, supportWitness_even, supportWitness_score⟩

def activeD5 : Finset (Equiv.Perm Fin5 × (Fin5 → Bool)) :=
  Finset.univ.filter (fun ps => evenSign ps.2 ∧ signedPermutationScore ps.1 ps.2 = 5)

/-- The handoff reports 68 active Type-D5 signed permutations; this checks that count exactly. -/
theorem activeD5_card : activeD5.card = 68 := by
  native_decide

end FormalResearch.QID
