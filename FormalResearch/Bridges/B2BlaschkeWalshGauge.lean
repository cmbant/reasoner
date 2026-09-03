import Mathlib
import FormalResearch.QIB2.HammingBooleanCubePhase
import FormalResearch.Blaschke.WalshBooleanCollapse

namespace FormalResearch.Bridges

open scoped BigOperators

/-- The B2 Boolean Walsh character depends only on the intersection parity of
its label and flip subset. -/
theorem qib2WalshCharacter_eq_negOne_pow_inter_card {n : Nat}
    (T S : Finset (Fin n)) :
    QIB2.booleanWalshCharacter T S =
      (-1 : ℂ) ^ (S ∩ T).card := by
  unfold QIB2.booleanWalshCharacter QIB2.booleanWalshSign
  rw [Finset.prod_ite_mem]
  simp

/-- Hence the B2 Walsh character is symmetric in its two Boolean subsets. -/
theorem qib2WalshCharacter_symm {n : Nat}
    (T S : Finset (Fin n)) :
    QIB2.booleanWalshCharacter T S = QIB2.booleanWalshCharacter S T := by
  rw [qib2WalshCharacter_eq_negOne_pow_inter_card,
    qib2WalshCharacter_eq_negOne_pow_inter_card, Finset.inter_comm]

/-- Locally, the Blaschke zero-flip sign is the negative of the B2 Walsh sign
with the subset used as the B2 label. -/
theorem blaschkeBooleanSign_cast_eq_neg_qib2WalshSign {n : Nat}
    (S : Finset (Fin n)) (j : Fin n) :
    (Blaschke.booleanSign S j : ℂ) = - QIB2.booleanWalshSign S j := by
  by_cases hj : j ∈ S <;>
    simp [Blaschke.booleanSign, QIB2.booleanWalshSign, hj]

/-- Exact gauge relation, in the orientation most directly produced by the
local sign identity: the cast Blaschke character differs from the B2 character
by the label-dependent phase `(-1)^|T|`. -/
theorem blaschkeWalshCharacter_cast_eq_gauge_mul_qib2 {n : Nat}
    (T S : Finset (Fin n)) :
    (Blaschke.walshCharacter T S : ℂ) =
      (-1 : ℂ) ^ T.card * QIB2.booleanWalshCharacter T S := by
  calc
    (Blaschke.walshCharacter T S : ℂ) =
        ∏ j ∈ T, (Blaschke.booleanSign S j : ℂ) := by
          simp [Blaschke.walshCharacter]
    _ = ∏ j ∈ T, (-QIB2.booleanWalshSign S j) := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [blaschkeBooleanSign_cast_eq_neg_qib2WalshSign]
    _ = (-1 : ℂ) ^ T.card * QIB2.booleanWalshCharacter S T := by
          simp_rw [neg_eq_neg_one_mul]
          rw [Finset.prod_mul_distrib]
          simp [QIB2.booleanWalshCharacter]
    _ = (-1 : ℂ) ^ T.card * QIB2.booleanWalshCharacter T S := by
          rw [qib2WalshCharacter_symm]

/-- Equivalent orientation: multiplying the Blaschke character by the same
self-inverse gauge recovers the B2 character. -/
theorem qib2WalshCharacter_eq_gauge_mul_blaschke_cast {n : Nat}
    (T S : Finset (Fin n)) :
    QIB2.booleanWalshCharacter T S =
      (-1 : ℂ) ^ T.card * (Blaschke.walshCharacter T S : ℂ) := by
  rw [blaschkeWalshCharacter_cast_eq_gauge_mul_qib2]
  rcases neg_one_pow_eq_or ℂ T.card with h | h
  · rw [h]
    simp
  · rw [h]
    simp

end FormalResearch.Bridges
