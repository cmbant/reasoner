import Mathlib
import FormalResearch.QIB2.HammingGate
import FormalResearch.QIB2.HammingSubsetExpansion

namespace FormalResearch.QIB2

open Complex
open scoped BigOperators

/-- The complex Walsh sign attached to a Boolean character label `T`. -/
def booleanWalshSign {d : Nat} (T : Finset (Fin d)) (i : Fin d) : ℂ :=
  if i ∈ T then -1 else 1

/-- Walsh character evaluated on a flip subset `S`. -/
def booleanWalshCharacter {d : Nat}
    (T S : Finset (Fin d)) : ℂ :=
  ∏ i ∈ S, booleanWalshSign T i

/-- The local canonical gate factor is `i` on coordinates belonging to the
Walsh label and `1` on the complementary coordinates. -/
theorem canonical_gate_boolean_local_phase {d : Nat}
    (T : Finset (Fin d)) (i : Fin d) :
    gateA + gateB * booleanWalshSign T i =
      if i ∈ T then I else 1 := by
  by_cases hi : i ∈ T
  · simpa [booleanWalshSign, hi, sub_eq_add_neg] using canonical_gate_at_minus
  · simpa [booleanWalshSign, hi] using gate_coeff_sum

/-- Product form of the full Boolean-cube phase law: an arbitrary Walsh label
`T` acquires exactly the phase `i^|T|`. -/
theorem canonical_gate_boolean_product_phase {d : Nat}
    (T : Finset (Fin d)) :
    (∏ i : Fin d, (gateA + gateB * booleanWalshSign T i)) = I ^ T.card := by
  simp_rw [canonical_gate_boolean_local_phase T]
  simp [Finset.prod_ite_mem]

/-- Full Boolean-cube spectral identity.  Expanding the canonical product gate
over all flip subsets `S` gives the Walsh eigenvalue `i^|T|` for every label
`T`, not merely for a canonical split representative of a given weight. -/
theorem canonical_gate_boolean_cube_phase {d : Nat}
    (T : Finset (Fin d)) :
    (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
      gateB ^ S.card * gateA ^ (d - S.card) * booleanWalshCharacter T S) =
      I ^ T.card := by
  simp only [booleanWalshCharacter]
  rw [← hamming_subset_expansion_fin gateA gateB (booleanWalshSign T)]
  exact canonical_gate_boolean_product_phase T

end FormalResearch.QIB2
