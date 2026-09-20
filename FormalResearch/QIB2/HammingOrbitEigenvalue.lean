import Mathlib
import FormalResearch.QIB2.KrawtchoukEigenvalue

namespace FormalResearch.QIB2

open scoped BigOperators

/-- Sum of a constant over the k-subsets of an n-element coordinate block. -/
lemma sum_powersetCard_const (n k : Nat) (c : Int) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, c) =
      (n.choose k : Int) * c := by
  simp [nsmul_eq_mul]

/-- The signed radius-r Hamming orbit count after splitting the d coordinates
into an m-coordinate `-1` character block and a `(d-m)`-coordinate `+1`
block.  A choice of `l` flipped coordinates in the negative block contributes
sign `(-1)^l`; the two inner sums enumerate the actual subsets. -/
def signedHammingOrbitCount (d m r : Nat) : Int :=
  ∑ l ∈ Finset.range (r + 1),
    ∑ A ∈ (Finset.univ : Finset (Fin m)).powersetCard l,
      ∑ B ∈ (Finset.univ : Finset (Fin (d - m))).powersetCard (r - l),
        (-1 : Int) ^ A.card

/-- The signed Hamming orbit count is exactly the binary Krawtchouk eigenvalue.
This is the finite counting statement behind the Bose--Mesner action on a
Walsh character of weight m. -/
theorem signedHammingOrbitCount_eq_binaryKrawtchouk (d m r : Nat) :
    signedHammingOrbitCount d m r = binaryKrawtchouk d m r := by
  unfold signedHammingOrbitCount binaryKrawtchouk
  apply Finset.sum_congr rfl
  intro l hl
  calc
    (∑ A ∈ (Finset.univ : Finset (Fin m)).powersetCard l,
        ∑ B ∈ (Finset.univ : Finset (Fin (d - m))).powersetCard (r - l),
          (-1 : Int) ^ A.card) =
      ∑ A ∈ (Finset.univ : Finset (Fin m)).powersetCard l,
        ((d - m).choose (r - l) : Int) * (-1 : Int) ^ A.card := by
          apply Finset.sum_congr rfl
          intro A hA
          rw [sum_powersetCard_const]
    _ = ∑ A ∈ (Finset.univ : Finset (Fin m)).powersetCard l,
        ((d - m).choose (r - l) : Int) * (-1 : Int) ^ l := by
          apply Finset.sum_congr rfl
          intro A hA
          have hcard : A.card = l := (Finset.mem_powersetCard.mp hA).2
          rw [hcard]
    _ = (m.choose l : Int) *
        (((d - m).choose (r - l) : Int) * (-1 : Int) ^ l) := by
          rw [sum_powersetCard_const]
    _ = (-1 : Int) ^ l * (m.choose l : Int) *
        ((d - m).choose (r - l) : Int) := by ring

end FormalResearch.QIB2
