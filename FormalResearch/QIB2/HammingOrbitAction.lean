import Mathlib
import FormalResearch.QIB2.HammingOrbitEigenvalue

namespace FormalResearch.QIB2

open scoped BigOperators symmDiff

/-- Local ±1 Walsh sign of a Boolean subset at one coordinate. -/
def bitSign {α : Type*} [DecidableEq α] (x : Finset α) (i : α) : Int :=
  if i ∈ x then -1 else 1

lemma bitSign_symmDiff {α : Type*} [DecidableEq α]
    (x s : Finset α) (i : α) :
    bitSign (x ∆ s) i = bitSign x i * bitSign s i := by
  by_cases hx : i ∈ x <;> by_cases hs : i ∈ s <;>
    simp [bitSign, Finset.mem_symmDiff, hx, hs]

/-- Canonical weight-m Walsh character in split coordinates: all m coordinates
of the first block carry the nontrivial character, while the remaining block
is trivial. -/
def splitWalshCharacter {m n : Nat}
    (x : Finset (Fin m)) (_y : Finset (Fin n)) : Int :=
  ∏ i : Fin m, bitSign x i

lemma all_bitSign_product {m : Nat} (s : Finset (Fin m)) :
    (∏ i : Fin m, bitSign s i) = (-1 : Int) ^ s.card := by
  classical
  simp [bitSign, Finset.prod_ite, Finset.prod_const]

lemma splitWalshCharacter_symmDiff {m n : Nat}
    (x : Finset (Fin m)) (y : Finset (Fin n))
    (a : Finset (Fin m)) (b : Finset (Fin n)) :
    splitWalshCharacter (x ∆ a) (y ∆ b) =
      (-1 : Int) ^ a.card * splitWalshCharacter x y := by
  unfold splitWalshCharacter
  simp_rw [bitSign_symmDiff]
  rw [Finset.prod_mul_distrib, all_bitSign_product x, all_bitSign_product a]
  ring

/-- Radius-r Hamming/Bose--Mesner orbit operator in coordinates split into an
m-dimensional nontrivial Walsh block and a `(d-m)`-dimensional trivial block.
The `l`-sum records how many of the r flipped coordinates lie in the first
block. -/
def splitHammingOrbitApply (d m r : Nat)
    (f : Finset (Fin m) → Finset (Fin (d - m)) → Int)
    (x : Finset (Fin m)) (y : Finset (Fin (d - m))) : Int :=
  ∑ l ∈ Finset.range (r + 1),
    ∑ a ∈ (Finset.univ : Finset (Fin m)).powersetCard l,
      ∑ b ∈ (Finset.univ : Finset (Fin (d - m))).powersetCard (r - l),
        f (x ∆ a) (y ∆ b)

/-- Actual Bose--Mesner eigenaction: the canonical Walsh character of weight m
is an eigenvector of the radius-r Hamming orbit operator, with binary
Krawtchouk eigenvalue.  This promotes the signed counting identity to the
operator statement used in the three-band manuscript. -/
theorem splitHammingOrbit_walsh_eigenaction (d m r : Nat)
    (x : Finset (Fin m)) (y : Finset (Fin (d - m))) :
    splitHammingOrbitApply d m r splitWalshCharacter x y =
      binaryKrawtchouk d m r * splitWalshCharacter x y := by
  unfold splitHammingOrbitApply
  simp_rw [splitWalshCharacter_symmDiff]
  calc
    (∑ l ∈ Finset.range (r + 1),
      ∑ a ∈ (Finset.univ : Finset (Fin m)).powersetCard l,
        ∑ b ∈ (Finset.univ : Finset (Fin (d - m))).powersetCard (r - l),
          (-1 : Int) ^ a.card * splitWalshCharacter x y) =
      signedHammingOrbitCount d m r * splitWalshCharacter x y := by
        unfold signedHammingOrbitCount
        simp_rw [Finset.sum_mul]
    _ = binaryKrawtchouk d m r * splitWalshCharacter x y := by
      rw [signedHammingOrbitCount_eq_binaryKrawtchouk]

end FormalResearch.QIB2
