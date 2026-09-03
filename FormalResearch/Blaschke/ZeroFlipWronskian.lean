import Mathlib
import FormalResearch.Blaschke.WronskianPair
import FormalResearch.Blaschke.ProductWronskian
import FormalResearch.Blaschke.WalshBooleanCollapse

namespace FormalResearch.Blaschke

open Polynomial Complex
open scoped BigOperators

/-- The selected/complementary Blaschke-factor Wronskian for a zero-flip
pattern `S`. -/
def blaschkeZeroFlipWronskian {n : Nat} (c : Fin n → ℂ)
    (S : Finset (Fin n)) : ℂ[X] :=
  selectedProductWronskian Finset.univ S
    (fun j => blaschkeA (c j)) (fun j => blaschkeB (c j))

/-- The polynomial coefficient multiplying the Boolean sign at coordinate `j`
in the zero-flip Wronskian formula. -/
def blaschkeWronskianAtom {n : Nat} (c : Fin n → ℂ) (j : Fin n) : ℂ[X] :=
  C (1 - conj (c j) * c j) *
    allPairProduct (Finset.univ.erase j)
      (fun k => blaschkeA (c k)) (fun k => blaschkeB (c k))

/-- The local selected/complementary Wronskian is exactly the reciprocal-pair
atom with the Boolean flip sign. -/
theorem selectedLocalWronskian_blaschke {n : Nat} (c : Fin n → ℂ)
    (S : Finset (Fin n)) (j : Fin n) :
    selectedLocalWronskian S
        (fun k => blaschkeA (c k)) (fun k => blaschkeB (c k)) j =
      booleanSign S j • C (1 - conj (c j) * c j) := by
  by_cases hj : j ∈ S
  · simp [selectedLocalWronskian, selectedFactor, complementaryFactor,
      booleanSign, hj]
    rw [← blaschke_pair_wronskian (c j)]
    ring
  · simp [selectedLocalWronskian, selectedFactor, complementaryFactor,
      booleanSign, hj]
    rw [← blaschke_pair_wronskian (c j)]
    ring

/-- Exact finite zero-flip Wronskian sign formula.  The full polynomial image
is linear in the Boolean signs, with one fixed Wronskian atom per zero. -/
theorem blaschkeZeroFlipWronskian_expansion {n : Nat} (c : Fin n → ℂ)
    (S : Finset (Fin n)) :
    blaschkeZeroFlipWronskian c S =
      ∑ j : Fin n, booleanSign S j • blaschkeWronskianAtom c j := by
  unfold blaschkeZeroFlipWronskian
  rw [selectedProductWronskian_expansion]
  simp only [Finset.sum_const_zero, Finset.sum_filter, Finset.mem_univ,
    if_true, Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro j hj
  rw [selectedLocalWronskian_blaschke]
  simp [blaschkeWronskianAtom, smul_mul_assoc]

/-- Walsh--Wronskian collapse: every Boolean Walsh character of level at least
`2` lies in the kernel of the zero-flip Wronskian transform.  In particular,
all odd Walsh levels at least `3` vanish, which is the structural kernel
statement used in the Blaschke--Virasoro handoff. -/
theorem blaschke_walsh_wronskian_collapse {n : Nat} (c : Fin n → ℂ)
    (T : Finset (Fin n)) (hT : 1 < T.card) :
    (∑ S : Finset (Fin n),
      walshCharacter T S • blaschkeZeroFlipWronskian c S) = 0 := by
  simp_rw [blaschkeZeroFlipWronskian_expansion]
  exact walsh_linear_sign_collapse_smul T hT (blaschkeWronskianAtom c)

end FormalResearch.Blaschke
