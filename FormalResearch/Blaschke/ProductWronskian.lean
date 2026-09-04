import Mathlib
import FormalResearch.Blaschke.WronskianPair

namespace FormalResearch.Blaschke

open Polynomial

section ProductWronskian

variable {ι : Type*} [DecidableEq ι]

/-- Choose `b_j` on the flipped set and `a_j` off it. -/
def selectedFactor (S : Finset ι) (a b : ι → ℂ[X]) (j : ι) : ℂ[X] :=
  if j ∈ S then b j else a j

/-- The complementary factor choice. -/
def complementaryFactor (S : Finset ι) (a b : ι → ℂ[X]) (j : ι) : ℂ[X] :=
  if j ∈ S then a j else b j

/-- Product for one zero-flip pattern, restricted to a finite coordinate set. -/
noncomputable def selectedProduct (I S : Finset ι) (a b : ι → ℂ[X]) : ℂ[X] :=
  ∏ j ∈ I, selectedFactor S a b j

/-- Product for the complementary zero-flip pattern. -/
noncomputable def complementaryProduct (I S : Finset ι) (a b : ι → ℂ[X]) : ℂ[X] :=
  ∏ j ∈ I, complementaryFactor S a b j

/-- Product of untouched reciprocal pairs. -/
noncomputable def allPairProduct (I : Finset ι) (a b : ι → ℂ[X]) : ℂ[X] :=
  ∏ j ∈ I, a j * b j

/-- Local selected/complementary Wronskian at one coordinate. -/
noncomputable def selectedLocalWronskian (S : Finset ι) (a b : ι → ℂ[X]) (j : ι) : ℂ[X] :=
  selectedFactor S a b j * derivative (complementaryFactor S a b j) -
    derivative (selectedFactor S a b j) * complementaryFactor S a b j

/-- Wronskian of the two complementary finite products, in the sign convention
used by the Blaschke handoff. -/
noncomputable def selectedProductWronskian (I S : Finset ι) (a b : ι → ℂ[X]) : ℂ[X] :=
  selectedProduct I S a b * derivative (complementaryProduct I S a b) -
    derivative (selectedProduct I S a b) * complementaryProduct I S a b

lemma selectedFactor_mul_complementary (S : Finset ι) (a b : ι → ℂ[X]) (j : ι) :
    selectedFactor S a b j * complementaryFactor S a b j = a j * b j := by
  by_cases hj : j ∈ S <;> simp [selectedFactor, complementaryFactor, hj, mul_comm]

/-- One-coordinate product recursion for the complementary-product Wronskian. -/
lemma selectedProductWronskian_insert (I S : Finset ι) (a b : ι → ℂ[X])
    {k : ι} (hk : k ∉ I) :
    selectedProductWronskian (insert k I) S a b =
      selectedLocalWronskian S a b k * allPairProduct I a b +
        (a k * b k) * selectedProductWronskian I S a b := by
  simp only [selectedProductWronskian, selectedProduct, complementaryProduct,
    allPairProduct, Finset.prod_insert hk, derivative_mul]
  have hkPair := selectedFactor_mul_complementary S a b k
  have hIPair :
      (∏ j ∈ I, selectedFactor S a b j) *
          (∏ j ∈ I, complementaryFactor S a b j) =
        ∏ j ∈ I, a j * b j := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    exact selectedFactor_mul_complementary S a b j
  rw [← hIPair, ← hkPair]
  unfold selectedLocalWronskian
  ring

/-- Finite product Wronskian expansion.  Each coordinate contributes its local
pair Wronskian multiplied by every untouched pair product. -/
theorem selectedProductWronskian_expansion (I S : Finset ι) (a b : ι → ℂ[X]) :
    selectedProductWronskian I S a b =
      ∑ j ∈ I, selectedLocalWronskian S a b j * allPairProduct (I.erase j) a b := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [selectedProductWronskian, selectedProduct, complementaryProduct]
  | @insert k I hk ih =>
      rw [selectedProductWronskian_insert I S a b hk, Finset.sum_insert hk]
      rw [ih]
      congr 1
      · simp [allPairProduct, hk]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hkj : k ≠ j := by
          intro h
          subst j
          exact hk hj
        rw [Finset.erase_insert_of_ne hkj]
        simp [allPairProduct, hk, mul_assoc, mul_left_comm, mul_comm]

end ProductWronskian

end FormalResearch.Blaschke
