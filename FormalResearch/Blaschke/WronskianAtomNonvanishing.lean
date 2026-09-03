import Mathlib
import FormalResearch.Blaschke.WronskianAtomIndependence

namespace FormalResearch.Blaschke

open Polynomial Complex
open scoped BigOperators

/-- The diagonal evaluation of a Wronskian atom factors into its local
Blaschke weight and the products of all distinct zero and reciprocal factors. -/
theorem blaschkeWronskianAtom_eval_diag {n : Nat} (c : Fin n → ℂ) (j : Fin n) :
    eval (c j) (blaschkeWronskianAtom c j) =
      (1 - conj (c j) * c j) *
        ∏ k ∈ Finset.univ.erase j,
          ((c j - c k) * (1 - conj (c k) * c j)) := by
  simp [blaschkeWronskianAtom, allPairProduct, eval_prod,
    blaschkeA, blaschkeB]

/-- A concrete algebraic nondegeneracy criterion for every diagonal atom
evaluation.  It separates the three possible sources of degeneration:
a boundary/self factor, repeated zeros, or a reciprocal collision. -/
theorem blaschkeWronskianAtom_diag_eval_ne_zero_of_nondegenerate
    {n : Nat} (c : Fin n → ℂ)
    (hself : ∀ j, 1 - conj (c j) * c j ≠ 0)
    (hinj : Function.Injective c)
    (hrecip : ∀ k j, k ≠ j → 1 - conj (c k) * c j ≠ 0) :
    ∀ j, eval (c j) (blaschkeWronskianAtom c j) ≠ 0 := by
  intro j
  rw [blaschkeWronskianAtom_eval_diag]
  apply mul_ne_zero (hself j)
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hkj : k ≠ j := Finset.ne_of_mem_erase hk
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro h
    exact hkj (hinj h.symm)
  · exact hrecip k j hkj

/-- Under the concrete nondegeneracy conditions, the Wronskian atoms are
linearly independent over `ℚ`. -/
theorem blaschkeWronskianAtom_linearIndependent_of_nondegenerate
    {n : Nat} (c : Fin n → ℂ)
    (hself : ∀ j, 1 - conj (c j) * c j ≠ 0)
    (hinj : Function.Injective c)
    (hrecip : ∀ k j, k ≠ j → 1 - conj (c k) * c j ≠ 0) :
    LinearIndependent ℚ (blaschkeWronskianAtom c) := by
  exact blaschkeWronskianAtom_linearIndependent_of_diag_eval_ne_zero c
    (blaschkeWronskianAtom_diag_eval_ne_zero_of_nondegenerate c hself hinj hrecip)

/-- Consequently the exact Walsh-kernel decomposition holds for every
nondegenerate finite zero configuration satisfying the three scalar
conditions above. -/
theorem zeroFlipWronskianLin_kernel_eq_nonSingletonWalshSpan_of_nondegenerate
    {n : Nat} (c : Fin n → ℂ)
    (hself : ∀ j, 1 - conj (c j) * c j ≠ 0)
    (hinj : Function.Injective c)
    (hrecip : ∀ k j, k ≠ j → 1 - conj (c k) * c j ≠ 0) :
    LinearMap.ker (zeroFlipWronskianLin c) = nonSingletonWalshSpan n := by
  exact zeroFlipWronskianLin_kernel_eq_nonSingletonWalshSpan c
    (blaschkeWronskianAtom_linearIndependent_of_nondegenerate c hself hinj hrecip)

end FormalResearch.Blaschke
