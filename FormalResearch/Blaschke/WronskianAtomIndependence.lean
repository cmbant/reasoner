import Mathlib
import FormalResearch.Blaschke.WalshWronskianKernelBasis

namespace FormalResearch.Blaschke

open Polynomial Complex
open scoped BigOperators

/-- Finite polynomial families are linearly independent if evaluation at a
corresponding family of points gives a diagonal matrix with nonzero diagonal. -/
theorem polynomialFamily_linearIndependent_of_diagonal_eval
    {n : Nat} (p : Fin n → ℂ[X]) (x : Fin n → ℂ)
    (hoff : ∀ i j, i ≠ j → eval (x j) (p i) = 0)
    (hdiag : ∀ j, eval (x j) (p j) ≠ 0) :
    LinearIndependent ℂ p := by
  rw [Fintype.linearIndependent_iff]
  intro a ha j
  have heval :
      (∑ i : Fin n, a i * eval (x j) (p i)) = 0 := by
    have h := congrArg (eval (x j)) ha
    simpa using h
  have hj : a j * eval (x j) (p j) = 0 := by
    calc
      a j * eval (x j) (p j) =
          ∑ i : Fin n, a i * eval (x j) (p i) := by
        symm
        apply Finset.sum_eq_single j
        · intro i hi hij
          rw [hoff i j hij, mul_zero]
        · simp
      _ = 0 := heval
  exact (mul_eq_zero.mp hj).resolve_right (hdiag j)

/-- A complex-linearly independent polynomial family is also independent over
`ℚ` after restricting scalars. -/
theorem polynomialFamily_linearIndependentQ_of_diagonal_eval
    {n : Nat} (p : Fin n → ℂ[X]) (x : Fin n → ℂ)
    (hoff : ∀ i j, i ≠ j → eval (x j) (p i) = 0)
    (hdiag : ∀ j, eval (x j) (p j) ≠ 0) :
    LinearIndependent ℚ p := by
  exact (polynomialFamily_linearIndependent_of_diagonal_eval p x hoff hdiag).restrict_scalars
    (smul_left_injective ℚ one_ne_zero)

/-- Evaluating the `i`th Wronskian atom at a different zero `c j` gives zero:
the atom contains the factor `X-c j`. -/
theorem blaschkeWronskianAtom_eval_offdiag {n : Nat} (c : Fin n → ℂ)
    {i j : Fin n} (hij : i ≠ j) :
    eval (c j) (blaschkeWronskianAtom c i) = 0 := by
  unfold blaschkeWronskianAtom
  rw [eval_mul, eval_C]
  have hpair :
      eval (c j)
        (allPairProduct (Finset.univ.erase i)
          (fun k => blaschkeA (c k)) (fun k => blaschkeB (c k))) = 0 := by
    unfold allPairProduct
    rw [eval_prod]
    apply Finset.prod_eq_zero (by simp [hij])
    simp [blaschkeA]
  rw [hpair, mul_zero]

/-- Therefore atom independence is reduced to the scalar diagonal condition
that each atom remains nonzero when evaluated at its own zero. -/
theorem blaschkeWronskianAtom_linearIndependent_of_diag_eval_ne_zero
    {n : Nat} (c : Fin n → ℂ)
    (hdiag : ∀ j, eval (c j) (blaschkeWronskianAtom c j) ≠ 0) :
    LinearIndependent ℚ (blaschkeWronskianAtom c) := by
  exact polynomialFamily_linearIndependentQ_of_diagonal_eval
    (blaschkeWronskianAtom c) c
    (fun i j hij => blaschkeWronskianAtom_eval_offdiag c hij) hdiag

/-- Under the diagonal nonvanishing condition, the exact Walsh-kernel theorem
is unconditional: the kernel is precisely the span of all nonsingleton Walsh
modes. -/
theorem zeroFlipWronskianLin_kernel_eq_nonSingletonWalshSpan_of_diag_eval
    {n : Nat} (c : Fin n → ℂ)
    (hdiag : ∀ j, eval (c j) (blaschkeWronskianAtom c j) ≠ 0) :
    LinearMap.ker (zeroFlipWronskianLin c) = nonSingletonWalshSpan n := by
  exact zeroFlipWronskianLin_kernel_eq_nonSingletonWalshSpan c
    (blaschkeWronskianAtom_linearIndependent_of_diag_eval_ne_zero c hdiag)

end FormalResearch.Blaschke
