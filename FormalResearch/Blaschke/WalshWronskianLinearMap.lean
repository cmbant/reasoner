import Mathlib
import FormalResearch.Blaschke.ZeroFlipWronskian

namespace FormalResearch.Blaschke

open Polynomial
open scoped BigOperators

/-- The zero-flip Wronskian transform as an actual linear map from functions on
the Boolean cube to polynomials. -/
def zeroFlipWronskianLin {n : Nat} (c : Fin n → ℂ) :
    (Finset (Fin n) → ℚ) →ₗ[ℚ] ℂ[X] :=
  Fintype.linearCombination ℚ (fun S => blaschkeZeroFlipWronskian c S)

/-- Coefficient vector of a Boolean Walsh character in the zero-flip basis. -/
def walshVector {n : Nat} (T : Finset (Fin n)) : Finset (Fin n) → ℚ :=
  fun S => walshCharacter T S

/-- Every Walsh vector of level at least two is literally in the kernel of the
linear Wronskian transform. -/
theorem walshVector_mem_zeroFlipWronskian_kernel {n : Nat} (c : Fin n → ℂ)
    (T : Finset (Fin n)) (hT : 1 < T.card) :
    walshVector T ∈ LinearMap.ker (zeroFlipWronskianLin c) := by
  rw [LinearMap.mem_ker]
  simp only [zeroFlipWronskianLin, Fintype.linearCombination_apply, walshVector]
  exact blaschke_walsh_wronskian_collapse c T hT

/-- The fixed `n` polynomial atoms which contain the entire image of the
zero-flip Wronskian transform. -/
def blaschkeWronskianAtomSpan {n : Nat} (c : Fin n → ℂ) : Submodule ℚ ℂ[X] :=
  Submodule.span ℚ (Set.range (blaschkeWronskianAtom c))

/-- Every zero-flip Wronskian lies in the span of the `n` fixed atoms. -/
theorem blaschkeZeroFlipWronskian_mem_atomSpan {n : Nat} (c : Fin n → ℂ)
    (S : Finset (Fin n)) :
    blaschkeZeroFlipWronskian c S ∈ blaschkeWronskianAtomSpan c := by
  rw [blaschkeZeroFlipWronskian_expansion]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self j))

/-- Consequently the range of the Wronskian transform is contained in the
`n`-atom span. -/
theorem zeroFlipWronskianLin_range_le_atomSpan {n : Nat} (c : Fin n → ℂ) :
    LinearMap.range (zeroFlipWronskianLin c) ≤ blaschkeWronskianAtomSpan c := by
  rintro y ⟨a, rfl⟩
  simp only [zeroFlipWronskianLin, Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro S hS
  exact Submodule.smul_mem _ _ (blaschkeZeroFlipWronskian_mem_atomSpan c S)

/-- Structural rank bound: regardless of the zeros, the polynomial-valued
Wronskian transform has rank at most the number `n` of Blaschke factors. -/
theorem zeroFlipWronskianLin_range_finrank_le {n : Nat} (c : Fin n → ℂ) :
    Module.finrank ℚ (LinearMap.range (zeroFlipWronskianLin c)) ≤ n := by
  calc
    Module.finrank ℚ (LinearMap.range (zeroFlipWronskianLin c)) ≤
        Module.finrank ℚ (blaschkeWronskianAtomSpan c) :=
      Submodule.finrank_mono (zeroFlipWronskianLin_range_le_atomSpan c)
    _ = (Set.range (blaschkeWronskianAtom c)).finrank ℚ := rfl
    _ ≤ Fintype.card (Fin n) := finrank_range_le_card (blaschkeWronskianAtom c)
    _ = n := Fintype.card_fin n

/-- Quantitative Walsh--Wronskian kernel bound.  The Boolean cube has dimension
`2^n`, while the Wronskian image has rank at most `n`; hence the kernel has
codimension at most `n`. -/
theorem zeroFlipWronskianLin_kernel_finrank_lower {n : Nat} (c : Fin n → ℂ) :
    2^n - n ≤ Module.finrank ℚ (LinearMap.ker (zeroFlipWronskianLin c)) := by
  have hnull := (zeroFlipWronskianLin c).finrank_range_add_finrank_ker
  have hrange := zeroFlipWronskianLin_range_finrank_le c
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_finset,
    Fintype.card_fin] at hnull
  omega

end FormalResearch.Blaschke
