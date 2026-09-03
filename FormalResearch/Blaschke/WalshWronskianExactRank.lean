import Mathlib
import FormalResearch.Blaschke.WalshWronskianLinearMap

namespace FormalResearch.Blaschke

open Polynomial
open scoped BigOperators

/-- Every Boolean sign squares to one. -/
theorem booleanSign_mul_self {n : Nat} (S : Finset (Fin n)) (j : Fin n) :
    booleanSign S j * booleanSign S j = 1 := by
  by_cases hj : j ∈ S <;> simp [booleanSign, hj]

/-- A singleton Walsh character is its Boolean coordinate sign. -/
theorem walshCharacter_singleton {n : Nat} (S : Finset (Fin n)) (j : Fin n) :
    walshCharacter {j} S = booleanSign S j := by
  simp [walshCharacter]

/-- Exact Boolean coordinate orthogonality over the full cube. -/
theorem booleanSign_correlation {n : Nat} (j k : Fin n) :
    (∑ S : Finset (Fin n), booleanSign S j * booleanSign S k) =
      if j = k then (((2^n : Nat) : ℚ)) else 0 := by
  by_cases hjk : j = k
  · subst k
    simp_rw [booleanSign_mul_self]
    simp [hjk, Fintype.card_finset, Fintype.card_fin]
  · have h := walsh_coordinate_orthogonal ({j} : Finset (Fin n))
        (j := k) (k := j) (by simp) hjk
    simpa [walshCharacter_singleton, hjk] using h

/-- A singleton Walsh transform isolates exactly one Wronskian atom, with the
Boolean-cube normalization factor `2^n`. -/
theorem zeroFlipWronskian_singleton_walsh {n : Nat} (c : Fin n → ℂ) (j : Fin n) :
    (∑ S : Finset (Fin n),
      booleanSign S j • blaschkeZeroFlipWronskian c S) =
      (((2^n : Nat) : ℚ)) • blaschkeWronskianAtom c j := by
  simp_rw [blaschkeZeroFlipWronskian_expansion, smul_sum, smul_smul]
  rw [Fintype.sum_comm]
  apply Eq.trans (Fintype.sum_congr _ _ fun k => by
    rw [booleanSign_correlation j k])
  simp

/-- The linear Wronskian map sends the singleton Walsh vector to `2^n` times
the corresponding atom. -/
theorem zeroFlipWronskianLin_walsh_singleton {n : Nat} (c : Fin n → ℂ) (j : Fin n) :
    zeroFlipWronskianLin c (walshVector ({j} : Finset (Fin n))) =
      (((2^n : Nat) : ℚ)) • blaschkeWronskianAtom c j := by
  simp only [zeroFlipWronskianLin, Fintype.linearCombination_apply, walshVector,
    walshCharacter_singleton]
  exact zeroFlipWronskian_singleton_walsh c j

/-- Every atom lies in the actual Wronskian range, because the nonzero factor
`2^n` can be divided out over `ℚ`. -/
theorem blaschkeWronskianAtom_mem_range {n : Nat} (c : Fin n → ℂ) (j : Fin n) :
    blaschkeWronskianAtom c j ∈ LinearMap.range (zeroFlipWronskianLin c) := by
  let q : ℚ := (((2^n : Nat) : ℚ))
  have hq : q ≠ 0 := by
    dsimp [q]
    positivity
  refine ⟨q⁻¹ • walshVector ({j} : Finset (Fin n)), ?_⟩
  rw [map_smul, zeroFlipWronskianLin_walsh_singleton]
  change q⁻¹ • (q • blaschkeWronskianAtom c j) = _
  rw [← mul_smul, inv_mul_cancel₀ hq, one_smul]

/-- The image is not merely contained in the atom span: it is exactly the span
of the `n` fixed Wronskian atoms. -/
theorem zeroFlipWronskianLin_range_eq_atomSpan {n : Nat} (c : Fin n → ℂ) :
    LinearMap.range (zeroFlipWronskianLin c) = blaschkeWronskianAtomSpan c := by
  apply le_antisymm
  · exact zeroFlipWronskianLin_range_le_atomSpan c
  · apply Submodule.span_le.mpr
    intro p hp
    rcases hp with ⟨j, rfl⟩
    exact blaschkeWronskianAtom_mem_range c j

/-- Exact nullity formula: all dependence on the actual Blaschke zeros is now
concentrated in the dimension of the fixed atom span. -/
theorem zeroFlipWronskianLin_kernel_finrank_exact {n : Nat} (c : Fin n → ℂ) :
    Module.finrank ℚ (LinearMap.ker (zeroFlipWronskianLin c)) =
      2^n - Module.finrank ℚ (blaschkeWronskianAtomSpan c) := by
  have hnull := (zeroFlipWronskianLin c).finrank_range_add_finrank_ker
  rw [zeroFlipWronskianLin_range_eq_atomSpan,
    Module.finrank_fintype_fun_eq_card, Fintype.card_finset,
    Fintype.card_fin] at hnull
  have hrange : Module.finrank ℚ (blaschkeWronskianAtomSpan c) ≤ 2^n := by
    omega
  omega

end FormalResearch.Blaschke
