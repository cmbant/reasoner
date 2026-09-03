import Mathlib
import FormalResearch.Blaschke.WalshBasis
import FormalResearch.Blaschke.WalshWronskianExactRank

namespace FormalResearch.Blaschke

open Polynomial
open scoped BigOperators

/-- Every non-singleton Walsh mode, including the constant mode, is killed by
the zero-flip Wronskian transform.  The singleton modes are exactly the only
Walsh modes that can survive. -/
theorem zeroFlipWronskianLin_walsh_of_card_ne_one {n : Nat}
    (c : Fin n → ℂ) (T : Finset (Fin n)) (hT : T.card ≠ 1) :
    zeroFlipWronskianLin c (walshVector T) = 0 := by
  simp only [zeroFlipWronskianLin, Fintype.linearCombination_apply, walshVector]
  simp_rw [blaschkeZeroFlipWronskian_expansion, smul_sum, smul_smul]
  rw [Fintype.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  rw [← Finset.sum_smul]
  change (∑ S : Finset (Fin n),
      walshCharacter T S * walshCharacter ({j} : Finset (Fin n)) S) •
        blaschkeWronskianAtom c j = 0
  have hne : T ≠ ({j} : Finset (Fin n)) := by
    intro h
    apply hT
    rw [h]
    simp
  rw [walshCharacter_orthogonal T {j}, if_neg hne, zero_smul]

/-- Index type for all Boolean Walsh modes except the singleton level. -/
abbrev NonSingletonWalshIndex (n : Nat) :=
  {T : Finset (Fin n) // T.card ≠ 1}

/-- Span of the non-singleton Walsh modes. -/
def nonSingletonWalshSpan (n : Nat) :
    Submodule ℚ (Finset (Fin n) → ℚ) :=
  Submodule.span ℚ
    (Set.range (fun T : NonSingletonWalshIndex n => walshVector T.1))

/-- Restricting the full Walsh basis preserves linear independence. -/
theorem nonSingletonWalsh_linearIndependent {n : Nat} :
    LinearIndependent ℚ
      (fun T : NonSingletonWalshIndex n => walshVector T.1) :=
  walshVector_linearIndependent.comp (fun T : NonSingletonWalshIndex n => T.1)
    Subtype.val_injective

/-- There are exactly `2^n-n` non-singleton Walsh modes. -/
theorem card_nonSingletonWalshIndex (n : Nat) :
    Fintype.card (NonSingletonWalshIndex n) = 2^n - n := by
  rw [Fintype.card_subtype_compl (fun T : Finset (Fin n) => T.card = 1)]
  simp [Fintype.card_finset_len, Fintype.card_fin]

/-- Hence the non-singleton Walsh span has dimension exactly `2^n-n`. -/
theorem nonSingletonWalshSpan_finrank (n : Nat) :
    Module.finrank ℚ (nonSingletonWalshSpan n) = 2^n - n := by
  unfold nonSingletonWalshSpan
  rw [finrank_span_eq_card nonSingletonWalsh_linearIndependent,
    card_nonSingletonWalshIndex]

/-- Every generator of the non-singleton Walsh span lies in the Wronskian
kernel. -/
theorem nonSingletonWalshSpan_le_kernel {n : Nat} (c : Fin n → ℂ) :
    nonSingletonWalshSpan n ≤ LinearMap.ker (zeroFlipWronskianLin c) := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with ⟨T, rfl⟩
  rw [LinearMap.mem_ker]
  exact zeroFlipWronskianLin_walsh_of_card_ne_one c T.1 T.2

/-- If the `n` fixed Wronskian atoms are linearly independent, their span has
full dimension `n`. -/
theorem blaschkeWronskianAtomSpan_finrank_of_independent {n : Nat}
    (c : Fin n → ℂ) (hAtoms : LinearIndependent ℚ (blaschkeWronskianAtom c)) :
    Module.finrank ℚ (blaschkeWronskianAtomSpan c) = n := by
  unfold blaschkeWronskianAtomSpan
  rw [finrank_span_eq_card hAtoms, Fintype.card_fin]

/-- Under atom independence the Wronskian kernel has the extremal nullity
`2^n-n`. -/
theorem zeroFlipWronskianLin_kernel_finrank_of_atom_independent {n : Nat}
    (c : Fin n → ℂ) (hAtoms : LinearIndependent ℚ (blaschkeWronskianAtom c)) :
    Module.finrank ℚ (LinearMap.ker (zeroFlipWronskianLin c)) = 2^n - n := by
  rw [zeroFlipWronskianLin_kernel_finrank_exact,
    blaschkeWronskianAtomSpan_finrank_of_independent c hAtoms]

/-- Basis-level kernel theorem.  If the Wronskian atoms are independent, then
nothing beyond the non-singleton Walsh modes lies in the zero-flip Wronskian
kernel.  Thus the kernel is exactly the span of the constant mode together
with every Walsh level at least two. -/
theorem zeroFlipWronskianLin_kernel_eq_nonSingletonWalshSpan {n : Nat}
    (c : Fin n → ℂ) (hAtoms : LinearIndependent ℚ (blaschkeWronskianAtom c)) :
    LinearMap.ker (zeroFlipWronskianLin c) = nonSingletonWalshSpan n := by
  symm
  apply Submodule.eq_of_le_of_finrank_le (nonSingletonWalshSpan_le_kernel c)
  rw [nonSingletonWalshSpan_finrank,
    zeroFlipWronskianLin_kernel_finrank_of_atom_independent c hAtoms]

end FormalResearch.Blaschke
