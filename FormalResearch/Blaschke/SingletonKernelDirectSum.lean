import Mathlib
import FormalResearch.Blaschke.SingletonWalshSynthesis
import FormalResearch.Blaschke.WronskianAtomUnitDisk

namespace FormalResearch.Blaschke

/-- The actual subspace synthesized by singleton Walsh coefficients. -/
def singletonWalshRange (n : Nat) :
    Submodule ℚ (Finset (Fin n) → ℚ) :=
  LinearMap.range (singletonWalshSynthesis n)

/-- Every singleton Walsh basis vector belongs to the singleton synthesis
range. -/
theorem walshVector_singleton_mem_singletonWalshRange
    {n : Nat} (j : Fin n) :
    walshVector ({j} : Finset (Fin n)) ∈ singletonWalshRange n := by
  refine ⟨Pi.single j 1, ?_⟩
  simp [singletonWalshRange, singletonWalshSynthesis,
    Fintype.linearCombination_apply_single]

/-- Singleton Walsh modes together with all non-singleton Walsh modes span the
entire Boolean coefficient space. -/
theorem singletonWalshRange_sup_nonSingletonWalshSpan_eq_top (n : Nat) :
    singletonWalshRange n ⊔ nonSingletonWalshSpan n = ⊤ := by
  rw [← (walshBasis n).span_eq]
  apply le_antisymm
  · exact le_top
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with ⟨T, rfl⟩
    by_cases hT : T.card = 1
    · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hT
      exact Submodule.mem_sup_left
        (walshVector_singleton_mem_singletonWalshRange j)
    · exact Submodule.mem_sup_right
        (Submodule.subset_span ⟨⟨T, hT⟩, rfl⟩)

/-- Under distinct open-disk zeros, the singleton sector meets the exact
Wronskian kernel only at zero. -/
theorem singletonWalshRange_inf_wronskianKernel_eq_bot_of_unitDisk
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    singletonWalshRange n ⊓ LinearMap.ker (zeroFlipWronskianLin c) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  rcases hx.1 with ⟨a, rfl⟩
  rw [LinearMap.mem_ker] at hx
  have hcomp :=
    zeroFlipWronskianLin_singletonSynthesis_injective_of_unitDisk c hdisk hinj
  have ha : a = 0 := hcomp (by
    simpa using hx.2)
  subst a
  simp

/-- Exact direct-sum decomposition of Boolean zero-flip coefficient space:
the singleton Walsh sector is a complement to the Wronskian kernel. -/
theorem singletonWalshRange_sup_wronskianKernel_eq_top_of_unitDisk
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    singletonWalshRange n ⊔ LinearMap.ker (zeroFlipWronskianLin c) = ⊤ := by
  rw [zeroFlipWronskianLin_kernel_eq_nonSingletonWalshSpan_of_unitDisk
    c hdisk hinj]
  exact singletonWalshRange_sup_nonSingletonWalshSpan_eq_top n

end FormalResearch.Blaschke
