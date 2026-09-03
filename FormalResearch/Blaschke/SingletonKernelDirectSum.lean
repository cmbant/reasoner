import Mathlib
import FormalResearch.Blaschke.SingletonWalshSynthesis
import FormalResearch.Blaschke.WronskianAtomUnitDisk

namespace FormalResearch.Blaschke

/-- The actual subspace synthesized by singleton Walsh coefficients. -/
def singletonWalshRange (n : Nat) :
    Submodule ℚ (Finset (Fin n) → ℚ) :=
  LinearMap.range (singletonWalshSynthesis n)

/-- The singleton Walsh complement has exactly the expected dimension `n`. -/
theorem singletonWalshRange_finrank (n : Nat) :
    Module.finrank ℚ (singletonWalshRange n) = n := by
  unfold singletonWalshRange
  rw [LinearMap.finrank_range_of_inj (singletonWalshSynthesis_injective n),
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

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
  apply le_antisymm
  · exact le_top
  · rw [← (walshBasis n).span_eq]
    apply Submodule.span_le.mpr
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
  apply le_antisymm
  · intro x hx
    rcases hx.1 with ⟨a, rfl⟩
    have hzero :
        zeroFlipWronskianLin c (singletonWalshSynthesis n a) = 0 :=
      LinearMap.mem_ker.mp hx.2
    have hcomp :=
      zeroFlipWronskianLin_singletonSynthesis_injective_of_unitDisk c hdisk hinj
    have ha : a = 0 := hcomp (by
      simpa using hzero)
    subst a
    simp
  · exact bot_le

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
