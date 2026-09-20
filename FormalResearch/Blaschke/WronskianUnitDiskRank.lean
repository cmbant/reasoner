import Mathlib
import FormalResearch.Blaschke.WronskianAtomUnitDisk

namespace FormalResearch.Blaschke

/-- For distinct zeros in the open unit disk, the polynomial-valued zero-flip
Wronskian transform has exact rank equal to the number of zeros. -/
theorem zeroFlipWronskianLin_range_finrank_of_unitDisk
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Module.finrank ℚ (LinearMap.range (zeroFlipWronskianLin c)) = n := by
  rw [zeroFlipWronskianLin_range_eq_atomSpan,
    blaschkeWronskianAtomSpan_finrank_of_independent c
      (blaschkeWronskianAtom_linearIndependent_of_unitDisk c hdisk hinj)]

/-- Exact nullity in the same ordinary finite-Blaschke regime. -/
theorem zeroFlipWronskianLin_kernel_finrank_of_unitDisk
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Module.finrank ℚ (LinearMap.ker (zeroFlipWronskianLin c)) = 2^n - n := by
  exact zeroFlipWronskianLin_kernel_finrank_of_atom_independent c
    (blaschkeWronskianAtom_linearIndependent_of_unitDisk c hdisk hinj)

/-- Compact rank-nullity/kernel certificate for distinct finite Blaschke zeros. -/
theorem zeroFlipWronskianLin_unitDisk_complete_certificate
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Module.finrank ℚ (LinearMap.range (zeroFlipWronskianLin c)) = n ∧
      Module.finrank ℚ (LinearMap.ker (zeroFlipWronskianLin c)) = 2^n - n ∧
      LinearMap.ker (zeroFlipWronskianLin c) = nonSingletonWalshSpan n := by
  exact ⟨zeroFlipWronskianLin_range_finrank_of_unitDisk c hdisk hinj,
    zeroFlipWronskianLin_kernel_finrank_of_unitDisk c hdisk hinj,
    zeroFlipWronskianLin_kernel_eq_nonSingletonWalshSpan_of_unitDisk c hdisk hinj⟩

end FormalResearch.Blaschke
