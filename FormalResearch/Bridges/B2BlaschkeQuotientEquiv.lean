import Mathlib
import FormalResearch.Blaschke.WronskianAtomUnitDisk
import FormalResearch.Blaschke.WronskianUnitDiskRank
import FormalResearch.Bridges.B2BlaschkeSingletonSelection

namespace FormalResearch.Bridges

/-- Intrinsic quotient form of the finite-Blaschke Walsh reduction.  Under
distinct open-disk zeros, quotienting the full Boolean coefficient space by
the span of every non-singleton Walsh mode gives exactly the image of the
zero-flip Wronskian transform. -/
noncomputable def nonSingletonWalshQuotientEquivWronskianRange
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    ((Finset (Fin n) → ℚ) ⧸ Blaschke.nonSingletonWalshSpan n) ≃ₗ[ℚ]
      LinearMap.range (Blaschke.zeroFlipWronskianLin c) :=
  (Submodule.quotEquivOfEq
      (Blaschke.nonSingletonWalshSpan n)
      (LinearMap.ker (Blaschke.zeroFlipWronskianLin c))
      (Blaschke.zeroFlipWronskianLin_kernel_eq_nonSingletonWalshSpan_of_unitDisk
        c hdisk hinj).symm).trans
    (LinearMap.quotKerEquivRange (Blaschke.zeroFlipWronskianLin c))

/-- The quotient dimension is therefore exactly the number `n` of surviving
weight-one Walsh coordinates. -/
theorem nonSingletonWalshQuotient_finrank_of_unitDisk
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Module.finrank ℚ
      ((Finset (Fin n) → ℚ) ⧸ Blaschke.nonSingletonWalshSpan n) = n := by
  rw [(nonSingletonWalshQuotientEquivWronskianRange c hdisk hinj).finrank_eq]
  exact Blaschke.zeroFlipWronskianLin_range_finrank_of_unitDisk c hdisk hinj

end FormalResearch.Bridges
