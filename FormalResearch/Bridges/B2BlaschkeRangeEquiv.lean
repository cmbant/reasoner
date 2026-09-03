import Mathlib
import FormalResearch.Blaschke.SingletonWalshSynthesis
import FormalResearch.Blaschke.WronskianUnitDiskRank
import FormalResearch.Bridges.B2BlaschkeWeightOneMultiplicity

namespace FormalResearch.Bridges

/-- The Wronskian transform restricted to the canonical singleton-Walsh
coefficient coordinates. -/
def singletonWronskianMap {n : Nat} (c : Fin n → ℂ) :
    (Fin n → ℚ) →ₗ[ℚ] ℂ[X] :=
  (Blaschke.zeroFlipWronskianLin c).comp (Blaschke.singletonWalshSynthesis n)

/-- Under distinct open-disk zeros, the singleton-coordinate Wronskian map is
injective. -/
theorem singletonWronskianMap_injective_of_unitDisk
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Function.Injective (singletonWronskianMap c) := by
  exact Blaschke.zeroFlipWronskianLin_singletonSynthesis_injective_of_unitDisk
    c hdisk hinj

/-- The singleton-coordinate image is contained in the full Wronskian image. -/
theorem singletonWronskianMap_range_le {n : Nat} (c : Fin n → ℂ) :
    LinearMap.range (singletonWronskianMap c) ≤
      LinearMap.range (Blaschke.zeroFlipWronskianLin c) := by
  rintro y ⟨a, rfl⟩
  exact ⟨Blaschke.singletonWalshSynthesis n a, rfl⟩

/-- In the finite-Blaschke regime the singleton-coordinate image is not merely
contained in the Wronskian image: it is the entire image. -/
theorem singletonWronskianMap_range_eq_wronskianRange_of_unitDisk
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    LinearMap.range (singletonWronskianMap c) =
      LinearMap.range (Blaschke.zeroFlipWronskianLin c) := by
  apply Submodule.eq_of_le_of_finrank_le (singletonWronskianMap_range_le c)
  rw [LinearMap.finrank_range_of_inj
      (singletonWronskianMap_injective_of_unitDisk c hdisk hinj),
    Blaschke.zeroFlipWronskianLin_range_finrank_of_unitDisk c hdisk hinj,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- Canonical linear equivalence from the `n` singleton Walsh coordinates to
the actual finite-Blaschke Wronskian image.  No basis choice is made: the
forward map is exactly the Wronskian transform after singleton synthesis. -/
noncomputable def singletonCoordinatesEquivWronskianRange
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    (Fin n → ℚ) ≃ₗ[ℚ] LinearMap.range (Blaschke.zeroFlipWronskianLin c) :=
  (LinearEquiv.ofInjective (singletonWronskianMap c)
      (singletonWronskianMap_injective_of_unitDisk c hdisk hinj)).trans
    (LinearEquiv.ofEq _ _
      (singletonWronskianMap_range_eq_wronskianRange_of_unitDisk
        c hdisk hinj))

end FormalResearch.Bridges
