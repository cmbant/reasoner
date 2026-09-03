import Mathlib
import FormalResearch.Bridges.B2BlaschkeSingletonSelection
import FormalResearch.Blaschke.WronskianUnitDiskRank
import FormalResearch.QIB2.HammingWalshWeightMultiplicity

namespace FormalResearch.Bridges

/-- The B2 Walsh weight-one sector has exactly `n` labels. -/
theorem b2_weight_one_walsh_card (n : Nat) :
    Fintype.card (QIB2.WalshWeightIndex n 1) = n := by
  rw [QIB2.card_WalshWeightIndex]
  simp

/-- In the distinct open-disk regime, the rank of the Blaschke Wronskian
transform is exactly the multiplicity of the B2 weight-one Walsh sector. -/
theorem wronskian_range_finrank_eq_b2_weight_one_card
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Module.finrank ℚ (LinearMap.range (Blaschke.zeroFlipWronskianLin c)) =
      Fintype.card (QIB2.WalshWeightIndex n 1) := by
  rw [Blaschke.zeroFlipWronskianLin_range_finrank_of_unitDisk c hdisk hinj,
    b2_weight_one_walsh_card]

/-- Dually, the Wronskian nullity is the full Boolean-cube dimension minus the
B2 weight-one multiplicity. -/
theorem wronskian_kernel_finrank_eq_cube_minus_b2_weight_one_card
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Module.finrank ℚ (LinearMap.ker (Blaschke.zeroFlipWronskianLin c)) =
      2^n - Fintype.card (QIB2.WalshWeightIndex n 1) := by
  rw [Blaschke.zeroFlipWronskianLin_kernel_finrank_of_unitDisk c hdisk hinj,
    b2_weight_one_walsh_card]

/-- Quantitative sector-identification certificate: the surviving Wronskian
quotient has exactly the dimension of the B2 weight-one eigenspace, while the
kernel accounts for all remaining Boolean Walsh dimensions. -/
theorem b2_blaschke_weight_one_multiplicity_certificate
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Module.finrank ℚ (LinearMap.range (Blaschke.zeroFlipWronskianLin c)) =
        Fintype.card (QIB2.WalshWeightIndex n 1) ∧
      Module.finrank ℚ (LinearMap.ker (Blaschke.zeroFlipWronskianLin c)) =
        2^n - Fintype.card (QIB2.WalshWeightIndex n 1) := by
  exact ⟨wronskian_range_finrank_eq_b2_weight_one_card c hdisk hinj,
    wronskian_kernel_finrank_eq_cube_minus_b2_weight_one_card c hdisk hinj⟩

end FormalResearch.Bridges
