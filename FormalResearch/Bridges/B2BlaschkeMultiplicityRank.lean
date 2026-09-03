import Mathlib
import FormalResearch.Bridges.B2BlaschkeSingletonSelection
import FormalResearch.Blaschke.WronskianUnitDiskRank
import FormalResearch.QIB2.HammingWalshWeightMultiplicity

namespace FormalResearch.Bridges

open Complex
open scoped BigOperators

/-- In the ordinary finite-Blaschke regime, the multiplicity of the B2
weight-one Walsh sector equals the exact Wronskian image rank, and both are
exactly the number `n` of Blaschke zeros. -/
theorem b2_weightOne_multiplicity_eq_wronskian_rank
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Fintype.card (QIB2.WalshWeightIndex n 1) =
        Module.finrank ℚ (LinearMap.range (Blaschke.zeroFlipWronskianLin c)) ∧
      Module.finrank ℚ (LinearMap.range (Blaschke.zeroFlipWronskianLin c)) = n := by
  have hcard : Fintype.card (QIB2.WalshWeightIndex n 1) = n := by
    rw [QIB2.card_WalshWeightIndex]
    simp
  have hrank :
      Module.finrank ℚ (LinearMap.range (Blaschke.zeroFlipWronskianLin c)) = n :=
    Blaschke.zeroFlipWronskianLin_range_finrank_of_unitDisk c hdisk hinj
  exact ⟨hcard.trans hrank.symm, hrank⟩

/-- Every B2 weight-one Walsh label has phase `-i` in the transported Blaschke
convention. -/
theorem b2_weightOne_blaschke_gauge_phase
    {n : Nat} (T : QIB2.WalshWeightIndex n 1) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      QIB2.gateB ^ S.card * QIB2.gateA ^ (n - S.card) *
        (Blaschke.walshCharacter T.1 S : ℂ)) = -I := by
  rw [canonical_gate_blaschke_walsh_phase, T.2]
  simp

/-- Compact multiplicity/rank/spectral certificate linking the B2 Hamming
sector to the finite-Blaschke Wronskian quotient. -/
theorem b2_blaschke_weightOne_rank_certificate
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Fintype.card (QIB2.WalshWeightIndex n 1) = n ∧
      Module.finrank ℚ (LinearMap.range (Blaschke.zeroFlipWronskianLin c)) = n ∧
      (∀ T : QIB2.WalshWeightIndex n 1,
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          QIB2.gateB ^ S.card * QIB2.gateA ^ (n - S.card) *
            (Blaschke.walshCharacter T.1 S : ℂ)) = -I) := by
  have hmul := b2_weightOne_multiplicity_eq_wronskian_rank c hdisk hinj
  exact ⟨by
      rw [QIB2.card_WalshWeightIndex]
      simp,
    hmul.2,
    fun T => b2_weightOne_blaschke_gauge_phase T⟩

end FormalResearch.Bridges
