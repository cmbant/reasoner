import Mathlib
import FormalResearch.Bridges.B2BlaschkeGatePhase
import FormalResearch.Blaschke.WronskianAtomUnitDisk
import FormalResearch.Blaschke.WalshWronskianExactRank
import FormalResearch.Blaschke.WalshWronskianKernelBasis

namespace FormalResearch.Bridges

open Complex
open scoped BigOperators

/-- Under the ordinary finite-Blaschke hypotheses, a Boolean Walsh mode
survives the zero-flip Wronskian transform exactly when it lies at Walsh
weight one.  Thus the Wronskian quotient selects precisely the singleton
Walsh sector. -/
theorem wronskian_walsh_survives_iff_singleton_of_unitDisk
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c)
    (T : Finset (Fin n)) :
    Blaschke.zeroFlipWronskianLin c (Blaschke.walshVector T) ≠ 0 ↔
      T.card = 1 := by
  constructor
  · intro hsurvive
    by_contra hcard
    exact hsurvive
      (Blaschke.zeroFlipWronskianLin_walsh_of_card_ne_one c T hcard)
  · intro hcard
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    rw [Blaschke.zeroFlipWronskianLin_walsh_singleton]
    apply smul_ne_zero
    · positivity
    · exact
        (Blaschke.blaschkeWronskianAtom_linearIndependent_of_unitDisk
          c hdisk hinj).ne_zero j

/-- Every Walsh mode that survives the finite-Blaschke Wronskian quotient is
therefore a weight-one eigenmode of the canonical B2 Hamming gate, with the
transported Blaschke-convention eigenphase `-i`. -/
theorem surviving_wronskian_walsh_mode_has_minus_i_gate_phase
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c)
    (T : Finset (Fin n))
    (hsurvive :
      Blaschke.zeroFlipWronskianLin c (Blaschke.walshVector T) ≠ 0) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      QIB2.gateB ^ S.card * QIB2.gateA ^ (n - S.card) *
        (Blaschke.walshCharacter T S : ℂ)) = -I := by
  have hcard : T.card = 1 :=
    (wronskian_walsh_survives_iff_singleton_of_unitDisk
      c hdisk hinj T).mp hsurvive
  rw [canonical_gate_blaschke_walsh_phase, hcard]
  simp

/-- Compact joint certificate: in the distinct open-disk regime, the
Wronskian-surviving Walsh modes are exactly the singleton sector, and every
survivor carries canonical Hamming-gate phase `-i` in the Blaschke gauge. -/
theorem b2_blaschke_singleton_selection_certificate
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c)
    (T : Finset (Fin n)) :
    (Blaschke.zeroFlipWronskianLin c (Blaschke.walshVector T) ≠ 0 ↔
      T.card = 1) ∧
    (Blaschke.zeroFlipWronskianLin c (Blaschke.walshVector T) ≠ 0 →
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        QIB2.gateB ^ S.card * QIB2.gateA ^ (n - S.card) *
          (Blaschke.walshCharacter T S : ℂ)) = -I) := by
  exact ⟨wronskian_walsh_survives_iff_singleton_of_unitDisk
      c hdisk hinj T,
    surviving_wronskian_walsh_mode_has_minus_i_gate_phase
      c hdisk hinj T⟩

end FormalResearch.Bridges
