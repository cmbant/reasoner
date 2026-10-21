import FormalResearch.QIA.IsotypicMultiplicityReductionCompletelyPositive
import FormalResearch.QIA.IsotypicMultiplicityReductionPOVMLift

/-!
# QI-A coordinate symmetry reduction as an exact channel simulation

The finite-coordinate reduction is now known to be CPTP, and its canonical
trace adjoint is known to lift each target POVM.  This file composes those
facts into the operational statement needed for the upper-bound half of the
QI-A symmetry-reduction theorem: encode first with the multiplicity reduction,
then choose an arbitrary finite multiplicity POVM later, and reproduce its
outcome probabilities exactly by a source POVM.

This is an exact simulation theorem after finite isotypic coordinates have
been supplied.  It does not identify the coordinates with a physical
compact-group representation, nor prove that the lifted effects are all and
only the physical invariant effects.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- The canonical finite isotypic reduction is a CPTP encoding that exactly
simulates every finite POVM on the direct-sum multiplicity memory.  The later
query `F` is lifted by the canonical trace adjoint, so the equality holds
outcome by outcome for every source matrix. -/
theorem exists_isotypicMultiplicityReductionCPTP_exact_POVM_simulation
    {α : Type*} [Fintype α] [DecidableEq α]
    (d g : α → Nat) :
    ∃ C : MatrixCPTP (isotypicDirectSumCarrier d g) (multiplicityMemoryCarrier g),
      ∀ {J : Type*} [Fintype J]
        (F : J → Matrix (multiplicityMemoryCarrier g)
          (multiplicityMemoryCarrier g) ℂ),
        (∀ j, (F j).PosSemidef) →
        (∑ j, F j) =
          (1 : Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ) →
        ∃ E : J → Matrix (isotypicDirectSumCarrier d g)
          (isotypicDirectSumCarrier d g) ℂ,
          (∀ j, (E j).PosSemidef) ∧
          (∑ j, E j) =
            (1 : Matrix (isotypicDirectSumCarrier d g)
              (isotypicDirectSumCarrier d g) ℂ) ∧
          ∀ j X,
            Matrix.trace (E j * X) =
              Matrix.trace (F j * C.toMatrixMap X) := by
  refine ⟨isotypicMultiplicityReductionCPTP d g, ?_⟩
  intro J _ F hFpos hPOVM
  obtain ⟨hEpos, hEsum, hstats⟩ :=
    isotypicMultiplicityEffectLift_lifts_POVM d g F hFpos hPOVM
  refine ⟨fun j => isotypicMultiplicityEffectLift d g (F j), hEpos, hEsum, ?_⟩
  intro j X
  change Matrix.trace (isotypicMultiplicityEffectLift d g (F j) * X) =
    Matrix.trace (F j * isotypicMultiplicityReduction d g X)
  exact hstats j X

end

end FormalResearch.QIA
