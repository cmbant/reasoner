import FormalResearch.QIA.IsotypicMultiplicityReductionPositivity

/-!
# QI-A finite amplification of an isotypic multiplicity block reduction

This module proves the finite-ancilla positivity statement behind complete
positivity for the explicit sector partial trace.  For an arbitrary finite
ancilla `β`, the map obtained by applying
`isotypicMultiplicityBlockReduction` to each `β × β` matrix block preserves
positive semidefiniteness.

This is genuine amplification-level positivity, but it is intentionally not yet
bundled as Mathlib's `CompletelyPositiveMap`: that API uses `CStarMatrix` and
its spectral order, whose transport from the raw `Matrix.PosSemidef` statement
is a separate bridge.
-/

namespace FormalResearch.QIA

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

/-- Applying the sector carrier partial trace entrywise to every block of a
finite ancilla amplification preserves positive semidefiniteness.

The proof is the same structural reason as for the unamplified map: for each
carrier basis coordinate, the amplified output contributes a principal
submatrix of the amplified input, and the partial trace is their finite sum. -/
theorem isotypicMultiplicityBlockReduction_amplification_posSemidef
    {β α : Type*} [Fintype β] [Fintype α] [DecidableEq α]
    (d g : α → Nat) (a : α)
    {X : Matrix (β × isotypicDirectSumCarrier d g)
          (β × isotypicDirectSumCarrier d g) ℂ}
    (hX : X.PosSemidef) :
    ((fun ir js : β × Fin (g a) =>
        isotypicMultiplicityBlockReduction d g a
          (fun p q => X (ir.1, p) (js.1, q)) ir.2 js.2) :
      Matrix (β × Fin (g a)) (β × Fin (g a)) ℂ).PosSemidef := by
  classical
  have hsum :
      (∑ c : Fin (d a),
        X.submatrix
          (fun ir : β × Fin (g a) =>
            (ir.1, (⟨⟨a, ir.2⟩, c⟩ : isotypicDirectSumCarrier d g)))
          (fun ir : β × Fin (g a) =>
            (ir.1, (⟨⟨a, ir.2⟩, c⟩ : isotypicDirectSumCarrier d g)))).PosSemidef := by
    apply Matrix.posSemidef_sum Finset.univ
    intro c hc
    exact hX.submatrix _
  have heq :
      (fun ir js : β × Fin (g a) =>
        isotypicMultiplicityBlockReduction d g a
          (fun p q => X (ir.1, p) (js.1, q)) ir.2 js.2) =
      ∑ c : Fin (d a),
        X.submatrix
          (fun ir : β × Fin (g a) =>
            (ir.1, (⟨⟨a, ir.2⟩, c⟩ : isotypicDirectSumCarrier d g)))
          (fun ir : β × Fin (g a) =>
            (ir.1, (⟨⟨a, ir.2⟩, c⟩ : isotypicDirectSumCarrier d g))) := by
    ext ir js
    rw [Matrix.sum_apply]
    rfl
  rw [heq]
  exact hsum

end

end FormalResearch.QIA
