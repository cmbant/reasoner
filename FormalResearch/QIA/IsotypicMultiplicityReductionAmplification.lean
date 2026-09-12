import FormalResearch.QIA.IsotypicMultiplicityBlockAmplification

/-!
# QI-A finite amplification of the assembled isotypic multiplicity reduction

This module lifts the finite-ancilla positivity result for each sector partial
trace to the full block-diagonal multiplicity reduction.  The ancilla-first
indexing `β × multiplicityMemoryCarrier g` is obtained as a principal
submatrix/reindexing of the sector-first dependent block diagonal.

This is amplification-level `Matrix.PosSemidef` preservation for the explicit
finite reduction after isotypic coordinates have been supplied.  It is not yet
a bundled Mathlib `CompletelyPositiveMap`, whose statement uses `CStarMatrix`
and spectral order, and it makes no CPTP claim.
-/

namespace FormalResearch.QIA

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

/-- Applying the full finite isotypic multiplicity reduction entrywise to every
block of an arbitrary finite ancilla amplification preserves positive
semidefiniteness. -/
theorem isotypicMultiplicityReduction_amplification_posSemidef
    {β α : Type*} [Fintype β] [Fintype α] [DecidableEq α]
    (d g : α → Nat)
    {X : Matrix (β × isotypicDirectSumCarrier d g)
          (β × isotypicDirectSumCarrier d g) ℂ}
    (hX : X.PosSemidef) :
    Matrix.PosSemidef
      (fun ir js : β × multiplicityMemoryCarrier g =>
        isotypicMultiplicityReduction d g
          (fun p q => X (ir.1, p) (js.1, q)) ir.2 js.2) := by
  classical
  let M : ∀ a, Matrix (β × Fin (g a)) (β × Fin (g a)) ℂ :=
    fun a ir js =>
      isotypicMultiplicityBlockReduction d g a
        (fun p q => X (ir.1, p) (js.1, q)) ir.2 js.2
  have hM : ∀ a, (M a).PosSemidef := by
    intro a
    exact isotypicMultiplicityBlockReduction_amplification_posSemidef d g a hX
  have hblock : (Matrix.blockDiagonal' M).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact Matrix.isHermitian_blockDiagonal'_iff.mpr fun a => (hM a).isHermitian
    · intro x
      have hsum :
          0 ≤ ∑ a : α,
            star (fun ir : β × Fin (g a) => x ⟨a, ir⟩) ⬝ᵥ
              (M a *ᵥ fun ir : β × Fin (g a) => x ⟨a, ir⟩) := by
        apply Finset.sum_nonneg
        intro a ha
        exact (hM a).dotProduct_mulVec_nonneg _
      simpa [dotProduct, mulVec, Matrix.blockDiagonal', Fintype.sum_sigma] using hsum
  let e : β × multiplicityMemoryCarrier g → Σ a, β × Fin (g a) :=
    fun ir => ⟨ir.2.1, (ir.1, ir.2.2)⟩
  have hsub := hblock.submatrix e
  have heq :
      (fun ir js : β × multiplicityMemoryCarrier g =>
        isotypicMultiplicityReduction d g
          (fun p q => X (ir.1, p) (js.1, q)) ir.2 js.2) =
      (Matrix.blockDiagonal' M).submatrix e e := by
    ext ir js
    rcases ir with ⟨b, ⟨a, r⟩⟩
    rcases js with ⟨c, ⟨a', s⟩⟩
    by_cases h : a = a'
    · subst a'
      change
        isotypicMultiplicityReduction d g
            (fun p q => X (b, p) (c, q)) ⟨a, r⟩ ⟨a, s⟩ =
          Matrix.blockDiagonal' M ⟨a, (b, r)⟩ ⟨a, (c, s)⟩
      rw [isotypicMultiplicityReduction_sameSector_apply]
      rw [Matrix.blockDiagonal'_apply_eq]
      rfl
    · simp [e, M, isotypicMultiplicityReduction, Matrix.blockDiagonal', h]
  rw [heq]
  exact hsub

end

end FormalResearch.QIA
