import FormalResearch.QIA.CStarMatrixPosSemidefOrder
import Mathlib.Data.Matrix.Composition

/-!
# QI-A nested C-star-matrix block flattening

Mathlib's completely-positive-map API tests positivity on matrices whose entries
are themselves C-star-algebra elements.  For the QI-A finite matrix algebras,
`Matrix.comp` is the canonical block flattening

`M_β(M_n(ℂ)) ≃ M_{β × n}(ℂ)`.

This module proves the input-side positivity bridge needed to feed a positive
`CStarMatrix` amplification into the existing raw `Matrix.PosSemidef`
amplification theorem.  It does not itself construct a `CompletelyPositiveMap`
and makes no CPTP claim.
-/

namespace FormalResearch.QIA

open Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder

noncomputable section

/-- Canonically flatten a square C-star matrix whose entries are square complex
C-star matrices into one raw complex matrix on the product index. -/
def cstarMatrixBlockFlatten
    {β n : Type*}
    (M : CStarMatrix β β (CStarMatrix n n ℂ)) :
    Matrix (β × n) (β × n) ℂ :=
  Matrix.comp β β n n ℂ M

@[simp] theorem cstarMatrixBlockFlatten_zero
    {β n : Type*} :
    cstarMatrixBlockFlatten
        (0 : CStarMatrix β β (CStarMatrix n n ℂ)) =
      (0 : Matrix (β × n) (β × n) ℂ) := by
  rfl

@[simp] theorem cstarMatrixBlockFlatten_add
    {β n : Type*}
    (X Y : CStarMatrix β β (CStarMatrix n n ℂ)) :
    cstarMatrixBlockFlatten (X + Y) =
      cstarMatrixBlockFlatten X + cstarMatrixBlockFlatten Y := by
  rfl

/-- Block flattening sends a nested star square to the ordinary conjugate-
transpose square of the flattened scalar matrix. -/
theorem cstarMatrixBlockFlatten_star_mul_self
    {β n : Type*} [Fintype β] [Fintype n]
    (M : CStarMatrix β β (CStarMatrix n n ℂ)) :
    cstarMatrixBlockFlatten (star M * M) =
      (cstarMatrixBlockFlatten M)ᴴ * cstarMatrixBlockFlatten M := by
  have hstar :
      Matrix.comp β β n n ℂ (star M) =
        (Matrix.comp β β n n ℂ M)ᴴ := by
    rfl
  calc
    cstarMatrixBlockFlatten (star M * M) =
        Matrix.comp β β n n ℂ (star M * M) := rfl
    _ = Matrix.comp β β n n ℂ (star M) * Matrix.comp β β n n ℂ M := by
      exact (Matrix.compRingEquiv β n ℂ).map_mul (star M) M
    _ = (cstarMatrixBlockFlatten M)ᴴ * cstarMatrixBlockFlatten M := by
      rw [hstar]
      rfl

/-- Spectral nonnegativity of a nested finite complex `CStarMatrix` implies raw
positive semidefiniteness after canonical block flattening. -/
theorem cstarMatrixBlockFlatten_posSemidef_of_nonneg
    {β n : Type*} [Fintype β] [DecidableEq β] [Fintype n] [DecidableEq n]
    {M : CStarMatrix β β (CStarMatrix n n ℂ)}
    (hM : 0 ≤ M) :
    (cstarMatrixBlockFlatten M).PosSemidef := by
  rw [StarOrderedRing.nonneg_iff] at hM
  induction hM using AddSubmonoid.closure_induction with
  | mem X hX =>
      obtain ⟨S, rfl⟩ := hX
      rw [cstarMatrixBlockFlatten_star_mul_self]
      exact Matrix.posSemidef_conjTranspose_mul_self _
  | zero =>
      rw [cstarMatrixBlockFlatten_zero]
      exact Matrix.PosSemidef.zero
  | add X Y hX hY ihX ihY =>
      rw [cstarMatrixBlockFlatten_add]
      exact ihX.add ihY

end

end FormalResearch.QIA
