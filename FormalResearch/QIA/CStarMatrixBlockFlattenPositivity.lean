import FormalResearch.QIA.CStarMatrixPosSemidefOrder
import Mathlib.Data.Matrix.Composition

/-!
# QI-A nested C-star-matrix block flattening

Mathlib's completely-positive-map API tests positivity on matrices whose entries
are themselves C-star-algebra elements.  For the QI-A finite matrix algebras,
`Matrix.comp` is the canonical block flattening

`M_β(M_n(ℂ)) ≃ M_{β × n}(ℂ)`.

This module proves the bidirectional positivity bridge between nested
`CStarMatrix` spectral nonnegativity and raw `Matrix.PosSemidef` after canonical
block flattening.  This is the order transport needed to connect Mathlib's CP
amplification semantics to the existing raw finite-amplification theorem.  It
does not itself construct a `CompletelyPositiveMap` and makes no CPTP claim.
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

/-- Canonically unflatten one raw complex matrix on a product index into a
square C-star matrix whose entries are square complex C-star matrices. -/
def cstarMatrixBlockUnflatten
    {β n : Type*}
    (M : Matrix (β × n) (β × n) ℂ) :
    CStarMatrix β β (CStarMatrix n n ℂ) :=
  (Matrix.comp β β n n ℂ).symm M

@[simp] theorem cstarMatrixBlockFlatten_unflatten
    {β n : Type*}
    (M : Matrix (β × n) (β × n) ℂ) :
    cstarMatrixBlockFlatten (cstarMatrixBlockUnflatten M) = M := by
  exact (Matrix.comp β β n n ℂ).apply_symm_apply M

@[simp] theorem cstarMatrixBlockUnflatten_flatten
    {β n : Type*}
    (M : CStarMatrix β β (CStarMatrix n n ℂ)) :
    cstarMatrixBlockUnflatten (cstarMatrixBlockFlatten M) = M := by
  exact (Matrix.comp β β n n ℂ).symm_apply_apply M

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

@[simp] theorem cstarMatrixBlockUnflatten_zero
    {β n : Type*} :
    cstarMatrixBlockUnflatten
        (0 : Matrix (β × n) (β × n) ℂ) =
      (0 : CStarMatrix β β (CStarMatrix n n ℂ)) := by
  rfl

@[simp] theorem cstarMatrixBlockUnflatten_add
    {β n : Type*}
    (X Y : Matrix (β × n) (β × n) ℂ) :
    cstarMatrixBlockUnflatten (X + Y) =
      cstarMatrixBlockUnflatten X + cstarMatrixBlockUnflatten Y := by
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

/-- Canonical block unflattening sends an ordinary raw star square to the
nested C-star-matrix star square. -/
theorem cstarMatrixBlockUnflatten_star_mul_self
    {β n : Type*} [Fintype β] [Fintype n]
    (M : Matrix (β × n) (β × n) ℂ) :
    cstarMatrixBlockUnflatten (star M * M) =
      star (cstarMatrixBlockUnflatten M) * cstarMatrixBlockUnflatten M := by
  have hstar :
      cstarMatrixBlockUnflatten (star M) =
        star (cstarMatrixBlockUnflatten M) := by
    rfl
  calc
    cstarMatrixBlockUnflatten (star M * M) =
        cstarMatrixBlockUnflatten (star M) * cstarMatrixBlockUnflatten M := by
      exact (Matrix.compRingEquiv β n ℂ).symm.map_mul (star M) M
    _ = star (cstarMatrixBlockUnflatten M) * cstarMatrixBlockUnflatten M := by
      rw [hstar]

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

/-- Raw positive semidefiniteness after canonical block flattening implies
spectral nonnegativity of the original nested finite complex `CStarMatrix`. -/
theorem cstarMatrixBlockFlatten_nonneg_of_posSemidef
    {β n : Type*} [Fintype β] [DecidableEq β] [Fintype n] [DecidableEq n]
    {M : CStarMatrix β β (CStarMatrix n n ℂ)}
    (hM : (cstarMatrixBlockFlatten M).PosSemidef) :
    0 ≤ M := by
  apply StarOrderedRing.nonneg_iff.mpr
  let Z : Matrix (β × n) (β × n) ℂ := cstarMatrixBlockFlatten M
  have hZpsd : Z.PosSemidef := by
    simpa [Z] using hM
  have hraw : (0 : Matrix (β × n) (β × n) ℂ) ≤ Z :=
    Matrix.nonneg_iff_posSemidef.mpr hZpsd
  have hclosure :
      Z ∈ AddSubmonoid.closure
        (Set.range fun S : Matrix (β × n) (β × n) ℂ => star S * S) :=
    StarOrderedRing.nonneg_iff.mp hraw
  have hflat :
      cstarMatrixBlockUnflatten Z ∈
        AddSubmonoid.closure
          (Set.range fun S : CStarMatrix β β (CStarMatrix n n ℂ) => star S * S) := by
    induction hclosure using AddSubmonoid.closure_induction with
    | mem X hX =>
        obtain ⟨S, rfl⟩ := hX
        rw [cstarMatrixBlockUnflatten_star_mul_self]
        exact AddSubmonoid.subset_closure (Set.mem_range_self _)
    | zero =>
        rw [cstarMatrixBlockUnflatten_zero]
        exact AddSubmonoid.zero_mem _
    | add X Y hX hY ihX ihY =>
        rw [cstarMatrixBlockUnflatten_add]
        exact AddSubmonoid.add_mem _ ihX ihY
  simpa [Z] using hflat

/-- For finite complex matrix blocks, nested `CStarMatrix` spectral
nonnegativity is exactly raw positive semidefiniteness of the canonical
product-index flattening. -/
theorem cstarMatrixBlockFlatten_nonneg_iff_posSemidef
    {β n : Type*} [Fintype β] [DecidableEq β] [Fintype n] [DecidableEq n]
    (M : CStarMatrix β β (CStarMatrix n n ℂ)) :
    0 ≤ M ↔ (cstarMatrixBlockFlatten M).PosSemidef :=
  ⟨cstarMatrixBlockFlatten_posSemidef_of_nonneg,
    cstarMatrixBlockFlatten_nonneg_of_posSemidef⟩

end

end FormalResearch.QIA
