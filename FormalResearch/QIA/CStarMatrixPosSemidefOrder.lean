import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Order

/-!
# QI-A raw matrix PSD and C-star-matrix spectral order

Mathlib's `CStarMatrix` is a type copy of raw matrices, but its square-matrix
order is the C-star-algebra spectral order rather than the scoped raw matrix
order.  This module proves the finite complex-matrix bridge needed before the
QI-A amplification theorems can be bundled into Mathlib's completely-positive
map API.

This is only an order-transport result.  It does not itself construct a
`CompletelyPositiveMap` and makes no CPTP claim.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- For a finite complex square matrix, nonnegativity in `CStarMatrix`'s
spectral order is equivalent to raw matrix positive semidefiniteness.

Both orders are star-ordered-ring structures on the same underlying matrix
algebra, so their nonnegative cones are the additive closures of the same
star-square generators. -/
theorem cstarMatrix_ofMatrix_nonneg_iff_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) :
    0 ≤ CStarMatrix.ofMatrix M ↔ M.PosSemidef := by
  rw [StarOrderedRing.nonneg_iff]
  rw [← Matrix.nonneg_iff_posSemidef]
  rw [StarOrderedRing.nonneg_iff]
  rfl

end

end FormalResearch.QIA
