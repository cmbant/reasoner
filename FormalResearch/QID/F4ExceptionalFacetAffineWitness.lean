import FormalResearch.QID.F4ExceptionalFacetCertificate

namespace FormalResearch.QID

/-!
# QI-D exceptional F4 facet: active affine-rank witness

This module upgrades the finite support certificate to the source's active
`affine_dimension = 15` claim without asking Lean to expand a 15-by-15
Leibniz determinant.

We give 16 explicit words in the two displayed F4 generators.  Lean checks that
all 16 attain the exceptional support.  After subtracting the first active
matrix and dropping the final ambient coordinate, the remaining 15 difference
vectors form a 15-by-15 rational matrix.  An explicit inverse is supplied and
checked on both sides, giving a kernel-triviality / independence certificate.

Together with the nonzero support normal, this is the exact finite affine-rank
certificate used to identify the displayed supporting hyperplane as a facet in
the known 16-dimensional `conv W(F4)` ambient space.  The ambient
full-dimensionality and the literature theorem that there are exactly two F4
facet orbits remain external structural inputs.
-/

/-- Evaluate a source-generator word (`false = G1`, `true = G2`) in the finite
parameter transition system. -/
def f4WordParam (w : List Bool) : F4Param :=
  w.foldl f4ParamStep ⟨0, f4B4Identity⟩

/-- Sixteen explicit active words: one affine base point plus fifteen points
whose differences are independent. -/
def f4AffineWord : Fin 16 → List Bool := ![
  [true,false,false,false,true],
  [false,false,false,true,true,false,true,true],
  [false,false,true,false,false,false,false,true],
  [true,false,false,false,true,false,false,false],
  [true,true,false,false,true,true,true,false],
  [true,false,true,true,false,false,false,false,true],
  [true,true,true,false,true,true,true,true,false],
  [true,true,true,true,false,true,true,true,false],
  [false,false,false,true,false,false,false,false,true,false],
  [false,false,true,true,true,false,false,true,false,false],
  [false,true,true,false,false,true,true,true,false,false],
  [true,false,false,true,true,true,false,false,true,false],
  [true,true,false,false,true,true,false,false,true,false],
  [false,false,false,false,true,true,false,false,true,false,false],
  [false,false,false,true,true,false,true,true,false,false,false],
  [false,true,true,false,false,true,true,true,false,true,true]
]

/-- The sixteen exact active generated matrices. -/
def f4AffineParam (i : Fin 16) : F4Param := f4WordParam (f4AffineWord i)

/-- Every chosen word attains the exceptional support `Tr(XA)=1`, represented
as the integer score `8`. -/
theorem f4AffineWords_active : ∀ i : Fin 16,
    f4ExceptionalScore8 (f4AffineParam i) = 8 := by
  native_decide

/-- Row-major coordinates of a 4-by-4 matrix with only the final `(3,3)`
coordinate omitted. -/
def f4Coord15 : Fin 15 → F4Fin × F4Fin := ![
  (0,0),(0,1),(0,2),(0,3),
  (1,0),(1,1),(1,2),(1,3),
  (2,0),(2,1),(2,2),(2,3),
  (3,0),(3,1),(3,2)
]

/-- Fifteen active difference vectors in the first fifteen ambient coordinates.
The scaled matrices store `2X`, hence division by two recovers the rational
source coordinates. -/
def f4AffineDifference : Matrix (Fin 15) (Fin 15) ℚ := fun r c =>
  let rc := f4Coord15 c
  ((f4ParamScaled (f4AffineParam r.succ) rc.1 rc.2 -
      f4ParamScaled (f4AffineParam 0) rc.1 rc.2 : ℤ) : ℚ) / 2

/-- Explicit inverse of the active difference matrix. -/
def f4AffineDifferenceInv : Matrix (Fin 15) (Fin 15) ℚ :=
!![ 3/4,    0,  1/4, -1/2,  1/2,  1/4,    0,  1/4, -1/2,    0, -1/4,    0, -1/4, -1/4,  1/4;
      -1, -1/2,    0,  1/2,    0, -1/2,    0,  1/2,  1/2, -1/2,    0,  1/2,    0,    1, -1/2;
       0,    0,    0,    0,    0,    0,    0,    0,    0,  1/2,    0,    0, -1/2,    0,    0;
     3/4,  1/2,  1/4,    0, -1/2, -1/4,    1, -1/4,    0,    0, -1/4, -1/2, -3/4, -1/4, -1/4;
     1/2,  1/2,  1/2,    0,    0,  1/2,    0, -1/2,  1/2,  1/2, -1/2, -1/2, -1/2, -1/2,    0;
     1/4,   -1, -1/4,    0,  1/2,  1/4,    0,  1/4, -1/2,    0,  1/4,    0,  1/4,  1/4, -1/4;
     1/4, -1/2, -1/4,  1/2,  1/2, -1/4,    0, -1/4,    0,    0,  1/4, -1/2, -1/4,  1/4,  1/4;
    -1/2,    0, -1/2,  1/2,    0,    0,    0,    0,    0,  1/2, -1/2,    0,    0,  1/2, -1/2;
     3/4,    0, -3/4,    0,  1/2, -1/4,    0, -1/4, -1/2,  1/2, -1/4,    0,  1/4, -1/4,  1/4;
       0,  1/2,    1,    0,    0,    0,    0,    0,  1/2,    0,    0, -1/2, -1/2,    0, -1/2;
       0,    0,    0, -1/2,    0,  1/2,    0,  1/2,    0,    0,    0,    0,    0,    0,    0;
     3/4,  1/2,  1/4, -1/2,  1/2,  1/4,    0, -3/4,    0,  1/2, -1/4, -1/2, -1/4, -1/4, -1/4;
    -1/2, -1/2, -1/2,  1/2,    0,    0,    0,    0, -1/2,    0,  1/2,  1/2,    0,  1/2,    0;
     3/4,    1,  5/4, -1/2, -1/2,  1/4,    0, -3/4,  1/2,  1/2, -1/4,   -1, -3/4, -1/4,  1/4;
     1/4, -1/2, -1/4,    0,  1/2,  1/4,   -1,  1/4,    0, -1/2,  1/4,  1/2,  1/4,  1/4,  1/4]

/-- Exact inverse certificate for the fifteen active difference directions. -/
theorem f4AffineDifference_inverse_certificate :
    f4AffineDifference * f4AffineDifferenceInv = 1 ∧
      f4AffineDifferenceInv * f4AffineDifference = 1 := by
  native_decide

/-- A row-coefficient relation among the fifteen difference vectors is trivial.
This is the affine independence certificate in a form independent of any
high-level rank API. -/
theorem f4AffineDifference_kernel_trivial
    (x : Fin 15 → ℚ)
    (h : Matrix.vecMul x f4AffineDifference = 0) : x = 0 := by
  calc
    x = Matrix.vecMul x (1 : Matrix (Fin 15) (Fin 15) ℚ) := by simp
    _ = Matrix.vecMul x (f4AffineDifference * f4AffineDifferenceInv) := by
      rw [f4AffineDifference_inverse_certificate.1]
    _ = Matrix.vecMul (Matrix.vecMul x f4AffineDifference)
          f4AffineDifferenceInv := by
      rw [Matrix.vecMul_vecMul]
    _ = Matrix.vecMul 0 f4AffineDifferenceInv := by rw [h]
    _ = 0 := by simp

/-- Bundled exact affine witness: sixteen support-active points and a trivial
kernel for their fifteen difference directions. -/
theorem f4Exceptional_active_affine15_certificate :
    (∀ i : Fin 16, f4ExceptionalScore8 (f4AffineParam i) = 8) ∧
    (∀ x : Fin 15 → ℚ,
      Matrix.vecMul x f4AffineDifference = 0 → x = 0) := by
  exact ⟨f4AffineWords_active, f4AffineDifference_kernel_trivial⟩

end FormalResearch.QID
