import Mathlib

namespace FormalResearch.QID

/-!
# QI-D exceptional F4 facet: exact finite certificate core

This module matches the exact source verifier
`cmbant/QIprojects:QI-D/code/certify_F4_exceptional_facet.py`, audited at
QIprojects main `51d23f262d3da3b90e512ede95b20757b41bdff5` (source blob
`c0c3534128658bb18c5563e1815893e3272fa7e0`).

The source uses the two displayed rational generators from Dutour Sikiric's
F4 Birkhoff-polytope paper.  Lean reproduces the finite generator closure and
checks the source's exact representative data:

* the closure stabilizes with `1152` rational matrices;
* the displayed rank-one facet has support `1` and `288` active matrices;
* the displayed exceptional normal has support `1` and `36` active matrices;
* the rank-one normal has an explicit outer-product factorization;
* the exceptional normal has determinant zero and a nonzero `3 x 3` minor,
  giving the exact algebraic rank-three certificate used here;
* the folded E6/F4 Gram identity and the displayed simple-root coordinate
  conversion hold exactly.

The affine-dimension-15 witness is intentionally split into a follow-up module
so the expensive finite generator/support computation can be hard-gated first.
The literature classification theorem saying that there are exactly two facet
orbits is external and is not asserted here.
-/

abbrev F4Fin := Fin 4
abbrev F4Vec := F4Fin → ℚ
abbrev F4Mat := Matrix F4Fin F4Fin ℚ

/-- First displayed F4 generator. -/
def f4Generator1 : F4Mat :=
  !![ 1/2, -1/2,  1/2,  1/2;
     -1/2, -1/2, -1/2,  1/2;
      1/2,  1/2, -1/2,  1/2;
      1/2, -1/2, -1/2, -1/2]

/-- Second displayed F4 generator. -/
def f4Generator2 : F4Mat :=
  !![-1/2,  1/2, -1/2, -1/2;
      1/2, -1/2, -1/2, -1/2;
     -1/2, -1/2,  1/2, -1/2;
      1/2,  1/2,  1/2, -1/2]

/-- One breadth layer of the source generator closure, multiplying on the
right by either displayed generator. -/
def f4ClosureStep (s : Finset F4Mat) : Finset F4Mat :=
  s ∪ s.image (fun w => w * f4Generator1) ∪
    s.image (fun w => w * f4Generator2)

/-- Finite breadth closure after `n` generator layers. -/
def f4Closure : Nat → Finset F4Mat
  | 0 => {1}
  | n + 1 => f4ClosureStep (f4Closure n)

/-- The source BFS reaches all 1152 displayed-generator matrices by depth 16. -/
def f4Weyl : Finset F4Mat := f4Closure 16

/-- Exact order certificate for the displayed-generator closure. -/
theorem f4Weyl_card : f4Weyl.card = 1152 := by
  native_decide

/-- Depth 16 is already a fixed point of the generator closure. -/
theorem f4Weyl_stable : f4Closure 17 = f4Closure 16 := by
  native_decide

/-- Source trace pairing `Tr(X A) = sum_ij X_ij A_ji`. -/
def f4TracePair (X A : F4Mat) : ℚ :=
  ∑ i : F4Fin, ∑ j : F4Fin, X i j * A j i

/-- Displayed rank-one Birkhoff representative. -/
def f4RankOneNormal : F4Mat :=
  !![0, 0, 0,  0;
     0, 0, 0,  0;
     0, 0, 0,  0;
     1, 0, 0, -1]

/-- Displayed exceptional rank-three normal. -/
def f4ExceptionalNormal : F4Mat :=
  !![1/4,   0, 1/4,    0;
       0, 1/4,   0, -1/4;
       0, 1/4,   0,  1/4;
     1/4,   0, 1/4, -2/4]

/-- Count matrices violating the claimed support bound `Tr(XA) <= 1`. -/
def f4SupportViolationCount (A : F4Mat) : Nat :=
  (f4Weyl.filter (fun X => decide (1 < f4TracePair X A))).card

/-- Count matrices attaining `Tr(XA)=1`. -/
def f4SupportActiveCount (A : F4Mat) : Nat :=
  (f4Weyl.filter (fun X => decide (f4TracePair X A = 1))).card

/-- Exact rank-one facet support audit from the source verifier. -/
theorem f4RankOne_support_certificate :
    f4SupportViolationCount f4RankOneNormal = 0 ∧
      f4SupportActiveCount f4RankOneNormal = 288 := by
  native_decide

/-- Exact exceptional facet support/active-count audit from the source verifier. -/
theorem f4Exceptional_support_certificate :
    f4SupportViolationCount f4ExceptionalNormal = 0 ∧
      f4SupportActiveCount f4ExceptionalNormal = 36 := by
  native_decide

/-- Outer product used for the explicit rank-one normal certificate. -/
def f4Outer (u v : F4Vec) : F4Mat := fun i j => u i * v j

/-- Last standard basis vector. -/
def f4E3 : F4Vec := ![0, 0, 0, 1]

/-- Covector appearing in the displayed rank-one normal. -/
def f4RankOneCovector : F4Vec := ![1, 0, 0, -1]

/-- The displayed rank-one normal is literally one outer product. -/
theorem f4RankOne_outer_certificate :
    f4RankOneNormal = f4Outer f4E3 f4RankOneCovector := by
  native_decide

/-- A nonzero `3 x 3` minor of the exceptional normal, using rows `(0,1,2)`
and columns `(0,1,3)`. -/
def f4ExceptionalMinor : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1/4,   0,    0;
       0, 1/4, -1/4;
       0, 1/4,  1/4]

/-- Exact algebraic rank-three certificate: the full determinant vanishes but
this displayed `3 x 3` minor has determinant `1/32`. -/
theorem f4Exceptional_rankThree_certificate :
    f4ExceptionalNormal.det = 0 ∧ f4ExceptionalMinor.det = 1 / 32 := by
  native_decide

/-- Standard Euclidean F4 simple-root coordinate matrix used by the source. -/
def f4SimpleRootMatrix : F4Mat :=
  !![ 0,  0, 0,  1/2;
      1,  0, 0, -1/2;
     -1,  1, 0, -1/2;
      0, -1, 1, -1/2]

/-- Explicit inverse of `f4SimpleRootMatrix`. -/
def f4SimpleRootMatrixInv : F4Mat :=
  !![1, 1, 0, 0;
     2, 1, 1, 0;
     3, 1, 1, 1;
     2, 0, 0, 0]

/-- Exact inverse certificate, avoiding any noncomputable matrix inverse. -/
theorem f4SimpleRoot_inverse_certificate :
    f4SimpleRootMatrix * f4SimpleRootMatrixInv = 1 ∧
      f4SimpleRootMatrixInv * f4SimpleRootMatrix = 1 := by
  native_decide

/-- Folded simple-root coordinate form printed by the source verifier. -/
def f4ExceptionalFoldedCoordinates : F4Mat :=
  !![   0, 1/2, -1/4,    0;
       0, 1/2,    0, -1/4;
     -1/2, 3/2, -1/2,    0;
     -1/2, 1/2,    0,    0]

/-- Exact coordinate conversion `S^{-1} A S = Acoord`. -/
theorem f4Exceptional_coordinate_conversion :
    f4SimpleRootMatrixInv * f4ExceptionalNormal * f4SimpleRootMatrix =
      f4ExceptionalFoldedCoordinates := by
  native_decide

abbrev E6Fin := Fin 6
abbrev E6Mat := Matrix E6Fin E6Fin ℚ
abbrev E6xF4Mat := Matrix E6Fin F4Fin ℚ

/-- E6 Cartan/Gram matrix used in the source folded-coordinate audit. -/
def f4E6Gram : E6Mat :=
  !![ 2,  0, -1,  0,  0,  0;
      0,  2,  0, -1,  0,  0;
     -1,  0,  2, -1,  0,  0;
      0, -1, -1,  2, -1,  0;
      0,  0,  0, -1,  2, -1;
      0,  0,  0,  0, -1,  2]

/-- Folding incidence matrix for E6 node orbits `(0,5)`, `(2,4)`, `(3)`, `(1)`. -/
def f4FoldIncidence : E6xF4Mat :=
  !![1, 0, 0, 0;
     0, 0, 0, 1;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- Folded E6 Gram equals twice the standard Euclidean F4 simple-root Gram. -/
theorem f4FoldedGram_certificate :
    Matrix.mul (Matrix.mul f4FoldIncidence.transpose f4E6Gram) f4FoldIncidence =
      2 • (f4SimpleRootMatrix.transpose * f4SimpleRootMatrix) := by
  native_decide

/-- Bundle of the exact finite representative facts checked in this first gate. -/
theorem f4Exceptional_finite_core_certificate :
    f4Weyl.card = 1152 ∧
    f4SupportViolationCount f4RankOneNormal = 0 ∧
    f4SupportActiveCount f4RankOneNormal = 288 ∧
    f4SupportViolationCount f4ExceptionalNormal = 0 ∧
    f4SupportActiveCount f4ExceptionalNormal = 36 := by
  exact ⟨f4Weyl_card,
    f4RankOne_support_certificate.1,
    f4RankOne_support_certificate.2,
    f4Exceptional_support_certificate.1,
    f4Exceptional_support_certificate.2⟩

end FormalResearch.QID
