import Mathlib

namespace FormalResearch.QID

/-!
# QI-D exceptional F4 facet: exact finite certificate core

This module matches the exact source verifier
`cmbant/QIprojects:QI-D/code/certify_F4_exceptional_facet.py`, audited at
QIprojects main `51d23f262d3da3b90e512ede95b20757b41bdff5` (source blob
`c0c3534128658bb18c5563e1815893e3272fa7e0`, committed verification-log blob
`43be8688e2361921906e4e218806ecdc57ec8e94`).

For efficient finite enumeration a Weyl matrix `X` is represented by the
integer matrix `2X`.  The displayed source generators therefore have entries
`±1`; scaled multiplication is `(AB)/2`.  Lean checks on the whole generated
closure that every such division is exact.

The expensive finite facts are deliberately bundled into one native
certificate, so the 1152-element closure is shared rather than recomputed by
several independent `native_decide` calls.

The literature classification theorem saying there are exactly two F4 facet
orbits remains external.  The active affine-dimension-15 witness is split into
a follow-up module after this finite core is hard-gated.
-/

abbrev F4Fin := Fin 4
abbrev F4Vec := F4Fin → ℚ
abbrev F4Mat := Matrix F4Fin F4Fin ℚ
abbrev F4ScaledMat := Matrix F4Fin F4Fin ℤ

/-- Integer matrix representing twice the first displayed F4 generator. -/
def f4ScaledGenerator1 : F4ScaledMat :=
  !![ 1, -1,  1,  1;
     -1, -1, -1,  1;
      1,  1, -1,  1;
      1, -1, -1, -1]

/-- Integer matrix representing twice the second displayed F4 generator. -/
def f4ScaledGenerator2 : F4ScaledMat :=
  !![-1,  1, -1, -1;
      1, -1, -1, -1;
     -1, -1,  1, -1;
      1,  1,  1, -1]

/-- Integer matrix representing twice the identity. -/
def f4ScaledIdentity : F4ScaledMat :=
  !![2,0,0,0; 0,2,0,0; 0,0,2,0; 0,0,0,2]

/-- Multiplication in the `2X` representation. -/
def f4ScaledMul (A B : F4ScaledMat) : F4ScaledMat :=
  fun i j => (∑ k : F4Fin, A i k * B k j) / 2

/-- Convert a scaled integer matrix back to its rational matrix. -/
def f4ScaledToRat (A : F4ScaledMat) : F4Mat :=
  fun i j => (A i j : ℚ) / 2

/-- Displayed rational source generators. -/
def f4Generator1 : F4Mat := f4ScaledToRat f4ScaledGenerator1
def f4Generator2 : F4Mat := f4ScaledToRat f4ScaledGenerator2

/-- The displayed rational generators are exactly the source matrices. -/
theorem f4Generator_source_certificate :
    f4Generator1 =
      !![ 1/2, -1/2,  1/2,  1/2;
         -1/2, -1/2, -1/2,  1/2;
          1/2,  1/2, -1/2,  1/2;
          1/2, -1/2, -1/2, -1/2] ∧
    f4Generator2 =
      !![-1/2,  1/2, -1/2, -1/2;
          1/2, -1/2, -1/2, -1/2;
         -1/2, -1/2,  1/2, -1/2;
          1/2,  1/2,  1/2, -1/2] := by
  native_decide

/-- One breadth layer of the displayed-generator closure. -/
def f4ScaledClosureStep (s : Finset F4ScaledMat) : Finset F4ScaledMat :=
  s ∪ s.image (fun w => f4ScaledMul w f4ScaledGenerator1) ∪
    s.image (fun w => f4ScaledMul w f4ScaledGenerator2)

/-- Finite breadth closure after `n` generator layers. -/
def f4ScaledClosure : Nat → Finset F4ScaledMat
  | 0 => {f4ScaledIdentity}
  | n + 1 => f4ScaledClosureStep (f4ScaledClosure n)

/-- The depth-16 fixed point used for all finite source audits. -/
def f4ScaledWeyl : Finset F4ScaledMat := f4ScaledClosure 16

/-- Four-times the exceptional displayed normal. -/
def f4ExceptionalNormalNumerator : F4ScaledMat :=
  !![1,0,1,0; 0,1,0,-1; 0,1,0,1; 1,0,1,-2]

/-- Exceptional displayed rank-three normal. -/
def f4ExceptionalNormal : F4Mat :=
  fun i j => (f4ExceptionalNormalNumerator i j : ℚ) / 4

/-- Rank-one displayed normal. -/
def f4RankOneNormal : F4Mat :=
  !![0,0,0,0; 0,0,0,0; 0,0,0,0; 1,0,0,-1]

/-- For the rank-one normal, `2 * Tr(X A1)` in the source is this integer
when the stored matrix is `2X`. -/
def f4RankOneScore2 (X : F4ScaledMat) : ℤ := X 0 3 - X 3 3

/-- For the exceptional normal, `8 * Tr(X A)` in the source is this integer
when the stored matrix is `2X`. -/
def f4ExceptionalScore8 (X : F4ScaledMat) : ℤ :=
  ∑ i : F4Fin, ∑ j : F4Fin,
    X i j * f4ExceptionalNormalNumerator j i

/-- Count closure elements on which `(AB)/2` would truncate for a generator.
Zero means the scaled operation agrees entrywise with exact rational matrix
multiplication on the whole closure. -/
def f4ScaledDivisionViolationCount (G : F4ScaledMat) : Nat :=
  (f4ScaledWeyl.filter (fun X => decide
    (2 • f4ScaledMul X G ≠ X * G))).card

/-- One shared native certificate for all expensive finite enumeration facts. -/
theorem f4FiniteNativeBundle :
    let W := f4ScaledClosure 16
    W.card = 1152 ∧
    f4ScaledClosure 17 = W ∧
    (W.filter (fun X => decide (2 < f4RankOneScore2 X))).card = 0 ∧
    (W.filter (fun X => decide (f4RankOneScore2 X = 2))).card = 288 ∧
    (W.filter (fun X => decide (8 < f4ExceptionalScore8 X))).card = 0 ∧
    (W.filter (fun X => decide (f4ExceptionalScore8 X = 8))).card = 36 ∧
    f4ScaledDivisionViolationCount f4ScaledGenerator1 = 0 ∧
    f4ScaledDivisionViolationCount f4ScaledGenerator2 = 0 := by
  native_decide

/-- Exact order certificate for the displayed-generator closure. -/
theorem f4Weyl_card : f4ScaledWeyl.card = 1152 := by
  simpa [f4ScaledWeyl] using f4FiniteNativeBundle.1

/-- Depth 16 is already a fixed point. -/
theorem f4Weyl_stable : f4ScaledClosure 17 = f4ScaledWeyl := by
  simpa [f4ScaledWeyl] using f4FiniteNativeBundle.2.1

/-- The scaled group computation performs no truncating division by generator 1. -/
theorem f4Generator1_exact_scaled_mul :
    f4ScaledDivisionViolationCount f4ScaledGenerator1 = 0 := by
  exact f4FiniteNativeBundle.2.2.2.2.2.2.1

/-- The scaled group computation performs no truncating division by generator 2. -/
theorem f4Generator2_exact_scaled_mul :
    f4ScaledDivisionViolationCount f4ScaledGenerator2 = 0 := by
  exact f4FiniteNativeBundle.2.2.2.2.2.2.2

/-- Exact rank-one support/active-count audit. -/
theorem f4RankOne_support_certificate :
    (f4ScaledWeyl.filter (fun X => decide (2 < f4RankOneScore2 X))).card = 0 ∧
    (f4ScaledWeyl.filter (fun X => decide (f4RankOneScore2 X = 2))).card = 288 := by
  constructor
  · simpa [f4ScaledWeyl] using f4FiniteNativeBundle.2.2.1
  · simpa [f4ScaledWeyl] using f4FiniteNativeBundle.2.2.2.1

/-- Exact exceptional support/active-count audit. -/
theorem f4Exceptional_support_certificate :
    (f4ScaledWeyl.filter (fun X => decide (8 < f4ExceptionalScore8 X))).card = 0 ∧
    (f4ScaledWeyl.filter (fun X => decide (f4ExceptionalScore8 X = 8))).card = 36 := by
  constructor
  · simpa [f4ScaledWeyl] using f4FiniteNativeBundle.2.2.2.2.1
  · simpa [f4ScaledWeyl] using f4FiniteNativeBundle.2.2.2.2.2.1

/-- Rational trace pairing used by the source. -/
def f4TracePair (X A : F4Mat) : ℚ :=
  ∑ i : F4Fin, ∑ j : F4Fin, X i j * A j i

/-- Outer product used for the explicit rank-one normal certificate. -/
def f4Outer (u v : F4Vec) : F4Mat := fun i j => u i * v j

def f4E3 : F4Vec := ![0,0,0,1]
def f4RankOneCovector : F4Vec := ![1,0,0,-1]

theorem f4RankOne_outer_certificate :
    f4RankOneNormal = f4Outer f4E3 f4RankOneCovector := by
  native_decide

/-- A nonzero 3x3 minor of the exceptional normal. -/
def f4ExceptionalMinor : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1/4,0,0; 0,1/4,-1/4; 0,1/4,1/4]

/-- Full determinant zero plus a nonzero 3x3 minor is the explicit algebraic
rank-three certificate used by this formalization. -/
theorem f4Exceptional_rankThree_certificate :
    f4ExceptionalNormal.det = 0 ∧ f4ExceptionalMinor.det = 1 / 32 := by
  native_decide

/-- Standard Euclidean F4 simple-root coordinate matrix used by the source. -/
def f4SimpleRootMatrix : F4Mat :=
  !![0,0,0,1/2; 1,0,0,-1/2; -1,1,0,-1/2; 0,-1,1,-1/2]

def f4SimpleRootMatrixInv : F4Mat :=
  !![1,1,0,0; 2,1,1,0; 3,1,1,1; 2,0,0,0]

theorem f4SimpleRoot_inverse_certificate :
    f4SimpleRootMatrix * f4SimpleRootMatrixInv = 1 ∧
      f4SimpleRootMatrixInv * f4SimpleRootMatrix = 1 := by
  native_decide

/-- Folded simple-root coordinate form printed by the source verifier. -/
def f4ExceptionalFoldedCoordinates : F4Mat :=
  !![0,1/2,-1/4,0; 0,1/2,0,-1/4; -1/2,3/2,-1/2,0; -1/2,1/2,0,0]

theorem f4Exceptional_coordinate_conversion :
    f4SimpleRootMatrixInv * f4ExceptionalNormal * f4SimpleRootMatrix =
      f4ExceptionalFoldedCoordinates := by
  native_decide

abbrev E6Fin := Fin 6
abbrev E6Mat := Matrix E6Fin E6Fin ℚ
abbrev E6xF4Mat := Matrix E6Fin F4Fin ℚ

def f4E6Gram : E6Mat :=
  !![2,0,-1,0,0,0; 0,2,0,-1,0,0; -1,0,2,-1,0,0;
     0,-1,-1,2,-1,0; 0,0,0,-1,2,-1; 0,0,0,0,-1,2]

def f4FoldIncidence : E6xF4Mat :=
  !![1,0,0,0; 0,0,0,1; 0,1,0,0; 0,0,1,0; 0,1,0,0; 1,0,0,0]

theorem f4FoldedGram_certificate :
    f4FoldIncidence.transpose * f4E6Gram * f4FoldIncidence =
      2 • (f4SimpleRootMatrix.transpose * f4SimpleRootMatrix) := by
  native_decide

end FormalResearch.QID
