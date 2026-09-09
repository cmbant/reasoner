import Mathlib

namespace FormalResearch.QID

/-!
# QI-D exceptional F4 facet: exact finite certificate core

This module matches the exact source verifier
`cmbant/QIprojects:QI-D/code/certify_F4_exceptional_facet.py`, audited at
QIprojects main `51d23f262d3da3b90e512ede95b20757b41bdff5` (source blob
`c0c3534128658bb18c5563e1815893e3272fa7e0`, committed verification-log blob
`43be8688e2361921906e4e218806ecdc57ec8e94`).

For efficient kernel-checked finite enumeration we represent a Weyl matrix `X`
by the integer matrix `2X`.  The two displayed source generators therefore have
entries `±1`; multiplication of scaled matrices is `(AB)/2`.  Lean checks that
this integer operation agrees exactly with rational matrix multiplication on
the entire generated closure.

The finite native bundle checks in one shared computation:

* the displayed-generator closure stabilizes with `1152` matrices;
* scaled multiplication agrees with the displayed rational generators;
* the rank-one displayed facet has support `1` and `288` active matrices;
* the exceptional displayed normal has support `1` and `36` active matrices.

Separate small exact checks certify the displayed rank-one/rank-three algebraic
normal data and the folded E6/F4 coordinate conversion.

The active affine-dimension-15 witness is intentionally split into a follow-up
module.  The literature classification theorem saying there are exactly two
facet orbits remains external.
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

/-- Multiplication in the `2X` representation.  On the generated F4 closure
all entrywise numerators are even; an exact compatibility audit below checks
that integer division by two agrees with rational matrix multiplication. -/
def f4ScaledMul (A B : F4ScaledMat) : F4ScaledMat :=
  fun i j => (∑ k : F4Fin, A i k * B k j) / 2

/-- Convert a scaled integer matrix back to its rational matrix. -/
def f4ScaledToRat (A : F4ScaledMat) : F4Mat :=
  fun i j => (A i j : ℚ) / 2

/-- Displayed rational source generators. -/
def f4Generator1 : F4Mat := f4ScaledToRat f4ScaledGenerator1
def f4Generator2 : F4Mat := f4ScaledToRat f4ScaledGenerator2

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

/-- Rank-one displayed normal, kept integral. -/
def f4RankOneNormal : F4Mat :=
  !![0,0,0,0; 0,0,0,0; 0,0,0,0; 1,0,0,-1]

/-- Four-times the exceptional displayed normal. -/
def f4ExceptionalNormalNumerator : Matrix F4Fin F4Fin ℤ :=
  !![1,0,1,0; 0,1,0,-1; 0,1,0,1; 1,0,1,-2]

/-- Exceptional displayed rank-three normal. -/
def f4ExceptionalNormal : F4Mat :=
  fun i j => (f4ExceptionalNormalNumerator i j : ℚ) / 4

/-- Integer numerator for `2 * Tr(X A1)` when the scaled matrix is `2X`. -/
def f4RankOneScoreNumerator (X : F4ScaledMat) : ℤ :=
  ∑ i : F4Fin, ∑ j : F4Fin,
    X i j * ((4 * f4RankOneNormal j i : ℚ).num)

/-- More directly, for the integral rank-one normal the source score is this
integer divided by two. -/
def f4RankOneScore2 (X : F4ScaledMat) : ℤ :=
  ∑ i : F4Fin, ∑ j : F4Fin,
    X i j * (if (j = 3 ∧ i = 0) then 1 else if (j = 3 ∧ i = 3) then -1 else 0)

/-- For the exceptional normal, `8 * Tr(X A)` is this integer. -/
def f4ExceptionalScore8 (X : F4ScaledMat) : ℤ :=
  ∑ i : F4Fin, ∑ j : F4Fin,
    X i j * f4ExceptionalNormalNumerator j i

/-- A mismatch count for the scaled multiplication/rational multiplication
bridge on one generator. -/
def f4ScaledMulMismatchCount
    (Gz : F4ScaledMat) (Gq : F4Mat) : Nat :=
  (f4ScaledWeyl.filter (fun X => decide
    (f4ScaledToRat (f4ScaledMul X Gz) ≠ f4ScaledToRat X * Gq))).card

/-- The expensive finite facts are bundled so the 1152-element closure is
shared by one native evaluation rather than recomputed theorem by theorem. -/
theorem f4FiniteNativeBundle :
    let W := f4ScaledClosure 16
    W.card = 1152 ∧
    f4ScaledClosure 17 = W ∧
    (W.filter (fun X => decide (2 < f4RankOneScore2 X))).card = 0 ∧
    (W.filter (fun X => decide (f4RankOneScore2 X = 2))).card = 288 ∧
    (W.filter (fun X => decide (8 < f4ExceptionalScore8 X))).card = 0 ∧
    (W.filter (fun X => decide (f4ExceptionalScore8 X = 8))).card = 36 ∧
    f4ScaledMulMismatchCount f4ScaledGenerator1 f4Generator1 = 0 ∧
    f4ScaledMulMismatchCount f4ScaledGenerator2 f4Generator2 = 0 := by
  native_decide

/-- Exact order certificate for the displayed-generator closure. -/
theorem f4Weyl_card : f4ScaledWeyl.card = 1152 := by
  simpa [f4ScaledWeyl] using f4FiniteNativeBundle.1

/-- Depth 16 is already a fixed point of the closure. -/
theorem f4Weyl_stable : f4ScaledClosure 17 = f4ScaledWeyl := by
  simpa [f4ScaledWeyl] using f4FiniteNativeBundle.2.1

/-- Scaled multiplication agrees with rational multiplication by generator 1
throughout the generated closure. -/
theorem f4Generator1_scaled_bridge :
    f4ScaledMulMismatchCount f4ScaledGenerator1 f4Generator1 = 0 := by
  exact f4FiniteNativeBundle.2.2.2.2.2.2.1

/-- Scaled multiplication agrees with rational multiplication by generator 2
throughout the generated closure. -/
theorem f4Generator2_scaled_bridge :
    f4ScaledMulMismatchCount f4ScaledGenerator2 f4Generator2 = 0 := by
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

/-- The integer exceptional score is exactly eight times the rational source
trace pairing after conversion. -/
theorem f4ExceptionalScore8_eq_trace (X : F4ScaledMat) :
    (f4ExceptionalScore8 X : ℚ) =
      8 * f4TracePair (f4ScaledToRat X) f4ExceptionalNormal := by
  simp [f4ExceptionalScore8, f4TracePair, f4ScaledToRat,
    f4ExceptionalNormal, Finset.mul_sum]
  ring

/-- The rank-one integer score is exactly twice the rational source trace
pairing after conversion. -/
theorem f4RankOneScore2_eq_trace (X : F4ScaledMat) :
    (f4RankOneScore2 X : ℚ) =
      2 * f4TracePair (f4ScaledToRat X) f4RankOneNormal := by
  fin_cases X <;> simp [f4RankOneScore2, f4TracePair, f4ScaledToRat,
    f4RankOneNormal]

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
