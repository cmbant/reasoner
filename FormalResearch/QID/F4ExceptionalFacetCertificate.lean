import Mathlib

namespace FormalResearch.QID

/-!
# QI-D exceptional F4 facet: parameterized exact finite certificate

Source authority:
`cmbant/QIprojects:QI-D/code/certify_F4_exceptional_facet.py`, audited at
QIprojects main `acfb127df5cc5998fb91cd00ea6e5311d1462e39`.

The source verifier generates `W(F4)` from two displayed rational `4 x 4`
generators and checks exact support/active data for a rank-one facet and the
rank-three exceptional facet.

A literal rational breadth-first closure is unnecessarily expensive in Lean.
This module uses the exact three-coset decomposition of the same generated set:
384 signed-permutation matrices times three fixed right-coset representatives.
The two source generators act by six explicit finite transitions between these
cosets. Lean checks, rather than assumes, that:

* the transition system reaches all `3 * 384 = 1152` parameters by word depth 16;
* all 1152 parameters give distinct exact matrices;
* each transition agrees exactly with right multiplication by the corresponding
  displayed source generator;
* the rank-one normal has support `1` with `288` active matrices;
* the exceptional rank-three normal has support `1` with `36` active matrices.

Small exact algebraic checks also certify the displayed normal ranks and folded
E6/F4 coordinate conversion.

The affine-dimension-15 facet witness is split into a follow-up module. The
literature theorem that there are exactly two facet orbits remains external.
-/

abbrev F4Fin := Fin 4
abbrev F4B4 := Equiv.Perm F4Fin × (F4Fin → Bool)
abbrev F4Param := Fin 3 × F4B4
abbrev F4IntMat := Matrix F4Fin F4Fin ℤ
abbrev F4RatMat := Matrix F4Fin F4Fin ℚ
abbrev F4RatVec := F4Fin → ℚ

/-- Signed-permutation matrix for the `B4` subgroup. -/
def f4B4Matrix (a : F4B4) : F4IntMat :=
  fun r c =>
    if r = a.1 c then
      if a.2 c then -1 else 1
    else 0

/-- Right multiplication of signed-permutation data by a fixed signed
permutation `(q,t)`. The matrix compatibility needed below is checked globally
on all F4 parameters. -/
def f4B4Right (a : F4B4) (q : Equiv.Perm F4Fin) (t : F4Fin → Bool) : F4B4 :=
  (q.trans a.1, fun c => Bool.xor (t c) (a.2 (q c)))

/-- Fixed signed-permutation factors in the six coset/generator transitions. -/
def f4Q02 : Equiv.Perm F4Fin := Equiv.swap 1 3
def f4Q11 : Equiv.Perm F4Fin :=
  (Equiv.swap 2 3).trans (Equiv.swap 1 2)
def f4Q21 : Equiv.Perm F4Fin :=
  (Equiv.swap 1 3).trans (Equiv.swap 0 1)
def f4Q22 : Equiv.Perm F4Fin :=
  (Equiv.swap 0 3).trans (Equiv.swap 0 1)

def f4S02 : F4Fin → Bool := ![true, true, true, false]
def f4S11 : F4Fin → Bool := ![false, true, false, true]
def f4S21 : F4Fin → Bool := ![true, true, true, false]
def f4S22 : F4Fin → Bool := ![false, true, true, true]

/-- Identity signed permutation. -/
def f4B4Identity : F4B4 := (Equiv.refl F4Fin, fun _ => false)

/-- Generator transition on the three cosets. `false` is source generator 1;
`true` is source generator 2. -/
def f4ParamStep (p : F4Param) (g2 : Bool) : F4Param :=
  match p.1.1, g2 with
  | 0, false => ⟨1, p.2⟩
  | 0, true  => ⟨1, f4B4Right p.2 f4Q02 f4S02⟩
  | 1, false => ⟨0, f4B4Right p.2 f4Q11 f4S11⟩
  | 1, true  => ⟨2, p.2⟩
  | _, false => ⟨2, f4B4Right p.2 f4Q21 f4S21⟩
  | _, true  => ⟨0, f4B4Right p.2 f4Q22 f4S22⟩

/-- Breadth closure of the finite parameter transition system. -/
def f4ParamClosureStep (s : Finset F4Param) : Finset F4Param :=
  s ∪ s.image (fun p => f4ParamStep p false) ∪
    s.image (fun p => f4ParamStep p true)

def f4ParamClosure : Nat → Finset F4Param
  | 0 => {⟨0, f4B4Identity⟩}
  | n + 1 => f4ParamClosureStep (f4ParamClosure n)

/-- All 1152 finite parameters are reached by source-generator words of length
at most 16. -/
theorem f4Param_reachable_all : f4ParamClosure 16 = Finset.univ := by
  native_decide

/-- Twice the first displayed rational source generator. -/
def f4ScaledGenerator1 : F4IntMat :=
  !![ 1, -1,  1,  1;
     -1, -1, -1,  1;
      1,  1, -1,  1;
      1, -1, -1, -1]

/-- Twice the second displayed rational source generator. -/
def f4ScaledGenerator2 : F4IntMat :=
  !![-1,  1, -1, -1;
      1, -1, -1, -1;
     -1, -1,  1, -1;
      1,  1,  1, -1]

/-- Twice the third right-coset representative `G1*G2`. -/
def f4ScaledRep2 : F4IntMat :=
  !![-1, 1,  1, -1;
      1, 1,  1,  1;
      1, 1, -1, -1;
     -1, 1, -1,  1]

/-- Twice each right-coset representative: `I`, `G1`, `G1*G2`. -/
def f4ScaledRep (c : Fin 3) : F4IntMat :=
  match c.1 with
  | 0 => !![2,0,0,0; 0,2,0,0; 0,0,2,0; 0,0,0,2]
  | 1 => f4ScaledGenerator1
  | _ => f4ScaledRep2

/-- Exact scaled matrix `2X` represented by a finite F4 parameter. -/
def f4ParamScaled (p : F4Param) : F4IntMat :=
  f4B4Matrix p.2 * f4ScaledRep p.1

/-- Source generator selected by the transition flag. -/
def f4ScaledGenerator (g2 : Bool) : F4IntMat :=
  if g2 then f4ScaledGenerator2 else f4ScaledGenerator1

/-- Entrywise doubling of an integer matrix. -/
def f4Twice (M : F4IntMat) : F4IntMat := fun i j => 2 * M i j

/-- Count transition/matrix mismatches. Since matrices store `2X`, exact right
multiplication by a generator satisfies `2 * scaled(next) = scaled(X) * scaled(G)`. -/
def f4TransitionMismatchCount (g2 : Bool) : Nat :=
  (Finset.univ.filter (fun p : F4Param => decide
    (f4Twice (f4ParamScaled (f4ParamStep p g2)) ≠
      f4ParamScaled p * f4ScaledGenerator g2))).card

/-- The six transition formulas agree with both displayed source generators on
all 1152 parameters. -/
theorem f4Transition_exact :
    f4TransitionMismatchCount false = 0 ∧
      f4TransitionMismatchCount true = 0 := by
  native_decide

/-- The parameterization contains 1152 distinct exact matrices. -/
def f4MatrixImage : Finset F4IntMat := Finset.univ.image f4ParamScaled

theorem f4MatrixImage_card : f4MatrixImage.card = 1152 := by
  native_decide

/-- Exact generated-set certificate matching the source BFS claim. -/
theorem f4DisplayedGenerators_generate_1152 :
    f4ParamClosure 16 = Finset.univ ∧
    f4TransitionMismatchCount false = 0 ∧
    f4TransitionMismatchCount true = 0 ∧
    f4MatrixImage.card = 1152 := by
  exact ⟨f4Param_reachable_all, f4Transition_exact.1,
    f4Transition_exact.2, f4MatrixImage_card⟩

/-- Integral rank-one displayed normal. -/
def f4RankOneNormalInt : F4IntMat :=
  !![0,0,0,0; 0,0,0,0; 0,0,0,0; 1,0,0,-1]

/-- Four times the exceptional displayed normal. -/
def f4ExceptionalNormalNumerator : F4IntMat :=
  !![1,0,1,0; 0,1,0,-1; 0,1,0,1; 1,0,1,-2]

/-- Integer trace numerator `sum S_ij N_ji`. -/
def f4IntTrace (S N : F4IntMat) : ℤ :=
  ∑ i : F4Fin, ∑ j : F4Fin, S i j * N j i

/-- For `S=2X`, this is `2 Tr(X A1)`. -/
def f4RankOneScore2 (p : F4Param) : ℤ :=
  f4IntTrace (f4ParamScaled p) f4RankOneNormalInt

/-- For `S=2X`, this is `8 Tr(X Aexc)`. -/
def f4ExceptionalScore8 (p : F4Param) : ℤ :=
  f4IntTrace (f4ParamScaled p) f4ExceptionalNormalNumerator

/-- Rank-one support and active-count certificate from all 1152 generated elements. -/
theorem f4RankOne_support_certificate :
    (Finset.univ.filter (fun p : F4Param => decide (2 < f4RankOneScore2 p))).card = 0 ∧
    (Finset.univ.filter (fun p : F4Param => decide (f4RankOneScore2 p = 2))).card = 288 := by
  native_decide

/-- Exceptional support and active-count certificate from all 1152 generated elements. -/
theorem f4Exceptional_support_certificate :
    (Finset.univ.filter (fun p : F4Param => decide (8 < f4ExceptionalScore8 p))).card = 0 ∧
    (Finset.univ.filter (fun p : F4Param => decide (f4ExceptionalScore8 p = 8))).card = 36 := by
  native_decide

/-- Convert a scaled matrix back to the rational source matrix. -/
def f4ScaledToRat (S : F4IntMat) : F4RatMat :=
  fun i j => (S i j : ℚ) / 2

def f4TracePair (X A : F4RatMat) : ℚ :=
  ∑ i : F4Fin, ∑ j : F4Fin, X i j * A j i

def f4RankOneNormal : F4RatMat :=
  fun i j => (f4RankOneNormalInt i j : ℚ)

def f4ExceptionalNormal : F4RatMat :=
  fun i j => (f4ExceptionalNormalNumerator i j : ℚ) / 4

/-- Finite audit that the integral support scores are exactly the displayed
rational trace pairings on every generated matrix. -/
def f4TraceBridgeMismatchCount : Nat :=
  (Finset.univ.filter (fun p : F4Param => decide
    ((f4RankOneScore2 p : ℚ) ≠
        2 * f4TracePair (f4ScaledToRat (f4ParamScaled p)) f4RankOneNormal ∨
     (f4ExceptionalScore8 p : ℚ) ≠
        8 * f4TracePair (f4ScaledToRat (f4ParamScaled p)) f4ExceptionalNormal))).card

theorem f4TraceBridge_exact : f4TraceBridgeMismatchCount = 0 := by
  native_decide

/-- Explicit rank-one factorization. -/
def f4Outer (u v : F4RatVec) : F4RatMat := fun i j => u i * v j
def f4E3 : F4RatVec := ![0,0,0,1]
def f4RankOneCovector : F4RatVec := ![1,0,0,-1]

theorem f4RankOne_outer_certificate :
    f4RankOneNormal = f4Outer f4E3 f4RankOneCovector := by
  native_decide

/-- Nonzero 3x3 minor of the exceptional normal. -/
def f4ExceptionalMinor : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1/4,0,0; 0,1/4,-1/4; 0,1/4,1/4]

theorem f4Exceptional_rankThree_certificate :
    f4ExceptionalNormal.det = 0 ∧ f4ExceptionalMinor.det = 1 / 32 := by
  native_decide

/-- Standard F4 simple-root coordinate matrix and explicit inverse. -/
def f4SimpleRootMatrix : F4RatMat :=
  !![0,0,0,1/2; 1,0,0,-1/2; -1,1,0,-1/2; 0,-1,1,-1/2]

def f4SimpleRootMatrixInv : F4RatMat :=
  !![1,1,0,0; 2,1,1,0; 3,1,1,1; 2,0,0,0]

theorem f4SimpleRoot_inverse_certificate :
    f4SimpleRootMatrix * f4SimpleRootMatrixInv = 1 ∧
      f4SimpleRootMatrixInv * f4SimpleRootMatrix = 1 := by
  native_decide

/-- Folded simple-root coordinate form printed by the source verifier. -/
def f4ExceptionalFoldedCoordinates : F4RatMat :=
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

/-- First-gate bundle. -/
theorem f4Exceptional_finite_core_certificate :
    f4MatrixImage.card = 1152 ∧
    (Finset.univ.filter (fun p : F4Param => decide (2 < f4RankOneScore2 p))).card = 0 ∧
    (Finset.univ.filter (fun p : F4Param => decide (f4RankOneScore2 p = 2))).card = 288 ∧
    (Finset.univ.filter (fun p : F4Param => decide (8 < f4ExceptionalScore8 p))).card = 0 ∧
    (Finset.univ.filter (fun p : F4Param => decide (f4ExceptionalScore8 p = 8))).card = 36 := by
  exact ⟨f4MatrixImage_card,
    f4RankOne_support_certificate.1,
    f4RankOne_support_certificate.2,
    f4Exceptional_support_certificate.1,
    f4Exceptional_support_certificate.2⟩

end FormalResearch.QID
