import Mathlib
import FormalResearch.QIC.Endpoint14Data

namespace FormalResearch.QIC

open Polynomial Matrix

noncomputable section

/-- Remove the universal `t^2` factor from one endpoint entry. -/
def r2b (a b c : Int) : Int[X] := C a + C b * X + C c * X^2

/-- The fixed endpoint minor after removing the common `t^2` from every entry. -/
def endpointReducedPolyB : Matrix Fin14 Fin14 Int[X] :=
  !![      r2b 0 0 0, r2b 0 0 0, r2b 8 (-4) 0, r2b (-4) 4 0, r2b (-4) 8 0, r2b 2 (-8) 0, r2b (-18) 0 0, r2b 18 0 0, r2b 0 0 0, r2b 0 0 0, r2b (-8) 8 0, r2b 8 (-8) 0, r2b 22 (-22) 0, r2b (-22) 22 0;
      r2b 4 (-4) 0, r2b 4 (-8) 4, r2b 4 (-4) 0, r2b 0 0 0, r2b (-16) 8 0, r2b (-16) 8 0, r2b (-24) 16 0, r2b (-8) 32 (-16), r2b 0 0 0, r2b 0 0 0, r2b (-8) 4 0, r2b 8 (-12) 4, r2b 6 (-6) 0, r2b (-38) 54 (-16);
      r2b 0 0 0, r2b 0 0 0, r2b 0 (-4) 0, r2b 0 4 0, r2b 0 0 0, r2b 0 0 0, r2b 8 0 0, r2b (-8) 0 0, r2b 4 (-4) 0, r2b 0 0 0, r2b (-4) 4 0, r2b 4 (-4) 0, r2b (-10) 10 0, r2b 10 (-10) 0;
      r2b (-4) 4 0, r2b (-4) 8 (-4), r2b 16 (-8) 0, r2b 8 (-8) 4, r2b (-6) 2 0, r2b (-8) 8 (-2), r2b (-16) 2 0, r2b 10 6 (-2), r2b 0 0 0, r2b (-4) 8 (-4), r2b 0 0 0, r2b 8 (-12) 4, r2b (-10) 10 0, r2b 10 (-10) 0;
      r2b 0 0 0, r2b 0 0 0, r2b 0 0 0, r2b 0 0 0, r2b 0 (-8) 0, r2b 0 8 0, r2b 8 0 0, r2b (-8) 0 0, r2b 4 (-4) 0, r2b 0 0 0, r2b (-8) 8 0, r2b 8 (-8) 0, r2b (-8) 8 0, r2b 8 (-8) 0;
      r2b 8 (-8) 0, r2b 8 (-16) 8, r2b (-60) 28 0, r2b (-64) 88 (-28), r2b 38 (-22) 0, r2b 28 (-40) 14, r2b (-16) 2 0, r2b 10 6 (-2), r2b 0 0 0, r2b (-4) 8 (-4), r2b (-20) 20 0, r2b (-4) 16 (-12), r2b 0 0 0, r2b 16 (-24) 8;
      r2b 0 0 0, r2b 0 0 0, r2b 0 0 0, r2b 0 0 0, r2b 16 (-8) 0, r2b (-8) 16 (-8), r2b (-8) 0 0, r2b 8 0 0, r2b 4 (-4) 0, r2b (-4) 8 (-4), r2b (-16) 8 0, r2b 16 (-24) 8, r2b (-16) 8 0, r2b 16 (-24) 8;
      r2b 0 0 0, r2b 0 0 0, r2b 0 0 0, r2b 0 0 0, r2b (-32) 16 0, r2b (-32) 80 (-32), r2b (-16) 0 0, r2b 16 0 0, r2b 8 (-8) 0, r2b 0 0 0, r2b (-24) 16 0, r2b 8 (-8) 0, r2b (-16) 16 0, r2b 16 (-16) 0;
      r2b 0 0 0, r2b 0 0 0, r2b 8 (-4) 0, r2b (-4) 8 (-4), r2b 0 0 0, r2b 0 0 0, r2b (-8) 0 0, r2b 8 0 0, r2b 4 (-4) 0, r2b (-4) 8 (-4), r2b (-8) 4 0, r2b 8 (-12) 4, r2b (-20) 10 0, r2b 20 (-30) 10;
      r2b 0 0 0, r2b 0 0 0, r2b (-16) 8 0, r2b (-16) 40 (-16), r2b 0 0 0, r2b 0 0 0, r2b (-16) 0 0, r2b 16 0 0, r2b 8 (-8) 0, r2b 0 0 0, r2b (-8) 8 0, r2b 8 (-8) 0, r2b (-24) 20 0, r2b 16 (-16) 0;
      r2b 0 0 0, r2b 0 0 0, r2b 0 (-4) 0, r2b 0 8 (-4), r2b (-12) 8 0, r2b 6 (-16) 8, r2b 18 0 0, r2b (-18) 0 0, r2b 0 0 0, r2b 0 0 0, r2b (-16) 8 0, r2b 16 (-24) 8, r2b 44 (-22) 0, r2b (-44) 66 (-22);
      r2b (-32) 32 0, r2b (-32) 64 (-32), r2b 112 (-56) 0, r2b 112 (-152) 48, r2b (-16) 16 0, r2b 0 0 0, r2b 48 (-32) 0, r2b 16 (-64) 32, r2b 0 0 0, r2b 0 0 0, r2b 24 (-24) 0, r2b 56 (-96) 40, r2b 56 (-28) 0, r2b (-32) 48 (-16);
      r2b (-8) 8 0, r2b (-4) 12 (-8), r2b 20 (-8) 0, r2b 12 (-16) 8, r2b (-14) 2 0, r2b (-32) 24 (-2), r2b (-56) 18 0, r2b 18 38 (-18), r2b 0 0 0, r2b 0 0 0, r2b 0 0 0, r2b 0 0 0, r2b (-18) 18 0, r2b (-18) 36 (-18);
      r2b 16 (-16) 0, r2b 20 (-36) 16, r2b (-112) 52 0, r2b (-124) 168 (-52), r2b 46 (-22) 0, r2b 36 (-56) 22, r2b (-56) 18 0, r2b 18 38 (-18), r2b 0 0 0, r2b 0 0 0, r2b (-36) 36 0, r2b (-36) 72 (-36), r2b 0 0 0, r2b 0 0 0]

/-- QI-C's endpoint factorization after removing the universal `X^28`. -/
def expectedReducedPolyB : Int[X] :=
  C 195689447424 * (X - C 1)^8 * (X - C 2)^2 *
    (2 * X^3 - 3 * X^2 - X - 3) *
    (144 * X^4 - 60 * X^3 - 841 * X^2 + 633 * X + 258)

set_option maxHeartbeats 2000000 in
/-- Bird's polynomial-time determinant certificate for the exact fixed minor. -/
theorem endpoint_reduced_det_bird_v2 :
    Matrix.det endpointReducedPolyB = expectedReducedPolyB := by
  rw [endpointReducedPolyB]
  unfold r2b
  eval_det
  ring

end

end FormalResearch.QIC
