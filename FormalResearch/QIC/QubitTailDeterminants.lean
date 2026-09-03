import Mathlib

namespace FormalResearch.QIC

open Polynomial

abbrev P := Polynomial Int

private def lin (a b : Int) : P := C a + C b * X

def tailPlus : Matrix (Fin 8) (Fin 8) P :=
  !![lin (-5) 4, lin 5 0, lin (-2) 0, lin (-14) (-16), lin 0 0, lin (-8) 4, lin 16 (-16), lin 0 0;
      lin 3 (-4), lin 1 4, lin 0 (-2), lin (-4) (-2), lin 4 (-4), lin (-4) 4, lin 0 0, lin 0 0;
      lin (-12) 8, lin 0 (-28), lin 14 14, lin (-4) (-2), lin 4 (-4), lin 12 (-12), lin (-8) 8, lin 0 0;
      lin 0 0, lin 0 0, lin 16 (-8), lin (-8) 0, lin 4 (-4), lin (-16) 8, lin (-16) 8, lin (-16) 8;
      lin 0 0, lin 8 (-4), lin 0 0, lin (-8) 0, lin 4 (-4), lin (-8) 4, lin (-20) 10, lin (-4) 2;
      lin (-4) 0, lin 4 (-4), lin 0 8, lin 6 0, lin 0 0, lin (-16) 8, lin 44 (-22), lin 12 (-6);
      lin 3 (-8), lin 1 8, lin 0 (-2), lin (-20) (-18), lin 0 0, lin 0 0, lin 18 (-18), lin 2 (-2);
      lin (-24) 16, lin 0 (-52), lin 14 22, lin (-20) (-18), lin 0 0, lin 36 (-36), lin 0 0, lin 14 4]

def tailMinus : Matrix (Fin 8) (Fin 8) P :=
  !![lin (-5) 4, lin (-3) 0, lin 14 0, lin 18 (-16), lin 0 0, lin 0 4, lin 16 (-16), lin (-16) 0;
      lin 3 (-4), lin (-7) 4, lin 8 (-2), lin 4 (-2), lin 4 (-4), lin (-4) 4, lin 0 0, lin 0 0;
      lin (-12) 8, lin 64 (-28), lin (-26) 14, lin 4 (-2), lin 4 (-4), lin 12 (-12), lin (-8) 8, lin 0 0;
      lin 0 0, lin 0 0, lin 48 (-24), lin 8 0, lin (-4) 4, lin 8 (-8), lin 0 (-8), lin (-48) 24;
      lin 0 0, lin 24 (-12), lin 0 0, lin 8 0, lin (-4) 4, lin 0 (-4), lin 4 (-10), lin (-12) 6;
      lin 28 (-32), lin (-108) 52, lin 16 (-8), lin (-42) 32, lin 0 0, lin (-40) 32, lin (-12) 6, lin 52 (-18);
      lin 3 (-8), lin (-7) 8, lin 24 (-2), lin 20 (-18), lin 0 0, lin 0 0, lin 18 (-18), lin (-14) (-2);
      lin (-24) 16, lin 120 (-52), lin (-26) 22, lin 20 (-18), lin 0 0, lin 36 (-36), lin 0 0, lin (-26) 4]

def qPlus : P :=
  C 2448 * X^5 + C 11018 * X^4 - C 8079 * X^3 - C 68674 * X^2 - C 31772 * X + C 76323

def qMinus : P :=
  C 20304 * X^5 - C 126366 * X^4 + C 249625 * X^3 - C 195988 * X^2 + C 51862 * X - C 2181

/-- Exact all-qubit odd-tail determinant certificate from the compact 8x8 reduction. -/
theorem tailPlus_det :
    tailPlus.det = C 6144 * (X - C 2) * (X - C 1) * qPlus := by
  native_decide

/-- Exact all-qubit even-tail determinant certificate from the compact 8x8 reduction. -/
theorem tailMinus_det :
    tailMinus.det = -(C 6144 * (X - C 2) * (X - C 1) * qMinus) := by
  native_decide

end FormalResearch.QIC
