import Mathlib

namespace FormalResearch.QID

def N5 : Matrix (Fin 5) (Fin 5) Int :=
  !![ 1, -1,  1,  1,  0;
      0, -2,  2,  0, -1;
      0,  2, -2,  0, -1;
     -1, -1, -1, -1,  0;
      0,  0,  0,  0,  1]

def N5minor : Matrix (Fin 4) (Fin 4) Int :=
  !![ 1, -1,  1,  0;
      0, -2,  2, -1;
      0,  2, -2, -1;
     -1, -1, -1,  0]

theorem N5_det_zero : N5.det = 0 := by
  native_decide

theorem N5minor_det : N5minor.det = 8 := by
  native_decide

end FormalResearch.QID
