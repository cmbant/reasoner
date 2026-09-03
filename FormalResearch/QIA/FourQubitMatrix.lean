import Mathlib

namespace FormalResearch.QIA

def chiralityK : Matrix (Fin 3) (Fin 3) Int :=
  !![-1, -1, -2;
      1,  1,  2;
      1, -1,  0]

theorem chiralityK_cubic : chiralityK ^ 3 = -(4 • chiralityK) := by
  native_decide

theorem chiralityK_ne_zero : chiralityK ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 3)) (0 : Fin 3)
  norm_num [chiralityK] at h00

end FormalResearch.QIA
