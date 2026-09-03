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

/-- Exact null vector of the radical-free chirality matrix. -/
def chiralityKernelVec : Fin 3 → Int := ![1, 1, -1]

theorem chiralityKernelVec_nonzero : chiralityKernelVec ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  norm_num [chiralityKernelVec] at h0

theorem chiralityK_kernel : chiralityK *ᵥ chiralityKernelVec = 0 := by
  native_decide

/-- A nonzero two-by-two minor, using rows 0,2 and columns 0,1. -/
def chiralityMinor2 : Matrix (Fin 2) (Fin 2) Int :=
  !![-1, -1;
      1, -1]

def det2 (A : Matrix (Fin 2) (Fin 2) Int) : Int :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

theorem chiralityMinor2_det : det2 chiralityMinor2 = 2 := by
  native_decide

/-- The matrix trace vanishes, consistent with the conjugate nonzero pair. -/
def trace3 (A : Matrix (Fin 3) (Fin 3) Int) : Int := ∑ i, A i i

theorem chiralityK_trace : trace3 chiralityK = 0 := by
  native_decide

end FormalResearch.QIA
