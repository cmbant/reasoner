import Mathlib
import FormalResearch.QIA.FourQubitMatrix
import FormalResearch.QIA.PrintedChiralityMatrix

namespace FormalResearch.QIA

open Complex

/-- The exact coordinate map from the original three pairing tensors to the
orthonormal invariant-qutrit basis.  If `x=sqrt 2`, `y=sqrt 3`, its columns are
`v₁,v₂,v₃` expressed in the normalized Gram--Schmidt basis. -/
def pairingToPrinted (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![2, 1, 1;
     0, y, y/3;
     0, 0, 2*x*y/3]

/-- Explicit inverse, written without division by radicals by using
`x²=2`, `y²=3`. -/
def pairingToPrintedInv (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1/2, -y/6, -x*y/12;
     0, y/3, -x*y/12;
     0, 0, x*y/4]

/-- Integral chirality matrix transported to complex coefficients with the
physical normalization `3 i / 8`. -/
def scaledIntegralChirality : Matrix (Fin 3) (Fin 3) ℂ :=
  (3 * I / 8) • (fun i j => (chiralityK i j : ℂ))

/-- The integral pairing-coordinate matrix and the printed Hermitian matrix are
exactly the same operator under the Gram--Schmidt change of basis. -/
theorem pairing_printed_intertwining (x y : ℝ) (hx : x^2 = 2) (hy : y^2 = 3) :
    printedA0xy x y * pairingToPrinted x y =
      pairingToPrinted x y * scaledIntegralChirality := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [printedA0xy, pairingToPrinted, scaledIntegralChirality,
      chiralityK, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    push_cast [hx, hy] <;>
    ring_nf at hx hy ⊢ <;>
    nlinarith

/-- The displayed coordinate change is genuinely invertible under the radical
relations used in the paper. -/
theorem pairingToPrinted_right_inverse (x y : ℝ) (hx : x^2 = 2) (hy : y^2 = 3) :
    pairingToPrinted x y * pairingToPrintedInv x y = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairingToPrinted, pairingToPrintedInv, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    push_cast [hx, hy] <;>
    ring_nf at hx hy ⊢ <;>
    nlinarith

/-- Two-sided inverse certificate for the same change of basis. -/
theorem pairingToPrinted_left_inverse (x y : ℝ) (hx : x^2 = 2) (hy : y^2 = 3) :
    pairingToPrintedInv x y * pairingToPrinted x y = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairingToPrinted, pairingToPrintedInv, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    push_cast [hx, hy] <;>
    ring_nf at hx hy ⊢ <;>
    nlinarith

/-- Concrete specification bridge for the matrix printed in the manuscript. -/
theorem printedA0_is_pairing_chirality :
    printedA0 * pairingToPrinted (Real.sqrt 2) (Real.sqrt 3) =
      pairingToPrinted (Real.sqrt 2) (Real.sqrt 3) * scaledIntegralChirality :=
  pairing_printed_intertwining _ _ sqrt2_sq sqrt3_sq

end FormalResearch.QIA
