import Mathlib
import FormalResearch.QIA.PrintedChiralityMatrix

namespace FormalResearch.QIA

open Complex

/-- Zero-eigenvalue vector for the radical-free printed matrix. -/
def printedVzero (x y : ℝ) : Fin 3 → ℂ :=
  ![-(x*y)/2, -x/2, 1]

/-- Positive-eigenvalue vector.  At `x=sqrt 2`, `y=sqrt 3` this is the
explicit eigenvector for eigenvalue `3/4`. -/
def printedVplus (x y : ℝ) : Fin 3 → ℂ :=
  ![(x*y/4) * (1 - I), (x/4) * (1 + 3*I), 1]

/-- Negative-eigenvalue vector, conjugate to the positive one. -/
def printedVminus (x y : ℝ) : Fin 3 → ℂ :=
  ![(x*y/4) * (1 + I), (x/4) * (1 - 3*I), 1]

lemma printedVzero_ne_zero (x y : ℝ) : printedVzero x y ≠ 0 := by
  intro h
  have h2 := congrFun h (2 : Fin 3)
  simp [printedVzero] at h2

lemma printedVplus_ne_zero (x y : ℝ) : printedVplus x y ≠ 0 := by
  intro h
  have h2 := congrFun h (2 : Fin 3)
  simp [printedVplus] at h2

lemma printedVminus_ne_zero (x y : ℝ) : printedVminus x y ≠ 0 := by
  intro h
  have h2 := congrFun h (2 : Fin 3)
  simp [printedVminus] at h2

/-- Exact zero eigenpair of the printed matrix. -/
theorem printedA0xy_zero_eigenpair (x y : ℝ) (hx : x^2 = 2) (hy : y^2 = 3) :
    printedA0xy x y *ᵥ printedVzero x y = 0 := by
  funext i
  fin_cases i <;>
    simp [printedA0xy, printedVzero, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    push_cast [hx, hy] <;>
    ring_nf at hx hy ⊢ <;>
    nlinarith

/-- Exact positive eigenpair of the printed matrix. -/
theorem printedA0xy_plus_eigenpair (x y : ℝ) (hx : x^2 = 2) (hy : y^2 = 3) :
    printedA0xy x y *ᵥ printedVplus x y =
      (3/4 : ℂ) • printedVplus x y := by
  funext i
  fin_cases i <;>
    simp [printedA0xy, printedVplus, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    push_cast [hx, hy] <;>
    ring_nf at hx hy ⊢ <;>
    nlinarith

/-- Exact negative eigenpair of the printed matrix. -/
theorem printedA0xy_minus_eigenpair (x y : ℝ) (hx : x^2 = 2) (hy : y^2 = 3) :
    printedA0xy x y *ᵥ printedVminus x y =
      (-3/4 : ℂ) • printedVminus x y := by
  funext i
  fin_cases i <;>
    simp [printedA0xy, printedVminus, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    push_cast [hx, hy] <;>
    ring_nf at hx hy ⊢ <;>
    nlinarith

/-- The three printed eigenvalues are realized by explicit nonzero vectors. -/
theorem printedA0_zero_eigenpair :
    printedA0 *ᵥ printedVzero (Real.sqrt 2) (Real.sqrt 3) = 0 :=
  printedA0xy_zero_eigenpair _ _ sqrt2_sq sqrt3_sq

theorem printedA0_plus_eigenpair :
    printedA0 *ᵥ printedVplus (Real.sqrt 2) (Real.sqrt 3) =
      (3/4 : ℂ) • printedVplus (Real.sqrt 2) (Real.sqrt 3) :=
  printedA0xy_plus_eigenpair _ _ sqrt2_sq sqrt3_sq

theorem printedA0_minus_eigenpair :
    printedA0 *ᵥ printedVminus (Real.sqrt 2) (Real.sqrt 3) =
      (-3/4 : ℂ) • printedVminus (Real.sqrt 2) (Real.sqrt 3) :=
  printedA0xy_minus_eigenpair _ _ sqrt2_sq sqrt3_sq

end FormalResearch.QIA
