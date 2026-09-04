import Mathlib

namespace FormalResearch.QIA

open Complex

/-- Radical-free parametrization of the printed Hermitian qutrit matrix.  The
paper is recovered by `x = sqrt 2`, `y = sqrt 3`; then `x*y = sqrt 6`. -/
noncomputable def printedA0xy (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -(I * y / 4), -(I * (x*y) / 8);
      I * y / 4, 0, 3 * I * x / 8;
      I * (x*y) / 8, -(3 * I * x / 8), 0]

/-- The exact cubic spectral identity of the printed matrix.  No numerical
linear algebra is involved: only `x²=2`, `y²=3`. -/
theorem printedA0xy_cubic (x y : ℝ) (hx : x^2 = 2) (hy : y^2 = 3) :
    printedA0xy x y ^ 3 = (9 / 16 : ℂ) • printedA0xy x y := by
  have hxc : (x : ℂ)^2 = 2 := by exact_mod_cast hx
  have hyc : (y : ℂ)^2 = 3 := by exact_mod_cast hy
  have hxc3 : (x : ℂ)^3 = 2 * (x : ℂ) := by
    calc
      (x : ℂ)^3 = (x : ℂ)^2 * (x : ℂ) := by ring
      _ = 2 * (x : ℂ) := by rw [hxc]
  have hyc3 : (y : ℂ)^3 = 3 * (y : ℂ) := by
    calc
      (y : ℂ)^3 = (y : ℂ)^2 * (y : ℂ) := by ring
      _ = 3 * (y : ℂ) := by rw [hyc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, printedA0xy, Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_sq] <;>
    ring_nf <;>
    simp [hxc, hyc, hxc3, hyc3] <;>
    ring_nf

/-- The paper's concrete matrix, written with `sqrt 2 * sqrt 3` in the
`√6` slots to keep the formal algebra transparent. -/
noncomputable def printedA0 : Matrix (Fin 3) (Fin 3) ℂ :=
  printedA0xy (Real.sqrt 2) (Real.sqrt 3)

theorem sqrt2_sq : (Real.sqrt 2)^2 = 2 := by norm_num
theorem sqrt3_sq : (Real.sqrt 3)^2 = 3 := by norm_num

theorem printedA0_cubic :
    printedA0 ^ 3 = (9 / 16 : ℂ) • printedA0 := by
  exact printedA0xy_cubic _ _ sqrt2_sq sqrt3_sq

/-- The matrix is genuinely nonzero. -/
theorem printedA0_ne_zero : printedA0 ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 3)) (1 : Fin 3)
  simp [printedA0, printedA0xy] at h01

/-- The displayed matrix is Hermitian. -/
theorem printedA0_hermitian : printedA0.conjTranspose = printedA0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [printedA0, printedA0xy, Matrix.conjTranspose_apply] <;>
    ring

end FormalResearch.QIA
