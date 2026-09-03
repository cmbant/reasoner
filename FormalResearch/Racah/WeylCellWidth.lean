import Mathlib

namespace FormalResearch.Racah

/-- Exact Weyl-midpoint form of the SU(2) Casimir. -/
theorem casimir_weyl_midpoint (c : ℚ) :
    c * (c + 1) = (c + 1/2)^2 - 1/4 := by
  ring

/-- Law-of-cosines coordinate used in the centered Racah lattice. -/
def lawCosinesX (A B s : ℚ) : ℚ :=
  (A^2 + B^2 - s^2) / (2*A*B)

/-- Exact cell-width identity: the Racah lattice weight `(2c+1)/(2AB)` is
literally the width of the law-of-cosines cell centered at the Weyl point
`C=c+1/2`. -/
theorem lawCosines_cell_width {A B : ℚ} (c : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) :
    lawCosinesX A B c - lawCosinesX A B (c + 1) =
      (2*c + 1) / (2*A*B) := by
  simp [lawCosinesX]
  field_simp [hA, hB]
  ring

/-- The same width written in the centered variable `C=c+1/2`. -/
theorem lawCosines_cell_width_centered {A B : ℚ} (c : ℚ)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    lawCosinesX A B c - lawCosinesX A B (c + 1) =
      (c + 1/2) / (A*B) := by
  rw [lawCosines_cell_width c hA hB]
  field_simp [hA, hB]
  ring

end FormalResearch.Racah
