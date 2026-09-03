import Mathlib
import FormalResearch.Racah.WeylCellWidth

namespace FormalResearch.Racah

/-- Exact span of `N` consecutive law-of-cosines cells.  This is the global
finite-mesh version of the one-cell Weyl-midpoint width identity. -/
theorem lawCosines_lattice_span {A B : ℚ} (c : ℚ) (N : Nat)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    lawCosinesX A B c - lawCosinesX A B (c + (N : ℚ)) =
      (N : ℚ) * (2 * c + (N : ℚ)) / (2 * A * B) := by
  simp [lawCosinesX]
  field_simp [hA, hB]
  ring

/-- For positive side lengths and a nonnegative starting Weyl coordinate, the
law-of-cosines lattice is strictly decreasing across every nonempty block of
cells. -/
theorem lawCosines_lattice_strict_decrease {A B c : ℚ} {N : Nat}
    (hA : 0 < A) (hB : 0 < B) (hc : 0 ≤ c) (hN : 0 < N) :
    lawCosinesX A B (c + (N : ℚ)) < lawCosinesX A B c := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hB0 : B ≠ 0 := ne_of_gt hB
  have hspan := lawCosines_lattice_span c N hA0 hB0
  have hNq : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hlinear : (0 : ℚ) < 2 * c + (N : ℚ) := by linarith
  have hden : (0 : ℚ) < 2 * A * B := by positivity
  have hpos :
      (0 : ℚ) < (N : ℚ) * (2 * c + (N : ℚ)) / (2 * A * B) :=
    div_pos (mul_pos hNq hlinear) hden
  rw [← hspan] at hpos
  exact sub_pos.mp hpos

/-- The span from the first physical cell `c=0` is exactly quadratic in the
number of cells. -/
theorem lawCosines_lattice_span_from_zero {A B : ℚ} (N : Nat)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    lawCosinesX A B 0 - lawCosinesX A B (N : ℚ) =
      (N : ℚ)^2 / (2 * A * B) := by
  rw [lawCosines_lattice_span 0 N hA hB]
  ring

end FormalResearch.Racah
