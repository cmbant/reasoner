import Mathlib
import FormalResearch.Racah.WeylLatticeSpan

namespace FormalResearch.Racah

open scoped BigOperators

/-- The individual Weyl-midpoint cell widths telescope exactly to the global
law-of-cosines endpoint span. -/
theorem lawCosines_cell_width_sum {A B : ℚ} (c : ℚ) (N : Nat)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    (∑ k ∈ Finset.range N,
      (2 * (c + (k : ℚ)) + 1) / (2 * A * B)) =
      lawCosinesX A B c - lawCosinesX A B (c + (N : ℚ)) := by
  calc
    (∑ k ∈ Finset.range N,
      (2 * (c + (k : ℚ)) + 1) / (2 * A * B)) =
      ∑ k ∈ Finset.range N,
        (lawCosinesX A B (c + (k : ℚ)) -
          lawCosinesX A B (c + ((k + 1 : Nat) : ℚ))) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hcell := lawCosines_cell_width (A := A) (B := B)
              (c + (k : ℚ)) hA hB
            simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hcell.symm
    _ = lawCosinesX A B c - lawCosinesX A B (c + (N : ℚ)) := by
      rw [Finset.sum_range_sub']
      simp

/-- Closed midpoint-mesh sum.  The discrete Weyl weights integrate the
quadratic law-of-cosines coordinate exactly over every finite block of cells. -/
theorem lawCosines_cell_width_sum_closed {A B : ℚ} (c : ℚ) (N : Nat)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    (∑ k ∈ Finset.range N,
      (2 * (c + (k : ℚ)) + 1) / (2 * A * B)) =
      (N : ℚ) * (2 * c + (N : ℚ)) / (2 * A * B) := by
  rw [lawCosines_cell_width_sum c N hA hB,
    lawCosines_lattice_span c N hA hB]

end FormalResearch.Racah
