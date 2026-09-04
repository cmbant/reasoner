import Mathlib
import FormalResearch.QIB1.ApolarTriangularRank

namespace FormalResearch.QIB1

/-- Full coefficient matrix of `D_F = 3 ∂ₓ²∂ᵧ - ∂ᵧ³` on degree-d binary
forms, with rows indexed by output y-degree and columns by input y-degree.
The coefficient normalization agrees with the selected square minor already
used in `ApolarTriangularRank`. -/
def apolarFull (d : Nat) : Matrix (Fin (d - 2)) (Fin (d + 1)) Int :=
  fun r k =>
    if k.val = r.val + 1 then (apolarPivot d r.val : Int)
    else if k.val = r.val + 3 then
      -((k.val : Int) * (k.val - 1) * (k.val - 2))
    else 0

/-- Columns of y-degree `1,...,d-2` select the canonical square pivot block. -/
def apolarSelectedCol {d : Nat} (c : Fin (d - 2)) : Fin (d + 1) :=
  ⟨c.val + 1, by omega⟩

/-- The selected block of the full differential matrix is exactly the
previously certified triangular square matrix. -/
theorem apolarFull_selected (d : Nat) :
    (apolarFull d).submatrix id (@apolarSelectedCol d) = apolarSquare d := by
  ext r c
  simp only [Matrix.submatrix_apply, id_eq]
  by_cases hrc : r = c
  · subst c
    simp [apolarFull, apolarSquare, apolarSelectedCol]
  · have hcr : c.val ≠ r.val := by
      intro h
      apply hrc
      apply Fin.ext
      exact h.symm
    by_cases h2 : r.val + 2 = c.val
    · have hk1 : (apolarSelectedCol c).val ≠ r.val + 1 := by
        simp [apolarSelectedCol]
        intro h
        apply hrc
        ext
        omega
      have hk3 : (apolarSelectedCol c).val = r.val + 3 := by
        simp [apolarSelectedCol]
        omega
      simp [apolarFull, apolarSquare, apolarSelectedCol, hrc, hcr, h2, hk1, hk3]
      ring_nf
    · have h2' : c.val ≠ r.val + 2 := fun h => h2 h.symm
      have hk1 : (apolarSelectedCol c).val ≠ r.val + 1 := by
        simp [apolarSelectedCol]
        intro h
        apply hrc
        ext
        omega
      have hk3 : (apolarSelectedCol c).val ≠ r.val + 3 := by
        simp [apolarSelectedCol]
        intro h
        apply h2
        omega
      simp [apolarFull, apolarSquare, apolarSelectedCol, hrc, hcr, h2, h2', hk1, hk3]

/-- The *full* apolar differential matrix has maximal possible row rank in
every degree `d≥3`.  Thus the earlier nonzero minor is promoted to a theorem
about the actual map `D_F`, not merely a selected certificate. -/
theorem apolarFull_rank {d : Nat} (hd : 3 ≤ d) :
    (apolarFull d).rank = d - 2 := by
  apply Nat.le_antisymm
  · simpa using Matrix.rank_le_card_height (apolarFull d)
  · have hsq : (apolarSquare d).rank = d - 2 := by
      rw [Matrix.rank_of_det_ne_zero (apolarSquare_det_ne_zero hd), Fintype.card_fin]
    calc
      d - 2 = (apolarSquare d).rank := hsq.symm
      _ = ((apolarFull d).submatrix id (@apolarSelectedCol d)).rank := by
        rw [apolarFull_selected]
      _ ≤ (apolarFull d).rank :=
        Matrix.rank_submatrix_le (apolarFull d) id (@apolarSelectedCol d)

end FormalResearch.QIB1
