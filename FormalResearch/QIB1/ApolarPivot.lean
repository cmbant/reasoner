import Mathlib

namespace FormalResearch.QIB1

/-- Diagonal coefficient of the square submatrix obtained from the
`3 ∂ₓ²∂ᵧ - ∂ᵧ³` apolar operator by taking input monomials with
`y`-degree `j+1`. -/
def apolarPivot (d j : Nat) : Nat :=
  3 * (d - (j + 1)) * (d - (j + 2)) * (j + 1)

/-- Every diagonal pivot occurring in degree `d ≥ 3` is strictly positive.
This is the elementary triangular-rank certificate behind the statement that
`D_F : Sym^d(C²) → Sym^(d-3)(C²)` has full row rank. -/
theorem apolarPivot_pos {d j : Nat} (h : j + 3 ≤ d) :
    0 < apolarPivot d j := by
  have h1 : 0 < d - (j + 1) := by omega
  have h2 : 0 < d - (j + 2) := by omega
  have h3 : 0 < j + 1 := Nat.zero_lt_succ j
  unfold apolarPivot
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) h1) h2) h3

/-- The second nonzero coefficient in the same monomial column comes from
`-∂ᵧ³`. Keeping it explicit records the two-diagonal triangular structure. -/
def apolarUpper (j : Nat) : Nat := (j + 1) * j * (j - 1)

/-- The selected square monomial matrix has no entries below its diagonal:
for input `y`-degree `j+1`, the only possible target degrees are `j` and
`j-2`. This arithmetic lemma is the index-level content of that triangularity. -/
theorem apolar_selected_target_le {j r : Nat}
    (h : r = j ∨ r + 2 = j) : r ≤ j := by
  rcases h with rfl | h
  · exact le_rfl
  · omega

/-- Source-status marker for the checkpoint-8 proof boundary.  A downstream
formal theorem that needs the reconstructed three-excitation L=2 rows should
accept a value of this type explicitly rather than silently treating those
rows as proved. -/
structure ReconstructedL2Rows where
  row02 : Prop
  row11 : Prop

end FormalResearch.QIB1
