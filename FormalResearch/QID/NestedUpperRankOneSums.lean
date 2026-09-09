import FormalResearch.QID.NestedUpperAtomicCore

namespace FormalResearch.QID

/-!
# QI-D nested upper rank-one sums

This module expands the collected `R_n` and `C_n` from
`NestedUpperAtomicCore` into the individual source atoms from
`QI-D/notes/HADAMARD_NESTED_DS_ALL_N.md`.

For `n=r+5`, the row contribution consists of one basis-row/sign atom for each
of the `r+1` stabilized rows plus five fixed D4-core row atoms, for `n+1`
row-sign atoms in total.  The column contribution is the five fixed
sign/basis-column atoms from the source.

Lean proves that these explicit rank-one sums are exactly the collected
matrices already used in the scaled identity.  This closes the structural
matrix-decomposition layer.  The sharp type-D support inequalities for the
individual atoms remain a separate bridge; this module does not assume them.
-/

/-- Standard basis vector over a finite index type. -/
def nestedBasisVec {ι : Type} [DecidableEq ι] (i : ι) : ι → ℚ :=
  fun j => if j = i then 1 else 0

/-- Basis-row/sign atom `e_i t^T`, visibly rank one. -/
def nestedRowAtom {ι : Type} [DecidableEq ι] (i : ι) (t : ι → ℚ) :
    Matrix ι ι ℚ :=
  nestedOuter (nestedBasisVec i) t

/-- Sign/basis-column atom `s e_j^T`, visibly rank one. -/
def nestedColAtom {ι : Type} [DecidableEq ι] (s : ι → ℚ) (j : ι) :
    Matrix ι ι ℚ :=
  nestedOuter s (nestedBasisVec j)

/-- One row atom for every stabilized row; the last row uses the distinguished
`x` sign exactly as in the source. -/
def nestedTopRowAtomSum (r : Nat) :
    Matrix (NestedIdx (r + 1)) (NestedIdx (r + 1)) ℚ :=
  ∑ i : Fin (r + 1),
    nestedRowAtom (Sum.inl i : NestedIdx (r + 1))
      (nestedColSign r 1
        (if i.1 + 1 = r + 1 then -1 else 1) 1 1 (-1))

/-- The five fixed core-row atoms: two on `u`, two on `v`, one on `q_r`. -/
def nestedSpecialRowAtomSum (r : Nat) :
    Matrix (NestedIdx (r + 1)) (NestedIdx (r + 1)) ℚ :=
  nestedRowAtom (Sum.inr (0 : D4Fin) : NestedIdx (r + 1))
      (nestedColSign r 1 (-1) 1 1 (-1)) +
  nestedRowAtom (Sum.inr (0 : D4Fin) : NestedIdx (r + 1))
      (nestedColSign r (-1) (-1) 1 (-1) (-1)) +
  nestedRowAtom (Sum.inr (1 : D4Fin) : NestedIdx (r + 1))
      (nestedColSign r 1 1 (-1) 1 (-1)) +
  nestedRowAtom (Sum.inr (1 : D4Fin) : NestedIdx (r + 1))
      (nestedColSign r (-1) 1 (-1) (-1) (-1)) +
  nestedRowAtom (Sum.inr (2 : D4Fin) : NestedIdx (r + 1))
      (nestedColSign r (-1) (-1) (-1) (-1) (-1))

/-- Full explicit source row-atom sum `R_n`. -/
def nestedExplicitRowAtomSum (r : Nat) :
    Matrix (NestedIdx (r + 1)) (NestedIdx (r + 1)) ℚ :=
  nestedTopRowAtomSum r + nestedSpecialRowAtomSum r

/-- The five fixed source sign-column atoms: two on `x`, two on `y`, one on
`z`. -/
def nestedExplicitColAtomSum (r : Nat) :
    Matrix (NestedIdx (r + 1)) (NestedIdx (r + 1)) ℚ :=
  nestedColAtom (nestedRowSign r 1 (-1) (-1) 1 (-1) (-1))
      (Sum.inr (0 : D4Fin) : NestedIdx (r + 1)) +
  nestedColAtom (nestedRowSign r 1 (-1) (-1) 1 (-1) 1)
      (Sum.inr (0 : D4Fin) : NestedIdx (r + 1)) +
  nestedColAtom (nestedRowSign r 1 1 1 (-1) (-1) (-1))
      (Sum.inr (1 : D4Fin) : NestedIdx (r + 1)) +
  nestedColAtom (nestedRowSign r 1 1 1 (-1) (-1) 1)
      (Sum.inr (1 : D4Fin) : NestedIdx (r + 1)) +
  nestedColAtom (nestedRowSign r 1 1 (-1) (-1) 1 1)
      (Sum.inr (3 : D4Fin) : NestedIdx (r + 1))

/-- The explicit `n+1` row-sign rank-one atoms collect exactly to `R_n`. -/
theorem nestedExplicitRowAtomSum_eq (r : Nat) :
    nestedExplicitRowAtomSum r = nestedRowContribution r := by
  classical
  ext a b
  rcases a with a | a
  · simp [nestedExplicitRowAtomSum, nestedTopRowAtomSum,
      nestedSpecialRowAtomSum, nestedRowAtom, nestedBasisVec, nestedOuter,
      nestedRowContribution]
  · fin_cases a <;> rcases b with b | b
    · simp [nestedExplicitRowAtomSum, nestedTopRowAtomSum,
        nestedSpecialRowAtomSum, nestedRowAtom, nestedBasisVec, nestedOuter,
        nestedRowContribution, nestedColSign]
      norm_num
    · fin_cases b <;>
        simp [nestedExplicitRowAtomSum, nestedTopRowAtomSum,
          nestedSpecialRowAtomSum, nestedRowAtom, nestedBasisVec, nestedOuter,
          nestedRowContribution, nestedColSign] <;>
        norm_num

/-- The five explicit sign-column rank-one atoms collect exactly to `C_n`. -/
theorem nestedExplicitColAtomSum_eq (r : Nat) :
    nestedExplicitColAtomSum r = nestedColContribution r := by
  classical
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · simp [nestedExplicitColAtomSum, nestedColAtom, nestedBasisVec, nestedOuter,
      nestedColContribution]
  · fin_cases b <;>
      simp [nestedExplicitColAtomSum, nestedColAtom, nestedBasisVec, nestedOuter,
        nestedColContribution, nestedRowSign] <;>
      (try split_ifs) <;> norm_num
  · simp [nestedExplicitColAtomSum, nestedColAtom, nestedBasisVec, nestedOuter,
      nestedColContribution]
  · fin_cases a <;> fin_cases b <;>
      simp [nestedExplicitColAtomSum, nestedColAtom, nestedBasisVec, nestedOuter,
        nestedColContribution, nestedRowSign] <;>
      norm_num

/-- The explicit row-atom count is `(r+1)+5 = n+1`. -/
theorem nestedExplicitRowAtomCount (r : Nat) :
    Fintype.card (Fin (r + 1)) + 5 = nestedRowAtomCount r := by
  simp [nestedRowAtomCount]

/-- Rewriting the collected core identity gives the actual source rank-one
matrix decomposition. -/
theorem nestedUpper_explicit_rankOne_identity (r : Nat) :
    (6 : ℚ) • nestedNormal (r + 1) =
      (2 : ℚ) • nestedExplicitRowAtomSum r +
      (2 : ℚ) • nestedExplicitColAtomSum r +
      nestedSignContribution r := by
  rw [nestedExplicitRowAtomSum_eq, nestedExplicitColAtomSum_eq]
  exact nestedUpper_scaled_identity r

end FormalResearch.QID
