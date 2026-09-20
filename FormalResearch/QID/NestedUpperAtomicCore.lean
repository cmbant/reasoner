import FormalResearch.QID.NestedLowerWitness

namespace FormalResearch.QID

/-!
# QI-D nested all-rank upper atomic core

This module formalizes the exact symbolic core of the positive decomposition in
`cmbant/QIprojects:QI-D/notes/HADAMARD_NESTED_DS_ALL_N.md`, re-audited at
QIprojects main `6ed6ec977206b9c1874939289fadd942c651bd3c`.

The canonical verifier `QI-D/code/verify_hadamard_nested_ds_all_n.py` is
byte-unchanged in the later source wave.  For rank `n >= 5`, write
`n = r + 5`, so the stabilized top block has size `r+1` and its last row is the
distinguished row.

The source decomposition is

`6 N_n = 2 R_n + 2 C_n + sum_{a=1}^4 s_a t_a^T`.

Here Lean checks the collected row contribution `R_n`, collected column
contribution `C_n`, the four explicit sign-sign outer products, their
opposite-parity signs, the exact scaled matrix identity, and the resulting
support-budget arithmetic `n + 2/3`.

Scope boundary: this module does not yet prove that the collected `R_n` and
`C_n` are sums of the individual `n+1` row-sign and five sign-column rank-one
atoms, nor does it rederive the sharp type-D support theorem for those atoms.
Those are the next semantic/structural bridge.  Thus the matrix identity and
parity/budget algebra are internal; the rank-one support implication is not
silently asserted.
-/

/-- Rank in the `n>=5` parametrization used by the atomic decomposition. -/
def nestedUpperRank (r : Nat) : Nat := r + 5

/-- A column sign vector: constant `ell` on the stabilized coordinates and
`(sx,sy,sq,sz)` on the D4 core `(x,y,q,z)`. -/
def nestedColSign (r : Nat)
    (ell sx sy sq sz : ℚ) : NestedIdx (r + 1) → ℚ
  | Sum.inl _ => ell
  | Sum.inr j => (![sx, sy, sq, sz] : D4Vec) j

/-- A row sign vector: `sord` on ordinary stabilized rows, `sd` on the last
(distinguished) stabilized row, and `(su,sv,sqr,szr)` on `(u,v,q_r,z_r)`. -/
def nestedRowSign (r : Nat)
    (sord sd su sv sqr szr : ℚ) : NestedIdx (r + 1) → ℚ
  | Sum.inl i => if i.1 + 1 = r + 1 then sd else sord
  | Sum.inr j => (![su, sv, sqr, szr] : D4Vec) j

/-- Rank-one outer product used for the four sign-sign atoms. -/
def nestedOuter {ι : Type} (s t : ι → ℚ) : Matrix ι ι ℚ :=
  fun i j => s i * t j

/-- Collected sum `R_n` of the source row-sign atoms.  This is the matrix
obtained after adding those atoms row by row. -/
def nestedRowContribution (r : Nat) :
    Matrix (NestedIdx (r + 1)) (NestedIdx (r + 1)) ℚ :=
  fun i j =>
    match i with
    | Sum.inl a =>
        nestedColSign r 1
          (if a.1 + 1 = r + 1 then -1 else 1) 1 1 (-1) j
    | Sum.inr a =>
        (![ nestedColSign r 0 (-2) 2 0 (-2) j,
            nestedColSign r 0 2 (-2) 0 (-2) j,
            nestedColSign r (-1) (-1) (-1) (-1) (-1) j,
            0 ] : D4Vec) a

/-- Collected sum `C_n` of the five source sign-column atoms. -/
def nestedColContribution (r : Nat) :
    Matrix (NestedIdx (r + 1)) (NestedIdx (r + 1)) ℚ :=
  fun i j =>
    match j with
    | Sum.inl _ => 0
    | Sum.inr a =>
        (![ nestedRowSign r 2 (-2) (-2) 2 (-2) 0 i,
            nestedRowSign r 2 2 2 (-2) (-2) 0 i,
            0,
            nestedRowSign r 1 1 (-1) (-1) 1 1 i ] : D4Vec) a

/-- First opposite-parity sign-sign atom. -/
def nestedSignS1 (r : Nat) : NestedIdx (r + 1) → ℚ :=
  nestedRowSign r 1 1 (-1) 1 (-1) (-1)
def nestedSignT1 (r : Nat) : NestedIdx (r + 1) → ℚ :=
  nestedColSign r 1 1 (-1) 1 (-1)

/-- Second opposite-parity sign-sign atom. -/
def nestedSignS2 (r : Nat) : NestedIdx (r + 1) → ℚ :=
  nestedRowSign r 1 1 (-1) 1 (-1) 1
def nestedSignT2 (r : Nat) : NestedIdx (r + 1) → ℚ :=
  nestedColSign r 1 1 (-1) 1 1

/-- Third opposite-parity sign-sign atom. -/
def nestedSignS3 (r : Nat) : NestedIdx (r + 1) → ℚ :=
  nestedRowSign r 1 1 1 (-1) (-1) (-1)
def nestedSignT3 (r : Nat) : NestedIdx (r + 1) → ℚ :=
  nestedColSign r 1 (-1) 1 1 (-1)

/-- Fourth opposite-parity sign-sign atom. -/
def nestedSignS4 (r : Nat) : NestedIdx (r + 1) → ℚ :=
  nestedRowSign r 1 1 1 (-1) (-1) 1
def nestedSignT4 (r : Nat) : NestedIdx (r + 1) → ℚ :=
  nestedColSign r 1 (-1) 1 1 1

/-- Sum of the four explicit sign-sign atoms. -/
def nestedSignContribution (r : Nat) :
    Matrix (NestedIdx (r + 1)) (NestedIdx (r + 1)) ℚ :=
  nestedOuter (nestedSignS1 r) (nestedSignT1 r) +
  nestedOuter (nestedSignS2 r) (nestedSignT2 r) +
  nestedOuter (nestedSignS3 r) (nestedSignT3 r) +
  nestedOuter (nestedSignS4 r) (nestedSignT4 r)

/-- Exact symbolic integer identity from the source decomposition, after the
row-sign and sign-column atoms are collected into `R_n` and `C_n`. -/
theorem nestedUpper_scaled_identity (r : Nat) :
    (6 : ℚ) • nestedNormal (r + 1) =
      (2 : ℚ) • nestedRowContribution r +
      (2 : ℚ) • nestedColContribution r +
      nestedSignContribution r := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [nestedNormal, nestedTopLeft, nestedRowContribution,
      nestedColContribution, nestedSignContribution, nestedOuter,
      nestedSignS1, nestedSignT1, nestedSignS2, nestedSignT2,
      nestedSignS3, nestedSignT3, nestedSignS4, nestedSignT4,
      nestedRowSign, nestedColSign]
    norm_num
  · fin_cases j <;>
      simp [nestedNormal, nestedTopRight, nestedRowContribution,
        nestedColContribution, nestedSignContribution, nestedOuter,
        nestedSignS1, nestedSignT1, nestedSignS2, nestedSignT2,
        nestedSignS3, nestedSignT3, nestedSignS4, nestedSignT4,
        nestedRowSign, nestedColSign] <;>
      (try split_ifs) <;> norm_num
  · fin_cases i <;>
      simp [nestedNormal, nestedBottomLeft, nestedRowContribution,
        nestedColContribution, nestedSignContribution, nestedOuter,
        nestedSignS1, nestedSignT1, nestedSignS2, nestedSignT2,
        nestedSignS3, nestedSignT3, nestedSignS4, nestedSignT4,
        nestedRowSign, nestedColSign] <;>
      norm_num
  · fin_cases i <;> fin_cases j <;>
      simp [nestedNormal, d4NestedNormal, d4FacetNormal,
        nestedRowContribution, nestedColContribution,
        nestedSignContribution, nestedOuter,
        nestedSignS1, nestedSignT1, nestedSignS2, nestedSignT2,
        nestedSignS3, nestedSignT3, nestedSignS4, nestedSignT4,
        nestedRowSign, nestedColSign] <;>
      norm_num

/-- Product of all signs in canonical block coordinates.  The D4 core is
written explicitly so the definition is stable and easy to reduce. -/
def nestedSignProduct (r : Nat) (v : NestedIdx (r + 1) → ℚ) : ℚ :=
  (∏ i : Fin (r + 1), v (Sum.inl i)) *
    v (Sum.inr (0 : D4Fin)) * v (Sum.inr (1 : D4Fin)) *
    v (Sum.inr (2 : D4Fin)) * v (Sum.inr (3 : D4Fin))

theorem nestedSign1_oppositeParity (r : Nat) :
    nestedSignProduct r (nestedSignS1 r) *
      nestedSignProduct r (nestedSignT1 r) = -1 := by
  simp [nestedSignProduct, nestedSignS1, nestedSignT1,
    nestedRowSign, nestedColSign]

theorem nestedSign2_oppositeParity (r : Nat) :
    nestedSignProduct r (nestedSignS2 r) *
      nestedSignProduct r (nestedSignT2 r) = -1 := by
  simp [nestedSignProduct, nestedSignS2, nestedSignT2,
    nestedRowSign, nestedColSign]

theorem nestedSign3_oppositeParity (r : Nat) :
    nestedSignProduct r (nestedSignS3 r) *
      nestedSignProduct r (nestedSignT3 r) = -1 := by
  simp [nestedSignProduct, nestedSignS3, nestedSignT3,
    nestedRowSign, nestedColSign]

theorem nestedSign4_oppositeParity (r : Nat) :
    nestedSignProduct r (nestedSignS4 r) *
      nestedSignProduct r (nestedSignT4 r) = -1 := by
  simp [nestedSignProduct, nestedSignS4, nestedSignT4,
    nestedRowSign, nestedColSign]

/-- Source atom counts in the `n=r+5` parametrization. -/
def nestedRowAtomCount (r : Nat) : Nat := r + 6
def nestedColAtomCount : Nat := 5
def nestedSignAtomCount : Nat := 4

theorem nestedRowAtomCount_eq_rank_add_one (r : Nat) :
    nestedRowAtomCount r = nestedUpperRank r + 1 := by
  simp [nestedRowAtomCount, nestedUpperRank]

theorem nestedColAtomCount_eq_five : nestedColAtomCount = 5 := rfl
theorem nestedSignAtomCount_eq_four : nestedSignAtomCount = 4 := rfl

/-- Scalar support budget obtained from `n+1` row atoms of support `1`, five
column atoms of support `1`, and four opposite-parity sign atoms of support
`n-2`, with source weights `1/3,1/3,1/6`. -/
def nestedAtomicSupportBudget (r : Nat) : ℚ :=
  (((nestedRowAtomCount r : Nat) : ℚ) + (nestedColAtomCount : ℚ)) / 3 +
    ((nestedSignAtomCount : ℚ) * ((nestedUpperRank r : ℚ) - 2)) / 6

/-- The exact source budget simplifies uniformly to `n+2/3`. -/
theorem nestedAtomicSupportBudget_eq (r : Nat) :
    nestedAtomicSupportBudget r = (nestedUpperRank r : ℚ) + 2 / 3 := by
  simp [nestedAtomicSupportBudget, nestedRowAtomCount, nestedColAtomCount,
    nestedSignAtomCount, nestedUpperRank]
  ring

end FormalResearch.QID
