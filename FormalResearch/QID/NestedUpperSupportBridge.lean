import FormalResearch.QID.NestedUpperRankOneSums

namespace FormalResearch.QID

/-!
# QI-D nested upper support bridge

This module completes the algebraic implication in the all-rank QI-D upper
bound while keeping the sharp type-D support theorem as an explicit semantic
boundary.

For `n=r+5`, the previous modules internally prove the exact positive
rank-one identity

`6 N_n = 2 R_n + 2 C_n + sum_{a=1}^4 s_a t_a^T`,

where `R_n` is the sum of `n+1` basis-row/sign atoms and `C_n` is the sum of
five sign/basis-column atoms.  The source's type-D rank-one support theorem
bounds every row/column atom by `1` and every opposite-parity sign atom by
`n-2` against every `T in DS(W(D_n))`.

That arbitrary-real Procrustes/rearrangement support theorem is not presently
formalized in the maintained reasoner tree.  Accordingly, the final theorem
below takes those *individual atom bounds* as hypotheses for an arbitrary test
matrix `T` and proves, internally in Lean, the exact consequence

`<N_n,T> <= n + 2/3`.

Thus no DS/Weyl semantic theorem is silently asserted: a future type-D support
module can discharge these hypotheses directly.
-/

/-- Frobenius pairing is additive in its first matrix argument. -/
@[simp] theorem nestedFrob_add_left {k : Nat}
    (X Y T : Matrix (NestedIdx k) (NestedIdx k) ℚ) :
    nestedFrob (X + Y) T = nestedFrob X T + nestedFrob Y T := by
  simp [nestedFrob, add_mul, Finset.sum_add_distrib]

/-- Frobenius pairing is homogeneous in its first matrix argument. -/
@[simp] theorem nestedFrob_smul_left {k : Nat}
    (c : ℚ) (X T : Matrix (NestedIdx k) (NestedIdx k) ℚ) :
    nestedFrob (c • X) T = c * nestedFrob X T := by
  simp [nestedFrob, mul_assoc, Finset.mul_sum]

/-- Frobenius pairing commutes with a finite sum in its first argument. -/
theorem nestedFrob_sum_left {k : Nat} {α : Type} [Fintype α]
    (f : α → Matrix (NestedIdx k) (NestedIdx k) ℚ)
    (T : Matrix (NestedIdx k) (NestedIdx k) ℚ) :
    nestedFrob (∑ a, f a) T = ∑ a, nestedFrob (f a) T := by
  classical
  simp [nestedFrob, Matrix.sum_apply, Finset.sum_mul, Finset.sum_comm]

/-- Named aliases for the five fixed core-row atoms in the source. -/
def nestedSpecialRowU1 (r : Nat) :=
  nestedRowAtom (Sum.inr (0 : D4Fin) : NestedIdx (r + 1))
    (nestedColSign r 1 (-1) 1 1 (-1))
def nestedSpecialRowU2 (r : Nat) :=
  nestedRowAtom (Sum.inr (0 : D4Fin) : NestedIdx (r + 1))
    (nestedColSign r (-1) (-1) 1 (-1) (-1))
def nestedSpecialRowV1 (r : Nat) :=
  nestedRowAtom (Sum.inr (1 : D4Fin) : NestedIdx (r + 1))
    (nestedColSign r 1 1 (-1) 1 (-1))
def nestedSpecialRowV2 (r : Nat) :=
  nestedRowAtom (Sum.inr (1 : D4Fin) : NestedIdx (r + 1))
    (nestedColSign r (-1) 1 (-1) (-1) (-1))
def nestedSpecialRowQ (r : Nat) :=
  nestedRowAtom (Sum.inr (2 : D4Fin) : NestedIdx (r + 1))
    (nestedColSign r (-1) (-1) (-1) (-1) (-1))

/-- Named aliases for the five fixed sign-column atoms in the source. -/
def nestedSpecialColX1 (r : Nat) :=
  nestedColAtom (nestedRowSign r 1 (-1) (-1) 1 (-1) (-1))
    (Sum.inr (0 : D4Fin) : NestedIdx (r + 1))
def nestedSpecialColX2 (r : Nat) :=
  nestedColAtom (nestedRowSign r 1 (-1) (-1) 1 (-1) 1)
    (Sum.inr (0 : D4Fin) : NestedIdx (r + 1))
def nestedSpecialColY1 (r : Nat) :=
  nestedColAtom (nestedRowSign r 1 1 1 (-1) (-1) (-1))
    (Sum.inr (1 : D4Fin) : NestedIdx (r + 1))
def nestedSpecialColY2 (r : Nat) :=
  nestedColAtom (nestedRowSign r 1 1 1 (-1) (-1) 1)
    (Sum.inr (1 : D4Fin) : NestedIdx (r + 1))
def nestedSpecialColZ (r : Nat) :=
  nestedColAtom (nestedRowSign r 1 1 (-1) (-1) 1 1)
    (Sum.inr (3 : D4Fin) : NestedIdx (r + 1))

/-- The named row aliases are exactly the fixed source row sum. -/
theorem nestedSpecialRowAtomSum_named (r : Nat) :
    nestedSpecialRowAtomSum r =
      nestedSpecialRowU1 r + nestedSpecialRowU2 r +
      nestedSpecialRowV1 r + nestedSpecialRowV2 r + nestedSpecialRowQ r := by
  rfl

/-- The named column aliases are exactly the fixed source column sum. -/
theorem nestedExplicitColAtomSum_named (r : Nat) :
    nestedExplicitColAtomSum r =
      nestedSpecialColX1 r + nestedSpecialColX2 r +
      nestedSpecialColY1 r + nestedSpecialColY2 r + nestedSpecialColZ r := by
  rfl

/-- Individual `<=1` top-row atom bounds sum to `r+1`. -/
theorem nestedTopRow_support_sum (r : Nat)
    (T : Matrix (NestedIdx (r + 1)) (NestedIdx (r + 1)) ℚ)
    (hTop : ∀ i : Fin (r + 1),
      nestedFrob
        (nestedRowAtom (Sum.inl i : NestedIdx (r + 1))
          (nestedColSign r 1
            (if i.1 + 1 = r + 1 then -1 else 1) 1 1 (-1))) T ≤ 1) :
    nestedFrob (nestedTopRowAtomSum r) T ≤ (r + 1 : Nat) := by
  rw [nestedTopRowAtomSum, nestedFrob_sum_left]
  calc
    (∑ i : Fin (r + 1),
        nestedFrob
          (nestedRowAtom (Sum.inl i : NestedIdx (r + 1))
            (nestedColSign r 1
              (if i.1 + 1 = r + 1 then -1 else 1) 1 1 (-1))) T)
        ≤ ∑ _i : Fin (r + 1), (1 : ℚ) := by
          exact Finset.sum_le_sum fun i _hi => hTop i
    _ = (r + 1 : Nat) := by simp

/-- The exact source upper bound follows from the sharp support inequalities
for every individual rank-one atom.  These hypotheses are precisely the
external type-D support/Procrustes layer still missing from Lean. -/
theorem nestedUpper_support_from_individual_atoms (r : Nat)
    (T : Matrix (NestedIdx (r + 1)) (NestedIdx (r + 1)) ℚ)
    (hTop : ∀ i : Fin (r + 1),
      nestedFrob
        (nestedRowAtom (Sum.inl i : NestedIdx (r + 1))
          (nestedColSign r 1
            (if i.1 + 1 = r + 1 then -1 else 1) 1 1 (-1))) T ≤ 1)
    (hRU1 : nestedFrob (nestedSpecialRowU1 r) T ≤ 1)
    (hRU2 : nestedFrob (nestedSpecialRowU2 r) T ≤ 1)
    (hRV1 : nestedFrob (nestedSpecialRowV1 r) T ≤ 1)
    (hRV2 : nestedFrob (nestedSpecialRowV2 r) T ≤ 1)
    (hRQ  : nestedFrob (nestedSpecialRowQ r) T ≤ 1)
    (hCX1 : nestedFrob (nestedSpecialColX1 r) T ≤ 1)
    (hCX2 : nestedFrob (nestedSpecialColX2 r) T ≤ 1)
    (hCY1 : nestedFrob (nestedSpecialColY1 r) T ≤ 1)
    (hCY2 : nestedFrob (nestedSpecialColY2 r) T ≤ 1)
    (hCZ  : nestedFrob (nestedSpecialColZ r) T ≤ 1)
    (hS1 : nestedFrob (nestedOuter (nestedSignS1 r) (nestedSignT1 r)) T ≤
      (nestedUpperRank r : ℚ) - 2)
    (hS2 : nestedFrob (nestedOuter (nestedSignS2 r) (nestedSignT2 r)) T ≤
      (nestedUpperRank r : ℚ) - 2)
    (hS3 : nestedFrob (nestedOuter (nestedSignS3 r) (nestedSignT3 r)) T ≤
      (nestedUpperRank r : ℚ) - 2)
    (hS4 : nestedFrob (nestedOuter (nestedSignS4 r) (nestedSignT4 r)) T ≤
      (nestedUpperRank r : ℚ) - 2) :
    nestedFrob (nestedNormal (r + 1)) T ≤
      (nestedUpperRank r : ℚ) + 2 / 3 := by
  have hTopSum := nestedTopRow_support_sum r T hTop
  have hRow : nestedFrob (nestedExplicitRowAtomSum r) T ≤
      (nestedUpperRank r : ℚ) + 1 := by
    rw [nestedExplicitRowAtomSum, nestedSpecialRowAtomSum_named,
      nestedFrob_add_left, nestedFrob_add_left, nestedFrob_add_left,
      nestedFrob_add_left, nestedFrob_add_left]
    simp [nestedUpperRank] at hTopSum ⊢
    linarith
  have hCol : nestedFrob (nestedExplicitColAtomSum r) T ≤ 5 := by
    rw [nestedExplicitColAtomSum_named, nestedFrob_add_left,
      nestedFrob_add_left, nestedFrob_add_left, nestedFrob_add_left]
    linarith
  have hSign : nestedFrob (nestedSignContribution r) T ≤
      4 * ((nestedUpperRank r : ℚ) - 2) := by
    rw [nestedSignContribution, nestedFrob_add_left,
      nestedFrob_add_left, nestedFrob_add_left]
    linarith
  have hPair := congrArg (fun X => nestedFrob X T)
    (nestedUpper_explicit_rankOne_identity r)
  simp only [nestedFrob_smul_left, nestedFrob_add_left] at hPair
  linarith

end FormalResearch.QID
