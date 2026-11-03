module

public import FormalResearch.FourQubitEntropy.PurityLPRank
public import FormalResearch.FourQubitEntropy.PurityLPGraph

/-!
# Kernel-computable cut ranks

Bridges `cutRank Γ S = rank_{𝔽₂} Γ[S,S^c]` (`PurityLPGraph.lean`, a `Matrix.rank`) to the bitmask elimination
`f2rank` of `PurityLPRank.lean`.  A graph is given by `adj : Fin n → ℕ` (the neighbourhood bitmasks, bit `j` of
`adj i` set iff `i ~ j`; this is the hexadecimal row format of the paper's scripts).

* `cutRankN adj S = f2rank [adj i &&& notMask S | i ∈ S]` -- computable (`decide +kernel`);
* `cutRank_eq`: `cutRank (adjGraph adj) S = cutRankN adj S`.
-/

@[expose] public section


open scoped BigOperators

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FourQubitEntropy.SpinFlip

variable {n : ℕ}

/-- The number whose binary digits (least significant first) are the given bits. -/
def ofBitsL : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * ofBitsL bs

theorem testBit_ofBitsL (l : List Bool) (j : ℕ) : (ofBitsL l).testBit j = l.getD j false := by
  induction l generalizing j with
  | nil => simp [ofBitsL]
  | cons b bs ih =>
    cases j with
    | zero =>
      cases b <;> simp [ofBitsL, Nat.testBit_zero]
    | succ j =>
      rw [Nat.testBit_succ]
      have : (ofBitsL (b :: bs)) / 2 = ofBitsL bs := by
        cases b <;> simp [ofBitsL] <;> omega
      rw [this, ih]
      simp

theorem ofBitsL_lt (l : List Bool) : ofBitsL l < 2 ^ l.length := by
  induction l with
  | nil => simp [ofBitsL]
  | cons b bs ih =>
    simp only [ofBitsL, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- The mask of the columns outside `S`. -/
def notMask (S : Finset (Fin n)) : ℕ := ofBitsL ((List.finRange n).map fun j => decide (j ∉ S))

theorem notMask_lt (S : Finset (Fin n)) : notMask S < 2 ^ n := by
  unfold notMask
  have h := ofBitsL_lt ((List.finRange n).map fun j => decide (j ∉ S))
  rw [List.length_map, List.length_finRange] at h
  exact h

theorem testBit_notMask (S : Finset (Fin n)) (j : Fin n) : (notMask S).testBit j = decide (j ∉ S) := by
  unfold notMask
  rw [testBit_ofBitsL]
  simp [List.getD_eq_getElem?_getD]

theorem testBit_notMask_ge (S : Finset (Fin n)) {j : ℕ} (hj : n ≤ j) : (notMask S).testBit j = false := by
  unfold notMask
  rw [testBit_ofBitsL]
  simp [List.getD_eq_getElem?_getD, hj]

/-- The adjacency function of the graph with neighbourhood bitmasks `adj`. -/
def adjGraph (adj : Fin n → ℕ) : Fin n → Fin n → Bool := fun i j => (adj i).testBit j

/-- The cut rows `adj i` restricted to the columns outside `S`, for `i ∈ S`. -/
def cutRows (adj : Fin n → ℕ) (S : Finset (Fin n)) : List ℕ :=
  ((List.finRange n).filter fun i => decide (i ∈ S)).map fun i => adj i &&& notMask S

/-- The cut rank computed by bitmask elimination. -/
def cutRankN (adj : Fin n → ℕ) (S : Finset (Fin n)) : ℕ := f2rank (cutRows adj S)

/-- Extension by zero from the columns outside `S`. -/
def pad (S : Finset (Fin n)) : ({j // j ∉ S} → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun v j := if h : j ∉ S then v ⟨j, h⟩ else 0
  map_add' v w := by ext j; by_cases h : j ∈ S <;> simp [h]
  map_smul' c v := by ext j; by_cases h : j ∈ S <;> simp [h]

theorem pad_injective (S : Finset (Fin n)) : Function.Injective (pad S) := by
  intro v w h
  funext j
  have := congrFun h j.1
  simpa [pad, j.2] using this

theorem pad_row (adj : Fin n → ℕ) (S : Finset (Fin n)) (i : {i // i ∈ S}) :
    pad S ((cutMat (adjGraph adj) S).row i) = toVec n (adj i.1 &&& notMask S) := by
  ext j
  simp only [pad, LinearMap.coe_mk, AddHom.coe_mk, Matrix.row_apply, toVec, Nat.testBit_and,
    testBit_notMask]
  by_cases hj : j ∈ S
  · simp [hj]
  · simp [hj, cutMat, adjGraph]
    rfl

theorem cutRank_eq (adj : Fin n → ℕ) (S : Finset (Fin n)) :
    cutRank (adjGraph adj) S = cutRankN adj S := by
  have hb : ∀ r ∈ cutRows adj S, r < 2 ^ n := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    exact Nat.and_lt_two_pow _ (notMask_lt S)
  unfold cutRankN
  rw [f2rank_eq n _ hb, cutRank, Matrix.rank_eq_finrank_span_row]
  have hset : {v | v ∈ (cutRows adj S).map (toVec n)}
      = pad S '' Set.range (cutMat (adjGraph adj) S).row := by
    ext v
    simp only [Set.mem_ofPred_eq, cutRows, List.map_map, List.mem_map, Function.comp,
      List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨⟨i, hi⟩, rfl⟩, pad_row adj S ⟨i, hi⟩⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i.1, i.2, (pad_row adj S i).symm⟩
  unfold rowSpan
  rw [hset, ← Submodule.map_span]
  exact (Submodule.equivMapOfInjective (pad S) (pad_injective S) _).finrank_eq

end FormalResearch.FourQubitEntropy.PurityLP
