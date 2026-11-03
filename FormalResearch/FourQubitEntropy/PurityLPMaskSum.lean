module

public import FormalResearch.FourQubitEntropy.PurityLPGraphMean

/-!
# Fast rank sums over bitmask cuts

The sums `Σ_{|S| = k} g(rk_2 Γ[S,S^c])` of the graph-state data modules are evaluated in the kernel by a binary
recursion on bitmasks (`maskSum`), not by unfolding `Finset.powersetCard (Fin n)`:
cuts are natural numbers `m` (bit `i` set iff `i ∈ S`), `rowsM` are the rows of the cut and `f2rank` their rank.

* `sum_cuts_eq_maskSum`: for every `n`, `adj`, `Σ_{S ∈ powersetCard k univ} g (cutRankN adj S) = maskSum g L full n k 0`
  (`adj i = L.getD i 0`, `full = 2^n - 1`);
* `cutRankN_compl`: `rk_2 Γ[S^c,S] = rk_2 Γ[S,S^c]` for a symmetric graph (transpose);
* `sum_cuts_half`: for `n = 2k` the sum over all `k`-cuts is twice the sum over those containing the last vertex;
* `maskSum_split`: one step of the recursion, used to split a sum into separate `decide +kernel` declarations.
-/

@[expose] public section


open scoped BigOperators

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FourQubitEntropy.SpinFlip

/-- `∑_{t ∈ T} 2^t`: the bitmask of a finite set of naturals. -/
def twoPow (T : Finset ℕ) : ℕ := ∑ t ∈ T, 2 ^ t

theorem testBit_twoPow (T : Finset ℕ) (j : ℕ) : (twoPow T).testBit j = decide (j ∈ T) := by
  have h1 : twoPow T = ((T.sort).map (fun i => 2 ^ i)).sum := by
    unfold twoPow
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
    rfl
  have h3 : (twoPow T).bitIndices = T.sort := by
    rw [h1]; exact Nat.bitIndices_sum_map_two_pow (Finset.sortedLT_sort T)
  have h2 := Nat.mem_bitIndices (i := j) (n := twoPow T)
  rw [h3, Finset.mem_sort] at h2
  cases hb : (twoPow T).testBit j
  · simpa [hb] using h2
  · simpa [hb] using h2

/-- The rows of the cut `m` (the vertices `i < n` with bit `i` set), restricted to the columns outside `m`. -/
def rowsM (n : ℕ) (L : List ℕ) (full m : ℕ) : List ℕ :=
  ((List.range n).filter (fun i => m.testBit i)).map (fun i => L.getD i 0 &&& (full ^^^ m))

/-- `g` of the rank of the cut `m`. -/
def maskVal (g : ℕ → ℕ) (n : ℕ) (L : List ℕ) (full m : ℕ) : ℕ := g (f2rank (rowsM n L full m))

/-- `Σ g(rk m')` over the masks `m'` obtained from `m` by adding `k` of the bits `0, …, i-1`
(binary recursion on `i`; depth `i`). -/
def maskSum (g : ℕ → ℕ) (n : ℕ) (L : List ℕ) (full : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, k, m => if k = 0 then maskVal g n L full m else 0
  | i + 1, k, m =>
      let rest := maskSum g n L full i k m
      match k with
      | 0 => rest
      | k + 1 => rest + maskSum g n L full i k (m + 2 ^ i)

/-- One step of the recursion (`i1 = i + 1`, `k = k' + 1`; stated with `i1` and `k` free so that numerals stay literal:
the kernel then never has to compare `maskSum` terms that differ only by `13` versus `12 + 1`, which makes it evaluate them). -/
theorem maskSum_split (g : ℕ → ℕ) (n : ℕ) (L : List ℕ) (full i i1 k k' m : ℕ) (hi : i1 = i + 1) (hk : k = k' + 1) :
    maskSum g n L full i1 k m = maskSum g n L full i k m + maskSum g n L full i k' (m + 2 ^ i) := by
  subst hi hk; rfl

theorem maskSum_succ_zero (g : ℕ → ℕ) (n : ℕ) (L : List ℕ) (full i m : ℕ) :
    maskSum g n L full (i + 1) 0 m = maskSum g n L full i 0 m := rfl

theorem maskSum_eq (g : ℕ → ℕ) (n : ℕ) (L : List ℕ) (full : ℕ) :
    ∀ (i k : ℕ) (P : Finset ℕ), (∀ p ∈ P, i ≤ p) →
      maskSum g n L full i k (twoPow P)
        = ∑ T ∈ (Finset.range i).powersetCard k, maskVal g n L full (twoPow (P ∪ T)) := by
  intro i
  induction i with
  | zero =>
    intro k P _
    cases k with
    | zero => simp [maskSum]
    | succ k =>
      simp only [maskSum, Finset.range_zero]
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]; simp
  | succ i ih =>
    intro k P hP
    have hP' : ∀ p ∈ P, i ≤ p := fun p hp => Nat.le_of_succ_le (hP p hp)
    cases k with
    | zero =>
      rw [maskSum_succ_zero, ih 0 P hP']
      simp
    | succ k =>
      have hiP : i ∉ P := fun h => by have := hP i h; omega
      have hins : twoPow (insert i P) = twoPow P + 2 ^ i := by
        unfold twoPow; rw [Finset.sum_insert hiP]; ring
      rw [maskSum_split g n L full i (i + 1) (k + 1) k _ rfl rfl, ← hins, ih (k + 1) P hP',
        ih k (insert i P) (by
          intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact le_rfl
          · exact hP' p hp),
        Finset.range_add_one, Finset.powersetCard_succ_insert Finset.notMem_range_self,
        Finset.sum_union, Finset.sum_image]
      · congr 1
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.insert_union, Finset.union_insert]
      · intro T1 h1 T2 h2 h
        have hT1 : i ∉ T1 := fun hi => by
          have := (Finset.mem_powersetCard.mp h1).1 hi; simp at this
        have hT2 : i ∉ T2 := fun hi => by
          have := (Finset.mem_powersetCard.mp h2).1 hi; simp at this
        have := congrArg (fun U => Finset.erase U i) h
        simpa [Finset.erase_insert hT1, Finset.erase_insert hT2] using this
      · rw [Finset.disjoint_left]
        intro T hT hT'
        obtain ⟨T', _, rfl⟩ := Finset.mem_image.mp hT'
        have := (Finset.mem_powersetCard.mp hT).1 (Finset.mem_insert_self i T')
        simp at this

/-! ### Bridge to `cutRankN` -/

theorem rowsM_eq (n : ℕ) (L : List ℕ) (adj : Fin n → ℕ) (hadj : ∀ i, adj i = L.getD i.1 0)
    (full : ℕ) (hf : full = 2 ^ n - 1) (T : Finset ℕ) (hT : T ⊆ Finset.range n) :
    rowsM n L full (twoPow T) = cutRows adj (Finset.univ.filter fun i : Fin n => i.val ∈ T) := by
  have hnm : notMask (Finset.univ.filter fun i : Fin n => i.val ∈ T) = full ^^^ twoPow T := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_xor, hf, Nat.testBit_two_pow_sub_one, testBit_twoPow]
    by_cases hj : j < n
    · have := testBit_notMask (Finset.univ.filter fun i : Fin n => i.val ∈ T) ⟨j, hj⟩
      simp only at this
      rw [this]
      simp [hj]
    · rw [testBit_notMask_ge _ (not_lt.mp hj)]
      have : j ∉ T := fun h => hj (Finset.mem_range.mp (hT h))
      simp [hj, this]
  unfold rowsM cutRows
  rw [hnm, ← List.map_coe_finRange_eq_range (n := n), List.filter_map, List.map_map]
  have hfilt : List.filter ((fun i => (twoPow T).testBit i) ∘ Fin.val) (List.finRange n)
      = List.filter (fun i => decide (i ∈ Finset.univ.filter fun i : Fin n => i.val ∈ T)) (List.finRange n) :=
    List.filter_congr (fun i _ => by simp [testBit_twoPow])
  rw [hfilt]
  apply List.map_congr_left
  intro i _
  simp [hadj]

theorem maskVal_twoPow (g : ℕ → ℕ) (n : ℕ) (L : List ℕ) (adj : Fin n → ℕ) (hadj : ∀ i, adj i = L.getD i.1 0)
    (full : ℕ) (hf : full = 2 ^ n - 1) (T : Finset ℕ) (hT : T ⊆ Finset.range n) :
    maskVal g n L full (twoPow T) = g (cutRankN adj (Finset.univ.filter fun i : Fin n => i.val ∈ T)) := by
  unfold maskVal cutRankN
  rw [rowsM_eq n L adj hadj full hf T hT]

/-- **Bridge**: the kernel recursion `maskSum` computes the sum over all `k`-subsets of `Fin n`. -/
theorem sum_cuts_eq_maskSum (g : ℕ → ℕ) (n : ℕ) (L : List ℕ) (adj : Fin n → ℕ)
    (hadj : ∀ i, adj i = L.getD i.1 0) (full : ℕ) (hf : full = 2 ^ n - 1) (k : ℕ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, g (cutRankN adj S)
      = maskSum g n L full n k 0 := by
  have h0 : (0 : ℕ) = twoPow ∅ := by simp [twoPow]
  rw [h0, maskSum_eq g n L full n k ∅ (by simp)]
  refine Finset.sum_bij (fun S _ => S.map Fin.valEmbedding) ?_ ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_powersetCard] at hS ⊢
    refine ⟨?_, by simpa using hS.2⟩
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
    simp
  · intro S _ S' _ h
    exact Finset.map_injective _ h
  · intro T hT
    rw [Finset.mem_powersetCard] at hT
    refine ⟨Finset.univ.filter fun i : Fin n => i.val ∈ T, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [← hT.2, ← Finset.card_map Fin.valEmbedding]
      congr 1
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx
        have := Finset.mem_range.mp (hT.1 hx)
        exact ⟨⟨x, this⟩, hx, rfl⟩
    · ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx
        have := Finset.mem_range.mp (hT.1 hx)
        exact ⟨⟨x, this⟩, hx, rfl⟩
  · intro S hS
    rw [Finset.empty_union, maskVal_twoPow g n L adj hadj full hf _ (by
      intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
      simp)]
    congr 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.valEmbedding_apply, Fin.val_inj]
    exact ⟨fun h => ⟨i, h, rfl⟩, fun ⟨a, ha, h⟩ => h ▸ ha⟩

/-! ### Complement symmetry and halving -/

/-- `rk_2 Γ[S^c, S] = rk_2 Γ[S, S^c]` for a symmetric graph. -/
theorem cutRankN_compl {n : ℕ} (adj : Fin n → ℕ) (hsym : ∀ i j : Fin n, (adj i).testBit j = (adj j).testBit i)
    (S : Finset (Fin n)) : cutRankN adj Sᶜ = cutRankN adj S := by
  rw [← cutRank_eq, ← cutRank_eq]
  unfold cutRank
  let e1 : {i // i ∈ Sᶜ} ≃ {j // j ∉ S} := Equiv.subtypeEquivRight (fun x => by simp)
  let e2 : {j // j ∉ Sᶜ} ≃ {i // i ∈ S} := Equiv.subtypeEquivRight (fun x => by simp)
  have h : cutMat (adjGraph adj) Sᶜ = ((cutMat (adjGraph adj) S).transpose).submatrix e1 e2 := by
    ext i j
    simp [cutMat, Matrix.submatrix, Matrix.transpose, adjGraph, e1, e2, hsym]
    rfl
  rw [h, Matrix.rank_submatrix, Matrix.rank_transpose]

theorem sum_cuts_half_aux (g : ℕ → ℕ) (p j : ℕ) (hp : p = 2 * j + 1) (L : List ℕ) (adj : Fin (p + 1) → ℕ)
    (hadj : ∀ i, adj i = L.getD i.1 0) (hsym : ∀ i j : Fin (p + 1), (adj i).testBit j = (adj j).testBit i)
    (full : ℕ) (hf : full = 2 ^ (p + 1) - 1) :
    ∑ S ∈ (Finset.univ : Finset (Fin (p + 1))).powersetCard (j + 1), g (cutRankN adj S)
      = 2 * maskSum g (p + 1) L full p j (2 ^ p) := by
  rw [sum_cuts_eq_maskSum g (p + 1) L adj hadj full hf, maskSum_split g (p + 1) L full p (p + 1) (j + 1) j 0 rfl rfl]
  have e0 : maskSum g (p + 1) L full p (j + 1) 0
      = ∑ T ∈ (Finset.range p).powersetCard (j + 1), maskVal g (p + 1) L full (twoPow T) := by
    have := maskSum_eq g (p + 1) L full p (j + 1) ∅ (by simp)
    simpa [twoPow] using this
  have e1 : maskSum g (p + 1) L full p j (0 + 2 ^ p)
      = ∑ T ∈ (Finset.range p).powersetCard j, maskVal g (p + 1) L full (twoPow (insert p T)) := by
    have := maskSum_eq g (p + 1) L full p j {p} (by simp)
    simpa [twoPow, add_comm] using this
  have e2 : maskSum g (p + 1) L full p j (2 ^ p) = maskSum g (p + 1) L full p j (0 + 2 ^ p) := by
    rw [zero_add]
  have key : ∑ T ∈ (Finset.range p).powersetCard (j + 1), maskVal g (p + 1) L full (twoPow T)
      = ∑ T ∈ (Finset.range p).powersetCard j, maskVal g (p + 1) L full (twoPow (insert p T)) := by
    refine Finset.sum_nbij' (fun T => Finset.range p \ T) (fun T => Finset.range p \ T) ?_ ?_ ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_powersetCard] at hT ⊢
      refine ⟨Finset.sdiff_subset, ?_⟩
      rw [Finset.card_sdiff_of_subset hT.1]; simp [hT.2]; omega
    · intro T hT
      rw [Finset.mem_powersetCard] at hT ⊢
      refine ⟨Finset.sdiff_subset, ?_⟩
      rw [Finset.card_sdiff_of_subset hT.1]; simp [hT.2]; omega
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      exact Finset.sdiff_sdiff_eq_self hT.1
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      exact Finset.sdiff_sdiff_eq_self hT.1
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      have hT1 : T ⊆ Finset.range (p + 1) := hT.1.trans (Finset.range_subset_range.mpr (Nat.le_succ p))
      have hT2 : insert p (Finset.range p \ T) ⊆ Finset.range (p + 1) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp
        · have := (Finset.mem_sdiff.mp hx).1
          exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp this))
      rw [maskVal_twoPow g (p + 1) L adj hadj full hf _ hT1, maskVal_twoPow g (p + 1) L adj hadj full hf _ hT2]
      congr 1
      rw [← cutRankN_compl adj hsym]
      congr 1
      ext i
      simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_sdiff, Finset.mem_range]
      have hi := i.2
      have := fun h : (i : ℕ) ∈ T => Finset.mem_range.mp (hT.1 h)
      by_cases hip : (i : ℕ) = p
      · have h1 := this
        rw [hip] at h1
        simp only [hip, true_or, iff_true]
        intro h; have := h1 h; omega
      · have hlt : (i : ℕ) < p := by omega
        simp [hip, hlt]
  rw [e0, e2, e1, ← key]
  ring

/-- **Halving** (`n = p + 1 = 2k`, `k = j + 1`, `p = 2j + 1`): the sum over all `k`-cuts of a symmetric graph is twice
the sum over the cuts containing the last vertex `p` (stated with `n`, `k` free so that numerals stay literal). -/
theorem sum_cuts_half (g : ℕ → ℕ) (n k p j : ℕ) (hn : n = p + 1) (hk : k = j + 1) (hp : p = 2 * j + 1)
    (L : List ℕ) (adj : Fin n → ℕ) (hadj : ∀ i, adj i = L.getD i.1 0)
    (hsym : ∀ i j : Fin n, (adj i).testBit j = (adj j).testBit i) (full : ℕ) (hf : full = 2 ^ n - 1) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, g (cutRankN adj S)
      = 2 * maskSum g n L full p j (2 ^ p) := by
  subst hn hk
  exact sum_cuts_half_aux g p j hp L adj hadj hsym full hf

end FormalResearch.FourQubitEntropy.PurityLP
