import FormalResearch.FourQubitEntropy.PurityLPGraphMean

/-!
# Block decomposition of the rank sum without filtering

`PurityLPGraphMean.lean` splits `Σ_{|S| = k}` according to `S ∩ A = T` (`blk`).  Evaluating `blk` by filtering all
`k`-subsets is as expensive as the whole sum, so here the block is rewritten (`blk'`) as a sum over the
`(k - |T|)`-subsets `S'` of the complement of `A`, with `S = T ∪ S'`.  `total_of_blocks'` is the form used by the
generated data modules `PurityLPGraphData16/17/18.lean`: the blocks are separate `decide +kernel` declarations, so
the kernel's cache is released between them.
-/

open scoped BigOperators

namespace FormalResearch.FourQubitEntropy.PurityLP

variable {n : ℕ}

theorem filter_eq_image (A T : Finset (Fin n)) (hT : T ⊆ A) (k : ℕ) (hk : T.card ≤ k) :
    ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => S ∩ A = T)
      = ((Finset.univ \ A).powersetCard (k - T.card)).image (fun S' => T ∪ S') := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hS, hSA⟩
    refine ⟨S \ A, ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      simp only [Finset.mem_sdiff] at hx ⊢
      exact ⟨Finset.mem_univ _, hx.2⟩
    · have := Finset.card_inter_add_card_sdiff S A
      rw [hSA] at this
      omega
    · rw [← hSA]
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
  · rintro ⟨S', ⟨hS'sub, hS'card⟩, rfl⟩
    have hdisj : Disjoint T S' := by
      rw [Finset.disjoint_left]
      intro x hxT hxS
      have := hS'sub hxS
      simp only [Finset.mem_sdiff] at this
      exact this.2 (hT hxT)
    refine ⟨?_, ?_⟩
    · rw [Finset.card_union_of_disjoint hdisj]; omega
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hxA⟩
        · exact h
        · have := hS'sub h
          simp only [Finset.mem_sdiff] at this
          exact absurd hxA this.2
      · intro hx; exact ⟨Or.inl hx, hT hx⟩

/-- The block `S ∩ A = T`, enumerated directly as `S = T ∪ S'`. -/
def blk' (adj : Fin n → ℕ) (k : ℕ) (A T : Finset (Fin n)) : ℕ :=
  ∑ S' ∈ (Finset.univ \ A).powersetCard (k - T.card), 2 ^ (k - cutRankN adj (T ∪ S'))

theorem blk_eq_blk' (adj : Fin n → ℕ) (k : ℕ) (A T : Finset (Fin n)) (hT : T ⊆ A) (hk : T.card ≤ k) :
    blk adj k A T = blk' adj k A T := by
  unfold blk blk'
  rw [filter_eq_image A T hT k hk, Finset.sum_image]
  intro S₁ h₁ S₂ h₂ h
  simp only [Finset.mem_coe, Finset.mem_powersetCard] at h₁ h₂
  have e : ∀ S', S' ⊆ Finset.univ \ A → (T ∪ S') \ A = S' := by
    intro S' hS'
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hxA⟩
      · exact absurd (hT h) hxA
      · exact h
    · intro hx
      have := hS' hx
      simp only [Finset.mem_sdiff] at this
      exact ⟨Or.inr hx, this.2⟩
  rw [← e S₁ h₁.1, ← e S₂ h₂.1]
  simp only at h
  rw [h]

theorem total_of_blocks' (adj : Fin n → ℕ) (k : ℕ) (A : Finset (Fin n)) (hAk : A.card ≤ k)
    (TL : List (Finset (Fin n))) (Ns : List ℕ) (hTL : A.powerset.val = (TL : Multiset (Finset (Fin n))))
    (h : List.Forall₂ (fun T N => blk' adj k A T = N) TL Ns) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, 2 ^ (k - cutRankN adj S) = Ns.sum := by
  rw [sum_blocks adj k A]
  have h1 : ∑ T ∈ A.powerset, blk adj k A T = ∑ T ∈ A.powerset, blk' adj k A T := by
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTA : T ⊆ A := Finset.mem_powerset.mp hT
    exact blk_eq_blk' adj k A T hTA ((Finset.card_le_card hTA).trans hAk)
  rw [h1]
  have h2 : ∀ {TL : List (Finset (Fin n))} {Ns : List ℕ},
      List.Forall₂ (fun T N => blk' adj k A T = N) TL Ns → TL.map (blk' adj k A) = Ns := by
    intro TL Ns h
    induction h with
    | nil => rfl
    | cons h1 _ ih => simp [h1, ih]
  replace h2 := h2 h
  show (A.powerset.val.map (blk' adj k A)).sum = _
  rw [hTL, Multiset.map_coe, Multiset.sum_coe, h2]

end FormalResearch.FourQubitEntropy.PurityLP
