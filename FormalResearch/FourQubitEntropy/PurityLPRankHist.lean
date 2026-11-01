import FormalResearch.FourQubitEntropy.PurityLPMaskSum

/-!
# Rank histograms from a packed rank sum

A single kernel computation of the packed sum `Σ_{|S| = k} B^{rk_2 Γ[S,S^c]}` (`B = 2^16 > C(n,k)`) determines the whole
rank histogram (`hist_of_packed`: base-`B` digits are unique) and hence the rank sum `Σ 2^{k - rk}` (`rankSum_of_hist`).
-/

open scoped BigOperators

namespace FormalResearch.FourQubitEntropy.PurityLP

/-- The packing weight `B^r`, `B = 2^16 > C(n, ⌊n/2⌋)` for every `n ≤ 18`. -/
def packG (r : ℕ) : ℕ := 65536 ^ r

theorem digits_unique (B : ℕ) (hB : 0 < B) : ∀ (R : ℕ) (a b : ℕ → ℕ), (∀ r, a r < B) → (∀ r, b r < B) →
    ∑ r ∈ Finset.range R, a r * B ^ r = ∑ r ∈ Finset.range R, b r * B ^ r → ∀ r < R, a r = b r := by
  intro R
  induction R with
  | zero => intro a b _ _ _ r hr; omega
  | succ R ih =>
    intro a b ha hb h r hr
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    have hx : ∀ c : ℕ → ℕ, ∑ i ∈ Finset.range R, c (i + 1) * B ^ (i + 1)
        = B * ∑ i ∈ Finset.range R, c (i + 1) * B ^ i := by
      intro c
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [hx, pow_zero, mul_one] at h
    have h0 : a 0 = b 0 := by
      have := congrArg (· % B) h
      simp only [Nat.mul_add_mod] at this
      rwa [Nat.mod_eq_of_lt (ha 0), Nat.mod_eq_of_lt (hb 0)] at this
    have h1 : ∑ i ∈ Finset.range R, a (i + 1) * B ^ i = ∑ i ∈ Finset.range R, b (i + 1) * B ^ i := by
      rw [h0] at h
      have := Nat.add_right_cancel h
      exact Nat.eq_of_mul_eq_mul_left hB this
    cases r with
    | zero => exact h0
    | succ r => exact ih (fun i => a (i + 1)) (fun i => b (i + 1)) (fun i => ha _) (fun i => hb _) h1 r (by omega)

variable {n : ℕ}

theorem sum_by_rank (adj : Fin n → ℕ) (k : ℕ) (f : ℕ → ℕ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, f (cutRankN adj S)
      = ∑ r ∈ Finset.range (k + 1),
          (((Finset.univ : Finset (Fin n)).powersetCard k).filter fun S => cutRankN adj S = r).card * f r := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := cutRankN adj) (t := Finset.range (k + 1))]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f r) (fun S hS => by rw [(Finset.mem_filter.mp hS).2])]
    simp
  · intro S hS
    have := cutRankN_le adj S
    rw [(Finset.mem_powersetCard.mp hS).2] at this
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le this)

/-- A packed rank sum `Σ B^{rk} = Σ_r c_r B^r` (`c_r < B`) is the rank histogram `c`. -/
theorem hist_of_packed (adj : Fin n → ℕ) (k B : ℕ) (hC : n.choose k < B) (cl : List ℕ) (hcl : ∀ c ∈ cl, c < B)
    (hlen : cl.length = k + 1)
    (h : ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, B ^ cutRankN adj S
      = ∑ r ∈ Finset.range (k + 1), cl.getD r 0 * B ^ r) :
    ∀ r, ((((Finset.univ : Finset (Fin n)).powersetCard k).filter fun S => cutRankN adj S = r).card)
      = cl.getD r 0 := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) hC
  have hcard : ∀ r, ((((Finset.univ : Finset (Fin n)).powersetCard k).filter fun S => cutRankN adj S = r).card) < B := by
    intro r
    refine lt_of_le_of_lt (Finset.card_filter_le _ _) ?_
    simpa [Finset.card_powersetCard] using hC
  have hget : ∀ r, cl.getD r 0 < B := by
    intro r
    by_cases hr : r < cl.length
    · rw [List.getD_eq_getElem _ _ hr]; exact hcl _ (List.getElem_mem hr)
    · rw [List.getD_eq_default _ _ (not_lt.mp hr)]; exact hB
  rw [sum_by_rank adj k (fun r => B ^ r)] at h
  intro r
  by_cases hr : r < k + 1
  · exact digits_unique B hB (k + 1) _ _ hcard hget h r hr
  · rw [List.getD_eq_default _ _ (by omega)]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro S hS hSr
    have := cutRankN_le adj S
    rw [(Finset.mem_powersetCard.mp hS).2] at this
    omega

theorem rankSum_of_hist (adj : Fin n → ℕ) (k : ℕ) (cl : List ℕ)
    (hist : ∀ r, ((((Finset.univ : Finset (Fin n)).powersetCard k).filter fun S => cutRankN adj S = r).card)
      = cl.getD r 0) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, 2 ^ (k - cutRankN adj S)
      = ∑ r ∈ Finset.range (k + 1), cl.getD r 0 * 2 ^ (k - r) := by
  rw [sum_by_rank adj k (fun r => 2 ^ (k - r))]
  exact Finset.sum_congr rfl fun r _ => by rw [hist r]

end FormalResearch.FourQubitEntropy.PurityLP
