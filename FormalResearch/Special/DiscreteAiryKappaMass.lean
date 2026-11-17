module

public import FormalResearch.Special.DiscreteAiryKappaMain

/-!
# The Gauss-weight identity `Σ_k Ŷ_k² = N` as finite-sum inequalities (plan K1, order-sharp `κ`)

`kf_mass_le` uses `ΣŶ² = N` only through `N ≤ N · sup Ŷ²`.  The order-sharp estimates need it as an *exact sum over the support*:

* `kk_mass_eq`: `Σ_{i < N - L₀} Ŷ_{L₀+i}² = N`, `L₀ = max(|M|,|σ|)`;
* `kk_sum_le`: `Σ_{k ∈ S} Ŷ_k² ≤ N` for every finite set `S ⊆ ℤ` (the chain vanishes off `[L₀, N-1]`);
* `kk_le_sum`: `N ≤ Σ_{k ∈ S} Ŷ_k²` if `S ⊇ [L₀, N-1]`.

**Claim class: proved** (from `gaussWeight_3j` and `hahn_chain_support`).
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **The Gauss-weight identity as a sum of squares of the natural-gauge chain.** -/
lemma kk_mass_eq (M σ N : ℤ) (hN : max |M| |σ| < N) (n : ℕ) (hn : (n : ℤ) < N - max |M| |σ|) :
    ∑ i ∈ Finset.range (N - max |M| |σ|).toNat,
        hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) (max |M| |σ| + (i : ℤ)) ^ 2 = N := by
  have hN0 : (0 : ℤ) < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  set L0 : ℤ := max |M| |σ| with hL0
  have hL00 : 0 ≤ L0 := le_trans (abs_nonneg M) (le_max_left _ _)
  set K : ℕ := (N - L0).toNat with hKdef
  have hK : (K : ℚ) = (N : ℚ) - max |(M : ℚ)| |(σ : ℚ)| := by
    have e : max |(M : ℚ)| |(σ : ℚ)| = (L0 : ℚ) := by rw [hL0]; push_cast; rfl
    rw [e]
    have : (K : ℤ) = N - L0 := Int.toNat_of_nonneg (by omega)
    have h2 : ((K : ℤ) : ℚ) = ((N - L0 : ℤ) : ℚ) := by rw [this]
    push_cast at h2
    exact h2
  have hnK : n < K := by omega
  have hg := (gaussWeight_3j (specAdm_int M σ N hN) (by exact_mod_cast hN0) hK hnK).1
  unfold lambdaSq3j at hg
  have hNc : (((N : ℚ) : ℝ)) = (N : ℝ) := by push_cast; rfl
  rw [hNc] at hg
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcast : (max |(M : ℚ)| |(σ : ℚ)| + (i : ℚ)) = ((L0 + (i : ℤ) : ℤ) : ℚ) := by
    have e : max |(M : ℚ)| |(σ : ℚ)| = (L0 : ℚ) := by rw [hL0]; push_cast; rfl
    rw [e]; push_cast; ring
  rw [hcast]
  have hk0 : (0 : ℝ) ≤ ((L0 + (i : ℤ) : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ L0 + (i : ℤ))
  unfold hahn3jY
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  push_cast; ring

/-- `Σ_{k∈S} Ŷ_k² ≤ N` for every finite `S ⊆ ℤ`. -/
lemma kk_sum_le (M σ N : ℤ) (hN : max |M| |σ| < N) (n : ℕ) (hn : (n : ℤ) < N - max |M| |σ|) (S : Finset ℤ) :
    ∑ k ∈ S, hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k ^ 2 ≤ N := by
  have h := kk_mass_eq M σ N hN n hn
  set L0 : ℤ := max |M| |σ| with hL0
  set y : ℤ → ℝ := fun k => hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k ^ 2 with hy
  have hy0 : ∀ k, 0 ≤ y k := fun k => sq_nonneg _
  have hsupp : ∀ k, k ∉ Finset.Ico L0 N → y k = 0 := by
    intro k hk
    simp only [hy]
    rw [hahn_chain_support M σ N _ k, sq]; · simp
    intro ⟨h1, h2, h3⟩
    exact hk (Finset.mem_Ico.2 ⟨max_le h1 h2, by omega⟩)
  have hIco : Finset.Ico L0 N = (Finset.range (N - L0).toNat).image (fun i : ℕ => L0 + (i : ℤ)) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      exact ⟨(k - L0).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  have hsum : ∑ k ∈ Finset.Ico L0 N, y k = N := by
    rw [hIco, Finset.sum_image (by intro i _ j _ hij; simpa using hij)]
    exact h
  calc ∑ k ∈ S, y k = ∑ k ∈ S.filter (fun k => k ∈ Finset.Ico L0 N), y k := by
        rw [Finset.sum_filter_of_ne]
        intro k _ hne
        by_contra hk
        exact hne (hsupp k hk)
    _ ≤ ∑ k ∈ Finset.Ico L0 N, y k :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.1 hk).2) (fun k _ _ => hy0 k)
    _ = N := hsum

/-- `N ≤ Σ_{k∈S} Ŷ_k²` for every finite `S ⊇ [L₀, N-1]`. -/
lemma kk_le_sum (M σ N : ℤ) (hN : max |M| |σ| < N) (n : ℕ) (hn : (n : ℤ) < N - max |M| |σ|) (S : Finset ℤ)
    (hS : ∀ k : ℤ, max |M| |σ| ≤ k → k < N → k ∈ S) :
    (N : ℝ) ≤ ∑ k ∈ S, hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k ^ 2 := by
  have h := kk_mass_eq M σ N hN n hn
  set L0 : ℤ := max |M| |σ| with hL0
  have hIco : Finset.Ico L0 N = (Finset.range (N - L0).toNat).image (fun i : ℕ => L0 + (i : ℤ)) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      exact ⟨(k - L0).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [← h, ← Finset.sum_image (f := fun k : ℤ => hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) k ^ 2)
    (s := Finset.range (N - L0).toNat) (g := fun i : ℕ => L0 + (i : ℤ)) (by intro i _ j _ hij; simpa using hij), ← hIco]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => hS k (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2)
    (fun k _ _ => sq_nonneg _)

/-- info: 'FormalResearch.Special.kk_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kk_sum_le

/-- info: 'FormalResearch.Special.kk_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kk_le_sum

end FormalResearch.Special
