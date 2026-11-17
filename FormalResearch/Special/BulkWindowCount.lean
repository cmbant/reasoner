module

public import FormalResearch.Special.BulkIndexCount

/-!
# Bulk window, part 3: abstract node count of a noisy lattice sampling of a function with counted sign changes

Abstract counting theorem for the Airy window (compare `BulkIndexCount.bix_count`, the amplitude-phase version).  Let `u : ℕ → ℝ` be a
sequence on the sites `k₀ ≤ j ≤ k₁` with

* `|u_j - s A_j f_j| ≤ E A_j` (`s = ±1`, `A_j > 0`, `E ≥ 0`): `u` is a noisy positive multiple of the sampling `f_j` of a function `f`;
* an integer-valued `z_j` (the number of zeros of `f` to the right of the site) with `(-1)^{z_j} f_j > 0` whenever `f_j ≠ 0`;
* `z_{j+1} ≤ z_j ≤ z_{j+1} + 1` (at most one zero of `f` between consecutive sites);
* every interior site with `|f_j| ≤ E` (a near-zero, *indefinite* site) has definite neighbours of opposite signs, `E < |f_{j±1}|`,
  `f_{j-1} f_{j+1} < 0`.

Then (`bwn_count`) for definite sites `k ≤ k'` (`E < |f|`) the number of nodes (`bix_c`: sign changes `u_j u_{j+1} < 0` plus interior zeros)
in the bonds `k, …, k'-1` is exactly `z_k - z_{k'}`.  The value of `u` at an indefinite site is irrelevant.

**Claim class: proved** (elementary: signs and induction on the site index).  **Not formalised:** that the hypotheses hold for a given
chain (that is `BulkWindowChart`).
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- The hypotheses of the abstract window count (see the module docstring). -/
structure BwnWin (u f A : ℕ → ℝ) (z : ℕ → ℕ) (s E : ℝ) (k₀ k₁ : ℕ) : Prop where
  hs : s = 1 ∨ s = -1
  hE : 0 ≤ E
  hA : ∀ j, k₀ ≤ j → j ≤ k₁ → 0 < A j
  hu : ∀ j, k₀ ≤ j → j ≤ k₁ → |u j - s * A j * f j| ≤ E * A j
  hsign : ∀ j, k₀ ≤ j → j ≤ k₁ → f j ≠ 0 → 0 < (-1 : ℝ) ^ z j * f j
  hz : ∀ j, k₀ ≤ j → j < k₁ → z (j + 1) ≤ z j ∧ z j ≤ z (j + 1) + 1
  hnd : ∀ j, k₀ < j → j < k₁ → |f j| ≤ E → E < |f (j - 1)| ∧ E < |f (j + 1)| ∧ f (j - 1) * f (j + 1) < 0

namespace BwnWin

variable {u f A : ℕ → ℝ} {z : ℕ → ℕ} {s E : ℝ} {k₀ k₁ : ℕ}

private lemma sq_neg_one_pow (n : ℕ) : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

/-- At a definite site `ε s u_j > 0` with `ε = (-1)^{z_j}`. -/
theorem sign_pos (W : BwnWin u f A z s E k₀ k₁) {j : ℕ} (h0 : k₀ ≤ j) (h1 : j ≤ k₁) (hD : E < |f j|) :
    0 < (-1 : ℝ) ^ z j * s * u j := by
  have hA := W.hA j h0 h1
  have hY := W.hu j h0 h1
  have hf : f j ≠ 0 := by intro h; rw [h] at hD; simp at hD; linarith [W.hE]
  have hsg := W.hsign j h0 h1 hf
  set ε : ℝ := (-1 : ℝ) ^ z j with hε
  have hεε : ε * ε = 1 := sq_neg_one_pow _
  have hss : s * s = 1 := by rcases W.hs with h | h <;> rw [h] <;> norm_num
  have h1 : |ε| = 1 := by
    have : |ε| * |ε| = 1 := by rw [← abs_mul, hεε]; simp
    nlinarith [abs_nonneg ε]
  have h2 : |s| = 1 := by
    have : |s| * |s| = 1 := by rw [← abs_mul, hss]; simp
    nlinarith [abs_nonneg s]
  have hεf : ε * f j = |f j| := by
    have : |ε * f j| = |f j| := by rw [abs_mul, h1, one_mul]
    rw [← this, abs_of_pos hsg]
  have e : ε * s * u j = ε * s * (u j - s * A j * f j) + A j * (ε * f j) := by
    linear_combination (A j * ε * f j) * hss
  have hb : |ε * s * (u j - s * A j * f j)| ≤ E * A j := by
    rw [abs_mul, abs_mul, h1, h2, one_mul, one_mul]; exact hY
  have hb' := (abs_le.1 hb).1
  rw [e]
  rw [hεf] at *
  nlinarith


private lemma pow_succ_neg (n : ℕ) : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by rw [pow_succ]; ring

private lemma pow_succ2_neg (n : ℕ) : (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n := by rw [pow_add]; norm_num

/-- Two definite sites: the product of the signs of `u`. -/
theorem prod_signs (W : BwnWin u f A z s E k₀ k₁) {i j : ℕ} (hi0 : k₀ ≤ i) (hi1 : i ≤ k₁) (hj0 : k₀ ≤ j)
    (hj1 : j ≤ k₁) (hi : E < |f i|) (hj : E < |f j|) :
    ((-1 : ℝ) ^ z i = (-1 : ℝ) ^ z j → 0 < u i * u j) ∧ ((-1 : ℝ) ^ z i = -((-1 : ℝ) ^ z j) → u i * u j < 0) :=
  bix_prod_aux _ _ s (u i) (u j) (sq_neg_one_pow _) (sq_neg_one_pow _) (bix_sq_s W.hs) (W.sign_pos hi0 hi1 hi)
    (W.sign_pos hj0 hj1 hj)

/-- One bond between two definite sites contributes the drop of `z`. -/
theorem step1 (W : BwnWin u f A z s E k₀ k₁) {j : ℕ} (h0 : k₀ ≤ j) (h1 : j < k₁) (hj : E < |f j|)
    (hj' : E < |f (j + 1)|) : (bix_c u j : ℤ) = (z j : ℤ) - z (j + 1) := by
  obtain ⟨d1, d2⟩ := W.hz j h0 h1
  have z1 := W.sign_pos h0 h1.le hj
  have hs := prod_signs W h0 h1.le (j := j + 1) (by omega) h1 hj hj'
  have hne : u j ≠ 0 := by
    intro h; rw [h] at z1; simp at z1
  unfold bix_c
  have : z j = z (j + 1) ∨ z j = z (j + 1) + 1 := by omega
  rcases this with h | h
  · have : 0 < u j * u (j + 1) := hs.1 (by rw [h])
    simp [hne, this.not_gt, h]
  · have : u j * u (j + 1) < 0 := hs.2 (by rw [h, pow_succ_neg])
    simp [hne, this, h]

/-- Two bonds around an indefinite site contribute exactly the drop of `z`. -/
theorem step2 (W : BwnWin u f A z s E k₀ k₁) {j : ℕ} (h0 : k₀ ≤ j) (h2 : j + 1 < k₁) (hj : E < |f j|)
    (hm : ¬ E < |f (j + 1)|) (hj' : E < |f (j + 2)|) :
    (bix_c u j : ℤ) + bix_c u (j + 1) = (z j : ℤ) - z (j + 2) := by
  obtain ⟨d1, d1'⟩ := W.hz j h0 (by omega)
  obtain ⟨d2, d2'⟩ : z (j + 2) ≤ z (j + 1) ∧ z (j + 1) ≤ z (j + 2) + 1 := W.hz (j + 1) (by omega) h2
  obtain ⟨-, -, hff⟩ := W.hnd (j + 1) (by omega) h2 (not_lt.1 hm)
  simp only [Nat.add_sub_cancel] at hff
  have hf1 : f j ≠ 0 := by intro h; rw [h] at hj; simp at hj; linarith [W.hE]
  have hf2 : f (j + 2) ≠ 0 := by intro h; rw [h] at hj'; simp at hj'; linarith [W.hE]
  have g1 := W.hsign j h0 (by omega) hf1
  have g2 := W.hsign (j + 2) (by omega) (by omega) hf2
  have hz1 : z j = z (j + 2) + 1 := by
    by_contra hne
    have hc : z j = z (j + 2) ∨ z j = z (j + 2) + 2 := by omega
    have heq : (-1 : ℝ) ^ z j = (-1 : ℝ) ^ z (j + 2) := by
      rcases hc with h | h
      · rw [h]
      · rw [h, pow_succ2_neg]
    have := mul_pos g1 g2
    rw [heq] at this
    have h3 : 0 < ((-1 : ℝ) ^ z (j + 2) * (-1 : ℝ) ^ z (j + 2)) * (f j * f (j + 2)) := by nlinarith
    rw [sq_neg_one_pow, one_mul] at h3
    linarith
  have hac : u j * u (j + 2) < 0 :=
    (prod_signs W h0 (by omega) (j := j + 2) (by omega) (by omega) hj hj').2 (by rw [hz1, pow_succ_neg])
  rw [show (z j : ℤ) - z (j + 2) = 1 by omega]
  have z1 := W.sign_pos h0 (by omega) hj
  have hne : u j ≠ 0 := by intro h; rw [h] at z1; simp at z1
  have := bix_sign3 (u j) (u (j + 1)) (u (j + 2)) hne hac
  unfold bix_c
  have hj1 : 0 < j + 1 := by omega
  simp only [hne, and_false, ite_false, add_zero, hj1, true_and]
  exact_mod_cast this

/-- **Node count.**  For definite sites `k ≤ k'` of the window, the number of nodes in the bonds `k, …, k'-1` is `z_k - z_{k'}`. -/
theorem count (W : BwnWin u f A z s E k₀ k₁) :
    ∀ d k : ℕ, k₀ ≤ k → k + d ≤ k₁ → E < |f k| → E < |f (k + d)| →
      ((∑ j ∈ Ico k (k + d), bix_c u j : ℕ) : ℤ) = (z k : ℤ) - z (k + d) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k h0 h1 hk hkd
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hcase : E < |f (k + d - 1)| ∨ (d ≥ 2 ∧ ¬ E < |f (k + d - 1)|) := by
        by_cases hD : E < |f (k + d - 1)|
        · exact Or.inl hD
        · refine Or.inr ⟨?_, hD⟩
          by_contra hlt
          have : d = 1 := by omega
          subst this
          exact hD (by simpa using hk)
      rcases hcase with hD | ⟨hd2, hD⟩
      · have ih' := ih (d - 1) (by omega) k h0 (by omega) hk (by
          have : k + (d - 1) = k + d - 1 := by omega
          rw [this]; exact hD)
        have e : k + d = (k + (d - 1)) + 1 := by omega
        have step := step1 W (j := k + (d - 1)) (by omega) (by omega) (by
          have : k + (d - 1) = k + d - 1 := by omega
          rw [this]; exact hD) (by rw [← e]; exact hkd)
        rw [e, sum_Ico_succ_top (by omega)]
        push_cast at ih' ⊢
        rw [ih', step]
        have : k + (d - 1) + 1 = k + d := by omega
        rw [this] at *
        ring
      · -- an indefinite site just before the end: its left neighbour is definite
        have hnd := W.hnd (k + d - 1) (by omega) (by omega) (not_lt.1 hD)
        have hD' : E < |f (k + (d - 2))| := by
          have := hnd.1
          have e2 : k + d - 1 - 1 = k + (d - 2) := by omega
          rwa [e2] at this
        have ih' := ih (d - 2) (by omega) k h0 (by omega) hk hD'
        have e : k + d = (k + (d - 2)) + 2 := by omega
        have hm : ¬ E < |f (k + (d - 2) + 1)| := by
          have : k + (d - 2) + 1 = k + d - 1 := by omega
          rw [this]; exact hD
        have step := step2 W (j := k + (d - 2)) (by omega) (by omega) hD' hm (by rw [← e]; exact hkd)
        have hsum : ∑ j ∈ Ico k (k + d), bix_c u j =
            ∑ j ∈ Ico k (k + (d - 2)), bix_c u j + bix_c u (k + (d - 2)) + bix_c u (k + (d - 2) + 1) := by
          rw [e, sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega)]
        rw [hsum]
        push_cast at ih' ⊢
        have : k + (d - 2) + 2 = k + d := by omega
        rw [this] at step
        linarith

end BwnWin

end FormalResearch.Special

/-- info: 'FormalResearch.Special.BwnWin.count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.BwnWin.count
