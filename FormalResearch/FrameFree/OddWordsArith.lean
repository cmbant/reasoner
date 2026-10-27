import Mathlib

/-!
# Binomial arithmetic for the string decomposition (Paper P, `prop:oddwords` (iii))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

`hwDim n k = C(n,k) - C(n,k-1)` and `sum_string_dim`: `Σ_{k ≤ n/2} (n-2k+1) hwDim n k = 2^n`, the
dimension count of the `sl₂` string decomposition of `(ℂ²)^{⊗n}` (`Σ_j (2j+1) g_j = 2^n`).
-/

set_option autoImplicit false

open Finset

namespace FormalResearch.FrameFree.OddWords


theorem choose_split (n : ℕ) :
    ∑ k ∈ range (n / 2 + 1), n.choose k + ∑ j ∈ range (n - n / 2), n.choose j = 2 ^ n := by
  obtain ⟨a, b, hab⟩ : ∃ a b, a = n / 2 + 1 ∧ b = n - n / 2 := ⟨_, _, rfl, rfl⟩
  have h2 : n + 1 = a + b := by omega
  have h1 : ∑ k ∈ range (a + b), n.choose k = 2 ^ n := by
    rw [← h2]; exact Nat.sum_range_choose n
  rw [Finset.sum_range_add] at h1
  have h3 : ∑ x ∈ range b, n.choose (a + x) = ∑ j ∈ range b, n.choose j := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have e : a + (b - 1 - j) = n - j := by omega
    rw [e]; exact Nat.choose_symm (by omega)
  rw [h3] at h1
  rw [hab.1, hab.2] at h1
  exact h1

/-- `dim HW_k = C(n,k) - C(n,k-1)` (with `C(n,-1) = 0`): the SU(2)-multiplicity of total spin `n/2 - k`
among `n` spin-`1/2`. -/
def hwDim (n k : ℕ) : ℕ := n.choose k - (if k = 0 then 0 else n.choose (k - 1))

theorem hwDim_zero (n : ℕ) : hwDim n 0 = 1 := by simp [hwDim]

theorem hwDim_succ_add {n m : ℕ} (hm : 2 * (m + 1) ≤ n) :
    hwDim n (m + 1) + n.choose m = n.choose (m + 1) := by
  have : n.choose m ≤ n.choose (m + 1) := Nat.choose_le_succ_of_lt_half_left (by omega)
  simp only [hwDim, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
  omega

theorem sum_string_aux (n : ℕ) : ∀ M : ℕ, 2 * M ≤ n →
    ∑ k ∈ range (M + 1), (n - 2 * k + 1) * hwDim n k
      = (n - 2 * M + 1) * n.choose M + 2 * ∑ k ∈ range M, n.choose k := by
  intro M
  induction M with
  | zero => intro _; simp [hwDim_zero]
  | succ M ih =>
    intro hM
    rw [Finset.sum_range_succ, ih (by omega), Finset.sum_range_succ _ M]
    have h := hwDim_succ_add hM
    obtain ⟨N, hN⟩ : ∃ N, n = 2 * (M + 1) + N := ⟨n - 2 * (M + 1), by omega⟩
    have e1 : n - 2 * M + 1 = N + 3 := by omega
    have e2 : n - 2 * (M + 1) + 1 = N + 1 := by omega
    have e3 : n - 2 * (M + 1) + 1 = N + 1 := e2
    rw [e1, e2]
    nlinarith [h]

theorem sum_string_dim (n : ℕ) :
    ∑ k ∈ range (n / 2 + 1), (n - 2 * k + 1) * hwDim n k = 2 ^ n := by
  rw [sum_string_aux n (n / 2) (by omega), ← choose_split n]
  have hd : n - n / 2 = n / 2 + (n - 2 * (n / 2)) := by omega
  have hd2 : n - 2 * (n / 2) = 0 ∨ n - 2 * (n / 2) = 1 := by omega
  rw [hd]
  rcases hd2 with h | h
  · rw [h]; simp [Finset.sum_range_succ]; ring
  · rw [h]; simp [Finset.sum_range_succ]; ring

end FormalResearch.FrameFree.OddWords
