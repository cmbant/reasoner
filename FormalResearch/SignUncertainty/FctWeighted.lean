/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctJC

/-!
# Weighted Leibniz bounds (F2a, `fct:comp-cfu`)

One-variable weighted bounds `|∂^n (Y^a g) A^b| ≤ C β max(Y,A)^{max(0,a+b-n)}` used for the small-argument weights of
`(fct:V-diff-jets)`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff

namespace FormalResearch.SignUncertainty

section Weighted

/-- Weighted Leibniz bound: `∂^n (Y^a g) A^b ≤ C β W^{max(0, a+b-n)}`, `W = max Y A ≤ 4`. -/
lemma weighted_monomial {n a b : ℕ} {g : ℝ → ℝ} {Y A β : ℝ} (hY : 0 ≤ Y) (hA : 0 ≤ A) (hY4 : Y ≤ 4) (hA4 : A ≤ 4)
    (hg : ContDiffAt ℝ n g Y) (hβ : ∀ k ≤ n, |iteratedDeriv k g Y| ≤ β) :
    |iteratedDeriv n (fun s => s ^ a * g s) Y * A ^ b| ≤
      (n + 1) * 2 ^ n * (a.factorial * 4 ^ (a + b)) * β * max Y A ^ (a + b - n) := by
  have hβ0 : 0 ≤ β := (abs_nonneg _).trans (hβ 0 (Nat.zero_le _))
  have hpow : ContDiffAt ℝ n (fun s : ℝ => s ^ a) Y := (contDiff_id.pow a).contDiffAt
  rw [iteratedDeriv_fun_mul hpow hg, Finset.sum_mul]
  set W := max Y A with hW
  have hW0 : 0 ≤ W := le_max_of_le_left hY
  have hW4 : W ≤ 4 := max_le hY4 hA4
  have hterm : ∀ i ∈ Finset.range (n + 1), |(n.choose i : ℝ) * iteratedDeriv i (fun s : ℝ => s ^ a) Y *
      iteratedDeriv (n - i) g Y * A ^ b| ≤ 2 ^ n * (a.factorial * 4 ^ (a + b)) * β * W ^ (a + b - n) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [iteratedDeriv_pow]
    by_cases hia : a < i
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hia]
      simp only [Nat.cast_zero, zero_mul, mul_zero, abs_zero]
      positivity
    · push Not at hia
      have h1 : (n.choose i : ℝ) ≤ 2 ^ n := by
        exact_mod_cast (Nat.choose_le_two_pow n i)
      have h2 : (a.descFactorial i : ℝ) ≤ a.factorial := by
        have h := Nat.factorial_mul_descFactorial hia
        have : a.descFactorial i ≤ a.factorial := by
          calc a.descFactorial i = 1 * a.descFactorial i := (one_mul _).symm
            _ ≤ (a - i).factorial * a.descFactorial i := Nat.mul_le_mul_right _ (Nat.factorial_pos _)
            _ = a.factorial := h
        exact_mod_cast this
      have h3 : |iteratedDeriv (n - i) g Y| ≤ β := hβ _ (Nat.sub_le n i)
      have h4 : Y ^ (a - i) * A ^ b ≤ W ^ (a + b - i) := by
        have hYW : Y ≤ W := le_max_left _ _
        have hAW : A ≤ W := le_max_right _ _
        calc Y ^ (a - i) * A ^ b ≤ W ^ (a - i) * W ^ b := by gcongr
          _ = W ^ (a + b - i) := by rw [← pow_add]; congr 1; omega
      have h5 : W ^ (a + b - i) ≤ 4 ^ (a + b) * W ^ (a + b - n) := by
        have : a + b - i = (a + b - i - (a + b - n)) + (a + b - n) := by omega
        rw [this, pow_add]
        gcongr
        calc W ^ (a + b - i - (a + b - n)) ≤ 4 ^ (a + b - i - (a + b - n)) := by gcongr
          _ ≤ 4 ^ (a + b) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hc0 : (0 : ℝ) ≤ n.choose i := by positivity
      have hd0 : (0 : ℝ) ≤ a.descFactorial i := by positivity
      have e : (n.choose i : ℝ) * ((a.descFactorial i : ℝ) * Y ^ (a - i)) * iteratedDeriv (n - i) g Y * A ^ b =
          ((n.choose i : ℝ) * (a.descFactorial i : ℝ) * (Y ^ (a - i) * A ^ b)) * iteratedDeriv (n - i) g Y := by ring
      rw [e, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n.choose i : ℝ) * (a.descFactorial i : ℝ) * (Y ^ (a - i) * A ^ b))]
      calc _ ≤ (2 ^ n * a.factorial * (4 ^ (a + b) * W ^ (a + b - n))) * β :=
            mul_le_mul (mul_le_mul (mul_le_mul h1 h2 hd0 (by positivity)) (h4.trans h5) (by positivity)
              (by positivity)) h3 (abs_nonneg _) (by positivity)
        _ = _ := by ring
  calc |∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * iteratedDeriv i (fun s : ℝ => s ^ a) Y *
        iteratedDeriv (n - i) g Y * A ^ b|
      ≤ ∑ i ∈ Finset.range (n + 1), |(n.choose i : ℝ) * iteratedDeriv i (fun s : ℝ => s ^ a) Y *
        iteratedDeriv (n - i) g Y * A ^ b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), 2 ^ n * (a.factorial * 4 ^ (a + b)) * β * W ^ (a + b - n) :=
        Finset.sum_le_sum hterm
    _ = _ := by simp; ring

/-- The one-variable shape of the divided-difference integral: `Σ_{k<5} A^k Y^{4-k} g₀ + Y⁵ g₁`. -/
lemma weighted_E1D {n : ℕ} {g0 g1 : ℝ → ℝ} {Y A β : ℝ} (hY : 0 ≤ Y) (hA : 0 ≤ A) (hY4 : Y ≤ 4) (hA4 : A ≤ 4)
    (hg0 : ContDiffAt ℝ n g0 Y) (hg1 : ContDiffAt ℝ n g1 Y) (hβ0 : ∀ k ≤ n, |iteratedDeriv k g0 Y| ≤ β)
    (hβ1 : ∀ k ≤ n, |iteratedDeriv k g1 Y| ≤ β) :
    |iteratedDeriv n (fun s => (∑ k ∈ Finset.range 5, A ^ k * (s ^ (4 - k) * g0 s)) + s ^ 5 * g1 s) Y| ≤
      (n + 1) * 2 ^ n * 1000000 * β * max Y A ^ (4 - n) := by
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hβ0 0 (Nat.zero_le _))
  have hW0 : 0 ≤ max Y A := le_max_of_le_left hY
  have hW4 : max Y A ≤ 4 := max_le hY4 hA4
  have hpk : ∀ k ∈ Finset.range 5, ContDiffAt ℝ n (fun s : ℝ => A ^ k * (s ^ (4 - k) * g0 s)) Y :=
    fun k _ => contDiffAt_const.mul (((contDiff_id.pow _).contDiffAt).mul hg0)
  have hp5 : ContDiffAt ℝ n (fun s : ℝ => s ^ 5 * g1 s) Y := ((contDiff_id.pow _).contDiffAt).mul hg1
  rw [iteratedDeriv_fun_add (ContDiffAt.sum hpk) hp5, iteratedDeriv_fun_sum hpk]
  set W := max Y A with hW
  have hterm : ∀ i ∈ Finset.range 5, |iteratedDeriv n (fun s : ℝ => A ^ i * (s ^ (4 - i) * g0 s)) Y| ≤
      (n + 1) * 2 ^ n * (24 * 4 ^ 4) * β * W ^ (4 - n) := by
    intro i hi
    have hi4 : i ≤ 4 := by have := Finset.mem_range.mp hi; omega
    have hc : ContDiffAt ℝ n (fun s : ℝ => s ^ (4 - i) * g0 s) Y := ((contDiff_id.pow _).contDiffAt).mul hg0
    rw [iteratedDeriv_const_mul (f := fun s : ℝ => s ^ (4 - i) * g0 s) (A ^ i) hc]
    have h := weighted_monomial (n := n) (a := 4 - i) (b := i) (g := g0) hY hA hY4 hA4 hg0 hβ0
    have hf : (4 - i).factorial ≤ 24 := by
      have : (4 - i).factorial ≤ (4 : ℕ).factorial := Nat.factorial_le (Nat.sub_le 4 i)
      simpa [Nat.factorial] using this
    have hexp : 4 - i + i = 4 := by omega
    rw [hexp] at h
    calc _ = |iteratedDeriv n (fun s : ℝ => s ^ (4 - i) * g0 s) Y * A ^ i| := by rw [mul_comm]
      _ ≤ _ := h
      _ ≤ _ := by
        have : ((4 - i).factorial : ℝ) ≤ 24 := by exact_mod_cast hf
        gcongr
  have h5 : |iteratedDeriv n (fun s : ℝ => s ^ 5 * g1 s) Y| ≤
      (n + 1) * 2 ^ n * (120 * 4 ^ 5) * β * W ^ (5 - n) := by
    have h := weighted_monomial (n := n) (a := 5) (b := 0) (g := g1) hY hA hY4 hA4 hg1 hβ1
    simp only [pow_zero, mul_one, add_zero] at h
    have : ((5 : ℕ).factorial : ℝ) = 120 := by simp [Nat.factorial]
    rw [this] at h
    exact h
  have h5' : W ^ (5 - n) ≤ 4 * W ^ (4 - n) := by
    by_cases hn : n ≤ 4
    · have : 5 - n = (4 - n) + 1 := by omega
      rw [this, pow_succ]
      nlinarith [pow_nonneg hW0 (4 - n)]
    · have h1 : 5 - n = 0 := by omega
      have h2 : 4 - n = 0 := by omega
      rw [h1, h2]; norm_num
  calc _ ≤ |∑ i ∈ Finset.range 5, iteratedDeriv n (fun s : ℝ => A ^ i * (s ^ (4 - i) * g0 s)) Y| +
        |iteratedDeriv n (fun s : ℝ => s ^ 5 * g1 s) Y| := abs_add_le _ _
    _ ≤ 5 * ((n + 1) * 2 ^ n * (24 * 4 ^ 4) * β * W ^ (4 - n)) +
        (n + 1) * 2 ^ n * (120 * 4 ^ 5) * β * (4 * W ^ (4 - n)) := by
      gcongr
      · calc _ ≤ ∑ i ∈ Finset.range 5, |iteratedDeriv n (fun s : ℝ => A ^ i * (s ^ (4 - i) * g0 s)) Y| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ Finset.range 5, (n + 1) * 2 ^ n * (24 * 4 ^ 4) * β * W ^ (4 - n) := Finset.sum_le_sum hterm
          _ = _ := by simp
      · exact h5.trans (by gcongr)
    _ ≤ _ := by
      have : 0 ≤ (n + 1 : ℝ) * 2 ^ n * β * W ^ (4 - n) := by positivity
      nlinarith

/-- info: 'FormalResearch.SignUncertainty.weighted_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weighted_monomial

end Weighted
end FormalResearch.SignUncertainty
