module

public import FormalResearch.Special.AiryZeroSpacing

/-!
# Lemma Z of the CFT survey: `a_n = -((3π/2)(n - 1/4))^{2/3} + O(n^{-4/3})`

With `t_n = (3π/2)(n - 1/4) = (3π/8)(4n - 1)` (DLMF 9.9.18) the first-order zero asymptotics (DLMF 9.9.6) read
`a_n = -t_n^{2/3} + δ_n`; DLMF 9.9.18's second term gives `δ_n = -(5/48) t_n^{-4/3} + O(t_n^{-10/3})`.  Here the bound
that follows from the phase theorem `airyZero_phase_r` alone is proved, with explicit constant:

* `airyMin_lemma`: for `a, b > 0`, `|a² - b²| min(a,b) ≤ |a³ - b³|`;
* **`airyZero_delta`**: for `n ≥ 2`, `|a_n + t_n^{2/3}| ≤ 0.1 n^{-4/3}`; cubic form `airyZero_delta_cube`:
  `n⁴ |a_n + t_n^{2/3}|³ ≤ 0.0008`.

(The CFT survey's `δ_k = O(k^{-4/3})` consequence of "Lemma Z"; the actual `|δ_n| n^{4/3}` decreases from `0.0155` (`n = 2`) to
`0.0140` (`n = 5`) and tends to `(5/48)(3π/2)^{-4/3} = 0.0132…`; mpmath, `2 ≤ n < 400`.)  The `5/(48 t²)` second term itself
(`δ_n = -(5/48) t_n^{-4/3} + O(t_n^{-10/3})`, DLMF 9.9.18) is proved in `AiryZeroSecondOrder` (`airyZero_second_order`,
`airyZero_delta_second`, `n ≥ 2`, constant `2` not sharp), which also gives `∃ C ∀ n ≥ 1` (`airyZero_delta_exists`, absorbing
`n = 1`).  The next coefficient `-(5/36) t^{-4}` is `airyZero_third_order` (`AiryZeroThird`).  **Not formalised:** the zeros of `Ai'`
(DLMF 9.9.19).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special

/-- `|a² - b²| · min(a, b) ≤ |a³ - b³|` for `a, b > 0`. -/
lemma airyMin_lemma {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a ^ 2 - b ^ 2| * min a b ≤ |a ^ 3 - b ^ 3| := by
  rcases le_total b a with h | h
  · rw [min_eq_right h, abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith [pow_le_pow_left₀ hb.le h 3])]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg a), mul_nonneg (sub_nonneg.mpr h) (mul_pos ha hb).le]
  · rw [min_eq_left h, abs_of_nonpos (by nlinarith), abs_of_nonpos (by nlinarith [pow_le_pow_left₀ ha.le h 3])]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg b), mul_nonneg (sub_nonneg.mpr h) (mul_pos ha hb).le]

/-- **Cubic form**: `n⁴ |a_n + t_n^{2/3}|³ ≤ 0.0008` for `n ≥ 2`, `t_n = (3π/2)(n - 1/4)`. -/
theorem airyZero_delta_cube {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ 4 * |airyZero n + (3 * π / 2 * ((n : ℝ) - 1 / 4)) ^ (2 / 3 : ℝ)| ^ 3 ≤ 0.0008 := by
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set t := 3 * π / 2 * ((n : ℝ) - 1 / 4) with ht
  have ht0 : 0 < t := by rw [ht]; nlinarith [Real.pi_pos]
  set w := t ^ (1 / 3 : ℝ) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos ht0 _
  have hw3 : w ^ 3 = t := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hw2 : t ^ (2 / 3 : ℝ) = w ^ 2 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  rw [hw2]
  set ρ := airyZeroRoot n with hρ
  have hρ0 := airyZeroRoot_pos n
  have hρ2 : 2 < ρ := two_lt_airyZeroRoot hn
  obtain ⟨hc1, -⟩ := airyZero_cube_bounds hn
  have hρ3 : 8 < ρ ^ 3 := by nlinarith [pow_lt_pow_left₀ hρ2 (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : 3 ≠ 0)]
  have hph := abs_le.mp (airyZero_phase_r hn)
  have hdiff : |ρ ^ 3 - w ^ 3| ≤ 0.6 / ρ ^ 3 := by
    rw [hw3, abs_le]
    have e : (2 : ℝ) / 5 / ρ ^ 3 * (3 / 2) = 0.6 / ρ ^ 3 := by field_simp; norm_num
    constructor <;> nlinarith [hph.1, hph.2, e]
  have hδ : airyZero n + w ^ 2 = -(ρ ^ 2 - w ^ 2) := by
    rw [airyZero_eq_neg_root_sq n]; ring
  rw [hδ, abs_neg]
  have hm := airyMin_lemma hρ0 hw0
  set m := min ρ w with hmdef
  have hm0 : 0 < m := lt_min hρ0 hw0
  have hmcube : 4.08 * (n : ℝ) ≤ m ^ 3 := by
    rcases min_choice ρ w with h | h
    · rw [hmdef, h]; exact hc1
    · rw [hmdef, h, hw3, ht]; nlinarith [Real.pi_pos]
  set d := |ρ ^ 2 - w ^ 2| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  -- d * m * ρ³ ≤ 0.6
  have h1 : d * m * ρ ^ 3 ≤ 0.6 := by
    have hmd : d * m ≤ 0.6 / ρ ^ 3 := hm.trans hdiff
    calc d * m * ρ ^ 3 ≤ (0.6 / ρ ^ 3) * ρ ^ 3 := mul_le_mul_of_nonneg_right hmd (by positivity)
      _ = 0.6 := by field_simp
  have h2 : (d * m * ρ ^ 3) ^ 3 ≤ 0.6 ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  have h3 : (d * m * ρ ^ 3) ^ 3 = d ^ 3 * m ^ 3 * (ρ ^ 3) ^ 3 := by ring
  rw [h3] at h2
  have h4 : 4.08 * (n : ℝ) * (4.08 * (n : ℝ)) ^ 3 ≤ m ^ 3 * (ρ ^ 3) ^ 3 :=
    mul_le_mul hmcube (pow_le_pow_left₀ (by positivity) hc1 3) (by positivity) (by positivity)
  have h5 : d ^ 3 * (4.08 * (n : ℝ) * (4.08 * (n : ℝ)) ^ 3) ≤ 0.6 ^ 3 := by
    calc _ ≤ d ^ 3 * (m ^ 3 * (ρ ^ 3) ^ 3) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = d ^ 3 * m ^ 3 * (ρ ^ 3) ^ 3 := by ring
      _ ≤ _ := h2
  nlinarith [pow_pos (by linarith : (0 : ℝ) < n) 4, pow_nonneg hd0 3]

/-- **Lemma Z (explicit `O(n^{-4/3})` form)**: for `n ≥ 2`, `|a_n + ((3π/2)(n - 1/4))^{2/3}| ≤ 0.1 n^{-4/3}`. -/
theorem airyZero_delta {n : ℕ} (hn : 2 ≤ n) :
    |airyZero n + (3 * π / 2 * ((n : ℝ) - 1 / 4)) ^ (2 / 3 : ℝ)| ≤ 0.1 * (n : ℝ) ^ (-(4 / 3) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := airyZero_delta_cube hn
  refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by positivity) ?_
  have e : ((n : ℝ) ^ (-(4 / 3) : ℝ)) ^ 3 = 1 / (n : ℝ) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, show (-(4 / 3) : ℝ) * ((3 : ℕ) : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hn0.le, Real.rpow_natCast, one_div]
  rw [mul_pow, e]
  have h4 : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
  rw [show (0.1 : ℝ) ^ 3 * (1 / (n : ℝ) ^ 4) = 0.001 / (n : ℝ) ^ 4 by ring, le_div_iff₀ h4]
  nlinarith

/-- info: 'FormalResearch.Special.airyZero_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_delta

end FormalResearch.Special
