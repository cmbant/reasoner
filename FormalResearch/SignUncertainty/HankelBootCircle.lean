module

public import FormalResearch.Special.AiryGoodCircles

/-!
# Good circles in a real window (M5-S6a)

`good_circle_exists` gives a good radius in `[k, k+1]` for an integer `k ≥ 10`.  The good radii are those with
`(2/3) r^{3/2} ∈ π/4 + πℕ`, whose spacing is `~ 3π/(2√r)`; so every real window `[t, t+1]`, `t ≥ 10`, contains one.
`hankelBoot_good_circle_window` is the real-window version (the proofs are those of `good_radius_exists` and `good_circle_exists`
with `k` real); it is what lets the bootstrap radius `R` lie in the window `[b² c^{2/3}, b² c^{2/3} + 1]` of the band-reduction instance.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- Every real window `[k, k+1]`, `k ≥ 10`, contains `r` with `(2/3) r^{3/2} = π/4 + mπ`, `m ∈ ℕ`. -/
lemma hankelBoot_good_radius_real (k : ℝ) (hk : 10 ≤ k) :
    ∃ r : ℝ, k ≤ r ∧ r ≤ k + 1 ∧ ∃ m : ℕ, 2 / 3 * r ^ (3 / 2 : ℝ) = π / 4 + m * π := by
  have hk' : (10 : ℝ) ≤ k := hk
  have hkpos : (0 : ℝ) < k := by linarith
  set G : ℝ := 2 / 3 * k ^ (3 / 2 : ℝ) with hG
  have hk32 := airyRpow_three_halves_eq hkpos
  have hs3 := airyGC_three_le_sqrt hk'
  have hG20 : 20 ≤ G := by rw [hG, hk32]; nlinarith
  have hpi := Real.pi_lt_d2
  have hpipos := Real.pi_pos
  set a : ℝ := (G - π / 4) / π with ha
  have ha0 : 0 ≤ a := by rw [ha]; apply div_nonneg <;> linarith
  set m : ℕ := ⌈a⌉₊ with hm
  have hm1 : a ≤ m := Nat.le_ceil a
  have hm2 : (m : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
  have hmπ1 : G - π / 4 ≤ m * π := by
    have := mul_le_mul_of_nonneg_right hm1 hpipos.le
    rwa [ha, div_mul_cancel₀ _ hpipos.ne'] at this
  have hmπ2 : (m : ℝ) * π < G - π / 4 + π := by
    have := mul_lt_mul_of_pos_right hm2 hpipos
    rwa [add_mul, ha, div_mul_cancel₀ _ hpipos.ne', one_mul] at this
  set t : ℝ := π / 4 + m * π with ht
  have ht0 : 0 ≤ 3 / 2 * t := by positivity
  set r : ℝ := (3 / 2 * t) ^ (2 / 3 : ℝ) with hr
  have hr32 : r ^ (3 / 2 : ℝ) = 3 / 2 * t := by
    rw [hr, ← Real.rpow_mul ht0]; norm_num
  have hr0 : 0 ≤ r := Real.rpow_nonneg ht0 _
  refine ⟨r, ?_, ?_, m, ?_⟩
  · rw [← Real.rpow_le_rpow_iff hkpos.le hr0 (by norm_num : (0 : ℝ) < 3 / 2), hr32]
    rw [hG] at hmπ1
    nlinarith
  · have hsucc := airyRpow_three_halves_succ_ge hkpos
    have hs3' : π ≤ √k :=
      le_trans hpi.le (Real.le_sqrt_of_sq_le (by norm_num; linarith))
    rw [← Real.rpow_le_rpow_iff hr0 (by positivity) (by norm_num : (0 : ℝ) < 3 / 2), hr32]
    rw [hG] at hmπ2
    nlinarith
  · rw [hr32]; ring

/-! ### The sector `Re u < -|u|/2`: `u = -q²` -/

/-- **Good circles in a real window.** For real `t ≥ 10` there is `r ∈ [t, t+1]` with
`(1/(25π))(1+r)^{-1/2} e(u) ≤ ‖Ai(u)‖²` on `‖u‖ = r`. -/
theorem hankelBoot_good_circle_window (k : ℝ) (hk : 10 ≤ k) :
    ∃ r : ℝ, k ≤ r ∧ r ≤ k + 1 ∧ ∀ u : ℂ, ‖u‖ = r →
      1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ ‖airyAiC u‖ ^ 2 := by
  obtain ⟨r, hr1, hr2, m, hm⟩ := hankelBoot_good_radius_real k hk
  have hr10 : 10 ≤ r := by linarith
  have hrpos : 0 < r := by linarith
  refine ⟨r, hr1, hr2, fun u hu => ?_⟩
  have hs3 := airyGC_three_le_sqrt hr10
  have hpi := Real.pi_pos
  have hr32 : r ^ (3 / 2 : ℝ) = r * √r := airyRpow_three_halves_eq hrpos
  have henv := airyEnv_pos u
  have hsqrt_pos : 0 < √r := by linarith
  have hw := airyOnePlus_rpow_le hrpos
  -- common target: ≤ e(u)/(c π √r)
  by_cases hcase : -(‖u‖ / 2) ≤ u.re
  · -- sector |arg u| ≤ 2π/3
    have hz : 0 < ‖u‖ := by rw [hu]; exact hrpos
    have hη : 5 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * ‖u‖ ^ (3 / 2 : ℝ)) ≤ 1 / 2 := by
      rw [hu, hr32]
      have h7 : (7 / 10 : ℝ) ≤ √(1 / 2 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
      have hden : (7 / 80 : ℝ) * (r * √r) ≤ (1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * (r * √r) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 (by norm_num : (0:ℝ) ≤ (1 / 2) ^ 3))
          (by positivity : (0:ℝ) ≤ r * √r)
        nlinarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul hr10 hs3 (by norm_num) (by linarith)]
    have := airyAiC_sq_ge_sector (z := u) (s := 1 / 2) (by norm_num) hz (by nlinarith) hη
    rw [hu] at this
    refine le_trans ?_ this
    have h1 : 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) ≤ 1 / (16 * π * √r) := by
      calc 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) ≤ 1 / (25 * π) * (1 / √r) := by gcongr
        _ ≤ 1 / (16 * π * √r) := by
          rw [one_div_mul_one_div, one_div_le_one_div (by positivity) (by positivity)]
          nlinarith
    calc 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ 1 / (16 * π * √r) * airyEnv u := by gcongr
      _ = airyEnv u / (16 * π * √r) := by ring
  · -- sector near the negative axis
    have hlt : u.re < -(‖u‖ / 2) := not_le.mp hcase
    set q : ℂ := (-u) ^ (1 / 2 : ℂ) with hqdef
    have hq : NegSector q := NegSector_of_re_lt hlt
    have hq2 : q ^ 2 = -u := cpow_half_sq _
    have hqn : ‖q‖ ^ 2 = r := by rw [hqdef, norm_cpow_half_sq, norm_neg, hu]
    have hq3 : ‖q‖ ^ 3 = r ^ (3 / 2 : ℝ) := by
      rw [hqdef, airyNorm_cpow_half_pow_three, norm_neg, hu]
    have hqs : ‖q‖ = √r := by
      rw [← hqn, Real.sqrt_sq (norm_nonneg _)]
    have := airyAiC_neg_sq_ge hq m (by rw [hq3]; exact hm) (by rw [hqs]; exact hs3)
    have e : -(q ^ 2) = u := by rw [hq2, neg_neg]
    rw [e, hqs] at this
    refine le_trans ?_ this
    calc 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ 1 / (25 * π) * (1 / √r) * airyEnv u := by
          gcongr
      _ = airyEnv u / (25 * π * √r) := by field_simp

/-- info: 'FormalResearch.Special.hankelBoot_good_circle_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_good_circle_window

end FormalResearch.Special
