module

public import FormalResearch.Special.AiryCftQSampleZeros

/-!
# Airy zero count on a good circle (M5-S6a)

`hankelBoot_zero_count_le`: if `N` counts the Airy zeros `a_n` with `-a_n < R` (`n ≤ N ↔ -a_n < R`), then `N ≤ R^{3/2}`
(from `12 n² ≤ (-a_n)³`, `airyZero_cube_ge12`).  This supplies the count in the node-sum slack `(6π)² (N+1) r_∞ ≤ C_α R^{3/2} r_∞`.
-/

@[expose] public section

open FormalResearch.Special
open scoped Real

namespace FormalResearch.SignUncertainty

theorem hankelBoot_zero_count_le {R : ℝ} (hR : 0 < R) {N : ℕ}
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R)) : (N : ℝ) ≤ R ^ (3 / 2 : ℝ) := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero]
    exact (Real.rpow_pos_of_pos hR _).le
  · have h1 : -airyZero N < R := (hN N hpos).mp le_rfl
    have h2 := airyZero_cube_ge12 hpos
    have h3 : 0 ≤ -airyZero N := (neg_pos.mpr (airyZero_neg N)).le
    have h4 : (-airyZero N) ^ 3 < R ^ 3 := pow_lt_pow_left₀ h1 h3 (by norm_num)
    have hsq : ((R ^ (3 / 2 : ℝ)) ^ 2 : ℝ) = R ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]; norm_num
    by_contra hlt
    push Not at hlt
    have hp : 0 ≤ R ^ (3 / 2 : ℝ) := Real.rpow_nonneg hR.le _
    have h5 : (R ^ (3 / 2 : ℝ)) ^ 2 < (N : ℝ) ^ 2 := pow_lt_pow_left₀ hlt hp (by norm_num)
    rw [hsq] at h5
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    nlinarith

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_zero_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_zero_count_le

end FormalResearch.SignUncertainty
