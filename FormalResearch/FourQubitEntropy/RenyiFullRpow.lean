import FormalResearch.FourQubitEntropy.RenyiFullTaylor

/-!
# Elementary rpow and logarithm estimates for the Rényi certificates

Paper E, `renyi_*` supplements.  Numerical rpow comparisons `b ≤ x^{m/n}` reduce to integer powers
(`le_rpow_of_pow_le`, `rpow_le_of_le_pow`); the logarithm estimates are the one-variable bounds used
for the binary entropy and head/tail estimates (`ln(1-z) ≥ -z - z²/(2(1-z))`, `ln(1+z) ≥ z - z²/2`).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Finset

/-- `b ≤ x^{m/n}` from the integer comparison `b^n ≤ x^m` (`x, b > 0`). -/
theorem le_rpow_of_pow_le {x b : ℝ} (_hb : 0 < b) (hx : 0 < x) {m n : ℕ} (hn : 0 < n)
    (h : b ^ n ≤ x ^ m) : b ≤ x ^ ((m : ℝ) / n) := by
  have hpos : 0 < x ^ ((m : ℝ) / n) := Real.rpow_pos_of_pos hx _
  have e : (x ^ ((m : ℝ) / n)) ^ n = x ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    rw [show (m : ℝ) / n * (n : ℝ) = (m : ℝ) by field_simp]
    exact Real.rpow_natCast x m
  by_contra hlt
  push Not at hlt
  have := pow_lt_pow_left₀ hlt hpos.le hn.ne'
  rw [e] at this
  linarith

/-- `x^{m/n} ≤ b` from `x^m ≤ b^n` (`x ≥ 0`, `b > 0`). -/
theorem rpow_le_of_le_pow {x b : ℝ} (hb : 0 < b) (hx : 0 ≤ x) {m n : ℕ} (hn : 0 < n)
    (h : x ^ m ≤ b ^ n) : x ^ ((m : ℝ) / n) ≤ b := by
  have hpos : 0 ≤ x ^ ((m : ℝ) / n) := Real.rpow_nonneg hx _
  have e : (x ^ ((m : ℝ) / n)) ^ n = x ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    rw [show (m : ℝ) / n * (n : ℝ) = (m : ℝ) by field_simp]
    exact Real.rpow_natCast x m
  by_contra hlt
  push Not at hlt
  have := pow_lt_pow_left₀ hlt hb.le hn.ne'
  rw [e] at this
  linarith

/-- `-ln(1-z) ≤ z + z²/(2(1-z))` for `0 ≤ z < 1`. -/
theorem neg_log_one_sub_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    -Real.log (1 - z) ≤ z + z ^ 2 / (2 * (1 - z)) := by
  set f : ℝ → ℝ := fun z => z + z ^ 2 / (2 * (1 - z)) + Real.log (1 - z) with hf
  have hder : ∀ s : ℝ, s < 1 → HasDerivAt f (s ^ 2 / (2 * (1 - s) ^ 2)) s := by
    intro s hs
    have h1s : (1 - s) ≠ 0 := by linarith
    have a1 : HasDerivAt (fun s : ℝ => s) 1 s := hasDerivAt_id s
    have a2 : HasDerivAt (fun s : ℝ => s ^ 2 / (2 * (1 - s)))
        ((2 * s * (2 * (1 - s)) - s ^ 2 * (-2)) / (2 * (1 - s)) ^ 2) s := by
      have n1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
        simpa using hasDerivAt_pow 2 s
      have n2 : HasDerivAt (fun s : ℝ => 2 * (1 - s)) (-2) s := by
        have := ((hasDerivAt_id s).const_sub 1).const_mul 2
        simpa using this
      exact n1.div n2 (mul_ne_zero two_ne_zero h1s)
    have a3 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - s)) s := by
      have := ((hasDerivAt_id s).const_sub 1).log (by simpa using h1s)
      simpa using this
    have := (a1.add a2).add a3
    convert this using 1
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1) (f' := fun s => s ^ 2 / (2 * (1 - s) ^ 2))
    · intro s hs
      exact (hder s hs.2).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      exact (hder s hs.2).hasDerivWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      have : 0 < 1 - s := by linarith [hs.2]
      positivity
  have := hmono (⟨le_rfl, by norm_num⟩ : (0 : ℝ) ∈ Set.Ico 0 1) (⟨hz0, hz1⟩ : z ∈ Set.Ico 0 1) hz0
  simp [hf] at this
  linarith

/-- `ln(1+z) ≥ z - z²/2` for `0 ≤ z ≤ 1`. -/
theorem log_ge_taylor2 {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    z - z ^ 2 / 2 ≤ Real.log (1 + z) := by
  have := log_ge_taylor4 hz
  nlinarith [mul_nonneg (pow_nonneg hz 3) (sub_nonneg.2 hz1)]

end FormalResearch.FourQubitEntropy.RenyiFull
