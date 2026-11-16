module

public import FormalResearch.Special.AiryClarkMid
public import FormalResearch.Special.AiryCftMittagLeffler

/-!
# The largest zero `a'_1` of `Ai'` and the seed lemma `S_1 = |a'_1|`

Formalises the seed lemma of CFT/PR240 `FOLD_TIP_THEOREM.md` ("`|a'_1| = S_1 = Σ_n (a_n - a'_1)^{-2}`", `a'_1 = -1.0187929716`):

* `airyDeriv_largest_zero`: **the first zero of `Ai'`**: there is `x ∈ (a_1, 0)` with `Ai'(x) = 0` and every real zero `y` of `Ai'` has
  `y ≤ x` (so `x = a'_1` is the largest zero; with `AiryClarkMid.airyAi'_existsUnique_zero_gap` these are all the real
  zeros `a'_n ∈ (a_{n+1}, a_n)`, `n ≥ 1`, and `a'_1 ∈ (a_1, 0)`).  Proof: the Prüfer angle `θ` of `(Ai, Ai')`
  (`airy_exists_prufer`, `θ 0 ∈ (π/2, π)`, increasing on `(-∞, 0]`): the zeros of `Ai'` are the levels `θ ∈ π/2 + πℤ`
  (`combo_eq_zero_iff`); the level `π/2` is attained exactly once on `(-∞, 0]` (`airy_node_exists_unique`), between the levels `0`
  (`a_1`) and `π` (not reached since `θ 0 < π`); on `x ≥ 0`, `Ai' < 0` (`airyAi'_neg`).
* `airy_S1_eq_abs_firstDerivZero`: `Σ_{n ≥ 1} (a_n - a'_1)^{-2} = -a'_1 = |a'_1|` (HasSum), from the sum rule
  `airyZero_sum_sq_of_deriv_zero` (`AiryCftMittagLeffler`; `(log Ai)'' = -Σ(x - a_n)^{-2}` and `Ai'(a'_1) = 0`).

Numerics (mpmath, 30 digits; evidence only): `a'_1 = -1.01879297164747…`; `Σ_{n ≤ 3000} (a_n - a'_1)^{-2} = 0.9924345797`, the tail
(DLMF 9.9.6 zeros up to `n = 2·10⁷` plus an integral remainder) `0.0263583…`, total `1.01879297 (±10⁻⁸)` `= |a'_1|`.  Everything here is proved (no numerical input).  Not formalised: the enclosure
`a'_1 ∈ (-1.0188, -1.0187)` (would need Taylor enclosures of `Ai'`), and the zeros of `Ai'` in `ℂ` (all real and negative: not needed).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

open SturmAiry

/-- **The largest zero of `Ai'`**: `a'_1 ∈ (a_1, 0)`, `Ai'(a'_1) = 0`, and every real zero of `Ai'` is `≤ a'_1`. -/
theorem airyDeriv_largest_zero :
    ∃ x : ℝ, airyZero 1 < x ∧ x < 0 ∧ airyAi' x = 0 ∧ ∀ y : ℝ, airyAi' y = 0 → y ≤ x := by
  obtain ⟨θ, hθ, hlo, hhi, hmono⟩ := airy_exists_prufer
  have hpi := Real.pi_pos
  have h0 : 0 < θ 0 := by linarith
  obtain ⟨x, ⟨hx0, hxθ, hxc⟩, huniq⟩ := airy_node_exists_unique hθ (α := π / 2) (m := 0)
    (by simp; linarith)
  have hxd : airyAi' x = 0 := by
    simp only [combo, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_sub, neg_eq_zero] at hxc
    exact hxc
  simp only [Int.cast_zero, zero_mul, add_zero] at hxθ
  have hAx : airyAi x ≠ 0 := airyAi_ne_zero_of_deriv_zero hxd
  -- every zero of Ai' is ≤ x
  have hlargest : ∀ y : ℝ, airyAi' y = 0 → y ≤ x := by
    intro y hy
    by_contra hyx
    have hxy : x < y := not_le.mp hyx
    by_cases hy0 : 0 ≤ y
    · have := airyAi'_neg hy0
      linarith
    · have hy0' : y ≤ 0 := (not_le.mp hy0).le
      have hcombo : combo (π / 2) airyAi airyAi' y = 0 := by simp [combo, hy]
      obtain ⟨m, hm⟩ := (hθ.combo_eq_zero_iff (π / 2) y).1 hcombo
      have hθy : θ y < θ 0 := hmono hy0' (le_refl _) (not_le.mp hy0)
      have hθxy : θ x < θ y := hmono hx0 hy0' hxy
      rw [hxθ] at hθxy
      -- π/2 < π/2 + mπ < π  forces no integer
      have h1 : (0 : ℝ) < m := by
        by_contra hc
        push Not at hc
        nlinarith
      have h2 : (m : ℝ) < 1 := by
        by_contra hc
        push Not at hc
        nlinarith
      have : (0 : ℤ) < m := by exact_mod_cast h1
      have : m < 1 := by exact_mod_cast h2
      omega
  refine ⟨x, ?_, lt_of_le_of_ne hx0 ?_, hxd, hlargest⟩
  · -- a_1 < x
    have hθa := airy_prufer_airyZero hθ h0 hhi (n := 1) le_rfl
    have hne : airyZero 1 ≠ x := fun h => hAx (by rw [← h, airyAi_airyZero])
    rcases lt_trichotomy (airyZero 1) x with h | h | h
    · exact h
    · exact absurd h hne
    · exfalso
      have := hmono hx0 (airyZero_nonpos 1) h
      rw [hθa, hxθ] at this
      simp at this
      linarith
  · intro h
    rw [h] at hxd
    have := airyAi'_neg (le_refl (0 : ℝ))
    linarith

/-- **Seed lemma `S_1 = |a'_1|`** (`FOLD_TIP_THEOREM.md`): at the largest zero `a'_1` of `Ai'`,
`Σ_{n ≥ 1} (a_n - a'_1)^{-2} = -a'_1 = |a'_1|`. -/
theorem airy_S1_eq_abs_firstDerivZero :
    ∃ x : ℝ, airyZero 1 < x ∧ x < 0 ∧ airyAi' x = 0 ∧ (∀ y : ℝ, airyAi' y = 0 → y ≤ x) ∧
      HasSum (fun n : ℕ => ((airyZero (n + 1) - x) ^ 2)⁻¹) |x| := by
  obtain ⟨x, h1, h2, h3, h4⟩ := airyDeriv_largest_zero
  refine ⟨x, h1, h2, h3, h4, ?_⟩
  have := airyZero_sum_sq_of_deriv_zero h3
  rw [abs_of_neg h2]
  convert this using 2 with n
  rw [← neg_sub, neg_sq]

/-- info: 'FormalResearch.Special.airyDeriv_largest_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyDeriv_largest_zero

/-- info: 'FormalResearch.Special.airy_S1_eq_abs_firstDerivZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_S1_eq_abs_firstDerivZero

end FormalResearch.Special
