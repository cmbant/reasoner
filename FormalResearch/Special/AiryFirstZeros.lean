module

public import FormalResearch.Special.AiryZeroTaylor
public import FormalResearch.Special.AiryZeroGap
public import FormalResearch.Special.AiryAsymZeros

/-!
# The zeros of `Ai` in `[-4.84, 0]`: `a_1 ∈ (-2.35, -2.33)`, `a_2 ∈ (-4.84, -4)`, and no others

Exact finite count (the finite numerical input to the labelling of the ordered zeros, `AiryZeroLabel`):

* `airyAi_neg_233_pos`, `airyAi_neg_235_neg` (`AiryZeroTaylor`): the sign change at `a_1 = -2.3381074…`, from the
  Taylor evaluation and the Gamma enclosures of `Ai(0), Ai'(0)`;
* `airyAi_neg_four_neg`, `airyAi_neg_484_pos`: `Ai(-4) < 0 < Ai(-4.84)` from the explicit asymptotic
  `airyAi_neg_sq_asymptotic` at `r = 2` and `r = 2.2` (error terms `≤ 0.0111`, `≤ 0.01`, main terms
  `≤ -0.0637`, `≥ 0.37`); hence a zero in `(-4.84, -4)` (`a_2 = -4.0879494…`);
* `airyAi_pos_of_neg_233_le`: `Ai > 0` on `[-2.33, 0]`: the Prüfer angle satisfies `θ(-2.33) ≥ θ(0) - 1 - 1.33·2.33 > -π`
  (`airy_prufer_rate`, `θ(0) > π/2`) and `sin θ(-2.33) > 0`, so `θ(-2.33) ∈ (0, π)`, and `θ` increases to
  `θ(0) < π`;
* `airy_zeros_Icc`: **the zero set of `Ai` in `[-4.84, 0]` is exactly `{a, w}` with `a ∈ (-2.35, -2.33)` and
  `w ∈ (-4.84, -4)`**: by `airy_zero_gap` (`Y = 4.84`) two distinct zeros in `[-4.84, 0]` are `≥ π/2.2 > 1.42` apart, which
  excludes a third zero.

Numerically checked (mpmath, 30 digits): `Ai(-2.33) = 0.0056849`, `Ai(-2.35) = -0.0083388`,
`Ai(-4) = -0.0702…`, `Ai(-4.84) = 0.3667…`, zeros `-2.3381074105, -4.0879494441, -5.5205598281`.
Everything is proved (no numerical evidence enters).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special

open SturmAiry

lemma airyFZ_pi_bounds : 3.1415 < π ∧ π < 3.1416 := ⟨Real.pi_gt_d4, Real.pi_lt_d4⟩

/-- `Ai(-4) < 0`. -/
theorem airyAi_neg_four_neg : airyAi (-4) < 0 := by
  have h := airyAi_neg_sq_asymptotic (r := 2) (by norm_num)
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  have hc : Real.cos (2 / 3 * (2 : ℝ) ^ 3 - π / 4) ≤ -0.16 := by
    have e : Real.cos (2 / 3 * (2 : ℝ) ^ 3 - π / 4) = -Real.sin (7 * π / 4 - 16 / 3) := by
      rw [show 2 / 3 * (2 : ℝ) ^ 3 - π / 4 = (π / 2 - (7 * π / 4 - 16 / 3)) + π by ring,
        Real.cos_add_pi, Real.cos_pi_div_two_sub]
    have hv : 0.1642 < 7 * π / 4 - 16 / 3 := by linarith
    have hv2 : 7 * π / 4 - 16 / 3 < 0.1645 := by linarith
    have := Real.sin_gt_sub_cube (by linarith : 0 < 7 * π / 4 - 16 / 3)
    set v := 7 * π / 4 - 16 / 3
    rw [e]
    nlinarith [sq_nonneg v, mul_pos (by linarith : 0 < v) (by linarith : 0 < v)]
  have hs2 : (1.41 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2' : √2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hspi : √π < 1.7725 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  have hspi0 : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hm : √π * √2 ≤ 2.51 := by nlinarith
  have hm0 : 0 < √π * √2 := by positivity
  have hq : Real.cos (2 / 3 * (2 : ℝ) ^ 3 - π / 4) / (√π * √2) ≤ -0.0637 := by
    rw [div_le_iff₀ hm0]; nlinarith
  have he : 1 / (8 * (√2 * (2 : ℝ) ^ 3)) ≤ 0.0111 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h' := (abs_le.mp h).2
  have e4 : -((2 : ℝ) ^ 2) = -4 := by norm_num
  rw [e4] at h'
  linarith

/-- `Ai(-4.84) > 0`. -/
theorem airyAi_neg_484_pos : 0 < airyAi (-4.84) := by
  have h := airyAi_neg_sq_asymptotic (r := 2.2) (by norm_num)
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  have hc : 0.999 ≤ Real.cos (2 / 3 * (2.2 : ℝ) ^ 3 - π / 4) := by
    have e : Real.cos (2 / 3 * (2.2 : ℝ) ^ 3 - π / 4) = Real.cos (2 / 3 * (2.2 : ℝ) ^ 3 - 9 * π / 4) := by
      rw [show 2 / 3 * (2.2 : ℝ) ^ 3 - π / 4 = (2 / 3 * (2.2 : ℝ) ^ 3 - 9 * π / 4) + 2 * π by ring,
        Real.cos_add_two_pi]
    rw [e]
    have := Real.one_sub_sq_div_two_le_cos (x := 2 / 3 * (2.2 : ℝ) ^ 3 - 9 * π / 4)
    have hu1 : 2 / 3 * (2.2 : ℝ) ^ 3 - 9 * π / 4 < 0.04 := by norm_num; linarith
    have hu2 : -0.04 < 2 / 3 * (2.2 : ℝ) ^ 3 - 9 * π / 4 := by norm_num; linarith
    set u := 2 / 3 * (2.2 : ℝ) ^ 3 - 9 * π / 4
    nlinarith
  have hs2 : (1.48 : ℝ) < √2.2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2' : √(2.2 : ℝ) < 1.49 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hspi : √π < 1.7725 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  have hspi0 : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hm : √π * √(2.2 : ℝ) ≤ 2.65 := by nlinarith
  have hm0 : 0 < √π * √(2.2 : ℝ) := by positivity
  have hq : 0.37 ≤ Real.cos (2 / 3 * (2.2 : ℝ) ^ 3 - π / 4) / (√π * √(2.2 : ℝ)) := by
    rw [le_div_iff₀ hm0]; nlinarith
  have he : 1 / (8 * (√(2.2 : ℝ) * (2.2 : ℝ) ^ 3)) ≤ 0.01 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h' := (abs_le.mp h).1
  have e4 : -((2.2 : ℝ) ^ 2) = -4.84 := by norm_num
  rw [e4] at h'
  linarith

/-- **`Ai > 0` on `[-2.33, 0]`.** -/
theorem airyAi_pos_of_neg_233_le {x : ℝ} (h1 : -2.33 ≤ x) (h2 : x ≤ 0) : 0 < airyAi x := by
  obtain ⟨θ, hθ, hlo, hhi, hmono⟩ := airy_exists_prufer
  have hpi := Real.pi_gt_three
  have r1 := airy_prufer_rate hθ (M := 1) (a := -1) (b := 0) le_rfl (by norm_num) (by norm_num)
  have r2 := airy_prufer_rate hθ (M := 2.33) (a := -2.33) (b := -1) (by norm_num) le_rfl (by norm_num)
  have hθ233 : -Real.pi < θ (-2.33) := by norm_num at r1 r2; linarith
  obtain ⟨r, hr, hy, -⟩ := hθ.exists_r
  have hsin : 0 < Real.sin (θ (-2.33)) := by
    have := airyAi_neg_233_pos
    rw [hy] at this
    exact (mul_pos_iff_of_pos_left (hr _)).mp this
  have hθpos : 0 < θ (-2.33) := by
    by_contra hneg
    push Not at hneg
    have := Real.sin_nonpos_of_nonpos_of_neg_pi_le hneg hθ233.le
    linarith
  have hmon : θ (-2.33) ≤ θ x := hmono.monotoneOn (by simp; norm_num) (by simpa using h2) h1
  have hle : θ x ≤ θ 0 := hmono.monotoneOn (by simpa using h2) (by simp) h2
  rw [hy x]
  exact mul_pos (hr x) (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

/-- **The first zero**: `Ai` has a zero in `(-2.35, -2.33)` (`a_1 = -2.3381074…`). -/
theorem airy_exists_zero_first : ∃ a : ℝ, -2.35 < a ∧ a < -2.33 ∧ airyAi a = 0 := by
  have hc : ContinuousOn airyAi (Icc (-2.35 : ℝ) (-2.33)) := isSol_airyAi.continuous.continuousOn
  obtain ⟨a, ha, ha0⟩ := intermediate_value_Icc (by norm_num) hc
    (show (0 : ℝ) ∈ Icc (airyAi (-2.35)) (airyAi (-2.33)) from
      ⟨airyAi_neg_235_neg.le, airyAi_neg_233_pos.le⟩)
  refine ⟨a, lt_of_le_of_ne ha.1 ?_, lt_of_le_of_ne ha.2 ?_, ha0⟩
  · rintro rfl; linarith [airyAi_neg_235_neg]
  · rintro rfl; linarith [airyAi_neg_233_pos]

/-- **The second zero**: `Ai` has a zero in `(-4.84, -4)` (`a_2 = -4.0879494…`). -/
theorem airy_exists_zero_second : ∃ w : ℝ, -4.84 < w ∧ w < -4 ∧ airyAi w = 0 := by
  have hc : ContinuousOn airyAi (Icc (-4.84 : ℝ) (-4)) := isSol_airyAi.continuous.continuousOn
  obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' (by norm_num) hc
    (show (0 : ℝ) ∈ Icc (airyAi (-4)) (airyAi (-4.84)) from
      ⟨airyAi_neg_four_neg.le, airyAi_neg_484_pos.le⟩)
  refine ⟨w, lt_of_le_of_ne hw.1 ?_, lt_of_le_of_ne hw.2 ?_, hw0⟩
  · rintro rfl; linarith [airyAi_neg_484_pos]
  · rintro rfl; linarith [airyAi_neg_four_neg]

/-- **The zeros of `Ai` in `[-4.84, 0]`** are exactly two: `a ∈ (-2.35, -2.33)` and `w ∈ (-4.84, -4)`. -/
theorem airy_zeros_Icc :
    ∃ a w : ℝ, -2.35 < a ∧ a < -2.33 ∧ -4.84 < w ∧ w < -4 ∧ airyAi a = 0 ∧ airyAi w = 0 ∧
      ∀ z : ℝ, -4.84 ≤ z → z ≤ 0 → airyAi z = 0 → z = a ∨ z = w := by
  obtain ⟨a, ha1, ha2, ha0⟩ := airy_exists_zero_first
  obtain ⟨w, hw1, hw2, hw0⟩ := airy_exists_zero_second
  refine ⟨a, w, ha1, ha2, hw1, hw2, ha0, hw0, fun z hz1 hz2 hz0 => ?_⟩
  by_contra hne
  push Not at hne
  have hY : (0 : ℝ) < 4.84 := by norm_num
  have hsq : √(4.84 : ℝ) = 2.2 := by
    rw [show (4.84 : ℝ) = 2.2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hg : (1.427 : ℝ) ≤ π / √4.84 := by
    rw [hsq, le_div_iff₀ (by norm_num)]; linarith [Real.pi_gt_d4]
  -- z versus a
  have hza : z < a := by
    rcases lt_or_gt_of_ne hne.1 with h | h
    · exact h
    · exfalso
      have := airy_zero_gap hY (x := a) (x' := z) (by linarith) h hz2 ha0 hz0
      have hz' : -2.33 ≤ z := by linarith
      exact (airyAi_pos_of_neg_233_le hz' hz2).ne' hz0
  have hza' : z ≤ -3.75 := by
    have := airy_zero_gap hY (x := z) (x' := a) hz1 hza (by linarith) hz0 ha0
    linarith
  rcases lt_or_gt_of_ne hne.2 with h | h
  · have := airy_zero_gap hY (x := z) (x' := w) hz1 h (by linarith) hz0 hw0
    linarith
  · have := airy_zero_gap hY (x := w) (x' := z) (by linarith) h hz2 hw0 hz0
    linarith

/-- info: 'FormalResearch.Special.airy_zeros_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_zeros_Icc

end FormalResearch.Special
