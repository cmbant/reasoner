module

public import Mathlib

/-!
# A quadratic majorant of `-x ln x` (Hermite, double contact at `b`)

For `0 < b ≤ a` put `f = negMulLog`, `T(x) = f b + f'(b)(x - b)` and `c = (f a - T a)/(a - b)²`
(`c = 0` when `a = b`).  Then `f x ≤ T x + c (x - b)²` for every `x ∈ [0, a]`, with equality at
`x = a` and `x = b`.

Proof.  `u(y) = f y - T y + (y-b)²/(2b)` has `u' = ln(b/y) + y/b - 1 ≥ 0`, so `u ≤ 0` on `[0,b]`
and `u ≥ 0` on `[b,∞)`; hence `c ≥ -1/(2b)` and `f x ≤ T x - (x-b)²/(2b) ≤ T x + c(x-b)²` for
`x ≤ b`.  For `x ∈ (b,a]` the second divided difference `ρ(y) = (f y - T y)/(y-b)²` is increasing
on `(b,∞)`: `ρ' = N/(y-b)³` with `N = (y+b) ln(y/b) - 2(y-b)` and `N' = ln(y/b) + b/y - 1 ≥ 0`.
-/

@[expose] public section


open Real

namespace FormalResearch.NQubit.Entropy

/-- The tangent line of `negMulLog` at `b`. -/
noncomputable def negMulLogTangent (b x : ℝ) : ℝ := negMulLog b + (-log b - 1) * (x - b)

/-- `f - T`. -/
noncomputable def tangentRemainder (b x : ℝ) : ℝ := negMulLog x - negMulLogTangent b x

theorem tangentRemainder_self (b : ℝ) : tangentRemainder b b = 0 := by simp [tangentRemainder, negMulLogTangent]

theorem hasDerivAt_tangentRemainder {b y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (tangentRemainder b) (log b - log y) y := by
  have h1 := Real.hasDerivAt_negMulLog hy
  have h2 : HasDerivAt (fun x => negMulLogTangent b x) (-log b - 1) y := by
    have := (((hasDerivAt_id y).sub_const b).const_mul (-log b - 1)).const_add (negMulLog b)
    simpa [negMulLogTangent] using this
  exact (h1.sub h2).congr_deriv (by ring)

/-- `u(y) = f y - T y + (y-b)²/(2b)`. -/
noncomputable def shiftedRemainder (b y : ℝ) : ℝ := tangentRemainder b y + (y - b) ^ 2 / (2 * b)

theorem hasDerivAt_shiftedRemainder {b y : ℝ} (hb : 0 < b) (hy : y ≠ 0) :
    HasDerivAt (shiftedRemainder b) (log b - log y + (y / b - 1)) y := by
  have h3 : HasDerivAt (fun y => (y - b) ^ 2 / (2 * b)) (y / b - 1) y := by
    have := (((hasDerivAt_id y).sub_const b).pow 2).div_const (2 * b)
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  exact (hasDerivAt_tangentRemainder hy).add h3

/-- `u` is nondecreasing on `[0,∞)`. -/
theorem shiftedRemainder_monotoneOn {b : ℝ} (hb : 0 < b) : MonotoneOn (shiftedRemainder b) (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · apply Continuous.continuousOn
    unfold shiftedRemainder tangentRemainder negMulLogTangent
    fun_prop
  · intro y hy
    rw [interior_Ici] at hy
    exact (hasDerivAt_shiftedRemainder hb (ne_of_gt hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : (0 : ℝ) < y := hy
    rw [(hasDerivAt_shiftedRemainder hb hy0.ne').deriv]
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hb)
    rw [Real.log_div hy0.ne' hb.ne'] at this
    linarith

theorem tangentRemainder_le_of_le {b x : ℝ} (hb : 0 < b) (hx0 : 0 ≤ x) (hxb : x ≤ b) :
    tangentRemainder b x ≤ -((x - b) ^ 2 / (2 * b)) := by
  have h := shiftedRemainder_monotoneOn hb (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 hb.le) hxb
  have h0 : tangentRemainder b b = 0 := tangentRemainder_self b
  simp only [shiftedRemainder, h0, sub_self] at h
  simp at h
  linarith

theorem tangentRemainder_ge_of_ge {b x : ℝ} (hb : 0 < b) (hxb : b ≤ x) :
    -((x - b) ^ 2 / (2 * b)) ≤ tangentRemainder b x := by
  have h := shiftedRemainder_monotoneOn hb (Set.mem_Ici.2 hb.le) (Set.mem_Ici.2 (hb.le.trans hxb)) hxb
  have h0 : tangentRemainder b b = 0 := tangentRemainder_self b
  simp only [shiftedRemainder, h0, sub_self] at h
  simp at h
  linarith

/-- The Hermite coefficient. -/
noncomputable def secondDivDiff (a b : ℝ) : ℝ := tangentRemainder b a / (a - b) ^ 2

theorem secondDivDiff_ge {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) : -(1 / (2 * b)) ≤ secondDivDiff a b := by
  rcases hba.eq_or_lt with h | h
  · subst h
    simp only [secondDivDiff, sub_self]
    simp
    positivity
  · unfold secondDivDiff
    have h1 := tangentRemainder_ge_of_ge hb hba
    have hp : 0 < (a - b) ^ 2 := by positivity
    rw [le_div_iff₀ hp]
    have : -(1 / (2 * b)) * (a - b) ^ 2 = -((a - b) ^ 2 / (2 * b)) := by field_simp
    linarith

/-- The numerator `N(y) = (y+b) ln(y/b) - 2(y-b)`: `ρ' = N/(y-b)³`. -/
noncomputable def divDiffNumerator (b y : ℝ) : ℝ := (y + b) * (log y - log b) - 2 * (y - b)

theorem divDiffNumerator_nonneg {b y : ℝ} (hb : 0 < b) (hy : b ≤ y) : 0 ≤ divDiffNumerator b y := by
  have hmono : MonotoneOn (divDiffNumerator b) (Set.Ici b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici b)
    · apply ContinuousOn.sub
      · apply ContinuousOn.mul (by fun_prop)
        apply ContinuousOn.sub
        · exact Real.continuousOn_log.mono (fun y hy => ne_of_gt (lt_of_lt_of_le hb hy))
        · exact continuousOn_const
      · fun_prop
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : (0 : ℝ) < y := hb.trans hy
      have := (((hasDerivAt_id y).add_const b).mul (((Real.hasDerivAt_log hy0.ne').sub_const (log b)))).sub
        (((hasDerivAt_id y).sub_const b).const_mul 2)
      exact this.differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : (0 : ℝ) < y := hb.trans hy
      have hd := (((hasDerivAt_id y).add_const b).mul (((Real.hasDerivAt_log hy0.ne').sub_const (log b)))).sub
        (((hasDerivAt_id y).sub_const b).const_mul 2)
      have hd' : HasDerivAt (divDiffNumerator b) (1 * (log y - log b) + (id y + b) * y⁻¹ - 2 * 1) y := by
        unfold divDiffNumerator; exact hd
      rw [hd'.deriv]
      have := Real.one_sub_inv_le_log_of_pos (div_pos hy0 hb)
      rw [Real.log_div hy0.ne' hb.ne'] at this
      simp only [id]
      have e : (1 * (log y - log b) + (y + b) * (y⁻¹)) - 2 * (1) = (log y - log b) + b / y - 1 := by
        field_simp; ring
      have e2 : 1 - (y / b)⁻¹ = 1 - b / y := by rw [inv_div]
      rw [e2] at this
      have : (log y - log b) + b / y - 1 ≥ 0 := by
        have h3 : b / y ≤ 1 := by rw [div_le_one hy0]; exact hy.le
        have h4 := Real.log_le_sub_one_of_pos (div_pos hb hy0)
        rw [Real.log_div hb.ne' hy0.ne'] at h4
        linarith
      simp at *
      nlinarith [this]
  have h0 : divDiffNumerator b b = 0 := by simp [divDiffNumerator]
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  rw [h0] at this
  exact this

theorem secondDivDiff_monotoneOn {b : ℝ} (hb : 0 < b) :
    MonotoneOn (fun y => tangentRemainder b y / (y - b) ^ 2) (Set.Ioi b) := by
  have hd : ∀ y ∈ Set.Ioi b, HasDerivAt (fun y => tangentRemainder b y / (y - b) ^ 2)
      (((log b - log y) * (y - b) ^ 2 - tangentRemainder b y * (2 * (y - b))) / ((y - b) ^ 2) ^ 2) y := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hb.trans hy
    have hyb : y - b ≠ 0 := sub_ne_zero.2 (ne_of_gt hy)
    have h2 : HasDerivAt (fun y => (y - b) ^ 2) (2 * (y - b)) y := by
      have := ((hasDerivAt_id y).sub_const b).pow 2
      refine this.congr_deriv ?_
      simp
    exact (hasDerivAt_tangentRemainder hy0.ne').div h2 (pow_ne_zero 2 hyb)
  apply monotoneOn_of_deriv_nonneg (convex_Ioi b)
  · intro y hy
    exact (hd y hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    exact (hd y hy).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    rw [(hd y hy).deriv]
    have hy0 : (0 : ℝ) < y := hb.trans hy
    have hyb : 0 < y - b := sub_pos.2 hy
    have hN := divDiffNumerator_nonneg hb hy.le
    apply div_nonneg _ (by positivity)
    have e : (log b - log y) * (y - b) ^ 2 - tangentRemainder b y * (2 * (y - b)) = (y - b) * divDiffNumerator b y := by
      simp only [tangentRemainder, negMulLogTangent, divDiffNumerator, negMulLog]
      ring
    rw [e]
    exact mul_nonneg hyb.le hN

/-- **Hermite majorant** of `-x ln x` with double contact at `b`, valid on `[0, a]`, `0 < b ≤ a`. -/
theorem negMulLog_le_hermiteMajorant {a b x : ℝ} (hb : 0 < b) (hba : b ≤ a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    negMulLog x ≤ negMulLogTangent b x + secondDivDiff a b * (x - b) ^ 2 := by
  have key : tangentRemainder b x ≤ secondDivDiff a b * (x - b) ^ 2 := by
    rcases le_or_gt x b with hxb | hxb
    · have h1 := tangentRemainder_le_of_le hb hx0 hxb
      have h2 := secondDivDiff_ge hb hba
      have : -(1 / (2 * b)) * (x - b) ^ 2 ≤ secondDivDiff a b * (x - b) ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      have e : -(1 / (2 * b)) * (x - b) ^ 2 = -((x - b) ^ 2 / (2 * b)) := by field_simp
      linarith
    · have hmono := secondDivDiff_monotoneOn hb (Set.mem_Ioi.2 hxb) (Set.mem_Ioi.2 (hxb.trans_le hxa)) hxa
      have hp : 0 < (x - b) ^ 2 := by have := sub_pos.2 hxb; positivity
      have : tangentRemainder b x / (x - b) ^ 2 ≤ secondDivDiff a b := hmono
      rw [div_le_iff₀ hp] at this
      exact this
  unfold tangentRemainder at key
  linarith

end FormalResearch.NQubit.Entropy
