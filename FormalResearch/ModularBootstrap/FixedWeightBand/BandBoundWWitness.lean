module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BandBoundW

/-!
# Non-Vacuity of the Hypotheses of Proposition `Y_V` at Weight `w` (`vlo:YV`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J4, Proposition `Y_V` (`vlo:YV`).

The hypotheses on the test function in `proposition_YV_W` (`g ∈ TestClass prob (c'/12)`, `M[g] > 0`,
`g ≥ 0` on `[T, ∞)`) are satisfiable at every weight and every `Q`: the thermal difference
`Ξ_{1/2}(t) = e^{-π t} - 2^w e^{-4π t}` is a test function with `M[Ξ_{1/2}] > 0`, and is positive on
`[w, ∞)` (`yvHypotheses_thermalDiff`).
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing

lemma thermalDiff_half_pos {w : ℕ} {t : ℝ} (ht : (w : ℝ) ≤ t) (hw : 1 ≤ w) :
    0 < thermalDiff w (1 / 2) t := by
  unfold thermalDiff
  have h2 : ((1 : ℝ) / 2) ^ (-(w : ℝ)) = 2 ^ w := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow, inv_inv]
  rw [h2]
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hexp1 : Real.exp (-2 * Real.pi * (1 / 2) * t) = Real.exp (-(Real.pi * t)) := by
    congr 1; ring
  have hexp2 : Real.exp (-2 * Real.pi * t / (1 / 2)) = Real.exp (-(4 * Real.pi * t)) := by
    congr 1; ring
  rw [hexp1, hexp2, sub_pos]
  have h2w : (2 : ℝ) ^ w < Real.exp (3 * Real.pi * t) := by
    have : (2 : ℝ) ^ w = Real.exp (w * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [this]
    apply Real.exp_lt_exp.mpr
    have hl : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hpi := Real.pi_gt_three
    have hw0 : (0 : ℝ) < w := by linarith
    have ht0 : 0 < t := hw0.trans_le ht
    nlinarith [mul_lt_mul_of_pos_left hl hw0, mul_pos ht0 (by linarith : (0 : ℝ) < 3 * Real.pi - 1)]
  calc (2 : ℝ) ^ w * Real.exp (-(4 * Real.pi * t))
      < Real.exp (3 * Real.pi * t) * Real.exp (-(4 * Real.pi * t)) :=
        mul_lt_mul_of_pos_right h2w (Real.exp_pos _)
    _ = Real.exp (-(Real.pi * t)) := by rw [← Real.exp_add]; congr 1; ring

/-- **Non-vacuity of `proposition_YV_W`**: at every weight and every `Q`, for every
`c' ≥ max 1 (24 S)`, the thermal difference `g = Ξ_{1/2}` is a test function at level `c'/12` with
`M[g] > 0` and `g ≥ 0` on `[T, ∞)` for every `T ≥ w`. -/
theorem yvHypotheses_thermalDiff (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') :
    TestClass prob (c' / 12) (thermalDiff prob.w (1 / 2)) ∧
      0 < prob.cardyNorm (c' / 12) (thermalDiff prob.w (1 / 2)) ∧
      ∀ T : ℝ, (prob.w : ℝ) ≤ T → ∀ t ∈ Ici T, 0 ≤ thermalDiff prob.w (1 / 2) t := by
  obtain ⟨hS, -, -⟩ := shift_le_of_max_le prob hc'
  have hg := thermalDiff_mem_TestClass prob hS (by norm_num : (0 : ℝ) < 1 / 2)
  have hw := prob.hw
  have hw0 : (0 : ℝ) < prob.w := by exact_mod_cast prob.hw
  refine ⟨hg, ?_, fun T hT t ht => ?_⟩
  · unfold FixedWeightProblem.cardyNorm
    have hcont : ContinuousOn (fun t => |thermalDiff prob.w (1 / 2) t| * prob.cardyV (c' / 12) t)
        (Ioi 0) :=
      (hg.cont.mono Ioi_subset_Ici_self).abs.mul (continuous_cardyV prob (c' / 12)).continuousOn
    have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ |thermalDiff prob.w (1 / 2) t| * prob.cardyV (c' / 12) t :=
      fun t ht => mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg hS (mem_Ioi.mp ht).le)
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hnn)) hg.int_cardy]
    refine lt_of_lt_of_le ?_ (measure_mono (s := Ioi (prob.w : ℝ)) (t := Function.support
      (fun t => |thermalDiff prob.w (1 / 2) t| * prob.cardyV (c' / 12) t) ∩ Ioi 0) ?_)
    · rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
    · intro t ht
      have ht0 : 0 < t := hw0.trans ht
      refine ⟨?_, ht0⟩
      have h1 := thermalDiff_half_pos (mem_Ioi.mp ht).le hw
      have h2 := prob.cardyV_pos hS ht0
      exact (mul_pos (abs_pos.mpr h1.ne') h2).ne'
  · exact (thermalDiff_half_pos (hT.trans (mem_Ici.mp ht)) hw).le

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.yvHypotheses_thermalDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yvHypotheses_thermalDiff

end FormalResearch.ModularBootstrap.FixedWeightBand
