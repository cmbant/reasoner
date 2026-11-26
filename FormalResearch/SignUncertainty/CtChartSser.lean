module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.Basic
public import FormalResearch.SignUncertainty.CtCfuSeries

/-!
# The complex entire series `S_a(y) = ∑ y^j/(2j+a)!` (CFU chart, `ct:cfu` Step 2/3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`.  **Proved.**
Complex version of `CtCfu.Sser`: entire, agrees with `Sser` on `ℝ`, and `S_a(ȳ) = conj S_a(y)`.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.SignUncertainty.CtChart

/-- `S_a(y) = ∑ y^j/(2j+a)!` over `ℂ`. -/
noncomputable def SserC (a : ℕ) (y : ℂ) : ℂ := ∑' j : ℕ, y ^ j / (((2 * j + a).factorial : ℕ) : ℂ)

private lemma ofScalars_sum_eqC (c : ℕ → ℂ) (y : ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ c).sum y = ∑' j : ℕ, c j * y ^ j := by
  simp [FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm]

private lemma radius_topC (a : ℕ) :
    (FormalMultilinearSeries.ofScalars ℂ (fun j : ℕ => 1 / (((2 * j + a).factorial : ℕ) : ℂ))).radius = ⊤ := by
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · exact Eventually.of_forall fun n => by
      have : ((2 * n + a).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      simpa using this
  · have h : ∀ n : ℕ, ‖(1 / (((2 * (n + 1) + a).factorial : ℕ) : ℂ))‖ / ‖(1 / (((2 * n + a).factorial : ℕ) : ℂ))‖ =
        1 / (((2 * n + a + 1 : ℕ) : ℝ) * ((2 * n + a + 2 : ℕ) : ℝ)) := by
      intro n
      have e : 2 * (n + 1) + a = (2 * n + a) + 1 + 1 := by ring
      rw [e, Nat.factorial_succ, Nat.factorial_succ]
      have h1 : (0 : ℝ) < ((2 * n + a).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      rw [norm_div, norm_div, norm_one, Complex.norm_natCast, Complex.norm_natCast]
      push_cast
      field_simp
      ring
    simp only [h]
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]

lemma hasFPowerSeriesOnBall_SserC (a : ℕ) :
    HasFPowerSeriesOnBall (SserC a)
      (FormalMultilinearSeries.ofScalars ℂ (fun j : ℕ => 1 / (((2 * j + a).factorial : ℕ) : ℂ))) 0 ⊤ := by
  have h := (FormalMultilinearSeries.ofScalars ℂ (fun j : ℕ => 1 / (((2 * j + a).factorial : ℕ) : ℂ))).hasFPowerSeriesOnBall
    (by rw [radius_topC]; exact ENNReal.zero_lt_top)
  rw [radius_topC] at h
  convert h using 1
  funext y
  rw [ofScalars_sum_eqC]
  unfold SserC
  refine tsum_congr fun j => ?_
  rw [one_div, inv_mul_eq_div]

lemma analyticOnNhd_SserC (a : ℕ) : AnalyticOnNhd ℂ (SserC a) univ := fun x _ =>
  (hasFPowerSeriesOnBall_SserC a).analyticAt_of_mem (by simp)

lemma contDiff_SserC (a : ℕ) {n : WithTop ℕ∞} : ContDiff ℂ n (SserC a) :=
  contDiffOn_univ.mp ((analyticOnNhd_SserC a).contDiffOn uniqueDiffOn_univ)

lemma SserC_zero (a : ℕ) : SserC a 0 = 1 / ((a.factorial : ℕ) : ℂ) := by
  unfold SserC
  rw [tsum_eq_single 0]
  · simp
  · intro j hj
    simp [zero_pow hj]

lemma SserC_ofReal (a : ℕ) (y : ℝ) : SserC a (y : ℂ) = ((CtCfu.Sser a y : ℝ) : ℂ) := by
  unfold SserC CtCfu.Sser
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun j => ?_
  push_cast
  rfl

lemma SserC_conj (a : ℕ) (y : ℂ) : SserC a (starRingEnd ℂ y) = starRingEnd ℂ (SserC a y) := by
  unfold SserC
  rw [Complex.conj_tsum]
  refine tsum_congr fun j => ?_
  simp [map_div₀, map_pow]

/-- info: 'FormalResearch.SignUncertainty.CtChart.contDiff_SserC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_SserC

end FormalResearch.SignUncertainty.CtChart
