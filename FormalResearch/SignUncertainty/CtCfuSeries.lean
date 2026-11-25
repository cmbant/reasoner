module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The entire series `S_a(y) = ∑ y^j/(2j+a)!` (support for `ct:cfu`)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2.  **Proved.**

`S_1(w²) w = sinh w`, `S_3(w²) w³ = sinh w - w`.  Each `S_a` is `C^∞` on `ℝ`, `S_a(y) = 1/a! + y S_{a+2}(y)`, so `S_a(0) = 1/a!`,
`S_a'(0) = 1/(a+2)!`.  These replace the (even) functions `sinh w/w`, `(sinh w - w)/w³` by smooth functions of `y = w²`.
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtCfu

/-- `S_a(y) = ∑ y^j/(2j+a)!`. -/
noncomputable def Sser (a : ℕ) (y : ℝ) : ℝ := ∑' j : ℕ, y ^ j / ((2 * j + a).factorial : ℝ)

private lemma ofScalars_sum_eq (c : ℕ → ℝ) (y : ℝ) :
    (FormalMultilinearSeries.ofScalars ℝ c).sum y = ∑' j : ℕ, c j * y ^ j := by
  simp [FormalMultilinearSeries.sum, mul_comm]

private lemma radius_top (a : ℕ) :
    (FormalMultilinearSeries.ofScalars ℝ (fun j : ℕ => 1 / ((2 * j + a).factorial : ℝ))).radius = ⊤ := by
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · exact Eventually.of_forall fun n => by positivity
  · have h : ∀ n : ℕ, ‖(1 / ((2 * (n + 1) + a).factorial : ℝ))‖ / ‖(1 / ((2 * n + a).factorial : ℝ))‖ =
        1 / (((2 * n + a + 1 : ℕ) : ℝ) * ((2 * n + a + 2 : ℕ) : ℝ)) := by
      intro n
      have e : 2 * (n + 1) + a = (2 * n + a) + 1 + 1 := by ring
      rw [e, Nat.factorial_succ, Nat.factorial_succ]
      have h1 : (0 : ℝ) < ((2 * n + a).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity)]
      push_cast
      field_simp
      ring
    simp only [h]
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]

lemma hasFPowerSeriesOnBall_Sser (a : ℕ) :
    HasFPowerSeriesOnBall (Sser a) (FormalMultilinearSeries.ofScalars ℝ (fun j : ℕ => 1 / ((2 * j + a).factorial : ℝ)))
      0 ⊤ := by
  have h := (FormalMultilinearSeries.ofScalars ℝ (fun j : ℕ => 1 / ((2 * j + a).factorial : ℝ))).hasFPowerSeriesOnBall
    (by rw [radius_top]; exact ENNReal.zero_lt_top)
  rw [radius_top] at h
  convert h using 1
  funext y
  rw [ofScalars_sum_eq]
  unfold Sser
  refine tsum_congr fun j => ?_
  rw [one_div, inv_mul_eq_div]

lemma analyticOnNhd_Sser (a : ℕ) : AnalyticOnNhd ℝ (Sser a) univ := fun x _ =>
  (hasFPowerSeriesOnBall_Sser a).analyticAt_of_mem (by simp)

lemma contDiff_Sser (a : ℕ) : ContDiff ℝ ⊤ (Sser a) :=
  contDiffOn_univ.mp ((analyticOnNhd_Sser a).contDiffOn uniqueDiffOn_univ)

lemma hasSum_Sser (a : ℕ) (y : ℝ) :
    HasSum (fun j : ℕ => y ^ j / ((2 * j + a).factorial : ℝ)) (Sser a y) := by
  have h := (hasFPowerSeriesOnBall_Sser a).hasSum (y := y) (by simp)
  simp only [zero_add] at h
  convert h using 2 with j
  simp [mul_comm, div_eq_mul_inv]

lemma Sser_zero (a : ℕ) : Sser a 0 = 1 / (a.factorial : ℝ) := by
  unfold Sser
  rw [tsum_eq_single 0]
  · simp
  · intro j hj
    simp [zero_pow hj]

/-- `S_a(y) = 1/a! + y S_{a+2}(y)`. -/
lemma Sser_succ (a : ℕ) (y : ℝ) : Sser a y = 1 / (a.factorial : ℝ) + y * Sser (a + 2) y := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_Sser a y)
  have h2 := (hasSum_Sser (a + 2) y).mul_left y
  have e : (fun n : ℕ => y ^ (n + 1) / ((2 * (n + 1) + a).factorial : ℝ)) =
      fun n : ℕ => y * (y ^ n / ((2 * n + (a + 2)).factorial : ℝ)) := by
    funext n
    rw [pow_succ, show 2 * (n + 1) + a = 2 * n + (a + 2) by ring]
    ring
  rw [e] at h
  have := h.unique h2
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_zero, zero_add] at this
  have e1 : (1 : ℝ) / (a.factorial : ℝ) = 1 / (a.factorial : ℝ) := rfl
  simp only [one_div] at this ⊢
  linarith

lemma hasDerivAt_Sser_zero (a : ℕ) : HasDerivAt (Sser a) (1 / ((a + 2).factorial : ℝ)) 0 := by
  have hg : HasDerivAt (Sser (a + 2)) (deriv (Sser (a + 2)) 0) 0 :=
    (((contDiff_Sser (a + 2)).differentiable (by simp)) 0).hasDerivAt
  have h0 : HasDerivAt (fun y : ℝ => y * Sser (a + 2) y) (1 * Sser (a + 2) 0 + 0 * deriv (Sser (a + 2)) 0) 0 :=
    (hasDerivAt_id' (0 : ℝ)).mul hg
  have h : HasDerivAt (fun y : ℝ => 1 / (a.factorial : ℝ) + y * Sser (a + 2) y)
      (1 * Sser (a + 2) 0 + 0 * deriv (Sser (a + 2)) 0) 0 := h0.const_add _
  have e : Sser a = fun y => 1 / (a.factorial : ℝ) + y * Sser (a + 2) y := funext (Sser_succ a)
  rw [e]
  refine h.congr_deriv ?_
  simp [Sser_zero]

lemma Sser1_sq (w : ℝ) : Sser 1 (w ^ 2) * w = Real.sinh w := by
  have h := (hasSum_Sser 1 (w ^ 2)).mul_right w
  have h2 := Real.hasSum_sinh w
  have e : (fun j : ℕ => (w ^ 2) ^ j / ((2 * j + 1).factorial : ℝ) * w) =
      fun n : ℕ => w ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
    funext j; rw [← pow_mul, pow_succ]; ring
  rw [e] at h
  exact h.unique h2

lemma Sser3_sq (w : ℝ) : Sser 3 (w ^ 2) * w ^ 3 = Real.sinh w - w := by
  have h := (hasSum_Sser 3 (w ^ 2)).mul_right (w ^ 3)
  have h2 := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_sinh w)
  have e : (fun j : ℕ => (w ^ 2) ^ j / ((2 * j + 3).factorial : ℝ) * w ^ 3) =
      fun n : ℕ => w ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1).factorial : ℝ) := by
    funext j
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
    ring
  rw [e] at h
  have := h.unique h2
  simpa using this

private lemma fact_ge (j : ℕ) : 6 * 9 ^ j ≤ (2 * j + 3).factorial := by
  induction j with
  | zero => norm_num [Nat.factorial]
  | succ j ih =>
    have e : 2 * (j + 1) + 3 = (2 * j + 3) + 1 + 1 := by ring
    rw [e, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
    have : 9 ≤ (2 * j + 3 + 1 + 1) * (2 * j + 3 + 1) := by nlinarith
    calc 6 * (9 ^ j * 9) = (6 * 9 ^ j) * 9 := by ring
      _ ≤ (2 * j + 3).factorial * ((2 * j + 3 + 1 + 1) * (2 * j + 3 + 1)) := Nat.mul_le_mul ih this
      _ = _ := by ring

lemma abs_Sser3_le {y : ℝ} (hy : |y| ≤ 1) : |Sser 3 y| ≤ 3 / 16 := by
  have hg : HasSum (fun j : ℕ => (1 / 6 : ℝ) * (1 / 9) ^ j) (3 / 16) := by
    have := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 9) (by norm_num)).mul_left (1 / 6 : ℝ)
    convert this using 1; norm_num
  have := (hasSum_Sser 3 y).norm_le_of_bounded hg (fun j => ?_)
  · simpa using this
  · rw [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    have h1 : (6 * 9 ^ j : ℝ) ≤ ((2 * j + 3).factorial : ℝ) := by exact_mod_cast fact_ge j
    have h2 : |y| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
    have h3 : (0 : ℝ) < ((2 * j + 3).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_le_iff₀ h3]
    calc |y| ^ j ≤ 1 := h2
      _ ≤ (1 / 6) * (1 / 9) ^ j * (6 * 9 ^ j) := by
          rw [one_div, one_div, inv_pow]; field_simp; exact le_rfl
      _ ≤ (1 / 6) * (1 / 9) ^ j * ((2 * j + 3).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)

lemma Sser1_ge {y : ℝ} (hy : |y| ≤ 1) : 4 / 5 ≤ Sser 1 y := by
  have h := Sser_succ 1 y
  have h3 := abs_Sser3_le hy
  have : |y * Sser 3 y| ≤ 3 / 16 := by
    rw [abs_mul]
    calc |y| * |Sser 3 y| ≤ 1 * (3 / 16) := mul_le_mul hy h3 (abs_nonneg _) zero_le_one
      _ = 3 / 16 := one_mul _
  have := (abs_le.mp this).1
  norm_num [Nat.factorial] at h
  linarith

/-- info: 'FormalResearch.SignUncertainty.CtCfu.contDiff_Sser' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_Sser

/-- info: 'FormalResearch.SignUncertainty.CtCfu.Sser1_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sser1_sq

/-- info: 'FormalResearch.SignUncertainty.CtCfu.Sser3_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sser3_sq

/-- info: 'FormalResearch.SignUncertainty.CtCfu.abs_Sser3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_Sser3_le

end FormalResearch.SignUncertainty.CtCfu
