module

public import FormalResearch.Special.BarnesKernel

/-!
# Elementary decay and integrability lemmas for the Barnes contour argument

* `integrable_exp_neg_mul_abs`: `x ↦ e^{-c|x|}` is integrable on `ℝ` for `c > 0`;
* `integrable_one_add_abs_mul_exp`: so is `x ↦ (1 + |x|) e^{-π|x|}`;
* `tendsto_poly_exp`: `(X+3)² e^{-πX} → 0` as `X → ∞`.
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set MeasureTheory
open scoped Real

lemma integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-c * x)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (b := 0)).mpr (exp_neg_integrableOn_Ioi 0 hc)
  have g1 : Integrable (Set.indicator (Ici (0 : ℝ)) fun x : ℝ => Real.exp (-c * x)) :=
    (integrable_indicator_iff measurableSet_Ici).mpr h1
  have g2 := g1.comp_neg
  refine (g1.add g2).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-c * |x|)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp only [Pi.add_apply, Set.indicator_apply, Set.mem_Ici]
    rcases lt_trichotomy x 0 with h | h | h
    · have h' : ¬ (0 ≤ x) := not_le.mpr h
      simp only [h', ite_false, zero_add, abs_of_neg h, neg_nonneg.mpr h.le, ite_true]
      apply le_of_eq; ring_nf
    · subst h; simp
    · have h' : ¬ (0 ≤ -x) := by linarith
      simp only [h.le, h', ite_true, ite_false, add_zero, abs_of_pos h]
      exact le_rfl

lemma integrable_one_add_abs_mul_exp :
    Integrable (fun x : ℝ => (1 + |x|) * Real.exp (-π * |x|)) := by
  have hc : 0 < π - 1 := by linarith [Real.pi_gt_three]
  refine (integrable_exp_neg_mul_abs hc).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ℝ => (1 + |x|) * Real.exp (-π * |x|)).aestronglyMeasurable
  · have h1 : 1 + |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (1 + |x|) * Real.exp (-π * |x|) ≤ Real.exp |x| * Real.exp (-π * |x|) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-(π - 1) * |x|) := by rw [← Real.exp_add]; ring_nf

/-- `(X+3)² e^{-πX} → 0`. -/
lemma tendsto_poly_exp :
    Tendsto (fun X : ℝ => (X + 3) ^ 2 * Real.exp (-π * X)) atTop (𝓝 0) := by
  have hπ : 0 < π - 1 := by linarith [Real.pi_gt_three]
  have h1 : Tendsto (fun X : ℝ => 2 * Real.exp 3 * Real.exp (-(π - 1) * X)) atTop (𝓝 0) := by
    have : Tendsto (fun X : ℝ => Real.exp (-(π - 1) * X)) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
    simpa using this.const_mul (2 * Real.exp 3)
  refine squeeze_zero' (Eventually.of_forall fun X => by positivity) ?_ h1
  filter_upwards [eventually_ge_atTop 0] with X hX
  have h2 : (X + 3) ^ 2 / (Nat.factorial 2 : ℝ) ≤ Real.exp (X + 3) :=
    Real.pow_div_factorial_le_exp _ (by linarith) 2
  have h3 : (X + 3) ^ 2 ≤ 2 * Real.exp (X + 3) := by
    have : (Nat.factorial 2 : ℝ) = 2 := by norm_num
    rw [this] at h2; linarith
  calc (X + 3) ^ 2 * Real.exp (-π * X) ≤ 2 * Real.exp (X + 3) * Real.exp (-π * X) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = 2 * Real.exp 3 * Real.exp (-(π - 1) * X) := by
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]; ring_nf

end FormalResearch.Special.Barnes
