module

public import FormalResearch.Complex.HardyWeightedArc

/-!
# Pointwise bound at a point near the real axis from the weighted arcs

Generic complex analysis, no Airy content.  **Proved.**  Companion of `HardyWeightedArc.hardy_sample_real` (the value at a *real* point)
for an arbitrary point `w` in the disc `|w - c| < r` about a real centre `c`: with `G` entire, the Hardy hypotheses (`‖G z‖ ≤ C(1+‖z‖)^m`
on `Im z ≥ 0`, `G|_ℝ ∈ L¹`) and the reflection `‖G z‖ ≤ E ‖G(-z)‖` on the lower half of the circle `|z - c| = r`,

`‖G(w)‖ ≤ (r/(r - |w - c|)) · (r/π) · (∫ ‖G(t)‖/((t-c)²+r²) dt + E ∫ ‖G(t)‖/((t+c)²+r²) dt)`    (`hardy_point_real`),

and, bounding the kernels by `1/r²`, `‖G(w)‖ ≤ (1 + E) ‖g‖₁ / (π (r - |w - c|))` (`hardy_point_real_le`).  Proof: Cauchy's formula on `|z - c| = r`
(`circleAverage_smul_div`, kernel `|z-c|/|z-w| ≤ r/(r - |w-c|)`), the lower semicircle reflected onto the upper semicircle about `-c`, and the weighted
Fejér–Riesz arc bound at the two real centres `±c` (`hardy_arc_weighted`).
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace FormalResearch.Hardy

/-- **Pointwise bound at `w` with `|w - c| < r` from the weighted arcs.** -/
theorem hardy_point_real {G : ℂ → ℂ} (hG : Differentiable ℂ G) {C : ℝ} {m : ℕ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ C * (1 + ‖z‖) ^ m) (hint : Integrable (fun x : ℝ => G (x : ℂ)))
    (c : ℝ) {r : ℝ} (hr : 0 < r) {E : ℝ} (hE : 0 ≤ E)
    (hrefl : ∀ w : ℂ, ‖w - (c : ℂ)‖ = r → w.im ≤ 0 → ‖G w‖ ≤ E * ‖G (-w)‖) {w : ℂ} (hw : ‖w - (c : ℂ)‖ < r) :
    ‖G w‖ ≤ (r / (r - ‖w - (c : ℂ)‖)) * ((r / π) * ((∫ t : ℝ, ‖G (t : ℂ)‖ / ((t - c) ^ 2 + r ^ 2)) +
      E * ∫ t : ℝ, ‖G (t : ℂ)‖ / ((t + c) ^ 2 + r ^ 2))) := by
  have hpi := Real.pi_pos
  have hgap : 0 < r - ‖w - (c : ℂ)‖ := by linarith
  have hwb : w ∈ Metric.ball (c : ℂ) |r| := by
    rw [mem_ball_iff_norm, abs_of_pos hr]; exact hw
  have hmv := (hG.diffContOnCl (s := Metric.ball (c : ℂ) |r|)).circleAverage_smul_div hwb
  have hcont : Continuous (fun θ : ℝ => ‖G (circleMap (c : ℂ) r θ)‖) :=
    (hG.continuous.comp (continuous_circleMap _ _)).norm
  set F : ℝ → ℝ := fun θ => ‖G (circleMap (c : ℂ) r θ)‖ with hF
  have hbound : ∀ θ : ℝ, ‖(((circleMap (c : ℂ) r θ) - (c : ℂ)) / (circleMap (c : ℂ) r θ - w)) • G (circleMap (c : ℂ) r θ)‖ ≤
      (r / (r - ‖w - (c : ℂ)‖)) * F θ := by
    intro θ
    rw [norm_smul, norm_div]
    have h1 : ‖circleMap (c : ℂ) r θ - (c : ℂ)‖ = r := by
      rw [circleMap_sub_center]; simp [abs_of_pos hr]
    have h2 : r - ‖w - (c : ℂ)‖ ≤ ‖circleMap (c : ℂ) r θ - w‖ := by
      have : ‖circleMap (c : ℂ) r θ - (c : ℂ)‖ - ‖w - (c : ℂ)‖ ≤ ‖(circleMap (c : ℂ) r θ - (c : ℂ)) - (w - (c : ℂ))‖ :=
        norm_sub_norm_le _ _
      rw [h1] at this
      have e : (circleMap (c : ℂ) r θ - (c : ℂ)) - (w - (c : ℂ)) = circleMap (c : ℂ) r θ - w := by ring
      rw [e] at this; exact this
    rw [h1]
    have : r / ‖circleMap (c : ℂ) r θ - w‖ ≤ r / (r - ‖w - (c : ℂ)‖) :=
      div_le_div_of_nonneg_left hr.le hgap h2
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hq : 0 ≤ r / (r - ‖w - (c : ℂ)‖) := by positivity
  have hint1 : ‖(∫ θ in (0 : ℝ)..2 * π, (((circleMap (c : ℂ) r θ) - (c : ℂ)) / (circleMap (c : ℂ) r θ - w)) •
        G (circleMap (c : ℂ) r θ))‖ ≤ ∫ θ in (0 : ℝ)..2 * π, (r / (r - ‖w - (c : ℂ)‖)) * F θ := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans ?_
    refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ (fun θ _ => hbound θ)
    · refine ContinuousOn.intervalIntegrable ?_
      refine (Continuous.continuousOn ?_)
      have hne : ∀ θ : ℝ, circleMap (c : ℂ) r θ - w ≠ 0 := by
        intro θ h0
        have h1 : ‖circleMap (c : ℂ) r θ - (c : ℂ)‖ = r := by
          rw [circleMap_sub_center]; simp [abs_of_pos hr]
        have : ‖circleMap (c : ℂ) r θ - (c : ℂ)‖ - ‖w - (c : ℂ)‖ ≤ ‖(circleMap (c : ℂ) r θ - (c : ℂ)) - (w - (c : ℂ))‖ :=
          norm_sub_norm_le _ _
        have e : (circleMap (c : ℂ) r θ - (c : ℂ)) - (w - (c : ℂ)) = circleMap (c : ℂ) r θ - w := by ring
        rw [e, h0, norm_zero, h1] at this
        linarith
      refine Continuous.norm ?_
      refine Continuous.smul (Continuous.div ((continuous_circleMap _ _).sub continuous_const)
        ((continuous_circleMap _ _).sub continuous_const) hne) (hG.continuous.comp (continuous_circleMap _ _))
    · exact (hcont.const_mul _).intervalIntegrable _ _
  have hsplit : (∫ θ in (0 : ℝ)..2 * π, F θ) =
      (∫ θ in (0 : ℝ)..π, F θ) + (∫ φ in (0 : ℝ)..π, F (φ + π)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 π)
      (hcont.intervalIntegrable π (2 * π))]
    congr 1
    rw [intervalIntegral.integral_comp_add_right F π]
    congr 1 <;> ring
  have hlow : (∫ φ in (0 : ℝ)..π, F (φ + π)) ≤ E * ∫ φ in (0 : ℝ)..π, ‖G (circleMap ((-c : ℝ) : ℂ) r φ)‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hpi.le ?_ ?_ ?_
    · exact (hcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    · exact (((hG.continuous.comp (continuous_circleMap _ _)).norm).const_mul E).intervalIntegrable _ _
    · intro φ hφ
      have hw' : circleMap (c : ℂ) r (φ + π) = -circleMap ((-c : ℝ) : ℂ) r φ := by
        simp only [circleMap, Complex.ofReal_neg, Complex.ofReal_add]
        rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
        ring
      have him : (circleMap (c : ℂ) r (φ + π)).im ≤ 0 := by
        rw [hw']
        have := circleMap_im_nonneg_real (-c) hr.le hφ
        simp only [Complex.neg_im]
        linarith
      have hnorm : ‖circleMap (c : ℂ) r (φ + π) - (c : ℂ)‖ = r := by
        rw [circleMap_sub_center]
        simp [abs_of_pos hr]
      have := hrefl _ hnorm him
      show ‖G (circleMap (c : ℂ) r (φ + π))‖ ≤ E * ‖G (circleMap ((-c : ℝ) : ℂ) r φ)‖
      rw [hw'] at this ⊢
      simpa using this
  have e1 := hardy_arc_weighted hG hC hint c hr
  have e2 := hardy_arc_weighted hG hC hint (-c) hr
  rw [integral_weight_eq] at e1 e2
  have hsub : ∀ t : ℝ, t - -c = t + c := fun t => by ring
  simp_rw [hsub] at e2
  set J1 := ∫ t : ℝ, ‖G (t : ℂ)‖ / ((t - c) ^ 2 + r ^ 2)
  set J2 := ∫ t : ℝ, ‖G (t : ℂ)‖ / ((t + c) ^ 2 + r ^ 2)
  set I1 := ∫ θ in (0 : ℝ)..π, F θ
  set I2 := ∫ φ in (0 : ℝ)..π, ‖G (circleMap ((-c : ℝ) : ℂ) r φ)‖
  have hI1 : I1 ≤ 2 * r * J1 := by nlinarith
  have hI2 : I2 ≤ 2 * r * J2 := by nlinarith
  rw [← hmv, Real.circleAverage_def, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  rw [intervalIntegral.integral_const_mul, hsplit] at hint1
  have hfin : (2 * π)⁻¹ * ‖(∫ θ in (0 : ℝ)..2 * π, (((circleMap (c : ℂ) r θ) - (c : ℂ)) / (circleMap (c : ℂ) r θ - w)) •
        G (circleMap (c : ℂ) r θ))‖ ≤ (2 * π)⁻¹ * ((r / (r - ‖w - (c : ℂ)‖)) * (I1 + E * I2)) := by
    gcongr
    refine hint1.trans ?_
    gcongr
  refine hfin.trans ?_
  have : I1 + E * I2 ≤ 2 * r * J1 + E * (2 * r * J2) := by
    have := mul_le_mul_of_nonneg_left hI2 hE
    linarith
  calc (2 * π)⁻¹ * ((r / (r - ‖w - (c : ℂ)‖)) * (I1 + E * I2))
      ≤ (2 * π)⁻¹ * ((r / (r - ‖w - (c : ℂ)‖)) * (2 * r * J1 + E * (2 * r * J2))) := by gcongr
    _ = _ := by field_simp

/-- **Pointwise bound at `w`, kernels bounded by `1/r²`**: `‖G w‖ ≤ (1 + E) ‖g‖₁ / (π (r - |w - c|))`. -/
theorem hardy_point_real_le {G : ℂ → ℂ} (hG : Differentiable ℂ G) {C : ℝ} {m : ℕ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ C * (1 + ‖z‖) ^ m) (hint : Integrable (fun x : ℝ => G (x : ℂ)))
    (c : ℝ) {r : ℝ} (hr : 0 < r) {E : ℝ} (hE : 0 ≤ E)
    (hrefl : ∀ w : ℂ, ‖w - (c : ℂ)‖ = r → w.im ≤ 0 → ‖G w‖ ≤ E * ‖G (-w)‖) {w : ℂ} (hw : ‖w - (c : ℂ)‖ < r) :
    ‖G w‖ ≤ (1 + E) * (∫ t : ℝ, ‖G (t : ℂ)‖) / (π * (r - ‖w - (c : ℂ)‖)) := by
  have hpi := Real.pi_pos
  have hgap : 0 < r - ‖w - (c : ℂ)‖ := by linarith
  have h := hardy_point_real hG hC hint c hr hE hrefl hw
  refine h.trans ?_
  have hn : Integrable (fun t : ℝ => ‖G (t : ℂ)‖) := hint.norm
  have hk : ∀ s : ℝ, ∫ t : ℝ, ‖G (t : ℂ)‖ / ((t - s) ^ 2 + r ^ 2) ≤ (∫ t : ℝ, ‖G (t : ℂ)‖) / r ^ 2 := by
    intro s
    rw [div_eq_inv_mul, ← MeasureTheory.integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => by positivity) (hn.const_mul _)
      (Eventually.of_forall fun t => ?_)
    show ‖G (t : ℂ)‖ / ((t - s) ^ 2 + r ^ 2) ≤ (r ^ 2)⁻¹ * ‖G (t : ℂ)‖
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by nlinarith [sq_nonneg (t - s)])
  have h1 := hk c
  have h2 := hk (-c)
  simp only [sub_neg_eq_add] at h2
  have hI0 : 0 ≤ ∫ t : ℝ, ‖G (t : ℂ)‖ := integral_nonneg fun t => norm_nonneg _
  calc (r / (r - ‖w - (c : ℂ)‖)) * ((r / π) * ((∫ t : ℝ, ‖G (t : ℂ)‖ / ((t - c) ^ 2 + r ^ 2)) +
        E * ∫ t : ℝ, ‖G (t : ℂ)‖ / ((t + c) ^ 2 + r ^ 2)))
      ≤ (r / (r - ‖w - (c : ℂ)‖)) * ((r / π) * ((∫ t : ℝ, ‖G (t : ℂ)‖) / r ^ 2 +
        E * ((∫ t : ℝ, ‖G (t : ℂ)‖) / r ^ 2))) := by gcongr
    _ = _ := by field_simp

/-- info: 'FormalResearch.Hardy.hardy_point_real_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.hardy_point_real_le

end FormalResearch.Hardy
