module

public import FormalResearch.Complex.HardyArcDecay

/-!
# Fejér–Riesz arc bound centred at a real point, with a Poisson-type weight

Generic complex analysis, no Airy content.  **Proved.**  Let `G : ℂ → ℂ` be entire with `‖G z‖ ≤ C (1+‖z‖)^m` on `Im z ≥ 0`
and `G|_ℝ ∈ L¹(ℝ)`.  Then for every real `x₀` and `r > 0`

`r ∫_0^π ‖G(x₀ + r e^{iφ})‖ dφ ≤ 2 ∫_ℝ ‖G(t)‖ r²/((t - x₀)² + r²) dt`

(`hardy_arc_weighted`): the semicircle of radius `r` about `x₀` carries at most a Cauchy-weighted `L¹` mass of the boundary values.
Proof: apply `hardy_arc_le_poly` to `h(z) = G(x₀ + z) (r/(z + ir))²`, which is holomorphic on a neighbourhood of `Im z ≥ 0`,
polynomially bounded, with `‖h(t)‖ = ‖G(x₀+t)‖ r²/(t²+r²)` on `ℝ` and `‖h‖ ≥ ‖G(x₀+·)‖/4` on the semicircle `|z| = r`
(there `|z + ir| ≤ 2r`).  This is the localised form of the Carleson-measure estimate of the Poisson representation, obtained
from the Fejér–Riesz arc bound alone (no Poisson integral is needed).

`hardy_sample_real` (sub-mean-value at a real point): if moreover `‖G w‖ ≤ E ‖G(-w)‖` on the lower half of the circle `|w - c| = r`
(`c` real), then `‖G(c)‖ ≤ (r/π)(∫ ‖G(t)‖/((t-c)²+r²) dt + E ∫ ‖G(t)‖/((t+c)²+r²) dt)`: the circle average of the entire `G`
(Mathlib `DiffContOnCl.circleAverage`) splits into the upper semicircle about `c` and the (reflected) upper semicircle about `-c`,
each bounded by `hardy_arc_weighted`.

`hardy_point_le` (value at an arbitrary fixed point): for `‖w‖ < ρ` and the same kind of reflection on `|z| = ρ`,
`‖Φ(w)‖ ≤ (ρ/(ρ-‖w‖))(2π)⁻¹(1+E) ∫_0^π ‖Φ(ρe^{iθ})‖ dθ` (Mathlib's generalised mean value property
`DiffContOnCl.circleAverage_smul_div`); together with `hardy_arc_le_poly` this bounds an entire `G` with the Hardy hypotheses at
any fixed point by a constant times `‖G|_ℝ‖₁`.  Not formalised: the Poisson representation of `G` and
`‖G(z)‖ ≤ ‖G|_ℝ‖₁/(π Im z)` for non-real `z`.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace FormalResearch.Hardy

/-- The weighted function `h(z) = G(x₀ + z) (r/(z + ir))²`. -/
noncomputable def hpWeighted (G : ℂ → ℂ) (x₀ r : ℝ) (z : ℂ) : ℂ :=
  G ((x₀ : ℂ) + z) * ((r : ℂ) / (z + (r : ℂ) * I)) ^ 2

lemma hpWeighted_ne {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : 0 ≤ z.im) : z + (r : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

lemma norm_add_rI_sq {r : ℝ} (z : ℂ) : ‖z + (r : ℂ) * I‖ ^ 2 = z.re ^ 2 + (z.im + r) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma hpWeighted_diff {G : ℂ → ℂ} (hG : Differentiable ℂ G) (x₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    DiffContOnCl ℂ (hpWeighted G x₀ r) {z : ℂ | 0 < z.im} := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [closure_setOfPred_lt_im]
  intro z hz
  have hz' : 0 ≤ z.im := hz
  have hne := hpWeighted_ne hr hz'
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold hpWeighted
  refine DifferentiableAt.mul ?_ ?_
  · exact (hG.differentiableAt (x := (x₀ : ℂ) + z)).comp z ((differentiableAt_const _).add differentiableAt_id)
  · refine DifferentiableAt.pow ?_ 2
    exact (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _)) hne

lemma norm_hpWeighted {G : ℂ → ℂ} {x₀ r : ℝ} (hr : 0 < r) (z : ℂ) :
    ‖hpWeighted G x₀ r z‖ = ‖G ((x₀ : ℂ) + z)‖ * (r ^ 2 / (z.re ^ 2 + (z.im + r) ^ 2)) := by
  unfold hpWeighted
  rw [norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_pow]
  have h1 := norm_add_rI_sq (r := r) z
  rw [h1]

lemma hpWeighted_norm_le {G : ℂ → ℂ} {x₀ r : ℝ} (hr : 0 < r) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖hpWeighted G x₀ r z‖ ≤ ‖G ((x₀ : ℂ) + z)‖ := by
  rw [norm_hpWeighted hr z]
  have : r ^ 2 / (z.re ^ 2 + (z.im + r) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg z.re, mul_nonneg hz hr.le]
  calc _ ≤ ‖G ((x₀ : ℂ) + z)‖ * 1 := by gcongr
    _ = _ := mul_one _

/-- On the semicircle `|z| = r`, `Im z ≥ 0`, the weight is at least `1/4`. -/
lemma hpWeighted_norm_ge {G : ℂ → ℂ} {x₀ r : ℝ} (hr : 0 < r) {z : ℂ} (hz : 0 ≤ z.im) (hzr : ‖z‖ = r) :
    ‖G ((x₀ : ℂ) + z)‖ / 4 ≤ ‖hpWeighted G x₀ r z‖ := by
  rw [norm_hpWeighted hr z]
  have hz2 : z.re ^ 2 + z.im ^ 2 = r ^ 2 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply, hzr] at this
    nlinarith
  have : 1 / 4 ≤ r ^ 2 / (z.re ^ 2 + (z.im + r) ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [mul_nonneg hz hr.le, sq_nonneg z.im]
  calc ‖G ((x₀ : ℂ) + z)‖ / 4 = ‖G ((x₀ : ℂ) + z)‖ * (1 / 4) := by ring
    _ ≤ _ := by gcongr

/-- **Weighted Fejér–Riesz arc bound at a real centre.** -/
theorem hardy_arc_weighted {G : ℂ → ℂ} (hG : Differentiable ℂ G) {C : ℝ} {m : ℕ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ C * (1 + ‖z‖) ^ m) (hint : Integrable (fun x : ℝ => G (x : ℂ)))
    (x₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    r * ∫ φ in (0 : ℝ)..π, ‖G (circleMap (x₀ : ℂ) r φ)‖ ≤
      2 * ∫ t : ℝ, ‖G (t : ℂ)‖ * (r ^ 2 / ((t - x₀) ^ 2 + r ^ 2)) := by
  set h := hpWeighted G x₀ r with hh
  have hdiff := hpWeighted_diff hG x₀ hr
  -- growth
  have hgrowth : ∀ z : ℂ, 0 ≤ z.im → ‖h z‖ ≤ (C * (1 + |x₀|) ^ m) * (1 + ‖z‖) ^ m := by
    intro z hz
    refine (hpWeighted_norm_le hr hz).trans ?_
    have h1 : 0 ≤ ((x₀ : ℂ) + z).im := by simpa using hz
    refine (hC _ h1).trans ?_
    have hC0 : 0 ≤ C := by
      have := hC 0 (by simp)
      simp at this
      exact le_trans (norm_nonneg _) this
    have hn : 1 + ‖(x₀ : ℂ) + z‖ ≤ (1 + |x₀|) * (1 + ‖z‖) := by
      have := norm_add_le (x₀ : ℂ) z
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      nlinarith [abs_nonneg x₀, norm_nonneg z]
    calc C * (1 + ‖(x₀ : ℂ) + z‖) ^ m ≤ C * ((1 + |x₀|) * (1 + ‖z‖)) ^ m := by
          gcongr
      _ = _ := by rw [mul_pow]; ring
  -- integrability of the boundary values
  have hcont_h : ContinuousOn h {z : ℂ | 0 ≤ z.im} := by
    have := hdiff.2; rwa [closure_setOfPred_lt_im] at this
  have hint_h : Integrable (fun x : ℝ => h (x : ℂ)) := by
    have hc : Continuous (fun x : ℝ => h (x : ℂ)) :=
      hcont_h.comp_continuous Complex.continuous_ofReal (fun x => by simp)
    have hint' : Integrable (fun x : ℝ => G ((x₀ : ℂ) + (x : ℂ))) := by
      have := hint.comp_add_left x₀
      simpa using this
    refine Integrable.mono' hint'.norm hc.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    exact hpWeighted_norm_le hr (show 0 ≤ (x : ℂ).im by simp)
  have key := hardy_arc_le_poly hdiff hgrowth hint_h hr
  -- left side
  have hL : r * ∫ φ in (0 : ℝ)..π, ‖G (circleMap (x₀ : ℂ) r φ)‖ ≤
      4 * (r * ∫ φ in (0 : ℝ)..π, ‖h (circleMap 0 r φ)‖) := by
    have hcm : ∀ φ : ℝ, circleMap (x₀ : ℂ) r φ = (x₀ : ℂ) + circleMap 0 r φ := by
      intro φ; simp [circleMap]
    have hG1 : Continuous (fun φ : ℝ => ‖G (circleMap (x₀ : ℂ) r φ)‖) :=
      (hG.continuous.comp (continuous_circleMap _ _)).norm
    have hh1 : IntervalIntegrable (fun φ : ℝ => ‖h (circleMap 0 r φ)‖) volume 0 π := by
      refine ContinuousOn.intervalIntegrable ?_
      refine (hcont_h.comp (continuous_circleMap 0 r).continuousOn (fun φ hφ => ?_)).norm
      rw [Set.uIcc_of_le Real.pi_pos.le] at hφ
      exact circleMap_im_nonneg hr.le hφ
    have : ∫ φ in (0 : ℝ)..π, ‖G (circleMap (x₀ : ℂ) r φ)‖ ≤ 4 * ∫ φ in (0 : ℝ)..π, ‖h (circleMap 0 r φ)‖ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on Real.pi_pos.le (hG1.intervalIntegrable _ _) (hh1.const_mul 4) ?_
      intro φ hφ
      have hz := circleMap_im_nonneg hr.le hφ
      have hzr : ‖circleMap 0 r φ‖ = r := by simp [abs_of_pos hr]
      have := hpWeighted_norm_ge (G := G) (x₀ := x₀) hr hz hzr
      rw [hcm]
      linarith
    nlinarith
  -- right side
  have hR : ∫ t : ℝ, ‖h (t : ℂ)‖ = ∫ t : ℝ, ‖G (t : ℂ)‖ * (r ^ 2 / ((t - x₀) ^ 2 + r ^ 2)) := by
    have e1 : ∀ t : ℝ, ‖h (t : ℂ)‖ = ‖G ((x₀ + t : ℝ) : ℂ)‖ * (r ^ 2 / ((x₀ + t - x₀) ^ 2 + r ^ 2)) := by
      intro t
      rw [norm_hpWeighted hr (t : ℂ)]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_add, Complex.ofReal_add]
      congr 2
      ring
    simp_rw [e1]
    exact MeasureTheory.integral_add_left_eq_self
      (fun t : ℝ => ‖G (t : ℂ)‖ * (r ^ 2 / ((t - x₀) ^ 2 + r ^ 2))) x₀
  rw [hR] at key
  linarith


lemma circleMap_im_nonneg_real (x : ℝ) {a : ℝ} (ha : 0 ≤ a) {φ : ℝ} (hφ : φ ∈ Icc (0 : ℝ) π) :
    0 ≤ (circleMap (x : ℂ) a φ).im := by
  simp only [circleMap, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have := mul_nonneg ha (Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 hφ.2)
  linarith

/-- Rewriting the weighted integrals with the constant `r²` pulled out. -/
lemma integral_weight_eq (F : ℝ → ℝ) (c r : ℝ) :
    ∫ t : ℝ, F t * (r ^ 2 / ((t - c) ^ 2 + r ^ 2)) = r ^ 2 * ∫ t : ℝ, F t / ((t - c) ^ 2 + r ^ 2) := by
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  ext t
  ring

/-- **Sub-mean-value bound at a real point.**  `G` entire with the Hardy hypotheses, `c` real, `r > 0`, and the reflection
`‖G w‖ ≤ E ‖G(-w)‖` on the lower half of the circle `|w - c| = r`:
`‖G(c)‖ ≤ (r/π) (∫ ‖G(t)‖/((t-c)² + r²) dt + E ∫ ‖G(t)‖/((t+c)² + r²) dt)`. -/
theorem hardy_sample_real {G : ℂ → ℂ} (hG : Differentiable ℂ G) {C : ℝ} {m : ℕ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ C * (1 + ‖z‖) ^ m) (hint : Integrable (fun x : ℝ => G (x : ℂ)))
    (c : ℝ) {r : ℝ} (hr : 0 < r) {E : ℝ} (hE : 0 ≤ E)
    (hrefl : ∀ w : ℂ, ‖w - (c : ℂ)‖ = r → w.im ≤ 0 → ‖G w‖ ≤ E * ‖G (-w)‖) :
    ‖G (c : ℂ)‖ ≤ (r / π) * ((∫ t : ℝ, ‖G (t : ℂ)‖ / ((t - c) ^ 2 + r ^ 2)) +
      E * ∫ t : ℝ, ‖G (t : ℂ)‖ / ((t + c) ^ 2 + r ^ 2)) := by
  have hpi := Real.pi_pos
  have hmv : G (c : ℂ) = Real.circleAverage G (c : ℂ) r := by
    have := (hG.diffContOnCl (s := Metric.ball (c : ℂ) |r|)).circleAverage
    exact this.symm
  have hcont : Continuous (fun θ : ℝ => ‖G (circleMap (c : ℂ) r θ)‖) :=
    (hG.continuous.comp (continuous_circleMap _ _)).norm
  have h1 : ‖G (c : ℂ)‖ ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖G (circleMap (c : ℂ) r θ)‖ := by
    rw [hmv, Real.circleAverage_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    gcongr
    exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
  have hsplit : ∫ θ in (0 : ℝ)..2 * π, ‖G (circleMap (c : ℂ) r θ)‖ =
      (∫ θ in (0 : ℝ)..π, ‖G (circleMap (c : ℂ) r θ)‖) +
        ∫ φ in (0 : ℝ)..π, ‖G (circleMap (c : ℂ) r (φ + π))‖ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 π)
      (hcont.intervalIntegrable π (2 * π))]
    congr 1
    rw [intervalIntegral.integral_comp_add_right (fun θ => ‖G (circleMap (c : ℂ) r θ)‖) π]
    congr 1 <;> ring
  have hlow : ∫ φ in (0 : ℝ)..π, ‖G (circleMap (c : ℂ) r (φ + π))‖ ≤
      E * ∫ φ in (0 : ℝ)..π, ‖G (circleMap ((-c : ℝ) : ℂ) r φ)‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hpi.le ?_ ?_ ?_
    · exact ((hG.continuous.comp ((continuous_circleMap _ _).comp (continuous_id.add continuous_const))).norm).intervalIntegrable _ _
    · exact (((hG.continuous.comp (continuous_circleMap _ _)).norm).const_mul E).intervalIntegrable _ _
    · intro φ hφ
      have hw : circleMap (c : ℂ) r (φ + π) = -circleMap ((-c : ℝ) : ℂ) r φ := by
        simp only [circleMap, Complex.ofReal_neg, Complex.ofReal_add]
        rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
        ring
      have him : (circleMap (c : ℂ) r (φ + π)).im ≤ 0 := by
        rw [hw]
        have := circleMap_im_nonneg_real (-c) hr.le hφ
        simp only [Complex.neg_im]
        linarith
      have hnorm : ‖circleMap (c : ℂ) r (φ + π) - (c : ℂ)‖ = r := by
        rw [circleMap_sub_center]
        simp [abs_of_pos hr]
      have := hrefl _ hnorm him
      rw [hw] at this ⊢
      simpa using this
  have e1 := hardy_arc_weighted hG hC hint c hr
  have e2 := hardy_arc_weighted hG hC hint (-c) hr
  rw [integral_weight_eq] at e1 e2
  have hsub : ∀ t : ℝ, t - -c = t + c := fun t => by ring
  simp_rw [hsub] at e2
  set J1 := ∫ t : ℝ, ‖G (t : ℂ)‖ / ((t - c) ^ 2 + r ^ 2)
  set J2 := ∫ t : ℝ, ‖G (t : ℂ)‖ / ((t + c) ^ 2 + r ^ 2)
  set I1 := ∫ θ in (0 : ℝ)..π, ‖G (circleMap (c : ℂ) r θ)‖
  set I2 := ∫ φ in (0 : ℝ)..π, ‖G (circleMap ((-c : ℝ) : ℂ) r φ)‖
  have hI1 : I1 ≤ 2 * r * J1 := by nlinarith
  have hI2 : I2 ≤ 2 * r * J2 := by nlinarith
  rw [hsplit] at h1
  have hfin : ‖G (c : ℂ)‖ ≤ (2 * π)⁻¹ * (2 * r * J1 + E * (2 * r * J2)) := by
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_left hI2 hE
    linarith
  calc _ ≤ _ := hfin
    _ = _ := by field_simp

/-- **Pointwise bound at an arbitrary fixed point from the arc integral.**  `Φ` entire, `ρ > ‖w‖`, and the reflection
`‖Φ z‖ ≤ E ‖Φ(-z)‖` on the lower half of the circle `|z| = ρ`.  Then
`‖Φ(w)‖ ≤ (ρ/(ρ - ‖w‖)) (1/(2π)) (1 + E) ∫_0^π ‖Φ(ρ e^{iθ})‖ dθ`
(Cauchy's formula on `|z| = ρ`, `circleAverage (z/(z-w) · Φ z) = Φ w`, the lower semicircle reflected to the upper one). -/
theorem hardy_point_le {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {w : ℂ} {ρ : ℝ} (hρ : ‖w‖ < ρ) {E : ℝ}
    (hrefl : ∀ z : ℂ, ‖z‖ = ρ → z.im ≤ 0 → ‖Φ z‖ ≤ E * ‖Φ (-z)‖) :
    ‖Φ w‖ ≤ (ρ / (ρ - ‖w‖)) * ((2 * π)⁻¹ * ((1 + E) * ∫ θ in (0 : ℝ)..π, ‖Φ (circleMap 0 ρ θ)‖)) := by
  have hpi := Real.pi_pos
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hρ
  have hgap : 0 < ρ - ‖w‖ := by linarith
  have hwb : w ∈ Metric.ball (0 : ℂ) |ρ| := by
    rw [mem_ball_zero_iff, abs_of_pos hρ0]; exact hρ
  have hmv := (hΦ.diffContOnCl (s := Metric.ball (0 : ℂ) |ρ|)).circleAverage_smul_div hwb
  rw [← hmv, Real.circleAverage_def, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  set F : ℝ → ℝ := fun θ => ‖Φ (circleMap 0 ρ θ)‖ with hF
  have hFc : Continuous F := (hΦ.continuous.comp (continuous_circleMap _ _)).norm
  have hbound : ∀ θ : ℝ, ‖(((circleMap 0 ρ θ) - 0) / (circleMap 0 ρ θ - w)) • Φ (circleMap 0 ρ θ)‖ ≤
      (ρ / (ρ - ‖w‖)) * F θ := by
    intro θ
    rw [norm_smul, norm_div, sub_zero]
    have h1 : ‖circleMap 0 ρ θ‖ = ρ := by simp [abs_of_pos hρ0]
    have h2 : ρ - ‖w‖ ≤ ‖circleMap 0 ρ θ - w‖ := by
      have := norm_sub_norm_le (circleMap 0 ρ θ) w
      rw [h1] at this; exact this
    rw [h1]
    have : ρ / ‖circleMap 0 ρ θ - w‖ ≤ ρ / (ρ - ‖w‖) :=
      div_le_div_of_nonneg_left hρ0.le hgap h2
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hint1 : ‖(∫ θ in (0 : ℝ)..2 * π, (((circleMap 0 ρ θ) - 0) / (circleMap 0 ρ θ - w)) • Φ (circleMap 0 ρ θ))‖ ≤
      (∫ θ in (0 : ℝ)..2 * π, (ρ / (ρ - ‖w‖)) * F θ) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans ?_
    refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ (fun θ _ => hbound θ)
    · refine ContinuousOn.intervalIntegrable ?_
      refine (Continuous.continuousOn ?_)
      have : Continuous fun θ : ℝ => circleMap 0 ρ θ - w := (continuous_circleMap _ _).sub continuous_const
      refine Continuous.norm ?_
      refine Continuous.smul (Continuous.div ((continuous_circleMap _ _).sub continuous_const) this ?_)
        (hΦ.continuous.comp (continuous_circleMap _ _))
      intro θ h0
      have := norm_sub_norm_le (circleMap 0 ρ θ) w
      have h1 : ‖circleMap 0 ρ θ‖ = ρ := by simp [abs_of_pos hρ0]
      rw [h0, norm_zero, h1] at this
      linarith
    · exact (hFc.const_mul _).intervalIntegrable _ _
  have hsplit : (∫ θ in (0 : ℝ)..2 * π, F θ) =
      (∫ θ in (0 : ℝ)..π, F θ) + (∫ φ in (0 : ℝ)..π, F (φ + π)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable 0 π)
      (hFc.intervalIntegrable π (2 * π))]
    congr 1
    rw [intervalIntegral.integral_comp_add_right F π]
    congr 1 <;> ring
  have hlow : (∫ φ in (0 : ℝ)..π, F (φ + π)) ≤ E * (∫ φ in (0 : ℝ)..π, F φ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hpi.le ?_ ?_ ?_
    · exact (hFc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    · exact (hFc.const_mul E).intervalIntegrable _ _
    · intro φ hφ
      have hw' : circleMap 0 ρ (φ + π) = -circleMap 0 ρ φ := by
        simp only [circleMap, Complex.ofReal_add, zero_add]
        rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
        ring
      have him : (circleMap 0 ρ (φ + π)).im ≤ 0 := by
        rw [hw']
        have := circleMap_im_nonneg hρ0.le hφ
        simp only [Complex.neg_im]
        linarith
      have hnorm : ‖circleMap 0 ρ (φ + π)‖ = ρ := by simp [abs_of_pos hρ0]
      have := hrefl _ hnorm him
      rw [hw', neg_neg] at this
      show ‖Φ (circleMap 0 ρ (φ + π))‖ ≤ E * ‖Φ (circleMap 0 ρ φ)‖
      rw [hw']
      exact this
  have hF1 : (∫ θ in (0 : ℝ)..2 * π, (ρ / (ρ - ‖w‖)) * F θ) =
      (ρ / (ρ - ‖w‖)) * (∫ θ in (0 : ℝ)..2 * π, F θ) := by
    exact intervalIntegral.integral_const_mul _ _
  rw [hF1, hsplit] at hint1
  have hI0 : 0 ≤ (∫ φ in (0 : ℝ)..π, F φ) := intervalIntegral.integral_nonneg hpi.le (fun θ _ => norm_nonneg _)
  have hq : 0 ≤ ρ / (ρ - ‖w‖) := by positivity
  calc (2 * π)⁻¹ * ‖(∫ θ in (0 : ℝ)..2 * π, (((circleMap 0 ρ θ) - 0) / (circleMap 0 ρ θ - w)) • Φ (circleMap 0 ρ θ))‖
      ≤ (2 * π)⁻¹ * ((ρ / (ρ - ‖w‖)) * ((∫ θ in (0 : ℝ)..π, F θ) + ∫ φ in (0 : ℝ)..π, F (φ + π))) := by
        gcongr
    _ ≤ (2 * π)⁻¹ * ((ρ / (ρ - ‖w‖)) * ((1 + E) * ∫ θ in (0 : ℝ)..π, F θ)) := by
        gcongr
        linarith
    _ = _ := by ring

/-- info: 'FormalResearch.Hardy.hardy_arc_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.hardy_arc_weighted

/-- info: 'FormalResearch.Hardy.hardy_point_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.hardy_point_le

/-- info: 'FormalResearch.Hardy.hardy_sample_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.hardy_sample_real

end FormalResearch.Hardy
