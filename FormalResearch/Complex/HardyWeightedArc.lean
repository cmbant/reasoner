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
each bounded by `hardy_arc_weighted`.  Not formalised: the Poisson representation of `G` and
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

/-- info: 'FormalResearch.Hardy.hardy_arc_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.hardy_arc_weighted

/-- info: 'FormalResearch.Hardy.hardy_sample_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.hardy_sample_real

end FormalResearch.Hardy
