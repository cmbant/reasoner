module

public import Mathlib

/-!
# The Hankel function `H₀¹` on the upper half-plane (Laplace form)

Source: `CFT/modular_bootstrap/paper/edge_transform_sd.tex`, proof of Lemma `SD_H` (`esd:hankel`);
plan item A3 (`UPPER_PLAN.md`).

`H₀¹(z) = (2/(π i)) K₀(-i z)` with `K₀(w) = ∫₀^∞ e^{-w cosh s} ds` for `Re w > 0`, i.e. `Im z > 0`.
The Laplace form never leaves its convergence region on `Im z > 0`.

## Main results
* `besselK0`, `hankel0`: the definitions (`hankel0 z = (2/(π i)) * besselK0 (-i z)`);
* `differentiableOn_besselK0`, `differentiableOn_hankel0`: holomorphy on `Re w > 0`, `Im z > 0`;
* `hankel0_reflection`: `H₀¹(-conj z) = -conj (H₀¹ z)` for `Im z > 0`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Hankel

/-- `K₀(w) = ∫₀^∞ e^{-w cosh s} ds` (the Macdonald function of order `0`, meaningful for `Re w > 0`). -/
noncomputable def besselK0 (w : ℂ) : ℂ := ∫ s in Ioi (0 : ℝ), Complex.exp (-w * (Real.cosh s : ℂ))

/-- The Hankel function `H₀¹(z) = (2/(π i)) K₀(-i z)`, defined by its Laplace form; meaningful for
`Im z > 0`. -/
noncomputable def hankel0 (z : ℂ) : ℂ := (2 / ((π : ℂ) * I)) * besselK0 (-I * z)

/-! ### Elementary bounds -/

lemma cosh_ge_half (s : ℝ) : (1 + s) / 2 ≤ Real.cosh s := by
  rw [Real.cosh_eq]
  have h1 := Real.add_one_le_exp s
  have h2 := Real.exp_pos (-s)
  linarith

lemma norm_exp_neg_mul_cosh (w : ℂ) (s : ℝ) :
    ‖Complex.exp (-w * (Real.cosh s : ℂ))‖ = Real.exp (-(w.re * Real.cosh s)) := by
  rw [Complex.norm_exp]
  simp

lemma norm_exp_neg_mul_cosh_le {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hw : ρ ≤ w.re) (s : ℝ) :
    ‖Complex.exp (-w * (Real.cosh s : ℂ))‖ ≤ Real.exp (-(ρ / 2) * (1 + s)) := by
  rw [norm_exp_neg_mul_cosh]
  apply Real.exp_le_exp.mpr
  have h1 := cosh_ge_half s
  have h2 : ρ * Real.cosh s ≤ w.re * Real.cosh s :=
    mul_le_mul_of_nonneg_right hw (by linarith [Real.one_le_cosh s])
  nlinarith

lemma integrableOn_exp_neg_mul_one_add {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => Real.exp (-(ρ / 2) * (1 + s))) (Ioi 0) := by
  have := (integrableOn_exp_mul_Ioi (a := -(ρ / 2)) (by linarith) 0).const_mul
    (Real.exp (-(ρ / 2)))
  refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
  rw [← Real.exp_add]; ring_nf

lemma integrableOn_exp_neg_mul_cosh {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun s : ℝ => Complex.exp (-w * (Real.cosh s : ℂ))) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg_mul_one_add hw) ?_ ?_
  · exact (by fun_prop : Continuous fun s : ℝ => Complex.exp (-w * (Real.cosh s : ℂ))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun s => norm_exp_neg_mul_cosh_le hw le_rfl s)

/-! ### Holomorphy of `K₀` -/

lemma cosh_exp_bound {c : ℝ} (hc : 0 < c) (s : ℝ) :
    Real.cosh s * Real.exp (-(2 * c) * Real.cosh s) ≤ (1 / c) * Real.exp (-(c / 2) * (1 + s)) := by
  have h1 : c * Real.cosh s ≤ Real.exp (c * Real.cosh s) := by
    linarith [Real.add_one_le_exp (c * Real.cosh s)]
  have h2 : Real.exp (-(c / 2) * (1 + s)) ≥ Real.exp (-c * Real.cosh s) := by
    apply Real.exp_le_exp.mpr
    have := cosh_ge_half s
    nlinarith
  have h3 : Real.cosh s * Real.exp (-(2 * c) * Real.cosh s)
      ≤ (1 / c) * Real.exp (-c * Real.cosh s) := by
    have e1 : Real.exp (-(2 * c) * Real.cosh s) =
        Real.exp (-c * Real.cosh s) * Real.exp (-(c * Real.cosh s)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(c * Real.cosh s)) = (Real.exp (c * Real.cosh s))⁻¹ := by
      rw [Real.exp_neg]
    rw [e1, e2]
    have hp := Real.exp_pos (c * Real.cosh s)
    have hq := Real.exp_pos (-c * Real.cosh s)
    rw [show (1 / c) * Real.exp (-c * Real.cosh s) = Real.exp (-c * Real.cosh s) * (1 / c) by ring]
    have : Real.cosh s * (Real.exp (c * Real.cosh s))⁻¹ ≤ 1 / c := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ hp hc]
      nlinarith
    calc Real.cosh s * (Real.exp (-c * Real.cosh s) * (Real.exp (c * Real.cosh s))⁻¹)
        = Real.exp (-c * Real.cosh s) * (Real.cosh s * (Real.exp (c * Real.cosh s))⁻¹) := by ring
      _ ≤ Real.exp (-c * Real.cosh s) * (1 / c) := mul_le_mul_of_nonneg_left this hq.le
  calc _ ≤ (1 / c) * Real.exp (-c * Real.cosh s) := h3
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

lemma hasDerivAt_besselK0 {w₀ : ℂ} (hw₀ : 0 < w₀.re) :
    HasDerivAt besselK0
      (∫ s in Ioi (0 : ℝ), -(Real.cosh s : ℂ) * Complex.exp (-w₀ * (Real.cosh s : ℂ))) w₀ := by
  set ρ := w₀.re with hρ
  have hρ2 : 0 < ρ / 2 := by positivity
  have hs : Metric.ball w₀ (ρ / 2) ∈ 𝓝 w₀ := Metric.ball_mem_nhds _ hρ2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (w : ℂ) (s : ℝ) => Complex.exp (-w * (Real.cosh s : ℂ)))
    (F' := fun (w : ℂ) (s : ℝ) => -(Real.cosh s : ℂ) * Complex.exp (-w * (Real.cosh s : ℂ)))
    (bound := fun s => (1 / (ρ / 4)) * Real.exp (-((ρ / 4) / 2) * (1 + s)))
    (x₀ := w₀) hs
    (Filter.Eventually.of_forall fun w =>
      (by fun_prop : Continuous fun s : ℝ => Complex.exp (-w * (Real.cosh s : ℂ))).aestronglyMeasurable)
    (integrableOn_exp_neg_mul_cosh hw₀)
    (by exact (by fun_prop : Continuous fun s : ℝ =>
      -(Real.cosh s : ℂ) * Complex.exp (-w₀ * (Real.cosh s : ℂ))).aestronglyMeasurable)
    ?_ ?_ ?_
  · exact key.2
  · refine Filter.Eventually.of_forall fun s w hw => ?_
    have hre : ρ / 2 ≤ w.re := by
      have := Complex.abs_re_le_norm (w - w₀)
      have h2 : ‖w - w₀‖ < ρ / 2 := by simpa [Complex.dist_eq] using hw
      have h3 : (w - w₀).re = w.re - ρ := by simp [hρ]
      rw [h3] at this
      have := (abs_le.mp this).1
      linarith
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by linarith [Real.one_le_cosh s]),
      norm_exp_neg_mul_cosh]
    have hb := cosh_exp_bound (c := ρ / 4) (by positivity) s
    have : Real.exp (-(w.re * Real.cosh s)) ≤ Real.exp (-(2 * (ρ / 4)) * Real.cosh s) := by
      apply Real.exp_le_exp.mpr
      have h1 : ρ / 2 * Real.cosh s ≤ w.re * Real.cosh s :=
        mul_le_mul_of_nonneg_right hre (by linarith [Real.one_le_cosh s])
      nlinarith
    calc Real.cosh s * Real.exp (-(w.re * Real.cosh s))
        ≤ Real.cosh s * Real.exp (-(2 * (ρ / 4)) * Real.cosh s) :=
          mul_le_mul_of_nonneg_left this (by linarith [Real.one_le_cosh s])
      _ ≤ _ := hb
  · exact (integrableOn_exp_neg_mul_one_add (by positivity : 0 < ρ / 4)).const_mul _
  · refine Filter.Eventually.of_forall fun s w _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -w * (Real.cosh s : ℂ)) (-(Real.cosh s : ℂ)) w := by
      simpa using ((hasDerivAt_id w).neg.mul_const (Real.cosh s : ℂ))
    simpa [mul_comm] using h1.cexp

theorem differentiableOn_besselK0 : DifferentiableOn ℂ besselK0 {w : ℂ | 0 < w.re} := fun _ hw =>
  (hasDerivAt_besselK0 hw).differentiableAt.differentiableWithinAt

lemma differentiableOn_hankel0 : DifferentiableOn ℂ hankel0 {z : ℂ | 0 < z.im} := by
  unfold hankel0
  refine DifferentiableOn.const_mul ?_ _
  refine differentiableOn_besselK0.comp (by fun_prop) ?_
  intro z hz
  simpa using hz

/-! ### Reflection -/

lemma besselK0_conj (w : ℂ) : besselK0 ((starRingEnd ℂ) w) = (starRingEnd ℂ) (besselK0 w) := by
  unfold besselK0
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [map_neg, map_mul, ← Complex.exp_conj, neg_mul, Complex.conj_ofReal]

/-- `H₀¹(-z̄) = -conj (H₀¹(z))`. -/
theorem hankel0_reflection (z : ℂ) :
    hankel0 (-(starRingEnd ℂ) z) = -(starRingEnd ℂ) (hankel0 z) := by
  unfold hankel0
  have h1 : -I * (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (-I * z) := by
    simp [Complex.conj_I]
  rw [h1, besselK0_conj, map_mul, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  field_simp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.differentiableOn_besselK0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_besselK0

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.differentiableOn_hankel0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_hankel0

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hankel0_reflection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel0_reflection

end FormalResearch.ModularBootstrap.Upper.Hankel
