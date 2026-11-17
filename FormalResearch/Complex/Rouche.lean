module

public import FormalResearch.Complex.ArgumentPrinciple
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Rouché's theorem on a circle

Generic complex analysis (no application content).  **Proved.**

Statement formalised (Rouché 1862; Ahlfors, *Complex Analysis*, §5.2.3; Conway V.3.8, circle case): let `f, g` be holomorphic
on `ball c R`, `0 < r < R`, and `‖f z - g z‖ < ‖g z‖` on the circle `sphere c r`.  Then `f` and `g` have the same number of
zeros, counted with multiplicity, in the open disc `ball c r` (`FormalResearch.ArgPrinciple.rouche`).

Proof: `f/g` maps the circle into the disc `‖w - 1‖ < 1 ⊂ {Re w > 0}`, so the principal logarithm `log (f/g)` is
holomorphic near every point of the circle and has derivative `f'/f - g'/g`.  The circle integral of a derivative vanishes
(`circleIntegral.integral_eq_zero_of_hasDerivWithinAt`), so the integrals of `f'/f` and `g'/g` agree, and the argument
principle (`ArgPrinciple.circleIntegral_logDeriv`) turns them into the zero counts.

**Not formalised.** The symmetric version `‖f - g‖ < ‖f‖ + ‖g‖` (needs a homotopy or `log` along an arc), poles, general contours.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ArgPrinciple

variable {f g : ℂ → ℂ} {c : ℂ} {r R : ℝ}

/-- On the circle, `f/g` lies in the disc `‖w - 1‖ < 1`, hence in the slit plane. -/
lemma div_mem_slitPlane {a b : ℂ} (h : ‖a - b‖ < ‖b‖) : a / b ∈ slitPlane := by
  have hb : b ≠ 0 := by
    intro h0; rw [h0] at h; simp at h; exact absurd h (not_lt.mpr (norm_nonneg _))
  have h1 : ‖a / b - 1‖ < 1 := by
    have : a / b - 1 = (a - b) / b := by field_simp
    rw [this, norm_div, div_lt_one (norm_pos_iff.mpr hb)]; exact h
  have h2 : |(a / b - 1).re| ≤ ‖a / b - 1‖ := abs_re_le_norm _
  have h3 : 0 < (a / b).re := by
    have := (abs_lt.mp (lt_of_le_of_lt h2 h1)).1
    simp at this; linarith
  exact Or.inl h3

/-- **Rouché's theorem on a circle.** -/
theorem rouche (hr : 0 < r) (hrR : r < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hg : DifferentiableOn ℂ g (ball c R)) (h : ∀ z ∈ sphere c r, ‖f z - g z‖ < ‖g z‖) :
    zeroCount f c r = zeroCount g c r := by
  have hgne : ∀ z ∈ sphere c r, g z ≠ 0 := fun z hz h0 => by
    have := h z hz; rw [h0] at this; simp at this; exact absurd this (not_lt.mpr (norm_nonneg _))
  have hfne : ∀ z ∈ sphere c r, f z ≠ 0 := fun z hz h0 => by
    have := h z hz; rw [h0] at this; simp at this
  have hsub : sphere c r ⊆ ball c R := (sphere_subset_closedBall).trans (closedBall_subset_ball hrR)
  have hanf : AnalyticOnNhd ℂ f (ball c R) := hf.analyticOnNhd isOpen_ball
  have hang : AnalyticOnNhd ℂ g (ball c R) := hg.analyticOnNhd isOpen_ball
  have hI : (∮ z in C(c, r), (deriv f z / f z - deriv g z / g z)) = 0 := by
    refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt (f := fun z => Complex.log (f z / g z)) hr.le fun z hz => ?_
    have hzR := hsub hz
    have hfd : HasDerivAt f (deriv f z) z := (hf.differentiableAt (isOpen_ball.mem_nhds hzR)).hasDerivAt
    have hgd : HasDerivAt g (deriv g z) z := (hg.differentiableAt (isOpen_ball.mem_nhds hzR)).hasDerivAt
    have hq := hfd.div hgd (hgne z hz)
    have hl := hq.clog (div_mem_slitPlane (h z hz))
    refine (hl.hasDerivWithinAt).congr_deriv ?_
    have h1 := hfne z hz
    have h2 := hgne z hz
    simp only [Pi.div_apply]
    field_simp
  have hc1 : CircleIntegrable (fun z => deriv f z / f z) c r :=
    ContinuousOn.circleIntegrable hr.le
      ((hanf.deriv.continuousOn.mono hsub).div (hanf.continuousOn.mono hsub) hfne)
  have hc2 : CircleIntegrable (fun z => deriv g z / g z) c r :=
    ContinuousOn.circleIntegrable hr.le
      ((hang.deriv.continuousOn.mono hsub).div (hang.continuousOn.mono hsub) hgne)
  rw [circleIntegral.integral_sub hc1 hc2] at hI
  have hf' := circleIntegral_logDeriv hr hrR hf hfne
  have hg' := circleIntegral_logDeriv hr hrR hg hgne
  rw [hf', hg', ← mul_sub] at hI
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have := (mul_eq_zero.mp hI).resolve_left h2pi
  exact_mod_cast sub_eq_zero.mp this

/-- info: 'FormalResearch.ArgPrinciple.rouche' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ArgPrinciple.rouche

end FormalResearch.ArgPrinciple
