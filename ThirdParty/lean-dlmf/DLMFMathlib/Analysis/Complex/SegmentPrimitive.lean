/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Straight-segment primitives of entire functions

The normalized straight-segment integral `z * ∫₀¹ f (t z) dt` of an entire function is a
primitive of it. The primitive existence theorem and the real fundamental theorem of calculus
come from Mathlib; the results here identify the segment integral with an arbitrary primitive
and give its complex derivative.

## Main results

* `eq_of_differentiable_of_eqOn_pos_reals`: entire functions agreeing on the positive real axis
  agree everywhere.
* `differentiable_dslope_entire`: the divided difference of an entire function is entire.
* `mul_integral_comp_mul_eq_sub`: integrating a complex derivative along a straight segment
  recovers the endpoint difference.
* `hasDerivAt_mul_integral_comp_mul`: the normalized segment integral differentiates to the
  integrand.
-/

@[expose] public noncomputable section
open Complex Set MeasureTheory
open scoped Interval

namespace Complex

/-- Entire functions agreeing on the positive real axis agree everywhere. -/
theorem eq_of_differentiable_of_eqOn_pos_reals {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ x : ℝ, 0<x → f x=g x) : f=g := by
  have ht : Filter.Tendsto (fun x : ℝ => (x:ℂ)) (nhdsWithin 0 (Ioi 0))
      (nhdsWithin (0:ℂ) {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  apply (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_frequently_eq
      (hg.differentiableOn.analyticOnNhd isOpen_univ)
  apply ht.frequently
  have he : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0), f x=g x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact h x hx
  exact he.frequently

/-- The divided difference of an entire complex function is entire at its filled-in center. -/
theorem differentiable_dslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (dslope f c) := by
  rw [← differentiableOn_univ,differentiableOn_dslope Filter.univ_mem]
  exact hf.differentiableOn

/-- Integrating a complex derivative on a straight segment recovers the endpoint difference. -/
theorem mul_integral_comp_mul_eq_sub {f g : ℂ → ℂ}
    (hg : ∀ z, HasDerivAt g (f z) z) (z : ℂ) :
    z * (∫ t : ℝ in 0..1, f (t*z)) = g z-g 0 := by
  have hgd : Differentiable ℂ g := fun w => (hg w).differentiableAt
  have he : deriv g = f := funext fun w => (hg w).deriv
  have hf : Continuous f := he ▸ hgd.deriv.continuous
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => g (u*z)) (z*f (t*z)) t := by
    simpa [mul_comm] using
      ((hg (t*z)).comp (t:ℂ) ((hasDerivAt_id (t:ℂ)).mul_const z)).comp_ofReal
  have hi : IntervalIntegrable (fun t : ℝ => z*f (t*z)) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => z*f (t*z))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa [intervalIntegral.integral_const_mul] using h

/-- The normalized straight-segment integral of an entire function differentiates to it. -/
theorem hasDerivAt_mul_integral_comp_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasDerivAt (fun w : ℂ => w*(∫ t : ℝ in 0..1, f (t*w))) (f z) z := by
  obtain ⟨g, hg⟩ := hf.isExactOn_univ
  have hg' (w : ℂ) := hg w (mem_univ w)
  have he : (fun w : ℂ => w*(∫ t : ℝ in 0..1, f (t*w))) = fun w => g w-g 0 :=
    funext (mul_integral_comp_mul_eq_sub hg')
  rw [he]
  exact (hg' z).sub_const _

end Complex
