module

public import Mathlib

/-!
# Algebraic identities for solutions of the Airy equation `y'' = x y`

This module is independent of any definition of the Airy function.  A solution is a pair
`(y, y')` of functions `𝕜 → 𝕜` (`𝕜 = ℝ` or `ℂ`, any `RCLike` field) with
`y' = dy/dx` and `(y')' = x y` everywhere (`IsAirySol`).  For solutions `(y, y')`, `(w, w')`:

* `IsAirySol.hasDerivAt_wronskian`, `IsAirySol.wronskian_const`: the Wronskian
  `y w' - y' w` is constant;
* `IsAirySol.hasDerivAt_energy`: `(x y² - y'²)' = y²`;
* `airyKernelXY y y' w w' x t = (y x · w' t - y' x · w t)/(x - t)` is the Airy kernel when both
  are `Ai`; `IsAirySol.tendsto_airyKernelXY_diag`: on the diagonal
  `K(x,t) → y'(x)² - x y(x)²` as `t → x` (for `w = y`), and
  `IsAirySol.hasDerivAt_airyKernelXY_shift`: `(∂_x + ∂_t) K(x,t) = - y(x) w(t)` for `x ≠ t`
  (the derivative of `u ↦ K(x+u, t+u)` at `u = 0`).
-/

@[expose] public section

open Filter Topology

namespace FormalResearch.Special

section

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `(y, y')` solves the Airy equation `y'' = x y` on `𝕜`. -/
def IsAirySol (y y' : 𝕜 → 𝕜) : Prop :=
  ∀ x, HasDerivAt y (y' x) x ∧ HasDerivAt y' (x * y x) x

variable {y y' w w' : 𝕜 → 𝕜}

lemma IsAirySol.hasDerivAt_wronskian (hy : IsAirySol y y') (hw : IsAirySol w w') (x : 𝕜) :
    HasDerivAt (fun x => y x * w' x - y' x * w x) 0 x := by
  have h := ((hy x).1.mul (hw x).2).sub ((hy x).2.mul (hw x).1)
  convert h using 1
  ring

/-- The Wronskian of two solutions is constant. -/
theorem IsAirySol.wronskian_const (hy : IsAirySol y y') (hw : IsAirySol w w') (x : 𝕜) :
    y x * w' x - y' x * w x = y 0 * w' 0 - y' 0 * w 0 := by
  have hd : Differentiable 𝕜 (fun x => y x * w' x - y' x * w x) := fun x =>
    (hy.hasDerivAt_wronskian hw x).differentiableAt
  have h0 : deriv (fun x => y x * w' x - y' x * w x) = 0 := funext fun x =>
    (hy.hasDerivAt_wronskian hw x).deriv
  exact is_const_of_deriv_eq_zero hd (fun x => by simp [h0]) x 0

/-- `(x y² - y'²)' = y²`. -/
lemma IsAirySol.hasDerivAt_energy (hy : IsAirySol y y') (x : 𝕜) :
    HasDerivAt (fun x => x * y x ^ 2 - y' x ^ 2) (y x ^ 2) x := by
  have h := ((hasDerivAt_id' x).mul ((hy x).1.pow 2)).sub ((hy x).2.pow 2)
  refine h.congr_deriv ?_
  norm_num
  ring

/-- The Airy-type kernel `(y(x) w'(t) - y'(x) w(t))/(x - t)`. -/
def airyKernelXY (y y' w w' : 𝕜 → 𝕜) (x t : 𝕜) : 𝕜 :=
  (y x * w' t - y' x * w t) / (x - t)

/-- On the diagonal: `K(x, t) → y'(x)² - x y(x)²` as `t → x`, `K = airyKernelXY y y' y y'`. -/
theorem IsAirySol.tendsto_airyKernelXY_diag (hy : IsAirySol y y') (x : 𝕜) :
    Tendsto (fun t => airyKernelXY y y' y y' x t) (𝓝[≠] x) (𝓝 (y' x ^ 2 - x * y x ^ 2)) := by
  have hg : HasDerivAt (fun t => y x * y' t - y' x * y t) (y x * (x * y x) - y' x * y' x) x :=
    ((hy x).2.const_mul (y x)).sub ((hy x).1.const_mul (y' x))
  have hs := (hasDerivAt_iff_tendsto_slope.mp hg).neg
  have hx : (fun t => y x * y' t - y' x * y t) x = 0 := by simp; ring
  have e : ∀ t, t ≠ x → -slope (fun t => y x * y' t - y' x * y t) x t =
      airyKernelXY y y' y y' x t := by
    intro t ht
    have h1 : t - x ≠ 0 := sub_ne_zero.mpr ht
    have h2 : x - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    simp only [slope_def_field, hx, sub_zero, airyKernelXY]
    field_simp
    ring
  refine (hs.congr' ?_).trans_eq ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht using e t ht
  · ring_nf

/-- `(∂_x + ∂_t) K(x, t) = - y(x) w(t)` for `x ≠ t`, as the derivative of `u ↦ K(x+u, t+u)` at
`u = 0`. -/
theorem IsAirySol.hasDerivAt_airyKernelXY_shift (hy : IsAirySol y y') (hw : IsAirySol w w')
    {x t : 𝕜} (hxt : x ≠ t) :
    HasDerivAt (fun u => airyKernelXY y y' w w' (x + u) (t + u)) (-(y x * w t)) 0 := by
  have sh : ∀ (f : 𝕜 → 𝕜) (f' a : 𝕜), HasDerivAt f f' a → HasDerivAt (fun u => f (a + u)) f' 0 :=
    fun f f' a h => HasDerivAt.comp_const_add a 0 (by simpa using h)
  have hyx := sh y _ x (hy x).1
  have hy'x := sh y' _ x (hy x).2
  have hwt := sh w _ t (hw t).1
  have hw't := sh w' _ t (hw t).2
  have hN := ((hyx.mul hw't).sub (hy'x.mul hwt)).div_const (x - t)
  have hne : x - t ≠ 0 := sub_ne_zero.mpr hxt
  convert hN using 1
  · funext u
    simp [airyKernelXY]
  · field_simp
    ring_nf

end

end FormalResearch.Special
