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

/-- **Uniqueness** for the Airy equation along the real line, complex values: a solution
`(y, y')` of `y'' = x y` (`x ∈ ℝ`, `y : ℝ → ℂ`) with `y(0) = y'(0) = 0` vanishes identically.
(Gronwall, through Mathlib's `ODE_solution_unique_of_mem_Ioo` for `v t (a, b) = (b, t a)` on
`ℂ × ℂ`, Lipschitz with constant `1 + R` for `|t| < R`.) -/
theorem airy_unique_real (y y' : ℝ → ℂ)
    (h : ∀ x : ℝ, HasDerivAt y (y' x) x ∧ HasDerivAt y' ((x : ℂ) * y x) x)
    (h0 : y 0 = 0) (h0' : y' 0 = 0) (x : ℝ) : y x = 0 := by
  set R : ℝ := |x| + 1 with hR
  have hRpos : 0 < R := by positivity
  let v : ℝ → ℂ × ℂ → ℂ × ℂ := fun t p => (p.2, (t : ℂ) * p.1)
  have hv : ∀ t ∈ Set.Ioo (-R) R, LipschitzOnWith (Real.toNNReal (1 + R))
      (v t) (Set.univ : Set (ℂ × ℂ)) := by
    intro t ht
    rw [lipschitzOnWith_univ]
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [Prod.dist_eq, Prod.dist_eq]
    have habs : |t| ≤ R := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
    have hK : (↑(Real.toNNReal (1 + R)) : ℝ) = 1 + R := Real.coe_toNNReal _ (by linarith)
    rw [hK]
    simp only [v, dist_eq_norm]
    refine max_le ?_ ?_
    · calc ‖p.2 - q.2‖ ≤ max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := le_max_right _ _
        _ ≤ (1 + R) * max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := by
            nlinarith [le_max_right ‖p.1 - q.1‖ ‖p.2 - q.2‖, norm_nonneg (p.2 - q.2),
              norm_nonneg (p.1 - q.1)]
    · calc ‖(t : ℂ) * p.1 - (t : ℂ) * q.1‖ = |t| * ‖p.1 - q.1‖ := by
            rw [← mul_sub, norm_mul]; simp
        _ ≤ R * max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := by
            apply mul_le_mul habs (le_max_left _ _) (norm_nonneg _) hRpos.le
        _ ≤ (1 + R) * max ‖p.1 - q.1‖ ‖p.2 - q.2‖ := by
            nlinarith [le_max_left ‖p.1 - q.1‖ ‖p.2 - q.2‖, norm_nonneg (p.1 - q.1)]
  have hf : ∀ t ∈ Set.Ioo (-R) R,
      HasDerivAt (fun t => (y t, y' t)) (v t (y t, y' t)) t ∧ (y t, y' t) ∈ (Set.univ : Set (ℂ × ℂ)) :=
    fun t _ => ⟨((h t).1).prodMk ((h t).2), Set.mem_univ _⟩
  have hg : ∀ t ∈ Set.Ioo (-R) R,
      HasDerivAt (fun _ : ℝ => ((0 : ℂ), (0 : ℂ))) (v t ((0 : ℂ), (0 : ℂ))) t ∧
        ((0 : ℂ), (0 : ℂ)) ∈ (Set.univ : Set (ℂ × ℂ)) := fun t _ => by
    refine ⟨?_, Set.mem_univ _⟩
    convert hasDerivAt_const t ((0 : ℂ), (0 : ℂ)) using 1
    simp [v]
  have := ODE_solution_unique_of_mem_Ioo (t₀ := 0) hv ⟨by linarith, hRpos⟩ hf hg
    (by simp [h0, h0'])
  have hx : x ∈ Set.Ioo (-R) R := by
    rw [hR]; constructor <;> cases abs_cases x <;> linarith
  have := this hx
  simpa using congrArg Prod.fst this

/-- A solution of `y'' = x y` on `ℝ` is determined by `(y(0), y'(0))`. -/
theorem airy_eq_of_initial (y y' w w' : ℝ → ℂ)
    (hy : ∀ x : ℝ, HasDerivAt y (y' x) x ∧ HasDerivAt y' ((x : ℂ) * y x) x)
    (hw : ∀ x : ℝ, HasDerivAt w (w' x) x ∧ HasDerivAt w' ((x : ℂ) * w x) x)
    (h0 : y 0 = w 0) (h0' : y' 0 = w' 0) (x : ℝ) : y x = w x := by
  have := airy_unique_real (fun x => y x - w x) (fun x => y' x - w' x)
    (fun x => ⟨(hy x).1.sub (hw x).1, by convert (hy x).2.sub (hw x).2 using 1; ring⟩)
    (by simp [h0]) (by simp [h0']) x
  exact sub_eq_zero.mp this

end FormalResearch.Special
