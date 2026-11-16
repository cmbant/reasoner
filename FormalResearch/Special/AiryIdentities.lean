module

public import FormalResearch.Special.AiryBound
public import FormalResearch.Special.AiryEquation

/-!
# Identities for `Ai` from the abstract Airy equation, and limits at `+∞`

* `isAirySol_airyAi`, `isAirySol_airyAiC`: `(Ai, Ai')` solves the Airy equation (`IsAirySol`) on `ℝ`
  and on `ℂ`, so every identity of `AiryEquation` applies (constant Wronskians, the energy identity
  `(x Ai² - Ai'²)' = Ai²`, the kernel limits).
* `tendsto_airyAi`, `tendsto_airyAi'`, `tendsto_airyAi_energy`: `Ai`, `Ai'` and `x Ai² - Ai'²`
  tend to `0` at `+∞` (from the explicit bounds of `AiryBound`).
* `integral_Ioi_airyAi_sq`: `∫_x^∞ Ai(t)² dt = Ai'(x)² - x Ai(x)²` for every real `x`
  (so `Ai'(x)² - x Ai(x)²` is the diagonal value `K(x,x)` of the Airy kernel, see
  `airyKernelAi_diag`).

Not formalised: `∫_0^∞ Ai = 1/3` (and hence `∫_x^∞ Ai = 1/3 - ∫_0^x Ai`).
-/

@[expose] public section

open Filter Topology MeasureTheory Set
open scoped Real

namespace FormalResearch.Special

theorem isAirySol_airyAi : IsAirySol airyAi airyAi' :=
  fun x => ⟨hasDerivAt_airyAi x, hasDerivAt_airyAi' x⟩

theorem isAirySol_airyAiC : IsAirySol airyAiC (deriv airyAiC) :=
  fun z => ⟨differentiable_airyAiC.differentiableAt.hasDerivAt, hasDerivAt_deriv_airyAiC z⟩

/-- The Airy kernel `K(x, t) = (Ai(x) Ai'(t) - Ai'(x) Ai(t))/(x - t)` (for `x ≠ t`; the value on
the diagonal is `airyKernelAi_diag`). -/
noncomputable def airyKernelAi (x t : ℝ) : ℝ :=
  (airyAi x * airyAi' t - airyAi' x * airyAi t) / (x - t)

/-- `K(x, t) → Ai'(x)² - x Ai(x)²` as `t → x`. -/
theorem airyKernelAi_diag (x : ℝ) :
    Tendsto (fun t => airyKernelAi x t) (𝓝[≠] x) (𝓝 (airyAi' x ^ 2 - x * airyAi x ^ 2)) :=
  isAirySol_airyAi.tendsto_airyKernelXY_diag x

/-- `(∂_x + ∂_t) K(x, t) = - Ai(x) Ai(t)` for `x ≠ t`. -/
theorem airyKernelAi_shift {x t : ℝ} (hxt : x ≠ t) :
    HasDerivAt (fun u => airyKernelAi (x + u) (t + u)) (-(airyAi x * airyAi t)) 0 :=
  isAirySol_airyAi.hasDerivAt_airyKernelXY_shift isAirySol_airyAi hxt

/-- The Wronskian of `Ai` with any real solution `(w, w')` is constant. -/
theorem airyAi_wronskian_const (w w' : ℝ → ℝ) (hw : IsAirySol w w') (x : ℝ) :
    airyAi x * w' x - airyAi' x * w x = airyAi 0 * w' 0 - airyAi' 0 * w 0 :=
  isAirySol_airyAi.wronskian_const hw x

lemma tendsto_rpow_mul_exp_rpow (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ a * Real.exp (-b * t ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => t ^ (3 / 2 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * a / 3) b hb).comp hu
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul ht.le]
  congr 2
  ring

/-- If `|g t| ≤ C t^a exp(-b t^{3/2})` eventually then `g → 0`. -/
lemma tendsto_zero_of_le_rpow_exp {g : ℝ → ℝ} {C b : ℝ} (a : ℝ) (hb : 0 < b)
    (h : ∀ᶠ t in atTop, |g t| ≤ C * (t ^ a * Real.exp (-b * t ^ (3 / 2 : ℝ)))) :
    Tendsto g atTop (𝓝 0) := by
  have := (tendsto_rpow_mul_exp_rpow a hb).const_mul C
  rw [mul_zero] at this
  exact squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using h) this

theorem tendsto_airyAi : Tendsto airyAi atTop (𝓝 0) := by
  refine tendsto_zero_of_le_rpow_exp (C := 1 / (2 * √π)) (b := 2 / 3) (-(1 / 4)) (by norm_num) ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have := airyAi_abs_le ht
  linarith [this, show 1 / (2 * √π) * t ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ)) =
    1 / (2 * √π) * (t ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ))) by ring]

theorem tendsto_sqrt_mul_airyAi : Tendsto (fun t => √t * airyAi t) atTop (𝓝 0) := by
  refine tendsto_zero_of_le_rpow_exp (C := 1 / (2 * √π)) (b := 2 / 3) (1 / 4) (by norm_num) ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have h1 := airyAi_abs_le ht
  have e : √t * t ^ (-(1 / 4) : ℝ) = t ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]; norm_num
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
  calc √t * |airyAi t| ≤ √t * (1 / (2 * √π) * t ^ (-(1 / 4) : ℝ) *
        Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg t)
    _ = 1 / (2 * √π) * (t ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * t ^ (3 / 2 : ℝ))) := by
        rw [← e]; ring

theorem tendsto_airyAi' : Tendsto airyAi' atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_mul_exp_rpow (1 / 4) (b := 2 / 3) (by norm_num)).const_mul
    (1 / (2 * π) * √π)
  have h2 := (tendsto_rpow_mul_exp_rpow (-(1 / 2)) (b := 2 / 3) (by norm_num)).const_mul
    (1 / (2 * π))
  have h := h1.add h2
  rw [mul_zero, mul_zero, add_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_gt_atTop 0] with t ht
  have := airyAi'_abs_le ht
  rw [Real.norm_eq_abs]
  refine this.trans (le_of_eq ?_)
  ring

theorem tendsto_airyAi_energy :
    Tendsto (fun x => x * airyAi x ^ 2 - airyAi' x ^ 2) atTop (𝓝 0) := by
  have h1 := (tendsto_sqrt_mul_airyAi).pow 2
  have h2 := (tendsto_airyAi').pow 2
  have h := h1.sub h2
  simp only [zero_pow two_ne_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [mul_pow, Real.sq_sqrt ht.le]

/-- `Ai²` is integrable on `[a, ∞)` and `∫_a^∞ Ai(t)² dt = Ai'(a)² - a Ai(a)²`. -/
theorem integral_Ioi_airyAi_sq (a : ℝ) :
    ∫ t in Ioi a, airyAi t ^ 2 = airyAi' a ^ 2 - a * airyAi a ^ 2 := by
  have := integral_Ioi_of_hasDerivAt_of_nonneg' (a := a)
    (g := fun x => x * airyAi x ^ 2 - airyAi' x ^ 2) (g' := fun x => airyAi x ^ 2)
    (fun x _ => isAirySol_airyAi.hasDerivAt_energy x) (fun _ _ => sq_nonneg _)
    tendsto_airyAi_energy
  rw [this]; ring

theorem integrableOn_Ioi_airyAi_sq (a : ℝ) : IntegrableOn (fun t => airyAi t ^ 2) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (a := a)
    (g := fun x => x * airyAi x ^ 2 - airyAi' x ^ 2) (g' := fun x => airyAi x ^ 2)
    (fun x _ => isAirySol_airyAi.hasDerivAt_energy x) (fun _ _ => sq_nonneg _)
    tendsto_airyAi_energy

end FormalResearch.Special
