module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Holomorphy of parameter integrals (support for `ct:outer`)

Generic complex analysis, no paper content.  **Proved.**

`FormalResearch.SignUncertainty.CtOuter.differentiableOn_integral_param`: let `Φ : ℂ → α → ℂ` be such
that `w ↦ Φ w t` is holomorphic on an open set `U` for almost every `t`, `Φ w` is a.e. strongly
measurable for `w ∈ U`, and near every point of `U` the family is dominated by one integrable function.
Then `w ↦ ∫ Φ w t ∂μ` is holomorphic on `U`.  The derivative of the integrand is bounded by Cauchy's
estimate, then differentiation under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
gives the derivative.  This is used for the strip integral `h` of `ct:outer`, its far part, and the
analytic kernel pieces of the local continuation across the strip edge.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set

namespace FormalResearch.SignUncertainty.CtOuter

/-- **Derivative of a dominated parameter integral** (differentiation under the integral sign for a holomorphic
integrand): the derivative is the integral of the `w`-derivative. -/
theorem hasDerivAt_integral_param {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Φ : ℂ → α → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hmeas : ∀ w ∈ U, AEStronglyMeasurable (Φ w) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => Φ w t) U)
    (hloc : ∀ w₀ ∈ U, ∃ r > 0, ∃ b : α → ℝ, Integrable b μ ∧
      ∀ᵐ t ∂μ, ∀ w ∈ ball w₀ r, ‖Φ w t‖ ≤ b t) {w₀ : ℂ} (hw₀ : w₀ ∈ U) :
    HasDerivAt (fun w => ∫ t, Φ w t ∂μ) (∫ t, deriv (fun z => Φ z t) w₀ ∂μ) w₀ := by
  obtain ⟨r₀, hr₀, b, hb, hbd⟩ := hloc w₀ hw₀
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  set r : ℝ := min r₀ r₁ with hr
  have hrpos : 0 < r := lt_min hr₀ hr₁
  have hrU : ball w₀ r ⊆ U := fun z hz => hball (ball_subset_ball (min_le_right _ _) hz)
  have hr2 : (0 : ℝ) < r / 2 := by positivity
  -- Cauchy estimate: derivative bound on `ball w₀ (r/2)`
  have hder : ∀ᵐ t ∂μ, ∀ w ∈ ball w₀ (r / 2), ‖deriv (fun z => Φ z t) w‖ ≤ b t / (r / 2) := by
    filter_upwards [hdiff, hbd] with t ht hbt w hw
    have hsub : closedBall w (r / 2) ⊆ ball w₀ r := by
      intro z hz
      rw [mem_ball] at hw ⊢
      rw [mem_closedBall] at hz
      calc dist z w₀ ≤ dist z w + dist w w₀ := dist_triangle _ _ _
        _ < r / 2 + r / 2 := add_lt_add_of_le_of_lt hz hw
        _ = r := by ring
    have hd : DiffContOnCl ℂ (fun z => Φ z t) (ball w (r / 2)) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball w hr2.ne']
      exact (ht.mono (hsub.trans hrU))
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr2 hd ?_
    intro z hz
    exact hbt z (ball_subset_ball (min_le_left _ _) (hsub (sphere_subset_closedBall hz)))
  have hFmeas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (Φ w) μ := by
    filter_upwards [hU.mem_nhds hw₀] with w hw using hmeas w hw
  have hFint : Integrable (Φ w₀) μ := by
    refine Integrable.mono' hb (hmeas w₀ hw₀) ?_
    filter_upwards [hbd] with t ht using ht w₀ (mem_ball_self hr₀)
  -- measurability of the derivative at `w₀` as a limit of difference quotients
  have hF'meas : AEStronglyMeasurable (fun t => deriv (fun z => Φ z t) w₀) μ := by
    let ε : ℕ → ℝ := fun n => r / (2 * ((n : ℝ) + 2))
    have hεpos : ∀ n, 0 < ε n := fun n => by positivity
    have hεlt : ∀ n, ε n < r := fun n => by
      have : (1 : ℝ) < 2 * ((n : ℝ) + 2) := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      calc ε n = r / (2 * ((n : ℝ) + 2)) := rfl
        _ < r / 1 := by gcongr
        _ = r := by ring
    have hεtend : Tendsto ε atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 2))) atTop atTop := by
        refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      exact this.const_div_atTop r
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n t => ((ε n : ℂ))⁻¹ * (Φ (w₀ + (ε n : ℂ)) t - Φ w₀ t)) ?_ ?_
    · intro n
      have h1 : w₀ + (ε n : ℂ) ∈ U := by
        apply hrU
        rw [mem_ball, dist_eq_norm]
        simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (hεpos n)]
        exact hεlt n
      exact ((hmeas _ h1).sub (hmeas _ hw₀)).const_mul _
    · filter_upwards [hdiff] with t ht
      have hda : HasDerivAt (fun z => Φ z t) (deriv (fun z => Φ z t) w₀) w₀ :=
        ((ht w₀ hw₀).differentiableAt (hU.mem_nhds hw₀)).hasDerivAt
      have := (hasDerivAt_iff_tendsto_slope_zero.mp hda)
      have hε' : Tendsto (fun n => (ε n : ℂ)) atTop (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · exact (Complex.continuous_ofReal.tendsto 0).comp hεtend |>.congr (fun n => rfl) |>.trans
            (by simp)
        · exact Eventually.of_forall (fun n => by
            simpa using (hεpos n).ne')
      exact this.comp hε' |>.congr (fun n => by simp [Function.comp])
  have hdominated := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (F := fun w t => Φ w t) (μ := μ) (x₀ := w₀) (s := ball w₀ (r / 2))
    (bound := fun t => b t / (r / 2)) (F' := fun w t => deriv (fun z => Φ z t) w)
    (ball_mem_nhds w₀ hr2) hFmeas hFint hF'meas
    (by
      filter_upwards [hder] with t ht w hw using ht w hw)
    (hb.div_const _)
    (by
      filter_upwards [hdiff] with t ht w hw
      have hwU : w ∈ U := hrU (ball_subset_ball (by linarith) hw)
      exact ((ht w hwU).differentiableAt (hU.mem_nhds hwU)).hasDerivAt)
  exact hdominated.2

/-- **Holomorphy of a dominated parameter integral.** -/
theorem differentiableOn_integral_param {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Φ : ℂ → α → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hmeas : ∀ w ∈ U, AEStronglyMeasurable (Φ w) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => Φ w t) U)
    (hloc : ∀ w₀ ∈ U, ∃ r > 0, ∃ b : α → ℝ, Integrable b μ ∧
      ∀ᵐ t ∂μ, ∀ w ∈ ball w₀ r, ‖Φ w t‖ ≤ b t) :
    DifferentiableOn ℂ (fun w => ∫ t, Φ w t ∂μ) U := fun _ hw₀ =>
  (hasDerivAt_integral_param hU hmeas hdiff hloc hw₀).differentiableAt.differentiableWithinAt

end FormalResearch.SignUncertainty.CtOuter
