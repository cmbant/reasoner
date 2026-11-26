module

public import FormalResearch.ModularBootstrap.Crossing.Setup
public import FormalResearch.ModularBootstrap.Upper.Membership.RadialFourier

/-!
# Hankel-oddness passes to `L¹(t^{w-1} dt)` limits

If `g_j ∈ Ā_w` converge pointwise on `[0, ∞)` and in `L¹((0, ∞), t^{w-1} dt)` to a `G` whose radial
lift is integrable, then `𝓕 (radialLift G) = -(radialLift G)`.  This is the step
"`ℋ_w g_j = -g_j → -g_*` pointwise, hence `ℋ_w g_* = -g_*`" of the proof of `ds:primal`
(`dual_spectrum_limit.tex`), done on the radial lift instead of through the Bessel kernel: the
Fourier transform is a contraction `L¹ → L^∞`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.ModularBootstrap.Crossing

theorem radialLift_fourier_odd_of_limit {w : ℕ} (hw : 1 ≤ w) {g : ℕ → ℝ → ℝ} {G : ℝ → ℝ}
    (hgi : ∀ j, Integrable (radialLift w (g j)))
    (hodd : ∀ j, 𝓕 (radialLift w (g j)) = -radialLift w (g j))
    (hGi : Integrable (radialLift w G))
    (hlim : Tendsto (fun j => ∫ t in Ioi (0 : ℝ), t ^ (w - 1) * |g j t - G t|) atTop (𝓝 0))
    (hpt : ∀ t : ℝ, 0 ≤ t → Tendsto (fun j => g j t) atTop (𝓝 (G t))) :
    𝓕 (radialLift w G) = -(radialLift w G) := by
  funext x
  set C : ℝ := (2 * π) ^ w / ((w - 1).factorial : ℝ) with hC
  have hC0 : 0 ≤ C := by positivity
  have hbound : ∀ j, ‖𝓕 (radialLift w G) x + radialLift w G x‖ ≤
      C * (∫ t in Ioi (0 : ℝ), t ^ (w - 1) * |g j t - G t|) +
        |g j (‖x‖ ^ 2 / 2) - G (‖x‖ ^ 2 / 2)| := fun j => by
    have hsub := Upper.Membership.fourier_sub_fn (hGi) (hgi j)
    have h1 : 𝓕 (radialLift w G) x - 𝓕 (radialLift w (g j)) x =
        𝓕 (fun v => radialLift w G v - radialLift w (g j) v) x := by
      rw [hsub]; rfl
    have h2 : 𝓕 (radialLift w G) x + radialLift w G x =
        𝓕 (fun v => radialLift w G v - radialLift w (g j) v) x +
          (radialLift w G x - radialLift w (g j) x) := by
      have := congrFun (hodd j) x
      simp only [Pi.neg_apply] at this
      rw [← h1]
      linear_combination this
    rw [h2]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Real.norm_fourier_le_integral_norm _ x).trans (le_of_eq ?_)
      have : ∀ v : EuclideanSpace ℝ (Fin (2 * w)),
          ‖radialLift w G v - radialLift w (g j) v‖ = |G (‖v‖ ^ 2 / 2) - g j (‖v‖ ^ 2 / 2)| := by
        intro v
        simp only [radialLift]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simp_rw [this]
      rw [integral_radialLiftReal hw (fun s => |G s - g j s|)]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [abs_sub_comm]
    · simp only [radialLift]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have h3 : Tendsto (fun j => |g j (‖x‖ ^ 2 / 2) - G (‖x‖ ^ 2 / 2)|) atTop (𝓝 0) := by
    have := (hpt (‖x‖ ^ 2 / 2) (by positivity)).sub_const (G (‖x‖ ^ 2 / 2))
    simpa using this.abs
  have hconv : Tendsto (fun j => C * (∫ t in Ioi (0 : ℝ), t ^ (w - 1) * |g j t - G t|) +
      |g j (‖x‖ ^ 2 / 2) - G (‖x‖ ^ 2 / 2)|) atTop (𝓝 0) := by
    simpa using (hlim.const_mul C).add h3
  have hle : ‖𝓕 (radialLift w G) x + radialLift w G x‖ ≤ 0 := by
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds hconv fun j => ?_
    simpa using hbound j
  have h0 : 𝓕 (radialLift w G) x + radialLift w G x = 0 := norm_le_zero_iff.1 hle
  simpa using eq_neg_of_add_eq_zero_left h0

end FormalResearch.ModularBootstrap.Crossing
