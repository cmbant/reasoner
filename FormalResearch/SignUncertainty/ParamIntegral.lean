module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.MeasureTheory.Function.AEMeasurableSequence

/-!
# Locally uniform convergence of parametric integrals

If `F k s v → Flim s₀ v` jointly as `(k, s) → (∞, s₀)`, the integrands are locally uniformly dominated by an
integrable function, and `s ↦ ∫ Flim s v` is continuous, then `s ↦ ∫ F k s v` converges to it locally uniformly
(`tendstoLocallyUniformly_integral`).
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set

namespace FormalResearch.SignUncertainty

theorem tendstoLocallyUniformly_integral {F : ℕ → ℝ → ℝ → ℂ} {Flim : ℝ → ℝ → ℂ}
    (hmeas : ∀ s₀ : ℝ, ∀ᶠ y in (atTop ×ˢ 𝓝 s₀ : Filter (ℕ × ℝ)), AEStronglyMeasurable (F y.1 y.2) volume)
    (hbound : ∀ s₀ : ℝ, ∃ bound : ℝ → ℝ, Integrable bound ∧ ∃ N : ℕ, ∃ r : ℝ, 0 < r ∧
      ∀ k ≥ N, ∀ s, |s - s₀| < r → ∀ v, ‖F k s v‖ ≤ bound v)
    (hlim : ∀ s₀ v, Tendsto (fun p : ℕ × ℝ => F p.1 p.2 v) (atTop ×ˢ 𝓝 s₀) (𝓝 (Flim s₀ v)))
    (hcont : Continuous fun s => ∫ v, Flim s v) :
    TendstoLocallyUniformly (fun k s => ∫ v, F k s v) (fun s => ∫ v, Flim s v) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro s₀
  rw [tendsto_uniformity_iff_dist_tendsto_zero]
  obtain ⟨bound, hbi, N, r, hr, hb⟩ := hbound s₀
  have h1 : Tendsto (fun y : ℕ × ℝ => ∫ v, F y.1 y.2 v) (atTop ×ˢ 𝓝 s₀) (𝓝 (∫ v, Flim s₀ v)) := by
    refine tendsto_integral_filter_of_dominated_convergence bound
      (hmeas s₀) ?_ hbi (Eventually.of_forall fun v => hlim s₀ v)
    have : ∀ᶠ y in (atTop ×ˢ 𝓝 s₀ : Filter (ℕ × ℝ)), y.1 ≥ N ∧ |y.2 - s₀| < r :=
      (tendsto_fst.eventually (eventually_ge_atTop N)).and
        (tendsto_snd.eventually (by
          filter_upwards [Metric.ball_mem_nhds s₀ hr] with y hy
          simpa [Real.dist_eq] using hy))
    filter_upwards [this] with y hy
    exact Eventually.of_forall fun v => hb y.1 hy.1 y.2 hy.2 v
  have h2 : Tendsto (fun y : ℕ × ℝ => ∫ v, Flim y.2 v) (atTop ×ˢ 𝓝 s₀) (𝓝 (∫ v, Flim s₀ v)) :=
    (hcont.continuousAt.tendsto).comp tendsto_snd
  have h3 := (tendsto_iff_dist_tendsto_zero.mp (h2.sub h1))
  have h4 : Tendsto (fun y : ℕ × ℝ => dist (∫ v, Flim y.2 v) (∫ v, F y.1 y.2 v)) (atTop ×ˢ 𝓝 s₀) (𝓝 0) := by
    have := (tendsto_iff_dist_tendsto_zero.mp h2).add (tendsto_iff_dist_tendsto_zero.mp h1)
    simp only [add_zero] at this
    refine squeeze_zero (fun y => dist_nonneg) (fun y => dist_triangle_right _ _ _) this
  exact h4

/-- Continuity of the limit integral, from the same domination. -/
theorem continuous_integral_lim {F : ℕ → ℝ → ℝ → ℂ} {Flim : ℝ → ℝ → ℂ}
    (hmeas : ∀ s₀ : ℝ, ∀ᶠ y in (atTop ×ˢ 𝓝 s₀ : Filter (ℕ × ℝ)), AEStronglyMeasurable (F y.1 y.2) volume)
    (hbound : ∀ s₀ : ℝ, ∃ bound : ℝ → ℝ, Integrable bound ∧ ∃ N : ℕ, ∃ r : ℝ, 0 < r ∧
      ∀ k ≥ N, ∀ s, |s - s₀| < r → ∀ v, ‖F k s v‖ ≤ bound v)
    (hlim : ∀ s₀ v, Tendsto (fun p : ℕ × ℝ => F p.1 p.2 v) (atTop ×ˢ 𝓝 s₀) (𝓝 (Flim s₀ v)))
    (hcv : ∀ v, Continuous fun s => Flim s v) :
    Continuous fun s => ∫ v, Flim s v := by
  refine continuous_iff_continuousAt.mpr fun s₀ => ?_
  obtain ⟨bound, hbi, N, r, hr, hb⟩ := hbound s₀
  have hlim' : ∀ s v, Tendsto (fun k : ℕ => F k s v) atTop (𝓝 (Flim s v)) := by
    intro s v
    have htp : Tendsto (fun k : ℕ => (k, s)) atTop (atTop ×ˢ 𝓝 s) :=
      Filter.Tendsto.prodMk tendsto_id tendsto_const_nhds
    exact (hlim s v).comp htp
  have hbd : ∀ s, |s - s₀| < r → ∀ v, ‖Flim s v‖ ≤ bound v := by
    intro s hs v
    refine le_of_tendsto (hlim' s v).norm ?_
    filter_upwards [eventually_ge_atTop N] with k hk
    exact hb k hk s hs v
  have hnear : ∀ᶠ s in 𝓝 s₀, |s - s₀| < r := by
    filter_upwards [Metric.ball_mem_nhds s₀ hr] with s hs
    simpa [Real.dist_eq] using hs
  refine continuousAt_of_dominated (bound := bound) ?_ ?_ hbi (Eventually.of_forall fun v => (hcv v).continuousAt)
  · filter_upwards [hnear] with s hs
    -- measurability of the limit, from the eventual measurability of `F · s`
    have hmeas' : ∀ᶠ k in atTop, AEStronglyMeasurable (F k s) volume := by
      have := (hmeas s)
      have htp : Tendsto (fun k : ℕ => (k, s)) atTop (atTop ×ˢ 𝓝 s) :=
        Filter.Tendsto.prodMk tendsto_id tendsto_const_nhds
      exact htp.eventually this
    obtain ⟨N', hN'⟩ := eventually_atTop.mp hmeas'
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun k => F (k + N') s) (g := Flim s)
      (fun k => hN' _ (by omega)) (Eventually.of_forall fun v => ?_)
    exact (hlim' s v).comp (tendsto_add_atTop_nat N')
  · filter_upwards [hnear] with s hs
    exact Eventually.of_forall fun v => hbd s hs v

/-- info: 'FormalResearch.SignUncertainty.tendstoLocallyUniformly_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendstoLocallyUniformly_integral

/-- info: 'FormalResearch.SignUncertainty.continuous_integral_lim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuous_integral_lim

end FormalResearch.SignUncertainty
