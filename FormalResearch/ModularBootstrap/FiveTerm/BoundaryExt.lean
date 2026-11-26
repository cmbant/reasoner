module

public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Boundary extension by limits (FIVE-0 tool)

If `f` has a limit along `𝓝[U] z` at every `z ∈ closure U ∖ bad`, then the extension
`extLim U f z := limUnder (𝓝[U] z) f` is continuous on `closure U ∖ bad`, and agrees with `f` at the points
of `U` where `f` is continuous within `U`.  Generic, no hypothesis on `U`.
-/

@[expose] public section

open Filter Topology Set Metric

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The extension of `f : ℂ → ℂ` from `U` by limits. -/
noncomputable def extLim (U : Set ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ := limUnder (𝓝[U] z) f

lemma tendsto_extLim {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ} (h : ∃ L, Tendsto f (𝓝[U] z) (𝓝 L)) :
    Tendsto f (𝓝[U] z) (𝓝 (extLim U f z)) :=
  tendsto_nhds_limUnder h

lemma extLim_eq_of_tendsto {U : Set ℂ} {f : ℂ → ℂ} {z L : ℂ} (hz : z ∈ closure U)
    (h : Tendsto f (𝓝[U] z) (𝓝 L)) : extLim U f z = L := by
  have : NeBot (𝓝[U] z) := mem_closure_iff_nhdsWithin_neBot.mp hz
  exact h.limUnder_eq

lemma extLim_of_mem {U : Set ℂ} {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ U) (hf : ContinuousWithinAt f U z) :
    extLim U f z = f z :=
  extLim_eq_of_tendsto (subset_closure hz) hf

/-- Continuity of the extension on `closure U ∖ bad`. -/
lemma continuousOn_extLim {U : Set ℂ} {f : ℂ → ℂ} {bad : Set ℂ}
    (h : ∀ z ∈ closure U \ bad, ∃ L, Tendsto f (𝓝[U] z) (𝓝 L)) :
    ContinuousOn (extLim U f) (closure U \ bad) := by
  intro z₀ hz₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hlim := tendsto_extLim (h z₀ hz₀)
  have hev : ∀ᶠ w in 𝓝[U] z₀, dist (f w) (extLim U f z₀) < ε / 2 :=
    (Metric.tendsto_nhds.mp hlim) (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨δ, hδ, fun z' hz' hd => ?_⟩
  have hz'cl : z' ∈ closure U := hz'.1
  have : NeBot (𝓝[U] z') := mem_closure_iff_nhdsWithin_neBot.mp hz'cl
  have hlim' := tendsto_extLim (h z' hz')
  have hball : ball z₀ δ ∈ 𝓝 z' := Metric.isOpen_ball.mem_nhds (by simpa [dist_comm] using hd)
  have hev' : ∀ᶠ w in 𝓝[U] z', dist (f w) (extLim U f z₀) < ε / 2 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with w hw hwU
    exact hsub ⟨hw, hwU⟩
  have hclosed : IsClosed {x : ℂ | dist x (extLim U f z₀) ≤ ε / 2} :=
    isClosed_le (continuous_id.dist continuous_const) continuous_const
  have := hclosed.mem_of_tendsto hlim' (hev'.mono fun w hw => le_of_lt hw)
  simp only [Set.mem_ofPred_eq] at this
  linarith

end FormalResearch.ModularBootstrap.FiveTerm
