module

public import FormalResearch.ModularBootstrap.Rigidity.AiryRigidity
public import FormalResearch.ModularBootstrap.TwoLevel.A2StarCurve

/-!
# The Clark two-node theorem for a blow-up limit (`virasoro_two_level.tex`, proof of Theorem 2.1)

Let `Ψ` be a limit of the blow-ups `Φ_j` (the output of Proposition T, in the `s`-variable
`u = -β s`) and `f(u) = Ψ(-u/β)`.  If `Ψ` is entire of Airy growth, integrable, real on `ℝ`, with
`∫ Ψ ≤ 0`, `Ψ ≥ 0` on `[y, ∞)` and `Ψ(s_1^*) ≥ 0` at the pinned point `s_1^* = -u₁/β`
(`u₁ > a₁`), then `f` satisfies the hypotheses of the Clark two-node theorem (`gt:1.2`) with
`u₂ = -β y`:

* `clark_of_blowup_limit`: `-β y ≤ z₂(α(u₁))`, and equality forces `Ψ(s) = c · g_α(-β s)`, `c > 0`;
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty

/-- **Clark two-node theorem for a blow-up limit** (`virasoro_two_level.tex`, Theorem 2.1, proof):
a limit `Ψ` of Airy growth with `Ψ ≥ 0` on `[y, ∞)`, `∫ Ψ ≤ 0` and `Ψ(-u₁/β) ≥ 0`
(`u₁ > a₁`) has `-β y ≤ z₂(α(u₁))`; equality forces `Ψ(s) = c · g_α(-β s)` with `c > 0`. -/
theorem clark_of_blowup_limit {Ψ : ℂ → ℂ} {C ν : ℝ}
    (hΨd : Differentiable ℂ Ψ) (hΨi : Integrable (fun s : ℝ => Ψ (s : ℂ)))
    (hC : 0 ≤ C) (hb : ∀ s : ℂ, ‖Ψ s‖ ≤ C * (1 + ‖s‖) ^ ν * airyEnv (-(betaTip : ℂ) * s))
    (hreal : ∀ s : ℝ, (Ψ (s : ℂ)).im = 0) {y : ℝ}
    (hnn : ∀ s : ℝ, y ≤ s → 0 ≤ (Ψ (s : ℂ)).re)
    (hint : (∫ s : ℝ, (Ψ (s : ℂ)).re) ≤ 0) (hne : ∃ z : ℂ, Ψ z ≠ 0)
    {u₁ : ℝ} (hu₁ : airyZero 1 < u₁) (hpin : 0 ≤ (Ψ ((-u₁ / betaTip : ℝ) : ℂ)).re) :
    -betaTip * y ≤ clarkNode (clarkAngle u₁) 2 ∧
    (-betaTip * y = clarkNode (clarkAngle u₁) 2 →
      ∃ c : ℝ, 0 < c ∧
        ∀ s : ℂ, Ψ s = (c : ℂ) * clarkExtremal (clarkAngle u₁) (-(betaTip : ℂ) * s)) := by
  obtain ⟨hfd, hfi, ⟨C', hC', hb'⟩, hfreal, hfnn, hfint, hfne⟩ :=
    local_pullback_setup hΨd hΨi hC hb hreal hnn hint hne
  have hα := sin_clarkAngle_ne_zero hu₁
  have hnode1 : clarkNode (clarkAngle u₁) 1 = u₁ := (clarkAngle_spec hu₁).2
  have hf1 : 0 ≤ ((fun u : ℂ => Ψ (-u / (betaTip : ℂ))) (clarkNode (clarkAngle u₁) 1 : ℂ)).re := by
    rw [hnode1]
    have : -(u₁ : ℂ) / (betaTip : ℂ) = ((-u₁ / betaTip : ℝ) : ℂ) := by push_cast; ring
    simp only [this]
    exact hpin
  have hfnn' : ∀ x : ℝ, x ≤ -betaTip * y →
      0 ≤ ((fun u : ℂ => Ψ (-u / (betaTip : ℂ))) (x : ℂ)).re := hfnn
  refine ⟨clark_two_node_uncertainty hα hfd hfi hC' hb' hfreal hfint hf1 hfnn' hfne, fun heq => ?_⟩
  have hf2 : ∀ x : ℝ, x ≤ clarkNode (clarkAngle u₁) 2 →
      0 ≤ ((fun u : ℂ => Ψ (-u / (betaTip : ℂ))) (x : ℂ)).re := fun x hx => hfnn' x (heq ▸ hx)
  obtain ⟨c, hc, hfc, -⟩ := clark_two_node_equality hα hfd hfi hC' hb' hfreal hfint hf1 hf2 hfne
  refine ⟨c, hc, fun s => ?_⟩
  have hb0 : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
  have h1 : Ψ (-(-(betaTip : ℂ) * s) / (betaTip : ℂ)) =
      (c : ℂ) * clarkExtremal (clarkAngle u₁) (-(betaTip : ℂ) * s) := hfc (-(betaTip : ℂ) * s)
  rwa [show -(-(betaTip : ℂ) * s) / (betaTip : ℂ) = s by field_simp] at h1

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.clark_of_blowup_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_of_blowup_limit

end FormalResearch.ModularBootstrap.TwoLevel
