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
* `blowupPullback`: the hypotheses of the Clark theorem for `f` (`local_pullback_setup` of
  `Rigidity/AiryRigidity.lean` for an arbitrary threshold, which is private there).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty

lemma blowupPullback_bound {Φ : ℂ → ℂ} {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ s : ℂ, ‖Φ s‖ ≤ C * (1 + ‖s‖) ^ ν * airyEnv (-(betaTip : ℂ) * s)) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ u : ℂ, ‖Φ (-u / (betaTip : ℂ))‖ ≤ C' * (1 + ‖u‖) ^ |ν| * airyEnv u := by
  let K : ℝ := max 1 betaTip⁻¹
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C * K ^ |ν|, by positivity, fun u => ?_⟩
  have hbu := hb (-u / (betaTip : ℂ))
  have hb0 : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
  rw [show -(betaTip : ℂ) * (-u / (betaTip : ℂ)) = u by field_simp] at hbu
  have hnorm_s : ‖-u / (betaTip : ℂ)‖ = ‖u‖ * betaTip⁻¹ := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos betaTip_pos, div_eq_mul_inv]
  have hlin : 1 + ‖-u / (betaTip : ℂ)‖ ≤ K * (1 + ‖u‖) := by
    rw [hnorm_s]; have : betaTip⁻¹ ≤ K := le_max_right _ _; nlinarith [norm_nonneg u, le_max_left 1 betaTip⁻¹]
  have hp : (1 + ‖-u / (betaTip : ℂ)‖) ^ ν ≤ K ^ |ν| * (1 + ‖u‖) ^ |ν| :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg (-u / (betaTip : ℂ))]) (le_abs_self ν)).trans
      ((Real.rpow_le_rpow (by linarith [norm_nonneg (-u / (betaTip : ℂ))]) hlin (abs_nonneg ν)).trans_eq
        (Real.mul_rpow hKpos.le (by linarith [norm_nonneg u])))
  calc ‖Φ (-u / (betaTip : ℂ))‖ ≤ C * (1 + ‖-u / (betaTip : ℂ)‖) ^ ν * airyEnv u := hbu
    _ ≤ C * (K ^ |ν| * (1 + ‖u‖) ^ |ν|) * airyEnv u := by gcongr; exact (airyEnv_pos u).le
    _ = (C * K ^ |ν|) * (1 + ‖u‖) ^ |ν| * airyEnv u := by ring

/-- The hypotheses of the Clark two-node theorem for `f(u) = Ψ(-u/β)`, with `u₂ = -β y`. -/
lemma blowupPullback {Ψ : ℂ → ℂ} {C ν : ℝ}
    (hΨ_diff : Differentiable ℂ Ψ) (hΨ_int : Integrable (fun s : ℝ => Ψ (s : ℂ)))
    (hC : 0 ≤ C) (hb : ∀ s : ℂ, ‖Ψ s‖ ≤ C * (1 + ‖s‖) ^ ν * airyEnv (-(betaTip : ℂ) * s))
    (hΨ_real : ∀ s : ℝ, (Ψ (s : ℂ)).im = 0) {y : ℝ}
    (hΨ_nonneg : ∀ s : ℝ, y ≤ s → 0 ≤ (Ψ (s : ℂ)).re)
    (hΨ_int_le : (∫ s : ℝ, (Ψ (s : ℂ)).re) ≤ 0) (hΨ_ne : ∃ z : ℂ, Ψ z ≠ 0) :
    let f : ℂ → ℂ := fun u => Ψ (-u / (betaTip : ℂ))
    Differentiable ℂ f ∧ Integrable (fun u : ℝ => f (u : ℂ)) ∧
      (∃ C' : ℝ, 0 ≤ C' ∧ ∀ u : ℂ, ‖f u‖ ≤ C' * (1 + ‖u‖) ^ |ν| * airyEnv u) ∧
      (∀ u : ℝ, (f (u : ℂ)).im = 0) ∧
      (∀ u : ℝ, u ≤ -betaTip * y → 0 ≤ (f (u : ℂ)).re) ∧
      (∫ u : ℝ, (f (u : ℂ)).re) ≤ 0 ∧ (∃ w : ℂ, f w ≠ 0) := by
  intro f
  have hfc : ∀ u : ℝ, f (u : ℂ) = Ψ (((-betaTip⁻¹ * u : ℝ) : ℂ)) := fun u => by
    dsimp [f]; push_cast; ring_nf
  obtain ⟨C', hC', hb'⟩ := blowupPullback_bound hC hb
  obtain ⟨z, hz⟩ := hΨ_ne
  refine ⟨hΨ_diff.comp ((differentiable_id.neg).div_const _), ?_, ⟨C', hC', hb'⟩,
    fun u => by rw [hfc]; exact hΨ_real _, fun u hu => ?_, ?_, ⟨-(betaTip : ℂ) * z, ?_⟩⟩
  · simp_rw [hfc]; exact hΨ_int.comp_mul_left' (neg_ne_zero.mpr (inv_ne_zero betaTip_pos.ne'))
  · rw [hfc]; apply hΨ_nonneg
    have h1 := mul_le_mul_of_nonneg_left hu (inv_pos.mpr betaTip_pos).le
    rw [show betaTip⁻¹ * (-betaTip * y) = -y by field_simp [betaTip_pos.ne']] at h1
    linarith
  · have hcomp : ∫ u : ℝ, (f (u : ℂ)).re = betaTip * ∫ s : ℝ, (Ψ (s : ℂ)).re := by
      simp_rw [hfc]
      rw [Measure.integral_comp_mul_left (fun s : ℝ => (Ψ (s : ℂ)).re) (-betaTip⁻¹)]
      simp only [abs_neg, abs_inv, abs_of_pos betaTip_pos, inv_inv, smul_eq_mul]
    rw [hcomp]; exact mul_nonpos_of_nonneg_of_nonpos betaTip_pos.le hΨ_int_le
  · dsimp [f]; have hb0 : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
    rwa [show -(-(betaTip : ℂ) * z) / (betaTip : ℂ) = z by field_simp]

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
    blowupPullback hΨd hΨi hC hb hreal hnn hint hne
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
