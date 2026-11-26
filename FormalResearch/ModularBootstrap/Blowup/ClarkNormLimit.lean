module

public import FormalResearch.ModularBootstrap.Blowup.AiryNormLimit
public import FormalResearch.SignUncertainty.ClarkTwoNode

/-!
# `bl:norm` at `m₀ = 2` (Clark level), transported-density form

Source: `CFT/modular_bootstrap/paper/blowup_limit.tex`, Lemma BL-N (`bl:norm`) at the Clark pair
`(P, Q_HB) = (cos α, -sin α)`, `N = ψ_α`, `m₀ = 2`, one prescribed node `z₁(α)`, terminal node
`z₂(α)`, `G_N = g_α`.

The Clark extremal `clarkExtremal α` obeys the equality principle of `NormLimitIdentify`
(`clark_two_node_equality_iff`), with one prescribed node `z₁(α)` and terminal node `z₂(α)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Blowup

open FormalResearch.Special FormalResearch.SignUncertainty

variable {α : ℝ}

/-- The Clark extremal is an extremal profile. -/
theorem clarkExtremalProfile (hα : Real.sin α ≠ 0) : ExtremalProfile (clarkExtremal α) where
  diff := differentiable_clarkExtremal α
  integrable := clarkExtremal_integrable hα
  real := (clarkExtremal_attains hα).2.2.2.1
  mass_pos := by
    refine integral_norm_pos_of_ne_zero (differentiable_clarkExtremal α)
      (clarkExtremal_integrable hα) (x₀ := airyZero 2) ?_
    intro h0
    have := clarkExtremal_pos_at_airyZero_two hα
    rw [h0] at this
    simp at this
  integral_re := (clarkExtremal_attains hα).2.2.2.2.2.2.2.2.2.1

/-- Equality principle at the Clark nodes. -/
theorem clarkEqualityPrinciple (hα : Real.sin α ≠ 0) :
    EqualityPrinciple (κ := Unit) (clarkExtremal α) (clarkNode α 2) (fun _ => clarkNode α 1) := by
  intro Φ hd hi hb hreal hpos hnode hint hne
  exact (clark_two_node_equality_iff hα).mp
    ⟨hd, hi, hb, hreal, hint, hnode (), hpos, hne⟩

/-- The Clark extremal is negative just to the right of `z₂(α)`. -/
theorem clarkExtremal_neg_right (hα : Real.sin α ≠ 0) : ∀ ε : ℝ, 0 < ε →
    ∃ x : ℝ, clarkNode α 2 < x ∧ x ≤ clarkNode α 2 + ε ∧ (clarkExtremal α (x : ℂ)).re < 0 := by
  intro ε hε
  have hgap : clarkNode α 2 < clarkNode α 1 := clarkNode_two_lt_one α
  set x : ℝ := clarkNode α 2 + min ε ((clarkNode α 1 - clarkNode α 2) / 2) with hx
  have hmin_pos : 0 < min ε ((clarkNode α 1 - clarkNode α 2) / 2) :=
    lt_min hε (by linarith)
  refine ⟨x, by linarith, by have := min_le_left ε ((clarkNode α 1 - clarkNode α 2) / 2); linarith, ?_⟩
  refine (clarkExtremal_attains hα).2.2.2.2.2.2.2.1 x (by linarith) ?_
  have := min_le_right ε ((clarkNode α 1 - clarkNode α 2) / 2)
  linarith

/-- The normalised Clark profile `g_α / ‖g_α‖₁`. -/
noncomputable abbrev clarkProfile (α : ℝ) : ℂ → ℂ := normProfile (clarkExtremal α)

variable {C₀ : ℝ} {R ς δ : ℕ → ℝ} {Ψ : ℕ → ℂ → ℂ} {uT : ℕ → ℝ}

/-- The prescribed node data: points `ũ_n → z₁(α)` with `Re Ψ_n(ũ_n) ≥ 0`. -/
def ClarkNodeData (α : ℝ) (Ψ : ℕ → ℂ → ℂ) : Prop :=
  ∃ ũ : ℕ → ℝ, Tendsto ũ atTop (𝓝 (clarkNode α 1)) ∧ ∀ n, 0 ≤ (Ψ n (ũ n : ℂ)).re

/-- **`bl:norm`(a), `m₀ = 2`**: `limsup uT_n ≤ z₂(α)`. -/
theorem clark_threshold_le (hα : Real.sin α ≠ 0) (S : DensitySeq C₀ R ς δ Ψ uT)
    (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n) (hn : ClarkNodeData α Ψ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, uT n ≤ clarkNode α 2 + ε :=
  threshold_le_of_negative S hbd (clarkExtremalProfile hα) (clarkEqualityPrinciple hα)
    (fun _ => hn) (clarkExtremal_neg_right hα) ε hε

/-- **`bl:norm`(b), `m₀ = 2`**: locally uniform convergence to the normalised Clark profile. -/
theorem clark_norm_limit (hα : Real.sin α ≠ 0) (S : DensitySeq C₀ R ς δ Ψ uT)
    (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n) (hn : ClarkNodeData α Ψ)
    (huT : ∀ x < clarkNode α 2, ∀ᶠ n in atTop, x ≤ uT n) :
    LocUnif Ψ id (clarkProfile α) :=
  norm_limit S hbd (clarkExtremalProfile hα) (clarkEqualityPrinciple hα) huT (fun _ => hn)

/-- Locally uniform convergence of the first derivatives. -/
theorem clark_norm_limit_deriv (hα : Real.sin α ≠ 0) (S : DensitySeq C₀ R ς δ Ψ uT)
    (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n) (hn : ClarkNodeData α Ψ)
    (huT : ∀ x < clarkNode α 2, ∀ᶠ n in atTop, x ≤ uT n) (m : ℕ) :
    TendstoLocallyUniformlyOn (fun n => deriv (Ψ n)) (deriv (clarkProfile α)) atTop
      (ball (0 : ℂ) ((m : ℝ) + 1)) :=
  norm_limit_deriv S hbd (clarkExtremalProfile hα) (clarkEqualityPrinciple hα) huT (fun _ => hn) m

/-- `L¹(ℝ)` convergence of the densities extended by zero. -/
theorem clark_norm_limit_l1 (hα : Real.sin α ≠ 0) (S : DensitySeq C₀ R ς δ Ψ uT)
    (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n) (hn : ClarkNodeData α Ψ)
    (huT : ∀ x < clarkNode α 2, ∀ᶠ n in atTop, x ≤ uT n) :
    Tendsto (fun n => ∫ x : ℝ, ‖(Icc (-(R n)) (R n)).indicator (fun x : ℝ => Ψ n (x : ℂ)) x -
      clarkProfile α (x : ℂ)‖) atTop (𝓝 0) :=
  norm_limit_l1 S hbd (clarkExtremalProfile hα) (clarkEqualityPrinciple hα) huT (fun _ => hn)

/-- The truncated total mass tends to `0`. -/
theorem clark_norm_limit_integral (hα : Real.sin α ≠ 0) (S : DensitySeq C₀ R ς δ Ψ uT)
    (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n) (hn : ClarkNodeData α Ψ)
    (huT : ∀ x < clarkNode α 2, ∀ᶠ n in atTop, x ≤ uT n) :
    Tendsto (fun n => ∫ x in (-(R n))..(R n), (Ψ n (x : ℂ)).re) atTop (𝓝 0) :=
  norm_limit_integral_re S hbd (clarkExtremalProfile hα) (clarkEqualityPrinciple hα) huT
    (fun _ => hn)

/-- The thresholds converge to `z₂(α)` once `liminf uT_n ≥ z₂(α)`. -/
theorem clark_threshold_tendsto (hα : Real.sin α ≠ 0) (S : DensitySeq C₀ R ς δ Ψ uT)
    (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n) (hn : ClarkNodeData α Ψ)
    (huT : ∀ x < clarkNode α 2, ∀ᶠ n in atTop, x ≤ uT n) :
    Tendsto uT atTop (𝓝 (clarkNode α 2)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [clark_threshold_le hα S hbd hn (ε / 2) (half_pos hε),
    huT (clarkNode α 2 - ε / 2) (by linarith)] with n h1 h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- info: 'FormalResearch.ModularBootstrap.Blowup.clark_norm_limit_l1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_norm_limit_l1

/-- info: 'FormalResearch.ModularBootstrap.Blowup.clark_threshold_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_threshold_le

end FormalResearch.ModularBootstrap.Blowup
