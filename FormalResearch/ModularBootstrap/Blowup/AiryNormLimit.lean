module

public import FormalResearch.ModularBootstrap.Blowup.NormLimitIdentify
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1Airy

/-!
# `bl:norm` at `m₀ = 1` (Airy level), transported-density form

Source: `CFT/modular_bootstrap/paper/blowup_limit.tex`, Lemma BL-N (`bl:norm`) at `(P, Q_HB) = (1, 0)`,
`N = Ai`, `z₁ = a₁`, `G_Ai = Ai²/(a₁ - u)`, `‖G_Ai‖₁ = 2 L_*`.

The Airy extremal `airyExtremal` (`Ai²/(a₁ - u)`) obeys the equality principle of `NormLimitIdentify`
(Paper I's Theorem B equality, `airy_sign_equality`), so a sequence of transported densities with
the data of `DensityHyp` (holomorphy on the Langer disc, type-(II) envelope, `∫|F| ≤ 1`, left-lobe
mass `1/2 - δ`, truncated total mass `≤ δ`) converges to `airyExtremal / ‖airyExtremal‖₁` as soon as
the thresholds `uT_n → a₁`, locally uniformly with derivatives and in `L¹`; and the thresholds
always satisfy `limsup uT_n ≤ a₁` (part (a)).

* `airyProfile`: `airyExtremal / ‖airyExtremal‖₁`.
* `airy_threshold_le`: `∀ ε > 0, ∀ᶠ n, uT n ≤ a₁ + ε` (part (a) of `bl:norm`, `m₀ = 1`).
* `airy_norm_limit`, `airy_norm_limit_deriv`, `airy_norm_limit_l1`, `airy_norm_limit_integral`:
  part (b), `m₀ = 1`, under `uT_n → a₁` (only `liminf uT_n ≥ a₁` is used).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Blowup

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap

/-- Positivity of the `L¹` norm of a continuous integrable function with a nonzero value on `ℝ`. -/
lemma integral_norm_pos_of_ne_zero {G : ℂ → ℂ} (hd : Differentiable ℂ G)
    (hi : Integrable (fun x : ℝ => G (x : ℂ))) {x₀ : ℝ} (hx₀ : G (x₀ : ℂ) ≠ 0) :
    0 < ∫ x : ℝ, ‖G (x : ℂ)‖ := by
  have hcont : Continuous (fun x : ℝ => ‖G (x : ℂ)‖) := (hd.continuous.comp continuous_ofReal).norm
  have h_open : IsOpen (Function.support (fun x : ℝ => ‖G (x : ℂ)‖)) := by
    have heq : Function.support (fun x : ℝ => ‖G (x : ℂ)‖) = {x : ℝ | 0 < ‖G (x : ℂ)‖} := by
      ext x; simp [Function.mem_support, norm_pos_iff]
    rw [heq]; exact isOpen_lt continuous_const hcont
  have h_pos_meas : 0 < volume (Function.support (fun x : ℝ => ‖G (x : ℂ)‖)) :=
    h_open.measure_pos volume ⟨x₀, by simpa [Function.mem_support] using hx₀⟩
  exact (integral_pos_iff_support_of_nonneg (fun x => norm_nonneg _) hi.norm).mpr h_pos_meas

/-- The Airy extremal is an extremal profile. -/
theorem airyExtremalProfile : ExtremalProfile airyExtremal where
  diff := differentiable_airyExtremal
  integrable := airyExtremal_integrable
  real := airyExtremal_attains.2.2.2.1
  mass_pos := quantC1Mass_pos
  integral_re := airyExtremal_attains.2.2.2.2.2.1

/-- Equality principle at the Airy node (Paper I Theorem B equality). -/
theorem airyEqualityPrinciple : EqualityPrinciple (κ := Empty) airyExtremal (airyZero 1) Empty.elim := by
  intro Φ hd hi ⟨C, ν, hC, hb⟩ hreal hpos _ hint hne
  obtain ⟨c, hc, hΦ, -⟩ := airy_sign_equality hd hi hC hb hreal hpos hint hne
  exact ⟨-c, by linarith, hΦ⟩

/-- The extremal is negative just to the right of the node `a₁`. -/
theorem airyExtremal_neg_right : ∀ ε : ℝ, 0 < ε →
    ∃ x : ℝ, airyZero 1 < x ∧ x ≤ airyZero 1 + ε ∧ (airyExtremal (x : ℂ)).re < 0 := by
  intro ε hε
  refine ⟨airyZero 1 + ε, by linarith, le_rfl, ?_⟩
  rw [airyExtremal_re]
  have hAi : 0 < airyAi (airyZero 1 + ε) := airyAi_pos_of_gt_first (by linarith)
  have : 0 < airyAi (airyZero 1 + ε) ^ 2 / (airyZero 1 + ε - airyZero 1) :=
    div_pos (pow_pos hAi 2) (by linarith)
  linarith

/-- The `L¹` norm `‖airyExtremal‖₁` is `quantC1Mass`. -/
lemma profileMass_airyExtremal : profileMass airyExtremal = quantC1Mass := rfl

/-- The normalised Airy profile `Ai²/((a₁ - u) ‖·‖₁)` (so `‖airyProfile‖₁ = 1`). -/
noncomputable abbrev airyProfile : ℂ → ℂ := normProfile airyExtremal

variable {C₀ : ℝ} {R ς δ : ℕ → ℝ} {Ψ : ℕ → ℂ → ℂ} {uT : ℕ → ℝ}

/-- **`bl:norm`(a), `m₀ = 1`**: the thresholds satisfy `limsup uT_n ≤ a₁`. -/
theorem airy_threshold_le (S : DensitySeq C₀ R ς δ Ψ uT) (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop, uT n ≤ airyZero 1 + ε :=
  threshold_le_of_negative S hbd airyExtremalProfile airyEqualityPrinciple
    (fun i => i.elim) airyExtremal_neg_right ε hε

/-- **`bl:norm`(b), `m₀ = 1`**: locally uniform convergence to the normalised Airy profile. -/
theorem airy_norm_limit (S : DensitySeq C₀ R ς δ Ψ uT) (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n)
    (huT : ∀ x < airyZero 1, ∀ᶠ n in atTop, x ≤ uT n) :
    LocUnif Ψ id airyProfile :=
  norm_limit S hbd airyExtremalProfile airyEqualityPrinciple huT (fun i => i.elim)

/-- Locally uniform convergence of the first derivatives. -/
theorem airy_norm_limit_deriv (S : DensitySeq C₀ R ς δ Ψ uT) (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n)
    (huT : ∀ x < airyZero 1, ∀ᶠ n in atTop, x ≤ uT n) (m : ℕ) :
    TendstoLocallyUniformlyOn (fun n => deriv (Ψ n)) (deriv airyProfile) atTop
      (ball (0 : ℂ) ((m : ℝ) + 1)) :=
  norm_limit_deriv S hbd airyExtremalProfile airyEqualityPrinciple huT (fun i => i.elim) m

/-- `L¹(ℝ)` convergence of the densities extended by zero; no mass escapes. -/
theorem airy_norm_limit_l1 (S : DensitySeq C₀ R ς δ Ψ uT) (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n)
    (huT : ∀ x < airyZero 1, ∀ᶠ n in atTop, x ≤ uT n) :
    Tendsto (fun n => ∫ x : ℝ, ‖(Icc (-(R n)) (R n)).indicator (fun x : ℝ => Ψ n (x : ℂ)) x -
      airyProfile (x : ℂ)‖) atTop (𝓝 0) :=
  norm_limit_l1 S hbd airyExtremalProfile airyEqualityPrinciple huT (fun i => i.elim)

/-- The truncated total mass `∫_{-R_n}^{R_n} Re Ψ_n` tends to `0` (the vacuum slack). -/
theorem airy_norm_limit_integral (S : DensitySeq C₀ R ς δ Ψ uT) (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n)
    (huT : ∀ x < airyZero 1, ∀ᶠ n in atTop, x ≤ uT n) :
    Tendsto (fun n => ∫ x in (-(R n))..(R n), (Ψ n (x : ℂ)).re) atTop (𝓝 0) :=
  norm_limit_integral_re S hbd airyExtremalProfile airyEqualityPrinciple huT (fun i => i.elim)

/-- **`bl:norm`, `m₀ = 1`, combined**: if the thresholds are bounded below, they converge to `a₁`
as soon as `liminf uT_n ≥ a₁`, and then the whole sequence converges to the normalised Airy profile.
(`limsup uT_n ≤ a₁` is automatic, `airy_threshold_le`.) -/
theorem airy_threshold_tendsto (S : DensitySeq C₀ R ς δ Ψ uT) (hbd : ∃ x₀, ∀ n, x₀ ≤ uT n)
    (huT : ∀ x < airyZero 1, ∀ᶠ n in atTop, x ≤ uT n) :
    Tendsto uT atTop (𝓝 (airyZero 1)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [airy_threshold_le S hbd (ε / 2) (half_pos hε),
    huT (airyZero 1 - ε / 2) (by linarith)] with n h1 h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- info: 'FormalResearch.ModularBootstrap.Blowup.airy_norm_limit_l1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_norm_limit_l1

/-- info: 'FormalResearch.ModularBootstrap.Blowup.airy_threshold_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_threshold_le

end FormalResearch.ModularBootstrap.Blowup
