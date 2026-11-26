module

public import FormalResearch.ModularBootstrap.WeightAxioms.HankelContinuation
public import FormalResearch.ModularBootstrap.WeightAxioms.ComplexAsymptotics

/-!
# Fixed-charge strip bound (`dsl:strip-fixed`(a), `dual_spectrum_limit.tex`)

`FixedChargeStrip prob cTilde` packages the analytic input of the primal-attainment argument at the
charge `a = c̃/12`:

* the Hankel continuation `G(b) = -2π ∫ g K_{-c̃ b²/3} dt` of every `g ∈ Ā_w` is continuous on the
  closed strip `|Im b| ≤ 1/2`, holomorphic in the open strip, and bounded there by `C · M[g]`;
* `t^{w-1} / V(t) → 0` as `t → ∞`.

`fixedChargeStrip_of_large` proves it for all charges `c̃ ≥ c₀(w, Q)`, from `Lemma 4(a)` as
formalised in `WeightAxioms.HankelContinuation` and the comparison `K ≤ C V`
(`kernelK_le_mul_cardyV_gen`).  The paper states `dsl:strip-fixed`(a) at every charge
`c̃ ≥ 12 S`; the Lean `Lemma 4` stack is for `c̃ ≥ c₀` only, so the low-charge range remains open
(it needs `V/K → D₀ > 0` at fixed charge, not formalised).
-/

@[expose] public section

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeight

open Crossing WeightAxioms

/-- The analytic input of the fixed-charge primal argument. -/
structure FixedChargeStrip (prob : FixedWeightProblem) (cTilde : ℝ) : Prop where
  hc_pos : 0 < cTilde
  hc : 12 * prob.totalShift ≤ cTilde
  bound : ∃ C : ℝ, ∀ g : ℝ → ℝ, TestClass prob (cTilde / 12) g → ∀ b : ℂ, |b.im| ≤ 1 / 2 →
    ‖hankelContinuationW prob.w cTilde g b‖ ≤ C * prob.cardyNorm (cTilde / 12) g
  cont : ∀ g : ℝ → ℝ, TestClass prob (cTilde / 12) g →
    ContinuousOn (hankelContinuationW prob.w cTilde g) {b : ℂ | |b.im| ≤ 1 / 2}
  diff : ∀ g : ℝ → ℝ, TestClass prob (cTilde / 12) g →
    DifferentiableOn ℂ (hankelContinuationW prob.w cTilde g) {b : ℂ | |b.im| < 1 / 2}
  tail : ∀ ε > 0, ∃ R : ℝ, ∀ t ≥ R, t ^ (prob.w - 1) ≤ ε * prob.cardyV (cTilde / 12) t

/-- `K_a^{(w)}(t) ≥ (2π t)^{w-1} · 4π² a t / w!` for `a, t ≥ 0`. -/
lemma kernelK_ge_linear (w : ℕ) (hw : 1 ≤ w) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (2 * π * t) ^ (w - 1) * (4 * π ^ 2 * a * t / (w.factorial : ℝ)) ≤ kernelK w a t := by
  unfold kernelK
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hnn : ∀ k, 0 ≤ kernelKTerm w a t k := fun k => by unfold kernelKTerm; positivity
  have h1 := (summable_kernelKTerm w a t).le_tsum 1 (fun k _ => hnn k)
  refine le_trans (le_of_eq ?_) h1
  unfold kernelKTerm
  have : (1 + w - 1) = w := by omega
  simp [this]

/-- `t^{w-1} / V(t) → 0` at large charge (`c' ≥ c₀`). -/
theorem tail_of_large (prob : FixedWeightProblem) :
    ∃ c₀ : ℝ, max 1 (24 * prob.totalShift) ≤ c₀ ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ ε > 0, ∃ R : ℝ,
      ∀ t ≥ R, t ^ (prob.w - 1) ≤ ε * prob.cardyV (c' / 12) t := by
  obtain ⟨C_K, c₀, hCK, hc₀, hK⟩ := kernelK_le_mul_cardyV_gen prob
  refine ⟨c₀, hc₀, fun {c'} hc' ε hε => ?_⟩
  have hcm : max 1 (24 * prob.totalShift) ≤ c' := hc₀.trans hc'
  have hc1 : 1 ≤ c' := (le_max_left _ _).trans hcm
  have hc'0 : 0 < c' := by linarith
  have ha : 0 < c' / 12 := by positivity
  have hw := prob.hw
  set D : ℝ := C_K * c' ^ (prob.m : ℝ) with hD
  have hD0 : 0 < D := by positivity
  have hfac : (0 : ℝ) < (prob.w.factorial : ℝ) := by positivity
  set R₁ : ℝ := (prob.w.factorial : ℝ) * D /
    (ε * ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2 * (c' / 12)))) with hR₁
  refine ⟨max (4 / c') R₁, fun t ht => ?_⟩
  have ht4 : 4 / c' ≤ t := (le_max_left _ _).trans ht
  have htR : R₁ ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht4
  have hVK := hK hc' ht4
  have hKlin := kernelK_ge_linear prob.w hw ha.le ht0.le
  have hpow : 0 < (2 * π) ^ (prob.w - 1) := by positivity
  have htw : 0 < t ^ (prob.w - 1) := pow_pos ht0 _
  have hcoef : 0 < ε * ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2 * (c' / 12))) := by positivity
  -- `t ≥ R₁` means `ε * (2π)^{w-1} * 4π² a * t ≥ w! D`
  have h1 : (prob.w.factorial : ℝ) * D ≤ t * (ε * ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2 * (c' / 12)))) := by
    have := (div_le_iff₀ hcoef).1 htR
    linarith
  have h2 : (2 * π * t) ^ (prob.w - 1) * (4 * π ^ 2 * (c' / 12) * t / (prob.w.factorial : ℝ)) ≤
      D * prob.cardyV (c' / 12) t := hKlin.trans hVK
  rw [mul_pow] at h2
  -- multiply out: t^{w-1} * [(2π)^{w-1} * (4π² a t / w!)] ≤ D V
  have h3 : t ^ (prob.w - 1) * ((prob.w.factorial : ℝ) * D) ≤
      t ^ (prob.w - 1) * (t * (ε * ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2 * (c' / 12))))) :=
    mul_le_mul_of_nonneg_left h1 htw.le
  have h4 : (prob.w.factorial : ℝ) * (D * prob.cardyV (c' / 12) t) ≥
      (2 * π) ^ (prob.w - 1) * t ^ (prob.w - 1) * (4 * π ^ 2 * (c' / 12) * t) := by
    have := mul_le_mul_of_nonneg_left h2 hfac.le
    calc (prob.w.factorial : ℝ) * (D * prob.cardyV (c' / 12) t)
        ≥ (prob.w.factorial : ℝ) * ((2 * π) ^ (prob.w - 1) * t ^ (prob.w - 1) *
            (4 * π ^ 2 * (c' / 12) * t / (prob.w.factorial : ℝ))) := this
      _ = (2 * π) ^ (prob.w - 1) * t ^ (prob.w - 1) * (4 * π ^ 2 * (c' / 12) * t) := by
          field_simp
  -- conclude
  have h5 : t ^ (prob.w - 1) * ((prob.w.factorial : ℝ) * D) ≤
      (prob.w.factorial : ℝ) * (D * (ε * prob.cardyV (c' / 12) t)) := by
    calc t ^ (prob.w - 1) * ((prob.w.factorial : ℝ) * D)
        ≤ t ^ (prob.w - 1) * (t * (ε * ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2 * (c' / 12))))) := h3
      _ = ε * ((2 * π) ^ (prob.w - 1) * t ^ (prob.w - 1) * (4 * π ^ 2 * (c' / 12) * t)) := by ring
      _ ≤ ε * ((prob.w.factorial : ℝ) * (D * prob.cardyV (c' / 12) t)) :=
          mul_le_mul_of_nonneg_left h4 hε.le
      _ = (prob.w.factorial : ℝ) * (D * (ε * prob.cardyV (c' / 12) t)) := by ring
  have h6 := le_of_mul_le_mul_left (by linarith : (prob.w.factorial : ℝ) * D * t ^ (prob.w - 1) ≤
      (prob.w.factorial : ℝ) * D * (ε * prob.cardyV (c' / 12) t)) (mul_pos hfac hD0)
  exact h6

/-- **`dsl:strip-fixed`(a) at large charge**: there is `c₀` with `FixedChargeStrip prob c̃` for every
`c̃ ≥ c₀`. -/
theorem fixedChargeStrip_of_large (prob : FixedWeightProblem) :
    ∃ c₀ : ℝ, ∀ {cTilde : ℝ}, c₀ ≤ cTilde → FixedChargeStrip prob cTilde := by
  obtain ⟨C_e, c₁, hCe, hc₁, hb⟩ := hankelContinuationW_strip_bound prob
  obtain ⟨c₂, hc₂, hcont⟩ := continuousOn_hankelContinuationW prob
  obtain ⟨c₃, hc₃, hdiff⟩ := differentiableOn_hankelContinuationW prob
  obtain ⟨c₄, hc₄, htail⟩ := tail_of_large prob
  refine ⟨max (max c₁ c₂) (max c₃ c₄), fun {cTilde} hc => ?_⟩
  have h1 : c₁ ≤ cTilde := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have h2 : c₂ ≤ cTilde := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have h3 : c₃ ≤ cTilde := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have h4 : c₄ ≤ cTilde := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hcm : max 1 (24 * prob.totalShift) ≤ cTilde := hc₁.trans h1
  have hc1 : 1 ≤ cTilde := (le_max_left _ _).trans hcm
  have hcS : 24 * prob.totalShift ≤ cTilde := (le_max_right _ _).trans hcm
  refine ⟨by linarith, by linarith [prob.totalShift_nonneg], ⟨C_e * (1 + cTilde ^ (prob.m : ℝ)), ?_⟩,
    fun g hg => hcont h2 hg, fun g hg => hdiff h3 hg, htail h4⟩
  intro g hg b hb'
  have := (hb h1 hg hb').2
  linarith [mul_comm C_e (1 + cTilde ^ (prob.m : ℝ))]

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.fixedChargeStrip_of_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.fixedChargeStrip_of_large

end FormalResearch.ModularBootstrap.FixedWeight
