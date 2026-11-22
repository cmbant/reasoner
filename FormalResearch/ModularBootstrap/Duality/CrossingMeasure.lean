module

public import FormalResearch.ModularBootstrap.Crossing.MehlerOddMoment

/-!
# Crossing measures at a gap: Proposition D1 and complementary slackness

Source: `CFT/modular_bootstrap/paper/dual_spectrum.tex` (Proposition D1, `ds:D1`) and
`spectral_rigidity.tex` (Propositions 1 and 2, `sr:P1`, `sr:P2`), in measure-theoretic form.

A *crossing measure at gap `τ > 0`* is a positive measure `ν` on `[τ, ∞)` with finite Laplace
transform at every positive argument (Z1) and `∫ Ξ_β d(ν - ρ_C dt) = 0` for every `β > 0` (Z2).
In Lean this is an `AdmissibleCrossingMeasure` (which already carries (Z1), (Z2) and
`ν (Iio 0) = 0`) together with `ν (Iio τ) = 0`; local finiteness (Radon) is a consequence of (Z1).

All results below are unconditional (they use `lemma_fwX_one_sided_unconditional` and
`lemma_fwX_equality_unconditional`, i.e. the proved Mehler moment input).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Duality

open FormalResearch.ModularBootstrap.Crossing

/-- A crossing measure at gap `τ` for the fixed-weight problem `prob` at vacuum shift `a`:
an `AdmissibleCrossingMeasure` (Z1, Z2) supported on `[τ, ∞)`. -/
def HasCrossingMeasureAt (prob : FixedWeightProblem) (a τ : ℝ) : Prop :=
  ∃ meas : AdmissibleCrossingMeasure prob a, meas.ν (Iio τ) = 0

/-- Abbreviation: the measure of `meas` vanishes below `τ`. -/
def IsAtGap {prob : FixedWeightProblem} {a : ℝ}
    (meas : AdmissibleCrossingMeasure prob a) (τ : ℝ) : Prop :=
  meas.ν (Iio τ) = 0

lemma ae_ge_of_isAtGap {prob : FixedWeightProblem} {a : ℝ}
    {meas : AdmissibleCrossingMeasure prob a} {τ : ℝ} (h : IsAtGap meas τ) :
    ∀ᵐ t ∂meas.ν, τ ≤ t := by
  have h' : meas.ν (Iio τ) = 0 := h
  have : ∀ᵐ t ∂meas.ν, t ∉ Iio τ := measure_eq_zero_iff_ae_notMem.1 h'
  filter_upwards [this] with t ht using not_lt.mp ht

lemma restrict_Ici_eq_self {prob : FixedWeightProblem} {a : ℝ}
    (meas : AdmissibleCrossingMeasure prob a) :
    meas.ν.restrict (Ici 0) = meas.ν := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff, show {a : ℝ | a ∉ Ici 0} = Iio 0 by ext t; simp]
  exact meas.supp_nonneg

/-- **Complementary slackness** (`spectral_rigidity.tex`, Proposition 2, `sr:P2`, measure form).
Let `ν` be a crossing measure at gap `τ > 0` and `g ∈ \overline{\mathcal A}` with `g ≥ 0` on
`[τ, ∞)`. Then `g` is `ν`-integrable and `0 ≤ ∫ g dν ≤ -g_vac`. In particular, if `g_vac ≥ 0`
(`g` weakly feasible with `t₁(g) ≤ τ`), then `g_vac = 0` and `g = 0` `ν`-almost everywhere
(on the support of the atoms). -/
theorem proposition_P2 (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) (ha_pos : 0 < a)
    (meas : AdmissibleCrossingMeasure prob a) {τ : ℝ} (_hτ : 0 < τ) (hgap : IsAtGap meas τ)
    {g : ℝ → ℝ} (hg : TestClass prob a g) (hg_nn : ∀ t, τ ≤ t → 0 ≤ g t) :
    IntegrableOn g (Ici 0) meas.ν ∧ 0 ≤ ∫ t in Ici 0, g t ∂meas.ν ∧
      ∫ t in Ici 0, g t ∂meas.ν ≤ -prob.gVac a g ∧
      (0 ≤ prob.gVac a g → prob.gVac a g = 0 ∧ ∀ᵐ t ∂meas.ν, g t = 0) := by
  obtain ⟨hint, hle⟩ := lemma_fwX_one_sided_unconditional prob ha ha_pos meas hg hg_nn
  have hae : ∀ᵐ t ∂meas.ν, 0 ≤ g t := by
    filter_upwards [ae_ge_of_isAtGap hgap] with t ht using hg_nn t ht
  rw [IntegrableOn, restrict_Ici_eq_self meas] at hint
  rw [restrict_Ici_eq_self meas] at hle ⊢
  have h0 : 0 ≤ ∫ t, g t ∂meas.ν := integral_nonneg_of_ae hae
  refine ⟨by rwa [IntegrableOn, restrict_Ici_eq_self meas], h0, by linarith, fun hv => ?_⟩
  have hv0 : prob.gVac a g = 0 := by linarith
  refine ⟨hv0, ?_⟩
  have hzero : ∫ t, g t ∂meas.ν = 0 := by linarith
  have := (integral_eq_zero_iff_of_nonneg_ae hae hint).1 hzero
  exact this

/-- **Spectral sum rule** (`spectral_rigidity.tex`, Proposition 1, `sr:P1`, measure form, before
the change of variables `u = u(t)` to the Airy window): for a crossing measure `ν` and
`g ∈ \overline{\mathcal A}` with `|g(t)| ≤ C (1+t)^{-q} e^{-4π √(a t)}`, `q > (w+1)/2`,
`g` is `ν`-integrable and `g_vac + ∫ g dν = 0`. (This is `lemma_fwX_equality_unconditional`.) -/
theorem proposition_P1 (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) (ha_pos : 0 < a)
    (meas : AdmissibleCrossingMeasure prob a)
    {g : ℝ → ℝ} (hg : TestClass prob a g) {q C_g : ℝ}
    (hq : (prob.w + 1 : ℝ) / 2 < q) (hC_g : 0 ≤ C_g)
    (hdecay : ∀ t, 0 ≤ t → |g t| ≤ C_g * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t))) :
    IntegrableOn g (Ici 0) meas.ν ∧
      prob.gVac a g + ∫ t in Ici 0, g t ∂meas.ν = 0 :=
  lemma_fwX_equality_unconditional prob ha ha_pos meas hg hq hC_g hdecay

/-- **Proposition D1** (`dual_spectrum.tex`, `ds:D1`). If a crossing measure at gap `τ > 0`
exists, no `g ∈ \overline{\mathcal A}` is feasible at any `T ≤ τ`; hence `T_V(c) ≥ τ` and
`Δ_best ≥ a + τ`, where `a = c̃ / 12` (`c̃ = c' = c - 1` in the paper's notation, `c ≥ 40`;
here any `c̃ ≥ 12 · totalShift`, which is `c̃ ≥ 24` for the Virasoro problem).
The two spectral propositions for `ν` are `proposition_P1` and `proposition_P2`. -/
theorem proposition_D1 (prob : FixedWeightProblem)
    {cTilde τ : ℝ} (hc : 12 * prob.totalShift ≤ cTilde) (hc_pos : 0 < cTilde) (hτ : 0 < τ)
    (hν : HasCrossingMeasureAt prob (cTilde / 12) τ) :
    (∀ T ≤ τ, ∀ g, ¬ prob.IsFeasible (cTilde / 12) T g) ∧
      τ ≤ prob.T_V cTilde ∧ cTilde / 12 + τ ≤ prob.Delta_best cTilde := by
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  have ha_pos : 0 < cTilde / 12 := by linarith
  obtain ⟨meas, hgap⟩ := hν
  have hnone : ∀ T ≤ τ, ∀ g, ¬ prob.IsFeasible (cTilde / 12) T g := by
    intro T hT g hg
    obtain ⟨h1, h2, h3, h4⟩ := proposition_P2 prob ha ha_pos meas hτ hgap hg.1
      (fun t ht => hg.2.2 t (hT.trans ht))
    linarith [hg.2.1]
  have hTV : τ ≤ prob.T_V cTilde := by
    unfold FixedWeightProblem.T_V
    refine le_csInf (prob.feasible_nonempty hc) ?_
    rintro T ⟨hT, g, hg⟩
    by_contra hlt
    exact hnone T (not_le.mp hlt).le g hg
  refine ⟨hnone, hTV, ?_⟩
  unfold FixedWeightProblem.Delta_best
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Duality.proposition_D1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.proposition_D1

/-- info: 'FormalResearch.ModularBootstrap.Duality.proposition_P2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.proposition_P2

/-- info: 'FormalResearch.ModularBootstrap.Duality.proposition_P1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.proposition_P1

end FormalResearch.ModularBootstrap.Duality
