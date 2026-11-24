module

public import FormalResearch.ModularBootstrap.FixedWeight.StrongDuality

/-!
# Strong duality on a constrained admissible set (Theorem E with `X` in place of `[τ, ∞)`)

`dual_spectrum.tex`, Theorem E (`ds:E`) and `virasoro_two_level.tex`, proof of Corollary 2.4 (`gt:2.4`):
the proof of Theorem E(a), (b) repeats verbatim with the admissible set `[τ, ∞)` replaced by any
closed `X ⊆ [T₀, ∞)`, in particular `X = {t₁} ∪ [τ, ∞)`.

A functional is *feasible on `X`* when `g ∈ Ā` (`TestClass`), `g_vac > 0` and `g ≥ 0` on `X`
(`IsFeasibleOn`; on `X = [T, ∞)` it is `IsFeasible a T`). The general moment-problem, compactness and
transport statements (`dual_inequality_on`, `exists_atomic_approx_on`, `exists_measure_exact_on`,
`exists_crossingMeasure_of_limit_on`, `pullMeasure_compl_eq_zero`) live beside the statements they generalise
(`FixedWeight/MomentProblem.lean`, `FixedWeight/StrongDuality.lean`, `Duality/LimitMeasure.lean`); the
`X = [T, ∞)` statements are their instances.

* `exists_crossingMeasure_of_not_feasible`: if no functional is feasible on the closed set `X ⊆ [T₀, ∞)`, there
  is a crossing measure `ν` with `ν (Xᶜ) = 0`, `w_* ∈ L¹(ν)` and `∫ w_* dν ≤ C₀`.
* `not_feasible_of_crossingMeasure`: conversely a crossing measure supported on `X` excludes every feasible
  functional on `X` (Lemma FW-X (1)).
* `constrained_strong_duality`: both directions, for every fixed weight `(w, Q)` under `DualSetupCore`.
* `constrained_strong_duality_two_level`: the instance `X = {t₁} ∪ [τ, ∞)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real NNReal BoundedContinuousFunction

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-- The cut-off `s ↦ dist (s, τ(X))` on `[0, 1]` for a closed set `X ⊆ [T₀, ∞)`. -/
noncomputable def cutoffOfSet (T₀ : ℝ) (X : Set ℝ) : Ecoord →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun s => Metric.infDist s (toE T₀ '' X), Metric.continuous_infDist_pt _⟩

lemma cutoffOfSet_nonneg (T₀ : ℝ) (X : Set ℝ) (s : Ecoord) : 0 ≤ cutoffOfSet T₀ X s :=
  Metric.infDist_nonneg

lemma cutoffOfSet_toE {T₀ : ℝ} {X : Set ℝ} {t : ℝ} (ht : t ∈ X) :
    cutoffOfSet T₀ X (toE T₀ t) = 0 :=
  Metric.infDist_zero_of_mem ⟨t, ht, rfl⟩

lemma tauE_mem_of_cutoffOfSet_eq_zero {T₀ : ℝ} {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀)
    (hne : X.Nonempty) {s : Ecoord} (hs : 0 < s.1) (h0 : cutoffOfSet T₀ X s = 0) :
    tauE T₀ s ∈ X := by
  have hE : (toE T₀ '' X).Nonempty := hne.image _
  have hcl : s ∈ closure (toE T₀ '' X) :=
    (Metric.mem_closure_iff_infDist_zero hE).2 h0
  obtain ⟨x, hxE, hxlim⟩ := mem_closure_iff_seq_limit.1 hcl
  have hτ : Tendsto (fun n => tauE T₀ (x n)) atTop (𝓝 (tauE T₀ s)) :=
    (continuousAt_tauE T₀ hs).tendsto.comp hxlim
  refine hXc.mem_of_tendsto hτ (Eventually.of_forall fun n => ?_)
  obtain ⟨t, ht, hxt⟩ := hxE n
  rw [← hxt, tauE_toE (hX ht)]
  exact ht

/-- **Theorem E with a constrained admissible set** (`dual_spectrum.tex`, `ds:E`(a), (b), repeated on a closed
`X ⊆ [T₀, ∞)`; `virasoro_two_level.tex`, `gt:2.4`): if no `g ∈ Ā` has `g_vac > 0` and `g ≥ 0` on `X`, there is a
crossing measure supported on `X` with `w_* ∈ L¹(ν)` and `∫ w_* dν ≤ C₀`. -/
theorem exists_crossingMeasure_of_not_feasible (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀)
    (hno : ∀ g, ¬ prob.IsFeasibleOn (cTilde / 12) X g) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν Xᶜ = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  have hne : X.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    obtain ⟨T, -, g, hg⟩ := prob.feasible_nonempty S.hc
    exact hno g ⟨hg.1, hg.2.1, by simp [hemp]⟩
  obtain ⟨μ, hmass, hζ, hcross⟩ := exists_measure_exact_on prob S hX hno (cutoffOfSet T₀ X)
    fun t ht => cutoffOfSet_toE ht
  obtain ⟨meas, hsupp, hint, hle⟩ := exists_crossingMeasure_of_limit_on prob S μ hmass hcross
  exact ⟨meas, hsupp hXc.measurableSet (cutoffOfSet T₀ X) (cutoffOfSet_nonneg T₀ X)
    (fun s hs h0 => tauE_mem_of_cutoffOfSet_eq_zero hXc hX hne hs h0) hζ, hint, hle⟩

/-- A crossing measure supported on `X ⊇ [τ, ∞)` excludes every functional feasible on `X`
(Lemma FW-X (1), `crossing_sum_rule.tex`; the converse of `exists_crossingMeasure_of_not_feasible`). -/
theorem not_feasible_of_crossingMeasure (prob : FixedWeightProblem) {a : ℝ}
    (ha : prob.totalShift ≤ a) (ha_pos : 0 < a) (meas : AdmissibleCrossingMeasure prob a)
    {X : Set ℝ} (hν : meas.ν Xᶜ = 0) {τ : ℝ} (hτ : Ici τ ⊆ X) (g : ℝ → ℝ) :
    ¬ prob.IsFeasibleOn a X g := by
  rintro ⟨hg, hvac, hnn⟩
  obtain ⟨-, hle⟩ := lemma_fwX_one_sided_unconditional prob ha ha_pos meas hg
    (T := τ) (fun t ht => hnn t (hτ ht))
  have hae : ∀ᵐ t ∂meas.ν, 0 ≤ g t := by
    have : ∀ᵐ t ∂meas.ν, t ∉ Xᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with t ht using hnn t (by simpa using ht)
  rw [restrict_Ici_eq_self meas] at hle
  have h0 : 0 ≤ ∫ t, g t ∂meas.ν := integral_nonneg_of_ae hae
  linarith

/-- **Constrained strong duality** (`dual_spectrum.tex`, `ds:E`, with `X` in place of `[τ, ∞)`): for a closed
`X ⊆ [T₀, ∞)` containing a ray `[τ, ∞)`, at every fixed weight `(w, Q)`, no `g ∈ Ā` has `g_vac > 0` and `g ≥ 0`
on `X` if and only if there is a crossing measure supported on `X` (with `∫ w_* dν ≤ C₀`). -/
theorem constrained_strong_duality (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀)
    (hray : ∃ τ, Ici τ ⊆ X) :
    (∀ g, ¬ prob.IsFeasibleOn (cTilde / 12) X g) ↔
      ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν Xᶜ = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
        ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  refine ⟨exists_crossingMeasure_of_not_feasible prob S hXc hX, ?_⟩
  rintro ⟨meas, hν, -, -⟩
  obtain ⟨τ, hτ⟩ := hray
  exact fun g => not_feasible_of_crossingMeasure prob S.ha S.ha_pos meas hν hτ g

/-- The two-level instance of `constrained_strong_duality`, `X = {t₁} ∪ [τ, ∞)`
(`virasoro_two_level.tex`, proof of `gt:2.4`, first bullet): no `g ∈ Ā` with `g_vac > 0`, `g(t₁) ≥ 0` and
`g ≥ 0` on `[τ, ∞)` if and only if there is a crossing measure supported on `{t₁} ∪ [τ, ∞)`. -/
theorem constrained_strong_duality_two_level (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {t₁ τ : ℝ} (ht₁ : T₀ ≤ t₁) (hτ : T₀ ≤ τ) :
    (∀ g, ¬ (TestClass prob (cTilde / 12) g ∧ 0 < prob.gVac (cTilde / 12) g ∧ 0 ≤ g t₁ ∧
        ∀ t, τ ≤ t → 0 ≤ g t)) ↔
      ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν ({t₁} ∪ Ici τ)ᶜ = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
        ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  have hXc : IsClosed ({t₁} ∪ Ici τ : Set ℝ) := isClosed_singleton.union isClosed_Ici
  have hX : ({t₁} ∪ Ici τ : Set ℝ) ⊆ Ici T₀ := by
    rintro t (rfl | ht)
    · exact ht₁
    · exact hτ.trans ht
  have hfe : ∀ g, prob.IsFeasibleOn (cTilde / 12) ({t₁} ∪ Ici τ) g ↔
      (TestClass prob (cTilde / 12) g ∧ 0 < prob.gVac (cTilde / 12) g ∧ 0 ≤ g t₁ ∧
        ∀ t, τ ≤ t → 0 ≤ g t) := fun g => by
    unfold FixedWeightProblem.IsFeasibleOn
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3 t₁ (Or.inl rfl), fun t ht => h3 t (Or.inr ht)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, ?_⟩
      rintro t (rfl | ht)
      · exact h3
      · exact h4 t ht
  have := constrained_strong_duality prob S hXc hX ⟨τ, subset_union_right⟩
  simpa only [hfe] using this

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.constrained_strong_duality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.constrained_strong_duality

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.constrained_strong_duality_two_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.constrained_strong_duality_two_level

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.exists_crossingMeasure_of_not_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.exists_crossingMeasure_of_not_feasible

end FormalResearch.ModularBootstrap.FixedWeight
