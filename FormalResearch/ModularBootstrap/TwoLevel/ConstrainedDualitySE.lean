module

public import FormalResearch.ModularBootstrap.Duality.Primal.Attainment
public import FormalResearch.ModularBootstrap.Mixtures.Duality

/-!
# Theorem SE.D (`se:cdual`): Constrained strong duality with primal attainment and atomicity

Source: `CFT/modular_bootstrap/paper/soft_edge_two_level_stability.tex`, Theorem SE.D (`se:cdual`).
Combines `ds:E`(b) (`Duality/ConstrainedThreshold.lean`, `Mixtures/ThermalSeparation.lean`) with
`ds:primal` (`Duality/Primal/Attainment.lean`, `Mixtures/Primal.lean`) unconditionally at every
fixed charge:

1. Fixed-weight problems `FixedWeightProblem` at every `c̃ > 0`, `12 S ≤ c̃`
   (`se_cdual_fixedWeight`), with the `F = {t₁}` specialization (`se_cdual_fixedWeight_singleton`).
2. Common shift sources `CommonSource` at every `12 C.a₀ ≤ c̃` (`se_cdual_common`), via `se_cdual_floor`.
3. Positive finite mixtures `MixtureData` at every rebased charge `12 r_min < c̃` with
   `12 S_max ≤ c̃ - 12 r_min` (`se_cdual_mixture`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight
open FormalResearch.ModularBootstrap.Mixtures

section FixedWeight

/-- **Theorem SE.D (`se:cdual`) at any fixed weight `(w, Q)`**, unconditionally for all fixed charges
`c̃ > 0` with `12 S ≤ c̃`: for compact `F ⊂ (0, ∞)` (possibly empty), `X_τ = F ∪ [τ, ∞)`:
1. `0 < T_V(c̃) ≤ T_V(c̃; F) < ∞` (`(constrainedGaps prob cTilde F).Nonempty`);
2. `T_V(c̃; F) = max {τ > 0 : ∃ positive crossing measure supported on X_τ}` (`IsGreatest`),
   attained (with `∫ w_* dν ≤ C₀` under any `DualSetupCore`);
3. every attaining crossing measure on `X_{T_V(c̃; F)}` is carried by a locally finite set and has
   a positive atom at `T_V(c̃; F)`;
4. if `ν` is a positive crossing measure on `X_τ` with `τ > T_V(c̃)`, then `ν(F) > 0`. -/
theorem se_cdual_fixedWeight (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde)
    {F : Set ℝ} (hFc : IsCompact F) (hF : F ⊆ Ioi 0) :
    (0 < prob.T_V cTilde ∧ prob.T_V cTilde ≤ constrainedThreshold prob cTilde F ∧
      (constrainedGaps prob cTilde F).Nonempty) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0} (constrainedThreshold prob cTilde F) ∧
    (∀ {β₀ T₀ : ℝ}, DualSetupCore prob cTilde β₀ T₀ → F ⊆ Ici T₀ → T₀ < prob.T_V cTilde →
      ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 ∧
        Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
        ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀) ∧
    (∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (F ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 →
        (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ meas.ν Zᶜ = 0) ∧
        0 < meas.ν {constrainedThreshold prob cTilde F}) ∧
    (∀ τ : ℝ, prob.T_V cTilde < τ → ∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0 → 0 < meas.ν F) := by
  have hP := theorem_primal hc_pos hc hFc hF
  have hE := theorem_E_b_compact prob hc_pos hc hFc hF hP.1.1
  exact ⟨hP.1, hE.2.1, hE.2.2.1, hP.2.choose_spec.2.2.1, hE.2.2.2⟩

/-- Singleton specialization `F = {t₁}` of `se_cdual_fixedWeight` (`ν({t₁}) > 0` for `τ > T_V`). -/
theorem se_cdual_fixedWeight_singleton (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde)
    {t₁ : ℝ} (ht₁ : 0 < t₁) :
    (0 < prob.T_V cTilde ∧ prob.T_V cTilde ≤ constrainedThreshold prob cTilde {t₁} ∧
      (constrainedGaps prob cTilde {t₁}).Nonempty) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν ({t₁} ∪ Ici τ)ᶜ = 0} (constrainedThreshold prob cTilde {t₁}) ∧
    (∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν ({t₁} ∪ Ici (constrainedThreshold prob cTilde {t₁}))ᶜ = 0 →
        (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ meas.ν Zᶜ = 0) ∧
        0 < meas.ν {constrainedThreshold prob cTilde {t₁}}) ∧
    (∀ τ : ℝ, prob.T_V cTilde < τ → ∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν ({t₁} ∪ Ici τ)ᶜ = 0 → 0 < meas.ν {t₁}) := by
  have h := se_cdual_fixedWeight prob hc_pos hc isCompact_singleton (Set.singleton_subset_iff.2 ht₁)
  exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

end FixedWeight

section CommonSourceSection

private lemma crossing_pos_on_F_of_gt_TV_src {src : ShiftSource} {Fl : FloorData src}
    {cTilde : ℝ} (hAt : Fl.At (cTilde / 12)) (hTV : 0 < src.T_V cTilde)
    {F : Set ℝ} {τ : ℝ} (hτ : src.T_V cTilde < τ)
    (meas : SourceCrossingMeasure src (cTilde / 12)) (hν : meas.ν (F ∪ Ici τ)ᶜ = 0) :
    0 < meas.ν F := by
  by_contra h0
  have hF0 : meas.ν F = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h0)
  have hIci : meas.ν (Ici τ)ᶜ = 0 := by
    refine measure_mono_null (fun t ht => ?_) (measure_union_null hF0 hν)
    by_cases htF : t ∈ F
    · exact Or.inl htF
    · refine Or.inr fun hX => ?_
      rcases hX with h | h
      · exact htF h
      · exact ht h
  have hmax := (theorem_E_b_compact_empty_src hAt hTV).2.2
  have hle : τ ≤ src.T_V cTilde := hmax.2 ⟨lt_trans hTV hτ, meas, hIci⟩
  linarith

/-- **Theorem SE.D (`se:cdual`) under any floor `Fl.At (c̃ / 12)`**:
for compact `F ⊂ (0, ∞)` (possibly empty), `X_τ = F ∪ [τ, ∞)`. -/
theorem se_cdual_floor {src : ShiftSource} {Fl : FloorData src} {cTilde : ℝ}
    (hAt : Fl.At (cTilde / 12)) {F : Set ℝ} (hFc : IsCompact F) (hF : F ⊆ Ioi 0) :
    (0 < src.T_V cTilde ∧ src.T_V cTilde ≤ constrainedThresholdS src cTilde F ∧
      (constrainedGapsS src cTilde F).Nonempty) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : SourceCrossingMeasure src (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0} (constrainedThresholdS src cTilde F) ∧
    (∀ meas : SourceCrossingMeasure src (cTilde / 12),
      meas.ν (F ∪ Ici (constrainedThresholdS src cTilde F))ᶜ = 0 →
        (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ meas.ν Zᶜ = 0) ∧
        0 < meas.ν {constrainedThresholdS src cTilde F}) ∧
    (∀ τ : ℝ, src.T_V cTilde < τ → ∀ meas : SourceCrossingMeasure src (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0 → 0 < meas.ν F) := by
  have hP := theorem_primal_floor hAt hFc hF
  have hE := theorem_E_b_compact_src hAt hFc hF hP.1.1
  exact ⟨hP.1, hE.2.2.1, hP.2.choose_spec.2.2.1,
    fun τ hτ meas hν => crossing_pos_on_F_of_gt_TV_src hAt hP.1.1 hτ meas hν⟩

/-- **Theorem SE.D (`se:cdual`) for any `CommonSource`**, unconditionally at all `12 C.a₀ ≤ c̃`. -/
theorem se_cdual_common (C : CommonSource) {cTilde : ℝ} (hc : 12 * C.a₀ ≤ cTilde)
    {F : Set ℝ} (hFc : IsCompact F) (hF : F ⊆ Ioi 0) :
    (0 < C.src.T_V cTilde ∧ C.src.T_V cTilde ≤ constrainedThresholdS C.src cTilde F ∧
      (constrainedGapsS C.src cTilde F).Nonempty) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : SourceCrossingMeasure C.src (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0} (constrainedThresholdS C.src cTilde F) ∧
    (∀ meas : SourceCrossingMeasure C.src (cTilde / 12),
      meas.ν (F ∪ Ici (constrainedThresholdS C.src cTilde F))ᶜ = 0 →
        (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ meas.ν Zᶜ = 0) ∧
        0 < meas.ν {constrainedThresholdS C.src cTilde F}) ∧
    (∀ τ : ℝ, C.src.T_V cTilde < τ → ∀ meas : SourceCrossingMeasure C.src (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0 → 0 < meas.ν F) :=
  se_cdual_floor (C.at_ (by linarith)) hFc hF

end CommonSourceSection

section MixtureSection

private lemma rebase_isFeasibleOn_iff (M : MixtureData) {a : ℝ} {X : Set ℝ} {g : ℝ → ℝ} :
    M.rebase.toSource.IsFeasibleOn (a - M.rmin) X g ↔ M.toSource.IsFeasibleOn a X g := by
  unfold ShiftSource.IsFeasibleOn
  rw [M.rebase_testClass_iff, M.rebase_gVac]

private lemma rebase_constrainedGapsS (M : MixtureData) (cTilde : ℝ) (F : Set ℝ) :
    constrainedGapsS M.rebase.toSource (cTilde - 12 * M.rmin) F =
      constrainedGapsS M.toSource cTilde F := by
  ext τ
  simp only [constrainedGapsS, mem_ofPred_eq, M.rebase_charge, rebase_isFeasibleOn_iff]

private lemma rebase_constrainedThresholdS (M : MixtureData) (cTilde : ℝ) (F : Set ℝ) :
    constrainedThresholdS M.rebase.toSource (cTilde - 12 * M.rmin) F =
      constrainedThresholdS M.toSource cTilde F := by
  unfold constrainedThresholdS
  rw [rebase_constrainedGapsS]

private lemma forall_measure_eq {src : ShiftSource} {a₁ a₂ : ℝ} (h : a₁ = a₂)
    {P : ∀ a, SourceCrossingMeasure src a → Prop}
    (hp : ∀ m : SourceCrossingMeasure src a₁, P a₁ m) :
    ∀ m : SourceCrossingMeasure src a₂, P a₂ m := by
  subst h; exact hp

/-- **Theorem SE.D (`se:cdual`) for any positive finite mixture `M : MixtureData`**,
unconditionally at every rebased charge `c̃ - 12 r_min > 0` with `12 S_max ≤ c̃ - 12 r_min`:
all four clauses directly for `M.toSource` at charge `c̃`. -/
theorem se_cdual_mixture (M : MixtureData) {cTilde : ℝ}
    (hc_pos : 0 < cTilde - 12 * M.rmin) (hc : 12 * M.rebase.Smax ≤ cTilde - 12 * M.rmin)
    {F : Set ℝ} (hFc : IsCompact F) (hF : F ⊆ Ioi 0) :
    (0 < M.toSource.T_V cTilde ∧
      M.toSource.T_V cTilde ≤ constrainedThresholdS M.toSource cTilde F ∧
      (constrainedGapsS M.toSource cTilde F).Nonempty) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : SourceCrossingMeasure M.toSource (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0} (constrainedThresholdS M.toSource cTilde F) ∧
    (∀ meas : SourceCrossingMeasure M.toSource (cTilde / 12),
      meas.ν (F ∪ Ici (constrainedThresholdS M.toSource cTilde F))ᶜ = 0 →
        (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ meas.ν Zᶜ = 0) ∧
        0 < meas.ν {constrainedThresholdS M.toSource cTilde F}) ∧
    (∀ τ : ℝ, M.toSource.T_V cTilde < τ → ∀ meas : SourceCrossingMeasure M.toSource (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0 → 0 < meas.ν F) := by
  obtain ⟨i₀, hi₀⟩ := M.rebase_exists_zero
  have hAt : (M.rebase.floorData i₀).At ((cTilde - 12 * M.rmin) / 12) :=
    M.rebase.floorAt hi₀ (by linarith) (by linarith)
  have h := se_cdual_floor hAt hFc hF
  have hTV_eq : M.rebase.toSource.T_V (cTilde - 12 * M.rmin) = M.toSource.T_V cTilde := M.rebase_T_V cTilde
  have hTF_eq : constrainedThresholdS M.rebase.toSource (cTilde - 12 * M.rmin) F =
      constrainedThresholdS M.toSource cTilde F := rebase_constrainedThresholdS M cTilde F
  have hgap_eq : constrainedGapsS M.rebase.toSource (cTilde - 12 * M.rmin) F =
      constrainedGapsS M.toSource cTilde F := rebase_constrainedGapsS M cTilde F
  have hm_iff : ∀ {X : Set ℝ},
      (∃ m : SourceCrossingMeasure M.rebase.toSource ((cTilde - 12 * M.rmin) / 12), m.ν Xᶜ = 0) ↔
      ∃ m : SourceCrossingMeasure M.toSource (cTilde / 12), m.ν Xᶜ = 0 := by
    intro X
    rw [M.rebase_charge cTilde]
    exact ⟨fun ⟨m, hm⟩ => ⟨crossingMeasure_of_rebase M m, hm⟩,
      fun ⟨m, hm⟩ => ⟨rebase_crossingMeasure M m, hm⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hTV_eq, hTF_eq, hgap_eq] using h.1
  · constructor
    · obtain ⟨hpos, hm⟩ := h.2.1.1
      rw [hTF_eq] at hpos hm
      exact ⟨hpos, (hm_iff).1 hm⟩
    · rintro τ ⟨hτ, hm⟩
      rw [← hTF_eq]
      exact h.2.1.2 ⟨hτ, (hm_iff).2 hm⟩
  · intro meas hν
    have h3 := forall_measure_eq (M.rebase_charge cTilde)
      (P := fun _ m =>
        m.ν (F ∪ Ici (constrainedThresholdS M.rebase.toSource (cTilde - 12 * M.rmin) F))ᶜ = 0 →
          (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ m.ν Zᶜ = 0) ∧
          0 < m.ν {constrainedThresholdS M.rebase.toSource (cTilde - 12 * M.rmin) F})
      h.2.2.1 (rebase_crossingMeasure M meas)
    have hν' : (rebase_crossingMeasure M meas).ν
        (F ∪ Ici (constrainedThresholdS M.rebase.toSource (cTilde - 12 * M.rmin) F))ᶜ = 0 := by
      simpa only [rebase_crossingMeasure, hTF_eq] using hν
    simpa only [rebase_crossingMeasure, hTF_eq] using h3 hν'
  · intro τ hτ meas hν
    have hτ' : M.rebase.toSource.T_V (cTilde - 12 * M.rmin) < τ := by rwa [hTV_eq]
    have h4 := forall_measure_eq (M.rebase_charge cTilde)
      (P := fun _ m => m.ν (F ∪ Ici τ)ᶜ = 0 → 0 < m.ν F)
      (h.2.2.2 τ hτ') (rebase_crossingMeasure M meas)
    exact h4 hν

end MixtureSection

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.se_cdual_fixedWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.se_cdual_fixedWeight

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.se_cdual_fixedWeight_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.se_cdual_fixedWeight_singleton

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.se_cdual_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.se_cdual_common

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.se_cdual_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.se_cdual_mixture

end FormalResearch.ModularBootstrap.TwoLevel
