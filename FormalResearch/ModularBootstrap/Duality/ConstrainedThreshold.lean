module

public import FormalResearch.ModularBootstrap.Duality.ThermalSeparation
public import FormalResearch.ModularBootstrap.Duality.ConstrainedFeasible

/-!
# Constrained strong duality with attainment (Theorem E(b), `ds:E`(b), `dual_spectrum.tex`)

For a compact `F ⊂ (0, ∞)` (possibly empty) put `X_τ = F ∪ [τ, ∞)` and
`T_F = inf {τ > 0 : ∃ g ∈ Ā_w, g_vac > 0, g ≥ 0 on X_τ}` (`constrainedThreshold`; `T_∅ = T_V`).
At every fixed weight `(w, Q)` with `c̃ > 0`, `c̃ ≥ 12 S` and `T_V(c̃) > 0`
(`theorem_E_b_compact`; positivity of `T_V` is the half-mass argument of `dsl:strip-fixed`(b), supplied by
the hypothesis `0 < T_V`, as in `DualSetup`):

* `T_V ≤ T_F < ∞` (finiteness from `exists_feasible_of_compact`);
* `T_F = max {τ > 0 : a positive crossing measure carried by X_τ exists}` (`IsGreatest`), the
  maximum being attained by a crossing measure on `X_{T_F}` with `∫ w_* dν_* ≤ C₀`;
* every crossing measure on `X_τ` with `τ > T_V` has `ν(F) > 0`;
* for `F = ∅`: `T_∅ = T_V` and `min supp ν_* = T_V` (`theorem_E_b_compact_empty`).

The attaining measure is the limit of crossing measures on `X_{τ_j}`, `τ_j ↑ T_F`, obtained from
`theorem_E_a_decreasing`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-- The gaps `τ > 0` at which a strictly feasible test on `X_τ = F ∪ [τ, ∞)` exists. -/
def constrainedGaps (prob : FixedWeightProblem) (cTilde : ℝ) (F : Set ℝ) : Set ℝ :=
  {τ : ℝ | 0 < τ ∧ ∃ g, prob.IsFeasibleOn (cTilde / 12) (F ∪ Ici τ) g}

/-- The constrained threshold `T_F(c̃) = inf {τ > 0 : ∃ g ∈ Ā_w, g_vac > 0, g ≥ 0 on F ∪ [τ, ∞)}`
(`dual_spectrum.tex`, `ds:E`(b)). -/
noncomputable def constrainedThreshold (prob : FixedWeightProblem) (cTilde : ℝ) (F : Set ℝ) : ℝ :=
  sInf (constrainedGaps prob cTilde F)

lemma constrainedGaps_empty (prob : FixedWeightProblem) (cTilde : ℝ) :
    constrainedGaps prob cTilde ∅ = {T : ℝ | 0 < T ∧ ∃ g, prob.IsFeasible (cTilde / 12) T g} := by
  ext τ
  simp only [constrainedGaps, empty_union, isFeasibleOn_Ici_iff, mem_ofPred_eq]

/-- `T_∅ = T_V`. -/
theorem constrainedThreshold_empty (prob : FixedWeightProblem) (cTilde : ℝ) :
    constrainedThreshold prob cTilde ∅ = prob.T_V cTilde := by
  unfold constrainedThreshold FixedWeightProblem.T_V
  rw [constrainedGaps_empty]

lemma exists_pos_lower_bound {F : Set ℝ} (hFc : IsCompact F) (hF : F ⊆ Ioi 0) :
    ∃ m : ℝ, 0 < m ∧ F ⊆ Ici m := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, empty_subset _⟩
  obtain ⟨m, hmF, hmin⟩ := hFc.exists_isMinOn hne continuous_id.continuousOn
  exact ⟨m, hF hmF, fun t ht => isMinOn_iff.1 hmin t ht⟩

/-- `T_V ≤ T_F` (once the feasible set is nonempty). -/
theorem T_V_le_constrainedThreshold (prob : FixedWeightProblem) {cTilde : ℝ} {F : Set ℝ}
    (hne : (constrainedGaps prob cTilde F).Nonempty) :
    prob.T_V cTilde ≤ constrainedThreshold prob cTilde F := by
  refine le_csInf hne fun τ hτ => ?_
  obtain ⟨hτ0, g, hg1, hg2, hg3⟩ := hτ
  unfold FixedWeightProblem.T_V
  exact csInf_le ⟨0, fun T hT => hT.1.le⟩ ⟨hτ0, g, hg1, hg2, fun t ht => hg3 t (Or.inr ht)⟩

/-- A feasible test on `X_τ` is feasible on `X_τ'` for `τ' ≥ τ`; hence a gap `τ > T_F` cannot carry a
crossing measure. -/
theorem le_constrainedThreshold_of_crossingMeasure (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde) {F : Set ℝ}
    (hne : (constrainedGaps prob cTilde F).Nonempty) {τ : ℝ}
    (meas : AdmissibleCrossingMeasure prob (cTilde / 12)) (hν : meas.ν (F ∪ Ici τ)ᶜ = 0) :
    τ ≤ constrainedThreshold prob cTilde F := by
  by_contra hlt
  push Not at hlt
  obtain ⟨τ', hτ', hτ'τ⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨hτ'0, g, hg⟩ := hτ'
  have hsub : F ∪ Ici τ ⊆ F ∪ Ici τ' := union_subset_union_right F (Ici_subset_Ici.2 hτ'τ.le)
  refine not_feasible_of_crossingMeasure prob (by linarith) (by linarith) meas hν
    (τ := τ) subset_union_right g ⟨hg.1, hg.2.1, fun t ht => hg.2.2 t (hsub ht)⟩

/-- **Attainment** (`ds:E`(b)): the constrained threshold is attained by a crossing measure on
`X_{T_F}` with `∫ w_* dν ≤ C₀`. -/
theorem exists_crossingMeasure_at_threshold (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetupCore prob cTilde β₀ T₀) {F : Set ℝ} (hFc : IsCompact F) (hF0 : F ⊆ Ici T₀)
    (hne : (constrainedGaps prob cTilde F).Nonempty)
    (hT₀V : T₀ < prob.T_V cTilde) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (F ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 ∧
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  set TF := constrainedThreshold prob cTilde F with hTF
  have hTVF : T₀ < TF := lt_of_lt_of_le hT₀V (T_V_le_constrainedThreshold prob hne)
  let τ : ℕ → ℝ := fun n => TF - (TF - T₀) / (n + 2)
  have hτ0 : ∀ n, T₀ ≤ τ n := fun n => by
    have : (TF - T₀) / (n + 2) ≤ TF - T₀ :=
      div_le_self (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    show T₀ ≤ TF - (TF - T₀) / (n + 2); linarith
  have hτlt : ∀ n, τ n < TF := fun n => by
    have : 0 < (TF - T₀) / (n + 2) :=
      div_pos (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    show TF - (TF - T₀) / (n + 2) < TF; linarith
  have hτmono : Monotone τ := by
    refine monotone_nat_of_le_succ fun n => ?_
    show TF - (TF - T₀) / (n + 2) ≤ TF - (TF - T₀) / ((n + 1 : ℕ) + 2)
    have h1 : (TF - T₀) / (((n + 1 : ℕ) : ℝ) + 2) ≤ (TF - T₀) / (n + 2) := by
      refine div_le_div_of_nonneg_left (by linarith)
        (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) ?_
      push_cast; linarith
    linarith
  let X : ℕ → Set ℝ := fun n => F ∪ Ici (τ n)
  have hXc : ∀ n, IsClosed (X n) := fun n => hFc.isClosed.union isClosed_Ici
  have hXa : Antitone X := fun m n hmn =>
    union_subset_union_right F (Ici_subset_Ici.2 (hτmono hmn))
  have hX0 : X 0 ⊆ Ici T₀ := union_subset hF0 (Ici_subset_Ici.2 (hτ0 0))
  have hns : ∀ n, NoSpanFeasible prob cTilde β₀ (X n) := by
    intro n B hB l μ hnn
    by_contra hpos
    have hmem := spanTest_mem prob S.ha S.ha_pos (β₀ := β₀) hB l μ
    have hτn : τ n ∈ constrainedGaps prob cTilde F :=
      ⟨lt_of_lt_of_le S.hT₀pos (hτ0 n), _, hmem, not_le.1 hpos, hnn⟩
    have : TF ≤ τ n := csInf_le ⟨0, fun t ht => ht.1.le⟩ hτn
    linarith [hτlt n]
  obtain ⟨meas, hν, hint, hle⟩ := theorem_E_a_decreasing prob S hXc hXa hX0 hns
  have hInter : (⋂ n, X n) = F ∪ Ici TF := by
    refine Subset.antisymm (fun y hy => ?_) (fun y hy => mem_iInter.2 fun n => ?_)
    · by_cases hyF : y ∈ F
      · exact Or.inl hyF
      · refine Or.inr ?_
        have hall : ∀ n, τ n ≤ y := fun n => by
          rcases mem_iInter.1 hy n with h | h
          · exact absurd h hyF
          · exact h
        by_contra hlt0
        have hlt : y < TF := by simpa using hlt0
        obtain ⟨n, hn⟩ := exists_nat_gt ((TF - T₀) / (TF - y))
        have hpos : 0 < TF - y := by linarith
        have : (TF - T₀) / (n + 2) < TF - y := by
          rw [div_lt_iff₀ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
          have := (div_lt_iff₀ hpos).mp hn
          nlinarith
        have h2 := hall n
        have : y < τ n := by show y < TF - (TF - T₀) / (n + 2); linarith
        linarith
    · rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (le_trans (hτlt n).le hy)
  exact ⟨meas, by rw [← hInter]; exact hν, hint, hle⟩

/-! ### The theorem -/

/-- **Theorem E(b)** (`ds:E`(b), `dual_spectrum.tex`) at every fixed weight `(w, Q)` with `c̃ > 0`,
`c̃ ≥ 12 S` and `T_V(c̃) > 0`, for a compact `F ⊂ (0, ∞)`:

1. `T_V ≤ T_F < ∞`;
2. `T_F = max {τ > 0 : a positive crossing measure carried by F ∪ [τ, ∞) exists}`;
3. for every `DualSetupCore prob cTilde β₀ T₀` with `F ⊆ [T₀, ∞)` and `T₀ < T_V`, the maximum is
   attained by a crossing measure on `X_{T_F}` with `∫ w_* dν_* ≤ C₀`;
4. every crossing measure carried by `X_τ`, `τ > T_V`, has `ν(F) > 0` (for `F = {t₁}`:
   `ν({t₁}) > 0`). -/
theorem theorem_E_b_compact (prob : FixedWeightProblem) {cTilde : ℝ} (hc_pos : 0 < cTilde)
    (hc : 12 * prob.totalShift ≤ cTilde) {F : Set ℝ} (hFc : IsCompact F) (hF : F ⊆ Ioi 0)
    (hTV : 0 < prob.T_V cTilde) :
    (prob.T_V cTilde ≤ constrainedThreshold prob cTilde F ∧
      (constrainedGaps prob cTilde F).Nonempty) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0} (constrainedThreshold prob cTilde F) ∧
    (∀ {β₀ T₀ : ℝ}, DualSetupCore prob cTilde β₀ T₀ → F ⊆ Ici T₀ → T₀ < prob.T_V cTilde →
      ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 ∧
        Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
        ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀) ∧
    (∀ τ : ℝ, prob.T_V cTilde < τ → ∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0 → 0 < meas.ν F) := by
  obtain ⟨τ₁, hτ₁, g₁, hg₁⟩ := exists_feasible_of_compact prob hc_pos hc hFc hF
  have hne : (constrainedGaps prob cTilde F).Nonempty := ⟨τ₁, hτ₁, g₁, hg₁⟩
  have hle := T_V_le_constrainedThreshold prob hne
  have hattain : ∀ {β₀ T₀ : ℝ}, DualSetupCore prob cTilde β₀ T₀ → F ⊆ Ici T₀ →
      T₀ < prob.T_V cTilde → ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 ∧
        Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
        ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ :=
    fun S hF0 hT₀V => exists_crossingMeasure_at_threshold prob S hFc hF0 hne hT₀V
  refine ⟨⟨hle, hne⟩, ⟨?_, fun τ hτ => ?_⟩, hattain, ?_⟩
  · -- membership: choose `T₀`, `β₀`
    obtain ⟨m, hm, hFm⟩ := exists_pos_lower_bound hFc hF
    set T₀ := min m (prob.T_V cTilde / 2) with hT₀def
    have hT₀pos : 0 < T₀ := lt_min hm (by linarith)
    have hT₀V : T₀ < prob.T_V cTilde := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    obtain ⟨β₀, hβ₀, hβ₀2, hβ₀t⟩ := exists_beta0 prob.w hT₀pos
    obtain ⟨meas, hν, -⟩ := hattain (β₀ := β₀) (T₀ := T₀) ⟨hc_pos, hc, hβ₀, hβ₀2, hβ₀t, hT₀pos⟩
      (fun t ht => (min_le_left _ _).trans (hFm ht)) hT₀V
    exact ⟨lt_of_lt_of_le hTV hle, meas, hν⟩
  · obtain ⟨-, meas, hν⟩ := hτ
    exact le_constrainedThreshold_of_crossingMeasure prob hc_pos hc hne meas hν
  · intro τ hτ meas hν
    by_contra h0
    have hF0 : meas.ν F = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h0)
    have hgap : meas.ν (Iio τ) = 0 := by
      refine measure_mono_null (fun t ht => ?_) (measure_union_null hF0 hν)
      by_cases htF : t ∈ F
      · exact Or.inl htF
      · refine Or.inr fun hX => ?_
        rcases hX with h | h
        · exact htF h
        · exact absurd (mem_Iio.1 ht) (not_lt.2 h)
    have := (Duality.proposition_D1 prob hc hc_pos (lt_trans hTV hτ) ⟨meas, hgap⟩).2.1
    unfold FixedWeightProblem.T_V at hτ this
    linarith

/-- **Theorem E(b) for `F = ∅`**: `T_∅ = T_V`, and the attaining crossing measure on `[T_V, ∞)` has
`min supp ν_* = T_V` (every `[T_V, T_V + ε)` has positive mass). -/
theorem theorem_E_b_compact_empty (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (S : DualSetup prob cTilde β₀ T₀) :
    constrainedThreshold prob cTilde ∅ = prob.T_V cTilde ∧
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (Iio (prob.T_V cTilde)) = 0 ∧
      (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (prob.T_V cTilde + ε))) ∧
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 prob (cTilde / 12) β₀ := by
  refine ⟨constrainedThreshold_empty prob cTilde, ?_⟩
  obtain ⟨-, -, hat, -⟩ := theorem_E_b_compact prob S.hc_pos S.hc (F := ∅) isCompact_empty
    (empty_subset _) (lt_trans S.hT₀pos S.hT₀V)
  obtain ⟨meas, hν, hint, hle⟩ := hat S.toCore (empty_subset _) S.hT₀V
  rw [constrainedThreshold_empty, empty_union, compl_Ici] at hν
  refine ⟨meas, hν, fun ε hε => ?_, hint, hle⟩
  by_contra hcon
  have hz : meas.ν (Iio (prob.T_V cTilde + ε)) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hcon)
  obtain ⟨_, hle', _⟩ := Duality.proposition_D1 prob (cTilde := cTilde) (τ := prob.T_V cTilde + ε)
    S.hc S.hc_pos (by linarith [lt_trans S.hT₀pos S.hT₀V]) ⟨meas, hz⟩
  linarith

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E_b_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E_b_compact

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_E_b_compact_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_E_b_compact_empty

end FormalResearch.ModularBootstrap.FixedWeight
