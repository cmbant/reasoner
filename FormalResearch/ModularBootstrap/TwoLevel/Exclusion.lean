module

public import FormalResearch.ModularBootstrap.TwoLevel.ExclusionChart
public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimumLimit

/-!
# Theorem 2.5: sharp leading-order two-level exclusion above `A₂*` (`virasoro_two_level.tex`, `gt:2.5`)

Notation: `t_i = ξ̄ c' + A_i c'^{1/3}` (`levelTime`), `a = c'/12`, `A₂* = A2star A₁`.

**Inputs.**
* `TwoSimpleZeroTransfer prob` (`ut:T2`, named hypothesis, `TwoLevel.TwoZeroTransfer`);
* Proposition 2.3 (`gt:2.3`), proved in `TwoLevel.WindowOptimum*`: `u₂*(K) < z₂`, `u₂*(K) → z₂`, with `∫ f_K` affine
  and increasing in `u₂`;
* Lemma FW-X (1) (`not_feasible_of_crossingMeasure`, unconditional);
* `TwoZeroNegativeVacuum` (named hypothesis, the window algebra of Step 1 of the proof of `gt:2.5`): for a
  Clark angle `α`, `K ≥ 3` and `u₂` with `∫ f_K(u₂) < 0`, there is an admissible two-simple-zero design `𝔇`
  (`TwoZeroDesign`) with second zero `q = u₂`, first zero `p < z₁(α)` and `V_𝔇 = ∫ W_𝔇 < 0`.  In the TeX this
  is `V_𝔇 → ∫ f_K` as `η_* → 0`, `N → ∞`, `u₁' → z₁` (Lemma E and the node sum of `ut:V`, `ut:E`).

**Results.**
* `exists_two_level_exclusion_functional`: for `A₁ < A_opt`, `δ > 0` and all large `c'` there is `g ∈ Ā`
  (`TestClass`) with `g_vac > 0`, `g(t₁) > 0` and `g > 0` on `[t₂, ∞)`, `t₂ = ξ̄ c' + (A₂* + δ) c'^{1/3}`;
* `theorem_two_five`: the same, and by Lemma FW-X (1) no crossing measure is supported on `{t₁} ∪ [t₂, ∞)`;
* `two_level_boundary_above`: every fixed `A₂ > A₂*(A₁)` is excluded;
* `twoZeroNegativeVacuum_hyp_satisfiable`: the hypotheses of `TwoZeroNegativeVacuum` are satisfiable.

All of these are conditional on `TwoSimpleZeroTransfer prob` and `TwoZeroNegativeVacuum`.  The proof differs from the
TeX only in Step 3: the first zero is fixed at `p = z₁ - r` (`r > 0` small), so the window limit at the single
point `u(t₁) → z₁` is enough and uniformity of `ut:T2` in `p` is not used.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Rigidity

/-- **Hypothesis (not formalised): the window algebra of Step 1 of the proof of `gt:2.5`.**  If `∫ f_K < 0` at the
second zero `u₂` (with `f_K` of `gt:2.3` at the Clark angle `α`), then some admissible two-simple-zero design with
second zero `q = u₂` and first zero `p < z₁(α)` has `∫ W_𝔇 < 0`.  In the TeX: `V_𝔇 → ∫ f_K` as `η_* → 0`,
`N → ∞`, `u₁' → z₁`, with `V_𝔇 ≤ ½ ∫ f_K` for a fixed small `z₁ - u₁'`. -/
def TwoZeroNegativeVacuum : Prop :=
  ∀ α : ℝ, Real.sin α ≠ 0 → ∀ K : ℕ, 3 ≤ K → ∀ u₂ : ℝ, windowInt α K u₂ < 0 →
    ∃ (n : ℕ) (_ : 1 ≤ n) (d : TwoZeroDesign n),
      d.Adm ∧ d.q = u₂ ∧ d.p < clarkNode α 1 ∧ ∫ u, d.Wr u < 0

/-- The functional of `gt:2.5`: for `A₁ < A_opt` and `δ > 0`, for all large `c'` there is `g ∈ Ā` with
`g_vac > 0`, `g(t₁) > 0` and `g > 0` on `[t₂, ∞)`, `t₂ = ξ̄ c' + (A₂*(A₁) + δ) c'^{1/3}`. -/
theorem exists_two_level_exclusion_functional (prob : FixedWeightProblem)
    (hT : TwoSimpleZeroTransfer prob) (hV : TwoZeroNegativeVacuum) {A₁ δ : ℝ} (hA₁ : A₁ < Aopt)
    (hδ : 0 < δ) :
    ∀ᶠ c' : ℝ in atTop, ∃ g : ℝ → ℝ, TestClass prob (c' / 12) g ∧ 0 < prob.gVac (c' / 12) g ∧
      0 < g (levelTime A₁ c') ∧ ∀ t, levelTime (A2star A₁ + δ) c' ≤ t → 0 < g t := by
  have hcs := cStar_pos
  have hu₁ : airyZero 1 < -A₁ / cStar := mem_gap_one_of_lt_Aopt hA₁
  set u₁ : ℝ := -A₁ / cStar with hu₁def
  set α : ℝ := clarkAngle u₁ with hαdef
  have hz₁ : clarkNode α 1 = u₁ := (clarkAngle_spec hu₁).2
  have hsin : Real.sin α ≠ 0 := sin_clarkAngle_ne_zero hu₁
  have hz₂ : clarkNode α 2 < 0 := clarkNode_two_lt_zero α
  have hA2 : A2star A₁ = -(cStar * clarkNode α 2) := by
    unfold A2star
    rw [← hu₁def, ← hαdef, abs_of_neg hz₂]; ring
  -- Proposition 2.3: choose `K` and `u₂`
  have hε : 0 < δ / (3 * cStar) := by positivity
  obtain ⟨K, hK3, hKclose⟩ : ∃ K : ℕ, 3 ≤ K ∧ clarkNode α 2 - δ / (3 * cStar) < windowOptimum α K := by
    have h := (tendsto_windowOptimum hsin).eventually
      (lt_mem_nhds (show clarkNode α 2 - δ / (3 * cStar) < clarkNode α 2 by linarith))
    exact (h.and (eventually_ge_atTop 3)).exists.imp fun K hK => ⟨hK.2, hK.1⟩
  set us : ℝ := windowOptimum α K with hus
  have hus_le : windowInt α K us ≤ 0 := (windowOptimum_isGreatest hsin hK3).1
  have hus_lt : us < clarkNode α 2 := windowOptimum_lt hsin hK3
  set u₂ : ℝ := us - δ / (6 * cStar) with hu₂
  have hslope := windowSlope_pos hsin hK3
  have hint : windowInt α K u₂ < 0 := by
    have h1 := windowInt_affine hsin hK3 u₂
    have h2 := windowInt_affine hsin hK3 us
    have : 0 < δ / (6 * cStar) := by positivity
    nlinarith
  have hu₂pos : -(cStar * u₂) < A2star A₁ + δ := by
    rw [hA2]
    have : δ / (3 * cStar) * cStar = δ / 3 := by field_simp
    have h6 : δ / (6 * cStar) * cStar = δ / 6 := by field_simp
    have hlt : cStar * (clarkNode α 2 - δ / (3 * cStar)) < cStar * us :=
      mul_lt_mul_of_pos_left hKclose hcs
    nlinarith
  -- the design and the transfer
  obtain ⟨n, hn, d, hd, hdq, hdp, hneg⟩ := hV α hsin K hK3 u₂ hint
  obtain ⟨X⟩ := hT n hn {d} (isCompactFamily_singleton d)
    (fun d' h => by rw [mem_singleton_iff.1 h]; exact hd)
  obtain ⟨κ, hκ, hvac⟩ := X.vac ⟨-∫ u, d.Wr u, by linarith, fun d' h => by
    rw [mem_singleton_iff.1 h]; linarith⟩
  have hw₁ : 0 < d.Wr u₁ := d.Wr_pos_of_gt hd (by rw [← hz₁]; exact hdp)
  have hwin := X.window (|u₁| + 1) (by positivity) (X.C₂ * d.Wr u₁ / 4)
    (by have := X.C₂_pos; positivity)
  have hulim := tendsto_uAiry_levelTime A₁
  have hWr_ev : ∀ᶠ c : ℝ in atTop, d.Wr u₁ / 2 < d.Wr (uAiry c (levelTime A₁ c)) :=
    (d.continuous_Wr.continuousAt.tendsto.comp hulim).eventually (lt_mem_nhds (by linarith))
  have hIcc : ∀ᶠ c : ℝ in atTop, uAiry c (levelTime A₁ c) ∈ Icc (-(|u₁| + 1)) (|u₁| + 1) :=
    hulim.eventually (Icc_mem_nhds (by linarith [neg_abs_le u₁]) (by linarith [le_abs_self u₁]))
  have hpt := eventually_tAiry_add_one_le_levelTime (u := u₂) (B := A2star A₁ + δ)
    (by linarith)
  filter_upwards [eventually_ge_atTop X.c₀, hwin, hWr_ev, hIcc, hpt, eventually_le_levelTime A₁ 1,
    eventually_ge_atTop (12 * prob.totalShift), eventually_gt_atTop (0 : ℝ)] with c hc hw hWr hI hpt'
    ht1 hshift hc0
  have hF := X.F_pos hc
  have hC₂ := X.C₂_pos
  refine ⟨X.g d c, X.testClass c hc d rfl, ?_, ?_, ?_⟩
  · have := hvac c hc d rfl
    have h3 : 0 < c ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hc0 _
    exact lt_of_lt_of_le (by positivity) this
  · -- `g(t₁) > 0` from the window limit at `u(t₁) → z₁`
    set t₁ : ℝ := levelTime A₁ c with ht₁
    have ht0 : 0 ≤ t₁ := by linarith
    have hψ := psiAiry_uAiry (prob := prob) (g := X.g d c) hc0 ht0
    have hw' := hw d rfl _ hI
    have hlow : 0 < (X.F c)⁻¹ * psiAiry prob c (X.g d c) (uAiry c t₁) := by
      have := (abs_le.1 hw').1
      have h2 : 0 < X.C₂ * d.Wr u₁ := mul_pos hC₂ hw₁
      nlinarith [mul_lt_mul_of_pos_left hWr hC₂]
    have hpsi : 0 < psiAiry prob c (X.g d c) (uAiry c t₁) := by
      by_contra hle
      push Not at hle
      have := mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 hF).le hle
      linarith
    rw [hψ] at hpsi
    have hV0 : 0 ≤ prob.cardyV (c / 12) t₁ := prob.cardyV_nonneg (by linarith) ht0
    have hJ : 0 < jAiry c t₁ := jAiry_pos hc0 (by linarith)
    by_contra hle
    push Not at hle
    have h1 : X.g d c t₁ * prob.cardyV (c / 12) t₁ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hV0
    have := mul_nonpos_of_nonpos_of_nonneg h1 hJ.le
    linarith
  · intro t ht
    refine X.pos c hc d rfl t ?_
    rw [hdq]; linarith

/-- **Theorem 2.5** (`virasoro_two_level.tex`, `gt:2.5`): sharp leading-order two-level exclusion above `A₂*`.
Fix `A₁ < A_opt` and `δ > 0`, `t₁ = ξ̄ c' + A₁ c'^{1/3}`, `t₂ = ξ̄ c' + (A₂*(A₁) + δ) c'^{1/3}`.  For all large `c'`
there is `g ∈ Ā` with `g(t₁) ≥ 0`, `g > 0` on `[t₂, ∞)` and `g_vac > 0` (indeed `g(t₁) > 0`), and by Lemma FW-X (1)
no crossing measure at central charge `c'` is supported on `{t₁} ∪ [t₂, ∞)`.  Conditional on `ut:T2`
(`TwoSimpleZeroTransfer prob`) and the window algebra `TwoZeroNegativeVacuum`; Proposition 2.3 is proved. -/
theorem theorem_two_five (prob : FixedWeightProblem) (hT : TwoSimpleZeroTransfer prob)
    (hV : TwoZeroNegativeVacuum) {A₁ δ : ℝ} (hA₁ : A₁ < Aopt) (hδ : 0 < δ) :
    ∀ᶠ c' : ℝ in atTop,
      (∃ g : ℝ → ℝ, TestClass prob (c' / 12) g ∧ 0 < prob.gVac (c' / 12) g ∧
        0 ≤ g (levelTime A₁ c') ∧ ∀ t, levelTime (A2star A₁ + δ) c' ≤ t → 0 < g t) ∧
      ∀ meas : AdmissibleCrossingMeasure prob (c' / 12),
        ¬ meas.ν ({levelTime A₁ c'} ∪ Ici (levelTime (A2star A₁ + δ) c'))ᶜ = 0 := by
  filter_upwards [exists_two_level_exclusion_functional prob hT hV hA₁ hδ,
    eventually_ge_atTop (12 * prob.totalShift), eventually_gt_atTop (0 : ℝ)] with c hg hshift hc0
  refine ⟨?_, fun meas hν => ?_⟩
  · obtain ⟨g, h1, h2, h3, h4⟩ := hg
    exact ⟨g, h1, h2, h3.le, fun t ht => h4 t ht⟩
  · obtain ⟨g, h1, h2, h3, h4⟩ := hg
    refine not_feasible_of_crossingMeasure prob (by linarith) (by linarith) meas hν
      (subset_union_right (s := {levelTime A₁ c})) g ⟨h1, h2, ?_⟩
    rintro t (rfl | ht)
    · exact h3.le
    · exact (h4 t ht).le

/-- **Leading-order boundary**: every fixed `A₂ > A₂*(A₁)` is excluded (no crossing measure is supported on
`{t₁} ∪ [t₂, ∞)`, `t_i = ξ̄ c' + A_i c'^{1/3}`, for all large `c'`); every `A₂ < A₂*(A₁)` is permitted by
`corollary_two_four`. -/
theorem two_level_boundary_above (prob : FixedWeightProblem) (hT : TwoSimpleZeroTransfer prob)
    (hV : TwoZeroNegativeVacuum) {A₁ A₂ : ℝ} (hA₁ : A₁ < Aopt) (hA₂ : A2star A₁ < A₂) :
    ∀ᶠ c' : ℝ in atTop, ∀ meas : AdmissibleCrossingMeasure prob (c' / 12),
      ¬ meas.ν ({levelTime A₁ c'} ∪ Ici (levelTime A₂ c'))ᶜ = 0 := by
  have h := theorem_two_five prob hT hV hA₁ (sub_pos.2 hA₂)
  rw [add_sub_cancel] at h
  exact h.mono fun _ hc => hc.2

/-- Non-vacuity of `TwoZeroNegativeVacuum`: its hypothesis `∫ f_K(u₂) < 0` is satisfiable. -/
theorem twoZeroNegativeVacuum_hyp_satisfiable :
    ∃ (α : ℝ) (K : ℕ) (u₂ : ℝ), Real.sin α ≠ 0 ∧ 3 ≤ K ∧ windowInt α K u₂ < 0 := by
  have hα : Real.sin (Real.pi / 2) ≠ 0 := by simp
  have hK : 3 ≤ 3 := le_rfl
  have hs := windowSlope_pos hα hK
  refine ⟨Real.pi / 2, 3, -(|windowInt (Real.pi / 2) 3 0| + 1) /
    (windowInt (Real.pi / 2) 3 1 - windowInt (Real.pi / 2) 3 0), hα, hK, ?_⟩
  rw [windowInt_affine hα hK]
  have : -(|windowInt (Real.pi / 2) 3 0| + 1) / (windowInt (Real.pi / 2) 3 1 - windowInt (Real.pi / 2) 3 0) *
      (windowInt (Real.pi / 2) 3 1 - windowInt (Real.pi / 2) 3 0) =
      -(|windowInt (Real.pi / 2) 3 0| + 1) := div_mul_cancel₀ _ hs.ne'
  rw [this]
  nlinarith [le_abs_self (windowInt (Real.pi / 2) 3 0)]

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.exists_two_level_exclusion_functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_two_level_exclusion_functional

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_two_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_two_five

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.two_level_boundary_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_level_boundary_above

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroNegativeVacuum_hyp_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroNegativeVacuum_hyp_satisfiable

end FormalResearch.ModularBootstrap.TwoLevel
