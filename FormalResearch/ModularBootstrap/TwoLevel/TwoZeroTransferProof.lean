module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransfer
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroPositivity
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuum
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroWindow
public import FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidity
public import FormalResearch.ModularBootstrap.Upper.Assembly.DesignG

/-!
# Theorem T2 at weight one (`upper_transfer.tex`, `ut:T2`), and Theorems 2.5, 2.6 at `w = 1`

`twoSimpleZeroTransfer_of_w1`: for `prob.w = 1`, `TwoSimpleZeroTransfer prob` holds.  The data of
`TwoZeroTransferData` are `F = twoZeroF prob`, `C₂ = twoZeroC₂`, `g d c = twoZeroG d c` (the functional
`½(h₂ - ĥ₂)`), with the fields supplied by the Regions I/II positivity, the window limit, the vacuum limsup and the
vacuum bound; the threshold `c₀` is the maximum of the eventual thresholds.  The corollaries drop the hypothesis
`TwoSimpleZeroTransfer`:

* `designPropertyP_twoZero_w1`: Property `sr:P` for the two-simple-zero windows;
* `theorem_two_five_w1`: Theorem 2.5 (`gt:2.5`) with the only hypothesis `prob.w = 1`;
* `theorem_two_six_w1`: Theorem 2.6 (`gt:2.6`) with the hypotheses `prob.w = 1` and `TwoZeroIdealApprox`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
open FormalResearch.ModularBootstrap.Upper.Hankel

/-- The weight-one functional `g = ½(h₂ - ĥ₂)` of `twoZeroG d c` (with `pairOdd`) at `t > 0` is half the real part
of `sech² B₂(x) - ĥ₂(t)`, `x = √(3t/c)`. -/
lemma twoZeroG_eq_half_re {n : ℕ} (d : TwoZeroDesign n) {c : ℝ} (hc : 0 < c)
    (hB : InnerCombHyp c (d.twoZeroComb c))
    {C : ℝ} (hd : DecayBound c C (combProfile c (d.twoZeroComb c))) {t : ℝ} (ht : 0 < t) :
    twoZeroG d c t =
      (sechSqProfile ((xOf c t : ℝ) : ℂ) * d.twoZeroComb c ((xOf c t : ℝ) : ℂ) -
        edgeHankel c (fun b => sechSqProfile b * d.twoZeroComb c b) t).re / 2 := by
  have he := hB.edgeHankel_eq hc hd ht
  have e1 : edgeHankel c (fun b => sechSqProfile b * d.twoZeroComb c b) t =
      (hankelTransform 1 (combProfile c (d.twoZeroComb c)) t : ℂ) := he
  rw [e1, Complex.sub_re, Complex.ofReal_re]
  unfold twoZeroG pairOdd combProfile combH0
  rfl

/-- The eventual form of the fields `testClass`, `decay`, `pos` of `TwoZeroTransferData`. -/
lemma twoZero_fields_eventually (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c : ℝ in atTop, 0 < c ∧ ∀ d ∈ 𝒦, TestClass prob (c / 12) (twoZeroG d c) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
        |twoZeroG d c t| ≤ C * Real.exp (-4 * π * Real.sqrt (c / 12 * t) - π * Real.sqrt (3 * t / c))) ∧
      ∀ t : ℝ, tAiry c d.q + 1 ≤ t → 0 < twoZeroG d c t := by
  filter_upwards [twoZero_pos_t hK hA, twoZeroComb_innerCombHyp hK hA,
    twoZeroComb_k7_membership_vacuum hw hK hA, eventually_gt_atTop (0 : ℝ)] with c hpos hI hK7 hc
  refine ⟨hc, fun d hd => ?_⟩
  obtain ⟨C, hC0, hd1, hd2, hT, -⟩ := hK7 d hd
  refine ⟨hT, ⟨C, hC0, fun t ht => ?_⟩, fun t ht => ?_⟩
  · have := (hd1.pairOdd hd2) t ht
    unfold decayEnv at this
    rw [decay_exponent_eq hc ht] at this
    have e : -(4 * π * √(c / 12 * t)) - π * xOf c t = -4 * π * √(c / 12 * t) - π * √(3 * t / c) := by
      unfold xOf; ring
    rw [e] at this
    exact this
  · have ht0 : 0 < t := lt_of_lt_of_le (by linarith [tAiry_nonneg hc d.q]) ht
    rw [twoZeroG_eq_half_re d hc (hI d hd) hd1 ht0]
    have := hpos d hd t ht
    positivity

/-- A threshold for the `vac` field: either no `δ` exists, or `twoZero_vac_field_of_threshold` supplies one. -/
lemma twoZero_vac_threshold (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ c₂ : ℝ, (∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ) → ∃ κ : ℝ, 0 < κ ∧
      ∀ c : ℝ, c₂ ≤ c → ∀ d ∈ 𝒦, κ * c ^ ((3 : ℝ) / 2) ≤ prob.gVac (c / 12) (twoZeroG d c) := by
  by_cases hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ
  · obtain ⟨κ, hκ, c₁, h⟩ := twoZero_vac_field_of_threshold prob hw hK hA hδ
    exact ⟨c₁, fun _ => ⟨κ, hκ, fun c hc => h c₁ le_rfl c hc⟩⟩
  · exact ⟨0, fun h => absurd h hδ⟩

/-- **Theorem T2 at weight one** (`ut:T2`): the two-simple-zero transfer holds for every fixed-weight problem with
`prob.w = 1`. -/
theorem twoSimpleZeroTransfer_of_w1 (prob : FixedWeightProblem) (hw : prob.w = 1) :
    TwoSimpleZeroTransfer prob := by
  intro n _ 𝒦 hK hA
  obtain ⟨c₁, h1⟩ := eventually_atTop.mp (twoZero_fields_eventually prob hw hK hA)
  obtain ⟨c₂, h2⟩ := twoZero_vac_threshold prob hw hK hA
  have hc₀ : 0 < max (max c₁ c₂) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hge : ∀ c : ℝ, max (max c₁ c₂) 1 ≤ c → c₁ ≤ c ∧ c₂ ≤ c := fun c hc =>
    ⟨(le_max_left _ _).trans ((le_max_left _ _).trans hc),
      (le_max_right _ _).trans ((le_max_left _ _).trans hc)⟩
  refine ⟨{ c₀ := max (max c₁ c₂) 1
            C₂ := twoZeroC₂
            F := twoZeroF prob
            g := twoZeroG
            c₀_pos := hc₀
            C₂_pos := twoZeroC₂_pos
            F_asymp := twoZeroF_asymp_field prob hc₀
            testClass := fun c hc d hd => (h1 c (hge c hc).1).2 d hd |>.1
            decay := fun c hc d hd => ((h1 c (hge c hc).1).2 d hd).2.1
            pos := fun c hc d hd => ((h1 c (hge c hc).1).2 d hd).2.2
            window := twoZero_window_field prob hw hK hA
            integrable := twoZero_integrable_psiAiry prob hw hK hA
            limsup_le := twoZero_limsup_field prob hw hK hA
            vac := fun hδ => ?_ }⟩
  obtain ⟨κ, hκ, h⟩ := h2 hδ
  exact ⟨κ, hκ, fun c hc d hd => h c (hge c hc).2 d hd⟩

/-- `ut:T2` at weight one gives Property `sr:P` for the two-simple-zero windows. -/
theorem designPropertyP_twoZero_w1 {prob : FixedWeightProblem} (hw : prob.w = 1)
    (S : CrossingSequence prob) : DesignPropertyP S.μS twoZeroClass :=
  designPropertyP_twoZero (twoSimpleZeroTransfer_of_w1 prob hw) S

/-- **Theorem 2.5** (`gt:2.5`) at weight one, with no hypothesis besides `prob.w = 1`. -/
theorem theorem_two_five_w1 (prob : FixedWeightProblem) (hw : prob.w = 1) {A₁ δ : ℝ}
    (hA₁ : A₁ < Aopt) (hδ : 0 < δ) :
    ∀ᶠ c' : ℝ in atTop,
      (∃ g : ℝ → ℝ, TestClass prob (c' / 12) g ∧ 0 < prob.gVac (c' / 12) g ∧
        0 ≤ g (levelTime A₁ c') ∧ ∀ t, levelTime (A2star A₁ + δ) c' ≤ t → 0 < g t) ∧
      ∀ meas : AdmissibleCrossingMeasure prob (c' / 12),
        ¬ meas.ν ({levelTime A₁ c'} ∪ Ici (levelTime (A2star A₁ + δ) c'))ᶜ = 0 :=
  theorem_two_five_of_T2 prob (twoSimpleZeroTransfer_of_w1 prob hw) hA₁ hδ

/-- **Theorem 2.6** (`gt:2.6`) at weight one, with hypotheses `prob.w = 1` and `TwoZeroIdealApprox`. -/
theorem theorem_two_six_w1 {prob : FixedWeightProblem} (hw : prob.w = 1)
    (hAp : TwoZeroIdealApprox) {A₁ : ℝ} (hA : A₁ < Aopt) (S : TwoLevelSequence prob A₁) :
    IsVagueLimit atTop S.μ (clarkMeasure (clarkAngle (-A₁ / cStar))) :=
  theorem_two_six (twoSimpleZeroTransfer_of_w1 prob hw) hAp hA S

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoSimpleZeroTransfer_of_w1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoSimpleZeroTransfer_of_w1

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.designPropertyP_twoZero_w1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designPropertyP_twoZero_w1

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_two_five_w1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_two_five_w1

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_two_six_w1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_two_six_w1

end FormalResearch.ModularBootstrap.TwoLevel
