module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroBumpVacuum
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransfer
public import FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum
public import FormalResearch.ModularBootstrap.TwoLevel.IdealApproxTheorem

/-!
# Theorem T2 at every weight (`upper_transfer.tex`, `ut:T2`), and Theorems 2.5, 2.6 for every `(w, Q)`

`twoSimpleZeroTransfer_all`: `TwoSimpleZeroTransfer prob` holds for **every** fixed-weight problem (every `w ≥ 1`, every
`Q`).  The data of `TwoZeroTransferData` are `F = twoZeroF prob`, `C₂ = twoZeroC₂`, `g d c = twoZeroBumpG prob d c`, the
functional `½(h₂^{(p)} - 𝓗_w h₂^{(p)})` with `h₂^{(p)} = sech² T_{χ(p)} B₁^{(p)}` the comb of `ut:T2` with the detuning bump
of `fw:s1` applied to the finite modification `B₁` (`p = w - 1`, cut `bumpCut` above the bump block).  At `w = 1` the bump
data are not needed (`twoSimpleZeroTransfer_of_w1` uses the unbumped comb); the two constructions are different witnesses of
the same predicate.  The fields are supplied by `twoZeroBump_fields_eventually` (K7 at every weight, Regions I/II positivity),
`twoZeroBump_window_field`, `twoZeroBump_integrable`, `twoZeroBump_limsup_field`, `twoZeroBump_vac_field_of_threshold`.
The corollaries drop the hypothesis `TwoSimpleZeroTransfer`:

* `designPropertyP_twoZero_all`: Property `sr:P` for the two-simple-zero windows;
* `theorem_two_five_all`: Theorem 2.5 (`gt:2.5`) at every weight, no hypothesis;
* `theorem_two_six_all`, `tendsto_atom_weight_all`: Theorem 2.6 (`gt:2.6`) and its atom-weight corollary at every weight,
  no hypothesis (`TwoZeroIdealApprox` is proved: `twoZeroIdealApprox`).

All results are proved unconditionally.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership

/-- A threshold for the `vac` field: either no `δ` exists, or `twoZeroBump_vac_field_of_threshold` supplies one. -/
lemma twoZeroBump_vac_threshold (prob : FixedWeightProblem) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ c₂ : ℝ, (∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ) → ∃ κ : ℝ, 0 < κ ∧
      ∀ c : ℝ, c₂ ≤ c → ∀ d ∈ 𝒦, κ * c ^ ((3 : ℝ) / 2) ≤ prob.gVac (c / 12) (twoZeroBumpG prob d c) := by
  by_cases hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ
  · obtain ⟨κ, hκ, c₁, h⟩ := twoZeroBump_vac_field_of_threshold prob hK hA hδ
    exact ⟨c₁, fun _ => ⟨κ, hκ, fun c hc => h c₁ le_rfl c hc⟩⟩
  · exact ⟨0, fun h => absurd h hδ⟩

/-- **Theorem T2 at every weight** (`ut:T2`): the two-simple-zero transfer holds for every fixed-weight problem. -/
theorem twoSimpleZeroTransfer_all (prob : FixedWeightProblem) : TwoSimpleZeroTransfer prob := by
  intro n _ 𝒦 hK hA
  obtain ⟨c₁, h1⟩ := eventually_atTop.mp (twoZeroBump_fields_eventually prob hK hA)
  obtain ⟨c₂, h2⟩ := twoZeroBump_vac_threshold prob hK hA
  have hc₀ : 0 < max (max c₁ c₂) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hge : ∀ c : ℝ, max (max c₁ c₂) 1 ≤ c → c₁ ≤ c ∧ c₂ ≤ c := fun c hc =>
    ⟨(le_max_left _ _).trans ((le_max_left _ _).trans hc),
      (le_max_right _ _).trans ((le_max_left _ _).trans hc)⟩
  refine ⟨{ c₀ := max (max c₁ c₂) 1
            C₂ := twoZeroC₂
            F := twoZeroF prob
            g := twoZeroBumpG prob
            c₀_pos := hc₀
            C₂_pos := twoZeroC₂_pos
            F_asymp := twoZeroF_asymp_field prob hc₀
            testClass := fun c hc d hd => (h1 c (hge c hc).1).2 d hd |>.1
            decay := fun c hc d hd => ((h1 c (hge c hc).1).2 d hd).2.1
            pos := fun c hc d hd => ((h1 c (hge c hc).1).2 d hd).2.2
            window := twoZeroBump_window_field prob hK hA
            integrable := twoZeroBump_integrable prob hK hA
            limsup_le := twoZeroBump_limsup_field prob hK hA
            vac := fun hδ => ?_ }⟩
  obtain ⟨κ, hκ, h⟩ := h2 hδ
  exact ⟨κ, hκ, fun c hc d hd => h c (hge c hc).2 d hd⟩

/-- `ut:T2` at every weight gives Property `sr:P` for the two-simple-zero windows. -/
theorem designPropertyP_twoZero_all {prob : FixedWeightProblem}
    (S : CrossingSequence prob) : DesignPropertyP S.μS twoZeroClass :=
  designPropertyP_twoZero (twoSimpleZeroTransfer_all prob) S

/-- **Theorem 2.5** (`gt:2.5`) at every weight, with no hypothesis. -/
theorem theorem_two_five_all (prob : FixedWeightProblem) {A₁ δ : ℝ}
    (hA₁ : A₁ < Aopt) (hδ : 0 < δ) :
    ∀ᶠ c' : ℝ in atTop,
      (∃ g : ℝ → ℝ, TestClass prob (c' / 12) g ∧ 0 < prob.gVac (c' / 12) g ∧
        0 ≤ g (levelTime A₁ c') ∧ ∀ t, levelTime (A2star A₁ + δ) c' ≤ t → 0 < g t) ∧
      ∀ meas : AdmissibleCrossingMeasure prob (c' / 12),
        ¬ meas.ν ({levelTime A₁ c'} ∪ Ici (levelTime (A2star A₁ + δ) c'))ᶜ = 0 :=
  theorem_two_five_of_T2 prob (twoSimpleZeroTransfer_all prob) hA₁ hδ

/-- **Theorem 2.6** (`gt:2.6`) at every weight, with no hypothesis. -/
theorem theorem_two_six_all {prob : FixedWeightProblem} {A₁ : ℝ}
    (hA : A₁ < Aopt) (S : TwoLevelSequence prob A₁) :
    IsVagueLimit atTop S.μ (clarkMeasure (clarkAngle (-A₁ / cStar))) :=
  theorem_two_six_of_T2 (twoSimpleZeroTransfer_all prob) hA S

/-- The atom-weight corollary of Theorem 2.6 at every weight, with no hypothesis. -/
theorem tendsto_atom_weight_all {prob : FixedWeightProblem} {A₁ : ℝ}
    (hA : A₁ < Aopt) (S : TwoLevelSequence prob A₁) :
    Tendsto (fun j => (S.μ j {uAiry (S.c j) (S.t₁ j)}).toReal) atTop
      (𝓝 (clarkKernel (clarkAngle (-A₁ / cStar)) 1)⁻¹) :=
  tendsto_atom_weight_of_T2 (twoSimpleZeroTransfer_all prob) hA S

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoSimpleZeroTransfer_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoSimpleZeroTransfer_all

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.designPropertyP_twoZero_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designPropertyP_twoZero_all

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_two_five_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_two_five_all

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_two_six_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_two_six_all

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tendsto_atom_weight_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_atom_weight_all

end FormalResearch.ModularBootstrap.TwoLevel
