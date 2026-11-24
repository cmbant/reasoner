module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityLow

/-!
# A measure with the ideal inequalities is the Clark measure (`virasoro_two_level.tex`, `gt:2.6`, Steps 3-5)

`measure_eq_clarkMeasure`: let `ν` be a locally finite measure carried by `{z₁} ∪ (-∞, z₂]` (`z_n = z_n(α)`) satisfying
the ideal inequality `∫ cutoff_{A,B} F_δ dν ≤ ∫ F_δ` (`IdealIneq`) for every admissible ideal datum `δ`, with
`B = z₁ + 1`.  Then `ν` is the Clark measure `Σ_n δ_{z_n}/K_n`:

1. `concentration_nodes`: `ν` is carried by the nodes (windows `clarkDatum α z₁ z₂ 0 K`);
2. `ν{z_n} ≤ 1/K_n` for every `n` (`weight_le_one_of_up`; windows `clarkDatum α p q m K`, `K → ∞`, with the zero
   pattern of `up_family`: `n = 1`: `p ∈ (z₂, z₁)`, `q = z₂`; `n = 2`: `p = z₁`, `q ∈ (z₂, min(z₁, 0))`;
   `n ≥ 3`: `p = z₁`, `q = z₂`, ideal pair at `a_n`);
3. `ν{z_n} ≥ 1/K_n` for every `n` (`low_family`; windows `lowDatum α M`, `M → ∞`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty
open FormalResearch.ModularBootstrap.Upper.Rigidity

lemma cNode_le_clarkNode_one (α : ℝ) (i : ℕ) : cNode α i ≤ clarkNode α 1 := by
  have := (cNode_strictAnti α).antitone (Nat.zero_le i)
  simpa [cNode] using this

/-- **Upper bound for the weight at `z_n`.** -/
theorem weight_le_one_of_up {α : ℝ} (hα : Real.sin α ≠ 0) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (hconc : ν (Set.range (cNode α))ᶜ = 0)
    (hI : ∀ δ : IdealDatum, δ.Adm → IdealIneq ν (clarkNode α 1 + 1) δ.win δ.q (∫ u, δ.win u))
    {p q : ℝ} {m n : ℕ} (hn : 1 ≤ n) (hm : UpIdx m n) (hqp : q < p) (hq0 : q < 0)
    (hzero : ∀ n', 1 ≤ n' → n' ≤ 2 → n' ≠ n → clarkNode α n' = p ∨ clarkNode α n' = q)
    (hpos : 0 < (clarkNode α n - p) * (clarkNode α n - q)) :
    (ν {cNode α (n - 1)}).toReal ≤ cWeight α (n - 1) := by
  obtain ⟨hτpos, hτnn, hlim⟩ := up_family hα hn hm hzero hpos
  have hadm : ∀ K, max 2 n ≤ K → (clarkDatum α p q m K).Adm := fun K hK =>
    clarkDatum_adm α hqp hq0 (by omega) (by
      rcases hm with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨by omega, by omega⟩)
  refine weight_le_one_of_family (z := cNode α) (w := cWeight α) (cWeight_pos α) (tendsto_cNode α)
    (cNode_strictAnti α) hconc (B := clarkNode α 1 + 1)
    (fun i => (cNode_le_clarkNode_one α i).trans (by linarith))
    (G := fun K => (clarkDatum α p q m K).win) (fun K => IdealDatum.continuous_win _)
    (q := fun _ => q) (V := fun K => ∫ u, (clarkDatum α p q m K).win u)
    (fun K u hu => IdealDatum.win_nonneg_of_le _ hu hqp)
    (eventually_atTop.2 ⟨max 2 n, fun K hK => hI _ (hadm K hK)⟩)
    (τ := fun K i => (clarkDatum α p q m K).tau α i)
    (eventually_atTop.2 ⟨max 2 n, fun K hK =>
      (clarkDatum α p q m K).hasSum_tau hα (show 2 ≤ K by omega)⟩)
    (Eventually.of_forall fun K i => (IdealDatum.win_cNode_mul_cWeight _ α i).symm)
    hτpos hτnn hlim

/-- **Lower bound for the weight at `z_n`**, given the upper bounds for all weights. -/
theorem weight_ge_one_of_low {α : ℝ} (hα : Real.sin α ≠ 0) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (hconc : ν (Set.range (cNode α))ᶜ = 0)
    (hI : ∀ δ : IdealDatum, δ.Adm → IdealIneq ν (clarkNode α 1 + 1) δ.win δ.q (∫ u, δ.win u))
    (hxle : ∀ i, (ν {cNode α i}).toReal ≤ cWeight α i) (j : ℕ) :
    cWeight α j ≤ (ν {cNode α j}).toReal := by
  obtain ⟨hneg, hlim⟩ := low_family hα j
  have hqp : ∀ M : ℕ, (lowDatum α M).q < (lowDatum α M).p := fun M => by
    show clarkNode α (M + 1) < clarkNode α 1 + 1
    have := cNode_le_clarkNode_one α M
    simp only [cNode] at this
    linarith
  refine weight_ge_one_of_family (z := cNode α) (w := cWeight α) (cWeight_pos α) (tendsto_cNode α)
    (cNode_strictAnti α) hconc hxle (B := clarkNode α 1 + 1)
    (fun i => (cNode_le_clarkNode_one α i).trans (by linarith))
    (G := fun M => (lowDatum α M).win) (fun M => IdealDatum.continuous_win _)
    (q := fun M => (lowDatum α M).q) (V := fun M => ∫ u, (lowDatum α M).win u)
    (fun M u hu => IdealDatum.win_nonneg_of_le _ hu (hqp M))
    (eventually_atTop.2 ⟨2, fun M hM => hI _ (lowDatum_adm α hM)⟩)
    (τ := fun M i => (lowDatum α M).tau α i)
    (eventually_atTop.2 ⟨2, fun M hM => (lowDatum α M).hasSum_tau hα (show 2 ≤ M from hM)⟩)
    (Eventually.of_forall fun M i => (IdealDatum.win_cNode_mul_cWeight _ α i).symm)
    hneg hlim

/-- **A measure with the ideal inequalities is the Clark measure.** -/
theorem measure_eq_clarkMeasure {α : ℝ} (hα : Real.sin α ≠ 0) {ν : Measure ℝ}
    [IsLocallyFiniteMeasure ν] (hae : ∀ᵐ u ∂ν, u = clarkNode α 1 ∨ u ≤ clarkNode α 2)
    (hI : ∀ δ : IdealDatum, δ.Adm → IdealIneq ν (clarkNode α 1 + 1) δ.win δ.q (∫ u, δ.win u)) :
    ν = clarkMeasure α := by
  have hz1 : clarkNode α 2 < clarkNode α 1 := clarkNode_lt_of_lt le_rfl (by norm_num) α
  have hz2 : clarkNode α 2 < 0 := clarkNode_two_lt_zero α
  have hconc : ν (Set.range (cNode α))ᶜ = 0 := by
    refine concentration_nodes hα hae fun K hK => ?_
    have h := hI (clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 K)
      (clarkDatum_adm α hz1 hz2 (by omega) (Or.inl rfl))
    rwa [integral_conc hα hK] at h
  have hxle : ∀ i, (ν {cNode α i}).toReal ≤ cWeight α i := by
    intro i
    have hn : 1 ≤ i + 1 := by omega
    have e : i + 1 - 1 = i := by omega
    have key : ∀ {p q : ℝ} {m : ℕ}, q < p → q < 0 → UpIdx m (i + 1) →
        (∀ n', 1 ≤ n' → n' ≤ 2 → n' ≠ i + 1 → clarkNode α n' = p ∨ clarkNode α n' = q) →
        0 < (clarkNode α (i + 1) - p) * (clarkNode α (i + 1) - q) →
        (ν {cNode α i}).toReal ≤ cWeight α i := by
      intro p q m hqp hq0 hm hzero hpos
      have := weight_le_one_of_up hα hconc hI hn hm hqp hq0 hzero hpos
      rwa [e] at this
    rcases Nat.lt_or_ge i 2 with hi | hi
    · rcases Nat.lt_or_ge i 1 with hi0 | hi1
      · -- n = 1
        have hi0' : i = 0 := by omega
        subst hi0'
        refine key (p := (clarkNode α 1 + clarkNode α 2) / 2) (q := clarkNode α 2) (m := 0)
          (by linarith) hz2 (Or.inl ⟨by norm_num, rfl⟩) ?_ ?_
        · intro n' h1 h2 hne
          right
          have : n' = 2 := by omega
          rw [this]
        · show 0 < (clarkNode α 1 - (clarkNode α 1 + clarkNode α 2) / 2) * (clarkNode α 1 - clarkNode α 2)
          nlinarith
      · -- n = 2
        have hi1' : i = 1 := by omega
        subst hi1'
        refine key (p := clarkNode α 1) (q := (clarkNode α 2 + min (clarkNode α 1) 0) / 2) (m := 0)
          ?_ ?_ (Or.inl ⟨by norm_num, rfl⟩) ?_ ?_
        · have := min_le_left (clarkNode α 1) 0
          have h3 : clarkNode α 2 < min (clarkNode α 1) 0 := lt_min hz1 hz2
          linarith
        · have h3 : clarkNode α 2 < min (clarkNode α 1) 0 := lt_min hz1 hz2
          have := min_le_right (clarkNode α 1) 0
          linarith
        · intro n' h1 h2 hne
          left
          have : n' = 1 := by omega
          rw [this]
        · show 0 < (clarkNode α 2 - clarkNode α 1) *
            (clarkNode α 2 - (clarkNode α 2 + min (clarkNode α 1) 0) / 2)
          have h3 : clarkNode α 2 < min (clarkNode α 1) 0 := lt_min hz1 hz2
          nlinarith
    · -- n ≥ 3
      refine key (p := clarkNode α 1) (q := clarkNode α 2) (m := i + 1) hz1 hz2
        (Or.inr ⟨by omega, rfl⟩) ?_ ?_
      · intro n' h1 h2 hne
        rcases (by omega : n' = 1 ∨ n' = 2) with h | h
        · left; rw [h]
        · right; rw [h]
      · have : clarkNode α (i + 1) < clarkNode α 2 :=
          clarkNode_lt_of_lt (n := 2) (m := i + 1) (by norm_num) (by omega) α
        nlinarith
  exact eq_clarkMeasure_of_atoms α hconc fun i =>
    le_antisymm (hxle i) (weight_ge_one_of_low hα hconc hI hxle i)

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.weight_le_one_of_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weight_le_one_of_up

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.weight_ge_one_of_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weight_ge_one_of_low

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.measure_eq_clarkMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms measure_eq_clarkMeasure

end FormalResearch.ModularBootstrap.TwoLevel
