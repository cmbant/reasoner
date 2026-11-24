module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoLevelLower
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransferProof
public import FormalResearch.ModularBootstrap.TwoLevel.CorollaryTwoFour

/-!
# Proposition W1.5(c): the two-level boundary has lower remainder `-O(1)` (`upper_transfer.tex`, `wone:clark`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition W1.5(c), last sentence: sharp leading-order
two-level exclusion above `A_2^*(A₁)` (Theorem 2.5, `gt:2.5`; matching crossing measures below `A_2^*(A₁)`, Corollary 2.4,
`gt:2.4`) together with `wone:genlower`(2) (`theorem_W1prime_two_fixed`) say that the two-level boundary has lower
remainder `-O_{w,Q,A₁,R_off}(1)` for `|r_{c'}| ≤ R_off`.

* `twoLevelThresholds prob A₁ R_off c'`: the thresholds `T` for which some weakly feasible `g` at `(c'/12, T)` is
  nonnegative at a level `t₁` with `|t₁ - (ξ̄ c' + A₁ c'^{1/3})| ≤ R_off`;
* `wone_clark_two_level_boundary`: for `prob.w = 1`, `A₁ < A_opt`, `R_off ≥ 0` there is `D₂` such that for every `δ > 0`,
  for all large `c'`: every threshold in `twoLevelThresholds` is `≥ ξ̄ c' + A_2^*(A₁) c'^{1/3} - D₂` (lower half,
  `theorem_W1prime_two_fixed`, valid for every fixed-weight problem), and some threshold is
  `≤ ξ̄ c' + (A_2^*(A₁) + δ) c'^{1/3}` (upper half, `theorem_two_five_w1`, pinned at offset `0`); hence the infimum
  lies in `[ξ̄ c' + A_2^*(A₁) c'^{1/3} - D₂, ξ̄ c' + (A_2^*(A₁) + δ) c'^{1/3}]`.

The crossing-measure half of the sentence is `corollary_two_four` (`prob.w = 1`) and is not repeated here.
`wone:genlower`(2) at general `(w, Q)` holds for every fixed-weight problem, whereas `gt:2.5` is proved here only at `w = 1`.
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special Crossing

/-- The thresholds of the pinned two-level problem at `(prob, A₁, R_off, c')`. -/
def twoLevelThresholds (prob : FixedWeightProblem) (A₁ R_off c' : ℝ) : Set ℝ :=
  {T | ∃ (g : ℝ → ℝ) (t₁ : ℝ), |t₁ - levelTime A₁ c'| ≤ R_off ∧ 0 ≤ g t₁ ∧
    prob.IsWeaklyFeasible (c' / 12) T g}

/-- **Proposition W1.5(c)** (`wone:clark`): the two-level boundary at `w = 1`, with lower remainder `-O(1)`. -/
theorem wone_clark_two_level_boundary (prob : FixedWeightProblem) (hw : prob.w = 1) {A₁ R_off : ℝ}
    (hA₁ : A₁ < Aopt) (hR_off : 0 ≤ R_off) :
    ∃ D₂ : ℝ, ∀ δ : ℝ, 0 < δ → ∀ᶠ c' : ℝ in atTop,
      (∀ T ∈ twoLevelThresholds prob A₁ R_off c', levelTime (A2star A₁) c' - D₂ ≤ T) ∧
      (∃ T ∈ twoLevelThresholds prob A₁ R_off c', T ≤ levelTime (A2star A₁ + δ) c') ∧
      levelTime (A2star A₁) c' - D₂ ≤ sInf (twoLevelThresholds prob A₁ R_off c') ∧
      sInf (twoLevelThresholds prob A₁ R_off c') ≤ levelTime (A2star A₁ + δ) c' := by
  obtain ⟨c₂, D₂, hlow⟩ := theorem_W1prime_two_fixed prob hA₁ hR_off
  refine ⟨D₂, fun δ hδ => ?_⟩
  filter_upwards [theorem_two_five_w1 prob hw hA₁ hδ, eventually_ge_atTop c₂] with c' h25 hc'
  have hL : ∀ T ∈ twoLevelThresholds prob A₁ R_off c', levelTime (A2star A₁) c' - D₂ ≤ T := by
    rintro T ⟨g, t₁, ht₁, hg, hwf⟩
    have := hlow c' hc' T g t₁ (by simpa [levelTime] using ht₁) hg hwf
    simpa [levelTime] using this
  obtain ⟨⟨g, hT, hv, hpin, hpos⟩, -⟩ := h25
  have hmem : levelTime (A2star A₁ + δ) c' ∈ twoLevelThresholds prob A₁ R_off c' :=
    ⟨g, levelTime A₁ c', by simpa using hR_off, hpin,
      (show prob.IsFeasible (c' / 12) (levelTime (A2star A₁ + δ) c') g from
        ⟨hT, hv, fun t ht => (hpos t ht).le⟩).isWeaklyFeasible⟩
  have hbdd : BddBelow (twoLevelThresholds prob A₁ R_off c') := ⟨_, hL⟩
  refine ⟨hL, ⟨_, hmem, le_rfl⟩, le_csInf ⟨_, hmem⟩ hL, csInf_le hbdd hmem⟩

end FormalResearch.ModularBootstrap.TwoLevel

/--
info: 'FormalResearch.ModularBootstrap.TwoLevel.wone_clark_two_level_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.wone_clark_two_level_boundary
