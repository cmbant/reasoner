module

public import FormalResearch.ModularBootstrap.TwoLevel.WOneFiveClark
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransferW

/-!
# Proposition W1.5(c) at every weight: the two-level boundary with lower remainder `-O(1)` (`upper_transfer.tex`, `wone:clark`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition W1.5(c), last sentence (see `WOneFiveClark.lean`).
`wone_clark_two_level_boundary_all`: the statement of `wone_clark_two_level_boundary` with the hypothesis `prob.w = 1`
removed: the lower half is `theorem_W1prime_two_fixed` (every fixed-weight problem) and the upper half is Theorem 2.5
at every weight, `theorem_two_five_all` (Theorem T2 at every weight, `twoSimpleZeroTransfer_all`).

All results are proved unconditionally.
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special Crossing

/-- **Proposition W1.5(c)** (`wone:clark`) at every fixed weight `(w, Q)`: the two-level boundary with lower remainder
`-O(1)`. -/
theorem wone_clark_two_level_boundary_all (prob : FixedWeightProblem) {A₁ R_off : ℝ}
    (hA₁ : A₁ < Aopt) (hR_off : 0 ≤ R_off) :
    ∃ D₂ : ℝ, ∀ δ : ℝ, 0 < δ → ∀ᶠ c' : ℝ in atTop,
      (∀ T ∈ twoLevelThresholds prob A₁ R_off c', levelTime (A2star A₁) c' - D₂ ≤ T) ∧
      (∃ T ∈ twoLevelThresholds prob A₁ R_off c', T ≤ levelTime (A2star A₁ + δ) c') ∧
      levelTime (A2star A₁) c' - D₂ ≤ sInf (twoLevelThresholds prob A₁ R_off c') ∧
      sInf (twoLevelThresholds prob A₁ R_off c') ≤ levelTime (A2star A₁ + δ) c' := by
  obtain ⟨c₂, D₂, hlow⟩ := theorem_W1prime_two_fixed prob hA₁ hR_off
  refine ⟨D₂, fun δ hδ => ?_⟩
  filter_upwards [theorem_two_five_all prob hA₁ hδ, eventually_ge_atTop c₂] with c' h25 hc'
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
info: 'FormalResearch.ModularBootstrap.TwoLevel.wone_clark_two_level_boundary_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.wone_clark_two_level_boundary_all
