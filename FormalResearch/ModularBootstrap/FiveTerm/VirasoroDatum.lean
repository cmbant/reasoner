module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroCoupling
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroBounds
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroJet
public import FormalResearch.ModularBootstrap.FiveTerm.CombMinimum

/-!
# The Virasoro outer-function datum (FIVE-0 slice 4)

`Gout` (`VirasoroOuter`) satisfies every field of `OuterDatum Wslit Kedge g₁ ·` for some real `g₁ = Gout'(0)`:
holomorphy, boundary continuity, real symmetry, non-vanishing (`VirasoroOuter`), the jet at the tip (`VirasoroJet`),
the two-sided bounds at `z = 1` and `z = ±i` (`VirasoroBounds`), the slit modulus `|G(iy)| = W_slit(y)`
(`VirasoroSlit`) and the edge coupling (`VirasoroCoupling`).  With `comb_minimum_c0StarOf` this gives the exact
minimum of the comb functional `𝒥` over `H_adm` as `α_tip g₁`, `g₁ = Gout'(0)`.  Identifying `g₁ = g1Vir` is the
Hilbert-transform computation of `ctu:jets` (not in this file).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- **`OuterDatum` for the Virasoro weights**: `Gout` has all the properties of `G_outer`. -/
theorem gout_outerDatum : ∃ g1 : ℝ, OuterDatum Wslit Kedge g1 Gout := by
  obtain ⟨g1, C, r, hr, hj⟩ := gout_jet
  exact ⟨g1, {
    diff := gout_diff
    cont := gout_cont
    conj := fun z hz => gout_conj hz
    ne_zero := fun z hz => gout_ne_zero hz
    jet := ⟨C, r, hr, hj⟩
    near_one := gout_near_one
    near_I := gout_near_I
    modulus := fun y hy => gout_modulus hy
    coupling := fun y hy => gout_coupling hy }⟩

/-- The real number `g₁ = G_outer'(0)` of the Virasoro outer function (unique, by the jet). -/
noncomputable def g1Out : ℝ := Classical.choose gout_outerDatum

theorem gout_outerDatum_g1Out : OuterDatum Wslit Kedge g1Out Gout := Classical.choose_spec gout_outerDatum

/-- **Exact minimum of the comb functional** over the admissible class, for the Virasoro weights:
`α_tip · G_outer'(0)`. -/
theorem comb_minimum_virasoro :
    IsLeast {x : ℝ | ∃ (F : ℂ → ℂ) (c1 : ℝ), HAdm F c1 ∧ combJ Wslit Kedge F = x} (c0StarOf g1Out) :=
  comb_minimum_c0StarOf gout_outerDatum_g1Out


/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_outerDatum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_outerDatum

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.comb_minimum_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.comb_minimum_virasoro

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_modulus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_modulus

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_coupling

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_near_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_near_I

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_near_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_near_one

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_jet

end FormalResearch.ModularBootstrap.FiveTerm
