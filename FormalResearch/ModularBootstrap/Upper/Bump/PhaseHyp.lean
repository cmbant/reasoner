module

public import FormalResearch.ModularBootstrap.Upper.Bump.Phase
public import FormalResearch.ModularBootstrap.Upper.Ramped.PhaseUniform

/-!
# The bumped comb satisfies `PhaseHyp` (`fw:e3.4`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, "Edge-phase stability" (`fw:e3.4`).

`bumped_phaseHyp`: if the base finite modification satisfies `Ramped.PhaseHyp c' f N₀ η₀ σ₀ ε₀ P` then the bumped comb
with any cut `N ≥ N₀` satisfies `PhaseHyp c' f N η₀ σ' ε' (P + 1)`, for `c'` large, with a threshold independent of
the base data, the cuts and `P`.  Hence the whole phase package (`Ramped.phase_package`, `Ramped.phase_k7`; the
order-`p` version is the one of the order-`p` transform package) applies to the bumped comb with total pair change
`P + 1`.  This file only wires the comb-level estimates `bumped_pairChange` and `bumped_admissible`.

All results are proved unconditionally.
-/

@[expose] public section

open Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Bump

open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Ramped

/-- **`fw:e3.4` ⇒ `PhaseHyp`.**  The bump adds at most `1` to the total pair change (it adds `O(1/c')`). -/
theorem bumped_phaseHyp (d : BumpData) (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N₀ N : ℕ) (σ₀ ε₀ : ℕ → ℝ) (P : ℝ), PhaseHyp c' f N₀ η₀ σ₀ ε₀ P → N₀ ≤ N →
      PhaseHyp c' f N η₀ (bumpSigma c' N₀ σ₀) (bumpEps d c' N₀ η₀ ε₀) (P + 1) := by
  filter_upwards [bumped_pairChange d hη₀0 hη₀1, bumped_admissible d f hf hη₀0 hη₀1,
    eventually_ge_atTop (max 1 (pairChangeC d))] with c' hpc hadm hc N₀ N σ₀ ε₀ P ⟨hfN₀, hA, hP⟩ hN
  have hc' : 0 < c' := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hc)
  refine ⟨hfN₀.trans hN, hadm N₀ N σ₀ ε₀ hfN₀ hN hA, ?_⟩
  have h1 := hpc f N₀ N σ₀ ε₀ hfN₀ hN
  have h2 : pairChangeC d / c' ≤ 1 := by
    rw [div_le_one hc']
    exact (le_max_right _ _).trans hc
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bumped_phaseHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumped_phaseHyp

end FormalResearch.ModularBootstrap.Upper.Bump
