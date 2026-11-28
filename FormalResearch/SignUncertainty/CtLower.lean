module

public import FormalResearch.SignUncertainty.CtLowerDefs
public import FormalResearch.SignUncertainty.CtLowerChartGap
public import FormalResearch.SignUncertainty.CtKappaNeg
public import FormalResearch.SignUncertainty.Radii
public import FormalResearch.SignUncertainty.CtOuter
public import FormalResearch.SignUncertainty.CtCfuData
public import FormalResearch.SignUncertainty.HankelTransportInt
public import FormalResearch.SignUncertainty.RadialRigidity
public import FormalResearch.SignUncertainty.HankelEdgePhase
public import FormalResearch.SignUncertainty.HankelThresholds
public import FormalResearch.SignUncertainty.CtBandTop
public import FormalResearch.SignUncertainty.CtNodeLower

/-!
# `thm:ct-lower`: statement and threshold corollary

`constant_terms_lower.tex`, "Proof of the lower bound in `thm:ct-lower`(i)" (`eq:ct-lower`, left half).
For real `c ≥ c₀` and `ε = ±1`, every feasible threshold `T` of the Hankel problem satisfies
`Δ₅^ε(c) - C c⁻¹ ≤ T`, where
`Δ₅^ε(c) = c/π² + A c^{1/3} + c₀^ε + c₁^{Langer} c^{-1/3} + d₂^{*,ε} c^{-2/3}`,
`c₀^ε = θ₁^ε/π²`, `c₁^{Langer} = 9π²A²/25`, `d₂^{*,ε} = A(θ₁^ε + 12θ₃^ε/π²)`.

`CtLowerStatement` is defined here, proved unconditionally in `CtLowerFinal.ct_lower` via
`CtLowerLogFreeSkeleton` (`ct_lower_of_boas_logfree`), `CtWindowSigned.window_signed_proved`,
and `CtBoasExactAssembly.boas_sharp_proved`; `ct_lower_hankelT` deduces `Δ₅^ε(c) - C c⁻¹ ≤ T_c^ε`.
The concrete objects `ctGap` and `ctBudget` live in `CtLowerDefs`.
-/

@[expose] public section

open scoped Real
open Filter Topology

namespace FormalResearch.SignUncertainty

/-- **`thm:ct-lower` (`eq:ct-lower`, left half), the statement:** non-effective `c₀, C` such that for real `c ≥ c₀` and
`ε = ±1`, every feasible threshold is at least `Δ₅^ε(c) - C c⁻¹` (equivalently, `Δ₅^ε(c) - C c⁻¹ ≤ T_c^ε`
when a feasible threshold exists). -/
def CtLowerStatement : Prop :=
  ∃ c₀ C : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ (T : ℝ) (f : ℝ → ℝ),
    IsHankelFeasible c ε T f → ctDelta5 ε c - C * c⁻¹ ≤ T

/-- Corollary in the paper's log-free form: `Δ₅^ε(c) - C c⁻¹ ≤ T_c^ε` once a feasible threshold exists for the given
`c` (for large `c` this is `HbThresholdsUpper`, `u1co:O9p`). -/
theorem ct_lower_hankelT (h : CtLowerStatement) :
    ∃ c₀ C : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      (∃ T f, IsHankelFeasible c ε T f) →
        ctDelta5 ε c - C * c⁻¹ ≤ hankelT ε c := by
  obtain ⟨c₀, C, hC⟩ := h
  refine ⟨c₀, C, fun c hc ε hε hne => ?_⟩
  exact le_csInf (by obtain ⟨T, f, hf⟩ := hne; exact ⟨T, f, hf⟩)
    fun T ⟨f, hf⟩ => hC c hc ε hε T f hf

/-- info: 'FormalResearch.SignUncertainty.ct_lower_hankelT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ct_lower_hankelT

end FormalResearch.SignUncertainty
