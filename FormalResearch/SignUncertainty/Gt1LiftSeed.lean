module

public import FormalResearch.SignUncertainty.Gt1Identify
public import FormalResearch.SignUncertainty.Gt1FromSeed

/-!
# `GT.1` bounds for `liftW` of an `AiryTailSymbolSeed`

`gt1Bounds_of_seed` (`Gt1FromSeed.lean`) gives the `Gt1Bounds` of the weighted Airy symbol `airyWeightedSymbol δ₀ m seed.F` for any
`AiryTailSymbolSeed`; `liftW_eq_airyWeightedSymbol` (`Gt1Identify.lean`) identifies it with the middle-band symbol `liftW`.  Their
composition is `gt1Bounds_liftW_of_seed`: the `GT.1` hypothesis of `middle_transfer_gt1` holds for the lift of every seed that carries the
tail-symbol package.  Discharging `Gt1BasisInput m` (`Gt1Interface.lean`) therefore reduces to exhibiting the three basis seeds
`f₁, g₁, g₁'` (spline multiplied) as `AiryTailSymbolSeed`s.

Status: proved.  Not formalised here: that `f₁, g₁, g₁'` are `AiryTailSymbolSeed`s.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `GT.1` bounds for `liftW` of an `AiryTailSymbolSeed`. -/
theorem gt1Bounds_liftW_of_seed (m : ℕ) (hm : 3 ≤ m) {x₀ : ℝ} (hx₀ : 1 ≤ x₀) (χ : AiryCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S M δ₀ : ℝ} (seed : AiryTailSymbolSeed x₀ χ S M), δ₀ ∈ Set.Icc (0 : ℝ) 2 →
      Gt1Bounds (C * (S + M)) (liftW seed.F δ₀ m) := by
  obtain ⟨C, hC, h⟩ := gt1Bounds_of_seed m hm hx₀ χ
  refine ⟨C, hC, fun {S M δ₀} seed hδ => ?_⟩
  have : liftW seed.F δ₀ m = airyWeightedSymbol δ₀ m seed.F := funext (liftW_eq_airyWeightedSymbol seed.F δ₀ m)
  rw [this]
  exact h seed hδ

/-- info: 'FormalResearch.SignUncertainty.gt1Bounds_liftW_of_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gt1Bounds_liftW_of_seed

end FormalResearch.SignUncertainty
