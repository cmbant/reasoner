module

public import FormalResearch.ModularBootstrap.FoldTip.FixedWeightSetting
public import FormalResearch.ModularBootstrap.Upper.Rigidity.CrossingDictionary

/-!
# Fixed-weight crossing data for Paper I Theorem FT (`ft:H4b`)

Defines `fwExtremal` and `fwCrossingData` (`FTCrossingData (FoldTipSetting.ofFixedWeight prob)`).
-/

@[expose] public section

open MeasureTheory Set

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Duality
  FormalResearch.ModularBootstrap.Upper.Rigidity

/-- The extremal crossing measures at scale `c`: admissible crossing measures at gap exactly `T_V(c)`
(supported on `[T_V(c), ∞)`, charging every `[T_V(c), T_V(c) + ε)`), for `c` in the range where `T_V(c) > 0`
and `c ≥ 12 S`. -/
def fwExtremal (prob : FixedWeightProblem) (c : ℝ) : Set (Measure ℝ) :=
  {ν | ∃ meas : AdmissibleCrossingMeasure prob (c / 12), meas.ν = ν ∧ 0 < c ∧
    12 * prob.totalShift ≤ c ∧ 0 < prob.T_V c ∧ IsAtGap meas (prob.T_V c) ∧
    ∀ ε : ℝ, 0 < ε → 0 < ν (Iio (prob.T_V c + ε))}

/-- The crossing data of a fixed-weight problem: extremal measures and the window measure `μ_S`
(`spectralMeasure`, in the tip variable of `Upper.Rigidity.Dictionary`). -/
noncomputable def fwCrossingData (prob : FixedWeightProblem) :
    FTCrossingData (FoldTipSetting.ofFixedWeight prob) where
  extremal := fwExtremal prob
  window := fun c ν => spectralMeasure prob c ν

end FormalResearch.ModularBootstrap.FoldTip
