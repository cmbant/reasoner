module

public import FormalResearch.SignUncertainty.Gt1Interface
public import FormalResearch.CohnElkies.AirySymbolTransfer
public import FormalResearch.CohnElkies.MellinLiftIntegrals

/-!
# Identification of the `GT.1` lift symbol with the weighted Airy symbol

For a seed `X : ℝ → ℝ`, a window width `δ₀`, a B-spline order `m` and `v : ℝ`, the middle-band symbol
`liftW X δ₀ m v = W_X(i v)` is the lift symbol `M_ψ(i v) X̃(i c_s · i v)` of `(e28)`, and `airyWeightedSymbol δ₀ m X v`
is the weighted Airy symbol `M_ψ(i v) F̃(-c_s v)`.  This module proves that the two agree for every seed, by unfolding the
definitions: the B-spline multipliers agree after commuting the factors `i v` and `i β v`, the constants `ceK = airyPhiK`
agree by definition, and the exponents `-(i c_s v)³/12 = -(i (-c_s v)³)/12` and the Fourier kernels `exp(i c_s v u)`
agree by a ring identity using `i² = -1`.

Status: proved (exact identity, no hypotheses).

Formalised here: `liftW_eq_airyWeightedSymbol`, the identification `liftW X δ₀ m = airyWeightedSymbol δ₀ m X` as functions of `v`.

Not formalised here: the `GT.1` bounds `Gt1Bounds` for the weighted symbol (`Gt1BasisInput m` remains the single named input of
`Gt1Interface.lean`), and the corollary for the abstract seed class `AiryTailSymbolSeed`, which needs the `GT.1` seed lemma
(`Gt1FromSeed.lean`, not yet merged into this branch).
-/

@[expose] public section

open Set Complex MeasureTheory

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The lift symbol of a seed is the weighted Airy symbol: `liftW X δ₀ m v = M_ψ(i v) X̃(-c_s v)` with `X̃` the twisted transform
`airyFtilde` of `(e28)` and `(ceo:O11n.2)`. -/
theorem liftW_eq_airyWeightedSymbol (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (v : ℝ) :
    liftW X δ₀ m v = airyWeightedSymbol δ₀ m X v := by
  have hk : ceK = airyPhiK := rfl
  have hmult : bsplineE1 (((ceCs * δ₀ / m : ℝ) : ℂ) * ((v : ℂ) * Complex.I)) =
      bsplineE1 (Complex.I * ((ceCs * δ₀ / m : ℝ) : ℂ) * (v : ℂ)) := by
    congr 1; ring
  have hexp : Complex.exp (-(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12) =
      Complex.exp (-(Complex.I * (-((ceCs : ℂ) * (v : ℂ))) ^ 3 / 12)) := by
    congr 1
    linear_combination (-((ceCs : ℂ) ^ 3 * (v : ℂ) ^ 3 * Complex.I) / 12) * Complex.I_sq
  have hint : ∫ u : ℝ, (X u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ)) =
      ∫ u : ℝ, (X u : ℂ) * Complex.exp (-(Complex.I * (-((ceCs : ℂ) * (v : ℂ))) * (u : ℂ))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    congr 2
    ring
  unfold liftW liftSymbol liftMultiplier airyWeightedSymbol airyFtilde airyFhat airyTwistedLaplaceC bsplineImag
  rw [hmult, hk, hexp, hint]
  simp only [Complex.ofReal_re]

/-- info: 'FormalResearch.SignUncertainty.liftW_eq_airyWeightedSymbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftW_eq_airyWeightedSymbol

end FormalResearch.SignUncertainty
