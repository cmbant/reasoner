module

public import FormalResearch.SignUncertainty.CtOuterTheta

/-!
# `ct:outer`: the Mellin-strip outer function `G_ε` (headline statements)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Proposition `ct:outer` (eq. `ct:Gdef`, `ct:Gmod`,
`ct:theta-form`).  **Proved:** clause (1) in full and the structural part of clause (2).  See the docstrings of the
two headline theorems for the exact scope; the Taylor coefficients and clause (3) are not in this file.

Notation (all in `FormalResearch.SignUncertainty.CtOuter`):
* `mPrime t = 1/t - π/sinh(π t)` (`= m'(t)`, `m(t) = log((πt/2)/tanh(πt/2))`), `uR` is `u_r`;
* `outerH ζ = ∫ u_r(t)/sin(π(ζ - it)) dt` on `strip = {0 < Re ζ < 1}`; `outerHbar` is its continuous extension to
  `closedStrip = closure strip` (`closure_strip_eq`);
* `outerG ε` is `G_-` (`ε = -1`) or `G_+ = b_{1/2} G_-` (`ε = +1`), `outerGbar ε` its continuous extension to the closed
  strip (the same formula with `outerHbar`);
* `outerTheta ε` is the boundary phase `θ_ε` of `ct:theta-form`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- **`ct:outer` (1)** (Mellin-strip outer function `G_ε`: analyticity, continuity, real symmetry, strip parity, boundary
modulus `ct:Gmod`, and the decay bound), for `ε = ±1`:

* `G_ε` is holomorphic on `S = {0 < Re ζ < 1}` and extends continuously (`outerGbar`, the limit of `G_ε` along `S`) to
  the closed strip, agreeing with `G_ε` on `S`;
* real symmetry `G_ε(ζ̄) = conj G_ε(ζ)` and the opposite strip parity `G_ε(1 - ζ) = -ε G_ε(ζ)` on the closed strip;
* the boundary modulus `|G_ε(iτ)| = |G_ε(1 + iτ)| = √((6/π²) m'(|τ|)/√(1+τ²))` for all `τ ∈ ℝ`;
* `|G_ε(σ + iτ)| ≤ C (1 + |τ|)⁻¹` uniformly on the closed strip.

Scope: complete for (1); the constant `C` is not effective. -/
theorem ct_outer_part1 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    DifferentiableOn ℂ (outerG ε) strip ∧
    ContinuousOn (outerGbar ε) (closure strip) ∧
    (∀ ζ ∈ strip, outerGbar ε ζ = outerG ε ζ) ∧
    (∀ ζ ∈ closure strip, outerGbar ε (starRingEnd ℂ ζ) = starRingEnd ℂ (outerGbar ε ζ)) ∧
    (∀ ζ ∈ closure strip, outerGbar ε (1 - ζ) = -ε * outerGbar ε ζ) ∧
    (∀ τ : ℝ,
      ‖outerGbar ε (Complex.I * (τ : ℂ))‖ = Real.sqrt (6 / π ^ 2 * mPrime |τ| / Real.sqrt (1 + τ ^ 2)) ∧
      ‖outerGbar ε (1 + Complex.I * (τ : ℂ))‖ = Real.sqrt (6 / π ^ 2 * mPrime |τ| / Real.sqrt (1 + τ ^ 2))) ∧
    ∃ C : ℝ, ∀ ζ ∈ closure strip, ‖outerGbar ε ζ‖ ≤ C / (1 + |ζ.im|) := by
  rw [closure_strip_eq]
  refine ⟨outerG_differentiableOn ε, outerGbar_continuousOn ε, fun ζ hζ => outerGbar_eq_outerG ε hζ,
    fun ζ hζ => outerGbar_conj hε hζ, fun ζ hζ => outerGbar_oneSub hε hζ,
    fun τ => ⟨norm_outerGbar_left hε τ, norm_outerGbar_right hε τ⟩, outerGbar_bound hε⟩

/-- **`ct:outer` (2), structural part** (boundary phase `θ_ε`, eq. `ct:theta-form`), for `ε = ±1`, with
`θ_-(τ) = Im h̄(iτ) - arctan τ` and `θ_+(τ) = θ_-(τ) - 2 arctan(tanh(πτ/2))` (`outerTheta`):

* the phase identity `G_ε(iτ)(1 - iτ)^{1/2} = √((6/π²) m'(τ)) e^{i(π/4 + θ_ε(τ))}` for `τ > 0`;
* `θ_ε` is odd and `C^∞` on `ℝ`;
* `θ_ε` extends to a function holomorphic on the disc `|τ| < 1/2` (it is the restriction of a holomorphic `Θ`).

Not included here: the Taylor coefficients `θ_1^ε`, `θ_3^ε`. -/
theorem ct_outer_part2_structure {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (∀ τ : ℝ, 0 < τ →
      outerGbar ε (Complex.I * (τ : ℂ)) * (1 - Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) =
        (Real.sqrt (6 / π ^ 2 * mPrime τ) : ℂ) *
          Complex.exp (Complex.I * ((π / 4 + outerTheta ε τ : ℝ) : ℂ))) ∧
    (∀ τ : ℝ, outerTheta ε (-τ) = -outerTheta ε τ) ∧ ContDiff ℝ ⊤ (outerTheta ε) ∧
    ∃ Θ : ℂ → ℂ, DifferentiableOn ℂ Θ (ball (0 : ℂ) (1 / 2)) ∧
      ∀ τ : ℝ, |τ| < 1 / 2 → Θ (τ : ℂ) = (outerTheta ε τ : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := outerTheta_structure ε
  exact ⟨fun τ hτ => phase_identity hε hτ, h1, h2, h3⟩

/-- `ct:theta-form`, `ε = -1`: `θ_-(τ) = Im h̄(iτ) - arctan τ`. -/
theorem outerTheta_minus (τ : ℝ) :
    outerTheta (-1) τ = (outerHbar (Complex.I * (τ : ℂ))).im - Real.arctan τ := by
  have hne : (-1 : ℝ) ≠ 1 := by norm_num
  simp [outerTheta, hne]

/-- `ct:theta-form`, `ε = +1`: `θ_+(τ) = θ_-(τ) - 2 arctan(tanh(πτ/2))`. -/
theorem outerTheta_plus (τ : ℝ) :
    outerTheta 1 τ = outerTheta (-1) τ - 2 * Real.arctan (Real.tanh (π * τ / 2)) := by
  have hne : (-1 : ℝ) ≠ 1 := by norm_num
  simp [outerTheta, hne]

/-- info: 'FormalResearch.SignUncertainty.CtOuter.ct_outer_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_part1

/-- info: 'FormalResearch.SignUncertainty.CtOuter.ct_outer_part2_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_part2_structure

end FormalResearch.SignUncertainty.CtOuter
