module

public import FormalResearch.SignUncertainty.CtOuterTheta
public import FormalResearch.SignUncertainty.CtOuterTaylor
public import Mathlib.NumberTheory.LSeries.RiemannZeta

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
    fun τ => ⟨norm_outerGbar_left hε τ, norm_outerGbar_right hε τ⟩, outerGbar_bound⟩

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

/-- **`ct:outer` (2), Taylor expansion with the linear coefficient** (`ct:theta1`, `ct:theta3` structure): for `ε = ±1`
there are constants `θ₃` and `C` such that, with
`θ_1^- = 2π ∫_0^∞ u_r(t) cosh(πt)/sinh²(πt) dt - 1` and `θ_1^+ = θ_1^- - π`,
`|θ_ε(τ) - θ_1^ε τ - θ_3^ε τ³| ≤ C |τ|⁵` for `|τ| ≤ 1` (`θ_3^ε = θ_ε'''(0)/6`).

Scope: the Taylor structure, oddness and the exact linear coefficient *as an integral*.  **Not proved:** the closed forms
`θ_1^- = -3 log 2 + I_0` (evaluation of the integral) and `θ_3^- = ζ(3)/2 + c_{3,mp}`, `θ_3^+ = θ_3^- + π³/6`; see the report. -/
theorem ct_outer_part2_taylor (ε : ℝ) :
    ∃ θ₁ θ₃ C : ℝ,
      θ₁ = 2 * (∫ t in Set.Ioi (0 : ℝ), π * uR t * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) - 1 -
          (if ε = 1 then π else 0) ∧
      (∀ τ : ℝ, |τ| ≤ 1 → |outerTheta ε τ - θ₁ * τ - θ₃ * τ ^ 3| ≤ C * |τ| ^ 5) := by
  obtain ⟨C, hC⟩ := outerTheta_taylor ε
  refine ⟨deriv (outerTheta ε) 0, iteratedDeriv 3 (outerTheta ε) 0 / 6, C, ?_, hC⟩
  rw [deriv_outerTheta_zero, deriv_H0_zero]
  have hre : (∫ t : ℝ, ((uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) : ℝ) : ℂ)).re =
      ∫ t : ℝ, uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) := by
    rw [integral_complex_ofReal]; simp
  rw [hre]
  have heven : (∫ t : ℝ, uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2)) =
      2 * ∫ t in Set.Ioi (0 : ℝ), uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) := by
    rw [← integral_comp_abs (f := fun t : ℝ => uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2))]
    congr 1
    ext t
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, uR_neg, mul_neg, Real.cosh_neg, Real.sinh_neg, neg_sq]
  rw [heven]
  have hcongr : ∫ t in Set.Ioi (0 : ℝ), uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) =
      ∫ t in Set.Ioi (0 : ℝ), π * uR t * Real.cosh (π * t) / Real.sinh (π * t) ^ 2 :=
    setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) (fun t _ => by ring)
  rw [hcongr]


/-! ### The paper's closed-form Taylor coefficients

`ctTheta1`, `ctTheta3` are the constants `θ_1^ε`, `θ_3^ε` of `ct:theta1`, `ct:theta3` (with `I_0` of `eq:ct-I0` and
`c_{3,mp}` of `ct:theta3`).  `CtThetaValuesTarget` is the proposition that the Taylor coefficients of `θ_ε` at `0`
are these constants.  It is proved in `CtOuterTheta3.lean` (`ctThetaValuesTarget`; the linear coefficient is
`theta_one_minus`/`theta_one_plus` of `CtOuterTheta1`, the cubic one `theta_three_eq`); it is kept here as a named
proposition because the proof imports this file. -/

/-- `I_0 = ∫_0^∞ log(6(sinh y - y)/y³) cosh y / sinh² y dy` (`eq:ct-I0`). -/
noncomputable def ctI0 : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), Real.log (6 * (Real.sinh y - y) / y ^ 3) * (Real.cosh y / Real.sinh y ^ 2)

/-- `c_{3,mp} = (π/6) ∫_0^∞ ((d²/dt²) log(m'(t)/t) + 7π²/30) cosh(πt)/sinh²(πt) dt` (`ct:theta3`). -/
noncomputable def ctC3mp : ℝ :=
  π / 6 * ∫ t in Set.Ioi (0 : ℝ),
    (deriv (deriv fun s : ℝ => Real.log (mPrime s / s)) t + 7 * π ^ 2 / 30) *
      (Real.cosh (π * t) / Real.sinh (π * t) ^ 2)

/-- `θ_1^-  = -3 log 2 + I_0`, `θ_1^+ = θ_1^- - π` (`ct:theta1`). -/
noncomputable def ctTheta1 (ε : ℝ) : ℝ :=
  -3 * Real.log 2 + ctI0 - (if ε = 1 then π else 0)

/-- `θ_3^- = ζ(3)/2 + c_{3,mp}`, `θ_3^+ = θ_3^- + π³/6` (`ct:theta3`). -/
noncomputable def ctTheta3 (ε : ℝ) : ℝ :=
  (riemannZeta 3).re / 2 + ctC3mp + (if ε = 1 then π ^ 3 / 6 else 0)

/-- The Taylor coefficients of `θ_ε` at `0` are the paper's constants
`θ_1^ε`, `θ_3^ε`. -/
def CtThetaValuesTarget : Prop :=
  ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    deriv (outerTheta ε) 0 = ctTheta1 ε ∧ iteratedDeriv 3 (outerTheta ε) 0 / 6 = ctTheta3 ε

/-- **`ct:outer` (2) with the paper's constants, from `CtThetaValuesTarget`** (proved in `CtOuterTheta3.lean`, which restates this theorem without the hypothesis as `ct_outer_part2_taylor_values`):
`θ_ε(τ) = θ_1^ε τ + θ_3^ε τ³ + O(τ⁵)` with `θ_1^ε = ctTheta1 ε`, `θ_3^ε = ctTheta3 ε`. -/
theorem ct_outer_part2_taylor_values (h : CtThetaValuesTarget) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ 1 →
      |outerTheta ε τ - ctTheta1 ε * τ - ctTheta3 ε * τ ^ 3| ≤ C * |τ| ^ 5 := by
  obtain ⟨C, hC⟩ := outerTheta_taylor ε
  obtain ⟨h1, h3⟩ := h ε hε
  refine ⟨C, fun τ hτ => ?_⟩
  have := hC τ hτ
  rwa [h1, h3] at this

/-- info: 'FormalResearch.SignUncertainty.CtOuter.ct_outer_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_part1

/-- info: 'FormalResearch.SignUncertainty.CtOuter.ct_outer_part2_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_part2_structure

/-- info: 'FormalResearch.SignUncertainty.CtOuter.ct_outer_part2_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_part2_taylor

/-! ### Axiom guards for the supporting theorems -/

/-- info: 'FormalResearch.SignUncertainty.CtOuter.differentiableOn_outerH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_outerH

/-- info: 'FormalResearch.SignUncertainty.CtOuter.re_outerH_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms re_outerH_bound

/-- info: 'FormalResearch.SignUncertainty.CtOuter.outerH_eq_contH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerH_eq_contH

/-- info: 'FormalResearch.SignUncertainty.CtOuter.differentiableOn_contH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_contH

/-- info: 'FormalResearch.SignUncertainty.CtOuter.re_contH_center' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms re_contH_center

/-- info: 'FormalResearch.SignUncertainty.CtOuter.continuousOn_outerHbar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuousOn_outerHbar

/-- info: 'FormalResearch.SignUncertainty.CtOuter.re_outerHbar_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms re_outerHbar_left

/-- info: 'FormalResearch.SignUncertainty.CtOuter.re_outerHbar_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms re_outerHbar_right

/-- info: 'FormalResearch.SignUncertainty.CtOuter.outerGbar_oneSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerGbar_oneSub

/-- info: 'FormalResearch.SignUncertainty.CtOuter.outerGbar_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerGbar_conj

/-- info: 'FormalResearch.SignUncertainty.CtOuter.norm_outerGbar_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_outerGbar_left

/-- info: 'FormalResearch.SignUncertainty.CtOuter.norm_outerGbar_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_outerGbar_right

/-- info: 'FormalResearch.SignUncertainty.CtOuter.outerGbar_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerGbar_bound

/-- info: 'FormalResearch.SignUncertainty.CtOuter.phase_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phase_identity

/-- info: 'FormalResearch.SignUncertainty.CtOuter.outerTheta_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerTheta_structure

/-- info: 'FormalResearch.SignUncertainty.CtOuter.deriv_H0_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deriv_H0_zero

/-- info: 'FormalResearch.SignUncertainty.CtOuter.deriv_outerTheta_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deriv_outerTheta_zero

/-- info: 'FormalResearch.SignUncertainty.CtOuter.outerTheta_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerTheta_taylor

/-- info: 'FormalResearch.SignUncertainty.CtOuter.odd_taylor5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms odd_taylor5

/-- info: 'FormalResearch.SignUncertainty.CtOuter.ct_outer_part2_taylor_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_part2_taylor_values

end FormalResearch.SignUncertainty.CtOuter
