module

public import Mathlib
public import FormalResearch.CohnElkies.AirySeedFloors

/-!
# The convolution source `S_c` of Lemma `O.12` (`ceo:conv`): definitions (M6)

With the smooth cutoff `η = convEta` (`0` on `(-∞, 1]`, `1` on `[2, ∞)`), the profile
`ϱ(t) = (t/(1+t))^p`, the long-range weight `w_h(y) = η(y) ϱ(h y) / y^{3/2}` and the full weight
`w_c = γ ε e^{-y} + θ w_h` (`ε = c^{-1/3}`, `h = λ ε²`), the convolution source is
`S_c(u) = ∫₀^∞ w_c(y) g₁(u + y) dy` with `g₁ = ceG1 (airyZero 1) = (Ai/(u - a₁))²`.

Only elementary facts live here (cutoff, profile and weight signs and pointwise bounds); the
analytic items of `ceo:conv` are in the modules importing this one.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The smooth nondecreasing cutoff of `ceo:conv`: `0` on `(-∞, 1]`, `1` on `[2, ∞)`. -/
noncomputable def convEta (y : ℝ) : ℝ := Real.smoothTransition (y - 1)

/-- The profile `ϱ(t) = (t/(1+t))^p`. -/
noncomputable def convRho (p t : ℝ) : ℝ := (t / (1 + t)) ^ p

/-- The long-range weight `w_h(y) = η(y) ϱ(h y) y^{-3/2}`. -/
noncomputable def convWh (p h y : ℝ) : ℝ := convEta y * convRho p (h * y) / y ^ (3 / 2 : ℝ)

/-- The full weight `w_c(y) = γ ε e^{-y} + θ w_h(y)`. -/
noncomputable def convWc (p γ θ ε h y : ℝ) : ℝ := γ * ε * Real.exp (-y) + θ * convWh p h y

/-- The convolution source `S_c(u) = ∫₀^∞ w_c(y) g₁(u + y) dy`. -/
noncomputable def convSource (p γ θ ε h u : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), convWc p γ θ ε h y * ceG1 (airyZero 1) (u + y)

lemma convEta_eq_zero {y : ℝ} (hy : y ≤ 1) : convEta y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma convEta_eq_one {y : ℝ} (hy : 2 ≤ y) : convEta y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma convEta_nonneg (y : ℝ) : 0 ≤ convEta y := Real.smoothTransition.nonneg _

lemma convEta_le_one (y : ℝ) : convEta y ≤ 1 := Real.smoothTransition.le_one _

lemma convEta_monotone : Monotone convEta := fun _ _ h => Real.smoothTransition.monotone (by linarith)

lemma convEta_contDiff {n : ℕ∞} : ContDiff ℝ n convEta :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma convRho_nonneg (p : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ convRho p t :=
  Real.rpow_nonneg (div_nonneg ht (by linarith)) p

lemma convRho_le_one {p : ℝ} (hp : 0 ≤ p) {t : ℝ} (ht : 0 ≤ t) : convRho p t ≤ 1 := by
  unfold convRho
  exact Real.rpow_le_one (div_nonneg ht (by linarith)) ((div_le_one (by linarith)).mpr (by linarith)) hp

lemma convWh_nonneg {p h : ℝ} (hh : 0 ≤ h) {y : ℝ} (hy : 0 < y) : 0 ≤ convWh p h y := by
  unfold convWh
  exact div_nonneg (mul_nonneg (convEta_nonneg y) (convRho_nonneg p (mul_nonneg hh hy.le)))
    (Real.rpow_nonneg hy.le _)

lemma convWh_eq_zero {p h y : ℝ} (hy : y ≤ 1) : convWh p h y = 0 := by
  unfold convWh; rw [convEta_eq_zero hy]; simp

lemma convWh_le {p h : ℝ} (hp : 0 ≤ p) (hh : 0 ≤ h) {y : ℝ} (hy : 0 < y) :
    convWh p h y ≤ y ^ (-(3 / 2 : ℝ)) := by
  unfold convWh
  rw [Real.rpow_neg hy.le, div_eq_mul_inv]
  have hinv : 0 ≤ (y ^ (3 / 2 : ℝ))⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg hy.le _)
  have h1 := convEta_le_one y
  have h2 := convRho_le_one hp (mul_nonneg hh hy.le)
  have h3 := convRho_nonneg p (mul_nonneg hh hy.le)
  have h4 := convEta_nonneg y
  have h5 : convEta y * convRho p (h * y) ≤ 1 := by nlinarith
  calc convEta y * convRho p (h * y) * (y ^ (3 / 2 : ℝ))⁻¹ ≤ 1 * (y ^ (3 / 2 : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right h5 hinv
    _ = (y ^ (3 / 2 : ℝ))⁻¹ := one_mul _

lemma convWc_nonneg {p γ θ ε h : ℝ} (hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hh : 0 ≤ h) {y : ℝ} (hy : 0 < y) :
    0 ≤ convWc p γ θ ε h y := by
  unfold convWc
  have := convWh_nonneg (p := p) hh hy
  positivity


/-- info: 'FormalResearch.SignUncertainty.convEta_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convEta_eq_zero

/-- info: 'FormalResearch.SignUncertainty.convEta_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convEta_eq_one

/-- info: 'FormalResearch.SignUncertainty.convEta_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convEta_nonneg

/-- info: 'FormalResearch.SignUncertainty.convEta_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convEta_le_one

/-- info: 'FormalResearch.SignUncertainty.convEta_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convEta_monotone

/-- info: 'FormalResearch.SignUncertainty.convRho_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convRho_nonneg

/-- info: 'FormalResearch.SignUncertainty.convRho_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convRho_le_one

/-- info: 'FormalResearch.SignUncertainty.convWh_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWh_nonneg

/-- info: 'FormalResearch.SignUncertainty.convWh_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWh_eq_zero

/-- info: 'FormalResearch.SignUncertainty.convWh_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWh_le

/-- info: 'FormalResearch.SignUncertainty.convWc_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWc_nonneg

/-- info: 'FormalResearch.SignUncertainty.convEta_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convEta_contDiff

end FormalResearch.SignUncertainty
