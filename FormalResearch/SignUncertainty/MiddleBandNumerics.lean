module

public import Mathlib

/-!
# Scalar inequalities for the cubic phase of the middle band (GT.2a G0)

Notation used throughout: `a := κ₀ π² S` (this is `c_s ṽ`), `u₀ := 2 √(3 κ₀ S)`,
`ψ u := a u - π² u³ / 36` (the cubic phase), so that
`ψ' u = a - π² u² / 12`, `ψ'' u = -π² u / 6`, `ψ''' = -π² / 6`.

Hypotheses are stated explicitly in each theorem: `1 ≤ κ₀`, `100 ≤ S`, and, for the
`ε`-statement, `κ₀ ≤ 1 + L/4`, `0 < L ≤ 0.002`, `L = π² ε² S`.

Classification: every statement is proved (unconditionally in the stated hypotheses), by
elementary algebra with `Real.sqrt` and the bounds `3.1415 < π` (`Real.pi_gt_d4`). The
derivative identities (`mb_psi_*`) restate the standard power rule in Mathlib
(`hasDerivAt_pow`, `HasDerivAt.const_mul`, `HasDerivAt.div_const`, `HasDerivAt.const_sub`,
`HasDerivAt.neg`); the square-root facts use `Real.sq_sqrt`, `Real.sqrt_nonneg` and
`Real.lt_sqrt`. Only the inequalities for `ψ'` and `ψ''` are specific to this module.

Negative regression: `mb_psi'_far` is stated only from `|u| ≥ 3 u₀ / 2` on. The zero of `ψ'` is at
`|u| = u₀` (since `π² u₀² / 12 = 12 κ₀ π² S / 12 = a`, so `ψ'(u₀) = 0`), where the bound
`5π²u²/108 ≤ |ψ'|` is false for any positive constant; the constant is therefore not claimed below `3 u₀ / 2`.
-/

@[expose] public section

open scoped Real

namespace FormalResearch.SignUncertainty

/-- `34 < 2 √(3 κ₀ S)` for `κ₀ ≥ 1`, `S ≥ 100`. Uses `Real.lt_sqrt` and `17² = 289 < 300 ≤ 3 κ₀ S`. -/
theorem mb_u0_gt {κ₀ S : ℝ} (hκ : 1 ≤ κ₀) (hS : 100 ≤ S) :
    34 < 2 * Real.sqrt (3 * κ₀ * S) := by
  have h17 : (17 : ℝ) < Real.sqrt (3 * κ₀ * S) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.2 hκ) (by linarith : (0 : ℝ) ≤ S)]
  linarith

/-- `2 ε u₀ < 0.1` in the middle band: `(ε u₀)² = 12 κ₀ L / π² ≤ 12 · 1.0005 · 0.002 / π² < 0.0025`
(using `κ₀ ≤ 1 + L/4 ≤ 1.0005`, `L ≤ 0.002`, `π > 3.1415`), stated as `2 · u₀ < 0.1 / ε`. -/
theorem mb_eps_u0_lt {κ₀ S L ε : ℝ} (hκ : 1 ≤ κ₀) (hκ' : κ₀ ≤ 1 + L / 4) (hS : 100 ≤ S)
    (hL : 0 < L) (hL2 : L ≤ 0.002) (hε : 0 < ε) (hεL : L = π ^ 2 * ε ^ 2 * S) :
    2 * (2 * Real.sqrt (3 * κ₀ * S)) < 0.1 / ε := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (3 * κ₀ * S) := ⟨_, rfl⟩
  rw [← hs]
  have h3 : 0 ≤ 3 * κ₀ * S := by nlinarith
  have hs0 : 0 ≤ s := hs ▸ Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 3 * κ₀ * S := hs ▸ Real.sq_sqrt h3
  have hκ1 : κ₀ ≤ 1.0005 := by linarith
  have hκL : κ₀ * L ≤ 0.002001 := by nlinarith
  have hπ : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hπ2 : (9.869 : ℝ) < π ^ 2 := by nlinarith
  have hP : (2 * ε * s) ^ 2 * π ^ 2 = 12 * κ₀ * L := by
    linear_combination (4 * ε ^ 2 * π ^ 2) * hs2 - 12 * κ₀ * hεL
  have hP0 : 0 ≤ 2 * ε * s := by
    have : 0 ≤ ε := hε.le
    positivity
  have key : 2 * ε * s < 0.05 := by
    by_contra hc
    rw [not_lt] at hc
    have h1 : (0.05 : ℝ) ^ 2 ≤ (2 * ε * s) ^ 2 := by nlinarith
    have h2 : (0.0025 : ℝ) * 9.869 ≤ (2 * ε * s) ^ 2 * π ^ 2 := by
      nlinarith [sq_nonneg π]
    nlinarith
  rw [lt_div_iff₀ hε]
  nlinarith [key]

/-- The cubic phase derivative: `(a u - π² u³/36)' = a - π² u²/12`, with the `HasDerivAt` form. -/
theorem mb_psi_hasDerivAt (a u : ℝ) :
    HasDerivAt (fun x : ℝ => a * x - π ^ 2 / 36 * x ^ 3) (a - π ^ 2 * u ^ 2 / 12) u := by
  have h := ((hasDerivAt_id' u).const_mul a).sub ((hasDerivAt_pow 3 u).const_mul (π ^ 2 / 36))
  convert h using 1
  norm_num
  ring

/-- `ψ' u = a - π² u²/12` for the cubic phase `ψ u = a u - π² u³/36`. -/
theorem mb_psi_deriv (a u : ℝ) :
    deriv (fun x : ℝ => a * x - π ^ 2 / 36 * x ^ 3) u = a - π ^ 2 * u ^ 2 / 12 :=
  (mb_psi_hasDerivAt a u).deriv

/-- `ψ'' u = -π² u / 6`. Restates the power rule. -/
theorem mb_psi_deriv2 (a u : ℝ) :
    deriv (deriv (fun x : ℝ => a * x - π ^ 2 / 36 * x ^ 3)) u = -(π ^ 2 * u / 6) := by
  have h1 : deriv (fun x : ℝ => a * x - π ^ 2 / 36 * x ^ 3) =
      fun x => a - π ^ 2 * x ^ 2 / 12 :=
    funext fun x => mb_psi_deriv a x
  rw [h1]
  have h := ((((hasDerivAt_pow 2 u).const_mul (π ^ 2)).div_const 12)).const_sub a
  have h' : HasDerivAt (fun x : ℝ => a - π ^ 2 * x ^ 2 / 12) (-(π ^ 2 * u / 6)) u := by
    convert h using 1
    norm_num
    ring
  exact h'.deriv

/-- `ψ''' = -π²/6`. Restates the power rule. -/
theorem mb_psi_deriv3 (a u : ℝ) :
    deriv (deriv (deriv (fun x : ℝ => a * x - π ^ 2 / 36 * x ^ 3))) u = -(π ^ 2 / 6) := by
  have h1 : deriv (deriv (fun x : ℝ => a * x - π ^ 2 / 36 * x ^ 3)) =
      fun x => -(π ^ 2 * x / 6) :=
    funext fun x => mb_psi_deriv2 a x
  rw [h1]
  have h := (((hasDerivAt_id' u).const_mul (π ^ 2)).div_const 6).neg
  have h' : HasDerivAt (fun x : ℝ => -(π ^ 2 * x / 6)) (-(π ^ 2 / 6)) u := by
    convert h using 1
    ring
  exact h'.deriv

/-- Inner region: for `|u| ≤ u₀/2` (`u₀ = 2√(3κ₀S)`), `ψ' ≥ 7 S`. -/
theorem mb_psi'_ge_inner {a κ₀ S u u₀ : ℝ} (hκ : 1 ≤ κ₀) (hS : 100 ≤ S)
    (ha : a = κ₀ * π ^ 2 * S) (hu₀ : u₀ = 2 * Real.sqrt (3 * κ₀ * S))
    (hu : |u| ≤ u₀ / 2) : 7 * S ≤ a - π ^ 2 * u ^ 2 / 12 := by
  subst ha
  have h3 : 0 ≤ 3 * κ₀ * S := by nlinarith
  have hr : Real.sqrt (3 * κ₀ * S) ^ 2 = 3 * κ₀ * S := Real.sq_sqrt h3
  have hr0 := Real.sqrt_nonneg (3 * κ₀ * S)
  have hab : |u| ≤ Real.sqrt (3 * κ₀ * S) := by rw [hu₀] at hu; linarith
  have hu2 : u ^ 2 ≤ 3 * κ₀ * S := by
    nlinarith [sq_abs u, abs_nonneg u, mul_self_le_mul_self (abs_nonneg u) hab]
  have hπ : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hπ2 : (9.61 : ℝ) ≤ π ^ 2 := by nlinarith
  have hS0 : 0 ≤ S := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hu2 (sq_nonneg π),
    mul_nonneg (sub_nonneg.2 hκ) (mul_nonneg (sq_nonneg π) hS0),
    mul_le_mul_of_nonneg_right hπ2 hS0]

/-- Far region, lower bound on `|ψ'|`: for `3 u₀/2 ≤ |u|`, `|ψ'(u)| ≥ (5π²/108) u²`. The constant
is valid only from `3 u₀ / 2` on (see the module docstring). -/
theorem mb_psi'_far {a κ₀ S u u₀ : ℝ} (hκ : 1 ≤ κ₀) (hS : 100 ≤ S)
    (ha : a = κ₀ * π ^ 2 * S) (hu₀ : u₀ = 2 * Real.sqrt (3 * κ₀ * S))
    (hu : 3 * u₀ / 2 ≤ |u|) :
    5 * π ^ 2 / 108 * u ^ 2 ≤ |a - π ^ 2 * u ^ 2 / 12| := by
  subst ha
  have h3 : 0 ≤ 3 * κ₀ * S := by nlinarith
  have hr : Real.sqrt (3 * κ₀ * S) ^ 2 = 3 * κ₀ * S := Real.sq_sqrt h3
  have hr0 := Real.sqrt_nonneg (3 * κ₀ * S)
  have hab : 3 * Real.sqrt (3 * κ₀ * S) ≤ |u| := by rw [hu₀] at hu; linarith
  have hu2 : 27 * κ₀ * S ≤ u ^ 2 := by
    nlinarith [sq_abs u, mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 3 * Real.sqrt (3 * κ₀ * S)) hab]
  have hS0 : 0 ≤ κ₀ * S := by nlinarith
  have hneg : κ₀ * π ^ 2 * S - π ^ 2 * u ^ 2 / 12 ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hu2 (sq_nonneg π), mul_nonneg hS0 (sq_nonneg π)]
  have hneg' : κ₀ * π ^ 2 * S - π ^ 2 * u ^ 2 / 12 ≤ 0 := hneg
  rw [abs_of_nonpos hneg']
  nlinarith [mul_le_mul_of_nonneg_left hu2 (sq_nonneg π)]

/-- Outer region, reference bound: for `2 u₀ ≤ |u|`, `|ψ'(u)| ≥ (π²/16) u²`. -/
theorem mb_psi'_outer {a κ₀ S u u₀ : ℝ} (hκ : 1 ≤ κ₀) (hS : 100 ≤ S)
    (ha : a = κ₀ * π ^ 2 * S) (hu₀ : u₀ = 2 * Real.sqrt (3 * κ₀ * S))
    (hu : 2 * u₀ ≤ |u|) :
    π ^ 2 * u ^ 2 / 16 ≤ |a - π ^ 2 * u ^ 2 / 12| := by
  subst ha
  have h3 : 0 ≤ 3 * κ₀ * S := by nlinarith
  have hr : Real.sqrt (3 * κ₀ * S) ^ 2 = 3 * κ₀ * S := Real.sq_sqrt h3
  have hr0 := Real.sqrt_nonneg (3 * κ₀ * S)
  have hab : 4 * Real.sqrt (3 * κ₀ * S) ≤ |u| := by rw [hu₀] at hu; linarith
  have hu2 : 48 * κ₀ * S ≤ u ^ 2 := by
    nlinarith [sq_abs u, mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 4 * Real.sqrt (3 * κ₀ * S)) hab]
  have hS0 : 0 ≤ κ₀ * S := by nlinarith
  have hneg : κ₀ * π ^ 2 * S - π ^ 2 * u ^ 2 / 12 ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hu2 (sq_nonneg π), mul_nonneg hS0 (sq_nonneg π)]
  rw [abs_of_nonpos hneg]
  nlinarith [mul_le_mul_of_nonneg_left hu2 (sq_nonneg π)]

/-- Middle band, `ψ''` lower bound: for `3 u₀/8 ≤ |u|`, `|ψ''(u)| ≥ π² u₀ / 16`. -/
theorem mb_psi''_lower {u u₀ : ℝ} (hu : 3 * u₀ / 8 ≤ |u|) :
    π ^ 2 * u₀ / 16 ≤ |π ^ 2 * u / 6| := by
  rw [show π ^ 2 * u / 6 = (π ^ 2 / 6) * u by ring, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ π ^ 2 / 6)]
  nlinarith [mul_le_mul_of_nonneg_left hu (sq_nonneg π)]

/-- `ψ' u = a - π² u²/12` is antitone on `[0, ∞)`. -/
theorem mb_psi'_antitoneOn (a : ℝ) :
    AntitoneOn (fun u : ℝ => a - π ^ 2 * u ^ 2 / 12) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx' : 0 ≤ x := hx
  have hxy' : x ≤ y := hxy
  show a - π ^ 2 * y ^ 2 / 12 ≤ a - π ^ 2 * x ^ 2 / 12
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg π)]

/-- `ψ' u = a - π² u²/12` is monotone on `(-∞, 0]`. -/
theorem mb_psi'_monotoneOn (a : ℝ) :
    MonotoneOn (fun u : ℝ => a - π ^ 2 * u ^ 2 / 12) (Set.Iic 0) := by
  intro x hx y hy hxy
  have hy' : y ≤ 0 := hy
  have hxy' : x ≤ y := hxy
  show a - π ^ 2 * x ^ 2 / 12 ≤ a - π ^ 2 * y ^ 2 / 12
  have hsq : y ^ 2 ≤ x ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg π)]

/-! `#print axioms` guards for each theorem above. -/

/-- info: 'FormalResearch.SignUncertainty.mb_u0_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_u0_gt

/-- info: 'FormalResearch.SignUncertainty.mb_eps_u0_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_eps_u0_lt

/-- info: 'FormalResearch.SignUncertainty.mb_psi_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_psi_hasDerivAt

/-- info: 'FormalResearch.SignUncertainty.mb_psi_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_psi_deriv

/-- info: 'FormalResearch.SignUncertainty.mb_psi_deriv2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_psi_deriv2

/-- info: 'FormalResearch.SignUncertainty.mb_psi_deriv3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_psi_deriv3

/-- info: 'FormalResearch.SignUncertainty.mb_psi'_ge_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_psi'_ge_inner

/-- info: 'FormalResearch.SignUncertainty.mb_psi'_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_psi'_far

/-- info: 'FormalResearch.SignUncertainty.mb_psi'_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_psi'_outer

/-- info: 'FormalResearch.SignUncertainty.mb_psi''_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_psi''_lower

/-- info: 'FormalResearch.SignUncertainty.mb_psi'_antitoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_psi'_antitoneOn

/-- info: 'FormalResearch.SignUncertainty.mb_psi'_monotoneOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_psi'_monotoneOn

end FormalResearch.SignUncertainty
