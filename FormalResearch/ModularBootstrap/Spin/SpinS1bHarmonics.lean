module

public import FormalResearch.ModularBootstrap.Spin.Defs
public import FormalResearch.ModularBootstrap.Crossing.SumRule

/-!
# Cardy `D_4` angular harmonics (`spinnotes:S1`(b), first two clauses)

Proves the exact Bessel–Chebyshev expansion of the `D_4` angular harmonics `spinV2Harmonic a ℓ t`
for `a ≥ 2`, `ℓ : ℕ`, `t ≥ 0`:
```
V_{2,ℓ}(t) = 2π (I_{4ℓ}(4π √(a t))
              - 2 (-1)^ℓ T_{2ℓ}(1 / (a - 1)) I_{4ℓ}(4π √((a - 1) t))
              + I_{4ℓ}(4π √((a - 2) t))),
```
its `ℓ = 0` specialization `spinV2Harmonic a 0 t = virasoroProblem.cardyDensity a t`, and the
`ℓ = 0` leading-term integral `∫_0^{2π} cosh(2π√a r_L) cosh(2π√a r_R) dψ = 2π I_0(4π √(a t))`
(used for `J`-finiteness of radial lifts in `SpinS1c`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Bessel

/-! ### Section 1: Shifted `cosh` integral representation of `I_{4ℓ}` -/

private lemma cos_four_mul_periodic (ℓ : ℕ) (x : ℝ) :
    Real.cos (4 * (ℓ : ℝ) * (x + 2 * π)) = Real.cos (4 * (ℓ : ℝ) * x) := by
  have h : 4 * (ℓ : ℝ) * (x + 2 * π) = 4 * (ℓ : ℝ) * x + ((4 * ℓ : ℕ) : ℝ) * (2 * π) := by
    push_cast; ring
  rw [h, Real.cos_add_nat_mul_two_pi]

private lemma sin_four_mul_periodic (ℓ : ℕ) (x : ℝ) :
    Real.sin (4 * (ℓ : ℝ) * (x + 2 * π)) = Real.sin (4 * (ℓ : ℝ) * x) := by
  have h : 4 * (ℓ : ℝ) * (x + 2 * π) = 4 * (ℓ : ℝ) * x + ((4 * ℓ : ℕ) : ℝ) * (2 * π) := by
    push_cast; ring
  rw [h, Real.sin_add_nat_mul_two_pi]

private lemma cos_four_mul_add_pi (ℓ : ℕ) (x : ℝ) :
    Real.cos (4 * (ℓ : ℝ) * (x + π)) = Real.cos (4 * (ℓ : ℝ) * x) := by
  have h : 4 * (ℓ : ℝ) * (x + π) = 4 * (ℓ : ℝ) * x + ((2 * ℓ : ℕ) : ℝ) * (2 * π) := by
    push_cast; ring
  rw [h, Real.cos_add_nat_mul_two_pi]

private lemma sin_four_mul_two_pi_sub (ℓ : ℕ) (x : ℝ) :
    Real.sin (4 * (ℓ : ℝ) * (2 * π - x)) = -Real.sin (4 * (ℓ : ℝ) * x) := by
  have h : 4 * (ℓ : ℝ) * (2 * π - x) = -(4 * (ℓ : ℝ) * x) + ((4 * ℓ : ℕ) : ℝ) * (2 * π) := by
    push_cast; ring
  rw [h, Real.sin_add_nat_mul_two_pi, Real.sin_neg]

private lemma cos_four_mul_two_pi_sub (ℓ : ℕ) (x : ℝ) :
    Real.cos (4 * (ℓ : ℝ) * (2 * π - x)) = Real.cos (4 * (ℓ : ℝ) * x) := by
  have h : 4 * (ℓ : ℝ) * (2 * π - x) = -(4 * (ℓ : ℝ) * x) + ((4 * ℓ : ℕ) : ℝ) * (2 * π) := by
    push_cast; ring
  rw [h, Real.cos_add_nat_mul_two_pi, Real.cos_neg]

private lemma integral_sin_four_mul_cosh_eq_zero (ℓ : ℕ) (z : ℝ) :
    ∫ u in (0 : ℝ)..(2 * π), Real.sin (4 * (ℓ : ℝ) * u) * Real.cosh (z * Real.cos u) = 0 := by
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun u => Real.sin (4 * (ℓ : ℝ) * u) * Real.cosh (z * Real.cos u)) (2 * π)
    (a := (0 : ℝ)) (b := 2 * π)
  simp only [sub_self, sub_zero] at hsub
  have hneg : ∫ u in (0 : ℝ)..(2 * π),
      Real.sin (4 * (ℓ : ℝ) * (2 * π - u)) * Real.cosh (z * Real.cos (2 * π - u)) =
      -(∫ u in (0 : ℝ)..(2 * π), Real.sin (4 * (ℓ : ℝ) * u) * Real.cosh (z * Real.cos u)) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [sin_four_mul_two_pi_sub, Real.cos_two_pi_sub]
    ring
  linarith

private lemma integral_cos_four_mul_exp_eq (ℓ : ℕ) (z : ℝ) :
    ∫ u in (0 : ℝ)..(2 * π), Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (z * Real.cos u) =
      2 * π * besselI (4 * ℓ) z := by
  have hsplit : ∫ u in (0 : ℝ)..(2 * π), Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (z * Real.cos u) =
      (∫ u in (0 : ℝ)..π, Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (z * Real.cos u)) +
      (∫ u in π..(2 * π), Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (z * Real.cos u)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable (by fun_prop) 0 π)
      (Continuous.intervalIntegrable (by fun_prop) π (2 * π))).symm
  have hsecond : ∫ u in π..(2 * π), Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (z * Real.cos u) =
      ∫ u in (0 : ℝ)..π, Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (z * Real.cos u) := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (fun u => Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (z * Real.cos u)) (2 * π)
      (a := π) (b := 2 * π)
    rw [sub_self, show 2 * π - π = π by ring] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [cos_four_mul_two_pi_sub, Real.cos_two_pi_sub]
  rw [hsplit, hsecond, ← two_mul]
  have hbes := Crossing.besselI_eq_integral (4 * ℓ) z
  have hcongr : ∫ u in (0 : ℝ)..π, Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (z * Real.cos u) =
      ∫ u in (0 : ℝ)..π, Real.exp (z * Real.cos u) * Real.cos (((4 * ℓ : ℕ) : ℝ) * u) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    push_cast; ring
  rw [hcongr, hbes]
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi]

private lemma integral_cos_four_mul_cosh_eq (ℓ : ℕ) (z : ℝ) :
    ∫ u in (0 : ℝ)..(2 * π), Real.cos (4 * (ℓ : ℝ) * u) * Real.cosh (z * Real.cos u) =
      2 * π * besselI (4 * ℓ) z := by
  have hper : Function.Periodic
      (fun u => Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (-(z * Real.cos u))) (2 * π) := fun u => by
    dsimp only
    rw [cos_four_mul_periodic, Real.cos_add_two_pi]
  have hneg_exp : ∫ u in (0 : ℝ)..(2 * π),
      Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (-(z * Real.cos u)) =
      ∫ u in (0 : ℝ)..(2 * π), Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (z * Real.cos u) := by
    have hshift := hper.intervalIntegral_add_eq (t := π) (s := 0)
    rw [zero_add] at hshift
    rw [← hshift]
    have hcomp := intervalIntegral.integral_comp_add_right
      (fun u => Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (-(z * Real.cos u))) π
      (a := (0 : ℝ)) (b := 2 * π)
    rw [zero_add, add_comm (2 * π) π] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [cos_four_mul_add_pi, Real.cos_add_pi, mul_neg, neg_neg]
  have hcosh : ∀ u : ℝ,
      Real.cos (4 * (ℓ : ℝ) * u) * Real.cosh (z * Real.cos u) =
        (1 / 2 : ℝ) * (Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (z * Real.cos u)) +
        (1 / 2 : ℝ) * (Real.cos (4 * (ℓ : ℝ) * u) * Real.exp (-(z * Real.cos u))) := by
    intro u; rw [Real.cosh_eq]; ring
  rw [intervalIntegral.integral_congr (fun u _ => hcosh u),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π))
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hneg_exp, integral_cos_four_mul_exp_eq]
  ring

/-- Shifted `cosh` Fourier integral for `4ℓ`-th angular harmonics:
`∫_0^{2π} cos(4ℓ ψ) cosh(z cos(ψ - φ)) dψ = 2π cos(4ℓ φ) I_{4ℓ}(z)`. -/
theorem spin_besselI_integral_cosh (ℓ : ℕ) (z φ : ℝ) :
    ∫ ψ in (0 : ℝ)..(2 * π), Real.cos (4 * (ℓ : ℝ) * ψ) * Real.cosh (z * Real.cos (ψ - φ)) =
      2 * π * Real.cos (4 * (ℓ : ℝ) * φ) * besselI (4 * ℓ) z := by
  have hper : Function.Periodic
      (fun ψ => Real.cos (4 * (ℓ : ℝ) * ψ) * Real.cosh (z * Real.cos (ψ - φ))) (2 * π) := fun ψ => by
    dsimp only
    rw [cos_four_mul_periodic, show ψ + 2 * π - φ = (ψ - φ) + 2 * π by ring, Real.cos_add_two_pi]
  have hshift := hper.intervalIntegral_add_eq (t := φ) (s := 0)
  rw [zero_add] at hshift
  rw [← hshift]
  have hcomp := intervalIntegral.integral_comp_add_right
    (fun ψ => Real.cos (4 * (ℓ : ℝ) * ψ) * Real.cosh (z * Real.cos (ψ - φ))) φ
    (a := (0 : ℝ)) (b := 2 * π)
  rw [zero_add, add_comm (2 * π) φ] at hcomp
  rw [← hcomp]
  have hexp : ∀ u : ℝ,
      Real.cos (4 * (ℓ : ℝ) * (u + φ)) * Real.cosh (z * Real.cos (u + φ - φ)) =
        Real.cos (4 * (ℓ : ℝ) * φ) * (Real.cos (4 * (ℓ : ℝ) * u) * Real.cosh (z * Real.cos u)) -
        Real.sin (4 * (ℓ : ℝ) * φ) * (Real.sin (4 * (ℓ : ℝ) * u) * Real.cosh (z * Real.cos u)) := by
    intro u
    rw [add_sub_cancel_right, mul_add, Real.cos_add]
    ring
  rw [intervalIntegral.integral_congr (fun u _ => hexp u),
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π))
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_four_mul_cosh_eq, integral_sin_four_mul_cosh_eq_zero]
  ring

/-! ### Section 2: Product of two chiral `cosh` weights on the `D_4` circle -/

private lemma cosh_mul_cosh_eq (A B : ℝ) :
    Real.cosh A * Real.cosh B = (1 / 2 : ℝ) * (Real.cosh (A + B) + Real.cosh (A - B)) := by
  rw [Real.cosh_eq, Real.cosh_eq, Real.cosh_eq, Real.cosh_eq]
  have h1 : Real.exp (A + B) = Real.exp A * Real.exp B := Real.exp_add A B
  have h2 : Real.exp (-(A + B)) = Real.exp (-A) * Real.exp (-B) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (A - B) = Real.exp A * Real.exp (-B) := by
    rw [← Real.exp_add]; rfl
  have h4 : Real.exp (-(A - B)) = Real.exp (-A) * Real.exp B := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2, h3, h4]
  ring

private lemma sqrt_two_mul_cos_pi_div_four_add {t : ℝ} (_ht : 0 ≤ t) (ψ : ℝ) :
    Real.sqrt (2 * t) * Real.cos (π / 4 + ψ) = Real.sqrt t * (Real.cos ψ - Real.sin ψ) := by
  rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
    have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    linarith
  calc Real.sqrt 2 * Real.sqrt t * (Real.sqrt 2 / 2 * Real.cos ψ - Real.sqrt 2 / 2 * Real.sin ψ)
      = (Real.sqrt 2 * (Real.sqrt 2 / 2)) * Real.sqrt t * (Real.cos ψ - Real.sin ψ) := by ring
    _ = Real.sqrt t * (Real.cos ψ - Real.sin ψ) := by rw [h2, one_mul]

private lemma sqrt_two_mul_sin_pi_div_four_add {t : ℝ} (_ht : 0 ≤ t) (ψ : ℝ) :
    Real.sqrt (2 * t) * Real.sin (π / 4 + ψ) = Real.sqrt t * (Real.cos ψ + Real.sin ψ) := by
  rw [Real.sin_add, Real.cos_pi_div_four, Real.sin_pi_div_four, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
    have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    linarith
  calc Real.sqrt 2 * Real.sqrt t * (Real.sqrt 2 / 2 * Real.cos ψ + Real.sqrt 2 / 2 * Real.sin ψ)
      = (Real.sqrt 2 * (Real.sqrt 2 / 2)) * Real.sqrt t * (Real.cos ψ + Real.sin ψ) := by ring
    _ = Real.sqrt t * (Real.cos ψ + Real.sin ψ) := by rw [h2, one_mul]

private lemma spin_cosh_prod_harmonic (ℓ : ℕ) {α β t R φ₁ φ₂ : ℝ} (ht : 0 ≤ t)
    (h1c : 2 * π * Real.sqrt t * (α + β) = R * Real.cos φ₁)
    (h1s : 2 * π * Real.sqrt t * (β - α) = R * Real.sin φ₁)
    (h2c : 2 * π * Real.sqrt t * (α - β) = R * Real.cos φ₂)
    (h2s : -(2 * π * Real.sqrt t * (α + β)) = R * Real.sin φ₂) :
    ∫ ψ in (0 : ℝ)..(2 * π),
      Real.cos (4 * (ℓ : ℝ) * ψ) *
        Real.cosh (2 * π * α * (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ))) *
        Real.cosh (2 * π * β * (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ))) =
      π * (Real.cos (4 * (ℓ : ℝ) * φ₁) + Real.cos (4 * (ℓ : ℝ) * φ₂)) * besselI (4 * ℓ) R := by
  have hpt : ∀ ψ : ℝ,
      Real.cos (4 * (ℓ : ℝ) * ψ) *
        Real.cosh (2 * π * α * (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ))) *
        Real.cosh (2 * π * β * (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ))) =
      (1 / 2 : ℝ) * (Real.cos (4 * (ℓ : ℝ) * ψ) * Real.cosh (R * Real.cos (ψ - φ₁))) +
      (1 / 2 : ℝ) * (Real.cos (4 * (ℓ : ℝ) * ψ) * Real.cosh (R * Real.cos (ψ - φ₂))) := by
    intro ψ
    rw [sqrt_two_mul_cos_pi_div_four_add ht, sqrt_two_mul_sin_pi_div_four_add ht,
      mul_assoc, cosh_mul_cosh_eq]
    have hadd : 2 * π * α * (Real.sqrt t * (Real.cos ψ - Real.sin ψ)) +
        2 * π * β * (Real.sqrt t * (Real.cos ψ + Real.sin ψ)) = R * Real.cos (ψ - φ₁) := by
      rw [Real.cos_sub]
      calc 2 * π * α * (Real.sqrt t * (Real.cos ψ - Real.sin ψ)) +
            2 * π * β * (Real.sqrt t * (Real.cos ψ + Real.sin ψ))
          = (2 * π * Real.sqrt t * (α + β)) * Real.cos ψ +
            (2 * π * Real.sqrt t * (β - α)) * Real.sin ψ := by ring
        _ = (R * Real.cos φ₁) * Real.cos ψ + (R * Real.sin φ₁) * Real.sin ψ := by rw [h1c, h1s]
        _ = R * (Real.cos ψ * Real.cos φ₁ + Real.sin ψ * Real.sin φ₁) := by ring
    have hsub : 2 * π * α * (Real.sqrt t * (Real.cos ψ - Real.sin ψ)) -
        2 * π * β * (Real.sqrt t * (Real.cos ψ + Real.sin ψ)) = R * Real.cos (ψ - φ₂) := by
      rw [Real.cos_sub]
      calc 2 * π * α * (Real.sqrt t * (Real.cos ψ - Real.sin ψ)) -
            2 * π * β * (Real.sqrt t * (Real.cos ψ + Real.sin ψ))
          = (2 * π * Real.sqrt t * (α - β)) * Real.cos ψ +
            (-(2 * π * Real.sqrt t * (α + β))) * Real.sin ψ := by ring
        _ = (R * Real.cos φ₂) * Real.cos ψ + (R * Real.sin φ₂) * Real.sin ψ := by rw [h2c, h2s]
        _ = R * (Real.cos ψ * Real.cos φ₂ + Real.sin ψ * Real.sin φ₂) := by ring
    rw [hadd, hsub]
    ring
  rw [intervalIntegral.integral_congr (fun ψ _ => hpt ψ),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π))
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    spin_besselI_integral_cosh, spin_besselI_integral_cosh]
  ring

private lemma spin_cosh_prod_harmonic_diag (ℓ : ℕ) {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t) :
    ∫ ψ in (0 : ℝ)..(2 * π),
      Real.cos (4 * (ℓ : ℝ) * ψ) *
        Real.cosh (2 * π * Real.sqrt α * (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ))) *
        Real.cosh (2 * π * Real.sqrt α * (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ))) =
      2 * π * besselI (4 * ℓ) (4 * π * Real.sqrt (α * t)) := by
  have hsq : Real.sqrt (α * t) = Real.sqrt α * Real.sqrt t := Real.sqrt_mul hα t
  have h := spin_cosh_prod_harmonic ℓ ht (α := Real.sqrt α) (β := Real.sqrt α)
    (R := 4 * π * Real.sqrt (α * t)) (φ₁ := 0) (φ₂ := -(π / 2))
    (by rw [Real.cos_zero, hsq]; ring)
    (by rw [Real.sin_zero]; ring)
    (by rw [Real.cos_neg, Real.cos_pi_div_two]; ring)
    (by rw [Real.sin_neg, Real.sin_pi_div_two, hsq]; ring)
  rw [h]
  have hcos1 : Real.cos (4 * (ℓ : ℝ) * 0) = 1 := by simp
  have hcos2 : Real.cos (4 * (ℓ : ℝ) * -(π / 2)) = 1 := by
    have heq : 4 * (ℓ : ℝ) * -(π / 2) = -(0 + ((ℓ : ℕ) : ℝ) * (2 * π)) := by ring
    rw [heq, Real.cos_neg, Real.cos_add_nat_mul_two_pi, Real.cos_zero]
  rw [hcos1, hcos2]
  ring

/-- `ℓ = 0` diagonal `cosh` integral:
`∫_0^{2π} cosh(2π √a r_L) cosh(2π √a r_R) dψ = 2π I_0(4π √(a t))`. -/
theorem spin_cosh_integral_zero {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    ∫ ψ in (0 : ℝ)..(2 * π),
      Real.cosh (2 * π * Real.sqrt a * (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ))) *
        Real.cosh (2 * π * Real.sqrt a * (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ))) =
      2 * π * besselI 0 (4 * π * Real.sqrt (a * t)) := by
  have h := spin_cosh_prod_harmonic_diag 0 ha ht
  simpa using h

/-! ### Section 3: Cross-term angle and Chebyshev polynomial identity -/

private lemma cross_angle_trig {a : ℝ} (ha : 2 ≤ a) :
    let θ := Real.arccos (1 / (a - 1))
    let φ := (π / 2 - θ) / 2
    Real.cos φ = (Real.sqrt a + Real.sqrt (a - 2)) / (2 * Real.sqrt (a - 1)) ∧
    Real.sin φ = (Real.sqrt a - Real.sqrt (a - 2)) / (2 * Real.sqrt (a - 1)) ∧
    ∀ ℓ : ℕ, Real.cos (4 * (ℓ : ℝ) * φ) =
      (-1 : ℝ) ^ ℓ * (Polynomial.Chebyshev.T ℝ (2 * ℓ : ℤ)).eval (1 / (a - 1)) := by
  intro θ φ
  have ha1_pos : (0 : ℝ) < a - 1 := by linarith
  have ha1_ge1 : (1 : ℝ) ≤ a - 1 := by linarith
  have hx_pos : (0 : ℝ) < 1 / (a - 1) := div_pos one_pos ha1_pos
  have hx_le1 : 1 / (a - 1) ≤ 1 := div_le_one_of_le₀ ha1_ge1 ha1_pos.le
  have hcos_θ : Real.cos θ = 1 / (a - 1) :=
    Real.cos_arccos (by linarith) hx_le1
  have hθ_nn : 0 ≤ θ := Real.arccos_nonneg _
  have hθ_le : θ ≤ π / 2 := Real.arccos_le_pi_div_two.mpr hx_pos.le
  have hsin_θ : Real.sin θ = Real.sqrt (a * (a - 2)) / (a - 1) := by
    rw [Real.sin_arccos]
    have h1 : 1 - (1 / (a - 1)) ^ 2 = a * (a - 2) / (a - 1) ^ 2 := by
      field_simp [ha1_pos.ne']
      ring
    rw [h1, Real.sqrt_div (by nlinarith : 0 ≤ a * (a - 2)), Real.sqrt_sq ha1_pos.le]
  have h2φ : 2 * φ = π / 2 - θ := by dsimp [φ]; ring
  have hcos_2φ : Real.cos (2 * φ) = Real.sqrt (a * (a - 2)) / (a - 1) := by
    rw [h2φ, Real.cos_pi_div_two_sub, hsin_θ]
  have hφ_nn : 0 ≤ φ := by dsimp [φ]; linarith
  have hφ_le : φ ≤ π / 4 := by dsimp [φ]; linarith
  have hcos_φ_nn : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin_φ_nn : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ_nn (by linarith [Real.pi_pos])
  have hsq_a : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  have hsq_a2 : Real.sqrt (a - 2) ^ 2 = a - 2 := Real.sq_sqrt (by linarith)
  have hsq_a1 : Real.sqrt (a - 1) ^ 2 = a - 1 := Real.sq_sqrt ha1_pos.le
  have hsqrt_prod : Real.sqrt a * Real.sqrt (a - 2) = Real.sqrt (a * (a - 2)) :=
    (Real.sqrt_mul (by linarith) (a - 2)).symm
  have hcos_sq : Real.cos φ ^ 2 = ((Real.sqrt a + Real.sqrt (a - 2)) / (2 * Real.sqrt (a - 1))) ^ 2 := by
    have hdouble : Real.cos φ ^ 2 = (1 + Real.cos (2 * φ)) / 2 := by
      rw [Real.cos_two_mul]; ring
    rw [hdouble, hcos_2φ, div_pow, mul_pow, hsq_a1]
    have hnum : (Real.sqrt a + Real.sqrt (a - 2)) ^ 2 = 2 * (a - 1) + 2 * Real.sqrt (a * (a - 2)) := by
      calc (Real.sqrt a + Real.sqrt (a - 2)) ^ 2
          = Real.sqrt a ^ 2 + 2 * (Real.sqrt a * Real.sqrt (a - 2)) + Real.sqrt (a - 2) ^ 2 := by ring
        _ = a + 2 * Real.sqrt (a * (a - 2)) + (a - 2) := by rw [hsq_a, hsq_a2, hsqrt_prod]
        _ = 2 * (a - 1) + 2 * Real.sqrt (a * (a - 2)) := by ring
    rw [hnum]
    field_simp [ha1_pos.ne']
  have hsin_sq : Real.sin φ ^ 2 = ((Real.sqrt a - Real.sqrt (a - 2)) / (2 * Real.sqrt (a - 1))) ^ 2 := by
    have hdouble : Real.sin φ ^ 2 = (1 - Real.cos (2 * φ)) / 2 := by
      linarith [Real.cos_two_mul' φ, Real.sin_sq_add_cos_sq φ]
    rw [hdouble, hcos_2φ, div_pow, mul_pow, hsq_a1]
    have hnum : (Real.sqrt a - Real.sqrt (a - 2)) ^ 2 = 2 * (a - 1) - 2 * Real.sqrt (a * (a - 2)) := by
      calc (Real.sqrt a - Real.sqrt (a - 2)) ^ 2
          = Real.sqrt a ^ 2 - 2 * (Real.sqrt a * Real.sqrt (a - 2)) + Real.sqrt (a - 2) ^ 2 := by ring
        _ = a - 2 * Real.sqrt (a * (a - 2)) + (a - 2) := by rw [hsq_a, hsq_a2, hsqrt_prod]
        _ = 2 * (a - 1) - 2 * Real.sqrt (a * (a - 2)) := by ring
    rw [hnum]
    field_simp [ha1_pos.ne']
  have hrhs1_nn : 0 ≤ (Real.sqrt a + Real.sqrt (a - 2)) / (2 * Real.sqrt (a - 1)) := by positivity
  have hrhs2_nn : 0 ≤ (Real.sqrt a - Real.sqrt (a - 2)) / (2 * Real.sqrt (a - 1)) := by
    refine div_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))) (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg Real.sqrt hcos_sq
    rwa [Real.sqrt_sq hcos_φ_nn, Real.sqrt_sq hrhs1_nn] at h
  · have h := congrArg Real.sqrt hsin_sq
    rwa [Real.sqrt_sq hsin_φ_nn, Real.sqrt_sq hrhs2_nn] at h
  · intro ℓ
    have h4 : 4 * (ℓ : ℝ) * φ = (ℓ : ℝ) * π - (2 * (ℓ : ℝ)) * θ := by
      dsimp [φ]; ring
    rw [h4, Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, zero_mul, add_zero]
    have hcheb := Polynomial.Chebyshev.T_real_cos θ (2 * (ℓ : ℤ))
    rw [hcos_θ, show ((2 * (ℓ : ℤ) : ℤ) : ℝ) = 2 * (ℓ : ℝ) by push_cast; ring] at hcheb
    rw [hcheb]

/-! ### Section 4: Cardy harmonic formula and `ℓ = 0` specialization (`spinnotes:S1`(b)) -/

/-- First clause of `spinnotes:S1`(b): exact Bessel–Chebyshev expansion of `spinV2Harmonic a ℓ t`
for `a ≥ 2`, `ℓ : ℕ`, `t ≥ 0`. -/
theorem spinV2Harmonic_eq {a : ℝ} (ha : 2 ≤ a) (ℓ : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    spinV2Harmonic a ℓ t =
      2 * π * (besselI (4 * ℓ) (4 * π * Real.sqrt (a * t)) -
        2 * (-1 : ℝ) ^ ℓ * (Polynomial.Chebyshev.T ℝ (2 * ℓ : ℤ)).eval (1 / (a - 1)) *
          besselI (4 * ℓ) (4 * π * Real.sqrt ((a - 1) * t)) +
        besselI (4 * ℓ) (4 * π * Real.sqrt ((a - 2) * t))) := by
  unfold spinV2Harmonic
  have hsplit : ∀ ψ : ℝ,
      Real.cos (4 * (ℓ : ℝ) * ψ) *
        spinV1 a (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ)) *
        spinV1 a (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ)) =
      (Real.cos (4 * (ℓ : ℝ) * ψ) *
          Real.cosh (2 * π * Real.sqrt a * (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ))) *
          Real.cosh (2 * π * Real.sqrt a * (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ))) -
        Real.cos (4 * (ℓ : ℝ) * ψ) *
          Real.cosh (2 * π * Real.sqrt a * (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ))) *
          Real.cosh (2 * π * Real.sqrt (a - 2) * (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ)))) -
      (Real.cos (4 * (ℓ : ℝ) * ψ) *
          Real.cosh (2 * π * Real.sqrt (a - 2) * (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ))) *
          Real.cosh (2 * π * Real.sqrt a * (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ))) -
        Real.cos (4 * (ℓ : ℝ) * ψ) *
          Real.cosh (2 * π * Real.sqrt (a - 2) * (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ))) *
          Real.cosh (2 * π * Real.sqrt (a - 2) * (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ)))) := by
    intro ψ; unfold spinV1; ring
  rw [intervalIntegral.integral_congr (fun ψ _ => hsplit ψ),
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π))
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π)),
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π))
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π)),
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π))
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * π))]
  have h1 := spin_cosh_prod_harmonic_diag ℓ (by linarith : 0 ≤ a) ht
  have h4 := spin_cosh_prod_harmonic_diag ℓ (by linarith : 0 ≤ a - 2) ht
  obtain ⟨hcos_φ, hsin_φ, hcheb⟩ := cross_angle_trig ha
  set θ := Real.arccos (1 / (a - 1))
  set φ := (π / 2 - θ) / 2
  have ha1_pos : (0 : ℝ) < a - 1 := by linarith
  have hsq1 : Real.sqrt ((a - 1) * t) = Real.sqrt (a - 1) * Real.sqrt t :=
    Real.sqrt_mul ha1_pos.le t
  have hsq1_ne : Real.sqrt (a - 1) ≠ 0 := (Real.sqrt_pos.mpr ha1_pos).ne'
  have h2 := spin_cosh_prod_harmonic ℓ ht (α := Real.sqrt a) (β := Real.sqrt (a - 2))
    (R := 4 * π * Real.sqrt ((a - 1) * t)) (φ₁ := -φ) (φ₂ := φ - π / 2)
    (by rw [Real.cos_neg, hcos_φ, hsq1]; field_simp [hsq1_ne]; ring)
    (by rw [Real.sin_neg, hsin_φ, hsq1]; field_simp [hsq1_ne]; ring)
    (by rw [Real.cos_sub_pi_div_two, hsin_φ, hsq1]; field_simp [hsq1_ne]; ring)
    (by rw [Real.sin_sub_pi_div_two, hcos_φ, hsq1]; field_simp [hsq1_ne]; ring)
  have h3 := spin_cosh_prod_harmonic ℓ ht (α := Real.sqrt (a - 2)) (β := Real.sqrt a)
    (R := 4 * π * Real.sqrt ((a - 1) * t)) (φ₁ := φ) (φ₂ := -φ - π / 2)
    (by rw [hcos_φ, hsq1]; field_simp [hsq1_ne]; ring)
    (by rw [hsin_φ, hsq1]; field_simp [hsq1_ne]; ring)
    (by rw [Real.cos_sub_pi_div_two, Real.sin_neg, hsin_φ, hsq1]; field_simp [hsq1_ne]; ring)
    (by rw [Real.sin_sub_pi_div_two, Real.cos_neg, hcos_φ, hsq1]; field_simp [hsq1_ne]; ring)
  have hcos_neg : Real.cos (4 * (ℓ : ℝ) * -φ) = Real.cos (4 * (ℓ : ℝ) * φ) := by
    rw [mul_neg, Real.cos_neg]
  have hcos_shift1 : Real.cos (4 * (ℓ : ℝ) * (φ - π / 2)) = Real.cos (4 * (ℓ : ℝ) * φ) := by
    have heq : 4 * (ℓ : ℝ) * φ = 4 * (ℓ : ℝ) * (φ - π / 2) + ((ℓ : ℕ) : ℝ) * (2 * π) := by ring
    rw [heq, Real.cos_add_nat_mul_two_pi]
  have hcos_shift2 : Real.cos (4 * (ℓ : ℝ) * (-φ - π / 2)) = Real.cos (4 * (ℓ : ℝ) * φ) := by
    have heq : 4 * (ℓ : ℝ) * (-φ - π / 2) = -(4 * (ℓ : ℝ) * φ + ((ℓ : ℕ) : ℝ) * (2 * π)) := by ring
    rw [heq, Real.cos_neg, Real.cos_add_nat_mul_two_pi]
  rw [h1, h2, h3, h4, hcos_neg, hcos_shift1, hcos_shift2, hcheb ℓ]
  ring

private lemma kernelK_one_eq_besselI0 {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t) :
    kernelK 1 α t = besselI 0 (4 * π * Real.sqrt (α * t)) := by
  unfold kernelK kernelKTerm besselI besselS besselTerm
  simp only [Nat.sub_self, pow_zero, one_mul, add_zero, Nat.add_sub_cancel]
  refine tsum_congr fun k => ?_
  have hsq : (4 * π * Real.sqrt (α * t)) ^ 2 / 4 = 4 * π ^ 2 * α * t := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hα ht)]
    ring
  rw [hsq]

/-- Second clause of `spinnotes:S1`(b): at `ℓ = 0`, `spinV2Harmonic a 0 t = ρ_C(t)`. -/
theorem spinV2Harmonic_zero_eq_cardyDensity {a : ℝ} (ha : 2 ≤ a) {t : ℝ} (ht : 0 ≤ t) :
    spinV2Harmonic a 0 t = virasoroProblem.cardyDensity a t := by
  rw [spinV2Harmonic_eq ha 0 ht]
  unfold FixedWeightProblem.cardyDensity
  rw [virasoro_cardyV_eq, kernelK_one_eq_besselI0 (by linarith) ht,
    kernelK_one_eq_besselI0 (by linarith) ht, kernelK_one_eq_besselI0 (by linarith) ht]
  simp

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_besselI_integral_cosh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_besselI_integral_cosh

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_cosh_integral_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_cosh_integral_zero

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinV2Harmonic_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinV2Harmonic_eq

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinV2Harmonic_zero_eq_cardyDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinV2Harmonic_zero_eq_cardyDensity

end FormalResearch.ModularBootstrap.Spin
