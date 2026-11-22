/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.KummerM
-- PATCH: removed `public import TauCeti.RingTheory.Polynomial.Hermite.Derivative` (TauCeti is not a dependency; the file does not use it)

/-!
# Canonical parabolic cylinder functions and Weber solution data

This file is the canonical home of Weber's parabolic cylinder functions `U(a,z)` and
`V(a,z)`, Whittaker's `D_ν(z)`, and the even and odd solutions of Weber's equation
`w'' = (z²/4 + a) w` (DLMF §12.2, §12.4, §12.7).

## Main definitions

* `parabolicCylinderEven`, `parabolicCylinderOdd`: the even and odd solutions `u₁`, `u₂` (DLMF
  12.7.12–12.7.13), with derivatives `parabolicCylinderEvenDeriv`, `parabolicCylinderOddDeriv`.
* `parabolicCylinderU`, `parabolicCylinderUDeriv`: Weber's function `U(a,z)` (DLMF 12.4.1) and its
  derivative.
* `parabolicCylinderD`: Whittaker's notation `D_ν(z) = U(-ν - 1/2, z)` (DLMF 12.2.5).
* `parabolicCylinderVZero`, `parabolicCylinderVDerivZero`: the initial values `V(a,0)`, `V'(a,0)`
  (DLMF 12.2.8–12.2.9).
* `parabolicCylinderV`, `parabolicCylinderVDeriv`: Weber's second function `V(a,z)` (DLMF 12.4.2)
  and its derivative.
* `IsWeberSolution`: a function and a derivative candidate solve Weber's equation.
* `parabolicCylinderMoment`: the moments `∫₀^∞ t^c e^{-t²/2 - zt} dt` used in DLMF 12.5.1.

## Implementation notes

`U(a,z)` is the entire solution fixed by its initial values (DLMF 12.2.6–12.2.7). The initial
values of `V` are written with reciprocal Gamma factors, so that `V(a,z)` is entire in `a`
and `z`.
-/

public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric
open MeasureTheory intervalIntegral

namespace DLMF.Confluent

/-- The even solution `u₁(a,z) = e^{-z²/4} M(a/2 + 1/4, 1/2, z²/2)` (DLMF 12.7.12). -/
@[expose,
  dlmf 12.7.E12]
def parabolicCylinderEven (a z : ℂ) : ℂ :=
  exp (-z ^ 2 / 4) * kummerM (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2)

/-- The odd solution `u₂(a,z) = z e^{-z²/4} M(a/2 + 3/4, 3/2, z²/2)` (DLMF 12.7.13). -/
@[expose,
  dlmf 12.7.E13]
def parabolicCylinderOdd (a z : ℂ) : ℂ :=
  z * exp (-z ^ 2 / 4) * kummerM (a / 2 + 3 / 4) (3 / 2) (z ^ 2 / 2)

/-- The derivative of `u₁`. -/
@[expose]
def parabolicCylinderEvenDeriv (a z : ℂ) : ℂ :=
  z * exp (-z ^ 2 / 4) * (-(1 / 2) * kummerM (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2) +
    (a + 1 / 2) * kummerM (a / 2 + 1 / 4 + 1) (1 / 2 + 1) (z ^ 2 / 2))

/-- The derivative of `u₂`. -/
@[expose]
def parabolicCylinderOddDeriv (a z : ℂ) : ℂ :=
  exp (-z ^ 2 / 4) * ((1 - z ^ 2 / 2) * kummerM (a / 2 + 3 / 4) (3 / 2) (z ^ 2 / 2) +
    (a + 3 / 2) / 3 * z ^ 2 * kummerM (a / 2 + 3 / 4 + 1) (3 / 2 + 1) (z ^ 2 / 2))

/-- **Weber's parabolic cylinder function** `U(a,z)`, the entire solution of
`w'' = (z²/4 + a) w` fixed by its initial values (DLMF 12.2.6, 12.2.7, 12.4.1):
`U(a,z) = U(a,0) u₁(a,z) + U'(a,0) u₂(a,z)`. The reciprocal Gamma factors vanish at the
poles, as for the entire function `1/Γ`. -/
@[expose,
  dlmf 12.4.E1]
def parabolicCylinderU (a z : ℂ) : ℂ :=
  (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ *
      parabolicCylinderEven a z -
    (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹ *
        parabolicCylinderOdd a z

/-- The derivative `U'(a,z)`. -/
@[expose]
def parabolicCylinderUDeriv (a z : ℂ) : ℂ :=
  (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ *
      parabolicCylinderEvenDeriv a z -
    (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹ *
        parabolicCylinderOddDeriv a z

/-- Whittaker's notation `D_ν(z) = U(-ν - 1/2, z)` (DLMF 12.2.5). -/
@[expose,
  dlmf 12.2.E5]
def parabolicCylinderD (ν z : ℂ) : ℂ := parabolicCylinderU (-ν - 1 / 2) z

/-- A function and a derivative candidate solve Weber's equation with parameter `a`. -/
@[expose]
def IsWeberSolution (a : ℂ) (f f' : ℂ → ℂ) : Prop :=
  ∀ z, HasDerivAt f (f' z) z ∧ HasDerivAt f' ((z ^ 2 / 4 + a) * f z) z

/-- The moments `∫₀^∞ t^c e^{-t²/2 - z t} dt` used in DLMF 12.5.1. -/
@[expose]
def parabolicCylinderMoment (c z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)

/-- `V(a,0)` (DLMF 12.2.8), with reciprocal Gamma factors, so that it is entire in `a`. -/
@[expose]
def parabolicCylinderVZero (a : ℂ) : ℂ :=
  π * (2 : ℂ) ^ (a / 2 + 1 / 4) * (Gamma (3 / 4 - a / 2))⁻¹ ^ 2 * (Gamma (1 / 4 + a / 2))⁻¹

/-- `V'(a,0)` (DLMF 12.2.9), with reciprocal Gamma factors. -/
@[expose]
def parabolicCylinderVDerivZero (a : ℂ) : ℂ :=
  π * (2 : ℂ) ^ (a / 2 + 3 / 4) * (Gamma (1 / 4 - a / 2))⁻¹ ^ 2 * (Gamma (3 / 4 + a / 2))⁻¹

/-- **Weber's second function** `V(a,z) = V(a,0) u₁(a,z) + V'(a,0) u₂(a,z)` (DLMF 12.4.2). It is
entire in `a` and `z`; see `parabolicCylinderV_eq` for the classical form in terms of `U(a, ±z)`. -/
@[expose,
  dlmf 12.4.E2]
def parabolicCylinderV (a z : ℂ) : ℂ := parabolicCylinderVZero a * parabolicCylinderEven a z +
    parabolicCylinderVDerivZero a * parabolicCylinderOdd a z

/-- The derivative `V'(a,z)`. -/
@[expose]
def parabolicCylinderVDeriv (a z : ℂ) : ℂ := parabolicCylinderVZero a *
    parabolicCylinderEvenDeriv a z + parabolicCylinderVDerivZero a * parabolicCylinderOddDeriv a z

end DLMF.Confluent
