/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.KummerM
public import TauCeti.Analysis.SpecialFunctions.Erf
public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Error functions, Fresnel integrals and Dawson's integral

This file defines the error function through Kummer's function (DLMF 13.6.7), its complement,
and the real Fresnel integrals, Dawson's integral and the auxiliary Fresnel functions of
DLMF §7.2.

## Main definitions

* `erf`: the entire error function `erf z = (2z/√π) M(1/2, 3/2, -z²)` (DLMF 13.6.7).
* `erfc`: the complementary error function `1 - erf z`.
* `Real.fresnelC`, `Real.fresnelS`: the Fresnel integrals `C(x)` and `S(x)`
  (DLMF 7.2.7, 7.2.8).
* `Real.dawsonF`: Dawson's integral `F(x)` (DLMF 7.2.5).
* `fresnelAuxiliaryF`, `fresnelAuxiliaryG`: the auxiliary Fresnel functions `f(x)` and `g(x)`
  (DLMF 7.2.10, 7.2.11).
* `fresnelZeta`: the Fresnel variable `ζ = √π (1 - i) x / 2` of DLMF 7.5.7.

## Implementation notes

On the real line `erf` agrees with TauCeti's `TauCeti.Real.erf`.
-/

public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric
open MeasureTheory intervalIntegral

namespace DLMF.Confluent

/-- The error function, entire in `z`, through the confluent series of AAR §4.4:
`erf z = (2z/√π) M(1/2, 3/2, -z²)`. On the real line it is TauCeti's `TauCeti.Real.erf`
(`erf_ofReal`). -/
@[expose,
  dlmf 13.6.E7]
def erf (z : ℂ) : ℂ :=
  (2 : ℂ) / (Real.sqrt π : ℂ) * z * kummerM (1 / 2) (3 / 2) (-(z ^ 2))

/-- Complementary error function `erfc z = 1 - erf z`. -/
@[expose]
def erfc (z : ℂ) : ℂ := 1 - erf z

/-- The Fresnel cosine integral `C(x) = ∫₀ˣ cos(π t²/2) dt` (DLMF 7.2.7). -/
@[expose,
  dlmf 7.2.E7]
def Real.fresnelC (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.cos (π * t ^ 2 / 2)

/-- The Fresnel sine integral `S(x) = ∫₀ˣ sin(π t²/2) dt` (DLMF 7.2.8). -/
@[expose,
  dlmf 7.2.E8]
def Real.fresnelS (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.sin (π * t ^ 2 / 2)

/-- Dawson's integral `F(x) = e^{-x²} ∫₀ˣ e^{t²} dt` (DLMF 7.2.5). -/
@[expose,
  dlmf 7.2.E5]
def Real.dawsonF (x : ℝ) : ℝ := Real.exp (-x ^ 2) * ∫ t in (0 : ℝ)..x, Real.exp (t ^ 2)

/-- The auxiliary Fresnel function `f(x) = (1/2 - S(x)) cos(πx²/2) - (1/2 - C(x)) sin(πx²/2)`
(DLMF 7.2.10). -/
@[expose,
  dlmf 7.2.E10]
def fresnelAuxiliaryF (x : ℝ) : ℝ :=
  (1 / 2 - Real.fresnelS x) * Real.cos (π * x ^ 2 / 2) - (1 / 2 - Real.fresnelC x)
      * Real.sin (π * x ^ 2 / 2)

/-- The auxiliary Fresnel function `g(x) = (1/2 - C(x)) cos(πx²/2) + (1/2 - S(x)) sin(πx²/2)`
(DLMF 7.2.11). -/
@[expose,
  dlmf 7.2.E11]
def fresnelAuxiliaryG (x : ℝ) : ℝ :=
  (1 / 2 - Real.fresnelC x) * Real.cos (π * x ^ 2 / 2) + (1 / 2 - Real.fresnelS x)
      * Real.sin (π * x ^ 2 / 2)

/-- The Fresnel variable `ζ = √π (1 - i) x / 2` of DLMF 7.5.7. -/
@[expose]
def fresnelZeta (x : ℝ) : ℂ := (Real.sqrt π : ℂ) * (1 - I) / 2 * x

end DLMF.Confluent
