/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Basic
public import DLMF.Confluent.Basic.ErrorFunctions

/-!
# Complex error, Fresnel, Dawson and Gaussian primitives

Definitions of the entire functions of DLMF §7.2, of the alternative notations of DLMF §7.1,
of the repeated integrals of `erfc` (DLMF §7.18) and of the Voigt functions (DLMF §7.19).
The complex error functions `erf` and `erfc` themselves are defined in
`DLMF.Confluent.Basic.ErrorFunctions`.

## Main definitions

* `faddeevaW`: the Faddeeva function `w(z)` (DLMF 7.2.3).
* `dawsonF`: Dawson's integral `F(z)` (DLMF 7.2.5).
* `fresnelC`, `fresnelS`, `fresnelTail`: the Fresnel integrals `C(z)`, `S(z)` and
  `ℱ(z)` (DLMF 7.2.6–7.2.8).
* `fresnelAuxiliaryFComplex`, `fresnelAuxiliaryGComplex`: the auxiliary functions `f(z)`, `g(z)`
  (DLMF 7.2.10, 7.2.11).
* `goodwinStatonG`: the Goodwin–Staton integral `G(z)` on the slit plane (DLMF 7.2.12).
* `gaussianTail`, `gaussianCdf`, `scaledErf`, `dawsonPrimitive`: the alternative notations
  `Q`, `P`, `Erf` and `Erfi` of DLMF §7.1.
* `fresnelC1`, `fresnelS1`, `fresnelC2`, `fresnelS2`: the alternative Fresnel normalizations of
  DLMF §7.1.
* `iteratedErfc`: the repeated integrals `iⁿ erfc(z)` (DLMF 7.18.1, 7.18.2); only indices
  `n ≥ -1` are meaningful.
* `Real.voigtU`, `Real.voigtV`: the Voigt functions for `t > 0` (DLMF 7.19.1, 7.19.2).
* `Real.voigtH`: the line-broadening function for `a > 0` (DLMF 7.19.4).
-/

public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric
open MeasureTheory

open DLMF.Core

namespace DLMF.Confluent

/-- Faddeeva complex probability function. -/
@[expose,
  dlmf 7.2.E3]
def faddeevaW (z : ℂ) : ℂ :=
  exp (-z^2)*erfc (-I*z)

/-- Entire Dawson integral. -/
@[expose,
  dlmf 7.2.E5]
def dawsonF (z : ℂ) : ℂ :=
  exp (-z^2)*primitive (fun t => exp (t^2)) z

/-- Entire Fresnel cosine integral. -/
@[expose,
  dlmf 7.2.E7]
def fresnelC (z : ℂ) : ℂ :=
  primitive (fun t => cos (π*t^2/2)) z

/-- Entire Fresnel sine integral. -/
@[expose,
  dlmf 7.2.E8]
def fresnelS (z : ℂ) : ℂ :=
  primitive (fun t => sin (π*t^2/2)) z

/-- Entire continued Fresnel tail integral. -/
@[expose,
  dlmf 7.2.E6]
def fresnelTail (z : ℂ) : ℂ :=
  (1+I)/2 - fresnelC z-I*fresnelS z

/-- Entire Fresnel auxiliary f. -/
@[expose,
  dlmf 7.2.E10]
def fresnelAuxiliaryFComplex (z : ℂ) : ℂ :=
  (1/2-fresnelS z)*cos (π*z^2/2)-(1/2-fresnelC z)*sin (π*z^2/2)

/-- Entire Fresnel auxiliary g. -/
@[expose,
  dlmf 7.2.E11]
def fresnelAuxiliaryGComplex (z : ℂ) : ℂ :=
  (1/2-fresnelC z)*cos (π*z^2/2)+(1/2-fresnelS z)*sin (π*z^2/2)

/-- Goodwin–Staton integral on the slit plane. -/
@[expose,
  dlmf 7.2.E12]
def goodwinStatonG (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)^2)/(t+z)

/-- Alternative Q notation in DLMF §7.1. -/
@[expose]
def gaussianTail (z : ℂ) : ℂ :=
  erfc (z/Real.sqrt 2)/2

/-- Alternative P or Φ notation in DLMF §7.1. -/
@[expose]
def gaussianCdf (z : ℂ) : ℂ :=
  erfc (-z/Real.sqrt 2)/2

/-- The capitalized Erf convention of DLMF §7.1. -/
@[expose]
def scaledErf (z : ℂ) : ℂ :=
  Real.sqrt π/2*erf z

/-- DLMF §7.1 Erfi normalization, without the usual 2/sqrt(π) factor. -/
@[expose]
def dawsonPrimitive (z : ℂ) : ℂ :=
  exp (z^2)*dawsonF z

/-- Alternative Fresnel C₁ normalization. -/
@[expose]
def fresnelC1 (z : ℂ) : ℂ :=
  fresnelC (Real.sqrt (2/π)*z)

/-- Alternative Fresnel S₁ normalization. -/
@[expose]
def fresnelS1 (z : ℂ) : ℂ :=
  fresnelS (Real.sqrt (2/π)*z)

/-- Alternative Fresnel C₂ normalization with the principal square root. -/
@[expose]
def fresnelC2 (z : ℂ) : ℂ :=
  fresnelC ((2*z/π)^(1/2 : ℂ))

/-- Alternative Fresnel S₂ normalization with the principal square root. -/
@[expose]
def fresnelS2 (z : ℂ) : ℂ :=
  fresnelS ((2*z/π)^(1/2 : ℂ))

/-- Repeated complementary Gaussian tail; only indices at least -1 have mathematical meaning. -/
@[expose,
  dlmf 7.18.E1, dlmf 7.18.E2]
def iteratedErfc (n : ℤ) (z : ℂ) : ℂ :=
  if n = -1 then 2/Real.sqrt π*exp (-z^2) else if n < 0 then 0 else
    2/Real.sqrt π*(∫ t : ℝ in Ioi 0, (t : ℂ)^n.toNat/(n.toNat.factorial : ℂ)*exp (-(z+t)^2))

/-- Voigt U for t>0. -/
@[expose,
  dlmf 7.19.E1]
def Real.voigtU (x t : ℝ) : ℝ :=
  1/Real.sqrt (4*π*t)*(∫ y : ℝ, Real.exp (-(x-y)^2/(4*t))/(1+y^2))

/-- Voigt V for t>0. -/
@[expose,
  dlmf 7.19.E2]
def Real.voigtV (x t : ℝ) : ℝ :=
  1/Real.sqrt (4*π*t)*(∫ y : ℝ, y*Real.exp (-(x-y)^2/(4*t))/(1+y^2))

/-- Voigt line-broadening profile for a>0. -/
@[expose,
  dlmf 7.19.E4]
def Real.voigtH (a u : ℝ) : ℝ :=
  a/π*(∫ t : ℝ, Real.exp (-t^2)/((u-t)^2+a^2))

end DLMF.Confluent
