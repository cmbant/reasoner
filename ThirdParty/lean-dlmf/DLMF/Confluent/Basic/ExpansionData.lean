/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Basic
public import DLMF.Hypergeometric.Basic.Pochhammer

/-!
# Coefficients of Kummer's series

This file defines coefficient sequences attached to Kummer's series `M(a,c,z)`, used for the
finite Kummer–Bessel expansion and for zero-free regions of parabolic type.

## Main definitions

* `kummerBesselCoeff`: the entire coefficient of the normalized finite Kummer–Bessel expansion.
* `SaffVarga.seriesCoeff`: the real coefficients `(a)_k / ((c)_k k!)` of Kummer's series.
* `SaffVarga.seriesCoeffRatio`: the ratio of consecutive coefficients `SaffVarga.seriesCoeff`.
-/

public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open DLMF.Hypergeometric

namespace DLMF.Confluent

/-- Entire coefficient for the normalized finite Kummer–Bessel expansion. -/
@[expose]
noncomputable def kummerBesselCoeff (ν : ℂ) (n k : ℕ) : ℂ :=
  (-1) ^ k * (n.choose k : ℂ) * pochhammer (2 * ν) k * (ν + k) *
    (1 / Gamma (2 * ν + 1 + n + k))
/-- The ratio `b (k+1) = A k / A (k+1) = (k+1)(c+k)/(a+k)` of consecutive coefficients of
Kummer's series. -/
@[expose]
noncomputable def SaffVarga.seriesCoeffRatio (a c : ℝ) (k : ℕ) : ℝ := k * (c + k - 1) / (a + k - 1)

/-- The real coefficients `(a)_k / ((c)_k k!)` of Kummer's series. -/
@[expose]
noncomputable def SaffVarga.seriesCoeff (a c : ℝ) (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval a / ((ascPochhammer ℝ k).eval c * k !)

end DLMF.Confluent
