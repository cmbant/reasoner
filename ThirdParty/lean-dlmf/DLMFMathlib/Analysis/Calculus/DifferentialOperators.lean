/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Weighted first-order differential operators

The operators `z ↦ z (z f(z))'` and `z ↦ (1-z) ((1-z) f(z))'`, for `f : 𝕜 → F` with `𝕜` a
nontrivially normed field and `F` a normed space over `𝕜`; the weights act by scalar
multiplication.

## Main definitions

* `mulDerivMul`: the operator `f ↦ z (z f)'`.
* `oneSubMulDerivMul`: the operator `f ↦ (1-z) ((1-z) f)'`.

## Main results

* `mulDerivMul_eq_mul`, `oneSubMulDerivMul_eq_mul`: the forms with multiplication for `F = 𝕜`.

## Implementation notes

The definitions use Mathlib's totalized derivative, so identities involving their iterates
require the appropriate smoothness assumptions.
-/

@[expose] public noncomputable section

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The weighted differential operator `f ↦ z (z f)'`. -/
def mulDerivMul (f : 𝕜 → F) (z : 𝕜) : F :=
  z • deriv (fun w => w • f w) z

/-- The weighted differential operator `f ↦ (1-z) ((1-z) f)'`. -/
def oneSubMulDerivMul (f : 𝕜 → F) (z : 𝕜) : F :=
  (1 - z) • deriv (fun w => (1 - w) • f w) z

/-- `mulDerivMul` on scalar-valued functions, written with multiplication. -/
theorem mulDerivMul_eq_mul (f : 𝕜 → 𝕜) (z : 𝕜) :
    mulDerivMul f z = z * deriv (fun w => w * f w) z :=
  rfl

/-- `oneSubMulDerivMul` on scalar-valued functions, written with multiplication. -/
theorem oneSubMulDerivMul_eq_mul (f : 𝕜 → 𝕜) (z : 𝕜) :
    oneSubMulDerivMul f z = (1 - z) * deriv (fun w => (1 - w) * f w) z :=
  rfl
