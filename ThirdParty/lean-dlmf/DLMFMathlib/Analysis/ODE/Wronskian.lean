/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.RealDeriv
/-!
# Wronskians of two functions

`ODE.wronskian f g` is `f g' - g f'` (DLMF 1.13.4). The scalar field and the normed-ring target
are independent, so real and complex functions and complex-valued functions of a real
variable share the same definition.

## Main definitions

* `wronskian`: the Wronskian `f g' - g f'`.
* `hasDerivAt_wronskian`: its derivative for two twice differentiable functions.
* `Complex.im_deriv_mul_conj_ofReal_mul`: real-amplitude rescaling of imaginary flux.

## Implementation notes

The derivatives are totalized as in Mathlib; results about solutions of differential
equations assert differentiability separately.
-/

@[expose] public noncomputable section

namespace ODE

/-- The Wronskian `f g' - g f'` of two functions with values in a normed ring. -/
@[dlmf 1.13.E4]
def wronskian {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
    [NormedSpace 𝕜 E] (f g : 𝕜 → E) (z : 𝕜) : E :=
  f z * deriv g z - g z * deriv f z

/-- The Wronskian of two twice differentiable scalar functions has derivative
`f g'' - g f''`. The normed commutative coefficient algebra need not be complete. -/
theorem hasDerivAt_wronskian {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedCommRing A] [NormedAlgebra 𝕜 A] {f g : 𝕜 → A} {x : 𝕜}
    {f' g' f'' g'' : A} (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (hf' : HasDerivAt (deriv f) f'' x) (hg' : HasDerivAt (deriv g) g'' x) :
    HasDerivAt (wronskian f g) (f x * g'' - g x * f'') x := by
  have h := (hf.mul hg').sub (hg.mul hf')
  apply h.congr_deriv
  rw [hf.deriv, hg.deriv]
  ring

end ODE

open Complex
open scoped ComplexConjugate

/-- A differentiable real amplitude multiplies the imaginary Lagrange flux by its square;
the derivative of the amplitude contributes only a real term. -/
theorem Complex.im_deriv_mul_conj_ofReal_mul {a : ℝ → ℝ} {y : ℝ → ℂ} {x : ℝ}
    (ha : DifferentiableAt ℝ a x) (hy : DifferentiableAt ℝ y x) :
    (deriv (fun t => (a t : ℂ) * y t) x * conj ((a x : ℂ) * y x)).im =
      a x ^ 2 * (deriv y x * conj (y x)).im := by
  rw [(ha.hasDerivAt.ofReal_comp.fun_mul hy.hasDerivAt).deriv]
  simp only [map_mul, Complex.conj_ofReal, add_mul, mul_im, mul_re, add_im, ofReal_re, ofReal_im,
    conj_re, conj_im]
  ring
