/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.Tricomi

/-!
# Full parameter continuation of Tricomi's function on the logarithmic plane

The raw connection formula `kummerUConnectionOnLog` has its intended function meaning at
noninteger second parameters. Here its whole-parameter limit defines the values at
integer parameters without changing that raw formula. The complex variable `w` is
a logarithm of the actual nonzero argument; its imaginary part is not reduced modulo `2π`.
Temme, *Special Functions* (1996), Chapter 7, equations (7.12)–(7.15).
-/

public noncomputable section

open Complex Filter
open scoped Topology Classical

namespace DLMF.Confluent

/-- Tricomi's function on the logarithmic argument plane, continued in its second
parameter through whole connection-formula limits. The value is normalized by the
principal connection formula when `|Im w|<π`. The definition itself does not establish
existence of the integer-parameter limit. Temme (7.12)–(7.15), TEM-07-03 and TEM-07-04. -/
@[expose]
def kummerUContinuedOnLog (a b w : ℂ) : ℂ :=
  if ∀ k : ℤ, b ≠ k then kummerUConnectionOnLog a b w else
    limUnder (𝓝[integerComplement] b) (fun c => kummerUConnectionOnLog a c w)

/-- The whole-parameter limit defining the continued logarithmic function. -/
theorem kummerUContinuedOnLog_def (a b w : ℂ) :
    kummerUContinuedOnLog a b w =
      if ∀ k : ℤ, b ≠ k then kummerUConnectionOnLog a b w else
        limUnder (𝓝[integerComplement] b) (fun c => kummerUConnectionOnLog a c w) := rfl

/-- At noninteger second parameters the continued function is the raw connection formula. -/
theorem kummerUContinuedOnLog_of_not_int (a b w : ℂ) (hb : ∀ k : ℤ, b ≠ k) :
    kummerUContinuedOnLog a b w = kummerUConnectionOnLog a b w := by
  rw [kummerUContinuedOnLog_def, ite_eq_left hb]

/-- At an integer second parameter the complete parameter limit is retained. -/
theorem kummerUContinuedOnLog_int (a w : ℂ) (n : ℤ) :
    kummerUContinuedOnLog a n w =
      limUnder (𝓝[integerComplement] (n : ℂ)) (fun c => kummerUConnectionOnLog a c w) := by
  rw [kummerUContinuedOnLog_def, ite_eq_right (by intro h; exact h n rfl)]

/-- In the principal logarithmic strip the raw lifted expression equals the
principal connection formula, including its totalized exceptional values.
Temme, Chapter 7, (7.14)–(7.15); DLMF 13.2.42. -/
theorem kummerUConnectionOnLog_eq_connection (a b : ℂ) {w : ℂ}
    (hleft : -Real.pi < w.im) (hright : w.im ≤ Real.pi) :
    kummerUConnectionOnLog a b w = kummerUConnection a b (exp w) := by
  simp only [kummerUConnectionOnLog, kummerUConnection,
    cpow_def_of_ne_zero (exp_ne_zero w), log_exp hleft hright]
  rw [mul_comm (1 - b) w]


end DLMF.Confluent
