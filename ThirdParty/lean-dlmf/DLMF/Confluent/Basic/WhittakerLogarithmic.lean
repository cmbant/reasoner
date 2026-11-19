/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.Whittaker
public import DLMF.Confluent.Basic.TricomiLogarithmic

/-!
# Full parameter continuation of Whittaker W on the logarithmic plane

Whittaker's `W` is formed from the whole-parameter continued Tricomi function, so
integer second parameters are included. The logarithmic coordinate records winding
without reducing its imaginary part modulo `2*pi`. Olver, *Asymptotics and Special
Functions*, Chapter 7, §10, pp. 260–262; DLMF 13.14.3.
-/

public noncomputable section

open Complex

namespace DLMF.Confluent

/-- Whittaker's `W` on the logarithmic argument plane, including every complex
parameter pair. The exponential power is normalized by the chosen logarithm `w`,
and Tricomi's whole-parameter limits supply exceptional second parameters.
Olver, Chapter 7, §10, pp. 260–262; DLMF 13.14.3. -/
@[expose]
def whittakerWContinuedOnLog (κ μ w : ℂ) : ℂ :=
  exp (-exp w / 2) * exp ((μ + 1 / 2) * w) *
    kummerUContinuedOnLog (μ - κ + 1 / 2) (1 + 2 * μ) w

/-- The defining continued-Tricomi expression of logarithmic Whittaker W. -/
theorem whittakerWContinuedOnLog_def (κ μ w : ℂ) :
    whittakerWContinuedOnLog κ μ w =
      exp (-exp w / 2) * exp ((μ + 1 / 2) * w) *
        kummerUContinuedOnLog (μ - κ + 1 / 2) (1 + 2 * μ) w := rfl

/-- The raw logarithmic Whittaker connection expression factors through the raw
Tricomi expression. Both sides are totalized formulas, with function meaning at
noninteger twice-order. DLMF 13.14.33 and 13.2.42. -/
theorem whittakerWConnectionOnLog_eq_kummerUConnectionOnLog (κ μ w : ℂ) :
    whittakerWConnectionOnLog κ μ w = exp (-exp w / 2) * exp ((μ + 1 / 2) * w) *
      kummerUConnectionOnLog (1 / 2 + μ - κ) (1 + 2 * μ) w := by
  unfold whittakerWConnectionOnLog whittakerMOnLog kummerUConnectionOnLog
  rw [show 1 - (1 + 2 * μ) = -2 * μ by ring,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring,
    show 1 + 2 * μ - 1 = 2 * μ by ring,
    show 2 - (1 + 2 * μ) = 1 + 2 * -μ by ring,
    show μ - κ + 1 / 2 = 1 / 2 + μ - κ by ring,
    show -μ - κ + 1 / 2 = 1 / 2 - μ - κ by ring]
  have he : exp ((-μ + 1 / 2) * w) = exp ((μ + 1 / 2) * w) * exp ((-2 * μ) * w) := by
    rw [← exp_add]; congr 1; ring
  rw [he]
  ring


/-- At noninteger twice-order the full continued function is its connection
expression. Olver, Chapter 7, §10; DLMF 13.14.33. -/
theorem whittakerWContinuedOnLog_of_not_int (κ μ w : ℂ)
    (hμ : ∀ n : ℤ, 2 * μ ≠ n) :
    whittakerWContinuedOnLog κ μ w = whittakerWConnectionOnLog κ μ w := by
  have hb : ∀ n : ℤ, 1 + 2 * μ ≠ n := by
    intro n hn
    apply hμ (n - 1)
    push_cast
    linear_combination hn
  rw [whittakerWContinuedOnLog_def,
    kummerUContinuedOnLog_of_not_int _ _ _ hb,
    whittakerWConnectionOnLog_eq_kummerUConnectionOnLog]
  congr 2
  ring


end DLMF.Confluent
