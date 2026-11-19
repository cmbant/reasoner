/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.Pochhammer
public import DLMF.Hypergeometric.Basic.GaussSeries
public import DLMF.Hypergeometric.Basic.SpecialValues

/-!
# Pochhammer symbols of real arguments

The scalar power-series calculus, the representation of `₂F₁` by its series on the unit disk
and the binomial series `hasSum_pochhammer_div_factorial` are in
`DLMF.Hypergeometric.Basic.GaussSeries`.

## Main results

* `pochhammer_ofReal`: Pochhammer symbols of real arguments are real.
-/

public section

open Complex FormalMultilinearSeries
open scoped Topology ENNReal

noncomputable section

namespace DLMF.Hypergeometric

/-- Helper lemma for generating-function estimates. -/
theorem pochhammer_ofReal (x : ℝ) (n : ℕ) :
    pochhammer (x : ℂ) n = ↑((ascPochhammer ℝ n).eval x) := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    rw [pochhammer_succ, ascPochhammer_succ_eval, ih]
    push_cast
    ring

end DLMF.Hypergeometric
