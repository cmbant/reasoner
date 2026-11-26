module

public import Mathlib

/-!
# Dyadic absorption (phase-free)

The absorption step of the multiscale dyadic bootstrap (`constant_terms_lower.tex`, `ct:dyadic` Part (1), Step 1c;
Paper II `ctl:dyadic`): a finite quantity `L` obeying `L ≤ a(1+k) + b e^{-k} L` with `b e^{-k} ≤ 1/2` satisfies
`L ≤ 2a(1+k)`.  Proved; `absorb_dyadic` is the form used with `L = L_max`, `a = C_*'`, `b = C_*'`.
-/

@[expose] public section

namespace FormalResearch.Asymptotics

/-- `L ≤ A + θ L` with `θ ≤ 1/2` gives `L ≤ 2A`. -/
theorem absorb_half {L A θ : ℝ} (hθ : θ ≤ 1 / 2) (hL : 0 ≤ L) (h : L ≤ A + θ * L) : L ≤ 2 * A := by
  nlinarith

/-- **Dyadic absorption.** If `L ≥ 0`, `L ≤ a(1+k) + b e^{-k} L` and `b e^{-k} ≤ 1/2`, then `L ≤ 2a(1+k)`. -/
theorem absorb_dyadic {L a b k : ℝ} (hL : 0 ≤ L) (hbk : b * Real.exp (-k) ≤ 1 / 2)
    (h : L ≤ a * (1 + k) + b * Real.exp (-k) * L) : L ≤ 2 * (a * (1 + k)) :=
  absorb_half hbk hL h

/-- The threshold: for `b > 0`, `k ≥ log (2 b)` gives `b e^{-k} ≤ 1/2`. -/
theorem exp_small_of_ge_log {b k : ℝ} (hb : 0 < b) (hk : Real.log (2 * b) ≤ k) :
    b * Real.exp (-k) ≤ 1 / 2 := by
  have h1 : Real.exp (Real.log (2 * b)) ≤ Real.exp k := Real.exp_le_exp.mpr hk
  rw [Real.exp_log (by positivity)] at h1
  have h2 : Real.exp (-k) = (Real.exp k)⁻¹ := Real.exp_neg k
  have hk0 : 0 < Real.exp k := Real.exp_pos k
  rw [h2, ← div_eq_mul_inv, div_le_iff₀ hk0]
  linarith

/-- info: 'FormalResearch.Asymptotics.absorb_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.absorb_dyadic

end FormalResearch.Asymptotics
