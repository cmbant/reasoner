module

public import FormalResearch.SignUncertainty.CtOuterEntire
public import FormalResearch.CohnElkies.MellinAiryToolkit

/-!
# Elementary hyperbolic inequalities (support for the evaluation of `I_0`-type integrals)

Generic real analysis.  **Proved.**  For `y > 0`:
`sinh y > y`, `y cosh y > sinh y`, `y cosh y - sinh y ≤ y² sinh y`, `sinh y - y ≤ y³/4` for `y ≤ 2`, and
`sinh y ≥ e^y/3` for `y ≥ 1`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

lemma sinh_gt_self {y : ℝ} (hy : 0 < y) : y < Real.sinh y := FormalResearch.CohnElkies.sinh_gt_id hy

lemma sinh_lt_mul_cosh {y : ℝ} (hy : 0 < y) : Real.sinh y < y * Real.cosh y := by
  have h := FormalResearch.CohnElkies.tanh_lt_id hy
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_iff₀ (Real.cosh_pos y)] at h
  exact h

/-- `y cosh y - sinh y ≤ y² sinh y`. -/
lemma mul_cosh_sub_sinh_le {y : ℝ} (hy : 0 ≤ y) : y * Real.cosh y - Real.sinh y ≤ y ^ 2 * Real.sinh y := by
  set g : ℝ → ℝ := fun x => x ^ 2 * Real.sinh x - x * Real.cosh x + Real.sinh x with hg
  have hd : ∀ x, HasDerivAt g (x * Real.sinh x + x ^ 2 * Real.cosh x) x := by
    intro x
    have h1 := ((hasDerivAt_pow 2 x).mul (Real.hasDerivAt_sinh x)).sub
      ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)) |>.add (Real.hasDerivAt_sinh x)
    exact h1.congr_deriv (by simp; ring)
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt).continuousOn
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      have hs0 : 0 < s := hs
      have := Real.sinh_pos_iff.mpr hs0
      have := Real.cosh_pos s
      positivity
  have := hmono (le_refl (0 : ℝ) |> fun h => (show (0 : ℝ) ∈ Ici 0 from h)) (show y ∈ Ici 0 from hy) hy
  simp [hg] at this
  linarith

/-- `sinh y - y ≤ y³/4` for `0 ≤ y ≤ 2`. -/
lemma sinh_sub_le_cube {y : ℝ} (hy0 : 0 < y) (hy2 : y ≤ 2) : Real.sinh y - y ≤ y ^ 3 / 4 := by
  have h := norm_sinhT_le (w := (y : ℂ)) (by simpa [Complex.norm_real, abs_of_pos hy0] using hy2)
  rw [sinhT_ofReal hy0.ne', Complex.norm_real, Real.norm_eq_abs] at h
  have h2 := sinh_two_lt
  have hpos : 0 < y ^ 3 := by positivity
  have hq : (Real.sinh y - y) / y ^ 3 ≤ 1 / 4 := by
    refine (le_abs_self _).trans (h.trans ?_)
    linarith
  rw [div_le_iff₀ hpos] at hq
  linarith

lemma exp_div_three_le_sinh {y : ℝ} (hy : 1 ≤ y) : Real.exp y / 3 ≤ Real.sinh y := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-y) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have h3 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp y := Real.exp_pos y
  nlinarith

end FormalResearch.SignUncertainty.CtOuter
