module

public import FormalResearch.SignUncertainty.RadialLimitXi

/-!
# Contour independence of `∫ limInt W u v s dv` (`lem:radial-compactness`, Step 4)

For `W` holomorphic on `Re w > 0` and bounded, `G(u) = ∫ limInt W u v s dv` is constant for `u > 0`:
`G'(u) = ∫ g'(u+iv) dv = -i [g(u+iv)]_{v=-∞}^{∞} = 0` by Gaussian decay (`G_const`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma gauss_lin_integrable {c d : ℝ} (hc : 0 < c) : Integrable fun v : ℝ => Real.exp (-c * v ^ 2 + d * v) := by
  have h := (integrable_exp_neg_mul_sq hc).comp_sub_right (d / (2 * c))
  have := h.const_mul (Real.exp (d ^ 2 / (4 * c)))
  refine this.congr (Eventually.of_forall fun v => ?_)
  simp only [Function.comp]
  rw [← Real.exp_add]; congr 1; field_simp; ring

lemma gauss_poly_bound {c d : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, (1 + v ^ 2) * Real.exp (-c * v ^ 2 + d * |v|) ≤ C * Real.exp (-(c / 2) * v ^ 2) := by
  refine ⟨(1 + 4 / c) * Real.exp (d ^ 2 / c), by positivity, fun v => ?_⟩
  have h1 : d * |v| ≤ c / 4 * v ^ 2 + d ^ 2 / c := by
    have : |d| * |v| ≤ c / 4 * v ^ 2 + d ^ 2 / c := by
      have h := sq_nonneg (c * |v| / 2 - |d|)
      have : c / 4 * v ^ 2 + d ^ 2 / c - |d| * |v| = (c * |v| / 2 - |d|) ^ 2 / c := by
        field_simp; rw [← sq_abs v, ← sq_abs d]; ring
      have h2 : 0 ≤ (c * |v| / 2 - |d|) ^ 2 / c := by positivity
      linarith
    nlinarith [le_abs_self d, abs_nonneg v]
  have h2 : 1 + v ^ 2 ≤ (1 + 4 / c) * Real.exp (c / 4 * v ^ 2) := by
    have := Real.add_one_le_exp (c / 4 * v ^ 2)
    have hc4 : 0 < 4 / c := by positivity
    have : (1 + 4 / c) * (c / 4 * v ^ 2 + 1) ≥ 1 + v ^ 2 := by
      have : (1 + 4 / c) * (c / 4 * v ^ 2 + 1) = 1 + v ^ 2 + c / 4 * v ^ 2 + 4 / c := by field_simp; ring
      rw [this]; nlinarith [sq_nonneg v, hc, hc4]
    calc 1 + v ^ 2 ≤ (1 + 4 / c) * (c / 4 * v ^ 2 + 1) := this
      _ ≤ (1 + 4 / c) * Real.exp (c / 4 * v ^ 2) := by gcongr
  have h3 : Real.exp (-c * v ^ 2 + d * |v|) ≤ Real.exp (d ^ 2 / c) * Real.exp (-(3 * c / 4) * v ^ 2) := by
    rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_; nlinarith
  calc (1 + v ^ 2) * Real.exp (-c * v ^ 2 + d * |v|)
      ≤ ((1 + 4 / c) * Real.exp (c / 4 * v ^ 2)) * (Real.exp (d ^ 2 / c) * Real.exp (-(3 * c / 4) * v ^ 2)) := by
        gcongr
    _ = (1 + 4 / c) * Real.exp (d ^ 2 / c) * (Real.exp (c / 4 * v ^ 2) * Real.exp (-(3 * c / 4) * v ^ 2)) := by
        ring
    _ = (1 + 4 / c) * Real.exp (d ^ 2 / c) * Real.exp (-(c / 2) * v ^ 2) := by
        rw [← Real.exp_add]; congr 2; ring

/-- info: 'FormalResearch.SignUncertainty.gauss_lin_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gauss_lin_integrable

/-- info: 'FormalResearch.SignUncertainty.gauss_poly_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gauss_poly_bound

end FormalResearch.SignUncertainty
