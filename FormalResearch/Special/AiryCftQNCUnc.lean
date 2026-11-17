module

public import FormalResearch.Special.AiryCftQNCSample
public import FormalResearch.Special.AiryCftQNCQuad

/-!
# Theorem Q (4) for `N = P Ai + Q Ai'` and the Clark functions: unconditional `HasSum`

With the sampling bound `airyNC_sampling_sum` (`AiryCftQNCSample`) the series over the zeros of `N = P Ai + Q Ai'` (`Q ≠ 0`), resp. of
`ψ_α = cos α Ai - sin α Ai'` (`sin α ≠ 0`), converges absolutely for every entire `f` with `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (any real `ν`, complex-valued `f`)
and `f ∈ L¹(ℝ)`, so the `Summable` hypotheses of `airyNC_hasSum` and `airyClark_hasSum` are dropped:

* `airyNC_summable`, `airyNC_hasSum_unc`: `∫_ℝ f = Σ_{N(z)=0} f(z) D(z)/N'(z)²`;
* `airyClark_summable`, `airyClark_hasSum_unc`: `∫_ℝ f = Σ_{ψ_α(z)=0} f(z)/K(z,z)`, `K = Ai'² - z Ai²`.

**Proved.**
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- **Absolute summability** of the quadrature series over the zeros of `N = P Ai + Q Ai'`. -/
theorem airyNC_summable (P Q : ℝ) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    Summable (fun z : {z : ℂ // airyNC P Q z = 0} => ‖f z * (airyDC P Q z / airyNC' P Q z ^ 2)‖) := by
  obtain ⟨B, -, hB⟩ := airyNC_sampling_sum P Q hQ
  exact summable_of_sum_le (fun z => norm_nonneg _) (fun S => hB hf hfi hC hb S)

/-- **Theorem Q (4) for `N = P Ai + Q Ai'`, unconditional.** -/
theorem airyNC_hasSum_unc (P Q : ℝ) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    HasSum (fun z : {z : ℂ // airyNC P Q z = 0} => f z * (airyDC P Q z / airyNC' P Q z ^ 2))
      (∫ x : ℝ, f (x : ℂ)) :=
  airyNC_hasSum P Q hQ hf hfi hC hb (airyNC_summable P Q hQ hf hfi hC hb).of_norm

/-- The Clark weights `1/K(z,z)` and the weights `D/N'²` of `N = cos α Ai - sin α Ai'` agree on the zeros; the zero subtypes
are in bijection. -/
theorem airyClark_summable (α : ℝ) (hα : Real.sin α ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    Summable (fun z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} =>
        f z / (deriv airyAiC z ^ 2 - z * airyAiC z ^ 2)) := by
  have hQ : -Real.sin α ≠ 0 := neg_ne_zero.mpr hα
  have hz : ∀ z : ℂ, airyNC (Real.cos α) (-Real.sin α) z = 0 ↔
      (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0 := by
    intro z
    unfold airyNC
    push_cast
    constructor <;> intro h <;> linear_combination h
  let e : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} ≃
      {z : ℂ // airyNC (Real.cos α) (-Real.sin α) z = 0} :=
    Equiv.subtypeEquivRight (fun z => (hz z).symm)
  have hw : ∀ z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0},
      f z / (deriv airyAiC z ^ 2 - z * airyAiC z ^ 2) =
        (fun w : {z : ℂ // airyNC (Real.cos α) (-Real.sin α) z = 0} =>
          f w * (airyDC (Real.cos α) (-Real.sin α) w / airyNC' (Real.cos α) (-Real.sin α) w ^ 2)) (e z) := by
    intro z
    have hz0 := (hz z.1).mpr z.2
    simp only [e, Equiv.subtypeEquivRight_apply_coe]
    rw [airyNC_weight_eq_inv_K _ _ hQ hz0]
    field_simp
  have hs := (airyNC_summable (Real.cos α) (-Real.sin α) hQ hf hfi hC hb).of_norm
  rw [← e.summable_iff] at hs
  exact hs.congr fun z => (hw z).symm

/-- **Theorem Q (4) for the Clark functions, unconditional.** -/
theorem airyClark_hasSum_unc (α : ℝ) (hα : Real.sin α ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    HasSum (fun z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} =>
        f z / (deriv airyAiC z ^ 2 - z * airyAiC z ^ 2)) (∫ x : ℝ, f (x : ℂ)) :=
  airyClark_hasSum α hα hf hfi hC hb (airyClark_summable α hα hf hfi hC hb)

/-- info: 'FormalResearch.Special.airyNC_hasSum_unc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_hasSum_unc

/-- info: 'FormalResearch.Special.airyClark_hasSum_unc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyClark_hasSum_unc

end FormalResearch.Special
