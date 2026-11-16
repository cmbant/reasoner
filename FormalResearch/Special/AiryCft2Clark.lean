module

public import FormalResearch.Special.AiryCft2ComboQuadrature

/-!
# The Clark-Airy summation in the form `∫ f = Σ f(z_n)/K(z_n, z_n)`

Specialisation of `airyNC_quadrature` (`AiryCft2ComboQuadrature`) to the Clark functions
`ψ_α = cos α Ai - sin α Ai'` (`P = cos α`, `Q = -sin α`, `sin α ≠ 0`), with the Airy reproducing-kernel weights
`K(z, z) = Ai'(z)² - z Ai(z)²` (CFT/PR240 `GENERAL_THEOREMS.md` Theorem 1.1; `STRUCTURAL_LINKS.md` §2.1):

* `airyNC_weight_eq_inv_K`: at a zero `z` of `N = P Ai + Q Ai'` (`Q ≠ 0`), `D(z)/N'(z)² = 1/K(z,z)` (`K = Ai² D/Q²` there, `N' = -Ai D/Q`);
* `airyNC_K_pos`: `K(x,x) > 0` at a real zero `x` of `N` (so every weight is positive);
* `airyClark_quadrature`: for `sin α ≠ 0`, `f` entire with `‖f(u)‖ ≤ C (1+|u|)^ν e(u)`, `ν < -1`:
  `∫_ℝ f = Σ_{ψ_α(z) = 0} f(z)/K(z,z)`, absolutely convergent (HasSum over the subtype of zeros of `ψ_α`; the zeros are
  real and simple, `airyNC_zero_im`, `airyNC_zero_weight_pos`).

Class: proved (axiom-checked) for `ν < -1` (Corollary-D1 range); the full range `ν ≤ 1/2` of Theorem 1.1 (`f ∈ 𝒢`) needs the Hardy-space
bound `∮ |f|/e → 0` (Theorem Q(1)), not formalised.  Not formalised either: the labelling `z_1(α) > a_1`, `z_n(α) ∈ (a_n, a_{n-1})` and the
dependence of the nodes on `α`.

Numerical check (mpmath, 20 digits; evidence only): `α = 0.4`, `f(u) = ∫_0^1 τ⁴(1-τ)⁴ Ai(2^{2/3}(u+τ)) dτ` (`∫ f = 2^{-2/3} 576/9! = 0.00099994`):
partial sums over the `50, 100, 200, 400` largest zeros of `ψ_α`: `0.000716, 0.000909, 0.000919, 0.000965` (slow oscillating approach, tail `~ n^{-8/9}`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- At a zero `z` of `N` (`Q ≠ 0`): `D(z)/N'(z)² = 1/K(z,z)`, `K = Ai'² - z Ai²`. -/
theorem airyNC_weight_eq_inv_K (P Q : ℝ) (hQ : Q ≠ 0) {z : ℂ} (h : airyNC P Q z = 0) :
    airyDC P Q z / airyNC' P Q z ^ 2 = 1 / (deriv airyAiC z ^ 2 - z * airyAiC z ^ 2) := by
  have hA : airyAiC z ≠ 0 := fun h0 => airyNC_ne_zero_of_airy_zero P Q hQ h0 h
  have him := airyNC_zero_im P Q hQ h
  have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hD : (P : ℂ) ^ 2 - z * (Q : ℂ) ^ 2 ≠ 0 := by
    have h0 := h
    rw [e] at h0
    have := (airyNC_zero_weight_pos P Q hQ h0).1
    have e2 : (P : ℂ) ^ 2 - z * (Q : ℂ) ^ 2 = (((P ^ 2 - z.re * Q ^ 2 : ℝ)) : ℂ) := by
      push_cast
      rw [← e]
    rw [e2]
    exact_mod_cast this.ne'
  have hQ' : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  have hder : deriv airyAiC z = -((P : ℂ) * airyAiC z / (Q : ℂ)) := by
    unfold airyNC at h
    field_simp
    linear_combination h
  unfold airyDC airyNC'
  rw [hder]
  have hK : (-((P : ℂ) * airyAiC z / (Q : ℂ))) ^ 2 - z * airyAiC z ^ 2 =
      airyAiC z ^ 2 * ((P : ℂ) ^ 2 - z * (Q : ℂ) ^ 2) / (Q : ℂ) ^ 2 := by
    field_simp
  have hN' : (P : ℂ) * (-((P : ℂ) * airyAiC z / (Q : ℂ))) + (Q : ℂ) * (z * airyAiC z) =
      -(airyAiC z * ((P : ℂ) ^ 2 - z * (Q : ℂ) ^ 2) / (Q : ℂ)) := by
    field_simp
    ring
  rw [hK, hN']
  field_simp

/-- info: 'FormalResearch.Special.airyNC_weight_eq_inv_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_weight_eq_inv_K

/-- `K(x,x) = Ai'(x)² - x Ai(x)² > 0` at a real zero `x` of `N` (`Q ≠ 0`). -/
theorem airyNC_K_pos (P Q : ℝ) (hQ : Q ≠ 0) {x : ℝ} (h : airyNC P Q (x : ℂ) = 0) :
    0 < airyAi' x ^ 2 - x * airyAi x ^ 2 := by
  have hD := (airyNC_zero_weight_pos P Q hQ h).1
  have h' := h
  rw [airyNC_ofReal, Complex.ofReal_eq_zero] at h'
  have hAx : airyAi x ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_add] at h'
    have : airyAi' x = 0 := by
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact absurd h1 hQ
      · exact h1
    exact airyAi_ne_zero_of_deriv_zero this h0
  have hm : airyAi' x = -(P / Q) * airyAi x := by
    field_simp; linarith
  have e : airyAi' x ^ 2 - x * airyAi x ^ 2 = airyAi x ^ 2 * (P ^ 2 - x * Q ^ 2) / Q ^ 2 := by
    rw [hm]; field_simp
  rw [e]
  have : 0 < airyAi x ^ 2 := by positivity
  positivity

/-- info: 'FormalResearch.Special.airyNC_K_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_K_pos

/-- **Clark-Airy summation** (`ν < -1`): for `sin α ≠ 0` and `f` entire with `‖f(u)‖ ≤ C (1+|u|)^ν e(u)`, `ν < -1`,
`∫_ℝ f = Σ_{cos α Ai(z) - sin α Ai'(z) = 0} f(z)/K(z,z)`, `K = Ai'² - z Ai²`. -/
theorem airyClark_quadrature (α : ℝ) (hα : Real.sin α ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C ν : ℝ}
    (hC : 0 ≤ C) (hν : ν < -1) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    HasSum (fun z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} =>
        f z / (deriv airyAiC z ^ 2 - z * airyAiC z ^ 2)) (∫ x : ℝ, f (x : ℂ)) := by
  have hQ : -Real.sin α ≠ 0 := neg_ne_zero.mpr hα
  have hz : ∀ z : ℂ, airyNC (Real.cos α) (-Real.sin α) z = 0 ↔
      (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0 := by
    intro z
    unfold airyNC
    push_cast
    constructor <;> intro h <;> linear_combination h
  have h := airyNC_quadrature (Real.cos α) (-Real.sin α) hQ hf hC hν hb
  let e : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} ≃
      {z : ℂ // airyNC (Real.cos α) (-Real.sin α) z = 0} :=
    Equiv.subtypeEquivRight (fun z => (hz z).symm)
  rw [← e.hasSum_iff] at h
  convert h using 2 with z
  have hz0 := (hz z.1).mpr z.2
  simp only [e, Equiv.subtypeEquivRight_apply_coe, Function.comp]
  rw [airyNC_weight_eq_inv_K _ _ hQ hz0]
  field_simp

/-- info: 'FormalResearch.Special.airyClark_quadrature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyClark_quadrature

end FormalResearch.Special
