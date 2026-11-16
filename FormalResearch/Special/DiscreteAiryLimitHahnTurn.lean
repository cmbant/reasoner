module

public import FormalResearch.Racah.P3JacobiComparison
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Hahn/Racah closed forms as a simple turn (`u`, `A`) for the discrete-to-Airy limit

Part of the wiring module `DiscreteAiryLimit*` (instance layer).  P3 (`A:1313-1322`) writes the Hahn and centred Racah
chains in the natural gauge `A_{k+1}Y_{k+1} + A_k Y_{k-1} = τ(x - B_k)Y_k` with the closed forms
`A_k = ½ r_k ẽ((kh)²)` (`rr`, `etilde` of `Racah/P3JacobiComparison`) and `B_k = hrB`.  The smooth coefficient data of
`DiscreteAiryLimit` for these are

* `A(q) = ½ ẽ(q²) = ½ √((1-Pq²)(1-Qq²))` (`P = σ₁⁻¹, Q = σ₂⁻¹`; `A_k = A(q_k - h/2)` up to `O(h²)`, `q_k = (k+½)h`),
* `u(q) = τ(x - β₀q²)/ẽ(q²)`, so that `2A(q)u(q) = τ(x - β₀q²)` (`B_k = β₀q_k² + O(h²)`), `β₀ = √(PQ)`.

This file proves, from the **simple-turn hypotheses of P3** (`Φ(q_*²) = 0` with `Φ(σ) = τ(x-β₀σ) - ẽ(σ)`, `1 - τx > 0`,
`τ² = 1`, `q_* > 0`, interior of the domain `ẽ(q_*²) > 0`):

* `hrA_contDiffAt`, `hrU_contDiffAt`: `A`, `u` are `C^n` at `q_*` (indeed analytic), `A(q_*) > 0`;
* `hrU_turn`: `u(q_*) = 1`;
* **`hrU_deriv_pos`**: `u'(q_*) > 0`, by the algebraic identity
  `σ(Pβ + Qα - 2τβ₀ s) = α + β - 2s² - 2τβ₀σ s ≥ 2s(1 - s - τβ₀σ) = 2s(1-τx) > 0` (`α = 1-Pσ`, `β = 1-Qσ`,
  `s = √(αβ) = ẽ`, AM-GM `α + β ≥ 2s`, and `τx = s + τβ₀σ` at the turn).  This is the paper's `Φ'(σ_*) > 0`
  (`eq:forbidden-slope`), obtained here directly from `1 - τx > 0`.

Proved.
-/

@[expose] public section

open FormalResearch.Racah.P3

namespace FormalResearch.Special

/-- `A(q) = ½ ẽ(q²)`. -/
noncomputable def hrA1 (P Q : ℝ) (q : ℝ) : ℝ := 1 / 2 * etilde P Q (q ^ 2)

/-- `u(q) = τ(x - β₀q²)/ẽ(q²)`, `β₀ = √(PQ)`. -/
noncomputable def hrU (P Q τ x : ℝ) (q : ℝ) : ℝ :=
  τ * (x - Real.sqrt (P * Q) * q ^ 2) / etilde P Q (q ^ 2)

lemma hrF_contDiffAt (P Q : ℝ) (n : WithTop ℕ∞) (q : ℝ) :
    ContDiffAt ℝ n (fun y : ℝ => (1 - P * y ^ 2) * (1 - Q * y ^ 2)) q := by
  fun_prop

lemma etilde_contDiffAt {P Q : ℝ} (n : WithTop ℕ∞) {qs : ℝ} (hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2)) :
    ContDiffAt ℝ n (fun y : ℝ => etilde P Q (y ^ 2)) qs := by
  unfold etilde
  exact (hrF_contDiffAt P Q n qs).sqrt hint.ne'

lemma hrA_contDiffAt {P Q : ℝ} (n : WithTop ℕ∞) {qs : ℝ}
    (hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2)) : ContDiffAt ℝ n (hrA1 P Q) qs :=
  contDiffAt_const.mul (etilde_contDiffAt n hint)

lemma hrA_pos {P Q : ℝ} {qs : ℝ} (hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2)) : 0 < hrA1 P Q qs := by
  unfold hrA1 etilde
  have := Real.sqrt_pos.2 hint
  positivity

lemma hrU_contDiffAt {P Q : ℝ} (τ x : ℝ) (n : WithTop ℕ∞) {qs : ℝ}
    (hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2)) : ContDiffAt ℝ n (hrU P Q τ x) qs := by
  unfold hrU
  have h1 : ContDiffAt ℝ n (fun y : ℝ => τ * (x - Real.sqrt (P * Q) * y ^ 2)) qs := by fun_prop
  refine h1.div (etilde_contDiffAt n hint) ?_
  unfold etilde
  exact (Real.sqrt_pos.2 hint).ne'

/-- `u(q_*) = 1` at a turn `Φ(q_*²) = 0`. -/
lemma hrU_turn {P Q τ x qs : ℝ} (hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2))
    (hturn : Phi P Q τ x (qs ^ 2) = 0) : hrU P Q τ x qs = 1 := by
  have hs : 0 < etilde P Q (qs ^ 2) := by unfold etilde; exact Real.sqrt_pos.2 hint
  unfold hrU
  unfold Phi at hturn
  rw [div_eq_one_iff_eq hs.ne']
  linarith

/-- The algebra behind `u'(q_*) > 0` (see the module docstring); `σ = q²`, no sign condition on `P, Q, β₀, τ`. -/
lemma hr_alg {P Q β₀ τ x q s α β : ℝ} (hq : 0 < q) (hα : α = 1 - P * q ^ 2) (hβ : β = 1 - Q * q ^ 2)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hs0 : 0 < s) (hss : s ^ 2 = α * β)
    (hN : τ * (x - β₀ * q ^ 2) = s) (hκ : 0 < 1 - τ * x) :
    0 < (-(2 * τ * β₀ * q) * s - s * ((-(2 * P * q) * β + α * (-(2 * Q * q))) / (2 * s))) / s ^ 2 := by
  have hσ : 0 < q ^ 2 := by positivity
  have hab : 2 * s ≤ α + β := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg (α - β)]
  have hPσ : q ^ 2 * P = 1 - α := by rw [hα]; ring
  have hQσ : q ^ 2 * Q = 1 - β := by rw [hβ]; ring
  have hx : τ * x = s + τ * β₀ * q ^ 2 := by linarith
  have key : 0 < q ^ 2 * (P * β + Q * α - 2 * τ * β₀ * s) := by
    have e : q ^ 2 * (P * β + Q * α - 2 * τ * β₀ * s) =
        α + β - 2 * s ^ 2 - 2 * s * (τ * β₀ * q ^ 2) := by
      have e1 : q ^ 2 * (P * β + Q * α) = (q ^ 2 * P) * β + (q ^ 2 * Q) * α := by ring
      have e2 : q ^ 2 * (2 * τ * β₀ * s) = 2 * s * (τ * β₀ * q ^ 2) := by ring
      calc q ^ 2 * (P * β + Q * α - 2 * τ * β₀ * s)
          = q ^ 2 * (P * β + Q * α) - q ^ 2 * (2 * τ * β₀ * s) := by ring
        _ = (1 - α) * β + (1 - β) * α - 2 * s * (τ * β₀ * q ^ 2) := by rw [e1, e2, hPσ, hQσ]
        _ = _ := by rw [hss]; ring
    rw [e]
    have : 0 < 2 * s * (1 - τ * x) := by positivity
    nlinarith [mul_pos hs0 hκ]
  have hpos : 0 < P * β + Q * α - 2 * τ * β₀ * s := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hσ.le (neg_nonneg.2 h)]
  have e : -(2 * τ * β₀ * q) * s - s * ((-(2 * P * q) * β + α * (-(2 * Q * q))) / (2 * s)) =
      q * (P * β + Q * α - 2 * τ * β₀ * s) := by
    field_simp
    ring
  rw [e]
  positivity

/-- **`u'(q_*) > 0`** at a simple turn (see the module docstring). -/
theorem hrU_deriv_pos {P Q : ℝ} {τ x qs : ℝ} (hqs : 0 < qs) (hκ : 0 < 1 - τ * x)
    (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0) :
    0 < deriv (hrU P Q τ x) qs := by
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  have hs0 : 0 < Real.sqrt ((1 - P * qs ^ 2) * (1 - Q * qs ^ 2)) := Real.sqrt_pos.2 hint
  have hF : HasDerivAt (fun y : ℝ => (1 - P * y ^ 2) * (1 - Q * y ^ 2))
      (-(2 * P * qs) * (1 - Q * qs ^ 2) + (1 - P * qs ^ 2) * (-(2 * Q * qs))) qs := by
    have h1 : HasDerivAt (fun y : ℝ => 1 - P * y ^ 2) (-(2 * P * qs)) qs := by
      have := ((hasDerivAt_pow 2 qs).const_mul P).const_sub 1
      convert this using 1; push_cast; ring
    have h2 : HasDerivAt (fun y : ℝ => 1 - Q * y ^ 2) (-(2 * Q * qs)) qs := by
      have := ((hasDerivAt_pow 2 qs).const_mul Q).const_sub 1
      convert this using 1; push_cast; ring
    exact h1.mul h2
  have hD : HasDerivAt (fun y : ℝ => etilde P Q (y ^ 2))
      ((-(2 * P * qs) * (1 - Q * qs ^ 2) + (1 - P * qs ^ 2) * (-(2 * Q * qs))) /
        (2 * Real.sqrt ((1 - P * qs ^ 2) * (1 - Q * qs ^ 2)))) qs := by
    unfold etilde
    exact hF.sqrt hint.ne'
  have hN : HasDerivAt (fun y : ℝ => τ * (x - Real.sqrt (P * Q) * y ^ 2))
      (-(2 * τ * Real.sqrt (P * Q) * qs)) qs := by
    have := (((hasDerivAt_pow 2 qs).const_mul (Real.sqrt (P * Q))).const_sub x).const_mul τ
    convert this using 1; push_cast; ring
  have hD0 : etilde P Q (qs ^ 2) = Real.sqrt ((1 - P * qs ^ 2) * (1 - Q * qs ^ 2)) := rfl
  have hu := hN.fun_div hD (by rw [hD0]; exact hs0.ne')
  have hN0 : τ * (x - Real.sqrt (P * Q) * qs ^ 2) = Real.sqrt ((1 - P * qs ^ 2) * (1 - Q * qs ^ 2)) := by
    unfold Phi at hturn; exact sub_eq_zero.1 hturn
  have hder : deriv (hrU P Q τ x) qs =
      (-(2 * τ * Real.sqrt (P * Q) * qs) * Real.sqrt ((1 - P * qs ^ 2) * (1 - Q * qs ^ 2)) -
        τ * (x - Real.sqrt (P * Q) * qs ^ 2) *
        ((-(2 * P * qs) * (1 - Q * qs ^ 2) + (1 - P * qs ^ 2) * (-(2 * Q * qs))) /
          (2 * Real.sqrt ((1 - P * qs ^ 2) * (1 - Q * qs ^ 2))))) /
        Real.sqrt ((1 - P * qs ^ 2) * (1 - Q * qs ^ 2)) ^ 2 := by
    have := hu.deriv
    unfold hrU
    rw [this, hD0]
  rw [hder, hN0]
  exact hr_alg hqs rfl rfl hα hβ hs0 (Real.sq_sqrt hint.le) hN0 hκ

/-- info: 'FormalResearch.Special.hrU_deriv_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hrU_deriv_pos

end FormalResearch.Special
