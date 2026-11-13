module

public import FormalResearch.Special.JacobiBeta
public import FormalResearch.Special.JacobiOrth

/-!
# Jacobi polynomials: orthogonality and norms for real parameters

For real `α, β > -1` the Jacobi polynomials `jacobi α β n` (DLMF 18.5.7) are orthogonal on `[-1,1]`
for the weight `(1-x)^α (1+x)^β` with real powers (DLMF 18.2.1, 18.3.1), with the norm of DLMF 18.3,
table 18.3.1:

  `∫_{-1}^1 (1-x)^α (1+x)^β P_n^{(α,β)}(x)² dx
      = 2^(α+β+1) / (2n+α+β+1) · Γ(n+α+1) Γ(n+β+1) / (Γ(n+α+β+1) n!)`.

This extends `JacobiOrth.lean` (natural parameters) to real parameters.

## Main results

* `jacobi_orthogonal_real`: `∫ w P_m P_n = 0` for `m ≠ n` (Sturm–Liouville argument: the
  fundamental theorem of calculus on `[-1,1]` with `p(x) = (1-x)^(α+1) (1+x)^(β+1)`, which is
  continuous and vanishes at `±1`, using the Jacobi equation `jacobi_ode`);
* `jacobi_orthogonal_lowerDegree_real`: `P_n` is orthogonal to every polynomial of degree `< n`;
* `jacobi_norm_real_zero`: the case `n = 0`, the Beta integral `jacobi_beta_integral`;
* `jacobi_norm_real`: the norm for all `n`, written as in DLMF 18.3 (table 18.3.1); for `n = 0`
  and `α + β + 1 = 0` the closed form `0/0` is not defined, and the hypothesis excludes that case
  (`jacobi_norm_real_zero` covers it).

The norm is obtained from the normalised three-term recurrence (`jacobi_X_mul_succ`) as in
`JacobiOrth.lean`: `⟨x P_n, P_{n+1}⟩` is computed twice, giving `h_{n+1} = c_{n+1}/a_n · h_n`.
-/

@[expose] public section

namespace FormalResearch.Special

open Polynomial MeasureTheory intervalIntegral Set

/-- `jacobiW` times a polynomial is interval integrable on `[-1,1]`. -/
lemma jacobiW_poly_integrable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (r : ℝ[X]) :
    IntervalIntegrable (fun x => jacobiW α β x * r.eval x) volume (-1 : ℝ) 1 :=
  jacobiW_mul_intervalIntegrable hα hβ (Polynomial.continuous r).continuousOn

lemma continuous_one_sub_rpow {p : ℝ} (hp : 0 ≤ p) : Continuous (fun x : ℝ => (1 - x) ^ p) :=
  (Real.continuous_rpow_const hp).comp (continuous_const.sub continuous_id)

lemma continuous_one_add_rpow {p : ℝ} (hp : 0 ≤ p) : Continuous (fun x : ℝ => (1 + x) ^ p) :=
  (Real.continuous_rpow_const hp).comp (continuous_const.add continuous_id)

/-- Derivative of the Sturm–Liouville coefficient `p(x) = (1-x)^(α+1) (1+x)^(β+1)`:
`p' = w · ((β-α) - (α+β+2) x)` on `(-1,1)`. -/
lemma hasDerivAt_jacobiP (α β : ℝ) {x : ℝ} (hx1 : x < 1) (hx2 : -1 < x) :
    HasDerivAt (fun y : ℝ => (1 - y) ^ (α + 1) * (1 + y) ^ (β + 1))
      (jacobiW α β x * ((β - α) - (α + β + 2) * x)) x := by
  have h0 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have h0' : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_id x).const_add 1
  have n1 : (1 - x) ≠ 0 := by linarith
  have n2 : (1 + x) ≠ 0 := by linarith
  have h1 := h0.rpow_const (p := α + 1) (Or.inl n1)
  have h2 := h0'.rpow_const (p := β + 1) (Or.inl n2)
  convert h1.mul h2 using 1
  simp only [add_sub_cancel_right, jacobiW]
  rw [Real.rpow_add_one n1, Real.rpow_add_one n2]
  ring

/-- **Orthogonality of Jacobi polynomials** (DLMF 18.2.1, 18.3.1) for real `α, β > -1`. -/
theorem jacobi_orthogonal_real {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (m n : ℕ) (h : m ≠ n) :
    ∫ x in (-1 : ℝ)..1, (1 - x) ^ α * (1 + x) ^ β * (jacobi α β m).eval x *
      (jacobi α β n).eval x = 0 := by
  set Pm := jacobi α β m with hPm
  set Pn := jacobi α β n with hPn
  set W : ℝ[X] := derivative Pm * Pn - Pm * derivative Pn with hW
  set lam : ℝ := (n : ℝ) * (n + α + β + 1) - m * (m + α + β + 1) with hlam
  set F : ℝ → ℝ := fun x => (1 - x) ^ (α + 1) * (1 + x) ^ (β + 1) * W.eval x with hF
  have hderiv : ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt F (lam * (jacobiW α β x * (Pm.eval x * Pn.eval x))) x := by
    intro x hx
    have hp := hasDerivAt_jacobiP α β hx.2 hx.1
    have hWd := Polynomial.hasDerivAt W x
    convert hp.mul hWd using 1
    have n1 : (1 - x) ≠ 0 := by linarith [hx.2]
    have n2 : (1 + x) ≠ 0 := by linarith [hx.1]
    have om := congrArg (eval x) (jacobi_ode α β m)
    have on := congrArg (eval x) (jacobi_ode α β n)
    simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_C, eval_X, eval_one, eval_zero] at om on
    simp only [hW, derivative_mul, derivative_sub, eval_add, eval_mul, eval_sub, hlam, jacobiW]
    rw [Real.rpow_add_one n1, Real.rpow_add_one n2]
    rw [← hPm] at om
    rw [← hPn] at on
    linear_combination ((1 - x) ^ α * (1 + x) ^ β * Pm.eval x) * on -
      ((1 - x) ^ α * (1 + x) ^ β * Pn.eval x) * om
  have hcont : ContinuousOn F (Icc (-1 : ℝ) 1) := by
    refine Continuous.continuousOn ?_
    exact ((continuous_one_sub_rpow (by linarith)).mul (continuous_one_add_rpow (by linarith))).mul
      (Polynomial.continuous W)
  have hint : IntervalIntegrable (fun x => lam * (jacobiW α β x * (Pm.eval x * Pn.eval x)))
      volume (-1 : ℝ) 1 := by
    have := (jacobiW_poly_integrable hα hβ (Pm * Pn)).const_mul lam
    simpa only [eval_mul] using this
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint
  have h1 : F 1 = 0 := by
    simp only [hF, sub_self]
    rw [Real.zero_rpow (by linarith)]; simp
  have h2 : F (-1) = 0 := by
    simp only [hF]
    rw [show (1 : ℝ) + -1 = 0 by norm_num, Real.zero_rpow (by linarith)]; simp
  rw [h1, h2, sub_zero, intervalIntegral.integral_const_mul] at hftc
  have hne : lam ≠ 0 := by
    have hmn : (n : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h.symm)
    have hpos : (0 : ℝ) < n + m + α + β + 1 := by
      have : (1 : ℝ) ≤ n + m := by
        have : 1 ≤ n + m := by omega
        exact_mod_cast this
      linarith
    have : lam = ((n : ℝ) - m) * (n + m + α + β + 1) := by rw [hlam]; ring
    rw [this]
    exact mul_ne_zero hmn hpos.ne'
  have h3 : ∫ x in (-1 : ℝ)..1, jacobiW α β x * (Pm.eval x * Pn.eval x) = 0 := by
    rcases mul_eq_zero.mp hftc with h0 | h0
    · exact absurd h0 hne
    · exact h0
  rw [← h3]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [jacobiW]; ring

/-! ### The inner product and the norm -/

/-- The weighted inner product `∫_{-1}^1 (1-x)^α (1+x)^β f g` of two polynomials. -/
noncomputable def jacIPr (α β : ℝ) (f g : ℝ[X]) : ℝ :=
  ∫ x in (-1 : ℝ)..1, jacobiW α β x * f.eval x * g.eval x

lemma jacIPr_integrable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (f g : ℝ[X]) :
    IntervalIntegrable (fun x => jacobiW α β x * f.eval x * g.eval x) volume (-1 : ℝ) 1 := by
  have := jacobiW_poly_integrable hα hβ (f * g)
  simpa only [eval_mul, mul_assoc] using this

lemma jacIPr_add_left {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (f₁ f₂ g : ℝ[X]) :
    jacIPr α β (f₁ + f₂) g = jacIPr α β f₁ g + jacIPr α β f₂ g := by
  unfold jacIPr
  rw [← intervalIntegral.integral_add (jacIPr_integrable hα hβ f₁ g)
    (jacIPr_integrable hα hβ f₂ g)]
  congr 1; funext x; simp only [eval_add]; ring

lemma jacIPr_C_mul_left (α β : ℝ) (c : ℝ) (f g : ℝ[X]) :
    jacIPr α β (C c * f) g = c * jacIPr α β f g := by
  unfold jacIPr
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext x; simp only [eval_mul, eval_C]; ring

lemma jacIPr_X_mul (α β : ℝ) (f g : ℝ[X]) : jacIPr α β (X * f) g = jacIPr α β f (X * g) := by
  unfold jacIPr
  congr 1; funext x; simp only [eval_mul, eval_X]; ring

lemma jacIPr_comm (α β : ℝ) (f g : ℝ[X]) : jacIPr α β f g = jacIPr α β g f := by
  unfold jacIPr
  congr 1; funext x; ring

lemma jacIPr_orth {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (m n : ℕ) (h : m ≠ n) :
    jacIPr α β (jacobi α β m) (jacobi α β n) = 0 :=
  jacobi_orthogonal_real hα hβ m n h

/-- `⟨x P_{n+1}, P_n⟩ = c_n h_n` from the normalised recurrence. -/
lemma jacIPr_X_succ_self {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    jacIPr α β (X * jacobi α β (n + 1)) (jacobi α β n)
      = jacC α β n * jacIPr α β (jacobi α β n) (jacobi α β n) := by
  have hs : (0 : ℝ) < α + β + 2 := by linarith
  rw [jacobi_X_mul_succ _ _ hs n, jacIPr_add_left hα hβ, jacIPr_add_left hα hβ,
    jacIPr_C_mul_left, jacIPr_C_mul_left, jacIPr_C_mul_left, jacIPr_orth hα hβ (n + 2) n (by omega),
    jacIPr_orth hα hβ (n + 1) n (by omega)]
  ring

/-- `a_0 h_1 = c_0 h_0`. -/
lemma jacIPr_step_zero {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    jacA0 α β * jacIPr α β (jacobi α β 1) (jacobi α β 1)
      = jacC α β 0 * jacIPr α β (jacobi α β 0) (jacobi α β 0) := by
  have hs : (0 : ℝ) < α + β + 2 := by linarith
  calc jacA0 α β * jacIPr α β (jacobi α β 1) (jacobi α β 1)
      = jacIPr α β (X * jacobi α β 0) (jacobi α β 1) := by
        rw [jacobi_X_mul_zero _ _ hs, jacIPr_add_left hα hβ, jacIPr_C_mul_left,
          jacIPr_C_mul_left, jacIPr_orth hα hβ 0 1 (by omega)]
        ring
    _ = jacIPr α β (jacobi α β 1) (X * jacobi α β 0) := by rw [jacIPr_comm]
    _ = jacIPr α β (X * jacobi α β 1) (jacobi α β 0) := (jacIPr_X_mul α β _ _).symm
    _ = _ := jacIPr_X_succ_self hα hβ 0

/-- `a_k h_{k+2} = c_{k+1} h_{k+1}`. -/
lemma jacIPr_step_succ {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (k : ℕ) :
    jacA α β k * jacIPr α β (jacobi α β (k + 2)) (jacobi α β (k + 2))
      = jacC α β (k + 1) * jacIPr α β (jacobi α β (k + 1)) (jacobi α β (k + 1)) := by
  have hs : (0 : ℝ) < α + β + 2 := by linarith
  calc jacA α β k * jacIPr α β (jacobi α β (k + 2)) (jacobi α β (k + 2))
      = jacIPr α β (X * jacobi α β (k + 1)) (jacobi α β (k + 2)) := by
        rw [jacobi_X_mul_succ _ _ hs k, jacIPr_add_left hα hβ, jacIPr_add_left hα hβ,
          jacIPr_C_mul_left, jacIPr_C_mul_left, jacIPr_C_mul_left, jacIPr_orth hα hβ k (k + 2) (by omega),
          jacIPr_orth hα hβ (k + 1) (k + 2) (by omega)]
        ring
    _ = jacIPr α β (jacobi α β (k + 1)) (X * jacobi α β (k + 2)) := jacIPr_X_mul α β _ _
    _ = jacIPr α β (X * jacobi α β (k + 2)) (jacobi α β (k + 1)) := jacIPr_comm α β _ _
    _ = _ := jacIPr_X_succ_self hα hβ (k + 1)

/-- The squared norm `h_n` of `jacobi α β n` as a closed form (DLMF 18.3, table 18.3.1); it is
meaningful for `n ≥ 1` (and for `n = 0` when `α + β + 1 ≠ 0`). -/
noncomputable def jacNormR (α β : ℝ) (n : ℕ) : ℝ :=
  2 ^ (α + β + 1) / (2 * (n : ℝ) + α + β + 1) *
    (Real.Gamma ((n : ℝ) + (α + 1)) * Real.Gamma ((n : ℝ) + (β + 1))) /
    (Real.Gamma ((n : ℝ) + (α + β + 1)) * (n.factorial : ℝ))

/-- `Γ(j + 1 + c) = (j + c) Γ(j + c)`. -/
lemma gam_succ (c : ℝ) (j : ℕ) (h : 0 < (j : ℝ) + c) :
    Real.Gamma (((j + 1 : ℕ) : ℝ) + c) = ((j : ℝ) + c) * Real.Gamma ((j : ℝ) + c) := by
  rw [show ((j + 1 : ℕ) : ℝ) + c = ((j : ℝ) + c) + 1 by push_cast; ring]
  exact Real.Gamma_add_one h.ne'

lemma jacNormR_step_zero {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    jacA0 α β * jacNormR α β 1
      = jacC α β 0 * (2 ^ (α + β + 1) * (Real.Gamma (α + 1) * Real.Gamma (β + 1)) /
          Real.Gamma (α + β + 2)) := by
  have hs : (0 : ℝ) < α + β + 2 := by linarith
  have ga := gam_succ (α + 1) 0 (by simp; linarith)
  have gb := gam_succ (β + 1) 0 (by simp; linarith)
  have e : (((0 + 1 : ℕ) : ℝ) + (α + β + 1)) = α + β + 2 := by push_cast; ring
  have hG : 0 < Real.Gamma (α + β + 2) := Real.Gamma_pos_of_pos hs
  have hA : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hB : 0 < Real.Gamma (β + 1) := Real.Gamma_pos_of_pos (by linarith)
  unfold jacNormR jacA0 jacC
  simp only [zero_add, Nat.cast_zero, Nat.cast_one, Nat.factorial_one, mul_zero] at ga gb ⊢
  rw [show (1 : ℝ) + (α + 1) = α + 1 + 1 by ring, show (1 : ℝ) + (β + 1) = β + 1 + 1 by ring,
    show (1 : ℝ) + (α + β + 1) = α + β + 2 by ring] at *
  rw [ga, gb, show (2 * 1 + α + β + 1 : ℝ) = α + β + 3 by ring]
  have h1 : (α + β + 2) ≠ 0 := hs.ne'
  have h2 : (α + β + 3) ≠ 0 := by intro h; linarith
  field_simp

lemma jacNormR_step_succ {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (k : ℕ) :
    jacA α β k * jacNormR α β (k + 2) = jacC α β (k + 1) * jacNormR α β (k + 1) := by
  have hs : (0 : ℝ) < α + β + 2 := by linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have p1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + (α + 1) := by push_cast; linarith
  have p2 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + (β + 1) := by push_cast; linarith
  have p3 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + (α + β + 1) := by push_cast; linarith
  have g1 : Real.Gamma (((k + 2 : ℕ) : ℝ) + (α + 1)) =
      (((k + 1 : ℕ) : ℝ) + (α + 1)) * Real.Gamma (((k + 1 : ℕ) : ℝ) + (α + 1)) :=
    gam_succ (α + 1) (k + 1) p1
  have g2 : Real.Gamma (((k + 2 : ℕ) : ℝ) + (β + 1)) =
      (((k + 1 : ℕ) : ℝ) + (β + 1)) * Real.Gamma (((k + 1 : ℕ) : ℝ) + (β + 1)) :=
    gam_succ (β + 1) (k + 1) p2
  have g3 : Real.Gamma (((k + 2 : ℕ) : ℝ) + (α + β + 1)) =
      (((k + 1 : ℕ) : ℝ) + (α + β + 1)) * Real.Gamma (((k + 1 : ℕ) : ℝ) + (α + β + 1)) :=
    gam_succ (α + β + 1) (k + 1) p3
  have hf : (((k + 2).factorial : ℕ) : ℝ) = ((k : ℝ) + 2) * (((k + 1).factorial : ℕ) : ℝ) := by
    rw [show k + 2 = (k + 1) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  have hA : 0 < Real.Gamma (((k + 1 : ℕ) : ℝ) + (α + 1)) := Real.Gamma_pos_of_pos p1
  have hB : 0 < Real.Gamma (((k + 1 : ℕ) : ℝ) + (β + 1)) := Real.Gamma_pos_of_pos p2
  have hG : 0 < Real.Gamma (((k + 1 : ℕ) : ℝ) + (α + β + 1)) := Real.Gamma_pos_of_pos p3
  have hF : (0 : ℝ) < (((k + 1).factorial : ℕ) : ℝ) := by positivity
  unfold jacNormR jacA jacC
  rw [g1, g2, g3, hf]
  generalize Real.Gamma (((k + 1 : ℕ) : ℝ) + (α + 1)) = A at *
  generalize Real.Gamma (((k + 1 : ℕ) : ℝ) + (β + 1)) = B at *
  generalize Real.Gamma (((k + 1 : ℕ) : ℝ) + (α + β + 1)) = G at *
  generalize (((k + 1).factorial : ℕ) : ℝ) = f at *
  generalize (2 : ℝ) ^ (α + β + 1) = K
  push_cast
  have q1 : (2 * ((k : ℝ) + 1) + α + β + 1) = 2 * k + α + β + 3 := by ring
  have q2 : (2 * ((k : ℝ) + 2) + α + β + 1) = 2 * k + α + β + 5 := by ring
  have r1 : (0 : ℝ) < 2 * k + α + β + 3 := by linarith
  have r2 : (0 : ℝ) < 2 * k + α + β + 4 := by linarith
  have r3 : (0 : ℝ) < 2 * k + α + β + 5 := by linarith
  have r4 : (0 : ℝ) < (k : ℝ) + 1 + (α + β + 1) := by linarith
  have r5 : (0 : ℝ) < (k : ℝ) + 2 := by linarith
  have q3 : (2 * ((k : ℝ) + 1) + α + β + 2) = 2 * k + α + β + 4 := by ring
  have q4 : (2 * ((k : ℝ) + 1) + α + β + 3) = 2 * k + α + β + 5 := by ring
  rw [q1, q2, q3, q4]
  have r1' := r1.ne'
  have r2' := r2.ne'
  have r3' := r3.ne'
  have r4' := r4.ne'
  have r5' := r5.ne'
  have hA' := hA.ne'
  have hB' := hB.ne'
  have hG' := hG.ne'
  have hF' := hF.ne'
  field_simp
  ring

lemma jacIPr_zero_zero {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    jacIPr α β (jacobi α β 0) (jacobi α β 0) =
      2 ^ (α + β + 1) * (Real.Gamma (α + 1) * Real.Gamma (β + 1)) / Real.Gamma (α + β + 2) := by
  unfold jacIPr
  simp only [jacobi_zero, eval_one, mul_one]
  exact jacobi_beta_integral hα hβ

lemma jacIPr_one_one {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    jacIPr α β (jacobi α β 1) (jacobi α β 1) = jacNormR α β 1 := by
  have hA0 : jacA0 α β ≠ 0 := by
    unfold jacA0
    have : (0 : ℝ) < α + β + 2 := by linarith
    positivity
  refine mul_left_cancel₀ hA0 ?_
  rw [jacIPr_step_zero hα hβ, jacIPr_zero_zero hα hβ, jacNormR_step_zero hα hβ]

/-- The weighted inner product of `P_n` with itself is `jacNormR α β n`, for `n ≥ 1`. -/
theorem jacIPr_self {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (hn : 1 ≤ n) :
    jacIPr α β (jacobi α β n) (jacobi α β n) = jacNormR α β n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih, hn with
    | 0, _, hn => omega
    | 1, _, _ => exact jacIPr_one_one hα hβ
    | k + 2, ih, _ =>
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hA : jacA α β k ≠ 0 := by
        unfold jacA
        refine div_ne_zero (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)).ne' ?_
        exact (mul_pos (by linarith) (by linarith)).ne'
      refine mul_left_cancel₀ hA ?_
      rw [jacIPr_step_succ hα hβ, jacNormR_step_succ hα hβ, ih (k + 1) (by omega) (by omega)]

/-- **Norm of Jacobi polynomials, `n = 0`** (DLMF 18.3, table 18.3.1): the Beta integral
`∫_{-1}^1 (1-x)^α (1+x)^β dx = 2^(α+β+1) Γ(α+1) Γ(β+1) / Γ(α+β+2)`, `α, β > -1`. -/
theorem jacobi_norm_real_zero {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    ∫ x in (-1 : ℝ)..1, (1 - x) ^ α * (1 + x) ^ β * ((jacobi α β 0).eval x) ^ 2 =
      2 ^ (α + β + 1) * (Real.Gamma (α + 1) * Real.Gamma (β + 1)) / Real.Gamma (α + β + 2) := by
  rw [← jacIPr_zero_zero hα hβ]
  unfold jacIPr jacobiW
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  ring

/-- **Norm of Jacobi polynomials** (DLMF 18.3, table 18.3.1) for real `α, β > -1`:
`∫_{-1}^1 (1-x)^α (1+x)^β P_n^{(α,β)}(x)² dx
  = 2^(α+β+1) / (2n+α+β+1) · Γ(n+α+1) Γ(n+β+1) / (Γ(n+α+β+1) n!)`.
The right-hand side is `0/0` for `n = 0` and `α + β + 1 = 0`; that case is
`jacobi_norm_real_zero`. -/
theorem jacobi_norm_real {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ)
    (hn : n ≠ 0 ∨ α + β + 1 ≠ 0) :
    ∫ x in (-1 : ℝ)..1, (1 - x) ^ α * (1 + x) ^ β * ((jacobi α β n).eval x) ^ 2 =
      2 ^ (α + β + 1) / (2 * (n : ℝ) + α + β + 1) *
        (Real.Gamma ((n : ℝ) + α + 1) * Real.Gamma ((n : ℝ) + β + 1)) /
        (Real.Gamma ((n : ℝ) + α + β + 1) * (n.factorial : ℝ)) := by
  have e1 : (n : ℝ) + α + 1 = n + (α + 1) := by ring
  have e2 : (n : ℝ) + β + 1 = n + (β + 1) := by ring
  have e3 : (n : ℝ) + α + β + 1 = n + (α + β + 1) := by ring
  rw [e1, e2, e3]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hne : α + β + 1 ≠ 0 := by
      rcases hn with h | h
      · exact absurd rfl h
      · exact h
    rw [jacobi_norm_real_zero hα hβ]
    have hΓ : Real.Gamma (α + β + 1) = Real.Gamma (α + β + 2) / (α + β + 1) := by
      rw [eq_div_iff hne, mul_comm, show α + β + 2 = (α + β + 1) + 1 by ring]
      exact (Real.Gamma_add_one hne).symm
    simp only [Nat.cast_zero, zero_add, mul_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
    rw [hΓ]
    have hG : 0 < Real.Gamma (α + β + 2) := Real.Gamma_pos_of_pos (by linarith)
    field_simp
  · have := jacIPr_self hα hβ n hpos
    unfold jacIPr jacNormR at this
    rw [← this]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [jacobiW]; ring

/-! ### Orthogonality to lower-degree polynomials -/

/-- For `α + β + 2 > 0` and `n ≥ 1` the leading coefficient of `jacobi α β n` is nonzero. -/
lemma jacobi_coeff_self_ne_zero_real {α β : ℝ} (hs : 0 < α + β + 2) (n : ℕ) (hn : 1 ≤ n) :
    (jacobi α β n).coeff n ≠ 0 := by
  rw [jacobi_coeff_self]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (ascPochhammer ℝ n).eval ((n : ℝ) + α + β + 1) :=
    ascPochhammer_pos n _ (by linarith)
  positivity

/-- `jacobi α β n` is orthogonal to every polynomial of degree `< n` (real `α, β > -1`), in the
inner-product form. -/
lemma jacIPr_orth_lowerDegree {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ∀ k, k < n → ∀ q : ℝ[X], q.natDegree ≤ k → jacIPr α β q (jacobi α β n) = 0 := by
  have hs : (0 : ℝ) < α + β + 2 := by linarith
  intro k
  induction k with
  | zero =>
    intro hk q hq
    have hq' : q = C (q.coeff 0) * jacobi α β 0 := by
      rw [jacobi_zero, mul_one]; exact eq_C_of_natDegree_le_zero hq
    rw [hq', jacIPr_C_mul_left, jacIPr_orth hα hβ 0 n (by omega), mul_zero]
  | succ k ih =>
    intro hk q hq
    set P := jacobi α β (k + 1) with hP
    have hlead : P.coeff (k + 1) ≠ 0 := jacobi_coeff_self_ne_zero_real hs (k + 1) (by omega)
    set c := q.coeff (k + 1) / P.coeff (k + 1) with hc
    set r := q - C c * P with hr
    have hPdeg : P.natDegree ≤ k + 1 := natDegree_jacobi_le _ _ _
    have hrdeg : r.natDegree ≤ k := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hr, coeff_sub, coeff_C_mul]
      rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hN) with h | h
      · rw [← h, hc]; field_simp; ring
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < N),
          coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < N)]
        simp
    have hq' : q = r + C c * P := by rw [hr]; ring
    rw [hq', jacIPr_add_left hα hβ, jacIPr_C_mul_left, ih (by omega) r hrdeg,
      jacIPr_orth hα hβ (k + 1) n (by omega), mul_zero, add_zero]

/-- `jacobi α β n` is orthogonal, for the weight `(1-x)^α (1+x)^β`, to every polynomial of
degree `< n`, for real `α, β > -1`. -/
theorem jacobi_orthogonal_lowerDegree_real {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ)
    (q : ℝ[X]) (hq : q.natDegree < n) :
    ∫ x in (-1 : ℝ)..1, (1 - x) ^ α * (1 + x) ^ β * q.eval x * (jacobi α β n).eval x = 0 :=
  jacIPr_orth_lowerDegree hα hβ n q.natDegree hq q le_rfl

/-- info: 'FormalResearch.Special.jacobi_orthogonal_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_orthogonal_real

/-- info: 'FormalResearch.Special.jacobi_orthogonal_lowerDegree_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_orthogonal_lowerDegree_real

/-- info: 'FormalResearch.Special.jacobi_norm_real_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_norm_real_zero

/-- info: 'FormalResearch.Special.jacobi_norm_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_norm_real

end FormalResearch.Special
