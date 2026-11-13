module

public import FormalResearch.Special.JacobiBasic
public import FormalResearch.Special.JacobiRec

/-!
# Jacobi polynomials: orthogonality and norms

For natural parameters `a b : ℕ` the Jacobi polynomials `jacobi a b n` (DLMF 18.5.7) are orthogonal
on `[-1,1]` for the weight `(1-x)^a (1+x)^b` (DLMF 18.3.1), with the norm of DLMF 18.3, table 18.3.1:

  `∫_{-1}^1 (1-x)^a (1+x)^b P_n^{(a,b)}(x)² dx
      = 2^(a+b+1) / (2n+a+b+1) · (n+a)! (n+b)! / ((n+a+b)! n!)`.

## Main results

* `jacobi_orthogonal`: `∫ w P_m P_n = 0` for `m ≠ n`, unconditionally, weight written out;
* `jacobi_orthogonal_lowerDegree`: `∫ w q P_n = 0` for every polynomial `q` of degree `< n`;
* `jacobi_norm`: the norm integral above (DLMF 18.3, table 18.3.1);
* `jacobi_norm_cos`: the form used for Wigner `d`-functions,
  `∫_0^π sin(θ/2)^(2a) cos(θ/2)^(2b) P_n(cos θ)² sin θ dθ
     = 2/(2n+a+b+1) · (n+a)! (n+b)! / ((n+a+b)! n!)`.

The norm is obtained from the normalised three-term recurrence (`jacobi_X_mul_succ`): the inner
product `⟨x P_n, P_{n+1}⟩` is computed twice, giving `h_{n+1} = c_{n+1}/a_n · h_n`, and the base case
`h_0` is the Beta integral `beta_nat`.
-/

@[expose] public section

namespace FormalResearch.Special

open Polynomial MeasureTheory intervalIntegral

/-- The weighted inner product `∫_{-1}^1 (1-x)^a (1+x)^b f g` of two polynomials. -/
noncomputable def jacIP (a b : ℕ) (f g : ℝ[X]) : ℝ :=
  ∫ x in (-1 : ℝ)..1, (jacobiWeight a b).eval x * f.eval x * g.eval x

lemma jacIP_add_left (a b : ℕ) (f₁ f₂ g : ℝ[X]) :
    jacIP a b (f₁ + f₂) g = jacIP a b f₁ g + jacIP a b f₂ g := by
  unfold jacIP
  have h1 : IntervalIntegrable (fun x => (jacobiWeight a b).eval x * f₁.eval x * g.eval x)
      volume (-1 : ℝ) 1 := by
    simpa only [eval_mul] using poly_intervalIntegrable (jacobiWeight a b * f₁ * g)
  have h2 : IntervalIntegrable (fun x => (jacobiWeight a b).eval x * f₂.eval x * g.eval x)
      volume (-1 : ℝ) 1 := by
    simpa only [eval_mul] using poly_intervalIntegrable (jacobiWeight a b * f₂ * g)
  rw [← intervalIntegral.integral_add h1 h2]
  congr 1; funext x; simp only [eval_add]; ring

lemma jacIP_C_mul_left (a b : ℕ) (c : ℝ) (f g : ℝ[X]) :
    jacIP a b (C c * f) g = c * jacIP a b f g := by
  unfold jacIP
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext x; simp only [eval_mul, eval_C]; ring

lemma jacIP_X_mul (a b : ℕ) (f g : ℝ[X]) : jacIP a b (X * f) g = jacIP a b f (X * g) := by
  unfold jacIP
  congr 1; funext x; simp only [eval_mul, eval_X]; ring

lemma jacIP_comm (a b : ℕ) (f g : ℝ[X]) : jacIP a b f g = jacIP a b g f := by
  unfold jacIP
  congr 1; funext x; ring

lemma jacIP_orth (a b m n : ℕ) (h : m ≠ n) :
    jacIP a b (jacobi (a : ℝ) (b : ℝ) m) (jacobi (a : ℝ) (b : ℝ) n) = 0 :=
  jacobi_orth_of_SL a b m n (jacobiSL_all a b m) (jacobiSL_all a b n) h

lemma jacobiWeight_eval (a b : ℕ) (x : ℝ) :
    (jacobiWeight a b).eval x = (1 - x) ^ a * (1 + x) ^ b := by
  simp [jacobiWeight]

/-- **Orthogonality of Jacobi polynomials** (DLMF 18.3.1) for natural parameters. -/
theorem jacobi_orthogonal (a b m n : ℕ) (h : m ≠ n) :
    ∫ x in (-1 : ℝ)..1, (1 - x) ^ a * (1 + x) ^ b * (jacobi (a : ℝ) (b : ℝ) m).eval x *
      (jacobi (a : ℝ) (b : ℝ) n).eval x = 0 := by
  have := jacIP_orth a b m n h
  unfold jacIP at this
  simpa only [jacobiWeight_eval] using this

/-- `jacobi a b n` is orthogonal to every polynomial of lower degree. -/
theorem jacobi_orthogonal_lowerDegree (a b n : ℕ) (q : ℝ[X]) (hq : q.natDegree < n) :
    ∫ x in (-1 : ℝ)..1, (1 - x) ^ a * (1 + x) ^ b * q.eval x *
      (jacobi (a : ℝ) (b : ℝ) n).eval x = 0 := by
  have := jacobi_orth_lowerDegree a b n (jacobiSL_all a b) q hq
  simpa only [jacobiWeight_eval] using this

/-- The squared norm `h_n = ⟨P_n, P_n⟩` of `jacobi a b n`, as a closed form. -/
noncomputable def jacNorm (a b n : ℕ) : ℝ :=
  2 ^ (a + b + 1) / (2 * (n : ℝ) + a + b + 1) *
    (((n + a).factorial : ℝ) * ((n + b).factorial : ℝ)) /
    (((n + a + b).factorial : ℝ) * (n.factorial : ℝ))

lemma jacNorm_zero (a b : ℕ) : jacIP a b (jacobi (a : ℝ) (b : ℝ) 0) (jacobi (a : ℝ) (b : ℝ) 0)
    = jacNorm a b 0 := by
  unfold jacIP jacNorm
  simp only [jacobi_zero, eval_one, mul_one, jacobiWeight_eval]
  rw [beta_nat]
  simp only [zero_add, Nat.cast_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
  have hf : (((a + b).factorial : ℝ)) ≠ 0 := by positivity
  rw [Nat.factorial_succ (a + b)]
  push_cast
  have h1 : ((a : ℝ) + b + 1) ≠ 0 := by positivity
  field_simp

/-- `⟨x P_{n+1}, P_n⟩ = c_n h_n` from the normalised recurrence. -/
lemma jacIP_X_succ_self (a b n : ℕ) :
    jacIP a b (X * jacobi (a : ℝ) (b : ℝ) (n + 1)) (jacobi (a : ℝ) (b : ℝ) n)
      = jacC (a : ℝ) (b : ℝ) n *
        jacIP a b (jacobi (a : ℝ) (b : ℝ) n) (jacobi (a : ℝ) (b : ℝ) n) := by
  have hs : (0 : ℝ) < (a : ℝ) + b + 2 := by positivity
  rw [jacobi_X_mul_succ _ _ hs n, jacIP_add_left, jacIP_add_left, jacIP_C_mul_left,
    jacIP_C_mul_left, jacIP_C_mul_left, jacIP_orth a b (n + 2) n (by omega),
    jacIP_orth a b (n + 1) n (by omega)]
  ring

/-- `h_1 a_0 = c_0 h_0`. -/
lemma jacIP_step_zero (a b : ℕ) :
    jacA0 (a : ℝ) (b : ℝ) * jacIP a b (jacobi (a : ℝ) (b : ℝ) 1) (jacobi (a : ℝ) (b : ℝ) 1)
      = jacC (a : ℝ) (b : ℝ) 0 *
        jacIP a b (jacobi (a : ℝ) (b : ℝ) 0) (jacobi (a : ℝ) (b : ℝ) 0) := by
  have hs : (0 : ℝ) < (a : ℝ) + b + 2 := by positivity
  calc jacA0 (a : ℝ) (b : ℝ) * jacIP a b (jacobi (a : ℝ) (b : ℝ) 1) (jacobi (a : ℝ) (b : ℝ) 1)
      = jacIP a b (X * jacobi (a : ℝ) (b : ℝ) 0) (jacobi (a : ℝ) (b : ℝ) 1) := by
        rw [jacobi_X_mul_zero _ _ hs, jacIP_add_left, jacIP_C_mul_left, jacIP_C_mul_left,
          jacIP_orth a b 0 1 (by omega)]
        ring
    _ = jacIP a b (jacobi (a : ℝ) (b : ℝ) 1) (X * jacobi (a : ℝ) (b : ℝ) 0) := by
        rw [jacIP_comm]
    _ = jacIP a b (X * jacobi (a : ℝ) (b : ℝ) 1) (jacobi (a : ℝ) (b : ℝ) 0) :=
        (jacIP_X_mul a b _ _).symm
    _ = _ := jacIP_X_succ_self a b 0

/-- `a_k h_{k+2} = c_{k+1} h_{k+1}`. -/
lemma jacIP_step_succ (a b k : ℕ) :
    jacA (a : ℝ) (b : ℝ) k *
        jacIP a b (jacobi (a : ℝ) (b : ℝ) (k + 2)) (jacobi (a : ℝ) (b : ℝ) (k + 2))
      = jacC (a : ℝ) (b : ℝ) (k + 1) *
        jacIP a b (jacobi (a : ℝ) (b : ℝ) (k + 1)) (jacobi (a : ℝ) (b : ℝ) (k + 1)) := by
  have hs : (0 : ℝ) < (a : ℝ) + b + 2 := by positivity
  calc jacA (a : ℝ) (b : ℝ) k *
        jacIP a b (jacobi (a : ℝ) (b : ℝ) (k + 2)) (jacobi (a : ℝ) (b : ℝ) (k + 2))
      = jacIP a b (X * jacobi (a : ℝ) (b : ℝ) (k + 1)) (jacobi (a : ℝ) (b : ℝ) (k + 2)) := by
        rw [jacobi_X_mul_succ _ _ hs k, jacIP_add_left, jacIP_add_left, jacIP_C_mul_left,
          jacIP_C_mul_left, jacIP_C_mul_left, jacIP_orth a b k (k + 2) (by omega),
          jacIP_orth a b (k + 1) (k + 2) (by omega)]
        ring
    _ = jacIP a b (jacobi (a : ℝ) (b : ℝ) (k + 1)) (X * jacobi (a : ℝ) (b : ℝ) (k + 2)) :=
        jacIP_X_mul a b _ _
    _ = jacIP a b (X * jacobi (a : ℝ) (b : ℝ) (k + 2)) (jacobi (a : ℝ) (b : ℝ) (k + 1)) :=
        jacIP_comm a b _ _
    _ = _ := jacIP_X_succ_self a b (k + 1)

lemma jacNorm_one (a b : ℕ) : jacIP a b (jacobi (a : ℝ) (b : ℝ) 1) (jacobi (a : ℝ) (b : ℝ) 1)
    = jacNorm a b 1 := by
  have hA0 : jacA0 (a : ℝ) (b : ℝ) ≠ 0 := by unfold jacA0; positivity
  refine mul_left_cancel₀ hA0 ?_
  rw [jacIP_step_zero, jacNorm_zero]
  unfold jacA0 jacC jacNorm
  have fa : (((1 + a).factorial : ℕ) : ℝ) = ((a.factorial : ℕ) : ℝ) * ((a : ℝ) + 1) := by
    rw [show 1 + a = a + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have fb : (((1 + b).factorial : ℕ) : ℝ) = ((b.factorial : ℕ) : ℝ) * ((b : ℝ) + 1) := by
    rw [show 1 + b = b + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have fs : (((1 + a + b).factorial : ℕ) : ℝ)
      = (((a + b).factorial : ℕ) : ℝ) * ((a : ℝ) + b + 1) := by
    rw [show 1 + a + b = (a + b) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have f0 : (((0 + a).factorial : ℕ) : ℝ) = ((a.factorial : ℕ) : ℝ) := by simp
  have f0' : (((0 + b).factorial : ℕ) : ℝ) = ((b.factorial : ℕ) : ℝ) := by simp
  have f0'' : (((0 + a + b).factorial : ℕ) : ℝ) = (((a + b).factorial : ℕ) : ℝ) := by simp
  rw [fa, fb, fs, f0, f0', f0'']
  simp only [Nat.cast_zero, mul_zero, zero_add, Nat.cast_one, Nat.factorial_zero, Nat.factorial_one,
    mul_one, pow_succ]
  have hf : (a.factorial : ℝ) ≠ 0 := by positivity
  have hg : (b.factorial : ℝ) ≠ 0 := by positivity
  have hh : ((a + b).factorial : ℝ) ≠ 0 := by positivity
  have h1 : (a : ℝ) + b + 1 ≠ 0 := by positivity
  have h2 : (a : ℝ) + b + 2 ≠ 0 := by positivity
  have h3 : (a : ℝ) + b + 3 ≠ 0 := by positivity
  have h4 : (2 : ℝ) + a + b + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma jacNorm_succ_succ (a b k : ℕ) :
    jacA (a : ℝ) (b : ℝ) k * jacNorm a b (k + 2)
      = jacC (a : ℝ) (b : ℝ) (k + 1) * jacNorm a b (k + 1) := by
  unfold jacA jacC jacNorm
  have fa : (((k + 1 + a).factorial : ℕ) : ℝ) = (((k + a).factorial : ℕ) : ℝ) * ((k : ℝ) + a + 1) := by
    rw [show k + 1 + a = (k + a) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have fb : (((k + 1 + b).factorial : ℕ) : ℝ) = (((k + b).factorial : ℕ) : ℝ) * ((k : ℝ) + b + 1) := by
    rw [show k + 1 + b = (k + b) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have fs : (((k + 1 + a + b).factorial : ℕ) : ℝ)
      = (((k + a + b).factorial : ℕ) : ℝ) * ((k : ℝ) + a + b + 1) := by
    rw [show k + 1 + a + b = (k + a + b) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have fa2 : (((k + 2 + a).factorial : ℕ) : ℝ)
      = (((k + a).factorial : ℕ) : ℝ) * ((k : ℝ) + a + 1) * ((k : ℝ) + a + 2) := by
    rw [show k + 2 + a = (k + a) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have fb2 : (((k + 2 + b).factorial : ℕ) : ℝ)
      = (((k + b).factorial : ℕ) : ℝ) * ((k : ℝ) + b + 1) * ((k : ℝ) + b + 2) := by
    rw [show k + 2 + b = (k + b) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have fs2 : (((k + 2 + a + b).factorial : ℕ) : ℝ)
      = (((k + a + b).factorial : ℕ) : ℝ) * ((k : ℝ) + a + b + 1) * ((k : ℝ) + a + b + 2) := by
    rw [show k + 2 + a + b = (k + a + b) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have fk1 : (((k + 1).factorial : ℕ) : ℝ) = (k.factorial : ℝ) * ((k : ℝ) + 1) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have fk2 : (((k + 2).factorial : ℕ) : ℝ) = (k.factorial : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    rw [show k + 2 = k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  rw [fa, fb, fs, fa2, fb2, fs2, fk1, fk2]
  push_cast
  have hf : ((k + a).factorial : ℝ) ≠ 0 := by positivity
  have hg : ((k + b).factorial : ℝ) ≠ 0 := by positivity
  have hh : ((k + a + b).factorial : ℝ) ≠ 0 := by positivity
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have p1 : (0 : ℝ) < 2 * k + a + b + 3 := by positivity
  have p2 : (0 : ℝ) < 2 * k + a + b + 4 := by positivity
  have p3 : (0 : ℝ) < 2 * k + a + b + 5 := by positivity
  have p5 : (0 : ℝ) < (k : ℝ) + a + b + 1 := by positivity
  have p6 : (0 : ℝ) < (k : ℝ) + a + b + 2 := by positivity
  have p8 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have p9 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have p10 : (0 : ℝ) < 2 * k + a + b + 2 := by positivity
  have p11 : (0 : ℝ) < 2 * k + a + b + 1 := by positivity
  have e1 : (2 * ((k : ℝ) + 1) + a + b + 1) = 2 * k + a + b + 3 := by ring
  have e2 : (2 * ((k : ℝ) + 2) + a + b + 1) = 2 * k + a + b + 5 := by ring
  have e3 : (2 * ((k : ℝ) + 1) + a + b + 2) = 2 * k + a + b + 4 := by ring
  have e4 : (2 * ((k : ℝ) + 1) + a + b + 3) = 2 * k + a + b + 5 := by ring
  simp only [e1, e2, e3, e4]
  field_simp
  ring

/-- The weighted inner product of `P_n` with itself is `jacNorm a b n`. -/
theorem jacIP_self (a b n : ℕ) :
    jacIP a b (jacobi (a : ℝ) (b : ℝ) n) (jacobi (a : ℝ) (b : ℝ) n) = jacNorm a b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => exact jacNorm_zero a b
    | 1, _ => exact jacNorm_one a b
    | k + 2, ih =>
      have hA : jacA (a : ℝ) (b : ℝ) k ≠ 0 := by unfold jacA; positivity
      refine mul_left_cancel₀ hA ?_
      rw [jacIP_step_succ, jacNorm_succ_succ, ih (k + 1) (by omega)]

/-- **Norm of Jacobi polynomials** (DLMF 18.3, table 18.3.1) for natural parameters:
`∫_{-1}^1 (1-x)^a (1+x)^b P_n^{(a,b)}(x)² dx
  = 2^(a+b+1) / (2n+a+b+1) · (n+a)! (n+b)! / ((n+a+b)! n!)`. -/
theorem jacobi_norm (a b n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (1 - x) ^ a * (1 + x) ^ b * ((jacobi (a : ℝ) (b : ℝ) n).eval x) ^ 2 =
      2 ^ (a + b + 1) / (2 * (n : ℝ) + a + b + 1) *
        (((n + a).factorial : ℝ) * ((n + b).factorial : ℝ)) /
        (((n + a + b).factorial : ℝ) * (n.factorial : ℝ)) := by
  have := jacIP_self a b n
  unfold jacIP jacNorm at this
  rw [← this]
  congr 1; funext x
  rw [jacobiWeight_eval]; ring

/-- The norm in the half-angle form used for Wigner `d`-functions:
`∫_0^π sin(θ/2)^(2a) cos(θ/2)^(2b) P_n^{(a,b)}(cos θ)² sin θ dθ
  = 2/(2n+a+b+1) · (n+a)! (n+b)! / ((n+a+b)! n!)`. -/
theorem jacobi_norm_cos (a b n : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin (θ / 2) ^ (2 * a) * Real.cos (θ / 2) ^ (2 * b) *
        ((jacobi (a : ℝ) (b : ℝ) n).eval (Real.cos θ)) ^ 2 * Real.sin θ =
      2 / (2 * (n : ℝ) + a + b + 1) *
        (((n + a).factorial : ℝ) * ((n + b).factorial : ℝ)) /
        (((n + a + b).factorial : ℝ) * (n.factorial : ℝ)) := by
  have hf : Continuous (fun x : ℝ => (1 - x) ^ a * (1 + x) ^ b *
      ((jacobi (a : ℝ) (b : ℝ) n).eval x) ^ 2) := by fun_prop
  have h := integral_cos_substitution _ hf
  rw [jacobi_norm] at h
  have hc : ∀ θ : ℝ, 1 + Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 := by
    intro θ
    rw [Real.cos_sq (θ / 2)]
    rw [show 2 * (θ / 2) = θ by ring]; ring
  have hs : ∀ θ : ℝ, 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
    intro θ
    have h := Real.cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    rw [Real.sin_sq]; linarith
  have e : ∀ θ : ℝ, (1 - Real.cos θ) ^ a * (1 + Real.cos θ) ^ b *
        ((jacobi (a : ℝ) (b : ℝ) n).eval (Real.cos θ)) ^ 2 * Real.sin θ =
      2 ^ (a + b) * (Real.sin (θ / 2) ^ (2 * a) * Real.cos (θ / 2) ^ (2 * b) *
        ((jacobi (a : ℝ) (b : ℝ) n).eval (Real.cos θ)) ^ 2 * Real.sin θ) := by
    intro θ
    rw [hs, hc, mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]
    ring
  simp only [e] at h
  rw [intervalIntegral.integral_const_mul] at h
  have h2 : (2 : ℝ) ^ (a + b) ≠ 0 := by positivity
  have h3 : (2 : ℝ) ^ (a + b + 1) = 2 ^ (a + b) * 2 := pow_succ _ _
  rw [h3] at h
  have h4 := h
  field_simp at h4 ⊢
  linarith

/-- info: 'FormalResearch.Special.jacobi_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_orthogonal

/-- info: 'FormalResearch.Special.jacobi_orthogonal_lowerDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_orthogonal_lowerDegree

/-- info: 'FormalResearch.Special.jacobi_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_norm

/-- info: 'FormalResearch.Special.jacobi_norm_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_norm_cos

end FormalResearch.Special
