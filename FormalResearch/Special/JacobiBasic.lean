module

public import FormalResearch.Special.JacobiInt

/-!
# Jacobi polynomials: basic properties

Basic identities for `jacobi α β n` (`FormalResearch/Special/JacobiDef.lean`, DLMF 18.5.7), for
arbitrary real `α β` unless stated otherwise. All proofs work in the basis `(X - 1)^ℓ`, using the
coefficient ratio recurrence `2 (ℓ+1) (α+ℓ+1) c_{ℓ+1} = (n-ℓ) (n+ℓ+α+β+1) c_ℓ`.

* `jacobi_eval_one`: `P_n^{(α,β)}(1) = (α+1)_n / n!` (DLMF 18.6.1);
* `jacobi_eval_neg_one`: `P_n^{(α,β)}(-1) = (-1)^n (β+1)_n / n!` (DLMF 18.6.1);
* `derivative_jacobi`: `d/dx P_{n+1}^{(α,β)} = (n+α+β+2)/2 · P_n^{(α+1,β+1)}` (DLMF 18.9.15);
* `jacobi_ode`: the Jacobi differential equation as a polynomial identity (DLMF 18.8.1);
* `jacobi_sturmLiouville`, `jacobiSL_all`: its self-adjoint form for natural `α β`, and
  `JacobiSL a b m` of `JacobiInt` for all `a b m`;
* `jacobi_comp_neg`: the reflection formula `P_n^{(α,β)}(-x) = (-1)^n P_n^{(β,α)}(x)`
  (DLMF 18.6.1).

The degree bound and leading coefficient (DLMF 18.3 table) are `natDegree_jacobi_le` and
`jacobi_coeff_self` in `FormalResearch/Special/JacobiInt.lean`.
-/

@[expose] public section

namespace FormalResearch.Special

open Polynomial

/-- `(y)_{n+1} = y (y+1)_n`. -/
lemma poch_succ_left_eval (n : ℕ) (y : ℝ) :
    (ascPochhammer ℝ (n + 1)).eval y = y * (ascPochhammer ℝ n).eval (y + 1) := by
  simp [ascPochhammer_succ_left, eval_comp]

/-- Ratio recurrence for the coefficients, in cleared-denominator form. -/
lemma jacobiCoeff_succ (α β : ℝ) (n ℓ : ℕ) (h : ℓ < n) :
    2 * ((ℓ : ℝ) + 1) * (α + ℓ + 1) * jacobiCoeff α β n (ℓ + 1) =
      ((n : ℝ) - ℓ) * ((n : ℝ) + ℓ + α + β + 1) * jacobiCoeff α β n ℓ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = ℓ + 1 + k := ⟨n - ℓ - 1, by omega⟩
  have h1 : ℓ + 1 + k - (ℓ + 1) = k := by omega
  have h2 : ℓ + 1 + k - ℓ = k + 1 := by omega
  unfold jacobiCoeff
  rw [h1, h2, ascPochhammer_succ_eval, poch_succ_left_eval k, Nat.factorial_succ ℓ,
    Nat.factorial_succ k]
  have e1 : (α + ((ℓ + 1 : ℕ) : ℝ) + 1) = α + ℓ + 1 + 1 := by push_cast; ring
  have e2 : (((ℓ + 1 + k : ℕ) : ℝ) + α + β + 1) = ((ℓ + 1 + k : ℕ) : ℝ) + α + β + 1 := rfl
  rw [e1]
  generalize (ascPochhammer ℝ ℓ).eval (((ℓ + 1 + k : ℕ) : ℝ) + α + β + 1) = A
  generalize (ascPochhammer ℝ k).eval (α + ℓ + 1 + 1) = B
  have hk : ((ℓ + 1 + k : ℕ) : ℝ) = ℓ + 1 + k := by push_cast; ring
  rw [hk]
  have hf : (0:ℝ) < (ℓ.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos ℓ
  have hg : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  push_cast
  field_simp
  ring


/-- Value at `1` (DLMF 18.6.1): `P_n^{(α,β)}(1) = (α+1)_n / n!`. -/
lemma jacobi_eval_one (α β : ℝ) (n : ℕ) :
    (jacobi α β n).eval 1 = (ascPochhammer ℝ n).eval (α + 1) / (n.factorial : ℝ) := by
  rw [jacobi_eval, Finset.sum_range_succ']
  simp [jacobiCoeff]

/-- Coefficient form of DLMF 18.9.15. -/
lemma jacobiCoeff_deriv (α β : ℝ) (n ℓ : ℕ) :
    ((ℓ : ℝ) + 1) * jacobiCoeff α β (n + 1) (ℓ + 1) =
      ((n : ℝ) + α + β + 2) / 2 * jacobiCoeff (α + 1) (β + 1) n ℓ := by
  unfold jacobiCoeff
  have h1 : n + 1 - (ℓ + 1) = n - ℓ := by omega
  rw [h1, poch_succ_left_eval ℓ, Nat.factorial_succ ℓ, pow_succ]
  have e1 : (α + ((ℓ + 1 : ℕ) : ℝ) + 1) = α + 1 + ℓ + 1 := by push_cast; ring
  have e2 : (((n + 1 : ℕ) : ℝ) + α + β + 1) + 1 = (n : ℝ) + (α + 1) + (β + 1) + 1 := by
    push_cast; ring
  have e3 : (((n + 1 : ℕ) : ℝ) + α + β + 1) = (n : ℝ) + α + β + 2 := by
    push_cast; ring
  rw [e1, e2, e3]
  generalize (ascPochhammer ℝ ℓ).eval ((n : ℝ) + (α + 1) + (β + 1) + 1) = A
  generalize (ascPochhammer ℝ (n - ℓ)).eval (α + 1 + ℓ + 1) = B
  have hf : (0:ℝ) < (ℓ.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos ℓ
  have hg : (0:ℝ) < ((n - ℓ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  push_cast
  field_simp


/-- Derivative of a power of `X - 1`. -/
lemma derivative_xsub_pow (ℓ : ℕ) :
    derivative ((X - 1 : ℝ[X]) ^ ℓ) = C (ℓ : ℝ) * (X - 1) ^ (ℓ - 1) := by
  simp [derivative_pow]

/-- Derivative formula (DLMF 18.9.15): `d/dx P_{n+1}^{(α,β)} = (n+α+β+2)/2 · P_n^{(α+1,β+1)}`. -/
lemma derivative_jacobi (α β : ℝ) (n : ℕ) :
    derivative (jacobi α β (n + 1)) =
      C (((n : ℝ) + α + β + 2) / 2) * jacobi (α + 1) (β + 1) n := by
  unfold jacobi
  simp only [derivative_sum, derivative_C_mul, derivative_xsub_pow]
  rw [Finset.sum_range_succ' _ (n + 1), Finset.mul_sum]
  simp only [Nat.cast_zero, map_zero, mul_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have h := jacobiCoeff_deriv α β n ℓ
  rw [← mul_assoc, ← C_mul, ← mul_assoc, ← C_mul]
  simp only [Nat.add_sub_cancel]
  congr 2
  push_cast
  linarith [h, mul_comm ((ℓ : ℝ) + 1) (jacobiCoeff α β (n + 1) (ℓ + 1))]


/-- The Jacobi operator applied to a power of `X - 1`. -/
lemma jacobiOp_pow (α β : ℝ) (ℓ : ℕ) :
    (1 - X ^ 2) * derivative (derivative ((X - 1 : ℝ[X]) ^ ℓ)) +
        (C (β - α) - C (α + β + 2) * X) * derivative ((X - 1 : ℝ[X]) ^ ℓ) =
      - C ((ℓ : ℝ) * (ℓ + α + β + 1)) * (X - 1) ^ ℓ -
        C (2 * (ℓ : ℝ) * (ℓ + α)) * (X - 1) ^ (ℓ - 1) := by
  rcases ℓ with _ | _ | m
  · simp
  · simp only [derivative_xsub_pow, derivative_C_mul]
    simp only [Nat.cast_zero, zero_add, Nat.cast_one, map_one, map_zero, map_add, map_sub,
      map_mul, map_ofNat, pow_zero, pow_one, mul_one, Nat.sub_self]
    ring
  · simp only [derivative_xsub_pow, derivative_C_mul, Nat.add_sub_cancel]
    simp only [Nat.cast_add, Nat.cast_one, map_one, map_add, map_sub, map_mul,
      map_ofNat, map_natCast, pow_succ]
    generalize (X - 1 : ℝ[X]) ^ m = w
    ring_nf


/-- Linearity of the Jacobi operator over sums in the basis `(X-1)^ℓ`. -/
lemma jacobiOp_sum (α β : ℝ) (f : ℕ → ℝ) (m : ℕ) :
    (1 - X ^ 2) * derivative (derivative (∑ ℓ ∈ Finset.range m, C (f ℓ) * (X - 1 : ℝ[X]) ^ ℓ)) +
        (C (β - α) - C (α + β + 2) * X) *
          derivative (∑ ℓ ∈ Finset.range m, C (f ℓ) * (X - 1 : ℝ[X]) ^ ℓ) =
      ∑ ℓ ∈ Finset.range m, C (f ℓ) *
        ((1 - X ^ 2) * derivative (derivative ((X - 1 : ℝ[X]) ^ ℓ)) +
          (C (β - α) - C (α + β + 2) * X) * derivative ((X - 1 : ℝ[X]) ^ ℓ)) := by
  simp only [derivative_sum, derivative_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  ring

/-- **Jacobi differential equation** (DLMF 18.8.1, `P_n^{(α,β)}`), as a polynomial identity,
for arbitrary real `α β`. -/
theorem jacobi_ode (α β : ℝ) (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (jacobi α β n)) +
        (C (β - α) - C (α + β + 2) * X) * derivative (jacobi α β n) +
      C ((n : ℝ) * (n + α + β + 1)) * jacobi α β n = 0 := by
  unfold jacobi
  rw [jacobiOp_sum, Finset.mul_sum]
  simp only [jacobiOp_pow]
  have h : ∀ ℓ : ℕ, C (jacobiCoeff α β n ℓ) *
      (-C ((ℓ : ℝ) * (ℓ + α + β + 1)) * (X - 1 : ℝ[X]) ^ ℓ -
        C (2 * (ℓ : ℝ) * (ℓ + α)) * (X - 1) ^ (ℓ - 1)) +
      C ((n : ℝ) * (n + α + β + 1)) * (C (jacobiCoeff α β n ℓ) * (X - 1 : ℝ[X]) ^ ℓ) =
      C (jacobiCoeff α β n ℓ * (((n : ℝ) - ℓ) * ((n : ℝ) + ℓ + α + β + 1))) * (X - 1) ^ ℓ -
        C (jacobiCoeff α β n ℓ * (2 * (ℓ : ℝ) * (ℓ + α))) * (X - 1) ^ (ℓ - 1) := by
    intro ℓ
    simp only [map_mul, map_add, map_sub, map_natCast, map_ofNat, map_one]
    ring
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun ℓ _ => h ℓ), Finset.sum_sub_distrib, Finset.sum_range_succ,
    Finset.sum_range_succ']
  simp only [Nat.cast_zero, sub_self, zero_mul, map_zero, mul_zero, add_zero, 
    Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  rw [sub_eq_zero]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hlt : ℓ < n := Finset.mem_range.mp hℓ
  have := jacobiCoeff_succ α β n ℓ hlt
  congr 2
  linarith


/-- Self-adjoint (Sturm–Liouville) form of the Jacobi equation (DLMF 18.8.1 with the weight
`(1-x)^α (1+x)^β`, cf. DLMF 18.3.1), for natural `α β`. -/
theorem jacobi_sturmLiouville (a b n : ℕ) :
    derivative ((1 - X : ℝ[X]) ^ (a + 1) * (1 + X) ^ (b + 1) * derivative (jacobi (a : ℝ) (b : ℝ) n)) =
      - C ((n : ℝ) * (n + a + b + 1)) * (1 - X) ^ a * (1 + X) ^ b * jacobi (a : ℝ) (b : ℝ) n := by
  have ode := jacobi_ode (a : ℝ) (b : ℝ) n
  have h1 : derivative ((1 - X : ℝ[X]) ^ (a + 1)) = - C ((a : ℝ) + 1) * (1 - X) ^ a := by
    simp [derivative_pow]
    ring
  have h2 : derivative ((1 + X : ℝ[X]) ^ (b + 1)) = C ((b : ℝ) + 1) * (1 + X) ^ b := by
    simp [derivative_pow]
  rw [derivative_mul, derivative_mul, h1, h2]
  simp only [map_add, map_sub, map_mul, map_natCast, map_one, map_ofNat] at ode ⊢
  rw [pow_succ (1 - X : ℝ[X]), pow_succ (1 + X : ℝ[X])]
  generalize (1 - X : ℝ[X]) ^ a = p
  generalize (1 + X : ℝ[X]) ^ b = q
  linear_combination (p * q) * ode


/-- The Sturm–Liouville form of the Jacobi equation holds for all natural `a b m`. -/
theorem jacobiSL_all (a b m : ℕ) : JacobiSL a b m :=
  by
  unfold JacobiSL jacobiSLCoeff jacobiWeight
  rw [jacobi_sturmLiouville]
  ring


/-- Reflection of the rising factorial: `(x)_k = (-1)^k (1-k-x)_k`. -/
lemma poch_reflect (k : ℕ) (x : ℝ) :
    (ascPochhammer ℝ k).eval x = (-1) ^ k * (ascPochhammer ℝ k).eval (1 - k - x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, poch_succ_left_eval k (1 - ((k + 1 : ℕ) : ℝ) - x), ih]
    have : 1 - ((k + 1 : ℕ) : ℝ) - x + 1 = 1 - k - x := by push_cast; ring
    rw [this]
    push_cast
    ring

/-- Value at `-1` (DLMF 18.6.1). -/
theorem jacobi_eval_neg_one (α β : ℝ) (n : ℕ) :
    (jacobi α β n).eval (-1) =
      (-1) ^ n * (ascPochhammer ℝ n).eval (β + 1) / (n.factorial : ℝ) := by
  induction n generalizing α β with
  | zero => simp [jacobi_zero]
  | succ n ih =>
    by_cases h : ((n + 1 : ℕ) : ℝ) + α + β + 1 = 0
    · rw [jacobi_eval, Finset.sum_range_succ']
      have hz : ∀ ℓ : ℕ, jacobiCoeff α β (n + 1) (ℓ + 1) = 0 := by
        intro ℓ
        unfold jacobiCoeff
        rw [poch_succ_left_eval ℓ, h]
        simp
      simp only [hz, zero_mul, Finset.sum_const_zero, zero_add]
      simp only [jacobiCoeff, Nat.factorial_zero, Nat.cast_zero, pow_zero, mul_one,
        ascPochhammer_zero, eval_one, one_mul, Nat.sub_zero, Nat.cast_one, add_zero]
      have hb : 1 - ((n + 1 : ℕ) : ℝ) - (α + 1) = β + 1 := by push_cast at h ⊢; linarith
      rw [poch_reflect (n + 1) (α + 1), hb]
    · have e := congrArg (Polynomial.eval (-1)) (jacobi_ode α β (n + 1))
      simp only [derivative_jacobi, eval_add, eval_mul, eval_sub, eval_pow, eval_one, eval_X,
        eval_C, eval_zero, derivative_C_mul] at e
      rw [ih (α + 1) (β + 1)] at e
      rw [poch_succ_left_eval n (β + 1), Nat.factorial_succ]
      have hn : ((n : ℝ) + 1 + α + β + 1) ≠ 0 := by
        intro h'; apply h; push_cast; linarith
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      generalize (jacobi α β (n + 1)).eval (-1) = V at e ⊢
      generalize (ascPochhammer ℝ n).eval (β + 1 + 1) = Pn at e ⊢
      push_cast at e ⊢
      norm_num at e
      rw [eq_div_iff (by positivity)]
      apply mul_left_cancel₀ hn
      field_simp at e
      rw [pow_succ]
      linear_combination (1/2 : ℝ) * e


/-- Reflection formula (DLMF 18.6.1): `P_n^{(α,β)}(-x) = (-1)^n P_n^{(β,α)}(x)`. -/
theorem jacobi_comp_neg (α β : ℝ) (n : ℕ) :
    (jacobi α β n).comp (-X) = (-1) ^ n • jacobi β α n := by
  induction n generalizing α β with
  | zero => simp [jacobi_zero]
  | succ n ih =>
    have hd : derivative ((jacobi α β (n + 1)).comp (-X)) =
        derivative ((-1) ^ (n + 1) • jacobi β α (n + 1)) := by
      rw [derivative_comp, derivative_jacobi, derivative_smul, derivative_jacobi]
      simp only [derivative_X, mul_comp, C_comp, ih, 
        map_neg]
      have : ((n : ℝ) + β + α + 2) = n + α + β + 2 := by ring
      rw [this]
      ring
    have hz : derivative ((jacobi α β (n + 1)).comp (-X) -
        (-1) ^ (n + 1) • jacobi β α (n + 1)) = 0 := by
      rw [derivative_sub, hd, sub_self]
    have hc := eq_C_of_derivative_eq_zero hz
    have h1 : ((jacobi α β (n + 1)).comp (-X) - (-1) ^ (n + 1) • jacobi β α (n + 1)).eval 1 = 0 := by
      simp only [eval_sub, eval_comp, eval_neg, eval_X, eval_smul, jacobi_eval_neg_one,
        jacobi_eval_one]
      ring
    have h2 : ((jacobi α β (n + 1)).comp (-X) - (-1) ^ (n + 1) • jacobi β α (n + 1)) = 0 := by
      generalize (jacobi α β (n + 1)).comp (-X) -
        (-1) ^ (n + 1) • jacobi β α (n + 1) = d at hc h1 ⊢
      have h3 := congrArg (Polynomial.eval 1) hc
      rw [h1, eval_C] at h3
      rw [hc, ← h3]
      simp
    exact sub_eq_zero.mp h2


/-- info: 'FormalResearch.Special.jacobi_eval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_eval_one

/-- info: 'FormalResearch.Special.jacobi_eval_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_eval_neg_one

/-- info: 'FormalResearch.Special.derivative_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms derivative_jacobi

/-- info: 'FormalResearch.Special.jacobi_ode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_ode

/-- info: 'FormalResearch.Special.jacobi_sturmLiouville' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_sturmLiouville

/-- info: 'FormalResearch.Special.jacobiSL_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobiSL_all

/-- info: 'FormalResearch.Special.jacobi_comp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_comp_neg

end FormalResearch.Special
