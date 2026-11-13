module

public import FormalResearch.Special.JacobiZeros

/-!
# Jacobi polynomials: Christoffel–Darboux and the hypergeometric form

For natural parameters `a b : ℕ`, write `P_k = jacobi a b k`, `h_k = jacNorm a b k` and let
`x P_k = α_k P_{k+1} + β_k P_k + γ_k P_{k-1}` be the three-term recurrence (`jacAlpha`, `jacBeta`,
`jacGamma`, repackaging `jacA0, jacB0` and `jacA, jacB, jacC` of `JacobiRec`, with `γ_0 = 0`).

## Main results

* `jacobi_X_mul_all`: the recurrence in uniform indexing, for all `k`;
* `jacAlpha_mul_jacNorm`: `α_k h_{k+1} = γ_{k+1} h_k`;
* `jacAlpha_eq_coeff_div`: `α_k = k_k / k_{k+1}` for the leading coefficients `k_k` of `P_k`;
* `jacobi_christoffel_darboux`: the Christoffel–Darboux formula (DLMF 18.2.12)
  `(x - y) ∑_{k ≤ n} P_k(x) P_k(y) / h_k = (α_n / h_n) (P_{n+1}(x) P_n(y) - P_n(x) P_{n+1}(y))`,
  and `jacobi_christoffel_darboux_coeff` with `α_n / h_n = k_n / (k_{n+1} h_n)`;
* `jacobi_christoffel_darboux_confluent`: the confluent form (DLMF 18.2.13)
  `∑_{k ≤ n} P_k(x)² / h_k = (α_n / h_n) (P_{n+1}'(x) P_n(x) - P_n'(x) P_{n+1}(x))`;
* `hypergeometric_eq_jacobi`: the terminating `₂F₁` in the normalisation of
  `bernstein_hahn_jacobi` (`FormalResearch/Racah/P2HahnBeta.lean`) is a multiple of the Jacobi
  polynomial (DLMF 18.5.7 rewritten):
  `∑_{k=0}^n (-n)_k (n+α+β+1)_k / ((α+1)_k k!) t^k = n!/(α+1)_n · P_n^{(α,β)}(1 - 2t)`.
-/

@[expose] public section

namespace FormalResearch.Special

open Polynomial

/-! ### Abstract Christoffel–Darboux -/

/-- Christoffel–Darboux for any sequence `P_n` obeying a three-term recurrence
`x P_n = α_n P_{n+1} + β_n P_n + γ_n P_{n-1}` with `P_0 = 1`, `γ_0 = 0`, and weights `h_n ≠ 0` with
`α_n h_{n+1} = γ_{n+1} h_n`. -/
theorem cd_abstract (P : ℕ → ℝ → ℝ) (α β γ h : ℕ → ℝ)
    (hrec : ∀ n x, x * P n x = α n * P (n + 1) x + β n * P n x + γ n * P (n - 1) x)
    (hγ0 : γ 0 = 0) (hh : ∀ n, h n ≠ 0)
    (hα : ∀ n, α n * h (n + 1) = γ (n + 1) * h n) (hP0 : ∀ x, P 0 x = 1) (x y : ℝ) (n : ℕ) :
    (x - y) * ∑ k ∈ Finset.range (n + 1), P k x * P k y / h k =
      α n / h n * (P (n + 1) x * P n y - P n x * P (n + 1) y) := by
  induction n with
  | zero =>
    have hx := hrec 0 x
    have hy := hrec 0 y
    simp only [hγ0, add_zero, hP0, mul_one] at hx hy
    simp only [zero_add, Finset.sum_range_one, hP0, mul_one, one_mul]
    have := hh 0
    field_simp
    linear_combination hx - hy
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hx := hrec (n + 1) x
    have hy := hrec (n + 1) y
    simp only [Nat.add_sub_cancel] at hx hy
    have e : α (n + 1) * (P (n + 2) x * P (n + 1) y - P (n + 1) x * P (n + 2) y) =
        (x - y) * (P (n + 1) x * P (n + 1) y) -
          γ (n + 1) * (P n x * P (n + 1) y - P (n + 1) x * P n y) := by
      linear_combination P (n + 1) x * hy - P (n + 1) y * hx
    have hg : γ (n + 1) / h (n + 1) = α n / h n := by
      have := hα n
      have := hh n; have := hh (n + 1)
      field_simp
      linarith
    have e2 : α (n + 1) / h (n + 1) * (P (n + 1 + 1) x * P (n + 1) y - P (n + 1) x * P (n + 1 + 1) y)
        = ((x - y) * (P (n + 1) x * P (n + 1) y)) / h (n + 1)
          - γ (n + 1) / h (n + 1) * (P n x * P (n + 1) y - P (n + 1) x * P n y) := by
      rw [div_mul_eq_mul_div, e]; ring
    rw [e2, hg]
    ring

/-! ### The Jacobi recurrence in uniform indexing -/

/-- `α_k`: coefficient of `P_{k+1}` in `x P_k`. -/
noncomputable def jacAlpha (α β : ℝ) : ℕ → ℝ
  | 0 => jacA0 α β
  | k + 1 => jacA α β k

/-- `β_k`: coefficient of `P_k` in `x P_k`. -/
noncomputable def jacBeta (α β : ℝ) : ℕ → ℝ
  | 0 => jacB0 α β
  | k + 1 => jacB α β k

/-- `γ_k`: coefficient of `P_{k-1}` in `x P_k` (`γ_0 = 0`). -/
noncomputable def jacGamma (α β : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => jacC α β k

/-- The three-term recurrence `x P_k = α_k P_{k+1} + β_k P_k + γ_k P_{k-1}` for all `k`
(polynomial form). -/
theorem jacobi_X_mul_all_poly (a b k : ℕ) :
    X * jacobi (a : ℝ) (b : ℝ) k =
      C (jacAlpha (a : ℝ) (b : ℝ) k) * jacobi (a : ℝ) (b : ℝ) (k + 1) +
        C (jacBeta (a : ℝ) (b : ℝ) k) * jacobi (a : ℝ) (b : ℝ) k +
        C (jacGamma (a : ℝ) (b : ℝ) k) * jacobi (a : ℝ) (b : ℝ) (k - 1) := by
  have hs : (0 : ℝ) < (a : ℝ) + b + 2 := by positivity
  cases k with
  | zero => simpa [jacAlpha, jacBeta, jacGamma] using jacobi_X_mul_zero _ _ hs
  | succ k => simpa [jacAlpha, jacBeta, jacGamma] using jacobi_X_mul_succ _ _ hs k

/-- The three-term recurrence for all `k`, evaluated. -/
theorem jacobi_X_mul_all (a b k : ℕ) (x : ℝ) :
    x * (jacobi (a : ℝ) (b : ℝ) k).eval x =
      jacAlpha (a : ℝ) (b : ℝ) k * (jacobi (a : ℝ) (b : ℝ) (k + 1)).eval x +
        jacBeta (a : ℝ) (b : ℝ) k * (jacobi (a : ℝ) (b : ℝ) k).eval x +
        jacGamma (a : ℝ) (b : ℝ) k * (jacobi (a : ℝ) (b : ℝ) (k - 1)).eval x := by
  have := congrArg (Polynomial.eval x) (jacobi_X_mul_all_poly a b k)
  simpa only [eval_mul, eval_add, eval_X, eval_C] using this

lemma jacNorm_pos (a b n : ℕ) : 0 < jacNorm a b n := by
  unfold jacNorm; positivity

lemma jacAlpha_pos (a b k : ℕ) : 0 < jacAlpha (a : ℝ) (b : ℝ) k := by
  cases k with
  | zero => simp only [jacAlpha, jacA0]; positivity
  | succ k => simp only [jacAlpha, jacA]; positivity

/-- The norms satisfy `α_k h_{k+1} = γ_{k+1} h_k`. -/
theorem jacAlpha_mul_jacNorm (a b k : ℕ) :
    jacAlpha (a : ℝ) (b : ℝ) k * jacNorm a b (k + 1) =
      jacGamma (a : ℝ) (b : ℝ) (k + 1) * jacNorm a b k := by
  cases k with
  | zero =>
    have h := jacIP_step_zero a b
    rw [jacNorm_zero, jacNorm_one] at h
    simpa [jacAlpha, jacGamma] using h
  | succ k =>
    simpa [jacAlpha, jacGamma] using jacNorm_succ_succ a b k

/-- `α_k = k_k / k_{k+1}`, the ratio of leading coefficients of `P_k` and `P_{k+1}`. -/
theorem jacAlpha_eq_coeff_div (a b k : ℕ) :
    jacAlpha (a : ℝ) (b : ℝ) k =
      (jacobi (a : ℝ) (b : ℝ) k).coeff k / (jacobi (a : ℝ) (b : ℝ) (k + 1)).coeff (k + 1) := by
  have hne := jacobi_coeff_self_ne_zero (a : ℝ) (b : ℝ) (by positivity) (by positivity) (k + 1)
  rw [eq_div_iff hne]
  have h := congrArg (fun p => p.coeff (k + 1)) (jacobi_X_mul_all_poly a b k)
  simp only [coeff_X_mul, coeff_add, coeff_C_mul] at h
  have h1 : (jacobi (a : ℝ) (b : ℝ) k).coeff (k + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [jacobi_natDegree]; omega)
  have h2 : (jacobi (a : ℝ) (b : ℝ) (k - 1)).coeff (k + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [jacobi_natDegree]; omega)
  rw [h1, h2] at h
  linarith

/-! ### Christoffel–Darboux -/

/-- **Christoffel–Darboux formula** (DLMF 18.2.12) for Jacobi polynomials, natural parameters:
`(x - y) ∑_{k=0}^n P_k(x) P_k(y) / h_k = (α_n / h_n) (P_{n+1}(x) P_n(y) - P_n(x) P_{n+1}(y))`,
with `h_k = ∫ w P_k²` (`jacNorm`) and `α_n` the coefficient of `P_{n+1}` in `x P_n`. -/
theorem jacobi_christoffel_darboux (a b n : ℕ) (x y : ℝ) :
    (x - y) * ∑ k ∈ Finset.range (n + 1),
        (jacobi (a : ℝ) (b : ℝ) k).eval x * (jacobi (a : ℝ) (b : ℝ) k).eval y / jacNorm a b k =
      jacAlpha (a : ℝ) (b : ℝ) n / jacNorm a b n *
        ((jacobi (a : ℝ) (b : ℝ) (n + 1)).eval x * (jacobi (a : ℝ) (b : ℝ) n).eval y -
          (jacobi (a : ℝ) (b : ℝ) n).eval x * (jacobi (a : ℝ) (b : ℝ) (n + 1)).eval y) :=
  cd_abstract (fun k z => (jacobi (a : ℝ) (b : ℝ) k).eval z) (jacAlpha (a : ℝ) (b : ℝ))
    (jacBeta (a : ℝ) (b : ℝ)) (jacGamma (a : ℝ) (b : ℝ)) (jacNorm a b)
    (fun k z => jacobi_X_mul_all a b k z) rfl (fun k => (jacNorm_pos a b k).ne')
    (jacAlpha_mul_jacNorm a b) (fun z => by simp [jacobi_zero]) x y n

/-- Christoffel–Darboux in the form of DLMF 18.2.12, with the ratio of leading coefficients
`k_n / k_{n+1}` of `P_n`, `P_{n+1}`:
`(x - y) ∑_{k ≤ n} P_k(x) P_k(y)/h_k = k_n / (k_{n+1} h_n) (P_{n+1}(x) P_n(y) - P_n(x) P_{n+1}(y))`. -/
theorem jacobi_christoffel_darboux_coeff (a b n : ℕ) (x y : ℝ) :
    (x - y) * ∑ k ∈ Finset.range (n + 1),
        (jacobi (a : ℝ) (b : ℝ) k).eval x * (jacobi (a : ℝ) (b : ℝ) k).eval y / jacNorm a b k =
      (jacobi (a : ℝ) (b : ℝ) n).coeff n /
          ((jacobi (a : ℝ) (b : ℝ) (n + 1)).coeff (n + 1) * jacNorm a b n) *
        ((jacobi (a : ℝ) (b : ℝ) (n + 1)).eval x * (jacobi (a : ℝ) (b : ℝ) n).eval y -
          (jacobi (a : ℝ) (b : ℝ) n).eval x * (jacobi (a : ℝ) (b : ℝ) (n + 1)).eval y) := by
  rw [jacobi_christoffel_darboux, jacAlpha_eq_coeff_div, div_div]

/-- **Confluent Christoffel–Darboux formula** (DLMF 18.2.13):
`∑_{k=0}^n P_k(x)² / h_k = (α_n / h_n) (P_{n+1}'(x) P_n(x) - P_n'(x) P_{n+1}(x))`. -/
theorem jacobi_christoffel_darboux_confluent (a b n : ℕ) (y : ℝ) :
    ∑ k ∈ Finset.range (n + 1),
        ((jacobi (a : ℝ) (b : ℝ) k).eval y) ^ 2 / jacNorm a b k =
      jacAlpha (a : ℝ) (b : ℝ) n / jacNorm a b n *
        ((derivative (jacobi (a : ℝ) (b : ℝ) (n + 1))).eval y * (jacobi (a : ℝ) (b : ℝ) n).eval y -
          (derivative (jacobi (a : ℝ) (b : ℝ) n)).eval y *
            (jacobi (a : ℝ) (b : ℝ) (n + 1)).eval y) := by
  set L : ℝ[X] := (X - C y) * ∑ k ∈ Finset.range (n + 1),
    C ((jacobi (a : ℝ) (b : ℝ) k).eval y / jacNorm a b k) * jacobi (a : ℝ) (b : ℝ) k with hL
  set R : ℝ[X] := C (jacAlpha (a : ℝ) (b : ℝ) n / jacNorm a b n) *
    (C ((jacobi (a : ℝ) (b : ℝ) n).eval y) * jacobi (a : ℝ) (b : ℝ) (n + 1) -
      C ((jacobi (a : ℝ) (b : ℝ) (n + 1)).eval y) * jacobi (a : ℝ) (b : ℝ) n) with hR
  have hLR : L = R := by
    refine Polynomial.funext (fun x => ?_)
    have h := jacobi_christoffel_darboux a b n x y
    simp only [hL, hR, eval_mul, eval_sub, eval_X, eval_C, eval_finsetSum]
    rw [show ∑ k ∈ Finset.range (n + 1), (jacobi (a : ℝ) (b : ℝ) k).eval y /
        jacNorm a b k * (jacobi (a : ℝ) (b : ℝ) k).eval x =
      ∑ k ∈ Finset.range (n + 1), (jacobi (a : ℝ) (b : ℝ) k).eval x *
        (jacobi (a : ℝ) (b : ℝ) k).eval y / jacNorm a b k from
      Finset.sum_congr rfl (fun k _ => by ring), h]
    ring
  have hd := congrArg (fun p => (derivative p).eval y) hLR
  simp only [hL, hR, derivative_mul, derivative_sub, derivative_X, derivative_C, eval_add, eval_mul,
    eval_sub, eval_C, eval_X, eval_finsetSum, sub_self, zero_mul, add_zero,
    sub_zero, one_mul, zero_add] at hd
  rw [show ∑ k ∈ Finset.range (n + 1), ((jacobi (a : ℝ) (b : ℝ) k).eval y) ^ 2 / jacNorm a b k =
      ∑ k ∈ Finset.range (n + 1), (jacobi (a : ℝ) (b : ℝ) k).eval y / jacNorm a b k *
        (jacobi (a : ℝ) (b : ℝ) k).eval y from Finset.sum_congr rfl (fun k _ => by ring)]
  linear_combination hd

/-! ### The hypergeometric form -/

lemma ascPoch_add_eval (c : ℝ) (k m : ℕ) :
    (ascPochhammer ℝ (k + m)).eval c =
      (ascPochhammer ℝ k).eval c * (ascPochhammer ℝ m).eval (c + k) := by
  rw [← ascPochhammer_mul ℝ k m]
  simp [eval_comp]

lemma ascPoch_one_eval (m : ℕ) : (ascPochhammer ℝ m).eval 1 = (m.factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ]
    push_cast; ring

/-- `(-n)_k (n-k)! = (-1)^k n!` for `k ≤ n`. -/
lemma poch_neg_nat_mul_factorial (n k : ℕ) (hk : k ≤ n) :
    (ascPochhammer ℝ k).eval (-(n : ℝ)) * ((n - k).factorial : ℝ) = (-1) ^ k * (n.factorial : ℝ) := by
  have h1 := ascPoch_add_eval 1 (n - k) k
  rw [Nat.sub_add_cancel hk, ascPoch_one_eval, ascPoch_one_eval] at h1
  have h2 := poch_reflect k (-(n : ℝ))
  have h3 : 1 - (k : ℝ) - -(n : ℝ) = 1 + ((n - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk]; ring
  rw [h3] at h2
  rw [h2, h1]; ring

/-- **The terminating `₂F₁` as a Jacobi polynomial** (DLMF 18.5.7 rewritten): for natural `α β n`,
`∑_{k=0}^n (-n)_k (n+α+β+1)_k / ((α+1)_k k!) t^k = n!/(α+1)_n · P_n^{(α,β)}(1 - 2t)`.
The left side is the right side of `FormalResearch.Racah.bernstein_hahn_jacobi`. -/
theorem hypergeometric_eq_jacobi (α β n : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range (n + 1),
        (ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1) /
          ((ascPochhammer ℝ k).eval ((α : ℝ) + 1) * (k.factorial : ℝ)) * t ^ k =
      (n.factorial : ℝ) / (ascPochhammer ℝ n).eval ((α : ℝ) + 1) *
        (jacobi (α : ℝ) (β : ℝ) n).eval (1 - 2 * t) := by
  rw [jacobi_eval, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hA : 0 < (ascPochhammer ℝ k).eval ((α : ℝ) + 1) := ascPochhammer_pos k _ (by positivity)
  have hB : 0 < (ascPochhammer ℝ (n - k)).eval ((α : ℝ) + k + 1) :=
    ascPochhammer_pos _ _ (by positivity)
  have hsplit := ascPoch_add_eval ((α : ℝ) + 1) k (n - k)
  rw [Nat.add_sub_cancel' hkn, show (α : ℝ) + 1 + k = α + k + 1 by ring] at hsplit
  have hQ := poch_neg_nat_mul_factorial n k hkn
  have hf : ((n - k).factorial : ℝ) ≠ 0 := by positivity
  have hk' : (k.factorial : ℝ) ≠ 0 := by positivity
  have hQ' : (ascPochhammer ℝ k).eval (-(n : ℝ)) =
      (-1) ^ k * (n.factorial : ℝ) / ((n - k).factorial : ℝ) := by
    rw [eq_div_iff hf]; exact hQ
  unfold jacobiCoeff
  rw [hsplit, hQ', show 1 - 2 * t - 1 = (-1) ^ 1 * 2 * t by ring]
  rw [show ((-1 : ℝ) ^ 1 * 2 * t) ^ k = (-1) ^ k * 2 ^ k * t ^ k by
    rw [pow_one, mul_pow, mul_pow, neg_pow]]
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp

/-- info: 'FormalResearch.Special.jacobi_christoffel_darboux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_christoffel_darboux

/-- info: 'FormalResearch.Special.jacobi_christoffel_darboux_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_christoffel_darboux_coeff

/-- info: 'FormalResearch.Special.jacobi_christoffel_darboux_confluent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_christoffel_darboux_confluent

/-- info: 'FormalResearch.Special.hypergeometric_eq_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hypergeometric_eq_jacobi

end FormalResearch.Special
