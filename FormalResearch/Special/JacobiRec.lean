module

public import FormalResearch.Special.JacobiDef

/-!
# Jacobi polynomials: the three-term recurrence

For the explicitly defined `jacobi α β n` (DLMF 18.5.7, `FormalResearch.Special.JacobiDef`) with
arbitrary real parameters `α β`, we prove the three-term recurrence DLMF 18.9.1 in denominator-free
form, valid for all `α β` including the exceptional parameters (`α + β + n ∈ ℤ_{≤ 0}`, ...):

  `2(n+2)(n+α+β+2)(2n+α+β+2) P_{n+2} = (2n+α+β+3) ((2n+α+β+4)(2n+α+β+2) x + α²-β²) P_{n+1}
      - 2(n+α+1)(n+β+1)(2n+α+β+4) P_n`,

and the same recurrence normalised (`x P_{n+1} = a_n P_{n+2} + b_n P_{n+1} + c_n P_n`, DLMF 18.9.1
divided through) under `0 < α + β + 2`, which makes every denominator positive. The proof compares
the coefficients of `(x-1)^ℓ` (basis of DLMF 18.5.7) term by term: each coefficient identity is
a rational-function identity between four Pochhammer/factorial products, split into the
interior range and the boundary indices `ℓ = 0, 1, n+1, n+2`.

## Main results

* `jacobi_three_term`: DLMF 18.9.1, denominator-free form (all real `α β`, all `n`).
* `jacobi_one`: `P_1^{(α,β)} = (α-β)/2 + (α+β+2)/2 · x`, DLMF 18.5.7 at `n = 1`.
* `jacobi_X_mul_succ`, `jacobi_X_mul_zero`: the normalised recurrence with coefficients `jacA`,
  `jacB`, `jacC` (and `jacA0`, `jacB0` for `P_0`).
-/

@[expose] public section

namespace FormalResearch.Special

open Polynomial

/-- Pochhammer step on the right: `(a)_{k+1} = (a)_k (a+k)`. -/
lemma jacRec_poch_r (a : ℝ) (k : ℕ) :
    (ascPochhammer ℝ (k + 1)).eval a = (ascPochhammer ℝ k).eval a * (a + k) :=
  ascPochhammer_succ_eval k a

/-- Pochhammer step on the left: `(a)_{k+1} = a (a+1)_k`. -/
lemma jacRec_poch_l (a : ℝ) (k : ℕ) :
    (ascPochhammer ℝ (k + 1)).eval a = a * (ascPochhammer ℝ k).eval (a + 1) := by
  rw [ascPochhammer_succ_left]; simp [eval_comp]

/-- The coefficient of `(x-1)^ℓ` in `P_m^{(α,β)}`, extended by `0` for `ℓ > m`. -/
noncomputable def jacRecCoeff (α β : ℝ) (m ℓ : ℕ) : ℝ :=
  if ℓ ≤ m then jacobiCoeff α β m ℓ else 0

/-- `jacobiCoeff` at `m = ℓ + d`, with the subtraction `m - ℓ = d` resolved. -/
lemma jacRec_coeff_add (α β : ℝ) (m ℓ d : ℕ) (h : m = ℓ + d) :
    jacobiCoeff α β m ℓ = (ascPochhammer ℝ ℓ).eval ((ℓ : ℝ) + d + α + β + 1) *
      (ascPochhammer ℝ d).eval (α + ℓ + 1) / ((ℓ.factorial : ℝ) * (d.factorial : ℝ) * 2 ^ ℓ) := by
  subst h
  simp only [jacobiCoeff, Nat.add_sub_cancel_left]
  push_cast
  rfl

/-- Factored form of the coefficient `[ℓ = i+2, n+2 = i+2+k+2]`, as `Q R` times a rational factor. -/
lemma jacRec_jcA (α β : ℝ) (i k : ℕ) :
    jacobiCoeff α β (i+2+k+2) (i+2) =
      (ascPochhammer ℝ i).eval ((i:ℝ)+k+α+β+5) * (ascPochhammer ℝ k).eval (α+i+3) *
        (((i:ℝ)+k+α+β+5+i) * ((i:ℝ)+k+α+β+5+i+1)) * ((α+i+3+k) * (α+i+3+k+1)) /
      (((i+2).factorial : ℝ) * ((k+2).factorial : ℝ) * 2 ^ (i+2)) := by
  rw [jacRec_coeff_add α β (i+2+k+2) (i+2) (k+2) (by omega), jacRec_poch_r _ (i+1), jacRec_poch_r _ i,
    jacRec_poch_r (α + ((i+2:ℕ):ℝ) + 1) (k+1), jacRec_poch_r _ k]
  have e1 : ((i+2:ℕ):ℝ) + ((k+2:ℕ):ℝ) + α + β + 1 = (i:ℝ)+k+α+β+5 := by push_cast; ring
  have e2 : α + ((i+2:ℕ):ℝ) + 1 = α+i+3 := by push_cast; ring
  rw [e1, e2]
  push_cast
  ring

/-- Factored form of the coefficient `[ℓ = i+2, m = i+2+k+1]`. -/
lemma jacRec_jcB (α β : ℝ) (i k : ℕ) :
    jacobiCoeff α β (i+2+k+1) (i+2) =
      ((i:ℝ)+k+α+β+4) * (ascPochhammer ℝ i).eval ((i:ℝ)+k+α+β+5) * ((i:ℝ)+k+α+β+5+i) *
        ((ascPochhammer ℝ k).eval (α+i+3) * (α+i+3+k)) /
      (((i+2).factorial : ℝ) * ((k+1).factorial : ℝ) * 2 ^ (i+2)) := by
  rw [jacRec_coeff_add α β (i+2+k+1) (i+2) (k+1) (by omega), jacRec_poch_r (α + ((i+2:ℕ):ℝ) + 1) k]
  have e1 : ((i+2:ℕ):ℝ) + ((k+1:ℕ):ℝ) + α + β + 1 = (i:ℝ)+k+α+β+4 := by push_cast; ring
  have e2 : α + ((i+2:ℕ):ℝ) + 1 = α+i+3 := by push_cast; ring
  have e3 : (i:ℝ)+k+α+β+4+1 = (i:ℝ)+k+α+β+5 := by ring
  rw [e1, e2, jacRec_poch_l ((i:ℝ)+k+α+β+4) (i+1), jacRec_poch_r _ i, e3]
  ring

/-- Factored form of the coefficient `[ℓ = i+1, m = i+2+k+1]`. -/
lemma jacRec_jcC (α β : ℝ) (i k : ℕ) :
    jacobiCoeff α β (i+2+k+1) (i+1) =
      ((i:ℝ)+k+α+β+4) * (ascPochhammer ℝ i).eval ((i:ℝ)+k+α+β+5) *
        ((α+i+2) * ((ascPochhammer ℝ k).eval (α+i+3) * (α+i+3+k))) /
      (((i+1).factorial : ℝ) * ((k+2).factorial : ℝ) * 2 ^ (i+1)) := by
  rw [jacRec_coeff_add α β (i+2+k+1) (i+1) (k+2) (by omega)]
  have e1 : ((i+1:ℕ):ℝ) + ((k+2:ℕ):ℝ) + α + β + 1 = (i:ℝ)+k+α+β+4 := by push_cast; ring
  have e2 : α + ((i+1:ℕ):ℝ) + 1 = α+i+2 := by push_cast; ring
  have e3 : (i:ℝ)+k+α+β+4+1 = (i:ℝ)+k+α+β+5 := by ring
  have e4 : α+i+2+1 = α+i+3 := by ring
  rw [e1, e2, jacRec_poch_l ((i:ℝ)+k+α+β+4) i, jacRec_poch_l (α+i+2) (k+1), jacRec_poch_r _ k, e3, e4]

/-- Factored form of the coefficient `[ℓ = i+2, m = i+2+k]`. -/
lemma jacRec_jcD (α β : ℝ) (i k : ℕ) :
    jacobiCoeff α β (i+2+k) (i+2) =
      (((i:ℝ)+k+α+β+3) * ((i:ℝ)+k+α+β+4)) * (ascPochhammer ℝ i).eval ((i:ℝ)+k+α+β+5) *
        (ascPochhammer ℝ k).eval (α+i+3) /
      (((i+2).factorial : ℝ) * (k.factorial : ℝ) * 2 ^ (i+2)) := by
  rw [jacRec_coeff_add α β (i+2+k) (i+2) k (by omega)]
  have e1 : ((i+2:ℕ):ℝ) + ((k:ℕ):ℝ) + α + β + 1 = (i:ℝ)+k+α+β+3 := by push_cast; ring
  have e2 : α + ((i+2:ℕ):ℝ) + 1 = α+i+3 := by push_cast; ring
  have e3 : (i:ℝ)+k+α+β+4+1 = (i:ℝ)+k+α+β+5 := by ring
  have e4 : (i:ℝ)+k+α+β+3+1 = (i:ℝ)+k+α+β+4 := by ring
  rw [e1, e2, jacRec_poch_l ((i:ℝ)+k+α+β+3) (i+1), jacRec_poch_l _ i, e4, e3]
  ring

/-- Coefficient identity of the recurrence for `(x-1)^{i+2}` in the interior range `i+2 ≤ n`. -/
lemma jacRec_coefInt (α β : ℝ) (i k : ℕ) :
    2*(((i+2+k:ℕ):ℝ)+2)*(((i+2+k:ℕ):ℝ)+α+β+2)*(2*((i+2+k:ℕ):ℝ)+α+β+2) *
        jacRecCoeff α β (i+2+k+2) (i+2)
      = (2*((i+2+k:ℕ):ℝ)+α+β+3) * ((2*((i+2+k:ℕ):ℝ)+α+β+4)*(2*((i+2+k:ℕ):ℝ)+α+β+2)
          * jacRecCoeff α β (i+2+k+1) (i+1)
        + ((2*((i+2+k:ℕ):ℝ)+α+β+4)*(2*((i+2+k:ℕ):ℝ)+α+β+2) + (α^2-β^2))
          * jacRecCoeff α β (i+2+k+1) (i+2))
        - 2*(((i+2+k:ℕ):ℝ)+α+1)*(((i+2+k:ℕ):ℝ)+β+1)*(2*((i+2+k:ℕ):ℝ)+α+β+4)
          * jacRecCoeff α β (i+2+k) (i+2) := by
  have h1 : i + 2 ≤ i + 2 + k + 2 := by omega
  have h2 : i + 1 ≤ i + 2 + k + 1 := by omega
  have h3 : i + 2 ≤ i + 2 + k + 1 := by omega
  have h4 : i + 2 ≤ i + 2 + k := by omega
  simp only [jacRecCoeff, h1, h2, h3, h4, ite_true]
  rw [jacRec_jcA, jacRec_jcB, jacRec_jcC, jacRec_jcD]
  simp only [Nat.factorial_succ]
  have hi : (i.factorial : ℝ) ≠ 0 := by positivity
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Coefficient identity of the recurrence for `(x-1)^{n+1}`, `n = i+1`. -/
lemma jacRec_coefT1 (α β : ℝ) (i : ℕ) :
    2*(((i+1:ℕ):ℝ)+2)*(((i+1:ℕ):ℝ)+α+β+2)*(2*((i+1:ℕ):ℝ)+α+β+2) *
        jacRecCoeff α β (i+1+2) (i+2)
      = (2*((i+1:ℕ):ℝ)+α+β+3) * ((2*((i+1:ℕ):ℝ)+α+β+4)*(2*((i+1:ℕ):ℝ)+α+β+2)
          * jacRecCoeff α β (i+1+1) (i+1)
        + ((2*((i+1:ℕ):ℝ)+α+β+4)*(2*((i+1:ℕ):ℝ)+α+β+2) + (α^2-β^2))
          * jacRecCoeff α β (i+1+1) (i+2))
        - 2*(((i+1:ℕ):ℝ)+α+1)*(((i+1:ℕ):ℝ)+β+1)*(2*((i+1:ℕ):ℝ)+α+β+4)
          * jacRecCoeff α β (i+1) (i+2) := by
  have h1 : i + 2 ≤ i + 1 + 2 := by omega
  have h2 : i + 1 ≤ i + 1 + 1 := by omega
  have h3 : i + 2 ≤ i + 1 + 1 := by omega
  have h4 : ¬ (i + 2 ≤ i + 1) := by omega
  simp only [jacRecCoeff, h1, h2, h3, h4, ite_true, ite_false]
  rw [jacRec_coeff_add α β (i+1+2) (i+2) 1 (by omega), jacRec_coeff_add α β (i+1+1) (i+1) 1 (by omega),
    jacRec_coeff_add α β (i+1+1) (i+2) 0 (by omega)]
  have e1 : ((i+2:ℕ):ℝ) + ((1:ℕ):ℝ) + α + β + 1 = (i:ℝ)+α+β+4 := by push_cast; ring
  have e2 : ((i+1:ℕ):ℝ) + ((1:ℕ):ℝ) + α + β + 1 = (i:ℝ)+α+β+3 := by push_cast; ring
  have e3 : ((i+2:ℕ):ℝ) + ((0:ℕ):ℝ) + α + β + 1 = (i:ℝ)+α+β+3 := by push_cast; ring
  have e4 : (i:ℝ)+α+β+3+1 = (i:ℝ)+α+β+4 := by ring
  rw [e1, e2, e3, jacRec_poch_r _ (i+1), jacRec_poch_r _ i, jacRec_poch_l ((i:ℝ)+α+β+3) i, e4,
    jacRec_poch_l ((i:ℝ)+α+β+3) (i+1), jacRec_poch_r _ i, e4]
  simp only [ascPochhammer_one, eval_X, ascPochhammer_zero, eval_one, Nat.factorial_succ,
    Nat.factorial_zero]
  have hi : (i.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Coefficient identity of the recurrence for `(x-1)^{n+2}`, `n = i`. -/
lemma jacRec_coefT2 (α β : ℝ) (i : ℕ) :
    2*((i:ℝ)+2)*((i:ℝ)+α+β+2)*(2*(i:ℝ)+α+β+2) * jacRecCoeff α β (i+2) (i+2)
      = (2*(i:ℝ)+α+β+3) * ((2*(i:ℝ)+α+β+4)*(2*(i:ℝ)+α+β+2)
          * jacRecCoeff α β (i+1) (i+1)
        + ((2*(i:ℝ)+α+β+4)*(2*(i:ℝ)+α+β+2) + (α^2-β^2))
          * jacRecCoeff α β (i+1) (i+2))
        - 2*((i:ℝ)+α+1)*((i:ℝ)+β+1)*(2*(i:ℝ)+α+β+4)
          * jacRecCoeff α β i (i+2) := by
  have h1 : i + 2 ≤ i + 2 := by omega
  have h2 : i + 1 ≤ i + 1 := by omega
  have h3 : ¬ (i + 2 ≤ i + 1) := by omega
  have h4 : ¬ (i + 2 ≤ i) := by omega
  simp only [jacRecCoeff, h1, h2, h3, h4, ite_true, ite_false]
  rw [jacRec_coeff_add α β (i+2) (i+2) 0 (by omega), jacRec_coeff_add α β (i+1) (i+1) 0 (by omega)]
  have e1 : ((i+2:ℕ):ℝ) + ((0:ℕ):ℝ) + α + β + 1 = (i:ℝ)+α+β+3 := by push_cast; ring
  have e2 : ((i+1:ℕ):ℝ) + ((0:ℕ):ℝ) + α + β + 1 = (i:ℝ)+α+β+2 := by push_cast; ring
  have e3 : (i:ℝ)+α+β+2+1 = (i:ℝ)+α+β+3 := by ring
  rw [e1, e2, jacRec_poch_r _ (i+1), jacRec_poch_r _ i, jacRec_poch_l ((i:ℝ)+α+β+2) i, e3]
  simp only [ascPochhammer_zero, eval_one, Nat.factorial_succ, Nat.factorial_zero]
  have hi : (i.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Coefficient identity of the recurrence for `(x-1)^0`. -/
lemma jacRec_coef0 (α β : ℝ) (n : ℕ) :
    2*((n:ℝ)+2)*(n+α+β+2)*(2*n+α+β+2) * jacRecCoeff α β (n+2) 0
      = (2*n+α+β+3) * ((2*n+α+β+4)*(2*n+α+β+2) + (α^2-β^2)) * jacRecCoeff α β (n+1) 0
        - 2*(n+α+1)*(n+β+1)*(2*n+α+β+4) * jacRecCoeff α β n 0 := by
  simp only [jacRecCoeff, jacobiCoeff, Nat.zero_le, ite_true, Nat.sub_zero, Nat.factorial_zero,
    ascPochhammer_zero, eval_one, Nat.cast_zero, add_zero, pow_zero, Nat.cast_one, one_mul, mul_one]
  rw [jacRec_poch_r, jacRec_poch_r]
  simp only [Nat.factorial_succ]
  have hg : (n.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Coefficient identity of the recurrence for `(x-1)^1` when `n = m+1 ≥ 1`. -/
lemma jacRec_coefS1 (α β : ℝ) (m : ℕ) :
    2*(((m+1:ℕ):ℝ)+2)*(((m+1:ℕ):ℝ)+α+β+2)*(2*((m+1:ℕ):ℝ)+α+β+2) * jacRecCoeff α β (m+1+2) (0+1)
      = (2*((m+1:ℕ):ℝ)+α+β+3) * ((2*((m+1:ℕ):ℝ)+α+β+4)*(2*((m+1:ℕ):ℝ)+α+β+2)
          * jacRecCoeff α β (m+1+1) 0
        + ((2*((m+1:ℕ):ℝ)+α+β+4)*(2*((m+1:ℕ):ℝ)+α+β+2) + (α^2-β^2)) * jacRecCoeff α β (m+1+1) (0+1))
        - 2*(((m+1:ℕ):ℝ)+α+1)*(((m+1:ℕ):ℝ)+β+1)*(2*((m+1:ℕ):ℝ)+α+β+4) * jacRecCoeff α β (m+1) (0+1) := by
  have h1 : 0 + 1 ≤ m + 1 + 2 := by omega
  have h2 : 0 + 1 ≤ m + 1 + 1 := by omega
  have h3 : 0 + 1 ≤ m + 1 := by omega
  simp only [jacRecCoeff, h1, h2, h3, Nat.zero_le, ite_true, jacobiCoeff, zero_add, ascPochhammer_one, eval_X]
  simp
  rw [jacRec_poch_l (α + 1) (m + 1), jacRec_poch_r (α + 1 + 1) (m + 1), jacRec_poch_r (α + 1 + 1) m]
  simp only [Nat.factorial_succ]
  have hg : (m.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Coefficient identity of the recurrence for `(x-1)^1` when `n = 0`. -/
lemma jacRec_coefS0 (α β : ℝ) :
    2*(((0:ℕ):ℝ)+2)*(((0:ℕ):ℝ)+α+β+2)*(2*((0:ℕ):ℝ)+α+β+2) * jacRecCoeff α β (0+2) (0+1)
      = (2*((0:ℕ):ℝ)+α+β+3) * ((2*((0:ℕ):ℝ)+α+β+4)*(2*((0:ℕ):ℝ)+α+β+2)
          * jacRecCoeff α β (0+1) 0
        + ((2*((0:ℕ):ℝ)+α+β+4)*(2*((0:ℕ):ℝ)+α+β+2) + (α^2-β^2))
          * jacRecCoeff α β (0+1) (0+1))
        - 2*(((0:ℕ):ℝ)+α+1)*(((0:ℕ):ℝ)+β+1)*(2*((0:ℕ):ℝ)+α+β+4)
          * jacRecCoeff α β 0 (0+1) := by
  have h1 : 0 + 1 ≤ 0 + 2 := by omega
  have h2 : 0 ≤ 0 + 1 := by omega
  have h3 : 0 + 1 ≤ 0 + 1 := by omega
  have h4 : ¬ (0 + 1 ≤ 0) := by omega
  simp only [jacRecCoeff, h1, h2, h3, h4, ite_true, ite_false]
  rw [jacRec_coeff_add α β (0+2) (0+1) 1 (by omega), jacRec_coeff_add α β (0+1) 0 1 (by omega),
    jacRec_coeff_add α β (0+1) (0+1) 0 (by omega)]
  simp only [ascPochhammer_one, ascPochhammer_zero, eval_X, eval_one, Nat.factorial_succ,
    Nat.factorial_zero]
  push_cast
  simp only [zero_add, ascPochhammer_one, eval_X]
  ring

/-- Coefficient identity of the recurrence for `(x-1)^{j+1}`, all `n` and `j ≤ n+1`. -/
lemma jacRec_coefS (α β : ℝ) (n j : ℕ) (hj : j ≤ n + 1) :
    2*((n:ℝ)+2)*(n+α+β+2)*(2*n+α+β+2) * jacRecCoeff α β (n+2) (j+1)
      = (2*(n:ℝ)+α+β+3) * ((2*n+α+β+4)*(2*n+α+β+2) * jacRecCoeff α β (n+1) j
        + ((2*n+α+β+4)*(2*n+α+β+2) + (α^2-β^2)) * jacRecCoeff α β (n+1) (j+1))
        - 2*((n:ℝ)+α+1)*(n+β+1)*(2*n+α+β+4) * jacRecCoeff α β n (j+1) := by
  rcases j with _ | i
  · rcases n with _ | m
    · exact jacRec_coefS0 α β
    · exact jacRec_coefS1 α β m
  · by_cases h : i + 2 ≤ n
    · obtain ⟨k, rfl⟩ : ∃ k, n = i + 2 + k := ⟨n - (i+2), by omega⟩
      exact jacRec_coefInt α β i k
    · by_cases h' : n = i + 1
      · subst h'; exact jacRec_coefT1 α β i
      · have : n = i := by omega
        subst this; exact jacRec_coefT2 α β n


/-- Coefficient-sum bookkeeping for the recurrence, with abstract coefficient sequences. -/
lemma jacRec_assemble (A B E H G u : ℝ) (c2 c1 c0 : ℕ → ℝ) (n : ℕ)
    (h0 : A * c2 0 = B * (E + H) * c1 0 - G * c0 0)
    (hS : ∀ j, j < n + 2 →
      A * c2 (j+1) = B * (E * c1 j + (E + H) * c1 (j+1)) - G * c0 (j+1))
    (htop : c1 (n+2) = 0) :
    A * ∑ ℓ ∈ Finset.range (n+3), c2 ℓ * u ^ ℓ
      = B * ((E * (u + 1) + H) * ∑ ℓ ∈ Finset.range (n+3), c1 ℓ * u ^ ℓ)
        - G * ∑ ℓ ∈ Finset.range (n+3), c0 ℓ * u ^ ℓ := by
  have hterm : ∀ j ∈ Finset.range (n+2),
      A * (c2 (j+1) * u^(j+1)) = B * E * (c1 j * u^(j+1))
        + B * (E + H) * (c1 (j+1) * u^(j+1)) - G * (c0 (j+1) * u^(j+1)) := by
    intro j hj
    have := hS j (Finset.mem_range.1 hj)
    linear_combination u^(j+1) * this
  have F1 := Finset.sum_congr rfl hterm
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum] at F1
  have hP : ∀ c : ℕ → ℝ, ∑ ℓ ∈ Finset.range (n+3), c ℓ * u ^ ℓ
      = ∑ j ∈ Finset.range (n+2), c (j+1) * u^(j+1) + c 0 := by
    intro c
    rw [Finset.sum_range_succ' _ (n+2)]
    simp
  have hu : u * ∑ ℓ ∈ Finset.range (n+3), c1 ℓ * u ^ ℓ
      = ∑ j ∈ Finset.range (n+2), c1 j * u^(j+1) := by
    rw [Finset.sum_range_succ, htop]
    simp only [zero_mul, add_zero]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hP2 := hP c2
  have hP1 := hP c1
  have hP0 := hP c0
  rw [hP1] at hu
  rw [hP2, hP1, hP0]
  linear_combination F1 + h0 - B * E * hu

/-- `P_m` as a sum over any range `N ≥ m + 1`, using the zero-extended coefficients. -/
lemma jacRec_eval_ext (α β : ℝ) (m N : ℕ) (h : m + 1 ≤ N) (x : ℝ) :
    (jacobi α β m).eval x = ∑ ℓ ∈ Finset.range N, jacRecCoeff α β m ℓ * (x - 1) ^ ℓ := by
  rw [jacobi_eval]
  have h1 : ∑ ℓ ∈ Finset.range (m+1), jacobiCoeff α β m ℓ * (x - 1) ^ ℓ
      = ∑ ℓ ∈ Finset.range (m+1), jacRecCoeff α β m ℓ * (x - 1) ^ ℓ := by
    refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
    have : ℓ ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
    simp [jacRecCoeff, this]
  rw [h1]
  refine Finset.sum_subset (Finset.range_mono h) (fun ℓ hℓ hn => ?_)
  have : ¬ ℓ ≤ m := fun hle => hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
  simp [jacRecCoeff, this]

/-- DLMF 18.9.1 evaluated at a point `x`. -/
lemma jacRec_three_term_eval (α β : ℝ) (n : ℕ) (x : ℝ) :
    2*((n:ℝ)+2)*(n+α+β+2)*(2*n+α+β+2) * (jacobi α β (n+2)).eval x
      = (2*(n:ℝ)+α+β+3) * (((2*n+α+β+4)*(2*n+α+β+2) * x + (α^2-β^2))
          * (jacobi α β (n+1)).eval x)
        - 2*((n:ℝ)+α+1)*(n+β+1)*(2*n+α+β+4) * (jacobi α β n).eval x := by
  rw [jacRec_eval_ext α β (n+2) (n+3) (by omega), jacRec_eval_ext α β (n+1) (n+3) (by omega),
    jacRec_eval_ext α β n (n+3) (by omega)]
  have key := jacRec_assemble (2*((n:ℝ)+2)*(n+α+β+2)*(2*n+α+β+2)) (2*(n:ℝ)+α+β+3)
    ((2*n+α+β+4)*(2*n+α+β+2)) (α^2-β^2) (2*((n:ℝ)+α+1)*(n+β+1)*(2*n+α+β+4)) (x - 1)
    (jacRecCoeff α β (n+2)) (jacRecCoeff α β (n+1)) (jacRecCoeff α β n) n
    (jacRec_coef0 α β n) (fun j hj => jacRec_coefS α β n j (by omega))
    (by simp [jacRecCoeff])
  have hx : x - 1 + 1 = x := by ring
  rw [hx] at key
  exact key

/-- **DLMF 18.9.1** (three-term recurrence of Jacobi polynomials), denominator-free form, for
all real `α β` and all `n`:
`2(n+2)(n+α+β+2)(2n+α+β+2) P_{n+2} = (2n+α+β+3)((2n+α+β+4)(2n+α+β+2) x + α²-β²) P_{n+1}
  - 2(n+α+1)(n+β+1)(2n+α+β+4) P_n`. -/
theorem jacobi_three_term (α β : ℝ) (n : ℕ) :
    C (2*((n:ℝ)+2)*(n+α+β+2)*(2*n+α+β+2)) * jacobi α β (n+2)
      = C (2*(n:ℝ)+α+β+3) * (C ((2*n+α+β+4)*(2*n+α+β+2)) * X + C (α^2-β^2))
          * jacobi α β (n+1)
        - C (2*((n:ℝ)+α+1)*(n+β+1)*(2*n+α+β+4)) * jacobi α β n := by
  refine Polynomial.funext (fun x => ?_)
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_X]
  linear_combination jacRec_three_term_eval α β n x

/-- `P_1^{(α,β)}(x) = (α-β)/2 + (α+β+2)/2 · x` (DLMF 18.5.7 at `n = 1`). -/
theorem jacobi_one (α β : ℝ) :
    jacobi α β 1 = C ((α - β) / 2) + C ((α + β + 2) / 2) * X := by
  refine Polynomial.funext (fun x => ?_)
  rw [jacobi_eval]
  simp [Finset.sum_range_succ, jacobiCoeff]
  ring

/-- Coefficient `a` of the normalised recurrence: `x P_{n+1} = a P_{n+2} + b P_{n+1} + c P_n`. -/
noncomputable def jacA (α β : ℝ) (n : ℕ) : ℝ :=
  2*((n:ℝ)+2)*(n+α+β+2) / ((2*n+α+β+3)*(2*n+α+β+4))

/-- Coefficient `b` of the normalised recurrence: `x P_{n+1} = a P_{n+2} + b P_{n+1} + c P_n`. -/
noncomputable def jacB (α β : ℝ) (n : ℕ) : ℝ :=
  (β^2 - α^2) / ((2*(n:ℝ)+α+β+2)*(2*n+α+β+4))

/-- Coefficient `c` of the normalised recurrence: `x P_{n+1} = a P_{n+2} + b P_{n+1} + c P_n`. -/
noncomputable def jacC (α β : ℝ) (n : ℕ) : ℝ :=
  2*((n:ℝ)+α+1)*(n+β+1) / ((2*n+α+β+2)*(2*n+α+β+3))

/-- Coefficient of `P_1` in `x P_0 = a P_1 + b P_0`. -/
noncomputable def jacA0 (α β : ℝ) : ℝ := 2 / (α + β + 2)

/-- Coefficient of `P_0` in `x P_0 = a P_1 + b P_0`. -/
noncomputable def jacB0 (α β : ℝ) : ℝ := (β - α) / (α + β + 2)

/-- Division of a three-term relation `A P₂ = B (E x + H) P₁ - G P₀` by `B E`. -/
lemma jacRec_normalise (A B E H G a b c : ℝ) (hB : B ≠ 0) (hE : E ≠ 0)
    (ha : a = A / (B * E)) (hb : b = -H / E) (hc : c = G / (B * E)) (P0 P1 P2 : ℝ[X])
    (h : C A * P2 = C B * (C E * X + C H) * P1 - C G * P0) :
    X * P1 = C a * P2 + C b * P1 + C c * P0 := by
  have hBE : (C B * C E : ℝ[X]) ≠ 0 :=
    mul_ne_zero (by simpa using hB) (by simpa using hE)
  have hA : C A = C a * C B * C E := by
    rw [← C_mul, ← C_mul]; congr 1; rw [ha]; field_simp
  have hG : C G = C c * C B * C E := by
    rw [← C_mul, ← C_mul]; congr 1; rw [hc]; field_simp
  have hH : C H = - (C b * C E) := by
    rw [← C_mul, ← C_neg]; congr 1; rw [hb]; field_simp
  rw [hA, hG, hH] at h
  refine mul_left_cancel₀ hBE ?_
  linear_combination -h

/-- The normalised three-term recurrence (DLMF 18.9.1 divided through): for `α + β + 2 > 0`,
`x P_{n+1} = a_n P_{n+2} + b_n P_{n+1} + c_n P_n`. -/
theorem jacobi_X_mul_succ (α β : ℝ) (hs : 0 < α + β + 2) (n : ℕ) :
    X * jacobi α β (n+1)
      = C (jacA α β n) * jacobi α β (n+2) + C (jacB α β n) * jacobi α β (n+1)
        + C (jacC α β n) * jacobi α β n := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : 0 < 2*(n:ℝ)+α+β+2 := by linarith
  have h3 : 0 < 2*(n:ℝ)+α+β+3 := by linarith
  have h4 : 0 < 2*(n:ℝ)+α+β+4 := by linarith
  refine jacRec_normalise _ (2*(n:ℝ)+α+β+3) ((2*n+α+β+4)*(2*n+α+β+2)) (α^2-β^2)
    (2*((n:ℝ)+α+1)*(n+β+1)*(2*n+α+β+4)) _ _ _ h3.ne' (mul_pos h4 h2).ne' ?_ ?_ ?_ _ _ _
    (jacobi_three_term α β n)
  · unfold jacA; field_simp
  · unfold jacB; field_simp; ring
  · unfold jacC; field_simp

/-- The normalised recurrence at the start: `x P_0 = a P_1 + b P_0` for `α + β + 2 > 0`. -/
theorem jacobi_X_mul_zero (α β : ℝ) (hs : 0 < α + β + 2) :
    X * jacobi α β 0 = C (jacA0 α β) * jacobi α β 1 + C (jacB0 α β) * jacobi α β 0 := by
  rw [jacobi_zero, jacobi_one]
  refine Polynomial.funext (fun x => ?_)
  simp only [eval_mul, eval_C, eval_add, eval_X, mul_one]
  unfold jacA0 jacB0
  field_simp
  ring

/-- info: 'FormalResearch.Special.jacobi_three_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_three_term

/-- info: 'FormalResearch.Special.jacobi_X_mul_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_X_mul_succ

/-- info: 'FormalResearch.Special.jacobi_X_mul_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_X_mul_zero

/-- info: 'FormalResearch.Special.jacobi_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_one

end FormalResearch.Special
