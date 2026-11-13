module

public import FormalResearch.Special.JacobiBasic
public import FormalResearch.Special.JacobiRec

/-!
# Jacobi polynomials: special cases and Rodrigues' formula

Connections of `jacobi α β n` (DLMF 18.5.7, `FormalResearch/Special/JacobiDef.lean`) to Mathlib's
classical families, and the Rodrigues formula (DLMF 18.5.5), all as identities in `ℝ[X]`.

## Conventions found in Mathlib

* `Polynomial.shiftedLegendre n : ℤ[X]` (`Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean`) is
  `∑ₖ (-1)ᵏ C(n,k) C(n+k,n) Xᵏ`, normalised by `P̃_n(0) = 1` (so `P̃_n(x) = P_n(1 - 2x)`, *not*
  `P_n(2x-1)`); hence `P_n^{(0,0)}(x) = P̃_n((1-x)/2)`.
* `Polynomial.Chebyshev.T R n`, `U R n` (`Mathlib/RingTheory/Polynomial/Chebyshev.lean`) are indexed
  by `ℤ` and defined by the recursion `T_{n+2} = 2X T_{n+1} - T_n`.

## Main results

* `jacobi_zero_zero_eq_shiftedLegendre`: `P_n^{(0,0)} = P̃_n ∘ ((1-x)/2)` (DLMF 18.7.9 with the sign
  convention above).
* `jacobi_chebyshevT`, `chebyshevT_eq_jacobi` (DLMF 18.7.3):
  `P_n^{(-1/2,-1/2)} = ((1/2)_n/n!) T_n`, i.e. `T_n = P_n^{(-1/2,-1/2)}/P_n^{(-1/2,-1/2)}(1)`.
* `jacobi_chebyshevU`, `chebyshevU_eq_jacobi` (DLMF 18.7.4):
  `P_n^{(1/2,1/2)} = ((3/2)_n/(n+1)!) U_n`, i.e. `U_n = (n+1) P_n^{(1/2,1/2)}/P_n^{(1/2,1/2)}(1)`.
* `gegenbauer` (DLMF 18.7.1), `gegenbauer_comp_neg` (parity), `gegenbauer_three_term`
  (DLMF 18.9.1).
* `jacobi_twoSided_poly`: the two-sided explicit sum DLMF 18.5.8 for natural parameters, as a
  polynomial identity.
* `jacobi_rodrigues`: **Rodrigues' formula** (DLMF 18.5.5) for natural `a b`:
  `(1-x)^a (1+x)^b P_n^{(a,b)} = ((-1)^n/(2^n n!)) dⁿ/dxⁿ [(1-x)^{n+a} (1+x)^{n+b}]`.
-/

@[expose] public section

namespace FormalResearch.Special

open Polynomial

/-! ### Explicit coefficients for natural parameters -/

lemma jacSp_poch_nat_succ (N k : ℕ) :
    (ascPochhammer ℝ k).eval ((N : ℝ) + 1) * (N.factorial : ℝ) = ((N + k).factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, mul_assoc, mul_comm ((N : ℝ) + 1 + k), ← mul_assoc, ih,
      show N + (k + 1) = (N + k) + 1 by ring, Nat.factorial_succ]
    push_cast; ring

/-- The Pochhammer coefficient of `jacobiCoeff` is a product of binomials. -/
lemma jacSp_coeff_eq_choose (μ ν n ℓ : ℕ) (hℓ : ℓ ≤ n) :
    (ascPochhammer ℝ ℓ).eval ((n : ℝ) + μ + ν + 1) *
        (ascPochhammer ℝ (n - ℓ)).eval ((μ : ℝ) + ℓ + 1) /
      ((ℓ.factorial : ℝ) * ((n - ℓ).factorial : ℝ)) =
    (((n + μ).choose (n - ℓ) * (n + μ + ν + ℓ).choose ℓ : ℕ) : ℝ) := by
  have p1 : (ascPochhammer ℝ ℓ).eval ((n : ℝ) + μ + ν + 1) =
      ((n + μ + ν + ℓ).factorial : ℝ) / ((n + μ + ν).factorial : ℝ) := by
    rw [eq_div_iff (by positivity)]
    have := jacSp_poch_nat_succ (n + μ + ν) ℓ
    push_cast at this
    exact this
  have p2 : (ascPochhammer ℝ (n - ℓ)).eval ((μ : ℝ) + ℓ + 1) =
      ((n + μ).factorial : ℝ) / ((μ + ℓ).factorial : ℝ) := by
    rw [eq_div_iff (by positivity)]
    have := jacSp_poch_nat_succ (μ + ℓ) (n - ℓ)
    rw [show μ + ℓ + (n - ℓ) = n + μ by omega] at this
    push_cast at this
    exact this
  have c1 : (((n + μ).choose (n - ℓ) : ℕ) : ℝ) =
      ((n + μ).factorial : ℝ) / (((n - ℓ).factorial : ℝ) * ((μ + ℓ).factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (by omega : n - ℓ ≤ n + μ), show n + μ - (n - ℓ) = μ + ℓ by omega]
  have c2 : (((n + μ + ν + ℓ).choose ℓ : ℕ) : ℝ) =
      ((n + μ + ν + ℓ).factorial : ℝ) / ((ℓ.factorial : ℝ) * ((n + μ + ν).factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (by omega : ℓ ≤ n + μ + ν + ℓ),
      show n + μ + ν + ℓ - ℓ = n + μ + ν by omega]
  rw [Nat.cast_mul, c1, c2, p1, p2]
  have h1 : (0 : ℝ) < ℓ.factorial := by positivity
  have h2 : (0 : ℝ) < (n - ℓ).factorial := by positivity
  have h3 : (0 : ℝ) < (μ + ℓ).factorial := by positivity
  have h4 : (0 : ℝ) < (n + μ + ν).factorial := by positivity
  field_simp

/-- For natural parameters `μ ν`, the coefficient of `(x-1)^ℓ` in `P_n^{(μ,ν)}` is
`C(n+μ, n-ℓ) C(n+μ+ν+ℓ, ℓ) / 2^ℓ` (`ℓ ≤ n`). -/
lemma jacobiCoeff_nat (μ ν n ℓ : ℕ) (hℓ : ℓ ≤ n) :
    jacobiCoeff (μ : ℝ) (ν : ℝ) n ℓ =
      (((n + μ).choose (n - ℓ) * (n + μ + ν + ℓ).choose ℓ : ℕ) : ℝ) / 2 ^ ℓ := by
  rw [← jacSp_coeff_eq_choose μ ν n ℓ hℓ]
  unfold jacobiCoeff
  have h1 : (0 : ℝ) < ℓ.factorial := by positivity
  have h2 : (0 : ℝ) < (n - ℓ).factorial := by positivity
  field_simp

/-! ### Legendre -/

/-- **Legendre case** (DLMF 18.7.9, with Mathlib's convention `P̃_n(x) = P_n(1-2x)` for
`shiftedLegendre`): `P_n^{(0,0)}(x) = P̃_n((1-x)/2)`. -/
theorem jacobi_zero_zero_eq_shiftedLegendre (n : ℕ) :
    jacobi 0 0 n =
      ((shiftedLegendre n).map (Int.castRingHom ℝ)).comp (C (1 / 2 : ℝ) * (1 - X)) := by
  unfold jacobi shiftedLegendre
  rw [Polynomial.map_sum, Polynomial.sum_comp]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hℓn : ℓ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
  have hc := jacobiCoeff_nat 0 0 n ℓ hℓn
  simp only [Nat.cast_zero] at hc
  rw [hc]
  simp only [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, mul_comp, C_comp, pow_comp,
    X_comp]
  have e : (C (1 / 2 : ℝ) * (1 - X) : ℝ[X]) = C (-(1 / 2 : ℝ)) * (X - 1) := by
    refine Polynomial.funext fun x => ?_
    simp; ring
  rw [e, mul_pow, ← C_pow, ← mul_assoc, ← C_mul]
  congr 2
  simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, neg_pow (1 / 2 : ℝ), Nat.cast_mul]
  have : ((n + ℓ).choose ℓ : ℕ) = (n + ℓ).choose n := by
    rw [Nat.choose_symm_add]
  simp only [Nat.add_zero]
  rw [Nat.choose_symm hℓn, this]
  have h2 : ((2 : ℝ) ^ ℓ) ≠ 0 := by positivity
  have h3 : ((-1 : ℝ) ^ (ℓ * 2)) = 1 := Even.neg_one_pow ⟨ℓ, by ring⟩
  rw [one_div, inv_pow]
  field_simp
  linear_combination (-(↑(n.choose ℓ) * ↑((n + ℓ).choose n)) : ℝ) * h3

/-! ### Chebyshev -/

/-- Transfer of the Jacobi three-term recurrence to a family `Q` with `Q_{n+2} = 2X Q_{n+1} - Q_n`,
when `P_n = c_n Q_n` and the scalars satisfy the two compatibility relations `e1`, `e2`. -/
lemma jacSp_step (K A B H G c0 c1 c2 : ℝ) (hK : K ≠ 0) (hH : H = 0)
    (e1 : 2 * (K * c2) = A * c1 * B) (e2 : K * c2 = G * c0) (Q0 Q1 Q2 P0 P1 P2 : ℝ[X])
    (h0 : P0 = C c0 * Q0) (h1 : P1 = C c1 * Q1) (hQ : Q2 = 2 * X * Q1 - Q0)
    (h3 : C K * P2 = C A * (C B * X + C H) * P1 - C G * P0) : P2 = C c2 * Q2 := by
  subst hH
  refine mul_left_cancel₀ (by simpa using hK : (C K : ℝ[X]) ≠ 0) ?_
  rw [h3, h0, h1, hQ]
  have e1' := congrArg (C : ℝ → ℝ[X]) e1
  have e2' := congrArg (C : ℝ → ℝ[X]) e2
  simp only [map_mul, map_ofNat] at e1' e2'
  simp only [map_zero, add_zero]
  linear_combination -(X * Q1) * e1' + Q0 * e2'

/-- Pochhammer/factorial ratio: `(a)_{n+1}/(n+1)! = (a)_n/n! · (a+n)/(n+1)`. -/
lemma jacSp_ratio (a : ℝ) (n : ℕ) :
    (ascPochhammer ℝ (n + 1)).eval a / ((n + 1).factorial : ℝ) =
      (ascPochhammer ℝ n).eval a / (n.factorial : ℝ) * ((a + n) / ((n : ℝ) + 1)) := by
  rw [ascPochhammer_succ_eval, Nat.factorial_succ]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **Chebyshev of the first kind** (DLMF 18.7.3): `P_n^{(-1/2,-1/2)} = ((1/2)_n/n!) T_n`. -/
theorem jacobi_chebyshevT (n : ℕ) :
    jacobi (-1 / 2) (-1 / 2) n =
      C ((ascPochhammer ℝ n).eval (1 / 2) / (n.factorial : ℝ)) * Chebyshev.T ℝ n := by
  suffices h : ∀ n : ℕ, jacobi (-1 / 2) (-1 / 2) n =
        C ((ascPochhammer ℝ n).eval (1 / 2) / (n.factorial : ℝ)) * Chebyshev.T ℝ n ∧
      jacobi (-1 / 2) (-1 / 2) (n + 1) =
        C ((ascPochhammer ℝ (n + 1)).eval (1 / 2) / ((n + 1).factorial : ℝ)) *
          Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) from (h n).1
  intro n
  induction n with
  | zero =>
    refine ⟨by simp [jacobi_zero], ?_⟩
    rw [jacobi_one]
    simp only [zero_add, Nat.factorial_one, Nat.cast_one, div_one,
      ascPochhammer_one, eval_X, Nat.cast_one, Chebyshev.T_one]
    refine Polynomial.funext fun x => ?_
    simp only [eval_add, eval_mul, eval_C, eval_X]
    ring
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hQ : Chebyshev.T ℝ ((n + 2 : ℕ) : ℤ) =
        2 * X * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) - Chebyshev.T ℝ (n : ℤ) := by
      have := Chebyshev.T_add_two ℝ (n : ℤ)
      push_cast
      exact this
    have r1 := jacSp_ratio (1 / 2 : ℝ) n
    have r2 := jacSp_ratio (1 / 2 : ℝ) (n + 1)
    generalize (ascPochhammer ℝ n).eval (1 / 2) / (n.factorial : ℝ) = c0 at r1 r2 ih ⊢
    generalize (ascPochhammer ℝ (n + 1)).eval (1 / 2) / ((n + 1).factorial : ℝ) = c1 at r1 r2 ih ⊢
    generalize (ascPochhammer ℝ (n + 1 + 1)).eval (1 / 2) / ((n + 1 + 1).factorial : ℝ) = c2 at r2 ⊢
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    refine jacSp_step _ _ _ _ _ c0 c1 c2 ?_ (by ring) ?_ ?_ _ _ _ _ _ _ ih.1 ih.2 hQ
      (jacobi_three_term (-1 / 2) (-1 / 2) n)
    · ring_nf; positivity
    · rw [r2, r1]; push_cast; field_simp; ring
    · rw [r2, r1]; push_cast; field_simp; ring

/-- `T_n = P_n^{(-1/2,-1/2)} / P_n^{(-1/2,-1/2)}(1)` (DLMF 18.7.3). -/
theorem chebyshevT_eq_jacobi (n : ℕ) :
    Chebyshev.T ℝ n =
      C (((jacobi (-1 / 2) (-1 / 2) n).eval 1)⁻¹) * jacobi (-1 / 2) (-1 / 2) n := by
  have h1 : (jacobi (-1 / 2) (-1 / 2) n).eval 1 =
      (ascPochhammer ℝ n).eval (1 / 2) / (n.factorial : ℝ) := by
    rw [jacobi_eval_one]; norm_num
  have h2 : (ascPochhammer ℝ n).eval (1 / 2 : ℝ) ≠ 0 := (ascPochhammer_pos n _ (by norm_num)).ne'
  rw [h1, jacobi_chebyshevT, ← mul_assoc, ← C_mul]
  have : (ascPochhammer ℝ n).eval (1 / 2 : ℝ) / (n.factorial : ℝ) ≠ 0 := by positivity
  rw [inv_mul_cancel₀ this]
  simp

/-- Pochhammer/factorial ratio shifted by one: `(a)_{n+1}/(n+2)! = (a)_n/(n+1)! · (a+n)/(n+2)`. -/
lemma jacSp_ratio' (a : ℝ) (n : ℕ) :
    (ascPochhammer ℝ (n + 1)).eval a / ((n + 1 + 1).factorial : ℝ) =
      (ascPochhammer ℝ n).eval a / ((n + 1).factorial : ℝ) * ((a + n) / ((n : ℝ) + 2)) := by
  rw [ascPochhammer_succ_eval, Nat.factorial_succ (n + 1)]
  have : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  have : ((n : ℝ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Chebyshev of the second kind** (DLMF 18.7.4): `P_n^{(1/2,1/2)} = ((3/2)_n/(n+1)!) U_n`. -/
theorem jacobi_chebyshevU (n : ℕ) :
    jacobi (1 / 2) (1 / 2) n =
      C ((ascPochhammer ℝ n).eval (3 / 2) / ((n + 1).factorial : ℝ)) * Chebyshev.U ℝ n := by
  suffices h : ∀ n : ℕ, jacobi (1 / 2) (1 / 2) n =
        C ((ascPochhammer ℝ n).eval (3 / 2) / ((n + 1).factorial : ℝ)) * Chebyshev.U ℝ n ∧
      jacobi (1 / 2) (1 / 2) (n + 1) =
        C ((ascPochhammer ℝ (n + 1)).eval (3 / 2) / ((n + 1 + 1).factorial : ℝ)) *
          Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ) from (h n).1
  intro n
  induction n with
  | zero =>
    refine ⟨by simp [jacobi_zero], ?_⟩
    rw [jacobi_one]
    simp only [zero_add, ascPochhammer_one, eval_X, Nat.cast_one, Chebyshev.U_one]
    refine Polynomial.funext fun x => ?_
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_ofNat]
    ring
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hQ : Chebyshev.U ℝ ((n + 2 : ℕ) : ℤ) =
        2 * X * Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ) - Chebyshev.U ℝ (n : ℤ) := by
      have := Chebyshev.U_add_two ℝ (n : ℤ)
      push_cast
      exact this
    have r1 := jacSp_ratio' (3 / 2 : ℝ) n
    have r2 := jacSp_ratio' (3 / 2 : ℝ) (n + 1)
    generalize (ascPochhammer ℝ n).eval (3 / 2) / ((n + 1).factorial : ℝ) = c0 at r1 r2 ih ⊢
    generalize (ascPochhammer ℝ (n + 1)).eval (3 / 2) / ((n + 1 + 1).factorial : ℝ) = c1
      at r1 r2 ih ⊢
    generalize (ascPochhammer ℝ (n + 1 + 1)).eval (3 / 2) / ((n + 1 + 1 + 1).factorial : ℝ) = c2
      at r2 ⊢
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    refine jacSp_step _ _ _ _ _ c0 c1 c2 ?_ (by ring) ?_ ?_ _ _ _ _ _ _ ih.1 ih.2 hQ
      (jacobi_three_term (1 / 2) (1 / 2) n)
    · ring_nf; positivity
    · rw [r2, r1]; push_cast; field_simp; ring
    · rw [r2, r1]; push_cast; field_simp; ring

/-- `U_n = (n+1) P_n^{(1/2,1/2)} / P_n^{(1/2,1/2)}(1)` (DLMF 18.7.4). -/
theorem chebyshevU_eq_jacobi (n : ℕ) :
    Chebyshev.U ℝ n =
      C (((n : ℝ) + 1) * ((jacobi (1 / 2) (1 / 2) n).eval 1)⁻¹) * jacobi (1 / 2) (1 / 2) n := by
  have h1 : (jacobi (1 / 2) (1 / 2) n).eval 1 =
      (ascPochhammer ℝ n).eval (3 / 2) / (n.factorial : ℝ) := by
    rw [jacobi_eval_one]; norm_num
  have h2 : (ascPochhammer ℝ n).eval (3 / 2 : ℝ) ≠ 0 := (ascPochhammer_pos n _ (by norm_num)).ne'
  rw [h1, jacobi_chebyshevU, ← mul_assoc, ← C_mul]
  have e : ((n : ℝ) + 1) * ((ascPochhammer ℝ n).eval (3 / 2) / (n.factorial : ℝ))⁻¹ *
      ((ascPochhammer ℝ n).eval (3 / 2) / ((n + 1).factorial : ℝ)) = 1 := by
    rw [Nat.factorial_succ]
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [e]
  simp

/-! ### Gegenbauer (ultraspherical) -/

/-- The Gegenbauer polynomial `C_n^{(λ)} = (2λ)_n/(λ+1/2)_n · P_n^{(λ-1/2,λ-1/2)}` (DLMF 18.7.1).
For `λ > -1/2` the normalising constant has nonzero denominator; at other `λ` the Lean convention
`x/0 = 0` applies, and the statements below assume `-1/2 < λ` where it matters. -/
noncomputable def gegenbauer (lam : ℝ) (n : ℕ) : ℝ[X] :=
  C ((ascPochhammer ℝ n).eval (2 * lam) / (ascPochhammer ℝ n).eval (lam + 1 / 2)) *
    jacobi (lam - 1 / 2) (lam - 1 / 2) n

lemma gegenbauer_zero (lam : ℝ) : gegenbauer lam 0 = 1 := by
  simp [gegenbauer, jacobi_zero]

/-- Parity of Gegenbauer polynomials (from DLMF 18.6.1 for Jacobi):
`C_n^{(λ)}(-x) = (-1)^n C_n^{(λ)}(x)`. -/
theorem gegenbauer_comp_neg (lam : ℝ) (n : ℕ) :
    (gegenbauer lam n).comp (-X) = (-1) ^ n • gegenbauer lam n := by
  unfold gegenbauer
  rw [mul_comp, C_comp, jacobi_comp_neg]
  exact mul_smul_comm _ _ _

/-- Value at `1` (DLMF 18.6.1): `C_n^{(λ)}(1) = (2λ)_n/n!` for `λ > -1/2`. -/
theorem gegenbauer_eval_one (lam : ℝ) (hlam : -1 / 2 < lam) (n : ℕ) :
    (gegenbauer lam n).eval 1 = (ascPochhammer ℝ n).eval (2 * lam) / (n.factorial : ℝ) := by
  unfold gegenbauer
  rw [eval_mul, eval_C, jacobi_eval_one, show lam - 1 / 2 + 1 = lam + 1 / 2 by ring]
  have : (ascPochhammer ℝ n).eval (lam + 1 / 2) ≠ 0 :=
    (ascPochhammer_pos n _ (by linarith)).ne'
  generalize (ascPochhammer ℝ n).eval (lam + 1 / 2) = b at this ⊢
  field_simp

/-- `C_1^{(λ)} = 2λ X` for `λ > -1/2`. -/
theorem gegenbauer_one (lam : ℝ) (hlam : -1 / 2 < lam) : gegenbauer lam 1 = C (2 * lam) * X := by
  unfold gegenbauer
  rw [jacobi_one]
  have : lam + 1 / 2 ≠ 0 := by linarith
  have h2 : 2 * lam + 1 ≠ 0 := by linarith
  refine Polynomial.funext fun x => ?_
  simp only [ascPochhammer_one, eval_X, eval_mul, eval_add, eval_C]
  rw [show lam - 1 / 2 - (lam - 1 / 2) = 0 by ring,
    show lam - 1 / 2 + (lam - 1 / 2) + 2 = 2 * (lam + 1 / 2) by ring]
  field_simp
  ring

/-- Ratio of the normalising constants of `gegenbauer`. -/
lemma jacSp_geg_ratio (lam : ℝ) (n : ℕ) :
    (ascPochhammer ℝ (n + 1)).eval (2 * lam) / (ascPochhammer ℝ (n + 1)).eval (lam + 1 / 2) =
      (ascPochhammer ℝ n).eval (2 * lam) / (ascPochhammer ℝ n).eval (lam + 1 / 2) *
        ((2 * lam + n) / (lam + 1 / 2 + n)) := by
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, mul_div_mul_comm]

/-- Transfer of the three-term recurrence to a rescaled family (scalar bookkeeping). -/
lemma jacSp_step2 (K A B H G L c2 c1 c0 R1 R0 : ℝ) (hK : K ≠ 0) (hH : H = 0)
    (e1 : L * c2 * A * B = K * R1 * c1) (e2 : L * c2 * G = K * R0 * c0) (P0 P1 P2 : ℝ[X])
    (h3 : C K * P2 = C A * (C B * X + C H) * P1 - C G * P0) :
    C L * (C c2 * P2) = C R1 * X * (C c1 * P1) - C R0 * (C c0 * P0) := by
  subst hH
  refine mul_left_cancel₀ (by simpa using hK : (C K : ℝ[X]) ≠ 0) ?_
  have e1' := congrArg (C : ℝ → ℝ[X]) e1
  have e2' := congrArg (C : ℝ → ℝ[X]) e2
  simp only [map_mul] at e1' e2'
  simp only [map_zero, add_zero] at h3
  linear_combination (C L * C c2) * h3 + (X * P1) * e1' - P0 * e2'

/-- **Three-term recurrence of Gegenbauer polynomials** (DLMF 18.9.1), for `λ > -1/2`:
`(n+2) C_{n+2}^{(λ)} = 2(n+1+λ) X C_{n+1}^{(λ)} - (n+2λ) C_n^{(λ)}`. -/
theorem gegenbauer_three_term (lam : ℝ) (hlam : -1 / 2 < lam) (n : ℕ) :
    C ((n : ℝ) + 2) * gegenbauer lam (n + 2) =
      C (2 * ((n : ℝ) + 1 + lam)) * X * gegenbauer lam (n + 1) -
        C ((n : ℝ) + 2 * lam) * gegenbauer lam n := by
  unfold gegenbauer
  have r1 := jacSp_geg_ratio lam n
  have r2 := jacSp_geg_ratio lam (n + 1)
  generalize (ascPochhammer ℝ n).eval (2 * lam) / (ascPochhammer ℝ n).eval (lam + 1 / 2) = c0
    at r1 r2 ⊢
  generalize (ascPochhammer ℝ (n + 1)).eval (2 * lam) /
    (ascPochhammer ℝ (n + 1)).eval (lam + 1 / 2) = c1 at r1 r2 ⊢
  generalize (ascPochhammer ℝ (n + 1 + 1)).eval (2 * lam) /
    (ascPochhammer ℝ (n + 1 + 1)).eval (lam + 1 / 2) = c2 at r2 ⊢
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have p1 : lam + 1 / 2 + n ≠ 0 := by linarith
  have p2 : lam + 1 / 2 + ((n + 1 : ℕ) : ℝ) ≠ 0 := by push_cast; linarith
  have hr1 : c1 * (lam + 1 / 2 + n) = c0 * (2 * lam + n) := by
    rw [r1, mul_assoc, div_mul_cancel₀ _ p1]
  have hr2 : c2 * (lam + 1 / 2 + (n + 1)) = c1 * (2 * lam + (n + 1)) := by
    push_cast at p2 r2
    rw [r2, mul_assoc, div_mul_cancel₀ _ p2]
  have hK : 2 * ((n : ℝ) + 2) * (n + (lam - 1 / 2) + (lam - 1 / 2) + 2) *
      (2 * n + (lam - 1 / 2) + (lam - 1 / 2) + 2) ≠ 0 := by
    have : 0 < (n : ℝ) + 2 := by linarith
    have : 0 < (n : ℝ) + (lam - 1 / 2) + (lam - 1 / 2) + 2 := by linarith
    have : 0 < 2 * (n : ℝ) + (lam - 1 / 2) + (lam - 1 / 2) + 2 := by linarith
    positivity
  refine jacSp_step2 _ _ _ _ _ _ c2 c1 c0 _ _ hK (by ring) ?_ ?_ _ _ _
    (jacobi_three_term (lam - 1 / 2) (lam - 1 / 2) n)
  · linear_combination (8 * ((n : ℝ) + 2) * ((n : ℝ) + lam + 1) * (lam + 1 / 2 + n)) * hr2
  · linear_combination (4 * ((n : ℝ) + 2) * (lam + 1 / 2 + n)) *
      ((lam + 1 / 2 + n) * hr2 + (2 * lam + n + 1) * hr1)

/-! ### The two-sided sum (DLMF 18.5.8) -/

/-- Vandermonde step: for `d ≤ n`,
`∑_{s ≤ d} C(n+μ, n-s) C(n+ν, s) C(n-s, d-s) = C(n+μ, n-d) C(n+μ+ν+d, d)`. -/
lemma jacSp_vandermonde (μ ν n d : ℕ) (hd : d ≤ n) :
    ∑ s ∈ Finset.range (d + 1), (n + μ).choose (n - s) * (n + ν).choose s * (n - s).choose (d - s) =
      (n + μ).choose (n - d) * (n + μ + ν + d).choose d := by
  have step : ∀ s ∈ Finset.range (d + 1),
      (n + μ).choose (n - s) * (n + ν).choose s * (n - s).choose (d - s) =
        (n + μ).choose (n - d) * ((n + ν).choose s * (μ + d).choose (d - s)) := by
    intro s hs
    have hs' : s ≤ d := by simp at hs; omega
    have h1 : (n - s).choose (d - s) = (n - s).choose (n - d) :=
      Nat.choose_symm_of_eq_add (by omega)
    have h2 := Nat.choose_mul (n := n + μ) (k := n - s) (s := n - d) (by omega)
    rw [show n + μ - (n - d) = μ + d by omega, show n - s - (n - d) = d - s by omega] at h2
    rw [h1, mul_assoc, mul_comm ((n + ν).choose s), ← mul_assoc, h2]
    ring
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum]
  congr 1
  rw [show n + μ + ν + d = (n + ν) + (μ + d) by ring, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The polynomial form of DLMF 18.5.8 in the variable `y = (x-1)/2`:
`∑_s C(n+μ,n-s) C(n+ν,s) y^s (1+y)^{n-s} = ∑_ℓ C(n+μ,n-ℓ) C(n+μ+ν+ℓ,ℓ) y^ℓ`. -/
lemma jacSp_twoSided_aux (μ ν n : ℕ) :
    ∑ s ∈ Finset.range (n + 1),
        C (((n + μ).choose (n - s) * (n + ν).choose s : ℕ) : ℝ) * X ^ s * (1 + X) ^ (n - s) =
      ∑ ℓ ∈ Finset.range (n + 1),
        C (((n + μ).choose (n - ℓ) * (n + μ + ν + ℓ).choose ℓ : ℕ) : ℝ) * X ^ ℓ := by
  ext d
  simp only [finsetSum_coeff, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_one_add_X_pow,
    coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hd : d ≤ n
  · simp only [Finset.mem_range, show d < n + 1 by omega, ↓reduceIte]
    have hsub : ∑ s ∈ Finset.range (n + 1), (if s ≤ d then
          (((n + μ).choose (n - s) * (n + ν).choose s : ℕ) : ℝ) * (((n - s).choose (d - s) : ℕ) : ℝ)
          else 0) =
        ∑ s ∈ Finset.range (d + 1), (((n + μ).choose (n - s) * (n + ν).choose s *
          (n - s).choose (d - s) : ℕ) : ℝ) := by
      rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : d + 1 ≤ n + 1))]
      · refine Finset.sum_congr rfl fun s hs => ?_
        have : s ≤ d := by simp at hs; omega
        simp only [this, ↓reduceIte]; push_cast; ring
      · intro s _ hs
        have : ¬ s ≤ d := by simp at hs; omega
        simp [this]
    rw [hsub, ← Nat.cast_sum, jacSp_vandermonde μ ν n d hd]
  · have hd' : d ∉ Finset.range (n + 1) := by simpa using hd
    simp only [hd', ↓reduceIte]
    apply Finset.sum_eq_zero
    intro s hs
    have hsn : s ≤ n := by simp at hs; omega
    by_cases hsd : s ≤ d
    · have : (n - s).choose (d - s) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hsd, this]
    · simp [hsd]

/-- **DLMF 18.5.8** for natural parameters, as a polynomial identity:
`P_n^{(μ,ν)} = 2^{-n} ∑_s C(n+μ, n-s) C(n+ν, s) (X-1)^s (X+1)^{n-s}`. -/
theorem jacobi_twoSided_poly (μ ν n : ℕ) :
    jacobi (μ : ℝ) (ν : ℝ) n =
      ∑ s ∈ Finset.range (n + 1),
        C ((((n + μ).choose (n - s) * (n + ν).choose s : ℕ) : ℝ) / 2 ^ n) *
          (X - 1) ^ s * (X + 1) ^ (n - s) := by
  refine Polynomial.funext fun x => ?_
  have h := congrArg (Polynomial.eval ((x - 1) / 2)) (jacSp_twoSided_aux μ ν n)
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one] at h
  rw [show (1 : ℝ) + (x - 1) / 2 = (x + 1) / 2 by ring] at h
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one, eval_sub]
  rw [jacobi_eval]
  have hL : ∑ ℓ ∈ Finset.range (n + 1), jacobiCoeff (μ : ℝ) (ν : ℝ) n ℓ * (x - 1) ^ ℓ =
      ∑ ℓ ∈ Finset.range (n + 1),
        (((n + μ).choose (n - ℓ) * (n + μ + ν + ℓ).choose ℓ : ℕ) : ℝ) * ((x - 1) / 2) ^ ℓ := by
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hℓn : ℓ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
    rw [jacobiCoeff_nat μ ν n ℓ hℓn, div_pow]
    have : ((2 : ℝ) ^ ℓ) ≠ 0 := by positivity
    field_simp
  rw [hL, ← h]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsn : s ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have : (2 : ℝ) ^ n = 2 ^ s * 2 ^ (n - s) := by rw [← pow_add]; congr 1; omega
  rw [div_pow, div_pow, this]
  have h2 : ((2 : ℝ) ^ s) ≠ 0 := by positivity
  have h3 : ((2 : ℝ) ^ (n - s)) ≠ 0 := by positivity
  field_simp

/-! ### Rodrigues' formula -/

/-- The Leibniz coefficient identity behind Rodrigues' formula:
`C(n,k) (n+a)_{(n-k)↓} (n+b)_{k↓} = n! C(n+a, n-k) C(n+b, k)`. -/
lemma jacSp_rodrigues_nat (a b n k : ℕ) (hk : k ≤ n) :
    n.choose k * ((n + a).descFactorial (n - k) * (n + b).descFactorial k) =
      n.factorial * ((n + a).choose (n - k) * (n + b).choose k) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  have h := Nat.choose_mul_factorial_mul_factorial hk
  calc n.choose k * ((n - k).factorial * (n + a).choose (n - k) *
        (k.factorial * (n + b).choose k))
      = (n.choose k * k.factorial * (n - k).factorial) *
          ((n + a).choose (n - k) * (n + b).choose k) := by ring
    _ = _ := by rw [h]

/-- The `n`-th derivative of `(X-1)^{n+a} (X+1)^{n+b}`, in terms of `P_n^{(a,b)}`. -/
lemma jacSp_iterate_derivative (a b n : ℕ) :
    derivative^[n] ((X - 1 : ℝ[X]) ^ (n + a) * (X + 1) ^ (n + b)) =
      C ((n.factorial : ℝ) * 2 ^ n) * ((X - 1) ^ a * (X + 1) ^ b * jacobi (a : ℝ) (b : ℝ) n) := by
  rw [iterate_derivative_mul, jacobi_twoSided_poly, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 := iterate_derivative_X_sub_pow (R := ℝ) (n + a) (n - k) 1
  have h2 := iterate_derivative_X_add_pow (R := ℝ) (n + b) k 1
  simp only [map_one] at h1 h2
  rw [h1, h2, show n + a - (n - k) = a + k by omega, show n + b - k = b + (n - k) by omega]
  simp only [nsmul_eq_mul, ← map_natCast (C : ℝ →+* ℝ[X]), pow_add]
  have hnat := jacSp_rodrigues_nat a b n k hkn
  have hs : (C ((n.choose k : ℕ) : ℝ) * (C (((n + a).descFactorial (n - k) : ℕ) : ℝ) *
        C (((n + b).descFactorial k : ℕ) : ℝ)) : ℝ[X]) =
      C ((n.factorial : ℝ) * 2 ^ n) *
        C ((((n + a).choose (n - k) * (n + b).choose k : ℕ) : ℝ) / 2 ^ n) := by
    rw [← C_mul, ← C_mul, ← C_mul]
    congr 1
    have := congrArg (fun m : ℕ => (m : ℝ)) hnat
    simp only [Nat.cast_mul] at this ⊢
    have h2n : ((2 : ℝ) ^ n) ≠ 0 := by positivity
    rw [this]
    field_simp
  linear_combination ((X - 1 : ℝ[X]) ^ a * (X - 1) ^ k * ((X + 1) ^ b * (X + 1) ^ (n - k))) * hs

/-- **Rodrigues' formula** (DLMF 18.5.5) for natural parameters `a b`, as an identity in `ℝ[X]`:
`(1-x)^a (1+x)^b P_n^{(a,b)}(x) = ((-1)^n/(2^n n!)) dⁿ/dxⁿ [(1-x)^{n+a} (1+x)^{n+b}]`. -/
theorem jacobi_rodrigues (a b n : ℕ) :
    (1 - X : ℝ[X]) ^ a * (1 + X) ^ b * jacobi (a : ℝ) (b : ℝ) n =
      C ((-1) ^ n / (2 ^ n * (n.factorial : ℝ))) *
        derivative^[n] ((1 - X : ℝ[X]) ^ (n + a) * (1 + X) ^ (n + b)) := by
  have e1 : (1 - X : ℝ[X]) ^ (n + a) = C ((-1) ^ (n + a)) * (X - 1) ^ (n + a) := by
    rw [show (1 - X : ℝ[X]) = C (-1) * (X - 1) by simp, mul_pow, C_pow]
  have e2 : (1 + X : ℝ[X]) = X + 1 := add_comm _ _
  have e3 : (1 - X : ℝ[X]) ^ a = C ((-1) ^ a) * (X - 1) ^ a := by
    rw [show (1 - X : ℝ[X]) = C (-1) * (X - 1) by simp, mul_pow, C_pow]
  rw [e1, e2, e3, mul_assoc (C ((-1 : ℝ) ^ (n + a))), iterate_derivative_C_mul,
    jacSp_iterate_derivative]
  have hn : ((2 : ℝ) ^ n * n.factorial) ≠ 0 := by positivity
  have hs : (C ((-1 : ℝ) ^ n / (2 ^ n * (n.factorial : ℝ))) * (C ((-1 : ℝ) ^ (n + a)) *
      C ((n.factorial : ℝ) * 2 ^ n)) : ℝ[X]) = C ((-1 : ℝ) ^ a) := by
    rw [← C_mul, ← C_mul]
    congr 1
    rw [pow_add]
    have h4 : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
    field_simp
    linear_combination h4
  linear_combination (-( (X - 1 : ℝ[X]) ^ a * (X + 1) ^ b * jacobi (a : ℝ) (b : ℝ) n)) * hs


/-- info: 'FormalResearch.Special.jacobiCoeff_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobiCoeff_nat

/-- info: 'FormalResearch.Special.jacobi_zero_zero_eq_shiftedLegendre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_zero_zero_eq_shiftedLegendre

/-- info: 'FormalResearch.Special.jacobi_chebyshevT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_chebyshevT

/-- info: 'FormalResearch.Special.chebyshevT_eq_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chebyshevT_eq_jacobi

/-- info: 'FormalResearch.Special.jacobi_chebyshevU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_chebyshevU

/-- info: 'FormalResearch.Special.chebyshevU_eq_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chebyshevU_eq_jacobi

/-- info: 'FormalResearch.Special.gegenbauer_comp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gegenbauer_comp_neg

/-- info: 'FormalResearch.Special.gegenbauer_eval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gegenbauer_eval_one

/-- info: 'FormalResearch.Special.gegenbauer_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gegenbauer_one

/-- info: 'FormalResearch.Special.gegenbauer_three_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gegenbauer_three_term

/-- info: 'FormalResearch.Special.jacobi_twoSided_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_twoSided_poly

/-- info: 'FormalResearch.Special.jacobi_rodrigues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_rodrigues

end FormalResearch.Special
