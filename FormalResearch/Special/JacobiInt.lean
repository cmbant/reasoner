module

public import FormalResearch.Special.JacobiDef

/-!
# Jacobi polynomials: integration layer for natural parameters

For `α = a`, `β = b` natural numbers the Jacobi weight `(1-x)^a (1+x)^b` is a polynomial, and the
orthogonality theory is elementary. This file proves, for real polynomials on `[-1,1]`:

* `poly_integral_derivative`, `poly_integral_by_parts`: the fundamental theorem of calculus and
  integration by parts;
* `beta_nat`: the Beta integral `∫_{-1}^1 (1-x)^a (1+x)^b dx = 2^(a+b+1) a! b! / (a+b+1)!`;
* `sturm_liouville_orth`: abstract Sturm–Liouville orthogonality for polynomials;
* `jacobi_orth_of_SL`: orthogonality of `jacobi a b m`, `jacobi a b n` (`m ≠ n`), taking the
  Sturm–Liouville form of the Jacobi equation (`JacobiSL`) as hypothesis;
* `natDegree_jacobi_le`, `jacobi_coeff_self`, `jacobi_coeff_self_ne_zero`: degree and leading
  coefficient of `jacobi α β n`;
* `jacobi_orth_lowerDegree`: orthogonality to all polynomials of lower degree, given `JacobiSL` for
  all degrees;
* `integral_cos_substitution`: `∫_0^π f(cos θ) sin θ dθ = ∫_{-1}^1 f`.
-/

@[expose] public section

namespace FormalResearch.Special

open Polynomial MeasureTheory intervalIntegral

/-- Polynomials are interval integrable. -/
lemma poly_intervalIntegrable (r : ℝ[X]) :
    IntervalIntegrable (fun x => r.eval x) volume (-1 : ℝ) 1 :=
  (Polynomial.continuous r).intervalIntegrable _ _

/-- Fundamental theorem of calculus on `[-1,1]` for real polynomials. -/
theorem poly_integral_derivative (p : ℝ[X]) :
    ∫ x in (-1 : ℝ)..1, (derivative p).eval x = p.eval 1 - p.eval (-1) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => p.eval x)
    (fun x _ => p.hasDerivAt x) (poly_intervalIntegrable _)

/-- Integration by parts on `[-1,1]` for real polynomials. -/
theorem poly_integral_by_parts (p q : ℝ[X]) :
    ∫ x in (-1 : ℝ)..1, (derivative p).eval x * q.eval x =
      p.eval 1 * q.eval 1 - p.eval (-1) * q.eval (-1) -
        ∫ x in (-1 : ℝ)..1, p.eval x * (derivative q).eval x := by
  have h := poly_integral_derivative (p * q)
  simp only [derivative_mul, eval_add, eval_mul] at h
  have h1 : IntervalIntegrable (fun x => (derivative p).eval x * q.eval x) volume (-1 : ℝ) 1 := by
    simpa using poly_intervalIntegrable (derivative p * q)
  have h2 : IntervalIntegrable (fun x => p.eval x * (derivative q).eval x) volume (-1 : ℝ) 1 := by
    simpa using poly_intervalIntegrable (p * derivative q)
  rw [intervalIntegral.integral_add h1 h2] at h
  linarith

/-- Beta integral recursion. -/
lemma beta_nat_step (a b : ℕ) :
    ((b : ℝ) + 1) * ∫ x in (-1 : ℝ)..1, (1 - x) ^ (a + 1) * (1 + x) ^ b =
      ((a : ℝ) + 1) * ∫ x in (-1 : ℝ)..1, (1 - x) ^ a * (1 + x) ^ (b + 1) := by
  have h := poly_integral_by_parts ((1 + X) ^ (b + 1)) ((1 - X) ^ (a + 1))
  simp only [derivative_pow, derivative_add, derivative_sub, derivative_one, derivative_X,
    eval_mul, eval_pow, eval_add, eval_sub, eval_one, eval_X, eval_C, eval_zero,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
  have e1 : ∫ x in (-1 : ℝ)..1, ((b : ℝ) + 1) * (1 + x) ^ b * (0 + 1) * (1 - x) ^ (a + 1) =
      ((b : ℝ) + 1) * ∫ x in (-1 : ℝ)..1, (1 - x) ^ (a + 1) * (1 + x) ^ b := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  have e2 : ∫ x in (-1 : ℝ)..1, (1 + x) ^ (b + 1) * (((a : ℝ) + 1) * (1 - x) ^ a * (0 - 1)) =
      -(((a : ℝ) + 1) * ∫ x in (-1 : ℝ)..1, (1 - x) ^ a * (1 + x) ^ (b + 1)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; funext x; ring
  rw [e1, e2] at h
  norm_num at h
  linarith

/-- Beta integral for natural parameters. -/
theorem beta_nat (a b : ℕ) :
    ∫ x in (-1 : ℝ)..1, (1 - x) ^ a * (1 + x) ^ b =
      2 ^ (a + b + 1) * (a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ) := by
  induction a generalizing b with
  | zero =>
    simp only [pow_zero, one_mul, zero_add, Nat.factorial_zero, Nat.cast_one, mul_one]
    rw [intervalIntegral.integral_comp_add_left (fun x : ℝ => x ^ b)]
    rw [integral_pow, Nat.factorial_succ]
    push_cast
    have hb : ((b : ℝ) + 1) ≠ 0 := by positivity
    have hf : (b.factorial : ℝ) ≠ 0 := by positivity
    norm_num
    field_simp
  | succ a ih =>
    have hs := beta_nat_step a b
    have hb : ((b : ℝ) + 1) ≠ 0 := by positivity
    have h1 : ∫ x in (-1 : ℝ)..1, (1 - x) ^ (a + 1) * (1 + x) ^ b =
        ((a : ℝ) + 1) / ((b : ℝ) + 1) *
          ∫ x in (-1 : ℝ)..1, (1 - x) ^ a * (1 + x) ^ (b + 1) := by
      field_simp
      linarith
    rw [h1, ih (b + 1)]
    have e : a + (b + 1) + 1 = a + 1 + b + 1 := by ring
    rw [e, Nat.factorial_succ a, Nat.factorial_succ b]
    have hf : (a.factorial : ℝ) ≠ 0 := by positivity
    have hg : (b.factorial : ℝ) ≠ 0 := by positivity
    have hh : ((a + 1 + b + 1).factorial : ℝ) ≠ 0 := by positivity
    push_cast
    rw [show a + 1 + b + 1 = (a + b + 1) + 1 by ring] at hh ⊢
    field_simp


/-- Abstract Sturm–Liouville orthogonality on `[-1,1]` for polynomials: if `q₁, q₂` satisfy
`(p q')' = -λ w q` with eigenvalues `λ₁ ≠ λ₂` and `p` vanishes at `±1`, then
`∫ w q₁ q₂ = 0`. -/
theorem sturm_liouville_orth (p w q₁ q₂ : ℝ[X]) (l₁ l₂ : ℝ) (hl : l₁ ≠ l₂)
    (h₁ : derivative (p * derivative q₁) = - C l₁ * w * q₁)
    (h₂ : derivative (p * derivative q₂) = - C l₂ * w * q₂)
    (hp1 : p.eval 1 = 0) (hp2 : p.eval (-1) = 0) :
    ∫ x in (-1 : ℝ)..1, w.eval x * q₁.eval x * q₂.eval x = 0 := by
  have key : derivative (p * (derivative q₁ * q₂ - q₁ * derivative q₂)) =
      C (l₂ - l₁) * (w * q₁ * q₂) := by
    have e : derivative (p * (derivative q₁ * q₂ - q₁ * derivative q₂)) =
        q₂ * derivative (p * derivative q₁) - q₁ * derivative (p * derivative q₂) := by
      simp only [derivative_mul, derivative_sub]; ring
    rw [e, h₁, h₂, map_sub]; ring
  have h := poly_integral_derivative (p * (derivative q₁ * q₂ - q₁ * derivative q₂))
  rw [key] at h
  simp only [eval_mul, hp1, hp2, zero_mul, sub_self, eval_C] at h
  have h' : ∫ x in (-1 : ℝ)..1, (l₂ - l₁) * (w.eval x * q₁.eval x * q₂.eval x) = 0 := h
  rw [intervalIntegral.integral_const_mul] at h'
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hl
  · exact h0

/-- The Jacobi weight `(1 - x)^a (1 + x)^b` as a polynomial. -/
noncomputable def jacobiWeight (a b : ℕ) : ℝ[X] := (1 - X) ^ a * (1 + X) ^ b

/-- The Sturm–Liouville coefficient `(1 - x)^(a+1) (1 + x)^(b+1)`. -/
noncomputable def jacobiSLCoeff (a b : ℕ) : ℝ[X] := (1 - X) ^ (a + 1) * (1 + X) ^ (b + 1)

/-- The Jacobi differential equation in Sturm–Liouville form for degree `m`:
`((1-x)^(a+1) (1+x)^(b+1) P_m')' = -m(m+a+b+1) (1-x)^a (1+x)^b P_m`. -/
def JacobiSL (a b m : ℕ) : Prop :=
  derivative (jacobiSLCoeff a b * derivative (jacobi (a : ℝ) (b : ℝ) m)) =
    - C ((m : ℝ) * (m + a + b + 1)) * jacobiWeight a b * jacobi (a : ℝ) (b : ℝ) m

lemma jacobiSLCoeff_eval_one (a b : ℕ) : (jacobiSLCoeff a b).eval 1 = 0 := by
  simp [jacobiSLCoeff]

lemma jacobiSLCoeff_eval_neg_one (a b : ℕ) : (jacobiSLCoeff a b).eval (-1) = 0 := by
  simp [jacobiSLCoeff]

/-- The Jacobi eigenvalues `m(m+a+b+1)` are distinct for distinct `m, n`. -/
lemma jacobi_eigenvalue_injective (a b m n : ℕ) (hmn : m ≠ n) :
    (m : ℝ) * (m + a + b + 1) ≠ (n : ℝ) * (n + a + b + 1) := by
  intro h
  have hmn' : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hpos : (0 : ℝ) < m + n + a + b + 1 := by positivity
  have : ((m : ℝ) - n) * (m + n + a + b + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hmn' h0
  · exact hpos.ne' h0

/-- Orthogonality of Jacobi polynomials of different degrees, given the Sturm–Liouville
form of the Jacobi equation. -/
theorem jacobi_orth_of_SL (a b m n : ℕ) (hm : JacobiSL a b m) (hn : JacobiSL a b n)
    (hmn : m ≠ n) :
    ∫ x in (-1 : ℝ)..1, (jacobiWeight a b).eval x * (jacobi (a : ℝ) (b : ℝ) m).eval x *
      (jacobi (a : ℝ) (b : ℝ) n).eval x = 0 :=
  sturm_liouville_orth (jacobiSLCoeff a b) (jacobiWeight a b) _ _ _ _
    (jacobi_eigenvalue_injective a b m n hmn) hm hn
    (jacobiSLCoeff_eval_one a b) (jacobiSLCoeff_eval_neg_one a b)

/-- Change of variables `x = cos θ` on `[0, π]`. -/
theorem integral_cos_substitution (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ θ in (0 : ℝ)..Real.pi, f (Real.cos θ) * Real.sin θ = ∫ x in (-1 : ℝ)..1, f x := by
  have h := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := Real.pi) (f := Real.cos)
    (f' := fun x => -Real.sin x) (g := f) (fun x _ => Real.hasDerivAt_cos x)
    (by fun_prop) hf.continuousOn
  simp only [Function.comp, mul_neg, intervalIntegral.integral_neg, Real.cos_zero,
    Real.cos_pi] at h
  rw [intervalIntegral.integral_symm (-1 : ℝ) 1] at h
  linarith


/-- `jacobi α β n` has degree at most `n`. -/
lemma natDegree_jacobi_le (α β : ℝ) (n : ℕ) : (jacobi α β n).natDegree ≤ n := by
  unfold jacobi
  refine natDegree_sum_le_of_forall_le _ _ (fun ℓ hℓ => ?_)
  have hℓn : ℓ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
  refine (natDegree_C_mul_le _ _).trans ?_
  have h1 : (X - 1 : ℝ[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : ℝ)
  rw [natDegree_pow, h1]
  simpa using hℓn

/-- The leading coefficient of `jacobi α β n` (coefficient of `X^n`), as a closed form. -/
lemma jacobi_coeff_self (α β : ℝ) (n : ℕ) :
    (jacobi α β n).coeff n =
      (ascPochhammer ℝ n).eval ((n : ℝ) + α + β + 1) / ((n.factorial : ℝ) * 2 ^ n) := by
  have hm : (X - 1 : ℝ[X]).Monic := by simpa using monic_X_sub_C (1 : ℝ)
  have h1 : (X - 1 : ℝ[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : ℝ)
  unfold jacobi
  rw [finsetSum_coeff, Finset.sum_eq_single n]
  · rw [coeff_C_mul]
    have : ((X - 1 : ℝ[X]) ^ n).coeff n = 1 := by
      have := (hm.pow n).coeff_natDegree
      rwa [natDegree_pow, h1, mul_one] at this
    rw [this, mul_one]
    simp [jacobiCoeff]
  · intro ℓ hℓ hne
    have hlt : ℓ < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)) hne
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [natDegree_pow, h1]
    simpa using hlt
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h

/-- For `α, β ≥ 0` the leading coefficient of `jacobi α β n` is nonzero. -/
lemma jacobi_coeff_self_ne_zero (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    (jacobi α β n).coeff n ≠ 0 := by
  rw [jacobi_coeff_self]
  have hp : 0 < (ascPochhammer ℝ n).eval ((n : ℝ) + α + β + 1) :=
    ascPochhammer_pos n _ (by positivity)
  positivity

/-- Core of the orthogonality-to-lower-degree argument, as a functional. -/
lemma jacobi_orth_aux (a b n : ℕ) (hSL : ∀ k, JacobiSL a b k) :
    ∀ k, k < n → ∀ q : ℝ[X], q.natDegree ≤ k →
      ∫ x in (-1 : ℝ)..1, (jacobiWeight a b * q * jacobi (a : ℝ) (b : ℝ) n).eval x = 0 := by
  have horth : ∀ k, k ≠ n → ∫ x in (-1 : ℝ)..1,
      (jacobiWeight a b * jacobi (a : ℝ) (b : ℝ) k * jacobi (a : ℝ) (b : ℝ) n).eval x = 0 := by
    intro k hk
    simpa only [eval_mul] using jacobi_orth_of_SL a b k n (hSL k) (hSL n) hk
  intro k
  induction k with
  | zero =>
    intro hk q hq
    have hq' : q = C (q.coeff 0) := eq_C_of_natDegree_le_zero hq
    have h0 := horth 0 (by omega)
    rw [hq']
    have : ∀ x : ℝ, (jacobiWeight a b * C (q.coeff 0) * jacobi (a : ℝ) (b : ℝ) n).eval x =
        q.coeff 0 * (jacobiWeight a b * jacobi (a : ℝ) (b : ℝ) 0 * jacobi (a : ℝ) (b : ℝ) n).eval x
        := by
      intro x; simp [jacobi_zero]; ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, h0, mul_zero]
  | succ k ih =>
    intro hk q hq
    set P := jacobi (a : ℝ) (b : ℝ) (k + 1) with hP
    have hlead : P.coeff (k + 1) ≠ 0 :=
      jacobi_coeff_self_ne_zero (a : ℝ) (b : ℝ) (by positivity) (by positivity) (k + 1)
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
    have hr0 := ih (by omega) r hrdeg
    have h0 := horth (k + 1) (by omega)
    have hq' : q = r + C c * P := by rw [hr]; ring
    have hsplit : ∀ x : ℝ, (jacobiWeight a b * q * jacobi (a : ℝ) (b : ℝ) n).eval x =
        (jacobiWeight a b * r * jacobi (a : ℝ) (b : ℝ) n).eval x +
          c * (jacobiWeight a b * P * jacobi (a : ℝ) (b : ℝ) n).eval x := by
      intro x
      conv_lhs => rw [hq']
      simp only [eval_mul, eval_add, eval_C]; ring
    simp_rw [hsplit]
    rw [intervalIntegral.integral_add (poly_intervalIntegrable _)
      ((poly_intervalIntegrable _).const_mul c), intervalIntegral.integral_const_mul]
    rw [hr0, h0]; ring

/-- If the Jacobi equation holds in Sturm–Liouville form for all degrees, then `jacobi a b n` is
orthogonal, with respect to the weight `(1-x)^a (1+x)^b`, to every polynomial of degree `< n`. -/
theorem jacobi_orth_lowerDegree (a b n : ℕ) (hSL : ∀ k, JacobiSL a b k) (q : ℝ[X])
    (hq : q.natDegree < n) :
    ∫ x in (-1 : ℝ)..1, (jacobiWeight a b).eval x * q.eval x *
      (jacobi (a : ℝ) (b : ℝ) n).eval x = 0 := by
  have := jacobi_orth_aux a b n hSL q.natDegree hq q le_rfl
  simpa only [eval_mul] using this


/-- info: 'FormalResearch.Special.beta_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms beta_nat

/-- info: 'FormalResearch.Special.sturm_liouville_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sturm_liouville_orth

/-- info: 'FormalResearch.Special.jacobi_orth_of_SL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_orth_of_SL

/-- info: 'FormalResearch.Special.jacobi_coeff_self_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_coeff_self_ne_zero

/-- info: 'FormalResearch.Special.jacobi_orth_lowerDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_orth_lowerDegree

/-- info: 'FormalResearch.Special.integral_cos_substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_cos_substitution

end FormalResearch.Special
