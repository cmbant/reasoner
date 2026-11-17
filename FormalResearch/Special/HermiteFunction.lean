module

public import Mathlib

/-!
# Orthonormal Hermite functions: exact recurrence, ladder relations and parity

The orthonormal Hermite functions are
`φ_n(x) = (π^{1/4} √(n!))⁻¹ · He_n(√2 x) · e^{-x²/2}`, where `He_n = Polynomial.hermite n` is Mathlib's
(probabilists') Hermite polynomial.  This module proves, from `Polynomial.hermite_succ` only, the facts that the
discrete-to-Airy machinery uses (`HermiteAiryEdge`):

* `hermitePsi_rec`: the exact three-term recurrence `√((n+1)/2) φ_{n+1} + √(n/2) φ_{n-1} = x φ_n`
  (a Jacobi chain with off-diagonal `a_k = √(k/2)` and constant diagonal `x`; `n = 0` included with `φ_{-1} = 0`);
* `hermitePhi_neg`: parity `φ_n(-x) = (-1)^n φ_n(x)`;
* `hasDerivAt_hermitePhi_succ`, `hasDerivAt_hermitePsi`: the ladder relations `φ_n' = √(2n) φ_{n-1} - x φ_n
  = √(n/2) φ_{n-1} - √((n+1)/2) φ_{n+1}`.

Not formalised here: the Weber equation `φ_n'' = (x² - 2n - 1) φ_n` (not needed downstream).

**Claim class: proved.**  Not formalised: completeness of `{φ_n}` in `L²(ℝ)`, the Mehler kernel, Cramér's inequality
`|φ_n| ≤ k π^{-1/4}` (`k ≈ 1.0865`; numerically `sup|φ_n| ≤ π^{-1/4}` for `n ≤ 100`) (only a polynomial sup bound is proved, in `HermiteNorm`).
-/

@[expose] public section

open Polynomial Real

namespace FormalResearch.Special

/-- Mathlib's Hermite polynomial `He_n` (integer coefficients) viewed over `ℝ`. -/
noncomputable def heR (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

lemma heR_zero : heR 0 = 1 := by simp [heR, hermite_zero]

lemma heR_succ (n : ℕ) : heR (n + 1) = X * heR n - derivative (heR n) := by
  simp [heR, hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.derivative_map]

/-- `He_{n+1}' = (n+1) He_n`. -/
lemma derivative_heR_succ (n : ℕ) : derivative (heR (n + 1)) = C ((n : ℝ) + 1) * heR n := by
  induction n with
  | zero =>
    rw [heR_succ, heR_zero]; simp
  | succ n ih =>
    have h1 : derivative (heR (n + 2)) =
        heR (n + 1) + X * derivative (heR (n + 1)) - derivative (derivative (heR (n + 1))) := by
      rw [heR_succ (n + 1)]; simp [derivative_mul]
    rw [h1, ih]
    have h2 : derivative (C ((n : ℝ) + 1) * heR n) = C ((n : ℝ) + 1) * derivative (heR n) := by
      simp [derivative_mul]
    rw [h2]
    have h3 : heR (n + 1) = X * heR n - derivative (heR n) := heR_succ n
    have h4 : C ((n : ℝ) + 1 + 1) = C ((n : ℝ) + 1) + 1 := by simp [map_add]
    push_cast
    rw [h4]
    linear_combination (-(C ((n : ℝ) + 1))) * h3

/-- The three-term recurrence `He_{n+2} = X He_{n+1} - (n+1) He_n`. -/
lemma heR_rec (n : ℕ) : heR (n + 2) = X * heR (n + 1) - C ((n : ℝ) + 1) * heR n := by
  rw [heR_succ (n + 1), derivative_heR_succ]

/-- The orthonormal Hermite function `φ_n`. -/
noncomputable def hermitePhi (n : ℕ) (x : ℝ) : ℝ :=
  ((π ^ (1 / 4 : ℝ)) * √(n.factorial : ℝ))⁻¹ * (heR n).eval (√2 * x) * Real.exp (-(x ^ 2 / 2))

/-- `φ_n` for integer `n`, extended by `0` for `n < 0`. -/
noncomputable def hermitePsi (n : ℤ) (x : ℝ) : ℝ := if 0 ≤ n then hermitePhi n.toNat x else 0

lemma hermitePsi_natCast (n : ℕ) (x : ℝ) : hermitePsi (n : ℤ) x = hermitePhi n x := by
  simp [hermitePsi]

lemma hermitePsi_neg {n : ℤ} (hn : n < 0) (x : ℝ) : hermitePsi n x = 0 := by
  simp [hermitePsi, not_le.2 hn]

lemma hermitePhi_zero (x : ℝ) : hermitePhi 0 x = π ^ (-(1 / 4 : ℝ)) * Real.exp (-(x ^ 2 / 2)) := by
  simp [hermitePhi, heR_zero, Real.rpow_neg Real.pi_pos.le]

lemma hermitePhi_one (x : ℝ) : hermitePhi 1 x = √2 * x * hermitePhi 0 x := by
  have : heR 1 = X := by rw [show (1 : ℕ) = 0 + 1 from rfl, heR_succ, heR_zero]; simp
  simp [hermitePhi, this, heR_zero]
  ring

private lemma sqrt_fact_succ (n : ℕ) :
    √((n + 1).factorial : ℝ) = √((n : ℝ) + 1) * √(n.factorial : ℝ) := by
  rw [Nat.factorial_succ]; push_cast
  rw [Real.sqrt_mul (by positivity)]

private lemma pi_quarter_pos : 0 < π ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _

lemma sqrt_half_mul_sqrt_two : √(1 / 2 : ℝ) * √2 = 1 := by
  rw [← Real.sqrt_mul (by norm_num)]; norm_num

/-- Recurrence for `n ≥ 1` in `ℕ` form. -/
lemma hermitePhi_rec_succ (m : ℕ) (x : ℝ) :
    √(((m : ℝ) + 2) / 2) * hermitePhi (m + 2) x + √(((m : ℝ) + 1) / 2) * hermitePhi m x =
      x * hermitePhi (m + 1) x := by
  have hr := heR_rec m
  have hfm : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hs0 : 0 < √(m.factorial : ℝ) := Real.sqrt_pos.2 hfm
  have s1 : √((m + 1).factorial : ℝ) = √((m : ℝ) + 1) * √(m.factorial : ℝ) := sqrt_fact_succ m
  have s2 : √((m + 2).factorial : ℝ) = √((m : ℝ) + 2) * √((m : ℝ) + 1) * √(m.factorial : ℝ) := by
    have := sqrt_fact_succ (m + 1)
    rw [this, sqrt_fact_succ m]; push_cast; ring_nf
  have hev : (heR (m + 2)).eval (√2 * x) =
      √2 * x * (heR (m + 1)).eval (√2 * x) - ((m : ℝ) + 1) * (heR m).eval (√2 * x) := by
    rw [hr]; simp
  have q1 : 0 < √((m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have q2 : 0 < √((m : ℝ) + 2) := Real.sqrt_pos.2 (by positivity)
  have h2 : √((m : ℝ) + 2) ^ 2 = (m : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have h1 : √((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hr2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrp : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have d1 : √(((m : ℝ) + 2) / 2) = √((m : ℝ) + 2) / √2 := Real.sqrt_div (by positivity) _
  have d2 : √(((m : ℝ) + 1) / 2) = √((m : ℝ) + 1) / √2 := Real.sqrt_div (by positivity) _
  have hc := pi_quarter_pos
  simp only [hermitePhi]
  rw [hev, s1, s2, d1, d2]
  field_simp
  linear_combination ((heR m).eval (√2 * x)) * h1

/-- **The exact Hermite recurrence** (`n ≥ 0`): `√((n+1)/2) φ_{n+1} + √(n/2) φ_{n-1} = x φ_n`, with `φ_{-1} = 0`.
In the Jacobi form `a_{k+1} y_{k+1} + a_k y_{k-1} = c y_k`: `a_k = √(k/2)`, `c = x`. -/
theorem hermitePsi_rec (n : ℤ) (hn : 0 ≤ n) (x : ℝ) :
    √(((n : ℝ) + 1) / 2) * hermitePsi (n + 1) x + √((n : ℝ) / 2) * hermitePsi (n - 1) x =
      x * hermitePsi n x := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rcases m with _ | m
  · have h1 : hermitePsi (((0 : ℕ) : ℤ) + 1) x = hermitePhi 1 x := by
      have := hermitePsi_natCast 1 x; simpa using this
    have h0 : hermitePsi ((0 : ℕ) : ℤ) x = hermitePhi 0 x := hermitePsi_natCast 0 x
    rw [h1, h0, hermitePhi_one]
    have e : √((((0 : ℕ) : ℤ) : ℝ) / 2) = 0 := by simp
    have e' : √(((((0 : ℕ) : ℤ) : ℝ) + 1) / 2) = √(1 / 2) := by simp
    rw [e, e']
    linear_combination (x * hermitePhi 0 x) * sqrt_half_mul_sqrt_two
  · have e1 : hermitePsi ((m + 1 : ℕ) : ℤ) x = hermitePhi (m + 1) x := hermitePsi_natCast _ x
    have e2 : hermitePsi (((m + 1 : ℕ) : ℤ) + 1) x = hermitePhi (m + 2) x := by
      have := hermitePsi_natCast (m + 2) x; simpa [add_assoc] using this
    have e3 : hermitePsi (((m + 1 : ℕ) : ℤ) - 1) x = hermitePhi m x := by
      have := hermitePsi_natCast m x; simpa using this
    rw [e1, e2, e3]
    have := hermitePhi_rec_succ m x
    push_cast
    convert this using 3
    ring_nf

lemma hasDerivAt_gauss_half (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (Real.exp (-(x ^ 2 / 2)) * -x) x := by
  have hq : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
    have := ((hasDerivAt_pow 2 x).div_const 2).neg
    refine this.congr_deriv ?_
    norm_num
  exact hq.exp

lemma hasDerivAt_hermitePhi_zero (x : ℝ) : HasDerivAt (hermitePhi 0) (-(x * hermitePhi 0 x)) x := by
  have : hermitePhi 0 = fun x => π ^ (-(1 / 4 : ℝ)) * Real.exp (-(x ^ 2 / 2)) := funext hermitePhi_zero
  rw [this]
  refine ((hasDerivAt_gauss_half x).const_mul (π ^ (-(1 / 4 : ℝ)))).congr_deriv ?_
  beta_reduce; ring

/-- **Ladder relation** `φ_{n+1}' = √(2(n+1)) φ_n - x φ_{n+1}`. -/
lemma hasDerivAt_hermitePhi_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (hermitePhi (n + 1)) (√(2 * ((n : ℝ) + 1)) * hermitePhi n x - x * hermitePhi (n + 1) x) x := by
  have hp : HasDerivAt (fun y : ℝ => (heR (n + 1)).eval (√2 * y))
      (((n : ℝ) + 1) * (heR n).eval (√2 * x) * √2) x := by
    have h1 := (heR (n + 1)).hasDerivAt (√2 * x)
    have h2 : HasDerivAt (fun y : ℝ => √2 * y) √2 x := by simpa using (hasDerivAt_id x).const_mul √2
    have := h1.comp x h2
    refine this.congr_deriv ?_
    rw [derivative_heR_succ]; simp
  have hg := hasDerivAt_gauss_half x
  have h := (hp.mul hg).const_mul (((π ^ (1 / 4 : ℝ)) * √((n + 1).factorial : ℝ))⁻¹)
  have hfun : hermitePhi (n + 1) = fun y => (((π ^ (1 / 4 : ℝ)) * √((n + 1).factorial : ℝ))⁻¹) *
      ((heR (n + 1)).eval (√2 * y) * Real.exp (-(y ^ 2 / 2))) := by
    funext y; simp [hermitePhi, mul_assoc]
  rw [hfun]
  refine h.congr_deriv ?_
  have hfm : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hs0 : 0 < √(n.factorial : ℝ) := Real.sqrt_pos.2 hfm
  have s1 : √((n + 1).factorial : ℝ) = √((n : ℝ) + 1) * √(n.factorial : ℝ) := sqrt_fact_succ n
  have q1 : 0 < √((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have h1 : √((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hc := pi_quarter_pos
  have e2 : √(2 * ((n : ℝ) + 1)) = √2 * √((n : ℝ) + 1) := Real.sqrt_mul (by norm_num) _
  simp only [hermitePhi]
  rw [e2, s1]
  field_simp
  linear_combination (-(√2 * (heR n).eval (√2 * x))) * h1

/-- **Ladder relation, symmetric form** (`n ≥ 0`, `φ_{-1} = 0`):
`φ_n' = √(n/2) φ_{n-1} - √((n+1)/2) φ_{n+1}`. -/
theorem hasDerivAt_hermitePsi (n : ℤ) (hn : 0 ≤ n) (x : ℝ) :
    HasDerivAt (hermitePsi n)
      (√((n : ℝ) / 2) * hermitePsi (n - 1) x - √(((n : ℝ) + 1) / 2) * hermitePsi (n + 1) x) x := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hrec := hermitePsi_rec ((m : ℕ) : ℤ) hn x
  have hm : hermitePsi ((m : ℕ) : ℤ) = hermitePhi m := funext (hermitePsi_natCast m)
  rcases m with _ | m
  · have h1 : hermitePsi (((0 : ℕ) : ℤ) + 1) x = hermitePhi 1 x := by
      have := hermitePsi_natCast 1 x; simpa using this
    have e : √((((0 : ℕ) : ℤ) : ℝ) / 2) = 0 := by simp
    have e' : √(((((0 : ℕ) : ℤ) : ℝ) + 1) / 2) = √(1 / 2) := by simp
    rw [hm, e, e', h1, zero_mul, zero_sub]
    refine (hasDerivAt_hermitePhi_zero x).congr_deriv ?_
    rw [hermitePhi_one]
    have : √(1 / 2 : ℝ) * √2 = 1 := sqrt_half_mul_sqrt_two
    linear_combination (x * hermitePhi 0 x) * this
  · rw [hm]
    have h := hasDerivAt_hermitePhi_succ m x
    refine h.congr_deriv ?_
    have e1 : hermitePsi (((m + 1 : ℕ) : ℤ) - 1) x = hermitePhi m x := by
      have := hermitePsi_natCast m x; simpa using this
    have e2 : hermitePsi (((m + 1 : ℕ) : ℤ) + 1) x = hermitePhi (m + 2) x := by
      have := hermitePsi_natCast (m + 2) x; simpa [add_assoc] using this
    have e3 : hermitePsi ((m + 1 : ℕ) : ℤ) x = hermitePhi (m + 1) x := hermitePsi_natCast _ x
    rw [e1, e2]
    rw [e1, e2, e3] at hrec
    push_cast at hrec ⊢
    have hs : √(2 * ((m : ℝ) + 1)) = 2 * √(((m : ℝ) + 1) / 2) := by
      rw [show 2 * ((m : ℝ) + 1) = 4 * (((m : ℝ) + 1) / 2) by ring, Real.sqrt_mul (by norm_num)]
      have : √(4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [this]
    rw [hs]
    linear_combination hrec

/-- Parity of `He_n`: `He_n(-y) = (-1)^n He_n(y)`. -/
lemma heR_eval_neg (n : ℕ) (y : ℝ) : (heR n).eval (-y) = (-1) ^ n * (heR n).eval y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [heR_zero]
    · have : heR 1 = X := by rw [show (1 : ℕ) = 0 + 1 from rfl, heR_succ, heR_zero]; simp
      simp [this]
    · have hr := heR_rec n
      have e : ∀ z, (heR (n + 2)).eval z = z * (heR (n + 1)).eval z - ((n : ℝ) + 1) * (heR n).eval z := by
        intro z; rw [hr]; simp
      rw [e, e, ih (n + 1) (by omega), ih n (by omega)]
      ring

/-- Parity of the Hermite functions: `φ_n(-x) = (-1)^n φ_n(x)`. -/
theorem hermitePhi_neg (n : ℕ) (x : ℝ) : hermitePhi n (-x) = (-1) ^ n * hermitePhi n x := by
  unfold hermitePhi
  have h : √2 * -x = -(√2 * x) := by ring
  rw [h, heR_eval_neg]
  simp only [neg_sq]
  ring

theorem abs_hermitePhi_neg (n : ℕ) (x : ℝ) : |hermitePhi n (-x)| = |hermitePhi n x| := by
  rw [hermitePhi_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- info: 'FormalResearch.Special.derivative_heR_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.derivative_heR_succ

/-- info: 'FormalResearch.Special.heR_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.heR_rec

/-- info: 'FormalResearch.Special.hermitePsi_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermitePsi_rec

/-- info: 'FormalResearch.Special.hasDerivAt_hermitePhi_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hasDerivAt_hermitePhi_succ

/-- info: 'FormalResearch.Special.hasDerivAt_hermitePsi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hasDerivAt_hermitePsi

end FormalResearch.Special
