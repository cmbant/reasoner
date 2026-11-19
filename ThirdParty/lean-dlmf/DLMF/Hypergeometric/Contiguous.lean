/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.RealPochhammer
public import DLMF.Hypergeometric.Basic.ParameterAnalyticity

/-!
# Contiguous relations (AAR §2.5 and §3.7)

Gauss listed fifteen relations among `₂F₁(a,b;c;z)` and the six functions obtained by shifting
one parameter by `±1`. This file proves the basic ones; the others are in
`DLMF.Hypergeometric.Derivatives`.

## Main results

* `ordinaryHypergeometric_mul_deriv_eq_shift_a`: `z F' = a (F(a+) - F)` (AAR (2.5.5)).
* `ordinaryHypergeometric_mul_one_sub_mul_deriv_eq`: `z(1-z) F' = (c-a) F(a-) + (a-c+bz) F`,
  DLMF 15.5.20 (AAR (2.5.8)).
* `contiguous_a`: the three-term relation in `a`, DLMF 15.5.11.

## Implementation notes

`contiguous_shift_b` (DLMF 15.5.16_5) and `contiguous_c` (shifting the denominator parameter)
are in `DLMF.Hypergeometric.Basic.ParameterAnalyticity`.

## References

* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §2.5 and §3.7.
-/

public section

open Complex

noncomputable section

namespace DLMF.Hypergeometric

/-- Helper lemma for AAR (2.5.5): the coefficient identity
`n (a)_n = a ((a+1)_n - (a)_n)`. -/
theorem gaussHypergeometricCoeff_AAR_2_5_5 {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n : ℂ) * gaussHypergeometricCoeff a b c n =
      a * (gaussHypergeometricCoeff (a + 1) b c n - gaussHypergeometricCoeff a b c n) := by
  cases n with
  | zero => simp [gaussHypergeometricCoeff, pochhammer_zero]
  | succ n =>
    have hcp := pochhammer_ne_zero_of_not_neg_nat hc (n + 1)
    have hf : ((n + 1).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (n + 1).factorial_ne_zero
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp only [gaussHypergeometricCoeff, pochhammer_succ_left a n, pochhammer_succ (a + 1) n]
    field_simp [hcp, hf, hn]
    push_cast
    ring

/-- AAR (2.5.5): `z · ∂F/∂z = a (F(a+) - F)`. -/
theorem ordinaryHypergeometric_mul_deriv_eq_shift_a {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    z * deriv (₂F₁ a b c) z = a * (₂F₁ (a + 1) b c z - ₂F₁ a b c z) := by
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hf := hasFPowerSeriesOnBall_ordinaryHypergeometric a b c
  have hL := hf.hasSum_z_mul_deriv hz'
  have hs1 := (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + 1) b c).hasSum_mul_pow hz'
  have hs0 := hf.hasSum_mul_pow hz'
  have hR := (hs1.sub hs0).mul_left a
  have hfun : (fun n : ℕ => (n : ℂ) * gaussHypergeometricCoeff a b c n * z ^ n) =
      fun n => a * (gaussHypergeometricCoeff (a + 1) b c n * z ^ n -
          gaussHypergeometricCoeff a b c n * z ^ n) := by
    funext n
    have hcoeff := gaussHypergeometricCoeff_AAR_2_5_5 (a := a) (b := b) (c := c) hc n
    linear_combination hcoeff * z ^ n
  have hL' : HasSum (fun n =>
      a * (gaussHypergeometricCoeff (a + 1) b c n * z ^ n -
          gaussHypergeometricCoeff a b c n * z ^ n))
      (z * deriv (₂F₁ a b c) z) := by
    rwa [hfun] at hL
  have hR' : HasSum (fun n =>
      a * (gaussHypergeometricCoeff (a + 1) b c n * z ^ n -
          gaussHypergeometricCoeff a b c n * z ^ n))
      (a * (₂F₁ (a + 1) b c z - ₂F₁ a b c z)) := by
    simpa [mul_sub] using hR
  exact hL'.unique hR'

/-- Helper lemma for AAR (2.5.8). -/
theorem gaussHypergeometricCoeff_AAR_2_5_8 {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n + 1 : ℂ) * gaussHypergeometricCoeff a b c (n + 1) - (n : ℂ) *
        gaussHypergeometricCoeff a b c n -
      (c - a) * gaussHypergeometricCoeff (a - 1) b c (n + 1) -
      (a - c) * gaussHypergeometricCoeff a b c (n + 1) -
      b * gaussHypergeometricCoeff a b c n = 0 := by
  have hcp := pochhammer_ne_zero_of_not_neg_nat hc n
  have hcp1 := pochhammer_ne_zero_of_not_neg_nat hc (n + 1)
  have hf0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hcn : c + (n : ℂ) ≠ 0 := by
    simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hc n
  have ha : pochhammer a (n + 1) = pochhammer a n * (a + n) := pochhammer_succ a n
  have ha1 : pochhammer (a - 1) (n + 1) = (a - 1) * pochhammer a n := by
    simpa [sub_add_cancel] using pochhammer_succ_left (a - 1) n
  have hb : pochhammer b (n + 1) = pochhammer b n * (b + n) := pochhammer_succ b n
  have hc' : pochhammer c (n + 1) = pochhammer c n * (c + n) := pochhammer_succ c n
  have hfac : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm]
  have hnum :
      (n + 1 : ℂ) * (a + n) * (b + n) - (n : ℂ) * (c + n) * (n + 1) -
        (c - a) * (a - 1) * (b + n) - (a - c) * (a + n) * (b + n) -
        b * (c + n) * (n + 1) = 0 := by
    ring
  have hden : pochhammer c n * (n.factorial : ℂ) * (n + 1) * (c + n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hcp hf0) hn) hcn
  simp only [gaussHypergeometricCoeff]
  rw [ha, ha1, hb, hc', hfac]
  apply mul_left_cancel₀ hden
  rw [mul_zero]
  field_simp [hcp, hf0, hn, hcn]
  linear_combination pochhammer a n * pochhammer b n * hnum

/-- AAR (2.5.8): `z(1-z) F' = (c-a) F(a-) + (a-c+bz) F`. -/
@[dlmf 15.5.E20]
theorem ordinaryHypergeometric_mul_one_sub_mul_deriv_eq {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    z * (1 - z) * deriv (₂F₁ a b c) z =
      (c - a) * ₂F₁ (a - 1) b c z + (a - c + b * z) * ₂F₁ a b c z := by
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hf := hasFPowerSeriesOnBall_ordinaryHypergeometric a b c
  have hFz := hf.hasSum_z_mul_deriv hz'
  have hF := hf.hasSum_mul_pow hz'
  have hFm := (hasFPowerSeriesOnBall_ordinaryHypergeometric (a - 1) b c).hasSum_mul_pow hz'
  let d : ℕ → ℂ := fun n =>
    match n with
    | 0 => 0
    | n + 1 => (n : ℂ) * gaussHypergeometricCoeff a b c n
  have hd0 : d 0 = 0 := rfl
  have hds : HasSum (fun n : ℕ => d (n + 1) * z ^ n) (z * deriv (₂F₁ a b c) z) := by
    have hfun : (fun n : ℕ => d (n + 1) * z ^ n) =
        fun n : ℕ => (n : ℂ) * gaussHypergeometricCoeff a b c n * z ^ n := by
      funext n
      simp [d]
    rwa [hfun]
  have hzz := HasSum.mul_pow_shift (c := d) (s := z * deriv (₂F₁ a b c) z) hds hd0
  have hBz : HasSum (fun n =>
      (match n with
        | 0 => (0 : ℂ)
        | n + 1 => b * gaussHypergeometricCoeff a b c n) * z ^ n)
      (z * (b * ₂F₁ a b c z)) :=
    HasSum.mul_pow_shift
      (c := fun n => match n with | 0 => 0 | n + 1 => b * gaussHypergeometricCoeff a b c n)
      (s := b * ₂F₁ a b c z)
      (by
        have hfun : (fun n : ℕ =>
            (match (n + 1) with
              | 0 => (0 : ℂ)
              | k + 1 => b * gaussHypergeometricCoeff a b c k) * z ^ n) =
            fun n : ℕ => b * (gaussHypergeometricCoeff a b c n * z ^ n) := by
          funext n
          simp
          ring
        rw [hfun]
        exact hF.mul_left b) rfl
  have hleft := hFz.sub hzz
  have hright := ((hFm.mul_left (c - a)).add (hF.mul_left (a - c))).add hBz
  have hcomb := hleft.sub hright
  have hfun : (fun n : ℕ =>
      (n : ℂ) * gaussHypergeometricCoeff a b c n * z ^ n - d n * z ^ n -
        ((c - a) * (gaussHypergeometricCoeff (a - 1) b c n * z ^ n) +
          (a - c) * (gaussHypergeometricCoeff a b c n * z ^ n) +
          (match n with
            | 0 => (0 : ℂ)
            | n + 1 => b * gaussHypergeometricCoeff a b c n) * z ^ n)) =
      fun _ => 0 := by
    funext n
    cases n with
    | zero => simp [d, gaussHypergeometricCoeff, pochhammer_zero]
    | succ n =>
      have hcoeff := gaussHypergeometricCoeff_AAR_2_5_8 (a := a) (b := b) (c := c) hc n
      simp [d]
      have hzpow := congrArg (fun t : ℂ => t * z ^ (n + 1)) hcoeff
      convert hzpow using 1
      · ring
      · simp
  have hsum' : HasSum (fun _ : ℕ => (0 : ℂ))
      (z * deriv (₂F₁ a b c) z - z * (z * deriv (₂F₁ a b c) z) -
        ((c - a) * ₂F₁ (a - 1) b c z + (a - c) * ₂F₁ a b c z +
          z * (b * ₂F₁ a b c z))) := by
    rwa [hfun] at hcomb
  have hval := hsum'.tsum_eq
  rw [tsum_zero] at hval
  have hrewrite : z * (1 - z) * deriv (₂F₁ a b c) z =
      z * deriv (₂F₁ a b c) z - z * (z * deriv (₂F₁ a b c) z) := by ring
  have hrewrite' : (c - a) * ₂F₁ (a - 1) b c z + (a - c + b * z) * ₂F₁ a b c z =
      (c - a) * ₂F₁ (a - 1) b c z + (a - c) * ₂F₁ a b c z +
        z * (b * ₂F₁ a b c z) := by ring
  rw [hrewrite, hrewrite']
  exact sub_eq_zero.mp hval.symm

/-- Gauss's three-term contiguous relation in the `a`-parameter (DLMF 15.5.11),
obtained as in AAR §2.5 by equating (2.5.5) and (2.5.8). The denominator parameter
is required not to be a nonpositive integer. -/
@[dlmf 15.5.E11]
theorem contiguous_a {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    (c - a) * ₂F₁ (a - 1) b c z + (2 * a - c + (b - a) * z) * ₂F₁ a b c z +
      a * (z - 1) * ₂F₁ (a + 1) b c z = 0 := by
  have h5 := ordinaryHypergeometric_mul_deriv_eq_shift_a (a := a) (b := b) (c := c) hc hz
  have h8 :=
    ordinaryHypergeometric_mul_one_sub_mul_deriv_eq (a := a) (b := b) (c := c) hc hz
  have hmul : (1 - z) * (z * deriv (₂F₁ a b c) z) =
      z * (1 - z) * deriv (₂F₁ a b c) z := by ring
  have heq : (1 - z) * a * (₂F₁ (a + 1) b c z - ₂F₁ a b c z) =
      (c - a) * ₂F₁ (a - 1) b c z + (a - c + b * z) * ₂F₁ a b c z := by
    calc
      _ = (1 - z) * (z * deriv (₂F₁ a b c) z) := by rw [h5]; ring
      _ = z * (1 - z) * deriv (₂F₁ a b c) z := hmul
      _ = _ := h8
  have hrearr :
      (c - a) * ₂F₁ (a - 1) b c z + (2 * a - c + (b - a) * z) * ₂F₁ a b c z +
          a * (z - 1) * ₂F₁ (a + 1) b c z =
        (c - a) * ₂F₁ (a - 1) b c z + (a - c + b * z) * ₂F₁ a b c z -
          (1 - z) * a * (₂F₁ (a + 1) b c z - ₂F₁ a b c z) := by
    ring
  rw [hrearr, heq]
  ring

end DLMF.Hypergeometric
