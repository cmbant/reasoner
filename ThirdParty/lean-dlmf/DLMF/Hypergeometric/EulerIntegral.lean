/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.Pochhammer

public import DLMF.Hypergeometric.Basic.RealPochhammer
public import Mathlib.Analysis.Normed.Group.Tannery
-- PATCH: removed `public import Carlson.TwoVariable.GaussHypergeometric` (its only use, `gauss_summation`, is removed; closure 100+ modules)
public import DLMF.Hypergeometric.Basic.CutPlane

/-!
# Euler's integral representation (AAR §2.2)

AAR Theorem 2.2.1: for `Re c > Re b > 0` and `|z| < 1`,

$$
{}_2F_1(a,b;c;z)=\frac{\Gamma(c)}{\Gamma(b)\Gamma(c-b)}
\int_0^1 t^{b-1}(1-t)^{c-b-1}(1-zt)^{-a}\,dt.
$$

## Main results

* `chu_vandermonde`: the Chu–Vandermonde sum, DLMF 15.4.24.

## Implementation notes

Euler's integral itself, `ordinaryHypergeometric_eq_integral` (DLMF 15.6.1), is in
`DLMF.Hypergeometric.Basic.CutPlane`.

## References

* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §2.2.
-/

public section

open Complex intervalIntegral MeasureTheory
open scoped Real

noncomputable section

namespace DLMF.Hypergeometric

section GaussSummation

open Filter Nat
open scoped Topology

/-- The value of `₂F₁(a, b; c; 1)` as the sum of the Gauss coefficients. -/
theorem ordinaryHypergeometric_one_eq_tsum (a b c : ℂ) :
    ₂F₁ a b c (1 : ℂ) = ∑' n, gaussHypergeometricCoeff a b c n := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul, one_pow, mul_one]
  congr 1
  funext n
  simp [gaussHypergeometricCoeff, pochhammer, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- For `Re z ≥ 0`, `(Re z)ₖ ≤ ‖(z)ₖ‖`. -/
theorem pochhammer_eval_re_le_norm_pochhammer {z : ℂ} (hz : 0 ≤ z.re) (k : ℕ) :
    (ascPochhammer ℝ k).eval z.re ≤ ‖pochhammer z k‖ := by
  induction k with
  | zero => simp [pochhammer_zero]
  | succ k ih =>
    rw [pochhammer_succ, norm_mul, ascPochhammer_succ_eval]
    have hle : z.re + k ≤ ‖z + k‖ := by
      simpa using re_le_norm (z + k)
    exact mul_le_mul ih hle (by positivity) (norm_nonneg _)

-- PATCH: removed (unused by the target; its closure is 100+ modules): `gauss_summation`, which needs `Carlson.ordinaryHypergeometric_one`. Upstream lines 75-81; see NOTICE.md

end GaussSummation

/-- Helper lemma for `chu_vandermonde`: the Pochhammer form of the Chu–Vandermonde identity. -/
theorem chu_vandermonde_sum (n : ℕ) (b c : ℂ) :
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ k * n.choose k * pochhammer b k * pochhammer (c + k) (n - k) =
          pochhammer (c - b) n := by
  induction n generalizing b c with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    let f : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * pochhammer b k * pochhammer (c + k) (n + 1 - k)
    have hf0 : f 0 = pochhammer c (n + 1) := by
      simp [f, pochhammer_zero]
    have hf_succ (k : ℕ) : f (k + 1) =
        -b * ((-1 : ℂ) ^ k * pochhammer (b + 1) k * pochhammer (c + 1 + k) (n - k)) := by
      have hk : n + 1 - (k + 1) = n - k := by omega
      have harg : (c + (k + 1 : ℕ) : ℂ) = c + 1 + k := by push_cast; ring
      simp only [f, pow_succ, hk, harg, pochhammer_succ_left b k]
      ring
    have hsplit :
        ∑ k ∈ Finset.range (n + 2), (n + 1).choose k * f k =
          ∑ k ∈ Finset.range (n + 1), n.choose k * f k +
            ∑ k ∈ Finset.range (n + 1), n.choose k * f (k + 1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
      have hch : ∀ i ∈ Finset.range (n + 1),
          ((n + 1).choose (i + 1) : ℂ) = n.choose i + n.choose (i + 1) := by
        intro i _
        rw [Nat.choose_succ_succ, Nat.succ_eq_add_one]
        simp
      have hsum := Finset.sum_congr (s₁ := Finset.range (n + 1)) rfl
        (fun i hi => show ((n + 1).choose (i + 1) : ℂ) * f (i + 1) =
            (n.choose i + n.choose (i + 1) : ℂ) * f (i + 1) by rw [hch i hi])
      rw [hsum]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      have htail :
          ∑ i ∈ Finset.range (n + 1), (n.choose (i + 1) : ℂ) * f (i + 1) =
            ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * f k - f 0 := by
        rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
        -- ∑_{i=0}^{n-1} C(n,i+1) f(i+1) = ∑_{j=1}^{n} C(n,j) f j
        have hreindex :=
          Finset.sum_range_succ' (fun j => (n.choose j : ℂ) * f j) n
        -- hreindex: ∑ range (n+1) C(n,j) f j = C(n,0) f 0 + ∑ range n C(n,j+1) f(j+1)
        have : ∑ i ∈ Finset.range n, (n.choose (i + 1) : ℂ) * f (i + 1) =
            ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * f k - f 0 := by
          rw [hreindex]
          simp [Nat.choose_zero_right]
        simpa using this
      rw [htail]
      ring
    have hfirst :
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * f k =
          (c + n) * pochhammer (c - b) n := by
      have hterm : ∀ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * f k =
            (c + n) * ((-1 : ℂ) ^ k * n.choose k * pochhammer b k *
                pochhammer (c + k) (n - k)) := by
        intro k hk
        have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hsub : n + 1 - k = (n - k) + 1 := by omega
        simp only [f, hsub, pochhammer_succ (c + k) (n - k)]
        have : (c + k + (n - k : ℕ) : ℂ) = c + n := by
          rw [Nat.cast_sub hk']
          ring
        rw [this]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ih]
    have hsecond :
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * f (k + 1) =
          -b * pochhammer (c - b) n := by
      have hterm : ∀ k ∈ Finset.range (n + 1),
          (n.choose k : ℂ) * f (k + 1) =
            -b * ((-1 : ℂ) ^ k * n.choose k * pochhammer (b + 1) k *
              pochhammer ((c + 1) + k) (n - k)) := by
        intro k _
        rw [hf_succ]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ih (b + 1) (c + 1)]
      simp
    -- Reassemble.
    have hsum := hsplit
    -- The left-hand side of `hsplit` is the `n.succ` instance of the claimed sum.
    have hgoal :
        ∑ k ∈ Finset.range (n + 2),
          (-1 : ℂ) ^ k * (n + 1).choose k * pochhammer b k * pochhammer (c + k) (n + 1 - k) =
          ∑ k ∈ Finset.range (n + 2), (n + 1).choose k * f k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [f]
      ring
    rw [hgoal, hsum, hfirst, hsecond, pochhammer_succ]
    ring

/-- Chu–Vandermonde: the terminating Gauss sum, AAR as the case `a = -n` of Gauss summation. -/
@[dlmf 15.4.E24]
theorem chu_vandermonde (n : ℕ) {b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    ₂F₁ (-n : ℂ) b c (1 : ℂ) = pochhammer (c - b) n / pochhammer c n := by
  have hcn := pochhammer_ne_zero_of_not_neg_nat hc n
  rw [ordinaryHypergeometric_eq_sum_neg_nat, eq_div_iff hcn]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      gaussHypergeometricCoeff (-(n : ℂ)) b c k * (1 : ℂ) ^ k * pochhammer c n =
        (-1 : ℂ) ^ k * n.choose k * pochhammer b k * pochhammer (c + k) (n - k) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hck := pochhammer_ne_zero_of_not_neg_nat hc k
    have hadd := pochhammer_add c k (n - k)
    rw [Nat.add_sub_of_le hk'] at hadd
    rw [one_pow, mul_one, gaussHypergeometricCoeff_neg_nat]
    field_simp [hck]
    rw [hadd]
    ring
  rw [mul_comm, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun k hk => ?_).trans (chu_vandermonde_sum n b c)
  convert hterm k hk using 1
  ring

/-- The binomial theorem for rising factorials (Chu–Vandermonde). -/
theorem pochhammer_add_binomial_sum (u v : ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * pochhammer u j * pochhammer v (n - j) =
        pochhammer (u + v) n := by
  have hchu := chu_vandermonde_sum n v (1 - u - n)
  have href := pochhammer_reflect (u + v) n
  rw [show 1 - (u + v) - (n : ℂ) = 1 - u - n - v by ring] at href
  rw [← hchu] at href
  have hs : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [← Finset.sum_range_reflect]
  have key : pochhammer (u + v) n = (-1) ^ n * ∑ k ∈ Finset.range (n + 1),
      (-1) ^ k * (n.choose k : ℂ) * pochhammer v k * pochhammer (1 - u - n + k) (n - k) := by
    rw [href]; linear_combination (-(pochhammer (u + v) n)) * hs
  rw [key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm hkn, Nat.sub_sub_self hkn]
  have hr := pochhammer_reflect u (n - k)
  rw [show 1 - u - ((n - k : ℕ) : ℂ) = 1 - u - n + k by push_cast [Nat.cast_sub hkn]; ring] at hr
  rw [hr]
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add]
  have h2 : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hm2 : ((-1 : ℂ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (-(((k + m).choose k : ℂ) * pochhammer u m * pochhammer v k)) * hm2 +
    (-(((k + m).choose k : ℂ) * pochhammer u m * pochhammer v k * ((-1 : ℂ) ^ m) ^ 2)) * h2

end DLMF.Hypergeometric
