/-
Copyright (c) 2026 Antony Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antony Lewis
-/
module

public import PhyslibAlpha.Mathematics.SpecialFunctions.Hypergeometric.Sears

/-!

# The Sears transformation for the sums of Racah's formula

The single sum `Xs` and Racah's sum `racahSum6` are, up to explicit factorials, two terminating
balanced `₄F₃(1)` series related by one Sears transformation.

## i. Overview

Write `a = v + w + k₁`, `b = z + k₁ + k₃`, `c = u + w + k₃`, `K = w + k₁ + k₃` with six free
natural numbers `k₁ k₃ u v w z`, and `N = u + v + w + z + k₁ + k₃ = a + b + c - K`. This
parametrization is exactly the region `k₁ + k₃ ≤ min b K` of the admissible `(a, b, c, K, k₁, k₃)`,
where `β₁ = N` is the smallest of Racah's three quadrilateral sums. In it

* `XsSeries` is the `₄F₃(1)` with upper parameters `-k₃, -k₁, u+w+1, v+w+1` and lower parameters
  `w+1, -(z+k₁+k₃), u+v+w+z+2`, which equals `Xs` up to explicit factorials;
* `racahSeries` is the `₄F₃(1)` with upper parameters `-k₃, -k₁, -u, -v` and lower parameters
  `w+1, z+1, -(N+1)`, which equals `racahSum6 (N-u) (N-k₃) (N-v) (N-k₁) N (N+z) (N+w)` summed from
  the top `t = N - s`, up to explicit factorials.

Both series are balanced. The Sears transformation `Hypergeometric.sears`, with `n = k₃`,
`A = -k₁`, `B = -u`, `C = -v`, `d = w + 1`, `e = z + 1`, `f = -(N + 1)`, gives
`XsSeries * searsPrefactor = racahSeries` (`sears_instance`), where the prefactor is the ratio of
Pochhammer symbols of the transformation. The identification of the two series with `Xs` and
`racahSum6`, and the matching of the constants, are in `XsSeries`, `RacahSumSeries` and `XsRacah`.

## ii. Key results

- `XsSeries`, `racahSeries`: the two `₄F₃(1)` series.
- `sears_instance`: `XsSeries * searsPrefactor = racahSeries`.

## iii. Table of contents

- A. The two series
- B. The Sears transformation

## iv. References

- G. E. Andrews, R. Askey, R. Roy, *Special Functions*, Cambridge University Press (1999),
  §3.3.
- W. N. Bailey, *Generalized Hypergeometric Series*, Cambridge University Press (1935),
  Chapter 4.

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open Finset PhyslibAlpha.Hypergeometric

/-!

## A. The two series

-/

/-- The `₄F₃` form of `Xs`. -/
def XsSeries (k1 k3 u v w z : ℕ) : ℝ :=
  ∑ k ∈ range (k3 + 1), rf (-(k3 : ℝ)) k * rf (-(k1 : ℝ)) k * rf ((u : ℝ) + w + 1) k *
    rf ((v : ℝ) + w + 1) k / ((k.factorial : ℝ) * rf ((w : ℝ) + 1) k * rf (-((z : ℝ) + k1 + k3)) k *
      rf ((u : ℝ) + v + w + z + 2) k)

/-- The `₄F₃` form of Racah's sum, summed from the top. -/
def racahSeries (k1 k3 u v w z : ℕ) : ℝ :=
  ∑ k ∈ range (k3 + 1), rf (-(k3 : ℝ)) k * rf (-(k1 : ℝ)) k * rf (-(u : ℝ)) k * rf (-(v : ℝ)) k /
    ((k.factorial : ℝ) * rf ((w : ℝ) + 1) k * rf ((z : ℝ) + 1) k *
      rf (-((u : ℝ) + v + w + z + k1 + k3 + 1)) k)

/-- The prefactor of the Sears transformation in this instance. -/
def searsPrefactor (k1 k3 u v w z : ℕ) : ℝ :=
  rf ((z : ℝ) + 1 + k1) k3 * rf (-((u : ℝ) + v + w + z + k1 + k3 + 1) + k1) k3 /
    (rf ((z : ℝ) + 1) k3 * rf (-((u : ℝ) + v + w + z + k1 + k3 + 1)) k3)

/-!

## B. The Sears transformation

-/

/-- The Sears transformation in the instance of `Xs` and Racah's sum: the `₄F₃(1)` form of `Xs`
times `searsPrefactor` is the `₄F₃(1)` form of Racah's sum. -/
lemma sears_instance (k1 k3 u v w z : ℕ) :
    XsSeries k1 k3 u v w z * searsPrefactor k1 k3 u v w z = racahSeries k1 k3 u v w z := by
  set N : ℝ := (u : ℝ) + v + w + z + k1 + k3 with hN
  have hbal : ((w : ℝ) + 1) + ((z : ℝ) + 1) + (-(N + 1)) =
      -(k1 : ℝ) + (-(u : ℝ)) + (-(v : ℝ)) - k3 + 1 := by
    rw [hN]; ring
  have hNk : k3 ≤ u + v + w + z + k1 + k3 + 1 := by omega
  have hd : rf ((w : ℝ) + 1) k3 ≠ 0 := (rf_pos (by positivity) k3).ne'
  have he : rf ((z : ℝ) + 1) k3 ≠ 0 := (rf_pos (by positivity) k3).ne'
  have hf : rf (-(N + 1)) k3 ≠ 0 := by
    have := rf_ne_zero_neg (m := u + v + w + z + k1 + k3 + 1) (k := k3) hNk
    convert this using 2; rw [hN]; push_cast; ring
  have hA2 : rf (-(k1 : ℝ) - ((z : ℝ) + 1) - k3 + 1) k3 ≠ 0 := by
    have := rf_ne_zero_neg (m := z + k1 + k3) (k := k3) (by omega)
    convert this using 2; push_cast; ring
  have hA3 : rf (-(k1 : ℝ) - (-(N + 1)) - k3 + 1) k3 ≠ 0 := by
    have h0 : (0 : ℝ) ≤ (u : ℝ) + v + w + z := by positivity
    have : 0 < -(k1 : ℝ) - (-(N + 1)) - k3 + 1 := by rw [hN]; linarith
    exact (rf_pos this k3).ne'
  have h1 : ∀ k, k ≤ k3 → rf (1 + (-(u : ℝ)) + (-(v : ℝ)) - ((w : ℝ) + 1) - k) k ≠ 0 := by
    intro k hk
    have := rf_ne_zero_neg (m := u + v + w + k) (k := k) (by omega)
    convert this using 2; push_cast; ring
  have key := sears k3 (-(k1 : ℝ)) (-(u : ℝ)) (-(v : ℝ)) ((w : ℝ) + 1) ((z : ℝ) + 1) (-(N + 1))
    hbal hd he hf hA2 hA3 h1
  have e1 : (w : ℝ) + 1 - (-(u : ℝ)) = (u : ℝ) + w + 1 := by ring
  have e2 : (w : ℝ) + 1 - (-(v : ℝ)) = (v : ℝ) + w + 1 := by ring
  have e3 : -(k1 : ℝ) - ((z : ℝ) + 1) - k3 + 1 = -((z : ℝ) + k1 + k3) := by ring
  have e4 : -(k1 : ℝ) - (-(N + 1)) - k3 + 1 = (u : ℝ) + v + w + z + 2 := by rw [hN]; try ring
  have e5 : (z : ℝ) + 1 - (-(k1 : ℝ)) = (z : ℝ) + 1 + k1 := by ring
  have e6 : -(N + 1) - (-(k1 : ℝ)) = -((u : ℝ) + v + w + z + k1 + k3 + 1) + k1 := by rw [hN]; ring
  have e7 : -(N + 1) = -((u : ℝ) + v + w + z + k1 + k3 + 1) := by rw [hN]
  rw [e1, e2, e3, e4, e5, e6] at key
  rw [e7] at key
  exact key

end PhyslibAlpha.Sl2
