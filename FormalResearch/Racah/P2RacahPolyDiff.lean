module

public import Mathlib

/-!
# The terminating Racah polynomial and its difference equation (Weyl P2,
`eq:physicalRacah4F3`, `eq:RacahPolyEigenvalue`: the polynomial side)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, subsection *Explicit physical Racah-polynomial
realization*.  The paper takes the standard terminating Racah polynomial (DLMF/Koekoek-Swarttouw)
```
R_n(λ(x); α,β,γ,δ) = ₄F₃(-n, n+α+β+1, -x, x+γ+δ+1; α+1, β+δ+1, γ+1; 1)
```
as the definition of `Q^R_r(y)`.  This file defines it as a finite sum of rising factorials and proves
the classical difference equation (generic real parameters, no Racah-lattice hypotheses):

`n(n+α+β+1) R_n(x) = B(x) (R_n(x+1) - R_n(x)) + D(x) (R_n(x-1) - R_n(x))`

with `B(x) = (x+α+1)(x+β+δ+1)(x+γ+1)(x+γ+δ+1)/((2x+γ+δ+1)(2x+γ+δ+2))` and
`D(x) = x(x-α+γ+δ)(x-β+γ)(x+δ)/((2x+γ+δ)(2x+γ+δ+1))`.

## Dictionary

| paper / standard | Lean |
|---|---|
| `(z)_k` | `rf z k` |
| `₄F₃(-n, n+α+β+1, -x, x+γ+δ+1; α+1, β+δ+1, γ+1; 1)` | `racahPoly α β γ δ n x` |
| `B(x)`, `D(x)` | `racahB α β γ δ x`, `racahD α β γ δ x` |

The proof is termwise: `racahPhi_diff` gives `L φ_k = k(k+α+β+1) φ_k - k(α+k)(β+δ+k)(γ+k) φ_{k-1}` on the
basis `φ_k(x) = (-x)_k (x+γ+δ+1)_k`, and the coefficients of the `₄F₃` telescope (`racahCoef_succ`).
-/

@[expose] public section

namespace FormalResearch.Racah.RacahPoly

/-- The rising factorial (Pochhammer symbol) `(z)_k = z (z+1) ⋯ (z+k-1)`. -/
noncomputable def rf (z : ℝ) (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (z + i)

lemma rf_zero (z : ℝ) : rf z 0 = 1 := by simp [rf]

lemma rf_succ (z : ℝ) (k : ℕ) : rf z (k + 1) = rf z k * (z + k) := by
  simp [rf, Finset.prod_range_succ]

lemma rf_succ' (z : ℝ) (k : ℕ) : rf z (k + 1) = z * rf (z + 1) k := by
  unfold rf
  rw [Finset.prod_range_succ', mul_comm]
  simp only [Nat.cast_zero, add_zero]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast; ring

/-- The `k`-th term of the series (without the coefficient): `(-x)_k (x+γ+δ+1)_k`. -/
noncomputable def racahPhi (γ δ : ℝ) (k : ℕ) (x : ℝ) : ℝ := rf (-x) k * rf (x + γ + δ + 1) k

/-- The coefficient `(-n)_k (n+α+β+1)_k / ((α+1)_k (β+δ+1)_k (γ+1)_k k!)` of the `₄F₃`. -/
noncomputable def racahCoef (α β γ δ : ℝ) (n k : ℕ) : ℝ :=
  rf (-(n : ℝ)) k * rf (n + α + β + 1) k /
    (rf (α + 1) k * rf (β + δ + 1) k * rf (γ + 1) k * (k.factorial : ℝ))

/-- The standard terminating Racah polynomial
`R_n(λ(x); α,β,γ,δ) = ₄F₃(-n, n+α+β+1, -x, x+γ+δ+1; α+1, β+δ+1, γ+1; 1)`
(Koekoek-Swarttouw 9.2.1; DLMF 18.26.1), as a finite sum over `k = 0..n`. -/
noncomputable def racahPoly (α β γ δ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), racahCoef α β γ δ n k * racahPhi γ δ k x

/-- `B(x)` of the Racah difference equation. -/
noncomputable def racahB (α β γ δ x : ℝ) : ℝ :=
  (x + α + 1) * (x + β + δ + 1) * (x + γ + 1) * (x + γ + δ + 1) /
    ((2 * x + γ + δ + 1) * (2 * x + γ + δ + 2))

/-- `D(x)` of the Racah difference equation. -/
noncomputable def racahD (α β γ δ x : ℝ) : ℝ :=
  x * (x - α + γ + δ) * (x - β + γ) * (x + δ) / ((2 * x + γ + δ) * (2 * x + γ + δ + 1))

/-- The difference operator `(L f)(x) = B(x) (f(x+1) - f(x)) + D(x) (f(x-1) - f(x))`. -/
noncomputable def racahL (α β γ δ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  racahB α β γ δ x * (f (x + 1) - f x) + racahD α β γ δ x * (f (x - 1) - f x)

set_option maxRecDepth 20000 in
/-- `L φ_{j+1} = (j+1)(j+α+β+2) φ_{j+1} - (j+1)(α+j+1)(β+δ+j+1)(γ+j+1) φ_j`. -/
theorem racahPhi_diff (α β γ δ x : ℝ) (j : ℕ) (h0 : x ≠ 0 → 2 * x + γ + δ ≠ 0)
    (h1 : 2 * x + γ + δ + 1 ≠ 0) (h2 : 2 * x + γ + δ + 2 ≠ 0) :
    racahL α β γ δ (racahPhi γ δ (j + 1)) x =
      (j + 1) * (j + 1 + α + β + 1) * racahPhi γ δ (j + 1) x -
        (j + 1) * (α + j + 1) * (β + δ + j + 1) * (γ + j + 1) * racahPhi γ δ j x := by
  set w : ℝ := x + γ + δ + 1 with hw
  set u : ℝ := rf (-x) j with hu
  set u' : ℝ := rf (-x + 1) j with hu'
  set v : ℝ := rf w j with hv
  set v' : ℝ := rf (w + 1) j with hv'
  have R1 : u * (j - x) = (-x) * u' := by
    have := rf_succ (-x) j
    rw [rf_succ'] at this
    simp only [hu, hu']
    linear_combination -this
  have R2 : v * (w + j) = w * v' := by
    have := rf_succ w j
    rw [rf_succ'] at this
    simp only [hv, hv']
    linear_combination -this
  have p0 : racahPhi γ δ j x = u * v := rfl
  have p1 : racahPhi γ δ (j + 1) x = u * (-x + j) * (v * (w + j)) := by
    unfold racahPhi
    rw [rf_succ, rf_succ]
  have p2 : racahPhi γ δ (j + 1) (x + 1) = (-x - 1) * u * (v' * (w + 1 + j)) := by
    unfold racahPhi
    have e1 : rf (-(x + 1)) (j + 1) = (-x - 1) * u := by
      have : -(x + 1) + 1 = -x := by ring
      rw [rf_succ', this]; ring
    have e2 : rf (x + 1 + γ + δ + 1) (j + 1) = v' * (w + 1 + j) := by
      rw [rf_succ]
      have : x + 1 + γ + δ + 1 = w + 1 := by rw [hw]; ring
      rw [this]
    rw [e1, e2]
  have p3 : racahPhi γ δ (j + 1) (x - 1) = u' * (-x + 1 + j) * ((w - 1) * v) := by
    unfold racahPhi
    have e1 : rf (-(x - 1)) (j + 1) = u' * (-x + 1 + j) := by
      have : -(x - 1) = -x + 1 := by ring
      rw [this, rf_succ]
    have e2 : rf (x - 1 + γ + δ + 1) (j + 1) = (w - 1) * v := by
      rw [rf_succ']
      have : x - 1 + γ + δ + 1 = w - 1 := by rw [hw]; ring
      rw [this]; have : w - 1 + 1 = w := by ring
      rw [this]
    rw [e1, e2]
  have eB : w * racahPhi γ δ (j + 1) (x + 1) =
      (-x - 1) * (w + 1 + j) * (w + j) * (u * v) := by
    rw [p2]; linear_combination ((-x - 1) * u * (w + 1 + j)) * (-R2)
  have eD : x * racahPhi γ δ (j + 1) (x - 1) =
      (x - j) * (-x + 1 + j) * (w - 1) * (u * v) := by
    rw [p3]; linear_combination ((-x + 1 + j) * (w - 1) * v) * R1
  have eB' : racahB α β γ δ x * racahPhi γ δ (j + 1) (x + 1) =
      (x + α + 1) * (x + β + δ + 1) * (x + γ + 1) / ((2 * x + γ + δ + 1) * (2 * x + γ + δ + 2)) *
        (w * racahPhi γ δ (j + 1) (x + 1)) := by
    unfold racahB; rw [hw]; ring
  have eD' : racahD α β γ δ x * racahPhi γ δ (j + 1) (x - 1) =
      (x - α + γ + δ) * (x - β + γ) * (x + δ) / ((2 * x + γ + δ) * (2 * x + γ + δ + 1)) *
        (x * racahPhi γ δ (j + 1) (x - 1)) := by
    unfold racahD; ring
  have eB'' : racahB α β γ δ x * racahPhi γ δ (j + 1) x =
      (x + α + 1) * (x + β + δ + 1) * (x + γ + 1) / ((2 * x + γ + δ + 1) * (2 * x + γ + δ + 2)) *
        (w * racahPhi γ δ (j + 1) x) := by
    unfold racahB; rw [hw]; ring
  have eD'' : racahD α β γ δ x * racahPhi γ δ (j + 1) x =
      (x - α + γ + δ) * (x - β + γ) * (x + δ) / ((2 * x + γ + δ) * (2 * x + γ + δ + 1)) *
        (x * racahPhi γ δ (j + 1) x) := by
    unfold racahD; ring
  unfold racahL
  by_cases hx : x = 0
  · -- the endpoint `x = 0`: `D(0) = 0` and `φ_{j+1}(0) = 0`
    have hD0 : racahD α β γ δ x = 0 := by simp [racahD, hx]
    have huj : u * (j : ℝ) = 0 := by rw [hx] at R1; linear_combination R1
    have hz : racahPhi γ δ (j + 1) x = 0 := by
      rw [p1, hx]
      linear_combination (v * (w + j)) * huj
    rw [hD0, zero_mul, add_zero, hz, sub_zero, mul_zero, zero_sub, p0, eB', eB]
    clear_value u u' v v' w
    subst hx
    rcases j with _ | j
    · have hu1 : u = 1 := by rw [hu]; simp [rf]
      have hv1 : v = 1 := by rw [hv]; simp [rf]
      rw [hu1, hv1, hw]
      have h1' : γ + δ + 1 ≠ 0 := by simpa using h1
      have h2' : γ + δ + 2 ≠ 0 := by simpa using h2
      simp only [mul_zero, zero_add, Nat.cast_zero, add_zero]
      field_simp
      ring
    · have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hu0 : u = 0 := by
        rcases mul_eq_zero.1 huj with h | h
        · exact h
        · exact absurd h hj
      rw [hu0]; ring
  · rw [mul_sub, mul_sub, eB', eD', eB'', eD'', eB, eD, p0, p1]
    have h0 := h0 hx
    clear_value u u' v v' w
    subst hw
    have h0' : x * 2 + γ + δ ≠ 0 := by rwa [mul_comm]
    have h1' : x * 2 + γ + δ + 1 ≠ 0 := by rwa [mul_comm]
    have h2' : x * 2 + γ + δ + 2 ≠ 0 := by rwa [mul_comm]
    field_simp
    ring

lemma rf_ne_zero (z : ℝ) (k : ℕ) (h : ∀ i : ℕ, i < k → z + i ≠ 0) : rf z k ≠ 0 := by
  unfold rf
  exact Finset.prod_ne_zero_iff.2 fun i hi => h i (Finset.mem_range.1 hi)

/-- Coefficient recurrence: `c_{k+1} (α+k+1)(β+δ+k+1)(γ+k+1)(k+1) = c_k (k-n)(n+α+β+1+k)`, provided
none of the Pochhammer denominators `(α+1)_{k+1}, (β+δ+1)_{k+1}, (γ+1)_{k+1}` vanishes. -/
theorem racahCoef_succ (α β γ δ : ℝ) (n k : ℕ) (hα : ∀ i : ℕ, i < k + 1 → α + 1 + i ≠ 0)
    (hβ : ∀ i : ℕ, i < k + 1 → β + δ + 1 + i ≠ 0) (hγ : ∀ i : ℕ, i < k + 1 → γ + 1 + i ≠ 0) :
    racahCoef α β γ δ n (k + 1) * ((α + 1 + k) * (β + δ + 1 + k) * (γ + 1 + k) * (k + 1)) =
      racahCoef α β γ δ n k * ((k - n) * (n + α + β + 1 + k)) := by
  have a1 := rf_ne_zero (α + 1) k (fun i hi => hα i (by omega))
  have b1 := rf_ne_zero (β + δ + 1) k (fun i hi => hβ i (by omega))
  have c1 := rf_ne_zero (γ + 1) k (fun i hi => hγ i (by omega))
  have a2 := hα k (by omega)
  have b2 := hβ k (by omega)
  have c2 := hγ k (by omega)
  have f1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have k1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  unfold racahCoef
  rw [rf_succ, rf_succ, rf_succ, rf_succ, rf_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma racahPhi_zero (γ δ x : ℝ) : racahPhi γ δ 0 x = 1 := by
  simp [racahPhi, rf_zero]

/-- **The Racah difference equation**: `n(n+α+β+1) R_n(x) = (L R_n)(x)`, with
`L f = B(x)(f(x+1) - f(x)) + D(x)(f(x-1) - f(x))`.  Hypotheses: the three lattice denominators and the
Pochhammer denominators `(α+1)_n, (β+δ+1)_n, (γ+1)_n` do not vanish. -/
theorem racahPoly_diff (α β γ δ : ℝ) (n : ℕ) (x : ℝ) (h0 : x ≠ 0 → 2 * x + γ + δ ≠ 0)
    (h1 : 2 * x + γ + δ + 1 ≠ 0) (h2 : 2 * x + γ + δ + 2 ≠ 0)
    (hα : ∀ i : ℕ, i < n → α + 1 + i ≠ 0) (hβ : ∀ i : ℕ, i < n → β + δ + 1 + i ≠ 0)
    (hγ : ∀ i : ℕ, i < n → γ + 1 + i ≠ 0) :
    racahL α β γ δ (racahPoly α β γ δ n) x = n * (n + α + β + 1) * racahPoly α β γ δ n x := by
  have hL : racahL α β γ δ (racahPoly α β γ δ n) x =
      ∑ k ∈ Finset.range (n + 1), racahCoef α β γ δ n k * racahL α β γ δ (racahPhi γ δ k) x := by
    simp only [racahL, racahPoly, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hL0 : racahL α β γ δ (racahPhi γ δ 0) x = 0 := by
    simp [racahL, racahPhi_zero]
  set c : ℕ → ℝ := racahCoef α β γ δ n with hc
  set φ : ℕ → ℝ := fun k => racahPhi γ δ k x with hφ
  rw [hL, Finset.sum_range_succ', hL0, mul_zero, add_zero]
  have hstep : ∀ k ∈ Finset.range n, c (k + 1) * racahL α β γ δ (racahPhi γ δ (k + 1)) x =
      c (k + 1) * (((k : ℝ) + 1) * ((k : ℝ) + 1 + α + β + 1)) * φ (k + 1) -
        c k * ((k - n) * (n + α + β + 1 + k)) * φ k := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [racahPhi_diff α β γ δ x k h0 h1 h2]
    have hr := racahCoef_succ α β γ δ n k (fun i hi => hα i (by omega))
      (fun i hi => hβ i (by omega)) (fun i hi => hγ i (by omega))
    simp only [hφ, hc] at hr ⊢
    linear_combination (-(racahPhi γ δ k x)) * hr
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib]
  have e1 : ∑ k ∈ Finset.range n, c (k + 1) * (((k : ℝ) + 1) * ((k : ℝ) + 1 + α + β + 1)) * φ (k + 1) =
      ∑ k ∈ Finset.range (n + 1), c k * ((k : ℝ) * ((k : ℝ) + α + β + 1)) * φ k := by
    rw [Finset.sum_range_succ' _ n]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  rw [e1, Finset.sum_range_succ _ n]
  have e2 : racahPoly α β γ δ n x = ∑ k ∈ Finset.range (n + 1), c k * φ k := rfl
  rw [e2, Finset.sum_range_succ _ n]
  have e4 := Finset.mul_sum (Finset.range n) (fun k => c k * φ k) ((n : ℝ) * (n + α + β + 1))
  have e3 : ∑ k ∈ Finset.range n, c k * ((k : ℝ) * ((k : ℝ) + α + β + 1)) * φ k -
      ∑ k ∈ Finset.range n, c k * (((k : ℝ) - n) * (n + α + β + 1 + k)) * φ k =
      ∑ k ∈ Finset.range n, (n * (n + α + β + 1)) * (c k * φ k) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  linear_combination e3 - e4

/-- `R_n(λ(0)) = 1`: the polynomial is normalised at `x = 0`. -/
theorem racahPoly_zero (α β γ δ : ℝ) (n : ℕ) : racahPoly α β γ δ n 0 = 1 := by
  unfold racahPoly
  rw [Finset.sum_range_succ']
  have h0 : ∀ k ∈ Finset.range n, racahCoef α β γ δ n (k + 1) * racahPhi γ δ (k + 1) 0 = 0 := by
    intro k _
    have : racahPhi γ δ (k + 1) 0 = 0 := by
      unfold racahPhi; rw [rf_succ']; simp
    rw [this, mul_zero]
  rw [Finset.sum_eq_zero h0, racahPhi_zero]
  simp [racahCoef, rf_zero]

/-- info: 'FormalResearch.Racah.RacahPoly.racahPoly_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racahPoly_diff

/-- info: 'FormalResearch.Racah.RacahPoly.racahPoly_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racahPoly_zero

end FormalResearch.Racah.RacahPoly
