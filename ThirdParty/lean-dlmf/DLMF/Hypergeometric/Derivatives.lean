/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.DiffEq
public import DLMFMathlib.Analysis.Calculus.DifferentialOperators

/-!
# Higher derivatives and contiguous relations (DLMF §15.5)

## Main results

* `iteratedDeriv_hypergeometric`: DLMF 15.5.2.
* `iterate_mulDerivMul`, `iteratedDeriv_mul_cpow`, `iterate_mulDerivMul_euler`,
  `iteratedDeriv_euler`, `iterate_oneSubMulDerivMul`, `iterate_oneSubMulDerivMul_cpow`,
  `iteratedDeriv_two_cpow`: the derivative formulas DLMF 15.5.3–15.5.9.
* `iterate_mulDerivMul_eq`: the operator identity DLMF 15.5.10.
* `contiguous_ab`, `contiguous_a_b_pred`, `contiguous_a_c_succ`, `contiguous_a_succ_c_pred`,
  `contiguous_a_pred_c_succ`, `contiguous_a_pred_c_pred`, `contiguous_c_three`,
  `contiguous_diagonal`: Gauss's contiguous relations DLMF 15.5.12–15.5.19.
* `deriv_contiguous_c_succ`: DLMF 15.5.21.
* `contiguous_ultrasphericalPolynomial_raise`, `contiguous_jacobi_lowering`,
  `contiguous_jacobi_raising`: hypergeometric forms of 18.9.7, 18.9.17 and 18.9.18.

## Implementation notes

15.5.1 and the symmetry `ordinaryHypergeometric_symm` are in
`DLMF.Hypergeometric.Basic.GaussEquation`; 15.5.11 is in `DLMF.Hypergeometric.Contiguous`;
15.5.16_5 is a parameter-swapped instance of `contiguous_shift_b`. 15.5.20 is
`ordinaryHypergeometric_mul_one_sub_mul_deriv_eq`; its second equality follows by swapping
`a, b`. Shifted denominator parameters are kept away from nonpositive integers. The factors
`z^s` are differentiated only on the principal logarithm's slit plane.
-/

public section

open Complex Filter
open scoped Real Topology ContDiff

noncomputable section

namespace DLMF.Hypergeometric

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (₂F₁ a b c) z =
pochhammer a n * pochhammer b n / pochhammer c n * ₂F₁ (a + n) (b + n) (c + n) z`. -/
@[dlmf 15.5.E2]
theorem iteratedDeriv_hypergeometric
    {a b c z : ℂ}
    (n : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)  :
    iteratedDeriv n (₂F₁ a b c) z =
      pochhammer a n * pochhammer b n / pochhammer c n * ₂F₁ (a + n) (b + n) (c + n) z := by
  induction n generalizing z with
  | zero => simp [iteratedDeriv_zero, pochhammer_zero]
  | succ n ih =>
    have heq : iteratedDeriv n (₂F₁ a b c) =ᶠ[𝓝 z]
        (fun w => pochhammer a n * pochhammer b n / pochhammer c n *
            ₂F₁ (a + n) (b + n) (c + n) w) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz] with w hw
      exact ih hw
    rw [iteratedDeriv_succ, heq.deriv_eq, deriv_const_mul_field,
      deriv_ordinaryHypergeometric (not_neg_nat_add_nat hc n) hz]
    simp only [pochhammer_succ, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
    ring

/-- For `z ≠ 0`, `z * z ^ (a - 1) = z ^ a`. -/
private lemma mul_cpow_pred {z : ℂ} (hz : z ≠ 0) (a : ℂ) :
    z * z ^ (a - 1) = z ^ a := by
  calc
    _ = z ^ (1 : ℂ) * z ^ (a - 1) := by rw [cpow_one]
    _ = z ^ ((1 : ℂ) + (a - 1)) := (cpow_add _ _ hz).symm
    _ = _ := by congr 1; ring

/-- Product rule for `z ^ s * ₂F₁(a, b; c; z)` inside the unit disk and the slit plane. -/
private lemma deriv_cpow_mul_hg {a b c z : ℂ} (s : ℂ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) (hs : z ∈ slitPlane) :
    deriv (fun w => w ^ s * ₂F₁ a b c w) z =
      s * z ^ (s - 1) * ₂F₁ a b c z + z ^ s * deriv (₂F₁ a b c) z := by
  have hF := hasDerivAt_ordinaryHypergeometric (a := a) (b := b) hc hz
  have hp := (hasDerivAt_id z).cpow_const (c := s) hs
  simpa only [mul_one, hF.deriv, id_eq, Pi.mul_def] using (hp.mul hF).deriv

/-- The operator `mulDerivMul` maps `z ^ (a - 1) ₂F₁(a, b; c; z)` to `a z ^ a ₂F₁(a + 1, b; c; z)`.
  -/
private lemma mulDerivMul_hg {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) (hs : z ∈ slitPlane) :
    mulDerivMul (fun w => w ^ (a - 1) * ₂F₁ a b c w) z =
      a * z ^ a * ₂F₁ (a + 1) b c z := by
  have heq : (fun w => w * (w ^ (a - 1) * ₂F₁ a b c w)) =ᶠ[𝓝 z]
      (fun w => w ^ a * ₂F₁ a b c w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hs] with w hw
    rw [← mul_assoc, mul_cpow_pred (slitPlane_ne_zero hw)]
  rw [mulDerivMul_eq_mul, heq.deriv_eq, deriv_cpow_mul_hg a hc hz hs,
    ← mul_cpow_pred (slitPlane_ne_zero hs) a]
  have h := ordinaryHypergeometric_mul_deriv_eq_shift_a (a := a) (b := b) hc hz
  linear_combination z * z ^ (a - 1) * h

/-- The derivative of `z ^ (c - 1) ₂F₁(a, b; c; z)` is `(c - 1) z ^ (c - 2) ₂F₁(a, b; c - 1; z)`. -/
private lemma deriv_cpow_mul_hg_lower {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hcm : ∀ k : ℕ, c - 1 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1) (hs : z ∈ slitPlane) :
    deriv (fun w => w ^ (c - 1) * ₂F₁ a b c w) z =
      (c - 1) * z ^ (c - 1 - 1) * ₂F₁ a b (c - 1) z := by
  rw [deriv_cpow_mul_hg (c - 1) hc hz hs,
    ← mul_cpow_pred (slitPlane_ne_zero hs) (c - 1)]
  have ha := ordinaryHypergeometric_mul_deriv_eq_shift_a (a := a) (b := b) hc hz
  have hd := contiguous_c (a := a) (b := b) hcm hz
  simp only [sub_add_cancel] at hd
  linear_combination z ^ (c - 1 - 1) * ha - z ^ (c - 1 - 1) * hd

/-- Identity under the stated parameter and domain assumptions: `(mulDerivMul^[n]) (fun w => w ^
(a - 1) * ₂F₁ a b c w) z = pochhammer a n * z ^ (a + n - 1) * ₂F₁ (a + n) b c z`. -/
@[dlmf 15.5.E3]
theorem iterate_mulDerivMul
    {a b c z : ℂ}
    (n : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hzs : z ∈ slitPlane) :
    (mulDerivMul^[n]) (fun w => w ^ (a - 1) * ₂F₁ a b c w) z =
      pochhammer a n * z ^ (a + n - 1) * ₂F₁ (a + n) b c z := by
  induction n generalizing z with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    have heq : (fun w => w * (mulDerivMul^[n]) (fun t => t ^ (a - 1) * ₂F₁ a b c t) w)
        =ᶠ[𝓝 z] (fun w => pochhammer a n * (w * (w ^ (a + n - 1) * ₂F₁ (a + n) b c w))) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz,
        isOpen_slitPlane.mem_nhds hzs] with w hw hs
      rw [ih hw hs]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul_eq_mul, heq.deriv_eq, deriv_const_mul_field]
    change z * (pochhammer a n * deriv (fun w => w * (w ^ (a + n - 1) * ₂F₁ (a + n) b c w)) z) = _
    calc
      _ = pochhammer a n * mulDerivMul (fun w => w ^ (a + n - 1) * ₂F₁ (a + n) b c w) z := by
        rw [mulDerivMul_eq_mul]; ring
      _ = _ := by
        rw [mulDerivMul_hg hc hz hzs]
        simp only [pochhammer_succ, Nat.cast_add, Nat.cast_one]
        ring

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => w ^ (c
- 1) * ₂F₁ a b c w) z = pochhammer (c - n) n * z ^ (c - n - 1) * ₂F₁ a b (c - n) z`. -/
@[dlmf 15.5.E4]
theorem iteratedDeriv_mul_cpow
    {a b c z : ℂ}
    (n : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hzs : z ∈ slitPlane)
    (hcn : ∀ k : ℕ, c - n ≠ -(k : ℂ)) :
    iteratedDeriv n (fun w => w ^ (c - 1) * ₂F₁ a b c w) z =
      pochhammer (c - n) n * z ^ (c - n - 1) * ₂F₁ a b (c - n) z := by
  induction n generalizing c with
  | zero => simp [iteratedDeriv_zero, pochhammer_zero]
  | succ n ih =>
    have hcm : ∀ k : ℕ, c - 1 ≠ -(k : ℂ) := by
      intro k hk
      apply hcn (k + n)
      push_cast
      linear_combination hk
    have hcn' : ∀ k : ℕ, c - 1 - n ≠ -(k : ℂ) := by
      intro k hk
      apply hcn k
      push_cast
      linear_combination hk
    have heq : deriv (fun w => w ^ (c - 1) * ₂F₁ a b c w) =ᶠ[𝓝 z]
        (fun w => (c - 1) * (w ^ (c - 1 - 1) * ₂F₁ a b (c - 1) w)) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz,
        isOpen_slitPlane.mem_nhds hzs] with w hw hs
      rw [deriv_cpow_mul_hg_lower hc hcm hw hs]
      ring
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field,
      ih hcm hcn']
    simp only [pochhammer_succ, Nat.cast_add, Nat.cast_one]
    ring

/-- Leibniz rule for `w ↦ w h(w)`: `(w h)^{(m+1)} = z h^{(m+1)} + (m + 1) h^{(m)}`. -/
private lemma iteratedDeriv_mul_id {h : ℂ → ℂ} (hh : ContDiff ℂ ⊤ h) (m : ℕ) (z : ℂ) :
    iteratedDeriv (m + 1) (fun w => w * h w) z =
      z * iteratedDeriv (m + 1) h z + (m + 1) * iteratedDeriv m h z := by
  have hid : ContDiffAt ℂ (m + 1 : ℕ) (id : ℂ → ℂ) z :=
    contDiff_id.contDiffAt.of_le le_top
  have hh' : ContDiffAt ℂ (m + 1 : ℕ) h z :=
    (hh.of_le le_top).contDiffAt
  rw [show (fun w : ℂ => w * h w) = id * h from rfl, iteratedDeriv_mul hid hh']
  have hterm (i : ℕ) (_hi : i ∈ Finset.range (m + 1 + 1)) :
      ((m + 1).choose i : ℂ) * iteratedDeriv i (id : ℂ → ℂ) z *
          iteratedDeriv (m + 1 - i) h z =
        if i = 0 then z * iteratedDeriv (m + 1) h z
        else if i = 1 then (m + 1 : ℂ) * iteratedDeriv m h z
        else 0 := by
    simp only [iteratedDeriv_id]
    split_ifs with h0i h1i
    · subst h0i; simp
    · subst h1i; simp
    · simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_ite]
  simp [Finset.filter_eq', Finset.filter_ne']

/-- Operator identity for smooth functions; no hypergeometric parameters occur. -/
@[dlmf 15.5.E10]
theorem iterate_mulDerivMul_eq (n : ℕ) {f : ℂ → ℂ} (hf : ContDiff ℂ ⊤ f) (z : ℂ) :
    (mulDerivMul^[n]) f z = z ^ n * iteratedDeriv n (fun w => w ^ n * f w) z := by
  induction n generalizing f z with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    have hg : ContDiff ℂ ⊤ (fun t : ℂ => t ^ n * f t) := (contDiff_id.pow n).mul hf
    have heq : (fun w => w * (mulDerivMul^[n] f) w) =
        fun w => w ^ (n + 1) * iteratedDeriv n (fun t => t ^ n * f t) w := by
      funext w
      rw [ih hf w, pow_succ]
      ring
    have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ (n + 1)) z := by fun_prop
    have hidiff : DifferentiableAt ℂ
        (iteratedDeriv n (fun t : ℂ => t ^ n * f t)) z :=
      (hg.differentiable_iteratedDeriv n (WithTop.coe_lt_top _)).differentiableAt
    have hpz : deriv (fun w : ℂ => w ^ (n + 1)) z = (n + 1 : ℂ) * z ^ n := by
      simp
    have hprod :
        deriv (fun w => w ^ (n + 1) * iteratedDeriv n (fun t => t ^ n * f t) w) z =
          (n + 1 : ℂ) * z ^ n * iteratedDeriv n (fun t => t ^ n * f t) z +
            z ^ (n + 1) * iteratedDeriv (n + 1) (fun t => t ^ n * f t) z := by
      rw [deriv_fun_mul hpow hidiff, hpz, iteratedDeriv_succ]
    rw [Function.iterate_succ_apply', mulDerivMul_eq_mul, heq, hprod]
    have hleib := iteratedDeriv_mul_id hg n z
    have hwg : (fun w : ℂ => w * (w ^ n * f w)) = fun w => w ^ (n + 1) * f w := by
      funext w
      rw [pow_succ]
      ring
    rw [hwg] at hleib
    calc
      z * ((n + 1 : ℂ) * z ^ n * iteratedDeriv n (fun t => t ^ n * f t) z +
            z ^ (n + 1) * iteratedDeriv (n + 1) (fun t => t ^ n * f t) z) =
          z ^ (n + 1) * ((n + 1 : ℂ) * iteratedDeriv n (fun t => t ^ n * f t) z +
            z * iteratedDeriv (n + 1) (fun t => t ^ n * f t) z) := by ring
      _ = z ^ (n + 1) * iteratedDeriv (n + 1) (fun w => w ^ (n + 1) * f w) z := by
        rw [hleib]; ring

/-- Identity under the stated parameter and domain assumptions: `(b - a) * ₂F₁ a b c z + a * ₂F₁
(a + 1) b c z - b * ₂F₁ a (b + 1) c z = 0`. -/
@[dlmf 15.5.E12]
theorem contiguous_ab {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1)  :
    (b - a) * ₂F₁ a b c z + a * ₂F₁ (a + 1) b c z - b * ₂F₁ a (b + 1) c z = 0 := by
  have ha := ordinaryHypergeometric_mul_deriv_eq_shift_a (a := a) (b := b) hc hz
  have hb := ordinaryHypergeometric_mul_deriv_eq_shift_a (a := b) (b := a) hc hz
  simp only [ordinaryHypergeometric_symm b a c, ordinaryHypergeometric_symm (b + 1) a c] at hb
  linear_combination hb - ha

/-- Identity under the stated parameter and domain assumptions: `(c - a - b) * ₂F₁ a b c z + a *
(1 - z) * ₂F₁ (a + 1) b c z - (c - b) * ₂F₁ a (b - 1) c z = 0`. -/
@[dlmf 15.5.E13]
theorem contiguous_a_b_pred {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1)  :
    (c - a - b) * ₂F₁ a b c z + a * (1 - z) * ₂F₁ (a + 1) b c z - (c - b) *
        ₂F₁ a (b - 1) c z = 0 := by
  have ha := ordinaryHypergeometric_mul_deriv_eq_shift_a (a := a) (b := b) hc hz
  have hb := ordinaryHypergeometric_mul_one_sub_mul_deriv_eq (a := b) (b := a) hc hz
  simp only [ordinaryHypergeometric_symm b a c, ordinaryHypergeometric_symm (b - 1) a c] at hb
  linear_combination hb - (1 - z) * ha

/-- One step along the antidiagonal: `(b-a)(1-z)F(a,b) = (c-a)F(a-1,b) + (b-c)F(a,b-1)`; it is
the hypergeometric form of 18.9.6. -/
theorem contiguous_a_pred_b_pred {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    (b - a) * (1 - z) * ₂F₁ a b c z =
      (c - a) * ₂F₁ (a - 1) b c z + (b - c) * ₂F₁ a (b - 1) c z := by
  have hab := contiguous_ab (a := a) (b := b) hc hz
  have h1 := contiguous_a_b_pred (a := a) (b := b) hc hz
  have h2 := contiguous_a_b_pred (a := b) (b := a) hc hz
  simp only [ordinaryHypergeometric_symm b a c, ordinaryHypergeometric_symm b (a - 1) c,
      ordinaryHypergeometric_symm (b + 1) a c] at h2
  linear_combination (1 - z) * hab + h2 - h1

/-- Raising `c` together with `a` or `b`:
`c(b-a)F(a,b;c) = (c-a) b F(a,b+1;c+1) - (c-b) a F(a+1,b;c+1)`, the hypergeometric form of the
`α`-raising companion of 18.9.5. -/
theorem contiguous_c_pair {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    c * (b - a) * ₂F₁ a b c z =
      (c - a) * b * ₂F₁ a (b + 1) (c + 1) z - (c - b) * a * ₂F₁ (a + 1) b (c + 1) z := by
  have h1 := contiguous_c (a := a) (b := b) hc hz
  have h2 := contiguous_c (a := b) (b := a) hc hz
  simp only [ordinaryHypergeometric_symm b a c, ordinaryHypergeometric_symm b a (c + 1),
      ordinaryHypergeometric_symm (b + 1) a (c + 1)] at h2
  linear_combination (c - a) * h2 - (c - b) * h1

/-- A three-term relation along the antidiagonal `(a,b) → (a+1,b-1) → (a+2,b-2)` with `c`
fixed; it is the hypergeometric form of the Jacobi three-term recurrence 18.9.2. The overall
factor `2a(a-c+2)` is what makes the multipliers polynomial. -/
theorem contiguous_antidiagonal {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    2 * a * (a - c + 2) *
      ((b - 1) * (a - b + 3) * (a - c + 1) * ₂F₁ a b c z -
        (a - b + 2) * ((a - b + 1) * (a - b + 3) * z + a * (2 * b - c - 2) - (b - 1) * (c - 2)) *
          ₂F₁ (a + 1) (b - 1) c z +
        (a + 1) * (a - b + 1) * (b - c - 1) * ₂F₁ (a + 2) (b - 2) c z) = 0 := by
  have h1 := contiguous_ab (a := a) (b := b - 2) hc hz
  have h2 := contiguous_ab (a := a) (b := b - 1) hc hz
  have h3 := contiguous_a_b_pred (a := a) (b := b - 1) hc hz
  have h4 := contiguous_ab (a := a + 1) (b := b - 2) hc hz
  ring_nf at h1 h2 h3 h4 ⊢
  linear_combination (2 * (a - b + 1) * (a - b + 3) * (a - c + 2) * (b - c - 1)) * h1 -
    (2 * a * (a - b + 3) * (a - c + 1) * (a - c + 2)) * h2 +
    (2 * (a - b + 1) * (a - b + 2) * (a - b + 3) * (a - c + 2)) * h3 +
    (2 * a * (a - b + 1) * (a - c + 2) * (b - c - 1)) * h4

/-- Identity under the stated parameter and domain assumptions: `c * (1 - z) * deriv (₂F₁ a b c) z
= (c - a) * (c - b) * ₂F₁ a b (c + 1) z + c * (a + b - c) * ₂F₁ a b c z`. -/
@[dlmf 15.5.E21]
theorem deriv_contiguous_c_succ {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    c * (1 - z) * deriv (₂F₁ a b c) z =
      (c - a) * (c - b) * ₂F₁ a b (c + 1) z + c * (a + b - c) * ₂F₁ a b c z := by
  have hcoeff (n : ℕ) :
      c * ((n + 1) * gaussHypergeometricCoeff a b c (n + 1) - n *
          gaussHypergeometricCoeff a b c n) =
        (c - a) * (c - b) * gaussHypergeometricCoeff a b (c + 1) n +
          c * (a + b - c) * gaussHypergeometricCoeff a b c n := by
    have hcp := pochhammer_ne_zero_of_not_neg_nat hc n
    have hc1 : ∀ k : ℕ, c + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hc 1
    have hcp1 := pochhammer_ne_zero_of_not_neg_nat hc1 n
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hshift : (c + n) * gaussHypergeometricCoeff a b (c + 1) n = c *
        gaussHypergeometricCoeff a b c n := by
      have hpoch := pochhammer_succ_left_mul c n
      simp only [gaussHypergeometricCoeff]
      field_simp [hcp, hcp1, hf]
      linear_combination -(pochhammer a n * pochhammer b n) * hpoch
    have hn : c + (n : ℂ) ≠ 0 := by simpa [eq_neg_iff_add_eq_zero] using hc n
    apply mul_left_cancel₀ hn
    have hrec := gaussHypergeometricCoeff_recurrence (a := a) (b := b) hc n
    linear_combination c * hrec - (c - a) * (c - b) * hshift
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hs := hasFPowerSeriesOnBall_ordinaryHypergeometric a b c
  have h₀ := hs.hasSum_mul_pow hz'
  have h₁ := hs.deriv_ofScalars.hasSum_mul_pow hz'
  have h₂ := hs.hasSum_z_mul_deriv hz'
  have h₃ := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b (c + 1)).hasSum_mul_pow hz'
  have hleft := (h₁.sub h₂).mul_left c
  have hright := (h₃.mul_left ((c - a) * (c - b))).add (h₀.mul_left (c * (a + b - c)))
  have heq : (fun n : ℕ => c * (((n + 1) * gaussHypergeometricCoeff a b c (n + 1) * z ^ n) -
        n * gaussHypergeometricCoeff a b c n * z ^ n)) =
      (fun n : ℕ => (c - a) * (c - b) * (gaussHypergeometricCoeff a b (c + 1) n * z ^ n) +
        c * (a + b - c) * (gaussHypergeometricCoeff a b c n * z ^ n)) := by
    funext n
    linear_combination hcoeff n * z ^ n
  rw [heq] at hleft
  have h := hleft.unique hright
  linear_combination h

/-- 15.5.21 with the derivative eliminated through 15.5.1:
`a b (1-z) F(a+1,b+1;c+1) = (c-a)(c-b) F(a,b;c+1) + c(a+b-c) F(a,b;c)`. -/
theorem contiguous_c_succ_shift {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    a * b * (1 - z) * ₂F₁ (a + 1) (b + 1) (c + 1) z =
      (c - a) * (c - b) * ₂F₁ a b (c + 1) z + c * (a + b - c) * ₂F₁ a b c z := by
  have h := deriv_contiguous_c_succ (a := a) (b := b) hc hz
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hd : c * deriv (₂F₁ a b c) z = a * b * ₂F₁ (a + 1) (b + 1) (c + 1) z := by
    rw [deriv_ordinaryHypergeometric hc hz]
    field_simp
  linear_combination h - (1 - z) * hd

/-- Identity under the stated parameter and domain assumptions: `c * (a + (b - c) * z) * ₂F₁ a b c
z - a * c * (1 - z) * ₂F₁ (a + 1) b c z + (c - a) * (c - b) * z * ₂F₁ a b (c + 1) z = 0`. -/
@[dlmf 15.5.E14]
theorem contiguous_a_c_succ {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1)  :
    c * (a + (b - c) * z) * ₂F₁ a b c z - a * c * (1 - z) * ₂F₁ (a + 1) b c z + (c - a) *
        (c - b) * z * ₂F₁
      a b (c + 1) z = 0 := by
  have ha := ordinaryHypergeometric_mul_deriv_eq_shift_a (a := a) (b := b) hc hz
  have hd := deriv_contiguous_c_succ (a := a) (b := b) hc hz
  linear_combination c * (1 - z) * ha - z * hd

/-- Identity under the stated parameter and domain assumptions: `(c - a - 1) * ₂F₁ a b c z + a *
₂F₁ (a + 1) b c z - (c - 1) * ₂F₁ a b (c - 1) z = 0`. -/
@[dlmf 15.5.E15]
theorem contiguous_a_succ_c_pred
    {a b c z : ℂ}
    (hz : ‖z‖ < 1)
    (hcm : ∀ k : ℕ, c - 1 ≠ -(k : ℂ)) :
    (c - a - 1) * ₂F₁ a b c z + a * ₂F₁ (a + 1) b c z - (c - 1) * ₂F₁ a b (c - 1) z = 0 := by
  have h := contiguous_c (a := a) (b := b) hcm hz
  simp only [sub_add_cancel] at h
  linear_combination -h

/-- Identity under the stated parameter and domain assumptions: `c * (1 - z) * ₂F₁ a b c z - c *
₂F₁ (a - 1) b c z + (c - b) * z * ₂F₁ a b (c + 1) z = 0`. -/
@[dlmf 15.5.E16]
theorem contiguous_a_pred_c_succ {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1)  :
    c * (1 - z) * ₂F₁ a b c z - c * ₂F₁ (a - 1) b c z + (c - b) * z * ₂F₁ a b (c + 1) z = 0 := by
  have hs := contiguous_shift_b (a := b) (b := a - 1) hc hz
  have hc' := contiguous_c (a := b) (b := a) hc hz
  simp only [sub_add_cancel, ordinaryHypergeometric_symm b (a - 1) c,
    ordinaryHypergeometric_symm b a c, ordinaryHypergeometric_symm (b + 1) a (c + 1)] at hs
  simp only [ordinaryHypergeometric_symm b a c, ordinaryHypergeometric_symm b a (c + 1),
      ordinaryHypergeometric_symm (b + 1) a (c + 1)] at hc'
  linear_combination -hs - z * hc'

/-- Identity under the stated parameter and domain assumptions: `(a - 1 + (b + 1 - c) * z) * ₂F₁ a
b c z + (c - a) * ₂F₁ (a - 1) b c z - (c - 1) * (1 - z) * ₂F₁ a b (c - 1) z = 0`. -/
@[dlmf 15.5.E17]
theorem contiguous_a_pred_c_pred
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hcm : ∀ k : ℕ, c - 1 ≠ -(k : ℂ)) :
    (a - 1 + (b + 1 - c) * z) * ₂F₁ a b c z + (c - a) * ₂F₁ (a - 1) b c z - (c - 1) *
        (1 - z) * ₂F₁ a b (c -
      1) z = 0 := by
  have h₁ := contiguous_a (a := a) (b := b) hc hz
  have h₂ := contiguous_a_succ_c_pred (a := a) (b := b) hz hcm
  linear_combination h₁ + (1 - z) * h₂

/-- Identity under the stated parameter and domain assumptions: `c * (c - 1) * (z - 1) * ₂F₁ a b
(c - 1) z + c * (c - 1 - (2 * c - a - b - 1) * z) * ₂F₁ a b c z + (c - a) * (c - b) * z * ₂F₁
a b (c + 1) z = 0`. -/
@[dlmf 15.5.E18]
theorem contiguous_c_three
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hcm : ∀ k : ℕ, c - 1 ≠ -(k : ℂ)) :
    c * (c - 1) * (z - 1) * ₂F₁ a b (c - 1) z + c * (c - 1 - (2 * c - a - b - 1) * z) *
        ₂F₁ a b c z + (c -
      a) * (c - b) * z * ₂F₁ a b (c + 1) z = 0 := by
  have h₁ := contiguous_a_c_succ (a := a) (b := b) hc hz
  have h₂ := contiguous_a (a := a) (b := b) hc hz
  have h₃ := contiguous_a_pred_c_pred (a := a) (b := b) hc hz hcm
  linear_combination h₁ - c * h₂ + c * h₃

/-- Identity under the stated parameter and domain assumptions: `z * (1 - z) * (a + 1) * (b + 1) *
₂F₁ (a + 2) (b + 2) (c + 2) z + (c - (a + b + 1) * z) * (c + 1) * ₂F₁ (a + 1) (b + 1) (c + 1)
z - c * (c + 1) * ₂F₁ a b c z = 0`. -/
@[dlmf 15.5.E19]
theorem contiguous_diagonal {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1)  :
    z * (1 - z) * (a + 1) * (b + 1) * ₂F₁ (a + 2) (b + 2) (c + 2) z +
        (c - (a + b + 1) * z) * (c + 1) * ₂F₁
      (a + 1) (b + 1) (c + 1) z - c * (c + 1) * ₂F₁ a b c z = 0 := by
  have hc1 : ∀ k : ℕ, c + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hc 1
  have hc10 : c + 1 ≠ 0 := by simpa using hc1 0
  have h₁ := ordinaryHypergeometric_mul_one_sub_mul_deriv_eq
    (a := a + 1) (b := b + 1) hc1 hz
  have h₂ := contiguous_a_b_pred (a := a) (b := b + 1) hc1 hz
  have h₃ := contiguous_c (a := b) (b := a) hc hz
  simp only [ordinaryHypergeometric_symm b a c, ordinaryHypergeometric_symm b a (c + 1),
      ordinaryHypergeometric_symm (b + 1) a (c + 1)] at h₃
  have hd : (c + 1) * deriv (₂F₁ (a + 1) (b + 1) (c + 1)) z =
      (a + 1) * (b + 1) * ₂F₁ (a + 2) (b + 2) (c + 2) z := by
    rw [deriv_ordinaryHypergeometric hc1 hz]
    field_simp [hc10]
    ring
  simp only [add_sub_cancel_right] at h₁ h₂
  linear_combination (c + 1) * h₁ + (c + 1) * h₂ - (c + 1) * h₃ - z * (1 - z) * hd

/-! The Euler-type formulas 15.5.5 and 15.5.6 are placed here because their proofs use the
contiguous derivative relation `deriv_contiguous_c_succ`. -/

/-- `1 - w` lies in the slit plane when `‖w‖ < 1`. -/
theorem one_sub_mem_slitPlane_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ∈ slitPlane := by
  simpa [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one (z := -w) (by simpa using hw)

/-- Product rule for `(1 - z) ^ t * ₂F₁(a, b; c; z)` inside the unit disk. -/
private lemma deriv_one_sub_cpow_mul_hg {a b c z : ℂ} (t : ℂ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    deriv (fun w => (1 - w) ^ t * ₂F₁ a b c w) z =
      -(t * (1 - z) ^ (t - 1)) * ₂F₁ a b c z + (1 - z) ^ t * deriv (₂F₁ a b c) z := by
  have hF := hasDerivAt_ordinaryHypergeometric (a := a) (b := b) hc hz
  have hq := ((hasDerivAt_id z).const_sub 1).cpow_const (c := t)
      (one_sub_mem_slitPlane_of_norm_lt_one hz)
  have h := (hq.mul hF).deriv
  simp only [id_eq, Pi.mul_def] at h
  rw [h, hF.deriv]
  ring

/-- Product rule for `z ^ s (1 - z) ^ t ₂F₁(a, b; c; z)` inside the unit disk and the slit plane. -/
private lemma deriv_cpow_mul_one_sub_cpow_mul_hg {a b c z : ℂ} (s t : ℂ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) (hs : z ∈ slitPlane) :
    deriv (fun w => w ^ s * (1 - w) ^ t * ₂F₁ a b c w) z =
      s * z ^ (s - 1) * (1 - z) ^ t * ₂F₁ a b c z -
        t * z ^ s * (1 - z) ^ (t - 1) * ₂F₁ a b c z +
        z ^ s * (1 - z) ^ t * deriv (₂F₁ a b c) z := by
  have hF := hasDerivAt_ordinaryHypergeometric (a := a) (b := b) hc hz
  have hp := (hasDerivAt_id z).cpow_const (c := s) hs
  have hq := ((hasDerivAt_id z).const_sub 1).cpow_const (c := t)
      (one_sub_mem_slitPlane_of_norm_lt_one hz)
  have h := ((hp.mul hq).mul hF).deriv
  simp only [id_eq, Pi.mul_def, mul_one] at h
  rw [h, hF.deriv]
  ring

/-- Identity under the stated parameter and domain assumptions: `(mulDerivMul^[n]) (fun w => w ^
(c - a - 1) * (1 - w) ^ (a + b - c) * ₂F₁ a b c w) z = pochhammer (c - a) n * z ^ (c - a + n - 1) *
(1 - z) ^ (a - n + b - c) * ₂F₁ (a - n) b c z`. -/
@[dlmf 15.5.E5]
theorem iterate_mulDerivMul_euler
    {a b c z : ℂ}
    (n : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hzs : z ∈ slitPlane) :
    (mulDerivMul^[n]) (fun w => w ^ (c - a - 1) * (1 - w) ^ (a + b - c) * ₂F₁ a b c w) z =
      pochhammer (c - a) n * z ^ (c - a + n - 1) * (1 - z) ^ (a - n + b - c) *
          ₂F₁ (a - n) b c z := by
  induction n generalizing z with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    have heq : (fun w => w * (mulDerivMul^[n])
          (fun t => t ^ (c - a - 1) * (1 - t) ^ (a + b - c) * ₂F₁ a b c t) w) =ᶠ[𝓝 z]
        (fun w => pochhammer (c - a) n *
          (w ^ (c - a + n) * (1 - w) ^ (a - n + b - c) * ₂F₁ (a - n) b c w)) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz,
        isOpen_slitPlane.mem_nhds hzs] with w hw hs
      rw [ih hw hs, ← mul_cpow_pred (slitPlane_ne_zero hs) (c - a + n)]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul_eq_mul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_one_sub_cpow_mul_hg (c - a + n) (a - n + b - c) hc hz hzs]
    have hd := ordinaryHypergeometric_mul_one_sub_mul_deriv_eq (a := a - n) (b := b) hc hz
    have hz0 : z ≠ 0 := slitPlane_ne_zero hzs
    have h1z : (1 : ℂ) - z ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hz)
    have e1 : z ^ (c - a + ((n + 1 : ℕ) : ℂ) - 1) = z ^ (c - a + n) := by
      congr 1; push_cast; ring
    have e2 : (1 - z) ^ (a - ((n + 1 : ℕ) : ℂ) + b - c) = (1 - z) ^ (a - n + b - c - 1) := by
      congr 1; push_cast; ring
    have e3 : (a - ((n + 1 : ℕ) : ℂ)) = a - n - 1 := by push_cast; ring
    have e4 : z ^ (c - a + n) = z * z ^ (c - a + n - 1) := (mul_cpow_pred hz0 _).symm
    have e5 : (1 - z) ^ (a - n + b - c) = (1 - z) * (1 - z) ^ (a - n + b - c - 1) :=
      (mul_cpow_pred h1z _).symm
    rw [e1, e2, e3, pochhammer_succ, e4, e5]
    linear_combination
      (pochhammer (c - a) n * z * z ^ (c - a + n - 1) * (1 - z) ^ (a - n + b - c - 1)) * hd

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => (1 - w)
^ (a + b - c) * ₂F₁ a b c w) z = pochhammer (c - a) n * pochhammer (c - b) n / pochhammer c n * (1 -
z) ^ (a + b
- c - n) * ₂F₁ a b (c + n) z`. -/
@[dlmf 15.5.E6]
theorem iteratedDeriv_euler {a b c z : ℂ} (n : ℕ) (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1)  :
    iteratedDeriv n (fun w => (1 - w) ^ (a + b - c) * ₂F₁ a b c w) z =
      pochhammer (c - a) n * pochhammer (c - b) n / pochhammer c n * (1 - z) ^ (a + b - c - n) *
          ₂F₁ a b (c + n) z := by
  induction n generalizing c with
  | zero => simp [iteratedDeriv_zero, pochhammer_zero]
  | succ n ih =>
    have hc1 : ∀ k : ℕ, c + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hc 1
    have hc0 : c ≠ 0 := by simpa using hc 0
    have heq : deriv (fun w => (1 - w) ^ (a + b - c) * ₂F₁ a b c w) =ᶠ[𝓝 z]
        (fun w => (c - a) * (c - b) / c *
          ((1 - w) ^ (a + b - (c + 1)) * ₂F₁ a b (c + 1) w)) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz] with w hw
      rw [deriv_one_sub_cpow_mul_hg (a + b - c) hc hw]
      have hw1 : (1 : ℂ) - w ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hw)
      have hd := deriv_contiguous_c_succ (a := a) (b := b) hc hw
      have hpow : (1 - w) ^ (a + b - c) = (1 - w) * (1 - w) ^ (a + b - c - 1) :=
        (mul_cpow_pred hw1 _).symm
      have hexp : (1 - w) ^ (a + b - (c + 1)) = (1 - w) ^ (a + b - c - 1) := by congr 1; ring
      rw [hexp, hpow]
      field_simp
      linear_combination ((1 - w) ^ (a + b - c - 1)) * hd
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih hc1]
    have h1 : pochhammer (c - a) (n + 1) = (c - a) * pochhammer (c + 1 - a) n := by
      rw [pochhammer_succ_left]; congr 2; ring
    have h2 : pochhammer (c - b) (n + 1) = (c - b) * pochhammer (c + 1 - b) n := by
      rw [pochhammer_succ_left]; congr 2; ring
    have h3 : pochhammer c (n + 1) = c * pochhammer (c + 1) n := pochhammer_succ_left c n
    have hexp2 : (1 - z) ^ (a + b - (c + 1) - n) = (1 - z) ^ (a + b - c - ((n + 1 : ℕ) : ℂ)) := by
      congr 1; push_cast; ring
    have harg : c + 1 + (n : ℂ) = c + ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h1, h2, h3, hexp2, harg]
    have hp : pochhammer (c + 1) n ≠ 0 := pochhammer_ne_zero_of_not_neg_nat hc1 n
    field_simp

/-- `c (1-z) F' = a c F - a (c-b) F(a+1,b;c+1)`. -/
private lemma one_sub_mul_deriv_eq_shift_a_c {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    c * (1 - z) * deriv (₂F₁ a b c) z =
      a * c * ₂F₁ a b c z - a * (c - b) * ₂F₁ (a + 1) b (c + 1) z := by
  have h1 := deriv_contiguous_c_succ (a := a) (b := b) hc hz
  have h2 := contiguous_c (a := a) (b := b) hc hz
  linear_combination h1 - (c - b) * h2

/-- `z (1-z) F' = (c-1) F(a-1,b;c-1) - (c-1) (1-z) F + (b-c+1) z F`. -/
private lemma mul_one_sub_deriv_eq_shift_down {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hc1 : ∀ k : ℕ, c - 1 ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    z * (1 - z) * deriv (₂F₁ a b c) z =
      (c - 1) * ₂F₁ (a - 1) b (c - 1) z - (c - 1) * (1 - z) * ₂F₁ a b c z +
        (b - c + 1) * z * ₂F₁ a b c z := by
  have h1 := ordinaryHypergeometric_mul_one_sub_mul_deriv_eq (a := a) (b := b) hc hz
  have h2 := contiguous_c (a := a - 1) (b := b) (c := c - 1) hc1 hz
  rw [show c - 1 + 1 = c by ring, show a - 1 + 1 = a by ring,
    show c - 1 - (a - 1) = c - a by ring] at h2
  linear_combination h1 - h2

/-- `z (1-z) F' = (c-1) F(a-1,b-1;c-1) - (c-1) (1-z) F + (a+b-c) z F`. -/
private lemma mul_one_sub_deriv_eq_shift_down_two {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hc1 : ∀ k : ℕ, c - 1 ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    z * (1 - z) * deriv (₂F₁ a b c) z =
      (c - 1) * ₂F₁ (a - 1) (b - 1) (c - 1) z - (c - 1) * (1 - z) * ₂F₁ a b c z +
        (a + b - c) * z * ₂F₁ a b c z := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have h1 := ordinaryHypergeometric_mul_one_sub_mul_deriv_eq (a := a) (b := b) hc hz
  have h2 := contiguous_c (a := a - 1) (b := b - 1) (c := c - 1) hc1 hz
  rw [show c - 1 + 1 = c by ring, show a - 1 + 1 = a by ring,
    show c - 1 - (a - 1) = c - a by ring] at h2
  have h3 := contiguous_shift_b (a := a - 1) (b := b - 1) (c := c) hc hz
  rw [show b - 1 + 1 = b by ring, show a - 1 + 1 = a by ring] at h3
  have h4 := contiguous_shift_b (a := a) (b := b - 1) (c := c) hc hz
  rw [show b - 1 + 1 = b by ring] at h4
  have h5 := contiguous_c (a := a) (b := b) (c := c) hc hz
  apply mul_left_cancel₀ hc0
  linear_combination c * h1 - c * h2 - (c - a) * h3 - (a - 1) * h4 - (a - 1) * z * h5

/-- Identity under the stated parameter and domain assumptions: `(oneSubMulDerivMul^[n]) (fun w =>
(1 - w) ^ (a - 1) * ₂F₁ a b c w) z = (-1 : ℂ) ^ n * pochhammer a n * pochhammer (c - b) n /
pochhammer c n * (1
- z) ^ (a + n - 1) * ₂F₁ (a + n) b (c + n) z`. -/
@[dlmf 15.5.E7]
theorem iterate_oneSubMulDerivMul
    {a b c z : ℂ}
    (n : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)  :
    (oneSubMulDerivMul^[n]) (fun w => (1 - w) ^ (a - 1) * ₂F₁ a b c w) z =
      (-1 : ℂ) ^ n * pochhammer a n * pochhammer (c - b) n / pochhammer c n *
          (1 - z) ^ (a + n - 1) *
          ₂F₁ (a + n) b (c + n) z
        := by
  induction n generalizing z with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    have hcn : ∀ k : ℕ, c + n ≠ -(k : ℂ) := not_neg_nat_add_nat hc n
    have hcn0 : c + (n : ℂ) ≠ 0 := by simpa using hcn 0
    have heq : (fun w => (1 - w) * (oneSubMulDerivMul^[n])
          (fun t => (1 - t) ^ (a - 1) * ₂F₁ a b c t) w) =ᶠ[𝓝 z]
        (fun w => (-1 : ℂ) ^ n * pochhammer a n * pochhammer (c - b) n / pochhammer c n *
          ((1 - w) ^ (a + n) * ₂F₁ (a + n) b (c + n) w)) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz] with w hw
      rw [ih hw, ← mul_cpow_pred (slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hw))
          (a + n)]
      ring
    rw [Function.iterate_succ_apply', oneSubMulDerivMul_eq_mul, heq.deriv_eq, deriv_const_mul_field,
      deriv_one_sub_cpow_mul_hg (a + n) hcn hz]
    have hd := one_sub_mul_deriv_eq_shift_a_c (a := a + n) (b := b) hcn hz
    have h1z : (1 : ℂ) - z ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hz)
    have e1 : (1 - z) ^ (a + ((n + 1 : ℕ) : ℂ) - 1) = (1 - z) ^ (a + n) := by
      congr 1; push_cast; ring
    have e2 : a + ((n + 1 : ℕ) : ℂ) = a + n + 1 := by push_cast; ring
    have e3 : c + ((n + 1 : ℕ) : ℂ) = c + n + 1 := by push_cast; ring
    have e4 : (1 - z) ^ (a + n) = (1 - z) * (1 - z) ^ (a + n - 1) := (mul_cpow_pred h1z _).symm
    rw [e1, e2, e3, pochhammer_succ, pochhammer_succ, pochhammer_succ, pow_succ, e4]
    have hp : pochhammer c n ≠ 0 := pochhammer_ne_zero_of_not_neg_nat hc n
    field_simp
    linear_combination (pochhammer a n * pochhammer (c - b) n * (1 - z) ^ (a + n - 1)) * hd

/-- Identity under the stated parameter and domain assumptions: `(oneSubMulDerivMul^[n]) (fun w =>
w ^ (c - 1) * (1 - w) ^ (b - c) * ₂F₁ a b c w) z = pochhammer (c - n) n * z ^ (c - n - 1) * (1 - z)
^ (b - c + n) * ₂F₁ (a - n) b (c - n) z`. -/
@[dlmf 15.5.E8]
theorem iterate_oneSubMulDerivMul_cpow
    {a b c z : ℂ}
    (n : ℕ)

    (hz : ‖z‖ < 1)
    (hzs : z ∈ slitPlane)
    (hcn : ∀ k : ℕ, c - n ≠ -(k : ℂ)) :
    (oneSubMulDerivMul^[n]) (fun w => w ^ (c - 1) * (1 - w) ^ (b - c) * ₂F₁ a b c w) z =
      pochhammer (c - n) n * z ^ (c - n - 1) * (1 - z) ^ (b - c + n) * ₂F₁ (a - n) b (c - n) z := by
  induction n generalizing z with
  | zero => simp [pochhammer_zero]
  | succ n ih =>
    have hcn' : ∀ k : ℕ, c - n ≠ -(k : ℂ) := by
      intro k hk
      apply hcn (k + 1)
      push_cast
      linear_combination hk
    have hcn1 : ∀ k : ℕ, c - n - 1 ≠ -(k : ℂ) := by
      intro k hk
      apply hcn k
      push_cast
      linear_combination hk
    have heq : (fun w => (1 - w) * (oneSubMulDerivMul^[n])
          (fun t => t ^ (c - 1) * (1 - t) ^ (b - c) * ₂F₁ a b c t) w) =ᶠ[𝓝 z]
        (fun w => pochhammer (c - n) n *
          (w ^ (c - n - 1) * (1 - w) ^ (b - c + n + 1) * ₂F₁ (a - n) b (c - n) w)) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz,
        isOpen_slitPlane.mem_nhds hzs] with w hw hs
      have h1w : (1 : ℂ) - w ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hw)
      have hw1 : (1 - w) * (1 - w) ^ (b - c + n) = (1 - w) ^ (b - c + n + 1) := by
        rw [← mul_cpow_pred h1w (b - c + n + 1)]
        congr 2
        ring
      rw [ih hw hs hcn', ← hw1]
      ring
    rw [Function.iterate_succ_apply', oneSubMulDerivMul_eq_mul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_one_sub_cpow_mul_hg (c - n - 1) (b - c + n + 1) hcn' hz hzs]
    have hd := mul_one_sub_deriv_eq_shift_down (a := a - n) (b := b) hcn' hcn1 hz
    have hz0 : z ≠ 0 := slitPlane_ne_zero hzs
    have h1z : (1 : ℂ) - z ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hz)
    have e1 : pochhammer (c - ((n + 1 : ℕ) : ℂ)) (n + 1) = (c - n - 1) * pochhammer (c - n) n := by
      rw [pochhammer_succ_left, show c - ((n + 1 : ℕ) : ℂ) + 1 = c - n by push_cast; ring,
        show c - ((n + 1 : ℕ) : ℂ) = c - n - 1 by push_cast; ring]
    have e2 : z ^ (c - ((n + 1 : ℕ) : ℂ) - 1) = z ^ (c - n - 1 - 1) := by
      congr 1; push_cast; ring
    have e3 : (1 - z) ^ (b - c + ((n + 1 : ℕ) : ℂ)) = (1 - z) ^ (b - c + n + 1) := by
      congr 1; push_cast; ring
    have e4 : a - ((n + 1 : ℕ) : ℂ) = a - n - 1 := by push_cast; ring
    have e5 : c - ((n + 1 : ℕ) : ℂ) = c - n - 1 := by push_cast; ring
    have e6 : z ^ (c - n - 1) = z * z ^ (c - n - 1 - 1) := (mul_cpow_pred hz0 _).symm
    have e7 : (1 - z) ^ (b - c + n + 1) = (1 - z) * (1 - z) ^ (b - c + n + 1 - 1) :=
      (mul_cpow_pred h1z _).symm
    rw [e1, e2, e3, e4, e5, e6, e7]
    linear_combination (pochhammer (c - n) n * z ^ (c - n - 1 - 1) *
      (1 - z) ^ (b - c + n + 1 - 1) * (1 - z)) * hd

/-- Identity under the stated parameter and domain assumptions: `iteratedDeriv n (fun w => w ^ (c
- 1) * (1 - w) ^ (a + b - c) * ₂F₁ a b c w) z = pochhammer (c - n) n * z ^ (c - n - 1) * (1 - z) ^
(a + b - c - n) * ₂F₁ (a - n) (b - n) (c - n) z`. -/
@[dlmf 15.5.E9]
theorem iteratedDeriv_two_cpow
    {a b c z : ℂ}
    (n : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hzs : z ∈ slitPlane)
    (hcn : ∀ k : ℕ, c - n ≠ -(k : ℂ)) :
    iteratedDeriv n (fun w => w ^ (c - 1) * (1 - w) ^ (a + b - c) * ₂F₁ a b c w) z =
      pochhammer (c - n) n * z ^ (c - n - 1) * (1 - z) ^ (a + b - c - n) *
          ₂F₁ (a - n) (b - n) (c - n) z := by
  induction n generalizing a b c with
  | zero => simp [iteratedDeriv_zero, pochhammer_zero]
  | succ n ih =>
    have hcm : ∀ k : ℕ, c - 1 ≠ -(k : ℂ) := by
      intro k hk
      apply hcn (k + n)
      push_cast
      linear_combination hk
    have hcn' : ∀ k : ℕ, c - 1 - n ≠ -(k : ℂ) := by
      intro k hk
      apply hcn k
      push_cast
      linear_combination hk
    have heq : deriv (fun w => w ^ (c - 1) * (1 - w) ^ (a + b - c) * ₂F₁ a b c w) =ᶠ[𝓝 z]
        (fun w => (c - 1) * (w ^ (c - 1 - 1) * (1 - w) ^ (a - 1 + (b - 1) - (c - 1)) *
          ₂F₁ (a - 1) (b - 1) (c - 1) w)) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz,
        isOpen_slitPlane.mem_nhds hzs] with w hw hs
      rw [deriv_cpow_mul_one_sub_cpow_mul_hg (c - 1) (a + b - c) hc hw hs]
      have hd := mul_one_sub_deriv_eq_shift_down_two (a := a) (b := b) hc hcm hw
      have hw0 : w ≠ 0 := slitPlane_ne_zero hs
      have h1w : (1 : ℂ) - w ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hw)
      have f1 : w ^ (c - 1) = w * w ^ (c - 1 - 1) := (mul_cpow_pred hw0 _).symm
      have f2 : (1 - w) ^ (a + b - c) = (1 - w) * (1 - w) ^ (a + b - c - 1) :=
        (mul_cpow_pred h1w _).symm
      have f3 : (1 - w) ^ (a - 1 + (b - 1) - (c - 1)) = (1 - w) ^ (a + b - c - 1) := by
        congr 1; ring
      rw [f1, f2, f3]
      linear_combination (w ^ (c - 1 - 1) * (1 - w) ^ (a + b - c - 1)) * hd
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field,
      ih hcm hcn']
    rw [show c - 1 - (n : ℂ) = c - ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show a - 1 - (n : ℂ) = a - ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show b - 1 - (n : ℂ) = b - ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show (1 - z) ^ (a - 1 + (b - 1) - (c - 1) - (n : ℂ)) =
        (1 - z) ^ (a + b - c - ((n + 1 : ℕ) : ℂ)) by congr 1; push_cast; ring,
      pochhammer_succ, show c - ((n + 1 : ℕ) : ℂ) + (n : ℂ) = c - 1 by push_cast; ring]
    ring

/-! ### Relations found by computer algebra for the orthogonal-polynomial identities -/

/-- Hypergeometric form of 18.9.7 (`b = 2c - 1 - a`). -/
theorem contiguous_ultrasphericalPolynomial_raise {a c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1) :
    (2*z*(a - 2*c + 2)) *
        ((-c*(2*c - 1)*(2*a - 2*c + 1)) * ₂F₁ a (-a + 2*c - 1) c z +
        (-(a - 2*c)*(2*c - 1)*(a - 2*c + 1)/2) * ₂F₁ a ((-a + 2*c - 1) + 2) (c + 1) z +
        (a*(a + 1)*(2*c - 1)/2) * ₂F₁ (a + 2) (-a + 2*c - 1) (c + 1) z) = 0 := by
  have h0 := DLMF.Hypergeometric.contiguous_ab (a := a) (b := ((-a + 2*c - 1) - 1)) (c := c) hc hz
  have h1 := contiguous_c (a := ((-a + 2*c - 1) - 1)) (b := a) (c := c) hc hz
  simp only [ordinaryHypergeometric_symm ((-a + 2*c - 1) - 1) a c,
    ordinaryHypergeometric_symm ((-a + 2*c - 1) - 1) a (c + 1),
    ordinaryHypergeometric_symm (((-a + 2*c - 1) - 1) + 1) a (c + 1)] at h1
  have h2 := contiguous_shift_b (a := a) (b := ((-a + 2*c - 1) - 1)) (c := c) hc hz
  have h3 := DLMF.Hypergeometric.contiguous_c_succ_shift (a := a)
      (b := ((-a + 2*c - 1) - 1)) (c := c) hc hz
  have h4 := DLMF.Hypergeometric.contiguous_ab (a := a) (b := (-a + 2*c - 1)) (c := c) hc hz
  have h5 := DLMF.Hypergeometric.contiguous_a_b_pred (a := a) (b := (-a + 2*c - 1)) (c := c) hc hz
  have h6 := contiguous_c (a := (-a + 2*c - 1)) (b := a) (c := c) hc hz
  simp only [ordinaryHypergeometric_symm (-a + 2*c - 1) a c,
    ordinaryHypergeometric_symm (-a + 2*c - 1) a (c + 1),
    ordinaryHypergeometric_symm ((-a + 2*c - 1) + 1) a (c + 1)] at h6
  have h7 := contiguous_c (a := ((-a + 2*c - 1) + 1)) (b := a) (c := c) hc hz
  simp only [ordinaryHypergeometric_symm ((-a + 2*c - 1) + 1) a c,
    ordinaryHypergeometric_symm ((-a + 2*c - 1) + 1) a (c + 1),
    ordinaryHypergeometric_symm (((-a + 2*c - 1) + 1) + 1) a (c + 1)] at h7
  have h8 := contiguous_shift_b (a := (a + 1)) (b := ((-a + 2*c - 1) - 1)) (c := c) hc hz
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  linear_combination (-c*(2*c - 1)*(a - 2*c + 2)) * h0 + (-z*(a - c)*(2*c - 1)*(a - c + 1)) * h1 +
      ((2*c - 1)*(z - 1)*(a - 2*c + 2)*(a - c + 1)) * h2 + (-z*(2*c - 1)*(a - c + 1)) * h3 +
      (c*z*(2*c - 1)*(a - 2*c + 2)) * h4 + (c*(2*c - 1)*(a - 2*c + 2)) * h5 +
      (-z*(a - c)*(2*c - 1)*(a - 2*c + 2)) * h6 + (-z*(2*c - 1)*(a - 2*c + 1)*(a - 2*c + 2)) * h7 +
      (a*(2*c - 1)*(a - 2*c + 2)) * h8

/-- Hypergeometric form of 18.9.8 (`b = 2c - 1 - a`). -/
theorem contiguous_ultrasphericalPolynomial_raise_sq {a c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1) :
    (a*(a + 1)) * ((2*c) * ₂F₁ a (-a + 2*c - 1) c z + (4*z*(z - 1)*(2*a - 2*c + 3)) *
        ₂F₁ (a + 2) (-a + 2*c - 1) (c + 1) z + (-2*c) *
        ₂F₁ (a + 2) ((-a + 2*c - 1) - 2) c z) = 0 := by
  have h0 := DLMF.Hypergeometric.contiguous_ab (a := a) (b := ((-a + 2*c - 1) - 2)) (c := c) hc hz
  have h1 := DLMF.Hypergeometric.contiguous_ab (a := a) (b := ((-a + 2*c - 1) - 1)) (c := c) hc hz
  have h2 := DLMF.Hypergeometric.contiguous_a_b_pred (a := a)
      (b := ((-a + 2*c - 1) - 1)) (c := c) hc hz
  have h3 := DLMF.Hypergeometric.contiguous_a_b_pred (a := a) (b := (-a + 2*c - 1)) (c := c) hc hz
  have h4 := DLMF.Hypergeometric.contiguous_ab (a := (a + 1))
      (b := ((-a + 2*c - 1) - 2)) (c := c) hc hz
  have h5 := contiguous_shift_b (a := (a + 1)) (b := ((-a + 2*c - 1) - 1)) (c := c) hc hz
  ring_nf at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (-4*c*(a - c + 2)) * h0 + (2*c*(a - 2*c + 3)) * h1 + (4*c*(2*a - 2*c + 3)) *
      h2 + (-4*c*(2*a - 2*c + 3)) * h3 + (-2*a*c) * h4 + (4*a*(z - 1)*(2*a - 2*c + 3)) * h5

/-- Hypergeometric form of 18.9.17. -/
theorem contiguous_jacobi_lowering {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    (a - 1) * ((2*a*c*(a - c + 1)*(a*z - b*z + b - c + z)) * ₂F₁ a b c z +
        (2*a*b*z*(z - 1)*(a - b + 1)*(a - c + 1)) * ₂F₁ (a + 1) (b + 1) (c + 1) z +
        (-2*a*c*(b - c)*(a - c + 1)) * ₂F₁ (a + 1) (b - 1) c z) = 0 := by
  have h0 := DLMF.Hypergeometric.contiguous_ab (a := (a - 1)) (b := (b - 1)) (c := c) hc hz
  have h1 := DLMF.Hypergeometric.contiguous_ab (a := (a - 1)) (b := b) (c := c) hc hz
  have h2 := DLMF.Hypergeometric.contiguous_a_b_pred (a := (a - 1)) (b := b) (c := c) hc hz
  have h3 := DLMF.Hypergeometric.contiguous_a_b_pred (a := (a - 1)) (b := (b + 1)) (c := c) hc hz
  have h4 := DLMF.Hypergeometric.contiguous_ab (a := a) (b := (b - 1)) (c := c) hc hz
  have h5 := contiguous_shift_b (a := a) (b := b) (c := c) hc hz
  ring_nf at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (-2*c*(b - c)*(a - b + 1)*(a - c + 1)) * h0 +
      (2*c*(a - b + 1)*(a + b - c)*(a - c + 1)) * h1 + (-2*c*(a - b)*(a - b + 1)*(a - c + 1)) * h2 +
      (-2*b*c*(a - b + 1)*(a - c + 1)) * h3 + (-2*c*(a - 1)*(b - c)*(a - c + 1)) * h4 +
      (2*b*(a - 1)*(z - 1)*(a - b + 1)*(a - c + 1)) * h5

/-- Hypergeometric form of 18.9.18. -/
theorem contiguous_jacobi_raising {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    (a - 2) * ((2*b*c*(a - 1)*(a*z - a - b*z + c - z)) * ₂F₁ a b c z +
        (2*a*b*z*(a - 1)*(z - 1)*(a - b - 1)) * ₂F₁ (a + 1) (b + 1) (c + 1) z +
        (2*b*c*(a - 1)*(a - c)) * ₂F₁ (a - 1) (b + 1) c z) = 0 := by
  have h0 := DLMF.Hypergeometric.contiguous_ab (a := (a - 2)) (b := b) (c := c) hc hz
  have h1 := DLMF.Hypergeometric.contiguous_ab (a := (a - 2)) (b := (b + 1)) (c := c) hc hz
  have h2 := DLMF.Hypergeometric.contiguous_a_b_pred (a := (a - 2)) (b := (b + 1)) (c := c) hc hz
  have h3 := DLMF.Hypergeometric.contiguous_a_b_pred (a := (a - 2)) (b := (b + 2)) (c := c) hc hz
  have h4 := DLMF.Hypergeometric.contiguous_ab (a := (a - 1)) (b := b) (c := c) hc hz
  have h5 := DLMF.Hypergeometric.contiguous_ab (a := (a - 1)) (b := (b + 1)) (c := c) hc hz
  have h6 := contiguous_shift_b (a := a) (b := b) (c := c) hc hz
  ring_nf at h0 h1 h2 h3 h4 h5 h6 ⊢
  linear_combination (-2*b*c*(a - b - 1)*(b - c + 1)) * h0 + (2*b*c*(a - b - 1)*(a + b - c)) * h1 +
      (-2*b*c*(a - b - 2)*(a - b - 1)) * h2 + (-2*b*c*(b + 1)*(a - b - 1)) * h3 +
      (-2*b*c*(a - 2)*(b - c + 1)) * h4 + (2*b*c*(a - 2)*(z - 1)*(a - b - 1)) * h5 +
      (2*b*(a - 2)*(a - 1)*(z - 1)*(a - b - 1)) * h6

end DLMF.Hypergeometric
