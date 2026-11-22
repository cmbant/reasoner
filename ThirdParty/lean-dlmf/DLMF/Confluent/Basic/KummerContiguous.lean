/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.KummerProperties
public import DLMFMathlib.Analysis.Complex.NonInteger

/-!
# Kummer's function: derivative, contiguous relations and conjugation

The derivative of Kummer's function, its contiguous relations (DLMF §13.3(i)) and its behaviour
under complex conjugation, proved from the power series.

## Main results

* `deriv_kummerM`, `hasDerivAt_kummerM_shift`: `M'(a,b,z) = (a/b) M(a+1,b+1,z)` (DLMF 13.3.15).
* `kummerM_contiguous_a`, `kummerM_contiguous_b`, `kummerM_contiguous_a_b`,
  `kummerM_contiguous_shift_a`, `kummerM_contiguous_mixed`, `kummerM_contiguous_down`:
  the contiguous relations for `M` (DLMF 13.3.1–13.3.6).
* `kummerM_ode_contiguous`: Kummer's equation as a contiguous relation (DLMF 13.3.13).
* `kummerM_contiguous_shift_b_succ`, `kummerM_contiguous_mixed_b_pred`: two further relations.
* `z_mul_deriv_kummerM_eq_shift_a`, `z_mul_deriv_kummerM_eq_shift_b_pred`,
  `z_mul_deriv_kummerM_eq_shift_a_pred`, `deriv_kummerM_eq_shift_b_succ`: the derivative in terms
  of contiguous functions.
* `conj_kummerM`: `conj M(a,c,z) = M(conj a, conj c, conj z)`.

## Implementation notes

Denominator parameters of `kummerM` stay off the nonpositive integers. The contiguous relations
for Tricomi's `U` and the iterated-derivative formulas are in
`DLMF.Confluent.Recurrence.Contiguous`.
-/

public section

open Complex Filter FormalMultilinearSeries
open scoped Real Topology ComplexConjugate
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

section KummerContiguous

/-- Kummer's series converges everywhere. -/
theorem hasSum_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n => kummerMCoeff a b n * z ^ n) (kummerM a b z) :=
  (hasFPowerSeriesOnBall_kummerM (a := a) hb).hasSum_mul_pow (by simp)

/-- Termwise differentiation of Kummer's series: `M'(a,b,z) = ∑ (n+1) c_{n+1} zⁿ`. -/
theorem hasSum_deriv_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n : ℕ => (n + 1 : ℂ) * kummerMCoeff a b (n + 1) * z ^ n)
      (deriv (kummerM a b) z) :=
  (hasFPowerSeriesOnBall_kummerM (a := a) hb).deriv_ofScalars.hasSum_mul_pow (by simp)

/-- `z M'(a,b,z) = ∑ n c_n zⁿ`, with `c_n` the Kummer coefficients. -/
theorem hasSum_z_mul_deriv_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n : ℕ => (n : ℂ) * kummerMCoeff a b n * z ^ n)
      (z * deriv (kummerM a b) z) :=
  (hasFPowerSeriesOnBall_kummerM (a := a) hb).hasSum_z_mul_deriv (by simp)

/-- `z M(a,b,z) = ∑_{n ≥ 1} c_{n-1} zⁿ`. -/
theorem hasSum_z_mul_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n : ℕ => (if n = 0 then 0 else kummerMCoeff a b (n - 1)) * z ^ n)
      (z * kummerM a b z) := by
  apply HasSum.mul_pow_shift (c := fun n => if n = 0 then 0 else kummerMCoeff a b (n - 1))
    ?_ (by simp)
  simpa using hasSum_kummerM hb z

/-- Coefficient identity `n c_n(a,b) = a c_n(a+1,b) - a c_n(a,b)`. -/
theorem kummerMCoeff_shift_a (a b : ℂ) (n : ℕ) :
    (n : ℂ) * kummerMCoeff a b n =
      a * kummerMCoeff (a + 1) b n - a * kummerMCoeff a b n := by
  simp only [kummerMCoeff]
  rw [mul_div_assoc', mul_div_assoc', mul_div_assoc', ← sub_div]
  congr 1
  cases n with
  | zero => simp [pochhammer_zero]
  | succ m =>
    rw [← pochhammer_succ_left, pochhammer_succ a (m + 1)]
    push_cast
    ring

/-- Coefficient identity `n c_n(a,b) = (b-1) c_n(a,b-1) - (b-1) c_n(a,b)`. -/
theorem kummerMCoeff_shift_b_pred {a b : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) (n : ℕ) :
    (n : ℂ) * kummerMCoeff a b n =
      (b - 1) * kummerMCoeff a (b - 1) n - (b - 1) * kummerMCoeff a b n := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  cases n with
  | zero => simp [kummerMCoeff, pochhammer_zero]
  | succ m =>
    have hb0 : b - 1 ≠ 0 := by simpa using hb1 0
    have hbm : b + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb m
    have hpb := pochhammer_ne_zero_of_not_neg_nat hb m
    have hf : ((m + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [kummerMCoeff]
    rw [pochhammer_succ_left (b - 1), sub_add_cancel, pochhammer_succ b m]
    push_cast
    field_simp
    ring

/-- Coefficient identity `n c_n(a,b) = (b-a) c_n(a-1,b) + (a-b) c_n(a,b) + c_{n-1}(a,b)`, behind
DLMF 13.3.1. -/
theorem kummerMCoeff_shift_a_pred {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    (n : ℂ) * kummerMCoeff a b n =
      (b - a) * kummerMCoeff (a - 1) b n + (a - b) * kummerMCoeff a b n +
        (if n = 0 then 0 else kummerMCoeff a b (n - 1)) := by
  cases n with
  | zero => simp [kummerMCoeff, pochhammer_zero]
  | succ m =>
    have hbm : b + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb m
    have hpb := pochhammer_ne_zero_of_not_neg_nat hb m
    have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [kummerMCoeff, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [pochhammer_succ_left (a - 1), sub_add_cancel, pochhammer_succ a m, pochhammer_succ b m,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- Coefficient identity `b (n+1) c_{n+1}(a,b) = (a-b) c_n(a,b+1) + b c_n(a,b)`.
-/
theorem kummerMCoeff_shift_b_succ {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    b * ((n + 1 : ℂ) * kummerMCoeff a b (n + 1)) =
      (a - b) * kummerMCoeff a (b + 1) n + b * kummerMCoeff a b n := by
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hbn : b + n ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb n
  have hpb := pochhammer_ne_zero_of_not_neg_nat hb n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hrel : b * pochhammer (b + 1) n = pochhammer b n * (b + n) := by
      rw [← pochhammer_succ_left, pochhammer_succ]
  have hX : pochhammer (b + 1) n = pochhammer b n * (b + n) / b := by
    rw [eq_div_iff hb0]; linear_combination hrel
  simp only [kummerMCoeff]
  rw [pochhammer_succ a n, pochhammer_succ b n, Nat.factorial_succ, hX]
  push_cast
  field_simp
  ring

/-- Coefficient form of `b M(a,b,z) - b M(a-1,b,z) - z M(a,b+1,z) = 0` (DLMF 13.3.4). -/
theorem kummerMCoeff_contiguous_shift_a {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    b * kummerMCoeff a b n - b * kummerMCoeff (a - 1) b n -
      (if n = 0 then 0 else kummerMCoeff a (b + 1) (n - 1)) = 0 := by
  cases n with
  | zero => simp [kummerMCoeff, pochhammer_zero]
  | succ m =>
    have hb0 : b ≠ 0 := by simpa using hb 0
    have hbm : b + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb m
    have hpb := pochhammer_ne_zero_of_not_neg_nat hb m
    have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hrel : b * pochhammer (b + 1) m = pochhammer b m * (b + m) := by
        rw [← pochhammer_succ_left, pochhammer_succ]
    have hX : pochhammer (b + 1) m = pochhammer b m * (b + m) / b := by
      rw [eq_div_iff hb0]; linear_combination hrel
    simp only [kummerMCoeff, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [pochhammer_succ_left (a - 1), sub_add_cancel, pochhammer_succ a m, pochhammer_succ b m,
      Nat.factorial_succ, hX]
    push_cast
    field_simp
    ring

/-- Coefficient identity combining the Kummer equation with contiguous relations in `(a,b) →
(a+1,b+1) → (a+2,b+2)`. -/
theorem kummerMCoeff_ode_contiguous {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    (a + 1) * (if n = 0 then 0 else kummerMCoeff (a + 2) (b + 2) (n - 1)) +
      (b + 1) * b * kummerMCoeff (a + 1) (b + 1) n -
      (b + 1) * (if n = 0 then 0 else kummerMCoeff (a + 1) (b + 1) (n - 1)) -
      b * (b + 1) * kummerMCoeff a b n = 0 := by
  cases n with
  | zero => simp [kummerMCoeff, pochhammer_zero]; ring
  | succ m =>
    have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
    have hb0 : b ≠ 0 := by simpa using hb 0
    have hb10 : b + 1 ≠ 0 := by simpa using hb1 0
    have hbm : b + 1 + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb1 m
    have hpb := pochhammer_ne_zero_of_not_neg_nat hb1 m
    have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hrelA : (a + 1) * pochhammer (a + 2) m = pochhammer (a + 1) m * (a + 1 + m) := by
      rw [show (a + 2 : ℂ) = a + 1 + 1 by ring, ← pochhammer_succ_left, pochhammer_succ]
    have hrelB : (b + 1) * pochhammer (b + 2) m = pochhammer (b + 1) m * (b + 1 + m) := by
      rw [show (b + 2 : ℂ) = b + 1 + 1 by ring, ← pochhammer_succ_left, pochhammer_succ]
    have hX : pochhammer (b + 2) m = pochhammer (b + 1) m * (b + 1 + m) / (b + 1) := by
      rw [eq_div_iff hb10]; linear_combination hrelB
    have hA : (a + 1) * kummerMCoeff (a + 2) (b + 2) m =
        pochhammer (a + 1) m * (a + 1 + m) / (pochhammer (b + 2) m * m.factorial) := by
      simp only [kummerMCoeff]
      rw [mul_div_assoc', hrelA]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [hA, hX]
    simp only [kummerMCoeff]
    rw [pochhammer_succ_left a, pochhammer_succ (a + 1) m, pochhammer_succ_left b,
        pochhammer_succ (b + 1) m,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `z M'(a,b,z) = a (M(a+1,b,z) - M(a,b,z))`. -/
theorem z_mul_deriv_kummerM_eq_shift_a {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    z * deriv (kummerM a b) z = a * kummerM (a + 1) b z - a * kummerM a b z := by
  have h := hasSum_z_mul_deriv_kummerM (a := a) hb z
  have h' := ((hasSum_kummerM (a := a + 1) hb z).mul_left a).sub
    ((hasSum_kummerM (a := a) hb z).mul_left a)
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * kummerMCoeff_shift_a a b n

/-- `z M'(a,b,z) = (b-1) (M(a,b-1,z) - M(a,b,z))`. -/
theorem z_mul_deriv_kummerM_eq_shift_b_pred {a b : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) (z : ℂ) :
    z * deriv (kummerM a b) z =
      (b - 1) * kummerM a (b - 1) z - (b - 1) * kummerM a b z := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  have h := hasSum_z_mul_deriv_kummerM (a := a) hb z
  have h' := ((hasSum_kummerM (a := a) hb1 z).mul_left (b - 1)).sub
    ((hasSum_kummerM (a := a) hb z).mul_left (b - 1))
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * kummerMCoeff_shift_b_pred (a := a) hb1 n

/-- `z M'(a,b,z) = (b-a) M(a-1,b,z) + (a-b+z) M(a,b,z)`. -/
theorem z_mul_deriv_kummerM_eq_shift_a_pred {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    z * deriv (kummerM a b) z =
      (b - a) * kummerM (a - 1) b z + (a - b) * kummerM a b z +
        z * kummerM a b z := by
  have h := hasSum_z_mul_deriv_kummerM (a := a) hb z
  have h' := (((hasSum_kummerM (a := a - 1) hb z).mul_left (b - a)).add
    ((hasSum_kummerM (a := a) hb z).mul_left (a - b))).add (hasSum_z_mul_kummerM (a := a) hb z)
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * kummerMCoeff_shift_a_pred (a := a) hb n

/-- `b M'(a,b,z) = (a-b) M(a,b+1,z) + b M(a,b,z)`. -/
theorem deriv_kummerM_eq_shift_b_succ {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    b * deriv (kummerM a b) z = (a - b) * kummerM a (b + 1) z + b * kummerM a b z := by
  have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have h := (hasSum_deriv_kummerM (a := a) hb z).mul_left b
  have h' := ((hasSum_kummerM (a := a) hb1 z).mul_left (a - b)).add
    ((hasSum_kummerM (a := a) hb z).mul_left b)
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * kummerMCoeff_shift_b_succ (a := a) hb n

/-- Identity under the stated parameter and domain assumptions: `(b - a) * kummerM (a - 1) b z +
(2 * a - b + z) * kummerM a b z - a * kummerM (a + 1) b z = 0`. -/
@[dlmf 13.3.E1]
theorem kummerM_contiguous_a {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    (b - a) * kummerM (a - 1) b z + (2 * a - b + z) * kummerM a b z -
      a * kummerM (a + 1) b z = 0 := by
  have hA := z_mul_deriv_kummerM_eq_shift_a (a := a) hb z
  have hC := z_mul_deriv_kummerM_eq_shift_a_pred (a := a) hb z
  linear_combination hA - hC

/-- Identity under the stated parameter and domain assumptions: `b * (b - 1) * kummerM a (b - 1) z
+ b * (1 - b - z) * kummerM a b z + z * (b - a) * kummerM a (b + 1) z = 0`. -/
@[dlmf 13.3.E2]
theorem kummerM_contiguous_b {a b z : ℂ} (hb : ∀ k : ℕ, b - 1 ≠ -k) :
    b * (b - 1) * kummerM a (b - 1) z + b * (1 - b - z) * kummerM a b z +
      z * (b - a) * kummerM a (b + 1) z = 0 := by
  have hb' : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hb z
  have hD := deriv_kummerM_eq_shift_b_succ (a := a) hb' z
  linear_combination z * hD - b * hB

/-- Identity under the stated parameter and domain assumptions: `(a - b + 1) * kummerM a b z - a *
kummerM (a + 1) b z + (b - 1) * kummerM a (b - 1) z = 0`. -/
@[dlmf 13.3.E3]
theorem kummerM_contiguous_a_b {a b z : ℂ} (hb : ∀ k : ℕ, b - 1 ≠ -k) :
    (a - b + 1) * kummerM a b z - a * kummerM (a + 1) b z +
      (b - 1) * kummerM a (b - 1) z = 0 := by
  have hb' : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hA := z_mul_deriv_kummerM_eq_shift_a (a := a) hb' z
  have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hb z
  linear_combination hA - hB

/-- Identity under the stated parameter and domain assumptions: `b * kummerM a b z - b * kummerM
(a - 1) b z - z * kummerM a (b + 1) z = 0`. -/
@[dlmf 13.3.E4]
theorem kummerM_contiguous_shift_a {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    b * kummerM a b z - b * kummerM (a - 1) b z - z * kummerM a (b + 1) z = 0 := by
  have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have h := (((hasSum_kummerM (a := a) hb z).mul_left b).sub
    ((hasSum_kummerM (a := a - 1) hb z).mul_left b)).sub
    (hasSum_z_mul_kummerM (a := a) hb1 z)
  refine h.unique ?_
  convert hasSum_zero using 1
  funext n
  linear_combination (z ^ n) * kummerMCoeff_contiguous_shift_a (a := a) hb n

/-- Identity under the stated parameter and domain assumptions: `b * (a + z) * kummerM a b z + z *
(a - b) * kummerM a (b + 1) z - a * b * kummerM (a + 1) b z = 0`. -/
@[dlmf 13.3.E5]
theorem kummerM_contiguous_mixed {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    b * (a + z) * kummerM a b z + z * (a - b) * kummerM a (b + 1) z -
      a * b * kummerM (a + 1) b z = 0 := by
  have hA := z_mul_deriv_kummerM_eq_shift_a (a := a) hb z
  have hD := deriv_kummerM_eq_shift_b_succ (a := a) hb z
  linear_combination b * hA - z * hD

/-- Identity under the stated parameter and domain assumptions: `(a - 1 + z) * kummerM a b z + (b
- a) * kummerM (a - 1) b z + (1 - b) * kummerM a (b - 1) z = 0`. -/
@[dlmf 13.3.E6]
theorem kummerM_contiguous_down {a b z : ℂ} (hb : ∀ k : ℕ, b - 1 ≠ -k) :
    (a - 1 + z) * kummerM a b z + (b - a) * kummerM (a - 1) b z +
      (1 - b) * kummerM a (b - 1) z = 0 := by
  have hb' : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hb z
  have hC := z_mul_deriv_kummerM_eq_shift_a_pred (a := a) hb' z
  linear_combination hB - hC

/-- Identity under the stated parameter and domain assumptions: `(a + 1) * z * kummerM (a + 2) (b
+ 2) z + (b + 1) * (b - z) * kummerM (a + 1) (b + 1) z - b * (b + 1) * kummerM a b z = 0`. -/
@[dlmf 13.3.E13]
theorem kummerM_ode_contiguous {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    (a + 1) * z * kummerM (a + 2) (b + 2) z +
      (b + 1) * (b - z) * kummerM (a + 1) (b + 1) z -
      b * (b + 1) * kummerM a b z = 0 := by
  have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hb2 : ∀ k : ℕ, b + 2 ≠ -k := by simpa using not_neg_nat_add_nat hb 2
  have h := ((((hasSum_z_mul_kummerM (a := a + 2) hb2 z).mul_left (a + 1)).add
    ((hasSum_kummerM (a := a + 1) hb1 z).mul_left ((b + 1) * b))).sub
    ((hasSum_z_mul_kummerM (a := a + 1) hb1 z).mul_left (b + 1))).sub
    ((hasSum_kummerM (a := a) hb z).mul_left (b * (b + 1)))
  have h0 : (a + 1) * (z * kummerM (a + 2) (b + 2) z) +
      (b + 1) * b * kummerM (a + 1) (b + 1) z -
      (b + 1) * (z * kummerM (a + 1) (b + 1) z) - b * (b + 1) * kummerM a b z = 0 := by
    refine h.unique ?_
    convert hasSum_zero using 1
    funext n
    linear_combination (z ^ n) * kummerMCoeff_ode_contiguous (a := a) hb n
  linear_combination h0

/-- Identity under the stated parameter and domain assumptions: `deriv (kummerM a b) z = a / b *
kummerM (a + 1) (b + 1) z`. -/
@[dlmf 13.3.E15]
theorem deriv_kummerM {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (hb0 : b ≠ 0) :
    deriv (kummerM a b) z = a / b * kummerM (a + 1) (b + 1) z := by
  have hc1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hcoeff (k : ℕ) : (k + 1 : ℂ) * kummerMCoeff a b (k + 1) =
      a / b * kummerMCoeff (a + 1) (b + 1) k := by
    have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hcp := pochhammer_ne_zero_of_not_neg_nat hc1 k
    simp only [kummerMCoeff, pochhammer_succ_left, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp
  have hd := (hasFPowerSeriesOnBall_kummerM (a := a) hb).deriv_ofScalars.hasSum_mul_pow
    (z := z) (by simp)
  have hs := ((hasFPowerSeriesOnBall_kummerM (a := a + 1) hc1).hasSum_mul_pow
    (z := z) (by simp)).mul_left (a / b)
  simp_rw [hcoeff] at hd
  simp only [mul_assoc] at hd hs
  exact hd.unique hs

/-- `a M(a+1,b+1,z) = (a-b) M(a,b+1,z) + b M(a,b,z)`. -/
theorem kummerM_contiguous_shift_b_succ {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    a * kummerM (a + 1) (b + 1) z =
      (a - b) * kummerM a (b + 1) z + b * kummerM a b z := by
  have hb0 : b ≠ 0 := by simpa using hb 0
  have h1 := deriv_kummerM_eq_shift_b_succ (a := a) hb z
  have h2 := deriv_kummerM (a := a) hb hb0 (z := z)
  have h3 : b * (a / b * kummerM (a + 1) (b + 1) z) = a * kummerM (a + 1) (b + 1) z := by
    field_simp
  rw [h2] at h1
  linear_combination h1 - h3

/-- `(b-1) b (M(a,b,z) - M(a,b-1,z)) + a z M(a+1,b+1,z) = 0`. -/
theorem kummerM_contiguous_mixed_b_pred {a b z : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) :
    (b - 1) * b * kummerM a b z - (b - 1) * b * kummerM a (b - 1) z +
      a * z * kummerM (a + 1) (b + 1) z = 0 := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hB := z_mul_deriv_kummerM_eq_shift_b_pred (a := a) hb1 z
  have h2 := deriv_kummerM (a := a) hb hb0 (z := z)
  have h3 : b * (a / b * kummerM (a + 1) (b + 1) z) = a * kummerM (a + 1) (b + 1) z := by
    field_simp
  rw [h2] at hB
  linear_combination b * hB - z * h3

end KummerContiguous

/-- Kummer's function has derivative `(a/b) M(a+1,b+1,z)`. -/
theorem hasDerivAt_kummerM_shift {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasDerivAt (kummerM a b) (a / b * kummerM (a + 1) (b + 1) z) z := by
  have h := (hasFPowerSeriesOnBall_kummerM (a := a) hb).analyticAt_of_mem (y := z) (by simp)
  have hb0 : b ≠ 0 := by simpa using hb 0
  rw [← deriv_kummerM hb hb0]
  exact h.differentiableAt.hasDerivAt

/-- Complex conjugation commutes with the Pochhammer symbol: `conj((a)_n) = (conj a)_n`. -/
theorem conj_pochhammer (a : ℂ) (n : ℕ) : conj (pochhammer a n) = pochhammer (conj a) n := by
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n ih => rw [pochhammer_succ, pochhammer_succ, map_mul, ih, map_add, map_natCast]

/-- Kummer's function commutes with complex conjugation. -/
theorem conj_kummerM (a c z : ℂ) :
    conj (kummerM a c z) = kummerM (conj a) (conj c) (conj z) := by
  rw [kummerM, kummerM, Complex.conj_tsum]
  congr 1
  funext n
  simp [conj_pochhammer, map_div₀, map_mul, map_pow]

end DLMF.Confluent
