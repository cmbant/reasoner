/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LiouvilleGreen
public import DLMFMathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Liouville–Green approximation: the exponential and oscillatory cases

Concrete forms of `LiouvilleGreen.exists_solution_of_kernel_bound` (F. W. J. Olver,
*Asymptotics and Special Functions*, Ch. 6, Thms. 2.1–2.2 and Ch. 10, Thm. 3.1).

Let `f > 0` with `f''` continuous and `g` continuous on `(a, ∞)`, let `ξ' = f^{1/2}`, and let
`V x = ∫_{(x,∞)} |f^{-1/4} (f^{-1/4})'' - g f^{-1/2}|` be the variation on `(x, ∞)` of the
error-control function. Then, for a parameter `u`,

* `w'' = (u² f + g) w`, `u > 0`, has the solution `f^{-1/4} e^{-uξ} (1 + ε)` with
  `|ε| ≤ exp (V/(2u)) - 1` and `|ε'| ≤ 2u f^{1/2} (exp (V/(2u)) - 1)`;
* `w'' = (-u² f + g) w`, `u ≠ 0` real, has the complex solution `f^{-1/4} e^{-iuξ} (1 + ε)` with
  `|ε| ≤ exp (V/|u|) - 1` and `|ε'| ≤ |u| f^{1/2} (exp (V/|u|) - 1)`.

For `u = 1` these are Olver's Theorems 2.1 (recessive solution) and 2.2; for large `u` they give
`ε = O(1/u)` uniformly in `x` (`Real.exp_sub_one_le_mul_exp`). Both are stated
first in terms of an amplitude `A` with `ξ' = A⁻²` (`f = A⁻⁴`), then with `A = f^{-1/4}`.

## Main results

* `LiouvilleGreen.exists_solution_exp`, `LiouvilleGreen.exists_solution_osc`: amplitude form.
* `LiouvilleGreen.errorDensity`: the integrand `f^{-1/4} (f^{-1/4})'' - g f^{-1/2}`.
* `LiouvilleGreen.exists_solution_exp_of_pos`, `LiouvilleGreen.exists_solution_osc_of_pos`:
  Olver's theorems for `w'' = (± u² f + g) w`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace LiouvilleGreen

/-- A function with nonnegative derivative on `(a, ∞)` is monotone there. -/
theorem le_of_hasDerivAt_nonneg {a : ℝ} {ξ d : ℝ → ℝ}
    (hξ : ∀ x, a < x → HasDerivAt ξ (d x) x) (hd : ∀ x, a < x → 0 ≤ d x)
    {x t : ℝ} (hx : a < x) (hxt : x ≤ t) : ξ x ≤ ξ t := by
  have hmono : MonotoneOn ξ (Ioi a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi a)
      (fun y hy => (hξ y hy).continuousAt.continuousWithinAt)
      (fun y hy => by
        rw [interior_Ioi] at hy
        exact (hξ y hy).differentiableAt.differentiableWithinAt) (fun y hy => ?_)
    rw [interior_Ioi] at hy
    rw [(hξ y hy).deriv]
    exact hd y hy
  exact hmono hx (lt_of_lt_of_le hx hxt) hxt

/-- The exponential Liouville–Green kernel: for `ξ' = A⁻²` and `u > 0`, `E = exp (-u ξ)` solves
`E' = -u A⁻² E`, `|E|` is nonincreasing and `|(1 - E(t)²/E(x)²)/(2u)| ≤ 1/(2u)` for `x < t`. -/
theorem exp_kernel {a u : ℝ} (hu : 0 < u) {A ξ : ℝ → ℝ}
    (hξ : ∀ x, a < x → HasDerivAt ξ ((A x ^ 2)⁻¹) x) :
    (∀ x, a < x → Real.exp (-(u * ξ x)) ≠ 0) ∧
    (∀ x, a < x → HasDerivAt (fun y => Real.exp (-(u * ξ y)))
      (-(u * (A x ^ 2)⁻¹ * Real.exp (-(u * ξ x)))) x) ∧
    (∀ x t, a < x → x < t → ‖Real.exp (-(u * ξ t))‖ ≤ ‖Real.exp (-(u * ξ x))‖) ∧
    (∀ x t, a < x → x < t →
      ‖(1 - Real.exp (-(u * ξ t)) ^ 2 / Real.exp (-(u * ξ x)) ^ 2) / (2 * u)‖ ≤ 1 / (2 * u)) := by
  set E : ℝ → ℝ := fun y => Real.exp (-(u * ξ y)) with hEdef
  have hξle : ∀ x t, a < x → x ≤ t → ξ x ≤ ξ t := fun x t hx hxt =>
    le_of_hasDerivAt_nonneg hξ (fun y _ => by positivity) hx hxt
  have hEle' : ∀ x t, a < x → x ≤ t → E t ≤ E x := fun x t hx hxt => by
    simp only [hEdef]
    gcongr
    exact hξle x t hx hxt
  have hEpos : ∀ y, 0 < E y := fun y => Real.exp_pos _
  refine ⟨fun x _ => (hEpos x).ne', fun x hx => ?_, fun x t hx hxt => ?_,
    fun x t hx hxt => ?_⟩
  · exact ((hξ x hx).const_mul u).neg.exp.congr_deriv (by simp only [Pi.neg_apply]; ring)
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hEpos t), abs_of_pos (hEpos x)]
    exact hEle' x t hx hxt.le
  · have h1 : E t ^ 2 / E x ^ 2 ≤ 1 := by
      rw [div_le_one (by have := hEpos x; positivity)]
      have := hEle' x t hx hxt.le
      have := hEpos t
      gcongr
    have h0 : 0 < E t ^ 2 / E x ^ 2 := by have := hEpos x; have := hEpos t; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) (by positivity))]
    gcongr
    linarith

/-- **Liouville–Green approximation, exponential case with a large parameter** (Olver,
*Asymptotics and Special Functions*, Ch. 6, Thm. 2.1 for `u = 1`, and Ch. 10, Thm. 3.1).
Let `A ≠ 0` be twice differentiable on `(a, ∞)` and `ξ' = A⁻²` (for `A = f^{-1/4}` this is
`ξ = ∫ f^{1/2}`). For `u > 0`, the equation `w'' = (u² A⁻⁴ + g) w` has a solution
`w = A exp (-u ξ) (1 + ε)` with

`|ε x| ≤ exp (V x / (2u)) - 1`,   `|A(x)² ε'(x)| ≤ 2u (exp (V x / (2u)) - 1)`,

where `V x = ∫_{(x,∞)} |A A'' - g A²|` is the variation of the error-control function on
`(x, ∞)`. This is the solution recessive at `+∞`. -/
theorem exists_solution_exp {a u : ℝ} (hu : 0 < u) {A A' A'' ξ g : ℝ → ℝ}
    (hA : ∀ x, a < x → A x ≠ 0)
    (hA' : ∀ x, a < x → HasDerivAt A (A' x) x)
    (hA'' : ∀ x, a < x → HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' (Ioi a)) (hgc : ContinuousOn g (Ioi a))
    (hξ : ∀ x, a < x → HasDerivAt ξ ((A x ^ 2)⁻¹) x)
    (hFi : ∀ c, a < c → IntegrableOn (fun t => |A t * A'' t - g t * A t ^ 2|) (Ioi c)) :
    ∃ ε ε' w' : ℝ → ℝ, ∀ x, a < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => A y * Real.exp (-(u * ξ y)) * (1 + ε y)) (w' x) x ∧
      HasDerivAt w'
        ((u ^ 2 * (A x ^ 4)⁻¹ + g x) * (A x * Real.exp (-(u * ξ x)) * (1 + ε x))) x ∧
      |ε x| ≤ Real.exp ((∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2|) / (2 * u)) - 1 ∧
      |A x ^ 2 * ε' x| ≤
        2 * u * (Real.exp ((∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2|) / (2 * u)) - 1) := by
  obtain ⟨hE0, hE, hEle, hK⟩ := exp_kernel (a := a) hu hξ
  obtain ⟨ε, ε', w', H⟩ := exists_solution_of_kernel_bound (𝕜 := ℝ) (a := a)
    (κ := 1 / (2 * u)) (k := u) (A := A) (A' := A') (A'' := A'')
    (E := fun y => Real.exp (-(u * ξ y))) (g := g)
    hu.ne' (by positivity) hA hA' hA'' hA''c hgc hE0 hE hEle hK
    (fun c hc => by simpa only [Real.norm_eq_abs] using hFi c hc)
  refine ⟨ε, ε', w', fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H x hx
  simp only [Real.norm_eq_abs] at h4 h5
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · convert h4 using 3
    ring
  · convert h5 using 1
    rw [show 1 / (2 * u) * ∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2| =
      (∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2|) / (2 * u) by ring]
    field_simp

/-- **Liouville–Green approximation, oscillatory case with a large parameter** (Olver,
*Asymptotics and Special Functions*, Ch. 6, Thm. 2.2 for `u = ±1`, and Ch. 10, §3).
Let `A ≠ 0` be twice differentiable on `(a, ∞)` and `ξ' = A⁻²`. For real `u ≠ 0`, the equation
`w'' = (-u² A⁻⁴ + g) w` has a complex solution `w = A exp (-i u ξ) (1 + ε)` with

`‖ε x‖ ≤ exp (V x / |u|) - 1`,   `‖A(x)² ε'(x)‖ ≤ |u| (exp (V x / |u|) - 1)`,

where `V x = ∫_{(x,∞)} |A A'' - g A²|`. The two signs of `u` give the two oscillatory
solutions `A exp (∓ i |u| ξ) (1 + ε)`. -/
theorem exists_solution_osc {a u : ℝ} (hu : u ≠ 0) {A A' A'' ξ g : ℝ → ℝ}
    (hA : ∀ x, a < x → A x ≠ 0)
    (hA' : ∀ x, a < x → HasDerivAt A (A' x) x)
    (hA'' : ∀ x, a < x → HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' (Ioi a)) (hgc : ContinuousOn g (Ioi a))
    (hξ : ∀ x, a < x → HasDerivAt ξ ((A x ^ 2)⁻¹) x)
    (hFi : ∀ c, a < c → IntegrableOn (fun t => |A t * A'' t - g t * A t ^ 2|) (Ioi c)) :
    ∃ ε ε' w' : ℝ → ℂ, ∀ x, a < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => (A y : ℂ) * Complex.exp (-(Complex.I * u * ξ y)) * (1 + ε y))
        (w' x) x ∧
      HasDerivAt w' (((-(u ^ 2 * (A x ^ 4)⁻¹) + g x : ℝ) : ℂ) *
        ((A x : ℂ) * Complex.exp (-(Complex.I * u * ξ x)) * (1 + ε x))) x ∧
      ‖ε x‖ ≤ Real.exp ((∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2|) / |u|) - 1 ∧
      ‖(A x : ℂ) ^ 2 * ε' x‖ ≤
        |u| * (Real.exp ((∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2|) / |u|) - 1) := by
  set E : ℝ → ℂ := fun y => Complex.exp (-(Complex.I * u * ξ y)) with hEdef
  have hEn : ∀ y, ‖E y‖ = 1 := fun y => by
    simp [hEdef, Complex.norm_exp]
  have hu' : 0 < |u| := abs_pos.2 hu
  have hnorm : ∀ t, ‖(A t : ℂ) * (A'' t : ℂ) - (g t : ℂ) * (A t : ℂ) ^ 2‖ =
      |A t * A'' t - g t * A t ^ 2| := fun t => by
    have : ((A t * A'' t - g t * A t ^ 2 : ℝ) : ℂ) =
        (A t : ℂ) * (A'' t : ℂ) - (g t : ℂ) * (A t : ℂ) ^ 2 := by push_cast; ring
    rw [← this, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨ε, ε', w', H⟩ := exists_solution_of_kernel_bound (𝕜 := ℂ) (a := a)
    (κ := 1 / |u|) (k := Complex.I * u) (A := fun y => (A y : ℂ)) (A' := fun y => (A' y : ℂ))
    (A'' := fun y => (A'' y : ℂ)) (E := E) (g := fun y => (g y : ℂ))
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hu)) (by positivity)
    (fun x hx => Complex.ofReal_ne_zero.2 (hA x hx))
    (fun x hx => (hA' x hx).ofReal_comp) (fun x hx => (hA'' x hx).ofReal_comp)
    (Complex.continuous_ofReal.comp_continuousOn hA''c)
    (Complex.continuous_ofReal.comp_continuousOn hgc)
    (fun x _ => by rw [← norm_ne_zero_iff, hEn]; exact one_ne_zero)
    (fun x hx => by
      have := (((hξ x hx).ofReal_comp.const_mul (Complex.I * u)).neg).cexp
      refine this.congr_deriv ?_
      simp only [hEdef, Pi.neg_apply]
      push_cast
      ring)
    (fun x t _ _ => by rw [hEn, hEn])
    (fun x t _ _ => by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
      have : ‖1 - E t ^ 2 / E x ^ 2‖ ≤ 2 := (norm_sub_le _ _).trans (by
        rw [norm_div, norm_pow, norm_pow, hEn, hEn]; norm_num)
      calc ‖1 - E t ^ 2 / E x ^ 2‖ / (‖(2 : ℂ)‖ * (1 * |u|)) ≤ 2 / (2 * (1 * |u|)) := by
            rw [Complex.norm_two]
            gcongr
        _ = 1 / |u| := by field_simp)
    (fun c hc => by
      exact (hFi c hc).congr_fun (fun t _ => (hnorm t).symm) measurableSet_Ioi)
  have hV : ∀ x, ∫ t in Ioi x, ‖(A t : ℂ) * (A'' t : ℂ) - (g t : ℂ) * (A t : ℂ) ^ 2‖ =
      ∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2| := fun x => by
    congr 1
    ext t
    exact hnorm t
  refine ⟨ε, ε', w', fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H x hx
  rw [hV] at h4 h5
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · convert h3 using 2
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  · convert h4 using 3
    ring
  · convert h5 using 1
    rw [show 1 / |u| * ∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2| =
      (∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2|) / |u| by ring]
    field_simp

/-! ### The form with `f^{-1/4}` -/

/-- Olver's error-control density `f^{-1/4} (f^{-1/4})'' - g f^{-1/2}`, written out in terms of
`f`, `f'`, `f''`: its integral is the error-control function `F` of Olver, Ch. 6, (2.03). -/
noncomputable def errorDensity (f f' f'' g : ℝ → ℝ) (x : ℝ) : ℝ :=
  5 / 16 * f' x ^ 2 * f x ^ (-(5 / 2) : ℝ) - 1 / 4 * f'' x * f x ^ (-(3 / 2) : ℝ) -
    g x * f x ^ (-(1 / 2) : ℝ)

/-- The amplitude `A = f^{-1/4}`: its first two derivatives, `A⁻² = f^{1/2}`, `A⁻⁴ = f`, and
`A A'' - g A² = errorDensity f f' f'' g`. -/
theorem amplitude {a : ℝ} {f f' f'' g : ℝ → ℝ} (hf : ∀ x, a < x → 0 < f x)
    (hf' : ∀ x, a < x → HasDerivAt f (f' x) x) (hf'' : ∀ x, a < x → HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Ioi a)) {x : ℝ} (hx : a < x) :
    f x ^ (-(1 / 4) : ℝ) ≠ 0 ∧
    HasDerivAt (fun y => f y ^ (-(1 / 4) : ℝ)) (-(1 / 4) * f' x * f x ^ (-(5 / 4) : ℝ)) x ∧
    HasDerivAt (fun y => -(1 / 4) * f' y * f y ^ (-(5 / 4) : ℝ))
      (-(1 / 4) * f'' x * f x ^ (-(5 / 4) : ℝ) + 5 / 16 * f' x ^ 2 * f x ^ (-(9 / 4) : ℝ)) x ∧
    ContinuousOn (fun y => -(1 / 4) * f'' y * f y ^ (-(5 / 4) : ℝ) +
      5 / 16 * f' y ^ 2 * f y ^ (-(9 / 4) : ℝ)) (Ioi a) ∧
    ((f x ^ (-(1 / 4) : ℝ)) ^ 2)⁻¹ = √(f x) ∧
    ((f x ^ (-(1 / 4) : ℝ)) ^ 4)⁻¹ = f x ∧
    (f x ^ (-(1 / 4) : ℝ)) ^ 2 = (√(f x))⁻¹ ∧
    f x ^ (-(1 / 4) : ℝ) * (-(1 / 4) * f'' x * f x ^ (-(5 / 4) : ℝ) +
      5 / 16 * f' x ^ 2 * f x ^ (-(9 / 4) : ℝ)) - g x * (f x ^ (-(1 / 4) : ℝ)) ^ 2 =
      errorDensity f f' f'' g x := by
  have hfx := hf x hx
  have hpow : ∀ (p : ℝ) (n : ℕ), (f x ^ p) ^ n = f x ^ (p * n) := fun p n => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hfx.le]
  have hmul : ∀ p q : ℝ, f x ^ p * f x ^ q = f x ^ (p + q) := fun p q =>
    (Real.rpow_add hfx p q).symm
  have hsq : (f x ^ (-(1 / 4) : ℝ)) ^ 2 = (√(f x))⁻¹ := by
    rw [hpow, Real.sqrt_eq_rpow, ← Real.rpow_neg hfx.le]
    norm_num
  refine ⟨(Real.rpow_pos_of_pos hfx _).ne', ?_, ?_, ?_, ?_, ?_, hsq, ?_⟩
  · refine ((hf' x hx).rpow_const (p := -(1 / 4)) (Or.inl hfx.ne')).congr_deriv ?_
    rw [show (-(1 / 4 : ℝ)) - 1 = -(5 / 4) by norm_num]
    ring
  · refine (((hf'' x hx).const_mul (-(1 / 4))).mul
      ((hf' x hx).rpow_const (p := -(5 / 4)) (Or.inl hfx.ne'))).congr_deriv ?_
    rw [show (-(5 / 4 : ℝ)) - 1 = -(9 / 4) by norm_num]
    ring
  · have hfc : ContinuousOn f (Ioi a) := fun y hy => (hf' y hy).continuousAt.continuousWithinAt
    have hf'c : ContinuousOn f' (Ioi a) := fun y hy =>
      (hf'' y hy).continuousAt.continuousWithinAt
    exact ((continuousOn_const.mul hf''c).mul
        (hfc.rpow_const fun y hy => Or.inl (hf y hy).ne')).add
      ((continuousOn_const.mul (hf'c.pow 2)).mul
        (hfc.rpow_const fun y hy => Or.inl (hf y hy).ne'))
  · rw [hsq, inv_inv]
  · rw [hpow, ← Real.rpow_neg hfx.le]
    norm_num
  · have h1 : f x ^ (-(1 / 4) : ℝ) * (-(1 / 4) * f'' x * f x ^ (-(5 / 4) : ℝ)) =
        -(1 / 4) * f'' x * f x ^ (-(3 / 2) : ℝ) := by
      rw [show (-(3 / 2) : ℝ) = -(1 / 4) + -(5 / 4) by norm_num, ← hmul]
      ring
    have h2 : f x ^ (-(1 / 4) : ℝ) * (5 / 16 * f' x ^ 2 * f x ^ (-(9 / 4) : ℝ)) =
        5 / 16 * f' x ^ 2 * f x ^ (-(5 / 2) : ℝ) := by
      rw [show (-(5 / 2) : ℝ) = -(1 / 4) + -(9 / 4) by norm_num, ← hmul]
      ring
    rw [hsq, errorDensity, mul_add, h1, h2, Real.sqrt_eq_rpow, ← Real.rpow_neg hfx.le]
    ring

/-- The variation of the error-control function computed from `A = f^{-1/4}` agrees with the
integral of `|errorDensity|`. -/
theorem integral_errorDensity {a : ℝ} {f f' f'' g : ℝ → ℝ} (hf : ∀ x, a < x → 0 < f x)
    (hf' : ∀ x, a < x → HasDerivAt f (f' x) x) (hf'' : ∀ x, a < x → HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Ioi a)) {c : ℝ} (hc : a ≤ c) :
    EqOn (fun t => |f t ^ (-(1 / 4) : ℝ) * (-(1 / 4) * f'' t * f t ^ (-(5 / 4) : ℝ) +
        5 / 16 * f' t ^ 2 * f t ^ (-(9 / 4) : ℝ)) - g t * (f t ^ (-(1 / 4) : ℝ)) ^ 2|)
      (fun t => |errorDensity f f' f'' g t|) (Ioi c) := fun t ht => by
  show |_| = |_|
  rw [(amplitude (g := g) hf hf' hf'' hf''c (lt_of_le_of_lt hc ht)).2.2.2.2.2.2.2]

/-- **Olver's Liouville–Green theorem, exponential case** (Olver, *Asymptotics and Special
Functions*, Ch. 6, Thm. 2.1 for `u = 1`; Ch. 10, Thm. 3.1). Let `f > 0` be twice differentiable
with continuous `f''` and `g` continuous on `(a, ∞)`, and let `ξ' = f^{1/2}`. If the error-control
function `F = ∫ (f^{-1/4} (f^{-1/4})'' - g f^{-1/2})` has finite variation `V x` on `(x, ∞)`,
then for `u > 0` the equation `w'' = (u² f + g) w` has the solution
`w = f^{-1/4} exp (-u ξ) (1 + ε)` with

`|ε x| ≤ exp (V x / (2u)) - 1`,   `|ε' x| ≤ 2u f(x)^{1/2} (exp (V x / (2u)) - 1)`.

In particular `ε = O(1/u)` uniformly in `x` when `V` is bounded (`Real.exp_sub_one_le_mul_exp`). -/
theorem exists_solution_exp_of_pos {a u : ℝ} (hu : 0 < u) {f f' f'' g ξ : ℝ → ℝ}
    (hf : ∀ x, a < x → 0 < f x)
    (hf' : ∀ x, a < x → HasDerivAt f (f' x) x) (hf'' : ∀ x, a < x → HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Ioi a)) (hgc : ContinuousOn g (Ioi a))
    (hξ : ∀ x, a < x → HasDerivAt ξ (√(f x)) x)
    (hFi : ∀ c, a < c → IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioi c)) :
    ∃ ε ε' w' : ℝ → ℝ, ∀ x, a < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => f y ^ (-(1 / 4) : ℝ) * Real.exp (-(u * ξ y)) * (1 + ε y)) (w' x) x ∧
      HasDerivAt w' ((u ^ 2 * f x + g x) *
        (f x ^ (-(1 / 4) : ℝ) * Real.exp (-(u * ξ x)) * (1 + ε x))) x ∧
      |ε x| ≤ Real.exp ((∫ t in Ioi x, |errorDensity f f' f'' g t|) / (2 * u)) - 1 ∧
      |ε' x| ≤
        2 * u * √(f x) *
          (Real.exp ((∫ t in Ioi x, |errorDensity f f' f'' g t|) / (2 * u)) - 1) := by
  have H := fun x (hx : a < x) => amplitude (g := g) hf hf' hf'' hf''c hx
  obtain ⟨ε, ε', w', H'⟩ := exists_solution_exp hu (fun x hx => (H x hx).1)
    (fun x hx => (H x hx).2.1) (fun x hx => (H x hx).2.2.1) (H (a + 1) (by linarith)).2.2.2.1 hgc
    (fun x hx => by rw [(H x hx).2.2.2.2.1]; exact hξ x hx)
    (fun c hc => (hFi c hc).congr_fun (integral_errorDensity hf hf' hf'' hf''c hc.le).symm
      measurableSet_Ioi)
  refine ⟨ε, ε', w', fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H' x hx
  have hV := setIntegral_congr_fun (μ := volume) measurableSet_Ioi
    (integral_errorDensity (g := g) hf hf' hf'' hf''c hx.le)
  rw [hV] at h4 h5
  refine ⟨h1, h2, ?_, h4, ?_⟩
  · rwa [(H x hx).2.2.2.2.2.1] at h3
  · rw [abs_mul, (H x hx).2.2.2.2.2.2.1, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)] at h5
    have hs : 0 < √(f x) := Real.sqrt_pos.2 (hf x hx)
    rw [inv_mul_le_iff₀ hs] at h5
    linarith

/-- **Olver's Liouville–Green theorem, oscillatory case** (Olver, *Asymptotics and Special
Functions*, Ch. 6, Thm. 2.2 for `u = ±1`; Ch. 10, §3). Under the hypotheses of
`exists_solution_exp_of_pos`, for real `u ≠ 0` the equation `w'' = (-u² f + g) w` has the
complex solution `w = f^{-1/4} exp (-i u ξ) (1 + ε)` with

`‖ε x‖ ≤ exp (V x / |u|) - 1`,   `‖ε' x‖ ≤ |u| f(x)^{1/2} (exp (V x / |u|) - 1)`. -/
theorem exists_solution_osc_of_pos {a u : ℝ} (hu : u ≠ 0) {f f' f'' g ξ : ℝ → ℝ}
    (hf : ∀ x, a < x → 0 < f x)
    (hf' : ∀ x, a < x → HasDerivAt f (f' x) x) (hf'' : ∀ x, a < x → HasDerivAt f' (f'' x) x)
    (hf''c : ContinuousOn f'' (Ioi a)) (hgc : ContinuousOn g (Ioi a))
    (hξ : ∀ x, a < x → HasDerivAt ξ (√(f x)) x)
    (hFi : ∀ c, a < c → IntegrableOn (fun t => |errorDensity f f' f'' g t|) (Ioi c)) :
    ∃ ε ε' w' : ℝ → ℂ, ∀ x, a < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => ((f y ^ (-(1 / 4) : ℝ) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * u * ξ y)) * (1 + ε y)) (w' x) x ∧
      HasDerivAt w' (((-(u ^ 2 * f x) + g x : ℝ) : ℂ) * (((f x ^ (-(1 / 4) : ℝ) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * u * ξ x)) * (1 + ε x))) x ∧
      ‖ε x‖ ≤ Real.exp ((∫ t in Ioi x, |errorDensity f f' f'' g t|) / |u|) - 1 ∧
      ‖ε' x‖ ≤ |u| * √(f x) *
        (Real.exp ((∫ t in Ioi x, |errorDensity f f' f'' g t|) / |u|) - 1) := by
  have H := fun x (hx : a < x) => amplitude (g := g) hf hf' hf'' hf''c hx
  obtain ⟨ε, ε', w', H'⟩ := exists_solution_osc hu (fun x hx => (H x hx).1)
    (fun x hx => (H x hx).2.1) (fun x hx => (H x hx).2.2.1) (H (a + 1) (by linarith)).2.2.2.1 hgc
    (fun x hx => by rw [(H x hx).2.2.2.2.1]; exact hξ x hx)
    (fun c hc => (hFi c hc).congr_fun (integral_errorDensity hf hf' hf'' hf''c hc.le).symm
      measurableSet_Ioi)
  refine ⟨ε, ε', w', fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H' x hx
  have hV := setIntegral_congr_fun (μ := volume) measurableSet_Ioi
    (integral_errorDensity (g := g) hf hf' hf'' hf''c hx.le)
  rw [hV] at h4 h5
  refine ⟨h1, h2, ?_, h4, ?_⟩
  · rwa [(H x hx).2.2.2.2.2.1] at h3
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      (H x hx).2.2.2.2.2.2.1] at h5
    have hs : 0 < √(f x) := Real.sqrt_pos.2 (hf x hx)
    rw [inv_mul_le_iff₀ hs] at h5
    linarith

end LiouvilleGreen
