module

public import FormalResearch.ModularBootstrap.Chart.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Left-Edge Chart Functions and Dispersion Bounds (Lemma J4.0, `vlo:J40`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J4, Lemma J4.0 (`vlo:J40`,
lines 502–512).

Defines the derivatives `edgeX0Deriv`, `edgeY0Deriv`, `edgeMuDeriv`, `edgeNuDeriv`,
second derivatives `edgeX0Deriv2`, `edgeY0Deriv2`, `edgeNuDeriv2`, and the dispersion
function `edgeMV τ = Real.log (edgeX0 τ)`.

Proves **Lemma J4.0** (`lemma_J4_0`):
* Exact derivatives `x₀' = ½ √(1 - 1/cosh πτ)` and `y₀' = ½ √(1 + 1/cosh πτ)` for `τ ≥ 0`.
* `x₀ ≍ 1 + τ`, `x₀' ≍ min(τ, 1)`, `ν' ≍ 1 + τ`, `|ν''| ≤ C` on `τ ≥ 0`.
* `ν` increases strictly from `0` to `∞` on `[0, ∞)`.
* `m_V(τ) - m_V(τ/2) ≳ min(τ^2, 1)` and `m_V'(τ) / ν'(τ) ≳ τ / (1 + τ^3)` for `τ > 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Chart

/-! ### Section 1: Exact first and second derivatives on the left edge -/

/-- Smooth formula for `x₀'(τ) = (1/√2) sinh(πτ/2) / √(cosh πτ)` (`lower_o1_two_edge.tex`, Lemma J4.0). -/
noncomputable def edgeX0Deriv (τ : ℝ) : ℝ :=
  (1 / √2) * Real.sinh (Real.pi * τ / 2) / √(Real.cosh (Real.pi * τ))

/-- Smooth formula for `y₀'(τ) = (1/√2) cosh(πτ/2) / √(cosh πτ)` (`lower_o1_two_edge.tex`, Lemma J4.0). -/
noncomputable def edgeY0Deriv (τ : ℝ) : ℝ :=
  (1 / √2) * Real.cosh (Real.pi * τ / 2) / √(Real.cosh (Real.pi * τ))

/-- Derivative of `μ(τ) = (π/3) x₀(τ)`. -/
noncomputable def edgeMuDeriv (τ : ℝ) : ℝ := (Real.pi / 3) * edgeX0Deriv τ

/-- Derivative of `ν(τ) = (2π/3) x₀(τ) y₀(τ)`. -/
noncomputable def edgeNuDeriv (τ : ℝ) : ℝ :=
  (2 * Real.pi / 3) * (edgeX0Deriv τ * edgeY0 τ + edgeX0 τ * edgeY0Deriv τ)

/-- Second derivative `x₀''(τ) = (π / (2 √2)) cosh(πτ/2) / cosh(πτ)^{3/2}`. -/
noncomputable def edgeX0Deriv2 (τ : ℝ) : ℝ :=
  (Real.pi / (2 * √2)) * Real.cosh (Real.pi * τ / 2) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ)

/-- Second derivative `y₀''(τ) = -(π / (2 √2)) sinh(πτ/2) / cosh(πτ)^{3/2}`. -/
noncomputable def edgeY0Deriv2 (τ : ℝ) : ℝ :=
  -(Real.pi / (2 * √2)) * Real.sinh (Real.pi * τ / 2) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ)

/-- Second derivative `ν''(τ)`. -/
noncomputable def edgeNuDeriv2 (τ : ℝ) : ℝ :=
  (2 * Real.pi / 3) *
    (edgeX0Deriv2 τ * edgeY0 τ + 2 * edgeX0Deriv τ * edgeY0Deriv τ + edgeX0 τ * edgeY0Deriv2 τ)

/-- Dispersion function `m_V(τ) = log x₀(τ)` (`lower_o1_two_edge.tex`, Lemma J4.0). -/
noncomputable def edgeMV (τ : ℝ) : ℝ := Real.log (edgeX0 τ)

private lemma cosh_sub_one_eq (u : ℝ) : Real.cosh (2 * u) - 1 = 2 * Real.sinh u ^ 2 := by
  have h1 := Real.cosh_two_mul u
  have h2 := Real.cosh_sq_sub_sinh_sq u
  linarith

private lemma cosh_add_one_eq (u : ℝ) : Real.cosh (2 * u) + 1 = 2 * Real.cosh u ^ 2 := by
  have h1 := Real.cosh_two_mul u
  have h2 := Real.cosh_sq_sub_sinh_sq u
  linarith

private lemma monotoneOn_sub_linear {f f' : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ t, HasDerivAt f (f' t) t) (c : ℝ) (hge : ∀ t ∈ interior s, c ≤ f' t) :
    MonotoneOn (fun t : ℝ => f t - c * t) s := by
  refine monotoneOn_of_deriv_nonneg hs ?_ ?_ ?_
  · exact (continuous_iff_continuousAt.mpr fun t =>
      ((hf t).fun_sub (((hasDerivAt_id t).const_mul c).congr_deriv (mul_one c))).continuousAt).continuousOn
  · intro t _
    exact ((hf t).fun_sub (((hasDerivAt_id t).const_mul c).congr_deriv (mul_one c))).differentiableAt.differentiableWithinAt
  · intro t ht
    have hd : HasDerivAt (fun x : ℝ => f x - c * x) (f' t - c) t :=
      (hf t).fun_sub (((hasDerivAt_id t).const_mul c).congr_deriv (mul_one c))
    rw [hd.deriv]
    linarith [hge t ht]

private lemma monotoneOn_linear_sub {f f' : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ t, HasDerivAt f (f' t) t) (c : ℝ) (hle : ∀ t ∈ interior s, f' t ≤ c) :
    MonotoneOn (fun t : ℝ => c * t - f t) s := by
  refine monotoneOn_of_deriv_nonneg hs ?_ ?_ ?_
  · exact (continuous_iff_continuousAt.mpr fun t =>
      ((((hasDerivAt_id t).const_mul c).congr_deriv (mul_one c)).fun_sub (hf t)).continuousAt).continuousOn
  · intro t _
    exact ((((hasDerivAt_id t).const_mul c).congr_deriv (mul_one c)).fun_sub (hf t)).differentiableAt.differentiableWithinAt
  · intro t ht
    have hd : HasDerivAt (fun x : ℝ => c * x - f x) (c - f' t) t :=
      (((hasDerivAt_id t).const_mul c).congr_deriv (mul_one c)).fun_sub (hf t)
    rw [hd.deriv]
    linarith [hle t ht]

lemma edgeX0Deriv_eq_of_nonneg {τ : ℝ} (hτ : 0 ≤ τ) :
    edgeX0Deriv τ = (1 / 2 : ℝ) * √(1 - 1 / Real.cosh (Real.pi * τ)) := by
  unfold edgeX0Deriv
  have hc_pos : 0 < Real.cosh (Real.pi * τ) := Real.cosh_pos _
  have hsh_nn : 0 ≤ Real.sinh (Real.pi * τ / 2) :=
    Real.sinh_nonneg_iff.mpr (by nlinarith [Real.pi_pos])
  have hc_sub : Real.cosh (Real.pi * τ) - 1 = 2 * Real.sinh (Real.pi * τ / 2) ^ 2 := by
    have h := cosh_sub_one_eq (Real.pi * τ / 2)
    rwa [show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring] at h
  have hsub : 1 - 1 / Real.cosh (Real.pi * τ) =
      2 * Real.sinh (Real.pi * τ / 2) ^ 2 / Real.cosh (Real.pi * τ) := by
    rw [one_sub_div hc_pos.ne', hc_sub]
  rw [hsub, Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hsh_nn]
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [Real.sqrt_ne_zero'.mpr hc_pos, Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  nlinarith

lemma edgeY0Deriv_eq (τ : ℝ) :
    edgeY0Deriv τ = (1 / 2 : ℝ) * √(1 + 1 / Real.cosh (Real.pi * τ)) := by
  unfold edgeY0Deriv
  have hc_pos : 0 < Real.cosh (Real.pi * τ) := Real.cosh_pos _
  have hch_pos : 0 < Real.cosh (Real.pi * τ / 2) := Real.cosh_pos _
  have hc_add : Real.cosh (Real.pi * τ) + 1 = 2 * Real.cosh (Real.pi * τ / 2) ^ 2 := by
    have h := cosh_add_one_eq (Real.pi * τ / 2)
    rwa [show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring] at h
  have hadd : 1 + 1 / Real.cosh (Real.pi * τ) =
      2 * Real.cosh (Real.pi * τ / 2) ^ 2 / Real.cosh (Real.pi * τ) := by
    rw [one_add_div hc_pos.ne', hc_add]
  rw [hadd, Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hch_pos.le]
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [Real.sqrt_ne_zero'.mpr hc_pos, Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  nlinarith

lemma hasDerivAt_edgeX0 (τ : ℝ) : HasDerivAt edgeX0 (edgeX0Deriv τ) τ := by
  unfold edgeX0
  have hc_pos : 0 < Real.cosh (Real.pi * τ) := Real.cosh_pos _
  have hinner : HasDerivAt (fun t : ℝ => Real.cosh (Real.pi * t))
      (Real.sinh (Real.pi * τ) * Real.pi) τ := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_cosh (Real.pi * τ)).comp τ ((hasDerivAt_id τ).const_mul Real.pi)
  have hsqrt := hinner.sqrt hc_pos.ne'
  have harsinh := ((Real.hasDerivAt_arsinh (√(Real.cosh (Real.pi * τ)))).comp τ hsqrt).div_const Real.pi
  refine harsinh.congr_deriv ?_
  have hc_add : 1 + Real.cosh (Real.pi * τ) = 2 * Real.cosh (Real.pi * τ / 2) ^ 2 := by
    have h := cosh_add_one_eq (Real.pi * τ / 2)
    rw [show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring] at h
    linarith
  have h1c : 1 + √(Real.cosh (Real.pi * τ)) ^ 2 = 2 * Real.cosh (Real.pi * τ / 2) ^ 2 := by
    rw [Real.sq_sqrt hc_pos.le, hc_add]
  have hch_pos : 0 < Real.cosh (Real.pi * τ / 2) := Real.cosh_pos _
  have hsqrt2 : √(1 + √(Real.cosh (Real.pi * τ)) ^ 2) = √2 * Real.cosh (Real.pi * τ / 2) := by
    rw [h1c, Real.sqrt_mul (by norm_num), Real.sqrt_sq hch_pos.le]
  have hsh2 : Real.sinh (Real.pi * τ) = 2 * Real.sinh (Real.pi * τ / 2) * Real.cosh (Real.pi * τ / 2) := by
    have h := Real.sinh_two_mul (Real.pi * τ / 2)
    rwa [show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring] at h
  unfold edgeX0Deriv
  rw [hsqrt2, hsh2]
  have hpi := Real.pi_pos.ne'
  have hrt_c := (Real.sqrt_pos.mpr hc_pos).ne'
  have hrt_2 : √2 ≠ 0 := by positivity
  field_simp [hpi, hrt_c, hrt_2, hch_pos.ne']

lemma hasDerivAt_edgeY0 (τ : ℝ) : HasDerivAt edgeY0 (edgeY0Deriv τ) τ := by
  unfold edgeY0
  have hc_pos : 0 < Real.cosh (Real.pi * τ) := Real.cosh_pos _
  have hinner : HasDerivAt (fun t : ℝ => √2 * Real.sinh (Real.pi * t / 2))
      (√2 * (Real.cosh (Real.pi * τ / 2) * (Real.pi / 2))) τ := by
    have h1 : HasDerivAt (fun t : ℝ => Real.pi * t / 2) (Real.pi / 2) τ := by
      simpa using ((hasDerivAt_id τ).const_mul Real.pi).div_const 2
    exact ((Real.hasDerivAt_sinh _).comp τ h1).const_mul √2
  have harsinh := ((Real.hasDerivAt_arsinh _).comp τ hinner).div_const Real.pi
  refine harsinh.congr_deriv ?_
  have hc_sub : Real.cosh (Real.pi * τ) - 1 = 2 * Real.sinh (Real.pi * τ / 2) ^ 2 := by
    have h := cosh_sub_one_eq (Real.pi * τ / 2)
    rwa [show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring] at h
  have h1s : 1 + (√2 * Real.sinh (Real.pi * τ / 2)) ^ 2 = Real.cosh (Real.pi * τ) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    linarith
  unfold edgeY0Deriv
  rw [h1s]
  have hpi := Real.pi_pos.ne'
  have hrt_c := (Real.sqrt_pos.mpr hc_pos).ne'
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hpi, hrt_c]
  nlinarith

lemma hasDerivAt_edgeMu (τ : ℝ) : HasDerivAt edgeMu (edgeMuDeriv τ) τ :=
  (hasDerivAt_edgeX0 τ).const_mul _

lemma hasDerivAt_edgeNu (τ : ℝ) : HasDerivAt edgeNu (edgeNuDeriv τ) τ := by
  unfold edgeNu edgeNuDeriv
  have h := ((hasDerivAt_edgeX0 τ).const_mul (2 * Real.pi / 3)).mul (hasDerivAt_edgeY0 τ)
  refine h.congr_deriv ?_
  ring

private lemma hasDerivAt_cosh_rpow_neg_half (τ : ℝ) :
    HasDerivAt (fun t : ℝ => (Real.cosh (Real.pi * t)) ^ (-(1 / 2 : ℝ)))
      (-(1 / 2 : ℝ) * Real.pi * Real.sinh (Real.pi * τ) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ)) τ := by
  have hc_pos : 0 < Real.cosh (Real.pi * τ) := Real.cosh_pos _
  have hinner : HasDerivAt (fun t : ℝ => Real.cosh (Real.pi * t))
      (Real.sinh (Real.pi * τ) * Real.pi) τ := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_cosh (Real.pi * τ)).comp τ ((hasDerivAt_id τ).const_mul Real.pi)
  have hrp := hinner.rpow_const (Or.inl hc_pos.ne') (p := -(1 / 2 : ℝ))
  refine hrp.congr_deriv ?_
  have hpow : Real.cosh (Real.pi * τ) ^ (-(1 / 2 : ℝ) - 1) =
      (Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hc_pos.le]; congr 1; norm_num
  rw [hpow]
  ring

private lemma cosh_mul_cosh_two_sub_sinh (u : ℝ) :
    Real.cosh u * Real.cosh (2 * u) - Real.sinh u * Real.sinh (2 * u) = Real.cosh u := by
  rw [Real.cosh_two_mul, Real.sinh_two_mul]
  have h := Real.cosh_sq_sub_sinh_sq u
  linear_combination Real.cosh u * h

private lemma sinh_mul_cosh_two_sub_cosh (u : ℝ) :
    Real.sinh u * Real.cosh (2 * u) - Real.cosh u * Real.sinh (2 * u) = -Real.sinh u := by
  rw [Real.cosh_two_mul, Real.sinh_two_mul]
  have h := Real.cosh_sq_sub_sinh_sq u
  linear_combination -(Real.sinh u * h)

lemma hasDerivAt_edgeX0Deriv (τ : ℝ) : HasDerivAt edgeX0Deriv (edgeX0Deriv2 τ) τ := by
  have heq : edgeX0Deriv = fun t : ℝ =>
      (1 / √2) * Real.sinh (Real.pi * t / 2) * Real.cosh (Real.pi * t) ^ (-(1 / 2 : ℝ)) := by
    ext t
    unfold edgeX0Deriv
    rw [Real.sqrt_eq_rpow (Real.cosh (Real.pi * t)), Real.rpow_neg (Real.cosh_pos _).le, div_eq_mul_inv]
  rw [heq]
  have h1 : HasDerivAt (fun t : ℝ => (1 / √2) * Real.sinh (Real.pi * t / 2))
      ((1 / √2) * (Real.cosh (Real.pi * τ / 2) * (Real.pi / 2))) τ := by
    have hlin : HasDerivAt (fun t : ℝ => Real.pi * t / 2) (Real.pi / 2) τ := by
      simpa using ((hasDerivAt_id τ).const_mul Real.pi).div_const 2
    exact ((Real.hasDerivAt_sinh _).comp τ hlin).const_mul _
  have hprod := h1.mul (hasDerivAt_cosh_rpow_neg_half τ)
  refine hprod.congr_deriv ?_
  have hc_pos : 0 < Real.cosh (Real.pi * τ) := Real.cosh_pos _
  have hc_half : Real.cosh (Real.pi * τ) ^ (-(1 / 2 : ℝ)) =
      Real.cosh (Real.pi * τ) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) := by
    calc Real.cosh (Real.pi * τ) ^ (-(1 / 2 : ℝ))
        = Real.cosh (Real.pi * τ) ^ ((1 : ℝ) - 3 / 2) := by norm_num
      _ = Real.cosh (Real.pi * τ) ^ (1 : ℝ) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) :=
          Real.rpow_sub hc_pos 1 (3 / 2)
      _ = Real.cosh (Real.pi * τ) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) := by
          rw [Real.rpow_one]
  have hiden : Real.cosh (Real.pi * τ / 2) * Real.cosh (Real.pi * τ) -
      Real.sinh (Real.pi * τ / 2) * Real.sinh (Real.pi * τ) = Real.cosh (Real.pi * τ / 2) := by
    have h := cosh_mul_cosh_two_sub_sinh (Real.pi * τ / 2)
    rwa [show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring] at h
  rw [hc_half]
  unfold edgeX0Deriv2
  have hc32 : Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hc_pos _).ne'
  have h2 : √2 ≠ 0 := by positivity
  calc (1 / √2) * (Real.cosh (Real.pi * τ / 2) * (Real.pi / 2)) *
          (Real.cosh (Real.pi * τ) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ)) +
        (1 / √2) * Real.sinh (Real.pi * τ / 2) *
          (-(1 / 2) * Real.pi * Real.sinh (Real.pi * τ) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ))
      = (Real.pi / (2 * √2)) *
          (Real.cosh (Real.pi * τ / 2) * Real.cosh (Real.pi * τ) -
            Real.sinh (Real.pi * τ / 2) * Real.sinh (Real.pi * τ)) /
          Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) := by
        field_simp [hc32, h2]; ring
    _ = (Real.pi / (2 * √2)) * Real.cosh (Real.pi * τ / 2) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) := by
        rw [hiden]

lemma hasDerivAt_edgeY0Deriv (τ : ℝ) : HasDerivAt edgeY0Deriv (edgeY0Deriv2 τ) τ := by
  have heq : edgeY0Deriv = fun t : ℝ =>
      (1 / √2) * Real.cosh (Real.pi * t / 2) * Real.cosh (Real.pi * t) ^ (-(1 / 2 : ℝ)) := by
    ext t
    unfold edgeY0Deriv
    rw [Real.sqrt_eq_rpow (Real.cosh (Real.pi * t)), Real.rpow_neg (Real.cosh_pos _).le, div_eq_mul_inv]
  rw [heq]
  have h1 : HasDerivAt (fun t : ℝ => (1 / √2) * Real.cosh (Real.pi * t / 2))
      ((1 / √2) * (Real.sinh (Real.pi * τ / 2) * (Real.pi / 2))) τ := by
    have hlin : HasDerivAt (fun t : ℝ => Real.pi * t / 2) (Real.pi / 2) τ := by
      simpa using ((hasDerivAt_id τ).const_mul Real.pi).div_const 2
    exact ((Real.hasDerivAt_cosh _).comp τ hlin).const_mul _
  have hprod := h1.mul (hasDerivAt_cosh_rpow_neg_half τ)
  refine hprod.congr_deriv ?_
  have hc_pos : 0 < Real.cosh (Real.pi * τ) := Real.cosh_pos _
  have hc_half : Real.cosh (Real.pi * τ) ^ (-(1 / 2 : ℝ)) =
      Real.cosh (Real.pi * τ) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) := by
    calc Real.cosh (Real.pi * τ) ^ (-(1 / 2 : ℝ))
        = Real.cosh (Real.pi * τ) ^ ((1 : ℝ) - 3 / 2) := by norm_num
      _ = Real.cosh (Real.pi * τ) ^ (1 : ℝ) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) :=
          Real.rpow_sub hc_pos 1 (3 / 2)
      _ = Real.cosh (Real.pi * τ) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) := by
          rw [Real.rpow_one]
  have hiden : Real.sinh (Real.pi * τ / 2) * Real.cosh (Real.pi * τ) -
      Real.cosh (Real.pi * τ / 2) * Real.sinh (Real.pi * τ) = -Real.sinh (Real.pi * τ / 2) := by
    have h := sinh_mul_cosh_two_sub_cosh (Real.pi * τ / 2)
    rwa [show 2 * (Real.pi * τ / 2) = Real.pi * τ by ring] at h
  rw [hc_half]
  unfold edgeY0Deriv2
  have hc32 : Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hc_pos _).ne'
  have h2 : √2 ≠ 0 := by positivity
  calc (1 / √2) * (Real.sinh (Real.pi * τ / 2) * (Real.pi / 2)) *
          (Real.cosh (Real.pi * τ) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ)) +
        (1 / √2) * Real.cosh (Real.pi * τ / 2) *
          (-(1 / 2) * Real.pi * Real.sinh (Real.pi * τ) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ))
      = (Real.pi / (2 * √2)) *
          (Real.sinh (Real.pi * τ / 2) * Real.cosh (Real.pi * τ) -
            Real.cosh (Real.pi * τ / 2) * Real.sinh (Real.pi * τ)) /
          Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) := by
        field_simp [hc32, h2]; ring
    _ = -(Real.pi / (2 * √2)) * Real.sinh (Real.pi * τ / 2) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) := by
        rw [hiden]; ring

lemma hasDerivAt_edgeNuDeriv (τ : ℝ) : HasDerivAt edgeNuDeriv (edgeNuDeriv2 τ) τ := by
  unfold edgeNuDeriv edgeNuDeriv2
  have h1 := ((hasDerivAt_edgeX0Deriv τ).mul (hasDerivAt_edgeY0 τ)).add
    ((hasDerivAt_edgeX0 τ).mul (hasDerivAt_edgeY0Deriv τ))
  refine (h1.const_mul (2 * Real.pi / 3)).congr_deriv ?_
  ring

/-! ### Section 2: Positivity, asymptotics, monotonicity, and dispersion bounds -/

lemma edgeX0_zero : edgeX0 0 = xiStar := by
  unfold edgeX0 xiStar; simp

lemma edgeY0_zero : edgeY0 0 = 0 := by
  unfold edgeY0; simp

lemma edgeNu_zero : edgeNu 0 = 0 := by
  unfold edgeNu; rw [edgeY0_zero, mul_zero]

lemma edgeX0Deriv_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ edgeX0Deriv τ := by
  rw [edgeX0Deriv_eq_of_nonneg hτ]; positivity

lemma edgeX0Deriv_le_half {τ : ℝ} (hτ : 0 ≤ τ) : edgeX0Deriv τ ≤ 1 / 2 := by
  rw [edgeX0Deriv_eq_of_nonneg hτ]
  have hc_pos : 0 < Real.cosh (Real.pi * τ) := Real.cosh_pos _
  have hle : 1 - 1 / Real.cosh (Real.pi * τ) ≤ 1 := by
    have : 0 < 1 / Real.cosh (Real.pi * τ) := by positivity
    linarith
  have hrt : √(1 - 1 / Real.cosh (Real.pi * τ)) ≤ 1 := Real.sqrt_le_one.mpr hle
  linarith

lemma edgeY0Deriv_bounds (τ : ℝ) : 1 / 2 ≤ edgeY0Deriv τ ∧ edgeY0Deriv τ ≤ 1 / √2 := by
  rw [edgeY0Deriv_eq]
  have hc_ge1 : 1 ≤ Real.cosh (Real.pi * τ) := Real.one_le_cosh _
  have hc_pos : 0 < Real.cosh (Real.pi * τ) := Real.cosh_pos _
  have h1 : 1 ≤ 1 + 1 / Real.cosh (Real.pi * τ) := by
    have : 0 ≤ 1 / Real.cosh (Real.pi * τ) := div_nonneg zero_le_one hc_pos.le
    linarith
  have h2 : 1 + 1 / Real.cosh (Real.pi * τ) ≤ 2 := by
    have : 1 / Real.cosh (Real.pi * τ) ≤ 1 := div_le_one_of_le₀ hc_ge1 hc_pos.le
    linarith
  constructor
  · have hrt : 1 ≤ √(1 + 1 / Real.cosh (Real.pi * τ)) := Real.one_le_sqrt.mpr h1
    linarith
  · have hrt : √(1 + 1 / Real.cosh (Real.pi * τ)) ≤ √2 := Real.sqrt_le_sqrt h2
    have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h2' : (1 / 2 : ℝ) * √2 = 1 / √2 := by
      field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
      linarith
    calc (1 / 2 : ℝ) * √(1 + 1 / Real.cosh (Real.pi * τ))
        ≤ (1 / 2 : ℝ) * √2 := by gcongr
      _ = 1 / √2 := h2'

lemma xiStar_le_edgeX0 {τ : ℝ} (hτ : 0 ≤ τ) : xiStar ≤ edgeX0 τ := by
  have hmono : MonotoneOn edgeX0 (Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeX0 t).continuousAt).continuousOn
    (fun t _ => (hasDerivAt_edgeX0 t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [interior_Ici] at ht; rw [(hasDerivAt_edgeX0 t).deriv]; exact edgeX0Deriv_nonneg ht.le)
  rw [← edgeX0_zero]
  exact hmono (by simp) hτ hτ

lemma edgeX0_pos {τ : ℝ} (hτ : 0 ≤ τ) : 0 < edgeX0 τ :=
  lt_of_lt_of_le xiStar_pos (xiStar_le_edgeX0 hτ)

lemma hasDerivAt_edgeMV {τ : ℝ} (hτ : 0 ≤ τ) :
    HasDerivAt edgeMV (edgeX0Deriv τ / edgeX0 τ) τ :=
  (hasDerivAt_edgeX0 τ).log (edgeX0_pos hτ).ne'

lemma edgeY0_bounds {τ : ℝ} (hτ : 0 ≤ τ) : (1 / 2 : ℝ) * τ ≤ edgeY0 τ ∧ edgeY0 τ ≤ (1 / √2) * τ := by
  have hdiff_l := monotoneOn_sub_linear (convex_Ici 0) hasDerivAt_edgeY0 (1 / 2)
    (fun t _ => (edgeY0Deriv_bounds t).1)
  have hdiff_u := monotoneOn_linear_sub (convex_Ici 0) hasDerivAt_edgeY0 (1 / √2)
    (fun t _ => (edgeY0Deriv_bounds t).2)
  have h0l := hdiff_l (by simp : (0 : ℝ) ∈ Ici 0) hτ hτ
  have h0u := hdiff_u (by simp : (0 : ℝ) ∈ Ici 0) hτ hτ
  simp only [edgeY0_zero, mul_zero, sub_zero] at h0l h0u
  exact ⟨by linarith, by linarith⟩

lemma edgeX0_asymp :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ {τ : ℝ}, 0 ≤ τ → c₁ * (1 + τ) ≤ edgeX0 τ ∧ edgeX0 τ ≤ c₂ * (1 + τ) := by
  have hc1_pos : 0 < Real.cosh Real.pi := Real.cosh_pos Real.pi
  have hc1_gt : 1 < Real.cosh Real.pi := by
    have hsq : Real.cosh Real.pi ^ 2 = 1 + Real.sinh Real.pi ^ 2 := by
      linarith [Real.cosh_sq_sub_sinh_sq Real.pi]
    have hsh : 0 < Real.sinh Real.pi ^ 2 := sq_pos_of_ne_zero (Real.sinh_ne_zero.mpr Real.pi_pos.ne')
    nlinarith [Real.cosh_pos Real.pi]
  let α : ℝ := (1 / 2 : ℝ) * √(1 - 1 / Real.cosh Real.pi)
  have hα_pos : 0 < α := by
    have : 0 < 1 - 1 / Real.cosh Real.pi := sub_pos.mpr (div_lt_one hc1_pos |>.mpr hc1_gt)
    positivity
  have hge_α : ∀ {τ : ℝ}, 1 ≤ τ → α ≤ edgeX0Deriv τ := by
    intro τ hτ
    rw [edgeX0Deriv_eq_of_nonneg (by linarith)]
    have hc_le : Real.cosh Real.pi ≤ Real.cosh (Real.pi * τ) := by
      rw [Real.cosh_le_cosh, abs_of_pos Real.pi_pos, abs_of_nonneg (by nlinarith [Real.pi_pos])]
      nlinarith [Real.pi_pos]
    have hdiv : 1 / Real.cosh (Real.pi * τ) ≤ 1 / Real.cosh Real.pi :=
      one_div_le_one_div_of_le hc1_pos hc_le
    dsimp [α]
    gcongr
  let m := min xiStar α
  have hm_pos : 0 < m := lt_min xiStar_pos hα_pos
  let c₁ : ℝ := m / 2
  let c₂ : ℝ := max xiStar (1 / 2)
  refine ⟨c₁, c₂, by positivity, by positivity [xiStar_pos], fun {τ} hτ => ?_⟩
  constructor
  · by_cases h1 : τ ≤ 1
    · have hm1 : m ≤ xiStar := min_le_left _ _
      calc c₁ * (1 + τ) ≤ (xiStar / 2) * (1 + 1) := by dsimp [c₁]; nlinarith [xiStar_pos]
        _ = xiStar := by ring
        _ ≤ edgeX0 τ := xiStar_le_edgeX0 hτ
    · push Not at h1
      have hmono := monotoneOn_sub_linear (convex_Ici 1) hasDerivAt_edgeX0 α
        (fun t ht => by rw [interior_Ici] at ht; exact hge_α ht.le)
      have hdiff := hmono (by simp : (1 : ℝ) ∈ Ici 1) h1.le h1.le
      have hx1 : xiStar ≤ edgeX0 1 := xiStar_le_edgeX0 zero_le_one
      have hx_lb : xiStar + α * (τ - 1) ≤ edgeX0 τ := by linarith
      have hm1 : m ≤ xiStar := min_le_left _ _
      have hm2 : m ≤ α := min_le_right _ _
      have hm_lb : m * τ ≤ xiStar + α * (τ - 1) := by
        calc m * τ = m * 1 + m * (τ - 1) := by ring
          _ ≤ xiStar * 1 + α * (τ - 1) := by nlinarith
          _ = xiStar + α * (τ - 1) := by ring
      have h1τ : 1 + τ ≤ 2 * τ := by linarith
      calc c₁ * (1 + τ) ≤ (m / 2) * (2 * τ) := by dsimp [c₁]; nlinarith
        _ = m * τ := by ring
        _ ≤ edgeX0 τ := le_trans hm_lb hx_lb
  · have hmono_u := monotoneOn_linear_sub (convex_Ici 0) hasDerivAt_edgeX0 (1 / 2)
      (fun t ht => by rw [interior_Ici] at ht; exact edgeX0Deriv_le_half ht.le)
    have h0 := hmono_u (by simp : (0 : ℝ) ∈ Ici 0) hτ hτ
    simp only [mul_zero, edgeX0_zero, zero_sub] at h0
    have hle : edgeX0 τ ≤ xiStar + (1 / 2 : ℝ) * τ := by linarith
    have hc2_1 : xiStar ≤ c₂ := le_max_left _ _
    have hc2_2 : (1 / 2 : ℝ) ≤ c₂ := le_max_right _ _
    nlinarith

lemma edgeX0Deriv_asymp :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ {τ : ℝ}, 0 ≤ τ → c₁ * min τ 1 ≤ edgeX0Deriv τ ∧ edgeX0Deriv τ ≤ c₂ * min τ 1 := by
  have hc1_pos : 0 < Real.cosh Real.pi := Real.cosh_pos Real.pi
  have hc1_gt : 1 < Real.cosh Real.pi := by
    have hsq : Real.cosh Real.pi ^ 2 = 1 + Real.sinh Real.pi ^ 2 := by
      linarith [Real.cosh_sq_sub_sinh_sq Real.pi]
    have hsh : 0 < Real.sinh Real.pi ^ 2 := sq_pos_of_ne_zero (Real.sinh_ne_zero.mpr Real.pi_pos.ne')
    nlinarith [Real.cosh_pos Real.pi]
  let α : ℝ := (1 / 2 : ℝ) * √(1 - 1 / Real.cosh Real.pi)
  have hα_pos : 0 < α := by
    have : 0 < 1 - 1 / Real.cosh Real.pi := sub_pos.mpr (div_lt_one hc1_pos |>.mpr hc1_gt)
    positivity
  let β₂ : ℝ := (Real.pi / (2 * √2)) / Real.cosh Real.pi ^ (3 / 2 : ℝ)
  have hβ₂_pos : 0 < β₂ := by positivity [Real.pi_pos, hc1_pos]
  let γ₂ : ℝ := Real.pi / (2 * √2)
  have hγ₂_pos : 0 < γ₂ := by positivity [Real.pi_pos]
  have hderiv2_bounds : ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → β₂ ≤ edgeX0Deriv2 t ∧ edgeX0Deriv2 t ≤ γ₂ := by
    intro t ht0 ht1
    unfold edgeX0Deriv2
    have hch_t_pos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
    have hch_t_ge1 : 1 ≤ Real.cosh (Real.pi * t) := Real.one_le_cosh _
    have hch_half_ge1 : 1 ≤ Real.cosh (Real.pi * t / 2) := Real.one_le_cosh _
    have hch_half_le : Real.cosh (Real.pi * t / 2) ≤ Real.cosh (Real.pi * t) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (by nlinarith [Real.pi_pos]),
        abs_of_nonneg (by nlinarith [Real.pi_pos])]
      nlinarith [Real.pi_pos]
    have hch_t_le : Real.cosh (Real.pi * t) ≤ Real.cosh Real.pi := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (by nlinarith [Real.pi_pos]), abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]
    constructor
    · have h32_le : Real.cosh (Real.pi * t) ^ (3 / 2 : ℝ) ≤ Real.cosh Real.pi ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hch_t_pos.le hch_t_le (by norm_num)
      have hnum : Real.pi / (2 * √2) ≤ (Real.pi / (2 * √2)) * Real.cosh (Real.pi * t / 2) := by
        nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
      calc β₂ = (Real.pi / (2 * √2)) / Real.cosh Real.pi ^ (3 / 2 : ℝ) := rfl
        _ ≤ ((Real.pi / (2 * √2)) * Real.cosh (Real.pi * t / 2)) / Real.cosh (Real.pi * t) ^ (3 / 2 : ℝ) :=
            div_le_div₀ (by positivity [Real.pi_pos]) hnum (Real.rpow_pos_of_pos hch_t_pos _) h32_le
    · have h32_ge : Real.cosh (Real.pi * t) ≤ Real.cosh (Real.pi * t) ^ (3 / 2 : ℝ) := by
        calc Real.cosh (Real.pi * t) = Real.cosh (Real.pi * t) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ Real.cosh (Real.pi * t) ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hch_t_ge1 (by norm_num)
      have hdiv_le : Real.cosh (Real.pi * t / 2) / Real.cosh (Real.pi * t) ^ (3 / 2 : ℝ) ≤ 1 := by
        rw [div_le_one (Real.rpow_pos_of_pos hch_t_pos _)]
        linarith
      calc (Real.pi / (2 * √2)) * Real.cosh (Real.pi * t / 2) / Real.cosh (Real.pi * t) ^ (3 / 2 : ℝ)
          = γ₂ * (Real.cosh (Real.pi * t / 2) / Real.cosh (Real.pi * t) ^ (3 / 2 : ℝ)) := by
            dsimp [γ₂]; ring
        _ ≤ γ₂ * 1 := by gcongr
        _ = γ₂ := mul_one _
  have hx0d0 : edgeX0Deriv 0 = 0 := by unfold edgeX0Deriv; simp
  refine ⟨min α β₂, max (1 / 2) γ₂, by positivity [hα_pos, hβ₂_pos], by positivity, fun {τ} hτ => ?_⟩
  by_cases h1 : τ ≤ 1
  · rw [min_eq_left h1]
    have hmono_l := monotoneOn_sub_linear (convex_Icc 0 1) hasDerivAt_edgeX0Deriv β₂
      (fun t ht => by rw [interior_Icc] at ht; exact (hderiv2_bounds ht.1.le ht.2.le).1)
    have hmono_u := monotoneOn_linear_sub (convex_Icc 0 1) hasDerivAt_edgeX0Deriv γ₂
      (fun t ht => by rw [interior_Icc] at ht; exact (hderiv2_bounds ht.1.le ht.2.le).2)
    have hl := hmono_l (by simp : (0 : ℝ) ∈ Icc 0 1) ⟨hτ, h1⟩ hτ
    have hu := hmono_u (by simp : (0 : ℝ) ∈ Icc 0 1) ⟨hτ, h1⟩ hτ
    simp only [hx0d0, mul_zero, sub_zero] at hl hu
    constructor
    · calc min α β₂ * τ ≤ β₂ * τ := mul_le_mul_of_nonneg_right (min_le_right _ _) hτ
        _ ≤ edgeX0Deriv τ := by linarith
    · calc edgeX0Deriv τ ≤ γ₂ * τ := by linarith
        _ ≤ max (1 / 2) γ₂ * τ := mul_le_mul_of_nonneg_right (le_max_right _ _) hτ
  · push Not at h1
    rw [min_eq_right h1.le, mul_one]
    have hge_α : α ≤ edgeX0Deriv τ := by
      rw [edgeX0Deriv_eq_of_nonneg hτ]
      have hc_le : Real.cosh Real.pi ≤ Real.cosh (Real.pi * τ) := by
        rw [Real.cosh_le_cosh, abs_of_pos Real.pi_pos, abs_of_nonneg (by nlinarith [Real.pi_pos])]
        nlinarith [Real.pi_pos]
      have hdiv : 1 / Real.cosh (Real.pi * τ) ≤ 1 / Real.cosh Real.pi :=
        one_div_le_one_div_of_le hc1_pos hc_le
      dsimp [α]
      gcongr
    exact ⟨(min_le_left _ _).trans hge_α, by simpa using (edgeX0Deriv_le_half hτ).trans (le_max_left (1 / 2) γ₂)⟩

lemma edgeNuDeriv_asymp :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ {τ : ℝ}, 0 ≤ τ → c₁ * (1 + τ) ≤ edgeNuDeriv τ ∧ edgeNuDeriv τ ≤ c₂ * (1 + τ) := by
  obtain ⟨cx1, cx2, hcx1, hcx2, hx_as⟩ := edgeX0_asymp
  let c₁ : ℝ := (Real.pi / 3) * cx1
  let c₂ : ℝ := (2 * Real.pi / 3) * (1 / (2 * √2) + cx2 / √2)
  refine ⟨c₁, c₂, by positivity [Real.pi_pos], by positivity [Real.pi_pos], fun {τ} hτ => ?_⟩
  unfold edgeNuDeriv
  have hy0_nn : 0 ≤ edgeY0 τ := by linarith [(edgeY0_bounds hτ).1]
  have hx0d_nn := edgeX0Deriv_nonneg hτ
  have hy0d_lb := (edgeY0Deriv_bounds τ).1
  have hy0d_ub := (edgeY0Deriv_bounds τ).2
  have hx_lb := (hx_as hτ).1
  have hx_ub := (hx_as hτ).2
  have hy_ub := (edgeY0_bounds hτ).2
  constructor
  · calc c₁ * (1 + τ) = (2 * Real.pi / 3) * (cx1 * (1 + τ) * (1 / 2)) := by dsimp [c₁]; ring
      _ ≤ (2 * Real.pi / 3) * (edgeX0 τ * edgeY0Deriv τ) := by
          gcongr
          exact (edgeX0_pos hτ).le
      _ ≤ (2 * Real.pi / 3) * (edgeX0Deriv τ * edgeY0 τ + edgeX0 τ * edgeY0Deriv τ) := by
          have : 0 ≤ edgeX0Deriv τ * edgeY0 τ := mul_nonneg hx0d_nn hy0_nn
          nlinarith [Real.pi_pos]
  · have h1 : edgeX0Deriv τ * edgeY0 τ ≤ (1 / 2) * ((1 / √2) * τ) :=
      mul_le_mul (edgeX0Deriv_le_half hτ) hy_ub hy0_nn (by norm_num)
    have h2 : edgeX0 τ * edgeY0Deriv τ ≤ (cx2 * (1 + τ)) * (1 / √2) :=
      mul_le_mul hx_ub hy0d_ub (by linarith) (by positivity)
    have hτ_le : τ ≤ 1 + τ := by linarith
    calc (2 * Real.pi / 3) * (edgeX0Deriv τ * edgeY0 τ + edgeX0 τ * edgeY0Deriv τ)
        ≤ (2 * Real.pi / 3) * ((1 / 2) * ((1 / √2) * (1 + τ)) + (cx2 * (1 + τ)) * (1 / √2)) := by
          have hpi_pos : 0 < 2 * Real.pi / 3 := by positivity [Real.pi_pos]
          nlinarith
      _ = c₂ * (1 + τ) := by dsimp [c₂]; ring

private lemma one_add_tau_mul_exp_neg_le (u : ℝ) : (1 + u) * Real.exp (-u) ≤ 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos u)]
  linarith [Real.add_one_le_exp u]

lemma edgeNuDeriv2_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ {τ : ℝ}, 0 ≤ τ → |edgeNuDeriv2 τ| ≤ C := by
  obtain ⟨_, cx2, _, hcx2, hx_as⟩ := edgeX0_asymp
  have hdec : ∀ {τ : ℝ}, 0 ≤ τ →
      |edgeX0Deriv2 τ| ≤ (Real.pi / √2) * Real.exp (-(Real.pi * τ / 2)) ∧
      |edgeY0Deriv2 τ| ≤ (Real.pi / √2) * Real.exp (-(Real.pi * τ / 2)) := by
    intro τ hτ
    have hc_pos : 0 < Real.cosh (Real.pi * τ) := Real.cosh_pos _
    have harg_nn : 0 ≤ Real.pi * τ / 2 := by nlinarith [Real.pi_pos]
    have hch_half_le : Real.cosh (Real.pi * τ / 2) ≤ Real.exp (Real.pi * τ / 2) := by
      rw [Real.cosh_eq]
      have : Real.exp (-(Real.pi * τ / 2)) ≤ Real.exp (Real.pi * τ / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hsh_half_le : |Real.sinh (Real.pi * τ / 2)| ≤ Real.exp (Real.pi * τ / 2) := by
      have hexp1 : 0 < Real.exp (-(Real.pi * τ / 2)) := Real.exp_pos _
      have hexp2 : Real.exp (-(Real.pi * τ / 2)) ≤ Real.exp (Real.pi * τ / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      rw [Real.sinh_eq, abs_of_nonneg (by linarith)]
      linarith
    have hc_lb : (1 / 2 : ℝ) * Real.exp (Real.pi * τ) ≤ Real.cosh (Real.pi * τ) := by
      rw [Real.cosh_eq]
      have : 0 < Real.exp (-(Real.pi * τ)) := Real.exp_pos _
      linarith
    have hc_lb_pow : (1 / 2 : ℝ) * Real.exp (Real.pi * τ) ≤ Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) := by
      calc (1 / 2 : ℝ) * Real.exp (Real.pi * τ) ≤ Real.cosh (Real.pi * τ) := hc_lb
        _ = Real.cosh (Real.pi * τ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (Real.one_le_cosh _) (by norm_num)
    have hdiv_exp : Real.exp (Real.pi * τ / 2) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) ≤
        2 * Real.exp (-(Real.pi * τ / 2)) := by
      have hexp_split : Real.exp (Real.pi * τ) =
          Real.exp (Real.pi * τ / 2) * Real.exp (Real.pi * τ / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      have hden_pos : 0 < (1 / 2 : ℝ) * Real.exp (Real.pi * τ) := by positivity
      calc Real.exp (Real.pi * τ / 2) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ)
          ≤ Real.exp (Real.pi * τ / 2) / ((1 / 2 : ℝ) * Real.exp (Real.pi * τ)) :=
            div_le_div_of_nonneg_left (Real.exp_pos _).le hden_pos hc_lb_pow
        _ = 2 * Real.exp (-(Real.pi * τ / 2)) := by
            rw [hexp_split, Real.exp_neg]
            field_simp [(Real.exp_pos (Real.pi * τ / 2)).ne']
    constructor
    · unfold edgeX0Deriv2
      rw [abs_of_nonneg (by positivity [Real.pi_pos, Real.cosh_pos (Real.pi * τ / 2), hc_pos])]
      calc (Real.pi / (2 * √2)) * Real.cosh (Real.pi * τ / 2) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ)
          ≤ (Real.pi / (2 * √2)) * Real.exp (Real.pi * τ / 2) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) := by
            gcongr
        _ = (Real.pi / (2 * √2)) * (Real.exp (Real.pi * τ / 2) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ)) := by
            ring
        _ ≤ (Real.pi / (2 * √2)) * (2 * Real.exp (-(Real.pi * τ / 2))) := by gcongr
        _ = (Real.pi / √2) * Real.exp (-(Real.pi * τ / 2)) := by ring
    · unfold edgeY0Deriv2
      rw [abs_div, abs_mul, abs_neg, abs_of_pos (by positivity [Real.pi_pos]),
        abs_of_pos (Real.rpow_pos_of_pos hc_pos _)]
      calc (Real.pi / (2 * √2)) * |Real.sinh (Real.pi * τ / 2)| / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ)
          ≤ (Real.pi / (2 * √2)) * Real.exp (Real.pi * τ / 2) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ) := by
            gcongr
        _ = (Real.pi / (2 * √2)) * (Real.exp (Real.pi * τ / 2) / Real.cosh (Real.pi * τ) ^ (3 / 2 : ℝ)) := by
            ring
        _ ≤ (Real.pi / (2 * √2)) * (2 * Real.exp (-(Real.pi * τ / 2))) := by gcongr
        _ = (Real.pi / √2) * Real.exp (-(Real.pi * τ / 2)) := by ring
  let C : ℝ := (2 * Real.pi / 3) * (2 / √2 + cx2 * (Real.pi / √2) + 1 / √2)
  refine ⟨C, by positivity [Real.pi_pos, hcx2], fun {τ} hτ => ?_⟩
  unfold edgeNuDeriv2
  have h1 : |edgeX0Deriv2 τ * edgeY0 τ| ≤ 2 / √2 := by
    rw [abs_mul]
    have hy_nn : 0 ≤ edgeY0 τ := by linarith [(edgeY0_bounds hτ).1]
    have hy_ub : |edgeY0 τ| ≤ (1 / √2) * τ := by rw [abs_of_nonneg hy_nn]; exact (edgeY0_bounds hτ).2
    have hxd := (hdec hτ).1
    have hτ_exp : (Real.pi * τ / 2) * Real.exp (-(Real.pi * τ / 2)) ≤ 1 := by
      have := one_add_tau_mul_exp_neg_le (Real.pi * τ / 2)
      have hexp : 0 < Real.exp (-(Real.pi * τ / 2)) := Real.exp_pos _
      nlinarith
    calc |edgeX0Deriv2 τ| * |edgeY0 τ|
        ≤ ((Real.pi / √2) * Real.exp (-(Real.pi * τ / 2))) * ((1 / √2) * τ) :=
          mul_le_mul hxd hy_ub (abs_nonneg _) (by positivity [Real.pi_pos])
      _ = (2 / (√2 * √2)) * ((Real.pi * τ / 2) * Real.exp (-(Real.pi * τ / 2))) := by ring
      _ = 1 * ((Real.pi * τ / 2) * Real.exp (-(Real.pi * τ / 2))) := by
          rw [Real.mul_self_sqrt (by norm_num)]; norm_num
      _ ≤ 1 := by linarith
      _ ≤ 2 / √2 := by
          have hsq : √2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
          linarith
  have h2 : |2 * edgeX0Deriv τ * edgeY0Deriv τ| ≤ 1 / √2 := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (edgeX0Deriv_nonneg hτ))
      (by linarith [(edgeY0Deriv_bounds τ).1]))]
    have := mul_le_mul (edgeX0Deriv_le_half hτ) (edgeY0Deriv_bounds τ).2
      (by linarith [(edgeY0Deriv_bounds τ).1]) (by norm_num)
    linarith
  have h3 : |edgeX0 τ * edgeY0Deriv2 τ| ≤ cx2 * (Real.pi / √2) := by
    rw [abs_mul, abs_of_pos (edgeX0_pos hτ)]
    have hτ_exp : (1 + Real.pi * τ / 2) * Real.exp (-(Real.pi * τ / 2)) ≤ 1 :=
      one_add_tau_mul_exp_neg_le (Real.pi * τ / 2)
    have h1τ : 1 + τ ≤ 1 + Real.pi * τ / 2 := by
      have hpi2 : 1 ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
      nlinarith
    have hexp_nn : 0 ≤ Real.exp (-(Real.pi * τ / 2)) := (Real.exp_pos _).le
    have h_bd : (1 + τ) * Real.exp (-(Real.pi * τ / 2)) ≤ 1 := by nlinarith
    calc edgeX0 τ * |edgeY0Deriv2 τ|
        ≤ (cx2 * (1 + τ)) * ((Real.pi / √2) * Real.exp (-(Real.pi * τ / 2))) :=
          mul_le_mul (hx_as hτ).2 (hdec hτ).2 (abs_nonneg _) (by positivity)
      _ = cx2 * (Real.pi / √2) * ((1 + τ) * Real.exp (-(Real.pi * τ / 2))) := by ring
      _ ≤ cx2 * (Real.pi / √2) * 1 := by gcongr
      _ = cx2 * (Real.pi / √2) := mul_one _
  rw [abs_mul, abs_of_pos (by positivity [Real.pi_pos])]
  have htri : |edgeX0Deriv2 τ * edgeY0 τ + 2 * edgeX0Deriv τ * edgeY0Deriv τ + edgeX0 τ * edgeY0Deriv2 τ| ≤
      |edgeX0Deriv2 τ * edgeY0 τ| + |2 * edgeX0Deriv τ * edgeY0Deriv τ| + |edgeX0 τ * edgeY0Deriv2 τ| := by
    calc |edgeX0Deriv2 τ * edgeY0 τ + 2 * edgeX0Deriv τ * edgeY0Deriv τ + edgeX0 τ * edgeY0Deriv2 τ|
        ≤ |edgeX0Deriv2 τ * edgeY0 τ + 2 * edgeX0Deriv τ * edgeY0Deriv τ| + |edgeX0 τ * edgeY0Deriv2 τ| :=
          abs_add_le _ _
      _ ≤ |edgeX0Deriv2 τ * edgeY0 τ| + |2 * edgeX0Deriv τ * edgeY0Deriv τ| + |edgeX0 τ * edgeY0Deriv2 τ| := by
          linarith [abs_add_le (edgeX0Deriv2 τ * edgeY0 τ) (2 * edgeX0Deriv τ * edgeY0Deriv τ)]
  have hpi_nn : 0 ≤ 2 * Real.pi / 3 := by positivity [Real.pi_pos]
  calc (2 * Real.pi / 3) *
        |edgeX0Deriv2 τ * edgeY0 τ + 2 * edgeX0Deriv τ * edgeY0Deriv τ + edgeX0 τ * edgeY0Deriv2 τ|
      ≤ (2 * Real.pi / 3) * (2 / √2 + 1 / √2 + cx2 * (Real.pi / √2)) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hpi_nn
    _ = C := by dsimp [C]; ring

lemma edgeNu_strictMonoOn : StrictMonoOn edgeNu (Ici 0) := by
  obtain ⟨c₁, _, hc₁, _, hnu⟩ := edgeNuDeriv_asymp
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeNu t).continuousAt).continuousOn ?_
  intro t ht
  rw [interior_Ici] at ht
  rw [(hasDerivAt_edgeNu t).deriv]
  have hbd := (hnu ht.le).1
  have hpos : 0 < c₁ * (1 + t) := by positivity [ht.le]
  linarith

lemma tendsto_edgeNu_atTop : Tendsto edgeNu atTop atTop := by
  have hmul : (fun τ : ℝ => (Real.pi / 3) * xiStar * τ) ≤ᶠ[atTop] edgeNu := by
    refine Filter.eventually_of_mem (Ici_mem_atTop 0) fun τ hτ => ?_
    unfold edgeNu
    have h1 := xiStar_le_edgeX0 hτ
    have h2 := (edgeY0_bounds hτ).1
    calc (Real.pi / 3) * xiStar * τ
        = (2 * Real.pi / 3) * xiStar * ((1 / 2) * τ) := by ring
      _ ≤ (2 * Real.pi / 3) * edgeX0 τ * edgeY0 τ :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity [Real.pi_pos])) h2
            (mul_nonneg (by norm_num) hτ) (mul_nonneg (by positivity [Real.pi_pos]) (edgeX0_pos hτ).le)
  exact tendsto_atTop_mono' atTop hmul
    (tendsto_id.const_mul_atTop (by positivity [Real.pi_pos, xiStar_pos] : 0 < (Real.pi / 3) * xiStar))

lemma edgeMV_diff_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ {τ : ℝ}, 0 < τ → c * min (τ ^ 2) 1 ≤ edgeMV τ - edgeMV (τ / 2) := by
  obtain ⟨cx1, cx2, hcx1, hcx2, hx_as⟩ := edgeX0_asymp
  obtain ⟨cd1, _, hcd1, _, hxd_as⟩ := edgeX0Deriv_asymp
  let c : ℝ := cd1 / (8 * cx2)
  refine ⟨c, by positivity, fun {τ} hτ => ?_⟩
  let κ : ℝ := cd1 * min (τ / 2) 1 / (cx2 * (1 + τ))
  have hmono : MonotoneOn (fun t : ℝ => edgeMV t - κ * t) (Icc (τ / 2) τ) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc (τ / 2) τ) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ (by fun_prop)
      refine ContinuousOn.log ?_ fun t ht => (edgeX0_pos (by linarith [ht.1])).ne'
      exact (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeX0 t).continuousAt).continuousOn
    · intro t ht
      exact ((hasDerivAt_edgeMV (by linarith [(interior_subset ht).1])).fun_sub
        (((hasDerivAt_id t).const_mul κ).congr_deriv (mul_one κ))).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht_mem := interior_subset ht
      rw [interior_Icc] at ht
      have ht_nn : 0 ≤ t := by linarith [ht_mem.1]
      have hd : HasDerivAt (fun s : ℝ => edgeMV s - κ * s) (edgeX0Deriv t / edgeX0 t - κ) t :=
        (hasDerivAt_edgeMV ht_nn).fun_sub (((hasDerivAt_id t).const_mul κ).congr_deriv (mul_one κ))
      rw [hd.deriv]
      have hnum : cd1 * min (τ / 2) 1 ≤ edgeX0Deriv t := by
        have hm : min (τ / 2) 1 ≤ min t 1 := min_le_min ht.1.le le_rfl
        calc cd1 * min (τ / 2) 1 ≤ cd1 * min t 1 := by gcongr
          _ ≤ edgeX0Deriv t := (hxd_as ht_nn).1
      have hden : edgeX0 t ≤ cx2 * (1 + τ) := by
        calc edgeX0 t ≤ cx2 * (1 + t) := (hx_as ht_nn).2
          _ ≤ cx2 * (1 + τ) := by gcongr; exact ht.2.le
      have hdiv : κ ≤ edgeX0Deriv t / edgeX0 t :=
        div_le_div₀ (edgeX0Deriv_nonneg ht_nn) hnum (edgeX0_pos ht_nn) hden
      linarith
  have hdiff := hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have hval : κ * (τ / 2) ≤ edgeMV τ - edgeMV (τ / 2) := by linarith
  refine le_trans ?_ hval
  by_cases hτ1 : τ ≤ 1
  · have hm : min (τ / 2) 1 = τ / 2 := min_eq_left (by linarith)
    have hm2 : min (τ ^ 2) 1 = τ ^ 2 := min_eq_left (by nlinarith)
    rw [hm2]
    have h1τ : 1 + τ ≤ 2 := by linarith
    have hden : cx2 * (1 + τ) ≤ 2 * cx2 := by nlinarith
    calc c * τ ^ 2 = cd1 * (τ / 2) / (2 * cx2) * (τ / 2) := by dsimp [c]; ring
      _ ≤ cd1 * min (τ / 2) 1 / (cx2 * (1 + τ)) * (τ / 2) := by
          rw [hm]
          gcongr
  · push Not at hτ1
    have hτ2 : 1 / 2 ≤ min (τ / 2) 1 := by apply le_min <;> linarith
    have hm2 : min (τ ^ 2) 1 = 1 := min_eq_right (by nlinarith)
    rw [hm2, mul_one]
    have h1τ : 1 + τ ≤ 2 * τ := by linarith
    have hden : cx2 * (1 + τ) ≤ 2 * cx2 * τ := by nlinarith
    calc c = (cd1 * (1 / 2) / (2 * cx2 * τ)) * (τ / 2) := by
          dsimp [c]; field_simp [hτ.ne']; norm_num
      _ ≤ cd1 * min (τ / 2) 1 / (cx2 * (1 + τ)) * (τ / 2) := by
          gcongr

lemma edgeMV_deriv_div_edgeNuDeriv_ge :
    ∃ c : ℝ, 0 < c ∧
      ∀ {τ : ℝ}, 0 < τ → c * (τ / (1 + τ ^ 3)) ≤ (edgeX0Deriv τ / edgeX0 τ) / edgeNuDeriv τ := by
  obtain ⟨_, cx2, _, hcx2, hx_as⟩ := edgeX0_asymp
  obtain ⟨cd1, _, hcd1, _, hxd_as⟩ := edgeX0Deriv_asymp
  obtain ⟨cnu1, cnu2, hcnu1, hcnu2, hnu_as⟩ := edgeNuDeriv_asymp
  let c : ℝ := cd1 / (4 * cx2 * cnu2)
  refine ⟨c, by positivity, fun {τ} hτ => ?_⟩
  have hnum : cd1 * min τ 1 ≤ edgeX0Deriv τ := (hxd_as hτ.le).1
  have hden1 : edgeX0 τ ≤ cx2 * (1 + τ) := (hx_as hτ.le).2
  have hden2 : edgeNuDeriv τ ≤ cnu2 * (1 + τ) := (hnu_as hτ.le).2
  have hx_pos := edgeX0_pos hτ.le
  have hnu_pos : 0 < edgeNuDeriv τ := by
    have := (hnu_as hτ.le).1
    have : 0 < cnu1 * (1 + τ) := by positivity
    linarith
  have hdiv : cd1 * min τ 1 / (cx2 * cnu2 * (1 + τ) ^ 2) ≤
      (edgeX0Deriv τ / edgeX0 τ) / edgeNuDeriv τ := by
    rw [div_div]
    refine div_le_div₀ (edgeX0Deriv_nonneg hτ.le) hnum (mul_pos hx_pos hnu_pos) ?_
    calc edgeX0 τ * edgeNuDeriv τ ≤ (cx2 * (1 + τ)) * (cnu2 * (1 + τ)) :=
          mul_le_mul hden1 hden2 hnu_pos.le (by positivity)
      _ = cx2 * cnu2 * (1 + τ) ^ 2 := by ring
  refine le_trans ?_ hdiv
  by_cases hτ1 : τ ≤ 1
  · rw [min_eq_left hτ1]
    have h1τ : (1 + τ) ^ 2 ≤ 4 := by nlinarith
    have hden_pos : 0 < 1 + τ ^ 3 := by positivity
    have h1_le : 1 ≤ 1 + τ ^ 3 := by linarith [pow_pos hτ 3]
    calc c * (τ / (1 + τ ^ 3)) ≤ c * (τ / 1) := by gcongr
      _ = cd1 * τ / (cx2 * cnu2 * 4) := by dsimp [c]; ring
      _ ≤ cd1 * τ / (cx2 * cnu2 * (1 + τ) ^ 2) := by
          gcongr
  · push Not at hτ1
    rw [min_eq_right hτ1.le, mul_one]
    have hτ2 : τ ≤ τ ^ 3 := by nlinarith [sq_nonneg (τ - 1)]
    have hτ3 : τ ^ 2 ≤ τ ^ 3 := by nlinarith [sq_nonneg τ]
    have h_cmp : τ * (1 + τ) ^ 2 ≤ 4 * (1 + τ ^ 3) := by
      calc τ * (1 + τ) ^ 2 = τ + 2 * τ ^ 2 + τ ^ 3 := by ring
        _ ≤ τ ^ 3 + 2 * τ ^ 3 + τ ^ 3 := by linarith
        _ ≤ 4 * (1 + τ ^ 3) := by linarith
    calc c * (τ / (1 + τ ^ 3))
        = (cd1 / (cx2 * cnu2)) * (τ / (4 * (1 + τ ^ 3))) := by dsimp [c]; field_simp [hcx2.ne', hcnu2.ne']
      _ ≤ (cd1 / (cx2 * cnu2)) * (1 / (1 + τ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos (by linarith))]
          linarith
      _ = cd1 / (cx2 * cnu2 * (1 + τ) ^ 2) := by field_simp [hcx2.ne', hcnu2.ne']

/-- **Lemma J4.0 (`vlo:J40`, `lower_o1_two_edge.tex`, lines 502–512)**:
summary of the exact left-edge derivatives, asymptotics, monotonicity of `ν`, and `m_V`
dispersion bounds. -/
theorem lemma_J4_0 :
    (∀ τ : ℝ, 0 ≤ τ → HasDerivAt edgeX0 ((1 / 2 : ℝ) * √(1 - 1 / Real.cosh (Real.pi * τ))) τ) ∧
    (∀ τ : ℝ, HasDerivAt edgeY0 ((1 / 2 : ℝ) * √(1 + 1 / Real.cosh (Real.pi * τ))) τ) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ τ : ℝ, 0 ≤ τ → c₁ * (1 + τ) ≤ edgeX0 τ ∧ edgeX0 τ ≤ c₂ * (1 + τ)) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ τ : ℝ, 0 ≤ τ → c₁ * min τ 1 ≤ edgeX0Deriv τ ∧ edgeX0Deriv τ ≤ c₂ * min τ 1) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ τ : ℝ, 0 ≤ τ → c₁ * (1 + τ) ≤ edgeNuDeriv τ ∧ edgeNuDeriv τ ≤ c₂ * (1 + τ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 ≤ τ → |edgeNuDeriv2 τ| ≤ C) ∧
    (StrictMonoOn edgeNu (Ici 0) ∧ edgeNu 0 = 0 ∧ Tendsto edgeNu atTop atTop) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ, 0 < τ → c * min (τ ^ 2) 1 ≤ edgeMV τ - edgeMV (τ / 2)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ, 0 < τ → c * (τ / (1 + τ ^ 3)) ≤ (edgeX0Deriv τ / edgeX0 τ) / edgeNuDeriv τ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨edgeNu_strictMonoOn, edgeNu_zero, tendsto_edgeNu_atTop⟩, ?_, ?_⟩
  · intro τ hτ
    rw [← edgeX0Deriv_eq_of_nonneg hτ]
    exact hasDerivAt_edgeX0 τ
  · intro τ
    rw [← edgeY0Deriv_eq τ]
    exact hasDerivAt_edgeY0 τ
  · obtain ⟨c₁, c₂, h1, h2, h⟩ := edgeX0_asymp
    exact ⟨c₁, c₂, h1, h2, fun τ hτ => h hτ⟩
  · obtain ⟨c₁, c₂, h1, h2, h⟩ := edgeX0Deriv_asymp
    exact ⟨c₁, c₂, h1, h2, fun τ hτ => h hτ⟩
  · obtain ⟨c₁, c₂, h1, h2, h⟩ := edgeNuDeriv_asymp
    exact ⟨c₁, c₂, h1, h2, fun τ hτ => h hτ⟩
  · obtain ⟨C, hC, h⟩ := edgeNuDeriv2_bounded
    exact ⟨C, hC, fun τ hτ => h hτ⟩
  · obtain ⟨c, hc, h⟩ := edgeMV_diff_ge
    exact ⟨c, hc, fun τ hτ => h hτ⟩
  · obtain ⟨c, hc, h⟩ := edgeMV_deriv_div_edgeNuDeriv_ge
    exact ⟨c, hc, fun τ hτ => h hτ⟩

/-- info: 'FormalResearch.ModularBootstrap.Chart.lemma_J4_0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Chart.lemma_J4_0

end FormalResearch.ModularBootstrap.Chart
