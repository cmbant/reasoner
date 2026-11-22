/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.Wronskian

public import DLMF.Hypergeometric.Basic.GaussSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# The Gauss differential equation and its standard solutions (DLMF §§15.5(i), 15.10(i))

Termwise differentiation of the series gives `d/dz ₂F₁(a,b;c;z) = (ab/c) ₂F₁(a+1,b+1;c+1;z)`,
and `₂F₁` satisfies the hypergeometric equation
`z(1-z)w'' + (c-(a+b+1)z)w' - ab w = 0`. The standard local solutions at `0`, `1` and `∞` solve
the same equation, with the Wronskians given by DLMF.

## Main definitions

* `gaussOperator`: the Gauss differential operator, DLMF 15.10.1, without division at its
  singular points.
* `ODE.wronskian`: the Wronskian, in the order used by DLMF.
* `zeroSecond`, `oneFirst`, `oneSecond`, `infinityFirst`: the standard local solutions,
  DLMF 15.10.2, 15.10.4, 15.10.6 (the first solution at zero is Mathlib's
  `ordinaryHypergeometric`).

## Main results

* `ordinaryHypergeometric_symm`: `₂F₁(a,b;c;z)` is symmetric in `a` and `b`.
* `hasDerivAt_ordinaryHypergeometric`, `deriv_ordinaryHypergeometric`: DLMF 15.5.1.
* `ordinaryHypergeometric_ode`, `gaussOperator_ordinaryHypergeometric`: the hypergeometric
  equation, DLMF 15.10.1.
* `regularizedGaussHypergeometricFun_ode`: the hypergeometric equation for the regularized function
  `𝐅`, for all parameters.
* `zero_second_ode`, `one_first_ode`, `one_second_ode`, `infinity_first_ode`: the local
  solutions solve the Gauss equation.
* `zero_wronskian`, `one_wronskian`, `infinity_wronskian`: Wronskians, DLMF 15.10.3, 15.10.5,
  15.10.7.
* `analyticAt_oneFirst`, `analyticAt_oneSecond`: analyticity of the solutions at `1`.
* `gaussOperator_comp_one_sub`, `gaussOperator_sub_smul`: the operator under `z ↦ 1 - z`, and
  its linearity.

## Implementation notes

The logarithmic solutions 15.10.8–15.10.10, the uniqueness of solutions and the connection
formulas are in `DLMF.Hypergeometric.Solutions`; higher derivatives and the contiguous
relations are in `DLMF.Hypergeometric.Derivatives` and `DLMF.Hypergeometric.Contiguous`.
-/

public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- `₂F₁(a, b; c; z)` is symmetric in the numerator parameters `a` and `b`. -/
theorem ordinaryHypergeometric_symm (a b c : ℂ) : (₂F₁ a b c : ℂ → ℂ) = ₂F₁ b a c := by
  funext z
  unfold ordinaryHypergeometric
  rw [ordinaryHypergeometricSeries_symm]

/-- The coefficient identity underlying termwise differentiation. No nonvanishing
condition on the numerator parameters is needed. -/
theorem gaussHypergeometricCoeff_shift {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n + 1 : ℂ) * gaussHypergeometricCoeff a b c (n + 1) =
      a * b / c * gaussHypergeometricCoeff (a + 1) (b + 1) (c + 1) n := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hcp : pochhammer (c + 1) n ≠ 0 :=
    pochhammer_ne_zero_of_not_neg_nat (by simpa using not_neg_nat_add_nat hc 1) n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [gaussHypergeometricCoeff, pochhammer_succ_left, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field [hc0, hcp, hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- The coefficient recurrence underlying the Gauss differential equation. -/
theorem gaussHypergeometricCoeff_recurrence {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n + 1 : ℂ) * (c + n) * gaussHypergeometricCoeff a b c (n + 1) =
      (a + n) * (b + n) * gaussHypergeometricCoeff a b c n := by
  have hcp := pochhammer_ne_zero_of_not_neg_nat hc n
  have hcn : c + (n : ℂ) ≠ 0 := by
    simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hc n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [gaussHypergeometricCoeff, pochhammer_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field [hcp, hcn, hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- Termwise derivative of the hypergeometric series, for `|z| < 1`. -/
@[dlmf 15.5.E1]
theorem hasDerivAt_ordinaryHypergeometric {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    HasDerivAt (₂F₁ a b c) (a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) z) z := by
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hf := hasFPowerSeriesOnBall_ordinaryHypergeometric a b c
  have hd := hf.deriv_ofScalars.hasSum_mul_pow hz'
  have hs := ((hasFPowerSeriesOnBall_ordinaryHypergeometric
    (a + 1) (b + 1) (c + 1)).hasSum_mul_pow hz').mul_left (a * b / c)
  have heq : (fun n : ℕ => (n + 1 : ℂ) * gaussHypergeometricCoeff a b c (n + 1) * z ^ n) =
      (fun n : ℕ => a * b / c * (gaussHypergeometricCoeff (a + 1) (b + 1) (c + 1) n * z ^ n)) := by
    funext n
    rw [gaussHypergeometricCoeff_shift hc]
    ring
  rw [heq] at hd
  rw [← hd.unique hs]
  exact (hf.analyticAt_of_mem hz').differentiableAt.hasDerivAt

/-- Identity under the stated parameter and domain assumptions: `deriv (₂F₁ a b c) z = a * b / c *
₂F₁ (a + 1) (b + 1) (c + 1) z`. -/
@[dlmf 15.5.E1]
theorem deriv_ordinaryHypergeometric {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    deriv (₂F₁ a b c) z = a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) z :=
  (hasDerivAt_ordinaryHypergeometric hc hz).deriv

/-- The Gaussian hypergeometric equation, AAR §2.3. -/
@[dlmf 15.10.E1]
theorem ordinaryHypergeometric_ode {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    z * (1 - z) * iteratedDeriv 2 (₂F₁ a b c) z +
        (c - (a + b + 1) * z) * deriv (₂F₁ a b c) z -
        a * b * ₂F₁ a b c z = 0 := by
  have h := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).ode_of_recurrence
    (A := 1) (B := a + b + 1) (C := a * b) (D := c) (fun n => ?_)
    (mem_eball_one_of_norm_lt_one hz)
  · simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h
  · rw [gaussHypergeometricCoeff_recurrence hc]
    ring

/-- The Gauss differential operator, without division at its singular points. -/
@[expose,
  dlmf 15.10.E1]
def gaussOperator (a b c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (1 - z) * iteratedDeriv 2 f z + (c - (a + b + 1) * z) * deriv f z - a * b * f z

/-- The common scalar Wronskian in the DLMF normalization. -/
@[deprecated ODE.wronskian +typeChanged (since := "2026-11-15")]
abbrev solutionWronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ := ODE.wronskian f g z


/-- The second solution at zero. The first is Mathlib's `ordinaryHypergeometric`. -/
@[expose,
  dlmf 15.10.E2]
def zeroSecond (a b c z : ℂ) : ℂ := z ^ (1 - c) * ₂F₁ (a - c + 1) (b - c + 1) (2 - c) z

/-- The first standard Gauss hypergeometric solution about one, given by the series in `1-z` with
denominator parameter `a+b-c+1`. -/
@[expose,
  dlmf 15.10.E4]
def oneFirst (a b c z : ℂ) : ℂ := ₂F₁ a b (a + b - c + 1) (1 - z)

/-- The second standard Gauss solution about one, with principal power `(1-z)^(c-a-b)` multiplying
the transformed series. -/
@[expose,
  dlmf 15.10.E4]
def oneSecond (a b c z : ℂ) : ℂ :=
  (1 - z) ^ (c - a - b) * ₂F₁ (c - a) (c - b) (c - a - b + 1) (1 - z)

/-- Interchanging `a,b` gives the second solution at infinity. -/
@[expose,
  dlmf 15.10.E6]
def infinityFirst (a b c z : ℂ) : ℂ := z ^ (-a) * ₂F₁ a (a - c + 1) (a - b + 1) (1 / z)

/-- The first local solution at `1` is analytic on the disk `‖1 - z‖ < 1`. -/
theorem analyticAt_oneFirst {a b c z : ℂ} (hz : ‖1 - z‖ < 1) : AnalyticAt ℂ (oneFirst a b c) z :=
  (analyticAt_ordinaryHypergeometric hz).comp (analyticAt_const.sub analyticAt_id)

/-- The second local solution at `1` is analytic on the disk `‖1 - z‖ < 1` inside the slit-plane
  condition. -/
theorem analyticAt_oneSecond {a b c z : ℂ} (hz : ‖1 - z‖ < 1) (hs : 1 - z ∈ slitPlane) :
    AnalyticAt ℂ (oneSecond a b c) z :=
  ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hs).mul
    ((analyticAt_ordinaryHypergeometric hz).comp (analyticAt_const.sub analyticAt_id))

/-- The Gauss operator is linear on functions analytic near the point. -/
theorem gaussOperator_sub_smul {a b c : ℂ} {f₁ f₂ f₃ : ℂ → ℂ} {α β z : ℂ}
    (h₁ : AnalyticAt ℂ f₁ z) (h₂ : AnalyticAt ℂ f₂ z) (h₃ : AnalyticAt ℂ f₃ z) :
    gaussOperator a b c (fun w => f₁ w - α * f₂ w - β * f₃ w) z =
      gaussOperator a b c f₁ z - α * gaussOperator a b c f₂ z -
        β * gaussOperator a b c f₃ z := by
  have hd : deriv (fun w => f₁ w - α * f₂ w - β * f₃ w) =ᶠ[𝓝 z]
      fun w => deriv f₁ w - α * deriv f₂ w - β * deriv f₃ w := by
    filter_upwards [h₁.eventually_analyticAt, h₂.eventually_analyticAt,
      h₃.eventually_analyticAt] with w hw₁ hw₂ hw₃
    exact ((hw₁.differentiableAt.hasDerivAt.sub
      (hw₂.differentiableAt.hasDerivAt.const_mul α)).sub
      (hw₃.differentiableAt.hasDerivAt.const_mul β)).deriv
  have hdd : deriv (deriv (fun w => f₁ w - α * f₂ w - β * f₃ w)) z =
      deriv (deriv f₁) z - α * deriv (deriv f₂) z - β * deriv (deriv f₃) z := by
    rw [hd.deriv_eq]
    exact ((h₁.deriv.differentiableAt.hasDerivAt.sub
      (h₂.deriv.differentiableAt.hasDerivAt.const_mul α)).sub
      (h₃.deriv.differentiableAt.hasDerivAt.const_mul β)).deriv
  simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hdd, hd.eq_of_nhds]
  ring

/-- Second derivative of `w ↦ w^s G(w)` for `G` analytic near a point of the slit plane. -/
theorem iteratedDeriv_two_cpow_mul {G : ℂ → ℂ} {s z : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hzU : z ∈ U) (hG : AnalyticOnNhd ℂ G U) (hUs : U ⊆ slitPlane) :
    deriv (fun w => w ^ s * G w) z = s * z ^ (s - 1) * G z + z ^ s * deriv G z ∧
    iteratedDeriv 2 (fun w => w ^ s * G w) z =
      s * (s - 1) * z ^ (s - 2) * G z + 2 * s * z ^ (s - 1) * deriv G z +
        z ^ s * iteratedDeriv 2 G z := by
  have hd : ∀ w ∈ U, HasDerivAt (fun w => w ^ s * G w)
      (s * w ^ (s - 1) * G w + w ^ s * deriv G w) w := by
    intro w hw
    have h1 := (hasDerivAt_id' w).cpow_const (c := s) (hUs hw)
    have h2 := (hG w hw).differentiableAt.hasDerivAt
    convert h1.mul h2 using 1
    ring
  refine ⟨(hd z hzU).deriv, ?_⟩
  have hev : deriv (fun w => w ^ s * G w) =ᶠ[𝓝 z]
      fun w => s * w ^ (s - 1) * G w + w ^ s * deriv G w :=
    Filter.eventually_of_mem (hU.mem_nhds hzU) fun w hw => (hd w hw).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, iteratedDeriv_succ, iteratedDeriv_one]
  have hz0 := hUs hzU
  have hG1 := (hG z hzU).differentiableAt.hasDerivAt
  have hG2 := (hG z hzU).deriv.differentiableAt.hasDerivAt
  have hp1 := (hasDerivAt_id' z).cpow_const (c := s - 1) hz0
  have hp0 := (hasDerivAt_id' z).cpow_const (c := s) hz0
  have := ((hp1.const_mul s).mul hG1).add (hp0.mul hG2)
  refine this.deriv.trans ?_
  rw [show s - 1 - 1 = s - 2 by ring]
  ring

/-- Identity under the stated parameter and domain assumptions: `gaussOperator a b c (zeroSecond a
b c) z = 0`. -/
@[dlmf 15.10.E2]
theorem zero_second_ode
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, 2 - c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator a b c (zeroSecond a b c) z = 0 := by
  set G : ℂ → ℂ := ₂F₁ (a - c + 1) (b - c + 1) (2 - c)
  have hU : IsOpen (Metric.ball (0 : ℂ) 1 ∩ slitPlane) := Metric.isOpen_ball.inter isOpen_slitPlane
  have hzU : z ∈ Metric.ball (0 : ℂ) 1 ∩ slitPlane := ⟨by simpa using hz, hs⟩
  have hG : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) 1 ∩ slitPlane) := fun w hw =>
    (hasFPowerSeriesOnBall_ordinaryHypergeometric _ _ _).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one (by simpa using hw.1))
  obtain ⟨h1, h2⟩ := iteratedDeriv_two_cpow_mul (s := 1 - c) hU hzU hG Set.inter_subset_right
  have hz0 : z ≠ 0 := slitPlane_ne_zero hs
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have hode := ordinaryHypergeometric_ode (a := a - c + 1) (b := b - c + 1) hc hz
  have he : zeroSecond a b c = fun w => w ^ (1 - c) * G w := by funext w; rfl
  have e1 : z ^ (1 - c - 1) = z ^ (1 - c) / z := by rw [cpow_sub _ _ hz0, cpow_one]
  have e2 : z ^ (1 - c - 2) = z ^ (1 - c) / z ^ 2 := by
    rw [cpow_sub _ _ hz0, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  rw [gaussOperator, he, h1, h2, e1, e2]
  set P := z ^ (1 - c)
  field_simp
  linear_combination (z * P) * hode

/-- The Gauss operator annihilates `₂F₁` on the whole unit disk, including the origin; the
coefficient recurrence also gives the equation at the regular point zero. -/
theorem gaussOperator_ordinaryHypergeometric {a b c w : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hw : ‖w‖ < 1) : gaussOperator a b c (₂F₁ a b c) w = 0 := by
  have h := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).ode_of_recurrence
    (A := 1) (B := a + b + 1) (C := a * b) (D := c) (fun n => ?_)
    (mem_eball_one_of_norm_lt_one hw)
  · simpa [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero] using h
  · rw [gaussHypergeometricCoeff_recurrence hc]
    ring

/-- Identity under the stated parameter and domain assumptions: `gaussOperator a b c (oneFirst a b
c) z = 0`. -/
@[dlmf 15.10.E4]
theorem one_first_ode {a b c z : ℂ} (hc : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ)) (hz : ‖1 - z‖ < 1) :
    gaussOperator a b c (oneFirst a b c) z = 0 := by
  have he : oneFirst a b c = (fun w => ₂F₁ a b (a + b - c + 1) (1 - w)) := by
    funext w
    rw [oneFirst]
  have hd : deriv (oneFirst a b c) z = -deriv (₂F₁ a b (a + b - c + 1)) (1 - z) := by
    have h := congrFun (iteratedDeriv_comp_const_sub (n := 1)
      (f := (₂F₁ a b (a + b - c + 1) : ℂ → ℂ)) (s := 1)) z
    rw [he]
    simpa [iteratedDeriv_one] using h
  have hdd : iteratedDeriv 2 (oneFirst a b c) z =
      iteratedDeriv 2 (₂F₁ a b (a + b - c + 1)) (1 - z) := by
    have h := congrFun (iteratedDeriv_comp_const_sub (n := 2)
      (f := (₂F₁ a b (a + b - c + 1) : ℂ → ℂ)) (s := 1)) z
    rw [he]
    simpa using h
  have h := gaussOperator_ordinaryHypergeometric (a := a) (b := b) hc hz
  rw [gaussOperator, hd, hdd, oneFirst]
  unfold gaussOperator at h
  linear_combination h

/-- The Gauss operator under the reflection `z ↦ 1 - z`. -/
theorem gaussOperator_comp_one_sub (a b c : ℂ) (g : ℂ → ℂ) (z : ℂ) :
    gaussOperator a b c (fun w => g (1 - w)) z = gaussOperator a b (a + b - c + 1) g (1 - z) := by
  have hd : deriv (fun w => g (1 - w)) z = -deriv g (1 - z) := by
    simpa [iteratedDeriv_one] using
      congrFun (iteratedDeriv_comp_const_sub (n := 1) (f := g) (s := 1)) z
  have hdd : iteratedDeriv 2 (fun w => g (1 - w)) z = iteratedDeriv 2 g (1 - z) := by
    simpa using congrFun (iteratedDeriv_comp_const_sub (n := 2) (f := g) (s := 1)) z
  rw [gaussOperator, gaussOperator, hd, hdd]
  ring

/-- Identity under the stated parameter and domain assumptions: `gaussOperator a b c (oneSecond a
b c) z = 0`. -/
@[dlmf 15.10.E4]
theorem one_second_ode
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ))
    (hz : ‖1 - z‖ < 1)
    (hs : 1 - z ∈ slitPlane) :
    gaussOperator a b c (oneSecond a b c) z = 0 := by
  have he : oneSecond a b c = fun w => zeroSecond a b (a + b - c + 1) (1 - w) := by
    funext w
    rw [oneSecond, zeroSecond, ordinaryHypergeometric_symm]
    congr 1 <;> ring_nf
  rw [he, gaussOperator_comp_one_sub]
  exact zero_second_ode (by simpa [show (2 : ℂ) - (a + b - c + 1) = c - a - b + 1 by ring]
    using hc) hz hs

/-- Derivatives of `w ↦ w^s H(1/w)`. -/
theorem iteratedDeriv_two_cpow_mul_recip {H : ℂ → ℂ} {s z : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hzU : z ∈ U) (hH : ∀ w ∈ U, AnalyticAt ℂ H w⁻¹) (hUs : U ⊆ slitPlane) :
    deriv (fun w => w ^ s * H w⁻¹) z =
      s * z ^ (s - 1) * H z⁻¹ - z ^ s * deriv H z⁻¹ / z ^ 2 ∧
    iteratedDeriv 2 (fun w => w ^ s * H w⁻¹) z =
      s * (s - 1) * z ^ (s - 1 - 1) * H z⁻¹ - s * z ^ (s - 1) * deriv H z⁻¹ / z ^ 2
        - (s * z ^ (s - 1) * deriv H z⁻¹ / z ^ 2
          - z ^ s * (2 * deriv H z⁻¹ / z ^ 3 + iteratedDeriv 2 H z⁻¹ / z ^ 4)) := by
  have hne : ∀ w ∈ U, w ≠ 0 := fun w hw => slitPlane_ne_zero (hUs hw)
  have hinv : ∀ w ∈ U, HasDerivAt (fun y : ℂ => y⁻¹) (-(w ^ 2)⁻¹) w := fun w hw =>
    hasDerivAt_inv (hne w hw)
  have hd : ∀ w ∈ U, HasDerivAt (fun w => w ^ s * H w⁻¹)
      (s * w ^ (s - 1) * H w⁻¹ - w ^ s * deriv H w⁻¹ / w ^ 2) w := by
    intro w hw
    have h1 := (hasDerivAt_id' w).cpow_const (c := s) (hUs hw)
    have h2 := (hH w hw).differentiableAt.hasDerivAt.comp w (hinv w hw)
    convert h1.mul h2 using 1
    · rfl
    · simp only [Function.comp_apply]
      field_simp [hne w hw]
      ring
  refine ⟨(hd z hzU).deriv, ?_⟩
  have hev : deriv (fun w => w ^ s * H w⁻¹) =ᶠ[𝓝 z]
      fun w => s * w ^ (s - 1) * H w⁻¹ - w ^ s * deriv H w⁻¹ / w ^ 2 :=
    Filter.eventually_of_mem (hU.mem_nhds hzU) fun w hw => (hd w hw).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, iteratedDeriv_succ, iteratedDeriv_one]
  have hz0 := hUs hzU
  have hz0' := hne z hzU
  have hH1 := (hH z hzU).differentiableAt.hasDerivAt.comp z (hinv z hzU)
  have hH2 := (hH z hzU).deriv.differentiableAt.hasDerivAt.comp z (hinv z hzU)
  have hp1 := (hasDerivAt_id' z).cpow_const (c := s - 1) hz0
  have hp0 := (hasDerivAt_id' z).cpow_const (c := s) hz0
  have hq := (hasDerivAt_id' z).pow 2
  have := ((hp1.const_mul s).mul hH1).sub ((hp0.mul hH2).div hq (pow_ne_zero 2 hz0'))
  refine this.deriv.trans ?_
  simp only [Function.comp_apply, Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `gaussOperator a b c
(infinityFirst a b c) z = 0`. -/
@[dlmf 15.10.E6]
theorem infinity_first_ode
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : 1 < ‖z‖)
    (hs : z ∈ slitPlane) :
    gaussOperator a b c (infinityFirst a b c) z = 0 := by
  set H : ℂ → ℂ := ₂F₁ a (a - c + 1) (a - b + 1)
  set U : Set ℂ := {w | 1 < ‖w‖} ∩ slitPlane
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter isOpen_slitPlane
  have hzU : z ∈ U := ⟨hz, hs⟩
  have hinvlt : ∀ w : ℂ, 1 < ‖w‖ → ‖w⁻¹‖ < 1 := fun w hw => by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hw
  have hH : ∀ w ∈ U, AnalyticAt ℂ H w⁻¹ := fun w hw =>
    (hasFPowerSeriesOnBall_ordinaryHypergeometric _ _ _).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one (hinvlt w hw.1))
  obtain ⟨h1, h2⟩ := iteratedDeriv_two_cpow_mul_recip (s := -a) hU hzU hH Set.inter_subset_right
  have hz0 : z ≠ 0 := slitPlane_ne_zero hs
  have hu := hinvlt z hz
  have hu0 : z⁻¹ ≠ 0 := inv_ne_zero hz0
  have hu1 : z⁻¹ ≠ 1 := by intro h; rw [h, norm_one] at hu; exact lt_irrefl _ hu
  have hode := ordinaryHypergeometric_ode (a := a) (b := a - c + 1) hc hu
  have he : infinityFirst a b c = fun w => w ^ (-a) * H w⁻¹ := by
    funext w; rw [infinityFirst, one_div]
  have e1 : z ^ (-a - 1) = z ^ (-a) / z := by rw [cpow_sub _ _ hz0, cpow_one]
  have e2 : z ^ (-a - 1 - 1) = z ^ (-a) / z ^ 2 := by
    rw [sub_sub, cpow_sub _ _ hz0, show (1 + 1 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  rw [gaussOperator, he, h1, h2, e1, e2]
  beta_reduce
  set P := z ^ (-a)
  set u := z⁻¹ with hu_def
  have hz' : z = u⁻¹ := (inv_inv z).symm
  rw [hz']
  field_simp
  linear_combination (-(P * u)) * hode

/-- Identity under the stated parameter and domain assumptions: `ODE.wronskian (₂F₁ a b c)
(zeroSecond a b c) z = (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1)`. -/
@[dlmf 15.10.E3]
theorem zero_wronskian
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hd : ∀ k : ℕ, 2 - c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    ODE.wronskian (₂F₁ a b c) (zeroSecond a b c) z =
      (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  set F : ℂ → ℂ := ₂F₁ a b c with hF
  set G : ℂ → ℂ := ₂F₁ (a - c + 1) (b - c + 1) (2 - c) with hG
  set k := a + b + 1 - c with hk
  set B : ℂ → ℂ := fun w => (1 - c) * F w * G w + w * (F w * deriv G w - deriv F w * G w) with hB
  have hFa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ F w := fun w hw =>
    (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one hw)
  have hGa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ G w := fun w hw =>
    (hasFPowerSeriesOnBall_ordinaryHypergeometric _ _ _).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one hw)
  have hBd : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt B ((1 - c) * (deriv F w * G w + F w * deriv G w) +
      (F w * deriv G w - deriv F w * G w) +
      w * (F w * iteratedDeriv 2 G w - iteratedDeriv 2 F w * G w)) w := by
    intro w hw
    have hF1 := (hFa w hw).differentiableAt.hasDerivAt
    have hG1 := (hGa w hw).differentiableAt.hasDerivAt
    have hF2 := (hFa w hw).deriv.differentiableAt.hasDerivAt
    have hG2 := (hGa w hw).deriv.differentiableAt.hasDerivAt
    have h := ((hF1.const_mul (1 - c)).mul hG1).add ((hasDerivAt_id w).mul
      ((hF1.mul hG2).sub (hF2.mul hG1)))
    refine h.congr_deriv ?_
    simp only [id, iteratedDeriv_succ, iteratedDeriv_zero, Pi.mul_apply, Pi.sub_apply]
    ring
  have hrel : ∀ w : ℂ, ‖w‖ < 1 → (1 - w) * ((1 - c) * (deriv F w * G w + F w * deriv G w) +
      (F w * deriv G w - deriv F w * G w) +
      w * (F w * iteratedDeriv 2 G w - iteratedDeriv 2 F w * G w)) = k * B w := by
    intro w hw
    have hoF := gaussOperator_ordinaryHypergeometric (a := a) (b := b) hc hw
    have hoG := gaussOperator_ordinaryHypergeometric (a := a - c + 1) (b := b - c + 1) hd hw
    simp only [gaussOperator] at hoF hoG
    simp only [hB, hk]
    linear_combination F w * hoG - G w * hoF
  set H : ℂ → ℂ := fun w => B w * (1 - w) ^ k with hH
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖w‖ < 1 := fun w hw => by simpa using hw
  have hHd : ∀ w ∈ Metric.ball (0 : ℂ) 1, HasDerivAt H 0 w := by
    intro w hw
    have hw1 := hball w hw
    have h1w : 1 - w ≠ 0 := by
      intro h
      have : w = 1 := by linear_combination -h
      rw [this] at hw1
      simp at hw1
    have hslit : 1 - w ∈ slitPlane := by
      refine mem_slitPlane_iff.mpr (Or.inl ?_)
      have := (re_le_norm w).trans_lt hw1
      simp only [sub_re, one_re]; linarith
    have hp := ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).cpow_const (c := k) hslit
    refine ((hBd w hw1).mul hp).congr_deriv ?_
    simp only [Pi.sub_apply, id]
    rw [show (1 - w) ^ (k - 1) = (1 - w) ^ k / (1 - w) by rw [cpow_sub _ _ h1w, cpow_one]]
    have := hrel w hw1
    field_simp
    linear_combination (1 - w) ^ k * this
  have hHc := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    (fun w hw => (hHd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hHd w hw).deriv) (x := z) (y := 0) (by simpa using hz) (by simp)
  have hH0 : H 0 = 1 - c := by
    simp [hH, hB, hF, hG, ordinaryHypergeometric_zero]
  rw [hH0] at hHc
  -- The Wronskian in terms of `B`.
  have hz0 : z ≠ 0 := slitPlane_ne_zero hs
  have h1z : 1 - z ≠ 0 := by
    intro h; have : z = 1 := by linear_combination -h
    rw [this] at hz; simp at hz
  have hS : HasDerivAt (zeroSecond a b c)
      ((1 - c) * z ^ (1 - c - 1) * 1 * G z + z ^ (1 - c) * deriv G z) z :=
    ((hasDerivAt_id z).cpow_const (c := 1 - c) hs).mul (hGa z hz).differentiableAt.hasDerivAt
  have hzc : z ^ (1 - c) = z * z ^ (-c) := by
    rw [show 1 - c = 1 + -c by ring, cpow_add _ _ hz0, cpow_one]
  have hzc' : z ^ (1 - c - 1) = z ^ (-c) := by congr 1; ring
  have hkne : (1 - z) ^ k ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl h1z)
  have hk' : (1 - z) ^ (c - a - b - 1) = ((1 - z) ^ k)⁻¹ := by
    rw [show c - a - b - 1 = -k by rw [hk]; ring, cpow_neg]
  have hBz : B z = (1 - c) * ((1 - z) ^ k)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hkne]; exact hHc
  unfold ODE.wronskian
  rw [hS.deriv]
  calc F z * ((1 - c) * z ^ (1 - c - 1) * 1 * G z + z ^ (1 - c) * deriv G z) -
        zeroSecond a b c z * deriv F z = z ^ (-c) * B z := by
        rw [show zeroSecond a b c z = z ^ (1 - c) * G z from rfl, hzc, hzc']
        simp only [hB]
        ring
    _ = (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
        rw [hBz, hk']
        ring

/-- Identity under the stated parameter and domain assumptions: `ODE.wronskian (oneFirst a b
c) (oneSecond a b c) z = (a + b - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1)`. -/
@[dlmf 15.10.E5]
theorem one_wronskian
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ))
    (hd : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ))
    (hz : ‖1 - z‖ < 1)
    (hs : 1 - z ∈ slitPlane) :
    ODE.wronskian (oneFirst a b c) (oneSecond a b c) z =
      (a + b - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  set C := a + b - c + 1 with hCdef
  have hd' : ∀ k : ℕ, 2 - C ≠ -(k : ℂ) := by
    rw [show 2 - C = c - a - b + 1 by rw [hCdef]; ring]; exact hd
  have h0 := zero_wronskian (a := a) (b := b) (c := C) (z := 1 - z) hc hd' hz hs
  have hF : DifferentiableAt ℂ (₂F₁ a b C) (1 - z) :=
    ((hasFPowerSeriesOnBall_ordinaryHypergeometric a b C).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one hz)).differentiableAt
  have hS : DifferentiableAt ℂ (zeroSecond a b C) (1 - z) :=
    ((hasDerivAt_id (1 - z)).cpow_const (c := 1 - C) hs).differentiableAt.mul
      ((hasFPowerSeriesOnBall_ordinaryHypergeometric _ _ _).analyticAt_of_mem
        (mem_eball_one_of_norm_lt_one hz)).differentiableAt
  have hr : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub 1
  have he1 : oneFirst a b c = fun w => ₂F₁ a b C (1 - w) := rfl
  have he2 : oneSecond a b c = fun w => zeroSecond a b C (1 - w) := by
    funext w
    rw [oneSecond, zeroSecond, ordinaryHypergeometric_symm]
    simp only [hCdef]
    congr 1 <;> ring_nf
  have hd1 : deriv (oneFirst a b c) z = -deriv (₂F₁ a b C) (1 - z) := by
    have h' : HasDerivAt (fun w => ₂F₁ a b C (1 - w)) _ z := hF.hasDerivAt.comp z hr
    rw [he1, h'.deriv]; ring
  have hd2 : deriv (oneSecond a b c) z = -deriv (zeroSecond a b C) (1 - z) := by
    have h' : HasDerivAt (fun w => zeroSecond a b C (1 - w)) _ z := hS.hasDerivAt.comp z hr
    rw [he2, h'.deriv]; ring
  unfold ODE.wronskian at h0 ⊢
  rw [hd1, hd2, he1, he2]
  simp only
  rw [sub_sub_cancel, show 1 - C = c - a - b by rw [hCdef]; ring,
    show C - a - b - 1 = -c by rw [hCdef]; ring, show -C = c - a - b - 1 by rw [hCdef]; ring]
    at h0
  linear_combination -h0

/-- Wronskian of a common factor times two functions. -/
theorem solutionWronskian_mul_left {p f g : ℂ → ℂ} {z : ℂ} (hp : DifferentiableAt ℂ p z)
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    ODE.wronskian (fun w => p w * f w) (fun w => p w * g w) z =
      p z ^ 2 * ODE.wronskian f g z := by
  unfold ODE.wronskian
  have h1 : HasDerivAt (fun w => p w * f w) _ z := hp.hasDerivAt.mul hf.hasDerivAt
  have h2 : HasDerivAt (fun w => p w * g w) _ z := hp.hasDerivAt.mul hg.hasDerivAt
  rw [h1.deriv, h2.deriv]
  ring

/-- Wronskian after the inversion `w ↦ w⁻¹`. -/
theorem solutionWronskian_comp_recip {f g : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : DifferentiableAt ℂ f z⁻¹) (hg : DifferentiableAt ℂ g z⁻¹) :
    ODE.wronskian (fun w => f w⁻¹) (fun w => g w⁻¹) z =
      -(z ^ 2)⁻¹ * ODE.wronskian f g z⁻¹ := by
  unfold ODE.wronskian
  have hi := hasDerivAt_inv hz
  have h1 : HasDerivAt (fun w => f w⁻¹) _ z := hf.hasDerivAt.comp z hi
  have h2 : HasDerivAt (fun w => g w⁻¹) _ z := hg.hasDerivAt.comp z hi
  rw [h1.deriv, h2.deriv]
  ring

/-- Identity under the stated parameter and domain assumptions: `ODE.wronskian (infinityFirst
a b c) (infinityFirst b a c) z = (a - b) * z ^ (-c) * (z - 1) ^ (c - a - b - 1)`. -/
@[dlmf 15.10.E7]
theorem infinity_wronskian
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hd : ∀ k : ℕ, b - a + 1 ≠ -(k : ℂ))
    (hz : 1 < z.re) :
    ODE.wronskian (infinityFirst a b c) (infinityFirst b a c) z =
      (a - b) * z ^ (-c) * (z - 1) ^ (c - a - b - 1) := by
  set B := a - c + 1
  set C := a - b + 1 with hCdef
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz; linarith
  have hre : ∀ w : ℂ, 0 < w.re → w⁻¹ ∈ slitPlane ∧ ‖w⁻¹‖ ≤ 1 / w.re := by
    intro w hw
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
    refine ⟨mem_slitPlane_iff.mpr (Or.inl ?_), ?_⟩
    · rw [inv_re]; exact div_pos hw (normSq_pos.mpr hw0)
    · rw [norm_inv]
      exact inv_anti₀ hw (re_le_norm w) |>.trans_eq (one_div _).symm
  have hu := hre z (by linarith)
  have hun : ‖z⁻¹‖ < 1 := hu.2.trans_lt (by rw [div_lt_one (by linarith)]; exact hz)
  have hd' : ∀ k : ℕ, 2 - C ≠ -(k : ℂ) := by
    rw [show 2 - C = b - a + 1 by rw [hCdef]; ring]; exact hd
  have h0 := zero_wronskian (a := a) (b := B) (c := C) hc hd' hun hu.1
  -- local rewriting of the two solutions
  have hU : ∀ᶠ w in 𝓝 z, 0 < w.re := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
    (show z ∈ re ⁻¹' Set.Ioi 0 by simp only [Set.mem_preimage, Set.mem_Ioi]; linarith)
  have e1 : infinityFirst a b c = fun w => w ^ (-a) * ₂F₁ a B C w⁻¹ := by
    funext w; rw [infinityFirst, one_div]
  have e2 : infinityFirst b a c =ᶠ[𝓝 z] fun w => w ^ (-a) * zeroSecond a B C w⁻¹ := by
    filter_upwards [hU] with w hw
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
    have harg : w.arg ≠ π := (mem_slitPlane_iff_arg.mp (mem_slitPlane_iff.mpr (Or.inl hw))).1
    simp only [infinityFirst, zeroSecond, one_div]
    rw [inv_cpow _ _ harg, ← cpow_neg, ← mul_assoc, ← cpow_add _ _ hw0]
    congr 2 <;> simp only [B, C] <;> ring
  have hW : ODE.wronskian (infinityFirst a b c) (infinityFirst b a c) z =
      ODE.wronskian (fun w => w ^ (-a) * ₂F₁ a B C w⁻¹)
        (fun w => w ^ (-a) * zeroSecond a B C w⁻¹) z := by
    unfold ODE.wronskian
    rw [e1, e2.deriv_eq, e2.eq_of_nhds]
  have hzs : z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by linarith))
  have hFa : DifferentiableAt ℂ (₂F₁ a B C) z⁻¹ :=
    ((hasFPowerSeriesOnBall_ordinaryHypergeometric a B C).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one hun)).differentiableAt
  have hSa : DifferentiableAt ℂ (zeroSecond a B C) z⁻¹ :=
    ((hasDerivAt_id z⁻¹).cpow_const (c := 1 - C) hu.1).differentiableAt.mul
      ((hasFPowerSeriesOnBall_ordinaryHypergeometric _ _ _).analyticAt_of_mem
        (mem_eball_one_of_norm_lt_one hun)).differentiableAt
  have hp : DifferentiableAt ℂ (fun w : ℂ => w ^ (-a)) z :=
    ((hasDerivAt_id z).cpow_const (c := -a) hzs).differentiableAt
  have hFi : DifferentiableAt ℂ (fun w => ₂F₁ a B C w⁻¹) z := hFa.comp z (differentiableAt_inv hz0)
  have hSi : DifferentiableAt ℂ (fun w => zeroSecond a B C w⁻¹) z :=
    hSa.comp z (differentiableAt_inv hz0)
  rw [hW, solutionWronskian_mul_left hp hFi hSi, solutionWronskian_comp_recip hz0 hFa hSa, h0]
  -- power bookkeeping
  have hz1 : z - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hz; simp at hz
  have hargz : z.arg ≠ π := (mem_slitPlane_iff_arg.mp hzs).1
  have habs : ∀ w : ℂ, 0 < w.re → |w.arg| < π / 2 := fun w hw =>
    abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have hzi : 0 < z⁻¹.re := by rw [inv_re]; exact div_pos (by linarith) (normSq_pos.mpr hz0)
  have hlog : log (1 - z⁻¹) = log (z - 1) + log z⁻¹ := by
    rw [show 1 - z⁻¹ = (z - 1) * z⁻¹ by field_simp]
    refine log_mul hz1 (inv_ne_zero hz0) ?_
    have h1 := habs (z - 1) (by simp; linarith)
    have h2 := habs z⁻¹ hzi
    rw [abs_lt] at h1 h2
    constructor <;> linarith [Real.pi_pos]
  set p := C - a - B - 1 with hpdef
  have hpow : (1 - z⁻¹) ^ p = (z - 1) ^ p * (z ^ p)⁻¹ := by
    have h1z : 1 - z⁻¹ ≠ 0 := by
      rw [show 1 - z⁻¹ = (z - 1) * z⁻¹ by field_simp]; exact mul_ne_zero hz1 (inv_ne_zero hz0)
    rw [cpow_def_of_ne_zero h1z, hlog, add_mul, exp_add, ← cpow_def_of_ne_zero hz1,
      ← cpow_def_of_ne_zero (inv_ne_zero hz0), inv_cpow _ _ hargz]
  have hC : z⁻¹ ^ (-C) = z ^ C := by rw [inv_cpow _ _ hargz, cpow_neg, inv_inv]
  have hp' : p = c - a - b - 1 := by rw [hpdef]; simp only [B, C]; ring
  have key : z ^ (-a) * z ^ (-a) * z ^ C = z ^ (-c) * z ^ p * z ^ (2 : ℂ) := by
    rw [← cpow_add _ _ hz0, ← cpow_add _ _ hz0, ← cpow_add _ _ hz0, ← cpow_add _ _ hz0]
    congr 1; rw [hp']; simp only [C]; ring
  have hz2 : z ^ (2 : ℂ) = z ^ 2 := by exact_mod_cast cpow_natCast z 2
  rw [hz2] at key
  rw [hpow, hC, ← hp']
  have hzp : z ^ p ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have h1C : 1 - C = -(a - b) := by simp only [C]; ring
  rw [h1C]
  field_simp
  linear_combination (a - b) * (z - 1) ^ p * key

/-- The hypergeometric equation (DLMF 15.10.1) for Olver's regularized function
`𝐅(a,b;c;z) = regularizedGaussHGFun a b c z` on the unit disk, for all parameters. -/
@[dlmf 15.10.E1]
theorem regularizedGaussHypergeometricFun_ode (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * (1 - z) * deriv (deriv (regularizedGaussHGFun a b c)) z +
        (c - (a + b + 1) * z) * deriv (regularizedGaussHGFun a b c) z -
        a * b * regularizedGaussHGFun a b c z = 0 := by
  have hpos : (0 : ENNReal) < (regularizedGaussHGFunSeries a b c).radius :=
    lt_of_lt_of_le (by norm_num) (radius_regularizedGaussHGFunSeries_ge_one a b c)
  have hp : HasFPowerSeriesOnBall (regularizedGaussHGFun a b c)
      (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff {a, b} {c})) 0 1 :=
    ((regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall hpos).mono
      (by norm_num) (radius_regularizedGaussHGFunSeries_ge_one a b c)
  have hcoeff : regularizedHGFunCoeff {a, b} {c} = (regularizedGaussHGFunSeries a b c).coeff := by
    rw [regularizedGaussHGFunSeries, regularizedHGFunSeries_coeff]
  have h := hp.ode_of_recurrence (A := 1) (B := a + b + 1) (C := a * b) (D := c)
    (fun n => ?_) (mem_eball_one_of_norm_lt_one hz)
  · simpa using h
  · rw [hcoeff, coeff_regularizedGaussHGFunSeries, coeff_regularizedGaussHGFunSeries,
      ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ]
    have hG : (c + n) * (Gamma (c + (n + 1)))⁻¹ = (Gamma (c + n))⁻¹ := by
      rcases eq_or_ne (c + n) 0 with h0 | h0
      · rw [h0, zero_mul, Complex.Gamma_zero, inv_zero]
      · rw [show c + ((n : ℂ) + 1) = (c + n) + 1 by ring,
          Complex.Gamma_add_one _ h0, mul_inv, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    push_cast
    simp only [div_eq_mul_inv, mul_inv]
    rw [← hG]
    field_simp
    ring

end DLMF.Hypergeometric
