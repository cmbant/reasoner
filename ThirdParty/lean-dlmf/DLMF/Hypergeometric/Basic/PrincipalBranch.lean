/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Basic
public import DLMF.Hypergeometric.Basic.GaussCoefficients
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Order

/-!
# Cut plane and Euler continuation of the Gauss function

## Main definitions

* `cutPlane`: the cut plane `ℂ ∖ [1, ∞)`, the natural domain of `₂F₁` in its argument.
* `eulerKernel`, `regularizedGaussHypergeometricIntegral`: Euler's integral 15.6.1 in the
  regularized normalization.
* `shiftB`, `shiftC`, `shiftMeasure`, `regularizedGaussHypergeometricByShifts`: the contiguous
  shifts into the Euler region and the recursion.
* `regularizedGaussHypergeometric`: the continuation of the regularized function `𝐅(a,b;c;z)` to the
  cut plane, for all parameters.

## Main results

* `isOpen_cutPlane`, `starConvex_zero_cutPlane`, `isPreconnected_cutPlane`: topology of the cut
  plane.
* `eqOn_cutPlane_of_eventuallyEq`, `eqOn_cutPlane_of_eqOn_disk`: the identity principle on the
  cut plane.
-/

public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open MeasureTheory intervalIntegral
open scoped ComplexOrder

namespace DLMF.Hypergeometric

/-- The cut plane `ℂ ∖ [1, ∞)`, the natural domain of `₂F₁` in its argument. -/
@[expose]
def cutPlane : Set ℂ := {z | 1 - z ∈ slitPlane}

/-- `z` lies in the cut plane `ℂ \ [1, ∞)` iff `1 - z` lies in the slit plane. -/
theorem mem_cutPlane {z : ℂ} : z ∈ cutPlane ↔ 1 - z ∈ slitPlane := Iff.rfl

/-- The cut plane `ℂ \ [1, ∞)` is open. -/
theorem isOpen_cutPlane : IsOpen cutPlane :=
  isOpen_slitPlane.preimage (continuous_const.sub continuous_id)

/-- `0` lies in the cut plane. -/
theorem zero_mem_cutPlane : (0 : ℂ) ∈ cutPlane := by
  show (1 : ℂ) - 0 ∈ slitPlane
  simp

/-- On the cut plane, `1 - z ≠ 0`. -/
theorem one_sub_ne_zero_of_mem_cutPlane {z : ℂ} (hz : z ∈ cutPlane) : 1 - z ≠ 0 :=
  slitPlane_ne_zero hz

/-- The open unit disk lies in the cut plane. -/
theorem mem_cutPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : z ∈ cutPlane := by
  show 1 - z ∈ slitPlane
  rw [mem_slitPlane_iff]
  left
  simp only [sub_re, one_re]
  linarith [re_le_norm z]

/-- The cut plane is star-convex about `0`. -/
theorem starConvex_zero_cutPlane : StarConvex ℝ 0 cutPlane := by
  intro y hy a b ha hb hab
  have h := starConvex_one_slitPlane (hy : 1 - y ∈ slitPlane) ha hb hab
  show 1 - (a • (0 : ℂ) + b • y) ∈ slitPlane
  convert h using 1
  simp only [smul_zero, zero_add, Complex.real_smul]
  have : (a : ℂ) + b = 1 := by exact_mod_cast hab
  linear_combination (-1 : ℂ) * this

/-- The cut plane is preconnected. -/
theorem isPreconnected_cutPlane : IsPreconnected cutPlane :=
  (starConvex_zero_cutPlane.isPathConnected zero_mem_cutPlane).isConnected.isPreconnected

/-- The identity principle on the cut plane: analytic functions agreeing near `0` agree on
the whole cut plane. -/
theorem eqOn_cutPlane_of_eventuallyEq {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f cutPlane)
    (hg : AnalyticOnNhd ℂ g cutPlane) (h : f =ᶠ[𝓝 0] g) : EqOn f g cutPlane :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_cutPlane zero_mem_cutPlane h

/-- The identity principle on the cut plane: analytic functions agreeing on a small disk
about `0` agree on the whole cut plane. -/
theorem eqOn_cutPlane_of_eqOn_ball {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f cutPlane)
    (hg : AnalyticOnNhd ℂ g cutPlane) {r : ℝ} (hr : 0 < r)
    (h : ∀ z : ℂ, ‖z‖ < r → f z = g z) : EqOn f g cutPlane :=
  eqOn_cutPlane_of_eventuallyEq hf hg (by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    exact h z (by simpa using hz))

/-- The identity principle on the cut plane: analytic functions agreeing on the unit disk
agree on the whole cut plane. -/
theorem eqOn_cutPlane_of_eqOn_disk {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f cutPlane)
    (hg : AnalyticOnNhd ℂ g cutPlane) (h : ∀ z : ℂ, ‖z‖ < 1 → f z = g z) :
    EqOn f g cutPlane :=
  eqOn_cutPlane_of_eqOn_ball hf hg one_pos h

/-- For `z` in the cut plane and `t ∈ [0,1]`, `1 - z t` lies in the slit plane. -/
theorem one_sub_mul_mem_slitPlane {z : ℂ} (hz : z ∈ cutPlane) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 - z * t ∈ slitPlane := by
  have hz' : ¬ (1 - z ≤ 0) := mem_slitPlane_iff_not_le_zero.mp hz
  rw [mem_slitPlane_iff_not_le_zero]
  intro hle
  apply hz'
  rw [Complex.le_def] at hle ⊢
  simp only [sub_re, sub_im, one_re, one_im, mul_re, mul_im, ofReal_re, ofReal_im, mul_zero,
    sub_zero, zero_re, zero_im, zero_add] at hle ⊢
  obtain ⟨hre, him⟩ := hle
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    norm_num at hre
  · have him' : z.im = 0 := by
      have : z.im * t = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right h0.ne'
    refine ⟨?_, by simp [him']⟩
    nlinarith [ht.2]

/-- The integrand of Euler's integral 15.6.1. -/
@[expose]
def eulerKernel (a b c z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)

/-- The `z`-derivative of the integrand. -/
@[expose]
def eulerKernelDeriv (a b c z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
    (-a * (1 - z * t) ^ (-a - 1) * -(1 * (t : ℂ)))

/-- Euler's integral in the regularized normalization:
`𝐅(a,b;c;z) = (Γ(b) Γ(c-b))⁻¹ ∫₀¹ t^(b-1) (1-t)^(c-b-1) (1 - z t)^(-a) dt`. -/
@[expose]
def regularizedGaussHypergeometricIntegral (a b c z : ℂ) : ℂ :=
  (Gamma b * Gamma (c - b))⁻¹ * ∫ t : ℝ in (0 : ℝ)..1, eulerKernel a b c z t

/-- Number of `b`-shifts needed to reach `Re b ≥ 1`. -/
@[expose]
def shiftB (b : ℂ) : ℕ := ⌈1 - b.re⌉₊

/-- Number of `c`-shifts needed so that `Re (c - b) ≥ 1` still holds after the `b`-shifts. -/
@[expose]
def shiftC (b c : ℂ) : ℕ := ⌈1 + shiftB b - (c - b).re⌉₊

/-- The recursion fuel. -/
@[expose]
def shiftMeasure (b c : ℂ) : ℕ := shiftB b + shiftC b c

/-- The recursion with fuel: shift `c` while `shiftC > 0`, then shift `b` while `shiftB > 0`,
then use Euler's integral. -/
@[expose]
def regularizedGaussHypergeometricByShifts : ℕ → ℂ → ℂ → ℂ → ℂ → ℂ
  | 0, a, b, c, z => regularizedGaussHypergeometricIntegral a b c z
  | n + 1, a, b, c, z =>
    if 0 < shiftC b c then
      (c - a) * regularizedGaussHypergeometricByShifts n a b (c + 1) z + a
          * regularizedGaussHypergeometricByShifts n (a + 1) b (c + 1) z
    else if 0 < shiftB b then
      regularizedGaussHypergeometricByShifts n a (b + 1) c z - a * z
          * regularizedGaussHypergeometricByShifts n (a + 1) (b + 1) (c + 1) z
    else regularizedGaussHypergeometricIntegral a b c z

/-- The regularized Gauss function `𝐅(a,b;c;z) = ₂F₁(a,b;c;z)/Γ(c)` continued to the cut
plane `ℂ ∖ [1, ∞)`, for all parameters (DLMF §15.2(i)). Its domain is `cutPlane`; the series is
Mathlib's `regularizedGaussHGFun` and the Euler integral is
`regularizedGaussHypergeometricIntegral`. -/
@[expose]
def regularizedGaussHypergeometric (a b c z : ℂ) : ℂ :=
    regularizedGaussHypergeometricByShifts (shiftMeasure b c) a b c z

end DLMF.Hypergeometric
