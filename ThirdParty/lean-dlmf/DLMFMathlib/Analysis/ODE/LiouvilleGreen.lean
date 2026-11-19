/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LiouvilleGreenVolterra

/-!
# The Liouville–Green (WKB) approximation with error bounds (stage 2)

Following F. W. J. Olver, *Asymptotics and Special Functions*, Ch. 6, §2 and Ch. 10, §3, we
prove that the equation

`w'' = (k² A⁻⁴ + g) w`

on `(a, ∞)` has a solution `w = A E (1 + ε)`, where `E' = -k A⁻² E` (so that, for `A = f^{-1/4}`
and `ξ' = f^{1/2}`, `A E = f^{-1/4} exp (-k ξ)` is the Liouville–Green approximation of a
solution of `w'' = (k² f + g) w`), with the error bounds

`‖ε x‖ ≤ exp (κ V x) - 1`,   `‖A(x)² ε'(x)‖ ≤ (exp (κ V x) - 1) / κ`,

where `V x = ∫_{(x,∞)} ‖A A'' - g A²‖` is the variation on `(x, ∞)` of Olver's error-control
function `F = ∫ (f^{-1/4} (f^{-1/4})'' - g f^{-1/2})`, and `κ` bounds the Volterra kernel
`(1 - E(t)²/E(x)²)/(2k)` for `x < t`. The parameter `k ∈ 𝕜` covers at once

* the exponential case (`k = u > 0` real, `E = exp (-u ξ)`, `κ = 1/(2u)`), Olver Ch. 6,
  Thm. 2.1 and Ch. 10, Thm. 3.1, and
* the oscillatory case (`k = i u`, `E = exp (-i u ξ)`, `κ = 1/|u|`), Olver Ch. 6, Thm. 2.2 and
  Ch. 10, §3.

The error is `O(1/u)` uniformly in `x` for large `u` whenever `V` is bounded. These concrete
cases are in `DLMFMathlib.Analysis.ODE.LiouvilleGreenReal`.

The proof solves the Volterra equation of `DLMFMathlib.Analysis.ODE.LiouvilleGreenVolterra` with
the rank-two kernel `(1 - E(t)²/E(x)²)/(2k)` and verifies the differential equation directly by
differentiating the tail integrals.

## Main results

* `LiouvilleGreen.exists_solution_of_kernel_bound`: the general theorem.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace LiouvilleGreen

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Liouville–Green approximation with error bounds**, general form.
Let `A ≠ 0` be twice differentiable on `(a, ∞)` and let `E` solve `E' = -k A⁻² E`, so that
`A E` is the Liouville–Green approximation `f^{-1/4} exp (-k ∫ f^{1/2})` with `f = A⁻⁴`.
Put `F' = A A'' - g A²` (the derivative of Olver's error-control function). If `‖E‖` is
nonincreasing, `‖(1 - E(t)²/E(x)²)/(2k)‖ ≤ κ` for `a < x < t` and `‖F'‖` is integrable at
infinity, then `w'' = (k² A⁻⁴ + g) w` has a solution `w = A E (1 + ε)` on `(a, ∞)` with
`‖ε x‖ ≤ exp (κ V x) - 1` and `‖A² ε'‖ ≤ (exp (κ V x) - 1)/κ`, where
`V x = ∫_{(x,∞)} ‖F'‖` is the variation of the error-control function on `(x, ∞)`
(Olver, *Asymptotics and Special Functions*, Ch. 6, Thm. 2.1 and Ch. 10, Thm. 3.1). -/
theorem exists_solution_of_kernel_bound {a κ : ℝ} {k : 𝕜} {A A' A'' E g : ℝ → 𝕜}
    (hk : k ≠ 0) (hκ : 0 < κ)
    (hA : ∀ x, a < x → A x ≠ 0)
    (hA' : ∀ x, a < x → HasDerivAt A (A' x) x)
    (hA'' : ∀ x, a < x → HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' (Ioi a)) (hgc : ContinuousOn g (Ioi a))
    (hE0 : ∀ x, a < x → E x ≠ 0)
    (hE : ∀ x, a < x → HasDerivAt E (-(k * (A x ^ 2)⁻¹ * E x)) x)
    (hEle : ∀ x t, a < x → x < t → ‖E t‖ ≤ ‖E x‖)
    (hK : ∀ x t, a < x → x < t → ‖(1 - E t ^ 2 / E x ^ 2) / (2 * k)‖ ≤ κ)
    (hFi : ∀ c, a < c → IntegrableOn (fun t => ‖A t * A'' t - g t * A t ^ 2‖) (Ioi c)) :
    ∃ ε ε' w' : ℝ → 𝕜, ∀ x, a < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => A y * E y * (1 + ε y)) (w' x) x ∧
      HasDerivAt w' ((k ^ 2 * (A x ^ 4)⁻¹ + g x) * (A x * E x * (1 + ε x))) x ∧
      ‖ε x‖ ≤ Real.exp (κ * ∫ t in Ioi x, ‖A t * A'' t - g t * A t ^ 2‖) - 1 ∧
      ‖A x ^ 2 * ε' x‖ ≤
        (Real.exp (κ * ∫ t in Ioi x, ‖A t * A'' t - g t * A t ^ 2‖) - 1) / κ := by
  set F' : ℝ → 𝕜 := fun t => A t * A'' t - g t * A t ^ 2 with hF'
  have hAc : ContinuousOn A (Ioi a) := fun x hx =>
    (hA' x hx).continuousAt.continuousWithinAt
  have hEc : ContinuousOn E (Ioi a) := fun x hx =>
    (hE x hx).continuousAt.continuousWithinAt
  have hF'c : ContinuousOn F' (Ioi a) := (hAc.mul hA''c).sub (hgc.mul (hAc.pow 2))
  have hF'i : ∀ c, a < c → IntegrableOn F' (Ioi c) := fun c hc =>
    (integrable_norm_iff ((hF'c.mono (Ioi_subset_Ioi hc.le)).aestronglyMeasurable
      measurableSet_Ioi)).1 (hFi c hc)
  set ρ : ℝ → ℝ := fun t => κ * ‖F' t‖ with hρ
  have hρc : ContinuousOn ρ (Ioi a) := continuousOn_const.mul hF'c.norm
  have hρi : ∀ c, a < c → IntegrableOn ρ (Ioi c) := fun c hc => (hFi c hc).const_mul κ
  have hρ0 : ∀ t, a < t → 0 ≤ ρ t := fun t _ => by positivity
  have hq₂ : ∀ c, a < c → IntegrableOn (fun t => E t ^ 2 * F' t) (Ioi c) := by
    intro c hc
    refine Integrable.mono' ((hFi c hc).const_mul (‖E c‖ ^ 2))
      (((hEc.pow 2).mul hF'c).mono (Ioi_subset_Ioi hc.le) |>.aestronglyMeasurable
        measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [norm_mul, norm_pow]
    gcongr
    exact hEle c t hc ht
  have hp₂c : ContinuousOn (fun x => (2 * k)⁻¹ * (E x ^ 2)⁻¹) (Ioi a) :=
    continuousOn_const.mul ((hEc.pow 2).inv₀ fun x hx => pow_ne_zero 2 (hE0 x hx))
  obtain ⟨h, hhm, hhb, hheq⟩ := exists_volterra_solution (𝕜 := 𝕜)
    (p₁ := fun _ => -(2 * k)⁻¹) (q₁ := fun _ => 1)
    (p₂ := fun x => (2 * k)⁻¹ * (E x ^ 2)⁻¹) (q₂ := fun t => E t ^ 2) (ψ := F')
    (J := fun _ => 1) (ρ := ρ) (a := a)
    aestronglyMeasurable_const (hp₂c.aestronglyMeasurable measurableSet_Ioi)
    (fun c hc => by simpa using hF'i c hc) hq₂ aestronglyMeasurable_const
    (fun _ _ => by simp) hρc hρi (fun x t hx hxt => by
      have heq : (-(2 * k)⁻¹ * 1 + (2 * k)⁻¹ * (E x ^ 2)⁻¹ * E t ^ 2) =
          -((1 - E t ^ 2 / E x ^ 2) / (2 * k)) := by ring
      rw [heq, norm_mul, norm_neg]
      exact mul_le_mul_of_nonneg_right (hK x t hx hxt) (norm_nonneg _))
  set R : ℝ → ℝ := fun t => ∫ s in Ioi t, ρ s with hR
  have hRx : ∀ x, R x = κ * ∫ t in Ioi x, ‖F' t‖ := fun x => integral_const_mul _ _
  have hub : ∀ t, a < t → ‖1 + h t‖ ≤ Real.exp (R t) := fun t ht =>
    (norm_add_le _ _).trans (by have := hhb t ht; simp only [norm_one]; linarith)
  have hum : AEStronglyMeasurable (fun t => 1 + h t) (volume.restrict (Ioi a)) :=
    aestronglyMeasurable_const.add hhm
  have hub' : ∀ x, a < x → ∀ t ∈ Ioi x, ‖1 + h t‖ ≤ Real.exp (R x) := fun x hx t ht =>
    (hub t (hx.trans ht)).trans (Real.exp_le_exp.2 (tail_anti hρ0 hρi hx (le_of_lt ht)))
  have hmulb : ∀ {q : ℝ → 𝕜}, (∀ c, a < c → IntegrableOn (fun t => q t * F' t) (Ioi c)) →
      ∀ c, a < c → IntegrableOn (fun t => q t * F' t * (1 + h t)) (Ioi c) := by
    intro q hq c hc
    exact (hq c hc).mul_bdd (hum.mono_measure (Measure.restrict_mono
      (Ioi_subset_Ioi hc.le) le_rfl)) (ae_restrict_of_forall_mem measurableSet_Ioi (hub' c hc))
  have hI₁i := hmulb (q := fun _ => 1) (fun c hc => by simpa using hF'i c hc)
  have hI₂i := hmulb hq₂
  set I₁ : ℝ → 𝕜 := fun x => ∫ t in Ioi x, 1 * F' t * (1 + h t) with hI₁
  set I₂ : ℝ → 𝕜 := fun x => ∫ t in Ioi x, E t ^ 2 * F' t * (1 + h t) with hI₂
  have hheq' : ∀ x, a < x → h x = -(2 * k)⁻¹ * I₁ x + (2 * k)⁻¹ * (E x ^ 2)⁻¹ * I₂ x :=
    fun x hx => hheq x hx
  have hhc : ContinuousOn h (Ioi a) :=
    ((continuousOn_const.mul (continuousOn_integral_Ioi hI₁i)).add
      (hp₂c.mul (continuousOn_integral_Ioi hI₂i))).congr fun x hx => hheq' x hx
  have hI₁d : ∀ x, a < x → HasDerivAt I₁ (-(1 * F' x * (1 + h x))) x := fun x hx =>
    hasDerivAt_integral_Ioi hI₁i hx ((continuousOn_const.mul hF'c).mul
      (continuousOn_const.add hhc) |>.continuousAt (Ioi_mem_nhds hx))
  have hI₂d : ∀ x, a < x → HasDerivAt I₂ (-(E x ^ 2 * F' x * (1 + h x))) x := fun x hx =>
    hasDerivAt_integral_Ioi hI₂i hx (((hEc.pow 2).mul hF'c).mul
      (continuousOn_const.add hhc) |>.continuousAt (Ioi_mem_nhds hx))
  have hEinv : ∀ x, a < x → HasDerivAt (fun y => (E y ^ 2)⁻¹)
      (-((2 : ℕ) * E x ^ (2 - 1) * -(k * (A x ^ 2)⁻¹ * E x)) / (E x ^ 2) ^ 2) x :=
    fun x hx => ((hE x hx).pow 2).inv (pow_ne_zero 2 (hE0 x hx))
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℝ → 𝕜, ε' = fun x => (A x ^ 2)⁻¹ * (E x ^ 2)⁻¹ * I₂ x :=
    ⟨_, rfl⟩
  have hεd : ∀ x, a < x → HasDerivAt h (ε' x) x := by
    intro x hx
    have := ((hasDerivAt_const x (-(2 * k)⁻¹)).mul (hI₁d x hx)).add
      (((hasDerivAt_const x (2 * k)⁻¹).mul (hEinv x hx)).mul (hI₂d x hx))
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · have := hA x hx
      have := hE0 x hx
      rw [hε'def]
      simp only [Pi.mul_apply]
      field_simp
      ring
    · filter_upwards [Ioi_mem_nhds hx] with y hy using hheq' y hy
  have hε'd : ∀ x, a < x → HasDerivAt ε'
      (-(2 * (A x * A' x - k)) * ε' x / A x ^ 2 - F' x * (1 + h x) / A x ^ 2) x := by
    intro x hx
    have := ((((hA' x hx).pow 2).inv (pow_ne_zero 2 (hA x hx))).mul (hEinv x hx)).mul
      (hI₂d x hx)
    rw [hε'def]
    refine this.congr_deriv ?_
    have := hA x hx
    have := hE0 x hx
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
    field_simp
    ring
  refine ⟨h, ε', fun y => E y * ((A' y - k * (A y)⁻¹) * (1 + h y) + A y * ε' y),
    fun x hx => ⟨hεd x hx, ?_, ?_, ?_, ?_⟩⟩
  · refine (((hA' x hx).mul (hE x hx)).mul ((hεd x hx).const_add 1)).congr_deriv ?_
    have := hA x hx
    simp only [Pi.mul_apply]
    field_simp
    ring
  · refine ((hE x hx).mul ((((hA'' x hx).sub (((hA' x hx).inv (hA x hx)).const_mul k)).mul
      ((hεd x hx).const_add 1)).add ((hA' x hx).mul (hε'd x hx)))).congr_deriv ?_
    have := hA x hx
    rw [hF']
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.inv_apply]
    field_simp
    ring
  · rw [← hRx]
    exact hhb x hx
  · rw [← hRx]
    have hεx : A x ^ 2 * ε' x = ∫ t in Ioi x, (E x ^ 2)⁻¹ * (E t ^ 2 * F' t * (1 + h t)) := by
      have := hA x hx
      rw [integral_const_mul, hε'def]
      field_simp
      rfl
    have hexpt := integral_Ioi_mul_exp_tail hρc hρ0 hρi hx
    have hEx : 0 < ‖E x‖ ^ 2 := by have := hE0 x hx; positivity
    calc ‖A x ^ 2 * ε' x‖
        = ‖∫ t in Ioi x, (E x ^ 2)⁻¹ * (E t ^ 2 * F' t * (1 + h t))‖ := by rw [hεx]
      _ ≤ ∫ t in Ioi x, κ⁻¹ * (ρ t * Real.exp (R t)) := by
          refine norm_integral_le_of_norm_le (hexpt.1.const_mul κ⁻¹)
            (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
          have hle : ‖E t‖ ^ 2 ≤ ‖E x‖ ^ 2 := by
            have := hEle x t hx ht
            gcongr
          rw [norm_mul, norm_inv, norm_mul, norm_mul, norm_pow, norm_pow]
          calc (‖E x‖ ^ 2)⁻¹ * (‖E t‖ ^ 2 * ‖F' t‖ * ‖1 + h t‖)
              ≤ (‖E x‖ ^ 2)⁻¹ * (‖E x‖ ^ 2 * ‖F' t‖ * Real.exp (R t)) := by
                gcongr
                exact hub t (hx.trans ht)
            _ = κ⁻¹ * (ρ t * Real.exp (R t)) := by
                have : ‖E x‖ ≠ 0 := norm_ne_zero_iff.2 (hE0 x hx)
                simp only [hρ]
                field_simp
      _ = (Real.exp (R x) - 1) / κ := by
          rw [integral_const_mul, hexpt.2, div_eq_inv_mul]

end LiouvilleGreen
