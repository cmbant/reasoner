/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Volterra integral equations on a half-line (Liouville–Green, stage 1)

This file provides the existence theory behind the Liouville–Green (WKB) approximation with
error bounds, following F. W. J. Olver, *Asymptotics and Special Functions*, Ch. 6, §10.

We consider Volterra equations on `(a, ∞)` with tail integrals,

`h x = ∫_{(x,∞)} K x t ψ t (J t + h t) dt`,

where the kernel has rank two, `K x t = p₁ x q₁ t + p₂ x q₂ t`. Every kernel produced by
variation of constants for a second-order linear equation has this form, and the rank-two
structure makes the solution easy to differentiate later. If `‖K x t ψ t‖ ≤ ρ t` for
`a < x < t` and `‖J‖ ≤ 1`, the Picard series converges and its sum satisfies

`‖h x‖ ≤ exp (∫_{(x,∞)} ρ) - 1`

(Olver, Ch. 6, Thm. 10.1). The weight `ρ` must be continuous on `(a, ∞)` and integrable on
every `(c, ∞)` with `c > a`; the data `p`, `q`, `ψ`, `J` need only be measurable. No uniform
integrability at `a` is required: all estimates are pointwise in `x > a`.

## Main results

* `LiouvilleGreen.continuousOn_integral_Ioi`, `LiouvilleGreen.hasDerivAt_integral_Ioi`:
  continuity and differentiation of tail integrals `x ↦ ∫_{(x,∞)} f`.
* `LiouvilleGreen.tendsto_exp_integral_Ioi_sub_one`: the error bounds tend to `0`.
* `LiouvilleGreen.integral_Ioi_mul_comp_tail`: `∫_{(x,∞)} ρ φ(R) = Φ(R x) - Φ 0` for the
  tail `R` of `ρ` and `Φ' = φ`, with the power and exponential cases.
* `LiouvilleGreen.volterraOp`: the rank-two Volterra operator.
* `LiouvilleGreen.exists_volterra_solution_add`: existence of a solution of the inhomogeneous
  equation `h = σ + L h` with the bound `‖h - σ‖ ≤ B (exp R - 1)`.
* `LiouvilleGreen.exists_volterra_solution`: the form `h = L (J + h)` with `‖h‖ ≤ exp R - 1`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace LiouvilleGreen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Splitting a tail integral: `∫_{(c,∞)} f = ∫_c^y f + ∫_{(y,∞)} f` for `c ≤ y`. -/
theorem integral_Ioi_eq_sub {f : ℝ → E} {c y : ℝ} (hf : IntegrableOn f (Ioi c))
    (hcy : c ≤ y) :
    ∫ t in Ioi y, f t = (∫ t in Ioi c, f t) - ∫ t in c..y, f t := by
  rw [intervalIntegral.integral_of_le hcy, ← Ioc_union_Ioi_eq_Ioi hcy,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hcy))]
  abel

/-- Tail integrals `x ↦ ∫_{(x,∞)} f` are continuous on `(a,∞)` when `f` is integrable on every
`(c,∞)`, `c > a`. -/
theorem continuousOn_integral_Ioi {f : ℝ → E} {a : ℝ}
    (hf : ∀ c, a < c → IntegrableOn f (Ioi c)) :
    ContinuousOn (fun x => ∫ t in Ioi x, f t) (Ioi a) := by
  intro x hx
  set c := (a + x) / 2 with hc
  have hac : a < c := by simp only [mem_Ioi] at hx; rw [hc]; linarith
  have hcx : c < x := by simp only [mem_Ioi] at hx; rw [hc]; linarith
  have hfc := hf c hac
  have hprim : ContinuousOn (fun y => ∫ t in c..y, f t) (uIcc c (x + 1)) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le (by linarith)]
      exact (integrableOn_Icc_iff_integrableOn_Ioc).2 (hfc.mono_set Ioc_subset_Ioi_self))
  have hnhds : Icc c (x + 1) ∈ 𝓝 x := Icc_mem_nhds hcx (by linarith)
  have hca : ContinuousAt (fun y => (∫ t in Ioi c, f t) - ∫ t in c..y, f t) x :=
    continuousAt_const.sub (hprim.continuousAt (by rwa [uIcc_of_le (by linarith)]))
  refine (hca.congr ?_).continuousWithinAt
  filter_upwards [Ioi_mem_nhds hcx] with y hy
  exact (integral_Ioi_eq_sub hfc hy.le).symm

/-- The derivative of a tail integral: `d/dx ∫_{(x,∞)} f = -f x` at a point of continuity. -/
theorem hasDerivAt_integral_Ioi [CompleteSpace E] {f : ℝ → E} {a x : ℝ}
    (hf : ∀ c, a < c → IntegrableOn f (Ioi c)) (hx : a < x) (hfx : ContinuousAt f x) :
    HasDerivAt (fun y => ∫ t in Ioi y, f t) (-f x) x := by
  set c := (a + x) / 2 with hc
  have hac : a < c := by rw [hc]; linarith
  have hcx : c < x := by rw [hc]; linarith
  have hfc := hf c hac
  have h1 : HasDerivAt (fun y => ∫ t in c..y, f t) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hcx.le).2
        (hfc.mono_set Ioc_subset_Ioi_self))
      (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hfc.aestronglyMeasurable
        (Ioi_mem_nhds hcx)) hfx
  refine (h1.const_sub (∫ t in Ioi c, f t)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hcx] with y hy
  exact integral_Ioi_eq_sub hfc hy.le

/-- Tail integrals tend to `0` at infinity. -/
theorem tendsto_integral_Ioi {f : ℝ → E} {c : ℝ} (hf : IntegrableOn f (Ioi c)) :
    Tendsto (fun y => ∫ t in Ioi y, f t) atTop (𝓝 0) := by
  have h := (intervalIntegral_tendsto_integral_Ioi c hf tendsto_id).const_sub
    (∫ t in Ioi c, f t)
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [Ici_mem_atTop c] with y hy
  exact (integral_Ioi_eq_sub hf hy).symm

/-- The Liouville–Green error bounds `exp (κ ∫_{(x,∞)} ρ) - 1` tend to `0` at infinity. -/
theorem tendsto_exp_integral_Ioi_sub_one {ρ : ℝ → ℝ} {c : ℝ} (hρ : IntegrableOn ρ (Ioi c))
    (κ : ℝ) : Tendsto (fun x => Real.exp (κ * ∫ t in Ioi x, ρ t) - 1) atTop (𝓝 0) := by
  have h0 := (tendsto_integral_Ioi hρ).const_mul κ
  rw [mul_zero] at h0
  have h := ((Real.continuous_exp.tendsto 0).comp h0).sub_const 1
  simpa using h

/-! ### The tail of a nonnegative function -/

section Tail

variable {ρ : ℝ → ℝ} {a : ℝ}

/-- The tail `∫_{(x,∞)} ρ` of a nonnegative function is nonnegative. -/
theorem tail_nonneg (hρ0 : ∀ t, a < t → 0 ≤ ρ t) {x : ℝ} (hx : a ≤ x) :
    0 ≤ ∫ t in Ioi x, ρ t :=
  setIntegral_nonneg measurableSet_Ioi fun t ht => hρ0 t (lt_of_le_of_lt hx ht)

/-- The tail `∫_{(x,∞)} ρ` of a nonnegative function is antitone in `x`. -/
theorem tail_anti (hρ0 : ∀ t, a < t → 0 ≤ ρ t) (hρi : ∀ c, a < c → IntegrableOn ρ (Ioi c))
    {x y : ℝ} (hx : a < x) (hxy : x ≤ y) :
    ∫ t in Ioi y, ρ t ≤ ∫ t in Ioi x, ρ t :=
  setIntegral_mono_set (hρi x hx)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => hρ0 t (hx.trans ht))
    (Ioi_subset_Ioi hxy).eventuallyLE

/-- Integration against the tail: if `Φ' = φ` and `R x = ∫_{(x,∞)} ρ`, then
`∫_{(x,∞)} ρ φ(R) = Φ(R x) - Φ 0`. -/
theorem integral_Ioi_mul_comp_tail (hρc : ContinuousOn ρ (Ioi a))
    (hρ0 : ∀ t, a < t → 0 ≤ ρ t) (hρi : ∀ c, a < c → IntegrableOn ρ (Ioi c))
    {Φ φ : ℝ → ℝ} (hΦ : ∀ s, HasDerivAt Φ (φ s) s) (hφ : Continuous φ) {x : ℝ} (hx : a < x) :
    IntegrableOn (fun t => ρ t * φ (∫ s in Ioi t, ρ s)) (Ioi x) ∧
      ∫ t in Ioi x, ρ t * φ (∫ s in Ioi t, ρ s) = Φ (∫ s in Ioi x, ρ s) - Φ 0 := by
  set R : ℝ → ℝ := fun t => ∫ s in Ioi t, ρ s with hR
  have hRc : ContinuousOn R (Ioi a) := continuousOn_integral_Ioi hρi
  have hRd : ∀ t, a < t → HasDerivAt R (-ρ t) t := fun t ht =>
    hasDerivAt_integral_Ioi hρi ht (hρc.continuousAt (Ioi_mem_nhds ht))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := R x)).exists_bound_of_continuousOn
    hφ.continuousOn
  have hmem : ∀ t ∈ Ioi x, R t ∈ Icc 0 (R x) := fun t ht =>
    ⟨tail_nonneg hρ0 (hx.trans ht).le, tail_anti hρ0 hρi hx (le_of_lt ht)⟩
  have hint : IntegrableOn (fun t => ρ t * φ (R t)) (Ioi x) :=
    (hρi x hx).mul_bdd
      ((hφ.comp_continuousOn (hRc.mono (Ioi_subset_Ioi hx.le))).aestronglyMeasurable
        measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => hC _ (hmem t ht))
  refine ⟨hint, ?_⟩
  have hft := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => -Φ (R t))
    (f' := fun t => ρ t * φ (R t)) (m := -Φ 0) (a := x)
    ((hΦ (R x)).continuousAt.comp (hRd x hx).continuousAt).neg.continuousWithinAt
    (fun t ht => by
      exact ((hΦ (R t)).comp t (hRd t (hx.trans ht))).neg.congr_deriv (by ring))
    hint ((hΦ 0).continuousAt.tendsto.comp (tendsto_integral_Ioi (hρi x hx))).neg
  rw [hft]
  ring

/-- `∫_{(x,∞)} ρ R^n / n! = R(x)^{n+1} / (n+1)!` for the tail `R` of `ρ`. -/
theorem integral_Ioi_mul_tail_pow (hρc : ContinuousOn ρ (Ioi a))
    (hρ0 : ∀ t, a < t → 0 ≤ ρ t) (hρi : ∀ c, a < c → IntegrableOn ρ (Ioi c)) (n : ℕ)
    {x : ℝ} (hx : a < x) :
    IntegrableOn (fun t => ρ t * ((∫ s in Ioi t, ρ s) ^ n / n.factorial)) (Ioi x) ∧
      ∫ t in Ioi x, ρ t * ((∫ s in Ioi t, ρ s) ^ n / n.factorial) =
        (∫ s in Ioi x, ρ s) ^ (n + 1) / (n + 1).factorial := by
  have h := integral_Ioi_mul_comp_tail hρc hρ0 hρi
    (Φ := fun s => s ^ (n + 1) / (n + 1).factorial) (φ := fun s => s ^ n / n.factorial)
    (fun s => by
      convert (hasDerivAt_pow (n + 1) s).div_const ((n + 1).factorial : ℝ) using 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp)
    (by fun_prop) hx
  simpa using h

/-- `∫_{(x,∞)} ρ exp(R) = exp(R x) - 1` for the tail `R` of `ρ`. -/
theorem integral_Ioi_mul_exp_tail (hρc : ContinuousOn ρ (Ioi a))
    (hρ0 : ∀ t, a < t → 0 ≤ ρ t) (hρi : ∀ c, a < c → IntegrableOn ρ (Ioi c))
    {x : ℝ} (hx : a < x) :
    IntegrableOn (fun t => ρ t * Real.exp (∫ s in Ioi t, ρ s)) (Ioi x) ∧
      ∫ t in Ioi x, ρ t * Real.exp (∫ s in Ioi t, ρ s) =
        Real.exp (∫ s in Ioi x, ρ s) - 1 := by
  have h := integral_Ioi_mul_comp_tail hρc hρ0 hρi (Φ := Real.exp) (φ := Real.exp)
    (fun s => Real.hasDerivAt_exp s) Real.continuous_exp hx
  simpa using h

end Tail

/-! ### Volterra equations with a rank-two kernel -/

section Volterra

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Volterra operator with the rank-two kernel `K x t = p₁ x q₁ t + p₂ x q₂ t` and weight
`ψ`: `(L φ) x = ∫_{(x,∞)} K x t ψ t φ t dt`, written with the two factors separated. -/
noncomputable def volterraOp (p₁ p₂ q₁ q₂ ψ : ℝ → 𝕜) (φ : ℝ → 𝕜) (x : ℝ) : 𝕜 :=
  p₁ x * (∫ t in Ioi x, q₁ t * ψ t * φ t) + p₂ x * ∫ t in Ioi x, q₂ t * ψ t * φ t

variable {p₁ p₂ q₁ q₂ ψ : ℝ → 𝕜} {ρ : ℝ → ℝ} {a : ℝ}

/-- One Picard step: if `‖φ t‖ ≤ B t R(t)ⁿ / n!` with `R` the tail of `ρ` and `B ≥ 0`
nonincreasing, then the integrands of `volterraOp` are integrable, `volterraOp φ` is measurable
and `‖volterraOp φ x‖ ≤ B x R(x)ⁿ⁺¹ / (n + 1)!`. -/
theorem volterraOp_step
    (hp₁ : AEStronglyMeasurable p₁ (volume.restrict (Ioi a)))
    (hp₂ : AEStronglyMeasurable p₂ (volume.restrict (Ioi a)))
    (hq₁ : ∀ c, a < c → IntegrableOn (fun t => q₁ t * ψ t) (Ioi c))
    (hq₂ : ∀ c, a < c → IntegrableOn (fun t => q₂ t * ψ t) (Ioi c))
    (hρc : ContinuousOn ρ (Ioi a)) (hρi : ∀ c, a < c → IntegrableOn ρ (Ioi c))
    (hK : ∀ x t, a < x → x < t → ‖(p₁ x * q₁ t + p₂ x * q₂ t) * ψ t‖ ≤ ρ t)
    {B : ℝ → ℝ} (hB0 : ∀ t, a < t → 0 ≤ B t) (hBa : ∀ x t, a < x → x ≤ t → B t ≤ B x)
    {φ : ℝ → 𝕜} (hφm : AEStronglyMeasurable φ (volume.restrict (Ioi a))) (n : ℕ)
    (hφ : ∀ t, a < t → ‖φ t‖ ≤ B t * ((∫ s in Ioi t, ρ s) ^ n / n.factorial)) :
    (∀ x, a < x → IntegrableOn (fun t => q₁ t * ψ t * φ t) (Ioi x)) ∧
    (∀ x, a < x → IntegrableOn (fun t => q₂ t * ψ t * φ t) (Ioi x)) ∧
    AEStronglyMeasurable (volterraOp p₁ p₂ q₁ q₂ ψ φ) (volume.restrict (Ioi a)) ∧
    ∀ x, a < x → ‖volterraOp p₁ p₂ q₁ q₂ ψ φ x‖ ≤
      B x * ((∫ s in Ioi x, ρ s) ^ (n + 1) / (n + 1).factorial) := by
  have hρ0 : ∀ t, a < t → 0 ≤ ρ t := fun t ht =>
    (norm_nonneg _).trans (hK ((a + t) / 2) t (by linarith) (by linarith))
  have hRle : ∀ x, a < x → ∀ t ∈ Ioi x,
      (∫ s in Ioi t, ρ s) ^ n / n.factorial ≤ (∫ s in Ioi x, ρ s) ^ n / n.factorial :=
    fun x hx t ht => div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (tail_nonneg hρ0 (hx.trans ht).le)
        (tail_anti hρ0 hρi hx (le_of_lt ht)) n) (Nat.cast_nonneg _)
  have hφx : ∀ x, a < x → ∀ t ∈ Ioi x,
      ‖φ t‖ ≤ B x * ((∫ s in Ioi x, ρ s) ^ n / n.factorial) :=
    fun x hx t ht => (hφ t (hx.trans ht)).trans (mul_le_mul (hBa x t hx (le_of_lt ht))
      (hRle x hx t ht) (by have := tail_nonneg hρ0 (hx.trans ht).le; positivity)
      (hB0 x hx))
  have hint : ∀ {q : ℝ → 𝕜}, (∀ c, a < c → IntegrableOn (fun t => q t * ψ t) (Ioi c)) →
      ∀ x, a < x → IntegrableOn (fun t => q t * ψ t * φ t) (Ioi x) := by
    intro q hq x hx
    exact (hq x hx).mul_bdd (hφm.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hx.le)
      le_rfl)) (ae_restrict_of_forall_mem measurableSet_Ioi (hφx x hx))
  have hi₁ := hint hq₁
  have hi₂ := hint hq₂
  refine ⟨hi₁, hi₂, ?_, ?_⟩
  · exact (hp₁.mul ((continuousOn_integral_Ioi hi₁).aestronglyMeasurable measurableSet_Ioi)).add
      (hp₂.mul ((continuousOn_integral_Ioi hi₂).aestronglyMeasurable measurableSet_Ioi))
  · intro x hx
    have heq : volterraOp p₁ p₂ q₁ q₂ ψ φ x =
        ∫ t in Ioi x, (p₁ x * q₁ t + p₂ x * q₂ t) * ψ t * φ t := by
      rw [volterraOp, ← integral_const_mul, ← integral_const_mul, ← integral_add
        ((hi₁ x hx).const_mul _) ((hi₂ x hx).const_mul _)]
      congr 1
      ext t
      ring
    have hb := integral_Ioi_mul_tail_pow hρc hρ0 hρi n hx
    rw [heq, ← hb.2, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hb.1.const_mul (B x))
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [norm_mul]
    have hR0 := tail_nonneg hρ0 (hx.trans ht).le
    calc ‖(p₁ x * q₁ t + p₂ x * q₂ t) * ψ t‖ * ‖φ t‖
        ≤ ρ t * (B t * ((∫ s in Ioi t, ρ s) ^ n / n.factorial)) :=
          mul_le_mul (hK x t hx ht) (hφ t (hx.trans ht)) (norm_nonneg _) (hρ0 t (hx.trans ht))
      _ ≤ ρ t * (B x * ((∫ s in Ioi t, ρ s) ^ n / n.factorial)) := by
          have := hρ0 t (hx.trans ht)
          gcongr
          exact hBa x t hx (le_of_lt ht)
      _ = B x * (ρ t * ((∫ s in Ioi t, ρ s) ^ n / n.factorial)) := by ring

/-- **Existence and bound for inhomogeneous Volterra equations with a rank-two kernel**
(Olver, *Asymptotics and Special Functions*, Ch. 6, Thm. 10.1, for kernels of the form
`K x t = p₁ x q₁ t + p₂ x q₂ t`, which covers every variation-of-constants kernel).
If `‖K x t ψ t‖ ≤ ρ t` for `a < x < t`, `ρ` is continuous and integrable at infinity, and the
forcing satisfies `‖σ t‖ ≤ B t` with `B ≥ 0` nonincreasing, then the equation
`h x = σ x + ∫_{(x,∞)} K x t ψ t h t dt` has a solution on `(a, ∞)` with
`‖h x - σ x‖ ≤ B x (exp (∫_{(x,∞)} ρ) - 1)`. The solution is the sum of the Picard series. -/
theorem exists_volterra_solution_add
    (hp₁ : AEStronglyMeasurable p₁ (volume.restrict (Ioi a)))
    (hp₂ : AEStronglyMeasurable p₂ (volume.restrict (Ioi a)))
    (hq₁ : ∀ c, a < c → IntegrableOn (fun t => q₁ t * ψ t) (Ioi c))
    (hq₂ : ∀ c, a < c → IntegrableOn (fun t => q₂ t * ψ t) (Ioi c))
    {σ : ℝ → 𝕜} {B : ℝ → ℝ} (hσm : AEStronglyMeasurable σ (volume.restrict (Ioi a)))
    (hσ : ∀ t, a < t → ‖σ t‖ ≤ B t) (hBa : ∀ x t, a < x → x ≤ t → B t ≤ B x)
    (hρc : ContinuousOn ρ (Ioi a)) (hρi : ∀ c, a < c → IntegrableOn ρ (Ioi c))
    (hK : ∀ x t, a < x → x < t → ‖(p₁ x * q₁ t + p₂ x * q₂ t) * ψ t‖ ≤ ρ t) :
    ∃ h : ℝ → 𝕜, AEStronglyMeasurable h (volume.restrict (Ioi a)) ∧
      (∀ x, a < x → ‖h x - σ x‖ ≤ B x * (Real.exp (∫ s in Ioi x, ρ s) - 1)) ∧
      ∀ x, a < x → h x = σ x + volterraOp p₁ p₂ q₁ q₂ ψ h x := by
  have hB0 : ∀ t, a < t → 0 ≤ B t := fun t ht => (norm_nonneg _).trans (hσ t ht)
  set L := volterraOp p₁ p₂ q₁ q₂ ψ with hL
  set φ : ℕ → ℝ → 𝕜 := fun n => L^[n] σ with hφdef
  set R : ℝ → ℝ := fun t => ∫ s in Ioi t, ρ s with hR
  have hφ : ∀ n, AEStronglyMeasurable (φ n) (volume.restrict (Ioi a)) ∧
      ∀ t, a < t → ‖φ n t‖ ≤ B t * (R t ^ n / n.factorial) := by
    intro n
    induction n with
    | zero => exact ⟨hσm, fun t ht => by simpa [φ] using hσ t ht⟩
    | succ n ih =>
      have hs := volterraOp_step hp₁ hp₂ hq₁ hq₂ hρc hρi hK hB0 hBa ih.1 n ih.2
      have hφs : φ (n + 1) = L (φ n) := Function.iterate_succ_apply' L n σ
      rw [hφs]
      exact ⟨hs.2.2.1, hs.2.2.2⟩
  have hstep : ∀ n, _ := fun n => volterraOp_step hp₁ hp₂ hq₁ hq₂ hρc hρi hK hB0 hBa
    (hφ n).1 n (hφ n).2
  have hρ0 : ∀ t, a < t → 0 ≤ ρ t := fun t ht =>
    (norm_nonneg _).trans (hK ((a + t) / 2) t (by linarith) (by linarith))
  have hexp : ∀ x, HasSum (fun n => R x ^ n / n.factorial) (Real.exp (R x)) := fun x => by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (R x)
  have hsumm : ∀ x, a < x → Summable (fun n => φ n x) := fun x hx =>
    Summable.of_norm_bounded ((hexp x).summable.mul_left (B x)) fun n => (hφ n).2 x hx
  set S : ℝ → 𝕜 := fun x => ∑' n, φ n x with hS
  have hSm : AEStronglyMeasurable S (volume.restrict (Ioi a)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (f := fun N x => ∑ n ∈ Finset.range N, φ n x)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun n _ => (hφ n).1)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
        (hsumm x hx).hasSum.tendsto_sum_nat)
  have hSσ : ∀ x, a < x → S x - σ x = ∑' n, φ (n + 1) x := fun x hx => by
    show ∑' n, φ n x - σ x = _
    rw [(hsumm x hx).tsum_eq_zero_add]
    simp [φ]
  refine ⟨S, hSm, ?_, ?_⟩
  · intro x hx
    have hs1 : HasSum (fun n => B x * (R x ^ (n + 1) / (n + 1).factorial))
        (B x * (Real.exp (R x) - 1)) := by
      have := ((hasSum_nat_add_iff' 1).2 (hexp x)).mul_left (B x)
      simpa using this
    have hnb : ∀ n, ‖φ (n + 1) x‖ ≤ B x * (R x ^ (n + 1) / (n + 1).factorial) :=
      fun n => (hφ (n + 1)).2 x hx
    have hns : Summable fun n => ‖φ (n + 1) x‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnb hs1.summable
    rw [hSσ x hx]
    exact (norm_tsum_le_tsum_norm hns).trans (hns.tsum_le_tsum hnb hs1.summable |>.trans_eq
      hs1.tsum_eq)
  · intro x hx
    -- interchange of sum and integral
    have hswap : ∀ {q : ℝ → 𝕜}, (∀ c, a < c → IntegrableOn (fun t => q t * ψ t) (Ioi c)) →
        (∀ n, IntegrableOn (fun t => q t * ψ t * φ n t) (Ioi x)) →
        Summable (fun n => ∫ t in Ioi x, q t * ψ t * φ n t) ∧
        ∫ t in Ioi x, q t * ψ t * S t = ∑' n, ∫ t in Ioi x, q t * ψ t * φ n t := by
      intro q hq hF
      have hnorm : ∀ n, ∫ t in Ioi x, ‖q t * ψ t * φ n t‖ ≤
          (∫ t in Ioi x, ‖q t * ψ t‖) * (B x * (R x ^ n / n.factorial)) := by
        intro n
        rw [← integral_mul_const]
        refine setIntegral_mono_on (hF n).norm ((hq x hx).norm.mul_const _) measurableSet_Ioi
          fun t ht => ?_
        rw [norm_mul]
        gcongr
        have hR0 := tail_nonneg hρ0 (hx.trans ht).le
        refine ((hφ n).2 t (hx.trans ht)).trans (mul_le_mul (hBa x t hx (le_of_lt ht))
          (div_le_div_of_nonneg_right (pow_le_pow_left₀ hR0
            (tail_anti hρ0 hρi hx (le_of_lt ht)) n) (Nat.cast_nonneg _))
          (by positivity) (hB0 x hx))
      have hsI : Summable fun n => ∫ t in Ioi x, ‖q t * ψ t * φ n t‖ :=
        Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hnorm
          (((hexp x).summable.mul_left (B x)).mul_left _)
      refine ⟨Summable.of_norm_bounded hsI fun n => norm_integral_le_integral_norm _, ?_⟩
      rw [integral_tsum_of_summable_integral_norm hF hsI]
      congr 1
      ext t
      rw [hS, tsum_mul_left]
    have h₁ := hswap hq₁ fun n => (hstep n).1 x hx
    have h₂ := hswap hq₂ fun n => (hstep n).2.1 x hx
    rw [← sub_eq_iff_eq_add', hSσ x hx, hL, volterraOp, h₁.2, h₂.2, ← tsum_mul_left,
      ← tsum_mul_left, ← (h₁.1.mul_left _).tsum_add (h₂.1.mul_left _)]
    congr 1
    ext n
    exact congrFun (Function.iterate_succ_apply' L n σ) x

/-- **Existence and bound for Volterra equations with a rank-two kernel** (Olver,
*Asymptotics and Special Functions*, Ch. 6, Thm. 10.1, specialized to kernels of the form
`K x t = p₁ x q₁ t + p₂ x q₂ t`). If `‖K x t ψ t‖ ≤ ρ t` for `a < x < t`, `‖J‖ ≤ 1` and `ρ` is
continuous and integrable at infinity, the equation `h x = ∫_{(x,∞)} K x t ψ t (J t + h t) dt`
has a solution with `‖h x‖ ≤ exp (∫_{(x,∞)} ρ) - 1` on `(a, ∞)`. -/
theorem exists_volterra_solution
    (hp₁ : AEStronglyMeasurable p₁ (volume.restrict (Ioi a)))
    (hp₂ : AEStronglyMeasurable p₂ (volume.restrict (Ioi a)))
    (hq₁ : ∀ c, a < c → IntegrableOn (fun t => q₁ t * ψ t) (Ioi c))
    (hq₂ : ∀ c, a < c → IntegrableOn (fun t => q₂ t * ψ t) (Ioi c))
    {J : ℝ → 𝕜} (hJm : AEStronglyMeasurable J (volume.restrict (Ioi a)))
    (hJ : ∀ t, a < t → ‖J t‖ ≤ 1)
    (hρc : ContinuousOn ρ (Ioi a)) (hρi : ∀ c, a < c → IntegrableOn ρ (Ioi c))
    (hK : ∀ x t, a < x → x < t → ‖(p₁ x * q₁ t + p₂ x * q₂ t) * ψ t‖ ≤ ρ t) :
    ∃ h : ℝ → 𝕜, AEStronglyMeasurable h (volume.restrict (Ioi a)) ∧
      (∀ x, a < x → ‖h x‖ ≤ Real.exp (∫ s in Ioi x, ρ s) - 1) ∧
      ∀ x, a < x → h x = volterraOp p₁ p₂ q₁ q₂ ψ (fun t => J t + h t) x := by
  obtain ⟨S, hSm, hSb, hSeq⟩ := exists_volterra_solution_add hp₁ hp₂ hq₁ hq₂ hJm
    (B := fun _ => 1) hJ (fun _ _ _ _ => le_rfl) hρc hρi hK
  refine ⟨fun x => S x - J x, hSm.sub hJm, fun x hx => by simpa using hSb x hx, fun x hx => ?_⟩
  have hJh : (fun t => J t + (S t - J t)) = S := by ext t; ring
  simp only [hJh]
  rw [hSeq x hx]
  ring

end Volterra

end LiouvilleGreen
