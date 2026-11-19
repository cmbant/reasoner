/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LiouvilleGreenReal

/-!
# Liouville–Green expansions with error bounds (stage 3)

Following F. W. J. Olver, *Asymptotics and Special Functions*, Ch. 10, §3, we bound the error of
an arbitrary approximant and of truncated Liouville–Green series for

`w'' = (k² A⁻⁴ + g) w`   on `(a, ∞)`,   `E' = -k A⁻² E`.

Writing `w = A E u`, the factor `u` satisfies `A² u'' + 2 (A A' - k) u' + (A A'' - g A²) u = 0`.
If `P` is any twice differentiable approximant with residual `r` in this equation, there is a
solution `w = A E (P + ε)` with `‖ε x‖ ≤ κ W x exp (κ V x)`, `W x = ∫_{(x,∞)} ‖r‖`
(`LiouvilleGreen.exists_solution_of_approx`). For the truncated series
`P = ∑_{s<n} (-1)^s A_s / k^s` with `A_0` constant and the recursion
`(A² A_s')' + (A A'' - g A²) A_s = -2 A_{s+1}'`, the residual is `2 (-1)^n A_n' k^{1-n}`
(`LiouvilleGreen.approxResidual_lgSeries`), so the error is bounded by
`2 κ |k|^{1-n} V_{x,∞}(A_n) exp (κ V x)` (`LiouvilleGreen.exists_solution_expansion`); for
`k = u > 0` this is `u^{-n} V_{x,∞}(A_n) exp (V x/(2u))`, Olver's Ch. 10, Thm. 3.1 (the variable
here is the original `x` rather than the Liouville variable `ξ`).

## Main results

* `LiouvilleGreen.approxResidual`, `LiouvilleGreen.lgSeries`.
* `LiouvilleGreen.exists_solution_of_approx`.
* `LiouvilleGreen.approxResidual_lgSeries`, `LiouvilleGreen.exists_solution_expansion`.
* `LiouvilleGreen.exists_solution_expansion_exp`: the real exponential case `k = u > 0`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace LiouvilleGreen

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The residual of an approximant `P` in the transformed equation
`A² u'' + 2 (A A' - k) u' + (A A'' - g A²) u = 0` satisfied by `u = w / (A E)`. -/
noncomputable def approxResidual (k : 𝕜) (A A' A'' g P P' P'' : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  A t ^ 2 * P'' t + 2 * (A t * A' t - k) * P' t + (A t * A'' t - g t * A t ^ 2) * P t

/-- The transformed ODE residual is continuous whenever the approximant, amplitude and
their displayed derivatives are continuous. This regularity step is shared by the finite-
endpoint and infinite-endpoint Liouville-Green constructions. -/
lemma continuousOn_approxResidual {S : Set ℝ} {k : 𝕜} {A A' A'' g P P' P'' : ℝ → 𝕜}
    (hA : ContinuousOn A S) (hA' : ContinuousOn A' S) (hA'' : ContinuousOn A'' S)
    (hg : ContinuousOn g S) (hP : ContinuousOn P S) (hP' : ContinuousOn P' S)
    (hP'' : ContinuousOn P'' S) : ContinuousOn (approxResidual k A A' A'' g P P' P'') S :=
  (((hA.pow 2).mul hP'').add
    ((continuousOn_const.mul ((hA.mul hA').sub continuousOn_const)).mul hP')).add
      (((hA.mul hA'').sub (hg.mul (hA.pow 2))).mul hP)

/-- **Liouville–Green approximation with an arbitrary approximant.** In the setting of
`exists_solution_of_kernel_bound`, let `P` be twice differentiable on `(a, ∞)` and let
`r = A² P'' + 2 (A A' - k) P' + (A A'' - g A²) P` be its residual, with `‖r‖` integrable at
infinity. Then `w'' = (k² A⁻⁴ + g) w` has a solution `w = A E (P + ε)` on `(a, ∞)` with

`‖ε x‖ ≤ κ W x exp (κ V x)`,   `‖A(x)² ε'(x)‖ ≤ W x exp (κ V x)`,

where `W x = ∫_{(x,∞)} ‖r‖` and `V x = ∫_{(x,∞)} ‖A A'' - g A²‖`. With `P = 1` the residual is
`A A'' - g A²`; with `P` a truncated Liouville–Green series this yields the error bounds for the
asymptotic expansions of Olver, *Asymptotics and Special Functions*, Ch. 10, §3. -/
theorem exists_solution_of_approx {a κ : ℝ} {k : 𝕜} {A A' A'' E g P P' P'' : ℝ → 𝕜}
    (hk : k ≠ 0) (hκ : 0 < κ)
    (hA : ∀ x, a < x → A x ≠ 0)
    (hA' : ∀ x, a < x → HasDerivAt A (A' x) x)
    (hA'' : ∀ x, a < x → HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' (Ioi a)) (hgc : ContinuousOn g (Ioi a))
    (hE0 : ∀ x, a < x → E x ≠ 0)
    (hE : ∀ x, a < x → HasDerivAt E (-(k * (A x ^ 2)⁻¹ * E x)) x)
    (hEle : ∀ x t, a < x → x < t → ‖E t‖ ≤ ‖E x‖)
    (hK : ∀ x t, a < x → x < t → ‖(1 - E t ^ 2 / E x ^ 2) / (2 * k)‖ ≤ κ)
    (hFi : ∀ c, a < c → IntegrableOn (fun t => ‖A t * A'' t - g t * A t ^ 2‖) (Ioi c))
    (hP : ∀ x, a < x → HasDerivAt P (P' x) x) (hP' : ∀ x, a < x → HasDerivAt P' (P'' x) x)
    (hP''c : ContinuousOn P'' (Ioi a))
    (hri : ∀ c, a < c →
      IntegrableOn (fun t => ‖approxResidual k A A' A'' g P P' P'' t‖) (Ioi c)) :
    ∃ ε ε' w' : ℝ → 𝕜, ∀ x, a < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => A y * E y * (P y + ε y)) (w' x) x ∧
      HasDerivAt w' ((k ^ 2 * (A x ^ 4)⁻¹ + g x) * (A x * E x * (P x + ε x))) x ∧
      ‖ε x‖ ≤ κ * (∫ t in Ioi x, ‖approxResidual k A A' A'' g P P' P'' t‖) *
        Real.exp (κ * ∫ t in Ioi x, ‖A t * A'' t - g t * A t ^ 2‖) ∧
      ‖A x ^ 2 * ε' x‖ ≤ (∫ t in Ioi x, ‖approxResidual k A A' A'' g P P' P'' t‖) *
        Real.exp (κ * ∫ t in Ioi x, ‖A t * A'' t - g t * A t ^ 2‖) := by
  set F' : ℝ → 𝕜 := fun t => A t * A'' t - g t * A t ^ 2 with hF'
  set r : ℝ → 𝕜 := approxResidual k A A' A'' g P P' P'' with hr
  have hAc : ContinuousOn A (Ioi a) := fun x hx =>
    (hA' x hx).continuousAt.continuousWithinAt
  have hA'c : ContinuousOn A' (Ioi a) := fun x hx =>
    (hA'' x hx).continuousAt.continuousWithinAt
  have hPc : ContinuousOn P (Ioi a) := fun x hx =>
    (hP x hx).continuousAt.continuousWithinAt
  have hP'c : ContinuousOn P' (Ioi a) := fun x hx =>
    (hP' x hx).continuousAt.continuousWithinAt
  have hEc : ContinuousOn E (Ioi a) := fun x hx =>
    (hE x hx).continuousAt.continuousWithinAt
  have hF'c : ContinuousOn F' (Ioi a) := (hAc.mul hA''c).sub (hgc.mul (hAc.pow 2))
  have hrc : ContinuousOn r (Ioi a) :=
    continuousOn_approxResidual hAc hA'c hA''c hgc hPc hP'c hP''c

  have hint_of : ∀ {f : ℝ → 𝕜}, ContinuousOn f (Ioi a) →
      (∀ c, a < c → IntegrableOn (fun t => ‖f t‖) (Ioi c)) →
      ∀ c, a < c → IntegrableOn f (Ioi c) := fun {f} hfc hfi c hc =>
    (integrable_norm_iff ((hfc.mono (Ioi_subset_Ioi hc.le)).aestronglyMeasurable
      measurableSet_Ioi)).1 (hfi c hc)
  have hF'i := hint_of hF'c hFi
  have hri' := hint_of hrc hri
  have hE2 : ∀ {f : ℝ → 𝕜}, ContinuousOn f (Ioi a) →
      (∀ c, a < c → IntegrableOn (fun t => ‖f t‖) (Ioi c)) →
      ∀ c, a < c → IntegrableOn (fun t => E t ^ 2 * f t) (Ioi c) := by
    intro f hfc hfi c hc
    refine Integrable.mono' ((hfi c hc).const_mul (‖E c‖ ^ 2))
      (((hEc.pow 2).mul hfc).mono (Ioi_subset_Ioi hc.le) |>.aestronglyMeasurable
        measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [norm_mul, norm_pow]
    gcongr
    exact hEle c t hc ht
  have hp₂c : ContinuousOn (fun x => (2 * k)⁻¹ * (E x ^ 2)⁻¹) (Ioi a) :=
    continuousOn_const.mul ((hEc.pow 2).inv₀ fun x hx => pow_ne_zero 2 (hE0 x hx))
  have hKψ : ∀ {ψ : ℝ → 𝕜} (x t : ℝ), a < x → x < t →
      ‖(-(2 * k)⁻¹ * 1 + (2 * k)⁻¹ * (E x ^ 2)⁻¹ * E t ^ 2) * ψ t‖ ≤ κ * ‖ψ t‖ := by
    intro ψ x t hx hxt
    have heq : (-(2 * k)⁻¹ * 1 + (2 * k)⁻¹ * (E x ^ 2)⁻¹ * E t ^ 2) =
        -((1 - E t ^ 2 / E x ^ 2) / (2 * k)) := by ring
    rw [heq, norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_right (hK x t hx hxt) (norm_nonneg _)
  -- the forcing term
  have hρr0 : ∀ t, a < t → 0 ≤ κ * ‖r t‖ := fun t _ => by positivity
  have hσ := volterraOp_step (𝕜 := 𝕜)
    (p₁ := fun _ => -(2 * k)⁻¹) (q₁ := fun _ => 1)
    (p₂ := fun x => (2 * k)⁻¹ * (E x ^ 2)⁻¹) (q₂ := fun t => E t ^ 2) (ψ := r)
    (ρ := fun t => κ * ‖r t‖) (a := a) (B := fun _ => 1)
    aestronglyMeasurable_const (hp₂c.aestronglyMeasurable measurableSet_Ioi)
    (fun c hc => by simpa using hri' c hc) (hE2 hrc hri)
    (continuousOn_const.mul hrc.norm) (fun c hc => (hri c hc).const_mul κ)
    (fun x t hx hxt => hKψ x t hx hxt) (fun _ _ => zero_le_one) (fun _ _ _ _ => le_rfl)
    (φ := fun _ => 1) aestronglyMeasurable_const 0 (fun _ _ => by simp)
  simp only [one_mul, zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hσ
  set σ : ℝ → 𝕜 := volterraOp (fun _ => -(2 * k)⁻¹) (fun x => (2 * k)⁻¹ * (E x ^ 2)⁻¹)
    (fun _ => 1) (fun t => E t ^ 2) r (fun _ => 1) with hσdef
  set ρ : ℝ → ℝ := fun t => κ * ‖F' t‖ with hρ
  have hρc : ContinuousOn ρ (Ioi a) := continuousOn_const.mul hF'c.norm
  have hρi : ∀ c, a < c → IntegrableOn ρ (Ioi c) := fun c hc => (hFi c hc).const_mul κ
  have hρ0 : ∀ t, a < t → 0 ≤ ρ t := fun t _ => by positivity
  set B : ℝ → ℝ := fun x => ∫ t in Ioi x, κ * ‖r t‖ with hB
  have hBa : ∀ x t, a < x → x ≤ t → B t ≤ B x := fun x t hx hxt =>
    tail_anti hρr0 (fun c hc => (hri c hc).const_mul κ) hx hxt
  obtain ⟨h, hhm, hhb, hheq⟩ := exists_volterra_solution_add (𝕜 := 𝕜)
    (p₁ := fun _ => -(2 * k)⁻¹) (q₁ := fun _ => 1)
    (p₂ := fun x => (2 * k)⁻¹ * (E x ^ 2)⁻¹) (q₂ := fun t => E t ^ 2) (ψ := F')
    (ρ := ρ) (a := a) (σ := σ) (B := B)
    aestronglyMeasurable_const (hp₂c.aestronglyMeasurable measurableSet_Ioi)
    (fun c hc => by simpa using hF'i c hc) (hE2 hF'c hFi) hσ.2.2.1
    (fun t ht => hσ.2.2.2 t ht) hBa hρc hρi (fun x t hx hxt => hKψ x t hx hxt)
  set R : ℝ → ℝ := fun t => ∫ s in Ioi t, ρ s with hR
  have hRx : ∀ x, R x = κ * ∫ t in Ioi x, ‖F' t‖ := fun x => integral_const_mul _ _
  have hBx : ∀ x, B x = κ * ∫ t in Ioi x, ‖r t‖ := fun x => integral_const_mul _ _
  have hB0 : ∀ x, a < x → 0 ≤ B x := fun x hx =>
    tail_nonneg hρr0 hx.le
  have hhb' : ∀ t, a < t → ‖h t‖ ≤ B t * Real.exp (R t) := fun t ht => by
    have h1 := hhb t ht
    have h2 := hσ.2.2.2 t ht
    calc ‖h t‖ ≤ ‖σ t‖ + ‖h t - σ t‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ B t + B t * (Real.exp (R t) - 1) := add_le_add h2 h1
      _ = B t * Real.exp (R t) := by ring
  have hhbx : ∀ x, a < x → ∀ t ∈ Ioi x, ‖h t‖ ≤ B x * Real.exp (R x) := fun x hx t ht =>
    (hhb' t (hx.trans ht)).trans (mul_le_mul (hBa x t hx (le_of_lt ht))
      (Real.exp_le_exp.2 (tail_anti hρ0 hρi hx (le_of_lt ht))) (Real.exp_pos _).le
      (hB0 x hx))
  have hmulb : ∀ {q : ℝ → 𝕜}, (∀ c, a < c → IntegrableOn (fun t => q t * F' t) (Ioi c)) →
      ∀ c, a < c → IntegrableOn (fun t => q t * F' t * h t) (Ioi c) := by
    intro q hq c hc
    exact (hq c hc).mul_bdd (hhm.mono_measure (Measure.restrict_mono
      (Ioi_subset_Ioi hc.le) le_rfl)) (ae_restrict_of_forall_mem measurableSet_Ioi (hhbx c hc))
  have hJ₁i := hmulb (q := fun _ => 1) (fun c hc => by simpa using hF'i c hc)
  have hJ₂i := hmulb (hE2 hF'c hFi)
  have hI₁i : ∀ c, a < c → IntegrableOn (fun t => F' t * h t + r t) (Ioi c) := fun c hc =>
    ((hJ₁i c hc).add (hri' c hc)).congr_fun (fun t _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi
  have hI₂i : ∀ c, a < c → IntegrableOn (fun t => E t ^ 2 * (F' t * h t + r t)) (Ioi c) :=
    fun c hc => ((hJ₂i c hc).add (hE2 hrc hri c hc)).congr_fun
      (fun t _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi
  set I₁ : ℝ → 𝕜 := fun x => ∫ t in Ioi x, (F' t * h t + r t) with hI₁
  set I₂ : ℝ → 𝕜 := fun x => ∫ t in Ioi x, E t ^ 2 * (F' t * h t + r t) with hI₂
  have hheq' : ∀ x, a < x → h x = -(2 * k)⁻¹ * I₁ x + (2 * k)⁻¹ * (E x ^ 2)⁻¹ * I₂ x := by
    intro x hx
    have e1 : I₁ x = (∫ t in Ioi x, 1 * F' t * h t) + ∫ t in Ioi x, 1 * r t * 1 := by
      rw [← integral_add (hJ₁i x hx)
        ((hri' x hx).congr_fun (fun t _ => by simp) measurableSet_Ioi)]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)
    have e2 : I₂ x = (∫ t in Ioi x, E t ^ 2 * F' t * h t) + ∫ t in Ioi x, E t ^ 2 * r t * 1 := by
      rw [← integral_add (hJ₂i x hx)
        ((hE2 hrc hri x hx).congr_fun (fun t _ => by simp) measurableSet_Ioi)]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)
    rw [hheq x hx, hσdef, volterraOp, volterraOp, e1, e2]
    ring
  have hhc : ContinuousOn h (Ioi a) :=
    ((continuousOn_const.mul (continuousOn_integral_Ioi hI₁i)).add
      (hp₂c.mul (continuousOn_integral_Ioi hI₂i))).congr fun x hx => hheq' x hx
  have hI₁d : ∀ x, a < x → HasDerivAt I₁ (-(F' x * h x + r x)) x := fun x hx =>
    hasDerivAt_integral_Ioi hI₁i hx ((hF'c.mul hhc).add hrc |>.continuousAt
      (Ioi_mem_nhds hx))
  have hI₂d : ∀ x, a < x → HasDerivAt I₂ (-(E x ^ 2 * (F' x * h x + r x))) x := fun x hx =>
    hasDerivAt_integral_Ioi hI₂i hx ((hEc.pow 2).mul ((hF'c.mul hhc).add hrc) |>.continuousAt
      (Ioi_mem_nhds hx))
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
      (-(2 * (A x * A' x - k)) * ε' x / A x ^ 2 - (F' x * h x + r x) / A x ^ 2) x := by
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
  refine ⟨h, ε', fun y => E y * ((A' y - k * (A y)⁻¹) * (P y + h y) + A y * (P' y + ε' y)),
    fun x hx => ⟨hεd x hx, ?_, ?_, ?_, ?_⟩⟩
  · refine (((hA' x hx).mul (hE x hx)).mul ((hP x hx).add (hεd x hx))).congr_deriv ?_
    have := hA x hx
    simp only [Pi.mul_apply, Pi.add_apply]
    field_simp
    ring
  · refine ((hE x hx).mul ((((hA'' x hx).sub (((hA' x hx).inv (hA x hx)).const_mul k)).mul
      ((hP x hx).add (hεd x hx))).add ((hA' x hx).mul ((hP' x hx).add (hε'd x hx))))).congr_deriv
      ?_
    have := hA x hx
    rw [hr, approxResidual, hF']
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.inv_apply]
    field_simp
    ring
  · calc ‖h x‖ ≤ B x * Real.exp (R x) := hhb' x hx
      _ = _ := by rw [hBx, hRx]
  · rw [← hRx]
    have hεx : A x ^ 2 * ε' x =
        ∫ t in Ioi x, (E x ^ 2)⁻¹ * (E t ^ 2 * (F' t * h t + r t)) := by
      have := hA x hx
      rw [integral_const_mul, hε'def]
      field_simp
      rfl
    have hexpt := integral_Ioi_mul_exp_tail hρc hρ0 hρi hx
    have hEx : 0 < ‖E x‖ ^ 2 := by have := hE0 x hx; positivity
    have hWx : ∫ t in Ioi x, ‖r t‖ = κ⁻¹ * B x := by rw [hBx]; field_simp
    have hbint : IntegrableOn (fun t => κ⁻¹ * B x * (ρ t * Real.exp (R t)) + ‖r t‖) (Ioi x) :=
      (hexpt.1.const_mul _).add (hri x hx)
    calc ‖A x ^ 2 * ε' x‖
        = ‖∫ t in Ioi x, (E x ^ 2)⁻¹ * (E t ^ 2 * (F' t * h t + r t))‖ := by rw [hεx]
      _ ≤ ∫ t in Ioi x, (κ⁻¹ * B x * (ρ t * Real.exp (R t)) + ‖r t‖) := by
          refine norm_integral_le_of_norm_le hbint
            (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
          have hle : ‖E t‖ ^ 2 ≤ ‖E x‖ ^ 2 := by
            have := hEle x t hx ht
            gcongr
          have hht : ‖h t‖ ≤ B x * Real.exp (R t) :=
            (hhb' t (hx.trans ht)).trans (mul_le_mul_of_nonneg_right
              (hBa x t hx (le_of_lt ht)) (Real.exp_pos _).le)
          rw [norm_mul, norm_inv, norm_mul, norm_pow, norm_pow]
          calc (‖E x‖ ^ 2)⁻¹ * (‖E t‖ ^ 2 * ‖F' t * h t + r t‖)
              ≤ (‖E x‖ ^ 2)⁻¹ * (‖E x‖ ^ 2 * (‖F' t‖ * (B x * Real.exp (R t)) + ‖r t‖)) := by
                gcongr
                refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
                rw [norm_mul]
                gcongr
            _ = κ⁻¹ * B x * (ρ t * Real.exp (R t)) + ‖r t‖ := by
                have : ‖E x‖ ≠ 0 := norm_ne_zero_iff.2 (hE0 x hx)
                simp only [hρ]
                field_simp
      _ = (∫ t in Ioi x, ‖r t‖) * Real.exp (R x) := by
          rw [integral_add (hexpt.1.const_mul _) (hri x hx), integral_const_mul, hexpt.2, hWx]
          field_simp
          ring

/-! ### Liouville–Green expansions -/

/-- The truncated Liouville–Green series `∑_{s<n} (-1)^s c_s(y) / k^s`. -/
noncomputable def lgSeries (k : 𝕜) (c : ℕ → ℝ → 𝕜) (n : ℕ) (y : ℝ) : 𝕜 :=
  ∑ s ∈ Finset.range n, (-1) ^ s * c s y / k ^ s

/-- **The residual of a truncated Liouville–Green series.** If the coefficients `A_s` satisfy
the recursion `(A² A_s')' + F' A_s = -2 A_{s+1}'` (with `F' = A A'' - g A²`) for `s < n` and
`A_0` is constant, the residual of `∑_{s<n} (-1)^s A_s / k^s` is `2 (-1)^n A_n' k / k^n`. -/
theorem approxResidual_lgSeries {k : 𝕜} (hk : k ≠ 0) {A A' A'' g : ℝ → 𝕜}
    {As Ad Ad2 : ℕ → ℝ → 𝕜} {x : ℝ} (h0 : Ad 0 x = 0) {n : ℕ}
    (hrec : ∀ s < n, A x ^ 2 * Ad2 s x + 2 * A x * A' x * Ad s x +
      (A x * A'' x - g x * A x ^ 2) * As s x = -(2 * Ad (s + 1) x)) :
    approxResidual k A A' A'' g (lgSeries k As n) (lgSeries k Ad n) (lgSeries k Ad2 n) x =
      2 * (-1) ^ n * Ad n x * k / k ^ n := by
  induction n with
  | zero => simp [approxResidual, lgSeries, h0]
  | succ n ih =>
    have ih' := ih fun s hs => hrec s (Nat.lt_succ_of_lt hs)
    have hn := hrec n (Nat.lt_succ_self n)
    simp only [approxResidual, lgSeries, Finset.sum_range_succ] at ih' ⊢
    have hkk : k * k⁻¹ = 1 := mul_inv_cancel₀ hk
    rw [pow_succ, pow_succ]
    linear_combination ih' + ((-1) ^ n / k ^ n) * hn + 2 * (-1) ^ n * Ad (n + 1) x / k ^ n * hkk

/-- **Liouville–Green expansions with error bounds** (Olver, *Asymptotics and Special
Functions*, Ch. 10, §3, here in the original variable). In the setting of
`exists_solution_of_kernel_bound`, let `A_0, …, A_n` satisfy `A_0' = 0` and the recursion
`A² A_s'' + 2 A A' A_s' + (A A'' - g A²) A_s = -2 A_{s+1}'` for `s < n` (in the Liouville variable
`ξ`, `d/dξ = A² d/dx`, this is Olver's `2 A_{s+1}' = -A_s'' + ψ A_s`). Then
`w'' = (k² A⁻⁴ + g) w` has a solution

`w = A E (∑_{s<n} (-1)^s A_s / k^s + ε)`,   `‖ε x‖ ≤ 2 κ ‖k‖^{1-n} (∫_{(x,∞)} ‖A_n'‖) exp (κ V x)`,

with `V x = ∫_{(x,∞)} ‖A A'' - g A²‖`, and `‖A² ε'‖` satisfies the same bound without the factor
`κ`. For `k = u > 0` (`κ = 1/(2u)`) the error is `u^{-n} V_{x,∞}(A_n) exp (V x / (2u))`. -/
theorem exists_solution_expansion {a κ : ℝ} {k : 𝕜} {A A' A'' E g : ℝ → 𝕜}
    (hk : k ≠ 0) (hκ : 0 < κ)
    (hA : ∀ x, a < x → A x ≠ 0)
    (hA' : ∀ x, a < x → HasDerivAt A (A' x) x)
    (hA'' : ∀ x, a < x → HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' (Ioi a)) (hgc : ContinuousOn g (Ioi a))
    (hE0 : ∀ x, a < x → E x ≠ 0)
    (hE : ∀ x, a < x → HasDerivAt E (-(k * (A x ^ 2)⁻¹ * E x)) x)
    (hEle : ∀ x t, a < x → x < t → ‖E t‖ ≤ ‖E x‖)
    (hK : ∀ x t, a < x → x < t → ‖(1 - E t ^ 2 / E x ^ 2) / (2 * k)‖ ≤ κ)
    (hFi : ∀ c, a < c → IntegrableOn (fun t => ‖A t * A'' t - g t * A t ^ 2‖) (Ioi c))
    {n : ℕ} {As Ad Ad2 : ℕ → ℝ → 𝕜}
    (hAs : ∀ s < n, ∀ x, a < x → HasDerivAt (As s) (Ad s x) x)
    (hAd : ∀ s < n, ∀ x, a < x → HasDerivAt (Ad s) (Ad2 s x) x)
    (hAd2c : ∀ s < n, ContinuousOn (Ad2 s) (Ioi a))
    (h0 : ∀ x, a < x → Ad 0 x = 0)
    (hrec : ∀ s < n, ∀ x, a < x → A x ^ 2 * Ad2 s x + 2 * A x * A' x * Ad s x +
      (A x * A'' x - g x * A x ^ 2) * As s x = -(2 * Ad (s + 1) x))
    (hAni : ∀ c, a < c → IntegrableOn (fun t => ‖Ad n t‖) (Ioi c)) :
    ∃ ε ε' w' : ℝ → 𝕜, ∀ x, a < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => A y * E y * (lgSeries k As n y + ε y)) (w' x) x ∧
      HasDerivAt w' ((k ^ 2 * (A x ^ 4)⁻¹ + g x) * (A x * E x * (lgSeries k As n x + ε x))) x ∧
      ‖ε x‖ ≤ κ * (2 * ‖k‖ / ‖k‖ ^ n * ∫ t in Ioi x, ‖Ad n t‖) *
        Real.exp (κ * ∫ t in Ioi x, ‖A t * A'' t - g t * A t ^ 2‖) ∧
      ‖A x ^ 2 * ε' x‖ ≤ (2 * ‖k‖ / ‖k‖ ^ n * ∫ t in Ioi x, ‖Ad n t‖) *
        Real.exp (κ * ∫ t in Ioi x, ‖A t * A'' t - g t * A t ^ 2‖) := by
  have hser : ∀ {c d : ℕ → ℝ → 𝕜}, (∀ s < n, ∀ x, a < x → HasDerivAt (c s) (d s x) x) →
      ∀ x, a < x → HasDerivAt (lgSeries k c n) (lgSeries k d n x) x := by
    intro c d hcd x hx
    unfold lgSeries
    exact HasDerivAt.fun_sum fun s hs =>
      ((hcd s (Finset.mem_range.1 hs) x hx).const_mul _).div_const _
  have hres : ∀ t, a < t → ‖approxResidual k A A' A'' g (lgSeries k As n) (lgSeries k Ad n)
      (lgSeries k Ad2 n) t‖ = 2 * ‖k‖ / ‖k‖ ^ n * ‖Ad n t‖ := fun t ht => by
    rw [approxResidual_lgSeries hk (h0 t ht) (fun s hs => hrec s hs t ht)]
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
      RCLike.norm_ofNat]
    ring
  obtain ⟨ε, ε', w', H⟩ := exists_solution_of_approx hk hκ hA hA' hA'' hA''c hgc hE0 hE hEle hK hFi
    (hser hAs) (hser hAd)
    (by
      unfold lgSeries
      exact continuousOn_finsetSum _ fun s hs =>
        (continuousOn_const.mul (hAd2c s (Finset.mem_range.1 hs))).div_const _)
    (fun c hc => IntegrableOn.congr_fun ((hAni c hc).const_mul (2 * ‖k‖ / ‖k‖ ^ n))
      (fun t ht => (hres t (hc.trans ht)).symm) measurableSet_Ioi)
  refine ⟨ε, ε', w', fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H x hx
  have hW : ∫ t in Ioi x, ‖approxResidual k A A' A'' g (lgSeries k As n) (lgSeries k Ad n)
      (lgSeries k Ad2 n) t‖ = 2 * ‖k‖ / ‖k‖ ^ n * ∫ t in Ioi x, ‖Ad n t‖ := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hres t (hx.trans ht)
  rw [hW] at h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **Liouville–Green expansions, exponential case** (Olver, *Asymptotics and Special
Functions*, Ch. 10, Thm. 3.1, in the original variable). Under the hypotheses of
`exists_solution_exp`, let `A_0, …, A_n` satisfy `A_0' = 0` and the recursion
`A² A_s'' + 2 A A' A_s' + (A A'' - g A²) A_s = -2 A_{s+1}'` for `s < n`. Then for `u > 0` the
equation `w'' = (u² A⁻⁴ + g) w` has a solution
`w = A exp (-u ξ) (∑_{s<n} (-1)^s A_s / u^s + ε)` with

`|ε x| ≤ u^{-n} V_{x,∞}(A_n) exp (V x / (2u))`,
`|A² ε'| ≤ 2u · u^{-n} V_{x,∞}(A_n) exp (V x / (2u))`,

where `V_{x,∞}(A_n) = ∫_{(x,∞)} |A_n'|` and `V x = ∫_{(x,∞)} |A A'' - g A²|`. -/
theorem exists_solution_expansion_exp {a u : ℝ} (hu : 0 < u) {A A' A'' ξ g : ℝ → ℝ}
    (hA : ∀ x, a < x → A x ≠ 0)
    (hA' : ∀ x, a < x → HasDerivAt A (A' x) x)
    (hA'' : ∀ x, a < x → HasDerivAt A' (A'' x) x)
    (hA''c : ContinuousOn A'' (Ioi a)) (hgc : ContinuousOn g (Ioi a))
    (hξ : ∀ x, a < x → HasDerivAt ξ ((A x ^ 2)⁻¹) x)
    (hFi : ∀ c, a < c → IntegrableOn (fun t => |A t * A'' t - g t * A t ^ 2|) (Ioi c))
    {n : ℕ} {As Ad Ad2 : ℕ → ℝ → ℝ}
    (hAs : ∀ s < n, ∀ x, a < x → HasDerivAt (As s) (Ad s x) x)
    (hAd : ∀ s < n, ∀ x, a < x → HasDerivAt (Ad s) (Ad2 s x) x)
    (hAd2c : ∀ s < n, ContinuousOn (Ad2 s) (Ioi a))
    (h0 : ∀ x, a < x → Ad 0 x = 0)
    (hrec : ∀ s < n, ∀ x, a < x → A x ^ 2 * Ad2 s x + 2 * A x * A' x * Ad s x +
      (A x * A'' x - g x * A x ^ 2) * As s x = -(2 * Ad (s + 1) x))
    (hAni : ∀ c, a < c → IntegrableOn (fun t => |Ad n t|) (Ioi c)) :
    ∃ ε ε' w' : ℝ → ℝ, ∀ x, a < x →
      HasDerivAt ε (ε' x) x ∧
      HasDerivAt (fun y => A y * Real.exp (-(u * ξ y)) * (lgSeries u As n y + ε y)) (w' x) x ∧
      HasDerivAt w' ((u ^ 2 * (A x ^ 4)⁻¹ + g x) *
        (A x * Real.exp (-(u * ξ x)) * (lgSeries u As n x + ε x))) x ∧
      |ε x| ≤ (∫ t in Ioi x, |Ad n t|) / u ^ n *
        Real.exp ((∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2|) / (2 * u)) ∧
      |A x ^ 2 * ε' x| ≤ 2 * u * ((∫ t in Ioi x, |Ad n t|) / u ^ n) *
        Real.exp ((∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2|) / (2 * u)) := by
  obtain ⟨hE0, hE, hEle, hK⟩ := exp_kernel (a := a) hu hξ
  obtain ⟨ε, ε', w', H⟩ := exists_solution_expansion (𝕜 := ℝ) (a := a)
    (κ := 1 / (2 * u)) (k := u) (A := A) (A' := A') (A'' := A'')
    (E := fun y => Real.exp (-(u * ξ y))) (g := g)
    hu.ne' (by positivity) hA hA' hA'' hA''c hgc hE0 hE hEle hK
    (fun c hc => by simpa only [Real.norm_eq_abs] using hFi c hc) hAs hAd hAd2c h0 hrec
    (fun c hc => by simpa only [Real.norm_eq_abs] using hAni c hc)
  refine ⟨ε, ε', w', fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H x hx
  simp only [Real.norm_eq_abs, abs_of_pos hu] at h4 h5
  have hV : 1 / (2 * u) * ∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2| =
      (∫ t in Ioi x, |A t * A'' t - g t * A t ^ 2|) / (2 * u) := by ring
  rw [hV] at h4 h5
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · convert h4 using 2
    field_simp
  · convert h5 using 2
    field_simp

end LiouvilleGreen
