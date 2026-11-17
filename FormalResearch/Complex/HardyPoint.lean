module

public import FormalResearch.Complex.HardyArcDecay

/-!
# Pointwise bound and vanishing integral for `L¹`-boundary functions on the half-plane

Generic complex analysis, no Airy content.  **Proved.**  Let `G` be holomorphic on the open upper half-plane `ℍ`, continuous on
its closure, with `‖G z‖ ≤ C (1 + ‖z‖)^m` on `Im z ≥ 0` and `G|_ℝ ∈ L¹(ℝ)` (the hypotheses of `hardy_arc_le_poly`).

* `hardy_value_le`: `‖G(x + iy)‖ ≤ (1/(4π y)) ∫_ℝ ‖G‖` for every `y > 0` (the pointwise bound of `H¹(ℍ)`; the notes'
  Lemma H states the weaker constant `1/(π y)`, which is a corollary `hardy_value_le_pi`);
* `hardy_integral_zero`: `∫_ℝ G = 0` (the mean of an `H¹` boundary function vanishes).

Proof.  The Möbius map `φ(w) = (w + i)/(1 + i w)` of `D` onto `ℍ` (`HardyHalfPlane.hpPhi`) turns `G` into `h = (G ∘ φ) φ'` on `D`
(`hpTransport`).  Both statements are Cauchy's theorem on the unit circle for `h`, read through the change of variables
`φ(e^{i(2β - π/2)}) = tan β`, under which `h(w) · i w dθ` becomes `G(t) dt` *exactly* (no phase: `2 i w/(1 + i w)² = 1/(2cos²β)` there):
`∮_{|w|=1} h dw = ∫_ℝ G` (`integral_circle_hpTransport_complex`, the complex companion of the norm identity
`HardyHalfPlane.integral_circle_hpTransport`), hence `∫_ℝ G = 0`; and `h(0) = 2 G(i)` is the circle mean of `h`, so
`2 ‖G(i)‖ ≤ (2π)⁻¹ ∫_ℝ ‖G‖`.  A general `z = x + iy` is moved to `i` by `G ↦ y G(x + y ·)`, and polynomial growth is handled by
the damping `G (1 - iδz)^{-K}` of `HardyArcDecay`, as there.

Not formalised: the Poisson representation `G(z) = ∫ P_z g`, the horizontal bound `∫ ‖G(x + iy)‖ dx ≤ ‖g‖₁`, the improvement
`4π`-factorisation `H¹ = H²·H²` (the constant `1/(4π y)` here is already that sharp constant).
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace FormalResearch.Hardy

/-- The unit-circle integrand `(i w) h(w)` of the transported function is, in the real parameter `t = tan β`, exactly `G(t)/(2 cos² β)`. -/
lemma hpTransport_circle_mul (G : ℂ → ℂ) {β : ℝ} (hβ : β ∈ Ioo (-(π / 2)) (π / 2)) :
    (I * circleMap 0 1 (2 * β - π / 2)) • hpTransport G (circleMap 0 1 (2 * β - π / 2)) =
      ((1 / (2 * Real.cos β ^ 2) : ℝ) : ℂ) • G (Real.tan β : ℂ) := by
  have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo hβ
  have hcC : (Real.cos β : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold hpTransport
  rw [hpPhi_circle β hc.ne', circleMap_one_two_sub, smul_eq_mul, smul_eq_mul]
  have hs2 : (Real.sin (2 * β) : ℂ) = 2 * Real.sin β * Real.cos β := by
    rw [Real.sin_two_mul]; push_cast; ring
  have hc2 : (Real.cos (2 * β) : ℂ) = 2 * (Real.cos β) ^ 2 - 1 := by
    rw [Real.cos_two_mul]; push_cast; ring
  have hpy : (Real.sin β : ℂ) ^ 2 + (Real.cos β : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq β
  have hu : (Real.cos β : ℂ) + I * (Real.sin β : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hc.ne' this
  have hden : 1 + I * (((Real.sin (2 * β) : ℝ) : ℂ) - I * ((Real.cos (2 * β) : ℝ) : ℂ)) =
      2 * (Real.cos β : ℂ) * ((Real.cos β : ℂ) + I * (Real.sin β : ℂ)) := by
    rw [hs2, hc2]
    linear_combination (-(2 * (Real.cos β : ℂ) ^ 2 - 1)) * Complex.I_sq
  have hnum : I * (((Real.sin (2 * β) : ℝ) : ℂ) - I * ((Real.cos (2 * β) : ℝ) : ℂ)) =
      ((Real.cos β : ℂ) + I * (Real.sin β : ℂ)) ^ 2 := by
    rw [hs2, hc2]
    linear_combination (-(2 * (Real.cos β : ℂ) ^ 2 - 1 + (Real.sin β : ℂ) ^ 2)) * Complex.I_sq + hpy
  rw [hden, hnum]
  have h1 : (((1 / (2 * Real.cos β ^ 2) : ℝ)) : ℂ) = 1 / (2 * (Real.cos β : ℂ) ^ 2) := by
    push_cast; ring
  rw [h1]
  field_simp

/-- **Change of variables on the circle, complex form:** `∮_{|w|=1} h dw = ∫_ℝ G` for `h = hpTransport G`. -/
theorem integral_circle_hpTransport_complex (G : ℂ → ℂ) :
    ∫ θ in (-π)..π, (I * circleMap 0 1 θ) • hpTransport G (circleMap 0 1 θ) = ∫ t : ℝ, G (t : ℂ) := by
  set F : ℝ → ℂ := fun θ => (I * circleMap 0 1 θ) • hpTransport G (circleMap 0 1 θ) with hF
  have hper : Function.Periodic F (2 * π) := fun θ => by
    simp only [hF]; rw [periodic_circleMap]
  have h1 : ∫ θ in (-π)..π, F θ = ∫ θ in (-(3 * π / 2))..(π / 2), F θ := by
    have := hper.intervalIntegral_add_eq (-π) (-(3 * π / 2))
    convert this using 2 <;> ring
  have h2 : ∫ θ in (-(3 * π / 2))..(π / 2), F θ = (2 : ℝ) • ∫ β in (-(π / 2))..(π / 2), F (2 * β - π / 2) := by
    have := intervalIntegral.integral_comp_mul_sub (a := -(π / 2)) (b := π / 2) F (two_ne_zero) (π / 2)
    have e1 : (2 : ℝ) * -(π / 2) - π / 2 = -(3 * π / 2) := by ring
    have e2 : (2 : ℝ) * (π / 2) - π / 2 = π / 2 := by ring
    rw [e1, e2] at this
    rw [this, smul_smul]
    norm_num
  have h3 : ∫ β in (-(π / 2))..(π / 2), F (2 * β - π / 2) =
      ∫ β in Ioo (-(π / 2)) (π / 2), ((1 / (2 * Real.cos β ^ 2) : ℝ) : ℂ) • G (Real.tan β : ℂ) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun β hβ => ?_
    exact hpTransport_circle_mul G hβ
  have h4 : ∫ t : ℝ, G (t : ℂ) = ∫ β in Ioo (-(π / 2)) (π / 2), |1 / Real.cos β ^ 2| • G (Real.tan β : ℂ) := by
    have := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioo (-(π / 2)) (π / 2))
      (f := Real.tan) (f' := fun β => 1 / Real.cos β ^ 2) measurableSet_Ioo
      (fun β hβ => (Real.hasDerivAt_tan (Real.cos_pos_of_mem_Ioo hβ).ne').hasDerivWithinAt)
      Real.strictMonoOn_tan.injOn (fun t => G (t : ℂ))
    rw [Real.image_tan_Ioo, Measure.restrict_univ] at this
    exact this
  rw [h1, h2, h3, h4, ← MeasureTheory.integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioo fun β hβ => ?_
  have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo hβ
  show (2 : ℝ) • (((1 / (2 * Real.cos β ^ 2) : ℝ) : ℂ) • G (Real.tan β : ℂ)) = |1 / Real.cos β ^ 2| • G (Real.tan β : ℂ)
  rw [abs_of_pos (by positivity), Complex.real_smul, Complex.real_smul, smul_eq_mul, ← mul_assoc]
  congr 1
  push_cast
  field_simp

/-- Cauchy's theorem for the transported function: `∫_ℝ G = 0` for `G` with the decay `‖G z‖ (1+‖z‖)³ ≤ C`. -/
theorem hardy_integral_zero_decay {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {C : ℝ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ * (1 + ‖z‖) ^ 3 ≤ C) : ∫ t : ℝ, G (t : ℂ) = 0 := by
  have h0 := (hpTransport_diffContOnCl hG hC).circleIntegral_eq_zero (zero_le_one' ℝ)
  rw [circleIntegral] at h0
  set F : ℝ → ℂ := fun θ => (I * circleMap 0 1 θ) • hpTransport G (circleMap 0 1 θ) with hF
  have hper : Function.Periodic F (2 * π) := fun θ => by
    simp only [hF]; rw [periodic_circleMap]
  have h1 : ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 1) θ • hpTransport G (circleMap 0 1 θ) =
      ∫ θ in (0 : ℝ)..2 * π, F θ := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [hF, deriv_circleMap]
    rw [mul_comm]
  rw [h1] at h0
  have h2 : ∫ θ in (0 : ℝ)..2 * π, F θ = ∫ θ in (-π)..π, F θ := by
    have := hper.intervalIntegral_add_eq 0 (-π)
    convert this using 2 <;> ring
  rw [h2, integral_circle_hpTransport_complex] at h0
  exact h0

/-- **The mean of an `H¹` boundary function vanishes:** `∫_ℝ G = 0` under the hypotheses of `hardy_arc_le_poly`. -/
theorem hardy_integral_zero {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {C : ℝ} {m : ℕ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ C * (1 + ‖z‖) ^ m) (hint : Integrable (fun x : ℝ => G (x : ℂ))) :
    ∫ t : ℝ, G (t : ℂ) = 0 := by
  have hdamp : ∀ δ : ℝ, 0 < δ → ∫ t : ℝ, G (t : ℂ) * hpDamp δ (m + 3) (t : ℂ) = 0 := fun δ hδ =>
    hardy_integral_zero_decay (diffContOnCl_damp hG hδ.le (m + 3)) (fun z hz => norm_damp_decay hC hδ hz)
  have hlim := tendsto_integral_damp hG hint (m + 3)
  -- `‖∫ G‖ = ‖∫ (G - G·damp)‖ ≤ ∫ ‖G - G·damp‖ → 0`
  have hle : ∀ δ : ℝ, 0 < δ → ‖∫ t : ℝ, G (t : ℂ)‖ ≤
      ∫ x : ℝ, ‖G (x : ℂ) - G (x : ℂ) * hpDamp δ (m + 3) (x : ℂ)‖ := by
    intro δ hδ
    have hi2 := integrable_damp hG hδ.le (m + 3) hint
    have : ∫ t : ℝ, G (t : ℂ) = ∫ t : ℝ, (G (t : ℂ) - G (t : ℂ) * hpDamp δ (m + 3) (t : ℂ)) := by
      rw [integral_sub hint hi2, hdamp δ hδ, sub_zero]
    rw [this]
    exact norm_integral_le_integral_norm _
  have h0 : ‖∫ t : ℝ, G (t : ℂ)‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_of_mem self_mem_nhdsWithin fun δ hδ => hle δ hδ)
  exact norm_le_zero_iff.1 h0

/-- info: 'FormalResearch.Hardy.hardy_integral_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.hardy_integral_zero

/-- Value at `i`, decaying case: `‖G(i)‖ ≤ (4π)⁻¹ ∫_ℝ ‖G‖` (circle mean of `h = hpTransport G` at `0`, `h(0) = 2 G(i)`). -/
theorem hardy_value_i_decay {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {C : ℝ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ * (1 + ‖z‖) ^ 3 ≤ C) :
    ‖G I‖ ≤ (4 * π)⁻¹ * ∫ t : ℝ, ‖G (t : ℂ)‖ := by
  have hpi := Real.pi_pos
  have hdc := hpTransport_diffContOnCl hG hC
  have hmv : hpTransport G 0 = Real.circleAverage (hpTransport G) 0 1 := by
    have hdc' : DiffContOnCl ℂ (hpTransport G) (ball (0 : ℂ) |(1 : ℝ)|) := by rwa [abs_one]
    exact hdc'.circleAverage.symm
  have h0 : hpTransport G 0 = 2 * G I := by
    simp [hpTransport, hpPhi, mul_comm]
  set F : ℝ → ℝ := fun θ => ‖hpTransport G (circleMap 0 1 θ)‖ with hF
  have hper : Function.Periodic F (2 * π) := fun θ => by
    simp only [hF]; rw [periodic_circleMap]
  have h1 : ‖hpTransport G 0‖ ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, F θ := by
    rw [hmv, Real.circleAverage_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    gcongr
    exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
  have h2 : ∫ θ in (0 : ℝ)..2 * π, F θ = ∫ θ in (-π)..π, F θ := by
    have := hper.intervalIntegral_add_eq 0 (-π)
    convert this using 2 <;> ring
  rw [h2, integral_circle_hpTransport, h0, norm_mul] at h1
  have e2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e2] at h1
  have : (4 * π)⁻¹ * ∫ t : ℝ, ‖G (t : ℂ)‖ = ((2 * π)⁻¹ * ∫ t : ℝ, ‖G (t : ℂ)‖) / 2 := by
    field_simp; ring
  rw [this]
  linarith

/-- Value at `i`, polynomial growth (damping `G (1 - iδz)^{-(m+3)}` and `δ → 0`). -/
theorem hardy_value_i {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {C : ℝ} {m : ℕ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ C * (1 + ‖z‖) ^ m) (hint : Integrable (fun x : ℝ => G (x : ℂ))) :
    ‖G I‖ ≤ (4 * π)⁻¹ * ∫ t : ℝ, ‖G (t : ℂ)‖ := by
  have hmain : ∀ δ : ℝ, 0 < δ → ‖G I * hpDamp δ (m + 3) I‖ ≤ (4 * π)⁻¹ * ∫ t : ℝ, ‖G (t : ℂ)‖ := by
    intro δ hδ
    have h1 := hardy_value_i_decay (diffContOnCl_damp hG hδ.le (m + 3)) (fun z hz => norm_damp_decay hC hδ hz)
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine integral_mono_of_nonneg (Eventually.of_forall fun x : ℝ => norm_nonneg (G (x : ℂ) * hpDamp δ (m + 3) (x : ℂ)))
      hint.norm (Eventually.of_forall fun x : ℝ => ?_)
    show ‖G (x : ℂ) * hpDamp δ (m + 3) (x : ℂ)‖ ≤ ‖G (x : ℂ)‖
    have := norm_hpDamp_le_one hδ.le (m + 3) (show 0 ≤ (x : ℂ).im by simp)
    rw [norm_mul]
    calc ‖G (x : ℂ)‖ * ‖hpDamp δ (m + 3) (x : ℂ)‖ ≤ ‖G (x : ℂ)‖ * 1 := by gcongr
      _ = _ := mul_one _
  have hlim : Tendsto (fun δ : ℝ => ‖G I * hpDamp δ (m + 3) I‖) (𝓝[>] 0) (𝓝 ‖G I‖) := by
    have := ((tendsto_const_nhds (x := G I)).mul (tendsto_hpDamp_zero (m + 3) I)).norm
    simpa using this
  exact le_of_tendsto hlim (eventually_of_mem self_mem_nhdsWithin fun δ hδ => hmain δ hδ)

/-- Dilation and real translation `w ↦ a G(x + a w)` preserve holomorphy on `ℍ` and continuity on its closure. -/
lemma diffContOnCl_affine {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) (x : ℝ) {a : ℝ} (ha : 0 < a) :
    DiffContOnCl ℂ (fun z => (a : ℂ) * G ((x : ℂ) + (a : ℂ) * z)) {z : ℂ | 0 < z.im} := by
  have hmaps : ∀ z : ℂ, 0 < z.im → 0 < ((x : ℂ) + (a : ℂ) * z).im := fun z hz => by
    simp [Complex.mul_im, hz, ha]
  have hmaps' : ∀ z : ℂ, 0 ≤ z.im → 0 ≤ ((x : ℂ) + (a : ℂ) * z).im := fun z hz => by
    simp [Complex.mul_im]; positivity
  refine ⟨?_, ?_⟩
  · intro z hz
    have h1 : DifferentiableAt ℂ G ((x : ℂ) + (a : ℂ) * z) :=
      hG.1.differentiableAt (isOpen_im_pos.mem_nhds (hmaps z hz))
    exact ((differentiableAt_const _).mul (h1.comp z (by fun_prop))).differentiableWithinAt
  · rw [closure_setOfPred_lt_im]
    intro z hz
    have hz' : 0 ≤ z.im := hz
    have h1 : ContinuousWithinAt G {z : ℂ | 0 ≤ z.im} ((x : ℂ) + (a : ℂ) * z) := by
      have := hG.2 ((x : ℂ) + (a : ℂ) * z) (by rw [closure_setOfPred_lt_im]; exact hmaps' z hz')
      rwa [closure_setOfPred_lt_im] at this
    refine continuousWithinAt_const.mul ?_
    exact h1.comp (f := fun z : ℂ => (x : ℂ) + (a : ℂ) * z) (by fun_prop) (fun v hv => hmaps' v hv)

/-- **Pointwise bound of `H¹(ℍ)`.**  `G` holomorphic on `ℍ`, continuous on the closure, of polynomial growth, with `G|_ℝ ∈ L¹`:
`‖G(x + iy)‖ ≤ (1/(4π y)) ∫_ℝ ‖G‖` for every real `x` and `y > 0`. -/
theorem hardy_value_le {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {C : ℝ} {m : ℕ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ C * (1 + ‖z‖) ^ m) (hint : Integrable (fun x : ℝ => G (x : ℂ)))
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖G ((x : ℂ) + (y : ℂ) * I)‖ ≤ (4 * π * y)⁻¹ * ∫ t : ℝ, ‖G (t : ℂ)‖ := by
  have hpi := Real.pi_pos
  set Gp : ℂ → ℂ := fun z => (y : ℂ) * G ((x : ℂ) + (y : ℂ) * z) with hGp
  have hC0 : 0 ≤ C := by
    have := hC 0 (by simp)
    simp at this
    exact le_trans (norm_nonneg _) this
  have hgrow : ∀ z : ℂ, 0 ≤ z.im → ‖Gp z‖ ≤ (y * (C * (1 + |x| + y) ^ m)) * (1 + ‖z‖) ^ m := by
    intro z hz
    have him : 0 ≤ ((x : ℂ) + (y : ℂ) * z).im := by simp [Complex.mul_im]; positivity
    have h1 := hC _ him
    have h2 : 1 + ‖(x : ℂ) + (y : ℂ) * z‖ ≤ (1 + |x| + y) * (1 + ‖z‖) := by
      have : ‖(x : ℂ) + (y : ℂ) * z‖ ≤ |x| + y * ‖z‖ := by
        calc ‖(x : ℂ) + (y : ℂ) * z‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * z‖ := norm_add_le _ _
          _ = |x| + y * ‖z‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hy.le]
      nlinarith [norm_nonneg z, abs_nonneg x]
    show ‖(y : ℂ) * G ((x : ℂ) + (y : ℂ) * z)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy.le]
    calc y * ‖G ((x : ℂ) + (y : ℂ) * z)‖ ≤ y * (C * (1 + ‖(x : ℂ) + (y : ℂ) * z‖) ^ m) := by gcongr
      _ ≤ y * (C * ((1 + |x| + y) * (1 + ‖z‖)) ^ m) := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have hcast : ∀ t : ℝ, Gp (t : ℂ) = (y : ℂ) * G (((x + y * t : ℝ)) : ℂ) := fun t => by
    simp only [hGp]; push_cast; rfl
  have hint' : Integrable (fun t : ℝ => Gp (t : ℂ)) := by
    simp_rw [hcast]
    have h1 : Integrable (fun t : ℝ => G (((x + t : ℝ)) : ℂ)) := by
      simpa using hint.comp_add_left x
    have h2 : Integrable (fun t : ℝ => G (((x + y * t : ℝ)) : ℂ)) := by
      have := h1.comp_mul_left' hy.ne'
      simpa using this
    exact h2.const_mul _
  have hnorm : ∫ t : ℝ, ‖Gp (t : ℂ)‖ = ∫ t : ℝ, ‖G (t : ℂ)‖ := by
    have e : ∀ t : ℝ, ‖Gp (t : ℂ)‖ = y * ‖G (((x + y * t : ℝ)) : ℂ)‖ := fun t => by
      rw [hcast, norm_mul, Complex.norm_real, Real.norm_of_nonneg hy.le]
    simp_rw [e]
    rw [MeasureTheory.integral_const_mul]
    have h1 := MeasureTheory.Measure.integral_comp_mul_left (fun t : ℝ => ‖G (((x + t : ℝ)) : ℂ)‖) y
    have h2 : ∫ t : ℝ, ‖G (((x + t : ℝ)) : ℂ)‖ = ∫ t : ℝ, ‖G (t : ℂ)‖ := by
      simpa using MeasureTheory.integral_add_left_eq_self (fun t : ℝ => ‖G (t : ℂ)‖) x
    rw [h2] at h1
    rw [h1, abs_of_pos (inv_pos.2 hy), smul_eq_mul]
    field_simp
  have key : ‖Gp I‖ ≤ (4 * π)⁻¹ * ∫ t : ℝ, ‖Gp (t : ℂ)‖ :=
    hardy_value_i (diffContOnCl_affine hG x hy) hgrow hint'
  have hGpI : Gp I = (y : ℂ) * G ((x : ℂ) + (y : ℂ) * I) := rfl
  rw [hGpI, hnorm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hy.le] at key
  have : (4 * π * y)⁻¹ * ∫ t : ℝ, ‖G (t : ℂ)‖ = (y)⁻¹ * ((4 * π)⁻¹ * ∫ t : ℝ, ‖G (t : ℂ)‖) := by
    field_simp
  rw [this]
  rw [inv_mul_eq_div, le_div_iff₀ hy]
  linarith

/-- The constant `1/(π y)` of the notes' Lemma H. -/
theorem hardy_value_le_pi {G : ℂ → ℂ} (hG : DiffContOnCl ℂ G {z : ℂ | 0 < z.im}) {C : ℝ} {m : ℕ}
    (hC : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ C * (1 + ‖z‖) ^ m) (hint : Integrable (fun x : ℝ => G (x : ℂ)))
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖G ((x : ℂ) + (y : ℂ) * I)‖ ≤ (π * y)⁻¹ * ∫ t : ℝ, ‖G (t : ℂ)‖ := by
  have h := hardy_value_le hG hC hint x hy
  refine h.trans ?_
  have hI : 0 ≤ ∫ t : ℝ, ‖G (t : ℂ)‖ := integral_nonneg fun t => norm_nonneg _
  have hpi := Real.pi_pos
  gcongr
  nlinarith [mul_pos hpi hy]

/-- info: 'FormalResearch.Hardy.hardy_value_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.hardy_value_le

end FormalResearch.Hardy
