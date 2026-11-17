module

public import FormalResearch.Special.AiryPwsClass

/-!
# Contour deformation in `s = √u`

For `f ∈ G` and `ζ = ξ + iη` (`η ≥ 0`) put `G_ζ(s) = f(s²) e^{-iζs²} 2s`, an entire function of `s`.  On the real ray
`G_ζ(x) dx = f(u) e^{-iζu} du` (`u = x²`) and on the imaginary ray `G_ζ(iy) i dy = -2y f(-y²) e^{iζy²} dy`
(`u = -y²`).  The rectangle `[0,R] × [0,b]` (Cauchy–Goursat, `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`)
moves the real ray to the line `Im s = b` (`airyPwsG_rect`).  With `b = -Re ζ/2 ≥ 0` the two pieces on the imaginary
axis between `0` and `b` cancel, which leaves

`f̂(ζ) = ∫_0^∞ G_ζ(t + ib) dt + ∫_b^∞ 2y f(-y²) e^{iζy²} dy`     (`airyFhat_eq_hor_add_vert`),

under two hypotheses which are verified in `AiryPwsGrowth` from the growth bound of `f`: integrability of
`t ↦ G_ζ(t+ib)` on `(0,∞)` and `∫_0^b G_ζ(R+iy) dy → 0` as `R → ∞`.

This is the contour deformation `i∞ → 0 → +∞  ⇝  i∞ → ib → ib + ∞` of the proof of Theorem 3.1 `(a)⇒(b)` in
`CFT/notes/general_theorems.tex` §3.  **Not formalised** here: the estimates of the two pieces (`AiryPwsGrowth`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set intervalIntegral
open scoped Real

namespace FormalResearch.Special

/-- `G_ζ(s) = f(s²) e^{-iζs²} 2s`. -/
noncomputable def airyPwsG (f : ℂ → ℂ) (ζ s : ℂ) : ℂ := f (s ^ 2) * cexp (-(I * ζ * s ^ 2)) * (2 * s)

lemma differentiable_airyPwsG {f : ℂ → ℂ} (hf : Differentiable ℂ f) (ζ : ℂ) :
    Differentiable ℂ (airyPwsG f ζ) := by
  unfold airyPwsG
  fun_prop

/-- The integrand of `f̂`. -/
noncomputable def airyJ (f : ℂ → ℂ) (ζ : ℂ) (u : ℝ) : ℂ := f (u : ℂ) * cexp (-(I * ζ * (u : ℂ)))

lemma integrable_airyJ {f : ℂ → ℂ} (hf : AiryClassG f) {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    Integrable (airyJ f ζ) := by
  obtain ⟨C, N, hC, hb⟩ := hf.bound
  refine (integrable_airyPwsDom hf (C := C) (N := N) 1 ζ.im).mono'
    (continuous_airyIntegrand hf ζ).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  exact airyPws_norm_integrand_le' hC hb ζ hζ le_rfl u

/-! ### The Cauchy rectangle -/

lemma airyPwsG_rect {f : ℂ → ℂ} (hf : Differentiable ℂ f) (ζ : ℂ) (R b : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..R, airyPwsG f ζ (x : ℂ)) - (∫ x : ℝ in (0 : ℝ)..R, airyPwsG f ζ (x + b * I)) +
      I • (∫ y : ℝ in (0 : ℝ)..b, airyPwsG f ζ (R + y * I)) -
      I • (∫ y : ℝ in (0 : ℝ)..b, airyPwsG f ζ (y * I)) = 0 := by
  have h := integral_boundary_rect_eq_zero_of_differentiableOn (airyPwsG f ζ) 0 ((R : ℂ) + b * I)
    (differentiable_airyPwsG hf ζ).differentiableOn
  simpa using h

/-! ### Changes of variables `u = x²`, `u = -y²` -/

lemma airyPws_image_sq_Ioi : (fun x : ℝ => x ^ 2) '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact pow_pos hx 2
  · intro hu
    exact ⟨√u, Real.sqrt_pos.mpr hu, Real.sq_sqrt (le_of_lt hu)⟩

lemma airyPws_image_neg_sq_Ioi : (fun x : ℝ => -x ^ 2) '' Ioi 0 = Iio 0 := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using pow_pos hx 2
  · intro hu
    have hu' : 0 < -u := neg_pos.mpr hu
    exact ⟨√(-u), Real.sqrt_pos.mpr hu', by show -(√(-u)) ^ 2 = u; rw [Real.sq_sqrt (le_of_lt hu')]; ring⟩

lemma airyPws_injOn_sq_Ioi : InjOn (fun x : ℝ => x ^ 2) (Ioi 0) := by
  intro x hx y hy h
  exact (sq_eq_sq₀ (le_of_lt hx) (le_of_lt hy)).mp h

lemma airyPws_injOn_neg_sq_Ioi : InjOn (fun x : ℝ => -x ^ 2) (Ioi 0) := by
  intro x hx y hy h
  have : x ^ 2 = y ^ 2 := by simpa using h
  exact (sq_eq_sq₀ (le_of_lt hx) (le_of_lt hy)).mp this

/-- `∫_{u>0} g(u) du = ∫_{x>0} 2x g(x²) dx`. -/
lemma airyPws_integral_Ioi_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ u in Ioi 0, g u = ∫ x in Ioi 0, (2 * x) • g (x ^ 2) := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun x : ℝ => x ^ 2) (f' := fun x => 2 * x)
    (measurableSet_Ioi (a := (0 : ℝ))) (fun x _ => by
      have := (hasDerivAt_pow 2 x).hasDerivWithinAt (s := Ioi 0)
      simpa using this) airyPws_injOn_sq_Ioi g
  rw [airyPws_image_sq_Ioi] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  show |2 * x| • g (x ^ 2) = (2 * x) • g (x ^ 2)
  rw [abs_of_pos (by have : 0 < x := hx; positivity)]

/-- `∫_{u<0} g(u) du = ∫_{y>0} 2y g(-y²) dy`. -/
lemma airyPws_integral_Iio_neg_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ u in Iio 0, g u = ∫ y in Ioi 0, (2 * y) • g (-y ^ 2) := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun x : ℝ => -x ^ 2) (f' := fun x => -(2 * x))
    (measurableSet_Ioi (a := (0 : ℝ))) (fun x _ => by
      have := ((hasDerivAt_pow 2 x).const_mul (-1 : ℝ)).hasDerivWithinAt (s := Ioi 0)
      simpa using this) airyPws_injOn_neg_sq_Ioi g
  rw [airyPws_image_neg_sq_Ioi] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  show |-(2 * x)| • g (-x ^ 2) = (2 * x) • g (-x ^ 2)
  rw [abs_neg, abs_of_pos (by have : 0 < x := hx; positivity)]

lemma airyPws_integrableOn_Ioi_sq_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    IntegrableOn g (Ioi 0) ↔ IntegrableOn (fun x => (2 * x) • g (x ^ 2)) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := fun x : ℝ => x ^ 2)
    (f' := fun x => 2 * x) (measurableSet_Ioi (a := (0 : ℝ))) (fun x _ => by
      have := (hasDerivAt_pow 2 x).hasDerivWithinAt (s := Ioi 0)
      simpa using this) airyPws_injOn_sq_Ioi g
  rw [airyPws_image_sq_Ioi] at h
  rw [h]
  refine integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioi
  show |2 * x| • g (x ^ 2) = (2 * x) • g (x ^ 2)
  rw [abs_of_pos (by have : 0 < x := hx; positivity)]

lemma airyPws_integrableOn_Iio_neg_sq_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    IntegrableOn g (Iio 0) ↔ IntegrableOn (fun x => (2 * x) • g (-x ^ 2)) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := fun x : ℝ => -x ^ 2)
    (f' := fun x => -(2 * x)) (measurableSet_Ioi (a := (0 : ℝ))) (fun x _ => by
      have := ((hasDerivAt_pow 2 x).const_mul (-1 : ℝ)).hasDerivWithinAt (s := Ioi 0)
      simpa using this) airyPws_injOn_neg_sq_Ioi g
  rw [airyPws_image_neg_sq_Ioi] at h
  rw [h]
  refine integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioi
  show |-(2 * x)| • g (-x ^ 2) = (2 * x) • g (-x ^ 2)
  rw [abs_neg, abs_of_pos (by have : 0 < x := hx; positivity)]

lemma airyPwsG_real (f : ℂ → ℂ) (ζ : ℂ) (x : ℝ) :
    airyPwsG f ζ (x : ℂ) = ((2 * x : ℝ)) • airyJ f ζ (x ^ 2) := by
  unfold airyPwsG airyJ
  rw [Complex.real_smul]
  push_cast
  ring

lemma airyPwsG_imag (f : ℂ → ℂ) (ζ : ℂ) (y : ℝ) :
    airyPwsG f ζ ((y : ℂ) * I) = (((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)) * I := by
  unfold airyPwsG airyJ
  rw [Complex.real_smul]
  have h : ((y : ℂ) * I) ^ 2 = -((y : ℂ) ^ 2) := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [h]
  push_cast
  ring

/-- **Contour deformation** (the integrals over the imaginary segment `[0, ib]` cancel). -/
theorem airyFhat_eq_hor_add_vert {f : ℂ → ℂ} (hf : AiryClassG f) {ζ : ℂ} (hζ : 0 ≤ ζ.im) {b : ℝ}
    (hb : 0 ≤ b)
    (hhor : IntegrableOn (fun t : ℝ => airyPwsG f ζ ((t : ℂ) + b * I)) (Ioi 0))
    (hvert : Tendsto (fun R : ℝ => ∫ y in (0 : ℝ)..b, airyPwsG f ζ ((R : ℂ) + y * I)) atTop (𝓝 0)) :
    airyFhat f ζ = (∫ t in Ioi (0 : ℝ), airyPwsG f ζ ((t : ℂ) + b * I)) +
      ∫ y in Ioi b, ((2 * y : ℝ)) • airyJ f ζ (-y ^ 2) := by
  have hJ := integrable_airyJ hf hζ
  have hsplit : airyFhat f ζ = (∫ u in Iio (0 : ℝ), airyJ f ζ u) + ∫ u in Ioi (0 : ℝ), airyJ f ζ u := by
    unfold airyFhat
    have := integral_add_compl (μ := volume) (measurableSet_Iio (a := (0 : ℝ))) hJ
    rw [compl_Iio, integral_Ici_eq_integral_Ioi] at this
    exact this.symm
  -- the three pieces
  set g : ℝ → ℂ := fun y => ((2 * y : ℝ)) • airyJ f ζ (-y ^ 2) with hg
  have hB : ∫ u in Iio (0 : ℝ), airyJ f ζ u = ∫ y in Ioi (0 : ℝ), g y := airyPws_integral_Iio_neg_sq _
  have hgint : IntegrableOn g (Ioi 0) := (airyPws_integrableOn_Iio_neg_sq_iff _).mp hJ.integrableOn
  have hA : ∫ u in Ioi (0 : ℝ), airyJ f ζ u = ∫ x in Ioi (0 : ℝ), airyPwsG f ζ (x : ℂ) := by
    rw [airyPws_integral_Ioi_sq]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [airyPwsG_real]
  have hGint : IntegrableOn (fun x : ℝ => airyPwsG f ζ (x : ℂ)) (Ioi 0) := by
    have := (airyPws_integrableOn_Ioi_sq_iff _).mp hJ.integrableOn
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [airyPwsG_real]
  -- the limit of the rectangle identity
  have hlim1 : Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, airyPwsG f ζ (x : ℂ)) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), airyPwsG f ζ (x : ℂ))) :=
    intervalIntegral_tendsto_integral_Ioi 0 hGint tendsto_id
  have hlim2 : Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, airyPwsG f ζ ((x : ℂ) + b * I)) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), airyPwsG f ζ ((x : ℂ) + b * I))) :=
    intervalIntegral_tendsto_integral_Ioi 0 hhor tendsto_id
  set W : ℂ := ∫ y in (0 : ℝ)..b, airyPwsG f ζ ((y : ℂ) * I) with hW
  have hlim3 : Tendsto (fun R : ℝ => (∫ x in (0 : ℝ)..R, airyPwsG f ζ ((x : ℂ) + b * I)) -
        I • (∫ y in (0 : ℝ)..b, airyPwsG f ζ ((R : ℂ) + y * I)) + I • W) atTop
      (𝓝 ((∫ x in Ioi (0 : ℝ), airyPwsG f ζ ((x : ℂ) + b * I)) - I • (0 : ℂ) + I • W)) :=
    (hlim2.sub (hvert.const_smul I)).add_const _
  have heq : ∀ R : ℝ, (∫ x in (0 : ℝ)..R, airyPwsG f ζ (x : ℂ)) =
      (∫ x in (0 : ℝ)..R, airyPwsG f ζ ((x : ℂ) + b * I)) -
        I • (∫ y in (0 : ℝ)..b, airyPwsG f ζ ((R : ℂ) + y * I)) + I • W := by
    intro R
    have := airyPwsG_rect hf.differentiable ζ R b
    rw [hW]
    linear_combination this
  have hAH : (∫ x in Ioi (0 : ℝ), airyPwsG f ζ (x : ℂ)) =
      (∫ x in Ioi (0 : ℝ), airyPwsG f ζ ((x : ℂ) + b * I)) - I • (0 : ℂ) + I • W := by
    refine tendsto_nhds_unique hlim1 (hlim3.congr fun R => (heq R).symm)
  -- the imaginary segment
  have hIW : I • W = -∫ y in (0 : ℝ)..b, g y := by
    rw [hW]
    have : ∀ y : ℝ, airyPwsG f ζ ((y : ℂ) * I) = g y * I := fun y => airyPwsG_imag f ζ y
    simp_rw [this]
    rw [intervalIntegral.integral_mul_const, smul_eq_mul]
    have : (∫ y in (0 : ℝ)..b, g y) * I * I = -∫ y in (0 : ℝ)..b, g y := by
      rw [mul_assoc, ← sq, Complex.I_sq]; ring
    rw [mul_comm I, this]
  -- split `∫_{y>0} g = ∫_0^b g + ∫_{y>b} g`
  have hsplit2 : ∫ y in Ioi (0 : ℝ), g y = (∫ y in (0 : ℝ)..b, g y) + ∫ y in Ioi b, g y := by
    rw [intervalIntegral.integral_of_le hb, ← Set.Ioc_union_Ioi_eq_Ioi hb]
    refine setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hgint.mono_set Set.Ioc_subset_Ioi_self) (hgint.mono_set ?_)
    exact Set.Ioi_subset_Ioi hb
  rw [hsplit, hB, hA, hAH, hIW, hsplit2]
  simp only [smul_zero, sub_zero]
  ring

/-- info: 'FormalResearch.Special.airyFhat_eq_hor_add_vert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyFhat_eq_hor_add_vert

end FormalResearch.Special
