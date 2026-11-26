module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroXb

/-!
# Cauchy on the strip for `Ψ̂`: the integral identity of Piece 3 (FIVE-0)

Edge values of `Ψ̂` are explicit in `x_T`, `v_T`; `strip_edge_integral_eq` (with the bound of `VirasoroXb`) gives
`∫_ℝ [1/(x_T √(c(1+c))) + v_T/(√2 √c (v_T²+¼) sinh(πτ/2))] dτ = 2π - 2√2`, `c = cosh πτ`.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `1/(x √(c(1+c)))`, `c = cosh πτ`. -/
noncomputable def xA (τ : ℝ) : ℝ := 1 / (xT τ * √(Real.cosh (π * τ) * (1 + Real.cosh (π * τ))))

/-- `v/(√2 √c (v²+¼) sinh(πτ/2))`. -/
noncomputable def vA (τ : ℝ) : ℝ :=
  vT τ / (√2 * √(Real.cosh (π * τ)) * (vT τ ^ 2 + 1 / 4) * Real.sinh (π * τ / 2))

noncomputable def fL (τ : ℝ) : ℝ := -xA τ + π / Real.cosh (π * τ) - √2 / Real.cosh (π * τ / 2)

noncomputable def fR (τ : ℝ) : ℝ := vA τ - π / Real.cosh (π * τ)

noncomputable def psiOneR (g k c : ℝ) : ℝ := -π * (1 / (√2 * k * g) - 1) / c - √2 / k

lemma psiOne_ofReal (g k c : ℝ) : psiOne (g : ℂ) (k : ℂ) (c : ℂ) = ((psiOneR g k c : ℝ) : ℂ) := by
  unfold psiOne psiOneR; push_cast; ring

lemma psiTil_left_eq {τ : ℝ} (hτ : τ ≠ 0) : psiTil ((τ : ℂ) * Complex.I) = ((fL τ : ℝ) : ℂ) := by
  rw [psiTil_left hτ]
  have hc : 0 < Real.cosh (π * τ) := Real.cosh_pos _
  rw [sInt_pos_real hc, psiOne_ofReal]
  congr 1
  unfold psiOneR fL xA
  set c := Real.cosh (π * τ) with hcdef
  set ch := Real.cosh (π * τ / 2) with hch
  have hchpos : 0 < ch := Real.cosh_pos _
  have hq : 0 < √c := Real.sqrt_pos.mpr hc
  have hqq : √c * √c = c := Real.mul_self_sqrt hc.le
  have hp : 0 < √(1 + c) := Real.sqrt_pos.mpr (by linarith)
  have hpp : √(1 + c) * √(1 + c) = 1 + c := Real.mul_self_sqrt (by linarith)
  have hc2 : c = 2 * ch ^ 2 - 1 := by
    have h2 : Real.cosh (π * τ) = Real.cosh (2 * (π * τ / 2)) := by congr 1; ring
    have h3 := Real.cosh_sq (π * τ / 2)
    rw [hcdef, hch, h2, Real.cosh_two_mul]; nlinarith
  have hpe : √(1 + c) = √2 * ch := by
    have : 1 + c = (√2 * ch) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; rw [hc2]; ring
    rw [this, Real.sqrt_sq (by positivity)]
  have hx : xT τ = Real.arsinh (√c) / π := rfl
  have hxpos : 0 < xT τ := xT_pos τ
  have hsq : √(c * (1 + c)) = √c * √(1 + c) := Real.sqrt_mul hc.le _
  rw [hsq, hpe, hx]
  have hpi := Real.pi_pos
  have ha : 0 < Real.arsinh (√c) := Real.arsinh_pos_iff.mpr hq
  have h2 : 0 < √2 := by positivity
  field_simp
  linear_combination (-π) * hqq

/-! ### `∫ sech` -/

lemma tendsto_sinh_atTop' : Tendsto Real.sinh atTop atTop :=
  tendsto_atTop_mono' atTop ((Filter.eventually_ge_atTop (0 : ℝ)).mono fun _ hx =>
    Real.self_le_sinh_iff.mpr hx) tendsto_id

lemma tendsto_sinh_atBot' : Tendsto Real.sinh atBot atBot :=
  tendsto_atBot_mono' atBot ((Filter.eventually_le_atBot (0 : ℝ)).mono fun _ hx =>
    Real.sinh_le_self_iff.mpr hx) tendsto_id

lemma continuous_sech {a : ℝ} : Continuous fun τ : ℝ => 1 / Real.cosh (a * τ) :=
  continuous_const.div (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
    (fun _ => (Real.cosh_pos _).ne')

lemma sech_le {a : ℝ} (τ : ℝ) : 1 / Real.cosh (a * τ) ≤ 2 * Real.exp (-(|a| * |τ|)) := by
  have h1 : Real.cosh (a * τ) = Real.cosh (|a| * |τ|) := by
    rw [← abs_mul, Real.cosh_abs]
  rw [h1, Real.cosh_eq]
  have hp := Real.exp_pos (|a| * |τ|)
  have hn := Real.exp_pos (-(|a| * |τ|))
  have : Real.exp (|a| * |τ|) * Real.exp (-(|a| * |τ|)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma integrable_sech {a : ℝ} (ha : 0 < a) : Integrable fun τ : ℝ => 1 / Real.cosh (a * τ) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_abs ha).const_mul 2)
    continuous_sech.aestronglyMeasurable (Filter.Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (by have := Real.cosh_pos (a * τ); positivity)]
  have := sech_le (a := a) τ
  rwa [abs_of_pos ha] at this

lemma integral_sech {a : ℝ} (ha : 0 < a) : ∫ τ : ℝ, 1 / Real.cosh (a * τ) = π / a := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => Real.arctan (Real.sinh (a * x)) / a)
      (1 / Real.cosh (a * x)) x := by
    intro x
    have h1 : HasDerivAt (fun x => Real.sinh (a * x)) (Real.cosh (a * x) * (a * 1)) x :=
      (Real.hasDerivAt_sinh (a * x)).comp x ((hasDerivAt_id x).const_mul a)
    have h2 := ((Real.hasDerivAt_arctan (Real.sinh (a * x))).comp x h1).div_const a
    refine h2.congr_deriv ?_
    have hc := Real.cosh_pos (a * x)
    have h3 : 1 + Real.sinh (a * x) ^ 2 = Real.cosh (a * x) ^ 2 := by
      linarith [Real.cosh_sq (a * x)]
    rw [h3]
    field_simp
  have hb : Tendsto (fun x : ℝ => Real.arctan (Real.sinh (a * x)) / a) atBot (𝓝 (-(π / 2) / a)) :=
    ((Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (tendsto_sinh_atBot'.comp (tendsto_id.const_mul_atBot ha))).div_const a
  have ht : Tendsto (fun x : ℝ => Real.arctan (Real.sinh (a * x)) / a) atTop (𝓝 ((π / 2) / a)) :=
    ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_sinh_atTop'.comp (tendsto_id.const_mul_atTop ha))).div_const a
  rw [integral_of_hasDerivAt_of_tendsto hd (integrable_sech ha) hb ht]
  field_simp
  ring

lemma right_aux (r σ v : ℝ) (hr : 0 < r) (hσ : σ ≠ 0) :
    psiOne (((π / r : ℝ) : ℂ) * (1 / 2 + Complex.I * (v : ℂ))) (-(Complex.I * (σ : ℂ)))
      (-((r * r : ℝ) : ℂ)) =
    ((v / (√2 * r * (v ^ 2 + 1 / 4) * σ) - π / (r * r) : ℝ) : ℂ) +
      Complex.I * ((r / (2 * √2 * (r * r) * σ * (v ^ 2 + 1 / 4)) - √2 / σ : ℝ) : ℂ) := by
  unfold psiOne
  have hI := Complex.I_sq
  have h2 : ((√2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < √2 := by positivity
    exact_mod_cast this.ne'
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hσ' : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hv : ((v : ℂ) ^ 2 + 1 / 4) ≠ 0 := by
    have h : ((v : ℂ) ^ 2 + 1 / 4) = ((v ^ 2 + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [h]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hv4 : ((v : ℂ) ^ 2 * 4 + 1) ≠ 0 := by
    intro h; apply hv; linear_combination h / 4
  have hl : (1 / 2 + Complex.I * (v : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hl4 : (1 + Complex.I * 2 * (v : ℂ)) ≠ 0 := by
    intro h; apply hl; linear_combination h / 2
  have h22 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI]; ring
  push_cast
  field_simp
  rw [h22]
  ring_nf
  simp only [hI, hI3]
  ring_nf

lemma psiTil_right_re {τ : ℝ} (hτ : τ ≠ 0) : (psiTil (1 + (τ : ℂ) * Complex.I)).re = fR τ := by
  have hc : 0 < Real.cosh (π * τ) := Real.cosh_pos _
  have hr : 0 < √(Real.cosh (π * τ)) := Real.sqrt_pos.mpr hc
  have hqq : √(Real.cosh (π * τ)) * √(Real.cosh (π * τ)) = Real.cosh (π * τ) :=
    Real.mul_self_sqrt hc.le
  have hσ : Real.sinh (π * τ / 2) ≠ 0 := by
    intro h
    have := Real.sinh_eq_zero.mp h
    have hpi := Real.pi_pos
    apply hτ
    nlinarith
  rw [psiTil_right hτ, kC_right, cC_right]
  have hcast : ((Real.cosh (π * τ) : ℝ) : ℂ) = ((√(Real.cosh (π * τ)) * √(Real.cosh (π * τ)) : ℝ) : ℂ) := by
    rw [hqq]
  rw [hcast]
  unfold Lg
  rw [right_aux _ _ _ hr hσ]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  unfold fR vA
  rw [hqq]

lemma psiTil_left_re {τ : ℝ} (hτ : τ ≠ 0) : (psiTil ((τ : ℂ) * Complex.I)).re = fL τ := by
  rw [psiTil_left_eq hτ]; simp

/-- **Piece 3 (Cauchy on the strip)**: `∫_ℝ (x_A + v_A) = 2π - 2√2`. -/
theorem xb_cauchy_identity :
    Integrable xA ∧ Integrable vA ∧ ∫ τ : ℝ, (xA τ + vA τ) = 2 * π - 2 * √2 := by
  obtain ⟨C, hC⟩ := psiHat_bound
  have hd : DifferentiableOn ℂ psiTil unitStrip :=
    differentiableOn_psiHat.congr (fun s hs => psiTil_of_mem hs)
  obtain ⟨hiL, hiR, heq⟩ := strip_edge_cauchy (ε := π / 2) hd (by positivity) continuousOn_psiTil
    (fun s hs => by rw [psiTil_of_mem hs]; exact hC s hs)
  have hae : ∀ᵐ τ : ℝ, τ ≠ 0 := by
    have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
    simpa using this
  have hfL : Integrable fL := by
    refine hiL.re.congr ?_
    filter_upwards [hae] with τ hτ using psiTil_left_re hτ
  have hfR : Integrable fR := by
    refine hiR.re.congr ?_
    filter_upwards [hae] with τ hτ using psiTil_right_re hτ
  have hint : ∫ τ : ℝ, fL τ = ∫ τ : ℝ, fR τ := by
    have hl := integral_re hiL
    have hr := integral_re hiR
    have h1 : ∫ τ : ℝ, (psiTil ((τ : ℂ) * Complex.I)).re =
        ∫ τ : ℝ, (psiTil (1 + (τ : ℂ) * Complex.I)).re :=
      hl.trans ((congrArg Complex.re heq).trans hr.symm)
    have hL : ∫ τ : ℝ, fL τ = ∫ τ : ℝ, (psiTil ((τ : ℂ) * Complex.I)).re :=
      integral_congr_ae (by filter_upwards [hae] with τ hτ using (psiTil_left_re hτ).symm)
    have hR : ∫ τ : ℝ, (psiTil (1 + (τ : ℂ) * Complex.I)).re = ∫ τ : ℝ, fR τ :=
      integral_congr_ae (by filter_upwards [hae] with τ hτ using psiTil_right_re hτ)
    exact hL.trans (h1.trans hR)
  have hpi := Real.pi_pos
  have s1 : Integrable fun τ : ℝ => 1 / Real.cosh (π * τ) := integrable_sech hpi
  have s2 : Integrable fun τ : ℝ => 1 / Real.cosh (π / 2 * τ) := integrable_sech (by positivity)
  have e1 : ∫ τ : ℝ, 1 / Real.cosh (π * τ) = 1 := by rw [integral_sech hpi]; field_simp
  have e2 : ∫ τ : ℝ, 1 / Real.cosh (π / 2 * τ) = 2 := by
    rw [integral_sech (by positivity)]; field_simp
  have hxA : xA = fun τ => π * (1 / Real.cosh (π * τ)) - √2 * (1 / Real.cosh (π / 2 * τ)) - fL τ := by
    funext τ
    unfold fL
    have : π * τ / 2 = π / 2 * τ := by ring
    rw [this]; ring
  have hvA : vA = fun τ => fR τ + π * (1 / Real.cosh (π * τ)) := by
    funext τ; unfold fR; ring
  have iA : Integrable xA := by
    rw [hxA]; exact ((s1.const_mul π).sub (s2.const_mul √2)).sub hfL
  have iV : Integrable vA := by
    rw [hvA]; exact hfR.add (s1.const_mul π)
  refine ⟨iA, iV, ?_⟩
  rw [integral_add iA iV]
  have jA : ∫ τ : ℝ, xA τ = π - √2 * 2 - ∫ τ : ℝ, fL τ := by
    rw [hxA]
    beta_reduce
    rw [integral_sub (f := fun τ : ℝ => π * (1 / Real.cosh (π * τ)) - √2 * (1 / Real.cosh (π / 2 * τ)))
      (g := fL) ((s1.const_mul π).sub (s2.const_mul √2)) hfL]
    rw [integral_sub (f := fun τ : ℝ => π * (1 / Real.cosh (π * τ)))
      (g := fun τ : ℝ => √2 * (1 / Real.cosh (π / 2 * τ))) (s1.const_mul π) (s2.const_mul √2)]
    rw [integral_const_mul, integral_const_mul, e1, e2]
    ring
  have jV : ∫ τ : ℝ, vA τ = (∫ τ : ℝ, fR τ) + π := by
    rw [hvA]
    beta_reduce
    rw [integral_add hfR (s1.const_mul π), integral_const_mul, e1]; ring
  rw [jA, jV, hint]; ring

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.xb_cauchy_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.xb_cauchy_identity

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.integral_sech' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.integral_sech
