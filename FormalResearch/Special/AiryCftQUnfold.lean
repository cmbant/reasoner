module

public import FormalResearch.Special.AiryCftWeights
public import FormalResearch.Complex.HardyArcDecay

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.Special

/-- The unfolded function `G(z) = z f(-z²) exp((4/3) i z³)` (Lemma U of the Airy-Poisson note), `z ∈ ℍ`. -/
noncomputable def airyQG (f : ℂ → ℂ) (z : ℂ) : ℂ := z * f (-(z ^ 2)) * cexp ((4 / 3 : ℂ) * I * z ^ 3)

/-- `Re (-z²)^{3/2} = - Im z³` for `Im z ≥ 0` (principal branch). -/
lemma airyQ_re_cpow_neg_sq {z : ℂ} (hz : 0 ≤ z.im) :
    ((-(z ^ 2)) ^ (3 / 2 : ℂ)).re = -(z ^ 3).im := by
  set s : ℂ := (-(z ^ 2)) ^ (1 / 2 : ℂ) with hs
  have hs2 : s ^ 2 = (-I * z) ^ 2 := by
    rw [hs, cpow_half_sq]; ring_nf; simp [Complex.I_sq]
  have hs3 : (-(z ^ 2)) ^ (3 / 2 : ℂ) = s ^ 3 := (cpow_half_cube _).symm
  have hre : 0 ≤ s.re := cpow_half_re_nonneg _
  have hcases : s = -I * z ∨ s = I * z := by
    have : (s - (-I * z)) * (s + (-I * z)) = 0 := by linear_combination hs2
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rw [hs3]
  rcases hz.lt_or_eq with hpos | hzero
  · have hcase : s = -I * z := by
      rcases hcases with h | h
      · exact h
      · exfalso
        have : s.re = -z.im := by rw [h]; simp
        linarith
    rw [hcase]
    have : (-I * z) ^ 3 = I * z ^ 3 := by
      have : (-I) ^ 3 = I := by
        have h1 : I ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
        calc (-I) ^ 3 = -(I ^ 3) := by ring
          _ = I := by rw [h1]; ring
      rw [mul_pow, this]
    rw [this]; simp
  · have hzim : z.im = 0 := hzero.symm
    have h3 : (z ^ 3).im = 0 := by
      have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzim])
      rw [hz']; simp [← Complex.ofReal_pow]
    rw [h3, neg_zero]
    rcases hcases with h | h
    · rw [h]
      have : (-I * z) ^ 3 = I * z ^ 3 := by
        have : (-I) ^ 3 = I := by
          have h1 : I ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
          calc (-I) ^ 3 = -(I ^ 3) := by ring
            _ = I := by rw [h1]; ring
        rw [mul_pow, this]
      rw [this]; simp [h3]
    · rw [h]
      have : (I * z) ^ 3 = -(I * z ^ 3) := by
        have h1 : I ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
        rw [mul_pow, h1]; ring
      rw [this]; simp [h3]

/-- `|exp((4/3) i z³)| · e(-z²) = 1` for `Im z ≥ 0`. -/
lemma airyQ_norm_exp_mul_env {z : ℂ} (hz : 0 ≤ z.im) :
    ‖cexp ((4 / 3 : ℂ) * I * z ^ 3)‖ * airyEnv (-(z ^ 2)) = 1 := by
  rw [Complex.norm_exp, airyEnv, airyQ_re_cpow_neg_sq hz, ← Real.exp_add]
  have : ((4 / 3 : ℂ) * I * z ^ 3).re = -(4 / 3) * (z ^ 3).im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  have : -(4 / 3) * (z ^ 3).im + -(4 / 3) * -(z ^ 3).im = 0 := by ring
  rw [this, Real.exp_zero]

/-- **Lemma U (unfolding).** For `Im z ≥ 0`: `‖G(z)‖ = ‖z‖ ‖f(-z²)‖ / e(-z²)`. -/
lemma airyQ_norm_G (f : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖airyQG f z‖ = ‖z‖ * (‖f (-(z ^ 2))‖ / airyEnv (-(z ^ 2))) := by
  have h1 := airyQ_norm_exp_mul_env hz
  have he := airyEnv_pos (-(z ^ 2))
  have h2 : ‖cexp ((4 / 3 : ℂ) * I * z ^ 3)‖ = 1 / airyEnv (-(z ^ 2)) := (eq_div_iff he.ne').2 h1
  unfold airyQG
  rw [norm_mul, norm_mul, h2]
  ring

lemma airyQ_differentiable_G {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Differentiable ℂ (airyQG f) := by
  unfold airyQG
  fun_prop

/-- Polynomial growth of `G` on the closed upper half-plane from `‖f u‖ ≤ C (1+|u|)^ν e(u)`. -/
lemma airyQ_G_growth {f : ℂ → ℂ} {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖airyQG f z‖ ≤ C * (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊ + 1) := by
  rw [airyQ_norm_G f hz]
  have he := airyEnv_pos (-(z ^ 2))
  have h1 : ‖f (-(z ^ 2))‖ / airyEnv (-(z ^ 2)) ≤ C * (1 + ‖z‖ ^ 2) ^ ν := by
    rw [div_le_iff₀ he]
    have := hb (-(z ^ 2))
    rwa [norm_neg, norm_pow] at this
  have h2 : (1 + ‖z‖ ^ 2) ^ ν ≤ (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊) := by
    have hbase : 1 ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z‖]
    calc (1 + ‖z‖ ^ 2) ^ ν ≤ (1 + ‖z‖ ^ 2) ^ (max ν 0) :=
          Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
      _ ≤ (1 + ‖z‖ ^ 2) ^ ((⌈max ν 0⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase (Nat.le_ceil _)
      _ = (1 + ‖z‖ ^ 2) ^ ⌈max ν 0⌉₊ := Real.rpow_natCast _ _
      _ ≤ ((1 + ‖z‖) ^ 2) ^ ⌈max ν 0⌉₊ := by
          gcongr
          nlinarith [norm_nonneg z]
      _ = (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊) := by rw [← pow_mul]
  have hz0 : ‖z‖ ≤ 1 + ‖z‖ := by linarith
  calc ‖z‖ * (‖f (-(z ^ 2))‖ / airyEnv (-(z ^ 2))) ≤ ‖z‖ * (C * (1 + ‖z‖ ^ 2) ^ ν) := by gcongr
    _ ≤ ‖z‖ * (C * (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊)) := by gcongr
    _ ≤ (1 + ‖z‖) * (C * (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊)) := by gcongr
    _ = C * (1 + ‖z‖) ^ (2 * ⌈max ν 0⌉₊ + 1) := by ring

lemma airyEnv_neg_sq_real (x : ℝ) : airyEnv (-((x : ℂ) ^ 2)) = 1 := by
  rw [airyEnv, airyQ_re_cpow_neg_sq (z := (x : ℂ)) (by simp)]
  have : ((x : ℂ) ^ 3).im = 0 := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
  rw [this]; simp

lemma airyQ_norm_G_real (f : ℂ → ℂ) (x : ℝ) :
    ‖airyQG f (x : ℂ)‖ = |x| * ‖f (((-(x ^ 2) : ℝ)) : ℂ)‖ := by
  rw [airyQ_norm_G f (by simp), airyEnv_neg_sq_real, div_one, Complex.norm_real, Real.norm_eq_abs]
  congr 3
  push_cast; ring

lemma integrable_comp_abs_of_Ioi {h : ℝ → ℝ} (hh : IntegrableOn (fun x => h |x|) (Ioi (0 : ℝ))) :
    Integrable (fun x : ℝ => h |x|) := by
  have int_Iic : IntegrableOn (fun x : ℝ => h |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hh
  have := int_Iic.union hh
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- The boundary values of `G` are integrable on `ℝ` when `f ∈ L¹(ℝ)`, and `∫_ℝ ‖G‖ = ∫_{x<0} ‖f‖`. -/
lemma airyQ_boundary {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ))) :
    Integrable (fun x : ℝ => airyQG f (x : ℂ)) ∧
      ∫ x : ℝ, ‖airyQG f (x : ℂ)‖ = ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
  set φ : ℝ → ℝ := fun v => ‖f ((-v : ℝ) : ℂ)‖ with hφ
  have h1 : Integrable φ := hfi.comp_neg.norm
  have hsq : (fun x : ℝ => x ^ 2) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩; exact pow_pos hx 2
    · intro hv; exact ⟨Real.sqrt v, Real.sqrt_pos.2 hv, Real.sq_sqrt hv.le⟩
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x ^ 2) (2 * x) (Ioi 0) x := fun x hx => by
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ => x ^ 2) (Ioi 0) := fun a ha b hb hab => (sq_eq_sq₀ ha.le hb.le).1 hab
  have h2 : IntegrableOn (fun x : ℝ => |2 * x| • φ (x ^ 2)) (Ioi 0) := by
    have := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi (0 : ℝ))
      (f := fun x : ℝ => x ^ 2) (f' := fun x => 2 * x) measurableSet_Ioi hd hinj φ).1
    rw [hsq] at this
    exact this h1.integrableOn
  set H : ℝ → ℝ := fun t => t * φ (t ^ 2) with hH
  have hG : ∀ x : ℝ, ‖airyQG f (x : ℂ)‖ = H |x| := by
    intro x
    rw [airyQ_norm_G_real, hH]
    simp only [hφ, sq_abs]
  have h3 : IntegrableOn (fun x : ℝ => H |x|) (Ioi 0) := by
    have : IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * (|2 * x| • φ (x ^ 2))) (Ioi 0) := h2.const_mul _
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [hH, smul_eq_mul, sq_abs]
    have hx' : 0 < x := hx
    rw [abs_of_pos hx', abs_of_pos (by linarith)]
    ring
  have h4 : Integrable (fun x : ℝ => H |x|) := integrable_comp_abs_of_Ioi h3
  have hGc : Continuous (fun x : ℝ => airyQG f (x : ℂ)) :=
    (airyQ_differentiable_G hf).continuous.comp Complex.continuous_ofReal
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' h4 hGc.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [hG x, ← hG x]
  · simp_rw [hG]
    rw [integral_comp_abs (f := H)]
    have h5 : ∫ v in Ioi (0 : ℝ), φ v = ∫ x in Ioi (0 : ℝ), |2 * x| • φ (x ^ 2) := by
      have := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
        (f := fun x : ℝ => x ^ 2) (f' := fun x => 2 * x) measurableSet_Ioi hd hinj φ
      rwa [hsq] at this
    have h6 : ∫ x in Ioi (0 : ℝ), |2 * x| • φ (x ^ 2) = 2 * ∫ x in Ioi (0 : ℝ), H x := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      simp only [hH, smul_eq_mul]
      rw [abs_of_pos (by have : 0 < x := hx; linarith)]
      ring
    have h7 : ∫ v in Ioi (0 : ℝ), φ v = ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
      have := integral_comp_neg_Ioi (0 : ℝ) (fun x : ℝ => ‖f (x : ℂ)‖)
      simpa [hφ] using this
    rw [← h7, h5, h6]

/-- info: 'FormalResearch.Special.airyQ_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_boundary

end FormalResearch.Special
