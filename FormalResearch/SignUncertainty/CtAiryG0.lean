module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The complex Airy integral `G_0` and its ODE

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 1.  **Proved.**

With `α = 2^{2/3} e^{2πi/3}` (`α³ = 4`) and `p > -1`, `u ∈ ℝ`:
`gI p u = ∫_0^∞ t^p e^{α u t - t³/3} dt`.  Then `∂_u gI p = α · gI (p+1)` (`hasDerivAt_gI`),
integration by parts of `t^{1/2} e^{αut - t³/3}` gives `½ gI(-1/2) + α u gI(1/2) = gI(5/2)`
(`gI_ibp`), hence `G_0 = gI(-1/2)/(α√π)` satisfies `G_0''' = 4uG_0' + 2G_0`
(`G0_ode`), and the values `gI p 0` are Gamma integrals (`gI_zero`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtAiry

/-- `r = 2^{-1/3}`, so that `r³ = 1/2`. -/
noncomputable def rr : ℝ := (2 : ℝ) ^ (-(1 / 3) : ℝ)

lemma rr_pos : 0 < rr := Real.rpow_pos_of_pos (by norm_num) _

lemma rr_cube : rr ^ 3 = 1 / 2 := by
  unfold rr
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma rr_lt_one : rr < 1 := by
  have h : rr ^ 3 = 1 / 2 := rr_cube
  have := rr_pos
  by_contra hc
  push Not at hc
  nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hc 3]

/-- `α = 2^{2/3} e^{2πi/3} = r(-1 + i√3)`. -/
noncomputable def al : ℂ := ⟨-rr, rr * √3⟩

lemma al_re : al.re = -rr := rfl

lemma al_cube : al ^ 3 = 4 := by
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : rr ^ 3 = 1 / 2 := rr_cube
  apply Complex.ext
  · simp [al, pow_succ, Complex.mul_re, Complex.mul_im]
    linear_combination (3 * rr ^ 3) * h3 + 8 * hr
  · simp [al, pow_succ, Complex.mul_re, Complex.mul_im]
    linear_combination (-(rr ^ 3 * √3)) * h3

lemma al_ne : al ≠ 0 := by
  intro h
  have := al_cube
  rw [h] at this
  norm_num at this

lemma norm_al_le : ‖al‖ ≤ 2 := by
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have := rr_lt_one
  have := rr_pos
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [al]
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [h3]

/-- The integrand `t^p e^{α u t - t³/3}`. -/
noncomputable def gF (p u t : ℝ) : ℂ :=
  ((t ^ p : ℝ) : ℂ) * cexp (al * u * t - (t : ℂ) ^ 3 / 3)

/-- `gI p u = ∫_0^∞ t^p e^{α u t - t³/3} dt`. -/
noncomputable def gI (p u : ℝ) : ℂ := ∫ t in Ioi (0 : ℝ), gF p u t

lemma norm_cexp_phase (u t : ℝ) :
    ‖cexp (al * u * t - (t : ℂ) ^ 3 / 3)‖ = Real.exp (-(rr * u * t) - t ^ 3 / 3) := by
  rw [Complex.norm_exp]
  congr 1
  simp [al, pow_succ, Complex.mul_re, Complex.mul_im, Complex.sub_re]

lemma norm_gF {p u t : ℝ} (ht : 0 < t) :
    ‖gF p u t‖ = t ^ p * Real.exp (-(rr * u * t) - t ^ 3 / 3) := by
  unfold gF
  rw [norm_mul, norm_cexp_phase, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]

/-- `B t ≤ t³/6 + 6 M²` for `0 ≤ t`, `M = max 1 B`. -/
lemma lin_le_cube {B t : ℝ} (ht : 0 ≤ t) :
    B * t ≤ t ^ 3 / 6 + 6 * (max 1 B) ^ 2 := by
  set M := max 1 B with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hBM : B ≤ M := le_max_right _ _
  have h1 : B * t ≤ M * t := mul_le_mul_of_nonneg_right hBM ht
  by_cases h : 6 * M ≤ t ^ 2
  · have : M * t ≤ t ^ 3 / 6 := by
      have : M * t ≤ (t ^ 2 / 6) * t := mul_le_mul_of_nonneg_right (by linarith) ht
      nlinarith [this]
    nlinarith [sq_nonneg M]
  · push Not at h
    have htM : t ≤ 6 * M := by
      by_contra hc
      push Not at hc
      nlinarith
    have : M * t ≤ M * (6 * M) := mul_le_mul_of_nonneg_left htM (by linarith)
    have : 0 ≤ t ^ 3 / 6 := by positivity
    nlinarith

lemma integrable_bound {p B : ℝ} (hp : -1 < p) :
    IntegrableOn (fun t : ℝ => t ^ p * Real.exp (B * t - t ^ 3 / 3)) (Ioi 0) := by
  have hI := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 3) (s := p) (b := 1 / 6) hp
    (by norm_num) (by norm_num)
  have hmeas : Measurable (fun t : ℝ => t ^ p * Real.exp (B * t - t ^ 3 / 3)) := by fun_prop
  refine Integrable.mono' (hI.const_mul (Real.exp (6 * (max 1 B) ^ 2)))
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have h1 := lin_le_cube (B := B) ht0.le
  have h3 : t ^ (3 : ℝ) = t ^ 3 := by exact_mod_cast Real.rpow_natCast t 3
  rw [Real.norm_of_nonneg (by positivity), h3]
  have : Real.exp (B * t - t ^ 3 / 3) ≤ Real.exp (6 * (max 1 B) ^ 2) * Real.exp (-(1 / 6) * t ^ 3) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [h1])
  calc t ^ p * Real.exp (B * t - t ^ 3 / 3)
      ≤ t ^ p * (Real.exp (6 * (max 1 B) ^ 2) * Real.exp (-(1 / 6) * t ^ 3)) :=
        mul_le_mul_of_nonneg_left this (Real.rpow_nonneg ht0.le _)
    _ = _ := by ring

lemma gF_integrable {p : ℝ} (hp : -1 < p) (u : ℝ) :
    Integrable (fun t => gF p u t) (volume.restrict (Ioi (0 : ℝ))) := by
  have hI := integrable_bound (p := p) (B := -(rr * u)) hp
  have hmeas : AEStronglyMeasurable (fun t => gF p u t) (volume.restrict (Ioi (0 : ℝ))) := by
    unfold gF
    refine Measurable.aestronglyMeasurable ?_
    fun_prop
  refine Integrable.mono' hI hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_gF ht]
  apply le_of_eq
  congr 2
  ring

lemma hasDerivAt_gF (p t u : ℝ) :
    HasDerivAt (fun v : ℝ => gF p v t) ((al * t) * gF p u t) u := by
  unfold gF
  have h1 : HasDerivAt (fun v : ℝ => al * (v : ℂ) * (t : ℂ) - (t : ℂ) ^ 3 / 3) (al * t) u := by
    have h0 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
    have := (h0.const_mul al).mul_const (t : ℂ)
    have h := this.sub_const ((t : ℂ) ^ 3 / 3)
    convert h using 1
    simp
  have h2 := (h1.cexp).const_mul (((t ^ p : ℝ) : ℂ))
  refine h2.congr_deriv ?_
  ring

/-- `∂_u gI p = α · gI (p+1)` for `p > -1`. -/
theorem hasDerivAt_gI {p : ℝ} (hp : -1 < p) (u : ℝ) :
    HasDerivAt (gI p) (al * gI (p + 1) u) u := by
  set B : ℝ := rr * (|u| + 1) with hB
  have hbd := integrable_bound (p := p + 1) (B := B) (by linarith)
  have hmeasF' : AEStronglyMeasurable (fun t => (al * t) * gF p u t)
      (volume.restrict (Ioi (0 : ℝ))) := by
    unfold gF
    refine Measurable.aestronglyMeasurable ?_
    fun_prop
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun v t => gF p v t) (F' := fun v t => (al * t) * gF p v t) (x₀ := u) (s := Metric.ball u 1)
    (bound := fun t => 2 * (t ^ (p + 1) * Real.exp (B * t - t ^ 3 / 3))) (Metric.ball_mem_nhds u one_pos)
    (Filter.Eventually.of_forall fun v => (gF_integrable hp v).aestronglyMeasurable)
    (gF_integrable hp u) hmeasF' ?_ (hbd.const_mul 2) ?_
  · have heq : ∫ t in Ioi (0 : ℝ), (al * t) * gF p u t = al * gI (p + 1) u := by
      unfold gI
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := ht
      simp only [gF]
      have : ((t ^ (p + 1) : ℝ) : ℂ) = (t : ℂ) * ((t ^ p : ℝ) : ℂ) := by
        rw [Real.rpow_add ht0, Real.rpow_one]; push_cast; ring
      rw [this]; ring
    have := key.2
    rw [heq] at this
    exact this
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht v hv
    have ht0 : 0 < t := ht
    have hv' : |v - u| < 1 := by simpa [Real.dist_eq] using hv
    have hvu : |v| ≤ |u| + 1 := by
      have := abs_sub_abs_le_abs_sub v u
      linarith
    rw [norm_mul, norm_mul, norm_gF ht0, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have h1 : -(rr * v * t) - t ^ 3 / 3 ≤ B * t - t ^ 3 / 3 := by
      have : -(rr * v) ≤ rr * (|u| + 1) := by
        have := neg_abs_le v
        nlinarith [rr_pos, neg_le_abs v]
      nlinarith [mul_le_mul_of_nonneg_right this ht0.le]
    have h2 : t ^ (p + 1) = t * t ^ p := by
      rw [Real.rpow_add ht0, Real.rpow_one]; ring
    have h3 := Real.exp_le_exp.2 h1
    have h4 : ‖al‖ ≤ 2 := norm_al_le
    have h5 : 0 ≤ t * t ^ p := mul_nonneg ht0.le (Real.rpow_nonneg ht0.le _)
    rw [h2]
    calc ‖al‖ * t * (t ^ p * Real.exp (-(rr * v * t) - t ^ 3 / 3))
        = ‖al‖ * ((t * t ^ p) * Real.exp (-(rr * v * t) - t ^ 3 / 3)) := by ring
      _ ≤ 2 * ((t * t ^ p) * Real.exp (B * t - t ^ 3 / 3)) := by
        gcongr
  · filter_upwards with t v _
    exact hasDerivAt_gF p t v

lemma tendsto_gF_half (u : ℝ) : Tendsto (fun t : ℝ => gF (1 / 2) u t) atTop (𝓝 0) := by
  set B : ℝ := -(rr * u) with hB
  have hz : Tendsto (fun t : ℝ => Real.exp (6 * (max 1 B) ^ 2) * (t ^ (1 / 2 : ℝ) *
      Real.exp (-(1 / 6 : ℝ) * t))) atTop (𝓝 0) := by
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2 : ℝ) (1 / 6 : ℝ) (by norm_num)
    simpa using this.const_mul (Real.exp (6 * (max 1 B) ^ 2))
  refine squeeze_zero_norm' ?_ hz
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  rw [norm_gF ht0]
  have h1 := lin_le_cube (B := B) ht0.le
  have h2 : t ≤ t ^ 3 := by nlinarith [sq_nonneg t, mul_nonneg ht0.le (sq_nonneg (t - 1))]
  have : Real.exp (-(rr * u * t) - t ^ 3 / 3) ≤
      Real.exp (6 * (max 1 B) ^ 2) * Real.exp (-(1 / 6 : ℝ) * t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by rw [hB] at h1; nlinarith [h1, h2])
  calc t ^ (1 / 2 : ℝ) * Real.exp (-(rr * u * t) - t ^ 3 / 3)
      ≤ t ^ (1 / 2 : ℝ) * (Real.exp (6 * (max 1 B) ^ 2) * Real.exp (-(1 / 6 : ℝ) * t)) :=
        mul_le_mul_of_nonneg_left this (Real.rpow_nonneg ht0.le _)
    _ = _ := by ring

/-- Integration by parts: `½ gI(-1/2) + α u gI(1/2) = gI(5/2)`. -/
theorem gI_ibp (u : ℝ) :
    (1 / 2 : ℂ) * gI (-1 / 2) u + al * u * gI (1 / 2) u - gI (5 / 2) u = 0 := by
  let f : ℝ → ℂ := fun t => gF (1 / 2) u t
  let f' : ℝ → ℂ := fun t => (1 / 2 : ℂ) * gF (-1 / 2) u t + (al * u) * gF (1 / 2) u t
      - gF (5 / 2) u t
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t := by
    intro t ht
    have ht0 : 0 < t := ht
    have h1 : HasDerivAt (fun t : ℝ => ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ))
        (((1 / 2 : ℝ) * t ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ) t :=
      (Real.hasDerivAt_rpow_const (Or.inl ht0.ne')).ofReal_comp
    have h0 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h2 : HasDerivAt (fun t : ℝ => al * (u : ℂ) * (t : ℂ) - (t : ℂ) ^ 3 / 3)
        (al * u - (t : ℂ) ^ 2) t := by
      have := ((h0.const_mul (al * (u : ℂ))).sub ((h0.pow 3).div_const 3))
      convert this using 1
      simp
    have h3 := h1.mul h2.cexp
    refine h3.congr_deriv ?_
    simp only [f']
    have e1 : t ^ ((1 / 2 : ℝ) - 1) = t ^ (-1 / 2 : ℝ) := by norm_num
    have e2 : t ^ (5 / 2 : ℝ) = t ^ (1 / 2 : ℝ) * t ^ 2 := by
      rw [show (5 / 2 : ℝ) = 1 / 2 + (2 : ℕ) by norm_num, Real.rpow_add ht0, Real.rpow_natCast]
    unfold gF
    rw [e1, e2]
    push_cast
    ring
  have hint : IntegrableOn f' (Ioi 0) := by
    have a1 := gF_integrable (p := -1 / 2) (by norm_num) u
    have a2 := gF_integrable (p := 1 / 2) (by norm_num) u
    have a3 := gF_integrable (p := 5 / 2) (by norm_num) u
    exact ((a1.const_mul (1 / 2 : ℂ)).add (a2.const_mul (al * u))).sub a3
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    have : Continuous f := by
      show Continuous (fun t : ℝ => gF (1 / 2) u t)
      unfold gF
      exact (Complex.continuous_ofReal.comp (Real.continuous_rpow_const (by norm_num))).mul
        (Complex.continuous_exp.comp (by fun_prop))
    exact this.continuousWithinAt
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint (tendsto_gF_half u)
  have h0 : f 0 = 0 := by simp [f, gF]
  rw [h0, sub_zero] at this
  have e : ∫ t in Ioi (0 : ℝ), f' t = (1 / 2 : ℂ) * gI (-1 / 2) u + al * u * gI (1 / 2) u
      - gI (5 / 2) u := by
    have a1 := gF_integrable (p := -1 / 2) (by norm_num) u
    have a2 := gF_integrable (p := 1 / 2) (by norm_num) u
    have a3 := gF_integrable (p := 5 / 2) (by norm_num) u
    simp only [f', gI]
    have i12 : Integrable (fun t => (1 / 2 : ℂ) * gF (-1 / 2) u t + (al * u) * gF (1 / 2) u t)
        (volume.restrict (Ioi (0 : ℝ))) := (a1.const_mul _).add (a2.const_mul _)
    rw [integral_sub i12 a3, integral_add (a1.const_mul _) (a2.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [← e, this]

/-- `G_0(u) = (α√π)⁻¹ ∫_0^∞ t^{-1/2} e^{αut - t³/3} dt`. -/
noncomputable def G0 (u : ℝ) : ℂ := gI (-1 / 2) u / (al * (√π : ℝ))
/-- `G_0'(u) = π^{-1/2} ∫_0^∞ t^{1/2} e^{αut - t³/3} dt`. -/
noncomputable def G1 (u : ℝ) : ℂ := gI (1 / 2) u / (√π : ℝ)
/-- `G_0''(u) = απ^{-1/2} ∫_0^∞ t^{3/2} e^{αut - t³/3} dt`. -/
noncomputable def G2 (u : ℝ) : ℂ := al * gI (3 / 2) u / (√π : ℝ)

lemma sqrtpi_ne : ((√π : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'

theorem hasDerivAt_G0 (u : ℝ) : HasDerivAt G0 (G1 u) u := by
  have h := (hasDerivAt_gI (p := -1 / 2) (by norm_num) u).div_const (al * (√π : ℝ))
  refine h.congr_deriv ?_
  have e : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [e]
  unfold G1
  field_simp [al_ne, sqrtpi_ne]

theorem hasDerivAt_G1 (u : ℝ) : HasDerivAt G1 (G2 u) u := by
  have h := (hasDerivAt_gI (p := 1 / 2) (by norm_num) u).div_const ((√π : ℝ) : ℂ)
  refine h.congr_deriv ?_
  have e : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
  rw [e]
  unfold G2
  ring

theorem hasDerivAt_G2 (u : ℝ) : HasDerivAt G2 (4 * (u : ℂ) * G1 u + 2 * G0 u) u := by
  have h := ((hasDerivAt_gI (p := 3 / 2) (by norm_num) u).const_mul al).div_const
    ((√π : ℝ) : ℂ)
  refine h.congr_deriv ?_
  have e : (3 / 2 : ℝ) + 1 = 5 / 2 := by norm_num
  rw [e]
  have hi := gI_ibp u
  have h5 : gI (5 / 2) u = (1 / 2 : ℂ) * gI (-1 / 2) u + al * u * gI (1 / 2) u := by
    linear_combination -hi
  rw [h5]
  unfold G1 G0
  have h3 : al ^ 3 = 4 := al_cube
  field_simp [al_ne, sqrtpi_ne]
  rw [show (-(1 / 2) : ℝ) = -1 / 2 by norm_num]
  linear_combination (gI (-1 / 2) u + 2 * al * u * gI (1 / 2) u) * h3

/-- info: 'FormalResearch.SignUncertainty.CtAiry.hasDerivAt_gI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_gI

/-- info: 'FormalResearch.SignUncertainty.CtAiry.gI_ibp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gI_ibp

/-- info: 'FormalResearch.SignUncertainty.CtAiry.hasDerivAt_G2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_G2

end FormalResearch.SignUncertainty.CtAiry
