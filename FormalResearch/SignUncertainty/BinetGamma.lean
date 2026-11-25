module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Gamma integral with complex rate

Generic.  **Proved**: for `Re z > 0`, `∫₀^∞ t^n e^{-tz} dt = n!/z^{n+1}`.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace FormalResearch.SignUncertainty.BinetDecay

lemma integrableOn_pow_exp_real {a : ℝ} (ha : 0 < a) (r : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ r * Real.exp (-(a * t))) (Ioi 0) := by
  have hgam : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (r : ℝ)) (Ioi 0) := by
    simpa [add_sub_cancel_right] using
      Real.GammaIntegral_convergent (by positivity : (0 : ℝ) < (r : ℝ) + 1)
  have hscaled : IntegrableOn (fun t : ℝ => Real.exp (-(a * t)) * (a * t) ^ (r : ℝ)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ (r : ℝ)) 0 ha).mpr
    rw [mul_zero] at h
    exact h hgam
  have hconst : IntegrableOn
      (fun t : ℝ => (a ^ r)⁻¹ * (Real.exp (-(a * t)) * (a * t) ^ (r : ℝ))) (Ioi 0) :=
    hscaled.const_mul (a ^ r)⁻¹
  refine hconst.congr_fun (fun t _ => ?_) measurableSet_Ioi
  dsimp only
  rw [Real.rpow_natCast, mul_pow]
  have ha0 : a ^ r ≠ 0 := pow_ne_zero r ha.ne'
  field_simp

lemma integrableOn_pow_exp_cpx (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-((t : ℂ) * z))) (Ioi 0) := by
  refine (integrableOn_pow_exp_real hz n).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-((t : ℂ) * z))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg (le_of_lt ht)]
    have : (-((t : ℂ) * z)).re = -(z.re * t) := by simp [mul_comm]
    rw [this]

lemma tendsto_pow_exp_cpx (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-((t : ℂ) * z))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun t : ℝ => (z.re * t) ^ n * Real.exp (-(z.re * t))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp (tendsto_id.const_mul_atTop hz)
  have h2 := h1.const_mul ((z.re ^ n)⁻¹)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg ht]
  have : (-((t : ℂ) * z)).re = -(z.re * t) := by simp [mul_comm]
  rw [this, mul_pow]
  have hr : z.re ^ n ≠ 0 := pow_ne_zero _ hz.ne'
  field_simp

/-- `∫₀^∞ t^n e^{-tz} dt = n!/z^{n+1}` for `Re z > 0`. -/
theorem integral_pow_exp_cpx (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-((t : ℂ) * z)) =
      (n.factorial : ℂ) / z ^ (n + 1) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  induction n with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    have e : ∀ t : ℝ, Complex.exp (-((t : ℂ) * z)) = Complex.exp (-z * (t : ℂ)) := fun t => by
      congr 1; ring
    simp_rw [e]
    rw [h]
    simp
  | succ n ih =>
    have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1))
        (((n + 1 : ℕ) : ℂ) * (x : ℂ) ^ n) x := by
      intro x _
      have := (hasDerivAt_pow (n + 1) (x : ℂ)).comp_ofReal
      simpa using this
    have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => -(Complex.exp (-((t : ℂ) * z))) / z)
        (Complex.exp (-((x : ℂ) * z))) x := by
      intro x _
      have h1 : HasDerivAt (fun y : ℂ => -(Complex.exp (-(y * z))) / z) (Complex.exp (-((x : ℂ) * z))) (x : ℂ) := by
        have := (((hasDerivAt_id (x : ℂ)).mul_const z).neg.cexp.neg.div_const z)
        refine this.congr_deriv ?_
        simp [hz0]
      exact h1.comp_ofReal
    have hI1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (n + 1) * Complex.exp (-((x : ℂ) * z))) (Ioi 0) :=
      integrableOn_pow_exp_cpx (n + 1) hz
    have hI2 : IntegrableOn (fun x : ℝ => (((n + 1 : ℕ) : ℂ) * (x : ℂ) ^ n) *
        (-(Complex.exp (-((x : ℂ) * z))) / z)) (Ioi 0) := by
      refine IntegrableOn.congr_fun ((integrableOn_pow_exp_cpx n hz).const_mul (-(((n + 1 : ℕ) : ℂ)) / z))
        (fun x _ => ?_) measurableSet_Ioi
      ring
    have h0 : Tendsto (fun x : ℝ => (x : ℂ) ^ (n + 1) * (-(Complex.exp (-((x : ℂ) * z))) / z))
        (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (n + 1) * (-(Complex.exp (-((x : ℂ) * z))) / z)) 0 := by
        fun_prop
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    have hinf : Tendsto (fun x : ℝ => (x : ℂ) ^ (n + 1) * (-(Complex.exp (-((x : ℂ) * z))) / z))
        atTop (𝓝 0) := by
      have := (tendsto_pow_exp_cpx (n + 1) hz).neg.div_const z
      simpa [mul_div_assoc, mul_neg, neg_div] using this
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv
      hI1 hI2 h0 hinf
    have e2 : ∫ x in Ioi (0 : ℝ), (((n + 1 : ℕ) : ℂ) * (x : ℂ) ^ n) * (-(Complex.exp (-((x : ℂ) * z))) / z) =
        -(((n + 1 : ℕ) : ℂ) / z) * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ n * Complex.exp (-((x : ℂ) * z)) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
    rw [e2, ih] at hibp
    have e3 : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (n + 1) * Complex.exp (-((x : ℂ) * z)) =
        ∫ x in Ioi (0 : ℝ), (fun t : ℝ => (t : ℂ) ^ (n + 1)) x * Complex.exp (-((x : ℂ) * z)) := rfl
    rw [e3, hibp, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- info: 'FormalResearch.SignUncertainty.BinetDecay.integral_pow_exp_cpx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_pow_exp_cpx

end FormalResearch.SignUncertainty.BinetDecay
