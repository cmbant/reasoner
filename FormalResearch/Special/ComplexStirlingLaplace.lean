module

public import Mathlib

/-!
# Laplace transforms of bounded kernels on the right half-plane

Infrastructure for the complex Stirling / Binet development (`ComplexStirlingKernel`,
`ComplexStirlingRemainder`, `ComplexStirlingBinet`, `ComplexStirlingLine`).

For `g : ℝ → ℝ` put `lap g z = ∫_{t>0} g(t) e^{-tz} dt`.  If `g` is continuous on `(0,∞)` and
`|g| ≤ M` there, then on `Re z > 0`:

* `norm_lap_le` : `‖lap g z‖ ≤ M / Re z`;
* `hasDerivAt_lap` : `lap g` is complex differentiable with derivative `-lap (t ↦ t g(t))` (domination of
  the derivative on a disc of radius `Re z / 2`);
* `norm_lap_mul_le` : `‖lap (t ↦ t g(t)) z‖ ≤ M / (Re z)²`;
* `lap_ofReal` : on the positive real axis `lap g x` is the real integral.

Everything is proved here from scratch (Mathlib has Mellin transforms and the Gamma integral but no Laplace
transform API).

Not formalised: the general theory of Laplace transforms (uniqueness, inversion, growth classes beyond bounded
kernels).
-/

@[expose] public section

namespace FormalResearch.Special.ComplexStirling

open MeasureTheory Set Filter Topology

/-- The Laplace transform `z ↦ ∫_{t>0} g(t) e^{-tz} dt` of a real kernel. -/
noncomputable def lap (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (g t : ℂ) * Complex.exp (-(t : ℂ) * z)

lemma norm_exp_neg_mul (t : ℝ) (z : ℂ) :
    ‖Complex.exp (-(t : ℂ) * z)‖ = Real.exp (-(z.re * t)) := by
  rw [Complex.norm_exp]; congr 1; simp [mul_comm]

lemma integrableOn_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-(x * t))) (Ioi 0) := by
  have := integrableOn_exp_mul_Ioi (a := -x) (by linarith) 0
  simpa [neg_mul] using this

lemma integral_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) = 1 / x := by
  have := integral_exp_mul_Ioi (a := -x) (by linarith) 0
  simp only [neg_mul, mul_zero, Real.exp_zero] at this
  rw [this]; field_simp

lemma integrableOn_mul_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(x * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := x) (by norm_num)
    one_pos hx
  simpa using this

lemma integral_mul_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(x * t)) = 1 / x ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := x) (by norm_num) hx
  have e : ∀ t : ℝ, t ^ ((2 : ℝ) - 1) * Real.exp (-(x * t)) = t * Real.exp (-(x * t)) := by
    intro t; norm_num
  simp only [e] at h
  rw [h]
  have : Real.Gamma 2 = 1 := by simp
  rw [this]; simp

section

variable {g : ℝ → ℝ} {M : ℝ}

lemma lap_integrand_aesm (hc : ContinuousOn g (Ioi 0)) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (g t : ℂ) * Complex.exp (-(t : ℂ) * z))
      (volume.restrict (Ioi 0)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  exact (Complex.continuous_ofReal.comp_continuousOn hc).mul (by fun_prop : Continuous
    fun t : ℝ => Complex.exp (-(t : ℂ) * z)).continuousOn

lemma norm_lap_integrand_le (hM : ∀ t, 0 < t → |g t| ≤ M) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(g t : ℂ) * Complex.exp (-(t : ℂ) * z)‖ ≤ M * Real.exp (-(z.re * t)) := by
  rw [norm_mul, norm_exp_neg_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM t ht) (Real.exp_pos _).le

lemma lap_integrable (hc : ContinuousOn g (Ioi 0)) (hM : ∀ t, 0 < t → |g t| ≤ M) {z : ℂ}
    (hz : 0 < z.re) :
    Integrable (fun t : ℝ => (g t : ℂ) * Complex.exp (-(t : ℂ) * z)) (volume.restrict (Ioi 0)) := by
  refine Integrable.mono' ((integrableOn_exp_neg_mul hz).const_mul M)
    (lap_integrand_aesm hc z) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Filter.Eventually.of_forall fun t ht => norm_lap_integrand_le hM z ht

/-- `‖lap g z‖ ≤ M / Re z` for a kernel bounded by `M`. -/
lemma norm_lap_le (hM : ∀ t, 0 < t → |g t| ≤ M) {z : ℂ}
    (hz : 0 < z.re) : ‖lap g z‖ ≤ M / z.re := by
  unfold lap
  have h := norm_integral_le_of_norm_le ((integrableOn_exp_neg_mul hz).const_mul M)
    ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun t ht => norm_lap_integrand_le hM z ht))
  rw [integral_const_mul, integral_exp_neg_mul hz] at h
  simpa [div_eq_mul_inv] using h

/-- `‖lap (t ↦ t g(t)) z‖ ≤ M / (Re z)²`. -/
lemma norm_lap_mul_le (hM : ∀ t, 0 < t → |g t| ≤ M) {z : ℂ} (hz : 0 < z.re) :
    ‖lap (fun t => t * g t) z‖ ≤ M / z.re ^ 2 := by
  unfold lap
  have hb : ∀ t : ℝ, 0 < t → ‖(((t * g t : ℝ)) : ℂ) * Complex.exp (-(t : ℂ) * z)‖ ≤
      M * (t * Real.exp (-(z.re * t))) := by
    intro t ht
    rw [norm_mul, norm_exp_neg_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos ht]
    calc t * |g t| * Real.exp (-(z.re * t)) ≤ (t * M) * Real.exp (-(z.re * t)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM t ht) ht.le)
            (Real.exp_pos _).le
      _ = _ := by ring
  have h := norm_integral_le_of_norm_le ((integrableOn_mul_exp_neg_mul hz).const_mul M)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hb))
  rw [integral_const_mul, integral_mul_exp_neg_mul hz] at h
  simpa [div_eq_mul_inv] using h

lemma lap_mul_continuousOn (hc : ContinuousOn g (Ioi 0)) :
    ContinuousOn (fun t : ℝ => t * g t) (Ioi 0) := continuousOn_id.mul hc

/-- Differentiation under the integral sign: `(lap g)' = -lap (t ↦ t g(t))` on `Re z > 0`. -/
theorem hasDerivAt_lap (hc : ContinuousOn g (Ioi 0)) (hM : ∀ t, 0 < t → |g t| ≤ M) {z : ℂ}
    (hz : 0 < z.re) : HasDerivAt (lap g) (-lap (fun t => t * g t) z) z := by
  have hx2 : 0 < z.re / 2 := by linarith
  set F : ℂ → ℝ → ℂ := fun z' t => (g t : ℂ) * Complex.exp (-(t : ℂ) * z') with hF
  set F' : ℂ → ℝ → ℂ := fun z' t => -(((t * g t : ℝ)) : ℂ) * Complex.exp (-(t : ℂ) * z') with hF'
  have hs : Metric.ball z (z.re / 2) ∈ 𝓝 z := Metric.ball_mem_nhds _ hx2
  have hre : ∀ z' ∈ Metric.ball z (z.re / 2), z.re / 2 < z'.re := by
    intro z' hz'
    have h1 : |z'.re - z.re| ≤ ‖z' - z‖ := by
      simpa using Complex.abs_re_le_norm (z' - z)
    have h2 : ‖z' - z‖ < z.re / 2 := by simpa [dist_eq_norm] using hz'
    have := (abs_lt.1 (lt_of_le_of_lt h1 h2)).1
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := F) (F' := F') (x₀ := z) (s := Metric.ball z (z.re / 2))
    (bound := fun t => M * (t * Real.exp (-((z.re / 2) * t)))) hs
    (Filter.Eventually.of_forall fun z' => lap_integrand_aesm hc z')
    (lap_integrable hc hM hz)
    (by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.mul ?_ (by fun_prop : Continuous
        fun t : ℝ => Complex.exp (-(t : ℂ) * z)).continuousOn
      exact (Complex.continuous_ofReal.comp_continuousOn (lap_mul_continuousOn hc)).neg)
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun t ht z' hz' => ?_
      have ht0 : (0 : ℝ) < t := ht
      rw [hF', norm_mul, norm_neg, norm_exp_neg_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_of_pos ht0]
      have h1 : Real.exp (-(z'.re * t)) ≤ Real.exp (-((z.re / 2) * t)) :=
        Real.exp_le_exp.2 (by nlinarith [hre z' hz'])
      have h2 : t * |g t| ≤ t * M := mul_le_mul_of_nonneg_left (hM t ht0) ht0.le
      calc t * |g t| * Real.exp (-(z'.re * t)) ≤ (t * M) * Real.exp (-((z.re / 2) * t)) :=
            mul_le_mul h2 h1 (Real.exp_pos _).le (by nlinarith [abs_nonneg (g t)])
        _ = M * (t * Real.exp (-((z.re / 2) * t))) := by ring)
    ((integrableOn_mul_exp_neg_mul hx2).const_mul M)
    (by
      refine Filter.Eventually.of_forall fun t z' _ => ?_
      have h := (((hasDerivAt_id z').const_mul (-(t : ℂ))).cexp).const_mul (g t : ℂ)
      refine HasDerivAt.congr_deriv h ?_
      simp only [hF', id]; push_cast; ring)
  have h2 := key.2
  unfold lap
  convert h2 using 1
  rw [← integral_neg]
  congr 1
  ext a
  simp only [hF']
  ring
/-- info: 'FormalResearch.Special.ComplexStirling.hasDerivAt_lap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.hasDerivAt_lap

/-- On the positive real axis the transform is the real integral. -/
lemma lap_ofReal (x : ℝ) :
    lap g (x : ℂ) = ((∫ t in Ioi (0 : ℝ), g t * Real.exp (-(t * x)) : ℝ) : ℂ) := by
  unfold lap
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  show _ = _
  rw [Complex.ofReal_mul, Complex.ofReal_exp]; push_cast; ring_nf

/-- Conjugation symmetry. -/
lemma lap_conj (z : ℂ) : lap g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (lap g z) := by
  unfold lap
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg]

end

end FormalResearch.Special.ComplexStirling
