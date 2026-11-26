module

public import Mathlib
public import FormalResearch.Complex.HalfDiscPoisson

/-!
# Two Cauchy moments and the pointwise Cauchy-moment bound on the upper half-disc (phase-free)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:dyadic` Part (2) ("Good circle by two Cauchy moments").
For `G` continuous on the closed upper half-disc `{‖z‖ ≤ A, 0 ≤ Im z}` and holomorphic on the open one, with arc mass
`Σ := ∫_0^π ‖G(A e^{iy})‖ A dy`:

* `hd_moment_zero`, `hd_moment_one`: the two Cauchy moments `‖∫_{-A}^A G‖ ≤ Σ` and `‖∫_{-A}^A t G(t) dt‖ ≤ A Σ`
  (Cauchy's theorem for `G` and `w G(w)`);
* `hd_moment_pointwise`: for `z` in the open half-disc with `ρ ≤ ‖z‖ ≤ A/4`,
  `2π ‖G(z)‖ ≤ Σ/ρ + AΣ/ρ² + 4Σ/(3A) + ρ⁻² ∫_{-A}^A t² ‖G(t)‖ / ‖z - t‖ dt`
  (Cauchy formula at `z`, the expansion `1/(t-z) = -1/z - t/z² + t²/(z²(t-z))`, both moments, and `‖w - z‖ ≥ 3A/4` on the arc).

Proved, unconditional.  The area integral of this bound over the annular half-sector is `hd_moment_area`.
-/

@[expose] public section

open Complex MeasureTheory Set intervalIntegral Filter Topology
open scoped Real Interval

namespace FormalResearch.HalfDiscCauchy

/-- The arc mass `Σ = ∫_0^π ‖G(A e^{iy})‖ A dy` (the integral of `‖G‖` against arclength on the upper semicircle). -/
noncomputable def hdArcMass (A : ℝ) (G : ℂ → ℂ) : ℝ :=
  ∫ y in (0 : ℝ)..π, ‖G (A * Complex.exp (y * I))‖ * A

lemma hdArcMass_nonneg {A : ℝ} (hA : 0 < A) (G : ℂ → ℂ) : 0 ≤ hdArcMass A G :=
  intervalIntegral.integral_nonneg Real.pi_pos.le fun _ _ => mul_nonneg (norm_nonneg _) hA.le

/-- Cauchy's theorem gives `‖∫_{-A}^A g‖ ≤ ∫_0^π ‖g(A e^{iy})‖ A dy`. -/
theorem hd_norm_diam_le {g : ℂ → ℂ} {A : ℝ} (hA : 0 < A) (hc : ContinuousOn g (closedHalfDisc A))
    (hd : DifferentiableOn ℂ g (openHalfDisc A)) :
    ‖∫ t in (-A)..A, g (t : ℂ)‖ ≤ ∫ y in (0 : ℝ)..π, ‖g (A * Complex.exp (y * I))‖ * A := by
  have h := halfDisc_cauchy hA hc hd
  have h2 : ∫ t in (-A)..A, g (t : ℂ) =
      -(I * ∫ y in (0 : ℝ)..π, g (A * Complex.exp (y * I)) * (A * Complex.exp (y * I))) := by
    linear_combination h
  rw [h2, norm_neg, norm_mul, Complex.norm_I, one_mul]
  refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [norm_mul, norm_arc A y hA]

/-- **Zeroth Cauchy moment**: `‖∫_{-A}^A G‖ ≤ Σ`. -/
theorem hd_moment_zero {G : ℂ → ℂ} {A : ℝ} (hA : 0 < A) (hc : ContinuousOn G (closedHalfDisc A))
    (hd : DifferentiableOn ℂ G (openHalfDisc A)) :
    ‖∫ t in (-A)..A, G (t : ℂ)‖ ≤ hdArcMass A G :=
  hd_norm_diam_le hA hc hd

/-- **First Cauchy moment**: `‖∫_{-A}^A t G(t) dt‖ ≤ A Σ`. -/
theorem hd_moment_one {G : ℂ → ℂ} {A : ℝ} (hA : 0 < A) (hc : ContinuousOn G (closedHalfDisc A))
    (hd : DifferentiableOn ℂ G (openHalfDisc A)) :
    ‖∫ t in (-A)..A, (t : ℂ) * G (t : ℂ)‖ ≤ A * hdArcMass A G := by
  have h := hd_norm_diam_le (g := fun w => w * G w) hA (continuousOn_id.mul hc)
    (differentiableOn_id.mul hd)
  refine h.trans (le_of_eq ?_)
  unfold hdArcMass
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [norm_mul, norm_arc A y hA]
  ring

lemma arcNorm_continuousOn {G : ℂ → ℂ} {A : ℝ} (hA : 0 < A) (hc : ContinuousOn G (closedHalfDisc A)) :
    ContinuousOn (fun y : ℝ => ‖G (A * Complex.exp (y * I))‖ * A) (Icc 0 π) :=
  ((BdCont.of_closed hA hc).2.norm).mul continuousOn_const

lemma hd_pointwise_expand (G : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) (t : ℝ) (ht : (t : ℂ) - z ≠ 0) :
    G (t : ℂ) * ((t : ℂ) - z)⁻¹ =
      -z⁻¹ * G (t : ℂ) - (z ^ 2)⁻¹ * ((t : ℂ) * G (t : ℂ)) +
        (z ^ 2)⁻¹ * ((t : ℂ) ^ 2 * G (t : ℂ) * ((t : ℂ) - z)⁻¹) := by
  field_simp
  ring

/-- **The pointwise Cauchy-moment bound** (`ct:dyadic` Part (2)): for `z ∈ D_+`, `ρ ≤ ‖z‖ ≤ A/4`,
`2π ‖G z‖ ≤ Σ/ρ + AΣ/ρ² + 4Σ/(3A) + ρ⁻² ∫_{-A}^A t² ‖G t‖ / ‖z - t‖ dt`, `Σ = hdArcMass A G`. -/
theorem hd_moment_pointwise {G : ℂ → ℂ} {A ρ : ℝ} {z : ℂ} (hA : 0 < A) (hρ : 0 < ρ)
    (hz : z ∈ openHalfDisc A) (hz4 : ‖z‖ ≤ A / 4) (hzρ : ρ ≤ ‖z‖)
    (hc : ContinuousOn G (closedHalfDisc A)) (hd : DifferentiableOn ℂ G (openHalfDisc A)) :
    2 * π * ‖G z‖ ≤ hdArcMass A G / ρ + A * hdArcMass A G / ρ ^ 2 + 4 * hdArcMass A G / (3 * A) +
      (ρ ^ 2)⁻¹ * ∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖G (t : ℂ)‖ / ‖z - t‖ := by
  have hz0 : z ≠ 0 := ne_zero_of_mem hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hcf := hdBoundary_cauchy_formula hA hz hc hd
  unfold hdBoundary at hcf
  set D : ℂ := ∫ t in (-A)..A, G (t : ℂ) * ((t : ℂ) - z)⁻¹ with hD
  set Ar : ℂ := ∫ y in (0 : ℝ)..π, G (A * Complex.exp (y * I)) * (A * Complex.exp (y * I) - z)⁻¹ *
    (A * Complex.exp (y * I)) with hAr
  have hcf' : D + I * Ar = 2 * π * I * G z := hcf
  have hnorm : 2 * π * ‖G z‖ ≤ ‖D‖ + ‖Ar‖ := by
    have h1 : ‖2 * π * I * G z‖ = 2 * π * ‖G z‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      simp
    rw [← h1, ← hcf']
    calc ‖D + I * Ar‖ ≤ ‖D‖ + ‖I * Ar‖ := norm_add_le _ _
      _ = ‖D‖ + ‖Ar‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  -- the arc term
  have hAr_le : ‖Ar‖ ≤ 4 * hdArcMass A G / (3 * A) := by
    have hint : IntervalIntegrable (fun y : ℝ => 4 / (3 * A) * (‖G (A * Complex.exp (y * I))‖ * A))
        volume 0 π :=
      (continuousOn_const.mul (arcNorm_continuousOn hA hc)).intervalIntegrable_of_Icc Real.pi_pos.le
    have := intervalIntegral.norm_integral_le_of_norm_le Real.pi_pos.le
      (f := fun y : ℝ => G (A * Complex.exp (y * I)) * (A * Complex.exp (y * I) - z)⁻¹ *
        (A * Complex.exp (y * I)))
      (g := fun y : ℝ => 4 / (3 * A) * (‖G (A * Complex.exp (y * I))‖ * A))
      (Filter.Eventually.of_forall fun y _ => by
        rw [norm_mul, norm_mul, norm_inv, norm_arc A y hA]
        have hlow : 3 * A / 4 ≤ ‖(A : ℂ) * Complex.exp (y * I) - z‖ := by
          have := norm_sub_norm_le ((A : ℂ) * Complex.exp (y * I)) z
          rw [norm_arc A y hA] at this
          linarith
        have hpos : 0 < ‖(A : ℂ) * Complex.exp (y * I) - z‖ := by linarith
        have hinv : (‖(A : ℂ) * Complex.exp (y * I) - z‖)⁻¹ ≤ 4 / (3 * A) := by
          rw [inv_le_comm₀ hpos (by positivity)]
          calc (4 / (3 * A))⁻¹ = 3 * A / 4 := by field_simp
            _ ≤ _ := hlow
        calc ‖G (A * Complex.exp (y * I))‖ * (‖(A : ℂ) * Complex.exp (y * I) - z‖)⁻¹ * A
            ≤ ‖G (A * Complex.exp (y * I))‖ * (4 / (3 * A)) * A := by gcongr
          _ = 4 / (3 * A) * (‖G (A * Complex.exp (y * I))‖ * A) := by ring) hint
    refine this.trans (le_of_eq ?_)
    unfold hdArcMass
    rw [intervalIntegral.integral_const_mul]
    ring
  -- the diameter term
  have hz_ne : ∀ t : ℝ, (t : ℂ) - z ≠ 0 := fun t h => by
    have := congrArg Complex.im (sub_eq_zero.mp h)
    simp at this; linarith [hz.2]
  have hGcont : ContinuousOn (fun t : ℝ => G (t : ℂ)) (Icc (-A) A) :=
    (BdCont.of_closed hA hc).1
  have hinvc : Continuous (fun t : ℝ => ((t : ℂ) - z)⁻¹) :=
    continuous_iff_continuousAt.2 fun t => ((Complex.continuous_ofReal.sub continuous_const).continuousAt).inv₀ (hz_ne t)
  have hi0 : IntervalIntegrable (fun t : ℝ => G (t : ℂ)) volume (-A) A :=
    hGcont.intervalIntegrable_of_Icc (by linarith)
  have hi1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) * G (t : ℂ)) volume (-A) A :=
    (Complex.continuous_ofReal.continuousOn.mul hGcont).intervalIntegrable_of_Icc (by linarith)
  have hi2 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ 2 * G (t : ℂ) * ((t : ℂ) - z)⁻¹) volume (-A) A :=
    (((Complex.continuous_ofReal.continuousOn.pow 2).mul hGcont).mul hinvc.continuousOn).intervalIntegrable_of_Icc
      (by linarith)
  have hDeq : D = -z⁻¹ * (∫ t in (-A)..A, G (t : ℂ)) - (z ^ 2)⁻¹ * (∫ t in (-A)..A, (t : ℂ) * G (t : ℂ)) +
      (z ^ 2)⁻¹ * (∫ t in (-A)..A, (t : ℂ) ^ 2 * G (t : ℂ) * ((t : ℂ) - z)⁻¹) := by
    rw [hD]
    have : ∀ t ∈ uIcc (-A) A, G (t : ℂ) * ((t : ℂ) - z)⁻¹ =
        -z⁻¹ * G (t : ℂ) - (z ^ 2)⁻¹ * ((t : ℂ) * G (t : ℂ)) +
          (z ^ 2)⁻¹ * ((t : ℂ) ^ 2 * G (t : ℂ) * ((t : ℂ) - z)⁻¹) := fun t _ =>
      hd_pointwise_expand G hz0 t (hz_ne t)
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    · exact hi0.const_mul _
    · exact hi1.const_mul _
    · exact (hi0.const_mul _).sub (hi1.const_mul _)
    · exact hi2.const_mul _
  have hm0 := hd_moment_zero hA hc hd
  have hm1 := hd_moment_one hA hc hd
  set S := hdArcMass A G with hS
  have hS0 : 0 ≤ S := hdArcMass_nonneg hA G
  have hI2 : ‖∫ t in (-A)..A, (t : ℂ) ^ 2 * G (t : ℂ) * ((t : ℂ) - z)⁻¹‖ ≤
      ∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖G (t : ℂ)‖ / ‖z - t‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [norm_sub_rev]
    ring
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hz2 : ρ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hρ.le hzρ 2
  have hDle : ‖D‖ ≤ S / ρ + A * S / ρ ^ 2 +
      (ρ ^ 2)⁻¹ * ∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖G (t : ℂ)‖ / ‖z - t‖ := by
    rw [hDeq]
    have e1 : ‖-z⁻¹ * (∫ t in (-A)..A, G (t : ℂ))‖ ≤ S / ρ := by
      rw [norm_mul, norm_neg, norm_inv]
      calc ‖z‖⁻¹ * ‖∫ t in (-A)..A, G (t : ℂ)‖ ≤ ρ⁻¹ * S := by
            gcongr
        _ = S / ρ := by ring
    have e2 : ‖(z ^ 2)⁻¹ * (∫ t in (-A)..A, (t : ℂ) * G (t : ℂ))‖ ≤ A * S / ρ ^ 2 := by
      rw [norm_mul, norm_inv, norm_pow]
      calc (‖z‖ ^ 2)⁻¹ * ‖∫ t in (-A)..A, (t : ℂ) * G (t : ℂ)‖ ≤ (ρ ^ 2)⁻¹ * (A * S) := by
            gcongr
        _ = A * S / ρ ^ 2 := by ring
    have e3 : ‖(z ^ 2)⁻¹ * (∫ t in (-A)..A, (t : ℂ) ^ 2 * G (t : ℂ) * ((t : ℂ) - z)⁻¹)‖ ≤
        (ρ ^ 2)⁻¹ * ∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖G (t : ℂ)‖ / ‖z - t‖ := by
      rw [norm_mul, norm_inv, norm_pow]
      gcongr
    refine (norm_add_le _ _).trans ?_
    have h2 := norm_sub_le (-z⁻¹ * (∫ t in (-A)..A, G (t : ℂ)))
      ((z ^ 2)⁻¹ * (∫ t in (-A)..A, (t : ℂ) * G (t : ℂ)))
    linarith [e1, e2, e3, h2]
  linarith

/-! ### The area integral of the pointwise bound over the annular half-sector -/

lemma norm_sub_ofReal_pos {z : ℂ} (hz : 0 < z.im) (t : ℝ) : 0 < ‖z - (t : ℂ)‖ := by
  rw [norm_pos_iff, sub_ne_zero]
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The real kernel integral is bounded by the corresponding lower integral over the open diameter. -/
lemma hd_kernel_lintegral_le {G : ℂ → ℂ} {A : ℝ} (hA : 0 < A) (hc : ContinuousOn G (closedHalfDisc A))
    {z : ℂ} (hz : 0 < z.im) :
    ENNReal.ofReal (∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖G (t : ℂ)‖ / ‖z - t‖) ≤
      ∫⁻ t in Ioo (-A) A, ENNReal.ofReal ((t : ℝ) ^ 2 * ‖G (t : ℂ)‖) * (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹ := by
  have hGc : ContinuousOn (fun t : ℝ => ‖G (t : ℂ)‖) (Icc (-A) A) := (BdCont.of_closed hA hc).1.norm
  have hcont : ContinuousOn (fun t : ℝ => (t : ℝ) ^ 2 * ‖G (t : ℂ)‖ / ‖z - t‖) (Icc (-A) A) := by
    refine ContinuousOn.div ((continuousOn_id.pow 2).mul hGc) ?_ fun t _ => (norm_sub_ofReal_pos hz t).ne'
    exact (continuous_const.sub Complex.continuous_ofReal).norm.continuousOn
  have hint : IntegrableOn (fun t : ℝ => (t : ℝ) ^ 2 * ‖G (t : ℂ)‖ / ‖z - t‖) (Ioo (-A) A) :=
    (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioo fun t _ =>
      div_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (norm_nonneg _))]
  refine le_of_eq (setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_)
  rw [ENNReal.ofReal_div_of_pos (norm_sub_ofReal_pos hz t), div_eq_mul_inv]

open scoped ENNReal in
/-- **Area bound for the Cauchy-moment estimate** (`ct:dyadic` Part (2)): over the annular half-sector
`r ∈ (r₀, 3r₀/2]`, `φ ∈ (0, π)`, composed with a map `ζ` landing in `{ρ ≤ ‖z‖ ≤ A/4}` in the open half-disc and satisfying the
inverse-norm area bound `∫∫ r ‖ζ(re^{iφ}) - t‖⁻¹ ≤ K r₀` for every `t ∈ (-A, A)`,
`∫∫ r ‖G(ζ(re^{iφ}))‖ dφ dr ≤ (3 r₀²/8) B₀ + K r₀ S₂ / (2πρ²)`,
`B₀ = Σ/ρ + AΣ/ρ² + 4Σ/(3A)`, `Σ = hdArcMass A G`, `S₂ = ∫_{-A}^A t²‖G(t)‖ dt`. -/
theorem hd_moment_area {G : ℂ → ℂ} {A ρ r₀ K : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hr₀ : 0 < r₀) (hK : 0 ≤ K)
    (hc : ContinuousOn G (closedHalfDisc A)) (hd : DifferentiableOn ℂ G (openHalfDisc A))
    (ζ : ℂ → ℂ) (hζc : ContinuousOn ζ {w : ℂ | r₀ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r₀})
    (hζ : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
      ζ ((r : ℂ) * Complex.exp (φ * I)) ∈ openHalfDisc A ∧ ρ ≤ ‖ζ ((r : ℂ) * Complex.exp (φ * I))‖ ∧
        ‖ζ ((r : ℂ) * Complex.exp (φ * I))‖ ≤ A / 4)
    (hinv : ∀ t ∈ Ioo (-A) A,
      ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
        ENNReal.ofReal p.1 * (ENNReal.ofReal ‖ζ ((p.1 : ℂ) * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹ ≤
          ENNReal.ofReal (K * r₀)) :
    ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
        ENNReal.ofReal (r * ‖G (ζ ((r : ℂ) * Complex.exp (φ * I)))‖) ≤
      ENNReal.ofReal (3 * r₀ ^ 2 / 8 *
          (hdArcMass A G / ρ + A * hdArcMass A G / ρ ^ 2 + 4 * hdArcMass A G / (3 * A)) +
        K * r₀ * (∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖G (t : ℂ)‖) / (2 * π * ρ ^ 2)) := by
  have hpi := Real.pi_pos
  have hSig := hdArcMass_nonneg hA G
  set B0 : ℝ := hdArcMass A G / ρ + A * hdArcMass A G / ρ ^ 2 + 4 * hdArcMass A G / (3 * A) with hB0
  have hB0nn : 0 ≤ B0 := by rw [hB0]; positivity
  set S₂ : ℝ := ∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖G (t : ℂ)‖ with hS₂
  set P : Set (ℝ × ℝ) := (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π) with hP
  have hPm : MeasurableSet P := measurableSet_Ioc.prod measurableSet_Ioo
  set W : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((t : ℝ) ^ 2 * ‖G (t : ℂ)‖) with hW
  let Z : ℝ × ℝ → ℂ := fun p => ζ ((p.1 : ℂ) * Complex.exp (p.2 * I))
  let Fk : ℝ × ℝ → ℝ → ℝ≥0∞ := fun p t => W t * (ENNReal.ofReal p.1 * (ENNReal.ofReal ‖Z p - (t : ℂ)‖)⁻¹)
  set c1 : ℝ≥0∞ := ENNReal.ofReal (3 / 2 * r₀ * B0 / (2 * π)) with hc1
  set C2 : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * π * ρ ^ 2)) with hC2
  -- pointwise bound
  have h_pt : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
      ENNReal.ofReal (r * ‖G (ζ ((r : ℂ) * Complex.exp (φ * I)))‖) ≤
        c1 + C2 * ∫⁻ t in Ioo (-A) A, Fk (r, φ) t := by
    intro r hr φ hφ
    have hr0 : 0 < r := by linarith [hr.1]
    obtain ⟨hmem, hρle, h4⟩ := hζ r hr φ hφ
    have hp := hd_moment_pointwise hA hρ hmem h4 hρle hc hd
    have hKl := hd_kernel_lintegral_le hA hc hmem.2
    set z := ζ ((r : ℂ) * Complex.exp (φ * I)) with hz
    set Kint := ∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖G (t : ℂ)‖ / ‖z - t‖ with hKint
    have hKnn : 0 ≤ Kint := intervalIntegral.integral_nonneg (by linarith) fun t _ =>
      div_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    have hG : ‖G z‖ ≤ (B0 + (ρ ^ 2)⁻¹ * Kint) / (2 * π) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h1 : r * ‖G z‖ ≤ r * B0 / (2 * π) + 1 / (2 * π * ρ ^ 2) * (r * Kint) := by
      calc r * ‖G z‖ ≤ r * ((B0 + (ρ ^ 2)⁻¹ * Kint) / (2 * π)) := by gcongr
        _ = r * B0 / (2 * π) + 1 / (2 * π * ρ ^ 2) * (r * Kint) := by field_simp
    have h2 : r * B0 / (2 * π) ≤ 3 / 2 * r₀ * B0 / (2 * π) := by
      have : r ≤ 3 / 2 * r₀ := hr.2
      gcongr
    have h3 : r * ‖G z‖ ≤ 3 / 2 * r₀ * B0 / (2 * π) + 1 / (2 * π * ρ ^ 2) * (r * Kint) := by linarith
    calc ENNReal.ofReal (r * ‖G z‖)
        ≤ ENNReal.ofReal (3 / 2 * r₀ * B0 / (2 * π) + 1 / (2 * π * ρ ^ 2) * (r * Kint)) :=
          ENNReal.ofReal_le_ofReal h3
      _ = c1 + C2 * (ENNReal.ofReal r * ENNReal.ofReal Kint) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul hr0.le]
      _ ≤ c1 + C2 * (ENNReal.ofReal r * ∫⁻ t in Ioo (-A) A, W t * (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹) := by
          gcongr
      _ = c1 + C2 * ∫⁻ t in Ioo (-A) A, Fk (r, φ) t := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 3
          funext t
          simp only [Fk, Z]
          ring
  -- measurability
  have hZ_aem : AEMeasurable Z (volume.restrict P) := by
    refine ContinuousOn.aemeasurable ?_ hPm
    refine hζc.comp (by fun_prop) fun p hp => ?_
    have hp1 : 0 < p.1 := by linarith [hp.1.1]
    refine ⟨?_, ?_⟩ <;>
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp1,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        linarith [hp.1.1, hp.1.2]
  have hGc' : ContinuousOn (fun t : ℝ => ‖G (t : ℂ)‖) (Icc (-A) A) := (BdCont.of_closed hA hc).1.norm
  have hWc : ContinuousOn (fun t : ℝ => (t : ℝ) ^ 2 * ‖G (t : ℂ)‖) (Icc (-A) A) :=
    (continuousOn_id.pow 2).mul hGc'
  have hW_aem : AEMeasurable W (volume.restrict (Ioo (-A) A)) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hWc.mono Ioo_subset_Icc_self)).aemeasurable
      measurableSet_Ioo
  have hF_aem : AEMeasurable (Function.uncurry Fk)
      ((volume.restrict P).prod (volume.restrict (Ioo (-A) A))) := by
    refine AEMeasurable.mul ?_ ?_
    · exact hW_aem.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    · exact ((ENNReal.continuous_ofReal.comp (continuous_fst.comp continuous_fst)).aemeasurable).mul
        ((AEMeasurable.ennreal_ofReal
          ((hZ_aem.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).sub
            (Complex.continuous_ofReal.comp continuous_snd).aemeasurable).norm).inv)
  have h_tonelli : ∫⁻ p in P, ∫⁻ t in Ioo (-A) A, Fk p t = ∫⁻ t in Ioo (-A) A, ∫⁻ p in P, Fk p t :=
    lintegral_lintegral_swap hF_aem
  have hWint : ∫⁻ t in Ioo (-A) A, W t = ENNReal.ofReal S₂ := by
    have hint : IntegrableOn (fun t : ℝ => (t : ℝ) ^ 2 * ‖G (t : ℂ)‖) (Ioo (-A) A) :=
      hWc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    rw [hS₂, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioo fun t _ =>
        mul_nonneg (sq_nonneg _) (norm_nonneg _))]
  have hS₂nn : 0 ≤ S₂ := intervalIntegral.integral_nonneg (by linarith) fun t _ =>
    mul_nonneg (sq_nonneg _) (norm_nonneg _)
  have h_inner : ∀ t ∈ Ioo (-A) A, ∫⁻ p in P, Fk p t ≤ W t * ENNReal.ofReal (K * r₀) := by
    intro t ht
    have h_pull : ∫⁻ p in P, Fk p t =
        W t * ∫⁻ p in P, ENNReal.ofReal p.1 * (ENNReal.ofReal ‖Z p - (t : ℂ)‖)⁻¹ :=
      lintegral_const_mul' _ _ (by simp [hW])
    rw [h_pull]
    gcongr
    exact hinv t ht
  have h_triple : ∫⁻ p in P, ∫⁻ t in Ioo (-A) A, Fk p t ≤ ENNReal.ofReal (K * r₀) * ENNReal.ofReal S₂ := by
    rw [h_tonelli]
    calc ∫⁻ t in Ioo (-A) A, ∫⁻ p in P, Fk p t ≤ ∫⁻ t in Ioo (-A) A, W t * ENNReal.ofReal (K * r₀) :=
          setLIntegral_mono' measurableSet_Ioo h_inner
      _ = ENNReal.ofReal (K * r₀) * ∫⁻ t in Ioo (-A) A, W t := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact setLIntegral_congr_fun measurableSet_Ioo fun t _ => mul_comm _ _
      _ = ENNReal.ofReal (K * r₀) * ENNReal.ofReal S₂ := by rw [hWint]
  have h_prod_eq : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π, ∫⁻ t in Ioo (-A) A, Fk (r, φ) t =
      ∫⁻ p in P, ∫⁻ t in Ioo (-A) A, Fk p t := by
    have h_vol : (volume : Measure (ℝ × ℝ)).restrict P =
        (volume.restrict (Ioc r₀ (3 / 2 * r₀))).prod (volume.restrict (Ioo (0 : ℝ) π)) := by
      rw [hP, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [h_vol, lintegral_prod]
    exact (AEMeasurable.lintegral_prod_right' (h_vol ▸ hF_aem))
  have hC2top : C2 ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
        ENNReal.ofReal (r * ‖G (ζ ((r : ℂ) * Complex.exp (φ * I)))‖)
      ≤ ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
          (c1 + C2 * ∫⁻ t in Ioo (-A) A, Fk (r, φ) t) :=
        setLIntegral_mono' measurableSet_Ioc fun r hr =>
          setLIntegral_mono' measurableSet_Ioo fun φ hφ => h_pt r hr φ hφ
    _ = ∫⁻ r in Ioc r₀ (3 / 2 * r₀), (c1 * volume (Ioo (0 : ℝ) π) +
          C2 * ∫⁻ φ in Ioo (0 : ℝ) π, ∫⁻ t in Ioo (-A) A, Fk (r, φ) t) := by
        refine lintegral_congr fun r => ?_
        rw [lintegral_add_left measurable_const, setLIntegral_const, lintegral_const_mul' _ _ hC2top]
    _ = c1 * volume (Ioo (0 : ℝ) π) * volume (Ioc r₀ (3 / 2 * r₀)) +
          C2 * ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π, ∫⁻ t in Ioo (-A) A, Fk (r, φ) t := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, lintegral_const_mul' _ _ hC2top]
    _ = c1 * volume (Ioo (0 : ℝ) π) * volume (Ioc r₀ (3 / 2 * r₀)) +
          C2 * ∫⁻ p in P, ∫⁻ t in Ioo (-A) A, Fk p t := by rw [h_prod_eq]
    _ ≤ c1 * volume (Ioo (0 : ℝ) π) * volume (Ioc r₀ (3 / 2 * r₀)) +
          C2 * (ENNReal.ofReal (K * r₀) * ENNReal.ofReal S₂) := by gcongr
    _ = ENNReal.ofReal (3 * r₀ ^ 2 / 8 * B0 + K * r₀ * S₂ / (2 * π * ρ ^ 2)) := by
        simp only [Real.volume_Ioc, Real.volume_Ioo, sub_zero,
          show 3 / 2 * r₀ - r₀ = r₀ / 2 by ring]
        rw [hc1, hC2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring

/-- info: 'FormalResearch.HalfDiscCauchy.hd_moment_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.HalfDiscCauchy.hd_moment_pointwise

/-- info: 'FormalResearch.HalfDiscCauchy.hd_moment_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.HalfDiscCauchy.hd_moment_area

end FormalResearch.HalfDiscCauchy
