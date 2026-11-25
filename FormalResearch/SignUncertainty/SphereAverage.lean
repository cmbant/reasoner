module

public import FormalResearch.SignUncertainty.SpherePolar
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Radial averaging commutes with the Fourier transform on `ℝ^{n+1}`

For `f` integrable on `ℝ^{n+1}`, the radial average `radialAvg f x = |S^n|⁻¹ ∫_{S^n} f(‖x‖ ω) dω` is integrable
(`integrable_radialAvg`) and `𝓕 (radialAvg f) y = |S^n|⁻¹ ∫_{S^n} 𝓕 f(‖y‖ ω) dω` (`fourier_radialAvg`).
Proof: polar coordinates (`integral_polar`), Fubini on `S^n × ℝ^{n+1}`, and the rotation invariance of the
sphere measure (`sphere_integral_inner_eq`), which makes `∫_ω e^{-2πi⟪v,ω⟫} dω` a function `Ψ(‖v‖)`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace Pointwise FourierTransform Real

namespace FormalResearch.SignUncertainty

/-- The character `a ↦ e^{-2πi a}`. -/
noncomputable def fchar (a : ℝ) : ℂ := Complex.exp (((-2 * Real.pi * a : ℝ) : ℂ) * Complex.I)

lemma norm_fchar (a : ℝ) : ‖fchar a‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma continuous_fchar : Continuous fchar := by unfold fchar; fun_prop

lemma fourier_eq_fchar {d : ℕ} (g : EuclSp d → ℂ) (w : EuclSp d) :
    𝓕 g w = ∫ v, fchar (⟪v, w⟫) * g v := by
  rw [Real.fourier_eq']
  simp [fchar, smul_eq_mul]

variable {n : ℕ}

/-- The spherical mean `∫_{S^n} f(r ω) dω` (unnormalised). -/
noncomputable def sphMean (f : EuclSp (n + 1) → ℂ) (r : ℝ) : ℂ :=
  ∫ ω : USph (n + 1), f (r • (ω : EuclSp (n + 1))) ∂sphMeas (n + 1)

/-- The total mass `|S^n|` of the sphere. -/
noncomputable def sphTotal (n : ℕ) : ℝ := (sphMeas (n + 1)).real univ

lemma sphTotal_pos (n : ℕ) : 0 < sphTotal n := by
  unfold sphTotal sphMeas
  rw [Measure.real, Measure.toSphere_apply_univ]
  simp only [finrank_euclideanSpace_fin]
  refine ENNReal.toReal_pos ?_ ?_
  · have := (Metric.measure_ball_pos (volume : Measure (EuclSp (n + 1))) (0 : EuclSp (n + 1)) one_pos).ne'
    simp [this]
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne

/-- The radial average `|S^n|⁻¹ ∫_{S^n} f(‖x‖ ω) dω`. -/
noncomputable def radialAvg (f : EuclSp (n + 1) → ℂ) (x : EuclSp (n + 1)) : ℂ :=
  ((sphTotal n : ℝ) : ℂ)⁻¹ * sphMean f ‖x‖

/-- `Ψ(t) = ∫_ω e^{-2πi t ⟪e₀, ω⟫} dω`. -/
noncomputable def sphPsi (n : ℕ) (t : ℝ) : ℂ :=
  ∫ ω : USph (n + 1), fchar (t * ⟪(EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) : EuclSp (n + 1)),
    (ω : EuclSp (n + 1))⟫) ∂sphMeas (n + 1)

lemma sphere_fchar_eq (v : EuclSp (n + 1)) :
    ∫ ω : USph (n + 1), fchar (⟪v, (ω : EuclSp (n + 1))⟫) ∂sphMeas (n + 1) = sphPsi n ‖v‖ := by
  set e : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) with he
  have hne : ‖e‖ = 1 := by rw [he, PiLp.norm_single]; simp
  have hw : ‖v‖ = ‖‖v‖ • e‖ := by rw [norm_smul, hne]; simp
  rw [sphere_integral_inner_eq fchar hw]
  unfold sphPsi
  simp only [real_inner_smul_left]
  rfl

lemma integrable_radialAvg {f : EuclSp (n + 1) → ℂ} (hf : Integrable f) :
    Integrable (radialAvg f) := by
  have := (integrable_fun_norm_addHaar (volume : Measure (EuclSp (n + 1)))
    (f := fun r : ℝ => ((sphTotal n : ℝ) : ℂ)⁻¹ * sphMean f r)).2
  rw [finrank_euclSp_sub_one] at this
  refine this ?_
  have h := (integrableOn_polar hf).const_mul (((sphTotal n : ℝ) : ℂ)⁻¹)
  refine IntegrableOn.congr_fun h (fun r _ => ?_) measurableSet_Ioi
  simp only [sphMean, Complex.real_smul]
  push_cast
  ring

/-- **Radial averaging commutes with the Fourier transform**:
`𝓕 (radialAvg f) y = |S^n|⁻¹ ∫_{S^n} 𝓕 f(‖y‖ ω) dω`. -/
theorem fourier_radialAvg {f : EuclSp (n + 1) → ℂ} (hf : Integrable f) (y : EuclSp (n + 1)) :
    𝓕 (radialAvg f) y = ((sphTotal n : ℝ) : ℂ)⁻¹ *
      ∫ ω : USph (n + 1), 𝓕 f (‖y‖ • (ω : EuclSp (n + 1))) ∂sphMeas (n + 1) := by
  set c : ℂ := ((sphTotal n : ℝ) : ℂ)⁻¹ with hc
  set ρ : ℝ := ‖y‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg y
  have hL : 𝓕 (radialAvg f) y =
      ∫ r in Ioi (0 : ℝ), (r ^ n : ℝ) • (c * sphMean f r * sphPsi n (r * ρ)) := by
    rw [fourier_eq_fchar]
    have h1 : Integrable (fun x : EuclSp (n + 1) => fchar (⟪x, y⟫) * radialAvg f x) :=
      (integrable_radialAvg hf).bdd_mul (c := 1)
        (continuous_fchar.comp (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun x => (norm_fchar _).le)
    rw [integral_polar h1]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    congr 1
    have key : ∀ ω : USph (n + 1), fchar (⟪r • (ω : EuclSp (n + 1)), y⟫) *
        radialAvg f (r • (ω : EuclSp (n + 1))) = (c * sphMean f r) * fchar (⟪r • y, (ω : EuclSp (n + 1))⟫) := by
      intro ω
      have hn : ‖r • (ω : EuclSp (n + 1))‖ = r := by
        rw [norm_smul, mem_sphere_zero_iff_norm.1 ω.2, Real.norm_eq_abs, abs_of_pos hr0, mul_one]
      have e1 : ⟪r • (ω : EuclSp (n + 1)), y⟫ = ⟪r • y, (ω : EuclSp (n + 1))⟫ := by
        rw [real_inner_smul_left, real_inner_smul_left, real_inner_comm]
      rw [e1]
      simp only [radialAvg, hn]
      ring
    simp_rw [key]
    rw [integral_const_mul, sphere_fchar_eq (r • y), norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
  set K : EuclSp (n + 1) → ℂ := fun x => ∫ ω : USph (n + 1),
    fchar (⟪x, ρ • (ω : EuclSp (n + 1))⟫) ∂sphMeas (n + 1) with hK
  have hKcont : Continuous K := by
    refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun x => ?_) (fun x => ?_)
      (integrable_const _) (Eventually.of_forall fun ω => ?_)
    · exact (continuous_fchar.comp (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall fun ω => (norm_fchar _).le
    · exact continuous_fchar.comp (by fun_prop)
  have hKb : ∀ x, ‖K x‖ ≤ sphTotal n := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := sphMeas (n + 1)) (C := 1)
      (f := fun ω : USph (n + 1) => fchar (⟪x, ρ • (ω : EuclSp (n + 1))⟫))
      (Eventually.of_forall fun ω => (norm_fchar _).le)
    simpa [sphTotal] using this
  have hR : ∫ ω : USph (n + 1), 𝓕 f (ρ • (ω : EuclSp (n + 1))) ∂sphMeas (n + 1) =
      ∫ r in Ioi (0 : ℝ), (r ^ n : ℝ) • (sphPsi n (r * ρ) * sphMean f r) := by
    simp_rw [fourier_eq_fchar]
    have hint2 : Integrable (fun p : USph (n + 1) × EuclSp (n + 1) =>
        fchar (⟪p.2, ρ • (p.1 : EuclSp (n + 1))⟫) * f p.2) ((sphMeas (n + 1)).prod volume) :=
      ((hf.comp_snd (sphMeas (n + 1))).bdd_mul (c := 1)
        (continuous_fchar.comp (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun p => (norm_fchar _).le))
    rw [integral_integral_swap (f := fun (ω : USph (n + 1)) (x : EuclSp (n + 1)) =>
      fchar (⟪x, ρ • (ω : EuclSp (n + 1))⟫) * f x) hint2]
    have hmul : ∀ x : EuclSp (n + 1), ∫ ω : USph (n + 1),
        fchar (⟪x, ρ • (ω : EuclSp (n + 1))⟫) * f x ∂sphMeas (n + 1) = K x * f x :=
      fun x => integral_mul_const _ _
    simp_rw [hmul]
    have hh2 : Integrable (fun x => K x * f x) :=
      hf.bdd_mul (c := sphTotal n) hKcont.aestronglyMeasurable (Eventually.of_forall hKb)
    rw [integral_polar hh2]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    congr 1
    have key : ∀ ω : USph (n + 1), K (r • (ω : EuclSp (n + 1))) * f (r • (ω : EuclSp (n + 1))) =
        sphPsi n (r * ρ) * f (r • (ω : EuclSp (n + 1))) := by
      intro ω
      have hn : ‖r • (ω : EuclSp (n + 1))‖ = r := by
        rw [norm_smul, mem_sphere_zero_iff_norm.1 ω.2, Real.norm_eq_abs, abs_of_pos hr0, mul_one]
      congr 1
      have e1 : ∀ ω' : USph (n + 1), ⟪r • (ω : EuclSp (n + 1)), ρ • (ω' : EuclSp (n + 1))⟫ =
          ⟪ρ • (r • (ω : EuclSp (n + 1))), (ω' : EuclSp (n + 1))⟫ := fun ω' => by
        simp only [real_inner_smul_left, real_inner_smul_right]
      simp only [hK, e1]
      rw [sphere_fchar_eq, norm_smul, hn, Real.norm_eq_abs, abs_of_nonneg hρ0, mul_comm]
    simp_rw [key]
    rw [integral_const_mul]
    rfl
  rw [hL, hR, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  simp only [Complex.real_smul]
  ring

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.fourier_radialAvg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_radialAvg

end FormalResearch.SignUncertainty
