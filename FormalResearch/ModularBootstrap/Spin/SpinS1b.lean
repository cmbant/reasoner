module

public import FormalResearch.ModularBootstrap.Spin.SpinS1bHarmonics
public import FormalResearch.ModularBootstrap.Spin.Statements
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Proof of `SpinS1b` (Theorem S1 (b))

Establishes the radial-lift equivalence and norm/vacuum identities for `a ≥ 2`:
- `spin_polar_integrable_iff`: for continuous `f` on `[0, ∞)` (`f ≥ 0`) and continuous `W ≥ 0` on
  `ℝ × ℝ` whose angular integral on the circle of radius `√(2t)` is `W₀ t`,
  `Integrable (fun p => f ((p.1² + p.2²)/2) * W p) ↔ IntegrableOn (fun t => f t * W₀ t) (Ioi 0)`.
- `spin_polar_integral_eq`: for continuous `g` on `[0, ∞)` with `Integrable (fun p => |g ((p.1²+p.2²)/2)| * W p)`,
  `∫ p, g ((p.1² + p.2²)/2) * W p = ∫ t in Ioi 0, g t * W₀ t`.
- `spinTestClass_radialLift_iff`: `TestClass virasoroProblem a g ↔ SpinTestClass a (spinRadialLift g)`.
- `spinS1b : SpinS1b`: all three clauses of Theorem S1 (b).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Bessel

/-! ### Section 1: Measure-preserving bridge `EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ` -/

private noncomputable def spinE2ToProd : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

private lemma spin_volume_preserving_e2ToProd : MeasurePreserving spinE2ToProd volume volume :=
  (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))

private lemma spinE2ToProd_apply (x : EuclideanSpace ℝ (Fin 2)) :
    spinE2ToProd x = (x 0, x 1) := rfl

private lemma spin_integrable_radialLift_iff (g : ℝ → ℝ) :
    Integrable (radialLift 1 g) ↔ Integrable (spinRadialLift g) := by
  rw [← spinToEuc_radialLift]
  have hreal : Integrable (spinToEuc (spinRadialLift g)) ↔
      Integrable (fun x : EuclideanSpace ℝ (Fin 2) => spinRadialLift g (x 0, x 1)) :=
    ⟨fun h => Complex.reCLM.integrable_comp h, fun h => Complex.ofRealCLM.integrable_comp h⟩
  rw [hreal]
  exact spin_volume_preserving_e2ToProd.integrable_comp_emb
    spinE2ToProd.measurableEmbedding (g := spinRadialLift g)

/-! ### Section 2: Polar-coordinate reduction for radial tests against a weight `W` -/

private lemma spin_quasiMeasurePreserving_polarCoord_symm :
    MeasureTheory.QuasiMeasurePreserving polarCoord.symm
      (volume.restrict polarCoord.target) volume := by
  refine ⟨continuous_polarCoord_symm.measurable.aemeasurable, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [Measure.map_apply continuous_polarCoord_symm.measurable hs]
  have hlin := lintegral_comp_polarCoord_symm (s.indicator (fun _ => (1 : ENNReal)))
  have hrhs : ∫⁻ p : ℝ × ℝ, s.indicator (fun _ => (1 : ENNReal)) p = 0 := by
    rw [lintegral_indicator hs, setLIntegral_one, hs0]
  rw [hrhs] at hlin
  have hae : ∀ᵐ p ∂(volume.restrict polarCoord.target),
      ENNReal.ofReal p.1 • s.indicator (fun _ => (1 : ENNReal)) (polarCoord.symm p) = 0 :=
    (lintegral_eq_zero_iff ((Measurable.ennreal_ofReal measurable_fst).smul
      ((Measurable.indicator measurable_const hs).comp continuous_polarCoord_symm.measurable))).mp hlin
  have hae_mem : ∀ᵐ p ∂(volume.restrict polarCoord.target),
      p ∉ polarCoord.symm ⁻¹' s := by
    rw [ae_restrict_iff' polarCoord.open_target.measurableSet] at hae ⊢
    refine hae.mono fun p hp hpt => ?_
    have hp1 : 0 < p.1 := hpt.1
    have hpos : ENNReal.ofReal p.1 ≠ 0 := (ENNReal.ofReal_pos.mpr hp1).ne'
    have hmul0 : ENNReal.ofReal p.1 * s.indicator (fun _ => (1 : ENNReal)) (polarCoord.symm p) = 0 := by
      simpa [smul_eq_mul] using hp hpt
    have hind0 : s.indicator (fun _ => (1 : ENNReal)) (polarCoord.symm p) = 0 :=
      (mul_eq_zero.mp hmul0).resolve_left hpos
    intro hmem
    have hmem' : polarCoord.symm p ∈ s := hmem
    rw [indicator_of_mem hmem'] at hind0
    exact one_ne_zero hind0
  have heq : {p : ℝ × ℝ | ¬ p ∉ polarCoord.symm ⁻¹' s} = polarCoord.symm ⁻¹' s := by
    ext p; simp
  rw [← heq]
  exact ae_iff.mp hae_mem

private lemma spin_circle_integral_shift {W : ℝ × ℝ → ℝ} (_hW : Continuous W) (r : ℝ) :
    ∫ θ in Ioo (-π) π, W (r * Real.cos θ, r * Real.sin θ) =
      ∫ ψ in (0 : ℝ)..(2 * π), W (r * Real.cos (π / 4 + ψ), r * Real.sin (π / 4 + ψ)) := by
  have hper : Function.Periodic (fun θ => W (r * Real.cos θ, r * Real.sin θ)) (2 * π) := fun θ => by
    dsimp only; rw [Real.cos_add_two_pi, Real.sin_add_two_pi]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have h1 : ∫ θ in (-π)..π, W (r * Real.cos θ, r * Real.sin θ) =
      ∫ θ in (π / 4)..(π / 4 + 2 * π), W (r * Real.cos θ, r * Real.sin θ) := by
    have hshift := hper.intervalIntegral_add_eq (t := -π) (s := π / 4)
    rw [show (-π) + 2 * π = π by ring] at hshift
    exact hshift
  rw [h1]
  have hcomp := intervalIntegral.integral_comp_add_left
    (fun θ => W (r * Real.cos θ, r * Real.sin θ)) (π / 4) (a := (0 : ℝ)) (b := 2 * π)
  rw [add_zero] at hcomp
  exact hcomp.symm

private lemma spin_polar_quad_eq (r θ : ℝ) :
    ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) / 2 = r ^ 2 / 2 := by
  have h : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by
    ring
  rw [h, Real.cos_sq_add_sin_sq, mul_one]

/-- Polar-coordinate integrability criterion for `p ↦ f ((p.1² + p.2²)/2) * W p` with continuous
nonnegative `f` on `[0, ∞)` and continuous nonnegative `W` on `ℝ × ℝ`. -/
theorem spin_polar_integrable_iff {f W₀ : ℝ → ℝ} {W : ℝ × ℝ → ℝ}
    (hf_cont : ContinuousOn f (Ici 0)) (hf_nn : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hW_cont : Continuous W) (hW_nn : ∀ p, 0 ≤ W p)
    (hW₀_cont : ContinuousOn W₀ (Ioi 0))
    (hW_avg : ∀ {t : ℝ}, 0 < t →
      ∫ ψ in (0 : ℝ)..(2 * π),
        W (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ), Real.sqrt (2 * t) * Real.sin (π / 4 + ψ)) =
        W₀ t) :
    Integrable (fun p : ℝ × ℝ => f ((p.1 ^ 2 + p.2 ^ 2) / 2) * W p) ↔
      IntegrableOn (fun t : ℝ => f t * W₀ t) (Ioi 0) := by
  let F : ℝ × ℝ → ℝ := fun p => f ((p.1 ^ 2 + p.2 ^ 2) / 2) * W p
  have hF_cont : Continuous F := by
    have hq : Continuous (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) / 2) := by fun_prop
    exact (hf_cont.comp_continuous hq fun p => mem_Ici.mpr (by positivity)).mul hW_cont
  have hF_nn : ∀ p : ℝ × ℝ, 0 ≤ F p := fun p => mul_nonneg (hf_nn _ (by positivity)) (hW_nn p)
  have hW₀_nn : ∀ t, 0 < t → 0 ≤ W₀ t := by
    intro t ht
    rw [← hW_avg ht]
    exact intervalIntegral.integral_nonneg (by positivity) fun ψ _ => hW_nn _
  have hlin_eq : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (F p) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * (f (r ^ 2 / 2) * W₀ (r ^ 2 / 2))) := by
    rw [← lintegral_comp_polarCoord_symm (fun p => ENNReal.ofReal (F p))]
    have hprod_target : (volume.restrict polarCoord.target : Measure (ℝ × ℝ)) =
        (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π)) := by
      rw [polarCoord_target, Measure.volume_eq_prod ℝ ℝ, Measure.prod_restrict]
    rw [hprod_target]
    simp_rw [smul_eq_mul]
    have hmeas : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal q.1 * ENNReal.ofReal (F (polarCoord.symm q))) :=
      (ENNReal.continuous_ofReal.comp continuous_fst).measurable.mul
        ((ENNReal.continuous_ofReal.comp (hF_cont.comp continuous_polarCoord_symm)).measurable)
    rw [lintegral_prod _ hmeas.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hrp : 0 < r := mem_Ioi.mp hr
    have ht_pos : 0 < r ^ 2 / 2 := by positivity
    have hsqrt : Real.sqrt (2 * (r ^ 2 / 2)) = r := by
      rw [show 2 * (r ^ 2 / 2) = r ^ 2 by ring, Real.sqrt_sq hrp.le]
    have hinner : ∀ θ : ℝ,
        ENNReal.ofReal r * ENNReal.ofReal (F (polarCoord.symm (r, θ))) =
          ENNReal.ofReal (r * f (r ^ 2 / 2)) * ENNReal.ofReal (W (r * Real.cos θ, r * Real.sin θ)) := by
      intro θ
      simp only [F, polarCoord_symm_apply, spin_polar_quad_eq]
      rw [← ENNReal.ofReal_mul hrp.le, ← ENNReal.ofReal_mul (mul_nonneg hrp.le (hf_nn _ ht_pos.le)),
        mul_assoc]
    simp_rw [hinner]
    have hW_circ_cont : Continuous (fun θ : ℝ => W (r * Real.cos θ, r * Real.sin θ)) :=
      hW_cont.comp (by fun_prop)
    rw [lintegral_const_mul _ hW_circ_cont.measurable.ennreal_ofReal]
    have hW_int : IntegrableOn (fun θ => W (r * Real.cos θ, r * Real.sin θ)) (Ioo (-π) π) :=
      hW_circ_cont.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have havg : ∫ ψ in (0 : ℝ)..(2 * π),
        W (r * Real.cos (π / 4 + ψ), r * Real.sin (π / 4 + ψ)) = W₀ (r ^ 2 / 2) := by
      conv_lhs => rw [← hsqrt]
      exact hW_avg ht_pos
    rw [← ofReal_integral_eq_lintegral_ofReal hW_int (Eventually.of_forall fun θ => hW_nn _),
      spin_circle_integral_shift hW_cont r, havg,
      ← ENNReal.ofReal_mul (mul_nonneg hrp.le (hf_nn _ ht_pos.le)), mul_assoc]
  have hr_cont : ContinuousOn (fun r : ℝ => r * (f (r ^ 2 / 2) * W₀ (r ^ 2 / 2))) (Ioi 0) := by
    have hsq : ContinuousOn (fun r : ℝ => r ^ 2 / 2) (Ioi 0) := (by fun_prop : Continuous fun r : ℝ => r ^ 2 / 2).continuousOn
    refine continuousOn_id.mul ((hf_cont.comp hsq fun r _ => mem_Ici.mpr (by positivity)).mul
      (hW₀_cont.comp hsq fun r hr => mem_Ioi.mpr (by have := mem_Ioi.mp hr; positivity)))
  have hr_nn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * (f (r ^ 2 / 2) * W₀ (r ^ 2 / 2)) := fun r hr => by
    have hrp : 0 < r := mem_Ioi.mp hr
    exact mul_nonneg hrp.le (mul_nonneg (hf_nn _ (by positivity)) (hW₀_nn _ (by positivity)))
  have hstep1 : Integrable F ↔
      IntegrableOn (fun r : ℝ => r * (f (r ^ 2 / 2) * W₀ (r ^ 2 / 2))) (Ioi 0) := by
    constructor
    · intro hF_int
      refine ⟨hr_cont.aestronglyMeasurable measurableSet_Ioi, ?_⟩
      change ∫⁻ r in Ioi (0 : ℝ), ‖r * (f (r ^ 2 / 2) * W₀ (r ^ 2 / 2))‖ₑ < ⊤
      have heq : ∫⁻ r in Ioi (0 : ℝ), ‖r * (f (r ^ 2 / 2) * W₀ (r ^ 2 / 2))‖ₑ =
          ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * (f (r ^ 2 / 2) * W₀ (r ^ 2 / 2))) :=
        setLIntegral_congr_fun measurableSet_Ioi fun r hr => by
          rw [Real.eNorm_eq_ofReal (hr_nn r hr)]
      rw [heq, ← hlin_eq]
      have hfin : ∫⁻ p : ℝ × ℝ, ‖F p‖ₑ < ⊤ := hF_int.hasFiniteIntegral
      have heq2 : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (F p) = ∫⁻ p : ℝ × ℝ, ‖F p‖ₑ :=
        lintegral_congr fun p => (Real.eNorm_eq_ofReal (hF_nn p)).symm
      rwa [heq2]
    · intro hr_int
      refine ⟨hF_cont.aestronglyMeasurable, ?_⟩
      change ∫⁻ p : ℝ × ℝ, ‖F p‖ₑ < ⊤
      have heq2 : ∫⁻ p : ℝ × ℝ, ‖F p‖ₑ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (F p) :=
        lintegral_congr fun p => Real.eNorm_eq_ofReal (hF_nn p)
      rw [heq2, hlin_eq]
      have hfin : ∫⁻ r in Ioi (0 : ℝ), ‖r * (f (r ^ 2 / 2) * W₀ (r ^ 2 / 2))‖ₑ < ⊤ :=
        hr_int.hasFiniteIntegral
      have heq : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * (f (r ^ 2 / 2) * W₀ (r ^ 2 / 2))) =
          ∫⁻ r in Ioi (0 : ℝ), ‖r * (f (r ^ 2 / 2) * W₀ (r ^ 2 / 2))‖ₑ :=
        setLIntegral_congr_fun measurableSet_Ioi fun r hr =>
          (Real.eNorm_eq_ofReal (hr_nn r hr)).symm
      rwa [heq]
  rw [hstep1]
  let φ : ℝ → ℝ := fun r => r ^ 2 / 2
  have himg : φ '' Ioi 0 = Ioi 0 := by
    ext t; simp only [Set.mem_image, Set.mem_Ioi, φ]
    constructor
    · rintro ⟨r, hr, rfl⟩; positivity
    · intro ht; refine ⟨Real.sqrt (2 * t), Real.sqrt_pos.mpr (by positivity), ?_⟩
      rw [Real.sq_sqrt (by positivity)]; ring
  have hcov := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := φ) (f' := fun r => r)
    measurableSet_Ioi
    (fun r _ => (((hasDerivAt_pow 2 r).div_const 2).congr_deriv (by ring)).hasDerivWithinAt)
    (fun r₁ hr₁ r₂ hr₂ heq => by
      have hr₁p : 0 < r₁ := Set.mem_Ioi.mp hr₁
      have hr₂p : 0 < r₂ := Set.mem_Ioi.mp hr₂
      have hsq : r₁ ^ 2 = r₂ ^ 2 := by dsimp [φ] at heq; linarith
      nlinarith)
    (fun t : ℝ => f t * W₀ t)
  rw [himg] at hcov
  rw [hcov]
  exact integrableOn_congr_fun (fun r hr => by
    simp only [φ, smul_eq_mul, abs_of_pos (mem_Ioi.mp hr)]) measurableSet_Ioi

/-- Polar-coordinate integral formula for `p ↦ g ((p.1² + p.2²)/2) * W p`. -/
theorem spin_polar_integral_eq {g W₀ : ℝ → ℝ} {W : ℝ × ℝ → ℝ}
    (hW_cont : Continuous W)
    (hW_avg : ∀ {t : ℝ}, 0 < t →
      ∫ ψ in (0 : ℝ)..(2 * π),
        W (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ), Real.sqrt (2 * t) * Real.sin (π / 4 + ψ)) =
        W₀ t)
    (hF_int : Integrable (fun p : ℝ × ℝ => g ((p.1 ^ 2 + p.2 ^ 2) / 2) * W p)) :
    ∫ p : ℝ × ℝ, g ((p.1 ^ 2 + p.2 ^ 2) / 2) * W p =
      ∫ t in Ioi (0 : ℝ), g t * W₀ t := by
  let F : ℝ × ℝ → ℝ := fun p => g ((p.1 ^ 2 + p.2 ^ 2) / 2) * W p
  change ∫ p : ℝ × ℝ, F p = _
  rw [← integral_comp_polarCoord_symm F]
  have hpolar_int : IntegrableOn (fun q : ℝ × ℝ => q.1 • F (polarCoord.symm q))
      polarCoord.target := by
    have haes : AEStronglyMeasurable (fun q : ℝ × ℝ => q.1 • F (polarCoord.symm q))
        (volume.restrict polarCoord.target) :=
      (continuous_fst.aestronglyMeasurable).smul
        (hF_int.aestronglyMeasurable.comp_quasiMeasurePreserving
          spin_quasiMeasurePreserving_polarCoord_symm)
    refine ⟨haes, ?_⟩
    have hlin := lintegral_comp_polarCoord_symm (fun p => ‖F p‖ₑ)
    have hfin : ∫⁻ p : ℝ × ℝ, ‖F p‖ₑ < ⊤ := hF_int.hasFiniteIntegral
    rw [← hlin] at hfin
    refine lt_of_le_of_lt (setLIntegral_mono' polarCoord.open_target.measurableSet ?_) hfin
    intro q hq
    have hq1 : 0 < q.1 := hq.1
    rw [← ofReal_norm, ← ofReal_norm, norm_smul, Real.norm_of_nonneg hq1.le,
      ENNReal.ofReal_mul hq1.le, smul_eq_mul]
  have hprod_target : (volume.restrict polarCoord.target : Measure (ℝ × ℝ)) =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π)) := by
    rw [polarCoord_target, Measure.volume_eq_prod ℝ ℝ, Measure.prod_restrict]
  have hprod_int : Integrable (fun q : ℝ × ℝ => q.1 • F (polarCoord.symm q))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
    rwa [← hprod_target]
  have hfubini : ∫ q in polarCoord.target, q.1 • F (polarCoord.symm q) =
      ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, r • F (polarCoord.symm (r, θ)) := by
    rw [hprod_target, integral_prod _ hprod_int]
  rw [hfubini]
  have hinner : EqOn (fun r : ℝ => ∫ θ in Ioo (-π) π, r • F (polarCoord.symm (r, θ)))
      (fun r : ℝ => r * (g (r ^ 2 / 2) * W₀ (r ^ 2 / 2))) (Ioi 0) := by
    intro r hr
    have hrp : 0 < r := mem_Ioi.mp hr
    have ht_pos : 0 < r ^ 2 / 2 := by positivity
    have hsqrt : Real.sqrt (2 * (r ^ 2 / 2)) = r := by
      rw [show 2 * (r ^ 2 / 2) = r ^ 2 by ring, Real.sqrt_sq hrp.le]
    have hpt : ∀ θ : ℝ, r • F (polarCoord.symm (r, θ)) =
        (r * g (r ^ 2 / 2)) * W (r * Real.cos θ, r * Real.sin θ) := by
      intro θ
      simp only [F, polarCoord_symm_apply, smul_eq_mul, spin_polar_quad_eq]
      ring
    simp_rw [hpt]
    have havg : ∫ ψ in (0 : ℝ)..(2 * π),
        W (r * Real.cos (π / 4 + ψ), r * Real.sin (π / 4 + ψ)) = W₀ (r ^ 2 / 2) := by
      conv_lhs => rw [← hsqrt]
      exact hW_avg ht_pos
    rw [integral_const_mul, spin_circle_integral_shift hW_cont r, havg, mul_assoc]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner]
  let φ : ℝ → ℝ := fun r => r ^ 2 / 2
  have himg : φ '' Ioi 0 = Ioi 0 := by
    ext t; simp only [Set.mem_image, Set.mem_Ioi, φ]
    constructor
    · rintro ⟨r, hr, rfl⟩; positivity
    · intro ht; refine ⟨Real.sqrt (2 * t), Real.sqrt_pos.mpr (by positivity), ?_⟩
      rw [Real.sq_sqrt (by positivity)]; ring
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := φ) (f' := fun r => r)
    measurableSet_Ioi
    (fun r _ => (((hasDerivAt_pow 2 r).div_const 2).congr_deriv (by ring)).hasDerivWithinAt)
    (fun r₁ hr₁ r₂ hr₂ heq => by
      have hr₁p : 0 < r₁ := Set.mem_Ioi.mp hr₁
      have hr₂p : 0 < r₂ := Set.mem_Ioi.mp hr₂
      have hsq : r₁ ^ 2 = r₂ ^ 2 := by dsimp [φ] at heq; linarith
      nlinarith)
    (fun t : ℝ => g t * W₀ t)
  rw [himg] at hcov
  rw [hcov]
  exact setIntegral_congr_fun measurableSet_Ioi fun r hr => by
    simp only [φ, smul_eq_mul, abs_of_pos (mem_Ioi.mp hr)]

/-! ### Section 3: Radial-lift equivalence and `SpinS1b` -/

private lemma spin_V1_prod_avg {a t : ℝ} (ha : 2 ≤ a) (ht : 0 < t) :
    ∫ ψ in (0 : ℝ)..(2 * π),
      spinV1 a (Real.sqrt (2 * t) * Real.cos (π / 4 + ψ)) *
        spinV1 a (Real.sqrt (2 * t) * Real.sin (π / 4 + ψ)) =
      virasoroProblem.cardyDensity a t := by
  have h := spinV2Harmonic_zero_eq_cardyDensity ha ht.le
  unfold spinV2Harmonic at h
  simpa using h

/-- Third clause (equivalence) of `spinnotes:S1`(b): for `a ≥ 2`,
`TestClass virasoroProblem a g ↔ SpinTestClass a (spinRadialLift g)`. -/
theorem spinTestClass_radialLift_iff {a : ℝ} (ha : 2 ≤ a) (g : ℝ → ℝ) :
    TestClass virasoroProblem a g ↔ SpinTestClass a (spinRadialLift g) := by
  have hW_cont : Continuous (fun p : ℝ × ℝ => spinV1 a p.1 * spinV1 a p.2) := by
    have hV1 : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    exact (hV1.comp continuous_fst).mul (hV1.comp continuous_snd)
  have hW_nn : ∀ p : ℝ × ℝ, 0 ≤ spinV1 a p.1 * spinV1 a p.2 := fun p =>
    mul_nonneg (spinV1_nonneg ha p.1) (spinV1_nonneg ha p.2)
  have hW₀_cont : ContinuousOn (virasoroProblem.cardyDensity a) (Ioi 0) :=
    (continuous_const.mul (continuous_cardyV virasoroProblem a)).continuousOn
  have hcont_iff : ContinuousOn g (Ici 0) ↔ Continuous (spinRadialLift g) := by
    constructor
    · intro hg
      have hq : Continuous (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) / 2) := by fun_prop
      exact hg.comp_continuous hq fun p => mem_Ici.mpr (by positivity)
    · intro hΦ
      have hcomp : ContinuousOn (fun t : ℝ => spinRadialLift g (Real.sqrt (2 * t), 0)) (Ici 0) :=
        (hΦ.comp (by fun_prop : Continuous fun t : ℝ => (Real.sqrt (2 * t), (0 : ℝ)))).continuousOn
      refine hcomp.congr fun t ht => ?_
      have ht0 : 0 ≤ t := mem_Ici.mp ht
      simp only [spinRadialLift, zero_pow two_ne_zero, add_zero]
      rw [Real.sq_sqrt (by linarith)]
      congr 1; ring
  constructor
  · intro hg
    have hint_M2 : Integrable (fun p : ℝ × ℝ => |spinRadialLift g p| * spinV1 a p.1 * spinV1 a p.2) := by
      have heq : (fun p : ℝ × ℝ => |spinRadialLift g p| * spinV1 a p.1 * spinV1 a p.2) =
          fun p => |g ((p.1 ^ 2 + p.2 ^ 2) / 2)| * (spinV1 a p.1 * spinV1 a p.2) := by
        ext p; simp only [spinRadialLift]; ring
      rw [heq]
      refine (spin_polar_integrable_iff hg.cont.abs (fun _ _ => abs_nonneg _)
        hW_cont hW_nn hW₀_cont (fun ht => spin_V1_prod_avg ha ht)).mpr ?_
      have hcd : (fun t : ℝ => |g t| * virasoroProblem.cardyDensity a t) =
          fun t => (2 * π) * (|g t| * virasoroProblem.cardyV a t) := by
        ext t; unfold FixedWeightProblem.cardyDensity; ring
      rw [hcd]
      exact hg.int_cardy.const_mul (2 * π)
    exact
      { cont := hcont_iff.mp hg.cont
        int := (spin_integrable_radialLift_iff g).mp hg.int_lift
        d4_inv := spinRadialLift_d4 g
        fourier_odd := by rw [spinToEuc_radialLift]; exact hg.fourier_odd
        int_M2 := hint_M2 }
  · intro hΦ
    have hcont : ContinuousOn g (Ici 0) := hcont_iff.mpr hΦ.cont
    have hint_cardy : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV a t) (Ioi 0) := by
      have hM2' : Integrable (fun p : ℝ × ℝ =>
          |g ((p.1 ^ 2 + p.2 ^ 2) / 2)| * (spinV1 a p.1 * spinV1 a p.2)) :=
        hΦ.int_M2.congr (Eventually.of_forall fun p => by simp only [spinRadialLift]; ring)
      have hcd := (spin_polar_integrable_iff hcont.abs (fun _ _ => abs_nonneg _)
        hW_cont hW_nn hW₀_cont (fun ht => spin_V1_prod_avg ha ht)).mp hM2'
      have hmul : (fun t : ℝ => |g t| * virasoroProblem.cardyV a t) =
          fun t => (2 * π)⁻¹ * (|g t| * virasoroProblem.cardyDensity a t) := by
        ext t; unfold FixedWeightProblem.cardyDensity
        have hpi : (2 * π : ℝ) ≠ 0 := by positivity
        field_simp [hpi]
      rw [hmul]
      exact hcd.const_mul (2 * π)⁻¹
    exact
      { cont := hcont
        int_lift := (spin_integrable_radialLift_iff g).mpr hΦ.int
        fourier_odd := by rw [virasoroProblem_w, ← spinToEuc_radialLift]; exact hΦ.fourier_odd
        int_cardy := hint_cardy }

/-- Third clause (norm and vacuum identities) of `spinnotes:S1`(b): for `a ≥ 2` and
`g ∈ TestClass virasoroProblem a`, `M_2[Φ_g] = 2π M[g]` and `Φ_{g,vac} = g_vac`. -/
theorem spinM2_and_phiVac_radialLift {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) :
    spinM2 a (spinRadialLift g) = 2 * π * virasoroProblem.cardyNorm a g ∧
      spinPhiVac a (spinRadialLift g) = virasoroProblem.gVac a g := by
  have hΦ : SpinTestClass a (spinRadialLift g) := (spinTestClass_radialLift_iff ha g).mp hg
  have hW_cont : Continuous (fun p : ℝ × ℝ => spinV1 a p.1 * spinV1 a p.2) := by
    have hV1 : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    exact (hV1.comp continuous_fst).mul (hV1.comp continuous_snd)
  refine ⟨?_, ?_⟩
  · unfold spinM2 FixedWeightProblem.cardyNorm
    have hM2_int : Integrable (fun p : ℝ × ℝ =>
        |g ((p.1 ^ 2 + p.2 ^ 2) / 2)| * (spinV1 a p.1 * spinV1 a p.2)) :=
      hΦ.int_M2.congr (Eventually.of_forall fun p => by simp only [spinRadialLift]; ring)
    have h1 : ∫ p : ℝ × ℝ, |spinRadialLift g p| * spinV1 a p.1 * spinV1 a p.2 =
        ∫ p : ℝ × ℝ, |g ((p.1 ^ 2 + p.2 ^ 2) / 2)| * (spinV1 a p.1 * spinV1 a p.2) :=
      integral_congr_ae (Eventually.of_forall fun p => by simp only [spinRadialLift]; ring)
    rw [h1, spin_polar_integral_eq (g := fun t => |g t|) hW_cont (fun ht => spin_V1_prod_avg ha ht) hM2_int]
    have h2 : ∫ t in Ioi (0 : ℝ), |g t| * virasoroProblem.cardyDensity a t =
        ∫ t in Ioi (0 : ℝ), (2 * π) * (|g t| * virasoroProblem.cardyV a t) :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        unfold FixedWeightProblem.cardyDensity; ring
    rw [h2, integral_const_mul]
  · unfold spinPhiVac FixedWeightProblem.gVac
    have hvac_int : Integrable (fun p : ℝ × ℝ =>
        g ((p.1 ^ 2 + p.2 ^ 2) / 2) * (spinV1 a p.1 * spinV1 a p.2)) :=
      (hΦ.int_vac ha).congr (Eventually.of_forall fun p => by simp only [spinRadialLift]; ring)
    have h1 : ∫ p : ℝ × ℝ, spinRadialLift g p * spinV1 a p.1 * spinV1 a p.2 =
        ∫ p : ℝ × ℝ, g ((p.1 ^ 2 + p.2 ^ 2) / 2) * (spinV1 a p.1 * spinV1 a p.2) :=
      integral_congr_ae (Eventually.of_forall fun p => by simp only [spinRadialLift]; ring)
    rw [h1, spin_polar_integral_eq hW_cont (fun ht => spin_V1_prod_avg ha ht) hvac_int]
    have h2 : ∫ t in Ioi (0 : ℝ), g t * virasoroProblem.cardyDensity a t =
        ∫ t in Ioi (0 : ℝ), (2 * π) * (g t * virasoroProblem.cardyV a t) :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        unfold FixedWeightProblem.cardyDensity; ring
    rw [h2, integral_const_mul]
    ring

/-- **Theorem S1 (b)** (`spinnotes:S1`): Cardy `D_4` harmonic expansion, `ℓ = 0` identity, and
radial-lift equivalence with `M_2` and `Φ_vac` identities. -/
theorem spinS1b : SpinS1b := by
  intro a ha
  refine ⟨fun ℓ {_t} ht => spinV2Harmonic_eq ha ℓ ht,
    fun {_t} ht => spinV2Harmonic_zero_eq_cardyDensity ha ht,
    fun g => ⟨spinTestClass_radialLift_iff ha g, fun hg => spinM2_and_phiVac_radialLift ha hg⟩⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_polar_integrable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_polar_integrable_iff

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_polar_integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_polar_integral_eq

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinTestClass_radialLift_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinTestClass_radialLift_iff

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinM2_and_phiVac_radialLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinM2_and_phiVac_radialLift

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS1b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS1b

end FormalResearch.ModularBootstrap.Spin
