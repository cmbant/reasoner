module

public import FormalResearch.ModularBootstrap.Integration.StripKernel
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Hankel inversion on the real axis and holomorphy of `hankelContinuation`

Proves the two properties of `Integration.hankelContinuation c' g` left open in
`Integration/StripKernel.lean` (paper: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`,
Lemma B (`vlo:Bessel`) (b), (d), and Lemma G (`vlo:Gap`), "The strip"):

* `hankelContinuation_ofReal`: for `0 < c'`, `g ∈ TestClass virasoroProblem (c' / 12)`, and
  any real `b : ℝ`, `hankelContinuation c' g (b : ℂ) = (g (c' * b ^ 2 / 3) : ℂ)`.
  This is the order-zero Hankel inversion `ĝ = -g` in radial coordinates on `ℝ²`, proved
  directly via `polarCoord` without needing Bessel-function orthogonality.
* `continuousOn_hankelContinuation`: for `1000 ≤ c'` and `g ∈ TestClass virasoroProblem (c' / 12)`,
  `hankelContinuation c' g` is continuous on the closed strip `{b : ℂ | |b.im| ≤ 1 / 2}`.
* `differentiableOn_hankelContinuation`, `analyticOnNhd_hankelContinuation`:
  `hankelContinuation c' g` is holomorphic on the open strip `{b : ℂ | |b.im| < 1 / 2}`.
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology
open scoped FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.PoissonJensen

open Crossing Integration Bessel

/-! ### 1. Complex `I₀` as a `(-π, π)` integral and Hankel inversion -/

/-- `I₀(z) = (2π)⁻¹ ∫_{(-π, π)} exp(-z cos θ) dθ`. -/
theorem besselI0C_eq_integral_Ioo (z : ℂ) :
    besselI0C z = (2 * π : ℂ)⁻¹ * ∫ θ in Ioo (-π) π, Complex.exp (-z * (Real.cos θ : ℝ)) := by
  have hpi := Real.pi_pos
  have h1 : ∫ θ in (0 : ℝ)..π, Complex.exp (z * (Real.cos θ : ℝ)) =
      ∫ θ in (0 : ℝ)..π, Complex.exp (-z * (Real.cos θ : ℝ)) := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => Complex.exp (-z * (Real.cos θ : ℝ))) π (a := 0) (b := π)
    simp only [sub_zero, sub_self] at hsub
    refine (intervalIntegral.integral_congr fun θ _ => ?_).trans hsub
    rw [Real.cos_pi_sub, Complex.ofReal_neg]; congr 1; ring
  have h2 : ∫ θ in (-π)..(0 : ℝ), Complex.exp (-z * (Real.cos θ : ℝ)) =
      ∫ θ in (0 : ℝ)..π, Complex.exp (-z * (Real.cos θ : ℝ)) := by
    have hneg := intervalIntegral.integral_comp_neg
      (fun θ : ℝ => Complex.exp (-z * (Real.cos θ : ℝ))) (a := 0) (b := π)
    simp only [neg_zero] at hneg
    refine hneg.symm.trans (intervalIntegral.integral_congr fun θ _ => ?_)
    rw [Real.cos_neg]
  have hint1 : IntervalIntegrable (fun θ : ℝ => Complex.exp (-z * (Real.cos θ : ℝ))) volume (-π) 0 :=
    (by fun_prop : Continuous fun θ : ℝ => Complex.exp (-z * (Real.cos θ : ℝ))).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ : ℝ => Complex.exp (-z * (Real.cos θ : ℝ))) volume 0 π :=
    (by fun_prop : Continuous fun θ : ℝ => Complex.exp (-z * (Real.cos θ : ℝ))).intervalIntegrable _ _
  have hsplit : ∫ θ in Ioo (-π) π, Complex.exp (-z * (Real.cos θ : ℝ)) =
      (∫ θ in (-π)..(0 : ℝ), Complex.exp (-z * (Real.cos θ : ℝ))) +
        ∫ θ in (0 : ℝ)..π, Complex.exp (-z * (Real.cos θ : ℝ)) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
    exact (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  unfold besselI0C
  rw [h1, hsplit, h2]
  have hpiC : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
  field_simp; ring

private lemma quasiMeasurePreserving_polarCoord_symm_real :
    MeasureTheory.QuasiMeasurePreserving polarCoord.symm
      (volume.restrict polarCoord.target) volume := by
  refine ⟨continuous_polarCoord_symm.measurable, ?_⟩
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

private noncomputable def e2ToProd : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

private lemma volume_preserving_e2ToProd : MeasurePreserving e2ToProd volume volume :=
  (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))

private lemma e2ToProd_symm_apply (p : ℝ × ℝ) (i : Fin 2) :
    (e2ToProd.symm p) i = if i = 0 then p.1 else p.2 := by
  fin_cases i <;> rfl

private lemma e2ToProd_symm_norm_sq (p : ℝ × ℝ) :
    ‖e2ToProd.symm p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, e2ToProd_symm_apply]
  simp

private lemma e2ToProd_symm_inner_single (p : ℝ × ℝ) (r : ℝ) :
    @inner ℝ (EuclideanSpace ℝ (Fin 2)) _ (e2ToProd.symm p) (EuclideanSpace.single 0 r) =
      p.1 * r := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  have h0 : (EuclideanSpace.single (0 : Fin 2) r : EuclideanSpace ℝ (Fin 2)) 0 = r := by
    simp [EuclideanSpace.single]
  have h1 : (EuclideanSpace.single (0 : Fin 2) r : EuclideanSpace ℝ (Fin 2)) 1 = 0 := by
    simp [EuclideanSpace.single]
  rw [h0, h1, e2ToProd_symm_apply, mul_comm]
  simp

/-- **Hankel inversion on the real axis** (`vlo:Bessel`, `vlo:Gap`):
for `0 < c'`, `g ∈ TestClass virasoroProblem (c' / 12)`, and any `b : ℝ`,
`hankelContinuation c' g (b : ℂ) = (g (c' * b ^ 2 / 3) : ℂ)`. -/
theorem hankelContinuation_ofReal {c' : ℝ} (hc : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) (b : ℝ) :
    hankelContinuation c' g (b : ℂ) = (g (c' * b ^ 2 / 3) : ℂ) := by
  let ξ₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (b * √(2 * c' / 3))
  have hξ₀_norm : ‖ξ₀‖ ^ 2 / 2 = c' * b ^ 2 / 3 := by
    have hnorm : ‖ξ₀‖ = ‖b * √(2 * c' / 3)‖ := by
      simp [ξ₀]
    rw [hnorm, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hfx : radialLift 1 g ξ₀ = (g (c' * b ^ 2 / 3) : ℂ) := by
    simp only [radialLift, hξ₀_norm]
  have hodd : 𝓕 (radialLift 1 g) ξ₀ = -(g (c' * b ^ 2 / 3) : ℂ) := by
    rw [← hfx]
    exact congrFun hg.fourier_odd ξ₀
  let F : ℝ × ℝ → ℂ := fun p =>
    𝐞 (-@inner ℝ (EuclideanSpace ℝ (Fin 2)) _ (e2ToProd.symm p) ξ₀) •
      radialLift 1 g (e2ToProd.symm p)
  have hF_int_E2 : Integrable (fun x : EuclideanSpace ℝ (Fin 2) =>
      𝐞 (-@inner ℝ (EuclideanSpace ℝ (Fin 2)) _ x ξ₀) • radialLift 1 g x) :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (L := innerₗ (EuclideanSpace ℝ (Fin 2))) continuous_inner ξ₀).2 hg.int_lift
  have hF_int : Integrable F :=
    (volume_preserving_e2ToProd.symm.integrable_comp_emb e2ToProd.symm.measurableEmbedding).2 hF_int_E2
  have hfourier_prod : 𝓕 (radialLift 1 g) ξ₀ = ∫ p : ℝ × ℝ, F p := by
    rw [Real.fourier_eq]
    exact (volume_preserving_e2ToProd.symm.integral_comp e2ToProd.symm.measurableEmbedding
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        𝐞 (-@inner ℝ (EuclideanSpace ℝ (Fin 2)) _ x ξ₀) • radialLift 1 g x)).symm
  have hpolar : ∫ p : ℝ × ℝ, F p =
      ∫ q in polarCoord.target, q.1 • F (polarCoord.symm q) :=
    (integral_comp_polarCoord_symm F).symm
  have hpolar_int : IntegrableOn (fun q : ℝ × ℝ => q.1 • F (polarCoord.symm q))
      polarCoord.target := by
    have haes : AEStronglyMeasurable (fun q : ℝ × ℝ => q.1 • F (polarCoord.symm q))
        (volume.restrict polarCoord.target) :=
      (continuous_fst.aestronglyMeasurable).smul
        (hF_int.aestronglyMeasurable.comp_quasiMeasurePreserving
          quasiMeasurePreserving_polarCoord_symm_real)
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
    have h1 : ∫ q in polarCoord.target, q.1 • F (polarCoord.symm q) =
        ∫ q : ℝ × ℝ, q.1 • F (polarCoord.symm q)
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
      rw [← hprod_target]
    rw [h1, integral_prod _ hprod_int]
  have hinner_simp : ∀ r ∈ Ioi (0 : ℝ),
      ∫ θ in Ioo (-π) π, r • F (polarCoord.symm (r, θ)) =
        (2 * π : ℂ) * (r : ℂ) * (g (r ^ 2 / 2) : ℂ) *
          besselI0C (4 * (π : ℂ) * Complex.I * (b : ℂ) * (Real.sqrt (c' * (r ^ 2 / 2) / 3) : ℝ)) := by
    intro r hr
    have hrp : 0 < r := mem_Ioi.mp hr
    have hsq : Real.sqrt (c' * (r ^ 2 / 2) / 3) = r * Real.sqrt (c' / 6) := by
      rw [show c' * (r ^ 2 / 2) / 3 = r ^ 2 * (c' / 6) by ring,
        Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hrp.le]
    have heq : ∀ θ : ℝ, r • F (polarCoord.symm (r, θ)) =
        ((r : ℂ) * (g (r ^ 2 / 2) : ℂ)) *
          Complex.exp (-(4 * (π : ℂ) * Complex.I * (b : ℂ) *
            (Real.sqrt (c' * (r ^ 2 / 2) / 3) : ℝ)) * (Real.cos θ : ℝ)) := by
      intro θ
      simp only [F, polarCoord_symm_apply, radialLift]
      rw [e2ToProd_symm_norm_sq, e2ToProd_symm_inner_single]
      have hnorm : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
        calc (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2
            = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
          _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
      rw [hnorm, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, Complex.real_smul]
      have hexp_eq : ((2 * π * -(r * Real.cos θ * (b * √(2 * c' / 3))) : ℝ) : ℂ) * Complex.I =
          -(4 * (π : ℂ) * Complex.I * (b : ℂ) * (Real.sqrt (c' * (r ^ 2 / 2) / 3) : ℝ)) *
            (Real.cos θ : ℝ) := by
        rw [hsq]
        have hsqrt : √(2 * c' / 3) = 2 * √(c' / 6) := by
          rw [show 2 * c' / 3 = 2 ^ 2 * (c' / 6) by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by positivity)]
        rw [hsqrt]
        push_cast; ring
      rw [hexp_eq]
      ring
    simp_rw [heq]
    rw [integral_const_mul, besselI0C_eq_integral_Ioo]
    have h2pi : (2 * π : ℂ) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
    field_simp
  have houter_eq : ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, r • F (polarCoord.symm (r, θ)) =
      (2 * π : ℂ) * ∫ r in Ioi (0 : ℝ), (r : ℂ) * ((g (r ^ 2 / 2) : ℂ) *
        besselI0C (4 * (π : ℂ) * Complex.I * (b : ℂ) * (Real.sqrt (c' * (r ^ 2 / 2) / 3) : ℝ))) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    rw [hinner_simp r hr]
    ring
  let φ : ℝ → ℝ := fun r => r ^ 2 / 2
  have himg : φ '' Ioi 0 = Ioi 0 := by
    ext t; simp only [mem_image, mem_Ioi, φ]
    constructor
    · rintro ⟨r, hr, rfl⟩; positivity
    · intro ht
      refine ⟨Real.sqrt (2 * t), Real.sqrt_pos.mpr (by positivity), ?_⟩
      rw [Real.sq_sqrt (by positivity)]; ring
  let Gfun : ℝ → ℂ := fun t =>
    (g t : ℂ) * besselI0C (4 * (π : ℂ) * Complex.I * (b : ℂ) * (Real.sqrt (c' * t / 3) : ℝ))
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := φ) (f' := fun r => r)
    measurableSet_Ioi
    (fun r _ => (((hasDerivAt_pow 2 r).div_const 2).congr_deriv (by ring)).hasDerivWithinAt)
    (fun r₁ hr₁ r₂ hr₂ heq => by
      have hr₁p : 0 < r₁ := mem_Ioi.mp hr₁
      have hr₂p : 0 < r₂ := mem_Ioi.mp hr₂
      have hsq : r₁ ^ 2 = r₂ ^ 2 := by dsimp [φ] at heq; linarith
      nlinarith)
    Gfun
  rw [himg] at hcov
  have hcov' : ∫ t in Ioi (0 : ℝ), Gfun t =
      ∫ r in Ioi (0 : ℝ), (r : ℂ) * Gfun (r ^ 2 / 2) := by
    rw [hcov]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    rw [abs_of_pos (mem_Ioi.mp hr), Complex.real_smul]
  have hfinal : 𝓕 (radialLift 1 g) ξ₀ =
      (2 * π : ℂ) * ∫ t in Ioi (0 : ℝ), Gfun t := by
    rw [hfourier_prod, hpolar, hfubini, houter_eq, hcov']
  rw [hodd] at hfinal
  unfold hankelContinuation
  change -2 * (π : ℂ) * ∫ t in Ioi (0 : ℝ), Gfun t = (g (c' * b ^ 2 / 3) : ℂ)
  have := congrArg (fun z : ℂ => -z) hfinal
  simpa [neg_mul, mul_assoc] using this.symm

/-! ### 2. Continuity on the closed strip and holomorphy on the open strip -/

/-- Derivative of `besselI0C`: `π⁻¹ ∫₀^π cos θ exp(z cos θ) dθ`. -/
noncomputable def besselI0CDeriv (z : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, (Real.cos θ : ℂ) * Complex.exp (z * (Real.cos θ : ℝ))

lemma besselI0CDeriv_norm_le (z : ℂ) : ‖besselI0CDeriv z‖ ≤ besselI0 z.re := by
  unfold besselI0CDeriv
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    besselI0_integral, ← div_eq_inv_mul]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans ?_
  refine intervalIntegral.integral_mono_on Real.pi_pos.le
    ((by fun_prop : Continuous fun θ : ℝ =>
      ‖(Real.cos θ : ℂ) * Complex.exp (z * (Real.cos θ : ℝ))‖).intervalIntegrable 0 π)
    ((by fun_prop : Continuous fun θ : ℝ => Real.exp (z.re * Real.cos θ)).intervalIntegrable 0 π)
    fun θ _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc |Real.cos θ| * Real.exp (z.re * Real.cos θ) ≤ 1 * Real.exp (z.re * Real.cos θ) := by
        gcongr; exact Real.abs_cos_le_one θ
    _ = Real.exp (z.re * Real.cos θ) := one_mul _

lemma hasDerivAt_besselI0C (z₀ : ℂ) : HasDerivAt besselI0C (besselI0CDeriv z₀) z₀ := by
  let F : ℂ → ℝ → ℂ := fun z θ => Complex.exp (z * (Real.cos θ : ℝ))
  let F' : ℂ → ℝ → ℂ := fun z θ => (Real.cos θ : ℂ) * Complex.exp (z * (Real.cos θ : ℝ))
  have hint := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (F := F) (F' := F') (x₀ := z₀) (s := Metric.ball z₀ 1)
    (a := 0) (b := π)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (by fun_prop : Continuous (F z)).aestronglyMeasurable)
    ((by fun_prop : Continuous (F z₀)).intervalIntegrable 0 π)
    (by fun_prop : Continuous (F' z₀)).aestronglyMeasurable
    (Eventually.of_forall fun θ _ z hz => by
      dsimp [F']
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
      have hz1 : ‖z‖ ≤ ‖z₀‖ + 1 := by
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ 1 + ‖z₀‖ := by linarith [(dist_eq_norm z z₀ ▸ Metric.mem_ball.mp hz).le]
          _ = ‖z₀‖ + 1 := by ring
      have hre : (z * (Real.cos θ : ℝ)).re ≤ ‖z₀‖ + 1 := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        calc z.re * Real.cos θ ≤ |z.re * Real.cos θ| := le_abs_self _
          _ = |z.re| * |Real.cos θ| := abs_mul _ _
          _ ≤ ‖z‖ * 1 := by gcongr; exact Complex.abs_re_le_norm z
          _ ≤ ‖z₀‖ + 1 := by linarith
      calc |Real.cos θ| * Real.exp (z * (Real.cos θ : ℝ)).re ≤ 1 * Real.exp (‖z₀‖ + 1) := by gcongr
        _ = Real.exp (‖z₀‖ + 1) := one_mul _)
    (intervalIntegrable_const (μ := volume))
    (Eventually.of_forall fun θ _ z _ => by
      dsimp [F, F']
      exact (((hasDerivAt_id z).mul_const (Real.cos θ : ℂ)).cexp).congr_deriv (by
        simp [mul_comm]))
  exact hint.2.const_mul (π : ℂ)⁻¹

private lemma continuous_besselI0C : Continuous besselI0C :=
  continuous_iff_continuousAt.mpr fun z => (hasDerivAt_besselI0C z).continuousAt

private lemma continuous_besselI0CDeriv : Continuous besselI0CDeriv := by
  have hdiff : Differentiable ℂ besselI0C := fun z => (hasDerivAt_besselI0C z).differentiableAt
  have hderiv : deriv besselI0C = besselI0CDeriv := funext fun z => (hasDerivAt_besselI0C z).deriv
  rw [← hderiv]
  exact continuousOn_univ.mp ((hdiff.differentiableOn.analyticOnNhd isOpen_univ).deriv.continuousOn)

private lemma sqrt_mul_besselI0_scaled_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → u * besselI0 (r * u) ≤ C * besselI0 u := by
  set δ : ℝ := 1 - r with hδ_def
  have hδ : 0 < δ := sub_pos.mpr hr1
  let C_big : ℝ := (4 / 3 : ℝ) * Real.sqrt (2 * π) * (16 / δ ^ 2)
  let C : ℝ := max (4 * Real.exp 4) C_big
  refine ⟨C, le_trans (by positivity) (le_max_left _ _), fun u hu => ?_⟩
  rcases le_or_gt u 4 with hu4 | hu4
  · have hI0_lo : 1 ≤ besselI0 u := one_le_besselI0 u
    have hI0_hi : besselI0 (r * u) ≤ Real.exp 4 :=
      (besselI0_le_exp (mul_nonneg hr0 hu)).trans (Real.exp_le_exp.mpr (by nlinarith))
    have hI0_nn : 0 ≤ besselI0 (r * u) := besselI_nonneg 0 (mul_nonneg hr0 hu)
    calc u * besselI0 (r * u) ≤ 4 * Real.exp 4 := by gcongr
      _ ≤ (4 * Real.exp 4) * besselI0 u := le_mul_of_one_le_right (by positivity) hI0_lo
      _ ≤ C * besselI0 u := mul_le_mul_of_nonneg_right (le_max_left _ _) (besselI_nonneg 0 hu)
  · have hu_pos : 0 < u := by linarith
    have hlo := besselI0_lower hu_pos
    have hAs_pos : 0 < besselAs u := besselAs_pos hu_pos
    have hcoef : (3 / 4 : ℝ) * besselAs u ≤ besselI0 u := by
      have : 1 - 1 / u ≥ 3 / 4 := by
        have : 1 / u ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hu4.le
        linarith
      exact le_trans (mul_le_mul_of_nonneg_right this hAs_pos.le) hlo
    have hI0_hi : besselI0 (r * u) ≤ Real.exp (r * u) := besselI0_le_exp (mul_nonneg hr0 hu)
    have hpoly : u ^ 2 ≤ (16 / δ ^ 2) * Real.exp (δ * u) := by
      have hexp := Real.add_one_le_exp (δ * u / 2)
      have h0 : 0 ≤ δ * u / 2 := by positivity
      have hsq : (δ * u / 2) ^ 2 ≤ Real.exp (δ * u / 2) ^ 2 :=
        pow_le_pow_left₀ h0 (by linarith) 2
      rw [← Real.exp_nat_mul] at hsq
      have heq : ((2 : ℕ) : ℝ) * (δ * u / 2) = δ * u := by push_cast; ring
      rw [heq] at hsq
      have h4 : δ ^ 2 * u ^ 2 / 4 ≤ Real.exp (δ * u) := by linarith [sq_nonneg (δ * u / 2)]
      calc u ^ 2 = (4 / δ ^ 2) * (δ ^ 2 * u ^ 2 / 4) := by field_simp [hδ.ne']
        _ ≤ (4 / δ ^ 2) * Real.exp (δ * u) := by gcongr
        _ ≤ (16 / δ ^ 2) * Real.exp (δ * u) := by gcongr; norm_num
    have hu32 : u * Real.sqrt (2 * π * u) ≤ Real.sqrt (2 * π) * u ^ 2 := by
      rw [show 2 * π * u = (2 * π) * u by ring, Real.sqrt_mul (by positivity)]
      have hsu : Real.sqrt u ≤ u := Real.sqrt_le_iff.mpr ⟨hu, by nlinarith⟩
      calc u * (Real.sqrt (2 * π) * Real.sqrt u)
          = Real.sqrt (2 * π) * (u * Real.sqrt u) := by ring
        _ ≤ Real.sqrt (2 * π) * (u * u) := by gcongr
        _ = Real.sqrt (2 * π) * u ^ 2 := by ring
    have hAs_eq : u * Real.exp (r * u) =
        (u * Real.sqrt (2 * π * u)) * Real.exp (-(δ * u)) * besselAs u := by
      unfold besselAs
      have hsq_pos : 0 < Real.sqrt (2 * π * u) := by positivity
      have hexp_eq : Real.exp (-(δ * u)) * Real.exp u = Real.exp (r * u) := by
        rw [← Real.exp_add]; congr 1; dsimp [δ]; ring
      calc u * Real.exp (r * u)
          = u * (Real.exp (-(δ * u)) * Real.exp u) := by rw [hexp_eq]
        _ = (u * Real.sqrt (2 * π * u)) * Real.exp (-(δ * u)) * (Real.exp u / Real.sqrt (2 * π * u)) := by
            field_simp
    have hI0_nn : 0 ≤ besselI0 u := besselI_nonneg 0 hu
    calc u * besselI0 (r * u) ≤ u * Real.exp (r * u) := by gcongr
      _ = (u * Real.sqrt (2 * π * u)) * Real.exp (-(δ * u)) * besselAs u := hAs_eq
      _ ≤ (Real.sqrt (2 * π) * u ^ 2) * Real.exp (-(δ * u)) * besselAs u := by
          gcongr
      _ ≤ (Real.sqrt (2 * π) * ((16 / δ ^ 2) * Real.exp (δ * u))) * Real.exp (-(δ * u)) * besselAs u := by
          gcongr
      _ = (Real.sqrt (2 * π) * (16 / δ ^ 2)) * (Real.exp (δ * u) * Real.exp (-(δ * u))) * besselAs u := by
          ring
      _ = Real.sqrt (2 * π) * (16 / δ ^ 2) * besselAs u := by
          rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]
      _ = C_big * ((3 / 4 : ℝ) * besselAs u) := by dsimp [C_big]; ring
      _ ≤ C_big * besselI0 u := by gcongr
      _ ≤ C * besselI0 u := by gcongr; exact le_max_right _ _

/-- **Continuity of `hankelContinuation` on the closed strip `{b : ℂ | |b.im| ≤ 1/2}`**
(Lemma G, `vlo:Gap`, "The strip"). -/
theorem continuousOn_hankelContinuation {c' : ℝ} (hc : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    ContinuousOn (hankelContinuation c' g) {b : ℂ | |b.im| ≤ 1 / 2} := by
  have hc0 : 0 < c' := by linarith
  obtain ⟨hint_Ka, _⟩ := lemmaB_d_integral hc hg
  unfold hankelContinuation
  refine continuousOn_const.mul ?_
  let F : ℂ → ℝ → ℂ := fun b t =>
    (g t : ℂ) * besselI0C (4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ))
  refine continuousOn_of_dominated (μ := volume.restrict (Ioi 0))
    (bound := fun t => |g t| * kernelK 1 (c' / 12) t) ?_ ?_ hint_Ka ?_
  · intro b _
    exact ((Complex.continuous_ofReal.comp_continuousOn hg.cont).mono Ioi_subset_Ici_self |>.mul
      ((continuous_besselI0C.comp (by fun_prop : Continuous fun s : ℝ =>
        4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * s / 3) : ℝ))).continuousOn))
      |>.aestronglyMeasurable measurableSet_Ioi
  · intro b hb
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    change ‖(g t : ℂ) * besselI0C (4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ))‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact besselI0C_strip_le hc0 (le_of_lt ht) hb
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t _ => ?_
    have hF : Continuous fun b : ℂ =>
        (g t : ℂ) * besselI0C (4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ)) :=
      continuous_const.mul (continuous_besselI0C.comp (by fun_prop))
    exact hF.continuousOn

/-- **Holomorphy of `hankelContinuation` on the open strip `{b : ℂ | |b.im| < 1/2}`**
(Lemma G, `vlo:Gap`, "The strip"). -/
theorem differentiableOn_hankelContinuation {c' : ℝ} (hc : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    DifferentiableOn ℂ (hankelContinuation c' g) {b : ℂ | |b.im| < 1 / 2} := by
  have hc0 : 0 < c' := by linarith
  obtain ⟨hint_Ka, _⟩ := lemmaB_d_integral hc hg
  intro b₀ hb₀
  have hbim_lt : |b₀.im| < 1 / 2 := hb₀
  refine DifferentiableAt.differentiableWithinAt ?_
  set r : ℝ := (|b₀.im| + 1 / 2) / 2 with hr_def
  have hr_gt : |b₀.im| < r := by rw [hr_def]; linarith
  have hr_lt : r < 1 / 2 := by rw [hr_def]; linarith
  set δb : ℝ := r - |b₀.im| with hδb_def
  have hδb_pos : 0 < δb := sub_pos.mpr hr_gt
  obtain ⟨C, hC_nn, hC_bd⟩ := sqrt_mul_besselI0_scaled_le (r := 2 * r)
    (by positivity : 0 ≤ 2 * r) (by linarith)
  let F : ℂ → ℝ → ℂ := fun b t =>
    (g t : ℂ) * besselI0C (4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ))
  let F' : ℂ → ℝ → ℂ := fun b t =>
    (g t : ℂ) * (4 * (π : ℂ) * Complex.I * (Real.sqrt (c' * t / 3) : ℝ)) *
      besselI0CDeriv (4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ))
  have hF_meas : ∀ b : ℂ, AEStronglyMeasurable (F b) (volume.restrict (Ioi 0)) := fun b =>
    ((Complex.continuous_ofReal.comp_continuousOn hg.cont).mono Ioi_subset_Ici_self |>.mul
      ((continuous_besselI0C.comp (by fun_prop : Continuous fun s : ℝ =>
        4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * s / 3) : ℝ))).continuousOn))
      |>.aestronglyMeasurable measurableSet_Ioi
  have hF'_meas : AEStronglyMeasurable (F' b₀) (volume.restrict (Ioi 0)) :=
    (((Complex.continuous_ofReal.comp_continuousOn hg.cont).mono Ioi_subset_Ici_self).mul
      ((by fun_prop : Continuous fun s : ℝ =>
        4 * (π : ℂ) * Complex.I * (Real.sqrt (c' * s / 3) : ℝ)).continuousOn) |>.mul
      ((continuous_besselI0CDeriv.comp (by fun_prop : Continuous fun s : ℝ =>
        4 * (π : ℂ) * Complex.I * b₀ * (Real.sqrt (c' * s / 3) : ℝ))).continuousOn))
      |>.aestronglyMeasurable measurableSet_Ioi
  have hF_int : Integrable (F b₀) (volume.restrict (Ioi 0)) := by
    refine hint_Ka.mono' (hF_meas b₀) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    dsimp [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact besselI0C_strip_le hc0 (le_of_lt ht) hbim_lt.le
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ b ∈ Metric.ball b₀ δb,
      ‖F' b t‖ ≤ (2 * C) * (|g t| * kernelK 1 (c' / 12) t) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht b hb => ?_
    have ht0 : 0 ≤ t := le_of_lt ht
    have hbim : |b.im| ≤ r := by
      have h1 : |b.im - b₀.im| ≤ ‖b - b₀‖ := by
        simpa using Complex.abs_im_le_norm (b - b₀)
      have h2 : ‖b - b₀‖ < δb := dist_eq_norm b b₀ ▸ Metric.mem_ball.mp hb
      have h3 : |b.im| ≤ |b₀.im| + |b.im - b₀.im| := by
        calc |b.im| = |b₀.im + (b.im - b₀.im)| := by ring_nf
          _ ≤ |b₀.im| + |b.im - b₀.im| := abs_add_le _ _
      linarith
    set s : ℝ := Real.sqrt (c' * t / 3) with hs_def
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    set u : ℝ := 4 * π * Real.sqrt (c' / 12 * t) with hu_def
    have hu0 : 0 ≤ u := by positivity
    have hus : u = 2 * π * s := by
      rw [hu_def, hs_def, show c' / 12 * t = (c' * t / 3) / 4 by ring,
        Real.sqrt_div (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      ring
    have harg_re : |(4 * (π : ℂ) * Complex.I * b * (s : ℝ)).re| ≤ (2 * r) * u := by
      have hre : (4 * (π : ℂ) * Complex.I * b * (s : ℝ)).re = -(4 * π * b.im * s) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, abs_neg, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π),
        abs_of_nonneg hs0, hus]
      calc 4 * π * |b.im| * s ≤ 4 * π * r * s := by gcongr
        _ = (2 * r) * (2 * π * s) := by ring
    have hI_le : besselI0 (4 * (π : ℂ) * Complex.I * b * (s : ℝ)).re ≤ besselI0 ((2 * r) * u) :=
      besselI0_le_of_abs_le harg_re
    have hbd_u : u * besselI0 ((2 * r) * u) ≤ C * besselI0 u := hC_bd u hu0
    have hK_eq : besselI0 u = kernelK 1 (c' / 12) t :=
      (kernelK_one_eq_besselI0 (by positivity) ht0).symm
    dsimp [F']
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h4pi : ‖4 * (π : ℂ) * Complex.I * (s : ℝ)‖ = 2 * u := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hs0, hus]
      ring
    rw [h4pi]
    calc |g t| * (2 * u) * ‖besselI0CDeriv (4 * (π : ℂ) * Complex.I * b * (s : ℝ))‖
        ≤ |g t| * (2 * u) * besselI0 (4 * (π : ℂ) * Complex.I * b * (s : ℝ)).re := by
          gcongr; exact besselI0CDeriv_norm_le _
      _ ≤ |g t| * (2 * u) * besselI0 ((2 * r) * u) := by gcongr
      _ = 2 * |g t| * (u * besselI0 ((2 * r) * u)) := by ring
      _ ≤ 2 * |g t| * (C * besselI0 u) := by gcongr
      _ = (2 * C) * (|g t| * kernelK 1 (c' / 12) t) := by rw [hK_eq]; ring
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ b ∈ Metric.ball b₀ δb,
      HasDerivAt (fun z => F z t) (F' b t) b := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t _ b _ => ?_
    dsimp [F, F']
    set c : ℂ := 4 * (π : ℂ) * Complex.I * (Real.sqrt (c' * t / 3) : ℝ)
    have hlin : HasDerivAt (fun z : ℂ => c * z) c b := by
      simpa using (hasDerivAt_id b).const_mul c
    have hcomp := ((hasDerivAt_besselI0C (c * b)).comp b hlin).const_mul (g t : ℂ)
    refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_) |>.congr_deriv ?_
    · congr 2; dsimp [c]; ring
    · dsimp [c]; ring
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (Metric.ball_mem_nhds b₀ hδb_pos)
    (Eventually.of_forall hF_meas) hF_int hF'_meas h_bound (hint_Ka.const_mul (2 * C)) h_diff).2
  unfold hankelContinuation
  exact (hderiv.const_mul (-2 * (π : ℂ))).differentiableAt

/-- **Analyticity of `hankelContinuation` on the open strip `{b : ℂ | |b.im| < 1/2}`**. -/
theorem analyticOnNhd_hankelContinuation {c' : ℝ} (hc : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    AnalyticOnNhd ℂ (hankelContinuation c' g) {b : ℂ | |b.im| < 1 / 2} :=
  (differentiableOn_hankelContinuation hc hg).analyticOnNhd
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

/-- info: 'FormalResearch.ModularBootstrap.PoissonJensen.hankelContinuation_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.PoissonJensen.hankelContinuation_ofReal

/-- info: 'FormalResearch.ModularBootstrap.PoissonJensen.continuousOn_hankelContinuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.PoissonJensen.continuousOn_hankelContinuation

/-- info: 'FormalResearch.ModularBootstrap.PoissonJensen.differentiableOn_hankelContinuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.PoissonJensen.differentiableOn_hankelContinuation

end FormalResearch.ModularBootstrap.PoissonJensen
