module

public import FormalResearch.ModularBootstrap.Spin.SpinDStatements
public import FormalResearch.ModularBootstrap.Spin.SpinDAssembly
public import FormalResearch.ModularBootstrap.Spin.SpinDLPi
public import FormalResearch.ModularBootstrap.Spin.SpinS1b
public import FormalResearch.ModularBootstrap.Spin.SpinS1c
public import FormalResearch.ModularBootstrap.Duality.SpanTests

/-!
# SPIN-D: Lemmas SD-M (`sd:M`), SD-P (`sd:P`), and `sd:LP`(ii) conditional on `sd:SD`

Proves unconditionally:
- `spinDM : SpinDM` (`sd:M`, Lemma SD-M: majorant and thermal tests in `SpinTestClassJ`,
  `w_*` decay on `[-2B, ∞)`, and thermal decay on `E_B`);
- `spinDP : SpinDP` (`sd:P`, Lemma SD-P: weak duality for `SpinCertifiedT`, thermal pairing,
  and joint Laplace integrability on `E_B ∩ {t_L + t_R ≥ τ}`).

Also records `spinDLPii_of_SD : SpinDSD → SpinDLPii`, combining the unconditional `spinDLPi`
with `spinDLPii_of_props`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.LP
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight

/-! ### Section 1: 2D anisotropic Gaussian Fourier transform and `SpinDM` (`sd:M`) -/

private noncomputable def spinD_e2ToProd : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

private lemma spinD_volume_preserving_e2ToProd : MeasurePreserving spinD_e2ToProd volume volume :=
  (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))

private lemma spinD_fourier_add_fn {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f₁ f₂ : V → ℂ} (h₁ : Integrable f₁) (h₂ : Integrable f₂) :
    𝓕 (f₁ + f₂) = 𝓕 f₁ + 𝓕 f₂ := by
  ext w
  simp only [Real.fourier_eq, Pi.add_apply]
  have hi1 : Integrable (fun v : V => Real.fourierChar (-⟪v, w⟫) • f₁ v) :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (L := innerₗ V) continuous_inner w).2 h₁
  have hi2 : Integrable (fun v : V => Real.fourierChar (-⟪v, w⟫) • f₂ v) :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (L := innerₗ V) continuous_inner w).2 h₂
  simp_rw [smul_add]
  exact integral_add hi1 hi2

private lemma spinD_fourier_smul_fn {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (c : ℂ) (f : V → ℂ) :
    𝓕 (c • f) = c • 𝓕 f := by
  ext w
  simp only [Real.fourier_eq, Pi.smul_apply]
  simp_rw [smul_comm _ c]
  exact integral_smul c _

private lemma spin_fourier_gaussian_1D {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    𝓕 (fun r : ℝ => (Real.exp (-π * β * r ^ 2) : ℂ)) ξ =
      ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Real.exp (-π * β⁻¹ * ξ ^ 2) : ℂ) := by
  have hb : 0 < ((π * β : ℝ) : ℂ).re := by simp [Real.pi_pos, hβ]
  have hfn : (fun r : ℝ => (Real.exp (-π * β * r ^ 2) : ℂ)) =
      fun r : ℝ => Complex.exp (-((π * β : ℝ) : ℂ) * (‖r‖ : ℂ) ^ 2) := by
    ext r
    rw [Complex.ofReal_exp]
    have hnr : (‖r‖ : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by
      rw [Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
    rw [hnr]; congr 1; push_cast; ring
  rw [hfn, fourier_gaussian_innerProductSpace hb ξ]
  have hdim : (Module.finrank ℝ ℝ / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by simp
  rw [hdim]
  have hpi : ((π : ℝ) : ℂ) / ((π * β : ℝ) : ℂ) = ((β⁻¹ : ℝ) : ℂ) := by
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hbc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
    push_cast; field_simp
  have hnrξ : (‖ξ‖ : ℂ) ^ 2 = ((ξ ^ 2 : ℝ) : ℂ) := by
    rw [Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
  rw [hpi, ← Complex.ofReal_cpow (by positivity : 0 ≤ β⁻¹), Real.inv_rpow hβ.le,
    ← Real.rpow_neg hβ.le, Complex.ofReal_exp, hnrξ]
  congr 2; push_cast
  have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hb_ne : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  field_simp

private lemma spin_fourier_gaussian_2D {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (spinToEuc (fun r : ℝ × ℝ => Real.exp (-π * βL * r.1 ^ 2 - π * βR * r.2 ^ 2))) ξ =
      (((βL * βR) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        spinToEuc (fun r : ℝ × ℝ => Real.exp (-π * βL⁻¹ * r.1 ^ 2 - π * βR⁻¹ * r.2 ^ 2)) ξ := by
  rw [Real.fourier_eq]
  have hchg : ∫ x : EuclideanSpace ℝ (Fin 2),
        Real.fourierChar (-⟪x, ξ⟫) •
          (Real.exp (-π * βL * (x 0) ^ 2 - π * βR * (x 1) ^ 2) : ℂ) =
      ∫ p : ℝ × ℝ,
        (Real.fourierChar (-(p.1 * ξ 0)) • (Real.exp (-π * βL * p.1 ^ 2) : ℂ)) *
        (Real.fourierChar (-(p.2 * ξ 1)) • (Real.exp (-π * βR * p.2 ^ 2) : ℂ)) := by
    rw [← spinD_volume_preserving_e2ToProd.integral_comp' (g := fun p : ℝ × ℝ =>
      (Real.fourierChar (-(p.1 * ξ 0)) • (Real.exp (-π * βL * p.1 ^ 2) : ℂ)) *
      (Real.fourierChar (-(p.2 * ξ 1)) • (Real.exp (-π * βR * p.2 ^ 2) : ℂ)))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    have he0 : (spinD_e2ToProd x).1 = x 0 := rfl
    have he1 : (spinD_e2ToProd x).2 = x 1 := rfl
    rw [he0, he1]
    have hinner : ⟪x, ξ⟫ = x 0 * ξ 0 + x 1 * ξ 1 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, Fin.sum_univ_two, mul_comm]
    rw [hinner, neg_add]
    simp only [Circle.smul_def, smul_eq_mul]
    have hexp : (Real.exp (-π * βL * (x 0) ^ 2 - π * βR * (x 1) ^ 2) : ℂ) =
        (Real.exp (-π * βL * (x 0) ^ 2) : ℂ) * (Real.exp (-π * βR * (x 1) ^ 2) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    have hchar : (Real.fourierChar (-(x 0 * ξ 0) + -(x 1 * ξ 1)) : ℂ) =
        (Real.fourierChar (-(x 0 * ξ 0)) : ℂ) * (Real.fourierChar (-(x 1 * ξ 1)) : ℂ) := by
      rw [AddChar.map_add_eq_mul]; rfl
    rw [hexp, hchar]; ring
  change ∫ x : EuclideanSpace ℝ (Fin 2),
      Real.fourierChar (-⟪x, ξ⟫) •
        (Real.exp (-π * βL * (x 0) ^ 2 - π * βR * (x 1) ^ 2) : ℂ) = _
  rw [hchg, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    integral_prod_mul (f := fun r : ℝ => Real.fourierChar (-(r * ξ 0)) • (Real.exp (-π * βL * r ^ 2) : ℂ))
      (g := fun r : ℝ => Real.fourierChar (-(r * ξ 1)) • (Real.exp (-π * βR * r ^ 2) : ℂ))]
  have hL : ∫ r : ℝ, Real.fourierChar (-(r * ξ 0)) • (Real.exp (-π * βL * r ^ 2) : ℂ) =
      𝓕 (fun r : ℝ => (Real.exp (-π * βL * r ^ 2) : ℂ)) (ξ 0) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp [mul_comm]
  have hR : ∫ r : ℝ, Real.fourierChar (-(r * ξ 1)) • (Real.exp (-π * βR * r ^ 2) : ℂ) =
      𝓕 (fun r : ℝ => (Real.exp (-π * βR * r ^ 2) : ℂ)) (ξ 1) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp [mul_comm]
  rw [hL, hR, spin_fourier_gaussian_1D hβL (ξ 0), spin_fourier_gaussian_1D hβR (ξ 1)]
  dsimp only [spinToEuc]
  have hexp_ξ : (Real.exp (-π * βL⁻¹ * (ξ 0) ^ 2 - π * βR⁻¹ * (ξ 1) ^ 2) : ℂ) =
      (Real.exp (-π * βL⁻¹ * (ξ 0) ^ 2) : ℂ) * (Real.exp (-π * βR⁻¹ * (ξ 1) ^ 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  rw [Real.mul_rpow hβL.le hβR.le, Complex.ofReal_mul, hexp_ξ]
  ring

private lemma spin_integrable_gaussian_linear {β c : ℝ} (hβ : 0 < β) :
    Integrable (fun r : ℝ => Real.exp (-π * β * r ^ 2 + c * r)) := by
  have hsq : Integrable (fun r : ℝ => Real.exp (-(π * β) * (r - c / (2 * π * β)) ^ 2)) :=
    (integrable_exp_neg_mul_sq (b := π * β) (by positivity)).comp_sub_right (c / (2 * π * β))
  refine (hsq.const_mul (Real.exp (c ^ 2 / (4 * π * β)))).congr (Eventually.of_forall fun r => ?_)
  dsimp only
  rw [← Real.exp_add]
  congr 1
  have hne : π * β ≠ 0 := by positivity
  field_simp [hne]; ring

private lemma spin_integrable_gaussian_cosh {β c : ℝ} (hβ : 0 < β) :
    Integrable (fun r : ℝ => Real.exp (-π * β * r ^ 2) * Real.cosh (c * r)) := by
  have h1 := spin_integrable_gaussian_linear (c := c) hβ
  have h2 := spin_integrable_gaussian_linear (c := -c) hβ
  have hpt : (fun r : ℝ => Real.exp (-π * β * r ^ 2) * Real.cosh (c * r)) =
      fun r => (1 / 2 : ℝ) * (Real.exp (-π * β * r ^ 2 + c * r) +
        Real.exp (-π * β * r ^ 2 + (-c) * r)) := by
    ext r
    rw [Real.cosh_eq, Real.exp_add, Real.exp_add]
    have : -(c * r) = -c * r := by ring
    rw [this]; ring
  rw [hpt]
  exact (h1.add h2).const_mul (1 / 2 : ℝ)

private lemma spin_thermalX_r_int_J {a βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    Integrable (fun p : ℝ × ℝ =>
      |spinLiftTToR (fun q => spinThermalX βL βR q.1 q.2) p| *
        Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) := by
  have hG : ∀ {γL γR : ℝ}, 0 < γL → 0 < γR →
      Integrable (fun p : ℝ × ℝ =>
        Real.exp (-π * γL * p.1 ^ 2 - π * γR * p.2 ^ 2) *
          Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) := by
    intro γL γR hL hR
    have hprod := (spin_integrable_gaussian_cosh (c := 2 * π * Real.sqrt a) hL).mul_prod
      (spin_integrable_gaussian_cosh (c := 2 * π * Real.sqrt a) hR)
    refine hprod.congr (Eventually.of_forall fun p => ?_)
    dsimp only
    have hexp : Real.exp (-π * γL * p.1 ^ 2 - π * γR * p.2 ^ 2) =
        Real.exp (-π * γL * p.1 ^ 2) * Real.exp (-π * γR * p.2 ^ 2) := by
      rw [sub_eq_add_neg, Real.exp_add]; congr 2; ring
    rw [hexp]; ring
  have h1 := hG hβL hβR
  have h2 := (hG (inv_pos.mpr hβL) (inv_pos.mpr hβR)).const_mul ((βL * βR) ^ (-(1 / 2 : ℝ)))
  refine (h1.add h2).mono' ?_ (Eventually.of_forall fun p => ?_)
  · exact (by unfold spinLiftTToR spinThermalX; fun_prop :
      Continuous fun p : ℝ × ℝ =>
        |spinLiftTToR (fun q => spinThermalX βL βR q.1 q.2) p| *
          Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)).aestronglyMeasurable
  · dsimp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
      (Real.cosh_pos _).le)]
    have hpt : spinLiftTToR (fun q => spinThermalX βL βR q.1 q.2) p =
        Real.exp (-π * βL * p.1 ^ 2 - π * βR * p.2 ^ 2) -
        (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-π * βL⁻¹ * p.1 ^ 2 - π * βR⁻¹ * p.2 ^ 2) := by
      unfold spinLiftTToR spinThermalX
      dsimp only
      have h1 : -2 * π * (βL * (p.1 ^ 2 / 2) + βR * (p.2 ^ 2 / 2)) =
          -π * βL * p.1 ^ 2 - π * βR * p.2 ^ 2 := by ring
      have h2 : -2 * π * (p.1 ^ 2 / 2 / βL + p.2 ^ 2 / 2 / βR) =
          -π * βL⁻¹ * p.1 ^ 2 - π * βR⁻¹ * p.2 ^ 2 := by
        field_simp [hβL.ne', hβR.ne']; ring
      rw [h1, h2]
    rw [hpt]
    have habs : |Real.exp (-π * βL * p.1 ^ 2 - π * βR * p.2 ^ 2) -
          (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-π * βL⁻¹ * p.1 ^ 2 - π * βR⁻¹ * p.2 ^ 2)| ≤
        Real.exp (-π * βL * p.1 ^ 2 - π * βR * p.2 ^ 2) +
        (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-π * βL⁻¹ * p.1 ^ 2 - π * βR⁻¹ * p.2 ^ 2) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_pos (Real.exp_pos _),
        abs_of_pos (mul_pos (Real.rpow_pos_of_pos (mul_pos hβL hβR) _) (Real.exp_pos _))]
    have hnn := mul_nonneg (Real.cosh_pos (2 * π * Real.sqrt a * p.1)).le
      (Real.cosh_pos (2 * π * Real.sqrt a * p.2)).le
    have hmul := mul_le_mul_of_nonneg_right habs hnn
    have hrearr : |Real.exp (-π * βL * p.1 ^ 2 - π * βR * p.2 ^ 2) -
        (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-π * βL⁻¹ * p.1 ^ 2 - π * βR⁻¹ * p.2 ^ 2)| *
        Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2) =
      |Real.exp (-π * βL * p.1 ^ 2 - π * βR * p.2 ^ 2) -
        (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-π * βL⁻¹ * p.1 ^ 2 - π * βR⁻¹ * p.2 ^ 2)| *
        (Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) := by ring
    rw [hrearr]
    linarith [show (Real.exp (-π * βL * p.1 ^ 2 - π * βR * p.2 ^ 2) +
        (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-π * βL⁻¹ * p.1 ^ 2 - π * βR⁻¹ * p.2 ^ 2)) *
        (Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) =
      Real.exp (-π * βL * p.1 ^ 2 - π * βR * p.2 ^ 2) *
        Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2) +
      (βL * βR) ^ (-(1 / 2 : ℝ)) *
        (Real.exp (-π * βL⁻¹ * p.1 ^ 2 - π * βR⁻¹ * p.2 ^ 2) *
          Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) by ring]

private lemma spin_thermalX_r_fourier_odd {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    𝓕 (spinToEuc (spinLiftTToR (fun q => spinThermalX βL βR q.1 q.2))) =
      -(spinToEuc (spinLiftTToR (fun q => spinThermalX βL βR q.1 q.2))) := by
  let g1 : EuclideanSpace ℝ (Fin 2) → ℂ :=
    spinToEuc (fun r : ℝ × ℝ => Real.exp (-π * βL * r.1 ^ 2 - π * βR * r.2 ^ 2))
  let g2 : EuclideanSpace ℝ (Fin 2) → ℂ :=
    spinToEuc (fun r : ℝ × ℝ => Real.exp (-π * βL⁻¹ * r.1 ^ 2 - π * βR⁻¹ * r.2 ^ 2))
  have hint_g : ∀ {γL γR : ℝ}, 0 < γL → 0 < γR →
      Integrable (spinToEuc (fun r : ℝ × ℝ => Real.exp (-π * γL * r.1 ^ 2 - π * γR * r.2 ^ 2))) := by
    intro γL γR hL hR
    have hJ : Integrable (fun r : ℝ × ℝ => Real.exp (-π * γL * r.1 ^ 2 - π * γR * r.2 ^ 2)) := by
      have hp := (integrable_exp_neg_mul_sq (b := π * γL) (by positivity)).mul_prod
        (integrable_exp_neg_mul_sq (b := π * γR) (by positivity))
      exact hp.congr (Eventually.of_forall fun r => by
        dsimp only; rw [← Real.exp_add]; congr 1; ring)
    have hreal : Integrable (fun x : EuclideanSpace ℝ (Fin 2) =>
        Real.exp (-π * γL * (x 0) ^ 2 - π * γR * (x 1) ^ 2)) :=
      spinD_volume_preserving_e2ToProd.integrable_comp_of_integrable hJ
    exact Complex.ofRealCLM.integrable_comp hreal
  have hg1 : Integrable g1 := hint_g hβL hβR
  have hg2 : Integrable g2 := hint_g (inv_pos.mpr hβL) (inv_pos.mpr hβR)
  set c : ℝ := (βL * βR) ^ (-(1 / 2 : ℝ)) with hc
  have hc_inv : (βL⁻¹ * βR⁻¹) ^ (-(1 / 2 : ℝ)) * c = 1 := by
    rw [hc, ← Real.mul_rpow (by positivity) (by positivity)]
    have hprod : βL⁻¹ * βR⁻¹ * (βL * βR) = 1 := by field_simp [hβL.ne', hβR.ne']
    rw [hprod, Real.one_rpow]
  have hfn : spinToEuc (spinLiftTToR (fun q => spinThermalX βL βR q.1 q.2)) =
      g1 + (-(c : ℂ)) • g2 := by
    ext x
    simp only [spinToEuc, spinLiftTToR, spinThermalX, g1, g2, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul]
    rw [sub_eq_add_neg, neg_mul, hc]
    have h1 : -(2 * π) * (βL * (x 0 ^ 2 / 2) + βR * (x 1 ^ 2 / 2)) =
        -π * βL * x 0 ^ 2 - π * βR * x 1 ^ 2 := by ring
    have h2 : -(2 * π) * (x 0 ^ 2 / 2 / βL + x 1 ^ 2 / 2 / βR) =
        -π * βL⁻¹ * x 0 ^ 2 - π * βR⁻¹ * x 1 ^ 2 := by
      field_simp [hβL.ne', hβR.ne']; ring
    rw [h1, h2]; ring
  rw [hfn, spinD_fourier_add_fn hg1 (hg2.smul (-(c : ℂ))), spinD_fourier_smul_fn]
  ext ξ
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  rw [spin_fourier_gaussian_2D hβL hβR ξ,
    spin_fourier_gaussian_2D (inv_pos.mpr hβL) (inv_pos.mpr hβR) ξ]
  simp only [inv_inv]
  have hc_inv_c : ((c : ℂ) * (((βL⁻¹ * βR⁻¹) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, mul_comm, hc_inv, Complex.ofReal_one]
  change ((c : ℂ) * g2 ξ) + -(c : ℂ) * ((((βL⁻¹ * βR⁻¹) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * g1 ξ) =
    -(g1 ξ + -(c : ℂ) * g2 ξ)
  rw [neg_mul, ← mul_assoc, hc_inv_c, one_mul]
  ring

private lemma spinSymThermalX_r_mem_TestClassJ {a βL βR : ℝ} (ha : 2 ≤ a)
    (hβL : 0 < βL) (hβR : 0 < βR) :
    SpinTestClassJ a (spinSymThermalX_r βL βR) := by
  have hintJ : Integrable (fun p : ℝ × ℝ =>
      |spinSymThermalX_r βL βR p| *
        Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) := by
    have h1 := (spin_thermalX_r_int_J (a := a) hβL hβR).const_mul (1 / 2 : ℝ)
    have h2 := (spin_thermalX_r_int_J (a := a) hβR hβL).const_mul (1 / 2 : ℝ)
    refine (h1.add h2).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (by unfold spinSymThermalX_r spinLiftTToR spinSymThermalX spinThermalX; fun_prop :
        Continuous fun p : ℝ × ℝ =>
          |spinSymThermalX_r βL βR p| *
            Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)).aestronglyMeasurable
    · dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
        (Real.cosh_pos _).le)]
      have habs : |spinSymThermalX_r βL βR p| ≤
          (1 / 2 : ℝ) * |spinLiftTToR (fun q => spinThermalX βL βR q.1 q.2) p| +
          (1 / 2 : ℝ) * |spinLiftTToR (fun q => spinThermalX βR βL q.1 q.2) p| := by
        unfold spinSymThermalX_r spinLiftTToR spinSymThermalX
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith [abs_add_le (spinThermalX βL βR (p.1 ^ 2 / 2) (p.2 ^ 2 / 2))
          (spinThermalX βR βL (p.1 ^ 2 / 2) (p.2 ^ 2 / 2))]
      have hnn := mul_nonneg (Real.cosh_pos (2 * π * Real.sqrt a * p.1)).le
        (Real.cosh_pos (2 * π * Real.sqrt a * p.2)).le
      have hmul := mul_le_mul_of_nonneg_right habs hnn
      have hrearr : |spinSymThermalX_r βL βR p| *
          Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2) =
        |spinSymThermalX_r βL βR p| *
          (Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) := by ring
      rw [hrearr]
      linarith [show ((1 / 2 : ℝ) * |spinLiftTToR (fun q => spinThermalX βL βR q.1 q.2) p| +
          (1 / 2 : ℝ) * |spinLiftTToR (fun q => spinThermalX βR βL q.1 q.2) p|) *
          (Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) =
        (1 / 2 : ℝ) * (|spinLiftTToR (fun q => spinThermalX βL βR q.1 q.2) p| *
          Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) +
        (1 / 2 : ℝ) * (|spinLiftTToR (fun q => spinThermalX βR βL q.1 q.2) p| *
          Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) by ring]
  have hcont : Continuous (spinSymThermalX_r βL βR) := by
    unfold spinSymThermalX_r spinLiftTToR spinSymThermalX spinThermalX; fun_prop
  have hint : Integrable (spinSymThermalX_r βL βR) := by
    refine hintJ.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    have h1 : 1 ≤ Real.cosh (2 * π * Real.sqrt a * p.1) := Real.one_le_cosh _
    have h2 : 1 ≤ Real.cosh (2 * π * Real.sqrt a * p.2) := Real.one_le_cosh _
    have h12 : 1 ≤ Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2) :=
      one_le_mul_of_one_le_of_one_le h1 h2
    calc |spinSymThermalX_r βL βR p|
        = |spinSymThermalX_r βL βR p| * 1 := (mul_one _).symm
      _ ≤ |spinSymThermalX_r βL βR p| *
            (Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) :=
          mul_le_mul_of_nonneg_left h12 (abs_nonneg _)
      _ = |spinSymThermalX_r βL βR p| *
            Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2) := by ring
  have hintM2 : Integrable (fun p : ℝ × ℝ =>
      |spinSymThermalX_r βL βR p| * spinV1 a p.1 * spinV1 a p.2) := by
    have hV1_cont : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    refine hintJ.mono'
      (((hcont.abs.mul (hV1_cont.comp continuous_fst)).mul (hV1_cont.comp continuous_snd))).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
      (spinV1_nonneg ha p.1)) (spinV1_nonneg ha p.2))]
    have hV1_le : ∀ r : ℝ, spinV1 a r ≤ Real.cosh (2 * π * Real.sqrt a * r) := fun r => by
      unfold spinV1; linarith [Real.cosh_pos (2 * π * Real.sqrt (a - 2) * r)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hV1_le p.1) (abs_nonneg _)) (hV1_le p.2)
      (spinV1_nonneg ha p.2) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
  have hd4 : IsD4Invariant (spinSymThermalX_r βL βR) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y; unfold spinSymThermalX_r spinLiftTToR spinSymThermalX spinThermalX; simp
    · intro x y; unfold spinSymThermalX_r spinLiftTToR spinSymThermalX spinThermalX; simp
    · intro x y; unfold spinSymThermalX_r spinLiftTToR spinSymThermalX spinThermalX
      have hmul : βL * βR = βR * βL := mul_comm _ _
      rw [hmul]; ring_nf
  have hfodd : 𝓕 (spinToEuc (spinSymThermalX_r βL βR)) = -(spinToEuc (spinSymThermalX_r βL βR)) := by
    have hX_euc_int : ∀ {γL γR : ℝ}, 0 < γL → 0 < γR →
        Integrable (spinToEuc (spinLiftTToR (fun q => spinThermalX γL γR q.1 q.2))) := by
      intro γL γR hL hR
      have hreal : Integrable (spinLiftTToR (fun q => spinThermalX γL γR q.1 q.2)) := by
        refine (spin_thermalX_r_int_J (a := a) hL hR).mono'
          (by unfold spinLiftTToR spinThermalX; fun_prop :
            Continuous (spinLiftTToR (fun q => spinThermalX γL γR q.1 q.2))).aestronglyMeasurable
          (Eventually.of_forall fun p => ?_)
        rw [Real.norm_eq_abs]
        have h12 : 1 ≤ Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2) :=
          one_le_mul_of_one_le_of_one_le (Real.one_le_cosh _) (Real.one_le_cosh _)
        calc |spinLiftTToR (fun q => spinThermalX γL γR q.1 q.2) p|
            = |spinLiftTToR (fun q => spinThermalX γL γR q.1 q.2) p| * 1 := (mul_one _).symm
          _ ≤ |spinLiftTToR (fun q => spinThermalX γL γR q.1 q.2) p| *
                (Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2)) :=
              mul_le_mul_of_nonneg_left h12 (abs_nonneg _)
          _ = |spinLiftTToR (fun q => spinThermalX γL γR q.1 q.2) p| *
                Real.cosh (2 * π * Real.sqrt a * p.1) * Real.cosh (2 * π * Real.sqrt a * p.2) := by ring
      exact Complex.ofRealCLM.integrable_comp
        (spinD_volume_preserving_e2ToProd.integrable_comp_of_integrable hreal)
    have h1_int := hX_euc_int hβL hβR
    have h2_int := hX_euc_int hβR hβL
    have hsplit : spinToEuc (spinSymThermalX_r βL βR) =
        ((1 / 2 : ℝ) : ℂ) • (spinToEuc (spinLiftTToR (fun q => spinThermalX βL βR q.1 q.2)) +
          spinToEuc (spinLiftTToR (fun q => spinThermalX βR βL q.1 q.2))) := by
      ext x; simp [spinToEuc, spinSymThermalX_r, spinLiftTToR, spinSymThermalX]
    rw [hsplit, spinD_fourier_smul_fn, spinD_fourier_add_fn h1_int h2_int,
      spin_thermalX_r_fourier_odd hβL hβR, spin_thermalX_r_fourier_odd hβR hβL]
    ext ξ; simp; ring
  exact ⟨⟨hcont, hint, hd4, hfodd, hintM2⟩, hintJ⟩

private lemma spinPhiVac_symThermalX_r {a βL βR : ℝ} (ha : 2 ≤ a)
    (hβL : 0 < βL) (hβR : 0 < βR) :
    spinPhiVac a (spinSymThermalX_r βL βR) = spinThermalXVac a βL βR := by
  have hint_one : ∀ {γL γR : ℝ}, 0 < γL → 0 < γR →
      Integrable (fun r : ℝ × ℝ =>
        spinLiftTToR (fun q => spinThermalX γL γR q.1 q.2) r * spinV1 a r.1 * spinV1 a r.2) := by
    intro γL γR hL hR
    have hV1_cont : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    refine (spin_thermalX_r_int_J (a := a) hL hR).mono'
      (((by unfold spinLiftTToR spinThermalX; fun_prop :
          Continuous (spinLiftTToR (fun q => spinThermalX γL γR q.1 q.2))).mul
        (hV1_cont.comp continuous_fst)).mul (hV1_cont.comp continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (spinV1_nonneg ha p.1),
      abs_of_nonneg (spinV1_nonneg ha p.2)]
    have hV1_le : ∀ r : ℝ, spinV1 a r ≤ Real.cosh (2 * π * Real.sqrt a * r) := fun r => by
      unfold spinV1; linarith [Real.cosh_pos (2 * π * Real.sqrt (a - 2) * r)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hV1_le p.1) (abs_nonneg _)) (hV1_le p.2)
      (spinV1_nonneg ha p.2) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
  have hpt : (fun r : ℝ × ℝ => spinSymThermalX_r βL βR r * spinV1 a r.1 * spinV1 a r.2) =
      fun r => (1 / 2 : ℝ) * (spinLiftTToR (fun q => spinThermalX βL βR q.1 q.2) r *
          spinV1 a r.1 * spinV1 a r.2 +
        spinLiftTToR (fun q => spinThermalX βR βL q.1 q.2) r * spinV1 a r.1 * spinV1 a r.2) := by
    ext r; unfold spinSymThermalX_r spinLiftTToR spinSymThermalX; ring
  have h1 := spinVacT_thermalX ha hβL hβR
  have h2 := spinVacT_thermalX ha hβR hβL
  have hsym : spinThermalXVac a βR βL = spinThermalXVac a βL βR := by
    unfold spinThermalXVac spinVacuumV; rw [mul_comm βR βL]; ring
  unfold spinVacT spinPhiVac at h1 h2
  unfold spinPhiVac
  rw [hpt, integral_const_mul, integral_add (hint_one hβL hβR) (hint_one hβR hβL)]
  linarith

private lemma spin_integrableOn_Ioc_thetaW {a β₀ : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (thetaW a) (Ioc 0 β₀) := by
  refine Integrable.of_bound (C := Real.exp (8 * π * a))
    (measurable_thetaW a).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun β hβ => ?_
  rw [Real.norm_eq_abs, abs_of_pos (thetaW_pos a β)]
  unfold thetaW
  refine Real.exp_le_exp.mpr ?_
  have hβ0 : 0 < β := hβ.1
  have hpos : 0 ≤ 4 * π * a * β⁻¹ := by positivity
  linarith

/-- **`sd:M`** (Lemma SD-M): unconditional proof of `SpinDM`. -/
theorem spinDM : SpinDM := by
  intro a ha
  have ha0 : 0 < a := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- Part (a): radial lift of `hMaj a β₀`
    intro T₀ β₀ hT₀ hβ₀ hβ₀2 ht0
    have hc : 12 * virasoroProblem.totalShift ≤ 12 * a := by
      rw [virasoroProblem_totalShift]; linarith
    have hM := Duality.lemma_M hc hβ₀ hβ₀2 ht0
    have h12 : 12 * a / 12 = a := by ring
    rw [h12] at hM
    refine ⟨spinTestClassJ_radialLift ha hM.1,
      Submodule.subset_span (Or.inr ⟨β₀, hβ₀, hβ₀2, rfl⟩), ?_, hM.2.2.1, ?_⟩
    · rw [(spinM2_and_phiVac_radialLift ha hM.1).2, hM.2.1]
    · intro tL tR hge
      exact ⟨wStar_pos ha0.le hβ₀ (hT₀.le.trans hge), hM.2.2.2.1 (tL + tR) hge⟩
  · -- Part (b): swap-symmetrised thermal tests
    intro βL βR hβL hβR
    exact ⟨spinSymThermalX_r_mem_TestClassJ ha hβL hβR, spinPhiVac_symThermalX_r ha hβL hβR⟩
  · -- Part (c): `w_*` bounds on `[-2B, ∞)` and thermal bounds on `E_B`
    intro β₀ B hβ₀ hβ₀2 hB
    refine ⟨?_, ?_⟩
    · intro m hm
      refine ⟨?_, tendsto_exp_div_wStar ha0.le hβ₀ hm⟩
      obtain ⟨C₁, _hC₁_pos, hC₁⟩ := exp_le_const_wStar ha0.le hβ₀ hm
      have hw0 : 0 < wStar a β₀ 0 := wStar_pos ha0.le hβ₀ le_rfl
      refine ⟨max C₁ (Real.exp (4 * π * m * B) / wStar a β₀ 0), fun t ht => ?_⟩
      by_cases ht0 : 0 ≤ t
      · exact ((div_le_iff₀ (wStar_pos ha0.le hβ₀ ht0)).mpr (hC₁ t ht0)).trans (le_max_left _ _)
      · push Not at ht0
        have hw_ge : wStar a β₀ 0 ≤ wStar a β₀ t := by
          unfold wStar
          refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun β hβ => ?_
          · exact (spin_integrableOn_Ioc_thetaW ha0.le).congr_fun
              (fun β _ => by simp) measurableSet_Ioc
          · have hbd : ∀ β ∈ Ioc 0 β₀, Real.exp (-2 * π * β * t) ≤ Real.exp (4 * π * β₀ * B) := by
              intro β hβ
              refine Real.exp_le_exp.mpr ?_
              have h1 : -2 * π * β * t ≤ -2 * π * β * (-2 * B) := by
                have hβ0 : 0 < β := hβ.1
                have h2piβ : 0 ≤ 2 * π * β := by positivity
                nlinarith
              have h2 : 4 * π * β * B ≤ 4 * π * β₀ * B := by
                have h4piB : 0 ≤ 4 * π * B := by positivity
                nlinarith [hβ.2]
              linarith
            refine ((spin_integrableOn_Ioc_thetaW ha0.le).const_mul (Real.exp (4 * π * β₀ * B))).mono'
              (by have := measurable_thetaW a; fun_prop :
                Measurable fun β => Real.exp (-2 * π * β * t) * thetaW a β).aestronglyMeasurable ?_
            rw [ae_restrict_iff' measurableSet_Ioc]
            refine Eventually.of_forall fun β hβ => ?_
            rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (thetaW_pos a β))]
            exact mul_le_mul_of_nonneg_right (hbd β hβ) (thetaW_pos a β).le
          · simp only [mul_zero, Real.exp_zero, one_mul]
            refine le_mul_of_one_le_left (thetaW_pos a β).le ?_
            have hβ0 : 0 < β := hβ.1
            have h2piβ : 0 ≤ 2 * π * β := by positivity
            exact Real.one_le_exp (by nlinarith)
        have hexp_le : Real.exp (-2 * π * m * t) ≤ Real.exp (4 * π * m * B) := by
          have h2pim : 0 ≤ 2 * π * m := by positivity
          exact Real.exp_le_exp.mpr (by nlinarith)
        have hdiv : Real.exp (-2 * π * m * t) / wStar a β₀ t ≤
            Real.exp (4 * π * m * B) / wStar a β₀ 0 :=
          div_le_div₀ (Real.exp_pos _).le hexp_le hw0 hw_ge
        exact hdiv.trans (le_max_right _ _)
    · intro βL βR hβL hβR
      set m : ℝ := min (min βL βR) (min βL⁻¹ βR⁻¹) with hm_def
      have hm_le_L : m ≤ βL := (min_le_left _ _).trans (min_le_left _ _)
      have hm_le_R : m ≤ βR := (min_le_left _ _).trans (min_le_right _ _)
      have hm_le_Li : m ≤ βL⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
      have hm_le_Ri : m ≤ βR⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
      have hterm : ∀ {γL γR : ℝ}, m ≤ γL → m ≤ γR → ∀ p ∈ spinConeB B,
          Real.exp (-2 * π * (γL * p.1 + γR * p.2)) ≤
            Real.exp (2 * π * B * (γL + γR - 2 * m)) * Real.exp (-2 * π * m * (p.1 + p.2)) := by
        intro γL γR h1 h2 p hp
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have h1' : -B * (γL - m) ≤ p.1 * (γL - m) := mul_le_mul_of_nonneg_right hp.1 (by linarith)
        have h2' : -B * (γR - m) ≤ p.2 * (γR - m) := mul_le_mul_of_nonneg_right hp.2 (by linarith)
        nlinarith [Real.pi_pos]
      refine ⟨Real.exp (2 * π * B * (βL + βR - 2 * m)) +
        (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (2 * π * B * (βL⁻¹ + βR⁻¹ - 2 * m)), fun p hp => ?_⟩
      unfold spinThermalX
      have h1 := hterm hm_le_L hm_le_R p hp
      have h2 := hterm hm_le_Li hm_le_Ri p hp
      have h2' : Real.exp (-2 * π * (p.1 / βL + p.2 / βR)) ≤
          Real.exp (2 * π * B * (βL⁻¹ + βR⁻¹ - 2 * m)) * Real.exp (-2 * π * m * (p.1 + p.2)) := by
        simpa only [div_eq_inv_mul] using h2
      have habs : |Real.exp (-2 * π * (βL * p.1 + βR * p.2)) -
            (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * (p.1 / βL + p.2 / βR))| ≤
          Real.exp (-2 * π * (βL * p.1 + βR * p.2)) +
          (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * (p.1 / βL + p.2 / βR)) := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_pos (Real.exp_pos _),
          abs_of_pos (mul_pos (Real.rpow_pos_of_pos (mul_pos hβL hβR) _) (Real.exp_pos _))]
      have hpow_nn : 0 ≤ (βL * βR) ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos (mul_pos hβL hβR) _).le
      nlinarith

/-! ### Section 2: `SpinDP` (`sd:P`) -/

private lemma spin_joint_laplace_integrable_of_meas {a B : ℝ} (hB : 0 ≤ B) {X : Set (ℝ × ℝ)}
    (hX : X ⊆ spinConeB B) (meas : SpinCrossingMeasureOn a X)
    {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (βL * p.1 + βR * p.2))) meas.ν := by
  have hνB : meas.ν (spinConeB B)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hX) meas.supp
  have hae : ∀ᵐ p ∂meas.ν, p ∈ spinConeB B := by
    have : ∀ᵐ p ∂meas.ν, p ∉ (spinConeB B)ᶜ := measure_eq_zero_iff_ae_notMem.1 hνB
    filter_upwards [this] with p hp using not_not.mp hp
  refine Integrable.mono'
    ((meas.finite_laplace (lt_min hβL hβR)).const_mul
      (Real.exp (2 * π * B * (βL + βR - 2 * min βL βR))))
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Real.exp (-2 * π * (βL * p.1 + βR * p.2))).aestronglyMeasurable ?_
  filter_upwards [hae] with p hp
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact spin_exp_dom_coneB hB hp

/-- **`sd:P`** (Lemma SD-P): unconditional proof of `SpinDP`. -/
theorem spinDP : SpinDP := by
  intro a B τ ha hB hτ X hX meas
  have hXB : X ⊆ spinConeB B := hX.trans inter_subset_left
  have hXpos : X ⊆ {p : ℝ × ℝ | 0 ≤ p.1 + p.2} :=
    (hX.trans inter_subset_right).trans fun _ hp => hτ.le.trans hp
  have hjoint : ∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
      Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (βL * p.1 + βR * p.2))) meas.ν :=
    fun hβL hβR => spin_joint_laplace_integrable_of_meas hB hXB meas hβL hβR
  have hsym_X : ∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
      Integrable (fun p : ℝ × ℝ => spinSymThermalX βL βR p.1 p.2) meas.ν ∧
      ∫ p : ℝ × ℝ, spinSymThermalX βL βR p.1 p.2 ∂meas.ν = -spinThermalXVac a βL βR := by
    intro βL βR hβL hβR
    have hX_int : ∀ {γL γR : ℝ}, 0 < γL → 0 < γR →
        Integrable (fun p : ℝ × ℝ => spinThermalX γL γR p.1 p.2) meas.ν := by
      intro γL γR hL hR
      have h1 := hjoint hL hR
      have h2 := (hjoint (inv_pos.mpr hL) (inv_pos.mpr hR)).const_mul ((γL * γR) ^ (-(1 / 2 : ℝ)))
      refine (h1.sub h2).congr (Eventually.of_forall fun p => ?_)
      dsimp only [Pi.sub_apply]
      unfold spinThermalX; simp only [div_eq_inv_mul]
    have h1 := hX_int hβL hβR
    have h2 := hX_int hβR hβL
    refine ⟨(h1.add h2).const_mul (1 / 2 : ℝ), ?_⟩
    unfold spinSymThermalX
    rw [integral_const_mul, integral_add h1 h2, meas.crossing hβL hβR, meas.crossing hβR hβL]
    have hvac_sym : spinThermalXVac a βR βL = spinThermalXVac a βL βR := by
      unfold spinThermalXVac spinVacuumV; rw [mul_comm βR βL]; ring
    rw [hvac_sym]; ring
  refine ⟨?_, hsym_X, hjoint⟩
  -- Part 1: every `Φ ∈ SpinCertifiedT a` is `ν`-integrable with `∫ Φ dν = -spinVacT a Φ`
  have hmain : ∀ Φ, SpinCertifiedT a Φ →
      Integrable Φ meas.ν ∧
      Integrable (fun r : ℝ × ℝ => spinLiftTToR Φ r * spinV1 a r.1 * spinV1 a r.2) ∧
      ∫ p : ℝ × ℝ, Φ p ∂meas.ν = -spinVacT a Φ := by
    intro Φ hΦ
    unfold SpinCertifiedT at hΦ
    refine Submodule.span_induction
      (p := fun Φ _ =>
        Integrable Φ meas.ν ∧
        Integrable (fun r : ℝ × ℝ => spinLiftTToR Φ r * spinV1 a r.1 * spinV1 a r.2) ∧
        ∫ p : ℝ × ℝ, Φ p ∂meas.ν = -spinVacT a Φ) ?_ ?_ ?_ ?_ hΦ
    · rintro f (⟨m, n, hmn, rfl⟩ | ⟨β₀, hβ₀, hβ₀2, rfl⟩)
      · -- Odd two-variable Laguerre basis function
        have hq_mem : spinOddLagPolyBasis m n ∈ spinOddLagPolySpace (m + n) :=
          Submodule.subset_span ⟨m, n, hmn, le_rfl, rfl⟩
        have hpair := spin_oddLagPoly_pairing ha hB hXB meas hq_mem
        have heq : (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2)) * spinOddLagPolyBasis m n p) =
            spinOddLagBasisT m n := funext (exp_mul_spinOddLagPolyBasis m n)
        rw [heq] at hpair
        have hVac_int := (spin_tensor_cayley_vac ha (θ := 1 / 2) (by norm_num) (by norm_num)
          (ϖL := 0) (ϖR := 0) (βL := 1) (βR := 1) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).1
        have hvac_i : Integrable (fun r : ℝ × ℝ =>
            spinLiftTToR (spinOddLagBasisT m n) r * spinV1 a r.1 * spinV1 a r.2) := by
          have hpt : (fun r : ℝ × ℝ =>
              spinLiftTToR (spinOddLagBasisT m n) r * spinV1 a r.1 * spinV1 a r.2) =
              fun r => (1 / 2 : ℝ) * (lagPsi (1 / 2) m (r.1 ^ 2 / 2) * lagPsi (1 / 2) n (r.2 ^ 2 / 2) *
                  spinV1 a r.1 * spinV1 a r.2) +
                (1 / 2 : ℝ) * (lagPsi (1 / 2) n (r.1 ^ 2 / 2) * lagPsi (1 / 2) m (r.2 ^ 2 / 2) *
                  spinV1 a r.1 * spinV1 a r.2) := by
            ext r; unfold spinLiftTToR spinOddLagBasisT; ring
          rw [hpt]
          exact ((hVac_int m n).const_mul _).add ((hVac_int n m).const_mul _)
        exact ⟨hpair.1, hvac_i, hpair.2⟩
      · -- Radial lift of `hMaj a β₀`
        let hrad := meas.toRadAdmissible hXpos
        have ha_prob : virasoroProblem.totalShift ≤ a := by rw [virasoroProblem_totalShift]; exact ha
        have ha0 : 0 < a := by linarith
        obtain ⟨C, hC, hdec⟩ := FixedWeight.hMaj_decay (w := 1) le_rfl ha0 hβ₀ hβ₀2
        have hq : (virasoroProblem.w + 1 : ℝ) / 2 < (((1 + 2 : ℕ) : ℝ) / 2) := by
          rw [virasoroProblem_w]; norm_num
        have hdec' : ∀ t, 0 ≤ t → |Duality.hMaj a β₀ t| ≤
            C * (1 + t) ^ (-(((1 + 2 : ℕ) : ℝ) / 2)) * Real.exp (-4 * π * Real.sqrt (a * t)) := by
          intro t ht
          have h1 := hdec t ht
          rw [FixedWeight.hMaj_one] at h1
          exact h1.trans (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by
              have hsq : Real.sqrt (a * t) ≤ Real.sqrt (2 * a * t) :=
                Real.sqrt_le_sqrt (by nlinarith)
              nlinarith [Real.pi_pos])) (by positivity))
        obtain ⟨hh_int_on, hh_eq⟩ := Duality.proposition_P1 virasoroProblem ha_prob ha0 hrad
          (Duality.hMaj_mem_TestClass ha) hq hC hdec'
        have hmeas_sum : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
        have hrad_neg : hrad.ν (Ici 0)ᶜ = 0 := by
          change (spinRadMarginal meas.ν) (Ici 0)ᶜ = 0
          unfold spinRadMarginal
          rw [Measure.map_apply hmeas_sum measurableSet_Ici.compl]
          have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' (Ici 0)ᶜ ⊆ Xᶜ :=
            fun p hp hpX => hp (hXpos hpX)
          exact measure_mono_null hsub meas.supp
        have hrad_ae : ∀ᵐ t ∂hrad.ν, t ∈ Ici (0 : ℝ) := by
          have : ∀ᵐ t ∂hrad.ν, t ∉ (Ici 0)ᶜ := measure_eq_zero_iff_ae_notMem.mp hrad_neg
          filter_upwards [this] with t ht using not_not.mp ht
        have hh_int_rad : Integrable (Duality.hMaj a β₀) hrad.ν := by
          have h1 : Integrable (Duality.hMaj a β₀) (hrad.ν.restrict (Ici 0)) := hh_int_on
          rwa [Measure.restrict_eq_self_of_ae_mem hrad_ae] at h1
        have hh_int : Integrable (fun p : ℝ × ℝ => Duality.hMaj a β₀ (p.1 + p.2)) meas.ν := by
          have hrad_eq : hrad.ν = meas.ν.map (fun p : ℝ × ℝ => p.1 + p.2) := rfl
          rw [hrad_eq] at hh_int_rad
          exact (integrable_map_measure (Duality.measurable_hMaj a β₀).aestronglyMeasurable
            hmeas_sum.aemeasurable).mp hh_int_rad
        have hlift_eq : spinLiftTToR (fun p : ℝ × ℝ => Duality.hMaj a β₀ (p.1 + p.2)) =
            spinRadialLift (Duality.hMaj a β₀) := by
          ext r; unfold spinLiftTToR spinRadialLift; dsimp only
          rw [show r.1 ^ 2 / 2 + r.2 ^ 2 / 2 = (r.1 ^ 2 + r.2 ^ 2) / 2 by ring]
        have htest_h : SpinTestClass a (spinRadialLift (Duality.hMaj a β₀)) :=
          (spinTestClassJ_radialLift ha (Duality.hMaj_mem_TestClass ha)).base
        have hvac_i : Integrable (fun r : ℝ × ℝ =>
            spinLiftTToR (fun p : ℝ × ℝ => Duality.hMaj a β₀ (p.1 + p.2)) r *
              spinV1 a r.1 * spinV1 a r.2) := by
          rw [hlift_eq]; exact htest_h.int_vac ha
        refine ⟨hh_int, hvac_i, ?_⟩
        have hmap_int : ∫ p : ℝ × ℝ, Duality.hMaj a β₀ (p.1 + p.2) ∂meas.ν =
            ∫ t in Ici (0 : ℝ), Duality.hMaj a β₀ t ∂hrad.ν := by
          rw [Measure.restrict_eq_self_of_ae_mem hrad_ae]
          exact (integral_map hmeas_sum.aemeasurable
            (Duality.measurable_hMaj a β₀).aestronglyMeasurable).symm
        have hvac_eq : spinVacT a (fun p : ℝ × ℝ => Duality.hMaj a β₀ (p.1 + p.2)) =
            virasoroProblem.gVac a (Duality.hMaj a β₀) := by
          unfold spinVacT
          rw [hlift_eq, (spinM2_and_phiVac_radialLift ha (Duality.hMaj_mem_TestClass ha)).2]
        rw [hmap_int, hvac_eq]
        linarith
    · refine ⟨integrable_zero _ _ _, ?_, ?_⟩
      · simp [spinLiftTToR]
      · unfold spinVacT spinPhiVac spinLiftTToR; simp
    · rintro f g _ _ ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
      have h2 : (fun r : ℝ × ℝ => spinLiftTToR (f + g) r * spinV1 a r.1 * spinV1 a r.2) =
          fun r => spinLiftTToR f r * spinV1 a r.1 * spinV1 a r.2 +
            spinLiftTToR g r * spinV1 a r.1 * spinV1 a r.2 := by
        ext r; unfold spinLiftTToR; simp only [Pi.add_apply]; ring
      refine ⟨hf1.add hg1, by rw [h2]; exact hf2.add hg2, ?_⟩
      change ∫ p : ℝ × ℝ, f p + g p ∂meas.ν = _
      rw [integral_add hf1 hg1, hf3, hg3]
      unfold spinVacT spinPhiVac
      rw [h2, integral_add hf2 hg2]; ring
    · rintro c f _ ⟨hf1, hf2, hf3⟩
      have h2 : (fun r : ℝ × ℝ => spinLiftTToR (c • f) r * spinV1 a r.1 * spinV1 a r.2) =
          fun r => c * (spinLiftTToR f r * spinV1 a r.1 * spinV1 a r.2) := by
        ext r; unfold spinLiftTToR; simp only [Pi.smul_apply, smul_eq_mul]; ring
      refine ⟨hf1.const_mul c, by rw [h2]; exact hf2.const_mul c, ?_⟩
      change ∫ p : ℝ × ℝ, c * f p ∂meas.ν = _
      rw [integral_const_mul, hf3]
      unfold spinVacT spinPhiVac
      rw [h2, integral_const_mul]; ring
  intro Φ hΦ
  obtain ⟨hi, -, heq⟩ := hmain Φ hΦ
  exact ⟨hi, heq⟩

/-! ### Section 3: `sd:LP`(ii) conditional only on `sd:SD` -/

/-- **`sd:LP`(ii) conditional only on `sd:SD`**, discharging `SpinDLPi` with `spinDLPi`. -/
theorem spinDLPii_of_SD (hSD : SpinDSD) : SpinDLPii :=
  spinDLPii_of_props spinDLPi hSD

/-! ### Axiom guards -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDM

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDP

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDLPii_of_SD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDLPii_of_SD

end FormalResearch.ModularBootstrap.Spin
