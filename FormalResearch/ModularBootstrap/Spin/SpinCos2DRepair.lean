module

public import FormalResearch.ModularBootstrap.Spin.SpinCos2DOp
public import FormalResearch.ModularBootstrap.Spin.Defs
public import FormalResearch.ModularBootstrap.Integrality.RepairIdentity
public import FormalResearch.ModularBootstrap.Integrality.RepairTaylor
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Exact 2D cosine--Sonine repair (`int:cos2d-repair`)

`CFT/modular_bootstrap/paper/integrality_spin.tex`, Lemma INT-7C (`int:cos2d-repair`).

Given `R > 0`, `M : ℕ`, and finite measures `σ, μ` supported in `[a_L, a_L + 2] × [a_R, a_R + 2] ⊂ Q_R = [0, R]^2`
matching all bivariate polynomials `P(r_L) Q(r_R)` of bi-degree `≤ (M, M)`, this file constructs the
continuous repair density `ϱ : ℝ × ℝ → ℝ` from `cos2DOp_inv`, proves exact two-temperature crossing
`∫ X_{β_L, β_R} dσ - ∫ X_{β_L, β_R} dμ + ∫_{Q_∞ \ Q_R} X_{β_L, β_R} ϱ = 0` (`∀ β_L, β_R > 0`),
and establishes the exterior Taylor + Sonine decay bound `(int:r2d-bound)`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped FourierTransform Nat Polynomial

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap.Integrality

/-! ### Section 1: 1D Gaussian cosine integral and 2D crossing eigenfunction -/

lemma pow_div_factorial_le_exp_pow_spin (m : ℕ) (hm : 1 ≤ m) {x : ℝ} (hx : 0 ≤ x) :
    x ^ m / (Nat.factorial m : ℝ) ≤ (Real.exp 1 * x / (m : ℝ)) ^ m := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp : (m : ℝ) ^ m / (Nat.factorial m : ℝ) ≤ Real.exp m :=
    Real.pow_div_factorial_le_exp (m : ℝ) hm_pos.le m
  have hexp_pow : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hexp_pow] at hexp
  have hm_pow_pos : (0 : ℝ) < (m : ℝ) ^ m := pow_pos hm_pos m
  have h1 : 1 / (Nat.factorial m : ℝ) ≤ (Real.exp 1 / (m : ℝ)) ^ m := by
    rw [div_pow, le_div_iff₀ hm_pow_pos]
    calc 1 / (Nat.factorial m : ℝ) * (m : ℝ) ^ m = (m : ℝ) ^ m / (Nat.factorial m : ℝ) := by ring
      _ ≤ (Real.exp 1) ^ m := hexp
  calc x ^ m / (Nat.factorial m : ℝ) = x ^ m * (1 / (Nat.factorial m : ℝ)) := by ring
    _ ≤ x ^ m * (Real.exp 1 / (m : ℝ)) ^ m := mul_le_mul_of_nonneg_left h1 (pow_nonneg hx m)
    _ = (Real.exp 1 * x / (m : ℝ)) ^ m := by rw [← mul_pow]; congr 1; ring

private lemma fourier_gaussian_1d_spin {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
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

private lemma integral_even_univ_eq_two_Ici {g : ℝ → ℝ} (hg : Integrable g volume)
    (heven : ∀ x, g (-x) = g x) :
    ∫ x : ℝ, g x = 2 * ∫ s in Ici (0 : ℝ), g s := by
  have hsplit : ∫ x : ℝ, g x = (∫ x in Iio (0 : ℝ), g x) + ∫ x in Ici (0 : ℝ), g x := by
    rw [← setIntegral_univ, ← Iio_union_Ici]
    exact setIntegral_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici hg.integrableOn hg.integrableOn
  have hpre : Neg.neg ⁻¹' (Iio (0 : ℝ)) = Ioi (0 : ℝ) := by
    ext s; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]; constructor <;> intro h <;> linarith
  have hneg : ∫ x in Iio (0 : ℝ), g x = ∫ s in Ici (0 : ℝ), g s := by
    have hmp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume := Measure.measurePreserving_neg volume
    have heq := hmp.setIntegral_preimage_emb (Homeomorph.neg ℝ).measurableEmbedding g (Iio 0)
    rw [hpre] at heq
    have hae : volume.restrict (Ioi (0 : ℝ)) = volume.restrict (Ici (0 : ℝ)) :=
      Measure.restrict_congr_set Ioi_ae_eq_Ici
    rw [← heq, hae]
    exact setIntegral_congr_fun measurableSet_Ici fun s _ => heven s
  rw [hsplit, hneg, two_mul]

private lemma cos_gaussian_Ici {β : ℝ} (hβ : 0 < β) (r : ℝ) :
    2 * ∫ s in Ici (0 : ℝ), Real.cos (2 * π * r * s) * Real.exp (-π * β * s ^ 2) =
      β ^ (-(1 / 2 : ℝ)) * Real.exp (-π * r ^ 2 / β) := by
  have hint : Integrable (fun x : ℝ => Real.cos (2 * π * r * x) * Real.exp (-π * β * x ^ 2)) volume := by
    have hg : Integrable (fun x : ℝ => Real.exp (-(π * β) * x ^ 2)) volume :=
      integrable_exp_neg_mul_sq (by positivity)
    refine hg.mono' ((Real.continuous_cos.comp (by fun_prop)).mul
      (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    calc |Real.cos (2 * π * r * x)| * Real.exp (-π * β * x ^ 2)
        ≤ 1 * Real.exp (-π * β * x ^ 2) :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (Real.exp_pos _).le
      _ = Real.exp (-(π * β) * x ^ 2) := by ring_nf
  have heven : ∀ x : ℝ,
      Real.cos (2 * π * r * (-x)) * Real.exp (-π * β * (-x) ^ 2) =
        Real.cos (2 * π * r * x) * Real.exp (-π * β * x ^ 2) := fun x => by
    rw [show 2 * π * r * (-x) = -(2 * π * r * x) by ring, Real.cos_neg, neg_sq]
  rw [← integral_even_univ_eq_two_Ici hint heven]
  have hfou := fourier_gaussian_1d_spin hβ r
  have hre : (𝓕 (fun x : ℝ => (Real.exp (-π * β * x ^ 2) : ℂ)) r).re =
      ∫ x : ℝ, Real.cos (2 * π * r * x) * Real.exp (-π * β * x ^ 2) := by
    rw [Real.fourier_eq']
    have hint_c : Integrable (fun x : ℝ =>
        Complex.exp (↑(-2 * π * inner ℝ x r) * Complex.I) • (Real.exp (-π * β * x ^ 2) : ℂ)) volume := by
      have hg : Integrable (fun x : ℝ => Real.exp (-(π * β) * x ^ 2)) volume :=
        integrable_exp_neg_mul_sq (by positivity)
      refine hg.mono' (by fun_prop : Continuous fun x : ℝ =>
          Complex.exp (↑(-2 * π * inner ℝ x r) * Complex.I) •
            (Real.exp (-π * β * x ^ 2) : ℂ)).aestronglyMeasurable ?_
      refine Eventually.of_forall fun x => ?_
      rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      exact le_of_eq (by ring_nf)
    change (Complex.reCLM (∫ x : ℝ, _)) = _
    rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint_c]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Complex.reCLM_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial]
    rw [show (↑(-2 * π * (r * x)) * Complex.I : ℂ) = (-((2 * π * r * x : ℝ) : ℂ)) * Complex.I by
      push_cast; ring, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hrhs_re : (((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Real.exp (-π * β⁻¹ * r ^ 2) : ℂ)).re =
      β ^ (-(1 / 2 : ℝ)) * Real.exp (-π * r ^ 2 / β) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re, div_eq_mul_inv]
    ring_nf
  rw [← hre, hfou, hrhs_re]

/-- The full first-quadrant measure `Q_∞ = [0, ∞)^2` under Lebesgue measure. -/
noncomputable def cos2DFullMeasure : Measure (ℝ × ℝ) :=
  (volume : Measure (ℝ × ℝ)).restrict (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ))

instance sigmaFinite_cos2DFullMeasure : SigmaFinite cos2DFullMeasure := by
  unfold cos2DFullMeasure
  infer_instance

private lemma integrable_gaussian_2d {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)))
      ((volume.restrict (Ici (0 : ℝ))).prod (volume.restrict (Ici (0 : ℝ)))) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-(π * βL) * x ^ 2)) (volume.restrict (Ici 0)) :=
    (integrable_exp_neg_mul_sq (by positivity)).restrict
  have h2 : Integrable (fun y : ℝ => Real.exp (-(π * βR) * y ^ 2)) (volume.restrict (Ici 0)) :=
    (integrable_exp_neg_mul_sq (by positivity)).restrict
  refine (h1.mul_prod h2).congr (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [← Real.exp_add]
  congr 1; ring

private lemma kerTransform_gaussian_2d {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) (r : ℝ × ℝ) :
    kerTransform cos2DFullMeasure cos2DKernel
      (fun p => Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2))) r =
      (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-π * (r.1 ^ 2 / βL + r.2 ^ 2 / βR)) := by
  unfold kerTransform cos2DFullMeasure
  have hint_prod : Integrable (fun p : ℝ × ℝ =>
      cos2DKernel r p * Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)))
      ((volume.restrict (Ici (0 : ℝ))).prod (volume.restrict (Ici (0 : ℝ)))) := by
    refine ((integrable_gaussian_2d hβL hβR).const_mul 4).mono' ?_ ?_
    · exact ((continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).mul
        (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (abs_cos2DKernel_le r p) (Real.exp_pos _).le
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod _ hint_prod]
  have h_inner : ∀ sL : ℝ,
      ∫ sR in Ici (0 : ℝ), cos2DKernel r (sL, sR) * Real.exp (-π * (βL * sL ^ 2 + βR * sR ^ 2)) =
        (2 * Real.cos (2 * π * r.1 * sL) * Real.exp (-π * βL * sL ^ 2)) *
          (2 * ∫ sR in Ici (0 : ℝ), Real.cos (2 * π * r.2 * sR) * Real.exp (-π * βR * sR ^ 2)) := by
    intro sL
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici fun sR _ => ?_
    unfold cos2DKernel
    have hexp : Real.exp (-π * (βL * sL ^ 2 + βR * sR ^ 2)) =
        Real.exp (-π * βL * sL ^ 2) * Real.exp (-π * βR * sR ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp]; ring
  simp_rw [h_inner, integral_mul_const, cos_gaussian_Ici hβR r.2]
  have hexp_r : Real.exp (-π * (r.1 ^ 2 / βL + r.2 ^ 2 / βR)) =
      Real.exp (-π * r.1 ^ 2 / βL) * Real.exp (-π * r.2 ^ 2 / βR) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpow_b : (βL * βR) ^ (-(1 / 2 : ℝ)) = βL ^ (-(1 / 2 : ℝ)) * βR ^ (-(1 / 2 : ℝ)) :=
    Real.mul_rpow hβL.le hβR.le
  have hpull : (∫ sL in Ici (0 : ℝ), 2 * Real.cos (2 * π * r.1 * sL) * Real.exp (-π * βL * sL ^ 2)) =
      2 * ∫ sL in Ici (0 : ℝ), Real.cos (2 * π * r.1 * sL) * Real.exp (-π * βL * sL ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici fun sL _ => by ring
  rw [hpull, cos_gaussian_Ici hβL r.1, hexp_r, hpow_b]
  ring

/-- Eigenfunction relation for `spinThermalX`: `H_{2D}(X_{βL, βR}) = -X_{βL, βR}` on `Q_∞`. -/
lemma kerTransform_spinThermalX {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) (r : ℝ × ℝ) :
    kerTransform cos2DFullMeasure cos2DKernel
      (fun p => spinThermalX βL βR (p.1 ^ 2 / 2) (p.2 ^ 2 / 2)) r =
      -spinThermalX βL βR (r.1 ^ 2 / 2) (r.2 ^ 2 / 2) := by
  have hg1 : Integrable (fun p : ℝ × ℝ =>
      cos2DKernel r p * Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2))) cos2DFullMeasure := by
    unfold cos2DFullMeasure
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine ((integrable_gaussian_2d hβL hβR).const_mul 4).mono' ?_ ?_
    · exact ((continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).mul
        (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (abs_cos2DKernel_le r p) (Real.exp_pos _).le
  have hg2 : Integrable (fun p : ℝ × ℝ =>
      cos2DKernel r p * Real.exp (-π * (βL⁻¹ * p.1 ^ 2 + βR⁻¹ * p.2 ^ 2))) cos2DFullMeasure := by
    unfold cos2DFullMeasure
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine ((integrable_gaussian_2d (inv_pos.mpr hβL) (inv_pos.mpr hβR)).const_mul 4).mono' ?_ ?_
    · exact ((continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).mul
        (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (abs_cos2DKernel_le r p) (Real.exp_pos _).le
  have hsplit : (fun p : ℝ × ℝ => cos2DKernel r p * spinThermalX βL βR (p.1 ^ 2 / 2) (p.2 ^ 2 / 2)) =
      fun p => cos2DKernel r p * Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) -
        (βL * βR) ^ (-(1 / 2 : ℝ)) *
          (cos2DKernel r p * Real.exp (-π * (βL⁻¹ * p.1 ^ 2 + βR⁻¹ * p.2 ^ 2))) := by
    ext p
    unfold spinThermalX
    have h1 : -2 * π * (βL * (p.1 ^ 2 / 2) + βR * (p.2 ^ 2 / 2)) =
        -π * (βL * p.1 ^ 2 + βR * p.2 ^ 2) := by ring
    have h2 : -2 * π * (p.1 ^ 2 / 2 / βL + p.2 ^ 2 / 2 / βR) =
        -π * (βL⁻¹ * p.1 ^ 2 + βR⁻¹ * p.2 ^ 2) := by field_simp
    rw [h1, h2]; ring
  unfold kerTransform
  rw [hsplit, integral_sub hg1 (hg2.const_mul _), integral_const_mul]
  change kerTransform cos2DFullMeasure cos2DKernel (fun p => Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2))) r -
      (βL * βR) ^ (-(1 / 2 : ℝ)) *
        kerTransform cos2DFullMeasure cos2DKernel (fun p => Real.exp (-π * (βL⁻¹ * p.1 ^ 2 + βR⁻¹ * p.2 ^ 2))) r = _
  rw [kerTransform_gaussian_2d hβL hβR r, kerTransform_gaussian_2d (inv_pos.mpr hβL) (inv_pos.mpr hβR) r]
  have hinv_pow : (βL⁻¹ * βR⁻¹) ^ (-(1 / 2 : ℝ)) = ((βL * βR) ^ (-(1 / 2 : ℝ)))⁻¹ := by
    rw [← mul_inv, Real.inv_rpow (mul_pos hβL hβR).le]
  have hpow_ne : (βL * βR) ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos (mul_pos hβL hβR) _).ne'
  rw [hinv_pow, ← mul_assoc, mul_inv_cancel₀ hpow_ne, one_mul]
  unfold spinThermalX
  have h1 : -2 * π * (βL * (r.1 ^ 2 / 2) + βR * (r.2 ^ 2 / 2)) =
      -π * (βL * r.1 ^ 2 + βR * r.2 ^ 2) := by ring
  have h2 : -2 * π * (r.1 ^ 2 / 2 / βL + r.2 ^ 2 / 2 / βR) =
      -π * (r.1 ^ 2 / βL + r.2 ^ 2 / βR) := by field_simp
  have h3 : r.1 ^ 2 / βL⁻¹ + r.2 ^ 2 / βR⁻¹ = βL * r.1 ^ 2 + βR * r.2 ^ 2 := by field_simp
  rw [h1, h2, h3]
  ring

/-! ### Section 2: 1D cosine Taylor approximation on `[a, a + 2]` and 2D dual bound -/

private lemma iteratedDeriv_cos_mul (c : ℝ) (m : ℕ) :
    iteratedDeriv m (fun s : ℝ => Real.cos (c * s)) =
      fun s => c ^ m * Real.cos (c * s + (m : ℝ) * (π / 2)) := by
  induction m with
  | zero => ext s; simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    ext s
    have hlin : HasDerivAt (fun t : ℝ => c * t + (m : ℝ) * (π / 2)) c s := by
      have h1 : HasDerivAt (fun t : ℝ => c * t) c s := by
        simpa using (hasDerivAt_id s).const_mul c
      simpa using h1.add_const ((m : ℝ) * (π / 2))
    have hcos := (Real.hasDerivAt_cos (c * s + (m : ℝ) * (π / 2))).comp s hlin
    have hmul := hcos.const_mul (c ^ m)
    have hderiv : deriv (fun s => c ^ m * Real.cos (c * s + (m : ℝ) * (π / 2))) s =
        c ^ m * (-Real.sin (c * s + (m : ℝ) * (π / 2)) * c) := hmul.deriv
    rw [hderiv]
    rw [show ((m + 1 : ℕ) : ℝ) * (π / 2) = (m : ℝ) * (π / 2) + π / 2 by push_cast; ring,
      ← add_assoc, Real.cos_add_pi_div_two, pow_succ]
    ring

private lemma exists_poly_cos_approx (M : ℕ) {r a : ℝ} (hr : 0 ≤ r) :
    ∃ P : ℝ[X], P.degree ≤ M ∧
      (∀ s ∈ Icc a (a + 2), |P.eval s| ≤ 2) ∧
      (∀ s ∈ Icc a (a + 2),
        |Real.cos (2 * π * r * s) - P.eval s| ≤
          min (1 : ℝ) ((2 * π * Real.exp 1 * r / ((M + 1 : ℕ) : ℝ)) ^ (M + 1))) := by
  let m : ℕ := M + 1
  let d : ℝ := min (1 : ℝ) ((2 * π * Real.exp 1 * r / (m : ℝ)) ^ m)
  by_cases h1 : 1 ≤ (2 * π * Real.exp 1 * r / (m : ℝ)) ^ m
  · refine ⟨0, by simp, fun s _ => by simp, fun s _ => ?_⟩
    simp only [Polynomial.eval_zero, sub_zero]
    rw [min_eq_left h1]
    exact Real.abs_cos_le_one _
  · have hlt : (2 * π * Real.exp 1 * r / (m : ℝ)) ^ m < 1 := lt_of_not_ge h1
    let s0 : ℝ := a + 1
    let f : ℝ → ℝ := fun s => Real.cos (2 * π * r * s)
    let P : ℝ[X] := ∑ k ∈ Finset.range (M + 1),
      Polynomial.C (iteratedDeriv k f s0 / (k ! : ℝ)) * (Polynomial.X - Polynomial.C s0) ^ k
    have hPdeg : P.degree ≤ M := by
      refine (Polynomial.degree_sum_le _ _).trans ?_
      refine Finset.sup_le fun k hk => ?_
      have hk' : k ≤ M := by simpa [Nat.lt_succ_iff] using hk
      calc (Polynomial.C (iteratedDeriv k f s0 / (k ! : ℝ)) * (Polynomial.X - Polynomial.C s0) ^ k).degree
          ≤ (Polynomial.C (iteratedDeriv k f s0 / (k ! : ℝ))).degree +
              ((Polynomial.X - Polynomial.C s0) ^ k).degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + (k : WithBot ℕ) := by
            gcongr
            · exact Polynomial.degree_C_le
            · refine (Polynomial.degree_pow_le _ _).trans ?_
              rw [Polynomial.degree_X_sub_C]
              simp
        _ ≤ (M : WithBot ℕ) := by rw [zero_add]; exact WithBot.coe_le_coe.mpr hk'
    have hPeval : ∀ s, P.eval s =
        ∑ k ∈ Finset.range (M + 1), iteratedDeriv k f s0 / (k ! : ℝ) * (s - s0) ^ k := by
      intro s
      change (Polynomial.evalRingHom s) P = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => by simp
    have hf_smooth : ContDiff ℝ (M + 1 : ℕ) f :=
      Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
    have hderiv_bd : ∀ y : ℝ, |iteratedDeriv (M + 1) f y| ≤ (2 * π * r) ^ m := by
      intro y
      have hd := congrFun (iteratedDeriv_cos_mul (2 * π * r) (M + 1)) y
      rw [hd, abs_mul, abs_of_nonneg (pow_nonneg (by positivity) _)]
      exact mul_le_of_le_one_right (pow_nonneg (by positivity) _) (Real.abs_cos_le_one _)
    have happrox : ∀ s ∈ Icc a (a + 2), |f s - P.eval s| ≤ d := by
      intro s hs
      rw [hPeval s]
      have hs0 : |s - s0| ≤ 1 := abs_le.mpr ⟨by show -1 ≤ s - (a + 1); linarith [hs.1],
        by show s - (a + 1) ≤ 1; linarith [hs.2]⟩
      have htr := taylor_remainder_bound M hf_smooth (x₀ := s0) (x := s)
        (C := (2 * π * r) ^ m) (fun y _ => hderiv_bd y)
      have hpow1 : |s - s0| ^ m ≤ 1 := by simpa using pow_le_pow_left₀ (abs_nonneg _) hs0 m
      have hfac := pow_div_factorial_le_exp_pow_spin m (Nat.succ_le_succ (Nat.zero_le M))
        (by positivity : 0 ≤ 2 * π * r)
      have hfac' : (2 * π * r) ^ m * |s - s0| ^ m / (m ! : ℝ) ≤
          (2 * π * Real.exp 1 * r / (m : ℝ)) ^ m := by
        calc (2 * π * r) ^ m * |s - s0| ^ m / (m ! : ℝ)
            ≤ (2 * π * r) ^ m * 1 / (m ! : ℝ) := by gcongr
          _ = (2 * π * r) ^ m / (m ! : ℝ) := by ring
          _ ≤ (Real.exp 1 * (2 * π * r) / (m : ℝ)) ^ m := hfac
          _ = (2 * π * Real.exp 1 * r / (m : ℝ)) ^ m := by congr 1; ring
      have htr' := htr.trans hfac'
      exact htr'.trans_eq (min_eq_right hlt.le).symm
    refine ⟨P, hPdeg, fun s hs => ?_, happrox⟩
    have ha := happrox s hs
    have hd1 : d ≤ 1 := min_le_left _ _
    calc |P.eval s| = |f s - (f s - P.eval s)| := by ring_nf
      _ ≤ |f s| + |f s - P.eval s| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (ha.trans hd1)
      _ = 2 := by norm_num

private lemma kerDual_cos2d_bound {M : ℕ} {aL aR : ℝ}
    {σ μ : Measure (ℝ × ℝ)} [IsFiniteMeasure σ] [IsFiniteMeasure μ]
    (hσ : σ (Icc aL (aL + 2) ×ˢ Icc aR (aR + 2))ᶜ = 0)
    (hμ : μ (Icc aL (aL + 2) ×ˢ Icc aR (aR + 2))ᶜ = 0)
    (hmom : ∀ P Q : ℝ[X], P.degree ≤ M → Q.degree ≤ M →
      ∫ p, P.eval p.1 * Q.eval p.2 ∂σ = ∫ p, P.eval p.1 * Q.eval p.2 ∂μ)
    {r : ℝ × ℝ} (hr1 : 0 ≤ r.1) (hr2 : 0 ≤ r.2) :
    let m : ℕ := M + 1
    |kerDual cos2DKernel σ μ r| ≤ 8 * (σ.real univ + μ.real univ) *
      (min (1 : ℝ) ((2 * π * Real.exp 1 * r.1 / (m : ℝ)) ^ m) +
       min (1 : ℝ) ((2 * π * Real.exp 1 * r.2 / (m : ℝ)) ^ m)) := by
  let m : ℕ := M + 1
  let dL : ℝ := min (1 : ℝ) ((2 * π * Real.exp 1 * r.1 / (m : ℝ)) ^ m)
  let dR : ℝ := min (1 : ℝ) ((2 * π * Real.exp 1 * r.2 / (m : ℝ)) ^ m)
  obtain ⟨PL, hPL_deg, hPL_bd, hPL_app⟩ := exists_poly_cos_approx M (a := aL) hr1
  obtain ⟨PR, hPR_deg, hPR_bd, hPR_app⟩ := exists_poly_cos_approx M (a := aR) hr2
  have hmom_eq := hmom PL PR hPL_deg hPR_deg
  have hI_ker : ∀ (η : Measure (ℝ × ℝ)) [IsFiniteMeasure η],
      Integrable (fun p : ℝ × ℝ => cos2DKernel r p) η := fun η _ =>
    Integrable.of_bound (continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      4 (Eventually.of_forall fun p => abs_cos2DKernel_le r p)
  have hI_poly : ∀ (η : Measure (ℝ × ℝ)) [IsFiniteMeasure η],
      η (Icc aL (aL + 2) ×ˢ Icc aR (aR + 2))ᶜ = 0 →
      Integrable (fun p : ℝ × ℝ => 4 * (PL.eval p.1 * PR.eval p.2)) η := fun η _ hη => by
    have hcont : Continuous (fun p : ℝ × ℝ => 4 * (PL.eval p.1 * PR.eval p.2)) :=
      continuous_const.mul ((PL.continuous.comp continuous_fst).mul (PR.continuous.comp continuous_snd))
    have h1 : IntegrableOn (fun p : ℝ × ℝ => 4 * (PL.eval p.1 * PR.eval p.2))
        (Icc aL (aL + 2) ×ˢ Icc aR (aR + 2)) η :=
      hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hae : ∀ᵐ p ∂η, p ∈ Icc aL (aL + 2) ×ˢ Icc aR (aR + 2) :=
      (measure_eq_zero_iff_ae_notMem.mp hη).mono fun p hp => Set.notMem_compl_iff.mp hp
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h1
  have h_bd_meas : ∀ (η : Measure (ℝ × ℝ)) [IsFiniteMeasure η],
      η (Icc aL (aL + 2) ×ˢ Icc aR (aR + 2))ᶜ = 0 →
      ‖∫ p, (cos2DKernel r p - 4 * (PL.eval p.1 * PR.eval p.2)) ∂η‖ ≤
        8 * (dL + dR) * η.real univ := by
    intro η _ hη
    refine norm_integral_le_of_norm_le_const ?_
    have hae : ∀ᵐ p ∂η, p ∈ Icc aL (aL + 2) ×ˢ Icc aR (aR + 2) :=
      (measure_eq_zero_iff_ae_notMem.mp hη).mono fun p hp => Set.notMem_compl_iff.mp hp
    filter_upwards [hae] with p hp
    have huL : |Real.cos (2 * π * r.1 * p.1)| ≤ 1 := Real.abs_cos_le_one _
    have huR : |Real.cos (2 * π * r.2 * p.2)| ≤ 1 := Real.abs_cos_le_one _
    have hpL : |PL.eval p.1| ≤ 2 := hPL_bd p.1 hp.1
    have hdL : |Real.cos (2 * π * r.1 * p.1) - PL.eval p.1| ≤ dL := hPL_app p.1 hp.1
    have hdR : |Real.cos (2 * π * r.2 * p.2) - PR.eval p.2| ≤ dR := hPR_app p.2 hp.2
    have hdiff_pt : |Real.cos (2 * π * r.1 * p.1) * Real.cos (2 * π * r.2 * p.2) -
        PL.eval p.1 * PR.eval p.2| ≤ 2 * (dL + dR) := by
      have hid : Real.cos (2 * π * r.1 * p.1) * Real.cos (2 * π * r.2 * p.2) -
          PL.eval p.1 * PR.eval p.2 =
          (Real.cos (2 * π * r.1 * p.1) - PL.eval p.1) * Real.cos (2 * π * r.2 * p.2) +
            PL.eval p.1 * (Real.cos (2 * π * r.2 * p.2) - PR.eval p.2) := by ring
      rw [hid]
      calc |(Real.cos (2 * π * r.1 * p.1) - PL.eval p.1) * Real.cos (2 * π * r.2 * p.2) +
              PL.eval p.1 * (Real.cos (2 * π * r.2 * p.2) - PR.eval p.2)|
          ≤ |(Real.cos (2 * π * r.1 * p.1) - PL.eval p.1) * Real.cos (2 * π * r.2 * p.2)| +
              |PL.eval p.1 * (Real.cos (2 * π * r.2 * p.2) - PR.eval p.2)| := abs_add_le _ _
        _ = |Real.cos (2 * π * r.1 * p.1) - PL.eval p.1| * |Real.cos (2 * π * r.2 * p.2)| +
              |PL.eval p.1| * |Real.cos (2 * π * r.2 * p.2) - PR.eval p.2| := by
            rw [abs_mul, abs_mul]
        _ ≤ dL * 1 + 2 * dR := by gcongr
        _ ≤ 2 * (dL + dR) := by have : 0 ≤ dL := le_min zero_le_one (by positivity); linarith
    rw [Real.norm_eq_abs]
    have h4 : cos2DKernel r p - 4 * (PL.eval p.1 * PR.eval p.2) =
        4 * (Real.cos (2 * π * r.1 * p.1) * Real.cos (2 * π * r.2 * p.2) - PL.eval p.1 * PR.eval p.2) := by
      unfold cos2DKernel; ring
    rw [h4, abs_mul, abs_of_pos (by norm_num)]
    linarith
  have hdiff_id : kerDual cos2DKernel σ μ r =
      ∫ p, (cos2DKernel r p - 4 * (PL.eval p.1 * PR.eval p.2)) ∂σ -
        ∫ p, (cos2DKernel r p - 4 * (PL.eval p.1 * PR.eval p.2)) ∂μ := by
    unfold kerDual
    rw [integral_sub (hI_ker σ) (hI_poly σ hσ), integral_sub (hI_ker μ) (hI_poly μ hμ),
      integral_const_mul, integral_const_mul, hmom_eq]
    ring
  rw [hdiff_id]
  calc |∫ p, (cos2DKernel r p - 4 * (PL.eval p.1 * PR.eval p.2)) ∂σ -
          ∫ p, (cos2DKernel r p - 4 * (PL.eval p.1 * PR.eval p.2)) ∂μ|
      ≤ ‖∫ p, (cos2DKernel r p - 4 * (PL.eval p.1 * PR.eval p.2)) ∂σ‖ +
          ‖∫ p, (cos2DKernel r p - 4 * (PL.eval p.1 * PR.eval p.2)) ∂μ‖ := by
        simpa [Real.norm_eq_abs] using abs_sub _ _
    _ ≤ 8 * (dL + dR) * σ.real univ + 8 * (dL + dR) * μ.real univ :=
        add_le_add (h_bd_meas σ hσ) (h_bd_meas μ hμ)
    _ = 8 * (σ.real univ + μ.real univ) * (dL + dR) := by ring

/-! ### Section 3: Exact 2D cosine--Sonine repair (`int:cos2d-repair`) -/

/-- **Lemma INT-7C (`int:cos2d-repair`, `integrality_spin.tex`)**:
for any `R > 0`, `M : ℕ`, and finite measures `σ, μ` supported in `[a_L, a_L+2] × [a_R, a_R+2] ⊂ Q_R = [0, R]^2`
annihilating all bivariate polynomials of bi-degree `≤ (M, M)`, there exists a continuous exterior
repair density `ϱ` on `ℝ × ℝ` satisfying exact two-temperature crossing against `spinThermalX` on
`Q_∞ \ Q_R` and the exponential-in-`M` bound `(int:r2d-bound)`. -/
theorem cos2d_repair {R : ℝ} (hR : 0 < R) (M : ℕ) {aL aR : ℝ}
    (_haL0 : 0 ≤ aL) (_haLR : aL + 2 ≤ R) (_haR0 : 0 ≤ aR) (_haRR : aR + 2 ≤ R)
    {σ μ : Measure (ℝ × ℝ)} [IsFiniteMeasure σ] [IsFiniteMeasure μ]
    (hσ : σ (Icc aL (aL + 2) ×ˢ Icc aR (aR + 2))ᶜ = 0)
    (hμ : μ (Icc aL (aL + 2) ×ˢ Icc aR (aR + 2))ᶜ = 0)
    (hmom : ∀ P Q : ℝ[X], P.degree ≤ M → Q.degree ≤ M →
      ∫ p, P.eval p.1 * Q.eval p.2 ∂σ = ∫ p, P.eval p.1 * Q.eval p.2 ∂μ) :
    ∃ ϱ : ℝ × ℝ → ℝ, Continuous ϱ ∧
      (∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
        IntegrableOn (fun r : ℝ × ℝ => Real.exp (-π * (βL * r.1 ^ 2 + βR * r.2 ^ 2)) * |ϱ r|)
          (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) \ cos2DBandSet R) ∧
        IntegrableOn (fun r : ℝ × ℝ => Real.exp (-π * (r.1 ^ 2 / βL + r.2 ^ 2 / βR)) * |ϱ r|)
          (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) \ cos2DBandSet R) ∧
        (∫ p : ℝ × ℝ, spinThermalX βL βR (p.1 ^ 2 / 2) (p.2 ^ 2 / 2) ∂σ -
          ∫ p : ℝ × ℝ, spinThermalX βL βR (p.1 ^ 2 / 2) (p.2 ^ 2 / 2) ∂μ +
          ∫ r in (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) \ cos2DBandSet R),
            spinThermalX βL βR (r.1 ^ 2 / 2) (r.2 ^ 2 / 2) * ϱ r = 0)) ∧
      (∀ {r : ℝ × ℝ}, 0 ≤ r.1 → 0 ≤ r.2 → r ∉ cos2DBandSet R →
        let m : ℕ := M + 1
        |ϱ r| ≤ 12 * (σ.real univ + μ.real univ) *
            (min (1 : ℝ) ((2 * π * Real.exp 1 * r.1 / (m : ℝ)) ^ m) +
             min (1 : ℝ) ((2 * π * Real.exp 1 * r.2 / (m : ℝ)) ^ m)) +
          96 * R ^ 2 * max 2 (256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2)) *
            (σ.real univ + μ.real univ) * (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m) := by
  let m : ℕ := M + 1
  let Λ : ℝ := max 2 (256 * π ^ 2 * R ^ 4 * Real.exp (8 * π * R ^ 2))
  have hΛ0 : 0 ≤ Λ := le_trans (by norm_num) (le_max_left _ _)
  let hη : ℝ × ℝ → ℝ := kerDual cos2DKernel σ μ
  have hhη_cont : Continuous hη := by
    have hc1 : Continuous (fun r : ℝ × ℝ => ∫ s, cos2DKernel r s ∂σ) := by
      rw [continuous_iff_continuousAt]
      intro r₀
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => (4 : ℝ)) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun r =>
          (continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact Eventually.of_forall fun r => Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs]; exact abs_cos2DKernel_le r s
      · exact integrable_const _
      · exact Eventually.of_forall fun s =>
          (continuous_cos2DKernel.comp (continuous_id.prodMk continuous_const)).continuousAt
    have hc2 : Continuous (fun r : ℝ × ℝ => ∫ s, cos2DKernel r s ∂μ) := by
      rw [continuous_iff_continuousAt]
      intro r₀
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => (4 : ℝ)) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun r =>
          (continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · exact Eventually.of_forall fun r => Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs]; exact abs_cos2DKernel_le r s
      · exact integrable_const _
      · exact Eventually.of_forall fun s =>
          (continuous_cos2DKernel.comp (continuous_id.prodMk continuous_const)).continuousAt
    exact hc1.sub hc2
  have hhη_mem : MemLp hη 2 (cos2DBandMeasure R) :=
    memLp_cos2DBandMeasure_of_continuous hhη_cont
  obtain ⟨A_inv, hA_right, _, hA_norm⟩ := cos2DOp_inv hR
  let f_L2 : Lp ℝ 2 (cos2DBandMeasure R) := A_inv (hhη_mem.toLp hη)
  let f₀ : ℝ × ℝ → ℝ := (cos2DBandSet R).indicator (f_L2 : ℝ × ℝ → ℝ)
  have hf_raw_eq : ∀ r : ℝ × ℝ,
      kerTransform cos2DFullMeasure cos2DKernel f₀ r = rawCos2DOp R f_L2 r := by
    intro r
    unfold kerTransform rawCos2DOp
    have h1 : ∫ s, cos2DKernel r s * f₀ s ∂cos2DFullMeasure =
        ∫ s in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ), cos2DKernel r s * f₀ s := rfl
    have h2 : ∫ s, cos2DKernel r s * (f_L2 : ℝ × ℝ → ℝ) s ∂cos2DBandMeasure R =
        ∫ s in cos2DBandSet R, cos2DKernel r s * (f_L2 : ℝ × ℝ → ℝ) s := rfl
    rw [h1, h2, ← integral_indicator (measurableSet_Ici.prod measurableSet_Ici),
      ← integral_indicator (measurableSet_cos2DBandSet R)]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    by_cases hs : s ∈ cos2DBandSet R
    · have hs' : s ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) := ⟨hs.1.1, hs.2.1⟩
      dsimp only [f₀]
      rw [Set.indicator_of_mem hs', Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    · by_cases hs' : s ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)
      · dsimp only [f₀]
        rw [Set.indicator_of_mem hs', Set.indicator_of_notMem hs, mul_zero, Set.indicator_of_notMem hs]
      · dsimp only [f₀]
        rw [Set.indicator_of_notMem hs', Set.indicator_of_notMem hs]
  let ϱ : ℝ × ℝ → ℝ := fun r => hη r - kerTransform cos2DFullMeasure cos2DKernel f₀ r
  have hϱ_cont : Continuous ϱ := by
    have hU_cont : Continuous (kerTransform cos2DFullMeasure cos2DKernel f₀) := by
      rw [show kerTransform cos2DFullMeasure cos2DKernel f₀ = rawCos2DOp R f_L2 from
        funext hf_raw_eq]
      exact continuous_rawCos2DOp f_L2
    exact hhη_cont.sub hU_cont
  -- Bounds on `‖hη‖_{L^2(Q_R)}`, `‖f₀‖_{L^2(Q_∞)}`, and `ϱ`.
  have hhη_L2 : Real.sqrt (∫ s in cos2DBandSet R, hη s ^ 2) ≤
      16 * R * (σ.real univ + μ.real univ) * (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m := by
    let C_band : ℝ := 16 * (σ.real univ + μ.real univ) * (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m
    have hCb : 0 ≤ C_band := by positivity
    have hpt : ∀ s ∈ cos2DBandSet R, hη s ^ 2 ≤ C_band ^ 2 := by
      intro s hs
      have hbd := kerDual_cos2d_bound hσ hμ hmom hs.1.1 hs.2.1
      have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
      have hs1_nn : 0 ≤ 2 * π * Real.exp 1 * s.1 / (m : ℝ) := by
        have := hs.1.1; positivity
      have hs2_nn : 0 ≤ 2 * π * Real.exp 1 * s.2 / (m : ℝ) := by
        have := hs.2.1; positivity
      have hpow1 : (2 * π * Real.exp 1 * s.1 / (m : ℝ)) ^ m ≤
          (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m :=
        pow_le_pow_left₀ hs1_nn (by gcongr; exact hs.1.2) m
      have hpow2 : (2 * π * Real.exp 1 * s.2 / (m : ℝ)) ^ m ≤
          (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m :=
        pow_le_pow_left₀ hs2_nn (by gcongr; exact hs.2.2) m
      have hd_sum : min (1 : ℝ) ((2 * π * Real.exp 1 * s.1 / (m : ℝ)) ^ m) +
          min (1 : ℝ) ((2 * π * Real.exp 1 * s.2 / (m : ℝ)) ^ m) ≤
          2 * (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m := by
        calc min (1 : ℝ) ((2 * π * Real.exp 1 * s.1 / (m : ℝ)) ^ m) +
              min (1 : ℝ) ((2 * π * Real.exp 1 * s.2 / (m : ℝ)) ^ m)
            ≤ (2 * π * Real.exp 1 * s.1 / (m : ℝ)) ^ m +
                (2 * π * Real.exp 1 * s.2 / (m : ℝ)) ^ m :=
              add_le_add (min_le_right _ _) (min_le_right _ _)
          _ ≤ (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m +
                (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m := add_le_add hpow1 hpow2
          _ = 2 * (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m := by ring
      have hηs : |hη s| ≤ C_band := by
        calc |hη s| ≤ 8 * (σ.real univ + μ.real univ) *
              (min (1 : ℝ) ((2 * π * Real.exp 1 * s.1 / (m : ℝ)) ^ m) +
               min (1 : ℝ) ((2 * π * Real.exp 1 * s.2 / (m : ℝ)) ^ m)) := hbd
          _ ≤ 8 * (σ.real univ + μ.real univ) * (2 * (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m) := by
              gcongr
          _ = C_band := by dsimp [C_band]; ring
      rw [← sq_abs (hη s)]
      exact pow_le_pow_left₀ (abs_nonneg _) hηs 2
    have hlhs_int : IntegrableOn (fun s => hη s ^ 2) (cos2DBandSet R) volume :=
      (hhη_cont.pow 2).continuousOn.integrableOn_compact (isCompact_cos2DBandSet R)
    have hconst_int : IntegrableOn (fun _ : ℝ × ℝ => C_band ^ 2) (cos2DBandSet R) volume :=
      integrableOn_const (hs := (volume_cos2DBandSet_lt_top R).ne)
    have hsq_le : ∫ s in cos2DBandSet R, hη s ^ 2 ≤ (16 * R * (σ.real univ + μ.real univ) *
        (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m) ^ 2 := by
      calc ∫ s in cos2DBandSet R, hη s ^ 2
          ≤ ∫ _s in cos2DBandSet R, C_band ^ 2 :=
            setIntegral_mono_on hlhs_int hconst_int (measurableSet_cos2DBandSet R) hpt
        _ = (cos2DBandMeasure R).real univ * C_band ^ 2 := by
            rw [setIntegral_const, smul_eq_mul, mul_comm, volume_real_cos2DBandSet]; ring
        _ = R ^ 2 * C_band ^ 2 := by rw [cos2DBandMeasure_real_univ hR.le]
        _ = (16 * R * (σ.real univ + μ.real univ) * (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m) ^ 2 := by
            dsimp [C_band]; ring
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq_le⟩
  have hsub_band : cos2DBandSet R ⊆ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) := fun p hp => ⟨hp.1.1, hp.2.1⟩
  have hrest_eq : cos2DFullMeasure.restrict (cos2DBandSet R) = cos2DBandMeasure R := by
    unfold cos2DFullMeasure cos2DBandMeasure
    rw [Measure.restrict_restrict (measurableSet_cos2DBandSet R), inter_eq_left.mpr hsub_band]
  have hf0_meas : Measurable f₀ :=
    ((Lp.stronglyMeasurable f_L2).measurable).indicator (measurableSet_cos2DBandSet R)
  have hf0_sq_int : Integrable (fun s => f₀ s ^ 2) cos2DFullMeasure := by
    have heq : (fun s => f₀ s ^ 2) =
        (cos2DBandSet R).indicator (fun s => (f_L2 : ℝ × ℝ → ℝ) s ^ 2) := by
      ext s; by_cases hs : s ∈ cos2DBandSet R <;> simp [f₀, hs]
    rw [heq, integrable_indicator_iff (measurableSet_cos2DBandSet R)]
    show Integrable (fun s => (f_L2 : ℝ × ℝ → ℝ) s ^ 2) (cos2DFullMeasure.restrict (cos2DBandSet R))
    rw [hrest_eq]
    exact (Lp.memLp f_L2).integrable_sq
  have hf0_mem : MemLp f₀ 2 cos2DFullMeasure :=
    (memLp_two_iff_integrable_sq hf0_meas.aestronglyMeasurable).mpr hf0_sq_int
  have hf0_L2_eq : ∫ s, f₀ s ^ 2 ∂cos2DFullMeasure = ‖f_L2‖ ^ 2 := by
    have heq : (fun s => f₀ s ^ 2) =
        (cos2DBandSet R).indicator (fun s => (f_L2 : ℝ × ℝ → ℝ) s ^ 2) := by
      ext s; by_cases hs : s ∈ cos2DBandSet R <;> simp [f₀, hs]
    rw [heq, integral_indicator (measurableSet_cos2DBandSet R), hrest_eq]
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp [sq]
  have hf_L2_norm : ‖f_L2‖ ≤ Λ * Real.sqrt (∫ s in cos2DBandSet R, hη s ^ 2) := by
    have hnorm := (A_inv.le_opNorm (hhη_mem.toLp hη)).trans
      (mul_le_mul_of_nonneg_right hA_norm (norm_nonneg _))
    have hhη_sq : ‖hhη_mem.toLp hη‖ = Real.sqrt (∫ s in cos2DBandSet R, hη s ^ 2) := by
      rw [← lp_norm_sq_cos2DBandMeasure hhη_mem, Real.sqrt_sq (norm_nonneg _)]
    exact hnorm.trans_eq (by rw [hhη_sq])
  have hΛ_sq : ∫ s, f₀ s ^ 2 ∂cos2DFullMeasure ≤
      Λ ^ 2 * ∫ s in cos2DBandSet R, hη s ^ 2 ∂cos2DFullMeasure := by
    rw [hf0_L2_eq]
    have hband_eq : ∫ s in cos2DBandSet R, hη s ^ 2 ∂cos2DFullMeasure =
        ∫ s in cos2DBandSet R, hη s ^ 2 := by
      rw [hrest_eq]; rfl
    rw [hband_eq]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hf_L2_norm 2
    rw [mul_pow, Real.sq_sqrt (setIntegral_nonneg (measurableSet_cos2DBandSet R) fun _ _ => sq_nonneg _)] at hsq
    exact hsq
  have hbound : ∀ {r : ℝ × ℝ}, 0 ≤ r.1 → 0 ≤ r.2 → r ∉ cos2DBandSet R →
      |ϱ r| ≤ 12 * (σ.real univ + μ.real univ) *
          (min (1 : ℝ) ((2 * π * Real.exp 1 * r.1 / (m : ℝ)) ^ m) +
           min (1 : ℝ) ((2 * π * Real.exp 1 * r.2 / (m : ℝ)) ^ m)) +
        96 * R ^ 2 * Λ * (σ.real univ + μ.real univ) * (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m := by
    intro r hr1 hr2 _
    have hk_mem : MemLp (fun s => cos2DKernel r s) 2 (cos2DFullMeasure.restrict (cos2DBandSet R)) := by
      rw [hrest_eq]
      exact memLp_cos2DBandMeasure_of_continuous (continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id))
    have hrib := repair_identity_bound (m := cos2DFullMeasure) (ηp := σ) (ηm := μ)
      (k := cos2DKernel) (f := f₀) (band := cos2DBandSet R)
      (fun t ht => Set.indicator_of_notMem ht _) hf0_mem r hk_mem hΛ_sq hΛ0
    have hk_norm : Real.sqrt (∫ s in cos2DBandSet R, cos2DKernel r s ^ 2 ∂cos2DFullMeasure) ≤ 4 * R := by
      rw [hrest_eq]
      have hconst_int : IntegrableOn (fun _ : ℝ × ℝ => (16 : ℝ)) (cos2DBandSet R) volume :=
        integrableOn_const (hs := (volume_cos2DBandSet_lt_top R).ne)
      have hlhs_int : IntegrableOn (fun s => cos2DKernel r s ^ 2) (cos2DBandSet R) volume :=
        ((continuous_cos2DKernel.comp (continuous_const.prodMk continuous_id)).pow 2).continuousOn.integrableOn_compact
          (isCompact_cos2DBandSet R)
      have hsq16 : ∫ s in cos2DBandSet R, cos2DKernel r s ^ 2 ≤ (4 * R) ^ 2 := by
        calc ∫ s in cos2DBandSet R, cos2DKernel r s ^ 2
            ≤ ∫ _s in cos2DBandSet R, (16 : ℝ) :=
              setIntegral_mono_on hlhs_int hconst_int (measurableSet_cos2DBandSet R) fun s _ => by
                calc cos2DKernel r s ^ 2 = |cos2DKernel r s| ^ 2 := (sq_abs _).symm
                  _ ≤ 4 ^ 2 := by gcongr; exact abs_cos2DKernel_le r s
                  _ = 16 := by norm_num
          _ = (cos2DBandMeasure R).real univ * 16 := by
              rw [setIntegral_const, smul_eq_mul, mul_comm, volume_real_cos2DBandSet]; ring
          _ = R ^ 2 * 16 := by rw [cos2DBandMeasure_real_univ hR.le]
          _ = (4 * R) ^ 2 := by ring
      exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq16⟩
    have hhη_sqrt : Real.sqrt (∫ s in cos2DBandSet R, hη s ^ 2 ∂cos2DFullMeasure) ≤
        16 * R * (σ.real univ + μ.real univ) * (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m := by
      have heq : ∫ s in cos2DBandSet R, hη s ^ 2 ∂cos2DFullMeasure =
          ∫ s in cos2DBandSet R, hη s ^ 2 := by rw [hrest_eq]; rfl
      rw [heq]; exact hhη_L2
    have hηr := kerDual_cos2d_bound hσ hμ hmom hr1 hr2
    have h1 : Real.sqrt (∫ s in cos2DBandSet R, cos2DKernel r s ^ 2 ∂cos2DFullMeasure) *
        (Λ * Real.sqrt (∫ s in cos2DBandSet R, hη s ^ 2 ∂cos2DFullMeasure)) ≤
        (4 * R) * (Λ * (16 * R * (σ.real univ + μ.real univ) *
          (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m)) := by
      gcongr
    have h8_le_12 : 8 * (σ.real univ + μ.real univ) *
        (min (1 : ℝ) ((2 * π * Real.exp 1 * r.1 / (m : ℝ)) ^ m) +
         min (1 : ℝ) ((2 * π * Real.exp 1 * r.2 / (m : ℝ)) ^ m)) ≤
        12 * (σ.real univ + μ.real univ) *
          (min (1 : ℝ) ((2 * π * Real.exp 1 * r.1 / (m : ℝ)) ^ m) +
           min (1 : ℝ) ((2 * π * Real.exp 1 * r.2 / (m : ℝ)) ^ m)) := by
      have hmin_nn : 0 ≤ min (1 : ℝ) ((2 * π * Real.exp 1 * r.1 / (m : ℝ)) ^ m) +
          min (1 : ℝ) ((2 * π * Real.exp 1 * r.2 / (m : ℝ)) ^ m) := by positivity
      have hmeas_nn : 0 ≤ σ.real univ + μ.real univ := by positivity
      nlinarith
    have h64_le_96 : (4 * R) * (Λ * (16 * R * (σ.real univ + μ.real univ) *
        (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m)) ≤
        96 * R ^ 2 * Λ * (σ.real univ + μ.real univ) * (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m := by
      have h_eq : (4 * R) * (Λ * (16 * R * (σ.real univ + μ.real univ) *
          (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m)) =
          64 * R ^ 2 * Λ * (σ.real univ + μ.real univ) * (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m := by
        ring
      rw [h_eq]
      have h_nn : 0 ≤ R ^ 2 * Λ * (σ.real univ + μ.real univ) *
          (2 * π * Real.exp 1 * R / (m : ℝ)) ^ m := by positivity
      linarith
    calc |ϱ r|
        ≤ |hη r| + Real.sqrt (∫ s in cos2DBandSet R, cos2DKernel r s ^ 2 ∂cos2DFullMeasure) *
            (Λ * Real.sqrt (∫ s in cos2DBandSet R, hη s ^ 2 ∂cos2DFullMeasure)) := hrib
      _ ≤ _ := add_le_add (hηr.trans h8_le_12) (h1.trans h64_le_96)
  have hϱ_glob : ∀ r : ℝ × ℝ, |ϱ r| ≤ 4 * (σ.real univ + μ.real univ) + 4 * R * ‖f_L2‖ := by
    intro r
    have hη_triv : |hη r| ≤ 4 * (σ.real univ + μ.real univ) := by
      have h_single : ∀ (η : Measure (ℝ × ℝ)) [IsFiniteMeasure η],
          |∫ s, cos2DKernel r s ∂η| ≤ 4 * η.real univ := fun η _ =>
        norm_integral_le_of_norm_le_const (μ := η) (f := fun s => cos2DKernel r s) (C := 4)
          (Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using abs_cos2DKernel_le r s)
      calc |hη r| = |∫ s, cos2DKernel r s ∂σ - ∫ s, cos2DKernel r s ∂μ| := rfl
        _ ≤ |∫ s, cos2DKernel r s ∂σ| + |∫ s, cos2DKernel r s ∂μ| := abs_sub _ _
        _ ≤ 4 * σ.real univ + 4 * μ.real univ := add_le_add (h_single σ) (h_single μ)
        _ = 4 * (σ.real univ + μ.real univ) := by ring
    have hU_triv : |kerTransform cos2DFullMeasure cos2DKernel f₀ r| ≤ 4 * R * ‖f_L2‖ := by
      rw [hf_raw_eq r]
      have hsq := rawCos2DOp_sq_le hR.le f_L2 r
      rw [show 16 * R ^ 2 * ‖f_L2‖ ^ 2 = (4 * R * ‖f_L2‖) ^ 2 by ring] at hsq
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa [sq_abs] using hsq)
    calc |ϱ r| = |hη r - kerTransform cos2DFullMeasure cos2DKernel f₀ r| := rfl
      _ ≤ |hη r| + |kerTransform cos2DFullMeasure cos2DKernel f₀ r| := abs_sub _ _
      _ ≤ 4 * (σ.real univ + μ.real univ) + 4 * R * ‖f_L2‖ := add_le_add hη_triv hU_triv
  refine ⟨ϱ, hϱ_cont, fun {βL βR} hβL hβR => ?_, hbound⟩
  let C_glob : ℝ := 4 * (σ.real univ + μ.real univ) + 4 * R * ‖f_L2‖
  have hC_glob0 : 0 ≤ C_glob := by positivity
  have hint_e1 : Integrable (fun r : ℝ × ℝ => Real.exp (-π * (βL * r.1 ^ 2 + βR * r.2 ^ 2)) * |ϱ r|)
      cos2DFullMeasure := by
    unfold cos2DFullMeasure
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine ((integrable_gaussian_2d hβL hβR).const_mul C_glob).mono' ?_ ?_
    · exact ((Real.continuous_exp.comp (by fun_prop)).mul hϱ_cont.abs).aestronglyMeasurable
    · refine Eventually.of_forall fun r => ?_
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)), mul_comm C_glob]
      exact mul_le_mul_of_nonneg_left (hϱ_glob r) (Real.exp_pos _).le
  have hint_e2 : Integrable (fun r : ℝ × ℝ => Real.exp (-π * (r.1 ^ 2 / βL + r.2 ^ 2 / βR)) * |ϱ r|)
      cos2DFullMeasure := by
    have hsplit : (fun r : ℝ × ℝ => Real.exp (-π * (r.1 ^ 2 / βL + r.2 ^ 2 / βR)) * |ϱ r|) =
        fun r => Real.exp (-π * (βL⁻¹ * r.1 ^ 2 + βR⁻¹ * r.2 ^ 2)) * |ϱ r| := by
      ext r; congr 2; field_simp
    rw [hsplit]
    unfold cos2DFullMeasure
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine ((integrable_gaussian_2d (inv_pos.mpr hβL) (inv_pos.mpr hβR)).const_mul C_glob).mono' ?_ ?_
    · exact ((Real.continuous_exp.comp (by fun_prop)).mul hϱ_cont.abs).aestronglyMeasurable
    · refine Eventually.of_forall fun r => ?_
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)), mul_comm C_glob]
      exact mul_le_mul_of_nonneg_left (hϱ_glob r) (Real.exp_pos _).le
  have hr1 : IntegrableOn (fun r : ℝ × ℝ => Real.exp (-π * (βL * r.1 ^ 2 + βR * r.2 ^ 2)) * |ϱ r|)
      (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) \ cos2DBandSet R) volume := by
    rw [IntegrableOn, Set.sdiff_eq, Set.inter_comm,
      ← Measure.restrict_restrict (measurableSet_cos2DBandSet R).compl]
    exact hint_e1.restrict
  have hr2 : IntegrableOn (fun r : ℝ × ℝ => Real.exp (-π * (r.1 ^ 2 / βL + r.2 ^ 2 / βR)) * |ϱ r|)
      (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) \ cos2DBandSet R) volume := by
    rw [IntegrableOn, Set.sdiff_eq, Set.inter_comm,
      ← Measure.restrict_restrict (measurableSet_cos2DBandSet R).compl]
    exact hint_e2.restrict
  refine ⟨hr1, hr2, ?_⟩
  · let g : ℝ × ℝ → ℝ := fun r => spinThermalX βL βR (r.1 ^ 2 / 2) (r.2 ^ 2 / 2)
    have hg_cont : Continuous g := by
      unfold g spinThermalX; fun_prop
    have hg_abs_int : Integrable (fun r => |g r|) cos2DFullMeasure := by
      unfold cos2DFullMeasure
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      have hi1 := integrable_gaussian_2d hβL hβR
      have hi2 := (integrable_gaussian_2d (inv_pos.mpr hβL) (inv_pos.mpr hβR)).const_mul
        ((βL * βR) ^ (-(1 / 2 : ℝ)))
      refine (hi1.add hi2).mono' hg_cont.abs.aestronglyMeasurable ?_
      refine Eventually.of_forall fun r => ?_
      rw [Real.norm_of_nonneg (abs_nonneg _)]
      dsimp only [g, spinThermalX]
      have h1 : -2 * π * (βL * (r.1 ^ 2 / 2) + βR * (r.2 ^ 2 / 2)) =
          -π * (βL * r.1 ^ 2 + βR * r.2 ^ 2) := by ring
      have h2 : -2 * π * (r.1 ^ 2 / 2 / βL + r.2 ^ 2 / 2 / βR) =
          -π * (βL⁻¹ * r.1 ^ 2 + βR⁻¹ * r.2 ^ 2) := by field_simp
      rw [h1, h2]
      calc |Real.exp (-π * (βL * r.1 ^ 2 + βR * r.2 ^ 2)) -
              (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-π * (βL⁻¹ * r.1 ^ 2 + βR⁻¹ * r.2 ^ 2))|
          ≤ |Real.exp (-π * (βL * r.1 ^ 2 + βR * r.2 ^ 2))| +
              |(βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-π * (βL⁻¹ * r.1 ^ 2 + βR⁻¹ * r.2 ^ 2))| :=
            abs_sub _ _
        _ = Real.exp (-π * (βL * r.1 ^ 2 + βR * r.2 ^ 2)) +
              (βL * βR) ^ (-(1 / 2 : ℝ)) * Real.exp (-π * (βL⁻¹ * r.1 ^ 2 + βR⁻¹ * r.2 ^ 2)) := by
            rw [abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)]
    have hf0_abs_int : Integrable (fun s => |f₀ s|) cos2DFullMeasure := by
      have heq : (fun s => |f₀ s|) =
          (cos2DBandSet R).indicator (fun s => |(f_L2 : ℝ × ℝ → ℝ) s|) := by
        ext s; by_cases hs : s ∈ cos2DBandSet R <;> simp [f₀, hs]
      rw [heq, integrable_indicator_iff (measurableSet_cos2DBandSet R)]
      show Integrable (fun s => |(f_L2 : ℝ × ℝ → ℝ) s|) (cos2DFullMeasure.restrict (cos2DBandSet R))
      rw [hrest_eq]
      exact ((Lp.memLp f_L2).integrable one_le_two).norm
    have hF1 : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => g p.1 * cos2DKernel p.1 p.2)
        (cos2DFullMeasure.prod σ) := by
      have hdom := (hg_abs_int.const_mul 4).mul_prod (integrable_const (1 : ℝ) : Integrable _ σ)
      have hm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => g p.1 * cos2DKernel p.1 p.2) :=
        (hg_cont.measurable.comp measurable_fst).mul continuous_cos2DKernel.measurable
      refine hdom.mono' hm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul, mul_one, mul_comm 4]
      exact mul_le_mul_of_nonneg_left (abs_cos2DKernel_le p.1 p.2) (abs_nonneg _)
    have hF2 : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => g p.1 * cos2DKernel p.1 p.2)
        (cos2DFullMeasure.prod μ) := by
      have hdom := (hg_abs_int.const_mul 4).mul_prod (integrable_const (1 : ℝ) : Integrable _ μ)
      have hm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => g p.1 * cos2DKernel p.1 p.2) :=
        (hg_cont.measurable.comp measurable_fst).mul continuous_cos2DKernel.measurable
      refine hdom.mono' hm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul, mul_one, mul_comm 4]
      exact mul_le_mul_of_nonneg_left (abs_cos2DKernel_le p.1 p.2) (abs_nonneg _)
    have hF3 : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => g p.1 * (cos2DKernel p.1 p.2 * f₀ p.2))
        (cos2DFullMeasure.prod cos2DFullMeasure) := by
      have hdom := (hg_abs_int.const_mul 4).mul_prod hf0_abs_int
      have hm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => g p.1 * (cos2DKernel p.1 p.2 * f₀ p.2)) :=
        (hg_cont.measurable.comp measurable_fst).mul
          (continuous_cos2DKernel.measurable.mul (hf0_meas.comp measurable_snd))
      refine hdom.mono' hm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |g p.1| * (|cos2DKernel p.1 p.2| * |f₀ p.2|)
          ≤ |g p.1| * (4 * |f₀ p.2|) := by gcongr; exact abs_cos2DKernel_le p.1 p.2
        _ = 4 * |g p.1| * |f₀ p.2| := by ring
    have hcross := repair_identity_cross cos2DKernel_symm (kerTransform_spinThermalX hβL hβR) hF1 hF2 hF3
    have hsol : ∀ᵐ r ∂cos2DFullMeasure, r ∈ cos2DBandSet R →
        f₀ r + kerTransform cos2DFullMeasure cos2DKernel f₀ r = hη r := by
      have h_ae_band : (f_L2 : ℝ × ℝ → ℝ) + (cos2DBandOp hR.le f_L2 : ℝ × ℝ → ℝ) =ᵐ[cos2DBandMeasure R] hη := by
        have hsum : f_L2 + cos2DBandOp hR.le f_L2 = hhη_mem.toLp hη := by
          have h1 : (1 + cos2DBandOp hR.le) f_L2 = hhη_mem.toLp hη :=
            congrArg (fun L => L (hhη_mem.toLp hη)) hA_right
          simpa [add_apply] using h1
        filter_upwards [Lp.coeFn_add f_L2 (cos2DBandOp hR.le f_L2), hhη_mem.coeFn_toLp] with r hr1 hr2
        rw [← hr1, hsum, hr2]
      have h_ae_band2 : ∀ᵐ r ∂cos2DBandMeasure R,
          f₀ r + kerTransform cos2DFullMeasure cos2DKernel f₀ r = hη r := by
        filter_upwards [h_ae_band, cos2DBandOp_apply_ae hR.le f_L2,
          ae_restrict_mem (measurableSet_cos2DBandSet R)] with r hr1 hr2 hrm
        have hf0r : f₀ r = (f_L2 : ℝ × ℝ → ℝ) r := Set.indicator_of_mem hrm _
        rw [hf0r, hf_raw_eq r]
        unfold rawCos2DOp
        rw [← hr2]
        exact hr1
      rw [← hrest_eq] at h_ae_band2
      exact (ae_restrict_iff' (measurableSet_cos2DBandSet R)).mp h_ae_band2
    have hi_dual : Integrable (fun r => g r * ϱ r) cos2DFullMeasure := by
      refine (hg_abs_int.const_mul C_glob).mono' (hg_cont.mul hϱ_cont).aestronglyMeasurable ?_
      refine Eventually.of_forall fun r => ?_
      rw [Real.norm_eq_abs, abs_mul, mul_comm C_glob]
      exact mul_le_mul_of_nonneg_left (hϱ_glob r) (abs_nonneg _)
    have hi_f : Integrable (fun s => g s * f₀ s) cos2DFullMeasure := by
      obtain ⟨r₀, _, hr₀⟩ := (isCompact_cos2DBandSet R).exists_isMaxOn
        ⟨(0, 0), ⟨le_rfl, hR.le⟩, ⟨le_rfl, hR.le⟩⟩ hg_cont.abs.continuousOn
      refine (hf0_abs_int.const_mul |g r₀|).mono' (hg_cont.measurable.mul hf0_meas).aestronglyMeasurable ?_
      refine Eventually.of_forall fun s => ?_
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hsm : s ∈ cos2DBandSet R
      · exact mul_le_mul_of_nonneg_right (hr₀ hsm) (abs_nonneg _)
      · have hs0 : f₀ s = 0 := Set.indicator_of_notMem hsm _
        simp [hs0]
    have hsplit_dual := integral_add_compl (measurableSet_cos2DBandSet R) hi_dual
    have hsplit_f := integral_add_compl (measurableSet_cos2DBandSet R) hi_f
    have hband_match :
        ∫ r in cos2DBandSet R, g r * ϱ r ∂cos2DFullMeasure =
          ∫ s in cos2DBandSet R, g s * f₀ s ∂cos2DFullMeasure := by
      refine setIntegral_congr_ae (measurableSet_cos2DBandSet R) ?_
      filter_upwards [hsol] with r hrm hr_mem
      have hr_eq := hrm hr_mem
      dsimp only [ϱ]
      congr 1; linarith
    have hcompl_f : ∫ s in (cos2DBandSet R)ᶜ, g s * f₀ s ∂cos2DFullMeasure = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
      dsimp [f₀]; rw [Set.indicator_of_notMem hs, mul_zero]
    have hcompl_tail :
        ∫ r in (cos2DBandSet R)ᶜ, g r * ϱ r ∂cos2DFullMeasure =
          ∫ r in (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) \ cos2DBandSet R), g r * ϱ r := by
      unfold cos2DFullMeasure
      rw [Measure.restrict_restrict (measurableSet_cos2DBandSet R).compl, Set.sdiff_eq, Set.inter_comm]
    have hcross' :
        ∫ s, g s ∂σ - ∫ s, g s ∂μ - ∫ s, g s * f₀ s ∂cos2DFullMeasure +
          ∫ r, g r * ϱ r ∂cos2DFullMeasure = 0 := by
      simpa [ϱ, hη, repairPairing] using hcross
    have h0 :
        ∫ s, g s ∂σ - ∫ s, g s ∂μ +
          ∫ r in (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) \ cos2DBandSet R), g r * ϱ r =
          ∫ s, g s ∂σ - ∫ s, g s ∂μ - ∫ s, g s * f₀ s ∂cos2DFullMeasure +
            ∫ r, g r * ϱ r ∂cos2DFullMeasure := by
      have hD := hsplit_dual.symm
      have hF : ∫ s, g s * f₀ s ∂cos2DFullMeasure =
          ∫ s in cos2DBandSet R, g s * f₀ s ∂cos2DFullMeasure := by
        rw [← hsplit_f, hcompl_f, add_zero]
      rw [← hcompl_tail, hD, hF, hband_match]; ring
    rw [h0]; exact hcross'

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.cos2d_repair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cos2d_repair

end FormalResearch.ModularBootstrap.Spin
