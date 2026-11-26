module

public import FormalResearch.ModularBootstrap.FiveTerm.QFactor

/-!
# Two-sided bounds for `Ŝ(u(z))` near `z = ±i` (FIVE-0 slice 2d)

For `Im u < 0`, `‖u‖ ≥ 2`: `‖S(u)‖ ≥ (1/√2) arsinh(√ρ)/√ρ` (the integrand lies in the first quadrant) and
`‖S(-u)‖ ≤ (π/2 + arsinh √(ρ-1))/√ρ` (`|1 - u t²| ≥ |1 - ρ t²|`), `ρ = ‖u‖`; hence `‖Ŝ(u)‖ ≤ Cq`.  By the
involution `Ŝ(-u) = Ŝ(u)⁻¹` and conjugation this gives `Cq⁻¹ ≤ ‖Ŝ(u(z))‖ ≤ Cq` for `z ∈ Ω` near `±i`
(`qHat_bounds_near_I`).  All results are proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- For `Im u < 0` the integrand of `S(u)` lies in the closed first quadrant. -/
lemma sIntegrand_quadrant {u : ℂ} (hu : u.im < 0) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ((1 + u * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))).re ∧ 0 ≤ ((1 + u * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))).im := by
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  set z : ℂ := 1 + u * (t : ℂ) ^ 2 with hz
  have him : z.im < 0 := by
    rw [hz]; simp [Complex.mul_im, pow_two]
    nlinarith [mul_pos hpos hpos]
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at him; simp at him
  have harg1 : -π < z.arg := Complex.neg_pi_lt_arg z
  have harg2 : z.arg < 0 := Complex.arg_neg_iff.mpr him
  rw [Complex.cpow_def_of_ne_zero hz0, Complex.exp_re, Complex.exp_im]
  have hlog : (Complex.log z * (-(1 / 2 : ℂ))).im = -(z.arg) / 2 := by
    simp [Complex.mul_im, Complex.log_im, Complex.log_re]; ring
  rw [hlog]
  constructor
  · apply mul_nonneg (Real.exp_pos _).le
    apply (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).le
  · apply mul_nonneg (Real.exp_pos _).le
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith

lemma re_add_im_le_sqrt_two_mul_norm (w : ℂ) : w.re + w.im ≤ √2 * ‖w‖ := by
  have h1 : (w.re + w.im) ^ 2 ≤ 2 * ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (w.re - w.im)]
  have h2 : 0 ≤ √2 * ‖w‖ := by positivity
  have h3 : (√2 * ‖w‖) ^ 2 = 2 * ‖w‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  exact abs_le_of_sq_le_sq' (by rw [h3]; exact h1) h2 |>.2

/-- Lower bound for `‖S(u)‖`, `Im u < 0`. -/
lemma norm_sInt_lower {u : ℂ} (hu : u.im < 0) (hρ : 0 < ‖u‖) :
    (1 / √2) * (Real.arsinh (√‖u‖) / √‖u‖) ≤ ‖sInt u‖ := by
  set ρ : ℝ := ‖u‖ with hρdef
  have hsd : u ∈ sDom := fun h => by have := h.1; linarith
  set g : ℝ → ℂ := fun t => (1 + u * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) with hg
  have hint : IntegrableOn g (Icc (0 : ℝ) 1) := (continuousOn_sIntegrand hsd).integrableOn_Icc
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, (1 + ρ * t ^ 2) ^ (-(1 / 2 : ℝ)) ≤ (g t).re + (g t).im := by
    intro t ht
    obtain ⟨h1, h2⟩ := sIntegrand_quadrant hu ht.1
    have hne : 1 + u * (t : ℂ) ^ 2 ≠ 0 := Complex.slitPlane_ne_zero (one_add_mul_mem_slit hsd ht)
    have e1 : ‖g t‖ = ‖1 + u * (t : ℂ) ^ 2‖ ^ (-(1 / 2 : ℝ)) := by
      have := Complex.norm_cpow_of_ne_zero hne (-(1 / 2 : ℂ))
      simpa [hg] using this
    have hle : ‖1 + u * (t : ℂ) ^ 2‖ ≤ 1 + ρ * t ^ 2 := by
      calc ‖1 + u * (t : ℂ) ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖u * (t : ℂ) ^ 2‖ := norm_add_le _ _
        _ = 1 + ρ * t ^ 2 := by
          rw [norm_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hpos : 0 < ‖1 + u * (t : ℂ) ^ 2‖ := norm_pos_iff.mpr hne
    have e2 : (1 + ρ * t ^ 2) ^ (-(1 / 2 : ℝ)) ≤ ‖g t‖ := by
      rw [e1]; exact Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
    have e3 : ‖g t‖ ≤ (g t).re + (g t).im := by
      have : ‖g t‖ ^ 2 ≤ ((g t).re + (g t).im) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        nlinarith [mul_nonneg h1 h2]
      exact abs_le_of_sq_le_sq' this (by linarith) |>.2
    exact e2.trans e3
  have hsum : (∫ t in Icc (0 : ℝ) 1, (1 + ρ * t ^ 2) ^ (-(1 / 2 : ℝ))) ≤
      (sInt u).re + (sInt u).im := by
    have hre : (sInt u).re = ∫ t in Icc (0 : ℝ) 1, (g t).re := by
      unfold sInt; rw [← hg]
      rw [← RCLike.re_to_complex, ← integral_re hint]; rfl
    have him : (sInt u).im = ∫ t in Icc (0 : ℝ) 1, (g t).im := by
      unfold sInt; rw [← hg]
      rw [← RCLike.im_to_complex, ← integral_im hint]; rfl
    have hre' : IntegrableOn (fun t => (g t).re) (Icc (0 : ℝ) 1) := hint.re
    have him' : IntegrableOn (fun t => (g t).im) (Icc (0 : ℝ) 1) := hint.im
    rw [hre, him, ← integral_add hre' him']
    refine setIntegral_mono_on ?_ (hre'.add him') measurableSet_Icc hnorm
    have : ContinuousOn (fun t : ℝ => (1 + ρ * t ^ 2) ^ (-(1 / 2 : ℝ))) (Icc (0 : ℝ) 1) := by
      refine ContinuousOn.rpow_const (by fun_prop) (fun t _ => Or.inl (by positivity))
    exact this.integrableOn_Icc
  have hval : (∫ t in Icc (0 : ℝ) 1, (1 + ρ * t ^ 2) ^ (-(1 / 2 : ℝ))) =
      Real.arsinh (√ρ) / √ρ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    have : ∀ t ∈ uIcc (0 : ℝ) 1, (1 + ρ * t ^ 2) ^ (-(1 / 2 : ℝ)) = 1 / √(1 + ρ * t ^ 2) := by
      intro t _
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    rw [intervalIntegral.integral_congr this, integral_inv_sqrt_one_add hρ]
  have h4 := re_add_im_le_sqrt_two_mul_norm (sInt u)
  rw [hval] at hsum
  have h5 : Real.arsinh (√ρ) / √ρ ≤ √2 * ‖sInt u‖ := hsum.trans h4
  have h6 : 0 < √2 := by positivity
  rw [one_div, inv_mul_le_iff₀ h6]
  linarith

/-- Upper bound for `‖S(-u)‖`. -/
lemma norm_sInt_neg_upper {u : ℂ} (hρ : 2 ≤ ‖u‖) :
    ‖sInt (-u)‖ ≤ (π / 2 + Real.arsinh (√(‖u‖ - 1))) / √‖u‖ := by
  set ρ : ℝ := ‖u‖ with hρdef
  have hρ1 : 1 < ρ := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hsρ : 0 < √ρ := Real.sqrt_pos.mpr hρ0
  set t₀ : ℝ := 1 / √ρ with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  have hsq : √ρ * √ρ = ρ := Real.mul_self_sqrt hρ0.le
  have hle : t₀ ≤ 1 := by
    rw [ht₀, div_le_one hsρ]; rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hρ1.le
  have hct : ρ * t₀ ^ 2 = 1 := by rw [ht₀]; field_simp; nlinarith [hsq]
  set h : ℝ → ℝ := fun t => 1 / √|1 - ρ * t ^ 2| with hh
  have h1 := (integral_inv_sqrt_one_sub (c := ρ) hρ0 (r := t₀) ht₀pos.le
    (by rw [ht₀]; field_simp; exact le_refl _))
  have h2 := integral_inv_sqrt_sub_one hρ1
  have e1 : ∀ t ∈ uIcc (0 : ℝ) t₀, h t = 1 / √(1 - ρ * t ^ 2) := by
    intro t ht
    rw [uIcc_of_le ht₀pos.le] at ht
    have : ρ * t ^ 2 ≤ ρ * t₀ ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 2) hρ0.le
    simp only [hh]
    rw [abs_of_nonneg (by linarith)]
  have e2 : ∀ t ∈ uIcc t₀ 1, h t = 1 / √(ρ * t ^ 2 - 1) := by
    intro t ht
    rw [uIcc_of_le hle] at ht
    have : ρ * t₀ ^ 2 ≤ ρ * t ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht₀pos.le ht.1 2) hρ0.le
    simp only [hh]
    rw [abs_of_nonpos (by linarith), neg_sub]
  have hI1 : IntervalIntegrable h volume 0 t₀ :=
    h1.2.congr (fun t ht => (e1 t (uIoc_subset_uIcc ht)).symm)
  have hI2 : IntervalIntegrable h volume t₀ 1 := by
    have h2' : IntervalIntegrable (fun t : ℝ => 1 / √(ρ * t ^ 2 - 1)) volume (1 / √ρ) 1 := h2.2
    exact h2'.congr (fun t ht => (e2 t (uIoc_subset_uIcc ht)).symm)
  have hIall : IntervalIntegrable h volume 0 1 := hI1.trans hI2
  have hval : (∫ t in (0 : ℝ)..1, h t) = (π / 2 + Real.arsinh (√(ρ - 1))) / √ρ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2,
      intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2, h1.1, h2.1]
    have hsct : √ρ * t₀ = 1 := by rw [ht₀]; field_simp
    rw [hsct, Real.arcsin_one]
    ring
  -- the pointwise bound
  have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ‖(1 + (-u) * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ h t := by
    have hne : ∀ᵐ t : ℝ ∂(volume.restrict (Icc (0 : ℝ) 1)), t ≠ t₀ :=
      ae_restrict_of_ae ((Set.countable_singleton t₀).ae_notMem volume)
    filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with t htt ht
    have hρt : |1 - ρ * t ^ 2| ≠ 0 := by
      intro h0
      have : 1 - ρ * t ^ 2 = 0 := abs_eq_zero.mp h0
      have h3 : t ^ 2 = t₀ ^ 2 := by
        have : ρ * t ^ 2 = ρ * t₀ ^ 2 := by rw [hct]; linarith
        exact mul_left_cancel₀ hρ0.ne' this
      exact htt ((pow_left_inj₀ ht.1 ht₀pos.le two_ne_zero).mp h3)
    have hρpos : 0 < |1 - ρ * t ^ 2| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hρt)
    have hlow : |1 - ρ * t ^ 2| ≤ ‖1 + (-u) * (t : ℂ) ^ 2‖ := by
      have h0 := abs_norm_sub_norm_le (1 : ℂ) (-((-u) * (t : ℂ) ^ 2))
      rw [sub_neg_eq_add, norm_neg, norm_one] at h0
      have e : ‖(-u) * (t : ℂ) ^ 2‖ = ρ * t ^ 2 := by
        rw [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [e] at h0
      exact h0
    have hz : 1 + (-u) * (t : ℂ) ^ 2 ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hlow; linarith
    have e1' : ‖(1 + (-u) * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ = ‖1 + (-u) * (t : ℂ) ^ 2‖ ^ (-(1 / 2 : ℝ)) := by
      have := Complex.norm_cpow_of_ne_zero hz (-(1 / 2 : ℂ))
      simpa using this
    rw [e1']
    calc ‖1 + (-u) * (t : ℂ) ^ 2‖ ^ (-(1 / 2 : ℝ)) ≤ |1 - ρ * t ^ 2| ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hρpos hlow (by norm_num)
      _ = h t := by
          simp only [hh]
          rw [Real.rpow_neg (abs_nonneg _), ← Real.sqrt_eq_rpow, one_div]
  have hhint : IntegrableOn h (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hIall
  calc ‖sInt (-u)‖ = ‖∫ t in Icc (0 : ℝ) 1, (1 + (-u) * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ := rfl
    _ ≤ ∫ t in Icc (0 : ℝ) 1, h t := norm_integral_le_of_norm_le hhint hbound
    _ = (π / 2 + Real.arsinh (√(ρ - 1))) / √ρ := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, hval]

/-- The absolute bound `Cq` for `‖Ŝ‖` on `|u| ≥ 2`, `Im u < 0`. -/
noncomputable def Cq : ℝ := √2 * (π / (2 * Real.arsinh 1) + 1)

lemma Cq_pos : 0 < Cq := by
  unfold Cq
  have : 0 < Real.arsinh 1 := Real.arsinh_pos_iff.mpr one_pos
  positivity

lemma norm_sHat_le {u : ℂ} (hu : u.im < 0) (hρ : 2 ≤ ‖u‖) : ‖sHat u‖ ≤ Cq := by
  set ρ : ℝ := ‖u‖ with hρdef
  have hρ0 : 0 < ρ := by linarith
  have hsρ : 0 < √ρ := Real.sqrt_pos.mpr hρ0
  have hB : Real.arsinh 1 ≤ Real.arsinh (√ρ) := by
    apply Real.arsinh_le_arsinh.mpr
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hB0 : 0 < Real.arsinh 1 := Real.arsinh_pos_iff.mpr one_pos
  have hBpos : 0 < Real.arsinh (√ρ) := lt_of_lt_of_le hB0 hB
  have hA : Real.arsinh (√(ρ - 1)) ≤ Real.arsinh (√ρ) := by
    apply Real.arsinh_le_arsinh.mpr
    exact Real.sqrt_le_sqrt (by linarith)
  have hlow := norm_sInt_lower hu hρ0
  have hup := norm_sInt_neg_upper hρ
  have hDpos : 0 < (1 / √2) * (Real.arsinh (√ρ) / √ρ) := by positivity
  have hD : 0 < ‖sInt u‖ := lt_of_lt_of_le hDpos hlow
  have hN : 0 ≤ ‖sInt (-u)‖ := norm_nonneg _
  unfold sHat
  rw [norm_div]
  calc ‖sInt (-u)‖ / ‖sInt u‖ ≤ ((π / 2 + Real.arsinh (√(ρ - 1))) / √ρ) /
        ((1 / √2) * (Real.arsinh (√ρ) / √ρ)) :=
        div_le_div₀ (div_nonneg (add_nonneg (by positivity)
          (Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg _))) hsρ.le) hup hDpos hlow
    _ = √2 * ((π / 2 + Real.arsinh (√(ρ - 1))) / Real.arsinh (√ρ)) := by
        field_simp
    _ ≤ Cq := by
        unfold Cq
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [add_div]
        have h1 : (π / 2) / Real.arsinh (√ρ) ≤ π / (2 * Real.arsinh 1) := by
          rw [show π / (2 * Real.arsinh 1) = (π / 2) / Real.arsinh 1 by ring]
          exact div_le_div_of_nonneg_left (by positivity) hB0 hB
        have h2 : Real.arsinh (√(ρ - 1)) / Real.arsinh (√ρ) ≤ 1 := by
          rw [div_le_one hBpos]; exact hA
        linarith

lemma norm_one_add_sq_eq (z : ℂ) : ‖1 + z ^ 2‖ = ‖z - Complex.I‖ * ‖z + Complex.I‖ := by
  rw [← norm_mul]
  congr 1
  have : (z - Complex.I) * (z + Complex.I) = z ^ 2 + 1 := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

lemma qHat_upper_near_I {z : ℂ} (hz : z ∈ halfDisc) (hr : ‖z - Complex.I‖ < 1 / 8) :
    ‖qHat z‖ ≤ Cq := by
  have him : 7 / 8 < z.im := by
    have : |(z - Complex.I).im| ≤ ‖z - Complex.I‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im, Complex.I_im] at this
    have := (abs_le.mp this).1
    linarith
  have hzn : 7 / 8 ≤ ‖z‖ := by
    have : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm _
    rw [abs_of_pos (by linarith)] at this; linarith
  have hw : ‖1 + z ^ 2‖ < 1 / 2 := by
    rw [norm_one_add_sq_eq]
    have h2 : ‖z + Complex.I‖ ≤ 2 + 1 / 8 := by
      have : z + Complex.I = (z - Complex.I) + 2 * Complex.I := by ring
      rw [this]
      calc ‖(z - Complex.I) + 2 * Complex.I‖ ≤ ‖z - Complex.I‖ + ‖2 * Complex.I‖ := norm_add_le _ _
        _ ≤ 1 / 8 + 2 := by
          have : ‖(2 : ℂ) * Complex.I‖ = 2 := by simp
          rw [this]; linarith
        _ = 2 + 1 / 8 := by ring
    have h1 : 0 ≤ ‖z - Complex.I‖ := norm_nonneg _
    nlinarith [norm_nonneg (z + Complex.I)]
  have hwpos : 0 < ‖1 + z ^ 2‖ := norm_pos_iff.mpr (one_add_sq_ne_zero_of_halfDisc hz)
  have hu : 2 ≤ ‖uC z‖ := by
    have e : uC z = 1 - 8 * z ^ 2 / (1 + z ^ 2) ^ 2 := by
      have hne := one_add_sq_ne_zero_of_halfDisc hz
      have := one_sub_uC hne
      linear_combination -this
    have h8 : ‖8 * z ^ 2 / (1 + z ^ 2) ^ 2‖ = 8 * ‖z‖ ^ 2 / ‖1 + z ^ 2‖ ^ 2 := by
      rw [norm_div, norm_mul, norm_pow, norm_pow]; simp
    have h9 : 8 * ‖z‖ ^ 2 / ‖1 + z ^ 2‖ ^ 2 ≥ 8 * (7 / 8) ^ 2 / (1 / 2) ^ 2 := by
      have hz2 : (7 / 8 : ℝ) ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith
      have hw2 : ‖1 + z ^ 2‖ ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith
      calc 8 * (7 / 8 : ℝ) ^ 2 / (1 / 2) ^ 2 ≤ 8 * ‖z‖ ^ 2 / (1 / 2) ^ 2 := by gcongr
        _ ≤ 8 * ‖z‖ ^ 2 / ‖1 + z ^ 2‖ ^ 2 := by
          exact div_le_div_of_nonneg_left (by positivity) (pow_pos hwpos 2) hw2
    have h10 := norm_sub_norm_le (8 * z ^ 2 / (1 + z ^ 2) ^ 2) 1
    have h11 : ‖uC z‖ ≥ ‖8 * z ^ 2 / (1 + z ^ 2) ^ 2‖ - 1 := by
      rw [e]
      have := norm_sub_norm_le (8 * z ^ 2 / (1 + z ^ 2) ^ 2) (1 : ℂ)
      rw [norm_sub_rev] at this
      simpa using this
    rw [h8] at h11
    norm_num at h9
    linarith
  exact norm_sHat_le (im_uC_neg hz (by linarith)) hu

lemma qHat_bounds_near_I {z : ℂ} (hz : z ∈ halfDisc)
    (hr : ‖z - Complex.I‖ < 1 / 12 ∨ ‖z + Complex.I‖ < 1 / 12) :
    1 / Cq ≤ ‖qHat z‖ ∧ ‖qHat z‖ ≤ Cq := by
  have hsq : ‖(1 - Complex.I : ℂ)‖ = √2 := by
    rw [Complex.norm_def, Complex.normSq_apply]; norm_num
  have hsq' : ‖(1 + Complex.I : ℂ)‖ = √2 := by
    rw [Complex.norm_def, Complex.normSq_apply]; norm_num
  have h1z : 1 ≤ ‖1 + z‖ := by
    have : (1 + z).re ≤ ‖1 + z‖ := Complex.re_le_norm _
    simp at this; linarith [hz.2]
  have hz1 : 1 + z ≠ 0 := by intro h; rw [h] at h1z; norm_num at h1z
  have hσ : sigmaHD z ∈ halfDisc := sigmaHD_mem hz
  have hσeq : sigmaHD z = (1 - z) / (1 + z) := rfl
  have hupper : ∀ w ∈ halfDisc, (‖w - Complex.I‖ < 1 / 8 ∨ ‖w + Complex.I‖ < 1 / 8) → ‖qHat w‖ ≤ Cq := by
    intro w hw hw8
    rcases hw8 with h | h
    · exact qHat_upper_near_I hw h
    · have hc := halfDisc_conj hw
      have : ‖starRingEnd ℂ w - Complex.I‖ < 1 / 8 := by
        have e : starRingEnd ℂ w - Complex.I = starRingEnd ℂ (w + Complex.I) := by simp [sub_eq_add_neg]
        rw [e, Complex.norm_conj]; exact h
      have := qHat_upper_near_I hc this
      rwa [qHat_conj hw, Complex.norm_conj] at this
  have hupz : ‖qHat z‖ ≤ Cq := by
    refine hupper z hz ?_
    rcases hr with h | h
    · left; linarith
    · right; linarith
  refine ⟨?_, hupz⟩
  -- lower bound through `σ`
  have hrel : qHat (sigmaHD z) = (qHat z)⁻¹ := qHat_sigma hz
  have hσnear : ‖sigmaHD z - Complex.I‖ < 1 / 8 ∨ ‖sigmaHD z + Complex.I‖ < 1 / 8 := by
    rcases hr with h | h
    · right
      have e : sigmaHD z + Complex.I = (1 - Complex.I) * (Complex.I - z) / (1 + z) := by
        rw [hσeq]; field_simp; ring_nf; rw [Complex.I_sq]; ring
      rw [e, norm_div, norm_mul, hsq, norm_sub_rev]
      have : √2 * ‖z - Complex.I‖ / ‖1 + z‖ ≤ √2 * ‖z - Complex.I‖ := by
        apply div_le_self (by positivity) h1z
      have hs2 : √2 < 3 / 2 := by
        rw [show (3 / 2 : ℝ) = √((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h0 : 0 ≤ ‖z - Complex.I‖ := norm_nonneg _
      nlinarith
    · left
      have e : sigmaHD z - Complex.I = -((1 + Complex.I) * (z + Complex.I)) / (1 + z) := by
        rw [hσeq]; field_simp; ring_nf; rw [Complex.I_sq]; ring
      rw [e, norm_div, norm_neg, norm_mul, hsq']
      have : √2 * ‖z + Complex.I‖ / ‖1 + z‖ ≤ √2 * ‖z + Complex.I‖ := by
        apply div_le_self (by positivity) h1z
      have hs2 : √2 < 3 / 2 := by
        rw [show (3 / 2 : ℝ) = √((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h0 : 0 ≤ ‖z + Complex.I‖ := norm_nonneg _
      nlinarith
  have hupσ := hupper _ hσ hσnear
  rw [hrel, norm_inv] at hupσ
  have hq0 : 0 < ‖qHat z‖ := norm_pos_iff.mpr (qHat_ne_zero hz)
  rw [one_div]
  exact (inv_le_comm₀ hq0 Cq_pos).mp hupσ

end FormalResearch.ModularBootstrap.FiveTerm
