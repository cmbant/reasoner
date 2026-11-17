module

public import FormalResearch.Special.AiryPwsContour

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma cpow_sq_three_halves {s : ℂ} (h1 : 0 ≤ s.re) (h2 : 0 ≤ s.im) :
    (s ^ 2) ^ (3 / 2 : ℂ) = s ^ 3 := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have harg1 : 0 ≤ Complex.arg s := Complex.arg_nonneg_iff.mpr h2
  have harg2 : Complex.arg s ≤ π / 2 := Complex.arg_le_pi_div_two_iff.mpr (Or.inl h1)
  have hlog : Complex.log (s * s) = Complex.log s + Complex.log s :=
    (Complex.log_mul_eq_add_log_iff hs hs).mpr ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [sq, Complex.cpow_def_of_ne_zero (mul_ne_zero hs hs), hlog]
  have : (Complex.log s + Complex.log s) * (3 / 2) = ((3 : ℕ) : ℂ) * Complex.log s := by push_cast; ring
  rw [this, Complex.exp_nat_mul, Complex.exp_log hs]

lemma airyEnv_sq_firstQuadrant {s : ℂ} (h1 : 0 ≤ s.re) (h2 : 0 ≤ s.im) :
    airyEnv (s ^ 2) = Real.exp (-(4 / 3) * (s ^ 3).re) := by
  unfold airyEnv
  rw [cpow_sq_three_halves h1 h2]

/-- Real part of the exponent on the line `Im s = b`, for `Re ζ = -2b`. -/
lemma re_airyZ (t b η : ℝ) :
    (-(4 / 3 : ℂ) * ((t : ℂ) + b * I) ^ 3 - I * (((-2 * b : ℝ) : ℂ) + η * I) * ((t : ℂ) + b * I) ^ 2 -
      I * (((-2 * b : ℝ) : ℂ) + η * I) ^ 3 / 12).re = -(4 / 3) * (t - η / 2) ^ 2 * (t + η / 4) := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re]
  ring

lemma norm_airyPwsG_le {f : ℂ → ℂ} {C : ℝ} {N : ℕ}
    (hb : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N * airyEnv z) (ζ : ℂ) {s : ℂ} (h1 : 0 ≤ s.re)
    (h2 : 0 ≤ s.im) :
    ‖airyPwsG f ζ s‖ ≤ 2 * C * (1 + ‖s‖ ^ 2) ^ N * ‖s‖ *
      (Real.exp (-(4 / 3) * (s ^ 3).re) * Real.exp ((-(I * ζ * s ^ 2)).re)) := by
  unfold airyPwsG
  rw [norm_mul, norm_mul, Complex.norm_exp]
  have hf := hb (s ^ 2)
  rw [airyEnv_sq_firstQuadrant h1 h2, norm_pow] at hf
  have e2 : ‖(2 : ℂ) * s‖ = 2 * ‖s‖ := by simp
  rw [e2]
  have hex := Real.exp_pos ((-(I * ζ * s ^ 2)).re)
  calc ‖f (s ^ 2)‖ * Real.exp ((-(I * ζ * s ^ 2)).re) * (2 * ‖s‖)
      ≤ (C * (1 + ‖s‖ ^ 2) ^ N * Real.exp (-(4 / 3) * (s ^ 3).re)) * Real.exp ((-(I * ζ * s ^ 2)).re) *
        (2 * ‖s‖) := by gcongr
    _ = _ := by ring

lemma re_airyZ_split (s ζ : ℂ) :
    (-(4 / 3) * (s ^ 3).re) + (-(I * ζ * s ^ 2)).re + (-(I * ζ ^ 3 / 12)).re =
      (-(4 / 3 : ℂ) * s ^ 3 - I * ζ * s ^ 2 - I * ζ ^ 3 / 12).re := by
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im]
  norm_num
  ring

/-- Pointwise bound on the horizontal line `s = t + ib`, `Re ζ = -2b`:
`‖e^{-iζ³/12}‖ ‖G_ζ(t + ib)‖ ≤ 2C ((1+b)(1+t))^{2N+1} exp(-(4/3)(t - η/2)²(t + η/4))`. -/
lemma norm_hor_le {f : ℂ → ℂ} {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N * airyEnv z) {b η t : ℝ} (hbb : 0 ≤ b) (ht : 0 ≤ t) :
    ‖cexp (-(I * (((-2 * b : ℝ) : ℂ) + η * I) ^ 3 / 12))‖ *
        ‖airyPwsG f (((-2 * b : ℝ) : ℂ) + η * I) ((t : ℂ) + b * I)‖ ≤
      2 * C * ((1 + b) * (1 + t)) ^ (2 * N + 1) * Real.exp (-(4 / 3) * (t - η / 2) ^ 2 * (t + η / 4)) := by
  set ζ : ℂ := ((-2 * b : ℝ) : ℂ) + η * I with hζ
  set s : ℂ := (t : ℂ) + b * I with hs
  have hs1 : 0 ≤ s.re := by simp [hs, ht]
  have hs2 : 0 ≤ s.im := by simp [hs, hbb]
  have h := norm_airyPwsG_le hb ζ hs1 hs2
  rw [Complex.norm_exp]
  have hmul : Real.exp ((-(I * ζ ^ 3 / 12)).re) *
      (Real.exp (-(4 / 3) * (s ^ 3).re) * Real.exp ((-(I * ζ * s ^ 2)).re)) =
      Real.exp (-(4 / 3) * (t - η / 2) ^ 2 * (t + η / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have := re_airyZ_split s ζ
    have h2 := re_airyZ t b η
    rw [hs, hζ] at this
    rw [← h2, ← this]; ring
  have hre : s.re = t := by simp [hs]
  have him : s.im = b := by simp [hs]
  have hsq : ‖s‖ ^ 2 = t ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
  have hnorm : ‖s‖ ≤ (1 + b) * (1 + t) := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [hre, him, abs_of_nonneg ht, abs_of_nonneg hbb] at this
    nlinarith [mul_nonneg hbb ht]
  have hn1 : 1 + ‖s‖ ^ 2 ≤ ((1 + b) * (1 + t)) ^ 2 := by
    rw [hsq]
    have : ((1 + b) * (1 + t)) ^ 2 - (1 + (t ^ 2 + b ^ 2)) =
        2 * t + 2 * b + 4 * b * t + 2 * b * t ^ 2 + 2 * b ^ 2 * t + b ^ 2 * t ^ 2 := by ring
    have h0 : 0 ≤ 2 * t + 2 * b + 4 * b * t + 2 * b * t ^ 2 + 2 * b ^ 2 * t + b ^ 2 * t ^ 2 := by positivity
    linarith
  have hpos : 0 ≤ 2 * C * (1 + ‖s‖ ^ 2) ^ N * ‖s‖ := by positivity
  calc Real.exp ((-(I * ζ ^ 3 / 12)).re) * ‖airyPwsG f ζ s‖
      ≤ Real.exp ((-(I * ζ ^ 3 / 12)).re) * (2 * C * (1 + ‖s‖ ^ 2) ^ N * ‖s‖ *
        (Real.exp (-(4 / 3) * (s ^ 3).re) * Real.exp ((-(I * ζ * s ^ 2)).re))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = (2 * C * (1 + ‖s‖ ^ 2) ^ N * ‖s‖) * Real.exp (-(4 / 3) * (t - η / 2) ^ 2 * (t + η / 4)) := by
        rw [← hmul]; ring
    _ ≤ (2 * C * ((1 + b) * (1 + t)) ^ (2 * N) * ((1 + b) * (1 + t))) *
          Real.exp (-(4 / 3) * (t - η / 2) ^ 2 * (t + η / 4)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have h3 : (1 + ‖s‖ ^ 2) ^ N ≤ (((1 + b) * (1 + t)) ^ 2) ^ N := pow_le_pow_left₀ (by positivity) hn1 N
        rw [← pow_mul] at h3
        have := norm_nonneg s
        calc 2 * C * (1 + ‖s‖ ^ 2) ^ N * ‖s‖ ≤ 2 * C * ((1 + b) * (1 + t)) ^ (2 * N) * ‖s‖ := by gcongr
          _ ≤ _ := by gcongr
    _ = _ := by rw [pow_succ]; ring

/-- `K_m = ∫_0^∞ (1+t)^m e^{-t³/3} dt`. -/
noncomputable def airyK3 (m : ℕ) : ℝ := ∫ t in Ioi (0 : ℝ), (1 + t) ^ m * Real.exp (-(t ^ 3 / 3))

lemma integrableOn_airyK3 (m : ℕ) :
    IntegrableOn (fun t : ℝ => (1 + t) ^ m * Real.exp (-(t ^ 3 / 3))) (Ioi 0) := by
  have h := (integrableOn_pow_mul_exp m (by norm_num : (0 : ℝ) < 1)).const_mul (Real.exp (2 / 3))
  refine Integrable.mono' h ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : Real.exp (-(t ^ 3 / 3)) ≤ Real.exp (2 / 3) * Real.exp (-1 * t) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [sq_nonneg (t - 1), mul_nonneg ht0 (sq_nonneg (t - 1))]
    calc (1 + t) ^ m * Real.exp (-(t ^ 3 / 3)) ≤ (1 + t) ^ m * (Real.exp (2 / 3) * Real.exp (-1 * t)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring

lemma airyK3_nonneg (m : ℕ) : 0 ≤ airyK3 m :=
  setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : 0 ≤ t := le_of_lt ht
    positivity

/-- `E(t) = exp(-(4/3)(t-η/2)²(t+η/4)) ≤ 1` and `≤ e^{-t³/3}` for `t ≥ η`. -/
lemma airyE_le {η t : ℝ} (hη : 0 ≤ η) (ht : 0 ≤ t) :
    Real.exp (-(4 / 3) * (t - η / 2) ^ 2 * (t + η / 4)) ≤ 1 ∧
      (η ≤ t → Real.exp (-(4 / 3) * (t - η / 2) ^ 2 * (t + η / 4)) ≤ Real.exp (-(t ^ 3 / 3))) := by
  refine ⟨Real.exp_le_one_iff.mpr ?_, fun h => Real.exp_le_exp.mpr ?_⟩
  · have : 0 ≤ (t - η / 2) ^ 2 * (t + η / 4) := by positivity
    nlinarith
  · have h1 : t / 2 ≤ t - η / 2 := by linarith
    have h2 : (t / 2) ^ 2 ≤ (t - η / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    have h3 : t ≤ t + η / 4 := by linarith
    have h4 : (t / 2) ^ 2 * t ≤ (t - η / 2) ^ 2 * (t + η / 4) :=
      mul_le_mul h2 h3 ht (by positivity)
    nlinarith

/-- The integrable majorant on the horizontal line. -/
noncomputable def airyHorMaj (C : ℝ) (m : ℕ) (b η : ℝ) (t : ℝ) : ℝ :=
  2 * C * (1 + b) ^ m * ((1 + η) ^ m * (Ioc (0 : ℝ) η).indicator (fun _ => (1 : ℝ)) t +
    (1 + t) ^ m * Real.exp (-(t ^ 3 / 3)))

lemma integrable_indicator_Ioc_one (η : ℝ) :
    Integrable (fun t : ℝ => (Ioc (0 : ℝ) η).indicator (fun _ => (1 : ℝ)) t) (volume.restrict (Ioi 0)) := by
  have : Integrable (fun t : ℝ => (Ioc (0 : ℝ) η).indicator (fun _ => (1 : ℝ)) t) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  exact this.restrict

lemma integrableOn_airyHorMaj (C : ℝ) (m : ℕ) (b η : ℝ) :
    IntegrableOn (airyHorMaj C m b η) (Ioi 0) := by
  unfold airyHorMaj
  exact Integrable.const_mul (Integrable.add ((integrable_indicator_Ioc_one η).const_mul _)
    (integrableOn_airyK3 m)) _

lemma integral_airyHorMaj {C : ℝ} (m : ℕ) {b η : ℝ} (hη : 0 ≤ η) :
    ∫ t in Ioi (0 : ℝ), airyHorMaj C m b η t = 2 * C * (1 + b) ^ m * ((1 + η) ^ m * η + airyK3 m) := by
  unfold airyHorMaj airyK3
  rw [integral_const_mul]
  congr 1
  rw [integral_add ((integrable_indicator_Ioc_one η).const_mul _) (integrableOn_airyK3 m),
    integral_const_mul]
  congr 1
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Ioc_subset_Ioi_self]
  simp [Real.volume_real_Ioc, hη]

/-- The twisted horizontal integrand is dominated by `airyHorMaj` on `t > 0`. -/
lemma hor_dom {f : ℂ → ℂ} {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N * airyEnv z) {b η : ℝ} (hbb : 0 ≤ b) (hη : 0 ≤ η)
    {t : ℝ} (ht : 0 < t) :
    ‖cexp (-(I * (((-2 * b : ℝ) : ℂ) + η * I) ^ 3 / 12))‖ *
        ‖airyPwsG f (((-2 * b : ℝ) : ℂ) + η * I) ((t : ℂ) + b * I)‖ ≤
      airyHorMaj C (2 * N + 1) b η t := by
  refine (norm_hor_le hC hb hbb ht.le).trans ?_
  unfold airyHorMaj
  obtain ⟨hE1, hE2⟩ := airyE_le hη ht.le
  set m := 2 * N + 1
  have hpos : 0 ≤ 2 * C * (1 + b) ^ m := by positivity
  have key : (1 + t) ^ m * Real.exp (-(4 / 3) * (t - η / 2) ^ 2 * (t + η / 4)) ≤
      (1 + η) ^ m * (Ioc (0 : ℝ) η).indicator (fun _ => (1 : ℝ)) t +
        (1 + t) ^ m * Real.exp (-(t ^ 3 / 3)) := by
    have h1 : 0 ≤ (1 + t) ^ m := by positivity
    by_cases hle : t ≤ η
    · have hmem : t ∈ Ioc (0 : ℝ) η := ⟨ht, hle⟩
      rw [Set.indicator_of_mem hmem]
      have : (1 + t) ^ m ≤ (1 + η) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      have h2 := Real.exp_pos (-(t ^ 3 / 3))
      calc (1 + t) ^ m * Real.exp (-(4 / 3) * (t - η / 2) ^ 2 * (t + η / 4)) ≤ (1 + t) ^ m * 1 :=
            mul_le_mul_of_nonneg_left hE1 h1
        _ ≤ (1 + η) ^ m * 1 + (1 + t) ^ m * Real.exp (-(t ^ 3 / 3)) := by
            have : 0 ≤ (1 + t) ^ m * Real.exp (-(t ^ 3 / 3)) := by positivity
            linarith
    · have hmem : t ∉ Ioc (0 : ℝ) η := fun h => hle h.2
      rw [Set.indicator_of_notMem hmem, mul_zero, zero_add]
      exact mul_le_mul_of_nonneg_left (hE2 (le_of_lt (not_le.mp hle))) h1
  calc 2 * C * ((1 + b) * (1 + t)) ^ m * Real.exp (-(4 / 3) * (t - η / 2) ^ 2 * (t + η / 4))
      = 2 * C * (1 + b) ^ m * ((1 + t) ^ m * Real.exp (-(4 / 3) * (t - η / 2) ^ 2 * (t + η / 4))) := by
        rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hpos

lemma re_vert_exponent (R y b η : ℝ) :
    (-(4 / 3) * (((R : ℂ) + y * I) ^ 3).re) +
        (-(I * (((-2 * b : ℝ) : ℂ) + η * I) * ((R : ℂ) + y * I) ^ 2)).re =
      -(4 / 3) * (R ^ 3 - 3 * R * y ^ 2) + (η * (R ^ 2 - y ^ 2) - 4 * b * R * y) := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re]
  ring

/-- Bound on the vertical side `s = R + iy`, `0 ≤ y ≤ b`. -/
lemma norm_vert_le {f : ℂ → ℂ} {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N * airyEnv z) {b η R y : ℝ} (hbb : 0 ≤ b) (hη : 0 ≤ η)
    (hR : 0 ≤ R) (hy0 : 0 ≤ y) (hyb : y ≤ b) :
    ‖airyPwsG f (((-2 * b : ℝ) : ℂ) + η * I) ((R : ℂ) + y * I)‖ ≤
      2 * C * (1 + R + b) ^ (2 * N + 1) * Real.exp (-(4 / 3) * R ^ 3 + 4 * b ^ 2 * R + η * R ^ 2) := by
  set ζ : ℂ := ((-2 * b : ℝ) : ℂ) + η * I with hζ
  set s : ℂ := (R : ℂ) + y * I with hs
  have hs1 : 0 ≤ s.re := by simp [hs, hR]
  have hs2 : 0 ≤ s.im := by simp [hs, hy0]
  have h := norm_airyPwsG_le hb ζ hs1 hs2
  have hre : s.re = R := by simp [hs]
  have him : s.im = y := by simp [hs]
  have hsq : ‖s‖ ^ 2 = R ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
  have hnorm : ‖s‖ ≤ 1 + R + b := by
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [hre, him, abs_of_nonneg hR, abs_of_nonneg hy0] at this
    linarith
  have hn1 : 1 + ‖s‖ ^ 2 ≤ (1 + R + b) ^ 2 := by
    rw [hsq]; nlinarith [mul_nonneg hR hbb, mul_self_le_mul_self hy0 hyb, mul_nonneg hR hy0]
  have hexp : Real.exp (-(4 / 3) * (s ^ 3).re) * Real.exp ((-(I * ζ * s ^ 2)).re) ≤
      Real.exp (-(4 / 3) * R ^ 3 + 4 * b ^ 2 * R + η * R ^ 2) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := re_vert_exponent R y b η
    rw [hs, hζ] at *
    rw [this]
    have h1 : y ^ 2 ≤ b ^ 2 := by nlinarith
    have h2 : 0 ≤ η * y ^ 2 := by positivity
    have h3 : 0 ≤ b * R * y := by positivity
    have h4 : R * y ^ 2 ≤ R * b ^ 2 := mul_le_mul_of_nonneg_left h1 hR
    nlinarith
  have hpos : 0 ≤ 2 * C * (1 + ‖s‖ ^ 2) ^ N * ‖s‖ := by positivity
  refine h.trans ?_
  calc 2 * C * (1 + ‖s‖ ^ 2) ^ N * ‖s‖ * (Real.exp (-(4 / 3) * (s ^ 3).re) * Real.exp ((-(I * ζ * s ^ 2)).re))
      ≤ (2 * C * (1 + ‖s‖ ^ 2) ^ N * ‖s‖) * Real.exp (-(4 / 3) * R ^ 3 + 4 * b ^ 2 * R + η * R ^ 2) :=
        mul_le_mul_of_nonneg_left hexp hpos
    _ ≤ (2 * C * (1 + R + b) ^ (2 * N) * (1 + R + b)) * Real.exp (-(4 / 3) * R ^ 3 + 4 * b ^ 2 * R + η * R ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have h3 : (1 + ‖s‖ ^ 2) ^ N ≤ ((1 + R + b) ^ 2) ^ N := pow_le_pow_left₀ (by positivity) hn1 N
        rw [← pow_mul] at h3
        have := norm_nonneg s
        calc 2 * C * (1 + ‖s‖ ^ 2) ^ N * ‖s‖ ≤ 2 * C * (1 + R + b) ^ (2 * N) * ‖s‖ := by gcongr
          _ ≤ _ := by gcongr
    _ = _ := by rw [pow_succ]; ring

/-- `(1+R+b)^m e^{-(4/3)R³+cR+ηR²} → 0`. -/
lemma tendsto_poly_exp_cubic (m : ℕ) (b c η : ℝ) (hη : 0 ≤ η) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    Tendsto (fun R : ℝ => (1 + R + b) ^ m * Real.exp (-(4 / 3) * R ^ 3 + c * R + η * R ^ 2)) atTop (𝓝 0) := by
  have hb0 : Tendsto (fun R : ℝ => R + (1 + b)) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp hb0
  have h2 := h1.mul_const (Real.exp (1 + b))
  rw [zero_mul] at h2
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have : 0 ≤ 1 + R + b := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (max 1 (3 * (η + c)))] with R hR
    have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
    have hR2 : 3 * (η + c) ≤ R := le_trans (le_max_right _ _) hR
    have hexp : -(4 / 3) * R ^ 3 + c * R + η * R ^ 2 ≤ -R := by
      have h3 : (η + c) * R ^ 2 ≤ R ^ 3 / 3 := by nlinarith [sq_nonneg R]
      have h4 : c * R ≤ c * R ^ 2 := by nlinarith [mul_nonneg hc (sq_nonneg R)]
      nlinarith [sq_nonneg R, pow_pos (by linarith : (0 : ℝ) < R) 3, mul_nonneg hη (sq_nonneg R)]
    simp only [Function.comp_apply]
    have hp : 0 ≤ (1 + R + b) ^ m := by
      have : 0 ≤ 1 + R + b := by linarith
      positivity
    have : (1 + R + b) ^ m * Real.exp (-(4 / 3) * R ^ 3 + c * R + η * R ^ 2) ≤
        (1 + R + b) ^ m * Real.exp (-R) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hp
    refine this.trans (le_of_eq ?_)
    have e : (R + (1 + b)) ^ m * Real.exp (-(R + (1 + b))) * Real.exp (1 + b) =
        (R + (1 + b)) ^ m * Real.exp (-R) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [e]; congr 2; ring

/-- The vertical side of the rectangle tends to `0`. -/
theorem tendsto_vert {f : ℂ → ℂ} {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N * airyEnv z) {b η : ℝ} (hbb : 0 ≤ b) (hη : 0 ≤ η) :
    Tendsto (fun R : ℝ => ∫ y in (0 : ℝ)..b, airyPwsG f (((-2 * b : ℝ) : ℂ) + η * I) ((R : ℂ) + y * I))
      atTop (𝓝 0) := by
  have hlim := (tendsto_poly_exp_cubic (2 * N + 1) b (4 * b ^ 2) η hη (by positivity) hbb).const_mul (2 * C * b)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := b)
    (f := fun y : ℝ => airyPwsG f (((-2 * b : ℝ) : ℂ) + η * I) ((R : ℂ) + y * I))
    (C := 2 * C * (1 + R + b) ^ (2 * N + 1) * Real.exp (-(4 / 3) * R ^ 3 + 4 * b ^ 2 * R + η * R ^ 2))
    (fun y hy => by
      rw [Set.uIoc_of_le hbb] at hy
      exact norm_vert_le hC hb hbb hη hR hy.1.le hy.2)
  rw [abs_of_nonneg (by simpa using hbb), sub_zero] at this
  refine this.trans (le_of_eq ?_)
  ring

lemma norm_cexp_twist (b η : ℝ) :
    ‖cexp (-(I * (((-2 * b : ℝ) : ℂ) + η * I) ^ 3 / 12))‖ = Real.exp (b ^ 2 * η - η ^ 3 / 12) := by
  rw [Complex.norm_exp]
  congr 1
  simp [pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  ring

lemma norm_cexp_twist_pos (ζ : ℂ) : 0 < ‖cexp (-(I * ζ ^ 3 / 12))‖ := by
  rw [Complex.norm_exp]; exact Real.exp_pos _

/-- The vertical piece: `‖e^{-iζ³/12}‖ ‖∫_b^∞ 2y J(-y²) dy‖ ≤ ∫_{u<0} ‖f‖`. -/
lemma vert_piece_le {f : ℂ → ℂ} (hf : AiryClassG f) {b η : ℝ} (hbb : 0 ≤ b) (hη : 0 ≤ η) :
    ‖cexp (-(I * (((-2 * b : ℝ) : ℂ) + η * I) ^ 3 / 12))‖ *
      ‖∫ y in Ioi b, ((2 * y : ℝ)) • airyJ f (((-2 * b : ℝ) : ℂ) + η * I) (-y ^ 2)‖ ≤
      ∫ u : ℝ, ‖f (u : ℂ)‖ := by
  set ζ : ℂ := ((-2 * b : ℝ) : ℂ) + η * I with hζ
  set c := ‖cexp (-(I * ζ ^ 3 / 12))‖ with hc
  have hc0 : 0 < c := norm_cexp_twist_pos ζ
  have hnf : Integrable (fun u : ℝ => ‖f (u : ℂ)‖) := hf.integrable.norm
  have hint0 : IntegrableOn (fun y : ℝ => ((2 * y : ℝ)) • ‖f ((-y ^ 2 : ℝ) : ℂ)‖) (Ioi 0) :=
    (integrableOn_Iio_neg_sq_iff (fun u : ℝ => ‖f (u : ℂ)‖)).mp hnf.integrableOn
  have hpt : ∀ y ∈ Ioi b, c * ‖((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)‖ ≤ ((2 * y : ℝ)) • ‖f ((-y ^ 2 : ℝ) : ℂ)‖ := by
    intro y hy
    have hyb : b < y := hy
    have hy0 : 0 ≤ y := by linarith
    simp only [airyJ, norm_smul, Real.norm_eq_abs, norm_mul, norm_cexp_airyFhat,
      abs_of_nonneg hy0, abs_two, smul_eq_mul]
    have hζim : ζ.im = η := by simp [hζ]
    rw [hζim, hc, hζ, norm_cexp_twist]
    have e1 : Real.exp (b ^ 2 * η - η ^ 3 / 12) * Real.exp (η * -y ^ 2) ≤ 1 := by
      rw [← Real.exp_add]
      refine Real.exp_le_one_iff.mpr ?_
      have : η * b ^ 2 ≤ η * y ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hη
      nlinarith [pow_nonneg hη 3]
    have h2 : 0 ≤ 2 * y * ‖f ((-y ^ 2 : ℝ) : ℂ)‖ := by positivity
    calc Real.exp (b ^ 2 * η - η ^ 3 / 12) * (2 * y * (‖f ((-y ^ 2 : ℝ) : ℂ)‖ * Real.exp (η * -y ^ 2)))
        = (2 * y * ‖f ((-y ^ 2 : ℝ) : ℂ)‖) * (Real.exp (b ^ 2 * η - η ^ 3 / 12) * Real.exp (η * -y ^ 2)) := by ring
      _ ≤ (2 * y * ‖f ((-y ^ 2 : ℝ) : ℂ)‖) * 1 := mul_le_mul_of_nonneg_left e1 h2
      _ = _ := by ring
  have hgi : IntegrableOn (fun y : ℝ => ‖((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)‖) (Ioi b) := by
    have hnn : ∀ y ∈ Ioi b, 0 ≤ ‖((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)‖ := fun _ _ => norm_nonneg _
    have hge : IntegrableOn (fun y : ℝ => ((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)) (Ioi 0) := by
      have hJ := integrable_airyJ hf (ζ := ζ) (by simp [hζ, hη])
      exact (integrableOn_Iio_neg_sq_iff _).mp hJ.integrableOn
    exact (hge.mono_set (Ioi_subset_Ioi hbb)).norm
  calc c * ‖∫ y in Ioi b, ((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)‖
      ≤ c * ∫ y in Ioi b, ‖((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hc0.le
    _ = ∫ y in Ioi b, c * ‖((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ y in Ioi b, ((2 * y : ℝ)) • ‖f ((-y ^ 2 : ℝ) : ℂ)‖ :=
        setIntegral_mono_on (hgi.const_mul c) (hint0.mono_set (Ioi_subset_Ioi hbb))
          measurableSet_Ioi hpt
    _ ≤ ∫ y in Ioi 0, ((2 * y : ℝ)) • ‖f ((-y ^ 2 : ℝ) : ℂ)‖ := by
        refine setIntegral_mono_set hint0 ?_ (Eventually.of_forall (Ioi_subset_Ioi hbb))
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
        have : 0 < y := hy
        simp only [Pi.zero_apply, smul_eq_mul]
        positivity
    _ = ∫ u in Iio (0 : ℝ), ‖f (u : ℂ)‖ := (integral_Iio_neg_sq (fun u : ℝ => ‖f (u : ℂ)‖)).symm
    _ ≤ ∫ u : ℝ, ‖f (u : ℂ)‖ :=
        setIntegral_le_integral hnf (Eventually.of_forall fun u => norm_nonneg _)

/-- **Exact decomposition and bound at one point** (`Re ζ = -2b ≤ 0`, `Im ζ = η ≥ 0`): with `m = 2N+1`,
`|F̃(ζ)| ≤ k (2C (1+b)^m ((1+η)^m η + K_m) + ‖f‖_{L¹})`. -/
theorem norm_airyFtilde_le {f : ℂ → ℂ} (hf : AiryClassG f) {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N * airyEnv z) {b η : ℝ} (hbb : 0 ≤ b) (hη : 0 ≤ η) :
    ‖airyFtilde f (((-2 * b : ℝ) : ℂ) + η * I)‖ ≤
      airyPhiK * (2 * C * (1 + b) ^ (2 * N + 1) * ((1 + η) ^ (2 * N + 1) * η + airyK3 (2 * N + 1)) +
        ∫ u : ℝ, ‖f (u : ℂ)‖) := by
  set ζ : ℂ := ((-2 * b : ℝ) : ℂ) + η * I with hζ
  have hζim : 0 ≤ ζ.im := by simp [hζ, hη]
  set c := ‖cexp (-(I * ζ ^ 3 / 12))‖ with hc
  have hc0 : 0 < c := norm_cexp_twist_pos ζ
  have hhor0 : IntegrableOn (fun t : ℝ => ‖cexp (-(I * ζ ^ 3 / 12))‖ * ‖airyPwsG f ζ ((t : ℂ) + b * I)‖)
      (Ioi 0) := by
    refine Integrable.mono' (integrableOn_airyHorMaj C (2 * N + 1) b η) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      have := (differentiable_airyPwsG hf.differentiable ζ).continuous
      fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hor_dom hC hb hbb hη ht
  have hhor : IntegrableOn (fun t : ℝ => airyPwsG f ζ ((t : ℂ) + b * I)) (Ioi 0) := by
    have := hhor0.const_mul c⁻¹
    refine this.mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      have := (differentiable_airyPwsG hf.differentiable ζ).continuous
      fun_prop
    · refine Eventually.of_forall fun t => ?_
      rw [← hc, ← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
  have hvert := tendsto_vert (f := f) hC hb hbb hη
  have hdec := airyFhat_eq_hor_add_vert hf hζim hbb hhor hvert
  have hHb : c * ‖∫ t in Ioi (0 : ℝ), airyPwsG f ζ ((t : ℂ) + b * I)‖ ≤
      2 * C * (1 + b) ^ (2 * N + 1) * ((1 + η) ^ (2 * N + 1) * η + airyK3 (2 * N + 1)) := by
    calc c * ‖∫ t in Ioi (0 : ℝ), airyPwsG f ζ ((t : ℂ) + b * I)‖
        ≤ c * ∫ t in Ioi (0 : ℝ), ‖airyPwsG f ζ ((t : ℂ) + b * I)‖ :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hc0.le
      _ = ∫ t in Ioi (0 : ℝ), c * ‖airyPwsG f ζ ((t : ℂ) + b * I)‖ := (integral_const_mul _ _).symm
      _ ≤ ∫ t in Ioi (0 : ℝ), airyHorMaj C (2 * N + 1) b η t :=
          setIntegral_mono_on hhor0 (integrableOn_airyHorMaj C (2 * N + 1) b η) measurableSet_Ioi
            (fun t ht => hor_dom hC hb hbb hη ht)
      _ = _ := integral_airyHorMaj (2 * N + 1) hη
  have hVb := vert_piece_le hf hbb hη
  unfold airyFtilde
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos airyPhiK_pos, hdec]
  have h3 : c * ‖(∫ t in Ioi (0 : ℝ), airyPwsG f ζ ((t : ℂ) + b * I)) +
      ∫ y in Ioi b, ((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)‖ ≤ _ :=
    calc c * ‖(∫ t in Ioi (0 : ℝ), airyPwsG f ζ ((t : ℂ) + b * I)) +
          ∫ y in Ioi b, ((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)‖
        ≤ c * (‖∫ t in Ioi (0 : ℝ), airyPwsG f ζ ((t : ℂ) + b * I)‖ +
          ‖∫ y in Ioi b, ((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hc0.le
      _ = c * ‖∫ t in Ioi (0 : ℝ), airyPwsG f ζ ((t : ℂ) + b * I)‖ +
          c * ‖∫ y in Ioi b, ((2 * y : ℝ)) • airyJ f ζ (-y ^ 2)‖ := by ring
      _ ≤ _ := add_le_add hHb hVb
  have := mul_le_mul_of_nonneg_left h3 airyPhiK_pos.le
  calc airyPhiK * c * _ = airyPhiK * (c * _) := by ring
    _ ≤ _ := this

end FormalResearch.Special
