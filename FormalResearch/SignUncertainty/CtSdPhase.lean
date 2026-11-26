module

public import FormalResearch.SignUncertainty.CtSdLine
public import FormalResearch.SignUncertainty.CtSdMoments
public import FormalResearch.SignUncertainty.CtAiryRay

/-!
# The Airy phase along the steepest-descent pieces (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 (`ct:sd-moments`).  **Proved.**
`Ph_U(w) = 2^{2/3} U w + w³/3`.  Along the pieces of `Γ_SD` the modulus `|e^{iPh}| = e^{-Im Ph}` is explicit:
* ray `w = r e^{iπ/6}`: `Im Ph = ν U r + r³/3`, `ν = 2^{-1/3}`;
* `U = -v²/κ` (`v = w_*`), `w = v t (1-i)`: `Im Ph = v³(t - 2t³/3)`;
* `w = v(1 + u(1+i))`: `Im Ph = v³ u²(2 + 2u/3)`;
* the ray again: `Im Ph = r³/3 - v² r/2`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

namespace FormalResearch.SignUncertainty.CtSd

/-- `κ = 2^{2/3}` (as in `ct:airy-id1`). -/
noncomputable abbrev kap : ℝ := CtAiry.kap

/-- The model phase `Ph_U(w) = κ U w + w³/3`. -/
noncomputable def PhU (U : ℝ) (w : ℂ) : ℂ := (kap : ℂ) * U * w + w ^ 3 / 3

lemma kap_pos : 0 < kap := by unfold kap CtAiry.kap; positivity

lemma norm_exp_I_mul (z : ℂ) : ‖Complex.exp (Complex.I * z)‖ = Real.exp (-z.im) := by
  rw [Complex.norm_exp]; simp

lemma nu_eq : nu = kap / 2 := by
  unfold nu kap CtAiry.kap
  have : (2 : ℝ) ^ (2 / 3 : ℝ) = 2 * (2 : ℝ) ^ (-(1 : ℝ) / 3) := by
    rw [show (2 / 3 : ℝ) = 1 + (-(1 : ℝ) / 3) by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
  rw [this]; ring

/-- If `‖h(w)‖ ≤ K ‖w‖^α` on the segment, the phase-weighted segment integral is bounded by the `α`-moment
(the dominating function is assumed interval integrable). -/
theorem lineInt_phase_le {U : ℝ} {z₀ d : ℂ} {a b : ℝ} (hab : a ≤ b) {h : ℂ → ℂ} {K α : ℝ}
    (hh : ∀ t ∈ Ioc a b, ‖h (z₀ + (t : ℂ) * d)‖ ≤ K * ‖z₀ + (t : ℂ) * d‖ ^ α)
    (hint : IntervalIntegrable (fun t : ℝ => K * (‖z₀ + (t : ℂ) * d‖ ^ α *
      Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) * ‖d‖)) volume a b) :
    ‖lineInt z₀ d a b (fun w => h w * Complex.exp (Complex.I * PhU U w))‖ ≤
      K * ∫ t in a..b, ‖z₀ + (t : ℂ) * d‖ ^ α * Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) * ‖d‖ := by
  rw [← intervalIntegral.integral_const_mul]
  unfold lineInt
  refine intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun t ht => ?_) hint
  rw [norm_mul, norm_mul, norm_exp_I_mul]
  have := hh t ht
  have hd : 0 ≤ ‖d‖ := norm_nonneg d
  have he : 0 ≤ Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) := (Real.exp_pos _).le
  calc ‖h (z₀ + (t : ℂ) * d)‖ * Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) * ‖d‖
      ≤ K * ‖z₀ + (t : ℂ) * d‖ ^ α * Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) * ‖d‖ := by gcongr
    _ = K * (‖z₀ + (t : ℂ) * d‖ ^ α * Real.exp (-(PhU U (z₀ + (t : ℂ) * d)).im) * ‖d‖) := by ring

/-- The ray direction `e^{iπ/6}`. -/
noncomputable def d6 : ℂ := Complex.exp (Complex.I * (π / 6 : ℝ))

lemma d6_eq : d6 = ⟨Real.sqrt 3 / 2, 1 / 2⟩ := by
  unfold d6
  rw [mul_comm]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]; exact Real.cos_pi_div_six
  · rw [Complex.exp_ofReal_mul_I_im]; exact Real.sin_pi_div_six

lemma d6_re : d6.re = Real.sqrt 3 / 2 := by rw [d6_eq]
lemma d6_im : d6.im = 1 / 2 := by rw [d6_eq]

lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma norm_d6 : ‖d6‖ = 1 := by
  unfold d6
  rw [Complex.norm_exp]; simp

lemma d6_cube : d6 ^ 3 = Complex.I := by
  rw [d6_eq]
  apply Complex.ext
  · simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, Complex.I_re]
    linear_combination (Real.sqrt 3 / 8) * sqrt3_sq
  · simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, Complex.I_im]
    linear_combination (3 / 8) * sqrt3_sq

lemma im_ray (U : ℝ) (t : ℝ) : (PhU U (0 + (t : ℂ) * d6)).im = nu * U * t + t ^ 3 / 3 := by
  have h3 : ((t : ℂ) * d6) ^ 3 = (t : ℂ) ^ 3 * Complex.I := by rw [mul_pow, d6_cube]
  have hw : ((t : ℂ) * d6).im = t / 2 := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, d6_im]; ring
  unfold PhU
  rw [zero_add, Complex.add_im, h3, Complex.div_ofNat_im]
  have e1 : ((kap : ℂ) * (U : ℂ) * ((t : ℂ) * d6)).im = kap * U * (t / 2) := by
    have : (kap : ℂ) * (U : ℂ) * ((t : ℂ) * d6) = ((kap * U : ℝ) : ℂ) * ((t : ℂ) * d6) := by push_cast; ring
    rw [this, Complex.im_ofReal_mul, hw]
  have e2 : ((t : ℂ) ^ 3 * Complex.I).im = t ^ 3 := by
    have : (t : ℂ) ^ 3 = ((t ^ 3 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.im_ofReal_mul, Complex.I_im, mul_one]
  rw [e1, e2, nu_eq]; ring

lemma norm_ray {t : ℝ} (ht : 0 ≤ t) : ‖(0 : ℂ) + (t : ℂ) * d6‖ = t := by
  rw [zero_add, norm_mul, norm_d6, Complex.norm_real, Real.norm_of_nonneg ht, mul_one]

/-- Ray piece: the moment equals the real integral of `momA`. -/
lemma ray_moment_eq (U R α : ℝ) (hR : 0 ≤ R) :
    ∫ t in (0 : ℝ)..R, ‖(0 : ℂ) + (t : ℂ) * d6‖ ^ α * Real.exp (-(PhU U (0 + (t : ℂ) * d6)).im) * ‖d6‖ =
      ∫ t in (0 : ℝ)..R, t ^ α * Real.exp (-(nu * U * t + t ^ 3 / 3)) := by
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le hR] at ht
  simp only [norm_ray ht.1, im_ray, norm_d6, mul_one]

lemma PhU_B (v : ℝ) (w : ℂ) : PhU (-(v ^ 2) / kap) w = w ^ 3 / 3 - (v : ℂ) ^ 2 * w := by
  unfold PhU
  have hk : (kap : ℂ) ≠ 0 := by exact_mod_cast kap_pos.ne'
  have : (kap : ℂ) * ((-(v ^ 2) / kap : ℝ) : ℂ) = -((v : ℂ) ^ 2) := by
    push_cast; field_simp
  rw [this]; ring

lemma im_cube_aux (w : ℂ) : (w ^ 3).im = 3 * w.re ^ 2 * w.im - w.im ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im]; ring

lemma im_PhB (v : ℝ) (w : ℂ) : (w ^ 3 / 3 - (v : ℂ) ^ 2 * w).im = (3 * w.re ^ 2 * w.im - w.im ^ 3) / 3 - v ^ 2 * w.im := by
  rw [Complex.sub_im, Complex.div_ofNat_im, im_cube_aux]
  have : ((v : ℂ) ^ 2 * w).im = v ^ 2 * w.im := by
    have : (v : ℂ) ^ 2 = ((v ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.im_ofReal_mul]
  rw [this]

lemma im_seg1 (v t : ℝ) : (PhU (-(v ^ 2) / kap) (0 + (t : ℂ) * ((v : ℂ) * (1 - Complex.I)))).im =
    v ^ 3 * (t - 2 / 3 * t ^ 3) := by
  rw [PhU_B, im_PhB]
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma im_seg2 (v t : ℝ) : (PhU (-(v ^ 2) / kap) ((v : ℂ) + (t : ℂ) * ((v : ℂ) * (1 + Complex.I)))).im =
    v ^ 3 * (t ^ 2 * (2 + 2 / 3 * t)) := by
  rw [PhU_B, im_PhB]
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma im_seg3 (v t : ℝ) : (PhU (-(v ^ 2) / kap) (0 + (t : ℂ) * d6)).im = t ^ 3 / 3 - v ^ 2 / 2 * t := by
  rw [im_ray, nu_eq]
  have := kap_pos.ne'
  field_simp
  ring

lemma norm_seg1 {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    ‖(0 : ℂ) + (t : ℂ) * ((v : ℂ) * (1 - Complex.I))‖ = Real.sqrt 2 * v * t := by
  rw [zero_add, Complex.norm_def, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  rw [show t * v * (t * v) + t * v * (t * v) = (Real.sqrt 2 * v * t) ^ 2 by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num); nlinarith]
  exact Real.sqrt_sq (by positivity)

lemma norm_d_seg1 {v : ℝ} (hv : 0 ≤ v) : ‖(v : ℂ) * (1 - Complex.I)‖ = Real.sqrt 2 * v := by
  have := norm_seg1 (v := v) (t := 1) hv (by norm_num)
  simpa using this

lemma norm_seg2 {v : ℝ} (hv : 0 ≤ v) (t : ℝ) :
    ‖(v : ℂ) + (t : ℂ) * ((v : ℂ) * (1 + Complex.I))‖ = v * Real.sqrt ((1 + t) ^ 2 + t ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  rw [show (v + t * v) * (v + t * v) + t * v * (t * v) = v ^ 2 * ((1 + t) ^ 2 + t ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv]

lemma norm_d_seg2 {v : ℝ} (hv : 0 ≤ v) : ‖(v : ℂ) * (1 + Complex.I)‖ = Real.sqrt 2 * v := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  rw [show v * v + v * v = (Real.sqrt 2 * v) ^ 2 by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num); nlinarith]
  exact Real.sqrt_sq (by positivity)

lemma seg1_moment_eq {v : ℝ} (hv : 0 ≤ v) (α : ℝ) :
    ∫ t in (0 : ℝ)..(1 / 2), ‖(0 : ℂ) + (t : ℂ) * ((v : ℂ) * (1 - Complex.I))‖ ^ α *
        Real.exp (-(PhU (-(v ^ 2) / kap) (0 + (t : ℂ) * ((v : ℂ) * (1 - Complex.I)))).im) *
          ‖(v : ℂ) * (1 - Complex.I)‖ =
      ∫ t in (0 : ℝ)..(1 / 2), (Real.sqrt 2 * v * t) ^ α * Real.exp (-(v ^ 3 * (t - 2 / 3 * t ^ 3))) *
        (Real.sqrt 2 * v) := by
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le (by norm_num)] at ht
  rw [norm_seg1 hv ht.1, im_seg1, norm_d_seg1 hv]

lemma seg2_moment_eq {v : ℝ} (hv : 0 ≤ v) (α uJ : ℝ) :
    ∫ t in (-(1 / 2 : ℝ))..uJ, ‖(v : ℂ) + (t : ℂ) * ((v : ℂ) * (1 + Complex.I))‖ ^ α *
        Real.exp (-(PhU (-(v ^ 2) / kap) ((v : ℂ) + (t : ℂ) * ((v : ℂ) * (1 + Complex.I)))).im) *
          ‖(v : ℂ) * (1 + Complex.I)‖ =
      ∫ t in (-(1 / 2 : ℝ))..uJ, (v * Real.sqrt ((1 + t) ^ 2 + t ^ 2)) ^ α *
        Real.exp (-(v ^ 3 * (t ^ 2 * (2 + 2 / 3 * t)))) * (Real.sqrt 2 * v) := by
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  simp only [norm_seg2 hv, im_seg2, norm_d_seg2 hv]

lemma seg3_moment_eq {v rJ R : ℝ} (hrJ : 0 ≤ rJ) (hR : rJ ≤ R) (α : ℝ) :
    ∫ t in rJ..R, ‖(0 : ℂ) + (t : ℂ) * d6‖ ^ α * Real.exp (-(PhU (-(v ^ 2) / kap) (0 + (t : ℂ) * d6)).im) * ‖d6‖ =
      ∫ t in rJ..R, t ^ α * Real.exp (-(t ^ 3 / 3 - v ^ 2 / 2 * t)) := by
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le hR] at ht
  rw [norm_ray (hrJ.trans ht.1), im_seg3, norm_d6, mul_one]

end FormalResearch.SignUncertainty.CtSd
