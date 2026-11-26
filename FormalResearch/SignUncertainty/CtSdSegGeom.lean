module

public import FormalResearch.SignUncertainty.CtSdAiry

/-!
# Geometry of the connecting segment `R e^{iπ/6} → R` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3, "Tail and connecting arc" (here the circular arc
`|s| = s₁`, `θ ∈ [0, π/6]` is replaced by the straight segment, which has the same properties used there).  **Proved.**
Along `w(t) = R(e^{iπ/6} + t(1 - e^{iπ/6}))`, `t ∈ [0,1]`: `|w| ≤ R`, `|w| ≥ (√3/2) R`, `Re w ≥ (√3/2)R`, `0 ≤ Im w ≤ R/2`,
`Re(w²) ≥ R²/2`, hence for `κ|U| ≤ R²/16`: `R²/4 ≤ |κU + w²| ≤ 2R²` and `Im Ph_U(w) ≥ 0`, with `Im Ph_U(Re^{iπ/6}) ≥ R³/4`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtSd

/-- The segment point `w(t) = R d6 + t (R - R d6)`. -/
noncomputable def segPt (R t : ℝ) : ℂ := (R : ℂ) * d6 + (t : ℂ) * ((R : ℂ) - (R : ℂ) * d6)

lemma segPt_re (R t : ℝ) : (segPt R t).re = R * (Real.sqrt 3 / 2 + t * (1 - Real.sqrt 3 / 2)) := by
  unfold segPt
  simp [Complex.mul_re, d6_re, d6_im]
  ring

lemma segPt_im (R t : ℝ) : (segPt R t).im = R * ((1 - t) / 2) := by
  unfold segPt
  simp [Complex.mul_im, d6_re, d6_im]
  ring

lemma sqrt3_bounds : 1.7 < Real.sqrt 3 ∧ Real.sqrt 3 < 1.8 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

section seg

variable {R t : ℝ} (hR : 0 ≤ R) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
include hR ht0 ht1

lemma segPt_re_ge : (Real.sqrt 3 / 2) * R ≤ (segPt R t).re := by
  rw [segPt_re]
  have := sqrt3_bounds
  nlinarith [mul_nonneg hR ht0, mul_nonneg (mul_nonneg hR ht0) (sub_nonneg.2 ht1)]

lemma segPt_re_le : (segPt R t).re ≤ R := by
  rw [segPt_re]
  have := sqrt3_bounds
  nlinarith [mul_nonneg hR (sub_nonneg.2 ht1), mul_nonneg hR ht0]

lemma segPt_im_nonneg : 0 ≤ (segPt R t).im := by
  rw [segPt_im]; exact mul_nonneg hR (by linarith)

lemma segPt_im_le : (segPt R t).im ≤ R / 2 := by
  rw [segPt_im]; nlinarith [mul_nonneg hR ht0]

lemma norm_segPt_le : ‖segPt R t‖ ≤ R := by
  have hs : ‖segPt R t‖ ^ 2 = (segPt R t).re ^ 2 + (segPt R t).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have key : (segPt R t).re ^ 2 + (segPt R t).im ^ 2 - R ^ 2
      = -(R ^ 2 * (2 - Real.sqrt 3) * (t * (1 - t))) := by
    rw [segPt_re, segPt_im]
    linear_combination (R ^ 2 * (1 - t) ^ 2 / 4) * sqrt3_sq
  have h2 : 0 ≤ R ^ 2 * (2 - Real.sqrt 3) * (t * (1 - t)) := by
    have := sqrt3_bounds
    exact mul_nonneg (mul_nonneg (sq_nonneg R) (by linarith)) (mul_nonneg ht0 (sub_nonneg.2 ht1))
  have : ‖segPt R t‖ ^ 2 ≤ R ^ 2 := by linarith
  exact (abs_le_of_sq_le_sq' this hR).2

lemma norm_segPt_ge : (Real.sqrt 3 / 2) * R ≤ ‖segPt R t‖ :=
  (segPt_re_ge hR ht0 ht1).trans (Complex.re_le_norm _)

lemma segPt_ne_zero (hR' : 0 < R) : segPt R t ≠ 0 := by
  intro h
  have := norm_segPt_ge hR ht0 ht1
  rw [h, norm_zero] at this
  have := sqrt3_bounds
  nlinarith

lemma re_segPt_sq_ge : R ^ 2 / 2 ≤ ((segPt R t) ^ 2).re := by
  have h0 := segPt_re_ge hR ht0 ht1
  have hi := segPt_im_nonneg hR ht0 ht1
  have hi2 := segPt_im_le hR ht0 ht1
  have hs := sqrt3_bounds
  have hre : ((segPt R t) ^ 2).re = (segPt R t).re ^ 2 - (segPt R t).im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  rw [hre]
  have hsq : (Real.sqrt 3 / 2) ^ 2 * R ^ 2 ≤ (segPt R t).re ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h0 2
  have : (3 / 4) * R ^ 2 ≤ (segPt R t).re ^ 2 := by
    have : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, sqrt3_sq]; norm_num
    rw [this] at hsq; exact hsq
  have h2 : (segPt R t).im ^ 2 ≤ R ^ 2 / 4 := by nlinarith
  nlinarith

lemma im_PhU_segPt {U : ℝ} (hU : kap * |U| ≤ R ^ 2 / 16) :
    R / 2 * (29 * R ^ 2 / 48) * (1 - t) ≤ (PhU U (segPt R t)).im := by
  have hre := segPt_re_ge hR ht0 ht1
  have him := segPt_im_le hR ht0 ht1
  have him0 := segPt_im_nonneg hR ht0 ht1
  have hs := sqrt3_bounds
  have hq := sqrt3_sq
  have hkU : -(R ^ 2 / 16) ≤ kap * U := by
    have := neg_abs_le U
    have hk := kap_pos
    nlinarith [abs_nonneg U]
  have hre2 : 3 * R ^ 2 / 4 ≤ (segPt R t).re ^ 2 := by
    have h1 : (Real.sqrt 3 / 2) ^ 2 * R ^ 2 ≤ (segPt R t).re ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hre 2
    have : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, hq]; norm_num
    rw [this] at h1; linarith
  have him2 : (segPt R t).im ^ 2 ≤ R ^ 2 / 4 := by nlinarith
  have : (PhU U (segPt R t)).im = (segPt R t).im * (kap * U + (segPt R t).re ^ 2 - (segPt R t).im ^ 2 / 3) := by
    unfold PhU
    simp [Complex.mul_im, Complex.div_ofNat_im, pow_succ, Complex.mul_re]
    ring
  rw [this]
  have hbr : 29 * R ^ 2 / 48 ≤ kap * U + (segPt R t).re ^ 2 - (segPt R t).im ^ 2 / 3 := by nlinarith
  have himl : R / 2 * (1 - t) ≤ (segPt R t).im := by rw [segPt_im]; nlinarith
  have h29 : 0 ≤ 29 * R ^ 2 / 48 := by positivity
  calc R / 2 * (29 * R ^ 2 / 48) * (1 - t) = R / 2 * (1 - t) * (29 * R ^ 2 / 48) := by ring
    _ ≤ (segPt R t).im * (kap * U + (segPt R t).re ^ 2 - (segPt R t).im ^ 2 / 3) :=
      mul_le_mul himl hbr h29 him0

lemma im_PhU_segPt_nonneg {U : ℝ} (hU : kap * |U| ≤ R ^ 2 / 16) : 0 ≤ (PhU U (segPt R t)).im :=
  le_trans (by have : 0 ≤ 1 - t := by linarith
               positivity) (im_PhU_segPt hR ht0 ht1 hU)

lemma norm_G_segPt_ge {U : ℝ} (hU : kap * |U| ≤ R ^ 2 / 16) : R ^ 2 / 4 ≤ ‖(kap : ℂ) * U + segPt R t ^ 2‖ := by
  have h := re_segPt_sq_ge hR ht0 ht1
  have hkU : -(R ^ 2 / 16) ≤ kap * U := by
    have := neg_abs_le U
    have hk := kap_pos
    nlinarith [abs_nonneg U]
  refine le_trans ?_ (Complex.re_le_norm _)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith

lemma norm_G_segPt_le {U : ℝ} (hU : kap * |U| ≤ R ^ 2 / 16) : ‖(kap : ℂ) * U + segPt R t ^ 2‖ ≤ 2 * R ^ 2 := by
  have hn := norm_segPt_le hR ht0 ht1
  have hk := kap_pos
  have h1 : ‖(kap : ℂ) * U‖ = kap * |U| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hk]
  calc ‖(kap : ℂ) * U + segPt R t ^ 2‖ ≤ ‖(kap : ℂ) * U‖ + ‖segPt R t ^ 2‖ := norm_add_le _ _
    _ ≤ R ^ 2 / 16 + R ^ 2 := by
      rw [h1, norm_pow]
      have : ‖segPt R t‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      linarith
    _ ≤ 2 * R ^ 2 := by nlinarith [sq_nonneg R]

end seg

end FormalResearch.SignUncertainty.CtSd
