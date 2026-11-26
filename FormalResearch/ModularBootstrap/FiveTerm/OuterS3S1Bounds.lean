module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterPL
public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3Ext
public import FormalResearch.Complex.HadamardCauchy

/-!
# FIVE-S, S3 (step 4a): `δ`-independent S1 bounds on `bandUpper (1/16)`

Proves the `δ`-independent two-sided modulus bounds and `C²` log-derivative bounds on `bandUpper (1/16)`
needed for `EsmExt δ` in `OuterS3`:

* `exp_hbarA_aRest_mul_one_add_sq_bounds`: `c ≤ ‖exp(hbarA aRest s) * (1 + sTan s ^ 2)‖ ≤ C` on `unitStripCl`
  via `pl_unit_strip` (`OuterPL`).
* `norm_exp_logGhatLower_bounds`: `c ≤ ‖exp(logGhatLower b)‖ ≤ C` on `bandUpper (3/32) ∩ {b.im ≤ 1/2}`.
* `norm_uE_le`: `‖uE w‖ ≤ M` on `{|Im w| ≤ 3/32}`.
* `abs_re_logGhatRefl_le` and `norm_deriv_logGhatRefl_le`: `|(logGhatRefl b).re| ≤ M` on `bandUpper (3/32)` and
  `‖deriv logGhatRefl b‖ + ‖deriv (deriv logGhatRefl) b‖ ≤ C` on `bandUpper (1/16)` via `Complex.borelCaratheodory`
  and `Hadamard.norm_iteratedDeriv_le_ball`.
* `norm_one_add_zetaD_sq_sq_bounds`, `norm_logDeriv_one_add_zetaD_sq_sq_le`: `‖(1 + ζ_D b²)²‖ ≍ e^{-2π|Re b|}` and
  bounded first/second log-derivatives on `bandUpper (1/16)`.
* `norm_R4cStrip_bounds`, `norm_logDeriv_R4cStrip_le`: `‖R4cStrip b‖ ≍ (1 + |Re b|)^{1/2}` and bounded
  first/second log-derivatives on `bandUpper (1/16)`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.Complex
open FormalResearch.Hadamard
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-! ### 1. `exp(hbarA aRest s) * (1 + sTan s ^ 2)` on `unitStripCl` and `logGhatLower` -/

private lemma aRest_ge_linear (t : ℝ) : (π / 2) * |t| - (13 / 4) * Real.log 2 ≤ aRest t := by
  unfold aRest
  have hpi := Real.pi_pos
  have h4 : 0 ≤ Real.log (lamT t) := Real.log_nonneg (one_le_lamT t)
  have h5 := le_log_cosh (π * t / 4)
  have h6 := le_log_cosh (π * t / 2)
  have h7 := log_cosh_le (π * t)
  have e5 : |π * t / 4| = π * |t| / 4 := by rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num
  have e6 : |π * t / 2| = π * |t| / 2 := by rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num
  have e7 : |π * t| = π * |t| := by rw [abs_mul, abs_of_pos hpi]
  rw [e5] at h5; rw [e6] at h6; rw [e7] at h7
  nlinarith [abs_nonneg t]

private lemma norm_cos_sq_le_cosh (s : ℂ) :
    ‖Complex.cos ((π : ℂ) * s / 4)‖ ^ 2 ≤ Real.cosh (π * s.im / 2) := by
  rw [norm_cos_sq', re_pi_mul_div_four, im_pi_mul_div_four]
  have h1 : Real.cos (π * s.re / 4) ^ 2 ≤ 1 := Real.cos_sq_le_one _
  have h2 : Real.cosh (π * s.im / 2) = 1 + 2 * Real.sinh (π * s.im / 4) ^ 2 := by
    have := Real.cosh_two_mul (π * s.im / 4)
    rw [show 2 * (π * s.im / 4) = π * s.im / 2 by ring] at this
    rw [this, Real.cosh_sq]; ring
  nlinarith [sq_nonneg (Real.sinh (π * s.im / 4))]

private lemma norm_one_add_sTan_sq_ge {s : ℂ} (hs : s ∈ unitStripCl) :
    Real.exp (-(π * |s.im| / 2)) ≤ ‖1 + sTan s ^ 2‖ := by
  rw [norm_one_add_sTan_sq hs, Real.exp_neg]
  have h1 := norm_cos_sq_le_cosh s
  have h2 : Real.cosh (π * s.im / 2) ≤ Real.exp (π * |s.im| / 2) := by
    rw [Real.cosh_eq]
    have ha : π * s.im / 2 ≤ π * |s.im| / 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self s.im) Real.pi_pos.le) (by norm_num)
    have hb : -(π * s.im / 2) ≤ π * |s.im| / 2 := by
      nlinarith [neg_le_abs s.im, Real.pi_pos]
    linarith [Real.exp_le_exp.mpr ha, Real.exp_le_exp.mpr hb]
  have hpos : 0 < ‖Complex.cos ((π : ℂ) * s / 4)‖ ^ 2 := by
    have := cos_ne_zero_of_cl hs; positivity
  exact inv_anti₀ hpos (h1.trans h2)

lemma exp_hbarA_aRest_mul_one_add_sq_bounds :
    ∃ c C : ℝ, 0 < c ∧ ∀ s ∈ unitStripCl,
      c ≤ ‖Complex.exp (hbarA aRest s) * (1 + sTan s ^ 2)‖ ∧
      ‖Complex.exp (hbarA aRest s) * (1 + sTan s ^ 2)‖ ≤ C := by
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  have h1e : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
    rw [sub_pos, Real.exp_lt_one_iff]; nlinarith
  set β : ℝ := (1 / 2) * Real.log 2 - 2 * Real.log (1 - Real.exp (-(4 * π * xiStar))) with hβdef
  set c0 : ℝ := Real.exp (-((13 / 4) * Real.log 2)) with hc0
  set C0 : ℝ := 4 * Real.exp β with hC0
  have hc0_pos : 0 < c0 := Real.exp_pos _
  have hC0_pos : 0 < C0 := by positivity
  obtain ⟨κ, hκ⟩ := re_hbarA_le amp_aRest (α := π / 2) (β := β) (by positivity) (fun t => aRest_le t)
  have hm_ge : ∀ s ∈ closedStrip, -((13 / 4) * Real.log 2) ≤ (hbarA aRest s).re :=
    fun s hs => re_hbarA_ge amp_aRest aRest_ge hs
  have hd_sTan : DifferentiableOn ℂ (fun s => 1 + sTan s ^ 2) unitStrip :=
    (differentiableOn_sTan.mono unitStrip_subset_cl).pow 2 |>.const_add 1
  have hc_sTan : ContinuousOn (fun s => 1 + sTan s ^ 2) unitStripCl :=
    continuousOn_const.add (differentiableOn_sTan.continuousOn.pow 2)
  have hne_sTan : ∀ s ∈ unitStripCl, 1 + sTan s ^ 2 ≠ 0 := fun s hs => by
    rw [one_add_sTan_sq hs]; exact inv_ne_zero (pow_ne_zero 2 (cos_ne_zero_of_cl hs))
  have hd_E : DifferentiableOn ℂ (fun s => Complex.exp (hbarA aRest s)) unitStrip :=
    (differentiableOn_hbarA_strip amp_aRest).cexp
  have hc_E : ContinuousOn (fun s => Complex.exp (hbarA aRest s)) unitStripCl :=
    (continuousOn_hbarA amp_aRest).mono (fun s (hs : s ∈ unitStripCl) => ⟨by linarith [hs.1], hs.2⟩) |>.cexp
  have hne_E : ∀ s ∈ unitStripCl, Complex.exp (hbarA aRest s) ≠ 0 := fun _ _ => Complex.exp_ne_zero _
  have h_upper : ∀ s ∈ unitStripCl, ‖(C0 : ℂ)⁻¹ * (Complex.exp (hbarA aRest s) * (1 + sTan s ^ 2))‖ ≤ 1 := by
    refine pl_unit_strip (a := π / 2 + π / 2)
      (b := |β + (π / 2) * κ| + Real.log 4 + |Real.log C0|)
      (hd_E.mul hd_sTan |>.const_mul _)
      (hc_E.mul hc_sTan |>.const_mul _)
      (by positivity) ?_ ?_ ?_
    · intro s hs _
      have hscl : s ∈ closedStrip := ⟨le_trans (by norm_num) hs.1.le, hs.2.le⟩
      have hre := hκ s hscl
      have hsq := norm_one_add_sTan_sq_le (unitStrip_subset_cl hs)
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC0_pos,
        Complex.norm_exp]
      have h1 : Real.exp (hbarA aRest s).re * ‖1 + sTan s ^ 2‖ ≤
          Real.exp ((π / 2) * |s.im| + (β + (π / 2) * κ)) * (4 * Real.exp (-(π * |s.im| / 2))) :=
        mul_le_mul (Real.exp_le_exp.mpr (by linarith [hre])) hsq (norm_nonneg _) (Real.exp_pos _).le
      have h2 : C0⁻¹ * (Real.exp ((π / 2) * |s.im| + (β + (π / 2) * κ)) * (4 * Real.exp (-(π * |s.im| / 2)))) ≤
          Real.exp ((π / 2 + π / 2) * |s.im| + (|β + (π / 2) * κ| + Real.log 4 + |Real.log C0|)) := by
        have hlC := Real.exp_log hC0_pos
        have hl4 := Real.exp_log (by norm_num : (0 : ℝ) < 4)
        nth_rw 1 [← hlC]
        nth_rw 1 [← hl4]
        rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : 0 ≤ π / 2 * |s.im| := by positivity
        linarith [le_abs_self (β + π / 2 * κ), neg_abs_le (Real.log C0)]
      exact (mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hC0_pos.le)).trans h2
    · intro t
      have hmem : (t : ℂ) * Complex.I ∈ unitStripCl := ⟨by simp, by simp⟩
      have hre : (hbarA aRest ((t : ℂ) * Complex.I)).re = aRest t := by
        rw [mul_comm]; exact re_hbarA_left amp_aRest t
      have hsq := norm_one_add_sTan_sq_le hmem
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
        Complex.I_re, mul_zero, add_zero] at hsq
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC0_pos,
        Complex.norm_exp, hre]
      have ha := aRest_le t
      have h3 : Real.exp (aRest t) * ‖1 + sTan ((t : ℂ) * Complex.I) ^ 2‖ ≤
          Real.exp ((π / 2) * |t| + β) * (4 * Real.exp (-(π * |t| / 2))) :=
        mul_le_mul (Real.exp_le_exp.mpr ha) hsq (norm_nonneg _) (Real.exp_pos _).le
      have h4 : Real.exp ((π / 2) * |t| + β) * (4 * Real.exp (-(π * |t| / 2))) = C0 := by
        rw [hC0, show (π / 2) * |t| + β = β + (π * |t| / 2) by ring, Real.exp_add]
        calc Real.exp β * Real.exp (π * |t| / 2) * (4 * Real.exp (-(π * |t| / 2)))
            = 4 * Real.exp β * (Real.exp (π * |t| / 2) * Real.exp (-(π * |t| / 2))) := by ring
          _ = 4 * Real.exp β * 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
          _ = 4 * Real.exp β := mul_one _
      rw [h4] at h3
      rw [inv_mul_le_one₀ hC0_pos]; exact h3
    · intro t
      have hmem : 1 + (t : ℂ) * Complex.I ∈ unitStripCl := ⟨by simp, by simp⟩
      have hre : (hbarA aRest (1 + (t : ℂ) * Complex.I)).re = aRest t := by
        rw [mul_comm]; exact re_hbarA_right amp_aRest t
      have hsq := norm_one_add_sTan_sq_le hmem
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add] at hsq
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC0_pos,
        Complex.norm_exp, hre]
      have ha := aRest_le t
      have h3 : Real.exp (aRest t) * ‖1 + sTan (1 + (t : ℂ) * Complex.I) ^ 2‖ ≤
          Real.exp ((π / 2) * |t| + β) * (4 * Real.exp (-(π * |t| / 2))) :=
        mul_le_mul (Real.exp_le_exp.mpr ha) hsq (norm_nonneg _) (Real.exp_pos _).le
      have h4 : Real.exp ((π / 2) * |t| + β) * (4 * Real.exp (-(π * |t| / 2))) = C0 := by
        rw [hC0, show (π / 2) * |t| + β = β + (π * |t| / 2) by ring, Real.exp_add]
        calc Real.exp β * Real.exp (π * |t| / 2) * (4 * Real.exp (-(π * |t| / 2)))
            = 4 * Real.exp β * (Real.exp (π * |t| / 2) * Real.exp (-(π * |t| / 2))) := by ring
          _ = 4 * Real.exp β * 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
          _ = 4 * Real.exp β := mul_one _
      rw [h4] at h3
      rw [inv_mul_le_one₀ hC0_pos]; exact h3
  have h_lower : ∀ s ∈ unitStripCl, ‖(c0 : ℂ) * (Complex.exp (hbarA aRest s) * (1 + sTan s ^ 2))⁻¹‖ ≤ 1 := by
    refine pl_unit_strip (a := π / 2) (b := (13 / 4) * Real.log 2 + |Real.log c0|)
      ((hd_E.mul hd_sTan).inv (fun s hs => mul_ne_zero (hne_E s (unitStrip_subset_cl hs))
        (hne_sTan s (unitStrip_subset_cl hs))) |>.const_mul _)
      ((hc_E.mul hc_sTan).inv₀ (fun s hs => mul_ne_zero (hne_E s hs) (hne_sTan s hs)) |>.const_mul _)
      (by positivity) ?_ ?_ ?_
    · intro s hs _
      have hscl : s ∈ closedStrip := ⟨le_trans (by norm_num) hs.1.le, hs.2.le⟩
      have hre := hm_ge s hscl
      have hsq := norm_one_add_sTan_sq_ge (unitStrip_subset_cl hs)
      rw [norm_mul, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0_pos,
        Complex.norm_exp, mul_inv]
      have hE_inv : (Real.exp (hbarA aRest s).re)⁻¹ ≤ Real.exp ((13 / 4) * Real.log 2) := by
        rw [← Real.exp_neg]; exact Real.exp_le_exp.mpr (by linarith)
      have hS_inv : ‖1 + sTan s ^ 2‖⁻¹ ≤ Real.exp (π * |s.im| / 2) := by
        rw [Real.exp_neg] at hsq
        have := inv_anti₀ (inv_pos.mpr (Real.exp_pos _)) hsq
        rwa [inv_inv] at this
      have h1 : (Real.exp (hbarA aRest s).re)⁻¹ * ‖1 + sTan s ^ 2‖⁻¹ ≤
          Real.exp ((13 / 4) * Real.log 2) * Real.exp (π * |s.im| / 2) :=
        mul_le_mul hE_inv hS_inv (inv_nonneg.mpr (norm_nonneg _)) (Real.exp_pos _).le
      calc c0 * ((Real.exp (hbarA aRest s).re)⁻¹ * ‖1 + sTan s ^ 2‖⁻¹)
          ≤ c0 * (Real.exp ((13 / 4) * Real.log 2) * Real.exp (π * |s.im| / 2)) :=
            mul_le_mul_of_nonneg_left h1 hc0_pos.le
        _ ≤ Real.exp (π / 2 * |s.im| + ((13 / 4) * Real.log 2 + |Real.log c0|)) := by
            have hlog := Real.exp_log hc0_pos
            nth_rw 1 [← hlog]
            rw [← Real.exp_add, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            linarith [le_abs_self (Real.log c0)]
    · intro t
      have hmem : (t : ℂ) * Complex.I ∈ unitStripCl := ⟨by simp, by simp⟩
      have hre : (hbarA aRest ((t : ℂ) * Complex.I)).re = aRest t := by
        rw [mul_comm]; exact re_hbarA_left amp_aRest t
      have hsq := norm_one_add_sTan_sq_ge hmem
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
        Complex.I_re, mul_zero, add_zero] at hsq
      rw [norm_mul, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0_pos,
        Complex.norm_exp, hre]
      have hprod : c0 ≤ Real.exp (aRest t) * ‖1 + sTan ((t : ℂ) * Complex.I) ^ 2‖ := by
        have ha := aRest_ge_linear t
        calc c0 = Real.exp ((π / 2) * |t| - (13 / 4) * Real.log 2) * Real.exp (-(π * |t| / 2)) := by
              rw [hc0, ← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (aRest t) * ‖1 + sTan ((t : ℂ) * Complex.I) ^ 2‖ := by
              gcongr
      rw [← div_eq_mul_inv, div_le_one (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (hne_sTan _ hmem)))]
      exact hprod
    · intro t
      have hmem : 1 + (t : ℂ) * Complex.I ∈ unitStripCl := ⟨by simp, by simp⟩
      have hre : (hbarA aRest (1 + (t : ℂ) * Complex.I)).re = aRest t := by
        rw [mul_comm]; exact re_hbarA_right amp_aRest t
      have hsq := norm_one_add_sTan_sq_ge hmem
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add] at hsq
      rw [norm_mul, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0_pos,
        Complex.norm_exp, hre]
      have hprod : c0 ≤ Real.exp (aRest t) * ‖1 + sTan (1 + (t : ℂ) * Complex.I) ^ 2‖ := by
        have ha := aRest_ge_linear t
        calc c0 = Real.exp ((π / 2) * |t| - (13 / 4) * Real.log 2) * Real.exp (-(π * |t| / 2)) := by
              rw [hc0, ← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (aRest t) * ‖1 + sTan (1 + (t : ℂ) * Complex.I) ^ 2‖ := by
              gcongr
      rw [← div_eq_mul_inv, div_le_one (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (hne_sTan _ hmem)))]
      exact hprod
  refine ⟨c0, C0, hc0_pos, fun s hs => ⟨?_, ?_⟩⟩
  · have h := h_lower s hs
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0_pos,
      ← div_eq_mul_inv] at h
    rwa [div_le_one (norm_pos_iff.mpr (mul_ne_zero (Complex.exp_ne_zero _) (hne_sTan s hs)))] at h
  · have h := h_upper s hs
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC0_pos,
      inv_mul_le_one₀ hC0_pos] at h
    exact h

private lemma exp_logGhatLower_eq' {b : ℂ} (hb : b ∈ bandUpper (1 / 8)) (hb_lt : b.im < 1 / 2) :
    Complex.exp (logGhatLower b) = (1 - zetaD b) ^ (-(1 / 2 : ℂ)) * Gtilde R4c (zetaD b) := by
  have hb_strip : b ∈ imStrip :=
    ⟨by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 8 from hb)).1],
     by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 8 from hb)).2]⟩
  have hb_q : b ∈ bandUpper (1 / 4) := lt_trans (show |b.im - 1 / 2| < 1 / 8 from hb) (by norm_num)
  have hzeta_hd : zetaD b ∈ halfDisc := zetaD_mem_halfDisc hb_strip.1 hb_lt
  have hcl : zetaD b ∈ closure halfDisc := subset_closure hzeta_hd
  have h1sq_ne : 1 + zetaD b ^ 2 ≠ 0 := one_add_zetaD_sq_ne_zero_imStrip hb_strip
  have h1z_ne : 1 + zetaD b ≠ 0 := one_add_ne_zero' hcl
  have hq_ne : qBd (zetaD b) ≠ 0 := qBd_ne_zero (halfDisc_mem_diff hzeta_hd)
  have hkap_ne : (kap : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr kap_pos.ne'
  have hr1_ne : (1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2) ≠ 0 :=
    Complex.slitPlane_ne_zero (r4c_alg_factor_mem_slitPlane hb_q)
  have hr2_ne : (π : ℂ) * b / Complex.sinh ((π : ℂ) * b) ≠ 0 :=
    Complex.slitPlane_ne_zero (pi_mul_div_sinh_mem_slitPlane hb_strip)
  have h1sub_ne : 1 - zetaD b ≠ 0 :=
    Complex.slitPlane_ne_zero (one_sub_mem_slit hcl (halfDisc_ne_special hzeta_hd).2.2)
  unfold logGhatLower
  rw [Complex.exp_add, Complex.exp_sub, Complex.exp_sub, Complex.exp_sub, Complex.exp_sub, Complex.exp_add]
  rw [Complex.exp_log h1sq_ne, Complex.exp_log hkap_ne]
  have he_1z : Complex.exp (2 * Complex.log (1 + zetaD b)) = (1 + zetaD b) ^ 2 := by
    rw [show (2 : ℂ) * Complex.log (1 + zetaD b) = Complex.log (1 + zetaD b) + Complex.log (1 + zetaD b) by ring,
      Complex.exp_add, Complex.exp_log h1z_ne, sq]
  have he_q : (Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))))⁻¹ = (qBd (zetaD b)) ^ (-(1 / 4 : ℂ)) := by
    rw [← Complex.exp_neg, Complex.cpow_def_of_ne_zero hq_ne]; congr 1; ring
  have he_r1 : Complex.exp ((1 / 2 : ℂ) * Complex.log ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2))) =
      ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hr1_ne]; congr 1; ring
  have he_r2 : Complex.exp ((1 / 2 : ℂ) * Complex.log ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b))) =
      ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hr2_ne]; congr 1; ring
  rw [he_1z, he_r1, he_r2]
  have hcancel : (1 - zetaD b) ^ (-(1 / 2 : ℂ)) * (1 - zetaD b) ^ (1 / 2 : ℂ) = 1 := by
    rw [Complex.cpow_def_of_ne_zero h1sub_ne, Complex.cpow_def_of_ne_zero h1sub_ne, ← Complex.exp_add]
    simp
  unfold Gtilde Gout
  rw [← R4cStrip_eq_R4c hb_q hb_lt]
  unfold R4cStrip
  have hR1_ne : ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hr1_ne]; exact Complex.exp_ne_zero _
  have hR2_ne : ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hr2_ne]; exact Complex.exp_ne_zero _
  have hq_exp_ne : Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))) ≠ 0 := Complex.exp_ne_zero _
  have h1z2_ne : (1 + zetaD b) ^ 2 ≠ 0 := pow_ne_zero 2 h1z_ne
  rw [← he_q]
  have hprod : (1 - zetaD b) ^ (-(1 / 2 : ℂ)) *
      ((1 + zetaD b ^ 2) * (Complex.exp (hbarA aAmp (sInv (zetaD b))) * (1 - zetaD b) ^ (1 / 2 : ℂ) /
        (1 + zetaD b) ^ 2 * (Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))))⁻¹) /
        (((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) *
          ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) / (kap : ℂ))) =
      ((1 - zetaD b) ^ (-(1 / 2 : ℂ)) * (1 - zetaD b) ^ (1 / 2 : ℂ)) *
      (Complex.exp (hbarA aAmp (sInv (zetaD b))) * (1 + zetaD b ^ 2) / (1 + zetaD b) ^ 2 /
        Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))) /
        ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) /
        ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) * (kap : ℂ)) := by
    field_simp
  rw [hprod, hcancel, one_mul]

lemma norm_exp_logGhatLower_bounds_lt :
    ∃ c C : ℝ, 0 < c ∧ ∀ b ∈ bandUpper (3 / 32), b.im < 1 / 2 →
      c ≤ ‖Complex.exp (logGhatLower b)‖ ∧ ‖Complex.exp (logGhatLower b)‖ ≤ C := by
  obtain ⟨c0, C0, hc0_pos, hbd⟩ := exp_hbarA_aRest_mul_one_add_sq_bounds
  refine ⟨c0 / 4, C0, by positivity, fun w hw hw_lt => ?_⟩
  have hw8 : w ∈ bandUpper (1 / 8) := lt_trans (show |w.im - 1 / 2| < 3 / 32 from hw) (by norm_num)
  have hw_strip : w ∈ imStrip :=
    ⟨by linarith [(abs_lt.mp (show |w.im - 1 / 2| < 1 / 8 from hw8)).1],
     by linarith [(abs_lt.mp (show |w.im - 1 / 2| < 1 / 8 from hw8)).2]⟩
  have hz : zetaD w ∈ halfDisc := zetaD_mem_halfDisc hw_strip.1 hw_lt
  have hs : sInv (zetaD w) ∈ unitStrip := sInv_mem_strip hz
  have hscl : sInv (zetaD w) ∈ unitStripCl := unitStrip_subset_cl hs
  have hstan : sTan (sInv (zetaD w)) = zetaD w :=
    sTan_sInv (halfDisc_ne_pm_I hz).1 (halfDisc_ne_pm_I hz).2
  have hexp_eq := exp_logGhatLower_eq' hw8 hw_lt
  have h4 : Complex.exp ((4 : ℂ) * Hxb (sInv (zetaD w))) = Kfun (sInv (zetaD w)) := by
    rw [exp_four_Hxb hscl, Kb_of_mem hs]
  have hnorm_Hxb : ‖Complex.exp (Hxb (sInv (zetaD w)))‖ ^ 4 = ‖Kfun (sInv (zetaD w))‖ := by
    rw [← norm_pow, ← Complex.exp_nat_mul, show ((4 : ℕ) : ℂ) * Hxb (sInv (zetaD w)) =
      (4 : ℂ) * Hxb (sInv (zetaD w)) by norm_cast, h4]
  have hK_eq : Kfun (sInv (zetaD w)) = qHat (zetaD w) * H3 (zetaD w) := by
    rw [Kfun_eq_qHat hs, hstan]
    unfold H3 gS
    have hu : Complex.cos ((π : ℂ) * sInv (zetaD w)) = uC (zetaD w) :=
      calc Complex.cos ((π : ℂ) * sInv (zetaD w)) = cC (sInv (zetaD w)) := rfl
        _ = uC (sTan (sInv (zetaD w))) := (uC_sTan hscl).symm
        _ = uC (zetaD w) := by rw [hstan]
    rw [hu]
    ring
  have hnorm_K : ‖Kfun (sInv (zetaD w))‖ = ‖qHat (zetaD w)‖ * ‖R4c (zetaD w)‖ ^ 4 := by
    rw [hK_eq, norm_mul, ← R4c_pow_four (z := zetaD w), norm_pow]
  have hR4_pos : 0 < ‖R4c (zetaD w)‖ := norm_pos_iff.mpr (R4c_ne_zero hz)
  have hq_pos : 0 < ‖qHat (zetaD w)‖ :=
    norm_pos_iff.mpr (Complex.slitPlane_ne_zero (qHat_mem_slit hz))
  have hnorm_Hxb' : ‖Complex.exp (Hxb (sInv (zetaD w)))‖ = ‖qHat (zetaD w)‖ ^ (1 / 4 : ℝ) * ‖R4c (zetaD w)‖ := by
    have hpow_eq : ‖Complex.exp (Hxb (sInv (zetaD w)))‖ ^ 4 = (‖qHat (zetaD w)‖ ^ (1 / 4 : ℝ) * ‖R4c (zetaD w)‖) ^ 4 := by
      rw [hnorm_Hxb, hnorm_K, mul_pow, ← Real.rpow_natCast (‖qHat (zetaD w)‖ ^ (1 / 4 : ℝ)) 4,
        ← Real.rpow_mul hq_pos.le]
      norm_num
    exact le_antisymm
      (le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) hpow_eq.le)
      (le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (norm_nonneg _) hpow_eq.symm.le)
  have hA_split : Complex.exp (hbarA aAmp (sInv (zetaD w))) =
      Complex.exp (Hxb (sInv (zetaD w))) * Complex.exp (hbarA aRest (sInv (zetaD w))) := by
    rw [← Complex.exp_add]; congr 1; unfold Hxb; ring
  have h1sub_ne : 1 - zetaD w ≠ 0 :=
    Complex.slitPlane_ne_zero (one_sub_mem_slit (subset_closure hz) (halfDisc_ne_special hz).2.2)
  have h1sub_cancel : ‖(1 - zetaD w) ^ (-(1 / 2 : ℂ))‖ * ‖(1 - zetaD w) ^ (1 / 2 : ℂ)‖ = 1 := by
    rw [← norm_mul, Complex.cpow_def_of_ne_zero h1sub_ne, Complex.cpow_def_of_ne_zero h1sub_ne,
      ← Complex.exp_add]
    simp
  have hq_cancel : ‖qHat (zetaD w)‖ ^ (1 / 4 : ℝ) * ‖(qBd (zetaD w)) ^ (-(1 / 4 : ℂ))‖ = 1 := by
    have hq_ne : qHat (zetaD w) ≠ 0 := Complex.slitPlane_ne_zero (qHat_mem_slit hz)
    rw [qBd_of_mem hz, Complex.cpow_def_of_ne_zero hq_ne, Complex.norm_exp]
    have hre_q : (Complex.log (qHat (zetaD w)) * (-(1 / 4 : ℂ))).re =
        -(1 / 4 : ℝ) * Real.log ‖qHat (zetaD w)‖ := by
      simp [Complex.mul_re, Complex.log_re]; ring
    rw [hre_q, Real.rpow_def_of_pos hq_pos, ← Real.exp_add]
    ring_nf; simp
  have hnorm_full : ‖Complex.exp (logGhatLower w)‖ =
      ‖Complex.exp (hbarA aRest (sInv (zetaD w))) * (1 + zetaD w ^ 2)‖ / ‖1 + zetaD w‖ ^ 2 := by
    rw [hexp_eq]
    unfold Gtilde Gout
    rw [hA_split, norm_mul, norm_div, norm_mul, norm_mul, norm_div, norm_mul, norm_mul,
      norm_pow, hnorm_Hxb', norm_mul (Complex.exp (hbarA aRest (sInv (zetaD w))))]
    calc ‖(1 - zetaD w) ^ (-(1 / 2 : ℂ))‖ *
          (‖1 + zetaD w ^ 2‖ *
            (‖qHat (zetaD w)‖ ^ (1 / 4 : ℝ) * ‖R4c (zetaD w)‖ * ‖Complex.exp (hbarA aRest (sInv (zetaD w)))‖ *
              ‖(1 - zetaD w) ^ (1 / 2 : ℂ)‖ / ‖1 + zetaD w‖ ^ 2 * ‖qBd (zetaD w) ^ (-(1 / 4 : ℂ))‖) /
            ‖R4c (zetaD w)‖)
        = (‖(1 - zetaD w) ^ (-(1 / 2 : ℂ))‖ * ‖(1 - zetaD w) ^ (1 / 2 : ℂ)‖) *
            (‖qHat (zetaD w)‖ ^ (1 / 4 : ℝ) * ‖qBd (zetaD w) ^ (-(1 / 4 : ℂ))‖) *
            (‖Complex.exp (hbarA aRest (sInv (zetaD w)))‖ * ‖1 + zetaD w ^ 2‖ / ‖1 + zetaD w‖ ^ 2) := by
          field_simp [hR4_pos.ne']
      _ = _ := by rw [h1sub_cancel, hq_cancel, one_mul, one_mul]
  rw [hnorm_full]
  obtain ⟨hb_lo, hb_hi⟩ := hbd (sInv (zetaD w)) hscl
  rw [hstan] at hb_lo hb_hi
  have hd1 : 1 ≤ ‖1 + zetaD w‖ ^ 2 := by
    have := one_le_norm_one_add (subset_closure hz); nlinarith
  have hd2 : ‖1 + zetaD w‖ ^ 2 ≤ 4 := by
    have := norm_one_add_le (subset_closure hz); nlinarith [norm_nonneg (1 + zetaD w)]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · calc ‖Complex.exp (hbarA aRest (sInv (zetaD w))) * (1 + zetaD w ^ 2)‖ /
          ‖1 + zetaD w‖ ^ 2
        ≤ ‖Complex.exp (hbarA aRest (sInv (zetaD w))) * (1 + zetaD w ^ 2)‖ / 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hd1
      _ = ‖Complex.exp (hbarA aRest (sInv (zetaD w))) * (1 + zetaD w ^ 2)‖ := div_one _
      _ ≤ C0 := hb_hi

/-! ### 2. Uniform bound on `uE` and Borel-Carathéodory + Cauchy estimates for `logGhatRefl` -/

private lemma cos_three_pi_32_pos : 0 < Real.cos (3 * π / 32) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

private lemma re_one_add_cosh_sq_ge {w : ℂ} (hw : |w.im| ≤ 3 / 32) :
    Real.cos (3 * π / 16) * Real.cosh (π * w.re) ^ 2 ≤
      (1 + Complex.cosh ((π : ℂ) * w) ^ 2).re := by
  have hpi := Real.pi_pos
  have hre : (Complex.cosh ((π : ℂ) * w) ^ 2).re =
      Real.cosh (π * w.re) ^ 2 * Real.cos (π * w.im) ^ 2 -
        Real.sinh (π * w.re) ^ 2 * Real.sin (π * w.im) ^ 2 := by
    rw [sq, Complex.mul_re, re_cosh', im_cosh']
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    ring
  have hcos2 : Real.cos (3 * π / 16) ≤ Real.cos (2 * (π * w.im)) := by
    have h1 : |2 * (π * w.im)| ≤ 3 * π / 16 := by
      rw [abs_mul, abs_of_pos (by norm_num), abs_mul, abs_of_pos hpi]; nlinarith
    rw [← Real.cos_abs (2 * (π * w.im))]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) h1
  have hcos_sq : Real.cos (2 * (π * w.im)) = Real.cos (π * w.im) ^ 2 - Real.sin (π * w.im) ^ 2 :=
    Real.cos_two_mul' _
  have hsh : Real.sinh (π * w.re) ^ 2 = Real.cosh (π * w.re) ^ 2 - 1 := by
    linarith [Real.cosh_sq_sub_sinh_sq (π * w.re)]
  simp only [Complex.add_re, Complex.one_re, hre, hsh]
  have : Real.sin (π * w.im) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  nlinarith [sq_nonneg (Real.cosh (π * w.re))]

lemma norm_uE_le : ∃ M : ℝ, 0 < M ∧ ∀ w : ℂ, |w.im| ≤ 3 / 32 → ‖uE w‖ ≤ M := by
  have hpi := Real.pi_pos
  have hcos_pos : 0 < Real.cos (3 * π / 32) := cos_three_pi_32_pos
  have hcos2_pos : 0 < Real.cos (3 * π / 16) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set c_c : ℝ := Real.cos (3 * π / 32)
  set c2 : ℝ := Real.cos (3 * π / 16)
  have hcc_half : 1 / 2 < c_c := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have hc2_half : 1 / 2 < c2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have hcosh_bd : ∀ w : ℂ, |w.im| ≤ 3 / 32 →
      c_c * Real.cosh (π * w.re) ≤ ‖Complex.cosh ((π : ℂ) * w)‖ ∧
      ‖Complex.cosh ((π : ℂ) * w)‖ ≤ Real.cosh (π * w.re) ∧
      c_c ≤ (Complex.cosh ((π : ℂ) * w)).re := by
    intro w hw
    have hcos : c_c ≤ Real.cos (π * w.im) := by
      have h1 : |π * w.im| ≤ 3 * π / 32 := by
        rw [abs_mul, abs_of_pos hpi]; nlinarith
      rw [← Real.cos_abs (π * w.im)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) h1
    have hre : (Complex.cosh ((π : ℂ) * w)).re = Real.cosh (π * w.re) * Real.cos (π * w.im) := by
      rw [re_cosh']; simp
    have hre_ge : c_c * Real.cosh (π * w.re) ≤ (Complex.cosh ((π : ℂ) * w)).re := by
      rw [hre, mul_comm (Real.cosh _)]; exact mul_le_mul_of_nonneg_right hcos (Real.cosh_pos _).le
    have h1 := Real.one_le_cosh (π * w.re)
    refine ⟨hre_ge.trans (Complex.re_le_norm _), ?_, by nlinarith⟩
    have hsq : ‖Complex.cosh ((π : ℂ) * w)‖ ^ 2 ≤ Real.cosh (π * w.re) ^ 2 := by
      rw [norm_cosh_sq]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero]
      have : Real.sinh (π * w.re) ^ 2 = Real.cosh (π * w.re) ^ 2 - 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq (π * w.re)]
      nlinarith [Real.cos_sq_le_one (π * w.im)]
    exact le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Real.cosh_pos _).le hsq
  have h1sq_bd : ∀ w : ℂ, |w.im| ≤ 3 / 32 →
      c2 * Real.cosh (π * w.re) ^ 2 ≤ ‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ ∧
      ‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ ≤ 2 * Real.cosh (π * w.re) ^ 2 := by
    intro w hw
    obtain ⟨_, hup, _⟩ := hcosh_bd w hw
    refine ⟨(re_one_add_cosh_sq_ge hw).trans (Complex.re_le_norm _), ?_⟩
    calc ‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖
        ≤ 1 + ‖Complex.cosh ((π : ℂ) * w)‖ ^ 2 := (norm_add_le _ _).trans (by simp [norm_pow])
      _ ≤ 1 + Real.cosh (π * w.re) ^ 2 := by linarith [pow_le_pow_left₀ (norm_nonneg _) hup 2]
      _ ≤ 2 * Real.cosh (π * w.re) ^ 2 := by
          have := Real.one_le_cosh (π * w.re); nlinarith
  have hsqrt_re : ∀ w : ℂ, |w.im| ≤ 3 / 32 →
      1 / 2 < ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)).re := by
    intro w hw
    have h1 := Real.one_le_cosh (π * w.re)
    have h1pos : 0 < (1 + Complex.cosh ((π : ℂ) * w) ^ 2).re := by
      have := re_one_add_cosh_sq_ge hw
      nlinarith [sq_nonneg (Real.cosh (π * w.re))]
    have hnorm_half : 1 / 2 < ‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ := by
      have := (h1sq_bd w hw).1
      nlinarith [sq_nonneg (Real.cosh (π * w.re) - 1), hc2_half]
    have harg : |(1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg| < π / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h1pos)
    have hne : 1 + Complex.cosh ((π : ℂ) * w) ^ 2 ≠ 0 := by
      intro h; rw [h] at h1pos; simp at h1pos
    rw [Complex.cpow_def_of_ne_zero hne, Complex.exp_re]
    have hmul : (Complex.log (1 + Complex.cosh ((π : ℂ) * w) ^ 2) * (1 / 2 : ℂ)).re =
        Real.log ‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ / 2 := by
      simp [Complex.mul_re, Complex.log_re]; ring
    have hmul_im : (Complex.log (1 + Complex.cosh ((π : ℂ) * w) ^ 2) * (1 / 2 : ℂ)).im =
        (1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg / 2 := by
      simp [Complex.mul_im, Complex.log_im]; ring
    rw [hmul, hmul_im, show Real.log ‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ / 2 =
      Real.log (‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ ^ (1 / 2 : ℝ)) by
      rw [Real.log_rpow (by linarith)]; ring, Real.exp_log (by positivity), ← Real.sqrt_eq_rpow]
    have hsqrt : 1 / √2 < √‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ := by
      rw [one_div, ← Real.sqrt_inv, Real.sqrt_lt_sqrt_iff (by norm_num)]
      linarith
    have hcos_ge : 1 / √2 ≤ Real.cos ((1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg / 2) := by
      rw [show 1 / √2 = √2 / 2 by
        rw [div_eq_div_iff (Real.sqrt_pos.mpr (by norm_num)).ne' (by norm_num)]
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)], ← Real.cos_pi_div_four]
      have h1' : |(1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg / 2| ≤ π / 4 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
      conv_rhs => rw [← Real.cos_abs]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) h1'
    have h_m1 : (1 / √2) * (1 / √2) < √‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ * (1 / √2) :=
      mul_lt_mul_of_pos_right hsqrt (by positivity)
    have h_m2 : √‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ * (1 / √2) ≤
        √‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ * Real.cos ((1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg / 2) :=
      mul_le_mul_of_nonneg_left hcos_ge (Real.sqrt_nonneg _)
    have h_half : (1 / √2 : ℝ) * (1 / √2) = 1 / 2 := by
      rw [← sq, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
    linarith
  have hsq_bd : ∀ w : ℂ, |w.im| ≤ 3 / 32 →
      √c2 * Real.cosh (π * w.re) ≤ ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)‖ ∧
      ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)‖ ≤ 3 * Real.cosh (π * w.re) := by
    intro w hw
    obtain ⟨hlo, hup⟩ := h1sq_bd w hw
    have hre_pos := hsqrt_re w hw
    have hpos1 : 0 < ‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ := by
      have := Real.one_le_cosh (π * w.re); nlinarith [sq_nonneg (Real.cosh (π * w.re))]
    have hnorm_sqrt_ge : √c2 * Real.cosh (π * w.re) ≤
        ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)‖ := by
      have hne : 1 + Complex.cosh ((π : ℂ) * w) ^ 2 ≠ 0 := norm_pos_iff.mp hpos1
      have hsq_eq : ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)) ^ 2 =
          1 + Complex.cosh ((π : ℂ) * w) ^ 2 := by
        rw [Complex.cpow_def_of_ne_zero hne, ← Complex.exp_nat_mul]
        push_cast
        rw [show (2 : ℂ) * (Complex.log (1 + Complex.cosh ((π : ℂ) * w) ^ 2) * (1 / 2 : ℂ)) =
          Complex.log (1 + Complex.cosh ((π : ℂ) * w) ^ 2) by ring, Complex.exp_log hne]
      apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _)
      rw [← norm_pow, hsq_eq, mul_pow, Real.sq_sqrt hcos2_pos.le]
      exact hlo
    refine ⟨?_, ?_⟩
    · have hnorm_add : ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)‖ ≤
          ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)‖ := by
        apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _)
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
        have hs2p : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
        nlinarith [hre_pos]
      exact hnorm_sqrt_ge.trans hnorm_add
    · have hnorm_sqrt : ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)‖ ≤
          √2 * Real.cosh (π * w.re) := by
        have hne : 1 + Complex.cosh ((π : ℂ) * w) ^ 2 ≠ 0 := norm_pos_iff.mp hpos1
        have hsq_eq : ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)) ^ 2 =
            1 + Complex.cosh ((π : ℂ) * w) ^ 2 := by
          rw [Complex.cpow_def_of_ne_zero hne, ← Complex.exp_nat_mul]
          push_cast
          rw [show (2 : ℂ) * (Complex.log (1 + Complex.cosh ((π : ℂ) * w) ^ 2) * (1 / 2 : ℂ)) =
            Complex.log (1 + Complex.cosh ((π : ℂ) * w) ^ 2) by ring, Complex.exp_log hne]
        apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity)
        rw [← norm_pow, hsq_eq, mul_pow, Real.sq_sqrt (by norm_num)]
        exact hup
      have h1c := Real.one_le_cosh (π * w.re)
      have hs2_le : √2 ≤ (3 - √2) * Real.cosh (π * w.re) := by
        have : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
        nlinarith
      calc ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)‖
          ≤ ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)‖ + ‖(√2 : ℂ)‖ := norm_add_le _ _
        _ ≤ √2 * Real.cosh (π * w.re) + √2 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num))]
            linarith
        _ ≤ 3 * Real.cosh (π * w.re) := by linarith [hs2_le]
  set cF : ℝ := Real.log (c_c + 1 / 2) / π
  have hcF_pos : 0 < cF := div_pos (Real.log_pos (by linarith)) hpi
  have hFc_re : ∀ w : ℂ, |w.im| ≤ 3 / 32 → cF ≤ (FcUE w).re := by
    intro w hw
    have hre1 := (hcosh_bd w hw).2.2
    have hre2 := hsqrt_re w hw
    have hnorm_sum : c_c + 1 / 2 ≤ ‖Complex.cosh ((π : ℂ) * w) + (1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)‖ :=
      le_trans (by simp only [Complex.add_re]; linarith) (Complex.re_le_norm _)
    unfold FcUE
    rw [show Complex.log (Complex.cosh ((π : ℂ) * w) + (1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)) / (π : ℂ) =
      ((1 / π : ℝ) : ℂ) * Complex.log (Complex.cosh ((π : ℂ) * w) + (1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)) by
      push_cast; ring, Complex.re_ofReal_mul, Complex.log_re, one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hnorm_sum) hpi.le
  set c_e : ℝ := 1 - Real.exp (-(4 * π * cF))
  have hc_e_pos : 0 < c_e := by
    rw [sub_pos, Real.exp_lt_one_iff]; nlinarith
  set M_re : ℝ := |Utilde0| + (3 / 8) * (|Real.log c2| + Real.log 2) +
    (1 / 4) * (|Real.log (√c2)| + Real.log 3) +
    (1 / 4) * |Real.log 2| + |Real.log c_c| + 2 * (|Real.log c_e| + Real.log 2)
  set M : ℝ := M_re + (29 / 8) * π + 1
  refine ⟨M, by positivity, fun w hw => ?_⟩
  obtain ⟨hc_lo, hc_up, _⟩ := hcosh_bd w hw
  obtain ⟨h1_lo, h1_up⟩ := h1sq_bd w hw
  obtain ⟨hs_lo, hs_up⟩ := hsq_bd w hw
  have hch_pos : 0 < Real.cosh (π * w.re) := Real.cosh_pos _
  have h1c : 1 ≤ Real.cosh (π * w.re) := Real.one_le_cosh _
  have hL1 : |Real.log ‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ - 2 * Real.log (Real.cosh (π * w.re))| ≤
      |Real.log c2| + Real.log 2 := by
    have h1 : Real.log c2 + 2 * Real.log (Real.cosh (π * w.re)) ≤ Real.log ‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ := by
      rw [show (2 : ℝ) * Real.log (Real.cosh (π * w.re)) = Real.log (Real.cosh (π * w.re) ^ 2) by
        rw [Real.log_pow]; norm_num, ← Real.log_mul hcos2_pos.ne' (by positivity)]
      exact Real.log_le_log (by positivity) h1_lo
    have h2 : Real.log ‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖ ≤ Real.log 2 + 2 * Real.log (Real.cosh (π * w.re)) := by
      rw [show (2 : ℝ) * Real.log (Real.cosh (π * w.re)) = Real.log (Real.cosh (π * w.re) ^ 2) by
        rw [Real.log_pow]; norm_num, ← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (lt_of_lt_of_le (by positivity) h1_lo) h1_up
    rw [abs_le]; constructor <;> linarith [neg_abs_le (Real.log c2), le_abs_self (Real.log c2),
      Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hL2 : |Real.log ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)‖ - Real.log (Real.cosh (π * w.re))| ≤
      |Real.log (√c2)| + Real.log 3 := by
    have hsc2_pos : 0 < √c2 := Real.sqrt_pos.mpr hcos2_pos
    have h1 : Real.log (√c2) + Real.log (Real.cosh (π * w.re)) ≤
        Real.log ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)‖ := by
      rw [← Real.log_mul hsc2_pos.ne' hch_pos.ne']
      exact Real.log_le_log (by positivity) hs_lo
    have h2 : Real.log ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)‖ ≤
        Real.log 3 + Real.log (Real.cosh (π * w.re)) := by
      rw [← Real.log_mul (by norm_num) hch_pos.ne']
      exact Real.log_le_log (lt_of_lt_of_le (by positivity) hs_lo) hs_up
    rw [abs_le]; constructor <;> linarith [neg_abs_le (Real.log (√c2)), le_abs_self (Real.log (√c2)),
      Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  have hL3 : |Real.log ‖Complex.cosh ((π : ℂ) * w)‖ - Real.log (Real.cosh (π * w.re))| ≤ |Real.log c_c| := by
    have h1 : Real.log c_c + Real.log (Real.cosh (π * w.re)) ≤ Real.log ‖Complex.cosh ((π : ℂ) * w)‖ := by
      rw [← Real.log_mul hcos_pos.ne' hch_pos.ne']
      exact Real.log_le_log (by positivity) hc_lo
    have h2 : Real.log ‖Complex.cosh ((π : ℂ) * w)‖ ≤ Real.log (Real.cosh (π * w.re)) :=
      Real.log_le_log (lt_of_lt_of_le (by positivity) hc_lo) hc_up
    rw [abs_le]; constructor <;> linarith [neg_abs_le (Real.log c_c), abs_nonneg (Real.log c_c)]
  have hL4 : |Real.log ‖1 - Complex.exp (-((4 : ℂ) * (π : ℂ) * FcUE w))‖| ≤ |Real.log c_e| + Real.log 2 := by
    have hexp_le : ‖Complex.exp (-((4 : ℂ) * (π : ℂ) * FcUE w))‖ ≤ Real.exp (-(4 * π * cF)) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : (-((4 : ℂ) * (π : ℂ) * FcUE w)).re = -(4 * π * (FcUE w).re) := by
        simp [Complex.mul_re]
      rw [hre]; nlinarith [hFc_re w hw]
    have hlo : c_e ≤ ‖1 - Complex.exp (-((4 : ℂ) * (π : ℂ) * FcUE w))‖ := by
      have := norm_sub_norm_le (1 : ℂ) (Complex.exp (-((4 : ℂ) * (π : ℂ) * FcUE w)))
      simp only [norm_one] at this
      linarith
    have hhi : ‖1 - Complex.exp (-((4 : ℂ) * (π : ℂ) * FcUE w))‖ ≤ 2 := by
      calc ‖1 - Complex.exp (-((4 : ℂ) * (π : ℂ) * FcUE w))‖
          ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-((4 : ℂ) * (π : ℂ) * FcUE w))‖ := norm_sub_le _ _
        _ = 1 + ‖Complex.exp (-((4 : ℂ) * (π : ℂ) * FcUE w))‖ := by rw [norm_one]
        _ ≤ 1 + Real.exp (-(4 * π * cF)) := by linarith
        _ ≤ 2 := by linarith [Real.exp_le_one_iff.mpr (by nlinarith : -(4 * π * cF) ≤ 0)]
    rw [abs_le]; constructor
    · linarith [Real.log_le_log hc_e_pos hlo, neg_abs_le (Real.log c_e), Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    · linarith [Real.log_le_log (by linarith) hhi, abs_nonneg (Real.log c_e)]
  -- Now bound |(uE w).re| and |(uE w).im|
  have hu_re : |(uE w).re| ≤ M_re := by
    unfold uE
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im, Complex.one_im,
      Complex.im_ofNat, Complex.re_ofNat, Complex.log_re, zero_div, zero_mul, sub_zero,
      norm_ofNat]
    set A1 := Real.log ‖1 + Complex.cosh ((π : ℂ) * w) ^ 2‖
    set A2 := Real.log ‖(1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)‖
    set A3 := Real.log ‖Complex.cosh ((π : ℂ) * w)‖
    set L := Real.log (Real.cosh (π * w.re))
    have hid : Utilde0 + (3 / 8) * A1 + (1 / 4) * A2 - (1 / 4) * Real.log 2 - A3 +
        2 * Real.log ‖1 - Complex.exp (-4 * (π : ℂ) * FcUE w)‖ =
        Utilde0 + (3 / 8) * (A1 - 2 * L) + (1 / 4) * (A2 - L) - (1 / 4) * Real.log 2 - (A3 - L) +
        2 * Real.log ‖1 - Complex.exp (-4 * (π : ℂ) * FcUE w)‖ := by ring
    rw [hid]
    calc |Utilde0 + (3 / 8) * (A1 - 2 * L) + (1 / 4) * (A2 - L) - (1 / 4) * Real.log 2 - (A3 - L) +
          2 * Real.log ‖1 - Complex.exp (-4 * (π : ℂ) * FcUE w)‖|
        ≤ |Utilde0 + (3 / 8) * (A1 - 2 * L) + (1 / 4) * (A2 - L) - (1 / 4) * Real.log 2 - (A3 - L)| +
          |2 * Real.log ‖1 - Complex.exp (-4 * (π : ℂ) * FcUE w)‖| := abs_add_le _ _
      _ ≤ |Utilde0 + (3 / 8) * (A1 - 2 * L) + (1 / 4) * (A2 - L) - (1 / 4) * Real.log 2| + |A3 - L| +
          |2 * Real.log ‖1 - Complex.exp (-4 * (π : ℂ) * FcUE w)‖| := by linarith [abs_sub (Utilde0 + (3 / 8) * (A1 - 2 * L) + (1 / 4) * (A2 - L) - (1 / 4) * Real.log 2) (A3 - L)]
      _ ≤ |Utilde0 + (3 / 8) * (A1 - 2 * L) + (1 / 4) * (A2 - L)| + |(1 / 4 : ℝ) * Real.log 2| + |A3 - L| +
          |2 * Real.log ‖1 - Complex.exp (-4 * (π : ℂ) * FcUE w)‖| := by linarith [abs_sub (Utilde0 + (3 / 8) * (A1 - 2 * L) + (1 / 4) * (A2 - L)) ((1 / 4 : ℝ) * Real.log 2)]
      _ ≤ |Utilde0| + |(3 / 8 : ℝ) * (A1 - 2 * L)| + |(1 / 4 : ℝ) * (A2 - L)| + |(1 / 4 : ℝ) * Real.log 2| + |A3 - L| +
          |2 * Real.log ‖1 - Complex.exp (-4 * (π : ℂ) * FcUE w)‖| := by
          linarith [abs_add_le (Utilde0 + (3 / 8) * (A1 - 2 * L)) ((1 / 4) * (A2 - L)),
            abs_add_le Utilde0 ((3 / 8) * (A1 - 2 * L))]
      _ = |Utilde0| + (3 / 8) * |A1 - 2 * L| + (1 / 4) * |A2 - L| + (1 / 4) * |Real.log 2| + |A3 - L| +
          2 * |Real.log ‖1 - Complex.exp (-4 * (π : ℂ) * FcUE w)‖| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 3 / 8),
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4),
            abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ M_re := by
          dsimp only [M_re]
          have hL4' : |Real.log ‖1 - Complex.exp (-4 * (π : ℂ) * FcUE w)‖| ≤ |Real.log c_e| + Real.log 2 := by
            simpa [neg_mul] using hL4
          linarith
  have hu_im : |(uE w).im| ≤ (29 / 8) * π := by
    unfold uE
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im, Complex.one_im, zero_div,
      zero_mul, add_zero, Complex.im_ofNat, Complex.re_ofNat, Complex.log_im, zero_add]
    have harg2 : (2 : ℂ).arg = 0 := by simp
    rw [harg2, mul_zero, sub_zero]
    have ha1 := Complex.abs_arg_le_pi (1 + Complex.cosh ((π : ℂ) * w) ^ 2)
    have ha2 := Complex.abs_arg_le_pi ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ))
    have ha3 := Complex.abs_arg_le_pi (Complex.cosh ((π : ℂ) * w))
    have ha4 := Complex.abs_arg_le_pi (1 - Complex.exp (-4 * (π : ℂ) * FcUE w))
    calc |(3 / 8) * (1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg +
          (1 / 4) * ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)).arg -
          (Complex.cosh ((π : ℂ) * w)).arg +
          2 * (1 - Complex.exp (-4 * (π : ℂ) * FcUE w)).arg|
        ≤ |(3 / 8) * (1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg +
            (1 / 4) * ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)).arg -
            (Complex.cosh ((π : ℂ) * w)).arg| +
          |2 * (1 - Complex.exp (-4 * (π : ℂ) * FcUE w)).arg| := abs_add_le _ _
      _ ≤ |(3 / 8) * (1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg +
            (1 / 4) * ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)).arg| +
          |(Complex.cosh ((π : ℂ) * w)).arg| +
          |2 * (1 - Complex.exp (-4 * (π : ℂ) * FcUE w)).arg| := by
          linarith [abs_sub ((3 / 8) * (1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg +
            (1 / 4) * ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)).arg)
            (Complex.cosh ((π : ℂ) * w)).arg]
      _ ≤ |(3 / 8 : ℝ) * (1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg| +
          |(1 / 4 : ℝ) * ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)).arg| +
          |(Complex.cosh ((π : ℂ) * w)).arg| +
          |2 * (1 - Complex.exp (-4 * (π : ℂ) * FcUE w)).arg| := by
          linarith [abs_add_le ((3 / 8 : ℝ) * (1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg)
            ((1 / 4 : ℝ) * ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)).arg)]
      _ = (3 / 8) * |(1 + Complex.cosh ((π : ℂ) * w) ^ 2).arg| +
          (1 / 4) * |((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)).arg| +
          |(Complex.cosh ((π : ℂ) * w)).arg| +
          2 * |(1 - Complex.exp (-4 * (π : ℂ) * FcUE w)).arg| := by
          rw [abs_mul, abs_mul, abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 3 / 8),
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4),
            abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (29 / 8) * π := by
          linarith
  have hnorm_sum : ‖uE w‖ ≤ |(uE w).re| + |(uE w).im| := by
    calc ‖uE w‖ = ‖((uE w).re : ℂ) + ((uE w).im : ℂ) * Complex.I‖ := by
          congr 1; apply Complex.ext <;> simp
      _ ≤ ‖((uE w).re : ℂ)‖ + ‖((uE w).im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |(uE w).re| + |(uE w).im| := by simp [Complex.norm_real]
  dsimp only [M]
  linarith

lemma abs_re_logGhatRefl_le :
    ∃ M : ℝ, 0 < M ∧ ∀ b ∈ bandUpper (3 / 32), |(logGhatRefl b).re| ≤ M := by
  obtain ⟨c0, C0, hc0_pos, hG⟩ := norm_exp_logGhatLower_bounds_lt
  obtain ⟨Mu, hMu_pos, huE⟩ := norm_uE_le
  have hC0_pos : 0 < C0 := by
    have := hG (Complex.I / 4 + 3 / 16 * Complex.I) (by
      change |(Complex.I / 4 + 3 / 16 * Complex.I).im - 1 / 2| < 3 / 32; simp; norm_num) (by simp; norm_num)
    linarith
  set M_low : ℝ := max (max |Real.log c0| |Real.log C0|) Mu + 1
  have hM_low : ∀ b ∈ bandUpper (3 / 32), b.im ≤ 1 / 2 → |(logGhatLower b).re| ≤ M_low := by
    intro b hb hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨h1, h2⟩ := hG b hb hlt
      rw [Complex.norm_exp] at h1 h2
      have h1' := Real.log_le_log hc0_pos h1
      have h2' := Real.log_le_log (Real.exp_pos _) h2
      rw [Real.log_exp] at h1' h2'
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Real.log c0), le_max_left |Real.log c0| |Real.log C0|,
          le_max_left (max |Real.log c0| |Real.log C0|) Mu]
      · linarith [le_abs_self (Real.log C0), le_max_right |Real.log c0| |Real.log C0|,
          le_max_left (max |Real.log c0| |Real.log C0|) Mu]
    · have hb_eq : b = (b.re : ℂ) + Complex.I / 2 := Complex.ext (by simp) (by simp [heq])
      rw [hb_eq, re_logGhatLower_edge b.re]
      have h1 := (Complex.abs_re_le_norm _).trans (huE (b.re : ℂ) (by simp; norm_num))
      linarith [le_max_right (max |Real.log c0| |Real.log C0|) Mu]
  refine ⟨2 * Mu + M_low, by positivity, fun b hb => ?_⟩
  by_cases hle : b.im ≤ 1 / 2
  · rw [logGhatRefl_eq_lower hle]
    linarith [hM_low b hb hle]
  · push Not at hle
    have hw_neg : (Complex.I / 2 - b).im < 0 := by simp; linarith
    have hw_mem : |((Complex.I / 2 - b).im)| ≤ 3 / 32 := by
      have : (Complex.I / 2 - b).im = -(b.im - 1 / 2) := by simp
      rw [this, abs_neg]
      exact (show |b.im - 1 / 2| < 3 / 32 from hb).le
    have hrefl_pt : (Complex.I + starRingEnd ℂ b) ∈ bandUpper (3 / 32) ∧
        (Complex.I + starRingEnd ℂ b).im ≤ 1 / 2 := by
      refine ⟨?_, ?_⟩
      · change |(Complex.I + starRingEnd ℂ b).im - 1 / 2| < 3 / 32
        have h1 : (Complex.I + starRingEnd ℂ b).im - 1 / 2 = -(b.im - 1 / 2) := by simp; ring
        rw [h1, abs_neg]
        exact hb
      · exact (by simp; linarith : (Complex.I + starRingEnd ℂ b).im ≤ 1 / 2)
    have heq : logGhatRefl b = 2 * uE (Complex.I / 2 - b) -
        starRingEnd ℂ (logGhatLower (Complex.I + starRingEnd ℂ b)) := by
      unfold logGhatRefl schwarzReflectPrescribedRe
      rw [ite_eq_right_iff.mpr (fun h => by linarith)]
      dsimp only
      have harg : -reflHoriz 0 (Complex.I / 2 - b) + Complex.I / 2 = Complex.I + starRingEnd ℂ b := by
        unfold reflHoriz
        simp only [Complex.ofReal_zero, zero_mul, map_sub, map_div₀, Complex.conj_I, map_ofNat,
          map_zero]
        ring
      rw [harg]
    rw [heq, Complex.sub_re, Complex.conj_re]
    have h2u : |(2 * uE (Complex.I / 2 - b)).re| ≤ 2 * Mu := by
      rw [show (2 * uE (Complex.I / 2 - b)).re = 2 * (uE (Complex.I / 2 - b)).re by simp,
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [(Complex.abs_re_le_norm _).trans (huE _ hw_mem)]
    have hlow := hM_low _ hrefl_pt.1 hrefl_pt.2
    linarith [abs_sub (2 * uE (Complex.I / 2 - b)).re (logGhatLower (Complex.I + starRingEnd ℂ b)).re]

lemma norm_deriv_logGhatRefl_le :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ bandUpper (1 / 16),
      ‖deriv logGhatRefl b‖ + ‖deriv (deriv logGhatRefl) b‖ ≤ C := by
  obtain ⟨M, hM_pos, hM⟩ := abs_re_logGhatRefl_le
  set A : ℝ := 4 * (2 * M) with hA
  set C : ℝ := A * 128 + 2 * A * 128 ^ 2 with hC
  refine ⟨C, by positivity, fun b hb => ?_⟩
  have hb_16 : |b.im - 1 / 2| < 1 / 16 := hb
  set R : ℝ := 1 / 32
  have hR_pos : 0 < R := by norm_num
  set g : ℂ → ℂ := fun z => logGhatRefl (b + z) - logGhatRefl b
  have hsub : ∀ z ∈ ball (0 : ℂ) R, b + z ∈ bandUpper (3 / 32) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    change |(b + z).im - 1 / 2| < 3 / 32
    have him : |(b + z).im - 1 / 2| ≤ |b.im - 1 / 2| + |z.im| := by
      rw [Complex.add_im, show b.im + z.im - 1 / 2 = (b.im - 1 / 2) + z.im by ring]
      exact abs_add_le _ _
    have hz_im : |z.im| < 1 / 32 := (Complex.abs_im_le_norm z).trans_lt hz
    linarith
  have hsub8 : ∀ z ∈ ball (0 : ℂ) R, b + z ∈ bandUpper (1 / 8) := fun z hz =>
    lt_trans (show |(b + z).im - 1 / 2| < 3 / 32 from hsub z hz) (by norm_num)
  have hgd : DifferentiableOn ℂ g (ball (0 : ℂ) R) := by
    refine (differentiableOn_logGhatRefl.comp (by fun_prop) fun z hz => hsub8 z hz).sub_const _
  have hmaps : Set.MapsTo g (ball (0 : ℂ) R) {w : ℂ | w.re ≤ 2 * M} := by
    intro z hz
    show (logGhatRefl (b + z) - logGhatRefl b).re ≤ 2 * M
    rw [Complex.sub_re]
    have h1 := (abs_le.mp (hM (b + z) (hsub z hz))).2
    have h2 := (abs_le.mp (hM b (lt_trans hb_16 (by norm_num)))).1
    linarith
  have hA_bd : ∀ z ∈ ball (0 : ℂ) (R / 2), ‖g z‖ ≤ A := by
    intro z hz
    have hzR : z ∈ ball (0 : ℂ) R := ball_subset_ball (by norm_num) hz
    have hBC := Complex.borelCaratheodory (by linarith : 0 < 2 * M) hgd hmaps hR_pos hzR
    have hg0 : g 0 = 0 := by simp [g]
    rw [hg0, norm_zero, zero_mul, zero_div, add_zero] at hBC
    rw [mem_ball_zero_iff] at hz
    have hden : R / 2 ≤ R - ‖z‖ := by linarith
    have h1 : 2 * (2 * M) * ‖z‖ / (R - ‖z‖) ≤ 2 * (2 * M) * (R / 2) / (R / 2) :=
      div_le_div₀ (by positivity) (by nlinarith) (by positivity) hden
    have h2 : 2 * (2 * M) * (R / 2) / (R / 2) ≤ A := by
      have : R / 2 ≠ 0 := by norm_num [R]
      rw [mul_div_cancel_right₀ _ this]
      linarith
    linarith
  have hc1 := norm_iteratedDeriv_le_ball hR_pos hgd hA_bd (z := 0) (by simp [R]) 1
  have hc2 := norm_iteratedDeriv_le_ball hR_pos hgd hA_bd (z := 0) (by simp [R]) 2
  rw [iteratedDeriv_one] at hc1
  rw [iteratedDeriv_succ, iteratedDeriv_one] at hc2
  have h4R : (4 / R : ℝ) = 128 := by norm_num [R]
  rw [h4R] at hc1 hc2
  have heq1 : deriv g 0 = deriv logGhatRefl b := by
    have hdiff : DifferentiableAt ℂ logGhatRefl b :=
      differentiableOn_logGhatRefl.differentiableAt ((isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.sub continuous_const)) continuous_const).mem_nhds
        (lt_trans hb_16 (by norm_num)))
    have h1 : HasDerivAt g (deriv logGhatRefl b) 0 := by
      have h_add : HasDerivAt (fun z : ℂ => b + z) 1 0 := (hasDerivAt_id (0 : ℂ)).const_add b
      have h_comp := (hdiff.hasDerivAt.comp_of_eq (0 : ℂ) h_add (by simp)).sub_const (logGhatRefl b)
      simpa [g] using h_comp
    exact h1.deriv
  have heq2 : deriv (deriv g) 0 = deriv (deriv logGhatRefl) b := by
    have hopen : IsOpen (bandUpper (1 / 8)) :=
      isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const
    have hev : ∀ᶠ z in 𝓝 (0 : ℂ), deriv g z = deriv logGhatRefl (b + z) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR_pos)] with z hz
      have hdiff : DifferentiableAt ℂ logGhatRefl (b + z) :=
        differentiableOn_logGhatRefl.differentiableAt (hopen.mem_nhds (hsub8 z hz))
      have h1 : HasDerivAt g (deriv logGhatRefl (b + z)) z := by
        have h_add : HasDerivAt (fun w : ℂ => b + w) 1 z := (hasDerivAt_id z).const_add b
        simpa [g] using (hdiff.hasDerivAt.comp z h_add).sub_const (logGhatRefl b)
      exact h1.deriv
    rw [Filter.EventuallyEq.deriv_eq hev]
    have hdiff2 : DifferentiableAt ℂ (deriv logGhatRefl) b :=
      (differentiableOn_logGhatRefl.deriv hopen).differentiableAt
        (hopen.mem_nhds (lt_trans hb_16 (by norm_num)))
    have h_add : HasDerivAt (fun z : ℂ => b + z) 1 0 := (hasDerivAt_id (0 : ℂ)).const_add b
    have hc := (hdiff2.hasDerivAt.comp_of_eq (0 : ℂ) h_add (by simp)).deriv
    simpa [Function.comp_def] using hc
  rw [heq1] at hc1
  rw [heq2] at hc2
  norm_num [Nat.factorial] at hc1 hc2
  linarith

/-! ### 3. Explicit bounds and log-derivative bounds on `(1 + ζ_D b²)²` and `R4cStrip` -/

lemma norm_sqrt2_add_cosh_bounds {b : ℂ} (hb : b ∈ bandUpper (3 / 32)) :
    (1 / 2 : ℝ) * Real.cosh (π * b.re) ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ∧
    ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ≤ (√2 + 1) * Real.cosh (π * b.re) := by
  have hpi := Real.pi_pos
  have hbim : |b.im - 1 / 2| < 3 / 32 := hb
  have hbim_lo : 13 / 32 < b.im := by linarith [(abs_lt.mp hbim).1]
  have hbim_hi : b.im < 19 / 32 := by linarith [(abs_lt.mp hbim).2]
  have hcos_ge : -Real.sin (3 * π / 32) ≤ Real.cos (π * b.im) := by
    have h1 : π * b.im ≤ 19 * π / 32 := by nlinarith
    have h2 : 0 ≤ π * b.im := by nlinarith
    have hle := Real.cos_le_cos_of_nonneg_of_le_pi h2 (by linarith) h1
    rwa [show 19 * π / 32 = π / 2 + 3 * π / 32 by ring, Real.cos_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, zero_mul, one_mul, zero_sub] at hle
  have hsin_lt : Real.sin (3 * π / 32) ≤ 3 / 10 := by
    have h1 : Real.sin (3 * π / 32) ≤ 3 * π / 32 := Real.sin_le (by positivity)
    have h2 := Real.pi_lt_d2
    linarith
  have hch_pos : 0 < Real.cosh (π * b.re) := Real.cosh_pos _
  have h1c : 1 ≤ Real.cosh (π * b.re) := Real.one_le_cosh _
  constructor
  · apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _)
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_add]
    rw [re_cosh', im_cosh']
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    set C := Real.cosh (π * b.re)
    set S := Real.sinh (π * b.re)
    have hS2 : S ^ 2 = C ^ 2 - 1 := by linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
    have hcs2 : Real.cos (π * b.im) ^ 2 + Real.sin (π * b.im) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    have hexpand : (√2 + C * Real.cos (π * b.im)) ^ 2 + (S * Real.sin (π * b.im)) ^ 2 =
        2 - Real.sin (π * b.im) ^ 2 + 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 := by
      calc (√2 + C * Real.cos (π * b.im)) ^ 2 + (S * Real.sin (π * b.im)) ^ 2
          = 2 + 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 * Real.cos (π * b.im) ^ 2 +
              (C ^ 2 - 1) * Real.sin (π * b.im) ^ 2 := by
                rw [← hS2]; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
        _ = 2 - Real.sin (π * b.im) ^ 2 + 2 * √2 * C * Real.cos (π * b.im) +
              C ^ 2 * (Real.cos (π * b.im) ^ 2 + Real.sin (π * b.im) ^ 2) := by ring
        _ = 2 - Real.sin (π * b.im) ^ 2 + 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 := by rw [hcs2]; ring
    rw [show (√2 + C * Real.cos (π * b.im)) * (√2 + C * Real.cos (π * b.im)) +
        S * Real.sin (π * b.im) * (S * Real.sin (π * b.im)) =
        (√2 + C * Real.cos (π * b.im)) ^ 2 + (S * Real.sin (π * b.im)) ^ 2 by ring, hexpand]
    have hsin1 : Real.sin (π * b.im) ^ 2 ≤ 1 := Real.sin_sq_le_one _
    have hsqrt2 : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hcos_term : -(9 / 10 : ℝ) * C ≤ 2 * √2 * C * Real.cos (π * b.im) := by
      have h1 : -Real.cos (π * b.im) ≤ 3 / 10 := by linarith
      rcases le_or_gt 0 (Real.cos (π * b.im)) with hc | hc
      · have hpos : 0 ≤ 2 * √2 * C * Real.cos (π * b.im) := by positivity
        linarith [show -(9 / 10 : ℝ) * C ≤ 0 by linarith]
      · have hpos : 0 ≤ -Real.cos (π * b.im) := by linarith
        have hneg : 2 * √2 * C * (-Real.cos (π * b.im)) ≤ 2 * (3 / 2) * C * (3 / 10) := by gcongr
        linarith
    nlinarith [sq_nonneg (C - 1)]
  · have hcosh_le : ‖Complex.cosh ((π : ℂ) * b)‖ ≤ Real.cosh (π * b.re) := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Real.cosh_pos _).le
      rw [norm_cosh_sq]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero]
      have hS2 : Real.sinh (π * b.re) ^ 2 = Real.cosh (π * b.re) ^ 2 - 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
      nlinarith [Real.cos_sq_le_one (π * b.im)]
    have hsq2 : 0 ≤ √2 := Real.sqrt_nonneg _
    have h1c : 1 ≤ Real.cosh (π * b.re) := Real.one_le_cosh _
    calc ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖
        ≤ ‖(√2 : ℂ)‖ + ‖Complex.cosh ((π : ℂ) * b)‖ := norm_add_le _ _
      _ ≤ √2 + Real.cosh (π * b.re) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num))]
          linarith
      _ ≤ (√2 + 1) * Real.cosh (π * b.re) := by nlinarith

lemma cosh_pi_re_bounds (u : ℝ) :
    (1 / 2 : ℝ) * Real.exp (π * |u|) ≤ Real.cosh (π * u) ∧ Real.cosh (π * u) ≤ Real.exp (π * |u|) := by
  have hpi := Real.pi_pos
  rw [Real.cosh_eq]
  have he1 : Real.exp (π * |u|) ≤ Real.exp (π * u) + Real.exp (-(π * u)) := by
    rcases abs_cases u with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; linarith [Real.exp_pos (-(π * u))]
    · rw [h1, show π * -u = -(π * u) by ring]; linarith [Real.exp_pos (π * u)]
  have he2 : Real.exp (π * u) ≤ Real.exp (π * |u|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self u) hpi.le)
  have he3 : Real.exp (-(π * u)) ≤ Real.exp (π * |u|) :=
    Real.exp_le_exp.mpr (by rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs u) hpi.le)
  constructor <;> linarith

lemma norm_one_add_zetaD_sq_sq_bounds :
    ∃ c C : ℝ, 0 < c ∧ ∀ b ∈ bandUpper (1 / 16),
      c * Real.exp (-(2 * π * |b.re|)) ≤ ‖(1 + zetaD b ^ 2) ^ 2‖ ∧
      ‖(1 + zetaD b ^ 2) ^ 2‖ ≤ C * Real.exp (-(2 * π * |b.re|)) := by
  refine ⟨8 / (√2 + 1) ^ 2, 128, by positivity, fun b hb => ?_⟩
  have hb_strip : b ∈ imStrip :=
    ⟨by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 16 from hb)).1],
     by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 16 from hb)).2]⟩
  rw [one_add_zetaD_sq_eq hb_strip, norm_pow, norm_div, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num)),
    div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num only
  obtain ⟨h1, h2⟩ := norm_sqrt2_add_cosh_bounds (lt_trans (show |b.im - 1 / 2| < 1 / 16 from hb) (by norm_num))
  obtain ⟨hc1, hc2⟩ := cosh_pi_re_bounds b.re
  have hlo : (1 / 4 : ℝ) * Real.exp (π * |b.re|) ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by linarith
  have hhi : ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ≤ (√2 + 1) * Real.exp (π * |b.re|) := by
    calc ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ≤ (√2 + 1) * Real.cosh (π * b.re) := h2
      _ ≤ (√2 + 1) * Real.exp (π * |b.re|) := mul_le_mul_of_nonneg_left hc2 (by positivity)
  have hE : Real.exp (-(2 * π * |b.re|)) = (Real.exp (π * |b.re|) ^ 2)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [hE]
  have hEpos : 0 < Real.exp (π * |b.re|) := Real.exp_pos _
  have hNpos : 0 < ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by linarith [Real.cosh_pos (π * b.re)]
  constructor
  · have hsq : ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2 ≤ (√2 + 1) ^ 2 * Real.exp (π * |b.re|) ^ 2 := by
      calc ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2
          ≤ ((√2 + 1) * Real.exp (π * |b.re|)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hhi 2
        _ = (√2 + 1) ^ 2 * Real.exp (π * |b.re|) ^ 2 := by ring
    calc 8 / (√2 + 1) ^ 2 * (Real.exp (π * |b.re|) ^ 2)⁻¹
        = 8 / ((√2 + 1) ^ 2 * Real.exp (π * |b.re|) ^ 2) := by field_simp
      _ ≤ 8 / ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
  · have hsq : (1 / 16 : ℝ) * Real.exp (π * |b.re|) ^ 2 ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2 := by
      calc (1 / 16 : ℝ) * Real.exp (π * |b.re|) ^ 2
          = ((1 / 4 : ℝ) * Real.exp (π * |b.re|)) ^ 2 := by ring
        _ ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2 := pow_le_pow_left₀ (by positivity) hlo 2
    calc (8 : ℝ) / ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2
        ≤ 8 / ((1 / 16 : ℝ) * Real.exp (π * |b.re|) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
      _ = 128 * (Real.exp (π * |b.re|) ^ 2)⁻¹ := by field_simp; ring

lemma norm_logDeriv_one_add_zetaD_sq_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ bandUpper (1 / 16),
      ‖logDeriv (fun w => (1 + zetaD w ^ 2) ^ 2) b‖ +
        ‖deriv (logDeriv (fun w => (1 + zetaD w ^ 2) ^ 2)) b‖ ≤ C := by
  have hpi := Real.pi_pos
  set L : ℂ → ℂ := fun w => -2 * (π : ℂ) * Complex.sinh ((π : ℂ) * w) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * w))
  have hopen16 : IsOpen (bandUpper (1 / 16)) :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const
  have h_eq : ∀ b ∈ bandUpper (1 / 16), logDeriv (fun w => (1 + zetaD w ^ 2) ^ 2) b = L b := by
    intro b hb
    have hden_ne : (√2 : ℂ) + Complex.cosh ((π : ℂ) * b) ≠ 0 := by
      intro h; have := (norm_sqrt2_add_cosh_bounds (lt_trans (show |b.im - 1 / 2| < 1 / 16 from hb) (by norm_num))).1
      rw [h, norm_zero] at this; linarith [Real.cosh_pos (π * b.re)]
    have hev : ∀ᶠ w in 𝓝 b, (1 + zetaD w ^ 2) ^ 2 =
        8 / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * w)) ^ 2 := by
      filter_upwards [isOpen_imStrip.mem_nhds ⟨by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 16 from hb)).1],
        by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 16 from hb)).2]⟩] with w hw
      rw [one_add_zetaD_sq_eq hw, div_pow, mul_pow]
      congr 1
      rw [show (2 : ℂ) ^ 2 * (√2 : ℂ) ^ 2 = ((2 ^ 2 * √2 ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Real.sq_sqrt (by norm_num)]
      norm_num
    have hderiv_eq : deriv (fun w => (1 + zetaD w ^ 2) ^ 2) b =
        deriv (fun w => 8 / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * w)) ^ 2) b :=
      Filter.EventuallyEq.deriv_eq hev
    have hd_den : HasDerivAt (fun w => (√2 : ℂ) + Complex.cosh ((π : ℂ) * w))
        ((π : ℂ) * Complex.sinh ((π : ℂ) * b)) b := by
      have h1 := (Complex.hasDerivAt_cosh ((π : ℂ) * b)).comp b ((hasDerivAt_id b).const_mul (π : ℂ))
      simpa [mul_comm] using h1.const_add (√2 : ℂ)
    have hd_sq : HasDerivAt (fun w => ((√2 : ℂ) + Complex.cosh ((π : ℂ) * w)) ^ 2)
        (2 * ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) * ((π : ℂ) * Complex.sinh ((π : ℂ) * b))) b := by
      convert hd_den.pow 2 using 1; ring
    have hd_f : HasDerivAt (fun w => 8 / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * w)) ^ 2)
        (-(8 * (2 * ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) * ((π : ℂ) * Complex.sinh ((π : ℂ) * b)))) /
          (((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) ^ 2) ^ 2) b := by
      convert (hasDerivAt_const b (8 : ℂ)).div hd_sq (pow_ne_zero 2 hden_ne) using 1
      ring
    rw [logDeriv_apply, hderiv_eq, hd_f.deriv, Filter.EventuallyEq.eq_of_nhds hev]
    dsimp only [L]
    field_simp [hden_ne]
  refine ⟨4 * π + 2 * π ^ 2 * (4 * (1 + √2)) + 1, by positivity, fun b hb => ?_⟩
  have hden_ne : (√2 : ℂ) + Complex.cosh ((π : ℂ) * b) ≠ 0 := by
    intro h; have := (norm_sqrt2_add_cosh_bounds (lt_trans (show |b.im - 1 / 2| < 1 / 16 from hb) (by norm_num))).1
    rw [h, norm_zero] at this; linarith [Real.cosh_pos (π * b.re)]
  have hnorm_sh : ‖Complex.sinh ((π : ℂ) * b)‖ ≤ Real.cosh (π * b.re) := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Real.cosh_pos _).le
    rw [norm_sinh_sq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    have : Real.sinh (π * b.re) ^ 2 = Real.cosh (π * b.re) ^ 2 - 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
    nlinarith [Real.sin_sq_le_one (π * b.im)]
  have hnorm_ch : ‖Complex.cosh ((π : ℂ) * b)‖ ≤ Real.cosh (π * b.re) := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Real.cosh_pos _).le
    rw [norm_cosh_sq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    have : Real.sinh (π * b.re) ^ 2 = Real.cosh (π * b.re) ^ 2 - 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
    nlinarith [Real.cos_sq_le_one (π * b.im)]
  have hden_lo := (norm_sqrt2_add_cosh_bounds (lt_trans (show |b.im - 1 / 2| < 1 / 16 from hb) (by norm_num))).1
  have hL_bd : ‖L b‖ ≤ 4 * π := by
    dsimp only [L]
    rw [norm_div, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpi]
    rw [div_le_iff₀ (by positivity)]
    have h1 : 2 * π * ‖Complex.sinh ((π : ℂ) * b)‖ ≤ 2 * π * Real.cosh (π * b.re) :=
      mul_le_mul_of_nonneg_left hnorm_sh (by positivity)
    have h2 : 2 * π * Real.cosh (π * b.re) ≤ 4 * π * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by
      have := mul_le_mul_of_nonneg_left hden_lo (by positivity : 0 ≤ 4 * π)
      linarith
    exact h1.trans h2
  have hd_num : HasDerivAt (fun w => -2 * (π : ℂ) * Complex.sinh ((π : ℂ) * w))
      (-2 * (π : ℂ) ^ 2 * Complex.cosh ((π : ℂ) * b)) b := by
    have h := ((Complex.hasDerivAt_sinh ((π : ℂ) * b)).comp b ((hasDerivAt_id b).const_mul (π : ℂ))).const_mul
      (-2 * (π : ℂ))
    simpa [sq, mul_assoc, mul_left_comm, mul_comm] using h
  have hd_den : HasDerivAt (fun w => (√2 : ℂ) + Complex.cosh ((π : ℂ) * w))
      ((π : ℂ) * Complex.sinh ((π : ℂ) * b)) b := by
    have h := (Complex.hasDerivAt_cosh ((π : ℂ) * b)).comp b ((hasDerivAt_id b).const_mul (π : ℂ))
    simpa [mul_comm] using h.const_add (√2 : ℂ)
  have hd_L : HasDerivAt L
      ((-2 * (π : ℂ) ^ 2 * (1 + (√2 : ℂ) * Complex.cosh ((π : ℂ) * b))) /
        ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) ^ 2) b := by
    have h := hd_num.div hd_den hden_ne
    have hid : Complex.cosh ((π : ℂ) * b) ^ 2 - Complex.sinh ((π : ℂ) * b) ^ 2 = 1 :=
      Complex.cosh_sq_sub_sinh_sq _
    convert h using 1
    linear_combination 2 * (π : ℂ) ^ 2 * hid / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) ^ 2
  have hderiv_L : deriv (logDeriv (fun w => (1 + zetaD w ^ 2) ^ 2)) b = deriv L b :=
    Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hopen16.mem_nhds hb) h_eq)
  have hL'_bd : ‖deriv L b‖ ≤ 2 * π ^ 2 * (4 * (1 + √2)) := by
    rw [hd_L.deriv, norm_div, norm_pow, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    have hnum_bd : ‖1 + (√2 : ℂ) * Complex.cosh ((π : ℂ) * b)‖ ≤ (1 + √2) * Real.cosh (π * b.re) := by
      have h1c := Real.one_le_cosh (π * b.re)
      have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
      calc ‖1 + (√2 : ℂ) * Complex.cosh ((π : ℂ) * b)‖
          ≤ 1 + √2 * ‖Complex.cosh ((π : ℂ) * b)‖ := by
            have := norm_add_le (1 : ℂ) ((√2 : ℂ) * Complex.cosh ((π : ℂ) * b))
            rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs2] at this
            exact this
        _ ≤ 1 + √2 * Real.cosh (π * b.re) := by gcongr
        _ ≤ (1 + √2) * Real.cosh (π * b.re) := by
          have : 1 ≤ Real.cosh (π * b.re) := h1c
          linarith
    have hden_sq : (1 / 4 : ℝ) * Real.cosh (π * b.re) ^ 2 ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2 := by
      calc (1 / 4 : ℝ) * Real.cosh (π * b.re) ^ 2 = ((1 / 2 : ℝ) * Real.cosh (π * b.re)) ^ 2 := by ring
        _ ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2 := pow_le_pow_left₀ (by positivity) hden_lo 2
    have h1c := Real.one_le_cosh (π * b.re)
    have hnum_bd2 : ‖1 + (√2 : ℂ) * Complex.cosh ((π : ℂ) * b)‖ ≤ (1 + √2) * Real.cosh (π * b.re) ^ 2 := by
      calc ‖1 + (√2 : ℂ) * Complex.cosh ((π : ℂ) * b)‖ ≤ (1 + √2) * Real.cosh (π * b.re) := hnum_bd
        _ = (1 + √2) * Real.cosh (π * b.re) * 1 := by ring
        _ ≤ (1 + √2) * Real.cosh (π * b.re) * Real.cosh (π * b.re) := by gcongr
        _ = (1 + √2) * Real.cosh (π * b.re) ^ 2 := by ring
    rw [div_le_iff₀ (by positivity)]
    have h_all : 2 * π ^ 2 * ‖1 + (√2 : ℂ) * Complex.cosh ((π : ℂ) * b)‖ ≤
        2 * π ^ 2 * ((1 + √2) * Real.cosh (π * b.re) ^ 2) :=
      mul_le_mul_of_nonneg_left hnum_bd2 (by positivity)
    calc 2 * π ^ 2 * ‖1 + (√2 : ℂ) * Complex.cosh ((π : ℂ) * b)‖
        ≤ 2 * π ^ 2 * ((1 + √2) * Real.cosh (π * b.re) ^ 2) := h_all
      _ = 2 * π ^ 2 * (4 * (1 + √2)) * ((1 / 4 : ℝ) * Real.cosh (π * b.re) ^ 2) := by ring
      _ ≤ 2 * π ^ 2 * (4 * (1 + √2)) * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hden_sq (by positivity)
  rw [h_eq b hb, hderiv_L]
  linarith

lemma norm_zetaD_bounds_band {b : ℂ} (hb : b ∈ bandUpper (3 / 32)) :
    (1 / 2 : ℝ) ≤ ‖zetaD b‖ ∧ ‖zetaD b‖ ≤ 3 := by
  have hb_strip : b ∈ imStrip :=
    ⟨by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).1],
     by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).2]⟩
  obtain ⟨hden_lo, hden_hi⟩ := norm_sqrt2_add_cosh_bounds hb
  have hcosh_le : ‖Complex.cosh ((π : ℂ) * b)‖ ≤ Real.cosh (π * b.re) := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Real.cosh_pos _).le
    rw [norm_cosh_sq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    have : Real.sinh (π * b.re) ^ 2 = Real.cosh (π * b.re) ^ 2 - 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
    nlinarith [Real.cos_sq_le_one (π * b.im)]
  have hnum_hi : ‖(√2 : ℂ) - Complex.cosh ((π : ℂ) * b)‖ ≤ (√2 + 1) * Real.cosh (π * b.re) := by
    have h1c := Real.one_le_cosh (π * b.re)
    have hsq2 : 0 ≤ √2 := Real.sqrt_nonneg _
    calc ‖(√2 : ℂ) - Complex.cosh ((π : ℂ) * b)‖
        ≤ ‖(√2 : ℂ)‖ + ‖Complex.cosh ((π : ℂ) * b)‖ := norm_sub_le _ _
      _ ≤ √2 + Real.cosh (π * b.re) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num))]
          linarith
      _ ≤ (√2 + 1) * Real.cosh (π * b.re) := by nlinarith
  have hpi := Real.pi_pos
  have hbim_lo : 13 / 32 < b.im := by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).1]
  have hbim_hi : b.im < 19 / 32 := by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).2]
  have hcos_le : Real.cos (π * b.im) ≤ Real.sin (3 * π / 32) := by
    have h1 : 13 * π / 32 ≤ π * b.im := by nlinarith
    have h2 : π * b.im ≤ π := by nlinarith
    have hle := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) h2 h1
    rwa [show 13 * π / 32 = π / 2 - 3 * π / 32 by ring, Real.cos_pi_div_two_sub] at hle
  have hsin_lt : Real.sin (3 * π / 32) ≤ 3 / 10 := by
    have h1 : Real.sin (3 * π / 32) ≤ 3 * π / 32 := Real.sin_le (by positivity)
    have h2 := Real.pi_lt_d2
    linarith
  have hnum_lo : (3 / 4 : ℝ) * Real.cosh (π * b.re) ≤ ‖(√2 : ℂ) - Complex.cosh ((π : ℂ) * b)‖ := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _)
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
    rw [re_cosh', im_cosh']
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    set C := Real.cosh (π * b.re)
    set S := Real.sinh (π * b.re)
    have hS2 : S ^ 2 = C ^ 2 - 1 := by linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
    have hcs2 : Real.cos (π * b.im) ^ 2 + Real.sin (π * b.im) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    have hexpand : (√2 - C * Real.cos (π * b.im)) ^ 2 + (- (S * Real.sin (π * b.im))) ^ 2 =
        2 - Real.sin (π * b.im) ^ 2 - 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 := by
      calc (√2 - C * Real.cos (π * b.im)) ^ 2 + (-(S * Real.sin (π * b.im))) ^ 2
          = 2 - 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 * Real.cos (π * b.im) ^ 2 +
              (C ^ 2 - 1) * Real.sin (π * b.im) ^ 2 := by
                rw [← hS2]; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
        _ = 2 - Real.sin (π * b.im) ^ 2 - 2 * √2 * C * Real.cos (π * b.im) +
              C ^ 2 * (Real.cos (π * b.im) ^ 2 + Real.sin (π * b.im) ^ 2) := by ring
        _ = 2 - Real.sin (π * b.im) ^ 2 - 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 := by rw [hcs2]; ring
    rw [show (√2 - Real.cosh (π * b.re) * Real.cos (π * b.im)) * (√2 - Real.cosh (π * b.re) * Real.cos (π * b.im)) +
        -(Real.sinh (π * b.re) * Real.sin (π * b.im)) * -(Real.sinh (π * b.re) * Real.sin (π * b.im)) =
        (√2 - C * Real.cos (π * b.im)) ^ 2 + (-(S * Real.sin (π * b.im))) ^ 2 by dsimp only [C, S]; ring, hexpand]
    have hsin1 : Real.sin (π * b.im) ^ 2 ≤ 1 := Real.sin_sq_le_one _
    have hsqrt2 : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h1c : 1 ≤ C := Real.one_le_cosh _
    have hcos_term : 2 * √2 * C * Real.cos (π * b.im) ≤ (9 / 10 : ℝ) * C := by
      have h1 : Real.cos (π * b.im) ≤ 3 / 10 := by linarith
      calc 2 * √2 * C * Real.cos (π * b.im)
          ≤ 2 * (3 / 2) * C * (3 / 10) := by
            rcases le_or_gt (Real.cos (π * b.im)) 0 with hc | hc
            · have : 2 * √2 * C * Real.cos (π * b.im) ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
              linarith
            · gcongr
        _ = (9 / 10 : ℝ) * C := by ring
    nlinarith [sq_nonneg (C - 36 / 35)]
  have hsq_eq := zetaD_sq_eq_imStrip hb_strip
  have hnorm_sq : ‖zetaD b‖ ^ 2 = ‖(√2 : ℂ) - Complex.cosh ((π : ℂ) * b)‖ / ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by
    rw [← norm_pow, hsq_eq, norm_div]
  have hch_pos : 0 < Real.cosh (π * b.re) := Real.cosh_pos _
  have hden_pos : 0 < ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by linarith
  have hlo : (1 / 4 : ℝ) ≤ ‖zetaD b‖ ^ 2 := by
    rw [hnorm_sq, le_div_iff₀ hden_pos]
    calc (1 / 4 : ℝ) * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖
        ≤ (1 / 4 : ℝ) * ((√2 + 1) * Real.cosh (π * b.re)) := mul_le_mul_of_nonneg_left hden_hi (by norm_num)
      _ ≤ (3 / 4 : ℝ) * Real.cosh (π * b.re) := by
          have : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
          nlinarith
      _ ≤ ‖(√2 : ℂ) - Complex.cosh ((π : ℂ) * b)‖ := hnum_lo
  have hhi : ‖zetaD b‖ ^ 2 ≤ 9 := by
    rw [hnorm_sq, div_le_iff₀ hden_pos]
    have : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    calc ‖(√2 : ℂ) - Complex.cosh ((π : ℂ) * b)‖ ≤ (√2 + 1) * Real.cosh (π * b.re) := hnum_hi
      _ ≤ 9 * ((1 / 2 : ℝ) * Real.cosh (π * b.re)) := by nlinarith
      _ ≤ 9 * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := mul_le_mul_of_nonneg_left hden_lo (by norm_num)
  constructor
  · nlinarith [norm_nonneg (zetaD b)]
  · nlinarith [norm_nonneg (zetaD b)]

private lemma norm_sinh_bounds_band {b : ℂ} (hb : b ∈ bandUpper (3 / 32)) :
    (1 / 2 : ℝ) * Real.cosh (π * b.re) ≤ ‖Complex.sinh ((π : ℂ) * b)‖ ∧
    ‖Complex.sinh ((π : ℂ) * b)‖ ≤ Real.cosh (π * b.re) := by
  have hpi := Real.pi_pos
  have hbim_lo : 13 / 32 < b.im := by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).1]
  have hbim_hi : b.im < 19 / 32 := by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).2]
  have hsin_ge : Real.cos (3 * π / 32) ≤ Real.sin (π * b.im) := by
    have h1 : 13 * π / 32 ≤ π * b.im := by nlinarith
    have h2 : π * b.im ≤ 19 * π / 32 := by nlinarith
    rcases le_total (π * b.im) (π / 2) with h | h
    · have := Real.strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, h⟩ h1
      rwa [show 13 * π / 32 = π / 2 - 3 * π / 32 by ring, Real.sin_pi_div_two_sub] at this
    · rw [← Real.sin_pi_sub (π * b.im)]
      have := Real.strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        (by linarith : 13 * π / 32 ≤ π - π * b.im)
      rwa [show 13 * π / 32 = π / 2 - 3 * π / 32 by ring, Real.sin_pi_div_two_sub] at this
  have hcos_gt : 1 / 2 ≤ Real.cos (3 * π / 32) := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  constructor
  · apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _)
    rw [norm_sinh_sq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    have h1 : Real.sinh (π * b.re) ^ 2 + 1 / 4 ≤ Real.sinh (π * b.re) ^ 2 + Real.sin (π * b.im) ^ 2 := by
      have : 1 / 2 ≤ Real.sin (π * b.im) := hcos_gt.trans hsin_ge
      nlinarith
    have h2 : Real.cosh (π * b.re) ^ 2 / 4 ≤ Real.sinh (π * b.re) ^ 2 + 1 / 4 := by
      linarith [Real.cosh_sq_sub_sinh_sq (π * b.re), sq_nonneg (Real.sinh (π * b.re))]
    nlinarith
  · apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Real.cosh_pos _).le
    rw [norm_sinh_sq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    have : Real.sinh (π * b.re) ^ 2 = Real.cosh (π * b.re) ^ 2 - 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
    nlinarith [Real.sin_sq_le_one (π * b.im)]

private lemma norm_one_add_2z_sub_z2_bounds {b : ℂ} (hb : b ∈ bandUpper (3 / 32)) :
    1 / 2 ≤ ‖1 + 2 * zetaD b - zetaD b ^ 2‖ ∧ ‖1 + 2 * zetaD b - zetaD b ^ 2‖ ≤ 16 := by
  have hb_strip : b ∈ imStrip :=
    ⟨by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).1],
     by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).2]⟩
  obtain ⟨_, hz_hi⟩ := norm_zetaD_bounds_band hb
  constructor
  · have hsq_eq := zetaD_sq_eq_imStrip hb_strip
    have harg_w : |(((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b))).arg| < π := by
      have hslit := (zetaD_w_mem_slitPlane_imStrip hb_strip).2
      have hne := Complex.slitPlane_arg_ne_pi hslit
      have hle := Complex.arg_le_pi (((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)))
      have hlt := Complex.neg_pi_lt_arg (((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)))
      rw [abs_lt]; constructor <;> [linarith; exact lt_of_le_of_ne hle hne]
    have hre_z : 0 < (zetaD b).re := by
      have hw_ne : ((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) ≠ 0 :=
        Complex.slitPlane_ne_zero (zetaD_w_mem_slitPlane_imStrip hb_strip).2
      unfold zetaD
      rw [Complex.cpow_def_of_ne_zero hw_ne, Complex.exp_re]
      have hmul : (Complex.log (((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b))) * (1 / 2 : ℂ)).im =
          (((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b))).arg / 2 := by
        simp [Complex.mul_im, Complex.log_im]; ring
      rw [hmul]
      exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [(abs_lt.mp harg_w).1], by linarith [(abs_lt.mp harg_w).2]⟩)
    have hpi := Real.pi_pos
    have hbim_lo : 13 / 32 < b.im := by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).1]
    have hbim_hi : b.im < 19 / 32 := by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).2]
    have hcos_abs : |Real.cos (π * b.im)| ≤ 3 / 10 := by
      have h1 : Real.cos (π * b.im) ≤ Real.sin (3 * π / 32) := by
        have hle := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith) (by nlinarith : 13 * π / 32 ≤ π * b.im)
        rwa [show 13 * π / 32 = π / 2 - 3 * π / 32 by ring, Real.cos_pi_div_two_sub] at hle
      have h2 : -Real.sin (3 * π / 32) ≤ Real.cos (π * b.im) := by
        have hle := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith) (by nlinarith : π * b.im ≤ 19 * π / 32)
        rwa [show 19 * π / 32 = π / 2 + 3 * π / 32 by ring, Real.cos_add, Real.cos_pi_div_two,
          Real.sin_pi_div_two, zero_mul, one_mul, zero_sub] at hle
      have hsin_lt : Real.sin (3 * π / 32) ≤ 3 / 10 := by
        have := Real.sin_le (by positivity : 0 ≤ 3 * π / 32)
        have := Real.pi_lt_d2
        linarith
      rw [abs_le]; constructor <;> linarith
    set C := Real.cosh (π * b.re)
    set S := Real.sinh (π * b.re)
    have hS2 : S ^ 2 = C ^ 2 - 1 := by linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
    have hcs2 : Real.cos (π * b.im) ^ 2 + Real.sin (π * b.im) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    have hnum_sq : ‖(√2 : ℂ) - Complex.cosh ((π : ℂ) * b)‖ ^ 2 ≤ 2 + C ^ 2 + (9 / 10 : ℝ) * C := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
      rw [re_cosh', im_cosh']
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero]
      have hexp : (√2 - C * Real.cos (π * b.im)) ^ 2 + (-(S * Real.sin (π * b.im))) ^ 2 =
          2 - Real.sin (π * b.im) ^ 2 - 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 := by
        calc (√2 - C * Real.cos (π * b.im)) ^ 2 + (-(S * Real.sin (π * b.im))) ^ 2
            = 2 - 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 * Real.cos (π * b.im) ^ 2 +
                (C ^ 2 - 1) * Real.sin (π * b.im) ^ 2 := by
                  rw [← hS2]; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
          _ = 2 - Real.sin (π * b.im) ^ 2 - 2 * √2 * C * Real.cos (π * b.im) +
                C ^ 2 * (Real.cos (π * b.im) ^ 2 + Real.sin (π * b.im) ^ 2) := by ring
          _ = 2 - Real.sin (π * b.im) ^ 2 - 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 := by rw [hcs2]; ring
      rw [show (√2 - Real.cosh (π * b.re) * Real.cos (π * b.im)) * (√2 - Real.cosh (π * b.re) * Real.cos (π * b.im)) +
          -(Real.sinh (π * b.re) * Real.sin (π * b.im)) * -(Real.sinh (π * b.re) * Real.sin (π * b.im)) =
          (√2 - C * Real.cos (π * b.im)) ^ 2 + (-(S * Real.sin (π * b.im))) ^ 2 by dsimp only [C, S]; ring, hexp]
      have hsqrt2 : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have h1c : 0 ≤ C := (Real.cosh_pos _).le
      have hsin0 : 0 ≤ Real.sin (π * b.im) ^ 2 := sq_nonneg _
      have hcross : -(9 / 10 * C) ≤ -(2 * √2 * C * Real.cos (π * b.im)) ∧
          -(2 * √2 * C * Real.cos (π * b.im)) ≤ 9 / 10 * C := by
        rw [← abs_le, abs_neg, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg h1c]
        have hcos := hcos_abs
        calc 2 * √2 * C * |Real.cos (π * b.im)|
            ≤ 2 * (3 / 2) * C * (3 / 10) := by gcongr
          _ = 9 / 10 * C := by ring
      linarith
    have hden_sq : 1 + C ^ 2 - (9 / 10 : ℝ) * C ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_add]
      rw [re_cosh', im_cosh']
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero]
      have hexp : (√2 + C * Real.cos (π * b.im)) ^ 2 + (S * Real.sin (π * b.im)) ^ 2 =
          2 - Real.sin (π * b.im) ^ 2 + 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 := by
        calc (√2 + C * Real.cos (π * b.im)) ^ 2 + (S * Real.sin (π * b.im)) ^ 2
            = 2 + 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 * Real.cos (π * b.im) ^ 2 +
                (C ^ 2 - 1) * Real.sin (π * b.im) ^ 2 := by
                  rw [← hS2]; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
          _ = 2 - Real.sin (π * b.im) ^ 2 + 2 * √2 * C * Real.cos (π * b.im) +
                C ^ 2 * (Real.cos (π * b.im) ^ 2 + Real.sin (π * b.im) ^ 2) := by ring
          _ = 2 - Real.sin (π * b.im) ^ 2 + 2 * √2 * C * Real.cos (π * b.im) + C ^ 2 := by rw [hcs2]; ring
      rw [show (√2 + Real.cosh (π * b.re) * Real.cos (π * b.im)) * (√2 + Real.cosh (π * b.re) * Real.cos (π * b.im)) +
          Real.sinh (π * b.re) * Real.sin (π * b.im) * (Real.sinh (π * b.re) * Real.sin (π * b.im)) =
          (√2 + C * Real.cos (π * b.im)) ^ 2 + (S * Real.sin (π * b.im)) ^ 2 by dsimp only [C, S]; ring, hexp]
      have hsqrt2 : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have h1c : 0 ≤ C := (Real.cosh_pos _).le
      have hsin1 : Real.sin (π * b.im) ^ 2 ≤ 1 := Real.sin_sq_le_one _
      have hcross : -(9 / 10 * C) ≤ 2 * √2 * C * Real.cos (π * b.im) ∧
          2 * √2 * C * Real.cos (π * b.im) ≤ 9 / 10 * C := by
        rw [← abs_le, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg h1c]
        have hcos := hcos_abs
        calc 2 * √2 * C * |Real.cos (π * b.im)|
            ≤ 2 * (3 / 2) * C * (3 / 10) := by gcongr
          _ = 9 / 10 * C := by ring
      linarith
    have h1c : 1 ≤ C := Real.one_le_cosh _
    have hz4 : ‖zetaD b‖ ^ 4 ≤ 4 := by
      have hnorm_sq : ‖zetaD b‖ ^ 2 = ‖(√2 : ℂ) - Complex.cosh ((π : ℂ) * b)‖ / ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by
        rw [← norm_pow, hsq_eq, norm_div]
      have hden_pos : 0 < ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by
        have h1 := (norm_sqrt2_add_cosh_bounds hb).1
        have h2 := Real.cosh_pos (π * b.re)
        linarith
      rw [show (‖zetaD b‖ : ℝ) ^ 4 = (‖zetaD b‖ ^ 2) ^ 2 by ring, hnorm_sq, div_pow, div_le_iff₀ (sq_pos_of_pos hden_pos)]
      nlinarith [sq_nonneg (C - 1)]
    have hz2 : ‖zetaD b‖ ^ 2 ≤ 2 := by
      nlinarith [sq_nonneg (‖zetaD b‖ ^ 2 - 2), show (‖zetaD b‖ ^ 2) ^ 2 = ‖zetaD b‖ ^ 4 by ring]
    have hre_sq : (zetaD b).re ^ 2 ≤ 2 := by
      have := Complex.sq_norm (zetaD b)
      rw [Complex.normSq_apply] at this
      nlinarith [sq_nonneg (zetaD b).im]
    have hre_le2 : (zetaD b).re ≤ 2 := by nlinarith
    have hre_12z : 1 ≤ (1 + 2 * zetaD b - zetaD b ^ 2).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.re_ofNat,
        Complex.im_ofNat, zero_mul, sub_zero, sq]
      nlinarith [sq_nonneg (zetaD b).im]
    exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans (hre_12z.trans (Complex.re_le_norm _))
  · calc ‖1 + 2 * zetaD b - zetaD b ^ 2‖
        ≤ ‖(1 : ℂ) + 2 * zetaD b‖ + ‖zetaD b ^ 2‖ := norm_sub_le _ _
      _ ≤ 1 + 2 * ‖zetaD b‖ + ‖zetaD b‖ ^ 2 := by
          have := norm_add_le (1 : ℂ) (2 * zetaD b)
          simp only [norm_one, norm_mul, Complex.norm_ofNat, norm_pow] at this ⊢
          linarith
      _ ≤ 1 + 2 * 3 + 3 ^ 2 := by nlinarith [norm_nonneg (zetaD b)]
      _ = 16 := by norm_num

lemma norm_R4cStrip_bounds_32 :
    ∃ c C : ℝ, 0 < c ∧ ∀ b ∈ bandUpper (3 / 32),
      c * (1 + |b.re|) ^ (1 / 2 : ℝ) ≤ ‖R4cStrip b‖ ∧
      ‖R4cStrip b‖ ≤ C * (1 + |b.re|) ^ (1 / 2 : ℝ) := by
  have hpi := Real.pi_pos
  have hkap := kap_pos
  set c2 : ℝ := 1 / (8 * √2 * kap ^ 2) * min (13 * π / 64) (π / 2)
  set C2 : ℝ := 16 * (√2 + 1) / (2 * √2 * kap ^ 2) * (2 * π)
  refine ⟨√c2, √C2, Real.sqrt_pos.mpr (by positivity), fun b hb => ?_⟩
  have hb_strip : b ∈ imStrip :=
    ⟨by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).1],
     by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).2]⟩
  have hb_q : b ∈ bandUpper (1 / 4) := lt_trans (show |b.im - 1 / 2| < 3 / 32 from hb) (by norm_num)
  have hr1_ne : (1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2) ≠ 0 :=
    Complex.slitPlane_ne_zero (r4c_alg_factor_mem_slitPlane hb_q)
  have hr2_ne : (π : ℂ) * b / Complex.sinh ((π : ℂ) * b) ≠ 0 :=
    Complex.slitPlane_ne_zero (pi_mul_div_sinh_mem_slitPlane hb_strip)
  have hcpow_sq : ∀ w : ℂ, w ≠ 0 → (w ^ (1 / 2 : ℂ)) ^ 2 = w := fun w hw => by
    rw [Complex.cpow_def_of_ne_zero hw, ← Complex.exp_nat_mul]
    push_cast
    rw [show (2 : ℂ) * (Complex.log w * (1 / 2 : ℂ)) = Complex.log w by ring, Complex.exp_log hw]
  have hnorm_sq : ‖R4cStrip b‖ ^ 2 =
      ‖(1 + 2 * zetaD b - zetaD b ^ 2)‖ * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ / (2 * √2) *
        (π * ‖b‖ / ‖Complex.sinh ((π : ℂ) * b)‖) / kap ^ 2 := by
    rw [← norm_pow]
    have hsq_R : R4cStrip b ^ 2 =
        ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) * ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) /
          (kap : ℂ) ^ 2 := by
      unfold R4cStrip
      rw [div_pow, mul_pow, hcpow_sq _ hr1_ne, hcpow_sq _ hr2_ne]
    rw [hsq_R, norm_div, norm_mul, norm_div, norm_div, norm_mul,
      Complex.norm_pow, one_add_zetaD_sq_eq hb_strip, norm_div, norm_mul, Complex.norm_ofNat]
    have hsq2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkap, abs_of_pos hpi, abs_of_pos hsq2]
    field_simp
  obtain ⟨ha_lo, ha_hi⟩ := norm_one_add_2z_sub_z2_bounds hb
  obtain ⟨hc_lo, hc_hi⟩ := norm_sqrt2_add_cosh_bounds hb
  obtain ⟨hs_lo, hs_hi⟩ := norm_sinh_bounds_band hb
  have hb_lo : 13 / 64 * (1 + |b.re|) ≤ ‖b‖ := by
    have hbim : 13 / 32 < b.im := by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)).1]
    have h1 : |b.re| ≤ ‖b‖ := Complex.abs_re_le_norm b
    have h2 : 13 / 32 ≤ ‖b‖ := hbim.le.trans (le_trans (le_abs_self _) (Complex.abs_im_le_norm b))
    linarith
  have hb_hi : ‖b‖ ≤ 1 + |b.re| := by
    have hbim : |b.im| ≤ 1 := by
      have := abs_lt.mp (show |b.im - 1 / 2| < 3 / 32 from hb)
      rw [abs_le]; constructor <;> linarith
    calc ‖b‖ = ‖(b.re : ℂ) + (b.im : ℂ) * Complex.I‖ := by congr 1; apply Complex.ext <;> simp
      _ ≤ ‖(b.re : ℂ)‖ + ‖(b.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |b.re| + |b.im| := by simp [Complex.norm_real]
      _ ≤ 1 + |b.re| := by linarith
  have hch_pos : 0 < Real.cosh (π * b.re) := Real.cosh_pos _
  have hsh_pos : 0 < ‖Complex.sinh ((π : ℂ) * b)‖ := by linarith
  have hlo : c2 * (1 + |b.re|) ≤ ‖R4cStrip b‖ ^ 2 := by
    rw [hnorm_sq]
    have h1 : 1 / (8 * √2) * Real.cosh (π * b.re) ≤
        ‖1 + 2 * zetaD b - zetaD b ^ 2‖ * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ / (2 * √2) := by
      rw [le_div_iff₀ (by positivity)]
      calc 1 / (8 * √2) * Real.cosh (π * b.re) * (2 * √2)
          = (1 / 2) * ((1 / 2) * Real.cosh (π * b.re)) := by field_simp; ring
        _ ≤ ‖1 + 2 * zetaD b - zetaD b ^ 2‖ * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ :=
            mul_le_mul ha_lo hc_lo (by positivity) (norm_nonneg _)
    have h2 : (13 * π / 64) * (1 + |b.re|) / Real.cosh (π * b.re) ≤ π * ‖b‖ / ‖Complex.sinh ((π : ℂ) * b)‖ := by
      apply div_le_div₀ (by positivity) (by nlinarith) hsh_pos hs_hi
    have h3 : min (13 * π / 64) (π / 2) ≤ 13 * π / 64 := min_le_left _ _
    have hprod : 1 / (8 * √2) * min (13 * π / 64) (π / 2) * (1 + |b.re|) ≤
        (‖1 + 2 * zetaD b - zetaD b ^ 2‖ * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ / (2 * √2)) *
          (π * ‖b‖ / ‖Complex.sinh ((π : ℂ) * b)‖) := by
      calc 1 / (8 * √2) * min (13 * π / 64) (π / 2) * (1 + |b.re|)
          ≤ 1 / (8 * √2) * (13 * π / 64) * (1 + |b.re|) := by gcongr
        _ = (1 / (8 * √2) * Real.cosh (π * b.re)) * ((13 * π / 64) * (1 + |b.re|) / Real.cosh (π * b.re)) := by
            field_simp
        _ ≤ _ := mul_le_mul h1 h2 (by positivity) (by positivity)
    rw [le_div_iff₀ (by positivity)]
    calc c2 * (1 + |b.re|) * kap ^ 2
        = 1 / (8 * √2) * min (13 * π / 64) (π / 2) * (1 + |b.re|) := by
          dsimp only [c2]; field_simp
      _ ≤ _ := hprod
  have hhi : ‖R4cStrip b‖ ^ 2 ≤ C2 * (1 + |b.re|) := by
    rw [hnorm_sq]
    have h1 : ‖1 + 2 * zetaD b - zetaD b ^ 2‖ * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ / (2 * √2) ≤
        16 * (√2 + 1) / (2 * √2) * Real.cosh (π * b.re) := by
      calc ‖1 + 2 * zetaD b - zetaD b ^ 2‖ * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ / (2 * √2)
          ≤ 16 * ((√2 + 1) * Real.cosh (π * b.re)) / (2 * √2) :=
            div_le_div_of_nonneg_right (mul_le_mul ha_hi hc_hi (by positivity) (by positivity)) (by positivity)
        _ = 16 * (√2 + 1) / (2 * √2) * Real.cosh (π * b.re) := by ring
    have h2 : π * ‖b‖ / ‖Complex.sinh ((π : ℂ) * b)‖ ≤ 2 * π * (1 + |b.re|) / Real.cosh (π * b.re) := by
      rw [div_le_div_iff₀ hsh_pos hch_pos]
      calc π * ‖b‖ * Real.cosh (π * b.re)
          ≤ π * (1 + |b.re|) * Real.cosh (π * b.re) := by gcongr
        _ = 2 * π * (1 + |b.re|) * ((1 / 2 : ℝ) * Real.cosh (π * b.re)) := by ring
        _ ≤ 2 * π * (1 + |b.re|) * ‖Complex.sinh ((π : ℂ) * b)‖ := by gcongr
    have hprod : (‖1 + 2 * zetaD b - zetaD b ^ 2‖ * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ / (2 * √2)) *
          (π * ‖b‖ / ‖Complex.sinh ((π : ℂ) * b)‖) ≤
        16 * (√2 + 1) / (2 * √2) * (2 * π) * (1 + |b.re|) := by
      calc _ ≤ (16 * (√2 + 1) / (2 * √2) * Real.cosh (π * b.re)) *
              (2 * π * (1 + |b.re|) / Real.cosh (π * b.re)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 16 * (√2 + 1) / (2 * √2) * (2 * π) * (1 + |b.re|) := by field_simp
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ 16 * (√2 + 1) / (2 * √2) * (2 * π) * (1 + |b.re|) := hprod
      _ = C2 * (1 + |b.re|) * kap ^ 2 := by dsimp only [C2]; field_simp
  have hc2_pos : 0 ≤ c2 := by dsimp only [c2]; positivity
  have hC2_pos : 0 ≤ C2 := by dsimp only [C2]; positivity
  have h1r : 0 ≤ 1 + |b.re| := by positivity
  rw [← Real.sqrt_eq_rpow]
  constructor
  · calc √c2 * √(1 + |b.re|) = √(c2 * (1 + |b.re|)) := (Real.sqrt_mul hc2_pos _).symm
      _ ≤ √(‖R4cStrip b‖ ^ 2) := Real.sqrt_le_sqrt hlo
      _ = ‖R4cStrip b‖ := Real.sqrt_sq (norm_nonneg _)
  · calc ‖R4cStrip b‖ = √(‖R4cStrip b‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(C2 * (1 + |b.re|)) := Real.sqrt_le_sqrt hhi
      _ = √C2 * √(1 + |b.re|) := Real.sqrt_mul hC2_pos _

lemma norm_R4cStrip_bounds :
    ∃ c C : ℝ, 0 < c ∧ ∀ b ∈ bandUpper (1 / 16),
      c * (1 + |b.re|) ^ (1 / 2 : ℝ) ≤ ‖R4cStrip b‖ ∧
      ‖R4cStrip b‖ ≤ C * (1 + |b.re|) ^ (1 / 2 : ℝ) := by
  obtain ⟨c, C, hc, hbd⟩ := norm_R4cStrip_bounds_32
  exact ⟨c, C, hc, fun b hb => hbd b (lt_trans (show |b.im - 1 / 2| < 1 / 16 from hb) (by norm_num))⟩

lemma norm_logDeriv_R4cStrip_le :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ bandUpper (1 / 16),
      ‖logDeriv R4cStrip b‖ + ‖deriv (logDeriv R4cStrip) b‖ ≤ C := by
  obtain ⟨c, C0, hc_pos, hbd⟩ := norm_R4cStrip_bounds_32
  have hC0_pos : 0 < C0 := by
    have h := hbd (Complex.I / 2) (by change |(Complex.I / 2).im - 1 / 2| < 3 / 32; simp)
    simp only [Complex.div_ofNat_re, Complex.I_re, zero_div, abs_zero, add_zero, Real.one_rpow,
      mul_one] at h
    linarith [h.1, h.2]
  set M : ℝ := Real.log (C0 / c * √2) + 1 with hM
  have hM_pos : 0 < M := by
    have hc_le_C0 : c ≤ C0 := by
      have h := hbd (Complex.I / 2) (by change |(Complex.I / 2).im - 1 / 2| < 3 / 32; simp)
      simp only [Complex.div_ofNat_re, Complex.I_re, zero_div, abs_zero, add_zero, Real.one_rpow,
        mul_one] at h
      linarith [h.1, h.2]
    have h1 : 1 ≤ C0 / c * √2 := by
      have : 1 ≤ √2 := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
      have : 1 ≤ C0 / c := (one_le_div hc_pos).mpr hc_le_C0
      nlinarith
    linarith [Real.log_nonneg h1]
  set A : ℝ := 2 * M with hA
  set C : ℝ := A * 128 + 2 * A * 128 ^ 2 with hC
  refine ⟨C, by positivity, fun b hb => ?_⟩
  set R : ℝ := 1 / 32
  have hR_pos : 0 < R := by norm_num
  have hsub32 : ∀ z ∈ ball (0 : ℂ) R, b + z ∈ bandUpper (3 / 32) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    change |(b + z).im - 1 / 2| < 3 / 32
    have him : |(b + z).im - 1 / 2| ≤ |b.im - 1 / 2| + |z.im| := by
      rw [Complex.add_im, show b.im + z.im - 1 / 2 = (b.im - 1 / 2) + z.im by ring]
      exact abs_add_le _ _
    have hz_im : |z.im| < 1 / 32 := (Complex.abs_im_le_norm z).trans_lt hz
    have hb16 : |b.im - 1 / 2| < 1 / 16 := hb
    linarith
  have hsub_q : ∀ z ∈ ball (0 : ℂ) R, b + z ∈ bandUpper (1 / 4) := fun z hz =>
    lt_trans (show |(b + z).im - 1 / 2| < 3 / 32 from hsub32 z hz) (by norm_num)
  set g : ℂ → ℂ := fun z => R4cStrip (b + z) / R4cStrip b
  have hgd : DifferentiableOn ℂ g (ball (0 : ℂ) R) :=
    (differentiableOn_R4cStrip.comp (by fun_prop) fun z hz => hsub_q z hz).div_const _
  have hb_q : b ∈ bandUpper (1 / 4) := lt_trans (show |b.im - 1 / 2| < 1 / 16 from hb) (by norm_num)
  have hne : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0 := fun z hz =>
    div_ne_zero (R4cStrip_ne_zero (hsub_q z hz)) (R4cStrip_ne_zero hb_q)
  obtain ⟨H, hHd, hHder, hH0, hHre⟩ := exists_log_ball hR_pos hgd hne
  have hg0 : g 0 = 1 := by simp [g, div_self (R4cStrip_ne_zero hb_q)]
  have hH0' : H 0 = 0 := by rw [hH0, hg0, norm_one, Real.log_one]; simp
  have hb32 : b ∈ bandUpper (3 / 32) := lt_trans (show |b.im - 1 / 2| < 1 / 16 from hb) (by norm_num)
  have hmaps : Set.MapsTo H (ball (0 : ℂ) R) {w : ℂ | w.re ≤ M} := by
    intro z hz
    show (H z).re ≤ M
    rw [hHre z hz]
    have h1 := (hbd (b + z) (hsub32 z hz)).2
    have h2 := (hbd b hb32).1
    have hre_rat : (1 + |(b + z).re|) / (1 + |b.re|) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      rw [mem_ball_zero_iff] at hz
      have hzr : |z.re| < 1 / 32 := (Complex.abs_re_le_norm z).trans_lt hz
      have hadd : |(b + z).re| ≤ |b.re| + |z.re| := by rw [Complex.add_re]; exact abs_add_le _ _
      linarith [abs_nonneg b.re]
    have hpow : (1 + |(b + z).re|) ^ (1 / 2 : ℝ) / (1 + |b.re|) ^ (1 / 2 : ℝ) ≤ √2 := by
      rw [← Real.div_rpow (by positivity) (by positivity), ← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt hre_rat
    have hR_pos1 : 0 < ‖R4cStrip b‖ := norm_pos_iff.mpr (R4cStrip_ne_zero hb_q)
    have hR_pos2 : 0 < ‖R4cStrip (b + z)‖ := norm_pos_iff.mpr (R4cStrip_ne_zero (hsub_q z hz))
    have hg_le : ‖g z‖ ≤ C0 / c * √2 := by
      dsimp only [g]
      rw [norm_div]
      calc ‖R4cStrip (b + z)‖ / ‖R4cStrip b‖
          ≤ (C0 * (1 + |(b + z).re|) ^ (1 / 2 : ℝ)) / (c * (1 + |b.re|) ^ (1 / 2 : ℝ)) := by
            gcongr
        _ = (C0 / c) * ((1 + |(b + z).re|) ^ (1 / 2 : ℝ) / (1 + |b.re|) ^ (1 / 2 : ℝ)) := by ring
        _ ≤ C0 / c * √2 := mul_le_mul_of_nonneg_left hpow (by positivity)
    have hlog := Real.log_le_log (norm_pos_iff.mpr (hne z hz)) hg_le
    linarith
  have hA_bd : ∀ z ∈ ball (0 : ℂ) (R / 2), ‖H z‖ ≤ A := by
    intro z hz
    have hzR : z ∈ ball (0 : ℂ) R := ball_subset_ball (by norm_num) hz
    have hBC := Complex.borelCaratheodory hM_pos hHd hmaps hR_pos hzR
    rw [hH0', norm_zero, zero_mul, zero_div, add_zero] at hBC
    rw [mem_ball_zero_iff] at hz
    have hden : R / 2 ≤ R - ‖z‖ := by linarith
    have h1 : 2 * M * ‖z‖ / (R - ‖z‖) ≤ 2 * M * (R / 2) / (R / 2) := by
      gcongr
    have h2 : 2 * M * (R / 2) / (R / 2) = A := by
      have : R / 2 ≠ 0 := by norm_num [R]
      rw [hA]; field_simp
    linarith
  have hc1 := norm_iteratedDeriv_le_ball hR_pos hHd hA_bd (z := 0) (by simp [R]) 1
  have hc2 := norm_iteratedDeriv_le_ball hR_pos hHd hA_bd (z := 0) (by simp [R]) 2
  rw [iteratedDeriv_one] at hc1
  rw [iteratedDeriv_succ, iteratedDeriv_one] at hc2
  have h4R : (4 / R : ℝ) = 128 := by norm_num [R]
  rw [h4R] at hc1 hc2
  have hlogDeriv_eq : ∀ z ∈ ball (0 : ℂ) R, deriv H z = logDeriv R4cStrip (b + z) := by
    intro z hz
    rw [hHder z hz, logDeriv_apply]
    have hdiff : DifferentiableAt ℂ R4cStrip (b + z) :=
      differentiableOn_R4cStrip.differentiableAt (isOpen_band.mem_nhds (hsub_q z hz))
    have h_add : HasDerivAt (fun w : ℂ => b + w) 1 z := (hasDerivAt_id z).const_add b
    have hdg : HasDerivAt g (deriv R4cStrip (b + z) / R4cStrip b) z := by
      simpa using (hdiff.hasDerivAt.comp z h_add).div_const (R4cStrip b)
    rw [hdg.deriv]
    dsimp only [g]
    have hRb : R4cStrip b ≠ 0 := R4cStrip_ne_zero hb_q
    field_simp [hRb]
  have heq1 : deriv H 0 = logDeriv R4cStrip b := by
    simpa using hlogDeriv_eq 0 (mem_ball_self hR_pos)
  have heq2 : deriv (deriv H) 0 = deriv (logDeriv R4cStrip) b := by
    have hev : ∀ᶠ z in 𝓝 (0 : ℂ), deriv H z = logDeriv R4cStrip (b + z) :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hR_pos)) hlogDeriv_eq
    rw [Filter.EventuallyEq.deriv_eq hev]
    have hdiff_ld : DifferentiableAt ℂ (logDeriv R4cStrip) b := by
      have hld_diff : DifferentiableOn ℂ (logDeriv R4cStrip) (bandUpper (1 / 4)) := by
        intro w hw
        have hd1 : DifferentiableAt ℂ (deriv R4cStrip) w :=
          (differentiableOn_R4cStrip.deriv isOpen_band).differentiableAt (isOpen_band.mem_nhds hw)
        have hd2 : DifferentiableAt ℂ R4cStrip w :=
          differentiableOn_R4cStrip.differentiableAt (isOpen_band.mem_nhds hw)
        exact (hd1.div hd2 (R4cStrip_ne_zero hw)).differentiableWithinAt.congr
          (fun z _ => by simp [logDeriv_apply]) (by simp [logDeriv_apply])
      exact hld_diff.differentiableAt (isOpen_band.mem_nhds hb_q)
    have h_add : HasDerivAt (fun z : ℂ => b + z) 1 0 := (hasDerivAt_id (0 : ℂ)).const_add b
    have hc := (hdiff_ld.hasDerivAt.comp_of_eq (0 : ℂ) h_add (by simp)).deriv
    simpa [Function.comp_def] using hc
  rw [heq1] at hc1
  rw [heq2] at hc2
  norm_num [Nat.factorial] at hc1 hc2
  linarith
