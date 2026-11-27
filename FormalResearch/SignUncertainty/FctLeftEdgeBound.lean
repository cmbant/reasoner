/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctRayAmp
public import FormalResearch.SignUncertainty.FctSplittingPsiFarBase
public import FormalResearch.SignUncertainty.FctSplittingPsiNear
public import FormalResearch.SignUncertainty.FctSplittingLeftC2
public import FormalResearch.SignUncertainty.CtOuterU2
public import FormalResearch.SignUncertainty.UctSeedEdgeZT
public import FormalResearch.SignUncertainty.UctSeedEdgeE
public import FormalResearch.SignUncertainty.FctCuspEdgeIbp

/-!
# Uniform left-edge bound `|Φ_c(iτ)| ≤ C(K₄)` (`fct:splitting` (2))

Proves `fctPhiC_left_edge_bound`: uniformly for `c ≥ c₀`, `ε = ±1`, and `τ ∈ ℝ`,
`‖fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (iτ)‖ ≤ M` (`M` independent of `c`).

Follows Paper I (`constant_terms_five.tex`, proof of Lemma FCT.6(2), left-boundary bullet):
* On `t = iτ`, `Re Φ_Mel(iτ; ξ₁) = 0` (`re_mellinPhi_imag_eq_zero`), so `‖K₀(iτ, ξ₁)‖ ≍ (1 + τ²)^{-1/4}`.
* For `0 < τ ≤ K₀ c^{-1/3}`: direct integration on `[0, τ]` gives `‖Φ_c(iτ)‖ ≲ c τ³ ≤ K₀³`.
* For `τ ≥ K₀ c^{-1/3}`: `fctWarpI = 0` and one integration by parts on `[τ, ∞)` cancel `c` and yield
  `‖Φ_c(iτ)‖ ≤ C(K₄)` uniformly (`uR1_abs_le_const` gives linear-times-exponential decay of
  `deriv (ctHG ε ∘ (· * I))` on `|τ| ≥ 1`, and `m(t) ≥ 2|L₁|` gives `O(t^{-7/2})` derivative of `W`
  for `K₀ c^{-1/3} ≤ t ≤ 2`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter FormalResearch.Asymptotics FormalResearch.SignUncertainty.FctMoment FormalResearch.SignUncertainty.FctCompD

namespace FormalResearch.SignUncertainty

/-! ### 1. Purely imaginary `Φ_Mel` and `K₀` two-sided bounds -/

lemma stripG_imag_im_eq_zero {v : ℝ} (hv : v ≠ 0) :
    (stripG ((v : ℂ) * Complex.I)).im = 0 := by
  have hv_ne : ((v : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hv) Complex.I_ne_zero
  unfold stripG
  simp only [hv_ne, ↓reduceIte]
  set r : ℝ := Real.pi * v / 2
  have hr : r ≠ 0 := by positivity
  have hr_eq : (π : ℂ) * ((v : ℂ) * Complex.I) / 2 = (r : ℂ) * Complex.I := by
    simp only [r]; push_cast; ring
  have hcos_ne : Real.cosh r ≠ 0 := (Real.cosh_pos r).ne'
  have hq : 0 < Real.sinh r / (Real.cosh r * r) := by
    rcases lt_or_gt_of_ne hv with h | h
    · have hr0 : r < 0 := by simp only [r]; nlinarith [Real.pi_pos]
      exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hr0)
        (mul_neg_of_pos_of_neg (Real.cosh_pos r) hr0)
    · have hr0 : 0 < r := by simp only [r]; nlinarith [Real.pi_pos]
      exact div_pos (Real.sinh_pos_iff.mpr hr0) (mul_pos (Real.cosh_pos r) hr0)
  have htan : Complex.tan ((π : ℂ) * ((v : ℂ) * Complex.I) / 2) /
      ((π : ℂ) * ((v : ℂ) * Complex.I) / 2) =
      ((Real.sinh r / (Real.cosh r * r) : ℝ) : ℂ) := by
    rw [hr_eq, Complex.tan_eq_sin_div_cos, Complex.sin_mul_I, Complex.cos_mul_I,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
    have hchc : (Real.cosh r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos_ne
    have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp [hchc, hrc, hI]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
    field_simp [hcos_ne, hr]
  rw [htan, ← Complex.ofReal_log hq.le, Complex.ofReal_im]

lemma stripG_imag_eq_neg_m {v : ℝ} (hv : v ≠ 0) :
    stripG ((v : ℂ) * Complex.I) = (-(hankelEdgeM |v| : ℝ) : ℂ) := by
  have him : (stripG ((v : ℂ) * Complex.I)).im = 0 := stripG_imag_im_eq_zero hv
  have hre : (stripG ((v : ℂ) * Complex.I)).re = -hankelEdgeM |v| := by
    rcases lt_or_gt_of_ne hv with h | h
    · have hpos : 0 < -v := by linarith
      have heq : ((0 : ℝ) : ℂ) + ((-(-v) : ℝ) : ℂ) * Complex.I = (v : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      have hn := re_stripG_neg_im (s := 0) (τ := -v) hpos.ne'
      rw [heq] at hn
      rw [hn, re_stripG_imag hpos, abs_of_neg h]
    · have heq : ((0 : ℝ) : ℂ) + (v : ℂ) * Complex.I = (v : ℂ) * Complex.I := by simp
      rw [← heq, re_stripG_imag h, abs_of_pos h]
  apply Complex.ext <;> simp [hre, him]

lemma re_mellinPhi_imag_eq_zero {ξ : ℝ} (hξ : 0 < ξ) (u : ℝ) :
    (mellinPhi ((u : ℂ) * Complex.I) ξ).re = 0 := by
  let ψ : ℝ → ℝ := fun t => (mellinPhi ((t : ℂ) * Complex.I) ξ).re
  have hderiv : ∀ t : ℝ, HasDerivAt ψ 0 t := fun t => by
    have ht_abs : |((t : ℂ) * Complex.I).re| < 1 := by simp
    have hmp : HasDerivAt (fun t : ℂ => mellinPhi t ξ)
        (stripG ((t : ℂ) * Complex.I) + Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ))) ((t : ℂ) * Complex.I) := by
      have hS := hasDerivAt_stripS0Tilde (ζ₀ := (t : ℂ) * Complex.I) ht_abs
      have hl := ((hasDerivAt_id ((t : ℂ) * Complex.I)).mul_const
        (Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))).congr_deriv (one_mul _)
      have hfn : (fun y : ℂ => mellinPhi y ξ) =
          stripS0Tilde + fun y => y * Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)) := rfl
      rw [hfn]
      exact hS.add hl
    have hline : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
    have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hmp.comp t hline)
    have hzero : (Complex.reCLM ((stripG ((t : ℂ) * Complex.I) +
        Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ))) * Complex.I)) = 0 := by
      have him_g : (stripG ((t : ℂ) * Complex.I)).im = 0 := by
        by_cases ht0 : t = 0
        · subst ht0; simp [stripG]
        · exact stripG_imag_im_eq_zero ht0
      have him_log : (Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ))).im = 0 := by
        have hpos : (0 : ℝ) < Real.pi ^ 2 * ξ := by positivity
        rw [show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_log hpos.le, Complex.ofReal_im]
      simp [Complex.reCLM_apply, Complex.mul_re, him_g, him_log]
    rw [hzero] at hcomp
    exact hcomp
  have hconst := is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt)
    (fun t => (hderiv t).deriv) u 0
  simpa [ψ, mellinPhi, stripS0Tilde] using hconst

lemma mellinK0_imag_bounds {c : ℝ} (hc1 : 1 ≤ c) (L1 u : ℝ) :
    Real.exp (-(1 / 6)) * (1 + u ^ 2) ^ (-(1 / 4 : ℝ)) ≤ ‖mellinK0 c ((u : ℂ) * Complex.I) (fctXi1 L1)‖ ∧
      ‖mellinK0 c ((u : ℂ) * Complex.I) (fctXi1 L1)‖ ≤ Real.exp (1 / 6) := by
  have hcpos : 0 < c := by linarith
  have hre : (mellinPhi ((u : ℂ) * Complex.I) (fctXi1 L1)).re = 0 :=
    re_mellinPhi_imag_eq_zero (fctXi1_pos L1) u
  have hb := binetDiff_norm_le hcpos (ζ := (u : ℂ) * Complex.I) (by simp)
  have hbd : ‖binetDiff c ((u : ℂ) * Complex.I)‖ ≤ 1 / 6 := by
    have h0 : 1 / (12 * c) * (1 / (1 - ((u : ℂ) * Complex.I).re) + 1) ≤ 1 / (12 * 1) * (1 / 1 + 1) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      have h12 : (1 : ℝ) / (12 * c) ≤ 1 / (12 * 1) :=
        div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
      linarith
    linarith [hb, h0]
  have hbre : -(1 / 6 : ℝ) ≤ (binetDiff c ((u : ℂ) * Complex.I)).re ∧
      (binetDiff c ((u : ℂ) * Complex.I)).re ≤ 1 / 6 :=
    abs_le.mp ((Complex.abs_re_le_norm _).trans hbd)
  have hnorm_base : ‖1 - (u : ℂ) * Complex.I‖ = Real.sqrt (1 + u ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    congr 1
    simp [Complex.sub_re, Complex.sub_im]
  have hcpow : ‖(1 - (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))‖ = (1 + u ^ 2) ^ (-(1 / 4 : ℝ)) := by
    have hneg_half : -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hneg_half, Complex.norm_cpow_real, hnorm_base, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by positivity)]
    congr 1; ring
  have h1u : 1 ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg u]
  have hcp_le : (1 + u ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1u (by norm_num)
  unfold mellinK0
  rw [norm_mul, norm_mul, hcpow, Complex.norm_exp, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre, mul_zero, Real.exp_zero, mul_one]
  constructor
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbre.1) (by positivity)).trans_eq (mul_comm _ _)
  · calc (1 + u ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (binetDiff c ((u : ℂ) * Complex.I)).re
        ≤ 1 * Real.exp (1 / 6) := mul_le_mul hcp_le (Real.exp_le_exp.mpr hbre.2) (by positivity) zero_le_one
      _ = Real.exp (1 / 6) := one_mul _

/-! ### 2. Bounded derivative of `outerHbar(iτ)` and near/far bounds on `ctHG(iτ)` -/

lemma uR1_abs_le_const : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |uR1 t| ≤ C := by
  obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_uR1.continuousOn
  have hB0_nn : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0 ⟨by norm_num, by norm_num⟩)
  have hw_far : ∀ t : ℝ, 1 ≤ t → |w1 t| ≤ 2 * π + 2 := fun t ht => by
    have ht0 : 0 < t := by linarith
    have hpt : 0 ≤ π * t := by positivity
    have hsh_ge : π * t ≤ Real.sinh (π * t) := Real.self_le_sinh_iff.mpr hpt
    have hsh_pos : 0 < Real.sinh (π * t) := lt_of_lt_of_le (by positivity) hsh_ge
    have hcosh_le : Real.cosh (π * t) ≤ 2 * Real.sinh (π * t) := by
      rw [Real.cosh_eq, Real.sinh_eq]
      have he1 : (4 : ℝ) ≤ Real.exp (2 * (π * t)) := by
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have hesq : (4 : ℝ) ≤ Real.exp 2 := by
          calc (4 : ℝ) = 2 ^ 2 := by norm_num
            _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
            _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
        exact hesq.trans (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three]))
      have hexp : Real.exp (-(π * t)) ≤ (1 / 4 : ℝ) * Real.exp (π * t) := by
        have hm : Real.exp (-(π * t)) * Real.exp (2 * (π * t)) = Real.exp (π * t) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [← hm]
        calc Real.exp (-(π * t)) = Real.exp (-(π * t)) * (1 / 4 * 4) := by ring
          _ ≤ Real.exp (-(π * t)) * (1 / 4 * Real.exp (2 * (π * t))) := by gcongr
          _ = 1 / 4 * (Real.exp (-(π * t)) * Real.exp (2 * (π * t))) := by ring
      have := Real.exp_pos (π * t)
      linarith
    have hpi_term : |π ^ 2 * Real.cosh (π * t) / Real.sinh (π * t) ^ 2| ≤ 2 * π / t := by
      rw [abs_of_pos (by positivity)]
      calc π ^ 2 * Real.cosh (π * t) / Real.sinh (π * t) ^ 2
          ≤ π ^ 2 * (2 * Real.sinh (π * t)) / Real.sinh (π * t) ^ 2 := by gcongr
        _ = 2 * π ^ 2 / Real.sinh (π * t) := by
            have := hsh_pos.ne'; field_simp
        _ ≤ 2 * π ^ 2 / (π * t) := div_le_div_of_nonneg_left (by positivity) (by positivity) hsh_ge
        _ = 2 * π / t := by
            have := Real.pi_pos.ne'; field_simp
    have hmP : |mP1 t| ≤ (1 + 2 * π) / t := by
      unfold mP1
      have ht1 : 1 / t ^ 2 ≤ 1 / t := one_div_le_one_div_of_le ht0 (by nlinarith)
      calc |-1 / t ^ 2 + π ^ 2 * Real.cosh (π * t) / Real.sinh (π * t) ^ 2|
          ≤ |-1 / t ^ 2| + |π ^ 2 * Real.cosh (π * t) / Real.sinh (π * t) ^ 2| := abs_add_le _ _
        _ = 1 / t ^ 2 + |π ^ 2 * Real.cosh (π * t) / Real.sinh (π * t) ^ 2| := by
            rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity)]
        _ ≤ 1 / t + 2 * π / t := by linarith [ht1, hpi_term]
        _ = (1 + 2 * π) / t := by ring
    have ha : |mP1 t / mPrime t| ≤ 2 * (1 + 2 * π) := by
      rw [abs_div, abs_of_pos (mPrime_pos ht0), div_eq_mul_one_div]
      calc |mP1 t| * (1 / mPrime t) ≤ ((1 + 2 * π) / t) * (2 * t) :=
            mul_le_mul hmP (inv_mPrime_le ht) (one_div_nonneg.mpr (mPrime_pos ht0).le) (by positivity)
        _ = 2 * (1 + 2 * π) := by field_simp [ht0.ne']
    have h2 : |1 / t| ≤ 1 := by rw [abs_of_pos (by positivity), div_le_one ht0]; exact ht
    have h3 : |2 * t / (1 + t ^ 2)| ≤ 1 := by
      rw [abs_of_pos (by positivity), div_le_one (by positivity)]
      nlinarith [sq_nonneg (t - 1)]
    unfold w1
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have htr1 := abs_sub (mP1 t / mPrime t - 1 / t) (2 * t / (1 + t ^ 2))
    have htr2 := abs_sub (mP1 t / mPrime t) (1 / t)
    linarith
  refine ⟨max B0 (2 * π + 2), by positivity, fun t => ?_⟩
  rcases le_or_gt 1 |t| with h1 | h1
  · rcases le_total 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at h1
      rw [uR1_eq (by linarith)]
      exact (hw_far t h1).trans (le_max_right _ _)
    · rw [abs_of_nonpos h0] at h1
      have e : uR1 t = -uR1 (-t) := by rw [uR1_neg]; ring
      rw [e, abs_neg, uR1_eq (by linarith)]
      exact (hw_far (-t) h1).trans (le_max_right _ _)
  · have hmem : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(abs_lt.mp h1).1], by linarith [(abs_lt.mp h1).2]⟩
    have hb := hB0 t hmem
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (le_max_left _ _)

lemma outerHbar_imag_deriv_le : ∃ C_h : ℝ, 0 ≤ C_h ∧
    ContDiff ℝ 2 (fun τ : ℝ => Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))) ∧
    ∀ τ : ℝ, ‖deriv (fun s : ℝ => outerHbar ((s : ℂ) * Complex.I)) τ‖ ≤ C_h := by
  obtain ⟨Cu, hCu0, hu1⟩ := uR1_abs_le_const
  obtain ⟨Cθ, hCθ0, _, ht1, _⟩ := theta_env
  obtain ⟨_, ha1, _⟩ := arctan_env
  have hθcd : ContDiff ℝ 2 (outerTheta (-1)) := (contDiff_outerTheta (-1)).of_le (by simp)
  have hucd : ContDiff ℝ 2 uR := contDiff_uR.of_le (by simp)
  have hfun : (fun s : ℝ => outerHbar ((s : ℂ) * Complex.I)) = fun s : ℝ =>
      ((uR s : ℝ) : ℂ) + Complex.I * ((outerTheta (-1) s : ℝ) : ℂ) + Complex.I * ((Real.arctan s : ℝ) : ℂ) := by
    funext s; rw [mul_comm (s : ℂ) Complex.I, outerHbar_edge]
  have hcd : ContDiff ℝ 2 (fun s : ℝ => outerHbar ((s : ℂ) * Complex.I)) := by
    rw [hfun]
    have h1 : ContDiff ℝ 2 (fun s : ℝ => ((uR s : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hucd
    have h2 : ContDiff ℝ 2 (fun s : ℝ => ((outerTheta (-1) s : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hθcd
    have h3 : ContDiff ℝ 2 (fun s : ℝ => ((Real.arctan s : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp Real.contDiff_arctan
    exact (h1.add (contDiff_const.mul h2)).add (contDiff_const.mul h3)
  refine ⟨Cu + Cθ + 1, by positivity, hcd.neg.cexp, fun τ => ?_⟩
  have hdu : HasDerivAt (fun s : ℝ => ((uR s : ℝ) : ℂ)) ((uR1 τ : ℝ) : ℂ) τ :=
    (hasDerivAt_uR τ).ofReal_comp
  have hdθ : HasDerivAt (fun s : ℝ => Complex.I * ((outerTheta (-1) s : ℝ) : ℂ))
      (Complex.I * ((deriv (outerTheta (-1)) τ : ℝ) : ℂ)) τ :=
    (((hθcd.differentiable (by simp)) τ).hasDerivAt.ofReal_comp).const_mul Complex.I
  have hda : HasDerivAt (fun s : ℝ => Complex.I * ((Real.arctan s : ℝ) : ℂ))
      (Complex.I * ((deriv Real.arctan τ : ℝ) : ℂ)) τ :=
    (((Real.contDiff_arctan (n := 2)).differentiable (by simp) τ).hasDerivAt.ofReal_comp).const_mul Complex.I
  have hdsum : HasDerivAt (fun s : ℝ => outerHbar ((s : ℂ) * Complex.I))
      (((uR1 τ : ℝ) : ℂ) + Complex.I * ((deriv (outerTheta (-1)) τ : ℝ) : ℂ) +
        Complex.I * ((deriv Real.arctan τ : ℝ) : ℂ)) τ := by
    rw [hfun]; exact (hdu.add hdθ).add hda
  rw [hdsum.deriv]
  calc ‖((uR1 τ : ℝ) : ℂ) + Complex.I * ((deriv (outerTheta (-1)) τ : ℝ) : ℂ) +
          Complex.I * ((deriv Real.arctan τ : ℝ) : ℂ)‖
      ≤ ‖((uR1 τ : ℝ) : ℂ) + Complex.I * ((deriv (outerTheta (-1)) τ : ℝ) : ℂ)‖ +
          ‖Complex.I * ((deriv Real.arctan τ : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖((uR1 τ : ℝ) : ℂ)‖ + ‖Complex.I * ((deriv (outerTheta (-1)) τ : ℝ) : ℂ)‖ +
          ‖Complex.I * ((deriv Real.arctan τ : ℝ) : ℂ)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = |uR1 τ| + |deriv (outerTheta (-1)) τ| + |deriv Real.arctan τ| := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    _ ≤ Cu + Cθ + 1 := add_le_add (add_le_add (hu1 τ) (ht1 τ)) (ha1 τ)

lemma ctHG_imag_far_deriv_le (ε : ℝ) : ∃ C_d : ℝ, 0 ≤ C_d ∧
    ContDiffOn ℝ 2 (fun τ : ℝ => ctHG ε ((τ : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} ∧
    ∀ τ : ℝ, 1 ≤ |τ| →
      ‖ctHG ε ((τ : ℂ) * Complex.I)‖ ≤ C_d * (1 + |τ|) * Real.exp (-(π * |τ|)) ∧
      ‖deriv (fun s : ℝ => ctHG ε ((s : ℂ) * Complex.I)) τ‖ ≤ C_d * (1 + |τ|) * Real.exp (-(π * |τ|)) := by
  obtain ⟨CZ, hCZ0, hZ⟩ := env2_seedZi ε
  obtain ⟨Ch, hCh0, hE_cd, hOh_d⟩ := outerHbar_imag_deriv_le
  obtain ⟨CE, hCE⟩ := norm_exp_neg_outerHbar_le
  set CE' := max CE 0
  have hCE'_0 : 0 ≤ CE' := le_max_right _ _
  have hZ_fun : (fun τ : ℝ => uctSeedZ ε ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ => uctSeedZ ε (0 + Complex.I * (τ : ℂ)) := by funext τ; congr 1; ring
  have hE_ub : ∀ τ : ℝ, ‖Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))‖ ≤ CE' * (1 + |τ|) ^ 2 := fun τ => by
    have h1 := hCE ((τ : ℂ) * Complex.I) ⟨by simp, by simp⟩
    have h1' : ‖Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))‖ ≤ CE * (1 + |τ| ^ 2) := by
      rw [sq_abs]; simpa using h1
    have hle1 : CE * (1 + |τ| ^ 2) ≤ CE' * (1 + |τ| ^ 2) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hle2 : CE' * (1 + |τ| ^ 2) ≤ CE' * (1 + |τ|) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith [abs_nonneg τ]) hCE'_0
    exact h1'.trans (hle1.trans hle2)
  have hE_d1 : ∀ τ : ℝ, ‖deriv (fun s : ℝ => Complex.exp (-outerHbar ((s : ℂ) * Complex.I))) τ‖ ≤
      Ch * CE' * (1 + |τ|) ^ 2 := fun τ => by
    have hfun : (fun s : ℝ => outerHbar ((s : ℂ) * Complex.I)) = fun s : ℝ =>
        ((uR s : ℝ) : ℂ) + Complex.I * ((outerTheta (-1) s : ℝ) : ℂ) + Complex.I * ((Real.arctan s : ℝ) : ℂ) := by
      funext s; rw [mul_comm (s : ℂ) Complex.I, outerHbar_edge]
    have hd_cd : ContDiff ℝ 2 (fun s : ℝ => outerHbar ((s : ℂ) * Complex.I)) := by
      rw [hfun]
      exact ((Complex.ofRealCLM.contDiff.comp (contDiff_uR.of_le (by simp))).add
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ((contDiff_outerTheta (-1)).of_le (by simp))))).add
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp Real.contDiff_arctan))
    have hd : HasDerivAt (fun s : ℝ => outerHbar ((s : ℂ) * Complex.I))
        (deriv (fun s : ℝ => outerHbar ((s : ℂ) * Complex.I)) τ) τ :=
      ((hd_cd.differentiable (by simp)) τ).hasDerivAt
    have he := hd.neg.cexp
    have he_eq : (fun s : ℝ => Complex.exp (-outerHbar ((s : ℂ) * Complex.I))) =
        (fun x : ℝ => Complex.exp ((-fun s : ℝ => outerHbar ((s : ℂ) * Complex.I)) x)) := rfl
    rw [he_eq, he.deriv, norm_mul, norm_neg]
    exact (mul_le_mul (hE_ub τ) (hOh_d τ) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hRS_c2 : ContDiffOn ℝ 2 (fun τ : ℝ => edgeR τ * edgeS τ) {τ : ℝ | τ ≠ 0} :=
    edgeR_EJ.c2.mul edgeS_EJ.c2
  have hRS_bd : ∀ τ : ℝ, 1 ≤ |τ| →
      ‖edgeR τ * edgeS τ‖ ≤ 32 * (1 + |τ|) ^ (-5 : ℝ) ∧
      ‖deriv (fun s : ℝ => edgeR s * edgeS s) τ‖ ≤ 320 * (1 + |τ|) ^ (-5 : ℝ) := fun τ hτ => by
    have hτ0 : τ ≠ 0 := fun h => by rw [h, abs_zero] at hτ; norm_num at hτ
    have hτpos : 0 < |τ| := abs_pos.mpr hτ0
    have h1τ : (0 : ℝ) < 1 + |τ| := by linarith
    have hτ_ge : (1 / 2 : ℝ) * (1 + |τ|) ≤ |τ| := by linarith
    have hS0 : ‖edgeS τ‖ = |τ| ^ (-(5 / 2 : ℝ)) := norm_cpow_line_I hτ0 (-(5 / 2))
    have hR0 : ‖edgeR τ‖ ≤ |τ| ^ (-(5 / 2 : ℝ)) := by
      have hz0 : (1 : ℂ) + (-Complex.I) * (τ : ℂ) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this
      unfold edgeR
      rw [Complex.norm_cpow_of_ne_zero hz0]
      simp only [Complex.ofReal_im, mul_zero, Real.exp_zero, div_one]
      have him_ge : |τ| ≤ ‖(1 : ℂ) + (-Complex.I) * (τ : ℂ)‖ := by
        simpa using Complex.abs_im_le_norm ((1 : ℂ) + (-Complex.I) * (τ : ℂ))
      exact Real.rpow_le_rpow_of_nonpos hτpos him_ge (by norm_num)
    have hS1 : ‖deriv edgeS τ‖ ≤ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ)) := by
      have hd := (cpow_line_deriv (0 : ℂ) Complex.I (((-(5 / 2) : ℝ)) : ℂ) isOpen_ne
        (fun t ht => slit_I ht) hτ0).1
      have e : (((-(5 / 2) : ℝ) : ℂ) - 1) = (((-(7 / 2) : ℝ)) : ℂ) := by push_cast; ring
      show ‖deriv edgeS τ‖ ≤ _
      unfold edgeS
      rw [hd, e, norm_mul, norm_mul, norm_cpow_line_I hτ0]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_neg, Complex.norm_I, mul_one]
      have hsub : |τ| ^ (-(7 / 2 : ℝ)) ≤ |τ| ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hτ (by norm_num)
      calc |(5 / 2 : ℝ)| * |τ| ^ (-(7 / 2 : ℝ)) = (5 / 2 : ℝ) * |τ| ^ (-(7 / 2 : ℝ)) := by norm_num
        _ ≤ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ)) := by gcongr
    have hR1 : ‖deriv edgeR τ‖ ≤ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ)) := by
      have hd := (cpow_line_deriv (1 : ℂ) (-Complex.I) (((-(5 / 2) : ℝ)) : ℂ) isOpen_ne
        (fun t _ => slit_one_sub t) hτ0).1
      have e : (((-(5 / 2) : ℝ) : ℂ) - 1) = (((-(7 / 2) : ℝ)) : ℂ) := by push_cast; ring
      have hz0 : (1 : ℂ) + (-Complex.I) * (τ : ℂ) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this
      have him_ge : |τ| ≤ ‖(1 : ℂ) + (-Complex.I) * (τ : ℂ)‖ := by
        simpa using Complex.abs_im_le_norm ((1 : ℂ) + (-Complex.I) * (τ : ℂ))
      show ‖deriv edgeR τ‖ ≤ _
      unfold edgeR
      rw [hd, e, norm_mul, norm_mul, Complex.norm_cpow_of_ne_zero hz0]
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_neg, Complex.norm_I, mul_one,
        Complex.ofReal_im, mul_zero, Real.exp_zero, div_one]
      have hpow : ‖(1 : ℂ) + (-Complex.I) * (τ : ℂ)‖ ^ (-(7 / 2 : ℝ)) ≤ |τ| ^ (-(7 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hτpos him_ge (by norm_num)
      have hsub : |τ| ^ (-(7 / 2 : ℝ)) ≤ |τ| ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hτ (by norm_num)
      calc |(5 / 2 : ℝ)| * ‖(1 : ℂ) + (-Complex.I) * (τ : ℂ)‖ ^ (-(7 / 2 : ℝ))
          = (5 / 2 : ℝ) * ‖(1 : ℂ) + (-Complex.I) * (τ : ℂ)‖ ^ (-(7 / 2 : ℝ)) := by norm_num
        _ ≤ (5 / 2 : ℝ) * |τ| ^ (-(7 / 2 : ℝ)) := by gcongr
        _ ≤ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ)) := by gcongr
    have hpow_cmp : |τ| ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (-(5 / 2 : ℝ)) := by
      have h1 : |τ| ^ (-(5 / 2 : ℝ)) ≤ ((1 / 2 : ℝ) * (1 + |τ|)) ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hτ_ge (by norm_num)
      rw [Real.mul_rpow (by norm_num) h1τ.le,
        show (1 / 2 : ℝ) ^ (-(5 / 2 : ℝ)) = 2 ^ (5 / 2 : ℝ) by
          rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]] at h1
      exact h1
    have h25_sq : (2 : ℝ) ^ (5 / 2 : ℝ) * (2 : ℝ) ^ (5 / 2 : ℝ) ≤ 32 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num
    have hadd52 : (1 + |τ|) ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ (-(5 / 2 : ℝ)) = (1 + |τ|) ^ (-5 : ℝ) := by
      rw [← Real.rpow_add h1τ]; congr 1; norm_num
    constructor
    · calc ‖edgeR τ * edgeS τ‖ = ‖edgeR τ‖ * ‖edgeS τ‖ := norm_mul _ _
        _ ≤ |τ| ^ (-(5 / 2 : ℝ)) * |τ| ^ (-(5 / 2 : ℝ)) := by rw [hS0]; gcongr
        _ ≤ ((2 : ℝ) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (-(5 / 2 : ℝ))) *
              ((2 : ℝ) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul hpow_cmp hpow_cmp (by positivity) (by positivity)
        _ = ((2 : ℝ) ^ (5 / 2 : ℝ) * (2 : ℝ) ^ (5 / 2 : ℝ)) *
              ((1 + |τ|) ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ (-(5 / 2 : ℝ))) := by ring
        _ ≤ 32 * (1 + |τ|) ^ (-5 : ℝ) := by rw [hadd52]; gcongr
    · have hnh : {t : ℝ | t ≠ 0} ∈ 𝓝 τ := isOpen_ne.mem_nhds hτ0
      have hdR : DifferentiableAt ℝ edgeR τ := ((edgeR_EJ.c2.differentiableOn (by norm_num)).differentiableAt hnh)
      have hdS : DifferentiableAt ℝ edgeS τ := ((edgeS_EJ.c2.differentiableOn (by norm_num)).differentiableAt hnh)
      have hderiv_eq : deriv (fun s : ℝ => edgeR s * edgeS s) τ = deriv edgeR τ * edgeS τ + edgeR τ * deriv edgeS τ :=
        deriv_mul hdR hdS
      rw [hderiv_eq]
      calc ‖deriv edgeR τ * edgeS τ + edgeR τ * deriv edgeS τ‖
          ≤ ‖deriv edgeR τ‖ * ‖edgeS τ‖ + ‖edgeR τ‖ * ‖deriv edgeS τ‖ := by
              simpa [norm_mul] using norm_add_le (deriv edgeR τ * edgeS τ) (edgeR τ * deriv edgeS τ)
        _ ≤ ((5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) * |τ| ^ (-(5 / 2 : ℝ)) +
              |τ| ^ (-(5 / 2 : ℝ)) * ((5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) := by
              rw [hS0]; exact add_le_add (mul_le_mul_of_nonneg_right hR1 (by positivity))
                (mul_le_mul hR0 hS1 (norm_nonneg _) (by positivity))
        _ = 5 * (|τ| ^ (-(5 / 2 : ℝ)) * |τ| ^ (-(5 / 2 : ℝ))) := by ring
        _ ≤ 5 * (32 * (1 + |τ|) ^ (-5 : ℝ)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              calc |τ| ^ (-(5 / 2 : ℝ)) * |τ| ^ (-(5 / 2 : ℝ))
                  ≤ ((2 : ℝ) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (-(5 / 2 : ℝ))) *
                      ((2 : ℝ) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (-(5 / 2 : ℝ))) :=
                    mul_le_mul hpow_cmp hpow_cmp (by positivity) (by positivity)
                _ = ((2 : ℝ) ^ (5 / 2 : ℝ) * (2 : ℝ) ^ (5 / 2 : ℝ)) * (1 + |τ|) ^ (-5 : ℝ) := by
                    rw [← hadd52]; ring
                _ ≤ 32 * (1 + |τ|) ^ (-5 : ℝ) := by gcongr
        _ ≤ 320 * (1 + |τ|) ^ (-5 : ℝ) := by linarith [Real.rpow_pos_of_pos h1τ (-5)]
  have hHG_c2 : ContDiffOn ℝ 2 (fun τ : ℝ => ctHG ε ((τ : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} := by
    have hZ_cd : ContDiff ℝ 2 (fun τ : ℝ => uctSeedZ ε ((τ : ℂ) * Complex.I)) := by
      rw [hZ_fun]; exact hZ.1
    exact (((hZ_cd.contDiffOn).mul hE_cd.contDiffOn).mul hRS_c2).congr fun τ _ => by
      rw [ctHG_edge]; ring
  set C_d : ℝ := max (CZ * CE' * 32) (CZ * CE' * 320 + CZ * (Ch * CE') * 32 + CZ * CE' * 32)
  refine ⟨C_d, by positivity, hHG_c2, fun τ hτ => ?_⟩
  have hτ0 : τ ≠ 0 := fun h => by rw [h, abs_zero] at hτ; norm_num at hτ
  have h1τ : (0 : ℝ) < 1 + |τ| := by linarith
  have hZ_01 := hZ.2 τ
  rw [← hZ_fun] at hZ_01
  have hZ0 : ‖uctSeedZ ε ((τ : ℂ) * Complex.I)‖ ≤ CZ * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|))) := hZ_01.1
  have hZ1 : ‖deriv (fun s : ℝ => uctSeedZ ε ((s : ℂ) * Complex.I)) τ‖ ≤
      CZ * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|))) := by
    simpa [hZ_fun] using hZ_01.2.1
  obtain ⟨hRS0, hRS1⟩ := hRS_bd τ hτ
  have hpow425 : (1 + |τ|) ^ 4 * (1 + |τ|) ^ 2 * (1 + |τ|) ^ (-5 : ℝ) = 1 + |τ| := by
    rw [show (1 + |τ|) ^ 4 * (1 + |τ|) ^ 2 = (1 + |τ|) ^ ((6 : ℝ)) by norm_cast; ring]
    rw [← Real.rpow_add h1τ]; norm_num
  have hct_eq : (fun s : ℝ => ctHG ε ((s : ℂ) * Complex.I)) =
      fun s : ℝ => (uctSeedZ ε ((s : ℂ) * Complex.I) * Complex.exp (-outerHbar ((s : ℂ) * Complex.I))) *
        (edgeR s * edgeS s) := funext fun s => by rw [ctHG_edge]; ring
  constructor
  · change ‖(fun s : ℝ => ctHG ε ((s : ℂ) * Complex.I)) τ‖ ≤ _
    rw [hct_eq, norm_mul, norm_mul]
    calc ‖uctSeedZ ε ((τ : ℂ) * Complex.I)‖ * ‖Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))‖ * ‖edgeR τ * edgeS τ‖
        ≤ (CZ * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|)))) * (CE' * (1 + |τ|) ^ 2) * (32 * (1 + |τ|) ^ (-5 : ℝ)) :=
          mul_le_mul (mul_le_mul hZ0 (hE_ub τ) (norm_nonneg _) (by positivity)) hRS0 (norm_nonneg _) (by positivity)
      _ = (CZ * CE' * 32) * ((1 + |τ|) ^ 4 * (1 + |τ|) ^ 2 * (1 + |τ|) ^ (-5 : ℝ)) * Real.exp (-(π * |τ|)) := by ring
      _ ≤ C_d * (1 + |τ|) * Real.exp (-(π * |τ|)) := by
          rw [hpow425]; gcongr; exact le_max_left _ _
  · have hZ_cd : ContDiff ℝ 2 (fun s : ℝ => uctSeedZ ε ((s : ℂ) * Complex.I)) := by
      rw [hZ_fun]; exact hZ.1
    have hdZ : DifferentiableAt ℝ (fun s : ℝ => uctSeedZ ε ((s : ℂ) * Complex.I)) τ :=
      (hZ_cd.differentiable (by simp)) τ
    have hdE : DifferentiableAt ℝ (fun s : ℝ => Complex.exp (-outerHbar ((s : ℂ) * Complex.I))) τ :=
      (hE_cd.differentiable (by simp)) τ
    have hdRS : DifferentiableAt ℝ (fun s : ℝ => edgeR s * edgeS s) τ :=
      ((hRS_c2.differentiableOn (by norm_num)).differentiableAt (isOpen_ne.mem_nhds hτ0))
    have hder : deriv (fun s : ℝ => ctHG ε ((s : ℂ) * Complex.I)) τ =
        (deriv (fun s : ℝ => uctSeedZ ε ((s : ℂ) * Complex.I)) τ * Complex.exp (-outerHbar ((τ : ℂ) * Complex.I)) +
          uctSeedZ ε ((τ : ℂ) * Complex.I) * deriv (fun s : ℝ => Complex.exp (-outerHbar ((s : ℂ) * Complex.I))) τ) *
          (edgeR τ * edgeS τ) +
        (uctSeedZ ε ((τ : ℂ) * Complex.I) * Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))) *
          deriv (fun s : ℝ => edgeR s * edgeS s) τ := by
      have hct_mul : (fun s : ℝ => ctHG ε ((s : ℂ) * Complex.I)) =
          ((fun s : ℝ => uctSeedZ ε ((s : ℂ) * Complex.I)) *
            (fun s : ℝ => Complex.exp (-outerHbar ((s : ℂ) * Complex.I)))) *
          (fun s : ℝ => edgeR s * edgeS s) :=
        funext fun s => by simp only [Pi.mul_apply]; exact congrFun hct_eq s
      rw [hct_mul, deriv_mul (hdZ.mul hdE) hdRS, deriv_mul hdZ hdE, Pi.mul_apply]
    rw [hder]
    have ht1 : ‖deriv (fun s : ℝ => uctSeedZ ε ((s : ℂ) * Complex.I)) τ‖ *
          ‖Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))‖ * ‖edgeR τ * edgeS τ‖ ≤
        (CZ * CE' * 32) * (1 + |τ|) * Real.exp (-(π * |τ|)) := by
      calc _ ≤ (CZ * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|)))) * (CE' * (1 + |τ|) ^ 2) * (32 * (1 + |τ|) ^ (-5 : ℝ)) :=
            mul_le_mul (mul_le_mul hZ1 (hE_ub τ) (norm_nonneg _) (by positivity)) hRS0 (norm_nonneg _) (by positivity)
        _ = (CZ * CE' * 32) * ((1 + |τ|) ^ 4 * (1 + |τ|) ^ 2 * (1 + |τ|) ^ (-5 : ℝ)) * Real.exp (-(π * |τ|)) := by ring
        _ = (CZ * CE' * 32) * (1 + |τ|) * Real.exp (-(π * |τ|)) := by rw [hpow425]
    have ht2 : ‖uctSeedZ ε ((τ : ℂ) * Complex.I)‖ *
          ‖deriv (fun s : ℝ => Complex.exp (-outerHbar ((s : ℂ) * Complex.I))) τ‖ * ‖edgeR τ * edgeS τ‖ ≤
        (CZ * (Ch * CE') * 32) * (1 + |τ|) * Real.exp (-(π * |τ|)) := by
      calc _ ≤ (CZ * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|)))) * (Ch * CE' * (1 + |τ|) ^ 2) * (32 * (1 + |τ|) ^ (-5 : ℝ)) :=
            mul_le_mul (mul_le_mul hZ0 (hE_d1 τ) (norm_nonneg _) (by positivity)) hRS0 (norm_nonneg _) (by positivity)
        _ = (CZ * (Ch * CE') * 32) * ((1 + |τ|) ^ 4 * (1 + |τ|) ^ 2 * (1 + |τ|) ^ (-5 : ℝ)) * Real.exp (-(π * |τ|)) := by ring
        _ = (CZ * (Ch * CE') * 32) * (1 + |τ|) * Real.exp (-(π * |τ|)) := by rw [hpow425]
    have ht3 : ‖uctSeedZ ε ((τ : ℂ) * Complex.I)‖ *
          ‖Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))‖ * ‖deriv (fun s : ℝ => edgeR s * edgeS s) τ‖ ≤
        (CZ * CE' * 320) * (1 + |τ|) * Real.exp (-(π * |τ|)) := by
      calc _ ≤ (CZ * ((1 + |τ|) ^ 4 * Real.exp (-(π * |τ|)))) * (CE' * (1 + |τ|) ^ 2) * (320 * (1 + |τ|) ^ (-5 : ℝ)) :=
            mul_le_mul (mul_le_mul hZ0 (hE_ub τ) (norm_nonneg _) (by positivity)) hRS1 (norm_nonneg _) (by positivity)
        _ = (CZ * CE' * 320) * ((1 + |τ|) ^ 4 * (1 + |τ|) ^ 2 * (1 + |τ|) ^ (-5 : ℝ)) * Real.exp (-(π * |τ|)) := by ring
        _ = (CZ * CE' * 320) * (1 + |τ|) * Real.exp (-(π * |τ|)) := by rw [hpow425]
    refine (norm_add_le _ _).trans ?_
    calc ‖(deriv (fun s : ℝ => uctSeedZ ε ((s : ℂ) * Complex.I)) τ *
            Complex.exp (-outerHbar ((τ : ℂ) * Complex.I)) +
            uctSeedZ ε ((τ : ℂ) * Complex.I) *
              deriv (fun s : ℝ => Complex.exp (-outerHbar ((s : ℂ) * Complex.I))) τ) *
            (edgeR τ * edgeS τ)‖ +
          ‖uctSeedZ ε ((τ : ℂ) * Complex.I) *
            Complex.exp (-outerHbar ((τ : ℂ) * Complex.I)) * deriv (fun s : ℝ => edgeR s * edgeS s) τ‖
        ≤ (‖deriv (fun s : ℝ => uctSeedZ ε ((s : ℂ) * Complex.I)) τ‖ *
              ‖Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))‖ +
            ‖uctSeedZ ε ((τ : ℂ) * Complex.I)‖ *
              ‖deriv (fun s : ℝ => Complex.exp (-outerHbar ((s : ℂ) * Complex.I))) τ‖) *
            ‖edgeR τ * edgeS τ‖ +
          ‖uctSeedZ ε ((τ : ℂ) * Complex.I)‖ *
            ‖Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))‖ *
            ‖deriv (fun s : ℝ => edgeR s * edgeS s) τ‖ := by
          refine add_le_add ?_ (by simp only [norm_mul]; exact le_rfl)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            ((norm_add_le _ _).trans (by simp only [norm_mul]; exact le_rfl)) (norm_nonneg _)
      _ = (‖deriv (fun s : ℝ => uctSeedZ ε ((s : ℂ) * Complex.I)) τ‖ *
            ‖Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))‖ * ‖edgeR τ * edgeS τ‖ +
          ‖uctSeedZ ε ((τ : ℂ) * Complex.I)‖ *
            ‖deriv (fun s : ℝ => Complex.exp (-outerHbar ((s : ℂ) * Complex.I))) τ‖ * ‖edgeR τ * edgeS τ‖) +
          ‖uctSeedZ ε ((τ : ℂ) * Complex.I)‖ *
            ‖Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))‖ * ‖deriv (fun s : ℝ => edgeR s * edgeS s) τ‖ := by ring
      _ ≤ ((CZ * CE' * 32) * (1 + |τ|) * Real.exp (-(π * |τ|)) +
            (CZ * (Ch * CE') * 32) * (1 + |τ|) * Real.exp (-(π * |τ|))) +
            (CZ * CE' * 320) * (1 + |τ|) * Real.exp (-(π * |τ|)) := add_le_add (add_le_add ht1 ht2) ht3
      _ = (CZ * CE' * 320 + CZ * (Ch * CE') * 32 + CZ * CE' * 32) * (1 + |τ|) * Real.exp (-(π * |τ|)) := by ring
      _ ≤ C_d * (1 + |τ|) * Real.exp (-(π * |τ|)) := by gcongr; exact le_max_right _ _

lemma ctHG_imag_near_bounds (ε : ℝ) : ∃ C_n C_inv : ℝ, 0 ≤ C_n ∧ 0 ≤ C_inv ∧
    (∀ τ : ℝ, 0 < τ → τ ≤ 2 →
      ‖ctHG ε ((τ : ℂ) * Complex.I)‖ ≤ C_n * τ ^ (-(5 / 2 : ℝ)) ∧
      ‖deriv (fun s : ℝ => ctHG ε ((s : ℂ) * Complex.I)) τ‖ ≤ C_n * τ ^ (-(7 / 2 : ℝ)) ∧
      ‖(ctHG ε ((τ : ℂ) * Complex.I))⁻¹‖ ≤ C_inv * τ ^ (5 / 2 : ℝ)) := by
  obtain ⟨MZ, hZE⟩ := ejZE ε
  have hprod : EJ (fun τ : ℝ => ctHG ε ((τ : ℂ) * Complex.I))
      (-(5 / 2 : ℝ)) 10 1 (4 * (4 * MZ * 9) * 9) := by
    have hp := (hZE.mul edgeR_EJ).mul edgeS_EJ
    have heq : (fun τ : ℝ =>
        uctSeedZ ε ((τ : ℂ) * Complex.I) * Complex.exp (-outerHbar ((τ : ℂ) * Complex.I)) *
          edgeR τ * edgeS τ) = fun τ : ℝ => ctHG ε ((τ : ℂ) * Complex.I) :=
      funext fun τ => (ctHG_edge ε τ).symm
    rw [heq] at hp
    exact hp.cast (a' := -(5 / 2 : ℝ)) (b' := 1) (by norm_num) (by norm_num)
  obtain ⟨MH, hMH0, hMH⟩ := ctHG_inv_near_zero ε
  have hcont : ContinuousOn (fun τ : ℝ => (ctHG ε ((τ : ℂ) * Complex.I))⁻¹) (Icc (1 / 4 : ℝ) 2) := by
    refine ((ctHG_continuousOn ε).comp (by fun_prop) fun τ hτ => ?_).inv₀ fun τ hτ => ?_
    · refine ⟨⟨by simp, by simp⟩, by simp; linarith [hτ.1], ?_⟩
      intro h1; have := congrArg Complex.re h1; simp at this
    · exact ctHG_ne_zero_of_closed_band ε (by simp) (by simp) (by simp; linarith [hτ.1])
  obtain ⟨Mmid, hMmid⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set C_n : ℝ := 4 * (4 * MZ * 9) * 9 * 3 ^ 11
  set C_inv : ℝ := max MH (32 * |Mmid|)
  refine ⟨C_n, C_inv, mul_nonneg hprod.hM (by positivity), le_max_of_le_left hMH0, fun τ hτ0 hτ2 => ?_⟩
  have hτ_abs : |τ| = τ := abs_of_pos hτ0
  have h1τ : 1 + τ ≤ 3 := by linarith
  have hexp : Real.exp (-(π * 1 * τ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hb0 : ‖ctHG ε ((τ : ℂ) * Complex.I)‖ ≤ C_n * τ ^ (-(5 / 2 : ℝ)) := by
    have h := hprod.b0 τ hτ0.ne'
    unfold ejW at h
    simp only [Nat.cast_zero, sub_zero, add_zero, hτ_abs] at h
    have hpow : (1 + τ) ^ 10 ≤ 3 ^ 11 :=
      (pow_le_pow_left₀ (by positivity) h1τ 10).trans (pow_le_pow_right₀ (by norm_num) (by norm_num))
    calc ‖ctHG ε ((τ : ℂ) * Complex.I)‖
        ≤ (4 * (4 * MZ * 9) * 9) * (τ ^ (-(5 / 2 : ℝ)) * (1 + τ) ^ 10 * Real.exp (-(π * 1 * τ))) := h
      _ ≤ (4 * (4 * MZ * 9) * 9) * (τ ^ (-(5 / 2 : ℝ)) * 3 ^ 11 * 1) := by
          have := hprod.hM; gcongr
      _ = C_n * τ ^ (-(5 / 2 : ℝ)) := by simp only [C_n]; ring
  have hb1 : ‖deriv (fun s : ℝ => ctHG ε ((s : ℂ) * Complex.I)) τ‖ ≤ C_n * τ ^ (-(7 / 2 : ℝ)) := by
    have h := hprod.b1 τ hτ0.ne'
    unfold ejW at h
    simp only [Nat.cast_one, hτ_abs] at h
    have hpow : (1 + τ) ^ 11 ≤ 3 ^ 11 := pow_le_pow_left₀ (by positivity) h1τ 11
    calc ‖deriv (fun s : ℝ => ctHG ε ((s : ℂ) * Complex.I)) τ‖
        ≤ (4 * (4 * MZ * 9) * 9) * (τ ^ (-(5 / 2 : ℝ) - 1) * (1 + τ) ^ (10 + 1) * Real.exp (-(π * 1 * τ))) := h
      _ ≤ (4 * (4 * MZ * 9) * 9) * (τ ^ (-(7 / 2 : ℝ)) * 3 ^ 11 * 1) := by
          rw [show -(5 / 2 : ℝ) - 1 = -(7 / 2 : ℝ) by ring]; have := hprod.hM; gcongr
      _ = C_n * τ ^ (-(7 / 2 : ℝ)) := by simp only [C_n]; ring
  have hinv : ‖(ctHG ε ((τ : ℂ) * Complex.I))⁻¹‖ ≤ C_inv * τ ^ (5 / 2 : ℝ) := by
    rcases le_or_gt τ (1 / 4) with hsmall | hbig
    · have hn : ‖(τ : ℂ) * Complex.I‖ = τ := by simp [hτ_abs]
      have h1 := hMH ((τ : ℂ) * Complex.I) ⟨by simp, by simp⟩ (by simp [hτ0.ne']) (by rw [hn]; exact hsmall)
      rw [hn] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have h1 := (hMmid τ ⟨hbig.le, hτ2⟩).trans (le_abs_self Mmid)
      have hpow : (1 : ℝ) ≤ 32 * τ ^ (5 / 2 : ℝ) := by
        have hq : (1 / 4 : ℝ) ^ (5 / 2 : ℝ) ≤ τ ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hbig.le (by norm_num)
        have h2 : (1 / 32 : ℝ) = (1 / 4 : ℝ) ^ (5 / 2 : ℝ) := by
          rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num, ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num)]; norm_num
        linarith
      calc ‖(ctHG ε ((τ : ℂ) * Complex.I))⁻¹‖ ≤ |Mmid| := h1
        _ ≤ |Mmid| * (32 * τ ^ (5 / 2 : ℝ)) := le_mul_of_one_le_right (abs_nonneg _) hpow
        _ = 32 * |Mmid| * τ ^ (5 / 2 : ℝ) := by ring
        _ ≤ C_inv * τ ^ (5 / 2 : ℝ) := by gcongr; exact le_max_right _ _
  exact ⟨hb0, hb1, hinv⟩

/-! ### 3. Phase `m(t)` lower bounds and derivative of `W_edge` -/

lemma hankelEdgeM_ge_sq_tenth {τ : ℝ} (h0 : 0 ≤ τ) (h2 : τ ≤ 2) : τ ^ 2 / 10 ≤ hankelEdgeM τ := by
  let g : ℝ → ℝ := fun t => hankelEdgeM t - t ^ 2 / 10
  have hg_cont : ContinuousOn g (Icc 0 2) :=
    (hankelEdgeM_continuousOn.mono Icc_subset_Ici_self).sub (continuousOn_pow 2 |>.div_const 10)
  have hg_deriv : ∀ t ∈ interior (Icc (0 : ℝ) 2), 0 ≤ deriv g t := fun t ht => by
    rw [interior_Icc] at ht
    have hd1 := hankelEdgeM_hasDerivAt ht.1
    have hd2 : HasDerivAt (fun s : ℝ => s ^ 2 / 10) (t / 5) t := by
      simpa using ((hasDerivAt_pow 2 t).div_const 10).congr_deriv (by ring)
    have hdg : HasDerivAt g (hankelEdgeM' t - t / 5) t := hd1.sub hd2
    rw [hdg.deriv]
    have hm' := (FctCuspEdge.hankelEdgeM'_bounds ht.1).1
    have h1t2 : 1 + t ^ 2 ≤ 5 := by nlinarith [ht.1, ht.2]
    have ht5 : t / 5 ≤ t / (1 + t ^ 2) := div_le_div_of_nonneg_left ht.1.le (by positivity) h1t2
    linarith
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 2) hg_cont
    (fun t ht => by
      rw [interior_Icc] at ht
      exact ((hankelEdgeM_hasDerivAt ht.1).sub ((hasDerivAt_pow 2 t).div_const 10)).differentiableAt.differentiableWithinAt)
    hg_deriv
  have hle := hmono ⟨le_rfl, by norm_num⟩ ⟨h0, h2⟩ h0
  simpa [g, hankelEdgeM_zero] using hle

lemma hankelEdgeM_ge_two_fifths {τ : ℝ} (h2 : 2 ≤ τ) : (2 / 5 : ℝ) ≤ hankelEdgeM τ := by
  have hm2 : (2 / 5 : ℝ) ≤ hankelEdgeM 2 := by
    have h := hankelEdgeM_ge_sq_tenth (by norm_num) le_rfl
    linarith
  exact hm2.trans (hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.mpr (by norm_num)) (mem_Ici.mpr (by linarith)) h2)

lemma hankelEdgeM_deriv_div_le {t : ℝ} (ht : 0 < t) : hankelEdgeM' t / hankelEdgeM t ≤ 20 / t := by
  have hmpos : 0 < hankelEdgeM t := hankelEdgeM_pos ht
  have hb := FctCuspEdge.hankelEdgeM'_bounds ht
  rcases le_or_gt t 2 with hle | hgt
  · have hlo := hankelEdgeM_ge_sq_tenth ht.le hle
    calc hankelEdgeM' t / hankelEdgeM t
        ≤ (π ^ 2 / 6 * t) / (t ^ 2 / 10) := div_le_div₀ (by positivity) hb.2.1 (by positivity) hlo
      _ = (5 * π ^ 2 / 3) / t := by field_simp [ht.ne']; ring
      _ ≤ 20 / t := div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos, Real.pi_lt_d2]) ht.le
  · have hlo := hankelEdgeM_ge_two_fifths hgt.le
    calc hankelEdgeM' t / hankelEdgeM t
        ≤ (1 / t) / (2 / 5) := div_le_div₀ (by positivity) hb.2.2 (by norm_num) hlo
      _ = (5 / 2) / t := by ring
      _ ≤ 20 / t := div_le_div_of_nonneg_right (by norm_num) ht.le

private lemma phiKill_imag_deriv_le : ∃ Ckd ≥ (0 : ℝ), ∀ {a t : ℝ}, 0 < a → 0 < t →
    ‖deriv (fun s : ℝ => FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) t‖ ≤ Ckd / t := by
  obtain ⟨C, hC0, hC⟩ := FctPhiKill.norm_iteratedDeriv_phiPQ_le 8 8 1 (by norm_num) (by norm_num) le_rfl
  refine ⟨C, hC0, fun {a t} ha ht => ?_⟩
  have hza : ((t : ℂ) * Complex.I) + (a : ℂ) ≠ 0 :=
    FctPhiKill.add_ofReal_ne_zero_of_re_nonneg ha (by simp)
  have hd_c := (FctPhiKill.hasDerivAt_phiPQ (p := 8) (q := 8) (by norm_num) (by norm_num) hza).differentiableAt
  have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
  have hc := hd_c.hasDerivAt.comp t hl
  have heq : deriv (fun s : ℝ => FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) t =
      Complex.I * deriv (FctPhiKill.phiPQ 8 8 a) ((t : ℂ) * Complex.I) := by
    rw [show (fun s : ℝ => FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) =
        (FctPhiKill.phiPQ 8 8 a ∘ fun s : ℝ => (s : ℂ) * Complex.I) from rfl, hc.deriv]
    ring
  rw [heq, norm_mul, Complex.norm_I, one_mul]
  have h1 := hC (a := a) (z := (t : ℂ) * Complex.I) ha (by simp) (by simp [ht.ne'])
  rw [iteratedDeriv_one] at h1
  have hnt : ‖(t : ℂ) * Complex.I‖ = t := by simp [abs_of_pos ht]
  rw [hnt] at h1
  rcases le_or_gt t a with hta | hat
  · have hm : min (t ^ ((8 : ℤ) - 1) * a ^ (-(8 : ℤ))) (a ^ 8 * t ^ (-((8 + 1 : ℕ) : ℤ))) ≤
        t ^ ((8 : ℤ) - 1) * a ^ (-(8 : ℤ)) := min_le_left _ _
    have hbd : t ^ ((8 : ℤ) - 1) * a ^ (-(8 : ℤ)) ≤ t⁻¹ := by
      rw [show (8 : ℤ) - 1 = ((7 : ℕ) : ℤ) by rfl, show -(8 : ℤ) = -((8 : ℕ) : ℤ) by rfl,
        zpow_natCast, zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_le_iff₀ (pow_pos ha 8)]
      have hpow : t ^ 8 ≤ a ^ 8 := pow_le_pow_left₀ ht.le hta 8
      calc t ^ 7 ≤ t ^ 7 * (t * t⁻¹) := by rw [mul_inv_cancel₀ ht.ne', mul_one]
        _ = t ^ 8 * t⁻¹ := by ring
        _ ≤ a ^ 8 * t⁻¹ := by gcongr
        _ = t⁻¹ * a ^ 8 := by ring
    exact h1.trans ((mul_le_mul_of_nonneg_left (hm.trans hbd) hC0).trans_eq (by ring))
  · have hm : min (t ^ ((8 : ℤ) - 1) * a ^ (-(8 : ℤ))) (a ^ 8 * t ^ (-((8 + 1 : ℕ) : ℤ))) ≤
        a ^ 8 * t ^ (-((8 + 1 : ℕ) : ℤ)) := min_le_right _ _
    have hbd : a ^ 8 * t ^ (-((8 + 1 : ℕ) : ℤ)) ≤ t⁻¹ := by
      rw [show -((8 + 1 : ℕ) : ℤ) = -((9 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast,
        ← div_eq_mul_inv, div_le_iff₀ (pow_pos ht 9)]
      have hpow : a ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ ha.le hat.le 8
      calc a ^ 8 ≤ t ^ 8 := hpow
        _ = t⁻¹ * t ^ 9 := by field_simp [ht.ne']
    exact h1.trans ((mul_le_mul_of_nonneg_left (hm.trans hbd) hC0).trans_eq (by ring))

private lemma fctPsi_eq_integral_of_ne_zero (K4 ε c L1 α : ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹ *
        (Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)) := by
  unfold fctPsi fctWarpKA
  congr 1
  have hc : (∫ s in (0 : ℝ)..1,
      mellinK0 c ((s : ℂ) * ((τ : ℂ) * Complex.I)) (fctXi1 L1) *
        fctWarpA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I))) =
      τ⁻¹ • ∫ u in (0 : ℝ)..τ,
        mellinK0 c ((u : ℂ) * Complex.I) (fctXi1 L1) *
          fctWarpA K4 ε c L1 α ((u : ℂ) * Complex.I) := by
    have h := intervalIntegral.integral_comp_mul_right
      (f := fun u : ℝ => mellinK0 c ((u : ℂ) * Complex.I) (fctXi1 L1) *
        fctWarpA K4 ε c L1 α ((u : ℂ) * Complex.I)) hτ (a := (0 : ℝ)) (b := (1 : ℝ))
    simp only [zero_mul, one_mul, Complex.ofReal_mul, mul_assoc] at h ⊢
    exact h
  rw [hc, Complex.real_smul, Complex.ofReal_inv]
  have htc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  field_simp

private lemma edge_subcase_B1 {τ C_W_n0 C_W_n1 C_W_f0 C_W_f1 I_tail lhs : ℝ}
    {W_edge : ℝ → ℂ} {tailTerm : ℝ → ℝ}
    (hτpos : 0 < τ) (hτ2 : τ ≤ 2)
    (hCWn1 : 0 ≤ C_W_n1) (hCWf1 : 0 ≤ C_W_f1) (hItail : 0 ≤ I_tail)
    (hI_tail_def : I_tail = C_W_f1 * (3 / π + 1 / π ^ 2) * Real.exp (-(2 * π)))
    (hW_cont : ContinuousOn (deriv W_edge) (Ici τ))
    (hW_near : ∀ t : ℝ, τ ≤ t → t ≤ 2 →
      ‖W_edge t‖ ≤ C_W_n0 * t ^ (-(5 / 2 : ℝ)) ∧ ‖deriv W_edge t‖ ≤ C_W_n1 * t ^ (-(7 / 2 : ℝ)))
    (hW_far : ∀ t : ℝ, 2 ≤ t →
      ‖deriv W_edge t‖ ≤ C_W_f1 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + t) * Real.exp (-(π * t)))
    (hWT_bd : ∀ T : ℝ, 2 ≤ T → ‖W_edge T‖ ≤ C_W_f0 * (1 + T) * Real.exp (-(π * T)))
    (h_ibp : ∀ T : ℝ, max 2 (τ + 1) ≤ T →
      lhs ≤ (tailTerm T - C_W_f0 * (1 + T) * Real.exp (-(π * T))) +
        ‖W_edge T‖ + ‖W_edge τ‖ + ∫ t in τ..T, ‖deriv W_edge t‖)
    (hT_lim : Filter.Tendsto tailTerm Filter.atTop (𝓝 0))
    (hexp_tail : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 + t) * Real.exp (-(π * t)) ≤ ((1 + a) / π + 1 / π ^ 2) * Real.exp (-(π * a))) :
    lhs ≤ (C_W_n0 + (2 / 5) * C_W_n1 + 8 * I_tail) * τ ^ (-(5 / 2 : ℝ)) := by
  have h_const_bd : ∀ T : ℝ, max 2 (τ + 1) ≤ T →
      lhs ≤ tailTerm T + (C_W_n0 + (2 / 5) * C_W_n1 + 8 * I_tail) * τ ^ (-(5 / 2 : ℝ)) := by
    intro T hT
    have h2T : (2 : ℝ) ≤ T := (le_max_left 2 (τ + 1)).trans hT
    have hτT : τ ≤ T := by linarith
    have hU_cont : ContinuousOn (fun t : ℝ => ‖deriv W_edge t‖) (Icc τ T) :=
      hW_cont.norm.mono fun _ hs => hs.1
    have hint_τ2 : IntervalIntegrable (fun t : ℝ => ‖deriv W_edge t‖) volume τ 2 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ2]
      exact (hU_cont.mono (Icc_subset_Icc_right h2T)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hint_2T : IntervalIntegrable (fun t : ℝ => ‖deriv W_edge t‖) volume 2 T := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h2T]
      exact (hU_cont.mono (Icc_subset_Icc_left hτ2)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hI1 : ∫ t in τ..2, ‖deriv W_edge t‖ ≤ (2 / 5 : ℝ) * C_W_n1 * τ ^ (-(5 / 2 : ℝ)) := by
      have hle : ∫ t in τ..2, ‖deriv W_edge t‖ ≤ ∫ t in τ..2, C_W_n1 * t ^ (-(7 / 2 : ℝ)) := by
        refine intervalIntegral.integral_mono_on hτ2 hint_τ2
          ((intervalIntegral.intervalIntegrable_rpow
            (Or.inr (notMem_uIcc_of_lt hτpos (by norm_num)))).const_mul _)
          fun t ht => (hW_near t ht.1 ht.2).2
      refine hle.trans ?_
      have hint72 : ∫ t in τ..2, C_W_n1 * t ^ (-(7 / 2 : ℝ)) =
          C_W_n1 * ((2 ^ (-(7 / 2 : ℝ) + 1) - τ ^ (-(7 / 2 : ℝ) + 1)) / (-(7 / 2 : ℝ) + 1)) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, by
          intro h0; exact absurd h0 (notMem_uIcc_of_lt hτpos (by norm_num))⟩)]
      rw [hint72]
      have hnonneg2 : 0 ≤ (2 : ℝ) ^ (-(5 / 2 : ℝ)) := by positivity
      have hexp : -(7 / 2 : ℝ) + 1 = -(5 / 2 : ℝ) := by norm_num
      rw [hexp]
      have hsub : (2 ^ (-(5 / 2 : ℝ)) - τ ^ (-(5 / 2 : ℝ))) / (-(5 / 2 : ℝ)) =
          (2 / 5 : ℝ) * (τ ^ (-(5 / 2 : ℝ)) - 2 ^ (-(5 / 2 : ℝ))) := by ring
      rw [hsub]
      calc C_W_n1 * ((2 / 5 : ℝ) * (τ ^ (-(5 / 2 : ℝ)) - 2 ^ (-(5 / 2 : ℝ))))
          ≤ C_W_n1 * ((2 / 5 : ℝ) * (τ ^ (-(5 / 2 : ℝ)) - 0)) := by gcongr
        _ = (2 / 5 : ℝ) * C_W_n1 * τ ^ (-(5 / 2 : ℝ)) := by ring
    have hI2 : ∫ t in (2 : ℝ)..T, ‖deriv W_edge t‖ ≤ I_tail := by
      have hint_exp : Continuous fun t : ℝ => C_W_f1 * (1 + t) * Real.exp (-(π * t)) :=
        (continuous_const.mul (continuous_const.add continuous_id)).mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
      have hle : ∫ t in (2 : ℝ)..T, ‖deriv W_edge t‖ ≤
          ∫ t in (2 : ℝ)..T, C_W_f1 * (1 + t) * Real.exp (-(π * t)) := by
        refine intervalIntegral.integral_mono_on h2T hint_2T (hint_exp.intervalIntegrable _ _) fun t ht => ?_
        have h1t : (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg t]) (by norm_num)
        have h1tp : 0 ≤ 1 + t := by linarith [ht.1]
        have hep : 0 ≤ Real.exp (-(π * t)) := (Real.exp_pos _).le
        calc ‖deriv W_edge t‖
            ≤ C_W_f1 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + t) * Real.exp (-(π * t)) := hW_far t ht.1
          _ ≤ C_W_f1 * 1 * (1 + t) * Real.exp (-(π * t)) := by gcongr
          _ = C_W_f1 * (1 + t) * Real.exp (-(π * t)) := by ring
      have hmul : ∫ t in (2 : ℝ)..T, C_W_f1 * (1 + t) * Real.exp (-(π * t)) =
          C_W_f1 * ∫ t in (2 : ℝ)..T, (1 + t) * Real.exp (-(π * t)) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun t _ => by ring
      have htail := hexp_tail 2 T le_rfl h2T
      refine hle.trans (hmul.le.trans ?_)
      calc C_W_f1 * ∫ t in (2 : ℝ)..T, (1 + t) * Real.exp (-(π * t))
          ≤ C_W_f1 * (((1 + 2) / π + 1 / π ^ 2) * Real.exp (-(π * 2))) :=
            mul_le_mul_of_nonneg_left htail hCWf1
        _ = I_tail := by rw [hI_tail_def]; ring_nf
    have hI12 : ∫ t in τ..T, ‖deriv W_edge t‖ ≤ (2 / 5 : ℝ) * C_W_n1 * τ ^ (-(5 / 2 : ℝ)) + I_tail := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hint_τ2 hint_2T]
      exact add_le_add hI1 hI2
    have h1_le_8 : 1 ≤ 8 * τ ^ (-(5 / 2 : ℝ)) := by
      have hpow : τ ^ (5 / 2 : ℝ) ≤ 8 := by
        calc τ ^ (5 / 2 : ℝ) ≤ (2 : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_le_rpow hτpos.le hτ2 (by norm_num)
          _ ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 8 := by norm_num
      rw [Real.rpow_neg hτpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hτpos _)]
      linarith
    have hItail_bd : I_tail ≤ 8 * I_tail * τ ^ (-(5 / 2 : ℝ)) := by
      calc I_tail = I_tail * 1 := (mul_one _).symm
        _ ≤ I_tail * (8 * τ ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h1_le_8 hItail
        _ = 8 * I_tail * τ ^ (-(5 / 2 : ℝ)) := by ring
    have hWτ := (hW_near τ le_rfl hτ2).1
    calc lhs
        ≤ (tailTerm T - C_W_f0 * (1 + T) * Real.exp (-(π * T))) +
            ‖W_edge T‖ + ‖W_edge τ‖ + ∫ t in τ..T, ‖deriv W_edge t‖ := h_ibp T hT
      _ ≤ (tailTerm T - C_W_f0 * (1 + T) * Real.exp (-(π * T))) +
            C_W_f0 * (1 + T) * Real.exp (-(π * T)) + C_W_n0 * τ ^ (-(5 / 2 : ℝ)) +
            ((2 / 5 : ℝ) * C_W_n1 * τ ^ (-(5 / 2 : ℝ)) + 8 * I_tail * τ ^ (-(5 / 2 : ℝ))) := by
          have := hWT_bd T h2T
          linarith
      _ = _ := by ring
  let B : ℝ := (C_W_n0 + (2 / 5) * C_W_n1 + 8 * I_tail) * τ ^ (-(5 / 2 : ℝ))
  have hT' : Filter.Tendsto (fun T : ℝ => tailTerm T + B) Filter.atTop (𝓝 (0 + B)) :=
    hT_lim.add tendsto_const_nhds
  rw [zero_add] at hT'
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hT'
    (Filter.eventually_atTop.mpr ⟨max 2 (τ + 1), h_const_bd⟩)

private lemma edge_subcase_B2 {τ C_W_f0 C_W_f1 lhs : ℝ}
    {W_edge : ℝ → ℂ} {tailTerm : ℝ → ℝ}
    (h2τ : 2 < τ) (hCWf1 : 0 ≤ C_W_f1)
    (hW_cont : ContinuousOn (deriv W_edge) (Ici τ))
    (hW_far : ∀ t : ℝ, τ ≤ t →
      ‖W_edge t‖ ≤ C_W_f0 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + t) * Real.exp (-(π * t)) ∧
      ‖deriv W_edge t‖ ≤ C_W_f1 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + t) * Real.exp (-(π * t)))
    (hWT_bd : ∀ T : ℝ, 2 ≤ T → ‖W_edge T‖ ≤ C_W_f0 * (1 + T) * Real.exp (-(π * T)))
    (h_ibp : ∀ T : ℝ, max 2 (τ + 1) ≤ T →
      lhs ≤ (tailTerm T - C_W_f0 * (1 + T) * Real.exp (-(π * T))) +
        ‖W_edge T‖ + ‖W_edge τ‖ + ∫ t in τ..T, ‖deriv W_edge t‖)
    (hT_lim : Filter.Tendsto tailTerm Filter.atTop (𝓝 0))
    (hexp_tail : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 + t) * Real.exp (-(π * t)) ≤ ((1 + a) / π + 1 / π ^ 2) * Real.exp (-(π * a))) :
    lhs ≤ (C_W_f0 + C_W_f1 * (1 / π + 1 / π ^ 2)) *
      ((1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + τ) * Real.exp (-(π * τ))) := by
  have h_const_bd : ∀ T : ℝ, max 2 (τ + 1) ≤ T →
      lhs ≤ tailTerm T + (C_W_f0 + C_W_f1 * (1 / π + 1 / π ^ 2)) *
        ((1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + τ) * Real.exp (-(π * τ))) := by
    intro T hT
    have h2T : (2 : ℝ) ≤ T := (le_max_left 2 (τ + 1)).trans hT
    have hτT : τ ≤ T := by linarith [le_max_right 2 (τ + 1)]
    have hU_cont : ContinuousOn (fun t : ℝ => ‖deriv W_edge t‖) (Icc τ T) :=
      hW_cont.norm.mono fun _ hs => hs.1
    have hint_τT : IntervalIntegrable (fun t : ℝ => ‖deriv W_edge t‖) volume τ T := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτT]
      exact hU_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hI_tail : ∫ t in τ..T, ‖deriv W_edge t‖ ≤
        C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + τ) * (1 / π + 1 / π ^ 2) * Real.exp (-(π * τ)) := by
      have hmaj_c : Continuous fun t : ℝ =>
          (C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) * ((1 + t) * Real.exp (-(π * t))) :=
        continuous_const.mul ((continuous_const.add continuous_id).mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg))
      have hle : ∫ t in τ..T, ‖deriv W_edge t‖ ≤
          ∫ t in τ..T, (C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) * ((1 + t) * Real.exp (-(π * t))) := by
        refine intervalIntegral.integral_mono_on hτT hint_τT (hmaj_c.intervalIntegrable _ _) fun t ht => ?_
        have hsq : (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
          refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
          nlinarith [ht.1]
        have h1tp : 0 ≤ 1 + t := by linarith [ht.1]
        have hep : 0 ≤ Real.exp (-(π * t)) := (Real.exp_pos _).le
        calc ‖deriv W_edge t‖
            ≤ C_W_f1 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + t) * Real.exp (-(π * t)) := (hW_far t ht.1).2
          _ ≤ C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + t) * Real.exp (-(π * t)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hCWf1) h1tp) hep
          _ = (C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) * ((1 + t) * Real.exp (-(π * t))) := by ring
      have hmul : ∫ t in τ..T, (C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) * ((1 + t) * Real.exp (-(π * t))) =
          (C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) * ∫ t in τ..T, (1 + t) * Real.exp (-(π * t)) :=
        intervalIntegral.integral_const_mul _ _
      have htail := hexp_tail τ T h2τ.le hτT
      have h1τ_ge1 : (1 : ℝ) ≤ 1 + τ := by linarith
      have hsum_le : (1 + τ) / π + 1 / π ^ 2 ≤ (1 + τ) * (1 / π + 1 / π ^ 2) := by
        have : 1 / π ^ 2 ≤ (1 + τ) / π ^ 2 := div_le_div_of_nonneg_right h1τ_ge1 (by positivity)
        linarith [show (1 + τ) * (1 / π + 1 / π ^ 2) = (1 + τ) / π + (1 + τ) / π ^ 2 by ring]
      refine hle.trans (hmul.le.trans ?_)
      have hC_nn : 0 ≤ C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by positivity
      have hepτ : 0 ≤ Real.exp (-(π * τ)) := (Real.exp_pos _).le
      calc (C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) * ∫ t in τ..T, (1 + t) * Real.exp (-(π * t))
          ≤ (C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) *
              (((1 + τ) / π + 1 / π ^ 2) * Real.exp (-(π * τ))) :=
            mul_le_mul_of_nonneg_left htail hC_nn
        _ ≤ (C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) *
              ((1 + τ) * (1 / π + 1 / π ^ 2) * Real.exp (-(π * τ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum_le hepτ) hC_nn
        _ = _ := by ring
    have hWτ := (hW_far τ le_rfl).1
    calc lhs
        ≤ (tailTerm T - C_W_f0 * (1 + T) * Real.exp (-(π * T))) +
            ‖W_edge T‖ + ‖W_edge τ‖ + ∫ t in τ..T, ‖deriv W_edge t‖ := h_ibp T hT
      _ ≤ (tailTerm T - C_W_f0 * (1 + T) * Real.exp (-(π * T))) +
            C_W_f0 * (1 + T) * Real.exp (-(π * T)) +
            C_W_f0 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + τ) * Real.exp (-(π * τ)) +
            C_W_f1 * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + τ) * (1 / π + 1 / π ^ 2) * Real.exp (-(π * τ)) := by
          have hwt := hWT_bd T h2T
          linarith [hI_tail]
      _ = _ := by ring
  let B : ℝ := (C_W_f0 + C_W_f1 * (1 / π + 1 / π ^ 2)) *
    ((1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + τ) * Real.exp (-(π * τ)))
  have hT' : Filter.Tendsto (fun T : ℝ => tailTerm T + B) Filter.atTop (𝓝 (0 + B)) :=
    hT_lim.add tendsto_const_nhds
  rw [zero_add] at hT'
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hT'
    (Filter.eventually_atTop.mpr ⟨max 2 (τ + 1), h_const_bd⟩)

/-! ### 4. Main uniform left-edge theorem -/

set_option maxHeartbeats 800000 in
theorem fctPhiC_left_edge_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ M : ℝ, 0 ≤ M ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ τ : ℝ, ‖fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I)‖ ≤ M := by
  set c0_pair : ℝ := h.choose_spec.choose
  obtain ⟨Cz, c0z, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨CL1, c0L1, hCL10, hc0L1, hL1_bd⟩ := abs_fctWarpL1_le h
  obtain ⟨B_D, c0D, hD_vdata⟩ := fctDcomp_vdata hK4 ⟨Cz, c0z, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨v0, -, -, -, hvB0, -⟩ := hD_vdata 1 (max c0D 1) (Or.inl rfl) (le_max_left _ _)
  have hB0_nn : 0 ≤ B_D 0 := (norm_nonneg _).trans (by simpa using hvB0 0 (by norm_num) 0 ⟨le_rfl, zero_le_one⟩)
  have hB1_nn : 0 ≤ B_D 1 := (norm_nonneg _).trans (by simpa using hvB0 1 (by norm_num) 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨Cpk, hCpk0, hCpk⟩ := FctPhiKill.norm_phiPQ_le 8 8
  obtain ⟨C1s, hC1s0, h1sCpk⟩ := FctPhiKill.norm_one_sub_phiPQ_le_one_and_tail 8 8 (by norm_num)
  obtain ⟨Ckd, hCkd0, hkd⟩ := phiKill_imag_deriv_le
  obtain ⟨Cd_p, hCdp0, hHG_c2_p, hHG_far_p⟩ := ctHG_imag_far_deriv_le (1 : ℝ)
  obtain ⟨Cd_m, hCdm0, hHG_c2_m, hHG_far_m⟩ := ctHG_imag_far_deriv_le (-1 : ℝ)
  obtain ⟨Cn_p, Ci_p, hCnp0, hCip0, hHG_near_p⟩ := ctHG_imag_near_bounds (1 : ℝ)
  obtain ⟨Cn_m, Ci_m, hCnm0, hCim0, hHG_near_m⟩ := ctHG_imag_near_bounds (-1 : ℝ)
  obtain ⟨cHG, CHG, hcHG, hCHG, _, hHG_left⟩ := ctHG_band_two_sided
  set Cd : ℝ := max Cd_p Cd_m
  set Cn : ℝ := max Cn_p Cn_m
  set Cinv : ℝ := max Ci_p Ci_m
  set K0 : ℝ := Real.sqrt (20 * |CL1| + 1)
  have hK0_pos : 0 < K0 := by positivity
  set c_th : ℝ := (max K0 (5 * |CL1| + 1)) ^ 3
  set c₀ : ℝ := max (max (max c0_pair c0L1) c0D) (max c_th 1)
  have hc01 : 1 ≤ c₀ := (le_max_right _ _).trans (le_max_right _ _)
  -- Uniform constants independent of `c, ε, τ`
  set C_gL : ℝ := Real.pi ^ 2 / 12 + |CL1| * Cpk
  set M_small : ℝ := (5 * Real.exp (1 / 6)) * Real.exp (B_D 0) * Cinv *
    (2 * Real.exp (1 / 6) * C_gL * Real.exp (B_D 0) * Cn) * K0 ^ 3
  set C_pref0 : ℝ := Real.exp (1 / 6) * Real.exp (B_D 0)
  set C_pref1 : ℝ := (1 / 2 + 1 / 2 + B_D 1) * Real.exp (1 / 6) * Real.exp (B_D 0)
  set C_f45_n0 : ℝ := Cn * (1 + C1s)
  set C_f45_n1 : ℝ := Cn * (2 * (1 + C1s) + Ckd + 40 * C1s)
  set C_W_n0 : ℝ := C_pref0 * C_f45_n0
  set C_W_n1 : ℝ := C_pref1 * C_f45_n0 * 2 + C_pref0 * C_f45_n1
  set C_f45_f0 : ℝ := Cd * (1 + C1s)
  set C_f45_f1 : ℝ := Cd * ((1 + C1s) + (Ckd + 40 * C1s) / 2)
  set C_W_f0 : ℝ := C_pref0 * C_f45_f0
  set C_W_f1 : ℝ := C_pref1 * C_f45_f0 + C_pref0 * C_f45_f1
  set I_tail : ℝ := C_W_f1 * (3 / Real.pi + 1 / Real.pi ^ 2) * Real.exp (-(2 * Real.pi))
  set M_mid_W : ℝ := (5 * Real.exp (1 / 6)) * Real.exp (B_D 0) * Cinv *
    (C_W_n0 + (2 / 5) * C_W_n1 + 8 * I_tail)
  set M_far_W : ℝ := Real.exp (1 / 6) * Real.exp (B_D 0) / cHG *
    (C_W_f0 + C_W_f1 * (1 / Real.pi + 1 / Real.pi ^ 2))
  set M : ℝ := max M_small (max M_mid_W M_far_W)
  refine ⟨c₀, M, le_trans (by positivity) (le_max_left _ _), fun ε c hε hc τ => ?_⟩
  have hc1 : 1 ≤ c := hc.trans' hc01
  have hcpos : 0 < c := by linarith
  have hc_pair : h.choose_spec.choose ≤ c :=
    hc.trans' (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
  have hc_L1 : c0L1 ≤ c :=
    hc.trans' (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
  have hc_D : c0D ≤ c := hc.trans' ((le_max_right _ _).trans (le_max_left _ _))
  have hc_th : c_th ≤ c := hc.trans' ((le_max_left _ _).trans (le_max_right _ _))
  obtain ⟨v, hv, hsupp, heven, hvB, hvD⟩ := hD_vdata ε c hε hc_D
  set L1 : ℝ := fctWarpL1 h ε c
  set α : ℝ := fctWarpAlpha h ε c
  set a : ℝ := c ^ (-(1 / 12 : ℝ))
  have hapos : 0 < a := Real.rpow_pos_of_pos hcpos _
  have hL1c : |L1| ≤ CL1 * c ^ (-(2 / 3 : ℝ)) := hL1_bd ε c hε hc_L1
  have hL1_abs : |L1| ≤ |CL1| * c ^ (-(2 / 3 : ℝ)) :=
    hL1c.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hD_conj : ∀ ζ ∈ closedStrip, fctDcompAt K4 c α (starRingEnd ℂ ζ) =
      starRingEnd ℂ (fctDcompAt K4 c α ζ) := fun ζ _ => by
    show fctDcomp K4 (fctWarpAlpha h) ε c (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcomp K4 (fctWarpAlpha h) ε c ζ)
    rw [hvD, hvD, stripCompGExt_conj heven ζ, Complex.exp_conj]
  have hD_ub : ∀ t : ℝ, ‖fctDcompAt K4 c α ((t : ℂ) * Complex.I)‖ ≤ Real.exp (B_D 0) := fun t => by
    show ‖fctDcomp K4 (fctWarpAlpha h) ε c ((t : ℂ) * Complex.I)‖ ≤ _
    rw [hvD, Complex.norm_exp]
    have h0 := hvB 0 (by norm_num) ((t : ℂ) * Complex.I) ⟨by simp, by simp⟩
    simp only [iteratedDeriv_zero] at h0
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans h0)
  have hD_inv_ub : ∀ t : ℝ, ‖(fctDcompAt K4 c α ((t : ℂ) * Complex.I))⁻¹‖ ≤ Real.exp (B_D 0) := fun t => by
    show ‖(fctDcomp K4 (fctWarpAlpha h) ε c ((t : ℂ) * Complex.I))⁻¹‖ ≤ _
    rw [hvD, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
    have h0 := hvB 0 (by norm_num) ((t : ℂ) * Complex.I) ⟨by simp, by simp⟩
    simp only [iteratedDeriv_zero] at h0
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp ((Complex.abs_re_le_norm _).trans h0)).1])
  have hHG_c2 : ContDiffOn ℝ 2 (fun t : ℝ => ctHG ε ((t : ℂ) * Complex.I)) {t : ℝ | t ≠ 0} := by
    rcases hε with rfl | rfl <;> assumption
  have hHG_far : ∀ t : ℝ, 1 ≤ |t| →
      ‖ctHG ε ((t : ℂ) * Complex.I)‖ ≤ Cd * (1 + |t|) * Real.exp (-(π * |t|)) ∧
      ‖deriv (fun s : ℝ => ctHG ε ((s : ℂ) * Complex.I)) t‖ ≤ Cd * (1 + |t|) * Real.exp (-(π * |t|)) := by
    intro t ht
    rcases hε with rfl | rfl
    · exact ⟨(hHG_far_p t ht).1.trans (by gcongr; exact le_max_left _ _),
        (hHG_far_p t ht).2.trans (by gcongr; exact le_max_left _ _)⟩
    · exact ⟨(hHG_far_m t ht).1.trans (by gcongr; exact le_max_right _ _),
        (hHG_far_m t ht).2.trans (by gcongr; exact le_max_right _ _)⟩
  have hHG_near : ∀ t : ℝ, 0 < t → t ≤ 2 →
      ‖ctHG ε ((t : ℂ) * Complex.I)‖ ≤ Cn * t ^ (-(5 / 2 : ℝ)) ∧
      ‖deriv (fun s : ℝ => ctHG ε ((s : ℂ) * Complex.I)) t‖ ≤ Cn * t ^ (-(7 / 2 : ℝ)) ∧
      ‖(ctHG ε ((t : ℂ) * Complex.I))⁻¹‖ ≤ Cinv * t ^ (5 / 2 : ℝ) := by
    intro t ht0 ht2
    rcases hε with rfl | rfl
    · refine ⟨(hHG_near_p t ht0 ht2).1.trans (by gcongr; exact le_max_left _ _),
        (hHG_near_p t ht0 ht2).2.1.trans (by gcongr; exact le_max_left _ _),
        (hHG_near_p t ht0 ht2).2.2.trans (by gcongr; exact le_max_left _ _)⟩
    · refine ⟨(hHG_near_m t ht0 ht2).1.trans (by gcongr; exact le_max_right _ _),
        (hHG_near_m t ht0 ht2).2.1.trans (by gcongr; exact le_max_right _ _),
        (hHG_near_m t ht0 ht2).2.2.trans (by gcongr; exact le_max_right _ _)⟩
  -- Core positive-`τ` bound:
  have hpos_bd : ∀ τ : ℝ, 0 < τ → ‖fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I)‖ ≤ M := by
    intro τ hτpos
    have hc13_ge : max K0 (5 * |CL1| + 1) ≤ c ^ (1 / 3 : ℝ) := by
      have h13 : c_th ^ (1 / 3 : ℝ) ≤ c ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hc_th (by norm_num)
      have heq : c_th ^ (1 / 3 : ℝ) = max K0 (5 * |CL1| + 1) := by
        simp only [c_th, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ max K0 (5 * |CL1| + 1))]
        norm_num
      linarith
    have hK0c_le_1 : K0 * c ^ (-(1 / 3 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg hcpos.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hcpos _)]
      exact (le_max_left _ _).trans hc13_ge
    rcases le_or_gt τ (K0 * c ^ (-(1 / 3 : ℝ))) with hτ_sm | hτ_big
    · -- Subcase A: `0 < τ ≤ K₀ c^{-1/3}` (trivial triangle bound on `[0, τ]`)
      have hτ1 : τ ≤ 1 := hτ_sm.trans hK0c_le_1
      have hτ2 : τ ≤ 2 := by linarith
      have hK0_inv : ‖(mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹‖ ≤ 5 * Real.exp (1 / 6) := by
        have hlb := (mellinK0_imag_bounds hc1 L1 τ).1
        have h1τ : 1 + τ ^ 2 ≤ 5 := by nlinarith
        have hcp_lb : (5 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1τ (by norm_num)
        have h5_lb : (1 / 5 : ℝ) ≤ (5 : ℝ) ^ (-(1 / 4 : ℝ)) := by
          rw [Real.rpow_neg (by norm_num), one_div]
          refine inv_anti₀ (by positivity) ?_
          calc (5 : ℝ) ^ (1 / 4 : ℝ) ≤ (5 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 5 := Real.rpow_one _
        have htot : (1 / 5 : ℝ) * Real.exp (-(1 / 6)) ≤ ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖ := by
          have hm0 : (1 / 5 : ℝ) * Real.exp (-(1 / 6)) ≤
              Real.exp (-(1 / 6)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
            have hle := h5_lb.trans hcp_lb
            have hexp0 : 0 ≤ Real.exp (-(1 / 6)) := (Real.exp_pos (-(1 / 6))).le
            nlinarith
          exact hm0.trans hlb
        rw [norm_inv]
        calc ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖⁻¹
            ≤ ((1 / 5 : ℝ) * Real.exp (-(1 / 6)))⁻¹ := inv_anti₀ (by positivity) htot
          _ = 5 * Real.exp (1 / 6) := by rw [mul_inv, Real.exp_neg, inv_inv]; ring
      have hInt_bd : ‖∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖ ≤
          (2 * Real.exp (1 / 6) * C_gL * Real.exp (B_D 0) * Cn) * τ ^ (1 / 2 : ℝ) := by
        set C_ker : ℝ := Real.exp (1 / 6) * C_gL * Real.exp (B_D 0) * Cn
        have hCker0 : 0 ≤ C_ker := by positivity
        have hpt_bd : ∀ u ∈ Ioc (0 : ℝ) τ,
            ‖fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖ ≤ C_ker * u ^ (-(1 / 2 : ℝ)) := by
          intro u hu
          have hu0 : 0 < u := hu.1
          have hu1 : u ≤ 1 := hu.2.trans hτ1
          have hu2 : u ≤ 2 := by linarith
          have hK0u : ‖mellinK0 c ((u : ℂ) * Complex.I) (fctXi1 L1)‖ ≤ Real.exp (1 / 6) :=
            (mellinK0_imag_bounds hc1 L1 u).2
          have hg_u : ‖stripG ((u : ℂ) * Complex.I)‖ ≤ Real.pi ^ 2 / 12 * u ^ 2 := by
            rw [stripG_imag_eq_neg_m hu0.ne', abs_of_pos hu0]
            simpa [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (hankelEdgeM_pos hu0).le] using
              hankelEdgeM_le_sq hu0.le
          have hpk_u : ‖(L1 : ℂ) * FctPhiKill.phiKill a ((u : ℂ) * Complex.I)‖ ≤ |CL1| * Cpk * u ^ 2 := by
            have hp1 := hCpk hapos (by simp : 0 ≤ ((u : ℂ) * Complex.I).re)
            have hnu : ‖(u : ℂ) * Complex.I‖ = u := by simp [abs_of_pos hu0]
            rw [hnu] at hp1
            have hm1 : min ((u / a) ^ 8) 1 ≤ (u / a) ^ 8 := min_le_left _ _
            have hdiv_pow : c ^ (-(2 / 3 : ℝ)) * (u / a) ^ 8 = u ^ 8 := by
              rw [div_pow, show a ^ 8 = c ^ (-(2 / 3 : ℝ)) by
                simp only [a, ← Real.rpow_natCast, ← Real.rpow_mul hcpos.le]; congr 1; norm_num]
              have hne : c ^ (-(2 / 3 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hcpos _).ne'
              field_simp [hne]
            have hu82 : u ^ 8 ≤ u ^ 2 := by
              have h1 : u ^ 6 ≤ 1 := pow_le_one₀ hu0.le hu1
              calc u ^ 8 = u ^ 2 * u ^ 6 := by ring
                _ ≤ u ^ 2 * 1 := by gcongr
                _ = u ^ 2 := mul_one _
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            calc |L1| * ‖FctPhiKill.phiKill a ((u : ℂ) * Complex.I)‖
                ≤ (|CL1| * c ^ (-(2 / 3 : ℝ))) * (Cpk * (u / a) ^ 8) :=
                  mul_le_mul hL1_abs (hp1.trans (mul_le_mul_of_nonneg_left hm1 hCpk0)) (norm_nonneg _) (by positivity)
              _ = |CL1| * Cpk * (c ^ (-(2 / 3 : ℝ)) * (u / a) ^ 8) := by ring
              _ = |CL1| * Cpk * u ^ 8 := by rw [hdiv_pow]
              _ ≤ |CL1| * Cpk * u ^ 2 := by gcongr
          have htan_u : ‖stripG ((u : ℂ) * Complex.I) + (L1 : ℂ) * FctPhiKill.phiKill a ((u : ℂ) * Complex.I)‖ ≤
              C_gL * u ^ 2 := by
            calc _ ≤ ‖stripG ((u : ℂ) * Complex.I)‖ + ‖(L1 : ℂ) * FctPhiKill.phiKill a ((u : ℂ) * Complex.I)‖ :=
                  norm_add_le _ _
              _ ≤ Real.pi ^ 2 / 12 * u ^ 2 + |CL1| * Cpk * u ^ 2 := add_le_add hg_u hpk_u
              _ = C_gL * u ^ 2 := by simp only [C_gL]; ring
          have hHG_u := (hHG_near u hu0 hu2).1
          have hpow : u ^ 2 * u ^ (-(5 / 2 : ℝ)) = u ^ (-(1 / 2 : ℝ)) := by
            rw [show u ^ 2 = u ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hu0]; congr 1; norm_num
          unfold fctWarpKA fctWarpA
          rw [norm_mul, norm_mul, norm_mul]
          calc ‖mellinK0 c ((u : ℂ) * Complex.I) (fctXi1 L1)‖ *
                (‖stripG ((u : ℂ) * Complex.I) + (L1 : ℂ) * FctPhiKill.phiKill a ((u : ℂ) * Complex.I)‖ *
                  ‖fctDcompAt K4 c α ((u : ℂ) * Complex.I)‖ * ‖ctHG ε ((u : ℂ) * Complex.I)‖)
              ≤ Real.exp (1 / 6) * ((C_gL * u ^ 2) * Real.exp (B_D 0) * (Cn * u ^ (-(5 / 2 : ℝ)))) :=
                mul_le_mul hK0u (mul_le_mul (mul_le_mul htan_u (hD_ub u) (norm_nonneg _) (by positivity))
                  hHG_u (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
            _ = C_ker * (u ^ 2 * u ^ (-(5 / 2 : ℝ))) := by simp only [C_ker]; ring
            _ = C_ker * u ^ (-(1 / 2 : ℝ)) := by rw [hpow]
        have hint_le : ‖∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖ ≤
            ∫ u in (0 : ℝ)..τ, C_ker * u ^ (-(1 / 2 : ℝ)) := by
          refine intervalIntegral.norm_integral_le_of_norm_le hτpos.le ?_ ?_
          · exact Filter.Eventually.of_forall fun u hu => hpt_bd u hu
          · exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul _
        have hval : ∫ u in (0 : ℝ)..τ, C_ker * u ^ (-(1 / 2 : ℝ)) =
            (2 * Real.exp (1 / 6) * C_gL * Real.exp (B_D 0) * Cn) * τ ^ (1 / 2 : ℝ) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
          rw [Real.zero_rpow (by norm_num), sub_zero]
          simp only [C_ker]; ring_nf
        exact hint_le.trans_eq hval
      have hPsi_bd : ‖fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)‖ ≤
          (5 * Real.exp (1 / 6)) * (2 * Real.exp (1 / 6) * C_gL * Real.exp (B_D 0) * Cn) * τ ^ (1 / 2 : ℝ) := by
        rw [fctPsi_eq_integral_of_ne_zero K4 ε c L1 α hτpos.ne', norm_mul, norm_mul, Complex.norm_I, one_mul,
          mul_assoc]
        exact mul_le_mul hK0_inv hInt_bd (norm_nonneg _) (by positivity)
      have htau_pow : τ ^ (1 / 2 : ℝ) * τ ^ (5 / 2 : ℝ) = τ ^ 3 := by
        rw [← Real.rpow_add hτpos, show (1 / 2 : ℝ) + (5 / 2 : ℝ) = 3 by norm_num]; norm_cast
      have hctau3 : c * τ ^ 3 ≤ K0 ^ 3 := by
        calc c * τ ^ 3 ≤ c * (K0 * c ^ (-(1 / 3 : ℝ))) ^ 3 := by gcongr
          _ = K0 ^ 3 * (c * (c ^ (-(1 / 3 : ℝ))) ^ 3) := by ring
          _ = K0 ^ 3 := by
              have h3 : (c ^ (-(1 / 3 : ℝ))) ^ 3 = c⁻¹ := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hcpos.le,
                  show -(1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
              rw [h3, mul_inv_cancel₀ hcpos.ne', mul_one]
      have hHG_inv := (hHG_near τ hτpos hτ2).2.2
      unfold fctPhiC
      rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
      calc c * ‖fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)‖ *
            (‖(fctDcompAt K4 c α ((τ : ℂ) * Complex.I))⁻¹‖ * ‖(ctHG ε ((τ : ℂ) * Complex.I))⁻¹‖)
          ≤ c * ((5 * Real.exp (1 / 6)) * (2 * Real.exp (1 / 6) * C_gL * Real.exp (B_D 0) * Cn) * τ ^ (1 / 2 : ℝ)) *
              (Real.exp (B_D 0) * (Cinv * τ ^ (5 / 2 : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hPsi_bd hcpos.le)
              (mul_le_mul (hD_inv_ub τ) hHG_inv (norm_nonneg _) (Real.exp_pos _).le)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
        _ = (5 * Real.exp (1 / 6)) * Real.exp (B_D 0) * Cinv *
              (2 * Real.exp (1 / 6) * C_gL * Real.exp (B_D 0) * Cn) * (c * (τ ^ (1 / 2 : ℝ) * τ ^ (5 / 2 : ℝ))) := by ring
        _ ≤ (5 * Real.exp (1 / 6)) * Real.exp (B_D 0) * Cinv *
              (2 * Real.exp (1 / 6) * C_gL * Real.exp (B_D 0) * Cn) * K0 ^ 3 := by
            rw [htau_pow]; gcongr
        _ = M_small := rfl
        _ ≤ M := le_max_left _ _
    · -- Subcase B: `K₀ c^{-1/3} < τ` (one IBP along `[τ, ∞)` using `fctWarpI = 0`)
      have hm_ge_2L : ∀ t : ℝ, K0 * c ^ (-(1 / 3 : ℝ)) ≤ t → 2 * |L1| ≤ hankelEdgeM t := by
        intro t ht
        rcases le_or_gt t 2 with ht2 | ht2
        · have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
          have hlo := hankelEdgeM_ge_sq_tenth ht0.le ht2
          have h1 : K0 ^ 2 * c ^ (-(2 / 3 : ℝ)) ≤ t ^ 2 := by
            have hsq := pow_le_pow_left₀ (by positivity) ht 2
            have heq : (K0 * c ^ (-(1 / 3 : ℝ))) ^ 2 = K0 ^ 2 * c ^ (-(2 / 3 : ℝ)) := by
              rw [mul_pow, ← Real.rpow_natCast (c ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hcpos.le]
              congr 2; norm_num
            linarith
          have hK0_sq : 20 * |CL1| ≤ K0 ^ 2 := by
            rw [show K0 ^ 2 = 20 * |CL1| + 1 from Real.sq_sqrt (by positivity)]; linarith
          calc 2 * |L1| ≤ 2 * (|CL1| * c ^ (-(2 / 3 : ℝ))) := by gcongr
            _ = (20 * |CL1|) * c ^ (-(2 / 3 : ℝ)) / 10 := by ring
            _ ≤ K0 ^ 2 * c ^ (-(2 / 3 : ℝ)) / 10 := by gcongr
            _ ≤ t ^ 2 / 10 := by gcongr
            _ ≤ hankelEdgeM t := hlo
        · have hlo := hankelEdgeM_ge_two_fifths ht2.le
          have hc23 : 5 * |CL1| ≤ c ^ (2 / 3 : ℝ) := by
            have h13 : 5 * |CL1| + 1 ≤ c ^ (1 / 3 : ℝ) := (le_max_right _ _).trans hc13_ge
            have h23 : c ^ (1 / 3 : ℝ) ≤ c ^ (2 / 3 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
            linarith
          have hL_le_fifth : |L1| ≤ 1 / 5 := by
            rw [Real.rpow_neg hcpos.le, ← div_eq_mul_inv] at hL1_abs
            calc |L1| ≤ |CL1| / c ^ (2 / 3 : ℝ) := hL1_abs
              _ ≤ 1 / 5 := by
                  rw [div_le_iff₀ (Real.rpow_pos_of_pos hcpos _)]; linarith
          linarith
      have hP_lb : ∀ t : ℝ, K0 * c ^ (-(1 / 3 : ℝ)) ≤ t →
          (1 / 2 : ℝ) * hankelEdgeM t ≤ ‖fctRayP L1 ((t : ℂ) * Complex.I)‖ ∧
          fctRayP L1 ((t : ℂ) * Complex.I) = ((L1 - hankelEdgeM t : ℝ) : ℂ) ∧
          fctRayP L1 ((t : ℂ) * Complex.I) ≠ 0 := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
        have hm2 := hm_ge_2L t ht
        have hPe : fctRayP L1 ((t : ℂ) * Complex.I) = ((L1 - hankelEdgeM t : ℝ) : ℂ) := by
          unfold fctRayP
          rw [stripG_imag_eq_neg_m ht0.ne', abs_of_pos ht0]
          push_cast; ring
        have hge : (1 / 2 : ℝ) * hankelEdgeM t ≤ |L1 - hankelEdgeM t| := by
          have := neg_abs_le L1
          have := le_abs_self L1
          rw [abs_of_nonpos (by linarith)]
          linarith
        have hP_ne : fctRayP L1 ((t : ℂ) * Complex.I) ≠ 0 := by
          rw [hPe]; exact Complex.ofReal_ne_zero.mpr (ne_of_lt (by linarith [hm2, hankelEdgeM_pos ht0, le_abs_self L1]))
        refine ⟨by rw [hPe, Complex.norm_real, Real.norm_eq_abs]; exact hge, hPe, hP_ne⟩
      -- Derivative and bounds for `W_edge(t) := fctRayW K4 ε c L1 α (t * I)` on `t ≥ K0 * c^{-(1/3)}`
      let f1 : ℝ → ℂ := fun t => (1 - (t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))
      let f2 : ℝ → ℂ := fun t => Complex.exp (binetDiff c ((t : ℂ) * Complex.I))
      let f3 : ℝ → ℂ := fun t => fctDcompAt K4 c α ((t : ℂ) * Complex.I)
      let f4 : ℝ → ℂ := fun t => ctHG ε ((t : ℂ) * Complex.I)
      let f5 : ℝ → ℂ := fun t =>
        1 - (L1 : ℂ) * (1 - FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) / fctRayP L1 ((t : ℂ) * Complex.I)
      let W_edge : ℝ → ℂ := fun t => fctRayW K4 ε c L1 α ((t : ℂ) * Complex.I)
      have hW_eq_prod : ∀ t : ℝ, K0 * c ^ (-(1 / 3 : ℝ)) ≤ t →
          W_edge t = (f1 t * f2 t * f3 t) * (f4 t * f5 t) := fun t ht => by
        have hPne := (hP_lb t ht).2.2
        have hfac := fctRayW_eq_factor (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α) (by simp) hPne
        simpa only [W_edge, f1, f2, f3, f4, f5, a, mul_assoc] using hfac
      have hf1_deriv : ∀ t : ℝ, ∃ d1, HasDerivAt f1 d1 t ∧
          ‖f1 t‖ = (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) ∧
          ‖d1‖ ≤ (1 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := fun t => by
        have hcd := cpow_line_hasDerivAt 1 (-Complex.I) (-(1 / 2 : ℂ)) (slit_one_sub t)
        have hfun : (fun s : ℝ => (1 + (-Complex.I) * (s : ℂ)) ^ (-(1 / 2 : ℂ))) = f1 := by
          funext s; simp only [f1]; ring_nf
        rw [hfun] at hcd
        have hn : ‖1 - (t : ℂ) * Complex.I‖ = Real.sqrt (1 + t ^ 2) := by
          rw [Complex.norm_eq_sqrt_sq_add_sq]
          congr 1
          simp [Complex.sub_re, Complex.sub_im]
        have hf1_eq : ‖f1 t‖ = (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by
          have hh : -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) := by push_cast; ring
          simp only [f1]; rw [hh, Complex.norm_cpow_real, hn, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
          congr 1; ring
        have h1t_ge : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
        have hneg32 : ‖((1 + (-Complex.I) * (t : ℂ)) ^ (-(1 / 2 : ℂ) - 1))‖ ≤ (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by
          have hh : -(1 / 2 : ℂ) - 1 = ((-(3 / 2) : ℝ) : ℂ) := by push_cast; ring
          have heq : 1 + (-Complex.I) * (t : ℂ) = 1 - (t : ℂ) * Complex.I := by ring
          rw [hh, heq, Complex.norm_cpow_real, hn, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
          calc (1 + t ^ 2) ^ ((1 / 2 : ℝ) * -(3 / 2)) = (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) := by congr 1; ring
            _ ≤ (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_le h1t_ge (by norm_num)
        refine ⟨(-(1 / 2 : ℂ)) * (-Complex.I) * (1 + (-Complex.I) * (t : ℂ)) ^ (-(1 / 2 : ℂ) - 1), hcd, hf1_eq, ?_⟩
        rw [norm_mul, norm_mul, norm_neg, norm_neg, Complex.norm_I, mul_one]
        have hnh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        rw [hnh]
        exact mul_le_mul_of_nonneg_left hneg32 (by norm_num)
      have hf2_deriv : ∀ t : ℝ, ∃ d2, HasDerivAt f2 d2 t ∧ ‖f2 t‖ ≤ Real.exp (1 / 6) ∧
          ‖d2‖ ≤ (1 / 2 : ℝ) * Real.exp (1 / 6) := fun t => by
        have hopen : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
        have hB_hol : DifferentiableOn ℂ (binetDiff c) {z : ℂ | z.re < 1} := binetDiff_differentiableOn hcpos
        have hball : closedBall ((t : ℂ) * Complex.I) (1 / 2) ⊆ {z : ℂ | z.re < 1} := fun z hz => by
          have h1 := Complex.abs_re_le_norm (z - (t : ℂ) * Complex.I)
          have h2 : ‖z - (t : ℂ) * Complex.I‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hz
          have hre : z.re ≤ 1 / 2 := (abs_le.mp (by simpa using h1.trans h2)).2
          exact hre.trans_lt (by norm_num)
        have hM_sph : ∀ z ∈ sphere ((t : ℂ) * Complex.I) (1 / 2), ‖binetDiff c z‖ ≤ 1 / 4 := fun z hz => by
          have hre : z.re ≤ 1 / 2 := by
            have h1 := Complex.abs_re_le_norm (z - (t : ℂ) * Complex.I)
            have h2 : ‖z - (t : ℂ) * Complex.I‖ = 1 / 2 := by simpa [dist_eq_norm] using hz
            exact (abs_le.mp (by simpa using h1.trans_eq h2)).2
          have hb := binetDiff_norm_le hcpos (by linarith : z.re < 1)
          have hinv : 1 / (1 - z.re) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
          calc ‖binetDiff c z‖ ≤ 1 / (12 * c) * (2 + 1) := hb.trans (by gcongr)
            _ ≤ 1 / (12 * 1) * (2 + 1) := by gcongr
            _ = 1 / 4 := by norm_num
        have hcauchy := (cauchy_deriv_two (by norm_num : (0 : ℝ) < 1 / 2) (hB_hol.mono hball) hM_sph).1
        have hderivB : HasDerivAt (fun s : ℝ => binetDiff c ((s : ℂ) * Complex.I))
            (Complex.I * deriv (binetDiff c) ((t : ℂ) * Complex.I)) t := by
          have hdb := (hB_hol.differentiableAt (hopen.mem_nhds (by simp : ((t : ℂ) * Complex.I).re < 1))).hasDerivAt
          have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
            simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
          exact (hdb.scomp t hl).congr_deriv (smul_eq_mul _ _)
        have hB0 : ‖f2 t‖ ≤ Real.exp (1 / 6) := by
          have hb := binetDiff_norm_le hcpos (ζ := (t : ℂ) * Complex.I) (by simp)
          have h16 : ‖binetDiff c ((t : ℂ) * Complex.I)‖ ≤ 1 / 6 := by
            have h12 : (1 : ℝ) / (12 * c) ≤ 1 / 12 :=
              div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
            simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, sub_zero] at hb
            linarith
          rw [show f2 t = Complex.exp (binetDiff c ((t : ℂ) * Complex.I)) from rfl, Complex.norm_exp]
          exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans h16)
        refine ⟨Complex.I * deriv (binetDiff c) ((t : ℂ) * Complex.I) * f2 t,
          (hderivB.cexp).congr_deriv (mul_comm _ _), hB0, ?_⟩
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
        have hd_le : ‖deriv (binetDiff c) ((t : ℂ) * Complex.I)‖ ≤ 1 / 2 := hcauchy.trans_eq (by norm_num)
        exact mul_le_mul hd_le hB0 (norm_nonneg _) (by norm_num)
      have hf3_deriv : ∀ t : ℝ, ∃ d3, HasDerivAt f3 d3 t ∧ ‖f3 t‖ ≤ Real.exp (B_D 0) ∧
          ‖d3‖ ≤ B_D 1 * Real.exp (B_D 0) := fun t => by
        have hθ := contDiff_fctThetaD hv hsupp
        let G0 : ℝ → ℂ := fun s => ((v s : ℝ) : ℂ) + Complex.I * ((fctThetaD v s : ℝ) : ℂ)
        let G1 : ℝ → ℂ := fun s => ((deriv v s : ℝ) : ℂ) + Complex.I * ((deriv (fctThetaD v) s : ℝ) : ℂ)
        have hf3_eq : f3 = fun s : ℝ => Complex.exp (G0 s) := by
          funext s
          change fctDcomp K4 (fctWarpAlpha h) ε c ((s : ℂ) * Complex.I) = _
          rw [hvD, stripCompGExt_left]
        have hdG0 : HasDerivAt G0 (G1 t) t := by
          have hv_d := ((hv.differentiable (by simp)) t).hasDerivAt.ofReal_comp
          have hθ_d := (((hθ.differentiable (by simp)) t).hasDerivAt.ofReal_comp).const_mul Complex.I
          exact hv_d.add hθ_d
        have hG1_bd : ‖G1 t‖ ≤ B_D 1 := by
          have hb1 := hvB 1 (by norm_num) ((t : ℂ) * Complex.I) ⟨by simp, by simp⟩
          rw [stripCompGExt_left, ← iteratedDeriv_fctThetaD hv hsupp 1, iteratedDeriv_one, iteratedDeriv_one] at hb1
          exact hb1
        refine ⟨G1 t * Complex.exp (G0 t), ?_, hD_ub t, ?_⟩
        · rw [hf3_eq]; exact hdG0.cexp.congr_deriv (mul_comm _ _)
        · rw [norm_mul]
          have hexp_eq : Complex.exp (G0 t) = f3 t := by rw [hf3_eq]
          rw [hexp_eq]
          exact mul_le_mul hG1_bd (hD_ub t) (norm_nonneg _) hB1_nn
      have hf5_deriv : ∀ t : ℝ, K0 * c ^ (-(1 / 3 : ℝ)) ≤ t →
          ∃ d5, HasDerivAt f5 d5 t ∧ ‖f5 t‖ ≤ 1 + C1s ∧ ‖d5‖ ≤ (Ckd + 40 * C1s) / t := fun t ht => by
        have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
        obtain ⟨hPlb, hPe, hPne⟩ := hP_lb t ht
        have hza : ((t : ℂ) * Complex.I) + (a : ℂ) ≠ 0 :=
          FctPhiKill.add_ofReal_ne_zero_of_re_nonneg hapos (by simp)
        have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
        have hpk_d : HasDerivAt (fun s : ℝ => FctPhiKill.phiKill a ((s : ℂ) * Complex.I))
            (deriv (fun s : ℝ => FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) t) t := by
          have hd_c := (FctPhiKill.hasDerivAt_phiPQ (p := 8) (q := 8) (by norm_num) (by norm_num) hza).differentiableAt
          have hc := hd_c.hasDerivAt.comp t hl
          exact hc.congr_deriv hc.deriv.symm
        have hnum_d : HasDerivAt (fun s : ℝ => (L1 : ℂ) * (1 - FctPhiKill.phiKill a ((s : ℂ) * Complex.I)))
            (-(L1 : ℂ) * deriv (fun s : ℝ => FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) t) t := by
          simpa using ((hasDerivAt_const t (1 : ℂ)).sub hpk_d).const_mul (L1 : ℂ)
        have hden_eq : (fun s : ℝ => fctRayP L1 ((s : ℂ) * Complex.I)) =ᶠ[𝓝 t]
            fun s : ℝ => ((L1 - hankelEdgeM s : ℝ) : ℂ) := by
          filter_upwards [isOpen_Ioi.mem_nhds ht0] with s hs
          unfold fctRayP
          rw [stripG_imag_eq_neg_m hs.ne', abs_of_pos hs]
          push_cast; ring
        have hden_d : HasDerivAt (fun s : ℝ => fctRayP L1 ((s : ℂ) * Complex.I))
            ((-hankelEdgeM' t : ℝ) : ℂ) t := by
          have hd_m : HasDerivAt (fun s : ℝ => L1 - hankelEdgeM s) (-hankelEdgeM' t) t := by
            simpa using (hasDerivAt_const t L1).fun_sub (hankelEdgeM_hasDerivAt ht0)
          exact hd_m.ofReal_comp.congr_of_eventuallyEq hden_eq
        have hq := hnum_d.div hden_d hPne
        have hf5_eq : f5 = fun s : ℝ => 1 - (L1 : ℂ) * (1 - FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) /
            fctRayP L1 ((s : ℂ) * Complex.I) := rfl
        have h1s_bd : ‖1 - FctPhiKill.phiKill a ((t : ℂ) * Complex.I)‖ ≤ C1s :=
          (h1sCpk hapos (by simp)).1
        have hmpos : 0 < hankelEdgeM t := hankelEdgeM_pos ht0
        have hm2 := hm_ge_2L t ht
        have hL_div_P : |L1| / ‖fctRayP L1 ((t : ℂ) * Complex.I)‖ ≤ 1 := by
          rw [div_le_one (norm_pos_iff.mpr hPne)]
          linarith [hPlb]
        have h1_sub : ‖f5 t‖ ≤ 1 + C1s := by
          calc ‖f5 t‖ ≤ ‖(1 : ℂ)‖ + ‖(L1 : ℂ) * (1 - FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) /
                  fctRayP L1 ((t : ℂ) * Complex.I)‖ := norm_sub_le _ _
            _ = 1 + (|L1| / ‖fctRayP L1 ((t : ℂ) * Complex.I)‖) *
                  ‖1 - FctPhiKill.phiKill a ((t : ℂ) * Complex.I)‖ := by
                rw [norm_one, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]; ring
            _ ≤ 1 + 1 * C1s := by gcongr
            _ = 1 + C1s := by ring
        refine ⟨_, ((hasDerivAt_const t (1 : ℂ)).fun_sub hq).congr_deriv (zero_sub _), h1_sub, ?_⟩
        have hPpos : 0 < ‖fctRayP L1 ((t : ℂ) * Complex.I)‖ := norm_pos_iff.mpr hPne
        have hP2_pos : 0 < ‖fctRayP L1 ((t : ℂ) * Complex.I)‖ ^ 2 := sq_pos_of_pos hPpos
        have hkd_t := hkd hapos ht0
        have hm_div := hankelEdgeM_deriv_div_le ht0
        have hm'_nn : 0 ≤ hankelEdgeM' t := (by positivity : 0 ≤ t / (1 + t ^ 2)).trans (FctCuspEdge.hankelEdgeM'_bounds ht0).1
        have hm_div_P : hankelEdgeM' t / ‖fctRayP L1 ((t : ℂ) * Complex.I)‖ ≤ 40 / t := by
          calc hankelEdgeM' t / ‖fctRayP L1 ((t : ℂ) * Complex.I)‖
              ≤ hankelEdgeM' t / ((1 / 2 : ℝ) * hankelEdgeM t) :=
                div_le_div_of_nonneg_left hm'_nn (by positivity) hPlb
            _ = 2 * (hankelEdgeM' t / hankelEdgeM t) := by ring
            _ ≤ 2 * (20 / t) := by gcongr
            _ = 40 / t := by ring
        rw [norm_neg, norm_div, norm_pow]
        have hnum_le : ‖(-(L1 : ℂ) * deriv (fun s : ℝ => FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) t) *
              fctRayP L1 ((t : ℂ) * Complex.I) -
              (L1 : ℂ) * (1 - FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) *
                ((-hankelEdgeM' t : ℝ) : ℂ)‖ ≤
            |L1| * (Ckd / t) * ‖fctRayP L1 ((t : ℂ) * Complex.I)‖ +
              |L1| * C1s * hankelEdgeM' t := by
          have h1 : ‖(-(L1 : ℂ) * deriv (fun s : ℝ => FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) t) *
              fctRayP L1 ((t : ℂ) * Complex.I)‖ ≤
              |L1| * (Ckd / t) * ‖fctRayP L1 ((t : ℂ) * Complex.I)‖ := by
            rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkd_t (abs_nonneg _)) (norm_nonneg _)
          have h2 : ‖(L1 : ℂ) * (1 - FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) *
              ((-hankelEdgeM' t : ℝ) : ℂ)‖ ≤ |L1| * C1s * hankelEdgeM' t := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_neg, abs_of_nonneg hm'_nn]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1s_bd (abs_nonneg _)) hm'_nn
          exact (norm_sub_le _ _).trans (add_le_add h1 h2)
        calc ‖_‖ / ‖fctRayP L1 ((t : ℂ) * Complex.I)‖ ^ 2
            ≤ (|L1| * (Ckd / t) * ‖fctRayP L1 ((t : ℂ) * Complex.I)‖ + |L1| * C1s * hankelEdgeM' t) /
                ‖fctRayP L1 ((t : ℂ) * Complex.I)‖ ^ 2 := div_le_div_of_nonneg_right hnum_le hP2_pos.le
          _ = (|L1| / ‖fctRayP L1 ((t : ℂ) * Complex.I)‖) * (Ckd / t) +
                (|L1| / ‖fctRayP L1 ((t : ℂ) * Complex.I)‖) * C1s *
                  (hankelEdgeM' t / ‖fctRayP L1 ((t : ℂ) * Complex.I)‖) := by
              field_simp [hPpos.ne']
          _ ≤ 1 * (Ckd / t) + 1 * C1s * (40 / t) := by
              have hCkd_nn : 0 ≤ Ckd / t := by positivity
              gcongr
          _ = (Ckd + 40 * C1s) / t := by ring
      -- Combine `f1, f2, f3, f4, f5` into `W_edge` differentiability and bounds on `{t | K0 * c^{-(1/3)} < t}`
      let U : Set ℝ := Ioi (K0 * c ^ (-(1 / 3 : ℝ)))
      have hU_open : IsOpen U := isOpen_Ioi
      have hW_deriv_all : ∀ t ∈ U, ∃ dW, HasDerivAt W_edge dW t ∧
          (t ≤ 2 → ‖W_edge t‖ ≤ C_W_n0 * t ^ (-(5 / 2 : ℝ)) ∧ ‖dW‖ ≤ C_W_n1 * t ^ (-(7 / 2 : ℝ))) ∧
          (2 ≤ t → ‖W_edge t‖ ≤ C_W_f0 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + t) * Real.exp (-(π * t)) ∧
            ‖dW‖ ≤ C_W_f1 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + t) * Real.exp (-(π * t))) := fun t htU => by
        have ht : K0 * c ^ (-(1 / 3 : ℝ)) ≤ t := le_of_lt htU
        have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
        obtain ⟨d1, hd1, hf1_t, hd1_t⟩ := hf1_deriv t
        have hf1_0 : ‖f1 t‖ ≤ 1 := by
          rw [hf1_t]; exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg t]) (by norm_num)
        have hd1_bd : ‖d1‖ ≤ 1 / 2 := by
          refine hd1_t.trans ?_
          calc (1 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) ≤ (1 / 2 : ℝ) * 1 := by
                gcongr
                exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg t]) (by norm_num)
            _ = 1 / 2 := mul_one _
        obtain ⟨d2, hd2, hf2_0, hd2_bd⟩ := hf2_deriv t
        obtain ⟨d3, hd3, hf3_0, hd3_bd⟩ := hf3_deriv t
        obtain ⟨d5, hd5, hf5_0, hd5_bd⟩ := hf5_deriv t ht
        have hd4 : HasDerivAt f4 (deriv f4 t) t :=
          ((hHG_c2.differentiableOn (by norm_num)).differentiableAt (isOpen_ne.mem_nhds ht0.ne')).hasDerivAt
        have hd123 := (hd1.mul hd2).mul hd3
        have hf123_0 : ‖f1 t * f2 t * f3 t‖ ≤ C_pref0 := by
          rw [norm_mul, norm_mul]
          calc ‖f1 t‖ * ‖f2 t‖ * ‖f3 t‖ ≤ 1 * Real.exp (1 / 6) * Real.exp (B_D 0) :=
                mul_le_mul (mul_le_mul hf1_0 hf2_0 (norm_nonneg _) zero_le_one) hf3_0 (norm_nonneg _) (by positivity)
            _ = C_pref0 := by simp only [C_pref0]; ring
        have hd123_bd : ‖(d1 * f2 t + f1 t * d2) * f3 t + f1 t * f2 t * d3‖ ≤ C_pref1 := by
          calc ‖(d1 * f2 t + f1 t * d2) * f3 t + f1 t * f2 t * d3‖
              ≤ (‖d1‖ * ‖f2 t‖ + ‖f1 t‖ * ‖d2‖) * ‖f3 t‖ + ‖f1 t‖ * ‖f2 t‖ * ‖d3‖ := by
                refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
                · rw [norm_mul]; exact mul_le_mul_of_nonneg_right
                    ((norm_add_le _ _).trans (by simp only [norm_mul]; exact le_rfl)) (norm_nonneg _)
                · simp only [norm_mul]; exact le_rfl
            _ ≤ ((1 / 2) * Real.exp (1 / 6) + 1 * ((1 / 2) * Real.exp (1 / 6))) * Real.exp (B_D 0) +
                  1 * Real.exp (1 / 6) * (B_D 1 * Real.exp (B_D 0)) := by
                gcongr
            _ = C_pref1 := by simp only [C_pref1]; ring
        have hd45 := hd4.mul hd5
        have hprod := hd123.mul hd45
        have hev_W : (fun s : ℝ => (f1 s * f2 s * f3 s) * (f4 s * f5 s)) =ᶠ[𝓝 t] W_edge := by
          filter_upwards [hU_open.mem_nhds htU] with s hs
          exact (hW_eq_prod s hs.le).symm
        have hW_hd := hprod.congr_of_eventuallyEq hev_W.symm
        refine ⟨_, hW_hd, fun ht2 => ?_, fun ht2 => ?_⟩
        · obtain ⟨hf4_0, hd4_bd, _⟩ := hHG_near t ht0 ht2
          have hf45_0 : ‖f4 t * f5 t‖ ≤ C_f45_n0 * t ^ (-(5 / 2 : ℝ)) := by
            rw [norm_mul]
            calc ‖f4 t‖ * ‖f5 t‖ ≤ (Cn * t ^ (-(5 / 2 : ℝ))) * (1 + C1s) := mul_le_mul hf4_0 hf5_0 (norm_nonneg _) (by positivity)
              _ = C_f45_n0 * t ^ (-(5 / 2 : ℝ)) := by simp only [C_f45_n0]; ring
          have hd45_bd : ‖deriv f4 t * f5 t + f4 t * d5‖ ≤ C_f45_n1 * t ^ (-(7 / 2 : ℝ)) := by
            have hinv_pow : t ^ (-(5 / 2 : ℝ)) * (1 / t) = t ^ (-(7 / 2 : ℝ)) := by
              rw [one_div, ← Real.rpow_neg_one t, ← Real.rpow_add ht0]; congr 1; norm_num
            calc ‖deriv f4 t * f5 t + f4 t * d5‖
                ≤ ‖deriv f4 t‖ * ‖f5 t‖ + ‖f4 t‖ * ‖d5‖ := by
                  simpa [norm_mul] using norm_add_le (deriv f4 t * f5 t) (f4 t * d5)
              _ ≤ (Cn * t ^ (-(7 / 2 : ℝ))) * (1 + C1s) +
                    (Cn * t ^ (-(5 / 2 : ℝ))) * ((Ckd + 40 * C1s) / t) := by
                  exact add_le_add (mul_le_mul hd4_bd hf5_0 (norm_nonneg _) (by positivity))
                    (mul_le_mul hf4_0 hd5_bd (norm_nonneg _) (by positivity))
              _ = Cn * (1 + C1s) * t ^ (-(7 / 2 : ℝ)) +
                    Cn * (Ckd + 40 * C1s) * (t ^ (-(5 / 2 : ℝ)) * (1 / t)) := by ring
              _ = Cn * ((1 + C1s) + (Ckd + 40 * C1s)) * t ^ (-(7 / 2 : ℝ)) := by rw [hinv_pow]; ring
              _ ≤ C_f45_n1 * t ^ (-(7 / 2 : ℝ)) := by
                  have hCn0 : 0 ≤ Cn := le_max_of_le_left hCnp0
                  have hsum : (1 + C1s) + (Ckd + 40 * C1s) ≤ 2 * (1 + C1s) + Ckd + 40 * C1s := by linarith [hC1s0]
                  simp only [C_f45_n1]
                  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hCn0) (by positivity)
          have ht_le_pow : t ^ (-(5 / 2 : ℝ)) ≤ 2 * t ^ (-(7 / 2 : ℝ)) := by
            have h1 : t ^ (-(5 / 2 : ℝ)) = t * t ^ (-(7 / 2 : ℝ)) := by
              have hadd := Real.rpow_add ht0 (1 : ℝ) (-(7 / 2 : ℝ))
              rw [show (1 : ℝ) + -(7 / 2 : ℝ) = -(5 / 2 : ℝ) by norm_num, Real.rpow_one] at hadd
              exact hadd
            rw [h1]; exact mul_le_mul_of_nonneg_right ht2 (by positivity)
          refine ⟨?_, ?_⟩
          · rw [hW_eq_prod t ht, norm_mul]
            exact (mul_le_mul hf123_0 hf45_0 (norm_nonneg _) (by positivity)).trans_eq (by simp only [C_W_n0]; ring)
          · refine (norm_add_le _ _).trans ?_
            calc ‖((d1 * f2 t + f1 t * d2) * f3 t + f1 t * f2 t * d3) * (f4 t * f5 t)‖ +
                  ‖(f1 t * f2 t * f3 t) * (deriv f4 t * f5 t + f4 t * d5)‖
                = ‖(d1 * f2 t + f1 t * d2) * f3 t + f1 t * f2 t * d3‖ * ‖f4 t * f5 t‖ +
                    ‖f1 t * f2 t * f3 t‖ * ‖deriv f4 t * f5 t + f4 t * d5‖ := by simp only [norm_mul]
              _ ≤ C_pref1 * (C_f45_n0 * t ^ (-(5 / 2 : ℝ))) + C_pref0 * (C_f45_n1 * t ^ (-(7 / 2 : ℝ))) :=
                  add_le_add (mul_le_mul hd123_bd hf45_0 (norm_nonneg _) (by positivity))
                    (mul_le_mul hf123_0 hd45_bd (norm_nonneg _) (by positivity))
              _ ≤ C_pref1 * (C_f45_n0 * (2 * t ^ (-(7 / 2 : ℝ)))) + C_pref0 * (C_f45_n1 * t ^ (-(7 / 2 : ℝ))) := by
                  gcongr
              _ = C_W_n1 * t ^ (-(7 / 2 : ℝ)) := by simp only [C_W_n1]; ring
        · obtain ⟨hf4_0, hd4_bd⟩ := hHG_far t (by rw [abs_of_pos ht0]; linarith)
          rw [abs_of_pos ht0] at hf4_0 hd4_bd
          have hf123_t : ‖f1 t * f2 t * f3 t‖ ≤ C_pref0 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by
            rw [norm_mul, norm_mul, hf1_t]
            calc (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * ‖f2 t‖ * ‖f3 t‖
                ≤ (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (1 / 6) * Real.exp (B_D 0) := by gcongr
              _ = C_pref0 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by simp only [C_pref0]; ring
          have hd123_t : ‖(d1 * f2 t + f1 t * d2) * f3 t + f1 t * f2 t * d3‖ ≤
              C_pref1 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by
            calc ‖(d1 * f2 t + f1 t * d2) * f3 t + f1 t * f2 t * d3‖
                ≤ (‖d1‖ * ‖f2 t‖ + ‖f1 t‖ * ‖d2‖) * ‖f3 t‖ + ‖f1 t‖ * ‖f2 t‖ * ‖d3‖ := by
                  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
                  · rw [norm_mul]; exact mul_le_mul_of_nonneg_right
                      ((norm_add_le _ _).trans (by simp only [norm_mul]; exact le_rfl)) (norm_nonneg _)
                  · simp only [norm_mul]; exact le_rfl
              _ ≤ (((1 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))) * Real.exp (1 / 6) +
                      (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * ((1 / 2 : ℝ) * Real.exp (1 / 6))) * Real.exp (B_D 0) +
                    (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (1 / 6) * (B_D 1 * Real.exp (B_D 0)) := by
                  rw [hf1_t]; gcongr
              _ = C_pref1 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by simp only [C_pref1]; ring
          have h2le : (2 : ℝ) ≤ t := ht2
          have hf45_0 : ‖f4 t * f5 t‖ ≤ C_f45_f0 * (1 + t) * Real.exp (-(π * t)) := by
            rw [norm_mul]
            calc ‖f4 t‖ * ‖f5 t‖ ≤ (Cd * (1 + t) * Real.exp (-(π * t))) * (1 + C1s) :=
                  mul_le_mul hf4_0 hf5_0 (norm_nonneg _) (by positivity)
              _ = C_f45_f0 * (1 + t) * Real.exp (-(π * t)) := by simp only [C_f45_f0]; ring
          have hd45_bd : ‖deriv f4 t * f5 t + f4 t * d5‖ ≤ C_f45_f1 * (1 + t) * Real.exp (-(π * t)) := by
            have hinv2 : (Ckd + 40 * C1s) / t ≤ (Ckd + 40 * C1s) / 2 :=
              div_le_div_of_nonneg_left (by positivity) (by norm_num) h2le
            calc ‖deriv f4 t * f5 t + f4 t * d5‖
                ≤ ‖deriv f4 t‖ * ‖f5 t‖ + ‖f4 t‖ * ‖d5‖ := by
                  simpa [norm_mul] using norm_add_le (deriv f4 t * f5 t) (f4 t * d5)
              _ ≤ (Cd * (1 + t) * Real.exp (-(π * t))) * (1 + C1s) +
                    (Cd * (1 + t) * Real.exp (-(π * t))) * ((Ckd + 40 * C1s) / 2) :=
                  add_le_add (mul_le_mul hd4_bd hf5_0 (norm_nonneg _) (by positivity))
                    (mul_le_mul hf4_0 (hd5_bd.trans hinv2) (norm_nonneg _) (by positivity))
              _ = C_f45_f1 * (1 + t) * Real.exp (-(π * t)) := by simp only [C_f45_f1]; ring
          refine ⟨?_, ?_⟩
          · rw [hW_eq_prod t ht, norm_mul]
            exact (mul_le_mul hf123_t hf45_0 (norm_nonneg _) (by positivity)).trans_eq (by
              simp only [C_W_f0]; ring)
          · refine (norm_add_le _ _).trans ?_
            calc ‖((d1 * f2 t + f1 t * d2) * f3 t + f1 t * f2 t * d3) * (f4 t * f5 t)‖ +
                  ‖(f1 t * f2 t * f3 t) * (deriv f4 t * f5 t + f4 t * d5)‖
                = ‖(d1 * f2 t + f1 t * d2) * f3 t + f1 t * f2 t * d3‖ * ‖f4 t * f5 t‖ +
                    ‖f1 t * f2 t * f3 t‖ * ‖deriv f4 t * f5 t + f4 t * d5‖ := by simp only [norm_mul]
              _ ≤ (C_pref1 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))) * (C_f45_f0 * (1 + t) * Real.exp (-(π * t))) +
                    (C_pref0 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))) * (C_f45_f1 * (1 + t) * Real.exp (-(π * t))) :=
                  add_le_add (mul_le_mul hd123_t hf45_0 (norm_nonneg _) (by positivity))
                    (mul_le_mul hf123_t hd45_bd (norm_nonneg _) (by positivity))
              _ = C_W_f1 * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + t) * Real.exp (-(π * t)) := by
                  simp only [C_W_f1]; ring
      -- Exponential tail integral bound via explicit antiderivative
      have hexp_tail_int : ∀ {a0 T0 : ℝ}, 2 ≤ a0 → a0 ≤ T0 →
          ∫ t in a0..T0, (1 + t) * Real.exp (-(π * t)) ≤
            ((1 + a0) / π + 1 / π ^ 2) * Real.exp (-(π * a0)) := by
        intro a0 T0 ha0 hT0
        let F_t : ℝ → ℝ := fun t => -(((1 + t) / π + 1 / π ^ 2) * Real.exp (-(π * t)))
        have hF_d : ∀ t ∈ uIcc a0 T0, HasDerivAt F_t ((1 + t) * Real.exp (-(π * t))) t := fun t _ => by
          have hlin : HasDerivAt (fun s : ℝ => (1 + s) / π + 1 / π ^ 2) (1 / π) t := by
            simpa using (((hasDerivAt_id t).const_add 1).div_const π).add_const (1 / π ^ 2)
          have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(π * s))) (-π * Real.exp (-(π * t))) t := by
            simpa using (((hasDerivAt_id t).const_mul π).neg.exp).congr_deriv (mul_comm _ _)
          refine (hlin.mul hexp).neg.congr_deriv ?_
          have hpi0 : π ≠ 0 := Real.pi_ne_zero
          field_simp [hpi0]; ring
        have hint_t : IntervalIntegrable (fun t : ℝ => (1 + t) * Real.exp (-(π * t))) volume a0 T0 :=
          (Continuous.continuousOn (by fun_prop)).intervalIntegrable
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF_d hint_t]
        have hT0p : 0 ≤ T0 := by linarith
        have hFT_nonpos : F_t T0 ≤ 0 := by
          simp only [F_t]; have : 0 ≤ ((1 + T0) / π + 1 / π ^ 2) * Real.exp (-(π * T0)) := by
            have := Real.pi_pos; positivity
          linarith
        linarith
      -- `deriv W_edge` is continuous on `U` (`Ioi (K0 * c^{-(1/3)})`) since every factor is `C¹` on `U`
      have hW_deriv_cont : ContinuousOn (deriv W_edge) U := by
        have hc1_U : ContDiffOn ℝ 1 W_edge U := by
          have hf1_c : ContDiffOn ℝ 1 f1 U := by
            have h0 := @cpow_line_contDiffOn univ (1 : ℂ) (-Complex.I) (-(1 / 2 : ℂ)) (fun s _ => slit_one_sub s)
            exact ((h0.mono (subset_univ _)).congr fun s _ => by simp only [f1]; ring_nf).of_le (by norm_num)
          have hf2_c : ContDiffOn ℝ 1 f2 U := by
            have hopen : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
            have hBc := (binetDiff_differentiableOn hcpos).contDiffOn hopen
            have hline : ContDiff ℝ 2 (fun s : ℝ => (s : ℂ) * Complex.I) :=
              Complex.ofRealCLM.contDiff.mul contDiff_const
            exact ((hBc.restrict_scalars ℝ).comp hline.contDiffOn (fun s _ => by simp)).cexp.of_le (by norm_num)
          have hf3_c : ContDiffOn ℝ 1 f3 U := by
            have hθ := contDiff_fctThetaD hv hsupp
            have hg : ContDiff ℝ 2 (fun s : ℝ => ((v s : ℝ) : ℂ) + Complex.I * ((fctThetaD v s : ℝ) : ℂ)) :=
              (Complex.ofRealCLM.contDiff.comp (hv.of_le (by simp))).add
                (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hθ.of_le (by simp))))
            have hf3_eq : f3 = fun s : ℝ => Complex.exp (((v s : ℝ) : ℂ) + Complex.I * ((fctThetaD v s : ℝ) : ℂ)) :=
              funext fun s => by
                change fctDcomp K4 (fctWarpAlpha h) ε c ((s : ℂ) * Complex.I) = _
                rw [hvD, stripCompGExt_left]
            rw [hf3_eq]
            exact hg.cexp.contDiffOn.of_le (by norm_num)
          have hf4_c : ContDiffOn ℝ 1 f4 U :=
            (hHG_c2.mono fun s hs => (lt_of_le_of_lt (by positivity) hs).ne').of_le (by norm_num)
          have hf5_c : ContDiffOn ℝ 1 f5 U := by
            have hpk_c : ContDiffOn ℝ 1 (fun s : ℝ => FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) U :=
              ((FctSym.contDiff_phiKill_imag hapos).of_le (by norm_cast)).contDiffOn
            have hP_c : ContDiffOn ℝ 1 (fun s : ℝ => fctRayP L1 ((s : ℂ) * Complex.I)) U := by
              have hUm : U ⊆ Ioi 0 := fun s hs => lt_of_le_of_lt (by positivity) hs
              have hm_c : ContDiffOn ℝ 1 (fun s : ℝ => ((L1 - hankelEdgeM s : ℝ) : ℂ)) U :=
                Complex.ofRealCLM.contDiff.comp_contDiffOn
                  (contDiffOn_const.sub ((CtMDeriv.contDiffOn_hankelEdgeM.mono hUm).of_le (by norm_num)))
              exact hm_c.congr fun s hs => (hP_lb s (le_of_lt hs)).2.1
            have hL1c_cd : ContDiffOn ℝ 1 (fun _ : ℝ => (L1 : ℂ)) U := contDiffOn_const
            have h1_cd : ContDiffOn ℝ 1 (fun _ : ℝ => (1 : ℂ)) U := contDiffOn_const
            have hsub_pk : ContDiffOn ℝ 1 (fun s : ℝ => 1 - FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) U :=
              h1_cd.sub hpk_c
            have h1s : ContDiffOn ℝ 1 (fun s : ℝ =>
                (L1 : ℂ) * (1 - FctPhiKill.phiKill a ((s : ℂ) * Complex.I)) / fctRayP L1 ((s : ℂ) * Complex.I)) U :=
              (hL1c_cd.mul hsub_pk).div hP_c fun s (hs : s ∈ U) => (hP_lb s (le_of_lt hs)).2.2
            exact h1_cd.sub h1s
          have hc_prod : ContDiffOn ℝ 1 (fun s : ℝ => (f1 s * f2 s * f3 s) * (f4 s * f5 s)) U :=
            ((hf1_c.mul hf2_c).mul hf3_c).mul (hf4_c.mul hf5_c)
          exact hc_prod.congr fun s hs => hW_eq_prod s (le_of_lt hs)
        exact ((contDiffOn_succ_iff_deriv_of_isOpen hU_open (n := 0)).mp hc1_U).2.2.continuousOn
      -- Relate `∫₀^τ K₀ A_ε` to `-∫_τ^T K₀ A_ε` via `fctWarpI = 0`, apply IBP on `[τ, T]` and let `T → ∞`
      have hI_pair : FctWarpZero K4 ε c L1 α := (fctWarpPair_spec h hε hc_pair).2
      let E_mel : ℝ → ℂ := fun t => Complex.exp ((c : ℂ) * mellinPhi ((t : ℂ) * Complex.I) (fctXi1 L1))
      have hEmel_norm : ∀ t : ℝ, ‖E_mel t‖ = 1 := fun t => by
        simp only [E_mel, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, re_mellinPhi_imag_eq_zero (fctXi1_pos L1) t, mul_zero, Real.exp_zero]
      have hEmel_d : ∀ t : ℝ, HasDerivAt E_mel ((c : ℂ) * Complex.I * fctRayP L1 ((t : ℂ) * Complex.I) * E_mel t) t :=
        fun t => by
          have hmp := hasDerivAt_mellinPhi_fct L1 (t := (t : ℂ) * Complex.I) (by simp)
          have hline : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
            simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
          have hcd := ((hmp.comp t hline).const_mul (c : ℂ)).cexp
          refine hcd.congr_deriv ?_
          unfold fctRayP; simp only [Function.comp_def, E_mel]; ring
      have hKA_eq : ∀ t : ℝ, K0 * c ^ (-(1 / 3 : ℝ)) < t →
          fctWarpKA K4 ε c L1 α ((t : ℂ) * Complex.I) =
            ((c : ℂ) * Complex.I)⁻¹ * ((((c : ℂ) * Complex.I * fctRayP L1 ((t : ℂ) * Complex.I) * E_mel t)) * W_edge t) := by
        intro t ht
        have hPne := (hP_lb t ht.le).2.2
        have hW := fctRayW_eq_factor (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α)
          (t := (t : ℂ) * Complex.I) (by simp) hPne
        have hEne : E_mel t ≠ 0 := Complex.exp_ne_zero _
        have hci : (c : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hcpos.ne') Complex.I_ne_zero
        unfold fctWarpKA fctWarpA mellinK0
        rw [show W_edge t = fctRayW K4 ε c L1 α ((t : ℂ) * Complex.I) from rfl, hW]
        simp only [E_mel]
        have h1_sub : fctRayP L1 ((t : ℂ) * Complex.I) *
            (1 - (L1 : ℂ) * (1 - FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) / fctRayP L1 ((t : ℂ) * Complex.I)) =
            stripG ((t : ℂ) * Complex.I) + (L1 : ℂ) * FctPhiKill.phiKill a ((t : ℂ) * Complex.I) := by
          have hPne' : stripG ((t : ℂ) * Complex.I) + (L1 : ℂ) ≠ 0 := hPne
          unfold fctRayP; field_simp [hPne']; ring
        have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
        calc _ = ((c : ℂ) * Complex.I)⁻¹ * ((c : ℂ) * Complex.I *
              (fctRayP L1 ((t : ℂ) * Complex.I) *
                (1 - (L1 : ℂ) * (1 - FctPhiKill.phiKill a ((t : ℂ) * Complex.I)) / fctRayP L1 ((t : ℂ) * Complex.I))) *
              ((1 - (t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c ((t : ℂ) * Complex.I)) *
                E_mel t * fctDcompAt K4 c α ((t : ℂ) * Complex.I) * ctHG ε ((t : ℂ) * Complex.I))) := by
              rw [h1_sub]; simp only [E_mel, a]; field_simp [hci, hc_ne]
          _ = _ := by ring
      have h_ibp_bd : ∀ T : ℝ, max 2 (τ + 1) ≤ T →
          c * ‖Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖ ≤
            c * ‖Complex.I * ∫ u in (0 : ℝ)..T, fctWarpIntegrand K4 ε c L1 α u‖ +
              ‖W_edge T‖ + ‖W_edge τ‖ + ∫ t in τ..T, ‖deriv W_edge t‖ := by
        intro T hT
        have hτT : τ ≤ T := by linarith [le_max_right 2 (τ + 1)]
        have h0τ : (0 : ℝ) ≤ τ := hτpos.le
        have h0T : (0 : ℝ) ≤ T := h0τ.trans hτT
        have hint_T : IntervalIntegrable (fctWarpIntegrand K4 ε c L1 α) volume 0 T :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le h0T).mpr (hI_pair.1.mono_set Ioc_subset_Ioi_self)
        have hint_τ : IntervalIntegrable (fctWarpIntegrand K4 ε c L1 α) volume 0 τ :=
          hint_T.mono_set (by rw [uIcc_of_le hτpos.le, uIcc_of_le h0T]; exact Icc_subset_Icc_right hτT)
        have hint_τT : IntervalIntegrable (fctWarpIntegrand K4 ε c L1 α) volume τ T :=
          hint_T.mono_set (by rw [uIcc_of_le hτT, uIcc_of_le h0T]; exact Icc_subset_Icc_left h0τ)
        have hsplit : (∫ u in (0 : ℝ)..τ, fctWarpIntegrand K4 ε c L1 α u) =
            (∫ u in (0 : ℝ)..T, fctWarpIntegrand K4 ε c L1 α u) -
              (∫ u in τ..T, fctWarpIntegrand K4 ε c L1 α u) := by
          have := intervalIntegral.integral_add_adjacent_intervals hint_τ hint_τT
          exact eq_sub_of_add_eq this
        have hW_diff_on : ∀ t ∈ uIcc τ T, HasDerivAt W_edge (deriv W_edge t) t := fun t ht => by
          rw [uIcc_of_le hτT] at ht
          obtain ⟨dW, hdW, _⟩ := hW_deriv_all t (lt_of_lt_of_le hτ_big ht.1)
          exact hdW.congr_deriv hdW.deriv.symm
        have hW_c1_cont : ContinuousOn (deriv W_edge) (uIcc τ T) :=
          hW_deriv_cont.mono (by rw [uIcc_of_le hτT]; intro s hs; exact lt_of_lt_of_le hτ_big hs.1)
        have hci0 : (c : ℂ) * Complex.I ≠ 0 :=
          mul_ne_zero (Complex.ofReal_ne_zero.mpr hcpos.ne') Complex.I_ne_zero
        have hE'W_pt : ∀ t : ℝ, K0 * c ^ (-(1 / 3 : ℝ)) < t →
            ((c : ℂ) * Complex.I * fctRayP L1 ((t : ℂ) * Complex.I) * E_mel t) * W_edge t =
              ((c : ℂ) * Complex.I) * fctWarpIntegrand K4 ε c L1 α t := fun t ht => by
          change _ = ((c : ℂ) * Complex.I) * fctWarpKA K4 ε c L1 α ((t : ℂ) * Complex.I)
          rw [hKA_eq t ht]; field_simp [hci0]
        have hint_Emel' : IntervalIntegrable
            (fun t : ℝ => (c : ℂ) * Complex.I * fctRayP L1 ((t : ℂ) * Complex.I) * E_mel t)
            volume τ T := by
          have hP_cont : ContinuousOn (fun t : ℝ => fctRayP L1 ((t : ℂ) * Complex.I)) (uIcc τ T) := by
            have hm_c : ContinuousOn (fun t : ℝ => ((L1 - hankelEdgeM t : ℝ) : ℂ)) (uIcc τ T) :=
              Complex.continuous_ofReal.comp_continuousOn
                (continuousOn_const.sub (hankelEdgeM_continuousOn.mono fun s hs => by
                  rw [uIcc_of_le hτT] at hs; exact h0τ.trans hs.1))
            refine hm_c.congr fun t ht => ?_
            rw [uIcc_of_le hτT] at ht
            exact (hP_lb t (hτ_big.le.trans ht.1)).2.1
          have hEmel_cont : Continuous E_mel := by
            refine Complex.continuous_exp.comp (continuous_const.mul ?_)
            have hg_c : ContinuousOn (fun t : ℝ => mellinPhi ((t : ℂ) * Complex.I) (fctXi1 L1)) univ := by
              intro t _
              have ht_abs : |((t : ℂ) * Complex.I).re| < 1 := by simp
              have hS := hasDerivAt_stripS0Tilde (ζ₀ := (t : ℂ) * Complex.I) ht_abs
              have hl := (hasDerivAt_id ((t : ℂ) * Complex.I)).mul_const
                (Complex.log ((Real.pi : ℂ) ^ 2 * (fctXi1 L1 : ℂ)))
              have hline : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
                simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
              have hfn : (fun y : ℂ => mellinPhi y (fctXi1 L1)) =
                  stripS0Tilde + fun y => y * Complex.log ((Real.pi : ℂ) ^ 2 * (fctXi1 L1 : ℂ)) := rfl
              exact (((by rw [hfn]; exact hS.add hl : HasDerivAt (fun y : ℂ => mellinPhi y (fctXi1 L1)) _ _).scomp t
                hline).continuousAt.continuousWithinAt)
            exact continuous_iff_continuousAt.mpr fun t => (hg_c t trivial).continuousAt Filter.univ_mem
          exact ((continuousOn_const.mul hP_cont).mul hEmel_cont.continuousOn).intervalIntegrable
        have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
          (fun t _ => hEmel_d t) hW_diff_on hint_Emel' hW_c1_cont.intervalIntegrable
        have hibp' : (∫ t in τ..T,
              ((c : ℂ) * Complex.I * fctRayP L1 ((t : ℂ) * Complex.I) * E_mel t) * W_edge t) =
            E_mel T * W_edge T - E_mel τ * W_edge τ - ∫ t in τ..T, E_mel t * deriv W_edge t := by
          rw [hibp]; ring
        have hE'W_eq : (∫ t in τ..T,
              ((c : ℂ) * Complex.I * fctRayP L1 ((t : ℂ) * Complex.I) * E_mel t) * W_edge t) =
            ((c : ℂ) * Complex.I) * (∫ t in τ..T, fctWarpIntegrand K4 ε c L1 α t) := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun t ht => ?_
          rw [uIcc_of_le hτT] at ht
          exact hE'W_pt t (lt_of_lt_of_le hτ_big ht.1)
        have hmul_eq : ((c : ℂ) * Complex.I) * (∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)) =
            ((c : ℂ) * Complex.I) * (∫ u in (0 : ℝ)..T, fctWarpIntegrand K4 ε c L1 α u) -
              (E_mel T * W_edge T - E_mel τ * W_edge τ - ∫ t in τ..T, E_mel t * deriv W_edge t) := by
          have hsub := congr_arg (((c : ℂ) * Complex.I) * ·) hsplit
          rw [mul_sub, ← hE'W_eq, hibp'] at hsub
          simpa only [fctWarpIntegrand] using hsub
        have hL_norm : ‖((c : ℂ) * Complex.I) * (∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I))‖ =
            c * ‖Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖ := by
          rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
        have hT_norm : ‖((c : ℂ) * Complex.I) * (∫ u in (0 : ℝ)..T, fctWarpIntegrand K4 ε c L1 α u)‖ =
            c * ‖Complex.I * ∫ u in (0 : ℝ)..T, fctWarpIntegrand K4 ε c L1 α u‖ := by
          rw [mul_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
        have hInt_norm : ‖∫ t in τ..T, E_mel t * deriv W_edge t‖ ≤ ∫ t in τ..T, ‖deriv W_edge t‖ := by
          have hint_EW : IntervalIntegrable (fun t : ℝ => ‖deriv W_edge t‖) volume τ T :=
            hW_c1_cont.norm.intervalIntegrable
          refine (intervalIntegral.norm_integral_le_of_norm_le hτT ?_ hint_EW).trans_eq rfl
          exact Filter.Eventually.of_forall fun t _ => by rw [norm_mul, hEmel_norm t, one_mul]
        rw [← hL_norm, hmul_eq]
        have htr1 : ‖E_mel T * W_edge T - E_mel τ * W_edge τ - ∫ t in τ..T, E_mel t * deriv W_edge t‖ ≤
            (‖W_edge T‖ + ‖W_edge τ‖) + ∫ t in τ..T, ‖deriv W_edge t‖ := by
          calc ‖E_mel T * W_edge T - E_mel τ * W_edge τ - ∫ t in τ..T, E_mel t * deriv W_edge t‖
              ≤ ‖E_mel T * W_edge T - E_mel τ * W_edge τ‖ + ‖∫ t in τ..T, E_mel t * deriv W_edge t‖ :=
                norm_sub_le _ _
            _ ≤ (‖E_mel T * W_edge T‖ + ‖E_mel τ * W_edge τ‖) + ∫ t in τ..T, ‖deriv W_edge t‖ :=
                add_le_add (norm_sub_le _ _) hInt_norm
            _ = (‖W_edge T‖ + ‖W_edge τ‖) + ∫ t in τ..T, ‖deriv W_edge t‖ := by
                rw [norm_mul, hEmel_norm T, one_mul, norm_mul, hEmel_norm τ, one_mul]
        have htr0 := norm_sub_le
          (((c : ℂ) * Complex.I) * (∫ u in (0 : ℝ)..T, fctWarpIntegrand K4 ε c L1 α u))
          (E_mel T * W_edge T - E_mel τ * W_edge τ - ∫ t in τ..T, E_mel t * deriv W_edge t)
        rw [hT_norm] at htr0
        exact htr0.trans (add_le_add_right htr1 _)
      -- Bound `‖W_edge T‖` for `2 ≤ T` and deduce `(1 + T) * exp(-π T) → 0`
      have hWT_bd : ∀ T : ℝ, 2 ≤ T → ‖W_edge T‖ ≤ C_W_f0 * (1 + T) * Real.exp (-(π * T)) := fun T hT2 => by
        have hTU : T ∈ U := hK0c_le_1.trans_lt (by linarith)
        obtain ⟨_, _, _, hfar⟩ := hW_deriv_all T hTU
        have h1T : (1 + T ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg T]) (by norm_num)
        calc ‖W_edge T‖ ≤ C_W_f0 * (1 + T ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + T) * Real.exp (-(π * T)) := (hfar hT2).1
          _ ≤ C_W_f0 * 1 * (1 + T) * Real.exp (-(π * T)) := by
              have hC0 : 0 ≤ C_W_f0 := by positivity
              have h1Tp : 0 ≤ 1 + T := by linarith
              have hep : 0 ≤ Real.exp (-(π * T)) := (Real.exp_pos _).le
              gcongr
          _ = C_W_f0 * (1 + T) * Real.exp (-(π * T)) := by ring
      have hT_lim : Filter.Tendsto
          (fun T : ℝ => c * ‖Complex.I * ∫ u in (0 : ℝ)..T, fctWarpIntegrand K4 ε c L1 α u‖ +
            C_W_f0 * (1 + T) * Real.exp (-(π * T)))
          Filter.atTop (𝓝 0) := by
        have hI_lim : Filter.Tendsto
            (fun T : ℝ => c * ‖Complex.I * ∫ u in (0 : ℝ)..T, fctWarpIntegrand K4 ε c L1 α u‖)
            Filter.atTop (𝓝 0) := by
          have ht0 := intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ)) hI_pair.1 Filter.tendsto_id
          have ht1 := ((ht0.const_mul Complex.I).norm).const_mul c
          have hz0 : c * ‖Complex.I * ∫ u in Ioi (0 : ℝ), fctWarpIntegrand K4 ε c L1 α u‖ = 0 := by
            have hIeq : Complex.I * ∫ u in Ioi (0 : ℝ), fctWarpIntegrand K4 ε c L1 α u = fctWarpI K4 ε c L1 α := rfl
            rw [hIeq, hI_pair.2, norm_zero, mul_zero]
          rwa [hz0] at ht1
        have hE_lim : Filter.Tendsto (fun T : ℝ => C_W_f0 * (1 + T) * Real.exp (-(π * T))) Filter.atTop (𝓝 0) := by
          have hpi_at : Filter.Tendsto (fun T : ℝ => π * T) Filter.atTop Filter.atTop :=
            Filter.Tendsto.const_mul_atTop Real.pi_pos Filter.tendsto_id
          have h0 : Filter.Tendsto (fun T : ℝ => Real.exp (-(π * T))) Filter.atTop (𝓝 0) :=
            Real.tendsto_exp_neg_atTop_nhds_zero.comp hpi_at
          have h1 : Filter.Tendsto (fun T : ℝ => (π * T) * Real.exp (-(π * T))) Filter.atTop (𝓝 0) := by
            have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hpi_at
            exact this.congr fun T => by simp [pow_one]
          have h2 : Filter.Tendsto (fun T : ℝ => T * Real.exp (-(π * T))) Filter.atTop (𝓝 0) := by
            have h2' := h1.const_mul (π⁻¹)
            rw [mul_zero] at h2'
            exact h2'.congr fun T => by
              dsimp only
              rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
          have h3 : Filter.Tendsto (fun T : ℝ => C_W_f0 * (Real.exp (-(π * T)) + T * Real.exp (-(π * T))))
              Filter.atTop (𝓝 0) := by
            simpa using (h0.add h2).const_mul C_W_f0
          refine h3.congr fun T => by ring
        simpa using hI_lim.add hE_lim
      let tailTerm : ℝ → ℝ := fun T : ℝ =>
        c * ‖Complex.I * ∫ u in (0 : ℝ)..T, fctWarpIntegrand K4 ε c L1 α u‖ +
          C_W_f0 * (1 + T) * Real.exp (-(π * T))
      have h_ibp' : ∀ T : ℝ, max 2 (τ + 1) ≤ T →
          c * ‖Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖ ≤
            (tailTerm T - C_W_f0 * (1 + T) * Real.exp (-(π * T))) +
              ‖W_edge T‖ + ‖W_edge τ‖ + ∫ t in τ..T, ‖deriv W_edge t‖ := fun T hT => by
        simpa [tailTerm] using h_ibp_bd T hT
      have hW_cont_τ : ContinuousOn (deriv W_edge) (Ici τ) :=
        hW_deriv_cont.mono fun s hs => lt_of_lt_of_le hτ_big hs
      rcases le_or_gt τ 2 with hτ2 | h2τ
      · -- Subcase B1: `K₀ c^{-1/3} < τ ≤ 2`
        have h_lim_bd : c * ‖Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖ ≤
            (C_W_n0 + (2 / 5) * C_W_n1 + 8 * I_tail) * τ ^ (-(5 / 2 : ℝ)) := by
          refine edge_subcase_B1 hτpos hτ2 (by positivity) (by positivity) (by positivity) rfl hW_cont_τ
            (fun t ht1 ht2 => by
              obtain ⟨dW, hdW, hnear, _⟩ := hW_deriv_all t (lt_of_lt_of_le hτ_big ht1)
              rw [hdW.deriv]; exact hnear ht2)
            (fun t ht2 => by
              obtain ⟨dW, hdW, _, hfar⟩ := hW_deriv_all t (lt_of_lt_of_le hτ_big (by linarith))
              rw [hdW.deriv]; exact (hfar ht2).2)
            hWT_bd h_ibp' hT_lim (fun _ _ ha hab => hexp_tail_int ha hab)
        have hK0_inv : ‖(mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹‖ ≤ 5 * Real.exp (1 / 6) := by
          have hlb := (mellinK0_imag_bounds hc1 L1 τ).1
          have h1τ : 1 + τ ^ 2 ≤ 5 := by nlinarith
          have hcp_lb : (5 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h1τ (by norm_num)
          have h5_lb : (1 / 5 : ℝ) ≤ (5 : ℝ) ^ (-(1 / 4 : ℝ)) := by
            rw [Real.rpow_neg (by norm_num), one_div]
            refine inv_anti₀ (by positivity) ?_
            calc (5 : ℝ) ^ (1 / 4 : ℝ) ≤ (5 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 5 := Real.rpow_one _
          have htot : (1 / 5 : ℝ) * Real.exp (-(1 / 6)) ≤ ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖ := by
            have hm0 : (1 / 5 : ℝ) * Real.exp (-(1 / 6)) ≤
                Real.exp (-(1 / 6)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
              have hle := h5_lb.trans hcp_lb
              have := (Real.exp_pos (-(1 / 6))).le
              nlinarith
            exact hm0.trans hlb
          rw [norm_inv]
          calc ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖⁻¹
              ≤ ((1 / 5 : ℝ) * Real.exp (-(1 / 6)))⁻¹ := inv_anti₀ (by positivity) htot
            _ = 5 * Real.exp (1 / 6) := by rw [mul_inv, Real.exp_neg, inv_inv]; ring
        have hPsi_eq : c * ‖fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)‖ =
            ‖(mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹‖ *
              (c * ‖Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖) := by
          rw [fctPsi_eq_integral_of_ne_zero K4 ε c L1 α hτpos.ne', norm_mul, norm_mul, Complex.norm_I, one_mul]
          ring
        have hHG_inv := (hHG_near τ hτpos hτ2).2.2
        have htau_pow : τ ^ (-(5 / 2 : ℝ)) * τ ^ (5 / 2 : ℝ) = 1 := by
          rw [← Real.rpow_add hτpos, neg_add_cancel, Real.rpow_zero]
        unfold fctPhiC
        rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le,
          ← mul_assoc, hPsi_eq]
        calc ‖(mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹‖ *
              (c * ‖Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖) *
              ‖(fctDcompAt K4 c α ((τ : ℂ) * Complex.I))⁻¹‖ * ‖(ctHG ε ((τ : ℂ) * Complex.I))⁻¹‖
            ≤ ((5 * Real.exp (1 / 6)) * ((C_W_n0 + (2 / 5) * C_W_n1 + 8 * I_tail) * τ ^ (-(5 / 2 : ℝ)))) *
                Real.exp (B_D 0) * (Cinv * τ ^ (5 / 2 : ℝ)) := by
              have h12 : ‖(mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹‖ *
                  (c * ‖Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖) ≤
                  (5 * Real.exp (1 / 6)) * ((C_W_n0 + (2 / 5) * C_W_n1 + 8 * I_tail) * τ ^ (-(5 / 2 : ℝ))) :=
                mul_le_mul hK0_inv h_lim_bd (by positivity) (by positivity)
              have h123 := mul_le_mul h12 (hD_inv_ub τ) (norm_nonneg _) (by positivity)
              exact mul_le_mul h123 hHG_inv (norm_nonneg _) (by positivity)
          _ = (5 * Real.exp (1 / 6)) * Real.exp (B_D 0) * Cinv *
                (C_W_n0 + (2 / 5) * C_W_n1 + 8 * I_tail) * (τ ^ (-(5 / 2 : ℝ)) * τ ^ (5 / 2 : ℝ)) := by ring
          _ = M_mid_W := by rw [htau_pow, mul_one]
          _ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
      · -- Subcase B2: `2 < τ`
        have h_lim_bd : c * ‖Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖ ≤
            (C_W_f0 + C_W_f1 * (1 / π + 1 / π ^ 2)) *
              ((1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + τ) * Real.exp (-(π * τ))) := by
          refine edge_subcase_B2 h2τ (by positivity) hW_cont_τ
            (fun t ht => by
              obtain ⟨dW, hdW, _, hfar⟩ := hW_deriv_all t (lt_of_lt_of_le hτ_big ht)
              rw [hdW.deriv]; exact hfar (by linarith))
            hWT_bd h_ibp' hT_lim (fun _ _ ha hab => hexp_tail_int ha hab)
        have hK0_inv : ‖(mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹‖ ≤
            (1 + τ ^ 2) ^ (1 / 4 : ℝ) * Real.exp (1 / 6) := by
          have hlb := (mellinK0_imag_bounds hc1 L1 τ).1
          rw [norm_inv]
          calc ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖⁻¹
              ≤ (Real.exp (-(1 / 6)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)))⁻¹ := inv_anti₀ (by positivity) hlb
            _ = (1 + τ ^ 2) ^ (1 / 4 : ℝ) * Real.exp (1 / 6) := by
                rw [mul_inv, Real.rpow_neg (by positivity), inv_inv, Real.exp_neg, inv_inv, mul_comm]
        have hHG_lb : cHG * (1 + τ) * Real.exp (-(π * τ)) ≤ ‖ctHG ε ((τ : ℂ) * Complex.I)‖ := by
          have him : 1 ≤ |((τ : ℂ) * Complex.I).im| := by simp [abs_of_pos hτpos]; linarith
          have h0 := (hHG_left ε ((τ : ℂ) * Complex.I) ⟨by simp, by simp⟩ (by simp; norm_num) him).1
          simpa [abs_of_pos hτpos] using h0
        have hHG_inv : ‖(ctHG ε ((τ : ℂ) * Complex.I))⁻¹‖ ≤
            (cHG * (1 + τ) * Real.exp (-(π * τ)))⁻¹ := by
          rw [norm_inv]
          exact inv_anti₀ (by positivity) hHG_lb
        have hPsi_eq : c * ‖fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)‖ =
            ‖(mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹‖ *
              (c * ‖Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖) := by
          rw [fctPsi_eq_integral_of_ne_zero K4 ε c L1 α hτpos.ne', norm_mul, norm_mul, Complex.norm_I, one_mul]
          ring
        have hpow0 : (1 + τ ^ 2) ^ (1 / 4 : ℝ) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) = 1 := by
          rw [← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero]
        have h1τe_pos : 0 < (1 + τ) * Real.exp (-(π * τ)) := by positivity
        unfold fctPhiC
        rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le,
          ← mul_assoc, hPsi_eq]
        calc ‖(mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹‖ *
              (c * ‖Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖) *
              ‖(fctDcompAt K4 c α ((τ : ℂ) * Complex.I))⁻¹‖ * ‖(ctHG ε ((τ : ℂ) * Complex.I))⁻¹‖
            ≤ (((1 + τ ^ 2) ^ (1 / 4 : ℝ) * Real.exp (1 / 6)) *
                ((C_W_f0 + C_W_f1 * (1 / π + 1 / π ^ 2)) *
                  ((1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + τ) * Real.exp (-(π * τ))))) *
                Real.exp (B_D 0) * (cHG * (1 + τ) * Real.exp (-(π * τ)))⁻¹ := by
              have h12 : ‖(mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹‖ *
                  (c * ‖Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)‖) ≤
                  ((1 + τ ^ 2) ^ (1 / 4 : ℝ) * Real.exp (1 / 6)) *
                    ((C_W_f0 + C_W_f1 * (1 / π + 1 / π ^ 2)) *
                      ((1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + τ) * Real.exp (-(π * τ)))) :=
                mul_le_mul hK0_inv h_lim_bd (by positivity) (by positivity)
              have h123 := mul_le_mul h12 (hD_inv_ub τ) (norm_nonneg _) (by positivity)
              exact mul_le_mul h123 hHG_inv (norm_nonneg _) (by positivity)
          _ = Real.exp (1 / 6) * Real.exp (B_D 0) / cHG * (C_W_f0 + C_W_f1 * (1 / π + 1 / π ^ 2)) *
                ((1 + τ ^ 2) ^ (1 / 4 : ℝ) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) *
                (((1 + τ) * Real.exp (-(π * τ))) / ((1 + τ) * Real.exp (-(π * τ)))) := by
              field_simp [hcHG.ne', h1τe_pos.ne']
          _ = M_far_W := by rw [hpow0, div_self h1τe_pos.ne', mul_one, mul_one]
          _ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  rcases lt_trichotomy τ 0 with hτneg | rfl | hτpos
  · have hconj : fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I) =
        starRingEnd ℂ (fctPhiC K4 ε c L1 α (((-τ : ℝ) : ℂ) * Complex.I)) := by
      have hst : (τ : ℂ) * Complex.I = starRingEnd ℂ (((-τ : ℝ) : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp
      have h0 : 0 ≤ (((-τ : ℝ) : ℂ) * Complex.I).re := by simp
      have h1 : (((-τ : ℝ) : ℂ) * Complex.I).re < 1 := by simp
      have hS : ((-τ : ℝ) : ℂ) * Complex.I ∈ closedStrip := ⟨h0, by linarith⟩
      rw [hst]
      unfold fctPhiC
      rw [fctPsi_conj hD_conj h0 h1, hD_conj _ hS, ctHG_conj ε hS]
      simp only [map_div₀, map_mul, Complex.conj_ofReal]
    rw [hconj, RCLike.norm_conj]
    exact hpos_bd (-τ) (neg_pos.mpr hτneg)
  · simp [fctPhiC_zero]
    exact le_trans (by positivity) (le_max_left _ _)
  · exact hpos_bd τ hτpos

/-- info: 'FormalResearch.SignUncertainty.fctPhiC_left_edge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiC_left_edge_bound

end FormalResearch.SignUncertainty
