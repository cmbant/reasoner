module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasCoordInv

/-!
# Quantitative vertical geometry of `zetaRight` on `lowerBoasRightDom`

This leaf module proves the two-sided vertical comparison for the conformal phase coordinate
`zetaRight c' b`:

* `zetaRight_im_abs_le`: `|Im(zetaRight c' b)| ≤ (2 c' / 3) * |Im b| * (1 + Re b)`.
* `zetaRight_im_abs_ge`: `(c' / 6000) * |Im b| * √(‖b - ξ_*‖ * (1 + Re b)) ≤ |Im(zetaRight c' b)|`.
-/

@[expose] public section

open Real Complex Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen

noncomputable section

private lemma exp_two_pi_le_600 : Real.exp (2 * π) ≤ 600 := by
  have hpi4 := Real.pi_lt_d4
  have h1 : 2 * π ≤ 6.3 := by linarith
  have h2 : Real.exp (2 * π) ≤ Real.exp 6.3 := Real.exp_le_exp.mpr h1
  have h3 : Real.exp 6.3 = Real.exp 1 ^ 6 * Real.exp 0.3 := by
    rw [show (6.3 : ℝ) = (6 : ℕ) * 1 + 0.3 by norm_num, Real.exp_add, Real.exp_nat_mul]
  have he1 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have hp6 : Real.exp 1 ^ 6 ≤ 2.72 ^ 6 := pow_le_pow_left₀ (Real.exp_pos 1).le he1 6
  have he03 : Real.exp 0.3 ≤ 10 / 7 := by
    have := Real.add_one_le_exp (-0.3 : ℝ)
    have hmul : Real.exp 0.3 * Real.exp (-0.3) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (0.3 : ℝ), Real.exp_pos (-0.3 : ℝ)]
  have hpow_num : (2.72 : ℝ) ^ 6 ≤ 405 := by norm_num
  have hprod : Real.exp 1 ^ 6 * Real.exp 0.3 ≤ 405 * (10 / 7) :=
    mul_le_mul (hp6.trans hpow_num) he03 (Real.exp_pos _).le (by norm_num)
  linarith

private lemma sinh_complexArsinh {w : ℂ} (hw : w ∈ arsinhDomain) :
    Complex.sinh (complexArsinh w) = w := by
  unfold complexArsinh
  set s : ℂ := (w ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hdom : w + s ∈ slitPlane := arsinhDomain_add_sqrt_mem_slitPlane hw
  have hne : w + s ≠ 0 := slitPlane_ne_zero hdom
  have hw0 : w ^ 2 + 1 ≠ 0 := slitPlane_ne_zero hw
  have hs_sq : s ^ 2 = w ^ 2 + 1 := by
    dsimp [s]
    rw [pow_two, Complex.cpow_def_of_ne_zero hw0, ← Complex.exp_add]
    have hadd : Complex.log (w ^ 2 + 1) * (1 / 2 : ℂ) + Complex.log (w ^ 2 + 1) * (1 / 2 : ℂ) =
        Complex.log (w ^ 2 + 1) := by ring
    rw [hadd, Complex.exp_log hw0]
  have hprod : (w + s) * (s - w) = 1 := by linear_combination hs_sq
  have hinv : (w + s)⁻¹ = s - w := inv_eq_of_mul_eq_one_right hprod
  rw [Complex.sinh, Complex.exp_log hne, Complex.exp_neg, Complex.exp_log hne, hinv]
  ring

private lemma sinh_pi_mul_pMap {b : ℂ} (hb : b ∈ slitStrip) :
    Complex.sinh ((π : ℂ) * pMap b) = -Complex.I * Complex.sinh ((π : ℂ) * b) := by
  unfold pMap
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  rw [show (π : ℂ) * ((π : ℂ)⁻¹ * complexArsinh (-Complex.I * Complex.sinh ((π : ℂ) * b))) =
      complexArsinh (-Complex.I * Complex.sinh ((π : ℂ) * b)) by field_simp [hpi]]
  exact sinh_complexArsinh (mem_arsinhDomain_of_slitStrip hb)

private lemma sinh_pi_pMap_re_sq_lower {x t : ℝ} (hx : xiStar < x) (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    (Real.sinh (π * x) ^ 2 - 1 + Real.sin (π * t) ^ 2 +
        Real.cosh (π * x) * Real.sin (π * t)) / 2 ≤
      Real.sinh (π * (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re) ^ 2 := by
  set b : ℂ := (x : ℂ) + (t : ℂ) * Complex.I
  have hb_re : b.re = x := by simp [b]
  have hb_im : b.im = t := by simp [b]
  have hb_mem : b ∈ slitStrip :=
    mem_slitStrip_of_im_ne_zero (by rw [hb_im, abs_of_pos ht0]; exact ht1) (by rw [hb_im]; exact ht0.ne')
  set p := pMap b
  set α := p.re
  set β := p.im
  have hsin_eq : Complex.sinh ((π : ℂ) * p) = -Complex.I * Complex.sinh ((π : ℂ) * b) :=
    sinh_pi_mul_pMap hb_mem
  have hpi_re : ((π : ℂ) * p).re = π * α := by simp [α]
  have hpi_im : ((π : ℂ) * p).im = π * β := by simp [β]
  have hsplit_p : (π : ℂ) * p = ((π * α : ℝ) : ℂ) + ((π * β : ℝ) : ℂ) * Complex.I :=
    Complex.ext (by simp [hpi_re]) (by simp [hpi_im])
  have hsinh_exp : Complex.sinh ((π : ℂ) * p) =
      ((Real.sinh (π * α) * Real.cos (π * β) : ℝ) : ℂ) +
        ((Real.cosh (π * α) * Real.sin (π * β) : ℝ) : ℂ) * Complex.I := by
    rw [hsplit_p, Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
    apply Complex.ext <;> simp <;> ring
  have hL_re : (Complex.sinh ((π : ℂ) * p)).re = Real.sinh (π * α) * Real.cos (π * β) := by
    rw [hsinh_exp]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero]
  have hL_im : (Complex.sinh ((π : ℂ) * p)).im = Real.cosh (π * α) * Real.sin (π * β) := by
    rw [hsinh_exp]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero, zero_add]
  obtain ⟨hR_re, hR_im⟩ := neg_I_mul_sinh_pi_re_im b
  rw [hb_re, hb_im] at hR_re hR_im
  have hre_id : Real.sinh (π * α) * Real.cos (π * β) = Real.cosh (π * x) * Real.sin (π * t) := by
    rw [← hL_re, hsin_eq, hR_re]
  have him_id : Real.cosh (π * α) * Real.sin (π * β) = -(Real.sinh (π * x) * Real.cos (π * t)) := by
    rw [← hL_im, hsin_eq, hR_im]
  set S : ℝ := Real.sinh (π * α) ^ 2
  set A : ℝ := Real.cosh (π * x) * Real.sin (π * t)
  set B : ℝ := -(Real.sinh (π * x) * Real.cos (π * t))
  set D : ℝ := Real.sinh (π * x) ^ 2 - 1 + Real.sin (π * t) ^ 2
  have hS_nn : 0 ≤ S := sq_nonneg _
  have hcosh_α : Real.cosh (π * α) ^ 2 = 1 + S := by
    dsimp [S]; linarith [Real.cosh_sq_sub_sinh_sq (π * α)]
  have hcosh_x : Real.cosh (π * x) ^ 2 = 1 + Real.sinh (π * x) ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq (π * x)]
  have hcos_β : Real.cos (π * β) ^ 2 = 1 - Real.sin (π * β) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (π * β)]
  have hcos_t : Real.cos (π * t) ^ 2 = 1 - Real.sin (π * t) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (π * t)]
  have h1 : S * (1 - Real.sin (π * β) ^ 2) = A ^ 2 := by
    have hsq := congrArg (· ^ 2) hre_id
    rw [mul_pow, hcos_β] at hsq
    exact hsq
  have h2 : (1 + S) * Real.sin (π * β) ^ 2 = B ^ 2 := by
    have hsq := congrArg (· ^ 2) him_id
    rw [mul_pow, hcosh_α] at hsq
    exact hsq
  have hAB : A ^ 2 + B ^ 2 = Real.sinh (π * x) ^ 2 + Real.sin (π * t) ^ 2 := by
    dsimp [A, B]
    rw [mul_pow, hcosh_x, neg_sq, mul_pow, hcos_t]
    ring
  have hpoly : S ^ 2 - D * S - A ^ 2 = 0 := by
    have h1' : S - A ^ 2 = S * Real.sin (π * β) ^ 2 := by linarith only [h1]
    have hmul : (1 + S) * (S - A ^ 2) = S * B ^ 2 := by
      calc (1 + S) * (S - A ^ 2) = (1 + S) * (S * Real.sin (π * β) ^ 2) := by rw [h1']
        _ = S * ((1 + S) * Real.sin (π * β) ^ 2) := by ring
        _ = S * B ^ 2 := by rw [h2]
    have hD_eq : D = A ^ 2 + B ^ 2 - 1 := by rw [hAB]; dsimp [D]; ring
    rw [hD_eq]
    linarith only [hmul]
  have hD_pos : 0 < D := by
    have hpi := Real.pi_pos
    have hsh : 1 < Real.sinh (π * x) := by
      rw [← sinh_pi_mul_xiStar]
      exact Real.sinh_strictMono (mul_lt_mul_of_pos_left hx hpi)
    have hs1 : 1 < Real.sinh (π * x) ^ 2 := by nlinarith only [hsh]
    have hsin2 : 0 ≤ Real.sin (π * t) ^ 2 := sq_nonneg _
    dsimp [D]; linarith only [hs1, hsin2]
  have hA_pos : 0 < A := by
    have hpi := Real.pi_pos
    exact mul_pos (Real.cosh_pos _) (Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi ht0) (by nlinarith))
  have hS_pos : 0 < S := by
    by_contra h0
    have hS0 : S = 0 := le_antisymm (not_lt.mp h0) hS_nn
    rw [hS0] at hpoly
    nlinarith only [sq_pos_of_pos hA_pos, hpoly]
  have hS_ge_D : D ≤ S := by
    have hDS : D * S ≤ S * S := by linarith only [sq_pos_of_pos hA_pos, hpoly]
    exact le_of_mul_le_mul_right hDS hS_pos
  have hS_ge_A : A ≤ S := by
    have hSS : A ^ 2 ≤ S ^ 2 := by nlinarith only [hD_pos, hS_nn, hpoly]
    exact (abs_le_of_sq_le_sq' hSS hS_nn).2
  change (D + A) / 2 ≤ S
  linarith only [hS_ge_D, hS_ge_A]

lemma sin_pi_t_ge_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    2 * t ≤ Real.sin (π * t) := by
  have hpi := Real.pi_pos
  have h1 := Real.mul_le_sin (x := π * t) (mul_nonneg hpi.le ht0) (by nlinarith)
  have h2 : 2 / π * (π * t) = 2 * t := by field_simp [hpi.ne']
  linarith only [h1, h2]

private lemma sinh_pi_x_ge_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    (Real.exp (π * x) / 3) ^ 2 ≤ Real.sinh (π * x) ^ 2 - 1 := by
  have hpi := Real.pi_gt_three
  have hpx : 3 ≤ π * x := by nlinarith
  have hepx : Real.exp 3 ≤ Real.exp (π * x) := Real.exp_le_exp.mpr hpx
  have he3 : (20 : ℝ) ≤ Real.exp 3 := by
    have he1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    rw [hpow]
    have h1 : (2.718 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1 3
    norm_num at h1
    linarith
  have he_ge : 20 ≤ Real.exp (π * x) := he3.trans hepx
  have hinv_le : Real.exp (-(π * x)) ≤ 1 / 20 := by
    rw [Real.exp_neg]
    exact inv_le_of_inv_le₀ (by positivity) (by norm_num; exact he_ge)
  have hsh : Real.exp (π * x) * (2 / 5 : ℝ) ≤ Real.sinh (π * x) := by
    rw [Real.sinh_eq]
    linarith
  have hsh_ge8 : 8 ≤ Real.sinh (π * x) := by linarith
  have hsq : (Real.exp (π * x) / 3) ^ 2 + 1 ≤ (Real.exp (π * x) * (2 / 5 : ℝ)) ^ 2 := by
    nlinarith [he_ge]
  have hsh2 : (Real.exp (π * x) * (2 / 5 : ℝ)) ^ 2 ≤ Real.sinh (π * x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsh 2
  linarith

private lemma pMap_re_ge_of_one_le {x t : ℝ} (hx : 1 ≤ x) (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    (1 + x) / 4 ≤ (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re := by
  have hξ_lt : xiStar < 1 := xiStar_lt_one
  have hsh_lb := sinh_pi_pMap_re_sq_lower (hξ_lt.trans_le hx) ht0 ht1
  have hhb : (x : ℂ) + (t : ℂ) * Complex.I ∈ slitStrip :=
    mem_slitStrip_of_im_ne_zero (by simpa [abs_of_pos ht0] using ht1) (by simpa using ht0.ne')
  have hx_re : 0 < ((x : ℂ) + (t : ℂ) * Complex.I).re := by simp; linarith
  have ht_im : 0 < ((x : ℂ) + (t : ℂ) * Complex.I).im := by simp [ht0]
  have hp_pos : 0 < (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re :=
    (pMap_pos_re_neg_im hhb hx_re ht_im).1
  set α : ℝ := (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re
  have hsin_nn : 0 ≤ Real.cosh (π * x) * Real.sin (π * t) := by
    have hpi := Real.pi_pos
    exact mul_nonneg (Real.cosh_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith))
  have hsq_lb : (Real.exp (π * x) / 3) ^ 2 / 2 ≤ Real.sinh (π * α) ^ 2 := by
    have h1 := sinh_pi_x_ge_of_one_le hx
    have h2 : 0 ≤ Real.sin (π * t) ^ 2 := sq_nonneg _
    linarith
  have hrt : Real.exp (π * x) / (3 * √2) ≤ Real.sinh (π * α) := by
    have hpi := Real.pi_pos
    have hsh_nn : 0 ≤ Real.sinh (π * α) := Real.sinh_nonneg_iff.mpr (mul_nonneg hpi.le hp_pos.le)
    have hsq2 : (Real.exp (π * x) / (3 * √2)) ^ 2 = (Real.exp (π * x) / 3) ^ 2 / 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
    rw [← hsq2] at hsq_lb
    exact (abs_le_of_sq_le_sq' hsq_lb hsh_nn).2
  have hexp_α : Real.exp (π * x) * (2 / (3 * √2)) ≤ Real.exp (π * α) := by
    have h1 : Real.sinh (π * α) ≤ Real.exp (π * α) / 2 := by
      rw [Real.sinh_eq]
      have : 0 < Real.exp (-(π * α)) := Real.exp_pos _
      linarith
    have h2 : 2 * (Real.exp (π * x) / (3 * √2)) = Real.exp (π * x) * (2 / (3 * √2)) := by ring
    linarith
  have hlog : π * x + Real.log (2 / (3 * √2)) ≤ π * α := by
    have h1 : Real.log (Real.exp (π * x) * (2 / (3 * √2))) ≤ Real.log (Real.exp (π * α)) :=
      Real.log_le_log (by positivity) hexp_α
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_exp] at h1
    exact h1
  have hlog_ge : -(1 : ℝ) ≤ Real.log (2 / (3 * √2)) := by
    rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
    have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have hinv : Real.exp (-1) ≤ (2.7 : ℝ)⁻¹ := by
      rw [Real.exp_neg]; exact inv_anti₀ (by norm_num) (by linarith [Real.exp_one_gt_d9])
    have hrt2 : √2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hcmp : (2.7 : ℝ)⁻¹ ≤ 2 / (3 * √2) := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [hrt2]
    linarith
  have hpi := Real.pi_gt_three
  have : π * ((1 + x) / 4) ≤ π * α := by nlinarith [hlog, hlog_ge, hpi]
  exact le_of_mul_le_mul_left this Real.pi_pos

private lemma sinh_pi_le_of_le_two {u : ℝ} (hu0 : 0 ≤ u) (hu2 : u ≤ 2) :
    Real.sinh (π * u) ≤ 1000 * u := by
  let φ : ℝ → ℝ := fun s => 1000 * s - Real.sinh (π * s)
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d4
  have hmono : MonotoneOn φ (Icc 0 u) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
      ((continuous_const.mul continuous_id).sub (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).continuousOn
      (fun s _ => (((hasDerivAt_id s).const_mul 1000).sub
        (((Real.hasDerivAt_sinh _).comp s (by simpa using (hasDerivAt_id s).const_mul π)))).differentiableAt.differentiableWithinAt)
      fun s hs => ?_
    rw [interior_Icc] at hs
    have hd1 : HasDerivAt (fun r : ℝ => 1000 * r) 1000 s := by
      simpa using (hasDerivAt_id s).const_mul 1000
    have hd2 : HasDerivAt (fun r : ℝ => Real.sinh (π * r)) (Real.cosh (π * s) * π) s :=
      (Real.hasDerivAt_sinh _).comp s (by simpa using (hasDerivAt_id s).const_mul π)
    have hd : HasDerivAt φ (1000 - Real.cosh (π * s) * π) s := hd1.sub hd2
    rw [hd.deriv]
    have hch : Real.cosh (π * s) ≤ 301 := by
      have h1 : Real.cosh (π * s) ≤ Real.cosh (2 * π) := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg hpi.le hs.1.le),
          abs_of_nonneg (by positivity)]
        nlinarith [hs.2]
      have h2 : Real.cosh (2 * π) ≤ 301 := by
        rw [Real.cosh_eq]
        have hpos := exp_two_pi_le_600
        have hneg : Real.exp (-(2 * π)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      linarith
    nlinarith
  have h0 := hmono (left_mem_Icc.mpr hu0) (right_mem_Icc.mpr hu0) hu0
  dsimp [φ] at h0
  simp only [mul_zero, Real.sinh_zero, sub_zero] at h0
  linarith

private lemma pMap_re_ge_of_le_one {x t : ℝ} (hx : xiStar < x) (hx1 : x ≤ 1)
    (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    (1 / 1000 : ℝ) * Real.sqrt (x - xiStar + t) ≤ (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re := by
  have hsh_lb := sinh_pi_pMap_re_sq_lower hx ht0 ht1
  have hhb : (x : ℂ) + (t : ℂ) * Complex.I ∈ slitStrip :=
    mem_slitStrip_of_im_ne_zero (by simpa [abs_of_pos ht0] using ht1) (by simpa using ht0.ne')
  have hx_re : 0 < ((x : ℂ) + (t : ℂ) * Complex.I).re := by simp; linarith [xiStar_pos]
  have ht_im : 0 < ((x : ℂ) + (t : ℂ) * Complex.I).im := by simp [ht0]
  have hp_pos : 0 < (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re :=
    (pMap_pos_re_neg_im hhb hx_re ht_im).1
  set α : ℝ := (pMap ((x : ℂ) + (t : ℂ) * Complex.I)).re
  have hα_le : α ≤ 2 := by
    have hre := pMap_re_abs_le hhb
    have hbx : |((x : ℂ) + (t : ℂ) * Complex.I).re| = x := by
      simp [abs_of_pos (xiStar_pos.trans hx)]
    rw [hbx] at hre
    linarith [(abs_le.mp hre).2]
  have hsinh_mv : 2 * π * (x - xiStar) ≤ Real.sinh (π * x) ^ 2 - 1 := by
    have hdiff : π * (x - xiStar) ≤ Real.sinh (π * x) - Real.sinh (π * xiStar) := by
      let φ : ℝ → ℝ := fun s => Real.sinh (π * s) - π * s
      have hm : MonotoneOn φ (Icc xiStar x) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc xiStar x)
          ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).sub
            (continuous_const.mul continuous_id)).continuousOn
          (fun s _ => (((Real.hasDerivAt_sinh _).comp s (by simpa using (hasDerivAt_id s).const_mul π)).sub
            ((hasDerivAt_id s).const_mul π)).differentiableAt.differentiableWithinAt)
          fun s _ => ?_
        have hd1 : HasDerivAt (fun r : ℝ => Real.sinh (π * r)) (Real.cosh (π * s) * π) s :=
          (Real.hasDerivAt_sinh _).comp s (by simpa using (hasDerivAt_id s).const_mul π)
        have hd2 : HasDerivAt (fun r : ℝ => π * r) π s := by
          simpa using (hasDerivAt_id s).const_mul π
        have hd : HasDerivAt φ (Real.cosh (π * s) * π - π) s := hd1.sub hd2
        rw [hd.deriv]
        have hch : 1 ≤ Real.cosh (π * s) := Real.one_le_cosh _
        nlinarith [Real.pi_pos]
      have h0 := hm (left_mem_Icc.mpr hx.le) (right_mem_Icc.mpr hx.le) hx.le
      dsimp [φ] at h0; linarith
    rw [sinh_pi_mul_xiStar] at hdiff
    have hge1 : 1 ≤ Real.sinh (π * x) := by
      have : 0 ≤ π * (x - xiStar) := mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hx.le)
      linarith
    nlinarith [Real.pi_pos]
  have hsin_lb : 2 * t ≤ Real.cosh (π * x) * Real.sin (π * t) := by
    have h1 := sin_pi_t_ge_two_mul ht0.le ht1.le
    have h2 : 1 ≤ Real.cosh (π * x) := Real.one_le_cosh _
    have h3 : 0 ≤ Real.sin (π * t) := by linarith
    nlinarith
  have hcomb : x - xiStar + t ≤ Real.sinh (π * α) ^ 2 := by
    have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
    have hsin2 : 0 ≤ Real.sin (π * t) ^ 2 := sq_nonneg _
    nlinarith [hsh_lb, hsinh_mv, hsin_lb, hpi3]
  have hrt : Real.sqrt (x - xiStar + t) ≤ Real.sinh (π * α) := by
    have hpi := Real.pi_pos
    exact Real.sqrt_le_iff.mpr ⟨Real.sinh_nonneg_iff.mpr (mul_nonneg hpi.le hp_pos.le), hcomb⟩
  linarith [sinh_pi_le_of_le_two hp_pos.le hα_le]

private lemma hasDerivAt_zetaRight_vert_im {c' x s : ℝ}
    (hmem : (x : ℂ) + (s : ℂ) * Complex.I ∈ lowerBoasRightDom) :
    HasDerivAt (fun r : ℝ => (zetaRight c' ((x : ℂ) + (r : ℂ) * Complex.I)).im)
      (deriv (zetaRight c') ((x : ℂ) + (s : ℂ) * Complex.I)).re s := by
  have hline : HasDerivAt (fun r : ℝ => (x : ℂ) + (r : ℂ) * Complex.I) Complex.I s := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I).const_add (x : ℂ)
  have hdZ := ((hasDerivAt_zetaRight (c' := c') hmem).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hline
  refine (Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hdZ).congr_deriv ?_
  simp

private lemma continuousOn_zetaRight_vert_im {c' x a b : ℝ}
    (hmem : ∀ s ∈ Icc a b, (x : ℂ) + (s : ℂ) * Complex.I ∈ lowerBoasRightDom) :
    ContinuousOn (fun r : ℝ => (zetaRight c' ((x : ℂ) + (r : ℂ) * Complex.I)).im) (Icc a b) := by
  have hcontZ : ContinuousOn (zetaRight c') lowerBoasRightDom := (differentiableOn_zetaRight c').continuousOn
  have hcontL : Continuous (fun r : ℝ => (x : ℂ) + (r : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  exact Complex.continuous_im.comp_continuousOn
    (hcontZ.comp hcontL.continuousOn (fun r hr => hmem r hr))

/-- Upper bound `|Im(zetaRight c' b)| ≤ (2 c' / 3) * |Im b| * (1 + Re b)` on `lowerBoasRightDom`. -/
theorem zetaRight_im_abs_le {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : b ∈ lowerBoasRightDom) :
    |(zetaRight c' b).im| ≤ (2 * c' / 3) * |b.im| * (b.re + 1) := by
  suffices hpos : ∀ {w : ℂ}, w ∈ lowerBoasRightDom → 0 ≤ w.im →
      (zetaRight c' w).im ≤ (2 * c' / 3) * w.im * (w.re + 1) by
    rcases le_or_gt 0 b.im with him | him
    · have h1 : 0 ≤ (zetaRight c' b).im := by
        rcases him.eq_or_lt with h0 | hgt
        · have hbr : b = (b.re : ℂ) := Complex.ext rfl h0.symm
          rw [hbr, zetaRight_ofReal hb.1]; simp
        · exact (zetaRight_im_pos_of_im_pos hc' hb hgt).le
      rw [abs_of_nonneg h1, abs_of_nonneg him]
      exact hpos hb him
    · have hconj : starRingEnd ℂ b ∈ lowerBoasRightDom := conj_mem_lowerBoasRightDom hb
      have him_c : 0 ≤ (starRingEnd ℂ b).im := by simp; linarith
      have him_neg : (zetaRight c' b).im < 0 := by
        have hp := zetaRight_im_pos_of_im_pos hc' hconj (by simp; exact him)
        have hc := congrArg Complex.im (zetaRight_conj hb (c' := c'))
        simp only [Complex.conj_im] at hc
        linarith
      have h1 := hpos hconj him_c
      have hc := congrArg Complex.im (zetaRight_conj hb (c' := c'))
      simp only [Complex.conj_im, Complex.conj_re] at h1 hc
      rw [abs_of_neg him_neg, abs_of_neg him]
      linarith
  intro w hw hw_im
  let φ : ℝ → ℝ := fun s =>
    (2 * c' / 3) * (w.re + 1) * s - (zetaRight c' ((w.re : ℂ) + (s : ℂ) * Complex.I)).im
  have hmem : ∀ s ∈ Icc (0 : ℝ) w.im, (w.re : ℂ) + (s : ℂ) * Complex.I ∈ lowerBoasRightDom := by
    intro s hs
    exact ⟨by simpa using hw.1, by
      change |((w.re : ℂ) + (s : ℂ) * Complex.I).im| < 1 / 2
      have hlt : w.im < 1 / 2 := (abs_lt.mp hw.2).2
      simpa [abs_of_nonneg hs.1] using hs.2.trans_lt hlt⟩
  have hcont : ContinuousOn φ (Icc 0 w.im) :=
    (continuous_const.mul continuous_id).continuousOn.sub (continuousOn_zetaRight_vert_im hmem)
  have hmono : MonotoneOn φ (Icc 0 w.im) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 w.im) hcont ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      have hms := hmem s ⟨hs.1.le, hs.2.le⟩
      exact (((hasDerivAt_id s).const_mul ((2 * c' / 3) * (w.re + 1))).sub
        (hasDerivAt_zetaRight_vert_im (c' := c') hms)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hms := hmem s ⟨hs.1.le, hs.2.le⟩
      have hs_pos : 0 < ((w.re : ℂ) + (s : ℂ) * Complex.I).im := by simpa using hs.1
      have hbs : (w.re : ℂ) + (s : ℂ) * Complex.I ∈ slitStrip :=
        mem_slitStrip_of_im_ne_zero hms.2 hs_pos.ne'
      have hd_lin : HasDerivAt (fun r : ℝ => (2 * c' / 3) * (w.re + 1) * r)
          ((2 * c' / 3) * (w.re + 1)) s := by
        simpa using (hasDerivAt_id s).const_mul ((2 * c' / 3) * (w.re + 1))
      have hdφ : HasDerivAt φ ((2 * c' / 3) * (w.re + 1) -
          (deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re) s :=
        hd_lin.sub (hasDerivAt_zetaRight_vert_im (c' := c') hms)
      rw [hdφ.deriv]
      have hzeta_eq : zetaRight c' =ᶠ[𝓝 ((w.re : ℂ) + (s : ℂ) * Complex.I)] zetaPlus c' := by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hs_pos] with z hz
        unfold zetaRight
        rw [ite_eq_left hz]
      have hd_val : deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I) =
          ((2 * c' / 3 : ℝ) : ℂ) * (pMap ((w.re : ℂ) + (s : ℂ) * Complex.I) + Complex.I / 2) := by
        rw [hzeta_eq.deriv_eq, (hasDerivAt_zetaPlus hbs).deriv]
      have hre_val : (deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re =
          (2 * c' / 3) * (pMap ((w.re : ℂ) + (s : ℂ) * Complex.I)).re := by
        rw [hd_val]
        simp [Complex.mul_re, Complex.add_re]
      have hp_ub := (abs_le.mp (pMap_re_abs_le hbs)).2
      have hwx : |((w.re : ℂ) + (s : ℂ) * Complex.I).re| = w.re := by
        simp [abs_of_pos (xiStar_pos.trans hw.1)]
      rw [hwx] at hp_ub
      rw [hre_val]
      nlinarith [hc']
  have hres := hmono (left_mem_Icc.mpr hw_im) (right_mem_Icc.mpr hw_im) hw_im
  have hφ0 : φ 0 = 0 := by
    dsimp [φ]
    have h0 : (w.re : ℂ) + (0 : ℂ) * Complex.I = (w.re : ℂ) := by simp
    rw [h0, zetaRight_ofReal hw.1]; simp
  have hφw : (w.re : ℂ) + (w.im : ℂ) * Complex.I = w := Complex.ext (by simp) (by simp)
  dsimp [φ] at hres hφ0
  rw [hφw] at hres
  have h0_eq : (w.re : ℂ) + (0 : ℂ) * Complex.I = (w.re : ℂ) := by simp
  rw [h0_eq, zetaRight_ofReal hw.1] at hres
  simp only [mul_zero, Complex.ofReal_im, sub_self] at hres
  linarith

/-- Lower bound `(c' / 6000) * |Im b| * √(‖b - ξ_*‖ * (1 + Re b)) ≤ |Im(zetaRight c' b)|`
on `lowerBoasRightDom`. -/
theorem zetaRight_im_abs_ge {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : b ∈ lowerBoasRightDom) :
    (c' / 6000) * |b.im| * Real.sqrt (‖b - (xiStar : ℂ)‖ * (1 + b.re)) ≤ |(zetaRight c' b).im| := by
  suffices hpos : ∀ {w : ℂ}, w ∈ lowerBoasRightDom → 0 ≤ w.im →
      (c' / 6000) * w.im * Real.sqrt (‖w - (xiStar : ℂ)‖ * (1 + w.re)) ≤ (zetaRight c' w).im by
    rcases le_or_gt 0 b.im with him | him
    · have h1 : 0 ≤ (zetaRight c' b).im := by
        rcases him.eq_or_lt with h0 | hgt
        · have hbr : b = (b.re : ℂ) := Complex.ext rfl h0.symm
          rw [hbr, zetaRight_ofReal hb.1]; simp
        · exact (zetaRight_im_pos_of_im_pos hc' hb hgt).le
      rw [abs_of_nonneg h1, abs_of_nonneg him]
      exact hpos hb him
    · have hconj : starRingEnd ℂ b ∈ lowerBoasRightDom := conj_mem_lowerBoasRightDom hb
      have him_c : 0 ≤ (starRingEnd ℂ b).im := by simp; linarith
      have him_neg : (zetaRight c' b).im < 0 := by
        have hc := congrArg Complex.im (zetaRight_conj hb (c' := c'))
        simp only [Complex.conj_im] at hc
        linarith [zetaRight_im_pos_of_im_pos hc' hconj (by simp; exact him)]
      have h1 := hpos hconj him_c
      have hnorm : ‖starRingEnd ℂ b - (xiStar : ℂ)‖ = ‖b - (xiStar : ℂ)‖ := by
        rw [show starRingEnd ℂ b - (xiStar : ℂ) = starRingEnd ℂ (b - (xiStar : ℂ)) by
          rw [map_sub, Complex.conj_ofReal], Complex.norm_conj]
      have hc := congrArg Complex.im (zetaRight_conj hb (c' := c'))
      simp only [Complex.conj_im, Complex.conj_re] at h1 hc
      rw [hnorm] at h1
      rw [abs_of_neg him_neg, abs_of_neg him]
      linarith
  intro w hw hw_im
  rcases eq_or_lt_of_le hw_im with hw0 | hw_pos
  · have hwr : w = (w.re : ℂ) := Complex.ext rfl hw0.symm
    rw [hwr, zetaRight_ofReal hw.1]
    simp only [Complex.ofReal_im, mul_zero, zero_mul, le_refl]
  have hw_lt : w.im < 1 / 2 := (abs_lt.mp hw.2).2
  let k : ℝ := if 1 ≤ w.re then (1 + w.re) / 4 else (1 / 1000 : ℝ) * Real.sqrt (w.re - xiStar + w.im / 2)
  have hk_lb : ∀ s ∈ Ioo (w.im / 2) w.im,
      (2 * c' / 3) * k ≤ (deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re := by
    intro s hs
    have hs_pos : 0 < s := by linarith [hs.1]
    have hs_lt : s < 1 / 2 := hs.2.trans hw_lt
    have hbs : (w.re : ℂ) + (s : ℂ) * Complex.I ∈ slitStrip :=
      mem_slitStrip_of_im_ne_zero (by simpa [abs_of_pos hs_pos] using hs_lt) (by simpa using hs_pos.ne')
    have hzeta_eq : zetaRight c' =ᶠ[𝓝 ((w.re : ℂ) + (s : ℂ) * Complex.I)] zetaPlus c' := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simpa using hs_pos)] with z hz
      unfold zetaRight; rw [ite_eq_left hz]
    have hre_val : (deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re =
        (2 * c' / 3) * (pMap ((w.re : ℂ) + (s : ℂ) * Complex.I)).re := by
      rw [hzeta_eq.deriv_eq, (hasDerivAt_zetaPlus hbs).deriv]
      simp [Complex.mul_re, Complex.add_re]
    rw [hre_val]
    gcongr
    dsimp [k]
    split_ifs with hx1
    · exact pMap_re_ge_of_one_le hx1 hs_pos hs_lt
    · have hrt : Real.sqrt (w.re - xiStar + w.im / 2) ≤ Real.sqrt (w.re - xiStar + s) :=
        Real.sqrt_le_sqrt (by linarith [hs.1])
      exact (mul_le_mul_of_nonneg_left hrt (by positivity)).trans
        (pMap_re_ge_of_le_one hw.1 (not_le.mp hx1).le hs_pos hs_lt)
  let ψ : ℝ → ℝ := fun s =>
    (zetaRight c' ((w.re : ℂ) + (s : ℂ) * Complex.I)).im - (2 * c' / 3) * k * s
  have hmem : ∀ s ∈ Icc (w.im / 2) w.im, (w.re : ℂ) + (s : ℂ) * Complex.I ∈ lowerBoasRightDom :=
    fun s hs => ⟨by simpa using hw.1, by
      change |((w.re : ℂ) + (s : ℂ) * Complex.I).im| < 1 / 2
      have : 0 ≤ s := by linarith [hs.1]
      simpa [abs_of_nonneg this] using hs.2.trans_lt hw_lt⟩
  have hcont : ContinuousOn ψ (Icc (w.im / 2) w.im) :=
    (continuousOn_zetaRight_vert_im hmem).sub (continuous_const.mul continuous_id).continuousOn
  have hmono : MonotoneOn ψ (Icc (w.im / 2) w.im) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc (w.im / 2) w.im) hcont ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      have hms := hmem s ⟨hs.1.le, hs.2.le⟩
      exact ((hasDerivAt_zetaRight_vert_im hms).sub
        ((hasDerivAt_id s).const_mul ((2 * c' / 3) * k))).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hms := hmem s ⟨hs.1.le, hs.2.le⟩
      have hd_lin : HasDerivAt (fun r : ℝ => (2 * c' / 3) * k * r) ((2 * c' / 3) * k) s := by
        simpa using (hasDerivAt_id s).const_mul ((2 * c' / 3) * k)
      have hdψ : HasDerivAt ψ ((deriv (zetaRight c') ((w.re : ℂ) + (s : ℂ) * Complex.I)).re -
          (2 * c' / 3) * k) s :=
        (hasDerivAt_zetaRight_vert_im (c' := c') hms).sub hd_lin
      rw [hdψ.deriv]
      linarith [hk_lb s hs]
  have hstep := hmono (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith)) (by linarith)
  have hmid_mem : (w.re : ℂ) + ((w.im / 2 : ℝ) : ℂ) * Complex.I ∈ lowerBoasRightDom :=
    hmem (w.im / 2) ⟨le_rfl, by linarith⟩
  have hmid_pos : 0 < (zetaRight c' ((w.re : ℂ) + ((w.im / 2 : ℝ) : ℂ) * Complex.I)).im :=
    zetaRight_im_pos_of_im_pos hc' hmid_mem (by simpa using half_pos hw_pos)
  have hbw : (w.re : ℂ) + (w.im : ℂ) * Complex.I = w := Complex.ext (by simp) (by simp)
  have him_ge : (c' / 3) * k * w.im ≤ (zetaRight c' w).im := by
    dsimp [ψ] at hstep
    rw [hbw] at hstep
    linarith
  have hnorm_ub : Real.sqrt (‖w - (xiStar : ℂ)‖ * (1 + w.re)) ≤ 2000 * k := by
    have hnorm_le : ‖w - (xiStar : ℂ)‖ ≤ (w.re - xiStar) + w.im := by
      have hre : (w - (xiStar : ℂ)).re = w.re - xiStar := by simp
      have him : (w - (xiStar : ℂ)).im = w.im := by simp
      calc ‖w - (xiStar : ℂ)‖ ≤ |(w - (xiStar : ℂ)).re| + |(w - (xiStar : ℂ)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = (w.re - xiStar) + w.im := by
            rw [hre, him, abs_of_pos (sub_pos.mpr hw.1), abs_of_pos hw_pos]
    by_cases hx1 : 1 ≤ w.re
    · have hk_eq : k = (1 + w.re) / 4 := by simp only [k, hx1, ↓reduceIte]
      rw [hk_eq]
      have h1 : ‖w - (xiStar : ℂ)‖ ≤ 1 + w.re := by linarith [xiStar_pos, hw_lt]
      have h2 : ‖w - (xiStar : ℂ)‖ * (1 + w.re) ≤ (1 + w.re) ^ 2 := by
        nlinarith [norm_nonneg (w - (xiStar : ℂ))]
      calc Real.sqrt (‖w - (xiStar : ℂ)‖ * (1 + w.re)) ≤ Real.sqrt ((1 + w.re) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = 1 + w.re := Real.sqrt_sq (by linarith)
        _ ≤ 2000 * ((1 + w.re) / 4) := by linarith
    · have hk_eq : k = (1 / 1000 : ℝ) * Real.sqrt (w.re - xiStar + w.im / 2) := by
        simp only [k, hx1, ↓reduceIte]
      rw [hk_eq]
      have hx_lt : w.re < 1 := not_le.mp hx1
      have h2 : ‖w - (xiStar : ℂ)‖ * (1 + w.re) ≤ 4 * (w.re - xiStar + w.im / 2) := by
        have : ‖w - (xiStar : ℂ)‖ ≤ 2 * (w.re - xiStar + w.im / 2) := by linarith [hw.1]
        nlinarith [norm_nonneg (w - (xiStar : ℂ))]
      calc Real.sqrt (‖w - (xiStar : ℂ)‖ * (1 + w.re))
          ≤ Real.sqrt (4 * (w.re - xiStar + w.im / 2)) := Real.sqrt_le_sqrt h2
        _ = 2 * Real.sqrt (w.re - xiStar + w.im / 2) := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        _ ≤ 2000 * ((1 / 1000 : ℝ) * Real.sqrt (w.re - xiStar + w.im / 2)) := by ring_nf; rfl
  calc (c' / 6000) * w.im * Real.sqrt (‖w - (xiStar : ℂ)‖ * (1 + w.re))
      ≤ (c' / 6000) * w.im * (2000 * k) := by gcongr
    _ = (c' / 3) * k * w.im := by ring
    _ ≤ (zetaRight c' w).im := him_ge

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.zetaRight_im_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.zetaRight_im_abs_le

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.zetaRight_im_abs_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.zetaRight_im_abs_ge
