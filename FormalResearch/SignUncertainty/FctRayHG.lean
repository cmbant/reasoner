/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctRayTanLower
public import FormalResearch.SignUncertainty.FctSplittingHol
public import FormalResearch.SignUncertainty.FctWarpAdmiss

/-!
# Two-sided interior-strip bounds for `H_*/G_ε` (`fct:splitting` (1))

Paper I (`constant_terms_five.tex`), Lemma FCT.6 (`fct:splitting`), proof steps (b), (d), and
left-strip `|Φ_c| ≤ C`.

* `ctHG_band_two_sided`: uniform two-sided bounds `c_HG (1 + |Im t|) e^{-π|Im t|} ≤ ‖ctHG ε t‖ ≤ C_HG (1 + |Im t|) e^{-π|Im t|}`
  on `{t ∈ closedStrip | 1/4 ≤ t.re ≤ 15/32}` and on `{t ∈ closedStrip | 0 ≤ t.re ≤ 15/32, 1 ≤ |t.im|}`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

private lemma real_cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

private lemma real_sinh_ge_quarter_exp {x : ℝ} (hx : 1 / 2 ≤ x) : (1 / 4 : ℝ) * Real.exp x ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-x) ≤ (1 / 2 : ℝ) * Real.exp x := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : (2 : ℝ) ≤ Real.exp (2 * x) := he.trans (Real.exp_le_exp.mpr (by linarith))
    have hmul : Real.exp (-x) * Real.exp (2 * x) = Real.exp x := by rw [← Real.exp_add]; congr 1; ring
    have hex : 0 < Real.exp (2 * x) := Real.exp_pos _
    calc Real.exp (-x) = Real.exp (-x) * 1 := (mul_one _).symm
      _ ≤ Real.exp (-x) * ((1 / 2) * Real.exp (2 * x)) := by gcongr; linarith
      _ = (1 / 2) * (Real.exp (-x) * Real.exp (2 * x)) := by ring
      _ = (1 / 2) * Real.exp x := by rw [hmul]
  linarith

private lemma sinh_sq_abs (x : ℝ) : Real.sinh |x| ^ 2 = Real.sinh x ^ 2 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, Real.sinh_neg, neg_sq]

private lemma fctRay_norm_seedA_le (ε : ℝ) (t : ℂ) : ‖seedA ε t‖ ≤ 2 * Real.exp (π * |t.im|) := by
  unfold seedA
  split_ifs with hε
  · have hcos_sq : ‖Complex.cos (bArg t)‖ ^ 2 ≤ Real.cosh (-(π * t.im / 2)) ^ 2 := by
      have hb : bArg t = ((bArg t).re : ℂ) + ((bArg t).im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [hb, norm_sq_complex_cos, bArg_im]
      have := Real.cosh_sq_sub_sinh_sq (-(π * t.im / 2))
      have := Real.cos_sq_le_one (bArg t).re
      linarith
    have hle : ‖Complex.cos (bArg t)‖ ≤ Real.exp (π * |t.im| / 2) := by
      have h1 : ‖Complex.cos (bArg t)‖ ≤ Real.cosh (-(π * t.im / 2)) :=
        le_of_sq_le_sq hcos_sq (Real.cosh_pos _).le
      have h2 := real_cosh_le_exp_abs (-(π * t.im / 2))
      have hab : |-(π * t.im / 2)| = π * |t.im| / 2 := by
        rw [abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact h1.trans (hab ▸ h2)
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have hsq : ‖Complex.cos (bArg t)‖ ^ 2 ≤ Real.exp (π * |t.im|) := by
      calc ‖Complex.cos (bArg t)‖ ^ 2 ≤ (Real.exp (π * |t.im| / 2)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ = Real.exp (π * |t.im|) := by rw [← Real.exp_nat_mul]; congr 1; ring
    linarith
  · have hcos_sq : ‖Complex.cos ((π : ℂ) * t)‖ ^ 2 ≤ Real.cosh (π * t.im) ^ 2 := by
      have hpt : (π : ℂ) * t = ((π * t.re : ℝ) : ℂ) + ((π * t.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [hpt, norm_sq_complex_cos]
      have := Real.cosh_sq_sub_sinh_sq (π * t.im)
      have := Real.cos_sq_le_one (π * t.re)
      linarith
    have h1 : ‖Complex.cos ((π : ℂ) * t)‖ ≤ Real.cosh (π * t.im) :=
      le_of_sq_le_sq hcos_sq (Real.cosh_pos _).le
    have h2 : Real.cosh (π * t.im) ≤ Real.exp (π * |t.im|) := by
      simpa [abs_mul, abs_of_pos Real.pi_pos] using real_cosh_le_exp_abs (π * t.im)
    exact (h1.trans h2).trans (le_mul_of_one_le_left (Real.exp_pos _).le (by norm_num))

private lemma fctRay_norm_seedA_ge : ∃ cA : ℝ, 0 < cA ∧ ∀ ε : ℝ, ∀ t : ℂ, 0 ≤ t.re → t.re ≤ 15 / 32 →
    cA * Real.exp (π * |t.im|) ≤ ‖seedA ε t‖ := by
  set c_cos : ℝ := Real.cos (15 * π / 32)
  have hc_cos : 0 < c_cos := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  refine ⟨min (min (1 / 8) (Real.exp (-1))) (c_cos * Real.exp (-1)), by positivity, fun ε t h0 h1 => ?_⟩
  unfold seedA
  split_ifs with hε
  · have hbr0 : 0 ≤ (bArg t).re := by rw [bArg_re]; nlinarith [Real.pi_pos]
    have hbr1 : (bArg t).re ≤ π / 4 := by rw [bArg_re]; nlinarith [Real.pi_pos]
    have hcos_ge : 1 / 2 ≤ Real.cos (bArg t).re ^ 2 := by
      have hcos_mono : Real.cos (π / 4) ≤ Real.cos (bArg t).re :=
        Real.strictAntiOn_cos.antitoneOn ⟨hbr0, by nlinarith [Real.pi_pos]⟩
          ⟨by positivity, by nlinarith [Real.pi_pos]⟩ hbr1
      rw [Real.cos_pi_div_four] at hcos_mono
      have hsq := pow_le_pow_left₀ (by positivity) hcos_mono 2
      have hsq2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      linarith
    have hsq_eq : ‖Complex.cos (bArg t)‖ ^ 2 = Real.cos (bArg t).re ^ 2 + Real.sinh (π * |t.im| / 2) ^ 2 := by
      have hb : bArg t = ((bArg t).re : ℂ) + ((-(π * t.im / 2) : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [bArg_im]
      have hab : π * |t.im| / 2 = |-(π * t.im / 2)| := by
        rw [abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [hb, norm_sq_complex_cos, hab, sinh_sq_abs]
      simp
    rw [norm_mul, Complex.norm_ofNat, norm_pow, hsq_eq]
    by_cases him : 1 / 2 ≤ π * |t.im| / 2
    · have hsh := real_sinh_ge_quarter_exp him
      have h2 : (1 / 16 : ℝ) * Real.exp (π * |t.im|) ≤ Real.sinh (π * |t.im| / 2) ^ 2 := by
        calc (1 / 16 : ℝ) * Real.exp (π * |t.im|) = ((1 / 4) * Real.exp (π * |t.im| / 2)) ^ 2 := by
              rw [mul_pow, ← Real.exp_nat_mul]; norm_num; ring
          _ ≤ Real.sinh (π * |t.im| / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hsh 2
      have hcA : min (min (1 / 8) (Real.exp (-1))) (c_cos * Real.exp (-1)) ≤ 1 / 8 :=
        (min_le_left _ _).trans (min_le_left _ _)
      calc min (min (1 / 8) (Real.exp (-1))) (c_cos * Real.exp (-1)) * Real.exp (π * |t.im|)
          ≤ (1 / 8) * Real.exp (π * |t.im|) := by gcongr
        _ ≤ 2 * (Real.cos (bArg t).re ^ 2 + Real.sinh (π * |t.im| / 2) ^ 2) := by
            linarith [sq_nonneg (Real.cos (bArg t).re)]
    · push Not at him
      have hexp : Real.exp (-1) * Real.exp (π * |t.im|) ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff]; linarith
      have hcA : min (min (1 / 8) (Real.exp (-1))) (c_cos * Real.exp (-1)) ≤ Real.exp (-1) :=
        (min_le_left _ _).trans (min_le_right _ _)
      calc min (min (1 / 8) (Real.exp (-1))) (c_cos * Real.exp (-1)) * Real.exp (π * |t.im|)
          ≤ Real.exp (-1) * Real.exp (π * |t.im|) := by gcongr
        _ ≤ 1 := hexp
        _ ≤ 2 * (Real.cos (bArg t).re ^ 2 + Real.sinh (π * |t.im| / 2) ^ 2) := by
            linarith [sq_nonneg (Real.sinh (π * |t.im| / 2))]
  · have hpt : (π : ℂ) * t = ((π * t.re : ℝ) : ℂ) + ((π * t.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have hsq_eq : ‖Complex.cos ((π : ℂ) * t)‖ ^ 2 = Real.cos (π * t.re) ^ 2 + Real.sinh (π * |t.im|) ^ 2 := by
      rw [hpt, norm_sq_complex_cos, show π * |t.im| = |π * t.im| by rw [abs_mul, abs_of_pos Real.pi_pos],
        sinh_sq_abs]
    have hcos_re : c_cos ≤ Real.cos (π * t.re) :=
      Real.strictAntiOn_cos.antitoneOn ⟨by positivity, by nlinarith [Real.pi_pos]⟩
        ⟨by positivity, by nlinarith [Real.pi_pos]⟩ (by nlinarith [Real.pi_pos])
    by_cases him : 1 / 2 ≤ π * |t.im|
    · have hsh := real_sinh_ge_quarter_exp him
      have hsh_le : Real.sinh (π * |t.im|) ≤ ‖Complex.cos ((π : ℂ) * t)‖ := by
        refine le_of_sq_le_sq ?_ (norm_nonneg _)
        rw [hsq_eq]; linarith [sq_nonneg (Real.cos (π * t.re))]
      have hcA : min (min (1 / 8) (Real.exp (-1))) (c_cos * Real.exp (-1)) ≤ 1 / 4 :=
        ((min_le_left _ _).trans (min_le_left _ _)).trans (by norm_num)
      calc min (min (1 / 8) (Real.exp (-1))) (c_cos * Real.exp (-1)) * Real.exp (π * |t.im|)
          ≤ (1 / 4) * Real.exp (π * |t.im|) := by gcongr
        _ ≤ Real.sinh (π * |t.im|) := hsh
        _ ≤ ‖Complex.cos ((π : ℂ) * t)‖ := hsh_le
    · push Not at him
      have hcos_le : Real.cos (π * t.re) ≤ ‖Complex.cos ((π : ℂ) * t)‖ := by
        refine le_of_sq_le_sq ?_ (norm_nonneg _)
        rw [hsq_eq]; linarith [sq_nonneg (Real.sinh (π * |t.im|))]
      have hexp : Real.exp (-1) * Real.exp (π * |t.im|) ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff]; linarith
      have hcA : min (min (1 / 8) (Real.exp (-1))) (c_cos * Real.exp (-1)) ≤ c_cos * Real.exp (-1) :=
        min_le_right _ _
      calc min (min (1 / 8) (Real.exp (-1))) (c_cos * Real.exp (-1)) * Real.exp (π * |t.im|)
          ≤ (c_cos * Real.exp (-1)) * Real.exp (π * |t.im|) := by gcongr
        _ = c_cos * (Real.exp (-1) * Real.exp (π * |t.im|)) := by ring
        _ ≤ c_cos * 1 := mul_le_mul_of_nonneg_left hexp hc_cos.le
        _ = c_cos := mul_one _
        _ ≤ Real.cos (π * t.re) := hcos_re
        _ ≤ ‖Complex.cos ((π : ℂ) * t)‖ := hcos_le

private lemma norm_sin_pi_le (t : ℂ) : ‖Complex.sin ((π : ℂ) * t)‖ ≤ Real.exp (π * |t.im|) := by
  have hpt : (π : ℂ) * t = ((π * t.re : ℝ) : ℂ) + ((π * t.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hsq : ‖Complex.sin ((π : ℂ) * t)‖ ^ 2 ≤ Real.cosh (π * t.im) ^ 2 := by
    rw [hpt, norm_sq_complex_sin]
    have := Real.cosh_sq_sub_sinh_sq (π * t.im)
    have := Real.sin_sq_le_one (π * t.re)
    linarith
  have h1 := le_of_sq_le_sq hsq (Real.cosh_pos _).le
  have h2 : Real.cosh (π * t.im) ≤ Real.exp (π * |t.im|) := by
    simpa [abs_mul, abs_of_pos Real.pi_pos] using real_cosh_le_exp_abs (π * t.im)
  exact h1.trans h2

private lemma norm_sin_pi_ge_of_band {t : ℂ} (h0 : 1 / 4 ≤ t.re) (h1 : t.re ≤ 15 / 32) :
    (1 / 4 : ℝ) * Real.exp (-1) * Real.exp (π * |t.im|) ≤ ‖Complex.sin ((π : ℂ) * t)‖ := by
  have hpt : (π : ℂ) * t = ((π * t.re : ℝ) : ℂ) + ((π * t.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hsq_eq : ‖Complex.sin ((π : ℂ) * t)‖ ^ 2 = Real.sin (π * t.re) ^ 2 + Real.sinh (π * |t.im|) ^ 2 := by
    rw [hpt, norm_sq_complex_sin, show π * |t.im| = |π * t.im| by rw [abs_mul, abs_of_pos Real.pi_pos],
      sinh_sq_abs]
  by_cases him : 1 / 2 ≤ π * |t.im|
  · have hsh := real_sinh_ge_quarter_exp him
    have hsh_le : Real.sinh (π * |t.im|) ≤ ‖Complex.sin ((π : ℂ) * t)‖ := by
      refine le_of_sq_le_sq ?_ (norm_nonneg _)
      rw [hsq_eq]; linarith [sq_nonneg (Real.sin (π * t.re))]
    have hexp : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
    calc (1 / 4 : ℝ) * Real.exp (-1) * Real.exp (π * |t.im|)
        ≤ (1 / 4) * 1 * Real.exp (π * |t.im|) := by gcongr
      _ = (1 / 4) * Real.exp (π * |t.im|) := by ring
      _ ≤ Real.sinh (π * |t.im|) := hsh
      _ ≤ ‖Complex.sin ((π : ℂ) * t)‖ := hsh_le
  · push Not at him
    have hsin_mono : Real.sin (π / 4) ≤ Real.sin (π * t.re) :=
      Real.strictMonoOn_sin.monotoneOn ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
        ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ (by nlinarith [Real.pi_pos])
    rw [Real.sin_pi_div_four] at hsin_mono
    have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt_of_sq_le (by norm_num)).trans_eq rfl
    have hsin_le : Real.sin (π * t.re) ≤ ‖Complex.sin ((π : ℂ) * t)‖ := by
      refine le_of_sq_le_sq ?_ (norm_nonneg _)
      rw [hsq_eq]; linarith [sq_nonneg (Real.sinh (π * |t.im|))]
    have hexp : Real.exp (-1) * Real.exp (π * |t.im|) ≤ 1 := by
      rw [← Real.exp_add, Real.exp_le_one_iff]; linarith
    calc (1 / 4 : ℝ) * Real.exp (-1) * Real.exp (π * |t.im|)
        ≤ (1 / 2) * (Real.exp (-1) * Real.exp (π * |t.im|)) := by nlinarith [Real.exp_pos (-1), Real.exp_pos (π * |t.im|)]
      _ ≤ 1 / 2 := by nlinarith
      _ ≤ Real.sqrt 2 / 2 := by linarith
      _ ≤ Real.sin (π * t.re) := hsin_mono
      _ ≤ ‖Complex.sin ((π : ℂ) * t)‖ := hsin_le

/-- **Two-sided `ctHG ε` bound** (`fct:splitting` (1)) on `{t ∈ closedStrip | 1/4 ≤ t.re ≤ 15/32}`
and on `{t ∈ closedStrip | 0 ≤ t.re ≤ 15/32, 1 ≤ |t.im|}`. -/
theorem ctHG_band_two_sided :
    ∃ cHG CHG : ℝ, 0 < cHG ∧ 0 < CHG ∧
      (∀ ε : ℝ, ∀ t : ℂ, t ∈ closedStrip → 1 / 4 ≤ t.re → t.re ≤ 15 / 32 →
        cHG * (1 + |t.im|) * Real.exp (-(π * |t.im|)) ≤ ‖ctHG ε t‖ ∧
          ‖ctHG ε t‖ ≤ CHG * (1 + |t.im|) * Real.exp (-(π * |t.im|))) ∧
      (∀ ε : ℝ, ∀ t : ℂ, t ∈ closedStrip → t.re ≤ 15 / 32 → 1 ≤ |t.im| →
        cHG * (1 + |t.im|) * Real.exp (-(π * |t.im|)) ≤ ‖ctHG ε t‖ ∧
          ‖ctHG ε t‖ ≤ CHG * (1 + |t.im|) * Real.exp (-(π * |t.im|))) := by
  obtain ⟨cA, hcA, hA_ge⟩ := fctRay_norm_seedA_ge
  obtain ⟨Cge, hCge⟩ := re_outerHbar_ge
  obtain ⟨Cbd, hCbd⟩ := re_outerHbar_bound
  set exp_hi : ℝ := Real.exp Cge
  set exp_lo : ℝ := Real.exp (-Cbd)
  have hexphi : 0 < exp_hi := Real.exp_pos _
  have hexplo : 0 < exp_lo := Real.exp_pos _
  have hnorm_bounds : ∀ t : ℂ, 0 ≤ t.re → t.re ≤ 15 / 32 →
      ‖t‖ ≤ 1 + |t.im| ∧ ‖1 - t‖ ≤ 1 + |t.im| := fun t h0 h1 => by
    have h1n : ‖t‖ ≤ 1 + |t.im| :=
      (Complex.norm_le_abs_re_add_abs_im t).trans (by rw [abs_of_nonneg h0]; linarith)
    have h2n : ‖1 - t‖ ≤ 1 + |t.im| := by
      have hsub := Complex.norm_le_abs_re_add_abs_im (1 - t)
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hsub
      rw [abs_of_nonneg (by linarith)] at hsub
      linarith
    exact ⟨h1n, h2n⟩
  have hexpH_bounds : ∀ t : ℂ, t ∈ closedStrip →
      exp_lo * (1 + |t.im|) ^ 2 ≤ ‖Complex.exp (-outerHbar t)‖ ∧
        ‖Complex.exp (-outerHbar t)‖ ≤ exp_hi * (1 + |t.im|) ^ 2 := fun t ht => by
    rw [Complex.norm_exp, Complex.neg_re]
    have hg := hCge t ht
    have hb := hCbd t ht
    have h1y : 0 < 1 + |t.im| := by linarith [abs_nonneg t.im]
    have hpow : Real.exp (2 * Real.log (1 + |t.im|)) = (1 + |t.im|) ^ 2 := by
      rw [mul_comm, Real.exp_mul, Real.exp_log h1y]; norm_cast
    constructor
    · calc exp_lo * (1 + |t.im|) ^ 2 = Real.exp (2 * Real.log (1 + |t.im|) - Cbd) := by
            rw [Real.exp_sub, hpow]; simp only [exp_lo, Real.exp_neg]; ring
        _ ≤ Real.exp (-(outerHbar t).re) := Real.exp_le_exp.mpr (by linarith)
    · calc Real.exp (-(outerHbar t).re) ≤ Real.exp (2 * Real.log (1 + |t.im|) + Cge) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = exp_hi * (1 + |t.im|) ^ 2 := by rw [Real.exp_add, hpow]; ring
  set s_band : ℝ := (1 / 4 : ℝ) * Real.exp (-1)
  have hs_band : 0 < s_band := by positivity
  set CHG_val : ℝ := 2 * π ^ 2 * exp_hi / (min s_band (1 / 4)) ^ 2 / ((1 / 8 : ℝ) ^ (5 / 2 : ℝ) * (1 / 4 : ℝ) ^ (5 / 2 : ℝ))
  set cHG_val : ℝ := cA * π ^ 2 * exp_lo * ((1 / 8 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ 2)
  refine ⟨cHG_val, CHG_val, by positivity, by positivity, ?_, ?_⟩
  · intro ε t ht h0 h1
    have h0' : 0 ≤ t.re := by linarith
    have ht_ne : t ≠ 0 := fun h => by rw [h] at h0; simp at h0; norm_num at h0
    have h1t_ne : 1 - t ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have ht_lb : (1 / 8 : ℝ) * (1 + |t.im|) ≤ ‖t‖ := by
      have hre : 1 / 4 ≤ ‖t‖ := h0.trans ((le_abs_self _).trans (Complex.abs_re_le_norm t))
      have him : |t.im| ≤ ‖t‖ := Complex.abs_im_le_norm t
      linarith
    have h1t_lb : (1 / 4 : ℝ) * (1 + |t.im|) ≤ ‖1 - t‖ := by
      have hre : (1 / 2 : ℝ) ≤ ‖1 - t‖ := by
        have := (le_abs_self (1 - t).re).trans (Complex.abs_re_le_norm (1 - t))
        simp only [Complex.sub_re, Complex.one_re] at this; linarith
      have him : |t.im| ≤ ‖1 - t‖ := by simpa using Complex.abs_im_le_norm (1 - t)
      linarith
    obtain ⟨ht_ub, h1t_ub⟩ := hnorm_bounds t h0' h1
    obtain ⟨helo, hehi⟩ := hexpH_bounds t ht
    have hsin_lb : min s_band (1 / 4) * Real.exp (π * |t.im|) ≤ ‖Complex.sin ((π : ℂ) * t)‖ := by
      have h1' := norm_sin_pi_ge_of_band h0 h1
      have hm : min s_band (1 / 4) ≤ s_band := min_le_left _ _
      exact (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le).trans h1'
    have hsin_ub := norm_sin_pi_le t
    have hsin_ne : Complex.sin ((π : ℂ) * t) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hsin_lb)
    have hZ_eq : uctSeedZ ε t = seedA ε t * ((π : ℂ) * t * (1 - t) / Complex.sin ((π : ℂ) * t)) ^ 2 := by
      rw [uctSeedZ_of_le (by linarith), seedZL_eq_of_sin hsin_ne]
    rw [ctHG_norm_eq ε ht_ne h1t_ne, norm_mul, hZ_eq, norm_mul, norm_pow, norm_div, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h1y : 0 < 1 + |t.im| := by linarith [abs_nonneg t.im]
    have hexp_pos : 0 < Real.exp (π * |t.im|) := Real.exp_pos _
    have hexp_neg : Real.exp (-(π * |t.im|)) = (Real.exp (π * |t.im|))⁻¹ := Real.exp_neg _
    have hpow_split : (1 + |t.im|) ^ (5 / 2 : ℝ) * (1 + |t.im|) ^ (5 / 2 : ℝ) = (1 + |t.im|) ^ 5 := by
      rw [← Real.rpow_add h1y, ← Real.rpow_natCast]; congr 1; norm_num
    constructor
    · have hA := hA_ge ε t h0' h1
      have hZ_lb : cA * π ^ 2 * ((1 / 8 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ 2) * (1 + |t.im|) ^ 4 * Real.exp (-(π * |t.im|)) ≤
          ‖seedA ε t‖ * (π * ‖t‖ * ‖1 - t‖ / ‖Complex.sin ((π : ℂ) * t)‖) ^ 2 := by
        have hrat_lb : π * ((1 / 8 : ℝ) * (1 + |t.im|)) * ((1 / 4 : ℝ) * (1 + |t.im|)) / Real.exp (π * |t.im|) ≤
            π * ‖t‖ * ‖1 - t‖ / ‖Complex.sin ((π : ℂ) * t)‖ :=
          div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul_of_nonneg_left ht_lb Real.pi_pos.le)
            h1t_lb (by positivity) (by positivity)) (norm_pos_iff.mpr hsin_ne) hsin_ub
        have hrat_sq := pow_le_pow_left₀ (by positivity) hrat_lb 2
        have hmul := mul_le_mul hA hrat_sq (by positivity) (by positivity)
        have he2 : Real.exp (π * |t.im|) * (Real.exp (π * |t.im|))⁻¹ ^ 2 = Real.exp (-(π * |t.im|)) := by
          rw [hexp_neg]; field_simp [hexp_pos.ne']
        have heq : cA * π ^ 2 * ((1 / 8 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ 2) * (1 + |t.im|) ^ 4 * Real.exp (-(π * |t.im|)) =
            (cA * Real.exp (π * |t.im|)) *
              (π * ((1 / 8 : ℝ) * (1 + |t.im|)) * ((1 / 4 : ℝ) * (1 + |t.im|)) / Real.exp (π * |t.im|)) ^ 2 := by
          rw [← he2]; field_simp [hexp_pos.ne']
        exact heq.le.trans hmul
      have hnum_lb : cHG_val * (1 + |t.im|) ^ 6 * Real.exp (-(π * |t.im|)) ≤
          ‖seedA ε t‖ * (π * ‖t‖ * ‖1 - t‖ / ‖Complex.sin ((π : ℂ) * t)‖) ^ 2 * ‖Complex.exp (-outerHbar t)‖ := by
        have hmul := mul_le_mul hZ_lb helo (by positivity) (by positivity)
        refine le_trans ?_ hmul
        simp only [cHG_val]; ring_nf; exact le_rfl
      have hden_ub : ‖t‖ ^ (5 / 2 : ℝ) * ‖1 - t‖ ^ (5 / 2 : ℝ) ≤ (1 + |t.im|) ^ 5 :=
        (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) ht_ub (by norm_num))
          (Real.rpow_le_rpow (norm_nonneg _) h1t_ub (by norm_num)) (by positivity) (by positivity)).trans_eq hpow_split
      rw [le_div_iff₀ (by positivity)]
      calc cHG_val * (1 + |t.im|) * Real.exp (-(π * |t.im|)) * (‖t‖ ^ (5 / 2 : ℝ) * ‖1 - t‖ ^ (5 / 2 : ℝ))
          ≤ cHG_val * (1 + |t.im|) * Real.exp (-(π * |t.im|)) * (1 + |t.im|) ^ 5 := by gcongr
        _ = cHG_val * (1 + |t.im|) ^ 6 * Real.exp (-(π * |t.im|)) := by ring
        _ ≤ _ := hnum_lb
    · have hA := fctRay_norm_seedA_le ε t
      have hZ_ub : ‖seedA ε t‖ * (π * ‖t‖ * ‖1 - t‖ / ‖Complex.sin ((π : ℂ) * t)‖) ^ 2 ≤
          (2 * π ^ 2 / (min s_band (1 / 4)) ^ 2) * (1 + |t.im|) ^ 4 * Real.exp (-(π * |t.im|)) := by
        have hrat_ub : π * ‖t‖ * ‖1 - t‖ / ‖Complex.sin ((π : ℂ) * t)‖ ≤
            π * (1 + |t.im|) * (1 + |t.im|) / (min s_band (1 / 4) * Real.exp (π * |t.im|)) :=
          div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul_of_nonneg_left ht_ub Real.pi_pos.le)
            h1t_ub (norm_nonneg _) (by positivity)) (by positivity) hsin_lb
        have hrat_sq := pow_le_pow_left₀ (by positivity) hrat_ub 2
        refine (mul_le_mul hA hrat_sq (by positivity) (by positivity)).trans ?_
        have hmpos : 0 < min s_band (1 / 4) := by positivity
        rw [hexp_neg]
        field_simp [hexp_pos.ne', hmpos.ne']
        ring_nf; exact le_rfl
      have hden_lb : (1 / 8 : ℝ) ^ (5 / 2 : ℝ) * (1 / 4 : ℝ) ^ (5 / 2 : ℝ) * (1 + |t.im|) ^ 5 ≤
          ‖t‖ ^ (5 / 2 : ℝ) * ‖1 - t‖ ^ (5 / 2 : ℝ) := by
        calc (1 / 8 : ℝ) ^ (5 / 2 : ℝ) * (1 / 4 : ℝ) ^ (5 / 2 : ℝ) * (1 + |t.im|) ^ 5
            = ((1 / 8 : ℝ) * (1 + |t.im|)) ^ (5 / 2 : ℝ) * ((1 / 4 : ℝ) * (1 + |t.im|)) ^ (5 / 2 : ℝ) := by
              rw [Real.mul_rpow (by positivity) h1y.le, Real.mul_rpow (by positivity) h1y.le, ← hpow_split]; ring
          _ ≤ ‖t‖ ^ (5 / 2 : ℝ) * ‖1 - t‖ ^ (5 / 2 : ℝ) :=
              mul_le_mul (Real.rpow_le_rpow (by positivity) ht_lb (by norm_num))
                (Real.rpow_le_rpow (by positivity) h1t_lb (by norm_num)) (by positivity) (by positivity)
      rw [div_le_iff₀ (by positivity)]
      have hnum_ub := mul_le_mul hZ_ub hehi (by positivity) (by positivity)
      refine hnum_ub.trans ?_
      have hconst_pos : 0 < (1 / 8 : ℝ) ^ (5 / 2 : ℝ) * (1 / 4 : ℝ) ^ (5 / 2 : ℝ) := by positivity
      calc (2 * π ^ 2 / min s_band (1 / 4) ^ 2) * (1 + |t.im|) ^ 4 * Real.exp (-(π * |t.im|)) *
            (exp_hi * (1 + |t.im|) ^ 2)
          = (CHG_val * (1 + |t.im|) * Real.exp (-(π * |t.im|))) *
              ((1 / 8 : ℝ) ^ (5 / 2 : ℝ) * (1 / 4 : ℝ) ^ (5 / 2 : ℝ) * (1 + |t.im|) ^ 5) := by
            simp only [CHG_val]; field_simp [hconst_pos.ne']
        _ ≤ _ := by gcongr
  · intro ε t ht h1 him
    have h0' : 0 ≤ t.re := ht.1
    have ht_lb : (1 / 2 : ℝ) * (1 + |t.im|) ≤ ‖t‖ := by
      have h : |t.im| ≤ ‖t‖ := Complex.abs_im_le_norm t
      linarith
    have h1t_lb : (1 / 2 : ℝ) * (1 + |t.im|) ≤ ‖1 - t‖ := by
      have h : |t.im| ≤ ‖1 - t‖ := by simpa using Complex.abs_im_le_norm (1 - t)
      linarith
    have ht_ne : t ≠ 0 := norm_pos_iff.mp (by linarith)
    have h1t_ne : 1 - t ≠ 0 := norm_pos_iff.mp (by linarith)
    obtain ⟨ht_ub, h1t_ub⟩ := hnorm_bounds t h0' h1
    obtain ⟨helo, hehi⟩ := hexpH_bounds t ht
    have hsin_lb : min s_band (1 / 4) * Real.exp (π * |t.im|) ≤ ‖Complex.sin ((π : ℂ) * t)‖ := by
      have hpt : (π : ℂ) * t = ((π * t.re : ℝ) : ℂ) + ((π * t.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      have hsq_eq : ‖Complex.sin ((π : ℂ) * t)‖ ^ 2 = Real.sin (π * t.re) ^ 2 + Real.sinh (π * |t.im|) ^ 2 := by
        rw [hpt, norm_sq_complex_sin, show π * |t.im| = |π * t.im| by rw [abs_mul, abs_of_pos Real.pi_pos],
          sinh_sq_abs]
      have hsh := real_sinh_ge_quarter_exp (by nlinarith [Real.pi_gt_three] : 1 / 2 ≤ π * |t.im|)
      have hsh_le : Real.sinh (π * |t.im|) ≤ ‖Complex.sin ((π : ℂ) * t)‖ := by
        refine le_of_sq_le_sq ?_ (norm_nonneg _)
        rw [hsq_eq]; linarith [sq_nonneg (Real.sin (π * t.re))]
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le).trans (hsh.trans hsh_le)
    have hsin_ub := norm_sin_pi_le t
    have hsin_ne : Complex.sin ((π : ℂ) * t) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hsin_lb)
    have hZ_eq : uctSeedZ ε t = seedA ε t * ((π : ℂ) * t * (1 - t) / Complex.sin ((π : ℂ) * t)) ^ 2 := by
      rw [uctSeedZ_of_le (by linarith), seedZL_eq_of_sin hsin_ne]
    rw [ctHG_norm_eq ε ht_ne h1t_ne, norm_mul, hZ_eq, norm_mul, norm_pow, norm_div, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h1y : 0 < 1 + |t.im| := by linarith [abs_nonneg t.im]
    have hexp_pos : 0 < Real.exp (π * |t.im|) := Real.exp_pos _
    have hexp_neg : Real.exp (-(π * |t.im|)) = (Real.exp (π * |t.im|))⁻¹ := Real.exp_neg _
    have hpow_split : (1 + |t.im|) ^ (5 / 2 : ℝ) * (1 + |t.im|) ^ (5 / 2 : ℝ) = (1 + |t.im|) ^ 5 := by
      rw [← Real.rpow_add h1y, ← Real.rpow_natCast]; congr 1; norm_num
    constructor
    · have hA := hA_ge ε t h0' h1
      have hZ_lb : cA * π ^ 2 * ((1 / 8 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ 2) * (1 + |t.im|) ^ 4 * Real.exp (-(π * |t.im|)) ≤
          ‖seedA ε t‖ * (π * ‖t‖ * ‖1 - t‖ / ‖Complex.sin ((π : ℂ) * t)‖) ^ 2 := by
        have hrat_lb : π * ((1 / 8 : ℝ) * (1 + |t.im|)) * ((1 / 4 : ℝ) * (1 + |t.im|)) / Real.exp (π * |t.im|) ≤
            π * ‖t‖ * ‖1 - t‖ / ‖Complex.sin ((π : ℂ) * t)‖ :=
          div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le)
            (by linarith) (by positivity) (by positivity)) (norm_pos_iff.mpr hsin_ne) hsin_ub
        have hrat_sq := pow_le_pow_left₀ (by positivity) hrat_lb 2
        have hmul := mul_le_mul hA hrat_sq (by positivity) (by positivity)
        have he2 : Real.exp (π * |t.im|) * (Real.exp (π * |t.im|))⁻¹ ^ 2 = Real.exp (-(π * |t.im|)) := by
          rw [hexp_neg]; field_simp [hexp_pos.ne']
        have heq : cA * π ^ 2 * ((1 / 8 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ 2) * (1 + |t.im|) ^ 4 * Real.exp (-(π * |t.im|)) =
            (cA * Real.exp (π * |t.im|)) *
              (π * ((1 / 8 : ℝ) * (1 + |t.im|)) * ((1 / 4 : ℝ) * (1 + |t.im|)) / Real.exp (π * |t.im|)) ^ 2 := by
          rw [← he2]; field_simp [hexp_pos.ne']
        exact heq.le.trans hmul
      have hnum_lb := mul_le_mul hZ_lb helo (by positivity) (by positivity)
      have hden_ub : ‖t‖ ^ (5 / 2 : ℝ) * ‖1 - t‖ ^ (5 / 2 : ℝ) ≤ (1 + |t.im|) ^ 5 :=
        (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) ht_ub (by norm_num))
          (Real.rpow_le_rpow (norm_nonneg _) h1t_ub (by norm_num)) (by positivity) (by positivity)).trans_eq hpow_split
      rw [le_div_iff₀ (by positivity)]
      calc cHG_val * (1 + |t.im|) * Real.exp (-(π * |t.im|)) * (‖t‖ ^ (5 / 2 : ℝ) * ‖1 - t‖ ^ (5 / 2 : ℝ))
          ≤ cHG_val * (1 + |t.im|) * Real.exp (-(π * |t.im|)) * (1 + |t.im|) ^ 5 := by gcongr
        _ = cHG_val * (1 + |t.im|) ^ 6 * Real.exp (-(π * |t.im|)) := by ring
        _ ≤ _ := by refine le_trans ?_ hnum_lb; simp only [cHG_val]; ring_nf; exact le_rfl
    · have hA := fctRay_norm_seedA_le ε t
      have hZ_ub : ‖seedA ε t‖ * (π * ‖t‖ * ‖1 - t‖ / ‖Complex.sin ((π : ℂ) * t)‖) ^ 2 ≤
          (2 * π ^ 2 / (min s_band (1 / 4)) ^ 2) * (1 + |t.im|) ^ 4 * Real.exp (-(π * |t.im|)) := by
        have hrat_sq := pow_le_pow_left₀ (by positivity)
          (div_le_div₀ (by positivity) (mul_le_mul (mul_le_mul_of_nonneg_left ht_ub Real.pi_pos.le)
            h1t_ub (norm_nonneg _) (by positivity)) (by positivity) hsin_lb) 2
        refine (mul_le_mul hA hrat_sq (by positivity) (by positivity)).trans ?_
        have hmpos : 0 < min s_band (1 / 4) := by positivity
        rw [hexp_neg]; field_simp [hexp_pos.ne', hmpos.ne']; ring_nf; exact le_rfl
      have hden_lb : (1 / 8 : ℝ) ^ (5 / 2 : ℝ) * (1 / 4 : ℝ) ^ (5 / 2 : ℝ) * (1 + |t.im|) ^ 5 ≤
          ‖t‖ ^ (5 / 2 : ℝ) * ‖1 - t‖ ^ (5 / 2 : ℝ) := by
        have hle1 : (1 / 8 : ℝ) ^ (5 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
        have hle2 : (1 / 4 : ℝ) ^ (5 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
        calc (1 / 8 : ℝ) ^ (5 / 2 : ℝ) * (1 / 4 : ℝ) ^ (5 / 2 : ℝ) * (1 + |t.im|) ^ 5
            = (1 / 8 : ℝ) ^ (5 / 2 : ℝ) * (1 / 4 : ℝ) ^ (5 / 2 : ℝ) *
                ((1 + |t.im|) ^ (5 / 2 : ℝ) * (1 + |t.im|) ^ (5 / 2 : ℝ)) := by rw [hpow_split]
          _ ≤ (1 / 2 : ℝ) ^ (5 / 2 : ℝ) * (1 / 2 : ℝ) ^ (5 / 2 : ℝ) *
                ((1 + |t.im|) ^ (5 / 2 : ℝ) * (1 + |t.im|) ^ (5 / 2 : ℝ)) := by gcongr
          _ = ((1 / 2 : ℝ) * (1 + |t.im|)) ^ (5 / 2 : ℝ) * ((1 / 2 : ℝ) * (1 + |t.im|)) ^ (5 / 2 : ℝ) := by
              rw [Real.mul_rpow (by positivity) h1y.le]; ring
          _ ≤ ‖t‖ ^ (5 / 2 : ℝ) * ‖1 - t‖ ^ (5 / 2 : ℝ) :=
              mul_le_mul (Real.rpow_le_rpow (by positivity) ht_lb (by norm_num))
                (Real.rpow_le_rpow (by positivity) h1t_lb (by norm_num)) (by positivity) (by positivity)
      rw [div_le_iff₀ (by positivity)]
      have hnum_ub := mul_le_mul hZ_ub hehi (by positivity) (by positivity)
      refine hnum_ub.trans ?_
      have hconst_pos : 0 < (1 / 8 : ℝ) ^ (5 / 2 : ℝ) * (1 / 4 : ℝ) ^ (5 / 2 : ℝ) := by positivity
      calc (2 * π ^ 2 / min s_band (1 / 4) ^ 2) * (1 + |t.im|) ^ 4 * Real.exp (-(π * |t.im|)) *
            (exp_hi * (1 + |t.im|) ^ 2)
          = (CHG_val * (1 + |t.im|) * Real.exp (-(π * |t.im|))) *
              ((1 / 8 : ℝ) ^ (5 / 2 : ℝ) * (1 / 4 : ℝ) ^ (5 / 2 : ℝ) * (1 + |t.im|) ^ 5) := by
            simp only [CHG_val]; field_simp [hconst_pos.ne']
        _ ≤ _ := by gcongr

/-- info: 'FormalResearch.SignUncertainty.ctHG_band_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctHG_band_two_sided

end FormalResearch.SignUncertainty
