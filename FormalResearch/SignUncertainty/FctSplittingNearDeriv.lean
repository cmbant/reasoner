/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingPsiNear
public import FormalResearch.SignUncertainty.UctEnvHolo

/-!
# Left-edge derivative bounds near `0` (`(fct:Psi-edge)`, `left_near_deriv`)

Paper I (`constant_terms_five.tex`), `fct:splitting` (3), `(fct:Psi-edge)`: for `c ≥ c₀`, `ε = ±1`,
and `0 < |τ| ≤ 1`,
`‖∂_τ^j Φ̂_c(iτ)‖ ≤ M |τ|^{3-j}` for `j = 1, 2`.

Proof:
* `hol_cubic_imag_deriv`: any function `F` holomorphic on `{|Re ζ| < 3/8}` with `F(ζ) = O(‖ζ‖³)`
  near `0` and bounded on `{|Re ζ| ≤ 1/4, |Im ζ| ≤ 5/4}` has `‖∂_τ^j F(iτ)‖ ≤ M |τ|^{3-j}` (`j = 1, 2`)
  on `|τ| ≤ 1` (Cauchy estimates + mean value theorem along `iℝ`).
* Applied to `fctCauchy ... (7/16)` (`F_-`) and `fctQ1` (`q₁`) for `fctLeftTail`, combined with
  `FctSplittingPsiNear.fctPhiC_near_ejOn` on `(0, 1]` and reflected to `[-1, 0)` by `fctPhiHat_conj`.

Class: proved from `FctDescentStmt` (named input).
-/

@[expose] public section

open Set Filter Topology Metric MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

private lemma hol_cubic_imag_deriv {F : ℂ → ℂ} {M3 MB : ℝ}
    (hF : DifferentiableOn ℂ F {ζ : ℂ | |ζ.re| < 3 / 8})
    (hM3 : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 / 4 → ‖F ζ‖ ≤ M3 * ‖ζ‖ ^ 3)
    (hMB : ∀ ζ : ℂ, |ζ.re| ≤ 1 / 4 → |ζ.im| ≤ 5 / 4 → ‖F ζ‖ ≤ MB) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, |τ| ≤ 1 →
      ‖deriv (fun t : ℝ => F ((t : ℂ) * Complex.I)) τ‖ ≤ M * |τ| ^ 2 ∧
        ‖deriv (deriv (fun t : ℝ => F ((t : ℂ) * Complex.I))) τ‖ ≤ M * |τ| := by
  set U : Set ℂ := {ζ : ℂ | |ζ.re| < 3 / 8}
  have hUo : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hF1 : DifferentiableOn ℂ (deriv F) U := hF.deriv hUo
  have hF2 : DifferentiableOn ℂ (deriv (deriv F)) U := hF1.deriv hUo
  have hF_0 : F 0 = 0 := norm_le_zero_iff.mp (by simpa using hM3 0 (by norm_num))
  have hF1_0 : deriv F 0 = 0 := by
    by_contra hne
    have hpos : 0 < ‖deriv F 0‖ := norm_pos_iff.mpr hne
    set r : ℝ := min (1 / 4) (‖deriv F 0‖ / (2 * (|M3| + 1)))
    have hr : 0 < r := lt_min (by norm_num) (by positivity)
    have hball : closedBall (0 : ℂ) r ⊆ U := fun z hz => by
      have hz' : ‖z‖ ≤ r := by simpa [dist_eq_norm] using hz
      have := (Complex.abs_re_le_norm z).trans hz'
      have : r ≤ 1 / 4 := min_le_left _ _
      show |z.re| < 3 / 8; linarith
    have hc := (cauchy_deriv_two hr (hF.mono hball) fun z hz => by
      have hz' : ‖z‖ = r := by simpa [mem_sphere_zero_iff_norm] using hz
      have h1 := hM3 z (by rw [hz']; exact min_le_left _ _)
      rw [hz'] at h1; exact h1).1
    have hc' : ‖deriv F 0‖ ≤ M3 * r ^ 2 := by
      have : r ≠ 0 := hr.ne'
      calc ‖deriv F 0‖ ≤ M3 * r ^ 3 / r := hc
        _ = M3 * r ^ 2 := by field_simp
    have hr1 : r ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hc'' : ‖deriv F 0‖ ≤ (|M3| + 1) * r := by
      calc ‖deriv F 0‖ ≤ |M3| * r ^ 2 := hc'.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg r))
        _ ≤ (|M3| + 1) * (r * r) := by nlinarith [sq_nonneg r]
        _ ≤ (|M3| + 1) * (r * 1) := by gcongr
        _ = (|M3| + 1) * r := by ring
    have hc''' : ‖deriv F 0‖ ≤ ‖deriv F 0‖ / 2 :=
      hc''.trans (calc (|M3| + 1) * r ≤ (|M3| + 1) * (‖deriv F 0‖ / (2 * (|M3| + 1))) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
        _ = ‖deriv F 0‖ / 2 := by
            have hne1 : |M3| + 1 ≠ 0 := by positivity
            field_simp [hne1])
    linarith
  have hF2_0 : deriv (deriv F) 0 = 0 := by
    by_contra hne
    have hpos : 0 < ‖deriv (deriv F) 0‖ := norm_pos_iff.mpr hne
    set r : ℝ := min (1 / 8) (‖deriv (deriv F) 0‖ / (2 * (8 * |M3| + 1)))
    have hr : 0 < r := lt_min (by norm_num) (by positivity)
    have hsub1 : ∀ w : ℂ, ‖w‖ = r → closedBall w r ⊆ closedBall (0 : ℂ) (1 / 4) := fun w hw z hz => by
      have hz' : ‖z - w‖ ≤ r := by simpa [dist_eq_norm] using hz
      have hw' : r ≤ 1 / 8 := min_le_left _ _
      show dist z 0 ≤ 1 / 4
      rw [dist_zero_right]
      calc ‖z‖ = ‖(z - w) + w‖ := by congr 1; ring
        _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ r + r := add_le_add hz' hw.le
        _ ≤ 1 / 4 := by linarith
    have hc := (cauchy_deriv_two hr (hF1.mono fun w hw => by
      rw [mem_closedBall, dist_zero_right] at hw
      have := (Complex.abs_re_le_norm w).trans hw
      have : r ≤ 1 / 8 := min_le_left _ _
      show |w.re| < 3 / 8; linarith) fun w hw => by
      have hw' : ‖w‖ = r := mem_sphere_zero_iff_norm.mp hw
      have hwb : closedBall w r ⊆ U := fun z hz => by
        have hzb := hsub1 w hw' hz
        rw [mem_closedBall, dist_zero_right] at hzb
        show |z.re| < 3 / 8; linarith [Complex.abs_re_le_norm z]
      have hcw := (cauchy_deriv_two hr (hF.mono hwb) fun z hz => by
        have hzb := hsub1 w hw' (sphere_subset_closedBall hz)
        rw [mem_closedBall, dist_zero_right] at hzb
        have hz' : ‖z‖ ≤ 2 * r := by
          have hz1 : ‖z - w‖ = r := by simpa [dist_eq_norm] using hz
          calc ‖z‖ = ‖(z - w) + w‖ := by congr 1; ring
            _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
            _ = r + r := by rw [hz1, hw']
            _ = 2 * r := by ring
        have hm := hM3 z hzb
        have hM3nn : 0 ≤ |M3| := abs_nonneg _
        calc ‖F z‖ ≤ |M3| * ‖z‖ ^ 3 := hm.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
          _ ≤ |M3| * (2 * r) ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz' 3) hM3nn
          _ = 8 * |M3| * r ^ 3 := by ring).1
      calc ‖deriv F w‖ ≤ 8 * |M3| * r ^ 3 / r := hcw
        _ = 8 * |M3| * r ^ 2 := by have : r ≠ 0 := hr.ne'; field_simp).1
    have hc' : ‖deriv (deriv F) 0‖ ≤ 8 * |M3| * r := by
      have : r ≠ 0 := hr.ne'
      calc ‖deriv (deriv F) 0‖ ≤ 8 * |M3| * r ^ 2 / r := hc
        _ = 8 * |M3| * r := by field_simp
    have hc'' : ‖deriv (deriv F) 0‖ ≤ (8 * |M3| + 1) * r := by nlinarith [hr.le]
    have hc''' : ‖deriv (deriv F) 0‖ ≤ ‖deriv (deriv F) 0‖ / 2 :=
      hc''.trans (calc (8 * |M3| + 1) * r ≤ (8 * |M3| + 1) * (‖deriv (deriv F) 0‖ / (2 * (8 * |M3| + 1))) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
        _ = ‖deriv (deriv F) 0‖ / 2 := by
            have hne1 : 8 * |M3| + 1 ≠ 0 := by positivity
            field_simp [hne1])
    linarith
  have hMBnn : 0 ≤ MB := (norm_nonneg _).trans (hMB 0 (by norm_num) (by norm_num))
  have h1 : ∀ w : ℂ, |w.re| ≤ 1 / 8 → |w.im| ≤ 9 / 8 → ‖deriv F w‖ ≤ 8 * MB := fun w hwr hwi => by
    have hwb : closedBall w (1 / 8) ⊆ U := fun z hz => by
      have hz' : ‖z - w‖ ≤ 1 / 8 := by simpa [dist_eq_norm] using hz
      have hzr := (Complex.abs_re_le_norm (z - w)).trans hz'
      have : |z.re| ≤ |w.re| + |(z - w).re| := by
        simpa [sub_eq_add_neg] using abs_add_le w.re (z - w).re
      show |z.re| < 3 / 8; linarith
    have hc := (cauchy_deriv_two (by norm_num : (0 : ℝ) < 1 / 8) (hF.mono hwb) fun z hz => by
      have hz' : ‖z - w‖ = 1 / 8 := by simpa [dist_eq_norm] using hz
      have hzr := (Complex.abs_re_le_norm (z - w)).trans hz'.le
      have hzi := (Complex.abs_im_le_norm (z - w)).trans hz'.le
      have hre : |z.re| ≤ 1 / 4 := by
        have : |z.re| ≤ |w.re| + |(z - w).re| := by simpa using abs_add_le w.re (z - w).re
        linarith
      have him : |z.im| ≤ 5 / 4 := by
        have : |z.im| ≤ |w.im| + |(z - w).im| := by simpa using abs_add_le w.im (z - w).im
        linarith
      exact hMB z hre him).1
    calc ‖deriv F w‖ ≤ MB / (1 / 8) := hc
      _ = 8 * MB := by ring
  have h3 : ∀ t : ℝ, |t| ≤ 1 → ‖deriv (deriv (deriv F)) ((t : ℂ) * Complex.I)‖ ≤ 1024 * MB := fun t ht => by
    have hwb : closedBall ((t : ℂ) * Complex.I) (1 / 8) ⊆ U := fun z hz => by
      have hz' : ‖z - (t : ℂ) * Complex.I‖ ≤ 1 / 8 := by simpa [dist_eq_norm] using hz
      have hzr := (Complex.abs_re_le_norm (z - (t : ℂ) * Complex.I)).trans hz'
      show |z.re| < 3 / 8
      have h1' : |z.re| = |(z - (t : ℂ) * Complex.I).re| := by simp
      linarith
    have hc := (cauchy_deriv_two (by norm_num : (0 : ℝ) < 1 / 8) (hF1.mono hwb) fun z hz => by
      have hz' : ‖z - (t : ℂ) * Complex.I‖ = 1 / 8 := by simpa [dist_eq_norm] using hz
      have hzr := (Complex.abs_re_le_norm (z - (t : ℂ) * Complex.I)).trans hz'.le
      have hzi := (Complex.abs_im_le_norm (z - (t : ℂ) * Complex.I)).trans hz'.le
      have hre : |z.re| ≤ 1 / 8 := by
        have : |z.re| = |(z - (t : ℂ) * Complex.I).re| := by simp
        linarith
      have him : |z.im| ≤ 9 / 8 := by
        have hti : ((t : ℂ) * Complex.I).im = t := by simp
        have : |z.im| ≤ |t| + |(z - (t : ℂ) * Complex.I).im| := by
          simpa [hti] using abs_add_le t (z - (t : ℂ) * Complex.I).im
        linarith
      exact h1 z hre him).2
    calc ‖deriv (deriv (deriv F)) ((t : ℂ) * Complex.I)‖ ≤ 2 * (8 * MB) / (1 / 8) ^ 2 := hc
      _ = 1024 * MB := by ring
  have hline : ∀ t : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ) * Complex.I) Complex.I t := fun t => by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
  have hmemU : ∀ t : ℝ, (t : ℂ) * Complex.I ∈ U := fun t => by show |((t : ℂ) * Complex.I).re| < 3 / 8; simp
  have hchain : ∀ (G : ℂ → ℂ), DifferentiableOn ℂ G U → ∀ t : ℝ,
      HasDerivAt (fun x : ℝ => G ((x : ℂ) * Complex.I)) (Complex.I * deriv G ((t : ℂ) * Complex.I)) t := fun G hG t => by
    have hda := (hG.differentiableAt (hUo.mem_nhds (hmemU t))).hasDerivAt
    have hcomp := (hda.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hline t)
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using hcomp
  set f : ℝ → ℂ := fun t => F ((t : ℂ) * Complex.I)
  have hf1 : ∀ t : ℝ, deriv f t = Complex.I * deriv F ((t : ℂ) * Complex.I) :=
    fun t => (hchain F hF t).deriv
  have hf2 : ∀ t : ℝ, deriv (deriv f) t = -(deriv (deriv F) ((t : ℂ) * Complex.I)) := fun t => by
    have hev : deriv f = fun x : ℝ => Complex.I * deriv F ((x : ℂ) * Complex.I) := funext hf1
    rw [hev]
    have hd := ((hchain (deriv F) hF1 t).const_mul Complex.I).deriv
    rw [hd]
    calc Complex.I * (Complex.I * deriv (deriv F) ((t : ℂ) * Complex.I))
        = (Complex.I ^ 2) * deriv (deriv F) ((t : ℂ) * Complex.I) := by ring
      _ = -(deriv (deriv F) ((t : ℂ) * Complex.I)) := by rw [Complex.I_sq]; ring
  have hf3 : ∀ t : ℝ, HasDerivAt (deriv (deriv f))
      (-Complex.I * deriv (deriv (deriv F)) ((t : ℂ) * Complex.I)) t := fun t => by
    have hev : deriv (deriv f) = fun x : ℝ => -(deriv (deriv F) ((x : ℂ) * Complex.I)) := funext hf2
    rw [hev]
    have hd := (hchain (deriv (deriv F)) hF2 t).neg
    convert hd using 1; ring
  have hb2 : ∀ τ ∈ Icc (-1 : ℝ) 1, ‖deriv (deriv f) τ‖ ≤ 1024 * MB * |τ| := fun τ hτ => by
    have hm := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (hf3 t).differentiableAt)
      (fun t ht => by
        rw [(hf3 t).deriv, norm_mul, norm_neg, Complex.norm_I, one_mul]
        exact h3 t (abs_le.mpr ⟨ht.1, ht.2⟩))
      (⟨by norm_num, by norm_num⟩ : (0 : ℝ) ∈ Icc (-1 : ℝ) 1) hτ
    have hz0 : deriv (deriv f) 0 = 0 := by rw [hf2 0]; simp [hF2_0]
    simpa [hz0, Real.norm_eq_abs] using hm
  have hb1 : ∀ τ ∈ Icc (-1 : ℝ) 1, ‖deriv f τ‖ ≤ 1024 * MB * |τ| ^ 2 := fun τ hτ => by
    have hτa : |τ| ≤ 1 := abs_le.mpr ⟨hτ.1, hτ.2⟩
    have hsub : Icc (-|τ|) |τ| ⊆ Icc (-1 : ℝ) 1 := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hdd : ∀ t : ℝ, HasDerivAt (deriv f) (deriv (deriv f) t) t := fun t => by
      have hev : deriv f = fun x : ℝ => Complex.I * deriv F ((x : ℂ) * Complex.I) := funext hf1
      rw [hev]
      have hd := (hchain (deriv F) hF1 t).const_mul Complex.I
      refine hd.congr_deriv ?_
      exact (((hchain (deriv F) hF1 t).const_mul Complex.I).deriv).symm
    have hm := (convex_Icc (-|τ|) |τ|).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (hdd t).differentiableAt)
      (fun t ht => by
        rw [(hdd t).deriv]
        exact (hb2 t (hsub ht)).trans (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨ht.1, ht.2⟩) (by positivity)))
      (⟨by linarith [abs_nonneg τ], abs_nonneg τ⟩ : (0 : ℝ) ∈ Icc (-|τ|) |τ|)
      ⟨neg_abs_le τ, le_abs_self τ⟩
    have hz0 : deriv f 0 = 0 := by rw [hf1 0]; simp [hF1_0]
    rw [hz0, sub_zero, sub_zero, Real.norm_eq_abs] at hm
    calc ‖deriv f τ‖ ≤ 1024 * MB * |τ| * |τ| := hm
      _ = 1024 * MB * |τ| ^ 2 := by ring
  refine ⟨1024 * MB, by positivity, fun τ hτ => ⟨hb1 τ (abs_le.mp hτ), hb2 τ (abs_le.mp hτ)⟩⟩

private lemma fctQ1_left_near_deriv :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, |τ| ≤ 1 →
      ‖deriv (fun t : ℝ => fctQ1 ((t : ℂ) * Complex.I)) τ‖ ≤ M * |τ| ^ 2 ∧
        ‖deriv (deriv (fun t : ℝ => fctQ1 ((t : ℂ) * Complex.I))) τ‖ ≤ M * |τ| := by
  have hUo : DifferentiableOn ℂ fctQ1 {ζ : ℂ | |ζ.re| < 3 / 8} := by
    refine (DifferentiableOn.mul ((differentiableOn_const (16 : ℂ)).mul (differentiableOn_id.pow 3))
      ((differentiableOn_const (1 : ℂ)).sub differentiableOn_id)).div
      ((differentiableOn_id.add (differentiableOn_const (1 : ℂ))).pow 4) ?_
    intro ζ hζ h0
    have hre : (ζ + 1).re > 0 := by simp; linarith [(abs_lt.mp (show |ζ.re| < 3 / 8 from hζ)).1]
    exact pow_ne_zero 4 (fun h => by rw [h] at hre; simp at hre) h0
  have hM3 : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 / 4 → ‖fctQ1 ζ‖ ≤ 64 * ‖ζ‖ ^ 3 := fun ζ hζ => by
    unfold fctQ1
    have h1 : ‖1 - ζ‖ ≤ 5 / 4 := (norm_sub_le 1 ζ).trans (by norm_num; linarith)
    have h2 : 3 / 4 ≤ ‖ζ + 1‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-ζ)
      simp only [norm_neg, norm_one, sub_neg_eq_add, add_comm] at this
      linarith
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
    have hn16 : ‖(16 : ℂ)‖ = 16 := by simp
    rw [hn16]
    have h3 : ‖ζ + 1‖ ^ 4 ≥ (3 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 4
    have h4 : 0 ≤ ‖ζ‖ ^ 3 := pow_nonneg (norm_nonneg ζ) 3
    calc 16 * ‖ζ‖ ^ 3 * ‖1 - ζ‖ / ‖ζ + 1‖ ^ 4
        ≤ 16 * ‖ζ‖ ^ 3 * (5 / 4) / (3 / 4) ^ 4 := by gcongr
      _ = (16 * (5 / 4) / (3 / 4) ^ 4) * ‖ζ‖ ^ 3 := by ring
      _ ≤ 64 * ‖ζ‖ ^ 3 := by gcongr; norm_num
  have hMB : ∀ ζ : ℂ, |ζ.re| ≤ 1 / 4 → |ζ.im| ≤ 5 / 4 → ‖fctQ1 ζ‖ ≤ 1024 := fun ζ hre him => by
    unfold fctQ1
    have hζ : ‖ζ‖ ≤ 3 / 2 := by
      have := Complex.norm_le_abs_re_add_abs_im ζ
      linarith
    have h1 : ‖1 - ζ‖ ≤ 5 / 2 := (norm_sub_le 1 ζ).trans (by norm_num; linarith)
    have h2 : 3 / 4 ≤ ‖ζ + 1‖ := by
      have := Complex.abs_re_le_norm (ζ + 1)
      have hre1 : 3 / 4 ≤ (ζ + 1).re := by simp; linarith [(abs_le.mp hre).1]
      linarith [le_abs_self (ζ + 1).re]
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
    have hn16 : ‖(16 : ℂ)‖ = 16 := by simp
    rw [hn16]
    calc 16 * ‖ζ‖ ^ 3 * ‖1 - ζ‖ / ‖ζ + 1‖ ^ 4
        ≤ 16 * (3 / 2) ^ 3 * (5 / 2) / (3 / 4) ^ 4 := by gcongr
      _ ≤ 1024 := by norm_num
  exact hol_cubic_imag_deriv hUo hM3 hMB

private lemma fctCauchy_left_near_deriv {K4 ε c L1 α B : ℝ} (hc : 0 < c)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip) (hB : 0 ≤ B)
    (hF : ∀ y : ℝ, ‖fctFint K4 ε c L1 α (((7 / 16 : ℝ) : ℂ) + y * Complex.I)‖ ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, |τ| ≤ 1 →
      ‖deriv (fun t : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((t : ℂ) * Complex.I)) τ‖ ≤ M * |τ| ^ 2 ∧
        ‖deriv (deriv (fun t : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((t : ℂ) * Complex.I))) τ‖ ≤ M * |τ| := by
  set U : Set ℂ := {ζ : ℂ | |ζ.re| < 3 / 8}
  have hUo : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hhol : DifferentiableOn ℂ (fctCauchy K4 ε c L1 α (7 / 16)) U :=
    fctCauchy_differentiableOn hc hDc (by norm_num) le_rfl hF hUo fun w (hw : |w.re| < 3 / 8) => by
      have ha := abs_lt.mp hw
      exact ⟨by linarith, by linarith⟩
  obtain ⟨K3, hK30, hK3⟩ := fctCauchy_norm_le_cubic (σ := 7 / 16) (by norm_num) le_rfl
  obtain ⟨K1, hK10, hK1⟩ := fctKsp_div_le_unif (σ := 7 / 16) (by norm_num) le_rfl
    (R := 3 / 2) (m := 3 / 4) (δ := 3 / 16) (by norm_num) (by norm_num) (by norm_num)
  set K_int := (1 / (2 * π)) * K1 * ∫ y : ℝ, 1 / (1 + |y|) ^ 2
  have hM3 : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 / 4 → ‖fctCauchy K4 ε c L1 α (7 / 16) ζ‖ ≤ (K3 * B) * ‖ζ‖ ^ 3 :=
    fun ζ hζ => hK3 K4 ε c L1 α B hB hF ζ hζ
  have hMB : ∀ ζ : ℂ, |ζ.re| ≤ 1 / 4 → |ζ.im| ≤ 5 / 4 →
      ‖fctCauchy K4 ε c L1 α (7 / 16) ζ‖ ≤ K_int * B := fun ζ hre him => by
    have hζ : ‖ζ‖ ≤ 3 / 2 := by linarith [Complex.norm_le_abs_re_add_abs_im ζ]
    have h1 : 3 / 4 ≤ ‖ζ + 1‖ := by
      have := Complex.abs_re_le_norm (ζ + 1)
      have hre1 : 3 / 4 ≤ (ζ + 1).re := by simp; linarith [(abs_le.mp hre).1]
      linarith [le_abs_self (ζ + 1).re]
    have h2 : 3 / 16 ≤ |ζ.re - 7 / 16| := by
      rw [abs_of_nonpos (by linarith [(abs_le.mp hre).2])]
      linarith [(abs_le.mp hre).2]
    unfold fctCauchy
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hint : ‖∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α (7 / 16) ζ y‖ ≤
        ∫ y : ℝ, K1 * B * (1 / (1 + |y|) ^ 2) := by
      refine norm_integral_le_of_norm_le (integrable_inv_one_add_abs_sq.const_mul (K1 * B))
        (Filter.Eventually.of_forall fun y => ?_)
      unfold fctCauchyIntegrand
      rw [mul_div_right_comm, norm_mul]
      calc _ ≤ (K1 / (1 + |y|) ^ 2) * B := mul_le_mul (hK1 ζ hζ h1 h2 y) (hF y) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    rw [integral_const_mul] at hint
    calc 1 / (2 * π) * ‖∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α (7 / 16) ζ y‖
        ≤ 1 / (2 * π) * (K1 * B * ∫ y : ℝ, 1 / (1 + |y|) ^ 2) := by gcongr
      _ = K_int * B := by ring
  exact hol_cubic_imag_deriv hhol hM3 hMB

private lemma fctPhiHat_left_pos_near {K4 ε c L1 α : ℝ} {MΦ MC MQ : ℝ} {Nc β : ℂ}
    (hSplit : ∀ t : ℝ, fctPhiHatAt K4 ε c L1 α ((t : ℂ) * Complex.I) =
      Nc⁻¹ * fctPhiC K4 ε c L1 α ((t : ℂ) * Complex.I) +
        (-(Nc⁻¹ * fctCauchy K4 ε c L1 α (7 / 16) ((t : ℂ) * Complex.I)) +
          β * fctQ1 ((t : ℂ) * Complex.I)))
    (hΦ : EJOn (Ioo (0 : ℝ) (3 / 2)) (fun t => fctPhiC K4 ε c L1 α ((t : ℂ) * Complex.I)) 3 0 0 MΦ)
    (hC_cd : ContDiff ℝ 2 (fun t : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((t : ℂ) * Complex.I)))
    (hC : ∀ τ : ℝ, |τ| ≤ 1 →
      ‖deriv (fun t : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((t : ℂ) * Complex.I)) τ‖ ≤ MC * |τ| ^ 2 ∧
        ‖deriv (deriv (fun t : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((t : ℂ) * Complex.I))) τ‖ ≤ MC * |τ|)
    (hQ_cd : ContDiff ℝ 2 (fun t : ℝ => fctQ1 ((t : ℂ) * Complex.I)))
    (hQ : ∀ τ : ℝ, |τ| ≤ 1 →
      ‖deriv (fun t : ℝ => fctQ1 ((t : ℂ) * Complex.I)) τ‖ ≤ MQ * |τ| ^ 2 ∧
        ‖deriv (deriv (fun t : ℝ => fctQ1 ((t : ℂ) * Complex.I))) τ‖ ≤ MQ * |τ|)
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ‖deriv (fun t : ℝ => fctPhiHatAt K4 ε c L1 α ((t : ℂ) * Complex.I)) τ‖ ≤
        (‖Nc⁻¹‖ * (4 * MΦ + MC) + ‖β‖ * MQ) * τ ^ 2 ∧
      ‖deriv (deriv (fun t : ℝ => fctPhiHatAt K4 ε c L1 α ((t : ℂ) * Complex.I))) τ‖ ≤
        (‖Nc⁻¹‖ * (4 * MΦ + MC) + ‖β‖ * MQ) * τ := by
  set φ1 : ℝ → ℂ := fun t => fctPhiC K4 ε c L1 α ((t : ℂ) * Complex.I)
  set φ2 : ℝ → ℂ := fun t => fctCauchy K4 ε c L1 α (7 / 16) ((t : ℂ) * Complex.I)
  set φ3 : ℝ → ℂ := fun t => fctQ1 ((t : ℂ) * Complex.I)
  have h1c : ContDiffOn ℝ 2 φ1 {t : ℝ | t ≠ 0} := hΦ.c2
  have h2c : ContDiffOn ℝ 2 φ2 {t : ℝ | t ≠ 0} := hC_cd.contDiffOn
  have h3c : ContDiffOn ℝ 2 φ3 {t : ℝ | t ≠ 0} := hQ_cd.contDiffOn
  have hd_on : ∀ (g : ℝ → ℂ), ContDiffOn ℝ 2 g {t : ℝ | t ≠ 0} → ∀ t : ℝ, t ≠ 0 →
      DifferentiableAt ℝ g t ∧ DifferentiableAt ℝ (deriv g) t := fun g hg t ht =>
    ⟨(hg.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_ne.mem_nhds ht),
     ((hg.deriv_of_isOpen isOpen_ne (by norm_num) : ContDiffOn ℝ 1 (deriv g) _).differentiableOn
        (by norm_num) t ht).differentiableAt (isOpen_ne.mem_nhds ht)⟩
  have hform1 : ∀ t : ℝ, t ≠ 0 →
      deriv (fun s : ℝ => fctPhiHatAt K4 ε c L1 α ((s : ℂ) * Complex.I)) t =
        Nc⁻¹ * deriv φ1 t + (-(Nc⁻¹ * deriv φ2 t) + β * deriv φ3 t) := fun t ht => by
    have hev : (fun s : ℝ => fctPhiHatAt K4 ε c L1 α ((s : ℂ) * Complex.I)) =
        fun s : ℝ => Nc⁻¹ * φ1 s + (-(Nc⁻¹ * φ2 s) + β * φ3 s) := funext hSplit
    rw [hev]
    have h1 := (hd_on φ1 h1c t ht).1.hasDerivAt.const_mul Nc⁻¹
    have h2 := ((hd_on φ2 h2c t ht).1.hasDerivAt.const_mul Nc⁻¹).neg
    have h3 := (hd_on φ3 h3c t ht).1.hasDerivAt.const_mul β
    exact (h1.add (h2.add h3)).deriv
  have hform2 :
      deriv (deriv (fun s : ℝ => fctPhiHatAt K4 ε c L1 α ((s : ℂ) * Complex.I))) τ =
        Nc⁻¹ * deriv (deriv φ1) τ + (-(Nc⁻¹ * deriv (deriv φ2) τ) + β * deriv (deriv φ3) τ) := by
    have hev : deriv (fun s : ℝ => fctPhiHatAt K4 ε c L1 α ((s : ℂ) * Complex.I)) =ᶠ[𝓝 τ]
        fun t : ℝ => Nc⁻¹ * deriv φ1 t + (-(Nc⁻¹ * deriv φ2 t) + β * deriv φ3 t) :=
      Filter.eventually_of_mem (isOpen_ne.mem_nhds hτ0.ne') hform1
    rw [hev.deriv_eq]
    have h1 := (hd_on φ1 h1c τ hτ0.ne').2.hasDerivAt.const_mul Nc⁻¹
    have h2 := ((hd_on φ2 h2c τ hτ0.ne').2.hasDerivAt.const_mul Nc⁻¹).neg
    have h3 := (hd_on φ3 h3c τ hτ0.ne').2.hasDerivAt.const_mul β
    exact (h1.add (h2.add h3)).deriv
  have hmemS : τ ∈ Ioo (0 : ℝ) (3 / 2) := ⟨hτ0, by linarith⟩
  have hΦ1 := hΦ.b1 τ hmemS hτ0.ne'
  have hΦ2 := hΦ.b2 τ hmemS hτ0.ne'
  have hw1 : ejW 3 0 0 1 τ ≤ 4 * τ ^ 2 := by
    unfold ejW; simp [abs_of_pos hτ0]
    have hpow : τ ^ ((3 : ℝ) - 1) = τ ^ 2 := by rw [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
    rw [hpow]
    nlinarith [sq_nonneg τ]
  have hw2 : ejW 3 0 0 2 τ ≤ 4 * τ := by
    unfold ejW
    rw [abs_of_pos hτ0, show (3 : ℝ) - ((2 : ℕ) : ℝ) = 1 by norm_num]
    simp
    nlinarith [hτ0, hτ1]
  have hΦ1' : ‖deriv φ1 τ‖ ≤ 4 * MΦ * τ ^ 2 :=
    hΦ1.trans (by calc MΦ * ejW 3 0 0 1 τ ≤ MΦ * (4 * τ ^ 2) := mul_le_mul_of_nonneg_left hw1 hΦ.hM
      _ = _ := by ring)
  have hΦ2' : ‖deriv (deriv φ1) τ‖ ≤ 4 * MΦ * τ :=
    hΦ2.trans (by calc MΦ * ejW 3 0 0 2 τ ≤ MΦ * (4 * τ) := mul_le_mul_of_nonneg_left hw2 hΦ.hM
      _ = _ := by ring)
  have hC12 := hC τ (abs_le.mpr ⟨by linarith, hτ1⟩)
  have hQ12 := hQ τ (abs_le.mpr ⟨by linarith, hτ1⟩)
  rw [abs_of_pos hτ0] at hC12 hQ12
  obtain ⟨hC1, hC2⟩ := hC12
  obtain ⟨hQ1, hQ2⟩ := hQ12
  refine ⟨?_, ?_⟩
  · rw [hform1 τ hτ0.ne']
    calc ‖Nc⁻¹ * deriv φ1 τ + (-(Nc⁻¹ * deriv φ2 τ) + β * deriv φ3 τ)‖
        ≤ ‖Nc⁻¹‖ * ‖deriv φ1 τ‖ + (‖Nc⁻¹‖ * ‖deriv φ2 τ‖ + ‖β‖ * ‖deriv φ3 τ‖) :=
          (norm_add_le _ _).trans (add_le_add (by rw [norm_mul])
            ((norm_add_le _ _).trans (by rw [norm_neg, norm_mul, norm_mul])))
      _ ≤ ‖Nc⁻¹‖ * (4 * MΦ * τ ^ 2) + (‖Nc⁻¹‖ * (MC * τ ^ 2) + ‖β‖ * (MQ * τ ^ 2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hΦ1' (norm_nonneg _))
            (add_le_add (mul_le_mul_of_nonneg_left hC1 (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hQ1 (norm_nonneg _)))
      _ = _ := by ring
  · rw [hform2]
    calc ‖Nc⁻¹ * deriv (deriv φ1) τ + (-(Nc⁻¹ * deriv (deriv φ2) τ) + β * deriv (deriv φ3) τ)‖
        ≤ ‖Nc⁻¹‖ * ‖deriv (deriv φ1) τ‖ + (‖Nc⁻¹‖ * ‖deriv (deriv φ2) τ‖ + ‖β‖ * ‖deriv (deriv φ3) τ‖) :=
          (norm_add_le _ _).trans (add_le_add (by rw [norm_mul])
            ((norm_add_le _ _).trans (by rw [norm_neg, norm_mul, norm_mul])))
      _ ≤ ‖Nc⁻¹‖ * (4 * MΦ * τ) + (‖Nc⁻¹‖ * (MC * τ) + ‖β‖ * (MQ * τ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hΦ2' (norm_nonneg _))
            (add_le_add (mul_le_mul_of_nonneg_left hC2 (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hQ2 (norm_nonneg _)))
      _ = _ := by ring

private lemma conj_neg_hasDerivAt {g : ℝ → ℂ} {t : ℝ} (hg : DifferentiableAt ℝ g (-t)) :
    HasDerivAt (fun s => Complex.conjCLE (g (-s))) (-(Complex.conjCLE (deriv g (-t)))) t := by
  have h1 := hg.hasDerivAt.scomp t (hasDerivAt_neg t)
  have h2 := (Complex.conjCLE.hasFDerivAt (x := g (-t))).comp_hasDerivAt t h1
  refine h2.congr_deriv ?_
  simp [map_neg]

/-- **`fct:splitting` (3), `(fct:Psi-edge)` (`left_near_deriv`)**: for `c ≥ c₀`, `ε = ±1`,
and `0 < |τ| ≤ 1`, `‖∂_τ^j Φ̂_c(iτ)‖ ≤ M |τ|^{3-j}` (`j = 1, 2`). Proved from `FctDescentStmt`. -/
theorem fctPhiHat_left_near_deriv {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ 1 →
        ‖deriv (fun t : ℝ => fctPhiHat h ε c ((t : ℂ) * Complex.I)) τ‖ ≤ M * |τ| ^ 2 ∧
          ‖deriv (deriv (fun t : ℝ => fctPhiHat h ε c ((t : ℂ) * Complex.I))) τ‖ ≤ M * |τ| := by
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨c0D, hcD⟩ := fctDcomp_compData hK4 ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨c0s, B, hSetup⟩ := fctSplitting_setup hK4 hD
  obtain ⟨c0c, hc0c⟩ := fctPhiHat_conj hK4 hD
  obtain ⟨c0c2, hc2⟩ := fctPhiHat_left_c2 hK4 hD
  refine ⟨max c0D (max c0s (max c0c c0c2)), fun ε c hε hc => ?_⟩
  have hDD := hcD ε c hε ((le_max_left _ _).trans hc)
  obtain ⟨hcpos, hDh, hDc, hDb, hF, hDconj⟩ :=
    hSetup ε c hε ((le_max_left _ _).trans (le_max_right _ _) |>.trans hc)
  have hconj := hc0c ε c hε ((le_max_left _ _).trans (le_max_right _ _) |>.trans (le_max_right _ _) |>.trans hc)
  have hc2' := hc2 ε c hε ((le_max_right _ _).trans (le_max_right _ _) |>.trans (le_max_right _ _) |>.trans hc)
  obtain ⟨P, _, hEnv⟩ := hDD.env
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set Nc := fctNcC K4 ε c L1 α
  obtain ⟨MΦ, hΦ_ej⟩ := fctPhiC_near_ejOn (ε := ε) (L1 := L1) hcpos hDc hDb hDconj hEnv
  have hBnn : 0 ≤ B := (norm_nonneg _).trans (hF (7 / 16) 0 (by norm_num) le_rfl)
  obtain ⟨MC, hMCnn, hMC⟩ := fctCauchy_left_near_deriv (K4 := K4) (ε := ε) (L1 := L1) (α := α)
    hcpos hDc hBnn fun y => hF (7 / 16) y (by norm_num) le_rfl
  obtain ⟨MQ, hMQnn, hMQ⟩ := fctQ1_left_near_deriv
  have hUo : IsOpen {ζ : ℂ | |ζ.re| < 3 / 8} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hC_cd : ContDiff ℝ 2 (fun t : ℝ => fctCauchy K4 ε c L1 α (7 / 16) ((t : ℂ) * Complex.I)) := by
    have hhol := fctCauchy_differentiableOn hcpos hDc (by norm_num) le_rfl
      (fun y => hF (7 / 16) y (by norm_num) le_rfl) hUo
      fun w (hw : |w.re| < 3 / 8) => ⟨by linarith [(abs_lt.mp hw).1], by linarith [(abs_lt.mp hw).2]⟩
    rw [← contDiffOn_univ]
    exact (hhol.contDiffOn hUo |>.restrict_scalars ℝ).comp
      (Complex.ofRealCLM.contDiff.mul contDiff_const).contDiffOn
      fun t _ => by show |((t : ℂ) * Complex.I).re| < 3 / 8; simp
  have hQ_cd : ContDiff ℝ 2 (fun t : ℝ => fctQ1 ((t : ℂ) * Complex.I)) := by
    have hhol : DifferentiableOn ℂ fctQ1 {ζ : ℂ | |ζ.re| < 3 / 8} := by
      refine (DifferentiableOn.mul ((differentiableOn_const (16 : ℂ)).mul (differentiableOn_id.pow 3))
        ((differentiableOn_const (1 : ℂ)).sub differentiableOn_id)).div
        ((differentiableOn_id.add (differentiableOn_const (1 : ℂ))).pow 4) ?_
      intro ζ hζ h0
      have hre : (ζ + 1).re > 0 := by simp; linarith [(abs_lt.mp (show |ζ.re| < 3 / 8 from hζ)).1]
      exact pow_ne_zero 4 (fun h => by rw [h] at hre; simp at hre) h0
    rw [← contDiffOn_univ]
    exact (hhol.contDiffOn hUo |>.restrict_scalars ℝ).comp
      (Complex.ofRealCLM.contDiff.mul contDiff_const).contDiffOn
      fun t _ => by show |((t : ℂ) * Complex.I).re| < 3 / 8; simp
  have hSplit : ∀ t : ℝ, fctPhiHatAt K4 ε c L1 α ((t : ℂ) * Complex.I) =
      Nc⁻¹ * fctPhiC K4 ε c L1 α ((t : ℂ) * Complex.I) +
        (-(Nc⁻¹ * fctCauchy K4 ε c L1 α (7 / 16) ((t : ℂ) * Complex.I)) +
          fctBetaC K4 ε c L1 α * fctQ1 ((t : ℂ) * Complex.I)) := fun t => by
    rw [fctPhiHatAt_left_eq_add_tail, fctLeftTail]; ring
  set M := ‖Nc⁻¹‖ * (4 * MΦ + MC) + ‖fctBetaC K4 ε c L1 α‖ * MQ
  have hMnn : 0 ≤ M := by have := hΦ_ej.hM; positivity
  refine ⟨M, hMnn, fun τ hτ hτ1 => ?_⟩
  rcases lt_or_gt_of_ne hτ with hlt | hgt
  · set φ : ℝ → ℂ := fun t => fctPhiHat h ε c ((t : ℂ) * Complex.I)
    have hneg_pos : 0 < -τ := by linarith
    have hneg_le : -τ ≤ 1 := by linarith [(abs_le.mp hτ1).1]
    have hpos := fctPhiHat_left_pos_near hSplit hΦ_ej hC_cd hMC hQ_cd hMQ hneg_pos hneg_le
    have hφ_neg_eq : ∀ t : ℝ, φ t = Complex.conjCLE (φ (-t)) := fun t => by
      have hc := hconj (((-t : ℝ) : ℂ) * Complex.I) ⟨by simp, by simp⟩
      have harg : starRingEnd ℂ (((-t : ℝ) : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      change fctPhiHat h ε c ((t : ℂ) * Complex.I) = _
      rw [← harg, hc]; rfl
    have hev_fn : (fun s => Complex.conjCLE (φ (-s))) = φ := funext fun s => (hφ_neg_eq s).symm
    have hd1 : deriv φ τ = -(Complex.conjCLE (deriv φ (-τ))) := by
      have hφ_neg : DifferentiableAt ℝ φ (-τ) :=
        (hc2'.differentiableOn (by norm_num) (-τ) hneg_pos.ne').differentiableAt (isOpen_ne.mem_nhds hneg_pos.ne')
      have hd := conj_neg_hasDerivAt hφ_neg
      rw [hev_fn] at hd
      exact hd.deriv
    have hd2 : deriv (deriv φ) τ = Complex.conjCLE (deriv (deriv φ) (-τ)) := by
      have hd_conj : ∀ t : ℝ, t < 0 → deriv φ t = -(Complex.conjCLE (deriv φ (-t))) := fun t ht => by
        have htne : (-t : ℝ) ≠ 0 := (by linarith : 0 < -t).ne'
        have hφ_n : DifferentiableAt ℝ φ (-t) :=
          (hc2'.differentiableOn (by norm_num) (-t) htne).differentiableAt (isOpen_ne.mem_nhds htne)
        have hd := conj_neg_hasDerivAt hφ_n
        rw [hev_fn] at hd
        exact hd.deriv
      have hev : deriv φ =ᶠ[𝓝 τ] fun t => -(Complex.conjCLE (deriv φ (-t))) :=
        Filter.eventually_of_mem (isOpen_Iio.mem_nhds hlt) hd_conj
      have hφ'_neg : DifferentiableAt ℝ (deriv φ) (-τ) :=
        ((hc2'.deriv_of_isOpen isOpen_ne (by norm_num) : ContDiffOn ℝ 1 (deriv φ) _).differentiableOn
          (by norm_num) (-τ) hneg_pos.ne').differentiableAt (isOpen_ne.mem_nhds hneg_pos.ne')
      have hd' : HasDerivAt (fun t : ℝ => -(Complex.conjCLE (deriv φ (-t))))
          (Complex.conjCLE (deriv (deriv φ) (-τ))) τ :=
        (conj_neg_hasDerivAt hφ'_neg).neg.congr_deriv (neg_neg _)
      rw [hev.deriv_eq, hd'.deriv]
    have hconj_norm : ∀ z : ℂ, ‖Complex.conjCLE z‖ = ‖z‖ := fun z => by
      change ‖starRingEnd ℂ z‖ = ‖z‖; exact Complex.norm_conj z
    have h1n : ‖deriv φ τ‖ = ‖deriv φ (-τ)‖ := by rw [hd1, norm_neg, hconj_norm]
    have h2n : ‖deriv (deriv φ) τ‖ = ‖deriv (deriv φ) (-τ)‖ := by rw [hd2, hconj_norm]
    have habs : |τ| = -τ := abs_of_neg hlt
    rw [habs, h1n, h2n]
    exact hpos
  · rw [abs_of_pos hgt]
    exact fctPhiHat_left_pos_near hSplit hΦ_ej hC_cd hMC hQ_cd hMQ hgt (by rwa [abs_of_pos hgt] at hτ1)

/-- info: 'FormalResearch.SignUncertainty.fctPhiHat_left_near_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiHat_left_near_deriv

end FormalResearch.SignUncertainty
