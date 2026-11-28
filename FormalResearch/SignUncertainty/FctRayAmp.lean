/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctRayHG
public import FormalResearch.SignUncertainty.UctEnvHolo
public import FormalResearch.SignUncertainty.FctSplittingPsiFarBase

/-!
# Interior-strip amplitude estimates `(d)` and `W(ζ)/A₀(ζ) - 1` (`fct:splitting` (1))

Paper I (`constant_terms_five.tex`), Lemma FCT.6 (`fct:splitting`), proof step (d) and the
boundary-factor ratio `W(ζ)/A₀(ζ) - 1 = O(c⁻¹ / log(2 + y))`.

* `fctRayW_eq_factor`: `fctRayW K4 ε c L1 α t = (1 - t)^{-1/2} exp(B_c(t)) D(t) (H_*/G_ε)(t) (1 - L₁(1 - φ_kill(t; a)) / fctRayP L₁ t)`
  on `|Re t| < 1`, `fctRayP L₁ t ≠ 0`.
* `fctRayP_lower_disc`: on `w ∈ closedBall (ζ + i s) (1 / 2000000)` (`5/16 ≤ ζ.re ≤ 7/16`, `0 ≤ ζ.im`, `0 ≤ s`),
  `7 / 1000000 ≤ ‖fctRayP L₁ w‖`.
* `fctRayW_interior_derivs_and_near_one`: uniform bounds `W0`, `W1`, `W2` and `W_near_one` for `FctRayData` (`(d)`),
  using `cauchy_deriv_two` on `closedBall (ζ + i s) (1 / 2000000)`.
* `fctWarpKA_left_ray_bound`: on `0 ≤ ζ.re ≤ 5/16`, `1 ≤ ζ.im`, `0 ≤ s`,
  `‖fctWarpKA K4 ε c L1 α (ζ + i s)‖ ≤ C_l * (1 + ζ.im + s) * Real.exp (-2 * s) * ‖fctRayN K4 ε c L1 α ζ‖`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty

/-! ### Algebraic factorisation of `fctRayW` and `mellinK0` ratio -/

private lemma mellinK0_eq_factor (c : ℝ) {t : ℂ} (_ht : t.re < 1) (ξ : ℝ) :
    mellinK0 c t ξ = (1 - t) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c t) *
      Complex.exp (c * mellinPhi t ξ) := by
  unfold mellinK0
  ring

/-- Factorisation `W(t) = (1 - t)^{-1/2} exp(B_c(t)) D(t) (H_*/G_ε)(t) (1 - L₁ (1 - φ_kill)/(g_tan+L₁))`
where `fctRayP L₁ t ≠ 0` and `t.re < 1`. -/
lemma fctRayW_eq_factor {K4 ε c L1 α : ℝ} {t : ℂ} (ht : t.re < 1) (hP : fctRayP L1 t ≠ 0) :
    fctRayW K4 ε c L1 α t =
      (1 - t) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c t) * fctDcompAt K4 c α t * ctHG ε t *
        (1 - (L1 : ℂ) * (1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t) / fctRayP L1 t) := by
  unfold fctRayW fctWarpKA fctWarpA fctRayE
  rw [mellinK0_eq_factor c ht (fctXi1 L1)]
  have hE : Complex.exp ((c : ℂ) * mellinPhi t (fctXi1 L1)) ≠ 0 := Complex.exp_ne_zero _
  have hP' : stripG t + (L1 : ℂ) ≠ 0 := hP
  have hlin : stripG t + (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t =
      fctRayP L1 t * (1 - (L1 : ℂ) * (1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t) / fctRayP L1 t) := by
    unfold fctRayP
    field_simp [hP']
    ring
  rw [hlin]
  field_simp [hE, hP]

/-- `W_near_one` identity: `fctRayE * fctRayW / fctRayN - 1 = - L₁ (1 - φ_kill) / fctRayP`. -/
lemma fctRayW_ratio_sub_one {K4 ε c L1 α : ℝ} {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1 / 2)
    (hP : fctRayP L1 ζ ≠ 0) :
    fctRayE c L1 ζ * fctRayW K4 ε c L1 α ζ / fctRayN K4 ε c L1 α ζ - 1 =
      -((L1 : ℂ) * (1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ζ) / fctRayP L1 ζ) := by
  rw [fctRayW_eq_factor (by linarith) hP]
  unfold fctRayN fctRayE
  rw [mellinK0_eq_factor c (by linarith) (fctXi1 L1)]
  have h1z : (1 - ζ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hcp : (1 - ζ) ^ (-(1 / 2 : ℂ)) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have he1 : Complex.exp (binetDiff c ζ) ≠ 0 := Complex.exp_ne_zero _
  have he2 : Complex.exp ((c : ℂ) * mellinPhi ζ (fctXi1 L1)) ≠ 0 := Complex.exp_ne_zero _
  have hD : fctDcompAt K4 c α ζ ≠ 0 := fctDcompAt_ne_zero _
  have hHG : ctHG ε ζ ≠ 0 := ctHG_ne_zero_of_band ε h0 h1
  field_simp [hcp, he1, he2, hD, hHG, hP]
  ring

/-! ### Tangent lower bound on `closedBall (ζ + i s) (1 / 2000000)` -/

private lemma norm_deriv_stripG_quarter {t : ℂ} (h0 : 1 / 4 ≤ t.re) (h1 : t.re ≤ 15 / 32) :
    ‖deriv stripG t‖ ≤ 11 := by
  have ht0 : t ≠ 0 := fun h => by rw [h] at h0; simp at h0; norm_num at h0
  have hre : |t.re| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [(stripG_hasDerivAt ht0 hre).deriv]
  have h1t : ‖1 / t‖ ≤ 4 := by
    rw [one_div, norm_inv]
    have hre_ge : 1 / 4 ≤ ‖t‖ := h0.trans ((le_abs_self _).trans (Complex.abs_re_le_norm t))
    exact (inv_anti₀ (by norm_num) hre_ge).trans_eq (by norm_num)
  have hsin_lb : (1 / 2 : ℝ) ≤ ‖Complex.sin ((π : ℂ) * t)‖ := by
    have hpt : (π : ℂ) * t = ((π * t.re : ℝ) : ℂ) + ((π * t.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have hsq : ‖Complex.sin ((π : ℂ) * t)‖ ^ 2 = Real.sin (π * t.re) ^ 2 + Real.sinh (π * t.im) ^ 2 := by
      rw [hpt, norm_sq_complex_sin]
    have hsin_mono : Real.sin (π / 4) ≤ Real.sin (π * t.re) :=
      Real.strictMonoOn_sin.monotoneOn ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
        ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ (by nlinarith [Real.pi_pos])
    rw [Real.sin_pi_div_four] at hsin_mono
    have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt_of_sq_le (by norm_num)).trans_eq rfl
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [hsq]; nlinarith [sq_nonneg (Real.sinh (π * t.im))]
  have hsin_div : ‖(π : ℂ) / Complex.sin ((π : ℂ) * t)‖ ≤ 6.4 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_iff₀ (by positivity)]
    calc π ≤ 3.2 := by linarith [Real.pi_lt_d2]
      _ = 6.4 * (1 / 2) := by norm_num
      _ ≤ 6.4 * ‖Complex.sin ((π : ℂ) * t)‖ := by gcongr
  have htri := norm_sub_le ((π : ℂ) / Complex.sin ((π : ℂ) * t)) (1 / t)
  linarith

/-- On `w ∈ closedBall (ζ + i s) (1 / 2000000)` (`5/16 ≤ ζ.re ≤ 7/16`, `0 ≤ ζ.im`, `0 ≤ s`, `|L₁| ≤ 1/100`),
`7 / 1000000 ≤ ‖fctRayP L₁ w‖` and `1/4 ≤ w.re ≤ 15/32`. -/
lemma fctRayP_lower_disc {L1 : ℝ} (hL1 : |L1| ≤ 1 / 100) {ζ : ℂ} (h0 : 5 / 16 ≤ ζ.re)
    (h1 : ζ.re ≤ 7 / 16) (him : 0 ≤ ζ.im) {s : ℝ} (hs : 0 ≤ s) {w : ℂ}
    (hw : w ∈ closedBall (ζ + (s : ℂ) * Complex.I) (1 / 2000000)) :
    (7 / 1000000 : ℝ) ≤ ‖fctRayP L1 w‖ ∧ 1 / 4 ≤ w.re ∧ w.re ≤ 15 / 32 := by
  set z0 : ℂ := ζ + (s : ℂ) * Complex.I
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre_diff : |(w - z0).re| ≤ 1 / 2000000 := (Complex.abs_re_le_norm _).trans hw
  have hw_re0 : 1 / 4 ≤ w.re := by
    have := (abs_le.mp hre_diff).1
    simp only [Complex.sub_re, z0, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero] at this
    linarith
  have hw_re1 : w.re ≤ 15 / 32 := by
    have := (abs_le.mp hre_diff).2
    simp only [Complex.sub_re, z0, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero] at this
    linarith
  have hdiff_seg : ‖stripG w - stripG z0‖ ≤ 11 * ‖w - z0‖ := by
    let seg : ℝ → ℂ := fun t => z0 + (t : ℂ) * (w - z0)
    have hmem_seg : ∀ t ∈ Icc (0 : ℝ) 1, 1 / 4 ≤ (seg t).re ∧ (seg t).re ≤ 15 / 32 := by
      intro t ht
      have hre_z0 : 5 / 16 ≤ z0.re ∧ z0.re ≤ 7 / 16 := by simp [z0]; constructor <;> linarith
      have hre_s : (seg t).re = (1 - t) * z0.re + t * w.re := by
        simp only [seg, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.sub_re, zero_mul, sub_zero]; ring
      rw [hre_s]
      constructor
      · nlinarith [ht.1, ht.2]
      · nlinarith [ht.1, ht.2]
    have hd : ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun x : ℝ => stripG (seg x)) (deriv stripG (seg t) * (w - z0)) (Icc 0 1) t := by
      intro t ht
      obtain ⟨hr0, hr1⟩ := hmem_seg t ht
      have he : seg t ∈ edgeStrip := by show |(seg t).re| < 1; rw [abs_lt]; constructor <;> linarith
      have hsg : HasDerivAt stripG (deriv stripG (seg t)) (seg t) :=
        (differentiableOn_stripG.differentiableAt (isOpen_edgeStrip.mem_nhds he)).hasDerivAt
      have hline : HasDerivAt seg (w - z0) t := by
        have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * (w - z0)) (1 * (w - z0)) t :=
          (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (w - z0)
        simpa [seg] using h1.const_add z0
      exact (hsg.comp t hline).hasDerivWithinAt
    have hnb : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv stripG (seg t) * (w - z0)‖ ≤ 11 * ‖w - z0‖ := fun t ht => by
      obtain ⟨hr0, hr1⟩ := hmem_seg t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_deriv_stripG_quarter hr0 hr1) (norm_nonneg _)
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hnb (convex_Icc 0 1)
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    simpa [seg, Real.norm_eq_abs] using hmvt
  have hP_diff : ‖fctRayP L1 z0 - fctRayP L1 w‖ ≤ 11 / 2000000 := by
    have heq : fctRayP L1 z0 - fctRayP L1 w = -(stripG w - stripG z0) := by unfold fctRayP; ring
    rw [heq, norm_neg]
    exact hdiff_seg.trans (by linarith)
  have hz0_lb : (1 / 80000 : ℝ) ≤ ‖fctRayP L1 z0‖ := by
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have hexp : Real.exp (1 : ℝ) < 4 := by linarith [Real.exp_one_lt_d9]
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      have hlt : Real.exp (1 / 2 : ℝ) < 2 := by
        have : Real.exp (1 / 2 : ℝ) ^ 2 < 2 ^ 2 := by linarith
        exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this
      exact ((Real.le_log_iff_exp_le (by norm_num)).mpr hlt.le)
    have hlog_ge : 1 / 2 ≤ Real.log (2 + (ζ.im + s)) :=
      hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
    have hP0 := fctRayP_lower_interior_const hL1 (σ := ζ.re) (u := ζ.im + s) h0 h1 (by linarith)
    have hz0_eq : ((ζ.re : ℂ) + ((ζ.im + s : ℝ) : ℂ) * Complex.I) = z0 := by
      apply Complex.ext <;> simp [z0]
    rw [hz0_eq] at hP0
    linarith
  have htri := norm_sub_norm_le (fctRayP L1 z0) (fctRayP L1 z0 - fctRayP L1 w)
  have hsub : fctRayP L1 z0 - (fctRayP L1 z0 - fctRayP L1 w) = fctRayP L1 w := by ring
  rw [hsub] at htri
  exact ⟨by linarith, hw_re0, hw_re1⟩

/-! ### Uniform ray amplitude bounds `W0`, `W1`, `W2`, and `W_near_one` (`(d)`) -/

private lemma poly_exp_decay_bound {s : ℝ} (hs : 0 ≤ s) :
    (2 + s) * Real.exp (-(π - 3) * s) ≤ 12 := by
  have hpi : (1 / 10 : ℝ) ≤ π - 3 := by linarith [Real.pi_gt_d2]
  have he : (π - 3) * s + 1 ≤ Real.exp ((π - 3) * s) := Real.add_one_le_exp _
  have h2 : s ≤ 10 * Real.exp ((π - 3) * s) := by nlinarith
  have h3 : (2 + s) ≤ 12 * Real.exp ((π - 3) * s) := by
    have : (1 : ℝ) ≤ Real.exp ((π - 3) * s) := Real.one_le_exp (by positivity)
    linarith
  have hexp_pos : 0 < Real.exp ((π - 3) * s) := Real.exp_pos _
  rw [neg_mul, Real.exp_neg]
  calc (2 + s) * (Real.exp ((π - 3) * s))⁻¹ ≤ (12 * Real.exp ((π - 3) * s)) * (Real.exp ((π - 3) * s))⁻¹ := by
        gcongr
    _ = 12 := by field_simp [hexp_pos.ne']

/-- Uniform bound on `fctRayW` on `closedBall (ζ + i s) (1 / 2000000)` for `5/16 ≤ ζ.re ≤ 7/16`,
`0 ≤ ζ.im`, `0 ≤ s`, `c ≥ c₀`, `ε = ±1`. -/
lemma fctRayW_closedBall_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ B_disc c₀ : ℝ, 0 ≤ B_disc ∧ 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ ζ : ℂ, 5 / 16 ≤ ζ.re → ζ.re ≤ 7 / 16 → 0 ≤ ζ.im →
        ∀ s : ℝ, 0 ≤ s → ∀ w ∈ closedBall (ζ + (s : ℂ) * Complex.I) (1 / 2000000),
          ‖fctRayW K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) w‖ ≤
            B_disc * (‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ /
              ‖fctRayE c (fctWarpL1 h ε c) ζ‖) * Real.exp (-3 * s) := by
  obtain ⟨Cz, c0z, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨CL1, c0L1, hCL10, hc0L1, hL1_bd⟩ := abs_fctWarpL1_le h
  obtain ⟨B_D, c0D, hD_data⟩ := fctDcomp_vdata hK4
    ⟨Cz, c0z, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨cHG, CHG, hcHG, hCHG, hHG_band, -⟩ := ctHG_band_two_sided
  obtain ⟨Cpk, hCpk0, hCpk⟩ := FctPhiKill.norm_one_sub_phiPQ_le_one_and_tail 8 8 (by norm_num)
  set C1 : ℝ := 1 + |CL1| * Cpk * (1000000 / 7)
  set c_L_th : ℝ := (100 * |CL1| + 1) ^ 2
  set c₀ : ℝ := max (max c0L1 (max c0D 1)) c_L_th
  have hc01 : 1 ≤ c₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  set B_disc : ℝ := 2 * Real.exp (1 / 2) * Real.exp (2 * |B_D 0|) * (CHG / cHG) * (12 * Real.exp π) * C1
  refine ⟨B_disc, c₀, by positivity, hc01, fun ε c hε hc ζ h0 h1 him s hs w hw => ?_⟩
  have hc1 : 1 ≤ c := hc.trans' hc01
  have hcpos : 0 < c := by linarith
  have hL1c := hL1_bd ε c hε (hc.trans' ((le_max_left _ _).trans (le_max_left _ _)))
  have hc_m23 : c ^ (-(2 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hL1_sm : |fctWarpL1 h ε c| ≤ 1 / 100 := by
    have hsq : (100 * |CL1| + 1) ^ 2 ≤ c := hc.trans' (le_max_right _ _)
    have hsqrt : 100 * |CL1| + 1 ≤ c ^ (2 / 3 : ℝ) := by
      have := Real.le_sqrt_of_sq_le hsq
      rw [Real.sqrt_eq_rpow] at this
      exact this.trans (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num))
    have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hcpos _
    have hinv : CL1 * c ^ (-(2 / 3 : ℝ)) ≤ 1 / 100 := by
      rw [Real.rpow_neg hcpos.le, ← div_eq_mul_inv, div_le_iff₀ hc23]
      have : CL1 ≤ |CL1| := le_abs_self _
      nlinarith
    exact hL1c.trans hinv
  have hL1_le_CL1 : |fctWarpL1 h ε c| ≤ |CL1| :=
    hL1c.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (mul_le_of_le_one_right (abs_nonneg _) hc_m23))
  obtain ⟨hP_lb, hw0, hw1⟩ := fctRayP_lower_disc hL1_sm h0 h1 him hs hw
  have hP_ne : fctRayP (fctWarpL1 h ε c) w ≠ 0 := norm_pos_iff.mp (by linarith)
  have hw_cl : w ∈ closedStrip := ⟨by linarith, by linarith⟩
  have hζ_cl : ζ ∈ closedStrip := ⟨by linarith, by linarith⟩
  rw [fctRayW_eq_factor (by linarith) hP_ne]
  have hNE_eq : ‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ /
      ‖fctRayE c (fctWarpL1 h ε c) ζ‖ =
      ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ * ‖Complex.exp (binetDiff c ζ)‖ *
        ‖fctDcompAt K4 c (fctWarpAlpha h ε c) ζ‖ * ‖ctHG ε ζ‖ := by
    unfold fctRayN fctRayE
    rw [mellinK0_eq_factor c (by linarith) (fctXi1 (fctWarpL1 h ε c))]
    have hEne : ‖Complex.exp ((c : ℂ) * mellinPhi ζ (fctXi1 (fctWarpL1 h ε c)))‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    field_simp [hEne]
  rw [hNE_eq, norm_mul, norm_mul, norm_mul, norm_mul]
  have h1w_norm : 1 / 2 ≤ ‖1 - w‖ := by
    have := (le_abs_self (1 - w).re).trans (Complex.abs_re_le_norm (1 - w))
    simp only [Complex.sub_re, Complex.one_re] at this; linarith
  have h1ζ_ub : ‖1 - ζ‖ ≤ 1 + ζ.im := by
    have := Complex.norm_le_abs_re_add_abs_im (1 - ζ)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
    rw [abs_of_nonneg (by linarith), abs_of_nonneg him] at this
    linarith
  have h1ζ_ratio : ‖1 - ζ‖ / ‖1 - w‖ ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]
    by_cases him1 : ζ.im ≤ 1
    · linarith
    · push Not at him1
      have hwim : ζ.im / 2 ≤ ‖1 - w‖ := by
        rw [mem_closedBall, dist_eq_norm] at hw
        have him_diff : |(w - (ζ + (s : ℂ) * Complex.I)).im| ≤ 1 / 2000000 :=
          (Complex.abs_im_le_norm _).trans hw
        have hwim' : ζ.im + s - 1 / 2000000 ≤ w.im := by
          have := (abs_le.mp him_diff).1; simp at this; linarith
        have h1w_im : |-(w.im)| ≤ ‖1 - w‖ := by simpa using Complex.abs_im_le_norm (1 - w)
        rw [abs_neg, abs_of_nonneg (by linarith)] at h1w_im
        linarith
      linarith
  have hcp_ratio : ‖(1 - w) ^ (-(1 / 2 : ℂ))‖ ≤ 2 * ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ := by
    have hneg_half : -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hneg_half, Complex.norm_cpow_real, Complex.norm_cpow_real,
      Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    have h4 : (‖1 - ζ‖ / ‖1 - w‖) ^ (1 / 2 : ℝ) ≤ 2 := by
      calc (‖1 - ζ‖ / ‖1 - w‖) ^ (1 / 2 : ℝ) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) h1ζ_ratio (by norm_num)
        _ = 2 := by norm_num
    have h1ζ_pos : 0 < ‖1 - ζ‖ := norm_pos_iff.mpr fun he => by
      have := congr_arg Complex.re he; simp at this; linarith
    rw [Real.div_rpow (norm_nonneg _) (norm_nonneg _), div_le_iff₀ (by positivity)] at h4
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = ‖1 - ζ‖ ^ (1 / 2 : ℝ) * (‖1 - ζ‖ ^ (1 / 2 : ℝ))⁻¹ := (mul_inv_cancel₀ (by positivity)).symm
      _ ≤ (2 * ‖1 - w‖ ^ (1 / 2 : ℝ)) * (‖1 - ζ‖ ^ (1 / 2 : ℝ))⁻¹ := by gcongr
      _ = 2 * (‖1 - ζ‖ ^ (1 / 2 : ℝ))⁻¹ * ‖1 - w‖ ^ (1 / 2 : ℝ) := by ring
  have hB_ratio : ‖Complex.exp (binetDiff c w)‖ ≤ Real.exp (1 / 2) * ‖Complex.exp (binetDiff c ζ)‖ := by
    have hbw : ‖binetDiff c w‖ ≤ 1 / 4 := by
      have hb := binetDiff_norm_le hcpos (by linarith : w.re < 1)
      have h1w_re : 1 / (1 - w.re) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      calc ‖binetDiff c w‖ ≤ 1 / (12 * c) * (2 + 1) := hb.trans (by gcongr)
        _ ≤ 1 / (12 * 1) * (2 + 1) := by gcongr
        _ = 1 / 4 := by norm_num
    have hbz : ‖binetDiff c ζ‖ ≤ 1 / 4 := by
      have hb := binetDiff_norm_le hcpos (by linarith : ζ.re < 1)
      have h1ζ_re : 1 / (1 - ζ.re) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      calc ‖binetDiff c ζ‖ ≤ 1 / (12 * c) * (2 + 1) := hb.trans (by gcongr)
        _ ≤ 1 / (12 * 1) * (2 + 1) := by gcongr
        _ = 1 / 4 := by norm_num
    rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp ((Complex.abs_re_le_norm _).trans hbw)).2,
      (abs_le.mp ((Complex.abs_re_le_norm _).trans hbz)).1])
  have hD_ratio : ‖fctDcompAt K4 c (fctWarpAlpha h ε c) w‖ ≤
      Real.exp (2 * |B_D 0|) * ‖fctDcompAt K4 c (fctWarpAlpha h ε c) ζ‖ := by
    obtain ⟨v, -, -, -, hvB, hvD⟩ := hD_data ε c hε (hc.trans' (by simp only [c₀, le_max_iff]; left; right; left; exact le_rfl))
    have hDw : fctDcompAt K4 c (fctWarpAlpha h ε c) w = Complex.exp (FctCompD.stripCompGExt v w) := hvD w
    have hDζ : fctDcompAt K4 c (fctWarpAlpha h ε c) ζ = Complex.exp (FctCompD.stripCompGExt v ζ) := hvD ζ
    have hgw := hvB 0 (by omega) w hw_cl
    have hgζ := hvB 0 (by omega) ζ hζ_cl
    simp only [iteratedDeriv_zero] at hgw hgζ
    change ‖fctDcompAt K4 c (fctWarpAlpha h ε c) w‖ ≤ _
    rw [show fctDcompAt K4 c (fctWarpAlpha h ε c) w = Complex.exp (FctCompD.stripCompGExt v w) from hDw,
      show fctDcompAt K4 c (fctWarpAlpha h ε c) ζ = Complex.exp (FctCompD.stripCompGExt v ζ) from hDζ,
      Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by
      have h1' := (abs_le.mp ((Complex.abs_re_le_norm (FctCompD.stripCompGExt v w)).trans hgw)).2
      have h2' := (abs_le.mp ((Complex.abs_re_le_norm (FctCompD.stripCompGExt v ζ)).trans hgζ)).1
      linarith [le_abs_self (B_D 0)])
  have hHG_ratio : ‖ctHG ε w‖ ≤ (CHG / cHG) * (12 * Real.exp π) * Real.exp (-3 * s) * ‖ctHG ε ζ‖ := by
    have hwb := (hHG_band ε w hw_cl hw0 hw1).2
    have hζb := (hHG_band ε ζ hζ_cl (by linarith) (by linarith)).1
    rw [mem_closedBall, dist_eq_norm] at hw
    have him_diff : |(w - (ζ + (s : ℂ) * Complex.I)).im| ≤ 1 :=
      (Complex.abs_im_le_norm _).trans (hw.trans (by norm_num))
    have hwim_le : |w.im| ≤ ζ.im + s + 1 := by
      have hadd : |w.im| ≤ |(ζ + (s : ℂ) * Complex.I).im| + |(w - (ζ + (s : ℂ) * Complex.I)).im| := by
        calc |w.im| = |(ζ + (s : ℂ) * Complex.I).im + (w - (ζ + (s : ℂ) * Complex.I)).im| := by
              congr 1; simp
          _ ≤ |(ζ + (s : ℂ) * Complex.I).im| + |(w - (ζ + (s : ℂ) * Complex.I)).im| := abs_add_le _ _
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, abs_of_nonneg (by linarith : 0 ≤ ζ.im + s)] at hadd
      linarith
    have hpoly : (1 + |w.im|) ≤ (1 + |ζ.im|) * (2 + s) := by
      rw [abs_of_nonneg him]; nlinarith
    have hexp_im : Real.exp (-(π * |w.im|)) ≤ Real.exp π * Real.exp (-(π * s)) * Real.exp (-(π * |ζ.im|)) := by
      have hwim_ge : ζ.im + s - 1 ≤ |w.im| := by
        have := (abs_le.mp him_diff).1
        simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at this
        exact (by linarith : ζ.im + s - 1 ≤ w.im).trans (le_abs_self _)
      rw [← Real.exp_add, ← Real.exp_add, abs_of_nonneg him]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have h1y_pos : 0 < 1 + |ζ.im| := by linarith [abs_nonneg ζ.im]
    have hrat_im : (1 + |w.im|) * Real.exp (-(π * |w.im|)) ≤
        (12 * Real.exp π) * Real.exp (-3 * s) * ((1 + |ζ.im|) * Real.exp (-(π * |ζ.im|))) := by
      have hpe := poly_exp_decay_bound hs
      have hexp_split : Real.exp π * Real.exp (-(π * s)) =
          Real.exp π * Real.exp (-(π - 3) * s) * Real.exp (-3 * s) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      calc (1 + |w.im|) * Real.exp (-(π * |w.im|))
          ≤ ((1 + |ζ.im|) * (2 + s)) * (Real.exp π * Real.exp (-(π * s)) * Real.exp (-(π * |ζ.im|))) :=
            mul_le_mul hpoly hexp_im (by positivity) (by positivity)
        _ = (2 + s) * (Real.exp π * Real.exp (-(π * s))) * ((1 + |ζ.im|) * Real.exp (-(π * |ζ.im|))) := by ring
        _ = (Real.exp π * ((2 + s) * Real.exp (-(π - 3) * s))) * Real.exp (-3 * s) *
              ((1 + |ζ.im|) * Real.exp (-(π * |ζ.im|))) := by
            rw [hexp_split]; ring
        _ ≤ (Real.exp π * 12) * Real.exp (-3 * s) * ((1 + |ζ.im|) * Real.exp (-(π * |ζ.im|))) := by
            gcongr
        _ = _ := by ring
    calc ‖ctHG ε w‖ ≤ CHG * (1 + |w.im|) * Real.exp (-(π * |w.im|)) := hwb
      _ = CHG * ((1 + |w.im|) * Real.exp (-(π * |w.im|))) := by ring
      _ ≤ CHG * ((12 * Real.exp π) * Real.exp (-3 * s) * ((1 + |ζ.im|) * Real.exp (-(π * |ζ.im|)))) := by
          gcongr
      _ = (CHG / cHG) * (12 * Real.exp π) * Real.exp (-3 * s) * (cHG * (1 + |ζ.im|) * Real.exp (-(π * |ζ.im|))) := by
          field_simp [hcHG.ne']
      _ ≤ (CHG / cHG) * (12 * Real.exp π) * Real.exp (-3 * s) * ‖ctHG ε ζ‖ := by gcongr
  have hcut_bd : ‖1 - (fctWarpL1 h ε c : ℂ) * (1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) w) /
      fctRayP (fctWarpL1 h ε c) w‖ ≤ C1 := by
    have ha : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hcpos _
    have hpk := (hCpk ha (by linarith : 0 ≤ w.re)).1
    have hpk' : ‖1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) w‖ ≤ Cpk := by
      simpa only [FctPhiKill.phiKill] using hpk
    calc ‖1 - (fctWarpL1 h ε c : ℂ) * (1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) w) /
            fctRayP (fctWarpL1 h ε c) w‖
        ≤ ‖(1 : ℂ)‖ + ‖(fctWarpL1 h ε c : ℂ) * (1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) w) /
            fctRayP (fctWarpL1 h ε c) w‖ := norm_sub_le _ _
      _ = 1 + |fctWarpL1 h ε c| * ‖1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) w‖ /
            ‖fctRayP (fctWarpL1 h ε c) w‖ := by
          rw [norm_one, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 + |CL1| * Cpk / (7 / 1000000) := by gcongr
      _ = C1 := by simp only [C1]; ring
  calc ‖(1 - w) ^ (-(1 / 2 : ℂ))‖ * ‖Complex.exp (binetDiff c w)‖ *
        ‖fctDcompAt K4 c (fctWarpAlpha h ε c) w‖ * ‖ctHG ε w‖ *
        ‖1 - (fctWarpL1 h ε c : ℂ) * (1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) w) /
          fctRayP (fctWarpL1 h ε c) w‖
      ≤ (2 * ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖) * (Real.exp (1 / 2) * ‖Complex.exp (binetDiff c ζ)‖) *
          (Real.exp (2 * |B_D 0|) * ‖fctDcompAt K4 c (fctWarpAlpha h ε c) ζ‖) *
          ((CHG / cHG) * (12 * Real.exp π) * Real.exp (-3 * s) * ‖ctHG ε ζ‖) * C1 := by
        gcongr
    _ = B_disc * (‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ * ‖Complex.exp (binetDiff c ζ)‖ *
          ‖fctDcompAt K4 c (fctWarpAlpha h ε c) ζ‖ * ‖ctHG ε ζ‖) * Real.exp (-3 * s) := by
        simp only [B_disc]; ring

/-- **Steps `(d)` and `W_near_one` of `FctRayData`** (`fct:splitting` (1)) for `5/16 ≤ ζ.re ≤ 7/16`, `0 ≤ ζ.im`. -/
theorem fctRayW_interior_derivs_and_near_one {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ B0 c₀ : ℝ, 0 ≤ B0 ∧ 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ ζ : ℂ, 5 / 16 ≤ ζ.re → ζ.re ≤ 7 / 16 → 0 ≤ ζ.im →
        (∀ s : ℝ, 0 ≤ s →
          ‖fctRayW K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (ζ + (s : ℂ) * Complex.I)‖ ≤
            B0 * (‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ /
              ‖fctRayE c (fctWarpL1 h ε c) ζ‖) * Real.exp (-3 * s) ∧
          ‖deriv (fctRayW K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)) (ζ + (s : ℂ) * Complex.I)‖ ≤
            B0 * (‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ /
              ‖fctRayE c (fctWarpL1 h ε c) ζ‖) * Real.exp (-3 * s) ∧
          ‖deriv (deriv (fctRayW K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c))) (ζ + (s : ℂ) * Complex.I)‖ ≤
            B0 * (‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ /
              ‖fctRayE c (fctWarpL1 h ε c) ζ‖) * Real.exp (-3 * s)) ∧
        ‖fctRayE c (fctWarpL1 h ε c) ζ * fctRayW K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ /
            fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ - 1‖ ≤
          B0 / (c * Real.log (2 + ζ.im)) := by
  obtain ⟨B_disc, c0w, hBw0, hc0w, hWdisc⟩ := fctRayW_closedBall_bound hK4 h
  obtain ⟨CL1, c0L1, hCL10, hc0L1, hL1_bd⟩ := abs_fctWarpL1_le h
  obtain ⟨Cz, c0z, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨c0D, hcD⟩ := fctDcomp_compData hK4 ⟨Cz, c0z, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨Cpk, hCpk0, hCpk⟩ := FctPhiKill.norm_one_sub_phiPQ_le_one_and_tail 8 8 (by norm_num)
  set r : ℝ := 1 / 2000000
  have hr : 0 < r := by norm_num
  set B_cau : ℝ := B_disc * (2 / r ^ 2)
  set B_near : ℝ := |CL1| * Cpk * (16 / 5 : ℝ) ^ 8 * 40000
  set B0 : ℝ := max (max B_disc B_cau) B_near
  set c_L_th : ℝ := (100 * |CL1| + 1) ^ 2
  set c₀ : ℝ := max (max (max c0w c0L1) c0D) (max c_L_th 1)
  have hc01 : 1 ≤ c₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B0, c₀, by positivity, hc01, fun ε c hε hc ζ h0 h1 him => ?_⟩
  have hc1 : 1 ≤ c := hc.trans' hc01
  have hcpos : 0 < c := by linarith
  have hcD' := hcD ε c hε (hc.trans' ((le_max_right _ _).trans (le_max_left _ _)))
  have hL1c := hL1_bd ε c hε (hc.trans' ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))))
  have hL1_sm : |fctWarpL1 h ε c| ≤ 1 / 100 := by
    have hsq : (100 * |CL1| + 1) ^ 2 ≤ c := hc.trans' ((le_max_left _ _).trans (le_max_right _ _))
    have hsqrt : 100 * |CL1| + 1 ≤ c ^ (2 / 3 : ℝ) := by
      have := Real.le_sqrt_of_sq_le hsq
      rw [Real.sqrt_eq_rpow] at this
      exact this.trans (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num))
    have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hcpos _
    have hinv : CL1 * c ^ (-(2 / 3 : ℝ)) ≤ 1 / 100 := by
      rw [Real.rpow_neg hcpos.le, ← div_eq_mul_inv, div_le_iff₀ hc23]
      have : CL1 ≤ |CL1| := le_abs_self _
      nlinarith
    exact hL1c.trans hinv
  have hW_diff := differentiableOn_fctRayW (K4 := K4) (ε := ε) (L1 := fctWarpL1 h ε c)
    (α := fctWarpAlpha h ε c) hcpos hcD'.hol
  constructor
  · intro s hs
    set z0 : ℂ := ζ + (s : ℂ) * Complex.I
    have hball_sub : closedBall z0 r ⊆ strip ∩ fctRayP (fctWarpL1 h ε c) ⁻¹' {0}ᶜ := by
      intro w hw
      obtain ⟨hP, hw0, hw1⟩ := fctRayP_lower_disc hL1_sm h0 h1 him hs hw
      exact ⟨⟨by linarith, by linarith⟩, fun hzero => by
        change fctRayP (fctWarpL1 h ε c) w = 0 at hzero
        rw [hzero, norm_zero] at hP; linarith⟩
    have hW_ball := hW_diff.mono hball_sub
    set M_ray : ℝ := B_disc * (‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ /
      ‖fctRayE c (fctWarpL1 h ε c) ζ‖) * Real.exp (-3 * s)
    have hM_ball : ∀ w ∈ sphere z0 r,
        ‖fctRayW K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) w‖ ≤ M_ray := fun w hw =>
      hWdisc ε c hε (hc.trans' ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))))
        ζ h0 h1 him s hs w (sphere_subset_closedBall hw)
    obtain ⟨hc1', hc2'⟩ := cauchy_deriv_two hr hW_ball hM_ball
    have hW0_ball := hWdisc ε c hε (hc.trans' ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))))
      ζ h0 h1 him s hs z0 (mem_closedBall_self hr.le)
    have hB_disc_le : B_disc ≤ B0 := (le_max_left _ _).trans (le_max_left _ _)
    have hAE_nn : 0 ≤ ‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ /
        ‖fctRayE c (fctWarpL1 h ε c) ζ‖ * Real.exp (-3 * s) := by positivity
    refine ⟨hW0_ball.trans ?_, hc1'.trans ?_, hc2'.trans ?_⟩
    · calc M_ray = B_disc * (‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ /
            ‖fctRayE c (fctWarpL1 h ε c) ζ‖ * Real.exp (-3 * s)) := by simp only [M_ray]; ring
        _ ≤ B0 * _ := by gcongr
        _ = _ := by ring
    · calc M_ray / r = (B_disc / r) * (‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ /
            ‖fctRayE c (fctWarpL1 h ε c) ζ‖ * Real.exp (-3 * s)) := by simp only [M_ray]; ring
        _ ≤ B_cau * _ := by
            have hle : B_disc / r ≤ B_cau := by
              have hdiv : 1 / r ≤ 2 / r ^ 2 := by norm_num [r]
              calc B_disc / r = B_disc * (1 / r) := by ring
                _ ≤ B_disc * (2 / r ^ 2) := by gcongr
            gcongr
        _ ≤ B0 * _ := by gcongr; exact (le_max_right _ _).trans (le_max_left _ _)
        _ = _ := by ring
    · calc 2 * M_ray / r ^ 2 = B_cau * (‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ /
            ‖fctRayE c (fctWarpL1 h ε c) ζ‖ * Real.exp (-3 * s)) := by simp only [M_ray, B_cau]; ring
        _ ≤ B0 * _ := by gcongr; exact (le_max_right _ _).trans (le_max_left _ _)
        _ = _ := by ring
  · have hP_lb := fctRayP_lower_interior_const hL1_sm h0 h1 him
    have hz_eq : ((ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I) = ζ := by apply Complex.ext <;> simp
    rw [hz_eq] at hP_lb
    have hlog2_pos : 0 < Real.log (2 + ζ.im) := Real.log_pos (by linarith)
    have hP_ne : fctRayP (fctWarpL1 h ε c) ζ ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hP_lb)
    rw [fctRayW_ratio_sub_one (by linarith) (by linarith) hP_ne, norm_neg, norm_div, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    have ha : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hcpos _
    have hζ_ne : ζ ≠ 0 := fun h0' => by rw [h0'] at h0; simp at h0; norm_num at h0
    have hpk := (hCpk ha (by linarith : 0 ≤ ζ.re)).2 hζ_ne
    have hζ_norm : 5 / 16 ≤ ‖ζ‖ := h0.trans ((le_abs_self _).trans (Complex.abs_re_le_norm ζ))
    have hrat : (c ^ (-(1 / 12 : ℝ)) / ‖ζ‖) ^ 8 ≤ (16 / 5 : ℝ) ^ 8 * c ^ (-(2 / 3 : ℝ)) := by
      have h1' : c ^ (-(1 / 12 : ℝ)) / ‖ζ‖ ≤ (16 / 5 : ℝ) * c ^ (-(1 / 12 : ℝ)) := by
        rw [div_le_iff₀ (by linarith)]
        calc c ^ (-(1 / 12 : ℝ)) = (16 / 5 : ℝ) * c ^ (-(1 / 12 : ℝ)) * (5 / 16) := by ring
          _ ≤ (16 / 5 : ℝ) * c ^ (-(1 / 12 : ℝ)) * ‖ζ‖ := by gcongr
      calc (c ^ (-(1 / 12 : ℝ)) / ‖ζ‖) ^ 8 ≤ ((16 / 5 : ℝ) * c ^ (-(1 / 12 : ℝ))) ^ 8 :=
            pow_le_pow_left₀ (by positivity) h1' 8
        _ = (16 / 5 : ℝ) ^ 8 * (c ^ (-(1 / 12 : ℝ))) ^ 8 := by rw [mul_pow]
        _ = (16 / 5 : ℝ) ^ 8 * c ^ (-(2 / 3 : ℝ)) := by
            rw [← Real.rpow_natCast (c ^ (-(1 / 12 : ℝ))) 8, ← Real.rpow_mul hcpos.le]; congr 2; norm_num
    have hcc : c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) ≤ c⁻¹ := by
      rw [← Real.rpow_add hcpos, ← Real.rpow_neg_one c]
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hnum_bd : |fctWarpL1 h ε c| * ‖1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ζ‖ ≤
        (|CL1| * Cpk * (16 / 5 : ℝ) ^ 8) * c⁻¹ := by
      have hpk' : ‖1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ζ‖ ≤ Cpk * (c ^ (-(1 / 12 : ℝ)) / ‖ζ‖) ^ 8 := by
        simpa only [FctPhiKill.phiKill] using hpk
      calc |fctWarpL1 h ε c| * ‖1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ζ‖
          ≤ (|CL1| * c ^ (-(2 / 3 : ℝ))) * (Cpk * ((16 / 5 : ℝ) ^ 8 * c ^ (-(2 / 3 : ℝ)))) := by
            gcongr
            · exact hL1c.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
            · exact hpk'.trans (mul_le_mul_of_nonneg_left hrat hCpk0)
        _ = (|CL1| * Cpk * (16 / 5 : ℝ) ^ 8) * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ))) := by ring
        _ ≤ (|CL1| * Cpk * (16 / 5 : ℝ) ^ 8) * c⁻¹ := by gcongr
    calc |fctWarpL1 h ε c| * ‖1 - FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ζ‖ / ‖fctRayP (fctWarpL1 h ε c) ζ‖
        ≤ ((|CL1| * Cpk * (16 / 5 : ℝ) ^ 8) * c⁻¹) / ((1 / 40000 : ℝ) * Real.log (2 + ζ.im)) :=
          div_le_div₀ (by positivity) hnum_bd (by positivity) hP_lb
      _ = B_near / (c * Real.log (2 + ζ.im)) := by
          simp only [B_near]; field_simp [hcpos.ne', hlog2_pos.ne']
      _ ≤ B0 / (c * Real.log (2 + ζ.im)) := by
          gcongr; exact le_max_right _ _

/-- Polynomial-times-exponential vertical ray bound on `{0 ≤ ζ.re ≤ 7/16, 1 ≤ ζ.im}`
(used both for horizontal tail decay `0 ≤ r ≤ 7/16` in Cauchy closing and for fixed-`c` linear
growth in Phragmén–Lindelöf on `[0, 5/16] × ℝ`). -/
lemma fctWarpKA_left_ray_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C_l c₀ : ℝ, 0 ≤ C_l ∧ 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 7 / 16 → 1 ≤ ζ.im →
        ∀ s : ℝ, 0 ≤ s →
          ‖fctWarpKA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (ζ + (s : ℂ) * Complex.I)‖ ≤
            C_l * (1 + ζ.im + s) * Real.exp (-2 * s) *
              ‖fctRayN K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ := by
  obtain ⟨Cz, c0z, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨CL1, c0L1, hCL10, hc0L1, hL1_bd⟩ := abs_fctWarpL1_le h
  obtain ⟨B_D, c0D, hD_data⟩ := fctDcomp_vdata hK4
    ⟨Cz, c0z, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨cHG, CHG, hcHG, hCHG, -, hHG_left⟩ := ctHG_band_two_sided
  obtain ⟨Cg, hCg0, hCg⟩ := stripG_far_bound
  obtain ⟨Cpk, hCpk0, hCpk⟩ := FctPhiKill.norm_phiPQ_le 8 8
  set c₀ : ℝ := max (max c0L1 c0D) 1
  have hc01 : 1 ≤ c₀ := le_max_right _ _
  set C_tan : ℝ := Cg + |CL1| * Cpk
  set C_l : ℝ := 2 * Real.exp (1 / 2) * Real.exp (2 * |B_D 0|) * (CHG / cHG) * 12 * C_tan
  refine ⟨C_l, c₀, by positivity, hc01, fun ε c hε hc ζ h0 h1 him s hs => ?_⟩
  have hc1 : 1 ≤ c := hc.trans' hc01
  have hcpos : 0 < c := by linarith
  have hL1c := hL1_bd ε c hε (hc.trans' ((le_max_left _ _).trans (le_max_left _ _)))
  have hL1_le : |fctWarpL1 h ε c| ≤ |CL1| :=
    hL1c.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (mul_le_of_le_one_right (abs_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num))))
  set t : ℂ := ζ + (s : ℂ) * Complex.I
  have ht_re : t.re = ζ.re := by simp [t]
  have ht_im : t.im = ζ.im + s := by simp [t]
  have ht_cl : t ∈ closedStrip := ⟨by rw [ht_re]; exact h0, by rw [ht_re]; linarith⟩
  have hζ_cl : ζ ∈ closedStrip := ⟨h0, by linarith⟩
  have him_t : 1 ≤ |t.im| := by rw [ht_im, abs_of_nonneg (by linarith)]; linarith
  have him_ζ : 1 ≤ |ζ.im| := by rw [abs_of_nonneg (by linarith)]; linarith
  unfold fctWarpKA fctWarpA fctRayN
  rw [mellinK0_eq_factor c (by rw [ht_re]; linarith : t.re < 1) (fctXi1 (fctWarpL1 h ε c)),
    mellinK0_eq_factor c (by linarith : ζ.re < 1) (fctXi1 (fctWarpL1 h ε c))]
  have hE_le : ‖fctRayE c (fctWarpL1 h ε c) t‖ ≤ ‖fctRayE c (fctWarpL1 h ε c) ζ‖ := by
    refine fctRayE_norm_le hcpos (by rw [abs_lt]; constructor <;> linarith) (fun v hv => ?_) s hs
    by_cases hv0 : ζ.re = 0
    · have hτpos : 0 < ζ.im + v := by linarith
      have ht0 : ζ + (v : ℂ) * Complex.I ≠ 0 := fun he => by
        have := congr_arg Complex.im he; simp at this; linarith
      have hz0 : ζ + (v : ℂ) * Complex.I = ((0 : ℝ) : ℂ) + ((ζ.im + v : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hv0]
      have hcont : ContinuousAt (fun x : ℝ => (stripG ((x : ℂ) + ((ζ.im + v : ℝ) : ℂ) * Complex.I)).im) 0 := by
        have hd : ContinuousAt stripG (((0 : ℝ) : ℂ) + ((ζ.im + v : ℝ) : ℂ) * Complex.I) :=
          stripG_differentiableOn.continuousOn.continuousAt
            (((isOpen_lt continuous_re.abs continuous_const).inter isOpen_ne).mem_nhds
              ⟨by simp, by simpa [hz0] using ht0⟩)
        have hlin : ContinuousAt (fun x : ℝ => (x : ℂ) + ((ζ.im + v : ℝ) : ℂ) * Complex.I) 0 :=
          (Complex.continuous_ofReal.add continuous_const).continuousAt
        exact ContinuousAt.comp (g := Complex.im) Complex.continuous_im.continuousAt
          (ContinuousAt.comp (g := stripG) (f := fun x : ℝ => (x : ℂ) + ((ζ.im + v : ℝ) : ℂ) * Complex.I) hd hlin)
      have hev : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0),
          0 ≤ (stripG ((x : ℂ) + ((ζ.im + v : ℝ) : ℂ) * Complex.I)).im := by
        have hlt : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0), x < 1 :=
          (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
        filter_upwards [eventually_mem_nhdsWithin, hlt] with x hx0 hx1
        exact im_stripG_nonneg (by simpa using hx0) (by simpa using hx1) (by simp; linarith)
      have hge := ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
      rw [← hz0] at hge
      exact hge
    · exact im_stripG_nonneg (by simp; exact lt_of_le_of_ne h0 (Ne.symm hv0)) (by simp; linarith) (by simp; linarith)
  have h1t_im : 1 ≤ ‖1 - t‖ := by
    have h : |t.im| ≤ ‖1 - t‖ := by simpa using Complex.abs_im_le_norm (1 - t)
    linarith
  have h1ζ_ub : ‖1 - ζ‖ ≤ 2 * ζ.im := by
    have := Complex.norm_le_abs_re_add_abs_im (1 - ζ)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at this
    linarith
  have h1ζ_ratio : ‖1 - ζ‖ / ‖1 - t‖ ≤ 2 := by
    have h1t_ge : ζ.im ≤ ‖1 - t‖ := by
      have h : |t.im| ≤ ‖1 - t‖ := by simpa using Complex.abs_im_le_norm (1 - t)
      rw [ht_im, abs_of_nonneg (by linarith)] at h; linarith
    rw [div_le_iff₀ (by linarith)]; linarith
  have hcp_ratio : ‖(1 - t) ^ (-(1 / 2 : ℂ))‖ ≤ 2 * ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ := by
    have hneg_half : -(1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hneg_half, Complex.norm_cpow_real, Complex.norm_cpow_real,
      Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    have h4 : (‖1 - ζ‖ / ‖1 - t‖) ^ (1 / 2 : ℝ) ≤ 2 := by
      calc (‖1 - ζ‖ / ‖1 - t‖) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) h1ζ_ratio (by norm_num)
        _ ≤ (4 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = 2 := by norm_num
    have h1ζ_pos : 0 < ‖1 - ζ‖ := norm_pos_iff.mpr fun he => by
      have := congr_arg Complex.re he; simp at this; linarith
    rw [Real.div_rpow (norm_nonneg _) (norm_nonneg _), div_le_iff₀ (by positivity)] at h4
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = ‖1 - ζ‖ ^ (1 / 2 : ℝ) * (‖1 - ζ‖ ^ (1 / 2 : ℝ))⁻¹ := (mul_inv_cancel₀ (by positivity)).symm
      _ ≤ (2 * ‖1 - t‖ ^ (1 / 2 : ℝ)) * (‖1 - ζ‖ ^ (1 / 2 : ℝ))⁻¹ := by gcongr
      _ = 2 * (‖1 - ζ‖ ^ (1 / 2 : ℝ))⁻¹ * ‖1 - t‖ ^ (1 / 2 : ℝ) := by ring
  have hB_ratio : ‖Complex.exp (binetDiff c t)‖ ≤ Real.exp (1 / 2) * ‖Complex.exp (binetDiff c ζ)‖ := by
    have hbw : ‖binetDiff c t‖ ≤ 1 / 4 := by
      have hb := binetDiff_norm_le hcpos (by rw [ht_re]; linarith : t.re < 1)
      have h1' : 1 / (1 - t.re) ≤ 2 := by rw [div_le_iff₀ (by rw [ht_re]; linarith), ht_re]; linarith
      calc ‖binetDiff c t‖ ≤ 1 / (12 * c) * (2 + 1) := hb.trans (by gcongr)
        _ ≤ 1 / (12 * 1) * (2 + 1) := by gcongr
        _ = 1 / 4 := by norm_num
    have hbz : ‖binetDiff c ζ‖ ≤ 1 / 4 := by
      have hb := binetDiff_norm_le hcpos (by linarith : ζ.re < 1)
      have h1' : 1 / (1 - ζ.re) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      calc ‖binetDiff c ζ‖ ≤ 1 / (12 * c) * (2 + 1) := hb.trans (by gcongr)
        _ ≤ 1 / (12 * 1) * (2 + 1) := by gcongr
        _ = 1 / 4 := by norm_num
    rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp ((Complex.abs_re_le_norm _).trans hbw)).2,
      (abs_le.mp ((Complex.abs_re_le_norm _).trans hbz)).1])
  have hD_ratio : ‖fctDcompAt K4 c (fctWarpAlpha h ε c) t‖ ≤
      Real.exp (2 * |B_D 0|) * ‖fctDcompAt K4 c (fctWarpAlpha h ε c) ζ‖ := by
    obtain ⟨v, -, -, -, hvB, hvD⟩ := hD_data ε c hε (hc.trans' ((le_max_right _ _).trans (le_max_left _ _)))
    have hDt : fctDcompAt K4 c (fctWarpAlpha h ε c) t = Complex.exp (FctCompD.stripCompGExt v t) := hvD t
    have hDζ : fctDcompAt K4 c (fctWarpAlpha h ε c) ζ = Complex.exp (FctCompD.stripCompGExt v ζ) := hvD ζ
    have hgt := hvB 0 (by omega) t ht_cl
    have hgζ := hvB 0 (by omega) ζ hζ_cl
    simp only [iteratedDeriv_zero] at hgt hgζ
    rw [show fctDcompAt K4 c (fctWarpAlpha h ε c) t = Complex.exp (FctCompD.stripCompGExt v t) from hDt,
      show fctDcompAt K4 c (fctWarpAlpha h ε c) ζ = Complex.exp (FctCompD.stripCompGExt v ζ) from hDζ,
      Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by
      have h1' := (abs_le.mp ((Complex.abs_re_le_norm (FctCompD.stripCompGExt v t)).trans hgt)).2
      have h2' := (abs_le.mp ((Complex.abs_re_le_norm (FctCompD.stripCompGExt v ζ)).trans hgζ)).1
      linarith [le_abs_self (B_D 0)])
  have htan_bd : ‖stripG t + (fctWarpL1 h ε c : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t‖ ≤
      C_tan * (1 + ζ.im + s) := by
    have hgt := hCg t (by rw [abs_le, ht_re]; constructor <;> linarith) (by linarith)
    have hpk0 := hCpk (a := c ^ (-(1 / 12 : ℝ))) (Real.rpow_pos_of_pos hcpos _) (by rw [ht_re]; exact h0)
    have hpk : ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t‖ ≤ Cpk := by
      simpa only [FctPhiKill.phiKill] using hpk0.trans (mul_le_of_le_one_right hCpk0 (min_le_right _ _))
    have hgt' : ‖stripG t‖ ≤ Cg * (1 + ζ.im + s) := by
      simpa [ht_im, abs_of_nonneg (by linarith : 0 ≤ ζ.im + s), add_assoc] using hgt
    have h1y : (1 : ℝ) ≤ 1 + ζ.im + s := by linarith
    calc ‖stripG t + (fctWarpL1 h ε c : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t‖
        ≤ ‖stripG t‖ + |fctWarpL1 h ε c| * ‖FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t‖ := by
          simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
            norm_add_le (stripG t) ((fctWarpL1 h ε c : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t)
      _ ≤ Cg * (1 + ζ.im + s) + |CL1| * Cpk * (1 + ζ.im + s) := by
          have h12 := mul_le_mul hL1_le hpk (norm_nonneg _) (abs_nonneg _)
          have h3 : |CL1| * Cpk ≤ |CL1| * Cpk * (1 + ζ.im + s) :=
            le_mul_of_one_le_right (by positivity) h1y
          linarith
      _ = C_tan * (1 + ζ.im + s) := by simp only [C_tan]; ring
  have hHG_ratio : ‖ctHG ε t‖ ≤ (CHG / cHG) * 12 * Real.exp (-2 * s) * ‖ctHG ε ζ‖ := by
    have htb := (hHG_left ε t ht_cl (by rw [ht_re]; linarith) him_t).2
    have hζb := (hHG_left ε ζ hζ_cl (by linarith) him_ζ).1
    have hpoly : 1 + |t.im| ≤ (1 + |ζ.im|) * (2 + s) := by
      rw [ht_im, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; nlinarith
    have hexp_im : Real.exp (-(π * |t.im|)) ≤ Real.exp (-(π * s)) * Real.exp (-(π * |ζ.im|)) := by
      rw [← Real.exp_add, ht_im, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      exact Real.exp_le_exp.mpr (by linarith)
    have h1y_pos : 0 < 1 + |ζ.im| := by linarith [abs_nonneg ζ.im]
    have hpe : (2 + s) * Real.exp (-(π - 2) * s) ≤ 12 := by
      have h1' : -(π - 2) * s ≤ -(π - 3) * s := by linarith
      calc (2 + s) * Real.exp (-(π - 2) * s) ≤ (2 + s) * Real.exp (-(π - 3) * s) := by gcongr
        _ ≤ 12 := poly_exp_decay_bound hs
    have hexp_split : Real.exp (-(π * s)) = Real.exp (-(π - 2) * s) * Real.exp (-2 * s) := by
      rw [← Real.exp_add]; congr 1; ring
    have hrat : (1 + |t.im|) * Real.exp (-(π * |t.im|)) ≤
        12 * Real.exp (-2 * s) * ((1 + |ζ.im|) * Real.exp (-(π * |ζ.im|))) := by
      have hm1 := mul_le_mul hpoly hexp_im (by positivity) (by positivity)
      have hm2 : ((2 + s) * Real.exp (-(π - 2) * s)) * Real.exp (-2 * s) *
          ((1 + |ζ.im|) * Real.exp (-(π * |ζ.im|))) ≤
          12 * Real.exp (-2 * s) * ((1 + |ζ.im|) * Real.exp (-(π * |ζ.im|))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpe (Real.exp_pos _).le) (by positivity)
      have heq1 : ((1 + |ζ.im|) * (2 + s)) * (Real.exp (-(π * s)) * Real.exp (-(π * |ζ.im|))) =
          ((2 + s) * Real.exp (-(π - 2) * s)) * Real.exp (-2 * s) * ((1 + |ζ.im|) * Real.exp (-(π * |ζ.im|))) := by
        rw [hexp_split]; ring
      linarith [hm1, hm2, heq1]
    calc ‖ctHG ε t‖ ≤ CHG * ((1 + |t.im|) * Real.exp (-(π * |t.im|))) := by linarith
      _ ≤ CHG * (12 * Real.exp (-2 * s) * ((1 + |ζ.im|) * Real.exp (-(π * |ζ.im|)))) :=
          mul_le_mul_of_nonneg_left hrat hCHG.le
      _ = (CHG / cHG) * 12 * Real.exp (-2 * s) * (cHG * (1 + |ζ.im|) * Real.exp (-(π * |ζ.im|))) := by
          field_simp [hcHG.ne']
      _ ≤ (CHG / cHG) * 12 * Real.exp (-2 * s) * ‖ctHG ε ζ‖ :=
          mul_le_mul_of_nonneg_left hζb (by positivity)
  change ‖(1 - t) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c t) * fctRayE c (fctWarpL1 h ε c) t *
      ((stripG t + (fctWarpL1 h ε c : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t) *
        fctDcompAt K4 c (fctWarpAlpha h ε c) t * ctHG ε t)‖ ≤
    C_l * (1 + ζ.im + s) * Real.exp (-2 * s) *
      ‖(1 - ζ) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c ζ) * fctRayE c (fctWarpL1 h ε c) ζ *
        fctDcompAt K4 c (fctWarpAlpha h ε c) ζ * ctHG ε ζ‖
  simp only [norm_mul]
  calc ‖(1 - t) ^ (-(1 / 2 : ℂ))‖ * ‖Complex.exp (binetDiff c t)‖ * ‖fctRayE c (fctWarpL1 h ε c) t‖ *
        (‖stripG t + (fctWarpL1 h ε c : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t‖ *
          ‖fctDcompAt K4 c (fctWarpAlpha h ε c) t‖ * ‖ctHG ε t‖)
      ≤ (2 * ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖) * (Real.exp (1 / 2) * ‖Complex.exp (binetDiff c ζ)‖) *
          ‖fctRayE c (fctWarpL1 h ε c) ζ‖ *
          ((C_tan * (1 + ζ.im + s)) * (Real.exp (2 * |B_D 0|) * ‖fctDcompAt K4 c (fctWarpAlpha h ε c) ζ‖) *
            ((CHG / cHG) * 12 * Real.exp (-2 * s) * ‖ctHG ε ζ‖)) :=
          mul_le_mul
            (mul_le_mul (mul_le_mul hcp_ratio hB_ratio (by positivity) (by positivity))
              hE_le (by positivity) (by positivity))
            (mul_le_mul (mul_le_mul htan_bd hD_ratio (by positivity) (by positivity))
              hHG_ratio (by positivity) (by positivity))
            (by positivity) (by positivity)
    _ = C_l * (1 + ζ.im + s) * Real.exp (-2 * s) *
          (‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ * ‖Complex.exp (binetDiff c ζ)‖ * ‖fctRayE c (fctWarpL1 h ε c) ζ‖ *
            ‖fctDcompAt K4 c (fctWarpAlpha h ε c) ζ‖ * ‖ctHG ε ζ‖) := by
        simp only [C_l]; ring

/-- info: 'FormalResearch.SignUncertainty.fctRayW_interior_derivs_and_near_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctRayW_interior_derivs_and_near_one

/-- info: 'FormalResearch.SignUncertainty.fctWarpKA_left_ray_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpKA_left_ray_bound

end FormalResearch.SignUncertainty
