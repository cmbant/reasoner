/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_1
public import FormalResearch.ModularBootstrap.Spin.SpinS4_3_3_Cap
public import FormalResearch.ModularBootstrap.PoissonJensen.LemmaPJAssembly
public import Mathlib.Analysis.Complex.Liouville

/-!
# Section 4.2 Strip Helpers (`s4:4.2`): Holomorphy, Polynomial Strip Bound, and Slit `L¹` Bound

Supporting lemmas for `SpinS4_4_2` (`Spin/SpinS4_4_2.lean`):
1. `norm_deriv_spinWa_strip`: Cauchy derivative bound for `spinWa a r` on `{|Im w| ≤ θ}` (`θ < 1/2`).
2. `spinQSlice_differentiableOn`: complex analyticity of `spinQSlice c N Φ χ` on `{|Im b| < γ_N / 2}`.
3. `spinHProfile_differentiableOn`: complex analyticity of `spinHProfile c N Φ χ` on `closedBall 0 R`
   once `c` is large enough that `ε * (R + 1) < γ_N / 2`.
4. `spinQSlice_rescaled_strip_bound` and `spinQSlice_rescaled_slit_bound`: polynomial boundary bound on
   `{|Im b'| ≤ 1/2}` and uniform `L¹` bound on the real slits `{|b'| ≥ ξ_*}` after rescaling
   `b = γ_N b'`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real

private lemma norm_deriv_spinWa_strip {a θ : ℝ} (ha : 2 ≤ a) (_hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (r : ℝ) {w : ℂ} (hw : |w.im| ≤ θ) :
    ‖deriv (spinWa a r) w‖ ≤
      ((1 + 4 * (|w.re| + (1 / 2 - θ) / 2) ^ 2) / ((1 / 2 - θ) / 2)) * spinV1 a r := by
  let rw : ℝ := (1 / 2 - θ) / 2
  have hrw_pos : 0 < rw := by dsimp [rw]; linarith
  have hdiff : DiffContOnCl ℂ (spinWa a r) (Metric.ball w rw) := by
    have hd : Differentiable ℂ (spinWa a r) := by unfold spinWa; fun_prop
    exact hd.differentiableOn.diffContOnCl
  have hbd : ∀ z ∈ Metric.sphere w rw,
      ‖spinWa a r z‖ ≤ (1 + 4 * (|w.re| + rw) ^ 2) * spinV1 a r := by
    intro z hz
    have hdist : ‖z - w‖ = rw := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
    have hzim : |z.im| ≤ 1 / 2 := by
      have h1 : |z.im - w.im| ≤ rw := by
        rw [← Complex.sub_im, ← hdist]; exact Complex.abs_im_le_norm (z - w)
      have h2 := abs_sub_abs_le_abs_sub z.im w.im
      dsimp [rw] at h1
      linarith only [h1, h2, hw, hθ]
    have hzre : |z.re| ≤ |w.re| + rw := by
      have h1 : |z.re - w.re| ≤ rw := by
        rw [← Complex.sub_re, ← hdist]; exact Complex.abs_re_le_norm (z - w)
      have h2 := abs_sub_abs_le_abs_sub z.re w.re
      linarith only [h1, h2]
    have hsq : z.re ^ 2 ≤ (|w.re| + rw) ^ 2 := by
      rw [← sq_abs z.re]
      exact pow_le_pow_left₀ (abs_nonneg _) hzre 2
    have hwa := norm_spinWa_le ha r hzim
    have hv1 := spinV1_nonneg ha r
    refine hwa.trans ?_
    gcongr
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrw_pos hdiff hbd
  refine hder.trans_eq ?_
  dsimp [rw]; ring

private lemma continuousAt_spinDaC_diag_d {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (c₁ c₂ : ℝ) (b : ℂ)
    (hb1 : |c₁ * b.im| ≤ 1 / 2) (hb2 : |c₂ * b.im| ≤ 1 / 2) (d₀ : ℝ) :
    ContinuousAt (fun d : ℝ =>
      spinDaC a Φ ((c₁ : ℂ) * (b + (d : ℂ))) ((c₂ : ℂ) * (b - (d : ℂ)))) d₀ := by
  let R_re : ℝ := |c₁| * (|b.re| + |d₀| + 1) + |c₂| * (|b.re| + |d₀| + 1)
  let C_bd : ℝ := (1 + 4 * R_re ^ 2) ^ 2
  let F : ℝ → ℝ × ℝ → ℂ := fun d p =>
    (Φ p : ℂ) * spinWa a p.1 ((c₁ : ℂ) * (b + (d : ℂ))) * spinWa a p.2 ((c₂ : ℂ) * (b - (d : ℂ)))
  have hF_meas : ∀ᶠ d in 𝓝 d₀, AEStronglyMeasurable (F d) volume :=
    Eventually.of_forall fun d => by
      have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
      have h2 : Continuous (fun p : ℝ × ℝ => spinWa a p.1 ((c₁ : ℂ) * (b + (d : ℂ)))) := by
        unfold spinWa; fun_prop
      have h3 : Continuous (fun p : ℝ × ℝ => spinWa a p.2 ((c₂ : ℂ) * (b - (d : ℂ)))) := by
        unfold spinWa; fun_prop
      exact ((h1.mul h2).mul h3).aestronglyMeasurable
  have hF_bd : ∀ᶠ d in 𝓝 d₀, ∀ᵐ p : ℝ × ℝ ∂volume,
      ‖F d p‖ ≤ C_bd * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
    filter_upwards [Metric.ball_mem_nhds d₀ zero_lt_one] with d hd
    refine Eventually.of_forall fun p => ?_
    have hd_abs : |d| ≤ |d₀| + 1 := by
      have h1 : |d - d₀| < 1 := by simpa [Real.dist_eq] using Metric.mem_ball.mp hd
      linarith [abs_sub_abs_le_abs_sub d d₀]
    have him1 : |((c₁ : ℂ) * (b + (d : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.im_ofReal_mul, Complex.add_im, Complex.ofReal_im, add_zero]
      exact hb1
    have him2 : |((c₂ : ℂ) * (b - (d : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.im_ofReal_mul, Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact hb2
    have hre1 : |((c₁ : ℂ) * (b + (d : ℂ))).re| ≤ R_re := by
      rw [Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re, abs_mul]
      calc |c₁| * |b.re + d| ≤ |c₁| * (|b.re| + |d|) := by
            gcongr; exact abs_add_le _ _
        _ ≤ |c₁| * (|b.re| + (|d₀| + 1)) := by gcongr
        _ ≤ R_re := by dsimp [R_re]; linarith [mul_nonneg (abs_nonneg c₂) (by positivity : 0 ≤ |b.re| + |d₀| + 1)]
    have hre2 : |((c₂ : ℂ) * (b - (d : ℂ))).re| ≤ R_re := by
      rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re, abs_mul]
      calc |c₂| * |b.re - d| ≤ |c₂| * (|b.re| + |d|) := by
            gcongr; exact abs_sub _ _
        _ ≤ |c₂| * (|b.re| + (|d₀| + 1)) := by gcongr
        _ ≤ R_re := by dsimp [R_re]; linarith [mul_nonneg (abs_nonneg c₁) (by positivity : 0 ≤ |b.re| + |d₀| + 1)]
    have h1 := norm_spinWa_le ha p.1 him1
    have h2 := norm_spinWa_le ha p.2 him2
    have hsq1 : ((c₁ : ℂ) * (b + (d : ℂ))).re ^ 2 ≤ R_re ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre1 2
    have hsq2 : ((c₂ : ℂ) * (b - (d : ℂ))).re ^ 2 ≤ R_re ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre2 2
    have h1' : ‖spinWa a p.1 ((c₁ : ℂ) * (b + (d : ℂ)))‖ ≤ (1 + 4 * R_re ^ 2) * spinV1 a p.1 := by
      refine h1.trans ?_; have := spinV1_nonneg ha p.1; gcongr
    have h2' : ‖spinWa a p.2 ((c₂ : ℂ) * (b - (d : ℂ)))‖ ≤ (1 + 4 * R_re ^ 2) * spinV1 a p.2 := by
      refine h2.trans ?_; have := spinV1_nonneg ha p.2; gcongr
    dsimp [F, C_bd]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hprod := mul_le_mul h1' h2' (norm_nonneg _)
      (mul_nonneg (by positivity) (spinV1_nonneg ha p.1))
    calc |Φ p| * ‖spinWa a p.1 ((c₁ : ℂ) * (b + (d : ℂ)))‖ * ‖spinWa a p.2 ((c₂ : ℂ) * (b - (d : ℂ)))‖
        = |Φ p| * (‖spinWa a p.1 ((c₁ : ℂ) * (b + (d : ℂ)))‖ * ‖spinWa a p.2 ((c₂ : ℂ) * (b - (d : ℂ)))‖) := by ring
      _ ≤ |Φ p| * (((1 + 4 * R_re ^ 2) * spinV1 a p.1) * ((1 + 4 * R_re ^ 2) * spinV1 a p.2)) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ = (1 + 4 * R_re ^ 2) ^ 2 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by ring
  have hF_cont : ∀ᵐ p : ℝ × ℝ ∂volume, ContinuousAt (fun d : ℝ => F d p) d₀ :=
    Eventually.of_forall fun p => by
      dsimp [F]
      have h1 : Continuous (fun d : ℝ => spinWa a p.1 ((c₁ : ℂ) * (b + (d : ℂ)))) := by
        unfold spinWa; fun_prop
      have h2 : Continuous (fun d : ℝ => spinWa a p.2 ((c₂ : ℂ) * (b - (d : ℂ)))) := by
        unfold spinWa; fun_prop
      exact ((continuous_const.mul h1).mul h2).continuousAt
  have hint_c := continuousAt_of_dominated hF_meas hF_bd (hΦ.int_M2.const_mul C_bd) hF_cont
  have heq : (fun d : ℝ => spinDaC a Φ ((c₁ : ℂ) * (b + (d : ℂ))) ((c₂ : ℂ) * (b - (d : ℂ)))) =
      fun d : ℝ => -(∫ p : ℝ × ℝ, F d p) := by
    ext d; rw [spinDaC_eq_spinWa]
  rw [heq]
  exact hint_c.neg

private lemma hasDerivAt_spinDaC_diag_and_bound {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {c₁ c₂ : ℝ} (hc1 : 0 < c₁) (hc2 : 0 < c₂)
    {b₀ : ℂ} (hb1 : c₁ * |b₀.im| < 1 / 2) (hb2 : c₂ * |b₀.im| < 1 / 2) (V_bd : ℝ) (hV0 : 0 ≤ V_bd) :
    ∃ (r_b M_bd : ℝ), 0 < r_b ∧ 0 ≤ M_bd ∧
      ∀ d : ℝ, |d| ≤ V_bd → ∀ b ∈ Metric.ball b₀ r_b,
        DifferentiableAt ℂ (fun z =>
          spinDaC a Φ ((c₁ : ℂ) * (z + (d : ℂ))) ((c₂ : ℂ) * (z - (d : ℂ)))) b ∧
        ‖deriv (fun z =>
          spinDaC a Φ ((c₁ : ℂ) * (z + (d : ℂ))) ((c₂ : ℂ) * (z - (d : ℂ)))) b‖ ≤ M_bd := by
  let r_b : ℝ := min ((1 / 2 - c₁ * |b₀.im|) / (2 * c₁)) ((1 / 2 - c₂ * |b₀.im|) / (2 * c₂))
  have hrb_pos : 0 < r_b := by
    dsimp [r_b]; exact lt_min (div_pos (by linarith) (by linarith)) (div_pos (by linarith) (by linarith))
  let θ₁ : ℝ := c₁ * (|b₀.im| + r_b)
  let θ₂ : ℝ := c₂ * (|b₀.im| + r_b)
  have hθ1_0 : 0 ≤ θ₁ := by positivity
  have hθ2_0 : 0 ≤ θ₂ := by positivity
  have hθ1_lt : θ₁ < 1 / 2 := by
    have h1 : r_b ≤ (1 / 2 - c₁ * |b₀.im|) / (2 * c₁) := min_le_left _ _
    have h2 : r_b * (2 * c₁) ≤ 1 / 2 - c₁ * |b₀.im| := (le_div_iff₀ (by positivity)).mp h1
    dsimp [θ₁]
    nlinarith [mul_pos hc1 hrb_pos]
  have hθ2_lt : θ₂ < 1 / 2 := by
    have h1 : r_b ≤ (1 / 2 - c₂ * |b₀.im|) / (2 * c₂) := min_le_right _ _
    have h2 : r_b * (2 * c₂) ≤ 1 / 2 - c₂ * |b₀.im| := (le_div_iff₀ (by positivity)).mp h1
    dsimp [θ₂]
    nlinarith [mul_pos hc2 hrb_pos]
  let θ : ℝ := max θ₁ θ₂
  have hθ0 : 0 ≤ θ := le_trans hθ1_0 (le_max_left _ _)
  have hθ_lt : θ < 1 / 2 := max_lt hθ1_lt hθ2_lt
  let r_w : ℝ := (1 / 2 - θ) / 2
  have hrw_pos : 0 < r_w := by dsimp [r_w]; linarith
  let R_re : ℝ := max c₁ c₂ * (|b₀.re| + r_b + V_bd)
  have hRre0 : 0 ≤ R_re := by positivity
  let D_bd : ℝ := ((1 + 4 * (R_re + r_w) ^ 2) / r_w) * max c₁ c₂
  let W_bd : ℝ := 1 + 4 * R_re ^ 2
  let C_bd : ℝ := 2 * D_bd * W_bd
  have hCbd0 : 0 ≤ C_bd := by positivity
  let M_bd : ℝ := C_bd * spinM2 a Φ
  have hMbd0 : 0 ≤ M_bd := mul_nonneg hCbd0 (spinM2_nonneg (by linarith) Φ)
  refine ⟨r_b, M_bd, hrb_pos, hMbd0, ?_⟩
  intro d hd b hb_ball
  have hb_dist : ‖b - b₀‖ < r_b := by simpa [dist_eq_norm] using Metric.mem_ball.mp hb_ball
  have hrim : ∀ z ∈ Metric.ball b₀ r_b, |z.im| ≤ |b₀.im| + r_b := fun z hz => by
    have h1 : |z.im - b₀.im| < r_b := by
      rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hz)
    linarith [abs_sub_abs_le_abs_sub z.im b₀.im]
  have hrre : ∀ z ∈ Metric.ball b₀ r_b, |z.re| ≤ |b₀.re| + r_b := fun z hz => by
    have h1 : |z.re - b₀.re| < r_b := by
      rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hz)
    linarith [abs_sub_abs_le_abs_sub z.re b₀.re]
  let F : ℂ → ℝ × ℝ → ℂ := fun z p =>
    (Φ p : ℂ) * spinWa a p.1 ((c₁ : ℂ) * (z + (d : ℂ))) * spinWa a p.2 ((c₂ : ℂ) * (z - (d : ℂ)))
  let F' : ℂ → ℝ × ℝ → ℂ := fun z p =>
    (Φ p : ℂ) *
      ((deriv (spinWa a p.1) ((c₁ : ℂ) * (z + (d : ℂ))) * (c₁ : ℂ)) *
          spinWa a p.2 ((c₂ : ℂ) * (z - (d : ℂ))) +
        spinWa a p.1 ((c₁ : ℂ) * (z + (d : ℂ))) *
          (deriv (spinWa a p.2) ((c₂ : ℂ) * (z - (d : ℂ))) * (c₂ : ℂ)))
  have hw_im : ∀ z ∈ Metric.ball b₀ r_b,
      |((c₁ : ℂ) * (z + (d : ℂ))).im| ≤ θ ∧ |((c₂ : ℂ) * (z - (d : ℂ))).im| ≤ θ := fun z hz => by
    have him := hrim z hz
    rw [Complex.im_ofReal_mul, Complex.add_im, Complex.ofReal_im, add_zero, abs_mul, abs_of_pos hc1,
      Complex.im_ofReal_mul, Complex.sub_im, Complex.ofReal_im, sub_zero, abs_mul, abs_of_pos hc2]
    exact ⟨(mul_le_mul_of_nonneg_left him hc1.le).trans (le_max_left _ _),
      (mul_le_mul_of_nonneg_left him hc2.le).trans (le_max_right _ _)⟩
  have hw_re : ∀ z ∈ Metric.ball b₀ r_b,
      |((c₁ : ℂ) * (z + (d : ℂ))).re| ≤ R_re ∧ |((c₂ : ℂ) * (z - (d : ℂ))).re| ≤ R_re := fun z hz => by
    have hre := hrre z hz
    rw [Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re, abs_mul, abs_of_pos hc1,
      Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re, abs_mul, abs_of_pos hc2]
    have h1 : |z.re + d| ≤ |b₀.re| + r_b + V_bd := (abs_add_le _ _).trans (by linarith)
    have h2 : |z.re - d| ≤ |b₀.re| + r_b + V_bd := (abs_sub _ _).trans (by linarith)
    exact ⟨mul_le_mul (le_max_left _ _) h1 (abs_nonneg _) (by positivity),
      mul_le_mul (le_max_right _ _) h2 (abs_nonneg _) (by positivity)⟩
  have hF_meas : ∀ᶠ z in 𝓝 b, AEStronglyMeasurable (F z) volume :=
    Eventually.of_forall fun z => by
      have hc1' : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
      have hc2' : Continuous (fun p : ℝ × ℝ => spinWa a p.1 ((c₁ : ℂ) * (z + (d : ℂ)))) := by
        unfold spinWa; fun_prop
      have hc3' : Continuous (fun p : ℝ × ℝ => spinWa a p.2 ((c₂ : ℂ) * (z - (d : ℂ)))) := by
        unfold spinWa; fun_prop
      exact ((hc1'.mul hc2').mul hc3').aestronglyMeasurable
  have hF_int : Integrable (F b) volume := by
    have hpt : ∀ p : ℝ × ℝ, ‖F b p‖ ≤ W_bd ^ 2 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := fun p => by
      obtain ⟨hi1, hi2⟩ := hw_im b hb_ball
      obtain ⟨hr1, hr2⟩ := hw_re b hb_ball
      have h1 := norm_spinWa_le ha p.1 (hi1.trans hθ_lt.le)
      have h2 := norm_spinWa_le ha p.2 (hi2.trans hθ_lt.le)
      have hs1 : ((c₁ : ℂ) * (b + (d : ℂ))).re ^ 2 ≤ R_re ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr1 2
      have hs2 : ((c₂ : ℂ) * (b - (d : ℂ))).re ^ 2 ≤ R_re ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr2 2
      have h1' : ‖spinWa a p.1 ((c₁ : ℂ) * (b + (d : ℂ)))‖ ≤ W_bd * spinV1 a p.1 := by
        refine h1.trans ?_; have := spinV1_nonneg ha p.1; dsimp [W_bd]; gcongr
      have h2' : ‖spinWa a p.2 ((c₂ : ℂ) * (b - (d : ℂ)))‖ ≤ W_bd * spinV1 a p.2 := by
        refine h2.trans ?_; have := spinV1_nonneg ha p.2; dsimp [W_bd]; gcongr
      dsimp [F]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hprod := mul_le_mul h1' h2' (norm_nonneg _) (mul_nonneg (by dsimp [W_bd]; positivity) (spinV1_nonneg ha p.1))
      calc |Φ p| * ‖spinWa a p.1 ((c₁ : ℂ) * (b + (d : ℂ)))‖ * ‖spinWa a p.2 ((c₂ : ℂ) * (b - (d : ℂ)))‖
          = |Φ p| * (‖spinWa a p.1 ((c₁ : ℂ) * (b + (d : ℂ)))‖ * ‖spinWa a p.2 ((c₂ : ℂ) * (b - (d : ℂ)))‖) := by ring
        _ ≤ |Φ p| * ((W_bd * spinV1 a p.1) * (W_bd * spinV1 a p.2)) :=
            mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
        _ = W_bd ^ 2 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by ring
    exact (hΦ.int_M2.const_mul (W_bd ^ 2)).mono' hF_meas.self_of_nhds (Eventually.of_forall hpt)
  have hF'_meas : AEStronglyMeasurable (F' b) volume := by
    let df : ℝ → ℂ → ℂ := fun r z =>
      -4 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) *
          Complex.cos (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * z) *
          Complex.sin (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * z) -
       4 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) *
          Complex.sin (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * z) *
          Complex.cos (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * z)
    have hdf_eq : ∀ r z, deriv (spinWa a r) z = df r z := fun r z => by
      have heq : spinWa a r = fun w : ℂ =>
          -2 * Complex.sin (2 * ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ) * w) *
            Complex.sin (2 * ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ) * w) := by
        ext w; unfold spinWa
        have h1 : Complex.cos (4 * (π : ℂ) * (Real.sqrt a : ℂ) * (r : ℂ) * w) -
            Complex.cos (4 * (π : ℂ) * (Real.sqrt (a - 2) : ℂ) * (r : ℂ) * w) =
            -2 * Complex.sin ((4 * (π : ℂ) * (Real.sqrt a : ℂ) * (r : ℂ) * w +
              4 * (π : ℂ) * (Real.sqrt (a - 2) : ℂ) * (r : ℂ) * w) / 2) *
            Complex.sin ((4 * (π : ℂ) * (Real.sqrt a : ℂ) * (r : ℂ) * w -
              4 * (π : ℂ) * (Real.sqrt (a - 2) : ℂ) * (r : ℂ) * w) / 2) :=
          Complex.cos_sub_cos _ _
        rw [h1]; congr 2
        · congr 1; push_cast; ring
        · congr 1; push_cast; ring
      rw [heq]
      set U : ℂ := ((π * r * (Real.sqrt a + Real.sqrt (a - 2)) : ℝ) : ℂ)
      set V : ℂ := ((π * r * (Real.sqrt a - Real.sqrt (a - 2)) : ℝ) : ℂ)
      have h1 : HasDerivAt (fun w => Complex.sin (2 * U * w)) (Complex.cos (2 * U * z) * (2 * U)) z := by
        simpa [Function.comp_def] using (Complex.hasDerivAt_sin (2 * U * z)).comp z
          ((hasDerivAt_id z).const_mul (2 * U))
      have h2 : HasDerivAt (fun w => Complex.sin (2 * V * w)) (Complex.cos (2 * V * z) * (2 * V)) z := by
        simpa [Function.comp_def] using (Complex.hasDerivAt_sin (2 * V * z)).comp z
          ((hasDerivAt_id z).const_mul (2 * V))
      have hprod := (h1.const_mul (-2 : ℂ)).fun_mul h2
      rw [hprod.deriv]; dsimp [df]; ring
    have heq' : F' b = fun p : ℝ × ℝ =>
        (Φ p : ℂ) *
          ((df p.1 ((c₁ : ℂ) * (b + (d : ℂ))) * (c₁ : ℂ)) *
              spinWa a p.2 ((c₂ : ℂ) * (b - (d : ℂ))) +
            spinWa a p.1 ((c₁ : ℂ) * (b + (d : ℂ))) *
              (df p.2 ((c₂ : ℂ) * (b - (d : ℂ))) * (c₂ : ℂ))) := by
      ext p; simp only [F', hdf_eq]
    rw [heq']
    have hc1' : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
    have hw1 : Continuous (fun p : ℝ × ℝ => spinWa a p.1 ((c₁ : ℂ) * (b + (d : ℂ)))) := by
      unfold spinWa; fun_prop
    have hw2 : Continuous (fun p : ℝ × ℝ => spinWa a p.2 ((c₂ : ℂ) * (b - (d : ℂ)))) := by
      unfold spinWa; fun_prop
    have hd1 : Continuous (fun p : ℝ × ℝ => df p.1 ((c₁ : ℂ) * (b + (d : ℂ)))) := by
      dsimp [df]; fun_prop
    have hd2 : Continuous (fun p : ℝ × ℝ => df p.2 ((c₂ : ℂ) * (b - (d : ℂ)))) := by
      dsimp [df]; fun_prop
    exact (hc1'.mul (((hd1.mul continuous_const).mul hw2).add
      (hw1.mul (hd2.mul continuous_const)))).aestronglyMeasurable
  let εb : ℝ := r_b - ‖b - b₀‖
  have hεb_pos : 0 < εb := sub_pos.mpr hb_dist
  have hsub_ball : Metric.ball b εb ⊆ Metric.ball b₀ r_b := fun z hz => by
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    calc ‖z - b₀‖ = ‖(z - b) + (b - b₀)‖ := by ring_nf
      _ ≤ ‖z - b‖ + ‖b - b₀‖ := norm_add_le _ _
      _ < εb + ‖b - b₀‖ := by linarith
      _ = r_b := by dsimp [εb]; ring
  have hbound_pt : ∀ p : ℝ × ℝ, ∀ z ∈ Metric.ball b εb,
      ‖F' z p‖ ≤ C_bd * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
    intro p z hz
    have hz0 := hsub_ball hz
    obtain ⟨hi1, hi2⟩ := hw_im z hz0
    obtain ⟨hr1, hr2⟩ := hw_re z hz0
    have hd1 := norm_deriv_spinWa_strip ha hθ0 hθ_lt p.1 hi1
    have hd2 := norm_deriv_spinWa_strip ha hθ0 hθ_lt p.2 hi2
    have hd1' : ‖deriv (spinWa a p.1) ((c₁ : ℂ) * (z + (d : ℂ))) * (c₁ : ℂ)‖ ≤ D_bd * spinV1 a p.1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc1]
      have hsq : (|((c₁ : ℂ) * (z + (d : ℂ))).re| + r_w) ^ 2 ≤ (R_re + r_w) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (add_le_add hr1 le_rfl) 2
      have hnum : (1 + 4 * (|((c₁ : ℂ) * (z + (d : ℂ))).re| + r_w) ^ 2) / r_w * spinV1 a p.1 ≤
          ((1 + 4 * (R_re + r_w) ^ 2) / r_w) * spinV1 a p.1 := by
        have := spinV1_nonneg ha p.1; gcongr
      calc ‖deriv (spinWa a p.1) ((c₁ : ℂ) * (z + (d : ℂ)))‖ * c₁
          ≤ ((1 + 4 * (R_re + r_w) ^ 2) / r_w * spinV1 a p.1) * c₁ := by
            gcongr; exact hd1.trans hnum
        _ ≤ D_bd * spinV1 a p.1 := by
            dsimp [D_bd]; have := spinV1_nonneg ha p.1
            calc ((1 + 4 * (R_re + r_w) ^ 2) / r_w * spinV1 a p.1) * c₁
                = ((1 + 4 * (R_re + r_w) ^ 2) / r_w * c₁) * spinV1 a p.1 := by ring
              _ ≤ ((1 + 4 * (R_re + r_w) ^ 2) / r_w * max c₁ c₂) * spinV1 a p.1 := by gcongr; exact le_max_left _ _
    have hd2' : ‖deriv (spinWa a p.2) ((c₂ : ℂ) * (z - (d : ℂ))) * (c₂ : ℂ)‖ ≤ D_bd * spinV1 a p.2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc2]
      have hsq : (|((c₂ : ℂ) * (z - (d : ℂ))).re| + r_w) ^ 2 ≤ (R_re + r_w) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (add_le_add hr2 le_rfl) 2
      have hnum : (1 + 4 * (|((c₂ : ℂ) * (z - (d : ℂ))).re| + r_w) ^ 2) / r_w * spinV1 a p.2 ≤
          ((1 + 4 * (R_re + r_w) ^ 2) / r_w) * spinV1 a p.2 := by
        have := spinV1_nonneg ha p.2; gcongr
      calc ‖deriv (spinWa a p.2) ((c₂ : ℂ) * (z - (d : ℂ)))‖ * c₂
          ≤ ((1 + 4 * (R_re + r_w) ^ 2) / r_w * spinV1 a p.2) * c₂ := by
            gcongr; exact hd2.trans hnum
        _ ≤ D_bd * spinV1 a p.2 := by
            dsimp [D_bd]; have := spinV1_nonneg ha p.2
            calc ((1 + 4 * (R_re + r_w) ^ 2) / r_w * spinV1 a p.2) * c₂
                = ((1 + 4 * (R_re + r_w) ^ 2) / r_w * c₂) * spinV1 a p.2 := by ring
              _ ≤ ((1 + 4 * (R_re + r_w) ^ 2) / r_w * max c₁ c₂) * spinV1 a p.2 := by gcongr; exact le_max_right _ _
    have hw1 : ‖spinWa a p.1 ((c₁ : ℂ) * (z + (d : ℂ)))‖ ≤ W_bd * spinV1 a p.1 := by
      have hs : ((c₁ : ℂ) * (z + (d : ℂ))).re ^ 2 ≤ R_re ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr1 2
      have := spinV1_nonneg ha p.1
      refine (norm_spinWa_le ha p.1 (hi1.trans hθ_lt.le)).trans ?_; dsimp [W_bd]; gcongr
    have hw2 : ‖spinWa a p.2 ((c₂ : ℂ) * (z - (d : ℂ)))‖ ≤ W_bd * spinV1 a p.2 := by
      have hs : ((c₂ : ℂ) * (z - (d : ℂ))).re ^ 2 ≤ R_re ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr2 2
      have := spinV1_nonneg ha p.2
      refine (norm_spinWa_le ha p.2 (hi2.trans hθ_lt.le)).trans ?_; dsimp [W_bd]; gcongr
    have hv1 := spinV1_nonneg ha p.1
    have hv2 := spinV1_nonneg ha p.2
    have ht1 : ‖(deriv (spinWa a p.1) ((c₁ : ℂ) * (z + (d : ℂ))) * (c₁ : ℂ)) *
        spinWa a p.2 ((c₂ : ℂ) * (z - (d : ℂ)))‖ ≤ D_bd * W_bd * spinV1 a p.1 * spinV1 a p.2 := by
      rw [norm_mul]
      exact (mul_le_mul hd1' hw2 (norm_nonneg _) (by positivity)).trans_eq (by ring)
    have ht2 : ‖spinWa a p.1 ((c₁ : ℂ) * (z + (d : ℂ))) *
        (deriv (spinWa a p.2) ((c₂ : ℂ) * (z - (d : ℂ))) * (c₂ : ℂ))‖ ≤ D_bd * W_bd * spinV1 a p.1 * spinV1 a p.2 := by
      rw [norm_mul]
      exact (mul_le_mul hw1 hd2' (norm_nonneg _) (by positivity)).trans_eq (by ring)
    dsimp [F']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsum : ‖(deriv (spinWa a p.1) ((c₁ : ℂ) * (z + (d : ℂ))) * (c₁ : ℂ)) *
          spinWa a p.2 ((c₂ : ℂ) * (z - (d : ℂ))) +
        spinWa a p.1 ((c₁ : ℂ) * (z + (d : ℂ))) *
          (deriv (spinWa a p.2) ((c₂ : ℂ) * (z - (d : ℂ))) * (c₂ : ℂ))‖ ≤
        C_bd * spinV1 a p.1 * spinV1 a p.2 := by
      calc _ ≤ _ + _ := norm_add_le _ _
        _ ≤ D_bd * W_bd * spinV1 a p.1 * spinV1 a p.2 + D_bd * W_bd * spinV1 a p.1 * spinV1 a p.2 :=
            add_le_add ht1 ht2
        _ = C_bd * spinV1 a p.1 * spinV1 a p.2 := by dsimp [C_bd]; ring
    calc |Φ p| * _ ≤ |Φ p| * (C_bd * spinV1 a p.1 * spinV1 a p.2) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = C_bd * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by ring
  have hbound_le : ∀ᵐ p : ℝ × ℝ ∂volume, ∀ z ∈ Metric.ball b εb,
      ‖F' z p‖ ≤ C_bd * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) :=
    Eventually.of_forall hbound_pt
  have hderiv_pt : ∀ᵐ p : ℝ × ℝ ∂volume, ∀ z ∈ Metric.ball b εb, HasDerivAt (fun w => F w p) (F' z p) z := by
    refine Eventually.of_forall fun p z _ => ?_
    have hdiff_wa : Differentiable ℂ (spinWa a p.1) := by unfold spinWa; fun_prop
    have hdiff_wb : Differentiable ℂ (spinWa a p.2) := by unfold spinWa; fun_prop
    have hwa : HasDerivAt (fun w => spinWa a p.1 ((c₁ : ℂ) * (w + (d : ℂ))))
        (deriv (spinWa a p.1) ((c₁ : ℂ) * (z + (d : ℂ))) * (c₁ : ℂ)) z := by
      have ha1 := (hdiff_wa ((c₁ : ℂ) * (z + (d : ℂ)))).hasDerivAt
      have ha2 : HasDerivAt (fun w => (c₁ : ℂ) * (w + (d : ℂ))) (c₁ : ℂ) z := by
        simpa using ((hasDerivAt_id z).add_const (d : ℂ)).const_mul (c₁ : ℂ)
      exact ha1.comp z ha2
    have hwb : HasDerivAt (fun w => spinWa a p.2 ((c₂ : ℂ) * (w - (d : ℂ))))
        (deriv (spinWa a p.2) ((c₂ : ℂ) * (z - (d : ℂ))) * (c₂ : ℂ)) z := by
      have hb1' := (hdiff_wb ((c₂ : ℂ) * (z - (d : ℂ)))).hasDerivAt
      have hb2' : HasDerivAt (fun w => (c₂ : ℂ) * (w - (d : ℂ))) (c₂ : ℂ) z := by
        simpa using ((hasDerivAt_id z).sub_const (d : ℂ)).const_mul (c₂ : ℂ)
      exact hb1'.comp z hb2'
    exact ((hwa.const_mul (Φ p : ℂ)).mul hwb).congr_deriv (by dsimp [F']; ring)
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b hεb_pos)
    hF_meas hF_int hF'_meas hbound_le (hΦ.int_M2.const_mul C_bd) hderiv_pt).2
  have hneg : HasDerivAt (fun z => spinDaC a Φ ((c₁ : ℂ) * (z + (d : ℂ))) ((c₂ : ℂ) * (z - (d : ℂ))))
      (-(∫ p : ℝ × ℝ, F' b p)) b :=
    hres.neg.congr_of_eventuallyEq (Eventually.of_forall fun z =>
      spinDaC_eq_spinWa a Φ ((c₁ : ℂ) * (z + (d : ℂ))) ((c₂ : ℂ) * (z - (d : ℂ))))
  refine ⟨hneg.differentiableAt, ?_⟩
  rw [hneg.deriv, norm_neg]
  have hF'int : Integrable (F' b) volume :=
    (hΦ.int_M2.const_mul C_bd).mono' hF'_meas
      (Eventually.of_forall fun p => hbound_pt p b (Metric.mem_ball_self hεb_pos))
  calc ‖∫ p : ℝ × ℝ, F' b p‖ ≤ ∫ p : ℝ × ℝ, ‖F' b p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ × ℝ, C_bd * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) :=
        integral_mono hF'int.norm (hΦ.int_M2.const_mul C_bd)
          (fun p => hbound_pt p b (Metric.mem_ball_self hεb_pos))
    _ = C_bd * spinM2 a Φ := integral_const_mul _ _

private lemma continuous_sum_range_c {M : ℕ} (F : ℕ → ℝ → ℂ)
    (hF : ∀ j < M, Continuous (F j)) :
    Continuous (fun d : ℝ => ∑ j ∈ Finset.range M, F j d) := by
  induction M with
  | zero => simpa using continuous_const
  | succ k ih =>
    simp_rw [Finset.sum_range_succ]
    exact (ih fun j hj => hF j (Nat.lt_succ_of_lt hj)).add (hF k (Nat.lt_succ_self k))

lemma continuous_spinTruncInvC_d {c : ℝ} (hc : 49 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) {b : ℂ}
    (hb : |b.im| ≤ (spinGamma ((c - 1) / 12) *
      (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹) / 2) :
    let n := c - 1
    let a := n / 12
    let N := Nat.ceil (Real.log n)
    Continuous (fun d : ℝ => spinTruncInvC a N Φ (b + (d : ℂ)) (b - (d : ℂ))) := by
  intro n a N
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have hlam_gt1 : 1 < spinLambda a := spinLambda_gt_one_s4 ha2
  have hN_pos : 1 ≤ N := Nat.ceil_pos.mpr (Real.log_pos (by linarith))
  let γN : ℝ := spinGamma a * (spinLambda a ^ (N - 1))⁻¹
  have hglam : spinLambda a ^ N * γN = 1 := by
    have hN1 : N = (N - 1) + 1 := (Nat.sub_add_cancel hN_pos).symm
    dsimp [γN]
    nth_rw 1 [hN1]
    rw [pow_succ', mul_assoc, mul_left_comm (spinLambda a ^ (N - 1)) (spinGamma a)]
    calc spinLambda a * (spinGamma a * (spinLambda a ^ (N - 1) * (spinLambda a ^ (N - 1))⁻¹))
        = (spinGamma a * spinLambda a) * (spinLambda a ^ (N - 1) * (spinLambda a ^ (N - 1))⁻¹) := by ring
      _ = 1 * 1 := by
          rw [spinGamma_mul_spinLambda ha2, mul_inv_cancel₀ (pow_ne_zero _ (lt_trans zero_lt_one hlam_gt1).ne')]
      _ = 1 := one_mul 1
  have hc_le : ∀ m : ℕ, m < N → |spinLambda a ^ (m + 1) * b.im| ≤ 1 / 2 := fun m hm => by
    have hpow : spinLambda a ^ (m + 1) ≤ spinLambda a ^ N := pow_le_pow_right₀ hlam_gt1.le hm
    rw [abs_mul, abs_of_pos (pow_pos (lt_trans zero_lt_one hlam_gt1) _)]
    calc spinLambda a ^ (m + 1) * |b.im| ≤ spinLambda a ^ N * |b.im| :=
          mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
      _ ≤ spinLambda a ^ N * (γN / 2) :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg (lt_trans zero_lt_one hlam_gt1).le _)
      _ = (spinLambda a ^ N * γN) / 2 := by ring
      _ = 1 / 2 := by rw [hglam]
  unfold spinTruncInvC
  refine continuous_sum_range_c (M := N) _ fun j hjN => continuous_sum_range_c (M := N) _ fun ℓ hℓN => ?_
  have heq : (fun d : ℝ => spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * (b + (d : ℂ)))
        ((spinLambda a ^ ℓ : ℝ) * (b - (d : ℂ)))) =
      fun d : ℝ => spinDaC a Φ (((spinLambda a ^ (j + 1) : ℝ) : ℂ) * (b + (d : ℂ)))
        (((spinLambda a ^ (ℓ + 1) : ℝ) : ℂ) * (b - (d : ℂ))) := by
    ext d; unfold spinDeltaAC; rw [pow_succ', pow_succ']; push_cast; ring_nf
  rw [heq, continuous_iff_continuousAt]
  exact fun d₀ => continuousAt_spinDaC_diag_d ha2.le hΦ _ _ b (hc_le j hjN) (hc_le ℓ hℓN) d₀

lemma spinQSlice_differentiableOn {c V : ℝ} (hc : 49 ≤ c) (hV : 0 < V)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {χ : ℝ → ℝ} (hχ_meas : Measurable χ) (hχ_bd : ∀ v, 0 ≤ χ v ∧ χ v ≤ 1)
    (hχ_supp : ∀ v, V < |v| → χ v = 0) :
    let n := c - 1
    let a := n / 12
    let N := Nat.ceil (Real.log n)
    let γN := spinGamma a * (spinLambda a ^ (N - 1))⁻¹
    DifferentiableOn ℂ (spinQSlice c N Φ χ) {b : ℂ | |b.im| < γN / 2} := by
  intro n a N γN b₀ hb₀
  change |b₀.im| < γN / 2 at hb₀
  have hn48 : 48 ≤ n := by dsimp [n]; linarith
  have hn_pos : 0 < n := by linarith
  have ha2 : 2 < a := by dsimp [a]; linarith
  have hlam_gt1 : 1 < spinLambda a := spinLambda_gt_one_s4 ha2
  have hN_pos : 1 ≤ N := Nat.ceil_pos.mpr (Real.log_pos (by linarith))
  have hglam : spinLambda a ^ N * γN = 1 := by
    have hN1 : N = (N - 1) + 1 := (Nat.sub_add_cancel hN_pos).symm
    dsimp [γN]
    nth_rw 1 [hN1]
    rw [pow_succ', mul_assoc, mul_left_comm (spinLambda a ^ (N - 1)) (spinGamma a)]
    calc spinLambda a * (spinGamma a * (spinLambda a ^ (N - 1) * (spinLambda a ^ (N - 1))⁻¹))
        = (spinGamma a * spinLambda a) * (spinLambda a ^ (N - 1) * (spinLambda a ^ (N - 1))⁻¹) := by ring
      _ = 1 * 1 := by
          rw [spinGamma_mul_spinLambda ha2, mul_inv_cancel₀ (pow_ne_zero _ (lt_trans zero_lt_one hlam_gt1).ne')]
      _ = 1 := one_mul 1
  have hγN_pos : 0 < γN := by
    have := pow_pos (lt_trans zero_lt_one hlam_gt1) N
    nlinarith
  have hc_lt : ∀ j : ℕ, j < N → spinLambda a ^ (j + 1) * |b₀.im| < 1 / 2 := fun j hj => by
    have hpow : spinLambda a ^ (j + 1) ≤ spinLambda a ^ N :=
      pow_le_pow_right₀ hlam_gt1.le hj
    calc spinLambda a ^ (j + 1) * |b₀.im| ≤ spinLambda a ^ N * |b₀.im| :=
          mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
      _ < spinLambda a ^ N * (γN / 2) := mul_lt_mul_of_pos_left hb₀ (pow_pos (lt_trans zero_lt_one hlam_gt1) N)
      _ = (spinLambda a ^ N * γN) / 2 := by ring
      _ = 1 / 2 := by rw [hglam]
  let ε : ℝ := n ^ (-(2 / 3 : ℝ))
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  let V_bd : ℝ := V * Real.sqrt ε
  have hVbd0 : 0 ≤ V_bd := by positivity
  -- Collect a uniform radius and derivative bound over all `(j, ℓ) ∈ range N × range N`
  have hpair : ∀ j ℓ : ℕ, ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
      (j < N → ℓ < N → ∀ d : ℝ, |d| ≤ V_bd → ∀ b ∈ Metric.ball b₀ r,
        DifferentiableAt ℂ (fun z =>
          spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * (z + (d : ℂ)))
            ((spinLambda a ^ ℓ : ℝ) * (z - (d : ℂ)))) b ∧
        ‖deriv (fun z =>
          spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * (z + (d : ℂ)))
            ((spinLambda a ^ ℓ : ℝ) * (z - (d : ℂ)))) b‖ ≤ M) := by
    intro j ℓ
    by_cases hj : j < N <;> by_cases hℓ : ℓ < N
    · obtain ⟨r, M, hr, hM, hall⟩ := hasDerivAt_spinDaC_diag_and_bound ha2.le hΦ
        (pow_pos (lt_trans zero_lt_one hlam_gt1) (j + 1))
        (pow_pos (lt_trans zero_lt_one hlam_gt1) (ℓ + 1)) (hc_lt j hj) (hc_lt ℓ hℓ) V_bd hVbd0
      refine ⟨r, M, hr, hM, fun _ _ d hd b hb => ?_⟩
      have heq : (fun z =>
          spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * (z + (d : ℂ)))
            ((spinLambda a ^ ℓ : ℝ) * (z - (d : ℂ)))) =
          fun z => spinDaC a Φ (((spinLambda a ^ (j + 1) : ℝ) : ℂ) * (z + (d : ℂ)))
            (((spinLambda a ^ (ℓ + 1) : ℝ) : ℂ) * (z - (d : ℂ))) := by
        ext z; unfold spinDeltaAC; rw [pow_succ', pow_succ']; push_cast; ring_nf
      rw [heq]; exact hall d hd b hb
    · exact ⟨1, 0, zero_lt_one, le_rfl, fun _ h2 => absurd h2 hℓ⟩
    · exact ⟨1, 0, zero_lt_one, le_rfl, fun h1 => absurd h1 hj⟩
    · exact ⟨1, 0, zero_lt_one, le_rfl, fun h1 => absurd h1 hj⟩
  choose r_jl M_jl hr_jl hM_jl hjl_all using hpair
  let S_idx : Finset (ℕ × ℕ) := Finset.range N ×ˢ Finset.range N
  have hS_ne : S_idx.Nonempty := ⟨(0, 0), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr hN_pos, Finset.mem_range.mpr hN_pos⟩⟩
  let r_min : ℝ := S_idx.inf' hS_ne (fun p => r_jl p.1 p.2)
  have hrmin_pos : 0 < r_min := (Finset.lt_inf'_iff hS_ne).mpr fun p _ => hr_jl p.1 p.2
  let M_sum : ℝ := ∑ p ∈ S_idx, M_jl p.1 p.2
  have hMsum0 : 0 ≤ M_sum := Finset.sum_nonneg fun p _ => hM_jl p.1 p.2
  let g_tr : ℂ → ℝ → ℂ := fun b d => spinTruncInvC a N Φ (b + (d : ℂ)) (b - (d : ℂ))
  have hg_diff_bd : ∀ d : ℝ, |d| ≤ V_bd → ∀ b ∈ Metric.ball b₀ r_min,
      DifferentiableAt ℂ (fun z => g_tr z d) b ∧ ‖deriv (fun z => g_tr z d) b‖ ≤ M_sum := by
    intro d hd b hb
    have hmem : ∀ p ∈ S_idx, b ∈ Metric.ball b₀ (r_jl p.1 p.2) := fun p hp =>
      Metric.ball_subset_ball (Finset.inf'_le (f := fun p : ℕ × ℕ => r_jl p.1 p.2) hp) hb
    have hsum_eq : (fun z : ℂ => g_tr z d) =
        fun z : ℂ => ∑ p ∈ S_idx,
          spinDeltaAC a Φ ((spinLambda a ^ p.1 : ℝ) * (z + (d : ℂ)))
            ((spinLambda a ^ p.2 : ℝ) * (z - (d : ℂ))) := by
      ext z; dsimp [g_tr, spinTruncInvC, S_idx]
      rw [Finset.sum_product]
    have hterm_d : ∀ p ∈ S_idx, DifferentiableAt ℂ (fun z =>
        spinDeltaAC a Φ ((spinLambda a ^ p.1 : ℝ) * (z + (d : ℂ)))
          ((spinLambda a ^ p.2 : ℝ) * (z - (d : ℂ)))) b := fun p hp =>
      (hjl_all p.1 p.2 (Finset.mem_range.mp (Finset.mem_product.mp hp).1)
        (Finset.mem_range.mp (Finset.mem_product.mp hp).2) d hd b (hmem p hp)).1
    have hdiff_s : DifferentiableAt ℂ (fun z => g_tr z d) b := by
      rw [hsum_eq]; exact DifferentiableAt.fun_sum hterm_d
    have hhas : HasDerivAt (fun z => g_tr z d)
        (∑ p ∈ S_idx, deriv (fun z =>
          spinDeltaAC a Φ ((spinLambda a ^ p.1 : ℝ) * (z + (d : ℂ)))
            ((spinLambda a ^ p.2 : ℝ) * (z - (d : ℂ)))) b) b := by
      rw [hsum_eq]; exact HasDerivAt.fun_sum fun p hp => (hterm_d p hp).hasDerivAt
    refine ⟨hdiff_s, ?_⟩
    rw [hhas.deriv]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp =>
      (hjl_all p.1 p.2 (Finset.mem_range.mp (Finset.mem_product.mp hp).1)
        (Finset.mem_range.mp (Finset.mem_product.mp hp).2) d hd b (hmem p hp)).2)
  let r_final : ℝ := min r_min ((γN / 2 - |b₀.im|) / 2)
  have hrfinal_pos : 0 < r_final := lt_min hrmin_pos (by linarith only [hb₀])
  have hb_im_strip : ∀ b ∈ Metric.ball b₀ r_final, |b.im| < γN / 2 := fun b hb => by
    have hbn : ‖b - b₀‖ < r_final := by simpa [dist_eq_norm] using Metric.mem_ball.mp hb
    have h1 : |b.im - b₀.im| < (γN / 2 - |b₀.im|) / 2 := by
      rw [← Complex.sub_im]
      exact (Complex.abs_im_le_norm _).trans_lt (hbn.trans_le (min_le_right _ _))
    linarith only [abs_sub_abs_le_abs_sub b.im b₀.im, h1, hb₀]
  have hc_lt_b : ∀ {b : ℂ}, |b.im| < γN / 2 → ∀ m : ℕ, m < N → |spinLambda a ^ (m + 1) * b.im| < 1 / 2 :=
    fun {b} hb m hm => by
      have hpow : spinLambda a ^ (m + 1) ≤ spinLambda a ^ N := pow_le_pow_right₀ hlam_gt1.le hm
      rw [abs_mul, abs_of_pos (pow_pos (lt_trans zero_lt_one hlam_gt1) _)]
      calc spinLambda a ^ (m + 1) * |b.im| ≤ spinLambda a ^ N * |b.im| :=
            mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
        _ < spinLambda a ^ N * (γN / 2) := mul_lt_mul_of_pos_left hb (pow_pos (lt_trans zero_lt_one hlam_gt1) N)
        _ = (spinLambda a ^ N * γN) / 2 := by ring
        _ = 1 / 2 := by rw [hglam]
  have hg_cont_d : ∀ b : ℂ, |b.im| < γN / 2 → Continuous (fun d : ℝ => g_tr b d) := fun b hb =>
    continuous_spinTruncInvC_d hc hΦ hb.le
  -- Now differentiate `spinQSlice` at `b₀` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  have hχ_supp_d : ∀ d : ℝ, V_bd < |d| → χ (d / Real.sqrt ε) = 0 := fun d hd => by
    apply hχ_supp
    rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hε_pos), lt_div_iff₀ (Real.sqrt_pos.mpr hε_pos)]
    exact hd
  let Fq : ℂ → ℝ → ℂ := fun b d => (χ (d / Real.sqrt ε) : ℂ) * g_tr b d
  let Fq' : ℂ → ℝ → ℂ := fun b d => (χ (d / Real.sqrt ε) : ℂ) * deriv (fun z => g_tr z d) b
  let bound_q : ℝ → ℝ := (Icc (-V_bd) V_bd).indicator (fun _ => M_sum)
  have hFq_meas : ∀ᶠ b in 𝓝 b₀, AEStronglyMeasurable (Fq b) volume := by
    filter_upwards [Metric.ball_mem_nhds b₀ hrfinal_pos] with b hb
    have hm1 : Measurable (fun d : ℝ => (χ (d / Real.sqrt ε) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hχ_meas.comp (measurable_id.div_const _))
    have hm2 : Measurable (fun d : ℝ => g_tr b d) := (hg_cont_d b (hb_im_strip b hb)).measurable
    exact (hm1.mul hm2).aestronglyMeasurable
  have hFq_int : Integrable (Fq b₀) volume := by
    have hm := hFq_meas.self_of_nhds
    have hcont : ContinuousOn (fun d : ℝ => ‖g_tr b₀ d‖) (Icc (-V_bd) V_bd) :=
      (hg_cont_d b₀ hb₀).norm.continuousOn
    obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    have hM0_nn : 0 ≤ M0 := (norm_nonneg (g_tr b₀ 0)).trans
      (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        hM0 0 (Set.mem_Icc.mpr ⟨neg_nonpos.mpr hVbd0, hVbd0⟩))
    have hbd_int : Integrable ((Icc (-V_bd) V_bd).indicator (fun _ => M0)) volume :=
      (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (hs := measure_Icc_lt_top.ne))
    refine hbd_int.mono' hm (Eventually.of_forall fun d => ?_)
    dsimp [Fq]
    by_cases hd : d ∈ Icc (-V_bd) V_bd
    · rw [Set.indicator_of_mem hd, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hχ1 : |χ (d / Real.sqrt ε)| ≤ 1 := by
        have h := hχ_bd (d / Real.sqrt ε); exact abs_le.mpr ⟨by linarith, h.2⟩
      calc |χ (d / Real.sqrt ε)| * ‖g_tr b₀ d‖ ≤ 1 * M0 :=
            mul_le_mul hχ1 (by simpa [Real.norm_eq_abs] using hM0 d hd) (norm_nonneg _) zero_le_one
        _ = M0 := one_mul _
    · have hnot : V_bd < |d| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hd
        rcases hd with h1 | h2
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      rw [Set.indicator_of_notMem hd, hχ_supp_d d hnot, Complex.ofReal_zero, zero_mul, norm_zero]
  have hFq'_meas : AEStronglyMeasurable (Fq' b₀) volume := by
    let g_seq : ℕ → ℝ → ℂ := fun m d =>
      (((m + 1 : ℕ) : ℝ) : ℂ) * (g_tr (b₀ + ((((m + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) d - g_tr b₀ d)
    let df_lim : ℝ → ℂ := (Icc (-V_bd) V_bd).indicator (fun d => deriv (fun z => g_tr z d) b₀)
    have hm_meas : ∀ m : ℕ, Measurable ((Icc (-V_bd) V_bd).indicator (g_seq m)) := fun m => by
      have him_eq : (b₀ + ((((m + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)).im = b₀.im := by
        simp [Complex.add_im]
      have hstrip_m : |(b₀ + ((((m + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)).im| < γN / 2 := by
        rw [him_eq]; exact hb₀
      have hc1 := hg_cont_d _ hstrip_m
      have hc2 := hg_cont_d b₀ hb₀
      exact (continuous_const.mul (hc1.sub hc2)).measurable.indicator measurableSet_Icc
    have hm_tend : ∀ d : ℝ,
        Tendsto (fun m => (Icc (-V_bd) V_bd).indicator (g_seq m) d) atTop (𝓝 (df_lim d)) := by
      intro d
      by_cases hd : d ∈ Icc (-V_bd) V_bd
      · have hd_abs : |d| ≤ V_bd := abs_le.mpr hd
        have hdiff := (hg_diff_bd d hd_abs b₀ (Metric.mem_ball_self hrmin_pos)).1
        have hslope := hasDerivAt_iff_tendsto_slope.mp hdiff.hasDerivAt
        have hstep : Tendsto (fun m : ℕ => b₀ + (((((m + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))) atTop (𝓝[≠] b₀) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun m => ?_⟩
          · have ht : Tendsto (fun m : ℕ => (((m + 1 : ℕ) : ℝ)⁻¹ : ℝ)) atTop (𝓝 0) :=
              tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
            have h0 : Tendsto (fun m : ℕ => (((((m + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))) atTop (𝓝 0) :=
              (Complex.continuous_ofReal.tendsto 0).comp ht
            simpa using tendsto_const_nhds.add h0
          · intro h
            have h0 : (((((m + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) = 0 := by
              simpa using sub_eq_zero.mpr h
            exact absurd (Complex.ofReal_eq_zero.mp h0) (inv_ne_zero (by positivity))
        have hlim := hslope.comp hstep
        have hconv : ∀ m : ℕ,
            (Icc (-V_bd) V_bd).indicator (g_seq m) d =
              slope (fun z => g_tr z d) b₀ (b₀ + (((((m + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))) := fun m => by
          rw [Set.indicator_of_mem hd, slope_def_module, smul_eq_mul]
          dsimp [g_seq]
          rw [add_sub_cancel_left, ← Complex.ofReal_inv, inv_inv]
          push_cast; rfl
        simp_rw [hconv]
        dsimp [df_lim]
        rw [Set.indicator_of_mem hd]
        exact hlim
      · have hconst : (fun m : ℕ => (Icc (-V_bd) V_bd).indicator (g_seq m) d) = fun _ => 0 := by
          ext m; exact Set.indicator_of_notMem hd _
        rw [hconst]
        dsimp [df_lim]
        rw [Set.indicator_of_notMem hd]
        exact tendsto_const_nhds
    have hlim_meas : Measurable df_lim :=
      measurable_of_tendsto_metrizable hm_meas (tendsto_pi_nhds.mpr hm_tend)
    have hFq'_eq : Fq' b₀ = fun d => (χ (d / Real.sqrt ε) : ℂ) * df_lim d := by
      ext d
      dsimp [Fq', df_lim]
      by_cases hd : d ∈ Icc (-V_bd) V_bd
      · rw [Set.indicator_of_mem hd]
      · have hnot : V_bd < |d| := by
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hd
          rcases hd with h1 | h2
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_nonneg (by linarith)]; linarith
        rw [Set.indicator_of_notMem hd, hχ_supp_d d hnot, Complex.ofReal_zero, zero_mul, zero_mul]
    rw [hFq'_eq]
    have hχm : Measurable (fun d : ℝ => (χ (d / Real.sqrt ε) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hχ_meas.comp (measurable_id.div_const _))
    exact (hχm.mul hlim_meas).aestronglyMeasurable
  have hbound_int : Integrable bound_q volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (hs := measure_Icc_lt_top.ne))
  have hbound_le : ∀ᵐ d : ℝ ∂volume, ∀ b ∈ Metric.ball b₀ r_final, ‖Fq' b d‖ ≤ bound_q d := by
    refine Eventually.of_forall fun d b hb => ?_
    dsimp [Fq', bound_q]
    by_cases hd : d ∈ Icc (-V_bd) V_bd
    · rw [Set.indicator_of_mem hd, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hχ1 : |χ (d / Real.sqrt ε)| ≤ 1 := by
        have h := hχ_bd (d / Real.sqrt ε); exact abs_le.mpr ⟨by linarith, h.2⟩
      have hder := (hg_diff_bd d (abs_le.mpr hd) b (Metric.ball_subset_ball (min_le_left _ _) hb)).2
      calc |χ (d / Real.sqrt ε)| * ‖deriv (fun z => g_tr z d) b‖ ≤ 1 * M_sum :=
            mul_le_mul hχ1 hder (norm_nonneg _) zero_le_one
        _ = M_sum := one_mul _
    · have hnot : V_bd < |d| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hd
        rcases hd with h1 | h2
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      rw [Set.indicator_of_notMem hd, hχ_supp_d d hnot, Complex.ofReal_zero, zero_mul, norm_zero]
  have hderiv_pt : ∀ᵐ d : ℝ ∂volume, ∀ b ∈ Metric.ball b₀ r_final, HasDerivAt (fun z => Fq z d) (Fq' b d) b := by
    refine Eventually.of_forall fun d b hb => ?_
    dsimp [Fq, Fq']
    by_cases hd : |d| ≤ V_bd
    · exact ((hg_diff_bd d hd b (Metric.ball_subset_ball (min_le_left _ _) hb)).1.hasDerivAt).const_mul _
    · have hnot : V_bd < |d| := lt_of_not_ge hd
      rw [hχ_supp_d d hnot, Complex.ofReal_zero, zero_mul]
      simpa only [zero_mul] using hasDerivAt_const b (0 : ℂ)
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b₀ hrfinal_pos)
    hFq_meas hFq_int hFq'_meas hbound_le hbound_int hderiv_pt).2
  have hq_eq : spinQSlice c N Φ χ = fun b => ∫ d : ℝ, Fq b d := rfl
  rw [hq_eq]
  exact hres.differentiableAt.differentiableWithinAt

lemma spinHProfile_differentiableOn {c V R : ℝ} (hc : 49 ≤ c) (hV : 0 < V) (_hR : 0 < R)
    (hεR : (c - 1) ^ (-(2 / 3 : ℝ)) * R <
      (spinGamma ((c - 1) / 12) * (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹) / 2)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {χ : ℝ → ℝ} (hχ_meas : Measurable χ) (hχ_bd : ∀ v, 0 ≤ χ v ∧ χ v ≤ 1)
    (hχ_supp : ∀ v, V < |v| → χ v = 0) :
    DifferentiableOn ℂ (spinHProfile c (Nat.ceil (Real.log (c - 1))) Φ χ)
      (Metric.closedBall (0 : ℂ) R) := by
  let n := c - 1
  have hn_pos : 0 < n := by dsimp [n]; linarith
  let ε := n ^ (-(2 / 3 : ℝ))
  let a := n / 12
  let N := Nat.ceil (Real.log n)
  let γN := spinGamma a * (spinLambda a ^ (N - 1))⁻¹
  have hq_diff := spinQSlice_differentiableOn hc hV hΦ hχ_meas hχ_bd hχ_supp
  intro ζ hζ
  have hζ_norm : ‖ζ‖ ≤ R := by simpa [dist_zero_right] using Metric.mem_closedBall.mp hζ
  have hε_nn : 0 ≤ ε := by dsimp [ε]; positivity
  have hmem : (xiStar : ℂ) + (ε : ℂ) * ζ ∈ {b : ℂ | |b.im| < γN / 2} := by
    change |((xiStar : ℂ) + (ε : ℂ) * ζ).im| < γN / 2
    rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_ofReal_mul, abs_mul,
      abs_of_nonneg hε_nn]
    calc ε * |ζ.im| ≤ ε * ‖ζ‖ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm ζ) hε_nn
      _ ≤ ε * R := mul_le_mul_of_nonneg_left hζ_norm hε_nn
      _ < γN / 2 := hεR
  have hopen : IsOpen {b : ℂ | |b.im| < γN / 2} :=
    isOpen_lt (Complex.continuous_im.abs) continuous_const
  have hq_at : DifferentiableAt ℂ (spinQSlice c N Φ χ) ((xiStar : ℂ) + (ε : ℂ) * ζ) :=
    (hq_diff _ hmem).differentiableAt (hopen.mem_nhds hmem)
  have hlin : Differentiable ℂ (fun w : ℂ => (xiStar : ℂ) + (ε : ℂ) * w) :=
    (differentiable_const _).add ((differentiable_const _).mul differentiable_id)
  have hexp : Differentiable ℂ (fun w : ℂ =>
      ((ε * a : ℝ) : ℂ) * Complex.exp (((n * (2 * π / 3) : ℝ) : ℂ) * ((xiStar : ℂ) + (ε : ℂ) * w))) :=
    differentiable_const _ |>.mul (Complex.differentiable_exp.comp ((differentiable_const _).mul hlin))
  have hq_comp : DifferentiableAt ℂ (fun w : ℂ => spinQSlice c N Φ χ ((xiStar : ℂ) + (ε : ℂ) * w)) ζ := by
    simpa [Function.comp_def] using hq_at.comp ζ (hlin ζ)
  have hcomp : DifferentiableAt ℂ (spinHProfile c N Φ χ) ζ := by
    unfold spinHProfile
    simpa [n, ε, a, N] using (hexp ζ).fun_mul hq_comp
  exact hcomp.differentiableWithinAt

end FormalResearch.ModularBootstrap.Spin

