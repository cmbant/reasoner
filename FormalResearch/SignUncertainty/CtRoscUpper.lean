module

public import Mathlib
public import FormalResearch.Special.AiryRatioBounds
public import FormalResearch.Complex.HalfDiscCauchy
public import FormalResearch.SignUncertainty.CtRoscDefect

/-!
# The upper-half-plane branch of `exp((4/3) u^{3/2})` and Cauchy's theorem for it (`(ct:rosc)`, proof)

`constant_terms_lower.tex`, proof of `(ct:rosc)`: "`R_+(u) = 2e^{(4/3)u^{3/2}} + O(R^{-3/2}/e)` on the upper semicircle; deforming the upper semicircle
to `[-R, R]` by Cauchy's theorem and taking `-Im` yields `(ct:rosc)`".

* `airyUpE u = exp((4/3) u^{3/2})` with the upper-half-plane branch `u^{3/2} = u · exp(½(log(-iu) + iπ/2))`.  For `Im u ≥ 0` it is the principal
  branch (`airyUpE_eq`, so `‖airyUpE u‖ = e(u)⁻¹`, `airyEnv`), and unlike the principal power it is continuous on the closed upper half-plane and
  holomorphic on the open one (`continuousOn_airyUpE`, `differentiableOn_airyUpE`).
* `airyUpE_ofReal_neg` / `airyUpE_ofReal_nonneg`: its boundary values, `e^{-i(4/3)v^{3/2}}` at `-v < 0` and the real `e^{(4/3)x^{3/2}}` at `x ≥ 0`.
* `airy_halfdisc_rosc`: for `H = W f` holomorphic and real-symmetric on `|u| < R'` and a good circle `|u| = R`, if
  `‖W(w)‖ ‖R_+(w) - 2 airyUpE(w)‖ e(w) ≤ K` on the upper semicircle (the Airy asymptotics `AiryRplusComparison`), then
  `|P_R(H) - ∫_{-R}^R H + 2∫_0^R Re H(-v) sin(4/3 v^{3/2}) dv| ≤ R K ∫_0^π ‖f(Re^{iθ})‖/e dθ`.

All proved.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.HalfDiscCauchy

/-- `log(-iu) + iπ/2`, the upper-half-plane logarithm of `u` (`= log u` for `Im u ≥ 0`, `u ≠ 0`). -/
noncomputable def airyUpL (u : ℂ) : ℂ := Complex.log (-I * u) + ((π / 2 : ℝ) : ℂ) * I

lemma exp_airyUpL {u : ℂ} (h0 : u ≠ 0) : Complex.exp (airyUpL u) = u := by
  unfold airyUpL
  have h1 : (-I * u) ≠ 0 := mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) h0
  rw [Complex.exp_add, Complex.exp_log h1]
  have : Complex.exp (((π / 2 : ℝ) : ℂ) * I) = I := by
    rw [Complex.exp_mul_I]; simp
  rw [this]
  linear_combination (-u) * (Complex.I_mul_I)

lemma log_eq_airyUpL {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) : Complex.log u = airyUpL u := by
  have h1 : 0 ≤ (-I * u).re := by simpa using hu
  have h2 := Complex.abs_arg_le_pi_div_two_iff.2 h1
  have h3 := abs_le.1 h2
  have hL : (airyUpL u).im = Complex.arg (-I * u) + π / 2 := by
    simp [airyUpL, Complex.log_im]
  conv_lhs => rw [← exp_airyUpL h0]
  refine Complex.log_exp ?_ ?_ <;> rw [hL] <;> linarith [Real.pi_pos]

/-- `e^{(4/3) u^{3/2}}` with the upper-half-plane branch of `u^{3/2}`. -/
noncomputable def airyUpE (u : ℂ) : ℂ :=
  Complex.exp ((4 / 3 : ℂ) * (u * Complex.exp ((1 / 2 : ℂ) * airyUpL u)))

lemma airyUp_pow_eq {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) :
    u * Complex.exp ((1 / 2 : ℂ) * airyUpL u) = u ^ (3 / 2 : ℂ) := by
  have h : Complex.exp (airyUpL u * (3 / 2)) = u * Complex.exp ((1 / 2 : ℂ) * airyUpL u) := by
    have : airyUpL u * (3 / 2) = airyUpL u + (1 / 2 : ℂ) * airyUpL u := by ring
    rw [this, Complex.exp_add, exp_airyUpL h0]
  rw [Complex.cpow_def_of_ne_zero h0, log_eq_airyUpL hu h0, h]

lemma norm_airyUpE {u : ℂ} (hu : 0 ≤ u.im) : ‖airyUpE u‖ = (airyEnv u)⁻¹ := by
  rcases eq_or_ne u 0 with rfl | h0
  · simp [airyUpE, airyEnv]
  · unfold airyUpE airyEnv
    rw [airyUp_pow_eq hu h0, Complex.norm_exp, ← Real.exp_neg]
    congr 1
    simp only [Complex.mul_re]
    norm_num


/-! ### Boundary values on the real axis -/

lemma airyUpE_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) :
    airyUpE (x : ℂ) = ((Real.exp (4 / 3 * x ^ (3 / 2 : ℝ)) : ℝ) : ℂ) := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp [airyUpE]
  · have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h0
    unfold airyUpE
    rw [airyUp_pow_eq (by simp) hx']
    have : ((x : ℂ)) ^ (3 / 2 : ℂ) = ((x ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring]
      exact (Complex.ofReal_cpow hx _).symm
    rw [this, show (4 / 3 : ℂ) * ((x ^ (3 / 2 : ℝ) : ℝ) : ℂ) = ((4 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_exp]

lemma airyUpE_ofReal_neg {v : ℝ} (hv : 0 < v) :
    airyUpE (((-v : ℝ)) : ℂ) = Complex.exp (-(((4 / 3 * v ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * I) := by
  have hx' : (((-v : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
  unfold airyUpE
  rw [airyUp_pow_eq (by simp) hx', Complex.cpow_def_of_ne_zero hx']
  congr 1
  have hlog : Complex.log (((-v : ℝ)) : ℂ) = ((Real.log v : ℝ) : ℂ) + (π : ℂ) * I := by
    rw [Complex.log, Complex.arg_ofReal_of_neg (by linarith)]
    simp [abs_of_pos hv]
  rw [hlog]
  have e1 : Complex.exp ((((Real.log v : ℝ) : ℂ) + (π : ℂ) * I) * (3 / 2)) =
      ((v ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (-I) := by
    rw [show (((Real.log v : ℝ) : ℂ) + (π : ℂ) * I) * (3 / 2) =
        ((Real.log v * (3 / 2) : ℝ) : ℂ) + (3 * π / 2 : ℝ) * I by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have h1 : Real.cos (3 * π / 2) = 0 := by
      rw [show 3 * π / 2 = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two]; simp
    have h2 : Real.sin (3 * π / 2) = -1 := by
      rw [show 3 * π / 2 = π / 2 + π by ring, Real.sin_add_pi, Real.sin_pi_div_two]
    rw [h1, h2, ← Real.rpow_def_of_pos hv]
    simp
  rw [e1]
  push_cast
  ring


/-! ### Continuity and holomorphy -/

lemma differentiableAt_airyUpE {u : ℂ} (hu : 0 < u.im) : DifferentiableAt ℂ airyUpE u := by
  have hs : (-I * u) ∈ Complex.slitPlane := Or.inl (by simpa using hu)
  have h1 : DifferentiableAt ℂ (fun u : ℂ => Complex.log (-I * u)) u :=
    (differentiableAt_const _ |>.mul differentiableAt_id).clog hs
  unfold airyUpE airyUpL
  fun_prop

lemma continuousAt_airyUpE_of_ne {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) : ContinuousAt airyUpE u := by
  have hs : (-I * u) ∈ Complex.slitPlane := by
    rcases hu.lt_or_eq with h | h
    · exact Or.inl (by simpa using h)
    · right
      have : u.re ≠ 0 := fun h' => h0 (Complex.ext h' h.symm)
      simpa using this
  have h1 : ContinuousAt (fun u : ℂ => Complex.log (-I * u)) u :=
    (continuousAt_clog hs).comp (f := fun u : ℂ => -I * u) (by fun_prop)
  unfold airyUpE airyUpL
  fun_prop

lemma norm_mul_airyUpS (u : ℂ) :
    ‖u * Complex.exp ((1 / 2 : ℂ) * airyUpL u)‖ = ‖u‖ ^ (3 / 2 : ℝ) := by
  rcases eq_or_ne u 0 with rfl | h0
  · simp
  · rw [norm_mul, Complex.norm_exp]
    have hre : ((1 / 2 : ℂ) * airyUpL u).re = (1 / 2 : ℝ) * Real.log ‖u‖ := by
      simp [airyUpL, Complex.log_re, Complex.mul_re]
    have hpos : 0 < ‖u‖ := norm_pos_iff.2 h0
    have h1 : Real.exp ((1 / 2 : ℝ) * Real.log ‖u‖) = ‖u‖ ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hpos, mul_comm]
    rw [hre, h1]
    calc ‖u‖ * ‖u‖ ^ (1 / 2 : ℝ) = ‖u‖ ^ (1 : ℝ) * ‖u‖ ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = ‖u‖ ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hpos]; norm_num

lemma continuousAt_airyUpE_zero : ContinuousAt airyUpE 0 := by
  have h : Tendsto (fun u : ℂ => u * Complex.exp ((1 / 2 : ℂ) * airyUpL u)) (𝓝 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_mul_airyUpS]
    have := (continuous_norm.rpow_const (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))).tendsto (0 : ℂ)
    simpa using this
  have h2 : Tendsto airyUpE (𝓝 0) (𝓝 (Complex.exp 0)) := by
    unfold airyUpE
    exact (Complex.continuous_exp.tendsto 0).comp (by simpa using h.const_mul (4 / 3 : ℂ))
  have e : airyUpE 0 = Complex.exp 0 := by simp [airyUpE]
  rw [ContinuousAt, e]
  exact h2

lemma continuousOn_airyUpE : ContinuousOn airyUpE {u : ℂ | 0 ≤ u.im} := by
  intro u hu
  rcases eq_or_ne u 0 with rfl | h0
  · exact continuousAt_airyUpE_zero.continuousWithinAt
  · exact (continuousAt_airyUpE_of_ne hu h0).continuousWithinAt


/-! ### The half-disc form of `(ct:rosc)` -/

/-- `R_+ = (Bi - iAi)/Ai`. -/
noncomputable def airyRplus (u : ℂ) : ℂ := (airyBiC u - I * airyAiC u) / airyAiC u

/-- The imaginary part of `∫ g` over `[a, b]` is the integral of the imaginary part. -/
lemma im_intervalIntegral {g : ℝ → ℂ} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    (∫ t in a..b, g t).im = ∫ t in a..b, (g t).im := by
  have := Complex.imCLM.intervalIntegral_comp_comm hg
  simpa using this.symm

theorem airy_halfdisc_rosc {N : ℕ} {R R' K : ℝ}
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R) (hRR : R < R')
    {W f : ℂ → ℂ} (hW : DifferentiableOn ℂ W (ball 0 R')) (hf : DifferentiableOn ℂ f (ball 0 R'))
    (hsym : ∀ z ∈ ball (0 : ℂ) R', W ((starRingEnd ℂ) z) * f ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (W z * f z))
    (hcmp : ∀ θ ∈ Icc (0 : ℝ) π, ‖W (circleMap 0 R θ)‖ *
      ‖airyRplus (circleMap 0 R θ) - 2 * airyUpE (circleMap 0 R θ)‖ ≤ K * ‖airyUpE (circleMap 0 R θ)‖) :
    ‖((∑ n ∈ Finset.Icc 1 N, (W (airyZero n : ℂ) * f (airyZero n : ℂ)) /
          (deriv airyAiC (airyZero n : ℂ)) ^ 2) - ∫ x in (-R)..R, (W (x : ℂ) * f (x : ℂ))) +
        2 * ((∫ v in (0 : ℝ)..R, (W (-(v : ℂ)) * f (-(v : ℂ))).re * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤
      R * K * ∫ θ in (0 : ℝ)..π, ‖f (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ := by
  set H : ℂ → ℂ := fun u => W u * f u with hHdef
  have hR := hD.radius_pos
  have hHd : DifferentiableOn ℂ H (ball 0 R') := hW.mul hf
  have hid := airy_defect_identity hD hRR hHd hsym
  set w : ℝ → ℂ := circleMap 0 R with hw
  have hwn : ∀ θ, ‖w θ‖ = R := fun θ => by rw [hw, norm_circleMap_zero, abs_of_pos hR]
  have hwc : Continuous w := continuous_circleMap 0 R
  have hwmem : ∀ θ, w θ ∈ ball (0 : ℂ) R' := fun θ => cft2_mem_ball hR hRR θ
  have hwim : ∀ θ ∈ Icc (0 : ℝ) π, 0 ≤ (w θ).im := fun θ hθ => by
    rw [hw, cftDef_im_circleMap]
    exact mul_nonneg hR.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
  have hHc : Continuous (fun θ : ℝ => H (w θ)) :=
    hHd.continuousOn.comp_continuous hwc hwmem
  set J : ℝ → ℂ := fun θ => w θ * I * H (w θ) with hJ
  have hJc : Continuous J := (hwc.mul continuous_const).mul hHc
  have hEc : ContinuousOn (fun θ => airyUpE (w θ)) (Icc 0 π) :=
    (continuousOn_airyUpE.comp hwc.continuousOn (fun θ hθ => hwim θ hθ))
  have hRc : Continuous (fun θ => airyRplus (w θ)) := by
    unfold airyRplus
    exact ((differentiable_airyBiC.continuous.comp hwc).sub
      (continuous_const.mul (hD.entire.continuous.comp hwc))).div
      (hD.entire.continuous.comp hwc) (fun θ => hD.ne_zero_sphere (hwn θ))
  -- the decomposition `A_+ = A_main + E'`
  have hint1 : IntervalIntegrable (fun θ => J θ * (2 * airyUpE (w θ))) volume 0 π :=
    ((hJc.continuousOn.mono (subset_univ _)).mul (continuousOn_const.mul hEc)).intervalIntegrable_of_Icc Real.pi_pos.le
  have hint2 : IntervalIntegrable (fun θ => J θ * airyRplus (w θ)) volume 0 π :=
    (hJc.mul hRc).intervalIntegrable 0 π
  set Amain : ℂ := ∫ θ in (0 : ℝ)..π, J θ * (2 * airyUpE (w θ)) with hAmain
  set E' : ℂ := ∫ θ in (0 : ℝ)..π, J θ * (airyRplus (w θ) - 2 * airyUpE (w θ)) with hE'
  have hAsplit : airyArcPlus R H = Amain + E' := by
    have hint3 : IntervalIntegrable (fun θ => J θ * (airyRplus (w θ) - 2 * airyUpE (w θ))) volume 0 π := by
      simpa [mul_sub] using hint2.sub hint1
    rw [hAmain, hE', ← intervalIntegral.integral_add hint1 hint3]
    unfold airyArcPlus
    refine integral_congr fun θ _ => ?_
    simp only [hJ, hw, airyRplus]
    ring
  -- Cauchy on the upper half-disc
  set g : ℂ → ℂ := fun u => H u * airyUpE u with hg
  have hgc : ContinuousOn g (closedHalfDisc R) := by
    refine (hHd.continuousOn.mono ?_).mul (continuousOn_airyUpE.mono ?_)
    · intro z hz
      rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hz.1 hRR
    · intro z hz; exact hz.2
  have hgd : DifferentiableOn ℂ g (openHalfDisc R) := by
    intro z hz
    have hzb : z ∈ ball (0 : ℂ) R' := by
      rw [mem_ball_zero_iff]; exact lt_trans hz.1 hRR
    exact (((hHd z hzb).differentiableAt (isOpen_ball.mem_nhds hzb)).mul
      (differentiableAt_airyUpE hz.2)).differentiableWithinAt
  have hcau := halfDisc_cauchy hR hgc hgd
  have hAm : Amain = -2 * ∫ t in (-R)..R, g (t : ℂ) := by
    have : Amain = 2 * (I * ∫ y in (0 : ℝ)..π, g (R * Complex.exp (y * I)) * (R * Complex.exp (y * I))) := by
      rw [hAmain, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
      refine integral_congr (fun θ _ => ?_)
      simp only [hJ, hw, hg, circleMap, zero_add]; ring
    rw [this]; linear_combination 2 * hcau
  -- the imaginary part of the diameter integral
  have hball : ∀ t : ℝ, |t| ≤ R → (t : ℂ) ∈ ball (0 : ℂ) R' := fun t ht => by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith
  have hHreal : ∀ t : ℝ, |t| ≤ R → (H (t : ℂ)).im = 0 := fun t ht => by
    have h1 := hsym (t : ℂ) (hball t ht)
    rw [Complex.conj_ofReal] at h1
    have h2 : H (t : ℂ) = (starRingEnd ℂ) (H (t : ℂ)) := h1
    have := congrArg Complex.im h2
    simp only [Complex.conj_im] at this
    linarith
  have hGim_nonneg : ∀ t : ℝ, 0 ≤ t → t ≤ R → (g (t : ℂ)).im = 0 := fun t h0 h1 => by
    simp only [hg, airyUpE_ofReal_nonneg h0, Complex.mul_im, hHreal t (by rw [abs_of_nonneg h0]; exact h1),
      Complex.ofReal_im, mul_zero, zero_mul, add_zero]
  have hGim_neg : ∀ v : ℝ, 0 ≤ v → v ≤ R →
      (g (-(v : ℂ))).im = -((H (-(v : ℂ))).re * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))) := fun v h0 h1 => by
    rw [← Complex.ofReal_neg]
    rcases h0.eq_or_lt with rfl | hv
    · have h00 : (H 0).im = 0 := by simpa using hHreal 0 (by simpa using hR.le)
      simp [hg, airyUpE, h00]
    · simp only [hg, airyUpE_ofReal_neg hv, Complex.mul_im, hHreal (-v) (by rw [abs_neg, abs_of_nonneg h0]; exact h1),
        zero_mul, add_zero]
      rw [Complex.exp_mul_I]
      have : (Complex.cos (-(((4 / 3 * v ^ (3 / 2 : ℝ) : ℝ) : ℂ))) +
          Complex.sin (-(((4 / 3 * v ^ (3 / 2 : ℝ) : ℝ) : ℂ))) * I).im = -Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)) := by
        rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [this]; ring
  set I₁ : ℝ := ∫ v in (0 : ℝ)..R, (H (-(v : ℂ))).re * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ)) with hI₁
  have hGint : IntervalIntegrable (fun t : ℝ => g (t : ℂ)) volume (-R) R := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith)]
    exact hgc.comp Complex.continuous_ofReal.continuousOn (fun t ht => ofReal_mem_closedHalfDisc ht)
  have hGint1 : IntervalIntegrable (fun t : ℝ => g (t : ℂ)) volume (-R) 0 :=
    hGint.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
  have hGint2 : IntervalIntegrable (fun t : ℝ => g (t : ℂ)) volume 0 R :=
    hGint.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl)
  have himG : (∫ t in (-R)..R, g (t : ℂ)).im = -I₁ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hGint1 hGint2, Complex.add_im,
      im_intervalIntegral hGint1, im_intervalIntegral hGint2]
    have h2 : ∫ t in (0 : ℝ)..R, (g (t : ℂ)).im = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro t ht
        rw [uIcc_of_le hR.le] at ht
        exact hGim_nonneg t ht.1 ht.2
    have h1 : ∫ t in (-R)..0, (g (t : ℂ)).im = -I₁ := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := R) (fun t : ℝ => (g (t : ℂ)).im)
      simp only [neg_zero] at this
      rw [← this, hI₁, ← intervalIntegral.integral_neg]
      refine integral_congr fun v hv => ?_
      rw [uIcc_of_le hR.le] at hv
      have := hGim_neg v hv.1 hv.2
      simpa [Complex.ofReal_neg] using this
    rw [h1, h2]; ring
  have hA : (airyArcPlus R H).im = 2 * I₁ + E'.im := by
    rw [hAsplit, Complex.add_im, hAm]
    have : (-2 * ∫ t in (-R)..R, g (t : ℂ)).im = -2 * (∫ t in (-R)..R, g (t : ℂ)).im := by
      simp [Complex.mul_im]
    rw [this, himG]; ring
  -- the bound on `E'`
  have hfc : Continuous (fun θ : ℝ => ‖f (w θ)‖) :=
    (hf.continuousOn.comp_continuous hwc hwmem).norm
  have hbd : IntervalIntegrable (fun θ => R * K * (‖f (w θ)‖ * ‖airyUpE (w θ)‖)) volume 0 π := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le Real.pi_pos.le]
    exact continuousOn_const.mul (hfc.continuousOn.mul hEc.norm)
  have hE'b : ‖E'‖ ≤ R * K * ∫ θ in (0 : ℝ)..π, ‖f (w θ)‖ * ‖airyUpE (w θ)‖ := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := π) Real.pi_pos.le
      (f := fun θ => J θ * (airyRplus (w θ) - 2 * airyUpE (w θ)))
      (g := fun θ => R * K * (‖f (w θ)‖ * ‖airyUpE (w θ)‖))
      (Eventually.of_forall fun θ hθ => ?_) hbd
    · rw [intervalIntegral.integral_const_mul] at hle
      exact hle
    · have hθ' : θ ∈ Icc (0 : ℝ) π := ⟨hθ.1.le, hθ.2⟩
      have hc := hcmp θ hθ'
      simp only [hJ, norm_mul, hwn, Complex.norm_I, mul_one]
      calc R * ‖H (w θ)‖ * ‖airyRplus (w θ) - 2 * airyUpE (w θ)‖
          = R * (‖f (w θ)‖ * (‖W (w θ)‖ * ‖airyRplus (w θ) - 2 * airyUpE (w θ)‖)) := by
            simp only [hHdef, norm_mul]; ring
        _ ≤ R * (‖f (w θ)‖ * (K * ‖airyUpE (w θ)‖)) := by gcongr
        _ = R * K * (‖f (w θ)‖ * ‖airyUpE (w θ)‖) := by ring
  change ‖((∑ n ∈ Finset.Icc 1 N, H (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
      ∫ x in (-R)..R, H (x : ℂ)) + 2 * (I₁ : ℂ)‖ ≤ _
  rw [hid, hA]
  have : ((-(2 * I₁ + E'.im) : ℝ) : ℂ) + 2 * (I₁ : ℂ) = ((-E'.im : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  exact (Complex.abs_im_le_norm E').trans hE'b

/-- info: 'FormalResearch.SignUncertainty.airy_halfdisc_rosc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_halfdisc_rosc

end FormalResearch.SignUncertainty
