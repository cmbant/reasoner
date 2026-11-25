module

public import FormalResearch.SignUncertainty.UctAiryTransAsymp

/-!
# Origin expansion and real-axis bounds of the twisted transforms of `F_{*,δ}` (`uct:airy-trans` (3), F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:airy-trans` (3) (`(uct:Fstar-small)`, `(uct:Fstar-real)`,
`(uct:Fstar-loc)`, `(uct:Fstar-vert)`).

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma entire_norm_deriv_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, ‖w‖ ≤ R → ‖deriv f w‖ ≤ M := by
  have hc : Continuous (deriv f) := (hf.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun w hw => ?_⟩
  exact (hM w (by simpa using hw)).trans (le_max_left _ _)

lemma entire_sub_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, ‖w‖ ≤ R → ‖f w - f 0‖ ≤ M * ‖w‖ := by
  obtain ⟨M, hM0, hM⟩ := entire_norm_deriv_bound hf R
  refine ⟨M, hM0, fun w hw => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Metric.closedBall (0 : ℂ) R) (C := M) (x := 0) (y := w)
    (fun z _ => hf z) (fun z hz => hM z (by simpa using hz)) (convex_closedBall _ _)
    (Metric.mem_closedBall_self (le_trans (norm_nonneg w) hw)) (by simpa using hw)
  simpa using h

lemma entire_sub_bound_two {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, ‖w‖ ≤ R → ‖f w‖ ≤ M * ‖w‖ ^ 2 := by
  have hd : Differentiable ℂ (deriv f) := by
    have := (hf.contDiff (n := 2)).differentiable_iteratedDeriv 1 (by norm_num)
    simpa [iteratedDeriv_one] using this
  obtain ⟨M, hM0, hM⟩ := entire_sub_bound hd R
  refine ⟨M, hM0, fun w hw => ?_⟩
  have hb : ∀ z ∈ Metric.closedBall (0 : ℂ) ‖w‖, ‖deriv f z‖ ≤ M * ‖w‖ := by
    intro z hz
    have hz' : ‖z‖ ≤ ‖w‖ := by simpa using hz
    have := hM z (hz'.trans hw)
    rw [hf1, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left hz' hM0)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Metric.closedBall (0 : ℂ) ‖w‖) (C := M * ‖w‖) (x := 0) (y := w)
    (fun z _ => hf z) hb (convex_closedBall _ _) (Metric.mem_closedBall_self (norm_nonneg w)) (by simp)
  simp only [hf0, sub_zero] at h
  calc ‖f w‖ ≤ M * ‖w‖ * ‖w‖ := h
    _ = M * ‖w‖ ^ 2 := by ring


lemma norm_cpow_half (w : ℂ) : ‖w ^ (1 / 2 : ℂ)‖ = ‖w‖ ^ (1 / 2 : ℝ) := by
  by_cases hw : w = 0
  · subst hw; simp [Complex.zero_cpow]
  · have := norm_cpow_ofReal_exponent hw (1 / 2); simpa using this

lemma norm_cpow_three_half (w : ℂ) : ‖w ^ (3 / 2 : ℂ)‖ = ‖w‖ ^ (3 / 2 : ℝ) := by
  by_cases hw : w = 0
  · subst hw; simp [Complex.zero_cpow]
  · have := norm_cpow_ofReal_exponent hw (3 / 2); simpa using this

lemma entire_bounds : ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, ‖w‖ ≤ 3 →
    ‖uctE w‖ ≤ M ∧ ‖uctE1 w‖ ≤ M ∧ ‖uctE2 w‖ ≤ M ∧ ‖uctE w - 1‖ ≤ M * ‖w‖ ∧ ‖uctE1 w - 1‖ ≤ M * ‖w‖ ∧
      ‖uctE1 w - 1 - uctA1 * w‖ ≤ M * ‖w‖ ^ 2 := by
  have hb : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, ‖w‖ ≤ 3 → ‖f w‖ ≤ M := by
    intro f hf
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 3).exists_bound_of_continuousOn hf.continuous.continuousOn
    exact ⟨max M 0, le_max_right _ _, fun w hw => (hM w (by simpa using hw)).trans (le_max_left _ _)⟩
  obtain ⟨M1, h1, hM1⟩ := hb uctE_differentiable
  obtain ⟨M2, h2, hM2⟩ := hb uctE1_differentiable
  obtain ⟨M3, h3, hM3⟩ := hb uctE2_differentiable
  obtain ⟨M4, h4, hM4⟩ := entire_sub_bound uctE_differentiable 3
  obtain ⟨M5, h5, hM5⟩ := entire_sub_bound uctE1_differentiable 3
  have hd : Differentiable ℂ (fun w : ℂ => uctE1 w - 1 - uctA1 * w) :=
    (uctE1_differentiable.sub_const 1).sub (differentiable_const _ |>.mul differentiable_id)
  have hd0 : deriv (fun w : ℂ => uctE1 w - 1 - uctA1 * w) 0 = 0 := by
    have : HasDerivAt (fun w : ℂ => uctE1 w - 1 - uctA1 * w) (uctA1 - uctA1 * 1) 0 :=
      ((hasDerivAt_uctE1_zero.sub_const 1).sub ((hasDerivAt_id (0 : ℂ)).const_mul uctA1))
    rw [this.deriv]; ring
  obtain ⟨M6, h6, hM6⟩ := entire_sub_bound_two hd (by simp [uctE1_zero]) hd0 3
  refine ⟨M1 + M2 + M3 + M4 + M5 + M6, by positivity, fun w hw => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · linarith [hM1 w hw]
  · linarith [hM2 w hw]
  · linarith [hM3 w hw]
  · have := hM4 w hw; rw [uctE_zero] at this
    calc ‖uctE w - 1‖ ≤ M4 * ‖w‖ := this
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  · have := hM5 w hw; rw [uctE1_zero] at this
    calc ‖uctE1 w - 1‖ ≤ M5 * ‖w‖ := this
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  · have := hM6 w hw
    calc ‖uctE1 w - 1 - uctA1 * w‖ ≤ M6 * ‖w‖ ^ 2 := this
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)


/-- `G_δ = -Φ - δ (Ψ - k)`: `F̃_{*,δ}(i w) + kδ`, the part of `F̃_{*,δ}` vanishing at the origin. -/
noncomputable def uctGd (δ : ℝ) (w : ℂ) : ℂ := -uctF1Ext w - (δ : ℂ) * (uctG1Ext w - (ceK : ℂ))

/-- `R^{(2)}_{*,δ}(w) = -c w^{1/2}(E-1) - δ (k (E₁ - 1 - a₁ w) + c w^{3/2} E₂)` (the right side of `(uct:Fstar-small)`). -/
noncomputable def uctR2 (δ : ℝ) (w : ℂ) : ℂ :=
  -(uctC * w ^ (1 / 2 : ℂ) * (uctE w - 1)) -
    (δ : ℂ) * ((ceK : ℂ) * (uctE1 w - 1 - uctA1 * w) + uctC * w ^ (3 / 2 : ℂ) * uctE2 w)

lemma norm_uctC : ‖uctC‖ = ceK / Real.sqrt π := by
  unfold uctC
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ceK_pos,
    abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]

lemma uctGd_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ w : ℂ, ‖w‖ ≤ 3 → ‖uctGd δ w‖ ≤ M * ‖w‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨M, hM0, hM⟩ := entire_bounds
  set cc := ‖uctC‖ with hcc
  refine ⟨cc * M + ceK * M * Real.sqrt 3 + cc * M * 3, by have := ceK_pos; positivity, fun δ hδ0 hδ1 w hw => ?_⟩
  obtain ⟨hE, hE1, hE2, hE', hE1', hE1''⟩ := hM w hw
  have hs : ‖w‖ ≤ Real.sqrt 3 * ‖w‖ ^ (1 / 2 : ℝ) := by
    have h0 : 0 ≤ ‖w‖ := norm_nonneg w
    have : ‖w‖ = ‖w‖ ^ (1 / 2 : ℝ) * ‖w‖ ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add' h0 (by norm_num)]; norm_num
    have h3 : ‖w‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt 3 := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow h0 hw (by norm_num)
    calc ‖w‖ = ‖w‖ ^ (1 / 2 : ℝ) * ‖w‖ ^ (1 / 2 : ℝ) := this
      _ ≤ Real.sqrt 3 * ‖w‖ ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right h3 (by positivity)
  have hp0 : 0 ≤ ‖w‖ ^ (1 / 2 : ℝ) := by positivity
  have hp32 : ‖w‖ ^ (3 / 2 : ℝ) ≤ 3 * ‖w‖ ^ (1 / 2 : ℝ) := by
    have : ‖w‖ ^ (3 / 2 : ℝ) = ‖w‖ * ‖w‖ ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' (norm_nonneg w) (by norm_num), Real.rpow_one]
    rw [this]
    exact mul_le_mul_of_nonneg_right hw hp0
  have e : uctGd δ w = -(uctC * w ^ (1 / 2 : ℂ) * uctE w) - (δ : ℂ) * ((ceK : ℂ) * (uctE1 w - 1) + uctC * w ^ (3 / 2 : ℂ) * uctE2 w) := by
    unfold uctGd uctF1Ext uctG1Ext; ring
  rw [e]
  have t1 : ‖uctC * w ^ (1 / 2 : ℂ) * uctE w‖ ≤ cc * M * ‖w‖ ^ (1 / 2 : ℝ) := by
    rw [norm_mul, norm_mul, norm_cpow_half]
    calc cc * ‖w‖ ^ (1 / 2 : ℝ) * ‖uctE w‖ ≤ cc * ‖w‖ ^ (1 / 2 : ℝ) * M := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = _ := by ring
  have t2 : ‖(δ : ℂ) * ((ceK : ℂ) * (uctE1 w - 1) + uctC * w ^ (3 / 2 : ℂ) * uctE2 w)‖ ≤ ceK * M * Real.sqrt 3 * ‖w‖ ^ (1 / 2 : ℝ) + cc * M * 3 * ‖w‖ ^ (1 / 2 : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ0]
    have a1 : ‖(ceK : ℂ) * (uctE1 w - 1)‖ ≤ ceK * M * (Real.sqrt 3 * ‖w‖ ^ (1 / 2 : ℝ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceK_pos]
      calc ceK * ‖uctE1 w - 1‖ ≤ ceK * (M * ‖w‖) := mul_le_mul_of_nonneg_left hE1' ceK_pos.le
        _ ≤ ceK * (M * (Real.sqrt 3 * ‖w‖ ^ (1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hM0) ceK_pos.le
        _ = _ := by ring
    have a2 : ‖uctC * w ^ (3 / 2 : ℂ) * uctE2 w‖ ≤ cc * M * (3 * ‖w‖ ^ (1 / 2 : ℝ)) := by
      rw [norm_mul, norm_mul, norm_cpow_three_half]
      calc cc * ‖w‖ ^ (3 / 2 : ℝ) * ‖uctE2 w‖ ≤ cc * ‖w‖ ^ (3 / 2 : ℝ) * M := mul_le_mul_of_nonneg_left hE2 (by positivity)
        _ ≤ cc * (3 * ‖w‖ ^ (1 / 2 : ℝ)) * M := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp32 (by positivity)) hM0
        _ = _ := by ring
    calc δ * ‖(ceK : ℂ) * (uctE1 w - 1) + uctC * w ^ (3 / 2 : ℂ) * uctE2 w‖
        ≤ 1 * (ceK * M * (Real.sqrt 3 * ‖w‖ ^ (1 / 2 : ℝ)) + cc * M * (3 * ‖w‖ ^ (1 / 2 : ℝ))) := by
          apply mul_le_mul hδ1 ((norm_add_le _ _).trans (add_le_add a1 a2)) (norm_nonneg _) zero_le_one
      _ = _ := by ring
  calc ‖-(uctC * w ^ (1 / 2 : ℂ) * uctE w) - (δ : ℂ) * ((ceK : ℂ) * (uctE1 w - 1) + uctC * w ^ (3 / 2 : ℂ) * uctE2 w)‖
      ≤ ‖uctC * w ^ (1 / 2 : ℂ) * uctE w‖ + ‖(δ : ℂ) * ((ceK : ℂ) * (uctE1 w - 1) + uctC * w ^ (3 / 2 : ℂ) * uctE2 w)‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
    _ ≤ _ := by nlinarith [t1, t2]

lemma differentiableAt_iteratedDeriv_of_open {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (k : ℕ) {z : ℂ} (hz : z ∈ U) : DifferentiableAt ℂ (iteratedDeriv k F) z := by
  have hC_on : ContDiffOn ℂ (⊤ : ℕ∞) F U := (hF.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn
  have hwk := hC_on.differentiableOn_iteratedDerivWithin (m := k) (by exact_mod_cast WithTop.coe_lt_top k) hU.uniqueDiffOn
  exact ((hwk _ hz).differentiableAt (hU.mem_nhds hz)).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => (iteratedDerivWithin_of_isOpen hU hw).symm)

/-- The `j`-th derivative of `t ↦ F(i t)` along the real line is `i^j F^{(j)}(i t)`. -/
lemma iteratedDeriv_real_imag {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (j : ℕ) :
    ∀ q : ℝ, Complex.I * (q : ℂ) ∈ U →
      iteratedDeriv j (fun t : ℝ => F (Complex.I * (t : ℂ))) q = Complex.I ^ j * iteratedDeriv j F (Complex.I * (q : ℂ)) := by
  induction j with
  | zero => intro q _; simp
  | succ k ih =>
    intro q hq
    have hnhds : {t : ℝ | Complex.I * (t : ℂ) ∈ U} ∈ 𝓝 q := by
      have hcont : Continuous fun t : ℝ => Complex.I * (t : ℂ) := by fun_prop
      exact (hU.preimage hcont).mem_nhds hq
    have hev : iteratedDeriv k (fun t : ℝ => F (Complex.I * (t : ℂ))) =ᶠ[𝓝 q] fun t : ℝ => Complex.I ^ k * iteratedDeriv k F (Complex.I * (t : ℂ)) :=
      Filter.eventually_of_mem hnhds fun t ht => ih t ht
    rw [iteratedDeriv_succ, iteratedDeriv_succ, hev.deriv_eq]
    have hd := differentiableAt_iteratedDeriv_of_open hU hF k hq
    have h1 : HasDerivAt (fun z : ℂ => iteratedDeriv k F (Complex.I * z)) (deriv (iteratedDeriv k F) (Complex.I * (q : ℂ)) * Complex.I) (q : ℂ) := by
      have := hd.hasDerivAt.comp (q : ℂ) ((hasDerivAt_id (q : ℂ)).const_mul Complex.I)
      exact this.congr_deriv (by simp)
    have h2 := (h1.comp_ofReal).const_mul (Complex.I ^ k)
    rw [h2.deriv]
    ring

/-- Cauchy estimates for the derivatives along the imaginary axis from a power bound near the origin. -/
lemma imag_cauchy {K p : ℝ} (hK : 0 ≤ K) (hp : 0 ≤ p) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : ℂ → ℂ, DifferentiableOn ℂ F Complex.slitPlane → (∀ w : ℂ, ‖w‖ ≤ 3 → ‖F w‖ ≤ K * ‖w‖ ^ p) →
      ∀ q : ℝ, q ≠ 0 → |q| ≤ 2 → ‖iteratedDeriv j (fun t : ℝ => F (Complex.I * (t : ℂ))) q‖ ≤ C * |q| ^ (p - j) := by
  refine ⟨(j.factorial : ℝ) * K * (3 / 2 : ℝ) ^ p * 2 ^ j, by positivity, fun F hF hbd q hq0 hq2 => ?_⟩
  have hqpos : 0 < |q| := abs_pos.mpr hq0
  have hslit : ∀ z : ℂ, ‖z - Complex.I * (q : ℂ)‖ ≤ |q| / 2 → z ∈ Complex.slitPlane := by
    intro z hz
    right
    intro him
    have h1 : |z.im - q| ≤ |q| / 2 := by
      have := Complex.abs_im_le_norm (z - Complex.I * (q : ℂ))
      simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] at this
      linarith
    rw [him, zero_sub, abs_neg] at h1
    linarith
  have hsub : Metric.closedBall (Complex.I * (q : ℂ)) (|q| / 2) ⊆ Complex.slitPlane := fun z hz =>
    hslit z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
  rw [iteratedDeriv_real_imag Complex.isOpen_slitPlane hF j q (hslit _ (by simp; positivity)), norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := Complex.I * (q : ℂ)) (R := |q| / 2)
    (C := K * (3 / 2 * |q|) ^ p) j (by positivity) (hF.diffContOnCl_ball hsub) (fun z hz => by
      have hz' : ‖z - Complex.I * (q : ℂ)‖ = |q| / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hzn : ‖z‖ ≤ 3 / 2 * |q| := by
        have := norm_le_norm_add_norm_sub' z (Complex.I * (q : ℂ))
        have h2 : ‖Complex.I * (q : ℂ)‖ = |q| := by simp
        linarith
      refine (hbd z (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ hK)
      exact Real.rpow_le_rpow (norm_nonneg _) hzn hp)
  refine hcauchy.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by norm_num) hqpos.le, div_pow, show (p - (j : ℝ)) = p + -(j : ℝ) by ring, Real.rpow_add hqpos,
    Real.rpow_neg hqpos.le, Real.rpow_natCast]
  field_simp


lemma uctR2_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ w : ℂ, ‖w‖ ≤ 3 → ‖uctR2 δ w‖ ≤ M * ‖w‖ ^ (3 / 2 : ℝ) := by
  obtain ⟨M, hM0, hM⟩ := entire_bounds
  set cc := ‖uctC‖ with hcc
  refine ⟨cc * M + ceK * M * Real.sqrt 3 + cc * M, by have := ceK_pos; positivity, fun δ hδ0 hδ1 w hw => ?_⟩
  obtain ⟨hE, hE1, hE2, hE', hE1', hE1''⟩ := hM w hw
  have hp0 : 0 ≤ ‖w‖ ^ (3 / 2 : ℝ) := by positivity
  have hq : ‖w‖ ^ (1 / 2 : ℝ) * ‖w‖ = ‖w‖ ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add' (norm_nonneg w) (by norm_num), Real.rpow_one]
  have hsq : ‖w‖ ^ 2 ≤ Real.sqrt 3 * ‖w‖ ^ (3 / 2 : ℝ) := by
    have h3 : ‖w‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt 3 := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow (norm_nonneg w) hw (by norm_num)
    have : ‖w‖ ^ 2 = ‖w‖ ^ (1 / 2 : ℝ) * ‖w‖ ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add' (norm_nonneg w) (by norm_num)]; norm_num
    rw [this]; exact mul_le_mul_of_nonneg_right h3 hp0
  have t1 : ‖uctC * w ^ (1 / 2 : ℂ) * (uctE w - 1)‖ ≤ cc * M * ‖w‖ ^ (3 / 2 : ℝ) := by
    rw [norm_mul, norm_mul, norm_cpow_half]
    calc cc * ‖w‖ ^ (1 / 2 : ℝ) * ‖uctE w - 1‖ ≤ cc * ‖w‖ ^ (1 / 2 : ℝ) * (M * ‖w‖) :=
          mul_le_mul_of_nonneg_left hE' (by positivity)
      _ = cc * M * (‖w‖ ^ (1 / 2 : ℝ) * ‖w‖) := by ring
      _ = _ := by rw [hq]
  have t2 : ‖(δ : ℂ) * ((ceK : ℂ) * (uctE1 w - 1 - uctA1 * w) + uctC * w ^ (3 / 2 : ℂ) * uctE2 w)‖ ≤ ceK * M * Real.sqrt 3 * ‖w‖ ^ (3 / 2 : ℝ) + cc * M * ‖w‖ ^ (3 / 2 : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ0]
    have a1 : ‖(ceK : ℂ) * (uctE1 w - 1 - uctA1 * w)‖ ≤ ceK * M * (Real.sqrt 3 * ‖w‖ ^ (3 / 2 : ℝ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceK_pos]
      calc ceK * ‖uctE1 w - 1 - uctA1 * w‖ ≤ ceK * (M * ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left hE1'' ceK_pos.le
        _ ≤ ceK * (M * (Real.sqrt 3 * ‖w‖ ^ (3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hM0) ceK_pos.le
        _ = _ := by ring
    have a2 : ‖uctC * w ^ (3 / 2 : ℂ) * uctE2 w‖ ≤ cc * M * ‖w‖ ^ (3 / 2 : ℝ) := by
      rw [norm_mul, norm_mul, norm_cpow_three_half]
      calc cc * ‖w‖ ^ (3 / 2 : ℝ) * ‖uctE2 w‖ ≤ cc * ‖w‖ ^ (3 / 2 : ℝ) * M := mul_le_mul_of_nonneg_left hE2 (by positivity)
        _ = _ := by ring
    calc δ * ‖(ceK : ℂ) * (uctE1 w - 1 - uctA1 * w) + uctC * w ^ (3 / 2 : ℂ) * uctE2 w‖
        ≤ 1 * (ceK * M * (Real.sqrt 3 * ‖w‖ ^ (3 / 2 : ℝ)) + cc * M * ‖w‖ ^ (3 / 2 : ℝ)) :=
          mul_le_mul hδ1 ((norm_add_le _ _).trans (add_le_add a1 a2)) (norm_nonneg _) zero_le_one
      _ = _ := by ring
  unfold uctR2
  calc ‖-(uctC * w ^ (1 / 2 : ℂ) * (uctE w - 1)) - (δ : ℂ) * ((ceK : ℂ) * (uctE1 w - 1 - uctA1 * w) + uctC * w ^ (3 / 2 : ℂ) * uctE2 w)‖
      ≤ ‖uctC * w ^ (1 / 2 : ℂ) * (uctE w - 1)‖ + ‖(δ : ℂ) * ((ceK : ℂ) * (uctE1 w - 1 - uctA1 * w) + uctC * w ^ (3 / 2 : ℂ) * uctE2 w)‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
    _ ≤ _ := by nlinarith [t1, t2]

lemma differentiableOn_uctGd (δ : ℝ) : DifferentiableOn ℂ (uctGd δ) Complex.slitPlane := by
  intro w hw
  have h1 := (hasDerivAt_uctF1Ext hw).differentiableAt
  have h2 := (hasDerivAt_uctG1Ext hw).differentiableAt
  exact ((h1.neg).sub ((differentiableAt_const (δ : ℂ)).mul (h2.sub_const (ceK : ℂ)))).differentiableWithinAt

lemma differentiableOn_uctR2 (δ : ℝ) : DifferentiableOn ℂ (uctR2 δ) Complex.slitPlane := by
  intro w hw
  have hs : DifferentiableAt ℂ (fun w : ℂ => w ^ (1 / 2 : ℂ)) w := (hasDerivAt_cpow_half hw).differentiableAt
  have hs3 : DifferentiableAt ℂ (fun w : ℂ => w ^ (3 / 2 : ℂ)) w := (hasDerivAt_cpow_three_half hw).differentiableAt
  have hE := uctE_differentiable w
  have hE1 := uctE1_differentiable w
  have hE2 := uctE2_differentiable w
  unfold uctR2
  exact ((((differentiableAt_const uctC).mul hs).mul (hE.sub_const 1)).neg.sub
    ((differentiableAt_const (δ : ℂ)).mul (((differentiableAt_const (ceK : ℂ)).mul ((hE1.sub_const 1).sub ((differentiableAt_const uctA1).mul differentiableAt_id))).add
      (((differentiableAt_const uctC).mul hs3).mul hE2)))).differentiableWithinAt

theorem uctR2_deriv_bound (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ q : ℝ, q ≠ 0 → |q| ≤ 2 →
    ‖iteratedDeriv j (fun t : ℝ => uctR2 δ (Complex.I * (t : ℂ))) q‖ ≤ C * |q| ^ ((3 / 2 : ℝ) - j) := by
  obtain ⟨M, hM0, hM⟩ := uctR2_bound
  obtain ⟨C, hC0, hC⟩ := imag_cauchy (K := M) (p := 3 / 2) hM0 (by norm_num) j
  exact ⟨C, hC0, fun δ hδ0 hδ1 q hq0 hq2 => hC _ (differentiableOn_uctR2 δ) (fun w hw => hM δ hδ0 hδ1 w hw) q hq0 hq2⟩

theorem uctGd_deriv_bound (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ q : ℝ, q ≠ 0 → |q| ≤ 2 →
    ‖iteratedDeriv j (fun t : ℝ => uctGd δ (Complex.I * (t : ℂ))) q‖ ≤ C * |q| ^ ((1 / 2 : ℝ) - j) := by
  obtain ⟨M, hM0, hM⟩ := uctGd_bound
  obtain ⟨C, hC0, hC⟩ := imag_cauchy (K := M) (p := 1 / 2) hM0 (by norm_num) j
  exact ⟨C, hC0, fun δ hδ0 hδ1 q hq0 hq2 => hC _ (differentiableOn_uctGd δ) (fun w hw => hM δ hδ0 hδ1 w hw) q hq0 hq2⟩

/-- The shifted extremal seed `F_{*,δ} = F_* - δ g₁ = -f₁ - δ g₁` (`(uct:Fstard)`). -/
noncomputable def uctFstarDelta (δ : ℝ) (u : ℝ) : ℝ := -ceF1 u - δ * ceG1 (airyZero 1) u

lemma airyTwistedLaplaceC_uctFstarDelta (δ : ℝ) {y : ℂ} (hy : 0 ≤ y.re) :
    airyTwistedLaplaceC (uctFstarDelta δ) y = -uctF1Ext y - (δ : ℂ) * uctG1Ext y := by
  have h1 : Integrable (fun u : ℝ => (ceF1 u : ℂ) * cexp (y * (u : ℂ))) := ceF1_regularity.1 y hy
  have h2 : Integrable (fun u : ℝ => (ceG1 (airyZero 1) u : ℂ) * cexp (y * (u : ℂ))) := hasU2_ceG1.integrable y hy
  unfold airyTwistedLaplaceC
  have e : ∀ u : ℝ, ((uctFstarDelta δ u : ℝ) : ℂ) * cexp (y * (u : ℂ)) =
      -((ceF1 u : ℂ) * cexp (y * (u : ℂ))) - (δ : ℂ) * ((ceG1 (airyZero 1) u : ℂ) * cexp (y * (u : ℂ))) := by
    intro u; unfold uctFstarDelta; push_cast; ring
  simp_rw [e]
  have hh : Integrable (fun u : ℝ => -((ceF1 u : ℂ) * cexp (y * (u : ℂ)))) := h1.neg
  rw [integral_sub hh (h2.const_mul (δ : ℂ)), integral_neg, integral_const_mul]
  have a := airyTwistedLaplaceC_ceF1_closed hy
  have b := airyTwistedLaplaceC_ceG1_closed hy
  unfold airyTwistedLaplaceC at a b
  have hF : (ceK : ℂ) * cexp (-(y ^ 3) / 12) * ∫ u : ℝ, (ceF1 u : ℂ) * cexp (y * (u : ℂ)) = uctF1Ext y := by
    rw [a]; rfl
  have hG : (ceK : ℂ) * cexp (-(y ^ 3) / 12) * ∫ u : ℝ, (ceG1 (airyZero 1) u : ℂ) * cexp (y * (u : ℂ)) = uctG1Ext y := by
    rw [b]; rfl
  calc (ceK : ℂ) * cexp (-(y ^ 3) / 12) * (-(∫ u : ℝ, (ceF1 u : ℂ) * cexp (y * (u : ℂ))) - (δ : ℂ) * ∫ u : ℝ, (ceG1 (airyZero 1) u : ℂ) * cexp (y * (u : ℂ)))
      = -((ceK : ℂ) * cexp (-(y ^ 3) / 12) * ∫ u : ℝ, (ceF1 u : ℂ) * cexp (y * (u : ℂ))) - (δ : ℂ) * ((ceK : ℂ) * cexp (-(y ^ 3) / 12) * ∫ u : ℝ, (ceG1 (airyZero 1) u : ℂ) * cexp (y * (u : ℂ))) := by ring
    _ = _ := by rw [hF, hG]

lemma airyTwistedLaplaceC_uctFstarDelta_eq_Gd (δ : ℝ) {y : ℂ} (hy : 0 ≤ y.re) :
    airyTwistedLaplaceC (uctFstarDelta δ) y = uctGd δ y - (δ : ℂ) * (ceK : ℂ) := by
  rw [airyTwistedLaplaceC_uctFstarDelta δ hy]; unfold uctGd; ring

lemma airyTwistedLaplaceC_uctFstarDelta_R2 (δ : ℝ) {y : ℂ} (hy : 0 ≤ y.re) :
    airyTwistedLaplaceC (uctFstarDelta δ) y + (ceK : ℂ) * δ + uctC * y ^ (1 / 2 : ℂ) + (δ : ℂ) * (ceK : ℂ) * uctA1 * y = uctR2 δ y := by
  rw [airyTwistedLaplaceC_uctFstarDelta δ hy]
  unfold uctR2 uctF1Ext uctG1Ext uctE1; ring


/-! ### The real axis -/

/-- The real form of `E`: `E(x) = ½ e^{a₁x - x³/12} ∫₀¹ t^{-1/2} e^{-a₁ x t + x³t³/12} dt`. -/
noncomputable def uctEr (x : ℝ) : ℝ :=
  (1 / 2) * Real.exp (airyZero 1 * x - x ^ 3 / 12) *
    ∫ t in Ioc (0 : ℝ) 1, t ^ (-(1 / 2 : ℝ)) * Real.exp (-(airyZero 1 * (x * t)) + (x * t) ^ 3 / 12)

lemma uctE_ofReal (x : ℝ) : uctE (x : ℂ) = (uctEr x : ℂ) := by
  unfold uctE uctEr uctWI
  have h : ∫ t in Ioc (0 : ℝ) 1, uctKap t * cexp (uctPsi ((x : ℂ) * (t : ℂ))) =
      ((∫ t in Ioc (0 : ℝ) 1, t ^ (-(1 / 2 : ℝ)) * Real.exp (-(airyZero 1 * (x * t)) + (x * t) ^ 3 / 12) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [uctKap_eq ht.1]
    unfold uctPsi uctA1
    push_cast
    rfl
  rw [h]
  push_cast
  unfold uctA1
  rfl

lemma uctEr_pos (x : ℝ) : 0 < uctEr x := by
  unfold uctEr
  apply mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
  set m : ℝ := Real.exp (-(|airyZero 1| * |x|) - |x| ^ 3 / 12) with hm
  have hmpos : 0 < m := Real.exp_pos _
  have hint : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) := by
    have h : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
  have hint2 : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-(airyZero 1 * (x * t)) + (x * t) ^ 3 / 12)) (Ioc (0 : ℝ) 1) := by
    have hc : Continuous fun t : ℝ => Real.exp (-(airyZero 1 * (x * t)) + (x * t) ^ 3 / 12) := by fun_prop
    have h1 : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Icc (0 : ℝ) 1) := (integrableOn_Icc_iff_integrableOn_Ioc).mpr hint
    exact (h1.mul_continuousOn hc.continuousOn isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hlow : ∫ t in Ioc (0 : ℝ) 1, m * t ^ (-(1 / 2 : ℝ)) ≤ ∫ t in Ioc (0 : ℝ) 1, t ^ (-(1 / 2 : ℝ)) * Real.exp (-(airyZero 1 * (x * t)) + (x * t) ^ 3 / 12) := by
    refine setIntegral_mono_on (hint.const_mul m) hint2 measurableSet_Ioc fun t ht => ?_
    have h1 : m ≤ Real.exp (-(airyZero 1 * (x * t)) + (x * t) ^ 3 / 12) := by
      rw [hm]; apply Real.exp_le_exp.mpr
      have ht0 := ht.1; have ht1 := ht.2
      have h2 : -(|airyZero 1| * |x|) ≤ -(airyZero 1 * (x * t)) := by
        have : |airyZero 1 * (x * t)| ≤ |airyZero 1| * |x| := by
          rw [abs_mul, abs_mul, abs_of_pos ht0]
          calc |airyZero 1| * (|x| * t) ≤ |airyZero 1| * (|x| * 1) := by gcongr
            _ = _ := by ring
        have := neg_abs_le (airyZero 1 * (x * t)); have := le_abs_self (airyZero 1 * (x * t)); linarith
      have h3 : -(|x| ^ 3 / 12) ≤ (x * t) ^ 3 / 12 := by
        have : |(x * t) ^ 3| ≤ |x| ^ 3 := by
          rw [abs_pow, abs_mul, abs_of_pos ht0]
          exact pow_le_pow_left₀ (by positivity) (by calc |x| * t ≤ |x| * 1 := by gcongr
                                                         _ = |x| := mul_one _) 3
        have := neg_abs_le ((x * t) ^ 3); linarith [le_abs_self ((x * t) ^ 3)]
      linarith
    calc m * t ^ (-(1 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) * m := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by have := ht.1; positivity)
  have hv : ∫ t in Ioc (0 : ℝ) 1, m * t ^ (-(1 / 2 : ℝ)) = m * 2 := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by norm_num))]
    rw [Real.one_rpow, Real.zero_rpow (by norm_num)]; norm_num
  linarith


/-- `f̃₁(i x)` for real `x ≥ 0`: `(k/√π) x^{1/2} E(x)`. -/
noncomputable def uctFr (x : ℝ) : ℝ := ceK / Real.sqrt π * x ^ (1 / 2 : ℝ) * uctEr x

lemma uctF1Ext_ofReal {x : ℝ} (hx : 0 ≤ x) : uctF1Ext (x : ℂ) = (uctFr x : ℂ) := by
  unfold uctF1Ext uctFr uctC
  rw [uctE_ofReal]
  have : (x : ℂ) ^ (1 / 2 : ℂ) = ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx]; push_cast; rfl
  rw [this]; push_cast; ring

lemma airyTwistedLaplace_uctFstarDelta {x : ℝ} (hx : 0 ≤ x) (δ : ℝ) :
    airyTwistedLaplace (uctFstarDelta δ) x = -uctFr x - δ * airyTwistedLaplace (ceG1 (airyZero 1)) x := by
  have h := airyTwistedLaplaceC_uctFstarDelta δ (y := (x : ℂ)) (by simpa using hx)
  rw [airyTwistedLaplaceC_ofReal] at h
  have hG : uctG1Ext (x : ℂ) = ((airyTwistedLaplace (ceG1 (airyZero 1)) x : ℝ) : ℂ) := by
    rw [← airyTwistedLaplaceC_ofReal, ← uctG1Ext_eq (by simpa using hx)]
  rw [hG, uctF1Ext_ofReal hx] at h
  exact_mod_cast h

lemma airyTwistedLaplace_ceF1_eq {x : ℝ} (hx : 0 ≤ x) : airyTwistedLaplace ceF1 x = uctFr x := by
  have h := airyTwistedLaplaceC_ceF1_closed (y := (x : ℂ)) (by simpa using hx)
  rw [airyTwistedLaplaceC_ofReal] at h
  have : (airyTwistedLaplace ceF1 x : ℂ) = (uctFr x : ℂ) := by
    rw [h]; exact uctF1Ext_ofReal hx
  exact_mod_cast this

lemma uctFr_pos {x : ℝ} (hx : 0 < x) : 0 < uctFr x := by
  unfold uctFr
  have := ceK_pos
  have := uctEr_pos x
  positivity


lemma continuous_uctEr : Continuous uctEr := by
  have h : uctEr = fun x : ℝ => (uctE (x : ℂ)).re := by
    funext x; rw [uctE_ofReal]; simp
  rw [h]
  exact Complex.continuous_re.comp (uctE_differentiable.continuous.comp Complex.continuous_ofReal)

lemma uctZ1_ofReal {x : ℝ} (hx : 0 ≤ x) : uctZ1 (x : ℂ) = ((ceK / Real.sqrt π * (x ^ 3 * uctEr x - 2) : ℝ) : ℂ) := by
  unfold uctZ1
  rw [uctF1Ext_ofReal hx]
  have hs : (x : ℂ) ^ (1 / 2 : ℂ) = ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx]; push_cast; rfl
  rw [hs]
  have hsq : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    rw [← Real.rpow_add' hx (by norm_num)]; norm_num
  unfold uctFr uctC
  have : ((x : ℝ) ^ (1 / 2 : ℝ)) * (ceK / Real.sqrt π * x ^ (1 / 2 : ℝ) * uctEr x) = ceK / Real.sqrt π * (x * uctEr x) := by
    calc x ^ (1 / 2 : ℝ) * (ceK / Real.sqrt π * x ^ (1 / 2 : ℝ) * uctEr x) = ceK / Real.sqrt π * ((x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) * uctEr x) := by ring
      _ = _ := by rw [hsq]
  have h2 : (x : ℂ) ^ 2 * (((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((ceK / Real.sqrt π * x ^ (1 / 2 : ℝ) * uctEr x : ℝ) : ℂ)) =
      ((x ^ 2 * (ceK / Real.sqrt π * (x * uctEr x)) : ℝ) : ℂ) := by
    rw [← this]; push_cast; ring
  rw [h2]; push_cast; ring


lemma uctP_bounds : ∃ p₁ p₂ : ℝ, 0 < p₁ ∧ p₁ ≤ p₂ ∧ ∀ x : ℝ, 1 ≤ x → p₁ ≤ x ^ 3 * uctEr x ∧ x ^ 3 * uctEr x ≤ p₂ := by
  obtain ⟨K, hK, h⟩ := uctZ1_bound_rhp
  set cr : ℝ := ceK / Real.sqrt π with hcr
  have hcr0 : 0 < cr := div_pos ceK_pos (Real.sqrt_pos.mpr Real.pi_pos)
  set R : ℝ := K / cr + 1 with hR
  have hR1 : 1 ≤ R := by have : 0 ≤ K / cr := by positivity
                         linarith
  -- large x
  have hlarge : ∀ x : ℝ, R ≤ x → 1 ≤ x ^ 3 * uctEr x ∧ x ^ 3 * uctEr x ≤ 3 := by
    intro x hx
    have hx1 : 1 ≤ x := hR1.trans hx
    have hx0 : 0 < x := by linarith
    have hb := h (x : ℂ) (by simpa using hx0) (by simpa [abs_of_pos hx0] using hx1)
    rw [uctZ1_ofReal hx0.le, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0,
      abs_mul, abs_of_pos hcr0] at hb
    have hxx : x ^ (-(2 : ℝ)) = 1 / x ^ 2 := by
      rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; simp
    rw [hxx] at hb
    have h2 : |x ^ 3 * uctEr x - 2| ≤ K / cr * (1 / x ^ 2) := by
      rw [show K / cr * (1 / x ^ 2) = (K * (1 / x ^ 2)) / cr by ring, le_div_iff₀ hcr0]
      linarith
    have h3 : K / cr * (1 / x ^ 2) ≤ 1 := by
      have : K / cr < x := by linarith
      have hx2 : x ≤ x ^ 2 := by nlinarith
      calc K / cr * (1 / x ^ 2) ≤ x * (1 / x ^ 2) := by gcongr
        _ ≤ x ^ 2 * (1 / x ^ 2) := by gcongr
        _ = 1 := by field_simp
    have := abs_le.mp (h2.trans h3)
    constructor <;> linarith
  -- compact part
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 * uctEr x) (Icc 1 R) := (continuous_pow 3 |>.mul continuous_uctEr).continuousOn
  obtain ⟨x₁, hx₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hR1) hcont
  obtain ⟨x₂, hx₂, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hR1) hcont
  have hP1 : 0 < x₁ ^ 3 * uctEr x₁ := by
    have : 0 < x₁ := by linarith [hx₁.1]
    have := uctEr_pos x₁; positivity
  refine ⟨min 1 (x₁ ^ 3 * uctEr x₁), max 3 (x₂ ^ 3 * uctEr x₂), lt_min one_pos hP1, ?_, fun x hx => ?_⟩
  · exact (min_le_left _ _).trans ((by norm_num : (1 : ℝ) ≤ 3).trans (le_max_left _ _))
  · rcases le_or_gt R x with hxR | hxR
    · obtain ⟨a, b⟩ := hlarge x hxR
      exact ⟨(min_le_left _ _).trans a, b.trans (le_max_left _ _)⟩
    · have hxm : x ∈ Icc 1 R := ⟨hx, hxR.le⟩
      exact ⟨(min_le_right _ _).trans (hmin hxm), (hmax hxm).trans (le_max_right _ _)⟩


lemma uctFr_two_sided : ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ x : ℝ, 0 < x →
    m * min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) ≤ uctFr x ∧ uctFr x ≤ M * min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) := by
  obtain ⟨p₁, p₂, hp₁, hp₁₂, hP⟩ := uctP_bounds
  set cr : ℝ := ceK / Real.sqrt π with hcr
  have hcr0 : 0 < cr := div_pos ceK_pos (Real.sqrt_pos.mpr Real.pi_pos)
  obtain ⟨x₁, hx₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) continuous_uctEr.continuousOn
  obtain ⟨x₂, hx₂, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) continuous_uctEr.continuousOn
  have he1 := uctEr_pos x₁
  set e₁ := uctEr x₁
  set e₂ := uctEr x₂
  have he12 : e₁ ≤ e₂ := hmin hx₂
  refine ⟨cr * min e₁ p₁, cr * max e₂ p₂, by positivity, ?_, fun x hx => ?_⟩
  · apply mul_le_mul_of_nonneg_left _ hcr0.le
    exact (min_le_left _ _).trans (he12.trans (le_max_left _ _))
  · rcases le_or_gt x 1 with hx1 | hx1
    · have hm : min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) = x ^ (1 / 2 : ℝ) := by
        apply min_eq_left
        calc x ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1 (by norm_num)
          _ ≤ x ^ (-(5 / 2) : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hx1 (by norm_num)
      rw [hm]
      have hxm : x ∈ Icc (0 : ℝ) 1 := ⟨hx.le, hx1⟩
      have h1 : e₁ ≤ uctEr x := hmin hxm
      have h2 : uctEr x ≤ e₂ := hmax hxm
      have hxp : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
      unfold uctFr
      rw [← hcr]
      constructor
      · calc cr * min e₁ p₁ * x ^ (1 / 2 : ℝ) = cr * x ^ (1 / 2 : ℝ) * min e₁ p₁ := by ring
          _ ≤ cr * x ^ (1 / 2 : ℝ) * uctEr x := by
              apply mul_le_mul_of_nonneg_left ((min_le_left _ _).trans h1) (by positivity)
      · calc cr * x ^ (1 / 2 : ℝ) * uctEr x ≤ cr * x ^ (1 / 2 : ℝ) * max e₂ p₂ :=
              mul_le_mul_of_nonneg_left (h2.trans (le_max_left _ _)) (by positivity)
          _ = cr * max e₂ p₂ * x ^ (1 / 2 : ℝ) := by ring
    · have hm : min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) = x ^ (-(5 / 2) : ℝ) := by
        apply min_eq_right
        calc x ^ (-(5 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
          _ ≤ x ^ (1 / 2 : ℝ) := Real.one_le_rpow hx1.le (by norm_num)
      rw [hm]
      obtain ⟨hp1', hp2'⟩ := hP x hx1.le
      have hrel : x ^ (1 / 2 : ℝ) = x ^ (-(5 / 2) : ℝ) * x ^ 3 := by
        rw [show x ^ 3 = x ^ (3 : ℝ) by norm_cast, ← Real.rpow_add hx]; norm_num
      have hxp : 0 < x ^ (-(5 / 2) : ℝ) := Real.rpow_pos_of_pos hx _
      unfold uctFr
      rw [← hcr, hrel]
      constructor
      · calc cr * min e₁ p₁ * x ^ (-(5 / 2) : ℝ) = cr * x ^ (-(5 / 2) : ℝ) * min e₁ p₁ := by ring
          _ ≤ cr * x ^ (-(5 / 2) : ℝ) * (x ^ 3 * uctEr x) :=
              mul_le_mul_of_nonneg_left (((min_le_right _ _).trans hp1')) (by positivity)
          _ = _ := by ring
      · calc cr * (x ^ (-(5 / 2) : ℝ) * x ^ 3) * uctEr x = cr * x ^ (-(5 / 2) : ℝ) * (x ^ 3 * uctEr x) := by ring
          _ ≤ cr * x ^ (-(5 / 2) : ℝ) * max e₂ p₂ :=
              mul_le_mul_of_nonneg_left (hp2'.trans (le_max_right _ _)) (by positivity)
          _ = cr * max e₂ p₂ * x ^ (-(5 / 2) : ℝ) := by ring


lemma uctFstarDelta_zero : uctFstarDelta 0 = fun u => -ceF1 u := by
  funext u; simp [uctFstarDelta]

lemma airyTwistedLaplace_ceG1_nonneg_bounds : ∃ bg Cg : ℝ, 0 < bg ∧ bg ≤ Cg ∧ ∀ x : ℝ, 0 ≤ x →
    bg * (1 + x) ^ (-(9 / 2 : ℝ)) ≤ airyTwistedLaplace (ceG1 (airyZero 1)) x ∧
      airyTwistedLaplace (ceG1 (airyZero 1)) x ≤ Cg * (1 + x) ^ (-(9 / 2 : ℝ)) := by
  obtain ⟨bg, Cg, hbg, hbC, hup, hlo⟩ := ceG1_twisted_bounds
  refine ⟨bg, Cg, hbg, hbC, fun x hx => ⟨hlo x hx, ?_⟩⟩
  have := hup (x : ℂ) (by simpa using hx)
  rw [airyTwistedLaplaceC_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
  simpa using (le_abs_self _).trans this

/-- **`(uct:Fstar-real)` of `uct:airy-trans` (3)**, with the positivity statements. -/
theorem uct_airy_trans_real : ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ x : ℝ, 0 < x →
    c₀ * (min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) + δ * (1 + x) ^ (-(9 / 2 : ℝ))) ≤ -airyTwistedLaplace (uctFstarDelta δ) x ∧
      -airyTwistedLaplace (uctFstarDelta δ) x ≤ C₀ * (min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) + δ * (1 + x) ^ (-(9 / 2 : ℝ))) := by
  obtain ⟨m, M, hm, hmM, hF⟩ := uctFr_two_sided
  obtain ⟨bg, Cg, hbg, hbC, hG⟩ := airyTwistedLaplace_ceG1_nonneg_bounds
  refine ⟨min m bg, max M Cg, lt_min hm hbg, (min_le_left _ _).trans (hmM.trans (le_max_left _ _)), fun δ hδ0 hδ1 x hx => ?_⟩
  have e : -(-uctFr x - δ * airyTwistedLaplace (ceG1 (airyZero 1)) x) = uctFr x + δ * airyTwistedLaplace (ceG1 (airyZero 1)) x := by ring
  rw [airyTwistedLaplace_uctFstarDelta hx.le, e]
  obtain ⟨hF1, hF2⟩ := hF x hx
  obtain ⟨hG1, hG2⟩ := hG x hx.le
  have hmin0 : 0 ≤ min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) := le_min (by positivity) (by positivity)
  have hp : 0 ≤ δ * (1 + x) ^ (-(9 / 2 : ℝ)) := by positivity
  constructor
  · calc min m bg * (min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) + δ * (1 + x) ^ (-(9 / 2 : ℝ)))
        = min m bg * min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) + min m bg * (δ * (1 + x) ^ (-(9 / 2 : ℝ))) := by ring
      _ ≤ m * min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) + δ * (bg * (1 + x) ^ (-(9 / 2 : ℝ))) := by
          apply add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) hmin0)
          calc min m bg * (δ * (1 + x) ^ (-(9 / 2 : ℝ))) ≤ bg * (δ * (1 + x) ^ (-(9 / 2 : ℝ))) := mul_le_mul_of_nonneg_right (min_le_right _ _) hp
            _ = _ := by ring
      _ ≤ uctFr x + δ * airyTwistedLaplace (ceG1 (airyZero 1)) x := add_le_add hF1 (mul_le_mul_of_nonneg_left hG1 hδ0)
  · calc uctFr x + δ * airyTwistedLaplace (ceG1 (airyZero 1)) x
        ≤ M * min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) + δ * (Cg * (1 + x) ^ (-(9 / 2 : ℝ))) :=
          add_le_add hF2 (mul_le_mul_of_nonneg_left hG2 hδ0)
      _ ≤ max M Cg * min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) + max M Cg * (δ * (1 + x) ^ (-(9 / 2 : ℝ))) := by
          apply add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hmin0)
          calc δ * (Cg * (1 + x) ^ (-(9 / 2 : ℝ))) = Cg * (δ * (1 + x) ^ (-(9 / 2 : ℝ))) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hp
      _ = _ := by ring


/-- The holomorphic extension of `F̃_{*,δ}`. -/
noncomputable def uctFd (δ : ℝ) (w : ℂ) : ℂ := -uctF1Ext w - (δ : ℂ) * uctG1Ext w

lemma uctFd_eq {δ : ℝ} {w : ℂ} (hw : 0 ≤ w.re) : airyTwistedLaplaceC (uctFstarDelta δ) w = uctFd δ w :=
  airyTwistedLaplaceC_uctFstarDelta δ hw

lemma differentiableOn_uctFd (δ : ℝ) : DifferentiableOn ℂ (uctFd δ) Complex.slitPlane := by
  intro w hw
  have h1 := (hasDerivAt_uctF1Ext hw).differentiableAt
  have h2 := (hasDerivAt_uctG1Ext hw).differentiableAt
  exact (h1.neg.sub ((differentiableAt_const (δ : ℂ)).mul h2)).differentiableWithinAt

lemma norm_rpow_neg_five_half_le {w : ℂ} (hw : 1 ≤ ‖w‖) : ‖w‖ ^ (-(9 / 2 : ℝ)) ≤ ‖w‖ ^ (-(5 / 2 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_le hw (by norm_num)

lemma continuousOn_uctF1Ext : ContinuousOn uctF1Ext {w : ℂ | 0 ≤ w.re} := by
  unfold uctF1Ext
  exact (continuousOn_const.mul (continuousOn_cpow_re_nonneg _ (by norm_num))).mul uctE_differentiable.continuous.continuousOn

lemma continuousOn_uctG1Ext : ContinuousOn uctG1Ext {w : ℂ | 0 ≤ w.re} := by
  unfold uctG1Ext
  exact (continuousOn_const.mul uctE1_differentiable.continuous.continuousOn).add
    ((continuousOn_const.mul (continuousOn_cpow_re_nonneg _ (by norm_num))).mul uctE2_differentiable.continuous.continuousOn)

/-- `F̃₁ = (Z₁ + 2c) w^{-5/2}`. -/
lemma uctF1Ext_eq_Z1 {w : ℂ} (hw : w ≠ 0) : ‖uctF1Ext w‖ * ‖w‖ ^ (5 / 2 : ℝ) = ‖uctZ1 w + 2 * uctC‖ := by
  have e : uctZ1 w + 2 * uctC = w ^ (5 / 2 : ℂ) * uctF1Ext w := by
    unfold uctZ1; rw [cpow_five_half]; ring
  rw [e, norm_mul, norm_cpow_five_half hw]; ring

/-- Global decay of `F̃_{*,δ}` on the right half plane (uniform in `δ ∈ [0,1]`). -/
lemma uctFd_global : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ w : ℂ, 0 ≤ w.re →
    ‖uctFd δ w‖ ≤ C * (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C1, hC1, h1⟩ := uctZ1_iteratedDeriv_bound 0
  obtain ⟨C2, hC2, h2⟩ := uctG1Ext_iteratedDeriv_bound 0
  set Kc : Set ℂ := {w : ℂ | 0 ≤ w.re ∧ ‖w‖ ≤ 2} with hKc
  have hKc_compact : IsCompact Kc := by
    have hclosed : IsClosed Kc :=
      IsClosed.inter (isClosed_le continuous_const Complex.continuous_re) (isClosed_le continuous_norm continuous_const)
    exact (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset hclosed (fun w hw => by simpa [Metric.mem_closedBall, dist_zero_right] using hw.2)
  obtain ⟨M1, hM1⟩ := hKc_compact.exists_bound_of_continuousOn (continuousOn_uctF1Ext.mono (fun w hw => hw.1))
  obtain ⟨M2, hM2⟩ := hKc_compact.exists_bound_of_continuousOn (continuousOn_uctG1Ext.mono (fun w hw => hw.1))
  set cc := ‖uctC‖
  have hM10 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 ⟨by simp, by simp⟩)
  have hM20 : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0 ⟨by simp, by simp⟩)
  refine ⟨(M1 + M2) * 3 ^ (5 / 2 : ℝ) + (C1 / 4 + 2 * cc + C2) * (3 / 2) ^ (5 / 2 : ℝ), by positivity, fun δ hδ0 hδ1 w hw => ?_⟩
  have hn : 0 ≤ ‖w‖ := norm_nonneg w
  have hdec : ‖uctFd δ w‖ ≤ ‖uctF1Ext w‖ + ‖uctG1Ext w‖ := by
    unfold uctFd
    calc ‖-uctF1Ext w - (δ : ℂ) * uctG1Ext w‖ ≤ ‖-uctF1Ext w‖ + ‖(δ : ℂ) * uctG1Ext w‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ0]
        have : δ * ‖uctG1Ext w‖ ≤ 1 * ‖uctG1Ext w‖ := mul_le_mul_of_nonneg_right hδ1 (norm_nonneg _)
        linarith
  rcases le_or_gt ‖w‖ 2 with hw2 | hw2
  · have a := hM1 w ⟨hw, hw2⟩
    have b := hM2 w ⟨hw, hw2⟩
    have hp : (3 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    have h3 : (3 : ℝ) ^ (5 / 2 : ℝ) * (3 : ℝ) ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    have hge : 0 ≤ (C1 / 4 + 2 * cc + C2) * (3 / 2) ^ (5 / 2 : ℝ) * (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) := by positivity
    calc ‖uctFd δ w‖ ≤ M1 + M2 := hdec.trans (add_le_add a b)
      _ = (M1 + M2) * 3 ^ (5 / 2 : ℝ) * 3 ^ (-(5 / 2 : ℝ)) := by rw [mul_assoc, h3, mul_one]
      _ ≤ (M1 + M2) * 3 ^ (5 / 2 : ℝ) * (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) := by gcongr
      _ ≤ _ := by nlinarith [hge]
  · have hw0 : w ≠ 0 := fun h => by rw [h] at hw2; simp at hw2; linarith
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have z1 := h1 w hw hw2.le
    simp only [iteratedDeriv_zero, Nat.cast_zero, add_zero] at z1
    have g1 := h2 w hw hw2.le
    simp only [iteratedDeriv_zero, Nat.cast_zero, add_zero] at g1
    have hw52 : 0 < ‖w‖ ^ (5 / 2 : ℝ) := by positivity
    have hZ : ‖uctZ1 w + 2 * uctC‖ ≤ (C1 / 4 + 2 * cc) := by
      calc ‖uctZ1 w + 2 * uctC‖ ≤ ‖uctZ1 w‖ + ‖2 * uctC‖ := norm_add_le _ _
        _ ≤ C1 * ‖w‖ ^ (-(2 : ℝ)) + 2 * cc := by rw [norm_mul]; simp only [RCLike.norm_ofNat]; linarith
        _ ≤ C1 / 4 + 2 * cc := by
            have : ‖w‖ ^ (-(2 : ℝ)) ≤ 1 / 4 := by
              rw [Real.rpow_neg hpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
              rw [inv_eq_one_div]; apply one_div_le_one_div_of_le (by norm_num); nlinarith
            nlinarith
    have hF1 : ‖uctF1Ext w‖ ≤ (C1 / 4 + 2 * cc) * ‖w‖ ^ (-(5 / 2 : ℝ)) := by
      have := uctF1Ext_eq_Z1 hw0
      rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ hw52]
      linarith
    have hG1 : ‖uctG1Ext w‖ ≤ C2 * ‖w‖ ^ (-(5 / 2 : ℝ)) :=
      g1.trans (mul_le_mul_of_nonneg_left (norm_rpow_neg_five_half_le (by linarith)) hC2)
    have hcomp : ‖w‖ ^ (-(5 / 2 : ℝ)) ≤ (3 / 2 : ℝ) ^ (5 / 2 : ℝ) * (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) := by
      have h32 : (2 / 3 : ℝ) * (1 + ‖w‖) ≤ ‖w‖ := by linarith
      calc ‖w‖ ^ (-(5 / 2 : ℝ)) ≤ ((2 / 3 : ℝ) * (1 + ‖w‖)) ^ (-(5 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h32 (by norm_num)
        _ = (2 / 3 : ℝ) ^ (-(5 / 2 : ℝ)) * (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) := Real.mul_rpow (by norm_num) (by positivity)
        _ = _ := by
            congr 1
            rw [Real.rpow_neg (by norm_num), show (2 / 3 : ℝ) = ((3 / 2 : ℝ))⁻¹ by norm_num, Real.inv_rpow (by norm_num), inv_inv]
    have hge : 0 ≤ (M1 + M2) * 3 ^ (5 / 2 : ℝ) * (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) := by positivity
    calc ‖uctFd δ w‖ ≤ ‖uctF1Ext w‖ + ‖uctG1Ext w‖ := hdec
      _ ≤ (C1 / 4 + 2 * cc + C2) * ‖w‖ ^ (-(5 / 2 : ℝ)) := by nlinarith [hF1, hG1]
      _ ≤ (C1 / 4 + 2 * cc + C2) * ((3 / 2 : ℝ) ^ (5 / 2 : ℝ) * (1 + ‖w‖) ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ = (C1 / 4 + 2 * cc + C2) * (3 / 2) ^ (5 / 2 : ℝ) * (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) := by ring
      _ ≤ _ := by nlinarith [hge]

lemma local_variation_right {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {w : ℂ | 0 < w.re}) {x B : ℝ} (hx : 0 < x)
    (hB : ∀ w : ℂ, x / 2 ≤ w.re → ‖w - (x : ℂ)‖ ≤ x / 2 → ‖F w‖ ≤ B) :
    ∀ y : ℝ, |y| ≤ x / 4 → ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - F (x : ℂ)‖ ≤ 4 * B / x * |y| := by
  intro y hy
  have hre : ∀ w : ℂ, ‖w - (x : ℂ)‖ ≤ x / 2 → x / 2 ≤ w.re := by
    intro w hw
    have := Complex.abs_re_le_norm (w - (x : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    have := (abs_le.mp (this.trans hw)).1
    linarith
  have hslit : ∀ w : ℂ, ‖w - (x : ℂ)‖ ≤ x / 2 → w ∈ {w : ℂ | 0 < w.re} := fun w hw => by
    have := hre w hw
    show 0 < w.re
    linarith
  have hderiv : ∀ z ∈ Metric.closedBall (x : ℂ) (x / 4), ‖deriv F z‖ ≤ 4 * B / x := by
    intro z hz
    have hz' : ‖z - (x : ℂ)‖ ≤ x / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hsub : Metric.closedBall z (x / 4) ⊆ {w : ℂ | 0 < w.re} := by
      intro w hw
      have hw' : ‖w - z‖ ≤ x / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
      apply hslit
      calc ‖w - (x : ℂ)‖ = ‖(w - z) + (z - (x : ℂ))‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z - (x : ℂ)‖ := norm_add_le _ _
        _ ≤ x / 2 := by linarith
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := x / 4) (C := B) (f := F) (by positivity)
      (hF.diffContOnCl_ball hsub) (fun w hw => by
        have hw' : ‖w - z‖ = x / 4 := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
        apply hB w
        · apply hre; calc ‖w - (x : ℂ)‖ = ‖(w - z) + (z - (x : ℂ))‖ := by ring_nf
                          _ ≤ ‖w - z‖ + ‖z - (x : ℂ)‖ := norm_add_le _ _
                          _ ≤ x / 2 := by linarith
        · calc ‖w - (x : ℂ)‖ = ‖(w - z) + (z - (x : ℂ))‖ := by ring_nf
            _ ≤ ‖w - z‖ + ‖z - (x : ℂ)‖ := norm_add_le _ _
            _ ≤ x / 2 := by linarith)
    calc ‖deriv F z‖ ≤ B / (x / 4) := this
      _ = 4 * B / x := by field_simp
  have hmem : (x : ℂ) + (y : ℂ) * Complex.I ∈ Metric.closedBall (x : ℂ) (x / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : (x : ℂ) + (y : ℂ) * Complex.I - (x : ℂ) = (y : ℂ) * Complex.I := by ring
    rw [this]; simpa using hy
  have hdiff : ∀ z ∈ Metric.closedBall (x : ℂ) (x / 4), DifferentiableAt ℂ F z := by
    intro z hz
    have hz' : ‖z - (x : ℂ)‖ ≤ x / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    exact (hF z (hslit z (by linarith))).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hslit z (by linarith)))
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := F) (s := Metric.closedBall (x : ℂ) (x / 4)) (C := 4 * B / x)
    (x := (x : ℂ)) (y := (x : ℂ) + (y : ℂ) * Complex.I) hdiff hderiv (convex_closedBall _ _) (Metric.mem_closedBall_self (by positivity)) hmem
  have e : ‖(x : ℂ) + (y : ℂ) * Complex.I - (x : ℂ)‖ = |y| := by
    have : (x : ℂ) + (y : ℂ) * Complex.I - (x : ℂ) = (y : ℂ) * Complex.I := by ring
    rw [this]; simp
  rw [e] at h
  exact h

lemma local_variation {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F Complex.slitPlane) {x B : ℝ} (hx : 0 < x)
    (hB : ∀ w : ℂ, x / 2 ≤ w.re → ‖w - (x : ℂ)‖ ≤ x / 2 → ‖F w‖ ≤ B) :
    ∀ y : ℝ, |y| ≤ x / 4 → ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - F (x : ℂ)‖ ≤ 4 * B / x * |y| :=
  local_variation_right (hF.mono fun _w hw => Or.inl hw) hx hB


lemma uctGd_eq_Fd (δ : ℝ) (w : ℂ) : uctGd δ w = uctFd δ w + (δ : ℂ) * (ceK : ℂ) := by
  unfold uctGd uctFd; ring

/-- **`(uct:Fstar-loc)` of `uct:airy-trans` (3).** -/
theorem uct_airy_trans_loc : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ x : ℝ, 0 < x → ∀ y : ℝ, |y| ≤ x / 4 →
    ‖airyTwistedLaplaceC (uctFstarDelta δ) ((x : ℂ) + (y : ℂ) * Complex.I) - airyTwistedLaplaceC (uctFstarDelta δ) (x : ℂ)‖ ≤
      C * (|y| / x) * (-airyTwistedLaplace (uctFstarDelta δ) x) := by
  obtain ⟨c₀, C₀, hc₀, hcC, hreal⟩ := uct_airy_trans_real
  obtain ⟨Cg, hCg, hglob⟩ := uctFd_global
  obtain ⟨M, hM0, hM⟩ := uctGd_bound
  refine ⟨max (4 * Cg * 2 ^ (5 / 2 : ℝ) / c₀) (4 * M * Real.sqrt (3 / 2) / c₀), by positivity, fun δ hδ0 hδ1 x hx y hy => ?_⟩
  have hre1 : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
  have hre2 : (x : ℂ).re = x := by simp
  rw [uctFd_eq (by rw [hre1]; exact hx.le), uctFd_eq (by rw [hre2]; exact hx.le)]
  obtain ⟨hlow, -⟩ := hreal δ hδ0 hδ1 x hx
  have hδG : 0 ≤ δ * (1 + x) ^ (-(9 / 2 : ℝ)) := by positivity
  have hy0 : 0 ≤ |y| / x := by positivity
  rcases le_or_gt 1 x with hx1 | hx1
  · -- x ≥ 1
    have hmin : min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) = x ^ (-(5 / 2) : ℝ) := by
      apply min_eq_right
      calc x ^ (-(5 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
        _ ≤ x ^ (1 / 2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    rw [hmin] at hlow
    have hlow' : c₀ * x ^ (-(5 / 2) : ℝ) ≤ -airyTwistedLaplace (uctFstarDelta δ) x := by
      have : 0 ≤ c₀ * (δ * (1 + x) ^ (-(9 / 2 : ℝ))) := by positivity
      nlinarith
    have hB : ∀ w : ℂ, x / 2 ≤ w.re → ‖w - (x : ℂ)‖ ≤ x / 2 → ‖uctFd δ w‖ ≤ Cg * (x / 2) ^ (-(5 / 2 : ℝ)) := by
      intro w hw1 _
      have hw0 : 0 ≤ w.re := by linarith
      have hwn : x / 2 ≤ ‖w‖ := hw1.trans (Complex.re_le_norm w)
      calc ‖uctFd δ w‖ ≤ Cg * (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) := hglob δ hδ0 hδ1 w hw0
        _ ≤ Cg * (x / 2) ^ (-(5 / 2 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hCg
            exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have hv := local_variation (differentiableOn_uctFd δ) hx hB y hy
    calc ‖uctFd δ ((x : ℂ) + (y : ℂ) * Complex.I) - uctFd δ (x : ℂ)‖ ≤ 4 * (Cg * (x / 2) ^ (-(5 / 2 : ℝ))) / x * |y| := hv
      _ = (4 * Cg * 2 ^ (5 / 2 : ℝ)) * (|y| / x) * x ^ (-(5 / 2) : ℝ) := by
          have hh : (x / 2) ^ (-(5 / 2 : ℝ)) = 2 ^ (5 / 2 : ℝ) * x ^ (-(5 / 2) : ℝ) := by
            rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            field_simp
          rw [hh]; field_simp
      _ = (4 * Cg * 2 ^ (5 / 2 : ℝ) / c₀) * (|y| / x) * (c₀ * x ^ (-(5 / 2) : ℝ)) := by field_simp
      _ ≤ (4 * Cg * 2 ^ (5 / 2 : ℝ) / c₀) * (|y| / x) * (-airyTwistedLaplace (uctFstarDelta δ) x) :=
          mul_le_mul_of_nonneg_left hlow' (by positivity)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by linarith [hlow', show 0 ≤ c₀ * x ^ (-(5 / 2) : ℝ) by positivity])
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hy0
  · -- x < 1
    have hmin : min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) = x ^ (1 / 2 : ℝ) := by
      apply min_eq_left
      calc x ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1.le (by norm_num)
        _ ≤ x ^ (-(5 / 2) : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hx1.le (by norm_num)
    rw [hmin] at hlow
    have hlow' : c₀ * x ^ (1 / 2 : ℝ) ≤ -airyTwistedLaplace (uctFstarDelta δ) x := by
      have : 0 ≤ c₀ * (δ * (1 + x) ^ (-(9 / 2 : ℝ))) := by positivity
      nlinarith
    have hB : ∀ w : ℂ, x / 2 ≤ w.re → ‖w - (x : ℂ)‖ ≤ x / 2 → ‖uctGd δ w‖ ≤ M * (3 / 2 * x) ^ (1 / 2 : ℝ) := by
      intro w hw1 hw2
      have hwn : ‖w‖ ≤ 3 / 2 * x := by
        have := norm_le_norm_add_norm_sub' w (x : ℂ)
        have h2 : ‖(x : ℂ)‖ = x := by simp [abs_of_pos hx]
        linarith
      calc ‖uctGd δ w‖ ≤ M * ‖w‖ ^ (1 / 2 : ℝ) := hM δ hδ0 hδ1 w (by linarith)
        _ ≤ M * (3 / 2 * x) ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hwn (by norm_num)) hM0
    have hv := local_variation (differentiableOn_uctGd δ) hx hB y hy
    have hdiff : uctGd δ ((x : ℂ) + (y : ℂ) * Complex.I) - uctGd δ (x : ℂ) = uctFd δ ((x : ℂ) + (y : ℂ) * Complex.I) - uctFd δ (x : ℂ) := by
      rw [uctGd_eq_Fd, uctGd_eq_Fd]; ring
    rw [hdiff] at hv
    have e : (3 / 2 * x) ^ (1 / 2 : ℝ) = Real.sqrt (3 / 2) * x ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hx.le, ← Real.sqrt_eq_rpow]
    calc ‖uctFd δ ((x : ℂ) + (y : ℂ) * Complex.I) - uctFd δ (x : ℂ)‖ ≤ 4 * (M * (3 / 2 * x) ^ (1 / 2 : ℝ)) / x * |y| := hv
      _ = (4 * M * Real.sqrt (3 / 2)) * (|y| / x) * x ^ (1 / 2 : ℝ) := by rw [e]; field_simp
      _ = (4 * M * Real.sqrt (3 / 2) / c₀) * (|y| / x) * (c₀ * x ^ (1 / 2 : ℝ)) := by field_simp
      _ ≤ (4 * M * Real.sqrt (3 / 2) / c₀) * (|y| / x) * (-airyTwistedLaplace (uctFstarDelta δ) x) :=
          mul_le_mul_of_nonneg_left hlow' (by positivity)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by linarith [hlow', show 0 ≤ c₀ * x ^ (1 / 2 : ℝ) by positivity])
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hy0


set_option maxHeartbeats 1000000 in
/-- **`(uct:Fstar-vert)` of `uct:airy-trans` (3).** -/
theorem uct_airy_trans_vert : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ x : ℝ, 0 < x → ∀ y : ℝ,
    ‖airyTwistedLaplaceC (uctFstarDelta δ) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      C * (-airyTwistedLaplace (uctFstarDelta δ) x) +
        C * (if x < 1 ∧ x / 2 < |y| then min (|y| ^ (1 / 2 : ℝ)) 1 else 0) := by
  obtain ⟨c₀, C₀, hc₀, hcC, hreal⟩ := uct_airy_trans_real
  obtain ⟨Cg, hCg, hglob⟩ := uctFd_global
  obtain ⟨M, hM0, hM⟩ := uctGd_bound
  set q : ℝ := (2 : ℝ) ^ (-(9 / 2 : ℝ)) with hq
  have hq0 : 0 < q := by positivity
  refine ⟨Cg / c₀ + max (M * Real.sqrt (3 / 2)) ceK / (c₀ * q) + M + Cg, by have := ceK_pos; positivity, fun δ hδ0 hδ1 x hx y => ?_⟩
  have hre1 : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
  rw [uctFd_eq (by rw [hre1]; exact hx.le)]
  set w : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hw
  have hwn : x ≤ ‖w‖ := by rw [← hre1]; exact (Complex.re_le_norm w).trans' (by rw [hre1])
  have hwy : |y| ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w
    simpa [hw] using this
  obtain ⟨hlow, -⟩ := hreal δ hδ0 hδ1 x hx
  set Fm := -airyTwistedLaplace (uctFstarDelta δ) x with hFm
  have hδG : 0 ≤ δ * (1 + x) ^ (-(9 / 2 : ℝ)) := by positivity
  have hFm0 : 0 ≤ Fm := by
    have : 0 ≤ c₀ * (min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) + δ * (1 + x) ^ (-(9 / 2 : ℝ))) := by
      have : 0 ≤ min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) := le_min (by positivity) (by positivity)
      positivity
    linarith
  have hind : 0 ≤ (if x < 1 ∧ x / 2 < |y| then min (|y| ^ (1 / 2 : ℝ)) 1 else 0) := by
    split_ifs
    · exact le_min (by positivity) zero_le_one
    · exact le_rfl
  set Ind := (if x < 1 ∧ x / 2 < |y| then min (|y| ^ (1 / 2 : ℝ)) 1 else 0) with hInd
  set CC : ℝ := Cg / c₀ + max (M * Real.sqrt (3 / 2)) ceK / (c₀ * q) + M + Cg with hCC
  have hCCnn : 0 ≤ CC := by have := ceK_pos; positivity
  have hglob' : ‖uctFd δ w‖ ≤ Cg * (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) := hglob δ hδ0 hδ1 w (by rw [hre1]; exact hx.le)
  rcases le_or_gt 1 x with hx1 | hx1
  · -- x ≥ 1
    have hmin : min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) = x ^ (-(5 / 2) : ℝ) := by
      apply min_eq_right
      calc x ^ (-(5 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
        _ ≤ x ^ (1 / 2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    rw [hmin] at hlow
    have hlow' : c₀ * x ^ (-(5 / 2) : ℝ) ≤ Fm := by nlinarith [mul_nonneg hc₀.le hδG]
    have h1 : ‖uctFd δ w‖ ≤ Cg * x ^ (-(5 / 2) : ℝ) :=
      hglob'.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx (by linarith) (by norm_num)) hCg)
    have hxp : 0 ≤ x ^ (-(5 / 2) : ℝ) := by positivity
    have hind0 : Ind = 0 := by rw [hInd, ite_eq_right]; intro h; linarith [h.1]
    calc ‖uctFd δ w‖ ≤ Cg * x ^ (-(5 / 2) : ℝ) := h1
      _ = (Cg / c₀) * (c₀ * x ^ (-(5 / 2) : ℝ)) := by field_simp
      _ ≤ (Cg / c₀) * Fm := mul_le_mul_of_nonneg_left hlow' (by positivity)
      _ ≤ CC * Fm := by
          apply mul_le_mul_of_nonneg_right _ hFm0
          have : 0 ≤ max (M * Real.sqrt (3 / 2)) ceK / (c₀ * q) := by have := ceK_pos; positivity
          rw [hCC]; linarith
      _ ≤ CC * Fm + CC * Ind := by rw [hind0]; simp
  · -- x < 1
    have hmin : min (x ^ (1 / 2 : ℝ)) (x ^ (-(5 / 2) : ℝ)) = x ^ (1 / 2 : ℝ) := by
      apply min_eq_left
      calc x ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1.le (by norm_num)
        _ ≤ x ^ (-(5 / 2) : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hx1.le (by norm_num)
    rw [hmin] at hlow
    have hq1 : q ≤ (1 + x) ^ (-(9 / 2 : ℝ)) := by
      rw [hq]; exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    have hq_le1 : q ≤ 1 := by
      rw [hq]; exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hxs : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
    have hlow' : c₀ * q * (x ^ (1 / 2 : ℝ) + δ) ≤ Fm := by
      have h1 : c₀ * q * x ^ (1 / 2 : ℝ) ≤ c₀ * x ^ (1 / 2 : ℝ) := by
        have : q * x ^ (1 / 2 : ℝ) ≤ 1 * x ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hq_le1 hxs
        nlinarith [hc₀]
      have h2 : c₀ * q * δ ≤ c₀ * (δ * (1 + x) ^ (-(9 / 2 : ℝ))) := by
        have : q * δ ≤ δ * (1 + x) ^ (-(9 / 2 : ℝ)) := by nlinarith [mul_le_mul_of_nonneg_left hq1 hδ0]
        nlinarith [hc₀]
      nlinarith
    have hK : max (M * Real.sqrt (3 / 2)) ceK / (c₀ * q) * Fm ≥ max (M * Real.sqrt (3 / 2)) ceK * (x ^ (1 / 2 : ℝ) + δ) := by
      have hcq : 0 < c₀ * q := by positivity
      calc max (M * Real.sqrt (3 / 2)) ceK / (c₀ * q) * Fm ≥ max (M * Real.sqrt (3 / 2)) ceK / (c₀ * q) * (c₀ * q * (x ^ (1 / 2 : ℝ) + δ)) :=
            mul_le_mul_of_nonneg_left hlow' (by have := ceK_pos; positivity)
        _ = _ := by field_simp
    have hMk : M ≤ max (M * Real.sqrt (3 / 2)) ceK := by
      refine (le_mul_of_one_le_right hM0 ?_).trans (le_max_left _ _)
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    have hkk : ceK ≤ max (M * Real.sqrt (3 / 2)) ceK := le_max_right _ _
    have hkd : ‖uctFd δ w‖ ≤ ‖uctGd δ w‖ + δ * ceK := by
      have : uctFd δ w = uctGd δ w - (δ : ℂ) * (ceK : ℂ) := by rw [uctGd_eq_Fd]; ring
      rw [this]
      calc ‖uctGd δ w - (δ : ℂ) * (ceK : ℂ)‖ ≤ ‖uctGd δ w‖ + ‖(δ : ℂ) * (ceK : ℂ)‖ := norm_sub_le _ _
        _ = _ := by rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hδ0, abs_of_pos ceK_pos]
    have hwle : ‖w‖ ≤ x + |y| := by
      have : w = (x : ℂ) + (y : ℂ) * Complex.I := hw
      calc ‖w‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := by rw [this]; exact norm_add_le _ _
        _ = x + |y| := by simp [abs_of_pos hx]
    have hsqrt : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) ^ (1 / 2 : ℝ) ≤ a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ) := by
      intro a b ha hb
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    by_cases hsub : x / 2 < |y|
    · by_cases hy1 : |y| ≤ 1
      · -- case B
        have hind : Ind = |y| ^ (1 / 2 : ℝ) := by
          rw [hInd, ite_eq_left ⟨hx1, hsub⟩]
          exact min_eq_left (Real.rpow_le_one (abs_nonneg _) hy1 (by norm_num))
        have hw3 : ‖w‖ ≤ 3 := by linarith
        have hG := hM δ hδ0 hδ1 w hw3
        have hpow : ‖w‖ ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) + |y| ^ (1 / 2 : ℝ) :=
          (Real.rpow_le_rpow (norm_nonneg _) hwle (by norm_num)).trans (hsqrt x |y| hx.le (abs_nonneg _))
        have hys : 0 ≤ |y| ^ (1 / 2 : ℝ) := by positivity
        calc ‖uctFd δ w‖ ≤ ‖uctGd δ w‖ + δ * ceK := hkd
          _ ≤ M * (x ^ (1 / 2 : ℝ) + |y| ^ (1 / 2 : ℝ)) + δ * ceK := by
              have := mul_le_mul_of_nonneg_left hpow hM0
              linarith
          _ ≤ max (M * Real.sqrt (3 / 2)) ceK * (x ^ (1 / 2 : ℝ) + δ) + M * |y| ^ (1 / 2 : ℝ) := by
              have h1 : M * x ^ (1 / 2 : ℝ) ≤ max (M * Real.sqrt (3 / 2)) ceK * x ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hMk hxs
              have h2 : δ * ceK ≤ max (M * Real.sqrt (3 / 2)) ceK * δ := by
                have := mul_le_mul_of_nonneg_left hkk hδ0; linarith
              linarith
          _ ≤ CC * Fm + CC * Ind := by
              rw [hind]
              have h3 : max (M * Real.sqrt (3 / 2)) ceK / (c₀ * q) * Fm ≤ CC * Fm := by
                apply mul_le_mul_of_nonneg_right _ hFm0
                rw [hCC]; have := ceK_pos; have : 0 ≤ Cg / c₀ := by positivity
                linarith [hM0, hCg]
              have h4 : M * |y| ^ (1 / 2 : ℝ) ≤ CC * |y| ^ (1 / 2 : ℝ) := by
                apply mul_le_mul_of_nonneg_right _ hys
                rw [hCC]; have := ceK_pos; have : 0 ≤ Cg / c₀ := by positivity
                have : 0 ≤ max (M * Real.sqrt (3 / 2)) ceK / (c₀ * q) := by positivity
                linarith
              linarith
      · -- case C
        have hy1' : 1 < |y| := not_le.mp hy1
        have hind : Ind = 1 := by
          rw [hInd, ite_eq_left ⟨hx1, hsub⟩]
          exact min_eq_right (Real.one_le_rpow hy1'.le (by norm_num))
        have h1 : ‖uctFd δ w‖ ≤ Cg := by
          refine hglob'.trans ?_
          calc Cg * (1 + ‖w‖) ^ (-(5 / 2 : ℝ)) ≤ Cg * 1 := mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg w]) (by norm_num)) hCg
            _ = Cg := mul_one _
        calc ‖uctFd δ w‖ ≤ Cg := h1
          _ ≤ CC * Ind := by
              have hCgle : Cg ≤ CC := by
                have h1 : 0 ≤ Cg / c₀ := by positivity
                have h2 : 0 ≤ max (M * Real.sqrt (3 / 2)) ceK / (c₀ * q) := by have := ceK_pos; positivity
                rw [hCC]; linarith [hM0]
              rw [hind, mul_one]; exact hCgle
          _ ≤ CC * Fm + CC * Ind := by have := mul_nonneg hCCnn hFm0; linarith
    · -- case A
      have hy2 : |y| ≤ x / 2 := not_lt.mp hsub
      have hind : Ind = 0 := by rw [hInd, ite_eq_right]; intro h; exact hsub h.2
      have hw3 : ‖w‖ ≤ 3 / 2 * x := by linarith
      have hG := hM δ hδ0 hδ1 w (by linarith)
      have hpow : ‖w‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt (3 / 2) * x ^ (1 / 2 : ℝ) := by
        calc ‖w‖ ^ (1 / 2 : ℝ) ≤ (3 / 2 * x) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (norm_nonneg _) hw3 (by norm_num)
          _ = _ := by rw [Real.mul_rpow (by norm_num) hx.le, ← Real.sqrt_eq_rpow]
      calc ‖uctFd δ w‖ ≤ ‖uctGd δ w‖ + δ * ceK := hkd
        _ ≤ M * (Real.sqrt (3 / 2) * x ^ (1 / 2 : ℝ)) + δ * ceK := by
            have := mul_le_mul_of_nonneg_left hpow hM0
            linarith
        _ ≤ max (M * Real.sqrt (3 / 2)) ceK * (x ^ (1 / 2 : ℝ) + δ) := by
            have h1 : M * (Real.sqrt (3 / 2) * x ^ (1 / 2 : ℝ)) ≤ max (M * Real.sqrt (3 / 2)) ceK * x ^ (1 / 2 : ℝ) := by
              rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hxs
            have h2 : δ * ceK ≤ max (M * Real.sqrt (3 / 2)) ceK * δ := by
              have := mul_le_mul_of_nonneg_left hkk hδ0; linarith
            linarith
        _ ≤ max (M * Real.sqrt (3 / 2)) ceK / (c₀ * q) * Fm := hK
        _ ≤ CC * Fm := by
            apply mul_le_mul_of_nonneg_right _ hFm0
            rw [hCC]; have := ceK_pos; have : 0 ≤ Cg / c₀ := by positivity
            linarith [hM0, hCg]
        _ ≤ CC * Fm + CC * Ind := by rw [hind]; simp

end FormalResearch.SignUncertainty
