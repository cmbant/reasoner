module

public import FormalResearch.SignUncertainty.HankelLangerU

/-!
# The Langer coordinate `y(w)` (`gt:7.7b` (iii))

With `Ξ = M ∘ K^{-1}` (`HankelLangerU`), `s = -log(1+w)` and `v = (12/π²) s`, put
`y(w) = (π²/12) Ξ(v)`.  Then `ũ = c^{2/3} κ y` with `κ = (3/π²)^{1/3}`.  We prove
`‖y(w) + w‖ ≤ 1.9·10⁻³ ‖w‖` for `‖w‖ ≤ 10⁻³ ≥ w₀ = π² r₀` (the paper's `θ`), `‖y' + 1‖ ≤ 4·10⁻³`, injectivity, surjectivity onto small discs, and the contraction
`‖Ξ(v) - v‖ ≤ 1.35·10⁻³ ‖v‖`.
-/

@[expose] public section

open Complex Set Metric
open scoped Real

namespace FormalResearch.SignUncertainty

section Y

variable {η : ℕ → ℝ}

/-- `Ξ = M ∘ K^{-1}`. -/
noncomputable def chartXi (η : ℕ → ℝ) (v : ℂ) : ℂ := chartM η (chartKinv η v)

lemma norm_chartM_sub_chartK_le (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖chartM η u - chartK η u‖ ≤ 1.35e-3 * ‖u‖ := by
  have h1 := norm_psW_aE_sub_one_u h hu
  have h2 := norm_psW_aG_sub_one_u h hu
  have hA := norm_one_add_cpow_sub_one_le (α := 2 / 3) (by norm_num) (by norm_num) h1 (by norm_num)
  have hF : psW (aE η) u = 1 + (psW (aE η) u - 1) := by ring
  rw [← hF] at hA
  have e : chartM η u - chartK η u =
      u * (psW (aE η) u ^ (((2 / 3 : ℝ)) : ℂ) - 1) - u * (psW (aG η) u - 1) := by
    unfold chartM powMapU chartK; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h3 : ‖u‖ * ‖psW (aE η) u ^ (((2 / 3 : ℝ)) : ℂ) - 1‖ ≤ ‖u‖ * (2 / 3 * 8.95e-4 / (1 - 8.95e-4)) :=
    mul_le_mul_of_nonneg_left hA (norm_nonneg _)
  have h4 : ‖u‖ * ‖psW (aG η) u - 1‖ ≤ ‖u‖ * 7.46e-4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have h5 : (2 / 3 * 8.95e-4 / (1 - 8.95e-4) : ℝ) + 7.46e-4 ≤ 1.35e-3 := by norm_num
  nlinarith [norm_nonneg u]

lemma norm_chartKinv_le (h : LangerEta η) {v : ℂ} (hv : v ∈ chartVdisc) :
    ‖chartKinv η v‖ * (1 - 7.46e-4) ≤ ‖v‖ := by
  obtain ⟨hu, hK⟩ := chartKinv_spec h hv
  set u := chartKinv η v
  have hun : ‖u‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu).le
  have e : chartK η u - u = u * (psW (aG η) u - 1) := by unfold chartK; ring
  have h2 := norm_psW_aG_sub_one_u h hun
  have h3 : ‖u‖ * ‖psW (aG η) u - 1‖ ≤ ‖u‖ * 7.46e-4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have h4 := norm_sub_norm_le u (-(chartK η u - u))
  have e2 : u - -(chartK η u - u) = chartK η u := by ring
  rw [e2, norm_neg, e, norm_mul] at h4
  rw [hK] at h4
  linarith

lemma norm_chartXi_sub_le (h : LangerEta η) {v : ℂ} (hv : v ∈ chartVdisc) :
    ‖chartXi η v - v‖ ≤ 1.36e-3 * ‖v‖ := by
  obtain ⟨hu, hK⟩ := chartKinv_spec h hv
  have hun : ‖chartKinv η v‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu).le
  have h1 := norm_chartM_sub_chartK_le h hun
  have h2 := norm_chartKinv_le h hv
  unfold chartXi
  have e : chartM η (chartKinv η v) - v = chartM η (chartKinv η v) - chartK η (chartKinv η v) := by
    rw [hK]
  rw [e]
  refine h1.trans ?_
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  nlinarith [norm_nonneg (chartKinv η v)]


/-- `v = (12/π²) s` with `s = -log(1 + w)`. -/
noncomputable def chartVofW (w : ℂ) : ℂ := (12 / π ^ 2 : ℝ) * (-Complex.log (1 + w))

/-- `y(w) = (π²/12) Ξ(v(w))`. -/
noncomputable def chartY (η : ℕ → ℝ) (w : ℂ) : ℂ := ((π ^ 2 / 12 : ℝ) : ℂ) * chartXi η (chartVofW w)

private lemma norm_log_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1e-3) :
    ‖Complex.log (1 + w) - w‖ ≤ 5.01e-4 * ‖w‖ := by
  have h1 : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have := Complex.norm_log_one_add_sub_self_le h1
  refine this.trans ?_
  have hw0 := norm_nonneg w
  have h2 : (1 - ‖w‖)⁻¹ ≤ (1 - 1e-3)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
  calc ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ * 1e-3 * (1 - 1e-3)⁻¹ / 2 := by
        have : ‖w‖ ^ 2 ≤ ‖w‖ * 1e-3 := by nlinarith
        gcongr
    _ ≤ 5.01e-4 * ‖w‖ := by nlinarith

private lemma norm_vofw_le {w : ℂ} (hw : ‖w‖ ≤ 1e-3) :
    ‖chartVofW w‖ ≤ (12 / 9.869) * (1.000501 * ‖w‖) := by
  have hL := norm_log_sub_le hw
  have hs : ‖-Complex.log (1 + w)‖ ≤ 1.000501 * ‖w‖ := by
    rw [norm_neg]
    have := norm_sub_norm_le (Complex.log (1 + w)) w
    have h' : ‖Complex.log (1 + w)‖ ≤ ‖w‖ + ‖Complex.log (1 + w) - w‖ := by
      have := norm_add_le w (Complex.log (1 + w) - w)
      simpa using this
    nlinarith
  unfold chartVofW
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hp : 12 / π ^ 2 ≤ 12 / 9.869 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith [Real.pi_gt_d4])
  exact mul_le_mul hp hs (norm_nonneg _) (by norm_num)

lemma chartVofW_mem {w : ℂ} (hw : ‖w‖ ≤ 1e-3) : chartVofW w ∈ chartVdisc := by
  rw [mem_chartVdisc]
  have := norm_vofw_le hw
  have hw0 := norm_nonneg w
  nlinarith

/-- **`gt:7.7b` (iii).** `‖y(w) + w‖ ≤ 1.9·10⁻³ ‖w‖` for `‖w‖ ≤ w₀ = 9.87·10⁻⁴`. -/
theorem norm_chartY_add_le (h : LangerEta η) {w : ℂ} (hw : ‖w‖ ≤ 1e-3) :
    ‖chartY η w + w‖ ≤ 1.9e-3 * ‖w‖ := by
  have hv := chartVofW_mem hw
  have hX := norm_chartXi_sub_le h hv
  have hL := norm_log_sub_le hw
  set s : ℂ := -Complex.log (1 + w) with hs
  have hsw : ‖s + w‖ ≤ 5.01e-4 * ‖w‖ := by
    have : s + w = -(Complex.log (1 + w) - w) := by rw [hs]; ring
    rw [this, norm_neg]; exact hL
  have hsn : ‖s‖ ≤ 1.000501 * ‖w‖ := by
    have := norm_add_le (s + w) (-w)
    simp only [add_neg_cancel_right, norm_neg] at this
    nlinarith
  have hpi : (π ^ 2 / 12 : ℝ) * (12 / π ^ 2 : ℝ) = 1 := by
    have : π ^ 2 ≠ 0 := by positivity
    field_simp
  have hvs : ((π ^ 2 / 12 : ℝ) : ℂ) * chartVofW w = s := by
    unfold chartVofW
    rw [← mul_assoc, ← Complex.ofReal_mul, hpi]; simp [hs]
  have e : chartY η w + w = ((π ^ 2 / 12 : ℝ) : ℂ) * (chartXi η (chartVofW w) - chartVofW w) + (s + w) := by
    unfold chartY; rw [mul_sub, hvs]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : (π ^ 2 / 12 : ℝ) * ‖chartXi η (chartVofW w) - chartVofW w‖ ≤ (π ^ 2 / 12 : ℝ) * (1.36e-3 * ‖chartVofW w‖) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have h2 : (π ^ 2 / 12 : ℝ) * ‖chartVofW w‖ = ‖s‖ := by
    rw [← hvs, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h3 : (π ^ 2 / 12 : ℝ) * (1.36e-3 * ‖chartVofW w‖) = 1.36e-3 * ‖s‖ := by rw [← h2]; ring
  have hw0 := norm_nonneg w
  nlinarith

/-- Derivative of `y`: `-M'(u)/(K'(u)(1+w))` at `u = K^{-1}(v(w))`. -/
noncomputable def chartYD (η : ℕ → ℝ) (w : ℂ) : ℂ :=
  -(chartMD η (chartKinv η (chartVofW w)) /
      (chartKD η (chartKinv η (chartVofW w)) * (1 + w)))

lemma one_add_ne_zero_of_small {w : ℂ} (hw : ‖w‖ ≤ 1e-3) : (1 + w) ≠ 0 := by
  intro h0
  have : w = -1 := by linear_combination h0
  rw [this] at hw; simp at hw; norm_num at hw

lemma hasDerivAt_chartVofW {w : ℂ} (hw : ‖w‖ ≤ 1e-3) :
    HasDerivAt chartVofW (((12 / π ^ 2 : ℝ) : ℂ) * (-(1 + w)⁻¹)) w := by
  have h1 : HasDerivAt (fun w : ℂ => 1 + w) 1 w := (hasDerivAt_id w).const_add 1
  have hs : (1 + w) ∈ slitPlane := one_add_mem_slitPlane_of_norm_lt (lt_of_le_of_lt hw (by norm_num))
  have h2 := (h1.clog hs)
  have h3 := (h2.neg).const_mul (((12 / π ^ 2 : ℝ) : ℂ))
  unfold chartVofW
  convert h3 using 1
  simp [div_eq_inv_mul]

theorem hasDerivAt_chartY (h : LangerEta η) {w : ℂ} (hw : ‖w‖ ≤ 1e-3) :
    HasDerivAt (chartY η) (chartYD η w) w := by
  have hv := chartVofW_mem hw
  obtain ⟨hu, _⟩ := chartKinv_spec h hv
  have hun : ‖chartKinv η (chartVofW w)‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu).le
  have hK := hasDerivAt_chartKinv h hv
  have hM := hasDerivAt_chartM h hun
  have hV := hasDerivAt_chartVofW hw
  have hXi : HasDerivAt (chartXi η)
      (chartMD η (chartKinv η (chartVofW w)) * (chartKD η (chartKinv η (chartVofW w)))⁻¹) (chartVofW w) :=
    HasDerivAt.comp (chartVofW w) hM hK
  have hXw := (hXi.comp w hV).const_mul (((π ^ 2 / 12 : ℝ)) : ℂ)
  have hne : chartKD η (chartKinv η (chartVofW w)) ≠ 0 := by
    intro h0
    have := re_chartKD_pos h hun
    rw [h0] at this; simp at this
  have h1w := one_add_ne_zero_of_small hw
  have hpi : ((π : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfun : chartY η = fun w => ((π ^ 2 / 12 : ℝ) : ℂ) * (chartXi η ∘ chartVofW) w := by
    funext w; rfl
  rw [hfun]
  convert hXw using 1
  unfold chartYD
  push_cast
  field_simp

private lemma norm_ratio_sub_le {a b w : ℂ} (ha : ‖a - 1‖ ≤ 1.5e-3) (hb : ‖b - 1‖ ≤ 1.3e-3)
    (hw : ‖w‖ ≤ 1e-3) : ‖-(b / (a * (1 + w))) + 1‖ ≤ 4e-3 := by
  have ha1 : 1 - 1.5e-3 ≤ ‖a‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - a)
    rw [norm_one, show (1 : ℂ) - (1 - a) = a by ring, norm_sub_rev] at this; linarith
  have hw1 : 1 - 1e-3 ≤ ‖1 + w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-w)
    rw [norm_one, sub_neg_eq_add, norm_neg] at this; linarith
  have hden : 0.9975 ≤ ‖a * (1 + w)‖ := by
    rw [norm_mul]; nlinarith
  have hden0 : a * (1 + w) ≠ 0 := by
    intro h0; rw [h0] at hden; simp at hden; norm_num at hden
  have e : -(b / (a * (1 + w))) + 1 = (a * (1 + w) - b) / (a * (1 + w)) := by
    rw [eq_div_iff hden0, add_mul, neg_mul, div_mul_cancel₀ _ hden0]; ring
  rw [e, norm_div]
  have hnum : ‖a * (1 + w) - b‖ ≤ 3.82e-3 * 0.9975 := by
    have e2 : a * (1 + w) - b = (a - 1) * (1 + w) + w - (b - 1) := by ring
    rw [e2]
    have h1 : ‖(a - 1) * (1 + w)‖ ≤ 1.5e-3 * 1.001 := by
      rw [norm_mul]
      have : ‖1 + w‖ ≤ 1.001 := by
        have := norm_add_le (1 : ℂ) w; rw [norm_one] at this; linarith
      exact mul_le_mul ha this (norm_nonneg _) (by norm_num)
    have := norm_sub_le ((a - 1) * (1 + w) + w) (b - 1)
    have h2 := norm_add_le ((a - 1) * (1 + w)) w
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma norm_chartYD_add_one_le (h : LangerEta η) {w : ℂ} (hw : ‖w‖ ≤ 1e-3) :
    ‖chartYD η w + 1‖ ≤ 4e-3 := by
  have hv := chartVofW_mem hw
  obtain ⟨hu, _⟩ := chartKinv_spec h hv
  have hun : ‖chartKinv η (chartVofW w)‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu).le
  exact norm_ratio_sub_le (norm_chartKD_sub_one_le h hun) (norm_chartMD_sub_one_le h hun) hw

lemma re_neg_chartYD_pos (h : LangerEta η) {w : ℂ} (hw : ‖w‖ ≤ 1e-3) : 0 < (-chartYD η w).re := by
  have := norm_chartYD_add_one_le h hw
  have h2 : |(chartYD η w + 1).re| ≤ ‖chartYD η w + 1‖ := Complex.abs_re_le_norm _
  have h3 := abs_le.1 (h2.trans this)
  simp only [Complex.add_re, Complex.one_re] at h3
  simp only [Complex.neg_re]
  linarith [h3.2]

/-- `y` is injective on `closedBall 0 (10⁻³)`. -/
lemma injOn_chartY (h : LangerEta η) : Set.InjOn (chartY η) (closedBall (0 : ℂ) 1e-3) := by
  have := injOn_of_re_deriv_pos (convex_closedBall (0 : ℂ) 1e-3) (f := fun w => -chartY η w)
    (f' := fun w => -chartYD η w)
    (fun w hw => (hasDerivAt_chartY h (by simpa using mem_closedBall_zero_iff.1 hw)).neg)
    (fun w hw => re_neg_chartYD_pos h (by simpa using mem_closedBall_zero_iff.1 hw))
  intro a ha b hb hab
  exact this ha hb (by simp [hab])

/-- **`gt:7.7b` (iii), surjectivity.** For `0 < r ≤ 9.9·10⁻⁴` and `‖y₀‖ + 1.9·10⁻³ r < r`
the equation `y(w) = y₀` has a solution `‖w‖ < r`. -/
theorem exists_chartY_eq (h : LangerEta η) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 9.9e-4) {y0 : ℂ}
    (hy : ‖y0‖ + 1.9e-3 * r < r) : ∃ w : ℂ, ‖w‖ < r ∧ chartY η w = y0 := by
  have hdiff : DifferentiableOn ℂ (fun w => -chartY η w) (ball (0 : ℂ) 1e-3) := fun w hw =>
    ((hasDerivAt_chartY h (by simpa using (mem_ball_zero_iff.1 hw).le)).neg.differentiableAt
      ).differentiableWithinAt
  obtain ⟨w, hw, hwy⟩ := exists_root_of_perturb (r := r) (R := 1e-3) hr (by linarith) hdiff
    (1.9e-3 * r) (fun z hz => by
      have hz' : ‖z‖ ≤ 1e-3 := by rw [hz]; linarith
      have := norm_chartY_add_le h hz'
      have e : -chartY η z - z = -(chartY η z + z) := by ring
      rw [e, norm_neg, hz] at *
      exact this) (w := -y0) (by rwa [norm_neg])
  exact ⟨w, mem_ball_zero_iff.1 hw, by simpa using hwy⟩

end Y

/-- info: 'FormalResearch.SignUncertainty.norm_chartY_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_chartY_add_le

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_chartY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_chartY

/-- info: 'FormalResearch.SignUncertainty.norm_chartYD_add_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_chartYD_add_one_le

/-- info: 'FormalResearch.SignUncertainty.injOn_chartY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms injOn_chartY

/-- info: 'FormalResearch.SignUncertainty.exists_chartY_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_chartY_eq

end FormalResearch.SignUncertainty
