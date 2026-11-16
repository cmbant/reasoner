module

public import FormalResearch.Special.AiryIdentities

/-!
# Positivity and monotonicity of `Ai` on `[0, ∞)`

* `airyAi_lower_bound`: for `x > 0`,
  `Ai(x) ≥ (1/(2√π)) x^{-1/4} exp(-(2/3) x^{3/2}) (1 - 5/(48 x^{3/2}))` (with the upper bound of
  `AiryBound` this gives `2√π x^{1/4} e^{(2/3)x^{3/2}} Ai(x) → 1`, `airyAi_asymptotic`).  Proof: with
  `c = √x` the integrand is `e^{-(2/3)c³ - c s²} cos(s³/3)`; use `cos u ≥ 1 - u²/2` and the Gaussian
  moments `∫ e^{-c s²} = √(π/c)`, `∫ s⁶ e^{-c s²} = (15/8) √(π/c)/c³`.
* `airyAi_pos`: `Ai(x) > 0` for `x ≥ 0`, hence `Ai` has no zero on `[0, ∞)`.  Proof: a zero `x₁ ≥ 0` would make
  `Ai·Ai'` (derivative `Ai'² + x Ai² ≥ 0`) nonnegative on `[x₁, ∞)`, so `Ai²` is nondecreasing there and
  tends to `0`, i.e. `Ai ≡ 0` on `[x₁, ∞)`, contradicting `airyAi_lower_bound`.
* `airyAi'_neg`, `strictAntiOn_airyAi`: `Ai' < 0` and `Ai` is strictly decreasing on `[0, ∞)`.
-/

@[expose] public section

open Filter Topology MeasureTheory Set
open scoped Real

namespace FormalResearch.Special

lemma im_airyKernel_exponent (c x s : ℝ) :
    (airyLine c s ^ 3 / 3 - (x : ℂ) * airyLine c s).im = c ^ 2 * s - s ^ 3 / 3 - x * s := by
  simp only [airyLine, pow_succ, pow_zero, one_mul, Complex.sub_im, Complex.div_im, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num
  ring

/-- On the line `c = √x` the kernel is `e^{-(2/3)c³ - c s²} (cos(s³/3) - i sin(s³/3))`: real part. -/
lemma re_airyKernel_sqrt {x : ℝ} (hx : 0 < x) (s : ℝ) :
    (airyKernel (√x) (x : ℂ) s).re =
      Real.exp (-(2 / 3) * (√x) ^ 3 - √x * s ^ 2) * Real.cos (s ^ 3 / 3) := by
  have hc := Real.sq_sqrt hx.le
  unfold airyKernel
  rw [Complex.exp_re, re_airyKernel_exponent, im_airyKernel_exponent]
  have e1 : (√x) ^ 3 / 3 - (x : ℂ).re * √x + (x : ℂ).im * s - √x * s ^ 2 =
      -(2 / 3) * (√x) ^ 3 - √x * s ^ 2 := by
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    have : x * √x = (√x) ^ 3 := by
      calc x * √x = (√x) ^ 2 * √x := by rw [hc]
        _ = (√x) ^ 3 := by ring
    nlinarith
  have e2 : (√x) ^ 2 * s - s ^ 3 / 3 - x * s = -(s ^ 3 / 3) := by rw [hc]; ring
  rw [e1, e2, Real.cos_neg]

lemma integral_sixth_gauss {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ, s ^ 6 * Real.exp (-c * s ^ 2) = 15 / 8 * √(π / c) / c ^ 3 := by
  have h := integral_comp_abs (f := fun y : ℝ => y ^ 6 * Real.exp (-c * y ^ 2))
  simp only [sq_abs] at h
  have h6 : ∀ s : ℝ, |s| ^ 6 = s ^ 6 := fun s => by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, pow_mul, sq_abs]
  simp only [h6] at h
  rw [h]
  have := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 6) (b := c) two_pos (by norm_num) hc
  simp only [Real.rpow_two, show (6 : ℝ) = ((6 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast] at this
  rw [this]
  have hG : Real.Gamma (7 / 2) = 15 / 8 * √π := by
    have := Real.Gamma_nat_add_half 3
    norm_num [Nat.doubleFactorial] at this
    rw [this]
    ring
  have hE : c ^ (-(((6 : ℕ) : ℝ) + 1) / 2) = (c ^ (1 / 2 : ℝ))⁻¹ / c ^ 3 := by
    rw [show -(((6 : ℕ) : ℝ) + 1) / 2 = -(3 + 1 / 2 : ℝ) by norm_num, Real.rpow_neg hc.le,
      Real.rpow_add hc, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hS : √(π / c) = √π / c ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow c]
  rw [show (((6 : ℕ) : ℝ) + 1) / 2 = 7 / 2 by norm_num, hG, hE, hS]
  field_simp

lemma main_eq {x : ℝ} (hx : 0 < x) :
    1 / (2 * π) * (Real.exp (-(2 / 3) * (√x) ^ 3) * √(π / √x)) =
      1 / (2 * √π) * x ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) := by
  rw [sqrt_cube_eq_rpow hx, Real.sqrt_div Real.pi_pos.le, sqrt_sqrt_eq_rpow hx,
    Real.rpow_neg hx.le]
  have hπ : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hsq : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hr : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  field_simp
  nlinarith [hsq]

/-- `Ai(x) = (1/2π) e^{-(2/3)c³} ∫ e^{-c s²} cos(s³/3) ds` for `c = √x`, `x > 0`. -/
lemma airyAi_eq_integral_cos {x : ℝ} (hx : 0 < x) :
    airyAi x = 1 / (2 * π) * ∫ s : ℝ, Real.exp (-(2 / 3) * (√x) ^ 3 - √x * s ^ 2) *
      Real.cos (s ^ 3 / 3) := by
  have hc : 0 < √x := Real.sqrt_pos.mpr hx
  rw [airyAi_eq_re_airyMom hc]
  unfold airyMom
  have e : (1 / (2 * (π : ℂ))) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
  have hre := Complex.reCLM.integral_comp_comm (integrable_airyPoly hc 0 (x : ℂ))
  simp only [Complex.reCLM_apply] at hre
  rw [e, Complex.re_ofReal_mul, ← hre]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [airyPoly, pow_zero, one_mul]
  exact re_airyKernel_sqrt hx s

/-- **Lower bound** for `x > 0`:
`Ai(x) ≥ (1/(2√π)) x^{-1/4} exp(-(2/3) x^{3/2}) (1 - 5/(48 x^{3/2}))`. -/
theorem airyAi_lower_bound {x : ℝ} (hx : 0 < x) :
    1 / (2 * √π) * x ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) *
        (1 - 5 / 48 / x ^ (3 / 2 : ℝ)) ≤ airyAi x := by
  have hc : 0 < √x := Real.sqrt_pos.mpr hx
  set c := √x with hcdef
  rw [airyAi_eq_integral_cos hx, ← main_eq hx, ← sqrt_cube_eq_rpow hx]
  set E := Real.exp (-(2 / 3) * c ^ 3) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have i0 : Integrable (fun s : ℝ => Real.exp (-c * s ^ 2)) := integrable_exp_neg_mul_sq hc
  have i6 : Integrable (fun s : ℝ => s ^ 6 * Real.exp (-c * s ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hc (s := ((6 : ℕ) : ℝ)) (by norm_num)
    simpa [Real.rpow_natCast] using this
  have hsplit : ∀ s : ℝ, Real.exp (-(2 / 3) * c ^ 3 - c * s ^ 2) = E * Real.exp (-c * s ^ 2) := by
    intro s
    rw [hE, ← Real.exp_add]; ring_nf
  have hlow : ∫ s : ℝ, E * (Real.exp (-c * s ^ 2) - (1 / 18) * (s ^ 6 * Real.exp (-c * s ^ 2))) ≤
      ∫ s : ℝ, Real.exp (-(2 / 3) * c ^ 3 - c * s ^ 2) * Real.cos (s ^ 3 / 3) := by
    refine integral_mono ?_ ?_ fun s => ?_
    · exact ((i0.sub (i6.const_mul (1 / 18))).const_mul E)
    · refine Integrable.mono' (i0.const_mul E) (by fun_prop) (Filter.Eventually.of_forall fun s => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), hsplit]
      exact mul_le_of_le_one_right (mul_pos hEpos (Real.exp_pos _)).le (Real.abs_cos_le_one _)
    · simp only [hsplit]
      have hcos := Real.one_sub_sq_div_two_le_cos (x := s ^ 3 / 3)
      have hp : 0 < E * Real.exp (-c * s ^ 2) := mul_pos hEpos (Real.exp_pos _)
      nlinarith [mul_le_mul_of_nonneg_left hcos hp.le]
  have hint : ∫ s : ℝ, E * (Real.exp (-c * s ^ 2) - (1 / 18) * (s ^ 6 * Real.exp (-c * s ^ 2))) =
      E * (√(π / c) * (1 - 5 / 48 / c ^ 3)) := by
    rw [integral_const_mul, integral_sub i0 (i6.const_mul _), integral_const_mul,
      integral_gauss_c c, integral_sixth_gauss hc]
    field_simp
    ring
  have h2 := mul_le_mul_of_nonneg_left (hint ▸ hlow) (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
  calc 1 / (2 * π) * (E * √(π / c)) * (1 - 5 / 48 / c ^ 3)
      = 1 / (2 * π) * (E * (√(π / c) * (1 - 5 / 48 / c ^ 3))) := by ring
    _ ≤ _ := h2

lemma airyScale_mul_main {x : ℝ} (hx : 0 < x) :
    2 * √π * x ^ (1 / 4 : ℝ) * Real.exp ((2 / 3) * x ^ (3 / 2 : ℝ)) *
      (1 / (2 * √π) * x ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))) = 1 := by
  have hπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have h1 : x ^ (1 / 4 : ℝ) * x ^ (-(1 / 4) : ℝ) = 1 := by
    rw [← Real.rpow_add hx]; norm_num
  have h2 : Real.exp ((2 / 3) * x ^ (3 / 2 : ℝ)) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) = 1 := by
    rw [← Real.exp_add]; simp
  calc _ = (x ^ (1 / 4 : ℝ) * x ^ (-(1 / 4) : ℝ)) *
        (Real.exp ((2 / 3) * x ^ (3 / 2 : ℝ)) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))) *
        (2 * √π * (1 / (2 * √π))) := by ring
    _ = 1 := by rw [h1, h2]; field_simp

/-- `Ai(x) ∼ (1/(2√π)) x^{-1/4} exp(-(2/3) x^{3/2})` as `x → +∞`, from the two-sided bounds. -/
theorem airyAi_asymptotic :
    Tendsto (fun x : ℝ => 2 * √π * x ^ (1 / 4 : ℝ) * Real.exp ((2 / 3) * x ^ (3 / 2 : ℝ)) *
      airyAi x) atTop (𝓝 1) := by
  have hu : Tendsto (fun x : ℝ => x ^ (3 / 2 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hlow : Tendsto (fun x : ℝ => 1 - 5 / 48 / x ^ (3 / 2 : ℝ)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (5 / 48 : ℝ))).div_atTop hu
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  all_goals filter_upwards [eventually_gt_atTop 0] with x hx
  all_goals set g := 2 * √π * x ^ (1 / 4 : ℝ) * Real.exp ((2 / 3) * x ^ (3 / 2 : ℝ)) with hg
  all_goals have hgpos : 0 < g := by
              have := Real.sqrt_pos.mpr Real.pi_pos
              have := Real.rpow_pos_of_pos hx (1 / 4 : ℝ)
              positivity
  · have := mul_le_mul_of_nonneg_left (airyAi_lower_bound hx) hgpos.le
    rw [← mul_assoc, airyScale_mul_main hx] at this
    simpa [mul_comm] using this
  · have h := (le_abs_self _).trans (airyAi_abs_le hx)
    have := mul_le_mul_of_nonneg_left h hgpos.le
    rwa [airyScale_mul_main hx] at this

theorem airyAi_pos_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 < airyAi x := by
  have hx0 : 0 < x := one_pos.trans_le hx
  have h := airyAi_lower_bound hx0
  have h32 : 1 ≤ x ^ (3 / 2 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hpos : 0 < 1 / (2 * √π) * x ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) := by
    have := Real.sqrt_pos.mpr Real.pi_pos
    have := Real.rpow_pos_of_pos hx0 (-(1 / 4) : ℝ)
    positivity
  have hfac : 0 < 1 - 5 / 48 / x ^ (3 / 2 : ℝ) := by
    have : 5 / 48 / x ^ (3 / 2 : ℝ) ≤ 5 / 48 := div_le_self (by norm_num) h32
    linarith
  exact (mul_pos hpos hfac).trans_le h

lemma hasDerivAt_airyAi_mul {x : ℝ} :
    HasDerivAt (fun x => airyAi x * airyAi' x) (airyAi' x ^ 2 + x * airyAi x ^ 2) x := by
  have := (hasDerivAt_airyAi x).mul (hasDerivAt_airyAi' x)
  convert this using 1; ring

/-- `Ai` has no zero on `[0, ∞)`. -/
theorem airyAi_ne_zero_of_nonneg {x₁ : ℝ} (hx₁ : 0 ≤ x₁) : airyAi x₁ ≠ 0 := by
  intro h0
  -- `Ai·Ai'` is nondecreasing on `[x₁, ∞)` and vanishes at `x₁`
  have hmono : MonotoneOn (fun x => airyAi x * airyAi' x) (Ici x₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici x₁)
      (fun x _ => (hasDerivAt_airyAi_mul).continuousAt.continuousWithinAt)
      (fun x _ => (hasDerivAt_airyAi_mul).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [hasDerivAt_airyAi_mul.deriv]
    have : 0 ≤ x := hx₁.trans (le_of_lt hx)
    positivity
  have hh0 : ∀ x ∈ Ici x₁, 0 ≤ airyAi x * airyAi' x := by
    intro x hx
    have := hmono (Set.mem_Ici.mpr le_rfl) hx (Set.mem_Ici.mp hx)
    simp only [h0, zero_mul] at this
    exact this
  -- hence `Ai²` is nondecreasing on `[x₁, ∞)`, tends to `0`, so vanishes there
  have hmono2 : MonotoneOn (fun x => airyAi x ^ 2) (Ici x₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici x₁)
      (fun x _ => ((hasDerivAt_airyAi x).pow 2).continuousAt.continuousWithinAt)
      (fun x _ => ((hasDerivAt_airyAi x).pow 2).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    have hd : HasDerivAt (fun x => airyAi x ^ 2) (((2 : ℕ) : ℝ) * airyAi x ^ (2 - 1) * airyAi' x) x :=
      (hasDerivAt_airyAi x).pow 2
    rw [hd.deriv]
    have := hh0 x (le_of_lt hx)
    norm_num
    nlinarith
  have hlim : Tendsto (fun x => airyAi x ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_airyAi.pow 2
  have hvan : ∀ x ∈ Ici x₁, airyAi x ^ 2 ≤ 0 := fun x hx =>
    ge_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop (max x x₁)] with y hy
      exact hmono2 hx (le_trans (le_max_right _ _) hy) (le_trans (le_max_left _ _) hy))
  have := hvan (max x₁ 1) (le_max_left _ _)
  have h1 := airyAi_pos_of_one_le (le_max_right x₁ 1)
  nlinarith

/-- **`Ai > 0` on `[0, ∞)`.** -/
theorem airyAi_pos {x : ℝ} (hx : 0 ≤ x) : 0 < airyAi x := by
  by_contra hneg
  have hle : airyAi x ≤ 0 := not_lt.mp hneg
  have hcont : ContinuousOn airyAi (uIcc x 1) :=
    differentiable_airyAi.continuous.continuousOn
  have h1 := airyAi_pos_of_one_le (le_refl (1 : ℝ))
  have : (0 : ℝ) ∈ uIcc (airyAi x) (airyAi 1) :=
    ⟨by simp [min_def]; split_ifs <;> linarith, by simp [max_def]; split_ifs <;> linarith⟩
  obtain ⟨y, hy, hy0⟩ := intermediate_value_uIcc hcont this
  have hy' : 0 ≤ y := by
    rcases Set.mem_uIcc.mp hy with h | h <;> linarith [h.1]
  exact airyAi_ne_zero_of_nonneg hy' hy0

theorem airyAi_deriv_nonpos_aux : ∀ x : ℝ, 0 ≤ x → airyAi' x ≤ 0 := by
  intro x hx
  have hmono : MonotoneOn airyAi' (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hasDerivAt_airyAi' x).continuousAt.continuousWithinAt)
      (fun x _ => (hasDerivAt_airyAi' x).differentiableAt.differentiableWithinAt) ?_
    intro y hy
    rw [interior_Ici] at hy
    rw [(hasDerivAt_airyAi' y).deriv]
    exact mul_nonneg (le_of_lt hy) (airyAi_pos (le_of_lt hy)).le
  refine ge_of_tendsto tendsto_airyAi' ?_
  filter_upwards [eventually_ge_atTop x] with y hy
  exact hmono hx (hx.trans hy) hy

/-- `Ai' < 0` on `[0, ∞)`. -/
theorem airyAi'_neg {x : ℝ} (hx : 0 ≤ x) : airyAi' x < 0 := by
  have hs : StrictMonoOn airyAi' (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun x _ => (hasDerivAt_airyAi' x).continuousAt.continuousWithinAt) ?_
    intro y hy
    rw [interior_Ici] at hy
    rw [(hasDerivAt_airyAi' y).deriv]
    exact mul_pos hy (airyAi_pos (le_of_lt hy))
  have h1 : airyAi' x < airyAi' (x + 1) := hs hx (by simp; linarith) (by linarith)
  have h2 := airyAi_deriv_nonpos_aux (x + 1) (by linarith)
  linarith

/-- `Ai` is strictly decreasing on `[0, ∞)`. -/
theorem strictAntiOn_airyAi : StrictAntiOn airyAi (Ici 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 0)
    differentiable_airyAi.continuous.continuousOn ?_
  intro y hy
  rw [interior_Ici] at hy
  rw [deriv_airyAi]
  exact airyAi'_neg (le_of_lt hy)

end FormalResearch.Special