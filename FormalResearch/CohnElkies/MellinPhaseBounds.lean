module

public import FormalResearch.CohnElkies.MellinAiryToolkit
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Mellin–Airy Phase Bounds (Lemmas T.3(3)–(5) and T.4(e))

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`,
remaining parts of Lemma T.3 (`mat:T3`) and Lemma T.4(e) (`mat:T4`, phase facts `(P1)`–`(P4)`).

## Main results
* `im_log_tan_div_eq`: complex imaginary identity `Im log(tan(π ζ / 2) / (π ζ / 2)) = arctan(sinh(π t) / sin(π σ)) - arctan(t / σ)`.
* `im_stripG_ge_gaussian`: Gaussian vertical-line bound `≥ 2 (3 / 56) σ min(ν, ν⁻¹)` for `σ ∈ (0, 1/2]`.
* `integral_im_stripG_ge`: integrated vertical-line bound `≥ 2 (3 / 56) σ ((1/2) min(ν², 1) + max 0 (log ν))`.
* `tau0_gt_sqrt`, `tau0_gt_exp`: `(P1)` lower bounds on the saddle `τ₀(L)`.
* `ceGamma`, `ceGamma_strictMonoOn`, `ceGamma_ge_min`, `edgePhiDeriv_ge_half_tau0`,
  `neg_edgePhiDeriv_ge_three_halves_tau0`, `neg_edgePhiDeriv_ge_quad`: `(P2)` phase slope bounds.
* `abs_edgePhiDeriv2_ge`, `abs_edgePhiDeriv2_band_ge`: `(P3)` second-derivative band lower bounds.
* `edgePhiDeriv_ge_log_bound`: `(P4)` global logarithmic lower bound `Φ'(τ; L) ≥ L - log(1 + π |τ| / 2)`.
-/

@[expose] public section

open Filter MeasureTheory Set Real

namespace FormalResearch.CohnElkies

/-! ### Elementary local helpers -/

private lemma nonneg_of_zero_of_deriv_nonneg {g : ℝ → ℝ} (g' : ℝ → ℝ) (h0 : g 0 = 0)
    (hnn : ∀ x ≥ 0, 0 ≤ g' x) (hd : ∀ x, HasDerivAt g (g' x) x) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ g x := by
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt).continuousOn
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      exact hnn s hs.le
  rw [← h0]
  exact hmono le_rfl hx hx

private lemma hasDerivAt_tanh' (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hch : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h : HasDerivAt (fun t => Real.sinh t / Real.cosh t)
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hch
  have h' : HasDerivAt Real.tanh
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x := by
    simpa only [← Real.tanh_eq_sinh_div_cosh] using h
  refine h'.congr_deriv ?_
  have hid := Real.cosh_sq_sub_sinh_sq x
  rw [sq, sq] at hid
  rw [hid]

private lemma ceEll_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < ceEll x := by
  unfold ceEll
  exact Real.log_pos ((one_lt_div (tanh_pos_of_pos hx)).mpr (tanh_lt_id hx))

/-! ### Lemma T.3(3)–(5): Complex imaginary identity and vertical-line bounds -/

private lemma arg_eq_arctan_of_re_pos {u : ℂ} (hu : 0 < u.re) :
    u.arg = Real.arctan (u.im / u.re) := by
  have hlt := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu))
  rw [← Real.arctan_tan hlt.1 hlt.2, Complex.tan_arg]

/-- **Lemma T.3(3) complex imaginary identity:** for `σ ∈ (0, 1)` and `t > 0`,
`Im log(tan(π ζ / 2) / (π ζ / 2)) = arctan(sinh(π t) / sin(π σ)) - arctan(t / σ)`. -/
theorem im_log_tan_div_eq {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (ht : 0 < t) :
    (Complex.log (Complex.tan (π * ((σ : ℂ) + (t : ℂ) * Complex.I) / 2) /
      (π * ((σ : ℂ) + (t : ℂ) * Complex.I) / 2))).im =
      Real.arctan (Real.sinh (π * t) / Real.sin (π * σ)) - Real.arctan (t / σ) := by
  set x : ℝ := π * σ / 2
  set y : ℝ := π * t / 2
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx_pi : x < π / 2 := by dsimp [x]; nlinarith [Real.pi_pos]
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hz_eq : π * ((σ : ℂ) + (t : ℂ) * Complex.I) / 2 = z := by
    apply Complex.ext <;> simp [z, x, y]
  rw [hz_eq]
  have htan_cond : (∀ k : ℤ, (x : ℂ) ≠ (2 * k + 1) * π / 2) ∧
      ∀ l : ℤ, (y : ℂ) * Complex.I ≠ (2 * l + 1) * π / 2 := by
    constructor
    · intro k hk
      have hre := congr_arg Complex.re hk
      simp at hre
      have hbound : π / 2 ≤ |(2 * (k : ℝ) + 1) * π / 2| := by
        have hk_int : (1 : ℝ) ≤ |2 * (k : ℝ) + 1| := by
          have : (2 * k + 1 : ℤ) ≠ 0 := by omega
          exact_mod_cast Int.one_le_abs this
        have hpi : |π| = π := abs_of_pos Real.pi_pos
        have h2 : |(2 : ℝ)| = 2 := abs_of_pos two_pos
        rw [abs_div, abs_mul, hpi, h2]
        nlinarith [Real.pi_pos]
      have hx_abs : |x| = |(2 * (k : ℝ) + 1) * π / 2| := congrArg abs hre
      rw [abs_of_pos hx0] at hx_abs
      linarith
    · intro l hl
      have hre := congr_arg Complex.re hl
      simp at hre
      have h_ne0 : (2 * (l : ℝ) + 1) ≠ 0 := by
        have : (2 * l + 1 : ℤ) ≠ 0 := by omega
        exact_mod_cast this
      have hne : (2 * (l : ℝ) + 1) * π / 2 ≠ 0 := by positivity
      exact hne hre.symm
  have htan_z : Complex.tan z = ((Complex.tan (x : ℂ) + Complex.tanh (y : ℂ) * Complex.I) /
      (1 - Complex.tan (x : ℂ) * Complex.tanh (y : ℂ) * Complex.I)) :=
    Complex.tan_add_mul_I (Or.inl htan_cond)
  set a : ℝ := Real.tan x
  set b : ℝ := Real.tanh y
  have ha : 0 < a := Real.tan_pos_of_pos_of_lt_pi_div_two hx0 hx_pi
  have hcos_x : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx_pi⟩
  have hsin_x : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  have hcosh_y : 0 < Real.cosh y := Real.cosh_pos y
  have hsinh_y : 0 < Real.sinh y := by linarith [sinh_gt_id hy0]
  have hb1 : 1 - b ^ 2 = (Real.cosh y)⁻¹ ^ 2 := by
    dsimp [b]
    rw [Real.tanh_eq_sinh_div_cosh]
    have hch0 : Real.cosh y ≠ 0 := hcosh_y.ne'
    have hid := Real.cosh_sq_sub_sinh_sq y
    field_simp
    linarith
  have h1b2 : 0 < 1 - b ^ 2 := by rw [hb1]; positivity
  have hden_pos : 0 < 1 + a ^ 2 * b ^ 2 := by positivity
  have hw_parts : Complex.tan z =
      ((a * (1 - b ^ 2) / (1 + a ^ 2 * b ^ 2) : ℝ) : ℂ) +
        ((b * (1 + a ^ 2) / (1 + a ^ 2 * b ^ 2) : ℝ) : ℂ) * Complex.I := by
    rw [htan_z]
    have h1ab : (1 : ℂ) - ((a : ℂ) * (b : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have hre := congr_arg Complex.re h
      simp at hre
    have hcx : Complex.tan (x : ℂ) = (a : ℂ) := by simp [a, Complex.ofReal_tan]
    have hcy : Complex.tanh (y : ℂ) = (b : ℂ) := by
      simp [b, Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
        Complex.ofReal_sinh, Complex.ofReal_cosh]
    rw [hcx, hcy, div_eq_iff h1ab]
    set r1 : ℝ := a * (1 - b ^ 2) / (1 + a ^ 2 * b ^ 2)
    set r2 : ℝ := b * (1 + a ^ 2) / (1 + a ^ 2 * b ^ 2)
    have hden0 : 1 + a ^ 2 * b ^ 2 ≠ 0 := hden_pos.ne'
    have hre_id : a = r1 + a * b * r2 := by dsimp [r1, r2]; field_simp; ring
    have him_id : b = r2 - a * b * r1 := by dsimp [r1, r2]; field_simp; ring
    apply Complex.ext <;> simp <;> linarith
  have hw_re : 0 < (Complex.tan z).re := by
    rw [hw_parts]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
      add_zero]
    positivity
  have hz_re : 0 < z.re := by simp [z, hx0]
  have hw_ne : Complex.tan z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw_re; exact lt_irrefl 0 hw_re
  have hz_ne : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz_re; exact lt_irrefl 0 hz_re
  have harg_div : (Complex.tan z / z).arg = (Complex.tan z).arg - z.arg := by
    have h1 := Complex.arg_div_coe_angle hw_ne hz_ne
    have hlt_w := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw_re))
    have hlt_z := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz_re))
    have hmem : (Complex.tan z).arg - z.arg ∈ Ioc (-π) π :=
      ⟨by linarith, by linarith⟩
    rw [← Complex.arg_coe_angle_toReal_eq_arg, h1, ← Real.Angle.coe_sub,
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hmem]
  have hw_ratio : (Complex.tan z).im / (Complex.tan z).re = Real.sinh (π * t) / Real.sin (π * σ) := by
    rw [hw_parts]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add,
      Complex.add_re, Complex.mul_I_re, neg_zero, add_zero]
    have h1a2 : 1 + a ^ 2 = (Real.cos x)⁻¹ ^ 2 := by
      dsimp [a]
      rw [Real.tan_eq_sin_div_cos]
      have hid := Real.cos_sq_add_sin_sq x
      have hcx0 : Real.cos x ≠ 0 := hcos_x.ne'
      field_simp
      linarith
    have hden0 : 1 + a ^ 2 * b ^ 2 ≠ 0 := hden_pos.ne'
    rw [div_div_div_cancel_right₀ hden0, hb1, h1a2]
    have hsin2 : Real.sin (π * σ) = 2 * Real.sin x * Real.cos x := by
      rw [show π * σ = 2 * x by dsimp [x]; ring, Real.sin_two_mul]
    have hsinh2 : Real.sinh (π * t) = 2 * Real.sinh y * Real.cosh y := by
      rw [show π * t = 2 * y by dsimp [y]; ring, Real.sinh_two_mul]
    rw [hsin2, hsinh2]
    dsimp [a, b]
    rw [Real.tan_eq_sin_div_cos, Real.tanh_eq_sinh_div_cosh]
    have h1 : Real.cos x ≠ 0 := hcos_x.ne'
    have h2 : Real.sin x ≠ 0 := hsin_x.ne'
    have h3 : Real.cosh y ≠ 0 := hcosh_y.ne'
    field_simp
  have hz_ratio : z.im / z.re = t / σ := by
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add,
      Complex.add_re, Complex.mul_I_re, neg_zero, add_zero, x, y]
    have := Real.pi_ne_zero
    field_simp
  rw [Complex.log_im, harg_div, arg_eq_arctan_of_re_pos hw_re, arg_eq_arctan_of_re_pos hz_re,
    hw_ratio, hz_ratio]

/-- **Lemma T.3(4) Gaussian vertical-line bound:** for `0 < σ ≤ 1 / 2` and `ν > 0`,
`arctan(sinh(π ν) / sin(π σ)) - arctan(ν / σ) ≥ 2 (3 / 56) σ min(ν, ν⁻¹)`. -/
theorem im_stripG_ge_gaussian {σ ν : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hν : 0 < ν) :
    2 * (3 / 56 : ℝ) * σ * min ν ν⁻¹ ≤
      Real.arctan (Real.sinh (π * ν) / Real.sin (π * σ)) - Real.arctan (ν / σ) := by
  have hσ_lt1 : σ < 1 := by linarith
  have hstrip := (im_stripG_ge hσ0 hσ_lt1 hν).2.2.2
  have hg' := (stripG_deriv_bounds hσ0 hσ_lt1).1
  have h1s : 1 - σ ≤ 1 := by linarith
  have h1s_pos : 0 < 1 - σ := by linarith
  have hg'_lb : 3 / 4 * σ < π / Real.sin (π * σ) - 1 / σ := by
    have hle : 3 / 4 * σ ≤ 3 / 4 * σ / (1 - σ) := by
      rw [le_div_iff₀ h1s_pos]
      nlinarith
    linarith
  have hm_le_one : min ν ν⁻¹ ≤ 1 := by
    rcases le_or_gt ν 1 with h1 | h1
    · exact (min_le_left _ _).trans h1
    · exact (min_le_right _ _).trans (inv_le_one_of_one_le₀ h1.le)
  have hm_nn : 0 ≤ min ν ν⁻¹ := le_min hν.le (inv_nonneg.mpr hν.le)
  have hterm1 : 3 / 4 * σ * min ν ν⁻¹ ≤ (π / Real.sin (π * σ) - 1 / σ) * ν := by
    have h1 : 3 / 4 * σ * min ν ν⁻¹ ≤ 3 / 4 * σ * ν := by gcongr; exact min_le_left _ _
    have h2 : 3 / 4 * σ * ν ≤ (π / Real.sin (π * σ) - 1 / σ) * ν := by gcongr
    linarith
  have hterm2 : 3 / 4 * σ * min ν ν⁻¹ ≤ 1 := by
    nlinarith
  have hterm3 : 3 / 4 * σ * min ν ν⁻¹ ≤ σ / ν := by
    have h1 : 3 / 4 * σ * min ν ν⁻¹ ≤ 1 * σ * ν⁻¹ := by
      gcongr
      · norm_num
      · exact min_le_right _ _
    calc 3 / 4 * σ * min ν ν⁻¹ ≤ 1 * σ * ν⁻¹ := h1
      _ = σ / ν := by ring
  have hmin_lb : 3 / 4 * σ * min ν ν⁻¹ ≤
      min ((π / Real.sin (π * σ) - 1 / σ) * ν) (min 1 (σ / ν)) :=
    le_min hterm1 (le_min hterm2 hterm3)
  calc 2 * (3 / 56 : ℝ) * σ * min ν ν⁻¹
      = 1 / 7 * (3 / 4 * σ * min ν ν⁻¹) := by ring
    _ ≤ 1 / 7 * min ((π / Real.sin (π * σ) - 1 / σ) * ν) (min 1 (σ / ν)) := by gcongr
    _ ≤ Real.arctan (Real.sinh (π * ν) / Real.sin (π * σ)) - Real.arctan (ν / σ) := hstrip

/-- **Lemma T.3(5) integrated vertical-line bound:** for `0 < σ ≤ 1 / 2` and `ν > 0`,
`∫ t in 0..ν, (arctan(sinh(π t) / sin(π σ)) - arctan(t / σ)) ≥ 2 (3 / 56) σ ((1/2) min(ν², 1) + max 0 (log ν))`. -/
theorem integral_im_stripG_ge {σ ν : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hν : 0 < ν) :
    2 * (3 / 56 : ℝ) * σ * ((1 / 2 : ℝ) * min (ν ^ 2) 1 + max 0 (Real.log ν)) ≤
      ∫ t in (0 : ℝ)..ν, (Real.arctan (Real.sinh (π * t) / Real.sin (π * σ)) - Real.arctan (t / σ)) := by
  let f : ℝ → ℝ := fun t => Real.arctan (Real.sinh (π * t) / Real.sin (π * σ)) - Real.arctan (t / σ)
  have hf_cont : Continuous f := by
    refine Continuous.sub ?_ ?_
    · exact Real.continuous_arctan.comp ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div_const _)
    · exact Real.continuous_arctan.comp (continuous_id.div_const _)
  let κ : ℝ := 2 * (3 / 56 : ℝ) * σ
  have hκ_nn : 0 ≤ κ := by dsimp [κ]; positivity
  have hf_ge_lin : ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → κ * t ≤ f t := by
    intro t ht0 ht1
    rcases eq_or_lt_of_le ht0 with rfl | ht_pos
    · simp [f]
    · have hmin : min t t⁻¹ = t := min_eq_left (ht1.trans ((one_le_inv₀ ht_pos).mpr ht1))
      simpa [κ, f, hmin] using im_stripG_ge_gaussian hσ0 hσ1 ht_pos
  have hf_ge_inv : ∀ {t : ℝ}, 1 ≤ t → κ * t⁻¹ ≤ f t := by
    intro t ht1
    have ht_pos : 0 < t := by linarith
    have hmin : min t t⁻¹ = t⁻¹ := min_eq_right ((inv_le_one_of_one_le₀ ht1).trans ht1)
    simpa [κ, f, hmin] using im_stripG_ge_gaussian hσ0 hσ1 ht_pos
  rcases le_or_gt ν 1 with hν1 | hν1
  · have hmono : ∫ t in (0 : ℝ)..ν, κ * t ≤ ∫ t in (0 : ℝ)..ν, f t := by
      refine intervalIntegral.integral_mono_on hν.le
        ((continuous_const.mul continuous_id).intervalIntegrable 0 ν)
        (hf_cont.intervalIntegrable 0 ν) fun t ht => hf_ge_lin ht.1 (ht.2.trans hν1)
    have hint_lin : ∫ t in (0 : ℝ)..ν, κ * t = κ * ((1 / 2 : ℝ) * ν ^ 2) := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    have hν2_le : ν ^ 2 ≤ 1 := by nlinarith
    have hlog_le : Real.log ν ≤ 0 := Real.log_nonpos hν.le hν1
    rw [min_eq_left hν2_le, max_eq_left hlog_le, add_zero]
    dsimp [κ] at hint_lin hmono
    linarith
  · have hsplit : (∫ t in (0 : ℝ)..1, f t) + (∫ t in (1 : ℝ)..ν, f t) = ∫ t in (0 : ℝ)..ν, f t :=
      intervalIntegral.integral_add_adjacent_intervals
        (hf_cont.intervalIntegrable 0 1) (hf_cont.intervalIntegrable 1 ν)
    have h1 : ∫ t in (0 : ℝ)..1, κ * t ≤ ∫ t in (0 : ℝ)..1, f t :=
      intervalIntegral.integral_mono_on zero_le_one
        ((continuous_const.mul continuous_id).intervalIntegrable 0 1)
        (hf_cont.intervalIntegrable 0 1) fun t ht => hf_ge_lin ht.1 ht.2
    have hint1 : ∫ t in (0 : ℝ)..1, κ * t = κ * (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    have hinv_int : IntervalIntegrable (fun t : ℝ => κ * t⁻¹) volume 1 ν := by
      refine (ContinuousOn.intervalIntegrable_of_Icc hν1.le ?_).const_mul κ
      exact continuousOn_inv₀.mono fun t ht h0 => by
        rw [Set.mem_singleton_iff] at h0
        linarith [ht.1]
    have h2 : ∫ t in (1 : ℝ)..ν, κ * t⁻¹ ≤ ∫ t in (1 : ℝ)..ν, f t :=
      intervalIntegral.integral_mono_on hν1.le hinv_int (hf_cont.intervalIntegrable 1 ν)
        fun t ht => hf_ge_inv ht.1
    have hint2 : ∫ t in (1 : ℝ)..ν, κ * t⁻¹ = κ * Real.log ν := by
      rw [intervalIntegral.integral_const_mul, integral_inv (fun h => by
        rw [Set.mem_uIcc] at h
        rcases h with h | h <;> linarith [h.1, h.2])]
      simp [div_one]
    have hν2_ge : 1 ≤ ν ^ 2 := one_le_pow₀ hν1.le
    have hlog_ge : 0 ≤ Real.log ν := (Real.log_pos hν1).le
    rw [min_eq_right hν2_ge, max_eq_right hlog_ge]
    dsimp [κ] at hint1 hint2 h1 h2
    linarith

/-! ### Lemma T.4(e): Phase facts `(P1)`–`(P4)` -/

/-- **Lemma T.4(e) `(P1)` (square-root lower bound):**
if `L > 0`, `τ₀ > 0`, and `ceEll (π τ₀ / 2) = L`, then `(2 √3 / π) √L < τ₀`. -/
theorem tau0_gt_sqrt {L τ₀ : ℝ} (hL : 0 < L) (hτ₀ : 0 < τ₀)
    (hτ₀_eq : ceEll (π * τ₀ / 2) = L) :
    (2 * Real.sqrt 3 / π) * Real.sqrt L < τ₀ := by
  set x : ℝ := π * τ₀ / 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hlt := ceEll_lt hx
  rw [hτ₀_eq] at hlt
  have hsqrt1 : 1 < Real.sqrt (1 + x ^ 2 / 3) := by
    conv_lhs => rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one (by linarith [sq_pos_of_pos hx])
  have hL_lt : L < x ^ 2 / 3 := by
    have h1 : x ^ 2 / (3 * Real.sqrt (1 + x ^ 2 / 3)) < x ^ 2 / 3 :=
      div_lt_div_of_pos_left (sq_pos_of_pos hx) (by norm_num) (by linarith)
    linarith
  have h3L : 3 * L < x ^ 2 := by linarith
  have hsqrt_3L : Real.sqrt (3 * L) < x := by
    rw [← Real.sqrt_sq hx.le]
    exact Real.sqrt_lt_sqrt (by positivity) h3L
  rw [Real.sqrt_mul (by norm_num)] at hsqrt_3L
  dsimp [x] at hsqrt_3L
  rw [lt_div_iff₀ two_pos] at hsqrt_3L
  rw [div_mul_eq_mul_div, div_lt_iff₀ Real.pi_pos]
  linarith

/-- **Lemma T.4(e) `(P1)` (exponential lower bound for `L > 1`):**
if `1 < L`, `τ₀ > 0`, and `ceEll (π τ₀ / 2) = L`, then
`(2 / π) tanh(√3) e^L < τ₀` and `(59 / 100) e^L < τ₀`. -/
theorem tau0_gt_exp {L τ₀ : ℝ} (hL : 1 < L) (hτ₀ : 0 < τ₀)
    (hτ₀_eq : ceEll (π * τ₀ / 2) = L) :
    (2 / π) * Real.tanh (Real.sqrt 3) * Real.exp L < τ₀ ∧
      (59 / 100 : ℝ) * Real.exp L < τ₀ := by
  set x : ℝ := π * τ₀ / 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hlt := ceEll_lt hx
  rw [hτ₀_eq] at hlt
  have hsqrt1 : 1 < Real.sqrt (1 + x ^ 2 / 3) := by
    conv_lhs => rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one (by linarith [sq_pos_of_pos hx])
  have hL_lt : L < x ^ 2 / 3 := by
    have h1 : x ^ 2 / (3 * Real.sqrt (1 + x ^ 2 / 3)) < x ^ 2 / 3 :=
      div_lt_div_of_pos_left (sq_pos_of_pos hx) (by norm_num) (by linarith)
    linarith
  have hx_gt : Real.sqrt 3 < x := by
    rw [← Real.sqrt_sq hx.le]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have htanh_mono : StrictMono Real.tanh :=
    strictMono_of_deriv_pos fun s => by rw [(hasDerivAt_tanh' s).deriv]; positivity
  have htanh_lt : Real.tanh (Real.sqrt 3) < Real.tanh x := htanh_mono hx_gt
  have hx_eq_exp : x = Real.exp L * Real.tanh x := by
    have h1 : x / Real.tanh x = Real.exp L := by
      rw [← hτ₀_eq, ceEll, Real.exp_log (div_pos hx (tanh_pos_of_pos hx))]
    exact (div_eq_iff (tanh_pos_of_pos hx).ne').mp h1
  have h1 : (2 / π) * Real.tanh (Real.sqrt 3) * Real.exp L < τ₀ := by
    have h2 : Real.exp L * Real.tanh (Real.sqrt 3) < x := by
      rw [hx_eq_exp]
      exact mul_lt_mul_of_pos_left htanh_lt (Real.exp_pos L)
    dsimp [x] at h2
    rw [lt_div_iff₀ two_pos] at h2
    rw [mul_assoc, div_mul_eq_mul_div, div_lt_iff₀ Real.pi_pos]
    linarith
  have hconst : (59 / 100 : ℝ) < (2 / π) * Real.tanh (Real.sqrt 3) := by
    have hsqrt3_lo : (1.732 : ℝ) < Real.sqrt 3 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.732)]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hexp_1 : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hexp_3 : (20.079 : ℝ) < Real.exp 3 := by
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hpow : (2.718 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
        pow_lt_pow_left₀ hexp_1 (by norm_num) (by decide)
      linarith [show (20.079 : ℝ) < (2.718 : ℝ) ^ 3 by norm_num]
    have hexp_rem : (1.464 : ℝ) < Real.exp (2 * Real.sqrt 3 - 3) := by
      linarith [Real.add_one_le_exp (2 * Real.sqrt 3 - 3)]
    have hexp_2s : (27 : ℝ) < Real.exp (2 * Real.sqrt 3) := by
      have hadd : Real.exp (2 * Real.sqrt 3) = Real.exp 3 * Real.exp (2 * Real.sqrt 3 - 3) := by
        rw [← Real.exp_add]; ring_nf
      rw [hadd]
      nlinarith
    have htanh_lb : (13 / 14 : ℝ) < Real.tanh (Real.sqrt 3) := by
      have h_eq : Real.tanh (Real.sqrt 3) =
          (Real.exp (2 * Real.sqrt 3) - 1) / (Real.exp (2 * Real.sqrt 3) + 1) := by
        rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
        have hsq : Real.exp (Real.sqrt 3) * Real.exp (Real.sqrt 3) = Real.exp (2 * Real.sqrt 3) := by
          rw [← Real.exp_add]; ring_nf
        have hneg : Real.exp (-Real.sqrt 3) = (Real.exp (Real.sqrt 3))⁻¹ := Real.exp_neg _
        have hne : Real.exp (Real.sqrt 3) ≠ 0 := (Real.exp_pos _).ne'
        rw [hneg, ← hsq]
        field_simp
      rw [h_eq, lt_div_iff₀ (by linarith)]
      linarith
    have hpi_hi : π < 3.1416 := Real.pi_lt_d4
    have hpi_lb : (2 / 3.1416 : ℝ) < 2 / π := div_lt_div_of_pos_left two_pos Real.pi_pos hpi_hi
    have hprod : (2 / 3.1416 : ℝ) * (13 / 14) < (2 / π) * Real.tanh (Real.sqrt 3) :=
      mul_lt_mul' hpi_lb.le htanh_lb (by norm_num) (by positivity)
    linarith [show (59 / 100 : ℝ) < (2 / 3.1416 : ℝ) * (13 / 14) by norm_num]
  have h2 : (59 / 100 : ℝ) * Real.exp L < τ₀ := by
    have hmul : (59 / 100 : ℝ) * Real.exp L < ((2 / π) * Real.tanh (Real.sqrt 3)) * Real.exp L :=
      mul_lt_mul_of_pos_right hconst (Real.exp_pos L)
    linarith
  exact ⟨h1, h2⟩

/-- `γ(x) = x ℓ'(x) = 1 - 2 x / sinh(2 x)` (`mellin_airy_toolkit.tex`, Lemma T.4(e) `(P2)`). -/
noncomputable def ceGamma (x : ℝ) : ℝ := 1 - 2 * x / Real.sinh (2 * x)

/-- Monotonicity of `ceGamma` on `(0, ∞)` (`mat:T4`(e) `(P2)`). -/
theorem ceGamma_strictMonoOn : StrictMonoOn ceGamma (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro x hx
    have hx0 : 0 < x := mem_Ioi.mp hx
    have hsh : Real.sinh (2 * x) ≠ 0 :=
      (by linarith [sinh_gt_id (by linarith : 0 < 2 * x)] : 0 < Real.sinh (2 * x)).ne'
    exact (continuousAt_const.sub ((continuousAt_const.mul continuousAt_id).div
      (Real.continuous_sinh.continuousAt.comp (continuousAt_const.mul continuousAt_id)) hsh)).continuousWithinAt
  · intro x hx
    rw [interior_Ioi, mem_Ioi] at hx
    have hx2 : 0 < 2 * x := by linarith
    have hsh : 0 < Real.sinh (2 * x) := by linarith [sinh_gt_id hx2]
    have hd : HasDerivAt ceGamma
        (-((2 * Real.sinh (2 * x) - (2 * x) * (2 * Real.cosh (2 * x))) / Real.sinh (2 * x) ^ 2)) x := by
      have h1 : HasDerivAt (fun s : ℝ => 2 * s) 2 x := by
        simpa using (hasDerivAt_id x).const_mul 2
      have h2 : HasDerivAt (fun s : ℝ => Real.sinh (2 * s)) (2 * Real.cosh (2 * x)) x :=
        ((Real.hasDerivAt_sinh (2 * x)).comp x h1).congr_deriv (by ring)
      exact ((hasDerivAt_const x 1).sub (h1.div h2 hsh.ne')).congr_deriv (by ring)
    rw [hd.deriv]
    have ht : Real.tanh (2 * x) < 2 * x := tanh_lt_id hx2
    rw [Real.tanh_eq_sinh_div_cosh, div_lt_iff₀ (Real.cosh_pos _)] at ht
    have hnum : 0 < 2 * x * Real.cosh (2 * x) - Real.sinh (2 * x) := by linarith
    have heq : -((2 * Real.sinh (2 * x) - (2 * x) * (2 * Real.cosh (2 * x))) / Real.sinh (2 * x) ^ 2) =
        2 * (2 * x * Real.cosh (2 * x) - Real.sinh (2 * x)) / Real.sinh (2 * x) ^ 2 := by ring
    rw [heq]
    positivity

private lemma ceGamma_ge_of_ge_half {x : ℝ} (hx : 1 / 2 ≤ x) :
    (149 / 1000 : ℝ) ≤ ceGamma x := by
  have hhalf_lb : (149 / 1000 : ℝ) ≤ ceGamma (1 / 2) := by
    have he1_lo : (2.71828 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have he1_neg : Real.exp (-1) < (2.71828 : ℝ)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_strictAnti₀ (by norm_num) he1_lo
    have hsh1_lo : (1.1751 : ℝ) < Real.sinh 1 := by
      rw [Real.sinh_eq]
      linarith
    have hinv_hi : 1 / Real.sinh 1 < (851 / 1000 : ℝ) := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    have heq : ceGamma (1 / 2) = 1 - 1 / Real.sinh 1 := by
      unfold ceGamma
      norm_num
    rw [heq]
    linarith
  have hmono : ceGamma (1 / 2) ≤ ceGamma x :=
    ceGamma_strictMonoOn.monotoneOn (mem_Ioi.mpr (by norm_num)) (mem_Ioi.mpr (by linarith)) hx
  exact hhalf_lb.trans hmono

/-- Lower bound `γ(x) ≥ min(x² / 3, 0.149)` for `x > 0` (`mat:T4`(e) `(P2)`). -/
theorem ceGamma_ge_min {x : ℝ} (hx : 0 < x) :
    min (x ^ 2 / 3) (149 / 1000 : ℝ) ≤ ceGamma x := by
  rcases le_or_gt x (1 / 2) with hx12 | hx12
  · set y : ℝ := 2 * x
    have hy0 : 0 < y := by dsimp [y]; positivity
    have hy1 : y ≤ 1 := by dsimp [y]; linarith
    have hsh_pos : 0 < Real.sinh y := by linarith [sinh_gt_id hy0]
    have hsh_sub : y ^ 3 / 6 ≤ Real.sinh y - y := by
      have hst := sinh_taylor_lower hy0.le
      have h5 : 0 ≤ y ^ 5 / 120 := by positivity
      linarith
    have hsh_ub : Real.sinh y ≤ y * Real.cosh y := by
      have ht := tanh_lt_id hy0
      rw [Real.tanh_eq_sinh_div_cosh, div_lt_iff₀ (Real.cosh_pos y)] at ht
      exact ht.le
    have hcosh_ub : Real.cosh y ≤ 2 := by
      have hcosh_mono : MonotoneOn Real.cosh (Ici 0) :=
        monotoneOn_of_deriv_nonneg (convex_Ici 0) Real.continuous_cosh.continuousOn
          (fun s _ => Real.differentiableAt_cosh.differentiableWithinAt) fun s hs => by
            rw [interior_Ici, mem_Ioi] at hs
            rw [(Real.hasDerivAt_cosh s).deriv]
            linarith [sinh_gt_id hs]
      have h1 : Real.cosh y ≤ Real.cosh 1 := hcosh_mono hy0.le zero_le_one hy1
      have h2 : Real.cosh 1 ≤ 2 := by
        rw [Real.cosh_eq]
        have he1 : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
        have he2 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
        linarith
      linarith
    have hce_eq : ceGamma x = (Real.sinh y - y) / Real.sinh y := by
      unfold ceGamma
      dsimp [y]
      rw [one_sub_div hsh_pos.ne']
    have hden_ub : Real.sinh y ≤ 2 * y := by
      calc Real.sinh y ≤ y * Real.cosh y := hsh_ub
        _ ≤ y * 2 := by gcongr
        _ = 2 * y := by ring
    have hgam_ge : x ^ 2 / 3 ≤ ceGamma x := by
      rw [hce_eq]
      calc x ^ 2 / 3 = (y ^ 3 / 6) / (2 * y) := by
            dsimp [y]
            have := hx.ne'
            field_simp; ring
        _ ≤ (Real.sinh y - y) / Real.sinh y := by
            have hy3 : 0 ≤ y ^ 3 / 6 := by dsimp [y]; positivity
            exact div_le_div₀ (by linarith) hsh_sub hsh_pos hden_ub
    exact (min_le_left _ _).trans hgam_ge
  · exact (min_le_right _ _).trans (ceGamma_ge_of_ge_half hx12.le)

private lemma ceEll_sub_ge_ceGamma_mul_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ceGamma a * Real.log (b / a) ≤ ceEll b - ceEll a := by
  let φ : ℝ → ℝ := fun u => ceEll u - ceGamma a * Real.log u
  have hφ_mono : MonotoneOn φ (Ici a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici a) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ ?_
      · intro u hu; exact (ceEll_hasDerivAt (by linarith [mem_Ici.mp hu])).continuousAt.continuousWithinAt
      · intro u hu
        have hu0 : u ≠ 0 := by linarith [mem_Ici.mp hu]
        exact (continuousAt_const.mul (Real.continuousAt_log hu0)).continuousWithinAt
    · intro u hu
      have hu_ge : a ≤ u := mem_Ici.mp (interior_subset hu)
      have hu_pos : 0 < u := by linarith
      exact ((ceEll_hasDerivAt hu_pos).sub
        ((Real.hasDerivAt_log hu_pos.ne').const_mul (ceGamma a))).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici, mem_Ioi] at hu
      have hu_pos : 0 < u := by linarith
      have hd : HasDerivAt φ (ceGamma u / u - ceGamma a / u) u := by
        refine ((ceEll_hasDerivAt hu_pos).sub
          ((Real.hasDerivAt_log hu_pos.ne').const_mul (ceGamma a))).congr_deriv ?_
        unfold ceGamma
        have hu0 : u ≠ 0 := hu_pos.ne'
        field_simp
      rw [hd.deriv, ← sub_div]
      have hgm : ceGamma a ≤ ceGamma u :=
        ceGamma_strictMonoOn.monotoneOn (mem_Ioi.mpr ha) (mem_Ioi.mpr hu_pos) hu.le
      exact div_nonneg (sub_nonneg.mpr hgm) hu_pos.le
  have hdiff := hφ_mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hab) hab
  dsimp [φ] at hdiff
  have hb0 : 0 < b := by linarith
  rw [Real.log_div hb0.ne' ha.ne']
  linarith

/-- **Lemma T.4(e) `(P2)` inner slope bound:**
`Φ'(τ; L) ≥ γ(π τ₀ / 4) log 2` for `|τ| ≤ τ₀ / 2`. -/
theorem edgePhiDeriv_ge_half_tau0 {L τ₀ τ : ℝ} (_hL : 0 < L) (hτ₀ : 0 < τ₀)
    (hτ₀_eq : ceEll (π * τ₀ / 2) = L) (hτ : |τ| ≤ τ₀ / 2) :
    ceGamma (π * τ₀ / 4) * Real.log 2 ≤ edgePhiDeriv L τ := by
  set a : ℝ := π * τ₀ / 4
  have ha : 0 < a := by dsimp [a]; positivity
  have h2a : ceGamma a * Real.log 2 ≤ ceEll (2 * a) - ceEll a := by
    have := ceEll_sub_ge_ceGamma_mul_log ha (by linarith : a ≤ 2 * a)
    rwa [show 2 * a / a = 2 by have := ha.ne'; field_simp] at this
  have h2a_eq : 2 * a = π * τ₀ / 2 := by dsimp [a]; ring
  rw [h2a_eq, hτ₀_eq] at h2a
  unfold edgePhiDeriv
  split_ifs with h0
  · have ha_pos : 0 < ceEll a := ceEll_pos_of_pos ha
    linarith
  · have hx_pos : 0 < π * |τ| / 2 := div_pos (mul_pos Real.pi_pos (abs_pos.mpr h0)) two_pos
    have hx_le : π * |τ| / 2 ≤ a := by
      dsimp [a]
      nlinarith [Real.pi_pos]
    have hmono : ceEll (π * |τ| / 2) ≤ ceEll a :=
      ceEll_strictMonoOn.monotoneOn (mem_Ioi.mpr hx_pos) (mem_Ioi.mpr ha) hx_le
    have hlog_eq : Real.log (Real.tanh (π * |τ| / 2) / (π * |τ| / 2)) = -ceEll (π * |τ| / 2) := by
      unfold ceEll; rw [← Real.log_inv, inv_div]
    rw [hlog_eq]
    linarith

/-- **Lemma T.4(e) `(P2)` outer slope bound:**
`-Φ'(τ; L) ≥ γ(π τ₀ / 2) log(3 / 2)` for `|τ| ≥ 3 τ₀ / 2`. -/
theorem neg_edgePhiDeriv_ge_three_halves_tau0 {L τ₀ τ : ℝ} (_hL : 0 < L) (hτ₀ : 0 < τ₀)
    (hτ₀_eq : ceEll (π * τ₀ / 2) = L) (hτ : 3 * τ₀ / 2 ≤ |τ|) :
    ceGamma (π * τ₀ / 2) * Real.log (3 / 2) ≤ -edgePhiDeriv L τ := by
  set b : ℝ := π * τ₀ / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have h3b : ceGamma b * Real.log (3 / 2) ≤ ceEll (3 * b / 2) - ceEll b := by
    have := ceEll_sub_ge_ceGamma_mul_log hb (by linarith : b ≤ 3 * b / 2)
    rwa [show 3 * b / 2 / b = 3 / 2 by have := hb.ne'; field_simp] at this
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hτ
    linarith
  have hx_pos : 0 < π * |τ| / 2 := div_pos (mul_pos Real.pi_pos (abs_pos.mpr hτ0)) two_pos
  have hx_ge : 3 * b / 2 ≤ π * |τ| / 2 := by
    dsimp [b]
    nlinarith [Real.pi_pos]
  have hmono : ceEll (3 * b / 2) ≤ ceEll (π * |τ| / 2) :=
    ceEll_strictMonoOn.monotoneOn (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr hx_pos) hx_ge
  have hlog_eq : Real.log (Real.tanh (π * |τ| / 2) / (π * |τ| / 2)) = -ceEll (π * |τ| / 2) := by
    unfold ceEll; rw [← Real.log_inv, inv_div]
  simp only [edgePhiDeriv, hτ0, ↓reduceIte, hlog_eq, ← hτ₀_eq]
  linarith

private lemma ceEll_sub_ge_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    (b ^ 2 - a ^ 2) / 6 ≤ ceEll b - ceEll a := by
  let φ : ℝ → ℝ := fun u => ceEll u - u ^ 2 / 6
  have hφ_mono : MonotoneOn φ (Ioc 0 (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 (1 / 2)) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ (by fun_prop)
      intro u hu; exact (ceEll_hasDerivAt hu.1).continuousAt.continuousWithinAt
    · intro u hu
      have hu_pos : 0 < u := (interior_subset hu).1
      exact ((ceEll_hasDerivAt hu_pos).sub ((hasDerivAt_pow 2 u).div_const 6)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ioc, mem_Ioo] at hu
      have hd : HasDerivAt φ ((ceGamma u - u ^ 2 / 3) / u) u := by
        refine ((ceEll_hasDerivAt hu.1).sub ((hasDerivAt_pow 2 u).div_const 6)).congr_deriv ?_
        unfold ceGamma
        have hu0 : u ≠ 0 := hu.1.ne'
        simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
        field_simp
        ring
      rw [hd.deriv]
      have hu_sq : u ^ 2 / 3 ≤ 149 / 1000 := by nlinarith [hu.1, hu.2]
      have hgam := ceGamma_ge_min hu.1
      rw [min_eq_left hu_sq] at hgam
      exact div_nonneg (sub_nonneg.mpr hgam) hu.1.le
  have hdiff := hφ_mono ⟨ha, hab.trans hb⟩ ⟨by linarith, hb⟩ hab
  dsimp [φ] at hdiff
  linarith

private lemma ceEll_sub_ge_log {a b : ℝ} (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    (149 / 1000 : ℝ) * Real.log (b / a) ≤ ceEll b - ceEll a := by
  let φ : ℝ → ℝ := fun u => ceEll u - (149 / 1000 : ℝ) * Real.log u
  have hφ_mono : MonotoneOn φ (Ici (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici (1 / 2)) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ ?_
      · intro u hu; exact (ceEll_hasDerivAt (by linarith [mem_Ici.mp hu])).continuousAt.continuousWithinAt
      · intro u hu
        have hu0 : u ≠ 0 := by linarith [mem_Ici.mp hu]
        exact (continuousAt_const.mul (Real.continuousAt_log hu0)).continuousWithinAt
    · intro u hu
      have hu_pos : 0 < u := by linarith [mem_Ici.mp (interior_subset hu)]
      exact ((ceEll_hasDerivAt hu_pos).sub
        ((Real.hasDerivAt_log hu_pos.ne').const_mul (149 / 1000 : ℝ))).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici, mem_Ioi] at hu
      have hu_pos : 0 < u := by linarith
      have hd : HasDerivAt φ ((ceGamma u - (149 / 1000 : ℝ)) / u) u := by
        refine ((ceEll_hasDerivAt hu_pos).sub
          ((Real.hasDerivAt_log hu_pos.ne').const_mul (149 / 1000 : ℝ))).congr_deriv ?_
        unfold ceGamma
        have hu0 : u ≠ 0 := hu_pos.ne'
        field_simp
      rw [hd.deriv]
      have hgam : (149 / 1000 : ℝ) ≤ ceGamma u := ceGamma_ge_of_ge_half hu.le
      exact div_nonneg (sub_nonneg.mpr hgam) hu_pos.le
  have hdiff := hφ_mono (mem_Ici.mpr ha) (mem_Ici.mpr (ha.trans hab)) hab
  dsimp [φ] at hdiff
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  rw [Real.log_div hb0 ha0]
  linarith

/-- **Lemma T.4(e) `(P2)` quadratic/constant tail bound:**
there exists an absolute constant `c₃ > 0` such that `-Φ'(τ; L) ≥ c₃ min(τ², 1)` for all `|τ| ≥ 3 τ₀ / 2`. -/
theorem neg_edgePhiDeriv_ge_quad :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ L > 0, ∀ τ₀ > 0, ceEll (π * τ₀ / 2) = L →
      ∀ τ, 3 * τ₀ / 2 ≤ |τ| → c₃ * min (τ ^ 2) 1 ≤ -edgePhiDeriv L τ := by
  refine ⟨1 / 100, by norm_num, fun L _hL τ₀ hτ₀ hτ₀_eq τ hτ => ?_⟩
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hτ
    linarith
  set x0 : ℝ := π * τ₀ / 2
  set X : ℝ := π * |τ| / 2
  have hx0 : 0 < x0 := by dsimp [x0]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hX_ge : 3 * x0 / 2 ≤ X := by dsimp [x0, X]; nlinarith [Real.pi_pos]
  have hφ_eq : -edgePhiDeriv L τ = ceEll X - ceEll x0 := by
    have hlog_eq : Real.log (Real.tanh X / X) = -ceEll X := by
      unfold ceEll; rw [← Real.log_inv, inv_div]
    simp only [edgePhiDeriv, hτ0, ↓reduceIte]
    change -(L + Real.log (Real.tanh X / X)) = ceEll X - ceEll x0
    rw [hlog_eq, hτ₀_eq]
    ring
  rw [hφ_eq]
  have hmin_le_one : min (τ ^ 2) 1 ≤ 1 := min_le_right _ _
  rcases le_or_gt X (1 / 2) with hX12 | hX12
  · have hsub := ceEll_sub_ge_sq hx0 (by linarith) hX12
    have hx0_le : x0 ≤ 2 * X / 3 := by linarith
    have hx0_sq : x0 ^ 2 ≤ 4 / 9 * X ^ 2 := by nlinarith
    have hX2_eq : X ^ 2 = π ^ 2 / 4 * τ ^ 2 := by
      dsimp [X]; rw [div_pow, mul_pow, sq_abs]; ring
    have hpi2 : (9 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    have hmin_le_tau : min (τ ^ 2) 1 ≤ τ ^ 2 := min_le_left _ _
    calc (1 / 100 : ℝ) * min (τ ^ 2) 1
        ≤ (1 / 100 : ℝ) * τ ^ 2 := by gcongr
      _ ≤ (5 * π ^ 2 / 216) * τ ^ 2 := by nlinarith [sq_nonneg τ]
      _ = 5 / 54 * X ^ 2 := by rw [hX2_eq]; ring
      _ ≤ (X ^ 2 - x0 ^ 2) / 6 := by linarith
      _ ≤ ceEll X - ceEll x0 := hsub
  · rcases le_or_gt (1 / 2) x0 with hx0_12 | hx0_12
    · have hsub := ceEll_sub_ge_log (b := X) hx0_12 (by linarith)
      have hlog : 1 - (3 / 2 : ℝ)⁻¹ ≤ Real.log (3 / 2) :=
        Real.one_sub_inv_le_log_of_pos (by norm_num)
      have hlog_ge : (1 / 3 : ℝ) ≤ Real.log (X / x0) := by
        have h1 : (3 / 2 : ℝ) ≤ X / x0 := (le_div_iff₀ hx0).mpr (by linarith)
        have h2 : Real.log (3 / 2) ≤ Real.log (X / x0) := Real.log_le_log (by norm_num) h1
        linarith
      calc (1 / 100 : ℝ) * min (τ ^ 2) 1
          ≤ 1 / 100 := by linarith
        _ ≤ (149 / 1000 : ℝ) * (1 / 3) := by norm_num
        _ ≤ (149 / 1000 : ℝ) * Real.log (X / x0) := by gcongr
        _ ≤ ceEll X - ceEll x0 := hsub
    · rcases le_or_gt x0 (3 / 8) with hx0_38 | hx0_38
      · have hsub1 := ceEll_sub_ge_sq hx0 (by linarith) le_rfl
        have hmono : ceEll (1 / 2) ≤ ceEll X :=
          ceEll_strictMonoOn.monotoneOn (mem_Ioi.mpr (by norm_num)) (mem_Ioi.mpr hX) hX12.le
        have hx0_sq : x0 ^ 2 ≤ (3 / 8) ^ 2 := by nlinarith [hx0.le]
        calc (1 / 100 : ℝ) * min (τ ^ 2) 1
            ≤ 1 / 100 := by linarith
          _ ≤ ((1 / 2) ^ 2 - (3 / 8) ^ 2) / 6 := by norm_num
          _ ≤ ((1 / 2) ^ 2 - x0 ^ 2) / 6 := by linarith
          _ ≤ ceEll (1 / 2) - ceEll x0 := hsub1
          _ ≤ ceEll X - ceEll x0 := by linarith
      · have hX_gt : (9 / 16 : ℝ) < X := by linarith
        have hsub2 := ceEll_sub_ge_log (b := X) le_rfl hX12.le
        have hmono : ceEll x0 ≤ ceEll (1 / 2) :=
          ceEll_strictMonoOn.monotoneOn (mem_Ioi.mpr hx0) (mem_Ioi.mpr (by norm_num)) hx0_12.le
        have hlog : 1 - (9 / 8 : ℝ)⁻¹ ≤ Real.log (9 / 8) :=
          Real.one_sub_inv_le_log_of_pos (by norm_num)
        have hlog_ge : (1 / 9 : ℝ) ≤ Real.log (X / (1 / 2)) := by
          have h1 : (9 / 8 : ℝ) ≤ X / (1 / 2) := by linarith
          have h2 : Real.log (9 / 8) ≤ Real.log (X / (1 / 2)) := Real.log_le_log (by norm_num) h1
          linarith
        calc (1 / 100 : ℝ) * min (τ ^ 2) 1
            ≤ 1 / 100 := by linarith
          _ ≤ (149 / 1000 : ℝ) * (1 / 9) := by norm_num
          _ ≤ (149 / 1000 : ℝ) * Real.log (X / (1 / 2)) := by gcongr
          _ ≤ ceEll X - ceEll (1 / 2) := hsub2
          _ ≤ ceEll X - ceEll x0 := by linarith

/-- **Lemma T.4(e) `(P3)` pointwise lower bound:**
`|Φ''(τ)| ≥ π² |τ| / (6 + π² τ²)` for `τ ≠ 0`. -/
theorem abs_edgePhiDeriv2_ge {τ : ℝ} (hτ : τ ≠ 0) :
    π ^ 2 * |τ| / (6 + π ^ 2 * τ ^ 2) ≤ |edgePhiDeriv2 τ| :=
  (edgePhiDeriv2_abs_ge hτ).2

/-- **Lemma T.4(e) `(P3)` band lower bound:**
on `3 τ₀ / 8 ≤ |τ| ≤ 2 τ₀` (`τ₀ > 0`),
`|Φ''(τ)| ≥ (3 / 16) * (π² (3 τ₀ / 8) / (6 + π² (3 τ₀ / 8)²))`. -/
theorem abs_edgePhiDeriv2_band_ge {τ₀ τ : ℝ} (hτ₀ : 0 < τ₀)
    (hτ_lo : 3 * τ₀ / 8 ≤ |τ|) (hτ_hi : |τ| ≤ 2 * τ₀) :
    (3 / 16 : ℝ) * (π ^ 2 * (3 * τ₀ / 8) / (6 + π ^ 2 * (3 * τ₀ / 8) ^ 2)) ≤ |edgePhiDeriv2 τ| := by
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hτ_lo
    linarith
  set a : ℝ := π * (3 * τ₀ / 8)
  set t : ℝ := π * |τ|
  have ha : 0 < a := by dsimp [a]; positivity
  have ht_lo : a ≤ t := by dsimp [a, t]; exact mul_le_mul_of_nonneg_left hτ_lo Real.pi_pos.le
  have ht_hi : t ≤ 16 * a / 3 := by
    dsimp [a, t]
    nlinarith [Real.pi_pos]
  have hcore : (3 / 16 : ℝ) * (a / (6 + a ^ 2)) ≤ t / (6 + t ^ 2) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have hid : 16 * t * (6 + a ^ 2) - 3 * a * (6 + t ^ 2) =
        (96 * t - 18 * a) + a * t * (16 * a - 3 * t) := by ring
    have h1 : 0 ≤ 96 * t - 18 * a := by linarith
    have h2 : 0 ≤ a * t * (16 * a - 3 * t) := mul_nonneg (by positivity) (by linarith)
    linarith
  have hleft : (3 / 16 : ℝ) * (π ^ 2 * (3 * τ₀ / 8) / (6 + π ^ 2 * (3 * τ₀ / 8) ^ 2)) =
      π * ((3 / 16 : ℝ) * (a / (6 + a ^ 2))) := by
    dsimp [a]; ring
  have hright : π ^ 2 * |τ| / (6 + π ^ 2 * τ ^ 2) = π * (t / (6 + t ^ 2)) := by
    dsimp [t]; rw [mul_pow, sq_abs]; ring
  have hcmp := mul_le_mul_of_nonneg_left hcore Real.pi_pos.le
  rw [← hleft, ← hright] at hcmp
  exact hcmp.trans (abs_edgePhiDeriv2_ge hτ0)

/-- **Lemma T.4(e) `(P4)` global logarithmic lower bound:**
`Φ'(τ; L) ≥ L - log(1 + π |τ| / 2)` for all `L, τ : ℝ`. -/
theorem edgePhiDeriv_ge_log_bound (L τ : ℝ) :
    L - Real.log (1 + π * |τ| / 2) ≤ edgePhiDeriv L τ := by
  unfold edgePhiDeriv
  split_ifs with h0
  · simp [h0]
  · set x : ℝ := π * |τ| / 2
    have hx : 0 < x := div_pos (mul_pos Real.pi_pos (abs_pos.mpr h0)) two_pos
    have hsh : 0 < Real.sinh x := by linarith [sinh_gt_id hx]
    have h_ell_le : ceEll x ≤ Real.log (1 + x) := by
      have hxcoth : x * Real.cosh x ≤ (1 + x) * Real.sinh x := by
        have hmono : 0 ≤ (1 + x) * Real.sinh x - x * Real.cosh x := by
          refine nonneg_of_zero_of_deriv_nonneg (g := fun s => (1 + s) * Real.sinh s - s * Real.cosh s)
            (fun s => Real.sinh s + s * (Real.cosh s - Real.sinh s)) (by simp)
            (fun s hs => by
              have hsh_s : 0 ≤ Real.sinh s := by
                rcases eq_or_lt_of_le hs with rfl | hpos
                · simp
                · linarith [sinh_gt_id hpos]
              have hch_sub : 0 ≤ Real.cosh s - Real.sinh s := by
                rw [Real.cosh_eq, Real.sinh_eq]
                linarith [Real.exp_pos (-s)]
              exact add_nonneg hsh_s (mul_nonneg hs hch_sub))
            (fun s => by
              have hA : HasDerivAt (fun t => (1 + t) * Real.sinh t)
                  (Real.sinh s + (1 + s) * Real.cosh s) s :=
                (((hasDerivAt_const s 1).add (hasDerivAt_id s)).mul
                  (Real.hasDerivAt_sinh s)).congr_deriv (by dsimp; ring)
              have hB : HasDerivAt (fun t => t * Real.cosh t)
                  (Real.cosh s + s * Real.sinh s) s :=
                ((hasDerivAt_id s).mul (Real.hasDerivAt_cosh s)).congr_deriv (by dsimp; ring)
              exact (hA.sub hB).congr_deriv (by ring))
            hx.le
        linarith
      have hratio : x / Real.tanh x ≤ 1 + x := by
        rw [Real.tanh_eq_sinh_div_cosh, div_div_eq_mul_div, div_le_iff₀ hsh]
        exact hxcoth
      unfold ceEll
      exact Real.log_le_log (div_pos hx (tanh_pos_of_pos hx)) hratio
    have hlog_eq : Real.log (Real.tanh x / x) = -ceEll x := by
      unfold ceEll; rw [← Real.log_inv, inv_div]
    change L - Real.log (1 + x) ≤ L + Real.log (Real.tanh x / x)
    rw [hlog_eq]
    linarith

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CohnElkies.im_log_tan_div_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.im_log_tan_div_eq

/-- info: 'FormalResearch.CohnElkies.im_stripG_ge_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.im_stripG_ge_gaussian

/-- info: 'FormalResearch.CohnElkies.integral_im_stripG_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.integral_im_stripG_ge

/-- info: 'FormalResearch.CohnElkies.tau0_gt_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.tau0_gt_sqrt

/-- info: 'FormalResearch.CohnElkies.tau0_gt_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.tau0_gt_exp

/-- info: 'FormalResearch.CohnElkies.ceGamma_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.ceGamma_strictMonoOn

/-- info: 'FormalResearch.CohnElkies.ceGamma_ge_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.ceGamma_ge_min

/-- info: 'FormalResearch.CohnElkies.edgePhiDeriv_ge_half_tau0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.edgePhiDeriv_ge_half_tau0

/-- info: 'FormalResearch.CohnElkies.neg_edgePhiDeriv_ge_three_halves_tau0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.neg_edgePhiDeriv_ge_three_halves_tau0

/-- info: 'FormalResearch.CohnElkies.neg_edgePhiDeriv_ge_quad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.neg_edgePhiDeriv_ge_quad

/-- info: 'FormalResearch.CohnElkies.abs_edgePhiDeriv2_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.abs_edgePhiDeriv2_ge

/-- info: 'FormalResearch.CohnElkies.abs_edgePhiDeriv2_band_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.abs_edgePhiDeriv2_band_ge

/-- info: 'FormalResearch.CohnElkies.edgePhiDeriv_ge_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.edgePhiDeriv_ge_log_bound

end FormalResearch.CohnElkies
