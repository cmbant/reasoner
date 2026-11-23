module

public import FormalResearch.ModularBootstrap.Upper.Saddle.TwoSaddleContour

/-!
# Lemma `SD_V'`: Uniform Two-Saddle Descent for a General Amplitude

Source: `CFT/modular_bootstrap/paper/edge_transform_sd.tex`, Lemma `esd:lemmap` (`SD_V'`),
l.204–378 (`(SD.5)–(SD.9)`).

Main results:
* `lemma_SD_V_prime`: For `0 < δ ≤ 1/4`, `C₃, C₄, M, M' ≥ 0`, there exist `N₀ ≥ 1` and `C ≥ 0`
  depending only on `(δ, C₃, C₄, M, M')` such that for any `EdgePhaseData δ C₃ C₄ Φ₀`, any
  `x > ξ_*`, any `n > 0` with `n * m_x^3 ≥ N₀`, and any amplitude `A` satisfying `(i)–(iii)`
  (`TwoSaddleAmplitude Φ₀ x n δ M M' A`),
  `e^{-iπ/4} 𝒥_A = 2 |A(b_x)| √(2π / (n α_x)) (cos Θ + O(1 / (n m_x^3)))`.
* `twoSaddleAmplitude_nonvacuous`: Concrete witness `Φ₀, x, n, M, M', A` satisfying both
  `EdgePhaseData δ C₃ C₄ Φ₀` and `TwoSaddleAmplitude Φ₀ x n δ M M' A`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Saddle

/-! ### 1. Core truncation radius `r₁` and local exponential helpers -/

/-- Core Gaussian truncation radius `r₁ = min(ℓ, (6/(n C₃))^{1/3})` (and `r₁ = ℓ` if `C₃ = 0`),
corresponding to `edge_transform_sd.tex`, l.334–335. -/
noncomputable def coreThreshold (δ C₃ M M' n x : ℝ) : ℝ :=
  if C₃ = 0 then saddleLength δ C₃ M M' x
  else min (saddleLength δ C₃ M M' x) ((6 / (n * C₃)) ^ (1 / 3 : ℝ))

lemma coreThreshold_nonneg {δ C₃ M M' n x : ℝ} (hδ : 0 < δ) (hx : xiStar < x)
    (hn : 0 < n) (hC₃ : 0 ≤ C₃) :
    0 ≤ coreThreshold δ C₃ M M' n x := by
  unfold coreThreshold
  have hℓ : 0 ≤ saddleLength δ C₃ M M' x :=
    mul_nonneg (saddleScaleD_pos C₃ M M' hδ).le (mX_pos hx).le
  split_ifs
  · exact hℓ
  · exact le_min hℓ (Real.rpow_nonneg (div_nonneg (by norm_num) (mul_nonneg hn.le hC₃)) _)

lemma coreThreshold_le_saddleLength {δ C₃ M M' n x : ℝ} :
    coreThreshold δ C₃ M M' n x ≤ saddleLength δ C₃ M M' x := by
  unfold coreThreshold
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma C₃_mul_coreThreshold_cubed_le {δ C₃ M M' n x : ℝ} (hδ : 0 < δ) (hx : xiStar < x)
    (hn : 0 < n) (hC₃ : 0 ≤ C₃) :
    C₃ * coreThreshold δ C₃ M M' n x ^ 3 ≤ 6 / n := by
  rcases eq_or_lt_of_le hC₃ with rfl | hC₃_pos
  · simp only [zero_mul]
    positivity
  · have hr₁_nn := coreThreshold_nonneg hδ hx hn hC₃ (M := M) (M' := M')
    have hr₁_le : coreThreshold δ C₃ M M' n x ≤ (6 / (n * C₃)) ^ (1 / 3 : ℝ) := by
      unfold coreThreshold
      simp only [hC₃_pos.ne', ↓reduceIte]
      exact min_le_right _ _
    have hpow : coreThreshold δ C₃ M M' n x ^ 3 ≤ 6 / (n * C₃) := by
      calc coreThreshold δ C₃ M M' n x ^ 3
          ≤ ((6 / (n * C₃)) ^ (1 / 3 : ℝ)) ^ 3 := pow_le_pow_left₀ hr₁_nn hr₁_le 3
        _ = ((6 / (n * C₃)) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) := by norm_cast
        _ = (6 / (n * C₃)) ^ ((1 / 3 : ℝ) * 3) := by
            rw [← Real.rpow_mul (div_nonneg (by norm_num) (mul_nonneg hn.le hC₃))]
        _ = 6 / (n * C₃) := by norm_num
    calc C₃ * coreThreshold δ C₃ M M' n x ^ 3
        ≤ C₃ * (6 / (n * C₃)) := mul_le_mul_of_nonneg_left hpow hC₃
      _ = 6 / n := by
          field_simp [hn.ne', hC₃_pos.ne']

lemma core_exponent_lower {δ C₃ M M' : ℝ} (hδ : 0 < δ) (hC₃ : 0 ≤ C₃) :
    ∃ c_core : ℝ, 0 < c_core ∧
      ∀ {x n : ℝ}, xiStar < x → 0 < n → 1 ≤ n * mX x ^ 3 →
        c_core * (n * mX x ^ 3) ^ (1 / 3 : ℝ) ≤
          n * alphaX x * coreThreshold δ C₃ M M' n x ^ 2 := by
  let d : ℝ := saddleScaleD δ C₃ M M'
  have hd_pos : 0 < d := saddleScaleD_pos C₃ M M' hδ
  let c_core : ℝ := if C₃ = 0 then d ^ 2 else min (d ^ 2) ((6 / C₃) ^ (2 / 3 : ℝ))
  have hc_pos : 0 < c_core := by
    dsimp [c_core]
    split_ifs with h0
    · positivity
    · have hC₃_pos : 0 < C₃ := lt_of_le_of_ne hC₃ (Ne.symm h0)
      exact lt_min (sq_pos_of_pos hd_pos) (Real.rpow_pos_of_pos (div_pos (by norm_num) hC₃_pos) _)
  refine ⟨c_core, hc_pos, fun {x n} hx hn hnm => ?_⟩
  have hm_pos : 0 < mX x := mX_pos hx
  have hm_le_a : mX x ≤ alphaX x := mX_le_alphaX x
  have h13 : (n * mX x ^ 3) ^ (1 / 3 : ℝ) ≤ n * mX x ^ 3 := by
    calc (n * mX x ^ 3) ^ (1 / 3 : ℝ)
        ≤ (n * mX x ^ 3) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnm (by norm_num)
      _ = n * mX x ^ 3 := Real.rpow_one _
  have h_core_sq : c_core * (n * mX x ^ 3) ^ (1 / 3 : ℝ) ≤
      n * mX x * coreThreshold δ C₃ M M' n x ^ 2 := by
    unfold coreThreshold
    split_ifs with h0
    · have hc_le : c_core ≤ d ^ 2 := by dsimp [c_core]; simp [h0]
      calc c_core * (n * mX x ^ 3) ^ (1 / 3 : ℝ)
          ≤ d ^ 2 * (n * mX x ^ 3) ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right hc_le (Real.rpow_nonneg (by positivity) _)
        _ ≤ d ^ 2 * (n * mX x ^ 3) := mul_le_mul_of_nonneg_left h13 (sq_nonneg _)
        _ = n * mX x * saddleLength δ C₃ M M' x ^ 2 := by dsimp [saddleLength, d]; ring
    · have hC₃_pos : 0 < C₃ := lt_of_le_of_ne hC₃ (Ne.symm h0)
      rcases le_total (saddleLength δ C₃ M M' x) ((6 / (n * C₃)) ^ (1 / 3 : ℝ)) with hle | hle
      · rw [min_eq_left hle]
        have hc_le : c_core ≤ d ^ 2 := by dsimp [c_core]; simp [h0]
        calc c_core * (n * mX x ^ 3) ^ (1 / 3 : ℝ)
            ≤ d ^ 2 * (n * mX x ^ 3) ^ (1 / 3 : ℝ) :=
              mul_le_mul_of_nonneg_right hc_le (Real.rpow_nonneg (by positivity) _)
          _ ≤ d ^ 2 * (n * mX x ^ 3) := mul_le_mul_of_nonneg_left h13 (sq_nonneg _)
          _ = n * mX x * saddleLength δ C₃ M M' x ^ 2 := by dsimp [saddleLength, d]; ring
      · rw [min_eq_right hle]
        have hc_le : c_core ≤ (6 / C₃) ^ (2 / 3 : ℝ) := by dsimp [c_core]; simp [h0]
        have h_pow_id : ((6 / (n * C₃)) ^ (1 / 3 : ℝ)) ^ 2 =
            (6 / C₃) ^ (2 / 3 : ℝ) * n ^ (-(2 / 3 : ℝ)) := by
          rw [← Real.rpow_natCast ((6 / (n * C₃)) ^ (1 / 3 : ℝ)) 2,
            ← Real.rpow_mul (div_nonneg (by norm_num) (mul_nonneg hn.le hC₃)),
            show (1 / 3 : ℝ) * (2 : ℕ) = 2 / 3 by norm_num,
            show 6 / (n * C₃) = (6 / C₃) * n⁻¹ by ring,
            Real.mul_rpow (div_nonneg (by norm_num) hC₃_pos.le) (inv_nonneg.mpr hn.le),
            Real.inv_rpow hn.le, ← Real.rpow_neg hn.le]
        have h_rhs_eq : n * mX x * ((6 / (n * C₃)) ^ (1 / 3 : ℝ)) ^ 2 =
            (6 / C₃) ^ (2 / 3 : ℝ) * (n * mX x ^ 3) ^ (1 / 3 : ℝ) := by
          rw [h_pow_id, Real.mul_rpow hn.le (pow_nonneg hm_pos.le 3),
            ← Real.rpow_natCast (mX x) 3, ← Real.rpow_mul hm_pos.le,
            show (3 : ℕ) * (1 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
          have hn_id : n * n ^ (-(2 / 3 : ℝ)) = n ^ (1 / 3 : ℝ) := by
            calc n * n ^ (-(2 / 3 : ℝ))
                = n ^ (1 : ℝ) * n ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
              _ = n ^ (1 + -(2 / 3 : ℝ)) := by rw [← Real.rpow_add hn]
              _ = n ^ (1 / 3 : ℝ) := by norm_num
          calc n * mX x * ((6 / C₃) ^ (2 / 3 : ℝ) * n ^ (-(2 / 3 : ℝ)))
              = (6 / C₃) ^ (2 / 3 : ℝ) * ((n * n ^ (-(2 / 3 : ℝ))) * mX x) := by ring
            _ = (6 / C₃) ^ (2 / 3 : ℝ) * (n ^ (1 / 3 : ℝ) * mX x) := by rw [hn_id]
        rw [h_rhs_eq]
        exact mul_le_mul_of_nonneg_right hc_le (Real.rpow_nonneg (by positivity) _)
  exact h_core_sq.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm_le_a hn.le) (sq_nonneg _))

private lemma complex_exp_sub_one_le (w : ℂ) :
    ‖Complex.exp w - 1‖ ≤ Real.exp (max 0 w.re) * ‖w‖ := by
  let g : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * w)
  have hg_d : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g (w * Complex.exp ((t : ℂ) * w)) t := fun t _ => by
    have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
      have h := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const w
      simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at h
      exact h
    exact (hlin.cexp).congr_deriv (by ring)
  have hftc : Complex.exp w - 1 = ∫ t in (0 : ℝ)..1, w * Complex.exp ((t : ℂ) * w) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hg_d
      ((by fun_prop : Continuous fun t : ℝ => w * Complex.exp ((t : ℂ) * w)).intervalIntegrable
        (μ := volume) 0 1)
    simpa [g] using h.symm
  rw [hftc]
  have hn := intervalIntegral.norm_integral_le_integral_norm
    (f := fun t : ℝ => w * Complex.exp ((t : ℂ) * w)) (μ := volume) (zero_le_one : (0 : ℝ) ≤ 1)
  have hm : ∫ t in (0 : ℝ)..1, ‖w * Complex.exp ((t : ℂ) * w)‖ ≤
      ∫ _t in (0 : ℝ)..1, Real.exp (max 0 w.re) * ‖w‖ := by
    refine intervalIntegral.integral_mono_on zero_le_one
      ((by fun_prop : Continuous fun t : ℝ => ‖w * Complex.exp ((t : ℂ) * w)‖).intervalIntegrable
        (μ := volume) 0 1)
      (intervalIntegrable_const (μ := volume)) fun t ht => ?_
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
    have hle : t * w.re ≤ max 0 w.re := by
      calc t * w.re ≤ t * max 0 w.re := mul_le_mul_of_nonneg_left (le_max_right 0 w.re) ht.1
        _ ≤ 1 * max 0 w.re := mul_le_mul_of_nonneg_right ht.2 (le_max_left 0 w.re)
        _ = max 0 w.re := one_mul _
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (norm_nonneg w)).trans_eq (mul_comm _ _)
  have hc : ∫ _t in (0 : ℝ)..1, Real.exp (max 0 w.re) * ‖w‖ = Real.exp (max 0 w.re) * ‖w‖ := by
    simp
  exact hn.trans (hm.trans_eq hc)

private lemma complex_exp_sub_one_sub_id_le' (w : ℂ) :
    ‖Complex.exp w - 1 - w‖ ≤ Real.exp (max 0 w.re) * ‖w‖ ^ 2 / 2 := by
  let g₁ : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * w) - 1
  let g₀ : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * w) - 1 - (t : ℂ) * w
  have hg₀_d : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g₀ (w * g₁ t) t := fun t _ => by
    have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
      have h := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const w
      simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at h
      exact h
    exact ((hlin.cexp.sub_const 1).sub hlin).congr_deriv (by dsimp [g₁]; ring)
  have hftc : Complex.exp w - 1 - w = ∫ t in (0 : ℝ)..1, w * g₁ t := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hg₀_d
      ((by fun_prop : Continuous fun t : ℝ => w * g₁ t).intervalIntegrable (μ := volume) 0 1)
    simpa [g₀] using h.symm
  rw [hftc]
  have hn := intervalIntegral.norm_integral_le_integral_norm
    (f := fun t : ℝ => w * g₁ t) (μ := volume) (zero_le_one : (0 : ℝ) ≤ 1)
  have hm : ∫ t in (0 : ℝ)..1, ‖w * g₁ t‖ ≤
      ∫ t in (0 : ℝ)..1, (Real.exp (max 0 w.re) * ‖w‖ ^ 2) * t := by
    refine intervalIntegral.integral_mono_on zero_le_one
      ((by fun_prop : Continuous fun t : ℝ => ‖w * g₁ t‖).intervalIntegrable (μ := volume) 0 1)
      ((by fun_prop : Continuous fun t : ℝ => (Real.exp (max 0 w.re) * ‖w‖ ^ 2) * t).intervalIntegrable
        (μ := volume) 0 1)
      fun t ht => ?_
    rw [norm_mul]
    have hg1 : ‖g₁ t‖ ≤ Real.exp (max 0 w.re) * (t * ‖w‖) := by
      have h1 := complex_exp_sub_one_le ((t : ℂ) * w)
      have hmax : max 0 ((t : ℂ) * w).re ≤ max 0 w.re := by
        rw [Complex.re_ofReal_mul]
        apply max_le (le_max_left 0 w.re)
        calc t * w.re ≤ t * max 0 w.re := mul_le_mul_of_nonneg_left (le_max_right 0 w.re) ht.1
          _ ≤ 1 * max 0 w.re := mul_le_mul_of_nonneg_right ht.2 (le_max_left 0 w.re)
          _ = max 0 w.re := one_mul _
      calc ‖g₁ t‖ ≤ Real.exp (max 0 ((t : ℂ) * w).re) * ‖(t : ℂ) * w‖ := h1
        _ ≤ Real.exp (max 0 w.re) * (t * ‖w‖) := by
            refine mul_le_mul (Real.exp_le_exp.mpr hmax) ?_ (norm_nonneg _) (Real.exp_pos _).le
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    calc ‖w‖ * ‖g₁ t‖ ≤ ‖w‖ * (Real.exp (max 0 w.re) * (t * ‖w‖)) :=
        mul_le_mul_of_nonneg_left hg1 (norm_nonneg w)
      _ = (Real.exp (max 0 w.re) * ‖w‖ ^ 2) * t := by ring
  have hl : ∫ t in (0 : ℝ)..1, (Real.exp (max 0 w.re) * ‖w‖ ^ 2) * t =
      Real.exp (max 0 w.re) * ‖w‖ ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  exact hn.trans (hm.trans_eq hl)

/-! ### 2. Local steepest-descent asymptotic `(SD.7) + (SD.9)` -/

/-- Exact leading constant `(SD.5)` on the positive local steepest-descent contour:
`S₀ = e^{-iπ/2} A(b_x) e^{n φ_x(b_x)} = ‖A(b_x)‖ exp(i Θ)`. -/
lemma saddle_prefactor_polar {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    {x n : ℝ} {A : ℂ → ℂ} :
    let dir := Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))
    let k : ℝ := 4 * Real.pi * n * x / 3
    let Θ : ℝ := n * (Φ₀ (bX x)).im + k * edgeV x - Real.pi / 2 + Complex.arg (A (bX x))
    Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A (bX x) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x (bX x)) * dir =
      ((‖A (bX x)‖ : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ : ℂ)) := by
  intro dir k Θ
  have hpi_half : Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * dir =
      Complex.exp (Complex.I * ((-Real.pi / 2 : ℝ) : ℂ)) := by
    dsimp [dir]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphi_eq : (n : ℂ) * phiX Φ₀ x (bX x) =
      Complex.I * ((n * (Φ₀ (bX x)).im + k * edgeV x : ℝ) : ℂ) := by
    have hre0 : (Φ₀ (bX x)).re = 0 := by dsimp [bX]; exact hΦ.re_edge (edgeV x)
    have hphi_val : phiX Φ₀ x (bX x) =
        Complex.I * (((Φ₀ (bX x)).im + (4 * Real.pi / 3 * x * edgeV x) : ℝ) : ℂ) := by
      unfold phiX
      have hsub : bX x - Complex.I / 2 = (edgeV x : ℂ) := by dsimp [bX]; ring
      have hdecomp : Φ₀ (bX x) = Complex.I * (((Φ₀ (bX x)).im : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hre0]
      conv_lhs => rw [hdecomp, hsub]
      push_cast
      ring
    rw [hphi_val]
    dsimp [k]
    push_cast
    ring
  have hA_polar : A (bX x) =
      ((‖A (bX x)‖ : ℝ) : ℂ) * Complex.exp (Complex.I * ((Complex.arg (A (bX x)) : ℝ) : ℂ)) := by
    have h := (Complex.norm_mul_exp_arg_mul_I (A (bX x))).symm
    rwa [mul_comm (Complex.arg (A (bX x)) : ℂ) Complex.I] at h
  calc Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A (bX x) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x (bX x)) * dir
      = A (bX x) * ((Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * dir) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x (bX x))) := by ring
    _ = ((‖A (bX x)‖ : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ((Complex.arg (A (bX x)) : ℝ) : ℂ)) *
            (Complex.exp (Complex.I * ((-Real.pi / 2 : ℝ) : ℂ)) *
              Complex.exp (Complex.I * ((n * (Φ₀ (bX x)).im + k * edgeV x : ℝ) : ℂ)))) := by
          rw [hpi_half, hphi_eq]
          conv_lhs => lhs; rw [hA_polar]
          ring
    _ = ((‖A (bX x)‖ : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ : ℂ)) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 2
          dsimp [Θ]
          push_cast
          ring

/-- `(SD.7) + (SD.9)`: Asymptotic evaluation of `localPosIntegral` relative to
`‖A(b_x)‖ √(2π / (n α_x))`. -/
lemma localPosIntegral_asymp {δ C₃ C₄ M M' : ℝ} (hδ : 0 < δ) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄)
    (hM : 0 ≤ M) (hM' : 0 ≤ M') :
    ∃ N_loc C_loc : ℝ, 1 ≤ N_loc ∧ 0 ≤ C_loc ∧
      ∀ {Φ₀ : ℂ → ℂ} {x n : ℝ} {A : ℂ → ℂ},
        xiStar < x → 0 < n → N_loc ≤ n * mX x ^ 3 →
        EdgePhaseData δ C₃ C₄ Φ₀ →
        TwoSaddleAmplitude Φ₀ x n δ M M' A →
        let dir := Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))
        let S₀ := Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A (bX x) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x (bX x)) * dir
        ‖localPosIntegral Φ₀ x n δ C₃ M M' A -
          S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ)‖ ≤
          ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (C_loc / (n * mX x ^ 3)) := by
  obtain ⟨c_core, hc_core_pos, h_core_exp⟩ := core_exponent_lower (M := M) (M' := M') hδ hC₃
  obtain ⟨C_tail, hC_tail_nn, hC_tail_bd⟩ :=
    exp_neg_rpow_mul_pow_le_inv (c := c_core / 6) (p := 1 / 3) (by positivity) (by norm_num) 0
  let C_rem : ℝ := √(3 / 2) *
    (3 * (4 * M ^ 2 + M') / 2 +
      27 * (Real.exp 1 * C₄ / 24 + M * C₃ / 6) / 4 +
      405 * (Real.exp 2 * C₃ ^ 2 / 72) / 8)
  let C_loc : ℝ := (2 * Real.exp 1 * √3 + √2) * C_tail + C_rem
  have hC_rem_nn : 0 ≤ C_rem := by positivity
  have hC_loc_nn : 0 ≤ C_loc := by positivity
  refine ⟨1, C_loc, le_rfl, hC_loc_nn, fun {Φ₀ x n A} hx hn hnm hΦ hA => ?_⟩
  let dir : ℂ := Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))
  let S₀ : ℂ := Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A (bX x) *
    Complex.exp ((n : ℂ) * phiX Φ₀ x (bX x)) * dir
  let ℓ : ℝ := saddleLength δ C₃ M M' x
  let r₁ : ℝ := coreThreshold δ C₃ M M' n x
  have hℓ_le : ℓ ≤ √2 * δ := saddleLength_le_sqrt2_mul_delta hδ hx
  have hr₁_nn : 0 ≤ r₁ := coreThreshold_nonneg hδ hx hn hC₃
  have hr₁_le : r₁ ≤ ℓ := coreThreshold_le_saddleLength
  have hℓ_nn : 0 ≤ ℓ := hr₁_nn.trans hr₁_le
  have ha_pos : 0 < alphaX x := alphaX_pos hx
  have hm_pos : 0 < mX x := mX_pos hx
  have hm_le_one : mX x ≤ 1 := mX_le_one x
  have hm_le_alpha : mX x ≤ alphaX x := mX_le_alphaX x
  have hdir_norm : ‖dir‖ = 1 := by
    dsimp [dir]
    rw [show -Complex.I * (Real.pi / 4 : ℂ) = ((-Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hS₀_norm : ‖S₀‖ = ‖A (bX x)‖ := by
    dsimp [S₀]
    have hn1 : ‖Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))‖ = 1 := hdir_norm
    have hn2 : ‖Complex.exp ((n : ℂ) * phiX Φ₀ x (bX x))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : ((n : ℂ) * phiX Φ₀ x (bX x)).re = 0 := by
        simp [bX, phiX_re_edge hΦ x (edgeV x)]
      rw [hre, Real.exp_zero]
    rw [norm_mul, norm_mul, norm_mul, hn1, one_mul, hn2, mul_one, mul_one]
  let g : ℝ → ℂ := fun r => saddleIntegrand Φ₀ x n A (bX x + (r : ℂ) * dir) * dir
  have hmem_loc : ∀ r ∈ Icc (-ℓ) ℓ, bX x + (r : ℂ) * dir ∈ edgeStrip δ := fun r hr => by
    change |(bX x + (r : ℂ) * dir).im - 1 / 2| ≤ δ
    have hdir_im : dir.im = -(√2 / 2) := by
      dsimp [dir]
      rw [show -Complex.I * (Real.pi / 4 : ℂ) = ((-Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_ofReal_mul_I, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re]
      simp [neg_div, Real.sin_neg, Real.sin_pi_div_four]
    have him : (bX x + (r : ℂ) * dir).im - 1 / 2 = -(r * (√2 / 2)) := by
      dsimp [bX]
      simp [hdir_im]
    rw [him, abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ √2 / 2)]
    have h1 : |r| ≤ ℓ := abs_le.mpr hr
    have hsq : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
    have hs : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
    calc |r| * (√2 / 2) ≤ ℓ * (√2 / 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (√2 * δ) * (√2 / 2) := mul_le_mul_of_nonneg_right hℓ_le (by positivity)
      _ = δ := by field_simp [hs]; rw [hsq]
  have hg_cont : ContinuousOn g (Icc (-ℓ) ℓ) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    dsimp [saddleIntegrand]
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const
      (hA.holo.continuousOn.comp (by fun_prop) hmem_loc)) ?_
    exact Complex.continuous_exp.continuousOn.comp
      (continuousOn_const.mul ((phiX_analyticOnNhd hΦ x).continuousOn.comp (by fun_prop) hmem_loc))
      fun _ _ => mem_univ _
  have hint_all : IntervalIntegrable g volume (-ℓ) ℓ :=
    (hg_cont.mono (by rw [Set.uIcc_of_le (by linarith)])).intervalIntegrable
  have hint_neg : IntervalIntegrable g volume (-ℓ) (-r₁) :=
    hint_all.mono_set (by
      simpa [Set.uIcc_of_le (by linarith : -ℓ ≤ -r₁), Set.uIcc_of_le (by linarith : -ℓ ≤ ℓ)]
        using Icc_subset_Icc le_rfl (by linarith))
  have hint_core : IntervalIntegrable g volume (-r₁) r₁ :=
    hint_all.mono_set (by
      simpa [Set.uIcc_of_le (by linarith : -r₁ ≤ r₁), Set.uIcc_of_le (by linarith : -ℓ ≤ ℓ)]
        using Icc_subset_Icc (by linarith : -ℓ ≤ -r₁) hr₁_le)
  have hint_pos : IntervalIntegrable g volume r₁ ℓ :=
    hint_all.mono_set (by
      simpa [Set.uIcc_of_le hr₁_le, Set.uIcc_of_le (by linarith : -ℓ ≤ ℓ)]
        using Icc_subset_Icc (by linarith : -ℓ ≤ r₁) le_rfl)
  have hsplit : localPosIntegral Φ₀ x n δ C₃ M M' A =
      (∫ r in (-ℓ)..(-r₁), g r) + (∫ r in (-r₁)..r₁, g r) + (∫ r in r₁..ℓ, g r) := by
    change (∫ r in (-ℓ)..ℓ, g r) = _
    have h1 := intervalIntegral.integral_add_adjacent_intervals hint_neg hint_core
    have hint_left : IntervalIntegrable g volume (-ℓ) r₁ := hint_neg.trans hint_core
    have h2 := intervalIntegral.integral_add_adjacent_intervals hint_left hint_pos
    rw [← h2, ← h1]
  have h_ann_bd : ∀ r ∈ Icc (-ℓ) ℓ,
      ‖g r‖ ≤ Real.exp 1 * ‖A (bX x)‖ * Real.exp (-(n * alphaX x / 3) * r ^ 2) := fun r hr => by
    have hMℓ : M * |r| ≤ 1 := by
      have hdM : M * saddleScaleD δ C₃ M M' ≤ 1 := saddleScaleD_mul_M_le_one hM
      calc M * |r| ≤ M * ℓ := mul_le_mul_of_nonneg_left (abs_le.mpr hr) hM
        _ = (M * saddleScaleD δ C₃ M M') * mX x := by dsimp [ℓ, saddleLength]; ring
        _ ≤ 1 * 1 := mul_le_mul hdM hm_le_one hm_pos.le zero_le_one
        _ = 1 := one_mul 1
    have hC₃r : C₃ * |r| ≤ alphaX x := by
      have hdC : C₃ * saddleScaleD δ C₃ M M' ≤ 1 := saddleScaleD_mul_C3_le_one hC₃
      calc C₃ * |r| ≤ C₃ * ℓ := mul_le_mul_of_nonneg_left (abs_le.mpr hr) hC₃
        _ = (C₃ * saddleScaleD δ C₃ M M') * mX x := by dsimp [ℓ, saddleLength]; ring
        _ ≤ 1 * alphaX x := mul_le_mul hdC hm_le_alpha hm_pos.le zero_le_one
        _ = alphaX x := one_mul _
    have hA_bd := amplitude_growth_le hA (bX_mem_edgeStrip hδ.le x) (hmem_loc r hr)
    have hnorm_diff : ‖bX x + (r : ℂ) * dir - bX x‖ = |r| := by
      rw [add_sub_cancel_left, norm_mul, hdir_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hphi_re := phiX_local_re_le hΦ hδ.le hx
      ((abs_le.mpr hr).trans hℓ_le) hC₃r
    have hnorm_g : ‖g r‖ = ‖A (bX x + (r : ℂ) * dir)‖ *
        Real.exp (n * (phiX Φ₀ x (bX x + (r : ℂ) * dir)).re) := by
      dsimp [g, saddleIntegrand]
      rw [norm_mul, norm_mul, norm_mul, hdir_norm, one_mul, mul_one, Complex.norm_exp]
      simp
    have hphi_sub : (phiX Φ₀ x (bX x + (r : ℂ) * dir)).re =
        (phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x)).re := by
      rw [Complex.sub_re]
      dsimp [bX]
      rw [phiX_re_edge hΦ x (edgeV x), sub_zero]
    rw [hnorm_diff] at hA_bd
    rw [hnorm_g]
    calc ‖A (bX x + (r : ℂ) * dir)‖ * Real.exp (n * (phiX Φ₀ x (bX x + (r : ℂ) * dir)).re)
        ≤ (‖A (bX x)‖ * Real.exp (M * |r|)) *
            Real.exp (n * (-alphaX x * r ^ 2 / 3)) := by
          refine mul_le_mul hA_bd ?_ (Real.exp_pos _).le (by positivity)
          rw [hphi_sub]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hphi_re hn.le)
      _ ≤ (‖A (bX x)‖ * Real.exp 1) * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hMℓ) (norm_nonneg _))
            (le_of_eq (congrArg Real.exp (by ring))) (Real.exp_pos _).le (by positivity)
      _ = Real.exp 1 * ‖A (bX x)‖ * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by ring
  have h_ann_pos : ‖∫ r in r₁..ℓ, g r‖ ≤
      ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
        (Real.exp 1 * √3 * C_tail / (n * mX x ^ 3)) := by
    have hn_le := intervalIntegral.norm_integral_le_integral_norm (f := g) (μ := volume) hr₁_le
    have hm_le : ∫ r in r₁..ℓ, ‖g r‖ ≤
        ∫ r in r₁..ℓ, (Real.exp 1 * ‖A (bX x)‖) * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
      refine intervalIntegral.integral_mono_on hr₁_le
        (hint_pos.norm)
        ((by fun_prop : Continuous fun r : ℝ =>
          (Real.exp 1 * ‖A (bX x)‖) * Real.exp (-(n * alphaX x / 3) * r ^ 2)).intervalIntegrable
          (μ := volume) r₁ ℓ)
        fun r hr => ?_
      exact h_ann_bd r ⟨(by linarith : -ℓ ≤ r₁).trans hr.1, hr.2⟩
    rw [intervalIntegral.integral_const_mul] at hm_le
    have hg_ann := gauss_annulus_integral_le (a := n * alphaX x / 3)
      (by positivity) hr₁_nn hr₁_le
    have h_exp_c : Real.exp (-(n * alphaX x / 3) * r₁ ^ 2 / 2) ≤
        Real.exp (-(c_core / 6) * (n * mX x ^ 3) ^ (1 / 3 : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 := h_core_exp hx hn hnm
      linarith
    have h_tail_inv : Real.exp (-(c_core / 6) * (n * mX x ^ 3) ^ (1 / 3 : ℝ)) ≤
        C_tail / (n * mX x ^ 3) := by
      simpa using hC_tail_bd (n * mX x ^ 3) hnm
    have h_sqrt3 : √(2 * Real.pi / (n * alphaX x / 3)) =
        √3 * √(2 * Real.pi / (n * alphaX x)) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    calc ‖∫ r in r₁..ℓ, g r‖
        ≤ (Real.exp 1 * ‖A (bX x)‖) * ∫ r in r₁..ℓ, Real.exp (-(n * alphaX x / 3) * r ^ 2) :=
          hn_le.trans hm_le
      _ ≤ (Real.exp 1 * ‖A (bX x)‖) *
            (Real.exp (-(n * alphaX x / 3) * r₁ ^ 2 / 2) *
              √(2 * Real.pi / (n * alphaX x / 3))) := by
          gcongr
      _ ≤ (Real.exp 1 * ‖A (bX x)‖) *
            ((C_tail / (n * mX x ^ 3)) * (√3 * √(2 * Real.pi / (n * alphaX x)))) := by
          rw [h_sqrt3]
          gcongr
          exact h_exp_c.trans h_tail_inv
      _ = ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
            (Real.exp 1 * √3 * C_tail / (n * mX x ^ 3)) := by ring
  have h_ann_neg : ‖∫ r in (-ℓ)..(-r₁), g r‖ ≤
      ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
        (Real.exp 1 * √3 * C_tail / (n * mX x ^ 3)) := by
    have hn_le := intervalIntegral.norm_integral_le_integral_norm
      (f := g) (μ := volume) (by linarith : -ℓ ≤ -r₁)
    have hm_le : ∫ r in (-ℓ)..(-r₁), ‖g r‖ ≤
        ∫ r in (-ℓ)..(-r₁), (Real.exp 1 * ‖A (bX x)‖) * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
      refine intervalIntegral.integral_mono_on (by linarith : -ℓ ≤ -r₁)
        (hint_neg.norm)
        ((by fun_prop : Continuous fun r : ℝ =>
          (Real.exp 1 * ‖A (bX x)‖) * Real.exp (-(n * alphaX x / 3) * r ^ 2)).intervalIntegrable
          (μ := volume) (-ℓ) (-r₁))
        fun r hr => ?_
      exact h_ann_bd r ⟨hr.1, hr.2.trans (by linarith : -r₁ ≤ ℓ)⟩
    rw [intervalIntegral.integral_const_mul] at hm_le
    have hg_ann := gauss_annulus_integral_neg_le (a := n * alphaX x / 3)
      (by positivity) hr₁_nn hr₁_le
    have h_exp_c : Real.exp (-(n * alphaX x / 3) * r₁ ^ 2 / 2) ≤
        Real.exp (-(c_core / 6) * (n * mX x ^ 3) ^ (1 / 3 : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 := h_core_exp hx hn hnm
      linarith
    have h_tail_inv : Real.exp (-(c_core / 6) * (n * mX x ^ 3) ^ (1 / 3 : ℝ)) ≤
        C_tail / (n * mX x ^ 3) := by
      simpa using hC_tail_bd (n * mX x ^ 3) hnm
    have h_sqrt3 : √(2 * Real.pi / (n * alphaX x / 3)) =
        √3 * √(2 * Real.pi / (n * alphaX x)) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    calc ‖∫ r in (-ℓ)..(-r₁), g r‖
        ≤ (Real.exp 1 * ‖A (bX x)‖) * ∫ r in (-ℓ)..(-r₁), Real.exp (-(n * alphaX x / 3) * r ^ 2) :=
          hn_le.trans hm_le
      _ ≤ (Real.exp 1 * ‖A (bX x)‖) *
            (Real.exp (-(n * alphaX x / 3) * r₁ ^ 2 / 2) *
              √(2 * Real.pi / (n * alphaX x / 3))) := by
          gcongr
      _ ≤ (Real.exp 1 * ‖A (bX x)‖) *
            ((C_tail / (n * mX x ^ 3)) * (√3 * √(2 * Real.pi / (n * alphaX x)))) := by
          rw [h_sqrt3]
          gcongr
          exact h_exp_c.trans h_tail_inv
      _ = ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
            (Real.exp 1 * √3 * C_tail / (n * mX x ^ 3)) := by ring
  -- Core integral `∫_{-r₁}^{r₁} g(r) dr`
  let a₁ : ℂ := deriv A (bX x) / A (bX x)
  let c₁ : ℂ := a₁ * dir
  let c₃ : ℂ := (n : ℂ) * ((1 / 6 : ℂ) * iteratedDeriv 3 Φ₀ (bX x) * dir ^ 3)
  let gaussReal : ℝ → ℝ := fun r => Real.exp (-(n * alphaX x / 2) * r ^ 2)
  let E : ℝ → ℂ := fun r =>
    g r - S₀ * (1 + c₁ * (r : ℂ) + c₃ * (r : ℂ) ^ 3) * (gaussReal r : ℂ)
  have hE_int : IntervalIntegrable E volume (-r₁) r₁ := by
    refine hint_core.sub ?_
    exact (by fun_prop : Continuous fun r : ℝ =>
      S₀ * (1 + c₁ * (r : ℂ) + c₃ * (r : ℂ) ^ 3) * (gaussReal r : ℂ)).intervalIntegrable
      (μ := volume) (-r₁) r₁
  have hc₁_bd : ‖c₁‖ ≤ M := by
    dsimp [c₁, a₁]
    rw [norm_mul, hdir_norm, mul_one]
    exact hA.logDeriv_bound (bX x) (bX_mem_edgeStrip hδ.le x)
  have hc₃_bd : ‖c₃‖ ≤ n * C₃ / 6 := by
    dsimp [c₃]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, hdir_norm, one_pow, mul_one,
      Complex.norm_real, Real.norm_of_nonneg hn.le]
    have h16 : ‖(1 / 6 : ℂ)‖ = 1 / 6 := by norm_num
    have hd3 := hΦ.deriv3_bound (bX x) (bX_mem_edgeStrip hδ.le x)
    rw [h16]
    calc n * (1 / 6 * ‖iteratedDeriv 3 Φ₀ (bX x)‖)
        ≤ n * (1 / 6 * C₃) := by gcongr
      _ = n * C₃ / 6 := by ring
  let K₂ : ℝ := ‖A (bX x)‖ * (4 * M ^ 2 + M')
  let K₄ : ℝ := ‖A (bX x)‖ * (Real.exp 1 * n * C₄ / 24 + M * n * C₃ / 6)
  let K₆ : ℝ := ‖A (bX x)‖ * (Real.exp 2 * n ^ 2 * C₃ ^ 2 / 72)
  have h_core_pt : ∀ r ∈ Icc (-r₁) r₁,
      ‖E r‖ ≤ (K₂ * r ^ 2 + K₄ * r ^ 4 + K₆ * r ^ 6) *
        Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
    intro r hr
    have hr_ℓ : r ∈ Icc (-ℓ) ℓ := ⟨(by linarith : -ℓ ≤ -r₁).trans hr.1, hr.2.trans hr₁_le⟩
    have hr_abs : |r| ≤ r₁ := abs_le.mpr hr
    have hr_le_d : |r| ≤ √2 * δ := (hr_abs.trans hr₁_le).trans hℓ_le
    have hMℓ : M * |r| ≤ 1 := by
      have hdM : M * saddleScaleD δ C₃ M M' ≤ 1 := saddleScaleD_mul_M_le_one hM
      calc M * |r| ≤ M * ℓ := mul_le_mul_of_nonneg_left (abs_le.mpr hr_ℓ) hM
        _ = (M * saddleScaleD δ C₃ M M') * mX x := by dsimp [ℓ, saddleLength]; ring
        _ ≤ 1 * 1 := mul_le_mul hdM hm_le_one hm_pos.le zero_le_one
        _ = 1 := one_mul 1
    have hC₃r : C₃ * |r| ≤ alphaX x := by
      have hdC : C₃ * saddleScaleD δ C₃ M M' ≤ 1 := saddleScaleD_mul_C3_le_one hC₃
      calc C₃ * |r| ≤ C₃ * ℓ := mul_le_mul_of_nonneg_left (abs_le.mpr hr_ℓ) hC₃
        _ = (C₃ * saddleScaleD δ C₃ M M') * mX x := by dsimp [ℓ, saddleLength]; ring
        _ ≤ 1 * alphaX x := mul_le_mul hdC hm_le_alpha hm_pos.le zero_le_one
        _ = alphaX x := one_mul _
    have hmem_seg : ∀ t ∈ uIcc 0 r, bX x + (t : ℂ) * dir ∈ edgeStrip δ := fun t ht => by
      have ht_bd : |t| ≤ |r| := by
        rcases le_total 0 r with hr0 | hr0
        · rw [Set.uIcc_of_le hr0] at ht
          rw [abs_of_nonneg ht.1, abs_of_nonneg hr0]
          exact ht.2
        · rw [Set.uIcc_of_ge hr0] at ht
          rw [abs_of_nonpos ht.2, abs_of_nonpos hr0]
          linarith [ht.1]
      have ht_icc : t ∈ Icc (-ℓ) ℓ :=
        abs_le.mp (ht_bd.trans (abs_le.mpr hr_ℓ))
      exact hmem_loc t ht_icc
    have hA_tay := amplitude_taylor_order1 hA hδ.le hdir_norm hmem_seg hMℓ
    have hA_growth := amplitude_growth_le hA (bX_mem_edgeStrip hδ.le x) (hmem_loc r hr_ℓ)
    have hnorm_diff : ‖bX x + (r : ℂ) * dir - bX x‖ = |r| := by
      rw [add_sub_cancel_left, norm_mul, hdir_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hAx_ne : A (bX x) ≠ 0 := hA.nonzero (bX x) (bX_mem_edgeStrip hδ.le x)
    have hA_ratio_bd : ‖A (bX x + (r : ℂ) * dir) / A (bX x)‖ ≤ Real.exp 1 := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hAx_ne)]
      rw [hnorm_diff] at hA_growth
      calc ‖A (bX x + (r : ℂ) * dir)‖ ≤ ‖A (bX x)‖ * Real.exp (M * |r|) := hA_growth
        _ ≤ ‖A (bX x)‖ * Real.exp 1 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hMℓ) (norm_nonneg _)
        _ = Real.exp 1 * ‖A (bX x)‖ := mul_comm _ _
    let ω₃ : ℂ := c₃ * (r : ℂ) ^ 3
    let q : ℂ := ((-(n * alphaX x / 2) * r ^ 2 : ℝ) : ℂ)
    let ω₄ : ℂ := (n : ℂ) * (phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x)) - q - ω₃
    have hω₃_bd : ‖ω₃‖ ≤ (n * C₃ / 6) * |r| ^ 3 := by
      dsimp [ω₃]
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hc₃_bd (pow_nonneg (abs_nonneg r) 3)
    have hω₃_le_one : ‖ω₃‖ ≤ 1 := by
      have hrcub : |r| ^ 3 ≤ r₁ ^ 3 := pow_le_pow_left₀ (abs_nonneg r) hr_abs 3
      calc ‖ω₃‖ ≤ (n * C₃ / 6) * |r| ^ 3 := hω₃_bd
        _ ≤ (n * C₃ / 6) * r₁ ^ 3 := mul_le_mul_of_nonneg_left hrcub (by positivity)
        _ = (n / 6) * (C₃ * r₁ ^ 3) := by ring
        _ ≤ (n / 6) * (6 / n) :=
            mul_le_mul_of_nonneg_left (C₃_mul_coreThreshold_cubed_le hδ hx hn hC₃) (by positivity)
        _ = 1 := by field_simp [hn.ne']
    have hω₃_re_le : ω₃.re ≤ (n * alphaX x / 6) * r ^ 2 := by
      have h1 : |r| ^ 3 = r ^ 2 * |r| := by
        rw [pow_succ, sq_abs]
      calc ω₃.re ≤ ‖ω₃‖ := Complex.re_le_norm ω₃
        _ ≤ (n * C₃ / 6) * |r| ^ 3 := hω₃_bd
        _ = (n / 6) * (C₃ * |r|) * r ^ 2 := by rw [h1]; ring
        _ ≤ (n / 6) * alphaX x * r ^ 2 := by gcongr
        _ = (n * alphaX x / 6) * r ^ 2 := by ring
    have hω₄_bd : ‖ω₄‖ ≤ (n * C₄ / 24) * r ^ 4 := by
      have hcub := phiX_local_cubic_bound hΦ hδ.le hx hr_le_d
      have hω₄_eq : ω₄ = (n : ℂ) * (phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x) +
          (1 / 2 : ℂ) * (alphaX x : ℂ) * (r : ℂ) ^ 2 -
          (1 / 6 : ℂ) * iteratedDeriv 3 Φ₀ (bX x) * dir ^ 3 * (r : ℂ) ^ 3) := by
        dsimp [ω₄, q, c₃, ω₃, dir]
        push_cast
        ring
      rw [hω₄_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hn.le]
      calc n * ‖phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x) +
              (1 / 2 : ℂ) * (alphaX x : ℂ) * (r : ℂ) ^ 2 -
              (1 / 6 : ℂ) * iteratedDeriv 3 Φ₀ (bX x) * dir ^ 3 * (r : ℂ) ^ 3‖
          ≤ n * (C₄ * r ^ 4 / 24) := mul_le_mul_of_nonneg_left hcub hn.le
        _ = (n * C₄ / 24) * r ^ 4 := by ring
    have h_sum_re : (ω₃ + ω₄).re ≤ (n * alphaX x / 6) * r ^ 2 := by
      have hre := phiX_local_re_le hΦ hδ.le hx hr_le_d hC₃r
      have h_id : ω₃ + ω₄ = (n : ℂ) * (phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x)) - q := by
        dsimp [ω₄]; ring
      rw [h_id, Complex.sub_re]
      have hq_re : q.re = -(n * alphaX x / 2) * r ^ 2 := rfl
      have hphi_n : ((n : ℂ) * (phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x))).re =
          n * (phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x)).re := by
        simp
      rw [hq_re, hphi_n]
      have h1 : n * (phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x)).re ≤
          -(n * alphaX x / 3) * r ^ 2 := by
        calc n * (phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x)).re
            ≤ n * (-alphaX x * r ^ 2 / 3) := mul_le_mul_of_nonneg_left hre hn.le
          _ = -(n * alphaX x / 3) * r ^ 2 := by ring
      linarith
    have h_rem_re : ω₃.re + max 0 ω₄.re ≤ (n * alphaX x / 6) * r ^ 2 := by
      rcases le_total ω₄.re 0 with h4 | h4
      · rw [max_eq_left h4, add_zero]
        exact hω₃_re_le
      · rw [max_eq_right h4, ← Complex.add_re]
        exact h_sum_re
    let R_Phi : ℂ := Complex.exp (ω₃ + ω₄) - 1 - ω₃
    let R_A : ℂ := A (bX x + (r : ℂ) * dir) / A (bX x) - 1 - c₁ * (r : ℂ)
    have hR_Phi_eq : R_Phi = (Complex.exp ω₃ - 1 - ω₃) +
        Complex.exp ω₃ * (Complex.exp ω₄ - 1) := by
      dsimp [R_Phi]
      rw [Complex.exp_add]
      ring
    have h_exp3_re : max 0 ω₃.re ≤ 1 := max_le zero_le_one ((Complex.re_le_norm ω₃).trans hω₃_le_one)
    have h_part1 : ‖(Complex.exp ω₃ - 1 - ω₃) * Complex.exp q‖ ≤
        (Real.exp 1 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6 * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
      have h_id := complex_exp_sub_one_sub_id_le' ω₃
      have h_sq_6 : ‖ω₃‖ ^ 2 ≤ (n ^ 2 * C₃ ^ 2 / 36) * r ^ 6 := by
        have hp : ‖ω₃‖ ^ 2 ≤ ((n * C₃ / 6) * |r| ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hω₃_bd 2
        have heq : ((n * C₃ / 6) * |r| ^ 3) ^ 2 = (n ^ 2 * C₃ ^ 2 / 36) * r ^ 6 := by
          rw [mul_pow, ← pow_mul, mul_comm 3 2, pow_mul, sq_abs, ← pow_mul]
          ring
        exact hp.trans_eq heq
      have h_q_le : Real.exp (-(n * alphaX x / 2) * r ^ 2) ≤ Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
        refine Real.exp_le_exp.mpr ?_
        have hpos : 0 ≤ n * alphaX x * r ^ 2 := by positivity
        linarith
      rw [norm_mul, Complex.norm_exp]
      have hq_re : q.re = -(n * alphaX x / 2) * r ^ 2 := rfl
      rw [hq_re]
      calc ‖Complex.exp ω₃ - 1 - ω₃‖ * Real.exp (-(n * alphaX x / 2) * r ^ 2)
          ≤ (Real.exp (max 0 ω₃.re) * ‖ω₃‖ ^ 2 / 2) * Real.exp (-(n * alphaX x / 3) * r ^ 2) :=
            mul_le_mul h_id h_q_le (Real.exp_pos _).le (by positivity)
        _ ≤ (Real.exp 1 * ((n ^ 2 * C₃ ^ 2 / 36) * r ^ 6) / 2) *
              Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            exact div_le_div_of_nonneg_right
              (mul_le_mul (Real.exp_le_exp.mpr h_exp3_re) h_sq_6 (sq_nonneg _) (Real.exp_pos _).le)
              (by norm_num)
        _ = (Real.exp 1 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6 * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
            ring
    have h_part2 : ‖Complex.exp ω₃ * (Complex.exp ω₄ - 1) * Complex.exp q‖ ≤
        (n * C₄ / 24) * r ^ 4 * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
      have h1 := complex_exp_sub_one_le ω₄
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
      have hq_re : q.re = -(n * alphaX x / 2) * r ^ 2 := rfl
      rw [hq_re]
      have hexp_comb : Real.exp ω₃.re * Real.exp (max 0 ω₄.re) * Real.exp (-(n * alphaX x / 2) * r ^ 2) ≤
          Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      calc Real.exp ω₃.re * ‖Complex.exp ω₄ - 1‖ * Real.exp (-(n * alphaX x / 2) * r ^ 2)
          ≤ Real.exp ω₃.re * (Real.exp (max 0 ω₄.re) * ‖ω₄‖) *
              Real.exp (-(n * alphaX x / 2) * r ^ 2) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) (Real.exp_pos _).le
        _ = (Real.exp ω₃.re * Real.exp (max 0 ω₄.re) * Real.exp (-(n * alphaX x / 2) * r ^ 2)) * ‖ω₄‖ := by
            ring
        _ ≤ Real.exp (-(n * alphaX x / 3) * r ^ 2) * ((n * C₄ / 24) * r ^ 4) :=
            mul_le_mul hexp_comb hω₄_bd (norm_nonneg _) (Real.exp_pos _).le
        _ = (n * C₄ / 24) * r ^ 4 * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by ring
    have hR_Phi_gauss : ‖R_Phi * Complex.exp q‖ ≤
        ((n * C₄ / 24) * r ^ 4 + (Real.exp 1 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6) *
          Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
      rw [hR_Phi_eq, add_mul]
      calc ‖(Complex.exp ω₃ - 1 - ω₃) * Complex.exp q +
              Complex.exp ω₃ * (Complex.exp ω₄ - 1) * Complex.exp q‖
          ≤ ‖(Complex.exp ω₃ - 1 - ω₃) * Complex.exp q‖ +
              ‖Complex.exp ω₃ * (Complex.exp ω₄ - 1) * Complex.exp q‖ := norm_add_le _ _
        _ ≤ (Real.exp 1 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6 * Real.exp (-(n * alphaX x / 3) * r ^ 2) +
              (n * C₄ / 24) * r ^ 4 * Real.exp (-(n * alphaX x / 3) * r ^ 2) :=
            add_le_add h_part1 h_part2
        _ = ((n * C₄ / 24) * r ^ 4 + (Real.exp 1 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6) *
              Real.exp (-(n * alphaX x / 3) * r ^ 2) := by ring
    have h_E_eq : E r = S₀ * ((A (bX x + (r : ℂ) * dir) / A (bX x)) * (R_Phi * Complex.exp q) +
        R_A * (1 + ω₃) * Complex.exp q + (c₁ * (r : ℂ)) * ω₃ * Complex.exp q) := by
      have hg_eq : g r = S₀ * (A (bX x + (r : ℂ) * dir) / A (bX x)) *
          Complex.exp (q + ω₃ + ω₄) := by
        have h_add : (n : ℂ) * phiX Φ₀ x (bX x + (r : ℂ) * dir) =
            (n : ℂ) * phiX Φ₀ x (bX x) + (q + ω₃ + ω₄) := by
          dsimp [ω₄]; ring
        dsimp [g, saddleIntegrand, S₀]
        rw [h_add, Complex.exp_add]
        have h_A_div : A (bX x) * (A (bX x + (r : ℂ) * dir) / A (bX x)) = A (bX x + (r : ℂ) * dir) :=
          mul_div_cancel₀ _ hAx_ne
        calc Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A (bX x + (r : ℂ) * dir) *
              (Complex.exp ((n : ℂ) * phiX Φ₀ x (bX x)) * Complex.exp (q + ω₃ + ω₄)) * dir
            = Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
                (A (bX x) * (A (bX x + (r : ℂ) * dir) / A (bX x))) *
                (Complex.exp ((n : ℂ) * phiX Φ₀ x (bX x)) * Complex.exp (q + ω₃ + ω₄)) * dir := by
              rw [h_A_div]
          _ = Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A (bX x) *
                Complex.exp ((n : ℂ) * phiX Φ₀ x (bX x)) * dir *
                (A (bX x + (r : ℂ) * dir) / A (bX x)) * Complex.exp (q + ω₃ + ω₄) := by ring
      have hexpq : Complex.exp q = (gaussReal r : ℂ) := by
        dsimp [q, gaussReal]
        rw [← Complex.ofReal_exp]
      have hexp_sum : Complex.exp (q + ω₃ + ω₄) = Complex.exp q * Complex.exp (ω₃ + ω₄) := by
        rw [add_assoc, Complex.exp_add]
      dsimp [E]
      rw [hg_eq, hexp_sum, ← hexpq]
      dsimp [R_Phi, R_A, ω₃]
      ring
    have h_q_le : ‖Complex.exp q‖ ≤ Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
      rw [Complex.norm_exp]
      have hq_re : q.re = -(n * alphaX x / 2) * r ^ 2 := rfl
      rw [hq_re]
      refine Real.exp_le_exp.mpr ?_
      have hpos : 0 ≤ n * alphaX x * r ^ 2 := by positivity
      linarith
    have h_termA : ‖(A (bX x + (r : ℂ) * dir) / A (bX x)) * (R_Phi * Complex.exp q)‖ ≤
        ((Real.exp 1 * n * C₄ / 24) * r ^ 4 + (Real.exp 2 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6) *
          Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
      rw [norm_mul]
      have he2 : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
        rw [← Real.exp_add]; norm_num
      calc ‖A (bX x + (r : ℂ) * dir) / A (bX x)‖ * ‖R_Phi * Complex.exp q‖
          ≤ Real.exp 1 * (((n * C₄ / 24) * r ^ 4 + (Real.exp 1 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6) *
              Real.exp (-(n * alphaX x / 3) * r ^ 2)) :=
            mul_le_mul hA_ratio_bd hR_Phi_gauss (norm_nonneg _) (Real.exp_pos _).le
        _ = ((Real.exp 1 * n * C₄ / 24) * r ^ 4 + ((Real.exp 1 * Real.exp 1) * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6) *
              Real.exp (-(n * alphaX x / 3) * r ^ 2) := by ring
        _ = ((Real.exp 1 * n * C₄ / 24) * r ^ 4 + (Real.exp 2 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6) *
              Real.exp (-(n * alphaX x / 3) * r ^ 2) := by rw [he2]
    have h_termB : ‖R_A * (1 + ω₃) * Complex.exp q‖ ≤
        (4 * M ^ 2 + M') * r ^ 2 * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
      have hRA_bd : ‖R_A‖ ≤ (2 * M ^ 2 + M' / 2) * r ^ 2 := by
        dsimp [R_A, c₁, a₁]
        exact hA_tay.2
      have h13 : ‖1 + ω₃‖ ≤ 2 := by
        calc ‖1 + ω₃‖ ≤ ‖(1 : ℂ)‖ + ‖ω₃‖ := norm_add_le _ _
          _ ≤ 1 + 1 := by simp [hω₃_le_one]
          _ = 2 := by norm_num
      rw [norm_mul, norm_mul]
      calc ‖R_A‖ * ‖1 + ω₃‖ * ‖Complex.exp q‖
          ≤ ((2 * M ^ 2 + M' / 2) * r ^ 2) * 2 * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
            refine mul_le_mul (mul_le_mul hRA_bd h13 (norm_nonneg _) (by positivity))
              h_q_le (norm_nonneg _) (by positivity)
        _ = (4 * M ^ 2 + M') * r ^ 2 * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by ring
    have h_termC : ‖c₁ * (r : ℂ) * ω₃ * Complex.exp q‖ ≤
        (M * n * C₃ / 6) * r ^ 4 * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hr4 : |r| * |r| ^ 3 = r ^ 4 := by
        rw [← pow_succ', show (3 + 1 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
      calc ‖c₁‖ * |r| * ‖ω₃‖ * ‖Complex.exp q‖
          ≤ M * |r| * ((n * C₃ / 6) * |r| ^ 3) * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
            refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hc₁_bd (abs_nonneg r))
              hω₃_bd (norm_nonneg _) (by positivity)) h_q_le (norm_nonneg _) (by positivity)
        _ = (M * n * C₃ / 6) * (|r| * |r| ^ 3) * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by ring
        _ = (M * n * C₃ / 6) * r ^ 4 * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by rw [hr4]
    rw [h_E_eq, norm_mul, hS₀_norm]
    have h_tri : ‖A (bX x + (r : ℂ) * dir) / A (bX x) * (R_Phi * Complex.exp q) +
          R_A * (1 + ω₃) * Complex.exp q + c₁ * (r : ℂ) * ω₃ * Complex.exp q‖ ≤
        ‖A (bX x + (r : ℂ) * dir) / A (bX x) * (R_Phi * Complex.exp q)‖ +
          ‖R_A * (1 + ω₃) * Complex.exp q‖ + ‖c₁ * (r : ℂ) * ω₃ * Complex.exp q‖ :=
      calc ‖A (bX x + (r : ℂ) * dir) / A (bX x) * (R_Phi * Complex.exp q) +
              R_A * (1 + ω₃) * Complex.exp q + c₁ * (r : ℂ) * ω₃ * Complex.exp q‖
          ≤ ‖A (bX x + (r : ℂ) * dir) / A (bX x) * (R_Phi * Complex.exp q) +
                R_A * (1 + ω₃) * Complex.exp q‖ + ‖c₁ * (r : ℂ) * ω₃ * Complex.exp q‖ :=
            norm_add_le _ _
        _ ≤ ‖A (bX x + (r : ℂ) * dir) / A (bX x) * (R_Phi * Complex.exp q)‖ +
              ‖R_A * (1 + ω₃) * Complex.exp q‖ + ‖c₁ * (r : ℂ) * ω₃ * Complex.exp q‖ :=
            add_le_add (norm_add_le _ _) le_rfl
    have h_sum_bd : ‖A (bX x + (r : ℂ) * dir) / A (bX x) * (R_Phi * Complex.exp q)‖ +
          ‖R_A * (1 + ω₃) * Complex.exp q‖ + ‖c₁ * (r : ℂ) * ω₃ * Complex.exp q‖ ≤
        ((4 * M ^ 2 + M') * r ^ 2 + (Real.exp 1 * n * C₄ / 24 + M * n * C₃ / 6) * r ^ 4 +
          (Real.exp 2 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6) *
          Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
      calc ‖A (bX x + (r : ℂ) * dir) / A (bX x) * (R_Phi * Complex.exp q)‖ +
            ‖R_A * (1 + ω₃) * Complex.exp q‖ + ‖c₁ * (r : ℂ) * ω₃ * Complex.exp q‖
          ≤ ((Real.exp 1 * n * C₄ / 24) * r ^ 4 + (Real.exp 2 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6) *
                Real.exp (-(n * alphaX x / 3) * r ^ 2) +
              (4 * M ^ 2 + M') * r ^ 2 * Real.exp (-(n * alphaX x / 3) * r ^ 2) +
              (M * n * C₃ / 6) * r ^ 4 * Real.exp (-(n * alphaX x / 3) * r ^ 2) :=
            add_le_add (add_le_add h_termA h_termB) h_termC
        _ = ((4 * M ^ 2 + M') * r ^ 2 + (Real.exp 1 * n * C₄ / 24 + M * n * C₃ / 6) * r ^ 4 +
              (Real.exp 2 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6) *
              Real.exp (-(n * alphaX x / 3) * r ^ 2) := by ring
    calc ‖A (bX x)‖ * ‖A (bX x + (r : ℂ) * dir) / A (bX x) * (R_Phi * Complex.exp q) +
            R_A * (1 + ω₃) * Complex.exp q + c₁ * (r : ℂ) * ω₃ * Complex.exp q‖
        ≤ ‖A (bX x)‖ * (((4 * M ^ 2 + M') * r ^ 2 +
            (Real.exp 1 * n * C₄ / 24 + M * n * C₃ / 6) * r ^ 4 +
            (Real.exp 2 * n ^ 2 * C₃ ^ 2 / 72) * r ^ 6) *
            Real.exp (-(n * alphaX x / 3) * r ^ 2)) :=
          mul_le_mul_of_nonneg_left (h_tri.trans h_sum_bd) (norm_nonneg _)
      _ = (K₂ * r ^ 2 + K₄ * r ^ 4 + K₆ * r ^ 6) * Real.exp (-(n * alphaX x / 3) * r ^ 2) := by
          dsimp [K₂, K₄, K₆]; ring
  have h_core_rem_raw := gauss_core_remainder_le hn ha_pos hr₁_nn
    (by dsimp [K₂]; positivity) (by dsimp [K₄]; positivity) (by dsimp [K₆]; positivity)
    hE_int h_core_pt
  have h_core_rem : ‖∫ r in (-r₁)..r₁, E r‖ ≤
      ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (C_rem / (n * mX x ^ 3)) := by
    have hm3_a1 : mX x ^ 3 ≤ alphaX x := by
      calc mX x ^ 3 = mX x * mX x ^ 2 := by ring
        _ ≤ mX x * 1 ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm_pos.le hm_le_one 2) hm_pos.le
        _ = mX x := by ring
        _ ≤ alphaX x := hm_le_alpha
    have hm3_a2 : mX x ^ 3 ≤ alphaX x ^ 2 := by
      have hm_sq : mX x ^ 2 ≤ alphaX x ^ 2 := pow_le_pow_left₀ hm_pos.le hm_le_alpha 2
      calc mX x ^ 3 = mX x ^ 2 * mX x := by ring
        _ ≤ mX x ^ 2 * 1 := mul_le_mul_of_nonneg_left hm_le_one (sq_nonneg _)
        _ = mX x ^ 2 := mul_one _
        _ ≤ alphaX x ^ 2 := hm_sq
    have hm3_a3 : mX x ^ 3 ≤ alphaX x ^ 3 := pow_le_pow_left₀ hm_pos.le hm_le_alpha 3
    have hT1 : 3 * K₂ / (2 * n * alphaX x) ≤
        ‖A (bX x)‖ * (3 * (4 * M ^ 2 + M') / 2) / (n * mX x ^ 3) := by
      rw [show 3 * K₂ / (2 * n * alphaX x) =
        ‖A (bX x)‖ * (3 * (4 * M ^ 2 + M') / 2) / (n * alphaX x) by dsimp [K₂]; ring]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hm3_a1 hn.le)
    have hT2 : 27 * K₄ / (4 * (n * alphaX x) ^ 2) ≤
        ‖A (bX x)‖ * (27 * (Real.exp 1 * C₄ / 24 + M * C₃ / 6) / 4) / (n * mX x ^ 3) := by
      rw [show 27 * K₄ / (4 * (n * alphaX x) ^ 2) =
        ‖A (bX x)‖ * (27 * (Real.exp 1 * C₄ / 24 + M * C₃ / 6) / 4) / (n * alphaX x ^ 2) by
          dsimp [K₄]; field_simp [hn.ne'] ]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hm3_a2 hn.le)
    have hT3 : 405 * K₆ / (8 * (n * alphaX x) ^ 3) ≤
        ‖A (bX x)‖ * (405 * (Real.exp 2 * C₃ ^ 2 / 72) / 8) / (n * mX x ^ 3) := by
      rw [show 405 * K₆ / (8 * (n * alphaX x) ^ 3) =
        ‖A (bX x)‖ * (405 * (Real.exp 2 * C₃ ^ 2 / 72) / 8) / (n * alphaX x ^ 3) by
          dsimp [K₆]; field_simp [hn.ne'] ]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hm3_a3 hn.le)
    calc ‖∫ r in (-r₁)..r₁, E r‖
        ≤ √(2 * Real.pi / (n * alphaX x)) * √(3 / 2) *
            (3 * K₂ / (2 * n * alphaX x) + 27 * K₄ / (4 * (n * alphaX x) ^ 2) +
              405 * K₆ / (8 * (n * alphaX x) ^ 3)) := h_core_rem_raw
      _ ≤ √(2 * Real.pi / (n * alphaX x)) * √(3 / 2) *
            (‖A (bX x)‖ * (3 * (4 * M ^ 2 + M') / 2) / (n * mX x ^ 3) +
              ‖A (bX x)‖ * (27 * (Real.exp 1 * C₄ / 24 + M * C₃ / 6) / 4) / (n * mX x ^ 3) +
              ‖A (bX x)‖ * (405 * (Real.exp 2 * C₃ ^ 2 / 72) / 8) / (n * mX x ^ 3)) := by
          gcongr
      _ = ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (C_rem / (n * mX x ^ 3)) := by
          dsimp [C_rem]; ring
  have h_lead_eq : ∫ r in (-r₁)..r₁,
        S₀ * (1 + c₁ * (r : ℂ) + c₃ * (r : ℂ) ^ 3) * (gaussReal r : ℂ) =
      S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) := by
    have h_split_fn : (fun r : ℝ =>
          S₀ * (1 + c₁ * (r : ℂ) + c₃ * (r : ℂ) ^ 3) * (gaussReal r : ℂ)) =
        (fun r : ℝ => S₀ * (gaussReal r : ℂ) +
          (S₀ * c₁ * ((r : ℂ) * (gaussReal r : ℂ)) +
            S₀ * c₃ * ((r : ℂ) ^ 3 * (gaussReal r : ℂ)))) := by
      ext r; ring
    rw [h_split_fn]
    have hi0 : IntervalIntegrable (fun r : ℝ => S₀ * (gaussReal r : ℂ)) volume (-r₁) r₁ :=
      (by fun_prop : Continuous fun r : ℝ => S₀ * (gaussReal r : ℂ)).intervalIntegrable
        (μ := volume) (-r₁) r₁
    have hi1 : IntervalIntegrable (fun r : ℝ => S₀ * c₁ * ((r : ℂ) * (gaussReal r : ℂ)))
        volume (-r₁) r₁ :=
      (by fun_prop : Continuous fun r : ℝ => S₀ * c₁ * ((r : ℂ) * (gaussReal r : ℂ))).intervalIntegrable
        (μ := volume) (-r₁) r₁
    have hi3 : IntervalIntegrable (fun r : ℝ => S₀ * c₃ * ((r : ℂ) ^ 3 * (gaussReal r : ℂ)))
        volume (-r₁) r₁ :=
      (by fun_prop : Continuous fun r : ℝ => S₀ * c₃ * ((r : ℂ) ^ 3 * (gaussReal r : ℂ))).intervalIntegrable
        (μ := volume) (-r₁) r₁
    rw [intervalIntegral.integral_add hi0 (hi1.add hi3), intervalIntegral.integral_add hi1 hi3,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    have hodd1 : ∫ r in (-r₁)..r₁, (r : ℂ) * (gaussReal r : ℂ) = 0 := by
      simpa [gaussReal] using intervalIntegral_odd_mul_exp_neg_sq (r₁ := r₁)
        (a := n * alphaX x / 2) (n := 1) (by decide)
    have hodd3 : ∫ r in (-r₁)..r₁, (r : ℂ) ^ 3 * (gaussReal r : ℂ) = 0 := by
      simpa [gaussReal] using intervalIntegral_odd_mul_exp_neg_sq (r₁ := r₁)
        (a := n * alphaX x / 2) (n := 3) (by decide)
    rw [hodd1, hodd3, mul_zero, mul_zero, add_zero, add_zero]
    congr 1
    exact intervalIntegral.integral_ofReal
  have h_core_sub : (∫ r in (-r₁)..r₁, g r) - S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) =
      ∫ r in (-r₁)..r₁, E r := by
    have hg_lead : IntervalIntegrable
        (fun r : ℝ => S₀ * (1 + c₁ * (r : ℂ) + c₃ * (r : ℂ) ^ 3) * (gaussReal r : ℂ))
        volume (-r₁) r₁ :=
      (by fun_prop : Continuous fun r : ℝ =>
        S₀ * (1 + c₁ * (r : ℂ) + c₃ * (r : ℂ) ^ 3) * (gaussReal r : ℂ)).intervalIntegrable
        (μ := volume) (-r₁) r₁
    rw [← h_lead_eq, ← intervalIntegral.integral_sub hint_core hg_lead]
  have h_gauss_tail : ‖S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) -
      S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ)‖ ≤
      ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (√2 * C_tail / (n * mX x ^ 3)) := by
    have ht := gauss_tail_complement_le (a := n * alphaX x / 2) (by positivity) hr₁_nn
    have h_pi_eq : √(Real.pi / (n * alphaX x / 2)) = √(2 * Real.pi / (n * alphaX x)) := by
      congr 1; ring
    have h_pi_rhs : √(2 * Real.pi / (n * alphaX x / 2)) = √2 * √(2 * Real.pi / (n * alphaX x)) := by
      rw [← Real.sqrt_mul zero_le_two]
      congr 1; ring
    have h_exp_le : Real.exp (-(n * alphaX x / 2) * r₁ ^ 2 / 2) ≤
        Real.exp (-(c_core / 6) * (n * mX x ^ 3) ^ (1 / 3 : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 := h_core_exp hx hn hnm
      have hpos : 0 ≤ n * alphaX x * r₁ ^ 2 := by positivity
      linarith
    have h_tail_inv : Real.exp (-(c_core / 6) * (n * mX x ^ 3) ^ (1 / 3 : ℝ)) ≤
        C_tail / (n * mX x ^ 3) := by
      simpa using hC_tail_bd (n * mX x ^ 3) hnm
    have h_sub_eq : S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) -
          S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ) =
        S₀ * (((∫ r in (-r₁)..r₁, gaussReal r) - √(2 * Real.pi / (n * alphaX x)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h_sub_eq, norm_mul, hS₀_norm, Complex.norm_real, Real.norm_eq_abs]
    rw [h_pi_eq, h_pi_rhs] at ht
    calc ‖A (bX x)‖ * |(∫ r in (-r₁)..r₁, gaussReal r) - √(2 * Real.pi / (n * alphaX x))|
        ≤ ‖A (bX x)‖ * (Real.exp (-(n * alphaX x / 2) * r₁ ^ 2 / 2) *
            (√2 * √(2 * Real.pi / (n * alphaX x)))) :=
          mul_le_mul_of_nonneg_left ht (norm_nonneg _)
      _ ≤ ‖A (bX x)‖ * ((C_tail / (n * mX x ^ 3)) * (√2 * √(2 * Real.pi / (n * alphaX x)))) := by
          gcongr
          exact h_exp_le.trans h_tail_inv
      _ = ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (√2 * C_tail / (n * mX x ^ 3)) := by ring
  have h_decomp : localPosIntegral Φ₀ x n δ C₃ M M' A -
        S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ) =
      (∫ r in (-ℓ)..(-r₁), g r) + (∫ r in r₁..ℓ, g r) +
        (∫ r in (-r₁)..r₁, E r) +
        (S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) -
          S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ)) := by
    rw [hsplit, ← h_core_sub]
    ring
  intro dir S₀
  rw [h_decomp]
  have htri : ‖(∫ r in (-ℓ)..(-r₁), g r) + (∫ r in r₁..ℓ, g r) +
        (∫ r in (-r₁)..r₁, E r) +
        (S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) -
          S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ))‖ ≤
      ‖∫ r in (-ℓ)..(-r₁), g r‖ + ‖∫ r in r₁..ℓ, g r‖ +
        ‖∫ r in (-r₁)..r₁, E r‖ +
        ‖S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) -
          S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ)‖ :=
    calc ‖(∫ r in (-ℓ)..(-r₁), g r) + (∫ r in r₁..ℓ, g r) +
            (∫ r in (-r₁)..r₁, E r) +
            (S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) -
              S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ))‖
        ≤ ‖(∫ r in (-ℓ)..(-r₁), g r) + (∫ r in r₁..ℓ, g r) +
              (∫ r in (-r₁)..r₁, E r)‖ +
            ‖S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) -
              S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖(∫ r in (-ℓ)..(-r₁), g r) + (∫ r in r₁..ℓ, g r)‖ + ‖∫ r in (-r₁)..r₁, E r‖) +
            ‖S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) -
              S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ‖∫ r in (-ℓ)..(-r₁), g r‖ + ‖∫ r in r₁..ℓ, g r‖ +
            ‖∫ r in (-r₁)..r₁, E r‖ +
            ‖S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) -
              S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ)‖ :=
          add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
  calc ‖(∫ r in (-ℓ)..(-r₁), g r) + (∫ r in r₁..ℓ, g r) +
          (∫ r in (-r₁)..r₁, E r) +
          (S₀ * ((∫ r in (-r₁)..r₁, gaussReal r : ℝ) : ℂ) -
            S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ))‖
      ≤ ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (Real.exp 1 * √3 * C_tail / (n * mX x ^ 3)) +
          ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (Real.exp 1 * √3 * C_tail / (n * mX x ^ 3)) +
          ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (C_rem / (n * mX x ^ 3)) +
          ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (√2 * C_tail / (n * mX x ^ 3)) :=
        htri.trans (add_le_add (add_le_add (add_le_add h_ann_neg h_ann_pos) h_core_rem) h_gauss_tail)
    _ = ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (C_loc / (n * mX x ^ 3)) := by
        dsimp [C_loc]; ring

/-! ### 3. Main theorem: Lemma `SD_V'` (`esd:lemmap`) -/

/-- **Lemma `SD_V'` (`edge_transform_sd.tex`, Lemma `esd:lemmap`, l.204–231, `(SD.5)`)**:
Uniform two-saddle steepest-descent asymptotic for an abstract amplitude `A` satisfying `(i)–(iii)`.
Constants `N₀ ≥ 1` and `C ≥ 0` depend only on `(δ, C₃, C₄, M, M')` and not on `Φ₀, A, x, n`. -/
theorem lemma_SD_V_prime {δ C₃ C₄ M M' : ℝ} (hδ : 0 < δ) (_hδ_le : δ ≤ 1 / 4)
    (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) (hM : 0 ≤ M) (hM' : 0 ≤ M') :
    ∃ N₀ C : ℝ, 1 ≤ N₀ ∧ 0 ≤ C ∧
      ∀ {Φ₀ : ℂ → ℂ} {x n : ℝ} {A : ℂ → ℂ},
        xiStar < x → 0 < n → N₀ ≤ n * mX x ^ 3 →
        EdgePhaseData δ C₃ C₄ Φ₀ →
        TwoSaddleAmplitude Φ₀ x n δ M M' A →
        let k : ℝ := 4 * Real.pi * n * x / 3
        let Θ : ℝ := n * (Φ₀ (bX x)).im + k * edgeV x - Real.pi / 2 + Complex.arg (A (bX x))
        ∃ err : ℝ,
          |err| ≤ C / (n * mX x ^ 3) ∧
          edgeIntegral Φ₀ x n A =
            ((2 * ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) *
              (Real.cos Θ + err) : ℝ) : ℂ) := by
  obtain ⟨c_mo, C_mo, N_mo, hc_mo, hC_mo, hN_mo, h_mo⟩ :=
    middle_outer_pos_bound (M' := M') hδ hC₃ hM
  obtain ⟨N_loc, C_loc, hN_loc, hC_loc, h_loc⟩ :=
    localPosIntegral_asymp hδ hC₃ hC₄ hM hM'
  obtain ⟨C_exp, hC_exp_nn, hC_exp_bd⟩ :=
    exp_neg_rpow_mul_pow_le_inv (c := c_mo) (p := 1) hc_mo zero_lt_one 0
  refine ⟨max N_mo N_loc, C_mo * C_exp + C_loc, le_max_of_le_left hN_mo, by positivity,
    fun {Φ₀ x n A} hx hn hnm hΦ hA => ?_⟩
  let dir : ℂ := Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))
  let k : ℝ := 4 * Real.pi * n * x / 3
  let Θ : ℝ := n * (Φ₀ (bX x)).im + k * edgeV x - Real.pi / 2 + Complex.arg (A (bX x))
  let S₀ : ℂ := Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A (bX x) *
    Complex.exp ((n : ℂ) * phiX Φ₀ x (bX x)) * dir
  let S : ℂ := middlePosIntegral Φ₀ x n δ C₃ M M' A +
    localPosIntegral Φ₀ x n δ C₃ M M' A + outerPosIntegral Φ₀ x n δ C₃ M M' A
  have h_edge_eq : edgeIntegral Φ₀ x n A = ((2 * S.re : ℝ) : ℂ) :=
    edgeIntegral_eq_two_mul_re_pos hΦ hδ hx hA
  have hmo := h_mo hx hn ((le_max_left _ _).trans hnm) hΦ hA
  have hloc := h_loc hx hn ((le_max_right _ _).trans hnm) hΦ hA
  have hm_pos : 0 < mX x := mX_pos hx
  have hnm1 : 1 ≤ n * mX x ^ 3 := hN_mo.trans ((le_max_left _ _).trans hnm)
  have hexp_inv : Real.exp (-c_mo * (n * mX x ^ 3)) ≤ C_exp / (n * mX x ^ 3) := by
    simpa using hC_exp_bd (n * mX x ^ 3) hnm1
  have hmo_inv : ‖middlePosIntegral Φ₀ x n δ C₃ M M' A + outerPosIntegral Φ₀ x n δ C₃ M M' A‖ ≤
      ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (C_mo * C_exp / (n * mX x ^ 3)) := by
    calc ‖middlePosIntegral Φ₀ x n δ C₃ M M' A + outerPosIntegral Φ₀ x n δ C₃ M M' A‖
        ≤ ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (C_mo * Real.exp (-c_mo * (n * mX x ^ 3))) :=
          hmo
      _ ≤ ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (C_mo * (C_exp / (n * mX x ^ 3))) := by
          gcongr
      _ = ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (C_mo * C_exp / (n * mX x ^ 3)) := by
          ring
  let P : ℝ := ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x))
  have ha_pos : 0 < alphaX x := alphaX_pos hx
  have hAx_ne : A (bX x) ≠ 0 := hA.nonzero (bX x) (bX_mem_edgeStrip hδ.le x)
  have hP_pos : 0 < P := mul_pos (norm_pos_iff.mpr hAx_ne) (Real.sqrt_pos.mpr (by positivity))
  have hS₀_polar : S₀ = ((‖A (bX x)‖ : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ : ℂ)) :=
    saddle_prefactor_polar hΦ
  have hS₀_re : (S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ)).re = P * Real.cos Θ := by
    rw [hS₀_polar]
    have heq : ((‖A (bX x)‖ : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ : ℂ)) *
          (√(2 * Real.pi / (n * alphaX x)) : ℂ) =
        (P : ℂ) * Complex.exp (((Θ : ℝ) : ℂ) * Complex.I) := by
      dsimp [P]; push_cast; rw [mul_comm Complex.I (Θ : ℂ)]; ring
    rw [heq, Complex.exp_ofReal_mul_I]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  have h_abs_re : |S.re - P * Real.cos Θ| ≤ P * ((C_mo * C_exp + C_loc) / (n * mX x ^ 3)) := by
    rw [← hS₀_re, ← Complex.sub_re]
    have h1 := Complex.abs_re_le_norm (S - S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ))
    have hsplit : S - S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ) =
        (middlePosIntegral Φ₀ x n δ C₃ M M' A + outerPosIntegral Φ₀ x n δ C₃ M M' A) +
        (localPosIntegral Φ₀ x n δ C₃ M M' A - S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ)) := by
      dsimp [S]; ring
    have h2 : ‖S - S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ)‖ ≤
        P * ((C_mo * C_exp + C_loc) / (n * mX x ^ 3)) := by
      rw [hsplit]
      calc ‖(middlePosIntegral Φ₀ x n δ C₃ M M' A + outerPosIntegral Φ₀ x n δ C₃ M M' A) +
              (localPosIntegral Φ₀ x n δ C₃ M M' A - S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ))‖
          ≤ ‖middlePosIntegral Φ₀ x n δ C₃ M M' A + outerPosIntegral Φ₀ x n δ C₃ M M' A‖ +
              ‖localPosIntegral Φ₀ x n δ C₃ M M' A - S₀ * (√(2 * Real.pi / (n * alphaX x)) : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ P * (C_mo * C_exp / (n * mX x ^ 3)) + P * (C_loc / (n * mX x ^ 3)) :=
            add_le_add hmo_inv hloc
        _ = P * ((C_mo * C_exp + C_loc) / (n * mX x ^ 3)) := by ring
    exact h1.trans h2
  let err : ℝ := (S.re - P * Real.cos Θ) / P
  refine ⟨err, ?_, ?_⟩
  · dsimp [err]
    rw [abs_div, abs_of_pos hP_pos, div_le_iff₀ hP_pos]
    exact h_abs_re.trans_eq (mul_comm P _)
  · rw [h_edge_eq]
    congr 1
    have herr : P * (Real.cos Θ + err) = S.re := by
      dsimp [err]; field_simp [hP_pos.ne']; ring
    calc 2 * S.re = 2 * (P * (Real.cos Θ + err)) := by rw [herr]
      _ = 2 * ‖A (bX x)‖ * √(2 * Real.pi / (n * alphaX x)) * (Real.cos Θ + err) := by
          dsimp [P, Θ, k]; ring

/-! ### 4. Non-vacuity of `(EdgePhaseData, TwoSaddleAmplitude)` -/

private lemma cosh_re_im (z : ℂ) :
    (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im ∧
      (Complex.cosh z).im = Real.sinh z.re * Real.sin z.im := by
  have hde : Complex.cosh z =
      (Real.cosh z.re : ℂ) * (Real.cos z.im : ℂ) +
        (Real.sinh z.re : ℂ) * ((Real.sin z.im : ℂ) * Complex.I) := by
    conv_lhs => rw [(Complex.re_add_im z).symm]
    rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hde]
  constructor <;>
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

private lemma sinh_re_im (z : ℂ) :
    (Complex.sinh z).re = Real.sinh z.re * Real.cos z.im ∧
      (Complex.sinh z).im = Real.cosh z.re * Real.sin z.im := by
  have hde : Complex.sinh z =
      (Real.sinh z.re : ℂ) * (Real.cos z.im : ℂ) +
        (Real.cosh z.re : ℂ) * ((Real.sin z.im : ℂ) * Complex.I) := by
    conv_lhs => rw [(Complex.re_add_im z).symm]
    rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hde]
  constructor <;>
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

private lemma cosh_strip_norm_lower {z : ℂ} (hz : |z.im| ≤ Real.pi / 4) :
    Real.cosh z.re / √2 ≤ ‖Complex.cosh z‖ := by
  have hri := cosh_re_im z
  have hcos : √2 / 2 ≤ Real.cos z.im := by
    rw [← Real.cos_pi_div_four, ← Real.cos_abs z.im]
    exact Real.strictAntiOn_cos.antitoneOn
      ⟨abs_nonneg _, hz.trans (by linarith [Real.pi_pos])⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩ hz
  have hcos_sq : (1 / 2 : ℝ) ≤ Real.cos z.im ^ 2 := by
    have h1 : (√2 / 2) ^ 2 ≤ Real.cos z.im ^ 2 :=
      pow_le_pow_left₀ (by positivity) hcos 2
    have hsq : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
    calc (1 / 2 : ℝ) = (√2 / 2) ^ 2 := by rw [div_pow, hsq]; norm_num
      _ ≤ Real.cos z.im ^ 2 := h1
  have hnsq : ‖Complex.cosh z‖ ^ 2 = Real.cos z.im ^ 2 + Real.sinh z.re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hri.1, hri.2]
    have h1 := Real.cosh_sq z.re
    have h2 := Real.sin_sq_add_cos_sq z.im
    calc (Real.cosh z.re * Real.cos z.im) * (Real.cosh z.re * Real.cos z.im) +
          (Real.sinh z.re * Real.sin z.im) * (Real.sinh z.re * Real.sin z.im)
        = (Real.sinh z.re ^ 2 + 1) * Real.cos z.im ^ 2 + Real.sinh z.re ^ 2 * Real.sin z.im ^ 2 := by
          rw [← sq, ← sq, mul_pow, mul_pow, h1]
      _ = Real.cos z.im ^ 2 + Real.sinh z.re ^ 2 * (Real.sin z.im ^ 2 + Real.cos z.im ^ 2) := by
          ring
      _ = Real.cos z.im ^ 2 + Real.sinh z.re ^ 2 := by rw [h2, mul_one]
  have hcosh1 : 1 ≤ Real.cosh z.re := Real.one_le_cosh z.re
  have hlb_sq : (Real.cosh z.re / √2) ^ 2 ≤ ‖Complex.cosh z‖ ^ 2 := by
    have hsq : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
    have hsh : Real.sinh z.re ^ 2 = Real.cosh z.re ^ 2 - 1 := by
      linarith [Real.cosh_sq z.re]
    rw [hnsq, div_pow, hsq, hsh]
    nlinarith [hcosh1, hcos_sq]
  have hsqrt := Real.sqrt_le_sqrt hlb_sq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at hsqrt

private lemma sinh_norm_le_cosh (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.cosh z.re := by
  have hri := sinh_re_im z
  have hnsq : ‖Complex.sinh z‖ ^ 2 ≤ Real.cosh z.re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hri.1, hri.2]
    have hsh : Real.sinh z.re ^ 2 ≤ Real.cosh z.re ^ 2 := by
      linarith [Real.cosh_sq z.re]
    have h2 := Real.sin_sq_add_cos_sq z.im
    calc (Real.sinh z.re * Real.cos z.im) * (Real.sinh z.re * Real.cos z.im) +
          (Real.cosh z.re * Real.sin z.im) * (Real.cosh z.re * Real.sin z.im)
        = Real.sinh z.re ^ 2 * Real.cos z.im ^ 2 + Real.cosh z.re ^ 2 * Real.sin z.im ^ 2 := by ring
      _ ≤ Real.cosh z.re ^ 2 * Real.cos z.im ^ 2 + Real.cosh z.re ^ 2 * Real.sin z.im ^ 2 := by
          gcongr
      _ = Real.cosh z.re ^ 2 * (Real.sin z.im ^ 2 + Real.cos z.im ^ 2) := by ring
      _ = Real.cosh z.re ^ 2 := by rw [h2, mul_one]
  have hsqrt := Real.sqrt_le_sqrt hnsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (Real.cosh_pos _).le] at hsqrt

private lemma integrable_exp_neg_abs_half :
    Integrable (fun v : ℝ => Real.exp (-|v| / 2)) volume := by
  have h1 : IntegrableOn (fun v : ℝ => Real.exp (-|v| / 2)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2) 0).congr_fun
      (fun v hv => ?_) measurableSet_Iic
    rw [mem_Iic] at hv
    rw [abs_of_nonpos hv, show -(-v) / 2 = (1 / 2 : ℝ) * v by ring]
  have h2 : IntegrableOn (fun v : ℝ => Real.exp (-|v| / 2)) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0).congr_fun
      (fun v hv => ?_) measurableSet_Ioi
    rw [mem_Ioi] at hv
    rw [abs_of_pos hv, show -v / 2 = -(1 / 2 : ℝ) * v by ring]
  have huniv : (univ : Set ℝ) = Iic 0 ∪ Ioi 0 := by ext v; simp
  rw [← integrableOn_univ, huniv]
  exact h1.union h2

/-- Non-vacuity of the hypotheses of `lemma_SD_V_prime`: for any `0 < δ ≤ 1/4`, there exist
`C₃, C₄, Φ₀, x, n, M, M', A` with `xiStar < x`, `0 < n`, `EdgePhaseData δ C₃ C₄ Φ₀`, and
`TwoSaddleAmplitude Φ₀ x n δ M M' A`. -/
theorem twoSaddleAmplitude_nonvacuous {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ (C₃ C₄ : ℝ) (Φ₀ : ℂ → ℂ) (x n M M' : ℝ) (A : ℂ → ℂ),
      xiStar < x ∧ 0 < n ∧
      EdgePhaseData δ C₃ C₄ Φ₀ ∧ TwoSaddleAmplitude Φ₀ x n δ M M' A := by
  obtain ⟨C₃, C₄, Φ₀, hΦ⟩ := edgePhaseData_nonvacuous hδ0 hδ1
  let x : ℝ := xiStar + 1
  let n : ℝ := 1
  let c₀ : ℝ := (Φ₀ (Complex.I / 2)).im
  let pref : ℂ := Complex.exp (Complex.I * ((Real.pi / 4 - c₀ : ℝ) : ℂ))
  let A : ℂ → ℂ := fun b => pref * (Complex.cosh ((b - Complex.I / 2) / 2))⁻¹
  let M : ℝ := √2 / 2
  let M' : ℝ := 1 / 2
  have hx : xiStar < x := by dsimp [x]; linarith
  have hn : 0 < n := by dsimp [n]; norm_num
  let U : Set ℂ := {b : ℂ | |b.im - 1 / 2| < 3 / 8}
  have hU_open : IsOpen U :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const
  have hstrip_U : edgeStrip δ ⊆ U := fun b hb => by
    change |b.im - 1 / 2| < 3 / 8
    exact hb.trans_lt (hδ1.trans_lt (by norm_num))
  have hz_pi4 : ∀ b ∈ U, |((b - Complex.I / 2) / 2).im| ≤ Real.pi / 4 := fun b hb => by
    have him : ((b - Complex.I / 2) / 2).im = (b.im - 1 / 2) / 2 := by simp
    rw [him, abs_div, abs_two]
    have hb' : |b.im - 1 / 2| < 3 / 8 := hb
    linarith [Real.pi_gt_three]
  have hcosh_ne : ∀ b ∈ U, Complex.cosh ((b - Complex.I / 2) / 2) ≠ 0 := fun b hb => by
    have hlb := cosh_strip_norm_lower (hz_pi4 b hb)
    have hpos : 0 < Real.cosh ((b - Complex.I / 2) / 2).re / √2 :=
      div_pos (Real.cosh_pos _) (Real.sqrt_pos.mpr zero_lt_two)
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hpos hlb))
  have hA_diff_U : DifferentiableOn ℂ A U := by
    intro b hb
    have hlin : HasDerivAt (fun z : ℂ => (z - Complex.I / 2) / 2) (1 / 2 : ℂ) b := by
      simpa using ((hasDerivAt_id b).sub_const _).div_const (2 : ℂ)
    have hch : HasDerivAt (fun z : ℂ => Complex.cosh ((z - Complex.I / 2) / 2))
        (Complex.sinh ((b - Complex.I / 2) / 2) * (1 / 2 : ℂ)) b :=
      (Complex.hasDerivAt_cosh _).comp b hlin
    exact ((hch.inv (hcosh_ne b hb)).const_mul pref).differentiableAt.differentiableWithinAt
  have hA_an : AnalyticOnNhd ℂ A (edgeStrip δ) := (hA_diff_U.analyticOnNhd hU_open).mono hstrip_U
  have hA_ne : ∀ b ∈ edgeStrip δ, A b ≠ 0 := fun b hb =>
    mul_ne_zero (Complex.exp_ne_zero _) (inv_ne_zero (hcosh_ne b (hstrip_U hb)))
  have hlogderiv_eq : ∀ b ∈ U,
      deriv A b / A b = -(1 / 2 : ℂ) * Complex.sinh ((b - Complex.I / 2) / 2) /
        Complex.cosh ((b - Complex.I / 2) / 2) := fun b hb => by
    have hlin : HasDerivAt (fun z : ℂ => (z - Complex.I / 2) / 2) (1 / 2 : ℂ) b := by
      have h1 : HasDerivAt (fun z : ℂ => z - Complex.I / 2) 1 b := (hasDerivAt_id b).sub_const _
      simpa using h1.div_const (2 : ℂ)
    have hch : HasDerivAt (fun z : ℂ => Complex.cosh ((z - Complex.I / 2) / 2))
        (Complex.sinh ((b - Complex.I / 2) / 2) * (1 / 2 : ℂ)) b :=
      (Complex.hasDerivAt_cosh _).comp b hlin
    have hinv := hch.inv (hcosh_ne b hb)
    have hA_d := hinv.const_mul pref
    change deriv (fun y => pref * (fun z => Complex.cosh ((z - Complex.I / 2) / 2))⁻¹ y) b / A b = _
    rw [hA_d.deriv]
    have hne := hcosh_ne b hb
    have hpref : pref ≠ 0 := Complex.exp_ne_zero _
    dsimp [A]
    field_simp [hne, hpref]
  have hlogderiv_bd : ∀ b ∈ edgeStrip δ, ‖deriv A b / A b‖ ≤ M := fun b hb => by
    rw [hlogderiv_eq b (hstrip_U hb)]
    have hsh := sinh_norm_le_cosh ((b - Complex.I / 2) / 2)
    have hch := cosh_strip_norm_lower (hz_pi4 b (hstrip_U hb))
    have h12 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by
      rw [norm_neg]; norm_num
    have hcosh_pos : 0 < Real.cosh ((b - Complex.I / 2) / 2).re := Real.cosh_pos _
    rw [norm_div, norm_mul, h12]
    calc (1 / 2) * ‖Complex.sinh ((b - Complex.I / 2) / 2)‖ /
          ‖Complex.cosh ((b - Complex.I / 2) / 2)‖
        ≤ (1 / 2) * Real.cosh ((b - Complex.I / 2) / 2).re /
            (Real.cosh ((b - Complex.I / 2) / 2).re / √2) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hsh (by norm_num))
            (div_pos hcosh_pos (Real.sqrt_pos.mpr zero_lt_two)) hch
      _ = M := by
          dsimp [M]
          field_simp [hcosh_pos.ne']
  have hlogderiv2_bd : ∀ b ∈ edgeStrip δ, ‖deriv (fun z => deriv A z / A z) b‖ ≤ M' := fun b hb => by
    let L₀ : ℂ → ℂ := fun z =>
      -(1 / 2 : ℂ) * Complex.sinh ((z - Complex.I / 2) / 2) / Complex.cosh ((z - Complex.I / 2) / 2)
    have hev : (fun z => deriv A z / A z) =ᶠ[𝓝 b] L₀ :=
      Filter.eventually_of_mem (hU_open.mem_nhds (hstrip_U hb)) hlogderiv_eq
    have hL₀_d : HasDerivAt L₀ (-(1 / 4 : ℂ) / Complex.cosh ((b - Complex.I / 2) / 2) ^ 2) b := by
      have hlin : HasDerivAt (fun z : ℂ => (z - Complex.I / 2) / 2) (1 / 2 : ℂ) b := by
        simpa using ((hasDerivAt_id b).sub_const _).div_const (2 : ℂ)
      have hsh : HasDerivAt (fun z : ℂ => Complex.sinh ((z - Complex.I / 2) / 2))
          (Complex.cosh ((b - Complex.I / 2) / 2) * (1 / 2 : ℂ)) b :=
        (Complex.hasDerivAt_sinh _).comp b hlin
      have hch : HasDerivAt (fun z : ℂ => Complex.cosh ((z - Complex.I / 2) / 2))
          (Complex.sinh ((b - Complex.I / 2) / 2) * (1 / 2 : ℂ)) b :=
        (Complex.hasDerivAt_cosh _).comp b hlin
      have hdiv := (hsh.const_mul (-(1 / 2 : ℂ))).div hch (hcosh_ne b (hstrip_U hb))
      refine hdiv.congr_deriv ?_
      have hne := hcosh_ne b (hstrip_U hb)
      let w : ℂ := (b - Complex.I / 2) / 2
      change (-(1 / 2 : ℂ) * (Complex.cosh w * (1 / 2)) * Complex.cosh w -
          -(1 / 2 : ℂ) * Complex.sinh w * (Complex.sinh w * (1 / 2))) / Complex.cosh w ^ 2 =
        -(1 / 4 : ℂ) / Complex.cosh w ^ 2
      have hsq_eq : Complex.cosh w ^ 2 - Complex.sinh w ^ 2 = 1 := by
        simpa [w, sq] using Complex.cosh_sq_sub_sinh_sq w
      calc (-(1 / 2 : ℂ) * (Complex.cosh w * (1 / 2)) * Complex.cosh w -
            -(1 / 2 : ℂ) * Complex.sinh w * (Complex.sinh w * (1 / 2))) / Complex.cosh w ^ 2
          = (-(1 / 4 : ℂ) * (Complex.cosh w ^ 2 - Complex.sinh w ^ 2)) / Complex.cosh w ^ 2 := by
            ring
        _ = -(1 / 4 : ℂ) / Complex.cosh w ^ 2 := by rw [hsq_eq, mul_one]
    rw [hev.deriv_eq, hL₀_d.deriv, norm_div, norm_pow]
    have h14 : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by rw [norm_neg]; norm_num
    have hch := cosh_strip_norm_lower (hz_pi4 b (hstrip_U hb))
    have hch_sq : 1 / 2 ≤ ‖Complex.cosh ((b - Complex.I / 2) / 2)‖ ^ 2 := by
      have h1 : 1 / √2 ≤ Real.cosh ((b - Complex.I / 2) / 2).re / √2 :=
        div_le_div_of_nonneg_right (Real.one_le_cosh _) (Real.sqrt_nonneg _)
      have h2 : (1 / √2) ^ 2 ≤ ‖Complex.cosh ((b - Complex.I / 2) / 2)‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) (h1.trans hch) 2
      have hsq : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
      calc (1 / 2 : ℝ) = (1 / √2) ^ 2 := by rw [div_pow, one_pow, hsq]
        _ ≤ ‖Complex.cosh ((b - Complex.I / 2) / 2)‖ ^ 2 := h2
    rw [h14]
    calc (1 / 4 : ℝ) / ‖Complex.cosh ((b - Complex.I / 2) / 2)‖ ^ 2
        ≤ (1 / 4 : ℝ) / (1 / 2) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hch_sq
      _ = M' := by dsimp [M']; norm_num
  have hA_exp_decay : ∀ v t : ℝ, |t - 1 / 2| ≤ δ →
      ‖A ((v : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * √2 * Real.exp (-|v| / 2) := fun v t ht => by
    have hz : (((v : ℂ) + (t : ℂ) * Complex.I - Complex.I / 2) / 2).re = v / 2 := by
      simp
    have hmemU : (v : ℂ) + (t : ℂ) * Complex.I ∈ U := hstrip_U (by simpa [edgeStrip] using ht)
    have hlb := cosh_strip_norm_lower (hz_pi4 _ hmemU)
    rw [hz] at hlb
    have hcosh_exp : Real.exp (|v| / 2) / 2 ≤ Real.cosh (v / 2) := by
      rw [Real.cosh_eq, add_div]
      rcases le_total 0 v with hv | hv
      · rw [abs_of_nonneg hv]
        linarith [Real.exp_pos (-(v / 2))]
      · rw [abs_of_nonpos hv, neg_div]
        linarith [Real.exp_pos (v / 2)]
    have hexp_inv : (Real.exp (|v| / 2) / (2 * √2)) ≤
        ‖Complex.cosh (((v : ℂ) + (t : ℂ) * Complex.I - Complex.I / 2) / 2)‖ := by
      calc Real.exp (|v| / 2) / (2 * √2)
          = (Real.exp (|v| / 2) / 2) / √2 := by ring
        _ ≤ Real.cosh (v / 2) / √2 := div_le_div_of_nonneg_right hcosh_exp (Real.sqrt_nonneg _)
        _ ≤ ‖Complex.cosh (((v : ℂ) + (t : ℂ) * Complex.I - Complex.I / 2) / 2)‖ := hlb
    have hpref_norm : ‖pref‖ = 1 := by
      dsimp [pref]
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
    dsimp [A]
    rw [norm_mul, hpref_norm, one_mul, norm_inv]
    calc ‖Complex.cosh (((v : ℂ) + (t : ℂ) * Complex.I - Complex.I / 2) / 2)‖⁻¹
        ≤ (Real.exp (|v| / 2) / (2 * √2))⁻¹ :=
          inv_anti₀ (by positivity) hexp_inv
      _ = 2 * √2 * Real.exp (-|v| / 2) := by
          rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, show -(|v| / 2) = -|v| / 2 by ring]
  let B : ℝ := (4 * Real.pi / 3) * δ * x + C₃ * δ ^ 3 / 6
  have hphi_strip_bd : ∀ v t : ℝ, 1 / 2 - δ ≤ t → t ≤ 1 / 2 →
      (phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I)).re ≤ B := fun v t ht1 ht2 => by
    let u : ℝ := t - 1 / 2
    have hu_abs : |u| ≤ δ := by dsimp [u]; exact abs_le.mpr ⟨by linarith, by linarith⟩
    have ht_Tay := phiX_re_normal_taylor hΦ hδ0.le x v u hu_abs
    have heq_pt : (v : ℂ) + Complex.I * ((1 / 2 + u : ℝ) : ℂ) =
        (v : ℂ) + (t : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [u]
    rw [heq_pt] at ht_Tay
    have ht_le := (abs_le.mp ht_Tay).2
    have hF_pos : 0 < edgeF v := by
      unfold edgeF
      exact div_pos (Real.arsinh_pos_iff.mpr (Real.cosh_pos _)) Real.pi_pos
    have hu_nonpos : u ≤ 0 := by dsimp [u]; linarith
    have h1 : (4 * Real.pi / 3) * u * (edgeF v - x) ≤ (4 * Real.pi / 3) * δ * x := by
      have hFu : u * edgeF v ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hu_nonpos hF_pos.le
      have hx_pos : 0 < x := lt_trans xiStar_pos hx
      have hneg : -u ≤ δ := by linarith [(abs_le.mp hu_abs).1]
      calc (4 * Real.pi / 3) * u * (edgeF v - x)
          = (4 * Real.pi / 3) * (u * edgeF v) + (4 * Real.pi / 3) * (-u) * x := by ring
        _ ≤ 0 + (4 * Real.pi / 3) * δ * x := by
            refine add_le_add (mul_nonpos_of_nonneg_of_nonpos (by positivity) hFu) ?_
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hneg (by positivity)) hx_pos.le
        _ = (4 * Real.pi / 3) * δ * x := zero_add _
    have h2 : C₃ * |u| ^ 3 / 6 ≤ C₃ * δ ^ 3 / 6 := by
      have hC₃_nn : 0 ≤ C₃ := (norm_nonneg _).trans (hΦ.deriv3_bound (bX x) (bX_mem_edgeStrip hδ0.le x))
      gcongr
    dsimp [B]
    linarith
  have h_edge_int : Integrable (fun v : ℝ =>
      A ((v : ℂ) + Complex.I / 2) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
    have hcont : Continuous (fun v : ℝ =>
        A ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
      refine Continuous.mul ?_ ?_
      · exact hA_an.continuousOn.comp_continuous (by fun_prop) fun v =>
          mem_edgeStrip_edge hδ0.le v
      · exact Complex.continuous_exp.comp (continuous_const.mul
          ((phiX_analyticOnNhd hΦ x).continuousOn.comp_continuous (by fun_prop) fun v =>
            mem_edgeStrip_edge hδ0.le v))
    refine integrable_exp_neg_abs_half.const_mul (2 * √2) |>.mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    have heq : (v : ℂ) + Complex.I / 2 = (v : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [norm_mul, heq, Complex.norm_exp]
    have hre0 : ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)).re = 0 := by
      rw [← heq]
      simp [phiX_re_edge hΦ x v]
    rw [hre0, Real.exp_zero, mul_one]
    exact hA_exp_decay v (1 / 2) (by simpa using hδ0.le)
  have h_lower_int : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Integrable (fun v : ℝ =>
        A ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)))) := by
    intro u₀ hu₀_pos hu₀_le
    have hmem : ∀ v : ℝ, (v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ) ∈ edgeStrip δ := fun v => by
      change |((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)).im - 1 / 2| ≤ δ
      simpa [abs_of_nonneg hu₀_pos.le] using hu₀_le
    have hcont : Continuous (fun v : ℝ =>
        A ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)))) := by
      refine Continuous.mul ?_ ?_
      · exact hA_an.continuousOn.comp_continuous (by fun_prop) hmem
      · exact Complex.continuous_exp.comp (continuous_const.mul
          ((phiX_analyticOnNhd hΦ x).continuousOn.comp_continuous (by fun_prop) hmem))
    refine (integrable_exp_neg_abs_half.const_mul (2 * √2 * Real.exp (n * B))).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    have heq : (v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ) =
        (v : ℂ) + ((1 / 2 - u₀ : ℝ) : ℂ) * Complex.I := by ring
    rw [heq, norm_mul, Complex.norm_exp]
    have hA_bd := hA_exp_decay v (1 / 2 - u₀) (by
      rw [show (1 / 2 - u₀) - 1 / 2 = -u₀ by ring, abs_neg, abs_of_nonneg hu₀_pos.le]
      exact hu₀_le)
    have hphi_bd := hphi_strip_bd v (1 / 2 - u₀) (by linarith) (by linarith)
    have hre : ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + ((1 / 2 - u₀ : ℝ) : ℂ) * Complex.I)).re =
        n * (phiX Φ₀ x ((v : ℂ) + ((1 / 2 - u₀ : ℝ) : ℂ) * Complex.I)).re := by
      simp
    rw [hre]
    calc ‖A ((v : ℂ) + ((1 / 2 - u₀ : ℝ) : ℂ) * Complex.I)‖ *
          Real.exp (n * (phiX Φ₀ x ((v : ℂ) + ((1 / 2 - u₀ : ℝ) : ℂ) * Complex.I)).re)
        ≤ (2 * √2 * Real.exp (-|v| / 2)) * Real.exp (n * B) :=
          mul_le_mul hA_bd (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hphi_bd hn.le))
            (Real.exp_pos _).le (by positivity)
      _ = 2 * √2 * Real.exp (n * B) * Real.exp (-|v| / 2) := by ring
  have h_vert_bd : ∀ (s : ℝ), |s| = 1 → ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Tendsto (fun R : ℝ => ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
        A ((s * R : ℝ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((s * R : ℝ) + (t : ℂ) * Complex.I)))
        atTop (𝓝 0) := by
    intro s hs u₀ hu₀_pos hu₀_le
    have hbound : ∀ᶠ R : ℝ in atTop,
        ‖∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
          A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
            Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤
          (2 * √2 * Real.exp (n * B) * u₀) * Real.exp (-R / 2) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      have hn_int := intervalIntegral.norm_integral_le_integral_norm
        (f := fun t : ℝ => A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
        (μ := volume) (by linarith : 1 / 2 - u₀ ≤ 1 / 2)
      have hcont : ContinuousOn (fun t : ℝ => ‖A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖)
          (Icc (1 / 2 - u₀) (1 / 2)) := by
        refine ContinuousOn.norm (ContinuousOn.mul ?_ ?_)
        · refine hA_an.continuousOn.comp (by fun_prop) fun t ht => ?_
          change |(((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
          simpa using abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        · refine Complex.continuous_exp.continuousOn.comp (continuousOn_const.mul ?_)
            fun _ _ => mem_univ _
          refine (phiX_analyticOnNhd hΦ x).continuousOn.comp (by fun_prop) fun t ht => ?_
          change |(((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
          simpa using abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hm_le : ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
            ‖A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤
          ∫ _t in (1 / 2 - u₀)..(1 / 2 : ℝ), (2 * √2 * Real.exp (n * B)) * Real.exp (-R / 2) := by
        refine intervalIntegral.integral_mono_on (by linarith : 1 / 2 - u₀ ≤ 1 / 2)
          ((hcont.mono (by rw [Set.uIcc_of_le (by linarith)])).intervalIntegrable)
          (intervalIntegrable_const (μ := volume)) fun t ht => ?_
        have ht_strip : |t - 1 / 2| ≤ δ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hA_bd := hA_exp_decay (s * R) t ht_strip
        have hphi_bd := hphi_strip_bd (s * R) t (by linarith [ht.1]) ht.2
        have habs_sR : |s * R| = R := by
          rw [abs_mul, hs, one_mul, abs_of_nonneg hR]
        rw [habs_sR] at hA_bd
        rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
        calc ‖A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ *
              Real.exp (n * (phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re)
            ≤ (2 * √2 * Real.exp (-R / 2)) * Real.exp (n * B) :=
              mul_le_mul hA_bd (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hphi_bd hn.le))
                (Real.exp_pos _).le (by positivity)
          _ = (2 * √2 * Real.exp (n * B)) * Real.exp (-R / 2) := by ring
      have hc_eq : ∫ _t in (1 / 2 - u₀)..(1 / 2 : ℝ),
            (2 * √2 * Real.exp (n * B)) * Real.exp (-R / 2) =
          (2 * √2 * Real.exp (n * B) * u₀) * Real.exp (-R / 2) := by
        simp only [intervalIntegral.integral_const, sub_sub_cancel, smul_eq_mul]
        ring
      exact hn_int.trans (hm_le.trans_eq hc_eq)
    have ht_zero : Tendsto (fun R : ℝ => (2 * √2 * Real.exp (n * B) * u₀) * Real.exp (-R / 2))
        atTop (𝓝 0) := by
      have hexp : Tendsto (fun R : ℝ => Real.exp (-R / 2)) atTop (𝓝 0) := by
        refine squeeze_zero' (Eventually.of_forall fun R => (Real.exp_pos _).le) ?_
          (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun R : ℝ => (2 : ℝ) / R) atTop (𝓝 0))
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
        have h1 : R / 2 ≤ Real.exp (R / 2) := by linarith [Real.add_one_le_exp (R / 2)]
        rw [show -R / 2 = -(R / 2) by ring, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
        simpa [one_div, inv_div] using h1
      simpa using hexp.const_mul (2 * √2 * Real.exp (n * B) * u₀)
    exact squeeze_zero_norm' hbound ht_zero
  have h_vert_R : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Tendsto (fun R : ℝ => ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
        A ((R : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((R : ℂ) + (t : ℂ) * Complex.I)))
        atTop (𝓝 0) := fun u₀ hu₀_pos hu₀_le => by
    simpa using h_vert_bd 1 abs_one u₀ hu₀_pos hu₀_le
  have h_vert_L : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Tendsto (fun R : ℝ => ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
        A ((-R : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((-R : ℂ) + (t : ℂ) * Complex.I)))
        atTop (𝓝 0) := fun u₀ hu₀_pos hu₀_le => by
    simpa [Complex.ofReal_neg] using h_vert_bd (-1) (by norm_num) u₀ hu₀_pos hu₀_le
  have h_ref : ∀ v : ℝ,
      Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
        A ((-v : ℂ) + Complex.I / 2) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((-v : ℂ) + Complex.I / 2)) =
      starRingEnd ℂ (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
        A ((v : ℂ) + Complex.I / 2) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
    let symΦ : ℝ → ℂ := fun t =>
      Φ₀ ((t : ℂ) + Complex.I / 2) + Φ₀ ((-t : ℂ) + Complex.I / 2)
    have h_deriv_sym : ∀ t : ℝ, HasDerivAt symΦ 0 t := fun t => by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) + Complex.I / 2) 1 t := by
        have h := (Complex.ofRealCLM.hasDerivAt (x := t)).add_const (Complex.I / 2)
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_one] at h
        exact h
      have h2 : HasDerivAt (fun s : ℝ => ((-s : ℝ) : ℂ) + Complex.I / 2) (-1) t := by
        have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).neg).add_const (Complex.I / 2)
        simp only [Complex.ofRealCLM_apply, Complex.ofReal_one] at h
        simpa [Complex.ofReal_neg] using h
      have hp1 := (hΦ.holo _ (mem_edgeStrip_edge hδ0.le t)).differentiableAt.hasDerivAt.comp t h1
      have hp2 := (hΦ.holo _ (mem_edgeStrip_edge hδ0.le (-t))).differentiableAt.hasDerivAt.comp t h2
      rw [show (deriv Φ₀ ((t : ℂ) + Complex.I / 2)) =
          -(4 * (Real.pi : ℂ) * Complex.I / 3) * (edgeF t : ℂ) from hΦ.deriv_edge t] at hp1
      rw [show (deriv Φ₀ (((-t : ℝ) : ℂ) + Complex.I / 2)) =
          -(4 * (Real.pi : ℂ) * Complex.I / 3) * (edgeF (-t) : ℂ) from hΦ.deriv_edge (-t),
        edgeF_neg t] at hp2
      have hadd : HasDerivAt (fun s : ℝ => (Φ₀ ∘ fun u : ℝ => (u : ℂ) + Complex.I / 2) s +
            (Φ₀ ∘ fun u : ℝ => ((-u : ℝ) : ℂ) + Complex.I / 2) s) (0 : ℂ) t :=
        (hp1.fun_add hp2).congr_deriv (by ring)
      exact hadd.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp [symΦ, Complex.ofReal_neg])
    have h_sym_const : ∀ v : ℝ, symΦ v = 2 * Φ₀ (Complex.I / 2) := fun v => by
      have h0 : ∀ t : ℝ, deriv symΦ t = 0 := fun t => (h_deriv_sym t).deriv
      have heq := is_const_of_deriv_eq_zero
        (fun t => (h_deriv_sym t).differentiableAt) h0 v 0
      simpa [symΦ, two_mul] using heq
    have hΦ₀_eq : Φ₀ (Complex.I / 2) = Complex.I * (c₀ : ℂ) := by
      have hre : (Φ₀ (Complex.I / 2)).re = 0 := by simpa using hΦ.re_edge 0
      apply Complex.ext <;> simp [c₀, hre]
    intro v
    have h_phi_rel : phiX Φ₀ x ((-v : ℂ) + Complex.I / 2) =
        starRingEnd ℂ (phiX Φ₀ x ((v : ℂ) + Complex.I / 2)) + 2 * Complex.I * (c₀ : ℂ) := by
      have hre0 : (phiX Φ₀ x ((v : ℂ) + Complex.I / 2)).re = 0 := phiX_re_edge hΦ x v
      have hconj : starRingEnd ℂ (phiX Φ₀ x ((v : ℂ) + Complex.I / 2)) =
          -phiX Φ₀ x ((v : ℂ) + Complex.I / 2) := by
        apply Complex.ext <;> simp [hre0]
      have hsum : phiX Φ₀ x ((v : ℂ) + Complex.I / 2) + phiX Φ₀ x ((-v : ℂ) + Complex.I / 2) =
          2 * Complex.I * (c₀ : ℂ) := by
        unfold phiX
        have hv1 : ((v : ℂ) + Complex.I / 2) - Complex.I / 2 = (v : ℂ) := by ring
        have hv2 : ((-v : ℂ) + Complex.I / 2) - Complex.I / 2 = (-v : ℂ) := by ring
        rw [hv1, hv2]
        have hs := h_sym_const v
        have hs' : Φ₀ ((v : ℂ) + Complex.I / 2) + Φ₀ ((-v : ℂ) + Complex.I / 2) =
            2 * Φ₀ (Complex.I / 2) := by
          simpa [symΦ, Complex.ofReal_neg] using hs
        calc Φ₀ ((v : ℂ) + Complex.I / 2) + Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * (v : ℂ) +
              (Φ₀ ((-v : ℂ) + Complex.I / 2) + Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * (-v : ℂ))
            = Φ₀ ((v : ℂ) + Complex.I / 2) + Φ₀ ((-v : ℂ) + Complex.I / 2) := by ring
          _ = 2 * Φ₀ (Complex.I / 2) := hs'
          _ = 2 * (Complex.I * (c₀ : ℂ)) := by rw [hΦ₀_eq]
          _ = 2 * Complex.I * (c₀ : ℂ) := by ring
      rw [hconj]
      calc phiX Φ₀ x ((-v : ℂ) + Complex.I / 2)
          = (phiX Φ₀ x ((v : ℂ) + Complex.I / 2) + phiX Φ₀ x ((-v : ℂ) + Complex.I / 2)) -
              phiX Φ₀ x ((v : ℂ) + Complex.I / 2) := by ring
        _ = -phiX Φ₀ x ((v : ℂ) + Complex.I / 2) + 2 * Complex.I * (c₀ : ℂ) := by
            rw [hsum]; ring
    have h_epref : Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * pref =
        Complex.exp (-Complex.I * (c₀ : ℂ)) := by
      dsimp [pref]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hcosh_even_real : (Complex.cosh (((-v : ℂ) + Complex.I / 2 - Complex.I / 2) / 2))⁻¹ =
        (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) := by
      have hz1 : ((-v : ℂ) + Complex.I / 2 - Complex.I / 2) / 2 = -(((v / 2 : ℝ) : ℂ)) := by
        push_cast; ring
      rw [hz1, Complex.cosh_neg, ← Complex.ofReal_cosh, ← Complex.ofReal_inv]
    have hcosh_pos_real : (Complex.cosh (((v : ℂ) + Complex.I / 2 - Complex.I / 2) / 2))⁻¹ =
        (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) := by
      have hz1 : ((v : ℂ) + Complex.I / 2 - Complex.I / 2) / 2 = ((v / 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hz1, ← Complex.ofReal_cosh, ← Complex.ofReal_inv]
    have h_exp_conj : Complex.exp (-Complex.I * (c₀ : ℂ) +
          (starRingEnd ℂ (phiX Φ₀ x ((v : ℂ) + Complex.I / 2)) + 2 * Complex.I * (c₀ : ℂ))) =
        starRingEnd ℂ (Complex.exp (-Complex.I * (c₀ : ℂ) +
          phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_add, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      ring
    dsimp [A, n]
    simp only [one_mul]
    calc Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          (pref * (Complex.cosh (((-v : ℂ) + Complex.I / 2 - Complex.I / 2) / 2))⁻¹) *
          Complex.exp (phiX Φ₀ x ((-v : ℂ) + Complex.I / 2))
        = (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * pref) *
            (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
            Complex.exp (phiX Φ₀ x ((-v : ℂ) + Complex.I / 2)) := by
          rw [hcosh_even_real]; ring
      _ = (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
            Complex.exp (-Complex.I * (c₀ : ℂ) +
              (starRingEnd ℂ (phiX Φ₀ x ((v : ℂ) + Complex.I / 2)) + 2 * Complex.I * (c₀ : ℂ))) := by
          rw [h_epref, h_phi_rel]
          calc Complex.exp (-Complex.I * (c₀ : ℂ)) * (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
                Complex.exp (starRingEnd ℂ (phiX Φ₀ x ((v : ℂ) + Complex.I / 2)) +
                  2 * Complex.I * (c₀ : ℂ))
              = (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
                  (Complex.exp (-Complex.I * (c₀ : ℂ)) *
                    Complex.exp (starRingEnd ℂ (phiX Φ₀ x ((v : ℂ) + Complex.I / 2)) +
                      2 * Complex.I * (c₀ : ℂ))) := by ring
            _ = (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
                  Complex.exp (-Complex.I * (c₀ : ℂ) +
                    (starRingEnd ℂ (phiX Φ₀ x ((v : ℂ) + Complex.I / 2)) + 2 * Complex.I * (c₀ : ℂ))) := by
                rw [← Complex.exp_add]
      _ = starRingEnd ℂ ((((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
            Complex.exp (-Complex.I * (c₀ : ℂ) + phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
          rw [h_exp_conj, map_mul, Complex.conj_ofReal]
      _ = starRingEnd ℂ (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
            (pref * (Complex.cosh (((v : ℂ) + Complex.I / 2 - Complex.I / 2) / 2))⁻¹) *
            Complex.exp (phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
          congr 1
          rw [hcosh_pos_real]
          calc (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
                Complex.exp (-Complex.I * (c₀ : ℂ) + phiX Φ₀ x ((v : ℂ) + Complex.I / 2))
              = (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ) *
                  (Complex.exp (-Complex.I * (c₀ : ℂ)) *
                    Complex.exp (phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
                  rw [← Complex.exp_add]
            _ = Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
                  (pref * (((Real.cosh (v / 2))⁻¹ : ℝ) : ℂ)) *
                  Complex.exp (phiX Φ₀ x ((v : ℂ) + Complex.I / 2)) := by
                  rw [← h_epref]; ring
  refine ⟨C₃, C₄, Φ₀, x, n, M, M', A, hx, hn, hΦ,
    ⟨hA_an, hA_ne, hlogderiv_bd, hlogderiv2_bd, h_edge_int, h_lower_int,
      h_vert_R, h_vert_L, h_ref⟩⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.lemma_SD_V_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.lemma_SD_V_prime

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.twoSaddleAmplitude_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.twoSaddleAmplitude_nonvacuous

end FormalResearch.ModularBootstrap.Upper.Saddle
