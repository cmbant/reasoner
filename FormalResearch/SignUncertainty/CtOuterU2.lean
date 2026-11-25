module

public import FormalResearch.SignUncertainty.CtOuterGen

/-!
# Smoothness and growth of `u_r` and its first two derivatives

Support for the cubic coefficient of `ct:outer` (2).  **Proved.**  `u_r` is `C^∞` on `ℝ` (local holomorphic
extensions), even, and its first and second derivatives grow at most polynomially.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

lemma contDiffAt_uR (y₀ : ℝ) : ContDiffAt ℝ ⊤ uR y₀ := by
  obtain ⟨r, hr, v, hv, hvu⟩ := exists_holo_uR y₀
  have han : AnalyticAt ℂ v (y₀ : ℂ) := (hv.analyticOnNhd isOpen_ball) _ (mem_ball_self hr)
  have h2 : ContDiffAt ℝ ⊤ v (y₀ : ℂ) := han.contDiffAt.restrict_scalars ℝ
  have h3 : ContDiffAt ℝ ⊤ (fun t : ℝ => v (t : ℂ)) y₀ :=
    ContDiffAt.comp y₀ (by simpa using h2) Complex.ofRealCLM.contDiff.contDiffAt
  have h4 : ContDiffAt ℝ ⊤ (fun t : ℝ => (v (t : ℂ)).re) y₀ :=
    ContDiffAt.comp y₀ Complex.reCLM.contDiff.contDiffAt h3
  refine h4.congr_of_eventuallyEq ?_
  have : ∀ᶠ t in 𝓝 y₀, |t - y₀| < r := by
    filter_upwards [Metric.ball_mem_nhds y₀ hr] with t ht using by simpa [Real.dist_eq] using ht
  filter_upwards [this] with t ht
  simp [hvu t ht]

theorem contDiff_uR : ContDiff ℝ ⊤ uR := contDiff_iff_contDiffAt.2 contDiffAt_uR

/-- First derivative of `u_r`. -/
noncomputable def uR1 : ℝ → ℝ := deriv uR
/-- Second derivative of `u_r`. -/
noncomputable def uR2 : ℝ → ℝ := deriv uR1

lemma hasDerivAt_uR (t : ℝ) : HasDerivAt uR (uR1 t) t :=
  ((contDiff_uR.differentiable (by simp)) t).hasDerivAt

lemma contDiff_uR_inf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) uR := contDiff_uR.of_le (by exact_mod_cast le_top)

lemma contDiff_uR1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) uR1 := by
  have := contDiff_uR_inf.iterate_deriv 1
  simpa [uR1] using this

lemma contDiff_uR2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) uR2 := by
  have := contDiff_uR_inf.iterate_deriv 2
  simpa [uR2, uR1] using this

lemma hasDerivAt_uR1 (t : ℝ) : HasDerivAt uR1 (uR2 t) t :=
  ((contDiff_uR1.differentiable (by simp)) t).hasDerivAt

lemma hasDerivAt_uR2 (t : ℝ) : HasDerivAt uR2 (deriv uR2 t) t :=
  ((contDiff_uR2.differentiable (by simp)) t).hasDerivAt

lemma continuous_uR1 : Continuous uR1 := contDiff_uR1.continuous
lemma continuous_uR2 : Continuous uR2 := contDiff_uR2.continuous

lemma uR1_neg (t : ℝ) : uR1 (-t) = -uR1 t := by
  have h := deriv_comp_neg (f := uR) t
  have e : (fun x : ℝ => uR (-x)) = uR := funext uR_neg
  rw [e] at h
  unfold uR1
  linarith only [h]

lemma uR2_neg (t : ℝ) : uR2 (-t) = uR2 t := by
  have h := deriv_comp_neg (f := uR1) t
  have e : (fun x : ℝ => uR1 (-x)) = fun x => -uR1 x := funext uR1_neg
  rw [e, deriv.fun_neg] at h
  unfold uR2
  linarith only [h]


/-! ### Growth: `ExpBdd` from polynomial bounds at infinity -/

lemma expBdd_of_poly {v : ℝ → ℝ} (hc : Continuous v) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc0 : 0 ≤ c)
    (h : ∀ t : ℝ, 1 ≤ |t| → |v t| ≤ a + b * |t| + c * t ^ 2) : ExpBdd v := by
  obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B0 (a + b + 2 * c), fun t => ?_⟩
  have hE : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  rcases le_or_gt 1 |t| with h1 | h1
  · have hq := Real.quadratic_le_exp_of_nonneg (abs_nonneg t)
    have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    have h2 := h t h1
    have h3 : a + b * |t| + c * t ^ 2 ≤ (a + b + 2 * c) * Real.exp |t| := by
      rw [hsq]
      have hx := abs_nonneg t
      nlinarith only [hq, mul_nonneg ha hx, mul_nonneg hb hx, mul_nonneg hc0 hx, mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ a + b + 2 * c), hE, ha, hb, hc0, h1]
    have h4 : (a + b + 2 * c) * Real.exp |t| ≤ max B0 (a + b + 2 * c) * Real.exp |t| :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    linarith only [h2, h3, h4]
  · have hmem : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(abs_lt.mp h1).1], by linarith [(abs_lt.mp h1).2]⟩
    have h2 := hB0 t hmem
    rw [Real.norm_eq_abs] at h2
    have h4 : B0 * 1 ≤ max B0 (a + b + 2 * c) * Real.exp |t| := by
      have hB : 0 ≤ B0 := (abs_nonneg _).trans (hB0 0 ⟨by norm_num, by norm_num⟩ |> fun h => by simpa using h)
      exact mul_le_mul (le_max_left _ _) hE (by norm_num) ((hB.trans (le_max_left _ _)))
    linarith only [h2, h4]


/-! ### Explicit derivative formulas on `t > 0` -/

/-- `m''(t) = -1/t² + π² cosh(πt)/sinh²(πt)`. -/
noncomputable def mP1 (t : ℝ) : ℝ := -1 / t ^ 2 + π ^ 2 * Real.cosh (π * t) / Real.sinh (π * t) ^ 2
/-- `m'''(t)`. -/
noncomputable def mP2 (t : ℝ) : ℝ :=
  2 / t ^ 3 - π ^ 3 * (1 + Real.cosh (π * t) ^ 2) / Real.sinh (π * t) ^ 3

lemma hasDerivAt_sinh_pi (t : ℝ) : HasDerivAt (fun s : ℝ => Real.sinh (π * s)) (Real.cosh (π * t) * π) t :=
  ((Real.hasDerivAt_sinh (π * t)).comp t ((hasDerivAt_id t).const_mul π)).congr_deriv (by simp)

lemma hasDerivAt_cosh_pi (t : ℝ) : HasDerivAt (fun s : ℝ => Real.cosh (π * s)) (Real.sinh (π * t) * π) t :=
  ((Real.hasDerivAt_cosh (π * t)).comp t ((hasDerivAt_id t).const_mul π)).congr_deriv (by simp)

lemma hasDerivAt_mPrime {t : ℝ} (ht : 0 < t) : HasDerivAt mPrime (mP1 t) t := by
  have hs : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have h1 : HasDerivAt (fun s : ℝ => 1 / s) (-1 / t ^ 2) t := by
    have := hasDerivAt_inv ht.ne'
    simp only [one_div]
    exact this.congr_deriv (by field_simp)
  have h3 := (hasDerivAt_const t π).div (hasDerivAt_sinh_pi t) hs.ne'
  have h4 := h1.sub h3
  refine h4.congr_deriv ?_
  unfold mP1
  field_simp
  ring

lemma hasDerivAt_mP1 {t : ℝ} (ht : 0 < t) : HasDerivAt mP1 (mP2 t) t := by
  have hs : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have h1 : HasDerivAt (fun s : ℝ => -1 / s ^ 2) (2 / t ^ 3) t :=
    ((hasDerivAt_const t (-1 : ℝ)).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht.ne')).congr_deriv
      (by field_simp; ring)
  have h3 := ((hasDerivAt_cosh_pi t).const_mul (π ^ 2)).div
    ((hasDerivAt_sinh_pi t).pow 2) (pow_ne_zero 2 hs.ne')
  have h4 := h1.add h3
  refine h4.congr_deriv ?_
  unfold mP2
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  have hc : Real.cosh (π * t) ^ 2 = 1 + Real.sinh (π * t) ^ 2 := by rw [Real.cosh_sq]; ring
  rw [show (1 + Real.cosh (π * t) ^ 2) = 2 + Real.sinh (π * t) ^ 2 by rw [hc]; ring]
  field_simp
  rw [Real.cosh_sq]
  ring


/-- `u_r'(t)` for `t > 0` in terms of `m'`, `m''`. -/
noncomputable def w1 (t : ℝ) : ℝ := (1 / 2) * (mP1 t / mPrime t - 1 / t - 2 * t / (1 + t ^ 2))
/-- `u_r''(t)` for `t > 0`. -/
noncomputable def w2 (t : ℝ) : ℝ :=
  (1 / 2) * (mP2 t / mPrime t - (mP1 t / mPrime t) ^ 2 + 1 / t ^ 2 - 2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2)

lemma mPrime_pos {t : ℝ} (ht : 0 < t) : 0 < mPrime t :=
  lt_of_lt_of_le (by positivity) (mPrime_bounds ht).1

lemma uR_eq_log {t : ℝ} (ht : 0 < t) :
    uR t = (1 / 2) * (Real.log (6 / π ^ 2) + Real.log (mPrime t) - Real.log t - Real.log (1 + t ^ 2)) := by
  have hN := mPrime_pos ht
  have hpi := Real.pi_pos
  rw [uR_eq ht.ne']
  unfold Freal
  have h1 : 0 < 1 + t ^ 2 := by positivity
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hN.ne',
    Real.log_mul ht.ne' h1.ne']
  ring

lemma uR1_eq {t : ℝ} (ht : 0 < t) : uR1 t = w1 t := by
  have hN := mPrime_pos ht
  have hd : HasDerivAt (fun s : ℝ => (1 / 2) * (Real.log (6 / π ^ 2) + Real.log (mPrime s) - Real.log s -
      Real.log (1 + s ^ 2))) (w1 t) t := by
    have h1 := (hasDerivAt_mPrime ht).log hN.ne'
    have h2 := Real.hasDerivAt_log ht.ne'
    have h3 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).const_add 1)
    have h4 := h3.log (by positivity)
    have h5 := (((hasDerivAt_const t (Real.log (6 / π ^ 2))).add h1).sub h2).sub h4
    refine (h5.const_mul (1 / 2)).congr_deriv ?_
    unfold w1
    field_simp
    ring
  have hev : uR =ᶠ[𝓝 t] fun s : ℝ => (1 / 2) * (Real.log (6 / π ^ 2) + Real.log (mPrime s) - Real.log s -
      Real.log (1 + s ^ 2)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs using uR_eq_log hs
  exact ((hd.congr_of_eventuallyEq hev).unique (hasDerivAt_uR t)).symm

lemma uR2_eq {t : ℝ} (ht : 0 < t) : uR2 t = w2 t := by
  have hN := mPrime_pos ht
  have hd : HasDerivAt w1 (w2 t) t := by
    have h1 := (hasDerivAt_mP1 ht).div (hasDerivAt_mPrime ht) hN.ne'
    have h2 : HasDerivAt (fun s : ℝ => 1 / s) (-1 / t ^ 2) t := by
      have := hasDerivAt_inv ht.ne'
      simp only [one_div]
      exact this.congr_deriv (by field_simp)
    have h3 : HasDerivAt (fun s : ℝ => 2 * s / (1 + s ^ 2)) (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2) t := by
      have h4 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
        simpa using ((hasDerivAt_pow 2 t).const_add 1)
      exact (((hasDerivAt_id t).const_mul 2).div h4 (by positivity)).congr_deriv (by
        simp only [id]; field_simp; ring)
    refine (((h1.sub h2).sub h3).const_mul (1 / 2)).congr_deriv ?_
    unfold w2
    field_simp
    ring
  have hev : uR1 =ᶠ[𝓝 t] w1 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs using uR1_eq hs
  exact ((hd.congr_of_eventuallyEq hev).unique (hasDerivAt_uR1 t)).symm


/-! ### Polynomial bounds at infinity -/

lemma mP1_abs_le {t : ℝ} (ht : 0 < t) : |mP1 t| ≤ π ^ 2 / 3 := by
  have h := FormalResearch.CohnElkies.edgePhiDeriv3_abs_le ht.ne'
  have e : mP1 t = -FormalResearch.CohnElkies.edgePhiDeriv3 t := by
    unfold mP1 FormalResearch.CohnElkies.edgePhiDeriv3
    have hpi := Real.pi_pos
    field_simp
    ring
  rw [e, abs_neg]; exact h

lemma mP2_abs_le {t : ℝ} (ht : 1 ≤ t) : |mP2 t| ≤ 2 + 3 * π ^ 3 := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have ht0 : 0 < t := by linarith
  have hs1 : 1 ≤ Real.sinh (π * t) := by
    have := Real.self_le_sinh_iff.mpr (by positivity : 0 ≤ π * t)
    nlinarith only [this, ht, hpi3]
  set S := Real.sinh (π * t) with hS
  have hc : Real.cosh (π * t) ^ 2 = 1 + S ^ 2 := by rw [Real.cosh_sq]; ring
  have hSpos : 0 < S := by linarith
  have h1 : 2 / t ^ 3 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ t ^ 3 := one_le_pow₀ ht
    linarith only [this]
  have h2 : (1 + Real.cosh (π * t) ^ 2) / S ^ 3 ≤ 3 := by
    rw [hc, div_le_iff₀ (by positivity)]
    have h3 : S ^ 2 ≤ S ^ 3 := by nlinarith only [hs1, sq_nonneg S, hSpos]
    have h4 : 1 ≤ S ^ 3 := one_le_pow₀ hs1
    linarith only [h3, h4]
  have h5 : 0 ≤ (1 + Real.cosh (π * t) ^ 2) / S ^ 3 := by positivity
  unfold mP2
  rw [← hS, mul_div_assoc]
  rw [abs_le]
  have hpp : 0 < π ^ 3 := by positivity
  have h6 := mul_le_mul_of_nonneg_left h2 hpp.le
  have h7 := mul_nonneg hpp.le h5
  have h8 : 0 < 2 / t ^ 3 := by positivity
  constructor <;> nlinarith only [h1, h6, h7, h8]

lemma inv_mPrime_le {t : ℝ} (ht : 1 ≤ t) : 1 / mPrime t ≤ 2 * t := by
  have ht0 : 0 < t := by linarith
  have hb := (mPrime_bounds ht0).1
  have h1 : 1 / (2 * t) ≤ t / (1 + t ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [ht]
  have hN : 1 / (2 * t) ≤ mPrime t := h1.trans hb
  rw [div_le_iff₀ (mPrime_pos ht0)]
  have := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ 2 * t)
  have e : 2 * t * (1 / (2 * t)) = 1 := by field_simp
  linarith only [this, e]

lemma abs_w1_le {t : ℝ} (ht : 1 ≤ t) : |w1 t| ≤ π ^ 2 / 3 * t + 1 := by
  have ht0 : 0 < t := by linarith
  have hN := mPrime_pos ht0
  have hi := inv_mPrime_le ht
  have h1 := mP1_abs_le ht0
  have ha : |mP1 t / mPrime t| ≤ π ^ 2 / 3 * (2 * t) := by
    rw [abs_div, abs_of_pos hN, div_eq_mul_one_div]
    exact mul_le_mul h1 hi (by positivity) (by positivity)
  have h2 : |1 / t| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one ht0]; exact ht
  have h3 : |2 * t / (1 + t ^ 2)| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one (by positivity)]
    nlinarith only [sq_nonneg (t - 1)]
  unfold w1
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have := abs_sub (mP1 t / mPrime t - 1 / t) (2 * t / (1 + t ^ 2))
  have := abs_sub (mP1 t / mPrime t) (1 / t)
  nlinarith only [ha, h2, h3, this, abs_sub (mP1 t / mPrime t - 1 / t) (2 * t / (1 + t ^ 2)),
    abs_sub (mP1 t / mPrime t) (1 / t)]

lemma abs_w2_le {t : ℝ} (ht : 1 ≤ t) :
    |w2 t| ≤ 3 / 2 + (2 + 3 * π ^ 3) * t + 2 * π ^ 4 / 9 * t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hN := mPrime_pos ht0
  have hi := inv_mPrime_le ht
  have h1 := mP1_abs_le ht0
  have hpi := Real.pi_pos
  have ha : |mP1 t / mPrime t| ≤ π ^ 2 / 3 * (2 * t) := by
    rw [abs_div, abs_of_pos hN, div_eq_mul_one_div]
    exact mul_le_mul h1 hi (by positivity) (by positivity)
  have hb : |mP2 t / mPrime t| ≤ (2 + 3 * π ^ 3) * (2 * t) := by
    rw [abs_div, abs_of_pos hN, div_eq_mul_one_div]
    exact mul_le_mul (mP2_abs_le ht) hi (by positivity) (by positivity)
  have hc : |(mP1 t / mPrime t) ^ 2| ≤ (π ^ 2 / 3 * (2 * t)) ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have h2 : |1 / t ^ 2| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one (by positivity)]
    nlinarith only [ht]
  have h3 : |2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2| ≤ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 + t ^ 2) ^ 2),
      abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by positivity)]
    have : |1 - t ^ 2| ≤ 1 + t ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith only [sq_nonneg t]
    nlinarith only [this, sq_nonneg t]
  unfold w2
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have e : (π ^ 2 / 3 * (2 * t)) ^ 2 = 4 * π ^ 4 / 9 * t ^ 2 := by ring
  rw [e] at hc
  have t1 := abs_sub (mP2 t / mPrime t - (mP1 t / mPrime t) ^ 2 + 1 / t ^ 2) (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2)
  have t2 := abs_add_le (mP2 t / mPrime t - (mP1 t / mPrime t) ^ 2) (1 / t ^ 2)
  have t3 := abs_sub (mP2 t / mPrime t) ((mP1 t / mPrime t) ^ 2)
  nlinarith only [t1, t2, t3, ha, hb, hc, h2, h3]


lemma expBdd_uR1 : ExpBdd uR1 := by
  refine expBdd_of_poly continuous_uR1 (a := 1) (b := π ^ 2 / 3) (c := 0) (by norm_num) (by positivity)
    le_rfl fun t ht => ?_
  rcases le_total 0 t with h0 | h0
  · have h1 : 1 ≤ t := by rwa [abs_of_nonneg h0] at ht
    rw [uR1_eq (by linarith), abs_of_nonneg h0]
    have := abs_w1_le h1
    linarith only [this]
  · have h1 : 1 ≤ -t := by rwa [abs_of_nonpos h0] at ht
    have e : uR1 t = -uR1 (-t) := by rw [uR1_neg]; ring
    rw [e, abs_neg, uR1_eq (by linarith), abs_of_nonpos h0]
    have := abs_w1_le h1
    linarith only [this]

lemma expBdd_uR2 : ExpBdd uR2 := by
  refine expBdd_of_poly continuous_uR2 (a := 3 / 2) (b := 2 + 3 * π ^ 3) (c := 2 * π ^ 4 / 9)
    (by norm_num) (by positivity) (by positivity) fun t ht => ?_
  rcases le_total 0 t with h0 | h0
  · have h1 : 1 ≤ t := by rwa [abs_of_nonneg h0] at ht
    rw [uR2_eq (by linarith), abs_of_nonneg h0]
    exact abs_w2_le h1
  · have h1 : 1 ≤ -t := by rwa [abs_of_nonpos h0] at ht
    rw [← uR2_neg t, uR2_eq (by linarith), abs_of_nonpos h0]
    have := abs_w2_le h1
    nlinarith only [this]

/-! ### Quadratic behaviour at `0` (even `C^∞`) -/

/-- Mean-value bound: if `|f'| ≤ K` on `[-r, r]` then `|f x - f 0| ≤ K |x|` for `|x| ≤ r`. -/
lemma abs_sub_le_of_deriv {f g : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (g t) t) {r K x : ℝ}
    (hb : ∀ y ∈ Icc (-r) r, |g y| ≤ K) (hx : |x| ≤ r) : |f x - f 0| ≤ K * |x| := by
  have hr : 0 ≤ r := (abs_nonneg x).trans hx
  have hconv : Convex ℝ (Icc (-r) r) := convex_Icc _ _
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := g) (s := Icc (-r) r) (C := K)
    (fun y _ => (hd y).hasDerivWithinAt) (fun y hy => by rw [Real.norm_eq_abs]; exact hb y hy) hconv
    (x := 0) (y := x) ⟨by linarith, hr⟩ (abs_le.mp hx |> fun h => ⟨h.1, h.2⟩)
  simpa [Real.norm_eq_abs] using this

/-- If `f' = g`, `g' = h` with `h` continuous and `g 0 = 0`, then `|f x - f 0| ≤ C x²` for `|x| ≤ 1`. -/
lemma sq_bound_of_deriv2 {f g h : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (hh : Continuous h) (g0 : g 0 = 0) : ∃ C : ℝ, ∀ x : ℝ, |x| ≤ 1 → |f x - f 0| ≤ C * x ^ 2 := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hh.continuousOn
  have hg1 : ∀ s : ℝ, |s| ≤ 1 → |g s| ≤ B * |s| := by
    intro s hs
    have := abs_sub_le_of_deriv hg (r := 1) (K := B) (x := s) (fun y hy => by
      have := hB y hy; rwa [Real.norm_eq_abs] at this) hs
    simpa [g0] using this
  have hB0 : 0 ≤ B := by
    have := hB 0 ⟨by norm_num, by norm_num⟩
    rw [Real.norm_eq_abs] at this
    exact (abs_nonneg _).trans this
  refine ⟨B, fun x hx => ?_⟩
  have := abs_sub_le_of_deriv hf (r := |x|) (K := B * |x|) (x := x) (fun y hy => by
    have hy' : |y| ≤ |x| := abs_le.mpr ⟨by linarith [hy.1, neg_abs_le x], hy.2⟩
    calc |g y| ≤ B * |y| := hg1 y (hy'.trans hx)
      _ ≤ B * |x| := mul_le_mul_of_nonneg_left hy' hB0) le_rfl
  calc |f x - f 0| ≤ B * |x| * |x| := this
    _ = B * x ^ 2 := by rw [mul_assoc, ← sq, sq_abs]


lemma contDiff_deriv_uR2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv uR2) := by
  have := contDiff_uR2.iterate_deriv 1
  simpa using this

lemma contDiff_deriv_deriv_uR2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv uR2)) := by
  have := contDiff_uR2.iterate_deriv 2
  simpa using this

lemma deriv_uR2_neg (t : ℝ) : deriv uR2 (-t) = -deriv uR2 t := by
  have h := deriv_comp_neg (f := uR2) t
  have e : (fun x : ℝ => uR2 (-x)) = uR2 := funext uR2_neg
  rw [e] at h
  linarith only [h]

lemma deriv_uR2_zero : deriv uR2 0 = 0 := by
  have := deriv_uR2_neg 0
  simp only [neg_zero] at this
  linarith only [this]

/-- `u_r''(t) - u_r''(0) = O(t²)`. -/
lemma uR2_quad : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → |uR2 t - uR2 0| ≤ C * t ^ 2 :=
  sq_bound_of_deriv2 (f := uR2) (g := deriv uR2) (h := deriv (deriv uR2)) hasDerivAt_uR2
    (fun t => ((contDiff_deriv_uR2.differentiable (by simp)) t).hasDerivAt)
    contDiff_deriv_deriv_uR2.continuous deriv_uR2_zero


/-- **`ct:outer` (2): `H₀'''(0) = -∫_ℝ (u_r''(t) - u_r''(0)) π cosh(πt)/sinh²(πt) dt`.** -/
theorem deriv3_H0_zero_uR :
    deriv (deriv (deriv H0)) 0 = -∫ t : ℝ, (((uR2 t - uR2 0) * thetaK t : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := uR2_quad
  exact deriv3_H0_zero hasDerivAt_uR hasDerivAt_uR1 continuous_uR1 continuous_uR2 expBdd_uR1 expBdd_uR2
    ⟨C, fun t ht => hC t (by linarith [ht])⟩

/-- info: 'FormalResearch.SignUncertainty.CtOuter.contDiff_uR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_uR

/-- info: 'FormalResearch.SignUncertainty.CtOuter.expBdd_uR1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expBdd_uR1

/-- info: 'FormalResearch.SignUncertainty.CtOuter.expBdd_uR2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expBdd_uR2

/-- info: 'FormalResearch.SignUncertainty.CtOuter.uR2_quad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uR2_quad

/-- info: 'FormalResearch.SignUncertainty.CtOuter.deriv3_H0_zero_uR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deriv3_H0_zero_uR

end FormalResearch.SignUncertainty.CtOuter
