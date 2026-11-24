module

public import FormalResearch.SignUncertainty.HankelBandInstance

/-!
# Second-order expansion of the Langer chart and the lower expansion of `ξ(u)` (M5-S7)

* `norm_chartM_sub_chartK_sq`: `‖M(u) - K(u)‖ ≤ 1.3 ‖u‖²` (the linear bounds of `E - 1`, `G - 1` and
  `norm_one_add_cpow_sub_one_le`);
* `norm_chartY_add_sq`: `‖y(w) + w‖ ≤ 3 ‖w‖²` for `‖w‖ ≤ 10⁻³`;
* `norm_chartYinv_add_sq`: `‖y⁻¹(y) + y‖ ≤ 3.1 ‖y‖²` for `‖y‖ ≤ 4.94·10⁻⁴`;
* `hankelXi_lower`: `c ξ(x) ≥ c/π² - x c^{1/3}/β₁ - 13` for `|x| ≤ 3`, `c ≥ 3·10⁶` (`β₁ = π² κ`).
-/

@[expose] public section

open Complex Set Metric
open scoped Real

namespace FormalResearch.SignUncertainty

lemma norm_psW_aE_sub_one_lin (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖psW (aE η) u - 1‖ ≤ 0.8 * ‖u‖ := by
  have h1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have := norm_chartE_sub_one_le h h1
  unfold chartE at this
  refine this.trans ?_
  have hpi : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d4]
  have hu0 := norm_nonneg u
  have h2 : (1 - 0.035 ^ 2 : ℝ) ≤ 1 - ‖u‖ := by linarith
  have h3 : 36 / (5 * π ^ 2) ≤ 36 / (5 * 9.869) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  calc 36 / (5 * π ^ 2) * ‖u‖ / (1 - ‖u‖) ≤ 36 / (5 * 9.869) * ‖u‖ / (1 - 0.035 ^ 2) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by norm_num) h2
    _ = (36 / (5 * 9.869) / (1 - 0.035 ^ 2)) * ‖u‖ := by ring
    _ ≤ 0.8 * ‖u‖ := by
        have : (36 / (5 * 9.869) / (1 - 0.035 ^ 2) : ℝ) ≤ 0.8 := by norm_num
        gcongr

lemma norm_psW_aG_sub_one_lin (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖psW (aG η) u - 1‖ ≤ 0.7 * ‖u‖ := by
  have h1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have := norm_chartEps_le h h1
  unfold chartEps at this
  refine this.trans ?_
  have hpi : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d4]
  have hu0 := norm_nonneg u
  have h2 : (1 - 0.035 ^ 2 : ℝ) ≤ 1 - ‖u‖ := by linarith
  have h3 : 6 / π ^ 2 ≤ 6 / 9.869 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi.le
  calc 6 / π ^ 2 * ‖u‖ / (1 - ‖u‖) ≤ 6 / 9.869 * ‖u‖ / (1 - 0.035 ^ 2) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by norm_num) h2
    _ = (6 / 9.869 / (1 - 0.035 ^ 2)) * ‖u‖ := by ring
    _ ≤ 0.7 * ‖u‖ := by
        have : (6 / 9.869 / (1 - 0.035 ^ 2) : ℝ) ≤ 0.7 := by norm_num
        gcongr

lemma norm_chartM_sub_chartK_sq (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖chartM η u - chartK η u‖ ≤ 1.3 * ‖u‖ ^ 2 := by
  have h1 := norm_psW_aE_sub_one_lin h hu
  have h2 := norm_psW_aG_sub_one_lin h hu
  have hu0 := norm_nonneg u
  have ht : 0.8 * ‖u‖ < 1 := by nlinarith
  have hA := norm_one_add_cpow_sub_one_le (α := 2 / 3) (by norm_num) (by norm_num)
    (x := psW (aE η) u - 1) (t := 0.8 * ‖u‖) h1 ht
  have hF : (1 + (psW (aE η) u - 1)) = psW (aE η) u := by ring
  rw [hF] at hA
  have e : chartM η u - chartK η u =
      u * (psW (aE η) u ^ (((2 / 3 : ℝ)) : ℂ) - 1) - u * (psW (aG η) u - 1) := by
    unfold chartM powMapU chartK; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h3 : ‖u‖ * ‖psW (aE η) u ^ (((2 / 3 : ℝ)) : ℂ) - 1‖ ≤ ‖u‖ * (2 / 3 * (0.8 * ‖u‖) / (1 - 0.8 * ‖u‖)) :=
    mul_le_mul_of_nonneg_left hA hu0
  have h4 : ‖u‖ * ‖psW (aG η) u - 1‖ ≤ ‖u‖ * (0.7 * ‖u‖) := mul_le_mul_of_nonneg_left h2 hu0
  have h5 : 2 / 3 * (0.8 * ‖u‖) / (1 - 0.8 * ‖u‖) ≤ 0.6 * ‖u‖ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h6 : ‖u‖ * (2 / 3 * (0.8 * ‖u‖) / (1 - 0.8 * ‖u‖)) ≤ ‖u‖ * (0.6 * ‖u‖) :=
    mul_le_mul_of_nonneg_left h5 hu0
  nlinarith

lemma norm_chartXi_sub_sq (h : LangerEta η) {v : ℂ} (hv : v ∈ chartVdisc) :
    ‖chartXi η v - v‖ ≤ 1.4 * ‖v‖ ^ 2 := by
  obtain ⟨hu, hK⟩ := chartKinv_spec h hv
  have hun : ‖chartKinv η v‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu).le
  have h1 := norm_chartM_sub_chartK_sq h hun
  have h2 := norm_chartKinv_le h hv
  unfold chartXi
  have e : chartM η (chartKinv η v) - v = chartM η (chartKinv η v) - chartK η (chartKinv η v) := by
    rw [hK]
  rw [e]
  refine h1.trans ?_
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  have hu0 := norm_nonneg (chartKinv η v)
  have h3 : ‖chartKinv η v‖ ≤ 1.001 * ‖v‖ := by nlinarith
  have h4 : ‖chartKinv η v‖ ^ 2 ≤ (1.001 * ‖v‖) ^ 2 := pow_le_pow_left₀ hu0 h3 2
  nlinarith

theorem norm_chartY_add_sq (h : LangerEta η) {w : ℂ} (hw : ‖w‖ ≤ 1e-3) :
    ‖chartY η w + w‖ ≤ 3 * ‖w‖ ^ 2 := by
  have hv := chartVofW_mem hw
  have hX := norm_chartXi_sub_sq h hv
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hL := Complex.norm_log_one_add_sub_self_le hw1
  have hw0 := norm_nonneg w
  have hLw : ‖Complex.log (1 + w) - w‖ ≤ 0.51 * ‖w‖ ^ 2 := by
    refine hL.trans ?_
    have h2 : (1 - ‖w‖)⁻¹ ≤ (1 - 1e-3)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    calc ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ ^ 2 * (1 - 1e-3)⁻¹ / 2 := by gcongr
      _ ≤ 0.51 * ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]
  have hlog : ‖Complex.log (1 + w)‖ ≤ 1.0006 * ‖w‖ := by
    have := norm_sub_norm_le (Complex.log (1 + w)) w
    nlinarith
  have hpi : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d4]
  have hpi2 : π ^ 2 < 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  set v := chartVofW w with hvdef
  have hvn : ‖v‖ ≤ (12 / 9.869) * (1.0006 * ‖w‖) := by
    rw [hvdef]; unfold chartVofW
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_neg]
    have h3 : 12 / π ^ 2 ≤ 12 / 9.869 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi.le
    calc 12 / π ^ 2 * ‖Complex.log (1 + w)‖ ≤ 12 / 9.869 * ‖Complex.log (1 + w)‖ := by gcongr
      _ ≤ _ := by gcongr
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  have e : chartY η w + w = ((π ^ 2 / 12 : ℝ) : ℂ) * (chartXi η v - v) -
      (Complex.log (1 + w) - w) := by
    unfold chartY
    rw [← hvdef]
    have : ((π ^ 2 / 12 : ℝ) : ℂ) * v = -Complex.log (1 + w) := by
      rw [hvdef]; unfold chartVofW
      rw [← mul_assoc]
      have : ((π ^ 2 / 12 : ℝ) : ℂ) * ((12 / π ^ 2 : ℝ) : ℂ) = 1 := by
        have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
        rw [← Complex.ofReal_mul]; field_simp; simp
      rw [this, one_mul]
    linear_combination this
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h4 : (π ^ 2 / 12 : ℝ) * ‖chartXi η v - v‖ ≤ (π ^ 2 / 12 : ℝ) * (1.4 * ‖v‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have h5 : ‖v‖ ^ 2 ≤ ((12 / 9.869) * (1.0006 * ‖w‖)) ^ 2 := pow_le_pow_left₀ hv0 hvn 2
  have h6 : (π ^ 2 / 12 : ℝ) * (1.4 * ‖v‖ ^ 2) ≤ (π ^ 2 / 12 : ℝ) * (1.4 * ((12 / 9.869) * (1.0006 * ‖w‖)) ^ 2) := by
    gcongr
  have h7 : (π ^ 2 / 12 : ℝ) * (1.4 * ((12 / 9.869) * (1.0006 * ‖w‖)) ^ 2) ≤ 2.4 * ‖w‖ ^ 2 := by
    have : (π ^ 2 / 12 : ℝ) * (1.4 * ((12 / 9.869) * 1.0006) ^ 2) ≤ 2.4 := by
      have hp : π ^ 2 / 12 ≤ 9.87 / 12 := by linarith
      calc (π ^ 2 / 12 : ℝ) * (1.4 * ((12 / 9.869) * 1.0006) ^ 2) ≤ 9.87 / 12 * (1.4 * ((12 / 9.869) * 1.0006) ^ 2) := by gcongr
        _ ≤ 2.4 := by norm_num
    nlinarith [sq_nonneg ‖w‖]
  nlinarith

theorem norm_chartYinv_add_sq {y : ℂ} (hy : ‖y‖ ≤ 4.94e-4) :
    ‖chartYinv etaC y + y‖ ≤ 3.1 * ‖y‖ ^ 2 := by
  obtain ⟨hw, hwy⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hy)
  set w := chartYinv etaC y with hwdef
  have hwn : ‖w‖ ≤ 1e-3 := (mem_ball_zero_iff.1 hw).le
  have h1 := norm_chartY_add_sq langerEta_etaC hwn
  have h2 := norm_chartY_add_le langerEta_etaC hwn
  rw [hwy] at h1 h2
  have hw0 := norm_nonneg w
  have hy0 := norm_nonneg y
  have h3 : ‖w‖ ≤ ‖y‖ + ‖y + w‖ := by
    calc ‖w‖ = ‖-y + (y + w)‖ := by ring_nf
      _ ≤ ‖-y‖ + ‖y + w‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have h4 : ‖w‖ ≤ 1.003 * ‖y‖ := by nlinarith
  have h5 : ‖w‖ ^ 2 ≤ (1.003 * ‖y‖) ^ 2 := pow_le_pow_left₀ hw0 h4 2
  have e : w + y = y + w := by ring
  rw [e]
  nlinarith

set_option maxHeartbeats 800000 in
/-- `c ξ(x) ≥ c/π² - x c^{1/3}/β₁ - 13` for `|x| ≤ 3`, `c ≥ 3·10⁶`. -/
theorem hankelXi_lower {c : ℝ} (hc : 3e6 ≤ c) {x : ℝ} (hx : |x| ≤ 3) :
    c / π ^ 2 - x * c ^ (1 / 3 : ℝ) / hankelBeta1 - 13 ≤ c * hankelXi c x := by
  have hc0 : 0 < c := by linarith
  have hK := hankelBand_langerScale_ge hc
  have hK0 : 0 < langerScale c := by linarith
  have hx' : |x| ≤ langerScale c * 4.94e-4 := by nlinarith
  obtain ⟨hreal, _⟩ := chartYinv_real_point hc0 hx'
  set yr : ℝ := x / langerScale c with hyr
  set w : ℝ := (chartYinv etaC (yr : ℂ)).re with hw
  have hyn : ‖(yr : ℂ)‖ ≤ 4.94e-4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, hyr, abs_div, abs_of_pos hK0, div_le_iff₀ hK0]
    linarith
  have hq := norm_chartYinv_add_sq hyn
  rw [hreal, ← Complex.ofReal_add, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs] at hq
  have hq' := (abs_le.1 hq).1
  have hyabs : |yr| ≤ 3 / langerScale c := by
    rw [hyr, abs_div, abs_of_pos hK0]; gcongr
  have hy2 : yr ^ 2 ≤ 9 / langerScale c ^ 2 := by
    have h1 : |yr| ^ 2 ≤ (3 / langerScale c) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hyabs 2
    calc yr ^ 2 = |yr| ^ 2 := (sq_abs yr).symm
      _ ≤ (3 / langerScale c) ^ 2 := h1
      _ = 9 / langerScale c ^ 2 := by rw [div_pow]; norm_num
  have hxi : hankelXi c x = (1 + w) / π ^ 2 := rfl
  have hpi : 0 < π ^ 2 := by positivity
  have hβ : hankelBeta1 = langerKappa * π ^ 2 := hankelBeta1_eq_kappa
  have hk := hankelLangerKappa_bounds
  set k : ℝ := c ^ (1 / 3 : ℝ) with hkdef
  have hk0 : 0 < k := Real.rpow_pos_of_pos hc0 _
  have hk3 : k ^ 3 = c := by
    rw [hkdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hkm : c ^ (2 / 3 : ℝ) = k ^ 2 := by
    rw [hkdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hKdef : langerScale c = k ^ 2 * langerKappa := by
    show c ^ (2 / 3 : ℝ) * langerKappa = _
    rw [hkm]
  have hkp := langerKappa_pos
  have hw_ge : w ≥ -yr - 3.1 * yr ^ 2 := by
    have : 3.1 * |yr| ^ 2 = 3.1 * yr ^ 2 := by rw [sq_abs]
    linarith
  have hmain : c * hankelXi c x ≥ c / π ^ 2 * (1 - yr - 3.1 * yr ^ 2) := by
    rw [hxi]
    have : c * ((1 + w) / π ^ 2) = c / π ^ 2 * (1 + w) := by ring
    rw [this]
    have h0 : 0 ≤ c / π ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h0
  have e1 : c / π ^ 2 * yr = x * k / hankelBeta1 := by
    rw [hyr, hKdef, hβ, ← hk3]
    field_simp
  have e2 : c / π ^ 2 * (3.1 * yr ^ 2) ≤ 13 := by
    have h1 : c / π ^ 2 * (3.1 * yr ^ 2) ≤ c / π ^ 2 * (3.1 * (9 / langerScale c ^ 2)) := by gcongr
    refine h1.trans ?_
    have hk2 : 1 / 4 ≤ langerKappa ^ 2 := by nlinarith [hk.1]
    have hpi9 : (9 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three]
    have hc1 : (1 : ℝ) ≤ k := by
      rw [hkdef]; exact Real.one_le_rpow (by linarith) (by norm_num)
    have e : c / π ^ 2 * (3.1 * (9 / langerScale c ^ 2)) = 27.9 / (π ^ 2 * langerKappa ^ 2 * k) := by
      rw [hKdef, ← hk3]
      field_simp
      norm_num
    rw [e, div_le_iff₀ (by positivity)]
    have h5 : 9 * (1 / 4) ≤ π ^ 2 * langerKappa ^ 2 := by nlinarith
    nlinarith
  have e3 : c / π ^ 2 * (1 - yr - 3.1 * yr ^ 2) =
      c / π ^ 2 - c / π ^ 2 * yr - c / π ^ 2 * (3.1 * yr ^ 2) := by ring
  rw [e1] at e3
  linarith

/-- info: 'FormalResearch.SignUncertainty.norm_chartY_add_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_chartY_add_sq

/-- info: 'FormalResearch.SignUncertainty.norm_chartYinv_add_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_chartYinv_add_sq

/-- info: 'FormalResearch.SignUncertainty.hankelXi_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelXi_lower

end FormalResearch.SignUncertainty
