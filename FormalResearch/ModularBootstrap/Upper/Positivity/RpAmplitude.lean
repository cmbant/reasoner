module

public import FormalResearch.ModularBootstrap.Upper.Positivity.AmplitudeLevel
public import FormalResearch.ModularBootstrap.Upper.Ramped.NearTipRatio
public import FormalResearch.ModularBootstrap.Upper.Saddle.FWSD

/-!
# The order-`p` amplitude factor `R_p` and the product `ρ_∞ R_p` (calculus)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, §`fw:s1`: the factor
`R_p(x) = (|b_x| / x)^{w-1}` of the order-`p` saddle amplitude (`fw:e1.5`) and the two limits `fw:e1.8`
of the product `ρ_∞ R_p`, where `ρ_∞(x) = vρ_∞(x; 3/4)` is the analytic ratio of `comb_estimates.tex`, Lemma K8.

* `rAmp p x = (√(v₀(x)² + 1/4) / x)^p` and `rhoRp p x = vρ_∞(x; 3/4) · R_p(x)`, with the saddle `v₀ = vZeroK8`
  of `Upper.Holes.K8` (equal to `edgeV`, `edgeV_eq_vZeroK8`).
* `fwsdRatio_eq_rAmp`: `rAmp` is the ratio `fwsdRatio` of `Upper.Saddle.FWSD`, i.e. `(‖b_x‖/x)^p`.
* `rAmp_le`: `R_p ≤ (1 + 1/(2ξ_*))^p` on `x > ξ_*` (`C_p` of `fw:FWM`).
* `rhoRp_le_explicit`: `ρ_∞ R_p ≤ 0.542 (1 + 1/(2ξ_*))^p` on `x > ξ_*`.
* `rhoRp_near_tip`: `ρ_∞ R_p ≤ C (x - ξ_*)^{5/4}` on `ξ_* < x ≤ ξ_* + 1` (first limit of `fw:e1.8`,
  from `nearTip_ratio`, the lemma behind `nearTip_amp_le`).
* `tendsto_rhoRp_atTop`: `ρ_∞ R_p → 1/2` at infinity (second limit of `fw:e1.8`).
* `rhoRp_neff_le`: `vρ_∞(x; n_eff) R_p ≤ ρ_∞ R_p` for `n_eff ≥ 3/4` (Lemma K8, used in `fw:e1.6`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Ramped

/-! ### 1. Definitions -/

/-- The amplitude factor `R_p(x) = (√(v₀² + 1/4) / x)^p = (|b_x| / x)^p` (`fw:e1.5`). -/
noncomputable def rAmp (p : ℕ) (x : ℝ) : ℝ :=
  (√(vZeroK8 x ^ 2 + 1 / 4) / x) ^ p

/-- The product `ρ_∞(x) R_p(x)` with `ρ_∞ = vρ_∞(·; 3/4)` (`fw:e1.7`, `fw:e1.8`). -/
noncomputable def rhoRp (p : ℕ) (x : ℝ) : ℝ :=
  vRhoInfty x (3 / 4) * rAmp p x

/-- The constant `1 + 1/(2ξ_*)` bounding `√(v₀² + 1/4)/x` on `x > ξ_*`. -/
noncomputable def rAmpConst : ℝ := 1 + 1 / (2 * xiStar)

theorem fwsdRatio_eq_rAmp (p : ℕ) {x : ℝ} (hx : xiStar < x) : fwsdRatio p x = rAmp p x := by
  unfold fwsdRatio rAmp
  rw [norm_bX, edgeV_eq_vZeroK8 hx]

lemma rAmp_zero (x : ℝ) : rAmp 0 x = 1 := pow_zero _

lemma rAmp_nonneg (p : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ rAmp p x :=
  pow_nonneg (div_nonneg (Real.sqrt_nonneg _) hx) p

lemma rAmp_pos (p : ℕ) {x : ℝ} (hx : 0 < x) : 0 < rAmp p x :=
  pow_pos (div_pos (Real.sqrt_pos.mpr (by positivity)) hx) p

lemma rAmpConst_pos : 0 < rAmpConst := by
  have := xiStar_pos
  unfold rAmpConst; positivity

/-! ### 2. Bounds -/

lemma sqrt_div_le_rAmpConst {x : ℝ} (hx : xiStar < x) :
    √(vZeroK8 x ^ 2 + 1 / 4) / x ≤ rAmpConst := by
  have hξ := xiStar_pos
  have hx0 : 0 < x := hξ.trans hx
  obtain ⟨hv0, hvx⟩ := vZeroK8_bounds hx
  have hsqrt : √(vZeroK8 x ^ 2 + 1 / 4) ≤ x + 1 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hxK : x + 1 / 2 ≤ rAmpConst * x := by
    unfold rAmpConst
    have : 1 / (2 * xiStar) * x ≥ 1 / 2 := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  rw [div_le_iff₀ hx0]
  exact hsqrt.trans hxK

/-- `R_p ≤ (1 + 1/(2ξ_*))^p` for `x > ξ_*`. -/
theorem rAmp_le (p : ℕ) {x : ℝ} (hx : xiStar < x) : rAmp p x ≤ rAmpConst ^ p :=
  pow_le_pow_left₀ (div_nonneg (Real.sqrt_nonneg _) (xiStar_pos.trans hx).le)
    (sqrt_div_le_rAmpConst hx) p

lemma vRhoInfty_nonneg (n : ℝ) {x : ℝ} (hx : xiStar < x) : 0 ≤ vRhoInfty x n := by
  have hξ := xiStar_pos
  have hpi := Real.pi_pos
  have hx0 : 0 < x := hξ.trans hx
  have hT : 0 < tanhTipK8 x := by
    unfold tanhTipK8
    exact mul_pos (tanh_pos_of_pos (div_pos (mul_pos hpi (sub_pos.mpr hx)) two_pos))
      (tanh_pos_of_pos (div_pos (mul_pos hpi (by linarith)) two_pos))
  have hs : 0 < Real.sinh (π * x / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hc : 0 < Real.cosh (π * x / 2) := Real.cosh_pos _
  unfold vRhoInfty
  have h1 : 0 ≤ (√(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hx0.le (Real.sqrt_nonneg _))) _
  have h2 : 0 ≤ tanhTipK8 x ^ (2 * n) := Real.rpow_nonneg hT.le _
  positivity

theorem rhoRp_nonneg (p : ℕ) {x : ℝ} (hx : xiStar < x) : 0 ≤ rhoRp p x :=
  mul_nonneg (vRhoInfty_nonneg _ hx) (rAmp_nonneg p (xiStar_pos.trans hx).le)

/-- Explicit bound `ρ_∞ R_p ≤ 0.542 (1 + 1/(2ξ_*))^p`, from Lemma K8 and `rAmp_le`. -/
theorem rhoRp_le_explicit (p : ℕ) {x : ℝ} (hx : xiStar < x) :
    rhoRp p x ≤ 542 / 1000 * rAmpConst ^ p := by
  obtain ⟨_, h2, h3, _⟩ := vRhoInfty_le (le_refl (3 / 4 : ℝ)) hx
  unfold rhoRp
  exact mul_le_mul (h2.trans h3.le) (rAmp_le p hx) (rAmp_nonneg p (xiStar_pos.trans hx).le)
    (by norm_num)

/-- `vρ_∞(x; n_eff) R_p ≤ ρ_∞ R_p` for `n_eff ≥ 3/4`, `x > ξ_*` (Lemma K8, used in `fw:e1.6`). -/
theorem rhoRp_neff_le (p : ℕ) {n x : ℝ} (hn : 3 / 4 ≤ n) (hx : xiStar < x) :
    vRhoInfty x n * rAmp p x ≤ rhoRp p x :=
  mul_le_mul_of_nonneg_right (vRhoInfty_le hn hx).1 (rAmp_nonneg p (xiStar_pos.trans hx).le)

/-- First limit of `fw:e1.8`: `ρ_∞ R_p ≤ C (x - ξ_*)^{5/4}` on `ξ_* < x ≤ ξ_* + 1`. -/
theorem rhoRp_near_tip (p : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, xiStar < x → x ≤ xiStar + 1 →
    rhoRp p x ≤ C * (x - xiStar) ^ (5 / 4 : ℝ) := by
  obtain ⟨Cv, hCv, h⟩ := nearTip_ratio
  have hK := rAmpConst_pos
  refine ⟨Cv * rAmpConst ^ p, by positivity, fun x hx hx1 => ?_⟩
  have h1 := h (x - xiStar) (by linarith) (by linarith)
  rw [show xiStar + (x - xiStar) = x by ring] at h1
  have h2 : rhoRp p x ≤ Cv * (x - xiStar) ^ (5 / 4 : ℝ) * rAmpConst ^ p :=
    mul_le_mul h1 (rAmp_le p hx) (rAmp_nonneg p (xiStar_pos.trans hx).le)
      (by have : 0 < x - xiStar := by linarith
          positivity)
  calc rhoRp p x ≤ _ := h2
    _ = Cv * rAmpConst ^ p * (x - xiStar) ^ (5 / 4 : ℝ) := by ring

/-! ### 3. The limit at infinity -/

lemma tendsto_lin_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

lemma tanh_eq_exp (u : ℝ) :
    Real.tanh u = (1 - Real.exp (-(2 * u))) / (1 + Real.exp (-(2 * u))) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hab : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have h2 : Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2]
  have ha := Real.exp_pos u
  have hb := Real.exp_pos (-u)
  rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0), div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (2 * Real.exp (-u)) * hab

lemma tendsto_tanh_atTop' : Tendsto Real.tanh atTop (𝓝 1) := by
  have h : Tendsto (fun u : ℝ => Real.exp (-(2 * u))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add h) (by norm_num)
  have h3 := h2.congr (fun u => (tanh_eq_exp u).symm)
  simpa using h3

lemma tendsto_tanh_lin {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => Real.tanh (a * x + b)) atTop (𝓝 1) :=
  tendsto_tanh_atTop'.comp (tendsto_lin_atTop ha b)

lemma tendsto_coth : Tendsto (fun x : ℝ => Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) atTop (𝓝 1) := by
  have h := tendsto_tanh_lin (a := π / 2) (by positivity) 0
  have h' := (tendsto_const_nhds (x := (1 : ℝ))).div h one_ne_zero
  have h'' := h'.congr (f₂ := fun x : ℝ => Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) (fun x => by
    simp only [Pi.div_apply]
    rw [show π / 2 * x + 0 = π * x / 2 by ring, Real.tanh_eq_sinh_div_cosh, one_div_div])
  simpa using h''

lemma tendsto_tanhTipK8 : Tendsto tanhTipK8 atTop (𝓝 1) := by
  have hpi := Real.pi_pos
  have h1 := tendsto_tanh_lin (a := π / 2) (by positivity) (-(π * xiStar / 2))
  have h2 := tendsto_tanh_lin (a := π / 2) (by positivity) (π * xiStar / 2)
  have h := h1.mul h2
  have h3 := h.congr (f₂ := tanhTipK8) (fun x => by
    unfold tanhTipK8
    rw [show π / 2 * x + -(π * xiStar / 2) = π * (x - xiStar) / 2 by ring,
      show π / 2 * x + π * xiStar / 2 = π * (x + xiStar) / 2 by ring])
  simpa using h3

lemma tendsto_edgeDerivK8 : Tendsto edgeDerivK8 atTop (𝓝 1) := by
  have hpi := Real.pi_pos
  have h0 : Tendsto (fun x : ℝ => 2 / Real.cosh (π * x) ^ 2) atTop (𝓝 0) := by
    have hb : Tendsto (fun x : ℝ => 2 / (π * x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hpi)
    refine squeeze_zero' ?_ ?_ hb
    · exact Eventually.of_forall fun x => by positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have h1 : π * x ≤ Real.cosh (π * x) :=
        (Real.self_le_sinh_iff.mpr (by positivity)).trans
          (by rw [Real.sinh_eq, Real.cosh_eq]; linarith [Real.exp_pos (-(π * x))])
      have h2 : 1 ≤ Real.cosh (π * x) := Real.one_le_cosh _
      have h3 : π * x ≤ Real.cosh (π * x) ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h3
  have h1 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h0).sqrt
  have h2 : Tendsto edgeDerivK8 atTop (𝓝 (√(1 - 0))) := h1
  simpa using h2

lemma vZeroK8_ge {x : ℝ} (hx : xiStar < x) (hx1 : 1 ≤ x) : x - 1 ≤ vZeroK8 x := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  obtain ⟨hv0, hvx⟩ := vZeroK8_bounds hx
  have hch : Real.cosh (π * vZeroK8 x) = Real.sinh (π * x) := by
    rw [← edgeV_eq_vZeroK8 hx]; exact cosh_pi_edgeV hx
  by_contra hlt
  push Not at hlt
  have hE := Real.exp_pos (π * x)
  have hexpπ : 4 ≤ Real.exp π := by linarith [Real.add_one_le_exp π]
  have hneg : Real.exp (-π) ≤ 1 / 4 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hexpπ
  have h1 : Real.exp (π * vZeroK8 x) < Real.exp (π * x) * Real.exp (-π) := by
    rw [← Real.exp_add]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have h2 : Real.cosh (π * vZeroK8 x) ≤ Real.exp (π * vZeroK8 x) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(π * vZeroK8 x)) ≤ Real.exp (π * vZeroK8 x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hpx : 4 ≤ Real.exp (π * x) := by
    have : 4 ≤ Real.exp π := hexpπ
    exact this.trans (Real.exp_le_exp.mpr (by nlinarith))
  have h3 : Real.exp (π * x) / 4 ≤ Real.sinh (π * x) := by
    rw [Real.sinh_eq]
    have : Real.exp (-(π * x)) ≤ 1 := by
      rw [Real.exp_neg]; exact inv_le_one_of_one_le₀ (by linarith)
    linarith
  have h4 : Real.exp (π * x) * Real.exp (-π) ≤ Real.exp (π * x) / 4 := by
    nlinarith
  linarith

lemma tendsto_sqrt_div :
    Tendsto (fun x : ℝ => √(vZeroK8 x ^ 2 + 1 / 4) / x) atTop (𝓝 1) := by
  have hlo : Tendsto (fun x : ℝ => 1 - 1 / x) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_id)
  have hhi : Tendsto (fun x : ℝ => 1 + 1 / (2 * x)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_gt_atTop (max 1 xiStar)] with x hx
    have hx1 : 1 < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hxξ : xiStar < x := lt_of_le_of_lt (le_max_right _ _) hx
    have hx0 : 0 < x := by linarith
    have h1 := vZeroK8_ge hxξ hx1.le
    have h2 : x - 1 ≤ √(vZeroK8 x ^ 2 + 1 / 4) :=
      h1.trans (Real.le_sqrt_of_sq_le (by nlinarith))
    rw [le_div_iff₀ hx0, sub_mul, one_mul, one_div, inv_mul_cancel₀ hx0.ne']
    linarith
  · filter_upwards [eventually_gt_atTop (max 1 xiStar)] with x hx
    have hxξ : xiStar < x := lt_of_le_of_lt (le_max_right _ _) hx
    have hx0 : 0 < x := (xiStar_pos).trans hxξ
    obtain ⟨hv0, hvx⟩ := vZeroK8_bounds hxξ
    have hsqrt : √(vZeroK8 x ^ 2 + 1 / 4) ≤ x + 1 / 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    rw [div_le_iff₀ hx0]
    have : (1 + 1 / (2 * x)) * x = x + 1 / 2 := by field_simp
    linarith

lemma tendsto_vRhoInfty_atTop : Tendsto (fun x : ℝ => vRhoInfty x (3 / 4)) atTop (𝓝 (1 / 2)) := by
  have hA : Tendsto (fun x : ℝ => (√(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x)) ^ (1 / 2 : ℝ))
      atTop (𝓝 1) := by
    have h := (tendsto_sqrt_div.div tendsto_edgeDerivK8 one_ne_zero).rpow_const
      (p := (1 / 2 : ℝ)) (Or.inl (by norm_num))
    have h2 := h.congr (f₂ := fun x : ℝ => (√(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x)) ^ (1 / 2 : ℝ))
      (fun x => by simp only [Pi.div_apply]; rw [div_div])
    simpa using h2
  have hT := tendsto_tanhTipK8.rpow_const (p := 2 * (3 / 4 : ℝ)) (Or.inl (by norm_num))
  have h := (((tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hA).mul tendsto_coth).mul hT
  unfold vRhoInfty
  simpa using h

/-- Second limit of `fw:e1.8`: `ρ_∞ R_p → 1/2` at infinity. -/
theorem tendsto_rhoRp_atTop (p : ℕ) : Tendsto (rhoRp p) atTop (𝓝 (1 / 2)) := by
  have h := tendsto_vRhoInfty_atTop.mul (tendsto_sqrt_div.pow p)
  unfold rhoRp rAmp
  simpa using h

/-- `R_p → 1` at infinity. -/
theorem tendsto_rAmp_atTop (p : ℕ) : Tendsto (rAmp p) atTop (𝓝 1) := by
  have h := tendsto_sqrt_div.pow p
  unfold rAmp
  simpa using h

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.rhoRp_near_tip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rhoRp_near_tip

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.tendsto_rhoRp_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_rhoRp_atTop

end FormalResearch.ModularBootstrap.Upper.Positivity
