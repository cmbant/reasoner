module

public import FormalResearch.SignUncertainty.HankelChartSecond
public import FormalResearch.SignUncertainty.HankelWindow
public import FormalResearch.SignUncertainty.HbMultilevelDefs

/-!
# Generalized Langer-level chart, band reduction, and window lemma (`R2a`, `R2c`)

Extends the one-level chart inversion, band reduction (`hankelBandInstance`), and window bound
(`hankel_yv_window`) from `u_T ∈ [-3, 0]` to arbitrary `u_T ∈ [-U, 0]` (`3 ≤ U`) for sufficiently
large `c`, together with `hankelLevel_to_u` (`R2a`) and `hankel_psi_sign_of_point`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.StripBand FormalResearch.CohnElkies FormalResearch.Special
  FormalResearch.ModularBootstrap.ConcreteBootstrap

/-! ### 1. Langer chart two-sided expansion & `hankelLevel` inversion (`R2a`) -/

/-- Two-sided Langer chart expansion for arbitrary `|x| ≤ U` inside the Langer disc:
`|c ξ(x) - (c/π² - x c^{1/3}/β₁)| ≤ 3.1 U² / (π² κ² c^{1/3})`. -/
theorem hankelXi_approx {c U x : ℝ} (hc : 3e6 ≤ c) (_hU : 0 ≤ U) (hUr : U ≤ langerRadius c)
    (hx : |x| ≤ U) :
    |c * hankelXi c x - (c / π ^ 2 - x * c ^ (1 / 3 : ℝ) / hankelBeta1)| ≤
      3.1 * U ^ 2 / (π ^ 2 * langerKappa ^ 2 * c ^ (1 / 3 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hK := hankelBand_langerScale_ge hc
  have hK0 : 0 < langerScale c := by linarith
  have hx' : |x| ≤ langerScale c * 4.94e-4 := hx.trans hUr
  obtain ⟨hreal, _⟩ := chartYinv_real_point hc0 hx'
  set yr : ℝ := x / langerScale c with hyr
  set w : ℝ := (chartYinv etaC (yr : ℂ)).re with hw
  have hyn : ‖(yr : ℂ)‖ ≤ 4.94e-4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, hyr, abs_div, abs_of_pos hK0, div_le_iff₀ hK0]
    linarith
  have hq := norm_chartYinv_add_sq hyn
  rw [hreal, ← Complex.ofReal_add, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs] at hq
  have hyabs : |yr| ≤ U / langerScale c := by
    rw [hyr, abs_div, abs_of_pos hK0]; gcongr
  have hy2 : yr ^ 2 ≤ U ^ 2 / langerScale c ^ 2 := by
    have h1 : |yr| ^ 2 ≤ (U / langerScale c) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hyabs 2
    calc yr ^ 2 = |yr| ^ 2 := (sq_abs yr).symm
      _ ≤ (U / langerScale c) ^ 2 := h1
      _ = U ^ 2 / langerScale c ^ 2 := by rw [div_pow]
  have hxi : hankelXi c x = (1 + w) / π ^ 2 := rfl
  have hpi : 0 < π ^ 2 := by positivity
  have hβ : hankelBeta1 = langerKappa * π ^ 2 := hankelBeta1_eq_kappa
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
  have hw_abs : |w + yr| ≤ 3.1 * yr ^ 2 := by
    have : 3.1 * |yr| ^ 2 = 3.1 * yr ^ 2 := by rw [sq_abs]
    linarith
  have e1 : c / π ^ 2 * yr = x * k / hankelBeta1 := by
    rw [hyr, hKdef, hβ, ← hk3]; field_simp
  have hdiff : c * hankelXi c x - (c / π ^ 2 - x * k / hankelBeta1) = c / π ^ 2 * (w + yr) := by
    rw [hxi, ← e1]; ring
  rw [hdiff, abs_mul, abs_of_nonneg (by positivity : 0 ≤ c / π ^ 2)]
  calc c / π ^ 2 * |w + yr| ≤ c / π ^ 2 * (3.1 * yr ^ 2) :=
        mul_le_mul_of_nonneg_left hw_abs (by positivity)
    _ ≤ c / π ^ 2 * (3.1 * (U ^ 2 / langerScale c ^ 2)) := by gcongr
    _ = 3.1 * U ^ 2 / (π ^ 2 * langerKappa ^ 2 * k) := by
        rw [hKdef, ← hk3]; field_simp

/-- For any `U ≥ 0` and `δ > 0`, eventually `U ≤ langerRadius c` and the Langer chart error on
`|x| ≤ U` is at most `δ`. -/
lemma hankelXi_approx_eventually {U δ : ℝ} (hU : 0 ≤ U) (hδ : 0 < δ) :
    ∀ᶠ c : ℝ in atTop, U ≤ langerRadius c ∧
      ∀ x : ℝ, |x| ≤ U → |c * hankelXi c x - (c / π ^ 2 - x * c ^ (1 / 3 : ℝ) / hankelBeta1)| ≤ δ := by
  have hK := langerKappa_pos
  have hrad : Tendsto langerRadius atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).atTop_mul_const hK).atTop_mul_const
      (by norm_num : (0 : ℝ) < 4.94e-4)
  have herr : Tendsto (fun c : ℝ => 3.1 * U ^ 2 / (π ^ 2 * langerKappa ^ 2 * c ^ (1 / 3 : ℝ)))
      atTop (𝓝 0) := by
    have hc13 : Tendsto (fun c : ℝ => c ^ (1 / 3 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)
    have hden : Tendsto (fun c : ℝ => π ^ 2 * langerKappa ^ 2 * c ^ (1 / 3 : ℝ)) atTop atTop :=
      hc13.const_mul_atTop (by positivity)
    exact tendsto_const_nhds.div_atTop hden
  filter_upwards [eventually_ge_atTop (3e6 : ℝ), hrad.eventually_ge_atTop U,
    herr (Iic_mem_nhds hδ)] with c hc hUr hε
  exact ⟨hUr, fun x hx => (hankelXi_approx hc hU hUr hx).trans hε⟩

/-- **`R2a` site-to-chart inversion**: for a fixed site `t : ℝ` and offset bound `R_off ≥ 0`, for
sufficiently large `c`, every level `hankelLevel t c o` with `|o| ≤ R_off` is `c * hankelXi c u`
for some `u` satisfying `|u - t| ≤ (hankelBeta1 * (R_off + 1)) * c^{-1/3}` and `|u| ≤ |t| + hankelBeta1 * (R_off + 1)`. -/
theorem hankelLevel_to_u (t R_off : ℝ) (hR : 0 ≤ R_off) :
    ∃ c₀ : ℝ, 3e6 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ o : ℝ, |o| ≤ R_off →
      ∃ u : ℝ, |u - t| ≤ hankelBeta1 * (R_off + 1) * c ^ (-(1 / 3 : ℝ)) ∧
        |u| ≤ |t| + hankelBeta1 * (R_off + 1) ∧
        c * hankelXi c u = hankelLevel t c o := by
  let D1 : ℝ := hankelBeta1 * (R_off + 1)
  let U : ℝ := |t| + D1
  have hβ := hankelBeta1_pos
  have hD1 : 0 < D1 := mul_pos hβ (by linarith)
  have hU : 0 ≤ U := add_nonneg (abs_nonneg _) hD1.le
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.1
    ((hankelXi_approx_eventually hU (by norm_num : (0 : ℝ) < 1 / 4)).and (eventually_ge_atTop (3e6 : ℝ)))
  refine ⟨max c₁ 3e6, le_max_right _ _, fun c hc o ho => ?_⟩
  have hsp := hc₁ c ((le_max_left _ _).trans hc)
  have hUr : U ≤ langerRadius c := hsp.1.1
  have herr := hsp.1.2
  have hc3 : (3e6 : ℝ) ≤ c := hsp.2
  have hc0 : 0 < c := by linarith
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hk_pos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hkm_le : c ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hk_mul : c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hc0]; norm_num
  have hstep_nn : 0 ≤ D1 * c ^ (-(1 / 3 : ℝ)) := mul_nonneg hD1.le (Real.rpow_nonneg hc0.le _)
  let u_lo : ℝ := t - D1 * c ^ (-(1 / 3 : ℝ))
  let u_hi : ℝ := t + D1 * c ^ (-(1 / 3 : ℝ))
  have hstep_le : D1 * c ^ (-(1 / 3 : ℝ)) ≤ D1 := mul_le_of_le_one_right hD1.le hkm_le
  have hulo_abs : |u_lo| ≤ U := by
    calc |t - D1 * c ^ (-(1 / 3 : ℝ))| ≤ |t| + |D1 * c ^ (-(1 / 3 : ℝ))| := abs_sub _ _
      _ = |t| + D1 * c ^ (-(1 / 3 : ℝ)) := by rw [abs_of_nonneg hstep_nn]
      _ ≤ U := by linarith
  have huhi_abs : |u_hi| ≤ U := by
    calc |t + D1 * c ^ (-(1 / 3 : ℝ))| ≤ |t| + |D1 * c ^ (-(1 / 3 : ℝ))| := abs_add_le _ _
      _ = |t| + D1 * c ^ (-(1 / 3 : ℝ)) := by rw [abs_of_nonneg hstep_nn]
      _ ≤ U := by linarith
  have he_lo := (abs_le.1 (herr u_lo hulo_abs)).1
  have he_hi := (abs_le.1 (herr u_hi huhi_abs)).2
  have hlo_eval : hankelLevel t c o ≤ c * hankelXi c u_lo := by
    have hmul : u_lo * c ^ (1 / 3 : ℝ) / hankelBeta1 =
        t * c ^ (1 / 3 : ℝ) / hankelBeta1 - (R_off + 1) := by
      dsimp [u_lo, D1]; rw [sub_mul, sub_div]; congr 1
      calc hankelBeta1 * (R_off + 1) * c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) / hankelBeta1
          = (R_off + 1) * (c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ)) * (hankelBeta1 / hankelBeta1) := by ring
        _ = R_off + 1 := by rw [hk_mul, div_self hβ.ne', mul_one, mul_one]
    have h1 := he_lo
    rw [hmul] at h1
    have h2 : t * c ^ (1 / 3 : ℝ) / hankelBeta1 = (t / hankelBeta1) * c ^ (1 / 3 : ℝ) := by ring
    unfold hankelLevel
    linarith [(abs_le.1 ho).2]
  have hhi_eval : c * hankelXi c u_hi ≤ hankelLevel t c o := by
    have hmul : u_hi * c ^ (1 / 3 : ℝ) / hankelBeta1 =
        t * c ^ (1 / 3 : ℝ) / hankelBeta1 + (R_off + 1) := by
      dsimp [u_hi, D1]; rw [add_mul, add_div]; congr 1
      calc hankelBeta1 * (R_off + 1) * c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) / hankelBeta1
          = (R_off + 1) * (c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ)) * (hankelBeta1 / hankelBeta1) := by ring
        _ = R_off + 1 := by rw [hk_mul, div_self hβ.ne', mul_one, mul_one]
    have h1 := he_hi
    rw [hmul] at h1
    have h2 : t * c ^ (1 / 3 : ℝ) / hankelBeta1 = (t / hankelBeta1) * c ^ (1 / 3 : ℝ) := by ring
    unfold hankelLevel
    linarith [(abs_le.1 ho).1]
  have hcont : ContinuousOn (fun x : ℝ => c * hankelXi c x) (Icc u_lo u_hi) := by
    intro x hx
    have hxA : |x| ≤ langerRadius c :=
      (abs_le.2 ⟨by linarith [(abs_le.1 hulo_abs).1, hx.1],
        by linarith [(abs_le.1 huhi_abs).2, hx.2]⟩).trans hUr
    exact ((hasDerivAt_hankelXi hc0 hxA).const_mul c).continuousAt.continuousWithinAt
  have h_le_lohi : u_lo ≤ u_hi := by dsimp [u_lo, u_hi]; linarith
  obtain ⟨u, hu_mem, hu_eq⟩ := intermediate_value_Icc' h_le_lohi hcont ⟨hhi_eval, hlo_eval⟩
  refine ⟨u, abs_le.2 ⟨by dsimp [u_lo] at hu_mem; linarith [hu_mem.1],
    by dsimp [u_hi] at hu_mem; linarith [hu_mem.2]⟩, ?_, hu_eq⟩
  exact abs_le.2 ⟨by linarith [(abs_le.1 hulo_abs).1, hu_mem.1],
    by linarith [(abs_le.1 huhi_abs).2, hu_mem.2]⟩

/-- Single-point Hankel sign: `0 ≤ f (c ξ(x))` gives `-r_∞ ≤ Re Ψ̃(x)` without tail positivity at `x`. -/
theorem hankel_psi_sign_of_point {c ε : ℝ} (hc : 5000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {x : ℝ} (hx : |x| ≤ langerRadius c)
    (hfx : 0 ≤ f (c * hankelXi c x)) : -hankelRinf c ≤ hankelPsiR c f x := by
  have hc0 : 0 < c := by linarith
  have h1 := (abs_le.1 (hankelPsiR_sub_Q_le hc hf hε hM hx)).1
  have hQ : 0 ≤ hankelPsiLead c f x := by
    unfold hankelPsiLead
    refine mul_nonneg (by have := hankelXiD_neg hc0 hx; nlinarith)
      (mul_nonneg (hankelRho0_nonneg hc0 (mul_pos hc0 (hankelXi_pos hc0 hx)).le) hfx)
  linarith

/-! ### 2. Generalized band parameters & window lemma for `-U ≤ u_T ≤ 0` (`3 ≤ U`) -/

/-- `BandReductionParams` with `A_0 = √(32 U / (3 κ))` for `-U ≤ u_T ≤ 0` (`U ≥ 3`). -/
noncomputable def hankelBandParamsGen (U : ℝ) (hU : 3 ≤ U) : BandReductionParams where
  M := 1 / 2
  b := 1 / 100
  κ_ζ := 2 * langerKappa
  A_0 := Real.sqrt (32 * U / (3 * langerKappa))
  C_W := 2
  C_a := 4
  c_1 := 3 / 16
  c_2 := 1 / 2
  C_ν := 1
  κ_sub := 1
  C_τ := 11 / langerKappa
  hM := by norm_num
  hb := by norm_num
  hκ_ζ := by have := langerKappa_pos; positivity
  hA_0 := Real.sqrt_pos.mpr (by have := langerKappa_pos; positivity)
  hC_W := by norm_num
  hC_a := by norm_num
  hc_1 := by norm_num
  hc_2 := by norm_num
  hC_ν := by norm_num
  hκ_sub := by norm_num
  hC_τ := by have := langerKappa_pos; positivity

noncomputable def hankelWindowCGen (U : ℝ) (hU : 3 ≤ U) : ℝ :=
  6 / 5 * tebBandConst (hankelBandParamsGen U hU) + 17

lemma one_le_hankelWindowCGen (U : ℝ) (hU : 3 ≤ U) : 1 ≤ hankelWindowCGen U hU := by
  unfold hankelWindowCGen
  have := tebBandConst_pos (hankelBandParamsGen U hU)
  linarith

lemma hankelBand_A0_sq_gen {U : ℝ} (hU : 3 ≤ U) {c : ℝ} (hc : 0 < c) :
    ((hankelBandParamsGen U hU).A_0 * c ^ (-(1 / 3 : ℝ))) ^ 2 = 32 * U / (3 * langerScale c) := by
  have hk := langerKappa_pos
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have e : (c ^ (-(1 / 3 : ℝ))) ^ 2 = (c ^ (2 / 3 : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_neg hc.le]; norm_num
  show (Real.sqrt (32 * U / (3 * langerKappa)) * c ^ (-(1 / 3 : ℝ))) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt (by positivity), e]
  unfold langerScale
  field_simp

theorem hankelBandTau0_below_gen {U c u_T ξ : ℝ} (hU : 3 ≤ U) (hc : 3e6 ≤ c)
    (hScale : 11 * U ≤ langerScale c) (hu0 : u_T ≤ 0) (huU : -U ≤ u_T)
    (huA : |u_T| ≤ langerRadius c) (hξ : ξ < hankelXi c u_T) :
    hankelBandTau0 ξ ≤ (hankelBandParamsGen U hU).A_0 * c ^ (-(1 / 3 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hB : 0 ≤ (hankelBandParamsGen U hU).A_0 * c ^ (-(1 / 3 : ℝ)) :=
    mul_nonneg (hankelBandParamsGen U hU).hA_0.le (Real.rpow_nonneg hc0.le _)
  rcases le_or_gt (hankelBandMu ξ) 0 with h0 | h0
  · rw [hankelBandTau0_zero h0]; exact hB
  · have hξ0 : 0 < ξ := by
      by_contra hneg
      unfold hankelBandMu at h0; rw [ite_eq_right hneg] at h0; exact lt_irrefl _ h0
    have hmu := hankelBand_mu_below hc0 hu0 huA hξ0 hξ
    have hK := hankelBand_langerScale_ge hc
    have hmu' : hankelBandMu ξ = Real.log (Real.pi ^ 2 * ξ) := by
      unfold hankelBandMu; rw [ite_eq_left hξ0]
    have hμ2U : hankelBandMu ξ ≤ 2 * U / langerScale c := by
      rw [hmu']
      refine hmu.trans ?_
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hμsmall : hankelBandMu ξ < 3 / 16 := by
      refine lt_of_le_of_lt hμ2U ?_
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    have hsq := hankelBandTau0_sq_le h0.le hμsmall
    have hfin : hankelBandTau0 ξ ^ 2 ≤ ((hankelBandParamsGen U hU).A_0 * c ^ (-(1 / 3 : ℝ))) ^ 2 := by
      rw [hankelBand_A0_sq_gen hU hc0]
      have h1 : 16 / 3 * hankelBandMu ξ ≤ 16 / 3 * (2 * U / langerScale c) := by linarith
      have h2 : 16 / 3 * (2 * U / langerScale c) = 32 * U / (3 * langerScale c) := by ring
      linarith
    by_contra hlt
    push Not at hlt
    have := pow_lt_pow_left₀ hlt hB two_ne_zero
    linarith

theorem hankelBandTau0_band_gen {U c u_T R ξ : ℝ} (hU : 3 ≤ U) (hc : 3e6 ≤ c) (hu0 : u_T ≤ 0)
    (huA : |u_T| ≤ langerRadius c) (hR0 : 0 ≤ R) (hR : R ≤ langerRadius c)
    (hξ : ξ ∈ Icc (hankelXi c u_T) (hankelXi c (-R))) :
    hankelBandTau0 ξ ^ 2 ≤ (hankelBandParamsGen U hU).C_τ * c ^ (-(2 / 3 : ℝ)) * (-hankelBandU c ξ) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hm0, hm1, hm2⟩ := hankelBand_mu_band hc0 hu0 huA hR0 hR hξ
  have hT := hankelXi_w_bounds hc0 huA hu0
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hξ0 : 0 < ξ := by have : 0 ≤ Real.pi ^ 2 * hankelXi c u_T - 1 := hT.1; nlinarith [hξ.1]
  have hmu' : hankelBandMu ξ = Real.log (Real.pi ^ 2 * ξ) := by
    unfold hankelBandMu; rw [ite_eq_left hξ0]
  rw [← hmu'] at hm0 hm1 hm2
  have hw0 : 0 ≤ Real.pi ^ 2 * ξ - 1 := by nlinarith [hξ.1, hT.1]
  have hUb := hankelBandU_le hc0 hw0 (by
    have hRb := hankelXi_w_bounds hc0 (x := -R) (by rw [abs_neg, abs_of_nonneg hR0]; exact hR) (by linarith)
    nlinarith [hξ.2, hRb.2.1])
  have hK := langerScale_pos hc0
  have hUnn : 0 ≤ -hankelBandU c ξ := by
    have : 0 ≤ langerScale c * (Real.pi ^ 2 * ξ - 1) / 2 :=
      div_nonneg (mul_nonneg hK.le hw0) (by norm_num)
    linarith [hUb]
  have hsq := hankelBandTau0_sq_le hm0 (by linarith)
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hneg : c ^ (-(2 / 3 : ℝ)) = (c ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg hc0.le _
  have hKdef : langerScale c = c ^ (2 / 3 : ℝ) * langerKappa := rfl
  have hk := langerKappa_pos
  show _ ≤ 11 / langerKappa * c ^ (-(2 / 3 : ℝ)) * _
  rw [hneg]
  have h1 : 16 / 3 * hankelBandMu ξ ≤ 16 / 3 * (2 * (-hankelBandU c ξ) / langerScale c) := by linarith
  refine hsq.trans (h1.trans ?_)
  rw [hKdef]
  have e1 : 16 / 3 * (2 * -hankelBandU c ξ / (c ^ (2 / 3 : ℝ) * langerKappa)) =
      32 / 3 * (-hankelBandU c ξ / (c ^ (2 / 3 : ℝ) * langerKappa)) := by ring
  have e2 : 11 / langerKappa * (c ^ (2 / 3 : ℝ))⁻¹ * -hankelBandU c ξ =
      11 * (-hankelBandU c ξ / (c ^ (2 / 3 : ℝ) * langerKappa)) := by field_simp
  rw [e1, e2]
  have hq : 0 ≤ -hankelBandU c ξ / (c ^ (2 / 3 : ℝ) * langerKappa) :=
    div_nonneg hUnn (mul_pos hc23 hk).le
  nlinarith

/-- Generalized Hankel band-reduction instance for `-U ≤ u_T ≤ 0` (`3 ≤ U`). -/
noncomputable def hankelBandInstanceGen {U c ε u_T R : ℝ} {f : ℝ → ℝ} (hU : 3 ≤ U) (hc : 3e6 ≤ c)
    (hScale : 11 * U ≤ langerScale c) (hε : ε = 1 ∨ ε = -1) (hf : IsHankelEigenfn c ε f)
    (hmass : hankelMass c f = 1) (hu0 : u_T ≤ 0) (huU : -U ≤ u_T) (huA : |u_T| ≤ langerRadius c)
    (hRlb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hRub : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (htail : ∀ Δ : ℝ, c * hankelXi c u_T ≤ Δ → 0 ≤ f Δ) :
    BandReductionInstance (hankelBandParamsGen U hU) :=
  have hc0 : 0 < c := by linarith
  have hc32 : 3 / 2 < c := by linarith
  have hR0 : (0 : ℝ) ≤ R := le_trans (by positivity) hRlb
  have hR : R ≤ langerRadius c := hRub.trans (hankelBand_radius_ge_one hc)
  have hfinP := isFiniteMeasure_hankelDmPos hc0 hf
  have hfinN := isFiniteMeasure_hankelDmNeg hc0 hf
  { c := c
    ε := ε
    R := R
    hc := by linarith
    hε := hε
    hR_lb := hRlb
    hR_ub := hRub
    hρR_ub := hankelBand_rho_le hc hRub
    W_tilde := hankelWtS c ε f
    hW_cont := hankelWtS_continuousOn hc32 hf
    hW_holo := hankelWtS_differentiableOn hc32 hf
    hW_symm := fun ζ h0 h1 => hankelWtS_one_sub hc32 hf hε h0 h1
    hW_bound := fun ζ h0 h1 => by
      have h := hankelWtS_norm_le hc32 hf hε h0 h1
      rw [hmass, one_mul] at h
      have h2 := hankelBand_exp_le_two (show 1 ≤ c by linarith)
      have h3 : 0 ≤ (1 + ‖ζ‖) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
      show ‖hankelWtS c ε f ζ‖ ≤ 2 * (1 + ‖ζ‖) ^ (1 / 2 : ℝ)
      nlinarith
    dmPos := hankelDmPos c f
    dmNeg := hankelDmNeg c f
    hdmPos_fin := hfinP
    hdmNeg_fin := hfinN
    hdmPos_supp := hankelDmPos_Iic c f
    hdmNeg_supp := hankelDmNeg_Iic c f
    hdm_tv := (hankelDm_tv hc0 hf).trans_le (le_of_eq hmass)
    T := hankelXi c u_T
    hdm_nonneg_tail := hankelDmNeg_tail hc0 htail
    E_sub := ∅
    hE_sub_meas := MeasurableSet.empty
    hE_sub_sub := empty_subset _
    K_edge := hankelBandK c
    hK_meas := hankelBandK_measurable hc0
    hW_edge := hankelBand_W_edge hc32 hf
    hK_sub := fun ξ hξ => absurd hξ (notMem_empty ξ)
    a_0 := hankelEdgeAmp c
    a_0' := hankelEdgeAmp' c
    a_2 := fun _ => 1
    R_0 := fun _ _ => 0
    Phi := hankelBandPhi
    hK_factor := fun ξ _ τ => rfl
    ha_2_bd := fun ξ _ => by show ‖(1 : ℂ)‖ ≤ 4; simp
    ha_0_deriv := hankelEdgeAmp_hasDerivAt hc0
    ha_0_bd := fun τ => hankelEdgeAmp_bound (by linarith) τ
    hR_0_nonpos := fun ξ _ τ => le_refl _
    hR_0_cont := fun ξ _ => continuousOn_const
    hR_0_even := fun ξ _ τ => rfl
    hR_0_unimodal := fun ξ _ => ⟨0, monotoneOn_const, antitoneOn_const⟩
    hPhi_odd := fun ξ _ τ => hankelEdgePhi_odd _ τ
    ν := fun τ => τ
    ν' := fun _ => 1
    invNu' := fun _ => 0
    hν_deriv := fun τ _ => hasDerivAt_id τ
    hν'_cont := continuousOn_const
    hν'_inv_pos := fun τ _ => ⟨by norm_num, by show ((1 : ℝ))⁻¹ ≤ 1; norm_num⟩
    hν'_inv_deriv := fun τ _ => hasDerivAt_const τ _
    hinvNu'_cont := continuousOn_const
    hinvNu'_int := by show ∫ τ in Ioi (0 : ℝ), |(0 : ℝ)| ≤ 1; simp
    hinvNu'_integrable := integrableOn_zero
    μ := hankelBandMu
    m := hankelEdgeM
    m' := hankelEdgeM'
    hPhi_deriv := fun ξ hξ τ hτ => by
      have hξ0 : 0 < ξ := hξ.1
      have h := hankelEdgePhi_hasDerivAt (Real.log (Real.pi ^ 2 * ξ)) hτ
      have hμ : hankelBandMu ξ = Real.log (Real.pi ^ 2 * ξ) := by
        unfold hankelBandMu; rw [ite_eq_left hξ0]
      exact h.congr_deriv (by rw [hμ]; ring)
    hm_0 := hankelEdgeM_zero
    hm_cont := hankelEdgeM_continuousOn
    hm_strictMono := hankelEdgeM_strictMonoOn
    hm_deriv := fun τ hτ => hankelEdgeM_hasDerivAt hτ
    hm_step := fun τ hτ => hankelEdgeM_step hτ
    hm_slope := fun τ hτ => by
      show (1 / 2 : ℝ) * τ / (1 + τ ^ 3) ≤ hankelEdgeM' τ / 1
      rw [div_one]; exact hankelEdgeM_slope hτ
    τ_0 := hankelBandTau0
    hτ_0_nn := hankelBandTau0_nonneg
    hτ_0_eq_zero := fun ξ h => hankelBandTau0_zero h
    hτ_0_root := fun ξ h => hankelBandTau0_root h
    u_tilde := hankelBandU c
    Delta := hankelXi c
    hτ_0_below := fun ξ hξ => hankelBandTau0_below_gen hU hc hScale hu0 huU huA hξ.1
    hτ_0_band := fun ξ hξ => hankelBandTau0_band_gen hU hc hu0 huA hR0 hR hξ
    hu_tilde_int := by
      refine ContinuousOn.integrableOn_Icc ?_
      intro ξ hξ
      obtain ⟨h0, h1⟩ := hankelBand_w_band hc0 hu0 huA hR0 hR hξ
      exact (hankelBandU_continuousAt h0 h1).neg.continuousWithinAt }

theorem hankel_band_reduction_pos_gen {U c ε u_T R : ℝ} {f : ℝ → ℝ} (hU : 3 ≤ U) (hc : 3e6 ≤ c)
    (hScale : 11 * U ≤ langerScale c) (hε : ε = 1 ∨ ε = -1) (hf : IsHankelEigenfn c ε f)
    (hmass : hankelMass c f = 1) (hu0 : u_T ≤ 0) (huU : -U ≤ u_T) (huA : |u_T| ≤ langerRadius c)
    (hRlb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hRub : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (htail : ∀ Δ : ℝ, c * hankelXi c u_T ≤ Δ → 0 ≤ f Δ) {ζ₀ : ℂ} {ψ : ℝ}
    (hlo : rhoR (hankelBandParamsGen U hU) c R / 3 ≤ ‖ζ₀‖)
    (hhi : ‖ζ₀‖ ≤ 2 * rhoR (hankelBandParamsGen U hU) c R)
    (hcos_eq : ζ₀.re = ‖ζ₀‖ * Real.cos ψ) (hcos : 0 < Real.cos ψ) :
    ‖hankelWtS c ε f ζ₀‖ ≤ tebBandConst (hankelBandParamsGen U hU) * c ^ (-(5 / 6 : ℝ)) *
      (c ^ (1 / 3 : ℝ) *
        (bandB1 (hankelBandInstanceGen hU hc hScale hε hf hmass hu0 huU huA hRlb hRub htail) +
          bandB2 (hankelBandInstanceGen hU hc hScale hε hf hmass hu0 huU huA hRlb hRub htail)) +
        c ^ (-(1 / 6 : ℝ))) / Real.cos ψ :=
  teb_band_reduction_pos (hankelBandInstanceGen hU hc hScale hε hf hmass hu0 huU huA hRlb hRub htail)
    hlo hhi hcos_eq hcos

theorem hankelBootB1_nonneg_gen {c : ℝ} (hc : 3e6 ≤ c) (f : ℝ → ℝ) {u_T R : ℝ}
    (hu0 : u_T ≤ 0) (huA : |u_T| ≤ langerRadius c) (hR0 : 0 < R) (hRA : R ≤ langerRadius c) :
    0 ≤ hankelBootB1 c f R u_T := by
  have hc0 : 0 < c := by linarith
  have hK := langerScale_pos hc0
  unfold hankelBootB1
  refine mul_nonneg (inv_nonneg.2 hR0.le) ?_
  refine setIntegral_nonneg measurableSet_Icc fun ξ hξ => ?_
  obtain ⟨h0, h1⟩ := hankelBand_w_band hc0 hu0 huA hR0.le hRA hξ
  have hU := hankelBandU_le hc0 h0 (by linarith)
  have hnn : 0 ≤ langerScale c * (Real.pi ^ 2 * ξ - 1) / 2 :=
    div_nonneg (mul_nonneg hK.le h0) (by norm_num)
  show 0 ≤ -hankelBandU c ξ
  linarith

theorem hankel_window_Wt_bound_gen {U c ε T u_T R : ℝ} {f : ℝ → ℝ} (hU : 3 ≤ U) (hc : 3e6 ≤ c)
    (hScale : 11 * U ≤ langerScale c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (huU : -U ≤ u_T) (huA : |u_T| ≤ langerRadius c)
    (hRlb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hRub : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hB12 : 0 ≤ hankelBootB1 c f R u_T + hankelBootB2 c f R)
    {σ τ0 h : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hρlo : 9 / 10 * rhoR hankelBandParams c R ≤ ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖)
    (hρhi : ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ≤ 11 / 10 * rhoR hankelBandParams c R)
    (hh : h ≤ 1 / 10 * ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖)
    {y : ℝ} (hy : |y - τ0| ≤ h) :
    ‖hankelWt c f ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      tebBandConst (hankelBandParamsGen U hU) * c ^ (-(5 / 6 : ℝ)) *
        (c ^ (1 / 3 : ℝ) * (hankelBootB1 c f R u_T + hankelBootB2 c f R) + c ^ (-(1 / 6 : ℝ))) *
        (11 / 10 * ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ / σ) := by
  have hc0 : 0 < c := by linarith
  set ζ : ℂ := (σ : ℂ) + (τ0 : ℂ) * Complex.I with hζ
  set ζ0 : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I with hζ0
  have hρ0 : 0 ≤ rhoR hankelBandParams c R := by
    unfold rhoR; have := hankelBandParams.hκ_ζ; positivity
  have hdiff : ‖ζ0 - ζ‖ = |y - τ0| := norm_window_diff σ τ0 y
  have hd1 := norm_sub_norm_le ζ0 ζ
  have hd2 := norm_sub_norm_le ζ ζ0
  rw [norm_sub_rev] at hd2
  rw [hdiff] at hd1 hd2
  have hζ0lo : 9 / 10 * ‖ζ‖ ≤ ‖ζ0‖ := by linarith
  have hζ0hi : ‖ζ0‖ ≤ 11 / 10 * ‖ζ‖ := by linarith
  have hζ0pos : 0 < ‖ζ0‖ := by
    have : σ ≤ ‖ζ0‖ := by simpa [hζ0] using Complex.re_le_norm ζ0
    linarith
  have hre : ζ0.re = σ := by simp [hζ0]
  have hρeq : rhoR (hankelBandParamsGen U hU) c R = rhoR hankelBandParams c R := rfl
  have hlo : rhoR (hankelBandParamsGen U hU) c R / 3 ≤ ‖ζ0‖ := by rw [hρeq]; nlinarith
  have hhi : ‖ζ0‖ ≤ 2 * rhoR (hankelBandParamsGen U hU) c R := by rw [hρeq]; nlinarith
  have hq : σ / ‖ζ0‖ ≤ 1 := by
    rw [div_le_one hζ0pos]
    have := Complex.re_le_norm ζ0; rwa [hre] at this
  have hdiv_nn : 0 ≤ σ / ‖ζ0‖ := div_nonneg hσ0.le hζ0pos.le
  have hcos_eq : ζ0.re = ‖ζ0‖ * Real.cos (Real.arccos (σ / ‖ζ0‖)) := by
    rw [Real.cos_arccos (by linarith) hq, hre]; field_simp
  set ψ := Real.arccos (σ / ‖ζ0‖) with hψ
  have hcosψ : Real.cos ψ = σ / ‖ζ0‖ := by rw [hψ, Real.cos_arccos (by linarith) hq]
  have hcos : 0 < Real.cos ψ := by rw [hcosψ]; positivity
  have hbr := hankel_band_reduction_pos_gen hU hc hScale hε hf.toIsHankelEigenfn hM hu0 huU huA
    hRlb hRub (fun Δ hΔ => hf.tail_nonneg Δ (by rw [← hT]; exact hΔ)) hlo hhi hcos_eq hcos
  rw [hankelWtS_eq (by linarith) hf.toIsHankelEigenfn (by rw [hre]; exact hσ0.le)
    (by rw [hre]; exact hσ1)] at hbr
  have hB1 : bandB1 (hankelBandInstanceGen hU hc hScale hε hf.toIsHankelEigenfn hM hu0 huU huA hRlb hRub
      (fun Δ hΔ => hf.tail_nonneg Δ (by rw [← hT]; exact hΔ))) = hankelBootB1 c f R u_T := rfl
  have hB2 : bandB2 (hankelBandInstanceGen hU hc hScale hε hf.toIsHankelEigenfn hM hu0 huU huA hRlb hRub
      (fun Δ hΔ => hf.tail_nonneg Δ (by rw [← hT]; exact hΔ))) = hankelBootB2 c f R := rfl
  rw [hB1, hB2] at hbr
  refine hbr.trans ?_
  set Q := tebBandConst (hankelBandParamsGen U hU) * c ^ (-(5 / 6 : ℝ)) *
    (c ^ (1 / 3 : ℝ) * (hankelBootB1 c f R u_T + hankelBootB2 c f R) + c ^ (-(1 / 6 : ℝ)))
  have hQ0 : 0 ≤ Q := by
    have := tebBandConst_pos (hankelBandParamsGen U hU)
    have := Real.rpow_nonneg hc0.le (-(5 / 6 : ℝ))
    have := Real.rpow_nonneg hc0.le (1 / 3 : ℝ)
    have := Real.rpow_nonneg hc0.le (-(1 / 6 : ℝ))
    positivity
  have h1 : Q / (σ / ‖ζ0‖) ≤ Q * (11 / 10 * ‖ζ‖ / σ) := by
    rw [div_div_eq_mul_div, mul_comm Q ‖ζ0‖, div_eq_mul_one_div,
      show Q * (11 / 10 * ‖ζ‖ / σ) = Q * (11 / 10 * ‖ζ‖ * (1 / σ)) by ring]
    calc ‖ζ0‖ * Q * (1 / σ) = Q * (‖ζ0‖ * (1 / σ)) := by ring
      _ ≤ Q * (11 / 10 * ‖ζ‖ * (1 / σ)) := by gcongr
  rw [← hcosψ] at h1
  exact h1

set_option maxHeartbeats 4000000 in
/-- **Generalized `YVEnvBound`** (`teb:mellin` (2)–(3), proved) for arbitrary `-U ≤ u_T ≤ 0` (`U ≥ 3`). -/
theorem hankel_yv_window_gen {U c ε T u_T R : ℝ} {f : ℝ → ℝ} (hU : 3 ≤ U) (hc : 1e14 ≤ c)
    (hScale : 11 * U ≤ langerScale c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (huU : -U ≤ u_T) (huA : |u_T| ≤ langerRadius c)
    (hRlb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hRub : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1) :
    YVEnvBound (hankelPsi c f) c R
      (hankelWindowCGen U hU * (c ^ (1 / 3 : ℝ) * (hankelBootB1 c f R u_T + hankelBootB2 c f R) + 1)) := by
  intro u _hIm hlo hhi hX
  obtain ⟨t, ht14, hct, hk4, hK8, hτi, hc56, hlog⟩ := hankel_window_cnum hc
  have hsqc : √c = t ^ 6 := by
    rw [hct, show t ^ 12 = (t ^ 6) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have hθ : 1e5 ≤ 2 * c ^ (-(1 / 12 : ℝ)) * √c := by
    rw [hτi, hsqc]
    have ht0 : 0 < t := by linarith
    have h5 : (14 : ℝ) ^ 5 ≤ t ^ 5 := pow_le_pow_left₀ (by norm_num) ht14 5
    have : 2 * t⁻¹ * t ^ 6 = 2 * t ^ 5 := by field_simp
    rw [this]; norm_num at h5; linarith
  have hc3 : 3e6 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have ht0 : 0 < t := by linarith
  set k : ℝ := c ^ (1 / 3 : ℝ) with hkdef
  have hk0 : 0 < k := Real.rpow_pos_of_pos hc0 _
  have hXorig := hX
  have ht8 : (14 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht14 8
  have ht8' : (1.4e9 : ℝ) ≤ t ^ 8 := by norm_num at ht8; linarith
  have hRlb8 : (1 / 100 : ℝ) ^ 2 * t ^ 8 ≤ R := by rw [← hK8]; exact hRlb
  have hRub8 : R ≤ (1 / 100 : ℝ) ^ 2 * t ^ 8 + 1 := by rw [← hK8]; exact hRub
  have hR1 : 1e5 ≤ R := by nlinarith only [hRlb8, ht8']
  obtain ⟨hκ1, _hκ2⟩ := hankelLangerKappa_bounds
  have hRdisc : R + 1 ≤ c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by
    rw [hK8]; nlinarith only [hRub8, ht8', mul_nonneg (sub_nonneg.2 hκ1) (pow_pos ht0 8).le]
  have hRA : R ≤ langerRadius c := by
    have : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := rfl
    rw [this]; linarith only [hRdisc]
  set N : ℝ := ‖u‖ with hNdef
  have hN1 : 9e4 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hu_ne : u ≠ 0 := by intro h; rw [h, norm_zero] at hNdef; linarith
  set s : ℝ := N ^ (1 / 2 : ℝ) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hN0 _
  have hsqrtN : Real.sqrt N = s := by rw [hsdef, Real.sqrt_eq_rpow]
  set X : ℝ := (u ^ (1 / 2 : ℂ)).re with hXdef
  rw [hsqrtN] at hX
  have hθ0 : 0 < 2 * c ^ (-(1 / 12 : ℝ)) := by positivity
  have hX0 : 0 < X := by
    have : 0 < 2 * c ^ (-(1 / 12 : ℝ)) * s := by positivity
    linarith
  have hcut := hankel_window_slit hu_ne hX0
  set K : ℝ := c ^ (2 / 3 : ℝ) * langerKappa with hK
  have hK0 : 0 < K := mul_pos (Real.rpow_pos_of_pos hc0 _) langerKappa_pos
  set y : ℂ := u / (K : ℂ) with hy
  have hKne : (K : ℂ) ≠ 0 := by exact_mod_cast hK0.ne'
  have huy : (K : ℂ) * y = u := by rw [hy]; field_simp
  have hyn : ‖y‖ ≤ 4.94e-4 := by
    rw [hy, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK0, div_le_iff₀ hK0]
    linarith
  obtain ⟨q, hq, hqn, hqu, hqg⟩ := chart_saddle_data langerEta_etaC hc0 hyn (by rw [huy]; exact hcut)
  rw [huy] at hqu
  obtain ⟨σ, τ0, h, hζeq, hσpos, hσle, hτ0, hh0, hhsq, hζlo, hζhi, hhle, hnzσ, _hXk, hkσ⟩ :=
    hankel_window_saddle hc hRlb hRub hlo hhi hθ hXorig hq hqn hqu
  set ζ := saddleRoot q with hζdef
  have hζn : ‖ζ‖ ≤ 0.035 := norm_saddleRoot_le hqn
  have hσ1 : σ < 1 := by linarith
  have hcσ0 : 0 < c * σ := by positivity
  have hnzσ' : ‖ζ‖ / σ ≤ 1.002 * s / X := by rw [hζeq]; exact hnzσ
  have hB12 : 0 ≤ hankelBootB1 c f R u_T + hankelBootB2 c f R := by
    have h1 := hankelBootB1_nonneg_gen hc3 f hu0 huA (by linarith) hRA
    have h2 := hankelBootB2_nonneg c f R
    linarith
  set Bs : ℝ := hankelBootB1 c f R u_T + hankelBootB2 c f R
  set Cy : ℝ := tebBandConst (hankelBandParamsGen U hU) with hCydef
  set Q : ℝ := Cy * c ^ (-(5 / 6 : ℝ)) * (k * Bs + c ^ (-(1 / 6 : ℝ))) with hQdef
  have hCy : 0 < Cy := tebBandConst_pos (hankelBandParamsGen U hU)
  have hc56' : 0 < c ^ (-(5 / 6 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hc16 : 0 < c ^ (-(1 / 6 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
  set W : ℝ := Q * (11 / 10 * ‖ζ‖ / σ) with hWdef
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hW : ∀ y : ℝ, |y| ≤ 1 / 3 → |y - τ0| ≤ h →
      ‖hankelWt c f ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ W := fun y _ hy => by
    have := hankel_window_Wt_bound_gen hU hc3 hScale hf hε hM hT hu0 huU huA hRlb hRub hB12
      hσpos hσ1 hζlo hζhi hhle hy
    rw [← hζeq] at this
    exact this
  set ℓ : ℂ := -(gSer etaC ζ) with hℓ
  have hl : ℓ.re ≤ 1 / 200 := by
    have h1 := Complex.re_le_norm (-(gSer etaC ζ))
    rw [norm_neg] at h1
    exact h1.trans (norm_gSer_small hζn)
  have hcrit : gSer etaC ((σ : ℂ) + (τ0 : ℂ) * Complex.I) + ℓ = 0 := by rw [← hζeq, hℓ]; ring
  have hwin := hankel_local_density_window (by linarith) hf.toIsHankelEigenfn hε hM ℓ hl hσpos hσle hτ0
    hcrit hh0 hW0 hW
  rw [← hζeq] at hwin
  have hph : (c : ℂ) * hankelLocPhi ℓ ζ = -(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ) := by
    rw [← hqu, ← phase_at_saddle langerEta_etaC hc0 hq hqn]
    unfold hankelLocPhi; ring
  have hexp : Real.exp (c * (hankelLocPhi ℓ ζ).re) = airyEnv u := by
    have h2 := congrArg Complex.re hph
    rw [Complex.re_ofReal_mul] at h2
    unfold airyEnv; rw [h2]; simp [Complex.mul_re]
  rw [hexp] at hwin
  have hlocal_eq : Complex.log (1 + chartYinv etaC y) = ℓ := hqg.symm
  have hwn := norm_chartYinv_le langerEta_etaC hyn
  have h1w : 0.9995 ≤ ‖1 + chartYinv etaC y‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(chartYinv etaC y))
    rw [norm_neg, norm_one, sub_neg_eq_add] at this; linarith
  have hder := norm_deriv_chartYinv_le hyn
  have hpref : k / (2 * π * langerKappa) ≤ k * 0.27 := hankel_pref_le hk0.le
  have hnorm : ‖hankelPsi c f u‖ = (k / (2 * π * langerKappa)) *
      ‖deriv (chartYinv etaC) y‖ / ‖1 + chartYinv etaC y‖ *
      ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖ := by
    show ‖hankelPsiY c f y‖ = _
    unfold hankelPsiY
    rw [norm_mul, norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have := langerKappa_pos; positivity)]
  have hL0 := norm_nonneg (hankelLocal c f (Complex.log (1 + chartYinv etaC y)))
  have hD0 := norm_nonneg (deriv (chartYinv etaC) y)
  have hpref0 : 0 ≤ k / (2 * π * langerKappa) := by have := langerKappa_pos; positivity
  have hΨ : ‖hankelPsi c f u‖ ≤ 0.272 * k *
      ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖ := by
    rw [hnorm]
    calc (k / (2 * π * langerKappa)) * ‖deriv (chartYinv etaC) y‖ / ‖1 + chartYinv etaC y‖ *
          ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖
        ≤ (k * 0.27) * (1 / 0.996) / 0.9995 *
          ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖ := by gcongr
      _ ≤ 0.272 * k * ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖ := by
        have h1 : (0.27 : ℝ) * (1 / 0.996) / 0.9995 ≤ 0.272 := by norm_num
        have h2 : (k * 0.27) * (1 / 0.996) / 0.9995 ≤ 0.272 * k := by
          calc (k * 0.27) * (1 / 0.996) / 0.9995 = (0.27 * (1 / 0.996) / 0.9995) * k := by ring
            _ ≤ 0.272 * k := by gcongr
        gcongr
  have hXs0 : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
  have hk3 : k ^ 3 = c := by rw [hkdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  set G : ℝ := Real.sqrt (c * σ) with hGdef
  have hG0 : 0 < G := Real.sqrt_pos.2 hcσ0
  have hGk : k * Real.sqrt X ≤ G := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    rw [mul_pow, Real.sq_sqrt hX0.le, ← hk3]
    have h1 : k ^ 2 * X ≤ k ^ 2 * (k * σ) := by gcongr
    have e : k ^ 2 * (k * σ) = k ^ 3 * σ := by ring
    linarith
  have hsqrt3 : Real.sqrt (π / ((2 / 5) * c * σ)) ≤ 3 / G := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [div_pow, hGdef, Real.sq_sqrt hcσ0.le]
    have : π / ((2 / 5) * c * σ) = (5 / 2 * π) / (c * σ) := by field_simp
    rw [this, div_le_div_iff_of_pos_right hcσ0]
    nlinarith only [Real.pi_lt_d2]
  have hNc : N ≤ c ^ (2 / 3 : ℝ) := by rw [hK8]; have : N ≤ R + 1 := hhi; linarith
  have hQs : Q * s ≤ Cy * (k * Bs + 1) * N ^ (-(3 / 4 : ℝ)) := by
    have hL1 := hankel_window_L1 hc0 hN0 hNc
    have hc16' : c ^ (-(1 / 6 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hBs0 : 0 ≤ k * Bs := mul_nonneg hk0.le hB12
    calc Q * s = Cy * (k * Bs + c ^ (-(1 / 6 : ℝ))) * (s * c ^ (-(5 / 6 : ℝ))) := by rw [hQdef]; ring
      _ ≤ Cy * (k * Bs + 1) * N ^ (-(3 / 4 : ℝ)) := by
        have h1 : k * Bs + c ^ (-(1 / 6 : ℝ)) ≤ k * Bs + 1 := by linarith
        have h2 : 0 ≤ s * c ^ (-(5 / 6 : ℝ)) := by positivity
        gcongr
  have hXN : X ≤ N ^ (1 / 2 : ℝ) := by
    have := Complex.re_le_norm (u ^ (1 / 2 : ℂ))
    have e : ‖u ^ (1 / 2 : ℂ)‖ = N ^ (1 / 2 : ℝ) := norm_saddleRoot u
    linarith
  have hci := hankel_window_L2 hc0 hN0 hNc hX0 hXN
  have hkc : k * c⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hc0, one_mul, hk4, hct]
    exact pow_le_pow_right₀ (by linarith) (by norm_num)
  have hek : Real.exp (-(0.035 * c * σ)) * k ≤ 1 := by
    have h1 : Real.exp (-(0.035 * c * σ)) ≤ Real.exp (-k) := Real.exp_le_exp.2 (by linarith only [hkσ])
    have h2 : Real.exp (-k) * k ≤ 1 := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos k), mul_one]
      linarith only [Real.add_one_le_exp k]
    nlinarith only [mul_le_mul_of_nonneg_right h1 hk0.le, h2]
  have hE : Real.exp (-((2 / 5) * c * σ * h ^ 2)) = (c⁻¹) ^ 2 := by
    have : (2 / 5) * c * σ * h ^ 2 = 2 * Real.log c := by rw [hhsq]; field_simp
    rw [this]
    have h2 : Real.exp (2 * Real.log c) = c ^ 2 := by
      rw [show (2 : ℝ) * Real.log c = ((2 : ℕ) : ℝ) * Real.log c by norm_num, Real.exp_nat_mul,
        Real.exp_log hc0]
    rw [Real.exp_neg, h2, inv_pow]
  have hCc : 2 * (2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c)) =
      2 * (2 * Real.exp (-(0.035 * c * σ)) * c⁻¹ / 0.07) := by field_simp
  have hΛ : 1 ≤ k * Bs + 1 := by have := mul_nonneg hk0.le hB12; linarith
  have harith := hankel_window_arith (k := k) (X := X) (Xs := Real.sqrt X) (s := s) (σ := σ) (nz := ‖ζ‖)
    (G := G) (W := W) (Q := Q) (Λ := k * Bs + 1) (Cy := Cy)
    (N34 := N ^ (-(3 / 4 : ℝ))) (ci := c⁻¹) (e := Real.exp (-(0.035 * c * σ)))
    hk0 hX0 hXs0 hs0 hG0 hQ0 hΛ hCy (Real.rpow_nonneg hN0.le _) (inv_pos.2 hc0)
    (Real.exp_pos _).le (le_of_eq hWdef) hnzσ' hQs hGk hci hkc hek
    (A := (100 / 81) * W * Real.sqrt (π / ((2 / 5) * c * σ))) (by gcongr)
  have hX32 : X ^ (-(3 / 2 : ℝ)) = (X * Real.sqrt X)⁻¹ := by
    rw [Real.rpow_neg hX0.le]; congr 1
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hX0, Real.rpow_one]
  have hair := (airyEnv_pos u).le
  rw [hlocal_eq] at hΨ
  calc ‖hankelPsi c f u‖ ≤ 0.272 * k * ‖hankelLocal c f ℓ‖ := hΨ
    _ ≤ 0.272 * k * (airyEnv u * ((100 / 81 * W * Real.sqrt (π / (2 / 5 * c * σ)) +
          4 / 3 * Real.exp (-(2 / 5 * c * σ * h ^ 2)) +
          2 * (2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c))))) :=
        mul_le_mul_of_nonneg_left hwin (by positivity)
    _ = airyEnv u * (0.272 * k * ((100 / 81) * W * Real.sqrt (π / ((2 / 5) * c * σ)) +
          (4 / 3) * (c⁻¹) ^ 2 + 2 * (2 * Real.exp (-(0.035 * c * σ)) * c⁻¹ / 0.07))) := by
        rw [hE, hCc]; ring
    _ ≤ airyEnv u * ((1.2 * Cy * (k * Bs + 1) + 17) * (N ^ (-(3 / 4 : ℝ)) / (X * Real.sqrt X))) := by
        gcongr
    _ ≤ airyEnv u * (hankelWindowCGen U hU * (k * Bs + 1) * (N ^ (-(3 / 4 : ℝ)) / (X * Real.sqrt X))) := by
        have h1 : 1.2 * Cy * (k * Bs + 1) + 17 ≤ hankelWindowCGen U hU * (k * Bs + 1) := by
          unfold hankelWindowCGen; rw [← hCydef]; nlinarith only [hΛ]
        have h2 : 0 ≤ N ^ (-(3 / 4 : ℝ)) / (X * Real.sqrt X) := by positivity
        gcongr
    _ = _ := by rw [hX32]; field_simp

/-- info: 'FormalResearch.SignUncertainty.hankelXi_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelXi_approx

/-- info: 'FormalResearch.SignUncertainty.hankelLevel_to_u' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelLevel_to_u

/-- info: 'FormalResearch.SignUncertainty.hankel_psi_sign_of_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_psi_sign_of_point

/-- info: 'FormalResearch.SignUncertainty.hankel_yv_window_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_yv_window_gen

end FormalResearch.SignUncertainty
