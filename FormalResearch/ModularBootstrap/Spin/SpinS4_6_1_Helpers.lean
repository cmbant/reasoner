/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_6_1_Arc
public import FormalResearch.TwoEdgeBootstrap.WeakFeedback

/-!
# Section 6.1 Weak Two-Edge Bootstrap Shrinkage Bound (`s4:6.1`)

Proves `spinS4_6_1_shrink_bound`: for any `C₀ > 0`, large `c`, `|x₁ - ξ_*| ≤ C₀ n^{-2/3}`,
`a₁ < u_T ≤ |a₁| + 1`, `b(u_T) = x₁`, and `SpinSlackHyp c x₁ Φ`,
we have `n^{1/3} (u_T - a₁) ≤ C_loc log n`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real ENNReal Interval
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.TwoEdgeBootstrap
open FormalResearch.Special

section WindowAndLine

private lemma spin_window_re_le {C₀ r₁ c x₁ u_lo u_hi : ℝ}
    {Φ : ℝ × ℝ → ℝ}
    (hc40 : 40 ≤ c) (hr₁_pos : 0 < r₁) (hr₁_lt : r₁ < xiStar)
    (hx₁_c0 : x₁ ≤ xiStar + C₀ * (c - 1) ^ (-(2 / 3 : ℝ)))
    (hx₁_hi : x₁ ≤ xiStar + r₁)
    (hS : SpinSlackHyp c x₁ Φ) (hB_pos : 0 < spinCalNorm c Φ)
    (hlo_gt : -(virasoroAC (c - 1) ^ 2) < u_lo) (h12 : u_lo ≤ u_hi)
    (hhi_lt : u_hi < virasoroAC (c - 1) ^ 2)
    (hbu_lo : (virasoroBChart (c - 1) (u_lo : ℂ)).re = xiStar + r₁)
    (hbu_hi : (virasoroBChart (c - 1) (u_hi : ℂ)).re = xiStar - r₁)
    {C₂₃ C₂₄ C_p : ℝ} (hC23 : 0 < C₂₃) (hC24 : 0 < C₂₄) (hCp : 0 < C_p)
    (hcal_23 : spinCalInt c Φ ≤ (C₂₃ + 1) * ((c - 1) ^ (-(2 / 3 : ℝ)) * Real.log (c - 1)))
    (h24_bd : (spinRhoProjMeasure c (fun q => max (-spinG ((c - 1) / 12) Φ q.1 q.2) 0)
      (Icc 0 (xiStar - r₁))).toReal ≤ C₂₄ * ((c - 1) ^ (-(2 / 3 : ℝ)) * Real.log (c - 1)) +
        C_p * (c - 1) ^ (-3 : ℝ)) :
    let n := c - 1
    ∫ u in u_lo..u_hi, (((2 : ℝ) : ℂ) * spinPtilde c Φ (u : ℂ)).re ≤
      2 * (spinCalNorm c Φ)⁻¹ * ((C₂₃ + 1) / 2 + C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
  intro n
  set a : ℝ := n / 12
  have hn_ge39 : 39 ≤ n := by dsimp [n]; linarith only [hc40]
  have hn_pos : 0 < n := by linarith only [hn_ge39]
  have hn_ge1 : 1 ≤ n := by linarith only [hn_ge39]
  have ha_pos : 0 < a := by dsimp [a]; linarith only [hn_pos]
  let Q : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re
  have hQ_int : Integrable Q volume := integrable_spinCalInt_integrand hc40 hS.2.1
  have hQmax_int : Integrable (fun b : ℝ => max (-Q b) 0) volume :=
    hQ_int.neg.sup (integrable_zero _ _ _)
  have hL_neg : ∀ b : ℝ, spinL (-b) = spinL b := fun b => by unfold spinL; rw [abs_neg]
  have hG_even : ∀ b : ℝ, (spinGcal a Φ ((-b : ℝ) : ℂ)).re = (spinGcal a Φ (b : ℂ)).re := fun b => by
    rw [spinGcal_re_ofReal ha_pos.le hS.2.1 (-b), spinGcal_re_ofReal ha_pos.le hS.2.1 b]
    congr 1
    have hsum : ∀ d : ℝ, spinHbCalReal (-b) (-d) * spinG a Φ (-b + -d) (-b - -d) =
        spinHbCalReal b d * spinG a Φ (b + d) (b - d) := fun d => by
      rw [spinHbCalReal_neg, show -b + -d = -(b + d) by ring, show -b - -d = -(b - d) by ring,
        spinG_d4_neg_left hS.2.1, spinG_d4_neg_right hS.2.1]
    rw [← integral_neg_eq_self (fun d => spinHbCalReal (-b) d * spinG a Φ (-b + d) (-b - d))]
    exact integral_congr_ae (Eventually.of_forall hsum)
  have hQ_even : ∀ b : ℝ, Q (-b) = Q b := fun b => by dsimp [Q]; rw [hL_neg, hG_even]
  have hhalf_int : 2 * ∫ b in Ioi (0 : ℝ), Q b = spinCalInt c Φ := by
    have hneg_eq : ∫ b in Iio (0 : ℝ), Q b = ∫ b in Ioi (0 : ℝ), Q b := by
      rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
        ← integral_neg_eq_self (fun b => (Ioi (0 : ℝ)).indicator Q b)]
      refine integral_congr_ae (Eventually.of_forall fun b => ?_)
      by_cases hb : b < 0
      · have hnb : -b ∈ Ioi (0 : ℝ) := by simpa using hb
        have hbm : b ∈ Iio (0 : ℝ) := hb
        simp [Set.indicator_of_mem hbm, Set.indicator_of_mem hnb, hQ_even b]
      · have hnot1 : b ∉ Iio (0 : ℝ) := hb
        have hnot2 : -b ∉ Ioi (0 : ℝ) := fun h => hb (by simpa using h)
        simp [Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot2]
    have hunion : (∫ b in Iic (0 : ℝ), Q b) + ∫ b in Ioi (0 : ℝ), Q b = ∫ b : ℝ, Q b := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hQ_int.integrableOn hQ_int.integrableOn, Iic_union_Ioi, setIntegral_univ]
    rw [MeasureTheory.integral_Iic_eq_integral_Iio, hneg_eq] at hunion
    have hcal : ∫ b : ℝ, Q b = spinCalInt c Φ := rfl
    linarith only [hunion, hcal]
  have hIoc_rm := spin_rhoMinus_Icc_le_of_slack (C₀ := C₀) hc40 hr₁_pos hr₁_lt hx₁_c0 hS h24_bd
  have hrpow_neg3 : n ^ (-3 : ℝ) ≤ n ^ (-(2 / 3 : ℝ)) * Real.log n := by
    have hlog1 : 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hn_pos]
      have hexp3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
      linarith only [hexp3, hn_ge39]
    have hp : n ^ (-3 : ℝ) ≤ n ^ (-(2 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn_ge1 (by norm_num)
    exact hp.trans (le_mul_of_one_le_right (Real.rpow_nonneg hn_pos.le _) hlog1)
  have hIoc_Q_ge : -(C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) ≤
      ∫ b in Ioc (0 : ℝ) (xiStar - r₁), Q b := by
    have h1 : ∫ b in Ioc (0 : ℝ) (xiStar - r₁), -Q b ≤
        ∫ b in Ioc (0 : ℝ) (xiStar - r₁), max (-Q b) 0 :=
      setIntegral_mono_on hQ_int.neg.integrableOn hQmax_int.integrableOn measurableSet_Ioc
        fun b _ => le_max_left _ _
    rw [integral_neg] at h1
    have h2 := mul_le_mul_of_nonneg_left hrpow_neg3 hCp.le
    linarith only [h1, hIoc_rm, h2]
  have hxs_m_pos : 0 < xiStar - r₁ := by linarith only [xiStar_pos, hr₁_lt]
  have hxs_m_le_p : xiStar - r₁ ≤ xiStar + r₁ := by linarith only [hr₁_pos]
  have h_hi_ext : 0 ≤ ∫ b in Ioi (xiStar + r₁), Q b := by
    refine setIntegral_nonneg measurableSet_Ioi fun b hb => ?_
    have hb_ge : x₁ ≤ b := by linarith only [mem_Ioi.mp hb, hx₁_hi]
    have hgb := spinGcal_re_nonneg_of_ge ha_pos.le hS.2.1 hS.1 hS.2.2.2.2 hb_ge
    exact mul_nonneg (mul_nonneg ha_pos.le (Real.exp_pos _).le) hgb
  have hsplit_top : ∫ b in Ioi (0 : ℝ), Q b =
      (∫ b in Ioc (0 : ℝ) (xiStar + r₁), Q b) + ∫ b in Ioi (xiStar + r₁), Q b := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      hQ_int.integrableOn hQ_int.integrableOn, Ioc_union_Ioi_eq_Ioi (by linarith only [xiStar_pos, hr₁_pos])]
  have hsplit_mid : ∫ b in Ioc (0 : ℝ) (xiStar + r₁), Q b =
      (∫ b in Ioc (0 : ℝ) (xiStar - r₁), Q b) + ∫ b in (xiStar - r₁)..(xiStar + r₁), Q b := by
    rw [intervalIntegral.integral_of_le hxs_m_le_p]
    have h1 : Ioc (0 : ℝ) (xiStar - r₁) ∪ Ioc (xiStar - r₁) (xiStar + r₁) = Ioc (0 : ℝ) (xiStar + r₁) :=
      Ioc_union_Ioc_eq_Ioc hxs_m_pos.le hxs_m_le_p
    have h2 := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl _)) measurableSet_Ioc
      (hQ_int.integrableOn (s := Ioc 0 (xiStar - r₁)))
      (hQ_int.integrableOn (s := Ioc (xiStar - r₁) (xiStar + r₁)))
    rwa [h1] at h2
  have hQ_win_le : ∫ b in (xiStar - r₁)..(xiStar + r₁), Q b ≤
      ((C₂₃ + 1) / 2 + C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
    linarith only [hhalf_int, hcal_23, hsplit_top, hsplit_mid, h_hi_ext, hIoc_Q_ge]
  have hjac := spinPtilde_jacobian_on hc40 hlo_gt h12 hhi_lt hS.2.1 hB_pos
  have h1_re : ∫ u in u_lo..u_hi, (spinPtilde c Φ (u : ℂ)).re =
      (spinCalNorm c Φ)⁻¹ * ∫ b in (xiStar - r₁)..(xiStar + r₁), Q b := by
    have h := hjac.2.2.1
    dsimp only at h
    rw [hbu_lo, hbu_hi] at h
    exact h
  have h_twice : ∫ u in u_lo..u_hi, (((2 : ℝ) : ℂ) * spinPtilde c Φ (u : ℂ)).re =
      2 * ∫ u in u_lo..u_hi, (spinPtilde c Φ (u : ℂ)).re := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [h_twice, h1_re]
  have hCnn : 0 ≤ (C₂₃ + 1) / 2 + C₂₄ + C_p := by linarith only [hC23, hC24, hCp]
  have h_le := mul_le_mul_of_nonneg_left hQ_win_le (inv_nonneg.mpr hB_pos.le)
  have h_le2 := mul_le_mul_of_nonneg_left h_le zero_le_two
  exact h_le2.trans_eq (by ring)

private lemma spin_line_band_piece {c R u_T ℓ : ℝ}
    {Φ : ℝ × ℝ → ℝ}
    (hR_pos : 0 < R) (hℓ_nn : 0 ≤ ℓ) (hnegRl_le_uT : -R + ℓ ≤ u_T) (huT_le1 : u_T ≤ -1)
    (hΨ_cont : ContinuousOn (fun v : ℝ => (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re)
      (Icc (-R) (R + ℓ)))
    (hΨ_nn : ∀ v ∈ Icc (-R) u_T, 0 ≤ (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re)
    (k : ℕ) :
    -(∫ v in (-R + ℓ)..u_T,
        (1 - (1 + (v - ℓ) / R) ^ (k + 1)) * (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re) -
      (∫ v in (-R)..(-R + ℓ), (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re) ≤
      -(63 / 100 : ℝ) * spinBandB1k c Φ R u_T k := by
  let P2 : ℝ → ℝ := fun v => (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re
  let W : ℝ → ℝ := fun v => (1 + (v - ℓ) / R) ^ (k + 1)
  have hW_cont : Continuous W :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have h_sub_Icc : ∀ {a b : ℝ}, -R ≤ a → b ≤ R + ℓ → Icc a b ⊆ Icc (-R) (R + ℓ) := Icc_subset_Icc
  have huT_le_R : u_T ≤ R + ℓ := by linarith only [huT_le1, hR_pos, hℓ_nn]
  have hi_P : ∀ a b, -R ≤ a → a ≤ b → b ≤ R + ℓ → IntervalIntegrable P2 volume a b :=
    fun a b ha hab hb => (hΨ_cont.mono (h_sub_Icc ha hb)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi_WP : ∀ a b, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v => (1 - W v) * P2 v) volume a b :=
    fun a b ha hab hb =>
      ((continuousOn_const.sub hW_cont.continuousOn).mul (hΨ_cont.mono (h_sub_Icc ha hb))).intervalIntegrable_of_Icc
        (μ := volume) hab
  have hi_B1k : ∀ a b, -R ≤ a → a ≤ b → b ≤ R + ℓ →
      IntervalIntegrable (fun v => min 1 (((k : ℝ) + 1) * (-v) / R) * P2 v) volume a b :=
    fun a b ha hab hb =>
      (((continuous_const.min ((continuous_const.mul continuous_neg).div_const R)).continuousOn).mul
        (hΨ_cont.mono (h_sub_Icc ha hb))).intervalIntegrable_of_Icc (μ := volume) hab
  have h_low_left : (63 / 100 : ℝ) * ∫ v in (-R)..(-R + ℓ), min 1 (((k : ℝ) + 1) * (-v) / R) * P2 v ≤
      ∫ v in (-R)..(-R + ℓ), P2 v := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith only [hℓ_nn])
      ((hi_B1k (-R) (-R + ℓ) le_rfl (by linarith only [hℓ_nn]) (by linarith only [hR_pos, hℓ_nn])).const_mul _)
      (hi_P (-R) (-R + ℓ) le_rfl (by linarith only [hℓ_nn]) (by linarith only [hR_pos, hℓ_nn])) fun v hv => ?_
    have hP_nn := hΨ_nn v ⟨hv.1, hv.2.trans hnegRl_le_uT⟩
    have hm1 : (63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R) ≤ 1 := by
      linarith only [min_le_left (1 : ℝ) (((k : ℝ) + 1) * (-v) / R)]
    calc (63 / 100 : ℝ) * (min 1 (((k : ℝ) + 1) * (-v) / R) * P2 v)
        = ((63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R)) * P2 v := by ring
      _ ≤ 1 * P2 v := mul_le_mul_of_nonneg_right hm1 hP_nn
      _ = P2 v := one_mul _
  have h_main_band : (63 / 100 : ℝ) * ∫ v in (-R + ℓ)..u_T, min 1 (((k : ℝ) + 1) * (-v) / R) * P2 v ≤
      ∫ v in (-R + ℓ)..u_T, (1 - W v) * P2 v := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hnegRl_le_uT
      ((hi_B1k (-R + ℓ) u_T (by linarith only [hℓ_nn]) hnegRl_le_uT huT_le_R).const_mul _)
      (hi_WP (-R + ℓ) u_T (by linarith only [hℓ_nn]) hnegRl_le_uT huT_le_R) fun v hv => ?_
    have hP_nn := hΨ_nn v ⟨by linarith only [hv.1, hℓ_nn], hv.2⟩
    have hbase_nn : 0 ≤ 1 + (v - ℓ) / R := by
      have hdiv_eq : 1 + (v - ℓ) / R = (R + (v - ℓ)) / R := by field_simp [hR_pos.ne']
      rw [hdiv_eq]
      exact div_nonneg (by linarith only [hv.1]) hR_pos.le
    have hbase_le : 1 + (v - ℓ) / R ≤ Real.exp (-(-v / R)) := by
      have hv_div : (v - ℓ) / R ≤ v / R := div_le_div_of_nonneg_right (by linarith only [hℓ_nn]) hR_pos.le
      have hexp1 : 1 + v / R ≤ Real.exp (v / R) := by linarith only [Real.add_one_le_exp (v / R)]
      rw [show -(-v / R) = v / R by ring]; linarith only [hv_div, hexp1]
    have hW_le : W v ≤ Real.exp (-(((k : ℝ) + 1) * (-v) / R)) := by
      dsimp [W]
      calc (1 + (v - ℓ) / R) ^ (k + 1)
          ≤ (Real.exp (-(-v / R))) ^ (k + 1) := pow_le_pow_left₀ hbase_nn hbase_le _
        _ = Real.exp (((k + 1 : ℕ) : ℝ) * (-(-v / R))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(((k : ℝ) + 1) * (-v) / R)) := by push_cast; ring_nf
    have h_min : (63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R) ≤ 1 - W v :=
      (sixtythree_hundredths_min_le_one_sub_exp
        (div_nonneg (mul_nonneg (by positivity) (by linarith only [hv.2, huT_le1])) hR_pos.le)).trans
        (sub_le_sub_left hW_le 1)
    calc (63 / 100 : ℝ) * (min 1 (((k : ℝ) + 1) * (-v) / R) * P2 v)
        = ((63 / 100 : ℝ) * min 1 (((k : ℝ) + 1) * (-v) / R)) * P2 v := by ring
      _ ≤ (1 - W v) * P2 v := mul_le_mul_of_nonneg_right h_min hP_nn
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi_B1k (-R) (-R + ℓ) le_rfl (by linarith only [hℓ_nn]) (by linarith only [hR_pos, hℓ_nn]))
    (hi_B1k (-R + ℓ) u_T (by linarith only [hℓ_nn]) hnegRl_le_uT huT_le_R)
  have hB1k : spinBandB1k c Φ R u_T k =
      (∫ v in (-R)..(-R + ℓ), min 1 (((k : ℝ) + 1) * (-v) / R) * P2 v) +
        (∫ v in (-R + ℓ)..u_T, min 1 (((k : ℝ) + 1) * (-v) / R) * P2 v) := by
    unfold spinBandB1k; exact hsplit.symm
  linarith only [h_low_left, h_main_band, hB1k]

private lemma spin_line_bound {c n R u_T u_lo u_hi R_dom C_env C_κ51 C₂ r_d cA ℓ η_vac : ℝ}
    {Φ : ℝ × ℝ → ℝ}
    (hc40 : 40 ≤ c) (hn_eq : n = c - 1) (hr_d : 0 < r_d) (hcA : 0 < cA) (hC_eq : C_env = 2 * C_κ51)
    (hCκ_pos : 0 < C_κ51)
    (hς_half : C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n ≤ 1 / 2)
    (hR_10 : 10 ≤ R) (hℓ_nn : 0 ≤ ℓ) (hℓ_half : ℓ ≤ 1 / 2)
    (hu_lo_le : u_lo ≤ -R) (hR_uhi : R + 1 ≤ u_hi)
    (hlo_ball : -r_d * n ^ (2 / 3 : ℝ) < u_lo) (hhi_ball : u_hi < r_d * n ^ (2 / 3 : ℝ))
    (huhi_cA : u_hi ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2)
    (huT_lo : -3.4 ≤ u_T) (huT_hi : u_T ≤ -1)
    (hRdom_ge4 : 4 ≤ R_dom) (hRdom_an : R_dom < r_d * n ^ (2 / 3 : ℝ))
    (hAn : AnalyticOnNhd ℂ (spinPtilde c Φ) (ball (0 : ℂ) (r_d * n ^ (2 / 3 : ℝ))))
    (hEnv : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2 → 0 < (u ^ (1 / 2 : ℂ)).re →
      ‖spinPtilde c Φ u‖ ≤ C_κ51 * spinAiryEnv u *
        Real.exp (C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * (u ^ (1 / 2 : ℂ)).re) /
          (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re))
    (hΨ_nn : ∀ v ∈ Icc u_lo u_T, 0 ≤ (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re)
    (hL1_dom : ∫ x in (-R_dom)..R_dom, ‖((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)‖ ≤ 1)
    (hWin : ∫ v in u_lo..u_hi, (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re ≤ η_vac)
    {k : ℕ} (hk5 : 5 ≤ k) (hkR : (k : ℝ) ≤ R / 5) :
    ∫ x in (-R)..R, (spinShiftedFun c Φ R ℓ k (x : ℂ)).re ≤
      -(63 / 100 : ℝ) * spinBandB1k c Φ R u_T k + η_vac +
        (4 * Real.exp (6 / 5) + 3 * C_env) * ((k : ℝ) + 1) / R := by
  subst hn_eq; subst hC_eq
  have hR_pos : 0 < R := by linarith only [hR_10]
  let P2 : ℝ → ℝ := fun v => (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re
  let P2_c : ℂ → ℂ := fun u => ((2 : ℝ) : ℂ) * spinPtilde c Φ u
  let W : ℝ → ℝ := fun v => (1 + (v - ℓ) / R) ^ (k + 1)
  have hAn2 : AnalyticOnNhd ℂ P2_c (ball (0 : ℂ) (r_d * (c - 1) ^ (2 / 3 : ℝ))) :=
    analyticOnNhd_const.mul hAn
  have hW_cont : Continuous W :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const R)).pow (k + 1)
  have hP2_cont_all : ContinuousOn P2 (Icc u_lo u_hi) := by
    refine Complex.continuous_re.comp_continuousOn (hAn2.continuousOn.comp continuous_ofReal.continuousOn
      fun v hv => ?_)
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨by linarith only [hlo_ball, hv.1], by linarith only [hhi_ball, hv.2]⟩
  have h_sub_all : ∀ {a b : ℝ}, u_lo ≤ a → b ≤ u_hi → Icc a b ⊆ Icc u_lo u_hi := Icc_subset_Icc
  have hi_P : ∀ a b, u_lo ≤ a → a ≤ b → b ≤ u_hi → IntervalIntegrable P2 volume a b :=
    fun a b ha hab hb => (hP2_cont_all.mono (h_sub_all ha hb)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi_WP : ∀ a b, u_lo ≤ a → a ≤ b → b ≤ u_hi →
      IntervalIntegrable (fun v => (1 - W v) * P2 v) volume a b :=
    fun a b ha hab hb =>
      ((continuousOn_const.sub hW_cont.continuousOn).mul (hP2_cont_all.mono (h_sub_all ha hb))).intervalIntegrable_of_Icc
        (μ := volume) hab
  have h_shift_eq : ∫ x in (-R)..R, (spinShiftedFun c Φ R ℓ k (x : ℂ)).re =
      ∫ v in (-R + ℓ)..(R + ℓ), W v * P2 v := by
    have hrew : (fun x : ℝ => (spinShiftedFun c Φ R ℓ k (x : ℂ)).re) =
        fun x : ℝ => (1 + x / R) ^ (k + 1) * P2 (x + ℓ) := by
      ext x; unfold spinShiftedFun P2
      have hreal_pow : ((1 + (x : ℂ) / (R : ℂ)) ^ (k + 1)) = (((1 + x / R) ^ (k + 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [mul_assoc, hreal_pow, show (x : ℂ) + (ℓ : ℂ) = ((x + ℓ : ℝ) : ℂ) by push_cast; ring]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_comm]
      ring_nf
    rw [hrew]
    simpa [W, add_sub_cancel_right] using
      intervalIntegral.integral_comp_add_right (fun v : ℝ => W v * P2 v) ℓ (a := -R) (b := R)
  have hnegRl_le_uT : -R + ℓ ≤ u_T := by linarith only [hR_10, hℓ_half, huT_lo]
  have h1_le_Rell : (1 : ℝ) ≤ R + ℓ := by linarith only [hR_10, hℓ_nn]
  have hRell_le_uhi : R + ℓ ≤ u_hi := by linarith only [hR_uhi, hℓ_half]
  have huT_le1 : u_T ≤ 1 := by linarith only [huT_hi]
  have h_split_W : ∫ v in (-R + ℓ)..(R + ℓ), W v * P2 v =
      (∫ v in u_lo..u_hi, P2 v) - (∫ v in u_lo..(-R), P2 v) +
      (-(∫ v in (-R + ℓ)..u_T, (1 - W v) * P2 v) - ∫ v in (-R)..(-R + ℓ), P2 v) -
      (∫ v in u_T..1, (1 - W v) * P2 v) - (∫ v in 1..(R + ℓ), (1 - W v) * P2 v) -
      (∫ v in (R + ℓ)..u_hi, P2 v) := by
    have h12 : IntervalIntegrable (fun v => W v * P2 v) volume (-R + ℓ) u_T :=
      (hW_cont.continuousOn.mul (hP2_cont_all.mono (h_sub_all (by linarith only [hu_lo_le, hℓ_nn])
        (huT_le1.trans (h1_le_Rell.trans hRell_le_uhi))))).intervalIntegrable_of_Icc (μ := volume) hnegRl_le_uT
    have h23 : IntervalIntegrable (fun v => W v * P2 v) volume u_T (R + ℓ) :=
      (hW_cont.continuousOn.mul (hP2_cont_all.mono (h_sub_all
        (by linarith only [hu_lo_le, hR_10, huT_lo]) hRell_le_uhi))).intervalIntegrable_of_Icc (μ := volume)
        (by linarith only [huT_hi, h1_le_Rell])
    have hw_split := intervalIntegral.integral_add_adjacent_intervals h12 h23
    have hsub1 : ∫ v in (-R + ℓ)..u_T, W v * P2 v =
        (∫ v in (-R + ℓ)..u_T, P2 v) - ∫ v in (-R + ℓ)..u_T, (1 - W v) * P2 v := by
      rw [← intervalIntegral.integral_sub
        (hi_P (-R + ℓ) u_T (by linarith only [hu_lo_le, hℓ_nn]) hnegRl_le_uT
          (huT_le1.trans (h1_le_Rell.trans hRell_le_uhi)))
        (hi_WP (-R + ℓ) u_T (by linarith only [hu_lo_le, hℓ_nn]) hnegRl_le_uT
          (huT_le1.trans (h1_le_Rell.trans hRell_le_uhi)))]
      exact intervalIntegral.integral_congr fun v _ => by ring
    have hsub2 : ∫ v in u_T..(R + ℓ), W v * P2 v =
        (∫ v in u_T..(R + ℓ), P2 v) -
        ((∫ v in u_T..1, (1 - W v) * P2 v) + ∫ v in 1..(R + ℓ), (1 - W v) * P2 v) := by
      have ha_mid := intervalIntegral.integral_add_adjacent_intervals
        (hi_WP u_T 1 (by linarith only [hu_lo_le, hR_10, huT_lo]) huT_le1 (h1_le_Rell.trans hRell_le_uhi))
        (hi_WP 1 (R + ℓ) (by linarith only [hu_lo_le, hR_10]) h1_le_Rell hRell_le_uhi)
      rw [ha_mid, ← intervalIntegral.integral_sub
        (hi_P u_T (R + ℓ) (by linarith only [hu_lo_le, hR_10, huT_lo])
          (huT_le1.trans h1_le_Rell) hRell_le_uhi)
        (hi_WP u_T (R + ℓ) (by linarith only [hu_lo_le, hR_10, huT_lo])
          (huT_le1.trans h1_le_Rell) hRell_le_uhi)]
      exact intervalIntegral.integral_congr fun v _ => by ring
    have hp_1 := intervalIntegral.integral_add_adjacent_intervals
      (hi_P u_lo (-R) le_rfl hu_lo_le (by linarith only [hR_pos, h1_le_Rell, hRell_le_uhi]))
      (hi_P (-R) (-R + ℓ) hu_lo_le (by linarith only [hℓ_nn]) (by linarith only [hR_10, hRell_le_uhi]))
    have hp_2 := intervalIntegral.integral_add_adjacent_intervals
      (hi_P u_lo (-R + ℓ) le_rfl (by linarith only [hu_lo_le, hℓ_nn]) (by linarith only [hR_10, hRell_le_uhi]))
      (hi_P (-R + ℓ) u_T (by linarith only [hu_lo_le, hℓ_nn]) hnegRl_le_uT (huT_le1.trans (h1_le_Rell.trans hRell_le_uhi)))
    have hp_3 := intervalIntegral.integral_add_adjacent_intervals
      (hi_P u_lo u_T le_rfl (by linarith only [hu_lo_le, hR_10, huT_lo]) (huT_le1.trans (h1_le_Rell.trans hRell_le_uhi)))
      (hi_P u_T (R + ℓ) (by linarith only [hu_lo_le, hR_10, huT_lo]) (huT_le1.trans h1_le_Rell) hRell_le_uhi)
    have hp_4 := intervalIntegral.integral_add_adjacent_intervals
      (hi_P u_lo (R + ℓ) le_rfl (by linarith only [hu_lo_le, hR_10, hℓ_nn]) hRell_le_uhi)
      (hi_P (R + ℓ) u_hi (by linarith only [hu_lo_le, hR_10, hℓ_nn]) hRell_le_uhi le_rfl)
    linarith only [hw_split, hsub1, hsub2, hp_1, hp_2, hp_3, hp_4]
  have h_left_nn : 0 ≤ ∫ v in u_lo..(-R), P2 v :=
    intervalIntegral.integral_nonneg hu_lo_le fun v hv => hΨ_nn v ⟨hv.1, hv.2.trans (by linarith only [hR_10, huT_lo])⟩
  have h_band_bd := spin_line_band_piece hR_pos hℓ_nn hnegRl_le_uT huT_hi
    (hP2_cont_all.mono (h_sub_all hu_lo_le hRell_le_uhi))
    (fun v hv => hΨ_nn v ⟨hu_lo_le.trans hv.1, hv.2⟩) k
  have h_mid_bd : -(∫ v in u_T..1, (1 - W v) * P2 v) ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by
    have hi1 := hi_WP u_T 1 (by linarith only [hu_lo_le, hR_10, huT_lo]) huT_le1 (h1_le_Rell.trans hRell_le_uhi)
    have hP2_norm_int1 : IntervalIntegrable (fun v : ℝ => ‖P2_c (v : ℂ)‖) volume u_T 1 :=
      (continuous_norm.comp_continuousOn (hAn2.continuousOn.comp continuous_ofReal.continuousOn fun v hv => by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact abs_lt.mpr ⟨by linarith only [hlo_ball, hu_lo_le, hR_10, huT_lo, hv.1],
          by linarith only [hhi_ball, hRell_le_uhi, h1_le_Rell, hv.2]⟩)).intervalIntegrable_of_Icc
        (μ := volume) huT_le1
    have h_abs : |∫ v in u_T..1, (1 - W v) * P2 v| ≤
        (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) * ∫ v in u_T..1, ‖P2_c (v : ℂ)‖ := by
      calc |∫ v in u_T..1, (1 - W v) * P2 v|
          ≤ ∫ v in u_T..1, |(1 - W v) * P2 v| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun v : ℝ => (1 - W v) * P2 v) (μ := volume) huT_le1
        _ ≤ ∫ v in u_T..1, (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) * ‖P2_c (v : ℂ)‖ := by
            refine intervalIntegral.integral_mono_on huT_le1 hi1.abs (hP2_norm_int1.const_mul _) fun v hv => ?_
            have hvl4 : |v - ℓ| ≤ 4 := abs_le.mpr ⟨by linarith only [huT_lo, hv.1, hℓ_half],
              by linarith only [hv.2, hℓ_nn]⟩
            have hpow := abs_one_add_pow_sub_one_le ((v - ℓ) / R) (k + 1)
            have h_abs_sub : |1 - W v| = |(1 + (v - ℓ) / R) ^ (k + 1) - 1| := by dsimp [W]; rw [abs_sub_comm]
            have h_exp_65 : ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| ≤ 6 / 5 := by
              rw [abs_div, abs_of_pos hR_pos]
              have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ R / 5 + 1 := by push_cast; linarith only [hkR]
              calc ((k + 1 : ℕ) : ℝ) * (|v - ℓ| / R) ≤ (R / 5 + 1) * (4 / R) := by gcongr
                _ = 4 / 5 + 4 / R := by field_simp [hR_pos.ne']
                _ ≤ 4 / 5 + 4 / 10 := by gcongr
                _ = 6 / 5 := by norm_num
            have hW_bd : |1 - W v| ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by
              rw [h_abs_sub]
              calc |(1 + (v - ℓ) / R) ^ (k + 1) - 1|
                  ≤ ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| * Real.exp (((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R|) := hpow
                _ ≤ ((k + 1 : ℕ) : ℝ) * (4 / R) * Real.exp (6 / 5) := by
                    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity))
                      (Real.exp_le_exp.mpr h_exp_65) (Real.exp_pos _).le (by positivity)
                    rw [abs_div, abs_of_pos hR_pos]; exact div_le_div_of_nonneg_right hvl4 hR_pos.le
                _ = 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by push_cast; ring
            calc |(1 - W v) * P2 v| = |1 - W v| * |P2 v| := abs_mul _ _
              _ ≤ (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) * ‖P2_c (v : ℂ)‖ :=
                  mul_le_mul hW_bd (Complex.abs_re_le_norm _) (abs_nonneg _) (by positivity)
        _ = (4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R) * ∫ v in u_T..1, ‖P2_c (v : ℂ)‖ :=
            intervalIntegral.integral_const_mul _ _
    have hL1_le1 : ∫ v in u_T..1, ‖P2_c (v : ℂ)‖ ≤ 1 := by
      have h_sub : ∫ v in u_T..1, ‖P2_c (v : ℂ)‖ ≤ ∫ x in (-R_dom)..R_dom, ‖P2_c (x : ℂ)‖ := by
        have h_cont_dom : ContinuousOn (fun v : ℝ => ‖P2_c (v : ℂ)‖) (Icc (-R_dom) R_dom) :=
          continuous_norm.comp_continuousOn (hAn2.continuousOn.comp continuous_ofReal.continuousOn fun v hv => by
            rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
            exact (abs_le.mpr hv).trans_lt hRdom_an)
        rw [intervalIntegral.integral_of_le huT_le1, intervalIntegral.integral_of_le (by linarith only [hRdom_ge4])]
        exact setIntegral_mono_set ((h_cont_dom.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self)
          (Eventually.of_forall fun _ => norm_nonneg _)
          (Eventually.of_forall (Ioc_subset_Ioc (by linarith only [huT_lo, hRdom_ge4]) (by linarith only [hRdom_ge4])))
      exact h_sub.trans hL1_dom
    have h_c_nn : 0 ≤ 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R := by positivity
    have h1 := (abs_le.mp h_abs).1
    nlinarith only [h1, hL1_le1, h_c_nn]
  have h_right_bd : -(∫ v in (1 : ℝ)..(R + ℓ), (1 - W v) * P2 v) ≤ 2 * C_κ51 * 2 * ((k : ℝ) + 1) / R := by
    have hi_r := hi_WP 1 (R + ℓ) (by linarith only [hu_lo_le, hR_10]) h1_le_Rell hRell_le_uhi
    let C_exp : ℝ := 2 * C_κ51 * ((k : ℝ) + 1) / R
    have hC_exp_nn : 0 ≤ C_exp := by dsimp [C_exp]; positivity
    have h_abs : |∫ v in (1 : ℝ)..(R + ℓ), (1 - W v) * P2 v| ≤
        ∫ v in (1 : ℝ)..(R + ℓ), C_exp * Real.exp (-(8 / 15 : ℝ) * v) := by
      calc |∫ v in (1 : ℝ)..(R + ℓ), (1 - W v) * P2 v|
          ≤ ∫ v in (1 : ℝ)..(R + ℓ), |(1 - W v) * P2 v| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun v : ℝ => (1 - W v) * P2 v) (μ := volume) h1_le_Rell
        _ ≤ ∫ v in (1 : ℝ)..(R + ℓ), C_exp * Real.exp (-(8 / 15 : ℝ) * v) := by
            refine intervalIntegral.integral_mono_on h1_le_Rell hi_r.abs
              ((continuous_const.mul (Real.continuous_exp.comp
                (continuous_const.mul continuous_id))).intervalIntegrable 1 (R + ℓ)) fun v hv => ?_
            have hv1 : 1 ≤ v := hv.1
            have hv_pos : 0 < v := by linarith only [hv1]
            have hvl : |v - ℓ| ≤ v := abs_le.mpr ⟨by linarith only [hv1, hℓ_half], by linarith only [hv.2, hℓ_nn]⟩
            have hpow := abs_one_add_pow_sub_one_le ((v - ℓ) / R) (k + 1)
            have h_abs_sub : |1 - W v| = |(1 + (v - ℓ) / R) ^ (k + 1) - 1| := by dsimp [W]; rw [abs_sub_comm]
            have h_exp_310 : ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| ≤ (3 / 10 : ℝ) * v := by
              rw [abs_div, abs_of_pos hR_pos]
              have hk1R : ((k + 1 : ℕ) : ℝ) / R ≤ 3 / 10 := by
                push_cast; rw [div_le_iff₀ hR_pos]; linarith only [hkR, hR_10]
              calc ((k + 1 : ℕ) : ℝ) * (|v - ℓ| / R) = (((k + 1 : ℕ) : ℝ) / R) * |v - ℓ| := by ring
                _ ≤ (3 / 10 : ℝ) * v := mul_le_mul hk1R hvl (abs_nonneg _) (by norm_num)
            have hW_bd : |1 - W v| ≤ (((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v) := by
              rw [h_abs_sub]
              calc |(1 + (v - ℓ) / R) ^ (k + 1) - 1|
                  ≤ ((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R| * Real.exp (((k + 1 : ℕ) : ℝ) * |(v - ℓ) / R|) := hpow
                _ ≤ (((k + 1 : ℕ) : ℝ) * (v / R)) * Real.exp ((3 / 10 : ℝ) * v) := by
                    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity))
                      (Real.exp_le_exp.mpr h_exp_310) (Real.exp_pos _).le (by positivity)
                    rw [abs_div, abs_of_pos hR_pos]; exact div_le_div_of_nonneg_right hvl hR_pos.le
                _ = (((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v) := by push_cast; ring
            have h_re_sqrt : ((v : ℂ) ^ (1 / 2 : ℂ)).re = √v := by
              rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hv_pos.le,
                Complex.ofReal_re, Real.sqrt_eq_rpow]
            have h_env_val : spinAiryEnv (v : ℂ) = Real.exp (-(4 / 3 : ℝ) * (v ^ (3 / 2 : ℝ))) := by
              unfold spinAiryEnv
              rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hv_pos.le,
                Complex.ofReal_re]
            have h_bd := hEnv (v : ℂ) (Complex.ofReal_ne_zero.mpr hv_pos.ne')
              (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos]
                  exact hv.2.trans (hRell_le_uhi.trans huhi_cA))
              (by rw [h_re_sqrt]; exact Real.sqrt_pos.mpr hv_pos)
            have hP2_bd : |P2 v| ≤
                2 * C_κ51 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) * √v) * v⁻¹ := by
              have h_norm_den : √‖(v : ℂ)‖ * ((v : ℂ) ^ (1 / 2 : ℂ)).re = v := by
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv_pos, h_re_sqrt, Real.mul_self_sqrt hv_pos.le]
              have h_p2 : P2 v = 2 * (spinPtilde c Φ (v : ℂ)).re := by
                dsimp [P2]; simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
              have h_bd' : ‖spinPtilde c Φ (v : ℂ)‖ ≤
                  C_κ51 * spinAiryEnv (v : ℂ) * Real.exp (C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) * √v) / v := by
                have htmp := h_bd
                rw [h_norm_den, h_re_sqrt] at htmp
                exact htmp
              calc |P2 v| = 2 * |(spinPtilde c Φ (v : ℂ)).re| := by rw [h_p2, abs_mul, abs_of_pos two_pos]
                _ ≤ 2 * ‖spinPtilde c Φ (v : ℂ)‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) two_pos.le
                _ ≤ 2 * (C_κ51 * spinAiryEnv (v : ℂ) * Real.exp (C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) * √v) / v) :=
                    mul_le_mul_of_nonneg_left h_bd' two_pos.le
                _ = 2 * C_κ51 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) * √v) * v⁻¹ := by
                    rw [h_env_val, div_eq_mul_inv, mul_assoc C_κ51, ← Real.exp_add]; ring
            have hv32 : v ≤ v ^ (3 / 2 : ℝ) := by
              conv_lhs => rw [← Real.rpow_one v]
              exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
            have hsqrt_le : √v ≤ v := by
              rw [Real.sqrt_eq_rpow]
              conv_rhs => rw [← Real.rpow_one v]
              exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
            have hexp_sum : -(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) * √v + (3 / 10 : ℝ) * v ≤
                -(8 / 15 : ℝ) * v := by
              have hsqrt_nn : 0 ≤ √v := Real.sqrt_nonneg v
              nlinarith only [hv32, hsqrt_le, hς_half, hv1, hsqrt_nn]
            have hexp_prod : Real.exp ((3 / 10 : ℝ) * v) *
                  Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) * √v) =
                Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) * √v + (3 / 10 : ℝ) * v) := by
              rw [← Real.exp_add]; ring_nf
            calc |(1 - W v) * P2 v| = |1 - W v| * |P2 v| := abs_mul _ _
              _ ≤ ((((k : ℝ) + 1) / R) * v * Real.exp ((3 / 10 : ℝ) * v)) *
                    (2 * C_κ51 * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) * √v) * v⁻¹) :=
                  mul_le_mul hW_bd hP2_bd (abs_nonneg _) (by positivity)
              _ = C_exp * (Real.exp ((3 / 10 : ℝ) * v) *
                    Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) * √v)) * (v * v⁻¹) := by
                  dsimp [C_exp]; ring
              _ = C_exp * Real.exp (-(4 / 3 : ℝ) * v ^ (3 / 2 : ℝ) + C₂ * (c - 1) ^ (-(1 / 3 : ℝ)) * Real.log (c - 1) * √v + (3 / 10 : ℝ) * v) := by
                  rw [hexp_prod, mul_inv_cancel₀ hv_pos.ne', mul_one]
              _ ≤ C_exp * Real.exp (-(8 / 15 : ℝ) * v) :=
                  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_sum) hC_exp_nn
    have h_ftc_r : ∫ v in (1 : ℝ)..(R + ℓ), C_exp * Real.exp (-(8 / 15 : ℝ) * v) ≤ 2 * C_exp := by
      have hderiv : ∀ v ∈ Set.uIcc 1 (R + ℓ),
          HasDerivAt (fun t : ℝ => -((15 / 8 : ℝ) * C_exp) * Real.exp (-(8 / 15 : ℝ) * t))
            (C_exp * Real.exp (-(8 / 15 : ℝ) * v)) v := fun v _ => by
        have h1 : HasDerivAt (fun t : ℝ => -(8 / 15 : ℝ) * t) (-(8 / 15 : ℝ)) v := by
          simpa using (hasDerivAt_id v).const_mul (-(8 / 15 : ℝ))
        exact (h1.exp.const_mul (-((15 / 8 : ℝ) * C_exp))).congr_deriv (by ring)
      have h_eq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable 1 (R + ℓ))
      have hR_nn : 0 ≤ ((15 / 8 : ℝ) * C_exp) * Real.exp (-(8 / 15 : ℝ) * (R + ℓ)) := by positivity
      have h1_le : Real.exp (-(8 / 15 : ℝ) * 1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      nlinarith only [h_eq, hR_nn, h1_le, hC_exp_nn]
    have h1 := (abs_le.mp h_abs).1
    have h2 : 2 * C_exp = 2 * C_κ51 * 2 * ((k : ℝ) + 1) / R := by dsimp [C_exp]; ring
    linarith only [h1, h_ftc_r, h2]
  have h_tail_bd : -(∫ v in (R + ℓ)..u_hi, P2 v) ≤ 2 * C_κ51 * ((k : ℝ) + 1) / R := by
    have ht := spinPtilde_tail_le_of_env hc40 hCκ_pos hr_d hcA h1_le_Rell hRell_le_uhi hhi_ball huhi_cA
      hς_half hAn hEnv
    have h_norm_int : |∫ v in (R + ℓ)..u_hi, P2 v| ≤
        2 * ∫ v in (R + ℓ)..u_hi, ‖spinPtilde c Φ (v : ℂ)‖ := by
      have hi_p : IntervalIntegrable (fun v => ‖spinPtilde c Φ (v : ℂ)‖) volume (R + ℓ) u_hi :=
        (continuous_norm.comp_continuousOn (hAn.continuousOn.comp continuous_ofReal.continuousOn fun v hv => by
          rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact abs_lt.mpr ⟨by linarith only [hlo_ball, hu_lo_le, hR_10, h1_le_Rell, hv.1],
            by linarith only [hhi_ball, hv.2]⟩)).intervalIntegrable_of_Icc (μ := volume) hRell_le_uhi
      have hre2 : ∫ v in (R + ℓ)..u_hi, P2 v = 2 * ∫ v in (R + ℓ)..u_hi, (spinPtilde c Φ (v : ℂ)).re := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun v _ => ?_
        dsimp [P2]; simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      rw [hre2, abs_mul, abs_of_pos two_pos]
      refine mul_le_mul_of_nonneg_left ?_ zero_le_two
      calc |∫ v in (R + ℓ)..u_hi, (spinPtilde c Φ (v : ℂ)).re|
          ≤ ∫ v in (R + ℓ)..u_hi, |(spinPtilde c Φ (v : ℂ)).re| := by
            simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
              (f := fun v : ℝ => (spinPtilde c Φ (v : ℂ)).re) (μ := volume) hRell_le_uhi
        _ ≤ ∫ v in (R + ℓ)..u_hi, ‖spinPtilde c Φ (v : ℂ)‖ := by
            refine intervalIntegral.integral_mono_on hRell_le_uhi
              ((Complex.continuous_re.comp_continuousOn (hAn.continuousOn.comp continuous_ofReal.continuousOn
                fun v hv => by
                  rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
                  exact abs_lt.mpr ⟨by linarith only [hlo_ball, hu_lo_le, hR_10, h1_le_Rell, hv.1],
                    by linarith only [hhi_ball, hv.2]⟩)).abs.intervalIntegrable_of_Icc (μ := volume) hRell_le_uhi)
              hi_p fun v _ => Complex.abs_re_le_norm _
    have hexp_mon : Real.exp (-(5 / 6 : ℝ) * (R + ℓ)) ≤ Real.exp (-(5 / 6 : ℝ) * R) :=
      Real.exp_le_exp.mpr (by linarith only [hℓ_nn])
    have h_xe : (5 / 6 : ℝ) * R * Real.exp (-(5 / 6 : ℝ) * R) ≤ 1 := by
      have := Real.add_one_le_exp ((5 / 6 : ℝ) * R)
      rw [show -(5 / 6 : ℝ) * R = -((5 / 6 : ℝ) * R) by ring, Real.exp_neg,
        mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith only [this]
    have h_exp_R : Real.exp (-(5 / 6 : ℝ) * R) ≤ (6 / 5 : ℝ) / R := by
      rw [le_div_iff₀ hR_pos]; linarith only [h_xe]
    have hk6 : (6 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (by omega : 6 ≤ k + 1)
    have h1 := (abs_le.mp h_norm_int).1
    have h2 : 2 * ((6 / 5 : ℝ) * C_κ51 * Real.exp (-(5 / 6 : ℝ) * (R + ℓ))) ≤
        2 * C_κ51 * ((k : ℝ) + 1) / R := by
      calc 2 * ((6 / 5 : ℝ) * C_κ51 * Real.exp (-(5 / 6 : ℝ) * (R + ℓ)))
          ≤ 2 * ((6 / 5 : ℝ) * C_κ51 * Real.exp (-(5 / 6 : ℝ) * R)) := by gcongr
        _ ≤ 2 * ((6 / 5 : ℝ) * C_κ51 * ((6 / 5 : ℝ) / R)) := by gcongr
        _ = (72 / 25 : ℝ) * C_κ51 / R := by ring
        _ ≤ (2 * C_κ51 * 6) / R := div_le_div_of_nonneg_right (by linarith only [hCκ_pos]) hR_pos.le
        _ ≤ 2 * C_κ51 * ((k : ℝ) + 1) / R := by gcongr
    nlinarith only [h1, ht, h2]
  have h_sum_c : 4 * Real.exp (6 / 5) * ((k : ℝ) + 1) / R +
      2 * C_κ51 * 2 * ((k : ℝ) + 1) / R + 2 * C_κ51 * ((k : ℝ) + 1) / R =
      (4 * Real.exp (6 / 5) + 3 * (2 * C_κ51)) * ((k : ℝ) + 1) / R := by ring
  linarith only [h_shift_eq, h_split_W, hWin, h_left_nn, h_band_bd, h_mid_bd, h_right_bd, h_tail_bd, h_sum_c]

end WindowAndLine

section NodesAndBootstrap

private lemma spin_p2_real_mv_sub {c R_dom : ℝ} {Φ : ℝ × ℝ → ℝ}
    (hΨ_an : AnalyticOnNhd ℂ (fun u => ((2 : ℝ) : ℂ) * spinPtilde c Φ u) (closedBall (0 : ℂ) R_dom))
    {a b : ℝ} (hab : a ≤ b) (ha : -R_dom ≤ a) (hb : b ≤ R_dom) (C₁ : ℝ)
    (hder : ∀ x ∈ Icc a b, ‖deriv (fun u => ((2 : ℝ) : ℂ) * spinPtilde c Φ u) (x : ℂ)‖ ≤ C₁) :
    |(((2 : ℝ) : ℂ) * spinPtilde c Φ (b : ℂ)).re -
        (((2 : ℝ) : ℂ) * spinPtilde c Φ (a : ℂ)).re| ≤ C₁ * (b - a) := by
  let P2_c : ℂ → ℂ := fun u => ((2 : ℝ) : ℂ) * spinPtilde c Φ u
  have hΨ_diff : ∀ t ∈ Icc a b, HasDerivAt (fun x : ℝ => (P2_c (x : ℂ)).re) ((deriv P2_c (t : ℂ)).re) t := by
    intro t ht
    have ht_ball : (t : ℂ) ∈ closedBall (0 : ℂ) R_dom := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith only [ha, ht.1], by linarith only [ht.2, hb]⟩
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hΨ_an (t : ℂ) ht_ball).differentiableAt.hasDerivAt).comp_ofReal
  have hcont_der : ContinuousOn (fun t : ℝ => (deriv P2_c (t : ℂ)).re) (Icc a b) := by
    refine Complex.continuous_re.comp_continuousOn (hΨ_an.deriv.continuousOn.comp continuous_ofReal.continuousOn
      fun t ht => ?_)
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith only [ha, ht.1], by linarith only [ht.2, hb]⟩
  have hftc : (P2_c (b : ℂ)).re - (P2_c (a : ℂ)).re = ∫ t in a..b, (deriv P2_c (t : ℂ)).re :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hΨ_diff t (Set.uIcc_of_le hab ▸ ht))
      (hcont_der.intervalIntegrable_of_Icc (μ := volume) hab)).symm
  have h_norm := intervalIntegral.norm_integral_le_integral_norm
    (f := fun t : ℝ => (deriv P2_c (t : ℂ)).re) (μ := volume) hab
  rw [← hftc, Real.norm_eq_abs] at h_norm
  have hint_bd : ∫ t in a..b, ‖(deriv P2_c (t : ℂ)).re‖ ≤ ∫ _ in a..b, C₁ := by
    refine intervalIntegral.integral_mono_on hab
      ((continuous_norm.comp_continuousOn hcont_der).intervalIntegrable_of_Icc (μ := volume) hab)
      intervalIntegrable_const fun t ht => (Complex.abs_re_le_norm _).trans (hder t ht)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint_bd
  have hle : |(P2_c (b : ℂ)).re - (P2_c (a : ℂ)).re| ≤ (b - a) * C₁ := h_norm.trans hint_bd
  linarith only [hle]

private lemma spin_pnodes_lb_and_theta {c n R u_T r_d_dom : ℝ} {N : ℕ}
    {Φ : ℝ × ℝ → ℝ}
    (hn_pos : 0 < n) (hR_96 : 96 ≤ R)
    (hR_dom_ball : |airyZero 1| + 1 < r_d_dom)
    (hAn : AnalyticOnNhd ℂ (spinPtilde c Φ) (ball (0 : ℂ) r_d_dom))
    (ha1_lt_uT : airyZero 1 < u_T)
    (hΨ_nn_all : ∀ x ∈ Icc (-R) u_T, 0 ≤ (((2 : ℝ) : ℂ) * spinPtilde c Φ (x : ℂ)).re)
    (hB2 : QuantC1B2Holds (fun u => ((2 : ℝ) : ℂ) * spinPtilde c Φ u) u_T)
    (hN : ∀ m : ℕ, 1 ≤ m → (m ≤ N ↔ -airyZero m < R))
    (P : BootstrapParams)
    (hP_C1 : P.C_1 = quantC1C1) (hP_w : P.w_star = quantC1WStar)
    (hP_κ : P.κ_star = quantC1KappaStar) (hP_δ : P.δ_star = quantC1DeltaStar)
    (hP_η : P.η_0 = quantC1Eta0) (_hP_k0 : P.k_0 = 5) :
    (∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
      ℓ ∈ Icc (P.D_1 * n ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      -tebLambdaN P 0 * ℓ - P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤ spinPNodes c Φ R ℓ k N) ∧
    (∀ k : ℕ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
      tebThetaHB P 0 * (u_T - airyZero 1) ∈
        Icc (P.D_1 * n ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      (P.κ_star / (4 * P.w_star)) * (u_T - airyZero 1) - P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤
        spinPNodes c Φ R (tebThetaHB P 0 * (u_T - airyZero 1)) k N) := by
  let P2_c : ℂ → ℂ := fun u => ((2 : ℝ) : ℂ) * spinPtilde c Φ u
  have hR_pos : 0 < R := by linarith only [hR_96]
  obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
  obtain ⟨_ha2_lo, ha2_hi⟩ := airyZero_two
  have hbase_nn : 0 ≤ 1 + airyZero 1 / R := by
    have hdiv_eq : 1 + airyZero 1 / R = (R + airyZero 1) / R := by field_simp [hR_pos.ne']
    rw [hdiv_eq]
    exact div_nonneg (by linarith only [hR_96, ha1_lo]) hR_pos.le
  have hbase_le1 : 1 + airyZero 1 / R ≤ 1 := by
    have : airyZero 1 / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith only [ha1_hi]) hR_pos.le
    linarith only [this]
  have hΨ_an_R : AnalyticOnNhd ℂ P2_c (closedBall (0 : ℂ) (|airyZero 1| + 1)) :=
    (analyticOnNhd_const.mul hAn).mono (closedBall_subset_ball hR_dom_ball)
  have hΨ_a1_nn : 0 ≤ (P2_c (airyZero 1 : ℂ)).re :=
    hΨ_nn_all (airyZero 1) ⟨by linarith only [hR_96, ha1_lo], ha1_lt_uT.le⟩
  have h_lower_aux : ∀ {ℓ : ℝ} (k : ℕ), 0 ≤ ℓ → ℓ ≤ min quantC1DeltaStar (min quantC1Eta0 1) →
      (1 + airyZero 1 / R) ^ (k + 1) * (P2_c ((airyZero 1 + ℓ : ℝ) : ℂ)).re / quantC1WStar ≤
        spinPNodes c Φ R ℓ k N := by
    intro ℓ k hℓ_nn hℓ_le
    have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨le_rfl, (hN 1 le_rfl).mpr (by linarith only [hR_96, ha1_lo])⟩
    have h_sum_split : spinPNodes c Φ R ℓ k N =
        (spinShiftedFun c Φ R ℓ k (airyZero 1 : ℂ)).re / airyAi' (airyZero 1) ^ 2 +
        ∑ m ∈ (Finset.Icc 1 N).erase 1,
          (spinShiftedFun c Φ R ℓ k (airyZero m : ℂ)).re / airyAi' (airyZero m) ^ 2 := by
      unfold spinPNodes; exact (Finset.add_sum_erase _ _ h1_mem).symm
    have h_tail_nn : 0 ≤ ∑ m ∈ (Finset.Icc 1 N).erase 1,
        (spinShiftedFun c Φ R ℓ k (airyZero m : ℂ)).re / airyAi' (airyZero m) ^ 2 := by
      refine Finset.sum_nonneg fun m hm => ?_
      rw [Finset.mem_erase, Finset.mem_Icc] at hm
      have hm2 : 2 ≤ m := by omega
      have ham_negR : -R < airyZero m := by have := (hN m hm.2.1).mp hm.2.2; linarith only [this]
      have ham_le_a2 : airyZero m ≤ airyZero 2 := airyZero_anti (by omega) hm2
      have hℓ_half : ℓ ≤ 1 / 2 := hℓ_le.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
      have hΨ_nn := hΨ_nn_all (airyZero m + ℓ)
        ⟨by linarith only [ham_negR, hℓ_nn], by linarith only [ham_le_a2, ha2_hi, ha1_lo, ha1_lt_uT, hℓ_half]⟩
      have hpow_nn : 0 ≤ (1 + airyZero m / R) ^ (k + 1) := by
        refine pow_nonneg ?_ _
        have hdiv_m : 1 + airyZero m / R = (R + airyZero m) / R := by field_simp [hR_pos.ne']
        rw [hdiv_m]
        exact div_nonneg (by linarith only [ham_negR]) hR_pos.le
      have hrew : (spinShiftedFun c Φ R ℓ k (airyZero m : ℂ)).re =
          (1 + airyZero m / R) ^ (k + 1) * (P2_c ((airyZero m + ℓ : ℝ) : ℂ)).re := by
        unfold spinShiftedFun P2_c
        have h1 : ((1 + (airyZero m : ℂ) / (R : ℂ)) ^ (k + 1)) =
            (((1 + airyZero m / R) ^ (k + 1) : ℝ) : ℂ) := by push_cast; ring
        rw [mul_assoc, h1, show (airyZero m : ℂ) + (ℓ : ℂ) = ((airyZero m + ℓ : ℝ) : ℂ) by push_cast; ring]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hrew]; exact div_nonneg (mul_nonneg hpow_nn hΨ_nn) (sq_nonneg _)
    have h1_rew : (spinShiftedFun c Φ R ℓ k (airyZero 1 : ℂ)).re / airyAi' (airyZero 1) ^ 2 =
        (1 + airyZero 1 / R) ^ (k + 1) * (P2_c ((airyZero 1 + ℓ : ℝ) : ℂ)).re / quantC1WStar := by
      unfold spinShiftedFun quantC1WStar P2_c
      have h1 : ((1 + (airyZero 1 : ℂ) / (R : ℂ)) ^ (k + 1)) =
          (((1 + airyZero 1 / R) ^ (k + 1) : ℝ) : ℂ) := by push_cast; ring
      rw [mul_assoc, h1, show (airyZero 1 : ℂ) + (ℓ : ℂ) = ((airyZero 1 + ℓ : ℝ) : ℂ) by push_cast; ring]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    linarith only [h_sum_split, h_tail_nn, h1_rew]
  refine ⟨?_, ?_⟩
  · intro k ℓ _ _ hℓ_mem
    have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hn_pos.le _)).trans hℓ_mem.1
    have hℓ_le' : ℓ ≤ min quantC1DeltaStar (min quantC1Eta0 1) := by simpa only [hP_δ, hP_η] using hℓ_mem.2
    have hℓ_δ : ℓ ≤ quantC1DeltaStar := hℓ_le'.trans (min_le_left _ _)
    have h_mv := spin_p2_real_mv_sub hΨ_an_R (a := airyZero 1) (b := airyZero 1 + ℓ)
      (by linarith only [hℓ_nn])
      (by linarith only [neg_abs_le (airyZero 1)])
      (by linarith only [le_abs_self (airyZero 1), hℓ_δ, quantC1DeltaStar_le])
      quantC1C1 fun x hx => (hB2.2 x ⟨by linarith only [hx.1, quantC1DeltaStar_pos], by linarith only [hx.2, hℓ_δ]⟩).1
    have hΨ_lb : -quantC1C1 * ℓ ≤ (P2_c ((airyZero 1 + ℓ : ℝ) : ℂ)).re := by
      have h1 := (abs_le.mp h_mv).1; linarith only [h1, hΨ_a1_nn]
    have hpow_le1 : (1 + airyZero 1 / R) ^ (k + 1) ≤ 1 := pow_le_one₀ hbase_nn hbase_le1
    have hw_pos : 0 < quantC1WStar := quantC1WStar_pos
    have hterm_lb : -(quantC1C1 / quantC1WStar) * ℓ ≤
        (1 + airyZero 1 / R) ^ (k + 1) * (P2_c ((airyZero 1 + ℓ : ℝ) : ℂ)).re / quantC1WStar := by
      have hmul : (1 + airyZero 1 / R) ^ (k + 1) * (-quantC1C1 * ℓ) ≤
          (1 + airyZero 1 / R) ^ (k + 1) * (P2_c ((airyZero 1 + ℓ : ℝ) : ℂ)).re :=
        mul_le_mul_of_nonneg_left hΨ_lb (pow_nonneg hbase_nn _)
      have h2 : -(quantC1C1 * ℓ) ≤ (1 + airyZero 1 / R) ^ (k + 1) * (-quantC1C1 * ℓ) := by
        have h3 : 0 ≤ quantC1C1 * ℓ := mul_nonneg quantC1C1_pos.le hℓ_nn
        nlinarith only [hpow_le1, h3]
      rw [← show -(quantC1C1 * ℓ) / quantC1WStar = -(quantC1C1 / quantC1WStar) * ℓ by ring]
      exact div_le_div_of_nonneg_right (h2.trans hmul) hw_pos.le
    have hΛ_ge : quantC1C1 / quantC1WStar ≤ tebLambdaN P 0 := by
      unfold tebLambdaN; rw [hP_C1, hP_w, add_zero]
      have : 0 ≤ quantC1C1 / quantC1WStar := div_nonneg quantC1C1_pos.le hw_pos.le
      linarith only [this, show 2 * quantC1C1 * (1 / quantC1WStar) = 2 * (quantC1C1 / quantC1WStar) by ring]
    have h_main := h_lower_aux k hℓ_nn hℓ_le'
    have hΛ_mul : -tebLambdaN P 0 * ℓ ≤ -(quantC1C1 / quantC1WStar) * ℓ := by nlinarith only [hΛ_ge, hℓ_nn]
    linarith only [hΛ_mul, hterm_lb, h_main, show P.C_α * R ^ (3 / 2 : ℝ) * 0 = 0 by ring]
  · intro k _ hkR hℓ_mem
    set θ := tebThetaHB P 0
    have hθ_pos : 0 < θ := tebThetaHB_pos P le_rfl
    have hθ_half : θ ≤ 1 / 2 := tebThetaHB_le_half P 0
    have hθ_le1 : θ ≤ 1 := hθ_half.trans (by norm_num)
    have hℓ_nn : 0 ≤ θ * (u_T - airyZero 1) :=
      (mul_nonneg P.hD1 (Real.rpow_nonneg hn_pos.le _)).trans hℓ_mem.1
    have hℓ_le' : θ * (u_T - airyZero 1) ≤ min quantC1DeltaStar (min quantC1Eta0 1) := by
      simpa only [hP_δ, hP_η] using hℓ_mem.2
    have hsec := quantC1B2_secant_lower le_rfl hΨ_an_R ha1_lt_uT
      (hΨ_nn_all u_T ⟨by linarith only [hR_96, ha1_lo, ha1_lt_uT], le_rfl⟩) hB2 hθ_pos.le hθ_le1
    have h_psi_lb : quantC1KappaStar * (u_T - airyZero 1) ≤
        (P2_c ((airyZero 1 + θ * (u_T - airyZero 1) : ℝ) : ℂ)).re := by
      have hk := quantC1KappaStar_pos.le
      have hx : 0 ≤ u_T - airyZero 1 := by linarith only [ha1_lt_uT]
      have h1 : quantC1KappaStar * (u_T - airyZero 1) ≤ 2 * quantC1KappaStar * (1 - θ) * (u_T - airyZero 1) := by
        have h12 : (1 : ℝ) ≤ 2 * (1 - θ) := by linarith only [hθ_half]
        have hmul := mul_le_mul_of_nonneg_left h12 (mul_nonneg hk hx)
        linarith only [hmul]
      exact h1.trans hsec
    have h_pow_lb : (1 / 2 : ℝ) ≤ (1 + airyZero 1 / R) ^ (k + 1) := by
      have h_ge_m1 : -1 ≤ airyZero 1 / R := by
        rw [le_div_iff₀ hR_pos]; linarith only [hR_96, ha1_lo]
      have h_bern := one_add_mul_le_pow (by linarith only [h_ge_m1] : -2 ≤ airyZero 1 / R) (k + 1)
      have h_lin : 1 / 2 ≤ 1 + ((k + 1 : ℕ) : ℝ) * (airyZero 1 / R) := by
        have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ R / 5 + 1 := by push_cast; linarith only [hkR]
        have h_a1_neg : 0 ≤ -airyZero 1 / R := div_nonneg (by linarith only [ha1_hi]) hR_pos.le
        have h_div_le : -airyZero 1 / R ≤ 2.35 / R :=
          div_le_div_of_nonneg_right (by linarith only [ha1_lo]) hR_pos.le
        have h_prod_le : ((k + 1 : ℕ) : ℝ) * (-airyZero 1 / R) ≤ (R / 5 + 1) * (2.35 / R) :=
          mul_le_mul hk1_le h_div_le h_a1_neg (by positivity [hR_pos])
        have h_R_simp : (R / 5 + 1) * (2.35 / R) = (1 / 5 + 1 / R) * 2.35 := by field_simp [hR_pos.ne']
        have h_1R : 1 / R ≤ 1 / 96 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hR_96
        have h_neg_eq : ((k + 1 : ℕ) : ℝ) * (-airyZero 1 / R) = -(((k + 1 : ℕ) : ℝ) * (airyZero 1 / R)) := by ring
        linarith only [h_neg_eq, h_prod_le, h_R_simp, h_1R]
      exact h_lin.trans h_bern
    have hterm_lb : (P.κ_star / (4 * P.w_star)) * (u_T - airyZero 1) ≤
        (1 + airyZero 1 / R) ^ (k + 1) *
          (P2_c ((airyZero 1 + θ * (u_T - airyZero 1) : ℝ) : ℂ)).re / quantC1WStar := by
      rw [hP_κ, hP_w]
      have hkn : 0 ≤ quantC1KappaStar * (u_T - airyZero 1) :=
        mul_nonneg quantC1KappaStar_pos.le (by linarith only [ha1_lt_uT])
      have h1 := mul_le_mul h_pow_lb h_psi_lb hkn (pow_nonneg hbase_nn _)
      have h2 : (quantC1KappaStar / (4 * quantC1WStar)) * (u_T - airyZero 1) ≤
          ((1 / 2 : ℝ) * (quantC1KappaStar * (u_T - airyZero 1))) / quantC1WStar := by
        have hw := quantC1WStar_pos
        rw [show ((1 / 2 : ℝ) * (quantC1KappaStar * (u_T - airyZero 1))) / quantC1WStar =
          (quantC1KappaStar / (2 * quantC1WStar)) * (u_T - airyZero 1) by ring]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left quantC1KappaStar_pos.le (mul_pos two_pos hw) (by linarith only [hw]))
          (by linarith only [ha1_lt_uT])
      exact h2.trans (div_le_div_of_nonneg_right h1 quantC1WStar_pos.le)
    have h_main := h_lower_aux k hℓ_nn hℓ_le'
    linarith only [hterm_lb, h_main, show P.C_α * R ^ (3 / 2 : ℝ) * 0 = 0 by ring]

/-- **Section 6.1 weak two-edge bootstrap shrinkage bound**:
for any `C₀ > 0`, sufficiently large `c`, `|x₁ - ξ_*| ≤ C₀ n^{-2/3}`, `a₁ < u_T ≤ |a₁| + 1`,
`b(u_T) = x₁`, and `SpinSlackHyp c x₁ Φ`, we have `n^{1/3} (u_T - a₁) ≤ C_loc log n`. -/
theorem spinS4_6_1_shrink_bound {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ (C_loc c_thr : ℝ), 0 < C_loc ∧ 40 ≤ c_thr ∧
      ∀ {c x₁ u_T : ℝ}, c_thr ≤ c →
        let n := c - 1
        |x₁ - xiStar| ≤ C₀ * n ^ (-(2 / 3 : ℝ)) →
        airyZero 1 < u_T → u_T ≤ |airyZero 1| + 1 →
        (virasoroBChart n (u_T : ℂ)).re = x₁ →
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinSlackHyp c x₁ Φ →
          n ^ (1 / 3 : ℝ) * (u_T - airyZero 1) ≤ C_loc * Real.log n := by
  obtain ⟨r₁, c₀, C_κ51, C₂, r_d, cA, _C_dl, κ_obs,
    hr₁_pos, hr₁_half, hlo, hhi, _hc₀_40, hCκ_pos, hC2_pos, hrd_pos, _hcA_pos, _hCdl_pos, hκ_pos,
    hr_d_eq, hcA_eq, hdisc⟩ := spinPtilde_quant_c1 hC₀
  have hr₁_lt : r₁ < xiStar := hr₁_half.trans (half_lt_self xiStar_pos)
  obtain ⟨_cσ, C₂₃, c₀_23, _, hC23_pos, hc0_23, h23⟩ := spinS4_2_3 (C_x := C₀)
  obtain ⟨C₂₄, C_p, c₀_24, hC24_pos, hCp_pos, hc0_24, h24⟩ :=
    spinS4_2_4 (C_x := C₀) (p := 3) (r₀ := r₁) (by norm_num) hr₁_pos hr₁_lt
  have hbv_pos : 0 < virasoroBV ^ 2 := sq_pos_of_pos virasoroBV_pos
  have hac_eq : virasoroAC 1 ^ 2 = 2 * virasoroBV ^ 2 := by
    rw [virasoroAC_sq 1 zero_le_one, Real.one_rpow, mul_one]
  have hbv_le_ac : virasoroBV ^ 2 ≤ virasoroAC 1 ^ 2 := by linarith only [hbv_pos, hac_eq]
  have hbv_abs : |virasoroBV ^ 2| ≤ virasoroAC 1 ^ 2 := by rw [abs_of_nonneg hbv_pos.le]; exact hbv_le_ac
  have hbv_neg_abs : |-(virasoroBV ^ 2)| ≤ virasoroAC 1 ^ 2 := by
    rw [abs_neg, abs_of_nonneg hbv_pos.le]; exact hbv_le_ac
  have hξ_m_mem := virasoroDeltaChart_div_mem one_pos hbv_abs
  have hξ_p_mem := virasoroDeltaChart_div_mem one_pos hbv_neg_abs
  have h0_eq : virasoroDeltaChart 1 0 / 1 = xiBar := by simp [virasoroDeltaChart_zero]
  have h0_mem : xiBar ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) := by
    have h0' := virasoroDeltaChart_div_mem one_pos (show |(0 : ℝ)| ≤ virasoroAC 1 ^ 2 from by simp [sq_nonneg])
    rwa [h0_eq] at h0'
  have hlt_sq : (xiStar - r₁) ^ 2 / 3 < xiBar := by
    unfold xiBar; nlinarith only [hr₁_pos, hr₁_lt]
  have hgt_sq : xiBar < (xiStar + r₁) ^ 2 / 3 := by
    unfold xiBar; nlinarith only [xiStar_pos, hr₁_pos]
  have hlo' : virasoroDeltaChart 1 (virasoroBV ^ 2) / 1 < (xiStar - r₁) ^ 2 / 3 := by
    rw [div_one]; exact hlo
  have hhi' : (xiStar + r₁) ^ 2 / 3 < virasoroDeltaChart 1 (-(virasoroBV ^ 2)) / 1 := by
    rw [div_one]; exact hhi
  have hu_hi1_pos : 0 < virasoroUChart 1 ((xiStar - r₁) ^ 2 / 3) := by
    rw [← virasoroUChart_deltaChart one_pos (show |(0 : ℝ)| ≤ virasoroAC 1 ^ 2 from by simp [sq_nonneg]), h0_eq]
    exact virasoroUChart_strictAnti one_pos ⟨hξ_m_mem.1.trans hlo'.le, hlt_sq.le.trans h0_mem.2⟩ h0_mem hlt_sq
  have hu_hi1_lt : virasoroUChart 1 ((xiStar - r₁) ^ 2 / 3) < virasoroBV ^ 2 := by
    have h1 := virasoroUChart_strictAnti one_pos hξ_m_mem
      ⟨hξ_m_mem.1.trans hlo'.le, hlt_sq.le.trans h0_mem.2⟩ hlo'
    rwa [virasoroUChart_deltaChart one_pos hbv_abs] at h1
  have hu_lo1_neg : virasoroUChart 1 ((xiStar + r₁) ^ 2 / 3) < 0 := by
    rw [← virasoroUChart_deltaChart one_pos (show |(0 : ℝ)| ≤ virasoroAC 1 ^ 2 from by simp [sq_nonneg]), h0_eq]
    exact virasoroUChart_strictAnti one_pos h0_mem ⟨h0_mem.1.trans hgt_sq.le, hhi'.le.trans hξ_p_mem.2⟩ hgt_sq
  have hu_lo1_gt : -(virasoroBV ^ 2) < virasoroUChart 1 ((xiStar + r₁) ^ 2 / 3) := by
    have h1 := virasoroUChart_strictAnti one_pos
      ⟨h0_mem.1.trans hgt_sq.le, hhi'.le.trans hξ_p_mem.2⟩ hξ_p_mem hhi'
    rwa [virasoroUChart_deltaChart one_pos hbv_neg_abs] at h1
  set u_hi1 := virasoroUChart 1 ((xiStar - r₁) ^ 2 / 3)
  set u_lo1 := virasoroUChart 1 ((xiStar + r₁) ^ 2 / 3)
  set C_env := 2 * C_κ51
  have hC_env_pos : 0 < C_env := mul_pos two_pos hCκ_pos
  set b := (1 / 2 : ℝ) * min virasoroBV (min √u_hi1 √(-u_lo1))
  have hb_pos : 0 < b := by
    dsimp [b]
    exact mul_pos (by norm_num) (lt_min virasoroBV_pos (lt_min (Real.sqrt_pos.mpr hu_hi1_pos)
      (Real.sqrt_pos.mpr (neg_pos.mpr hu_lo1_neg))))
  have hb_sq_uhi : 4 * b ^ 2 ≤ u_hi1 := by
    have h1 : 2 * b ≤ √u_hi1 := by
      dsimp [b]
      have h2 := (min_le_right virasoroBV (min √u_hi1 √(-u_lo1))).trans (min_le_left _ _)
      linarith only [h2]
    have hsq := pow_le_pow_left₀ (mul_nonneg two_pos.le hb_pos.le) h1 2
    rw [Real.sq_sqrt hu_hi1_pos.le] at hsq
    linarith only [hsq]
  have hb_sq_ulo : 4 * b ^ 2 ≤ -u_lo1 := by
    have h1 : 2 * b ≤ √(-u_lo1) := by
      dsimp [b]
      have h2 := (min_le_right virasoroBV (min √u_hi1 √(-u_lo1))).trans (min_le_right _ _)
      linarith only [h2]
    have hsq := pow_le_pow_left₀ (mul_nonneg two_pos.le hb_pos.le) h1 2
    rw [Real.sq_sqrt (neg_pos.mpr hu_lo1_neg).le] at hsq
    linarith only [hsq]
  let C_win : ℝ := 2 / κ_obs * ((C₂₃ + 1) / 2 + C₂₄ + C_p)
  let C_vac : ℝ := 3 * C_win
  have hC_win_nn : 0 ≤ C_win := by dsimp [C_win]; positivity
  have hC_vac_nn : 0 ≤ C_vac := by dsimp [C_vac]; positivity
  let P : BootstrapParams := {
    b := b
    C_a := max (spinArcCovConst C_env) (4 * Real.exp (6 / 5) + 3 * C_env)
    C_unc := spinArcUncConst C_env
    C_1 := quantC1C1
    w_star := quantC1WStar
    κ_star := quantC1KappaStar
    C_α := 1
    C_fb := 1
    D_1 := 1
    η_0 := quantC1Eta0
    δ_star := quantC1DeltaStar
    κ := 1
    C_0 := 1
    C_L := max 1 (2 * b * Real.exp 1)
    γ := 2 * C₂ * b + 1 / 3
    k_0 := 5
    hb := hb_pos
    hCa := (spinArcCovConst_pos hC_env_pos).le.trans (le_max_left _ _)
    hCunc := (spinArcUncConst_pos hC_env_pos).le
    hC1 := quantC1C1_pos
    hw_star := quantC1WStar_pos
    hκ_star := quantC1KappaStar_pos
    hCα := zero_le_one
    hCfb := le_rfl
    hD1 := zero_le_one
    hη0 := quantC1Eta0_pos
    hδ_star := quantC1DeltaStar_pos
    hκ := zero_lt_one
    hC0 := zero_lt_one
    hCL := le_max_left _ _
    hγ := by positivity
    hk0 := by norm_num
  }
  let CK := tebCKWeak P (tebThetaHB P 0) (P.κ_star / (4 * P.w_star)) C_vac
  have hCK_pos : 0 < CK := tebCKWeak_pos P (tebThetaHB_pos P le_rfl)
    (div_pos P.hκ_star (mul_pos (by norm_num) P.hw_star)) hC_vac_nn
  let C_loc : ℝ := CK * (1 + Real.log P.C_L + P.γ)
  have hC_loc_pos : 0 < C_loc := mul_pos hCK_pos (by
    have h1 := Real.log_nonneg P.hCL; have h2 := P.hγ; linarith only [h1, h2])
  let K_ς : ℝ := 24 * C₂ * (3 * π * 2 * b + 1)
  have hK_ς_pos : 0 < K_ς := by dsimp [K_ς]; positivity
  let c_thr : ℝ := max (max (max c₀ (max c₀_23 c₀_24)) (max (tebC2 P + 1) 4097))
    (max (max ((C₀ / r₁) ^ (3 / 2 : ℝ) + 1) ((3 * π) ^ (12 : ℕ) + 1))
      (max ((96 / b ^ 2) ^ (3 / 2 : ℝ) + 1)
        (max ((1 + (4 : ℝ) / min u_hi1 (-u_lo1)) ^ (3 / 2 : ℝ) + 1)
          (max ((max (48 * C₂) K_ς) ^ (24 : ℕ) + 1)
            (((2 / r_d) ^ (2 : ℕ) + 1) + ((|airyZero 1| + 2) / r_d) ^ (3 / 2 : ℝ) + 1)))))
  have hc_thr_ge40 : 40 ≤ c_thr := by
    have h1 : (40 : ℝ) ≤ 4097 := by norm_num
    exact h1.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  refine ⟨C_loc, c_thr, hC_loc_pos, hc_thr_ge40, ?_⟩
  intro c x₁ u_T hc_ge n hx₁ ha1_lt huT_le hbuT Φ hS
  have hc_c₀ : c₀ ≤ c :=
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hc_ge
  have hc_23 : c₀_23 ≤ c :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hc_ge
  have hc_24 : c₀_24 ≤ c :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hc_ge
  have hc40 : 40 ≤ c := hc_thr_ge40.trans hc_ge
  have hn_ge4096 : 4096 ≤ n := by
    have h1 : (4097 : ℝ) ≤ c :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc_ge
    dsimp [n]; linarith only [h1]
  have hn_pos : 0 < n := by linarith only [hn_ge4096]
  have hn_ge1 : 1 ≤ n := by linarith only [hn_ge4096]
  have hn_tebC2 : tebC2 P ≤ n := by
    have h1 : tebC2 P + 1 ≤ c :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc_ge
    dsimp [n]; linarith only [h1]
  have hC0_r1 : C₀ * n ^ (-(2 / 3 : ℝ)) ≤ r₁ := by
    have h1 : (C₀ / r₁) ^ (3 / 2 : ℝ) ≤ n := by
      have h2 : (C₀ / r₁) ^ (3 / 2 : ℝ) + 1 ≤ c :=
        ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hc_ge
      dsimp [n]; linarith only [h2]
    have h2 : C₀ / r₁ ≤ n ^ (2 / 3 : ℝ) := by
      calc C₀ / r₁ = ((C₀ / r₁) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
            rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
        _ ≤ n ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
    rw [Real.rpow_neg hn_pos.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hn_pos _)]
    exact (div_le_iff₀ hr₁_pos).mp h2 |>.trans_eq (by ring)
  have hx1_abs_r1 : |x₁ - xiStar| ≤ r₁ := hx₁.trans hC0_r1
  have hx1_hi : x₁ ≤ xiStar + r₁ := by linarith only [(abs_le.mp hx1_abs_r1).2]
  have hn_c12 : (3 * π) ^ (12 : ℕ) ≤ n := by
    have h1 : (3 * π) ^ (12 : ℕ) + 1 ≤ c :=
      ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hc_ge
    dsimp [n]; linarith only [h1]
  have hn_b96 : 96 ≤ b ^ 2 * n ^ (2 / 3 : ℝ) := by
    have h1 : (96 / b ^ 2) ^ (3 / 2 : ℝ) ≤ n := by
      have h2 : (96 / b ^ 2) ^ (3 / 2 : ℝ) + 1 ≤ c :=
        ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc_ge
      dsimp [n]; linarith only [h2]
    have h2 : 96 / b ^ 2 ≤ n ^ (2 / 3 : ℝ) := by
      calc 96 / b ^ 2 = ((96 / b ^ 2) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
            rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
        _ ≤ n ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
    exact (div_le_iff₀' (sq_pos_of_pos hb_pos)).mp h2
  have hn_b48 : 48 ≤ b ^ 2 * n ^ (2 / 3 : ℝ) := by linarith only [hn_b96]
  have hn_tail : 4 ≤ min u_hi1 (-u_lo1) * n ^ (2 / 3 : ℝ) := by
    have hm_pos : 0 < min u_hi1 (-u_lo1) := lt_min hu_hi1_pos (neg_pos.mpr hu_lo1_neg)
    have h1 : (1 + (4 : ℝ) / min u_hi1 (-u_lo1)) ^ (3 / 2 : ℝ) ≤ n := by
      have h2 : (1 + (4 : ℝ) / min u_hi1 (-u_lo1)) ^ (3 / 2 : ℝ) + 1 ≤ c :=
        ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc_ge
      dsimp [n]; linarith only [h2]
    have h2 : (4 : ℝ) / min u_hi1 (-u_lo1) ≤ n ^ (2 / 3 : ℝ) := by
      calc (4 : ℝ) / min u_hi1 (-u_lo1) ≤ 1 + (4 : ℝ) / min u_hi1 (-u_lo1) := by linarith only
        _ = ((1 + (4 : ℝ) / min u_hi1 (-u_lo1)) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
            rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
        _ ≤ n ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
    exact (div_le_iff₀' hm_pos).mp h2
  have h_last_c := ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))).trans hc_ge
  have hn_last : ((2 / r_d) ^ (2 : ℕ) + 1) + ((|airyZero 1| + 2) / r_d) ^ (3 / 2 : ℝ) ≤ n := by
    dsimp [n]; linarith only [h_last_c]
  have hR_dom_lt_ball : n ^ (1 / 6 : ℝ) < r_d * n ^ (2 / 3 : ℝ) := by
    have h1 : (2 / r_d) ^ (2 : ℕ) ≤ n := by
      have hpos : 0 ≤ ((|airyZero 1| + 2) / r_d) ^ (3 / 2 : ℝ) := by positivity
      linarith only [hn_last, hpos]
    have h2 : 2 / r_d ≤ n ^ (1 / 2 : ℝ) := by
      calc 2 / r_d = ((2 / r_d) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ n ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
    have h3 : 1 < r_d * n ^ (1 / 2 : ℝ) := by
      have := (div_le_iff₀' hrd_pos).mp h2; linarith only [this]
    have h_split : n ^ (2 / 3 : ℝ) = n ^ (1 / 6 : ℝ) * n ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    rw [h_split, ← mul_assoc, mul_comm r_d (n ^ (1 / 6 : ℝ)), mul_assoc]
    exact lt_mul_of_one_lt_right (Real.rpow_pos_of_pos hn_pos _) h3
  have ha1_ball : |airyZero 1| + 1 < r_d * n ^ (2 / 3 : ℝ) := by
    have h1 : ((|airyZero 1| + 2) / r_d) ^ (3 / 2 : ℝ) ≤ n := by
      have hpos : 0 ≤ (2 / r_d) ^ (2 : ℕ) + 1 := by positivity
      linarith only [hn_last, hpos]
    have h2 : (|airyZero 1| + 2) / r_d ≤ n ^ (2 / 3 : ℝ) := by
      calc (|airyZero 1| + 2) / r_d = (((|airyZero 1| + 2) / r_d) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
            rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
        _ ≤ n ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
    linarith only [(div_le_iff₀' hrd_pos).mp h2]
  have h_log_max : max (48 * C₂) K_ς ≤ n ^ (1 / 24 : ℝ) := by
    have h1 : (max (48 * C₂) K_ς) ^ (24 : ℕ) ≤ n := by
      have h2 : (max (48 * C₂) K_ς) ^ (24 : ℕ) + 1 ≤ c :=
        ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _))))).trans hc_ge
      dsimp [n]; linarith only [h2]
    calc max (48 * C₂) K_ς = ((max (48 * C₂) K_ς) ^ (24 : ℕ)) ^ (1 / 24 : ℝ) := by
          rw [← Real.rpow_natCast _ 24, ← Real.rpow_mul (by linarith only [hK_ς_pos, le_max_right (48 * C₂) K_ς])]
          norm_num
      _ ≤ n ^ (1 / 24 : ℝ) := Real.rpow_le_rpow (by positivity [hK_ς_pos]) h1 (by positivity)
  have hlog_n_le : Real.log n ≤ 24 * n ^ (1 / 24 : ℝ) := by
    have h1 := Real.log_le_rpow_div hn_pos.le (by norm_num : (0 : ℝ) < 1 / 24)
    linarith only [h1]
  have hς_half : C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n ≤ 1 / 2 := by
    have h48_le : 48 * C₂ ≤ n ^ (1 / 24 : ℝ) := (le_max_left _ _).trans h_log_max
    have h1 : C₂ * Real.log n ≤ (1 / 2 : ℝ) * n ^ (1 / 3 : ℝ) := by
      calc C₂ * Real.log n ≤ C₂ * (24 * n ^ (1 / 24 : ℝ)) := mul_le_mul_of_nonneg_left hlog_n_le hC2_pos.le
        _ = (1 / 2 : ℝ) * ((48 * C₂) * n ^ (1 / 24 : ℝ)) := by ring
        _ ≤ (1 / 2 : ℝ) * (n ^ (1 / 24 : ℝ) * n ^ (1 / 24 : ℝ)) := by gcongr
        _ ≤ (1 / 2 : ℝ) * (n ^ (1 / 3 : ℝ) * 1) := by
            have h24_add : n ^ (1 / 24 : ℝ) * n ^ (1 / 24 : ℝ) = n ^ (1 / 12 : ℝ) := by
              rw [← Real.rpow_add hn_pos]; norm_num
            have h12_13 : n ^ (1 / 12 : ℝ) ≤ n ^ (1 / 3 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hn_ge1 (by norm_num)
            linarith only [h24_add, h12_13]
        _ = (1 / 2 : ℝ) * n ^ (1 / 3 : ℝ) := by ring
    calc C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n = (C₂ * Real.log n) / n ^ (1 / 3 : ℝ) := by
          rw [Real.rpow_neg hn_pos.le, div_eq_mul_inv]; ring
      _ ≤ 1 / 2 := (div_le_iff₀ (Real.rpow_pos_of_pos hn_pos _)).mpr h1
  have hς_unc_all : C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n *
      (3 * π * (2 * b * n ^ (1 / 3 : ℝ)) * n ^ (-(1 / 12 : ℝ)) + 1) ≤ 1 := by
    have h1_le_n13 : (1 : ℝ) ≤ n ^ (1 / 3 : ℝ) * n ^ (-(1 / 12 : ℝ)) := by
      rw [← Real.rpow_add hn_pos, show (1 / 3 : ℝ) + -(1 / 12 : ℝ) = 1 / 4 by norm_num]
      exact Real.one_le_rpow hn_ge1 (by norm_num)
    have h_br : 3 * π * (2 * b * n ^ (1 / 3 : ℝ)) * n ^ (-(1 / 12 : ℝ)) + 1 ≤
        (3 * π * 2 * b + 1) * (n ^ (1 / 3 : ℝ) * n ^ (-(1 / 12 : ℝ))) := by
      linarith only [h1_le_n13]
    have h_cn : C₂ * n ^ (-(1 / 3 : ℝ)) * (n ^ (1 / 3 : ℝ) * n ^ (-(1 / 12 : ℝ))) = C₂ * n ^ (-(1 / 12 : ℝ)) := by
      rw [← mul_assoc, mul_assoc C₂, ← Real.rpow_add hn_pos, neg_add_cancel, Real.rpow_zero, mul_one]
    have hK_le : K_ς ≤ n ^ (1 / 24 : ℝ) := (le_max_right _ _).trans h_log_max
    have hς_nn' : 0 ≤ C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n :=
      mul_nonneg (mul_nonneg hC2_pos.le (Real.rpow_nonneg hn_pos.le _)) (Real.log_nonneg hn_ge1)
    calc C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * (3 * π * (2 * b * n ^ (1 / 3 : ℝ)) * n ^ (-(1 / 12 : ℝ)) + 1)
        ≤ C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n * ((3 * π * 2 * b + 1) * (n ^ (1 / 3 : ℝ) * n ^ (-(1 / 12 : ℝ)))) :=
          mul_le_mul_of_nonneg_left h_br hς_nn'
      _ = (C₂ * (3 * π * 2 * b + 1)) * Real.log n * n ^ (-(1 / 12 : ℝ)) := by
          calc _ = (C₂ * n ^ (-(1 / 3 : ℝ)) * (n ^ (1 / 3 : ℝ) * n ^ (-(1 / 12 : ℝ)))) *
                  ((3 * π * 2 * b + 1) * Real.log n) := by ring
            _ = _ := by rw [h_cn]; ring
      _ ≤ (C₂ * (3 * π * 2 * b + 1)) * (24 * n ^ (1 / 24 : ℝ)) * n ^ (-(1 / 12 : ℝ)) := by gcongr
      _ = K_ς * (n ^ (-(1 / 12 : ℝ)) * n ^ (1 / 24 : ℝ)) := by dsimp [K_ς]; ring
      _ = K_ς * n ^ (-(1 / 24 : ℝ)) := by
          rw [← Real.rpow_add hn_pos, show -(1 / 12 : ℝ) + 1 / 24 = -(1 / 24 : ℝ) by norm_num]
      _ ≤ n ^ (1 / 24 : ℝ) * n ^ (-(1 / 24 : ℝ)) := by gcongr
      _ = 1 := by rw [← Real.rpow_add hn_pos, add_neg_cancel, Real.rpow_zero]
  obtain ⟨hκ_lo, hAn, _him_ball, hEnv_1, _him_dom, _hpos_band, hL1_dom, hB2⟩ :=
    hdisc hc_c₀ hx₁ ha1_lt huT_le hbuT hS
  have hB_pos : 0 < spinCalNorm c Φ := lt_of_lt_of_le hκ_pos hκ_lo
  set k₀ : ℕ := Nat.ceil (b ^ 2 * n ^ (2 / 3 : ℝ))
  have hk₀_ge96 : 96 ≤ k₀ := by
    have : (96 : ℝ) ≤ (k₀ : ℝ) := hn_b96.trans (Nat.le_ceil _)
    exact_mod_cast this
  have h_circ := good_circle_exists k₀ (by omega : 10 ≤ k₀)
  let R : ℝ := Classical.choose h_circ
  have hR_spec := Classical.choose_spec h_circ
  have hR_lb : (k₀ : ℝ) ≤ R := hR_spec.1
  have hR_le_k : R ≤ (k₀ : ℝ) + 1 := hR_spec.2.1
  have hR_low := hR_spec.2.2
  have hR_96 : 96 ≤ R := (by exact_mod_cast hk₀_ge96 : (96 : ℝ) ≤ k₀).trans hR_lb
  have hR_48 : 48 ≤ R := by linarith only [hR_96]
  have hR_10 : 10 ≤ R := by linarith only [hR_48]
  have hR_pos : 0 < R := by linarith only [hR_48]
  have hR_bv : b ^ 2 * n ^ (2 / 3 : ℝ) ≤ R := (Nat.le_ceil _).trans hR_lb
  have hR_ub_ceil : R ≤ b ^ 2 * n ^ (2 / 3 : ℝ) + 2 := by
    have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ b ^ 2 * n ^ (2 / 3 : ℝ))
    linarith only [hR_le_k, hlt]
  have hR_ub_2b : R ≤ 2 * b ^ 2 * n ^ (2 / 3 : ℝ) + 1 := by linarith only [hR_bv, hR_ub_ceil, hn_b48]
  have hsqrtR_ub : √R ≤ 2 * b * n ^ (1 / 3 : ℝ) := by
    have h1 : R ≤ (2 * b * n ^ (1 / 3 : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, ← Real.rpow_natCast (n ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hn_pos.le]
      norm_num
      linarith only [hR_ub_ceil, hR_bv, hn_b48]
    calc √R ≤ √((2 * b * n ^ (1 / 3 : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 2 * b * n ^ (1 / 3 : ℝ) := Real.sqrt_sq (by positivity)
  let u_lo := virasoroUChart n ((xiStar + r₁) ^ 2 / 3)
  let u_hi := virasoroUChart n ((xiStar - r₁) ^ 2 / 3)
  have hu_hi_eq : u_hi = u_hi1 * n ^ (2 / 3 : ℝ) := by
    dsimp [u_hi, u_hi1]; rw [virasoroUChart_scale_eq' hn_pos]; ring
  have hu_lo_eq : u_lo = u_lo1 * n ^ (2 / 3 : ℝ) := by
    dsimp [u_lo, u_lo1]; rw [virasoroUChart_scale_eq' hn_pos]; ring
  have hR_uhi : R + 1 ≤ u_hi := by
    have hm := min_le_left u_hi1 (-u_lo1)
    have hm1 : 4 ≤ u_hi1 * n ^ (2 / 3 : ℝ) :=
      hn_tail.trans (mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hn_pos.le _))
    have h4b : 4 * b ^ 2 * n ^ (2 / 3 : ℝ) ≤ u_hi1 * n ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hb_sq_uhi (Real.rpow_nonneg hn_pos.le _)
    linarith only [hR_ub_ceil, h4b, hm1, hu_hi_eq]
  have hu_lo_le : u_lo ≤ -R := by
    have hm := min_le_right u_hi1 (-u_lo1)
    have hm1 : 4 ≤ -u_lo1 * n ^ (2 / 3 : ℝ) :=
      hn_tail.trans (mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hn_pos.le _))
    have h4b : 4 * b ^ 2 * n ^ (2 / 3 : ℝ) ≤ -u_lo1 * n ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hb_sq_ulo (Real.rpow_nonneg hn_pos.le _)
    linarith only [hR_ub_ceil, h4b, hm1, hu_lo_eq]
  have hac_sq_eq : virasoroAC n ^ 2 = r_d * n ^ (2 / 3 : ℝ) := by rw [virasoroAC_sq n hn_pos.le, hr_d_eq]
  have hcA_sq_eq : (cA * n ^ (1 / 3 : ℝ)) ^ 2 = virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) := by
    rw [hcA_eq, mul_pow, ← Real.rpow_natCast (n ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hn_pos.le]; norm_num
  have huhi_cA : u_hi ≤ (cA * n ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [hcA_sq_eq, hu_hi_eq]; exact mul_le_mul_of_nonneg_right hu_hi1_lt.le (Real.rpow_nonneg hn_pos.le _)
  have huhi_ac : u_hi < virasoroAC n ^ 2 := by
    rw [virasoroAC_sq n hn_pos.le]
    have hcA_pos' : 0 < virasoroBV ^ 2 * n ^ (2 / 3 : ℝ) := by positivity
    rw [← hcA_sq_eq] at hcA_pos'
    linarith only [huhi_cA, hcA_sq_eq, hcA_pos']
  have hlo_ac : -(virasoroAC n ^ 2) < u_lo := by
    rw [hu_lo_eq, virasoroAC_sq n hn_pos.le]
    have h1 : -(2 * virasoroBV ^ 2) < u_lo1 := by linarith only [hbv_pos, hu_lo1_gt]
    have h2 := mul_lt_mul_of_pos_right h1 (Real.rpow_pos_of_pos hn_pos (2 / 3 : ℝ))
    linarith only [h2]
  have hlo_ball : -r_d * n ^ (2 / 3 : ℝ) < u_lo := by
    rw [show -r_d * n ^ (2 / 3 : ℝ) = -(r_d * n ^ (2 / 3 : ℝ)) by ring, ← hac_sq_eq]; exact hlo_ac
  have hhi_ball : u_hi < r_d * n ^ (2 / 3 : ℝ) := by rw [← hac_sq_eq]; exact huhi_ac
  have h_ac_nn := sq_nonneg (virasoroAC 1)
  have hξ_scale_lo : virasoroDeltaChart n (virasoroAC n ^ 2) / n = virasoroDeltaChart 1 (virasoroAC 1 ^ 2) := by
    have hac : virasoroAC n ^ 2 = (virasoroAC 1 ^ 2) * n ^ (2 / 3 : ℝ) := by
      rw [virasoroAC_sq n hn_pos.le, virasoroAC_sq 1 zero_le_one, Real.one_rpow, mul_one]
    rw [hac]; exact virasoroDeltaChart_div_scale_eq' hn_pos _
  have hξ_scale_hi : virasoroDeltaChart n (-(virasoroAC n ^ 2)) / n = virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)) := by
    have hac : -(virasoroAC n ^ 2) = (-(virasoroAC 1 ^ 2)) * n ^ (2 / 3 : ℝ) := by
      rw [virasoroAC_sq n hn_pos.le, virasoroAC_sq 1 zero_le_one, Real.one_rpow, mul_one, neg_mul]
    rw [hac]; exact virasoroDeltaChart_div_scale_eq' hn_pos _
  have hlo_ac1 : virasoroDeltaChart 1 (virasoroAC 1 ^ 2) < (xiStar - r₁) ^ 2 / 3 := by
    have hanti := virasoroDeltaChart_strictAnti one_pos
    have hmem_ac := (abs_of_nonneg h_ac_nn).le
    have hlt := hanti ⟨by linarith only [hbv_pos, hbv_le_ac], hbv_le_ac⟩ ⟨by linarith only [h_ac_nn], le_rfl⟩
      (by linarith only [hbv_pos, hac_eq] : virasoroBV ^ 2 < virasoroAC 1 ^ 2)
    linarith only [hlo, hlt, hmem_ac]
  have hhi_ac1 : (xiStar + r₁) ^ 2 / 3 < virasoroDeltaChart 1 (-(virasoroAC 1 ^ 2)) := by
    have hanti := virasoroDeltaChart_strictAnti one_pos
    have hmem_ac : |-(virasoroAC 1 ^ 2)| ≤ virasoroAC 1 ^ 2 := by rw [abs_neg, abs_of_nonneg h_ac_nn]
    have hlt := hanti ⟨le_rfl, by linarith only [h_ac_nn]⟩
      ⟨by linarith only [hbv_pos, hbv_le_ac], by linarith only [hbv_pos, hbv_le_ac]⟩
      (by linarith only [hbv_pos, hac_eq] : -(virasoroAC 1 ^ 2) < -(virasoroBV ^ 2))
    linarith only [hhi, hlt, hmem_ac]
  have hbu_hi : (virasoroBChart n (u_hi : ℂ)).re = xiStar - r₁ := by
    have hdu := virasoroDeltaChart_uChart (ξ := (xiStar - r₁) ^ 2 / 3) hn_pos
      (by rw [hξ_scale_lo]; exact hlo_ac1.le)
      (by rw [hξ_scale_hi]; exact hlt_sq.le.trans (hgt_sq.le.trans hhi_ac1.le))
    have huhi_pos : 0 < u_hi := by
      rw [hu_hi_eq]; exact mul_pos hu_hi1_pos (Real.rpow_pos_of_pos hn_pos (2 / 3 : ℝ))
    have huhi_abs : |u_hi| ≤ virasoroAC n ^ 2 :=
      abs_le.mpr ⟨by linarith only [huhi_pos, sq_nonneg (virasoroAC n)], huhi_ac.le⟩
    rw [(virasoroBChart_ofReal_eq_sqrt hn_pos huhi_abs).2.1]
    change Real.sqrt (3 * virasoroDeltaChart n u_hi / n) = _
    dsimp [u_hi]; rw [hdu, show 3 * (n * ((xiStar - r₁) ^ 2 / 3)) / n = (xiStar - r₁) ^ 2 by field_simp [hn_pos.ne'],
      Real.sqrt_sq (by linarith only [xiStar_pos, hr₁_lt])]
  have hbu_lo : (virasoroBChart n (u_lo : ℂ)).re = xiStar + r₁ := by
    have hdu := virasoroDeltaChart_uChart (ξ := (xiStar + r₁) ^ 2 / 3) hn_pos
      (by rw [hξ_scale_lo]; exact hlo_ac1.le.trans (hlt_sq.le.trans hgt_sq.le))
      (by rw [hξ_scale_hi]; exact hhi_ac1.le)
    have hulo_neg : u_lo < 0 := by
      rw [hu_lo_eq]; exact mul_neg_of_neg_of_pos hu_lo1_neg (Real.rpow_pos_of_pos hn_pos (2 / 3 : ℝ))
    have hulo_abs : |u_lo| ≤ virasoroAC n ^ 2 :=
      abs_le.mpr ⟨hlo_ac.le, by linarith only [hulo_neg, sq_nonneg (virasoroAC n)]⟩
    rw [(virasoroBChart_ofReal_eq_sqrt hn_pos hulo_abs).2.1]
    change Real.sqrt (3 * virasoroDeltaChart n u_lo / n) = _
    dsimp [u_lo]; rw [hdu, show 3 * (n * ((xiStar + r₁) ^ 2 / 3)) / n = (xiStar + r₁) ^ 2 by field_simp [hn_pos.ne'],
      Real.sqrt_sq (by linarith only [xiStar_pos, hr₁_pos])]
  have hx1_ub_hi : x₁ ≤ xiStar + C₀ * n ^ (-(2 / 3 : ℝ)) := by linarith only [(abs_le.mp hx₁).2]
  have hcal_23 : spinCalInt c Φ ≤ (C₂₃ + 1) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) :=
    ((h23 hc_23 hS.1 hx1_ub_hi hS.2.1 hS.2.2.1 hS.2.2.2.2).2.2 hS.2.2.2.1)
  have h24_bd := (h24 hc_24 hx1_ub_hi hS).2.2.2
  have hWin_inv := spin_window_re_le hc40 hr₁_pos hr₁_lt hx1_ub_hi hx1_hi hS hB_pos hlo_ac
    (hu_lo_le.trans (by linarith only [hR_48, hR_uhi])) huhi_ac hbu_lo hbu_hi
    hC23_pos hC24_pos hCp_pos hcal_23 h24_bd
  have hlog_nn : 0 ≤ n ^ (-(2 / 3 : ℝ)) * Real.log n :=
    mul_nonneg (Real.rpow_nonneg hn_pos.le _) (Real.log_nonneg hn_ge1)
  set η_vac : ℝ := C_win * (n ^ (-(2 / 3 : ℝ)) * Real.log n)
  have hη_nn : 0 ≤ η_vac := mul_nonneg hC_win_nn hlog_nn
  have hη_ub : η_vac ≤ C_vac * n ^ (-(1 / 3 : ℝ)) := by
    have hlog3 : Real.log n ≤ 3 * n ^ (1 / 3 : ℝ) := by
      have h1 := Real.log_le_rpow_div hn_pos.le (by norm_num : (0 : ℝ) < 1 / 3)
      linarith only [h1]
    have h_rpow : n ^ (-(2 / 3 : ℝ)) * Real.log n ≤ 3 * n ^ (-(1 / 3 : ℝ)) := by
      calc n ^ (-(2 / 3 : ℝ)) * Real.log n ≤ n ^ (-(2 / 3 : ℝ)) * (3 * n ^ (1 / 3 : ℝ)) := by gcongr
        _ = 3 * (n ^ (-(2 / 3 : ℝ)) * n ^ (1 / 3 : ℝ)) := by ring
        _ = 3 * n ^ (-(1 / 3 : ℝ)) := by rw [← Real.rpow_add hn_pos]; norm_num
    dsimp [η_vac, C_vac]
    calc C_win * (n ^ (-(2 / 3 : ℝ)) * Real.log n) ≤ C_win * (3 * n ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left h_rpow hC_win_nn
      _ = 3 * C_win * n ^ (-(1 / 3 : ℝ)) := by ring
  have hWin : ∫ u in u_lo..u_hi, (((2 : ℝ) : ℂ) * spinPtilde c Φ (u : ℂ)).re ≤ η_vac := by
    have hB_inv_le : 2 * (spinCalNorm c Φ)⁻¹ ≤ 2 / κ_obs := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left (inv_anti₀ hκ_pos hκ_lo) zero_le_two
    have hCnn : 0 ≤ ((C₂₃ + 1) / 2 + C₂₄ + C_p) * (n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
      positivity [hlog_nn]
    exact hWin_inv.trans <| by
      rw [mul_assoc (2 * (spinCalNorm c Φ)⁻¹)]
      exact (mul_le_mul_of_nonneg_right hB_inv_le hCnn).trans_eq (by dsimp [η_vac, C_win]; ring)
  have h_good_ai : ∀ u : ℂ, ‖u‖ = R → airyAiC u ≠ 0 := by
    intro u hu h0
    have h1 := hR_low u hu
    rw [h0, norm_zero] at h1
    have h2 : 0 < 1 / (25 * π) * (1 + R) ^ (-(1 / 2 : ℝ)) * airyEnv u := by
      have := airyEnv_pos u
      have := Real.rpow_pos_of_pos (by linarith only [hR_pos] : (0 : ℝ) < 1 + R) (-(1 / 2 : ℝ))
      positivity
    linarith only [h1, h2]
  have hN_ex := airy_circleData hR_pos h_good_ai
  let N : ℕ := Classical.choose hN_ex
  have hN_spec := Classical.choose_spec hN_ex
  have hN : ∀ m : ℕ, 1 ≤ m → (m ≤ N ↔ -airyZero m < R) := hN_spec.1
  have hD : CftCircleData airyAiC (fun m => (airyZero m : ℂ)) (Finset.Icc 1 N) R := hN_spec.2
  have hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖(airyBiC w - I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π :=
    fun w hw him => airy_Rplus_bound him (hw ▸ hR_low w hw)
  have hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖(airyBiC w + I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π :=
    fun w hw him => airy_Rminus_bound him (hw ▸ hR_low w hw)
  obtain ⟨ha1_lo_z, ha1_hi_z⟩ := airyZero_one
  have huT_le_a1_half : u_T ≤ airyZero 1 + 1 / 2 := by
    have h2 : min quantC1DeltaStar (min quantC1Eta0 1) ≤ 1 / 2 :=
      (min_le_left _ _).trans quantC1DeltaStar_le
    linarith only [hB2.1, h2]
  have huT_hi : u_T ≤ -1 := by linarith only [huT_le_a1_half, ha1_hi_z]
  have huT_lo : -3.4 ≤ u_T := by linarith only [ha1_lt, ha1_lo_z]
  have huT_abs : |u_T| ≤ virasoroAC n ^ 2 := by
    have h34 : |u_T| ≤ 3.4 := abs_le.mpr ⟨huT_lo, by linarith only [huT_hi]⟩
    have h_min : R ≤ virasoroAC n ^ 2 := (by linarith only [hR_uhi] : R ≤ u_hi).trans huhi_ac.le
    linarith only [h34, hR_10, h_min]
  have hΨ_nn_all : ∀ v ∈ Icc u_lo u_hi, v ≤ u_T →
      0 ≤ (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re := fun v hv hvu => by
    have h1 := spinPtilde_re_nonneg_of_le hc40 hS.1 hS.2.1 hS.2.2.2.2 hB_pos.le huT_abs hbuT
      (abs_lt.mpr ⟨hlo_ac.trans_le hv.1, hv.2.trans_lt huhi_ac⟩) hvu
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linarith only [h1]
  have hΨ_nn_uT : ∀ v ∈ Icc u_lo u_T, 0 ≤ (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re := fun v hv =>
    hΨ_nn_all v ⟨hv.1, hv.2.trans (huT_hi.trans (by linarith only [hR_10, hR_uhi]))⟩ hv.2
  have hΨ_nn_bandR : ∀ v ∈ Icc (-R) u_T, 0 ≤ (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re := fun v hv =>
    hΨ_nn_uT v ⟨hu_lo_le.trans hv.1, hv.2⟩
  have hRdom_ge4 : 4 ≤ n ^ (1 / 6 : ℝ) := by
    have h1 := Real.rpow_le_rpow (by norm_num) hn_ge4096 (by norm_num : (0 : ℝ) ≤ 1 / 6)
    have h46 : ((4096 : ℝ) ^ (1 / 6 : ℝ)) = 4 := by
      rw [show (4096 : ℝ) = (4 : ℝ) ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast (4 : ℝ) 6,
        ← Real.rpow_mul (by norm_num)]; norm_num
    linarith only [h1, h46]
  set ς : ℝ := C₂ * n ^ (-(1 / 3 : ℝ)) * Real.log n
  have hς_nn : 0 ≤ ς := mul_nonneg (mul_nonneg hC2_pos.le (Real.rpow_nonneg hn_pos.le _)) (Real.log_nonneg hn_ge1)
  set L_exp : ℝ := Real.exp 1 * n ^ (2 * C₂ * b)
  set L : ℝ := √R * L_exp
  have hL_exp_ub : Real.exp (ς * (√R + 1)) ≤ L_exp := by
    have hς_b : ς * (√R + 1) ≤ 2 * C₂ * b * Real.log n + 1 := by
      have h1 : ς * √R ≤ 2 * C₂ * b * Real.log n := by
        have hmul := mul_le_mul_of_nonneg_left hsqrtR_ub hς_nn
        calc ς * √R ≤ ς * (2 * b * n ^ (1 / 3 : ℝ)) := hmul
          _ = 2 * C₂ * b * Real.log n * (n ^ (-(1 / 3 : ℝ)) * n ^ (1 / 3 : ℝ)) := by dsimp [ς]; ring
          _ = 2 * C₂ * b * Real.log n := by
              rw [← Real.rpow_add hn_pos, neg_add_cancel, Real.rpow_zero, mul_one]
      have h2 : ς * 1 ≤ 1 / 2 := by linarith only [hς_half]
      linarith only [h1, h2]
    calc Real.exp (ς * (√R + 1)) ≤ Real.exp (2 * C₂ * b * Real.log n + 1) := Real.exp_le_exp.mpr hς_b
      _ = Real.exp 1 * Real.exp (2 * C₂ * b * Real.log n) := by rw [Real.exp_add, mul_comm]
      _ = L_exp := by rw [mul_comm (2 * C₂ * b), ← Real.rpow_def_of_pos hn_pos (2 * C₂ * b)]
  have hL_exp_ge1 : 1 ≤ L_exp :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one) (Real.one_le_rpow hn_ge1 (by positivity))
  have hL_lb : 1 ≤ L :=
    one_le_mul_of_one_le_of_one_le (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith only [hR_48])) hL_exp_ge1
  have hL_ub : L ≤ P.C_L * n ^ P.γ := by
    have hCL_b : 2 * b * Real.exp 1 ≤ P.C_L := le_max_right _ _
    calc L = √R * (Real.exp 1 * n ^ (2 * C₂ * b)) := rfl
      _ ≤ (2 * b * n ^ (1 / 3 : ℝ)) * (Real.exp 1 * n ^ (2 * C₂ * b)) :=
          mul_le_mul_of_nonneg_right hsqrtR_ub (by positivity)
      _ = (2 * b * Real.exp 1) * (n ^ (2 * C₂ * b) * n ^ (1 / 3 : ℝ)) := by ring
      _ ≤ P.C_L * n ^ (2 * C₂ * b + 1 / 3 : ℝ) := by
          rw [← Real.rpow_add hn_pos]; gcongr
  have hEnv_2 : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ R + 1 → 0 < (u ^ (1 / 2 : ℂ)).re →
      ‖((2 : ℝ) : ℂ) * spinPtilde c Φ u‖ ≤
        C_env * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
    intro u hu_ne hu_R hu_re
    have hbd := hEnv_1 u hu_ne (hu_R.trans (hR_uhi.trans huhi_cA)) hu_re
    have h_inv : (Real.sqrt ‖u‖ * (u ^ (1 / 2 : ℂ)).re)⁻¹ =
        ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
      rw [Real.sqrt_eq_rpow, mul_inv, Real.rpow_neg (norm_nonneg _)]
    have h_env_eq : spinAiryEnv u = airyEnv u := rfl
    have hbd' : ‖spinPtilde c Φ u‖ ≤ C_κ51 * airyEnv u * Real.exp (ς * (u ^ (1 / 2 : ℂ)).re) *
        (‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by
      rw [← h_env_eq, ← h_inv, ← div_eq_mul_inv]; exact hbd
    have h2n : ‖((2 : ℝ) : ℂ) * spinPtilde c Φ u‖ = 2 * ‖spinPtilde c Φ u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg two_pos.le]
    rw [h2n]
    exact (mul_le_mul_of_nonneg_left hbd' two_pos.le).trans_eq (by dsimp [C_env]; ring)
  have hς_unc_R : ς * (3 * π * √R * n ^ (-(1 / 12 : ℝ)) + 1) ≤ 1 := by
    have h1 : 3 * π * √R * n ^ (-(1 / 12 : ℝ)) + 1 ≤
        3 * π * (2 * b * n ^ (1 / 3 : ℝ)) * n ^ (-(1 / 12 : ℝ)) + 1 := by gcongr
    exact (mul_le_mul_of_nonneg_left h1 hς_nn).trans hς_unc_all
  have hB1_nn : 0 ≤ spinBandB1 c Φ R u_T := by
    refine intervalIntegral.integral_nonneg (by linarith only [hR_10, huT_lo]) fun v hv => ?_
    have hP2_nn := hΨ_nn_bandR v hv
    have hneg_nn : 0 ≤ -v / R := div_nonneg (by linarith only [hv.2, huT_hi]) hR_pos.le
    exact mul_nonneg hneg_nn hP2_nn
  have hPN := spin_pnodes_lb_and_theta hn_pos hR_96 ha1_ball hAn ha1_lt hΨ_nn_bandR hB2 hN P
    rfl rfl rfl rfl rfl rfl
  let W : BootstrapWeakCore P := {
    c := n
    R := R
    a := √R
    B_1 := spinBandB1 c Φ R u_T
    B_2 := 0
    L := L
    x_tilde := u_T - airyZero 1
    r_inf := 0
    C_err := 0
    hc := by linarith only [hn_ge4096]
    ha_lb := by
      calc P.b * n ^ (1 / 3 : ℝ) = √(b ^ 2 * n ^ (2 / 3 : ℝ)) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb_pos.le,
              show n ^ (2 / 3 : ℝ) = (n ^ (1 / 3 : ℝ)) ^ 2 by
                rw [← Real.rpow_natCast (n ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hn_pos.le]; norm_num,
              Real.sqrt_sq (Real.rpow_nonneg hn_pos.le _)]
        _ ≤ √R := Real.sqrt_le_sqrt hR_bv
    ha_sq := Real.sq_sqrt hR_pos.le
    hR_ub := hR_ub_2b
    hB1 := hB1_nn
    hB2 := le_rfl
    hL_lb := hL_lb
    hL_ub := hL_ub
    hx_pos := by linarith only [ha1_lt]
    hx_ub := hB2.1
    hr_inf_nn := le_rfl
    hr_inf_ub := by positivity
    hC_err_nn := le_rfl
    hC_err_ub := zero_le_one
    B_1k := fun k => spinBandB1k c Φ R u_T k
    B_2' := fun _ => 0
    P_nodes := fun k ℓ => spinPNodes c Φ R ℓ k N
    I_line := fun k ℓ => ∫ x in (-R)..R, (spinShiftedFun c Φ R ℓ k (x : ℂ)).re
    Arc_cov := fun k ℓ => spinArcCov C_env R L ℓ k
    Arc_unc := spinArcUncConst C_env * n ^ (-(3 / 8 : ℝ))
    hB1k_nn := fun k _ _ => by
      refine intervalIntegral.integral_nonneg (by linarith only [hR_10, huT_lo]) fun v hv => ?_
      have hmin : 0 ≤ min (1 : ℝ) (((k : ℝ) + 1) * (-v) / R) :=
        le_min zero_le_one (div_nonneg (mul_nonneg (by positivity) (by linarith only [hv.2, huT_hi])) hR_pos.le)
      exact mul_nonneg hmin (hΨ_nn_bandR v hv)
    hB2'_nn := fun _ _ _ => le_rfl
    hB_sum := fun k _ _ => by
      rw [add_zero, add_zero]
      refine intervalIntegral.integral_mono_on (by linarith only [hR_10, huT_lo])
        (by
          have hP2_cont : ContinuousOn (fun v : ℝ => (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re)
              (Icc (-R) u_T) :=
            Complex.continuous_re.comp_continuousOn ((analyticOnNhd_const.mul hAn).continuousOn.comp
              continuous_ofReal.continuousOn fun v hv => by
                rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
                exact abs_lt.mpr ⟨by linarith only [hlo_ball, hu_lo_le, hv.1],
                  by linarith only [hhi_ball, hR_uhi, hR_10, huT_hi, hv.2]⟩)
          exact ((continuousOn_id.neg.div_const R).mul hP2_cont).intervalIntegrable_of_Icc
            (by linarith only [hR_10, huT_lo]))
        (by
          have hP2_cont : ContinuousOn (fun v : ℝ => (((2 : ℝ) : ℂ) * spinPtilde c Φ (v : ℂ)).re)
              (Icc (-R) u_T) :=
            Complex.continuous_re.comp_continuousOn ((analyticOnNhd_const.mul hAn).continuousOn.comp
              continuous_ofReal.continuousOn fun v hv => by
                rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
                exact abs_lt.mpr ⟨by linarith only [hlo_ball, hu_lo_le, hv.1],
                  by linarith only [hhi_ball, hR_uhi, hR_10, huT_hi, hv.2]⟩)
          exact (((continuous_const.min ((continuous_const.mul continuous_neg).div_const R)).continuousOn).mul
            hP2_cont).intervalIntegrable_of_Icc (by linarith only [hR_10, huT_lo]))
        fun v hv => by
          have hv1 : (-v) / R ≤ 1 := (div_le_one hR_pos).mpr (by linarith only [hv.1])
          have hvk : (-v) / R ≤ ((k : ℝ) + 1) * (-v) / R :=
            div_le_div_of_nonneg_right (le_mul_of_one_le_left (by linarith only [hv.2, huT_hi]) (by linarith only)) hR_pos.le
          exact mul_le_mul_of_nonneg_right (le_min hv1 hvk) (hΨ_nn_bandR v hv)
    hP_le := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hn_pos.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 := hℓ_mem.2.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
      exact spin_quad_arc_bound hC_env_pos hς_nn hn_c12 hς_unc_R hR_10
        (hR_uhi.trans_lt hhi_ball) hAn hℓ_nn hℓ_half hL_exp_ub hEnv_2 hD hRp hRm
        (by exact_mod_cast hk0)
    hArc_cov := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_pos : 0 < ℓ := lt_of_lt_of_le (by have : P.D_1 = 1 := rfl; rw [this]; positivity) hℓ_mem.1
      have hle := spinArcCov_le hC_env_pos.le hR_10 (zero_le_one.trans hL_lb) hℓ_pos (by exact_mod_cast hk0)
      exact hle.trans (by
        have hCa : spinArcCovConst C_env ≤ P.C_a := le_max_left _ _
        gcongr)
    hArc_unc := le_rfl
    C_vac := C_vac
    η_vac := η_vac
    C_N := tebLambdaN P 0
    θ := tebThetaHB P 0
    a_N := P.κ_star / (4 * P.w_star)
    hCvac := hC_vac_nn
    hη_vac_nn := hη_nn
    hη_vac_ub := hη_ub
    hCN := tebLambdaN_nonneg P le_rfl
    hθ_pos := tebThetaHB_pos P le_rfl
    hθ_half := tebThetaHB_le_half P 0
    haN_pos := div_pos P.hκ_star (mul_pos (by norm_num) P.hw_star)
    hI_line_vac := fun k ℓ hk0 hkR hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hn_pos.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 := hℓ_mem.2.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
      have hlb := spin_line_bound hc40 rfl hrd_pos (hcA_eq ▸ virasoroBV_pos : 0 < cA) (rfl : C_env = 2 * C_κ51)
        hCκ_pos hς_half hR_10 hℓ_nn hℓ_half hu_lo_le hR_uhi hlo_ball hhi_ball huhi_cA huT_lo huT_hi hRdom_ge4
        hR_dom_lt_ball hAn hEnv_1 hΨ_nn_uT hL1_dom hWin (by exact_mod_cast hk0) hkR
      have hCa : 4 * Real.exp (6 / 5) + 3 * C_env ≤ P.C_a := le_max_right _ _
      have h_ca_term : (4 * Real.exp (6 / 5) + 3 * C_env) * ((k : ℝ) + 1) / R ≤
          P.C_a * ((k : ℝ) + 1) / R := by gcongr
      linarith only [hlb, h_ca_term]
    hP_nodes_lb := fun k ℓ hk0 hkR hℓ_mem => hPN.1 k ℓ hk0 hkR hℓ_mem
    hP_theta_lb := fun k hk0 hk0_R hℓ_mem => hPN.2 k hk0 hk0_R hℓ_mem
  }
  have hK := teb_weak_K_log_bound P W hn_tebC2
  have hlog_ge1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn_pos]
    have hexp3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
    linarith only [hexp3, hn_ge4096]
  have hlogW_le : 1 + Real.log W.L ≤ (1 + Real.log P.C_L + P.γ) * Real.log n := by
    have h1 : Real.log W.L ≤ Real.log (P.C_L * n ^ P.γ) := Real.log_le_log (by linarith only [hL_lb]) hL_ub
    have hCL_pos : 0 < P.C_L := lt_of_lt_of_le zero_lt_one P.hCL
    rw [Real.log_mul hCL_pos.ne' (Real.rpow_pos_of_pos hn_pos _).ne', Real.log_rpow hn_pos] at h1
    have h1log : 1 + Real.log P.C_L + P.γ * Real.log n ≤ (1 + Real.log P.C_L + P.γ) * Real.log n := by
      have hlog_CL : 0 ≤ Real.log P.C_L := Real.log_nonneg P.hCL
      nlinarith only [hlog_ge1, hlog_CL, P.hγ]
    linarith only [h1, h1log]
  calc n ^ (1 / 3 : ℝ) * (u_T - airyZero 1) = W.c ^ (1 / 3 : ℝ) * W.x_tilde := rfl
    _ ≤ CK * (1 + Real.log W.L) := hK
    _ ≤ CK * ((1 + Real.log P.C_L + P.γ) * Real.log n) := mul_le_mul_of_nonneg_left hlogW_le hCK_pos.le
    _ = C_loc * Real.log n := by dsimp [C_loc]; ring

end NodesAndBootstrap

end FormalResearch.ModularBootstrap.Spin
