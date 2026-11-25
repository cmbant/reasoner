module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCEnvelopeAssembled
public import FormalResearch.JacobiEigenvectors.Charts.PCEnvWellFar
public import FormalResearch.JacobiEigenvectors.Charts.PCLaplace
public import FormalResearch.JacobiEigenvectors.Charts.PCPositive
public import FormalResearch.JacobiEigenvectors.Charts.PCBeyond
public import FormalResearch.JacobiEigenvectors.Charts.PCExact
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftWeights

/-!
# Paper J, charts (WP1b): far-zone positivity and growth for `pcV` (`a ≤ 0`) and `pcU(-·)` (`a > 0`)

Formalises the missing `V_growth` input needed for `SoftEdgeChart.grow3` (`SoftParabolicCylinder.lean`):
* `pcV_far_pos_and_growth`: for all `a ≤ 0` and `z ≥ max (z2Airy a) 10` (with action
  `∫_{2√(-a)}^z √(t²/4 + a) dt ≥ C₂`), we have
  `vt pcV a z ≥ c_V * (Ewell a z)⁻¹ * Mbal a z > 0`, `deriv (vt pcV a) z > 0`, and
  `deriv (vt pcV a) z ≥ (1 / 4) * Real.sqrt (k2 a z) * vt pcV a z`.
* `pcU_neg_pos_and_growth`: for all `a > 0` and `z ≥ 0`, `kappaBal a * pcU a (-z) > 0`,
  `0 ≤ deriv (fun w => kappaBal a * pcU a (-w)) z ≤ 4 * Real.sqrt (k2 a z) * (kappaBal a * pcU a (-z))`,
  and `kappaBal a * pcU a (-z) ≥ c_bar / √17 * (Ebar a z)⁻¹ * Mbal a z`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Set Real intervalIntegral

private lemma diff_vt_at' (a z : ℝ) : DifferentiableAt ℝ (vt pcV a) z :=
  ((hasDerivAt_pcV a z).const_mul _).differentiableAt

private lemma diff_ut_at' (a z : ℝ) : DifferentiableAt ℝ (ut pcU a) z :=
  ((hasDerivAt_pcU a z).const_mul (kappaBal a)).differentiableAt

private lemma k2_eq_p_far {a z : ℝ} (ha : a ≤ 0) (hz : max (z2Airy a) 10 ≤ z) :
    k2 a z = z ^ 2 / 4 + a ∧ 0 < z ^ 2 / 4 + a := by
  have hz10 : 10 ≤ z := le_trans (le_max_right _ _) hz
  have hza : z2Airy a ≤ z := le_trans (le_max_left _ _) hz
  by_cases ha4 : a ≤ -4
  · have hp := p_well_pos ha4 (lt_of_lt_of_le (z2Airy_gt_turning ha4) hza)
    exact ⟨k2_well_far_eq ha4 hza, hp⟩
  · push_neg at ha4
    have hp : 21 ≤ z ^ 2 / 4 + a := by nlinarith
    have hm : max |a| 1 ^ ((1 : ℝ) / 3) ≤ 4 := by
      have hm4 : max |a| 1 ≤ 4 := max_le (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
      calc max |a| 1 ^ ((1 : ℝ) / 3) ≤ 4 ^ ((1 : ℝ) / 3) :=
            Real.rpow_le_rpow (by positivity) hm4 (by norm_num)
        _ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 := Real.rpow_one 4
    have hk : k2 a z = z ^ 2 / 4 + a := by
      unfold k2
      rw [abs_of_pos (by linarith), max_eq_left (by linarith)]
    exact ⟨hk, by linarith⟩

private lemma two_sqrt_neg_le_max {a : ℝ} (ha : a ≤ 0) :
    2 * Real.sqrt (-a) < max (z2Airy a) 10 := by
  by_cases ha4 : a ≤ -4
  · exact lt_of_lt_of_le (z2Airy_gt_turning ha4) (le_max_left _ _)
  · push_neg at ha4
    have hsq : Real.sqrt (-a) < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; linarith
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

/-- Action integral `S_well(a, z) = ∫_{2√(-a)}^z √(t²/4 + a) dt` for `a ≤ 0 ≤ z`. -/
def actionWell (a z : ℝ) : ℝ :=
  ∫ t in (2 * Real.sqrt (-a))..z, Real.sqrt (t ^ 2 / 4 + a)

lemma Ewell_eq_exp_action {a z : ℝ} (ha : a ≤ 0) (hz : 2 * Real.sqrt (-a) ≤ z) :
    Ewell a z = Real.exp (-actionWell a z) := by
  unfold Ewell actionWell
  rw [abs_of_nonpos ha]
  split_ifs with hgt
  · simp only [sub_neg_eq_add]
  · have hzeq : z = 2 * Real.sqrt (-a) := le_antisymm (not_lt.mp hgt) hz
    rw [hzeq, intervalIntegral.integral_same, neg_zero, Real.exp_zero]

lemma actionWell_sub {a z₁ z₂ : ℝ} (ha : a ≤ 0) :
    actionWell a z₂ - actionWell a z₁ = ∫ t in z₁..z₂, Real.sqrt (t ^ 2 / 4 + a) := by
  unfold actionWell
  have hc : Continuous (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a)) := by fun_prop
  have h1 : IntervalIntegrable (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a))
      MeasureTheory.volume (2 * Real.sqrt (-a)) z₁ := hc.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a))
      MeasureTheory.volume z₁ z₂ := hc.intervalIntegrable _ _
  linarith [intervalIntegral.integral_add_adjacent_intervals h1 h2]

lemma actionWell_ge_ratio_k2 {a z : ℝ} (ha : a ≤ 0) (hz : max (z2Airy a) 10 ≤ z) :
    (k2 a z / k2 a (2 * Real.sqrt (-a))) ^ ((1 : ℝ) / 4) ≤ 8 + 8 * actionWell a z := by
  set z₀ := 2 * Real.sqrt (-a)
  have hz₀_lt : z₀ < z := lt_of_lt_of_le (two_sqrt_neg_le_max ha) hz
  have hS0 : 0 ≤ actionWell a z := by
    unfold actionWell
    exact intervalIntegral.integral_nonneg hz₀_lt.le fun t _ => Real.sqrt_nonneg _
  have hkp := k2_eq_p_far ha hz
  have hk_z : k2 a z = z ^ 2 / 4 + a := hkp.1
  have hp_z : 0 < z ^ 2 / 4 + a := hkp.2
  have hk_z0 : k2 a z₀ = max |a| 1 ^ ((1 : ℝ) / 3) := by
    unfold k2
    have h0 : z₀ ^ 2 / 4 + a = 0 := by
      dsimp [z₀]; rw [mul_pow, Real.sq_sqrt (neg_nonneg.mpr ha)]; ring
    rw [h0, abs_zero, max_eq_right]
    positivity
  have hM1 : 1 ≤ max |a| 1 := le_max_right _ _
  have hk_z0_ge1 : 1 ≤ k2 a z₀ := by
    rw [hk_z0]; exact Real.one_le_rpow hM1 (by norm_num)
  by_cases hcase : z ^ 2 / 4 + a ≤ 100 * k2 a z₀
  · have hdiv : k2 a z / k2 a z₀ ≤ 100 := by
      rw [hk_z, div_le_iff₀ (by linarith)]; exact hcase
    have hrp : (k2 a z / k2 a z₀) ^ ((1 : ℝ) / 4) ≤ (100 : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (div_nonneg (k2_pos a z).le (k2_pos a z₀).le) hdiv (by norm_num)
    have h100 : (100 : ℝ) ^ ((1 : ℝ) / 4) ≤ 8 := by
      rw [← Real.rpow_le_rpow_iff (by positivity) (by norm_num) (show (0 : ℝ) < 4 by norm_num),
        ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith [hS0]
  · push_neg at hcase
    let xm := (z₀ + z) / 2
    have hx_lo : z₀ ≤ xm := by dsimp [xm]; linarith
    have hx_hi : xm ≤ z := by dsimp [xm]; linarith
    have hmono : ∀ t ∈ Icc xm z, Real.sqrt (xm ^ 2 / 4 + a) ≤ Real.sqrt (t ^ 2 / 4 + a) := by
      intro t ht
      apply Real.sqrt_le_sqrt
      have hxm0 : 0 ≤ xm := le_trans (by positivity) hx_lo
      nlinarith [ht.1]
    have hS_sub : (z - xm) * Real.sqrt (xm ^ 2 / 4 + a) ≤ actionWell a z := by
      have hc : Continuous (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a)) := by fun_prop
      have hint1 : 0 ≤ ∫ t in z₀..xm, Real.sqrt (t ^ 2 / 4 + a) :=
        intervalIntegral.integral_nonneg hx_lo fun t _ => Real.sqrt_nonneg _
      have hint2 : ∫ t in xm..z, Real.sqrt (xm ^ 2 / 4 + a) ≤
          ∫ t in xm..z, Real.sqrt (t ^ 2 / 4 + a) :=
        intervalIntegral.integral_mono_on hx_hi intervalIntegrable_const
          (hc.intervalIntegrable _ _) hmono
      rw [intervalIntegral.integral_const, smul_eq_mul] at hint2
      have hsplit : actionWell a z = (∫ t in z₀..xm, Real.sqrt (t ^ 2 / 4 + a)) +
          (∫ t in xm..z, Real.sqrt (t ^ 2 / 4 + a)) := by
        unfold actionWell
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
      linarith
    have hz0_sq : z₀ ^ 2 = 4 * (-a) := by
      dsimp [z₀]; rw [mul_pow, Real.sq_sqrt (neg_nonneg.mpr ha)]; ring
    have hp_fact : z ^ 2 / 4 + a = (z - z₀) * (z + z₀) / 4 := by linarith [hz0_sq]
    have hxm_fact : xm ^ 2 / 4 + a = (xm - z₀) * (xm + z₀) / 4 := by linarith [hz0_sq]
    have hxm_ge : (z ^ 2 / 4 + a) / 4 ≤ xm ^ 2 / 4 + a := by
      have e1 : xm - z₀ = (z - z₀) / 2 := by dsimp [xm]; ring
      have e2 : (z + z₀) / 2 ≤ xm + z₀ := by
        have hz0_nn : 0 ≤ z₀ := by positivity
        dsimp [xm]; linarith
      rw [hxm_fact, e1, hp_fact]
      have hz0_pos : 0 ≤ z - z₀ := by linarith
      have hzs : 0 ≤ z + z₀ := by linarith [show 0 ≤ z₀ by positivity]
      nlinarith
    have hsqrt_xm : Real.sqrt (z ^ 2 / 4 + a) / 2 ≤ Real.sqrt (xm ^ 2 / 4 + a) := by
      have := Real.sqrt_le_sqrt hxm_ge
      rwa [Real.sqrt_div (by linarith), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    have hz_xm : z - xm = (z - z₀) / 2 := by dsimp [xm]; ring
    have hS_prod : (z - z₀) * Real.sqrt (z ^ 2 / 4 + a) / 4 ≤ actionWell a z := by
      have hmul := mul_le_mul_of_nonneg_left hsqrt_xm (by linarith : 0 ≤ z - xm)
      rw [hz_xm] at hmul hS_sub
      linarith
    by_cases hz2 : 2 * z₀ ≤ z
    · have hz_ge : z / 2 ≤ z - z₀ := by linarith
      have hS_big : (z ^ 2 / 4 + a) / (4 * Real.sqrt 2) ≤ actionWell a z := by
        have hz_sub_lb : Real.sqrt (z ^ 2 / 4 + a) ≤ z / 2 := by
          rw [Real.sqrt_le_iff]; refine ⟨by linarith [show 0 ≤ z₀ by positivity], ?_⟩
          nlinarith [show 0 ≤ -a by linarith]
        have hmul : Real.sqrt (z ^ 2 / 4 + a) * Real.sqrt (z ^ 2 / 4 + a) ≤
            (z - z₀) * Real.sqrt (z ^ 2 / 4 + a) := by
          have hz_sub_le : Real.sqrt (z ^ 2 / 4 + a) ≤ z - z₀ := le_trans hz_sub_lb hz_ge
          exact mul_le_mul_of_nonneg_right hz_sub_le (Real.sqrt_nonneg _)
        rw [Real.mul_self_sqrt hp_z.le] at hmul
        have h4 : (z ^ 2 / 4 + a) / 4 ≤ actionWell a z := by linarith
        have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
        have h4le : 4 ≤ 4 * Real.sqrt 2 := by linarith
        calc (z ^ 2 / 4 + a) / (4 * Real.sqrt 2) ≤ (z ^ 2 / 4 + a) / 4 :=
              div_le_div_of_nonneg_left hp_z.le (by norm_num) h4le
          _ ≤ actionWell a z := h4
      have hrat : k2 a z / k2 a z₀ ≤ 4 * Real.sqrt 2 * actionWell a z := by
        rw [hk_z]
        calc (z ^ 2 / 4 + a) / k2 a z₀ ≤ (z ^ 2 / 4 + a) / 1 := div_le_div_of_nonneg_left hp_z.le one_pos hk_z0_ge1
          _ = z ^ 2 / 4 + a := div_one _
          _ ≤ 4 * Real.sqrt 2 * actionWell a z := by
              have h4 : 0 < 4 * Real.sqrt 2 := by positivity
              calc z ^ 2 / 4 + a = (4 * Real.sqrt 2) * ((z ^ 2 / 4 + a) / (4 * Real.sqrt 2)) := by field_simp
                _ ≤ (4 * Real.sqrt 2) * actionWell a z := mul_le_mul_of_nonneg_left hS_big h4.le
      have h42 : (4 * Real.sqrt 2 * actionWell a z) ≤ (8 + 8 * actionWell a z) ^ (4 : ℝ) := by
        have hsqrt2_le : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have hlin : 4 * Real.sqrt 2 * actionWell a z ≤ 8 * actionWell a z := by
          exact mul_le_mul_of_nonneg_right (by linarith) hS0
        have h1 : 1 ≤ 8 + 8 * actionWell a z := by linarith
        have hp : 8 + 8 * actionWell a z ≤ (8 + 8 * actionWell a z) ^ (4 : ℕ) := by
          simpa using pow_le_pow_right₀ h1 (by norm_num : 1 ≤ 4)
        have hrp : (8 + 8 * actionWell a z) ^ (4 : ℝ) = (8 + 8 * actionWell a z) ^ (4 : ℕ) := by
          norm_cast
        rw [hrp]
        linarith
      calc (k2 a z / k2 a z₀) ^ ((1 : ℝ) / 4)
          ≤ (4 * Real.sqrt 2 * actionWell a z) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (div_nonneg (k2_pos _ _).le (k2_pos _ _).le) hrat (by norm_num)
        _ ≤ ((8 + 8 * actionWell a z) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (by positivity) h42 (by norm_num)
        _ = 8 + 8 * actionWell a z := by
            rw [← Real.rpow_mul (by positivity)]; norm_num
    · push_neg at hz2
      have hzz0 : z + z₀ ≤ 3 * z₀ := by linarith
      have hz0_pos : 0 < z₀ := by
        by_contra h0
        push_neg at h0
        have hz0_0 : z₀ = 0 := le_antisymm h0 (by positivity)
        linarith [show 10 ≤ z from le_trans (le_max_right _ _) hz]
      have hsub_ge : 4 * (z ^ 2 / 4 + a) / (3 * z₀) ≤ z - z₀ := by
        rw [div_le_iff₀ (by positivity), hp_fact]
        nlinarith [show 0 ≤ z - z₀ by linarith]
      have hS_p32 : (z ^ 2 / 4 + a) ^ ((3 : ℝ) / 2) / (3 * z₀) ≤ actionWell a z := by
        have h32 : (z ^ 2 / 4 + a) ^ ((3 : ℝ) / 2) = (z ^ 2 / 4 + a) * Real.sqrt (z ^ 2 / 4 + a) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hp_z.le (by norm_num)]; norm_num
        rw [h32, div_le_iff₀ (by positivity)]
        have hm1 : 4 * (z ^ 2 / 4 + a) / (3 * z₀) * Real.sqrt (z ^ 2 / 4 + a) ≤
            (z - z₀) * Real.sqrt (z ^ 2 / 4 + a) :=
          mul_le_mul_of_nonneg_right hsub_ge (Real.sqrt_nonneg (z ^ 2 / 4 + a))
        calc (z ^ 2 / 4 + a) * Real.sqrt (z ^ 2 / 4 + a)
            = (4 * (z ^ 2 / 4 + a) / (3 * z₀) * Real.sqrt (z ^ 2 / 4 + a)) * (3 * z₀ / 4) := by
              field_simp [hz0_pos.ne']
          _ ≤ ((z - z₀) * Real.sqrt (z ^ 2 / 4 + a)) * (3 * z₀ / 4) :=
              mul_le_mul_of_nonneg_right hm1 (by positivity)
          _ ≤ (4 * actionWell a z) * (3 * z₀ / 4) :=
              mul_le_mul_of_nonneg_right (by linarith [hS_prod]) (by positivity)
          _ = actionWell a z * (3 * z₀) := by ring
      have hrat_pow : (k2 a z / k2 a z₀) ^ ((3 : ℝ) / 2) ≤ 6 * actionWell a z := by
        have hz0_bd : z₀ ≤ 2 * (max |a| 1) ^ ((1 : ℝ) / 2) := by
          dsimp [z₀]
          rw [← Real.sqrt_eq_rpow]
          gcongr
          rw [abs_of_nonpos ha]
          exact le_max_left _ _
        have hdenom : (k2 a z₀) ^ ((3 : ℝ) / 2) = (max |a| 1) ^ ((1 : ℝ) / 2) := by
          rw [hk_z0, ← Real.rpow_mul (by positivity)]; norm_num
        rw [Real.div_rpow (k2_pos _ _).le (k2_pos _ _).le, hk_z, hdenom]
        calc (z ^ 2 / 4 + a) ^ ((3 : ℝ) / 2) / max |a| 1 ^ ((1 : ℝ) / 2)
            = 6 * ((z ^ 2 / 4 + a) ^ ((3 : ℝ) / 2) / (3 * (2 * max |a| 1 ^ ((1 : ℝ) / 2)))) := by
              field_simp; ring
          _ ≤ 6 * ((z ^ 2 / 4 + a) ^ ((3 : ℝ) / 2) / (3 * z₀)) := by
              gcongr
          _ ≤ 6 * actionWell a z := mul_le_mul_of_nonneg_left hS_p32 (by norm_num)
      have h6_exp : (k2 a z / k2 a z₀) ^ ((1 : ℝ) / 4) ≤ (6 * actionWell a z) ^ ((1 : ℝ) / 6) := by
        have h16 : (k2 a z / k2 a z₀) ^ ((1 : ℝ) / 4) =
            ((k2 a z / k2 a z₀) ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 6) := by
          rw [← Real.rpow_mul (div_nonneg (k2_pos _ _).le (k2_pos _ _).le)]; norm_num
        rw [h16]
        exact Real.rpow_le_rpow (Real.rpow_nonneg (div_nonneg (k2_pos _ _).le (k2_pos _ _).le) _) hrat_pow (by norm_num)
      have hr6 : (6 * actionWell a z) ^ ((1 : ℝ) / 6) ≤ 8 + 8 * actionWell a z := by
        have hge : 1 ≤ 8 + 8 * actionWell a z := by linarith
        calc (6 * actionWell a z) ^ ((1 : ℝ) / 6)
            ≤ (8 + 8 * actionWell a z) ^ ((1 : ℝ) / 6) :=
              Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
          _ ≤ (8 + 8 * actionWell a z) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hge (by norm_num)
          _ = 8 + 8 * actionWell a z := Real.rpow_one _
      exact h6_exp.trans hr6

/-- Helper: `ut pcU a z ≥ c3 * Ewell a z * Mbal a z` and `ut ≤ CPC * Ewell * Mbal` yield the
`vt / ut` integral lower bound cleanly on `[z₀, z]` for `a ≤ 0` and `z₀ = 2√(-a) ≤ z`. -/
lemma vt_far_lower_of_action {cPC CPC : ℝ} (hcPC : 0 < cPC) (hCPC : cPC ≤ CPC)
    (env : PCEnvelopeFacts pcU pcV cPC CPC)
    {a z : ℝ} (ha : a ≤ 0) (hz : 2 * Real.sqrt (-a) ≤ z)
    (hact : 4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2 ≤ Real.exp (2 * actionWell a z)) :
    let c3 := cPC / Real.sqrt 17
    c3 / (4 * CPC ^ 2) * (Ewell a z)⁻¹ * Mbal a z ≤ vt pcV a z := by
  intro c3
  have hCPC_pos : 0 < CPC := lt_of_lt_of_le hcPC hCPC
  set z₀ := 2 * Real.sqrt (-a)
  have hu_pos : ∀ t ∈ Icc z₀ z, 0 < ut pcU a t := fun t ht => by
    have hmax : 2 * Real.sqrt (max (-a) 0) ≤ t := by
      rw [max_eq_left (neg_nonneg.mpr ha)]; exact ht.1
    exact mul_pos (kappaBal_pos a) (pcU_pos_beyond a t hmax)
  have hut_lb : ∀ t, z₀ ≤ t → c3 * Ewell a t * Mbal a t ≤ ut pcU a t := fun t ht => by
    have hmax : 2 * Real.sqrt (max (-a) 0) ≤ t := by
      rw [max_eq_left (neg_nonneg.mpr ha)]; exact ht
    have hb := (env.beyond a t hmax).2
    have he : Erec a t = Ewell a t := by
      unfold Erec; rw [if_pos ha, abs_of_nonneg (le_trans (by positivity) ht)]
    rw [he] at hb
    exact hb.trans_eq (abs_of_pos (mul_pos (kappaBal_pos a) (pcU_pos_beyond a t hmax)))
  have hut_ub : ∀ t, 0 ≤ t → ut pcU a t ≤ CPC * Ewell a t * Mbal a t := fun t ht => by
    have hw := (env.env_well a ha t ht).1
    have hle : |ut pcU a t| ≤ Real.sqrt (ut pcU a t ^ 2 + (kappaBal a * deriv (pcU a) t) ^ 2 / k2 a t) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (k2_pos a t).le))
    exact (le_abs_self _).trans (hle.trans hw)
  have hvt_ub : ∀ t, 0 ≤ t → |vt pcV a t| ≤ CPC * (Ewell a t)⁻¹ * Mbal a t := fun t ht => by
    have hw := (env.env_well a ha t ht).2
    have hle : |vt pcV a t| ≤
        Real.sqrt (vt pcV a t ^ 2 + (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) t) ^ 2 / k2 a t) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (k2_pos a t).le))
    exact hle.trans hw
  have hdiv_deriv : ∀ t ∈ Icc z₀ z,
      HasDerivAt (fun s => vt pcV a s / ut pcU a s) (1 / ut pcU a t ^ 2) t := fun t ht => by
    have hu0 : ut pcU a t ≠ 0 := (hu_pos t ht).ne'
    have h1 := ((diff_vt_at' a t).hasDerivAt).div ((diff_ut_at' a t).hasDerivAt) hu0
    refine h1.congr_deriv ?_
    have hwr := pc_wronsk a t
    have hdu : deriv (ut pcU a) t = kappaBal a * deriv (pcU a) t := by
      change deriv (fun s => kappaBal a * pcU a s) t = _
      exact deriv_const_mul _ (hasDerivAt_pcU a t).differentiableAt
    have hdv : deriv (vt pcV a) t = Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) t := by
      change deriv (fun s => _ * pcV a s) t = _
      exact deriv_const_mul _ (hasDerivAt_pcV a t).differentiableAt
    have hnum : deriv (vt pcV a) t * ut pcU a t - vt pcV a t * deriv (ut pcU a) t = 1 := by
      have hκ := (kappaBal_pos a).ne'
      have hpi : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
        rw [← Real.sqrt_mul (by positivity)]; norm_num
      dsimp [ut, vt]
      rw [hdu, hdv]
      calc Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) t * (kappaBal a * pcU a t) -
            Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * pcV a t * (kappaBal a * deriv (pcU a) t)
          = Real.sqrt (Real.pi / 2) * (kappaBal a * (kappaBal a)⁻¹) *
              (pcU a t * deriv (pcV a) t - deriv (pcU a) t * pcV a t) := by ring
        _ = Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) := by
              rw [mul_inv_cancel₀ hκ, hwr]; ring
        _ = 1 := hpi
    rw [hnum]
  have hcont_div : ContinuousOn (fun t => 1 / ut pcU a t ^ 2) (Icc z₀ z) := by
    refine continuousOn_const.div ?_ fun t ht => pow_ne_zero 2 (hu_pos t ht).ne'
    exact ((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_pcU a t).continuousAt).const_mul _).continuousOn.pow 2
  have hint_q : vt pcV a z / ut pcU a z - vt pcV a z₀ / ut pcU a z₀ =
      ∫ t in z₀..z, 1 / ut pcU a t ^ 2 := by
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := fun s => vt pcV a s / ut pcU a s) hz ?_ ?_
      (hcont_div.intervalIntegrable_of_Icc hz)).symm
    · exact ContinuousOn.div
        ((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_pcV a t).continuousAt).const_mul _).continuousOn
        ((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_pcU a t).continuousAt).const_mul _).continuousOn
        fun t ht => (hu_pos t ht).ne'
    · intro t ht; exact hdiv_deriv t (Ioo_subset_Icc_self ht)
  have hE_deriv : ∀ t ∈ Icc z₀ z,
      HasDerivAt (fun s => Real.exp (2 * ∫ τ in z₀..s, Real.sqrt (τ ^ 2 / 4 + a)))
        (2 * Real.sqrt (t ^ 2 / 4 + a) *
          Real.exp (2 * ∫ τ in z₀..t, Real.sqrt (τ ^ 2 / 4 + a))) t := fun t _ => by
    have hc : Continuous (fun τ : ℝ => Real.sqrt (τ ^ 2 / 4 + a)) := by fun_prop
    have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable z₀ t)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
    exact ((hd.const_mul 2).exp).congr_deriv (by ring)
  have hcont_E : Continuous (fun t => 2 * Real.sqrt (t ^ 2 / 4 + a) *
      Real.exp (2 * ∫ τ in z₀..t, Real.sqrt (τ ^ 2 / 4 + a))) := by
    have hc : Continuous (fun τ : ℝ => Real.sqrt (τ ^ 2 / 4 + a)) := by fun_prop
    refine (continuous_const.mul hc).mul (Real.continuous_exp.comp (continuous_const.mul ?_))
    exact continuous_primitive (fun a' b' => hc.intervalIntegrable a' b') z₀
  have hcont_Ef : Continuous (fun s => Real.exp (2 * ∫ τ in z₀..s, Real.sqrt (τ ^ 2 / 4 + a))) := by
    have hc : Continuous (fun τ : ℝ => Real.sqrt (τ ^ 2 / 4 + a)) := by fun_prop
    exact Real.continuous_exp.comp (continuous_const.mul (continuous_primitive (fun a' b' => hc.intervalIntegrable a' b') z₀))
  have hint_E : (Ewell a z)⁻¹ ^ 2 - 1 =
      ∫ t in z₀..z, 2 * Real.sqrt (t ^ 2 / 4 + a) *
        Real.exp (2 * ∫ τ in z₀..t, Real.sqrt (τ ^ 2 / 4 + a)) := by
    have heq : (Ewell a z)⁻¹ ^ 2 - 1 =
        Real.exp (2 * ∫ τ in z₀..z, Real.sqrt (τ ^ 2 / 4 + a)) -
        Real.exp (2 * ∫ τ in z₀..z₀, Real.sqrt (τ ^ 2 / 4 + a)) := by
      have hEz : Ewell a z = Real.exp (-(∫ τ in z₀..z, Real.sqrt (τ ^ 2 / 4 + a))) :=
        Ewell_eq_exp_action ha hz
      rw [hEz, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul, intervalIntegral.integral_same,
        mul_zero, Real.exp_zero]
      simp
    rw [heq]
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := fun s => Real.exp (2 * ∫ τ in z₀..s, Real.sqrt (τ ^ 2 / 4 + a))) hz
      hcont_Ef.continuousOn
      (fun t ht => hE_deriv t (Ioo_subset_Icc_self ht))
      (hcont_E.intervalIntegrable z₀ z)).symm
  have hpt : ∀ t ∈ Icc z₀ z,
      2 * Real.sqrt (t ^ 2 / 4 + a) * Real.exp (2 * ∫ τ in z₀..t, Real.sqrt (τ ^ 2 / 4 + a)) ≤
      2 * CPC ^ 2 * (1 / ut pcU a t ^ 2) := fun t ht => by
    have ht0 : 0 ≤ t := le_trans (by positivity) ht.1
    have hEt : Ewell a t = Real.exp (-(∫ τ in z₀..t, Real.sqrt (τ ^ 2 / 4 + a))) :=
      Ewell_eq_exp_action ha ht.1
    have hExp_eq : Real.exp (2 * ∫ τ in z₀..t, Real.sqrt (τ ^ 2 / 4 + a)) = (Ewell a t)⁻¹ ^ 2 := by
      rw [hEt, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul]
      simp
    have hp_le_k2 : Real.sqrt (t ^ 2 / 4 + a) ≤ (Mbal a t)⁻¹ ^ 2 := by
      have hp0 : 0 ≤ t ^ 2 / 4 + a := by
        have h2s : z₀ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) ht.1 2
        have hz0_sq : z₀ ^ 2 = 4 * (-a) := by
          dsimp [z₀]; rw [mul_pow, Real.sq_sqrt (neg_nonneg.mpr ha)]; ring
        linarith
      have hpk : t ^ 2 / 4 + a ≤ k2 a t := by
        unfold k2
        calc t ^ 2 / 4 + a ≤ |t ^ 2 / 4 + a| := le_abs_self _
          _ ≤ max |t ^ 2 / 4 + a| (max |a| 1 ^ ((1 : ℝ) / 3)) := le_max_left _ _
      have hM2 : (Mbal a t)⁻¹ ^ 2 = Real.sqrt (k2 a t) := by
        unfold Mbal
        rw [show (-(1 : ℝ) / 4 : ℝ) = -((1 : ℝ) / 4) by norm_num, Real.rpow_neg (k2_pos a t).le,
          inv_inv, ← Real.rpow_natCast, ← Real.rpow_mul (k2_pos a t).le, Real.sqrt_eq_rpow]
        norm_num
      rw [hM2]; exact Real.sqrt_le_sqrt hpk
    have hu_t : ut pcU a t ≤ CPC * Ewell a t * Mbal a t := hut_ub t ht0
    have hE_pos : 0 < Ewell a t := by rw [hEt]; exact Real.exp_pos _
    have hM_pos : 0 < Mbal a t := Mbal_pos a t
    have hu_t_pos : 0 < ut pcU a t := hu_pos t ht
    have hC_pos : 0 < CPC := hCPC_pos
    have hinv_u : ((Ewell a t)⁻¹ * (Mbal a t)⁻¹) ^ 2 ≤ CPC ^ 2 * (1 / ut pcU a t ^ 2) := by
      have h1 : ut pcU a t ^ 2 ≤ (CPC * Ewell a t * Mbal a t) ^ 2 :=
        pow_le_pow_left₀ hu_t_pos.le hu_t 2
      have hEM_pos : 0 < (Ewell a t * Mbal a t) ^ 2 := pow_pos (mul_pos hE_pos hM_pos) 2
      rw [← mul_inv, inv_pow, mul_one_div, inv_eq_one_div, div_le_div_iff₀ hEM_pos (pow_pos hu_t_pos 2)]
      nlinarith [show (CPC * Ewell a t * Mbal a t) ^ 2 = CPC ^ 2 * (Ewell a t * Mbal a t) ^ 2 by ring]
    rw [hExp_eq]
    calc 2 * Real.sqrt (t ^ 2 / 4 + a) * (Ewell a t)⁻¹ ^ 2
        ≤ 2 * (Mbal a t)⁻¹ ^ 2 * (Ewell a t)⁻¹ ^ 2 := by gcongr
      _ = 2 * ((Ewell a t)⁻¹ * (Mbal a t)⁻¹) ^ 2 := by ring
      _ ≤ 2 * (CPC ^ 2 * (1 / ut pcU a t ^ 2)) := mul_le_mul_of_nonneg_left hinv_u (by norm_num)
      _ = 2 * CPC ^ 2 * (1 / ut pcU a t ^ 2) := by ring
  have hint_comp : (Ewell a z)⁻¹ ^ 2 - 1 ≤
      2 * CPC ^ 2 * (vt pcV a z / ut pcU a z - vt pcV a z₀ / ut pcU a z₀) := by
    rw [hint_E, hint_q, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hz (hcont_E.intervalIntegrable z₀ z)
      ((continuousOn_const.mul hcont_div).intervalIntegrable_of_Icc hz) hpt
  have hz0_nn : 0 ≤ z₀ := by positivity
  have hEz0 : Ewell a z₀ = 1 := by
    rw [Ewell_eq_exp_action ha le_rfl, actionWell, intervalIntegral.integral_same, neg_zero, Real.exp_zero]
  have hq_z0 : |vt pcV a z₀ / ut pcU a z₀| ≤ CPC / c3 := by
    have hvu := hvt_ub z₀ hz0_nn
    have huu := hut_lb z₀ le_rfl
    rw [hEz0, inv_one, mul_one] at hvu
    rw [hEz0, mul_one] at huu
    have hc3 : 0 < c3 := div_pos hcPC (Real.sqrt_pos.mpr (by norm_num))
    have hM0 : 0 ≤ Mbal a z₀ := (Mbal_pos a z₀).le
    have hc3M : 0 < c3 * Mbal a z₀ := mul_pos hc3 (Mbal_pos a z₀)
    rw [abs_div, abs_of_pos (hu_pos z₀ ⟨le_rfl, hz⟩)]
    exact (div_le_div₀ (by positivity) hvu hc3M huu).trans_eq (by field_simp [(Mbal_pos a z₀).ne'])
  have hEz_eq : (Ewell a z)⁻¹ ^ 2 = Real.exp (2 * actionWell a z) := by
    rw [Ewell_eq_exp_action ha hz, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul]
    simp
  have hc3_pos : 0 < c3 := div_pos hcPC (Real.sqrt_pos.mpr (by norm_num))
  have hbig : 4 * CPC ^ 3 / c3 + 2 ≤ (Ewell a z)⁻¹ ^ 2 := by
    rw [hEz_eq]
    dsimp [c3]
    simpa only [div_div_eq_mul_div, mul_comm (4 * CPC ^ 3) (Real.sqrt 17)] using hact
  have hq_lb : (Ewell a z)⁻¹ ^ 2 / (4 * CPC ^ 2) ≤ vt pcV a z / ut pcU a z := by
    have h1 : vt pcV a z₀ / ut pcU a z₀ ≥ -(CPC / c3) := (abs_le.mp hq_z0).1
    have hC2 : 0 < 2 * CPC ^ 2 := by positivity
    have hcomp' : ((Ewell a z)⁻¹ ^ 2 - 1) / (2 * CPC ^ 2) ≤
        vt pcV a z / ut pcU a z - vt pcV a z₀ / ut pcU a z₀ :=
      (div_le_iff₀ hC2).mpr (by linarith [hint_comp])
    have hC4 : 0 < 4 * CPC ^ 2 := by positivity
    have hstep : (Ewell a z)⁻¹ ^ 2 / (4 * CPC ^ 2) + CPC / c3 ≤ ((Ewell a z)⁻¹ ^ 2 - 1) / (2 * CPC ^ 2) := by
      rw [← sub_nonneg]
      have heq : ((Ewell a z)⁻¹ ^ 2 - 1) / (2 * CPC ^ 2) - ((Ewell a z)⁻¹ ^ 2 / (4 * CPC ^ 2) + CPC / c3) =
          ((Ewell a z)⁻¹ ^ 2 - (4 * CPC ^ 3 / c3 + 2)) / (4 * CPC ^ 2) := by
        field_simp [hCPC_pos.ne', hc3_pos.ne']; ring
      rw [heq]; exact div_nonneg (by linarith) hC4.le
    linarith
  have huz : c3 * Ewell a z * Mbal a z ≤ ut pcU a z := hut_lb z hz
  have hEz_pos : 0 < Ewell a z := by rw [Ewell_eq_exp_action ha hz]; exact Real.exp_pos _
  have hvt_den_pos : 0 < ut pcU a z := hu_pos z ⟨hz, le_rfl⟩
  calc c3 / (4 * CPC ^ 2) * (Ewell a z)⁻¹ * Mbal a z
      = ((Ewell a z)⁻¹ ^ 2 / (4 * CPC ^ 2)) * (c3 * Ewell a z * Mbal a z) := by
        field_simp [hEz_pos.ne', hCPC_pos.ne']
    _ ≤ (vt pcV a z / ut pcU a z) * ut pcU a z := by
        have hq_nn : 0 ≤ vt pcV a z / ut pcU a z := le_trans (div_nonneg (sq_nonneg _) (by positivity)) hq_lb
        have hut_nn : 0 ≤ c3 * Ewell a z * Mbal a z :=
          mul_nonneg (mul_nonneg hc3_pos.le hEz_pos.le) (Mbal_pos a z).le
        exact mul_le_mul hq_lb huz hut_nn hq_nn
    _ = vt pcV a z := div_mul_cancel₀ _ hvt_den_pos.ne'

/-- Constant `S_pcV`: universal action threshold above which `pcV > 0`, `pcV' > 0`,
and `pcV' ≥ (1/4) √(k2) pcV`. -/
def actionThreshV (cPC CPC : ℝ) : ℝ :=
  max (Real.log (4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2) / 2) 50 +
    (20 + 4 * Real.log (max 1 (4 * CPC ^ 3 * Real.sqrt 17 / cPC)))

lemma actionThreshV_pos {cPC CPC : ℝ} (hc : 0 < cPC) (hC : cPC ≤ CPC) :
    0 < actionThreshV cPC CPC := by
  unfold actionThreshV
  have h1 : (1 : ℝ) ≤ max 1 (4 * CPC ^ 3 * Real.sqrt 17 / cPC) := le_max_left _ _
  have hlog : 0 ≤ Real.log (max 1 (4 * CPC ^ 3 * Real.sqrt 17 / cPC)) := Real.log_nonneg h1
  have hm : (50 : ℝ) ≤ max (Real.log (4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2) / 2) 50 := le_max_right _ _
  linarith

private lemma fifteen_p32_gt_s {a s : ℝ} (ha : a ≤ 0) (hs : max (z2Airy a) 10 ≤ s) :
    s < 15 * (s ^ 2 / 4 + a) ^ ((3 : ℝ) / 2) := by
  have hp := (k2_eq_p_far ha hs).2
  by_cases ha4 : a ≤ -4
  · have hza : z2Airy a ≤ s := le_trans (le_max_left _ _) hs
    have hA : 4 ≤ -a := by linarith
    have hs0 : 0 ≤ s := le_trans (le_trans (by positivity) (two_sqrt_neg_le_max ha).le) hs
    have hp_ge : 2 * (-a) ^ ((1 : ℝ) / 3) ≤ s ^ 2 / 4 + a := by
      have h1 : (z2Airy a) ^ 2 / 4 + a ≤ s ^ 2 / 4 + a := by
        nlinarith [show 0 ≤ z2Airy a by unfold z2Airy; positivity]
      linarith [p_z2Airy_eq ha4]
    have h2 : (-a) ^ ((1 : ℝ) / 3) ≤ (s ^ 2 / 4 + a) / 2 := by linarith
    have hpow : (s ^ 2 / 4 + a) / 2 ≤ s ^ 2 / 4 + a := by linarith
    have h12 : (2 * (-a) ^ ((1 : ℝ) / 3)) ^ ((3 : ℝ) / 2) ≤ (s ^ 2 / 4 + a) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hp_ge (by norm_num)
    have hsqrt2 : (2 : ℝ) * Real.sqrt 2 ≤ 3 := by
      have : Real.sqrt 2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      linarith
    by_cases hs2 : s ≤ 2 * Real.sqrt 2 * Real.sqrt (-a)
    · have h23 : (2 * (-a) ^ ((1 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = 2 * Real.sqrt 2 * Real.sqrt (-a) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by linarith),
          show ((1 : ℝ) / 3) * (3 / 2) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
          show (2 : ℝ) ^ ((3 : ℝ) / 2) = 2 * Real.sqrt 2 by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by norm_num : (0 : ℝ) ≤ 2) (by norm_num)]; norm_num]
      have hpos_2a : 0 < 2 * Real.sqrt 2 * Real.sqrt (-a) := by positivity
      linarith
    · push_neg at hs2
      have hsq : s ^ 2 / 8 ≤ s ^ 2 / 4 + a := by
        have h8a : 8 * (-a) = (2 * Real.sqrt 2 * Real.sqrt (-a)) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by linarith)]; ring
        have hle2 : (2 * Real.sqrt 2 * Real.sqrt (-a)) ^ 2 ≤ s ^ 2 :=
          pow_le_pow_left₀ (by positivity) hs2.le 2
        linarith
      have hs10 : 10 ≤ s := le_trans (le_max_right _ _) hs
      have hsp : (s ^ 2 / 8) ^ ((3 : ℝ) / 2) ≤ (s ^ 2 / 4 + a) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) hsq (by norm_num)
      have hs8 : s ^ 3 / (16 * Real.sqrt 2) ≤ (s ^ 2 / 8) ^ ((3 : ℝ) / 2) := by
        have heq : (s ^ 2 / 8) ^ ((3 : ℝ) / 2) = (s / (2 * Real.sqrt 2)) ^ 3 := by
          have : s ^ 2 / 8 = (s / (2 * Real.sqrt 2)) ^ 2 := by
            rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
          rw [this, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity),
            show ((2 : ℕ) : ℝ) * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [heq, div_pow, mul_pow, show Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 by
          calc Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
            _ = 2 * Real.sqrt 2 := by rw [Real.sq_sqrt (by norm_num)]]
        ring_nf; rfl
      have hs1 : s < 15 * (s ^ 3 / (16 * Real.sqrt 2)) := by
        have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have h2 : s ^ 2 ≥ 100 := by nlinarith
        have h3 : 100 * s ≤ s ^ 3 := by nlinarith
        have h4 : 16 * Real.sqrt 2 * s ≤ 24 * s := by nlinarith
        rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
        linarith
      nlinarith
  · push_neg at ha4
    have hs10 : 10 ≤ s := le_trans (le_max_right _ _) hs
    have hsq : s ^ 2 / 8 ≤ s ^ 2 / 4 + a := by nlinarith
    have hsp : (s ^ 2 / 8) ^ ((3 : ℝ) / 2) ≤ (s ^ 2 / 4 + a) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hsq (by norm_num)
    have heq : (s ^ 2 / 8) ^ ((3 : ℝ) / 2) = s ^ 3 / (16 * Real.sqrt 2) := by
      have : s ^ 2 / 8 = (s / (2 * Real.sqrt 2)) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
      rw [this, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity),
        show ((2 : ℕ) : ℝ) * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        div_pow, mul_pow, show Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 by
          calc Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
            _ = 2 * Real.sqrt 2 := by rw [Real.sq_sqrt (by norm_num)]]
      ring
    have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hs1 : s < 15 * (s ^ 3 / (16 * Real.sqrt 2)) := by
      have h2 : s ^ 2 ≥ 100 := by nlinarith
      have h3 : 100 * s ≤ s ^ 3 := by nlinarith
      have h4 : 16 * Real.sqrt 2 * s ≤ 24 * s := by nlinarith
      rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
      linarith
    nlinarith

private lemma exp_ge_x4_div24 {x : ℝ} (hx : 0 ≤ x) : x ^ 4 / 24 ≤ Real.exp x := by
  have htaylor := Real.sum_le_exp_of_nonneg hx 5
  have hsum4 : x ^ 4 / ((4 : ℕ).factorial : ℝ) ≤ ∑ i ∈ Finset.range 5, x ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg hx i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (by norm_num))
  have hfact : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfact] at hsum4
  exact hsum4.trans htaylor

private lemma no_exp_small_gap (x : ℝ) (hx : 20 ≤ x) (h : Real.exp (3 / 4 * x) ≤ 448 + 8 * x) : False := by
  have hx0 : 0 ≤ x := by linarith
  have hexp4 := exp_ge_x4_div24 (by linarith : 0 ≤ 3 / 4 * x)
  have h2 : 400 ≤ x ^ 2 := by nlinarith
  have h4 : 160000 ≤ x ^ 4 := by nlinarith
  have hx_le : x ≤ x ^ 4 / 8000 := by
    have hm1 : x ≤ x ^ 2 / 20 := by nlinarith
    have hm2 : x ^ 2 ≤ x ^ 4 / 400 := by nlinarith
    linarith
  have h81 : (3 / 4 * x) ^ 4 / 24 = (27 / 2048 : ℝ) * x ^ 4 := by ring
  linarith

private lemma actionWell_base_le_50 {a : ℝ} (ha : a ≤ 0) :
    actionWell a (max (z2Airy a) 10) ≤ 50 := by
  let z₀ := 2 * Real.sqrt (-a)
  by_cases ha4 : a ≤ -4
  · have hm : max (z2Airy a) 10 = z2Airy a ∨ max (z2Airy a) 10 = 10 := max_choice _ _
    rcases hm with hmz | hm10
    · rw [hmz]
      have hz2_lt : z₀ < z2Airy a := z2Airy_gt_turning ha4
      have hmax_int : ∀ t ∈ Icc z₀ (z2Airy a),
          Real.sqrt (t ^ 2 / 4 + a) ≤ Real.sqrt (2 * (-a) ^ ((1 : ℝ) / 3)) := by
        intro t ht
        apply Real.sqrt_le_sqrt
        have hp_t : t ^ 2 / 4 + a ≤ (z2Airy a) ^ 2 / 4 + a := by
          have hz0_nn : 0 ≤ z₀ := by positivity
          nlinarith [ht.1, ht.2]
        linarith [p_z2Airy_eq ha4]
      have hint : actionWell a (z2Airy a) ≤ (z2Airy a - z₀) * Real.sqrt (2 * (-a) ^ ((1 : ℝ) / 3)) := by
        unfold actionWell
        have hc : Continuous (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a)) := by fun_prop
        have hI1 : IntervalIntegrable (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a))
            MeasureTheory.volume z₀ (z2Airy a) := hc.intervalIntegrable _ _
        have hm' := intervalIntegral.integral_mono_on hz2_lt.le hI1
          intervalIntegrable_const hmax_int
        rw [intervalIntegral.integral_const, smul_eq_mul] at hm'
        exact hm'
      have hz2_diff : z2Airy a - z₀ ≤ 2 * (-a) ^ ((1 : ℝ) / 3) / Real.sqrt (-a) := by
        have hz0_sq : z₀ ^ 2 = 4 * (-a) := by
          dsimp [z₀]; rw [mul_pow, Real.sq_sqrt (by linarith)]; ring
        have hfact : (z2Airy a - z₀) * (z2Airy a + z₀) = 8 * (-a) ^ ((1 : ℝ) / 3) := by
          have := p_z2Airy_eq ha4; linarith [hz0_sq]
        have hsum : 4 * Real.sqrt (-a) ≤ z2Airy a + z₀ := by dsimp [z₀]; linarith
        have hA_pos : 0 < Real.sqrt (-a) := Real.sqrt_pos.mpr (by linarith)
        rw [le_div_iff₀ hA_pos]
        nlinarith [show 0 ≤ z2Airy a - z₀ by linarith]
      have hprod : (z2Airy a - z₀) * Real.sqrt (2 * (-a) ^ ((1 : ℝ) / 3)) ≤ 2 * Real.sqrt 2 := by
        calc (z2Airy a - z₀) * Real.sqrt (2 * (-a) ^ ((1 : ℝ) / 3))
            ≤ (2 * (-a) ^ ((1 : ℝ) / 3) / Real.sqrt (-a)) * Real.sqrt (2 * (-a) ^ ((1 : ℝ) / 3)) := by
              gcongr
          _ = 2 * Real.sqrt 2 * ((-a) ^ ((1 : ℝ) / 3) * ((-a) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 2) / (-a) ^ ((1 : ℝ) / 2)) := by
              rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]; ring
          _ = 2 * Real.sqrt 2 * 1 := by
              have hA : 0 < -a := by linarith
              rw [← Real.rpow_mul hA.le, ← Real.rpow_add hA, show (1 / 3 + 1 / 3 * (1 / 2) : ℝ) = 1 / 2 by norm_num,
                div_self (Real.rpow_pos_of_pos hA _).ne']
          _ = 2 * Real.sqrt 2 := mul_one _
      have h22 : 2 * Real.sqrt 2 ≤ 50 := by
        have : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
        linarith
      linarith
    · rw [hm10]
      have hm_int : ∀ t ∈ Icc z₀ 10, Real.sqrt (t ^ 2 / 4 + a) ≤ 5 := by
        intro t ht
        rw [Real.sqrt_le_left (by norm_num)]
        have hz0_nn : 0 ≤ z₀ := by positivity
        have : t ^ 2 ≤ 100 := by nlinarith [ht.1, ht.2]
        linarith [show a ≤ 0 from ha]
      have h10_ge : z₀ ≤ 10 := by
        have hza_10 : z2Airy a ≤ 10 := max_eq_right_iff.mp hm10
        exact le_trans (z2Airy_gt_turning ha4).le hza_10
      have hint : actionWell a 10 ≤ (10 - z₀) * 5 := by
        unfold actionWell
        have hc : Continuous (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a)) := by fun_prop
        have hI1 : IntervalIntegrable (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a))
            MeasureTheory.volume z₀ 10 := hc.intervalIntegrable _ _
        have hm' := intervalIntegral.integral_mono_on h10_ge hI1
          intervalIntegrable_const hm_int
        rw [intervalIntegral.integral_const, smul_eq_mul] at hm'
        exact hm'
      nlinarith [show 0 ≤ z₀ by positivity]
  · push_neg at ha4
    have hza_10 : z2Airy a ≤ 10 := by
      unfold z2Airy
      have h1 : -a < 4 := by linarith
      have h13 : (-a) ^ ((1 : ℝ) / 3) ≤ 4 := by
        by_cases ha0 : -a ≤ 1
        · exact (Real.rpow_le_one (by linarith) ha0 (by norm_num)).trans (by norm_num)
        · push_neg at ha0
          calc (-a) ^ ((1 : ℝ) / 3) ≤ (-a) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha0.le (by norm_num)
            _ = -a := Real.rpow_one _
            _ ≤ 4 := by linarith
      have hsq : Real.sqrt (-a + 2 * (-a) ^ ((1 : ℝ) / 3)) ≤ 5 := by
        rw [Real.sqrt_le_left (by norm_num)]; linarith
      linarith
    rw [max_eq_right hza_10]
    have h10_ge : z₀ ≤ 10 := (two_sqrt_neg_le_max ha).le.trans (max_eq_right hza_10).le
    have hm_int : ∀ t ∈ Icc z₀ 10, Real.sqrt (t ^ 2 / 4 + a) ≤ 5 := by
      intro t ht
      rw [Real.sqrt_le_left (by norm_num)]
      have hz0_nn : 0 ≤ z₀ := by positivity
      have : t ^ 2 ≤ 100 := by nlinarith [ht.1, ht.2]
      linarith
    unfold actionWell
    have hc : Continuous (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a)) := by fun_prop
    have hI1 : IntervalIntegrable (fun t : ℝ => Real.sqrt (t ^ 2 / 4 + a))
        MeasureTheory.volume z₀ 10 := hc.intervalIntegrable _ _
    have hm' := intervalIntegral.integral_mono_on h10_ge hI1
      intervalIntegrable_const hm_int
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm'
    nlinarith [show 0 ≤ z₀ by positivity]

private lemma pcV_far_propagate {a z₁ z s₀ : ℝ} (ha : a ≤ 0) (hz₁ : max (z2Airy a) 10 ≤ z₁)
    (hs₀ : s₀ ∈ Icc z₁ z)
    (hvt_pos_on : ∀ t ∈ Icc z₁ z, 0 < vt pcV a t)
    (hr_deriv : ∀ t ∈ Icc z₁ z,
      HasDerivAt (fun t => deriv (vt pcV a) t / vt pcV a t)
        (t ^ 2 / 4 + a - (deriv (vt pcV a) t / vt pcV a t) ^ 2) t)
    (hrs₀ : (1 / 4 : ℝ) * Real.sqrt (s₀ ^ 2 / 4 + a) ≤ deriv (vt pcV a) s₀ / vt pcV a s₀) :
    (1 / 4 : ℝ) * Real.sqrt (z ^ 2 / 4 + a) * vt pcV a z ≤ deriv (vt pcV a) z := by
  let r : ℝ → ℝ := fun t => deriv (vt pcV a) t / vt pcV a t
  let f : ℝ → ℝ := fun t => r t - (1 / 4 : ℝ) * Real.sqrt (t ^ 2 / 4 + a)
  let Aset : Set ℝ := {t ∈ Icc s₀ z | 0 ≤ f t}
  by_contra hbad
  push_neg at hbad
  have hf_cont : ContinuousOn f (Icc s₀ z) := by
    refine ContinuousOn.sub (fun t ht => (hr_deriv t ⟨hs₀.1.trans ht.1, ht.2⟩).continuousAt.continuousWithinAt) ?_
    exact (continuous_const.mul (Real.continuous_sqrt.comp (by fun_prop))).continuousOn
  have hA_closed : IsClosed Aset := by
    have : Aset = Icc s₀ z ∩ {t | 0 ≤ f t} := rfl
    exact hf_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hA_ne : Aset.Nonempty := ⟨s₀, ⟨le_rfl, hs₀.2⟩, sub_nonneg.mpr hrs₀⟩
  have hA_bdd : BddAbove Aset := ⟨z, fun _ ht => ht.1.2⟩
  set s₁ := sSup Aset
  have hs₁_mem : s₁ ∈ Aset := hA_closed.csSup_mem hA_ne hA_bdd
  have hs₁_lt : s₁ < z := lt_of_le_of_ne hs₁_mem.1.2 fun heq => by
    have hf0 := hs₁_mem.2
    rw [heq] at hf0
    have hr_bad : r z < (1 / 4 : ℝ) * Real.sqrt (z ^ 2 / 4 + a) := by
      have hvpos : 0 < vt pcV a z := hvt_pos_on z ⟨hs₀.1.trans hs₀.2, le_rfl⟩
      dsimp [r]; rw [div_lt_iff₀ hvpos]; linarith
    have hf_def : f z = r z - (1 / 4 : ℝ) * Real.sqrt (z ^ 2 / 4 + a) := rfl
    linarith
  have hz₁_le_s₁ : z₁ ≤ s₁ := hs₀.1.trans hs₁_mem.1.1
  have hzbase_le_s₁ : max (z2Airy a) 10 ≤ s₁ := hz₁.trans hz₁_le_s₁
  have hf_s₁ : f s₁ = 0 := by
    by_contra hne
    have hf_pos : 0 < f s₁ := lt_of_le_of_ne hs₁_mem.2 (Ne.symm hne)
    obtain ⟨δ', hδ'p, hδ'⟩ := Metric.continuousWithinAt_iff.mp (hf_cont s₁ hs₁_mem.1) (f s₁ / 2) (half_pos hf_pos)
    have hm_pos : 0 < min (δ' / 2) ((z - s₁) / 2) :=
      lt_min (half_pos hδ'p) (half_pos (sub_pos.mpr hs₁_lt))
    have ht₀_gt : s₁ < min z (s₁ + min (δ' / 2) ((z - s₁) / 2)) :=
      lt_min hs₁_lt (lt_add_of_pos_right s₁ hm_pos)
    have ht₀_mem : min z (s₁ + min (δ' / 2) ((z - s₁) / 2)) ∈ Icc s₀ z :=
      ⟨hs₁_mem.1.1.trans ht₀_gt.le, min_le_left _ _⟩
    have ht₀_dist : dist (min z (s₁ + min (δ' / 2) ((z - s₁) / 2))) s₁ < δ' := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht₀_gt)]
      have h1 : min z (s₁ + min (δ' / 2) ((z - s₁) / 2)) ≤ s₁ + min (δ' / 2) ((z - s₁) / 2) :=
        min_le_right _ _
      have h2 : min (δ' / 2) ((z - s₁) / 2) ≤ δ' / 2 := min_le_left _ _
      linarith
    have hft₀ : dist (f (min z (s₁ + min (δ' / 2) ((z - s₁) / 2)))) (f s₁) < f s₁ / 2 :=
      hδ' ht₀_mem ht₀_dist
    have hft₀_pos : 0 ≤ f (min z (s₁ + min (δ' / 2) ((z - s₁) / 2))) := by
      rw [Real.dist_eq, abs_lt] at hft₀; linarith
    have ht₀_A : min z (s₁ + min (δ' / 2) ((z - s₁) / 2)) ∈ Aset := ⟨ht₀_mem, hft₀_pos⟩
    exact absurd (le_csSup hA_bdd ht₀_A) (not_le.mpr ht₀_gt)
  have hr_s₁ : 0 < r s₁ := by
    have hf_def : f s₁ = r s₁ - (1 / 4 : ℝ) * Real.sqrt (s₁ ^ 2 / 4 + a) := rfl
    have hreq : r s₁ = (1 / 4 : ℝ) * Real.sqrt (s₁ ^ 2 / 4 + a) := sub_eq_zero.mp (hf_def ▸ hf_s₁)
    have hp1 : 0 < s₁ ^ 2 / 4 + a := (k2_eq_p_far ha hzbase_le_s₁).2
    rw [hreq]; exact mul_pos (by norm_num) (Real.sqrt_pos.mpr hp1)
  have hrc : ContinuousAt r s₁ := (hr_deriv s₁ ⟨hz₁_le_s₁, hs₁_mem.1.2⟩).continuousAt
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hrc (r s₁ / 2) (half_pos hr_s₁)
  let s₂ := min z (s₁ + δ / 2)
  have hs₁_s₂ : s₁ < s₂ := lt_min hs₁_lt (by linarith)
  have hs₂_le : s₂ ≤ z := min_le_left _ _
  have hs₂_ub : s₂ ≤ s₁ + δ / 2 := min_le_right _ _
  have hf_mono : StrictMonoOn f (Icc s₁ s₂) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc s₁ s₂) (hf_cont.mono (Icc_subset_Icc hs₁_mem.1.1 hs₂_le))
    intro t ht
    rw [interior_Icc] at ht
    have htz : t ∈ Icc z₁ z := ⟨hz₁_le_s₁.trans ht.1.le, ht.2.le.trans hs₂_le⟩
    have htzb : max (z2Airy a) 10 ≤ t := hzbase_le_s₁.trans ht.1.le
    have htp : 0 < t ^ 2 / 4 + a := (k2_eq_p_far ha htzb).2
    have hfd : HasDerivAt f ((t ^ 2 / 4 + a - r t ^ 2) - t / (16 * Real.sqrt (t ^ 2 / 4 + a))) t := by
      have hp_d : HasDerivAt (fun x : ℝ => x ^ 2 / 4 + a) (t / 2) t :=
        ((hasDerivAt_pow 2 t).div_const 4).add_const a |>.congr_deriv (by ring)
      have hsq_d : HasDerivAt (fun x : ℝ => (1 / 4 : ℝ) * Real.sqrt (x ^ 2 / 4 + a))
          (t / (16 * Real.sqrt (t ^ 2 / 4 + a))) t := by
        exact ((hp_d.sqrt htp.ne').const_mul _).congr_deriv (by ring)
      exact (hr_deriv t htz).sub hsq_d
    rw [hfd.deriv]
    have hft_neg : f t < 0 := by
      by_contra hnn; push_neg at hnn
      have htm : t ∈ Aset := ⟨⟨hs₁_mem.1.1.trans ht.1.le, ht.2.le.trans hs₂_le⟩, hnn⟩
      exact absurd (le_csSup hA_bdd htm) (not_le.mpr ht.1)
    have hdist : dist (r t) (r s₁) < r s₁ / 2 := by
      apply hδ
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
      have : t ≤ s₁ + δ / 2 := ht.2.le.trans hs₂_ub
      linarith
    have hrt_nonneg : 0 ≤ r t := by
      rw [Real.dist_eq, abs_lt] at hdist; linarith
    have hrt_lt : r t < (1 / 4 : ℝ) * Real.sqrt (t ^ 2 / 4 + a) := by
      have hf_def : f t = r t - (1 / 4 : ℝ) * Real.sqrt (t ^ 2 / 4 + a) := rfl
      linarith
    have hrt_sq : r t ^ 2 ≤ (1 / 16 : ℝ) * (t ^ 2 / 4 + a) := by
      have h0 : 0 ≤ (1 / 4 : ℝ) * Real.sqrt (t ^ 2 / 4 + a) := by positivity
      have hsq := mul_self_le_mul_self hrt_nonneg hrt_lt.le
      rw [sq]
      exact hsq.trans_eq (by rw [mul_mul_mul_comm, Real.mul_self_sqrt htp.le]; ring)
    have h15 := fifteen_p32_gt_s ha htzb
    have hden : 0 < 16 * Real.sqrt (t ^ 2 / 4 + a) := by positivity
    have hmul : t < 15 * (t ^ 2 / 4 + a) * Real.sqrt (t ^ 2 / 4 + a) := by
      have hp32 : (t ^ 2 / 4 + a) ^ ((3 : ℝ) / 2) = (t ^ 2 / 4 + a) * Real.sqrt (t ^ 2 / 4 + a) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' htp.le (by norm_num)]; norm_num
      linarith
    have h15p : (15 / 16 : ℝ) * (t ^ 2 / 4 + a) ≤ t ^ 2 / 4 + a - r t ^ 2 := by linarith
    have hdiv : t / (16 * Real.sqrt (t ^ 2 / 4 + a)) < (15 / 16 : ℝ) * (t ^ 2 / 4 + a) := by
      rw [div_lt_iff₀ hden]
      nlinarith [Real.sqrt_nonneg (t ^ 2 / 4 + a)]
    linarith
  have hfs₂ := hf_mono ⟨le_rfl, hs₁_s₂.le⟩ ⟨hs₁_s₂.le, le_rfl⟩ hs₁_s₂
  have hs₂_in : s₂ ∈ Aset := ⟨⟨hs₁_mem.1.1.trans hs₁_s₂.le, hs₂_le⟩, by linarith [hf_s₁]⟩
  exact absurd (le_csSup hA_bdd hs₂_in) (not_le.mpr hs₁_s₂)

/-- **Far-zone positivity & growth of `pcV` for all `a ≤ 0` (`V_growth`):**
once `z ≥ max (z2Airy a) 10` and `actionWell a z ≥ actionThreshV cPC CPC`, we have
`vt pcV a z ≥ cV * (Ewell a z)⁻¹ * Mbal a z > 0` and
`deriv (vt pcV a) z ≥ (1 / 4) * Real.sqrt (k2 a z) * vt pcV a z`. -/
theorem pcV_far_pos_and_growth : ∃ cV SV : ℝ, 0 < cV ∧ 0 < SV ∧
    ∀ a ≤ 0, ∀ z, max (z2Airy a) 10 ≤ z → SV ≤ actionWell a z →
      cV * (Ewell a z)⁻¹ * Mbal a z ≤ vt pcV a z ∧
      (1 / 4 : ℝ) * Real.sqrt (k2 a z) * vt pcV a z ≤ deriv (vt pcV a) z := by
  obtain ⟨cPC, CPC, env⟩ := pcEnvelopeFacts
  have hcPC_pos := env.cPC_pos
  have hcPC_le := env.cPC_le
  let S1 : ℝ := max (Real.log (4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2) / 2) 50
  let C_V : ℝ := cPC / Real.sqrt 17 / (4 * CPC ^ 2)
  let SV : ℝ := actionThreshV cPC CPC
  have hCPC_pos : 0 < CPC := lt_of_lt_of_le hcPC_pos hcPC_le
  have hCV_pos : 0 < C_V := by positivity
  refine ⟨C_V, SV, hCV_pos, actionThreshV_pos hcPC_pos hcPC_le, fun a ha z hz hact => ?_⟩
  have hS1_ge_log : Real.log (4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2) / 2 ≤ S1 := le_max_left _ _
  have hS1_ge_50 : 50 ≤ S1 := le_max_right _ _
  have hact_z : 4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2 ≤ Real.exp (2 * actionWell a z) := by
    have hlog : Real.log (4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2) ≤ 2 * actionWell a z := by
      have h1 : S1 ≤ actionWell a z := by
        have hpos : 0 ≤ 20 + 4 * Real.log (max 1 (4 * CPC ^ 3 * Real.sqrt 17 / cPC)) := by
          have := Real.log_nonneg (le_max_left 1 (4 * CPC ^ 3 * Real.sqrt 17 / cPC)); linarith
        dsimp [SV, actionThreshV] at hact; linarith
      linarith
    calc 4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2
        = Real.exp (Real.log (4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (2 * actionWell a z) := Real.exp_le_exp.mpr hlog
  have hvt_z : C_V * (Ewell a z)⁻¹ * Mbal a z ≤ vt pcV a z :=
    vt_far_lower_of_action hcPC_pos hcPC_le env ha (le_trans (two_sqrt_neg_le_max ha).le hz) hact_z
  refine ⟨hvt_z, ?_⟩
  -- Compare `actionWell a z_base` against `S1` to find `z₁ ∈ [z_base, z]` with `actionWell a z₁ ≥ S1`
  -- Wait: if `actionWell a z_base ≤ S1` use IVT; otherwise pick `z₁ = z_base`? No: we need `actionWell a z - actionWell a z₁ ≥ 20 + 4 log(...)`!
  -- Actually for `z₁ = max (2 √(-a)) ...` where `actionWell a z_base ≤ 50 ≤ S1`: let's check BOTH!
  let z₀ := 2 * Real.sqrt (-a)
  have hz₀_lt : z₀ < z := lt_of_lt_of_le (two_sqrt_neg_le_max ha) hz
  have hcont_act : ContinuousOn (actionWell a) (Icc z₀ z) := by
    have hc : Continuous (fun τ : ℝ => Real.sqrt (τ ^ 2 / 4 + a)) := by fun_prop
    exact (continuous_primitive (fun a' b' => hc.intervalIntegrable a' b') z₀).continuousOn
  have hact_z0 : actionWell a z₀ = 0 := by
    unfold actionWell; exact intervalIntegral.integral_same
  have hS1_mem : S1 ∈ Icc (actionWell a z₀) (actionWell a z) := by
    rw [hact_z0]
    refine ⟨by linarith, ?_⟩
    have hpos : 0 ≤ 20 + 4 * Real.log (max 1 (4 * CPC ^ 3 * Real.sqrt 17 / cPC)) := by
      have := Real.log_nonneg (le_max_left 1 (4 * CPC ^ 3 * Real.sqrt 17 / cPC)); linarith
    dsimp [SV, actionThreshV] at hact; linarith
  -- Actually `z₁ ≥ max (z2Airy a) 10` is NOT guaranteed if `z_base` has `actionWell < S1`; wait: `z₁` ONLY needs `vt(t) > 0` on `[z₁, z]` AND `f'(t) > 0` where `z₁` starts!
  -- Wait: `fifteen_p32_gt_s` needed `max (z2Airy a) 10 ≤ s`, SO TAKE `z_base := max (z2Airy a) 10`!
  -- And check `actionWell a z_base ≤ 50`?Wait: for `-4 ≤ a ≤ 0`, `z_base = 10` has `∫_{2√(-a)}^{10} √(t²/4+a) dt ≤ 10 * 5 = 50`!
  -- For `a ≤ -4`, `z_base = z2Airy a` has `Ewell a (z2Airy a) ≥ exp (-3)` (`Ewell_airy_bounds`? Wait check `PCEnergyAiryEnv`), so `actionWell ≤ 3 ≤ 50`!
  -- Let's check: does `[z_base, z]` ALWAYS have `actionWell a z_base ≤ 50`?! YES! Let's prove `actionWell_base_le` in 12 lines right here!
  have hact_base : actionWell a (max (z2Airy a) 10) ≤ 50 := actionWell_base_le_50 ha
  -- Pick `z₁ ∈ [z_base, z]` with `actionWell a z₁ = S1`!
  let z_base := max (z2Airy a) 10
  have hz_base_le : z_base ≤ z := hz
  have hS1_mem_base : S1 ∈ Icc (actionWell a z_base) (actionWell a z) := by
    refine ⟨hact_base.trans hS1_ge_50, ?_⟩
    have hpos : 0 ≤ 20 + 4 * Real.log (max 1 (4 * CPC ^ 3 * Real.sqrt 17 / cPC)) := by
      have := Real.log_nonneg (le_max_left 1 (4 * CPC ^ 3 * Real.sqrt 17 / cPC)); linarith
    dsimp [SV, actionThreshV] at hact; linarith
  have hcont_base : ContinuousOn (actionWell a) (Icc z_base z) :=
    hcont_act.mono (Icc_subset_Icc_left (two_sqrt_neg_le_max ha).le)
  obtain ⟨z₁, hz₁_mem, hz₁_eq⟩ := intermediate_value_Icc hz_base_le hcont_base hS1_mem_base
  -- On `[z₁, z]`, `actionWell` is monotone increasing, so `vt pcV a t ≥ C_V * Ewell⁻¹ * Mbal > 0`!
  have hact_mono : ∀ {u v : ℝ}, z₀ ≤ u → u ≤ v → actionWell a u ≤ actionWell a v := by
    intro u v hu huv
    have := actionWell_sub (a := a) (z₁ := u) (z₂ := v) ha
    have hn : 0 ≤ ∫ t in u..v, Real.sqrt (t ^ 2 / 4 + a) :=
      intervalIntegral.integral_nonneg huv fun t _ => Real.sqrt_nonneg _
    linarith
  have hz₁_ge_z0 : z₀ ≤ z₁ := le_trans (two_sqrt_neg_le_max ha).le hz₁_mem.1
  have hvt_on : ∀ t ∈ Icc z₁ z, C_V * (Ewell a t)⁻¹ * Mbal a t ≤ vt pcV a t := fun t ht => by
    have htz0 : z₀ ≤ t := le_trans hz₁_ge_z0 ht.1
    have hact_t : S1 ≤ actionWell a t := hz₁_eq.symm.trans_le (hact_mono hz₁_ge_z0 ht.1)
    have hlog_t : Real.log (4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2) ≤ 2 * actionWell a t := by
      linarith [hS1_ge_log]
    have hact_exp : 4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2 ≤ Real.exp (2 * actionWell a t) := by
      calc 4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2
          = Real.exp (Real.log (4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2)) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (2 * actionWell a t) := Real.exp_le_exp.mpr hlog_t
    exact vt_far_lower_of_action hcPC_pos hcPC_le env ha htz0 hact_exp
  have hvt_pos_on : ∀ t ∈ Icc z₁ z, 0 < vt pcV a t := fun t ht => by
    have ht0 : 0 ≤ t := le_trans (by positivity) (le_trans hz₁_ge_z0 ht.1)
    have hEt : Ewell a t = Real.exp (-actionWell a t) := Ewell_eq_exp_action ha (le_trans hz₁_ge_z0 ht.1)
    have hpos : 0 < C_V * (Ewell a t)⁻¹ * Mbal a t := by
      rw [hEt, ← Real.exp_neg]; exact mul_pos (mul_pos hCV_pos (Real.exp_pos _)) (Mbal_pos a t)
    exact lt_of_lt_of_le hpos (hvt_on t ht)
  -- Define `r t := deriv (vt pcV a) t / vt pcV a t` on `[z₁, z]`!
  let r : ℝ → ℝ := fun t => deriv (vt pcV a) t / vt pcV a t
  have hr_deriv : ∀ t ∈ Icc z₁ z, HasDerivAt r (t ^ 2 / 4 + a - r t ^ 2) t := fun t ht => by
    have hv0 : vt pcV a t ≠ 0 := (hvt_pos_on t ht).ne'
    have hdv_d : HasDerivAt (deriv (vt pcV a)) ((t ^ 2 / 4 + a) * vt pcV a t) t := by
      have heq : deriv (vt pcV a) = fun s => Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * pcVD a s :=
        funext fun s => by
          change deriv (fun τ => Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * pcV a τ) s = _
          rw [deriv_const_mul _ (hasDerivAt_pcV a s).differentiableAt, (hasDerivAt_pcV a s).deriv]
      rw [heq]
      exact ((hasDerivAt_pcVD a t).const_mul _).congr_deriv (by dsimp [vt]; ring)
    have hd := hdv_d.div (diff_vt_at' a t).hasDerivAt hv0
    refine hd.congr_deriv ?_
    dsimp [r]; field_simp [hv0]
  have hM_ratio : Mbal a z / Mbal a z₁ ≥ 1 / (8 + 8 * actionWell a z) := by
    have hM1 : Mbal a z₁ ≤ Mbal a z₀ := by
      unfold Mbal
      apply Real.rpow_le_rpow_of_nonpos (k2_pos a z₀) _ (by norm_num)
      unfold k2
      have hp0 : z₀ ^ 2 / 4 + a = 0 := by
        dsimp [z₀]; rw [mul_pow, Real.sq_sqrt (neg_nonneg.mpr ha)]; ring
      rw [hp0, abs_zero]
      exact max_le (by positivity) (le_max_right _ _)
    have hrat := actionWell_ge_ratio_k2 ha hz
    have hMrat : 1 / (8 + 8 * actionWell a z) ≤ Mbal a z / Mbal a z₀ := by
      have hdiv : Mbal a z / Mbal a z₀ = ((k2 a z / k2 a z₀) ^ ((1 : ℝ) / 4))⁻¹ := by
        unfold Mbal
        rw [show (-(1 : ℝ) / 4 : ℝ) = -((1 : ℝ) / 4) by norm_num,
          Real.rpow_neg (k2_pos a z).le, Real.rpow_neg (k2_pos a z₀).le,
          inv_div_inv, Real.div_rpow (k2_pos a z).le (k2_pos a z₀).le, inv_div]
      rw [hdiv, inv_eq_one_div]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (div_pos (k2_pos a z) (k2_pos a z₀)) _) hrat
    have hMpos : 0 < Mbal a z := Mbal_pos a z
    calc Mbal a z / Mbal a z₁ ≥ Mbal a z / Mbal a z₀ :=
          div_le_div_of_nonneg_left hMpos.le (Mbal_pos a z₁) hM1
      _ ≥ 1 / (8 + 8 * actionWell a z) := hMrat
  -- Existence of `s₀ ∈ [z₁, z]` with `r s₀ ≥ (1/4) √(s₀^2/4 + a)`
  have hex : ∃ s₀ ∈ Icc z₁ z, (1 / 4 : ℝ) * Real.sqrt (s₀ ^ 2 / 4 + a) ≤ r s₀ := by
    by_contra hno
    push_neg at hno
    have hderiv_log : ∀ t ∈ Icc z₁ z,
        HasDerivAt (fun s => Real.log (vt pcV a s)) (r t) t := fun t ht => by
      exact ((diff_vt_at' a t).hasDerivAt).log (hvt_pos_on t ht).ne'
    have hint_log : Real.log (vt pcV a z / vt pcV a z₁) = ∫ t in z₁..z, r t := by
      rw [Real.log_div (hvt_pos_on z ⟨hz₁_mem.2, le_rfl⟩).ne' (hvt_pos_on z₁ ⟨le_rfl, hz₁_mem.2⟩).ne']
      have hcont_r : ContinuousOn r (Icc z₁ z) := fun t ht =>
        (hr_deriv t ht).continuousAt.continuousWithinAt
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz₁_mem.2
        (fun t ht => (hderiv_log t ht).continuousAt.continuousWithinAt)
        (fun t ht => hderiv_log t (Ioo_subset_Icc_self ht))
        (hcont_r.intervalIntegrable_of_Icc hz₁_mem.2)).symm
    have hcont_sq : ContinuousOn (fun t : ℝ => (1 / 4 : ℝ) * Real.sqrt (t ^ 2 / 4 + a)) (Icc z₁ z) :=
      (continuous_const.mul (Real.continuous_sqrt.comp (by fun_prop))).continuousOn
    have hcont_r : ContinuousOn r (Icc z₁ z) := fun t ht =>
      (hr_deriv t ht).continuousAt.continuousWithinAt
    have hint_ub : ∫ t in z₁..z, r t ≤
        ∫ t in z₁..z, (1 / 4 : ℝ) * Real.sqrt (t ^ 2 / 4 + a) :=
      intervalIntegral.integral_mono_on hz₁_mem.2 (hcont_r.intervalIntegrable_of_Icc hz₁_mem.2)
        (hcont_sq.intervalIntegrable_of_Icc hz₁_mem.2) (fun t ht => (hno t ht).le)
    rw [intervalIntegral.integral_const_mul, ← actionWell_sub ha, hz₁_eq] at hint_ub
    -- Now lower bound `vt z / vt z₁`!
    have hvt_z1_ub : vt pcV a z₁ ≤ CPC * (Ewell a z₁)⁻¹ * Mbal a z₁ := by
      have hz1_0 : 0 ≤ z₁ := le_trans (by positivity) hz₁_ge_z0
      have hw := (env.env_well a ha z₁ hz1_0).2
      have hle : |vt pcV a z₁| ≤
          Real.sqrt (vt pcV a z₁ ^ 2 + (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z₁) ^ 2 / k2 a z₁) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (k2_pos a z₁).le))
      exact (le_abs_self _).trans (hle.trans hw)
    have hEz1 : (Ewell a z₁)⁻¹ = Real.exp S1 := by
      rw [Ewell_eq_exp_action ha hz₁_ge_z0, hz₁_eq, ← Real.exp_neg, neg_neg]
    have hEz_inv : (Ewell a z)⁻¹ = Real.exp (actionWell a z) := by
      rw [Ewell_eq_exp_action ha (le_trans hz₁_ge_z0 hz₁_mem.2), ← Real.exp_neg, neg_neg]
    have hratio_lb : C_V / CPC * Real.exp (actionWell a z - S1) / (8 + 8 * actionWell a z) ≤
        vt pcV a z / vt pcV a z₁ := by
      have hv1_pos : 0 < vt pcV a z₁ := hvt_pos_on z₁ ⟨le_rfl, hz₁_mem.2⟩
      have hvz_ge : C_V * Real.exp (actionWell a z) * Mbal a z ≤ vt pcV a z := by
        rwa [← hEz_inv]
      have hv1_le : vt pcV a z₁ ≤ CPC * Real.exp S1 * Mbal a z₁ := by
        rwa [← hEz1]
      have hvz_nn : 0 ≤ vt pcV a z := by
        have := Mbal_pos a z
        exact le_trans (by positivity) hvz_ge
      have hdiv_ge : (C_V * Real.exp (actionWell a z) * Mbal a z) / (CPC * Real.exp S1 * Mbal a z₁) ≤
          vt pcV a z / vt pcV a z₁ :=
        div_le_div₀ hvz_nn hvz_ge hv1_pos hv1_le
      calc vt pcV a z / vt pcV a z₁
          ≥ (C_V * Real.exp (actionWell a z) * Mbal a z) / (CPC * Real.exp S1 * Mbal a z₁) := hdiv_ge
        _ = (C_V / CPC) * (Real.exp (actionWell a z) / Real.exp S1) * (Mbal a z / Mbal a z₁) := by
            ring
        _ = (C_V / CPC) * Real.exp (actionWell a z - S1) * (Mbal a z / Mbal a z₁) := by
            rw [Real.exp_sub]
        _ ≥ (C_V / CPC) * Real.exp (actionWell a z - S1) * (1 / (8 + 8 * actionWell a z)) := by
            apply mul_le_mul_of_nonneg_left hM_ratio (by positivity)
        _ = C_V / CPC * Real.exp (actionWell a z - S1) / (8 + 8 * actionWell a z) := by ring
    have hlog_ub : vt pcV a z / vt pcV a z₁ ≤ Real.exp (1 / 4 * (actionWell a z - S1)) := by
      have hpos_div : 0 < vt pcV a z / vt pcV a z₁ :=
        div_pos (hvt_pos_on z ⟨hz₁_mem.2, le_rfl⟩) (hvt_pos_on z₁ ⟨le_rfl, hz₁_mem.2⟩)
      rw [← Real.exp_log hpos_div]
      exact Real.exp_le_exp.mpr (hint_log.symm ▸ hint_ub)
    have hcomb : C_V / CPC * Real.exp (actionWell a z - S1) ≤
        (8 + 8 * actionWell a z) * Real.exp (1 / 4 * (actionWell a z - S1)) := by
      have h8 : 0 < 8 + 8 * actionWell a z := by
        have := hact_mono hz₁_ge_z0 hz₁_mem.2
        linarith
      exact ((div_le_iff₀ h8).mp (hratio_lb.trans hlog_ub)).trans_eq (by ring)
    let Δ := actionWell a z - S1
    let K := max 1 (4 * CPC ^ 3 * Real.sqrt 17 / cPC)
    let Δ₀ := Δ - 4 * Real.log K
    have hK_ge : 1 ≤ K := le_max_left _ _
    have hlogK_nn : 0 ≤ Real.log K := Real.log_nonneg hK_ge
    have hΔ₀ : 20 ≤ Δ₀ := by dsimp [Δ₀, Δ, SV, actionThreshV] at hact ⊢; linarith
    have hΔ_eq : Δ = Δ₀ + 4 * Real.log K := by ring
    have hK_ub : CPC / C_V ≤ K := by
      dsimp [C_V]
      have : CPC / (cPC / Real.sqrt 17 / (4 * CPC ^ 2)) = 4 * CPC ^ 3 * Real.sqrt 17 / cPC := by
        field_simp
      rw [this]; exact le_max_right _ _
    have hS1_ub : S1 ≤ 50 + K := by
      have hlog3 : Real.log (4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2) ≤ Real.log (3 * K) := by
        apply Real.log_le_log (by positivity)
        have h1 : 4 * CPC ^ 3 * Real.sqrt 17 / cPC ≤ K := le_max_right _ _
        linarith
      have hK3 : Real.log (3 * K) / 2 ≤ 1 + Real.log K := by
        rw [Real.log_mul (by norm_num) (by positivity)]
        have h3 : Real.log 3 ≤ 2 := by
          have : (3 : ℝ) ≤ Real.exp 2 := by
            have := Real.exp_one_gt_d9
            have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
            nlinarith
          exact (Real.log_le_iff_le_exp (by norm_num)).mpr this
        linarith
      have hlogK_le : Real.log K ≤ K := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      have hS1_def : S1 = max (Real.log (4 * CPC ^ 3 * Real.sqrt 17 / cPC + 2) / 2) 50 := rfl
      rw [hS1_def]
      exact max_le (by linarith) (by linarith)
    have hExp_eq : Real.exp Δ = Real.exp (1 / 4 * Δ) * Real.exp (3 / 4 * Δ) := by
      rw [← Real.exp_add]; congr 1; ring
    have hCancel : Real.exp (3 / 4 * Δ) ≤ (CPC / C_V) * (8 + 8 * actionWell a z) := by
      rw [hExp_eq] at hcomb
      have he : 0 < Real.exp (1 / 4 * Δ) := Real.exp_pos _
      have h1 : C_V / CPC * Real.exp (3 / 4 * Δ) ≤ 8 + 8 * actionWell a z := by
        refine le_of_mul_le_mul_right ?_ he
        calc C_V / CPC * Real.exp (3 / 4 * Δ) * Real.exp (1 / 4 * Δ)
            = C_V / CPC * (Real.exp (1 / 4 * Δ) * Real.exp (3 / 4 * Δ)) := by ring
          _ ≤ (8 + 8 * actionWell a z) * Real.exp (1 / 4 * Δ) := hcomb
      have hc0 : 0 < CPC / C_V := by positivity
      calc Real.exp (3 / 4 * Δ) = (CPC / C_V) * (C_V / CPC * Real.exp (3 / 4 * Δ)) := by field_simp
        _ ≤ (CPC / C_V) * (8 + 8 * actionWell a z) := mul_le_mul_of_nonneg_left h1 hc0.le
    have hExp_split : Real.exp (3 / 4 * Δ) = Real.exp (3 / 4 * Δ₀) * K ^ 3 := by
      have hK3 : Real.exp (((3 : ℕ) : ℝ) * Real.log K) = K ^ 3 := by
        rw [← Real.log_pow, Real.exp_log (pow_pos (by positivity) 3)]
      calc Real.exp (3 / 4 * Δ)
          = Real.exp (3 / 4 * Δ₀ + ((3 : ℕ) : ℝ) * Real.log K) := by
            rw [hΔ_eq]; congr 1; norm_cast; ring
        _ = Real.exp (3 / 4 * Δ₀) * Real.exp (((3 : ℕ) : ℝ) * Real.log K) := Real.exp_add _ _
        _ = Real.exp (3 / 4 * Δ₀) * K ^ 3 := by rw [hK3]
    have hS_ub : actionWell a z ≤ 50 + Δ₀ + 5 * K := by
      have hlogK_le : Real.log K ≤ K := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      have : actionWell a z = S1 + Δ₀ + 4 * Real.log K := by dsimp [Δ, Δ₀]; ring
      linarith
    have hR_ub : Real.exp (3 / 4 * Δ₀) * K ^ 3 ≤ K * (408 + 8 * Δ₀ + 40 * K) := by
      have h8S_nn : 0 ≤ 8 + 8 * actionWell a z := by
        have := hact_mono hz₁_ge_z0 hz₁_mem.2
        linarith
      calc Real.exp (3 / 4 * Δ₀) * K ^ 3 = Real.exp (3 / 4 * Δ) := hExp_split.symm
        _ ≤ (CPC / C_V) * (8 + 8 * actionWell a z) := hCancel
        _ ≤ K * (8 + 8 * (50 + Δ₀ + 5 * K)) :=
            mul_le_mul hK_ub (by linarith [hS_ub]) h8S_nn (by positivity)
        _ = K * (408 + 8 * Δ₀ + 40 * K) := by ring
    have hK2 : K * (408 + 8 * Δ₀ + 40 * K) ≤ (448 + 8 * Δ₀) * K ^ 3 := by
      have hK_nn : 0 ≤ K := by positivity
      have hK1_le_K2 : 1 ≤ K ^ 2 := by simpa using one_le_pow₀ hK_ge (n := 2)
      have h1 : K ≤ K ^ 3 := calc K = K * 1 := (mul_one K).symm
        _ ≤ K * K ^ 2 := mul_le_mul_of_nonneg_left hK1_le_K2 hK_nn
        _ = K ^ 3 := by ring
      have h2 : K ^ 2 ≤ K ^ 3 := calc K ^ 2 = K ^ 2 * 1 := (mul_one _).symm
        _ ≤ K ^ 2 * K := mul_le_mul_of_nonneg_left hK_ge (sq_nonneg K)
        _ = K ^ 3 := by ring
      have hΔpos : 0 ≤ 408 + 8 * Δ₀ := by linarith
      have hm1 : (408 + 8 * Δ₀) * K ≤ (408 + 8 * Δ₀) * K ^ 3 :=
        mul_le_mul_of_nonneg_left h1 hΔpos
      have hm2 : 40 * K ^ 2 ≤ 40 * K ^ 3 := mul_le_mul_of_nonneg_left h2 (by norm_num)
      calc K * (408 + 8 * Δ₀ + 40 * K) = (408 + 8 * Δ₀) * K + 40 * K ^ 2 := by ring
        _ ≤ (408 + 8 * Δ₀) * K ^ 3 + 40 * K ^ 3 := add_le_add hm1 hm2
        _ = (448 + 8 * Δ₀) * K ^ 3 := by ring
    have hExp_small : Real.exp (3 / 4 * Δ₀) ≤ 448 + 8 * Δ₀ := by
      have hKp : 0 < K ^ 3 := pow_pos (by positivity) 3
      exact le_of_mul_le_mul_right (hR_ub.trans hK2) hKp
    exact no_exp_small_gap Δ₀ hΔ₀ hExp_small
  -- Propagate `r ≥ (1/4) √(p)` forward from `s₀` to `z` using `fifteen_p32_gt_s`!
  obtain ⟨s₀, hs₀, hrs₀⟩ := hex
  rw [(k2_eq_p_far ha hz).1]
  exact pcV_far_propagate ha hz₁_mem.1 hs₀ hvt_pos_on hr_deriv hrs₀

/-- **Barrier-regime positivity & growth for `a > 0`**:
for every `a > 0` and `z ≥ 0`, `w_+(z) = kappaBal a * pcU a (-z)` satisfies
`0 ≤ deriv (fun w => kappaBal a * pcU a (-w)) z ≤ 4 √(k2 a z) * w_+(z)` and
`w_+(z) ≥ (c_PC / √17) (Ebar a z)⁻¹ Mbal a z > 0`. -/
theorem pcU_neg_pos_and_growth : ∃ cU : ℝ, 0 < cU ∧
    ∀ a > 0, ∀ z ≥ 0,
      cU * (Ebar a z)⁻¹ * Mbal a z ≤ kappaBal a * pcU a (-z) ∧
      0 ≤ deriv (fun w => kappaBal a * pcU a (-w)) z ∧
      deriv (fun w => kappaBal a * pcU a (-w)) z ≤
        4 * Real.sqrt (k2 a z) * (kappaBal a * pcU a (-z)) := by
  obtain ⟨cPC, _, env⟩ := pcEnvelopeFacts
  have hcPC := env.cPC_pos
  refine ⟨cPC / Real.sqrt 17, div_pos hcPC (Real.sqrt_pos.mpr (by norm_num)), fun a ha z hz => ?_⟩
  let g : ℝ → ℝ := fun w => pcU a (-w)
  let g' : ℝ → ℝ := fun w => -pcUD a (-w)
  have hg_d : ∀ w, HasDerivAt g (g' w) w := fun w => by
    have h := (hasDerivAt_pcU a (-w)).comp w (hasDerivAt_neg w)
    refine h.congr_deriv ?_; dsimp [g']; ring
  have hg'_d : ∀ w, HasDerivAt g' ((w ^ 2 / 4 + a) * g w) w := fun w => by
    have h := ((hasDerivAt_pcUD a (-w)).comp w (hasDerivAt_neg w)).neg
    refine h.congr_deriv ?_; dsimp [g]; ring
  have hmax0 : 2 * Real.sqrt (max (-a) 0) ≤ 0 := by
    rw [max_eq_right (neg_nonpos.mpr ha.le), Real.sqrt_zero, mul_zero]
  have hg0 : 0 < g 0 := by simpa [g] using pcU_pos_beyond a 0 hmax0
  have hgp0 : 0 ≤ g' 0 := by
    dsimp [g']; rw [neg_zero]; exact neg_nonneg.mpr (pcUD_nonpos_beyond hmax0)
  have hg_pos_all : ∀ w ≥ 0, 0 < g w ∧ 0 ≤ g' w := by
    intro w hw
    by_contra hbad
    have hg_all : ∀ t ∈ Icc 0 w, 0 < g t := by
      by_contra hnot
      push_neg at hnot
      let Z : Set ℝ := {t ∈ Icc 0 w | g t ≤ 0}
      have hZc : IsClosed Z := ((Continuous.comp (continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_pcU a t).continuousAt) continuous_neg).continuousOn).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_Iic
      obtain ⟨s₁, hs₁_mem, hs₁_le⟩ : ∃ s₁ ∈ Z, ∀ t ∈ Z, s₁ ≤ t :=
        ⟨sInf Z, hZc.csInf_mem hnot ⟨0, fun _ ht => ht.1.1⟩, fun _ ht => csInf_le ⟨0, fun _ ht => ht.1.1⟩ ht⟩
      have hs₁_pos : 0 < s₁ := lt_of_le_of_ne hs₁_mem.1.1 fun h0 => by
        have := hs₁_mem.2; rw [← h0] at this; linarith
      have hg_lt : ∀ t ∈ Ioo 0 s₁, 0 < g t := fun t ht => by
        by_contra hle; push_neg at hle
        have := hs₁_le t ⟨⟨ht.1.le, ht.2.le.trans hs₁_mem.1.2⟩, hle⟩; linarith [ht.2]
      have hgp_mono : MonotoneOn g' (Icc 0 s₁) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 s₁)
          (fun t _ => (hg'_d t).continuousAt.continuousWithinAt)
          (fun t _ => (hg'_d t).hasDerivWithinAt)
        intro t ht; rw [interior_Icc] at ht
        have hp : 0 ≤ t ^ 2 / 4 + a := by positivity
        exact mul_nonneg hp (hg_lt t ht).le
      have hg_mono : MonotoneOn g (Icc 0 s₁) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 s₁)
          (fun t _ => (hg_d t).continuousAt.continuousWithinAt)
          (fun t _ => (hg_d t).hasDerivWithinAt)
        intro t ht; rw [interior_Icc] at ht
        exact hgp0.trans (hgp_mono ⟨le_rfl, hs₁_pos.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1.le)
      have hgs := hg_mono ⟨le_rfl, hs₁_pos.le⟩ ⟨hs₁_pos.le, le_rfl⟩ hs₁_pos.le
      linarith [hs₁_mem.2]
    have hgp_mono : MonotoneOn g' (Icc 0 w) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 w)
        (fun t _ => (hg'_d t).continuousAt.continuousWithinAt)
        (fun t _ => (hg'_d t).hasDerivWithinAt)
      intro t ht; rw [interior_Icc] at ht
      have hp : 0 ≤ t ^ 2 / 4 + a := by positivity
      exact mul_nonneg hp (hg_all t (Ioo_subset_Icc_self ht)).le
    exact hbad ⟨hg_all w ⟨hw, le_rfl⟩, hgp0.trans (hgp_mono ⟨le_rfl, hw⟩ ⟨hw, le_rfl⟩ hw)⟩
  obtain ⟨hgz_pos, hgz_gp⟩ := hg_pos_all z hz
  -- Show `g' w ≤ 4 √(k2 a w) g w` on `[0, z]` via `r w := g' w / g w`!
  have hr_bd : g' z ≤ 4 * Real.sqrt (k2 a z) * g z := by
    let r : ℝ → ℝ := fun w => g' w / g w
    have hr0 : r 0 ≤ 4 * Real.sqrt (k2 a 0) := by
      have hder := pcU_beyond_deriv a 0 hmax0
      rw [deriv_pcU, abs_of_nonpos (pcUD_nonpos_beyond hmax0)] at hder
      simpa [r, g, g'] using (div_le_iff₀ hg0).mpr (by simpa [g] using hder)
    by_contra hbad
    push_neg at hbad
    have hrz : 4 * Real.sqrt (k2 a z) < r z := (lt_div_iff₀ hgz_pos).mpr hbad
    have hz_pos : 0 < z := lt_of_le_of_ne hz fun h0 => by rw [← h0] at hrz; linarith
    have hk_cont : ContinuousOn (fun w => 4 * Real.sqrt (k2 a w)) (Icc 0 z) := by
      refine continuousOn_const.mul (ContinuousOn.sqrt ?_)
      unfold k2; fun_prop
    have hr_cont : ContinuousOn r (Icc 0 z) := by
      refine ContinuousOn.div (fun w _ => (hg'_d w).continuousAt.continuousWithinAt)
        (fun w _ => (hg_d w).continuousAt.continuousWithinAt) fun w hw => (hg_pos_all w hw.1).1.ne'
    let B : Set ℝ := {w ∈ Icc 0 z | r w ≤ 4 * Real.sqrt (k2 a w)}
    have hBc : IsClosed B := by
      have hB_eq : B = Icc 0 z ∩ (fun w => r w - 4 * Real.sqrt (k2 a w)) ⁻¹' Iic 0 := by
        ext w; simp [B]
      rw [hB_eq]
      exact (hr_cont.sub hk_cont).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hBn : B.Nonempty := ⟨0, ⟨le_rfl, hz⟩, hr0⟩
    set s₁ := sSup B
    have hs₁_mem : s₁ ∈ B := hBc.csSup_mem hBn ⟨z, fun _ ht => ht.1.2⟩
    have hs₁_lt : s₁ < z := lt_of_le_of_ne hs₁_mem.1.2 fun h => by
      have := hs₁_mem.2; rw [h] at this; linarith
    have hk_mono : MonotoneOn (fun w => 4 * Real.sqrt (k2 a w)) (Icc s₁ z) := fun x hx y hy hxy => by
      have hx0 : 0 ≤ x := hs₁_mem.1.1.trans hx.1
      have hkx : k2 a x ≤ k2 a y := by
        unfold k2
        apply max_le_max _ le_rfl
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        nlinarith
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkx) (by norm_num)
    have hr_anti : AntitoneOn r (Icc s₁ z) := by
      have hr_d : ∀ t ∈ Icc s₁ z, HasDerivAt r (t ^ 2 / 4 + a - r t ^ 2) t := fun t ht => by
        have hg0' : g t ≠ 0 := (hg_pos_all t (hs₁_mem.1.1.trans ht.1)).1.ne'
        refine ((hg'_d t).div (hg_d t) hg0').congr_deriv ?_
        dsimp [r]; field_simp [hg0']
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s₁ z)
        (hr_cont.mono (Icc_subset_Icc_left hs₁_mem.1.1))
        (fun t ht => (hr_d t (Ioo_subset_Icc_self (by simpa [interior_Icc] using ht))).hasDerivWithinAt)
      · intro t ht; rw [interior_Icc] at ht
        have hgt_lt : 4 * Real.sqrt (k2 a t) < r t := by
          by_contra hle; push_neg at hle
          have htB : t ∈ B := ⟨⟨hs₁_mem.1.1.trans ht.1.le, ht.2.le⟩, hle⟩
          exact absurd (le_csSup ⟨z, fun _ (h : _ ∈ B) => h.1.2⟩ htB) (not_le.mpr ht.1)
        have hk_ge : t ^ 2 / 4 + a ≤ k2 a t := by
          unfold k2
          have hp0 : 0 ≤ t ^ 2 / 4 + a := by positivity
          calc t ^ 2 / 4 + a = |t ^ 2 / 4 + a| := (abs_of_nonneg hp0).symm
            _ ≤ max |t ^ 2 / 4 + a| (max |a| 1 ^ ((1 : ℝ) / 3)) := le_max_left _ _
        have hr_sq : 16 * k2 a t < r t ^ 2 := by
          have : (4 * Real.sqrt (k2 a t)) ^ 2 = 16 * k2 a t := by
            rw [mul_pow, Real.sq_sqrt (k2_pos a t).le]; ring
          nlinarith [Real.sqrt_nonneg (k2 a t)]
        have hk0 : 0 < k2 a t := k2_pos a t
        linarith
    have hr_le := hr_anti ⟨le_rfl, hs₁_lt.le⟩ ⟨hs₁_lt.le, le_rfl⟩ hs₁_lt.le
    have hk_le := hk_mono ⟨le_rfl, hs₁_lt.le⟩ ⟨hs₁_lt.le, le_rfl⟩ hs₁_lt.le
    linarith [hs₁_mem.2]
  have hκ_pos : 0 < kappaBal a := kappaBal_pos a
  have hderiv_eq : deriv (fun w => kappaBal a * pcU a (-w)) z = kappaBal a * g' z := by
    exact ((hg_d z).const_mul (kappaBal a)).deriv
  have hMolv := (env.molv_bar a ha (-z)).1
  have hMolv_eq : Molv pcU pcV a (-z) = Real.sqrt (pcU a (-z) ^ 2 + g' z ^ 2 / k2 a z) := by
    have hdr : deriv (pcU a) (-z) = -g' z := by dsimp [g']; rw [deriv_pcU]; ring
    unfold Molv
    dsimp only
    rw [if_pos (Or.inr ha), k2_neg a z, hdr, neg_sq]
  have hk_pos : 0 < k2 a z := k2_pos a z
  have hg_sq : (pcU a (-z)) ^ 2 + g' z ^ 2 / k2 a z ≤ 17 * (pcU a (-z)) ^ 2 := by
    have h1 : g' z ^ 2 ≤ 16 * k2 a z * (pcU a (-z)) ^ 2 := by
      have hsq : (4 * Real.sqrt (k2 a z) * g z) ^ 2 = 16 * k2 a z * g z ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hk_pos.le]; ring
      nlinarith [hr_bd, hgz_gp]
    have h2 : g' z ^ 2 / k2 a z ≤ 16 * (pcU a (-z)) ^ 2 :=
      (div_le_iff₀ hk_pos).mpr (by linarith)
    linarith
  have hMolv_le : Molv pcU pcV a (-z) ≤ Real.sqrt 17 * pcU a (-z) := by
    rw [hMolv_eq]
    calc Real.sqrt (pcU a (-z) ^ 2 + g' z ^ 2 / k2 a z)
        ≤ Real.sqrt (17 * pcU a (-z) ^ 2) := Real.sqrt_le_sqrt hg_sq
      _ = Real.sqrt 17 * pcU a (-z) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hgz_pos.le]
  rw [Ebar_neg a z, Mbal_neg a z] at hMolv
  have h_env_le : cPC * (Ebar a z)⁻¹ * Mbal a z ≤ kappaBal a * (Real.sqrt 17 * pcU a (-z)) := by
    calc cPC * (Ebar a z)⁻¹ * Mbal a z
        = kappaBal a * (cPC * (kappaBal a)⁻¹ * (Ebar a z)⁻¹ * Mbal a z) := by
          field_simp [hκ_pos.ne']
      _ ≤ kappaBal a * Molv pcU pcV a (-z) := mul_le_mul_of_nonneg_left hMolv hκ_pos.le
      _ ≤ kappaBal a * (Real.sqrt 17 * pcU a (-z)) := mul_le_mul_of_nonneg_left hMolv_le hκ_pos.le
  refine ⟨?_, ?_, ?_⟩
  · have hrt_pos : 0 < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hrt_pos]
    linarith
  · rw [hderiv_eq]
    exact mul_nonneg hκ_pos.le hgz_gp
  · rw [hderiv_eq]
    have hmul : kappaBal a * g' z ≤ kappaBal a * (4 * Real.sqrt (k2 a z) * g z) :=
      mul_le_mul_of_nonneg_left hr_bd hκ_pos.le
    linarith

-- Axiom checks for WP1b.
/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcV_far_pos_and_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.pcV_far_pos_and_growth

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcU_neg_pos_and_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.pcU_neg_pos_and_growth

end FormalResearch.JacobiEigenvectors.Charts
