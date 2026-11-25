module

public import FormalResearch.CohnElkies.LobeSaddleCore

/-!
# Lobe Saddle Bounds (`ce_rate.tex` Proposition P.4, Remark P.4a)

Source: `CFT/sign_uncertainty/paper/ce_rate.tex` (PR 240, commit `c3d8c90fe`).

Outer tail and additional damping estimates, `lobe_saddle_asymptotic` (`(cel:5.7)`–`(cel:5.9)`),
and `lobeSaddleAmp_nonvacuous`.
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Real Topology

namespace FormalResearch.CohnElkies

private lemma lobe_gauss10_tail {c g' ε_L τ_sd a τ_core : ℝ}
    (hc_pos : 0 < c) (hg'_pos : 0 < g') (hεL_pos : 0 < ε_L) (hτsd_pos : 0 < τ_sd)
    (ha_pos : 0 < a) (hτcore_pos : 0 < τ_core)
    (ha_def : a = ε_L ^ (-(1 / 4 : ℝ))) (hτcore_def : τ_core = a * τ_sd)
    (hτsd_sq : τ_sd ^ 2 = (c * g')⁻¹) (hu_ge : (18.25 : ℝ) ≤ ε_L ^ (-(1 / 2 : ℝ)))
    {b : ℝ} :
    (1 / τ_sd) * ∫ τ in Ioc τ_core b, Real.exp (-(1 / 10 : ℝ) * (c * g') * τ ^ 2) ≤ (62.89 : ℝ) * ε_L := by
  let k_10 := (1 / 10 : ℝ) * (c * g')
  obtain ⟨hint, hbd⟩ := integral_exp_neg_div_Ioi_le hτcore_pos (by positivity : 0 < k_10)
  have hm : ∫ τ in Ioc τ_core b, Real.exp (-k_10 * τ ^ 2) ≤ ∫ τ in Ioi τ_core, Real.exp (-k_10 * τ ^ 2) :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) Ioc_subset_Ioi_self.eventuallySubset
  have ha_sq : a ^ 2 = ε_L ^ (-(1 / 2 : ℝ)) := by
    rw [ha_def, ← Real.rpow_natCast (ε_L ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hεL_pos.le,
      show -(1 / 4 : ℝ) * (2 : ℕ) = -(1 / 2 : ℝ) by norm_num]
  have h_u32 : (ε_L ^ (-(1 / 2 : ℝ))) ^ (3 / 2 : ℝ) * ε_L = ε_L ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_mul hεL_pos.le]; norm_num; nth_rw 2 [← Real.rpow_one ε_L]; rw [← Real.rpow_add hεL_pos]; norm_num
  have ha_inv : a⁻¹ = ε_L ^ (1 / 4 : ℝ) := by
    rw [ha_def, ← Real.rpow_neg_one, ← Real.rpow_mul hεL_pos.le, show -(1 / 4 : ℝ) * -(1 : ℝ) = (1 / 4 : ℝ) by norm_num]
  have h_rhs : (1 / τ_sd) * ((1 / (2 * k_10 * τ_core)) * Real.exp (-k_10 * τ_core ^ 2)) =
      5 * (ε_L ^ (-(1 / 2 : ℝ))) ^ (3 / 2 : ℝ) * Real.exp (-(ε_L ^ (-(1 / 2 : ℝ))) / 10) * ε_L := by
    rw [← mul_assoc, show (1 / τ_sd) * (1 / (2 * k_10 * τ_core)) = 5 * a⁻¹ by
        dsimp [k_10]; rw [hτcore_def]; calc _ = 5 * (c * g')⁻¹ / (a * τ_sd ^ 2) := by ring
          _ = 5 * τ_sd ^ 2 / (a * τ_sd ^ 2) := by rw [← hτsd_sq]
          _ = 5 * a⁻¹ := by field_simp [hτsd_pos.ne', ha_pos.ne'],
      show -k_10 * τ_core ^ 2 = -(a ^ 2) / 10 by
        dsimp [k_10]; rw [hτcore_def]; calc _ = -(1 / 10) * (c * g' * τ_sd ^ 2) * a ^ 2 := by ring
          _ = -(1 / 10) * 1 * a ^ 2 := by rw [hτsd_sq, mul_inv_cancel₀ (mul_pos hc_pos hg'_pos).ne']
          _ = -(a ^ 2) / 10 := by ring,
      ha_sq, ha_inv, ← h_u32]; ring
  rw [show (fun τ : ℝ => Real.exp (-(1 / 10 : ℝ) * (c * g') * τ ^ 2)) = fun τ => Real.exp (-k_10 * τ ^ 2) by
    ext τ; dsimp [k_10]; ring_nf]
  calc (1 / τ_sd) * ∫ τ in Ioc τ_core b, Real.exp (-k_10 * τ ^ 2) ≤ (1 / τ_sd) * ((1 / (2 * k_10 * τ_core)) * Real.exp (-k_10 * τ_core ^ 2)) :=
        mul_le_mul_of_nonneg_left (hm.trans hbd) (by positivity)
    _ = _ := h_rhs
    _ ≤ 62.89 * ε_L := by gcongr; exact (exp_neg_tail_const_bounds hu_ge).2

private lemma lobe_inv_eps_of_lt {ε_L X : ℝ} (hεL_pos : 0 < ε_L) (hX : 0 < X) (hlt : ε_L ^ (-2 : ℝ) < X) :
    X ^ (-(1 / 2 : ℝ)) ≤ ε_L := by
  rw [rpow_neg_half_eq_inv_sqrt hX.le, le_iff_lt_or_eq]; left
  rw [← Real.sqrt_sq hεL_pos.le, inv_lt_iff_one_lt_mul₀ (Real.sqrt_pos.mpr hX), ← Real.sqrt_mul (sq_nonneg ε_L), Real.lt_sqrt zero_le_one, one_pow]
  have hinv : (ε_L ^ 2)⁻¹ = ε_L ^ (-2 : ℝ) := by
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hεL_pos.le, Real.rpow_natCast]
  rw [mul_comm (ε_L ^ 2) X] at *; rwa [← inv_lt_iff_one_lt_mul₀ (pow_pos hεL_pos 2), hinv]

private lemma lobe_half_B {c σ_star g' τ_sd τ : ℝ}
    (hc_pos : 0 < c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hg'_pos : 0 < g') (hg'_def : g' = stripGDerivReal σ_star)
    (hτsd_def : τ_sd = (c * g') ^ (-(1 / 2 : ℝ))) (hτ : τ ∈ Ioi (1 / 2 : ℝ)) :
    (1 / τ_sd) * ((1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ))) ≤ Real.sqrt (2 * c) * τ ^ (-(1 / 2 : ℝ)) := by
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  have hg'_lt : g' < 2 / (1 - σ_star) := by
    rw [hg'_def]; exact ((stripG_deriv_bounds hσ0 hσ1).2).trans (div_lt_div_of_pos_right (by linarith only [hσ1]) h1s_pos)
  have h1 : 1 / τ_sd ≤ Real.sqrt (2 * c / (1 - σ_star)) := by
    rw [hτsd_def, rpow_neg_half_eq_inv_sqrt (mul_pos hc_pos hg'_pos).le, one_div, inv_inv]
    exact Real.sqrt_le_sqrt (by nlinarith only [mul_lt_mul_of_pos_left hg'_lt hc_pos, show c * (2 / (1 - σ_star)) = 2 * c / (1 - σ_star) by ring])
  have h2 : (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) ≤ (1 - σ_star) ^ (1 / 2 : ℝ) * τ ^ (-(1 / 2 : ℝ)) := by
    have hτ0 : 0 < τ := lt_trans (by norm_num) (mem_Ioi.mp hτ)
    have hr := Real.rpow_le_rpow_of_nonpos (z := -(1 / 4 : ℝ)) (div_pos (pow_pos hτ0 2) (pow_pos h1s_pos 2))
      (by linarith only [] : τ ^ 2 / (1 - σ_star) ^ 2 ≤ 1 + τ ^ 2 / (1 - σ_star) ^ 2) (by norm_num)
    refine hr.trans_eq ?_
    rw [Real.div_rpow (sq_nonneg τ) (sq_nonneg (1 - σ_star)), ← Real.rpow_natCast τ 2, ← Real.rpow_natCast (1 - σ_star) 2,
      ← Real.rpow_mul hτ0.le, ← Real.rpow_mul h1s_pos.le,
      show (2 : ℕ) * -(1 / 4 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg h1s_pos.le, div_eq_mul_inv, inv_inv, mul_comm]
  have h3 : Real.sqrt (2 * c / (1 - σ_star)) * (1 - σ_star) ^ (1 / 2 : ℝ) = Real.sqrt (2 * c) := by
    rw [Real.sqrt_div (by positivity), ← Real.sqrt_eq_rpow]; field_simp [(Real.sqrt_pos.mpr h1s_pos).ne']
  calc _ ≤ Real.sqrt (2 * c / (1 - σ_star)) * ((1 - σ_star) ^ (1 / 2 : ℝ) * τ ^ (-(1 / 2 : ℝ))) := mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by rw [← mul_assoc, h3]

private lemma lobe_outer_le_half {c σ_star g' ε_L τ_sd τ_core : ℝ}
    (hc_pos : 0 < c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hg'_pos : 0 < g') (hg'_def : g' = stripGDerivReal σ_star)
    (hεL_pos : 0 < ε_L) (hτsd_pos : 0 < τ_sd) (hτsd_def : τ_sd = (c * g') ^ (-(1 / 2 : ℝ)))
    (hτcore_pos : 0 < τ_core) (hτcore_eq : τ_core = ε_L ^ (3 / 4 : ℝ) * min σ_star (1 - σ_star))
    (hεL_34_le_18 : ε_L ^ (3 / 4 : ℝ) ≤ 1 / 8) (hεL_inv2_ge : (100000 : ℝ) ≤ ε_L ^ (-2 : ℝ))
    (hx_eps : 1 / 2 * (c ^ (1 / 3 : ℝ) * σ_star) ^ (-(3 / 2 : ℝ)) < ε_L)
    (h_gauss10 : ∀ b : ℝ, τ_core ≤ b → (1 / τ_sd) * ∫ τ in Ioc τ_core b, Real.exp (-(1 / 10 : ℝ) * (c * g') * τ ^ 2) ≤ (62.89 : ℝ) * ε_L)
    (hA_dec : (∀ τ ∈ Ioc 0 (1 / 2 : ℝ), (1 / 10 : ℝ) * c * stripGDerivReal σ_star * τ ^ 2 ≤ c * vertUpsilon σ_star τ) ∧
      (∀ τ ∈ Ioi (1 / 2 : ℝ), (3 / 160 : ℝ) * (c * σ_star) + (3 / 20 : ℝ) * (c * σ_star) * Real.log (2 * τ) ≤ c * vertUpsilon σ_star τ))
    (hhalf : σ_star ≤ 1 / 2) :
    let F_out := fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)
    IntegrableOn F_out (Ioi τ_core) ∧ (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ ≤ 54 * ε_L := by
  dsimp only
  let F_out := fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  have hf_cont : Continuous F_out :=
    (Continuous.rpow (by fun_prop) continuous_const fun _ => Or.inl (by positivity)).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (intervalIntegral.continuous_primitive (fun a b => (vertUpsilon_continuousIntegrand σ_star).intervalIntegrable (μ := volume) a b) 0)))
  have hsqrt2pi : (2.506 : ℝ) ≤ Real.sqrt (2 * π) := Real.le_sqrt_of_sq_le (by nlinarith only [Real.pi_gt_d4, Real.pi_pos])
  have h_alg_le1 : ∀ τ : ℝ, (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 := fun τ =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [div_nonneg (sq_nonneg τ) (sq_nonneg (1 - σ_star))]) (by norm_num)
  have hτcore_lt : τ_core < 1 / 2 := by
    rw [hτcore_eq]
    nlinarith only [min_le_left σ_star (1 - σ_star), hεL_34_le_18, hhalf, lt_min hσ0 h1s_pos, Real.rpow_nonneg hεL_pos.le (3 / 4 : ℝ)]
  have h_Ioc_int : IntegrableOn F_out (Ioc τ_core (1 / 2)) := hf_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hm_eps2 : ε_L ^ (-2 : ℝ) < c * σ_star := by
    have hsq := pow_lt_pow_left₀ hx_eps (by positivity) (by decide : 2 ≠ 0)
    rw [mul_pow, ← Real.rpow_natCast ((c ^ (1 / 3 : ℝ) * σ_star) ^ (-(3 / 2 : ℝ))) 2, ← Real.rpow_mul (by positivity),
      show -(3 / 2 : ℝ) * (2 : ℕ) = -(3 : ℕ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast] at hsq
    have h3 : (4 * (c ^ (1 / 3 : ℝ) * σ_star) ^ 3)⁻¹ < ε_L ^ 2 := by
      rw [mul_inv, show (4 : ℝ)⁻¹ = (1 / 2 : ℝ) ^ 2 by norm_num]; exact hsq
    have h4 : 4 * (c ^ (1 / 3 : ℝ) * σ_star) ^ 3 ≤ c * σ_star := by
      have hσsq : 4 * σ_star ^ 2 ≤ 1 := by nlinarith only [hσ0, hhalf]
      rw [mul_pow, rpow_one_third_cube hc_pos]
      calc 4 * (c * σ_star ^ 3) = c * (4 * σ_star ^ 2) * σ_star := by ring
        _ ≤ c * 1 * σ_star := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hσsq hc_pos.le) hσ0.le
        _ = c * σ_star := by ring
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hεL_pos.le, Real.rpow_natCast]
    exact (((inv_lt_inv₀ (pow_pos hεL_pos 2) (by positivity)).mpr h3).trans_eq (inv_inv _)).trans_le h4
  have hm_ge : (100000 : ℝ) ≤ c * σ_star := hεL_inv2_ge.trans hm_eps2.le
  have h_Ioi_int : IntegrableOn F_out (Ioi (1 / 2)) := by
    refine ((integral_inv_sq_Ioi (a := (1 / 2 : ℝ)) (by norm_num)).1.const_mul (Real.exp (-(3 / 160 : ℝ) * (c * σ_star)))).mono'
      hf_cont.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]; refine Filter.Eventually.of_forall fun τ hτ => ?_
    have hτ0 : 0 < τ := lt_trans (by norm_num) (mem_Ioi.mp hτ)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le)]
    have hlog1 : Real.log τ ≤ Real.log (2 * τ) := Real.log_le_log hτ0 (le_mul_of_one_le_left hτ0.le one_le_two)
    have h320 : (2 : ℝ) ≤ (3 / 20 : ℝ) * (c * σ_star) :=
      (by norm_num : (2 : ℝ) ≤ (3 / 20 : ℝ) * 100000).trans (mul_le_mul_of_nonneg_left hm_ge (by norm_num))
    have hlog : 2 * Real.log τ ≤ (3 / 20 : ℝ) * (c * σ_star) * Real.log (2 * τ) :=
      (mul_le_mul_of_nonneg_left hlog1 (by norm_num)).trans
        (mul_le_mul_of_nonneg_right h320 (Real.log_nonneg (by linarith only [mem_Ioi.mp hτ])))
    have hid : Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * τ ^ (-2 : ℝ) = Real.exp (-((3 / 160 : ℝ) * (c * σ_star) + 2 * Real.log τ)) := by
      rw [Real.rpow_def_of_pos hτ0, ← Real.exp_add]; congr 1; ring
    have h_exp : Real.exp (-c * vertUpsilon σ_star τ) ≤ Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * τ ^ (-2 : ℝ) := by
      rw [hid]
      have hA2 := hA_dec.2 τ hτ
      exact Real.exp_le_exp.mpr (by
        calc -c * vertUpsilon σ_star τ = -(c * vertUpsilon σ_star τ) := by ring
          _ ≤ -((3 / 160 : ℝ) * (c * σ_star) + (3 / 20 : ℝ) * (c * σ_star) * Real.log (2 * τ)) := neg_le_neg hA2
          _ ≤ -((3 / 160 : ℝ) * (c * σ_star) + 2 * Real.log τ) := neg_le_neg (add_le_add le_rfl hlog))
    exact (mul_le_mul (h_alg_le1 τ) h_exp (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
  have h_part1 : (1 / τ_sd) * ∫ τ in Ioc τ_core (1 / 2), F_out τ ≤ 62.89 * ε_L := by
    have hm := setIntegral_mono_on h_Ioc_int ((by fun_prop : Continuous fun τ : ℝ =>
        Real.exp (-(1 / 10 : ℝ) * (c * g') * τ ^ 2)).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
      fun τ hτ => (mul_le_mul (h_alg_le1 τ) (Real.exp_le_exp.mpr (by
        have hA1 := hA_dec.1 τ ⟨hτcore_pos.trans hτ.1, hτ.2⟩
        rw [← hg'_def] at hA1
        linarith only [hA1])) (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
    exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans (h_gauss10 (1 / 2) hτcore_lt.le)
  have h_part2 : (1 / τ_sd) * ∫ τ in Ioi (1 / 2 : ℝ), F_out τ ≤ 0.01 * ε_L := by
    obtain ⟨h_inv_int, h_inv_val⟩ := integral_inv_sq_Ioi (a := (1 / 2 : ℝ)) (by norm_num)
    have hpt : ∀ τ ∈ Ioi (1 / 2 : ℝ), F_out τ ≤ (Real.sqrt 2 * (1 / 4 : ℝ) * Real.exp (-(3 / 160 : ℝ) * (c * σ_star))) * τ ^ (-2 : ℝ) :=
      fun τ hτ => by
        have hτ0 : 0 < τ := lt_trans (by norm_num) (mem_Ioi.mp hτ)
        have h_alg : (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) ≤ Real.sqrt 2 := by
          have h1s_sq : (1 - σ_star) ^ 2 ≤ 1 := by nlinarith only [hσ0, h1s_pos, hhalf]
          have hdiv_ge : τ ^ 2 ≤ τ ^ 2 / (1 - σ_star) ^ 2 := by
            rw [le_div_iff₀ (pow_pos h1s_pos 2)]; exact mul_le_of_le_one_right (sq_nonneg τ) h1s_sq
          have hτ_sq : (1 / 4 : ℝ) ≤ τ ^ 2 := by nlinarith only [mem_Ioi.mp hτ]
          have hr := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 4)
            (by linarith only [hdiv_ge, hτ_sq] : 1 / 4 ≤ 1 + τ ^ 2 / (1 - σ_star) ^ 2) (by norm_num : -(1 / 4 : ℝ) ≤ 0)
          have h4 : (1 / 4 : ℝ) ^ (-(1 / 4 : ℝ)) = Real.sqrt 2 := by
            rw [show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num; exact (Real.sqrt_eq_rpow 2).symm
          exact hr.trans_eq h4
        have h2τ : Real.exp (-c * vertUpsilon σ_star τ) ≤ (1 / 4 : ℝ) * Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * τ ^ (-2 : ℝ) := by
          have h320 : (2 : ℝ) ≤ (3 / 20 : ℝ) * (c * σ_star) :=
            (by norm_num : (2 : ℝ) ≤ (3 / 20 : ℝ) * 100000).trans (mul_le_mul_of_nonneg_left hm_ge (by norm_num))
          have hlog : 2 * Real.log (2 * τ) ≤ (3 / 20 : ℝ) * (c * σ_star) * Real.log (2 * τ) :=
            mul_le_mul_of_nonneg_right h320 (Real.log_nonneg (by linarith only [mem_Ioi.mp hτ] : 1 ≤ 2 * τ))
          have he1 : Real.exp (-c * vertUpsilon σ_star τ) ≤ Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * (2 * τ) ^ (-2 : ℝ) := by
            rw [show Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * (2 * τ) ^ (-2 : ℝ) = Real.exp (-((3 / 160 : ℝ) * (c * σ_star) + 2 * Real.log (2 * τ))) by
              rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]; congr 1; ring]
            have hA2 := hA_dec.2 τ hτ
            exact Real.exp_le_exp.mpr (by
              calc -c * vertUpsilon σ_star τ = -(c * vertUpsilon σ_star τ) := by ring
                _ ≤ -((3 / 160 : ℝ) * (c * σ_star) + (3 / 20 : ℝ) * (c * σ_star) * Real.log (2 * τ)) := neg_le_neg hA2
                _ ≤ -((3 / 160 : ℝ) * (c * σ_star) + 2 * Real.log (2 * τ)) := neg_le_neg (add_le_add le_rfl hlog))
          rw [Real.mul_rpow (by norm_num) hτ0.le, show (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 by norm_num] at he1
          exact he1.trans_eq (by ring)
        calc F_out τ ≤ Real.sqrt 2 * ((1 / 4 : ℝ) * Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * τ ^ (-2 : ℝ)) :=
              mul_le_mul h_alg h2τ (Real.exp_pos _).le (Real.sqrt_nonneg _)
          _ = _ := by ring
    have hmono := (setIntegral_mono_on h_Ioi_int (h_inv_int.const_mul _) measurableSet_Ioi hpt).trans_eq (by
      rw [integral_const_mul, h_inv_val, show (1 / 2 : ℝ)⁻¹ = 2 by norm_num])
    have h_1sd : 1 / τ_sd ≤ Real.sqrt (4 * (c * σ_star)) := by
      rw [hτsd_def, rpow_neg_half_eq_inv_sqrt (mul_pos hc_pos hg'_pos).le, one_div, inv_inv]
      have hg'_lt : g' < 4 * σ_star := by
        rw [hg'_def]; exact ((stripG_deriv_bounds hσ0 hσ1).2).trans_le ((div_le_iff₀ h1s_pos).mpr (by nlinarith only [hσ0, hhalf]))
      exact Real.sqrt_le_sqrt (by nlinarith only [hc_pos, hg'_lt])
    have hsqrt2 : Real.sqrt 2 * (1 / 4 : ℝ) * 2 ≤ 1 := by linarith only [show Real.sqrt 2 ≤ 2 by rw [Real.sqrt_le_left (by norm_num)]; norm_num]
    calc (1 / τ_sd) * ∫ τ in Ioi (1 / 2 : ℝ), F_out τ
        ≤ Real.sqrt (2 * (2 * (c * σ_star))) * (Real.sqrt 2 * (1 / 4 : ℝ) * 2 * Real.exp (-(3 / 320 : ℝ) * (2 * (c * σ_star)))) := by
          refine mul_le_mul (h_1sd.trans (Real.sqrt_le_sqrt (le_of_eq (by ring))))
            (hmono.trans_eq (by ring)) (setIntegral_nonneg measurableSet_Ioi fun _ _ => by positivity) (by positivity)
      _ ≤ Real.sqrt (2 * (2 * (c * σ_star))) * Real.exp (-(3 / 320 : ℝ) * (2 * (c * σ_star))) :=
          mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_right hsqrt2 (Real.exp_pos _).le) (by positivity)
      _ ≤ 0.01 * (2 * (c * σ_star)) ^ (-(1 / 2 : ℝ)) :=
          tiny_exp_3_320 ((by norm_num : (100000 : ℝ) ≤ 2 * 100000).trans (mul_le_mul_of_nonneg_left hm_ge (by norm_num)))
      _ ≤ 0.01 * ε_L := by
          have h_le := (Real.rpow_le_rpow_of_nonpos (mul_pos hc_pos hσ0) (le_mul_of_one_le_left (mul_pos hc_pos hσ0).le one_le_two) (by norm_num)).trans
            (lobe_inv_eps_of_lt hεL_pos (mul_pos hc_pos hσ0) hm_eps2)
          gcongr
  have hsplit : ∫ τ in Ioi τ_core, F_out τ = (∫ τ in Ioc τ_core (1 / 2), F_out τ) + ∫ τ in Ioi (1 / 2), F_out τ := by
    rw [← Ioc_union_Ioi_eq_Ioi hτcore_lt.le]; exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h_Ioc_int h_Ioi_int
  refine ⟨(by rw [← Ioc_union_Ioi_eq_Ioi hτcore_lt.le]; exact h_Ioc_int.union h_Ioi_int), ?_⟩
  calc (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ
      = (2 / Real.sqrt (2 * π)) * ((1 / τ_sd) * ∫ τ in Ioi τ_core, F_out τ) := by ring
    _ ≤ (2 / 2.506) * ((62.90 : ℝ) * ε_L) := mul_le_mul
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqrt2pi)
        (by rw [hsplit, mul_add]; linarith only [h_part1, h_part2])
        (mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun _ _ => by dsimp [F_out]; positivity))
        (by norm_num)
    _ ≤ 54 * ε_L := by nlinarith only [hεL_pos]

private lemma lobe_outer_gt_half {c σ_star g' ε_L τ_sd τ_core : ℝ}
    (hc_pos : 0 < c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hg'_pos : 0 < g') (hg'_def : g' = stripGDerivReal σ_star)
    (hεL_pos : 0 < ε_L) (hτsd_pos : 0 < τ_sd) (hτsd_def : τ_sd = (c * g') ^ (-(1 / 2 : ℝ)))
    (hτsd_sq : τ_sd ^ 2 = (c * g')⁻¹)
    (hτcore_pos : 0 < τ_core) (hτcore_eq : τ_core = ε_L ^ (3 / 4 : ℝ) * min σ_star (1 - σ_star))
    (hεL_34_le_18 : ε_L ^ (3 / 4 : ℝ) ≤ 1 / 8) (hεL_inv2_ge : (100000 : ℝ) ≤ ε_L ^ (-2 : ℝ))
    (hz_eps : 1 / Real.sqrt 2 * (c * (1 - σ_star)) ^ (-(1 / 2 : ℝ)) < ε_L)
    (h_gauss10 : ∀ b : ℝ, τ_core ≤ b → (1 / τ_sd) * ∫ τ in Ioc τ_core b, Real.exp (-(1 / 10 : ℝ) * (c * g') * τ ^ 2) ≤ (62.89 : ℝ) * ε_L)
    (hB_dec : (∀ τ ∈ Ioc 0 ((1 - σ_star) / 2), (1 / 10 : ℝ) * c * stripGDerivReal σ_star * τ ^ 2 ≤ c * vertUpsilon σ_star τ) ∧
      (∀ τ ∈ Ioc ((1 - σ_star) / 2) (1 / 2 : ℝ), (3 / 320 : ℝ) * (c * (1 - σ_star)) + (3 / 80 : ℝ) * c * (τ - (1 - σ_star) / 2) ≤ c * vertUpsilon σ_star τ) ∧
      (∀ τ ∈ Ioi (1 / 2 : ℝ), (3 / 320 : ℝ) * (c * (1 - σ_star)) + (3 / 320 : ℝ) * c + (3 / 40 : ℝ) * c * max 0 (Real.log τ) ≤ c * vertUpsilon σ_star τ))
    (hhalf : 1 / 2 < σ_star) :
    let F_out := fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)
    IntegrableOn F_out (Ioi τ_core) ∧ (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ ≤ 54 * ε_L := by
  dsimp only
  let F_out := fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)
  let z_pos := c * (1 - σ_star)
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  have hf_cont : Continuous F_out :=
    (Continuous.rpow (by fun_prop) continuous_const fun _ => Or.inl (by positivity)).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (intervalIntegral.continuous_primitive (fun a b => (vertUpsilon_continuousIntegrand σ_star).intervalIntegrable (μ := volume) a b) 0)))
  have hsqrt2pi : (2.506 : ℝ) ≤ Real.sqrt (2 * π) := Real.le_sqrt_of_sq_le (by nlinarith only [Real.pi_gt_d4, Real.pi_pos])
  have h_alg_le1 : ∀ τ : ℝ, (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 := fun τ =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [div_nonneg (sq_nonneg τ) (sq_nonneg (1 - σ_star))]) (by norm_num)
  let τ₁ := (1 - σ_star) / 2
  have hτ₁_lt : τ₁ < 1 / 4 := by dsimp [τ₁]; linarith only [hhalf]
  have hτcore_lt_τ₁ : τ_core < τ₁ := by rw [hτcore_eq, min_eq_right (by linarith only [hhalf])]; dsimp [τ₁]; nlinarith only [hεL_34_le_18, h1s_pos, Real.rpow_nonneg hεL_pos.le (3 / 4 : ℝ)]
  have hz_eps2 : ε_L ^ (-2 : ℝ) < 2 * z_pos := by
    have h1 := pow_lt_pow_left₀ hz_eps (by positivity) (by decide : 2 ≠ 0)
    rw [mul_pow, show (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) by rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)],
      ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity), show -(1 / 2 : ℝ) * (2 : ℕ) = -1 by norm_num,
      Real.rpow_neg_one] at h1
    have h1' : (2 * (c * (1 - σ_star)))⁻¹ < ε_L ^ 2 := by
      rw [mul_inv, inv_eq_one_div (2 : ℝ)]; exact h1
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hεL_pos.le, Real.rpow_natCast]
    exact ((inv_lt_inv₀ (pow_pos hεL_pos 2) (by positivity)).mpr h1').trans_eq (inv_inv _)
  have hc_100k : (100000 : ℝ) ≤ c := by linarith only [show 2 * z_pos < c by dsimp [z_pos]; nlinarith only [hc_pos, hhalf], hεL_inv2_ge, hz_eps2]
  have h_Ioc1 : IntegrableOn F_out (Ioc τ_core τ₁) := hf_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h_Ioc2 : IntegrableOn F_out (Ioc τ₁ (1 / 2)) := hf_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  obtain ⟨h_tail_int, h_tail_bd⟩ := integrable_log_tail (K := (3 / 40 : ℝ) * c) (by linarith only [hc_100k])
  have h_half_mono : ∀ τ ∈ Ioi (1 / 2 : ℝ), (1 / τ_sd) * F_out τ ≤
      (Real.sqrt (2 * c) * Real.exp (-(3 / 320 : ℝ) * c)) *
        (τ ^ (-(1 / 2 : ℝ)) * Real.exp (-((3 / 40 : ℝ) * c) * max 0 (Real.log τ))) := fun τ hτ => by
    have h_exp : Real.exp (-c * vertUpsilon σ_star τ) ≤ Real.exp (-(3 / 320 : ℝ) * c) * Real.exp (-((3 / 40 : ℝ) * c) * max 0 (Real.log τ)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith only [hB_dec.2.2 τ hτ, show 0 ≤ (3 / 320 : ℝ) * z_pos by dsimp [z_pos]; positivity])
    calc (1 / τ_sd) * F_out τ = ((1 / τ_sd) * (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ))) * Real.exp (-c * vertUpsilon σ_star τ) := by
          dsimp [F_out]; ring
      _ ≤ (Real.sqrt (2 * c) * τ ^ (-(1 / 2 : ℝ))) * _ :=
          mul_le_mul (lobe_half_B hc_pos hσ0 hσ1 hg'_pos hg'_def hτsd_def hτ) h_exp (Real.exp_pos _).le
            (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (lt_trans (by norm_num) (mem_Ioi.mp hτ)).le _))
      _ = _ := by ring
  have h_Ioi : IntegrableOn F_out (Ioi (1 / 2)) := by
    have h1 : IntegrableOn (fun τ : ℝ => (1 / τ_sd) * F_out τ) (Ioi (1 / 2)) := by
      refine (h_tail_int.const_mul (Real.sqrt (2 * c) * Real.exp (-(3 / 320 : ℝ) * c))).mono'
        ((continuous_const.mul hf_cont).continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]; exact Filter.Eventually.of_forall fun τ hτ => by
        rw [Real.norm_of_nonneg (by dsimp [F_out]; positivity)]; exact h_half_mono τ hτ
    have h2 : IntegrableOn (fun τ : ℝ => τ_sd * ((1 / τ_sd) * F_out τ)) (Ioi (1 / 2)) := h1.const_mul τ_sd
    exact h2.congr_fun (fun τ _ => by field_simp [hτsd_pos.ne']) measurableSet_Ioi
  have h_part1 : (1 / τ_sd) * ∫ τ in Ioc τ_core τ₁, F_out τ ≤ 62.89 * ε_L := by
    have hm := setIntegral_mono_on h_Ioc1 ((by fun_prop : Continuous fun τ : ℝ =>
        Real.exp (-(1 / 10 : ℝ) * (c * g') * τ ^ 2)).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
      fun τ hτ => (mul_le_mul (h_alg_le1 τ) (Real.exp_le_exp.mpr (by
        have hB1 := hB_dec.1 τ ⟨hτcore_pos.trans hτ.1, hτ.2⟩; rw [← hg'_def] at hB1; linarith only [hB1]))
        (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
    exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans (h_gauss10 τ₁ hτcore_lt_τ₁.le)
  have h_part2 : (1 / τ_sd) * ∫ τ in Ioc τ₁ (1 / 2), F_out τ ≤ 0.01 * ε_L := by
    have hdom_int : IntegrableOn (fun τ : ℝ => Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁))) (Ioc τ₁ (1 / 2)) :=
      (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁))).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hm := setIntegral_mono_on h_Ioc2 hdom_int measurableSet_Ioc fun τ hτ => by
      have h_exp : Real.exp (-c * vertUpsilon σ_star τ) ≤ Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁)) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by dsimp [z_pos, τ₁]; linarith only [hB_dec.2.1 τ hτ])
      exact (mul_le_mul (h_alg_le1 τ) h_exp (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
    rw [integral_const_mul] at hm
    have hm2 : ∫ τ in Ioc τ₁ (1 / 2), Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁)) ≤ 1 / ((3 / 80 : ℝ) * c) := by
      rw [← intervalIntegral.integral_of_le (by linarith only [hτ₁_lt] : τ₁ ≤ 1 / 2),
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => Real.exp (-(3 / 80 : ℝ) * c * u)) τ₁, sub_self,
        intervalIntegral.integral_of_le (by linarith only [hτ₁_lt])]
      obtain ⟨hl, hvl⟩ := integral_exp_neg_lin_Ioi (a := (0 : ℝ)) (k := (3 / 80 : ℝ) * c) (by positivity)
      have hvl' : ∫ u in Ioi (0 : ℝ), Real.exp (-(3 / 80 : ℝ) * c * u) = 1 / ((3 / 80 : ℝ) * c) := by
        simpa only [mul_zero, Real.exp_zero, neg_mul] using hvl
      have hs' : IntegrableOn (fun u : ℝ => Real.exp (-(3 / 80 : ℝ) * c * u)) (Ioi 0) := by
        simpa only [neg_mul] using hl
      exact (setIntegral_mono_set hs' (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
        Ioc_subset_Ioi_self.eventuallySubset).trans_eq hvl'
    have h_pref : 1 / (c * τ_sd) ≤ 2 * ε_L := le_of_sq_le_sq (by
      have hg'_lt : g' < 2 / (1 - σ_star) := by
        rw [hg'_def]; exact ((stripG_deriv_bounds hσ0 hσ1).2).trans (div_lt_div_of_pos_right (by linarith only [hσ1]) h1s_pos)
      have h1 : (1 / (c * τ_sd)) ^ 2 = g' / c := by rw [div_pow, one_pow, mul_pow, hτsd_sq]; field_simp [hc_pos.ne', hg'_pos.ne']
      have h2 : g' / c < 2 / z_pos := by
        rw [show z_pos = c * (1 - σ_star) from rfl]
        exact (div_lt_div_iff₀ hc_pos (mul_pos hc_pos h1s_pos)).mpr (by nlinarith only [(lt_div_iff₀ h1s_pos).mp hg'_lt, hc_pos])
      have h3 : 2 / z_pos < (2 * ε_L) ^ 2 := by
        rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hεL_pos.le, Real.rpow_natCast,
          inv_lt_iff_one_lt_mul₀ (pow_pos hεL_pos 2)] at hz_eps2
        rw [div_lt_iff₀ (mul_pos hc_pos h1s_pos)]; nlinarith only [hz_eps2]
      linarith only [h1, h2, h3]) (by positivity)
    have hexp_tiny : Real.exp (-(3 / 320 : ℝ) * z_pos) ≤ 1 / 80000 := by
      have hz50k : 50000 ≤ z_pos := by linarith only [hεL_inv2_ge.trans hz_eps2.le]
      have hs := Real.sum_le_exp_of_nonneg (by dsimp [z_pos]; positivity : 0 ≤ (3 / 320 : ℝ) * z_pos) 3
      have hp : (80000 : ℝ) ≤ ∑ i ∈ Finset.range 3, ((3 / 320 : ℝ) * z_pos) ^ i / i.factorial := by
        simp [Finset.sum_range_succ, Nat.factorial]; nlinarith only [hz50k]
      rw [show -(3 / 320 : ℝ) * z_pos = -((3 / 320 : ℝ) * z_pos) by ring, Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) (hp.trans hs)
    calc (1 / τ_sd) * ∫ τ in Ioc τ₁ (1 / 2), F_out τ
        ≤ (1 / τ_sd) * ((80 / (3 * c)) * Real.exp (-(3 / 320 : ℝ) * z_pos)) :=
          mul_le_mul_of_nonneg_left (hm.trans (by
            have h80 : (1 / ((3 / 80 : ℝ) * c) : ℝ) = 80 / (3 * c) := by ring
            linarith only [mul_le_mul_of_nonneg_left (hm2.trans_eq h80) (Real.exp_pos (-(3 / 320 : ℝ) * z_pos)).le])) (by positivity)
      _ = (1 / (c * τ_sd)) * (80 / 3 : ℝ) * Real.exp (-(3 / 320 : ℝ) * z_pos) := by field_simp [hc_pos.ne', hτsd_pos.ne']
      _ ≤ (2 * ε_L) * (80 / 3 : ℝ) * (1 / 80000 : ℝ) := by gcongr
      _ ≤ 0.01 * ε_L := by linarith only [hεL_pos]
  have h_part3 : (1 / τ_sd) * ∫ τ in Ioi (1 / 2 : ℝ), F_out τ ≤ 0.02 * ε_L := by
    have hm1 := setIntegral_mono_on (h_Ioi.const_mul _) (h_tail_int.const_mul _) measurableSet_Ioi h_half_mono
    rw [integral_const_mul, integral_const_mul] at hm1
    have hm2 : (1 / τ_sd) * ∫ τ in Ioi (1 / 2 : ℝ), F_out τ ≤ (Real.sqrt (2 * c) * Real.exp (-(3 / 320 : ℝ) * c)) * 2 :=
      hm1.trans (mul_le_mul_of_nonneg_left h_tail_bd (by positivity))
    have hc_eps := lobe_inv_eps_of_lt hεL_pos hc_pos (hz_eps2.trans (by dsimp [z_pos]; nlinarith only [hc_pos, hhalf]))
    exact hm2.trans ((mul_le_mul_of_nonneg_right (tiny_exp_3_320 hc_100k) (by norm_num)).trans
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc_eps (by norm_num)) (by norm_num)).trans_eq (by ring)))
  have h_Ioi_τ1 : IntegrableOn F_out (Ioi τ₁) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by linarith only [hτ₁_lt] : τ₁ ≤ 1 / 2)]; exact h_Ioc2.union h_Ioi
  have h_int_tot : IntegrableOn F_out (Ioi τ_core) := by
    rw [← Ioc_union_Ioi_eq_Ioi hτcore_lt_τ₁.le]; exact h_Ioc1.union h_Ioi_τ1
  have hsplit : ∫ τ in Ioi τ_core, F_out τ = (∫ τ in Ioc τ_core τ₁, F_out τ) + (∫ τ in Ioc τ₁ (1 / 2), F_out τ) + ∫ τ in Ioi (1 / 2), F_out τ := by
    rw [← Ioc_union_Ioi_eq_Ioi hτcore_lt_τ₁.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h_Ioc1 h_Ioi_τ1,
      ← Ioc_union_Ioi_eq_Ioi (by linarith only [hτ₁_lt] : τ₁ ≤ 1 / 2), setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h_Ioc2 h_Ioi]; ring
  refine ⟨h_int_tot, ?_⟩
  calc (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ
      = (2 / Real.sqrt (2 * π)) * ((1 / τ_sd) * ∫ τ in Ioi τ_core, F_out τ) := by ring
    _ ≤ (2 / 2.506) * ((62.92 : ℝ) * ε_L) := mul_le_mul
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqrt2pi)
        (by rw [hsplit, mul_add, mul_add]; linarith only [h_part1, h_part2, h_part3])
        (mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun _ _ => by dsimp [F_out]; positivity))
        (by norm_num)
    _ ≤ 54 * ε_L := by nlinarith only [hεL_pos]

private lemma lobe_add_bound {c σ_star g' τ_sd z_pos ε : ℝ}
    (hc60 : 60 ≤ c) (hc_pos : 0 < c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hg'_pos : 0 < g') (hg'_def : g' = stripGDerivReal σ_star)
    (hτsd_pos : 0 < τ_sd) (hτsd_def : τ_sd = (c * g') ^ (-(1 / 2 : ℝ)))
    (hz_def : z_pos = c * (1 - σ_star)) (hz_gt : π < z_pos) (hε_def : ε = c ^ (-(1 / 3 : ℝ)))
    (hB_dec : (∀ τ ∈ Ioc 0 ((1 - σ_star) / 2), (1 / 10 : ℝ) * c * stripGDerivReal σ_star * τ ^ 2 ≤ c * vertUpsilon σ_star τ) ∧
      (∀ τ ∈ Ioc ((1 - σ_star) / 2) (1 / 2 : ℝ), (3 / 320 : ℝ) * (c * (1 - σ_star)) + (3 / 80 : ℝ) * c * (τ - (1 - σ_star) / 2) ≤ c * vertUpsilon σ_star τ) ∧
      (∀ τ ∈ Ioi (1 / 2 : ℝ), (3 / 320 : ℝ) * (c * (1 - σ_star)) + (3 / 320 : ℝ) * c + (3 / 40 : ℝ) * c * max 0 (Real.log τ) ≤ c * vertUpsilon σ_star τ))
    (hhalf : 1 / 2 < σ_star) :
    let F_out := fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)
    let F_add := fun τ : ℝ => F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1
    IntegrableOn F_add (Ioi ((1 - σ_star) / 2)) ∧
      (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi ((1 - σ_star) / 2), F_add τ ≤ 430 * ε * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
  dsimp only
  let F_out := fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)
  let F_add := fun τ : ℝ => F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  have hε_pos : 0 < ε := by rw [hε_def]; positivity
  let τ₁ := (1 - σ_star) / 2
  have hτ₁_pos : 0 < τ₁ := by positivity
  have hτ₁_lt : τ₁ < 1 / 4 := by dsimp [τ₁]; linarith only [hhalf]
  have hf_cont : Continuous F_out :=
    (Continuous.rpow (by fun_prop) continuous_const fun _ => Or.inl (by positivity)).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (intervalIntegral.continuous_primitive (fun a b => (vertUpsilon_continuousIntegrand σ_star).intervalIntegrable (μ := volume) a b) 0)))
  have hsqrt2pi : (2.506 : ℝ) ≤ Real.sqrt (2 * π) := Real.le_sqrt_of_sq_le (by nlinarith only [Real.pi_gt_d4, Real.pi_pos])
  have h_alg_le1 : ∀ τ : ℝ, (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 := fun τ =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [div_nonneg (sq_nonneg τ) (sq_nonneg (1 - σ_star))]) (by norm_num)
  have hF_add_cont : Continuous F_add := hf_cont.mul ((Continuous.rpow continuous_id continuous_const
    fun _ => Or.inr (by norm_num)).const_mul _ |>.min continuous_const)
  have h_Ioc_int : IntegrableOn F_add (Ioc τ₁ (1 / 2)) :=
    hF_add_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  obtain ⟨h_tail_int, h_tail_bd⟩ := integrable_log_tail (K := (3 / 40 : ℝ) * c) (by linarith only [hc60])
  have hpt_B : ∀ τ ∈ Ioi (1 / 2 : ℝ), (1 / τ_sd) * F_add τ ≤
      (Real.sqrt (2 * c) * Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 320 : ℝ) * c)) *
        (τ ^ (-(1 / 2 : ℝ)) * Real.exp (-((3 / 40 : ℝ) * c) * max 0 (Real.log τ))) := fun τ hτ => by
    have h_exp : Real.exp (-c * vertUpsilon σ_star τ) ≤ Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 320 : ℝ) * c) *
        Real.exp (-((3 / 40 : ℝ) * c) * max 0 (Real.log τ)) := by
      rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by rw [hz_def]; linarith only [hB_dec.2.2 τ hτ])
    have hτ0 : 0 < τ := lt_trans (by norm_num) (mem_Ioi.mp hτ)
    calc (1 / τ_sd) * F_add τ = ((1 / τ_sd) * (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ))) *
          Real.exp (-c * vertUpsilon σ_star τ) * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 := by dsimp [F_add, F_out]; ring
      _ ≤ (Real.sqrt (2 * c) * τ ^ (-(1 / 2 : ℝ))) * _ * 1 :=
          mul_le_mul (mul_le_mul (lobe_half_B hc_pos hσ0 hσ1 hg'_pos hg'_def hτsd_def hτ) h_exp (Real.exp_pos _).le
              (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hτ0.le _)))
            (min_le_right _ _) (le_min (mul_nonneg (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg hτ0.le _)) zero_le_one)
            (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hτ0.le _)) (by positivity))
      _ = _ := by ring
  have h_Ioi_int : IntegrableOn F_add (Ioi (1 / 2)) := by
    have h1 : IntegrableOn (fun τ : ℝ => (1 / τ_sd) * F_add τ) (Ioi (1 / 2)) := by
      refine (h_tail_int.const_mul (Real.sqrt (2 * c) * Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 320 : ℝ) * c))).mono'
        ((continuous_const.mul hF_add_cont).continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]; exact Filter.Eventually.of_forall fun τ hτ => by
        have hτ0 : 0 < τ := lt_trans (by norm_num) (mem_Ioi.mp hτ)
        rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (by dsimp [F_add, F_out]; exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le) (le_min (mul_nonneg (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg hτ0.le _)) zero_le_one)))]
        exact hpt_B τ hτ
    have h2 : IntegrableOn (fun τ : ℝ => τ_sd * ((1 / τ_sd) * F_add τ)) (Ioi (1 / 2)) := h1.const_mul τ_sd
    exact h2.congr_fun (fun τ _ => by field_simp [hτsd_pos.ne']) measurableSet_Ioi
  have h_partA : (1 / τ_sd) * ∫ τ in Ioc τ₁ (1 / 2), F_add τ ≤ 138 * ε * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
    have h_1sd : 1 / τ_sd ≤ c ^ (1 / 2 : ℝ) * τ₁ ^ (-(1 / 2 : ℝ)) := by
      have hg'_lt : g' < τ₁⁻¹ := by
        have h1 : 2 * σ_star / (1 - σ_star) < 2 / (1 - σ_star) := div_lt_div_of_pos_right (by linarith only [hσ1]) h1s_pos
        rw [hg'_def]; exact ((stripG_deriv_bounds hσ0 hσ1).2).trans (h1.trans_eq (by dsimp [τ₁]; rw [inv_div]))
      rw [hτsd_def, rpow_neg_half_eq_inv_sqrt (mul_pos hc_pos hg'_pos).le, one_div, inv_inv]
      calc Real.sqrt (c * g') ≤ Real.sqrt (c * τ₁⁻¹) := Real.sqrt_le_sqrt (by gcongr)
        _ = c ^ (1 / 2 : ℝ) * τ₁ ^ (-(1 / 2 : ℝ)) := by
            rw [Real.sqrt_mul hc_pos.le, Real.sqrt_eq_rpow, rpow_neg_half_eq_inv_sqrt hτ₁_pos.le, Real.sqrt_inv]
    let d₁ := fun τ : ℝ => τ₁ ^ (1 / 2 : ℝ) * Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁))
    let d₂ := fun τ : ℝ => (τ - τ₁) ^ (1 / 2 : ℝ) * Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁))
    have hd1 : IntegrableOn d₁ (Ioc τ₁ (1 / 2)) := (by fun_prop : Continuous d₁).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hd2 : IntegrableOn d₂ (Ioc τ₁ (1 / 2)) := ((ContinuousOn.rpow_const (continuousOn_id.sub continuousOn_const)
      fun _ _ => Or.inr (by norm_num)).mul (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁))).continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hptA : ∀ τ ∈ Ioc τ₁ (1 / 2), F_add τ ≤ (c ^ (1 / 6 : ℝ) * Real.exp (-(3 / 320 : ℝ) * z_pos)) * (d₁ τ + d₂ τ) := fun τ hτ => by
      have h_exp : Real.exp (-c * vertUpsilon σ_star τ) ≤ Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁)) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by rw [hz_def]; dsimp [τ₁]; linarith only [hB_dec.2.1 τ hτ])
      have hmin : min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 ≤ c ^ (1 / 6 : ℝ) * (τ₁ ^ (1 / 2 : ℝ) + (τ - τ₁) ^ (1 / 2 : ℝ)) := by
        refine (min_le_left _ _).trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hc_pos.le _))
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        refine le_of_sq_le_sq ?_ (by positivity)
        rw [Real.sq_sqrt (hτ₁_pos.trans hτ.1).le, add_sq, Real.sq_sqrt hτ₁_pos.le, Real.sq_sqrt (by linarith only [hτ.1])]
        linarith only [mul_nonneg (Real.sqrt_nonneg τ₁) (Real.sqrt_nonneg (τ - τ₁))]
      have hτ0 : 0 ≤ τ := (hτ₁_pos.trans hτ.1).le
      calc F_add τ ≤ (1 * (Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁)))) * _ :=
            mul_le_mul (mul_le_mul (h_alg_le1 τ) h_exp (Real.exp_pos _).le zero_le_one) hmin
              (le_min (mul_nonneg (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg hτ0 _)) zero_le_one) (by positivity)
        _ = _ := by dsimp [d₁, d₂]; ring
    have hm := setIntegral_mono_on h_Ioc_int ((hd1.add hd2).const_mul _) measurableSet_Ioc hptA
    dsimp only [Pi.add_apply] at hm
    rw [integral_const_mul, integral_add hd1 hd2] at hm
    have hi1 : ∫ τ in Ioc τ₁ (1 / 2), d₁ τ ≤ τ₁ ^ (1 / 2 : ℝ) * (80 / (3 * c)) := by
      dsimp [d₁]; rw [integral_const_mul, ← intervalIntegral.integral_of_le (by linarith only [hτ₁_lt] : τ₁ ≤ 1 / 2),
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => Real.exp (-(3 / 80 : ℝ) * c * u)) τ₁, sub_self,
        intervalIntegral.integral_of_le (by linarith only [hτ₁_lt])]
      obtain ⟨hl, hvl⟩ := integral_exp_neg_lin_Ioi (a := (0 : ℝ)) (k := (3 / 80 : ℝ) * c) (by positivity)
      have h2 : ∫ u in Ioc 0 (1 / 2 - τ₁), Real.exp (-(3 / 80 : ℝ) * c * u) ≤ 1 / ((3 / 80 : ℝ) * c) := by
        have hvl' : ∫ u in Ioi (0 : ℝ), Real.exp (-(3 / 80 : ℝ) * c * u) = 1 / ((3 / 80 : ℝ) * c) := by
          simpa only [mul_zero, Real.exp_zero, neg_mul] using hvl
        have hs' : IntegrableOn (fun u : ℝ => Real.exp (-(3 / 80 : ℝ) * c * u)) (Ioi 0) := by
          simpa only [neg_mul] using hl
        exact (setIntegral_mono_set hs' (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
          Ioc_subset_Ioi_self.eventuallySubset).trans_eq hvl'
      exact mul_le_mul_of_nonneg_left (h2.trans_eq (by ring)) (Real.rpow_nonneg hτ₁_pos.le _)
    have hi2 : ∫ τ in Ioc τ₁ (1 / 2), d₂ τ ≤ ((3 / 80 : ℝ) * c) ^ (-(3 / 2 : ℝ)) := by
      dsimp [d₂]; rw [← intervalIntegral.integral_of_le (by linarith only [hτ₁_lt] : τ₁ ≤ 1 / 2),
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ (1 / 2 : ℝ) * Real.exp (-(3 / 80 : ℝ) * c * u)) τ₁,
        sub_self, intervalIntegral.integral_of_le (by linarith only [hτ₁_lt])]
      obtain ⟨hs, hvs⟩ := integral_sqrt_mul_exp_neg_Ioi (k := (3 / 80 : ℝ) * c) (by positivity)
      rw [show (fun u : ℝ => u ^ (1 / 2 : ℝ) * Real.exp (-((3 / 80 : ℝ) * c) * u)) =
        fun u => u ^ (1 / 2 : ℝ) * Real.exp (-(3 / 80 : ℝ) * c * u) by ext u; ring_nf] at hs hvs
      exact (setIntegral_mono_set hs ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx =>
        mul_nonneg (Real.rpow_nonneg (mem_Ioi.mp hx).le _) (Real.exp_pos _).le)) Ioc_subset_Ioi_self.eventuallySubset).trans hvs
    have hz_pos : 0 < z_pos := by rw [hz_def]; positivity
    have hτ1_eq : τ₁ ^ (-(1 / 2 : ℝ)) = Real.sqrt 2 * c ^ (1 / 2 : ℝ) * z_pos ^ (-(1 / 2 : ℝ)) := by
      calc τ₁ ^ (-(1 / 2 : ℝ)) = (Real.sqrt ((1 - σ_star) / 2))⁻¹ := rpow_neg_half_eq_inv_sqrt hτ₁_pos.le
        _ = (Real.sqrt (c * (1 - σ_star) / (2 * c)))⁻¹ := by rw [show (1 - σ_star) / 2 = c * (1 - σ_star) / (2 * c) by field_simp [hc_pos.ne']]
        _ = (Real.sqrt z_pos / Real.sqrt (2 * c))⁻¹ := by rw [hz_def, Real.sqrt_div (mul_pos hc_pos h1s_pos).le]
        _ = Real.sqrt (2 * c) * (Real.sqrt z_pos)⁻¹ := by rw [inv_div, div_eq_mul_inv]
        _ = Real.sqrt 2 * c ^ (1 / 2 : ℝ) * z_pos ^ (-(1 / 2 : ℝ)) := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow c, ← rpow_neg_half_eq_inv_sqrt hz_pos.le]
    have h_bd2 : τ₁ ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) * c ^ (1 / 6 : ℝ) * ((3 / 80 : ℝ) * c) ^ (-(3 / 2 : ℝ)) ≤ 111 * ε := by
      have hz_lt : z_pos ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt π⁻¹ := by
        rw [rpow_neg_half_eq_inv_sqrt (by rw [hz_def]; positivity), ← Real.sqrt_inv]
        exact Real.sqrt_le_sqrt (by simpa only [one_div] using one_div_le_one_div_of_le Real.pi_pos hz_gt.le)
      have hnum1 : Real.sqrt 2 * Real.sqrt π⁻¹ ≤ 0.8 := by
        rw [← Real.sqrt_mul (by norm_num), Real.sqrt_le_left (by norm_num), mul_inv_le_iff₀ Real.pi_pos]; linarith only [Real.pi_gt_d4]
      have hnum2 : (80 / 3 : ℝ) ^ (3 / 2 : ℝ) ≤ 138.7 := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
        nlinarith only [show Real.sqrt (80 / 3) ≤ 5.2 by rw [Real.sqrt_le_left (by norm_num)]; norm_num]
      rw [hτ1_eq, Real.mul_rpow (by norm_num) hc_pos.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3 / 80),
        ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3 / 80), inv_div]
      have hc_pow : c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) * c ^ (1 / 6 : ℝ) * c ^ (-(3 / 2 : ℝ)) = ε := by
        rw [← Real.rpow_add hc_pos, ← Real.rpow_add hc_pos, ← Real.rpow_add hc_pos, hε_def]; norm_num
      calc _ = (Real.sqrt 2 * z_pos ^ (-(1 / 2 : ℝ))) * (80 / 3 : ℝ) ^ (3 / 2 : ℝ) *
              (c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) * c ^ (1 / 6 : ℝ) * c ^ (-(3 / 2 : ℝ))) := by ring
        _ ≤ 0.8 * 138.7 * ε := by rw [hc_pow]; gcongr; exact (mul_le_mul_of_nonneg_left hz_lt (Real.sqrt_nonneg _)).trans hnum1
        _ ≤ 111 * ε := by nlinarith only [hε_pos]
    have h_bd1 : c ^ (1 / 2 : ℝ) * c ^ (1 / 6 : ℝ) * (80 / (3 * c)) = (80 / 3 : ℝ) * ε := by
      have h1 : c ^ (1 / 2 : ℝ) * c ^ (1 / 6 : ℝ) = c ^ (2 / 3 : ℝ) := by rw [← Real.rpow_add hc_pos]; norm_num
      have h2 : c ^ (2 / 3 : ℝ) / c = ε := by nth_rw 2 [← Real.rpow_one c]; rw [← Real.rpow_sub hc_pos, hε_def]; norm_num
      calc _ = (80 / 3 : ℝ) * (c ^ (2 / 3 : ℝ) / c) := by rw [h1]; ring
        _ = _ := by rw [h2]
    have hτ₁_c : τ₁ ^ (-(1 / 2 : ℝ)) * τ₁ ^ (1 / 2 : ℝ) = 1 := by rw [← Real.rpow_add hτ₁_pos]; norm_num
    calc (1 / τ_sd) * ∫ τ in Ioc τ₁ (1 / 2), F_add τ
        ≤ (c ^ (1 / 2 : ℝ) * τ₁ ^ (-(1 / 2 : ℝ))) * ((c ^ (1 / 6 : ℝ) * Real.exp (-(3 / 320 : ℝ) * z_pos)) *
            (τ₁ ^ (1 / 2 : ℝ) * (80 / (3 * c)) + ((3 / 80 : ℝ) * c) ^ (-(3 / 2 : ℝ)))) :=
          mul_le_mul h_1sd (hm.trans (mul_le_mul_of_nonneg_left (add_le_add hi1 hi2) (by positivity)))
            (setIntegral_nonneg measurableSet_Ioc fun τ hτ => by
              have hτ0 : 0 ≤ τ := (hτ₁_pos.trans hτ.1).le
              dsimp [F_add, F_out]
              exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le)
                (le_min (mul_nonneg (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg hτ0 _)) zero_le_one))
            (by positivity)
      _ = ((τ₁ ^ (-(1 / 2 : ℝ)) * τ₁ ^ (1 / 2 : ℝ)) * (c ^ (1 / 2 : ℝ) * c ^ (1 / 6 : ℝ) * (80 / (3 * c))) +
            τ₁ ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) * c ^ (1 / 6 : ℝ) * ((3 / 80 : ℝ) * c) ^ (-(3 / 2 : ℝ))) *
            Real.exp (-(3 / 320 : ℝ) * z_pos) := by ring
      _ ≤ (80 / 3 * ε + 111 * ε) * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
          rw [hτ₁_c, one_mul, h_bd1]; exact mul_le_mul_of_nonneg_right (add_le_add le_rfl h_bd2) (Real.exp_pos _).le
      _ ≤ 138 * ε * Real.exp (-(3 / 320 : ℝ) * z_pos) := by nlinarith only [hε_pos, Real.exp_pos (-(3 / 320 : ℝ) * z_pos)]
  have h_partB : (1 / τ_sd) * ∫ τ in Ioi (1 / 2 : ℝ), F_add τ ≤ 120 * ε * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
    have hm1 := setIntegral_mono_on (h_Ioi_int.const_mul _) (h_tail_int.const_mul _) measurableSet_Ioi hpt_B
    rw [integral_const_mul, integral_const_mul] at hm1
    have hm2 : (1 / τ_sd) * ∫ τ in Ioi (1 / 2 : ℝ), F_add τ ≤
        (Real.sqrt (2 * c) * Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 320 : ℝ) * c)) * 2 :=
      hm1.trans (mul_le_mul_of_nonneg_left h_tail_bd (by positivity))
    have hc_exp : c * Real.exp (-(3 / 320 : ℝ) * c) ≤ 40 := by
      have h1 : (3 / 320 : ℝ) * c * Real.exp 1 ≤ Real.exp ((3 / 320 : ℝ) * c) := by
        have hadd := Real.add_one_le_exp ((3 / 320 : ℝ) * c - 1)
        rw [show (3 / 320 : ℝ) * c - 1 = (3 / 320 : ℝ) * c + -1 by ring, Real.exp_add, Real.exp_neg, ← div_eq_mul_inv] at hadd
        have hadd' : (3 / 320 : ℝ) * c ≤ Real.exp ((3 / 320 : ℝ) * c) / Real.exp 1 := by linarith only [hadd]
        exact (le_div_iff₀ (Real.exp_pos 1)).mp hadd'
      have he1 : (2.718 : ℝ) ≤ Real.exp 1 := (Real.exp_one_gt_d9.le).trans' (by norm_num)
      have hmul : (3 / 320 : ℝ) * 2.718 * (c * Real.exp (-(3 / 320 : ℝ) * c)) ≤ 1 := by
        rw [show -(3 / 320 : ℝ) * c = -((3 / 320 : ℝ) * c) by ring, Real.exp_neg]
        calc _ = ((3 / 320 : ℝ) * c * 2.718) * (Real.exp ((3 / 320 : ℝ) * c))⁻¹ := by ring
          _ ≤ ((3 / 320 : ℝ) * c * Real.exp 1) * (Real.exp ((3 / 320 : ℝ) * c))⁻¹ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1 (by positivity)) (inv_nonneg.mpr (Real.exp_pos _).le)
          _ ≤ Real.exp ((3 / 320 : ℝ) * c) * (Real.exp ((3 / 320 : ℝ) * c))⁻¹ :=
              mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (Real.exp_pos _).le)
          _ = 1 := mul_inv_cancel₀ (Real.exp_pos _).ne'
      linarith only [hmul]
    have hc56 : c ^ (5 / 6 : ℝ) ≤ c := by nth_rw 2 [← Real.rpow_one c]; exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hc60]) (by norm_num)
    have hc12 : Real.sqrt (2 * c) = Real.sqrt 2 * c ^ (5 / 6 : ℝ) * ε := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow c, hε_def, mul_assoc, ← Real.rpow_add hc_pos]; norm_num
    have hsq2 : Real.sqrt 2 ≤ 1.5 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hsqrt2c : Real.sqrt (2 * c) * Real.exp (-(3 / 320 : ℝ) * c) * 2 ≤ 120 * ε := by
      calc _ = 2 * Real.sqrt 2 * (c ^ (5 / 6 : ℝ) * Real.exp (-(3 / 320 : ℝ) * c)) * ε := by rw [hc12]; ring
        _ ≤ 2 * 1.5 * (c ^ (5 / 6 : ℝ) * Real.exp (-(3 / 320 : ℝ) * c)) * ε := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq2 (by norm_num)) (by positivity)) hε_pos.le
        _ ≤ 3 * (c * Real.exp (-(3 / 320 : ℝ) * c)) * ε := by
            rw [show (2 : ℝ) * 1.5 = 3 by norm_num]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc56 (Real.exp_pos _).le) (by norm_num)) hε_pos.le
        _ ≤ 3 * 40 * ε := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc_exp (by norm_num)) hε_pos.le
        _ = 120 * ε := by ring
    exact (hm2.trans_eq (by ring)).trans (mul_le_mul_of_nonneg_right hsqrt2c (Real.exp_pos _).le)
  have hsplit : ∫ τ in Ioi τ₁, F_add τ = (∫ τ in Ioc τ₁ (1 / 2), F_add τ) + ∫ τ in Ioi (1 / 2), F_add τ := by
    rw [← Ioc_union_Ioi_eq_Ioi (by linarith only [hτ₁_lt] : τ₁ ≤ 1 / 2)]; exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h_Ioc_int h_Ioi_int
  refine ⟨by rw [← Ioc_union_Ioi_eq_Ioi (by linarith only [hτ₁_lt] : τ₁ ≤ 1 / 2)]; exact h_Ioc_int.union h_Ioi_int, ?_⟩
  calc (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ₁, F_add τ
      = (2 / Real.sqrt (2 * π)) * ((1 / τ_sd) * ∫ τ in Ioi τ₁, F_add τ) := by ring
    _ ≤ (2 / 2.506) * ((258 : ℝ) * ε * Real.exp (-(3 / 320 : ℝ) * z_pos)) := mul_le_mul
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqrt2pi)
        (by rw [hsplit, mul_add]; linarith only [h_partA, h_partB])
        (mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun τ hτ => by
          have hτ0 : 0 ≤ τ := (hτ₁_pos.trans (mem_Ioi.mp hτ)).le
          dsimp [F_add, F_out]
          exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le)
            (le_min (mul_nonneg (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg hτ0 _)) zero_le_one)))
        (by norm_num)
    _ ≤ 430 * ε * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
        have hnn : 0 ≤ ε * Real.exp (-(3 / 320 : ℝ) * z_pos) := by positivity
        nlinarith only [hnn]

private lemma lobe_outer_and_add_bounds {Δ₁ U c Δ ξ σ_star : ℝ}
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U) (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (amp : LobeSaddleAmp σ_star (c ^ (1 / 3 : ℝ) * σ_star) (c ^ (1 / 3 : ℝ) * (1 - σ_star)))
    (h_eps0 : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤ min (3 / 1000 : ℝ) ((4 * amp.M) ^ (-(4 / 3 : ℝ)))) :
    let ε_L := saddleEpsL c σ_star
    let τ_sd := (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))
    let τ_core := ε_L ^ (-(1 / 4 : ℝ)) * τ_sd
    let z_pos := c * (1 - σ_star)
    let ε := c ^ (-(1 / 3 : ℝ))
    let F_out := fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)
    let F_add := fun τ : ℝ => F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1
    IntegrableOn F_out (Ioi τ_core) ∧
    (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ ≤ 54 * ε_L ∧
    (0 < amp.Λ_add → IntegrableOn F_add (Ioi ((1 - σ_star) / 2)) ∧
      (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi ((1 - σ_star) / 2), F_add τ ≤ 430 * ε * Real.exp (-(3 / 320 : ℝ) * z_pos)) := by
  dsimp only
  have hc60 : 60 ≤ c := by have := Real.one_le_rpow hU (by norm_num : (0 : ℝ) ≤ 3 / 2); linarith [(le_max_right (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ))).trans hc]
  have hc_pos : 0 < c := by linarith
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  let g' := stripGDerivReal σ_star; let ε_L := saddleEpsL c σ_star; let τ_sd := (c * g') ^ (-(1 / 2 : ℝ))
  let a := ε_L ^ (-(1 / 4 : ℝ)); let τ_core := a * τ_sd; let z_pos := c * (1 - σ_star); let ε := c ^ (-(1 / 3 : ℝ))
  have hg'_pos : 0 < g' := stripGDerivReal_pos hσ0 hσ1
  have hεL_pos : 0 < ε_L := saddleEpsL_pos hc_pos hσ0 hσ1
  have hτsd_pos : 0 < τ_sd := Real.rpow_pos_of_pos (mul_pos hc_pos hg'_pos) _
  have ha_pos : 0 < a := Real.rpow_pos_of_pos hεL_pos _
  have hτcore_pos : 0 < τ_core := mul_pos ha_pos hτsd_pos
  obtain ⟨_, _, hz_gt⟩ := saddle_endpoint_scales hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq
  obtain ⟨hz_eps, hx_eps, hεL_ub⟩ := saddleEpsL_bounds hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq
  have hεL_le_3e3 : ε_L ≤ 3 / 1000 := hεL_ub.le.trans (h_eps0.trans (min_le_left _ _))
  have hεL_34_pow4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 = ε_L ^ 3 := by
    rw [← Real.rpow_natCast (ε_L ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul hεL_pos.le,
      show (3 / 4 : ℝ) * (4 : ℕ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have hεL_34_le_18 : ε_L ^ (3 / 4 : ℝ) ≤ 1 / 8 := by
    have h4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := by
      rw [hεL_34_pow4]; exact (pow_le_pow_left₀ hεL_pos.le hεL_le_3e3 3).trans (by norm_num)
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h4
  have hτcore_eq : τ_core = ε_L ^ (3 / 4 : ℝ) * min σ_star (1 - σ_star) := by
    have hm := (lt_min hσ0 h1s_pos).ne'
    have h_add : ε_L ^ (-(1 / 4 : ℝ)) * ε_L = ε_L ^ (3 / 4 : ℝ) := by
      nth_rw 2 [← Real.rpow_one ε_L]; rw [← Real.rpow_add hεL_pos]; norm_num
    calc τ_core = (ε_L ^ (-(1 / 4 : ℝ)) * ε_L) * min σ_star (1 - σ_star) := by
          dsimp [τ_core, a, τ_sd, ε_L, saddleEpsL]; rw [mul_assoc, div_mul_cancel₀ _ hm]
      _ = _ := by rw [h_add]
  have hu_ge : (18.25 : ℝ) ≤ ε_L ^ (-(1 / 2 : ℝ)) := by
    have hsq : (18.25 : ℝ) ^ 2 ≤ (ε_L ^ (-(1 / 2 : ℝ))) ^ 2 := by
      rw [← Real.rpow_natCast (ε_L ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hεL_pos.le,
        show -(1 / 2 : ℝ) * (2 : ℕ) = (-1 : ℝ) by norm_num, Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hεL_pos]; nlinarith [hεL_le_3e3]
    exact le_of_sq_le_sq hsq (Real.rpow_nonneg hεL_pos.le _)
  have hεL_inv2_ge : (100000 : ℝ) ≤ ε_L ^ (-2 : ℝ) := by
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hεL_pos.le, Real.rpow_natCast, inv_eq_one_div, le_div_iff₀ (pow_pos hεL_pos 2)]
    nlinarith [pow_le_pow_left₀ hεL_pos.le hεL_le_3e3 2]
  have hτsd_sq : τ_sd ^ 2 = (c * g')⁻¹ := by
    dsimp [τ_sd]; rw [rpow_neg_half_eq_inv_sqrt (by positivity), inv_pow, Real.sq_sqrt (by positivity)]
  have h_gauss10 : ∀ b : ℝ, τ_core ≤ b →
      (1 / τ_sd) * ∫ τ in Ioc τ_core b, Real.exp (-(1 / 10 : ℝ) * (c * g') * τ ^ 2) ≤ (62.89 : ℝ) * ε_L := fun b _ =>
    lobe_gauss10_tail hc_pos hg'_pos hεL_pos hτsd_pos ha_pos hτcore_pos rfl rfl hτsd_sq hu_ge
  obtain ⟨hA_dec, hB_dec⟩ := lobe_vertical_phase_decay_bounds (c := c) (σ_star := σ_star) (by linarith) hσ0 hσ1
  have h_out : IntegrableOn (fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)) (Ioi τ_core) ∧
      (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ) ≤ 54 * ε_L := by
    rcases le_or_gt σ_star (1 / 2) with hhalf | hhalf
    · exact lobe_outer_le_half hc_pos hσ0 hσ1 hg'_pos rfl hεL_pos hτsd_pos rfl
        hτcore_pos hτcore_eq hεL_34_le_18 hεL_inv2_ge (hx_eps hhalf) h_gauss10 (hA_dec hhalf) hhalf
    · exact lobe_outer_gt_half hc_pos hσ0 hσ1 hg'_pos rfl hεL_pos hτsd_pos rfl hτsd_sq
        hτcore_pos hτcore_eq hεL_34_le_18 hεL_inv2_ge hz_eps h_gauss10 (hB_dec hhalf) hhalf
  refine ⟨h_out.1, h_out.2, fun h_add_pos => ?_⟩
  exact lobe_add_bound hc60 hc_pos hσ0 hσ1 hg'_pos rfl hτsd_pos rfl rfl (by nlinarith [hΔ₁, Real.pi_pos, hz_gt])
    rfl (hB_dec (amp.hΛ_add_half h_add_pos)) (amp.hΛ_add_half h_add_pos)

/-- **Proposition P.4 (`cel:L5`, `(cel:5.7)`–`(cel:5.9)` & Remark P.4a `cel:L5a`):**
uniform lobe saddle asymptotic for abstract amplitudes `(W_S, W_D)`. -/
theorem lobe_saddle_asymptotic {Δ₁ U c Δ ξ σ_star : ℝ}
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U) (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (amp : LobeSaddleAmp σ_star (c ^ (1 / 3 : ℝ) * σ_star) (c ^ (1 / 3 : ℝ) * (1 - σ_star)))
    (h_eps0 : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤
      min (3 / 1000 : ℝ) ((4 * amp.M) ^ (-(4 / 3 : ℝ)))) :
    let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
    let W₀ := (amp.W_S ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ)).re + (amp.W_D ((c ^ (1 / 3 : ℝ) * (1 - σ_star) : ℝ) : ℂ)).re
    let L_lead := (1 / (2 * π * ξ)) * K₀ * W₀ * Real.sqrt (2 * π / (c * stripGDerivReal σ_star))
    let I_val := lobeSaddleIntegral amp.W_S amp.W_D c ξ σ_star
    let z_pos := c * (1 - σ_star)
    let ε := c ^ (-(1 / 3 : ℝ))
    (mellinK0 c (σ_star : ℂ) ξ).im = 0 ∧ 0 < K₀ ∧ I_val.im = 0 ∧
      |(I_val.re - L_lead) / L_lead| ≤
        (8 * amp.M + 54 * amp.Λ + 109) * saddleEpsL c σ_star +
          430 * amp.Λ_add * (ε / W₀) * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
  dsimp only
  have hc_pos : 0 < c := by linarith [(le_max_left _ _).trans hc]
  have hξ_pos : 0 < ξ := by rw [hξ]; exact div_pos (by linarith) hc_pos
  let g' := stripGDerivReal σ_star; let ε_L := saddleEpsL c σ_star; let τ_sd := (c * g') ^ (-(1 / 2 : ℝ))
  let τ_core := ε_L ^ (-(1 / 4 : ℝ)) * τ_sd; let ε := c ^ (-(1 / 3 : ℝ))
  let x_pos := c ^ (1 / 3 : ℝ) * σ_star; let x_neg := c ^ (1 / 3 : ℝ) * (1 - σ_star); let z_pos := c * (1 - σ_star)
  let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re; let W₀ := (amp.W_S (x_pos : ℂ)).re + (amp.W_D (x_neg : ℂ)).re
  have hg'_pos : 0 < g' := stripGDerivReal_pos hσ0 hσ1
  have hτsd_pos : 0 < τ_sd := Real.rpow_pos_of_pos (mul_pos hc_pos (stripGDerivReal_pos hσ0 hσ1)) _
  have hεL_pos : 0 < ε_L := saddleEpsL_pos hc_pos hσ0 hσ1
  have hτcore_pos : 0 < τ_core := mul_pos (Real.rpow_pos_of_pos hεL_pos _) hτsd_pos
  have hK₀_spec := mellinK0_saddle_pos hc_pos hξ_pos hσ0 hσ1
  have hK₀_pos : 0 < K₀ := hK₀_spec.2
  have hW₀_pos : 0 < W₀ := amp.hW0_pos
  let f := fun τ : ℝ => mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
    (amp.W_S (((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (ε : ℂ)) + amp.W_D ((1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / (ε : ℂ)))
  have hf_int : Integrable f := lobeSaddle_integrable hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq amp
  obtain ⟨_, h_symm, h_outer_pt⟩ := lobe_integrand_cont_symm_bound hc_pos hξ_pos hσ0 hσ1 amp
  have h_int_real : (∫ τ : ℝ, f τ).im = 0 := by
    have hconj : starRingEnd ℂ (∫ τ : ℝ, f τ) = ∫ τ : ℝ, f τ := by
      rw [← integral_conj]
      calc ∫ τ : ℝ, starRingEnd ℂ (f τ) = ∫ τ : ℝ, f (-τ) := integral_congr_ae (Filter.Eventually.of_forall fun τ => (h_symm τ).symm)
        _ = ∫ τ : ℝ, f τ := integral_neg_eq_self f volume
    exact Complex.conj_eq_iff_im.mp hconj
  have hI_eq : lobeSaddleIntegral amp.W_S amp.W_D c ξ σ_star = ((1 / (2 * π * ξ) : ℝ) : ℂ) * ∫ τ : ℝ, f τ := rfl
  have h_Ival_im : (lobeSaddleIntegral amp.W_S amp.W_D c ξ σ_star).im = 0 := by
    rw [hI_eq]; simp [Complex.mul_im, h_int_real]
  refine ⟨hK₀_spec.1, hK₀_pos, h_Ival_im, ?_⟩
  let F_rel := fun τ : ℝ => f τ / ((K₀ * W₀ : ℝ) : ℂ)
  have hF_rel_int : Integrable F_rel := hf_int.div_const _
  have hI_re_eq : (lobeSaddleIntegral amp.W_S amp.W_D c ξ σ_star).re = (1 / (2 * π * ξ)) * (K₀ * W₀) * ∫ τ : ℝ, (F_rel τ).re := by
    have hf_eq : f = fun τ => ((K₀ * W₀ : ℝ) : ℂ) * F_rel τ := funext fun τ => by
      dsimp [F_rel]; rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (mul_pos hK₀_pos hW₀_pos).ne')]
    rw [hI_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    conv_lhs => rw [hf_eq, integral_const_mul]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hF_rel_int]
    simp [Complex.reCLM_apply]; ring
  have h_sqrt_eq : Real.sqrt (2 * π / (c * g')) = Real.sqrt (2 * π) * τ_sd := by
    rw [Real.sqrt_div (by positivity)]; dsimp [τ_sd]
    rw [rpow_neg_half_eq_inv_sqrt (by positivity), div_eq_mul_inv]
  set L_lead := (1 / (2 * π * ξ)) * K₀ * W₀ * Real.sqrt (2 * π / (c * g'))
  have h_div_eq : ((lobeSaddleIntegral amp.W_S amp.W_D c ξ σ_star).re - L_lead) / L_lead =
      (1 / (Real.sqrt (2 * π) * τ_sd)) * ((∫ τ : ℝ, (F_rel τ).re) - Real.sqrt (2 * π) * τ_sd) := by
    rw [hI_re_eq]; dsimp [L_lead]; rw [h_sqrt_eq]
    have h1 : (1 / (2 * π * ξ)) * (K₀ * W₀) ≠ 0 := by positivity
    field_simp [h1]
  let G_g := fun τ : ℝ => Real.exp (-(τ / τ_sd) ^ 2 / 2)
  have hG_int : Integrable G_g := by
    rw [show G_g = fun τ => Real.exp (-(1 / (2 * τ_sd ^ 2)) * τ ^ 2) by ext τ; dsimp [G_g]; congr 1; field_simp [hτsd_pos.ne']]
    exact integrable_exp_neg_mul_sq (by positivity)
  have hG_val : ∫ τ : ℝ, G_g τ = Real.sqrt (2 * π) * τ_sd := by
    rw [show G_g = fun τ => Real.exp (-(1 / (2 * τ_sd ^ 2)) * τ ^ 2) by ext τ; dsimp [G_g]; congr 1; field_simp [hτsd_pos.ne'],
      integral_gaussian, show π / (1 / (2 * τ_sd ^ 2)) = (2 * π) * τ_sd ^ 2 by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hτsd_pos.le]
  have h_diff_int : Integrable (fun τ : ℝ => ‖F_rel τ - (G_g τ : ℂ)‖) := (hF_rel_int.sub (Complex.ofRealCLM.integrable_comp hG_int)).norm
  have h_abs_le : |(∫ τ : ℝ, (F_rel τ).re) - Real.sqrt (2 * π) * τ_sd| ≤ ∫ τ : ℝ, ‖F_rel τ - (G_g τ : ℂ)‖ := by
    change |(∫ τ : ℝ, Complex.reCLM (F_rel τ)) - Real.sqrt (2 * π) * τ_sd| ≤ _
    rw [← hG_val, ← integral_sub (Complex.reCLM.integrable_comp hF_rel_int) hG_int]
    refine abs_integral_le_integral_abs.trans (integral_mono ((Complex.reCLM.integrable_comp hF_rel_int).sub hG_int).abs h_diff_int fun τ => ?_)
    rw [show Complex.reCLM (F_rel τ) - G_g τ = (F_rel τ - (G_g τ : ℂ)).re by simp]; exact Complex.abs_re_le_norm _
  have h_compl_le : ∫ τ in (Icc (-τ_core) τ_core)ᶜ, ‖F_rel τ - (G_g τ : ℂ)‖ ≤
      2 * (∫ τ in Ioi τ_core, ‖F_rel τ‖) + 2 * (∫ τ in Ioi τ_core, G_g τ) := by
    have h_disj : Disjoint (Iio (-τ_core)) (Ioi τ_core) :=
      disjoint_iff_forall_ne.mpr fun a ha b hb => by linarith [mem_Iio.mp ha, mem_Ioi.mp hb]
    have h_even_Iio : ∀ {g : ℝ → ℝ}, Integrable g → (∀ τ, g (-τ) = g τ) → ∫ τ in Iio (-τ_core), g τ = ∫ τ in Ioi τ_core, g τ :=
      fun {g} _ hev => by
        calc ∫ τ in Iio (-τ_core), g τ = ∫ τ in Iic (-τ_core), g τ := (integral_Iic_eq_integral_Iio).symm
          _ = ∫ τ in Iic (-τ_core), g (-τ) := setIntegral_congr_fun measurableSet_Iic fun τ _ => (hev τ).symm
          _ = ∫ τ in Ioi (- -τ_core), g τ := integral_comp_neg_Iic (-τ_core) g
          _ = ∫ τ in Ioi τ_core, g τ := by rw [neg_neg]
    have h_tri : ∫ τ in (Icc (-τ_core) τ_core)ᶜ, ‖F_rel τ - (G_g τ : ℂ)‖ ≤
        ∫ τ in (Icc (-τ_core) τ_core)ᶜ, (‖F_rel τ‖ + G_g τ) :=
      setIntegral_mono_on h_diff_int.integrableOn (hF_rel_int.norm.add hG_int).integrableOn measurableSet_Icc.compl fun τ _ => by
        refine (norm_sub_le _ _).trans_eq ?_; rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hcompl_eq : (Icc (-τ_core) τ_core)ᶜ = Iio (-τ_core) ∪ Ioi τ_core := by
      ext τ; simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi]
      constructor
      · intro h; by_cases h1 : τ < -τ_core
        · exact Or.inl h1
        · exact Or.inr (lt_of_not_ge fun h2 => h ⟨not_lt.mp h1, h2⟩)
      · rintro (h | h) ⟨h1, h2⟩ <;> linarith
    rw [integral_add hF_rel_int.norm.integrableOn hG_int.integrableOn, hcompl_eq,
      setIntegral_union h_disj measurableSet_Ioi hF_rel_int.norm.integrableOn hF_rel_int.norm.integrableOn,
      setIntegral_union h_disj measurableSet_Ioi hG_int.integrableOn hG_int.integrableOn,
      h_even_Iio hF_rel_int.norm (fun τ => by
        have h_symm' : f (-τ) = starRingEnd ℂ (f τ) := h_symm τ
        dsimp [F_rel]; rw [h_symm', norm_div, Complex.norm_conj, norm_div]),
      h_even_Iio hG_int (fun τ => by dsimp [G_g]; simp [neg_div])] at h_tri
    rw [hcompl_eq]
    linarith only [h_tri]
  have h_core := lobe_core_error_bound hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq amp h_eps0
  obtain ⟨hFout_int, h_outer_bd, h_add_spec⟩ := lobe_outer_and_add_bounds hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq amp h_eps0
  let F_out := fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)
  let F_add_pt := fun τ : ℝ => if (1 - σ_star) / 2 < τ then F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 else 0
  have h_F_outer_le : (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖) ≤
      54 * amp.Λ * ε_L + 430 * amp.Λ_add * (ε / W₀) * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
    by_cases h_add : 0 < amp.Λ_add
    · obtain ⟨hFadd_int, h_add_bd⟩ := h_add_spec h_add
      have hhalf := amp.hΛ_add_half h_add
      let τ₁ := (1 - σ_star) / 2
      have hεL_34 : ε_L ^ (3 / 4 : ℝ) ≤ 1 / 8 := by
        have h4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := by
          rw [← Real.rpow_natCast (ε_L ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul hεL_pos.le,
            show (3 / 4 : ℝ) * (4 : ℕ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
          have h_le3 : ε_L ≤ 3 / 1000 := (saddleEpsL_bounds hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq).2.2.le.trans (h_eps0.trans (min_le_left _ _))
          exact (pow_le_pow_left₀ hεL_pos.le h_le3 3).trans (by norm_num)
        exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h4
      have hτcore_lt_τ₁ : τ_core < τ₁ := by
        have hid : τ_core = ε_L ^ (3 / 4 : ℝ) * min σ_star (1 - σ_star) := by
          have hm := (lt_min hσ0 (sub_pos.mpr hσ1)).ne'
          have h_add : ε_L ^ (-(1 / 4 : ℝ)) * ε_L = ε_L ^ (3 / 4 : ℝ) := by
            nth_rw 2 [← Real.rpow_one ε_L]; rw [← Real.rpow_add hεL_pos]; norm_num
          calc τ_core = (ε_L ^ (-(1 / 4 : ℝ)) * ε_L) * min σ_star (1 - σ_star) := by
                dsimp [τ_core, ε_L, saddleEpsL, τ_sd]; rw [mul_assoc, div_mul_cancel₀ _ hm]
            _ = _ := by rw [h_add]
        rw [hid, min_eq_right (by linarith)]; dsimp [τ₁]
        nlinarith [hεL_34, sub_pos.mpr hσ1, Real.rpow_nonneg hεL_pos.le (3 / 4 : ℝ)]
      have h_add_zero : ∀ τ ∈ Ioc τ_core τ₁, F_add_pt τ = 0 := fun τ hτ => by
        dsimp [F_add_pt]; split_ifs with h <;> first | rfl | exact absurd h (not_lt.mpr (hτ.2 : τ ≤ (1 - σ_star) / 2))
      have h_add_pos : ∀ τ ∈ Ioi τ₁, F_add_pt τ = F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 := fun τ hτ => by
        dsimp [F_add_pt]; split_ifs with h <;> first | rfl | exact absurd (hτ : (1 - σ_star) / 2 < τ) h
      have hFadd_pt_Ioc : IntegrableOn F_add_pt (Ioc τ_core τ₁) :=
        integrableOn_zero.congr_fun (fun τ hτ => (h_add_zero τ hτ).symm) measurableSet_Ioc
      have hFadd_pt_Ioi : IntegrableOn F_add_pt (Ioi τ₁) :=
        hFadd_int.congr_fun (fun τ hτ => (h_add_pos τ hτ).symm) measurableSet_Ioi
      have hFadd_pt_int : IntegrableOn F_add_pt (Ioi τ_core) := by
        rw [← Ioc_union_Ioi_eq_Ioi hτcore_lt_τ₁.le]; exact hFadd_pt_Ioc.union hFadd_pt_Ioi
      have hFadd_pt_eq : ∫ τ in Ioi τ_core, F_add_pt τ = ∫ τ in Ioi τ₁, F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 := by
        rw [← Ioc_union_Ioi_eq_Ioi hτcore_lt_τ₁.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hFadd_pt_Ioc hFadd_pt_Ioi,
          setIntegral_eq_zero_of_forall_eq_zero h_add_zero, zero_add,
          setIntegral_congr_fun measurableSet_Ioi h_add_pos]
      have hm := setIntegral_mono_on hF_rel_int.norm.integrableOn ((hFout_int.const_mul amp.Λ).add (hFadd_pt_int.const_mul (amp.Λ_add / W₀)))
        measurableSet_Ioi fun τ hτ => (h_outer_pt τ (hτcore_pos.trans hτ).le).trans_eq (by dsimp [F_add_pt]; split_ifs <;> ring)
      dsimp only [Pi.add_apply] at hm
      rw [integral_add (hFout_int.const_mul _) (hFadd_pt_int.const_mul _), integral_const_mul, integral_const_mul, hFadd_pt_eq] at hm
      have hlhs : (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖) =
          (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, ‖F_rel τ‖ := by ring
      calc (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖)
          ≤ amp.Λ * ((2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ) +
              (amp.Λ_add / W₀) * ((2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ₁, F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1) := by
            rw [hlhs]; exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq (by ring)
        _ ≤ amp.Λ * (54 * ε_L) + (amp.Λ_add / W₀) * (430 * ε * Real.exp (-(3 / 320 : ℝ) * z_pos)) :=
            add_le_add (mul_le_mul_of_nonneg_left h_outer_bd (by linarith only [amp.hΛ]))
              (mul_le_mul_of_nonneg_left h_add_bd (div_nonneg amp.hΛ_add hW₀_pos.le))
        _ = _ := by ring
    · have h0 : amp.Λ_add = 0 := le_antisymm (not_lt.mp h_add) amp.hΛ_add
      have hm := setIntegral_mono_on hF_rel_int.norm.integrableOn (hFout_int.const_mul amp.Λ) measurableSet_Ioi fun τ hτ =>
        (h_outer_pt τ (hτcore_pos.trans hτ).le).trans_eq (by rw [h0]; simp; ring)
      rw [integral_const_mul] at hm
      have hlhs : (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖) =
          (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, ‖F_rel τ‖ := by ring
      calc (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖)
          ≤ amp.Λ * ((2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ) := by
            rw [hlhs]; exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq (by ring)
        _ ≤ amp.Λ * (54 * ε_L) := mul_le_mul_of_nonneg_left h_outer_bd (by linarith [amp.hΛ])
        _ = 54 * amp.Λ * ε_L + 430 * amp.Λ_add * (ε / W₀) * Real.exp (-(3 / 320 : ℝ) * z_pos) := by rw [h0]; ring
  rw [h_div_eq, abs_mul, abs_of_pos (by positivity : 0 < 1 / (Real.sqrt (2 * π) * τ_sd))]
  dsimp only at h_core
  have h1 := mul_le_mul_of_nonneg_left (h_abs_le.trans ((integral_add_compl measurableSet_Icc h_diff_int).symm ▸
    (add_le_add le_rfl h_compl_le))) (by positivity : 0 ≤ 1 / (Real.sqrt (2 * π) * τ_sd))
  have h1' : (1 / (Real.sqrt (2 * π) * τ_sd)) * |(∫ τ : ℝ, (F_rel τ).re) - Real.sqrt (2 * π) * τ_sd| ≤
      (1 / (Real.sqrt (2 * π) * τ_sd)) * ((∫ τ in Icc (-τ_core) τ_core, ‖F_rel τ - (G_g τ : ℂ)‖) + 2 * ∫ τ in Ioi τ_core, G_g τ) +
        (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖) :=
    h1.trans_eq (by ring)
  have h_core' : (1 / (Real.sqrt (2 * π) * τ_sd)) *
      ((∫ τ in Icc (-τ_core) τ_core, ‖F_rel τ - (G_g τ : ℂ)‖) + 2 * ∫ τ in Ioi τ_core, G_g τ) ≤ (7.7 * amp.M + 108.6) * ε_L := h_core
  have h78 : (7.7 * amp.M + 108.6) * ε_L + 54 * amp.Λ * ε_L ≤ (8 * amp.M + 54 * amp.Λ + 109) * ε_L :=
    calc (7.7 * amp.M + 108.6) * ε_L + 54 * amp.Λ * ε_L = (7.7 * amp.M + 54 * amp.Λ + 108.6) * ε_L := by ring
      _ ≤ (8 * amp.M + 54 * amp.Λ + 109) * ε_L := mul_le_mul_of_nonneg_right (by linarith only [amp.hM]) hεL_pos.le
  linarith [h1', h_core', h_F_outer_le, h78]

/-- Explicit non-vacuous witness satisfying `LobeSaddleAmp` and `lobe_saddle_asymptotic`. -/
theorem lobeSaddleAmp_nonvacuous :
    ∃ (Δ₁ U c Δ ξ σ_star : ℝ)
      (_hΔ₁ : 1 ≤ Δ₁) (_hU : 1 ≤ U) (_hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
      (_hΔ_lo : Δ₁ ≤ Δ) (_hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
      (_hξ : ξ = Δ / c) (_hσ0 : 0 < σ_star) (_hσ1 : σ_star < 1) (_hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
      (amp : LobeSaddleAmp σ_star (c ^ (1 / 3 : ℝ) * σ_star) (c ^ (1 / 3 : ℝ) * (1 - σ_star))),
      max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤
        min (3 / 1000 : ℝ) ((4 * amp.M) ^ (-(4 / 3 : ℝ))) := by
  let Δ₁ : ℝ := 10 ^ 6; let U : ℝ := 2 ^ 16; let c : ℝ := 2 ^ 33; let Δ : ℝ := 10 ^ 6; let ξ : ℝ := Δ / c
  have hU32 : U ^ (3 / 2 : ℝ) = (2 : ℝ) ^ 24 := by
    dsimp [U]; rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num),
      show (16 : ℕ) * (3 / 2 : ℝ) = (24 : ℕ) by norm_num, Real.rpow_natCast]
  have hc23 : c ^ (-(2 / 3 : ℝ)) = (2 : ℝ) ^ (-22 : ℝ) := by
    dsimp [c]; rw [← Real.rpow_natCast (2 : ℝ) 33, ← Real.rpow_mul (by norm_num)]; norm_num
  have hpi2 : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hexp_ge : (5 / 6 : ℝ) ≤ Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) := by
    rw [hc23, show (-22 : ℝ) = -(22 : ℕ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast, ← one_div]
    dsimp [U]
    have hpi_mul : π ^ 2 * (2 : ℝ) ^ 16 * (1 / 2 ^ 22) ≤ 10 * 2 ^ 16 * (1 / 2 ^ 22) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpi2 (by positivity)) (by positivity)
    linarith [Real.add_one_le_exp (-(π ^ 2 * (2 : ℝ) ^ 16 * (1 / 2 ^ 22))),
      show (10 : ℝ) * 2 ^ 16 * (1 / 2 ^ 22) ≤ 1 / 6 by norm_num]
  have hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) := by
    have h1 := mul_le_mul (div_le_div_of_nonneg_left (a := c) (by dsimp [c]; norm_num) (by positivity) hpi2) hexp_ge (by norm_num) (by positivity)
    exact (by dsimp [Δ, c]; norm_num : Δ ≤ c / 10 * (5 / 6)).trans h1
  obtain ⟨σ_star, ⟨⟨hσ0, hσ1⟩, hσ_eq⟩, _⟩ := exists_unique_saddleSigma (ξ := ξ) (by dsimp [ξ, Δ, c]; norm_num)
    (by dsimp [ξ, Δ, c]; nlinarith)
  let amp : LobeSaddleAmp σ_star (c ^ (1 / 3 : ℝ) * σ_star) (c ^ (1 / 3 : ℝ) * (1 - σ_star)) :=
    { W_S := fun w => (1 + w)⁻¹, W_D := fun _ => 0, M := 1, Λ := 1, Λ_add := 0
      hM := le_rfl, hΛ := le_rfl, hΛ_add := le_rfl
      hW_S_diff := fun w hw => ((differentiableAt_const (1 : ℂ)).add differentiableAt_id).inv
        (fun h => by have := congrArg Complex.re h; simp at this; linarith [show 0 < w.re from hw]) |>.differentiableWithinAt
      hW_D_diff := differentiableOn_const _
      hW_S_real := fun x _ => by rw [show (1 + (x : ℂ))⁻¹ = (((1 + x)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_im]
      hW_D_real := fun _ _ => rfl
      hW_S_nonneg := by rw [show (1 + ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ))⁻¹ = (((1 + c ^ (1 / 3 : ℝ) * σ_star)⁻¹ : ℝ) : ℂ) by
        push_cast; rfl, Complex.ofReal_re]; positivity
      hW_D_nonneg := by simp
      hW0_pos := by rw [show (1 + ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ))⁻¹ = (((1 + c ^ (1 / 3 : ℝ) * σ_star)⁻¹ : ℝ) : ℂ) by
        push_cast; rfl, Complex.ofReal_re, Complex.zero_re, add_zero]; positivity
      hA1_S := fun y _ => by
        set x := c ^ (1 / 3 : ℝ) * σ_star
        have hx : 0 < x := mul_pos (Real.rpow_pos_of_pos (by dsimp [c]; norm_num) _) hσ0
        have hne1 : 1 + ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
        have hne2 : 1 + (x : ℂ) ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
        rw [show (1 + ((x : ℂ) + (y : ℂ) * Complex.I))⁻¹ - (1 + (x : ℂ))⁻¹ =
            -((y : ℂ) * Complex.I) / ((1 + ((x : ℂ) + (y : ℂ) * Complex.I)) * (1 + (x : ℂ))) by field_simp [hne1, hne2]; ring,
          norm_div, norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
          show ‖1 + (x : ℂ)‖ = 1 + x by rw [show 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_of_nonneg (by linarith)],
          show ((1 + (x : ℂ))⁻¹).re = (1 + x)⁻¹ by rw [show (1 + (x : ℂ))⁻¹ = (((1 + x)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]]
        have h_re : 1 + x ≤ ‖1 + ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by simpa using Complex.re_le_norm (1 + ((x : ℂ) + (y : ℂ) * Complex.I))
        calc |y| / (‖1 + ((x : ℂ) + (y : ℂ) * Complex.I)‖ * (1 + x)) ≤ |y| / (x * (1 + x)) := by gcongr; linarith [h_re]
          _ = (|y| / x) * (1 + x)⁻¹ := by field_simp [hx.ne', (by linarith : 1 + x ≠ 0)]
          _ ≤ 4 * 1 * (|y| / x) * (1 + x)⁻¹ := by nlinarith [div_nonneg (abs_nonneg y) hx.le, show (0 : ℝ) < (1 + x)⁻¹ by positivity]
      hA1_D := fun _ _ => by simp
      hA2_S := fun y => by
        set x := c ^ (1 / 3 : ℝ) * σ_star
        have hx : 0 < x := mul_pos (Real.rpow_pos_of_pos (by dsimp [c]; norm_num) _) hσ0
        rw [norm_inv, show ((1 + (x : ℂ))⁻¹).re = (1 + x)⁻¹ by rw [show (1 + (x : ℂ))⁻¹ = (((1 + x)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re],
          one_mul]
        exact inv_anti₀ (by linarith) (by simpa using Complex.re_le_norm (1 + ((x : ℂ) + (y : ℂ) * Complex.I)))
      hA2_D := fun _ => by simp
      hΛ_add_half := fun h => by linarith }
  refine ⟨Δ₁, U, c, Δ, ξ, σ_star, (by dsimp [Δ₁]; norm_num), (by dsimp [U]; norm_num),
    (by rw [hU32]; dsimp [Δ₁, c]; norm_num), le_rfl, hΔ_hi, rfl, hσ0, hσ1, hσ_eq, amp, ?_⟩
  have hU34 : U ^ (-(3 / 4 : ℝ)) = 1 / 4096 := by
    dsimp [U]; rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num)]; norm_num
  have hΔ12 : Δ₁ ^ (-(1 / 2 : ℝ)) = 1 / 1000 := by
    dsimp [Δ₁]; rw [rpow_neg_half_eq_inv_sqrt (by norm_num), show (10 : ℝ) ^ 6 = (1000 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num), one_div]
  have hM43 : (3 / 1000 : ℝ) ≤ (4 * amp.M) ^ (-(4 / 3 : ℝ)) := by
    rw [show 4 * amp.M = (4 : ℝ) by dsimp [amp]; norm_num]
    have h2 : (4 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / 8 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 2, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith [Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) (by norm_num : -(3 / 2 : ℝ) ≤ -(4 / 3 : ℝ))]
  rw [hU34, hΔ12]; exact le_trans (max_le (by norm_num) (by norm_num)) (le_min le_rfl hM43)


/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CohnElkies.lobe_saddle_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.lobe_saddle_asymptotic

/-- info: 'FormalResearch.CohnElkies.lobeSaddleAmp_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.lobeSaddleAmp_nonvacuous

end FormalResearch.CohnElkies
