module

public import FormalResearch.SignUncertainty.CtScaleWindow
public import FormalResearch.SignUncertainty.HankelBootNodes
public import FormalResearch.SignUncertainty.HankelBootNumerics
public import FormalResearch.SignUncertainty.HankelBootArc
public import FormalResearch.SignUncertainty.CtDyadicEta
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.ArcBounds
public import FormalResearch.Asymptotics.StirlingHalfInt
public import FormalResearch.Special.AiryRatioBounds
public import FormalResearch.Special.AiryCftZeros

/-!
# Scale-`r` Hankel Good-Circle Quadrature and Arc Bound (`ct:dyadic` Part (1), Step 1b)

Splits `hankelBootNodes c f r ℓ k N` against `∫_{-r}^r Re(hankelBootShifted ...)` on any good
circle `r ∈ [r_min(c), R_J]` (`r_min(c) = 10⁸ (log c)²`) via `airy_defect_ball_split`,
bounding the covered arc by `virasoroArcCov_le` + `teb_stirling_bound` and the uncovered
wedge by `hankelPsi_envelope`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.Asymptotics
open FormalResearch.ModularBootstrap.ConcreteBootstrap
/-- Window half-width `δ₀(c, r) = 1200 π r^{-3/4} √(log c)` on the good circle `|u| = r`. -/
noncomputable def hankelScaleDelta (c r : ℝ) : ℝ :=
  1200 * π * r ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c)

private lemma deriv_airyAiC_ofReal (x : ℝ) :
    deriv airyAiC (x : ℂ) = (airyAi' x : ℂ) := by
  have hd_ai := (differentiable_airyAiC (x : ℂ)).hasDerivAt
  have hd_c : HasDerivAt (fun t : ℝ => airyAiC (t : ℂ)) (deriv airyAiC (x : ℂ)) x :=
    hd_ai.comp_ofReal
  have heq : (fun t : ℝ => airyAiC (t : ℂ)) = (fun t : ℝ => (airyAi t : ℂ)) :=
    funext airyAiC_ofReal
  rw [heq] at hd_c
  exact hd_c.unique (hasDerivAt_airyAi x).ofReal_comp

private lemma log_ge_32_of_1e14 {c : ℝ} (hc : 1e14 ≤ c) : 32 ≤ Real.log c := by
  have hc0 : 0 < c := by linarith
  have hexp1 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have hexp32 : Real.exp 32 ≤ c := by
    have h3 : Real.exp (32 : ℝ) = (Real.exp 1) ^ (32 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2.72 : ℝ) ^ (32 : ℕ) ≤ 1e14 := by norm_num
    calc Real.exp 32 = (Real.exp 1) ^ (32 : ℕ) := h3
      _ ≤ (2.72 : ℝ) ^ (32 : ℕ) := pow_le_pow_left₀ (Real.exp_pos 1).le hexp1 32
      _ ≤ 1e14 := h4
      _ ≤ c := hc
  exact (Real.le_log_iff_exp_le hc0).2 hexp32

private lemma scale_circleMap_mem_slitPlane {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo (-π) π) :
    circleMap 0 r θ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (circleMap 0 r θ).im = 0
  · left
    have hsin : Real.sin θ = 0 := by
      have : (circleMap 0 r θ).im = r * Real.sin θ := by simp [circleMap]
      nlinarith
    have hθ0 : θ = 0 := by
      rcases Real.sin_eq_zero_iff.1 hsin with ⟨k, hk⟩
      have hk0 : (k : ℝ) * π = θ := hk
      have hk_gt : (-1 : ℝ) < k := by nlinarith [hθ.1, Real.pi_pos]
      have hk_lt : (k : ℝ) < 1 := by nlinarith [hθ.2, Real.pi_pos]
      have hk_int : k = 0 := by
        have hk1 : -1 < k := by exact_mod_cast hk_gt
        have hk2 : k < 1 := by exact_mod_cast hk_lt
        omega
      subst hk_int; simp [← hk0]
    simp [hθ0, circleMap, hr]
  · exact Or.inr him

private lemma hankel_scale_delta_bounds {c r : ℝ} (hc : 1e14 ≤ c)
    (hr_log : 1e8 * (Real.log c) ^ 2 ≤ r) :
    0 < hankelScaleDelta c r ∧
      hankelScaleDelta c r ≤ 1 / 4 ∧
      hankelScaleDelta c r ≤ 40 * r ^ (-(1 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hlog32 : 32 ≤ Real.log c := log_ge_32_of_1e14 hc
  have hlog0 : 0 < Real.log c := by linarith
  have hsqrt_log_pos : 0 < Real.sqrt (Real.log c) := Real.sqrt_pos.2 hlog0
  have hr_pos : 0 < r := lt_of_lt_of_le (by positivity) hr_log
  have hpos : 0 < hankelScaleDelta c r := by
    unfold hankelScaleDelta; positivity
  -- `r^{1/4} ≥ 100 * √(log c)`
  have hr14_lb : 100 * Real.sqrt (Real.log c) ≤ r ^ (1 / 4 : ℝ) := by
    have h4 : (100 * Real.sqrt (Real.log c)) ^ 4 ≤ (r ^ (1 / 4 : ℝ)) ^ 4 := by
      have hsq : Real.sqrt (Real.log c) ^ 2 = Real.log c := Real.sq_sqrt hlog0.le
      have hr4 : (r ^ (1 / 4 : ℝ)) ^ 4 = r := by
        rw [← Real.rpow_natCast (r ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hr_pos.le]
        norm_num
      calc (100 * Real.sqrt (Real.log c)) ^ 4
          = 1e8 * (Real.sqrt (Real.log c) ^ 2) ^ 2 := by ring
        _ = 1e8 * (Real.log c) ^ 2 := by rw [hsq]
        _ ≤ r := hr_log
        _ = (r ^ (1 / 4 : ℝ)) ^ 4 := hr4.symm
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hr_pos.le _) h4
  have hr14_pos : 0 < r ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hr_pos _
  have hpi4 : 1200 * π ≤ 4000 := by linarith [Real.pi_lt_d2]
  have h_inv_split : r ^ (-(3 / 4 : ℝ)) = r ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hr_pos]; norm_num
  have h_r14_inv : r ^ (-(1 / 4 : ℝ)) * Real.sqrt (Real.log c) ≤ 1 / 100 := by
    rw [Real.rpow_neg hr_pos.le, inv_mul_le_iff₀ hr14_pos]
    linarith
  have hub40 : hankelScaleDelta c r ≤ 40 * r ^ (-(1 / 2 : ℝ)) := by
    unfold hankelScaleDelta
    rw [h_inv_split]
    have hr12_nn : 0 ≤ r ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hr_pos.le _
    calc 1200 * π * (r ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 4 : ℝ))) * Real.sqrt (Real.log c)
        = (1200 * π) * r ^ (-(1 / 2 : ℝ)) * (r ^ (-(1 / 4 : ℝ)) * Real.sqrt (Real.log c)) := by ring
      _ ≤ 4000 * r ^ (-(1 / 2 : ℝ)) * (1 / 100) := by
          gcongr
      _ = 40 * r ^ (-(1 / 2 : ℝ)) := by ring
  -- Also `r ≥ 1e8 * 32^2 ≥ 25600`, so `40 * r^{-1/2} ≤ 1/4`
  have hr_big : (25600 : ℝ) ≤ r := by
    have : 1e8 * (32 : ℝ) ^ 2 ≤ 1e8 * (Real.log c) ^ 2 := by gcongr
    linarith
  have hub_quarter : hankelScaleDelta c r ≤ 1 / 4 := by
    have hsq : (160 : ℝ) ≤ √r := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 160)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hr12_le : r ^ (-(1 / 2 : ℝ)) ≤ 1 / 160 := by
      rw [Real.rpow_neg hr_pos.le, ← Real.sqrt_eq_rpow]
      exact (inv_le_comm₀ (by positivity) (Real.sqrt_pos.2 hr_pos)).1 (by linarith)
    linarith
  exact ⟨hpos, hub_quarter, hub40⟩


private lemma hankel_scale_shifted_diff {c ε r ℓ : ℝ} {f : ℝ → ℝ} {k : ℕ}
    (hc0 : 0 < c) (hfe : IsHankelEigenfn c ε f) (hrA : r + 1 ≤ langerRadius c)
    (hℓ0 : 0 ≤ ℓ) (hℓh : ℓ ≤ 1 / 2) :
    DifferentiableOn ℂ (hankelBootShifted c f r ℓ k) (ball 0 (r + 1 / 3)) := by
  have h_an := analyticOnNhd_hankelPsi hc0 hfe
  intro u hu
  have hu' : ‖u‖ < r + 1 / 3 := by simpa [Metric.mem_ball, dist_zero_right] using hu
  have hmem : u + (ℓ : ℂ) ∈ closedBall (0 : ℂ) (c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4) := by
    rw [mem_closedBall_zero_iff]
    have hA : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := hankelBoot_langerRadius_eq c
    calc ‖u + (ℓ : ℂ)‖ ≤ ‖u‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
      _ = ‖u‖ + ℓ := by rw [Complex.norm_real, Real.norm_of_nonneg hℓ0]
      _ ≤ r + 1 := by linarith
      _ ≤ c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by rw [← hA]; exact hrA
  have h1 : DifferentiableAt ℂ (fun z : ℂ => hankelPsi c f (z + (ℓ : ℂ))) u :=
    DifferentiableAt.comp (g := hankelPsi c f) (f := fun z : ℂ => z + (ℓ : ℂ)) u
      ((h_an _ hmem).differentiableAt) ((differentiableAt_id.add (differentiableAt_const _)))
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (1 + z / (r : ℂ)) ^ (k + 1)) u :=
    ((differentiableAt_const _).add (differentiableAt_id.div_const _)).pow _
  exact (h1.mul h2).differentiableWithinAt

private lemma hankel_scale_cov_pt {c ε T u_T R_J r θ ℓ : ℝ} {f : ℝ → ℝ} {k : ℕ}
    (hc : 1e14 ≤ c) (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    (hmass : hankelMass c f = 1) (hT : c * hankelXi c u_T = T)
    (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hRJ_lb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R_J)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J) (hr_log : 1e8 * (Real.log c) ^ 2 ≤ r)
    (hℓ0 : 0 ≤ ℓ) (hℓh : ℓ ≤ 1 / 2) (hθ : θ ∈ Icc (-π) π) (h_abs_lt : |θ| < π)
    (hcov : |θ| ≤ π - hankelScaleDelta c r) :
    ‖hankelBootShifted c f r ℓ k (circleMap 0 r θ)‖ / airyEnv (circleMap 0 r θ) ≤
      (2 ^ (3 / 4 : ℝ) * ((π / 2) ^ (3 / 2 : ℝ) * hankelScaleWindowC * hankelScaleL c R_J r u_T f) *
        (√r) ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)) *
        ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) *
        Real.exp (-(4 * ℓ * √r / π) * ((π - |θ|) / 2)) := by
  have hc0 : 0 < c := by linarith
  have hr_pos : 0 < r := by linarith
  have ha_pos : 0 < √r := Real.sqrt_pos.2 hr_pos
  have ha_sq : √r ^ 2 = r := Real.sq_sqrt hr_pos.le
  have hθ_Ioo : θ ∈ Ioo (-π) π := abs_lt.1 h_abs_lt
  set u : ℂ := circleMap 0 r θ
  set w : ℂ := u + (ℓ : ℂ)
  have hnorm_u : ‖u‖ = r := by simp [u, norm_circleMap_zero, abs_of_pos hr_pos]
  have hw_slit : u ∈ Complex.slitPlane := scale_circleMap_mem_slitPlane hr_pos hθ_Ioo
  have hre_u : (u ^ (1 / 2 : ℂ)).re = √r * Real.cos (θ / 2) := re_cpow_half_circleMap hr_pos hθ_Ioo
  have hcos_bounds : (π - |θ|) / π ≤ Real.cos (θ / 2) ∧ Real.cos (θ / 2) ≤ (π - |θ|) / 2 := by
    have hcos_eq : Real.cos (θ / 2) = Real.sin ((π - |θ|) / 2) := by
      rw [← Real.cos_abs (θ / 2), abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2),
        ← Real.sin_pi_div_two_sub]
      congr 1; ring
    rw [hcos_eq]
    have hx0 : 0 ≤ (π - |θ|) / 2 := by linarith [h_abs_lt]
    have hxpi2 : (π - |θ|) / 2 ≤ π / 2 := by linarith [abs_nonneg θ]
    exact ⟨by calc (π - |θ|) / π = (2 / π) * ((π - |θ|) / 2) := by ring
      _ ≤ Real.sin ((π - |θ|) / 2) := Real.mul_le_sin hx0 hxpi2, Real.sin_le hx0⟩
  have hcos_pos : 0 < Real.cos (θ / 2) :=
    lt_of_lt_of_le (div_pos (by linarith [h_abs_lt]) Real.pi_pos) hcos_bounds.1
  -- Norm bounds on `w`
  have hw_lo : r - 1 ≤ ‖w‖ := by
    have hsub := norm_sub_le (u + (ℓ : ℂ)) (ℓ : ℂ)
    rw [add_sub_cancel_right, hnorm_u, Complex.norm_real, Real.norm_of_nonneg hℓ0] at hsub
    linarith
  have hw_lo_half : r / 2 ≤ ‖w‖ := by linarith
  have hw_hi : ‖w‖ ≤ r + 1 := by
    calc ‖w‖ ≤ ‖u‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
      _ = r + ℓ := by rw [hnorm_u, Complex.norm_real, Real.norm_of_nonneg hℓ0]
      _ ≤ r + 1 := by linarith
  have hw_pos : 0 < ‖w‖ := by linarith
  -- Parameter `θ_win` for `hankel_scale_cov_window`
  set δ₀ : ℝ := hankelScaleDelta c r
  have ⟨hδ_pos, _, _⟩ := hankel_scale_delta_bounds hc hr_log
  set θ_win : ℝ := 2 * δ₀ / (3 * π)
  have hθ_win_pos : 0 < θ_win := by positivity
  have hθr : 250 * Real.log c ≤ θ_win * r ^ (3 / 2 : ℝ) := by
    have hlog32 : 32 ≤ Real.log c := log_ge_32_of_1e14 hc
    have hlog0 : 0 < Real.log c := by linarith
    have hr34 : 1e6 * Real.sqrt (Real.log c) ^ 3 ≤ r ^ (3 / 4 : ℝ) := by
      have h_pow : (1e8 * (Real.log c) ^ 2) ^ (3 / 4 : ℝ) ≤ r ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hr_log (by norm_num)
      have h10 : (1e8 : ℝ) ^ (3 / 4 : ℝ) = 1e6 := by
        have h1 : (1e8 : ℝ) = (1e2 : ℝ) ^ (4 : ℕ) := by norm_num
        rw [h1, ← Real.rpow_natCast (1e2 : ℝ) 4, ← Real.rpow_mul (by norm_num)]
        norm_num
      have hpow_log : ((Real.log c) ^ (2 : ℕ)) ^ (3 / 4 : ℝ) = Real.sqrt (Real.log c) ^ 3 := by
        rw [← Real.rpow_natCast (Real.log c) 2, ← Real.rpow_mul hlog0.le,
          Real.sqrt_eq_rpow, ← Real.rpow_natCast (Real.log c ^ (1 / 2 : ℝ)) 3,
          ← Real.rpow_mul hlog0.le]
        norm_num
      rw [Real.mul_rpow (by norm_num) (by positivity), h10, hpow_log] at h_pow
      exact h_pow
    have hr_spl : r ^ (-(3 / 4 : ℝ)) * r ^ (3 / 2 : ℝ) = r ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hr_pos]; norm_num
    have hmul : θ_win * r ^ (3 / 2 : ℝ) = 800 * (r ^ (3 / 4 : ℝ) * Real.sqrt (Real.log c)) := by
      dsimp [θ_win, δ₀, hankelScaleDelta]
      calc 2 * (1200 * π * r ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c)) / (3 * π) * r ^ (3 / 2 : ℝ)
          = 800 * (π / π) * (r ^ (-(3 / 4 : ℝ)) * r ^ (3 / 2 : ℝ)) * Real.sqrt (Real.log c) := by ring
        _ = 800 * 1 * r ^ (3 / 4 : ℝ) * Real.sqrt (Real.log c) := by
            rw [div_self Real.pi_ne_zero, hr_spl]
        _ = 800 * (r ^ (3 / 4 : ℝ) * Real.sqrt (Real.log c)) := by ring
    rw [hmul]
    have hlog_sq : Real.sqrt (Real.log c) ^ 2 = Real.log c := Real.sq_sqrt hlog0.le
    have hsqrt_ge : 1 ≤ Real.sqrt (Real.log c) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
    have hsqrt4 : 1e6 * (Real.log c) ^ 2 ≤ r ^ (3 / 4 : ℝ) * Real.sqrt (Real.log c) := by
      calc 1e6 * (Real.log c) ^ 2 = 1e6 * (Real.sqrt (Real.log c) ^ 2) ^ 2 := by rw [hlog_sq]
        _ = (1e6 * Real.sqrt (Real.log c) ^ 3) * Real.sqrt (Real.log c) := by ring
        _ ≤ r ^ (3 / 4 : ℝ) * Real.sqrt (Real.log c) :=
            mul_le_mul_of_nonneg_right hr34 (Real.sqrt_nonneg _)
    have hlog_sq_le : Real.log c ≤ 1e6 * (Real.log c) ^ 2 := by
      have h1 : 1 ≤ 1e6 * Real.log c := by linarith
      calc Real.log c = 1 * Real.log c := (one_mul _).symm
        _ ≤ (1e6 * Real.log c) * Real.log c := mul_le_mul_of_nonneg_right h1 hlog0.le
        _ = 1e6 * (Real.log c) ^ 2 := by ring
    linarith only [hsqrt4, hlog_sq_le, hlog0]
  have hX_lb : θ_win * √‖w‖ ≤ (w ^ (1 / 2 : ℂ)).re := by
    have hsqrt_w : √‖w‖ ≤ (3 / 2 : ℝ) * √r := by
      have h1 : ‖w‖ ≤ (9 / 4 : ℝ) * r := by linarith
      calc √‖w‖ ≤ √((9 / 4 : ℝ) * r) := Real.sqrt_le_sqrt h1
        _ = √((3 / 2 : ℝ) ^ 2 * r) := by norm_num
        _ = (3 / 2 : ℝ) * √r := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    have hshift_re : (u ^ (1 / 2 : ℂ)).re ≤ (w ^ (1 / 2 : ℂ)).re :=
      (re_cpow_half_add_real_bounds hw_slit hℓ0).1
    have hcos_ge_δ : δ₀ / π ≤ Real.cos (θ / 2) := by
      have : δ₀ / π ≤ (π - |θ|) / π := div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
      exact this.trans hcos_bounds.1
    calc θ_win * √‖w‖ ≤ θ_win * ((3 / 2 : ℝ) * √r) := by gcongr
      _ = (δ₀ / π) * √r := by dsimp [θ_win]; ring
      _ ≤ Real.cos (θ / 2) * √r := by gcongr
      _ = (u ^ (1 / 2 : ℂ)).re := by rw [hre_u]; ring
      _ ≤ (w ^ (1 / 2 : ℂ)).re := hshift_re
  -- Apply `hankel_scale_cov_window`
  have hPsi := hankel_scale_cov_window hc hf hε hmass hT hu0 hu3 hRJ_lb hRJ_ub hr_lb hr_RJ
    hw_lo hw_hi hθ_win_pos hθr hX_lb
  -- Now translate shift & circle bounds
  have h_env_shift : airyEnv w ≤ airyEnv u * Real.exp (-(4 * ℓ * √r / π) * ((π - |θ|) / 2)) := by
    have h1 := (airyEnv_add_real_le u ℓ)
    have h2 : airySqrtRe u = √r * Real.cos (θ / 2) := hre_u
    rw [h2] at h1
    have h3 : -(4 * ℓ * √r / π) * ((π - |θ|) / 2) = -2 * ℓ * (√r * ((π - |θ|) / π)) := by
      field_simp [Real.pi_ne_zero]; ring
    have h4 : -2 * ℓ * (√r * Real.cos (θ / 2)) ≤ -2 * ℓ * (√r * ((π - |θ|) / π)) := by
      have hℓr : 0 ≤ 2 * ℓ * √r := by positivity
      linarith [mul_le_mul_of_nonneg_left hcos_bounds.1 hℓr]
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [h3, h4])) (airyEnv_pos u).le)
  have hpi_half_pos : 0 < (π - |θ|) / π := div_pos (by linarith [h_abs_lt]) Real.pi_pos
  have hwre_lb : √r * ((π - |θ|) / π) ≤ (w ^ (1 / 2 : ℂ)).re := by
    have := (re_cpow_half_add_real_bounds hw_slit hℓ0).1
    rw [hre_u] at this
    exact (mul_le_mul_of_nonneg_left hcos_bounds.1 ha_pos.le).trans this
  have hwre_pow : ((w ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) ≤
      (√r) ^ (-(3 / 2 : ℝ)) * (π / 2) ^ (3 / 2 : ℝ) * ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ)) := by
    have hle := Real.rpow_le_rpow_of_nonpos (mul_pos ha_pos hpi_half_pos) hwre_lb (by norm_num : -(3 / 2 : ℝ) ≤ 0)
    rw [Real.mul_rpow ha_pos.le hpi_half_pos.le] at hle
    have hfrac : (π - |θ|) / π = (2 / π) * ((π - |θ|) / 2) := by ring
    have hpi2 : (2 / π) ^ (-(3 / 2 : ℝ)) = (π / 2) ^ (3 / 2 : ℝ) := by
      rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
    rw [hfrac, Real.mul_rpow (by positivity) (by linarith [h_abs_lt]), hpi2] at hle
    calc ((w ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ))
        ≤ (√r) ^ (-(3 / 2 : ℝ)) * ((π / 2) ^ (3 / 2 : ℝ) * ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ))) := hle
      _ = (√r) ^ (-(3 / 2 : ℝ)) * (π / 2) ^ (3 / 2 : ℝ) * ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ)) := by ring
  have hwnorm_pow : ‖w‖ ^ (-(3 / 4 : ℝ)) ≤ 2 ^ (3 / 4 : ℝ) * (√r) ^ (-(3 / 2 : ℝ)) := by
    have hle := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < r / 2) hw_lo_half (by norm_num : -(3 / 4 : ℝ) ≤ 0)
    have hr2 : (r / 2) ^ (-(3 / 4 : ℝ)) = 2 ^ (3 / 4 : ℝ) * r ^ (-(3 / 4 : ℝ)) := by
      have h2inv : (2⁻¹ : ℝ) ^ (-(3 / 4 : ℝ)) = 2 ^ (3 / 4 : ℝ) := by
        rw [Real.rpow_neg (by norm_num), Real.inv_rpow (by norm_num), inv_inv]
      rw [div_eq_mul_inv, Real.mul_rpow hr_pos.le (by positivity), h2inv]
      ring
    have hr32 : r ^ (-(3 / 4 : ℝ)) = (√r) ^ (-(3 / 2 : ℝ)) := by
      rw [← ha_sq, ← Real.rpow_natCast √r 2, ← Real.rpow_mul ha_pos.le]
      norm_num
    rw [hr2, hr32] at hle
    exact hle
  have h1u_pow : ‖(1 + u / (r : ℂ)) ^ (k + 1)‖ ≤
      (2 : ℝ) ^ (k + 1) * ((π - |θ|) / 2) ^ ((k : ℝ) + 1) := by
    have h1w : ‖1 + u / (r : ℂ)‖ = 2 * Real.cos (θ / 2) := norm_one_add_circleMap_div hr_pos hθ
    rw [norm_pow, h1w]
    have hle : 2 * Real.cos (θ / 2) ≤ 2 * ((π - |θ|) / 2) := by linarith [hcos_bounds.2]
    have hp := pow_le_pow_left₀ (by linarith [hcos_pos]) hle (k + 1)
    have hcast : ((π - |θ|) / 2) ^ (k + 1) = ((π - |θ|) / 2) ^ ((k : ℝ) + 1) := by
      rw [← Real.rpow_natCast ((π - |θ|) / 2) (k + 1)]; push_cast; rfl
    calc (2 * Real.cos (θ / 2)) ^ (k + 1)
        ≤ (2 * ((π - |θ|) / 2)) ^ (k + 1) := hp
      _ = (2 : ℝ) ^ (k + 1) * ((π - |θ|) / 2) ^ (k + 1) := mul_pow _ _ _
      _ = (2 : ℝ) ^ (k + 1) * ((π - |θ|) / 2) ^ ((k : ℝ) + 1) := by rw [hcast]
  -- Combine all factors
  have hr_sqrt3 : (√r) ^ (-(3 / 2 : ℝ)) * (√r) ^ (-(3 / 2 : ℝ)) = (√r) ^ (-(3 : ℤ)) := by
    rw [← Real.rpow_add ha_pos, ← Real.rpow_intCast √r (-3)]
    norm_num
  have hhalf_pow : ((π - |θ|) / 2) ^ ((k : ℝ) + 1) * ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ)) =
      ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) := by
    have hp : 0 < (π - |θ|) / 2 := by linarith [h_abs_lt]
    rw [← Real.rpow_add hp]
    ring_nf
  have hRJ_A : R_J ≤ langerRadius c := by
    have h48 : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
      have hc12 : (1e12 : ℝ) ^ (2 / 3 : ℝ) ≤ c ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      have h1e8 : (1e12 : ℝ) ^ (2 / 3 : ℝ) = 1e8 := by
        have h1 : (1e12 : ℝ) = (1e4 : ℝ) ^ (3 : ℕ) := by norm_num
        rw [h1, ← Real.rpow_natCast (1e4 : ℝ) 3, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith
    have hrad := hankelBoot_radius_facts (by linarith) h48 hRJ_lb hRJ_ub
    linarith only [hrad.2.1]
  have hL_ge_1 : 1 ≤ hankelScaleL c R_J r u_T f :=
    hankelScaleL_ge_one (by linarith) hf hε hmass hT hu0 hu3 hr_lb hr_RJ hRJ_A
  have hL_nn : 0 ≤ hankelScaleWindowC * hankelScaleL c R_J r u_T f :=
    mul_nonneg hankelScaleWindowC_pos.le (by linarith)
  have hPsi_div : ‖hankelPsi c f w‖ / airyEnv u ≤
      (2 ^ (3 / 4 : ℝ) * ((π / 2) ^ (3 / 2 : ℝ) * hankelScaleWindowC * hankelScaleL c R_J r u_T f) *
        (√r) ^ (-(3 : ℤ))) * ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ)) *
        Real.exp (-(4 * ℓ * √r / π) * ((π - |θ|) / 2)) := by
    rw [div_le_iff₀ (airyEnv_pos u)]
    have hwre_nn : 0 ≤ ((w ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_nonneg (mul_pos ha_pos hpi_half_pos |>.le.trans hwre_lb) _
    have hstep1 : hankelScaleWindowC * hankelScaleL c R_J r u_T f * airyEnv w *
        ((w ^ (1 / 2 : ℂ)).re) ^ (-(3 / 2 : ℝ)) * ‖w‖ ^ (-(3 / 4 : ℝ)) ≤
        hankelScaleWindowC * hankelScaleL c R_J r u_T f *
          (airyEnv u * Real.exp (-(4 * ℓ * √r / π) * ((π - |θ|) / 2))) *
          ((√r) ^ (-(3 / 2 : ℝ)) * (π / 2) ^ (3 / 2 : ℝ) * ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ))) *
          (2 ^ (3 / 4 : ℝ) * (√r) ^ (-(3 / 2 : ℝ))) := by
      refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h_env_shift hL_nn) hwre_pow hwre_nn
        (mul_nonneg hL_nn (mul_nonneg (airyEnv_pos u).le (Real.exp_pos _).le))) hwnorm_pow
        (Real.rpow_nonneg hw_pos.le _)
        (mul_nonneg (mul_nonneg hL_nn (mul_nonneg (airyEnv_pos u).le (Real.exp_pos _).le)) (by positivity))
    refine hPsi.trans (hstep1.trans_eq ?_)
    calc hankelScaleWindowC * hankelScaleL c R_J r u_T f *
          (airyEnv u * Real.exp (-(4 * ℓ * √r / π) * ((π - |θ|) / 2))) *
          ((√r) ^ (-(3 / 2 : ℝ)) * (π / 2) ^ (3 / 2 : ℝ) * ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ))) *
          (2 ^ (3 / 4 : ℝ) * (√r) ^ (-(3 / 2 : ℝ)))
        = (2 ^ (3 / 4 : ℝ) * ((π / 2) ^ (3 / 2 : ℝ) * hankelScaleWindowC * hankelScaleL c R_J r u_T f) *
            ((√r) ^ (-(3 / 2 : ℝ)) * (√r) ^ (-(3 / 2 : ℝ)))) * ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ)) *
            Real.exp (-(4 * ℓ * √r / π) * ((π - |θ|) / 2)) * airyEnv u := by ring
      _ = _ := by rw [hr_sqrt3]
  have hp1 : 0 ≤ (√r) ^ (-(3 : ℤ)) := zpow_nonneg ha_pos.le _
  have hp3 : 0 ≤ ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith [h_abs_lt]) _
  have hcov_nn : 0 ≤ (2 ^ (3 / 4 : ℝ) * ((π / 2) ^ (3 / 2 : ℝ) * hankelScaleWindowC * hankelScaleL c R_J r u_T f) *
      (√r) ^ (-(3 : ℤ))) * ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-(4 * ℓ * √r / π) * ((π - |θ|) / 2)) :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) hankelScaleWindowC_pos.le)
              (by linarith only [hL_ge_1])))
          hp1)
        hp3)
      (Real.exp_pos _).le
  calc ‖hankelBootShifted c f r ℓ k u‖ / airyEnv u
      = (‖hankelPsi c f w‖ / airyEnv u) * ‖(1 + u / (r : ℂ)) ^ (k + 1)‖ := by
        unfold hankelBootShifted; rw [norm_mul, div_mul_eq_mul_div]
    _ ≤ ((2 ^ (3 / 4 : ℝ) * ((π / 2) ^ (3 / 2 : ℝ) * hankelScaleWindowC * hankelScaleL c R_J r u_T f) *
          (√r) ^ (-(3 : ℤ))) * ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(4 * ℓ * √r / π) * ((π - |θ|) / 2))) *
          ((2 : ℝ) ^ (k + 1) * ((π - |θ|) / 2) ^ ((k : ℝ) + 1)) :=
        mul_le_mul hPsi_div h1u_pow (norm_nonneg _) hcov_nn
    _ = (2 ^ (3 / 4 : ℝ) * ((π / 2) ^ (3 / 2 : ℝ) * hankelScaleWindowC * hankelScaleL c R_J r u_T f) *
          (√r) ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)) *
          (((π - |θ|) / 2) ^ ((k : ℝ) + 1) * ((π - |θ|) / 2) ^ (-(3 / 2 : ℝ))) *
          Real.exp (-(4 * ℓ * √r / π) * ((π - |θ|) / 2)) := by ring
    _ = _ := by rw [hhalf_pow]

private lemma hankel_scale_unc_pt {c ε r θ ℓ : ℝ} {f : ℝ → ℝ} {k : ℕ}
    (hc : 1e14 ≤ c) (hfe : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1)
    (hmass : hankelMass c f = 1) (hr_pos : 0 < r) (hrA : r + 1 ≤ langerRadius c)
    (hℓ0 : 0 ≤ ℓ) (hℓh : ℓ ≤ 1 / 2) (hδ_pos : 0 < hankelScaleDelta c r)
    (hθ : θ ∈ Icc (-π) π) (hunc : hankelScaleDelta c r ≤ π - |θ| → False) :
    ‖hankelBootShifted c f r ℓ k (circleMap 0 r θ)‖ / airyEnv (circleMap 0 r θ) ≤
      60 * √π * r ^ (-(1 / 4 : ℝ)) * (hankelScaleDelta c r) ^ ((k : ℝ) + 1 / 2) := by
  set u : ℂ := circleMap 0 r θ
  have hnorm_u : ‖u‖ = r := by simp [u, norm_circleMap_zero, abs_of_pos hr_pos]
  by_cases h_eq : |θ| = π
  · -- At `θ = ±π`, `(1 + u / r) ^ (k + 1) = 0`.
    have hcos_eq : Real.cos (θ / 2) = 0 := by
      have : |θ| = π := h_eq
      rcases abs_eq Real.pi_pos.le |>.1 this with rfl | hneg
      · norm_num [Real.cos_pi_div_two]
      · have hpi : θ = -π := by linarith
        rw [hpi, neg_div, Real.cos_neg, Real.cos_pi_div_two]
    have h1u : 1 + u / (r : ℂ) = 0 := by
      have hn : ‖1 + u / (r : ℂ)‖ = 0 := by
        rw [norm_one_add_circleMap_div hr_pos hθ, hcos_eq, mul_zero]
      exact norm_eq_zero.1 hn
    have hsh : hankelBootShifted c f r ℓ k u = 0 := by
      unfold hankelBootShifted
      rw [h1u, zero_pow (Nat.succ_ne_zero k), mul_zero]
    rw [hsh, norm_zero, zero_div]
    positivity
  · have h_abs_lt : |θ| < π := lt_of_le_of_ne (abs_le.2 ⟨hθ.1, hθ.2⟩) h_eq
    have hθ_Ioo : θ ∈ Ioo (-π) π := abs_lt.1 h_abs_lt
    have hw_slit : u ∈ Complex.slitPlane := scale_circleMap_mem_slitPlane hr_pos hθ_Ioo
    have h_u_slit : u + (ℓ : ℂ) ∈ Complex.slitPlane := not_nonpos_add_ofReal hw_slit hℓ0
    have h_cut : ¬((u + (ℓ : ℂ)).im = 0 ∧ (u + (ℓ : ℂ)).re ≤ 0) := by
      rw [Complex.mem_slitPlane_iff] at h_u_slit
      intro ⟨him, hre⟩
      rcases h_u_slit with h | h
      · linarith
      · exact h him
    have hwA : ‖u + (ℓ : ℂ)‖ ≤ c ^ (2 / 3 : ℝ) * langerKappa * 494e-6 := by
      have hA : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 494e-6 := hankelBoot_langerRadius_eq c
      calc ‖u + (ℓ : ℂ)‖ ≤ ‖u‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
        _ = r + ℓ := by rw [hnorm_u, Complex.norm_real, Real.norm_of_nonneg hℓ0]
        _ ≤ r + 1 := by linarith
        _ ≤ _ := by rw [← hA]; exact hrA
    have hPsi := hankelPsi_envelope (by linarith : 2 ≤ c) hfe hε hmass hwA h_cut
    have h_env_eq : ‖Complex.exp (-(4 / 3 : ℂ) * (u + (ℓ : ℂ)) ^ (3 / 2 : ℂ))‖ =
        airyEnv (u + (ℓ : ℂ)) := by
      rw [Complex.norm_exp]; unfold airyEnv
      congr 1
      simp [Complex.mul_re]
    have h_env_le : airyEnv (u + (ℓ : ℂ)) ≤ airyEnv u := by
      have h1 := airyEnv_add_real_le u ℓ
      have h2 : Real.exp (-2 * ℓ * airySqrtRe u) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [airySqrtRe_nonneg u])
      nlinarith [h1, h2, airyEnv_pos u]
    have hre_u : (u ^ (1 / 2 : ℂ)).re = √r * Real.cos (θ / 2) := re_cpow_half_circleMap hr_pos hθ_Ioo
    have hcos_bounds : (π - |θ|) / π ≤ Real.cos (θ / 2) ∧ Real.cos (θ / 2) ≤ (π - |θ|) / 2 := by
      have hcos_eq : Real.cos (θ / 2) = Real.sin ((π - |θ|) / 2) := by
        rw [← Real.cos_abs (θ / 2), abs_div, abs_of_pos (zero_lt_two : (0 : ℝ) < 2),
          ← Real.sin_pi_div_two_sub]
        congr 1; ring
      rw [hcos_eq]
      have hx0 : 0 ≤ (π - |θ|) / 2 := by linarith [h_abs_lt]
      have hxpi2 : (π - |θ|) / 2 ≤ π / 2 := by linarith [abs_nonneg θ]
      exact ⟨by calc (π - |θ|) / π = (2 / π) * ((π - |θ|) / 2) := by ring
        _ ≤ Real.sin ((π - |θ|) / 2) := Real.mul_le_sin hx0 hxpi2, Real.sin_le hx0⟩
    have h_gap_pos : 0 < π - |θ| := by linarith [h_abs_lt]
    have h_gap_lt : π - |θ| < hankelScaleDelta c r := lt_of_not_ge hunc
    have hbase_pos : 0 < √r * ((π - |θ|) / π) :=
      mul_pos (Real.sqrt_pos.2 hr_pos) (div_pos h_gap_pos Real.pi_pos)
    have hwre_lb : √r * ((π - |θ|) / π) ≤ ((u + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re := by
      have := (re_cpow_half_add_real_bounds hw_slit hℓ0).1
      rw [hre_u] at this
      exact (mul_le_mul_of_nonneg_left hcos_bounds.1 (Real.sqrt_nonneg _)).trans this
    have hwre_pow : ((u + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) ≤
        r ^ (-(1 / 4 : ℝ)) * √π * (π - |θ|) ^ (-(1 / 2 : ℝ)) := by
      have h1 := Real.rpow_le_rpow_of_nonpos hbase_pos hwre_lb (by norm_num : -(1 / 2 : ℝ) ≤ 0)
      have h_split : (√r * ((π - |θ|) / π)) ^ (-(1 / 2 : ℝ)) =
          r ^ (-(1 / 4 : ℝ)) * √π * (π - |θ|) ^ (-(1 / 2 : ℝ)) := by
        have hpi_inv : π ^ (-(1 / 2 : ℝ)) = (√π)⁻¹ := by
          rw [Real.rpow_neg Real.pi_pos.le, ← Real.sqrt_eq_rpow]
        have hr14 : (√r) ^ (-(1 / 2 : ℝ)) = r ^ (-(1 / 4 : ℝ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr_pos.le]; norm_num
        rw [Real.mul_rpow (Real.sqrt_nonneg _) (div_nonneg h_gap_pos.le Real.pi_pos.le),
          Real.div_rpow h_gap_pos.le Real.pi_pos.le, hpi_inv, hr14, div_inv_eq_mul]
        ring
      exact h1.trans_eq h_split
    have h1u_pow : ‖(1 + u / (r : ℂ)) ^ (k + 1)‖ ≤ (π - |θ|) ^ ((k : ℝ) + 1) := by
      rw [norm_pow, norm_one_add_circleMap_div hr_pos hθ]
      have hle : 2 * Real.cos (θ / 2) ≤ π - |θ| := by linarith [hcos_bounds.2]
      have hcos0 : 0 ≤ Real.cos (θ / 2) := (div_pos h_gap_pos Real.pi_pos).le.trans hcos_bounds.1
      have hp := pow_le_pow_left₀ (by linarith) hle (k + 1)
      have hcast : (π - |θ|) ^ (k + 1) = (π - |θ|) ^ ((k : ℝ) + 1) := by
        rw [← Real.rpow_natCast (π - |θ|) (k + 1)]; push_cast; rfl
      exact hp.trans_eq hcast
    have hΨ_div : ‖hankelPsi c f (u + (ℓ : ℂ))‖ / airyEnv u ≤
        60 * √π * r ^ (-(1 / 4 : ℝ)) * (π - |θ|) ^ (-(1 / 2 : ℝ)) := by
      rw [div_le_iff₀ (airyEnv_pos u)]
      rw [h_env_eq] at hPsi
      have hwre_nn : 0 ≤ ((u + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg (lt_of_lt_of_le hbase_pos hwre_lb).le _
      calc ‖hankelPsi c f (u + (ℓ : ℂ))‖
          ≤ 60 * airyEnv (u + (ℓ : ℂ)) * ((u + (ℓ : ℂ)) ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) := hPsi
        _ ≤ 60 * airyEnv u * (r ^ (-(1 / 4 : ℝ)) * √π * (π - |θ|) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h_env_le (by norm_num)) hwre_pow hwre_nn
              (mul_nonneg (by norm_num) (airyEnv_pos u).le)
        _ = 60 * √π * r ^ (-(1 / 4 : ℝ)) * (π - |θ|) ^ (-(1 / 2 : ℝ)) * airyEnv u := by ring
    have h_exp : (π - |θ|) ^ (-(1 / 2 : ℝ)) * (π - |θ|) ^ ((k : ℝ) + 1) =
        (π - |θ|) ^ ((k : ℝ) + 1 / 2) := by
      rw [← Real.rpow_add h_gap_pos]; ring_nf
    have h_mono_δ : (π - |θ|) ^ ((k : ℝ) + 1 / 2) ≤ (hankelScaleDelta c r) ^ ((k : ℝ) + 1 / 2) :=
      Real.rpow_le_rpow h_gap_pos.le h_gap_lt.le (by positivity)
    have hΨ_nn : 0 ≤ 60 * √π * r ^ (-(1 / 4 : ℝ)) * (π - |θ|) ^ (-(1 / 2 : ℝ)) := by positivity
    calc ‖hankelBootShifted c f r ℓ k u‖ / airyEnv u
        = (‖hankelPsi c f (u + (ℓ : ℂ))‖ / airyEnv u) * ‖(1 + u / (r : ℂ)) ^ (k + 1)‖ := by
          unfold hankelBootShifted; rw [norm_mul, div_mul_eq_mul_div]
      _ ≤ (60 * √π * r ^ (-(1 / 4 : ℝ)) * (π - |θ|) ^ (-(1 / 2 : ℝ))) *
            (π - |θ|) ^ ((k : ℝ) + 1) :=
          mul_le_mul hΨ_div h1u_pow (norm_nonneg _) hΨ_nn
      _ = 60 * √π * r ^ (-(1 / 4 : ℝ)) * ((π - |θ|) ^ (-(1 / 2 : ℝ)) * (π - |θ|) ^ ((k : ℝ) + 1)) := by ring
      _ = 60 * √π * r ^ (-(1 / 4 : ℝ)) * (π - |θ|) ^ ((k : ℝ) + 1 / 2) := by rw [h_exp]
      _ ≤ 60 * √π * r ^ (-(1 / 4 : ℝ)) * (hankelScaleDelta c r) ^ ((k : ℝ) + 1 / 2) :=
          mul_le_mul_of_nonneg_left h_mono_δ (by positivity)

private lemma intervalIntegral_unc_box {δ₀ M : ℝ} (hδ0 : 0 ≤ δ₀) (hδpi : δ₀ ≤ π) :
    IntervalIntegrable (fun θ : ℝ => if π - δ₀ < |θ| then M else 0) volume (-π) π ∧
      ∫ θ in (-π)..π, (if π - δ₀ < |θ| then M else 0) = 2 * δ₀ * M := by
  let g : ℝ → ℝ := fun θ => if π - δ₀ < |θ| then M else 0
  have hae_ne : ∀ a : ℝ, ∀ᵐ θ ∂volume, θ ≠ a := fun a =>
    ae_iff.2 (by simp [measure_singleton])
  have h1 : IntervalIntegrable g volume 0 (π - δ₀) := by
    refine (intervalIntegrable_const (c := (0 : ℝ))).congr ?_
    intro θ hθ
    rw [uIoc_of_le (by linarith)] at hθ
    simp only [g, abs_of_pos hθ.1, not_lt.2 hθ.2, ↓reduceIte]
  have h2 : IntervalIntegrable g volume (π - δ₀) π := by
    refine (intervalIntegrable_const (c := M)).congr ?_
    intro θ hθ
    rw [uIoc_of_le (by linarith)] at hθ
    have hθ_pos : 0 < θ := lt_of_le_of_lt (sub_nonneg.2 hδpi) hθ.1
    simp only [g, abs_of_pos hθ_pos, hθ.1, ↓reduceIte]
  have hn1 : IntervalIntegrable g volume (-π) (-(π - δ₀)) := by
    refine (intervalIntegrable_const (c := M)).congr_ae ?_
    filter_upwards [ae_restrict_of_ae (hae_ne (-(π - δ₀))),
      ae_restrict_mem measurableSet_Ioc] with θ hne hθ
    rw [uIoc_of_le (by linarith)] at hθ
    have hθ_nonpos : θ ≤ 0 := hθ.2.trans (neg_nonpos.2 (sub_nonneg.2 hδpi))
    have hlt : θ < -(π - δ₀) := lt_of_le_of_ne hθ.2 hne
    have hcond : π - δ₀ < |θ| := by rw [abs_of_nonpos hθ_nonpos]; linarith
    simp only [g, hcond, ↓reduceIte]
  have hn2 : IntervalIntegrable g volume (-(π - δ₀)) 0 := by
    refine (intervalIntegrable_const (c := (0 : ℝ))).congr ?_
    intro θ hθ
    rw [uIoc_of_le (by linarith)] at hθ
    have hnot : ¬ (π - δ₀ < |θ|) := by rw [abs_of_nonpos hθ.2]; linarith [hθ.1]
    simp only [g, hnot, ↓reduceIte]
  have h0_pi : IntervalIntegrable g volume 0 π := h1.trans h2
  have h_neg_pi_0 : IntervalIntegrable g volume (-π) 0 := hn1.trans hn2
  have hint_full : IntervalIntegrable g volume (-π) π := h_neg_pi_0.trans h0_pi
  have hint_0_pi : ∫ θ in (0 : ℝ)..π, g θ = δ₀ * M := by
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have i1 : ∫ θ in (0 : ℝ)..(π - δ₀), g θ = 0 := by
      have : ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (π - δ₀) → g θ = 0 :=
        Eventually.of_forall fun θ hθ => by
          rw [uIoc_of_le (by linarith)] at hθ
          simp only [g, abs_of_pos hθ.1, not_lt.2 hθ.2, ↓reduceIte]
      rw [intervalIntegral.integral_congr_ae this, intervalIntegral.integral_zero]
    have i2 : ∫ θ in (π - δ₀)..π, g θ = δ₀ * M := by
      have : ∀ᵐ θ ∂volume, θ ∈ Ι (π - δ₀) π → g θ = M :=
        Eventually.of_forall fun θ hθ => by
          rw [uIoc_of_le (by linarith)] at hθ
          have hθ_pos : 0 < θ := lt_of_le_of_lt (sub_nonneg.2 hδpi) hθ.1
          simp only [g, abs_of_pos hθ_pos, hθ.1, ↓reduceIte]
      rw [intervalIntegral.integral_congr_ae this, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [i1, i2, zero_add]
  have hint_neg_0 : ∫ θ in (-π)..(0 : ℝ), g θ = δ₀ * M := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hn1 hn2]
    have i1 : ∫ θ in (-π)..(-(π - δ₀)), g θ = δ₀ * M := by
      have : ∀ᵐ θ ∂volume, θ ∈ Ι (-π) (-(π - δ₀)) → g θ = M := by
        filter_upwards [hae_ne (-(π - δ₀))] with θ hne hθ
        rw [uIoc_of_le (by linarith)] at hθ
        have hθ_nonpos : θ ≤ 0 := hθ.2.trans (neg_nonpos.2 (sub_nonneg.2 hδpi))
        have hlt : θ < -(π - δ₀) := lt_of_le_of_ne hθ.2 hne
        have hcond : π - δ₀ < |θ| := by rw [abs_of_nonpos hθ_nonpos]; linarith
        simp only [g, hcond, ↓reduceIte]
      rw [intervalIntegral.integral_congr_ae this, intervalIntegral.integral_const, smul_eq_mul]
      ring
    have i2 : ∫ θ in (-(π - δ₀))..(0 : ℝ), g θ = 0 := by
      have : ∀ᵐ θ ∂volume, θ ∈ Ι (-(π - δ₀)) (0 : ℝ) → g θ = 0 :=
        Eventually.of_forall fun θ hθ => by
          rw [uIoc_of_le (by linarith)] at hθ
          have hnot : ¬ (π - δ₀ < |θ|) := by rw [abs_of_nonpos hθ.2]; linarith [hθ.1]
          simp only [g, hnot, ↓reduceIte]
      rw [intervalIntegral.integral_congr_ae this, intervalIntegral.integral_zero]
    rw [i1, i2, add_zero]
  have hint_full_eq : ∫ θ in (-π)..π, g θ = 2 * δ₀ * M := by
    rw [← intervalIntegral.integral_add_adjacent_intervals h_neg_pi_0 h0_pi, hint_neg_0, hint_0_pi]
    ring
  exact ⟨hint_full, hint_full_eq⟩

/-- **Scale-`r` good-circle quadrature and arc bound (`constant_terms_lower.tex`, `ct:dyadic` Step 1b).** -/
theorem hankel_scale_quad_arc {c ε T u_T R_J r ℓ : ℝ} {N : ℕ} {f : ℝ → ℝ} {k : ℕ}
    (hc : 1e14 ≤ c) (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    (hmass : hankelMass c f = 1) (hT : c * hankelXi c u_T = T)
    (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hRJ_lb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R_J)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J) (hr_log : 1e8 * (Real.log c) ^ 2 ≤ r)
    (hrA : r + 1 ≤ langerRadius c)
    (hℓ_eq : ℓ = (π / 2) * (k : ℝ) / √r) (hℓh : ℓ ≤ 1 / 2)
    (hk9 : 9 ≤ k)
    (hgood : ctGoodRadius r)
    (_hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < r))
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) r) :
    hankelBootNodes c f r ℓ k N ≤
      (∫ x in (-r)..r, (hankelBootShifted c f r ℓ k (x : ℂ)).re) +
        4 * virasoroArcCovConst * (π / 2) ^ (3 / 2 : ℝ) * hankelScaleWindowC *
          Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f * r ^ (-(1 / 2 : ℝ)) +
        1800 * π * 40 ^ (5 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr_pos : 0 < r := by linarith
  have ha_pos : 0 < √r := Real.sqrt_pos.2 hr_pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hℓ0 : 0 < ℓ := by rw [hℓ_eq]; positivity
  have ⟨hδ_pos, hδ_quarter, hδ40⟩ := hankel_scale_delta_bounds hc hr_log
  have hδ_le_pi : hankelScaleDelta c r ≤ π := by linarith [Real.two_le_pi]
  have hRp : ∀ w : ℂ, ‖w‖ = r → 0 ≤ w.im →
      ‖(airyBiC w - Complex.I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π :=
    fun w hw him => airy_Rplus_bound him (hw ▸ hgood w hw)
  have hRm : ∀ w : ℂ, ‖w‖ = r → w.im ≤ 0 →
      ‖(airyBiC w + Complex.I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π :=
    fun w hw him => airy_Rminus_bound him (hw ▸ hgood w hw)
  have hf_diff := hankel_scale_shifted_diff (k := k) hc0 hfe hrA hℓ0.le hℓh
  have hL_ge_1 : 1 ≤ hankelScaleL c R_J r u_T f := by
    have h48 : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
      have hc12 : (1e12 : ℝ) ^ (2 / 3 : ℝ) ≤ c ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      have h1e8 : (1e12 : ℝ) ^ (2 / 3 : ℝ) = 1e8 := by
        have h1 : (1e12 : ℝ) = (1e4 : ℝ) ^ (3 : ℕ) := by norm_num
        rw [h1, ← Real.rpow_natCast (1e4 : ℝ) 3, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith
    have hRJ_A : R_J ≤ langerRadius c := by
      have := (hankelBoot_radius_facts (by linarith) h48 hRJ_lb hRJ_ub).2.1
      linarith
    exact hankelScaleL_ge_one (by linarith) hf hε hmass hT hu0 hu3 hr_lb hr_RJ hRJ_A
  set L' : ℝ := (π / 2) ^ (3 / 2 : ℝ) * hankelScaleWindowC * hankelScaleL c R_J r u_T f
  have hL'_nn : 0 ≤ L' := by
    dsimp [L']
    exact mul_nonneg (mul_nonneg (by positivity) hankelScaleWindowC_pos.le) (by linarith [hL_ge_1])
  set B_cov : ℝ → ℝ := fun θ =>
    (2 ^ (3 / 4 : ℝ) * L' * (√r) ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)) *
      ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) *
      Real.exp (-(4 * ℓ * √r / π) * ((π - |θ|) / 2))
  set M_u : ℝ := 60 * √π * r ^ (-(1 / 4 : ℝ)) * (hankelScaleDelta c r) ^ ((k : ℝ) + 1 / 2)
  set B_unc : ℝ → ℝ := fun θ => if π - hankelScaleDelta c r < |θ| then M_u else 0
  have hB_cov_nn : ∀ θ : ℝ, θ ∈ Icc (-π) π → 0 ≤ B_cov θ := fun θ hθ => by
    have hp : 0 ≤ (π - |θ|) / 2 := by linarith [abs_le.2 hθ]
    dsimp [B_cov]; positivity
  have hB_unc_nn : ∀ θ : ℝ, 0 ≤ B_unc θ := fun θ => by
    dsimp [B_unc]; split_ifs <;> positivity
  have hB_cov_int : IntervalIntegrable B_cov volume (-π) π := by
    have hk_half_pos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by
      have : (9 : ℝ) ≤ k := by exact_mod_cast hk9
      linarith
    refine Continuous.intervalIntegrable ?_ _ _
    dsimp [B_cov]
    refine (continuous_const.mul ((Continuous.rpow_const
      ((continuous_const.sub continuous_abs).div_const 2) (fun _ => Or.inr hk_half_pos.le)))).mul
      (Real.continuous_exp.comp (continuous_const.mul ((continuous_const.sub continuous_abs).div_const 2)))
  have ⟨hB_unc_int, hB_unc_eq⟩ := intervalIntegral_unc_box (δ₀ := hankelScaleDelta c r) (M := M_u)
    hδ_pos.le hδ_le_pi
  have hB_int : IntervalIntegrable (fun θ => B_cov θ + B_unc θ) volume (-π) π :=
    hB_cov_int.add hB_unc_int
  have hB_bd : ∀ θ ∈ Icc (-π) π,
      ‖hankelBootShifted c f r ℓ k (circleMap 0 r θ)‖ / airyEnv (circleMap 0 r θ) ≤
        B_cov θ + B_unc θ := by
    intro θ hθ
    by_cases hcov : |θ| ≤ π - hankelScaleDelta c r
    · have h_abs_lt : |θ| < π := by linarith
      have h1 := hankel_scale_cov_pt hc hf hε hmass hT hu0 hu3 hRJ_lb hRJ_ub hr_lb hr_RJ
        hr_log hℓ0.le hℓh hθ h_abs_lt hcov (k := k)
      exact h1.trans (le_add_of_nonneg_right (hB_unc_nn θ))
    · have h_not : hankelScaleDelta c r ≤ π - |θ| → False := fun h => hcov (by linarith)
      have h1 := hankel_scale_unc_pt hc hfe hε hmass hr_pos hrA hℓ0.le hℓh hδ_pos hθ h_not (k := k)
      have h_eq_u : B_unc θ = M_u := by
        dsimp [B_unc]
        split_ifs with h
        · rfl
        · exact absurd (lt_of_not_ge hcov) h
      have h_unc_le : ‖hankelBootShifted c f r ℓ k (circleMap 0 r θ)‖ / airyEnv (circleMap 0 r θ) ≤
          B_unc θ :=
        h1.trans_eq h_eq_u.symm
      exact h_unc_le.trans (le_add_of_nonneg_left (hB_cov_nn θ hθ))
  have h_def := airy_defect_ball_split hD (by linarith : r < r + 1 / 3) hf_diff hRp hRm hB_int hB_bd
  -- Relate defect sum to `hankelBootNodes`
  have h_re_diff : hankelBootNodes c f r ℓ k N - ∫ x in (-r)..r, (hankelBootShifted c f r ℓ k (x : ℂ)).re ≤
      15 * √π * r * ∫ θ in (-π)..π, (B_cov θ + B_unc θ) := by
    have h_sum_re : hankelBootNodes c f r ℓ k N =
        (∑ n ∈ Finset.Icc 1 N,
          hankelBootShifted c f r ℓ k (airyZero n : ℂ) / deriv airyAiC (airyZero n : ℂ) ^ 2).re := by
      rw [Complex.re_sum]
      unfold hankelBootNodes
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [deriv_airyAiC_ofReal, ← Complex.ofReal_pow, Complex.div_ofReal_re]
    have h_int_cont : ContinuousOn (fun x : ℝ => hankelBootShifted c f r ℓ k (x : ℂ)) (Icc (-r) r) := by
      intro x hx
      have hdiff_sub : DifferentiableOn ℂ (hankelBootShifted c f r ℓ k) (Complex.ofReal '' Icc (-r) r) :=
        hf_diff.mono fun z hz => by
          rcases hz with ⟨t, ht, rfl⟩
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
          linarith [abs_le.2 ht]
      have hcont_sub := hdiff_sub.continuousOn
      exact (hcont_sub (x : ℂ) ⟨x, hx, rfl⟩).comp Complex.continuous_ofReal.continuousWithinAt
        fun t ht => ⟨t, ht, rfl⟩
    have h_int_re : ∫ x in (-r)..r, (hankelBootShifted c f r ℓ k (x : ℂ)).re =
        (∫ x in (-r)..r, hankelBootShifted c f r ℓ k (x : ℂ)).re := by
      have hi := h_int_cont.intervalIntegrable_of_Icc (μ := volume) (by linarith)
      simpa using Complex.reCLM.intervalIntegral_comp_comm hi
    have hre_norm : (∑ n ∈ Finset.Icc 1 N,
          hankelBootShifted c f r ℓ k (airyZero n : ℂ) / deriv airyAiC (airyZero n : ℂ) ^ 2 -
          ∫ x in (-r)..r, hankelBootShifted c f r ℓ k (x : ℂ)).re ≤
        ‖∑ n ∈ Finset.Icc 1 N,
          hankelBootShifted c f r ℓ k (airyZero n : ℂ) / deriv airyAiC (airyZero n : ℂ) ^ 2 -
          ∫ x in (-r)..r, hankelBootShifted c f r ℓ k (x : ℂ)‖ :=
      Complex.re_le_norm _
    rw [Complex.sub_re] at hre_norm
    rw [h_sum_re, h_int_re]
    exact hre_norm.trans h_def
  -- Split covered and uncovered integral bounds
  have h_cov_eq : 15 * √π * r * ∫ θ in (-π)..π, B_cov θ = virasoroArcCov c r 0 L' ℓ (fun _ => 0) k := by
    unfold virasoroArcCov; rfl
  have h_cov_bd : virasoroArcCov c r 0 L' ℓ (fun _ => 0) k ≤
      4 * virasoroArcCovConst * (π / 2) ^ (3 / 2 : ℝ) * hankelScaleWindowC *
        Real.exp (-(k : ℝ)) * hankelScaleL c R_J r u_T f * r ^ (-(1 / 2 : ℝ)) := by
    have h_arc := virasoroArcCov_le (c' := c) (T := 0) (by linarith : 10 ≤ r) hL'_nn hℓ0 (fun _ => 0)
      (by omega : 5 ≤ k)
    have h_st := teb_stirling_bound (k := k) (ℓ := ℓ) (a := √r) (by omega) hℓ0 ha_pos
      (by rw [hℓ_eq, div_mul_cancel₀ _ ha_pos.ne'])
    have h_pref_nn : 0 ≤ virasoroArcCovConst * L' * (√r)⁻¹ :=
      mul_nonneg (mul_nonneg virasoroArcCovConst_pos.le hL'_nn) (by positivity)
    have h1 : virasoroArcCov c r 0 L' ℓ (fun _ => 0) k ≤
        virasoroArcCovConst * L' * (√r)⁻¹ * (4 * Real.exp (-(k : ℝ))) :=
      h_arc.trans (mul_le_mul_of_nonneg_left h_st h_pref_nn)
    refine h1.trans_eq ?_
    have hr12 : (√r)⁻¹ = r ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hr_pos.le]
    rw [hr12]
    dsimp [L']
    ring
  have h_unc_bd : 15 * √π * r * ∫ θ in (-π)..π, B_unc θ ≤
      1800 * π * 40 ^ (5 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by
    rw [hB_unc_eq]
    set δ₀ := hankelScaleDelta c r
    have h_rew : 15 * √π * r * (2 * δ₀ * M_u) =
        1800 * π * r ^ (3 / 4 : ℝ) * δ₀ ^ ((k : ℝ) + 3 / 2) := by
      dsimp [M_u]
      have hsq_pi : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
      have hr34 : r * r ^ (-(1 / 4 : ℝ)) = r ^ (3 / 4 : ℝ) := by
        nth_rw 1 [← Real.rpow_one r]
        rw [← Real.rpow_add hr_pos]
        norm_num
      have hδk : δ₀ * δ₀ ^ ((k : ℝ) + 1 / 2) = δ₀ ^ ((k : ℝ) + 3 / 2) := by
        nth_rw 1 [← Real.rpow_one δ₀]
        rw [← Real.rpow_add hδ_pos]
        ring_nf
      calc 15 * √π * r * (2 * δ₀ * (60 * √π * r ^ (-(1 / 4 : ℝ)) * δ₀ ^ ((k : ℝ) + 1 / 2)))
          = 1800 * (√π * √π) * (r * r ^ (-(1 / 4 : ℝ))) * (δ₀ * δ₀ ^ ((k : ℝ) + 1 / 2)) := by ring
        _ = 1800 * π * r ^ (3 / 4 : ℝ) * δ₀ ^ ((k : ℝ) + 3 / 2) := by rw [hsq_pi, hr34, hδk]
    rw [h_rew]
    have hδ_split : δ₀ ^ ((k : ℝ) + 3 / 2) = δ₀ ^ (5 / 2 : ℝ) * δ₀ ^ ((k : ℝ) - 1) := by
      rw [← Real.rpow_add hδ_pos]; ring_nf
    have hδ52 : δ₀ ^ (5 / 2 : ℝ) ≤ 40 ^ (5 / 2 : ℝ) * r ^ (-(5 / 4 : ℝ)) := by
      have h1 := Real.rpow_le_rpow hδ_pos.le hδ40 (by norm_num : (0 : ℝ) ≤ 5 / 2)
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hr_pos.le _), ← Real.rpow_mul hr_pos.le] at h1
      norm_num at h1 ⊢
      exact h1
    have hδkm1 : δ₀ ^ ((k : ℝ) - 1) ≤ 1 := by
      have hk1 : 0 ≤ (k : ℝ) - 1 := by
        have : (9 : ℝ) ≤ k := by exact_mod_cast hk9
        linarith
      exact Real.rpow_le_one hδ_pos.le (by linarith) hk1
    have hr_comb : r ^ (3 / 4 : ℝ) * r ^ (-(5 / 4 : ℝ)) = r ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hr_pos]; norm_num
    have h_step : 1800 * π * r ^ (3 / 4 : ℝ) * (δ₀ ^ (5 / 2 : ℝ) * δ₀ ^ ((k : ℝ) - 1)) ≤
        1800 * π * r ^ (3 / 4 : ℝ) * (40 ^ (5 / 2 : ℝ) * r ^ (-(5 / 4 : ℝ)) * 1) := by
      gcongr
    rw [hδ_split]
    refine h_step.trans_eq ?_
    calc 1800 * π * r ^ (3 / 4 : ℝ) * (40 ^ (5 / 2 : ℝ) * r ^ (-(5 / 4 : ℝ)) * 1)
        = 1800 * π * 40 ^ (5 / 2 : ℝ) * (r ^ (3 / 4 : ℝ) * r ^ (-(5 / 4 : ℝ))) := by ring
      _ = 1800 * π * 40 ^ (5 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by rw [hr_comb]
  have hint_sum : ∫ θ in (-π)..π, (B_cov θ + B_unc θ) =
      (∫ θ in (-π)..π, B_cov θ) + ∫ θ in (-π)..π, B_unc θ :=
    intervalIntegral.integral_add hB_cov_int hB_unc_int
  rw [hint_sum, mul_add, h_cov_eq] at h_re_diff
  linarith [h_re_diff, h_cov_bd, h_unc_bd]


/-- info: 'FormalResearch.SignUncertainty.hankel_scale_quad_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankel_scale_quad_arc

end FormalResearch.SignUncertainty
