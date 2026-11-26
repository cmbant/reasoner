module

public import FormalResearch.SignUncertainty.FctCuspEdgeSmall

/-!
# `fct:cusp-edge` large-`L` outer regime (`1 ≤ L`, `S ≥ 16`)
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty.FctCuspEdge

open FormalResearch.SignUncertainty
open FormalResearch.Analysis
open FormalResearch.CohnElkies

/-! ### Regime B: positive outer half-line for `1 ≤ L` and `S ≥ 16` -/

set_option maxHeartbeats 1200000 in
theorem cusp_outer_pos_large {α η C_A C_Y : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hη : 0 < η)
    (hCA : 0 ≤ C_A) (hCY : 0 ≤ C_Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c L : ℝ), 1 ≤ c → 1 ≤ L → 16 ≤ c ^ ((2 : ℝ) / 3) * L →
      ∀ (A Y Y₀ R : ℝ → ℂ), CuspAmplitude η C_A A → CuspProfile α C_Y Y Y₀ R →
        ‖∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) *
          (((1 - chi0 u : ℝ) : ℂ) * A (c ^ (-(1 : ℝ) / 3) * u) * Y u)‖ ≤
          C * (c ^ ((2 : ℝ) / 3) * L) ^ (-α - 1) := by
  obtain ⟨Bχ, hBχ1, hBχ⟩ := chi0_deriv_bound
  obtain ⟨Bρ, hBρ1, hBρ⟩ := rhoSaddle_deriv_bound
  obtain ⟨Bin, hBin1, hBin⟩ := rhoInner_deriv_bound
  obtain ⟨C2, hC2_nn, hC2⟩ := edgePhi_iteratedDeriv_bound 2 (by norm_num)
  obtain ⟨C3, hC3_nn, hC3⟩ := edgePhi_iteratedDeriv_bound 3 (by norm_num)
  obtain ⟨C4, hC4_nn, hC4⟩ := edgePhi_iteratedDeriv_bound 4 (by norm_num)
  set q := 2 * α + 3 / 2
  set M₀ := 64 * (2 * Bχ) * (6 * max 1 ((2 / η) ^ 3) * C_A) * C_Y
  set K_in := max 1 (max (π ^ 2 / 3) (max (2 * C2) (max (2 * C3) (2 * C4))))
  set C_in := (104 * K_in ^ 3) ^ 3 * 8 * (8 * (2 * Bin) * M₀) * (2 ^ (q + 2) / (q + 2))
  -- Constants for outer part in `τ`
  set M_tau := 8 * (8 * (2 * 1000 * Bin) * (2 * 25 ^ 3 * Bχ)) * (8 * C_A * (C_Y * 20 ^ (q + 3)))
  set K_tau := max 1 (max (32 * C2) (max (32 * C3) (32 * C4)))
  obtain ⟨C_abs_t, hC_abs_t0, hC_abs_t⟩ := rpow_mul_exp_neg_bdd (κ := η / 4) (p := 3 / 2) (by positivity) (by norm_num)
  obtain ⟨C_abs_t1, hC_abs_t10, hC_abs_t1⟩ := rpow_mul_exp_neg_bdd (κ := η / 4) (p := 1 / 2) (by positivity) (by norm_num)
  obtain ⟨C_exp_sad, hC_exp_sad0, hC_exp_sad⟩ :=
    exp_neg_exp_half_le_rpow (κ := η / (4 * π)) (p := α + 1) (by positivity) (by linarith)
  obtain ⟨C_exp_tail, hC_exp_tail0, hC_exp_tail⟩ :=
    exp_neg_exp_half_le_rpow (κ := η / (8 * π)) (p := α + 1) (by positivity) (by linarith)
  set C_sadL := 8 * (Bρ * M_tau * C_abs_t1 + 4 * 8 * Bρ * M_tau * C_abs_t) * Real.sqrt 10 * C_exp_sad
  set C_tailL := 2 * ((104 * K_tau ^ 3) ^ 3 * 32 ^ 3 * (8 * (2 * 8 * Bρ) * M_tau) * (1 / η) * C_exp_tail)
  refine ⟨C_in + C_sadL + C_tailL, by positivity, fun c L hc hL hS A Y Y₀ R hA hY => ?_⟩
  have hc0 : 0 < c := by linarith
  have hL0 : 0 < L := by linarith
  set ς : ℝ := c ^ (-(1 : ℝ) / 3)
  set S : ℝ := c ^ ((2 : ℝ) / 3) * L
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  have hς_le : ς ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num)
  have hS_pos : 0 < S := by linarith
  have hS_ge1 : 1 ≤ S := by linarith
  have hς_inv : ς⁻¹ = c ^ ((1 : ℝ) / 3) := by
    dsimp [ς]; rw [← Real.rpow_neg hc0.le]; congr 1; ring
  -- Saddle `t = tau0 L` and inner cutoff scale `t_* = exp(L/2) / (4π)`
  obtain ⟨ht_lo, ht_hi⟩ := tau0_large_bounds hL
  set t : ℝ := tau0 L
  set tstar : ℝ := Real.exp (L / 2) / (4 * π)
  have ht0 : 0 < t := tau0_pos hL0
  have htstar_pos : 0 < tstar := by positivity
  have htstar_ge : (1 / 10 : ℝ) ≤ tstar := by
    dsimp [tstar]
    have h1 : (3 / 2 : ℝ) ≤ Real.exp (L / 2) := by linarith [Real.add_one_le_exp (L / 2)]
    have h2 : 4 * π < 13 := by nlinarith [Real.pi_lt_d2]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have ht_ge_half : (1 / 2 : ℝ) ≤ t := by
    have hexp : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    have hpi : π < 4 := lt_trans Real.pi_lt_d2 (by norm_num)
    have : 2 / 4 ≤ Real.exp L / π := div_le_div₀ (by positivity) hexp Real.pi_pos hpi.le
    linarith
  have htstar_lt : tstar < t / 4 := by
    have h1 : Real.exp (L / 2) < Real.exp L := Real.exp_lt_exp.mpr (by linarith)
    have h2 : tstar < Real.exp L / (4 * π) := div_lt_div_of_pos_right h1 (by positivity)
    have h3 : Real.exp L / (4 * π) ≤ t / 4 := by
      have := div_le_div_of_nonneg_right ht_lo (by norm_num : (0 : ℝ) ≤ 4)
      rwa [div_div, mul_comm π 4] at this
    linarith
  have hm_tstar : hankelEdgeM tstar ≤ L / 2 := by
    rcases le_or_gt tstar (1 / 2) with hle | hgt
    · have h1 := hankelEdgeM_le_sq tstar
      have hpi : π ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      nlinarith
    · have h1 := hankelEdgeM_le_log hgt.le
      have h2 : π * tstar = Real.exp (L / 2) / 4 := by dsimp [tstar]; field_simp [Real.pi_pos.ne']
      rw [h2, Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h1
      have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
      linarith
  let g : ℝ → ℂ := fun u => ((1 - chi0 u : ℝ) : ℂ) * A (ς * u) * Y u
  have hg_cd : ContDiffOn ℝ 3 g (Ioi 0) :=
    (((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub contDiff_chi0)).of_le (by simp)).contDiffOn.mul
      ((hA.contDiff.comp ((contDiff_const.mul contDiff_id).of_le le_top)).contDiffOn)).mul
      (hY.contDiffOn_Y.mono fun u (hu : 0 < u) => hu.ne')
  have hg_zero : ∀ u : ℝ, 0 < u → u ≤ 1 → g u = 0 := fun u hu hu1 => by
    simp [g, chi0_eq_one (by rw [abs_of_pos hu]; exact hu1)]
  have hg_bd : ∀ u : ℝ, 1 ≤ u → ∀ j ≤ 3, ‖iteratedDeriv j g u‖ ≤ M₀ * u ^ (-q) * u ^ (-(j : ℤ)) := by
    intro u hu j hj
    have h := outer_amp_deriv_bound hα0 hη hCA hCY hBχ1 hBχ hc hA hY hu j hj
    have hexp : Real.exp (-(η / 2) * ς * u) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ (η / 2) * ς * u := by positivity
      linarith
    calc ‖iteratedDeriv j g u‖ ≤ M₀ * (u ^ (-q) * Real.exp (-(η / 2) * ς * u)) * u ^ (-(j : ℤ)) := h
      _ ≤ M₀ * (u ^ (-q) * 1) * u ^ (-(j : ℤ)) := by gcongr
      _ = M₀ * u ^ (-q) * u ^ (-(j : ℤ)) := by ring
  let g_in : ℝ → ℂ := fun u => (rhoInner (ς * u / tstar) : ℂ) * g u
  let g_out : ℝ → ℂ := fun u => ((1 - rhoInner (ς * u / tstar) : ℝ) : ℂ) * g u
  have hg_int_Ioi : ∀ (w : ℝ → ℝ), Continuous w → (∀ u, |w u| ≤ 1) →
      IntegrableOn (fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * ((w u : ℂ) * g u)) (Ioi 0) := by
    intro w hw hw1
    have hcont : ContinuousOn (fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * ((w u : ℂ) * g u)) (Ioi 0) :=
      ((Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (contDiff_scaledPsi c L).continuous))).continuousOn).mul
        ((Complex.continuous_ofReal.comp hw).continuousOn.mul hg_cd.continuousOn)
    have hdom_int : IntegrableOn (fun u : ℝ => if u ≤ 1 then (0 : ℝ) else M₀ * u ^ (-q)) (Ioi 0) := by
      have h1 : IntegrableOn (fun u : ℝ => M₀ * u ^ (-q)) (Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt (show -q < -1 by dsimp [q]; linarith) zero_lt_one).const_mul M₀
      have h2 : IntegrableOn (fun u : ℝ => (Ioi (1 : ℝ)).indicator (fun x => M₀ * x ^ (-q)) u) (Ioi 0) :=
        (h1.integrable_indicator measurableSet_Ioi).integrableOn
      refine h2.congr_fun (fun u _ => ?_) measurableSet_Ioi
      by_cases hu : u ≤ 1
      · simp [hu]
      · push Not at hu
        simp [not_le.mpr hu, Set.indicator_of_mem (show u ∈ Ioi (1 : ℝ) from hu)]
    refine hdom_int.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hu1 : u ≤ 1
    · rw [ite_eq_left_iff.mpr fun h => absurd hu1 h, hg_zero u hu hu1, norm_zero, mul_zero]
    · push Not at hu1
      rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hu1))]
      have h0 := hg_bd u hu1.le 0 (by omega)
      simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at h0
      calc |w u| * ‖g u‖ ≤ 1 * (M₀ * u ^ (-q)) := mul_le_mul (hw1 u) h0 (norm_nonneg _) zero_le_one
        _ = M₀ * u ^ (-q) := one_mul _
  have hint_in := hg_int_Ioi (fun u => rhoInner (ς * u / tstar))
    (contDiff_rhoInner.continuous.comp ((continuous_const.mul continuous_id).div_const tstar))
    (fun u => by rw [abs_of_nonneg (rhoInner_nonneg _)]; exact rhoInner_le_one _)
  have hint_out := hg_int_Ioi (fun u => 1 - rhoInner (ς * u / tstar))
    (continuous_const.sub (contDiff_rhoInner.continuous.comp ((continuous_const.mul continuous_id).div_const tstar)))
    (fun u => by rw [abs_of_nonneg (by linarith [rhoInner_le_one (ς * u / tstar)])]; linarith [rhoInner_nonneg (ς * u / tstar)])
  have hsplit_pt : ∀ u : ℝ, Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g u =
      Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_in u +
      Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_out u := fun u => by
    dsimp [g_in, g_out]; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hsplit_pt u),
    integral_add hint_in hint_out]
  -- (1) Inner part `g_in` (`ς u ≤ tstar`) via `ibp3_interval`
  have hIn : ‖∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_in u‖ ≤
      C_in * S ^ (-α - 1) := by
    set ustar : ℝ := tstar / ς
    have hustar_pos : 0 < ustar := by positivity
    rcases le_or_gt ustar 1 with hu_le1 | hu_gt1
    · have hzero_all : ∀ u ∈ Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_in u = 0 := by
        intro u hu
        rcases le_or_gt u 1 with h1 | h1
        · simp [g_in, hg_zero u hu h1]
        · have hge1 : 1 ≤ |ς * u / tstar| := by
            rw [abs_of_pos (by positivity), one_le_div htstar_pos]
            have : tstar ≤ ς := by dsimp [ustar] at hu_le1; rwa [div_le_one hς_pos] at hu_le1
            nlinarith
          simp [g_in, rhoInner_eq_zero hge1]
      rw [setIntegral_eq_zero_of_forall_eq_zero hzero_all, norm_zero]
      positivity
    · -- `1 < ustar`: `g_in` supported on `[1, ustar] ⊂ [1/2, ustar]`
      have heq_int : ∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_in u =
          ∫ u in (1 / 2 : ℝ)..ustar, Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_in u := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (s := Ioc (1 / 2) ustar) (t := Ioi 0)
          (f := fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_in u)
          measurableSet_Ioi.nullMeasurableSet
          (fun u hu => mem_Ioi.mpr (by linarith [hu.1]))
          (Filter.Eventually.of_forall fun u hu => by
            have hu_pos : 0 < u := hu.1
            have hnot : u ≤ 1 / 2 ∨ ustar < u := by
              have := hu.2; rw [mem_Ioc] at this; push Not at this
              rcases le_or_gt u (1 / 2) with h | h
              · exact Or.inl h
              · exact Or.inr (this h)
            rcases hnot with h1 | h1
            · rw [show g_in u = 0 by simp [g_in, hg_zero u hu_pos (by linarith)], mul_zero]
            · have hge1 : 1 ≤ |ς * u / tstar| := by
                rw [abs_of_pos (by positivity), one_le_div htstar_pos]
                have : tstar < u * ς := by dsimp [ustar] at h1; rwa [div_lt_iff₀ hς_pos] at h1
                linarith
              rw [show g_in u = 0 by simp [g_in, rhoInner_eq_zero hge1], mul_zero])
      rw [heq_int]
      have hg_in_cd : ContDiffOn ℝ 3 g_in (Ioi 0) :=
        ((Complex.ofRealCLM.contDiff.comp (contDiff_rhoInner.comp
          ((contDiff_const.mul contDiff_id).div_const tstar))).of_le (by simp)).contDiffOn.mul hg_cd
      have hvan_a : ∀ j ≤ 2, iteratedDeriv j g_in (1 / 2) = 0 := by
        intro j _
        have hev : g_in =ᶠ[𝓝 (1 / 2 : ℝ)] 0 := by
          filter_upwards [(isOpen_Ioo (a := (0 : ℝ)) (b := 1)).mem_nhds (by norm_num)] with y hy
          simp [g_in, hg_zero y hy.1 hy.2.le]
        rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero]
      have hvan_b : ∀ j ≤ 2, iteratedDeriv j g_in ustar = 0 :=
        iteratedDeriv_eq_zero_of_eq_zero_on_Ioo isOpen_Ioi hg_in_cd
          (a := ustar) (b := ustar + 1) (by linarith) ⟨le_rfl, by linarith⟩ hustar_pos
          (fun y hy => by
            have hy0 : 0 < y := hustar_pos.trans hy.1
            have hge1 : 1 ≤ |ς * y / tstar| := by
              rw [abs_of_pos (by positivity), one_le_div htstar_pos]
              have : tstar < y * ς := by
                have := hy.1; dsimp [ustar] at this; rwa [div_lt_iff₀ hς_pos] at this
              linarith
            simp [g_in, rhoInner_eq_zero hge1])
      have hU_in : IsOpen (Ioo (0 : ℝ) (2 * ustar)) := isOpen_Ioo
      have hne_in : ∀ x ∈ Ioo (0 : ℝ) (2 * ustar), deriv (scaledPsi c L) x ≠ 0 := by
        intro x hx
        have hx0 : 0 < x := hx.1
        rw [deriv_scaledPsi hc0, edgePhiDeriv_eq_sub_m]
        have hςx_lt : ς * x < t := by
          have h1 : ς * x < ς * (2 * ustar) := mul_lt_mul_of_pos_left hx.2 hς_pos
          have h2 : ς * (2 * ustar) = 2 * tstar := by dsimp [ustar]; field_simp [hς_pos.ne']
          linarith
        have hm_lt : hankelEdgeM (ς * x) < L := by
          rw [← ceEll_tau0 hL0]
          exact hankelEdgeM_strictMonoOn (mul_nonneg hς_pos.le hx0.le) ht0.le hςx_lt
        exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos hc0 _) (sub_pos.mpr hm_lt))
      have hψ_in : ∀ x ∈ Icc (1 / 2 : ℝ) ustar,
          S / 2 ≤ |deriv (scaledPsi c L) x| ∧
          ∀ j ∈ ({1, 2, 3} : Finset ℕ),
            |iteratedDeriv (j + 1) (scaledPsi c L) x| ≤ K_in * x ^ (-(j : ℤ)) * |deriv (scaledPsi c L) x| := by
        intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have hςx_le : ς * x ≤ tstar := by
          have := mul_le_mul_of_nonneg_left hx.2 hς_pos.le
          rwa [show ς * ustar = tstar by dsimp [ustar]; field_simp [hς_pos.ne']] at this
        have hψ1 : S / 2 ≤ deriv (scaledPsi c L) x := by
          rw [deriv_scaledPsi hc0, edgePhiDeriv_eq_sub_m]
          have hm_le : hankelEdgeM (ς * x) ≤ L / 2 :=
            (hankelEdgeM_strictMonoOn.monotoneOn (mul_nonneg hς_pos.le hx0.le) htstar_pos.le hςx_le).trans hm_tstar
          have := mul_le_mul_of_nonneg_left (show L / 2 ≤ L - hankelEdgeM (ς * x) by linarith)
            (Real.rpow_nonneg hc0.le ((2 : ℝ) / 3))
          dsimp [S, ς] at this ⊢; linarith
        have habs1 : S / 2 ≤ |deriv (scaledPsi c L) x| := by rw [abs_of_pos (by linarith)]; exact hψ1
        have hc23_le : c ^ ((2 : ℝ) / 3) / 2 ≤ |deriv (scaledPsi c L) x| := by
          have : c ^ ((2 : ℝ) / 3) ≤ S := by
            dsimp [S]; exact le_mul_of_one_le_right (Real.rpow_nonneg hc0.le _) hL
          linarith
        refine ⟨habs1, fun j hj => ?_⟩
        rw [iteratedDeriv_scaledPsi hc0]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases le_or_gt (ς * x) 1 with hle1 | hgt1
        · -- `ς * x ≤ 1`: `|ψ^{(j+1)}| ≤ C * ς^{j-2} ≤ C * (ς x)^j * c^{2/3} x^{-j}`?
          -- Even simpler: `ς * x ≤ 1` implies `c^{2/3} x^{-j} = ς^{-2} x^{-j} ≥ ς^{j-2}`!
          have hcs2 : c ^ ((2 : ℝ) / 3) * ς ^ 2 = 1 := by
            dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
          rcases hj with rfl | rfl | rfl
          · rw [edgePhi_iteratedDeriv_ge_two L 2 le_rfl, show (2 - 2 : ℕ) = 0 by rfl, iteratedDeriv_zero,
              abs_mul, abs_of_nonneg (by positivity)]
            have hςx_pos : 0 < ς * x := mul_pos hς_pos hx0
            have h2 : |edgePhiDeriv2 (ς * x)| ≤ π ^ 2 / 6 * (ς * x) := by
              have := (edgePhiDeriv2_abs_le hςx_pos.ne').trans (min_le_left _ _)
              simpa only [abs_of_pos hςx_pos] using this
            have hc1 : c * ς ^ 2 * ς = 1 := by
              dsimp [ς]; rw [mul_assoc, ← pow_succ, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le,
                show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
            have hbd : c * ς ^ 2 * |edgePhiDeriv2 (ς * x)| ≤ π ^ 2 / 6 * x := by
              calc c * ς ^ 2 * |edgePhiDeriv2 (ς * x)| ≤ c * ς ^ 2 * (π ^ 2 / 6 * (ς * x)) :=
                    mul_le_mul_of_nonneg_left h2 (by positivity)
                _ = (c * ς ^ 2 * ς) * (π ^ 2 / 6 * x) := by ring
                _ = π ^ 2 / 6 * x := by rw [hc1, one_mul]
            have hx_le : x ≤ c ^ ((2 : ℝ) / 3) * x ^ (-1 : ℤ) := by
              rw [zpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hx0]
              have hsq : ς ^ 2 * x ^ 2 ≤ 1 := by rw [← mul_pow]; exact pow_le_one₀ (by positivity) hle1
              have := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hc0.le ((2 : ℝ) / 3))
              calc x * x = (c ^ ((2 : ℝ) / 3) * ς ^ 2) * x ^ 2 := by rw [hcs2, one_mul, _root_.sq]
                _ = c ^ ((2 : ℝ) / 3) * (ς ^ 2 * x ^ 2) := by ring
                _ ≤ c ^ ((2 : ℝ) / 3) * 1 := this
                _ = c ^ ((2 : ℝ) / 3) := mul_one _
            have hK : π ^ 2 / 3 ≤ K_in := le_trans (le_max_left _ _) (le_max_right _ _)
            calc c * ς ^ 2 * |edgePhiDeriv2 (ς * x)| ≤ π ^ 2 / 6 * x := hbd
              _ ≤ π ^ 2 / 6 * (c ^ ((2 : ℝ) / 3) * x ^ (-1 : ℤ)) := mul_le_mul_of_nonneg_left hx_le (by positivity)
              _ = (π ^ 2 / 3) * x ^ (-1 : ℤ) * (c ^ ((2 : ℝ) / 3) / 2) := by ring
              _ ≤ K_in * x ^ (-1 : ℤ) * |deriv (scaledPsi c L) x| := by gcongr
          · have hc1 : c * ς ^ 3 = 1 := by
              dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le,
                show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
            rw [hc1, one_mul]
            have h3 := (hC3 L (ς * x)).trans (div_le_self hC3_nn (one_le_pow₀ (by linarith [abs_nonneg (ς * x)])))
            have h1 : (1 : ℝ) ≤ c ^ ((2 : ℝ) / 3) * x ^ (-2 : ℤ) := by
              rw [zpow_neg, show (2 : ℤ) = (2 : ℕ) from rfl, zpow_natCast, ← div_eq_mul_inv, one_le_div (pow_pos hx0 2)]
              have hsq : ς ^ 2 * x ^ 2 ≤ 1 := by rw [← mul_pow]; exact pow_le_one₀ (by positivity) hle1
              have := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hc0.le ((2 : ℝ) / 3))
              calc x ^ 2 = (c ^ ((2 : ℝ) / 3) * ς ^ 2) * x ^ 2 := by rw [hcs2, one_mul]
                _ = c ^ ((2 : ℝ) / 3) * (ς ^ 2 * x ^ 2) := by ring
                _ ≤ c ^ ((2 : ℝ) / 3) * 1 := this
                _ = c ^ ((2 : ℝ) / 3) := mul_one _
            have hK : 2 * C3 ≤ K_in := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
            calc |iteratedDeriv 3 (edgePhi L) (ς * x)| ≤ C3 * 1 := by rw [mul_one]; exact h3
              _ ≤ C3 * (c ^ ((2 : ℝ) / 3) * x ^ (-2 : ℤ)) := mul_le_mul_of_nonneg_left h1 hC3_nn
              _ = (2 * C3) * x ^ (-2 : ℤ) * (c ^ ((2 : ℝ) / 3) / 2) := by ring
              _ ≤ K_in * x ^ (-2 : ℤ) * |deriv (scaledPsi c L) x| := by gcongr
          · have hc1 : c * ς ^ 4 = ς := by
              have h3 : c * ς ^ 3 = 1 := by
                dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le,
                  show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
              calc c * ς ^ 4 = (c * ς ^ 3) * ς := by ring
                _ = ς := by rw [h3, one_mul]
            rw [hc1, abs_mul, abs_of_pos hς_pos]
            have h4 := (hC4 L (ς * x)).trans (div_le_self hC4_nn (one_le_pow₀ (by linarith [abs_nonneg (ς * x)])))
            have h1 : ς ≤ c ^ ((2 : ℝ) / 3) * x ^ (-3 : ℤ) := by
              rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hx0 3)]
              have h3 : (ς * x) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) hle1
              have := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hc0.le ((2 : ℝ) / 3))
              calc ς * x ^ 3 = (c ^ ((2 : ℝ) / 3) * ς ^ 2) * (ς * x ^ 3) := by rw [hcs2, one_mul]
                _ = c ^ ((2 : ℝ) / 3) * (ς * x) ^ 3 := by ring
                _ ≤ c ^ ((2 : ℝ) / 3) * 1 := this
                _ = c ^ ((2 : ℝ) / 3) := mul_one _
            have hK : 2 * C4 ≤ K_in := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
            calc ς * |iteratedDeriv 4 (edgePhi L) (ς * x)| ≤ (c ^ ((2 : ℝ) / 3) * x ^ (-3 : ℤ)) * C4 :=
                  mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
              _ = (2 * C4) * x ^ (-3 : ℤ) * (c ^ ((2 : ℝ) / 3) / 2) := by ring
              _ ≤ K_in * x ^ (-3 : ℤ) * |deriv (scaledPsi c L) x| := by gcongr
        · -- `ς * x > 1`: `|Φ^{(j+1)}(ς x)| ≤ C_{j+1} (ς x)^{-j}`
          have hstep : ∀ (k : ℕ) (Ck : ℝ), 0 ≤ Ck → 2 * Ck ≤ K_in →
              |iteratedDeriv (k + 1) (edgePhi L) (ς * x)| ≤ Ck / (1 + |ς * x|) ^ k →
              |c * ς ^ (k + 1) * iteratedDeriv (k + 1) (edgePhi L) (ς * x)| ≤
                K_in * x ^ (-(k : ℤ)) * |deriv (scaledPsi c L) x| := by
            intro k Ck hCk hK_le hbound
            rw [abs_mul, abs_of_nonneg (by positivity)]
            have hden : (ς * x) ^ k ≤ (1 + |ς * x|) ^ k := by
              rw [abs_of_pos (by positivity)]
              exact pow_le_pow_left₀ (by positivity) (by linarith) k
            have h1 : |iteratedDeriv (k + 1) (edgePhi L) (ς * x)| ≤ Ck / (ς * x) ^ k :=
              hbound.trans (div_le_div_of_nonneg_left hCk (pow_pos (by positivity) k) hden)
            have hc_pow : c * ς ^ (k + 1) / (ς * x) ^ k = c ^ ((2 : ℝ) / 3) * x ^ (-(k : ℤ)) := by
              rw [mul_pow, zpow_neg, zpow_natCast, pow_succ]
              have hcs : c * ς = c ^ ((2 : ℝ) / 3) := by
                dsimp [ς]
                calc c * c ^ (-(1 : ℝ) / 3) = c ^ (1 : ℝ) * c ^ (-(1 : ℝ) / 3) := by rw [Real.rpow_one]
                  _ = c ^ ((1 : ℝ) + (-(1 : ℝ) / 3)) := (Real.rpow_add hc0 _ _).symm
                  _ = c ^ ((2 : ℝ) / 3) := by norm_num
              have hςk : ς ^ k ≠ 0 := pow_ne_zero k hς_pos.ne'
              have hxk : x ^ k ≠ 0 := pow_ne_zero k hx0.ne'
              field_simp [hςk, hxk]; rw [← hcs]
            calc c * ς ^ (k + 1) * |iteratedDeriv (k + 1) (edgePhi L) (ς * x)|
                ≤ c * ς ^ (k + 1) * (Ck / (ς * x) ^ k) := mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = Ck * (c * ς ^ (k + 1) / (ς * x) ^ k) := by ring
              _ = (2 * Ck) * x ^ (-(k : ℤ)) * (c ^ ((2 : ℝ) / 3) / 2) := by rw [hc_pow]; ring
              _ ≤ K_in * x ^ (-(k : ℤ)) * |deriv (scaledPsi c L) x| := by gcongr
          rcases hj with rfl | rfl | rfl
          · exact hstep 1 C2 hC2_nn (by simp only [K_in]; exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) (hC2 L (ς * x))
          · exact hstep 2 C3 hC3_nn (by simp only [K_in]; exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) (hC3 L (ς * x))
          · exact hstep 3 C4 hC4_nn (by simp only [K_in]; exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) (hC4 L (ς * x))
      have hg_in_bd : ∀ x ∈ Icc (1 / 2 : ℝ) ustar, ∀ j ≤ 3,
          ‖iteratedDeriv j g_in x‖ ≤ (8 * (2 * Bin) * M₀) * x ^ (-q) * x ^ (-(j : ℤ)) := by
        intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        rcases le_or_gt 1 x with hx1 | hx1
        · have hcut : ∀ j ≤ 3, |iteratedDeriv j (fun s => rhoInner (ς * s / tstar)) x| ≤ (2 * Bin) * x ^ (-(j : ℤ)) := by
            intro j hj
            have heq : (fun s => rhoInner (ς * s / tstar)) = fun s => rhoInner (ustar⁻¹ * s) := by
              ext s; dsimp [ustar]; rw [inv_div]; ring_nf
            rw [heq, iteratedDeriv_comp_mul_left_R, abs_mul, abs_of_pos (pow_pos (inv_pos.mpr hustar_pos) j)]
            have h1 : (ustar⁻¹) ^ j ≤ x ^ (-(j : ℤ)) := by
              rw [zpow_neg, zpow_natCast, inv_pow, ← one_div, ← one_div]
              exact one_div_le_one_div_of_le (pow_pos hx0 j) (pow_le_pow_left₀ hx0.le hx.2 j)
            calc (ustar⁻¹) ^ j * |iteratedDeriv j rhoInner (ustar⁻¹ * x)|
                ≤ x ^ (-(j : ℤ)) * Bin := mul_le_mul h1 (hBin j hj _) (abs_nonneg _) (by positivity)
              _ ≤ (2 * Bin) * x ^ (-(j : ℤ)) := by nlinarith [show 0 ≤ Bin * x ^ (-(j : ℤ)) by positivity]
          have hleib := leibniz3_real_mul_bound (f := fun s => rhoInner (ς * s / tstar)) (g := g) (x := x)
            (M₁ := 2 * Bin) (M₂ := M₀ * x ^ (-q)) (w := x)
            ((contDiff_rhoInner.comp ((contDiff_const.mul contDiff_id).div_const tstar)).contDiffAt.of_le (by simp))
            (hg_cd.contDiffAt (isOpen_Ioi.mem_nhds hx0))
            (by positivity) (by positivity) hx0 hcut (hg_bd x hx1)
          intro j hj; refine (hleib j hj).trans (le_of_eq ?_); ring
        · intro j _
          have hev : g_in =ᶠ[𝓝 x] 0 := by
            filter_upwards [(isOpen_Ioo (a := (0 : ℝ)) (b := 1)).mem_nhds ⟨hx0, hx1⟩] with y hy
            simp [g_in, hg_zero y hy.1 hy.2.le]
          rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero, norm_zero]; positivity
      have hibp := ibp3_interval (a := 1 / 2) (b := ustar) (by linarith) hU_in
        (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (φ := scaledPsi c L) (h := g_in) (B := fun x => (8 * (2 * Bin) * M₀) * x ^ (-q)) (w := fun x => x)
        (Λ := S / 2) (K := K_in)
        (((contDiff_scaledPsi c L).of_le (by simp)).contDiffOn)
        (hg_in_cd.mono fun x hx => hx.1) hne_in (by positivity) (le_max_left _ _)
        hvan_a hvan_b (fun x hx => by linarith [hx.1]) (fun x hx => by
          have hx0 : 0 < x := by linarith [hx.1]
          positivity)
        (fun x hx => (hψ_in x hx).1) (fun x hx => (hψ_in x hx).2) hg_in_bd
        (by
          have hcont : ContinuousOn (fun x : ℝ => (8 * (2 * Bin) * M₀) * x ^ (-q) * x ^ (-3 : ℤ)) (Icc (1 / 2) ustar) :=
            (continuousOn_const.mul (continuousOn_id.rpow_const fun x hx => Or.inl (show x ≠ 0 by linarith [hx.1]))).mul
              (continuousOn_id.zpow₀ (-3) fun x hx => Or.inl (show x ≠ 0 by linarith [hx.1]))
          exact hcont.intervalIntegrable_of_Icc (by linarith))
      have hint_le : ∫ x in (1 / 2 : ℝ)..ustar, (8 * (2 * Bin) * M₀) * x ^ (-q) * x ^ (-3 : ℤ) ≤
          (8 * (2 * Bin) * M₀) * (2 ^ (q + 2) / (q + 2)) := by
        have hcongr : ∫ x in (1 / 2 : ℝ)..ustar, (8 * (2 * Bin) * M₀) * x ^ (-q) * x ^ (-3 : ℤ) =
            (8 * (2 * Bin) * M₀) * ∫ x in (1 / 2 : ℝ)..ustar, x ^ (-q - 3) := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun x hx => ?_
          rw [uIcc_of_le (by linarith)] at hx
          have hx0 : 0 < x := by linarith [hx.1]
          rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, ← Real.rpow_natCast x 3,
            ← Real.rpow_neg hx0.le, mul_assoc, ← Real.rpow_add hx0, show -q + -(3 : ℕ) = -q - 3 by push_cast; ring]
        rw [hcongr, integral_rpow (Or.inr ⟨by dsimp [q]; linarith, fun h => by rw [uIcc_of_le (by linarith)] at h; linarith [h.1]⟩)]
        have h1 : (ustar ^ (-q - 3 + 1) - (1 / 2 : ℝ) ^ (-q - 3 + 1)) / (-q - 3 + 1) ≤ 2 ^ (q + 2) / (q + 2) := by
          rw [show -q - 3 + 1 = -(q + 2) by ring, div_neg, ← neg_div, neg_sub, sub_div]
          have h2 : (1 / 2 : ℝ) ^ (-(q + 2)) = 2 ^ (q + 2) := by
            rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
          rw [h2]
          have hnn : 0 ≤ ustar ^ (-(q + 2)) / (q + 2) := by dsimp [q]; positivity
          linarith
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hS3 : (S / 2) ^ (-3 : ℤ) ≤ 8 * S ^ (-α - 1) := by
        have h1 : (S / 2) ^ (-3 : ℤ) = 8 * S ^ (-3 : ℝ) := by
          rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, div_pow, inv_div,
            Real.rpow_neg hS_pos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num [div_eq_mul_inv]
        rw [h1]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hS_ge1 (by linarith)) (by positivity)
      calc ‖∫ u in (1 / 2 : ℝ)..ustar, Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_in u‖
          ≤ (104 * K_in ^ 3) ^ 3 * (S / 2) ^ (-3 : ℤ) * ((8 * (2 * Bin) * M₀) * (2 ^ (q + 2) / (q + 2))) :=
            hibp.trans (mul_le_mul_of_nonneg_left hint_le (by positivity))
        _ ≤ (104 * K_in ^ 3) ^ 3 * (8 * S ^ (-α - 1)) * ((8 * (2 * Bin) * M₀) * (2 ^ (q + 2) / (q + 2))) := by
            gcongr
        _ = C_in * S ^ (-α - 1) := by dsimp [C_in]; ring
  -- (2) Outer part `g_out`: change variables to `τ = ς u` (so `u = c^{1/3} τ`)
  have hOut : ‖∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_out u‖ ≤
      (C_sadL + C_tailL) * S ^ (-α - 1) := by
    let h : ℝ → ℂ := fun τ => ((1 - rhoInner (τ / tstar) : ℝ) : ℂ) *
      (((1 - chi0 (c ^ ((1 : ℝ) / 3) * τ) : ℝ) : ℂ) * A τ * Y (c ^ ((1 : ℝ) / 3) * τ))
    have hchg : ∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_out u =
        ((c ^ ((1 : ℝ) / 3) : ℝ) : ℂ) *
          ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h τ := by
      have hsc := MeasureTheory.integral_comp_mul_left_Ioi (fun u =>
        Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_out u) (0 : ℝ) (Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 3))
      simp only [mul_zero, Complex.real_smul] at hsc
      have hcongr : ∀ τ : ℝ, Complex.exp (Complex.I * (scaledPsi c L (c ^ ((1 : ℝ) / 3) * τ) : ℂ)) *
          g_out (c ^ ((1 : ℝ) / 3) * τ) =
          Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h τ := by
        intro τ
        have hmul : ς * (c ^ ((1 : ℝ) / 3) * τ) = τ := by
          rw [← mul_assoc, show ς * c ^ ((1 : ℝ) / 3) = 1 by
            rw [← hς_inv, mul_inv_cancel₀ hς_pos.ne'], one_mul]
        have hmul' : c ^ (-(1 : ℝ) / 3) * (c ^ ((1 : ℝ) / 3) * τ) = τ := hmul
        simp only [scaledPsi, g_out, g, h, hmul, hmul']
      rw [show (∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h τ) =
        ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L (c ^ ((1 : ℝ) / 3) * τ) : ℂ)) *
          g_out (c ^ ((1 : ℝ) / 3) * τ) from setIntegral_congr_fun measurableSet_Ioi fun τ _ => (hcongr τ).symm]
      rw [hsc, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.rpow_pos_of_pos hc0 _).ne',
        Complex.ofReal_one, one_mul]
    rw [hchg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
    -- Derivative bounds for `h` on `τ ≥ tstar / 2` (and `h = 0` on `τ ≤ tstar / 2` or `c^{1/3} τ ≤ 1`)
    have hh_cd : ContDiffOn ℝ 3 h (Ioi 0) := by
      have h1 : ContDiffOn ℝ 3 (fun τ : ℝ => ((1 - rhoInner (τ / tstar) : ℝ) : ℂ)) (Ioi 0) :=
        ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_rhoInner.comp (contDiff_id.div_const tstar)))).of_le
          (by simp)).contDiffOn
      have h2 : ContDiffOn ℝ 3 (fun τ : ℝ => ((1 - chi0 (c ^ ((1 : ℝ) / 3) * τ) : ℝ) : ℂ)) (Ioi 0) :=
        ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_chi0.comp
          (contDiff_const.mul contDiff_id)))).of_le (by simp)).contDiffOn
      have h3 : ContDiffOn ℝ 3 (fun τ : ℝ => Y (c ^ ((1 : ℝ) / 3) * τ)) (Ioi 0) :=
        hY.contDiffOn_Y.comp ((contDiff_const.mul contDiff_id).of_le le_top).contDiffOn
          (fun τ (hτ : 0 < τ) => ne_of_gt (mul_pos (Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 3)) hτ))
      exact h1.mul ((h2.mul hA.contDiff.contDiffOn).mul h3)
    have hh_zero : ∀ τ : ℝ, 0 < τ → τ ≤ tstar / 2 ∨ c ^ ((1 : ℝ) / 3) * τ ≤ 1 → h τ = 0 := by
      intro τ hτ hdisj
      rcases hdisj with h1 | h1
      · have hle : |τ / tstar| ≤ 1 / 2 := by rw [abs_of_pos (by positivity), div_le_iff₀ htstar_pos]; linarith
        dsimp only [h]; rw [rhoInner_eq_one hle]; simp
      · have hle : |c ^ ((1 : ℝ) / 3) * τ| ≤ 1 := by
          rw [abs_of_pos (mul_pos (Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 3)) hτ)]; exact h1
        dsimp only [h]; rw [chi0_eq_one hle]; simp
    have hh_bd : ∀ τ : ℝ, tstar / 2 ≤ τ → ∀ j ≤ 3,
        ‖iteratedDeriv j h τ‖ ≤ M_tau * c ^ (-q / 3) * Real.exp (-η * τ) * (1 : ℝ) ^ (-(j : ℤ)) := by
      intro τ hτ
      have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
      have hτ_ge20 : (1 / 20 : ℝ) ≤ τ := by linarith
      rcases le_or_gt 1 (c ^ ((1 : ℝ) / 3) * τ) with hcτ1 | hcτ1
      · -- `c^{1/3} τ ≥ 1` and `τ ≥ 1/20`
        have hcut1 : ∀ j ≤ 3, |iteratedDeriv j (fun s => 1 - rhoInner (s / tstar)) τ| ≤
            (2 * 1000 * Bin) * (1 : ℝ) ^ (-(j : ℤ)) := by
          intro j hj
          simp only [one_zpow, mul_one]
          rcases eq_or_ne j 0 with rfl | hj0
          · simp only [iteratedDeriv_zero]
            have : |1 - rhoInner (τ / tstar)| ≤ 1 := by
              rw [abs_of_nonneg (by linarith [rhoInner_le_one (τ / tstar)])]; linarith [rhoInner_nonneg (τ / tstar)]
            linarith
          · have hsub : iteratedDeriv j (fun s => 1 - rhoInner (s / tstar)) τ =
                -iteratedDeriv j (fun s => rhoInner (tstar⁻¹ * s)) τ := by
              have h1 := iteratedDeriv_sub (n := j) (x := τ) (contDiffAt_const (c := (1 : ℝ)))
                ((contDiff_rhoInner.comp (contDiff_const (c := tstar⁻¹) |>.mul contDiff_id)).contDiffAt.of_le (by simp))
              dsimp only [Function.comp_def, id_eq] at h1
              have hc0' : iteratedDeriv j (fun _ : ℝ => (1 : ℝ)) τ = 0 := by
                obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
                rw [iteratedDeriv_succ', show deriv (fun _ : ℝ => (1 : ℝ)) = 0 from funext fun _ => deriv_const _ _,
                  iteratedDeriv_const_zero]
              rw [show (fun s => 1 - rhoInner (s / tstar)) = (fun _ => (1 : ℝ)) - (fun s => rhoInner (tstar⁻¹ * s)) by
                ext s; simp [div_eq_mul_inv, mul_comm], h1, hc0', zero_sub]
            rw [hsub, abs_neg, iteratedDeriv_comp_mul_left_R, abs_mul, abs_of_pos (pow_pos (inv_pos.mpr htstar_pos) j)]
            have hinv10 : tstar⁻¹ ≤ 10 := by rw [inv_le_iff_one_le_mul₀ htstar_pos]; linarith
            have hpow : (tstar⁻¹) ^ j ≤ 1000 := by
              calc (tstar⁻¹) ^ j ≤ 10 ^ j := pow_le_pow_left₀ (by positivity) hinv10 j
                _ ≤ 10 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
                _ = 1000 := by norm_num
            calc (tstar⁻¹) ^ j * |iteratedDeriv j rhoInner (tstar⁻¹ * τ)| ≤ 1000 * Bin :=
                  mul_le_mul hpow (hBin j hj _) (abs_nonneg _) (by norm_num)
              _ ≤ 2 * 1000 * Bin := by linarith
        have hcut2 : ∀ j ≤ 3, |iteratedDeriv j (fun s => 1 - chi0 (c ^ ((1 : ℝ) / 3) * s)) τ| ≤
            (2 * 25 ^ 3 * Bχ) * (1 : ℝ) ^ (-(j : ℤ)) := by
          intro j hj
          simp only [one_zpow, mul_one]
          rcases eq_or_ne j 0 with rfl | hj0
          · simp only [iteratedDeriv_zero]
            have : |1 - chi0 (c ^ ((1 : ℝ) / 3) * τ)| ≤ 1 := by
              rw [abs_of_nonneg (by linarith [chi0_le_one (c ^ ((1 : ℝ) / 3) * τ)])]
              linarith [chi0_nonneg (c ^ ((1 : ℝ) / 3) * τ)]
            linarith
          · have hsub : iteratedDeriv j (fun s => 1 - chi0 (c ^ ((1 : ℝ) / 3) * s)) τ =
                -iteratedDeriv j (fun s => chi0 (c ^ ((1 : ℝ) / 3) * s)) τ := by
              have h1 := iteratedDeriv_sub (n := j) (x := τ) (contDiffAt_const (c := (1 : ℝ)))
                ((contDiff_chi0.comp (contDiff_const (c := c ^ ((1 : ℝ) / 3)) |>.mul contDiff_id)).contDiffAt.of_le (by simp))
              dsimp only [Function.comp_def, id_eq] at h1
              have hc0' : iteratedDeriv j (fun _ : ℝ => (1 : ℝ)) τ = 0 := by
                obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
                rw [iteratedDeriv_succ', show deriv (fun _ : ℝ => (1 : ℝ)) = 0 from funext fun _ => deriv_const _ _,
                  iteratedDeriv_const_zero]
              rw [show (fun s => 1 - chi0 (c ^ ((1 : ℝ) / 3) * s)) =
                (fun _ => (1 : ℝ)) - (fun s => chi0 (c ^ ((1 : ℝ) / 3) * s)) from rfl, h1, hc0', zero_sub]
            rw [hsub, abs_neg, iteratedDeriv_comp_mul_left_R, abs_mul,
              abs_of_pos (pow_pos (Real.rpow_pos_of_pos hc0 _) j)]
            by_cases h54 : c ^ ((1 : ℝ) / 3) * τ ≤ 5 / 4
            · have hc13_le : c ^ ((1 : ℝ) / 3) ≤ 25 := by nlinarith
              have hpow : (c ^ ((1 : ℝ) / 3)) ^ j ≤ 25 ^ 3 := by
                calc (c ^ ((1 : ℝ) / 3)) ^ j ≤ 25 ^ j := pow_le_pow_left₀ (Real.rpow_nonneg hc0.le _) hc13_le j
                  _ ≤ 25 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
              calc (c ^ ((1 : ℝ) / 3)) ^ j * |iteratedDeriv j chi0 (c ^ ((1 : ℝ) / 3) * τ)|
                  ≤ 25 ^ 3 * Bχ := mul_le_mul hpow (hBχ j hj _) (abs_nonneg _) (by positivity)
                _ ≤ 2 * 25 ^ 3 * Bχ := by linarith [show 0 ≤ 25 ^ 3 * Bχ by positivity]
            · push Not at h54
              have hev : chi0 =ᶠ[𝓝 (c ^ ((1 : ℝ) / 3) * τ)] 0 := by
                filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds
                  (show 5 / 4 < |c ^ ((1 : ℝ) / 3) * τ| by rw [abs_of_pos (by positivity)]; exact h54)] with y hy
                exact chi0_eq_zero hy.le
              rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero, abs_zero, mul_zero]; positivity
        have hY_sc : ∀ j ≤ 3, ‖iteratedDeriv j (fun s => Y (c ^ ((1 : ℝ) / 3) * s)) τ‖ ≤
            (C_Y * 20 ^ (q + 3) * c ^ (-q / 3)) * (1 : ℝ) ^ (-(j : ℤ)) := by
          intro j hj
          simp only [one_zpow, mul_one]
          rw [iteratedDeriv_comp_mul_left_C, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (pow_pos (Real.rpow_pos_of_pos hc0 _) j)]
          have h1 := hY.far_bound j hj (c ^ ((1 : ℝ) / 3) * τ) (by rw [abs_of_pos (by positivity)]; exact hcτ1)
          rw [abs_of_pos (by positivity)] at h1
          have hrpow : (c ^ ((1 : ℝ) / 3)) ^ j * (c ^ ((1 : ℝ) / 3) * τ) ^ (-q - (j : ℝ)) =
              c ^ (-q / 3) * τ ^ (-q - (j : ℝ)) := by
            rw [Real.mul_rpow (Real.rpow_nonneg hc0.le _) hτ0.le, ← mul_assoc,
              ← Real.rpow_natCast (c ^ ((1 : ℝ) / 3)) j, ← Real.rpow_mul hc0.le, ← Real.rpow_mul hc0.le,
              ← Real.rpow_add hc0]
            congr 2; ring
          have hτ_pow : τ ^ (-q - (j : ℝ)) ≤ 20 ^ (q + 3) := by
            have h1' : τ ^ (-q - (j : ℝ)) ≤ (1 / 20 : ℝ) ^ (-q - (j : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hτ_ge20 (by dsimp [q]; linarith)
            have h2' : (1 / 20 : ℝ) ^ (-q - (j : ℝ)) = 20 ^ (q + (j : ℝ)) := by
              rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]; congr 1; ring
            have h3' : (20 : ℝ) ^ (q + (j : ℝ)) ≤ 20 ^ (q + 3) := by
              have hjr : (j : ℝ) ≤ 3 := by exact_mod_cast hj
              exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            linarith
          calc (c ^ ((1 : ℝ) / 3)) ^ j * ‖iteratedDeriv j Y (c ^ ((1 : ℝ) / 3) * τ)‖
              ≤ (c ^ ((1 : ℝ) / 3)) ^ j * (C_Y * (c ^ ((1 : ℝ) / 3) * τ) ^ (-q - (j : ℝ))) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = C_Y * ((c ^ ((1 : ℝ) / 3)) ^ j * (c ^ ((1 : ℝ) / 3) * τ) ^ (-q - (j : ℝ))) := by ring
            _ = C_Y * (c ^ (-q / 3) * τ ^ (-q - (j : ℝ))) := by rw [hrpow]
            _ ≤ C_Y * (c ^ (-q / 3) * 20 ^ (q + 3)) := by gcongr
            _ = C_Y * 20 ^ (q + 3) * c ^ (-q / 3) := by ring
        have h12 := leibniz3_real_mul_bound (f := fun s => 1 - rhoInner (s / tstar))
          (g := fun s => ((1 - chi0 (c ^ ((1 : ℝ) / 3) * s) : ℝ) : ℂ)) (x := τ)
          (M₁ := 2 * 1000 * Bin) (M₂ := 2 * 25 ^ 3 * Bχ) (w := 1)
          ((contDiff_const.sub (contDiff_rhoInner.comp (contDiff_id.div_const tstar))).contDiffAt.of_le (by simp))
          ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_chi0.comp
            (contDiff_const.mul contDiff_id)))).contDiffAt.of_le (by simp))
          (by positivity) (by positivity) one_pos hcut1
          (fun j hj => by rw [iteratedDeriv_ofReal_eq', Complex.norm_real, Real.norm_eq_abs]; exact hcut2 j hj)
        have hY_comp_cd : ContDiffOn ℝ 3 (fun s : ℝ => Y (c ^ ((1 : ℝ) / 3) * s)) (Ioi 0) :=
          hY.contDiffOn_Y.comp ((contDiff_const.mul contDiff_id).of_le le_top).contDiffOn
            (fun s (hs : 0 < s) => ne_of_gt (mul_pos (Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 3)) hs))
        have h34 := leibniz3_bound (f := A) (g := fun s => Y (c ^ ((1 : ℝ) / 3) * s)) (x := τ)
          (M₁ := C_A * Real.exp (-η * τ)) (M₂ := C_Y * 20 ^ (q + 3) * c ^ (-q / 3)) (w := 1)
          hA.contDiff.contDiffAt (hY_comp_cd.contDiffAt (isOpen_Ioi.mem_nhds hτ0))
          (by positivity) (by positivity) one_pos
          (fun j hj => by simpa [abs_of_pos hτ0] using hA.deriv_bound j hj τ) hY_sc
        have htot := leibniz3_bound
          (f := fun s => ((1 - rhoInner (s / tstar) : ℝ) : ℂ) * ((1 - chi0 (c ^ ((1 : ℝ) / 3) * s) : ℝ) : ℂ))
          (g := fun s => A s * Y (c ^ ((1 : ℝ) / 3) * s)) (x := τ)
          (M₁ := 8 * (2 * 1000 * Bin) * (2 * 25 ^ 3 * Bχ))
          (M₂ := 8 * (C_A * Real.exp (-η * τ)) * (C_Y * 20 ^ (q + 3) * c ^ (-q / 3))) (w := 1)
          (((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_rhoInner.comp (contDiff_id.div_const tstar)))).contDiffAt.of_le (by simp)).mul
            ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_chi0.comp (contDiff_const.mul contDiff_id)))).contDiffAt.of_le (by simp)))
          (hA.contDiff.contDiffAt.mul (hY_comp_cd.contDiffAt (isOpen_Ioi.mem_nhds hτ0)))
          (by positivity) (by positivity) one_pos h12 h34
        have hh_eq : h = fun s => (((1 - rhoInner (s / tstar) : ℝ) : ℂ) * ((1 - chi0 (c ^ ((1 : ℝ) / 3) * s) : ℝ) : ℂ)) *
            (A s * Y (c ^ ((1 : ℝ) / 3) * s)) := by ext s; dsimp [h]; ring
        intro j hj
        rw [hh_eq]
        refine (htot j hj).trans (le_of_eq ?_); dsimp [M_tau]; ring
      · intro j _
        have hev : h =ᶠ[𝓝 τ] 0 := by
          have hτ_lt : τ < ς := by
            have hmul1 : c ^ ((1 : ℝ) / 3) * ς = 1 := by rw [← hς_inv, inv_mul_cancel₀ hς_pos.ne']
            have h2 : c ^ ((1 : ℝ) / 3) * τ < c ^ ((1 : ℝ) / 3) * ς := by rw [hmul1]; exact hcτ1
            exact lt_of_mul_lt_mul_left h2 (Real.rpow_nonneg hc0.le _)
          filter_upwards [(isOpen_Ioo (a := (0 : ℝ)) (b := ς)).mem_nhds ⟨hτ0, hτ_lt⟩] with s hs
          exact hh_zero s hs.1 (Or.inr (by
            have h1 : c ^ ((1 : ℝ) / 3) * s < c ^ ((1 : ℝ) / 3) * ς :=
              mul_lt_mul_of_pos_left hs.2 (Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 3))
            have h2 : c ^ ((1 : ℝ) / 3) * ς = 1 := by rw [← hς_inv, inv_mul_cancel₀ hς_pos.ne']
            linarith))
        rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero, norm_zero]; positivity
    -- Split `h = h_sad + h_ns` with `rhoSaddle (τ / t)`
    let h_sad : ℝ → ℂ := fun τ => (rhoSaddle (τ / t) : ℂ) * h τ
    let h_ns : ℝ → ℂ := fun τ => ((1 - rhoSaddle (τ / t) : ℝ) : ℂ) * h τ
    have hh_int_Ioi : ∀ (w : ℝ → ℝ), Continuous w → (∀ τ, |w τ| ≤ 1) →
        IntegrableOn (fun τ => Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * ((w τ : ℂ) * h τ)) (Ioi 0) := by
      intro w hw hw1
      have hcont : ContinuousOn (fun τ => Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * ((w τ : ℂ) * h τ)) (Ioi 0) :=
        ((Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.mul (contDiff_edgePhi L).continuous)))).continuousOn).mul
          ((Complex.continuous_ofReal.comp hw).continuousOn.mul hh_cd.continuousOn)
      have hdom : IntegrableOn (fun τ : ℝ => M_tau * c ^ (-q / 3) * Real.exp (-η * τ)) (Ioi 0) :=
        (integrableOn_exp_mul_Ioi (show -η < 0 by linarith) 0).const_mul (M_tau * c ^ (-q / 3))
      refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rcases le_or_gt τ (tstar / 2) with hle | hgt
      · rw [hh_zero τ hτ (Or.inl hle), norm_zero, mul_zero]; positivity
      · have h0 := hh_bd τ hgt.le 0 (by omega)
        simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at h0
        calc |w τ| * ‖h τ‖ ≤ 1 * (M_tau * c ^ (-q / 3) * Real.exp (-η * τ)) :=
              mul_le_mul (hw1 τ) h0 (norm_nonneg _) zero_le_one
          _ = M_tau * c ^ (-q / 3) * Real.exp (-η * τ) := one_mul _
    have hint_hsad := hh_int_Ioi (fun τ => rhoSaddle (τ / t))
      (contDiff_rhoSaddle.continuous.comp (continuous_id.div_const t))
      (fun τ => by rw [abs_of_nonneg (rhoSaddle_nonneg _)]; exact rhoSaddle_le_one _)
    have hint_hns := hh_int_Ioi (fun τ => 1 - rhoSaddle (τ / t))
      (continuous_const.sub (contDiff_rhoSaddle.continuous.comp (continuous_id.div_const t)))
      (fun τ => by rw [abs_of_nonneg (by linarith [rhoSaddle_le_one (τ / t)])]; linarith [rhoSaddle_nonneg (τ / t)])
    have hsplit_h : ∀ τ : ℝ, Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h τ =
        Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_sad τ +
        Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ := fun τ => by
      dsimp [h_sad, h_ns]; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun τ _ => hsplit_h τ),
      integral_add hint_hsad hint_hns]
    -- (2a) Saddle `[t/2, 2t]` via `van_der_corput_second`
    have hSadL : c ^ ((1 : ℝ) / 3) * ‖∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_sad τ‖ ≤
        C_sadL * S ^ (-α - 1) := by
      have heq_int : ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_sad τ =
          ∫ τ in (t / 2)..(2 * t), h_sad τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        have hcongr : ∫ τ in Ioc (t / 2) (2 * t), h_sad τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) =
            ∫ τ in Ioc (t / 2) (2 * t), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_sad τ := by
          refine setIntegral_congr_fun measurableSet_Ioc fun τ _ => ?_
          rw [mul_comm]; congr 2; push_cast; ring
        rw [hcongr]
        exact setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (s := Ioc (t / 2) (2 * t)) (t := Ioi 0)
          (f := fun τ => Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_sad τ)
          measurableSet_Ioi.nullMeasurableSet
          (fun τ hτ => lt_of_lt_of_le (by positivity) hτ.1.le)
          (Filter.Eventually.of_forall fun τ hτ => by
            have hnot : τ ≤ t / 2 ∨ 2 * t < τ := by
              have := hτ.2; rw [mem_Ioc] at this; push Not at this
              rcases le_or_gt τ (t / 2) with h1 | h1
              · exact Or.inl h1
              · exact Or.inr (this h1)
            rcases hnot with h1 | h1
            · have hle : τ / t ≤ 1 / 2 := (div_le_iff₀ ht0).mpr (by linarith)
              rw [show h_sad τ = 0 by simp [h_sad, rhoSaddle_eq_zero_of_le hle], mul_zero]
            · have hge : 7 / 4 ≤ τ / t := (le_div_iff₀ ht0).mpr (by linarith)
              rw [show h_sad τ = 0 by simp [h_sad, rhoSaddle_eq_zero_of_ge hge], mul_zero])
      rw [heq_int]
      have hφ : ∀ y ∈ Icc (t / 2) (2 * t), HasDerivAt (edgePhi L) (edgePhiDeriv L y) y :=
        fun y _ => hasDerivAt_edgePhi L y
      have hφ' : ∀ y ∈ Icc (t / 2) (2 * t), HasDerivAt (edgePhiDeriv L) (edgePhiDeriv2 y) y :=
        fun y _ => hasDerivAt_edgePhiDeriv L y
      have hφ''_neg : ∀ y ∈ Icc (t / 2) (2 * t), edgePhiDeriv2 y ≤ -(1 / (10 * t)) := by
        intro y hy
        have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy.1
        have hm' := (hankelEdgeM'_bounds hy0).1
        have hden : 1 + y ^ 2 ≤ 10 * t * y := by
          have h1 : 1 ≤ 8 * t * y := by nlinarith [hy.1, ht_ge_half]
          have h2 : y ^ 2 ≤ 2 * t * y := by nlinarith [hy.2, hy0]
          linarith
        have hlb : 1 / (10 * t) ≤ y / (1 + y ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        have hed2 : edgePhiDeriv2 y = -hankelEdgeM' y := by unfold hankelEdgeM'; ring
        linarith
      have hφ'_anti : AntitoneOn (edgePhiDeriv L) (Icc (t / 2) (2 * t)) :=
        antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
          (contDiff_edgePhiDeriv L).continuous.continuousOn
          (fun y hy => (hφ' y (interior_subset hy)).hasDerivWithinAt)
          (fun y hy => by
            have h1 := hφ''_neg y (interior_subset hy)
            have h2 : 0 < 1 / (10 * t) := by positivity
            linarith)
      have hh_sad_cd : ContDiffOn ℝ 3 h_sad (Ioi 0) :=
        ((Complex.ofRealCLM.contDiff.comp (contDiff_rhoSaddle.comp (contDiff_id.div_const t))).of_le (by simp)).contDiffOn.mul hh_cd
      have hh_sad_bd : ∀ y ∈ Icc (t / 2) (2 * t),
          ‖h_sad y‖ ≤ Bρ * M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2)) := by
        intro y hy
        have hy_ts : tstar / 2 ≤ y := by linarith [hy.1, htstar_lt]
        dsimp only [h_sad]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hρ0 := hBρ 0 (by omega) (y / t); simp only [iteratedDeriv_zero] at hρ0
        have hh0 := hh_bd y hy_ts 0 (by omega); simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at hh0
        have hexp : Real.exp (-η * y) ≤ Real.exp (-η * (t / 2)) := Real.exp_le_exp.mpr (by nlinarith [hy.1])
        calc |rhoSaddle (y / t)| * ‖h y‖ ≤ Bρ * (M_tau * c ^ (-q / 3) * Real.exp (-η * y)) :=
              mul_le_mul hρ0 hh0 (norm_nonneg _) (by linarith)
          _ ≤ Bρ * (M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2))) := by gcongr
          _ = Bρ * M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2)) := by ring
      have hh_sad_deriv_bd : ∀ y ∈ Icc (t / 2) (2 * t),
          ‖deriv h_sad y‖ ≤ 8 * Bρ * M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2)) := by
        intro y hy
        have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy.1
        have hy_ts : tstar / 2 ≤ y := by linarith [hy.1, htstar_lt]
        have hdρ : HasDerivAt (fun s => rhoSaddle (s / t)) (deriv rhoSaddle (y / t) / t) y :=
          (((contDiff_rhoSaddle.differentiable (by simp) (y / t)).hasDerivAt).comp y
            ((hasDerivAt_id y).div_const t)).congr_deriv (by ring)
        have hdh : HasDerivAt h (deriv h y) y :=
          ((hh_cd.differentiableOn (by norm_num) y hy0).differentiableAt (isOpen_Ioi.mem_nhds hy0)).hasDerivAt
        rw [show deriv h_sad y = ((deriv rhoSaddle (y / t) / t : ℝ) : ℂ) * h y + (rhoSaddle (y / t) : ℂ) * deriv h y from
          ((hdρ.ofReal_comp).mul hdh).deriv]
        have hρ0 := hBρ 0 (by omega) (y / t); simp only [iteratedDeriv_zero] at hρ0
        have hρ1 := hBρ 1 (by omega) (y / t); rw [iteratedDeriv_one] at hρ1
        have hh0 := hh_bd y hy_ts 0 (by omega); simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at hh0
        have hh1 := hh_bd y hy_ts 1 (by omega); simp only [iteratedDeriv_one, Nat.cast_one, zpow_neg_one, inv_one, mul_one] at hh1
        have hexp : Real.exp (-η * y) ≤ Real.exp (-η * (t / 2)) := Real.exp_le_exp.mpr (by nlinarith [hy.1])
        have ht_inv : t⁻¹ ≤ 2 := by rw [inv_le_iff_one_le_mul₀ ht0]; linarith
        calc ‖((deriv rhoSaddle (y / t) / t : ℝ) : ℂ) * h y + (rhoSaddle (y / t) : ℂ) * deriv h y‖
            ≤ |deriv rhoSaddle (y / t)| * t⁻¹ * ‖h y‖ + |rhoSaddle (y / t)| * ‖deriv h y‖ := by
              refine (norm_add_le _ _).trans (le_of_eq ?_)
              simp [Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, abs_of_pos ht0]
          _ ≤ Bρ * 2 * (M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2))) +
              Bρ * (M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2))) := by
              have h1 : |deriv rhoSaddle (y / t)| * t⁻¹ * ‖h y‖ ≤ Bρ * 2 * (M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2))) :=
                mul_le_mul (mul_le_mul hρ1 ht_inv (by positivity) (by linarith))
                  (hh0.trans (by gcongr)) (norm_nonneg _) (by positivity)
              have h2 : |rhoSaddle (y / t)| * ‖deriv h y‖ ≤ Bρ * (M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2))) :=
                mul_le_mul hρ0 (hh1.trans (by gcongr)) (norm_nonneg _) (by linarith)
              linarith
          _ ≤ 8 * Bρ * M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2)) := by
              have : 0 ≤ Bρ * M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2)) := by positivity
              linarith
      obtain ⟨hbv, hev_le⟩ := eVariationOn_le_of_deriv_bound (a := t / 2) (b := 2 * t)
        (M' := 8 * Bρ * M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2))) (by linarith) (by positivity)
        isOpen_Ioi (fun y hy => lt_of_lt_of_le (by positivity) hy.1) (hh_sad_cd.of_le (by norm_num))
        hh_sad_deriv_bd
      have hvdc := van_der_corput_second (a := t / 2) (b := 2 * t) (c := c) (lam := 1 / (10 * t))
        (M := Bρ * M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2))) (by linarith) hc0 (by positivity)
        hφ hφ' (Or.inr hφ'_anti)
        (fun y hy => by
          have h1 := hφ''_neg y hy
          have h2 : 0 < 1 / (10 * t) := by positivity
          rw [abs_of_neg (by linarith)]; linarith)
        (hh_sad_cd.continuousOn.mono fun y hy => lt_of_lt_of_le (by positivity) hy.1)
        hbv hh_sad_bd
      -- Combine powers of `c`, `t`, and `exp(-η t / 2)`
      have hc_pow : c ^ ((1 : ℝ) / 3) * c ^ (-q / 3) / Real.sqrt c = c ^ (-(2 * (α + 1)) / 3) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hc0, ← Real.rpow_sub hc0]
        congr 1; dsimp [q]; ring
      have hsqrt : Real.sqrt (c * (1 / (10 * t))) = Real.sqrt c / (Real.sqrt 10 * t ^ ((1 : ℝ) / 2)) := by
        rw [show c * (1 / (10 * t)) = c / (10 * t) by ring, Real.sqrt_div hc0.le,
          Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow t]
      have hexp_split : Real.exp (-η * (t / 2)) = Real.exp (-(η / 4) * t) * Real.exp (-(η / 4) * t) := by
        rw [← Real.exp_add]; congr 1; ring
      have hexp_L : Real.exp (-(η / 4) * t) ≤ C_exp_sad * L ^ (-α - 1) := by
        have h1 : Real.exp (L / 2) / π ≤ t := by
          have : Real.exp (L / 2) ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
          exact (div_le_div_of_nonneg_right this Real.pi_pos.le).trans ht_lo
        have h2 : Real.exp (-(η / 4) * t) ≤ Real.exp (-(η / (4 * π)) * Real.exp (L / 2)) :=
          Real.exp_le_exp.mpr (by
            have : η / 4 * (Real.exp (L / 2) / π) ≤ η / 4 * t := mul_le_mul_of_nonneg_left h1 (by positivity)
            linarith [show -(η / (4 * π)) * Real.exp (L / 2) = -(η / 4 * (Real.exp (L / 2) / π)) by ring])
        exact h2.trans (by simpa [show -(α + 1) = -α - 1 by ring] using hC_exp_sad L hL)
      have hS_eq : c ^ (-(2 * (α + 1)) / 3) * L ^ (-α - 1) = S ^ (-α - 1) := by
        dsimp [S]
        rw [Real.mul_rpow (Real.rpow_nonneg hc0.le _) hL0.le, ← Real.rpow_mul hc0.le]
        congr 2; ring
      have hlen : 2 * t - t / 2 ≤ 4 * t := by linarith
      have ht_pow32 : t ^ ((1 : ℝ) / 2) * t = t ^ ((3 : ℝ) / 2) := by
        conv_rhs => rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num]
        rw [Real.rpow_add ht0, Real.rpow_one]
      have hterm1 : t ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * t) ≤ C_abs_t1 := hC_abs_t1 t ht0.le
      have hterm2 : t ^ ((1 : ℝ) / 2) * (4 * t) * Real.exp (-(η / 4) * t) ≤ 4 * C_abs_t := by
        calc t ^ ((1 : ℝ) / 2) * (4 * t) * Real.exp (-(η / 4) * t)
            = 4 * (t ^ ((3 : ℝ) / 2) * Real.exp (-(η / 4) * t)) := by rw [← ht_pow32]; ring
          _ ≤ 4 * C_abs_t := mul_le_mul_of_nonneg_left (hC_abs_t t ht0.le) (by norm_num)
      calc c ^ ((1 : ℝ) / 3) * ‖∫ τ in (t / 2)..(2 * t), h_sad τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖
          ≤ c ^ ((1 : ℝ) / 3) * (8 * (Bρ * M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2)) +
              (eVariationOn h_sad (Icc (t / 2) (2 * t))).toReal) / Real.sqrt (c * (1 / (10 * t)))) :=
            mul_le_mul_of_nonneg_left hvdc (Real.rpow_nonneg hc0.le _)
        _ ≤ c ^ ((1 : ℝ) / 3) * (8 * (Bρ * M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2)) +
              8 * Bρ * M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2)) * (4 * t)) /
              (Real.sqrt c / (Real.sqrt 10 * t ^ ((1 : ℝ) / 2)))) := by
            rw [hsqrt]
            have hev' : (eVariationOn h_sad (Icc (t / 2) (2 * t))).toReal ≤
                8 * Bρ * M_tau * c ^ (-q / 3) * Real.exp (-η * (t / 2)) * (4 * t) :=
              hev_le.trans (mul_le_mul_of_nonneg_left hlen (by positivity))
            gcongr
        _ = 8 * (Bρ * M_tau * (t ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * t)) +
              8 * Bρ * M_tau * (t ^ ((1 : ℝ) / 2) * (4 * t) * Real.exp (-(η / 4) * t))) *
              Real.sqrt 10 * (c ^ ((1 : ℝ) / 3) * c ^ (-q / 3) / Real.sqrt c) * Real.exp (-(η / 4) * t) := by
            rw [hexp_split]; field_simp [(Real.sqrt_pos.mpr hc0).ne']
        _ ≤ 8 * (Bρ * M_tau * C_abs_t1 + 8 * Bρ * M_tau * (4 * C_abs_t)) *
              Real.sqrt 10 * c ^ (-(2 * (α + 1)) / 3) * (C_exp_sad * L ^ (-α - 1)) := by
            rw [hc_pow]
            have hsum_le : Bρ * M_tau * (t ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * t)) +
                8 * Bρ * M_tau * (t ^ ((1 : ℝ) / 2) * (4 * t) * Real.exp (-(η / 4) * t)) ≤
                Bρ * M_tau * C_abs_t1 + 8 * Bρ * M_tau * (4 * C_abs_t) := by
              have h1 := mul_le_mul_of_nonneg_left hterm1 (show 0 ≤ Bρ * M_tau by positivity)
              have h2 := mul_le_mul_of_nonneg_left hterm2 (show 0 ≤ 8 * Bρ * M_tau by positivity)
              linarith
            have hfac_le : 8 * (Bρ * M_tau * (t ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * t)) +
                8 * Bρ * M_tau * (t ^ ((1 : ℝ) / 2) * (4 * t) * Real.exp (-(η / 4) * t))) *
                Real.sqrt 10 * c ^ (-(2 * (α + 1)) / 3) ≤
                8 * (Bρ * M_tau * C_abs_t1 + 8 * Bρ * M_tau * (4 * C_abs_t)) *
                Real.sqrt 10 * c ^ (-(2 * (α + 1)) / 3) := by gcongr
            exact mul_le_mul hfac_le hexp_L (Real.exp_pos _).le (by positivity)
        _ = C_sadL * S ^ (-α - 1) := by
            rw [← hS_eq]; dsimp [C_sadL]; ring
    -- (2b) Tails `[tstar/2, 3t/4]` and `[3t/2, ∞)` via `ibp3_interval` and `ibp3_Ioi`
    have hTailL : c ^ ((1 : ℝ) / 3) * ‖∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ‖ ≤
        C_tailL * S ^ (-α - 1) := by
      have hh_ns_cd : ContDiffOn ℝ 3 h_ns (Ioi 0) :=
        ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_rhoSaddle.comp (contDiff_id.div_const t)))).of_le
          (by simp)).contDiffOn.mul hh_cd
      have hh_ns_zero_mid : ∀ τ : ℝ, 3 / 4 * t ≤ τ → τ ≤ 3 / 2 * t → h_ns τ = 0 := fun τ h1 h2 => by
        have hρ : rhoSaddle (τ / t) = 1 :=
          rhoSaddle_eq_one (by rw [le_div_iff₀ ht0]; linarith) (by rw [div_le_iff₀ ht0]; linarith)
        simp [h_ns, hρ]
      have hsplit_ns : ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ =
          (∫ τ in (tstar / 2)..(3 / 4 * t), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ) +
          (∫ τ in Ioi (3 / 2 * t), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ) := by
        have h1 : (∫ τ in Ioc (0 : ℝ) (3 / 2 * t), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ) +
            (∫ τ in Ioi (3 / 2 * t), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ) =
            ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ := by
          rw [← setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
            measurableSet_Ioi (hint_hns.mono_set Ioc_subset_Ioi_self) (hint_hns.mono_set (Ioi_subset_Ioi (by positivity))),
            Ioc_union_Ioi_eq_Ioi (by positivity)]
        rw [← h1]; congr 1
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (s := Ioc (tstar / 2) (3 / 4 * t)) (t := Ioc 0 (3 / 2 * t))
          (f := fun τ => Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ)
          measurableSet_Ioc.nullMeasurableSet
          (Ioc_subset_Ioc (by positivity) (by linarith))
          (Filter.Eventually.of_forall fun τ hτ => by
            have hnot : τ ≤ tstar / 2 ∨ 3 / 4 * t < τ := by
              have := hτ.2; rw [mem_Ioc] at this; push Not at this
              rcases le_or_gt τ (tstar / 2) with h1 | h1
              · exact Or.inl h1
              · exact Or.inr (this h1)
            rcases hnot with h1 | h1
            · rw [show h_ns τ = 0 by simp [h_ns, hh_zero τ hτ.1.1 (Or.inl h1)], mul_zero]
            · rw [hh_ns_zero_mid τ h1.le hτ.1.2, mul_zero])
      -- Derivative bound on `h_ns` for `τ ≥ tstar / 2` with `w = 1`
      have hh_ns_bd : ∀ τ : ℝ, tstar / 2 ≤ τ → ∀ j ≤ 3,
          ‖iteratedDeriv j h_ns τ‖ ≤ (8 * (2 * 8 * Bρ) * M_tau) * c ^ (-q / 3) * Real.exp (-η * τ) * (1 : ℝ) ^ (-(j : ℤ)) := by
        intro τ hτ
        have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
        have hcut : ∀ j ≤ 3, |iteratedDeriv j (fun s => 1 - rhoSaddle (s / t)) τ| ≤ (2 * 8 * Bρ) * (1 : ℝ) ^ (-(j : ℤ)) := by
          intro j hj
          simp only [one_zpow, mul_one]
          rcases eq_or_ne j 0 with rfl | hj0
          · simp only [iteratedDeriv_zero]
            have : |1 - rhoSaddle (τ / t)| ≤ 1 := by
              rw [abs_of_nonneg (by linarith [rhoSaddle_le_one (τ / t)])]; linarith [rhoSaddle_nonneg (τ / t)]
            linarith
          · have hsub : iteratedDeriv j (fun s => 1 - rhoSaddle (s / t)) τ =
                -iteratedDeriv j (fun s => rhoSaddle (t⁻¹ * s)) τ := by
              have h1 := iteratedDeriv_sub (n := j) (x := τ) (contDiffAt_const (c := (1 : ℝ)))
                ((contDiff_rhoSaddle.comp (contDiff_const (c := t⁻¹) |>.mul contDiff_id)).contDiffAt.of_le (by simp))
              dsimp only [Function.comp_def, id_eq] at h1
              have hc0' : iteratedDeriv j (fun _ : ℝ => (1 : ℝ)) τ = 0 := by
                obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
                rw [iteratedDeriv_succ', show deriv (fun _ : ℝ => (1 : ℝ)) = 0 from funext fun _ => deriv_const _ _,
                  iteratedDeriv_const_zero]
              rw [show (fun s => 1 - rhoSaddle (s / t)) = (fun _ => (1 : ℝ)) - (fun s => rhoSaddle (t⁻¹ * s)) by
                ext s; simp [div_eq_mul_inv, mul_comm], h1, hc0', zero_sub]
            rw [hsub, abs_neg, iteratedDeriv_comp_mul_left_R, abs_mul, abs_of_pos (pow_pos (inv_pos.mpr ht0) j)]
            have ht_inv : t⁻¹ ≤ 2 := by rw [inv_le_iff_one_le_mul₀ ht0]; linarith
            have hpow : (t⁻¹) ^ j ≤ 8 := by
              calc (t⁻¹) ^ j ≤ 2 ^ j := pow_le_pow_left₀ (by positivity) ht_inv j
                _ ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
                _ = 8 := by norm_num
            calc (t⁻¹) ^ j * |iteratedDeriv j rhoSaddle (t⁻¹ * τ)| ≤ 8 * Bρ :=
                  mul_le_mul hpow (hBρ j hj _) (abs_nonneg _) (by norm_num)
              _ ≤ 2 * 8 * Bρ := by linarith
        have hleib := leibniz3_real_mul_bound (f := fun s => 1 - rhoSaddle (s / t)) (g := h) (x := τ)
          (M₁ := 2 * 8 * Bρ) (M₂ := M_tau * c ^ (-q / 3) * Real.exp (-η * τ)) (w := 1)
          ((contDiff_const.sub (contDiff_rhoSaddle.comp (contDiff_id.div_const t))).contDiffAt.of_le (by simp))
          (hh_cd.contDiffAt (isOpen_Ioi.mem_nhds hτ0))
          (by positivity) (by positivity) one_pos hcut (hh_bd τ hτ)
        intro j hj; refine (hleib j hj).trans (le_of_eq ?_); ring
      -- Phase derivative bounds for `φ(τ) = c * edgePhi L τ` on both tails
      have hφ_cd : ContDiff ℝ (⊤ : ℕ∞) (fun τ => c * edgePhi L τ) := contDiff_const.mul (contDiff_edgePhi L)
      have hφ_d1 : ∀ τ : ℝ, deriv (fun s => c * edgePhi L s) τ = c * (L - hankelEdgeM τ) := fun τ => by
        rw [((hasDerivAt_edgePhi L τ).const_mul c).deriv, edgePhiDeriv_eq_sub_m]
      have hφ_dk : ∀ (τ : ℝ), c / 32 ≤ |deriv (fun s => c * edgePhi L s) τ| →
          ∀ j ∈ ({1, 2, 3} : Finset ℕ),
            |iteratedDeriv (j + 1) (fun s => c * edgePhi L s) τ| ≤
              K_tau * (1 : ℝ) ^ (-(j : ℤ)) * |deriv (fun s => c * edgePhi L s) τ| := by
        intro τ h1 j hj
        simp only [one_zpow, mul_one]
        rw [iteratedDeriv_const_mul_field c (edgePhi L), abs_mul, abs_of_pos hc0]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl
        · have h2 := (hC2 L τ).trans (div_le_self hC2_nn (one_le_pow₀ (by linarith [abs_nonneg τ])))
          have hK : 32 * C2 ≤ K_tau := le_trans (le_max_left _ _) (le_max_right _ _)
          calc c * |iteratedDeriv 2 (edgePhi L) τ| ≤ c * C2 := mul_le_mul_of_nonneg_left h2 hc0.le
            _ = (32 * C2) * (c / 32) := by ring
            _ ≤ K_tau * |deriv (fun s => c * edgePhi L s) τ| := by gcongr
        · have h3 := (hC3 L τ).trans (div_le_self hC3_nn (one_le_pow₀ (by linarith [abs_nonneg τ])))
          have hK : 32 * C3 ≤ K_tau := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
          calc c * |iteratedDeriv 3 (edgePhi L) τ| ≤ c * C3 := mul_le_mul_of_nonneg_left h3 hc0.le
            _ = (32 * C3) * (c / 32) := by ring
            _ ≤ K_tau * |deriv (fun s => c * edgePhi L s) τ| := by gcongr
        · have h4 := (hC4 L τ).trans (div_le_self hC4_nn (one_le_pow₀ (by linarith [abs_nonneg τ])))
          have hK : 32 * C4 ≤ K_tau := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
          calc c * |iteratedDeriv 4 (edgePhi L) τ| ≤ c * C4 := mul_le_mul_of_nonneg_left h4 hc0.le
            _ = (32 * C4) * (c / 32) := by ring
            _ ≤ K_tau * |deriv (fun s => c * edgePhi L s) τ| := by gcongr
      -- Vanishing of `h_ns` at `tstar/2`, `3t/4`, `3t/2`
      have hvan_ts : ∀ j ≤ 2, iteratedDeriv j h_ns (tstar / 2) = 0 :=
        iteratedDeriv_eq_zero_of_eq_zero_on_Ioo isOpen_Ioi hh_ns_cd
          (a := 0) (b := tstar / 2) (by positivity) ⟨by positivity, le_rfl⟩ (mem_Ioi.mpr (by positivity))
          (fun y hy => by simp [h_ns, hh_zero y hy.1 (Or.inl hy.2.le)])
      have hvan_34 : ∀ j ≤ 2, iteratedDeriv j h_ns (3 / 4 * t) = 0 :=
        iteratedDeriv_eq_zero_of_eq_zero_on_Ioo isOpen_Ioi hh_ns_cd
          (a := 3 / 4 * t) (b := 3 / 2 * t) (by linarith) ⟨le_rfl, by linarith⟩ (mem_Ioi.mpr (by positivity))
          (fun y hy => hh_ns_zero_mid y hy.1.le hy.2.le)
      have hvan_32 : ∀ j ≤ 2, iteratedDeriv j h_ns (3 / 2 * t) = 0 :=
        iteratedDeriv_eq_zero_of_eq_zero_on_Ioo isOpen_Ioi hh_ns_cd
          (a := 3 / 4 * t) (b := 3 / 2 * t) (by linarith) ⟨by linarith, le_rfl⟩ (mem_Ioi.mpr (by positivity))
          (fun y hy => hh_ns_zero_mid y hy.1.le hy.2.le)
      set M_t := 8 * (2 * 8 * Bρ) * M_tau
      have hibp1 := ibp3_interval (a := tstar / 2) (b := 3 / 4 * t) (by linarith)
        isOpen_Ioo (fun x hx => ⟨lt_of_lt_of_le (by positivity) hx.1, by linarith [hx.2]⟩)
        (φ := fun s => c * edgePhi L s) (h := h_ns)
        (B := fun s => M_t * c ^ (-q / 3) * Real.exp (-η * s)) (w := fun _ => 1)
        (Λ := c / 32) (K := K_tau)
        ((hφ_cd.of_le (by simp)).contDiffOn)
        (hh_ns_cd.mono fun x (hx : x ∈ Ioo 0 (7 / 8 * t)) => hx.1)
        (fun x hx => by
          rw [hφ_d1]
          have hm_lt : hankelEdgeM x < L := by
            rw [← ceEll_tau0 hL0]
            exact hankelEdgeM_strictMonoOn hx.1.le ht0.le (by linarith [hx.2])
          exact ne_of_gt (mul_pos hc0 (sub_pos.mpr hm_lt)))
        (by positivity) (le_max_left _ _) hvan_ts hvan_34
        (fun _ _ => one_pos) (fun _ _ => by positivity)
        (fun x hx => by
          rw [hφ_d1, abs_mul, abs_of_pos hc0]
          have h1 := hankelEdgeM_diff_large_inner hL (le_trans (by positivity) hx.1) hx.2
          rw [abs_of_pos (by linarith)]; nlinarith)
        (fun x hx => hφ_dk x (by
          rw [hφ_d1, abs_mul, abs_of_pos hc0]
          have h1 := hankelEdgeM_diff_large_inner hL (le_trans (by positivity) hx.1) hx.2
          rw [abs_of_pos (by linarith)]; nlinarith))
        (fun x hx => hh_ns_bd x hx.1)
        (by
          have hcont : Continuous (fun s : ℝ => M_t * c ^ (-q / 3) * Real.exp (-η * s) * (1 : ℝ) ^ (-3 : ℤ)) :=
            ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul continuous_const)
          exact hcont.intervalIntegrable _ _)
      have hibp2 := ibp3_Ioi (a := 3 / 2 * t)
        isOpen_Ioi (fun x hx => lt_of_lt_of_le (by linarith : 5 / 4 * t < 3 / 2 * t) hx)
        (φ := fun s => c * edgePhi L s) (h := h_ns)
        (B := fun s => M_t * c ^ (-q / 3) * Real.exp (-η * s)) (w := fun _ => 1)
        (Λ := c / 32) (K := K_tau)
        ((hφ_cd.of_le (by simp)).contDiffOn)
        (hh_ns_cd.mono fun x (hx : 5 / 4 * t < x) => lt_trans (by positivity) hx)
        (fun x hx => by
          rw [hφ_d1]
          have hm_gt : L < hankelEdgeM x := by
            rw [← ceEll_tau0 hL0]
            exact hankelEdgeM_strictMonoOn ht0.le (le_of_lt (lt_trans (by positivity) hx)) (by linarith [mem_Ioi.mp hx])
          exact ne_of_lt (mul_neg_of_pos_of_neg hc0 (sub_neg.mpr hm_gt)))
        (by positivity) (le_max_left _ _) hvan_32
        (fun _ _ => one_pos) (fun _ _ => by positivity)
        (fun x hx => by
          rw [hφ_d1, abs_mul, abs_of_pos hc0]
          have h1 := hankelEdgeM_diff_large_outer hL hx
          rw [abs_of_neg (by linarith)]; nlinarith)
        (fun x hx => hφ_dk x (by
          rw [hφ_d1, abs_mul, abs_of_pos hc0]
          have h1 := hankelEdgeM_diff_large_outer hL hx
          rw [abs_of_neg (by linarith)]; nlinarith))
        (fun x hx => hh_ns_bd x (by linarith [mem_Ici.mp hx]))
        (hint_hns.mono_set (Ioi_subset_Ioi (by positivity)))
        (by
          exact IntegrableOn.congr_fun
            ((integrableOn_exp_mul_Ioi (show -η < 0 by linarith) (3 / 2 * t)).const_mul (M_t * c ^ (-q / 3)))
            (fun x _ => by simp only [one_zpow, mul_one]) measurableSet_Ioi)
        (fun j _ => by
          simp only [one_zpow, mul_one]
          have ht : Tendsto (fun x : ℝ => Real.exp (-η * x)) atTop (𝓝 0) :=
            Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id)
          simpa using ht.const_mul (M_t * c ^ (-q / 3)))
      have hint1_le : ∫ s in (tstar / 2)..(3 / 4 * t), M_t * c ^ (-q / 3) * Real.exp (-η * s) * (1 : ℝ) ^ (-3 : ℤ) ≤
          M_t * c ^ (-q / 3) * (Real.exp (-η * (tstar / 2)) / η) := by
        simp only [one_zpow, mul_one]
        rw [intervalIntegral.integral_const_mul]
        have hev : ∫ s in (tstar / 2)..(3 / 4 * t), Real.exp (-η * s) =
            (Real.exp (-η * (tstar / 2)) - Real.exp (-η * (3 / 4 * t))) / η := by
          have hd : ∀ x ∈ uIcc (tstar / 2) (3 / 4 * t),
              HasDerivAt (fun s => -Real.exp (-η * s) / η) (Real.exp (-η * x)) x := fun x _ => by
            have h1 : HasDerivAt (fun s => -η * s) (-η) x := by simpa using (hasDerivAt_id x).const_mul (-η)
            have h2 := ((Real.hasDerivAt_exp (-η * x)).comp x h1).neg.div_const η
            exact h2.congr_deriv (by field_simp [hη.ne'])
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
            ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
          ring
        rw [hev]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 0 ≤ Real.exp (-η * (3 / 4 * t)) / η := by positivity
        rw [sub_div]; linarith
      have hint2_le : ∫ s in Ioi (3 / 2 * t), M_t * c ^ (-q / 3) * Real.exp (-η * s) * (1 : ℝ) ^ (-3 : ℤ) ≤
          M_t * c ^ (-q / 3) * (Real.exp (-η * (tstar / 2)) / η) := by
        simp only [one_zpow, mul_one]
        rw [integral_const_mul, integral_exp_mul_Ioi (show -η < 0 by linarith) (3 / 2 * t)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_neg, ← neg_div, neg_neg]
        have : Real.exp (-η * (3 / 2 * t)) ≤ Real.exp (-η * (tstar / 2)) :=
          Real.exp_le_exp.mpr (by nlinarith)
        exact div_le_div_of_nonneg_right this hη.le
      have hexp_ts : Real.exp (-η * (tstar / 2)) ≤ C_exp_tail * L ^ (-α - 1) := by
        have heq : -η * (tstar / 2) = -(η / (8 * π)) * Real.exp (L / 2) := by dsimp [tstar]; ring
        rw [heq]
        simpa [show -(α + 1) = -α - 1 by ring] using hC_exp_tail L hL
      have hc_pow : c ^ ((1 : ℝ) / 3) * (c / 32) ^ (-3 : ℤ) * c ^ (-q / 3) ≤
          32 ^ 3 * c ^ (-(2 * (α + 1)) / 3) := by
        have h1 : (c / 32) ^ (-3 : ℤ) = 32 ^ 3 * c ^ (-3 : ℝ) := by
          rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, div_pow, inv_div,
            Real.rpow_neg hc0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          ring_nf
        rw [h1]
        have h2 : c ^ ((1 : ℝ) / 3) * (32 ^ 3 * c ^ (-3 : ℝ)) * c ^ (-q / 3) =
            32 ^ 3 * c ^ (1 / 3 - 3 - q / 3) := by
          calc c ^ ((1 : ℝ) / 3) * (32 ^ 3 * c ^ (-3 : ℝ)) * c ^ (-q / 3)
              = 32 ^ 3 * (c ^ ((1 : ℝ) / 3) * c ^ (-3 : ℝ) * c ^ (-q / 3)) := by ring
            _ = 32 ^ 3 * c ^ (1 / 3 - 3 - q / 3) := by
                rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; congr 2; ring
        rw [h2]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hc (by dsimp [q]; linarith)) (by positivity)
      have hS_eq : c ^ (-(2 * (α + 1)) / 3) * L ^ (-α - 1) = S ^ (-α - 1) := by
        dsimp [S]
        rw [Real.mul_rpow (Real.rpow_nonneg hc0.le _) hL0.le, ← Real.rpow_mul hc0.le]
        congr 2; ring
      rw [hsplit_ns]
      calc c ^ ((1 : ℝ) / 3) * ‖(∫ τ in (tstar / 2)..(3 / 4 * t), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ) +
              ∫ τ in Ioi (3 / 2 * t), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ‖
          ≤ c ^ ((1 : ℝ) / 3) * (‖∫ τ in (tstar / 2)..(3 / 4 * t), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ‖ +
              ‖∫ τ in Ioi (3 / 2 * t), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.rpow_nonneg hc0.le _)
        _ ≤ c ^ ((1 : ℝ) / 3) * (2 * ((104 * K_tau ^ 3) ^ 3 * (c / 32) ^ (-3 : ℤ) *
              (M_t * c ^ (-q / 3) * (Real.exp (-η * (tstar / 2)) / η)))) := by
            have h1 := hibp1.trans (mul_le_mul_of_nonneg_left hint1_le (by positivity))
            have h2 := hibp2.trans (mul_le_mul_of_nonneg_left hint2_le (by positivity))
            exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hc0.le _)
        _ = 2 * ((104 * K_tau ^ 3) ^ 3 * M_t * (1 / η)) *
              (c ^ ((1 : ℝ) / 3) * (c / 32) ^ (-3 : ℤ) * c ^ (-q / 3)) * Real.exp (-η * (tstar / 2)) := by ring
        _ ≤ 2 * ((104 * K_tau ^ 3) ^ 3 * M_t * (1 / η)) *
              (32 ^ 3 * c ^ (-(2 * (α + 1)) / 3)) * (C_exp_tail * L ^ (-α - 1)) := by
            gcongr
        _ = C_tailL * S ^ (-α - 1) := by rw [← hS_eq]; dsimp [C_tailL, M_t]; ring
    calc c ^ ((1 : ℝ) / 3) * ‖(∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_sad τ) +
            ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ‖
        ≤ c ^ ((1 : ℝ) / 3) * (‖∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_sad τ‖ +
            ‖∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.rpow_nonneg hc0.le _)
      _ = c ^ ((1 : ℝ) / 3) * ‖∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_sad τ‖ +
          c ^ ((1 : ℝ) / 3) * ‖∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * h_ns τ‖ := by ring
      _ ≤ C_sadL * S ^ (-α - 1) + C_tailL * S ^ (-α - 1) := add_le_add hSadL hTailL
      _ = (C_sadL + C_tailL) * S ^ (-α - 1) := by ring
  calc ‖(∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_in u) +
          ∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_out u‖
      ≤ ‖∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_in u‖ +
        ‖∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_out u‖ := norm_add_le _ _
    _ ≤ C_in * S ^ (-α - 1) + (C_sadL + C_tailL) * S ^ (-α - 1) := add_le_add hIn hOut
    _ = (C_in + C_sadL + C_tailL) * S ^ (-α - 1) := by ring


end FormalResearch.SignUncertainty.FctCuspEdge
