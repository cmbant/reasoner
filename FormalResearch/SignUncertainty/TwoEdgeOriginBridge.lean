module

public import FormalResearch.SignUncertainty.TwoEdgeOriginRem

/-!
# Two-edge origin Mellin bridge (`cepe:PE3` / `ce_o1_pre_edge.tex`)

* `pe3OriginData_of_twoEdge`: constructs `PE3OriginData fhat (Icc 0 Δ₁)` for a two-edge
  pair `(S_c, D_c)` with `D_c` in a bounded finite-dimensional subspace of `ℛ_Ai^gen`,
  `D_c ≤ 0` on `(-∞, w_cut]` (`w_cut ≤ 0`), `‖W_{S_c}‖ ≤ C_S` on `{Re w ≥ 0}`, and
  `W_{S_c}(c^{1/3}) + W_{D_c}(0) ≥ b_J ε`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- **Origin Mellin representation (`PE3OriginData`) for any bounded finite-dimensional two-edge pair `(S_c, D_c)`.** -/
theorem pe3OriginData_of_twoEdge {ι : Type*} (s : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
    (hB : ∀ i ∈ s, HasGenRationalAiryCoeffs (B i) (b₀₀ i) (b₁₁ i))
    (α : ι → ℝ → ℝ) {R c_min w_cut b_J C_S C_δ Δ₁ : ℝ}
    (hR : 0 ≤ R) (hc_min : 4 ≤ c_min) (hw_cut : w_cut ≤ 0) (hb_J : 0 < b_J)
    (hCS : 0 ≤ C_S) (hCδ : 0 ≤ C_δ) (hΔ₁ : 0 < Δ₁)
    (m : ℕ) (hm : 1 ≤ m) (δ₀ : ℝ → ℝ)
    (hδ0 : ∀ {c : ℝ}, c_min ≤ c → 0 ≤ δ₀ c) (hδ_bd : ∀ {c : ℝ}, c_min ≤ c → δ₀ c ≤ C_δ * liftEps c)
    (S : ℝ → ℝ → ℝ) (hUS : ∀ {c : ℝ}, c_min ≤ c → HasU2 (S c))
    (hWS_bd : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 ≤ w.re → ‖liftSymbol (S c) (δ₀ c) m w‖ ≤ C_S)
    (D : ℝ → ℝ → ℝ) (hD_eq : ∀ {c u : ℝ}, D c u = ∑ i ∈ s, α i c * (B i (u : ℂ)).re)
    (hα : ∀ i ∈ s, ∀ c : ℝ, c_min ≤ c → |α i c| ≤ R)
    (hD_neg : ∀ {c u : ℝ}, c_min ≤ c → u ≤ w_cut → D c u ≤ 0)
    (hJ₀ : ∀ {c : ℝ}, c_min ≤ c →
      b_J * liftEps c ≤ (liftSymbol (S c) (δ₀ c) m (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) + liftSymbol (D c) (δ₀ c) m 0).re)
    (fhat : ℝ → ℝ → ℝ)
    (hfhat0 : ∀ {c : ℝ}, c_min ≤ c →
      fhat c 0 = (liftSymbol (S c) (δ₀ c) m (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) + liftSymbol (D c) (δ₀ c) m 0).re)
    (hfhat_pos : ∀ {c Δ : ℝ}, c_min ≤ c → 0 < Δ → Δ ≤ Δ₁ →
      fhat c Δ = admissLift c (fun ζ => liftSymbol (S c) (δ₀ c) m (ζ / (liftEps c : ℂ)) +
        liftSymbol (D c) (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ))) Δ) :
    Nonempty (PE3OriginData fhat (Icc 0 Δ₁)) := by
  classical
  have hcs0 : 0 < ceCs := ceCs_pos
  have hk0 : 0 < ceK := ceK_pos
  let c_min' : ℝ := max c_min 216
  have hc4' : 4 ≤ c_min' := hc_min.trans (le_max_left _ _)
  have h216' : 216 ≤ c_min' := le_max_right _ _
  have hc_min_le : ∀ {c : ℝ}, c_min' ≤ c → c_min ≤ c := fun hc => (le_max_left _ _).trans hc
  obtain ⟨db⟩ := twoEdge_dual_bounds s B b₀₀ b₁₁ hB α hR hw_cut m (fun c => δ₀ c)
    (fun hc => hδ0 (hc_min_le hc)) D hD_eq fun i hi c hc => hα i hi c (hc_min_le hc)
  let W_tilde : ℝ → ℂ → ℂ := fun c ζ =>
    liftSymbol (S c) (δ₀ c) m (ζ / (liftEps c : ℂ)) +
      liftSymbol (D c) (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ))
  let J₀ : ℝ → ℝ := fun c => (W_tilde c 1).re
  have hJ₀_eq : ∀ {c : ℝ}, c_min' ≤ c →
      J₀ c = (liftSymbol (S c) (δ₀ c) m (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) + liftSymbol (D c) (δ₀ c) m 0).re := by
    intro c hc
    have hc0 : 0 < c := by linarith
    have hε_inv : (liftEps c)⁻¹ = c ^ (1 / 3 : ℝ) := by
      unfold liftEps; rw [← Real.rpow_neg_one, ← Real.rpow_mul hc0.le]; norm_num
    have h1 : (1 : ℂ) / (liftEps c : ℂ) = (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) := by
      rw [one_div, ← Complex.ofReal_inv, hε_inv]
    dsimp [J₀, W_tilde]; rw [h1]; simp
  let g : ℝ → ℝ → ℝ := fun c X =>
    if -(liftEps c ^ 2 * w_cut) < X then
      ceK * (liftEps c ^ 3)⁻¹ * (-D c (-X / liftEps c ^ 2))
    else 0
  let C_ν : ℝ := ceK * db.C_neg
  have hC_ν : 0 ≤ C_ν := mul_nonneg hk0.le db.hC_neg
  have hg_meas : ∀ {c : ℝ}, c_min' ≤ c → AEMeasurable (g c) (volume.restrict (Ioi 0)) := fun {c} _ => by
    have hD_m : Continuous fun X : ℝ => ceK * (liftEps c ^ 3)⁻¹ * (-D c (-X / liftEps c ^ 2)) :=
      continuous_const.mul (db.hD_cont.comp (continuous_neg.div_const _)).neg
    exact (Measurable.ite (measurableSet_Ioi) hD_m.measurable measurable_const).aemeasurable.restrict
  have hg_nn : ∀ {c : ℝ}, c_min' ≤ c → ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g c X := fun {c} hc X _ => by
    dsimp [g]
    split_ifs with hX
    · have hc0 : 0 < c := by linarith
      have hε : 0 < liftEps c := liftEps_pos hc0
      have hε2 : 0 < liftEps c ^ 2 := pow_pos hε 2
      have hu : -X / liftEps c ^ 2 ≤ w_cut := by rw [div_le_iff₀ hε2]; linarith
      exact mul_nonneg (by positivity) (neg_nonneg.mpr (hD_neg (hc_min_le hc) hu))
    · exact le_rfl
  have hg_le : ∀ {c : ℝ}, c_min' ≤ c → ∀ X ∈ Ioi (0 : ℝ), g c X ≤ C_ν * X ^ (-(3 / 2 : ℝ)) := fun {c} hc X hX => by
    have hX0 : 0 < X := hX
    dsimp [g]
    split_ifs with hXw
    · have hc0 : 0 < c := by linarith
      have hε : 0 < liftEps c := liftEps_pos hc0
      have hu_neg : -X / liftEps c ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
      have hbd := db.hD_neg_bd hc hu_neg
      have hε2_rpow : (liftEps c ^ 2) ^ (3 / 2 : ℝ) = liftEps c ^ 3 := by
        rw [← Real.rpow_natCast (liftEps c) 2, ← Real.rpow_mul hε.le,
          show ((2 : ℕ) : ℝ) * (3 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hpow_eq : (1 + |-X / liftEps c ^ 2|) ^ (-(3 / 2 : ℝ)) ≤ liftEps c ^ 3 * X ^ (-(3 / 2 : ℝ)) := by
        have h2 : |-X / liftEps c ^ 2| = X / liftEps c ^ 2 := by rw [abs_of_nonpos hu_neg]; ring
        rw [h2]
        calc (1 + X / liftEps c ^ 2) ^ (-(3 / 2 : ℝ))
            ≤ (X / liftEps c ^ 2) ^ (-(3 / 2 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (div_pos hX0 (sq_pos_of_pos hε)) (by linarith) (by norm_num)
          _ = ((X / liftEps c ^ 2) ^ (3 / 2 : ℝ))⁻¹ := Real.rpow_neg (div_pos hX0 (sq_pos_of_pos hε)).le _
          _ = (X ^ (3 / 2 : ℝ) / (liftEps c ^ 2) ^ (3 / 2 : ℝ))⁻¹ := by
              rw [Real.div_rpow hX0.le (sq_nonneg _)]
          _ = liftEps c ^ 3 * X ^ (-(3 / 2 : ℝ)) := by
              rw [inv_div, hε2_rpow, Real.rpow_neg hX0.le, div_eq_mul_inv]
      have hneg_le : -D c (-X / liftEps c ^ 2) ≤ db.C_neg * (liftEps c ^ 3 * X ^ (-(3 / 2 : ℝ))) :=
        (neg_le_abs _).trans (hbd.trans (mul_le_mul_of_nonneg_left hpow_eq db.hC_neg))
      calc ceK * (liftEps c ^ 3)⁻¹ * (-D c (-X / liftEps c ^ 2))
          ≤ ceK * (liftEps c ^ 3)⁻¹ * (db.C_neg * (liftEps c ^ 3 * X ^ (-(3 / 2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left hneg_le (by positivity)
        _ = C_ν * X ^ (-(3 / 2 : ℝ)) := by dsimp [C_ν]; field_simp [hε.ne']
    · exact mul_nonneg hC_ν (Real.rpow_nonneg hX0.le _)
  let I_osc : ℝ → ℝ → ℂ := fun c y =>
    ((liftEps c : ℝ) : ℂ) * ∫ X in Ioi (0 : ℝ),
      (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ))))
        ∂(volume.withDensity fun X => ENNReal.ofReal (g c X))
  let R_c : ℝ → ℝ → ℂ := fun c y =>
    ceOriginG c (W_tilde c) y -
      (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) * I_osc c y
  let C_J : ℝ := C_S + db.C_D
  let C_B : ℝ := (2 * ceCs + 4) * C_ν
  have hCJ0 : 0 ≤ C_J := add_nonneg hCS db.hC_D.le
  have hCB0 : 0 ≤ C_B := by positivity
  obtain ⟨CH_pha, hCH_pha, hpha_bd⟩ := ceOrigin_phase_quad_bound
  let R_b : ℝ := ceCs * C_δ / (m : ℝ) + 1
  have hRb0 : 0 ≤ R_b := by positivity
  obtain ⟨Cm_unif, hCm_unif, hbm_unif⟩ := norm_bsplineE1_pow_sub_one_le m hRb0
  let C_err : ℝ := Real.exp (3 / 2 * CH_pha) * CH_pha * C_J + 2 * C_S +
    Cm_unif * (ceCs * C_δ / (m : ℝ)) * ceK * db.L1_D +
    ceK * (ceCs ^ 3 / 12 * Real.exp (ceCs ^ 3 / 96)) * db.L1_D + ceK * ceCs * db.M_mom + 1
  have hL10 := db.hL1_D; have hM0 := db.hM_mom
  have hCerr0 : 0 ≤ C_err := by positivity
  refine ⟨⟨c_min', b_J, C_ν, C_err, C_J, C_B, Δ₁, hc4', hb_J, hC_ν, hCerr0, hCJ0, hCB0,
    fun _ hΔ => hΔ, J₀, g, R_c, ?_, ?_, hg_meas, hg_nn, hg_le, ?_, ?_, ?_, ?_⟩⟩
  · intro c hc; rw [hJ₀_eq hc]; exact hJ₀ (hc_min_le hc)
  · intro c hc _; rw [hJ₀_eq hc]; exact hfhat0 (hc_min_le hc)
  · intro c hc
    have hc2 : 2 ≤ c := by linarith
    have hsm := twoEdge_W_tilde_stripM1 (m := m) (by linarith : 4 ≤ c) (hUS (hc_min_le hc)) db.hUD (hδ0 (hc_min_le hc))
    have hhol := twoEdge_W_tilde_holder s B b₀₀ b₁₁ hB α hR h216' m hm δ₀
      (fun hc' => hδ0 (hc_min_le hc')) S D (fun hc' => hUS (hc_min_le hc')) hD_eq
      (fun i hi c' hc' => hα i hi c' (hc_min_le hc')) db hc
    have hshift := ceOrigin_shift hc2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hsm hhol
    have h4c : Continuous fun y : ℝ => (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) := by
      have heq : (fun y : ℝ => (4 : ℂ) ^ (-(Complex.I * (y : ℂ)))) =
          fun y : ℝ => Complex.exp (-(Complex.I * (y : ℂ)) * ((Real.log 4 : ℝ) : ℂ)) := funext fun y => by
        rw [Complex.cpow_def_of_ne_zero (by norm_num),
          show Complex.log (4 : ℂ) = ((Real.log 4 : ℝ) : ℂ) by
            simpa using (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 4)).symm, mul_comm]
      rw [heq]; fun_prop
    have hGam : AEStronglyMeasurable (fun y : ℝ => Complex.Gamma (Complex.I * (y : ℂ))) volume := by
      rw [← MeasureTheory.restrict_compl_singleton (μ := volume) 0]
      refine ContinuousOn.aestronglyMeasurable (fun y hy => ?_) (measurableSet_singleton (0 : ℝ)).compl
      have hy0 := mem_compl_singleton_iff.mp hy
      have hcont_iy : Continuous fun y : ℝ => Complex.I * (y : ℂ) := by fun_prop
      exact ((Complex.differentiableAt_Gamma _ fun k hk => by
        have := congrArg Complex.im hk; simp [hy0] at this).continuousAt.comp
        hcont_iy.continuousAt).continuousWithinAt
    have hI_osc_cont : Continuous (I_osc c) := by
      refine continuous_const.mul ?_
      have hν_int : IntegrableOn (fun X : ℝ => min X 1) (Ioi 0) (volume.withDensity fun X => ENNReal.ofReal (g c X)) := by
        rw [IntegrableOn, restrict_withDensity measurableSet_Ioi,
          integrable_withDensity_iff_integrable_smul₀' (hg_meas hc).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        have h1 : IntegrableOn (fun X : ℝ => g c X * min X 1) (Ioc 0 1) := by
          have hle : ∀ X ∈ Ioc (0 : ℝ) 1, ‖g c X * min X 1‖ ≤ C_ν * X ^ (-(1 / 2 : ℝ)) := fun X hX => by
            rw [Real.norm_of_nonneg (mul_nonneg (hg_nn hc X hX.1) (le_min hX.1.le zero_le_one)), min_eq_left hX.2]
            calc g c X * X ≤ (C_ν * X ^ (-(3 / 2 : ℝ))) * X := mul_le_mul_of_nonneg_right (hg_le hc X hX.1) hX.1.le
              _ = C_ν * (X ^ (-(3 / 2 : ℝ)) * X ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
              _ = C_ν * X ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hX.1]; norm_num
          exact ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).1.const_mul C_ν).mono'
            (((hg_meas hc).aestronglyMeasurable.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)).mul
              (continuous_id.min continuous_const).aestronglyMeasurable.restrict)
            (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with X hX; exact hle X hX)
        have h2 : IntegrableOn (fun X : ℝ => g c X * min X 1) (Ioi 1) := by
          have hle : ∀ X ∈ Ioi (1 : ℝ), ‖g c X * min X 1‖ ≤ C_ν * X ^ (-(3 / 2 : ℝ)) := fun X hX => by
            have hX0 : 0 < X := lt_trans zero_lt_one hX
            rw [Real.norm_of_nonneg (mul_nonneg (hg_nn hc X hX0) (le_min hX0.le zero_le_one)), min_eq_right (mem_Ioi.mp hX).le, mul_one]
            exact hg_le hc X hX0
          exact ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) one_pos).const_mul C_ν).mono'
            (((hg_meas hc).aestronglyMeasurable.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl)).mul
              (continuous_id.min continuous_const).aestronglyMeasurable.restrict)
            (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX; exact hle X hX)
        change IntegrableOn (fun x => (ENNReal.ofReal (g c x)).toReal • min x 1) (Ioi 0) volume
        rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
        exact ⟨h1.congr_fun (fun X hX => by simp [smul_eq_mul, ENNReal.toReal_ofReal (hg_nn hc X hX.1)]) measurableSet_Ioc,
          h2.congr_fun (fun X hX => by simp [smul_eq_mul, ENNReal.toReal_ofReal (hg_nn hc X (lt_trans zero_lt_one hX))]) measurableSet_Ioi⟩
      refine continuous_iff_continuousAt.mpr fun y₀ =>
        continuousAt_of_dominated (bound := fun X : ℝ => max (ceCs * (|y₀| + 1)) 2 * min X 1)
          (Eventually.of_forall fun _ => (Continuous.aestronglyMeasurable (by fun_prop)).restrict)
          (by filter_upwards [Metric.ball_mem_nhds y₀ one_pos] with y hy
              have hy_abs : |y| ≤ |y₀| + 1 := by
                have h1 : ‖y - y₀‖ < 1 := Metric.mem_ball.mp hy; rw [Real.norm_eq_abs] at h1; linarith [abs_sub_abs_le_abs_sub y y₀]
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
              have hX0 : 0 < X := hX
              have hosc := norm_one_sub_exp_neg_le (v := Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)) (by simp)
              rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
                Real.norm_of_nonneg (mul_nonneg hcs0.le hX0.le), Real.norm_eq_abs] at hosc
              rcases le_or_gt X 1 with hX1 | hX1
              · rw [min_eq_left hX1]
                calc ‖1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))‖ ≤ ceCs * X * |y| :=
                      hosc.trans (min_le_left _ _)
                  _ = ceCs * |y| * X := by ring
                  _ ≤ max (ceCs * (|y₀| + 1)) 2 * X :=
                      mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_left hy_abs hcs0.le) (le_max_left _ _)) hX0.le
              · rw [min_eq_right hX1.le, mul_one]
                exact (hosc.trans (min_le_right _ _)).trans (le_max_right _ _))
          (hν_int.const_mul _) (ae_of_all _ fun _ => by fun_prop)
    exact hshift.1.aestronglyMeasurable.sub ((h4c.aestronglyMeasurable.mul hGam).mul hI_osc_cont.aestronglyMeasurable)
  · intro c y hc hy0 hy_le
    have h4n : ‖(4 : ℂ) ^ (-(Complex.I * (y : ℂ)))‖ = 1 := by
      have h4_eq : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_num
      rw [h4_eq, show -(Complex.I * (y : ℂ)) = ((-y : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), show (((-y : ℝ) : ℂ) * Complex.I).re = 0 by simp, Real.rpow_zero]
    have hR_eq : R_c c y = (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
        (ceOriginE c ((y : ℂ) * Complex.I) * W_tilde c (1 - ((y : ℂ) * Complex.I) / (c : ℂ)) - W_tilde c 1 - I_osc c y) := by
      dsimp [R_c, ceOriginG]
      rw [show (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) = (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) by congr 2; ring,
        show Complex.Gamma ((y : ℂ) * Complex.I) = Complex.Gamma (Complex.I * (y : ℂ)) by congr 1; ring]
      ring
    have hrem := twoEdge_Rem_lo_bound s B b₀₀ b₁₁ α h216' hCS hCδ hCH_pha hCm_unif m hm δ₀
      (fun hc' => hδ0 (hc_min_le hc')) (fun hc' => hδ_bd (hc_min_le hc')) S D
      (fun hc' => hUS (hc_min_le hc')) (fun {c'} {w} hc' hw => hWS_bd (hc_min_le hc') hw)
      db hpha_bd hbm_unif hc hy_le g (fun _ => rfl) (hg_meas hc) (hg_nn hc) hw_cut
    have hrem' : ‖ceOriginE c ((y : ℂ) * Complex.I) * W_tilde c (1 - ((y : ℂ) * Complex.I) / (c : ℂ)) - W_tilde c 1 - I_osc c y‖ ≤
        C_err * (c ^ (-(1 / 3 : ℝ))) ^ 2 * (|y| + |y| ^ 4) := by
      refine hrem.trans_eq ?_
      dsimp [C_err, C_J, liftEps]
    rw [hR_eq, norm_mul, norm_mul, h4n, one_mul, mul_comm Complex.I (y : ℂ)]
    exact mul_le_mul_of_nonneg_left hrem' (norm_nonneg _)
  · intro c y hc _
    have hc0 : 0 < c := by linarith
    have hε : 0 < liftEps c := liftEps_pos hc0
    have h4n : ‖(4 : ℂ) ^ (-(Complex.I * (y : ℂ)))‖ = 1 := by
      have h4_eq : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_num
      rw [h4_eq, show -(Complex.I * (y : ℂ)) = ((-y : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), show (((-y : ℝ) : ℂ) * Complex.I).re = 0 by simp, Real.rpow_zero]
    have hR_eq : R_c c y = (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
        (ceOriginE c ((y : ℂ) * Complex.I) * W_tilde c (1 - ((y : ℂ) * Complex.I) / (c : ℂ)) - W_tilde c 1 - I_osc c y) := by
      dsimp [R_c, ceOriginG]
      rw [show (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) = (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) by congr 2; ring,
        show Complex.Gamma ((y : ℂ) * Complex.I) = Complex.Gamma (Complex.I * (y : ℂ)) by congr 1; ring]
      ring
    have hWtilde_bd : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖W_tilde c ζ‖ ≤ C_J := fun ζ h0 h1 => by
      dsimp [W_tilde]
      have h1' : 0 ≤ (ζ / (liftEps c : ℂ)).re := by rw [Complex.div_ofReal_re]; exact div_nonneg h0 hε.le
      have h2' : 0 ≤ ((1 - ζ) / (liftEps c : ℂ)).re := by
        rw [Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]; exact div_nonneg (sub_nonneg.mpr h1) hε.le
      exact (norm_add_le _ _).trans (add_le_add (hWS_bd (hc_min_le hc) h1') (db.hWD_unif hc h2'))
    have hE_im : ‖ceOriginE c ((y : ℂ) * Complex.I)‖ = Real.exp (c * CohnElkies.hB (|y| / c)) := by
      rw [norm_ceOriginE_imag hc0 y]
      rcases le_or_gt 0 y with hy | hy
      · rw [abs_of_nonneg hy]
      · rw [abs_of_neg hy, neg_div, hB_neg_even]
    have hI_bd : ‖I_osc c y‖ ≤ c ^ (-(1 / 3 : ℝ)) * C_B * |y| ^ (1 / 2 : ℝ) := by
      have hz := pe3a_holder_bound hC_ν (hg_meas hc) (hg_nn hc) (hg_le hc) (z := (y : ℂ) * Complex.I) (by simp)
      rw [show ‖(y : ℂ) * Complex.I‖ = |y| by simp [Complex.norm_real]] at hz
      have hz' : ‖∫ X in Ioi (0 : ℝ), (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ))))
            ∂(volume.withDensity fun X => ENNReal.ofReal (g c X))‖ ≤ C_B * |y| ^ (1 / 2 : ℝ) := by
        refine hz.trans_eq' (congrArg norm (setIntegral_congr_fun measurableSet_Ioi fun X _ => ?_))
        congr 2; push_cast; ring
      dsimp [I_osc]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
      calc liftEps c * ‖∫ X in Ioi (0 : ℝ), _ ∂(volume.withDensity fun X => ENNReal.ofReal (g c X))‖
          ≤ liftEps c * (C_B * |y| ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hz' hε.le
        _ = c ^ (-(1 / 3 : ℝ)) * C_B * |y| ^ (1 / 2 : ℝ) := by unfold liftEps; ring
    have h1y : 0 ≤ (1 - ((y : ℂ) * Complex.I) / (c : ℂ)).re ∧ (1 - ((y : ℂ) * Complex.I) / (c : ℂ)).re ≤ 1 := by
      simp [Complex.div_ofReal_re]
    rw [hR_eq, norm_mul, norm_mul, h4n, one_mul, mul_comm Complex.I (y : ℂ)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖ceOriginE c ((y : ℂ) * Complex.I) * W_tilde c (1 - ((y : ℂ) * Complex.I) / (c : ℂ)) - W_tilde c 1 - I_osc c y‖
        ≤ ‖ceOriginE c ((y : ℂ) * Complex.I) * W_tilde c (1 - ((y : ℂ) * Complex.I) / (c : ℂ))‖ + ‖W_tilde c 1‖ + ‖I_osc c y‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ Real.exp (c * CohnElkies.hB (|y| / c)) * C_J + C_J + c ^ (-(1 / 3 : ℝ)) * C_B * |y| ^ (1 / 2 : ℝ) := by
          refine add_le_add (add_le_add ?_ (hWtilde_bd 1 zero_le_one le_rfl)) hI_bd
          rw [norm_mul, hE_im]
          exact mul_le_mul_of_nonneg_left (hWtilde_bd _ h1y.1 h1y.2) (Real.exp_pos _).le
  · intro c Δ hc hΔ hΔ0
    have hc2 : 2 ≤ c := by linarith
    have hsm := twoEdge_W_tilde_stripM1 (m := m) (by linarith : 4 ≤ c) (hUS (hc_min_le hc)) db.hUD (hδ0 (hc_min_le hc))
    have hhol := twoEdge_W_tilde_holder s B b₀₀ b₁₁ hB α hR h216' m hm δ₀
      (fun hc' => hδ0 (hc_min_le hc')) S D (fun hc' => hUS (hc_min_le hc')) hD_eq
      (fun i hi c' hc' => hα i hi c' (hc_min_le hc')) db hc
    have hshift := ceOrigin_shift hc2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hsm hhol
    have hfhat_eq : fhat c Δ = admissLift c (W_tilde c) Δ := hfhat_pos (hc_min_le hc) hΔ0 hΔ.2
    have hW1_real : W_tilde c 1 = (J₀ c : ℂ) := by
      have hconj := hsm.real 1 zero_le_one le_rfl
      rw [map_one] at hconj
      exact Complex.ext rfl (Complex.conj_eq_iff_im.mp hconj.symm)
    rw [hfhat_eq]
    have hshiftΔ : ((admissLift c (W_tilde c) Δ : ℝ) : ℂ) - W_tilde c 1 * ((Real.exp (-(4 * Δ)) : ℝ) : ℂ) =
        ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, ceOriginG c (W_tilde c) y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) :=
      hshift.2 hΔ0
    rw [hW1_real] at hshiftΔ
    have h_diff : ((admissLift c (W_tilde c) Δ - J₀ c * Real.exp (-4 * Δ) : ℝ) : ℂ) =
        ((admissLift c (W_tilde c) Δ : ℝ) : ℂ) - (J₀ c : ℂ) * ((Real.exp (-(4 * Δ)) : ℝ) : ℂ) := by
      rw [show (-4 * Δ : ℝ) = -(4 * Δ) by ring]; push_cast; ring
    rw [h_diff, hshiftΔ]
    congr 1
    · push_cast; ring
    · refine integral_congr_ae (ae_of_all _ fun y => ?_)
      dsimp only [R_c, I_osc, ceOriginG, liftEps]
      rw [show (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) = (Δ : ℂ) ^ (-(Complex.I * (y : ℂ))) by congr 2; ring]
      ring

/-- info: 'FormalResearch.SignUncertainty.pe3OriginData_of_twoEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pe3OriginData_of_twoEdge

end FormalResearch.SignUncertainty
