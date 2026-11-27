module

public import FormalResearch.SignUncertainty.TwoEdgeOriginHelpers

/-!
# Oscillatory remainder estimates for the two-edge origin Mellin bridge (`cepe:PE3`)
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

private lemma sq_le_abs_add_pow4 (y : ℝ) : y ^ 2 ≤ |y| + |y| ^ 4 := by
  rw [← sq_abs y]
  rcases le_or_gt |y| 1 with h | h
  · have h1 : |y| ^ 2 ≤ |y| * 1 := by
      rw [pow_two]; exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    linarith [pow_nonneg (abs_nonneg y) 4]
  · have h1 : |y| ^ 2 ≤ |y| ^ 4 := pow_le_pow_right₀ h.le (by norm_num : 2 ≤ 4)
    linarith [abs_nonneg y]

private lemma abs_cube_le_abs_add_pow4 (y : ℝ) : |y| ^ 3 ≤ |y| + |y| ^ 4 := by
  rcases le_or_gt |y| 1 with h | h
  · have h1 : |y| ^ 3 ≤ |y| ^ 1 := pow_le_pow_of_le_one (abs_nonneg _) h (by norm_num)
    rw [pow_one] at h1
    linarith [pow_nonneg (abs_nonneg y) 4]
  · have h1 : |y| ^ 3 ≤ |y| ^ 4 := pow_le_pow_right₀ h.le (by norm_num : 3 ≤ 4)
    linarith [abs_nonneg y]

/-- Exact identity rewriting the oscillatory tail `I_osc` in terms of `D c` on `(-∞, w_cut)`. -/
lemma twoEdge_I_osc_eq {w_cut c y : ℝ} (hw_cut : w_cut ≤ 0) (hc0 : 0 < c)
    (D : ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (hg_def : ∀ X, g c X = if -(liftEps c ^ 2 * w_cut) < X then ceK * (liftEps c ^ 3)⁻¹ * (-D c (-X / liftEps c ^ 2)) else 0)
    (hg_meas : AEMeasurable (g c) (volume.restrict (Ioi 0)))
    (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g c X) :
    ((liftEps c : ℝ) : ℂ) * ∫ X in Ioi (0 : ℝ),
        (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ))))
          ∂(volume.withDensity fun X => ENNReal.ofReal (g c X)) =
      (ceK : ℂ) * ∫ u in Iio w_cut, (D c u : ℂ) *
        (Complex.exp (Complex.I * ((ceCs * (liftEps c ^ 2 * y) : ℝ) : ℂ) * (u : ℂ)) - 1) := by
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hε2_pos : 0 < liftEps c ^ 2 := pow_pos hε 2
  set v : ℝ := liftEps c ^ 2 * y
  have hg_eq : ∫ X in Ioi (0 : ℝ),
        (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ))))
          ∂(volume.withDensity fun X => ENNReal.ofReal (g c X)) =
      ∫ X in Ioi (0 : ℝ), (g c X : ℂ) * (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) := by
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hg_meas.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    · refine setIntegral_congr_fun measurableSet_Ioi fun X hX => ?_
      rw [ENNReal.toReal_ofReal (hg_nn X hX), Complex.real_smul]
    · exact measurableSet_Ioi
  have h_ite_eq : ∫ X in Ioi (0 : ℝ), (g c X : ℂ) * (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) =
      ∫ X in Ioi (-(liftEps c ^ 2 * w_cut)),
        ((ceK * (liftEps c ^ 3)⁻¹ * (-D c (-X / liftEps c ^ 2)) : ℝ) : ℂ) *
          (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun X => ?_)
    by_cases hX : -(liftEps c ^ 2 * w_cut) < X
    · have hX0 : 0 < X := lt_of_le_of_lt (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hw_cut)) hX
      simp [hg_def X, hX, hX0]
    · simp [hg_def X, hX]
  have hsc := integral_comp_mul_left_Ioi
    (fun X : ℝ => ((ceK * (liftEps c ^ 3)⁻¹ * (-D c (-X / liftEps c ^ 2)) : ℝ) : ℂ) *
      (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ))))) (-w_cut) hε2_pos
  have hm0' : liftEps c ^ 2 * (-w_cut) = -(liftEps c ^ 2 * w_cut) := by ring
  rw [hm0'] at hsc
  have h_in : ∫ x in Ioi (-w_cut),
        ((ceK * (liftEps c ^ 3)⁻¹ * (-D c (-(liftEps c ^ 2 * x) / liftEps c ^ 2)) : ℝ) : ℂ) *
          (1 - Complex.exp (-(Complex.I * ((ceCs * (liftEps c ^ 2 * x) : ℝ) : ℂ) * (y : ℂ)))) =
      ∫ t in Ioi (-w_cut),
        ((ceK * (liftEps c ^ 3)⁻¹ * (-D c (-t)) : ℝ) : ℂ) *
          (1 - Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * ((-t : ℝ) : ℂ))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have h1 : -(liftEps c ^ 2 * t) / liftEps c ^ 2 = -t := by field_simp [hε.ne']
    have h2 : -(Complex.I * ((ceCs * (liftEps c ^ 2 * t) : ℝ) : ℂ) * (y : ℂ)) =
        Complex.I * ((ceCs * v : ℝ) : ℂ) * ((-t : ℝ) : ℂ) := by
      dsimp [v]; push_cast; ring
    rw [h1, h2]
  have hscale : ∫ X in Ioi (-(liftEps c ^ 2 * w_cut)),
        ((ceK * (liftEps c ^ 3)⁻¹ * (-D c (-X / liftEps c ^ 2)) : ℝ) : ℂ) *
          (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) =
      ((liftEps c ^ 2 : ℝ) : ℂ) * ∫ t in Ioi (-w_cut),
        ((ceK * (liftEps c ^ 3)⁻¹ * (-D c (-t)) : ℝ) : ℂ) *
          (1 - Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * ((-t : ℝ) : ℂ))) := by
    calc ∫ X in Ioi (-(liftEps c ^ 2 * w_cut)), _
        = ((liftEps c ^ 2 : ℝ) : ℂ) * (((liftEps c ^ 2)⁻¹ : ℝ) • ∫ X in Ioi (-(liftEps c ^ 2 * w_cut)), _) := by
          rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hε2_pos.ne',
            Complex.ofReal_one, one_mul]
      _ = ((liftEps c ^ 2 : ℝ) : ℂ) * ∫ x in Ioi (-w_cut), _ := by rw [hsc]
      _ = _ := by rw [h_in]
  have hneg_sub : ∫ t in Ioi (-w_cut),
        ((ceK * (liftEps c ^ 3)⁻¹ * (-D c (-t)) : ℝ) : ℂ) *
          (1 - Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * ((-t : ℝ) : ℂ))) =
      ∫ u in Iio w_cut,
        ((ceK * (liftEps c ^ 3)⁻¹ * (-D c u) : ℝ) : ℂ) *
          (1 - Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ))) := by
    have h_n := integral_comp_neg_Ioi (-w_cut)
      (fun u : ℝ => ((ceK * (liftEps c ^ 3)⁻¹ * (-D c u) : ℝ) : ℂ) *
        (1 - Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ))))
    rw [neg_neg, ← setIntegral_congr_set Iio_ae_eq_Iic] at h_n
    exact h_n
  rw [hg_eq, h_ite_eq, hscale, hneg_sub, ← integral_const_mul, ← integral_const_mul]
  calc ∫ u in Iio w_cut, ((liftEps c : ℝ) : ℂ) * (((liftEps c ^ 2 : ℝ) : ℂ) *
          (((ceK * (liftEps c ^ 3)⁻¹ * (-D c u) : ℝ) : ℂ) *
            (1 - Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)))))
      = ∫ u in Iio w_cut, (ceK : ℂ) * ((D c u : ℂ) *
          (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1)) := by
        refine setIntegral_congr_fun measurableSet_Iio fun u _ => ?_
        have hcoeff : (liftEps c : ℂ) * ((liftEps c ^ 2 : ℝ) : ℂ) *
            ((ceK * (liftEps c ^ 3)⁻¹ * (-D c u) : ℝ) : ℂ) = -((ceK : ℂ) * (D c u : ℂ)) := by
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
          congr 1; field_simp [hε.ne']
        rw [← mul_assoc, ← mul_assoc, hcoeff]
        ring
    _ = (ceK : ℂ) * ∫ u in Iio w_cut, (D c u : ℂ) *
          (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1) := by
        rw [integral_const_mul]

/-- Five-term low-frequency remainder bound `‖Rem c y‖ ≤ C_err * ε^2 * (|y| + |y|^4)` for
`|y| ≤ (8/π) log(c^{1/3})`. -/
lemma twoEdge_Rem_lo_bound {ι : Type*} (s : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
    (α : ι → ℝ → ℝ) {c_min w_cut C_S C_δ CH_pha Cm_unif : ℝ} (hc216 : 216 ≤ c_min)
    (hCS : 0 ≤ C_S) (hCδ : 0 ≤ C_δ) (hCH_pha : 0 < CH_pha) (hCm_unif : 0 ≤ Cm_unif)
    (m : ℕ) (hm : 1 ≤ m) (δ₀ : ℝ → ℝ)
    (hδ0 : ∀ {c : ℝ}, c_min ≤ c → 0 ≤ δ₀ c) (hδ_bd : ∀ {c : ℝ}, c_min ≤ c → δ₀ c ≤ C_δ * liftEps c)
    (S D : ℝ → ℝ → ℝ) (hUS : ∀ {c : ℝ}, c_min ≤ c → HasU2 (S c))
    (hWS_bd : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 ≤ w.re → ‖liftSymbol (S c) (δ₀ c) m w‖ ≤ C_S)
    (db : TwoEdgeDualBounds s B b₀₀ b₁₁ α D δ₀ m w_cut c_min)
    (hpha_bd : ∀ {c : ℝ}, 0 < c → ∀ {z : ℂ}, 0 ≤ z.re → ‖z‖ ≤ c / 2 →
      ‖(c : ℂ) * stripH (z / (c : ℂ)) - z * ((Real.log (Real.pi / 2) : ℝ) : ℂ)‖ ≤ CH_pha * ‖z‖ ^ 2 / c)
    (hbm_unif : ∀ z : ℂ, ‖z‖ ≤ ceCs * C_δ / (m : ℝ) + 1 → ‖bsplineE1 z ^ m - 1‖ ≤ Cm_unif * ‖z‖)
    {c y : ℝ} (hc : c_min ≤ c) (hy_le : |y| ≤ 8 / π * Real.log (c ^ (1 / 3 : ℝ)))
    (g : ℝ → ℝ → ℝ)
    (hg_def : ∀ X, g c X = if -(liftEps c ^ 2 * w_cut) < X then ceK * (liftEps c ^ 3)⁻¹ * (-D c (-X / liftEps c ^ 2)) else 0)
    (hg_meas : AEMeasurable (g c) (volume.restrict (Ioi 0)))
    (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g c X) (hw_cut : w_cut ≤ 0) :
    ‖ceOriginE c ((y : ℂ) * Complex.I) *
        (liftSymbol (S c) (δ₀ c) m ((1 - ((y : ℂ) * Complex.I) / (c : ℂ)) / (liftEps c : ℂ)) +
          liftSymbol (D c) (δ₀ c) m ((1 - (1 - ((y : ℂ) * Complex.I) / (c : ℂ))) / (liftEps c : ℂ))) -
        (liftSymbol (S c) (δ₀ c) m ((1 : ℂ) / (liftEps c : ℂ)) +
          liftSymbol (D c) (δ₀ c) m ((1 - (1 : ℂ)) / (liftEps c : ℂ))) -
        ((liftEps c : ℝ) : ℂ) * ∫ X in Ioi (0 : ℝ),
          (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ))))
            ∂(volume.withDensity fun X => ENNReal.ofReal (g c X))‖ ≤
      (Real.exp (3 / 2 * CH_pha) * CH_pha * (C_S + db.C_D) + 2 * C_S +
        Cm_unif * (ceCs * C_δ / (m : ℝ)) * ceK * db.L1_D +
        ceK * (ceCs ^ 3 / 12 * Real.exp (ceCs ^ 3 / 96)) * db.L1_D + ceK * ceCs * db.M_mom + 1) *
        (liftEps c) ^ 2 * (|y| + |y| ^ 4) := by
  have hcs0 : 0 < ceCs := ceCs_pos
  have hk0 : 0 < ceK := ceK_pos
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc0 : 0 < c := by linarith
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hδ0' := hδ0 hc
  have hL10 := db.hL1_D
  have hM0 := db.hM_mom
  have hCD0 := db.hC_D.le
  have hc13_ge : 6 ≤ c ^ (1 / 3 : ℝ) := by
    have h6 : (6 : ℝ) ^ 3 ≤ c := by linarith
    rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact (Real.pow_rpow_inv_natCast (by positivity) (by norm_num : 3 ≠ 0)).symm.le.trans
      (Real.rpow_le_rpow (by positivity) h6 (by norm_num))
  have hε_le : liftEps c ≤ 1 / 6 := by
    rw [show liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ by unfold liftEps; rw [Real.rpow_neg hc0.le]]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hlog_le : Real.log (c ^ (1 / 3 : ℝ)) ≤ c ^ (1 / 3 : ℝ) :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hy_c13 : |y| ≤ 3 * c ^ (1 / 3 : ℝ) := by
    have h8pi : 8 / π ≤ 3 := by rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    calc |y| ≤ (8 / π) * Real.log (c ^ (1 / 3 : ℝ)) := hy_le
      _ ≤ 3 * c ^ (1 / 3 : ℝ) := mul_le_mul h8pi hlog_le (Real.log_nonneg (by linarith)) (by positivity)
  have hy_c2 : |y| ≤ c / 2 := by
    have hc23 : c = c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
    have h36 : 6 ≤ c ^ (2 / 3 : ℝ) := by
      calc (6 : ℝ) ≤ 6 * 6 := by norm_num
        _ ≤ c ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) := mul_le_mul hc13_ge hc13_ge (by norm_num) (by positivity)
        _ = c ^ (2 / 3 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
    rw [hc23]; nlinarith
  have hy2_c : y ^ 2 / c ≤ 3 / 2 := by
    have hcube : c = (c ^ (1 / 3 : ℝ)) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hy2 : y ^ 2 ≤ 9 * (c ^ (1 / 3 : ℝ)) ^ 2 := by
      rw [← sq_abs y]
      exact (pow_le_pow_left₀ (abs_nonneg _) hy_c13 2).trans_eq (by ring)
    calc y ^ 2 / c ≤ 9 * (c ^ (1 / 3 : ℝ)) ^ 2 / (c ^ (1 / 3 : ℝ)) ^ 3 := by rw [← hcube]; gcongr
      _ = 9 / c ^ (1 / 3 : ℝ) := by field_simp [(by linarith : 0 < c ^ (1 / 3 : ℝ)).ne']
      _ ≤ 9 / 6 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc13_ge
      _ = 3 / 2 := by norm_num
  set v : ℝ := liftEps c ^ 2 * y
  have hv_abs : |v| = liftEps c ^ 2 * |y| := by rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hv_half : |v| ≤ 1 / 2 := by
    have hc23_inv : liftEps c ^ 2 * c ^ (1 / 3 : ℝ) = liftEps c := by
      unfold liftEps
      rw [← Real.rpow_natCast (c ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
    calc |v| = liftEps c ^ 2 * |y| := hv_abs
      _ ≤ liftEps c ^ 2 * (3 * c ^ (1 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hy_c13 (sq_nonneg _)
      _ = 3 * (liftEps c ^ 2 * c ^ (1 / 3 : ℝ)) := by ring
      _ = 3 * liftEps c := by rw [hc23_inv]
      _ ≤ 1 / 2 := by linarith
  have hc_prod1 : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc0
  have hε_inv : (liftEps c)⁻¹ = c ^ (1 / 3 : ℝ) := by
    unfold liftEps; rw [← Real.rpow_neg_one, ← Real.rpow_mul hc0.le]; norm_num
  have h_inv_eq : (c * liftEps c)⁻¹ * y = liftEps c ^ 2 * y := by
    calc (c * liftEps c)⁻¹ * y = (c * liftEps c)⁻¹ * (liftEps c ^ 3 * c) * y := by rw [hc_prod1, mul_one]
      _ = liftEps c ^ 2 * y := by field_simp [hc0.ne', hε.ne']
  have h_W1_arg : (1 - ((y : ℂ) * Complex.I) / (c : ℂ)) / (liftEps c : ℂ) =
      (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)) - (v : ℂ) * Complex.I := by
    rw [sub_div, one_div, ← Complex.ofReal_inv, hε_inv]
    congr 1
    dsimp [v]
    calc ((y : ℂ) * Complex.I / (c : ℂ)) / (liftEps c : ℂ)
        = (((c : ℂ) * (liftEps c : ℂ))⁻¹ * (y : ℂ)) * Complex.I := by ring
      _ = (((c * liftEps c)⁻¹ * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
      _ = (((liftEps c ^ 2 * y : ℝ)) : ℂ) * Complex.I := by rw [h_inv_eq]
  have h_W2_arg : (1 - (1 - ((y : ℂ) * Complex.I) / (c : ℂ))) / (liftEps c : ℂ) = (v : ℂ) * Complex.I := by
    rw [sub_sub_cancel]; dsimp [v]
    calc ((y : ℂ) * Complex.I / (c : ℂ)) / (liftEps c : ℂ)
        = (((c * liftEps c)⁻¹ * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
      _ = (((liftEps c ^ 2 * y : ℝ)) : ℂ) * Complex.I := by rw [h_inv_eq]
  have hE_sub : ‖ceOriginE c ((y : ℂ) * Complex.I) - 1‖ ≤ Real.exp (3 / 2 * CH_pha) * CH_pha * (y ^ 2 / c) := by
    have hz0 : 0 ≤ ((y : ℂ) * Complex.I).re := by simp
    have hzn : ‖(y : ℂ) * Complex.I‖ = |y| := by simp [Complex.norm_real]
    have hph := hpha_bd hc0 hz0 (hzn.symm ▸ hy_c2)
    rw [hzn, sq_abs] at hph
    have hph_bd : ‖(c : ℂ) * stripH (((y : ℂ) * Complex.I) / (c : ℂ)) -
        (y : ℂ) * Complex.I * ((Real.log (Real.pi / 2) : ℝ) : ℂ)‖ ≤ 3 / 2 * CH_pha := by
      calc _ ≤ CH_pha * y ^ 2 / c := hph
        _ = CH_pha * (y ^ 2 / c) := by ring
        _ ≤ CH_pha * (3 / 2) := mul_le_mul_of_nonneg_left hy2_c hCH_pha.le
        _ = 3 / 2 * CH_pha := by ring
    unfold ceOriginE
    refine norm_exp_sub_one_le_mul.trans ?_
    calc ‖_‖ * Real.exp ‖_‖
        ≤ (CH_pha * y ^ 2 / c) * Real.exp (3 / 2 * CH_pha) :=
          mul_le_mul hph (Real.exp_le_exp.mpr hph_bd) (Real.exp_pos _).le (by positivity)
      _ = Real.exp (3 / 2 * CH_pha) * CH_pha * (y ^ 2 / c) := by ring
  have hWtilde_bd : ‖liftSymbol (S c) (δ₀ c) m ((1 - ((y : ℂ) * Complex.I) / (c : ℂ)) / (liftEps c : ℂ)) +
        liftSymbol (D c) (δ₀ c) m ((1 - (1 - ((y : ℂ) * Complex.I) / (c : ℂ))) / (liftEps c : ℂ))‖ ≤ C_S + db.C_D := by
    rw [h_W1_arg, h_W2_arg]
    exact (norm_add_le _ _).trans (add_le_add (hWS_bd hc (by simp; positivity)) (db.hWD_unif hc (by simp)))
  have hWS_sub : ‖liftSymbol (S c) (δ₀ c) m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) - (v : ℂ) * Complex.I) -
        liftSymbol (S c) (δ₀ c) m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ))‖ ≤ 2 * C_S * |v| := by
    have hSdata := liftSymbolData_of_hasU2 (hUS hc) hδ0' m
    let x₀ : ℂ := ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)
    have hball : Metric.closedBall x₀ (1 / 2) ⊆ {w : ℂ | 0 < w.re} := fun w hw => by
      have hre : |w.re - c ^ (1 / 3 : ℝ)| ≤ 1 / 2 :=
        (by simp [x₀] : |w.re - c ^ (1 / 3 : ℝ)| = |(w - x₀).re|) ▸
          (Complex.abs_re_le_norm _).trans (mem_closedBall_iff_norm.mp hw)
      change 0 < w.re; linarith [(abs_le.mp hre).1]
    have hderiv : ∀ z₀ ∈ Metric.closedBall x₀ (1 / 2), ‖deriv (liftSymbol (S c) (δ₀ c) m) z₀‖ ≤ 2 * C_S := by
      intro z₀ hz₀
      have hcl : Metric.closedBall z₀ (1 / 2) ⊆ {w : ℂ | 0 < w.re} := fun ζ hζ => by
        have h1 : ‖ζ - x₀‖ ≤ 1 := by
          calc ‖ζ - x₀‖ = ‖(ζ - z₀) + (z₀ - x₀)‖ := by ring_nf
            _ ≤ ‖ζ - z₀‖ + ‖z₀ - x₀‖ := norm_add_le _ _
            _ ≤ 1 / 2 + 1 / 2 := add_le_add (mem_closedBall_iff_norm.mp hζ) (mem_closedBall_iff_norm.mp hz₀)
            _ = 1 := by ring
        have hre : |ζ.re - c ^ (1 / 3 : ℝ)| ≤ 1 :=
          (by simp [x₀] : |ζ.re - c ^ (1 / 3 : ℝ)| = |(ζ - x₀).re|) ▸ (Complex.abs_re_le_norm _).trans h1
        change 0 < ζ.re; linarith [(abs_le.mp hre).1]
      exact (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 2)
        ⟨hSdata.diff.mono (Metric.ball_subset_closedBall.trans hcl),
          by rw [closure_ball z₀ (by norm_num)]; exact hSdata.diff.continuousOn.mono hcl⟩
        fun ζ hζ => hWS_bd hc (le_of_lt (hcl (Metric.sphere_subset_closedBall hζ)))).trans_eq (by ring)
    have hpt1 : x₀ ∈ Metric.closedBall x₀ (1 / 2) := Metric.mem_closedBall_self (by norm_num)
    have hpt2 : x₀ - (v : ℂ) * Complex.I ∈ Metric.closedBall x₀ (1 / 2) := by
      rw [mem_closedBall_iff_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, mul_one]; exact hv_half
    have hmv := (convex_closedBall x₀ (1 / 2)).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hSdata.diff z (hball hz)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hball hz)))
      hderiv hpt1 hpt2
    dsimp [x₀] at hmv
    rw [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hmv
    exact hmv
  have hmult_sub : ‖liftMultiplier (δ₀ c) m ((v : ℂ) * Complex.I) - 1‖ ≤
      Cm_unif * (ceCs * C_δ / (m : ℝ)) * (liftEps c * |v|) := by
    unfold liftMultiplier
    have harg_le : ‖(((ceCs * δ₀ c / (m : ℝ) : ℝ) : ℂ) * ((v : ℂ) * Complex.I))‖ ≤ ceCs * C_δ / (m : ℝ) + 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, mul_one]
      have h1 : δ₀ c ≤ C_δ * liftEps c := hδ_bd hc
      calc ceCs * δ₀ c / (m : ℝ) * |v| ≤ ceCs * C_δ / (m : ℝ) * 1 := by
            gcongr
            · exact h1.trans (mul_le_of_le_one_right hCδ (hε_le.trans (by norm_num)))
            · linarith
        _ = ceCs * C_δ / (m : ℝ) := by ring
        _ ≤ ceCs * C_δ / (m : ℝ) + 1 := by linarith
    calc ‖bsplineE1 (((ceCs * δ₀ c / (m : ℝ) : ℝ) : ℂ) * ((v : ℂ) * Complex.I)) ^ m - 1‖
        ≤ Cm_unif * (ceCs * δ₀ c / (m : ℝ) * |v|) := by
          refine (hbm_unif _ harg_le).trans_eq ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
            Real.norm_eq_abs, Complex.norm_I, mul_one]
      _ ≤ Cm_unif * (ceCs * (C_δ * liftEps c) / (m : ℝ) * |v|) := by have := hδ_bd hc; gcongr
      _ = Cm_unif * (ceCs * C_δ / (m : ℝ)) * (liftEps c * |v|) := by ring
  have hcub_sub : ‖Complex.exp (-(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12) - 1‖ ≤
      (ceCs ^ 3 / 12 * Real.exp (ceCs ^ 3 / 96)) * |v| ^ 3 := by
    have harg : ‖-(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12‖ = ceCs ^ 3 / 12 * |v| ^ 3 := by
      rw [norm_div, norm_neg, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcs0.le,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
        show ‖(12 : ℂ)‖ = 12 by norm_num, mul_pow]; ring
    have harg_le : ‖-(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12‖ ≤ ceCs ^ 3 / 96 := by
      rw [harg]; calc ceCs ^ 3 / 12 * |v| ^ 3 ≤ ceCs ^ 3 / 12 * (1 / 2) ^ 3 := by gcongr
        _ = ceCs ^ 3 / 96 := by ring
    refine norm_exp_sub_one_le_mul.trans ?_
    rw [harg]
    calc (ceCs ^ 3 / 12 * |v| ^ 3) * Real.exp (ceCs ^ 3 / 12 * |v| ^ 3)
        ≤ (ceCs ^ 3 / 12 * |v| ^ 3) * Real.exp (ceCs ^ 3 / 96) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (harg.symm ▸ harg_le)) (by positivity)
      _ = (ceCs ^ 3 / 12 * Real.exp (ceCs ^ 3 / 96)) * |v| ^ 3 := by ring
  have hD_split_int : ∫ u : ℝ, (D c u : ℂ) * (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1) =
      (∫ u in Iio w_cut, (D c u : ℂ) * (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1)) +
        (∫ u in Ici w_cut, (D c u : ℂ) * (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1)) := by
    have hint_sub : Integrable (fun u : ℝ => (D c u : ℂ) * (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1)) := by
      refine ((db.hD_L1_int (c := c)).const_mul 2).mono' ((Complex.continuous_ofReal.comp db.hD_cont).aestronglyMeasurable.mul
        (Continuous.aestronglyMeasurable (by fun_prop))) (ae_of_all _ fun u => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hosc : ‖Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1‖ ≤ 2 := by
        have heq : Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ) = -((-(((ceCs * v * u : ℝ) : ℂ)) * Complex.I)) := by
          push_cast; ring
        have h1 := norm_one_sub_exp_neg_le (v := (-(((ceCs * v * u : ℝ) : ℂ)) * Complex.I)) (by simp)
        rw [norm_sub_rev, ← heq] at h1
        exact h1.trans (min_le_right _ _)
      exact (mul_le_mul_of_nonneg_left hosc (abs_nonneg _)).trans_eq (by ring)
    rw [← setIntegral_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici hint_sub.integrableOn hint_sub.integrableOn,
      Iio_union_Ici, setIntegral_univ]
  have hD_lap_eq : airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) - airyTwistedLaplaceC (D c) 0 =
      (ceK : ℂ) * (Complex.exp (-(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12) - 1) *
        (∫ u : ℝ, (D c u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ))) +
        (ceK : ℂ) * ∫ u : ℝ, (D c u : ℂ) * (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1) := by
    have hint_1 : Integrable (fun u : ℝ => (D c u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ))) := by
      refine (db.hD_L1_int (c := c)).mono' ((Complex.continuous_ofReal.comp db.hD_cont).aestronglyMeasurable.mul
        (Continuous.aestronglyMeasurable (by fun_prop))) (ae_of_all _ fun u => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
        show (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ)).re = 0 by simp, Real.exp_zero, mul_one]
    have hint_2 : Integrable (fun u : ℝ => (D c u : ℂ)) :=
      (db.hD_L1_int (c := c)).mono' (Complex.continuous_ofReal.comp db.hD_cont).aestronglyMeasurable (ae_of_all _ fun u => by
        rw [Complex.norm_real, Real.norm_eq_abs])
    have h_sub_int : (∫ u : ℝ, (D c u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ))) -
          (∫ u : ℝ, (D c u : ℂ)) =
        ∫ u : ℝ, (D c u : ℂ) * (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1) := by
      rw [← integral_sub hint_1 hint_2]
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      have heq : ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ) = Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ) := by
        push_cast; ring
      dsimp only; rw [heq]; ring
    unfold airyTwistedLaplaceC
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
      Complex.exp_zero, mul_one, zero_mul]
    rw [← h_sub_int]; ring
  have hI_osc := twoEdge_I_osc_eq (y := y) hw_cut hc0 D g hg_def hg_meas hg_nn
  have hRem_eq : ceOriginE c ((y : ℂ) * Complex.I) *
        (liftSymbol (S c) (δ₀ c) m ((1 - ((y : ℂ) * Complex.I) / (c : ℂ)) / (liftEps c : ℂ)) +
          liftSymbol (D c) (δ₀ c) m ((1 - (1 - ((y : ℂ) * Complex.I) / (c : ℂ))) / (liftEps c : ℂ))) -
        (liftSymbol (S c) (δ₀ c) m ((1 : ℂ) / (liftEps c : ℂ)) +
          liftSymbol (D c) (δ₀ c) m ((1 - (1 : ℂ)) / (liftEps c : ℂ))) -
        ((liftEps c : ℝ) : ℂ) * ∫ X in Ioi (0 : ℝ),
          (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ))))
            ∂(volume.withDensity fun X => ENNReal.ofReal (g c X)) =
      (ceOriginE c ((y : ℂ) * Complex.I) - 1) *
        (liftSymbol (S c) (δ₀ c) m ((1 - ((y : ℂ) * Complex.I) / (c : ℂ)) / (liftEps c : ℂ)) +
          liftSymbol (D c) (δ₀ c) m ((1 - (1 - ((y : ℂ) * Complex.I) / (c : ℂ))) / (liftEps c : ℂ))) +
        (liftSymbol (S c) (δ₀ c) m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) - (v : ℂ) * Complex.I) -
          liftSymbol (S c) (δ₀ c) m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ))) +
        (liftMultiplier (δ₀ c) m ((v : ℂ) * Complex.I) - 1) *
          airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
        (ceK : ℂ) * (Complex.exp (-(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12) - 1) *
          (∫ u : ℝ, (D c u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ))) +
        (ceK : ℂ) * ∫ u in Ici w_cut, (D c u : ℂ) * (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1) := by
    rw [hI_osc, h_W1_arg, h_W2_arg, show (1 : ℂ) / (liftEps c : ℂ) = (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)) by
        rw [one_div, ← Complex.ofReal_inv, hε_inv],
      show (1 - (1 : ℂ)) / (liftEps c : ℂ) = 0 by simp,
      show liftSymbol (D c) (δ₀ c) m 0 = airyTwistedLaplaceC (D c) 0 by
        simp [liftSymbol, liftMultiplier, bsplineE1_zero]]
    have hLS : liftSymbol (D c) (δ₀ c) m ((v : ℂ) * Complex.I) =
        liftMultiplier (δ₀ c) m ((v : ℂ) * Complex.I) * airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) := rfl
    have hsubD := hD_lap_eq
    rw [hD_split_int] at hsubD
    rw [hLS]
    linear_combination hsubD
  have hy2_y14 : y ^ 2 ≤ |y| + |y| ^ 4 := sq_le_abs_add_pow4 y
  have hy3_y14 : |y| ^ 3 ≤ |y| + |y| ^ 4 := abs_cube_le_abs_add_pow4 y
  have hε3_le : liftEps c ^ 3 ≤ liftEps c ^ 2 := by
    calc liftEps c ^ 3 = liftEps c * liftEps c ^ 2 := by ring
      _ ≤ 1 * liftEps c ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = liftEps c ^ 2 := one_mul _
  have hε6_le : liftEps c ^ 6 ≤ liftEps c ^ 2 := by
    have h2 : liftEps c ^ 4 ≤ 1 := pow_le_one₀ hε.le (by linarith)
    calc liftEps c ^ 6 = liftEps c ^ 4 * liftEps c ^ 2 := by ring
      _ ≤ 1 * liftEps c ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = liftEps c ^ 2 := one_mul _
  have hc_inv : c⁻¹ = liftEps c ^ 3 := by
    calc c⁻¹ = (liftEps c ^ 3 * c) * c⁻¹ := by rw [hc_prod1, one_mul]
      _ = liftEps c ^ 3 := by field_simp [hc0.ne']
  have ht1 : ‖(ceOriginE c ((y : ℂ) * Complex.I) - 1) *
        (liftSymbol (S c) (δ₀ c) m ((1 - ((y : ℂ) * Complex.I) / (c : ℂ)) / (liftEps c : ℂ)) +
          liftSymbol (D c) (δ₀ c) m ((1 - (1 - ((y : ℂ) * Complex.I) / (c : ℂ))) / (liftEps c : ℂ)))‖ ≤
      Real.exp (3 / 2 * CH_pha) * CH_pha * (C_S + db.C_D) * liftEps c ^ 2 * (|y| + |y| ^ 4) := by
    calc _ ≤ (Real.exp (3 / 2 * CH_pha) * CH_pha * (y ^ 2 / c)) * (C_S + db.C_D) :=
          (norm_mul_le _ _).trans (mul_le_mul hE_sub hWtilde_bd (norm_nonneg _) (by positivity))
      _ = Real.exp (3 / 2 * CH_pha) * CH_pha * (C_S + db.C_D) * liftEps c ^ 3 * y ^ 2 := by
          rw [show y ^ 2 / c = y ^ 2 * c⁻¹ from div_eq_mul_inv _ _, hc_inv]; ring
      _ ≤ Real.exp (3 / 2 * CH_pha) * CH_pha * (C_S + db.C_D) * liftEps c ^ 2 * (|y| + |y| ^ 4) := by gcongr
  have ht2 : ‖liftSymbol (S c) (δ₀ c) m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) - (v : ℂ) * Complex.I) -
        liftSymbol (S c) (δ₀ c) m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ))‖ ≤
      2 * C_S * liftEps c ^ 2 * (|y| + |y| ^ 4) := by
    refine hWS_sub.trans ?_
    rw [hv_abs]
    calc 2 * C_S * (liftEps c ^ 2 * |y|) = 2 * C_S * liftEps c ^ 2 * |y| := by ring
      _ ≤ 2 * C_S * liftEps c ^ 2 * (|y| + |y| ^ 4) := by gcongr; linarith [pow_nonneg (abs_nonneg y) 4]
  have hD_imag : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((v : ℂ) * Complex.I))‖ ≤ ceK * db.L1_D := by
    have hre0 : (-(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12).re = 0 := by
      have harg : -(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12 =
          (((ceCs ^ 3 * v ^ 3 / 12 : ℝ)) : ℂ) * Complex.I := by
        have hi3 : Complex.I ^ 3 = -Complex.I := by
          calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
            _ = -Complex.I := by rw [Complex.I_sq]; ring
        calc -(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12
            = -((ceCs : ℂ) ^ 3 * (v : ℂ) ^ 3 * Complex.I ^ 3) / 12 := by ring
          _ = (((ceCs ^ 3 * v ^ 3 / 12 : ℝ)) : ℂ) * Complex.I := by rw [hi3]; push_cast; ring
      rw [harg, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
    unfold airyTwistedLaplaceC
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk0.le, Complex.norm_exp,
      hre0, Real.exp_zero, mul_one]
    exact mul_le_mul_of_nonneg_left (db.hD_lap_int_bd hc) hk0.le
  have ht3 : ‖(liftMultiplier (δ₀ c) m ((v : ℂ) * Complex.I) - 1) *
        airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((v : ℂ) * Complex.I))‖ ≤
      Cm_unif * (ceCs * C_δ / (m : ℝ)) * ceK * db.L1_D * liftEps c ^ 2 * (|y| + |y| ^ 4) := by
    calc _ ≤ (Cm_unif * (ceCs * C_δ / (m : ℝ)) * (liftEps c * |v|)) * (ceK * db.L1_D) :=
          (norm_mul_le _ _).trans (mul_le_mul hmult_sub hD_imag (norm_nonneg _) (by positivity))
      _ = Cm_unif * (ceCs * C_δ / (m : ℝ)) * ceK * db.L1_D * liftEps c ^ 3 * |y| := by rw [hv_abs]; ring
      _ ≤ Cm_unif * (ceCs * C_δ / (m : ℝ)) * ceK * db.L1_D * liftEps c ^ 2 * (|y| + |y| ^ 4) := by
          gcongr; linarith [pow_nonneg (abs_nonneg y) 4]
  have ht4 : ‖(ceK : ℂ) * (Complex.exp (-(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12) - 1) *
        (∫ u : ℝ, (D c u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ)))‖ ≤
      ceK * (ceCs ^ 3 / 12 * Real.exp (ceCs ^ 3 / 96)) * db.L1_D * liftEps c ^ 2 * (|y| + |y| ^ 4) := by
    calc _ = ceK * ‖Complex.exp (-(((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3) / 12) - 1‖ *
            ‖∫ u : ℝ, (D c u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ))‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk0.le]
      _ ≤ ceK * ((ceCs ^ 3 / 12 * Real.exp (ceCs ^ 3 / 96)) * |v| ^ 3) * db.L1_D := by
          have := db.hD_lap_int_bd (v := v) hc; gcongr
      _ = ceK * (ceCs ^ 3 / 12 * Real.exp (ceCs ^ 3 / 96)) * db.L1_D * liftEps c ^ 6 * |y| ^ 3 := by
          rw [hv_abs, mul_pow]; ring
      _ ≤ ceK * (ceCs ^ 3 / 12 * Real.exp (ceCs ^ 3 / 96)) * db.L1_D * liftEps c ^ 2 * (|y| + |y| ^ 4) := by gcongr
  have ht5 : ‖(ceK : ℂ) * ∫ u in Ici w_cut, (D c u : ℂ) * (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1)‖ ≤
      ceK * ceCs * db.M_mom * liftEps c ^ 2 * (|y| + |y| ^ 4) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk0.le]
    calc ceK * ‖∫ u in Ici w_cut, (D c u : ℂ) * (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1)‖
        ≤ ceK * (ceCs * db.M_mom * |v|) := mul_le_mul_of_nonneg_left (db.hD_osc_right hc) hk0.le
      _ = ceK * ceCs * db.M_mom * liftEps c ^ 2 * |y| := by rw [hv_abs]; ring
      _ ≤ ceK * ceCs * db.M_mom * liftEps c ^ 2 * (|y| + |y| ^ 4) := by
          gcongr; linarith [pow_nonneg (abs_nonneg y) 4]
  rw [hRem_eq]
  calc _ ≤ (Real.exp (3 / 2 * CH_pha) * CH_pha * (C_S + db.C_D) + 2 * C_S +
        Cm_unif * (ceCs * C_δ / (m : ℝ)) * ceK * db.L1_D +
        ceK * (ceCs ^ 3 / 12 * Real.exp (ceCs ^ 3 / 96)) * db.L1_D + ceK * ceCs * db.M_mom) *
        (liftEps c) ^ 2 * (|y| + |y| ^ 4) := by
        have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ht1 ht2)) ht3)) ht4)) ht5)
        refine hsum.trans_eq (by ring)
    _ ≤ _ := by
        have hnn : 0 ≤ (liftEps c) ^ 2 * (|y| + |y| ^ 4) := by positivity
        linarith

end FormalResearch.SignUncertainty
