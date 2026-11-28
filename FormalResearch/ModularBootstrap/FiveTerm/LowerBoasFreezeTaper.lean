module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeTaperBase

/-!
# Taper Regularity, Relative Derivative Bounds, and Window Comparability (`ctl:freeze`)

Establishes:
* `taperWζ_bounds_and_derivs`: `0 < taperWζ c' R ζ ≤ 1`, `C^1` regularity (`ContinuousOn W1`),
  piecewise `C^2` bounds `|W^(j)| ≤ C_W * taperWζ / ζ^j`, and `taperWζ ≤ 2 * (taperV / R)^12`.
* `lowerPζ_properties`: positivity, global `C^1` regularity (`ContinuousOn P1 (Ici (ζ_min/2))`),
  piecewise-`C^2` relative bounds `|P^(j)(ζ)| ≤ C_P * P(ζ) / ζ^j` (`j = 1, 2`), and window
  comparability `P(ζ₁) ≤ 2 * P(ζ₂)` on `|ζ₁ - ζ₂| ≤ 8 log c' + 1` for `ζ₁, ζ₂ ≥ ζ_min c' / 2`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.TipFront

noncomputable section

private lemma taperV_deriv_bounds {c' R : ℝ} (hc' : taperC0 ≤ c')
    (hR : LowerRadiusRange virasoroC1 c' R) :
    ∃ v1 v2 : ℝ → ℝ, ∀ {ζ : ℝ}, zetaMin c' / 2 ≤ ζ → ζ ≤ zetaR c' R + 1 →
      HasDerivAt (taperV c') (v1 ζ) ζ ∧ HasDerivAt v1 (v2 ζ) ζ ∧
      (1 / 2 : ℝ) * vOfZeta ζ ≤ taperV c' ζ ∧ taperV c' ζ ≤ (3 / 2 : ℝ) * vOfZeta ζ ∧
      0 < v1 ζ ∧ |v1 ζ| ≤ 2 * taperV c' ζ / ζ ∧ |v2 ζ| ≤ 2 * taperV c' ζ / ζ ^ 2 ∧
      (ζ ≤ zetaR c' R → taperV c' ζ ≤ R) := by
  have hc0 : 0 < c' := by linarith [taperC0_ge]
  have hc2 : 2 ≤ c' := by linarith [taperC0_ge]
  have hε0 : 0 ≤ c' ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le _
  have hε1 : c' ^ (-2 : ℝ) ≤ 1 / 4 := by
    rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (c' ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith only [hc2])
      _ = 1 / 4 := by norm_num
  have hβ := betaTip_pos
  have hc23 : 0 < c' ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  let s : ℝ := betaTip⁻¹ * c' ^ (-(2 / 3 : ℝ))
  have hs_pos : 0 < s := by positivity
  have hs_lam : virasoroLam c' * s = c'⁻¹ := by
    dsimp [s, virasoroLam]
    calc betaTip * c' ^ (-(1 / 3 : ℝ)) * (betaTip⁻¹ * c' ^ (-(2 / 3 : ℝ)))
        = (betaTip * betaTip⁻¹) * (c' ^ (-(1 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ))) := by ring
      _ = 1 * c' ^ (-1 : ℝ) := by
          rw [mul_inv_cancel₀ hβ.ne', ← Real.rpow_add hc0]; congr 2; norm_num
      _ = c'⁻¹ := by rw [one_mul, Real.rpow_neg_one]
  let ψR : ℝ → ℝ := fun t => (virasoroPsiEps (c' ^ (-2 : ℝ)) (t : ℂ)).re
  let ψ1 : ℝ → ℝ := fun t => (deriv (virasoroPsiEps (c' ^ (-2 : ℝ))) (t : ℂ)).re
  let ψ2 : ℝ → ℝ := fun t => (deriv (deriv (virasoroPsiEps (c' ^ (-2 : ℝ)))) (t : ℂ)).re
  let v01 : ℝ → ℝ := fun t => (2 / 3 : ℝ) * vOfZeta t / t
  let v02 : ℝ → ℝ := fun t => -(2 / 9 : ℝ) * vOfZeta t / t ^ 2
  let v1 : ℝ → ℝ := fun t => v01 t * (1 + c'⁻¹ * ψ1 (-s * vOfZeta t))
  let v2 : ℝ → ℝ := fun t => v02 t * (1 + c'⁻¹ * ψ1 (-s * vOfZeta t)) +
    v01 t * (c'⁻¹ * ψ2 (-s * vOfZeta t) * (-s * v01 t))
  obtain ⟨_, _, hv_zmin, hζR_lo, hzmin_ge, _⟩ := zetaR_bounds hc' hR
  obtain ⟨_, _, _, _, h5_uR, hneg_uR, _, hu_inv⟩ := taper_R_phi_bounds hc' hR
  have hMψ := chartParams.hMψ_nn
  have hrψ := chartParams.hrψ_pos
  have hc_m : 2 * (chartParams.M_ψ + 1) + 4 * chartParams.M_ψ / chartParams.r_ψ + 1 ≤ c' := taperC0_psi hc'
  have hc_b : (4 * betaTip * (chartParams.M_ψ + 1) + 1) ^ 2 ≤ c' := taperC0_beta hc'
  have hw_bd_all : ∀ {ζ : ℝ}, zetaMin c' / 2 ≤ ζ → ζ ≤ zetaR c' R + 1 →
      |-s * vOfZeta ζ| ≤ chartParams.r_ψ / 2 := by
    intro ζ hζ_lo hζ_hi
    have hζ_pos : 0 < ζ := by linarith only [hzmin_ge, hζ_lo]
    have hζR_pos : 20 ≤ zetaR c' R := by linarith only [hζR_lo, hzmin_ge]
    have hvζ : vOfZeta ζ ≤ (6 / 5 : ℝ) * (5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) := by
      have hv_up := vOfZeta_mono hζ_pos.le hζ_hi
      have hdiv : (zetaR c' R + 1) / zetaR c' R ≤ 21 / 20 := by
        rw [div_le_div_iff₀ (by linarith only [hζR_pos]) (by norm_num)]
        linarith only [hζR_pos]
      have hzetaR_eq : vOfZeta (zetaR c' R) = -(virasoroPhi c' (-R)).re := by
        unfold zetaR; exact vOfZeta_zetaOfV (by linarith only [hneg_uR])
      have hv_split : vOfZeta (zetaR c' R + 1) =
          vOfZeta (zetaR c' R) * ((zetaR c' R + 1) / zetaR c' R) ^ (2 / 3 : ℝ) := by
        unfold vOfZeta
        have hmul : 3 * π * (zetaR c' R + 1) / 2 =
            (3 * π * zetaR c' R / 2) * ((zetaR c' R + 1) / zetaR c' R) := by
          field_simp [(by linarith only [hζR_pos] : zetaR c' R ≠ 0)]
        rw [hmul, Real.mul_rpow (by positivity) (by positivity)]
      have hpow : ((zetaR c' R + 1) / zetaR c' R) ^ (2 / 3 : ℝ) ≤ 6 / 5 := by
        calc ((zetaR c' R + 1) / zetaR c' R) ^ (2 / 3 : ℝ)
            ≤ (21 / 20 : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hdiv (by norm_num)
          _ ≤ (21 / 20 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 21 / 20 := Real.rpow_one _
          _ ≤ 6 / 5 := by norm_num
      have hvR_le : vOfZeta (zetaR c' R) ≤ 5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := by
        rw [hzetaR_eq]; linarith only [h5_uR]
      calc vOfZeta ζ ≤ vOfZeta (zetaR c' R + 1) := hv_up
        _ = vOfZeta (zetaR c' R) * ((zetaR c' R + 1) / zetaR c' R) ^ (2 / 3 : ℝ) := hv_split
        _ ≤ (5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) * (6 / 5) := by gcongr
        _ = (6 / 5) * (5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) := by ring
    have hw_nn : 0 ≤ s * vOfZeta ζ := mul_nonneg hs_pos.le (vOfZeta_pos hζ_pos).le
    rw [show |-s * vOfZeta ζ| = s * vOfZeta ζ by rw [neg_mul, abs_neg, abs_of_nonneg hw_nn]]
    have hc_prod : c' ^ (-(2 / 3 : ℝ)) * c' ^ (2 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc0]; simp
    have h4r : 4 * virasoroC1 ^ 2 * betaTip⁻¹ ≤ chartParams.r_ψ / 4 := by
      have h1 : virasoroC1 ≤ √(chartParams.r_ψ * betaTip / 16) :=
        (min_le_right _ _).trans (min_le_left _ _)
      have hsq : virasoroC1 ^ 2 ≤ chartParams.r_ψ * betaTip / 16 := by
        calc virasoroC1 ^ 2 ≤ (√(chartParams.r_ψ * betaTip / 16)) ^ 2 :=
              pow_le_pow_left₀ virasoroC1_pos.le h1 2
          _ = chartParams.r_ψ * betaTip / 16 := Real.sq_sqrt (by positivity)
      calc 4 * virasoroC1 ^ 2 * betaTip⁻¹ ≤ 4 * (chartParams.r_ψ * betaTip / 16) * betaTip⁻¹ := by gcongr
        _ = chartParams.r_ψ / 4 := by field_simp [hβ.ne']; ring
    calc s * vOfZeta ζ ≤ s * (6 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) := by
          gcongr; linarith only [hvζ]
      _ = (6 * virasoroC1 ^ 2 * betaTip⁻¹) * (c' ^ (-(2 / 3 : ℝ)) * c' ^ (2 / 3 : ℝ)) := by
          dsimp [s]; ring
      _ = 6 * virasoroC1 ^ 2 * betaTip⁻¹ := by rw [hc_prod, mul_one]
      _ = (3 / 2) * (4 * virasoroC1 ^ 2 * betaTip⁻¹) := by ring
      _ ≤ (3 / 2) * (chartParams.r_ψ / 4) := by gcongr
      _ ≤ chartParams.r_ψ / 2 := by linarith only [hrψ]
  have hderiv_all : ∀ {ζ : ℝ}, zetaMin c' / 2 ≤ ζ → ζ ≤ zetaR c' R + 1 →
      HasDerivAt (taperV c') (v1 ζ) ζ ∧ HasDerivAt v1 (v2 ζ) ζ ∧
      (1 / 2 : ℝ) * vOfZeta ζ ≤ taperV c' ζ ∧ taperV c' ζ ≤ (3 / 2 : ℝ) * vOfZeta ζ ∧
      0 < v1 ζ ∧ |v1 ζ| ≤ 2 * taperV c' ζ / ζ ∧ |v2 ζ| ≤ 2 * taperV c' ζ / ζ ^ 2 := by
    intro ζ hζ_lo hζ_hi
    have hζ_pos : 0 < ζ := by linarith only [hzmin_ge, hζ_lo]
    obtain ⟨hd_v0, hd_v01⟩ := vOfZeta_derivs hζ_pos
    have hw_bd := hw_bd_all hζ_lo hζ_hi
    obtain ⟨hd_ψR, hd_ψ1, hbd0, hbd1, hbd2⟩ := virasoroPsiEps_re_c2 hε0 hε1 hw_bd
    have hd_s_neg : HasDerivAt (fun t => -s * vOfZeta t) (-s * v01 ζ) ζ :=
      (hd_v0.const_mul (-s)).congr_deriv (by ring)
    change HasDerivAt ψR (ψ1 (-s * vOfZeta ζ)) (-s * vOfZeta ζ) at hd_ψR
    change HasDerivAt ψ1 (ψ2 (-s * vOfZeta ζ)) (-s * vOfZeta ζ) at hd_ψ1
    have hψ_comp1 : HasDerivAt (fun t => ψR (-s * vOfZeta t)) (ψ1 (-s * vOfZeta ζ) * (-s * v01 ζ)) ζ := by
      show HasDerivAt (ψR ∘ fun t => -s * vOfZeta t) (ψ1 (-s * vOfZeta ζ) * (-s * v01 ζ)) ζ
      exact hd_ψR.comp ζ hd_s_neg
    have hψ_comp2 : HasDerivAt (fun t => ψ1 (-s * vOfZeta t)) (ψ2 (-s * vOfZeta ζ) * (-s * v01 ζ)) ζ := by
      show HasDerivAt (ψ1 ∘ fun t => -s * vOfZeta t) (ψ2 (-s * vOfZeta ζ) * (-s * v01 ζ)) ζ
      exact hd_ψ1.comp ζ hd_s_neg
    have htaper_eq : taperV c' = fun t => vOfZeta t - virasoroLam c' * ψR (-s * vOfZeta t) := by
      ext t; unfold taperV virasoroUhat fjUhat virasoroPsiChart virasoroMu; dsimp [s, ψR]; ring_nf
    have hd1 : HasDerivAt (taperV c') (v1 ζ) ζ := by
      rw [htaper_eq]
      refine (hd_v0.sub (hψ_comp1.const_mul (virasoroLam c'))).congr_deriv ?_
      dsimp [v1]
      calc v01 ζ - virasoroLam c' * (ψ1 (-s * vOfZeta ζ) * (-s * v01 ζ))
          = v01 ζ * (1 + (virasoroLam c' * s) * ψ1 (-s * vOfZeta ζ)) := by ring
        _ = v01 ζ * (1 + c'⁻¹ * ψ1 (-s * vOfZeta ζ)) := by rw [hs_lam]
    have hd2 : HasDerivAt v1 (v2 ζ) ζ := by
      have hfac : HasDerivAt (fun t => 1 + c'⁻¹ * ψ1 (-s * vOfZeta t))
          (c'⁻¹ * (ψ2 (-s * vOfZeta ζ) * (-s * v01 ζ))) ζ :=
        ((hasDerivAt_const ζ (1 : ℝ)).add (hψ_comp2.const_mul c'⁻¹)).congr_deriv (by simp)
      refine (hd_v01.mul hfac).congr_deriv ?_
      dsimp [v2]
      ring
    have hvζ_lb : (1 / 2 : ℝ) * c' ^ (4 / 7 : ℝ) ≤ vOfZeta ζ :=
      hv_zmin.trans (vOfZeta_mono (by positivity) hζ_lo)
    have hlam_bd : virasoroLam c' * |ψR (-s * vOfZeta ζ)| ≤ (1 / 2 : ℝ) * vOfZeta ζ := by
      have hlam_nn : 0 ≤ virasoroLam c' := by unfold virasoroLam; positivity
      have hlam_m : virasoroLam c' * chartParams.M_ψ = betaTip * chartParams.M_ψ * c' ^ (-(1 / 3 : ℝ)) := by
        unfold virasoroLam; ring
      have hc_sqrt : 4 * betaTip * (chartParams.M_ψ + 1) ≤ c' ^ (1 / 2 : ℝ) := by
        have h1 := Real.sqrt_le_sqrt hc_b
        rw [Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow] at h1
        linarith only [h1]
      have hc_prod : c' ^ (1 / 2 : ℝ) ≤ c' ^ (1 / 3 : ℝ) * c' ^ (4 / 7 : ℝ) := by
        rw [← Real.rpow_add hc0]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [taperC0_ge]) (by norm_num)
      have hc_m2 : 4 * betaTip * chartParams.M_ψ * c' ^ (-(1 / 3 : ℝ)) ≤ c' ^ (4 / 7 : ℝ) := by
        have h1 : 4 * betaTip * chartParams.M_ψ ≤ c' ^ (1 / 3 : ℝ) * c' ^ (4 / 7 : ℝ) := by
          have : 4 * betaTip * chartParams.M_ψ ≤ 4 * betaTip * (chartParams.M_ψ + 1) := by nlinarith only [hβ]
          linarith only [this, hc_sqrt, hc_prod]
        have h3_nn : 0 ≤ c' ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
        calc 4 * betaTip * chartParams.M_ψ * c' ^ (-(1 / 3 : ℝ))
            ≤ (c' ^ (1 / 3 : ℝ) * c' ^ (4 / 7 : ℝ)) * c' ^ (-(1 / 3 : ℝ)) := by gcongr
          _ = c' ^ (4 / 7 : ℝ) * (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ))) := by ring
          _ = c' ^ (4 / 7 : ℝ) := by rw [← Real.rpow_add hc0]; simp
      calc virasoroLam c' * |ψR (-s * vOfZeta ζ)|
          ≤ virasoroLam c' * chartParams.M_ψ := mul_le_mul_of_nonneg_left hbd0 hlam_nn
        _ ≤ (1 / 4 : ℝ) * c' ^ (4 / 7 : ℝ) := by
            rw [hlam_m]; linarith only [hc_m2]
        _ ≤ (1 / 2 : ℝ) * vOfZeta ζ := by linarith only [hvζ_lb]
    have ht_eq' : taperV c' ζ = vOfZeta ζ - virasoroLam c' * ψR (-s * vOfZeta ζ) := by
      rw [htaper_eq]
    have hlam_abs : |virasoroLam c' * ψR (-s * vOfZeta ζ)| ≤ (1 / 2 : ℝ) * vOfZeta ζ := by
      rw [abs_mul, abs_of_nonneg (by unfold virasoroLam; positivity)]
      exact hlam_bd
    have hlo_t : (1 / 2 : ℝ) * vOfZeta ζ ≤ taperV c' ζ := by
      rw [ht_eq']
      linarith only [(abs_le.mp hlam_abs).2]
    have hhi_t : taperV c' ζ ≤ (3 / 2 : ℝ) * vOfZeta ζ := by
      rw [ht_eq']
      linarith only [(abs_le.mp hlam_abs).1]
    have hv01_pos : 0 < v01 ζ := by dsimp [v01]; have := vOfZeta_pos hζ_pos; positivity
    have hcψ1 : |c'⁻¹ * ψ1 (-s * vOfZeta ζ)| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hc0)]
      have hc2M : 2 * chartParams.M_ψ ≤ c' := by linarith only [hc_m, div_nonneg (by linarith : 0 ≤ 4 * chartParams.M_ψ) hrψ.le]
      rw [inv_mul_le_iff₀ hc0]
      linarith only [hbd1, hc2M]
    have hv1_pos : 0 < v1 ζ := by
      dsimp [v1]
      have hfac : 1 / 2 ≤ 1 + c'⁻¹ * ψ1 (-s * vOfZeta ζ) := by linarith only [(abs_le.mp hcψ1).1]
      positivity
    have hv1_bd : |v1 ζ| ≤ 2 * taperV c' ζ / ζ := by
      rw [abs_of_pos hv1_pos]
      dsimp [v1, v01]
      have hfac : 1 + c'⁻¹ * ψ1 (-s * vOfZeta ζ) ≤ 3 / 2 := by linarith only [(abs_le.mp hcψ1).2]
      calc (2 / 3 * vOfZeta ζ / ζ) * (1 + c'⁻¹ * ψ1 (-s * vOfZeta ζ))
          ≤ (2 / 3 * vOfZeta ζ / ζ) * (3 / 2) := by gcongr
        _ = vOfZeta ζ / ζ := by ring
        _ ≤ (2 * taperV c' ζ) / ζ := by gcongr; linarith only [hlo_t]
    have hv2_bd : |v2 ζ| ≤ 2 * taperV c' ζ / ζ ^ 2 := by
      have ht1 : |v02 ζ * (1 + c'⁻¹ * ψ1 (-s * vOfZeta ζ))| ≤ (1 / 3 : ℝ) * vOfZeta ζ / ζ ^ 2 := by
        have hv02_abs : |v02 ζ| = (2 / 9 : ℝ) * vOfZeta ζ / ζ ^ 2 := by
          dsimp [v02]
          rw [show -(2 / 9 : ℝ) * vOfZeta ζ / ζ ^ 2 = -((2 / 9 : ℝ) * vOfZeta ζ / ζ ^ 2) by ring,
            abs_neg, abs_of_pos (by have := vOfZeta_pos hζ_pos; positivity)]
        have hfac : |1 + c'⁻¹ * ψ1 (-s * vOfZeta ζ)| ≤ 3 / 2 :=
          abs_le.mpr ⟨by linarith only [(abs_le.mp hcψ1).1], by linarith only [(abs_le.mp hcψ1).2]⟩
        have hv02_nn : 0 ≤ 2 / 9 * vOfZeta ζ / ζ ^ 2 := by
          have := vOfZeta_pos hζ_pos; positivity
        rw [abs_mul, hv02_abs]
        calc (2 / 9 * vOfZeta ζ / ζ ^ 2) * |1 + c'⁻¹ * ψ1 (-s * vOfZeta ζ)|
            ≤ (2 / 9 * vOfZeta ζ / ζ ^ 2) * (3 / 2) := by gcongr
          _ = 1 / 3 * vOfZeta ζ / ζ ^ 2 := by ring
      have ht2 : |v01 ζ * (c'⁻¹ * ψ2 (-s * vOfZeta ζ) * (-s * v01 ζ))| ≤
          (1 / 2 : ℝ) * vOfZeta ζ / ζ ^ 2 := by
        have hsv_nn : 0 ≤ s * vOfZeta ζ := mul_nonneg hs_pos.le (vOfZeta_pos hζ_pos).le
        have hws : s * vOfZeta ζ ≤ chartParams.r_ψ / 2 := by
          have h1 := hw_bd
          rwa [neg_mul, abs_neg, abs_of_nonneg hsv_nn] at h1
        have hψw : |ψ2 (-s * vOfZeta ζ)| * (s * vOfZeta ζ) ≤ chartParams.M_ψ := by
          calc |ψ2 (-s * vOfZeta ζ)| * (s * vOfZeta ζ)
              ≤ (2 * chartParams.M_ψ / chartParams.r_ψ) * (chartParams.r_ψ / 2) := by
                gcongr
            _ = chartParams.M_ψ := by field_simp [hrψ.ne']
        have hre : v01 ζ * (c'⁻¹ * ψ2 (-s * vOfZeta ζ) * (-s * v01 ζ)) =
            -(4 / 9 : ℝ) * c'⁻¹ * (ψ2 (-s * vOfZeta ζ) * (s * vOfZeta ζ)) * (vOfZeta ζ / ζ ^ 2) := by
          dsimp [v01]; ring
        have hvv_pos : 0 < vOfZeta ζ / ζ ^ 2 := div_pos (vOfZeta_pos hζ_pos) (sq_pos_of_pos hζ_pos)
        rw [hre, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 4 / 9),
          abs_of_pos (inv_pos.mpr hc0), abs_mul, abs_of_nonneg hsv_nn, abs_of_pos hvv_pos]
        have hcM : (4 / 9 : ℝ) * c'⁻¹ * chartParams.M_ψ ≤ 1 / 2 := by
          have hc2M : 2 * chartParams.M_ψ ≤ c' := by linarith only [hc_m, div_nonneg (by linarith : 0 ≤ 4 * chartParams.M_ψ) hrψ.le]
          have hmc : chartParams.M_ψ / c' ≤ 1 / 2 := (div_le_iff₀ hc0).mpr (by linarith only [hc2M])
          calc (4 / 9 : ℝ) * c'⁻¹ * chartParams.M_ψ = 4 / 9 * (chartParams.M_ψ / c') := by ring
            _ ≤ 4 / 9 * (1 / 2) := by gcongr
            _ ≤ 1 / 2 := by norm_num
        calc 4 / 9 * c'⁻¹ * (|ψ2 (-s * vOfZeta ζ)| * (s * vOfZeta ζ)) * (vOfZeta ζ / ζ ^ 2)
            ≤ 4 / 9 * c'⁻¹ * chartParams.M_ψ * (vOfZeta ζ / ζ ^ 2) := by gcongr
          _ ≤ (1 / 2) * (vOfZeta ζ / ζ ^ 2) := by gcongr
          _ = 1 / 2 * vOfZeta ζ / ζ ^ 2 := by ring
      have h56 : 1 / 3 * vOfZeta ζ / ζ ^ 2 + 1 / 2 * vOfZeta ζ / ζ ^ 2 =
          (5 / 6 : ℝ) * (vOfZeta ζ / ζ ^ 2) := by ring
      have hvv_nn : 0 ≤ vOfZeta ζ / ζ ^ 2 := by have := vOfZeta_pos hζ_pos; positivity
      calc |v2 ζ| ≤ _ + _ := by dsimp [v2]; exact abs_add_le _ _
        _ ≤ 1 / 3 * vOfZeta ζ / ζ ^ 2 + 1 / 2 * vOfZeta ζ / ζ ^ 2 := add_le_add ht1 ht2
        _ = (5 / 6 : ℝ) * (vOfZeta ζ / ζ ^ 2) := h56
        _ ≤ 1 * (vOfZeta ζ / ζ ^ 2) := by gcongr; norm_num
        _ = vOfZeta ζ / ζ ^ 2 := one_mul _
        _ ≤ 2 * taperV c' ζ / ζ ^ 2 := by gcongr; linarith only [hlo_t]
    exact ⟨hd1, hd2, hlo_t, hhi_t, hv1_pos, hv1_bd, hv2_bd⟩
  refine ⟨v1, v2, fun {ζ} hζ_lo hζ_hi => ?_⟩
  obtain ⟨hd1, hd2, hlo_t, hhi_t, hv1_pos, hv1_bd, hv2_bd⟩ := hderiv_all hζ_lo hζ_hi
  refine ⟨hd1, hd2, hlo_t, hhi_t, hv1_pos, hv1_bd, hv2_bd, fun hζR => ?_⟩
  have hζR_hi' : zetaR c' R ≤ zetaR c' R + 1 := by linarith
  have ht_val : taperV c' (zetaR c' R) = R := by
    unfold taperV zetaR
    rw [vOfZeta_zetaOfV (by linarith only [hneg_uR]), neg_neg, hu_inv]
    ring
  rcases hζR.eq_or_lt with rfl | hlt
  · exact ht_val.le
  · rw [← ht_val]
    have hmon := monotoneOn_of_deriv_nonneg (convex_Icc (zetaMin c' / 2) (zetaR c' R + 1))
      (fun z hz => (hderiv_all hz.1 hz.2).1.continuousAt.continuousWithinAt)
      (fun z hz =>
        have hz_icc := interior_subset hz
        (hderiv_all hz_icc.1 hz_icc.2).1.differentiableAt.differentiableWithinAt)
      (fun z hz => by
        have hz_icc := interior_subset hz
        have h := hderiv_all hz_icc.1 hz_icc.2
        rw [h.1.deriv]
        exact h.2.2.2.2.1.le)
    exact hmon ⟨hζ_lo, hζ_hi⟩ ⟨by linarith only [hζR_lo, hzmin_ge], hζR_hi'⟩ hlt.le

lemma taperWζ_bounds_and_derivs {c' R : ℝ} (hc' : taperC0 ≤ c')
    (hR : LowerRadiusRange virasoroC1 c' R) :
    ∃ W1 W2 : ℝ → ℝ,
      ContinuousOn W1 (Ici (zetaMin c' / 2)) ∧
      ∀ {ζ : ℝ}, zetaMin c' / 2 ≤ ζ →
        0 < taperWζ c' R ζ ∧ taperWζ c' R ζ ≤ 1 ∧
        (ζ ≤ zetaR c' R → taperWζ c' R ζ ≤ 2 * (taperV c' ζ / R) ^ 12 ∧
          (1 / 2 : ℝ) * vOfZeta ζ ≤ taperV c' ζ ∧ taperV c' ζ ≤ (3 / 2 : ℝ) * vOfZeta ζ) ∧
        HasDerivAt (taperWζ c' R) (W1 ζ) ζ ∧
        |W1 ζ| ≤ 96 * taperWζ c' R ζ / ζ ∧
        (ζ ≠ zetaR c' R → HasDerivAt W1 (W2 ζ) ζ) ∧
        |W2 ζ| ≤ 3360 * taperWζ c' R ζ / ζ ^ 2 := by
  have hc0 : 0 < c' := by linarith [taperC0_ge]
  have hR_pos : 0 < R := lt_of_lt_of_le (mul_pos (pow_pos virasoroC1_pos 2) (Real.rpow_pos_of_pos hc0 _)) hR.1
  obtain ⟨v1, v2, hv_spec⟩ := taperV_deriv_bounds hc' hR
  obtain ⟨_, _, _, hζR_lo, hzmin_ge, _⟩ := zetaR_bounds hc' hR
  obtain ⟨_, _, _, _, _, hneg_uR, _, hu_inv⟩ := taper_R_phi_bounds hc' hR
  let u : ℝ → ℝ := fun ζ => taperV c' ζ / R
  let u1 : ℝ → ℝ := fun ζ => v1 ζ / R
  let u2 : ℝ → ℝ := fun ζ => v2 ζ / R
  let WL : ℝ → ℝ := fun ζ => 2 * u ζ ^ 12 - u ζ ^ 24
  let WL1 : ℝ → ℝ := fun ζ => 24 * u ζ ^ 11 * u1 ζ - 24 * u ζ ^ 23 * u1 ζ
  let WL2 : ℝ → ℝ := fun ζ =>
    2 * (132 * u ζ ^ 10 * u1 ζ ^ 2 + 12 * u ζ ^ 11 * u2 ζ) -
      (552 * u ζ ^ 22 * u1 ζ ^ 2 + 24 * u ζ ^ 23 * u2 ζ)
  let W1 : ℝ → ℝ := fun ζ => if ζ ≤ zetaR c' R then WL1 ζ else 0
  let W2 : ℝ → ℝ := fun ζ => if ζ ≤ zetaR c' R then WL2 ζ else 0
  have hWL_eq : ∀ ζ, 1 - lowerW6 R (taperV c' ζ) = WL ζ := fun ζ => by
    unfold lowerW6; dsimp [WL, u]; ring
  have hWL_derivs : ∀ {ζ : ℝ}, zetaMin c' / 2 ≤ ζ → ζ ≤ zetaR c' R + 1 →
      HasDerivAt WL (WL1 ζ) ζ ∧ HasDerivAt WL1 (WL2 ζ) ζ := by
    intro ζ hlo hhi
    obtain ⟨hd_v, hd_v1, _⟩ := hv_spec hlo hhi
    have hd_u : HasDerivAt u (u1 ζ) ζ := hd_v.div_const R
    have hd_u1 : HasDerivAt u1 (u2 ζ) ζ := hd_v1.div_const R
    have hd_12 : HasDerivAt (fun t => u t ^ 12) (12 * u ζ ^ 11 * u1 ζ) ζ :=
      (hd_u.pow 12).congr_deriv (by simp)
    have hd_24 : HasDerivAt (fun t => u t ^ 24) (24 * u ζ ^ 23 * u1 ζ) ζ :=
      (hd_u.pow 24).congr_deriv (by simp)
    have hd1 : HasDerivAt WL (WL1 ζ) ζ := by
      refine ((hd_12.const_mul 2).sub hd_24).congr_deriv ?_
      dsimp [WL1]; ring
    have hd_11 : HasDerivAt (fun t => u t ^ 11) (11 * u ζ ^ 10 * u1 ζ) ζ :=
      (hd_u.pow 11).congr_deriv (by simp)
    have hd_23 : HasDerivAt (fun t => u t ^ 23) (23 * u ζ ^ 22 * u1 ζ) ζ :=
      (hd_u.pow 23).congr_deriv (by simp)
    have hd_u11 : HasDerivAt (fun t => u t ^ 11 * u1 t) (11 * u ζ ^ 10 * u1 ζ ^ 2 + u ζ ^ 11 * u2 ζ) ζ :=
      (hd_11.mul hd_u1).congr_deriv (by ring)
    have hd_u23 : HasDerivAt (fun t => u t ^ 23 * u1 t) (23 * u ζ ^ 22 * u1 ζ ^ 2 + u ζ ^ 23 * u2 ζ) ζ :=
      (hd_23.mul hd_u1).congr_deriv (by ring)
    have hd2 : HasDerivAt WL1 (WL2 ζ) ζ := by
      have hL : WL1 = fun t => 24 * (u t ^ 11 * u1 t) - 24 * (u t ^ 23 * u1 t) := by
        ext t; dsimp [WL1]; ring
      rw [hL]
      refine ((hd_u11.const_mul 24).sub (hd_u23.const_mul 24)).congr_deriv ?_
      dsimp [WL2]; ring
    exact ⟨hd1, hd2⟩
  have hζR_mem : zetaMin c' / 2 ≤ zetaR c' R := by linarith only [hζR_lo, hzmin_ge]
  have hu_ζR : u (zetaR c' R) = 1 := by
    dsimp [u, taperV, zetaR]
    rw [vOfZeta_zetaOfV (by linarith only [hneg_uR]), neg_neg, hu_inv, neg_neg, div_self hR_pos.ne']
  have hWL_ζR : WL (zetaR c' R) = 1 := by dsimp [WL]; rw [hu_ζR]; norm_num
  have hWL1_ζR : WL1 (zetaR c' R) = 0 := by dsimp [WL1]; rw [hu_ζR]; ring
  have hcont_W1 : ContinuousOn W1 (Ici (zetaMin c' / 2)) := by
    intro ζ hζ
    rcases lt_trichotomy ζ (zetaR c' R) with hlt | rfl | hgt
    · have hev : W1 =ᶠ[𝓝 ζ] WL1 := by
        filter_upwards [Iio_mem_nhds hlt] with t ht
        simp only [W1, ht.le, ↓reduceIte]
      have hcont_WL1 : ContinuousAt WL1 ζ :=
        (hWL_derivs hζ (by linarith only [hlt])).2.continuousAt
      exact (hcont_WL1.congr hev.symm).continuousWithinAt
    · have hcL : ContinuousWithinAt W1 (Iic (zetaR c' R)) (zetaR c' R) := by
        have hcont_WL1 : ContinuousWithinAt WL1 (Iic (zetaR c' R)) (zetaR c' R) :=
          (hWL_derivs hζR_mem (by linarith)).2.continuousAt.continuousWithinAt
        exact hcont_WL1.congr (fun t ht => by
          have ht' : t ≤ zetaR c' R := ht
          simp only [W1, ht', ↓reduceIte])
          (by simp only [W1, le_rfl, ↓reduceIte])
      have hcR : ContinuousWithinAt W1 (Ici (zetaR c' R)) (zetaR c' R) := by
        have hc0' : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Ici (zetaR c' R)) (zetaR c' R) :=
          continuousWithinAt_const
        refine hc0'.congr (fun t ht => ?_) (by simp only [W1, le_rfl, ↓reduceIte, hWL1_ζR])
        dsimp [W1]
        rcases eq_or_lt_of_le (ht : zetaR c' R ≤ t) with rfl | hgt
        · simp only [le_rfl, ↓reduceIte, hWL1_ζR]
        · simp only [not_le.mpr hgt, ↓reduceIte]
      have huniv : ContinuousWithinAt W1 univ (zetaR c' R) := by
        simpa [Iic_union_Ici] using hcL.union hcR
      exact huniv.mono (subset_univ _)
    · have hev : W1 =ᶠ[𝓝 ζ] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hgt] with t ht
        simp only [W1, not_le.mpr ht, ↓reduceIte]
      exact (continuousAt_const.congr hev.symm).continuousWithinAt
  refine ⟨W1, W2, hcont_W1, fun {ζ} hζ_lo => ?_⟩
  by_cases hle : ζ ≤ zetaR c' R
  · have hζ_hi : ζ ≤ zetaR c' R + 1 := by linarith only [hle]
    obtain ⟨_, _, hlo_t, hhi_t, _, hv1_bd, hv2_bd, hle_R⟩ := hv_spec hζ_lo hζ_hi
    have hζ_pos : 0 < ζ := by linarith only [hzmin_ge, hζ_lo]
    have hu_pos : 0 < u ζ := div_pos (by have := vOfZeta_pos hζ_pos; linarith only [hlo_t, this]) hR_pos
    have hu_le1 : u ζ ≤ 1 := (div_le_one hR_pos).mpr (hle_R hle)
    have hW_eq : taperWζ c' R ζ = WL ζ := by unfold taperWζ; simp only [hle, ↓reduceIte, hWL_eq]
    have hu12_le1 : u ζ ^ 12 ≤ 1 := pow_le_one₀ hu_pos.le hu_le1
    have hW_pos : 0 < taperWζ c' R ζ := by
      rw [hW_eq]; dsimp [WL]
      have hfac : 2 * u ζ ^ 12 - u ζ ^ 24 = u ζ ^ 12 * (2 - u ζ ^ 12) := by ring
      have h2_pos : 0 < 2 - u ζ ^ 12 := by linarith only [hu12_le1]
      rw [hfac]; positivity
    have hu12_le_W : u ζ ^ 12 ≤ taperWζ c' R ζ := by
      rw [hW_eq]; dsimp [WL]
      nlinarith only [pow_pos hu_pos 12, hu12_le1]
    have hW_le1 : taperWζ c' R ζ ≤ 1 := by
      rw [hW_eq]; dsimp [WL]
      have hsq : 0 ≤ (1 - u ζ ^ 12) ^ 2 := sq_nonneg _
      linarith only [hsq, show 2 * u ζ ^ 12 - u ζ ^ 24 = 1 - (1 - u ζ ^ 12) ^ 2 by ring]
    have hW_le2u : taperWζ c' R ζ ≤ 2 * (taperV c' ζ / R) ^ 12 := by
      rw [hW_eq]; dsimp [WL, u]
      have h24_nn : 0 ≤ (taperV c' ζ / R) ^ 24 := by positivity
      linarith only [h24_nn]
    have hu1_bd : |u1 ζ| ≤ 2 * u ζ / ζ := by
      dsimp [u1, u]
      rw [abs_div, abs_of_pos hR_pos]
      calc |v1 ζ| / R ≤ (2 * taperV c' ζ / ζ) / R := by gcongr
        _ = 2 * (taperV c' ζ / R) / ζ := by ring
    have hu2_bd : |u2 ζ| ≤ 2 * u ζ / ζ ^ 2 := by
      dsimp [u2, u]
      rw [abs_div, abs_of_pos hR_pos]
      calc |v2 ζ| / R ≤ (2 * taperV c' ζ / ζ ^ 2) / R := by gcongr
        _ = 2 * (taperV c' ζ / R) / ζ ^ 2 := by ring
    have hu24_le : u ζ ^ 24 ≤ u ζ ^ 12 := by
      calc u ζ ^ 24 = u ζ ^ 12 * u ζ ^ 12 := by ring
        _ ≤ u ζ ^ 12 * 1 := mul_le_mul_of_nonneg_left hu12_le1 (by positivity)
        _ = u ζ ^ 12 := mul_one _
    have hW1_bd : |W1 ζ| ≤ 96 * taperWζ c' R ζ / ζ := by
      simp only [W1, hle, ↓reduceIte]; dsimp [WL1]
      have ha : |24 * u ζ ^ 11 * u1 ζ| ≤ 48 * u ζ ^ 12 / ζ := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num), abs_pow, abs_of_pos hu_pos]
        calc 24 * u ζ ^ 11 * |u1 ζ| ≤ 24 * u ζ ^ 11 * (2 * u ζ / ζ) := by gcongr
          _ = 48 * u ζ ^ 12 / ζ := by ring
      have hb : |24 * u ζ ^ 23 * u1 ζ| ≤ 48 * u ζ ^ 12 / ζ := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num), abs_pow, abs_of_pos hu_pos]
        calc 24 * u ζ ^ 23 * |u1 ζ| ≤ 24 * u ζ ^ 23 * (2 * u ζ / ζ) := by gcongr
          _ = 48 * u ζ ^ 24 / ζ := by ring
          _ ≤ 48 * u ζ ^ 12 / ζ := by gcongr
      calc |24 * u ζ ^ 11 * u1 ζ - 24 * u ζ ^ 23 * u1 ζ|
          ≤ |24 * u ζ ^ 11 * u1 ζ| + |24 * u ζ ^ 23 * u1 ζ| := abs_sub _ _
        _ ≤ 48 * u ζ ^ 12 / ζ + 48 * u ζ ^ 12 / ζ := add_le_add ha hb
        _ = 96 * u ζ ^ 12 / ζ := by ring
        _ ≤ 96 * taperWζ c' R ζ / ζ := by gcongr
    have hW2_bd : |W2 ζ| ≤ 3360 * taperWζ c' R ζ / ζ ^ 2 := by
      simp only [W2, hle, ↓reduceIte]; dsimp [WL2]
      have hu1_sq : |u1 ζ| ^ 2 ≤ 4 * u ζ ^ 2 / ζ ^ 2 := by
        calc |u1 ζ| ^ 2 ≤ (2 * u ζ / ζ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hu1_bd 2
          _ = 4 * u ζ ^ 2 / ζ ^ 2 := by ring
      have ht1 : |2 * (132 * u ζ ^ 10 * u1 ζ ^ 2 + 12 * u ζ ^ 11 * u2 ζ)| ≤ 1104 * u ζ ^ 12 / ζ ^ 2 := by
        have h1 : |132 * u ζ ^ 10 * u1 ζ ^ 2| ≤ 528 * u ζ ^ 12 / ζ ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num), abs_pow, abs_of_pos hu_pos, abs_pow]
          calc 132 * u ζ ^ 10 * |u1 ζ| ^ 2 ≤ 132 * u ζ ^ 10 * (4 * u ζ ^ 2 / ζ ^ 2) := by gcongr
            _ = 528 * u ζ ^ 12 / ζ ^ 2 := by ring
        have h2 : |12 * u ζ ^ 11 * u2 ζ| ≤ 24 * u ζ ^ 12 / ζ ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num), abs_pow, abs_of_pos hu_pos]
          calc 12 * u ζ ^ 11 * |u2 ζ| ≤ 12 * u ζ ^ 11 * (2 * u ζ / ζ ^ 2) := by gcongr
            _ = 24 * u ζ ^ 12 / ζ ^ 2 := by ring
        rw [abs_mul, abs_of_pos zero_lt_two]
        calc 2 * |132 * u ζ ^ 10 * u1 ζ ^ 2 + 12 * u ζ ^ 11 * u2 ζ|
            ≤ 2 * (|132 * u ζ ^ 10 * u1 ζ ^ 2| + |12 * u ζ ^ 11 * u2 ζ|) :=
              mul_le_mul_of_nonneg_left (abs_add_le _ _) zero_le_two
          _ ≤ 2 * (528 * u ζ ^ 12 / ζ ^ 2 + 24 * u ζ ^ 12 / ζ ^ 2) := by gcongr
          _ = 1104 * u ζ ^ 12 / ζ ^ 2 := by ring
      have ht2 : |552 * u ζ ^ 22 * u1 ζ ^ 2 + 24 * u ζ ^ 23 * u2 ζ| ≤ 2256 * u ζ ^ 12 / ζ ^ 2 := by
        have h1 : |552 * u ζ ^ 22 * u1 ζ ^ 2| ≤ 2208 * u ζ ^ 12 / ζ ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num), abs_pow, abs_of_pos hu_pos, abs_pow]
          calc 552 * u ζ ^ 22 * |u1 ζ| ^ 2 ≤ 552 * u ζ ^ 22 * (4 * u ζ ^ 2 / ζ ^ 2) := by gcongr
            _ = 2208 * u ζ ^ 24 / ζ ^ 2 := by ring
            _ ≤ 2208 * u ζ ^ 12 / ζ ^ 2 := by gcongr
        have h2 : |24 * u ζ ^ 23 * u2 ζ| ≤ 48 * u ζ ^ 12 / ζ ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num), abs_pow, abs_of_pos hu_pos]
          calc 24 * u ζ ^ 23 * |u2 ζ| ≤ 24 * u ζ ^ 23 * (2 * u ζ / ζ ^ 2) := by gcongr
            _ = 48 * u ζ ^ 24 / ζ ^ 2 := by ring
            _ ≤ 48 * u ζ ^ 12 / ζ ^ 2 := by gcongr
        calc |552 * u ζ ^ 22 * u1 ζ ^ 2 + 24 * u ζ ^ 23 * u2 ζ|
            ≤ |552 * u ζ ^ 22 * u1 ζ ^ 2| + |24 * u ζ ^ 23 * u2 ζ| := abs_add_le _ _
          _ ≤ 2208 * u ζ ^ 12 / ζ ^ 2 + 48 * u ζ ^ 12 / ζ ^ 2 := add_le_add h1 h2
          _ = 2256 * u ζ ^ 12 / ζ ^ 2 := by ring
      calc |2 * (132 * u ζ ^ 10 * u1 ζ ^ 2 + 12 * u ζ ^ 11 * u2 ζ) -
              (552 * u ζ ^ 22 * u1 ζ ^ 2 + 24 * u ζ ^ 23 * u2 ζ)|
          ≤ |2 * (132 * u ζ ^ 10 * u1 ζ ^ 2 + 12 * u ζ ^ 11 * u2 ζ)| +
              |552 * u ζ ^ 22 * u1 ζ ^ 2 + 24 * u ζ ^ 23 * u2 ζ| := abs_sub _ _
        _ ≤ 1104 * u ζ ^ 12 / ζ ^ 2 + 2256 * u ζ ^ 12 / ζ ^ 2 := add_le_add ht1 ht2
        _ = 3360 * u ζ ^ 12 / ζ ^ 2 := by ring
        _ ≤ 3360 * taperWζ c' R ζ / ζ ^ 2 := by gcongr
    have hd_tot : HasDerivAt (taperWζ c' R) (W1 ζ) ζ := by
      rcases hle.eq_or_lt with rfl | hlt
      · have hd_WL := (hWL_derivs hζ_lo hζ_hi).1
        have hL : HasDerivWithinAt (taperWζ c' R) (WL1 (zetaR c' R)) (Iic (zetaR c' R)) (zetaR c' R) :=
          hd_WL.hasDerivWithinAt.congr (fun t ht => by
            have ht' : t ≤ zetaR c' R := ht
            unfold taperWζ; simp only [ht', ↓reduceIte, hWL_eq])
            (by unfold taperWζ; simp only [le_rfl, ↓reduceIte, hWL_eq])
        have hR' : HasDerivWithinAt (taperWζ c' R) 0 (Ici (zetaR c' R)) (zetaR c' R) := by
          refine (hasDerivWithinAt_const (zetaR c' R) _ (1 : ℝ)).congr (fun t ht => ?_) ?_
          · unfold taperWζ
            rcases eq_or_lt_of_le (ht : zetaR c' R ≤ t) with rfl | hgt
            · simp only [le_rfl, ↓reduceIte, hWL_eq, hWL_ζR]
            · simp only [not_le.mpr hgt, ↓reduceIte]
          · unfold taperWζ; simp only [le_rfl, ↓reduceIte, hWL_eq, hWL_ζR]
        rw [hWL1_ζR] at hL
        have hun := (hL.union hR').hasDerivAt (by simp [Iic_union_Ici])
        refine hun.congr_deriv ?_
        simp only [W1, le_rfl, ↓reduceIte, hWL1_ζR]
      · have hev : taperWζ c' R =ᶠ[𝓝 ζ] WL := by
          filter_upwards [Iio_mem_nhds hlt] with t ht
          unfold taperWζ; simp only [ht.le, ↓reduceIte, hWL_eq]
        have h1 := (hWL_derivs hζ_lo hζ_hi).1.congr_of_eventuallyEq hev
        refine h1.congr_deriv ?_; simp only [W1, hle, ↓reduceIte]
    refine ⟨hW_pos, hW_le1, fun _ => ⟨hW_le2u, hlo_t, hhi_t⟩, hd_tot, hW1_bd, fun hne => ?_, hW2_bd⟩
    have hlt : ζ < zetaR c' R := lt_of_le_of_ne hle hne
    have hev1 : W1 =ᶠ[𝓝 ζ] WL1 := by
      filter_upwards [Iio_mem_nhds hlt] with t ht
      simp only [W1, ht.le, ↓reduceIte]
    have h2 := (hWL_derivs hζ_lo hζ_hi).2.congr_of_eventuallyEq hev1
    refine h2.congr_deriv ?_; simp only [W2, hle, ↓reduceIte]
  · have hlt : zetaR c' R < ζ := lt_of_not_ge hle
    have hW_eq : taperWζ c' R ζ = 1 := by unfold taperWζ; simp only [hle, ↓reduceIte]
    have hd_tot : HasDerivAt (taperWζ c' R) (W1 ζ) ζ := by
      have hev : taperWζ c' R =ᶠ[𝓝 ζ] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hlt] with t ht
        unfold taperWζ; simp only [not_le.mpr ht, ↓reduceIte]
      refine (hasDerivAt_const ζ (1 : ℝ)).congr_of_eventuallyEq hev |>.congr_deriv ?_
      simp only [W1, hle, ↓reduceIte]
    have hd2_tot : HasDerivAt W1 (W2 ζ) ζ := by
      have hev1 : W1 =ᶠ[𝓝 ζ] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hlt] with t ht
        simp only [W1, not_le.mpr ht, ↓reduceIte]
      refine (hasDerivAt_const ζ (0 : ℝ)).congr_of_eventuallyEq hev1 |>.congr_deriv ?_
      simp only [W2, hle, ↓reduceIte]
    have hζ_pos : 0 < ζ := by linarith only [hzmin_ge, hζ_lo]
    have hW1_bd : |W1 ζ| ≤ 96 * taperWζ c' R ζ / ζ := by
      simp only [W1, hle, ↓reduceIte, abs_zero, hW_eq]; positivity
    have hW2_bd : |W2 ζ| ≤ 3360 * taperWζ c' R ζ / ζ ^ 2 := by
      simp only [W2, hle, ↓reduceIte, abs_zero, hW_eq]; positivity
    exact ⟨by rw [hW_eq]; exact zero_lt_one, by rw [hW_eq], fun h => (hle h).elim, hd_tot,
      hW1_bd, fun _ => hd2_tot, hW2_bd⟩

/-! ### 4. Global `C^1` + piecewise-`C^2` bounds and window comparability for `lowerPζ` -/

theorem lowerPζ_properties :
    ∃ c_T C_P : ℝ, taperC0 ≤ c_T ∧ 0 < C_P ∧
      ∀ {c' R : ℝ}, c_T ≤ c' → LowerRadiusRange virasoroC1 c' R →
        ∃ P1 P2 : ℝ → ℝ,
          ContinuousOn P1 (Ici (zetaMin c' / 2)) ∧
          (∀ {ζ : ℝ}, zetaMin c' / 2 ≤ ζ →
            0 < lowerPζ c' R ζ ∧
            HasDerivAt (lowerPζ c' R) (P1 ζ) ζ ∧
            |P1 ζ| ≤ C_P * lowerPζ c' R ζ / ζ ∧
            (ζ ≠ zetaR c' R → HasDerivAt P1 (P2 ζ) ζ) ∧
            |P2 ζ| ≤ C_P * lowerPζ c' R ζ / ζ ^ 2) ∧
          (∀ {ζ₁ ζ₂ : ℝ}, zetaMin c' / 2 ≤ ζ₁ → zetaMin c' / 2 ≤ ζ₂ →
            |ζ₁ - ζ₂| ≤ 8 * Real.log c' + 1 →
            lowerPζ c' R ζ₁ ≤ 2 * lowerPζ c' R ζ₂) := by
  obtain ⟨C_P0, hCP0_pos, hP0_deriv⟩ := lowerP0_deriv_bounds
  let C_P : ℝ := 3360 + 193 * C_P0 + 96
  have hCP_pos : 0 < C_P := by positivity
  have ht_lim : Tendsto (fun c' : ℝ => (8 * Real.log c' + 1) * (2 * C_P) / zetaMin c')
      atTop (𝓝 0) := by
    have hpi := Real.pi_pos
    have hlog_bd : ∀ᶠ c' : ℝ in atTop,
        0 ≤ (8 * Real.log c' + 1) * (2 * C_P) / zetaMin c' ∧
        (8 * Real.log c' + 1) * (2 * C_P) / zetaMin c' ≤
          (12 * π * 17 * (2 * C_P)) * c' ^ (-(17 / 28 : ℝ)) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc1
      have hc0 : 0 < c' := by linarith
      have hlog : Real.log c' ≤ 4 * c' ^ (1 / 4 : ℝ) := by
        have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc0 (1 / 4 : ℝ))
        rw [Real.log_rpow hc0] at h
        linarith only [h]
      have h14 : 1 ≤ c' ^ (1 / 4 : ℝ) := Real.one_le_rpow hc1 (by norm_num)
      refine ⟨by have := Real.log_nonneg hc1; have := zetaMin_pos hc0; positivity, ?_⟩
      have h3 : 3 * π / 2 * 33 * (2 * C_P) ≤ 12 * π * 17 * (2 * C_P) := by
        nlinarith only [hpi, hCP_pos]
      have hpow_neg : c' ^ (-(17 / 28 : ℝ)) = c' ^ (1 / 4 : ℝ) * c' ^ (-(6 / 7 : ℝ)) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have hnum_le : 8 * Real.log c' + 1 ≤ 8 * (4 * c' ^ (1 / 4 : ℝ)) + c' ^ (1 / 4 : ℝ) := by
        linarith only [hlog, h14]
      calc (8 * Real.log c' + 1) * (2 * C_P) / zetaMin c'
          ≤ (8 * (4 * c' ^ (1 / 4 : ℝ)) + c' ^ (1 / 4 : ℝ)) * (2 * C_P) / ((2 / (3 * π)) * c' ^ (6 / 7 : ℝ)) := by
            unfold zetaMin; gcongr
        _ = (3 * π / 2 * 33 * (2 * C_P)) * (c' ^ (1 / 4 : ℝ) * c' ^ (-(6 / 7 : ℝ))) := by
            rw [Real.rpow_neg hc0.le]; field_simp [Real.pi_ne_zero]; ring
        _ ≤ (12 * π * 17 * (2 * C_P)) * (c' ^ (1 / 4 : ℝ) * c' ^ (-(6 / 7 : ℝ))) := by gcongr
        _ = (12 * π * 17 * (2 * C_P)) * c' ^ (-(17 / 28 : ℝ)) := by rw [← hpow_neg]
    have hlim0 : Tendsto (fun c' : ℝ => (12 * π * 17 * (2 * C_P)) * c' ^ (-(17 / 28 : ℝ)))
        atTop (𝓝 0) := by
      have h17 : (0 : ℝ) < 17 / 28 := by norm_num
      simpa only [mul_zero] using (tendsto_rpow_neg_atTop h17).const_mul (12 * π * 17 * (2 * C_P))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim0
      (Filter.Eventually.mono hlog_bd fun _ h => h.1)
      (Filter.Eventually.mono hlog_bd fun _ h => h.2)
  have hev_log : ∀ᶠ c' : ℝ in atTop,
      (8 * Real.log c' + 1) * (2 * C_P) / zetaMin c' ≤ Real.log 2 :=
    ht_lim.eventually (Iic_mem_nhds (Real.log_pos one_lt_two))
  rw [eventually_atTop] at hev_log
  obtain ⟨c_L, hc_L⟩ := hev_log
  refine ⟨max taperC0 c_L, C_P, le_max_left _ _, hCP_pos, fun {c' R} hc' hR => ?_⟩
  have hcT : taperC0 ≤ c' := (le_max_left _ _).trans hc'
  have hcL : c_L ≤ c' := (le_max_right _ _).trans hc'
  have hc0 : 0 < c' := by linarith [taperC0_ge]
  obtain ⟨W1, W2, hcont_W1, hW_spec⟩ := taperWζ_bounds_and_derivs hcT hR
  obtain ⟨_, _, _, _, hzmin_ge, _⟩ := zetaR_bounds hcT hR
  let P0 := lowerP0 c'
  let P01 := lowerP0Deriv1 c'
  let P02 := lowerP0Deriv2 c'
  let P1 : ℝ → ℝ := fun ζ => W1 ζ * P0 ζ + taperWζ c' R ζ * P01 ζ
  let P2 : ℝ → ℝ := fun ζ => W2 ζ * P0 ζ + 2 * W1 ζ * P01 ζ + taperWζ c' R ζ * P02 ζ
  have hev_eq : ∀ {ζ : ℝ}, zetaMin c' / 2 ≤ ζ → lowerPζ c' R =ᶠ[𝓝 ζ] fun t => taperWζ c' R t * P0 t := by
    intro ζ hζ
    have hζ_pos : 0 < ζ := by linarith only [hzmin_ge, hζ]
    filter_upwards [Ioi_mem_nhds hζ_pos] with t ht
    unfold lowerPζ P0
    rw [lowerTaper_zeta_eq hcT hR ht]
  have hcont_P1 : ContinuousOn P1 (Ici (zetaMin c' / 2)) := by
    have hW_cont : ContinuousOn (taperWζ c' R) (Ici (zetaMin c' / 2)) := fun z hz =>
      (hW_spec hz).2.2.2.1.continuousAt.continuousWithinAt
    have hP0_cont : ContinuousOn P0 (Ici (zetaMin c' / 2)) := fun z hz => by
      have hz' : zetaMin c' / 2 ≤ z := hz
      exact (hP0_deriv hc0 (by linarith only [hzmin_ge, hz'])).1.continuousAt.continuousWithinAt
    have hP01_cont : ContinuousOn P01 (Ici (zetaMin c' / 2)) := fun z hz => by
      have hz' : zetaMin c' / 2 ≤ z := hz
      exact (hP0_deriv hc0 (by linarith only [hzmin_ge, hz'])).2.1.continuousAt.continuousWithinAt
    exact (hcont_W1.mul hP0_cont).add (hW_cont.mul hP01_cont)
  have hP_pt : ∀ {ζ : ℝ}, zetaMin c' / 2 ≤ ζ →
      0 < lowerPζ c' R ζ ∧
      HasDerivAt (lowerPζ c' R) (P1 ζ) ζ ∧
      |P1 ζ| ≤ C_P * lowerPζ c' R ζ / ζ ∧
      (ζ ≠ zetaR c' R → HasDerivAt P1 (P2 ζ) ζ) ∧
      |P2 ζ| ≤ C_P * lowerPζ c' R ζ / ζ ^ 2 := by
    intro ζ hζ
    have hζ_pos : 0 < ζ := by linarith only [hzmin_ge, hζ]
    obtain ⟨hW_pos, _, _, hd_W, hW1_bd, hW_c2, hW2_bd⟩ := hW_spec hζ
    obtain ⟨hd_P0, hd_P01, hP01_bd, hP02_bd⟩ := hP0_deriv hc0 hζ_pos
    have hP0_pos : 0 < P0 ζ := lowerP0_pos hc0 hζ_pos
    have hP_eq : lowerPζ c' R ζ = taperWζ c' R ζ * P0 ζ := by
      unfold lowerPζ P0; rw [lowerTaper_zeta_eq hcT hR hζ_pos]
    have hP_pos : 0 < lowerPζ c' R ζ := by rw [hP_eq]; exact mul_pos hW_pos hP0_pos
    have hd_P : HasDerivAt (lowerPζ c' R) (P1 ζ) ζ :=
      (hd_W.mul hd_P0).congr_of_eventuallyEq (hev_eq hζ)
    have hP1_bd : |P1 ζ| ≤ C_P * lowerPζ c' R ζ / ζ := by
      have h1 : |W1 ζ * P0 ζ| ≤ 96 * (taperWζ c' R ζ * P0 ζ) / ζ := by
        rw [abs_mul, abs_of_pos hP0_pos]
        calc |W1 ζ| * P0 ζ ≤ (96 * taperWζ c' R ζ / ζ) * P0 ζ := by gcongr
          _ = 96 * (taperWζ c' R ζ * P0 ζ) / ζ := by ring
      have h2 : |taperWζ c' R ζ * P01 ζ| ≤ C_P0 * (taperWζ c' R ζ * P0 ζ) / ζ := by
        rw [abs_mul, abs_of_pos hW_pos]
        calc taperWζ c' R ζ * |P01 ζ| ≤ taperWζ c' R ζ * (C_P0 * P0 ζ / ζ) := by gcongr
          _ = C_P0 * (taperWζ c' R ζ * P0 ζ) / ζ := by ring
      calc |P1 ζ| ≤ _ + _ := by dsimp [P1]; exact abs_add_le _ _
        _ ≤ 96 * (taperWζ c' R ζ * P0 ζ) / ζ + C_P0 * (taperWζ c' R ζ * P0 ζ) / ζ := add_le_add h1 h2
        _ = (96 + C_P0) * lowerPζ c' R ζ / ζ := by rw [← hP_eq]; ring
        _ ≤ C_P * lowerPζ c' R ζ / ζ := by
            gcongr; dsimp [C_P]; linarith only [hCP0_pos]
    have hd_P1 : ζ ≠ zetaR c' R → HasDerivAt P1 (P2 ζ) ζ := fun hne => by
      have hd_W1 := hW_c2 hne
      have h1 := hd_W1.mul hd_P0
      have h2 := hd_W.mul hd_P01
      refine (h1.add h2).congr_deriv ?_
      dsimp [P2]; ring
    have hP2_bd : |P2 ζ| ≤ C_P * lowerPζ c' R ζ / ζ ^ 2 := by
      have h1 : |W2 ζ * P0 ζ| ≤ 3360 * (taperWζ c' R ζ * P0 ζ) / ζ ^ 2 := by
        rw [abs_mul, abs_of_pos hP0_pos]
        calc |W2 ζ| * P0 ζ ≤ (3360 * taperWζ c' R ζ / ζ ^ 2) * P0 ζ := by gcongr
          _ = 3360 * (taperWζ c' R ζ * P0 ζ) / ζ ^ 2 := by ring
      have h2 : |2 * W1 ζ * P01 ζ| ≤ 192 * C_P0 * (taperWζ c' R ζ * P0 ζ) / ζ ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos zero_lt_two]
        calc 2 * |W1 ζ| * |P01 ζ|
            ≤ 2 * (96 * taperWζ c' R ζ / ζ) * (C_P0 * P0 ζ / ζ) := by gcongr
          _ = 192 * C_P0 * (taperWζ c' R ζ * P0 ζ) / ζ ^ 2 := by ring
      have h3 : |taperWζ c' R ζ * P02 ζ| ≤ C_P0 * (taperWζ c' R ζ * P0 ζ) / ζ ^ 2 := by
        rw [abs_mul, abs_of_pos hW_pos]
        calc taperWζ c' R ζ * |P02 ζ| ≤ taperWζ c' R ζ * (C_P0 * P0 ζ / ζ ^ 2) := by gcongr
          _ = C_P0 * (taperWζ c' R ζ * P0 ζ) / ζ ^ 2 := by ring
      have htri := (abs_add_le (W2 ζ * P0 ζ + 2 * W1 ζ * P01 ζ) (taperWζ c' R ζ * P02 ζ)).trans
        (add_le_add (abs_add_le _ _) le_rfl)
      dsimp [P2]
      calc |W2 ζ * P0 ζ + 2 * W1 ζ * P01 ζ + taperWζ c' R ζ * P02 ζ|
          ≤ 3360 * (taperWζ c' R ζ * P0 ζ) / ζ ^ 2 +
              192 * C_P0 * (taperWζ c' R ζ * P0 ζ) / ζ ^ 2 +
              C_P0 * (taperWζ c' R ζ * P0 ζ) / ζ ^ 2 := by linarith only [htri, h1, h2, h3]
        _ = (3360 + 193 * C_P0) * lowerPζ c' R ζ / ζ ^ 2 := by rw [← hP_eq]; ring
        _ ≤ C_P * lowerPζ c' R ζ / ζ ^ 2 := by gcongr; dsimp [C_P]; linarith
    exact ⟨hP_pos, hd_P, hP1_bd, hd_P1, hP2_bd⟩
  refine ⟨P1, P2, hcont_P1, hP_pt, fun {ζ₁ ζ₂} hζ₁ hζ₂ hdist => ?_⟩
  rcases eq_or_ne ζ₁ ζ₂ with rfl | hne
  · linarith only [(hP_pt hζ₁).1]
  have hdiff_log : ∀ {a b : ℝ}, zetaMin c' / 2 ≤ a → a < b →
      |Real.log (lowerPζ c' R b) - Real.log (lowerPζ c' R a)| ≤
        (b - a) * (2 * C_P) / zetaMin c' := by
    intro a b ha hab
    have hcont_log : ContinuousOn (fun t => Real.log (lowerPζ c' R t)) (Icc a b) := fun z hz =>
      ((hP_pt (ha.trans hz.1)).2.1.continuousAt.log (hP_pt (ha.trans hz.1)).1.ne').continuousWithinAt
    have hderiv_log : ∀ z ∈ Ioo a b,
        HasDerivAt (fun t => Real.log (lowerPζ c' R t)) (P1 z / lowerPζ c' R z) z := fun z hz =>
      (hP_pt (ha.trans hz.1.le)).2.1.log (hP_pt (ha.trans hz.1.le)).1.ne'
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => Real.log (lowerPζ c' R t))
      (fun t => P1 t / lowerPζ c' R t) hab hcont_log hderiv_log
    have hξ_lo : zetaMin c' / 2 ≤ ξ := ha.trans hξ.1.le
    have hPξ_pos : 0 < lowerPζ c' R ξ := (hP_pt hξ_lo).1
    have hrat : |P1 ξ / lowerPζ c' R ξ| ≤ 2 * C_P / zetaMin c' := by
      rw [abs_div, abs_of_pos hPξ_pos]
      calc |P1 ξ| / lowerPζ c' R ξ ≤ (C_P * lowerPζ c' R ξ / ξ) / lowerPζ c' R ξ := by
            gcongr; exact (hP_pt hξ_lo).2.2.1
        _ = C_P / ξ := by field_simp [hPξ_pos.ne']
        _ ≤ C_P / (zetaMin c' / 2) := by gcongr
        _ = 2 * C_P / zetaMin c' := by ring
    have heq : Real.log (lowerPζ c' R b) - Real.log (lowerPζ c' R a) =
        (P1 ξ / lowerPζ c' R ξ) * (b - a) := by
      rw [hslope, div_mul_cancel₀ _ (sub_pos.mpr hab).ne']
    rw [heq, abs_mul, abs_of_pos (sub_pos.mpr hab)]
    calc |P1 ξ / lowerPζ c' R ξ| * (b - a) ≤ (2 * C_P / zetaMin c') * (b - a) := by gcongr
      _ = (b - a) * (2 * C_P) / zetaMin c' := by ring
  have hlog_le : Real.log (lowerPζ c' R ζ₁) - Real.log (lowerPζ c' R ζ₂) ≤ Real.log 2 := by
    have hcL_bd := hc_L c' hcL
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hbd := hdiff_log hζ₁ hlt
      have hsub : ζ₂ - ζ₁ ≤ 8 * Real.log c' + 1 := by linarith only [(abs_le.mp hdist).1]
      have hle : |Real.log (lowerPζ c' R ζ₂) - Real.log (lowerPζ c' R ζ₁)| ≤ Real.log 2 := by
        calc |Real.log (lowerPζ c' R ζ₂) - Real.log (lowerPζ c' R ζ₁)|
            ≤ (ζ₂ - ζ₁) * (2 * C_P) / zetaMin c' := hbd
          _ ≤ (8 * Real.log c' + 1) * (2 * C_P) / zetaMin c' := by gcongr
          _ ≤ Real.log 2 := hcL_bd
      linarith only [(abs_le.mp hle).1]
    · have hbd := hdiff_log hζ₂ hlt
      have hsub : ζ₁ - ζ₂ ≤ 8 * Real.log c' + 1 := by linarith only [(abs_le.mp hdist).2]
      have hle : |Real.log (lowerPζ c' R ζ₁) - Real.log (lowerPζ c' R ζ₂)| ≤ Real.log 2 := by
        calc |Real.log (lowerPζ c' R ζ₁) - Real.log (lowerPζ c' R ζ₂)|
            ≤ (ζ₁ - ζ₂) * (2 * C_P) / zetaMin c' := hbd
          _ ≤ (8 * Real.log c' + 1) * (2 * C_P) / zetaMin c' := by gcongr
          _ ≤ Real.log 2 := hcL_bd
      linarith only [(abs_le.mp hle).2]
  have hP1_pos : 0 < lowerPζ c' R ζ₁ := (hP_pt hζ₁).1
  have hP2_pos : 0 < lowerPζ c' R ζ₂ := (hP_pt hζ₂).1
  have hlog_div : Real.log (lowerPζ c' R ζ₁ / lowerPζ c' R ζ₂) ≤ Real.log 2 := by
    rw [Real.log_div hP1_pos.ne' hP2_pos.ne']
    exact hlog_le
  have hdiv_le : lowerPζ c' R ζ₁ / lowerPζ c' R ζ₂ ≤ 2 :=
    (Real.log_le_log_iff (div_pos hP1_pos hP2_pos) zero_lt_two).mp hlog_div
  rwa [div_le_iff₀ hP2_pos] at hdiv_le

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerPζ_properties' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerPζ_properties
