module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasSlitPJ

/-!
# Uniform `slitEntropy` bound on `lowerBoasRightDom`

* `slitEntropy_le_of_confB`:
  `slitEntropy z₀.re z₀.im ≤ 35 + 2 log (1 / |Im(confB z₀)|)` when `Re(confB z₀) > ξ_*` and `0 < |Im(confB z₀)| ≤ 1/4`.
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.TipFront

noncomputable section

private lemma pkernel_mul_invJacobian_right {z₀ : ℂ} (hz₀ : 0 < z₀.im) (hz_le2 : ‖z₀‖ ≤ 2)
    {M_z : ℝ} (hMz : ‖z₀ * (z₀ + 1)‖ / z₀.im ≤ M_z) (hMz_nn : 0 ≤ M_z)
    {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 0) (hne : u ≠ sigmaStar) :
    poissonKernel z₀.re z₀.im u * invJacobian u ≤ (4 * (M_z + 4)) / |u - sigmaStar| := by
  have hu_pos : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h1u : |1 - u| ≤ 2 := by rw [abs_of_pos (by linarith [hu.2])]; linarith [hu.1]
  have hplus : 2 ≤ |u - sigmaPlus| := by
    rw [abs_of_neg (by linarith [hu.2, sigmaPlus_gt_two])]
    linarith [hu.2, sigmaPlus_gt_two]
  have hstar_pos : 0 < |u - sigmaStar| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hden_eq : (u - z₀.re) ^ 2 + z₀.im ^ 2 = ‖(u : ℂ) - z₀‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp; ring
  have huz_ge : z₀.im ≤ ‖(u : ℂ) - z₀‖ := by
    have h1 : |((u : ℂ) - z₀).im| = z₀.im := by
      simp [abs_of_pos hz₀]
    rw [← h1]
    exact Complex.abs_im_le_norm _
  have hu_sub_z : ‖(u : ℂ) * ((u : ℂ) + 1)‖ ≤ ‖z₀ * (z₀ + 1)‖ + 4 * ‖(u : ℂ) - z₀‖ := by
    have hid : (u : ℂ) * ((u : ℂ) + 1) = z₀ * (z₀ + 1) + ((u : ℂ) - z₀) * ((u : ℂ) + z₀ + 1) := by ring
    have h4 : ‖(u : ℂ) + z₀ + 1‖ ≤ 4 := by
      have hu1 : ‖(u : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real] using hu_pos
      have h11 : ‖(1 : ℂ)‖ = 1 := norm_one
      have htri1 := norm_add_le ((u : ℂ) + z₀) 1
      have htri2 := norm_add_le (u : ℂ) z₀
      linarith
    calc ‖(u : ℂ) * ((u : ℂ) + 1)‖
        ≤ ‖z₀ * (z₀ + 1)‖ + ‖((u : ℂ) - z₀) * ((u : ℂ) + z₀ + 1)‖ := by rw [hid]; exact norm_add_le _ _
      _ = ‖z₀ * (z₀ + 1)‖ + ‖(u : ℂ) - z₀‖ * ‖(u : ℂ) + z₀ + 1‖ := by congr 1; exact norm_mul _ _
      _ ≤ ‖z₀ * (z₀ + 1)‖ + ‖(u : ℂ) - z₀‖ * 4 := by gcongr
      _ = ‖z₀ * (z₀ + 1)‖ + 4 * ‖(u : ℂ) - z₀‖ := by ring
  have hprod_eq : |u * (u ^ 2 - 1)| = ‖(u : ℂ) * ((u : ℂ) + 1)‖ * |1 - u| := by
    rw [show u * (u ^ 2 - 1) = -((u * (u + 1)) * (1 - u)) by ring, abs_neg, abs_mul,
      show ‖(u : ℂ) * ((u : ℂ) + 1)‖ = |u * (u + 1)| by
        rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.norm_real,
          Real.norm_eq_abs]]
  have huz_pos : 0 < ‖(u : ℂ) - z₀‖ := hz₀.trans_le huz_ge
  have hP_bd : poissonKernel z₀.re z₀.im u * ‖(u : ℂ) * ((u : ℂ) + 1)‖ ≤
      (M_z + 4) / π := by
    unfold poissonKernel
    rw [hden_eq, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) Real.pi_pos]
    have hzm : ‖z₀ * (z₀ + 1)‖ ≤ M_z * z₀.im := (div_le_iff₀ hz₀).mp hMz
    have hterm1 : z₀.im * ‖z₀ * (z₀ + 1)‖ * π ≤ (M_z * z₀.im ^ 2) * π := by
      have : z₀.im * ‖z₀ * (z₀ + 1)‖ ≤ M_z * z₀.im ^ 2 := by nlinarith [hz₀]
      exact mul_le_mul_of_nonneg_right this Real.pi_pos.le
    have hterm1' : (M_z * z₀.im ^ 2) * π ≤ M_z * ‖(u : ℂ) - z₀‖ ^ 2 * π := by
      have : z₀.im ^ 2 ≤ ‖(u : ℂ) - z₀‖ ^ 2 := pow_le_pow_left₀ hz₀.le huz_ge 2
      have : M_z * z₀.im ^ 2 ≤ M_z * ‖(u : ℂ) - z₀‖ ^ 2 := mul_le_mul_of_nonneg_left this hMz_nn
      exact mul_le_mul_of_nonneg_right this Real.pi_pos.le
    have hterm2 : z₀.im * (4 * ‖(u : ℂ) - z₀‖) * π ≤ 4 * ‖(u : ℂ) - z₀‖ ^ 2 * π := by
      have : z₀.im * ‖(u : ℂ) - z₀‖ ≤ ‖(u : ℂ) - z₀‖ ^ 2 := by
        calc z₀.im * ‖(u : ℂ) - z₀‖ ≤ ‖(u : ℂ) - z₀‖ * ‖(u : ℂ) - z₀‖ :=
              mul_le_mul_of_nonneg_right huz_ge (norm_nonneg _)
          _ = _ := (sq _).symm
      nlinarith [Real.pi_pos]
    calc z₀.im * ‖(u : ℂ) * ((u : ℂ) + 1)‖ * π
        ≤ z₀.im * (‖z₀ * (z₀ + 1)‖ + 4 * ‖(u : ℂ) - z₀‖) * π := by gcongr
      _ = z₀.im * ‖z₀ * (z₀ + 1)‖ * π + z₀.im * (4 * ‖(u : ℂ) - z₀‖) * π := by ring
      _ ≤ M_z * ‖(u : ℂ) - z₀‖ ^ 2 * π + 4 * ‖(u : ℂ) - z₀‖ ^ 2 * π :=
            add_le_add (hterm1.trans hterm1') hterm2
      _ = (M_z + 4) * (π * ‖(u : ℂ) - z₀‖ ^ 2) := by ring
  unfold invJacobian
  rw [hprod_eq]
  have h1 : poissonKernel z₀.re z₀.im u *
      (2 * π * (‖(u : ℂ) * ((u : ℂ) + 1)‖ * |1 - u|) / (|u - sigmaStar| * |u - sigmaPlus|)) =
      (poissonKernel z₀.re z₀.im u * ‖(u : ℂ) * ((u : ℂ) + 1)‖) *
        (2 * π * |1 - u| / (|u - sigmaStar| * |u - sigmaPlus|)) := by ring
  rw [h1]
  have h2 : 2 * π * |1 - u| / (|u - sigmaStar| * |u - sigmaPlus|) ≤ (2 * π) / |u - sigmaStar| := by
    rw [div_le_div_iff₀ (mul_pos hstar_pos (by linarith)) hstar_pos]
    calc 2 * π * |1 - u| * |u - sigmaStar| ≤ 2 * π * 2 * |u - sigmaStar| := by gcongr
      _ = 2 * π * (|u - sigmaStar| * 2) := by ring
      _ ≤ 2 * π * (|u - sigmaStar| * |u - sigmaPlus|) := by gcongr
  have hp_nn : 0 ≤ poissonKernel z₀.re z₀.im u * ‖(u : ℂ) * ((u : ℂ) + 1)‖ :=
    mul_nonneg (poissonKernel_nonneg hz₀.le u) (norm_nonneg _)
  calc (poissonKernel z₀.re z₀.im u * ‖(u : ℂ) * ((u : ℂ) + 1)‖) *
        (2 * π * |1 - u| / (|u - sigmaStar| * |u - sigmaPlus|))
      ≤ ((M_z + 4) / π) * ((2 * π) / |u - sigmaStar|) :=
        mul_le_mul hP_bd h2 (by positivity) (by positivity)
    _ = (2 * (M_z + 4)) / |u - sigmaStar| := by field_simp [Real.pi_pos.ne']
    _ ≤ (4 * (M_z + 4)) / |u - sigmaStar| := by gcongr; norm_num

private lemma leftSlitEntropy_le_of_confB {z₀ : ℂ} (hz₀ : 0 < z₀.im)
    (hre_le : z₀.re ≤ 1 / 2) (hy₀_le : z₀.im ≤ 0.85) :
    leftSlitEntropy z₀.re z₀.im ≤ 14 := by
  have hP_tail : ∀ τ : ℝ, 1 < τ → poissonKernel z₀.re z₀.im τ ≤ 4 * z₀.im / (π * τ ^ 2) := by
    intro τ hτ
    unfold poissonKernel
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hτ2 : τ / 2 ≤ τ - z₀.re := by linarith
    have hsq : τ ^ 2 / 4 ≤ (τ - z₀.re) ^ 2 := by nlinarith
    have hpi := Real.pi_pos
    have hpi_sq : π * (τ ^ 2 / 4) ≤ π * ((τ - z₀.re) ^ 2 + z₀.im ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith [sq_nonneg z₀.im]) hpi.le
    calc z₀.im * (π * τ ^ 2) = 4 * z₀.im * (π * (τ ^ 2 / 4)) := by ring
      _ ≤ 4 * z₀.im * (π * ((τ - z₀.re) ^ 2 + z₀.im ^ 2)) :=
          mul_le_mul_of_nonneg_left hpi_sq (by linarith)
  have hleft_dens : ∀ σ : ℝ, 1 < σ →
      leftSlitDensity z₀.re z₀.im σ ≤
        (if σ ≤ 4 then 250 / |σ - sigmaPlus| else 60) := by
    intro σ hσ1
    let τ := leftSlitInv σ
    have hτ1 : 1 < τ := by
      change 1 < (σ + 1) / (σ - 1)
      rw [lt_div_iff₀ (by linarith)]; linarith
    have hτ_term : poissonKernel z₀.re z₀.im τ * invJacobian τ ≤
        (if σ ≤ 4 then 70 / |σ - sigmaPlus| else 50) := by
      by_cases hsp : σ = sigmaPlus
      · subst hsp
        have hτsp_eq : τ = sigmaPlus := by
          change (sigmaPlus + 1) / (sigmaPlus - 1) = sigmaPlus
          unfold sigmaPlus
          have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          field_simp [show √2 ≠ 0 by positivity]; nlinarith [hsq]
        rw [hτsp_eq]
        unfold invJacobian; simp only [sub_self, abs_zero, mul_zero, div_zero]
        split_ifs <;> positivity
      · have hτsp : τ ≠ sigmaPlus := by
          intro heq
          apply hsp
          have hinv : leftSlitInv (leftSlitInv σ) = σ := by
            unfold leftSlitInv; field_simp [show σ - 1 ≠ 0 by linarith]; ring
          rw [← hinv, show leftSlitInv σ = τ by rfl, heq]
          unfold leftSlitInv sigmaPlus
          have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          field_simp [show √2 ≠ 0 by positivity]; nlinarith [hsq]
        have hinv_le : invJacobian τ ≤ 4 * π * τ * (τ - 1) / |τ - sigmaPlus| := by
          unfold invJacobian
          have hstar : 0 < τ - sigmaStar := by linarith [sigmaStar_neg]
          rw [abs_of_pos (mul_pos (by linarith) (by nlinarith)), abs_of_pos hstar,
            show τ ^ 2 - 1 = (τ - 1) * (τ + 1) by ring]
          have h2 : τ / (τ - sigmaStar) ≤ 1 := (div_le_one hstar).mpr (by linarith [sigmaStar_neg])
          have h1 : τ + 1 ≤ 2 * τ := by linarith
          have hp : 0 < |τ - sigmaPlus| := abs_pos.mpr (sub_ne_zero.mpr hτsp)
          calc 2 * π * (τ * ((τ - 1) * (τ + 1))) / ((τ - sigmaStar) * |τ - sigmaPlus|)
              = (τ / (τ - sigmaStar)) * (2 * π * (τ - 1) * (τ + 1) / |τ - sigmaPlus|) := by
                  field_simp [hstar.ne', hp.ne']
            _ ≤ 1 * (2 * π * (τ - 1) * (2 * τ) / |τ - sigmaPlus|) := by gcongr
            _ = 4 * π * τ * (τ - 1) / |τ - sigmaPlus| := by ring
        have hP := hP_tail τ hτ1
        have hprod : poissonKernel z₀.re z₀.im τ * invJacobian τ ≤
            16 * z₀.im * ((τ - 1) / (τ * |τ - sigmaPlus|)) := by
          calc poissonKernel z₀.re z₀.im τ * invJacobian τ
              ≤ (4 * z₀.im / (π * τ ^ 2)) * (4 * π * τ * (τ - 1) / |τ - sigmaPlus|) :=
                mul_le_mul hP hinv_le (by unfold invJacobian; positivity) (by positivity)
            _ = 16 * z₀.im * ((τ - 1) / (τ * |τ - sigmaPlus|)) := by
                field_simp [Real.pi_pos.ne', (by linarith : τ ≠ 0)]; ring
        have hratio_τ : (τ - 1) / |τ - sigmaPlus| ≤ 5 / |σ - sigmaPlus| := by
          have hτ_m1 : τ - 1 = 2 / (σ - 1) := by
            unfold τ leftSlitInv; field_simp [show σ - 1 ≠ 0 by linarith]; ring
          have hτ_sp : τ - sigmaPlus = (-√2) * (σ - sigmaPlus) / (σ - 1) := by
            unfold τ leftSlitInv sigmaPlus
            have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
            field_simp [show σ - 1 ≠ 0 by linarith]
            ring_nf
            rw [hsq]
            ring
          rw [hτ_m1, hτ_sp, abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < √2),
            abs_of_pos (by linarith : 0 < σ - 1)]
          have hsp_pos : 0 < |σ - sigmaPlus| := abs_pos.mpr (sub_ne_zero.mpr hsp)
          rw [div_div_eq_mul_div, div_mul_cancel₀ _ (by linarith : σ - 1 ≠ 0)]
          rw [div_le_div_iff₀ (mul_pos (by positivity) hsp_pos) hsp_pos]
          have h5_ge : 2 ≤ 5 * √2 := by linarith only [sqrt2_gt_slit]
          nlinarith only [h5_ge, hsp_pos]
        have hτ_div : (τ - 1) / (τ * |τ - sigmaPlus|) ≤ 5 / |σ - sigmaPlus| := by
          calc (τ - 1) / (τ * |τ - sigmaPlus|) = ((τ - 1) / |τ - sigmaPlus|) / τ := by ring
            _ ≤ (5 / |σ - sigmaPlus|) / 1 := div_le_div₀ (by positivity) hratio_τ (by norm_num) (by linarith)
            _ = 5 / |σ - sigmaPlus| := div_one _
        have h70 : poissonKernel z₀.re z₀.im τ * invJacobian τ ≤ 70 / |σ - sigmaPlus| := by
          calc poissonKernel z₀.re z₀.im τ * invJacobian τ
              ≤ 16 * z₀.im * (5 / |σ - sigmaPlus|) :=
                hprod.trans (mul_le_mul_of_nonneg_left hτ_div (by positivity))
            _ ≤ 16 * 0.85 * (5 / |σ - sigmaPlus|) := by gcongr
            _ = 68 / |σ - sigmaPlus| := by ring
            _ ≤ 70 / |σ - sigmaPlus| := by gcongr; norm_num
        split_ifs with hσ4
        · exact h70
        · have hsp_ge : 1.5 ≤ |σ - sigmaPlus| := by
            have h1 := not_le.mp hσ4
            rw [abs_of_pos (by linarith [sigmaPlus_lt_242])]
            linarith [sigmaPlus_lt_242]
          calc poissonKernel z₀.re z₀.im τ * invJacobian τ ≤ 70 / |σ - sigmaPlus| := h70
            _ ≤ 70 / 1.5 := by gcongr
            _ ≤ 50 := by norm_num
    have hσ_term : poissonKernel z₀.re z₀.im σ * invJacobian σ ≤
        (if σ ≤ 4 then 180 / |σ - sigmaPlus| else 10) := by
      by_cases hsp : σ = sigmaPlus
      · subst hsp; unfold invJacobian; simp only [sub_self, abs_zero, mul_zero, div_zero]
        split_ifs <;> positivity
      · have hsp_pos : 0 < |σ - sigmaPlus| := abs_pos.mpr (sub_ne_zero.mpr hsp)
        split_ifs with hσ4
        · have hinv_le : invJacobian σ ≤ 4 * π * σ * (σ - 1) / |σ - sigmaPlus| := by
            unfold invJacobian
            have hstar : 0 < σ - sigmaStar := by linarith [sigmaStar_neg]
            rw [abs_of_pos (mul_pos (by linarith) (by nlinarith)), abs_of_pos hstar,
              show σ ^ 2 - 1 = (σ - 1) * (σ + 1) by ring]
            have h2 : σ / (σ - sigmaStar) ≤ 1 := (div_le_one hstar).mpr (by linarith [sigmaStar_neg])
            have h1 : σ + 1 ≤ 2 * σ := by linarith
            calc 2 * π * (σ * ((σ - 1) * (σ + 1))) / ((σ - sigmaStar) * |σ - sigmaPlus|)
                = (σ / (σ - sigmaStar)) * (2 * π * (σ - 1) * (σ + 1) / |σ - sigmaPlus|) := by
                    field_simp [hstar.ne', hsp_pos.ne']
              _ ≤ 1 * (2 * π * (σ - 1) * (2 * σ) / |σ - sigmaPlus|) := by gcongr
              _ = 4 * π * σ * (σ - 1) / |σ - sigmaPlus| := by ring
          have hP := hP_tail σ hσ1
          calc poissonKernel z₀.re z₀.im σ * invJacobian σ
              ≤ (4 * z₀.im / (π * σ ^ 2)) * (4 * π * σ * (σ - 1) / |σ - sigmaPlus|) :=
                mul_le_mul hP hinv_le (by unfold invJacobian; positivity) (by positivity)
            _ = 16 * z₀.im * ((σ - 1) / σ) / |σ - sigmaPlus| := by
                field_simp [Real.pi_pos.ne', (by linarith : σ ≠ 0)]; ring
            _ ≤ 16 * 0.85 * 1 / |σ - sigmaPlus| := by
                gcongr; rw [div_le_one (by linarith)]; linarith
            _ ≤ 180 / |σ - sigmaPlus| := by gcongr; norm_num
        · have h4 : 4 < σ := not_le.mp hσ4
          have hsp_ge : σ / 3 ≤ |σ - sigmaPlus| := by
            rw [abs_of_pos (by linarith [sigmaPlus_lt_242])]
            linarith [sigmaPlus_lt_242]
          have hinv_le : invJacobian σ ≤ 6 * π * σ := by
            unfold invJacobian
            rw [abs_of_pos (mul_pos (by linarith) (by nlinarith)),
              abs_of_pos (by linarith [sigmaStar_neg] : 0 < σ - sigmaStar),
              div_le_iff₀ (mul_pos (by linarith [sigmaStar_neg]) hsp_pos)]
            calc 2 * π * (σ * (σ ^ 2 - 1)) ≤ 2 * π * (σ * σ ^ 2) := by gcongr; linarith
              _ = 6 * π * σ * (σ * (σ / 3)) := by ring
              _ ≤ 6 * π * σ * ((σ - sigmaStar) * |σ - sigmaPlus|) := by
                  gcongr
                  · exact (by linarith [sigmaStar_neg] : 0 ≤ σ - sigmaStar)
                  · linarith [sigmaStar_neg]
          have hP := hP_tail σ hσ1
          calc poissonKernel z₀.re z₀.im σ * invJacobian σ
              ≤ (4 * z₀.im / (π * σ ^ 2)) * (6 * π * σ) :=
                mul_le_mul hP hinv_le (by unfold invJacobian; positivity) (by positivity)
            _ = 24 * z₀.im / σ := by field_simp [Real.pi_pos.ne', (by linarith : σ ≠ 0)]; ring
            _ ≤ 24 * 0.85 / 4 := by gcongr
            _ ≤ 10 := by norm_num
    unfold leftSlitDensity
    change poissonKernel z₀.re z₀.im σ * invJacobian σ +
      poissonKernel z₀.re z₀.im τ * invJacobian τ ≤ _
    split_ifs with hσ4
    · simp only [hσ4, ↓reduceIte] at hσ_term hτ_term
      calc poissonKernel z₀.re z₀.im σ * invJacobian σ +
            poissonKernel z₀.re z₀.im τ * invJacobian τ
          ≤ 180 / |σ - sigmaPlus| + 70 / |σ - sigmaPlus| := add_le_add hσ_term hτ_term
        _ = 250 / |σ - sigmaPlus| := by ring
    · simp only [hσ4, ↓reduceIte] at hσ_term hτ_term
      linarith only [hσ_term, hτ_term]
  unfold leftSlitEntropy
  have hm_left : Measurable (leftSlitDensity z₀.re z₀.im) := by
    unfold leftSlitDensity poissonKernel leftSlitInv invJacobian
    fun_prop (disch := measurability)
  have hm_integrand : Measurable (fun σ =>
      poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ))) :=
    (continuous_poissonKernel z₀.re hz₀).measurable.mul
      (Measurable.max measurable_const (Real.measurable_log.comp hm_left))
  have hlog250 : Real.log 250 ≤ 6 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    rw [hpow]
    have h250 : (250 : ℝ) ≤ (2.71 : ℝ) ^ 6 := by norm_num
    exact h250.trans (pow_le_pow_left₀ (by norm_num) he1 6)
  have hlog60 : Real.log 60 ≤ 5 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpow : Real.exp 5 = Real.exp 1 ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    rw [hpow]
    have h60 : (60 : ℝ) ≤ (2.71 : ℝ) ^ 5 := by norm_num
    exact h60.trans (pow_le_pow_left₀ (by norm_num) he1 5)
  let dom1 : ℝ → ℝ := fun σ =>
    Real.log 250 * poissonKernel z₀.re z₀.im σ +
      (4 * z₀.im / π) * max 0 (Real.log (1 / |σ - sigmaPlus|))
  have hdom1 : IntegrableOn dom1 (Ioc 1 4) :=
    ((integrable_poissonKernel z₀.re hz₀).const_mul _).integrableOn.add
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 4)).1
        ((intervalIntegrable_posLog_inv_abs sigmaPlus 1 4).const_mul _))
  have hpt1 : ∀ σ ∈ Ioc (1 : ℝ) 4,
      poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)) ≤ dom1 σ := by
    intro σ hσ
    have hP0 := poissonKernel_nonneg (x := z₀.re) hz₀.le σ
    have hbd := hleft_dens σ hσ.1
    rw [ite_eq_left hσ.2] at hbd
    have hL := (posLog_mono_nn (leftSlitDensity_nonneg' z₀.re hz₀.le σ) hbd).trans
      (posLog_div_le_posLog_add (by norm_num : (0 : ℝ) ≤ 250) (abs_nonneg (σ - sigmaPlus)))
    rw [max_eq_right (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 250))] at hL
    have hP_le : poissonKernel z₀.re z₀.im σ ≤ 4 * z₀.im / π := by
      calc poissonKernel z₀.re z₀.im σ ≤ 4 * z₀.im / (π * σ ^ 2) := hP_tail σ hσ.1
        _ ≤ 4 * z₀.im / (π * 1 ^ 2) := by gcongr; nlinarith [hσ.1]
        _ = 4 * z₀.im / π := by ring
    have hnn2 : 0 ≤ max 0 (Real.log (1 / |σ - sigmaPlus|)) := le_max_left 0 _
    have hstep1 : poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)) ≤
        poissonKernel z₀.re z₀.im σ * (Real.log 250 + max 0 (Real.log (1 / |σ - sigmaPlus|))) :=
      mul_le_mul_of_nonneg_left hL hP0
    have hstep2 : poissonKernel z₀.re z₀.im σ * max 0 (Real.log (1 / |σ - sigmaPlus|)) ≤
        (4 * z₀.im / π) * max 0 (Real.log (1 / |σ - sigmaPlus|)) :=
      mul_le_mul_of_nonneg_right hP_le hnn2
    dsimp [dom1]; linarith
  have hint_Ioc : IntegrableOn
      (fun σ => poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)))
      (Ioc 1 4) :=
    hdom1.mono' hm_integrand.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun σ hσ => by
        rw [Real.norm_of_nonneg (mul_nonneg (poissonKernel_nonneg hz₀.le σ) (le_max_left 0 _))]
        exact hpt1 σ hσ))
  have hpt2 : ∀ σ ∈ Ioi (4 : ℝ),
      poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)) ≤
        Real.log 60 * poissonKernel z₀.re z₀.im σ := by
    intro σ hσ
    have hP0 := poissonKernel_nonneg (x := z₀.re) hz₀.le σ
    have hbd := hleft_dens σ (by linarith [mem_Ioi.mp hσ])
    rw [ite_eq_right (not_le.mpr hσ)] at hbd
    have hL := posLog_mono_nn (leftSlitDensity_nonneg' z₀.re hz₀.le σ) hbd
    rw [max_eq_right (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 60))] at hL
    nlinarith
  have hint_Ioi : IntegrableOn
      (fun σ => poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)))
      (Ioi 4) :=
    ((integrable_poissonKernel z₀.re hz₀).const_mul (Real.log 60)).integrableOn.mono'
      hm_integrand.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun σ hσ => by
          rw [Real.norm_of_nonneg (mul_nonneg (poissonKernel_nonneg hz₀.le σ) (le_max_left 0 _))]
          exact hpt2 σ hσ))
  have hsplit_eq : ∫ σ in Ioi 1, poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)) =
      (∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ))) +
        (∫ σ in Ioi 4, poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ))) := by
    rw [show Ioi (1 : ℝ) = Ioc 1 4 ∪ Ioi 4 from (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_Ioc hint_Ioi]
  have hIoc_le : ∫ σ in Ioc 1 4,
      poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)) ≤ 9 := by
    have hm1 := setIntegral_mono_on hint_Ioc hdom1 measurableSet_Ioc hpt1
    have hdom_eval : ∫ σ in Ioc 1 4, dom1 σ =
        Real.log 250 * (∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ) +
          (4 * z₀.im / π) * (∫ σ in Ioc 1 4, max 0 (Real.log (1 / |σ - sigmaPlus|))) := by
      dsimp [dom1]
      rw [integral_add ((integrable_poissonKernel z₀.re hz₀).const_mul _).integrableOn
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 4)).1
          ((intervalIntegrable_posLog_inv_abs sigmaPlus 1 4).const_mul _)),
        integral_const_mul, integral_const_mul]
    have hpk1 : ∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ ≤ 1 := by
      calc ∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ
          ≤ ∫ σ : ℝ, poissonKernel z₀.re z₀.im σ :=
            setIntegral_le_integral (integrable_poissonKernel z₀.re hz₀)
              (Eventually.of_forall fun σ => poissonKernel_nonneg hz₀.le σ)
        _ = 1 := integral_poissonKernel z₀.re hz₀
    have hlog_inv_int : ∫ σ in Ioc 1 4, max 0 (Real.log (1 / |σ - sigmaPlus|)) ≤ 2 := by
      have hsub_int : ∫ σ in (1 : ℝ)..4, max 0 (Real.log (1 / |σ - sigmaPlus|)) ≤ 2 := by
        have hlo : (1 : ℝ) ≤ sigmaPlus - 1 := by linarith [sigmaPlus_gt_two]
        have hhi : sigmaPlus + 1 ≤ 4 := by linarith [sigmaPlus_lt_242]
        have hint_a : ∫ σ in (1 : ℝ)..(sigmaPlus - 1), max 0 (Real.log (1 / |σ - sigmaPlus|)) = 0 := by
          refine intervalIntegral.integral_zero_ae ?_
          filter_upwards with σ hσ
          rw [uIoc_of_le hlo] at hσ
          have hge1 : 1 ≤ |σ - sigmaPlus| := by rw [abs_of_nonpos (by linarith [hσ.2])]; linarith [hσ.2]
          exact max_eq_left (Real.log_nonpos (by positivity) (div_le_one_of_le₀ hge1 (abs_nonneg _)))
        have hint_b : ∫ σ in (sigmaPlus + 1)..4, max 0 (Real.log (1 / |σ - sigmaPlus|)) = 0 := by
          refine intervalIntegral.integral_zero_ae ?_
          filter_upwards with σ hσ
          rw [uIoc_of_le hhi] at hσ
          have hge1 : 1 ≤ |σ - sigmaPlus| := by rw [abs_of_nonneg (by linarith [hσ.1])]; linarith [hσ.1]
          exact max_eq_left (Real.log_nonpos (by positivity) (div_le_one_of_le₀ hge1 (abs_nonneg _)))
        have hcomb := intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_posLog_inv_abs sigmaPlus 1 (sigmaPlus - 1))
          (intervalIntegrable_posLog_inv_abs sigmaPlus (sigmaPlus - 1) 4)
        have hcomb2 := intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_posLog_inv_abs sigmaPlus (sigmaPlus - 1) (sigmaPlus + 1))
          (intervalIntegrable_posLog_inv_abs sigmaPlus (sigmaPlus + 1) 4)
        rw [hint_a, zero_add] at hcomb
        rw [hint_b, add_zero] at hcomb2
        have hpos_val : ∫ σ in (sigmaPlus - 1)..(sigmaPlus + 1),
            max 0 (Real.log (1 / |σ - sigmaPlus|)) = 2 := by
          have hshift : ∫ σ in (sigmaPlus - 1)..(sigmaPlus + 1),
              max 0 (Real.log (1 / |σ - sigmaPlus|)) =
              ∫ u in (-1 : ℝ)..1, max 0 (Real.log (1 / |u|)) := by
            have h := intervalIntegral.integral_comp_sub_right
              (fun u => max 0 (Real.log (1 / |u|))) sigmaPlus (a := sigmaPlus - 1) (b := sigmaPlus + 1)
            simpa [sub_self] using h
          rw [hshift]
          have h_sym := intervalIntegral.integral_add_adjacent_intervals
            (intervalIntegrable_posLog_inv_abs 0 (-1) 0)
            (intervalIntegrable_posLog_inv_abs 0 0 1)
          simp only [sub_zero] at h_sym
          have hneg_eq : ∫ u in (-1 : ℝ)..0, max 0 (Real.log (1 / |u|)) =
              ∫ u in (0 : ℝ)..1, max 0 (Real.log (1 / |u|)) := by
            have h := intervalIntegral.integral_comp_neg
              (f := fun u => max 0 (Real.log (1 / |u|))) (a := -1) (b := 0)
            simpa [abs_neg] using h
          have h01 : ∫ u in (0 : ℝ)..1, max 0 (Real.log (1 / |u|)) = 1 := by
            have heq_ae : ∀ᵐ u ∂volume, u ∈ Ioc (0 : ℝ) 1 →
                max 0 (Real.log (1 / |u|)) = -Real.log u := by
              filter_upwards with u hu
              rw [abs_of_pos hu.1, one_div, Real.log_inv]
              exact max_eq_right (by linarith [Real.log_nonpos hu.1.le hu.2])
            rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
              setIntegral_congr_ae measurableSet_Ioc heq_ae,
              ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
              intervalIntegral.integral_neg, integral_log]
            norm_num
          linarith only [h_sym, hneg_eq, h01]
        linarith only [hcomb, hcomb2, hpos_val]
      rw [← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 4)]
      exact hsub_int
    have h4y_le : 4 * z₀.im / π ≤ 4 / 3 := by
      have hpi3 := Real.pi_gt_three
      rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
      nlinarith only [hy₀_le, hpi3]
    have h1 : Real.log 250 * (∫ σ in Ioc 1 4, poissonKernel z₀.re z₀.im σ) ≤ 6 * 1 :=
      mul_le_mul hlog250 hpk1 (setIntegral_nonneg measurableSet_Ioc fun σ _ => poissonKernel_nonneg hz₀.le σ)
        (by norm_num)
    have h2 : (4 * z₀.im / π) * (∫ σ in Ioc 1 4, max 0 (Real.log (1 / |σ - sigmaPlus|))) ≤
        (4 / 3) * 2 :=
      mul_le_mul h4y_le hlog_inv_int (setIntegral_nonneg measurableSet_Ioc fun _ _ => le_max_left 0 _)
        (by norm_num)
    linarith only [hm1, hdom_eval, h1, h2]
  have hIoi_le : ∫ σ in Ioi 4,
      poissonKernel z₀.re z₀.im σ * max 0 (Real.log (leftSlitDensity z₀.re z₀.im σ)) ≤ 5 := by
    have hm2 := setIntegral_mono_on hint_Ioi
      ((integrable_poissonKernel z₀.re hz₀).const_mul (Real.log 60)).integrableOn
      measurableSet_Ioi hpt2
    rw [integral_const_mul] at hm2
    have hpk2 : ∫ σ in Ioi 4, poissonKernel z₀.re z₀.im σ ≤ 1 := by
      calc ∫ σ in Ioi 4, poissonKernel z₀.re z₀.im σ
          ≤ ∫ σ : ℝ, poissonKernel z₀.re z₀.im σ :=
            setIntegral_le_integral (integrable_poissonKernel z₀.re hz₀)
              (Eventually.of_forall fun σ => poissonKernel_nonneg hz₀.le σ)
        _ = 1 := integral_poissonKernel z₀.re hz₀
    have hpk_nn : 0 ≤ ∫ σ in Ioi 4, poissonKernel z₀.re z₀.im σ :=
      setIntegral_nonneg measurableSet_Ioi fun σ _ => poissonKernel_nonneg (x := z₀.re) hz₀.le σ
    nlinarith [hlog60, hpk2, hpk_nn, hm2]
  linarith

/-- Uniform slit entropy bound on `lowerBoasRightDom` for `0 < |Im b| ≤ 1/4`:
`slitEntropy z₀.re z₀.im ≤ 35 + 2 * log (1 / |b.im|)`. -/
theorem slitEntropy_le_of_confB {z₀ b : ℂ} (hz₀ : 0 < z₀.im) (hb : confB z₀ = b)
    (hre : xiStar < b.re) (him_le : |b.im| ≤ 1 / 4) (him_ne : b.im ≠ 0) :
    slitEntropy z₀.re z₀.im ≤ 35 + 2 * Real.log (1 / |b.im|) := by
  obtain ⟨hz_le2, _, hre_le, hy₀_le, hre_star_le⟩ :=
    z0_norm_re_im_bounds_of_confB hz₀ hb hre
  have hratio := z0_im_ratio_of_confB hz₀ hb hre him_le him_ne
  obtain ⟨hsep, hsmall⟩ := z0_sigmaStar_sep_of_confB hz₀ hb hre him_le
  have hb_pos : 0 < |b.im| := abs_pos.mpr him_ne
  have hleft_ent : leftSlitEntropy z₀.re z₀.im ≤ 14 :=
    leftSlitEntropy_le_of_confB hz₀ hre_le hy₀_le
  have hright_ent : rightSlitEntropy z₀.re z₀.im ≤ 21 + 2 * Real.log (1 / |b.im|) := by
    unfold rightSlitEntropy
    set M_R : ℝ := 160 / |b.im|
    have hMR_ge1 : 1 ≤ M_R := by
      dsimp [M_R]; rw [one_le_div hb_pos]; linarith
    have hdens_ub : ∀ σ ∈ Ioo (-1 : ℝ) 0,
        rightSlitDensity z₀.re z₀.im σ ≤ M_R / |σ - sigmaStar| := by
      intro σ hσ
      by_cases hne : σ = sigmaStar
      · subst hne; unfold rightSlitDensity; rw [slitInv_sigmaStar]; unfold invJacobian; simp
      · have hMz : ‖z₀ * (z₀ + 1)‖ / z₀.im ≤ 13 / |b.im| := hratio
        have h1 : poissonKernel z₀.re z₀.im σ * invJacobian σ ≤
            (4 * (13 / |b.im| + 4)) / |σ - sigmaStar| :=
          pkernel_mul_invJacobian_right hz₀ hz_le2 hMz (by positivity) hσ hne
        have hτ_mem : slitInv σ ∈ Ioo (-1 : ℝ) 0 := slitInv_mem_Ioo hσ
        have hτ_ne : slitInv σ ≠ sigmaStar := by
          intro heq
          have h := abs_slitInv_sub_sigmaStar_lower hσ
          rw [heq, sub_self, abs_zero] at h
          have : 0 < |σ - sigmaStar| / √2 := div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by positivity)
          linarith
        have h2 : poissonKernel z₀.re z₀.im (slitInv σ) * invJacobian (slitInv σ) ≤
            (4 * √2 * (13 / |b.im| + 4)) / |σ - sigmaStar| := by
          have hbase := pkernel_mul_invJacobian_right hz₀ hz_le2 hMz (by positivity) hτ_mem hτ_ne
          have hinv := abs_slitInv_sub_sigmaStar_lower hσ
          have h3 : (4 * (13 / |b.im| + 4)) / |slitInv σ - sigmaStar| ≤
              (4 * (13 / |b.im| + 4)) / (|σ - sigmaStar| / √2) := by
            gcongr
          refine hbase.trans (h3.trans ?_)
          rw [div_div_eq_mul_div]; apply le_of_eq; ring
        have hsum_le : (4 + 4 * √2) * (13 / |b.im| + 4) ≤ M_R := by
          have h4_le : (4 : ℝ) ≤ 1 / |b.im| := by rw [le_div_iff₀ hb_pos]; linarith
          have hrt : 4 + 4 * √2 ≤ 10 := by linarith [sqrt2_lt_slit]
          have h13_add : 13 / |b.im| + 4 ≤ 14 / |b.im| := by
            linarith [show 13 / |b.im| + 1 / |b.im| = 14 / |b.im| by ring]
          dsimp [M_R]
          calc (4 + 4 * √2) * (13 / |b.im| + 4) ≤ 10 * (14 / |b.im|) := by gcongr
            _ = 140 / |b.im| := by ring
            _ ≤ 160 / |b.im| := by gcongr; norm_num
        unfold rightSlitDensity
        have hsum := add_le_add h1 h2
        have heq_s : (4 * (13 / |b.im| + 4)) / |σ - sigmaStar| +
            (4 * √2 * (13 / |b.im| + 4)) / |σ - sigmaStar| =
            ((4 + 4 * √2) * (13 / |b.im| + 4)) / |σ - sigmaStar| := by ring
        rw [heq_s] at hsum
        exact hsum.trans (by gcongr)
    set e : ℝ := z₀.re - sigmaStar
    set ρ : ℝ := max z₀.im |e|
    have hρ_pos : 0 < ρ := lt_of_lt_of_le hz₀ (le_max_left _ _)
    have hρ_le1 : ρ ≤ 1 := max_le (by linarith) (by linarith)
    have hρ_lb : |b.im| / 1000 ≤ ρ := by
      by_cases hfar : xiStar + 0.1 ≤ b.re
      · have hnorm := hsep hfar
        have h005 : 0.005 ≤ ρ := by
          by_contra hlt
          have hl : z₀.im < 0.005 := lt_of_le_of_lt (le_max_left _ _) (not_le.mp hlt)
          have hr : |e| < 0.005 := lt_of_le_of_lt (le_max_right _ _) (not_le.mp hlt)
          have hbd : ‖z₀ - (sigmaStar : ℂ)‖ ≤ |e| + z₀.im := by
            have h1 : (z₀ - (sigmaStar : ℂ)).re = e := by simp [e]
            have h2 : (z₀ - (sigmaStar : ℂ)).im = z₀.im := by simp
            calc ‖z₀ - (sigmaStar : ℂ)‖ ≤ |(z₀ - (sigmaStar : ℂ)).re| + |(z₀ - (sigmaStar : ℂ)).im| :=
                  Complex.norm_le_abs_re_add_abs_im _
              _ = |e| + z₀.im := by rw [h1, h2, abs_of_pos hz₀]
          linarith
        linarith
      · exact (hsmall (not_le.mp hfar).le).trans (le_max_left _ _)
    have hPK_eq : z₀.re = sigmaStar + e := by dsimp [e]; ring
    have hlemmaS := lemmaS_poisson_log_bound (y := z₀.im) (e := e) hz₀ hρ_le1
    rw [← hPK_eq] at hlemmaS
    have hint_R : IntegrableOn
        (fun σ => poissonKernel z₀.re z₀.im σ * max 0 (Real.log (rightSlitDensity z₀.re z₀.im σ)))
        (Ioo (-1) 0) := by
      let dom : ℝ → ℝ := fun σ => (π * z₀.im)⁻¹ * (Real.log M_R + max 0 (Real.log (1 / |σ - sigmaStar|)))
      have hdom : IntegrableOn dom (Ioo (-1) 0) :=
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 0)).1
          ((intervalIntegrable_const.add
            (intervalIntegrable_posLog_inv_abs sigmaStar (-1) 0)).const_mul _)).mono_set
          Ioo_subset_Ioc_self
      have hm_d : Measurable (rightSlitDensity z₀.re z₀.im) := by
        unfold rightSlitDensity poissonKernel slitInv invJacobian
        fun_prop (disch := measurability)
      have hmeas : AEStronglyMeasurable
          (fun σ => poissonKernel z₀.re z₀.im σ * max 0 (Real.log (rightSlitDensity z₀.re z₀.im σ)))
          (volume.restrict (Ioo (-1) 0)) :=
        ((continuous_poissonKernel z₀.re hz₀).measurable.mul
          (Measurable.max measurable_const (Real.measurable_log.comp hm_d))).aestronglyMeasurable
      refine hdom.mono' hmeas ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun σ hσ => ?_))
      rw [Real.norm_of_nonneg (mul_nonneg (poissonKernel_nonneg hz₀.le σ) (le_max_left 0 _))]
      have hP_ub : poissonKernel z₀.re z₀.im σ ≤ (π * z₀.im)⁻¹ := by
        simpa [one_div] using poissonKernel_le_inv_pi_mul_y hz₀ σ
      have hnn : 0 ≤ rightSlitDensity z₀.re z₀.im σ := rightSlitDensity_nonneg' z₀.re hz₀.le σ
      have hL_ub : max 0 (Real.log (rightSlitDensity z₀.re z₀.im σ)) ≤
          Real.log M_R + max 0 (Real.log (1 / |σ - sigmaStar|)) := by
        have h1 := posLog_mono_nn hnn (hdens_ub σ hσ)
        have h2 := posLog_div_le_posLog_add (by linarith : 0 ≤ M_R) (abs_nonneg (σ - sigmaStar))
        rw [max_eq_right (Real.log_nonneg hMR_ge1)] at h2
        exact h1.trans h2
      exact mul_le_mul hP_ub hL_ub (le_max_left 0 _) (by positivity)
    have hint_dom2 : IntegrableOn
        (fun σ => Real.log (M_R / ρ) * poissonKernel z₀.re z₀.im σ +
          poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|)))
        (Ioo (-1) 0) :=
      ((integrable_poissonKernel z₀.re hz₀).const_mul (Real.log (M_R / ρ))).integrableOn.add
        (integrable_poisson_mul_posLog_div z₀.re z₀.im ρ hz₀ hρ_pos).integrableOn
    have hpt_dom : ∀ σ ∈ Ioo (-1 : ℝ) 0,
        poissonKernel z₀.re z₀.im σ * max 0 (Real.log (rightSlitDensity z₀.re z₀.im σ)) ≤
          Real.log (M_R / ρ) * poissonKernel z₀.re z₀.im σ +
            poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|)) := by
      intro σ hσ
      have hP0 := poissonKernel_nonneg (x := z₀.re) hz₀.le σ
      have hnn := rightSlitDensity_nonneg' z₀.re hz₀.le σ
      have h1 := posLog_mono_nn hnn (hdens_ub σ hσ)
      have hMR_div : 1 ≤ M_R / ρ := (one_le_div hρ_pos).mpr (hρ_le1.trans hMR_ge1)
      have hsplit_log : max 0 (Real.log (M_R / |σ - sigmaStar|)) ≤
          Real.log (M_R / ρ) + max 0 (Real.log (ρ / |σ - sigmaStar|)) := by
        by_cases hsig : σ = sigmaStar
        · simp [hsig, Real.log_nonneg hMR_div]
        · have habs_pos : 0 < |σ - sigmaStar| := abs_pos.mpr (sub_ne_zero.mpr hsig)
          have hdiv_eq : M_R / |σ - sigmaStar| = (M_R / ρ) * (ρ / |σ - sigmaStar|) := by
            field_simp [hρ_pos.ne']
          rw [hdiv_eq, Real.log_mul (by positivity) (by positivity)]
          exact max_le (by linarith only [Real.log_nonneg hMR_div, le_max_left 0 (Real.log (ρ / |σ - sigmaStar|))])
            (by linarith only [le_max_right 0 (Real.log (ρ / |σ - sigmaStar|))])
      have hmul := mul_le_mul_of_nonneg_left (h1.trans hsplit_log) hP0
      linarith only [hmul]
    have hint_mono := setIntegral_mono_on hint_R hint_dom2 measurableSet_Ioo hpt_dom
    have hlog_eval : ∫ σ in Ioo (-1 : ℝ) 0,
        (Real.log (M_R / ρ) * poissonKernel z₀.re z₀.im σ +
          poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|))) =
        Real.log (M_R / ρ) * (∫ σ in Ioo (-1 : ℝ) 0, poissonKernel z₀.re z₀.im σ) +
          (∫ σ in Ioo (-1 : ℝ) 0,
            poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|))) := by
      rw [integral_add ((integrable_poissonKernel z₀.re hz₀).const_mul _).integrableOn
        (integrable_poisson_mul_posLog_div z₀.re z₀.im ρ hz₀ hρ_pos).integrableOn,
        integral_const_mul]
    have hpk_le1 : ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel z₀.re z₀.im σ ≤ 1 := by
      calc ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel z₀.re z₀.im σ
          ≤ ∫ σ : ℝ, poissonKernel z₀.re z₀.im σ :=
            setIntegral_le_integral (integrable_poissonKernel z₀.re hz₀)
              (Eventually.of_forall fun σ => poissonKernel_nonneg hz₀.le σ)
        _ = 1 := integral_poissonKernel z₀.re hz₀
    have hlog_mr_le : Real.log (M_R / ρ) ≤ 12 + 2 * Real.log (1 / |b.im|) := by
      have hMR_div_le : M_R / ρ ≤ 160000 * (1 / |b.im|) ^ 2 := by
        dsimp [M_R]
        calc (160 / |b.im|) / ρ ≤ (160 / |b.im|) / (|b.im| / 1000) := by gcongr
          _ = 160000 * (1 / |b.im|) ^ 2 := by field_simp [hb_pos.ne']; ring
      have h1 : Real.log (M_R / ρ) ≤ Real.log (160000 * (1 / |b.im|) ^ 2) :=
        Real.log_le_log (div_pos (by positivity) hρ_pos) hMR_div_le
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Nat.cast_ofNat] at h1
      have h160 : Real.log 160000 ≤ 12 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have he1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
        have hpow : Real.exp 12 = Real.exp 1 ^ 12 := by
          rw [show (12 : ℝ) = (12 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
        rw [hpow]
        have h2a : (160000 : ℝ) ≤ (2.718 : ℝ) ^ 12 := by norm_num
        exact h2a.trans (pow_le_pow_left₀ (by norm_num) he1 12)
      linarith only [h1, h160]
    have hterm2_le : ∫ σ in Ioo (-1 : ℝ) 0,
        poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|)) ≤
        (4 / π) * (1 + Real.log 2) + 3 := by
      calc ∫ σ in Ioo (-1 : ℝ) 0,
            poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|))
          ≤ ∫ σ : ℝ, poissonKernel z₀.re z₀.im σ * max 0 (Real.log (ρ / |σ - sigmaStar|)) :=
            setIntegral_le_integral (integrable_poisson_mul_posLog_div z₀.re z₀.im ρ hz₀ hρ_pos)
              (Eventually.of_forall fun σ => mul_nonneg (poissonKernel_nonneg hz₀.le σ) (le_max_left 0 _))
        _ ≤ (4 / π) * (1 + Real.log 2) + 3 := hlemmaS
    have hconst6 : (4 / π) * (1 + Real.log 2) + 3 ≤ 6 := by
      have hlog2 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]; linarith only [Real.exp_one_gt_d9]
      have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
      have hdiv : 4 / π ≤ 4 / 3 := by gcongr
      have hmul : (4 / π) * (1 + Real.log 2) ≤ (4 / 3) * 2 :=
        mul_le_mul hdiv (by linarith only [hlog2])
          (add_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) (by norm_num)
      linarith only [hmul]
    have hMR_div_nn : 0 ≤ Real.log (M_R / ρ) :=
      Real.log_nonneg ((one_le_div hρ_pos).mpr (hρ_le1.trans hMR_ge1))
    have hpk_nn : 0 ≤ ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel z₀.re z₀.im σ :=
      setIntegral_nonneg measurableSet_Ioo fun σ _ => poissonKernel_nonneg hz₀.le σ
    have hstep_mr : Real.log (M_R / ρ) * (∫ σ in Ioo (-1 : ℝ) 0, poissonKernel z₀.re z₀.im σ) ≤
        Real.log (M_R / ρ) * 1 := mul_le_mul_of_nonneg_left hpk_le1 hMR_div_nn
    linarith only [hint_mono, hlog_eval, hstep_mr, hterm2_le, hlog_mr_le, hconst6]
  unfold slitEntropy
  linarith only [hleft_ent, hright_ent]

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.slitEntropy_le_of_confB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.slitEntropy_le_of_confB
