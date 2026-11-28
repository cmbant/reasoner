/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingPsiFarBase
public import FormalResearch.SignUncertainty.FctSplittingHorizFTC

/-!
# Exponential decay of `Ψ_c(iτ)` and its first two derivatives on the far left edge `|τ| ≥ 1/2`

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.8 (`fct:splitting`), far-edge
estimate for `Ψ_c(iτ)` (`|τ| ≥ 1/2`, `j = 0, 1, 2`).

Starting from `FctDescentStmt h` alone (horizontal strip descent at `σ = 3/8 ∈ [5/16, 7/16]`):
* Horizontal FTC (`FctSplittingHorizFTC.horiz_ftc_gen`) expresses
  `K₀(iτ) Ψ_c(iτ) = K₀(3/8 + iτ) Ψ_c(3/8 + iτ) - ∫_{0}^{3/8} K₀(r + iτ) A_ε(r + iτ) dr`
  for `τ > 0`, giving `‖Ψ_c(iτ)‖ ≤ M₀ (1 + τ)^8 exp(-π τ)` on `τ ≥ 1/2`.
* Using the ODE `Ψ_c'(iτ) = i (A_ε(iτ) - (K₀'/K₀)(iτ) Ψ_c(iτ))` from `fctPsi_hasDerivAt_pos`,
  along with `EJOn` bounds from `FctSplittingPsiFarBase` and polynomial bounds for `(K₀'/K₀)(iτ)`
  and its derivative, gives matching `(1 + |τ|)^N exp(-π |τ|)` bounds for `∂_τ Ψ_c(iτ)` and
  `∂_τ^2 Ψ_c(iτ)`.
* Reflection by `fctPsi_conj` extends the `j = 0, 1, 2` bounds to `τ ≤ -1/2`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real ContDiff
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-! ### Part 1: Zero-order `Ψ_c(iτ)` bound on `τ ≥ 1/2` -/

private lemma mellinK0_mul_fctPsi_eq {K4 ε c L1 α : ℝ} {ζ : ℂ} (hζ : ζ.re < 1) :
    mellinK0 c ζ (fctXi1 L1) * fctPsi K4 ε c L1 α ζ =
      ζ * ∫ s in (0 : ℝ)..1, fctWarpKA K4 ε c L1 α ((s : ℂ) * ζ) := by
  unfold fctPsi fctWarpKA
  have hne := mellinK0_ne_zero c hζ (fctXi1 L1)
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

private lemma fctPsi_horiz_ftc {K4 ε c L1 α : ℝ} (hc : 0 < c)
    (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    {τ : ℝ} (hτ : 0 < τ) :
    mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1) *
        fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) -
      mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
        fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      ∫ r in (0 : ℝ)..(3 / 8 : ℝ), fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I) := by
  have hgen := horiz_ftc_gen (f := fctWarpKA K4 ε c L1 α)
    (fctWarpKA_differentiableOn (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDh)
    (fctWarpKA_continuousOn (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc)
    (fctWarpKA_near_zero (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDb)
    (fun z hz0 hz1 _ => fctWarpKA_segment_integrable (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc hDb hz0 hz1)
    (fctPsi_integral_continuousOn (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc hDb)
    hτ
  rw [mellinK0_mul_fctPsi_eq (by norm_num : ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I).re < 1),
    mellinK0_mul_fctPsi_eq (by simp : ((τ : ℂ) * Complex.I).re < 1)]
  exact hgen

private lemma mellinK0_imag_inv_le {c ξ τ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hτ : 0 ≤ τ) :
    ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖⁻¹ ≤ Real.exp (1 / (6 * c)) * (1 + τ) := by
  have hmag := (norm_mellinK0_imag_le hc hξ τ).1
  have hbin : ‖FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)‖ ≤ 1 / (6 * c) := by
    have hb := FormalResearch.Asymptotics.binetDiff_norm_le hc (by simp : ((τ : ℂ) * Complex.I).re < 1)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_zero, div_one] at hb
    exact hb.trans_eq (by ring)
  have hre : -(1 / (6 * c)) ≤ (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re := by
    linarith [neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hbin)]
  have hexp : Real.exp (-(1 / (6 * c))) ≤
      Real.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re :=
    Real.exp_le_exp.mpr hre
  have hpow : (1 + τ)⁻¹ ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
    have h4 : 1 + τ ^ 2 ≤ (1 + τ) ^ 4 := by
      have h0 := pow_nonneg hτ 3
      nlinarith [sq_nonneg τ]
    have hp1 : ((1 + τ) ^ 4) ^ (-(1 / 4 : ℝ)) ≤ (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h4 (by norm_num)
    have hpi : ((1 + τ) ^ 4) ^ (-(1 / 4 : ℝ)) = (1 + τ)⁻¹ := by
      rw [← Real.rpow_natCast (1 + τ) 4, ← Real.rpow_mul (by positivity)]
      norm_num
      exact Real.rpow_neg_one (1 + τ)
    linarith
  have hlo : (1 + τ)⁻¹ * Real.exp (-(1 / (6 * c))) ≤ ‖mellinK0 c ((τ : ℂ) * Complex.I) ξ‖ := by
    rw [hmag]; exact mul_le_mul hpow hexp (by positivity) (by positivity)
  have hinv := inv_anti₀ (by positivity) hlo
  rwa [mul_inv, inv_inv, Real.exp_neg, inv_inv, mul_comm (1 + τ)] at hinv

private lemma fctPsi_far_zero_pos {K4 ε c L1 α B Cdesc : ℝ} (hc : 0 < c)
    (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hCD : ∀ τ : ℝ, 1 / 2 ≤ τ →
      ‖fctFint K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ Cdesc * c⁻¹ / Real.log (2 + τ)) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ τ : ℝ, 1 / 2 ≤ τ →
      ‖fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)‖ ≤ M0 * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ)) := by
  have h0_mem : (0 : ℂ) ∈ closedStrip := by simp [closedStrip]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDb 0 h0_mem)
  have hC0 : 0 ≤ Cdesc := by
    have hlogpos : 0 < Real.log (2 + (1 / 2 : ℝ)) := Real.log_pos (by norm_num)
    have hnn := (norm_nonneg _).trans (hCD (1 / 2) le_rfl)
    have : 0 ≤ Cdesc * c⁻¹ := (div_nonneg_iff.mp hnn).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hlogpos))
    exact nonneg_of_mul_nonneg_left this (by positivity)
  obtain ⟨Kk, hKk0, hKk⟩ := norm_mellinK0_half_strip_decay hc (fctXi1_pos L1)
  obtain ⟨Khg, hKhg0, hKhg⟩ := ctHG_far ε
  obtain ⟨Cg, hCg0, hCg⟩ := stripG_far_bound
  obtain ⟨Cpk, hCpk0, hCpk⟩ := (FctPhiKill.fct_phikill).2.2.2.2.2.1
  set a : ℝ := c ^ (-(1 / 12 : ℝ))
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  set M_right : ℝ := Kk * ((Cdesc * c⁻¹ / Real.log 2 + 1) * (B * Khg) * c⁻¹)
  set M_int : ℝ := Kk * (Cg + |L1| * Cpk) * B * Khg
  set M0 : ℝ := Real.exp (1 / (6 * c)) * (M_right + M_int)
  refine ⟨M0, by positivity, fun τ hτ => ?_⟩
  have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  have him_ge : 1 / 2 ≤ |((3 / 8 : ℂ) + (τ : ℂ) * Complex.I).im| := by
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    have him0 : ((3 / 8 : ℂ)).im = 0 := by simp
    rw [him0, zero_add, abs_of_pos hτpos]
    exact hτ
  have hftc := fctPsi_horiz_ftc (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDh hDc ⟨B, hDb⟩ hτpos
  have hmul : mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) *
      fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1) *
        fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) -
      ∫ r in (0 : ℝ)..(3 / 8 : ℝ), fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I) := by
    linear_combination -hftc
  have hK_38 : ‖mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1)‖ ≤ Kk := by
    have h1 := hKk (3 / 8 : ℝ) τ (by norm_num) (by norm_num)
    norm_num at h1
    have hp : (1 + |τ|) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg τ]) (by norm_num)
    exact h1.trans (mul_le_of_le_one_right hKk0 hp)
  have hmem_38 : (3 / 8 : ℂ) + (τ : ℂ) * Complex.I ∈ closedStrip := by
    simp [closedStrip]; norm_num
  have hPsi_38_eq : fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) =
      (fctFint K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) + 1) *
        (fctDcompAt K4 c α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
          ctHG ε ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) * (c : ℂ)⁻¹ := by
    have hre0 : 0 < ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I).re := by simp
    have hre1 : ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I).re < 1 / 2 := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      norm_num
    have hHG_ne := ctHG_ne_zero_of_band ε hre0 hre1
    have hD_ne := fctDcompAt_ne_zero (K4 := K4) (c := c) (α := α) ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)
    have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    unfold fctFint fctPhiC
    rw [sub_add_cancel, div_mul_cancel₀ _ (mul_ne_zero hD_ne hHG_ne), mul_comm (c : ℂ) _,
      mul_inv_cancel_right₀ hc_ne]
  have hFint_bd : ‖fctFint K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) + 1‖ ≤
      Cdesc * c⁻¹ / Real.log 2 + 1 := by
    have h1 := hCD τ hτ
    have hlog : Real.log 2 ≤ Real.log (2 + τ) := Real.log_le_log (by norm_num) (by linarith)
    have h2 : Cdesc * c⁻¹ / Real.log (2 + τ) ≤ Cdesc * c⁻¹ / Real.log 2 :=
      div_le_div_of_nonneg_left (by positivity) (Real.log_pos (by norm_num)) hlog
    exact (norm_add_le _ _).trans (by simpa using add_le_add_right (h1.trans h2) 1)
  have hD_38 : ‖fctDcompAt K4 c α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ B := hDb _ hmem_38
  have hHG_38 : ‖ctHG ε ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      Khg * ((1 + τ) ^ 6 * Real.exp (-(Real.pi * τ))) := by
    have h := hKhg _ hmem_38 him_ge
    have him38 : ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I).im = τ := by simp
    rwa [him38, abs_of_pos hτpos] at h
  have hbd_right :
      ‖mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1) *
          fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        M_right * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by
    rw [hPsi_38_eq, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc]
    have h67 : (1 + τ) ^ 6 ≤ (1 + τ) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc ‖mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1)‖ *
          (‖fctFint K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) + 1‖ *
            (‖fctDcompAt K4 c α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ *
              ‖ctHG ε ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖) * c⁻¹)
        ≤ Kk * ((Cdesc * c⁻¹ / Real.log 2 + 1) * (B * (Khg * ((1 + τ) ^ 6 * Real.exp (-(Real.pi * τ))))) * c⁻¹) := by
          gcongr
      _ = M_right * (1 + τ) ^ 6 * Real.exp (-(Real.pi * τ)) := by simp only [M_right]; ring
      _ ≤ M_right * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by gcongr
  have hint_pt : ∀ r ∈ uIoc (0 : ℝ) (3 / 8),
      ‖fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        M_int * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by
    intro r hr
    rw [uIoc_of_le (by norm_num)] at hr
    set t : ℂ := (r : ℂ) + (τ : ℂ) * Complex.I
    have ht_re : t.re = r := by simp [t]
    have ht_im : t.im = τ := by simp [t]
    have ht_mem : t ∈ closedStrip := ⟨by simp [ht_re]; linarith [hr.1], by simp [ht_re]; linarith [hr.2]⟩
    have ht_K0 : ‖mellinK0 c t (fctXi1 L1)‖ ≤ Kk := by
      have h1 := hKk r τ hr.1.le (hr.2.trans (by norm_num))
      have hp : (1 + |τ|) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg τ]) (by norm_num)
      exact h1.trans (mul_le_of_le_one_right hKk0 hp)
    have ht_g : ‖stripG t‖ ≤ Cg * (1 + τ) := by
      have hre1 : |t.re| ≤ 1 := by
        rw [ht_re, abs_le]; constructor <;> linarith [hr.1, hr.2]
      have him1 : 1 / 2 ≤ |t.im| := by rw [ht_im, abs_of_pos hτpos]; exact hτ
      have h := hCg t hre1 him1
      rwa [ht_im, abs_of_pos hτpos] at h
    have ht_pk : ‖FctPhiKill.phiKill a t‖ ≤ Cpk := by
      have h1 := hCpk (a := a) (z := t) ha (by simp [ht_re]; linarith [hr.1])
      exact h1.trans (mul_le_of_le_one_right hCpk0 (min_le_right _ _))
    have ht_fac : ‖stripG t + (L1 : ℂ) * FctPhiKill.phiKill a t‖ ≤ (Cg + |L1| * Cpk) * (1 + τ) := by
      have ht_pk' : ‖FctPhiKill.phiKill a t‖ ≤ Cpk * (1 + τ) :=
        ht_pk.trans (le_mul_of_one_le_right hCpk0 (by linarith))
      calc ‖stripG t + (L1 : ℂ) * FctPhiKill.phiKill a t‖
          ≤ ‖stripG t‖ + |L1| * ‖FctPhiKill.phiKill a t‖ := by
            simpa [Complex.norm_real, Real.norm_eq_abs] using norm_add_le (stripG t) ((L1 : ℂ) * FctPhiKill.phiKill a t)
        _ ≤ Cg * (1 + τ) + |L1| * (Cpk * (1 + τ)) :=
            add_le_add ht_g (mul_le_mul_of_nonneg_left ht_pk' (abs_nonneg _))
        _ = (Cg + |L1| * Cpk) * (1 + τ) := by ring
    have ht_D : ‖fctDcompAt K4 c α t‖ ≤ B := hDb t ht_mem
    have ht_HG : ‖ctHG ε t‖ ≤ Khg * ((1 + τ) ^ 6 * Real.exp (-(Real.pi * τ))) := by
      have him1 : 1 / 2 ≤ |t.im| := by rw [ht_im, abs_of_pos hτpos]; exact hτ
      have h := hKhg t ht_mem him1
      rwa [ht_im, abs_of_pos hτpos] at h
    unfold fctWarpKA fctWarpA
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖mellinK0 c t (fctXi1 L1)‖ * (‖stripG t + (L1 : ℂ) * FctPhiKill.phiKill a t‖ *
          ‖fctDcompAt K4 c α t‖ * ‖ctHG ε t‖)
        ≤ Kk * ((Cg + |L1| * Cpk) * (1 + τ) * B * (Khg * ((1 + τ) ^ 6 * Real.exp (-(Real.pi * τ))))) := by
          gcongr
      _ = M_int * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by simp only [M_int]; ring
  have hbd_int :
      ‖∫ r in (0 : ℝ)..(3 / 8 : ℝ), fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        M_int * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hint_pt
    have h2 : |(3 / 8 : ℝ) - 0| ≤ 1 := by norm_num
    exact h1.trans (mul_le_of_le_one_right (by positivity) h2)
  have hK0_ne := mellinK0_ne_zero c (by simp : ((τ : ℂ) * Complex.I).re < 1) (fctXi1 L1)
  have hpsi_eq : fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹ *
        (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)) := by
    rw [← mul_assoc, inv_mul_cancel₀ hK0_ne, one_mul]
  rw [hpsi_eq, norm_mul, norm_inv, hmul]
  have hKinv := mellinK0_imag_inv_le hc (fctXi1_pos L1) hτpos.le
  have hcomb :
      ‖mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1) *
          fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) -
        ∫ r in (0 : ℝ)..(3 / 8 : ℝ), fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        (M_right + M_int) * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ)) := by
    calc ‖_‖ ≤ ‖mellinK0 c ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) (fctXi1 L1) *
            fctPsi K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ +
          ‖∫ r in (0 : ℝ)..(3 / 8 : ℝ), fctWarpKA K4 ε c L1 α ((r : ℂ) + (τ : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  calc ‖mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)‖⁻¹ * ‖_‖
      ≤ (Real.exp (1 / (6 * c)) * (1 + τ)) * ((M_right + M_int) * (1 + τ) ^ 7 * Real.exp (-(Real.pi * τ))) := by
        gcongr
    _ = M0 * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ)) := by simp only [M0]; ring

/-! ### Part 2: Logarithmic derivative of `K₀` and derivatives `j = 1, 2` on `τ ≥ 1/2` -/

private noncomputable def fctRk (c L1 : ℝ) (τ : ℝ) : ℂ :=
  1 / (2 * (1 - (τ : ℂ) * Complex.I)) +
    deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I) +
    (c : ℂ) * (stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ))

private lemma mellinK0_log_deriv_imag {c L1 : ℝ} (hc : 0 < c) (τ : ℝ) :
    deriv (fun w : ℂ => mellinK0 c w (fctXi1 L1)) ((τ : ℂ) * Complex.I) /
        mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) = fctRk c L1 τ := by
  set w : ℂ := (τ : ℂ) * Complex.I
  have hw_re0 : w.re = 0 := by simp [w]
  have hw_abs : |w.re| < 1 := by simp [hw_re0]
  have hw_lt1 : w.re < 1 := by simp [hw_re0]
  have h1_re : 0 < (1 - w).re := by simp [hw_re0]
  have hsp : 1 - w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl h1_re)
  have h1w_ne : 1 - w ≠ 0 := Complex.slitPlane_ne_zero hsp
  have hpow : HasDerivAt (fun z : ℂ => (1 - z) ^ (-(1 / 2 : ℂ)))
      ((1 / (2 * (1 - w))) * (1 - w) ^ (-(1 / 2 : ℂ))) w := by
    have hlin : HasDerivAt (fun z : ℂ => 1 - z) (-1) w :=
      ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).congr_deriv (by ring)
    have h1 := hlin.cpow_const hsp (c := -(1 / 2 : ℂ))
    refine h1.congr_deriv ?_
    have hsub : (1 - w) ^ (-(1 / 2 : ℂ) - 1) = (1 - w) ^ (-(1 / 2 : ℂ)) * (1 - w)⁻¹ := by
      rw [show (-(1 / 2 : ℂ) - 1) = -(1 / 2 : ℂ) + (-1 : ℂ) by ring,
        Complex.cpow_add _ _ h1w_ne, Complex.cpow_neg_one]
    rw [hsub]
    field_simp [h1w_ne]
  have hopen_b : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hbd_at : HasDerivAt (FormalResearch.Asymptotics.binetDiff c)
      (deriv (FormalResearch.Asymptotics.binetDiff c) w) w :=
    ((binetDiff_differentiableOn hc).differentiableAt (hopen_b.mem_nhds hw_lt1)).hasDerivAt
  have hbin := hbd_at.cexp
  have hphi := ((hasDerivAt_mellinPhi_fct L1 hw_abs).const_mul (c : ℂ)).cexp
  have hmul : HasDerivAt (fun z : ℂ => mellinK0 c z (fctXi1 L1)) _ w := (hpow.mul hbin).mul hphi
  rw [hmul.deriv]
  have hKne := mellinK0_ne_zero c hw_lt1 (fctXi1 L1)
  have h1ne : (1 - w) ^ (-(1 / 2 : ℂ)) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h1w_ne)
  have h2ne : Complex.exp (FormalResearch.Asymptotics.binetDiff c w) ≠ 0 := Complex.exp_ne_zero _
  have h3ne : Complex.exp ((c : ℂ) * mellinPhi w (fctXi1 L1)) ≠ 0 := Complex.exp_ne_zero _
  unfold fctRk mellinK0 fctRayP
  rw [show (τ : ℂ) * Complex.I = w from rfl]
  field_simp [h1w_ne, h1ne, h2ne, h3ne]
  dsimp only [Pi.mul_apply]
  ring

private lemma fctRk_far_bounds {c L1 : ℝ} (hc : 0 < c) :
    ∃ Mr : ℝ, 0 ≤ Mr ∧ ∀ τ : ℝ, 1 / 2 ≤ τ →
      ‖fctRk c L1 τ‖ ≤ Mr * (1 + τ) ∧
      ‖deriv (fctRk c L1) τ‖ ≤ Mr := by
  obtain ⟨Cg, hCg0, hCg⟩ := stripG_far_bound
  set Mr : ℝ := 1 / 2 + 1 / (6 * c) + c * (Cg + |L1| + Real.pi + 2) + 1
  have hMr0 : 0 ≤ Mr := by positivity
  refine ⟨Mr, hMr0, fun τ hτ => ?_⟩
  have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  have h1τ_ge : 1 ≤ ‖(1 : ℂ) - (τ : ℂ) * Complex.I‖ := by
    simpa using Complex.abs_re_le_norm (1 - (τ : ℂ) * Complex.I)
  have ht1_norm : ‖(1 : ℂ) / (2 * (1 - (τ : ℂ) * Complex.I))‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp, div_le_iff₀ (by linarith)]
    linarith
  have ht2_norm : ‖deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖ ≤
      1 / (12 * c) := by
    have h := FormalResearch.Asymptotics.binetDiff_iteratedDeriv_norm_le hc
      (by simp : ((τ : ℂ) * Complex.I).re ≤ 0) (r := 1) le_rfl
    simpa [iteratedDeriv_one] using h
  have hsg_norm : ‖stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ)‖ ≤ (Cg + |L1|) * (1 + τ) := by
    have him : 1 / 2 ≤ |((τ : ℂ) * Complex.I).im| := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
        Complex.I_re, mul_zero, add_zero, abs_of_pos hτpos]
      exact hτ
    have hsg := hCg ((τ : ℂ) * Complex.I) (by simp) him
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, abs_of_pos hτpos] at hsg
    calc ‖stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ)‖
        ≤ ‖stripG ((τ : ℂ) * Complex.I)‖ + |L1| := by
          simpa [Complex.norm_real, Real.norm_eq_abs] using norm_add_le (stripG ((τ : ℂ) * Complex.I)) (L1 : ℂ)
      _ ≤ Cg * (1 + τ) + |L1| * (1 + τ) := by
          gcongr; exact le_mul_of_one_le_right (abs_nonneg _) (by linarith)
      _ = (Cg + |L1|) * (1 + τ) := by ring
  have hRk0 : ‖fctRk c L1 τ‖ ≤ Mr * (1 + τ) := by
    unfold fctRk
    have hb1 : ‖1 / (2 * (1 - (τ : ℂ) * Complex.I)) +
        deriv (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖ ≤
        (1 / 2 + 1 / (12 * c)) * (1 + τ) := by
      have hsum := (norm_add_le _ _).trans (add_le_add ht1_norm ht2_norm)
      exact hsum.trans (le_mul_of_one_le_right (by positivity) (by linarith))
    have hb2 : ‖(c : ℂ) * (stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ))‖ ≤
        (c * (Cg + |L1|)) * (1 + τ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      calc c * ‖stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ)‖
          ≤ c * ((Cg + |L1|) * (1 + τ)) := mul_le_mul_of_nonneg_left hsg_norm hc.le
        _ = (c * (Cg + |L1|)) * (1 + τ) := by ring
    calc ‖_‖ ≤ (1 / 2 + 1 / (12 * c)) * (1 + τ) + (c * (Cg + |L1|)) * (1 + τ) :=
          (norm_add_le _ _).trans (add_le_add hb1 hb2)
      _ = (1 / 2 + 1 / (12 * c) + c * (Cg + |L1|)) * (1 + τ) := by ring
      _ ≤ Mr * (1 + τ) := by
          gcongr
          simp only [Mr]
          have : 0 ≤ c * (Real.pi + 2) := mul_nonneg hc.le (by linarith [Real.pi_pos])
          linarith [show (1 : ℝ) / (12 * c) ≤ 1 / (6 * c) by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith]
  have hd1 : HasDerivAt (fun t : ℝ => 1 / (2 * (1 - (t : ℂ) * Complex.I)))
      (Complex.I / (2 * (1 - (τ : ℂ) * Complex.I) ^ 2)) τ := by
    have hden_ne : (2 : ℂ) * (1 - (τ : ℂ) * Complex.I) ≠ 0 := by
      intro h0; rw [mul_eq_zero] at h0
      rcases h0 with h | h
      · norm_num at h
      · have := congr_arg Complex.re h; simp at this
    have hlin : HasDerivAt (fun t : ℝ => (2 : ℂ) * (1 - (t : ℂ) * Complex.I)) (-2 * Complex.I) τ := by
      have h1 := ((Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I)
      have h2 := ((hasDerivAt_const τ (1 : ℂ)).sub h1).const_mul (2 : ℂ)
      refine h2.congr_deriv ?_; simp
    have hd := (hasDerivAt_const τ (1 : ℂ)).div hlin hden_ne
    refine hd.congr_deriv ?_
    field_simp [hden_ne]; ring
  have hd2 : HasDerivAt (fun t : ℝ => deriv (FormalResearch.Asymptotics.binetDiff c) ((t : ℂ) * Complex.I))
      (Complex.I * iteratedDeriv 2 (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)) τ := by
    have hopen : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
    have hcd := (binetDiff_differentiableOn hc).contDiffOn hopen (n := 2)
    have hcd1 : ContDiffOn ℂ 1 (deriv (FormalResearch.Asymptotics.binetDiff c)) {z : ℂ | z.re < 1} :=
      (contDiffOn_succ_iff_deriv_of_isOpen hopen (n := 1)).mp hcd |>.2.2
    have hdiff := (hcd1.differentiableOn (by norm_num)).differentiableAt
      (hopen.mem_nhds (by simp : ((τ : ℂ) * Complex.I).re < 1))
    have hl : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I τ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I
    refine (hdiff.hasDerivAt.comp τ hl).congr_deriv ?_
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    ring
  have hd3 : HasDerivAt (fun t : ℝ => (c : ℂ) * (stripG ((t : ℂ) * Complex.I) + (L1 : ℂ)))
      ((c : ℂ) * deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) τ) τ := by
    have hsg := stripG_imag_deriv_pos hτpos
    rw [← hsg.deriv] at hsg
    exact (hsg.add_const (L1 : ℂ)).const_mul (c : ℂ)
  have hd_tot := (hd1.add hd2).add hd3
  have hRk1 : ‖deriv (fctRk c L1) τ‖ ≤ Mr := by
    rw [show deriv (fctRk c L1) τ = _ from hd_tot.deriv]
    have hb1 : ‖Complex.I / (2 * (1 - (τ : ℂ) * Complex.I) ^ 2)‖ ≤ 1 / 2 := by
      rw [norm_div, Complex.norm_I, norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by simp,
        div_le_iff₀ (by have := one_le_pow₀ h1τ_ge (n := 2); positivity)]
      linarith [one_le_pow₀ h1τ_ge (n := 2)]
    have hb2 : ‖Complex.I * iteratedDeriv 2 (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖ ≤
        1 / (6 * c) := by
      rw [norm_mul, Complex.norm_I, one_mul]
      have h := FormalResearch.Asymptotics.binetDiff_iteratedDeriv_norm_le hc
        (by simp : ((τ : ℂ) * Complex.I).re ≤ 0) (r := 2) (by norm_num)
      simpa [Nat.factorial] using h.trans_eq (by ring)
    have hb3 : ‖(c : ℂ) * deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) τ‖ ≤ c * (Real.pi + 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left (stripG_imag_deriv_far_bounds hτ).1 hc.le
    calc ‖_‖ ≤ ‖Complex.I / (2 * (1 - (τ : ℂ) * Complex.I) ^ 2) +
            Complex.I * iteratedDeriv 2 (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖ +
          ‖(c : ℂ) * deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) τ‖ :=
          norm_add_le _ _
      _ ≤ (‖Complex.I / (2 * (1 - (τ : ℂ) * Complex.I) ^ 2)‖ +
            ‖Complex.I * iteratedDeriv 2 (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖) +
          ‖(c : ℂ) * deriv (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) τ‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ 1 / 2 + 1 / (6 * c) + c * (Real.pi + 2) := by linarith
      _ ≤ Mr := by
          simp only [Mr]
          have : 0 ≤ c * (Cg + |L1|) := mul_nonneg hc.le (by positivity)
          linarith
  exact ⟨hRk0, hRk1⟩

private lemma fctPsi_far_pos {K4 ε c L1 α P B Cdesc : ℝ} (hc : 0 < c) (hP : 0 ≤ P)
    (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hEnv : Env2 (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) (fun _ => P))
    (hCD : ∀ τ : ℝ, 1 / 2 ≤ τ →
      ‖fctFint K4 ε c L1 α ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ Cdesc * c⁻¹ / Real.log (2 + τ)) :
    ∃ (N : ℕ) (M : ℝ), 0 ≤ M ∧ ∀ τ : ℝ, 1 / 2 ≤ τ →
      let ψ := fun t : ℝ => fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I)
      ‖ψ τ‖ ≤ M * (1 + τ) ^ N * Real.exp (-(Real.pi * τ)) ∧
      ‖deriv ψ τ‖ ≤ M * (1 + τ) ^ N * Real.exp (-(Real.pi * τ)) ∧
      ‖deriv (deriv ψ) τ‖ ≤ M * (1 + τ) ^ N * Real.exp (-(Real.pi * τ)) := by
  obtain ⟨M0, hM0, hpsi0⟩ := fctPsi_far_zero_pos hc hDh hDc hDb hCD
  obtain ⟨Ma, hMa, hA_ej⟩ := fctWarpA_far_EJOn (ε := ε) (L1 := L1) hc hP hEnv
  obtain ⟨Mr, hMr, hRk_bd⟩ := fctRk_far_bounds (c := c) (L1 := L1) hc
  set ψ : ℝ → ℂ := fun t => fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I)
  set A : ℝ → ℂ := fun t => fctWarpA K4 ε c L1 α ((t : ℂ) * Complex.I)
  set M1 : ℝ := Ma + Mr * M0
  set M2 : ℝ := 2 * Ma + Mr * M0 + Mr * M1
  set M : ℝ := max M0 (max M1 M2)
  refine ⟨12, M, hM0.trans (le_max_left _ _), fun τ hτ => ?_⟩
  have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  have h1τ : 1 ≤ 1 + τ := by linarith
  have hexp_pos : 0 ≤ Real.exp (-(Real.pi * τ)) := (Real.exp_pos _).le
  have hb0_raw := hpsi0 τ hτ
  have hb0 : ‖ψ τ‖ ≤ M * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by
    have hpow : (1 + τ) ^ 8 ≤ (1 + τ) ^ 12 := pow_le_pow_right₀ h1τ (by norm_num)
    have hM : M0 ≤ M := le_max_left _ _
    calc ‖ψ τ‖ ≤ M0 * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ)) := hb0_raw
      _ ≤ M * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by gcongr
  have hode : ∀ t : ℝ, 0 < t → deriv ψ t = Complex.I * (A t - fctRk c L1 t * ψ t) := fun t ht => by
    have h1 := (fctPsi_hasDerivAt_pos (K4 := K4) (ε := ε) (L1 := L1) (α := α)
      hc hDc ⟨B, hDb⟩ hEnv ht).deriv
    rwa [mellinK0_log_deriv_imag hc t] at h1
  have hA0 : ‖A τ‖ ≤ Ma * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) := by
    have h := hA_ej.b0 τ hτ hτpos.ne'
    simp only [ejW, sub_zero, Nat.cast_zero, add_zero, mul_one, Real.rpow_zero, one_mul,
      abs_of_pos hτpos] at h
    rwa [mul_assoc]
  have hA1 : ‖deriv A τ‖ ≤ (2 * Ma) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by
    have h := hA_ej.b1 τ hτ hτpos.ne'
    simp only [ejW, zero_sub, Nat.cast_one, abs_of_pos hτpos, Real.rpow_neg hτpos.le,
      Real.rpow_one] at h
    have hτinv : τ⁻¹ ≤ 2 := by
      simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hτ
    have h12 : (1 + τ) ^ (11 + 1) = (1 + τ) ^ 12 := rfl
    rw [h12, mul_one] at h
    calc ‖deriv A τ‖ ≤ Ma * (τ⁻¹ * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ))) := h
      _ ≤ Ma * (2 * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ))) := by gcongr
      _ = (2 * Ma) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by ring
  obtain ⟨hRk0, hRk1⟩ := hRk_bd τ hτ
  have h9_11 : (1 + τ) ^ 9 ≤ (1 + τ) ^ 11 := pow_le_pow_right₀ h1τ (by norm_num)
  have h8_12 : (1 + τ) ^ 8 ≤ (1 + τ) ^ 12 := pow_le_pow_right₀ h1τ (by norm_num)
  have hb1_raw : ‖deriv ψ τ‖ ≤ M1 * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) := by
    rw [hode τ hτpos, norm_mul, Complex.norm_I, one_mul]
    have hterm : ‖fctRk c L1 τ * ψ τ‖ ≤ (Mr * M0) * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) := by
      calc ‖fctRk c L1 τ * ψ τ‖ = ‖fctRk c L1 τ‖ * ‖ψ τ‖ := norm_mul _ _
        _ ≤ (Mr * (1 + τ)) * (M0 * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ))) :=
            mul_le_mul hRk0 hb0_raw (norm_nonneg _) (by positivity)
        _ = (Mr * M0) * (1 + τ) ^ 9 * Real.exp (-(Real.pi * τ)) := by ring
        _ ≤ (Mr * M0) * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) := by gcongr
    calc ‖A τ - fctRk c L1 τ * ψ τ‖ ≤ ‖A τ‖ + ‖fctRk c L1 τ * ψ τ‖ := norm_sub_le _ _
      _ ≤ Ma * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) +
            (Mr * M0) * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) := add_le_add hA0 hterm
      _ = M1 * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ)) := by simp only [M1]; ring
  have hb1 : ‖deriv ψ τ‖ ≤ M * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by
    have hpow : (1 + τ) ^ 11 ≤ (1 + τ) ^ 12 := pow_le_pow_right₀ h1τ (by norm_num)
    have hM : M1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    exact hb1_raw.trans (by gcongr)
  have hderiv2 : deriv (deriv ψ) τ =
      Complex.I * (deriv A τ - (deriv (fctRk c L1) τ * ψ τ + fctRk c L1 τ * deriv ψ τ)) := by
    have hev : deriv ψ =ᶠ[𝓝 τ] fun t : ℝ => Complex.I * (A t - fctRk c L1 t * ψ t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hτpos] with t ht
      exact hode t ht
    have hdA : HasDerivAt A (deriv A τ) τ :=
      ((hA_ej.c2.differentiableOn (by norm_num)).differentiableAt (isOpen_ne.mem_nhds hτpos.ne')).hasDerivAt
    have hdψ : HasDerivAt ψ (deriv ψ τ) τ := by
      have h := fctPsi_hasDerivAt_pos (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc ⟨B, hDb⟩ hEnv hτpos
      exact h.congr_deriv h.deriv.symm
    have hdRk : HasDerivAt (fctRk c L1) (deriv (fctRk c L1) τ) τ := by
      have h1d : DifferentiableAt ℝ (fun t : ℝ => 1 / (2 * (1 - (t : ℂ) * Complex.I))) τ := by
        have hne : (2 : ℂ) * (1 - (τ : ℂ) * Complex.I) ≠ 0 := by
          intro h0; rw [mul_eq_zero] at h0
          rcases h0 with h | h
          · norm_num at h
          · have := congr_arg Complex.re h; simp at this
        exact (differentiableAt_const _).div (by fun_prop) hne
      have h2d : DifferentiableAt ℝ (fun t : ℝ => deriv (FormalResearch.Asymptotics.binetDiff c) ((t : ℂ) * Complex.I)) τ := by
        have hopen : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
        have hcd := (binetDiff_differentiableOn hc).contDiffOn hopen (n := 2)
        have hcd1 := (contDiffOn_succ_iff_deriv_of_isOpen hopen (n := 1)).mp hcd |>.2.2
        have hdiff_at := ((hcd1.differentiableOn (by norm_num)).differentiableAt
          (hopen.mem_nhds (by simp : ((τ : ℂ) * Complex.I).re < 1))).hasDerivAt
        have hl : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I τ :=
          ((hasDerivAt_id τ).ofReal_comp).mul_const Complex.I |>.congr_deriv (by simp)
        exact (hdiff_at.comp τ hl).differentiableAt
      have h3d : DifferentiableAt ℝ (fun t : ℝ => (c : ℂ) * (stripG ((t : ℂ) * Complex.I) + (L1 : ℂ))) τ :=
        (((stripG_imag_deriv_pos hτpos).differentiableAt).add_const _).const_mul _
      exact ((h1d.add h2d).add h3d).hasDerivAt
    have hprod := hdRk.mul hdψ
    have hcomb := (hdA.sub hprod).const_mul Complex.I
    rw [hev.deriv_eq, show deriv (fun t : ℝ => Complex.I * (A t - fctRk c L1 t * ψ t)) τ = _ from hcomb.deriv]
  have hb2_raw : ‖deriv (deriv ψ) τ‖ ≤ M2 * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by
    rw [hderiv2, norm_mul, Complex.norm_I, one_mul]
    have ht1 : ‖deriv (fctRk c L1) τ * ψ τ‖ ≤ (Mr * M0) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by
      calc ‖deriv (fctRk c L1) τ * ψ τ‖ = ‖deriv (fctRk c L1) τ‖ * ‖ψ τ‖ := norm_mul _ _
        _ ≤ Mr * (M0 * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ))) :=
            mul_le_mul hRk1 hb0_raw (norm_nonneg _) hMr
        _ = (Mr * M0) * (1 + τ) ^ 8 * Real.exp (-(Real.pi * τ)) := by ring
        _ ≤ (Mr * M0) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by gcongr
    have ht2 : ‖fctRk c L1 τ * deriv ψ τ‖ ≤ (Mr * M1) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by
      calc ‖fctRk c L1 τ * deriv ψ τ‖ = ‖fctRk c L1 τ‖ * ‖deriv ψ τ‖ := norm_mul _ _
        _ ≤ (Mr * (1 + τ)) * (M1 * (1 + τ) ^ 11 * Real.exp (-(Real.pi * τ))) :=
            mul_le_mul hRk0 hb1_raw (norm_nonneg _) (by positivity)
        _ = (Mr * M1) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by ring
    calc ‖deriv A τ - (deriv (fctRk c L1) τ * ψ τ + fctRk c L1 τ * deriv ψ τ)‖
        ≤ ‖deriv A τ‖ + ‖deriv (fctRk c L1) τ * ψ τ + fctRk c L1 τ * deriv ψ τ‖ := norm_sub_le _ _
      _ ≤ ‖deriv A τ‖ + (‖deriv (fctRk c L1) τ * ψ τ‖ + ‖fctRk c L1 τ * deriv ψ τ‖) :=
          add_le_add le_rfl (norm_add_le (deriv (fctRk c L1) τ * ψ τ) (fctRk c L1 τ * deriv ψ τ))
      _ ≤ (2 * Ma) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) +
            ((Mr * M0) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) +
              (Mr * M1) * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ))) :=
          add_le_add hA1 (add_le_add ht1 ht2)
      _ = M2 * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) := by simp only [M2]; ring
  have hb2 : ‖deriv (deriv ψ) τ‖ ≤ M * (1 + τ) ^ 12 * Real.exp (-(Real.pi * τ)) :=
    hb2_raw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)) hexp_pos)
  exact ⟨hb0, hb1, hb2⟩

/-! ### Part 3: Reflection to `τ ≤ -1/2` and main theorem `fctPsi_far` -/

private lemma conj_reflect_derivs {ψ : ℝ → ℂ} (hconj : ∀ t : ℝ, ψ (-t) = starRingEnd ℂ (ψ t))
    (hdiff : DifferentiableOn ℝ ψ {t : ℝ | 0 < t})
    (hdiff2 : DifferentiableOn ℝ (deriv ψ) {t : ℝ | 0 < t})
    {τ : ℝ} (hτ : τ < 0) :
    ‖ψ τ‖ = ‖ψ (-τ)‖ ∧
    ‖deriv ψ τ‖ = ‖deriv ψ (-τ)‖ ∧
    ‖deriv (deriv ψ) τ‖ = ‖deriv (deriv ψ) (-τ)‖ := by
  have hpos : 0 < -τ := neg_pos.mpr hτ
  have hnh : {t : ℝ | 0 < t} ∈ 𝓝 (-τ) := isOpen_Ioi.mem_nhds hpos
  have heq : ψ = fun t : ℝ => Complex.conjCLE (ψ (-t)) := by
    funext t; simpa using (congr_arg (starRingEnd ℂ) (hconj t)).symm
  have hrefl1 : ∀ t : ℝ, t < 0 → deriv ψ t = -Complex.conjCLE (deriv ψ (-t)) := fun t ht => by
    have h0 : HasDerivAt ψ (deriv ψ (-t)) (-t) :=
      (hdiff.differentiableAt (isOpen_Ioi.mem_nhds (neg_pos.mpr ht))).hasDerivAt
    have h1 := h0.scomp t (hasDerivAt_neg t)
    have hpt := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t h1
    have hfn : (⇑Complex.conjCLE ∘ ψ ∘ Neg.neg) = ψ := heq.symm
    rw [hfn] at hpt
    rw [hpt.deriv]; simp
  have hd2 : HasDerivAt (deriv ψ) (deriv (deriv ψ) (-τ)) (-τ) := (hdiff2.differentiableAt hnh).hasDerivAt
  have hrefl2_at : deriv (deriv ψ) τ = Complex.conjCLE (deriv (deriv ψ) (-τ)) := by
    have hev : deriv ψ =ᶠ[𝓝 τ] fun t : ℝ => -Complex.conjCLE (deriv ψ (-t)) := by
      filter_upwards [isOpen_Iio.mem_nhds hτ] with t ht
      exact hrefl1 t ht
    have h1 := hd2.scomp τ (hasDerivAt_neg τ)
    have hpt := (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt τ h1).neg
    rw [hev.deriv_eq, show deriv (fun t : ℝ => -Complex.conjCLE (deriv ψ (-t))) τ = _ from hpt.deriv]
    simp
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [show τ = -(-τ) by ring, hconj (-τ), Complex.norm_conj]
  · rw [hrefl1 τ hτ, norm_neg]; simp
  · rw [hrefl2_at]; simp

/-- **Far left-edge decay (`fct:splitting`)**: on `|τ| ≥ 1/2`, `Ψ_c(iτ)` and its first two
derivatives decay like `(1 + |τ|)^N exp(-π |τ|)` under `FctDescentStmt h`. -/
theorem fctPsi_far {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      let ψ := fun t : ℝ => fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I)
      ∃ (N : ℕ) (M : ℝ), 0 ≤ M ∧ ∀ τ : ℝ, 1 / 2 ≤ |τ| →
        ‖ψ τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(Real.pi * |τ|)) ∧
        ‖deriv ψ τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(Real.pi * |τ|)) ∧
        ‖deriv (deriv ψ) τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(Real.pi * |τ|)) := by
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨c0D, hcD⟩ := fctDcomp_compData hK4 ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨Cdesc, c0Desc, hDesc⟩ := hD
  refine ⟨max (max c0D c0Desc) 1, fun ε c hε hc => ?_⟩
  have hc1 : 1 ≤ c := hc.trans' (le_max_right _ _)
  have hcpos : 0 < c := by linarith
  have hcD' := hcD ε c hε (hc.trans' ((le_max_left _ _).trans (le_max_left _ _)))
  have hcDesc' := hDesc ε c hε (hc.trans' ((le_max_right _ _).trans (le_max_left _ _)))
  obtain ⟨B, hB⟩ := hcD'.bd
  obtain ⟨P, hP, hEnv⟩ := hcD'.env
  have hCD : ∀ τ : ℝ, 1 / 2 ≤ τ →
      ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        Cdesc * c⁻¹ / Real.log (2 + τ) := fun τ hτ => by
    have h1 := hcDesc' (3 / 8) τ (by norm_num) (by norm_num)
    simpa [abs_of_pos (by linarith : 0 < τ)] using h1
  obtain ⟨N, M, hM, hpos⟩ := fctPsi_far_pos hcpos hP hcD'.hol hcD'.cont hB hEnv hCD
  refine ⟨N, M, hM, fun τ hτ => ?_⟩
  rcases le_or_gt 0 τ with hτ0 | hτneg
  · have habs : |τ| = τ := abs_of_nonneg hτ0
    simpa [habs] using hpos τ (by linarith)
  · have habs : |τ| = -τ := abs_of_neg hτneg
    have hneg_ge : 1 / 2 ≤ -τ := by linarith
    have hconj : ∀ t : ℝ, fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (((-t : ℝ) : ℂ) * Complex.I) =
        starRingEnd ℂ (fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I)) := by
      intro t
      have heq : ((-t : ℝ) : ℂ) * Complex.I = starRingEnd ℂ ((t : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp
      rw [heq]
      exact fctPsi_conj hcD'.conj (by simp) (by simp)
    have hcd_pos : ContDiffOn ℝ 2 (fun t : ℝ =>
        fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I)) {t : ℝ | 0 < t} :=
      (fctPsi_contDiffOn_left hcpos hcD'.cont ⟨B, hB⟩ hcD'.conj hEnv).mono fun _ ht => ne_of_gt ht
    have hdiff1 : DifferentiableOn ℝ (fun t : ℝ =>
        fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I)) {t : ℝ | 0 < t} :=
      hcd_pos.differentiableOn (by norm_num)
    have hdiff2 : DifferentiableOn ℝ (deriv (fun t : ℝ =>
        fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I))) {t : ℝ | 0 < t} :=
      ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi (n := 1)).mp hcd_pos).2.2.differentiableOn
        (by norm_num)
    have hrefl := conj_reflect_derivs hconj hdiff1 hdiff2 hτneg
    have hp := hpos (-τ) hneg_ge
    simpa [habs, hrefl.1, hrefl.2.1, hrefl.2.2] using hp

/-- info: 'FormalResearch.SignUncertainty.fctPsi_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPsi_far

end FormalResearch.SignUncertainty
