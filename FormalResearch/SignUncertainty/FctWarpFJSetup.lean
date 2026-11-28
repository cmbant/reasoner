/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpFJ
public import FormalResearch.SignUncertainty.FctInnerPhase
public import FormalResearch.SignUncertainty.FctInnerCoord
public import FormalResearch.SignUncertainty.FctWarpZero
public import FormalResearch.SignUncertainty.FctInnerB1

/-!
# Chart centering helper package (`FctWarpFJSetup`)

Shared compensator bounds (`r = 0, 1, 2` at `α = 0` and `r = 0` for `vAlpha 1`),
`Φ₀` / `Φ₁` comparison helpers, log/exp Lipchitz bridges, and `FctWarpChartData`
for `FctWarpFJCenter` (`fct:warp-asymp` (1)).

Class: proved, unconditional.
-/

@[expose] public section

open Set Filter Topology Metric MeasureTheory
open scoped Real ContDiff
open FormalResearch.CohnElkies
open FormalResearch.Special
open FormalResearch.SignUncertainty.CtCfu
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

lemma rpow_neg_quarter_pow4 {c : ℝ} (hc : 0 < c) :
    (c ^ (-(1 / 4 : ℝ))) ^ 4 = c⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  norm_num [Real.rpow_neg_one]

lemma rpow_neg_quarter_sq {c : ℝ} (hc : 0 < c) :
    (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num

lemma rpow_neg_third_sq {c : ℝ} (hc : 0 < c) :
    (c ^ (-(1 / 3 : ℝ))) ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num

lemma rpow_third_mul_neg_quarter {c : ℝ} (hc : 0 < c) :
    c ^ (-(1 / 3 : ℝ)) / c ^ (-(1 / 4 : ℝ)) = c ^ (-(1 / 12 : ℝ)) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg hc.le, ← Real.rpow_add hc]; norm_num

private lemma thetaD_center_decomp {K4 c τ₁ : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c) (hτ₁ : 0 < τ₁)
    (hτ₁_le : τ₁ ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (hcτ : τ₁ ^ 4 * c = 1)
    (hcd_v : ContDiff ℝ (⊤ : ℕ∞) (v0Base StripKernelChoice.star τ₁) ∧ ContDiff ℝ (⊤ : ℕ∞) (v0Marg τ₁) ∧
      ContDiff ℝ (⊤ : ℕ∞) (vAlpha 0 τ₁) ∧ ContDiff ℝ (⊤ : ℕ∞) (v1Base StripKernelChoice.star c τ₁) ∧
      ContDiff ℝ (⊤ : ℕ∞) (v1Marg c τ₁) ∧ ContDiff ℝ (⊤ : ℕ∞) (vTotal StripKernelChoice.star K4 c 0 τ₁))
    (hcs_v : HasCompactSupport (v0Base StripKernelChoice.star τ₁) ∧ HasCompactSupport (v0Marg τ₁) ∧
      HasCompactSupport (vAlpha 0 τ₁) ∧
      HasCompactSupport (v1Base StripKernelChoice.star c τ₁) ∧ HasCompactSupport (v1Marg c τ₁) ∧
      HasCompactSupport (v0 StripKernelChoice.star K4 τ₁) ∧ HasCompactSupport (v1 StripKernelChoice.star K4 c τ₁)) :
    ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) ∧
    ∀ (r : ℕ) (t : ℝ), iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) t =
      iteratedDeriv r (fctThetaD (v0Base StripKernelChoice.star τ₁)) t +
        K4 * iteratedDeriv r (fctThetaD (v0Marg τ₁)) t +
        iteratedDeriv r (fctThetaD (v1Base StripKernelChoice.star c τ₁)) t +
        K4 * iteratedDeriv r (fctThetaD (v1Marg c τ₁)) t := by
  obtain ⟨hv0b_cs, hv0m_cs, hva0_cs, hv1b_cs, hv1m_cs, hv0_cs, hv1_cs⟩ := hcs_v
  have hva_info := fctThetaD_vAlpha_eq hK4 hc hτ₁ hτ₁_le hcτ 0
  have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) (v0 StripKernelChoice.star K4 τ₁) := hcd_v.1.add (contDiff_const.mul hcd_v.2.1)
  have hv1_cd : ContDiff ℝ (⊤ : ℕ∞) (v1 StripKernelChoice.star K4 c τ₁) := hcd_v.2.2.2.1.add (contDiff_const.mul hcd_v.2.2.2.2.1)
  have hsum_fn : fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁) =
      fun t => fctThetaD (v0Base StripKernelChoice.star τ₁) t + K4 * fctThetaD (v0Marg τ₁) t +
        fctThetaD (v1Base StripKernelChoice.star c τ₁) t + K4 * fctThetaD (v1Marg c τ₁) t := by
    ext s
    have h1 := fctThetaD_linear hv0_cd hv0_cs hv1_cd hv1_cs 1 1 s
    have h2 := fctThetaD_linear (hv0_cd.add hv1_cd) (hv0_cs.add hv1_cs) hcd_v.2.2.1 hva0_cs 1 1 s
    have h0 := fctThetaD_linear hcd_v.1 hv0b_cs hcd_v.2.1 hv0m_cs 1 K4 s
    have h1' := fctThetaD_linear hcd_v.2.2.2.1 hv1b_cs hcd_v.2.2.2.2.1 hv1m_cs 1 K4 s
    have ha0 : fctThetaD (vAlpha 0 τ₁) s = 0 := by simpa using (hva_info s).1
    simp only [one_mul] at h1 h2 h0 h1'
    change fctThetaD (fun u => (v0 StripKernelChoice.star K4 τ₁ u +
      v1 StripKernelChoice.star K4 c τ₁ u) + vAlpha 0 τ₁ u) s = _
    rw [h2, ha0, add_zero, h1,
      show v0 StripKernelChoice.star K4 τ₁ = fun s => v0Base StripKernelChoice.star τ₁ s + K4 * v0Marg τ₁ s from rfl,
      show v1 StripKernelChoice.star K4 c τ₁ = fun s => v1Base StripKernelChoice.star c τ₁ s + K4 * v1Marg c τ₁ s from rfl,
      h0, h1']; ring
  have hcd_b0 := contDiff_fctThetaD hcd_v.1 hv0b_cs
  have hcd_m0 := contDiff_fctThetaD hcd_v.2.1 hv0m_cs
  have hcd_b1 := contDiff_fctThetaD hcd_v.2.2.2.1 hv1b_cs
  have hcd_m1 := contDiff_fctThetaD hcd_v.2.2.2.2.1 hv1m_cs
  refine ⟨by rw [hsum_fn]; exact ((hcd_b0.add (contDiff_const.mul hcd_m0)).add hcd_b1).add (contDiff_const.mul hcd_m1),
    fun r t => by
      rw [hsum_fn]
      have hb0a : ContDiffAt ℝ r (fctThetaD (v0Base StripKernelChoice.star τ₁)) t :=
        hcd_b0.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hm0a : ContDiffAt ℝ r (fctThetaD (v0Marg τ₁)) t :=
        hcd_m0.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hb1a : ContDiffAt ℝ r (fctThetaD (v1Base StripKernelChoice.star c τ₁)) t :=
        hcd_b1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hm1a : ContDiffAt ℝ r (fctThetaD (v1Marg c τ₁)) t :=
        hcd_m1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hm0k : ContDiffAt ℝ r (fun x => K4 * fctThetaD (v0Marg τ₁) x) t := contDiffAt_const.mul hm0a
      have hm1k : ContDiffAt ℝ r (fun x => K4 * fctThetaD (v1Marg c τ₁) x) t := contDiffAt_const.mul hm1a
      have d1 : iteratedDeriv r (fun x => (fctThetaD (v0Base StripKernelChoice.star τ₁) x +
          K4 * fctThetaD (v0Marg τ₁) x + fctThetaD (v1Base StripKernelChoice.star c τ₁) x) +
          K4 * fctThetaD (v1Marg c τ₁) x) t =
          iteratedDeriv r (fun x => fctThetaD (v0Base StripKernelChoice.star τ₁) x +
            K4 * fctThetaD (v0Marg τ₁) x + fctThetaD (v1Base StripKernelChoice.star c τ₁) x) t +
          iteratedDeriv r (fun x => K4 * fctThetaD (v1Marg c τ₁) x) t := by
        simpa only [Pi.add_def] using iteratedDeriv_add ((hb0a.add hm0k).add hb1a) hm1k
      have d2 : iteratedDeriv r (fun x => (fctThetaD (v0Base StripKernelChoice.star τ₁) x +
          K4 * fctThetaD (v0Marg τ₁) x) + fctThetaD (v1Base StripKernelChoice.star c τ₁) x) t =
          iteratedDeriv r (fun x => fctThetaD (v0Base StripKernelChoice.star τ₁) x +
            K4 * fctThetaD (v0Marg τ₁) x) t +
          iteratedDeriv r (fctThetaD (v1Base StripKernelChoice.star c τ₁)) t := by
        simpa only [Pi.add_def] using iteratedDeriv_add (hb0a.add hm0k) hb1a
      have d3 : iteratedDeriv r (fun x => fctThetaD (v0Base StripKernelChoice.star τ₁) x +
          K4 * fctThetaD (v0Marg τ₁) x) t =
          iteratedDeriv r (fctThetaD (v0Base StripKernelChoice.star τ₁)) t +
          iteratedDeriv r (fun x => K4 * fctThetaD (v0Marg τ₁) x) t := by
        simpa only [Pi.add_def] using iteratedDeriv_add hb0a hm0k
      rw [d1, d2, d3]
      simp only [iteratedDeriv_const_mul_field]⟩

private lemma abs_add4_le_linear {a b c d A B C D K4 M : ℝ} (hK4 : 1 ≤ K4) (hM : 0 ≤ M)
    (ha : |a| ≤ A * M) (hb : |b| ≤ B * M) (hc : |c| ≤ C * M) (hd : |d| ≤ D * M)
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    |a + K4 * b + c + K4 * d| ≤ (A + B + C + D + 1) * K4 * M := by
  have hK4_pos : 0 < K4 := lt_of_lt_of_le zero_lt_one hK4
  have ha' : |a| ≤ K4 * (A * M) := ha.trans (le_mul_of_one_le_left (mul_nonneg hA hM) hK4)
  have hc' : |c| ≤ K4 * (C * M) := hc.trans (le_mul_of_one_le_left (mul_nonneg hC hM) hK4)
  have hb' : |K4 * b| ≤ K4 * (B * M) := by
    rw [abs_mul, abs_of_pos hK4_pos]; exact mul_le_mul_of_nonneg_left hb hK4_pos.le
  have hd' : |K4 * d| ≤ K4 * (D * M) := by
    rw [abs_mul, abs_of_pos hK4_pos]; exact mul_le_mul_of_nonneg_left hd hK4_pos.le
  have htri : |a + K4 * b + c + K4 * d| ≤ |a| + |K4 * b| + |c| + |K4 * d| := by
    have h1 := abs_add_le (a + K4 * b + c) (K4 * d)
    have h2 := abs_add_le (a + K4 * b) c
    have h3 := abs_add_le a (K4 * b)
    linarith
  have hbound : |a| + |K4 * b| + |c| + |K4 * d| ≤ (A + B + C + D) * K4 * M := by
    calc |a| + |K4 * b| + |c| + |K4 * d|
        ≤ K4 * (A * M) + K4 * (B * M) + K4 * (C * M) + K4 * (D * M) := by linarith
      _ = (A + B + C + D) * K4 * M := by ring
  exact htri.trans (hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith) hK4_pos.le) hM))

private lemma thetaD_center_step
    {C_th0b C_th0m C_tha C_th1b C_th1m : ℕ → ℝ}
    (h0n : 0 ≤ C_th0b 0 ∧ 0 ≤ C_th0m 0 ∧ 0 ≤ C_tha 0 ∧ 0 ≤ C_th1b 0 ∧ 0 ≤ C_th1m 0)
    (h1n : 0 ≤ C_th0b 1 ∧ 0 ≤ C_th0m 1 ∧ 0 ≤ C_tha 1 ∧ 0 ≤ C_th1b 1 ∧ 0 ≤ C_th1m 1)
    (h2n : 0 ≤ C_th0b 2 ∧ 0 ≤ C_th0m 2 ∧ 0 ≤ C_tha 2 ∧ 0 ≤ C_th1b 2 ∧ 0 ≤ C_th1m 2)
    {K4 c τ₁ : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c) (hτ₁ : 0 < τ₁) (hτ₁_1 : τ₁ ≤ 1)
    (hcτ : τ₁ ^ 4 * c = 1) (hiter_eq : ∀ (r : ℕ) (t : ℝ),
      iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) t =
        iteratedDeriv r (fctThetaD (v0Base StripKernelChoice.star τ₁)) t +
          K4 * iteratedDeriv r (fctThetaD (v0Marg τ₁)) t +
          iteratedDeriv r (fctThetaD (v1Base StripKernelChoice.star c τ₁)) t +
          K4 * iteratedDeriv r (fctThetaD (v1Marg c τ₁)) t)
    (hth_in : ∀ (r : ℕ) (t : ℝ), |t| ≤ 12 * τ₁ →
      |iteratedDeriv r (fctThetaD (v0Base StripKernelChoice.star τ₁)) t| ≤ C_th0b r * τ₁ ^ ((2 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v0Marg τ₁)) t| ≤ C_th0m r * τ₁ ^ ((4 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (vAlpha 0 τ₁)) t| ≤ C_tha r * |0| * τ₁ ^ ((2 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v1Base StripKernelChoice.star c τ₁)) t| ≤ C_th1b r * c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v1Marg c τ₁)) t| ≤ C_th1m r * c⁻¹ * τ₁ ^ ((1 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)))
    (hth_inA : ∀ (r : ℕ) (t : ℝ), |t| ≤ 12 * τ₁ →
      |iteratedDeriv r (fctThetaD (v0Base StripKernelChoice.star τ₁)) t| ≤ C_th0b r * τ₁ ^ ((2 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v0Marg τ₁)) t| ≤ C_th0m r * τ₁ ^ ((4 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (vAlpha (τ₁ ^ 2) τ₁)) t| ≤ C_tha r * |τ₁ ^ 2| * τ₁ ^ ((2 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v1Base StripKernelChoice.star c τ₁)) t| ≤ C_th1b r * c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v1Marg c τ₁)) t| ≤ C_th1m r * c⁻¹ * τ₁ ^ ((1 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)))
    (hAe_fn : ∀ τ, fctThetaD (vAlpha (τ₁ ^ 2) τ₁) τ = τ₁ ^ 2 * fctThetaD (vAlpha 1 τ₁) τ) :
    ∀ τ : ℝ, |τ| ≤ 12 * τ₁ →
      |fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁) τ| ≤
        (C_th0b 0 + C_th0m 0 + C_th1b 0 + C_th1m 0 + 1) * K4 * τ₁ ^ 2 * (|τ| / τ₁) ^ 11 ∧
      |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) τ| ≤
        (C_th0b 1 + C_th0m 1 + C_th1b 1 + C_th1m 1 + 1) * K4 * τ₁ ∧
      |iteratedDeriv 2 (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) τ| ≤
        (C_th0b 2 + C_th0m 2 + C_th1b 2 + C_th1m 2 + 1) * K4 * (|τ| / τ₁) ^ 9 ∧
      |fctThetaD (vAlpha 1 τ₁) τ| ≤ (C_tha 0 + 1) * τ₁ ^ 2 * (|τ| / τ₁) ^ 11 := by
  intro τ hτ
  have hcinv : c⁻¹ = τ₁ ^ 4 := inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact hcτ)
  have hm0 := hth_in 0 τ hτ; have hm1 := hth_in 1 τ hτ; have hm2 := hth_in 2 τ hτ
  have hrat_nn : 0 ≤ |τ| / τ₁ := div_nonneg (abs_nonneg τ) hτ₁.le
  have hr11_nn : 0 ≤ (|τ| / τ₁) ^ 11 := pow_nonneg hrat_nn 11
  have hr9_nn : 0 ≤ (|τ| / τ₁) ^ 9 := pow_nonneg hrat_nn 9
  have hτ2_le : τ₁ ^ 2 ≤ 1 := pow_le_one₀ hτ₁.le hτ₁_1
  have hτ3_le : τ₁ ^ 3 ≤ 1 := pow_le_one₀ hτ₁.le hτ₁_1
  have hτ42 : τ₁ ^ 4 ≤ τ₁ ^ 2 := by
    rw [show τ₁ ^ 4 = τ₁ ^ 2 * τ₁ ^ 2 by ring]; exact mul_le_of_le_one_right (sq_nonneg _) hτ2_le
  have hτ32 : τ₁ ^ 3 ≤ τ₁ ^ 2 := by
    rw [show τ₁ ^ 3 = τ₁ ^ 2 * τ₁ by ring]; exact mul_le_of_le_one_right (sq_nonneg _) hτ₁_1
  have hτ52 : τ₁ ^ 5 ≤ τ₁ ^ 2 := by
    rw [show τ₁ ^ 5 = τ₁ ^ 2 * τ₁ ^ 3 by ring]; exact mul_le_of_le_one_right (sq_nonneg _) hτ3_le
  have hτ21 : τ₁ ^ 2 ≤ τ₁ := by
    rw [_root_.sq]; exact mul_le_of_le_one_right hτ₁.le hτ₁_1
  have hτ31 : τ₁ ^ 3 ≤ τ₁ := by
    rw [show τ₁ ^ 3 = τ₁ * τ₁ ^ 2 by ring]; exact mul_le_of_le_one_right hτ₁.le hτ2_le
  have hτ41 : τ₁ ^ 4 ≤ τ₁ := by
    rw [show τ₁ ^ 4 = τ₁ * τ₁ ^ 3 by ring]; exact mul_le_of_le_one_right hτ₁.le hτ3_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e0 := hiter_eq 0 τ
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, Nat.sub_zero] at e0 hm0
    have hz2 : τ₁ ^ (2 : ℤ) = τ₁ ^ 2 := by rw [show (2 : ℤ) = (2 : ℕ) by rfl, zpow_natCast]
    have hz4 : τ₁ ^ (4 : ℤ) = τ₁ ^ 4 := by rw [show (4 : ℤ) = (4 : ℕ) by rfl, zpow_natCast]
    have hz1 : τ₁ ^ (1 : ℤ) = τ₁ := zpow_one τ₁
    rw [hz2, hz4, hz1] at hm0
    have hb0 : |fctThetaD (v0Base StripKernelChoice.star τ₁) τ| ≤ C_th0b 0 * (τ₁ ^ 2 * (|τ| / τ₁) ^ 11) := by
      simpa [mul_assoc] using hm0.1.trans
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg h0n.1 (sq_nonneg τ₁)))
    have hm0' : |fctThetaD (v0Marg τ₁) τ| ≤ C_th0m 0 * (τ₁ ^ 2 * (|τ| / τ₁) ^ 11) := by
      have h := hm0.2.1.trans (mul_le_mul_of_nonneg_left (min_le_right _ _)
        (mul_nonneg h0n.2.1 (pow_nonneg hτ₁.le 4)))
      calc |fctThetaD (v0Marg τ₁) τ| ≤ C_th0m 0 * τ₁ ^ 4 * (|τ| / τ₁) ^ 11 := h
        _ ≤ C_th0m 0 * τ₁ ^ 2 * (|τ| / τ₁) ^ 11 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ42 h0n.2.1) hr11_nn
        _ = C_th0m 0 * (τ₁ ^ 2 * (|τ| / τ₁) ^ 11) := by ring
    have hb1 : |fctThetaD (v1Base StripKernelChoice.star c τ₁) τ| ≤ C_th1b 0 * (τ₁ ^ 2 * (|τ| / τ₁) ^ 11) := by
      have hcτ1 : c⁻¹ * τ₁ ^ (-1 : ℤ) = τ₁ ^ 3 := by
        rw [hcinv, zpow_neg_one, show τ₁ ^ 4 * τ₁⁻¹ = τ₁ ^ 3 * (τ₁ * τ₁⁻¹) by ring,
          mul_inv_cancel₀ hτ₁.ne', mul_one]
      have h1 := hm0.2.2.2.1.trans (mul_le_mul_of_nonneg_left (min_le_right _ _)
        (mul_nonneg (mul_nonneg h0n.2.2.2.1 (inv_nonneg.mpr hc.le)) (zpow_nonneg hτ₁.le _)))
      have h1' : C_th1b 0 * c⁻¹ * τ₁ ^ (-1 : ℤ) * (|τ| / τ₁) ^ 11 = C_th1b 0 * τ₁ ^ 3 * (|τ| / τ₁) ^ 11 := by
        calc C_th1b 0 * c⁻¹ * τ₁ ^ (-1 : ℤ) * (|τ| / τ₁) ^ 11
            = C_th1b 0 * (c⁻¹ * τ₁ ^ (-1 : ℤ)) * (|τ| / τ₁) ^ 11 := by ring
          _ = C_th1b 0 * τ₁ ^ 3 * (|τ| / τ₁) ^ 11 := by rw [hcτ1]
      calc |fctThetaD (v1Base StripKernelChoice.star c τ₁) τ| ≤ C_th1b 0 * c⁻¹ * τ₁ ^ (-1 : ℤ) * (|τ| / τ₁) ^ 11 := by
              simpa [mul_assoc] using h1
        _ = C_th1b 0 * τ₁ ^ 3 * (|τ| / τ₁) ^ 11 := h1'
        _ ≤ C_th1b 0 * τ₁ ^ 2 * (|τ| / τ₁) ^ 11 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ32 h0n.2.2.2.1) hr11_nn
        _ = C_th1b 0 * (τ₁ ^ 2 * (|τ| / τ₁) ^ 11) := by ring
    have hm1' : |fctThetaD (v1Marg c τ₁) τ| ≤ C_th1m 0 * (τ₁ ^ 2 * (|τ| / τ₁) ^ 11) := by
      have hcτ1 : c⁻¹ * τ₁ = τ₁ ^ 5 := by rw [hcinv]; ring
      have h1 := hm0.2.2.2.2.trans (mul_le_mul_of_nonneg_left (min_le_right _ _)
        (mul_nonneg (mul_nonneg h0n.2.2.2.2 (inv_nonneg.mpr hc.le)) hτ₁.le))
      have h1' : C_th1m 0 * c⁻¹ * τ₁ * (|τ| / τ₁) ^ 11 = C_th1m 0 * τ₁ ^ 5 * (|τ| / τ₁) ^ 11 := by
        calc C_th1m 0 * c⁻¹ * τ₁ * (|τ| / τ₁) ^ 11 = C_th1m 0 * (c⁻¹ * τ₁) * (|τ| / τ₁) ^ 11 := by ring
          _ = C_th1m 0 * τ₁ ^ 5 * (|τ| / τ₁) ^ 11 := by rw [hcτ1]
      calc |fctThetaD (v1Marg c τ₁) τ| ≤ C_th1m 0 * c⁻¹ * τ₁ * (|τ| / τ₁) ^ 11 := by
              simpa [mul_assoc] using h1
        _ = C_th1m 0 * τ₁ ^ 5 * (|τ| / τ₁) ^ 11 := h1'
        _ ≤ C_th1m 0 * τ₁ ^ 2 * (|τ| / τ₁) ^ 11 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ52 h0n.2.2.2.2) hr11_nn
        _ = C_th1m 0 * (τ₁ ^ 2 * (|τ| / τ₁) ^ 11) := by ring
    rw [e0]
    have hM := mul_nonneg (sq_nonneg τ₁) hr11_nn
    simpa [mul_assoc] using abs_add4_le_linear hK4 hM hb0 hm0' hb1 hm1' h0n.1 h0n.2.2.2.1
  · have e1 := hiter_eq 1 τ
    simp only [iteratedDeriv_one, Nat.cast_one] at e1 hm1
    have h21 : (2 : ℤ) - 1 = 1 := by norm_num
    have h41 : (4 : ℤ) - 1 = 3 := by norm_num
    have hn11 : (-1 : ℤ) - 1 = -2 := by norm_num
    rw [h21, h41, hn11, sub_self, zpow_one, zpow_zero, mul_one] at hm1
    have hb0 : |deriv (fctThetaD (v0Base StripKernelChoice.star τ₁)) τ| ≤ C_th0b 1 * τ₁ := by
      simpa only [mul_one] using hm1.1.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg h1n.1 hτ₁.le))
    have hm0' : |deriv (fctThetaD (v0Marg τ₁)) τ| ≤ C_th0m 1 * τ₁ := by
      rw [show τ₁ ^ (3 : ℤ) = τ₁ ^ 3 by rw [show (3 : ℤ) = (3 : ℕ) by rfl, zpow_natCast]] at hm1
      have h := hm1.2.1.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg h1n.2.1 (pow_nonneg hτ₁.le 3)))
      rw [mul_one] at h; exact h.trans (mul_le_mul_of_nonneg_left hτ31 h1n.2.1)
    have hb1 : |deriv (fctThetaD (v1Base StripKernelChoice.star c τ₁)) τ| ≤ C_th1b 1 * τ₁ := by
      have hcτ2 : c⁻¹ * τ₁ ^ (-2 : ℤ) = τ₁ ^ 2 := by
        rw [hcinv, zpow_neg, show (2 : ℤ) = (2 : ℕ) by rfl, zpow_natCast,
          show τ₁ ^ 4 * (τ₁ ^ 2)⁻¹ = τ₁ ^ 2 * (τ₁ ^ 2 * (τ₁ ^ 2)⁻¹) by ring,
          mul_inv_cancel₀ (pow_ne_zero 2 hτ₁.ne'), mul_one]
      have h := hm1.2.2.2.1.trans (mul_le_mul_of_nonneg_left (min_le_left _ _)
        (mul_nonneg (mul_nonneg h1n.2.2.2.1 (inv_nonneg.mpr hc.le)) (zpow_nonneg hτ₁.le _)))
      rw [mul_one, mul_assoc (C_th1b 1) c⁻¹ _, hcτ2] at h; exact h.trans (mul_le_mul_of_nonneg_left hτ21 h1n.2.2.2.1)
    have hm1' : |deriv (fctThetaD (v1Marg c τ₁)) τ| ≤ C_th1m 1 * τ₁ := by
      have h := hm1.2.2.2.2.trans (mul_le_mul_of_nonneg_left (min_le_left _ _)
        (mul_nonneg h1n.2.2.2.2 (inv_nonneg.mpr hc.le)))
      rw [mul_one, hcinv] at h; exact h.trans (mul_le_mul_of_nonneg_left hτ41 h1n.2.2.2.2)
    rw [e1]
    exact abs_add4_le_linear hK4 hτ₁.le hb0 hm0' hb1 hm1' h1n.1 h1n.2.2.2.1
  · have e2 := hiter_eq 2 τ
    simp only [Nat.cast_ofNat, sub_self, zpow_zero, mul_one, show (11 : ℕ) - 2 = 9 by rfl] at hm2
    have hb0 : |iteratedDeriv 2 (fctThetaD (v0Base StripKernelChoice.star τ₁)) τ| ≤ C_th0b 2 * (|τ| / τ₁) ^ 9 :=
      hm2.1.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) h2n.1)
    have hm0' : |iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) τ| ≤ C_th0m 2 * (|τ| / τ₁) ^ 9 := by
      have h := hm2.2.1.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg h2n.2.1 (zpow_nonneg hτ₁.le _)))
      rw [show (4 : ℤ) - 2 = 2 by norm_num, show (2 : ℤ) = (2 : ℕ) by rfl, zpow_natCast] at h
      calc |iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) τ| ≤ C_th0m 2 * τ₁ ^ 2 * (|τ| / τ₁) ^ 9 := h
        _ ≤ C_th0m 2 * 1 * (|τ| / τ₁) ^ 9 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ2_le h2n.2.1) hr9_nn
        _ = C_th0m 2 * (|τ| / τ₁) ^ 9 := by ring
    have hb1 : |iteratedDeriv 2 (fctThetaD (v1Base StripKernelChoice.star c τ₁)) τ| ≤ C_th1b 2 * (|τ| / τ₁) ^ 9 := by
      have hcτ3 : c⁻¹ * τ₁ ^ (-3 : ℤ) = τ₁ := by
        rw [hcinv, zpow_neg, show (3 : ℤ) = (3 : ℕ) by rfl, zpow_natCast,
          show τ₁ ^ 4 * (τ₁ ^ 3)⁻¹ = τ₁ * (τ₁ ^ 3 * (τ₁ ^ 3)⁻¹) by ring,
          mul_inv_cancel₀ (pow_ne_zero 3 hτ₁.ne'), mul_one]
      have h := hm2.2.2.2.1.trans (mul_le_mul_of_nonneg_left (min_le_right _ _)
        (mul_nonneg (mul_nonneg h2n.2.2.2.1 (inv_nonneg.mpr hc.le)) (zpow_nonneg hτ₁.le _)))
      have h' : C_th1b 2 * c⁻¹ * τ₁ ^ (-1 - 2 : ℤ) * (|τ| / τ₁) ^ 9 = C_th1b 2 * τ₁ * (|τ| / τ₁) ^ 9 := by
        rw [show (-1 - 2 : ℤ) = -3 by rfl]
        calc C_th1b 2 * c⁻¹ * τ₁ ^ (-3 : ℤ) * (|τ| / τ₁) ^ 9
            = C_th1b 2 * (c⁻¹ * τ₁ ^ (-3 : ℤ)) * (|τ| / τ₁) ^ 9 := by ring
          _ = C_th1b 2 * τ₁ * (|τ| / τ₁) ^ 9 := by rw [hcτ3]
      calc |iteratedDeriv 2 (fctThetaD (v1Base StripKernelChoice.star c τ₁)) τ|
            ≤ C_th1b 2 * c⁻¹ * τ₁ ^ (-1 - 2 : ℤ) * (|τ| / τ₁) ^ 9 := by simpa [mul_assoc] using h
        _ = C_th1b 2 * τ₁ * (|τ| / τ₁) ^ 9 := h'
        _ ≤ C_th1b 2 * 1 * (|τ| / τ₁) ^ 9 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ₁_1 h2n.2.2.2.1) hr9_nn
        _ = C_th1b 2 * (|τ| / τ₁) ^ 9 := by ring
    have hm1' : |iteratedDeriv 2 (fctThetaD (v1Marg c τ₁)) τ| ≤ C_th1m 2 * (|τ| / τ₁) ^ 9 := by
      have hcτ1 : c⁻¹ * τ₁ ^ (-1 : ℤ) = τ₁ ^ 3 := by
        rw [hcinv, zpow_neg_one, show τ₁ ^ 4 * τ₁⁻¹ = τ₁ ^ 3 * (τ₁ * τ₁⁻¹) by ring,
          mul_inv_cancel₀ hτ₁.ne', mul_one]
      have h := hm2.2.2.2.2.trans (mul_le_mul_of_nonneg_left (min_le_right _ _)
        (mul_nonneg (mul_nonneg h2n.2.2.2.2 (inv_nonneg.mpr hc.le)) (zpow_nonneg hτ₁.le _)))
      have h' : C_th1m 2 * c⁻¹ * τ₁ ^ (1 - 2 : ℤ) * (|τ| / τ₁) ^ 9 = C_th1m 2 * τ₁ ^ 3 * (|τ| / τ₁) ^ 9 := by
        rw [show (1 - 2 : ℤ) = -1 by rfl]
        calc C_th1m 2 * c⁻¹ * τ₁ ^ (-1 : ℤ) * (|τ| / τ₁) ^ 9
            = C_th1m 2 * (c⁻¹ * τ₁ ^ (-1 : ℤ)) * (|τ| / τ₁) ^ 9 := by ring
          _ = C_th1m 2 * τ₁ ^ 3 * (|τ| / τ₁) ^ 9 := by rw [hcτ1]
      calc |iteratedDeriv 2 (fctThetaD (v1Marg c τ₁)) τ|
            ≤ C_th1m 2 * c⁻¹ * τ₁ ^ (1 - 2 : ℤ) * (|τ| / τ₁) ^ 9 := by simpa [mul_assoc] using h
        _ = C_th1m 2 * τ₁ ^ 3 * (|τ| / τ₁) ^ 9 := h'
        _ ≤ C_th1m 2 * 1 * (|τ| / τ₁) ^ 9 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ3_le h2n.2.2.2.2) hr9_nn
        _ = C_th1m 2 * (|τ| / τ₁) ^ 9 := by ring
    rw [e2]
    exact abs_add4_le_linear hK4 hr9_nn hb0 hm0' hb1 hm1' h2n.1 h2n.2.2.2.1
  · have hA := (hth_inA 0 τ hτ).2.2.1
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, Nat.sub_zero, abs_sq] at hA
    rw [show τ₁ ^ (2 : ℤ) = τ₁ ^ 2 by rw [show (2 : ℤ) = (2 : ℕ) by rfl, zpow_natCast]] at hA
    rw [hAe_fn τ, abs_mul, abs_of_pos (sq_pos_of_pos hτ₁)] at hA
    have hA' : τ₁ ^ 2 * |fctThetaD (vAlpha 1 τ₁) τ| ≤ τ₁ ^ 2 * (C_tha 0 * τ₁ ^ 2 * (|τ| / τ₁) ^ 11) := by
      calc τ₁ ^ 2 * |fctThetaD (vAlpha 1 τ₁) τ|
          ≤ C_tha 0 * τ₁ ^ 2 * τ₁ ^ 2 * min 1 ((|τ| / τ₁) ^ 11) := hA
        _ ≤ C_tha 0 * τ₁ ^ 2 * τ₁ ^ 2 * (|τ| / τ₁) ^ 11 :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg (mul_nonneg h0n.2.2.1 (sq_nonneg τ₁)) (sq_nonneg τ₁))
        _ = τ₁ ^ 2 * (C_tha 0 * τ₁ ^ 2 * (|τ| / τ₁) ^ 11) := by ring
    exact (le_of_mul_le_mul_left hA' (sq_pos_of_pos hτ₁)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [h0n.2.2.1]) (sq_nonneg τ₁)) hr11_nn)

set_option maxHeartbeats 400000 in
/-- Uniform compensator derivative bounds (`r = 0, 1, 2` at `α = 0` and `r = 0` for `vAlpha 1`). -/
lemma thetaD_center_bounds :
    ∃ (Cv0 Cv1 Cv2 Cα0 : ℝ), 0 ≤ Cv0 ∧ 0 ≤ Cv1 ∧ 0 ≤ Cv2 ∧ 0 ≤ Cα0 ∧
      ∀ {K4 c : ℝ}, 1 ≤ K4 → 0 < c →
        c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose →
        (∀ τ : ℝ, |τ| ≤ 12 * c ^ (-(1 / 4 : ℝ)) →
          |fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ)))) τ| ≤
            Cv0 * K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 * (|τ| / c ^ (-(1 / 4 : ℝ))) ^ 11 ∧
          |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))))) τ| ≤
            Cv1 * K4 * c ^ (-(1 / 4 : ℝ)) ∧
          |iteratedDeriv 2 (fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))))) τ| ≤
            Cv2 * K4 * (|τ| / c ^ (-(1 / 4 : ℝ))) ^ 9 ∧
          |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ| ≤
            Cα0 * (c ^ (-(1 / 4 : ℝ))) ^ 2 * (|τ| / c ^ (-(1 / 4 : ℝ))) ^ 11) ∧
        ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))))) := by
  obtain ⟨_, hτD_le, _, _, _, _, _, C_th0b, C_th0m, C_tha, C_th1b, C_th1m,
    _, _, _, _, _, _, _, _, hCth_nn, _, _, hmain⟩ := (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  have h0n := hCth_nn 0; have h1n := hCth_nn 1; have h2n := hCth_nn 2
  refine ⟨C_th0b 0 + C_th0m 0 + C_th1b 0 + C_th1m 0 + 1, C_th0b 1 + C_th0m 1 + C_th1b 1 + C_th1m 1 + 1,
    C_th0b 2 + C_th0m 2 + C_th1b 2 + C_th1m 2 + 1, C_tha 0 + 1,
    by linarith [h0n.1, h0n.2.1, h0n.2.2.2.1, h0n.2.2.2.2],
    by linarith [h1n.1, h1n.2.1, h1n.2.2.2.1, h1n.2.2.2.2],
    by linarith [h2n.1, h2n.2.1, h2n.2.2.2.1, h2n.2.2.2.2],
    by linarith [h0n.2.2.1], ?_⟩
  intro K4 c hK4 hc hτ₁_le
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc _
  have hτ₁_1 : τ₁ ≤ 1 := hτ₁_le.trans (hτD_le.trans (by norm_num))
  have hcτ : τ₁ ^ 4 * c = 1 := by rw [rpow_neg_quarter_pow4 hc, inv_mul_cancel₀ hc.ne']
  obtain ⟨hcd_v, _, _, hcs_v, _, _, _, _, hth_in, _⟩ :=
    hmain hK4 hc hτ₁ hτ₁_le hcτ (show |(0 : ℝ)| ≤ τ₁ ^ 2 by rw [abs_zero]; exact sq_nonneg τ₁)
  obtain ⟨_, _, _, _, _, _, _, _, hth_inA, _⟩ :=
    hmain hK4 hc hτ₁ hτ₁_le hcτ (show |τ₁ ^ 2| ≤ τ₁ ^ 2 by rw [abs_of_nonneg (sq_nonneg _)])
  rcases hcs_v with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hv0b_cs, hv0m_cs, hva0_cs, hv1b_cs, hv1m_cs, hv0_cs, hv1_cs, _⟩
  obtain ⟨hv_cd, hiter_eq⟩ := thetaD_center_decomp hK4 hc hτ₁ hτ₁_le hcτ hcd_v
    ⟨hv0b_cs, hv0m_cs, hva0_cs, hv1b_cs, hv1m_cs, hv0_cs, hv1_cs⟩
  exact ⟨thetaD_center_step h0n h1n h2n hK4 hc hτ₁ hτ₁_1 hcτ hiter_eq hth_in hth_inA
    (fun τ => (fctThetaD_vAlpha_eq hK4 hc hτ₁ hτ₁_le hcτ (τ₁ ^ 2) τ).1), hv_cd⟩

lemma concretePhi0_eq {K4 ε c τ L1 : ℝ} (hε : ε = 1 ∨ ε = -1) (hτ0 : 0 ≤ τ) (hτ2 : τ ^ 2 < rr) :
    concretePhiLambda K4 ε c 0 τ L1 0 =
      τ ^ 3 * fjQ fF (concreteThetaT ε) c⁻¹ (τ ^ 2) +
        ((L1 - c⁻¹ * ctTheta1 ε) - fjFcrit nfun (concreteThetaT ε) c⁻¹ (τ ^ 2)) * τ := by
  have hspec := (concreteThetaT_spec hε).1 τ
  unfold concretePhiLambda
  rw [zero_mul, zero_mul, add_zero, concretePhiPh_eq_ntil hτ0 hτ2, hspec]
  unfold fjQ fjFcrit fjH1 fF
  ring

lemma concretePhi0_hasDerivAt {K4 ε c τ L1 : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hτ0 : 0 < τ) (hτ2 : τ ^ 2 < rr) (hτ_le : τ ≤ 2) :
    HasDerivAt (fun t => concretePhiLambda K4 ε c 0 t L1 0)
      ((L1 - c⁻¹ * ctTheta1 ε) - fjFcrit nfun (concreteThetaT ε) c⁻¹ (τ ^ 2)) τ := by
  obtain ⟨-, -, -, hθd⟩ := outerTheta_deriv_sq hε
  have hmc : ContinuousOn hankelEdgeM (Ici 0) := hankelEdgeM_continuousOn
  have hP : HasDerivAt (fun x : ℝ => ∫ u in (0 : ℝ)..x, hankelEdgeM u) (hankelEdgeM τ) τ := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
    · exact (hmc.mono (by rw [uIcc_of_le hτ0.le]; exact fun x hx => hx.1)).intervalIntegrable
    · exact (hmc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi τ hτ0
    · exact (hankelEdgeM_hasDerivAt hτ0).continuousAt
  have hPh : HasDerivAt (fun t => concretePhiPh t L1) (L1 - hankelEdgeM τ) τ :=
    (((hasDerivAt_id' τ).const_mul L1).fun_sub hP).congr_deriv (by ring)
  have hTh := (hθd τ (abs_le.mpr ⟨by linarith, hτ_le⟩)).const_mul c⁻¹
  have htot := hPh.sub hTh
  have heq : (fun t => concretePhiLambda K4 ε c 0 t L1 0) = fun t => concretePhiPh t L1 - c⁻¹ * outerTheta ε t := by
    ext t; simp [concretePhiLambda]
  rw [heq]
  refine htot.congr_deriv ?_
  rw [hankelEdgeM_eq hτ0.le hτ2]
  unfold fjFcrit
  ring

/-- Helper package of chart centering data from `concretePhaseBox_exist` at `(K4, ε, c)`. -/
structure FctWarpChartData (K4 ε c : ℝ) where
  ellMin : ℝ
  S : ChartSetup (ℝ × ℝ × ℝ)
  box : FctPhaseBox (concretePhiTilde K4 ε c) (concretePhaseDom ellMin ε c) (concreteTau0 ε c S)
  L_ctr : ℝ
  z_ctr : ℝ
  C_ctr : ℝ
  h_ellMin_pos : 0 < ellMin
  h_tau_lt2 : ∀ p ∈ concretePhaseDom ellMin ε c, concreteTau0 ε c S p < 2 * c ^ (-(1 / 4 : ℝ))
  h_atil_eq : ∀ p ∈ concretePhaseDom ellMin ε c,
    fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p =
      c ^ (-(1 / 2 : ℝ)) * S.A (concreteEll1 ε c p.1, 1, p.2)
  h_dL : ∀ p ∈ concretePhaseDom ellMin ε c,
    fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p (1, 0) =
      S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2))
  h_dA : ∀ p ∈ concretePhaseDom ellMin ε c,
    fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p (0, 1) =
      c⁻¹ * fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c S p) /
        Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p)
  h_S_V_bounds : ∀ p ∈ concretePhaseDom ellMin ε c,
    100 / 95 ≤ S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2)) ∧
    S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2)) ≤ 100 / 92
  h_V_eq : ∀ p ∈ concretePhaseDom ellMin ε c,
    concreteTau0 ε c S p =
      Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p) *
        S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2))
  hz_pos : 0 < z_ctr
  hL_eq : L_ctr = z_ctr * nfun z_ctr
  hL_scale : 1 * c ^ (-(2 / 3 : ℝ)) ≤ L_ctr ∧ L_ctr ≤ 12 * c ^ (-(2 / 3 : ℝ))
  hT_ctr : |c / π ^ 2 * Real.exp L_ctr - ctDelta5 ε c| ≤ C_ctr * c⁻¹
  h_rect_sub : Ioo (L_ctr / 2) (2 * L_ctr) ×ˢ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))) ⊆
    concretePhaseDom ellMin ε c
  h_ctr_mem : L_ctr ∈ Ioo (L_ctr / 2) (2 * L_ctr)
  h_u_ctr : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L_ctr, 0) - airyZero 1| ≤
    C_ctr * c ^ (-(4 / 3 : ℝ))
  h_surj : closedBall (airyZero 1, (0 : ℝ)) (c ^ (-(7 / 6 : ℝ))) ⊆
    fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ))) (concretePhiTilde K4 ε c) (concreteTau0 ε c S) ''
      (Ioo (L_ctr / 2) (2 * L_ctr) ×ˢ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))))

/-- Uniform `uAlpha` bound on `concretePhaseDom ellMin ε c` via `S.V = τ₀ / √ã` cancellation. -/
lemma fctChart_uAlpha_bound :
    ∃ Cα : ℝ, 0 ≤ Cα ∧ ∀ {K4 ε c ellMin : ℝ} {S : ChartSetup (ℝ × ℝ × ℝ)},
      1 ≤ K4 → 100 ≤ c →
      c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose →
      (∀ p ∈ concretePhaseDom ellMin ε c, concreteTau0 ε c S p < 2 * c ^ (-(1 / 4 : ℝ))) →
      (∀ p ∈ concretePhaseDom ellMin ε c,
        fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p (0, 1) =
          c⁻¹ * fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c S p) /
            Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p)) →
      (∀ p ∈ concretePhaseDom ellMin ε c,
        100 / 95 ≤ S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2)) ∧
        S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2)) ≤ 100 / 92) →
      (∀ p ∈ concretePhaseDom ellMin ε c,
        concreteTau0 ε c S p =
          Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p) *
            S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2))) →
      (∀ p ∈ concretePhaseDom ellMin ε c,
        0 < fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p) →
      ∀ p ∈ concretePhaseDom ellMin ε c,
        |fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p (0, 1)| ≤
          Cα * c ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨_, _, _, Cα0, _, _, _, hCα0, hth_bd⟩ := thetaD_center_bounds
  refine ⟨Cα0 * (100 / 92) * 2 ^ 10, by linarith [hCα0], ?_⟩
  intro K4 ε c ellMin S hK4 hc hτD hτ_lt2 h_dA h_S_V h_V_eq h_atil_pos p hp
  have hc0 : 0 < c := by linarith
  have hτ₁ : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hτ0_2 := hτ_lt2 p hp
  have hã_pos := h_atil_pos p hp
  have hτ0_pos : 0 < concreteTau0 ε c S p := by
    rw [h_V_eq p hp]
    exact mul_pos (Real.sqrt_pos.mpr hã_pos) (by linarith [(h_S_V p hp).1])
  have hτ0_le12 : |concreteTau0 ε c S p| ≤ 12 * c ^ (-(1 / 4 : ℝ)) := by
    rw [abs_of_pos hτ0_pos]; linarith
  have hth := ((hth_bd hK4 hc0 hτD).1 _ hτ0_le12).2.2.2
  rw [abs_of_pos hτ0_pos] at hth
  have hV_le : (concreteTau0 ε c S p) / Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p) ≤ 100 / 92 := by
    rw [h_V_eq p hp, mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr hã_pos).ne']
    exact (h_S_V p hp).2
  have hrat10 : (concreteTau0 ε c S p / c ^ (-(1 / 4 : ℝ))) ^ 10 ≤ (2 : ℝ) ^ 10 :=
    pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hτ₁).mpr hτ0_2.le) 10
  have hcinv_eq : c⁻¹ * c ^ (-(1 / 4 : ℝ)) = c ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
  rw [h_dA p hp, abs_div, abs_mul, abs_of_pos (inv_pos.mpr hc0), abs_of_pos (Real.sqrt_pos.mpr hã_pos)]
  calc c⁻¹ * |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c S p)| /
        Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p)
      ≤ c⁻¹ * (Cα0 * (c ^ (-(1 / 4 : ℝ))) ^ 2 * (concreteTau0 ε c S p / c ^ (-(1 / 4 : ℝ))) ^ 11) /
          Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p) := by gcongr
    _ = Cα0 * (c⁻¹ * c ^ (-(1 / 4 : ℝ))) *
          (concreteTau0 ε c S p / Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p)) *
          (concreteTau0 ε c S p / c ^ (-(1 / 4 : ℝ))) ^ 10 := by
            field_simp [hτ₁.ne']
    _ ≤ Cα0 * c ^ (-(5 / 4 : ℝ)) * (100 / 92) * (2 : ℝ) ^ 10 := by rw [hcinv_eq]; gcongr
    _ = (Cα0 * (100 / 92) * 2 ^ 10) * c ^ (-(5 / 4 : ℝ)) := by ring

lemma one_sub_half_rpow_23 :
    ∀ {x : ℝ}, Real.pi ^ 2 / 36 ≤ x → x ≤ Real.pi ^ 2 / 10 →
      (1 / 2 : ℝ) ≤ ((3 / 2 : ℝ) * x) ^ (2 / 3 : ℝ) ∧ ((3 / 2 : ℝ) * x) ^ (2 / 3 : ℝ) ≤ 1.4 := by
  intro x hxlo hxhi
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
  have hp2_lo : (9 : ℝ) < Real.pi ^ 2 := by nlinarith
  have hp2_hi : Real.pi ^ 2 < 10 := by nlinarith
  have h32_lo : (3 / 8 : ℝ) < (3 / 2 : ℝ) * x := by linarith
  have h32_hi : (3 / 2 : ℝ) * x < 1.5 := by linarith
  have h32_pos : 0 < (3 / 2 : ℝ) * x := by positivity
  have hc3 : (((3 / 2 : ℝ) * x) ^ (2 / 3 : ℝ)) ^ 3 = ((3 / 2 : ℝ) * x) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h32_pos.le]; norm_num
  have hval_pos : 0 < ((3 / 2 : ℝ) * x) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos h32_pos _
  constructor
  · by_contra hc; push Not at hc
    have hlt := pow_lt_pow_left₀ hc hval_pos.le (by norm_num : 3 ≠ 0)
    rw [hc3] at hlt; nlinarith
  · by_contra hc; push Not at hc
    have hlt := pow_lt_pow_left₀ hc (by norm_num) (by norm_num : 3 ≠ 0)
    rw [hc3] at hlt; nlinarith

private lemma exp_sub_ge_abs_nonneg {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) :
    |L₁ - L₂| ≤ |Real.exp L₁ - Real.exp L₂| := by
  wlog hle : L₂ ≤ L₁ generalizing L₁ L₂
  · rw [abs_sub_comm L₁, abs_sub_comm (Real.exp L₁)]
    exact this hL₂ hL₁ (le_of_not_ge hle)
  rcases hle.eq_or_lt with rfl | hlt
  · simp
  · obtain ⟨ξ, hξm, hξe⟩ := exists_hasDerivAt_eq_slope Real.exp Real.exp hlt
      Real.continuous_exp.continuousOn fun w _ => Real.hasDerivAt_exp w
    have hpos : 0 < L₁ - L₂ := sub_pos.mpr hlt
    have he1 : 1 ≤ Real.exp ξ := Real.one_le_exp (by linarith [hL₂, hξm.1])
    have hfe : Real.exp L₁ - Real.exp L₂ = Real.exp ξ * (L₁ - L₂) := by rw [hξe, div_mul_cancel₀ _ hpos.ne']
    rw [abs_of_pos hpos, abs_of_pos (sub_pos.mpr (Real.exp_lt_exp.mpr hlt)), hfe]
    exact le_mul_of_one_le_left hpos.le he1

lemma l1_sub_ctr_of_exp_close {c Δ5 L₁ L₂ C₁ C₂ : ℝ} (hc : 100 ≤ c)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (h1 : |c / Real.pi ^ 2 * Real.exp L₁ - Δ5| ≤ C₁ * c⁻¹)
    (h2 : |c / Real.pi ^ 2 * Real.exp L₂ - Δ5| ≤ C₂ * c⁻¹) :
    |L₁ - L₂| ≤ Real.pi ^ 2 * (|C₁| + |C₂|) * c ^ (-(2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hexp_diff : c / Real.pi ^ 2 * |Real.exp L₁ - Real.exp L₂| ≤ (|C₁| + |C₂|) * c⁻¹ := by
    have htri : |c / Real.pi ^ 2 * Real.exp L₁ - c / Real.pi ^ 2 * Real.exp L₂| ≤ C₁ * c⁻¹ + C₂ * c⁻¹ := by
      have hsub : c / Real.pi ^ 2 * Real.exp L₁ - c / Real.pi ^ 2 * Real.exp L₂ =
          (c / Real.pi ^ 2 * Real.exp L₁ - Δ5) - (c / Real.pi ^ 2 * Real.exp L₂ - Δ5) := by ring
      rw [hsub]
      exact (abs_sub_le (c / Real.pi ^ 2 * Real.exp L₁ - Δ5) 0 (c / Real.pi ^ 2 * Real.exp L₂ - Δ5)).trans
        (by simpa only [sub_zero, zero_sub, abs_neg] using add_le_add h1 h2)
    have hmul : c / Real.pi ^ 2 * |Real.exp L₁ - Real.exp L₂| =
        |c / Real.pi ^ 2 * Real.exp L₁ - c / Real.pi ^ 2 * Real.exp L₂| := by
      conv_lhs => rw [← abs_of_pos (div_pos hc0 hpi2), ← abs_mul, mul_sub]
    rw [hmul]
    exact htri.trans (by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (add_le_add (le_abs_self C₁) (le_abs_self C₂)) (inv_nonneg.mpr hc0.le))
  have hmvt : |L₁ - L₂| ≤ |Real.exp L₁ - Real.exp L₂| := exp_sub_ge_abs_nonneg hL₁ hL₂
  have hpi_inv : (c / Real.pi ^ 2)⁻¹ = Real.pi ^ 2 * c⁻¹ := by field_simp [hpi2.ne', hc0.ne']
  have hc2 : c⁻¹ * c⁻¹ = c ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
  have hdiv : |Real.exp L₁ - Real.exp L₂| ≤ Real.pi ^ 2 * (|C₁| + |C₂|) * c ^ (-(2 : ℝ)) := by
    have h1' : |Real.exp L₁ - Real.exp L₂| ≤ (|C₁| + |C₂|) * c⁻¹ * (c / Real.pi ^ 2)⁻¹ :=
      (le_div_iff₀' (div_pos hc0 hpi2)).mpr hexp_diff
    rw [hpi_inv] at h1'
    calc |Real.exp L₁ - Real.exp L₂| ≤ (|C₁| + |C₂|) * c⁻¹ * (Real.pi ^ 2 * c⁻¹) := h1'
      _ = Real.pi ^ 2 * (|C₁| + |C₂|) * (c⁻¹ * c⁻¹) := by ring
      _ = Real.pi ^ 2 * (|C₁| + |C₂|) * c ^ (-(2 : ℝ)) := by rw [hc2]
  exact hmvt.trans hdiv

private lemma exp_lip_le_two {L₁ L₂ : ℝ} (hL₁ : L₁ ≤ 2) (hL₂ : L₂ ≤ 2) :
    |Real.exp L₁ - Real.exp L₂| ≤ Real.exp 2 * |L₁ - L₂| := by
  wlog hle : L₂ ≤ L₁ generalizing L₁ L₂
  · rw [abs_sub_comm (Real.exp L₁), abs_sub_comm L₁]
    exact this hL₂ hL₁ (le_of_not_ge hle)
  rcases hle.eq_or_lt with rfl | hlt
  · simp
  · obtain ⟨ξ, hξm, hξe⟩ := exists_hasDerivAt_eq_slope Real.exp Real.exp hlt
      Real.continuous_exp.continuousOn fun w _ => Real.hasDerivAt_exp w
    have hpos : 0 < L₁ - L₂ := sub_pos.mpr hlt
    have he2 : Real.exp ξ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith [hξm.2, hL₁])
    have hfe : Real.exp L₁ - Real.exp L₂ = Real.exp ξ * (L₁ - L₂) := by rw [hξe, div_mul_cancel₀ _ hpos.ne']
    rw [abs_of_pos (sub_pos.mpr (Real.exp_lt_exp.mpr hlt)), abs_of_pos hpos, hfe]
    exact mul_le_mul_of_nonneg_right he2 hpos.le

lemma exp_sub_ctr_of_l1_close {c Δ5 L₁ L_ctr C_ctr C_L : ℝ} (hc : 100 ≤ c)
    (hL_ctr : L_ctr ≤ 1) (hL_diff : |L₁ - L_ctr| ≤ C_L * c ^ (-(2 : ℝ)))
    (hC_L_small : C_L * c ^ (-(2 : ℝ)) ≤ 1)
    (h_ctr : |c / Real.pi ^ 2 * Real.exp L_ctr - Δ5| ≤ C_ctr * c⁻¹) :
    |c / Real.pi ^ 2 * Real.exp L₁ - Δ5| ≤ (C_ctr + Real.exp 2 / Real.pi ^ 2 * C_L) * c⁻¹ := by
  have hc0 : 0 < c := by linarith
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hexp_lip : |Real.exp L₁ - Real.exp L_ctr| ≤ Real.exp 2 * |L₁ - L_ctr| :=
    exp_lip_le_two (by linarith [abs_le.mp hL_diff]) (by linarith)
  have hcc2 : c * c ^ (-(2 : ℝ)) = c⁻¹ := by
    calc c * c ^ (-(2 : ℝ)) = c ^ (1 : ℝ) * c ^ (-(2 : ℝ)) := by rw [Real.rpow_one]
      _ = c ^ (-(1 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
      _ = c⁻¹ := Real.rpow_neg_one c
  calc |c / Real.pi ^ 2 * Real.exp L₁ - Δ5|
      = |(c / Real.pi ^ 2 * Real.exp L_ctr - Δ5) + c / Real.pi ^ 2 * (Real.exp L₁ - Real.exp L_ctr)| := by ring_nf
    _ ≤ |c / Real.pi ^ 2 * Real.exp L_ctr - Δ5| + c / Real.pi ^ 2 * |Real.exp L₁ - Real.exp L_ctr| := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul, abs_of_pos (div_pos hc0 hpi2)]
    _ ≤ C_ctr * c⁻¹ + c / Real.pi ^ 2 * (Real.exp 2 * (C_L * c ^ (-(2 : ℝ)))) := by
          gcongr
          exact hexp_lip.trans (mul_le_mul_of_nonneg_left hL_diff (Real.exp_pos _).le)
    _ = (C_ctr + Real.exp 2 / Real.pi ^ 2 * C_L) * c⁻¹ := by
          rw [show c / Real.pi ^ 2 * (Real.exp 2 * (C_L * c ^ (-(2 : ℝ)))) =
            (Real.exp 2 / Real.pi ^ 2 * C_L) * (c * c ^ (-(2 : ℝ))) by ring, hcc2]; ring

/-- Lipchitz bound for `y ↦ y^(2/3)` on `[lo, ∞)` with `lo > 0`: `|y₁^(2/3) - y₂^(2/3)| ≤ (2/3) * lo^(-1/3) * |y₁ - y₂|`. -/
lemma rpow_two_thirds_lip {lo y₁ y₂ : ℝ} (hlo : 0 < lo) (hy₁ : lo ≤ y₁) (hy₂ : lo ≤ y₂) :
    |y₁ ^ (2 / 3 : ℝ) - y₂ ^ (2 / 3 : ℝ)| ≤ (2 / 3 : ℝ) * lo ^ (-(1 / 3 : ℝ)) * |y₁ - y₂| := by
  wlog hle : y₁ ≤ y₂ generalizing y₁ y₂
  · rw [abs_sub_comm (y₁ ^ _), abs_sub_comm y₁]; exact this hy₂ hy₁ (le_of_not_ge hle)
  rcases hle.eq_or_lt with rfl | hlt
  · simp
  · have hpos : 0 < y₂ - y₁ := sub_pos.mpr hlt
    have hcont : ContinuousOn (fun y : ℝ => y ^ (2 / 3 : ℝ)) (Icc y₁ y₂) := fun y hy =>
      ((hasDerivAt_id' y).rpow_const (Or.inl (by linarith [hy.1] : y ≠ 0))).continuousAt.continuousWithinAt
    have hdiff : ∀ y ∈ Ioo y₁ y₂, HasDerivAt (fun w : ℝ => w ^ (2 / 3 : ℝ)) ((2 / 3 : ℝ) * y ^ (-(1 / 3 : ℝ))) y :=
      fun y hy => ((hasDerivAt_id' y).rpow_const (p := (2 / 3 : ℝ)) (Or.inl (by linarith [hy.1] : y ≠ 0))).congr_deriv (by
        rw [show (2 / 3 : ℝ) - 1 = -(1 / 3 : ℝ) by norm_num]; ring)
    obtain ⟨ξ, hξm, hξe⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hdiff
    have hξlo : lo ≤ ξ := by linarith [hξm.1]
    have hbd : (2 / 3 : ℝ) * ξ ^ (-(1 / 3 : ℝ)) ≤ (2 / 3 : ℝ) * lo ^ (-(1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hlo hξlo (by norm_num)) (by norm_num)
    have hfe : y₂ ^ (2 / 3 : ℝ) - y₁ ^ (2 / 3 : ℝ) = ((2 / 3 : ℝ) * ξ ^ (-(1 / 3 : ℝ))) * (y₂ - y₁) := by
      rw [hξe, div_mul_cancel₀ _ hpos.ne']
    rw [abs_sub_comm (y₁ ^ _), abs_sub_comm y₁, abs_of_pos hpos, abs_of_nonneg (sub_nonneg.mpr
      (Real.rpow_le_rpow (by linarith) hle (by norm_num))), hfe]
    exact mul_le_mul_of_nonneg_right hbd hpos.le

lemma langer_node_exp_bound {ε c φ τ_Ph L_ctr C5 CC : ℝ} {Ξ : ℝ → ℝ}
    (hc0 : 0 < c) (hφ_mem : φ ∈ Icc (-3 : ℝ) (-2))
    (hφ_err : |ctChartX c φ - ctDelta5 ε c| ≤ C5 * c⁻¹)
    (hΞ_eq : Ξ (ctMu c * φ) = Real.exp (hankelEdgeM τ_Ph) / Real.pi ^ 2)
    (hL_hm : L_ctr = hankelEdgeM τ_Ph)
    (hΞ0 : Ξ 0 = 1 / Real.pi ^ 2)
    (hΞ1 : deriv Ξ 0 * ((2 : ℝ) ^ ((2 : ℝ) / 3) * ceBeta1) = -1)
    (hΞ2 : deriv (deriv Ξ) 0 / 2 * ((2 : ℝ) ^ ((4 : ℝ) / 3) * ceBeta1 ^ 2) = 9 * Real.pi ^ 2 / 25)
    (hXi_tay : |Ξ (ctMu c * φ) - Ξ 0 - deriv Ξ 0 * (ctMu c * φ) -
      deriv (deriv Ξ) 0 / 2 * (ctMu c * φ) ^ 2| ≤ CC * |ctMu c * φ| ^ 3) :
    |c / Real.pi ^ 2 * Real.exp L_ctr - ctDelta5 ε c| ≤ (|CC| * (1.6 * 3) ^ 3 + |C5|) * c⁻¹ := by
  set a_node : ℝ := ctMu c * φ
  have h223 := two_rpow_23_bounds
  have hexp_eq : c / Real.pi ^ 2 * Real.exp L_ctr = c * Ξ a_node := by
    rw [hL_hm, hΞ_eq]; field_simp [Real.pi_pos.ne']
  have hβ_pos : 0 < hankelBeta1 := hankelBeta1_pos
  have h4_eq : (2 : ℝ) ^ (4 / 3 : ℝ) = ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hXi1_val : deriv Ξ 0 * (2 : ℝ) ^ (2 / 3 : ℝ) = -1 / hankelBeta1 := by
    have h := hΞ1; rw [show ceBeta1 = hankelBeta1 from rfl] at h
    field_simp [hβ_pos.ne'] at h ⊢; linarith
  have hXi2_val : deriv (deriv Ξ) 0 / 2 * ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 2 = 9 * Real.pi ^ 2 / (25 * hankelBeta1 ^ 2) := by
    have h := hΞ2; rw [show ceBeta1 = hankelBeta1 from rfl, h4_eq] at h
    field_simp [hβ_pos.ne'] at h ⊢; linarith
  have hk_eq : c * c ^ (-(2 / 3 : ℝ)) = c ^ (1 / 3 : ℝ) ∧ c * (c ^ (-(2 / 3 : ℝ))) ^ 2 = c ^ (-(1 / 3 : ℝ)) ∧
      c * (c ^ (-(2 / 3 : ℝ))) ^ 3 = c⁻¹ := by
    refine ⟨?_, ?_, ?_⟩
    · calc c * c ^ (-(2 / 3 : ℝ)) = c ^ (1 : ℝ) * c ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
        _ = c ^ (1 / 3 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
    · calc c * (c ^ (-(2 / 3 : ℝ))) ^ 2 = c ^ (1 : ℝ) * c ^ (-(4 / 3 : ℝ)) := by
            rw [Real.rpow_one, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hc0.le]; norm_num
        _ = c ^ (-(1 / 3 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
    · calc c * (c ^ (-(2 / 3 : ℝ))) ^ 3 = c ^ (1 : ℝ) * c ^ (-(2 : ℝ)) := by
            rw [Real.rpow_one, ← Real.rpow_natCast _ 3, ← Real.rpow_mul hc0.le]; norm_num
        _ = c ^ (-(1 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
        _ = c⁻¹ := Real.rpow_neg_one c
  have hchart_match : c * (Ξ 0 + deriv Ξ 0 * a_node + deriv (deriv Ξ) 0 / 2 * a_node ^ 2) = ctChartX c φ := by
    have ha_eq : a_node = (2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * φ := rfl
    rw [ha_eq, hΞ0]
    calc c * (1 / Real.pi ^ 2 + deriv Ξ 0 * ((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * φ) +
          deriv (deriv Ξ) 0 / 2 * ((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * φ) ^ 2)
        = c / Real.pi ^ 2 + (deriv Ξ 0 * (2 : ℝ) ^ (2 / 3 : ℝ)) * φ * (c * c ^ (-(2 / 3 : ℝ))) +
            (deriv (deriv Ξ) 0 / 2 * ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 2) * φ ^ 2 * (c * (c ^ (-(2 / 3 : ℝ))) ^ 2) := by ring
      _ = c / Real.pi ^ 2 - φ * c ^ (1 / 3 : ℝ) / hankelBeta1 +
            9 * Real.pi ^ 2 / 25 * (φ / hankelBeta1) ^ 2 * c ^ (-(1 / 3 : ℝ)) := by
          rw [hXi1_val, hXi2_val, hk_eq.1, hk_eq.2.1]; ring
      _ = ctChartX c φ := rfl
  have hc_mul : |c * Ξ a_node - ctChartX c φ| ≤ |CC| * (1.6 * 3) ^ 3 * c⁻¹ := by
    have hsub : c * Ξ a_node - ctChartX c φ =
        c * (Ξ a_node - Ξ 0 - deriv Ξ 0 * a_node - deriv (deriv Ξ) 0 / 2 * a_node ^ 2) := by
      rw [← hchart_match]; ring
    rw [hsub, abs_mul, abs_of_pos hc0]
    have ha3 : |a_node| ^ 3 ≤ (1.6 * 3) ^ 3 * (c ^ (-(2 / 3 : ℝ))) ^ 3 := by
      have h1 : |a_node| ≤ 1.6 * 3 * c ^ (-(2 / 3 : ℝ)) := by
        unfold a_node ctMu
        rw [abs_mul, abs_mul, abs_of_pos (by positivity), abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
        have hφabs : |φ| ≤ 3 := abs_le.mpr ⟨hφ_mem.1, by linarith [hφ_mem.2]⟩
        calc (2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * |φ| = ((2 : ℝ) ^ (2 / 3 : ℝ) * |φ|) * c ^ (-(2 / 3 : ℝ)) := by ring
          _ ≤ (1.6 * 3) * c ^ (-(2 / 3 : ℝ)) := by gcongr; exact h223.2
      calc |a_node| ^ 3 ≤ (1.6 * 3 * c ^ (-(2 / 3 : ℝ))) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1 3
        _ = (1.6 * 3) ^ 3 * (c ^ (-(2 / 3 : ℝ))) ^ 3 := by ring
    calc c * |Ξ a_node - Ξ 0 - deriv Ξ 0 * a_node - deriv (deriv Ξ) 0 / 2 * a_node ^ 2|
        ≤ c * (CC * |a_node| ^ 3) := mul_le_mul_of_nonneg_left hXi_tay hc0.le
      _ ≤ c * (|CC| * ((1.6 * 3) ^ 3 * (c ^ (-(2 / 3 : ℝ))) ^ 3)) := by gcongr; exact le_abs_self _
      _ = |CC| * (1.6 * 3) ^ 3 * c⁻¹ := by rw [← hk_eq.2.2]; ring
  rw [hexp_eq]
  calc |c * Ξ a_node - ctDelta5 ε c|
      ≤ |c * Ξ a_node - ctChartX c φ| + |ctChartX c φ - ctDelta5 ε c| := abs_sub_le _ (ctChartX c φ) _
    _ ≤ |CC| * (1.6 * 3) ^ 3 * c⁻¹ + C5 * c⁻¹ := add_le_add hc_mul hφ_err
    _ ≤ (|CC| * (1.6 * 3) ^ 3 + |C5|) * c⁻¹ := by
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right (add_le_add le_rfl (le_abs_self _)) (inv_nonneg.mpr hc0.le)

lemma center_rect_sub_phaseDom {ellMin ε c L_ctr : ℝ} (hc0 : 0 < c) (hL_lo : 1 * c ^ (-(2 / 3 : ℝ)) ≤ L_ctr)
    (hL_hi : L_ctr ≤ 12 * c ^ (-(2 / 3 : ℝ)))
    (hell_bd : (ellMin + |ctTheta1 ε| + 1) * c ^ (-(1 / 3 : ℝ)) < 0.05)
    (h255_bd : 24 * c ^ (-(1 / 6 : ℝ)) + |ctTheta1 ε| * c ^ (-(1 / 2 : ℝ)) < 2.55) :
    Ioo (L_ctr / 2) (2 * L_ctr) ×ˢ Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))) ⊆
      concretePhaseDom ellMin ε c := by
  rintro ⟨L1, α⟩ ⟨⟨hL1_lo, hL1_hi⟩, ⟨hα_lo, hα_hi⟩⟩
  have hτ₁_sq : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := rpow_neg_quarter_sq hc0
  have hc_13_23 : c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c⁻¹ := by
    rw [← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]
  have hL1_gt : (ellMin + |ctTheta1 ε| + 1) * c⁻¹ < L1 := by
    have h1 : (ellMin + |ctTheta1 ε| + 1) * c⁻¹ < 0.05 * c ^ (-(2 / 3 : ℝ)) := by
      rw [← hc_13_23, ← mul_assoc]; exact mul_lt_mul_of_pos_right hell_bd (Real.rpow_pos_of_pos hc0 _)
    linarith [Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
  have h_low : ellMin * c ^ (-(1 / 2 : ℝ)) < concreteEll1 ε c L1 := by
    unfold concreteEll1
    rw [hτ₁_sq, lt_div_iff₀ (Real.rpow_pos_of_pos hc0 _),
      show ellMin * c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = ellMin * c⁻¹ by
        rw [mul_assoc, ← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]]
    have hct : ctTheta1 ε / c ≤ |ctTheta1 ε| * c⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (inv_nonneg.mpr hc0.le)
    linarith [inv_pos.mpr hc0, hL1_gt, hct]
  have h_high : concreteEll1 ε c L1 < 2.55 := by
    unfold concreteEll1
    rw [hτ₁_sq, div_lt_iff₀ (Real.rpow_pos_of_pos hc0 _), sub_lt_iff_lt_add]
    have h1 : L1 < 24 * c ^ (-(2 / 3 : ℝ)) := by linarith
    have h2 : -(|ctTheta1 ε| * c⁻¹) ≤ ctTheta1 ε / c := by
      rw [div_eq_mul_inv, ← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le _) (inv_nonneg.mpr hc0.le)
    have h3 : 24 * c ^ (-(2 / 3 : ℝ)) + |ctTheta1 ε| * c⁻¹ < 2.55 * c ^ (-(1 / 2 : ℝ)) := by
      have hmul := mul_lt_mul_of_pos_right h255_bd (Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ)))
      have ha : c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      have hb : c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c⁻¹ := by
        rw [← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]
      rw [add_mul, mul_assoc, ha, mul_assoc, hb] at hmul; exact hmul
    linarith
  have hα_abs : |α| < 2 * c ^ (-(1 / 2 : ℝ)) := by
    have : |α| < 3 / 2 * c ^ (-(1 / 2 : ℝ)) := abs_lt.mpr ⟨hα_lo, hα_hi⟩
    linarith [Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))]
  exact ⟨h_low, h_high, hα_abs⟩

lemma max_at_crit_of_antitone {f f' : ℝ → ℝ} {lo ctr hi x : ℝ}
    (hd : ∀ t ∈ Icc lo hi, HasDerivAt f (f' t) t) (hanti : AntitoneOn f' (Icc lo hi))
    (hcrit : f' ctr = 0) (hctr : ctr ∈ Icc lo hi) (hx : x ∈ Icc lo hi) : f x ≤ f ctr := by
  rcases le_total x ctr with hle | hle
  · have hm : MonotoneOn f (Icc lo ctr) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun t ht => (hd t ⟨ht.1, ht.2.trans hctr.2⟩).continuousAt.continuousWithinAt)
        (fun t ht => (hd t ⟨(interior_subset ht).1, (interior_subset ht).2.trans hctr.2⟩).differentiableAt.differentiableWithinAt)
        fun t ht => by
          have ht' := interior_subset ht
          rw [(hd t ⟨ht'.1, ht'.2.trans hctr.2⟩).deriv, ← hcrit]
          exact hanti ⟨ht'.1, ht'.2.trans hctr.2⟩ hctr ht'.2
    exact hm ⟨hx.1, hle⟩ ⟨hctr.1, le_rfl⟩ hle
  · have ha : AntitoneOn f (Icc ctr hi) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        (fun t ht => (hd t ⟨hctr.1.trans ht.1, ht.2⟩).continuousAt.continuousWithinAt)
        (fun t ht => (hd t ⟨hctr.1.trans (interior_subset ht).1, (interior_subset ht).2⟩).differentiableAt.differentiableWithinAt)
        fun t ht => by
          have ht' := interior_subset ht
          rw [(hd t ⟨hctr.1.trans ht'.1, ht'.2⟩).deriv, ← hcrit]
          exact hanti hctr ⟨hctr.1.trans ht'.1, ht'.2⟩ ht'.1
    exact ha ⟨le_rfl, hctr.2⟩ ⟨hle, hx.2⟩ hle

lemma fctAtil_alpha_mvt {Φ : ℝ → ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} {τ0 : ℝ × ℝ → ℝ}
    (hPB : FctPhaseBox Φ Ω τ0) {L rJ M : ℝ} (_hM : 0 ≤ M) (hrJ : 0 < rJ)
    (hsub : ∀ t ∈ Ioo (-rJ) rJ, (L, t) ∈ Ω)
    (hbd : ∀ t ∈ Ioo (-rJ) rJ, |fderiv ℝ (fctAtil Φ τ0) (L, t) (0, 1)| ≤ M)
    {α : ℝ} (hα : α ∈ Ioo (-rJ) rJ) :
    |fctAtil Φ τ0 (L, α) - fctAtil Φ τ0 (L, 0)| ≤ M * |α| := by
  have hcont : ContinuousOn (fun t => fctAtil Φ τ0 (L, t)) (Icc (min 0 α) (max 0 α)) := fun t ht =>
    (((hPB.atil_contDiffAt (hsub t ⟨lt_of_lt_of_le (lt_min (neg_lt_zero.mpr hrJ) hα.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hrJ hα.2)⟩)).differentiableAt (by simp)).continuousAt.comp
      ((continuous_const.prodMk continuous_id).continuousAt)).continuousWithinAt
  have hdiff : ∀ t ∈ Ioo (min 0 α) (max 0 α),
      HasDerivAt (fun s => fctAtil Φ τ0 (L, s)) (fderiv ℝ (fctAtil Φ τ0) (L, t) (0, 1)) t := fun t ht => by
    have htJ : t ∈ Ioo (-rJ) rJ := ⟨lt_of_lt_of_le (lt_min (neg_lt_zero.mpr hrJ) hα.1) ht.1.le,
      lt_of_le_of_lt ht.2.le (max_lt hrJ hα.2)⟩
    exact (((hPB.atil_contDiffAt (hsub t htJ)).differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_const t L).prodMk (hasDerivAt_id t))
  rcases le_total 0 α with hα0 | hα0
  · rcases hα0.eq_or_lt with rfl | hlt
    · simp
    · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hcont hdiff
      obtain ⟨ξ, hξm, hξe⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hdiff
      have hfe : fctAtil Φ τ0 (L, α) - fctAtil Φ τ0 (L, 0) = fderiv ℝ (fctAtil Φ τ0) (L, ξ) (0, 1) * α := by
        rw [hξe, sub_zero, div_mul_cancel₀ _ hlt.ne']
      rw [hfe, abs_mul, abs_of_pos hlt]
      exact mul_le_mul_of_nonneg_right (hbd ξ ⟨lt_trans (neg_lt_zero.mpr hrJ) hξm.1, lt_trans hξm.2 hα.2⟩) hlt.le
  · rcases hα0.eq_or_lt with h0 | hlt
    · subst h0; simp
    · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hcont hdiff
      obtain ⟨ξ, hξm, hξe⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hdiff
      have hpos : 0 < -α := neg_pos.mpr hlt
      have hfe : fctAtil Φ τ0 (L, 0) - fctAtil Φ τ0 (L, α) = fderiv ℝ (fctAtil Φ τ0) (L, ξ) (0, 1) * (-α) := by
        rw [hξe, zero_sub, div_mul_cancel₀ _ hpos.ne']
      rw [abs_sub_comm, hfe, abs_mul, abs_of_pos hpos, (abs_of_neg hlt).symm]
      exact mul_le_mul_of_nonneg_right (hbd ξ ⟨lt_trans hα.1 hξm.1, lt_trans hξm.2 hrJ⟩) (abs_nonneg α)

lemma fctAtil_L_mvt_ge {Φ : ℝ → ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} {τ0 : ℝ × ℝ → ℝ}
    (hPB : FctPhaseBox Φ Ω τ0) {α L₁ L₂ mV : ℝ} (hle : L₁ ≤ L₂)
    (hsub : ∀ L ∈ Icc L₁ L₂, (L, α) ∈ Ω)
    (hbd : ∀ L ∈ Ioo L₁ L₂, mV ≤ fderiv ℝ (fctAtil Φ τ0) (L, α) (1, 0)) :
    mV * (L₂ - L₁) ≤ fctAtil Φ τ0 (L₂, α) - fctAtil Φ τ0 (L₁, α) := by
  rcases hle.eq_or_lt with rfl | hlt
  · simp
  · have hcont : ContinuousOn (fun L => fctAtil Φ τ0 (L, α)) (Icc L₁ L₂) := fun L hL =>
      (((hPB.atil_contDiffAt (hsub L hL)).differentiableAt (by simp)).continuousAt.comp_of_eq
        ((continuous_id.prodMk continuous_const).continuousAt (x := L)) rfl).continuousWithinAt
    have hdiff : ∀ L ∈ Ioo L₁ L₂, HasDerivAt (fun s => fctAtil Φ τ0 (s, α)) (fderiv ℝ (fctAtil Φ τ0) (L, α) (1, 0)) L :=
      fun L hL => by
        change HasDerivAt (fctAtil Φ τ0 ∘ fun s : ℝ => (s, α)) _ L
        exact (((hPB.atil_contDiffAt (hsub L (Ioo_subset_Icc_self hL))).differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt L
          ((hasDerivAt_id' L).prodMk (hasDerivAt_const L α))
    obtain ⟨ξ, hξm, hξe⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hdiff
    have hpos : 0 < L₂ - L₁ := sub_pos.mpr hlt
    rw [show fctAtil Φ τ0 (L₂, α) - fctAtil Φ τ0 (L₁, α) = fderiv ℝ (fctAtil Φ τ0) (ξ, α) (1, 0) * (L₂ - L₁) by
      rw [hξe, div_mul_cancel₀ _ hpos.ne']]
    exact mul_le_mul_of_nonneg_right (hbd ξ hξm) hpos.le

lemma fctWarp_S_V_bounds {ε c ellMin : ℝ} {S : ChartSetup (ℝ × ℝ × ℝ)}
    (hc0 : 0 < c) (hellMin_nn : 0 ≤ ellMin) (hSΩ : S.Ω = OmT (c ^ (-(1 / 4 : ℝ))))
    {p : ℝ × ℝ} (hp : p ∈ concretePhaseDom ellMin ε c) :
    100 / 95 ≤ S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2)) ∧
    S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2)) ≤ 100 / 92 := by
  have hq : (concreteEll1 ε c p.1, (1 : ℝ), p.2) ∈ S.Ω := by
    rw [hSΩ]; exact concreteEll1_mem_OmT hc0 hellMin_nn hp
  have hAm : S.A (concreteEll1 ε c p.1, (1 : ℝ), p.2) ∈ Yint := S.A_mem hq
  have hZm : S.Z ((concreteEll1 ε c p.1, (1 : ℝ), p.2), S.A (concreteEll1 ε c p.1, (1 : ℝ), p.2)) ∈ Ioo (-1 : ℝ) 6 :=
    S.Z_mem ⟨hq, hAm⟩
  have hDb := S.D_bounds (q := ((concreteEll1 ε c p.1, (1 : ℝ), p.2),
    S.Z ((concreteEll1 ε c p.1, (1 : ℝ), p.2), S.A (concreteEll1 ε c p.1, (1 : ℝ), p.2)))) ⟨hq, hZm⟩
  simp only [ChartSetup.V, inv_eq_one_div]
  constructor <;> [rw [le_div_iff₀ (by linarith)]; rw [div_le_iff₀ (by linarith)]] <;> linarith

lemma fctWarp_V_eq {K4 ε c ellMin : ℝ} {S : ChartSetup (ℝ × ℝ × ℝ)}
    (hc0 : 0 < c) (hellMin_nn : 0 ≤ ellMin) (hSΩ : S.Ω = OmT (c ^ (-(1 / 4 : ℝ))))
    {p : ℝ × ℝ} (hp : p ∈ concretePhaseDom ellMin ε c)
    (hA_pos : 0 < S.A (concreteEll1 ε c p.1, 1, p.2))
    (hã_eq : fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p =
      c ^ (-(1 / 2 : ℝ)) * S.A (concreteEll1 ε c p.1, 1, p.2)) :
    concreteTau0 ε c S p = Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p) *
      S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2)) := by
  have hq : (concreteEll1 ε c p.1, (1 : ℝ), p.2) ∈ S.Ω := by
    rw [hSΩ]; exact concreteEll1_mem_OmT hc0 hellMin_nn hp
  have hAm : S.A (concreteEll1 ε c p.1, (1 : ℝ), p.2) ∈ Yint := S.A_mem hq
  have hV_pos : 0 < S.V ((concreteEll1 ε c p.1, 1, p.2), S.A (concreteEll1 ε c p.1, 1, p.2)) := by
    linarith [(fctWarp_S_V_bounds hc0 hellMin_nn hSΩ hp).1]
  have hVe := S.V_eq (y := ((concreteEll1 ε c p.1, (1 : ℝ), p.2), S.A (concreteEll1 ε c p.1, (1 : ℝ), p.2))) ⟨hq, hAm⟩
  rw [hã_eq]
  unfold concreteTau0
  rw [← hVe, Real.sqrt_mul hA_pos.le, Real.sqrt_sq hV_pos.le, Real.sqrt_mul (Real.rpow_nonneg hc0.le _)]
  have hsqτ : Real.sqrt (c ^ (-(1 / 2 : ℝ))) = c ^ (-(1 / 4 : ℝ)) := by
    rw [← rpow_neg_quarter_sq hc0, Real.sqrt_sq (Real.rpow_nonneg hc0.le _)]
  rw [hsqτ]; ring

end FormalResearch.SignUncertainty
