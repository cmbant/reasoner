/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasHarmonics
public import FormalResearch.SignUncertainty.CtFejer

/-!
# Exact-phase `ct:boas` assembly (`boas_sharp_proved`)

`CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:boas`, Steps 3–5:
assembles the exact-phase Boas lower bound
`∫_{L ≥ ctLv0 c} ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L) ≥ -C * c ^ (-(4/3))`
from:
1. Far field (`boas_far_field_hankel` + `eventually_farEps_le`): `-O(c^{-2})`.
2. Upper tail above `nearB c - 1` (`one_sub_boasSf_tail_le`): `O(c^{-20})`.
3. Lower truncation below `ctLv0 c` (`boas_field_trunc_lo`): `O(c^{-29/21})`.
4. Mollification difference (`exists_near_weights`): `O(c^{-4/3})`.
5. Smooth block Fejér decomposition (`fejer_identity`) on `nearWeight`:
   - `h ≥ 0` on `supp (nearWeight)` because `Lt ≤ ctLv0 c / 3` (`ct_boas_moments_top` +
     `ctLv0_facts`) and `hankelHL_nonneg_of_tail`, so the Fejér square term `k ≥ 0` is `≥ 0`;
   - `k = 1` term is `-O(c^{-2})` since `∑_j nearWeight j ≤ 2`;
   - harmonics `2 ≤ k ≤ ⌈c²⌉` give `-O(N * c² * c^{-14})` via `boas_harmonic_bound`.

Proves `boas_sharp_proved`, matching `CtBoasSharpStatement c₁` without importing
`CtLowerLogFreeSkeleton`.

Class: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.SignUncertainty.CtBoasWindow
open FormalResearch.SignUncertainty.CtFejer

private lemma fejerS_abs_le (n : ℕ) (θ : ℝ) : |fejerS n θ| ≤ (n : ℝ) ^ 2 := by
  rw [abs_of_nonneg (fejerS_nonneg n θ)]
  exact fejerS_le n θ

private lemma fejerS_continuous (n : ℕ) : Continuous (fejerS n) := by
  have hfun : fejerS n = fun θ => 2 * ∑ k ∈ Finset.range n, ((n : ℝ) - k) * Real.cos (k * θ) - n :=
    funext (fejerS_expand n)
  rw [hfun]
  have hsum : Continuous fun θ : ℝ => ∑ k ∈ Finset.range n, ((n : ℝ) - k) * Real.cos (k * θ) := by
    fun_prop
  exact (continuous_const.mul hsum).sub continuous_const

private lemma one_sub_sFar_mono_bound {c Lmin : ℝ} (hc : 1 < c) (hc_e2 : Real.exp 2 ≤ c)
    (_hLB : Lmin ≤ nearB c - 1) {L : ℝ} (_hL : L ∈ Ici Lmin) (hnot : nearB c - 1 < L) :
    |(1 - sFar c (c * (Real.exp L / π ^ 2))) * (1 - nearCut c L)| ≤ c ^ (-20 : ℝ) := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hsf := one_sub_boasSf_tail_le hc_e2 hnot.le
  have hcu := nearCut_bounds c L
  have h01 : 0 ≤ 1 - nearCut c L ∧ 1 - nearCut c L ≤ 1 := ⟨by linarith, by linarith⟩
  have h20 : Real.exp (-20 * Real.log c) = c ^ (-20 : ℝ) := by
    rw [show -20 * Real.log c = Real.log c * (-20) by ring, ← Real.rpow_def_of_pos hc0]
  rw [abs_of_nonneg (mul_nonneg hsf.1 h01.1)]
  calc (1 - sFar c (c * (Real.exp L / π ^ 2))) * (1 - nearCut c L)
      ≤ Real.exp (-20 * Real.log c) * 1 := mul_le_mul hsf.2 h01.2 h01.1 (Real.exp_pos _).le
    _ = c ^ (-20 : ℝ) := by rw [mul_one, h20]

private lemma near_block_fejer_lower
    {c ε R T : ℝ} {f : ℝ → ℝ} (hc1 : 1 < c) (hf : IsHankelFeasible c ε T f)
    {C_har : ℝ} (hChar0 : 0 ≤ C_har)
    {N : ℕ} (hN_le_har : ∀ j ∈ Finset.range N, ∀ k : ℕ, 2 ≤ k → k ≤ Nat.ceil (c ^ 2) →
      |∫ L : ℝ, nearWeight ε c R j L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))| ≤
        C_har * hankelMass c f * c ^ (-(14 : ℝ)))
    (hcd : ∀ j ∈ Finset.range N, ∀ n : ℕ, ContDiff ℝ n (nearWeight ε c R j))
    (hbdd : ∀ j ∈ Finset.range N, ∀ L, 0 ≤ nearWeight ε c R j L ∧ nearWeight ε c R j L ≤ 1)
    (hsupp_lo : ∀ j ∈ Finset.range N, ∀ L ≤ ctLv0 c / 3, nearWeight ε c R j L = 0)
    (hsum_om : ∀ L, ∑ j ∈ Finset.range N, nearOmega ε c R j L =
      ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) * nearCut c L)
    (hdiff_le : ∀ L, ∑ j ∈ Finset.range N, |nearWeight ε c R j L - nearOmega ε c R j L| ≤ c ^ (-(4 / 3 : ℝ)))
    (hw_bd : ∀ L, 0 ≤ ctTaper ε c R L ∧ ctTaper ε c R L ≤ 1)
    (hmass : hankelMass c f = 1) (hLt_le : ∀ L, ctLv0 c / 3 < L → T ≤ c * (Real.exp L / π ^ 2)) :
    -(4 * c ^ (-(2 : ℝ)) + 2 * (N : ℝ) * (Nat.ceil (c ^ 2) : ℝ) * C_har * c ^ (-(14 : ℝ))) ≤
      ∑ j ∈ Finset.range N, ∫ L : ℝ, nearWeight ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
  have hc0 : 0 < c := zero_lt_one.trans hc1
  have hf' := hf.toIsHankelEigenfn
  have hh := integrable_hankelHL hc0 hf'
  have hXm : Measurable (boasX c ε) := measurable_boasX c ε
  set NF : ℕ := Nat.ceil (c ^ 2)
  have hNF2 : 2 ≤ NF := by
    have h1 : (1 : ℝ) < c ^ 2 := by nlinarith only [hc1]
    have h2 : (1 : ℝ) < (NF : ℝ) := lt_of_lt_of_le h1 (Nat.le_ceil _)
    exact_mod_cast h2
  have hNF_pos : (0 : ℝ) < (NF : ℝ) := by positivity
  have hNF_ge_c2 : c ^ 2 ≤ (NF : ℝ) := Nat.le_ceil _
  have hc_pos_r2 : (0 : ℝ) < c ^ 2 := by positivity
  have hblock : ∀ j ∈ Finset.range N,
      -(2 / (NF : ℝ) * (∫ L : ℝ, nearWeight ε c R j L * |hankelHL c f L|) +
        2 * (NF : ℝ) * (C_har * c ^ (-(14 : ℝ)))) ≤
        ∫ L : ℝ, nearWeight ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
    intro j hj
    set wj : ℝ → ℝ := nearWeight ε c R j
    have hwj_cont : Continuous wj := (hcd j hj 0).continuous
    have hwj_m : Measurable wj := hwj_cont.measurable
    have hwj_bd := hbdd j hj
    have hnonneg_wh : ∀ L : ℝ, 0 ≤ wj L * hankelHL c f L := by
      intro L
      rcases le_or_gt L (ctLv0 c / 3) with hle | hgt
      · simp [wj, hsupp_lo j hj L hle]
      · exact mul_nonneg (hwj_bd L).1 (hankelHL_nonneg_of_tail hc0 hf (hLt_le L hgt))
    have hwj_h_eq : ∀ L : ℝ, wj L * hankelHL c f L = wj L * |hankelHL c f L| := fun L => by
      rcases le_or_gt L (ctLv0 c / 3) with hle | hgt
      · simp [wj, hsupp_lo j hj L hle]
      · rw [abs_of_nonneg (hankelHL_nonneg_of_tail hc0 hf (hLt_le L hgt))]
    set g1 : ℝ → ℝ := fun L => wj L * hankelHL c f L * (fejerS NF (boasX c ε L + π / 2) / (NF : ℝ))
    set g2 : ℝ → ℝ := fun L => (2 / (NF : ℝ)) * (wj L * hankelHL c f L * Real.cos (boasX c ε L + π / 2))
    set hk : ℕ → ℝ → ℝ := fun k L =>
      (1 - (k : ℝ) / (NF : ℝ)) * (wj L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2)))
    have hint_g1 : Integrable g1 := by
      refine (hh.abs.const_mul (NF : ℝ)).mono'
        ((hwj_m.aestronglyMeasurable.mul hh.aestronglyMeasurable).mul
          (((fejerS_continuous NF).measurable.comp (hXm.add measurable_const)).div_const _).aestronglyMeasurable)
        (ae_of_all _ fun L => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hwj_bd L).1]
      have hfbd : |fejerS NF (boasX c ε L + π / 2) / (NF : ℝ)| ≤ (NF : ℝ) := by
        rw [abs_div, abs_of_pos hNF_pos, div_le_iff₀ hNF_pos, ← sq]
        exact fejerS_abs_le NF _
      calc wj L * |hankelHL c f L| * |fejerS NF (boasX c ε L + π / 2) / (NF : ℝ)|
          ≤ 1 * |hankelHL c f L| * (NF : ℝ) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hwj_bd L).2 (abs_nonneg _)) hfbd (abs_nonneg _) (by positivity)
        _ = (NF : ℝ) * |hankelHL c f L| := by ring
    have hint_g2 : Integrable g2 := by
      refine (hh.abs.const_mul (2 / (NF : ℝ))).mono'
        (aestronglyMeasurable_const.mul
          ((hwj_m.aestronglyMeasurable.mul hh.aestronglyMeasurable).mul
            (Real.measurable_cos.comp (hXm.add measurable_const)).aestronglyMeasurable))
        (ae_of_all _ fun L => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / (NF : ℝ)),
        abs_mul, abs_mul, abs_of_nonneg (hwj_bd L).1]
      have h1 : wj L * |hankelHL c f L| * |Real.cos (boasX c ε L + π / 2)| ≤ 1 * |hankelHL c f L| * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hwj_bd L).2 (abs_nonneg _))
          (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
      calc 2 / (NF : ℝ) * (wj L * |hankelHL c f L| * |Real.cos (boasX c ε L + π / 2)|)
          ≤ 2 / (NF : ℝ) * (1 * |hankelHL c f L| * 1) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 / (NF : ℝ) * |hankelHL c f L| := by ring
    have hint_k_raw : ∀ k : ℕ, Integrable fun L =>
        wj L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2)) := fun k => by
      refine hh.abs.mono'
        ((hwj_m.aestronglyMeasurable.mul hh.aestronglyMeasurable).mul
          (Real.measurable_cos.comp (measurable_const.mul (hXm.add measurable_const))).aestronglyMeasurable)
        (ae_of_all _ fun L => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hwj_bd L).1]
      calc wj L * |hankelHL c f L| * |Real.cos ((k : ℝ) * (boasX c ε L + π / 2))|
          ≤ 1 * |hankelHL c f L| * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hwj_bd L).2 (abs_nonneg _))
              (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
        _ = |hankelHL c f L| := by ring
    have hint_hk : ∀ k : ℕ, Integrable (hk k) := fun k => (hint_k_raw k).const_mul _
    have hsplit_eq : (fun L => wj L * (hankelHL c f L * boasKernel (boasX c ε) L)) =
        fun L => g1 L + g2 L - 2 * ∑ k ∈ Finset.Ico 2 NF, hk k L := by
      ext L
      have hbk : boasKernel (boasX c ε) L = 1 + 2 * Real.cos (boasX c ε L + π / 2) := by
        unfold boasKernel
        rw [Real.cos_add_pi_div_two]
        ring
      rw [hbk, fejer_identity hNF2 (boasX c ε L + π / 2)]
      simp only [g1, g2, hk]
      have hsub0 : wj L * (hankelHL c f L * (fejerS NF (boasX c ε L + π / 2) / (NF : ℝ) +
            (2 / (NF : ℝ)) * Real.cos (boasX c ε L + π / 2) - 2 * ∑ k ∈ Finset.Ico 2 NF,
              (1 - (k : ℝ) / (NF : ℝ)) * Real.cos ((k : ℝ) * (boasX c ε L + π / 2)))) =
          wj L * hankelHL c f L * (fejerS NF (boasX c ε L + π / 2) / (NF : ℝ) +
            (2 / (NF : ℝ)) * Real.cos (boasX c ε L + π / 2)) -
          wj L * hankelHL c f L * (2 * ∑ k ∈ Finset.Ico 2 NF,
            (1 - (k : ℝ) / (NF : ℝ)) * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))) := by ring
      have hsub1 : wj L * hankelHL c f L * (fejerS NF (boasX c ε L + π / 2) / (NF : ℝ) +
            (2 / (NF : ℝ)) * Real.cos (boasX c ε L + π / 2)) =
          wj L * hankelHL c f L * (fejerS NF (boasX c ε L + π / 2) / (NF : ℝ)) +
            (2 / (NF : ℝ)) * (wj L * hankelHL c f L * Real.cos (boasX c ε L + π / 2)) := by ring
      have hsub2 : wj L * hankelHL c f L * (2 * ∑ k ∈ Finset.Ico 2 NF,
            (1 - (k : ℝ) / (NF : ℝ)) * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))) =
          2 * ∑ k ∈ Finset.Ico 2 NF,
            (1 - (k : ℝ) / (NF : ℝ)) * (wj L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))) := by
        rw [← mul_assoc, mul_comm (wj L * hankelHL c f L) 2, mul_assoc, Finset.mul_sum]
        exact congrArg (2 * ·) (Finset.sum_congr rfl fun k _ => by ring)
      rw [hsub0, hsub1, hsub2]
    have hint_g12 : Integrable fun L => g1 L + g2 L := hint_g1.add hint_g2
    have hint_k2 : Integrable fun L => 2 * ∑ k ∈ Finset.Ico 2 NF, hk k L :=
      (integrable_finsetSum _ fun k _ => hint_hk k).const_mul 2
    rw [hsplit_eq, integral_sub hint_g12 hint_k2, integral_add hint_g1 hint_g2, integral_const_mul 2,
      integral_finsetSum _ fun k _ => hint_hk k]
    have hg1_nn : 0 ≤ ∫ L, g1 L := integral_nonneg fun L =>
      mul_nonneg (hnonneg_wh L) (div_nonneg (fejerS_nonneg NF _) hNF_pos.le)
    have hg2_bd : -(2 / (NF : ℝ) * ∫ L : ℝ, wj L * |hankelHL c f L|) ≤ ∫ L, g2 L := by
      have hint_abs : Integrable fun L => wj L * |hankelHL c f L| :=
        hh.abs.mono' (hwj_m.aestronglyMeasurable.mul hh.abs.aestronglyMeasurable)
          (ae_of_all _ fun L => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwj_bd L).1, abs_abs]
            exact mul_le_of_le_one_left (abs_nonneg _) (hwj_bd L).2)
      have hpt : ∀ L, -(2 / (NF : ℝ) * (wj L * |hankelHL c f L|)) ≤ g2 L := fun L => by
        dsimp only [g2]
        rw [← hwj_h_eq L]
        have h1 : -(wj L * hankelHL c f L) ≤ wj L * hankelHL c f L * Real.cos (boasX c ε L + π / 2) := by
          have hc_lb := Real.neg_one_le_cos (boasX c ε L + π / 2)
          nlinarith only [hnonneg_wh L, hc_lb]
        have h2 : (0 : ℝ) ≤ 2 / (NF : ℝ) := by positivity
        nlinarith only [mul_le_mul_of_nonneg_left h1 h2]
      have hint_neg : Integrable fun L => -(2 / (NF : ℝ) * (wj L * |hankelHL c f L|)) :=
        (hint_abs.const_mul (2 / (NF : ℝ))).neg
      have hm := integral_mono hint_neg hint_g2 hpt
      rw [integral_neg, integral_const_mul] at hm
      exact hm
    have hk_sum_bd : ∑ k ∈ Finset.Ico 2 NF, ∫ L, hk k L ≤ (NF : ℝ) * (C_har * c ^ (-(14 : ℝ))) := by
      have hle1 : ∀ k ∈ Finset.Ico 2 NF, ∫ L, hk k L ≤ C_har * c ^ (-(14 : ℝ)) := fun k hk_mem => by
        obtain ⟨hk2, hk_lt⟩ := Finset.mem_Ico.1 hk_mem
        have hk_bd := hN_le_har j hj k hk2 hk_lt.le
        rw [hmass, mul_one] at hk_bd
        have hfac : |1 - (k : ℝ) / (NF : ℝ)| ≤ 1 := by
          rw [abs_le]
          have h1 : (0 : ℝ) ≤ (k : ℝ) / (NF : ℝ) := by positivity
          have h2 : (k : ℝ) / (NF : ℝ) ≤ 1 := (div_le_one hNF_pos).2 (by exact_mod_cast hk_lt.le)
          constructor <;> linarith
        calc ∫ L, hk k L
            = (1 - (k : ℝ) / (NF : ℝ)) *
                ∫ L : ℝ, wj L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2)) := by
                  simp only [hk, integral_const_mul]
          _ ≤ |1 - (k : ℝ) / (NF : ℝ)| *
                |∫ L : ℝ, wj L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))| :=
                  le_trans (le_abs_self _) (by rw [abs_mul])
          _ ≤ 1 * (C_har * c ^ (-(14 : ℝ))) :=
                mul_le_mul hfac hk_bd (abs_nonneg _) zero_le_one
          _ = C_har * c ^ (-(14 : ℝ)) := one_mul _
      calc ∑ k ∈ Finset.Ico 2 NF, ∫ L, hk k L
          ≤ ∑ _k ∈ Finset.Ico 2 NF, C_har * c ^ (-(14 : ℝ)) := Finset.sum_le_sum hle1
        _ = ((Finset.Ico 2 NF).card : ℝ) * (C_har * c ^ (-(14 : ℝ))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (NF : ℝ) * (C_har * c ^ (-(14 : ℝ))) := by
              have hcard : ((Finset.Ico 2 NF).card : ℝ) ≤ (NF : ℝ) := by
                rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le NF 2
              exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hChar0 (Real.rpow_nonneg hc0.le _))
    linarith only [hg1_nn, hg2_bd, hk_sum_bd]
  have hsum_bd : ∑ j ∈ Finset.range N,
        -(2 / (NF : ℝ) * (∫ L : ℝ, nearWeight ε c R j L * |hankelHL c f L|) +
          2 * (NF : ℝ) * (C_har * c ^ (-(14 : ℝ)))) ≤
      ∑ j ∈ Finset.range N, ∫ L : ℝ, nearWeight ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) :=
    Finset.sum_le_sum hblock
  have hint_abs_j : ∀ j ∈ Finset.range N, Integrable fun L => nearWeight ε c R j L * |hankelHL c f L| :=
    fun j hj => hh.abs.mono'
      (((hcd j hj 0).continuous.measurable).aestronglyMeasurable.mul hh.abs.aestronglyMeasurable)
      (ae_of_all _ fun L => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hbdd j hj L).1, abs_abs]
        exact mul_le_of_le_one_left (abs_nonneg _) (hbdd j hj L).2)
  have hsum_wt_le : ∀ L : ℝ, ∑ j ∈ Finset.range N, nearWeight ε c R j L ≤ 2 := fun L => by
    have hsf := (⟨sFar_nonneg hc1 (c * (Real.exp L / π ^ 2)), sFar_le_one hc1 (c * (Real.exp L / π ^ 2))⟩ :
      0 ≤ sFar c (c * (Real.exp L / π ^ 2)) ∧ sFar c (c * (Real.exp L / π ^ 2)) ≤ 1)
    have hcu := nearCut_bounds c L
    have h1 : ∑ j ∈ Finset.range N, nearOmega ε c R j L ≤ 1 := by
      rw [hsum_om L]
      have h01 : 0 ≤ ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) :=
        mul_nonneg (hw_bd L).1 (by linarith only [hsf.2])
      have hle1 : ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) ≤ 1 := by
        nlinarith only [hw_bd L, hsf]
      nlinarith only [h01, hle1, hcu]
    have h2 : ∑ j ∈ Finset.range N, nearWeight ε c R j L ≤
        (∑ j ∈ Finset.range N, nearOmega ε c R j L) +
          ∑ j ∈ Finset.range N, |nearWeight ε c R j L - nearOmega ε c R j L| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => by linarith [le_abs_self (nearWeight ε c R j L - nearOmega ε c R j L)]
    have hc43_le1 : c ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hc1.le (by norm_num)
    linarith only [h1, h2, hdiff_le L, hc43_le1]
  have hsum_k1_int : ∑ j ∈ Finset.range N, ∫ L : ℝ, nearWeight ε c R j L * |hankelHL c f L| ≤ 2 := by
    rw [← integral_finsetSum _ fun j hj => hint_abs_j j hj]
    have hint_sum_mul : Integrable fun L => (∑ j ∈ Finset.range N, nearWeight ε c R j L) * |hankelHL c f L| :=
      (integrable_finsetSum _ fun j hj => hint_abs_j j hj).congr
        (ae_of_all _ fun L => by dsimp only; exact (Finset.sum_mul _ _ _).symm)
    calc ∫ L : ℝ, ∑ j ∈ Finset.range N, nearWeight ε c R j L * |hankelHL c f L|
        = ∫ L : ℝ, (∑ j ∈ Finset.range N, nearWeight ε c R j L) * |hankelHL c f L| :=
          integral_congr_ae (ae_of_all _ fun L => (Finset.sum_mul _ _ _).symm)
      _ ≤ ∫ L : ℝ, 2 * |hankelHL c f L| :=
          integral_mono hint_sum_mul (hh.abs.const_mul 2) fun L =>
            mul_le_mul_of_nonneg_right (hsum_wt_le L) (abs_nonneg _)
      _ = 2 := by rw [integral_const_mul, integral_abs_hankelHL hc0 hf', hmass, mul_one]
  have hcm2 : 2 / (NF : ℝ) * 2 ≤ 4 * c ^ (-(2 : ℝ)) := by
    have h1 : c ^ (-(2 : ℝ)) = (c ^ 2)⁻¹ := by
      rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h2 : (NF : ℝ)⁻¹ ≤ (c ^ 2)⁻¹ := inv_anti₀ hc_pos_r2 hNF_ge_c2
    rw [h1, div_eq_mul_inv]
    linarith only [h2]
  have hlhs : -(4 * c ^ (-(2 : ℝ)) + 2 * (N : ℝ) * (NF : ℝ) * C_har * c ^ (-(14 : ℝ))) ≤
      ∑ j ∈ Finset.range N, -(2 / (NF : ℝ) * (∫ L : ℝ, nearWeight ε c R j L * |hankelHL c f L|) +
        2 * (NF : ℝ) * (C_har * c ^ (-(14 : ℝ)))) := by
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have h_k1 : 2 / (NF : ℝ) * ∑ j ∈ Finset.range N, ∫ L : ℝ, nearWeight ε c R j L * |hankelHL c f L| ≤
        4 * c ^ (-(2 : ℝ)) := by
      calc 2 / (NF : ℝ) * ∑ j ∈ Finset.range N, ∫ L : ℝ, nearWeight ε c R j L * |hankelHL c f L|
          ≤ 2 / (NF : ℝ) * 2 := mul_le_mul_of_nonneg_left hsum_k1_int (by positivity)
        _ ≤ 4 * c ^ (-(2 : ℝ)) := hcm2
    linarith only [h_k1]
  exact hlhs.trans hsum_bd

/-- **Log-free `ct:boas` (`constant_terms_lower.tex`)**:
for small `c₁ > 0` and large `c ≥ c₀`, at every good radius `R ∈ [c₁² c^{2/3}, 4 c₁² c^{2/3}]`,
`-C c^{-4/3} ≤ ∫_{L ≥ ctLv0 c} ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L)`.
Proved cleanly from `boas_harmonic_bound`, `exists_near_weights`, `boas_far_field_hankel`,
`boas_field_trunc_lo`, `fejer_identity`, `hankelHL_nonneg_of_tail`, and `ct_boas_moments_top`. -/
theorem boas_sharp_proved :
    ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ →
      ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
          T < c * hankelXi c (airyZero 1) → 0 < ctGap ε c T →
          ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
            ctGoodRadius R →
            -(C * c ^ (-(4 / 3) : ℝ)) ≤
              ∫ L in Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
  obtain ⟨Cθ1, hCθ1⟩ := ct_outer_theta_asymp
  set Cθ : ℝ := max Cθ1 0
  obtain ⟨K, cM, hK0, hmom⟩ := ct_boas_moments_top
  obtain ⟨κ_L, hκL_pos, cL, hcL1, hLv0⟩ := ctLv0_facts
  obtain ⟨γ₁, hγ₁, hband₁⟩ := taperBand_regime (ε := 1) (Or.inl rfl)
  obtain ⟨γ₂, hγ₂, hband₂⟩ := taperBand_regime (ε := -1) (Or.inr rfl)
  obtain ⟨c₁₀_w, hc₁₀_w, hnw⟩ := exists_near_weights
  obtain ⟨c₁₀_h, hc₁₀_h, hharm⟩ := boas_harmonic_bound
  refine ⟨min (min (min γ₁ γ₂) (1 / 200)) (min c₁₀_w c₁₀_h),
    lt_min (lt_min (lt_min hγ₁ hγ₂) (by norm_num)) (lt_min hc₁₀_w hc₁₀_h),
    fun c₁ hc₁ hc₁_le => ?_⟩
  have hc₁_g1 : c₁ ≤ γ₁ := ((hc₁_le.trans (min_le_left _ _)).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hc₁_g2 : c₁ ≤ γ₂ := ((hc₁_le.trans (min_le_left _ _)).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hc₁_200 : c₁ ≤ 1 / 200 := (hc₁_le.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hc₁_w : c₁ ≤ c₁₀_w := (hc₁_le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hc₁_h : c₁ ≤ c₁₀_h := (hc₁_le.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨cB₁, hcB₁, hB₁⟩ := hband₁ c₁ hc₁ hc₁_g1
  obtain ⟨cB₂, hcB₂, hB₂⟩ := hband₂ c₁ hc₁ hc₁_g2
  obtain ⟨c_w, κ_min, hcw_e2, hκmin_pos, C_m, hCm0, hblocks⟩ := hnw c₁ hc₁ hc₁_w
  obtain ⟨c_h, C_har, hch_e2, hChar0, hharm_c₁⟩ := hharm c₁ hc₁ hc₁_h
  have hev_Lt : ∀ᶠ c : ℝ in atTop, 3 / (0.998 * langerScale c) ≤ (2 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)) := by
    have hκ := langerKappa_pos
    have hpow := ev_rpow_ge (by norm_num : (0 : ℝ) < 12 / 21) (3 / (0.998 * langerKappa) / ((2 / 5 : ℝ) * κ_L))
    filter_upwards [hpow, eventually_gt_atTop (0 : ℝ)] with c hc_p hc0
    have hK := langerScale_pos hc0
    have hmul : c ^ (-(2 / 21 : ℝ)) * c ^ (2 / 3 : ℝ) = c ^ (12 / 21 : ℝ) := by
      rw [← Real.rpow_add hc0]; norm_num
    rw [div_le_iff₀ (by positivity)] at hc_p ⊢
    calc (3 : ℝ) ≤ (0.998 * langerKappa) * ((2 / 5 : ℝ) * κ_L * c ^ (12 / 21 : ℝ)) := by
          rw [div_le_iff₀ (by positivity)] at hc_p; nlinarith only [hc_p]
      _ = (2 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)) * (0.998 * langerScale c) := by
          unfold langerScale; rw [← hmul]; ring
  have hev_har : ∀ᶠ c : ℝ in atTop,
      2 * (250 * Real.log (16 / ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)))) + 200 * nearB c + 810) *
        (2 * c ^ 2) * C_har * c ^ (-(14 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
    let A_N : ℝ := |250 * Real.log (80 / (6 * κ_L))| + 2260
    have hpow := ev_rpow_ge (by norm_num : (0 : ℝ) < 29 / 3) (4 * A_N * C_har)
    filter_upwards [eventually_ge_atTop (Real.exp 7), hpow] with c hce7 hp
    have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 7) hce7
    have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (7 : ℝ)]) hce7
    have hc7 : 7 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hce7
    have hlog_le_c : Real.log c ≤ c := (Real.log_le_sub_one_of_pos hc0).trans (by linarith)
    have h16_le : 16 / ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ))) ≤ (80 / (6 * κ_L)) * c := by
      have h1 : (c ^ (-(2 / 21 : ℝ)))⁻¹ = c ^ (2 / 21 : ℝ) := by
        rw [← Real.rpow_neg hc0.le, neg_neg]
      have h2 : c ^ (2 / 21 : ℝ) ≤ c :=
        (Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num : (2 / 21 : ℝ) ≤ 1)).trans_eq (Real.rpow_one c)
      calc 16 / ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)))
          = (80 / (6 * κ_L)) * (c ^ (-(2 / 21 : ℝ)))⁻¹ := by field_simp [hκL_pos.ne']; norm_num
        _ = (80 / (6 * κ_L)) * c ^ (2 / 21 : ℝ) := by rw [h1]
        _ ≤ (80 / (6 * κ_L)) * c := mul_le_mul_of_nonneg_left h2 (by positivity)
    have hlog16 : Real.log (16 / ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)))) ≤
        Real.log (80 / (6 * κ_L)) + Real.log c := by
      refine (Real.log_le_log (by positivity) h16_le).trans_eq ?_
      rw [Real.log_mul (by positivity) hc0.ne']
    have hnearB_le : nearB c ≤ 5 + Real.log c := by
      unfold nearB
      have hpi2 : π ^ 2 ≤ 16 := by nlinarith only [Real.pi_lt_four, Real.pi_pos]
      have h1 : π ^ 2 * Real.log c ≤ 16 * c :=
        mul_le_mul hpi2 hlog_le_c (Real.log_nonneg hc1.le) (by norm_num)
      have h2 : Real.log (π ^ 2 * Real.log c) ≤ Real.log 16 + Real.log c := by
        refine (Real.log_le_log (by positivity) h1).trans_eq ?_
        rw [Real.log_mul (by norm_num) hc0.ne']
      have h3 : Real.log 16 ≤ 3 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have : Real.exp 1 ^ 3 = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
        calc (16 : ℝ) ≤ 2.7 ^ 3 := by norm_num
          _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 3
          _ = Real.exp 3 := this
      linarith only [h2, h3]
    have hC_N : 250 * Real.log (16 / ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)))) + 200 * nearB c + 810 ≤ A_N * c := by
      have h1 : (|250 * Real.log (80 / (6 * κ_L))| + 1810) * 1 ≤
          (|250 * Real.log (80 / (6 * κ_L))| + 1810) * c :=
        mul_le_mul_of_nonneg_left hc1.le (by positivity)
      dsimp only [A_N]
      linarith only [hlog16, hnearB_le, le_abs_self (250 * Real.log (80 / (6 * κ_L))), h1, hlog_le_c]
    have hexp_11 : c * c ^ 2 * c ^ (-(14 : ℝ)) = c ^ (-(11 : ℝ)) := by
      have h1 : c * c ^ 2 = c ^ (3 : ℝ) := by
        calc c * c ^ 2 = c ^ (3 : ℕ) := by ring
          _ = c ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast c 3).symm
          _ = c ^ (3 : ℝ) := by norm_num
      rw [h1, ← Real.rpow_add hc0]; norm_num
    have hexp_29 : c ^ (-(11 : ℝ)) * c ^ (29 / 3 : ℝ) = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    have h4C : 4 * A_N * C_har * c ^ (-(11 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
      calc 4 * A_N * C_har * c ^ (-(11 : ℝ)) ≤ c ^ (29 / 3 : ℝ) * c ^ (-(11 : ℝ)) :=
            mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hc0.le _)
        _ = c ^ (-(11 : ℝ)) * c ^ (29 / 3 : ℝ) := mul_comm _ _
        _ = c ^ (-(4 / 3 : ℝ)) := hexp_29
    calc 2 * (250 * Real.log (16 / ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)))) + 200 * nearB c + 810) *
          (2 * c ^ 2) * C_har * c ^ (-(14 : ℝ))
        ≤ 2 * (A_N * c) * (2 * c ^ 2) * C_har * c ^ (-(14 : ℝ)) := by gcongr
      _ = 4 * A_N * C_har * (c * c ^ 2 * c ^ (-(14 : ℝ))) := by ring
      _ = 4 * A_N * C_har * c ^ (-(11 : ℝ)) := by rw [hexp_11]
      _ ≤ c ^ (-(4 / 3 : ℝ)) := h4C
  have hev : ∀ᶠ c : ℝ in atTop,
      cM ≤ c ∧ cL ≤ c ∧ cB₁ ≤ c ∧ cB₂ ≤ c ∧ c_w ≤ c ∧ c_h ≤ c ∧ Real.exp 7 ≤ c ∧
      (2 ≤ c ^ (4 / 7 : ℝ) ∧ c ^ (4 / 7 : ℝ) + 1 / 2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧
      boasFarEps c ⌈c ^ 2⌉₊ (boasPhaseEps c Cθ) ≤ 60 * c ^ (-(2 : ℝ)) ∧
      3 / (0.998 * langerScale c) ≤ (2 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)) ∧
      2 * (250 * Real.log (16 / ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)))) + 200 * nearB c + 810) *
        (2 * c ^ 2) * C_har * c ^ (-(14 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
    filter_upwards [eventually_ge_atTop cM, eventually_ge_atTop cL, eventually_ge_atTop cB₁,
      eventually_ge_atTop cB₂, eventually_ge_atTop c_w, eventually_ge_atTop c_h,
      eventually_ge_atTop (Real.exp 7), ev_hcR hc₁, eventually_farEps_le Cθ, hev_Lt, hev_har] with
      c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hev
  refine ⟨60 + 3 * (2 ^ 12 * (K + 1) / c₁ ^ 24) + 11, c₀, ?_⟩
  intro c hc ε hε T f hf hmass hT _hgap R hR _hgood
  obtain ⟨hcM, hcL, hcB₁, hcB₂, hcw, hch, hc7, ⟨hc47, hcR⟩, hfar_eps, hLt_cmp, hhar_cmp⟩ := hc₀ c hc
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 7) hc7
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (7 : ℝ)]) hc7
  have hc3 : 3 ≤ c := le_trans (by linarith [Real.add_one_le_exp (7 : ℝ)]) hc7
  have hc_e2 : Real.exp 2 ≤ c := le_trans (Real.exp_le_exp.2 (by norm_num)) hc7
  have hlog7 : 7 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hc7
  have hlog2 : 2 ≤ Real.log c := by linarith only [hlog7]
  have hB : TaperBand ε c R := by
    rcases hε with rfl | rfl
    · exact hB₁ c hcB₁ R hR.1 hR.2
    · exact hB₂ c hcB₂ R hR.1 hR.2
  have hI := hB.inputs
  have hf' := hf.toIsHankelEigenfn
  have hh := integrable_hankelHL hc0 hf'
  have hmass1 : ∫ L, |hankelHL c f L| = 1 := by rw [integral_abs_hankelHL hc0 hf', hmass]
  have hw_m : Measurable (ctTaper ε c R) := measurable_ctTaper hI
  have hw_bd : ∀ L, 0 ≤ ctTaper ε c R L ∧ ctTaper ε c R L ≤ 1 := fun L => hI.reg.mem L
  have hsf_m : Measurable (boasSf c) := measurable_sFar_comp hc1
  have hsf_eq : ∀ L, boasSf c L = sFar c (c * (Real.exp L / π ^ 2)) := fun _ => rfl
  have hsf_bd : ∀ L, 0 ≤ boasSf c L ∧ boasSf c L ≤ 1 := fun L => ⟨sFar_nonneg hc1 _, sFar_le_one hc1 _⟩
  have hXm : Measurable (boasX c ε) := measurable_boasX c ε
  have hKm : Measurable (boasKernel (boasX c ε)) := measurable_boasKernel hXm
  have hKb := abs_boasKernel_le (boasX c ε)
  -- Moments + Lmin
  obtain ⟨LJ, Lt, hLJ0, hLJe, hLJv, -, hLt0, hLtLJ, hLte, hLtv, hLT, hTπ, hMom, -⟩ :=
    hmom c ε T f hcM hf hε hmass hT
  obtain ⟨hL0, hLe, hLv, hLκ⟩ := hLv0 c hcL
  set Lmin : ℝ := ctLv0 c
  have hRhi : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    have h23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have : 4 * c₁ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith only [hc₁, hc₁_200]
    nlinarith only [hR.2, h23, this]
  obtain ⟨hΛJ, -⟩ := boas_geometry hc0 hB hLJ0.le hLJe hLJv hRhi
  have hLΛ : Lmin ≤ ctTaperLam ε c R := lmin_le_lam hc0 hB hL0.le hLe hLv (hcR.trans hR.1)
  have hLJ : Lmin ≤ LJ := hLΛ.trans hΛJ
  -- 1. Far field
  have hCθ : ∀ τ : ℝ, 1 ≤ τ → |CtOuter.outerTheta ε τ + (3 + ε) * π / 4| ≤
      Cθ * ((1 + τ ^ 2) * Real.exp (-π * τ)) := fun τ hτ =>
    (hCθ1 ε hε.symm τ hτ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hT_le_c : T ≤ c := by
    have hπ2 : 9 < π ^ 2 := by nlinarith only [Real.pi_gt_three]
    by_contra hlt; rw [not_le] at hlt
    have : 9 * c < T * π ^ 2 := by nlinarith only [hlt, hπ2, hc0]
    linarith only [this, hTπ, hc0]
  have hT_far : T ≤ farD c / 2 := by
    unfold farD
    nlinarith only [hT_le_c, hlog7, hc0]
  have hLmin_far : c * (Real.exp Lmin / π ^ 2) ≤ farD c / 2 := by
    have hpi2 : 9 < π ^ 2 := by nlinarith only [Real.pi_gt_three]
    have h1 : Real.exp Lmin ≤ π ^ 2 := by linarith only [hLe, hpi2]
    have h2 : Real.exp Lmin / π ^ 2 ≤ 1 := (div_le_one (by positivity)).2 h1
    unfold farD
    nlinarith only [h2, hlog7, hc0]
  have hNF2 : 2 ≤ ⌈c ^ 2⌉₊ := by
    have h1 : (2 : ℝ) ≤ c ^ 2 := by nlinarith only [hc3]
    have h2 : (2 : ℝ) ≤ (⌈c ^ 2⌉₊ : ℝ) := h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  have hfarI := boas_far_field_hankel (wt := ctTaper ε c R) (sf := boasSf c) (Lmin := Lmin)
    hc1 hlog2 hε.symm hCθ hf hmass hT_far hNF2 hw_m hsf_m hw_bd hsf_eq (ctTaper_hwt1 hc1 hI)
    hLmin_far hXm
  have hcm2_le_43 : c ^ (-(2 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
  have hfar_43 : -(60 * c ^ (-(4 / 3 : ℝ))) ≤
      ∫ L in Ici Lmin, ctTaper ε c R L * boasSf c L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
    have h1 : -60 * c ^ (-(2 : ℝ)) ≤ -(boasFarEps c ⌈c ^ 2⌉₊ (boasPhaseEps c Cθ)) := by linarith only [hfar_eps]
    have h2 : -(60 * c ^ (-(4 / 3 : ℝ))) ≤ -60 * c ^ (-(2 : ℝ)) := by nlinarith only [hcm2_le_43]
    linarith only [hfarI, h1, h2]
  -- 2 & 3. Near-field cutoff vs `Ici Lmin`
  obtain ⟨hLB, hN_le, hsum_om, hdiff_le, hblock⟩ := hblocks hε hcw hR.1 hR.2
  have htlo := boas_field_trunc_lo (sf := boasSf c) hsf_bd hc3 hB hc₁ hR.1 hh hmass1
    hL0 hLe hLv hLΛ hLJ hLJe hK0 hMom
  have hc29_le_43 : c ^ (-(29 / 21 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
  have hc20_le_43 : c ^ (-20 : ℝ) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
  have hcut_m : Measurable (nearCut c) := by
    unfold nearCut
    exact ((contDiff_smoothStep (ctLv0 c / 2) (ctLv0 c)).continuous.measurable).mul
      (measurable_const.sub ((contDiff_smoothStep (nearB c - 1) (nearB c)).continuous.measurable))
  set Om : ℝ → ℝ := fun L => ctTaper ε c R L * (1 - boasSf c L)
  have hOm_m : Measurable Om := hw_m.mul (measurable_const.sub hsf_m)
  have hOm0 : ∀ L, 0 ≤ Om L := fun L => mul_nonneg (hw_bd L).1 (by linarith only [(hsf_bd L).2])
  have hOm1 : ∀ L, Om L ≤ 1 := fun L => by
    have h1 := hw_bd L; have h2 := hsf_bd L
    dsimp only [Om]; nlinarith only [h1, h2]
  have hnear_diff :
      -(3 * (2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(4 / 3 : ℝ))) + 3 * c ^ (-(4 / 3 : ℝ))) ≤
        (∫ L in Ici Lmin, Om L * (hankelHL c f L * boasKernel (boasX c ε) L)) -
          ∫ L : ℝ, Om L * nearCut c L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
    have hi_Ici : Integrable ((Ici Lmin).indicator fun L => Om L * (hankelHL c f L * boasKernel (boasX c ε) L)) :=
      (integrable_wmul hh hKm hKb hOm_m fun L => by rw [abs_of_nonneg (hOm0 L)]; exact hOm1 L).indicator
        measurableSet_Ici
    have hi_cut : Integrable fun L => Om L * nearCut c L * (hankelHL c f L * boasKernel (boasX c ε) L) :=
      integrable_wmul hh hKm hKb (hOm_m.mul hcut_m) fun L => by
        have hcu := nearCut_bounds c L
        rw [abs_of_nonneg (mul_nonneg (hOm0 L) hcu.1)]
        nlinarith only [hOm0 L, hOm1 L, hcu]
    have hi_lo : Integrable ((Iio Lmin).indicator fun L => 3 * (Om L * |hankelHL c f L|)) := by
      have hi1 : Integrable fun L => Om L * |hankelHL c f L| :=
        integrable_wmul hh.abs measurable_const (fun _ => by rw [abs_one]; norm_num) hOm_m
          (fun L => by rw [abs_of_nonneg (hOm0 L)]; exact hOm1 L) |>.congr (ae_of_all _ fun L => by simp)
      exact (hi1.const_mul 3).indicator measurableSet_Iio
    have hi_tail : Integrable (fun L => 3 * c ^ (-20 : ℝ) * |hankelHL c f L|) :=
      hh.abs.const_mul _
    have hpt_bd : ∀ L : ℝ,
        -((Iio Lmin).indicator (fun L => 3 * (Om L * |hankelHL c f L|)) L + 3 * c ^ (-20 : ℝ) * |hankelHL c f L|) ≤
          (Ici Lmin).indicator (fun L => Om L * (hankelHL c f L * boasKernel (boasX c ε) L)) L -
            Om L * nearCut c L * (hankelHL c f L * boasKernel (boasX c ε) L) := fun L => by
      have hcu := nearCut_bounds c L
      have hK3 : |hankelHL c f L * boasKernel (boasX c ε) L| ≤ 3 * |hankelHL c f L| := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hKb L) (abs_nonneg (hankelHL c f L))).trans_eq (mul_comm _ 3)
      have htail_nn : 0 ≤ 3 * c ^ (-20 : ℝ) * |hankelHL c f L| :=
        mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hc0.le _)) (abs_nonneg _)
      rcases lt_or_ge L Lmin with hlt | hge
      · have e1 : (Ici Lmin).indicator (fun L => Om L * (hankelHL c f L * boasKernel (boasX c ε) L)) L = 0 :=
          Set.indicator_of_notMem (by simpa using hlt) _
        have e2 : (Iio Lmin).indicator (fun L => 3 * (Om L * |hankelHL c f L|)) L = 3 * (Om L * |hankelHL c f L|) :=
          Set.indicator_of_mem hlt _
        rw [e1, e2]
        have h3 : |Om L * nearCut c L * (hankelHL c f L * boasKernel (boasX c ε) L)| ≤ 3 * (Om L * |hankelHL c f L|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (hOm0 L), abs_of_nonneg hcu.1]
          calc Om L * nearCut c L * |hankelHL c f L * boasKernel (boasX c ε) L|
              ≤ Om L * 1 * (3 * |hankelHL c f L|) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hcu.2 (hOm0 L)) hK3 (abs_nonneg _)
                  (mul_nonneg (hOm0 L) zero_le_one)
            _ = 3 * (Om L * |hankelHL c f L|) := by ring
        have h4 := (abs_le.1 h3).2
        linarith only [h4, htail_nn]
      · have e1 : (Ici Lmin).indicator (fun L => Om L * (hankelHL c f L * boasKernel (boasX c ε) L)) L =
            Om L * (hankelHL c f L * boasKernel (boasX c ε) L) := Set.indicator_of_mem hge _
        have e2 : (Iio Lmin).indicator (fun L => 3 * (Om L * |hankelHL c f L|)) L = 0 :=
          Set.indicator_of_notMem (by simpa using hge) _
        rw [e1, e2, zero_add]
        rcases le_or_gt L (nearB c - 1) with hleB | hgtB
        · rw [nearCut_eq_one_of_mem hL0 hLB ⟨hge, hleB⟩, mul_one, sub_self]
          linarith only [htail_nn]
        · have hsub_tail := one_sub_sFar_mono_bound hc1 hc_e2 hLB hge hgtB
          have hwt01 := hw_bd L
          have hdiff_abs : |Om L * (hankelHL c f L * boasKernel (boasX c ε) L) -
              Om L * nearCut c L * (hankelHL c f L * boasKernel (boasX c ε) L)| ≤
              3 * c ^ (-20 : ℝ) * |hankelHL c f L| := by
            have hrew : Om L * (hankelHL c f L * boasKernel (boasX c ε) L) -
                Om L * nearCut c L * (hankelHL c f L * boasKernel (boasX c ε) L) =
                ctTaper ε c R L * ((1 - sFar c (c * (Real.exp L / π ^ 2))) * (1 - nearCut c L)) *
                  (hankelHL c f L * boasKernel (boasX c ε) L) := by
              dsimp only [Om, boasSf]; ring
            rw [hrew, abs_mul, abs_mul, abs_of_nonneg hwt01.1]
            calc ctTaper ε c R L * |(1 - sFar c (c * (Real.exp L / π ^ 2))) * (1 - nearCut c L)| *
                  |hankelHL c f L * boasKernel (boasX c ε) L|
                ≤ (1 * c ^ (-20 : ℝ)) * (3 * |hankelHL c f L|) :=
                  mul_le_mul (mul_le_mul hwt01.2 hsub_tail (abs_nonneg _) zero_le_one) hK3
                    (abs_nonneg _) (by positivity)
              _ = 3 * c ^ (-20 : ℝ) * |hankelHL c f L| := by ring
          exact neg_le_of_abs_le hdiff_abs
    have hi_lhs : Integrable fun L : ℝ =>
        -((Iio Lmin).indicator (fun L => 3 * (Om L * |hankelHL c f L|)) L + 3 * c ^ (-20 : ℝ) * |hankelHL c f L|) :=
      (hi_lo.add hi_tail).neg
    have hi_rhs : Integrable fun L : ℝ =>
        (Ici Lmin).indicator (fun L => Om L * (hankelHL c f L * boasKernel (boasX c ε) L)) L -
          Om L * nearCut c L * (hankelHL c f L * boasKernel (boasX c ε) L) :=
      hi_Ici.sub hi_cut
    have hmono := integral_mono hi_lhs hi_rhs hpt_bd
    rw [integral_neg, integral_add hi_lo hi_tail, integral_indicator measurableSet_Iio,
      integral_sub hi_Ici hi_cut] at hmono
    rw [integral_indicator measurableSet_Ici,
      integral_const_mul (3 * c ^ (-20 : ℝ)), hmass1, mul_one,
      show ∫ L in Iio Lmin, 3 * (Om L * |hankelHL c f L|) =
        3 * ∫ L in Iio Lmin, ctTaper ε c R L * (1 - boasSf c L) * |hankelHL c f L| by
          rw [integral_const_mul]] at hmono
    have hlo_43 : 3 * ∫ L in Iio Lmin, ctTaper ε c R L * (1 - boasSf c L) * |hankelHL c f L| ≤
        3 * (2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(4 / 3 : ℝ))) := by
      have hconst0 : 0 ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 := by positivity
      calc 3 * ∫ L in Iio Lmin, ctTaper ε c R L * (1 - boasSf c L) * |hankelHL c f L|
          ≤ 3 * (2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21 : ℝ))) :=
            mul_le_mul_of_nonneg_left htlo (by norm_num)
        _ ≤ 3 * (2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(4 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc29_le_43 hconst0) (by norm_num)
    have htail_43 : 3 * c ^ (-20 : ℝ) ≤ 3 * c ^ (-(4 / 3 : ℝ)) := by nlinarith only [hc20_le_43]
    linarith only [hmono, hlo_43, htail_43]
  -- 4. Mollification diff
  set N : ℕ := partCount (ctLv0 c / 4) (nearB c)
  have hnw_int : ∀ j ∈ Finset.range N,
      Integrable fun L => nearWeight ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) := fun j hj => by
    have hcdj := (hblock j hj).2.2.2.2.2.2.1
    have hbdj := (hblock j hj).2.2.2.2.2.2.2.1
    exact integrable_wmul hh hKm hKb (hcdj 0).continuous.measurable
      fun L => by rw [abs_of_nonneg (hbdj L).1]; exact (hbdj L).2
  have hom_m : ∀ j ∈ Finset.range N, Measurable (nearOmega ε c R j) := fun j _ => by
    unfold nearOmega partChi
    have hchi_m : Measurable (fun L => smoothStep (partGrid (ctLv0 c / 4) j) (partGrid (ctLv0 c / 4) (j + 1)) L -
        smoothStep (partGrid (ctLv0 c / 4) (j + 1)) (partGrid (ctLv0 c / 4) (j + 2)) L) :=
      ((contDiff_smoothStep _ _).continuous.measurable).sub ((contDiff_smoothStep _ _).continuous.measurable)
    exact (hOm_m.mul hcut_m).mul hchi_m
  have hom_bd : ∀ j ∈ Finset.range N, ∀ L, |nearOmega ε c R j L| ≤ 1 := fun j _ L => by
    unfold nearOmega partChi
    have hcu := nearCut_bounds c L
    have hw01 := hw_bd L
    have hsf01 : 0 ≤ sFar c (c * (Real.exp L / π ^ 2)) ∧ sFar c (c * (Real.exp L / π ^ 2)) ≤ 1 := hsf_bd L
    have hOm01 : 0 ≤ ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) :=
      mul_nonneg hw01.1 (by linarith only [hsf01.2])
    have hOm_le1 : ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) ≤ 1 := by
      nlinarith only [hw01, hsf01]
    have hs10 := smoothStep_nonneg (partGrid (ctLv0 c / 4) j) (partGrid (ctLv0 c / 4) (j + 1)) L
    have hs11 := smoothStep_le_one (partGrid (ctLv0 c / 4) j) (partGrid (ctLv0 c / 4) (j + 1)) L
    have hs20 := smoothStep_nonneg (partGrid (ctLv0 c / 4) (j + 1)) (partGrid (ctLv0 c / 4) (j + 2)) L
    have hs21 := smoothStep_le_one (partGrid (ctLv0 c / 4) (j + 1)) (partGrid (ctLv0 c / 4) (j + 2)) L
    have hchi : |smoothStep (partGrid (ctLv0 c / 4) j) (partGrid (ctLv0 c / 4) (j + 1)) L -
        smoothStep (partGrid (ctLv0 c / 4) (j + 1)) (partGrid (ctLv0 c / 4) (j + 2)) L| ≤ 1 :=
      abs_le.2 ⟨by linarith only [hs10, hs21], by linarith only [hs11, hs20]⟩
    rw [abs_mul, abs_of_nonneg (mul_nonneg hOm01 hcu.1)]
    have h1 : ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) * nearCut c L ≤ 1 := by
      nlinarith only [hOm01, hOm_le1, hcu]
    calc ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) * nearCut c L *
          |smoothStep (partGrid (ctLv0 c / 4) j) (partGrid (ctLv0 c / 4) (j + 1)) L -
            smoothStep (partGrid (ctLv0 c / 4) (j + 1)) (partGrid (ctLv0 c / 4) (j + 2)) L|
        ≤ 1 * 1 := mul_le_mul h1 hchi (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hom_int : ∀ j ∈ Finset.range N,
      Integrable fun L => nearOmega ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) :=
    fun j hj => integrable_wmul hh hKm hKb (hom_m j hj) (hom_bd j hj)
  have hmoll_diff : -(3 * c ^ (-(4 / 3 : ℝ))) ≤
      (∫ L : ℝ, Om L * nearCut c L * (hankelHL c f L * boasKernel (boasX c ε) L)) -
        ∑ j ∈ Finset.range N, ∫ L : ℝ, nearWeight ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
    rw [← integral_finsetSum _ hnw_int]
    have hsum_om_int :
        ∫ L : ℝ, Om L * nearCut c L * (hankelHL c f L * boasKernel (boasX c ε) L) =
          ∫ L : ℝ, ∑ j ∈ Finset.range N, nearOmega ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
      refine integral_congr_ae (ae_of_all _ fun L => ?_)
      dsimp only [Om, boasSf]
      rw [← hsum_om L]
      exact Finset.sum_mul _ _ _
    have hint_om_sum : Integrable fun L =>
        ∑ j ∈ Finset.range N, nearOmega ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) :=
      integrable_finsetSum _ hom_int
    have hint_nw_sum : Integrable fun L =>
        ∑ j ∈ Finset.range N, nearWeight ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) :=
      integrable_finsetSum _ hnw_int
    rw [hsum_om_int, ← integral_sub hint_om_sum hint_nw_sum]
    have hpt : ∀ L : ℝ, -(3 * c ^ (-(4 / 3 : ℝ)) * |hankelHL c f L|) ≤
        (∑ j ∈ Finset.range N, nearOmega ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L)) -
          ∑ j ∈ Finset.range N, nearWeight ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) := fun L => by
      have hrew : (∑ j ∈ Finset.range N, nearOmega ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L)) -
            ∑ j ∈ Finset.range N, nearWeight ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) =
          (∑ j ∈ Finset.range N, (nearOmega ε c R j L - nearWeight ε c R j L)) *
            (hankelHL c f L * boasKernel (boasX c ε) L) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      have hsum_abs : |∑ j ∈ Finset.range N, (nearOmega ε c R j L - nearWeight ε c R j L)| ≤ c ^ (-(4 / 3 : ℝ)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ j ∈ Finset.range N, |nearOmega ε c R j L - nearWeight ε c R j L|
            = ∑ j ∈ Finset.range N, |nearWeight ε c R j L - nearOmega ε c R j L| :=
              Finset.sum_congr rfl fun _ _ => abs_sub_comm _ _
          _ ≤ c ^ (-(4 / 3 : ℝ)) := hdiff_le L
      have hK3 : |hankelHL c f L * boasKernel (boasX c ε) L| ≤ 3 * |hankelHL c f L| := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hKb L) (abs_nonneg (hankelHL c f L))).trans_eq (mul_comm _ 3)
      rw [hrew]
      refine neg_le_of_abs_le ?_
      rw [abs_mul]
      calc |∑ j ∈ Finset.range N, (nearOmega ε c R j L - nearWeight ε c R j L)| *
            |hankelHL c f L * boasKernel (boasX c ε) L|
          ≤ c ^ (-(4 / 3 : ℝ)) * (3 * |hankelHL c f L|) :=
            mul_le_mul hsum_abs hK3 (abs_nonneg _) (Real.rpow_nonneg hc0.le _)
        _ = 3 * c ^ (-(4 / 3 : ℝ)) * |hankelHL c f L| := by ring
    have hint_neg : Integrable fun L : ℝ => -(3 * c ^ (-(4 / 3 : ℝ)) * |hankelHL c f L|) :=
      (hh.abs.const_mul (3 * c ^ (-(4 / 3 : ℝ)))).neg
    have hint_sub : Integrable fun L : ℝ =>
        (∑ j ∈ Finset.range N, nearOmega ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L)) -
          ∑ j ∈ Finset.range N, nearWeight ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) :=
      hint_om_sum.sub hint_nw_sum
    have hm := integral_mono hint_neg hint_sub hpt
    rw [integral_neg, integral_const_mul, integral_abs_hankelHL hc0 hf', hmass, mul_one] at hm
    exact hm
  -- 5. Fejer lower bound on blocks
  have hLt_thresh : ∀ L, ctLv0 c / 3 < L → T ≤ c * (Real.exp L / π ^ 2) := fun L hL => by
    have hK := langerScale_pos hc0
    have h1 : Lt * (0.998 * langerScale c) ≤ 3 := by
      have := (ctVprime_bounds hc0 hLt0 hLte).1.trans hLtv
      linarith only [this]
    have h2 : Lt ≤ 3 / (0.998 * langerScale c) := by
      rw [le_div_iff₀ (by positivity)]; exact h1
    have h3 : (2 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)) ≤ ctLv0 c / 3 := by linarith only [hLκ]
    exact hLT L (by linarith only [h2, hLt_cmp, h3, hL])
  have hhar_block : ∀ j ∈ Finset.range N, ∀ k : ℕ, 2 ≤ k → k ≤ Nat.ceil (c ^ 2) →
      |∫ L : ℝ, nearWeight ε c R j L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))| ≤
        C_har * hankelMass c f * c ^ (-(14 : ℝ)) := fun j hj k hk2 hk_le =>
    hharm_c₁ hε hch hR.1 hR.2 hf' j hj k hk2 hk_le
  have hfejer := near_block_fejer_lower hc1 hf hChar0 hhar_block
    (fun j hj => (hblock j hj).2.2.2.2.2.2.1)
    (fun j hj => (hblock j hj).2.2.2.2.2.2.2.1)
    (fun j hj => (hblock j hj).2.2.2.2.2.2.2.2.2.1)
    hsum_om hdiff_le hw_bd hmass hLt_thresh
  have hN_log_bd : (N : ℝ) ≤ 250 * Real.log (16 / ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)))) + 200 * nearB c + 810 := by
    have hL_ge : (6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)) ≤ ctLv0 c := by linarith only [hLκ]
    have h16_le : 16 / ctLv0 c ≤ 16 / ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ))) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hL_ge
    have hlog := Real.log_le_log (by positivity) h16_le
    linarith only [hN_le, hlog]
  have hNF_le_2c2 : (Nat.ceil (c ^ 2) : ℝ) ≤ 2 * c ^ 2 := by
    have h1 : (Nat.ceil (c ^ 2) : ℝ) < c ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 ≤ c ^ 2 := by nlinarith only [hc3]
    linarith only [h1, h2]
  have hhar_43 : 2 * (N : ℝ) * (Nat.ceil (c ^ 2) : ℝ) * C_har * c ^ (-(14 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
    calc 2 * (N : ℝ) * (Nat.ceil (c ^ 2) : ℝ) * C_har * c ^ (-(14 : ℝ))
        ≤ 2 * (250 * Real.log (16 / ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)))) + 200 * nearB c + 810) *
            (2 * c ^ 2) * C_har * c ^ (-(14 : ℝ)) := by
          gcongr
          have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith only [hN0, hN_log_bd]
      _ ≤ c ^ (-(4 / 3 : ℝ)) := hhar_cmp
  have hfejer_43 : -(5 * c ^ (-(4 / 3 : ℝ))) ≤
      ∑ j ∈ Finset.range N, ∫ L : ℝ, nearWeight ε c R j L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
    have h1 : 4 * c ^ (-(2 : ℝ)) ≤ 4 * c ^ (-(4 / 3 : ℝ)) := by nlinarith only [hcm2_le_43]
    linarith only [hfejer, h1, hhar_43]
  -- Split `∫_{Ici Lmin} ctTaper * h * K` into `sf + (1 - sf)`
  have hi_sf : IntegrableOn (fun L => ctTaper ε c R L * boasSf c L * (hankelHL c f L * boasKernel (boasX c ε) L))
      (Ici Lmin) :=
    (integrable_wmul hh hKm hKb (hw_m.mul hsf_m) fun L => by
      show |ctTaper ε c R L * boasSf c L| ≤ 1
      rw [abs_of_nonneg (mul_nonneg (hw_bd L).1 (hsf_bd L).1)]
      nlinarith only [hw_bd L, hsf_bd L]).integrableOn
  have hi_om : IntegrableOn (fun L => Om L * (hankelHL c f L * boasKernel (boasX c ε) L)) (Ici Lmin) :=
    (integrable_wmul hh hKm hKb hOm_m fun L => by rw [abs_of_nonneg (hOm0 L)]; exact hOm1 L).integrableOn
  have hsplit : ∫ L in Ici Lmin, ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L) =
      (∫ L in Ici Lmin, Om L * (hankelHL c f L * boasKernel (boasX c ε) L)) +
        ∫ L in Ici Lmin, ctTaper ε c R L * boasSf c L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
    rw [← integral_add hi_om hi_sf]
    refine integral_congr_ae (ae_of_all _ fun L => ?_)
    dsimp only [Om]; ring
  rw [hsplit]
  linarith only [hfar_43, hnear_diff, hmoll_diff, hfejer_43]

/-- info: 'FormalResearch.SignUncertainty.boas_sharp_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_sharp_proved

end FormalResearch.SignUncertainty

