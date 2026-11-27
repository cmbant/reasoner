/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerSymCal
public import FormalResearch.SignUncertainty.FctInnerB2
public import FormalResearch.SignUncertainty.FctPhiKillCore
public import FormalResearch.SignUncertainty.FctCompDTargets
public import FormalResearch.SignUncertainty.CtCfuGerm
public import FormalResearch.Asymptotics.BinetRemainder

/-!
# Concrete factor symbol bounds (Part A): `T`, `T⁴`, `B_c(i T)`, `φ_kill(i T)/m(T)`

Proves `FctSymClsOn (Icc 0 (fctUc c)) 8` bounds for the concrete inner variable `T = fctInnerT c V`
and the factors `K₄ T⁴`, `B_c(i T)`, and `φ_kill(i T; a) / m(T)` needed in
`fct:inner-symbols` (b3) and (b4).

Class: proved.
-/

@[expose] public section

open Set Filter Topology
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

open FormalResearch.Asymptotics FormalResearch.SignUncertainty.FctPhiKill
open FormalResearch.SignUncertainty.CtCfu

/-! ### Symbol bounds for `T = fctInnerT c V` on `[0, U_c]` -/

lemma fctUc_pos {c : ℝ} (hc : 0 < c) : 0 < fctUc c := by
  unfold fctUc; positivity

lemma one_add_fctUc_le {c : ℝ} (hc : 1 ≤ c) : 1 + fctUc c ≤ 4 * c ^ ((1 : ℝ) / 12) := by
  have hc12 : 1 ≤ c ^ ((1 : ℝ) / 12) := Real.one_le_rpow hc (by norm_num)
  unfold fctUc
  linarith

lemma fctInnerT_sym_bounds {K : ℝ} (hK : 0 ≤ K) :
    ∃ B_T : ℝ, 1 ≤ B_T ∧ ∀ {c : ℝ}, 1 ≤ c → K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 →
      ∀ {V : ℝ → ℝ}, FctVJets K c V →
        ContDiffOn ℝ 8 (fctInnerT c V) (Icc 0 (fctUc c)) ∧
        (∀ u ∈ Icc 0 (fctUc c), 0 ≤ fctInnerT c V u ∧
          fctInnerT c V u ≤ B_T * c ^ (-(1 / 3 : ℝ)) * (1 + u)) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ 8 → ∀ u ∈ Icc 0 (fctUc c),
          |iteratedDerivWithin j (fctInnerT c V) (Icc 0 (fctUc c)) u| ≤
            B_T * c ^ (-(1 / 3 : ℝ)) * (1 + u) ^ ((1 : ℝ) - j)) ∧
        FctSymClsOn (Icc 0 (fctUc c)) 8 1 (B_T * c ^ (-(1 / 3 : ℝ)))
          (fun u => ((fctInnerT c V u : ℝ) : ℂ)) := by
  set τs : ℝ := (12 / π ^ 2) ^ (1 / 3 : ℝ)
  have hτs0 : 0 ≤ τs := Real.rpow_nonneg (by positivity) _
  obtain ⟨B, hB1, hBG⟩ := fctB2_G_bound (K + τs) (by positivity)
  set B_T : ℝ := max 1 ((Nat.factorial 8 : ℝ) * 4 ^ 7 * B)
  refine ⟨B_T, le_max_left _ _, fun {c} hc hη {V} hV => ?_⟩
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu : UniqueDiffOn ℝ (Icc 0 (fctUc c)) := uniqueDiffOn_Icc hUc0
  have hsu : UniqueDiffOn ℝ (Icc (0 : ℝ) 2.96) := uniqueDiffOn_Icc (by norm_num)
  have hVb : ∀ j : ℕ, j ≤ 8 → ∀ Y ∈ Icc (0 : ℝ) 3.6,
      ‖iteratedFDerivWithin ℝ j V (Icc (0 : ℝ) 3.6) Y‖ ≤ K + τs := by
    intro j hj Y hY
    have h := hV.2 j (by omega) Y hY
    rw [← Real.norm_eq_abs, ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin] at h
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [norm_iteratedFDerivWithin_zero] at h ⊢
      calc ‖V Y‖ = ‖(V Y - τs) + τs‖ := by ring_nf
        _ ≤ ‖V Y - τs‖ + ‖τs‖ := norm_add_le _ _
        _ ≤ K + τs := by
          rw [Real.norm_of_nonneg hτs0]
          have hc1 : K * c ^ (-(1 / 2 : ℝ)) ≤ K :=
            mul_le_of_le_one_right hK (Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num))
          linarith
    · have e : iteratedDerivWithin j V (Icc (0 : ℝ) 3.6) Y =
          iteratedDerivWithin j (fun z => τs + (V z - τs)) (Icc (0 : ℝ) 3.6) Y := by
        congr 1; funext z; ring
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, e,
        iteratedDerivWithin_const_add hj0, ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
      have h' : ‖iteratedFDerivWithin ℝ j (fun z => V z - τs) (Icc (0 : ℝ) 3.6) Y‖ ≤
          K * c ^ (-(1 / 2 : ℝ)) := h
      have hc1 : K * c ^ (-(1 / 2 : ℝ)) ≤ K :=
        mul_le_of_le_one_right hK (Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num))
      linarith
  obtain ⟨hGc, hGb⟩ := hBG V (hV.1.of_le (by norm_num)) hVb
  set x12 : ℝ := c ^ ((1 : ℝ) / 12)
  have hx12_pos : 0 < x12 := Real.rpow_pos_of_pos hc0 _
  have hx12_ge1 : 1 ≤ x12 := Real.one_le_rpow hc (by norm_num)
  set l : ℝ := x12⁻¹
  have hl0 : 0 < l := inv_pos.mpr hx12_pos
  set τ₁ : ℝ := fctTau1 c
  have hτ₁0 : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_eq : τ₁ * l = c ^ (-(1 / 3 : ℝ)) := by
    dsimp only [τ₁, fctTau1, l, x12]
    rw [← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]
    congr 1; norm_num
  have hmaps : MapsTo (fun u : ℝ => l * u) (Icc 0 (fctUc c)) (Icc (0 : ℝ) 2.96) := by
    intro u hu
    refine ⟨mul_nonneg hl0.le hu.1, ?_⟩
    have h1 : u ≤ 2.96 * x12 := hu.2
    calc l * u ≤ l * (2.96 * x12) := mul_le_mul_of_nonneg_left h1 hl0.le
      _ = 2.96 := by dsimp only [l]; field_simp [hx12_pos.ne']
  let G : ℝ → ℝ := fun x => 2 ^ (-(2 / 3 : ℝ)) * (x * V (2 ^ (-(4 / 3 : ℝ)) * x ^ 2))
  have hTeq : fctInnerT c V = fun u => τ₁ * G (l * u) := by
    ext u
    have hr := fctB2_inner_ratio hc0 V u
    have hdiv : fctInnerT c V u = τ₁ * (fctInnerT c V u / τ₁) := by
      field_simp [hτ₁0.ne']
    rw [hdiv, hr]
    dsimp only [G, l, x12]
    rw [div_eq_mul_inv]
    ring
  have hlin : ContDiffOn ℝ 8 (fun u : ℝ => l * u) (Icc 0 (fctUc c)) :=
    (contDiff_const.mul contDiff_id).contDiffOn
  have hTcd : ContDiffOn ℝ 8 (fctInnerT c V) (Icc 0 (fctUc c)) := by
    rw [hTeq]; exact contDiffOn_const.mul (hGc.comp hlin hmaps)
  have hY_mem : ∀ u ∈ Icc 0 (fctUc c),
      2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2 ∈ Icc (0 : ℝ) 3.6 := by
    intro u hu
    have hYeq : 2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2 =
        2 ^ (-(4 / 3 : ℝ)) * (l * u) ^ 2 := by
      dsimp only [l, x12]
      have hc16 : (c ^ ((1 : ℝ) / 12)) ^ 2 = c ^ ((1 : ℝ) / 6) := by
        rw [← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc0.le]; norm_num
      rw [mul_pow, inv_pow, hc16, ← Real.rpow_neg hc0.le]
      ring
    rw [hYeq]
    have hlu := hmaps hu
    refine ⟨by positivity, ?_⟩
    have hmle : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 0.3969 := fctB2_two_rpow_neg43_le
    have hsq : (l * u) ^ 2 ≤ 2.96 ^ 2 := pow_le_pow_left₀ hlu.1 hlu.2 2
    nlinarith [sq_nonneg (l * u)]
  have hT0 : ∀ u ∈ Icc 0 (fctUc c), 0 ≤ fctInnerT c V u ∧
      fctInnerT c V u ≤ B_T * c ^ (-(1 / 3 : ℝ)) * (1 + u) := by
    intro u hu
    have hY := hY_mem u hu
    have hτs_ge : (1 : ℝ) ≤ τs := by
      have hpi2 : π ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      have h12 : 1 ≤ 12 / π ^ 2 := by rw [one_le_div (by positivity)]; exact hpi2.le
      exact Real.one_le_rpow h12 (by norm_num)
    have hτs_le : τs ≤ 1.2 := by
      have hpi2 : (9 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three]
      have h12 : 12 / π ^ 2 ≤ 12 / 9 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hpi2.le
      have hc3 : τs ^ 3 = 12 / π ^ 2 := by
        dsimp only [τs]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      by_contra hgt; push Not at hgt
      have : (1.2 : ℝ) ^ 3 < τs ^ 3 := pow_lt_pow_left₀ hgt (by norm_num) (by norm_num)
      rw [hc3] at this; linarith
    have hVb_abs := abs_le.mp (hV.2 0 (Nat.zero_le _) _ hY)
    rw [iteratedDerivWithin_zero] at hVb_abs
    have hV0 : 0 ≤ V (2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2) := by
      linarith [hVb_abs.1, hη]
    have hVle : V (2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2) ≤ τs + 0.001 := by
      linarith [hVb_abs.2, hη]
    have hnn : 0 ≤ fctInnerT c V u := by
      unfold fctInnerT
      exact mul_nonneg (by have := hu.1; positivity) hV0
    have h23 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 0.63 := fctB2_two_rpow_neg23_le
    have hprod : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * V (2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2) ≤ 1 := by
      nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(2 / 3 : ℝ))]
    have hle : fctInnerT c V u ≤ B_T * c ^ (-(1 / 3 : ℝ)) * (1 + u) := by
      unfold fctInnerT
      calc (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u *
              V (2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2)
          = c ^ (-(1 / 3 : ℝ)) * u *
              ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * V (2 ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) * u ^ 2)) := by ring
        _ ≤ c ^ (-(1 / 3 : ℝ)) * u * 1 := by gcongr; exact mul_nonneg (by positivity) hu.1
        _ ≤ B_T * c ^ (-(1 / 3 : ℝ)) * (1 + u) := by
            have hc13 : 0 ≤ c ^ (-(1 / 3 : ℝ)) := by positivity
            have hBT1 : 1 ≤ B_T := le_max_left _ _
            have hBTu : u ≤ B_T * (1 + u) := by nlinarith [hu.1]
            calc c ^ (-(1 / 3 : ℝ)) * u * 1 = c ^ (-(1 / 3 : ℝ)) * u := mul_one _
              _ ≤ c ^ (-(1 / 3 : ℝ)) * (B_T * (1 + u)) := mul_le_mul_of_nonneg_left hBTu hc13
              _ = B_T * c ^ (-(1 / 3 : ℝ)) * (1 + u) := by ring
    exact ⟨hnn, hle⟩
  have hTderiv : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → ∀ u ∈ Icc 0 (fctUc c),
      |iteratedDerivWithin j (fctInnerT c V) (Icc 0 (fctUc c)) u| ≤
        B_T * c ^ (-(1 / 3 : ℝ)) * (1 + u) ^ ((1 : ℝ) - j) := by
    intro j hj1 hj8 u hu
    have h1u0 : 0 < 1 + u := by linarith [hu.1]
    have hcomp_j := norm_iteratedFDerivWithin_comp_le (g := G) (f := fun u : ℝ => l * u)
      (n := j) (N := 8) hGc hlin (by exact_mod_cast hj8) hsu hDu hmaps hu
      (C := B) (D := l)
      (fun i hi => hGb i (hi.trans hj8) (l * u) (hmaps hu))
      (fun i hi1 hij => by
        refine (fctB2_affine_norm l hDu hu hi1).trans ?_
        rw [abs_of_pos hl0])
    have hGcomp_eq : fctInnerT c V = fun v => τ₁ * (G ∘ fun w => l * w) v := hTeq
    rw [hGcomp_eq, iteratedDerivWithin_const_mul hu hDu τ₁
      ((hGc.comp hlin hmaps).contDiffWithinAt hu |>.of_le (by exact_mod_cast hj8)),
      abs_mul, abs_of_pos hτ₁0, ← Real.norm_eq_abs, ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    have hle_T : τ₁ * ‖iteratedFDerivWithin ℝ j (G ∘ fun w => l * w) (Icc 0 (fctUc c)) u‖ ≤
        τ₁ * ((j.factorial : ℝ) * B * l ^ j) := mul_le_mul_of_nonneg_left hcomp_j hτ₁0.le
    refine hle_T.trans ?_
    have hj_fac : (j.factorial : ℝ) ≤ Nat.factorial 8 := by exact_mod_cast Nat.factorial_le hj8
    have h1u_le : 1 + u ≤ 4 * x12 := (by linarith [hu.2] : 1 + u ≤ 1 + fctUc c).trans (one_add_fctUc_le hc)
    have hpow_le : (1 + u) ^ (j - 1) ≤ (4 * x12) ^ (j - 1) :=
      pow_le_pow_left₀ h1u0.le h1u_le (j - 1)
    have hl_split : l ^ j = l * l ^ (j - 1) := by
      have : j = 1 + (j - 1) := (Nat.add_sub_cancel' hj1).symm
      conv_lhs => rw [this, pow_add, pow_one]
    have hl4 : l ^ (j - 1) ≤ 4 ^ (j - 1) * ((1 + u) ^ (j - 1))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos h1u0 _), ← mul_pow]
      have hmul : l * (1 + u) ≤ 4 := by
        calc l * (1 + u) ≤ l * (4 * x12) := mul_le_mul_of_nonneg_left h1u_le hl0.le
          _ = 4 := by dsimp only [l]; field_simp [hx12_pos.ne']
      exact pow_le_pow_left₀ (by positivity) hmul (j - 1)
    have h4pow : (4 : ℝ) ^ (j - 1) ≤ 4 ^ 7 := pow_le_pow_right₀ (by norm_num) (by omega)
    have hrpow_eq : (1 + u) ^ ((1 : ℝ) - j) = ((1 + u) ^ (j - 1))⁻¹ := by
      have hsub_cast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
      rw [show (1 : ℝ) - (j : ℝ) = -(((j - 1 : ℕ) : ℝ)) by rw [hsub_cast]; ring,
        Real.rpow_neg h1u0.le, Real.rpow_natCast]
    rw [hrpow_eq, hl_split]
    have hfac_B : (j.factorial : ℝ) * B * 4 ^ (j - 1) ≤ B_T := by
      have hB0 : 0 ≤ B := by linarith [hB1]
      calc (j.factorial : ℝ) * B * 4 ^ (j - 1)
          ≤ (Nat.factorial 8 : ℝ) * B * 4 ^ 7 := by gcongr
        _ = (Nat.factorial 8 : ℝ) * 4 ^ 7 * B := by ring
        _ ≤ B_T := le_max_right _ _
    have hc13_eq : τ₁ * ((j.factorial : ℝ) * B * (l * l ^ (j - 1))) =
        (τ₁ * l) * ((j.factorial : ℝ) * B * l ^ (j - 1)) := by ring
    rw [hc13_eq, hτ₁_eq]
    have hB0 : 0 ≤ B := by linarith [hB1]
    calc c ^ (-(1 / 3 : ℝ)) * ((j.factorial : ℝ) * B * l ^ (j - 1))
        ≤ c ^ (-(1 / 3 : ℝ)) * ((j.factorial : ℝ) * B * (4 ^ (j - 1) * ((1 + u) ^ (j - 1))⁻¹)) := by
          gcongr
      _ = ((j.factorial : ℝ) * B * 4 ^ (j - 1)) * c ^ (-(1 / 3 : ℝ)) * ((1 + u) ^ (j - 1))⁻¹ := by ring
      _ ≤ B_T * c ^ (-(1 / 3 : ℝ)) * ((1 + u) ^ (j - 1))⁻¹ := by gcongr
  have hsym : FctSymClsOn (Icc 0 (fctUc c)) 8 1 (B_T * c ^ (-(1 / 3 : ℝ)))
      (fun u => ((fctInnerT c V u : ℝ) : ℂ)) := by
    refine FctSymClsOn.ofReal_cast hDu hTcd fun r hr u hu => ?_
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero, Real.rpow_one, abs_of_nonneg (hT0 u hu).1]
      exact (hT0 u hu).2
    · exact hTderiv r hr0 hr u hu
  exact ⟨hTcd, hT0, hTderiv, hsym⟩

/-! ### `K₄ T⁴ ∈ S⁴(C K₄ c^{-4/3})` -/

lemma fctInner_T4_sym {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K4 c : ℝ}, 1 ≤ K4 → 1 ≤ c → K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 →
      ∀ {V : ℝ → ℝ}, FctVJets K c V →
        FctSymClsOn (Icc 0 (fctUc c)) 8 4 (C * K4 * c ^ (-(4 / 3 : ℝ)))
          (fun u => ((-(K4 * (fctInnerT c V u) ^ 4) : ℝ) : ℂ)) := by
  obtain ⟨B_T, hBT1, hBT⟩ := fctInnerT_sym_bounds hK
  refine ⟨2 ^ 24 * B_T ^ 4, by positivity, fun {K4 c} hK4 hc hη {V} hV => ?_⟩
  have hc0 : 0 < c := by linarith
  have hDu : UniqueDiffOn ℝ (Icc 0 (fctUc c)) := uniqueDiffOn_Icc (fctUc_pos hc0)
  obtain ⟨_, _, _, hTsym⟩ := hBT hc hη hV
  have h2 := hTsym.mul Icc_subset_Ici_self hDu hTsym
  have h4 := h2.mul Icc_subset_Ici_self hDu h2
  have h4neg := (h4.const_mul hDu ((-K4 : ℝ) : ℂ))
  have hK4n : ‖((-K4 : ℝ) : ℂ)‖ = K4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith)]
  have hceq : ‖((-K4 : ℝ) : ℂ)‖ * (2 ^ 8 * (2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) *
      (B_T * c ^ (-(1 / 3 : ℝ)))) * (2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) *
      (B_T * c ^ (-(1 / 3 : ℝ))))) =
      2 ^ 24 * B_T ^ 4 * K4 * c ^ (-(4 / 3 : ℝ)) := by
    rw [hK4n]
    have hpow4 : (c ^ (-(1 / 3 : ℝ))) ^ 4 = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    calc K4 * (2 ^ 8 * (2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ)))) *
          (2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ)))))
        = 2 ^ 24 * B_T ^ 4 * K4 * (c ^ (-(1 / 3 : ℝ))) ^ 4 := by ring
      _ = 2 ^ 24 * B_T ^ 4 * K4 * c ^ (-(4 / 3 : ℝ)) := by rw [hpow4]
  have hfeq : EqOn (fun u => ((-K4 : ℝ) : ℂ) * (((fctInnerT c V u : ℝ) : ℂ) *
      ((fctInnerT c V u : ℝ) : ℂ) * (((fctInnerT c V u : ℝ) : ℂ) *
      ((fctInnerT c V u : ℝ) : ℂ)))) (fun u => ((-(K4 * (fctInnerT c V u) ^ 4) : ℝ) : ℂ))
      (Icc 0 (fctUc c)) := fun u _ => by
    push_cast; ring
  have hexp : (1 : ℝ) + 1 + (1 + 1) = 4 := by norm_num
  rw [hexp, hceq] at h4neg
  exact h4neg.congr hDu (fun u hu => (hfeq hu).symm)

/-! ### `B_c(i T) ∈ S¹(C c^{-4/3})` -/

private lemma binetDiff_differentiableOn_left {c : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (binetDiff c) {ζ : ℂ | ζ.re < 1} := by
  have h1 : DifferentiableOn ℂ (fun ζ : ℂ => binetRem ((c : ℂ) * (1 - ζ))) {ζ : ℂ | ζ.re < 1} := by
    refine binetRem_differentiableOn.comp ?_ ?_
    · exact (differentiable_const _ |>.mul (differentiable_const _ |>.sub differentiable_id)).differentiableOn
    · intro ζ hζ
      simp only [mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, zero_mul, sub_zero]
      have : 0 < 1 - ζ.re := sub_pos.mpr hζ
      positivity
  exact h1.sub (differentiableOn_const _)

private lemma contDiff_binetImag {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ⊤ (fun τ : ℝ => binetDiff c ((τ : ℂ) * Complex.I)) := by
  have hopen : IsOpen {ζ : ℂ | ζ.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hcd_C : ContDiffOn ℂ ⊤ (binetDiff c) {ζ : ℂ | ζ.re < 1} :=
    (binetDiff_differentiableOn_left hc).contDiffOn hopen
  have hcd_R : ContDiffOn ℝ ⊤ (binetDiff c) {ζ : ℂ | ζ.re < 1} := hcd_C.restrict_scalars ℝ
  rw [contDiff_iff_contDiffAt]
  intro τ
  have hmem : ((τ : ℂ) * Complex.I) ∈ {ζ : ℂ | ζ.re < 1} := by simp
  have hat : ContDiffAt ℝ ⊤ (binetDiff c) ((τ : ℂ) * Complex.I) := hcd_R.contDiffAt (hopen.mem_nhds hmem)
  have hlin : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  exact hat.comp τ hlin.contDiffAt

private lemma iteratedDeriv_binetImag {c : ℝ} (hc : 0 < c) (k : ℕ) (τ : ℝ) :
    iteratedDeriv k (fun t : ℝ => binetDiff c ((t : ℂ) * Complex.I)) τ =
      Complex.I ^ k * iteratedDeriv k (binetDiff c) ((τ : ℂ) * Complex.I) := by
  have hopen : IsOpen {ζ : ℂ | ζ.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hcd_C : ContDiffOn ℂ ⊤ (binetDiff c) {ζ : ℂ | ζ.re < 1} :=
    (binetDiff_differentiableOn_left hc).contDiffOn hopen
  induction k generalizing τ with
  | zero => simp
  | succ k ih =>
    have hfun : iteratedDeriv k (fun t : ℝ => binetDiff c ((t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.I ^ k * iteratedDeriv k (binetDiff c) ((t : ℂ) * Complex.I) := funext ih
    rw [iteratedDeriv_succ, hfun]
    have hmem : ((τ : ℂ) * Complex.I) ∈ {ζ : ℂ | ζ.re < 1} := by simp
    have hcd_k : ContDiffOn ℂ ⊤ (iteratedDeriv k (binetDiff c)) {ζ : ℂ | ζ.re < 1} := by
      clear hmem ih hfun τ
      induction k with
      | zero => simpa using hcd_C
      | succ k ihk =>
        rw [show iteratedDeriv (k + 1) (binetDiff c) = deriv (iteratedDeriv k (binetDiff c)) by
          ext z; rw [iteratedDeriv_succ]]
        exact ihk.deriv_of_isOpen hopen (by simp)
    have hd_C : HasDerivAt (iteratedDeriv k (binetDiff c))
        (iteratedDeriv (k + 1) (binetDiff c) ((τ : ℂ) * Complex.I)) ((τ : ℂ) * Complex.I) := by
      rw [iteratedDeriv_succ]
      exact ((hcd_k.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)).hasDerivAt
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I τ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I
    have hcomp := (hd_C.scomp τ hlin).const_mul (Complex.I ^ k)
    have hcomp_deriv : deriv (fun t : ℝ => Complex.I ^ k * iteratedDeriv k (binetDiff c) ((t : ℂ) * Complex.I)) τ =
        Complex.I ^ k * (Complex.I * iteratedDeriv (k + 1) (binetDiff c) ((τ : ℂ) * Complex.I)) := by
      simpa [Function.comp, smul_eq_mul] using hcomp.deriv
    rw [hcomp_deriv, pow_succ]
    ring

lemma fctInner_binet_sym {K : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ}, 1 ≤ c → K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 →
      ∀ {V : ℝ → ℝ}, FctVJets K c V →
        FctSymClsOn (Icc 0 (fctUc c)) 8 1 (C * c ^ (-(4 / 3 : ℝ)))
          (fun u => binetDiff c (Complex.I * ((fctInnerT c V u : ℝ) : ℂ))) := by
  obtain ⟨B_T, hBT1, hBT⟩ := fctInnerT_sym_bounds hK
  set M_b : ℝ := max 1 (4 * B_T)
  set C1 : ℝ := (Nat.factorial 7 : ℝ) * ((Nat.factorial 8 : ℝ) / 12) * M_b ^ 7
  set C_all : ℝ := max (B_T / 12) (2 ^ 7 * C1 * B_T)
  refine ⟨C_all, by positivity, fun {c} hc hη {V} hV => ?_⟩
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu : UniqueDiffOn ℝ (Icc 0 (fctUc c)) := uniqueDiffOn_Icc hUc0
  obtain ⟨hTcd, hT0, hTderiv, hTsym⟩ := hBT hc hη hV
  let bI : ℝ → ℂ := fun τ => binetDiff c ((τ : ℂ) * Complex.I)
  have hbI_cd : ContDiff ℝ ⊤ bI := contDiff_binetImag hc0
  have hbI_deriv_bd : ∀ j : ℕ, 1 ≤ j → ∀ τ : ℝ, ‖iteratedDeriv j bI τ‖ ≤ (j.factorial : ℝ) / (12 * c) := by
    intro j hj τ
    rw [iteratedDeriv_binetImag hc0 j τ, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
    have hre : ((τ : ℂ) * Complex.I).re ≤ 0 := by simp
    exact binetDiff_iteratedDeriv_norm_le hc0 hre hj
  -- `bI' ∘ T ∈ S^0` up to order 7
  let bI' : ℝ → ℂ := deriv bI
  have hbI'_cd : ContDiffOn ℝ 7 bI' univ :=
    ((hbI_cd.of_le (show ((7 + 1 : ℕ) : WithTop ℕ∞) ≤ ⊤ by simp)).deriv').contDiffOn
  have hbI'_bd : ∀ i ≤ 7, ∀ τ ∈ (univ : Set ℝ),
      ‖iteratedDerivWithin i bI' univ τ‖ ≤ ((Nat.factorial 8 : ℝ) / 12) * c⁻¹ := by
    intro i hi τ _
    rw [iteratedDerivWithin_univ, ← iteratedDeriv_succ']
    refine (hbI_deriv_bd (i + 1) (Nat.succ_pos i) τ).trans ?_
    have hfac : ((i + 1).factorial : ℝ) ≤ Nat.factorial 8 := by
      exact_mod_cast Nat.factorial_le (by omega : i + 1 ≤ 8)
    calc ((i + 1).factorial : ℝ) / (12 * c)
        ≤ (Nat.factorial 8 : ℝ) / (12 * c) := by gcongr
      _ = ((Nat.factorial 8 : ℝ) / 12) * c⁻¹ := by ring
  have hBfM : B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c) ≤ M_b := by
    have hUc4 := one_add_fctUc_le hc
    have hc14 : c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12) = c ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hc_le1 : c ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num)
    calc B_T * c ^ (-(1 / 3 : ℝ)) * (1 + fctUc c)
        ≤ B_T * c ^ (-(1 / 3 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
      _ = 4 * B_T * (c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
      _ ≤ 4 * B_T * 1 := by rw [hc14]; gcongr
      _ ≤ M_b := by rw [mul_one]; exact le_max_right _ _
  have hbI'_T := FctSymClsOn.comp_T_zero hUc0 (le_max_left _ _ : 1 ≤ M_b) uniqueDiffOn_univ
    hbI'_cd (by positivity) hbI'_bd (hTcd.of_le (by norm_num)) (mapsTo_univ _ _)
    (by positivity) hBfM (fun j hj1 hj7 u hu => hTderiv j hj1 (le_trans hj7 (by norm_num)) u hu)
  have hT'_sym : FctSymClsOn (Icc 0 (fctUc c)) 7 0 (B_T * c ^ (-(1 / 3 : ℝ)))
      (fun u => ((derivWithin (fctInnerT c V) (Icc 0 (fctUc c)) u : ℝ) : ℂ)) := by
    have hTd := hTsym.derivWithin_Icc hUc0 (by norm_num)
    rw [show (8 - 1 : ℕ) = 7 from rfl, show ((1 : ℝ) - 1) = 0 by ring] at hTd
    refine hTd.congr (uniqueDiffOn_Icc hUc0) ?_
    intro u hu
    have hd1 : HasDerivWithinAt (fctInnerT c V)
        (derivWithin (fctInnerT c V) (Icc 0 (fctUc c)) u) (Icc 0 (fctUc c)) u :=
      (hTcd.differentiableOn (by norm_num) u hu).hasDerivWithinAt
    have hd2 : HasDerivWithinAt (fun x => ((fctInnerT c V x : ℝ) : ℂ))
        ((derivWithin (fctInnerT c V) (Icc 0 (fctUc c)) u : ℝ) : ℂ) (Icc 0 (fctUc c)) u :=
      hd1.ofReal_comp
    exact (hd2.derivWithin (hDu u hu)).symm
  have hprod := hbI'_T.mul Icc_subset_Ici_self hDu hT'_sym
  have hcd_main : ContDiffOn ℝ 8 (fun u => binetDiff c (Complex.I * ((fctInnerT c V u : ℝ) : ℂ)))
      (Icc 0 (fctUc c)) := by
    have heq : (fun u => binetDiff c (Complex.I * ((fctInnerT c V u : ℝ) : ℂ))) = bI ∘ fctInnerT c V := by
      ext u; simp [bI, mul_comm]
    rw [heq]
    exact (hbI_cd.of_le (by simp)).comp_contDiffOn hTcd
  refine ⟨hcd_main, fun r hr u hu => ?_⟩
  have h1u0 : 0 < 1 + u := by linarith [hu.1]
  have heq_main : EqOn (fun u => binetDiff c (Complex.I * ((fctInnerT c V u : ℝ) : ℂ)))
      (bI ∘ fctInnerT c V) (Icc 0 (fctUc c)) := fun x _ => by simp [bI, mul_comm]
  rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedFDerivWithin_congr heq_main hu r, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rw [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero, Real.rpow_one]
    have h0 : bI 0 = 0 := by
      simp [bI, binetDiff]
    have hbd0 : ∀ t ∈ Icc 0 (fctInnerT c V u), ‖deriv bI t‖ ≤ 1 / (12 * c) := fun t _ => by
      simpa using hbI_deriv_bd 1 le_rfl t
    have hmv := (convex_Icc 0 (fctInnerT c V u)).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (hbI_cd.differentiable (by simp)).differentiableAt)
      hbd0 (left_mem_Icc.mpr (hT0 u hu).1) (right_mem_Icc.mpr (hT0 u hu).1)
    rw [h0, sub_zero, Real.norm_eq_abs, sub_zero, abs_of_nonneg (hT0 u hu).1] at hmv
    have hc43 : c⁻¹ * c ^ (-(1 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; congr 1; norm_num
    calc ‖bI (fctInnerT c V u)‖ ≤ (1 / (12 * c)) * fctInnerT c V u := hmv
      _ ≤ (1 / (12 * c)) * (B_T * c ^ (-(1 / 3 : ℝ)) * (1 + u)) :=
          mul_le_mul_of_nonneg_left (hT0 u hu).2 (by positivity)
      _ = (B_T / 12) * (c⁻¹ * c ^ (-(1 / 3 : ℝ))) * (1 + u) := by ring
      _ = (B_T / 12) * c ^ (-(4 / 3 : ℝ)) * (1 + u) := by rw [hc43]
      _ ≤ C_all * c ^ (-(4 / 3 : ℝ)) * (1 + u) := by gcongr; exact le_max_left _ _
  · have hderiv_eq : EqOn (derivWithin (bI ∘ fctInnerT c V) (Icc 0 (fctUc c)))
        (fun x => bI' (fctInnerT c V x) *
          ((derivWithin (fctInnerT c V) (Icc 0 (fctUc c)) x : ℝ) : ℂ)) (Icc 0 (fctUc c)) := by
      intro x hx
      have hd1 : HasDerivWithinAt (fctInnerT c V)
          (derivWithin (fctInnerT c V) (Icc 0 (fctUc c)) x) (Icc 0 (fctUc c)) x :=
        (hTcd.differentiableOn (by norm_num) x hx).hasDerivWithinAt
      have hd2 : HasDerivAt bI (bI' (fctInnerT c V x)) (fctInnerT c V x) :=
        (hbI_cd.differentiable (by simp) _).hasDerivAt
      have hd := (hd2.scomp_hasDerivWithinAt x hd1).derivWithin (hDu x hx)
      rw [hd, Complex.real_smul, mul_comm]
    rw [← Nat.sub_add_cancel hr0, iteratedDerivWithin_succ',
      ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedFDerivWithin_congr hderiv_eq hu (r - 1),
      norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    have hbd := hprod.2 (r - 1) (Nat.sub_le_sub_right hr 1) u hu
    have hexp1 : ((0 : ℝ) + 0 - ((r - 1 : ℕ) : ℝ)) = 1 - (((r - 1 + 1 : ℕ) : ℝ)) := by
      have hsub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by rw [Nat.cast_sub hr0, Nat.cast_one]
      have hadd : ((r - 1 + 1 : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast Nat.sub_add_cancel hr0
      rw [hsub, hadd]; ring
    rw [hexp1] at hbd
    have hc43 : c⁻¹ * c ^ (-(1 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; congr 1; norm_num
    have hc_eq : 2 ^ 7 * ((Nat.factorial 7 : ℝ) * ((Nat.factorial 8 : ℝ) / 12 * c⁻¹) * M_b ^ 7) *
        (B_T * c ^ (-(1 / 3 : ℝ))) = (2 ^ 7 * C1 * B_T) * c ^ (-(4 / 3 : ℝ)) := by
      dsimp only [C1]
      calc 2 ^ 7 * ((Nat.factorial 7 : ℝ) * ((Nat.factorial 8 : ℝ) / 12 * c⁻¹) * M_b ^ 7) *
            (B_T * c ^ (-(1 / 3 : ℝ)))
          = 2 ^ 7 * ((Nat.factorial 7 : ℝ) * ((Nat.factorial 8 : ℝ) / 12) * M_b ^ 7) * B_T *
              (c⁻¹ * c ^ (-(1 / 3 : ℝ))) := by ring
        _ = (2 ^ 7 * C1 * B_T) * c ^ (-(4 / 3 : ℝ)) := by rw [hc43]
    rw [hc_eq] at hbd
    refine hbd.trans ?_
    have hpow0 : 0 ≤ (1 + u) ^ (1 - (((r - 1 + 1 : ℕ) : ℝ))) := (Real.rpow_pos_of_pos h1u0 _).le
    have hc_le : 2 ^ 7 * C1 * B_T ≤ C_all := le_max_right _ _
    gcongr

/-! ### `φ_kill(i T; a) / m(T) ∈ S⁶(C c^{-4/3})` -/

/-- Smooth rational part of `φ_kill(i τ; a) / (τ/a)^8` (`w = τ/a`). -/
noncomputable def phiKillR (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range 8, ((Nat.choose 15 (8 + j) : ℝ) : ℂ) * w ^ j / (1 + w) ^ 15

lemma phiKill_imag_eq_mul_phiKillR {a τ : ℝ} (ha : 0 < a) :
    phiKill a ((τ : ℂ) * Complex.I) =
      (((τ / a) ^ 8 : ℝ) : ℂ) * phiKillR (((τ / a : ℝ) : ℂ) * Complex.I) := by
  unfold phiKill phiPQ phiKillR
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  set w : ℂ := ((τ / a : ℝ) : ℂ) * Complex.I
  have h1w : 1 + w ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp [w] at hre
  have hza : ((τ : ℂ) * Complex.I) + (a : ℂ) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp [ha.ne'] at hre
  have heq : Finset.Ico 8 (8 + 8) = Finset.image (fun j => 8 + j) (Finset.range 8) := by
    ext l; simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]; constructor
    · intro ⟨h1, h2⟩; exact ⟨l - 8, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega
  rw [heq, Finset.sum_image (fun x _ y _ h => by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj8 : j < 8 := Finset.mem_range.mp hj
  have hw8 : w ^ 8 = (((τ / a) ^ 8 : ℝ) : ℂ) := by
    dsimp only [w]
    have hI8 : Complex.I ^ 8 = 1 := by
      calc Complex.I ^ 8 = (Complex.I ^ 2) ^ 4 := by ring
        _ = 1 := by norm_num [Complex.I_sq]
    rw [mul_pow, hI8, mul_one, ← Complex.ofReal_pow]
  have hz_eq : ((τ : ℂ) * Complex.I) = (a : ℂ) * w := by
    dsimp only [w]; push_cast; field_simp [ha.ne']
  have hza_eq : ((τ : ℂ) * Complex.I) + (a : ℂ) = (a : ℂ) * (1 + w) := by
    rw [hz_eq]; ring
  rw [hza_eq, hz_eq, ← hw8]
  have hsub : 8 + 8 - 1 - (8 + j) = 7 - j := by omega
  rw [hsub]
  have hdiv1 : ((a : ℂ) * w / ((a : ℂ) * (1 + w))) ^ (8 + j) = (w / (1 + w)) ^ (8 + j) := by
    congr 1; field_simp [haC]
  have hdiv2 : ((a : ℂ) / ((a : ℂ) * (1 + w))) ^ (7 - j) = (1 / (1 + w)) ^ (7 - j) := by
    congr 1; field_simp [haC]
  rw [hdiv1, hdiv2, div_pow, div_pow, one_pow, mul_assoc, div_mul_div_comm, ← pow_add,
    show (8 + j) + (7 - j) = 15 by omega, pow_add, show 8 + 8 - 1 = 15 from rfl]
  push_cast; ring

/-- Smooth continuation of `τ ↦ φ_kill(i τ; a) / m(τ)` on `[0, √rr)`. -/
noncomputable def phiKillDivM (a τ : ℝ) : ℂ :=
  if τ = 0 then 0 else phiKill a ((τ : ℂ) * Complex.I) / ((uctM τ : ℝ) : ℂ)

lemma phiKillDivM_eq {a τ : ℝ} (ha : 0 < a) (h0 : 0 ≤ τ) (hrr : τ ^ 2 < rr) :
    phiKillDivM a τ =
      ((τ ^ 6 * a ^ (-8 : ℤ) : ℝ) : ℂ) * phiKillR (((τ / a : ℝ) : ℂ) * Complex.I) /
        ((nfun (τ ^ 2) : ℝ) : ℂ) := by
  by_cases hτ0 : τ = 0
  · subst hτ0; simp [phiKillDivM]
  · unfold phiKillDivM
    simp only [hτ0, ↓reduceIte]
    have hm : uctM τ = τ ^ 2 * nfun (τ ^ 2) := by
      change hankelEdgeM τ = _; exact hankelEdgeM_eq h0 hrr
    rw [phiKill_imag_eq_mul_phiKillR ha, hm, div_pow]
    push_cast
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hτC : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ0
    rw [zpow_neg, show (8 : ℤ) = ((8 : ℕ) : ℤ) by rfl, zpow_natCast]
    field_simp [haC, hτC]

private lemma contDiff_phiKillR_imag :
    ContDiff ℝ 8 (fun s : ℝ => phiKillR ((s : ℂ) * Complex.I)) := by
  have h1s : ∀ s : ℝ, 1 + (s : ℂ) * Complex.I ≠ 0 := fun s h0 => by
    have hre := congrArg Complex.re h0; simp at hre
  have hdiff : DifferentiableOn ℂ phiKillR {z : ℂ | 1 + z ≠ 0} := by
    refine DifferentiableOn.fun_sum fun j _ => ?_
    refine (differentiableOn_const _ |>.mul (differentiableOn_id.pow j)).div
      ((differentiableOn_const 1 |>.add differentiableOn_id).pow 15) fun z hz => pow_ne_zero 15 hz
  have hopen : IsOpen {z : ℂ | 1 + z ≠ 0} := isOpen_ne.preimage (continuous_const.add continuous_id)
  have hcd_R : ContDiffOn ℝ 8 phiKillR {z : ℂ | 1 + z ≠ 0} :=
    ((hdiff.contDiffOn hopen).restrict_scalars ℝ).of_le le_top
  have hlin : ContDiff ℝ 8 (fun s : ℝ => (s : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  exact contDiffOn_univ.mp (hcd_R.comp hlin.contDiffOn fun s _ => h1s s)

private lemma contDiffOn_Ioo_bdd_on_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} (hR : 0 < R) {n : ℕ} {g : ℝ → F} (hg : ContDiffOn ℝ n g (Ioo (-R) R)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ n, ∀ t ∈ Ioo (-(R / 2)) (R / 2),
      ‖iteratedDerivWithin i g (Ioo (-(R / 2)) (R / 2)) t‖ ≤ C := by
  have hsub : Icc (-(R / 2)) (R / 2) ⊆ Ioo (-R) R := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsub' : Ioo (-(R / 2)) (R / 2) ⊆ Icc (-(R / 2)) (R / 2) := fun x hx => ⟨hx.1.le, hx.2.le⟩
  have hcd_k : ∀ k : ℕ, k ≤ n →
      ContDiffOn ℝ ((n - k : ℕ) : WithTop ℕ∞) (iteratedDerivWithin k g (Ioo (-R) R)) (Ioo (-R) R) := by
    intro k
    induction k with
    | zero => intro _; simpa using hg
    | succ k ih =>
      intro hk
      have hprev := ih (Nat.le_of_succ_le hk)
      have hsplit : ((n - k : ℕ) : WithTop ℕ∞) = (((n - (k + 1) : ℕ) : ℕ∞) + 1 : ℕ∞) := by
        have hn : n - k = (n - (k + 1)) + 1 := by omega
        rw [hn]; push_cast; rfl
      rw [hsplit] at hprev
      have hd := hprev.derivWithin (m := ((n - (k + 1) : ℕ) : ℕ∞)) isOpen_Ioo.uniqueDiffOn
        (by rw [← WithTop.coe_one, ← WithTop.coe_add])
      simpa [iteratedDerivWithin_succ] using hd.of_le (by norm_cast)
  have hbd : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ (k ≤ n → ∀ t ∈ Icc (-(R / 2)) (R / 2), ‖iteratedDeriv k g t‖ ≤ B) := by
    intro k
    by_cases hk : k ≤ n
    · obtain ⟨B, hB⟩ := (isCompact_Icc (a := -(R / 2)) (b := R / 2)).exists_bound_of_continuousOn
        ((hcd_k k hk).continuousOn.mono hsub)
      refine ⟨max B 0, le_max_right _ _, fun _ t ht => ?_⟩
      rw [← iteratedDerivWithin_of_isOpen isOpen_Ioo (hsub ht)]
      exact (hB t ht).trans (le_max_left _ _)
    · exact ⟨0, le_rfl, fun hkn => absurd hkn hk⟩
  choose B hB0 hB using hbd
  refine ⟨∑ i ∈ Finset.range (n + 1), B i, Finset.sum_nonneg fun i _ => hB0 i, fun i hi t ht => ?_⟩
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioo ht]
  exact (hB i hi t (hsub' ht)).trans (Finset.single_le_sum (fun k _ => hB0 k) (Finset.mem_range.mpr (by omega)))

lemma fctInner_phiKillDivM_sym {K : ℝ} (hK : 0 ≤ K) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ {c : ℝ}, c₀ ≤ c →
      ∀ {V : ℝ → ℝ}, FctVJets K c V →
        FctSymClsOn (Icc 0 (fctUc c)) 8 6 (C * c ^ (-(4 / 3 : ℝ)))
          (fun u => phiKillDivM (c ^ (-(1 / 12 : ℝ))) (fctInnerT c V u)) := by
  obtain ⟨B_T, hBT1, hBT⟩ := fctInnerT_sym_bounds hK
  -- Bound `phiKillR (· * I)` on `(-1/2, 1/2)`
  have hcd_pkR : ContDiffOn ℝ 8 (fun s : ℝ => phiKillR ((s : ℂ) * Complex.I)) (Ioo (-1 : ℝ) 1) :=
    contDiff_phiKillR_imag.contDiffOn
  obtain ⟨CR, hCR0, hCR⟩ := contDiffOn_Ioo_bdd_on_Icc zero_lt_one hcd_pkR
  -- Neighborhood `(-δ_n, δ_n)` around `0` where `nfun > 0`
  have hnfun_ev : ∀ᶠ y in 𝓝 (0 : ℝ), 0 < nfun y := by
    have hcont : ContinuousAt nfun 0 :=
      (contDiffOn_nfun.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith [rr_pos], rr_pos⟩)).continuousAt
    exact hcont.eventually (lt_mem_nhds (by rw [nfun_zero]; positivity))
  obtain ⟨δ_raw, hδ_raw0, hδ_raw_pos⟩ := Metric.eventually_nhds_iff.mp hnfun_ev
  set δ_n : ℝ := min (rr / 2) (δ_raw / 2)
  have hδn0 : 0 < δ_n := lt_min (half_pos rr_pos) (half_pos hδ_raw0)
  have hnfun_pos : ∀ y ∈ Ioo (-δ_n) δ_n, nfun y ≠ 0 := fun y hy => by
    have hy_raw : dist y 0 < δ_raw := by
      rw [Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [hy.1, min_le_right (rr / 2) (δ_raw / 2)],
        by linarith [hy.2, min_le_right (rr / 2) (δ_raw / 2)]⟩
    exact (hδ_raw_pos hy_raw).ne'
  have hcd_ninv : ContDiffOn ℝ 8 (fun y : ℝ => ((nfun y : ℝ) : ℂ)⁻¹) (Ioo (-δ_n) δ_n) := by
    have hsub : Ioo (-δ_n) δ_n ⊆ Ioo (-rr) rr := fun y hy =>
      ⟨by linarith [hy.1, min_le_left (rr / 2) (δ_raw / 2), rr_pos],
       by linarith [hy.2, min_le_left (rr / 2) (δ_raw / 2), rr_pos]⟩
    have hn_cd : ContDiffOn ℝ 8 nfun (Ioo (-δ_n) δ_n) :=
      (contDiffOn_nfun.mono hsub).of_le (WithTop.coe_le_coe.mpr le_top)
    have h1 : ContDiffOn ℝ 8 (fun y : ℝ => ((nfun y : ℝ) : ℂ)) (Ioo (-δ_n) δ_n) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hn_cd
    exact h1.inv fun y hy => Complex.ofReal_ne_zero.mpr (hnfun_pos y hy)
  obtain ⟨Cn, hCn0, hCn⟩ := contDiffOn_Ioo_bdd_on_Icc hδn0 hcd_ninv
  -- Choose `c₀ ≥ 1` sufficiently large for `K c^{-1/2} ≤ 0.001`, `2 τ₁ < min (1/2) √(δ_n/2)`, `2 c^{-1/6} < 1/2`
  set c_eta : ℝ := (1000 * K) ^ 2 + 1
  set c_div : ℝ := (8 * B_T + 1) ^ 6 + 1
  set c_n : ℝ := ((16 * B_T ^ 2 + 1) / (δ_n / 2)) ^ 2 + 1
  set c_rr : ℝ := ((16 * B_T ^ 2 + 1) / rr) ^ 2 + 1
  set c₀ : ℝ := max (max c_eta c_div) (max c_n c_rr)
  have hc0_ge1 : 1 ≤ c₀ := by
    have : 1 ≤ c_eta := by dsimp only [c_eta]; linarith [sq_nonneg (1000 * K)]
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  set M_pk : ℝ := max 1 (4 * B_T)
  set C_R_sym : ℝ := (Nat.factorial 8 : ℝ) * CR * M_pk ^ 8
  set M_n : ℝ := max 1 (16 * 2 ^ 8 * B_T ^ 2)
  set C_n_sym : ℝ := (Nat.factorial 8 : ℝ) * Cn * M_n ^ 8
  set C_all : ℝ := 2 ^ 8 * (2 ^ 8 * (2 ^ 40 * B_T ^ 6) * C_R_sym) * C_n_sym
  refine ⟨C_all, c₀, by positivity, hc0_ge1, fun {c} hc {V} hV => ?_⟩
  have hc1 : 1 ≤ c := hc0_ge1.trans hc
  have hc0 : 0 < c := by linarith
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu : UniqueDiffOn ℝ (Icc 0 (fctUc c)) := uniqueDiffOn_Icc hUc0
  have hη : K * c ^ (-(1 / 2 : ℝ)) ≤ 0.001 := by
    have hc_eta : (1000 * K) ^ 2 ≤ c := by
      have : (1000 * K) ^ 2 ≤ c_eta := by dsimp only [c_eta]; linarith
      exact this.trans ((le_max_left _ _).trans ((le_max_left _ _).trans hc))
    exact fctB2_eta_small hc_eta hc1
  obtain ⟨hTcd, hT0, hTderiv, hTsym⟩ := hBT hc1 hη hV
  set a : ℝ := c ^ (-(1 / 12 : ℝ))
  have ha0 : 0 < a := Real.rpow_pos_of_pos hc0 _
  have hc16 : c ^ (-(1 / 6 : ℝ)) ≤ 1 / (8 * B_T + 1) := by
    have hc_div : (8 * B_T + 1) ^ 6 ≤ c := by
      have : (8 * B_T + 1) ^ 6 ≤ c_div := by dsimp only [c_div]; linarith
      exact this.trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc))
    have hinv : c ^ (-(1 / 6 : ℝ)) = (c ^ ((1 : ℝ) / 6))⁻¹ := by rw [Real.rpow_neg hc0.le]
    rw [hinv, ← one_div, div_le_div_iff₀ (Real.rpow_pos_of_pos hc0 _) (by linarith [hBT1]), one_mul, one_mul]
    have hpow : (8 * B_T + 1) ^ 6 ≤ (c ^ ((1 : ℝ) / 6)) ^ 6 := by
      rw [← Real.rpow_natCast (c ^ ((1 : ℝ) / 6)), ← Real.rpow_mul hc0.le]; norm_num; exact hc_div
    by_contra hlt; push Not at hlt
    have : (c ^ ((1 : ℝ) / 6)) ^ 6 < (8 * B_T + 1) ^ 6 :=
      pow_lt_pow_left₀ hlt (Real.rpow_nonneg hc0.le _) (by norm_num)
    linarith
  have hc12_n : (16 * B_T ^ 2 + 1) * c ^ (-(1 / 2 : ℝ)) ≤ δ_n / 2 := by
    have hc_n : ((16 * B_T ^ 2 + 1) / (δ_n / 2)) ^ 2 ≤ c := by
      have : ((16 * B_T ^ 2 + 1) / (δ_n / 2)) ^ 2 ≤ c_n := by dsimp only [c_n]; linarith
      exact this.trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
    have hsq : (16 * B_T ^ 2 + 1) / (δ_n / 2) ≤ √c := Real.le_sqrt_of_sq_le hc_n
    rw [Real.rpow_neg hc0.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv, div_le_iff₀ (Real.sqrt_pos.mpr hc0)]
    rw [div_le_iff₀ (by positivity)] at hsq
    linarith
  have hc12_rr : (16 * B_T ^ 2 + 1) * c ^ (-(1 / 2 : ℝ)) ≤ rr := by
    have hc_rr : ((16 * B_T ^ 2 + 1) / rr) ^ 2 ≤ c := by
      have : ((16 * B_T ^ 2 + 1) / rr) ^ 2 ≤ c_rr := by dsimp only [c_rr]; linarith
      exact this.trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
    have hsq : (16 * B_T ^ 2 + 1) / rr ≤ √c := Real.le_sqrt_of_sq_le hc_rr
    rw [Real.rpow_neg hc0.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv, div_le_iff₀ (Real.sqrt_pos.mpr hc0)]
    rw [div_le_iff₀ rr_pos] at hsq
    linarith
  -- Bound on `T(u)`: `0 ≤ T(u) ≤ 4 B_T c^{-1/4}`
  have hT_unif : ∀ u ∈ Icc 0 (fctUc c), fctInnerT c V u ≤ 4 * B_T * c ^ (-(1 / 4 : ℝ)) := by
    intro u hu
    have h1u : 1 + u ≤ 4 * c ^ ((1 : ℝ) / 12) := (by linarith [hu.2] : 1 + u ≤ 1 + fctUc c).trans (one_add_fctUc_le hc1)
    have hc14 : c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12) = c ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc fctInnerT c V u ≤ B_T * c ^ (-(1 / 3 : ℝ)) * (1 + u) := (hT0 u hu).2
      _ ≤ B_T * c ^ (-(1 / 3 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
      _ = 4 * B_T * (c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
      _ = 4 * B_T * c ^ (-(1 / 4 : ℝ)) := by rw [hc14]
  -- (1) `T^6 ∈ S^6(2^40 B_T^6 c^{-2})`
  have hT2 := hTsym.mul Icc_subset_Ici_self hDu hTsym
  have hT4 := hT2.mul Icc_subset_Ici_self hDu hT2
  have hT6 := hT4.mul Icc_subset_Ici_self hDu hT2
  have hT6' : FctSymClsOn (Icc 0 (fctUc c)) 8 6 (2 ^ 40 * B_T ^ 6 * c ^ (-2 : ℝ))
      (fun u => ((fctInnerT c V u ^ 6 : ℝ) : ℂ)) := by
    have hceq : 2 ^ 8 * (2 ^ 8 * (2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ)))) *
          (2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ))))) *
          (2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ)))) =
        2 ^ 40 * B_T ^ 6 * c ^ (-2 : ℝ) := by
      have hpow6 : (c ^ (-(1 / 3 : ℝ))) ^ 6 = c ^ (-2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
      calc _ = 2 ^ 40 * B_T ^ 6 * (c ^ (-(1 / 3 : ℝ))) ^ 6 := by ring
        _ = 2 ^ 40 * B_T ^ 6 * c ^ (-2 : ℝ) := by rw [hpow6]
    have hexp : (1 : ℝ) + 1 + (1 + 1) + (1 + 1) = 6 := by norm_num
    rw [hexp, hceq] at hT6
    exact hT6.congr hDu fun u _ => by push_cast; ring
  -- (2) `phiKillR (T(u)/a * I) ∈ S^0(C_R_sym)`
  have hdiv_cd : ContDiffOn ℝ 8 (fun u => fctInnerT c V u / a) (Icc 0 (fctUc c)) :=
    hTcd.div_const a
  have hdiv_maps : MapsTo (fun u => fctInnerT c V u / a) (Icc 0 (fctUc c)) (Ioo (-(1 / 2) : ℝ) (1 / 2)) := by
    intro u hu
    have h0 : 0 ≤ fctInnerT c V u / a := div_nonneg (hT0 u hu).1 ha0.le
    have hc_ratio : c ^ (-(1 / 4 : ℝ)) / a = c ^ (-(1 / 6 : ℝ)) := by
      dsimp only [a]; rw [div_eq_mul_inv, ← Real.rpow_neg hc0.le, neg_neg, ← Real.rpow_add hc0]
      congr 1; norm_num
    have hlt : fctInnerT c V u / a < 1 / 2 := by
      calc fctInnerT c V u / a ≤ (4 * B_T * c ^ (-(1 / 4 : ℝ))) / a :=
            div_le_div_of_nonneg_right (hT_unif u hu) ha0.le
        _ = 4 * B_T * c ^ (-(1 / 6 : ℝ)) := by rw [mul_div_assoc, hc_ratio]
        _ ≤ 4 * B_T * (1 / (8 * B_T + 1)) := by gcongr
        _ < 1 / 2 := by
            rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
            linarith
    exact ⟨by linarith, hlt⟩
  have hdiv_deriv : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → ∀ u ∈ Icc 0 (fctUc c),
      |iteratedDerivWithin j (fun u => fctInnerT c V u / a) (Icc 0 (fctUc c)) u| ≤
        (B_T * c ^ (-(1 / 4 : ℝ))) * (1 + u) ^ ((1 : ℝ) - j) := by
    intro j hj1 hj8 u hu
    have heq : (fun u => fctInnerT c V u / a) = fun u => a⁻¹ * fctInnerT c V u := by
      ext x; rw [div_eq_mul_inv, mul_comm]
    rw [heq, iteratedDerivWithin_const_mul hu hDu a⁻¹ (hTcd.contDiffWithinAt hu |>.of_le (by exact_mod_cast hj8)),
      abs_mul, abs_of_pos (inv_pos.mpr ha0)]
    have hc14' : a⁻¹ * c ^ (-(1 / 3 : ℝ)) = c ^ (-(1 / 4 : ℝ)) := by
      dsimp only [a]; rw [← Real.rpow_neg hc0.le, neg_neg, ← Real.rpow_add hc0]; congr 1; norm_num
    calc a⁻¹ * |iteratedDerivWithin j (fctInnerT c V) (Icc 0 (fctUc c)) u|
        ≤ a⁻¹ * (B_T * c ^ (-(1 / 3 : ℝ)) * (1 + u) ^ ((1 : ℝ) - j)) :=
          mul_le_mul_of_nonneg_left (hTderiv j hj1 hj8 u hu) (inv_pos.mpr ha0).le
      _ = B_T * (a⁻¹ * c ^ (-(1 / 3 : ℝ))) * (1 + u) ^ ((1 : ℝ) - j) := by ring
      _ = (B_T * c ^ (-(1 / 4 : ℝ))) * (1 + u) ^ ((1 : ℝ) - j) := by rw [hc14']
  have hdiv_M : B_T * c ^ (-(1 / 4 : ℝ)) * (1 + fctUc c) ≤ M_pk := by
    have hUc4 := one_add_fctUc_le hc1
    have hc16_le : c ^ (-(1 / 4 : ℝ)) * c ^ ((1 : ℝ) / 12) = c ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hc16_1 : c ^ (-(1 / 6 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    calc B_T * c ^ (-(1 / 4 : ℝ)) * (1 + fctUc c)
        ≤ B_T * c ^ (-(1 / 4 : ℝ)) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
      _ = 4 * B_T * (c ^ (-(1 / 4 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
      _ ≤ 4 * B_T * 1 := by rw [hc16_le]; gcongr
      _ ≤ M_pk := by rw [mul_one]; exact le_max_right _ _
  have hpkR_mono : ∀ i ≤ 8, ∀ s ∈ Ioo (-(1 / 2) : ℝ) (1 / 2),
      ‖iteratedDerivWithin i (fun t : ℝ => phiKillR ((t : ℂ) * Complex.I)) (Ioo (-(1 / 2) : ℝ) (1 / 2)) s‖ ≤ CR :=
    fun i hi s hs => hCR i hi s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hpkR_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_R_sym
      (fun u => phiKillR (((fctInnerT c V u / a : ℝ) : ℂ) * Complex.I)) :=
    FctSymClsOn.comp_T_zero hUc0 (le_max_left _ _ : 1 ≤ M_pk) isOpen_Ioo.uniqueDiffOn
      (contDiff_phiKillR_imag.contDiffOn) hCR0 hpkR_mono hdiv_cd hdiv_maps (by positivity) hdiv_M hdiv_deriv
  -- (3) `(nfun (T(u)^2))⁻¹ ∈ S^0(C_n_sym)`
  have hTsq_cd : ContDiffOn ℝ 8 (fun u => fctInnerT c V u ^ 2) (Icc 0 (fctUc c)) := hTcd.pow 2
  have hTsq_lt : ∀ u ∈ Icc 0 (fctUc c), fctInnerT c V u ^ 2 < min (δ_n / 2) rr := by
    intro u hu
    have hc14_sq : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hsq : fctInnerT c V u ^ 2 ≤ 16 * B_T ^ 2 * c ^ (-(1 / 2 : ℝ)) := by
      calc fctInnerT c V u ^ 2 ≤ (4 * B_T * c ^ (-(1 / 4 : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (hT0 u hu).1 (hT_unif u hu) 2
        _ = 16 * B_T ^ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 := by ring
        _ = 16 * B_T ^ 2 * c ^ (-(1 / 2 : ℝ)) := by rw [hc14_sq]
    have hc12_pos : 0 < c ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    exact lt_min (by linarith [hc12_n, hc12_pos]) (by linarith [hc12_rr, hc12_pos])
  have hTsq_maps : MapsTo (fun u => fctInnerT c V u ^ 2) (Icc 0 (fctUc c)) (Ioo (-(δ_n / 2)) (δ_n / 2)) :=
    fun u hu => ⟨by linarith [sq_nonneg (fctInnerT c V u), hδn0],
      (hTsq_lt u hu).trans_le (min_le_left _ _)⟩
  have hTsq_deriv : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → ∀ u ∈ Icc 0 (fctUc c),
      |iteratedDerivWithin j (fun u => fctInnerT c V u ^ 2) (Icc 0 (fctUc c)) u| ≤
        (4 * 2 ^ 8 * B_T ^ 2 * c ^ (-(7 / 12 : ℝ))) * (1 + u) ^ ((1 : ℝ) - j) := by
    intro j hj1 hj8 u hu
    have hbd := hT2.2 j hj8 u hu
    rw [show (1 : ℝ) + 1 - (j : ℝ) = 1 + ((1 : ℝ) - j) by ring] at hbd
    have h1u0 : 0 < 1 + u := by linarith [hu.1]
    rw [Real.rpow_add h1u0, Real.rpow_one] at hbd
    have heq_c : ((c ^ (-(1 / 3 : ℝ))) * (c ^ (-(1 / 3 : ℝ)))) * c ^ ((1 : ℝ) / 12) =
        c ^ (-(7 / 12 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; congr 1; norm_num
    have h1u_le : 1 + u ≤ 4 * c ^ ((1 : ℝ) / 12) :=
      (by linarith [hu.2] : 1 + u ≤ 1 + fctUc c).trans (one_add_fctUc_le hc1)
    have hid_eq : iteratedDerivWithin j (fun x => ((fctInnerT c V x ^ 2 : ℝ) : ℂ)) (Icc 0 (fctUc c)) u =
        ((iteratedDerivWithin j (fun x => fctInnerT c V x ^ 2) (Icc 0 (fctUc c)) u : ℝ) : ℂ) := by
      exact iteratedDerivWithin_ofReal_cast hDu hTsq_cd hj8 u hu
    have hmul_eq : (fun x => ((fctInnerT c V x : ℝ) : ℂ) * ((fctInnerT c V x : ℝ) : ℂ)) =
        fun x => ((fctInnerT c V x ^ 2 : ℝ) : ℂ) := by
      ext x; push_cast; ring
    have hbd' := hbd
    rw [hmul_eq, hid_eq, Complex.norm_real, Real.norm_eq_abs] at hbd'
    have hpow0 : 0 ≤ (1 + u) ^ ((1 : ℝ) - j) := (Real.rpow_pos_of_pos h1u0 _).le
    calc |iteratedDerivWithin j (fun x => fctInnerT c V x ^ 2) (Icc 0 (fctUc c)) u|
        ≤ 2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ))) *
            ((1 + u) * (1 + u) ^ ((1 : ℝ) - j)) := hbd'
      _ ≤ 2 ^ 8 * (B_T * c ^ (-(1 / 3 : ℝ))) * (B_T * c ^ (-(1 / 3 : ℝ))) *
            ((4 * c ^ ((1 : ℝ) / 12)) * (1 + u) ^ ((1 : ℝ) - j)) := by
          gcongr
      _ = 4 * 2 ^ 8 * B_T ^ 2 *
            (c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * c ^ ((1 : ℝ) / 12)) * (1 + u) ^ ((1 : ℝ) - j) := by
          ring
      _ = (4 * 2 ^ 8 * B_T ^ 2 * c ^ (-(7 / 12 : ℝ))) * (1 + u) ^ ((1 : ℝ) - j) := by rw [heq_c]
  have hTsq_M : (4 * 2 ^ 8 * B_T ^ 2 * c ^ (-(7 / 12 : ℝ))) * (1 + fctUc c) ≤ M_n := by
    have hUc4 := one_add_fctUc_le hc1
    have hc12' : c ^ (-(7 / 12 : ℝ)) * c ^ ((1 : ℝ) / 12) = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    have hc_le1 : c ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    calc (4 * 2 ^ 8 * B_T ^ 2 * c ^ (-(7 / 12 : ℝ))) * (1 + fctUc c)
        ≤ (4 * 2 ^ 8 * B_T ^ 2 * c ^ (-(7 / 12 : ℝ))) * (4 * c ^ ((1 : ℝ) / 12)) := by gcongr
      _ = 16 * 2 ^ 8 * B_T ^ 2 * (c ^ (-(7 / 12 : ℝ)) * c ^ ((1 : ℝ) / 12)) := by ring
      _ ≤ 16 * 2 ^ 8 * B_T ^ 2 * 1 := by rw [hc12']; gcongr
      _ ≤ M_n := by rw [mul_one]; exact le_max_right _ _
  have hn_sym : FctSymClsOn (Icc 0 (fctUc c)) 8 0 C_n_sym
      (fun u => ((nfun (fctInnerT c V u ^ 2) : ℝ) : ℂ)⁻¹) :=
    FctSymClsOn.comp_T_zero hUc0 (le_max_left _ _ : 1 ≤ M_n) isOpen_Ioo.uniqueDiffOn
      (hcd_ninv.mono (Ioo_subset_Ioo (by linarith) (by linarith)) |>.of_le (by simp))
      hCn0 hCn hTsq_cd hTsq_maps (by positivity) hTsq_M hTsq_deriv
  -- Multiply `(T^6 * a^{-8}) * phiKillR * (nfun(T^2))⁻¹` and rewrite on `[0, U_c]`
  have ha8_norm : ‖((a ^ (-8 : ℤ) : ℝ) : ℂ)‖ = c ^ (2 / 3 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zpow_pos ha0 _)]
    dsimp only [a]
    rw [← Real.rpow_intCast, ← Real.rpow_mul hc0.le]
    congr 1; norm_num
  have hc43 : c ^ (-2 : ℝ) * c ^ (2 / 3 : ℝ) = c ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_add hc0]; congr 1; norm_num
  have hT6a := hT6'.const_mul hDu ((a ^ (-8 : ℤ) : ℝ) : ℂ)
  have hmul1 := (hT6a.congr hDu (fun u _ => by rw [mul_comm])).mul Icc_subset_Ici_self hDu hpkR_sym
  have hmul2 := hmul1.mul Icc_subset_Ici_self hDu hn_sym
  have hmain_eq : EqOn (fun u => phiKillDivM a (fctInnerT c V u))
      (fun u => (((fctInnerT c V u ^ 6 : ℝ) : ℂ) * ((a ^ (-8 : ℤ) : ℝ) : ℂ) *
        phiKillR (((fctInnerT c V u / a : ℝ) : ℂ) * Complex.I)) *
        ((nfun (fctInnerT c V u ^ 2) : ℝ) : ℂ)⁻¹) (Icc 0 (fctUc c)) := by
    intro u hu
    change phiKillDivM a (fctInnerT c V u) = _
    rw [phiKillDivM_eq ha0 (hT0 u hu).1 ((hTsq_lt u hu).trans_le (min_le_right _ _)),
      div_eq_mul_inv]
    push_cast; ring
  have hC_eq : 2 ^ 8 * (2 ^ 8 * (‖((a ^ (-8 : ℤ) : ℝ) : ℂ)‖ *
        (2 ^ 40 * B_T ^ 6 * c ^ (-2 : ℝ))) * C_R_sym) * C_n_sym = C_all * c ^ (-(4 / 3 : ℝ)) := by
    rw [ha8_norm]
    dsimp only [C_all]
    calc 2 ^ 8 * (2 ^ 8 * (c ^ (2 / 3 : ℝ) * (2 ^ 40 * B_T ^ 6 * c ^ (-2 : ℝ))) * C_R_sym) * C_n_sym
        = 2 ^ 8 * (2 ^ 8 * (2 ^ 40 * B_T ^ 6) * C_R_sym) * C_n_sym * (c ^ (-2 : ℝ) * c ^ (2 / 3 : ℝ)) := by ring
      _ = C_all * c ^ (-(4 / 3 : ℝ)) := by rw [hc43]
  have hexp6 : (6 : ℝ) + 0 + 0 = 6 := by norm_num
  rw [hexp6] at hmul2
  have hmul2'' : FctSymClsOn (Icc 0 (fctUc c)) 8 6
      (2 ^ 8 * (2 ^ 8 * (‖((a ^ (-8 : ℤ) : ℝ) : ℂ)‖ *
        (2 ^ 40 * B_T ^ 6 * c ^ (-2 : ℝ))) * C_R_sym) * C_n_sym)
      (fun u => phiKillDivM a (fctInnerT c V u)) :=
    hmul2.congr hDu hmain_eq
  rw [hC_eq] at hmul2''
  exact hmul2''

end FormalResearch.SignUncertainty

