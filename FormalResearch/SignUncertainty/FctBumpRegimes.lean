/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctBumpMidRegime

/-!
# Macroscopic and far lower bounds for `normDensity (ctWbump B ε c) c ξ` (`fct:bump-5`)

For `χ` (`IsCutoff χ`), `K₄ ≥ 1`, `(T₁, α)` solving the zero condition (`FctWarpZeroStmt`),
`N_c = 1 + O(c⁻¹)` (`FctSplittingNormStmt`), and
`B := physBump χ (1 / Nc ε c) c (physDelta c) (physShift ε c) K₁ K₄ O F (fun L => τ₀(L)⁴ I_fl(L))`:

* `physBump_mac_lower` (`3 δ_L ≤ L ≤ (1/4) log c`): `normDensity (ctWbump B ε c) c ξ` exceeds
  `c⁻¹ n_c γ ((O - F) + (1/2) η (O + F)) - C(K₄) (c⁻¹ I_fl (c⁻¹ + c⁻² L⁻²) + c^{-5/2}) - c^{-5/2}`.
* `physBump_far_lower` (`(1/4) log c ≤ L`): `normDensity (ctWbump B ε c) c ξ` exceeds
  `c⁻¹ n_c γ ((1 + η) O - (1 - η) F) - C(K₄, K₁) c⁻² L⁻²`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctSym
open FormalResearch.SignUncertainty.FctSym.SymW
open FormalResearch.SignUncertainty.FctCompD

namespace FormalResearch.SignUncertainty

private lemma mac_rpow_neg_nat {L : ℝ} (hL : 0 < L) (γ : ℝ) (k : ℕ) :
    L ^ (-γ - (k : ℝ)) = L ^ (-γ) / L ^ k := by
  rw [sub_eq_add_neg, Real.rpow_add hL, div_eq_mul_inv]
  congr 1
  rw [Real.rpow_neg hL.le k, Real.rpow_natCast]

private lemma mac_rpow_neg_two {x : ℝ} (hx : 0 < x) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]

private lemma mac_rpow_neg_three {x : ℝ} (hx : 0 < x) : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
  rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]

private lemma mac_inv_bound3 {a₀ c δ L : ℝ} (ha₀ : 0 < a₀) (hc0 : 0 < c)
    (hδ_lo : a₀ * c ^ (-(1 / 2 : ℝ)) ≤ δ) (hL_lo : 3 * δ ≤ L) :
    (c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹ ≤ ((3 * a₀)⁻¹ + (3 * a₀) ^ (-3 : ℝ)) * c ^ (-(3 / 2 : ℝ)) := by
  have hLa : 3 * a₀ * c ^ (-(1 / 2 : ℝ)) ≤ L := by
    have h1 : 3 * (a₀ * c ^ (-(1 / 2 : ℝ))) ≤ 3 * δ := mul_le_mul_of_nonneg_left hδ_lo (by norm_num)
    linarith only [hL_lo, h1]
  have hpos_a : 0 < 3 * a₀ * c ^ (-(1 / 2 : ℝ)) :=
    mul_pos (mul_pos (by norm_num) ha₀) (Real.rpow_pos_of_pos hc0 _)
  have hL_pos : 0 < L := lt_of_lt_of_le hpos_a hLa
  have hL1_bd : L⁻¹ ≤ (3 * a₀)⁻¹ * c ^ (1 / 2 : ℝ) := by
    have h1 : L⁻¹ ≤ (3 * a₀ * c ^ (-(1 / 2 : ℝ)))⁻¹ := inv_anti₀ hpos_a hLa
    rw [mul_inv, ← Real.rpow_neg hc0.le, neg_neg] at h1; exact h1
  have hL3_bd : (L ^ 3)⁻¹ ≤ (3 * a₀) ^ (-3 : ℝ) * c ^ (3 / 2 : ℝ) := by
    have h2 : L ^ (-3 : ℝ) ≤ (3 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hLa (by norm_num)
    rw [← mac_rpow_neg_three hL_pos]; refine h2.trans_eq ?_
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc0.le]; norm_num
  have hc2_eq : (c ^ 2)⁻¹ * c ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast c 2, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
  have hc3_eq : (c ^ 3)⁻¹ * c ^ (3 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast c 3, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
  calc (c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹
      ≤ (c ^ 2)⁻¹ * ((3 * a₀)⁻¹ * c ^ (1 / 2 : ℝ)) +
          (c ^ 3)⁻¹ * ((3 * a₀) ^ (-3 : ℝ) * c ^ (3 / 2 : ℝ)) := by gcongr
    _ = (3 * a₀)⁻¹ * ((c ^ 2)⁻¹ * c ^ (1 / 2 : ℝ)) + (3 * a₀) ^ (-3 : ℝ) * ((c ^ 3)⁻¹ * c ^ (3 / 2 : ℝ)) := by ring
    _ = ((3 * a₀)⁻¹ + (3 * a₀) ^ (-3 : ℝ)) * c ^ (-(3 / 2 : ℝ)) := by rw [hc2_eq, hc3_eq]; ring

private lemma mac_max_div {c M_x : ℝ} (hc0 : 0 < c) (hMx : 0 < M_x) :
    (if M_x ≤ 1 then M_x * uctIfl M_x else uctIfl M_x) * ((c ^ 2)⁻¹ * M_x⁻¹ + (c ^ 3)⁻¹ * (M_x ^ 3)⁻¹) ≤
      c⁻¹ * uctIfl M_x * (c⁻¹ + c ^ (-2 : ℝ) * M_x ^ (-2 : ℝ)) := by
  have hIfl : 0 ≤ uctIfl M_x := (uctIfl_pos' hMx).le
  rw [mac_rpow_neg_two hc0, mac_rpow_neg_two hMx]
  split_ifs with h1
  · have : M_x * uctIfl M_x * ((c ^ 2)⁻¹ * M_x⁻¹ + (c ^ 3)⁻¹ * (M_x ^ 3)⁻¹) =
        c⁻¹ * uctIfl M_x * (c⁻¹ + (c ^ 2)⁻¹ * (M_x ^ 2)⁻¹) := by
      field_simp [hMx.ne', hc0.ne']
    exact this.le
  · have hm1 : 1 ≤ M_x := (not_le.mp h1).le
    have hmi : M_x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm1
    have hmi3 : (M_x ^ 3)⁻¹ ≤ (M_x ^ 2)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity)]; nlinarith only [hm1]
    have h1' : (c ^ 2)⁻¹ * M_x⁻¹ + (c ^ 3)⁻¹ * (M_x ^ 3)⁻¹ ≤ (c ^ 2)⁻¹ + (c ^ 3)⁻¹ * (M_x ^ 2)⁻¹ :=
      add_le_add (mul_le_of_le_one_right (by positivity) hmi) (mul_le_mul_of_nonneg_left hmi3 (by positivity))
    calc uctIfl M_x * ((c ^ 2)⁻¹ * M_x⁻¹ + (c ^ 3)⁻¹ * (M_x ^ 3)⁻¹)
        ≤ uctIfl M_x * ((c ^ 2)⁻¹ + (c ^ 3)⁻¹ * (M_x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1' hIfl
      _ = c⁻¹ * uctIfl M_x * (c⁻¹ + (c ^ 2)⁻¹ * (M_x ^ 2)⁻¹) := by field_simp [hMx.ne', hc0.ne']

private abbrev BumpLocalFn (b α β : ℝ) (K : ℕ → ℝ) (a0 Cloc : ℝ) : Prop :=
  ∀ (B : ℝ → ℝ) (δ M Mloc c ξ : ℝ), 0 < δ → δ ≤ 1 → b * δ ≤ 1 → 0 ≤ M → 0 ≤ Mloc → 2 ≤ c →
    a0 ≤ Real.sqrt c * δ → 0 < ξ → b * δ / 2 ≤ Real.log (Real.pi ^ 2 * ξ) →
    (∀ k : ℕ, 1 ≤ k → k ≤ 9 → |iteratedDeriv k B (Real.log (Real.pi ^ 2 * ξ))| ≤
      K k * Mloc / (Real.log (Real.pi ^ 2 * ξ)) ^ k) →
    BumpProfile b δ M α β K B →
      ‖bumpHmain c B ξ - ((c⁻¹ * B (Real.log (Real.pi ^ 2 * ξ)) : ℝ) : ℂ)‖ ≤
        Cloc * Mloc * (((c ^ 2)⁻¹) * (Real.log (Real.pi ^ 2 * ξ))⁻¹ +
          ((c ^ 3)⁻¹) * ((Real.log (Real.pi ^ 2 * ξ)) ^ 3)⁻¹) +
        Cloc * M * bumpLambda α δ * ((c ^ 2)⁻¹ * δ)

private lemma mac_p1_bound {a₀ a₁ M1 Cloc1 C_mac δ c ξ : ℝ} {K1_k : ℕ → ℝ} {p1 : ℝ → ℝ}
    (_ha₀ : 0 < a₀) (_ha₁ : 0 < a₁) (hM1 : 0 ≤ M1) (hCloc1 : 0 ≤ Cloc1)
    (hαfl : 0 < uctAlphaFl) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδ32 : 3 / 2 * δ ≤ 1)
    (hsqrt_δ : a₀ ≤ Real.sqrt c * δ) (hδ_hi : δ ≤ a₁ * c ^ (-(1 / 2 : ℝ)))
    (hc2 : 2 ≤ c) (hξ : 0 < ξ) (hL_lo : 3 * δ ≤ Real.log (Real.pi ^ 2 * ξ))
    (hc1m : Cloc1 * (M1 / uctAlphaFl) ≤ C_mac / 4)
    (hc2m : Cloc1 * M1 * 2 * a₁ ≤ C_mac / 4)
    (hbs1 : BSym δ M1 (1 / 2) (3 / 2) K1_k p1)
    (hloc1 : BumpLocalFn (3 / 2) (1 / 2) (3 / 2) K1_k a₀ Cloc1) :
    ‖bumpHmain c p1 ξ - ((c⁻¹ * p1 (Real.log (Real.pi ^ 2 * ξ)) : ℝ) : ℂ)‖ ≤
      C_mac / 4 * (c⁻¹ * uctIfl (Real.log (Real.pi ^ 2 * ξ)) *
        (c⁻¹ + c ^ (-2 : ℝ) * (Real.log (Real.pi ^ 2 * ξ)) ^ (-2 : ℝ)) + c ^ (-(5 / 2 : ℝ))) := by
  have hc0 : 0 < c := by linarith only [hc2]
  set L := Real.log (Real.pi ^ 2 * ξ)
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_lo
  have hIfl_nn : 0 ≤ uctIfl L := (uctIfl_pos' hL_pos).le
  have hL32 : 3 / 2 * δ ≤ L := by linarith only [hL_lo, hδ0]
  have hL32_lo : 3 / 2 * δ / 2 ≤ L := by linarith only [hL_lo, hδ0]
  set Mloc1 : ℝ := (M1 / uctAlphaFl) * (if L ≤ 1 then L * uctIfl L else uctIfl L)
  have hMloc1 : 0 ≤ Mloc1 := by
    dsimp only [Mloc1]; split_ifs
    · exact mul_nonneg (div_nonneg hM1 hαfl.le) (mul_nonneg hL_pos.le hIfl_nn)
    · exact mul_nonneg (div_nonneg hM1 hαfl.le) hIfl_nn
  have hloc := hloc1 p1 δ M1 Mloc1 c ξ hδ0 hδ1 hδ32 hM1 hMloc1 hc2 hsqrt_δ hξ hL32_lo
    (fun k _ _ => by
      have hbd := hbs1.bound k L hL32; refine hbd.trans ?_
      have hmin_eq : uctAlphaFl * min (L ^ (-(1 / 2 : ℝ))) (L ^ (-(3 / 2 : ℝ))) =
          if L ≤ 1 then L * uctIfl L else uctIfl L := by
        unfold uctIfl; split_ifs with hL1
        · rw [min_eq_left (Real.rpow_le_rpow_of_exponent_ge hL_pos hL1 (by norm_num))]
          have : L * L ^ (-(3 / 2 : ℝ)) = L ^ (-(1 / 2 : ℝ)) := by
            conv_lhs => arg 1; rw [← Real.rpow_one L]
            rw [← Real.rpow_add hL_pos]; norm_num
          rw [mul_left_comm, this]
        · rw [min_eq_right (Real.rpow_le_rpow_of_exponent_le (not_le.mp hL1).le (by norm_num))]
      have hpow_eq : K1_k k * M1 * min (L ^ (-(1 / 2 : ℝ) - (k : ℝ))) (L ^ (-(3 / 2 : ℝ) - (k : ℝ))) =
          K1_k k * ((M1 / uctAlphaFl) * (uctAlphaFl * min (L ^ (-(1 / 2 : ℝ))) (L ^ (-(3 / 2 : ℝ))))) /
            (Real.log (Real.pi ^ 2 * ξ)) ^ k := by
        rw [mac_rpow_neg_nat hL_pos (1 / 2) k, mac_rpow_neg_nat hL_pos (3 / 2) k,
          min_div_div_right (pow_pos hL_pos k).le]
        dsimp only [L]
        field_simp [hαfl.ne', hL_pos.ne']
      rw [hpow_eq, hmin_eq]) (hbs1.profile hM1)
  have hlam1 : bumpLambda (1 / 2) δ ≤ 2 := by
    unfold bumpLambda; rw [ite_eq_right (by norm_num)]
    linarith only [Real.rpow_le_one hδ0.le hδ1 (by norm_num : 0 ≤ 1 - (1 / 2 : ℝ))]
  have hc2_52 : (c ^ 2)⁻¹ * δ ≤ a₁ * c ^ (-(5 / 2 : ℝ)) := by
    have hc212 : (c ^ 2)⁻¹ * c ^ (-(1 / 2 : ℝ)) = c ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast c 2, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
    calc (c ^ 2)⁻¹ * δ ≤ (c ^ 2)⁻¹ * (a₁ * c ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hδ_hi (by positivity)
      _ = a₁ * c ^ (-(5 / 2 : ℝ)) := by linear_combination a₁ * hc212
  have ht1 : Cloc1 * Mloc1 * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹) ≤
      (Cloc1 * (M1 / uctAlphaFl)) * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ))) := by
    dsimp only [Mloc1]
    calc Cloc1 * ((M1 / uctAlphaFl) * (if L ≤ 1 then L * uctIfl L else uctIfl L)) *
            ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹)
        = (Cloc1 * (M1 / uctAlphaFl)) *
            ((if L ≤ 1 then L * uctIfl L else uctIfl L) * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mac_max_div hc0 hL_pos) (mul_nonneg hCloc1 (div_nonneg hM1 hαfl.le))
  have ht2 : Cloc1 * M1 * bumpLambda (1 / 2) δ * ((c ^ 2)⁻¹ * δ) ≤ (Cloc1 * M1 * 2 * a₁) * c ^ (-(5 / 2 : ℝ)) :=
    calc Cloc1 * M1 * bumpLambda (1 / 2) δ * ((c ^ 2)⁻¹ * δ)
        ≤ Cloc1 * M1 * 2 * (a₁ * c ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlam1 (mul_nonneg hCloc1 hM1)) hc2_52 (by positivity) (by positivity)
      _ = (Cloc1 * M1 * 2 * a₁) * c ^ (-(5 / 2 : ℝ)) := by ring
  have hfac_nn : 0 ≤ c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hc0.le) hIfl_nn) (by positivity)
  calc ‖bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)‖
      ≤ Cloc1 * Mloc1 * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹) +
          Cloc1 * M1 * bumpLambda (1 / 2) δ * ((c ^ 2)⁻¹ * δ) := hloc
    _ ≤ (Cloc1 * (M1 / uctAlphaFl)) * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ))) +
          (Cloc1 * M1 * 2 * a₁) * c ^ (-(5 / 2 : ℝ)) := add_le_add ht1 ht2
    _ ≤ C_mac / 4 * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ))) + C_mac / 4 * c ^ (-(5 / 2 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_right hc1m hfac_nn) (mul_le_mul_of_nonneg_right hc2m (Real.rpow_nonneg hc0.le _))
    _ = C_mac / 4 * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) + c ^ (-(5 / 2 : ℝ))) := by ring

private lemma mac_p4_bound {χ : ℝ → ℝ} {a₀ a₁ M4 Cloc4 C_mac δ c ξ K4 : ℝ} {K4_k : ℕ → ℝ} {p4 : ℝ → ℝ}
    (hχ1 : ∀ x : ℝ, 1 ≤ x → χ x = 1) (hp4 : ∀ x : ℝ, p4 x = 2 * K4 * (χ (x / (3 * δ)) * ((1 - χ (x / (6 * δ))) * (tau0 x ^ 4 * uctIfl x))))
    (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hM4 : 0 ≤ M4) (hCloc4 : 0 ≤ Cloc4)
    (hαfl : 0 < uctAlphaFl) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδ32 : 3 / 2 * δ ≤ 1) (h6δ : 6 * δ ≤ 1)
    (hsqrt_δ : a₀ ≤ Real.sqrt c * δ) (hδ_hi : δ ≤ a₁ * c ^ (-(1 / 2 : ℝ)))
    (hc2 : 2 ≤ c) (hξ : 0 < ξ) (hL_lo : 3 * δ ≤ Real.log (Real.pi ^ 2 * ξ))
    (hc1m : Cloc4 * (M4 / uctAlphaFl) ≤ C_mac / 4)
    (hc2m : Cloc4 * M4 * 2 * a₁ ≤ C_mac / 4)
    (hbs4 : BSym δ M4 (-(1 / 2)) (3 / 2) K4_k p4)
    (hloc4 : BumpLocalFn (3 / 2) (-(1 / 2)) (3 / 2) K4_k a₀ Cloc4) :
    ‖bumpHmain c p4 ξ - ((c⁻¹ * p4 (Real.log (Real.pi ^ 2 * ξ)) : ℝ) : ℂ)‖ ≤
      C_mac / 4 * (c⁻¹ * uctIfl (Real.log (Real.pi ^ 2 * ξ)) *
        (c⁻¹ + c ^ (-2 : ℝ) * (Real.log (Real.pi ^ 2 * ξ)) ^ (-2 : ℝ)) + c ^ (-(5 / 2 : ℝ))) := by
  have hc0 : 0 < c := by linarith only [hc2]
  set L := Real.log (Real.pi ^ 2 * ξ)
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_lo
  have hIfl_nn : 0 ≤ uctIfl L := (uctIfl_pos' hL_pos).le
  have hL32 : 3 / 2 * δ ≤ L := by linarith only [hL_lo, hδ0]
  have hL32_lo : 3 / 2 * δ / 2 ≤ L := by linarith only [hL_lo, hδ0]
  set Mloc4 : ℝ := if L ≤ 6 * δ then (M4 / uctAlphaFl) * (L * uctIfl L) else 0
  have hMloc4 : 0 ≤ Mloc4 := by
    dsimp only [Mloc4]; split_ifs
    · exact mul_nonneg (div_nonneg hM4 hαfl.le) (mul_nonneg hL_pos.le hIfl_nn)
    · exact le_rfl
  have hloc := hloc4 p4 δ M4 Mloc4 c ξ hδ0 hδ1 hδ32 hM4 hMloc4 hc2 hsqrt_δ hξ hL32_lo
    (fun k _ _ => by
      rcases lt_or_ge L (6 * δ) with hlt | hge
      · have hL1 : L ≤ 1 := by linarith only [hlt, h6δ]
        have hbd := hbs4.bound k L hL32
        have hmin : min (L ^ (-(-(1 / 2 : ℝ)) - (k : ℝ))) (L ^ (-(3 / 2 : ℝ) - (k : ℝ))) = L ^ (1 / 2 - (k : ℝ)) := by
          rw [show -(-(1 / 2 : ℝ)) - (k : ℝ) = 1 / 2 - (k : ℝ) by ring]
          exact min_eq_left (Real.rpow_le_rpow_of_exponent_ge hL_pos hL1 (by linarith))
        rw [hmin] at hbd
        have hpow4 : L ^ (1 / 2 - (k : ℝ)) = (L ^ 2 * L ^ (-(3 / 2 : ℝ))) / L ^ k := by
          rw [sub_eq_add_neg, Real.rpow_add hL_pos, Real.rpow_neg hL_pos.le, Real.rpow_natCast, div_eq_mul_inv]
          congr 1; rw [← Real.rpow_natCast L 2, ← Real.rpow_add hL_pos]; norm_num
        have hle1 : L ^ 2 ≤ L := by nlinarith only [hL_pos, hL1]
        have hm4eq : Mloc4 = (M4 / uctAlphaFl) * (L * uctIfl L) := by simp only [Mloc4, hlt.le, ↓reduceIte]
        refine hbd.trans ?_; rw [hpow4, hm4eq]
        have hifl : uctIfl L = uctAlphaFl * L ^ (-(3 / 2 : ℝ)) := rfl
        calc K4_k k * M4 * (L ^ 2 * L ^ (-(3 / 2 : ℝ)) / L ^ k)
            ≤ K4_k k * M4 * (L * L ^ (-(3 / 2 : ℝ)) / L ^ k) := by
              gcongr; exact mul_nonneg (hbs4.K_nonneg k) hM4
          _ = K4_k k * ((M4 / uctAlphaFl) * (L * uctIfl L)) / L ^ k := by
              rw [hifl]; field_simp [hαfl.ne']
      · have h0 : ∀ x > 6 * δ, p4 x = 0 := fun x hx => by
          have hx6 : 1 ≤ x / (6 * δ) := by rw [le_div_iff₀ (by positivity)]; linarith only [hx]
          rw [hp4 x, hχ1 _ hx6, sub_self, zero_mul, mul_zero, mul_zero]
        rw [iteratedDeriv_eq_zero_of_eqOn_Ioi hbs4.smooth h0 k L hge, abs_zero]
        exact div_nonneg (mul_nonneg (hbs4.K_nonneg k) hMloc4) (pow_nonneg hL_pos.le k)) (hbs4.profile hM4)
  have hlam4 : bumpLambda (-(1 / 2)) δ ≤ 2 := by
    unfold bumpLambda; rw [ite_eq_right (by norm_num)]
    linarith only [Real.rpow_le_one hδ0.le hδ1 (by norm_num : 0 ≤ 1 - (-(1 / 2 : ℝ)))]
  have hc2_52 : (c ^ 2)⁻¹ * δ ≤ a₁ * c ^ (-(5 / 2 : ℝ)) := by
    have hc212 : (c ^ 2)⁻¹ * c ^ (-(1 / 2 : ℝ)) = c ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast c 2, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
    calc (c ^ 2)⁻¹ * δ ≤ (c ^ 2)⁻¹ * (a₁ * c ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hδ_hi (by positivity)
      _ = a₁ * c ^ (-(5 / 2 : ℝ)) := by linear_combination a₁ * hc212
  have hfac_nn : 0 ≤ c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hc0.le) hIfl_nn) (by positivity)
  have ht1 : Cloc4 * Mloc4 * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹) ≤
      (Cloc4 * (M4 / uctAlphaFl)) * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ))) := by
    dsimp only [Mloc4]; split_ifs
    · have heq : (L * uctIfl L) * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹) =
          c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) := by
        rw [mac_rpow_neg_two hc0, mac_rpow_neg_two hL_pos]; field_simp [hL_pos.ne', hc0.ne']
      exact le_of_eq <| calc Cloc4 * (M4 / uctAlphaFl * (L * uctIfl L)) * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹)
          = Cloc4 * (M4 / uctAlphaFl) * ((L * uctIfl L) * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹)) := by ring
        _ = Cloc4 * (M4 / uctAlphaFl) * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ))) := by rw [heq]
    · rw [mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg hCloc4 (div_nonneg hM4 hαfl.le)) hfac_nn
  have ht2 : Cloc4 * M4 * bumpLambda (-(1 / 2)) δ * ((c ^ 2)⁻¹ * δ) ≤ (Cloc4 * M4 * 2 * a₁) * c ^ (-(5 / 2 : ℝ)) :=
    calc Cloc4 * M4 * bumpLambda (-(1 / 2)) δ * ((c ^ 2)⁻¹ * δ)
        ≤ Cloc4 * M4 * 2 * (a₁ * c ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlam4 (mul_nonneg hCloc4 hM4)) hc2_52 (by positivity) (by positivity)
      _ = (Cloc4 * M4 * 2 * a₁) * c ^ (-(5 / 2 : ℝ)) := by ring
  calc ‖bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)‖
      ≤ Cloc4 * Mloc4 * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹) +
          Cloc4 * M4 * bumpLambda (-(1 / 2)) δ * ((c ^ 2)⁻¹ * δ) := hloc
    _ ≤ (Cloc4 * (M4 / uctAlphaFl)) * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ))) +
          (Cloc4 * M4 * 2 * a₁) * c ^ (-(5 / 2 : ℝ)) := add_le_add ht1 ht2
    _ ≤ C_mac / 4 * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ))) + C_mac / 4 * c ^ (-(5 / 2 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_right hc1m hfac_nn) (mul_le_mul_of_nonneg_right hc2m (Real.rpow_nonneg hc0.le _))
    _ = C_mac / 4 * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) + c ^ (-(5 / 2 : ℝ))) := by ring

private lemma mac_p2_bound {a₀ a₁ M2_0 Cloc2 δ c ξ K1 : ℝ} {K2_k : ℕ → ℝ} {p2 : ℝ → ℝ}
    (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hM2 : 0 ≤ M2_0) (hCloc2 : 0 ≤ Cloc2)
    (hαfl : 0 < uctAlphaFl) (hK1 : 0 ≤ K1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδ32 : 3 / 2 * δ ≤ 1)
    (hsqrt_δ : a₀ ≤ Real.sqrt c * δ) (hδ_lo : a₀ * c ^ (-(1 / 2 : ℝ)) ≤ δ) (hδ_hi : δ ≤ a₁ * c ^ (-(1 / 2 : ℝ)))
    (hc2 : 2 ≤ c) (hξ : 0 < ξ) (hL_lo : 3 * δ ≤ Real.log (Real.pi ^ 2 * ξ))
    (hbs2 : BSym δ (M2_0 * K1 * c ^ (-2 : ℝ)) (7 / 2) (7 / 2) K2_k p2)
    (hloc2 : BumpLocalFn (3 / 2) (7 / 2) (7 / 2) K2_k a₀ Cloc2) :
    ‖bumpHmain c p2 ξ - ((c⁻¹ * p2 (Real.log (Real.pi ^ 2 * ξ)) : ℝ) : ℂ)‖ ≤
      (Cloc2 * (M2_0 / uctAlphaFl) * ((3 * a₀)⁻¹ + (3 * a₀) ^ (-3 : ℝ))) * c ^ (-(1 / 2 : ℝ)) *
          (c⁻¹ * (K1 * c⁻¹ ^ 2 * (Real.log (Real.pi ^ 2 * ξ)) ^ (-2 : ℝ)) * uctIfl (Real.log (Real.pi ^ 2 * ξ))) +
      (Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ) := by
  have hc0 : 0 < c := by linarith only [hc2]
  have hc1 : 1 ≤ c := by linarith only [hc2]
  set L := Real.log (Real.pi ^ 2 * ξ)
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_lo
  have hIfl_nn : 0 ≤ uctIfl L := (uctIfl_pos' hL_pos).le
  have hL32 : 3 / 2 * δ ≤ L := by linarith only [hL_lo, hδ0]
  have hL32_lo : 3 / 2 * δ / 2 ≤ L := by linarith only [hL_lo, hδ0]
  have hM2c : 0 ≤ M2_0 * K1 * c ^ (-2 : ℝ) := by positivity
  set Mloc2 : ℝ := (M2_0 / uctAlphaFl) * K1 * c ^ (-2 : ℝ) * L ^ (-2 : ℝ) * uctIfl L
  have hMloc2 : 0 ≤ Mloc2 := by
    dsimp only [Mloc2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hM2 hαfl.le) hK1) (by positivity)) (by positivity)) hIfl_nn
  have hloc := hloc2 p2 δ (M2_0 * K1 * c ^ (-2 : ℝ)) Mloc2 c ξ hδ0 hδ1 hδ32 hM2c hMloc2 hc2 hsqrt_δ hξ hL32_lo
    (fun k _ _ => by
      have hbd := hbs2.bound k L hL32; simp only [min_self] at hbd
      refine hbd.trans_eq ?_
      have hL72 : L ^ (-(7 / 2 : ℝ) - (k : ℝ)) = (L ^ (-2 : ℝ) * L ^ (-(3 / 2 : ℝ))) / L ^ k := by
        rw [mac_rpow_neg_nat hL_pos (7 / 2) k, ← Real.rpow_add hL_pos]; congr 2; ring
      rw [hL72]
      have hifl : uctIfl L = uctAlphaFl * L ^ (-(3 / 2 : ℝ)) := rfl
      dsimp only [Mloc2]; rw [hifl]; dsimp only [L]; field_simp [hαfl.ne', hL_pos.ne']) (hbs2.profile hM2c)
  have hlam2 : bumpLambda (7 / 2) δ ≤ (1 + a₀ ^ (-(5 / 2 : ℝ))) * c ^ (5 / 4 : ℝ) := by
    unfold bumpLambda; rw [ite_eq_right (by norm_num)]
    have hc54 : 1 ≤ c ^ (5 / 4 : ℝ) := Real.one_le_rpow hc1 (by norm_num)
    have hδ52 : δ ^ (1 - (7 / 2 : ℝ)) ≤ a₀ ^ (-(5 / 2 : ℝ)) * c ^ (5 / 4 : ℝ) := by
      have h1 : δ ^ (-(5 / 2 : ℝ)) ≤ (a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hδ_lo (by norm_num)
      rw [show 1 - (7 / 2 : ℝ) = -(5 / 2 : ℝ) by norm_num]; refine h1.trans_eq ?_
      rw [Real.mul_rpow ha₀.le (by positivity), ← Real.rpow_mul hc0.le]; norm_num
    nlinarith only [hc54, hδ52]
  have ht1 : Cloc2 * Mloc2 * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹) ≤
      (Cloc2 * (M2_0 / uctAlphaFl) * ((3 * a₀)⁻¹ + (3 * a₀) ^ (-3 : ℝ))) * c ^ (-(1 / 2 : ℝ)) *
        (c⁻¹ * (K1 * c⁻¹ ^ 2 * L ^ (-2 : ℝ)) * uctIfl L) := by
    have hc112 : c ^ (-(3 / 2 : ℝ)) = c ^ (-(1 / 2 : ℝ)) * c⁻¹ := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
    have hcinv2 : c ^ (-2 : ℝ) = c⁻¹ ^ 2 := by rw [mac_rpow_neg_two hc0, inv_pow]
    dsimp only [Mloc2]
    calc Cloc2 * ((M2_0 / uctAlphaFl) * K1 * c ^ (-2 : ℝ) * L ^ (-2 : ℝ) * uctIfl L) *
            ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹)
        ≤ Cloc2 * ((M2_0 / uctAlphaFl) * K1 * c ^ (-2 : ℝ) * L ^ (-2 : ℝ) * uctIfl L) *
            (((3 * a₀)⁻¹ + (3 * a₀) ^ (-3 : ℝ)) * c ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mac_inv_bound3 ha₀ hc0 hδ_lo hL_lo) (mul_nonneg hCloc2 hMloc2)
      _ = _ := by rw [hc112, hcinv2]; ring
  have ht2 : Cloc2 * (M2_0 * K1 * c ^ (-2 : ℝ)) * bumpLambda (7 / 2) δ * ((c ^ 2)⁻¹ * δ) ≤
      (Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ) := by
    have hc_ex : c ^ (-2 : ℝ) * c ^ (5 / 4 : ℝ) * ((c ^ 2)⁻¹ * c ^ (-(1 / 2 : ℝ))) ≤ c ^ (-3 : ℝ) := by
      rw [mac_rpow_neg_two hc0, ← Real.rpow_natCast c 2, ← Real.rpow_neg hc0.le,
        ← Real.rpow_add hc0, ← Real.rpow_add hc0, ← Real.rpow_add hc0]
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc Cloc2 * (M2_0 * K1 * c ^ (-2 : ℝ)) * bumpLambda (7 / 2) δ * ((c ^ 2)⁻¹ * δ)
        ≤ Cloc2 * (M2_0 * K1 * c ^ (-2 : ℝ)) * ((1 + a₀ ^ (-(5 / 2 : ℝ))) * c ^ (5 / 4 : ℝ)) *
            ((c ^ 2)⁻¹ * (a₁ * c ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlam2 (by positivity))
            (mul_le_mul_of_nonneg_left hδ_hi (by positivity)) (by positivity) (by positivity)
      _ = (Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1) *
            (c ^ (-2 : ℝ) * c ^ (5 / 4 : ℝ) * ((c ^ 2)⁻¹ * c ^ (-(1 / 2 : ℝ)))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc_ex (by positivity)
  exact hloc.trans (add_le_add ht1 ht2)

private lemma mac_p3_bound {a₀ a₁ M3_0 Cloc3 δ c ξ K1 : ℝ} {K3_k : ℕ → ℝ} {p3 : ℝ → ℝ}
    (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hM3 : 0 ≤ M3_0) (hCloc3 : 0 ≤ Cloc3)
    (hαfl : 0 < uctAlphaFl) (hK1 : 0 ≤ K1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδ32 : 3 / 2 * δ ≤ 1)
    (hsqrt_δ : a₀ ≤ Real.sqrt c * δ) (hδ_lo : a₀ * c ^ (-(1 / 2 : ℝ)) ≤ δ) (hδ_hi : δ ≤ a₁ * c ^ (-(1 / 2 : ℝ)))
    (hc2 : 2 ≤ c) (hξ : 0 < ξ) (hL_lo : 3 * δ ≤ Real.log (Real.pi ^ 2 * ξ))
    (hbs3 : BSym δ (M3_0 * K1 * c⁻¹) (3 / 2) (3 / 2) K3_k p3)
    (hloc3 : BumpLocalFn (3 / 2) (3 / 2) (3 / 2) K3_k a₀ Cloc3) :
    ‖bumpHmain c p3 ξ - ((c⁻¹ * p3 (Real.log (Real.pi ^ 2 * ξ)) : ℝ) : ℂ)‖ ≤
      (Cloc3 * (M3_0 / uctAlphaFl) * ((3 * a₀)⁻¹ + (3 * a₀) ^ (-3 : ℝ))) * c ^ (-(1 / 2 : ℝ)) *
          (c⁻¹ * (K1 * c⁻¹) * uctIfl (Real.log (Real.pi ^ 2 * ξ))) +
      (Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ) := by
  have hc0 : 0 < c := by linarith only [hc2]
  have hc1 : 1 ≤ c := by linarith only [hc2]
  set L := Real.log (Real.pi ^ 2 * ξ)
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_lo
  have hIfl_nn : 0 ≤ uctIfl L := (uctIfl_pos' hL_pos).le
  have hL32 : 3 / 2 * δ ≤ L := by linarith only [hL_lo, hδ0]
  have hL32_lo : 3 / 2 * δ / 2 ≤ L := by linarith only [hL_lo, hδ0]
  have hM3c : 0 ≤ M3_0 * K1 * c⁻¹ := by positivity
  set Mloc3 : ℝ := (M3_0 / uctAlphaFl) * K1 * c⁻¹ * uctIfl L
  have hMloc3 : 0 ≤ Mloc3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hM3 hαfl.le) hK1) (inv_nonneg.mpr hc0.le)) hIfl_nn
  have hloc := hloc3 p3 δ (M3_0 * K1 * c⁻¹) Mloc3 c ξ hδ0 hδ1 hδ32 hM3c hMloc3 hc2 hsqrt_δ hξ hL32_lo
    (fun k _ _ => by
      have hbd := hbs3.bound k L hL32; simp only [min_self] at hbd
      refine hbd.trans_eq ?_
      rw [mac_rpow_neg_nat hL_pos (3 / 2) k]
      have hifl : uctIfl L = uctAlphaFl * L ^ (-(3 / 2 : ℝ)) := rfl
      dsimp only [Mloc3]; rw [hifl]; dsimp only [L]; field_simp [hαfl.ne', hL_pos.ne']) (hbs3.profile hM3c)
  have hlam3 : bumpLambda (3 / 2) δ ≤ (1 + a₀ ^ (-(1 / 2 : ℝ))) * c ^ (1 / 4 : ℝ) := by
    unfold bumpLambda; rw [ite_eq_right (by norm_num)]
    have hc14 : 1 ≤ c ^ (1 / 4 : ℝ) := Real.one_le_rpow hc1 (by norm_num)
    have hδ12 : δ ^ (1 - (3 / 2 : ℝ)) ≤ a₀ ^ (-(1 / 2 : ℝ)) * c ^ (1 / 4 : ℝ) := by
      have h1 : δ ^ (-(1 / 2 : ℝ)) ≤ (a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hδ_lo (by norm_num)
      rw [show 1 - (3 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num]; refine h1.trans_eq ?_
      rw [Real.mul_rpow ha₀.le (by positivity), ← Real.rpow_mul hc0.le]; norm_num
    nlinarith only [hc14, hδ12]
  have ht1 : Cloc3 * Mloc3 * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹) ≤
      (Cloc3 * (M3_0 / uctAlphaFl) * ((3 * a₀)⁻¹ + (3 * a₀) ^ (-3 : ℝ))) * c ^ (-(1 / 2 : ℝ)) *
        (c⁻¹ * (K1 * c⁻¹) * uctIfl L) := by
    have hc112 : c ^ (-(3 / 2 : ℝ)) = c ^ (-(1 / 2 : ℝ)) * c⁻¹ := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
    dsimp only [Mloc3]
    calc Cloc3 * ((M3_0 / uctAlphaFl) * K1 * c⁻¹ * uctIfl L) * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹)
        ≤ Cloc3 * ((M3_0 / uctAlphaFl) * K1 * c⁻¹ * uctIfl L) *
            (((3 * a₀)⁻¹ + (3 * a₀) ^ (-3 : ℝ)) * c ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mac_inv_bound3 ha₀ hc0 hδ_lo hL_lo) (mul_nonneg hCloc3 hMloc3)
      _ = _ := by rw [hc112]; ring
  have ht2 : Cloc3 * (M3_0 * K1 * c⁻¹) * bumpLambda (3 / 2) δ * ((c ^ 2)⁻¹ * δ) ≤
      (Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ) := by
    have hc_ex : c⁻¹ * c ^ (1 / 4 : ℝ) * ((c ^ 2)⁻¹ * c ^ (-(1 / 2 : ℝ))) ≤ c ^ (-3 : ℝ) := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_natCast c 2, ← Real.rpow_neg hc0.le,
        ← Real.rpow_add hc0, ← Real.rpow_add hc0, ← Real.rpow_add hc0]
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc Cloc3 * (M3_0 * K1 * c⁻¹) * bumpLambda (3 / 2) δ * ((c ^ 2)⁻¹ * δ)
        ≤ Cloc3 * (M3_0 * K1 * c⁻¹) * ((1 + a₀ ^ (-(1 / 2 : ℝ))) * c ^ (1 / 4 : ℝ)) *
            ((c ^ 2)⁻¹ * (a₁ * c ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlam3 (by positivity))
            (mul_le_mul_of_nonneg_left hδ_hi (by positivity)) (by positivity) (by positivity)
      _ = (Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1) *
            (c⁻¹ * c ^ (1 / 4 : ℝ) * ((c ^ 2)⁻¹ * c ^ (-(1 / 2 : ℝ)))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc_ex (by positivity)
  exact hloc.trans (add_le_add ht1 ht2)

private lemma mac_refl_neg_three {C_r κ_r M_B0 M_BK K1 c ξ : ℝ} {B : ℝ → ℝ}
    (hCr0 : 0 ≤ C_r) (hκr0 : 0 < κ_r) (hMBK : 0 ≤ M_BK) (hK1 : 0 ≤ K1)
    (hM0 : 0 ≤ M_B0 + M_BK * K1 * c⁻¹) (hc1 : 1 ≤ c) (hc0 : 0 < c)
    (hr : ‖bumpHrefl c B ξ‖ ≤ C_r * (M_B0 + M_BK * K1 * c⁻¹) * Real.exp (-(κ_r * Real.sqrt c))) :
    ‖bumpHrefl c B ξ‖ ≤ C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * (M_B0 + M_BK * K1) * c ^ (-3 : ℝ) := by
  have hci : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
  have hMB_le : M_B0 + M_BK * K1 * c⁻¹ ≤ M_B0 + M_BK * K1 := by
    have hm : M_BK * K1 * c⁻¹ ≤ M_BK * K1 * 1 := mul_le_mul_of_nonneg_left hci (mul_nonneg hMBK hK1)
    linarith only [hm]
  have hc3_pos : 0 < c ^ 3 := by positivity
  have hr3 := mul_le_mul_of_nonneg_right hr hc3_pos.le
  have hMB_nn : 0 ≤ M_B0 + M_BK * K1 := le_trans hM0 hMB_le
  have hbd3 : ‖bumpHrefl c B ξ‖ * c ^ 3 ≤ C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * (M_B0 + M_BK * K1) := by
    calc ‖bumpHrefl c B ξ‖ * c ^ 3
        ≤ C_r * (M_B0 + M_BK * K1 * c⁻¹) * Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3 := hr3
      _ = (C_r * (M_B0 + M_BK * K1 * c⁻¹)) * (Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3) := by ring
      _ ≤ (C_r * (M_B0 + M_BK * K1)) * (Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB_le hCr0)
            (mul_nonneg (Real.exp_pos _).le hc3_pos.le)
      _ ≤ (C_r * (M_B0 + M_BK * K1)) * ((Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹) :=
          mul_le_mul_of_nonneg_left (exp_half_absorb hκr0 hc0) (mul_nonneg hCr0 hMB_nn)
      _ = _ := by ring
  rw [mac_rpow_neg_three hc0, le_mul_inv_iff₀ hc3_pos]
  exact hbd3

/-- **Regime 3 (`3 δ_L ≤ L ≤ (1/4) log c`)**: macroscopic lower bound absorbing `p2 + p3` symbol error
into half of `η (O + F)` and leaving only `O_{K₄}(c⁻¹ I_fl (c⁻¹ + c⁻² L⁻²) + c^{-5/2}) + c^{-5/2}`. -/
theorem physBump_mac_lower {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K4 : ℝ} (hK4 : 1 ≤ K4)
    {T1 alpha Nc : ℝ → ℝ → ℝ} (hwarp : FctWarpZeroStmt T1 alpha) (hNc : FctSplittingNormStmt Nc) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K1 : ℝ, 0 ≤ K1 → ∃ c₀ : ℝ, 2 ≤ c₀ ∧
      ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
        3 * physDelta c ≤ Real.log (Real.pi ^ 2 * ξ) →
        Real.log (Real.pi ^ 2 * ξ) ≤ 1 / 4 * Real.log c →
        c⁻¹ * (1 / Nc ε c) * physGamma c (physShift ε c) (Real.log (Real.pi ^ 2 * ξ)) *
            ((physOscDatum StripKernelChoice.star K4 T1 alpha ε c (Real.log (Real.pi ^ 2 * ξ)) -
              physF (physShift ε c) (physL1 T1 ε c) (Real.log (Real.pi ^ 2 * ξ))) +
             1 / 2 * physEta c K1 (Real.log (Real.pi ^ 2 * ξ)) *
              (physOscDatum StripKernelChoice.star K4 T1 alpha ε c (Real.log (Real.pi ^ 2 * ξ)) +
               physF (physShift ε c) (physL1 T1 ε c) (Real.log (Real.pi ^ 2 * ξ)))) -
          C * (c⁻¹ * uctIfl (Real.log (Real.pi ^ 2 * ξ)) *
            (c⁻¹ + c ^ (-2 : ℝ) * (Real.log (Real.pi ^ 2 * ξ)) ^ (-2 : ℝ)) + c ^ (-(5 / 2 : ℝ))) -
          c ^ (-(5 / 2 : ℝ)) ≤
          normDensity (ctWbump (physBump χ (1 / Nc ε c) c (physDelta c) (physShift ε c) K1 K4
            (physOscDatum StripKernelChoice.star K4 T1 alpha ε c)
            (physF (physShift ε c) (physL1 T1 ε c)) (fun L => tau0 L ^ 4 * uctIfl L)) ε c) c ξ := by
  obtain ⟨c_d, a₀, a₁, M1, M2_0, M3_0, M4, M_B0, M_BK, K1_k, K2_k, K3_k, K4_k, K_B,
    _, ha₀, ha₁, hM1, hM2, hM3, hM4, hMB0, hMBK, _, hdec⟩ := physBump_decomp hχ hK4 hwarp hNc
  obtain ⟨c_mac, _, hmac_pos⟩ := phys_mac_positivity hK4 hwarp
  obtain ⟨Cloc1, hCloc1, hloc1⟩ := bump_weighted_local (b := 3 / 2) (α := 1 / 2) (β := 3 / 2) (by norm_num) le_rfl K1_k K1_k ha₀
  obtain ⟨Cloc2, hCloc2, hloc2⟩ := bump_weighted_local (b := 3 / 2) (α := 7 / 2) (β := 7 / 2) (by norm_num) (by norm_num) K2_k K2_k ha₀
  obtain ⟨Cloc3, hCloc3, hloc3⟩ := bump_weighted_local (b := 3 / 2) (α := 3 / 2) (β := 3 / 2) (by norm_num) le_rfl K3_k K3_k ha₀
  obtain ⟨Cloc4, hCloc4, hloc4⟩ := bump_weighted_local (b := 3 / 2) (α := -(1 / 2)) (β := 3 / 2) (by norm_num) le_rfl K4_k K4_k ha₀
  obtain ⟨C_r, κ_r, hCr0, hκr0, hrefl⟩ := fct_bump5_refl (α := 7 / 2) (β := 3 / 2) le_rfl K_B ha₀
  have hαfl_pos : 0 < uctAlphaFl := by
    unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
  set K_L3 : ℝ := (3 * a₀)⁻¹ + (3 * a₀) ^ (-3 : ℝ)
  have hKL3_nn : 0 ≤ K_L3 := add_nonneg (inv_nonneg.mpr (by linarith only [ha₀])) (Real.rpow_nonneg (by linarith only [ha₀]) _)
  set C_p23 : ℝ := 2 * (Cloc2 * (M2_0 / uctAlphaFl) + Cloc3 * (M3_0 / uctAlphaFl)) * K_L3
  have hCp23_nn : 0 ≤ C_p23 := by
    dsimp only [C_p23]
    exact mul_nonneg (mul_nonneg zero_le_two (add_nonneg (mul_nonneg hCloc2 (div_nonneg hM2 hαfl_pos.le))
      (mul_nonneg hCloc3 (div_nonneg hM3 hαfl_pos.le)))) hKL3_nn
  set C_mac : ℝ := 4 * max (max (Cloc1 * (M1 / uctAlphaFl)) (Cloc4 * (M4 / uctAlphaFl)))
    (max (Cloc1 * M1 * 2 * a₁) (Cloc4 * M4 * 2 * a₁))
  have hCmac_nn : 0 ≤ C_mac := by
    dsimp only [C_mac]
    exact mul_nonneg (by norm_num) (le_max_of_le_left (le_max_of_le_left (mul_nonneg hCloc1 (div_nonneg hM1 hαfl_pos.le))))
  refine ⟨C_mac, hCmac_nn, fun K1 hK1 => ?_⟩
  set c_abs23 : ℝ := (32 * C_p23 + 1) ^ 2
  set E_lamK1 : ℝ := 2 * (Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1 +
    Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1) +
    C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * (M_B0 + M_BK * K1)
  have hElam_nn : 0 ≤ E_lamK1 := by dsimp only [E_lamK1]; positivity
  set c_lam : ℝ := (E_lamK1 + 1) ^ 2
  set c_r1 : ℝ := (1 / a₀ + 1) ^ 2
  set c₀ : ℝ := max (max (max c_d c_mac) (max c_abs23 c_lam)) (max c_r1 2)
  refine ⟨c₀, le_max_of_le_right (le_max_right _ _), fun ε c ξ hε hc hξ hL_lo _ => ?_⟩
  simp only [c₀, max_le_iff] at hc
  obtain ⟨⟨⟨hcd', hcmac'⟩, ⟨hc23', hclam'⟩⟩, ⟨hcr1', hc2⟩⟩ := hc
  have hc0 : 0 < c := by linarith only [hc2]
  have hc1 : 1 ≤ c := by linarith only [hc2]
  set δ := physDelta c
  set s := physShift ε c
  set L1 := physL1 T1 ε c
  set n := 1 / Nc ε c
  set F := physF s L1
  set O := physOscDatum StripKernelChoice.star K4 T1 alpha ε c
  set T4 : ℝ → ℝ := fun L => tau0 L ^ 4 * uctIfl L
  set R : ℝ → ℝ := fun x => O x / F x
  set p1 : ℝ → ℝ := fun x => χ (x / (3 * δ)) * physGamma c s x * (F x * R x - F x)
  set p2 : ℝ → ℝ := fun x => χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) * (F x * R x + F x))
  set p3 : ℝ → ℝ := fun x => χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ * (F x * R x + F x))
  set p4 : ℝ → ℝ := fun x => 2 * K4 * (χ (x / (3 * δ)) * ((1 - χ (x / (6 * δ))) * T4 x))
  set B := physBump χ n c δ s K1 K4 O F T4
  obtain ⟨⟨hδ_lo, hδ_hi, hsqrt_δ, hδ0, hδ1', hδ32, h6δ, hn_lo, hn_hi, hs_le, hL1_le⟩, hBeq,
    hbs1, hbs2, hbs3, hbs4, hp4_nn, _, hprof⟩ := hdec K1 ε c hK1 hε hcd'
  set L := Real.log (Real.pi ^ 2 * ξ)
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_lo
  have hIfl_nn : 0 ≤ uctIfl L := (uctIfl_pos' hL_pos).le
  have hL32 : 3 / 2 * δ ≤ L := by linarith only [hL_lo, hδ0]
  obtain ⟨hO_nn, hF_lo, hγ_half, _⟩ := hmac_pos ε c L hε hcmac' hL_lo
  have hC1m : Cloc1 * (M1 / uctAlphaFl) ≤ C_mac / 4 := by
    dsimp only [C_mac]; linarith only [le_max_left (Cloc1 * (M1 / uctAlphaFl)) (Cloc4 * (M4 / uctAlphaFl)),
      le_max_left (max (Cloc1 * (M1 / uctAlphaFl)) (Cloc4 * (M4 / uctAlphaFl)))
        (max (Cloc1 * M1 * 2 * a₁) (Cloc4 * M4 * 2 * a₁))]
  have hC1a : Cloc1 * M1 * 2 * a₁ ≤ C_mac / 4 := by
    dsimp only [C_mac]; linarith only [le_max_left (Cloc1 * M1 * 2 * a₁) (Cloc4 * M4 * 2 * a₁),
      le_max_right (max (Cloc1 * (M1 / uctAlphaFl)) (Cloc4 * (M4 / uctAlphaFl)))
        (max (Cloc1 * M1 * 2 * a₁) (Cloc4 * M4 * 2 * a₁))]
  have hC4m : Cloc4 * (M4 / uctAlphaFl) ≤ C_mac / 4 := by
    dsimp only [C_mac]; linarith only [le_max_right (Cloc1 * (M1 / uctAlphaFl)) (Cloc4 * (M4 / uctAlphaFl)),
      le_max_left (max (Cloc1 * (M1 / uctAlphaFl)) (Cloc4 * (M4 / uctAlphaFl)))
        (max (Cloc1 * M1 * 2 * a₁) (Cloc4 * M4 * 2 * a₁))]
  have hC4a : Cloc4 * M4 * 2 * a₁ ≤ C_mac / 4 := by
    dsimp only [C_mac]; linarith only [le_max_right (Cloc1 * M1 * 2 * a₁) (Cloc4 * M4 * 2 * a₁),
      le_max_right (max (Cloc1 * (M1 / uctAlphaFl)) (Cloc4 * (M4 / uctAlphaFl)))
        (max (Cloc1 * M1 * 2 * a₁) (Cloc4 * M4 * 2 * a₁))]
  have hp1_bd := mac_p1_bound ha₀ ha₁ hM1 hCloc1 hαfl_pos hδ0 hδ1' hδ32 hsqrt_δ hδ_hi hc2 hξ hL_lo hC1m hC1a hbs1 hloc1
  have hp4_bd := mac_p4_bound hχ.one (fun _ => rfl) ha₀ ha₁ hM4 hCloc4 hαfl_pos hδ0 hδ1' hδ32 h6δ hsqrt_δ hδ_hi hc2 hξ hL_lo hC4m hC4a hbs4 hloc4
  have hp2_bd := mac_p2_bound ha₀ ha₁ hM2 hCloc2 hαfl_pos hK1 hδ0 hδ1' hδ32 hsqrt_δ hδ_lo hδ_hi hc2 hξ hL_lo hbs2 hloc2
  have hp3_bd := mac_p3_bound ha₀ ha₁ hM3 hCloc3 hαfl_pos hK1 hδ0 hδ1' hδ32 hsqrt_δ hδ_lo hδ_hi hc2 hξ hL_lo hbs3 hloc3
  have hM0' : 0 ≤ M_B0 + M_BK * K1 * c⁻¹ := by positivity
  have ha0_sq : 1 ≤ a₀ * Real.sqrt c := by
    have h1 : 1 / a₀ + 1 ≤ Real.sqrt c := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / a₀ + 1)]; exact Real.sqrt_le_sqrt hcr1'
    have h2 : 1 ≤ a₀ * (1 / a₀ + 1) := by field_simp; linarith only [ha₀]
    calc 1 ≤ a₀ * (1 / a₀ + 1) := h2
      _ ≤ a₀ * Real.sqrt c := mul_le_mul_of_nonneg_left h1 ha₀.le
  have hrefl_bd := mac_refl_neg_three hCr0 hκr0 hMBK hK1 hM0' hc1 hc0
    (hrefl B δ (M_B0 + M_BK * K1 * c⁻¹) c ξ hδ0 hδ1' hδ32 hM0' hc2 ha0_sq hsqrt_δ hξ hprof).1
  have hmain_eq : bumpHmain c B ξ =
      (n : ℂ) * (bumpHmain c p1 ξ + bumpHmain c p2 ξ + bumpHmain c p3 ξ + bumpHmain c p4 ξ) := by
    change bumpHmain c (physBump χ n c δ s K1 K4 O F T4) ξ = _
    rw [hBeq]
    exact bumpHmain_lin4 hc1 hδ0 hδ32 le_rfl (by norm_num) le_rfl le_rfl
      hM1 (by positivity) (by positivity) hM4 hξ
      (hbs1.profile hM1) (hbs2.profile (by positivity)) (hbs3.profile (by positivity)) (hbs4.profile hM4)
  have hχ1 : χ (L / (3 * δ)) = 1 := hχ.one _ (by rw [le_div_iff₀ (by positivity)]; linarith only [hL_lo])
  have hBL_main : n * (c⁻¹ * p1 L + c⁻¹ * p2 L + c⁻¹ * p3 L) =
      c⁻¹ * n * physGamma c s L * ((O L - F L) + physEta c K1 L * (O L + F L)) := by
    have hFpos := physF_pos (by positivity : 0 < 3 / 2 * δ) hs_le hL1_le hL32
    dsimp only [p1, p2, p3, R]; rw [hχ1, mul_div_cancel₀ _ hFpos.ne']; unfold physEta; ring
  have hc23_absorb : C_p23 * c ^ (-(1 / 2 : ℝ)) ≤ 1 / 32 := by
    have h1 : 32 * C_p23 + 1 ≤ Real.sqrt c := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 32 * C_p23 + 1)]; exact Real.sqrt_le_sqrt hc23'
    rw [Real.sqrt_eq_rpow] at h1
    rw [Real.rpow_neg hc0.le (1 / 2)]
    have h3 : (c ^ (1 / 2 : ℝ))⁻¹ ≤ (32 * C_p23 + 1)⁻¹ := inv_anti₀ (by positivity) h1
    have hrat : C_p23 * (32 * C_p23 + 1)⁻¹ ≤ 1 / 32 := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith only [hCp23_nn]
    calc C_p23 * (c ^ (1 / 2 : ℝ))⁻¹ ≤ C_p23 * (32 * C_p23 + 1)⁻¹ := mul_le_mul_of_nonneg_left h3 hCp23_nn
      _ ≤ 1 / 32 := hrat
  have hlam_absorb : E_lamK1 * c ^ (-3 : ℝ) ≤ c ^ (-(5 / 2 : ℝ)) := by
    have h1 : E_lamK1 + 1 ≤ Real.sqrt c := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ E_lamK1 + 1)]; exact Real.sqrt_le_sqrt hclam'
    rw [Real.sqrt_eq_rpow] at h1
    have h2 : c ^ (-(1 / 2 : ℝ)) ≤ (E_lamK1 + 1)⁻¹ := by
      rw [Real.rpow_neg hc0.le (1 / 2)]; exact inv_anti₀ (by positivity) h1
    have h3 : E_lamK1 * c ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      have : E_lamK1 * (E_lamK1 + 1)⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one (by positivity)]; linarith only [hElam_nn]
      calc E_lamK1 * c ^ (-(1 / 2 : ℝ)) ≤ E_lamK1 * (E_lamK1 + 1)⁻¹ := mul_le_mul_of_nonneg_left h2 hElam_nn
        _ ≤ 1 := this
    have hc352 : c ^ (-3 : ℝ) = c ^ (-(1 / 2 : ℝ)) * c ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    rw [hc352, ← mul_assoc]
    calc E_lamK1 * c ^ (-(1 / 2 : ℝ)) * c ^ (-(5 / 2 : ℝ)) ≤ 1 * c ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hc0.le _)
      _ = c ^ (-(5 / 2 : ℝ)) := one_mul _
  have hre_diff : (bumpHmain c B ξ).re - c⁻¹ * n * physGamma c s L * ((O L - F L) + physEta c K1 L * (O L + F L)) =
      n * ((bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re + (bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re +
        (bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re + (bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re) +
      n * c⁻¹ * p4 L := by
    rw [hmain_eq, ← hBL_main]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.sub_re,
      zero_mul, sub_zero]
    ring
  have hn_pos : 0 ≤ n := by linarith only [hn_lo]
  have hp4_term_nn : 0 ≤ n * c⁻¹ * p4 L := mul_nonneg (mul_nonneg hn_pos (inv_nonneg.mpr hc0.le)) (hp4_nn L)
  have hη_bound : 2 * ((Cloc2 * (M2_0 / uctAlphaFl) * K_L3) * c ^ (-(1 / 2 : ℝ)) * (c⁻¹ * (K1 * c⁻¹ ^ 2 * L ^ (-2 : ℝ)) * uctIfl L) +
      (Cloc3 * (M3_0 / uctAlphaFl) * K_L3) * c ^ (-(1 / 2 : ℝ)) * (c⁻¹ * (K1 * c⁻¹) * uctIfl L)) ≤
      c⁻¹ * n * physGamma c s L * (1 / 2 * physEta c K1 L * (O L + F L)) := by
    have hη_eq : K1 * c⁻¹ ^ 2 * L ^ (-2 : ℝ) + K1 * c⁻¹ = physEta c K1 L := by unfold physEta; ring
    set t2 := c⁻¹ * (K1 * c⁻¹ ^ 2 * L ^ (-2 : ℝ)) * uctIfl L
    set t3 := c⁻¹ * (K1 * c⁻¹) * uctIfl L
    have ht2_nn : 0 ≤ t2 := mul_nonneg (mul_nonneg (inv_nonneg.mpr hc0.le) (by positivity)) hIfl_nn
    have ht3_nn : 0 ≤ t3 := mul_nonneg (mul_nonneg (inv_nonneg.mpr hc0.le) (by positivity)) hIfl_nn
    set A2 := Cloc2 * (M2_0 / uctAlphaFl) * K_L3
    set A3 := Cloc3 * (M3_0 / uctAlphaFl) * K_L3
    have hA2_nn : 0 ≤ A2 := mul_nonneg (mul_nonneg hCloc2 (div_nonneg hM2 hαfl_pos.le)) hKL3_nn
    have hA3_nn : 0 ≤ A3 := mul_nonneg (mul_nonneg hCloc3 (div_nonneg hM3 hαfl_pos.le)) hKL3_nn
    have hsumA : A2 + A3 = C_p23 / 2 := by dsimp only [A2, A3, C_p23]; ring
    have hc12_nn : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hle1 : 2 * (A2 * c ^ (-(1 / 2 : ℝ)) * t2 + A3 * c ^ (-(1 / 2 : ℝ)) * t3) ≤
        C_p23 * c ^ (-(1 / 2 : ℝ)) * (c⁻¹ * physEta c K1 L * uctIfl L) := by
      have hs : t2 + t3 = c⁻¹ * physEta c K1 L * uctIfl L := by dsimp only [t2, t3]; rw [← hη_eq]; ring
      have h1 : A2 * c ^ (-(1 / 2 : ℝ)) * t2 ≤ (A2 + A3) * c ^ (-(1 / 2 : ℝ)) * t2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hA3_nn]) hc12_nn) ht2_nn
      have h2 : A3 * c ^ (-(1 / 2 : ℝ)) * t3 ≤ (A2 + A3) * c ^ (-(1 / 2 : ℝ)) * t3 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hA2_nn]) hc12_nn) ht3_nn
      calc 2 * (A2 * c ^ (-(1 / 2 : ℝ)) * t2 + A3 * c ^ (-(1 / 2 : ℝ)) * t3)
          ≤ 2 * ((A2 + A3) * c ^ (-(1 / 2 : ℝ)) * t2 + (A2 + A3) * c ^ (-(1 / 2 : ℝ)) * t3) := by linarith only [h1, h2]
        _ = (2 * (A2 + A3)) * c ^ (-(1 / 2 : ℝ)) * (t2 + t3) := by ring
        _ = C_p23 * c ^ (-(1 / 2 : ℝ)) * (c⁻¹ * physEta c K1 L * uctIfl L) := by rw [hsumA, hs]; ring
    have hη_nn : 0 ≤ physEta c K1 L := by unfold physEta; positivity
    have hOF_lo : 1 / 4 * uctIfl L ≤ O L + F L := by linarith only [hO_nn, hF_lo]
    have h_low : 1 / 32 * (c⁻¹ * physEta c K1 L * uctIfl L) ≤
        c⁻¹ * n * physGamma c s L * (1 / 2 * physEta c K1 L * (O L + F L)) := by
      have hmid : c⁻¹ * (1 / 2) * (1 / 2) * (1 / 2 * physEta c K1 L * (1 / 4 * uctIfl L)) ≤
          c⁻¹ * n * physGamma c s L * (1 / 2 * physEta c K1 L * (O L + F L)) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hn_lo (inv_nonneg.mpr hc0.le))
          hγ_half (by norm_num) (by positivity))
          (mul_le_mul_of_nonneg_left hOF_lo (by positivity)) (by positivity) (by positivity)
      linarith only [hmid]
    exact hle1.trans ((mul_le_mul_of_nonneg_right hc23_absorb
      (mul_nonneg (mul_nonneg (inv_nonneg.mpr hc0.le) hη_nn) hIfl_nn)).trans h_low)
  have hre1 := (abs_le.mp (le_refl |(bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re|)).1
  have hre2 := (abs_le.mp (le_refl |(bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re|)).1
  have hre3 := (abs_le.mp (le_refl |(bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re|)).1
  have hre4 := (abs_le.mp (le_refl |(bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re|)).1
  have href_re := (abs_le.mp (le_refl |((ε : ℂ) * bumpHrefl c B ξ).re|)).1
  have href_abs : |((ε : ℂ) * bumpHrefl c B ξ).re| ≤
      C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * (M_B0 + M_BK * K1) * c ^ (-3 : ℝ) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rcases hε with rfl | rfl
    · simp only [abs_one, one_mul]; exact hrefl_bd
    · simp only [abs_neg, abs_one, one_mul]; exact hrefl_bd
  have a1 := (Complex.abs_re_le_norm _).trans hp1_bd
  have a2 := (Complex.abs_re_le_norm _).trans hp2_bd
  have a3 := (Complex.abs_re_le_norm _).trans hp3_bd
  have a4 := (Complex.abs_re_le_norm _).trans hp4_bd
  have hcomb_14 : n * (|(bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re| +
        |(bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re|) ≤
      C_mac * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) + c ^ (-(5 / 2 : ℝ))) := by
    calc n * (|(bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re| + |(bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re|)
        ≤ 2 * (C_mac / 4 * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) + c ^ (-(5 / 2 : ℝ))) +
            C_mac / 4 * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) + c ^ (-(5 / 2 : ℝ)))) :=
          mul_le_mul hn_hi (add_le_add a1 a4) (add_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_two
      _ = C_mac * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) + c ^ (-(5 / 2 : ℝ))) := by ring
  have hcomb_lam : n * ((Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ) +
        (Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ)) + |((ε : ℂ) * bumpHrefl c B ξ).re| ≤
      E_lamK1 * c ^ (-3 : ℝ) := by
    have hp2_nn : 0 ≤ (Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCloc2 hM2) (by positivity)) ha₁.le) hK1) (by positivity)
    have hp3_nn : 0 ≤ (Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCloc3 hM3) (by positivity)) ha₁.le) hK1) (by positivity)
    calc _ ≤ 2 * ((Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ) +
            (Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ)) +
            C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * (M_B0 + M_BK * K1) * c ^ (-3 : ℝ) :=
          add_le_add (mul_le_mul hn_hi le_rfl (add_nonneg hp2_nn hp3_nn) zero_le_two) href_abs
      _ = E_lamK1 * c ^ (-3 : ℝ) := by dsimp only [E_lamK1]; ring
  have hcomb_p23 : n * (|(bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re| +
        |(bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re|) ≤
      c⁻¹ * n * physGamma c s L * (1 / 2 * physEta c K1 L * (O L + F L)) +
      n * ((Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ) +
        (Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1) * c ^ (-3 : ℝ)) := by
    have hs23 := mul_le_mul_of_nonneg_left (add_le_add a2 a3) hn_pos
    have hη_term_nn : 0 ≤ (Cloc2 * (M2_0 / uctAlphaFl) * K_L3) * c ^ (-(1 / 2 : ℝ)) *
          (c⁻¹ * (K1 * c⁻¹ ^ 2 * L ^ (-2 : ℝ)) * uctIfl L) +
        (Cloc3 * (M3_0 / uctAlphaFl) * K_L3) * c ^ (-(1 / 2 : ℝ)) * (c⁻¹ * (K1 * c⁻¹) * uctIfl L) :=
      add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCloc2 (div_nonneg hM2 hαfl_pos.le)) hKL3_nn)
        (Real.rpow_nonneg hc0.le _)) (mul_nonneg (mul_nonneg (inv_nonneg.mpr hc0.le) (by positivity)) hIfl_nn))
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCloc3 (div_nonneg hM3 hαfl_pos.le)) hKL3_nn)
        (Real.rpow_nonneg hc0.le _)) (mul_nonneg (mul_nonneg (inv_nonneg.mpr hc0.le) (by positivity)) hIfl_nn))
    have h2 : n * ((Cloc2 * (M2_0 / uctAlphaFl) * K_L3) * c ^ (-(1 / 2 : ℝ)) * (c⁻¹ * (K1 * c⁻¹ ^ 2 * L ^ (-2 : ℝ)) * uctIfl L) +
        (Cloc3 * (M3_0 / uctAlphaFl) * K_L3) * c ^ (-(1 / 2 : ℝ)) * (c⁻¹ * (K1 * c⁻¹) * uctIfl L)) ≤
        c⁻¹ * n * physGamma c s L * (1 / 2 * physEta c K1 L * (O L + F L)) :=
      (mul_le_mul_of_nonneg_right hn_hi hη_term_nn).trans hη_bound
    linarith only [hs23, h2]
  have hn_abs : -(n * (|(bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re| + |(bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re|) +
        n * (|(bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re| + |(bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re|)) ≤
      n * ((bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re + (bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re +
        (bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re + (bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re) := by
    have hs : -(|(bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re| + |(bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re| +
          (|(bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re| + |(bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re|)) ≤
        (bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re + (bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re +
          (bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re + (bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re := by
      linarith only [hre1, hre2, hre3, hre4]
    calc -(n * (|(bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re| + |(bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re|) +
          n * (|(bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re| + |(bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re|))
        = n * -(|(bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re| + |(bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re| +
            (|(bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re| + |(bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re|)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs hn_pos
  have hre_main : c⁻¹ * n * physGamma c s L * ((O L - F L) + 1 / 2 * physEta c K1 L * (O L + F L)) -
      C_mac * (c⁻¹ * uctIfl L * (c⁻¹ + c ^ (-2 : ℝ) * L ^ (-2 : ℝ)) + c ^ (-(5 / 2 : ℝ))) -
      c ^ (-(5 / 2 : ℝ)) ≤ (bumpHmain c B ξ).re + ((ε : ℂ) * bumpHrefl c B ξ).re := by
    have hsplit_η : c⁻¹ * n * physGamma c s L * ((O L - F L) + physEta c K1 L * (O L + F L)) -
        c⁻¹ * n * physGamma c s L * (1 / 2 * physEta c K1 L * (O L + F L)) =
        c⁻¹ * n * physGamma c s L * ((O L - F L) + 1 / 2 * physEta c K1 L * (O L + F L)) := by ring
    linarith only [hre_diff, hp4_term_nn, hn_abs, href_re, hcomb_14, hcomb_p23, hcomb_lam, hlam_absorb, hsplit_η]
  change _ ≤ normDensity (ctWbump B ε c) c ξ
  rw [normDensity_ctWbump hc1 hδ0 hδ32 le_rfl hM0' hξ hprof, Complex.add_re]
  exact hre_main

/-- **Regime 4 (`(1/4) log c ≤ L`)**: `normDensity (ctWbump B ε c) c ξ ≥ c⁻¹ n_c γ ((1 + η) O - (1 - η) F) - C(K₄, K₁) c⁻² L⁻²`. -/
theorem physBump_far_lower {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K4 : ℝ} (hK4 : 1 ≤ K4)
    {T1 alpha Nc : ℝ → ℝ → ℝ} (hwarp : FctWarpZeroStmt T1 alpha) (hNc : FctSplittingNormStmt Nc) :
    ∀ K1 : ℝ, 0 ≤ K1 → ∃ C c₀ : ℝ, 0 ≤ C ∧ 2 ≤ c₀ ∧
      ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
        1 / 4 * Real.log c ≤ Real.log (Real.pi ^ 2 * ξ) →
        c⁻¹ * (1 / Nc ε c) * physGamma c (physShift ε c) (Real.log (Real.pi ^ 2 * ξ)) *
            ((1 + physEta c K1 (Real.log (Real.pi ^ 2 * ξ))) *
              physOscDatum StripKernelChoice.star K4 T1 alpha ε c (Real.log (Real.pi ^ 2 * ξ)) -
             (1 - physEta c K1 (Real.log (Real.pi ^ 2 * ξ))) *
              physF (physShift ε c) (physL1 T1 ε c) (Real.log (Real.pi ^ 2 * ξ))) -
          C * (c ^ 2)⁻¹ * ((Real.log (Real.pi ^ 2 * ξ)) ^ 2)⁻¹ ≤
          normDensity (ctWbump (physBump χ (1 / Nc ε c) c (physDelta c) (physShift ε c) K1 K4
            (physOscDatum StripKernelChoice.star K4 T1 alpha ε c)
            (physF (physShift ε c) (physL1 T1 ε c)) (fun L => tau0 L ^ 4 * uctIfl L)) ε c) c ξ := by
  obtain ⟨c_d, a₀, _, M1, M2_0, M3_0, M4, M_B0, M_BK, K1_k, K2_k, K3_k, K4_k, K_B,
    _, ha₀, _, hM1, _, _, hM4, hMB0, hMBK, _, hdec⟩ := physBump_decomp hχ hK4 hwarp hNc
  obtain ⟨Cf1, hCf1, hfar1⟩ := fct_bump5_far (α := 1 / 2) (β := 3 / 2) (by norm_num) le_rfl K1_k ha₀
  obtain ⟨Cf2, hCf2, hfar2⟩ := fct_bump5_far (α := 7 / 2) (β := 7 / 2) (by norm_num) (by norm_num) K2_k ha₀
  obtain ⟨Cf3, hCf3, hfar3⟩ := fct_bump5_far (α := 3 / 2) (β := 3 / 2) (by norm_num) le_rfl K3_k ha₀
  obtain ⟨Cf4, hCf4, hfar4⟩ := fct_bump5_far (α := -(1 / 2)) (β := 3 / 2) (by norm_num) le_rfl K4_k ha₀
  obtain ⟨C_r, κ_r, hCr0, hκr0, hrefl⟩ := fct_bump5_refl (α := 7 / 2) (β := 3 / 2) le_rfl K_B ha₀
  intro K1 hK1
  set C_far : ℝ := 2 * (Cf1 * M1 + Cf2 * M2_0 * K1 + Cf3 * M3_0 * K1 + Cf4 * M4) +
    C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * (M_B0 + M_BK * K1)
  set c_r1 : ℝ := (1 / a₀ + 1) ^ 2
  set c₀ : ℝ := max (max c_d c_r1) (Real.exp 8)
  have hexp8_ge2 : 2 ≤ Real.exp 8 := by linarith only [Real.add_one_le_exp 8]
  refine ⟨C_far, c₀, by positivity, hexp8_ge2.trans (le_max_right _ _), fun ε c ξ hε hc hξ hL => ?_⟩
  simp only [c₀, max_le_iff] at hc
  obtain ⟨⟨hcd', hcr1'⟩, hce8⟩ := hc
  have hc2 : 2 ≤ c := hexp8_ge2.trans hce8
  have hc0 : 0 < c := by linarith only [hc2]
  have hc1 : 1 ≤ c := by linarith only [hc2]
  set δ := physDelta c
  set s := physShift ε c
  set L1 := physL1 T1 ε c
  set n := 1 / Nc ε c
  set F := physF s L1
  set O := physOscDatum StripKernelChoice.star K4 T1 alpha ε c
  set T4 : ℝ → ℝ := fun L => tau0 L ^ 4 * uctIfl L
  set R : ℝ → ℝ := fun x => O x / F x
  set p1 : ℝ → ℝ := fun x => χ (x / (3 * δ)) * physGamma c s x * (F x * R x - F x)
  set p2 : ℝ → ℝ := fun x => χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) * (F x * R x + F x))
  set p3 : ℝ → ℝ := fun x => χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ * (F x * R x + F x))
  set p4 : ℝ → ℝ := fun x => 2 * K4 * (χ (x / (3 * δ)) * ((1 - χ (x / (6 * δ))) * T4 x))
  set B := physBump χ n c δ s K1 K4 O F T4
  obtain ⟨⟨_, _, hsqrt_δ, hδ0, hδ1', hδ32, h6δ, hn_lo, hn_hi, hs_le, hL1_le⟩, hBeq,
    hbs1, hbs2, hbs3, hbs4, _, _, hprof⟩ := hdec K1 ε c hK1 hε hcd'
  set L := Real.log (Real.pi ^ 2 * ξ)
  have hL_ge2 : 2 ≤ L := by
    have hlogc : 8 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).mpr hce8
    linarith only [hL, hlogc]
  have hL_ge1 : 1 ≤ L := by linarith only [hL_ge2]
  have hL_pos : 0 < L := by linarith only [hL_ge1]
  have hL_far : Real.log c / 4 ≤ L := by linarith only [hL]
  have h1 := hfar1 p1 δ M1 c ξ hδ0 hδ1' hδ32 hM1 hce8 hsqrt_δ hξ hL_far hbs1
  have h2 := hfar2 p2 δ (M2_0 * K1 * c ^ (-2 : ℝ)) c ξ hδ0 hδ1' hδ32 (by positivity) hce8 hsqrt_δ hξ hL_far hbs2
  have h3 := hfar3 p3 δ (M3_0 * K1 * c⁻¹) c ξ hδ0 hδ1' hδ32 (by positivity) hce8 hsqrt_δ hξ hL_far hbs3
  have h4 := hfar4 p4 δ M4 c ξ hδ0 hδ1' hδ32 hM4 hce8 hsqrt_δ hξ hL_far hbs4
  have hM0' : 0 ≤ M_B0 + M_BK * K1 * c⁻¹ := by positivity
  have ha0_sq : 1 ≤ a₀ * Real.sqrt c := by
    have h1' : 1 / a₀ + 1 ≤ Real.sqrt c := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / a₀ + 1)]; exact Real.sqrt_le_sqrt hcr1'
    have h2' : 1 ≤ a₀ * (1 / a₀ + 1) := by field_simp; linarith only [ha₀]
    calc 1 ≤ a₀ * (1 / a₀ + 1) := h2'
      _ ≤ a₀ * Real.sqrt c := mul_le_mul_of_nonneg_left h1' ha₀.le
  have hrefl_bd : ‖bumpHrefl c B ξ‖ ≤
      C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * (M_B0 + M_BK * K1) * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ := by
    have hr := (hrefl B δ (M_B0 + M_BK * K1 * c⁻¹) c ξ hδ0 hδ1' hδ32 hM0' hc2 ha0_sq hsqrt_δ hξ hprof).2 hL_ge1
    have hci : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
    have hMB_le : M_B0 + M_BK * K1 * c⁻¹ ≤ M_B0 + M_BK * K1 := by
      have hm : M_BK * K1 * c⁻¹ ≤ M_BK * K1 * 1 := mul_le_mul_of_nonneg_left hci (mul_nonneg hMBK hK1)
      linarith only [hm]
    have hc3_pos : 0 < c ^ 3 := by positivity
    have hbd3 : ‖bumpHrefl c B ξ‖ * c ^ 3 * L ^ 2 ≤ C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * (M_B0 + M_BK * K1) := by
      have hr' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ L ^ 2)) hc3_pos.le
      have hdiv : C_r * (M_B0 + M_BK * K1 * c⁻¹) * Real.exp (-(κ_r * Real.sqrt c)) / L ^ 2 * L ^ 2 * c ^ 3 =
          C_r * (M_B0 + M_BK * K1 * c⁻¹) * (Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3) := by
        field_simp [hL_pos.ne']
      rw [hdiv] at hr'
      calc ‖bumpHrefl c B ξ‖ * c ^ 3 * L ^ 2 = ‖bumpHrefl c B ξ‖ * L ^ 2 * c ^ 3 := by ring
        _ ≤ C_r * (M_B0 + M_BK * K1 * c⁻¹) * (Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3) := hr'
        _ ≤ C_r * (M_B0 + M_BK * K1) * ((Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hMB_le hCr0) (exp_half_absorb hκr0 hc0) (by positivity) (by positivity)
        _ = _ := by ring
    have hc2_3 : (c ^ 3)⁻¹ ≤ (c ^ 2)⁻¹ := by rw [inv_le_inv₀ hc3_pos (by positivity)]; nlinarith only [hc2]
    have hbd_fin : ‖bumpHrefl c B ξ‖ ≤
        C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * (M_B0 + M_BK * K1) * (c ^ 3)⁻¹ * (L ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity : 0 < L ^ 2), le_mul_inv_iff₀ hc3_pos]
      calc ‖bumpHrefl c B ξ‖ * L ^ 2 * c ^ 3 = ‖bumpHrefl c B ξ‖ * c ^ 3 * L ^ 2 := by ring
        _ ≤ _ := hbd3
    exact hbd_fin.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2_3 (by positivity)) (by positivity))
  have hmain_eq : bumpHmain c B ξ =
      (n : ℂ) * (bumpHmain c p1 ξ + bumpHmain c p2 ξ + bumpHmain c p3 ξ + bumpHmain c p4 ξ) := by
    change bumpHmain c (physBump χ n c δ s K1 K4 O F T4) ξ = _
    rw [hBeq]
    exact bumpHmain_lin4 hc1 hδ0 hδ32 le_rfl (by norm_num) le_rfl le_rfl
      hM1 (by positivity) (by positivity) hM4 hξ
      (hbs1.profile hM1) (hbs2.profile (by positivity)) (hbs3.profile (by positivity)) (hbs4.profile hM4)
  have hχ1 : χ (L / (3 * δ)) = 1 := hχ.one _ (by rw [le_div_iff₀ (by positivity)]; linarith only [hL_ge2, h6δ])
  have hχ6 : χ (L / (6 * δ)) = 1 := hχ.one _ (by rw [le_div_iff₀ (by positivity)]; linarith only [hL_ge2, h6δ])
  have hBL_eq : n * (c⁻¹ * p1 L + c⁻¹ * p2 L + c⁻¹ * p3 L + c⁻¹ * p4 L) =
      c⁻¹ * n * physGamma c s L * ((1 + physEta c K1 L) * O L - (1 - physEta c K1 L) * F L) := by
    have hL32 : 3 / 2 * δ ≤ L := by linarith only [hL_ge2, h6δ, hδ0]
    have hFpos := physF_pos (by positivity : 0 < 3 / 2 * δ) hs_le hL1_le hL32
    dsimp only [p1, p2, p3, p4, R]
    rw [hχ1, hχ6, mul_div_cancel₀ _ hFpos.ne']
    unfold physEta; ring
  have hre_diff : (bumpHmain c B ξ).re - c⁻¹ * n * physGamma c s L *
        ((1 + physEta c K1 L) * O L - (1 - physEta c K1 L) * F L) =
      n * ((bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re + (bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re +
        (bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re + (bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re) := by
    rw [hmain_eq, ← hBL_eq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.sub_re,
      zero_mul, sub_zero]
    ring
  have hc2_1 : c ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hci : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
  have hmain_abs : |(bumpHmain c B ξ).re - c⁻¹ * n * physGamma c s L *
        ((1 + physEta c K1 L) * O L - (1 - physEta c K1 L) * F L)| ≤
      2 * (Cf1 * M1 + Cf2 * M2_0 * K1 + Cf3 * M3_0 * K1 + Cf4 * M4) * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ := by
    rw [hre_diff, abs_mul, abs_of_nonneg (by linarith only [hn_lo])]
    have a1 := (Complex.abs_re_le_norm _).trans h1
    have a2 := (Complex.abs_re_le_norm _).trans (h2.trans (by
      have hc2' : M2_0 * K1 * c ^ (-2 : ℝ) ≤ M2_0 * K1 := by
        calc M2_0 * K1 * c ^ (-2 : ℝ) ≤ M2_0 * K1 * 1 := mul_le_mul_of_nonneg_left hc2_1 (by positivity)
          _ = M2_0 * K1 := mul_one _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2' hCf2) (by positivity)) (by positivity)))
    have a3 := (Complex.abs_re_le_norm _).trans (h3.trans (by
      have hc1' : M3_0 * K1 * c⁻¹ ≤ M3_0 * K1 := by
        calc M3_0 * K1 * c⁻¹ ≤ M3_0 * K1 * 1 := mul_le_mul_of_nonneg_left hci (by positivity)
          _ = M3_0 * K1 := mul_one _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc1' hCf3) (by positivity)) (by positivity)))
    have a4 := (Complex.abs_re_le_norm _).trans h4
    have htri := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add a1 a2)) a3)) a4)
    have hsum : Cf1 * M1 * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ + Cf2 * (M2_0 * K1) * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ +
        Cf3 * (M3_0 * K1) * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ + Cf4 * M4 * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ =
        (Cf1 * M1 + Cf2 * M2_0 * K1 + Cf3 * M3_0 * K1 + Cf4 * M4) * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ := by ring
    calc n * |_| ≤ 2 * ((Cf1 * M1 + Cf2 * M2_0 * K1 + Cf3 * M3_0 * K1 + Cf4 * M4) * (c ^ 2)⁻¹ * (L ^ 2)⁻¹) :=
          mul_le_mul hn_hi (htri.trans_eq hsum) (abs_nonneg _) zero_le_two
      _ = _ := by ring
  have href_abs : |((ε : ℂ) * bumpHrefl c B ξ).re| ≤
      C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * (M_B0 + M_BK * K1) * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rcases hε with rfl | rfl
    · simp only [abs_one, one_mul]; exact hrefl_bd
    · simp only [abs_neg, abs_one, one_mul]; exact hrefl_bd
  change _ ≤ normDensity (ctWbump B ε c) c ξ
  rw [normDensity_ctWbump hc1 hδ0 hδ32 le_rfl hM0' hξ hprof, Complex.add_re]
  have h1' := (abs_le.mp hmain_abs).1
  have h2' := (abs_le.mp href_abs).1
  dsimp only [C_far]
  linarith only [h1', h2']

/-- info: 'FormalResearch.SignUncertainty.physBump_mac_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physBump_mac_lower

/-- info: 'FormalResearch.SignUncertainty.physBump_far_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physBump_far_lower

end FormalResearch.SignUncertainty
