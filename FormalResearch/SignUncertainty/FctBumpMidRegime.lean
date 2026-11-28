/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctBumpDecomp

/-!
# Middle regime lower bound for `normDensity (ctWbump B ε c) c ξ` (`fct:bump-5` + `fct:bump-sym-check`)

For `χ` (`IsCutoff χ`), `K₄ ≥ 1`, `(T₁, α)` solving the zero condition (`FctWarpZeroStmt`),
`N_c = 1 + O(c⁻¹)` (`FctSplittingNormStmt`), and
`B := physBump χ (1 / Nc ε c) c (physDelta c) (physShift ε c) K₁ K₄ O F (fun L => τ₀(L)⁴ I_fl(L))`:

* `physBump_mid_lower` (`3 δ_L / 4 ≤ L ≤ 3 δ_L`): `normDensity (ctWbump B ε c) c ξ ≥ -(C₀(K₄) + C₁(K₄) K₁) c^{-7/4}`
  (uses `physBump_nonneg_le_three_delta` and `physDiff_mid_symW` so `C₀, C₁` do not depend on `K₁`).

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctSym
open FormalResearch.SignUncertainty.FctSym.SymW
open FormalResearch.SignUncertainty.FctCompD

namespace FormalResearch.SignUncertainty

private lemma mid_rpow_neg_nat {L : ℝ} (hL : 0 < L) (γ : ℝ) (k : ℕ) :
    L ^ (-γ - (k : ℝ)) = L ^ (-γ) / L ^ k := by
  rw [sub_eq_add_neg, Real.rpow_add hL, div_eq_mul_inv]
  congr 1
  rw [Real.rpow_neg hL.le k, Real.rpow_natCast]

private lemma mid_rpow_half_nat {L : ℝ} (hL : 0 < L) (k : ℕ) :
    L ^ (1 / 2 - (k : ℝ)) = L ^ (1 / 2 : ℝ) / L ^ k := by
  rw [sub_eq_add_neg, Real.rpow_add hL, div_eq_mul_inv]
  congr 1
  rw [Real.rpow_neg hL.le k, Real.rpow_natCast]

private lemma mid_rpow_neg_two {x : ℝ} (hx : 0 < x) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]

private lemma mid_rpow_neg_three {x : ℝ} (hx : 0 < x) : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
  rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]

private lemma mid_refl_seven_quarter {C_r κ_r M_B0 M_BK K1 c ξ : ℝ} {B : ℝ → ℝ}
    (hCr0 : 0 ≤ C_r) (hκr0 : 0 < κ_r) (hMBK : 0 ≤ M_BK) (hK1 : 0 ≤ K1) (hM0 : 0 ≤ M_B0 + M_BK * K1 * c⁻¹)
    (hc1 : 1 ≤ c) (hc0 : 0 < c)
    (hr : ‖bumpHrefl c B ξ‖ ≤ C_r * (M_B0 + M_BK * K1 * c⁻¹) * Real.exp (-(κ_r * Real.sqrt c))) :
    ‖bumpHrefl c B ξ‖ ≤ (C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * M_B0 +
        C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * M_BK * K1) * c ^ (-(7 / 4 : ℝ)) := by
  have hci : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
  have hMB_le : M_B0 + M_BK * K1 * c⁻¹ ≤ M_B0 + M_BK * K1 := by
    have hm : M_BK * K1 * c⁻¹ ≤ M_BK * K1 * 1 := mul_le_mul_of_nonneg_left hci (mul_nonneg hMBK hK1)
    linarith only [hm]
  have hc3_pos : 0 < c ^ 3 := by positivity
  have h74_3 : c ^ (-3 : ℝ) ≤ c ^ (-(7 / 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hr3 := mul_le_mul_of_nonneg_right hr hc3_pos.le
  set Er0 := C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * M_B0
  set Er1 := C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * M_BK
  have hMB_nn : 0 ≤ M_B0 + M_BK * K1 := le_trans hM0 hMB_le
  have hbd3 : ‖bumpHrefl c B ξ‖ * c ^ 3 ≤ Er0 + Er1 * K1 := by
    calc ‖bumpHrefl c B ξ‖ * c ^ 3
        ≤ C_r * (M_B0 + M_BK * K1 * c⁻¹) * Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3 := hr3
      _ = (C_r * (M_B0 + M_BK * K1 * c⁻¹)) * (Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3) := by ring
      _ ≤ (C_r * (M_B0 + M_BK * K1)) * (Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB_le hCr0)
            (mul_nonneg (Real.exp_pos _).le hc3_pos.le)
      _ ≤ (C_r * (M_B0 + M_BK * K1)) * ((Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹) :=
          mul_le_mul_of_nonneg_left (exp_half_absorb hκr0 hc0) (mul_nonneg hCr0 hMB_nn)
      _ = Er0 + Er1 * K1 := by dsimp only [Er0, Er1]; ring
  have hEr_nn : 0 ≤ Er0 + Er1 * K1 := by
    dsimp only [Er0, Er1]
    have hfac : 0 ≤ C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ := by positivity
    nlinarith only [hfac, hMB_nn]
  have hc3inv : ‖bumpHrefl c B ξ‖ ≤ (Er0 + Er1 * K1) * (c ^ 3)⁻¹ := by
    rw [le_mul_inv_iff₀ hc3_pos]; exact hbd3
  refine hc3inv.trans ?_
  rw [← mid_rpow_neg_three hc0]
  exact mul_le_mul_of_nonneg_left h74_3 hEr_nn

/-- **Regime 2 (`3 δ_L / 4 ≤ L ≤ 3 δ_L`)**: `normDensity (ctWbump B ε c) c ξ ≥ -(C₀(K₄) + C₁(K₄) K₁) c^{-7/4}`
with `C₀, C₁` independent of `K₁`. -/
theorem physBump_mid_lower {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K4 : ℝ} (hK4 : 1 ≤ K4)
    {T1 alpha Nc : ℝ → ℝ → ℝ} (hwarp : FctWarpZeroStmt T1 alpha) (hNc : FctSplittingNormStmt Nc) :
    ∃ (C0 C1 : ℝ), 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ K1 : ℝ, 0 ≤ K1 → ∃ c₀ : ℝ, 2 ≤ c₀ ∧
      ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
        3 / 4 * physDelta c ≤ Real.log (Real.pi ^ 2 * ξ) →
        Real.log (Real.pi ^ 2 * ξ) ≤ 3 * physDelta c →
        -(C0 + C1 * K1) * c ^ (-(7 / 4 : ℝ)) ≤
          normDensity (ctWbump (physBump χ (1 / Nc ε c) c (physDelta c) (physShift ε c) K1 K4
            (physOscDatum StripKernelChoice.star K4 T1 alpha ε c)
            (physF (physShift ε c) (physL1 T1 ε c)) (fun L => tau0 L ^ 4 * uctIfl L)) ε c) c ξ := by
  obtain ⟨c_d, a₀, a₁, M1, M2_0, M3_0, M4, M_B0, M_BK, K1_k, K2_k, K3_k, K4_k, K_B,
    _, ha₀, ha₁, hM1, hM2, hM3, hM4, hMB0, hMBK, _, hdec⟩ := physBump_decomp hχ hK4 hwarp hNc
  obtain ⟨c_pos, _, hB_nonneg⟩ := physBump_nonneg_le_three_delta hχ hK4 hwarp hNc
  obtain ⟨c_diff, C_diff, K_diff, _, hCdiff0, _, hmid_sym⟩ := physDiff_mid_symW hχ hK4 hwarp
  set Kl1 : ℕ → ℝ := fun k => max (K1_k k) (K_diff k)
  obtain ⟨Cloc1, hCloc1, hloc1⟩ := bump_weighted_local (b := 3 / 2) (α := 1 / 2) (β := 3 / 2) (by norm_num) le_rfl K1_k Kl1 ha₀
  obtain ⟨Cloc2, hCloc2, hloc2⟩ := bump_weighted_local (b := 3 / 2) (α := 7 / 2) (β := 7 / 2) (by norm_num) (by norm_num) K2_k K2_k ha₀
  obtain ⟨Cloc3, hCloc3, hloc3⟩ := bump_weighted_local (b := 3 / 2) (α := 3 / 2) (β := 3 / 2) (by norm_num) le_rfl K3_k K3_k ha₀
  obtain ⟨Cloc4, hCloc4, hloc4⟩ := bump_weighted_local (b := 3 / 2) (α := -(1 / 2)) (β := 3 / 2) (by norm_num) le_rfl K4_k K4_k ha₀
  obtain ⟨C_r, κ_r, hCr0, hκr0, hrefl⟩ := fct_bump5_refl (α := 7 / 2) (β := 3 / 2) le_rfl K_B ha₀
  set K_L : ℝ := (3 / 4 * a₀)⁻¹ + (3 / 4 * a₀) ^ (-3 : ℝ)
  set E1 : ℝ := Cloc1 * C_diff * K_L + Cloc1 * M1 * 2 * a₁
  set E4 : ℝ := Cloc4 * (M4 * (3 * a₁) ^ (1 / 2 : ℝ)) * K_L + Cloc4 * M4 * 2 * a₁
  set E2 : ℝ := Cloc2 * (M2_0 * (3 / 2 * a₀) ^ (-(7 / 2 : ℝ))) * K_L + Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁
  set E3 : ℝ := Cloc3 * (M3_0 * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ))) * K_L + Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁
  set Er0 : ℝ := C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * M_B0
  set Er1 : ℝ := C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * M_BK
  set C0 : ℝ := 2 * (E1 + E4) + Er0
  set C1 : ℝ := 2 * (E2 + E3) + Er1
  refine ⟨C0, C1, by positivity, by positivity, fun K1 hK1 => ?_⟩
  set c_r1 : ℝ := (1 / a₀ + 1) ^ 2
  set c₀ : ℝ := max (max (max c_d c_pos) (max c_diff c_r1)) 2
  refine ⟨c₀, le_max_right _ _, fun ε c ξ hε hc hξ hL_lo hL_hi => ?_⟩
  simp only [c₀, max_le_iff] at hc
  obtain ⟨⟨⟨hcd', hcpos'⟩, ⟨hcdiff', hcr1'⟩⟩, hc2⟩ := hc
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
    hbs1, hbs2, hbs3, hbs4, _, _, hprof⟩ := hdec K1 ε c hK1 hε hcd'
  set L := Real.log (Real.pi ^ 2 * ξ)
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_lo
  have hL32_lo : 3 / 2 * δ / 2 ≤ L := by linarith only [hL_lo]
  have hL_rpow_inv : (c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹ ≤ K_L * c ^ (-(3 / 2 : ℝ)) := by
    have hLa : 3 / 4 * a₀ * c ^ (-(1 / 2 : ℝ)) ≤ L := by
      have h1 : 3 / 4 * (a₀ * c ^ (-(1 / 2 : ℝ))) ≤ 3 / 4 * δ := mul_le_mul_of_nonneg_left hδ_lo (by norm_num)
      linarith only [hL_lo, h1]
    have hL1_bd : L⁻¹ ≤ (3 / 4 * a₀)⁻¹ * c ^ (1 / 2 : ℝ) := by
      have h1 : L⁻¹ ≤ (3 / 4 * a₀ * c ^ (-(1 / 2 : ℝ)))⁻¹ := inv_anti₀ (by positivity) hLa
      rw [mul_inv, ← Real.rpow_neg hc0.le, neg_neg] at h1; exact h1
    have hL3_bd : (L ^ 3)⁻¹ ≤ (3 / 4 * a₀) ^ (-3 : ℝ) * c ^ (3 / 2 : ℝ) := by
      have h2 : L ^ (-3 : ℝ) ≤ (3 / 4 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hLa (by norm_num)
      rw [← mid_rpow_neg_three hL_pos]; refine h2.trans_eq ?_
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc0.le]; norm_num
    have hc2_eq : (c ^ 2)⁻¹ * c ^ (1 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast c 2, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
    have hc3_eq : (c ^ 3)⁻¹ * c ^ (3 / 2 : ℝ) = c ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast c 3, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
    calc (c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹
        ≤ (c ^ 2)⁻¹ * ((3 / 4 * a₀)⁻¹ * c ^ (1 / 2 : ℝ)) +
            (c ^ 3)⁻¹ * ((3 / 4 * a₀) ^ (-3 : ℝ) * c ^ (3 / 2 : ℝ)) := by gcongr
      _ = (3 / 4 * a₀)⁻¹ * ((c ^ 2)⁻¹ * c ^ (1 / 2 : ℝ)) + (3 / 4 * a₀) ^ (-3 : ℝ) * ((c ^ 3)⁻¹ * c ^ (3 / 2 : ℝ)) := by ring
      _ = K_L * c ^ (-(3 / 2 : ℝ)) := by rw [hc2_eq, hc3_eq]; dsimp only [K_L]; ring
  have h14_74 : c ^ (-(1 / 4 : ℝ)) * (K_L * c ^ (-(3 / 2 : ℝ))) = K_L * c ^ (-(7 / 4 : ℝ)) := by
    have : c ^ (-(1 / 4 : ℝ)) * c ^ (-(3 / 2 : ℝ)) = c ^ (-(7 / 4 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    linear_combination K_L * this
  have h52_74 : (c ^ 2)⁻¹ * δ ≤ a₁ * c ^ (-(7 / 4 : ℝ)) := by
    have hc212 : (c ^ 2)⁻¹ * c ^ (-(1 / 2 : ℝ)) = c ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast c 2, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
    have h74 : c ^ (-(5 / 2 : ℝ)) ≤ c ^ (-(7 / 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc (c ^ 2)⁻¹ * δ ≤ (c ^ 2)⁻¹ * (a₁ * c ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hδ_hi (by positivity)
      _ = a₁ * c ^ (-(5 / 2 : ℝ)) := by linear_combination a₁ * hc212
      _ ≤ a₁ * c ^ (-(7 / 4 : ℝ)) := mul_le_mul_of_nonneg_left h74 ha₁.le
  have hp1_bd : ‖bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)‖ ≤ E1 * c ^ (-(7 / 4 : ℝ)) := by
    have hMloc1 : 0 ≤ C_diff * c ^ (-(1 / 4 : ℝ)) := mul_nonneg hCdiff0 (Real.rpow_nonneg hc0.le _)
    have hloc := hloc1 p1 δ M1 (C_diff * c ^ (-(1 / 4 : ℝ))) c ξ hδ0 hδ1' hδ32 hM1 hMloc1 hc2 hsqrt_δ hξ hL32_lo
      (fun k _ _ => by
        rcases le_or_gt L (3 / 2 * δ) with hle | hgt
        · rw [iteratedDeriv_eq_zero_of_eqOn_Iio hbs1.smooth hbs1.support k L hle, abs_zero]
          exact div_nonneg (mul_nonneg (le_max_of_le_left (hbs1.K_nonneg k)) hMloc1) (pow_nonneg hL_pos.le k)
        · have hsym := hmid_sym ε c hε hcdiff'
          have hbd := hsym.bound k L ⟨hgt.le, hL_hi⟩
          have hev : (fun x => χ (x / (3 * δ)) * physGamma c s x * (O x - F x)) =ᶠ[𝓝 L] p1 := by
            filter_upwards [isOpen_Ioi.mem_nhds hgt] with x hx
            have hFpos := physF_pos (by positivity : 0 < 3 / 2 * δ) hs_le hL1_le (le_of_lt hx)
            dsimp only [p1, R]; rw [mul_div_cancel₀ _ hFpos.ne']
          rw [hev.iteratedDeriv_eq k] at hbd
          refine hbd.trans ?_
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hMloc1) (inv_nonneg.mpr (pow_nonneg hL_pos.le k)))
      (hbs1.profile hM1)
    have hlam1 : bumpLambda (1 / 2) δ ≤ 2 := by
      unfold bumpLambda; rw [ite_eq_right (by norm_num)]
      linarith only [Real.rpow_le_one hδ0.le hδ1' (by norm_num : 0 ≤ 1 - (1 / 2 : ℝ))]
    have hc2_nn : 0 ≤ (c ^ 2)⁻¹ * δ := by positivity
    have hterm1 : Cloc1 * (C_diff * c ^ (-(1 / 4 : ℝ))) * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹) ≤
        Cloc1 * C_diff * K_L * c ^ (-(7 / 4 : ℝ)) := by
      calc Cloc1 * (C_diff * c ^ (-(1 / 4 : ℝ))) * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹)
          ≤ Cloc1 * (C_diff * c ^ (-(1 / 4 : ℝ))) * (K_L * c ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hL_rpow_inv (mul_nonneg hCloc1 hMloc1)
        _ = Cloc1 * C_diff * (c ^ (-(1 / 4 : ℝ)) * (K_L * c ^ (-(3 / 2 : ℝ)))) := by ring
        _ = Cloc1 * C_diff * K_L * c ^ (-(7 / 4 : ℝ)) := by rw [h14_74]; ring
    have hterm2 : Cloc1 * M1 * bumpLambda (1 / 2) δ * ((c ^ 2)⁻¹ * δ) ≤ Cloc1 * M1 * 2 * a₁ * c ^ (-(7 / 4 : ℝ)) := by
      calc Cloc1 * M1 * bumpLambda (1 / 2) δ * ((c ^ 2)⁻¹ * δ)
          ≤ Cloc1 * M1 * 2 * (a₁ * c ^ (-(7 / 4 : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hlam1 (mul_nonneg hCloc1 hM1)) h52_74 hc2_nn (by positivity)
        _ = Cloc1 * M1 * 2 * a₁ * c ^ (-(7 / 4 : ℝ)) := by ring
    exact hloc.trans (by dsimp only [E1]; linarith only [hterm1, hterm2])
  have hp4_bd : ‖bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)‖ ≤ E4 * c ^ (-(7 / 4 : ℝ)) := by
    have hMloc4 : 0 ≤ M4 * (3 * a₁) ^ (1 / 2 : ℝ) * c ^ (-(1 / 4 : ℝ)) := by positivity
    have hloc := hloc4 p4 δ M4 (M4 * (3 * a₁) ^ (1 / 2 : ℝ) * c ^ (-(1 / 4 : ℝ))) c ξ
      hδ0 hδ1' hδ32 hM4 hMloc4 hc2 hsqrt_δ hξ hL32_lo
      (fun k _ _ => by
        rcases le_or_gt L (3 / 2 * δ) with hle | hgt
        · rw [iteratedDeriv_eq_zero_of_eqOn_Iio hbs4.smooth hbs4.support k L hle, abs_zero]
          exact div_nonneg (mul_nonneg (hbs4.K_nonneg k) hMloc4) (pow_nonneg hL_pos.le k)
        · have hbd := hbs4.bound k L hgt.le
          have hL1 : L ≤ 1 := by linarith only [hL_hi, h6δ]
          have hmin : min (L ^ (-(-(1 / 2 : ℝ)) - (k : ℝ))) (L ^ (-(3 / 2 : ℝ) - (k : ℝ))) = L ^ (1 / 2 - (k : ℝ)) := by
            rw [show -(-(1 / 2 : ℝ)) - (k : ℝ) = 1 / 2 - (k : ℝ) by ring]
            exact min_eq_left (Real.rpow_le_rpow_of_exponent_ge hL_pos hL1 (by linarith))
          rw [hmin] at hbd
          have hL12_bd : L ^ (1 / 2 : ℝ) ≤ (3 * a₁) ^ (1 / 2 : ℝ) * c ^ (-(1 / 4 : ℝ)) := by
            have hLhi : L ≤ 3 * a₁ * c ^ (-(1 / 2 : ℝ)) := by
              have h1 : 3 * δ ≤ 3 * (a₁ * c ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hδ_hi (by norm_num)
              linarith only [hL_hi, h1]
            have hr := Real.rpow_le_rpow hL_pos.le hLhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc0.le,
              show (-(1 / 2 : ℝ)) * (1 / 2 : ℝ) = -(1 / 4 : ℝ) by norm_num] at hr; exact hr
          refine hbd.trans ?_; rw [mid_rpow_half_nat hL_pos k]
          calc K4_k k * M4 * (L ^ (1 / 2 : ℝ) / L ^ k)
              = K4_k k * (M4 * L ^ (1 / 2 : ℝ)) / L ^ k := by ring
            _ ≤ K4_k k * (M4 * ((3 * a₁) ^ (1 / 2 : ℝ) * c ^ (-(1 / 4 : ℝ)))) / L ^ k := by
                gcongr; exact hbs4.K_nonneg k
            _ = K4_k k * (M4 * (3 * a₁) ^ (1 / 2 : ℝ) * c ^ (-(1 / 4 : ℝ))) / L ^ k := by ring) (hbs4.profile hM4)
    have hlam4 : bumpLambda (-(1 / 2)) δ ≤ 2 := by
      unfold bumpLambda; rw [ite_eq_right (by norm_num)]
      linarith only [Real.rpow_le_one hδ0.le hδ1' (by norm_num : 0 ≤ 1 - (-(1 / 2 : ℝ)))]
    have hc2_nn : 0 ≤ (c ^ 2)⁻¹ * δ := by positivity
    have hterm1 : Cloc4 * (M4 * (3 * a₁) ^ (1 / 2 : ℝ) * c ^ (-(1 / 4 : ℝ))) * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹) ≤
        Cloc4 * (M4 * (3 * a₁) ^ (1 / 2 : ℝ)) * K_L * c ^ (-(7 / 4 : ℝ)) := by
      calc Cloc4 * (M4 * (3 * a₁) ^ (1 / 2 : ℝ) * c ^ (-(1 / 4 : ℝ))) * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹)
          ≤ Cloc4 * (M4 * (3 * a₁) ^ (1 / 2 : ℝ) * c ^ (-(1 / 4 : ℝ))) * (K_L * c ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hL_rpow_inv (mul_nonneg hCloc4 hMloc4)
        _ = Cloc4 * (M4 * (3 * a₁) ^ (1 / 2 : ℝ)) * (c ^ (-(1 / 4 : ℝ)) * (K_L * c ^ (-(3 / 2 : ℝ)))) := by ring
        _ = Cloc4 * (M4 * (3 * a₁) ^ (1 / 2 : ℝ)) * K_L * c ^ (-(7 / 4 : ℝ)) := by rw [h14_74]; ring
    have hterm2 : Cloc4 * M4 * bumpLambda (-(1 / 2)) δ * ((c ^ 2)⁻¹ * δ) ≤ Cloc4 * M4 * 2 * a₁ * c ^ (-(7 / 4 : ℝ)) := by
      calc Cloc4 * M4 * bumpLambda (-(1 / 2)) δ * ((c ^ 2)⁻¹ * δ)
          ≤ Cloc4 * M4 * 2 * (a₁ * c ^ (-(7 / 4 : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hlam4 (mul_nonneg hCloc4 hM4)) h52_74 hc2_nn (by positivity)
        _ = Cloc4 * M4 * 2 * a₁ * c ^ (-(7 / 4 : ℝ)) := by ring
    exact hloc.trans (by dsimp only [E4]; linarith only [hterm1, hterm2])
  have hp2_bd : ‖bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)‖ ≤ E2 * K1 * c ^ (-(7 / 4 : ℝ)) := by
    have hM2c : 0 ≤ M2_0 * K1 * c ^ (-2 : ℝ) := by positivity
    have hMloc2 : 0 ≤ M2_0 * (3 / 2 * a₀) ^ (-(7 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ)) := by positivity
    have hloc := hloc2 p2 δ (M2_0 * K1 * c ^ (-2 : ℝ)) (M2_0 * (3 / 2 * a₀) ^ (-(7 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ))) c ξ
      hδ0 hδ1' hδ32 hM2c hMloc2 hc2 hsqrt_δ hξ hL32_lo
      (fun k _ _ => by
        rcases le_or_gt L (3 / 2 * δ) with hle | hgt
        · rw [iteratedDeriv_eq_zero_of_eqOn_Iio hbs2.smooth hbs2.support k L hle, abs_zero]
          exact div_nonneg (mul_nonneg (hbs2.K_nonneg k) hMloc2) (pow_nonneg hL_pos.le k)
        · have hbd := hbs2.bound k L hgt.le; simp only [min_self] at hbd
          have hL_ge : 3 / 2 * a₀ * c ^ (-(1 / 2 : ℝ)) ≤ L := by
            have h1 : 3 / 2 * (a₀ * c ^ (-(1 / 2 : ℝ))) ≤ 3 / 2 * δ := mul_le_mul_of_nonneg_left hδ_lo (by norm_num)
            linarith only [hgt, h1]
          have hL72_bd : L ^ (-(7 / 2 : ℝ)) ≤ (3 / 2 * a₀) ^ (-(7 / 2 : ℝ)) * c ^ (7 / 4 : ℝ) := by
            have hr := Real.rpow_le_rpow_of_nonpos (by positivity) hL_ge (by norm_num : (-(7 / 2 : ℝ)) ≤ 0)
            refine hr.trans_eq ?_
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc0.le]; norm_num
          have hc274 : c ^ (-2 : ℝ) * c ^ (7 / 4 : ℝ) = c ^ (-(1 / 4 : ℝ)) := by
            rw [mid_rpow_neg_two hc0, ← Real.rpow_natCast c 2, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
          refine hbd.trans ?_; rw [mid_rpow_neg_nat hL_pos (7 / 2) k]
          calc K2_k k * (M2_0 * K1 * c ^ (-2 : ℝ)) * (L ^ (-(7 / 2 : ℝ)) / L ^ k)
              ≤ K2_k k * (M2_0 * K1 * c ^ (-2 : ℝ)) * ((3 / 2 * a₀) ^ (-(7 / 2 : ℝ)) * c ^ (7 / 4 : ℝ) / L ^ k) := by
                gcongr; exact mul_nonneg (hbs2.K_nonneg k) hM2c
            _ = K2_k k * (M2_0 * (3 / 2 * a₀) ^ (-(7 / 2 : ℝ)) * K1 * (c ^ (-2 : ℝ) * c ^ (7 / 4 : ℝ))) / L ^ k := by ring
            _ = K2_k k * (M2_0 * (3 / 2 * a₀) ^ (-(7 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ))) / L ^ k := by rw [hc274])
      (hbs2.profile hM2c)
    have hlam2 : bumpLambda (7 / 2) δ ≤ (1 + a₀ ^ (-(5 / 2 : ℝ))) * c ^ (5 / 4 : ℝ) := by
      unfold bumpLambda; rw [ite_eq_right (by norm_num)]
      have hc54 : 1 ≤ c ^ (5 / 4 : ℝ) := Real.one_le_rpow hc1 (by norm_num)
      have hδ52 : δ ^ (1 - (7 / 2 : ℝ)) ≤ a₀ ^ (-(5 / 2 : ℝ)) * c ^ (5 / 4 : ℝ) := by
        have h1 : δ ^ (-(5 / 2 : ℝ)) ≤ (a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hδ_lo (by norm_num)
        rw [show 1 - (7 / 2 : ℝ) = -(5 / 2 : ℝ) by norm_num]; refine h1.trans_eq ?_
        rw [Real.mul_rpow ha₀.le (by positivity), ← Real.rpow_mul hc0.le]; norm_num
      nlinarith only [hc54, hδ52]
    have hterm1 : Cloc2 * (M2_0 * (3 / 2 * a₀) ^ (-(7 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ))) *
          ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹) ≤
        Cloc2 * (M2_0 * (3 / 2 * a₀) ^ (-(7 / 2 : ℝ))) * K_L * K1 * c ^ (-(7 / 4 : ℝ)) := by
      calc Cloc2 * (M2_0 * (3 / 2 * a₀) ^ (-(7 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ))) * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹)
          ≤ Cloc2 * (M2_0 * (3 / 2 * a₀) ^ (-(7 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ))) * (K_L * c ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hL_rpow_inv (mul_nonneg hCloc2 hMloc2)
        _ = Cloc2 * (M2_0 * (3 / 2 * a₀) ^ (-(7 / 2 : ℝ))) * K1 * (c ^ (-(1 / 4 : ℝ)) * (K_L * c ^ (-(3 / 2 : ℝ)))) := by ring
        _ = Cloc2 * (M2_0 * (3 / 2 * a₀) ^ (-(7 / 2 : ℝ))) * K_L * K1 * c ^ (-(7 / 4 : ℝ)) := by rw [h14_74]; ring
    have hterm2 : Cloc2 * (M2_0 * K1 * c ^ (-2 : ℝ)) * bumpLambda (7 / 2) δ * ((c ^ 2)⁻¹ * δ) ≤
        Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1 * c ^ (-(7 / 4 : ℝ)) := by
      have hc254 : c ^ (-2 : ℝ) * c ^ (5 / 4 : ℝ) ≤ 1 := by
        rw [mid_rpow_neg_two hc0, ← Real.rpow_natCast c 2, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]
        exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      have hc2_nn : 0 ≤ (c ^ 2)⁻¹ * δ := by positivity
      calc Cloc2 * (M2_0 * K1 * c ^ (-2 : ℝ)) * bumpLambda (7 / 2) δ * ((c ^ 2)⁻¹ * δ)
          ≤ Cloc2 * (M2_0 * K1 * c ^ (-2 : ℝ)) * ((1 + a₀ ^ (-(5 / 2 : ℝ))) * c ^ (5 / 4 : ℝ)) * (a₁ * c ^ (-(7 / 4 : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hlam2 (by positivity)) h52_74 hc2_nn (by positivity)
        _ = Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1 * (c ^ (-2 : ℝ) * c ^ (5 / 4 : ℝ)) * c ^ (-(7 / 4 : ℝ)) := by ring
        _ ≤ Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1 * 1 * c ^ (-(7 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc254 (by positivity)) (Real.rpow_nonneg hc0.le _)
        _ = Cloc2 * M2_0 * (1 + a₀ ^ (-(5 / 2 : ℝ))) * a₁ * K1 * c ^ (-(7 / 4 : ℝ)) := by ring
    exact hloc.trans (by dsimp only [E2]; linarith only [hterm1, hterm2])
  have hp3_bd : ‖bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)‖ ≤ E3 * K1 * c ^ (-(7 / 4 : ℝ)) := by
    have hM3c : 0 ≤ M3_0 * K1 * c⁻¹ := by positivity
    have hMloc3 : 0 ≤ M3_0 * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ)) := by positivity
    have hloc := hloc3 p3 δ (M3_0 * K1 * c⁻¹) (M3_0 * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ))) c ξ
      hδ0 hδ1' hδ32 hM3c hMloc3 hc2 hsqrt_δ hξ hL32_lo
      (fun k _ _ => by
        rcases le_or_gt L (3 / 2 * δ) with hle | hgt
        · rw [iteratedDeriv_eq_zero_of_eqOn_Iio hbs3.smooth hbs3.support k L hle, abs_zero]
          exact div_nonneg (mul_nonneg (hbs3.K_nonneg k) hMloc3) (pow_nonneg hL_pos.le k)
        · have hbd := hbs3.bound k L hgt.le; simp only [min_self] at hbd
          have hL_ge : 3 / 2 * a₀ * c ^ (-(1 / 2 : ℝ)) ≤ L := by
            have h1 : 3 / 2 * (a₀ * c ^ (-(1 / 2 : ℝ))) ≤ 3 / 2 * δ := mul_le_mul_of_nonneg_left hδ_lo (by norm_num)
            linarith only [hgt, h1]
          have hL32_bd : L ^ (-(3 / 2 : ℝ)) ≤ (3 / 2 * a₀) ^ (-(3 / 2 : ℝ)) * c ^ (3 / 4 : ℝ) := by
            have hr := Real.rpow_le_rpow_of_nonpos (by positivity) hL_ge (by norm_num : (-(3 / 2 : ℝ)) ≤ 0)
            refine hr.trans_eq ?_
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc0.le]; norm_num
          have hc134 : c⁻¹ * c ^ (3 / 4 : ℝ) = c ^ (-(1 / 4 : ℝ)) := by
            rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
          refine hbd.trans ?_; rw [mid_rpow_neg_nat hL_pos (3 / 2) k]
          calc K3_k k * (M3_0 * K1 * c⁻¹) * (L ^ (-(3 / 2 : ℝ)) / L ^ k)
              ≤ K3_k k * (M3_0 * K1 * c⁻¹) * ((3 / 2 * a₀) ^ (-(3 / 2 : ℝ)) * c ^ (3 / 4 : ℝ) / L ^ k) := by
                gcongr; exact mul_nonneg (hbs3.K_nonneg k) hM3c
            _ = K3_k k * (M3_0 * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ)) * K1 * (c⁻¹ * c ^ (3 / 4 : ℝ))) / L ^ k := by ring
            _ = K3_k k * (M3_0 * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ))) / L ^ k := by rw [hc134])
      (hbs3.profile hM3c)
    have hlam3 : bumpLambda (3 / 2) δ ≤ (1 + a₀ ^ (-(1 / 2 : ℝ))) * c ^ (1 / 4 : ℝ) := by
      unfold bumpLambda; rw [ite_eq_right (by norm_num)]
      have hc14 : 1 ≤ c ^ (1 / 4 : ℝ) := Real.one_le_rpow hc1 (by norm_num)
      have hδ12 : δ ^ (1 - (3 / 2 : ℝ)) ≤ a₀ ^ (-(1 / 2 : ℝ)) * c ^ (1 / 4 : ℝ) := by
        have h1 : δ ^ (-(1 / 2 : ℝ)) ≤ (a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hδ_lo (by norm_num)
        rw [show 1 - (3 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num]; refine h1.trans_eq ?_
        rw [Real.mul_rpow ha₀.le (by positivity), ← Real.rpow_mul hc0.le]; norm_num
      nlinarith only [hc14, hδ12]
    have hterm1 : Cloc3 * (M3_0 * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ))) *
          ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹) ≤
        Cloc3 * (M3_0 * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ))) * K_L * K1 * c ^ (-(7 / 4 : ℝ)) := by
      calc Cloc3 * (M3_0 * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ))) * ((c ^ 2)⁻¹ * L⁻¹ + (c ^ 3)⁻¹ * (L ^ 3)⁻¹)
          ≤ Cloc3 * (M3_0 * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ)) * K1 * c ^ (-(1 / 4 : ℝ))) * (K_L * c ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hL_rpow_inv (mul_nonneg hCloc3 hMloc3)
        _ = Cloc3 * (M3_0 * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ))) * K1 * (c ^ (-(1 / 4 : ℝ)) * (K_L * c ^ (-(3 / 2 : ℝ)))) := by ring
        _ = Cloc3 * (M3_0 * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ))) * K_L * K1 * c ^ (-(7 / 4 : ℝ)) := by rw [h14_74]; ring
    have hterm2 : Cloc3 * (M3_0 * K1 * c⁻¹) * bumpLambda (3 / 2) δ * ((c ^ 2)⁻¹ * δ) ≤
        Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1 * c ^ (-(7 / 4 : ℝ)) := by
      have hc114 : c⁻¹ * c ^ (1 / 4 : ℝ) ≤ 1 := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]
        exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
      have hc2_nn : 0 ≤ (c ^ 2)⁻¹ * δ := by positivity
      calc Cloc3 * (M3_0 * K1 * c⁻¹) * bumpLambda (3 / 2) δ * ((c ^ 2)⁻¹ * δ)
          ≤ Cloc3 * (M3_0 * K1 * c⁻¹) * ((1 + a₀ ^ (-(1 / 2 : ℝ))) * c ^ (1 / 4 : ℝ)) * (a₁ * c ^ (-(7 / 4 : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hlam3 (by positivity)) h52_74 hc2_nn (by positivity)
        _ = Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1 * (c⁻¹ * c ^ (1 / 4 : ℝ)) * c ^ (-(7 / 4 : ℝ)) := by ring
        _ ≤ Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1 * 1 * c ^ (-(7 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc114 (by positivity)) (Real.rpow_nonneg hc0.le _)
        _ = Cloc3 * M3_0 * (1 + a₀ ^ (-(1 / 2 : ℝ))) * a₁ * K1 * c ^ (-(7 / 4 : ℝ)) := by ring
    exact hloc.trans (by dsimp only [E3]; linarith only [hterm1, hterm2])
  have hM0' : 0 ≤ M_B0 + M_BK * K1 * c⁻¹ := by positivity
  have ha0_sq : 1 ≤ a₀ * Real.sqrt c := by
    have h1 : 1 / a₀ + 1 ≤ Real.sqrt c := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / a₀ + 1)]; exact Real.sqrt_le_sqrt hcr1'
    have h2 : 1 ≤ a₀ * (1 / a₀ + 1) := by field_simp; linarith only [ha₀]
    calc 1 ≤ a₀ * (1 / a₀ + 1) := h2
      _ ≤ a₀ * Real.sqrt c := mul_le_mul_of_nonneg_left h1 ha₀.le
  have hrefl_bd : ‖bumpHrefl c B ξ‖ ≤ (Er0 + Er1 * K1) * c ^ (-(7 / 4 : ℝ)) :=
    mid_refl_seven_quarter hCr0 hκr0 hMBK hK1 hM0' hc1 hc0
      (hrefl B δ (M_B0 + M_BK * K1 * c⁻¹) c ξ hδ0 hδ1' hδ32 hM0' hc2 ha0_sq hsqrt_δ hξ hprof).1
  have hBnn : 0 ≤ B L := hB_nonneg K1 hK1 ε c hε hcpos' L hL_hi
  have hmain_eq : bumpHmain c B ξ =
      (n : ℂ) * (bumpHmain c p1 ξ + bumpHmain c p2 ξ + bumpHmain c p3 ξ + bumpHmain c p4 ξ) := by
    change bumpHmain c (physBump χ n c δ s K1 K4 O F T4) ξ = _
    rw [hBeq]
    exact bumpHmain_lin4 hc1 hδ0 hδ32 le_rfl (by norm_num) le_rfl le_rfl
      hM1 (by positivity) (by positivity) hM4 hξ
      (hbs1.profile hM1) (hbs2.profile (by positivity)) (hbs3.profile (by positivity)) (hbs4.profile hM4)
  have hBL_eq : n * (c⁻¹ * p1 L + c⁻¹ * p2 L + c⁻¹ * p3 L + c⁻¹ * p4 L) = c⁻¹ * B L := by
    change _ = c⁻¹ * (physBump χ n c δ s K1 K4 O F T4 L)
    rw [hBeq]; dsimp only; ring
  have hmain_re : -(2 * (E1 + E4 + (E2 + E3) * K1) * c ^ (-(7 / 4 : ℝ))) ≤ (bumpHmain c B ξ).re - c⁻¹ * B L := by
    have hre_diff : (bumpHmain c B ξ).re - c⁻¹ * B L =
        n * ((bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re + (bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re +
          (bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re + (bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re) := by
      rw [hmain_eq, ← hBL_eq]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.sub_re,
        zero_mul, sub_zero]
      ring
    have habs : |(bumpHmain c B ξ).re - c⁻¹ * B L| ≤ 2 * (E1 + E4 + (E2 + E3) * K1) * c ^ (-(7 / 4 : ℝ)) := by
      rw [hre_diff, abs_mul, abs_of_nonneg (by linarith only [hn_lo])]
      have a1 := (Complex.abs_re_le_norm _).trans hp1_bd
      have a2 := (Complex.abs_re_le_norm _).trans hp2_bd
      have a3 := (Complex.abs_re_le_norm _).trans hp3_bd
      have a4 := (Complex.abs_re_le_norm _).trans hp4_bd
      have hs : |(bumpHmain c p1 ξ - ((c⁻¹ * p1 L : ℝ) : ℂ)).re + (bumpHmain c p2 ξ - ((c⁻¹ * p2 L : ℝ) : ℂ)).re +
            (bumpHmain c p3 ξ - ((c⁻¹ * p3 L : ℝ) : ℂ)).re + (bumpHmain c p4 ξ - ((c⁻¹ * p4 L : ℝ) : ℂ)).re| ≤
          (E1 + E4 + (E2 + E3) * K1) * c ^ (-(7 / 4 : ℝ)) := by
        have htri := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add ((abs_add_le _ _).trans (add_le_add a1 a2)) a3)) a4)
        linarith only [htri]
      calc n * |_| ≤ 2 * ((E1 + E4 + (E2 + E3) * K1) * c ^ (-(7 / 4 : ℝ))) := mul_le_mul hn_hi hs (abs_nonneg _) zero_le_two
        _ = 2 * (E1 + E4 + (E2 + E3) * K1) * c ^ (-(7 / 4 : ℝ)) := by ring
    linarith only [(abs_le.mp habs).1]
  have href_re : -((Er0 + Er1 * K1) * c ^ (-(7 / 4 : ℝ))) ≤ ((ε : ℂ) * bumpHrefl c B ξ).re := by
    have ha : |((ε : ℂ) * bumpHrefl c B ξ).re| ≤ (Er0 + Er1 * K1) * c ^ (-(7 / 4 : ℝ)) := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rcases hε with rfl | rfl <;> simp [hrefl_bd]
    linarith only [(abs_le.mp ha).1]
  change -(C0 + C1 * K1) * c ^ (-(7 / 4 : ℝ)) ≤ normDensity (ctWbump B ε c) c ξ
  rw [normDensity_ctWbump hc1 hδ0 hδ32 le_rfl hM0' hξ hprof, Complex.add_re]
  have hcB_nn : 0 ≤ c⁻¹ * B L := mul_nonneg (inv_nonneg.mpr hc0.le) hBnn
  dsimp only [C0, C1]
  linarith only [hmain_re, href_re, hcB_nn]

/-- info: 'FormalResearch.SignUncertainty.physBump_mid_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physBump_mid_lower

end FormalResearch.SignUncertainty
