/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctTotSplit
public import FormalResearch.SignUncertainty.FctBump5
public import FormalResearch.SignUncertainty.FctRSymbol

/-!
# Four-regime bounds for the physical bump `ctWbump (fctBphys ...)` (Step 2)

For `K₄ ≥ 1`, `(T₁, α)` solving the zero condition (`FctWarpZeroStmt`), `N_c = 1 + O(c⁻¹)` (`FctSplittingNormStmt`),
and `B(K₁, ε, c) := physBump fctChi (1 / N_c) c (physDelta c) (physShift ε c) K₁ K₄ O F T₄`, proves:

* `fctBphys_nonneg_le_three_delta`: `0 ≤ B(K₁, ε, c)(L)` for all `L ≤ 3 δ_L`, `K₁ ≥ 0`, `c ≥ c₀(K₄)` (`c₀` independent of `K₁`);
* `fctBphys_pretrans_bound`: for `L ≤ 3 δ_L / 4`, `‖normDensity (ctWbump B ε c) c ξ‖ ≤ c^{-2}` (`c ≥ c₁(K₄, K₁)`);
* `fctBphys_mid_lower`: for `3 δ_L / 4 ≤ L ≤ 3 δ_L`, `normDensity (ctWbump B ε c) c ξ ≥ -(C₀(K₄) + C₁(K₄) K₁) c^{-7/4}`;
* `fctBphys_mac_lower`: for `3 δ_L ≤ L ≤ (1/4) log c`, explicit lower bound matching `(O - F) + η(O + F)`;
* `fctBphys_far_lower`: for `(1/4) log c ≤ L`, `normDensity (ctWbump B ε c) c ξ ≥ c⁻¹ B(L) - C(K₄, K₁) c⁻² L⁻²`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctSym
open FormalResearch.SignUncertainty.FctCompD

namespace FormalResearch.SignUncertainty

section Linearity

lemma bumpLaplace_add {B1 B2 : ℝ → ℝ} {b δ M1 M2 α1 α2 β1 β2 : ℝ} {K1 K2 : ℕ → ℝ}
    (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ1 : 1 < β1) (hβ2 : 1 < β2)
    (h1 : BumpProfile b δ M1 α1 β1 K1 B1) (h2 : BumpProfile b δ M2 α2 β2 K2 B2)
    {s : ℂ} (hs : 0 ≤ s.re) :
    bumpLaplace (fun x => B1 x + B2 x) s = bumpLaplace B1 s + bumpLaplace B2 s := by
  have i1 : Integrable (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (B1 x : ℂ)) := by
    simpa using h1.integrable_laplace_mul hb0 hbδ hβ1 0 hs
  have i2 : Integrable (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (B2 x : ℂ)) := by
    simpa using h2.integrable_laplace_mul hb0 hbδ hβ2 0 hs
  unfold bumpLaplace
  have hpt : (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (((B1 x + B2 x : ℝ) : ℂ))) =
      fun x : ℝ => Complex.exp (-s * (x : ℂ)) * ((B1 x : ℂ)) + Complex.exp (-s * (x : ℂ)) * ((B2 x : ℂ)) := by
    funext x; push_cast; ring
  rw [hpt, integral_add i1 i2]

lemma bumpLaplace_const_mul (a : ℝ) (B : ℝ → ℝ) (s : ℂ) :
    bumpLaplace (fun x => a * B x) s = (a : ℂ) * bumpLaplace B s := by
  unfold bumpLaplace
  have hpt : (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (((a * B x : ℝ) : ℂ))) =
      fun x : ℝ => (a : ℂ) * (Complex.exp (-s * (x : ℂ)) * ((B x : ℂ))) := by
    funext x; push_cast; ring
  rw [hpt, integral_const_mul]

lemma bumpHmain_add {B1 B2 : ℝ → ℝ} {δ M1 M2 α1 α2 β1 β2 c ξ : ℝ} {K1 K2 : ℕ → ℝ}
    (hc : 1 ≤ c) (hδ0 : 0 < δ) (hδ1 : 3 / 2 * δ ≤ 1) (hβ1 : 3 / 2 ≤ β1) (hβ2 : 3 / 2 ≤ β2)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hξ : 0 < ξ)
    (h1 : BumpProfile (3 / 2) δ M1 α1 β1 K1 B1) (h2 : BumpProfile (3 / 2) δ M2 α2 β2 K2 B2) :
    bumpHmain c (fun x => B1 x + B2 x) ξ = bumpHmain c B1 ξ + bumpHmain c B2 ξ := by
  have hb0 : 0 ≤ (3 / 2 : ℝ) * δ := by positivity
  have i1 := bumpDW_edge_integrable hc hδ0 hδ1 hβ1 hM1 hξ h1
  have i2 := bumpDW_edge_integrable hc hδ0 hδ1 hβ2 hM2 hξ h2
  have hpt : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c (fun x => B1 x + B2 x) ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B1 ((τ : ℂ) * Complex.I) +
        mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B2 ((τ : ℂ) * Complex.I) := by
    funext τ
    have hre : ((c : ℂ) * ((τ : ℂ) * Complex.I)).re = 0 := by simp
    unfold bumpDW
    rw [bumpLaplace_add hb0 hδ1 (by linarith) (by linarith) h1 h2 hre.ge]
    ring
  unfold bumpHmain
  rw [hpt, integral_add i1 i2]
  ring

lemma bumpHmain_const_mul (a c : ℝ) (B : ℝ → ℝ) (ξ : ℝ) :
    bumpHmain c (fun x => a * B x) ξ = (a : ℂ) * bumpHmain c B ξ := by
  unfold bumpHmain
  have hpt : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c (fun x => a * B x) ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ => (a : ℂ) * (mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B ((τ : ℂ) * Complex.I)) := by
    funext τ; unfold bumpDW; rw [bumpLaplace_const_mul]; ring
  rw [hpt, integral_const_mul]
  ring

end Linearity

section BumpNonneg

private lemma symW_mΦ_nonneg {δ MΦ α β : ℝ} {KΦ : ℕ → ℝ} {F : ℝ → ℝ}
    (hδ0 : 0 < δ) (hF : SymW (Ici (3 / 2 * δ)) (pw MΦ α β) KΦ F) : 0 ≤ MΦ := by
  have h := hF.w_nonneg (3 / 2 * δ) le_rfl
  by_cases h1 : 3 / 2 * δ ≤ 1
  · have hp : pw MΦ α β (3 / 2 * δ) = MΦ * (3 / 2 * δ) ^ (-α) := by simp only [pw, h1, ↓reduceIte]
    rw [hp] at h
    exact nonneg_of_mul_nonneg_left h (Real.rpow_pos_of_pos (by positivity) _)
  · have hp : pw MΦ α β (3 / 2 * δ) = MΦ * (3 / 2 * δ) ^ (-β) := by simp only [pw, h1, ↓reduceIte]
    rw [hp] at h
    exact nonneg_of_mul_nonneg_left h (Real.rpow_pos_of_pos (by positivity) _)

private lemma rpow_three_halves_div_le {a b : ℝ} (hb : 0 < b) (hab : a ≤ 10 / 9 * b) (ha : 0 < a) :
    a ^ (3 / 2 : ℝ) ≤ 11 / 9 * b ^ (3 / 2 : ℝ) := by
  have h1 : a ^ 3 ≤ (10 / 9 * b) ^ 3 := pow_le_pow_left₀ ha.le hab 3
  have h2 : (10 / 9 : ℝ) ^ 3 ≤ (11 / 9 : ℝ) ^ 2 := by norm_num
  have h3 : (a ^ (3 / 2 : ℝ)) ^ 2 = a ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]; norm_num
  have h4 : (11 / 9 * b ^ (3 / 2 : ℝ)) ^ 2 = (11 / 9) ^ 2 * b ^ 3 := by
    have hb3 : (b ^ (3 / 2 : ℝ)) ^ 2 = b ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]; norm_num
    rw [mul_pow, hb3]
  have h5 : (a ^ (3 / 2 : ℝ)) ^ 2 ≤ (11 / 9 * b ^ (3 / 2 : ℝ)) ^ 2 := by
    rw [h3, h4]
    calc a ^ 3 ≤ (10 / 9) ^ 3 * b ^ 3 := by convert h1 using 1; ring
      _ ≤ (11 / 9) ^ 2 * b ^ 3 := mul_le_mul_of_nonneg_right h2 (by positivity)
  have hb0 : 0 ≤ 11 / 9 * b ^ (3 / 2 : ℝ) := by positivity
  nlinarith [sq_nonneg (a ^ (3 / 2 : ℝ) - 11 / 9 * b ^ (3 / 2 : ℝ)), Real.rpow_nonneg ha.le (3 / 2 : ℝ)]

private lemma tau0_ratio_bound {T1 : ℝ → ℝ → ℝ}
    (hT1 : ∃ C1 c1 : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c1 ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C1 * c⁻¹) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∀ L : ℝ,
      3 / 2 * physDelta c ≤ L → L ≤ 3 * physDelta c →
        0 < L - physShift ε c ∧ L - physShift ε c ≤ 31 / 10 * physDelta c ∧
        tau0 (L - physShift ε c) ≤ 2 * c ^ (-(1 / 4 : ℝ)) ∧
        tau0 (L - physShift ε c) ^ 4 ≤ 11 / 10 * tau0 L ^ 4 ∧
        (L - physShift ε c) / (L - physL1 T1 ε c) ≤ 11 / 10 ∧
        uctIfl (L - physShift ε c) ≤ 11 / 9 * uctIfl L ∧
        1 / 2 * L ≤ L - physShift ε c := by
  obtain ⟨cτ, hcτ, htau_lo⟩ := FctSym.tau0_sq_ge
  obtain ⟨Kθ, hKθ⟩ := ctTheta1_bound
  have hKθ0 : 0 ≤ Kθ := (abs_nonneg _).trans (hKθ 0)
  obtain ⟨KL, cL, hcL1, hL⟩ := physL1_le T1 hT1
  have hKL0 : 0 ≤ KL := by
    have := hL 1 (max cL 1) (Or.inl rfl) (le_max_left _ _)
    have h0 : 0 < (max cL 1) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h0
    linarith [abs_nonneg (physL1 T1 1 (max cL 1))]
  obtain ⟨cs, a₀, a₁, hcs, ha₀, hsc⟩ := physDatum_scales T1 hT1
  obtain ⟨c₁, hc₁1, hc₁⟩ := FctSym.exists_rpow_neg_le (p := 1 / 4) (η := (1 / 20 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨c₂, hc₂1, hc₂⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2)
    (η := (3 * a₀ / 2) / (50 * (Kθ + 1))) (by norm_num) (by positivity)
  obtain ⟨c₃, hc₃1, hc₃⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2)
    (η := 1 / (6 * (|a₁| + 1))) (by norm_num)
    (one_div_pos.mpr (mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg a₁) one_pos)))
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  obtain ⟨c₄, hc₄1, hc₄⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2)
    (η := (Real.pi ^ 2 * (cτ * (3 * a₀ / 4))) / (350 * (Kθ + 1))) (by norm_num)
    (div_pos (mul_pos (pow_pos Real.pi_pos 2) (mul_pos hcτ (by positivity))) (by positivity))
  obtain ⟨c₅, hc₅1, hc₅⟩ := FctSym.exists_rpow_neg_le (p := 1 / 6)
    (η := (3 * a₀ / 2) / (50 * (KL + 1))) (by norm_num) (by positivity)
  refine ⟨max (max (max cs cL) (max c₁ c₂)) (max (max c₃ c₄) c₅),
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left hcs)), fun ε c hε hc L hLlo hLhi => ?_⟩
  have hcs' : cs ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _) |>.trans hc
  have hcL' : cL ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _) |>.trans hc
  have hc1' : c₁ ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _) |>.trans hc
  have hc2' : c₂ ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _) |>.trans hc
  have hc3' : c₃ ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _) |>.trans hc
  have hc4' : c₄ ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _) |>.trans hc
  have hc5' : c₅ ≤ c := (le_max_right _ _).trans (le_max_right _ _) |>.trans hc
  obtain ⟨hδ0, -, -, -, -, -, hδ_lo, hδ_hi, h6δ⟩ := hsc ε c hε hcs'
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := hcs.trans hcs'
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ)) with hτ₁def
  have hτ₁pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_le : τ₁ ≤ 1 / 20 := hc₁ c hc1'
  have hτ₁_16 : τ₁ ≤ 1 / 16 := by linarith
  have hτ₁_two : τ₁ ≤ 1 / 20 := hτ₁_le
  have hs_abs : |physShift ε c| ≤ Kθ * c⁻¹ := by
    unfold physShift
    rw [abs_div, abs_of_pos hc0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hKθ ε) (inv_nonneg.mpr hc0.le)
  have hL1_abs : |physL1 T1 ε c| ≤ KL * c ^ (-(2 / 3 : ℝ)) := hL ε c hε hcL'
  have hc_half_sq : (c ^ (-(1 / 2 : ℝ))) ^ 2 = c⁻¹ := by
    rw [← Real.rpow_natCast (c ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hc0.le,
      show (-(1 / 2 : ℝ)) * (2 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
  have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    rw [hτ₁def, ← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
  have hτ₁_four : τ₁ ^ 4 = c⁻¹ := by rw [show τ₁ ^ 4 = (τ₁ ^ 2) ^ 2 by ring, hτ₁_sq, hc_half_sq]
  have hLpos : 0 < L := by linarith only [hδ0, hLlo]
  have hs_L : |physShift ε c| ≤ 1 / 50 * L := by
    have hch := hc₂ c hc2'
    have h3 : c⁻¹ ≤ (3 * a₀ / 2 / (50 * (Kθ + 1))) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← hc_half_sq, _root_.sq]
      exact mul_le_mul_of_nonneg_right hch (by positivity)
    have hk_rat : Kθ / (Kθ + 1) ≤ 1 := by rw [div_le_one (by linarith only [hKθ0])]; linarith only [hKθ0]
    have hc12_pos : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
    calc |physShift ε c| ≤ Kθ * c⁻¹ := hs_abs
      _ ≤ Kθ * ((3 * a₀ / 2 / (50 * (Kθ + 1))) * c ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h3 hKθ0
      _ = 1 / 50 * (3 / 2 * (a₀ * c ^ (-(1 / 2 : ℝ)))) * (Kθ / (Kθ + 1)) := by field_simp
      _ ≤ 1 / 50 * (3 / 2 * (a₀ * c ^ (-(1 / 2 : ℝ)))) * 1 :=
          mul_le_mul_of_nonneg_left hk_rat (by positivity)
      _ = 1 / 50 * (3 / 2 * (a₀ * c ^ (-(1 / 2 : ℝ)))) := mul_one _
      _ ≤ 1 / 50 * (3 / 2 * physDelta c) := by gcongr
      _ ≤ 1 / 50 * L := by gcongr
  have hL1_L : |physL1 T1 ε c| ≤ 1 / 50 * L := by
    have hch := hc₅ c hc5'
    have h23 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    have hkl_rat : KL / (KL + 1) ≤ 1 := by rw [div_le_one (by linarith only [hKL0])]; linarith only [hKL0]
    have hc12_pos : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
    calc |physL1 T1 ε c| ≤ KL * c ^ (-(2 / 3 : ℝ)) := hL1_abs
      _ = KL * (c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ))) := by rw [h23]
      _ ≤ KL * ((3 * a₀ / 2 / (50 * (KL + 1))) * c ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = 1 / 50 * (3 / 2 * (a₀ * c ^ (-(1 / 2 : ℝ)))) * (KL / (KL + 1)) := by field_simp
      _ ≤ 1 / 50 * (3 / 2 * (a₀ * c ^ (-(1 / 2 : ℝ)))) * 1 :=
          mul_le_mul_of_nonneg_left hkl_rat (by positivity)
      _ = 1 / 50 * (3 / 2 * (a₀ * c ^ (-(1 / 2 : ℝ)))) := mul_one _
      _ ≤ 1 / 50 * (3 / 2 * physDelta c) := by gcongr
      _ ≤ 1 / 50 * L := by gcongr
  have hLs_lo : 49 / 50 * L ≤ L - physShift ε c := by linarith [(abs_le.mp hs_L).2]
  have hLs_hi : L - physShift ε c ≤ 51 / 50 * L := by linarith [(abs_le.mp hs_L).1]
  have hLs_pos : 0 < L - physShift ε c := by nlinarith
  have hLs_31 : L - physShift ε c ≤ 31 / 10 * physDelta c := by linarith [hδ0]
  have hu_lt : L - physShift ε c < uctM (2 * τ₁) := by
    have h31 := uctM_two_gt_31 hτ₁pos (by linarith)
    change L - physShift ε c ≤ 31 / 10 * uctM τ₁ at hLs_31
    linarith
  have ht2 : tau0 (L - physShift ε c) ≤ 2 * τ₁ := (tau0_lt_of_lt (by positivity) hLs_pos hu_lt).le
  have hL_12 : 3 / 4 * physDelta c ≤ min L (L - physShift ε c) := le_min (by linarith) (by linarith)
  have hmax_le1 : max L (L - physShift ε c) ≤ 1 := max_le (by linarith) (by linarith)
  have hmin_pos : 0 < min L (L - physShift ε c) := by positivity
  have htau_a_pos : 0 < tau0 (min L (L - physShift ε c)) := tau0_pos hmin_pos
  have htau_a_sq : cτ * (3 * a₀ / 4) * τ₁ ^ 2 ≤ tau0 (min L (L - physShift ε c)) ^ 2 := by
    have ha_lo : 3 * a₀ / 4 * τ₁ ^ 2 ≤ min L (L - physShift ε c) := by
      have h1 : 3 / 4 * (a₀ * τ₁ ^ 2) ≤ 3 / 4 * physDelta c := by
        rw [hτ₁_sq]; exact mul_le_mul_of_nonneg_left hδ_lo (by norm_num)
      linarith only [h1, hL_12]
    have hmin_le1 : min L (L - physShift ε c) ≤ 1 :=
      (min_le_left _ _).trans ((le_max_left _ _).trans hmax_le1)
    have hL_sq : cτ * min L (L - physShift ε c) ≤ tau0 (min L (L - physShift ε c)) ^ 2 :=
      htau_lo (min L (L - physShift ε c)) ⟨hmin_pos, hmin_le1⟩
    linarith only [hL_sq, mul_le_mul_of_nonneg_left ha_lo hcτ.le]
  have htau_b_hi : tau0 (max L (L - physShift ε c)) ≤ 2 * τ₁ := by
    rcases le_or_gt (L - physShift ε c) L with hle | hgt
    · rw [max_eq_left hle]
      have : L < uctM (2 * τ₁) := by
        have h31 := uctM_two_gt_31 hτ₁pos (by linarith only [hτ₁_le])
        change L ≤ 3 * uctM τ₁ at hLhi
        linarith only [uctM_pos hτ₁pos, hLhi, h31]
      exact (tau0_lt_of_lt (by positivity) hLpos this).le
    · rw [max_eq_right hgt.le]; exact ht2
  have hm_inv : ∀ x ∈ Icc (min L (L - physShift ε c)) (max L (L - physShift ε c)),
      ‖deriv tau0 x‖ ≤ 7 / (Real.pi ^ 2 * tau0 (min L (L - physShift ε c))) := by
    intro x hx
    have hx0 : 0 < x := hmin_pos.trans_le hx.1
    rw [deriv_tau0 hx0, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mPrime_pos (tau0_pos hx0)))]
    have htx_lo : tau0 (min L (L - physShift ε c)) ≤ tau0 x := tau0_mono hmin_pos hx.1
    have htx_hi : tau0 x ≤ tau0 (max L (L - physShift ε c)) := tau0_mono hx0 hx.2
    have htx_le1 : tau0 x ≤ 1 / 8 := by linarith only [htx_hi, htau_b_hi, hτ₁_16]
    have hth := theta_ge (tau0_pos hx0)
    have hpi2 : (Real.pi * tau0 x) ^ 2 ≤ 1 := by
      have hbd : Real.pi * tau0 x ≤ 4 * (1 / 8) :=
        mul_le_mul Real.pi_lt_four.le htx_le1 (tau0_pos hx0).le (by norm_num)
      have h0 : 0 ≤ Real.pi * tau0 x := mul_nonneg Real.pi_pos.le (tau0_pos hx0).le
      nlinarith only [hbd, h0]
    have hm1 : (Real.pi ^ 2 / 7) * tau0 x ≤ CtOuter.mPrime (tau0 x) := by
      have h1 : (Real.pi * tau0 x) ^ 2 / 7 ≤ (Real.pi * tau0 x) ^ 2 / (6 + (Real.pi * tau0 x) ^ 2) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith only [hpi2])
      have h2 := h1.trans hth
      have h3 : (Real.pi ^ 2 / 7) * tau0 x * tau0 x ≤ CtOuter.mPrime (tau0 x) * tau0 x := by
        calc (Real.pi ^ 2 / 7) * tau0 x * tau0 x = (Real.pi * tau0 x) ^ 2 / 7 := by ring
          _ ≤ tau0 x * CtOuter.mPrime (tau0 x) := h2
          _ = CtOuter.mPrime (tau0 x) * tau0 x := mul_comm _ _
      exact le_of_mul_le_mul_right h3 (tau0_pos hx0)
    rw [inv_eq_one_div, div_le_div_iff₀ (mPrime_pos (tau0_pos hx0)) (by positivity)]
    calc 1 * (Real.pi ^ 2 * tau0 (min L (L - physShift ε c)))
        = 7 * ((Real.pi ^ 2 / 7) * tau0 (min L (L - physShift ε c))) := by ring
      _ ≤ 7 * ((Real.pi ^ 2 / 7) * tau0 x) := by gcongr
      _ ≤ 7 * CtOuter.mPrime (tau0 x) := by gcongr
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := tau0)
    (C := 7 / (Real.pi ^ 2 * tau0 (min L (L - physShift ε c))))
    (s := Icc (min L (L - physShift ε c)) (max L (L - physShift ε c))) (x := L) (y := L - physShift ε c)
    (fun x hx => (hasDerivAt_tau0 (hmin_pos.trans_le hx.1)).differentiableAt)
    hm_inv (convex_Icc _ _) ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
  simp only [Real.norm_eq_abs, show L - physShift ε c - L = -physShift ε c by ring, abs_neg] at hmvt
  have hτaL : tau0 (min L (L - physShift ε c)) ≤ tau0 L := tau0_mono hmin_pos (min_le_left _ _)
  have hc4_bd : τ₁ ^ 2 ≤ Real.pi ^ 2 * (cτ * (3 * a₀ / 4)) / (350 * (Kθ + 1)) := by
    rw [hτ₁_sq]; exact hc₄ c hc4'
  have htau_a_le : 7 * Kθ * τ₁ ^ 4 ≤ 1 / 50 * (Real.pi ^ 2 * tau0 (min L (L - physShift ε c)) ^ 2) := by
    have h1 : 350 * (Kθ + 1) * τ₁ ^ 2 ≤ Real.pi ^ 2 * (cτ * (3 * a₀ / 4)) := by
      rw [le_div_iff₀ (by positivity)] at hc4_bd; linarith only [hc4_bd]
    have h2 : 350 * (Kθ + 1) * τ₁ ^ 4 ≤ Real.pi ^ 2 * (cτ * (3 * a₀ / 4) * τ₁ ^ 2) := by
      calc 350 * (Kθ + 1) * τ₁ ^ 4 = (350 * (Kθ + 1) * τ₁ ^ 2) * τ₁ ^ 2 := by ring
        _ ≤ (Real.pi ^ 2 * (cτ * (3 * a₀ / 4))) * τ₁ ^ 2 := by gcongr
        _ = Real.pi ^ 2 * (cτ * (3 * a₀ / 4) * τ₁ ^ 2) := by ring
    have h3 : 350 * Kθ * τ₁ ^ 4 ≤ Real.pi ^ 2 * tau0 (min L (L - physShift ε c)) ^ 2 := by
      calc 350 * Kθ * τ₁ ^ 4 ≤ 350 * (Kθ + 1) * τ₁ ^ 4 := by nlinarith only [hKθ0, pow_nonneg hτ₁pos.le 4]
        _ ≤ Real.pi ^ 2 * (cτ * (3 * a₀ / 4) * τ₁ ^ 2) := h2
        _ ≤ Real.pi ^ 2 * tau0 (min L (L - physShift ε c)) ^ 2 := by gcongr
    linarith only [h3]
  have hLip : |tau0 (L - physShift ε c) - tau0 L| ≤ 1 / 50 * tau0 L := by
    have h1 : 7 / (Real.pi ^ 2 * tau0 (min L (L - physShift ε c))) * |physShift ε c| ≤
        1 / 50 * tau0 (min L (L - physShift ε c)) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc 7 * |physShift ε c| ≤ 7 * (Kθ * τ₁ ^ 4) := by rw [hτ₁_four]; gcongr
        _ = 7 * Kθ * τ₁ ^ 4 := by ring
        _ ≤ 1 / 50 * (Real.pi ^ 2 * tau0 (min L (L - physShift ε c)) ^ 2) := htau_a_le
        _ = 1 / 50 * tau0 (min L (L - physShift ε c)) * (Real.pi ^ 2 * tau0 (min L (L - physShift ε c))) := by ring
    exact hmvt.trans (h1.trans (by linarith))
  have htau_pow4 : tau0 (L - physShift ε c) ^ 4 ≤ 11 / 10 * tau0 L ^ 4 := by
    have hle : tau0 (L - physShift ε c) ≤ 51 / 50 * tau0 L := by linarith [(abs_le.mp hLip).2]
    have h0 : 0 ≤ tau0 (L - physShift ε c) := (tau0_pos hLs_pos).le
    have h4 : tau0 (L - physShift ε c) ^ 4 ≤ (51 / 50 * tau0 L) ^ 4 := pow_le_pow_left₀ h0 hle 4
    have hnum : (51 / 50 : ℝ) ^ 4 ≤ 11 / 10 := by norm_num
    calc tau0 (L - physShift ε c) ^ 4 ≤ (51 / 50) ^ 4 * tau0 L ^ 4 := by convert h4 using 1; ring
      _ ≤ 11 / 10 * tau0 L ^ 4 := mul_le_mul_of_nonneg_right hnum (pow_nonneg (tau0_pos hLpos).le 4)
  have hratio_L : (L - physShift ε c) / (L - physL1 T1 ε c) ≤ 11 / 10 := by
    have hden : 49 / 50 * L ≤ L - physL1 T1 ε c := by linarith [(abs_le.mp hL1_L).2]
    rw [div_le_iff₀ (by linarith)]; linarith
  have hratio_ifl : uctIfl (L - physShift ε c) ≤ 11 / 9 * uctIfl L := by
    unfold uctIfl
    have hα0 := uctAlphaFl_pos
    have hLrat : L ≤ 10 / 9 * (L - physShift ε c) := by linarith
    have hpow := rpow_three_halves_div_le hLs_pos hLrat hLpos
    rw [Real.rpow_neg hLs_pos.le, Real.rpow_neg hLpos.le, mul_left_comm (11 / 9 : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ hα0.le
    rw [inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hLs_pos _)]
    calc (1 : ℝ) = (L ^ (3 / 2 : ℝ))⁻¹ * L ^ (3 / 2 : ℝ) := (inv_mul_cancel₀ (Real.rpow_pos_of_pos hLpos _).ne').symm
      _ ≤ (L ^ (3 / 2 : ℝ))⁻¹ * (11 / 9 * (L - physShift ε c) ^ (3 / 2 : ℝ)) := by gcongr
      _ = 11 / 9 * (L ^ (3 / 2 : ℝ))⁻¹ * (L - physShift ε c) ^ (3 / 2 : ℝ) := by ring
  refine ⟨hLs_pos, hLs_31, ht2, htau_pow4, hratio_L, hratio_ifl, by linarith⟩

private lemma vacP_inner_eq :
    ∃ τc : ℝ, 0 < τc ∧ ∀ {K4 c α τ₁ t : ℝ}, 1 ≤ K4 → 0 < c → 0 < τ₁ → τ₁ ≤ τc → τ₁ ^ 4 * c = 1 →
      |α| ≤ τ₁ ^ 2 → 0 < t → t ≤ 2 * τ₁ →
      vacP StripKernelChoice.star K4 c α τ₁ (uctM t) = uctIfl (uctM t) *
        (Real.exp (-(K4 * t ^ 4) + α * t ^ 2) *
          (Real.exp (-stripDeltaCurv c (FctMoment.fctThetaD (v0 StripKernelChoice.star K4 τ₁)) t) *
            (1 + stripDeltaCurv c (FctMoment.fctThetaD (v0 StripKernelChoice.star K4 τ₁)) t))) := by
  obtain ⟨τc, hτc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpart1⟩ :=
    fct_comp_D_part1 StripKernelChoice.star
  refine ⟨τc, hτc, fun {K4 c α τ₁ t} hK4 hc0 hτ₁pos hτc' hτ₁_four hα_bd htpos ht2 => ?_⟩
  obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _, _, hinner, _⟩ :=
    hpart1 hK4 hc0 hτ₁pos hτc' hτ₁_four hα_bd
  have hin := ((hinner t (by rw [abs_of_pos htpos]; exact ht2)).2.2.2.2.2 htpos.ne').2.2
  have hr0 := stripR0_pos StripKernelChoice.star htpos
  have hu_pos := uctM_pos htpos
  have hv := vacP_eq StripKernelChoice.star K4 c α τ₁ hu_pos
  have htau_id : tau0 (uctM t) = t := by
    rw [show uctM t = ceEll (Real.pi * t / 2) from rfl, tau0_ceEll htpos]
  rw [htau_id] at hv
  rw [hv]
  have hratio : stripIosc StripKernelChoice.star (uctM t) / uctIfl (uctM t) = stripR0 StripKernelChoice.star t :=
    (stripR0_eq_div htpos).symm
  rw [hratio] at hin
  set Δ := stripDeltaCurv c (FctMoment.fctThetaD (v0 StripKernelChoice.star K4 τ₁)) t
  have hexp : stripR0 StripKernelChoice.star t * Real.exp (vTotal StripKernelChoice.star K4 c α τ₁ t) * (1 + Δ) =
      Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-Δ) * (1 + Δ)) := by
    rw [hin, show -Real.log (stripR0 StripKernelChoice.star t) - K4 * t ^ 4 - Δ + α * t ^ 2 =
      -Real.log (stripR0 StripKernelChoice.star t) + ((-(K4 * t ^ 4) + α * t ^ 2) + -Δ) by ring,
      Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hr0]
    field_simp
  have hqd : vacQD StripKernelChoice.star K4 c α τ₁ t + 1 =
      stripR0 StripKernelChoice.star t * Real.exp (vTotal StripKernelChoice.star K4 c α τ₁ t) * (1 + Δ) := by
    unfold vacQD; ring
  rw [hqd, hexp]

private lemma physBump_assemble {nc χ3 χ6 γ η O F T4 K4 : ℝ}
    (hnc : 0 ≤ nc) (hχ3 : 0 ≤ χ3) (hχ6 : χ6 = 0)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hη : 0 ≤ η) (hO : 0 ≤ O) (hF : 0 < F) (hT4 : 0 ≤ T4) (hK4 : 1 ≤ K4)
    (hOF : -(14 / 10 * (121 / 90) * K4 * T4) ≤ O - F) :
    0 ≤ nc * (χ3 * γ * ((1 + η) * O - (1 - η) * F)) +
      nc * (2 * K4 * (χ3 * ((1 - χ6) * T4))) := by
  have h1 : -(14 / 10 * (121 / 90) * K4 * T4) ≤ γ * (O - F) := by
    rcases le_or_gt (O - F) 0 with hneg | hpos
    · have hpm := mul_le_mul_of_nonpos_right hγ1 hneg
      linarith only [hpm, hOF]
    · exact (neg_nonpos.mpr (by positivity)).trans (mul_nonneg hγ0 hpos.le)
  have hdiff : 0 ≤ γ * (O - F) + 2 * K4 * T4 := by
    have hK4T : 0 ≤ K4 * T4 := by positivity
    linarith only [h1, hK4T]
  have hmain : 0 ≤ γ * ((1 + η) * O - (1 - η) * F) + 2 * K4 * (1 - χ6) * T4 := by
    rw [hχ6, sub_zero, mul_one]
    have hmar : 0 ≤ γ * (η * (O + F)) := by positivity
    linarith only [hdiff, hmar]
  have ef : nc * (χ3 * γ * ((1 + η) * O - (1 - η) * F)) +
      nc * (2 * K4 * (χ3 * ((1 - χ6) * T4))) =
      nc * χ3 * (γ * ((1 + η) * O - (1 - η) * F) + 2 * K4 * (1 - χ6) * T4) := by ring
  rw [ef]
  exact mul_nonneg (mul_nonneg hnc hχ3) hmain

/-- `fct:physical-budget`: `0 ≤ physBump` for all `L ≤ 3 δ_L`, `K₁ ≥ 0`, and `c ≥ c₀(K₄)` (`c₀` independent of `K₁`). -/
theorem physBump_nonneg_le_three_delta {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K4 : ℝ} (hK4 : 1 ≤ K4)
    {T1 alpha Nc : ℝ → ℝ → ℝ}
    (hwarp : FctWarpZeroStmt T1 alpha) (hNc : FctSplittingNormStmt Nc) :
    ∃ c₀ : ℝ, 2 ≤ c₀ ∧ ∀ K1 : ℝ, 0 ≤ K1 → ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ L : ℝ, L ≤ 3 * physDelta c →
        0 ≤ physBump χ (1 / Nc ε c) c (physDelta c) (physShift ε c) K1 K4
          (physOscDatum StripKernelChoice.star K4 T1 alpha ε c) (physF (physShift ε c) (physL1 T1 ε c))
          (fun L => tau0 L ^ 4 * uctIfl L) L := by
  obtain ⟨Cw, cw, hw⟩ := hwarp
  have hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹ :=
    ⟨Cw, cw, fun ε c hε hc => (hw ε c hε hc).1⟩
  have hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) :=
    ⟨Cw, cw, fun ε c hε hc => (hw ε c hε hc).2⟩
  obtain ⟨Kα, cα, hαf⟩ := hα
  have hKα0 : 0 ≤ Kα := by
    have := hαf 1 (max cα 1) (Or.inl rfl) (le_max_left _ _)
    have h0 : 0 < (max cα 1) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h0
    linarith [abs_nonneg (alpha 1 (max cα 1))]
  obtain ⟨cs, a₀, a₁, hcs, ha₀, hsc⟩ := physDatum_scales T1 hT1
  obtain ⟨cr, hcr1, hrat⟩ := tau0_ratio_bound hT1
  obtain ⟨cτ, hcτ, htau_lo⟩ := FctSym.tau0_sq_ge
  obtain ⟨KL, cL, hcL1, hL⟩ := physL1_le T1 hT1
  have hKL0 : 0 ≤ KL := by
    have := hL 1 (max cL 1) (Or.inl rfl) (le_max_left _ _)
    have h0 : 0 < (max cL 1) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h0
    linarith [abs_nonneg (physL1 T1 1 (max cL 1))]
  obtain ⟨Kφ, hKφ1, hΦ⟩ := vacPhi_norm_le
  obtain ⟨_, cn, hnc_b⟩ := nc_inv_bound Nc hNc
  obtain ⟨τa, hτa, hτa100, hΔall⟩ := stripDeltaCurv_le_all StripKernelChoice.star
  obtain ⟨CD, hCD, hΔ⟩ := hΔall K4 hK4
  obtain ⟨τc, hτc, hvacP_inner⟩ := vacP_inner_eq
  -- Thresholds for `τ₁`:
  set cK : ℝ := cτ * (3 / 2 * a₀) with hcK
  have hcK0 : 0 < cK := by positivity
  -- Need: `τ₁ ≤ min τa τc`, `|α| ≤ τ₁²` (`c^{-1/6} ≤ 1/(Kα+1)`), `1 - ...` small error `< 1/5 * K4 * cK^2 * τ₁^4`
  obtain ⟨c_tau, hc_tau1, hc_tau⟩ := FctSym.exists_rpow_neg_le (p := 1 / 4)
    (η := min (min τa τc) (min (1 / 20) (1 / (32 * K4 + 2))))
    (by norm_num) (lt_min (lt_min hτa hτc) (lt_min (by norm_num) (by positivity)))
  obtain ⟨c_al, hc_al1, hc_al⟩ := FctSym.exists_rpow_neg_le (p := 1 / 6) (η := 1 / (Kα + 1)) (by norm_num) (by positivity)
  obtain ⟨c_err1, hc_err1_1, hc_err1⟩ := FctSym.exists_rpow_neg_le (p := 1 / 6)
    (η := (1 / 10 * K4 * cK ^ 2) / (16 * (Kα + 1) + 1)) (by norm_num) (by positivity)
  obtain ⟨c_err2, hc_err2_1, hc_err2⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2)
    (η := (1 / 10 * K4 * cK ^ 2) / (CD ^ 2 + 1)) (by norm_num) (by positivity)
  obtain ⟨c_err3, hc_err3_1, hc_err3⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2)
    (η := (1 / 10 * K4 * cK ^ 2) / (KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 + 1)) (by norm_num) (by positivity)
  obtain ⟨c_err4, hc_err4_1, hc_err4⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2)
    (η := 1 / (2 * (CD + 1))) (by norm_num) (by positivity)
  have hck_c0 : ∃ c_k : ℝ, 1 ≤ c_k ∧ ∀ c : ℝ, c_k ≤ c → K4 * cK ^ 2 * c⁻¹ ≤ 1 := by
    refine ⟨max 1 (K4 * cK ^ 2 + 1), le_max_left _ _, fun c hc => ?_⟩
    have hcpos : 0 < c := by linarith [le_max_left 1 (K4 * cK ^ 2 + 1) |>.trans hc]
    rw [mul_inv_le_iff₀ hcpos]
    linarith [le_max_right 1 (K4 * cK ^ 2 + 1) |>.trans hc]
  obtain ⟨c_k, hck1, hck⟩ := hck_c0
  obtain ⟨c_gam, hc_gam1, hc_gam⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2)
    (η := (3 / 4 * a₀) ^ 3 / (5 * Real.pi ^ 2 / 96 + 1)) (by norm_num) (by positivity)
  refine ⟨max (max (max (max (max cs cr) (max cα cL)) (max cn (max c_tau c_al)))
    (max (max c_err1 c_err2) (max c_err3 (max c_err4 c_k)))) (max c_gam 2),
    le_max_of_le_right (le_max_right _ _), ?_⟩
  intro K1 hK1 ε c hε hc L hLhi
  simp only [max_le_iff] at hc
  obtain ⟨⟨⟨⟨⟨hcs', hcr'⟩, ⟨hcα', hcL'⟩⟩, ⟨hcn', ⟨hct', hcal'⟩⟩⟩, ⟨⟨hce1', hce2'⟩, ⟨hce3', ⟨hce4', hck'⟩⟩⟩⟩, ⟨hcgam', hc2⟩⟩ := hc
  obtain ⟨hδ0, hδ1, hs_le, hL1_le, _, hsmall, hδ_lo, hδ_hi, h6δ⟩ := hsc ε c hε hcs'
  have hc0 : 0 < c := by linarith only [hc2]
  have hc1 : 1 ≤ c := by linarith only [hc2]
  rcases lt_or_ge L (3 / 2 * physDelta c) with hLlt | hLlo
  · have hχ0 : χ (L / (3 * physDelta c)) = 0 :=
      hχ.zero _ (by rw [div_le_iff₀ (by positivity)]; linarith only [hLlt])
    simp [physBump, hχ0]
  -- Now `3/2 * δ ≤ L ≤ 3 * δ`
  obtain ⟨hLs_pos, hLs_31, ht2, htau4_rat, hLrat, hIflrat, hLs_halfL⟩ := hrat ε c hε hcr' L hLlo hLhi
  set δ := physDelta c
  set s := physShift ε c
  set L1 := physL1 T1 ε c
  set u := L - s
  set t := tau0 u
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_bd : τ₁ ≤ min (min τa τc) (min (1 / 20) (1 / (32 * K4 + 2))) := hc_tau c hct'
  have hτa' : τ₁ ≤ τa := hτ₁_bd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτc' : τ₁ ≤ τc := hτ₁_bd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτ16 : τ₁ ≤ 1 / 20 := hτ₁_bd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτK4 : τ₁ ≤ 1 / (32 * K4 + 2) := hτ₁_bd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
  have hτ₁_four : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by
      rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 4, ← Real.rpow_mul hc0.le,
        show (-(1 / 4 : ℝ)) * (4 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
    rw [this]; field_simp
  have hα_bd : |alpha ε c| ≤ τ₁ ^ 2 := by
    have h1 := hαf ε c hε hcα'
    have h2 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * τ₁ ^ 2 := by
      rw [hτ₁_sq, ← Real.rpow_add hc0]; norm_num
    have h3 : Kα * c ^ (-(1 / 6 : ℝ)) ≤ 1 := by
      have hcal_c := hc_al c hcal'
      have hKrat : Kα / (Kα + 1) ≤ 1 := by rw [div_le_one (by linarith only [hKα0])]; linarith only [hKα0]
      calc Kα * c ^ (-(1 / 6 : ℝ)) ≤ Kα * (1 / (Kα + 1)) := mul_le_mul_of_nonneg_left hcal_c hKα0
        _ = Kα / (Kα + 1) := by ring
        _ ≤ 1 := hKrat
    calc |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) := h1
      _ = (Kα * c ^ (-(1 / 6 : ℝ))) * τ₁ ^ 2 := by rw [h2]; ring
      _ ≤ 1 * τ₁ ^ 2 := by gcongr
      _ = τ₁ ^ 2 := one_mul _
  -- Exact inner `vacP` formula from `vacP_inner_eq`
  have htpos : 0 < t := tau0_pos hLs_pos
  set Δ := stripDeltaCurv c (FctMoment.fctThetaD (v0 StripKernelChoice.star K4 τ₁)) t
  have hΔ_bd : |Δ| ≤ CD * τ₁ ^ 3 := hΔ hc0 hτ₁pos hτa' hτ₁_four hα_bd t htpos
  have hΔ_half : |Δ| ≤ 1 / 2 := by
    have hτ2 : τ₁ ^ 3 ≤ c ^ (-(1 / 2 : ℝ)) := by
      rw [← hτ₁_sq]
      exact pow_le_pow_of_le_one hτ₁pos.le (by linarith only [hτ16]) (by norm_num)
    have : CD * c ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
      have hbd := hc_err4 c hce4'
      have hratCD : CD / (CD + 1) ≤ 1 := by rw [div_le_one (by linarith only [hCD])]; linarith only [hCD]
      calc CD * c ^ (-(1 / 2 : ℝ)) ≤ CD * (1 / (2 * (CD + 1))) := mul_le_mul_of_nonneg_left hbd hCD
        _ = 1 / 2 * (CD / (CD + 1)) := by field_simp
        _ ≤ 1 / 2 := by linarith only [hratCD]
    exact hΔ_bd.trans (le_trans (mul_le_mul_of_nonneg_left hτ2 hCD) this)
  have hvacP_eq : vacP StripKernelChoice.star K4 c (alpha ε c) τ₁ u =
      uctIfl u * (Real.exp (-(K4 * t ^ 4) + alpha ε c * t ^ 2) * (Real.exp (-Δ) * (1 + Δ))) := by
    have hmu : uctM t = u := ceEll_tau0 hLs_pos
    have hin := hvacP_inner hK4 hc0 hτ₁pos hτc' hτ₁_four hα_bd htpos ht2
    rw [hmu] at hin
    exact hin
  -- Lower bound on `O L / F L` and positivity `O L ≥ 0`:
  set F := physF s L1 L
  set O := physOscDatum StripKernelChoice.star K4 T1 alpha ε c L
  have hF_pos : 0 < F := physF_pos (by positivity) hs_le hL1_le hLlo
  have hO_nn : 0 ≤ O := by
    have h1 : 0 < 1 + Δ := by linarith only [(abs_le.mp hΔ_half).1]
    have h2 : 0 ≤ uctIfl u := (uctIfl_pos' hLs_pos).le
    have h3 : 0 ≤ vacP StripKernelChoice.star K4 c (alpha ε c) τ₁ u := by rw [hvacP_eq]; positivity
    have hL_L1 : 0 < L - L1 := by linarith only [(abs_le.mp hL1_le).2, hLlo, hδ0]
    unfold O physOscDatum physOsc
    exact div_nonneg (mul_nonneg h3 (norm_nonneg _)) hL_L1.le
  -- Bound `|L1 * vacPhi / u|`
  set a_phi : ℝ := c ^ (-(1 / 12 : ℝ))
  have ha_pos : 0 < a_phi := Real.rpow_pos_of_pos hc0 _
  have ha_le1 : a_phi ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hφ_bd : |L1| * ‖vacPhi a_phi u‖ / u ≤ KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 * c ^ (-(3 / 2 : ℝ)) := by
    have ha_sq : a_phi ^ 2 = c ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_natCast (c ^ (-(1 / 12 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
    have hu_hi : u ≤ 4 * a₁ * c ^ (-(1 / 2 : ℝ)) := by
      have h1 : u ≤ 4 * δ := by linarith only [hLs_31, hδ0]
      nlinarith only [h1, hδ_hi]
    have hua : u / a_phi ^ 2 ≤ 4 * a₁ * c ^ (-(1 / 3 : ℝ)) := by
      rw [ha_sq, div_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
      calc u ≤ 4 * a₁ * c ^ (-(1 / 2 : ℝ)) := hu_hi
        _ = 4 * a₁ * (c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ))) := by
            congr 1; rw [← Real.rpow_add hc0]; norm_num
        _ = 4 * a₁ * c ^ (-(1 / 3 : ℝ)) * c ^ (-(1 / 6 : ℝ)) := by ring
    have hnorm_φ : ‖vacPhi a_phi u‖ ≤ Kφ * (4 * a₁) ^ 4 * c ^ (-(4 / 3 : ℝ)) := by
      refine (hΦ ha_pos ha_le1 hLs_pos).trans ?_
      have hu4 : (u / a_phi ^ 2) ^ 4 ≤ (4 * a₁) ^ 4 * c ^ (-(4 / 3 : ℝ)) := by
        have h1 : (u / a_phi ^ 2) ^ 4 ≤ (4 * a₁ * c ^ (-(1 / 3 : ℝ))) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hua 4
        have h2 : (c ^ (-(1 / 3 : ℝ))) ^ 4 = c ^ (-(4 / 3 : ℝ)) := by
          rw [← Real.rpow_natCast (c ^ (-(1 / 3 : ℝ))) 4, ← Real.rpow_mul hc0.le]; norm_num
        calc (u / a_phi ^ 2) ^ 4 ≤ (4 * a₁ * c ^ (-(1 / 3 : ℝ))) ^ 4 := h1
          _ = (4 * a₁) ^ 4 * (c ^ (-(1 / 3 : ℝ))) ^ 4 := by ring
          _ = _ := by rw [h2]
      calc Kφ * min 1 ((u / a_phi ^ 2) ^ 4) ≤ Kφ * (u / a_phi ^ 2) ^ 4 := by
            gcongr; exact min_le_right _ _
        _ ≤ Kφ * ((4 * a₁) ^ 4 * c ^ (-(4 / 3 : ℝ))) := by gcongr
        _ = _ := by ring
    have hu_lo : 3 * a₀ / 4 * c ^ (-(1 / 2 : ℝ)) ≤ u := by
      have h1 : 3 / 4 * δ ≤ u := by linarith only [hLs_halfL, hLlo]
      nlinarith only [h1, hδ_lo]
    have hL1_c := hL ε c hε hcL'
    rw [div_le_iff₀ hLs_pos]
    have h32 : c ^ (-(2 / 3 : ℝ)) * c ^ (-(4 / 3 : ℝ)) = c ^ (-(3 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
    calc |L1| * ‖vacPhi a_phi u‖ ≤ (KL * c ^ (-(2 / 3 : ℝ))) * (Kφ * (4 * a₁) ^ 4 * c ^ (-(4 / 3 : ℝ))) := by gcongr
      _ = KL * Kφ * (4 * a₁) ^ 4 * (c ^ (-(3 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ))) := by rw [← h32]; ring
      _ ≤ KL * Kφ * (4 * a₁) ^ 4 * (c ^ (-(3 / 2 : ℝ)) * (u / (3 * a₀ / 4))) := by
          have : c ^ (-(1 / 2 : ℝ)) ≤ u / (3 * a₀ / 4) := by rw [le_div_iff₀ (by positivity)]; linarith only [hu_lo]
          gcongr
      _ = KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 * c ^ (-(3 / 2 : ℝ)) * u := by ring
  -- Lower bound on each factor in `O / F`:
  have h1m : 1 - KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 * c ^ (-(3 / 2 : ℝ)) ≤
      ‖(u : ℂ) - (L1 : ℂ) * vacPhi a_phi u‖ / u := by
    have hnorm_ge : u - |L1| * ‖vacPhi a_phi u‖ ≤ ‖(u : ℂ) - (L1 : ℂ) * vacPhi a_phi u‖ := by
      have hsub := norm_sub_norm_le (u : ℂ) ((L1 : ℂ) * vacPhi a_phi u)
      have hru : ‖(u : ℂ)‖ = u := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLs_pos]
      have hrv : ‖(L1 : ℂ) * vacPhi a_phi u‖ = |L1| * ‖vacPhi a_phi u‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      linarith only [hsub, hru, hrv]
    have hdiv : 1 - |L1| * ‖vacPhi a_phi u‖ / u ≤ ‖(u : ℂ) - (L1 : ℂ) * vacPhi a_phi u‖ / u := by
      rw [show 1 - |L1| * ‖vacPhi a_phi u‖ / u = (u - |L1| * ‖vacPhi a_phi u‖) / u by field_simp]
      exact div_le_div_of_nonneg_right hnorm_ge hLs_pos.le
    linarith only [hφ_bd, hdiv]
  have hΔ_sq_le : Δ ^ 2 ≤ CD ^ 2 * c ^ (-(3 / 2 : ℝ)) := by
    have h1 : Δ ^ 2 ≤ (CD * τ₁ ^ 3) ^ 2 :=
      sq_le_sq' (by linarith only [(abs_le.mp hΔ_bd).1]) (abs_le.mp hΔ_bd).2
    have h2 : (τ₁ ^ 3) ^ 2 = c ^ (-(3 / 2 : ℝ)) := by
      have : (τ₁ ^ 3) ^ 2 = (τ₁ ^ 2) ^ 3 := by ring
      rw [this, hτ₁_sq, ← Real.rpow_natCast (c ^ (-(1 / 2 : ℝ))) 3, ← Real.rpow_mul hc0.le]; norm_num
    calc Δ ^ 2 ≤ CD ^ 2 * (τ₁ ^ 3) ^ 2 := by convert h1 using 1; ring
      _ = _ := by rw [h2]
  have h1d : 1 - CD ^ 2 * c ^ (-(3 / 2 : ℝ)) ≤ Real.exp (-Δ) * (1 + Δ) := by
    have he := Real.add_one_le_exp (-Δ)
    have hp : 0 ≤ 1 + Δ := by linarith only [(abs_le.mp hΔ_half).1]
    have hmul := mul_le_mul_of_nonneg_right he hp
    have : (-Δ + 1) * (1 + Δ) = 1 - Δ ^ 2 := by ring
    linarith only [hmul, this, hΔ_sq_le]
  have hα_t2 : |alpha ε c| * t ^ 2 ≤ 4 * Kα * c ^ (-(7 / 6 : ℝ)) := by
    have ht2_sq : t ^ 2 ≤ 4 * c ^ (-(1 / 2 : ℝ)) := by
      rw [← hτ₁_sq]; nlinarith only [pow_le_pow_left₀ htpos.le ht2 2]
    have h76 : c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c ^ (-(7 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    calc |alpha ε c| * t ^ 2 ≤ (Kα * c ^ (-(2 / 3 : ℝ))) * (4 * c ^ (-(1 / 2 : ℝ))) := by gcongr; exact hαf ε c hε hcα'
      _ = 4 * Kα * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 2 : ℝ))) := by ring
      _ = _ := by rw [h76]
  have he_t : 1 - K4 * t ^ 4 - 4 * Kα * c ^ (-(7 / 6 : ℝ)) ≤ Real.exp (-(K4 * t ^ 4) + alpha ε c * t ^ 2) := by
    have he := Real.add_one_le_exp (-(K4 * t ^ 4) + alpha ε c * t ^ 2)
    have hneg : -(alpha ε c * t ^ 2) ≤ |alpha ε c| * t ^ 2 := by
      rw [show -(alpha ε c * t ^ 2) = (-alpha ε c) * t ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right (neg_le_abs _) (sq_nonneg t)
    linarith only [he, hneg, hα_t2]
  have herr_sum : 4 * Kα * c ^ (-(7 / 6 : ℝ)) + CD ^ 2 * c ^ (-(3 / 2 : ℝ)) +
      KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 * c ^ (-(3 / 2 : ℝ)) ≤ 3 / 10 * K4 * cK ^ 2 * c⁻¹ := by
    have h1 : 4 * Kα * c ^ (-(7 / 6 : ℝ)) ≤ 1 / 10 * K4 * cK ^ 2 * c⁻¹ := by
      have hb := hc_err1 c hce1'
      have h76 : c ^ (-(7 / 6 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c⁻¹ := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
      have hc16 : 0 ≤ c ^ (-(1 / 6 : ℝ)) := by positivity
      have hk_den : 4 * Kα ≤ 16 * (Kα + 1) + 1 := by linarith only [hKα0]
      rw [h76]
      calc 4 * Kα * (c ^ (-(1 / 6 : ℝ)) * c⁻¹) ≤ (16 * (Kα + 1) + 1) * c ^ (-(1 / 6 : ℝ)) * c⁻¹ := by
            have := mul_le_mul_of_nonneg_right hk_den hc16
            nlinarith only [this, inv_nonneg.mpr hc0.le]
        _ ≤ (16 * (Kα + 1) + 1) * ((1 / 10 * K4 * cK ^ 2) / (16 * (Kα + 1) + 1)) * c⁻¹ := by gcongr
        _ = 1 / 10 * K4 * cK ^ 2 * c⁻¹ := by field_simp
    have h2 : CD ^ 2 * c ^ (-(3 / 2 : ℝ)) ≤ 1 / 10 * K4 * cK ^ 2 * c⁻¹ := by
      have hb := hc_err2 c hce2'
      have h32 : c ^ (-(3 / 2 : ℝ)) = c ^ (-(1 / 2 : ℝ)) * c⁻¹ := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
      rw [h32]
      calc CD ^ 2 * (c ^ (-(1 / 2 : ℝ)) * c⁻¹) ≤ (CD ^ 2 + 1) * c ^ (-(1 / 2 : ℝ)) * c⁻¹ := by
            nlinarith only [Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ)), inv_pos.mpr hc0]
        _ ≤ (CD ^ 2 + 1) * ((1 / 10 * K4 * cK ^ 2) / (CD ^ 2 + 1)) * c⁻¹ := by gcongr
        _ = 1 / 10 * K4 * cK ^ 2 * c⁻¹ := by field_simp
    have h3 : KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 * c ^ (-(3 / 2 : ℝ)) ≤ 1 / 10 * K4 * cK ^ 2 * c⁻¹ := by
      have hb := hc_err3 c hce3'
      have h32 : c ^ (-(3 / 2 : ℝ)) = c ^ (-(1 / 2 : ℝ)) * c⁻¹ := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
      rw [h32]
      calc KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 * (c ^ (-(1 / 2 : ℝ)) * c⁻¹)
          ≤ (KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 + 1) * c ^ (-(1 / 2 : ℝ)) * c⁻¹ := by
            nlinarith only [Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ)), inv_pos.mpr hc0]
        _ ≤ (KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 + 1) *
            ((1 / 10 * K4 * cK ^ 2) / (KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 + 1)) * c⁻¹ := by gcongr
        _ = 1 / 10 * K4 * cK ^ 2 * c⁻¹ := by field_simp
    linarith only [h1, h2, h3]
  have hO_ratio : O / F = (Real.exp (-(K4 * t ^ 4) + alpha ε c * t ^ 2) * (Real.exp (-Δ) * (1 + Δ))) *
      (‖(u : ℂ) - (L1 : ℂ) * vacPhi a_phi u‖ / u) := by
    have hL_L1 : L - L1 ≠ 0 := by linarith only [(abs_le.mp hL1_le).2, hLlo, hδ0]
    have hFu : F ≠ 0 := hF_pos.ne'
    have hIf : uctIfl u ≠ 0 := (uctIfl_pos' hLs_pos).ne'
    have hu0 : u ≠ 0 := hLs_pos.ne'
    unfold O F physOscDatum physOsc physF
    dsimp only [s, L1, u, a_phi] at hvacP_eq hL_L1 hFu hIf hu0 ⊢
    rw [hvacP_eq]
    field_simp
  have hck_bd : K4 * cK ^ 2 * c⁻¹ ≤ 1 := hck c hck'
  have he1_nn : 0 ≤ 1 - KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 * c ^ (-(3 / 2 : ℝ)) := by
    have hp1 : 0 ≤ 4 * Kα * c ^ (-(7 / 6 : ℝ)) := by positivity
    have hp2 : 0 ≤ CD ^ 2 * c ^ (-(3 / 2 : ℝ)) := by positivity
    linarith only [herr_sum, hck_bd, hp1, hp2]
  have he2_nn : 0 ≤ 1 - CD ^ 2 * c ^ (-(3 / 2 : ℝ)) := by
    have hp1 : 0 ≤ 4 * Kα * c ^ (-(7 / 6 : ℝ)) := by positivity
    have hp3 : 0 ≤ KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 * c ^ (-(3 / 2 : ℝ)) := by positivity
    linarith only [herr_sum, hck_bd, hp1, hp3]
  have hK4t4_le : K4 * t ^ 4 ≤ 1 / 2 := by
    have h1 : t ^ 4 ≤ 16 * τ₁ ^ 4 := by
      have := pow_le_pow_left₀ htpos.le ht2 4
      calc t ^ 4 ≤ (2 * τ₁) ^ 4 := this
        _ = 16 * τ₁ ^ 4 := by ring
    have h2 : τ₁ ^ 4 ≤ τ₁ := pow_le_of_le_one hτ₁pos.le (by linarith only [hτ16]) (by norm_num)
    have h3 : τ₁ * (32 * K4 + 2) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hτK4
    have h4 : K4 * t ^ 4 ≤ K4 * (16 * τ₁) := mul_le_mul_of_nonneg_left (h1.trans (by linarith only [h2])) (by linarith only [hK4])
    nlinarith only [h4, h3, hτ₁pos]
  have he3_nn : 0 ≤ 1 - K4 * t ^ 4 - 4 * Kα * c ^ (-(7 / 6 : ℝ)) := by
    have hp2 : 0 ≤ CD ^ 2 * c ^ (-(3 / 2 : ℝ)) := by positivity
    have hp3 : 0 ≤ KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 * c ^ (-(3 / 2 : ℝ)) := by positivity
    linarith only [herr_sum, hck_bd, hK4t4_le, hp2, hp3]
  have hO_div_lo : 1 - K4 * t ^ 4 - 3 / 10 * K4 * cK ^ 2 * c⁻¹ ≤ O / F := by
    set a1 := 4 * Kα * c ^ (-(7 / 6 : ℝ))
    set a2 := CD ^ 2 * c ^ (-(3 / 2 : ℝ))
    set a3 := KL * Kφ * (4 / (3 * a₀)) * (4 * a₁) ^ 4 * c ^ (-(3 / 2 : ℝ))
    have ha1 : 0 ≤ a1 := by positivity
    have ha2 : 0 ≤ a2 := by positivity
    have ha3 : 0 ≤ a3 := by positivity
    have hprod1 : (1 - K4 * t ^ 4 - a1) * (1 - a2) ≤
        Real.exp (-(K4 * t ^ 4) + alpha ε c * t ^ 2) * (Real.exp (-Δ) * (1 + Δ)) :=
      mul_le_mul he_t h1d he2_nn (Real.exp_pos _).le
    have hprod2 : (1 - K4 * t ^ 4 - a1) * (1 - a2) * (1 - a3) ≤ O / F := by
      rw [hO_ratio]
      exact mul_le_mul hprod1 h1m he1_nn (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (by linarith only [(abs_le.mp hΔ_half).1])))
    have hlin : 1 - K4 * t ^ 4 - a1 - a2 - a3 ≤ (1 - K4 * t ^ 4 - a1) * (1 - a2) * (1 - a3) := by
      have hsub1 : 1 - K4 * t ^ 4 - a1 - a2 ≤ (1 - K4 * t ^ 4 - a1) * (1 - a2) := by
        have hp : 0 ≤ (K4 * t ^ 4 + a1) * a2 := by positivity
        nlinarith only [hp]
      have hsub2 : (1 - K4 * t ^ 4 - a1 - a2) * (1 - a3) ≤ (1 - K4 * t ^ 4 - a1) * (1 - a2) * (1 - a3) :=
        mul_le_mul_of_nonneg_right hsub1 he1_nn
      have hsub3 : 1 - K4 * t ^ 4 - a1 - a2 - a3 ≤ (1 - K4 * t ^ 4 - a1 - a2) * (1 - a3) := by
        have hp : 0 ≤ (K4 * t ^ 4 + a1 + a2) * a3 := by positivity
        nlinarith only [hp]
      linarith only [hsub2, hsub3]
    linarith only [hprod2, hlin, herr_sum]
  have htauL_sq : cK * τ₁ ^ 2 ≤ tau0 L ^ 2 := by
    have hL_ge : 3 / 2 * (a₀ * τ₁ ^ 2) ≤ L := by rw [hτ₁_sq]; linarith only [hLlo, hδ_lo]
    have hL_le1 : L ≤ 1 := by linarith only [hLhi, h6δ]
    have hsq := htau_lo L ⟨by linarith only [hLlo, hδ0], hL_le1⟩
    calc cK * τ₁ ^ 2 = cτ * (3 / 2 * (a₀ * τ₁ ^ 2)) := by rw [hcK]; ring
      _ ≤ cτ * L := mul_le_mul_of_nonneg_left hL_ge hcτ.le
      _ ≤ tau0 L ^ 2 := hsq
  have hcK_tauL : cK ^ 2 * c⁻¹ ≤ tau0 L ^ 4 := by
    have hc_inv : c⁻¹ = (τ₁ ^ 2) ^ 2 := by
      have : c * (τ₁ ^ 2) ^ 2 = 1 := by
        calc c * (τ₁ ^ 2) ^ 2 = τ₁ ^ 4 * c := by ring
          _ = 1 := hτ₁_four
      exact (eq_inv_of_mul_eq_one_right this).symm
    rw [hc_inv, show tau0 L ^ 4 = (tau0 L ^ 2) ^ 2 by ring, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) htauL_sq 2
  have hF_le : F ≤ 121 / 90 * uctIfl L := by
    unfold F physF
    calc (L - s) / (L - L1) * uctIfl u ≤ (11 / 10) * (11 / 9 * uctIfl L) := by
          exact mul_le_mul hLrat hIflrat (uctIfl_pos' hLs_pos).le (by norm_num)
      _ = 121 / 90 * uctIfl L := by ring
  have hOF_sub : -(14 / 10 * (121 / 90) * K4 * (tau0 L ^ 4 * uctIfl L)) ≤ O - F := by
    have h1 : F - O ≤ (K4 * t ^ 4 + 3 / 10 * K4 * cK ^ 2 * c⁻¹) * F := by
      have : 1 - O / F ≤ K4 * t ^ 4 + 3 / 10 * K4 * cK ^ 2 * c⁻¹ := by linarith only [hO_div_lo]
      have hmul := mul_le_mul_of_nonneg_right this hF_pos.le
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hF_pos.ne'] at hmul
      exact hmul
    have h2 : K4 * t ^ 4 + 3 / 10 * K4 * cK ^ 2 * c⁻¹ ≤ 14 / 10 * K4 * tau0 L ^ 4 := by
      have hkt : K4 * t ^ 4 ≤ 11 / 10 * K4 * tau0 L ^ 4 := by nlinarith only [htau4_rat, hK4]
      have hck4 := mul_le_mul_of_nonneg_left hcK_tauL (by linarith only [hK4] : 0 ≤ K4)
      linarith only [hkt, hck4]
    have h3 : (K4 * t ^ 4 + 3 / 10 * K4 * cK ^ 2 * c⁻¹) * F ≤
        (14 / 10 * K4 * tau0 L ^ 4) * (121 / 90 * uctIfl L) :=
      mul_le_mul h2 hF_le hF_pos.le (by positivity)
    linarith only [h1, h3]
  -- Finally assemble `physBump`!
  obtain ⟨hnc0, -⟩ := hnc_b ε c hε hcn'
  have hLpos : 0 < L := by linarith only [hLlo, hδ0]
  have hχ3 : 0 ≤ χ (L / (3 * δ)) := (hχ.mem _).1
  have hχ6 : χ (L / (6 * δ)) = 0 := hχ.zero _ (by rw [div_le_iff₀ (by positivity)]; linarith only [hLhi, hδ0])
  have hγ_le1 : physGamma c s L ≤ 1 := by
    unfold physGamma
    have : 0 ≤ (5 * Real.pi ^ 2 / 96) * c⁻¹ ^ 2 * (L - s) ^ (-3 : ℝ) := by positivity
    linarith only [this]
  have hγ_nn : 0 ≤ physGamma c s L := by
    unfold physGamma
    have hLs_34 : 3 / 4 * (a₀ * c ^ (-(1 / 2 : ℝ))) ≤ L - s := by
      have h1 : 3 / 4 * δ ≤ L - s := by linarith only [(abs_le.mp hs_le).2, hLlo]
      nlinarith only [h1, hδ_lo]
    have hpow : (L - s) ^ (-3 : ℝ) ≤ (3 / 4 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [hLs_34]) (by norm_num)
    have hgam_le1 : (5 * Real.pi ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 4 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ) ≤ 1 := by
      have hcg := hc_gam c hcgam'
      have hp3 : (3 / 4 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ) = (3 / 4 * a₀) ^ (-3 : ℝ) * c ^ (3 / 2 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul hc0.le, show (-(1 / 2 : ℝ)) * (-3 : ℝ) = 3 / 2 by norm_num]
      have hcpow : c⁻¹ ^ 2 * c ^ (3 / 2 : ℝ) = c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_natCast (c ^ (-1 : ℝ)) 2, ← Real.rpow_mul hc0.le,
          ← Real.rpow_add hc0]; norm_num
      have h5 := Real.pi_pos
      calc (5 * Real.pi ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 4 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ)
          = (5 * Real.pi ^ 2 / 96) * (3 / 4 * a₀) ^ (-3 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by rw [hp3]; linear_combination (5 * Real.pi ^ 2 / 96) * (3 / 4 * a₀) ^ (-3 : ℝ) * hcpow
        _ ≤ (5 * Real.pi ^ 2 / 96 + 1) * (3 / 4 * a₀) ^ (-3 : ℝ) * ((3 / 4 * a₀) ^ 3 / (5 * Real.pi ^ 2 / 96 + 1)) := by
            have ha3_pos : 0 < (3 / 4 * a₀) ^ (-3 : ℝ) := by positivity
            have hc12_nn : 0 ≤ c ^ (-(1 / 2 : ℝ)) := by positivity
            have hlt : 5 * Real.pi ^ 2 / 96 ≤ 5 * Real.pi ^ 2 / 96 + 1 := by linarith
            calc (5 * Real.pi ^ 2 / 96) * (3 / 4 * a₀) ^ (-3 : ℝ) * c ^ (-(1 / 2 : ℝ))
                ≤ (5 * Real.pi ^ 2 / 96 + 1) * (3 / 4 * a₀) ^ (-3 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by gcongr
              _ ≤ _ := by gcongr
        _ = 1 := by
            rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
            field_simp
    have hmul : (5 * Real.pi ^ 2 / 96) * c⁻¹ ^ 2 * (L - s) ^ (-3 : ℝ) ≤
        (5 * Real.pi ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 4 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    linarith only [hmul, hgam_le1]
  have hη_nn : 0 ≤ physEta c K1 L := by unfold physEta; positivity
  have huf : 0 ≤ uctIfl L := (uctIfl_pos' hLpos).le
  unfold physBump
  exact physBump_assemble hnc0 hχ3 hχ6 hγ_nn hγ_le1 hη_nn hO_nn hF_pos (by positivity) hK4 hOF_sub

end BumpNonneg

/-- info: 'FormalResearch.SignUncertainty.physBump_nonneg_le_three_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physBump_nonneg_le_three_delta

end FormalResearch.SignUncertainty
