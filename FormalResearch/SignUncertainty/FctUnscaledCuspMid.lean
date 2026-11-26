/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspMidFar

/-!
# `fct:unscaled-cusp`, regime `c^{-2/3} ≤ u ≤ 1`: the second estimate (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`, second estimate
`|∫_ℝ e^{icφ(τ;u)} a_c(τ) dτ| ≤ C M c^{-1/2}` for `c^{-2/3} ≤ u ≤ 1`.

Proof, on `τ > 0` (the negative half is the reflection `cuspInt_eq`): with `t₀ = 𝔪⁻¹(u)` and `r = √t₀`, split at `t₀/2`
and `2t₀`.  Piece `[0, t₀/2]`: one integration by parts (`cuspMid_piece1`); piece `[t₀/2, 2t₀]`: van der Corput
(`cuspMid_piece2`); piece `[2t₀, ∞)`: one integration by parts (`cuspMid_piece3`).  The hypothesis `c^{-2/3} ≤ u` gives
`√c r³ ≥ √ζ` (`CuspPhase.q_lb`), which turns `c^{-1} r^{-3}` into `c^{-1/2}`.

* `cuspIntPos_mid_le`: the half-line estimate with the explicit constant `cuspMidC`.
* `cuspInt_mid_le`: the estimate for `cuspInt`, constants independent of `M`, `a`, `c`, `u`.

Class: proved; hypotheses exactly those of `CuspPhase` and `CuspAmp` (`|𝔪 - m| ≤ C₀` and `|𝔪''| ≤ C₂` are not used).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

section Mid

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ η Ca M : ℝ} {a : ℝ → ℂ}

/-- The constant of the second estimate. -/
noncomputable def cuspMidC (η κ₁ κ₂ : ℝ) : ℝ :=
  (cuspD1 κ₁ κ₂ + cuspE1 κ₁ κ₂) / Real.sqrt (cuspZeta κ₂) + cuspD2 κ₁ + cuspE2 κ₁ * cuspTm κ₁ + cuspE3 η κ₁ κ₂

/-- The half-line estimate `‖∫_0^∞ e^{icφ} a‖ ≤ K C / √c` for `c^{-2/3} ≤ u ≤ 1`. -/
theorem cuspIntPos_mid_le (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u : ℝ} (hc : 0 < c) (hcu : c ^ (-(2 : ℝ) / 3) ≤ u) (hu1 : u ≤ 1) :
    ‖cuspIntPos 𝔪 c u a‖ ≤ Ca * M * ampC η * cuspMidC η κ₁ κ₂ / Real.sqrt c := by
  have hκ := h.κ₁_pos
  have hκ3 := h.κ₃_pos
  have hTp := cuspTm_pos κ₁
  have hT1 := one_le_cuspTm κ₁ hκ
  have hz := cuspZeta_pos h
  set K : ℝ := Ca * M * ampC η with hK
  have hK0 : 0 ≤ K := cuspK_nonneg hη hCa hM
  have hu0 : 0 < u := lt_of_lt_of_le (Real.rpow_pos_of_pos hc _) hcu
  -- `c ≥ 1`
  have hc1 : 1 ≤ c := by
    by_contra hlt
    push Not at hlt
    have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hc hlt (show -(2 : ℝ) / 3 < 0 by norm_num)
    linarith
  obtain ⟨t₀, ht₀, hv⟩ := h.exists_t0 hu0
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ t₀ = r ^ 2 := ⟨Real.sqrt t₀, Real.sqrt_pos.2 ht₀, (Real.sq_sqrt ht₀.le).symm⟩
  have hTm := (h.t0_bounds ht₀ hv hu1).1
  have hrT : r ≤ cuspTm κ₁ := by nlinarith [sq_nonneg (r - 1), sq_nonneg (r ^ 2 - 1)]
  have hq := h.q_lb ht₀ hv hu1 hc hcu
  rw [Real.sqrt_sq hr.le] at hq
  set s : ℝ := Real.sqrt c with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hc
  have hcs : c = s ^ 2 := (Real.sq_sqrt hc.le).symm
  have hs1 : 1 ≤ s := by
    rw [hs]; exact Real.one_le_sqrt.2 hc1
  set z0 : ℝ := Real.sqrt (cuspZeta κ₂) with hz0
  have hz0pos : 0 < z0 := Real.sqrt_pos.2 hz
  -- the three pieces
  have p1 := cuspMid_piece1 h ha hη hCa hM hc hr hv hu1
  have p2 := cuspMid_piece2 h ha hη hCa hM hc hr hv hu1
  have p3 := cuspMid_piece3 h ha hη hCa hM hc hr hv
  -- splitting of the integral
  have hF : IntegrableOn (fun x => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x) (Ioi 0) :=
    cuspF_integrableOn h.continuous ha hη hCa hM c u
  have hα1 : (0 : ℝ) ≤ r ^ 2 / 2 := by positivity
  have hα12 : r ^ 2 / 2 ≤ 2 * r ^ 2 := by nlinarith [sq_nonneg r]
  have hsplit : cuspIntPos 𝔪 c u a =
      (∫ x in (0 : ℝ)..(r ^ 2 / 2), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x) +
      ((∫ x in (r ^ 2 / 2)..(2 * r ^ 2), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x) +
      ∫ x in Ioi (2 * r ^ 2), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x) := by
    unfold cuspIntPos
    rw [integral_Ioi_split hα1 hF, integral_Ioi_split hα12 (hF.mono_set (Ioi_subset_Ioi hα1))]
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add p1 ((norm_add_le _ _).trans (add_le_add p2 p3))).trans ?_
  -- arithmetic
  have hD1 : 0 ≤ cuspD1 κ₁ κ₂ := by unfold cuspD1; positivity
  have hD2 : 0 ≤ cuspD2 κ₁ := by unfold cuspD2; positivity
  have hE1 : 0 ≤ cuspE1 κ₁ κ₂ := by unfold cuspE1; positivity
  have hE2 : 0 ≤ cuspE2 κ₁ := by unfold cuspE2; positivity
  have hE3 : 0 ≤ cuspE3 η κ₁ κ₂ := by
    have := cuspGam_nonneg η
    unfold cuspE3; positivity
  have hq' : z0 ≤ s * r ^ 3 := hq
  have hcr : s * z0 ≤ c * r ^ 3 := by
    rw [hcs]; nlinarith [mul_le_mul_of_nonneg_left hq' hs0.le]
  have hinv : (c * r ^ 3)⁻¹ ≤ (s * z0)⁻¹ := inv_anti₀ (by positivity) hcr
  have e1 : cuspD1 κ₁ κ₂ * K / (c * r ^ 3) ≤ K * (cuspD1 κ₁ κ₂ / z0) / s := by
    have : cuspD1 κ₁ κ₂ * K / (c * r ^ 3) = cuspD1 κ₁ κ₂ * K * (c * r ^ 3)⁻¹ := by rw [div_eq_mul_inv]
    rw [this]
    calc cuspD1 κ₁ κ₂ * K * (c * r ^ 3)⁻¹ ≤ cuspD1 κ₁ κ₂ * K * (s * z0)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = K * (cuspD1 κ₁ κ₂ / z0) / s := by field_simp
  have e2 : K * (cuspE1 κ₁ κ₂ * (r ^ 3)⁻¹ + cuspE2 κ₁ * r + cuspE3 η κ₁ κ₂) / c ≤
      K * (cuspE1 κ₁ κ₂ / z0 + cuspE2 κ₁ * cuspTm κ₁ + cuspE3 η κ₁ κ₂) / s := by
    have h1 : (r ^ 3)⁻¹ / c ≤ (z0)⁻¹ / s := by
      have : (r ^ 3)⁻¹ / c = (c * r ^ 3)⁻¹ := by field_simp
      have h2 : (z0)⁻¹ / s = (s * z0)⁻¹ := by field_simp
      rw [this, h2]; exact hinv
    have h3 : 1 / c ≤ 1 / s := by
      rw [div_le_div_iff₀ hc hs0]; nlinarith
    have h4 : r / c ≤ cuspTm κ₁ / s := by
      calc r / c = r * (1 / c) := by ring
        _ ≤ cuspTm κ₁ * (1 / s) := mul_le_mul hrT h3 (by positivity) hTp.le
        _ = cuspTm κ₁ / s := by ring
    have h5 : K * (cuspE1 κ₁ κ₂ * (r ^ 3)⁻¹ + cuspE2 κ₁ * r + cuspE3 η κ₁ κ₂) / c =
        K * (cuspE1 κ₁ κ₂ * ((r ^ 3)⁻¹ / c) + cuspE2 κ₁ * (r / c) + cuspE3 η κ₁ κ₂ * (1 / c)) := by
      field_simp
    have h6 : K * (cuspE1 κ₁ κ₂ / z0 + cuspE2 κ₁ * cuspTm κ₁ + cuspE3 η κ₁ κ₂) / s =
        K * (cuspE1 κ₁ κ₂ * ((z0)⁻¹ / s) + cuspE2 κ₁ * (cuspTm κ₁ / s) + cuspE3 η κ₁ κ₂ * (1 / s)) := by
      field_simp
    rw [h5, h6]
    refine mul_le_mul_of_nonneg_left ?_ hK0
    have := mul_le_mul_of_nonneg_left h1 hE1
    have := mul_le_mul_of_nonneg_left h4 hE2
    have := mul_le_mul_of_nonneg_left h3 hE3
    linarith
  have hC : K * cuspMidC η κ₁ κ₂ / s =
      K * (cuspD1 κ₁ κ₂ / z0) / s + K * cuspD2 κ₁ / s +
        K * (cuspE1 κ₁ κ₂ / z0 + cuspE2 κ₁ * cuspTm κ₁ + cuspE3 η κ₁ κ₂) / s := by
    unfold cuspMidC; rw [← hz0]; field_simp; ring
  rw [hC]
  have : K * cuspD1 κ₁ κ₂ / (c * r ^ 3) = cuspD1 κ₁ κ₂ * K / (c * r ^ 3) := by rw [mul_comm K]
  rw [this]
  linarith [e1, e2]

/-- **Second estimate of `fct:unscaled-cusp`** (`c^{-2/3} ≤ u ≤ 1`), with explicit constant:
`‖∫_ℝ e^{icφ(τ;u)} a_c(τ) dτ‖ ≤ 2 C_a (e^η + 8/η²) C M c^{-1/2}`. -/
theorem cuspInt_mid_le (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmp η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u : ℝ} (hc : 0 < c) (hcu : c ^ (-(2 : ℝ) / 3) ≤ u) (hu1 : u ≤ 1) :
    ‖cuspInt 𝔪 c u a‖ ≤ 2 * Ca * ampC η * cuspMidC η κ₁ κ₂ * M * c ^ (-(1 : ℝ) / 2) := by
  rw [cuspInt_eq h.continuous h.even ha hη hCa hM]
  refine (norm_add_le _ _).trans ?_
  rw [norm_star]
  have h1 := cuspIntPos_mid_le h ha.pos hη hCa hM hc hcu hu1
  have h2 := cuspIntPos_mid_le h ha.neg hη hCa hM hc hcu hu1
  have e : c ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt c := by
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hc.le, ← Real.sqrt_eq_rpow, one_div]
  rw [e]
  have : 2 * Ca * ampC η * cuspMidC η κ₁ κ₂ * M * (1 / Real.sqrt c) =
      Ca * M * ampC η * cuspMidC η κ₁ κ₂ / Real.sqrt c + Ca * M * ampC η * cuspMidC η κ₁ κ₂ / Real.sqrt c := by
    ring
  rw [this]
  exact add_le_add h1 h2

/-- **Second estimate of `fct:unscaled-cusp`**, in the paper's quantifier order: for fixed phase data `(κ₁, κ₂, C₂, C₀)`
and decay rate `η`, symbol constant `C_a`, there is `C` with `‖∫_ℝ e^{icφ(τ;u)} a_c‖ ≤ C M c^{-1/2}` for all `M ≥ 0`,
`a_c` with the symbol bounds, `c > 0` and `c^{-2/3} ≤ u ≤ 1`. -/
theorem cuspInt_mid_le_exists (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {η Ca : ℝ} (hη : 0 < η) (hCa : 0 ≤ Ca) :
    ∃ C : ℝ, ∀ (M : ℝ) (a : ℝ → ℂ) (c u : ℝ), 0 ≤ M → CuspAmp η Ca M a → 0 < c → c ^ (-(2 : ℝ) / 3) ≤ u →
      u ≤ 1 → ‖cuspInt 𝔪 c u a‖ ≤ C * M * c ^ (-(1 : ℝ) / 2) :=
  ⟨2 * Ca * ampC η * cuspMidC η κ₁ κ₂, fun M a c u hM ha hc hcu hu1 =>
    (cuspInt_mid_le h ha hη hCa hM hc hcu hu1).trans (le_of_eq (by ring))⟩

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.cuspInt_mid_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cuspInt_mid_le

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.cuspInt_mid_le_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cuspInt_mid_le_exists

end Mid

end FormalResearch.SignUncertainty.FctUnscaledCusp
