/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspFarTail
public import FormalResearch.SignUncertainty.FctUnscaledCuspMid

/-!
# `fct:unscaled-cusp`, regime `u ≥ 1`: the third estimate (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`, third estimate
`|∫_ℝ e^{icφ(τ;u)} a_c| ≤ C M ((cu)^{-3/2} + c^{-1/2} e^{-η' t₀})` for `u ≥ 1`, `t₀ = 𝔪⁻¹(u)`, `η' = η/8`.

Proof on `τ > 0` (the negative half is the reflection `cuspInt_eq`): with `y = (cu)^{-1/2}` and the cut point `t_*`
(`𝔪 t_* = u/2`, `CuspPhase.exists_cut`), `γ = min(t_*, t₀/2)`:
* `[0, y²]`: absolute integration (`‖a x‖ ≤ K √x`), `≤ K y³`;
* `[y², t₀/2]`: two integrations by parts with the gap `u - 𝔪 ≥ u/2` on `[0, γ]` and `≥ g_m` afterwards, the majorant integral
  split between the two regimes through the dominating function `Ψ` (`cuspFar_low`);
* `[t₀/2, 2t₀]`: van der Corput (`cuspFar_saddle`);
* `[2t₀, ∞)`: one integration by parts (`cuspFar_tail`).

The condition `(cu)² ≥ 2κ₃` guarantees `y² ≤ γ`; in the complementary range the absolute estimate `cuspInt_abs_le` is already
`≤ C M (cu)^{-3/2}`.  The hypothesis `c ≥ 1` replaces the paper's "sufficiently large `c`"; `|𝔪 - m| ≤ C₀` is not used.

* `cuspIntPos_far_le`: the half-line estimate.
* `cuspInt_far_le`, `cuspInt_far_le_exists`: the estimate for `cuspInt`, constants independent of `M`, `a`, `c`, `u`, `t₀`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

section Far

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ η Ca M : ℝ} {a : ℝ → ℂ}

/-- `N_max = 4κ₃² · 24/(η/4)⁴`, the bound for `u² e^{-ηγ/4}` when `u ≤ 2κ₃γ²`. -/
noncomputable def cuspFarNmax (η κ₃ : ℝ) : ℝ := 4 * κ₃ ^ 2 * (24 / (η / 4) ^ 4)

/-- The coefficient of `(cu)^{-3/2}`. -/
noncomputable def cuspFarDy (η κ₁ κ₂ C₂ : ℝ) : ℝ :=
  1 + cuspFarD0 η (cuspK3 κ₂) C₂ +
    cuspFarD1 η (cuspK3 κ₂) C₂ (cuspGm κ₁ κ₂) * cuspFarNmax η (cuspK3 κ₂)

/-- The coefficient of `c^{-1/2} e^{-ηt₀/8}`. -/
noncomputable def cuspFarDe (η κ₁ κ₂ : ℝ) : ℝ :=
  cuspFarD2 η (cuspK3 κ₂) (cuspGm κ₁ κ₂) + cuspFarD3 η κ₁ κ₂ + cuspFarD4 η κ₁ κ₂

/-- The cut data: `y = (cu)^{-1/2}`, `t_*` with `𝔪 t_* = u/2`, `γ = min (t_*, t₀/2)`. -/
lemma far_cut_data (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {c u t₀ : ℝ} (hc : 1 ≤ c) (hu : 1 ≤ u) (ht₀ : 0 < t₀)
    (hv : 𝔪 t₀ = u) (hcu : 2 * cuspK3 κ₂ ≤ (c * u) ^ 2) :
    ∃ y ts γ : ℝ, y = (Real.sqrt (c * u))⁻¹ ∧ 0 < y ∧ y ^ 2 * (c * u) = 1 ∧ 𝔪 ts = u / 2 ∧ 0 ≤ γ ∧ γ ≤ ts ∧ γ ≤ t₀ / 2 ∧ y ^ 2 ≤ γ ∧
      u ≤ 2 * cuspK3 κ₂ * γ ^ 2 := by
  have hκ3 := h.κ₃_pos
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  obtain ⟨ts, hts0, hts, htsu⟩ := h.exists_cut hu0
  have hcu0 : 0 < c * u := mul_pos hc0 hu0
  have hsq0 : 0 < Real.sqrt (c * u) := Real.sqrt_pos.2 hcu0
  set y : ℝ := (Real.sqrt (c * u))⁻¹ with hy
  have hy0 : 0 < y := inv_pos.2 hsq0
  have hyc : y ^ 2 * (c * u) = 1 := by
    rw [hy, inv_pow, Real.sq_sqrt hcu0.le]; field_simp
  have hy4 : 2 * cuspK3 κ₂ * y ^ 4 ≤ 1 := by
    have h1 : (y ^ 2 * (c * u)) ^ 2 = 1 := by rw [hyc]; norm_num
    have h2 : y ^ 4 * (2 * cuspK3 κ₂) ≤ y ^ 4 * (c * u) ^ 2 := mul_le_mul_of_nonneg_left hcu (by positivity)
    have h3 : y ^ 4 * (c * u) ^ 2 = 1 := by rw [← h1]; ring
    linarith
  have h2s := h.two_le_sq ht₀ hv hu
  have hle2 := h.le_sq ht₀.le
  rw [hv] at hle2
  have hyts : y ^ 2 ≤ ts := by
    by_contra hlt
    push Not at hlt
    have h1 : ts ^ 2 < y ^ 4 := by
      have : ts ^ 2 < (y ^ 2) ^ 2 := pow_lt_pow_left₀ hlt hts0.le (by norm_num)
      linarith [show (y ^ 2) ^ 2 = y ^ 4 by ring]
    have := mul_lt_mul_of_pos_left h1 hκ3
    linarith
  have hyt₀ : y ^ 2 ≤ t₀ / 2 := by
    by_contra hlt
    push Not at hlt
    have h1 : (t₀ / 2) ^ 2 < y ^ 4 := by
      have : (t₀ / 2) ^ 2 < (y ^ 2) ^ 2 := pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
      linarith [show (y ^ 2) ^ 2 = y ^ 4 by ring]
    have := mul_lt_mul_of_pos_left h1 hκ3
    nlinarith [this, h2s]
  refine ⟨y, ts, min ts (t₀ / 2), hy, hy0, hyc, hts, ?_, min_le_left _ _, min_le_right _ _, le_min hyts hyt₀, ?_⟩
  · exact le_min hts0.le (by positivity)
  · by_cases hle : ts ≤ t₀ / 2
    · rw [min_eq_left hle]; nlinarith [sq_nonneg ts]
    · rw [min_eq_right (not_le.1 hle).le]; nlinarith

/-- Piece `[0, y²]`: absolute integration, `≤ K y³`. -/
lemma far_piece0 (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u y : ℝ} (hy0 : 0 < y) :
    ‖∫ x in (0 : ℝ)..(y ^ 2), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      Ca * M * ampC η * y ^ 3 := by
  have hK0 := cuspK_nonneg hη hCa hM
  have hα : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := y ^ 2)
    (f := fun x => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x)
    (C := Ca * M * ampC η * y) (fun x hx => by
      rw [uIoc_of_le hα] at hx
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
      have h0 := ha.amp0 hη hCa hM hx.1
      have he : Real.exp (-(η / 2) * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith only [hx.1, hη])
      have hx1 : x ^ ((1 : ℝ) / 2) ≤ y := by
        calc x ^ ((1 : ℝ) / 2) ≤ (y ^ 2) ^ ((1 : ℝ) / 2) :=
              Real.rpow_le_rpow hx.1.le hx.2 (by norm_num)
          _ = y := rpow_sq_half hy0
      have h1 : x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x) ≤ y := by
        have h3 := Real.rpow_nonneg hx.1.le ((1 : ℝ) / 2)
        calc _ ≤ x ^ ((1 : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left he h3
          _ ≤ y := by linarith
      exact h0.trans (mul_le_mul_of_nonneg_left h1 hK0))
  rw [sub_zero, abs_of_nonneg hα] at this
  calc _ ≤ Ca * M * ampC η * y * y ^ 2 := this
    _ = Ca * M * ampC η * y ^ 3 := by ring

/-- **Third estimate** on `τ > 0`: `‖∫_0^∞ e^{icφ} a‖ ≤ K (D_y (√(cu)³)⁻¹ + D_e e^{-ηt₀/8}/√c)`, for `u ≥ 1`, `c ≥ 1`,
`(cu)² ≥ 2κ₃`, `𝔪 t₀ = u`. -/
theorem cuspIntPos_far_le (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u t₀ : ℝ} (hc : 1 ≤ c) (hu : 1 ≤ u) (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u)
    (hcu : 2 * cuspK3 κ₂ ≤ (c * u) ^ 2) :
    ‖cuspIntPos 𝔪 c u a‖ ≤ Ca * M * ampC η * (cuspFarDy η κ₁ κ₂ C₂ * (Real.sqrt (c * u) ^ 3)⁻¹ +
      cuspFarDe η κ₁ κ₂ * Real.exp (-(η / 8) * t₀) / Real.sqrt c) := by
  have hκ := h.κ₁_pos
  have hκ3 := h.κ₃_pos
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have hK0 := cuspK_nonneg hη hCa hM
  obtain ⟨y, ts, γ, hyd, hy0, hyc, hts, hγ0, hγs, hγb, hyγ, hγu⟩ := far_cut_data h hc hu ht₀ hv hcu
  set K : ℝ := Ca * M * ampC η with hK
  set κ₃ : ℝ := cuspK3 κ₂ with hκ₃
  -- the bound for `u² e^{-ηγ/4}`
  have hN : u ^ 2 * Real.exp (-(η / 4) * γ) ≤ cuspFarNmax η κ₃ := by
    have h1 := pow_four_mul_exp_le (z := η / 4) (t := γ) (by positivity) hγ0
    have h2 : u ^ 2 ≤ 4 * κ₃ ^ 2 * γ ^ 4 := by
      have : u ^ 2 ≤ (2 * κ₃ * γ ^ 2) ^ 2 := pow_le_pow_left₀ hu0.le hγu 2
      calc u ^ 2 ≤ (2 * κ₃ * γ ^ 2) ^ 2 := this
        _ = 4 * κ₃ ^ 2 * γ ^ 4 := by ring
    unfold cuspFarNmax
    calc u ^ 2 * Real.exp (-(η / 4) * γ) ≤ (4 * κ₃ ^ 2 * γ ^ 4) * Real.exp (-(η / 4) * γ) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = 4 * κ₃ ^ 2 * (γ ^ 4 * Real.exp (-(η / 4) * γ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  -- the four pieces
  have hlow := cuspFar_low h ha hη hCa hM hc hu ht₀ hv hts hγs hγb hy0 hyγ hyc
  have hsad := cuspFar_saddle h ha hη hCa hM hc0 hu ht₀ hv
  have htail := cuspFar_tail h ha hη hCa hM hc0 hu ht₀ hv
  have hP0 := far_piece0 (𝔪 := 𝔪) (c := c) (u := u) ha hη hCa hM hy0
  have hα : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hαβ : y ^ 2 ≤ t₀ / 2 := hyγ.trans hγb
  have hβ2 : t₀ / 2 ≤ 2 * t₀ := by linarith
  have hF : IntegrableOn (fun x => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x) (Ioi 0) :=
    cuspF_integrableOn h.continuous ha hη hCa hM c u
  have hsplit : cuspIntPos 𝔪 c u a =
      (∫ x in (0 : ℝ)..(y ^ 2), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x) +
      ((∫ x in (y ^ 2)..(t₀ / 2), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x) +
      ((∫ x in (t₀ / 2)..(2 * t₀), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x) +
      ∫ x in Ioi (2 * t₀), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x)) := by
    unfold cuspIntPos
    rw [integral_Ioi_split hα hF, integral_Ioi_split hαβ (hF.mono_set (Ioi_subset_Ioi hα)),
      integral_Ioi_split hβ2 (hF.mono_set (Ioi_subset_Ioi (hα.trans hαβ)))]
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add hP0 ((norm_add_le _ _).trans (add_le_add hlow ((norm_add_le _ _).trans
    (add_le_add hsad htail))))).trans ?_
  -- arithmetic
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have hsc1 : Real.sqrt c ≤ c := by
    rw [Real.sqrt_le_left hc0.le]; nlinarith only [hc]
  have hKc : K / c ≤ K / Real.sqrt c := div_le_div_of_nonneg_left hK0 hsc hsc1
  have hD1 : 0 ≤ cuspFarD1 η κ₃ C₂ (cuspGm κ₁ κ₂) := by
    unfold cuspFarD1
    have h1 := cuspGm_pos h
    have h2 := cuspFarA_nonneg h1 hκ3.le
    have h3 := cuspGamB_nonneg η
    have h4 : 0 ≤ C₂ := (abs_nonneg _).trans (h.deriv2_bound 0)
    exact add_nonneg (mul_nonneg two_pos.le h2) (mul_nonneg (mul_nonneg h4 h3) (inv_nonneg.2 (pow_pos h1 3).le))
  have hy3 : y ^ 3 = (Real.sqrt (c * u) ^ 3)⁻¹ := by rw [hyd, inv_pow]
  have hE : 0 < Real.exp (-(η / 8) * t₀) := Real.exp_pos _
  have hy3p : 0 ≤ y ^ 3 := by positivity
  have hlow' : K * y ^ 3 * (cuspFarD0 η κ₃ C₂ + cuspFarD1 η κ₃ C₂ (cuspGm κ₁ κ₂) *
        (u ^ 2 * Real.exp (-(η / 4) * γ))) ≤
      K * y ^ 3 * (cuspFarD0 η κ₃ C₂ + cuspFarD1 η κ₃ C₂ (cuspGm κ₁ κ₂) * cuspFarNmax η κ₃) := by
    gcongr
  have hl2 : K / c * (cuspFarD2 η κ₃ (cuspGm κ₁ κ₂) * Real.exp (-(η / 8) * t₀)) ≤
      K / Real.sqrt c * (cuspFarD2 η κ₃ (cuspGm κ₁ κ₂) * Real.exp (-(η / 8) * t₀)) := by
    have : 0 ≤ cuspFarD2 η κ₃ (cuspGm κ₁ κ₂) := by
      unfold cuspFarD2
      have := cuspGm_pos h
      positivity
    exact mul_le_mul_of_nonneg_right hKc (by positivity)
  have ht2 : K / c * (cuspFarD4 η κ₁ κ₂ * Real.exp (-(η / 8) * t₀)) ≤
      K / Real.sqrt c * (cuspFarD4 η κ₁ κ₂ * Real.exp (-(η / 8) * t₀)) := by
    have : 0 ≤ cuspFarD4 η κ₁ κ₂ := by
      unfold cuspFarD4
      have := cuspGam_nonneg (η / 2)
      positivity
    exact mul_le_mul_of_nonneg_right hKc (by positivity)
  have hmain : K * y ^ 3 + (K * y ^ 3 * (cuspFarD0 η κ₃ C₂ + cuspFarD1 η κ₃ C₂ (cuspGm κ₁ κ₂) * cuspFarNmax η κ₃) +
      K / Real.sqrt c * (cuspFarD2 η κ₃ (cuspGm κ₁ κ₂) * Real.exp (-(η / 8) * t₀)) +
      (K * cuspFarD3 η κ₁ κ₂ * Real.exp (-(η / 8) * t₀) / Real.sqrt c +
        K / Real.sqrt c * (cuspFarD4 η κ₁ κ₂ * Real.exp (-(η / 8) * t₀)))) =
      K * (cuspFarDy η κ₁ κ₂ C₂ * y ^ 3 + cuspFarDe η κ₁ κ₂ * Real.exp (-(η / 8) * t₀) / Real.sqrt c) := by
    unfold cuspFarDy cuspFarDe
    field_simp
    ring
  rw [← hy3]
  linarith [hlow', hl2, ht2, hmain]

lemma rpow_neg_three_half_eq {x : ℝ} (hx : 0 < x) : x ^ (-(3 : ℝ) / 2) = (Real.sqrt x ^ 3)⁻¹ := by
  rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg hx.le,
    show (3 : ℝ) / 2 = 1 / 2 * ((3 : ℕ) : ℝ) by norm_num, Real.rpow_mul hx.le, Real.rpow_natCast,
    ← Real.sqrt_eq_rpow]

lemma cuspFarDy_nonneg (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (hη : 0 < η) : 0 ≤ cuspFarDy η κ₁ κ₂ C₂ := by
  have hκ3 := h.κ₃_pos
  have hC2 : 0 ≤ C₂ := (abs_nonneg _).trans (h.deriv2_bound 0)
  have h1 := cuspGm_pos h
  have h2 := cuspFarA_nonneg h1 hκ3.le
  have h3 := cuspGamB_nonneg η
  have h4 : 0 ≤ cuspFarD1 η (cuspK3 κ₂) C₂ (cuspGm κ₁ κ₂) :=
    add_nonneg (mul_nonneg two_pos.le h2) (mul_nonneg (mul_nonneg hC2 h3) (inv_nonneg.2 (pow_pos h1 3).le))
  have h5 : 0 ≤ cuspFarD0 η (cuspK3 κ₂) C₂ := by
    unfold cuspFarD0; positivity
  have h6 : 0 ≤ cuspFarNmax η (cuspK3 κ₂) := by
    unfold cuspFarNmax; positivity
  unfold cuspFarDy
  have := mul_nonneg h4 h6
  linarith

lemma cuspFarDe_nonneg (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (hη : 0 < η) : 0 ≤ cuspFarDe η κ₁ κ₂ := by
  unfold cuspFarDe cuspFarD2 cuspFarD3 cuspFarD4
  have hκ := h.κ₁_pos
  have hκ3 := h.κ₃_pos
  have h1 := cuspGm_pos h
  have h2 := cuspGam_nonneg (η / 2)
  positivity

/-- The constant of the third estimate. -/
noncomputable def cuspFarC (η κ₁ κ₂ C₂ Ca : ℝ) : ℝ :=
  2 * Ca * ampC η * (cuspFarDy η κ₁ κ₂ C₂ + cuspFarDe η κ₁ κ₂) + 2 * Ca * domInt η * (1 + 2 * cuspK3 κ₂)

lemma cuspFarC_nonneg (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (hη : 0 < η) (hCa : 0 ≤ Ca) :
    0 ≤ cuspFarC η κ₁ κ₂ C₂ Ca := by
  unfold cuspFarC
  have hAy := ampC_pos hη
  have h1 := domInt_nonneg η
  have h2 := cuspFarDy_nonneg h hη (κ₁ := κ₁) (κ₂ := κ₂) (C₂ := C₂) (C₀ := C₀)
  have h3 := cuspFarDe_nonneg h hη
  have hκ3 := h.κ₃_pos
  positivity

/-- **Third estimate of `fct:unscaled-cusp`** (`u ≥ 1`), with explicit constant. -/
theorem cuspInt_far_le (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmp η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u t₀ : ℝ} (hc : 1 ≤ c) (hu : 1 ≤ u) (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u) :
    ‖cuspInt 𝔪 c u a‖ ≤ cuspFarC η κ₁ κ₂ C₂ Ca * M *
      ((c * u) ^ (-(3 : ℝ) / 2) + c ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 8) * t₀)) := by
  have hκ3 := h.κ₃_pos
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  have hcu0 : 0 < c * u := mul_pos hc0 hu0
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have hw : 0 < Real.sqrt (c * u) := Real.sqrt_pos.2 hcu0
  have e1 : (c * u) ^ (-(3 : ℝ) / 2) = (Real.sqrt (c * u) ^ 3)⁻¹ := rpow_neg_three_half_eq hcu0
  have e2 : c ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt c := by
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hc0.le, ← Real.sqrt_eq_rpow, one_div]
  rw [e1, e2]
  have hε : 0 ≤ 1 / Real.sqrt c * Real.exp (-(η / 8) * t₀) := by positivity
  have hW : 0 < (Real.sqrt (c * u) ^ 3)⁻¹ := by positivity
  have hAy := ampC_pos hη
  have hDy := cuspFarDy_nonneg h hη
  have hDe := cuspFarDe_nonneg h hη
  by_cases hcu : 2 * cuspK3 κ₂ ≤ (c * u) ^ 2
  · rw [cuspInt_eq h.continuous h.even ha hη hCa hM]
    refine (norm_add_le _ _).trans ?_
    rw [norm_star]
    have h1 := cuspIntPos_far_le h ha.pos hη hCa hM hc hu ht₀ hv hcu
    have h2 := cuspIntPos_far_le h ha.neg hη hCa hM hc hu ht₀ hv hcu
    have hK : 0 ≤ Ca * M * ampC η := cuspK_nonneg hη hCa hM
    have key : cuspFarDy η κ₁ κ₂ C₂ * (Real.sqrt (c * u) ^ 3)⁻¹ +
        cuspFarDe η κ₁ κ₂ * Real.exp (-(η / 8) * t₀) / Real.sqrt c ≤
        (cuspFarDy η κ₁ κ₂ C₂ + cuspFarDe η κ₁ κ₂) *
          ((Real.sqrt (c * u) ^ 3)⁻¹ + 1 / Real.sqrt c * Real.exp (-(η / 8) * t₀)) := by
      have : cuspFarDe η κ₁ κ₂ * Real.exp (-(η / 8) * t₀) / Real.sqrt c =
          cuspFarDe η κ₁ κ₂ * (1 / Real.sqrt c * Real.exp (-(η / 8) * t₀)) := by ring
      rw [this]
      nlinarith [mul_nonneg hDy hε, mul_nonneg hDe hW.le]
    have h12 := add_le_add h1 h2
    refine h12.trans ?_
    unfold cuspFarC
    have hP : 0 ≤ (Real.sqrt (c * u) ^ 3)⁻¹ + 1 / Real.sqrt c * Real.exp (-(η / 8) * t₀) := by positivity
    have hq := mul_le_mul_of_nonneg_left key hK
    have hdom : 0 ≤ 2 * Ca * domInt η * (1 + 2 * cuspK3 κ₂) := by
      have := domInt_nonneg η
      positivity
    calc _ ≤ 2 * (Ca * M * ampC η * ((cuspFarDy η κ₁ κ₂ C₂ + cuspFarDe η κ₁ κ₂) *
          ((Real.sqrt (c * u) ^ 3)⁻¹ + 1 / Real.sqrt c * Real.exp (-(η / 8) * t₀)))) := by linarith
      _ = 2 * Ca * ampC η * (cuspFarDy η κ₁ κ₂ C₂ + cuspFarDe η κ₁ κ₂) * M *
          ((Real.sqrt (c * u) ^ 3)⁻¹ + 1 / Real.sqrt c * Real.exp (-(η / 8) * t₀)) := by ring
      _ ≤ _ := by
        have : 0 ≤ M * ((Real.sqrt (c * u) ^ 3)⁻¹ + 1 / Real.sqrt c * Real.exp (-(η / 8) * t₀)) :=
          mul_nonneg hM hP
        nlinarith [mul_nonneg hdom this]
  · push Not at hcu
    have hab := cuspInt_abs_le h.continuous h.even ha hη hCa hM c u
    refine hab.trans ?_
    -- `1 ≤ (1 + 2κ₃) (√(cu)³)⁻¹`
    set w : ℝ := Real.sqrt (c * u) with hwdef
    have hw4 : w ^ 4 < 2 * cuspK3 κ₂ := by
      have : w ^ 4 = (c * u) ^ 2 := by
        rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hwdef, Real.sq_sqrt hcu0.le]
      rw [this]; exact hcu
    have hw3 : w ^ 3 ≤ 1 + 2 * cuspK3 κ₂ := by
      by_cases hw1 : w ≤ 1
      · have : w ^ 3 ≤ 1 := pow_le_one₀ hw.le hw1
        linarith
      · push Not at hw1
        have : w ^ 3 ≤ w ^ 4 := pow_le_pow_right₀ hw1.le (by norm_num)
        linarith
    have hone : 1 ≤ (1 + 2 * cuspK3 κ₂) * (w ^ 3)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    have hP : 0 ≤ (w ^ 3)⁻¹ + 1 / Real.sqrt c * Real.exp (-(η / 8) * t₀) := by positivity
    unfold cuspFarC
    have hD1 : 0 ≤ 2 * Ca * ampC η * (cuspFarDy η κ₁ κ₂ C₂ + cuspFarDe η κ₁ κ₂) := by positivity
    have hdom : 0 ≤ 2 * Ca * domInt η := by
      have := domInt_nonneg η
      positivity
    have step1 : 2 * Ca * domInt η * M ≤ 2 * Ca * domInt η * (1 + 2 * cuspK3 κ₂) * M * (w ^ 3)⁻¹ := by
      have := mul_le_mul_of_nonneg_left hone (mul_nonneg hdom hM)
      nlinarith [this]
    have step2 : 2 * Ca * domInt η * (1 + 2 * cuspK3 κ₂) * M * (w ^ 3)⁻¹ ≤
        (2 * Ca * ampC η * (cuspFarDy η κ₁ κ₂ C₂ + cuspFarDe η κ₁ κ₂) +
          2 * Ca * domInt η * (1 + 2 * cuspK3 κ₂)) * M *
        ((w ^ 3)⁻¹ + 1 / Real.sqrt c * Real.exp (-(η / 8) * t₀)) := by
      have h0 : 0 ≤ 2 * Ca * domInt η * (1 + 2 * cuspK3 κ₂) * M := by positivity
      have h1 : 0 ≤ 2 * Ca * ampC η * (cuspFarDy η κ₁ κ₂ C₂ + cuspFarDe η κ₁ κ₂) * M := by positivity
      have h2 : 0 ≤ M * ((w ^ 3)⁻¹ + 1 / Real.sqrt c * Real.exp (-(η / 8) * t₀)) := mul_nonneg hM hP
      nlinarith [mul_nonneg hD1 h2, mul_nonneg h0 hε]
    linarith

/-- **Third estimate of `fct:unscaled-cusp`**, in the paper's quantifier order: for fixed phase data and symbol constants
there is `C` with `‖∫_ℝ e^{icφ(τ;u)} a_c‖ ≤ C M ((cu)^{-3/2} + c^{-1/2} e^{-η' t₀})`, `η' = η/8`, for all `M ≥ 0`, `a_c`
with the symbol bounds, `c ≥ 1`, `u ≥ 1` and `t₀ > 0` with `𝔪 t₀ = u`. -/
theorem cuspInt_far_le_exists (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {η Ca : ℝ} (hη : 0 < η) (hCa : 0 ≤ Ca) :
    ∃ C : ℝ, ∀ (M : ℝ) (a : ℝ → ℂ) (c u t₀ : ℝ), 0 ≤ M → CuspAmp η Ca M a → 1 ≤ c → 1 ≤ u → 0 < t₀ →
      𝔪 t₀ = u → ‖cuspInt 𝔪 c u a‖ ≤
        C * M * ((c * u) ^ (-(3 : ℝ) / 2) + c ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 8) * t₀)) :=
  ⟨cuspFarC η κ₁ κ₂ C₂ Ca, fun _ _ _ _ _ hM ha hc hu ht₀ hv => cuspInt_far_le h ha hη hCa hM hc hu ht₀ hv⟩

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.cuspInt_far_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cuspInt_far_le

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.cuspInt_far_le_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cuspInt_far_le_exists

end Far

end FormalResearch.SignUncertainty.FctUnscaledCusp
