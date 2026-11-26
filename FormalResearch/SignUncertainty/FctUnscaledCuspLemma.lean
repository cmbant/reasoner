/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspFar

/-!
# `fct:unscaled-cusp`: the assembled lemma (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp` (label `fct:unscaled-cusp`).

`fct_unscaled_cusp` combines the three regimes (`cuspInt_abs_le`, `cuspInt_mid_le`, `cuspInt_far_le`): for phase data
`CuspPhase 𝔪 κ₁ κ₂ C₂ C₀` and amplitude constants `(η, C_a)` there are `C` and `η' > 0` (namely `η' = η/8`) such that for every
`M ≥ 0` and every amplitude `a_c` with the symbol bounds `CuspAmp η C_a M a`,

* `|∫_ℝ e^{icφ(τ;u)} a_c| ≤ C M` for all `c > 0`, `u`;
* `≤ C M c^{-1/2}` for `c^{-2/3} ≤ u ≤ 1`;
* `≤ C M ((cu)^{-3/2} + c^{-1/2} e^{-η' t₀})` for `c ≥ 1`, `u ≥ 1`, `t₀ > 0`, `𝔪 t₀ = u`;
* in particular `≤ C M c^{-1/2} u^{-3/2}` for `c ≥ 1`, `u ≥ 1`;
* (`cuspInt_far_le_log`) for `c ≥ 1`, `u ≥ 1` and `log c ≤ 4u + 4A`: `≤ C_A M (cu)^{-3/2}`.

Deviations from the paper's statement: "for sufficiently large `c`" is the explicit `c ≥ 1` in the third and fourth bullets (the
first two hold for every `c > 0`, the second needs `c^{-2/3} ≤ u ≤ 1`, which forces `c ≥ 1`); the hypothesis `|𝔪 - m| ≤ C₀` of
`CuspPhase` is not used by any regime.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

section Lemma

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ : ℝ}

/-- For `u ≥ 1`: `u^{-3/2} ≥ u^{-2}`, in the form `(√u³)⁻¹ ≥ (u²)⁻¹`. -/
lemma inv_sqrt_cube_ge {u : ℝ} (hu : 1 ≤ u) : (u ^ 2)⁻¹ ≤ (Real.sqrt u ^ 3)⁻¹ := by
  have hu0 : 0 < u := by linarith
  have hs : Real.sqrt u ≤ u := by
    rw [Real.sqrt_le_left hu0.le]; nlinarith
  have hs0 : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hs2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
  apply inv_anti₀ (by positivity)
  calc Real.sqrt u ^ 3 = Real.sqrt u ^ 2 * Real.sqrt u := by ring
    _ = u * Real.sqrt u := by rw [hs2]
    _ ≤ u * u := mul_le_mul_of_nonneg_left hs hu0.le
    _ = u ^ 2 := by ring

/-- The decay `u² e^{-η' t₀} ≤ (κ₃²/4) 24/η'⁴` for `𝔪 t₀ = u ≥ 1`. -/
lemma u_sq_mul_exp_le (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {η' t₀ u : ℝ} (hη' : 0 < η') (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u) :
    u ^ 2 * Real.exp (-η' * t₀) ≤ cuspK3 κ₂ ^ 2 / 4 * (24 / η' ^ 4) := by
  have hle := h.le_sq ht₀.le
  rw [hv] at hle
  have hκ3 := h.κ₃_pos
  have hu0 : 0 ≤ u := by
    have := h.nonneg ht₀.le
    rwa [hv] at this
  have h1 : u ^ 2 ≤ cuspK3 κ₂ ^ 2 / 4 * t₀ ^ 4 := by
    have : u ^ 2 ≤ (cuspK3 κ₂ * t₀ ^ 2 / 2) ^ 2 := pow_le_pow_left₀ hu0 hle 2
    calc u ^ 2 ≤ (cuspK3 κ₂ * t₀ ^ 2 / 2) ^ 2 := this
      _ = cuspK3 κ₂ ^ 2 / 4 * t₀ ^ 4 := by ring
  have h2 := pow_four_mul_exp_le hη' ht₀.le
  calc u ^ 2 * Real.exp (-η' * t₀) ≤ (cuspK3 κ₂ ^ 2 / 4 * t₀ ^ 4) * Real.exp (-η' * t₀) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = cuspK3 κ₂ ^ 2 / 4 * (t₀ ^ 4 * Real.exp (-η' * t₀)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The constant of the fourth bullet. -/
noncomputable def cuspLemmaC4 (η κ₂ Cf : ℝ) : ℝ := Cf * (1 + cuspK3 κ₂ ^ 2 / 4 * (24 / (η / 8) ^ 4))

/-- The "in particular" bound for `u ≥ 1`: `‖∫‖ ≤ C M c^{-1/2} u^{-3/2}`. -/
theorem cuspInt_far_le_simple (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {η Ca M : ℝ} {a : ℝ → ℂ} (ha : CuspAmp η Ca M a)
    (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M) {c u : ℝ} (hc : 1 ≤ c) (hu : 1 ≤ u) :
    ‖cuspInt 𝔪 c u a‖ ≤ cuspLemmaC4 η κ₂ (cuspFarC η κ₁ κ₂ C₂ Ca) * M *
      (c ^ (-(1 : ℝ) / 2) * u ^ (-(3 : ℝ) / 2)) := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  obtain ⟨t₀, ht₀, hv⟩ := h.exists_t0 hu0
  have h3 := cuspInt_far_le h ha hη hCa hM hc hu ht₀ hv
  have hC := cuspFarC_nonneg h hη hCa
  refine h3.trans ?_
  have e1 : (c * u) ^ (-(3 : ℝ) / 2) = c ^ (-(3 : ℝ) / 2) * u ^ (-(3 : ℝ) / 2) :=
    Real.mul_rpow hc0.le hu0.le
  have hcc : c ^ (-(3 : ℝ) / 2) ≤ c ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hc (by norm_num)
  have hupos : 0 < u ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hu0 _
  have hcpos : 0 < c ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hc0 _
  have hd := u_sq_mul_exp_le h (η' := η / 8) (by positivity) ht₀ hv
  -- `e^{-η' t₀} ≤ K1 u^{-3/2}`
  have hexp : Real.exp (-(η / 8) * t₀) ≤ cuspK3 κ₂ ^ 2 / 4 * (24 / (η / 8) ^ 4) * u ^ (-(3 : ℝ) / 2) := by
    have hu2 : 0 < u ^ 2 := by positivity
    have h1 : Real.exp (-(η / 8) * t₀) ≤ cuspK3 κ₂ ^ 2 / 4 * (24 / (η / 8) ^ 4) * (u ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hu2]; linarith
    refine h1.trans ?_
    rw [rpow_neg_three_half_eq hu0]
    exact mul_le_mul_of_nonneg_left (inv_sqrt_cube_ge hu) (by have := h.κ₃_pos; positivity)
  have hK1 : 0 ≤ cuspK3 κ₂ ^ 2 / 4 * (24 / (η / 8) ^ 4) := by positivity
  have hMC : 0 ≤ cuspFarC η κ₁ κ₂ C₂ Ca * M := mul_nonneg hC hM
  unfold cuspLemmaC4
  have hbr : (c * u) ^ (-(3 : ℝ) / 2) + c ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 8) * t₀) ≤
      (1 + cuspK3 κ₂ ^ 2 / 4 * (24 / (η / 8) ^ 4)) * (c ^ (-(1 : ℝ) / 2) * u ^ (-(3 : ℝ) / 2)) := by
    rw [e1]
    have h1 : c ^ (-(3 : ℝ) / 2) * u ^ (-(3 : ℝ) / 2) ≤ c ^ (-(1 : ℝ) / 2) * u ^ (-(3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hcc hupos.le
    have h2 : c ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 8) * t₀) ≤
        c ^ (-(1 : ℝ) / 2) * (cuspK3 κ₂ ^ 2 / 4 * (24 / (η / 8) ^ 4) * u ^ (-(3 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hexp hcpos.le
    nlinarith [h1, h2]
  calc _ ≤ cuspFarC η κ₁ κ₂ C₂ Ca * M * ((1 + cuspK3 κ₂ ^ 2 / 4 * (24 / (η / 8) ^ 4)) *
        (c ^ (-(1 : ℝ) / 2) * u ^ (-(3 : ℝ) / 2))) := mul_le_mul_of_nonneg_left hbr hMC
    _ = _ := by ring

/-- The phase grows superlinearly: `4u²/(5κ₃²) ≤ t₀ + 1` for `𝔪 t₀ = u`, `t₀ > 0` (from `u ≤ κ₃ log(1+t₀²)/2`). -/
lemma CuspPhase.quad_lb (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {t₀ u : ℝ} (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u) :
    4 * u ^ 2 / (5 * cuspK3 κ₂ ^ 2) ≤ t₀ + 1 := by
  have hκ3 := h.κ₃_pos
  have hu0 : 0 ≤ u := by
    have := h.nonneg ht₀.le
    rwa [hv] at this
  have h1 := (h.diff_bounds le_rfl ht₀.le).2
  rw [cuspLam_zero, h.zero, hv] at h1
  unfold cuspLam at h1
  set y : ℝ := 2 * u / cuspK3 κ₂ with hy
  have hy0 : 0 ≤ y := by positivity
  have hlog : y ≤ Real.log (1 + t₀ ^ 2) := by
    rw [hy, div_le_iff₀ hκ3]; linarith
  have hexp : Real.exp y ≤ 1 + t₀ ^ 2 := by
    rw [← Real.le_log_iff_exp_le (by positivity)]; exact hlog
  have h4 := Real.pow_div_factorial_le_exp y hy0 4
  have h24 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24] at h4
  have h5 : (y ^ 2 / 5) ^ 2 ≤ (t₀ + 1) ^ 2 := by
    have : (y ^ 2 / 5) ^ 2 = y ^ 4 / 25 := by ring
    rw [this]
    nlinarith [pow_nonneg hy0 4, sq_nonneg t₀]
  have h6 : y ^ 2 / 5 ≤ t₀ + 1 := by
    by_contra hlt
    push Not at hlt
    have := pow_lt_pow_left₀ hlt (by linarith) (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  have h7 : y ^ 2 / 5 = 4 * u ^ 2 / (5 * cuspK3 κ₂ ^ 2) := by
    rw [hy]; field_simp; ring
  rw [← h7]; exact h6

/-- The constant of the logarithmic range. -/
noncomputable def cuspLemmaC5 (η κ₂ Cf A : ℝ) : ℝ :=
  Cf * (1 + 2 * Real.exp (4 * A + η / 8 + 25 / (4 * (4 * (η / 8) / (5 * cuspK3 κ₂ ^ 2)))))

/-- **`fct:unscaled-cusp`, last clause.**  If `log c ≤ 4u + 4A` (`u ≥ ¼ log c - A`; the paper's `O(c⁻¹)` slack is
`A/c ≤ A`; the proof needs no sign of `A`), then the third bound is `≤ C_A M (cu)^{-3/2}`. -/
theorem cuspInt_far_le_log (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {η Ca M : ℝ} {a : ℝ → ℂ} (ha : CuspAmp η Ca M a)
    (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M) {A c u : ℝ} (hc : 1 ≤ c) (hu : 1 ≤ u)
    (hlog : Real.log c ≤ 4 * u + 4 * A) :
    ‖cuspInt 𝔪 c u a‖ ≤ cuspLemmaC5 η κ₂ (cuspFarC η κ₁ κ₂ C₂ Ca) A * M * (c * u) ^ (-(3 : ℝ) / 2) := by
  have hκ3 := h.κ₃_pos
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  obtain ⟨t₀, ht₀, hv⟩ := h.exists_t0 hu0
  have h3 := cuspInt_far_le h ha hη hCa hM hc hu ht₀ hv
  have hC := cuspFarC_nonneg h hη hCa
  refine h3.trans ?_
  set a₁ : ℝ := 4 * (η / 8) / (5 * cuspK3 κ₂ ^ 2) with ha₁
  have ha₁0 : 0 < a₁ := by positivity
  -- `c u² e^{-η t₀/8} ≤ 2 e^{4A + η/8 + 25/(4 a₁)}`
  have hq := h.quad_lb ht₀ hv
  have hexp1 : Real.exp (-(η / 8) * t₀) ≤ Real.exp (η / 8) * Real.exp (-(a₁ * u ^ 2)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : a₁ * u ^ 2 = (η / 8) * (4 * u ^ 2 / (5 * cuspK3 κ₂ ^ 2)) := by rw [ha₁]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hq (show 0 ≤ η / 8 by positivity)]
  have hcle : c ≤ Real.exp (4 * A) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    calc c = Real.exp (Real.log c) := (Real.exp_log hc0).symm
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  have hu2 : u ^ 2 ≤ 2 * Real.exp u := by
    have := Real.quadratic_le_exp_of_nonneg hu0.le
    nlinarith
  have hquad : 5 * u - a₁ * u ^ 2 ≤ 25 / (4 * a₁) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * a₁ * u - 5)]
  have hkey : c * u ^ 2 * Real.exp (-(η / 8) * t₀) ≤
      2 * Real.exp (4 * A + η / 8 + 25 / (4 * a₁)) := by
    have e1 : c * u ^ 2 * Real.exp (-(η / 8) * t₀) ≤
        (Real.exp (4 * A) * Real.exp (4 * u)) * (2 * Real.exp u) *
          (Real.exp (η / 8) * Real.exp (-(a₁ * u ^ 2))) := by
      have hE := Real.exp_pos (-(η / 8) * t₀)
      have := mul_le_mul hcle hu2 (sq_nonneg u) (by positivity)
      exact mul_le_mul this hexp1 hE.le (by positivity)
    refine e1.trans ?_
    have e2 : Real.exp (4 * A + η / 8 + (5 * u - a₁ * u ^ 2)) =
        Real.exp (4 * A) * Real.exp (4 * u) * Real.exp u * Real.exp (η / 8) * Real.exp (-(a₁ * u ^ 2)) := by
      rw [show 4 * A + η / 8 + (5 * u - a₁ * u ^ 2) = 4 * A + 4 * u + u + η / 8 + (-(a₁ * u ^ 2)) by ring]
      simp only [Real.exp_add]
    have e3 : (Real.exp (4 * A) * Real.exp (4 * u)) * (2 * Real.exp u) *
          (Real.exp (η / 8) * Real.exp (-(a₁ * u ^ 2))) =
        2 * Real.exp (4 * A + η / 8 + (5 * u - a₁ * u ^ 2)) := by rw [e2]; ring
    rw [e3]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num)
  set Kc : ℝ := 2 * Real.exp (4 * A + η / 8 + 25 / (4 * a₁)) with hKc
  have hKc0 : 0 < Kc := by positivity
  have hupos : 0 < u ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hu0 _
  have hcpos : 0 < c ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hc0 _
  have hce : c * Real.exp (-(η / 8) * t₀) ≤ Kc * u ^ (-(3 : ℝ) / 2) := by
    have hu2p : 0 < u ^ 2 := by positivity
    have h1 : c * Real.exp (-(η / 8) * t₀) ≤ Kc * (u ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hu2p]; linarith
    refine h1.trans ?_
    rw [rpow_neg_three_half_eq hu0]
    exact mul_le_mul_of_nonneg_left (inv_sqrt_cube_ge hu) hKc0.le
  have e1 : (c * u) ^ (-(3 : ℝ) / 2) = c ^ (-(3 : ℝ) / 2) * u ^ (-(3 : ℝ) / 2) :=
    Real.mul_rpow hc0.le hu0.le
  have e2 : c ^ (-(1 : ℝ) / 2) = c ^ (-(3 : ℝ) / 2) * c := by
    rw [← Real.rpow_add_one hc0.ne']; norm_num
  have hterm : c ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 8) * t₀) ≤ Kc * (c * u) ^ (-(3 : ℝ) / 2) := by
    rw [e2, e1]
    calc c ^ (-(3 : ℝ) / 2) * c * Real.exp (-(η / 8) * t₀) =
        c ^ (-(3 : ℝ) / 2) * (c * Real.exp (-(η / 8) * t₀)) := by ring
      _ ≤ c ^ (-(3 : ℝ) / 2) * (Kc * u ^ (-(3 : ℝ) / 2)) := mul_le_mul_of_nonneg_left hce hcpos.le
      _ = _ := by ring
  have hMC : 0 ≤ cuspFarC η κ₁ κ₂ C₂ Ca * M := mul_nonneg hC hM
  unfold cuspLemmaC5
  calc cuspFarC η κ₁ κ₂ C₂ Ca * M * ((c * u) ^ (-(3 : ℝ) / 2) + c ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 8) * t₀))
      ≤ cuspFarC η κ₁ κ₂ C₂ Ca * M * ((1 + Kc) * (c * u) ^ (-(3 : ℝ) / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hMC
        linarith
    _ = _ := by rw [hKc, ha₁]; ring

/-- **`fct:unscaled-cusp`** (absolute estimate for an unscaled square-root cusp).  For phase data
`CuspPhase 𝔪 κ₁ κ₂ C₂ C₀` and amplitude constants `(η, C_a)` there are `C` and `η' > 0` (`η' = η/8`) such that for every
`M ≥ 0` and `a_c` with the symbol bounds `CuspAmp η C_a M a`:
`|∫_ℝ e^{icφ(τ;u)} a_c| ≤ C M` (all `c > 0`, `u`); `≤ C M c^{-1/2}` (`c^{-2/3} ≤ u ≤ 1`);
`≤ C M ((cu)^{-3/2} + c^{-1/2} e^{-η' t₀})` (`c ≥ 1`, `u ≥ 1`, `t₀ > 0`, `𝔪 t₀ = u`); and in particular
`≤ C M c^{-1/2} u^{-3/2}` (`c ≥ 1`, `u ≥ 1`).  "For sufficiently large `c`" is the explicit `c ≥ 1`. -/
theorem fct_unscaled_cusp (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {η Ca : ℝ} (hη : 0 < η) (hCa : 0 ≤ Ca) :
    ∃ C η' : ℝ, 0 < η' ∧ ∀ (M : ℝ) (a : ℝ → ℂ), 0 ≤ M → CuspAmp η Ca M a →
      (∀ c u : ℝ, 0 < c → ‖cuspInt 𝔪 c u a‖ ≤ C * M) ∧
      (∀ c u : ℝ, 0 < c → c ^ (-(2 : ℝ) / 3) ≤ u → u ≤ 1 →
        ‖cuspInt 𝔪 c u a‖ ≤ C * M * c ^ (-(1 : ℝ) / 2)) ∧
      (∀ c u t₀ : ℝ, 1 ≤ c → 1 ≤ u → 0 < t₀ → 𝔪 t₀ = u →
        ‖cuspInt 𝔪 c u a‖ ≤
          C * M * ((c * u) ^ (-(3 : ℝ) / 2) + c ^ (-(1 : ℝ) / 2) * Real.exp (-η' * t₀))) ∧
      (∀ c u : ℝ, 1 ≤ c → 1 ≤ u →
        ‖cuspInt 𝔪 c u a‖ ≤ C * M * (c ^ (-(1 : ℝ) / 2) * u ^ (-(3 : ℝ) / 2))) := by
  set C1 : ℝ := 2 * Ca * domInt η with hC1
  set C2' : ℝ := 2 * Ca * ampC η * cuspMidC η κ₁ κ₂ with hC2'
  set C3 : ℝ := cuspFarC η κ₁ κ₂ C₂ Ca with hC3
  set C4 : ℝ := cuspLemmaC4 η κ₂ C3 with hC4
  refine ⟨max (max C1 C2') (max C3 C4), η / 8, by positivity, fun M a hM ha => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro c u hc
    refine (cuspInt_abs_le h.continuous h.even ha hη hCa hM c u).trans ?_
    have : C1 * M ≤ max (max C1 C2') (max C3 C4) * M :=
      mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hM
    calc _ = C1 * M := rfl
      _ ≤ _ := this
  · intro c u hc hcu hu1
    refine (cuspInt_mid_le h ha hη hCa hM hc hcu hu1).trans ?_
    have hp : 0 ≤ M * c ^ (-(1 : ℝ) / 2) := mul_nonneg hM (Real.rpow_nonneg hc.le _)
    have := mul_le_mul_of_nonneg_right ((le_max_right C1 C2').trans (le_max_left (max C1 C2') (max C3 C4))) hp
    calc _ = C2' * (M * c ^ (-(1 : ℝ) / 2)) := by ring
      _ ≤ _ := by linarith
  · intro c u t₀ hc hu ht₀ hv
    refine (cuspInt_far_le h ha hη hCa hM hc hu ht₀ hv).trans ?_
    have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
    have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
    have hp : 0 ≤ M * ((c * u) ^ (-(3 : ℝ) / 2) + c ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 8) * t₀)) := by positivity
    have := mul_le_mul_of_nonneg_right ((le_max_left C3 C4).trans (le_max_right (max C1 C2') (max C3 C4))) hp
    calc _ = C3 * (M * ((c * u) ^ (-(3 : ℝ) / 2) + c ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 8) * t₀))) := by
          ring
      _ ≤ _ := by linarith
  · intro c u hc hu
    refine (cuspInt_far_le_simple h ha hη hCa hM hc hu).trans ?_
    have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
    have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
    have hp : 0 ≤ M * (c ^ (-(1 : ℝ) / 2) * u ^ (-(3 : ℝ) / 2)) := by positivity
    have := mul_le_mul_of_nonneg_right ((le_max_right C3 C4).trans (le_max_right (max C1 C2') (max C3 C4))) hp
    calc _ = C4 * (M * (c ^ (-(1 : ℝ) / 2) * u ^ (-(3 : ℝ) / 2))) := by ring
      _ ≤ _ := by linarith

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.cuspInt_far_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cuspInt_far_le_log

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.fct_unscaled_cusp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fct_unscaled_cusp

end Lemma

end FormalResearch.SignUncertainty.FctUnscaledCusp
