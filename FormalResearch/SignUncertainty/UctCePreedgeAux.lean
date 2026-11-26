module

public import FormalResearch.SignUncertainty.UctPosFloorWpos
public import FormalResearch.SignUncertainty.CeGenOrigin
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# `uct:ce-band` (2) / `uct:ce-preedge` (2): `T₄` pre-edge floor check and `(iy)^{1/2}` origin inversion

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:ce-band` (2)
(also labelled `uct:ce-preedge`), including equation `(uct:sqrt-iy-inv)`.
Directly used by Proposition `fct:ce-preedge` Steps 1 and 2 in `constant_terms_five.tex`.

Main results:
* `uct_ce_preedge_T4_pos`: bounds for `T₄⁺(ζ) = η_{ĥ} W_pos(c^{1/3} ζ)` (`η_{ĥ} > 0`) on
  `Re ζ ≥ σ/2` and `|τ| ≤ σ/4`, with an absolute constant `C_pos` independent of `c, δ₀, η_{ĥ}`.
* `uct_ce_preedge_T4_neg`: bounds for `T₄⁻(ζ) = η₀ W_pos(c^{1/3}(1 - ζ))` (`0 ≤ η₀ ≤ K₀ c^{-2/5}`)
  against any positive comparison scale `T₁(σ)` obeying the three-regime lower bounds
  (`σ ≤ 1/2`, `x_- ≥ 1`, `x_- ≤ 1` with `x_- = c^{1/3}(1 - σ) > π Δ₁ c^{-2/3}`), giving
  `|T₄⁻(ζ)| ≤ (1/10) T₁(σ)` on both `|ζ - σ| ≤ (1 - σ)/2` and `Re ζ = σ`, and the Cauchy
  variation bound `|T₄⁻(σ + iτ) - T₄⁻(σ)| ≤ (|τ|/(1 - σ)) T₁(σ)` for `|τ| ≤ (1 - σ)/4`.
* `cpow_half_I_mul_eq_integral`: `(i y)^{1/2} = (2√π)⁻¹ ∫₀^∞ (1 - e^{-i y L}) L^{-3/2} dL` for all `y : ℝ`.
* `uct_sqrt_iy_inv`: equation `(uct:sqrt-iy-inv)`: for every `Δ > 0`,
  `(2π)⁻¹ ∫_ℝ 4^{-iy} Γ(iy) (iy)^{1/2} Δ^{-iy} dy = (2√π)⁻¹ ∫₀^∞ (e^{-4Δ} - e^{-4 e^L Δ}) L^{-3/2} dL ≥ 0`.

Class: proved, unconditional.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-! ### Part A: Auxiliary pre-edge floor `T₄ = T₄⁺ - T₄⁻` -/

/-- `T₄⁺(ζ) = η_{ĥ} W_pos(c^{1/3} ζ)` with `W_pos = liftSymbol uctSpos δ₀ 4`. -/
noncomputable def uctT4Pos (δ₀ c η_hhat : ℝ) (ζ : ℂ) : ℂ :=
  (η_hhat : ℂ) * liftSymbol uctSpos δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ζ)

/-- `T₄⁻(ζ) = η₀ W_pos(c^{1/3}(1 - ζ))` with `W_pos = liftSymbol uctSpos δ₀ 4`. -/
noncomputable def uctT4Neg (δ₀ c η₀ : ℝ) (ζ : ℂ) : ℂ :=
  (η₀ : ℂ) * liftSymbol uctSpos δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - ζ))

/-- **Lemma `uct:ce-preedge` (2), `T₄⁺` bounds:**
there is an absolute constant `C_pos > 0` (independent of `δ₀, c, η_{ĥ}, σ`) such that for every
`δ₀ > 0`, `c > 0`, `η_{ĥ} > 0`, and `σ > 0`:
* `T₄⁺(σ)` is real and strictly positive;
* `‖T₄⁺(σ + iτ)‖ ≤ C_pos * (T₄⁺(σ)).re` for all `τ : ℝ` (in fact on `Re ζ ≥ σ/2`);
* `‖T₄⁺(σ + iτ) - T₄⁺(σ)‖ ≤ 4 * C_pos * (|τ| / σ) * (T₄⁺(σ)).re` for `|τ| ≤ σ / 4`. -/
theorem uct_ce_preedge_T4_pos :
    ∃ Cpos : ℝ, 0 < Cpos ∧ ∀ {δ₀ c η_hhat σ : ℝ},
      0 < δ₀ → 0 < c → 0 < η_hhat → 0 < σ →
      0 < (uctT4Pos δ₀ c η_hhat (σ : ℂ)).re ∧
      (uctT4Pos δ₀ c η_hhat (σ : ℂ)).im = 0 ∧
      (∀ ζ : ℂ, σ / 2 ≤ ζ.re →
        ‖uctT4Pos δ₀ c η_hhat ζ‖ ≤ Cpos * (uctT4Pos δ₀ c η_hhat (σ : ℂ)).re) ∧
      (∀ τ : ℝ, |τ| ≤ σ / 4 →
        ‖uctT4Pos δ₀ c η_hhat ((σ : ℂ) + (τ : ℂ) * Complex.I) - uctT4Pos δ₀ c η_hhat (σ : ℂ)‖ ≤
          4 * Cpos * (|τ| / σ) * (uctT4Pos δ₀ c η_hhat (σ : ℂ)).re) := by
  obtain ⟨_, _, Cpos, hCpos, hpre⟩ := uct_pos_floor_pre_edge
  refine ⟨Cpos, hCpos, fun {δ₀ c η_hhat σ} hδ hc hη hσ => ?_⟩
  obtain ⟨hpos, _, hrel⟩ := hpre δ₀ hδ
  have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  set x : ℝ := c ^ (1 / 3 : ℝ) * σ with hx_def
  have hx : 0 < x := mul_pos hc13 hσ
  have hcast : ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (σ : ℂ) = (x : ℂ) := by
    rw [hx_def]; push_cast; ring
  have hre_eq : (uctT4Pos δ₀ c η_hhat (σ : ℂ)).re = η_hhat * (liftSymbol uctSpos δ₀ 4 (x : ℂ)).re := by
    unfold uctT4Pos; rw [hcast, Complex.re_ofReal_mul]
  have him_eq : (uctT4Pos δ₀ c η_hhat (σ : ℂ)).im = 0 := by
    unfold uctT4Pos; rw [hcast, Complex.im_ofReal_mul, (hpos x hx.le).2, mul_zero]
  obtain ⟨hrel_bd, hrel_var⟩ := hrel x hx
  refine ⟨?_, him_eq, ?_, ?_⟩
  · rw [hre_eq]; exact mul_pos hη (hpos x hx.le).1
  · intro ζ hζ
    unfold uctT4Pos
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le, hcast, Complex.re_ofReal_mul]
    have hw_re : x / 2 ≤ (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ζ).re := by
      rw [Complex.re_ofReal_mul, hx_def]; nlinarith
    calc η_hhat * ‖liftSymbol uctSpos δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ζ)‖
        ≤ η_hhat * (Cpos * (liftSymbol uctSpos δ₀ 4 (x : ℂ)).re) :=
          mul_le_mul_of_nonneg_left (hrel_bd _ hw_re) hη.le
      _ = Cpos * (η_hhat * (liftSymbol uctSpos δ₀ 4 (x : ℂ)).re) := by ring
  · intro τ hτ
    unfold uctT4Pos
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le, hcast, Complex.re_ofReal_mul]
    set y : ℝ := c ^ (1 / 3 : ℝ) * τ with hy_def
    have harg : ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) =
        (x : ℂ) + (y : ℂ) * Complex.I := by
      rw [hx_def, hy_def]; push_cast; ring
    have hy_le : |y| ≤ x / 4 := by
      rw [hy_def, abs_mul, abs_of_pos hc13, hx_def]; nlinarith
    have hdiv : |y| / x = |τ| / σ := by
      rw [hy_def, abs_mul, abs_of_pos hc13, hx_def]; field_simp [hc13.ne', hσ.ne']
    rw [harg]
    calc η_hhat * ‖liftSymbol uctSpos δ₀ 4 ((x : ℂ) + (y : ℂ) * Complex.I) - liftSymbol uctSpos δ₀ 4 (x : ℂ)‖
        ≤ η_hhat * (4 * Cpos * (|y| / x) * (liftSymbol uctSpos δ₀ 4 (x : ℂ)).re) :=
          mul_le_mul_of_nonneg_left (hrel_var y hy_le) hη.le
      _ = 4 * Cpos * (|τ| / σ) * (η_hhat * (liftSymbol uctSpos δ₀ 4 (x : ℂ)).re) := by
          rw [hdiv]; ring

/-- **Lemma `uct:ce-preedge` (2), `T₄⁻` bounds:**
given `K₀ ≥ 0`, `Δ₁ > 0`, and positive comparison constants `c₁, c₂, c₃ > 0`, there is
`c₀ = c₀(K₀, Δ₁, c₁, c₂, c₃) ≥ 60` (independent of `δ₀ > 0`) such that for all `c ≥ c₀`,
all `δ₀ > 0`, all `0 ≤ η₀ ≤ K₀ c^{-2/5}`, every `σ ∈ (0, 1)` with
`x_- = c^{1/3}(1 - σ) > π Δ₁ c^{-2/3}`, and every `T₁ > 0` satisfying
* `σ ≤ 1/2 → c₁ c^{-5/6} σ^{-1/2} ≤ T₁`,
* `1 ≤ x_- → c₂ x_-^{-5/2} ≤ T₁`,
* `x_- ≤ 1 → c₃ x_-^{1/2} ≤ T₁`,

we have `‖T₄⁻(ζ)‖ ≤ (1/10) T₁` on both the disc `‖ζ - σ‖ ≤ (1 - σ)/2` and the vertical line
`Re ζ = σ`, and `‖T₄⁻(σ + iτ) - T₄⁻(σ)‖ ≤ (|τ|/(1 - σ)) T₁` for `|τ| ≤ (1 - σ)/4`.
(Note: the `σ ≤ 1/2` hypothesis is actually redundant once `x_- ≥ 1` holds for `σ ≤ 1/2`, which is
automatic for `c ≥ 8`, so the proof needs only the `x_- ≥ 1` and `x_- ≤ 1` regimes.) -/
theorem uct_ce_preedge_T4_neg {K₀ Δ₁ c₁ c₂ c₃ : ℝ}
    (hK₀ : 0 ≤ K₀) (hΔ₁ : 0 < Δ₁) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ c₀ : ℝ, 60 ≤ c₀ ∧ ∀ {c δ₀ η₀ σ T₁ : ℝ},
      c₀ ≤ c → 0 < δ₀ → 0 ≤ η₀ → η₀ ≤ K₀ * c ^ (-(2 / 5 : ℝ)) →
      0 < σ → σ < 1 →
      π * Δ₁ * c ^ (-(2 / 3 : ℝ)) < c ^ (1 / 3 : ℝ) * (1 - σ) →
      0 < T₁ →
      (σ ≤ 1 / 2 → c₁ * c ^ (-(5 / 6 : ℝ)) * σ ^ (-(1 / 2 : ℝ)) ≤ T₁) →
      (1 ≤ c ^ (1 / 3 : ℝ) * (1 - σ) → c₂ * (c ^ (1 / 3 : ℝ) * (1 - σ)) ^ (-(5 / 2 : ℝ)) ≤ T₁) →
      (c ^ (1 / 3 : ℝ) * (1 - σ) ≤ 1 → c₃ * (c ^ (1 / 3 : ℝ) * (1 - σ)) ^ (1 / 2 : ℝ) ≤ T₁) →
      (∀ ζ : ℂ, (‖ζ - (σ : ℂ)‖ ≤ (1 - σ) / 2 ∨ ζ.re = σ) →
        ‖uctT4Neg δ₀ c η₀ ζ‖ ≤ (1 / 10 : ℝ) * T₁) ∧
      (∀ τ : ℝ, |τ| ≤ (1 - σ) / 4 →
        ‖uctT4Neg δ₀ c η₀ ((σ : ℂ) + (τ : ℂ) * Complex.I) - uctT4Neg δ₀ c η₀ (σ : ℂ)‖ ≤
          (|τ| / (1 - σ)) * T₁) := by
  obtain ⟨C, hC, _, _, hpre⟩ := uct_pos_floor_pre_edge
  let M : ℝ := 2 ^ (5 / 2 : ℝ) * C * K₀ * max (2 ^ (5 / 2 : ℝ) / c₁) (max (1 / c₂) (1 / (c₃ * √(π * Δ₁))))
  have hM_nn : 0 ≤ M := by positivity
  refine ⟨max 60 ((10 * M + 1) ^ (15 : ℝ)), le_max_left _ _,
    fun {c δ₀ η₀ σ T₁} hc hδ hη₀ hη_le hσ0 hσ1 hx_lo hT₁ _hreg1 hreg2 hreg3 => ?_⟩
  have hc60 : 60 ≤ c := (le_max_left _ _).trans hc
  have hc_pos : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
  set s : ℝ := 1 - σ with hs_def
  have hs_pos : 0 < s := by linarith
  set xm : ℝ := c ^ (1 / 3 : ℝ) * s with hxm_def
  have hxm_pos : 0 < xm := mul_pos hc13 hs_pos
  have hdecay := (hpre δ₀ hδ).2.1
  have hmain_bd : ∀ ζ : ℂ, (‖ζ - (σ : ℂ)‖ ≤ s / 2 ∨ ζ.re = σ) →
      ‖uctT4Neg δ₀ c η₀ ζ‖ ≤ (1 / 10 : ℝ) * T₁ := by
    intro ζ hζ
    have hre_ge : s / 2 ≤ (1 - ζ).re := by
      rcases hζ with hball | hline
      · have h1 := Complex.abs_re_le_norm (ζ - (σ : ℂ))
        simp only [Complex.sub_re, Complex.ofReal_re] at h1
        have h2 := (abs_le.mp (h1.trans hball)).2
        simp only [Complex.sub_re, Complex.one_re]; linarith
      · simp only [Complex.sub_re, Complex.one_re, hline]; linarith
    have hw_re : xm / 2 ≤ (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - ζ)).re := by
      rw [Complex.re_ofReal_mul, hxm_def]; nlinarith
    have hw_nn : 0 ≤ (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - ζ)).re := by linarith
    have hstep1 : ‖uctT4Neg δ₀ c η₀ ζ‖ ≤ 2 ^ (5 / 2 : ℝ) * C * K₀ * c ^ (-(2 / 5 : ℝ)) * (1 + xm) ^ (-(5 / 2 : ℝ)) := by
      unfold uctT4Neg
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hη₀]
      have hW := hdecay (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - ζ)) hw_nn
      have hpow1 : (1 + (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - ζ)).re) ^ (-(5 / 2 : ℝ)) ≤
          (1 + xm / 2) ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
      have hpow2 : (1 + xm / 2) ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * (1 + xm) ^ (-(5 / 2 : ℝ)) := by
        have h1 : (1 + xm / 2) ^ (-(5 / 2 : ℝ)) ≤ (2⁻¹ * (1 + xm)) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
        have h2 : ((2 : ℝ)⁻¹) ^ (-(5 / 2 : ℝ)) = 2 ^ (5 / 2 : ℝ) := by
          rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
        rw [Real.mul_rpow (by norm_num) (by linarith), h2] at h1
        exact h1
      calc η₀ * ‖liftSymbol uctSpos δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - ζ))‖
          ≤ (K₀ * c ^ (-(2 / 5 : ℝ))) * (C * (2 ^ (5 / 2 : ℝ) * (1 + xm) ^ (-(5 / 2 : ℝ)))) :=
            mul_le_mul hη_le (hW.trans (mul_le_mul_of_nonneg_left (hpow1.trans hpow2) hC.le))
              (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hcmp : c ^ (-(2 / 5 : ℝ)) * (1 + xm) ^ (-(5 / 2 : ℝ)) ≤
        max (2 ^ (5 / 2 : ℝ) / c₁) (max (1 / c₂) (1 / (c₃ * √(π * Δ₁)))) * c ^ (-(1 / 15 : ℝ)) * T₁ := by
      have hc25_le_115 : c ^ (-(2 / 5 : ℝ)) ≤ c ^ (-(1 / 15 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      by_cases hxm1 : 1 ≤ xm
      · have hT := hreg2 hxm1
        have hpow : (1 + xm) ^ (-(5 / 2 : ℝ)) ≤ xm ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hxm_pos (by linarith) (by norm_num)
        have h1 : xm ^ (-(5 / 2 : ℝ)) ≤ (1 / c₂) * T₁ := by
          rw [one_div, inv_mul_eq_div, le_div_iff₀ hc₂]; linarith
        have hmax : 1 / c₂ ≤ max (2 ^ (5 / 2 : ℝ) / c₁) (max (1 / c₂) (1 / (c₃ * √(π * Δ₁)))) :=
          (le_max_left _ _).trans (le_max_right _ _)
        calc c ^ (-(2 / 5 : ℝ)) * (1 + xm) ^ (-(5 / 2 : ℝ))
            ≤ c ^ (-(1 / 15 : ℝ)) * ((1 / c₂) * T₁) :=
              mul_le_mul hc25_le_115 (hpow.trans h1) (by positivity) (by positivity)
          _ = (1 / c₂) * c ^ (-(1 / 15 : ℝ)) * T₁ := by ring
          _ ≤ max (2 ^ (5 / 2 : ℝ) / c₁) (max (1 / c₂) (1 / (c₃ * √(π * Δ₁)))) * c ^ (-(1 / 15 : ℝ)) * T₁ := by
              gcongr
      · push Not at hxm1
        have hT := hreg3 hxm1.le
        have hpow : (1 + xm) ^ (-(5 / 2 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
        have hxm_sqrt : √(π * Δ₁) * c ^ (-(1 / 3 : ℝ)) ≤ xm ^ (1 / 2 : ℝ) := by
          have h1 : (π * Δ₁ * c ^ (-(2 / 3 : ℝ))) ^ (1 / 2 : ℝ) ≤ xm ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hx_lo.le (by norm_num)
          have h2 : (π * Δ₁ * c ^ (-(2 / 3 : ℝ))) ^ (1 / 2 : ℝ) = √(π * Δ₁) * c ^ (-(1 / 3 : ℝ)) := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc_pos.le,
              ← Real.sqrt_eq_rpow]
            norm_num
          exact h2 ▸ h1
        have hT_lb : c₃ * √(π * Δ₁) * c ^ (-(1 / 3 : ℝ)) ≤ T₁ := by
          calc c₃ * √(π * Δ₁) * c ^ (-(1 / 3 : ℝ)) = c₃ * (√(π * Δ₁) * c ^ (-(1 / 3 : ℝ))) := by ring
            _ ≤ c₃ * xm ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hxm_sqrt hc₃.le
            _ ≤ T₁ := hT
        have hc_split : c ^ (-(2 / 5 : ℝ)) = c ^ (-(1 / 15 : ℝ)) * c ^ (-(1 / 3 : ℝ)) := by
          rw [← Real.rpow_add hc_pos]; congr 1; norm_num
        have hmax : 1 / (c₃ * √(π * Δ₁)) ≤ max (2 ^ (5 / 2 : ℝ) / c₁) (max (1 / c₂) (1 / (c₃ * √(π * Δ₁)))) :=
          (le_max_right _ _).trans (le_max_right _ _)
        have hden_pos : 0 < c₃ * √(π * Δ₁) := by positivity
        have h1 : c ^ (-(1 / 3 : ℝ)) ≤ (1 / (c₃ * √(π * Δ₁))) * T₁ := by
          rw [show 1 / (c₃ * √(π * Δ₁)) * T₁ = T₁ / (c₃ * √(π * Δ₁)) by ring, le_div_iff₀ hden_pos]
          linarith
        calc c ^ (-(2 / 5 : ℝ)) * (1 + xm) ^ (-(5 / 2 : ℝ))
            ≤ c ^ (-(2 / 5 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = c ^ (-(1 / 15 : ℝ)) * c ^ (-(1 / 3 : ℝ)) := by rw [mul_one, hc_split]
          _ ≤ c ^ (-(1 / 15 : ℝ)) * ((1 / (c₃ * √(π * Δ₁))) * T₁) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (1 / (c₃ * √(π * Δ₁))) * c ^ (-(1 / 15 : ℝ)) * T₁ := by ring
          _ ≤ max (2 ^ (5 / 2 : ℝ) / c₁) (max (1 / c₂) (1 / (c₃ * √(π * Δ₁)))) * c ^ (-(1 / 15 : ℝ)) * T₁ := by
              gcongr
    have hM_small : M * c ^ (-(1 / 15 : ℝ)) ≤ 1 / 10 := by
      have hc_ge : (10 * M + 1) ^ (15 : ℝ) ≤ c := (le_max_right _ _).trans hc
      have h1 : 10 * M + 1 ≤ c ^ (1 / 15 : ℝ) := by
        have h2 := Real.rpow_le_rpow (by positivity) hc_ge (by norm_num : (0 : ℝ) ≤ 1 / 15)
        rw [← Real.rpow_mul (by positivity), show (15 : ℝ) * (1 / 15 : ℝ) = 1 by norm_num,
          Real.rpow_one] at h2
        exact h2
      have hc15_pos : 0 < c ^ (1 / 15 : ℝ) := Real.rpow_pos_of_pos hc_pos _
      rw [Real.rpow_neg hc_pos.le, ← div_eq_mul_inv, div_le_iff₀ hc15_pos]
      linarith
    calc ‖uctT4Neg δ₀ c η₀ ζ‖
        ≤ 2 ^ (5 / 2 : ℝ) * C * K₀ * (c ^ (-(2 / 5 : ℝ)) * (1 + xm) ^ (-(5 / 2 : ℝ))) := by
          linarith [hstep1]
      _ ≤ 2 ^ (5 / 2 : ℝ) * C * K₀ *
            (max (2 ^ (5 / 2 : ℝ) / c₁) (max (1 / c₂) (1 / (c₃ * √(π * Δ₁)))) * c ^ (-(1 / 15 : ℝ)) * T₁) :=
          mul_le_mul_of_nonneg_left hcmp (by positivity)
      _ = (M * c ^ (-(1 / 15 : ℝ))) * T₁ := by dsimp [M]; ring
      _ ≤ (1 / 10 : ℝ) * T₁ := mul_le_mul_of_nonneg_right hM_small hT₁.le
  refine ⟨hmain_bd, fun τ hτ => ?_⟩
  let F : ℂ → ℂ := fun w => uctT4Neg δ₀ c η₀ (1 - w)
  have hF_diff : DifferentiableOn ℂ F {w : ℂ | 0 < w.re} := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * z) w :=
      (differentiableAt_id.const_mul _)
    have h2 : DifferentiableWithinAt ℂ (liftSymbol uctSpos δ₀ 4) {z : ℂ | 0 < z.re}
        (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * w) :=
      liftSymbol_differentiableOn hasU2_uctSpos δ₀ 4 _ (by
        show 0 < (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * w).re
        rw [Complex.re_ofReal_mul]; exact mul_pos hc13 hw)
    have h3 : DifferentiableAt ℂ (liftSymbol uctSpos δ₀ 4) (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * w) :=
      h2.differentiableAt (IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) (by
        show 0 < (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * w).re
        rw [Complex.re_ofReal_mul]; exact mul_pos hc13 hw))
    have h4 : DifferentiableAt ℂ F w := by
      have hFeq : F = fun z : ℂ => (η₀ : ℂ) * liftSymbol uctSpos δ₀ 4 (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * z) := by
        funext z; simp [F, uctT4Neg]
      rw [hFeq]
      exact (h3.comp w h1).const_mul (η₀ : ℂ)
    exact h4.differentiableWithinAt
  have hvar := local_variation_right hF_diff hs_pos (B := (1 / 10 : ℝ) * T₁)
    (fun w _ hw_ball => by
      apply hmain_bd (1 - w) (Or.inl ?_)
      have hsub : (1 - w) - (σ : ℂ) = -(w - (s : ℂ)) := by rw [hs_def]; push_cast; ring
      rw [hsub, norm_neg]; exact hw_ball)
    (-τ) (by simpa [abs_neg] using hτ)
  have hF1 : F ((s : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I) = uctT4Neg δ₀ c η₀ ((σ : ℂ) + (τ : ℂ) * Complex.I) := by
    simp only [F, hs_def]; congr 1; push_cast; ring
  have hF2 : F (s : ℂ) = uctT4Neg δ₀ c η₀ (σ : ℂ) := by
    simp only [F, hs_def]; congr 1; push_cast; ring
  rw [hF1, hF2, abs_neg] at hvar
  have h410 : 4 * ((1 / 10 : ℝ) * T₁) / s * |τ| ≤ (|τ| / s) * T₁ := by
    have h1 : 4 * ((1 / 10 : ℝ) * T₁) / s * |τ| = (2 / 5 : ℝ) * ((|τ| / s) * T₁) := by ring
    rw [h1]
    have hnn : 0 ≤ (|τ| / s) * T₁ := by positivity
    linarith
  exact hvar.trans h410

/-! ### Part B: `(iy)^{1/2}` integral representation and `(uct:sqrt-iy-inv)` -/

private lemma exp_log_div_two {r : ℝ} (hr : 0 < r) : Real.exp (Real.log r / 2) = √r := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]; congr 1; ring

private lemma one_add_abs_rpow_neg_two_le (y : ℝ) :
    (1 + |y|) ^ (-(2 : ℝ)) ≤ 2 * (1 + y ^ 2)⁻¹ := by
  rw [Real.rpow_neg (by positivity), Real.rpow_two, inv_eq_one_div, ← div_eq_mul_inv,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_abs y, abs_nonneg y]

private lemma norm_one_sub_exp_neg_le_min {w : ℂ} (hw : 0 ≤ w.re) :
    ‖1 - Complex.exp (-w)‖ ≤ min ‖w‖ 2 := by
  refine le_min ?_ ?_
  · have hftc : (1 : ℂ) - Complex.exp (-w) = ∫ t in (0 : ℝ)..1, w * Complex.exp (-(t : ℂ) * w) := by
      have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
          HasDerivAt (fun s : ℝ => -Complex.exp (-(s : ℂ) * w)) (w * Complex.exp (-(t : ℂ) * w)) t := by
        intro t _
        have h1 : HasDerivAt (fun s : ℝ => -(s : ℂ) * w) (-w) t := by
          have := (Complex.ofRealCLM.hasDerivAt (x := t)).neg.mul_const w
          simpa using this
        have h2 : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) * w)) (Complex.exp (-(t : ℂ) * w) * (-w)) t :=
          (Complex.hasDerivAt_exp (-(t : ℂ) * w)).comp t h1
        exact h2.neg.congr_deriv (by ring)
      have hint : IntervalIntegrable (fun t : ℝ => w * Complex.exp (-(t : ℂ) * w)) volume 0 1 :=
        (by fun_prop : Continuous fun t : ℝ => w * Complex.exp (-(t : ℂ) * w)).intervalIntegrable 0 1
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      simp; ring
    rw [hftc]
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := ‖w‖)
      (f := fun t : ℝ => w * Complex.exp (-(t : ℂ) * w)) (fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        rw [norm_mul, Complex.norm_exp]
        have hre : (-(t : ℂ) * w).re = -t * w.re := by simp
        rw [hre]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (Real.exp_le_one_iff.mpr (by nlinarith [ht.1, hw])))
    simpa using hbd
  · calc ‖1 - Complex.exp (-w)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-w)‖ := norm_sub_le _ _
      _ = 1 + Real.exp (-w.re) := by rw [norm_one, Complex.norm_exp, Complex.neg_re]
      _ ≤ 1 + 1 := by gcongr; exact Real.exp_le_one_iff.mpr (by linarith)
      _ = 2 := by norm_num

/-- For `a ≥ 0`, `L ↦ min (a * L) 2 * L^{-3/2}` is integrable on `(0, ∞)`. -/
private lemma integrableOn_min_rpow_neg_three_halves_nonneg {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun L : ℝ => min (a * L) 2 * L ^ (-(3 / 2 : ℝ))) (Ioi (0 : ℝ)) := by
  have h1 : IntegrableOn (fun L : ℝ => a * L ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).1.const_mul a
  have h2 : IntegrableOn (fun L : ℝ => 2 * L ^ (-(3 / 2 : ℝ))) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) zero_lt_one).const_mul 2
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hmin_cont : Continuous fun L : ℝ => min (a * L) 2 := Continuous.min (by fun_prop) continuous_const
  rw [hsplit, integrableOn_union]
  refine ⟨h1.mono' ?_ ?_, h2.mono' ?_ ?_⟩
  · exact (hmin_cont.continuousOn.mul
      (ContinuousOn.rpow_const continuousOn_id (fun L (hL : L ∈ Ioc 0 1) => Or.inl hL.1.ne'))).aestronglyMeasurable
      measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
    have hL0 : 0 < L := hL.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_min (mul_nonneg ha hL0.le) (by norm_num)),
      abs_of_pos (Real.rpow_pos_of_pos hL0 _)]
    calc min (a * L) 2 * L ^ (-(3 / 2 : ℝ))
        ≤ (a * L) * L ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = a * (L ^ (1 : ℝ) * L ^ (-(3 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
      _ = a * L ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hL0]; norm_num
  · exact (hmin_cont.continuousOn.mul
      (ContinuousOn.rpow_const continuousOn_id (fun L hL => Or.inl (lt_trans zero_lt_one hL).ne'))).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
    have hL0 : 0 < L := lt_trans zero_lt_one hL
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_min (mul_nonneg ha hL0.le) (by norm_num)),
      abs_of_pos (Real.rpow_pos_of_pos hL0 _)]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)

private lemma integral_min_rpow_neg_three_halves_le {a : ℝ} (ha : 0 < a) :
    ∫ L in Ioi (0 : ℝ), min (a * L) 2 * L ^ (-(3 / 2 : ℝ)) ≤ 4 * √2 * √a := by
  set c : ℝ := 2 / a with hc_def
  have hc_pos : 0 < c := by positivity
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) c ∪ Ioi c := (Ioc_union_Ioi_eq_Ioi hc_pos.le).symm
  have hint := integrableOn_min_rpow_neg_three_halves_nonneg ha.le
  rw [hsplit, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self)
    (hint.mono_set (Ioi_subset_Ioi hc_pos.le))]
  have hleft : ∫ L in Ioc (0 : ℝ) c, min (a * L) 2 * L ^ (-(3 / 2 : ℝ)) ≤ 2 * √2 * √a := by
    have h1 : IntegrableOn (fun L : ℝ => a * L ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) c) :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).1.const_mul a
    calc ∫ L in Ioc (0 : ℝ) c, min (a * L) 2 * L ^ (-(3 / 2 : ℝ))
        ≤ ∫ L in Ioc (0 : ℝ) c, a * L ^ (-(1 / 2 : ℝ)) := by
          refine setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self) h1
            measurableSet_Ioc fun L hL => ?_
          have hL0 : 0 < L := hL.1
          calc min (a * L) 2 * L ^ (-(3 / 2 : ℝ))
              ≤ (a * L) * L ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
            _ = a * (L ^ (1 : ℝ) * L ^ (-(3 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
            _ = a * L ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hL0]; norm_num
      _ = a * ∫ L in (0 : ℝ)..c, L ^ (-(1 / 2 : ℝ)) := by
          rw [integral_const_mul, intervalIntegral.integral_of_le hc_pos.le]
      _ = a * (c ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) := by
          rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
          norm_num
      _ = 2 * √2 * √a := by
          rw [hc_def, ← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num)]
          have hsq : √a * √a = a := Real.mul_self_sqrt ha.le
          have hne : √a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
          field_simp [hne]; nlinarith [hsq]
  have hright : ∫ L in Ioi c, min (a * L) 2 * L ^ (-(3 / 2 : ℝ)) ≤ 2 * √2 * √a := by
    have h2 : IntegrableOn (fun L : ℝ => 2 * L ^ (-(3 / 2 : ℝ))) (Ioi c) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hc_pos).const_mul 2
    calc ∫ L in Ioi c, min (a * L) 2 * L ^ (-(3 / 2 : ℝ))
        ≤ ∫ L in Ioi c, 2 * L ^ (-(3 / 2 : ℝ)) := by
          refine setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi hc_pos.le)) h2 measurableSet_Ioi
            fun L hL => mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (lt_trans hc_pos hL).le _)
      _ = 2 * ∫ L in Ioi c, L ^ (-(3 / 2 : ℝ)) := integral_const_mul _ _
      _ = 2 * (-c ^ (-(1 / 2 : ℝ)) / (-(1 / 2 : ℝ))) := by
          rw [integral_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hc_pos]
          norm_num
      _ = 2 * √2 * √a := by
          rw [hc_def, Real.rpow_neg hc_pos.le, ← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num)]
          have hne : √2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
          have hsq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          field_simp [hne]; linarith [hsq2]
  linarith

private lemma tendsto_setIntegral_Icc_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    Tendsto (fun n : ℕ => ∫ L in Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1), f L)
      atTop (𝓝 (∫ L in Ioi (0 : ℝ), f L)) := by
  have heq : ∀ n : ℕ, ∫ L in Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1), f L =
      ∫ L in Ioi (0 : ℝ), (Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1)).indicator f L := fun n => by
    rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr
      (fun L (hL : L ∈ Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1)) =>
        lt_of_lt_of_le (inv_pos.mpr (by positivity : (0 : ℝ) < (n : ℝ) + 1)) hL.1)]
  simp_rw [heq]
  refine tendsto_integral_of_dominated_convergence (fun L => ‖f L‖) ?_ hf.norm ?_ ?_
  · intro n; exact hf.1.indicator measurableSet_Icc
  · intro n; filter_upwards with L; exact norm_indicator_le_norm_self _ _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
    have hL0 : 0 < L := hL
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt L⁻¹
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt L
    refine tendsto_atTop_of_eventually_const (i₀ := max N₁ N₂) fun n hn => ?_
    have hn1 : L⁻¹ < (n : ℝ) + 1 := lt_of_lt_of_le hN₁ (by exact_mod_cast (le_max_left N₁ N₂).trans hn |>.trans (Nat.le_succ n))
    have hn2 : L < (n : ℝ) + 1 := lt_of_lt_of_le hN₂ (by exact_mod_cast (le_max_right N₁ N₂).trans hn |>.trans (Nat.le_succ n))
    have hmem : L ∈ Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1) :=
      ⟨(inv_lt_comm₀ hL0 (by positivity)).mp hn1 |>.le, hn2.le⟩
    exact Set.indicator_of_mem hmem f

private lemma integral_one_sub_exp_neg_rpow_one :
    ∫ L in Ioi (0 : ℝ), (1 - Real.exp (-L)) * L ^ (-(3 / 2 : ℝ)) = 2 * √π := by
  have hint : IntegrableOn (fun L : ℝ => (1 - Real.exp (-L)) * L ^ (-(3 / 2 : ℝ))) (Ioi (0 : ℝ)) := by
    refine (integrableOn_min_rpow_neg_three_halves_nonneg zero_le_one).mono' ?_ ?_
    · exact ((continuousOn_const.sub (Real.continuous_exp.comp continuous_neg).continuousOn).mul
        (ContinuousOn.rpow_const continuousOn_id (fun L hL => Or.inl (Set.mem_Ioi.mp hL).ne'))).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
      have hL0 : 0 < L := hL
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))),
        abs_of_pos (Real.rpow_pos_of_pos hL0 _)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine le_min ?_ ?_
      · rw [one_mul]; linarith [Real.add_one_le_exp (-L)]
      · linarith [Real.exp_pos (-L)]
  have hGamma : ∫ L in Ioi (0 : ℝ), Real.exp (-L) * L ^ (-(1 / 2 : ℝ)) = √π := by
    have h := Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.Gamma_one_half_eq] at h
    rw [h]
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    norm_num
  have hGamma_int : IntegrableOn (fun L : ℝ => Real.exp (-L) * L ^ (-(1 / 2 : ℝ))) (Ioi (0 : ℝ)) := by
    have h := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)
    refine h.congr_fun (fun L _ => ?_) measurableSet_Ioi
    norm_num
  have hibp : ∀ n : ℕ,
      ∫ L in (((n : ℝ) + 1)⁻¹ : ℝ)..((n : ℝ) + 1), (1 - Real.exp (-L)) * L ^ (-(3 / 2 : ℝ)) =
        (1 - Real.exp (-((n : ℝ) + 1))) * (-2 * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))) -
        (1 - Real.exp (-(((n : ℝ) + 1)⁻¹))) * (-2 * (((n : ℝ) + 1)⁻¹) ^ (-(1 / 2 : ℝ))) +
        2 * ∫ L in (((n : ℝ) + 1)⁻¹ : ℝ)..((n : ℝ) + 1), Real.exp (-L) * L ^ (-(1 / 2 : ℝ)) := by
    intro n
    set a : ℝ := ((n : ℝ) + 1)⁻¹ with ha_def
    set b : ℝ := (n : ℝ) + 1 with hb_def
    have ha_pos : 0 < a := inv_pos.mpr (by positivity)
    have hab : a ≤ b := by
      have h1 : (1 : ℝ) ≤ b := by linarith
      exact (inv_le_one_of_one_le₀ h1).trans h1
    have hderiv_u : ∀ x ∈ uIcc a b,
        HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-x)) x := fun x _ => by
      have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * (-1)) x :=
        (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
      exact ((hasDerivAt_const x (1 : ℝ)).sub h1).congr_deriv (by ring)
    have hderiv_v : ∀ x ∈ uIcc a b,
        HasDerivAt (fun t : ℝ => -2 * t ^ (-(1 / 2 : ℝ))) (x ^ (-(3 / 2 : ℝ))) x := fun x hx => by
      rw [uIcc_of_le hab] at hx
      have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
      have h1 := (Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hx_pos.ne')).const_mul (-2)
      convert h1 using 1; norm_num; ring
    have hu' : IntervalIntegrable (fun x : ℝ => Real.exp (-x)) volume a b :=
      (by fun_prop : Continuous fun x : ℝ => Real.exp (-x)).intervalIntegrable a b
    have hv' : IntervalIntegrable (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) volume a b :=
      (ContinuousOn.rpow_const continuousOn_id fun x hx => by
        rw [uIcc_of_le hab] at hx; exact Or.inl (lt_of_lt_of_le ha_pos hx.1).ne').intervalIntegrable
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hderiv_u hderiv_v hu' hv'
    rw [hparts]
    have hsub : ∫ x in a..b, Real.exp (-x) * (-2 * x ^ (-(1 / 2 : ℝ))) =
        -2 * ∫ x in a..b, Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => by ring
    rw [hsub]; ring
  have h_top_lim : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hlim_lhs : Tendsto (fun n : ℕ =>
      ∫ L in (((n : ℝ) + 1)⁻¹ : ℝ)..((n : ℝ) + 1), (1 - Real.exp (-L)) * L ^ (-(3 / 2 : ℝ)))
      atTop (𝓝 (∫ L in Ioi (0 : ℝ), (1 - Real.exp (-L)) * L ^ (-(3 / 2 : ℝ)))) :=
    (tendsto_setIntegral_Icc_Ioi hint).congr fun n => by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
        ((inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)).trans (by linarith))]
  have hlim_rhs : Tendsto (fun n : ℕ =>
      (1 - Real.exp (-((n : ℝ) + 1))) * (-2 * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))) -
      (1 - Real.exp (-(((n : ℝ) + 1)⁻¹))) * (-2 * (((n : ℝ) + 1)⁻¹) ^ (-(1 / 2 : ℝ))) +
      2 * ∫ L in (((n : ℝ) + 1)⁻¹ : ℝ)..((n : ℝ) + 1), Real.exp (-L) * L ^ (-(1 / 2 : ℝ)))
      atTop (𝓝 (0 - 0 + 2 * √π)) := by
    have h_hi : Tendsto (fun n : ℕ =>
        (1 - Real.exp (-((n : ℝ) + 1))) * (-2 * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n : ℕ => 2 * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))) (fun n => ?_) ?_
      · have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))),
          abs_neg, abs_of_pos two_pos, abs_of_pos (Real.rpow_pos_of_pos hn_pos _)]
        have h1 : 1 - Real.exp (-((n : ℝ) + 1)) ≤ 1 := by linarith [Real.exp_pos (-((n : ℝ) + 1))]
        nlinarith [Real.rpow_pos_of_pos hn_pos (-(1 / 2 : ℝ))]
      · have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h_top_lim
        simpa using h.const_mul 2
    have h_lo : Tendsto (fun n : ℕ =>
        (1 - Real.exp (-(((n : ℝ) + 1)⁻¹))) * (-2 * (((n : ℝ) + 1)⁻¹) ^ (-(1 / 2 : ℝ)))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n : ℕ => 2 * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))) (fun n => ?_) ?_
      · have ha_pos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr (by positivity)
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))),
          abs_neg, abs_of_pos two_pos, abs_of_pos (Real.rpow_pos_of_pos ha_pos _)]
        have h1 : 1 - Real.exp (-(((n : ℝ) + 1)⁻¹)) ≤ ((n : ℝ) + 1)⁻¹ := by
          linarith [Real.add_one_le_exp (-(((n : ℝ) + 1)⁻¹))]
        calc (1 - Real.exp (-(((n : ℝ) + 1)⁻¹))) * (2 * (((n : ℝ) + 1)⁻¹) ^ (-(1 / 2 : ℝ)))
            ≤ ((n : ℝ) + 1)⁻¹ * (2 * (((n : ℝ) + 1)⁻¹) ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = 2 * (((n : ℝ) + 1)⁻¹ ^ (1 : ℝ) * (((n : ℝ) + 1)⁻¹) ^ (-(1 / 2 : ℝ))) := by
              rw [Real.rpow_one]; ring
          _ = 2 * (((n : ℝ) + 1)⁻¹) ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_add ha_pos]; norm_num
          _ = 2 * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
              rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
      · have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h_top_lim
        simpa using h.const_mul 2
    have h_gam : Tendsto (fun n : ℕ =>
        2 * ∫ L in (((n : ℝ) + 1)⁻¹ : ℝ)..((n : ℝ) + 1), Real.exp (-L) * L ^ (-(1 / 2 : ℝ)))
        atTop (𝓝 (2 * √π)) := by
      rw [← hGamma]
      exact ((tendsto_setIntegral_Icc_Ioi hGamma_int).congr fun n => by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
          ((inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)).trans (by linarith))]).const_mul 2
    exact (h_hi.sub h_lo).add h_gam
  have hlim_rhs' : Tendsto (fun n : ℕ =>
      ∫ L in (((n : ℝ) + 1)⁻¹ : ℝ)..((n : ℝ) + 1), (1 - Real.exp (-L)) * L ^ (-(3 / 2 : ℝ)))
      atTop (𝓝 (2 * √π)) := by
    simpa [hibp] using hlim_rhs
  exact tendsto_nhds_unique hlim_lhs hlim_rhs'

private lemma integral_one_sub_exp_neg_rpow_real {x : ℝ} (hx : 0 < x) :
    ∫ L in Ioi (0 : ℝ), (1 - Real.exp (-x * L)) * L ^ (-(3 / 2 : ℝ)) = 2 * √π * √x := by
  have hcov := MeasureTheory.integral_comp_mul_left_Ioi
    (fun t : ℝ => (1 - Real.exp (-t)) * t ^ (-(3 / 2 : ℝ))) (0 : ℝ) hx
  simp only [mul_zero, smul_eq_mul] at hcov
  rw [integral_one_sub_exp_neg_rpow_one] at hcov
  have hstep : ∫ L in Ioi (0 : ℝ), (1 - Real.exp (-x * L)) * L ^ (-(3 / 2 : ℝ)) =
      x ^ (3 / 2 : ℝ) * ∫ L in Ioi (0 : ℝ), (1 - Real.exp (-(x * L))) * (x * L) ^ (-(3 / 2 : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun L hL => ?_
    have hL0 : 0 < L := hL
    rw [Real.mul_rpow hx.le hL0.le, show -x * L = -(x * L) by ring]
    have hcancel : x ^ (3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hx]; norm_num
    calc (1 - Real.exp (-(x * L))) * L ^ (-(3 / 2 : ℝ))
        = (x ^ (3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))) * ((1 - Real.exp (-(x * L))) * L ^ (-(3 / 2 : ℝ))) := by
          rw [hcancel, one_mul]
      _ = _ := by ring
  rw [hstep, hcov]
  have hpow : x ^ (3 / 2 : ℝ) * x⁻¹ = √x := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx, Real.sqrt_eq_rpow]; norm_num
  calc x ^ (3 / 2 : ℝ) * (x⁻¹ * (2 * √π)) = 2 * √π * (x ^ (3 / 2 : ℝ) * x⁻¹) := by ring
    _ = 2 * √π * √x := by rw [hpow]

private lemma integral_one_sub_exp_neg_rpow_rhp {z : ℂ} (hz : 0 < z.re) :
    ∫ L in Ioi (0 : ℝ), (1 - Complex.exp (-z * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) =
      ((2 * √π : ℝ) : ℂ) * z ^ (1 / 2 : ℂ) := by
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  let F : ℂ → ℂ := fun w => ∫ L in Ioi (0 : ℝ), (1 - Complex.exp (-w * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)
  let G : ℂ → ℂ := fun w => ((2 * √π : ℝ) : ℂ) * w ^ (1 / 2 : ℂ)
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hF_diff : DifferentiableOn ℂ F U := by
    intro w₀ hw₀
    set r : ℝ := w₀.re / 2 with hr_def
    have hr : 0 < r := half_pos hw₀
    have hball_re : ∀ w ∈ Metric.ball w₀ r, r ≤ w.re := fun w hw => by
      have h1 := Complex.abs_re_le_norm (w - w₀)
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h2 := (abs_le.mp (h1.trans hw.le)).1
      simp only [Complex.sub_re] at h2; linarith
    let bound : ℝ → ℝ := fun L => Real.exp (-r * L) * L ^ (-(1 / 2 : ℝ))
    have hbound_int : IntegrableOn bound (Ioi (0 : ℝ)) := by
      have hG := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)
      have hcomp := (integrableOn_Ioi_comp_mul_left_iff
        (fun t : ℝ => Real.exp (-t) * t ^ (-(1 / 2 : ℝ))) 0 hr).mpr (by
          simpa only [mul_zero] using hG.congr_fun (fun t _ => by norm_num) measurableSet_Ioi)
      refine (hcomp.const_mul (r ^ (1 / 2 : ℝ))).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
      have hL0 : 0 < L := hL
      dsimp only [bound]
      rw [Real.mul_rpow hr.le hL0.le, show -(r * L) = -r * L by ring]
      have hcancel : r ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add hr]; norm_num
      calc r ^ (1 / 2 : ℝ) * (Real.exp (-r * L) * (r ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ))))
          = (r ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ))) * (Real.exp (-r * L) * L ^ (-(1 / 2 : ℝ))) := by ring
        _ = Real.exp (-r * L) * L ^ (-(1 / 2 : ℝ)) := by rw [hcancel, one_mul]
    have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun (w : ℂ) (L : ℝ) => (1 - Complex.exp (-w * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ))
      (F' := fun (w : ℂ) (L : ℝ) => Complex.exp (-w * (L : ℂ)) * ((L ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
      (Metric.ball_mem_nhds w₀ hr)
      (Eventually.of_forall fun w => by
        exact ((continuousOn_const.sub (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn).mul
          (Complex.continuous_ofReal.comp_continuousOn
            (ContinuousOn.rpow_const continuousOn_id (fun L hL => Or.inl (Set.mem_Ioi.mp hL).ne')))).aestronglyMeasurable
          measurableSet_Ioi)
      (by
        refine (integrableOn_min_rpow_neg_three_halves_nonneg (norm_nonneg w₀)).mono' ?_ ?_
        · exact ((continuousOn_const.sub (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn).mul
            (Complex.continuous_ofReal.comp_continuousOn
              (ContinuousOn.rpow_const continuousOn_id (fun L hL => Or.inl (Set.mem_Ioi.mp hL).ne')))).aestronglyMeasurable
            measurableSet_Ioi
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
          have hL0 : 0 < L := hL
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos hL0 _).le]
          have hre_nn : 0 ≤ (w₀ * (L : ℂ)).re := by
            rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
            exact mul_nonneg hw₀.le hL0.le
          have hbd := norm_one_sub_exp_neg_le_min hre_nn
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hL0.le] at hbd
          rw [show -w₀ * (L : ℂ) = -(w₀ * (L : ℂ)) by ring]
          exact mul_le_mul_of_nonneg_right hbd (by positivity))
      (by
        exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn.mul
          (Complex.continuous_ofReal.comp_continuousOn
            (ContinuousOn.rpow_const continuousOn_id (fun L hL => Or.inl (Set.mem_Ioi.mp hL).ne')))).aestronglyMeasurable
          measurableSet_Ioi)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL w hw
        have hL0 : 0 < L := hL
        rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos hL0 _).le]
        have hre : (-w * (L : ℂ)).re = -w.re * L := by simp
        rw [hre]
        dsimp [bound]
        gcongr
        nlinarith [hball_re w hw, hL0])
      hbound_int
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL w _
        have hL0 : 0 < L := hL
        have h1 : HasDerivAt (fun u : ℂ => -u * (L : ℂ)) (-(L : ℂ)) w := by
          simpa using (hasDerivAt_id w).neg.mul_const (L : ℂ)
        have h2 : HasDerivAt (fun u : ℂ => (1 - Complex.exp (-u * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ))
            ((0 - Complex.exp (-w * (L : ℂ)) * -(L : ℂ)) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) w :=
          ((hasDerivAt_const w (1 : ℂ)).sub ((Complex.hasDerivAt_exp _).comp w h1)).mul_const
            ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)
        refine h2.congr_deriv ?_
        have hLpow : (L : ℂ) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) = ((L ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul]
          congr 1
          calc L * L ^ (-(3 / 2 : ℝ)) = L ^ (1 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_one]
            _ = L ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hL0]; norm_num
        calc (0 - Complex.exp (-w * (L : ℂ)) * -(L : ℂ)) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)
            = Complex.exp (-w * (L : ℂ)) * ((L : ℂ) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by ring
          _ = Complex.exp (-w * (L : ℂ)) * ((L ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by rw [hLpow])
    exact hderiv.2.differentiableAt.differentiableWithinAt
  have hG_diff : DifferentiableOn ℂ G U := fun w hw =>
    ((differentiableAt_id.cpow_const (Or.inl hw)).const_mul _).differentiableWithinAt
  have hF_an : AnalyticOnNhd ℂ F U := hF_diff.analyticOnNhd hU_open
  have hG_an : AnalyticOnNhd ℂ G U := hG_diff.analyticOnNhd hU_open
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), F w = G w := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [Metric.mem_nhdsWithin_iff] at hs
    obtain ⟨ε, hε, hsub⟩ := hs
    let x : ℝ := 1 + min (ε / 2) (1 / 2)
    have hx_pos : 0 < x := by positivity
    have hx_ne : (x : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp [x] at this
      have : 0 < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
      linarith
    have hx_mem : (x : ℂ) ∈ s := by
      apply hsub
      refine ⟨?_, hx_ne⟩
      rw [Metric.mem_ball, dist_eq_norm, show (x : ℂ) - 1 = ((min (ε / 2) (1 / 2) : ℝ) : ℂ) by
        simp [x], Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith [min_le_left (ε / 2) (1 / 2)]
    refine ⟨(x : ℂ), hx_mem, ?_⟩
    dsimp [F, G]
    have hreal : ∫ L in Ioi (0 : ℝ), (1 - Complex.exp (-(x : ℂ) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) =
        ((∫ L in Ioi (0 : ℝ), (1 - Real.exp (-x * L)) * L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
      simp [Complex.ofReal_exp]
    rw [hreal, integral_one_sub_exp_neg_rpow_real hx_pos]
    have hx_cpow : (x : ℂ) ^ (1 / 2 : ℂ) = (√x : ℂ) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx_pos.ne'), ← Complex.ofReal_log hx_pos.le,
        show ((Real.log x : ℝ) : ℂ) * (1 / 2 : ℂ) = ((Real.log x / 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp, exp_log_div_two hx_pos]
    rw [hx_cpow]; push_cast; ring
  exact hF_an.eqOn_of_preconnected_of_frequently_eq hG_an hU_conn (by simp [U] : (1 : ℂ) ∈ U) hfreq hz

/-- **Integral representation of `(i y)^{1/2}`** (`uct:ce-preedge` (2) proof):
for every `y : ℝ`,
`(i y)^{1/2} = (2√π)⁻¹ ∫₀^∞ (1 - e^{-i y L}) L^{-3/2} dL`. -/
theorem cpow_half_I_mul_eq_integral (y : ℝ) :
    ((y : ℂ) * Complex.I) ^ (1 / 2 : ℂ) =
      ((1 / (2 * √π) : ℝ) : ℂ) *
        ∫ L in Ioi (0 : ℝ), (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) *
          ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
  suffices h : ∫ L in Ioi (0 : ℝ), (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) *
      ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) = ((2 * √π : ℝ) : ℂ) * ((y : ℂ) * Complex.I) ^ (1 / 2 : ℂ) by
    rw [h, ← mul_assoc, ← Complex.ofReal_mul,
      show 1 / (2 * √π) * (2 * √π) = 1 by field_simp, Complex.ofReal_one, one_mul]
  let ε : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hε_pos : ∀ n : ℕ, 0 < ε n := fun n => inv_pos.mpr (by positivity)
  have hε_le1 : ∀ n : ℕ, ε n ≤ 1 := fun n => inv_le_one_of_one_le₀ (by linarith)
  have hε_lim : Tendsto ε atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hseq : ∀ n : ℕ,
      ∫ L in Ioi (0 : ℝ), (1 - Complex.exp (-((ε n : ℂ) + (y : ℂ) * Complex.I) * (L : ℂ))) *
          ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) =
        ((2 * √π : ℝ) : ℂ) * ((ε n : ℂ) + (y : ℂ) * Complex.I) ^ (1 / 2 : ℂ) := fun n =>
    integral_one_sub_exp_neg_rpow_rhp (by simp [hε_pos n])
  have hlim_lhs : Tendsto (fun n : ℕ =>
      ∫ L in Ioi (0 : ℝ), (1 - Complex.exp (-((ε n : ℂ) + (y : ℂ) * Complex.I) * (L : ℂ))) *
        ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ))
      atTop (𝓝 (∫ L in Ioi (0 : ℝ), (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) *
        ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun L => min ((1 + |y|) * L) 2 * L ^ (-(3 / 2 : ℝ))) ?_
      (integrableOn_min_rpow_neg_three_halves_nonneg (by positivity)) ?_ ?_
    · intro n
      exact ((continuousOn_const.sub (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn).mul
        (Complex.continuous_ofReal.comp_continuousOn
          (ContinuousOn.rpow_const continuousOn_id (fun L hL => Or.inl (Set.mem_Ioi.mp hL).ne')))).aestronglyMeasurable
        measurableSet_Ioi
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
      have hL0 : 0 < L := hL
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos hL0 _).le]
      have hre_nn : 0 ≤ (((ε n : ℂ) + (y : ℂ) * Complex.I) * (L : ℂ)).re := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
        exact mul_nonneg (hε_pos n).le hL0.le
      have hbd := norm_one_sub_exp_neg_le_min hre_nn
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hL0.le] at hbd
      have hwnorm : ‖(ε n : ℂ) + (y : ℂ) * Complex.I‖ ≤ 1 + |y| := by
        calc ‖(ε n : ℂ) + (y : ℂ) * Complex.I‖ ≤ ‖(ε n : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = ε n + |y| := by rw [Complex.norm_real, Real.norm_of_nonneg (hε_pos n).le, norm_mul,
              Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ 1 + |y| := by linarith [hε_le1 n]
      rw [show -((ε n : ℂ) + (y : ℂ) * Complex.I) * (L : ℂ) = -(((ε n : ℂ) + (y : ℂ) * Complex.I) * (L : ℂ)) by ring]
      exact mul_le_mul_of_nonneg_right (hbd.trans (min_le_min_right 2 (mul_le_mul_of_nonneg_right hwnorm hL0.le)))
        (by positivity)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L _
      have h1 : Tendsto (fun n : ℕ => (ε n : ℂ) + (y : ℂ) * Complex.I) atTop (𝓝 ((y : ℂ) * Complex.I)) := by
        simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hε_lim).add tendsto_const_nhds
      exact (tendsto_const_nhds.sub (Complex.continuous_exp.continuousAt.tendsto.comp
        (h1.neg.mul tendsto_const_nhds))).mul tendsto_const_nhds
  have hlim_rhs : Tendsto (fun n : ℕ =>
      ((2 * √π : ℝ) : ℂ) * ((ε n : ℂ) + (y : ℂ) * Complex.I) ^ (1 / 2 : ℂ))
      atTop (𝓝 (((2 * √π : ℝ) : ℂ) * ((y : ℂ) * Complex.I) ^ (1 / 2 : ℂ))) := by
    refine Tendsto.const_mul _ ?_
    by_cases hy : y = 0
    · subst hy
      simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0)]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnorm : ∀ n : ℕ, ‖((ε n : ℂ)) ^ (1 / 2 : ℂ)‖ = √(ε n) := fun n => by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (hε_pos n).ne'), ← Complex.ofReal_log (hε_pos n).le,
          show ((Real.log (ε n) : ℝ) : ℂ) * (1 / 2 : ℂ) = ((Real.log (ε n) / 2 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, exp_log_div_two (hε_pos n), Complex.norm_real,
          Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      simp_rw [hnorm]
      have hsqrt : Tendsto (fun x : ℝ => √x) (𝓝 0) (𝓝 0) := by
        simpa using (Real.continuous_sqrt.continuousAt (x := 0)).tendsto
      exact hsqrt.comp hε_lim
    · have hslit : (y : ℂ) * Complex.I ∈ Complex.slitPlane := Or.inr (by simp [hy])
      have h1 : Tendsto (fun n : ℕ => (ε n : ℂ) + (y : ℂ) * Complex.I) atTop (𝓝 ((y : ℂ) * Complex.I)) := by
        simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hε_lim).add tendsto_const_nhds
      exact (differentiableAt_id.cpow_const hslit).continuousAt.tendsto.comp h1
  simp_rw [hseq] at hlim_lhs
  exact tendsto_nhds_unique hlim_lhs hlim_rhs

private lemma exp_sub_one_le_exp_one_mul {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1) :
    Real.exp L - 1 ≤ Real.exp 1 * L := by
  rcases hL0.eq_or_lt with rfl | hL_pos
  · simp
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope Real.exp Real.exp hL_pos
      Real.continuous_exp.continuousOn (fun x _ => Real.hasDerivAt_exp x)
    rw [Real.exp_zero, sub_zero, eq_div_iff hL_pos.ne'] at hslope
    have hc1 : Real.exp c ≤ Real.exp 1 := Real.exp_le_exp.mpr (le_trans hc.2.le hL1)
    nlinarith

/-- **Lemma `uct:ce-preedge` (2), `(iy)^{1/2}` origin inversion `(uct:sqrt-iy-inv)`**
(`CFT/sign_uncertainty/paper/constant_terms_upper.tex`).

For every `Δ > 0`:
`(2π)⁻¹ ∫_ℝ 4^{-iy} Γ(iy) (iy)^{1/2} Δ^{-iy} dy = (2√π)⁻¹ ∫₀^∞ (e^{-4Δ} - e^{-4 e^L Δ}) L^{-3/2} dL ≥ 0`,
and both integrals converge absolutely. -/
theorem uct_sqrt_iy_inv {Δ : ℝ} (hΔ : 0 < Δ) :
    Integrable (fun y : ℝ => (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) *
        Complex.Gamma ((y : ℂ) * Complex.I) * ((y : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
        (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))) ∧
    IntegrableOn (fun L : ℝ => (Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ))) *
        L ^ (-(3 / 2 : ℝ))) (Ioi (0 : ℝ)) ∧
    ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ y : ℝ, (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) *
          Complex.Gamma ((y : ℂ) * Complex.I) * ((y : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
          (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) =
      (((1 / (2 * √π)) * ∫ L in Ioi (0 : ℝ),
        (Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ))) * L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) ∧
    0 ≤ (1 / (2 * √π)) * ∫ L in Ioi (0 : ℝ),
      (Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ))) * L ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨B, hB⟩ := Gamma_decay_strip (a := 1) (b := 1) one_pos le_rfl
  have hnorm_4 : ∀ y : ℝ, ‖(4 : ℂ) ^ (-((y : ℂ) * Complex.I))‖ = 1 := fun y => by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]; simp
  have hnorm_Δ : ∀ y : ℝ, ‖(Δ : ℂ) ^ (-((y : ℂ) * Complex.I))‖ = 1 := fun y => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hΔ]; simp
  have hnorm_G : ∀ y : ℝ, y ≠ 0 →
      ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ≤ |B| * (1 + |y|) ^ (-(2 : ℝ)) / |y| := fun y hy => by
    have hz0 : (y : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hy) Complex.I_ne_zero
    have hG1 : Complex.Gamma (1 + (y : ℂ) * Complex.I) = ((y : ℂ) * Complex.I) * Complex.Gamma ((y : ℂ) * Complex.I) := by
      rw [add_comm, Complex.Gamma_add_one _ hz0]
    have hbd := hB (1 + (y : ℂ) * Complex.I) (by simp) (by simp)
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at hbd
    have hn : ‖((y : ℂ) * Complex.I)‖ = |y| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [hG1, norm_mul, hn] at hbd
    rw [le_div_iff₀ (abs_pos.mpr hy)]
    calc ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * |y|
        = |y| * ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ := mul_comm _ _
      _ ≤ B * (1 + |y|) ^ (-(2 : ℝ)) := hbd
      _ ≤ |B| * (1 + |y|) ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
  have hmaj_y : Integrable fun y : ℝ => (1 + |y|) ^ (-(2 : ℝ)) * |y| ^ (-(1 / 2 : ℝ)) := by
    have h1 : IntegrableOn (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) (Icc (-1 : ℝ) 1) := by
      have hpos : IntegrableOn (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) :=
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).1
      have hpos_oo : IntegrableOn (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (Ioo (0 : ℝ) 1) :=
        hpos.mono_set Ioo_subset_Ioc_self
      have hneg : IntegrableOn (fun y : ℝ => (-y) ^ (-(1 / 2 : ℝ))) (Ioo (-1 : ℝ) 0) := by
        have hcomp := hpos_oo.comp_neg
        convert hcomp using 1
        ext x; simp only [mem_Ioo, Set.mem_neg]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
      have hIoc : IntegrableOn (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) :=
        hpos.congr_fun (fun y hy => by rw [abs_of_pos hy.1]) measurableSet_Ioc
      have hIoo : IntegrableOn (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) (Ioo (-1 : ℝ) 0) :=
        hneg.congr_fun (fun y hy => by rw [abs_of_neg hy.2]) measurableSet_Ioo
      have hU : Icc (-1 : ℝ) 1 =ᵐ[volume] Ioo (-1 : ℝ) 0 ∪ Ioc (0 : ℝ) 1 := by
        have hsub : Ioo (-1 : ℝ) 0 ∪ Ioc (0 : ℝ) 1 = Ioc (-1 : ℝ) 1 \ {0} := by
          ext y; simp only [mem_union, mem_Ioo, mem_Ioc, Set.mem_sdiff, mem_singleton_iff]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact ⟨⟨h1, by linarith⟩, h2.ne⟩
            · exact ⟨⟨by linarith, h2⟩, h1.ne'⟩
          · rintro ⟨⟨h1, h2⟩, hne⟩
            rcases lt_or_gt_of_ne hne with h | h
            · exact Or.inl ⟨h1, h⟩
            · exact Or.inr ⟨h, h2⟩
        rw [hsub]
        have h1 := Ioc_ae_eq_Icc (a := (-1 : ℝ)) (b := 1) (μ := volume)
        have h2 : (Ioc (-1 : ℝ) 1 \ {0} : Set ℝ) =ᵐ[volume] Ioc (-1 : ℝ) 1 :=
          sdiff_ae_eq_self.mpr (measure_mono_null Set.inter_subset_right (measure_singleton 0))
        exact h1.symm.trans h2.symm
      exact (hIoo.union hIoc).congr_set_ae hU
    have h2 : IntegrableOn (fun y : ℝ => (1 + y ^ 2)⁻¹) (Icc (-1 : ℝ) 1)ᶜ :=
      integrable_inv_one_add_sq.integrableOn
    have hmeas : AEStronglyMeasurable (fun y : ℝ => (1 + |y|) ^ (-(2 : ℝ)) * |y| ^ (-(1 / 2 : ℝ))) volume := by
      have : Measurable fun y : ℝ => (1 + |y|) ^ (-(2 : ℝ)) * |y| ^ (-(1 / 2 : ℝ)) := by fun_prop
      exact this.aestronglyMeasurable
    rw [← integrableOn_univ, show (univ : Set ℝ) = Icc (-1 : ℝ) 1 ∪ (Icc (-1 : ℝ) 1)ᶜ by simp, integrableOn_union]
    refine ⟨h1.mono' hmeas.restrict ?_, (h2.const_mul 2).mono' hmeas.restrict ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with y _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_left (by positivity)
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg y]) (by norm_num))
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with y hy
      have hy1 : 1 < |y| := by
        simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hy
        rcases hy with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hpow1 : |y| ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by norm_num)
      calc (1 + |y|) ^ (-(2 : ℝ)) * |y| ^ (-(1 / 2 : ℝ))
          ≤ (1 + |y|) ^ (-(2 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hpow1 (by positivity)
        _ ≤ 2 * (1 + y ^ 2)⁻¹ := by rw [mul_one]; exact one_add_abs_rpow_neg_two_le y
  -- Integrability of LHS
  have hInt_lhs : Integrable (fun y : ℝ => (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) *
      Complex.Gamma ((y : ℂ) * Complex.I) * ((y : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
      (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))) := by
    have hmeas : AEStronglyMeasurable (fun y : ℝ => (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) *
        Complex.Gamma ((y : ℂ) * Complex.I) * ((y : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
        (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))) volume := by
      have hcont : ContinuousOn (fun y : ℝ => (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) *
          Complex.Gamma ((y : ℂ) * Complex.I) * ((y : ℂ) * Complex.I) ^ (1 / 2 : ℂ) *
          (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))) {y : ℝ | y ≠ 0} := by
        intro y hy
        have h1 : ContinuousAt (fun t : ℝ => (4 : ℂ) ^ (-((t : ℂ) * Complex.I))) y :=
          ContinuousAt.const_cpow (by fun_prop) (Or.inl (by norm_num))
        have h2 : ContinuousAt (fun t : ℝ => Complex.Gamma ((t : ℂ) * Complex.I)) y :=
          (Complex.differentiableAt_Gamma _ (fun m => by
            intro h; have := congrArg Complex.im h; simp at this; exact hy this)).continuousAt.comp (by fun_prop)
        have h3 : ContinuousAt (fun t : ℝ => ((t : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) y :=
          (differentiableAt_id.cpow_const (Or.inr (by simpa using hy))).continuousAt.comp (by fun_prop)
        have h4 : ContinuousAt (fun t : ℝ => (Δ : ℂ) ^ (-((t : ℂ) * Complex.I))) y :=
          ContinuousAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hΔ.ne'))
        exact (((h1.mul h2).mul h3).mul h4).continuousWithinAt
      have hrestrict : volume.restrict ({y : ℝ | y ≠ 0} : Set ℝ) = volume :=
        Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr (measure_singleton 0))
      have h := hcont.aestronglyMeasurable (μ := volume) isOpen_ne.measurableSet
      rwa [hrestrict] at h
    refine (hmaj_y.const_mul |B|).mono' hmeas ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with y hy
    have hy0 : y ≠ 0 := hy
    rw [norm_mul, norm_mul, norm_mul, hnorm_4 y, hnorm_Δ y, one_mul, mul_one]
    have hsqrt : ‖((y : ℂ) * Complex.I) ^ (1 / 2 : ℂ)‖ = |y| ^ (1 / 2 : ℝ) := by
      have hz0 : (y : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hy0) Complex.I_ne_zero
      rw [Complex.cpow_def_of_ne_zero hz0, Complex.norm_exp,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        ← Real.rpow_def_of_pos (abs_pos.mpr hy0)]
    rw [hsqrt]
    calc ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * |y| ^ (1 / 2 : ℝ)
        ≤ (|B| * (1 + |y|) ^ (-(2 : ℝ)) / |y|) * |y| ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (hnorm_G y hy0) (by positivity)
      _ = |B| * ((1 + |y|) ^ (-(2 : ℝ)) * (|y| ^ (-(1 : ℝ)) * |y| ^ (1 / 2 : ℝ))) := by
          rw [Real.rpow_neg_one]; ring
      _ = |B| * ((1 + |y|) ^ (-(2 : ℝ)) * |y| ^ (-(1 / 2 : ℝ))) := by
          rw [← Real.rpow_add (abs_pos.mpr hy0)]; norm_num
  -- Integrability and nonnegativity of RHS
  have hInt_rhs : IntegrableOn (fun L : ℝ =>
      (Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ))) * L ^ (-(3 / 2 : ℝ))) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun L : ℝ => 4 * Δ * Real.exp 1 * L ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).1.const_mul _
    have h2 : IntegrableOn (fun L : ℝ => L ^ (-(3 / 2 : ℝ))) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) zero_lt_one
    have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
    rw [hsplit, integrableOn_union]
    refine ⟨h1.mono' ?_ ?_, h2.mono' ?_ ?_⟩
    · exact ((continuousOn_const.sub (by fun_prop)).mul
        (ContinuousOn.rpow_const continuousOn_id (fun L (hL : L ∈ Ioc 0 1) => Or.inl hL.1.ne'))).aestronglyMeasurable
        measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
      have hL0 : 0 < L := hL.1
      have hL1 : L ≤ 1 := hL.2
      have hdiff_nn : 0 ≤ Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ)) :=
        sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [Real.one_le_exp hL0.le]))
      have hdiff_le : Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ)) ≤ 4 * Δ * Real.exp 1 * L := by
        have hfac : Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ)) =
            Real.exp (-(4 * Δ)) * (1 - Real.exp (-(4 * Δ * (Real.exp L - 1)))) := by
          rw [mul_sub, mul_one, ← Real.exp_add]; congr 2; ring
        rw [hfac]
        have he1 : Real.exp (-(4 * Δ)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have he2 : 1 - Real.exp (-(4 * Δ * (Real.exp L - 1))) ≤ 4 * Δ * (Real.exp L - 1) := by
          linarith [Real.add_one_le_exp (-(4 * Δ * (Real.exp L - 1)))]
        have he3 : Real.exp L - 1 ≤ Real.exp 1 * L := exp_sub_one_le_exp_one_mul hL0.le hL1
        calc Real.exp (-(4 * Δ)) * (1 - Real.exp (-(4 * Δ * (Real.exp L - 1))))
            ≤ 1 * (4 * Δ * (Real.exp L - 1)) :=
              mul_le_mul he1 he2 (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [Real.one_le_exp hL0.le]))) zero_le_one
          _ ≤ 4 * Δ * (Real.exp 1 * L) := by rw [one_mul]; gcongr
          _ = 4 * Δ * Real.exp 1 * L := by ring
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hdiff_nn, abs_of_pos (Real.rpow_pos_of_pos hL0 _)]
      calc (Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ))) * L ^ (-(3 / 2 : ℝ))
          ≤ (4 * Δ * Real.exp 1 * L) * L ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hdiff_le (by positivity)
        _ = 4 * Δ * Real.exp 1 * (L ^ (1 : ℝ) * L ^ (-(3 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
        _ = 4 * Δ * Real.exp 1 * L ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hL0]; norm_num
    · exact ((continuousOn_const.sub (by fun_prop)).mul
        (ContinuousOn.rpow_const continuousOn_id (fun L hL => Or.inl (lt_trans zero_lt_one hL).ne'))).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
      have hL0 : 0 < L := lt_trans zero_lt_one hL
      have hdiff_nn : 0 ≤ Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ)) :=
        sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [Real.one_le_exp hL0.le]))
      have hdiff_le : Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ)) ≤ 1 := by
        linarith [Real.exp_le_one_iff.mpr (by linarith : -(4 * Δ) ≤ 0), Real.exp_pos (-(4 * Real.exp L * Δ))]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hdiff_nn, abs_of_pos (Real.rpow_pos_of_pos hL0 _)]
      exact mul_le_of_le_one_left (by positivity) hdiff_le
  have hnn_rhs : 0 ≤ (1 / (2 * √π)) * ∫ L in Ioi (0 : ℝ),
      (Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ))) * L ^ (-(3 / 2 : ℝ)) := by
    refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun L hL => ?_)
    have hL0 : 0 < L := hL
    exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [Real.one_le_exp hL0.le]))) (by positivity)
  refine ⟨hInt_lhs, hInt_rhs, ?_, hnn_rhs⟩
  -- Fubini on ℝ × Icc δ_n R_n, then DCT as n → ∞
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let R : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hδR : ∀ n : ℕ, 0 < δ n ∧ δ n ≤ R n := fun n =>
    ⟨inv_pos.mpr (by positivity),
      (inv_le_one_of_one_le₀ (by dsimp [R]; linarith : (1 : ℝ) ≤ R n)).trans (by dsimp [R]; linarith)⟩
  let K : ℝ → ℝ → ℂ := fun y L =>
    (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
      (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) *
      ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)
  have hfub : ∀ n : ℕ,
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ,
        (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
          (((1 / (2 * √π) : ℝ) : ℂ) * ∫ L in Icc (δ n) (R n),
            (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) *
          (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) =
      (((1 / (2 * √π)) * ∫ L in Icc (δ n) (R n),
        (Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ))) * L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
    intro n
    have hδ0 : 0 < δ n := (hδR n).1
    have hK_int : Integrable (Function.uncurry K) (volume.prod (volume.restrict (Icc (δ n) (R n)))) := by
      have hmeas_prod : AEStronglyMeasurable (Function.uncurry K) (volume.prod (volume.restrict (Icc (δ n) (R n)))) := by
        let S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≠ 0 ∧ 0 < p.2}
        have hS_open : IsOpen S := (isOpen_ne.preimage continuous_fst).inter (isOpen_lt continuous_const continuous_snd)
        have hS_ae : S ∈ ae (volume.prod (volume.restrict (Icc (δ n) (R n)))) := by
          have h1 : ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Icc (δ n) (R n)))), p.1 ≠ 0 :=
            MeasureTheory.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (compl_mem_ae_iff.mpr (measure_singleton 0))
          have h2 : ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Icc (δ n) (R n)))), 0 < p.2 :=
            (MeasureTheory.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (ae_restrict_mem measurableSet_Icc)).mono
              fun p hp => lt_of_lt_of_le hδ0 hp.1
          exact h1.and h2
        have hcont_S : ContinuousOn (Function.uncurry K) S := by
          intro p hp
          have h1 : ContinuousAt (fun q : ℝ × ℝ => (4 : ℂ) ^ (-((q.1 : ℂ) * Complex.I))) p :=
            ContinuousAt.const_cpow (by fun_prop) (Or.inl (by norm_num))
          have h2 : ContinuousAt (fun q : ℝ × ℝ => Complex.Gamma ((q.1 : ℂ) * Complex.I)) p :=
            (Complex.differentiableAt_Gamma _ (fun m => fun h => by
              have := congrArg Complex.im h; simp at this; exact hp.1 this)).continuousAt.comp (by fun_prop)
          have h3 : ContinuousAt (fun q : ℝ × ℝ => 1 - Complex.exp (-((q.1 : ℂ) * Complex.I) * (q.2 : ℂ))) p := by
            fun_prop
          have h4 : ContinuousAt (fun q : ℝ × ℝ => (Δ : ℂ) ^ (-((q.1 : ℂ) * Complex.I))) p :=
            ContinuousAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hΔ.ne'))
          have h5 : ContinuousAt (fun q : ℝ × ℝ => ((q.2 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) p :=
            Complex.continuous_ofReal.continuousAt.comp
              ((ContinuousAt.rpow_const continuousAt_snd (Or.inl hp.2.ne')))
          exact ((((h1.mul h2).mul h3).mul h4).mul h5).continuousWithinAt
        have hrestrict : (volume.prod (volume.restrict (Icc (δ n) (R n)))).restrict S =
            volume.prod (volume.restrict (Icc (δ n) (R n))) :=
          Measure.restrict_eq_self_of_ae_mem hS_ae
        rw [← hrestrict]
        exact hcont_S.aestronglyMeasurable hS_open.measurableSet
      have hdom_y : Integrable (fun y : ℝ => |B| * R n * (1 + |y|) ^ (-(2 : ℝ))) volume := by
        have hmeas_y : AEStronglyMeasurable (fun y : ℝ => |B| * R n * (1 + |y|) ^ (-(2 : ℝ))) volume :=
          (continuous_const.mul ((continuous_const.add continuous_abs).rpow_const
            (fun y => Or.inl (by dsimp; linarith [abs_nonneg y])))).aestronglyMeasurable
        refine (integrable_inv_one_add_sq.const_mul (2 * (|B| * R n))).mono' hmeas_y (Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc |B| * R n * (1 + |y|) ^ (-(2 : ℝ))
            ≤ |B| * R n * (2 * (1 + y ^ 2)⁻¹) := mul_le_mul_of_nonneg_left (one_add_abs_rpow_neg_two_le y) (by positivity)
          _ = _ := by ring
      have hdom_L : Integrable (fun _ : ℝ => (δ n) ^ (-(3 / 2 : ℝ))) (volume.restrict (Icc (δ n) (R n))) :=
        integrableOn_const (by simp)
      refine (hdom_y.mul_prod hdom_L).mono' hmeas_prod ?_
      have hae_y : ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Icc (δ n) (R n)))), p.1 ≠ 0 ∧ p.2 ∈ Icc (δ n) (R n) := by
        have h1 : ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Icc (δ n) (R n)))), p.1 ≠ 0 :=
          MeasureTheory.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (compl_mem_ae_iff.mpr (measure_singleton 0))
        have h2 : ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Icc (δ n) (R n)))), p.2 ∈ Icc (δ n) (R n) :=
          MeasureTheory.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (ae_restrict_mem measurableSet_Icc)
        exact h1.and h2
      filter_upwards [hae_y] with ⟨y, L⟩ ⟨hy0, hL⟩
      have hL0 : 0 < L := lt_of_lt_of_le hδ0 hL.1
      dsimp only [Function.uncurry, K]
      rw [norm_mul, norm_mul, norm_mul, norm_mul, hnorm_4 y, hnorm_Δ y, one_mul, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos hL0 _).le]
      have h1e : ‖1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))‖ ≤ |y| * R n := by
        have hbd := norm_one_sub_exp_neg_le_min (w := ((y : ℂ) * Complex.I) * (L : ℂ)) (by simp)
        rw [show -((y : ℂ) * Complex.I) * (L : ℂ) = -(((y : ℂ) * Complex.I) * (L : ℂ)) by ring]
        refine (hbd.trans (min_le_left _ _)).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_of_nonneg hL0.le]
        exact mul_le_mul_of_nonneg_left hL.2 (abs_nonneg y)
      have hLpow : L ^ (-(3 / 2 : ℝ)) ≤ (δ n) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hδ0 hL.1 (by norm_num)
      calc ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * ‖1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))‖ * L ^ (-(3 / 2 : ℝ))
          ≤ (|B| * (1 + |y|) ^ (-(2 : ℝ)) / |y|) * (|y| * R n) * (δ n) ^ (-(3 / 2 : ℝ)) := by
            gcongr; exact hnorm_G y hy0
        _ = |B| * R n * (1 + |y|) ^ (-(2 : ℝ)) * (δ n) ^ (-(3 / 2 : ℝ)) := by
            field_simp [(abs_pos.mpr hy0).ne']
    have hswap := integral_integral_swap hK_int
    have hlhs_eq : ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ,
        (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
          (((1 / (2 * √π) : ℝ) : ℂ) * ∫ L in Icc (δ n) (R n),
            (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) *
          (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) =
        ((1 / (2 * √π) : ℝ) : ℂ) * (((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, ∫ L in Icc (δ n) (R n), K y L) := by
      have h1 : ∀ y : ℝ,
          (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
            (((1 / (2 * √π) : ℝ) : ℂ) * ∫ L in Icc (δ n) (R n),
              (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) *
            (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) =
          ((1 / (2 * √π) : ℝ) : ℂ) * ∫ L in Icc (δ n) (R n), K y L := fun y => by
        rw [show (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
            (((1 / (2 * √π) : ℝ) : ℂ) * ∫ L in Icc (δ n) (R n),
              (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) *
            (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) =
          ((1 / (2 * √π) : ℝ) : ℂ) * (((4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
            (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))) *
            ∫ L in Icc (δ n) (R n),
              (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) by ring]
        congr 1
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Icc fun L _ => ?_
        dsimp [K]; ring
      simp_rw [h1, integral_const_mul]; ring
    rw [hlhs_eq, hswap, ← integral_const_mul]
    have hinner : ∫ L in Icc (δ n) (R n), ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, K y L =
        ((∫ L in Icc (δ n) (R n), (Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ))) * L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Icc fun L hL => ?_
      have hL0 : 0 ≤ L := le_trans hδ0.le hL.1
      have hpe3 := (pe3_mellin_identity hΔ hL0).1
      have hpull : ∫ y : ℝ, K y L =
          (∫ y : ℝ, (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
            (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))) *
          ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
        rw [← integral_mul_const]
      rw [hpull, ← mul_assoc, hpe3, ← Complex.ofReal_mul]
    rw [hinner]; push_cast; ring
  -- Take n → ∞ on both sides
  have hlim_rhs : Tendsto (fun n : ℕ =>
      (((1 / (2 * √π)) * ∫ L in Icc (δ n) (R n),
        (Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ))) * L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ))
      atTop (𝓝 (((1 / (2 * √π)) * ∫ L in Ioi (0 : ℝ),
        (Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ))) * L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_setIntegral_Icc_Ioi hInt_rhs).const_mul _)
  have hlim_lhs : Tendsto (fun n : ℕ =>
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ,
        (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
          (((1 / (2 * √π) : ℝ) : ℂ) * ∫ L in Icc (δ n) (R n),
            (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) *
          (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)))
      atTop (𝓝 (((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ,
        (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
          ((y : ℂ) * Complex.I) ^ (1 / 2 : ℂ) * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)))) := by
    refine Tendsto.const_mul _ ?_
    refine tendsto_integral_of_dominated_convergence
      (fun y => |B| * (2 * √2 / √π) * ((1 + |y|) ^ (-(2 : ℝ)) * |y| ^ (-(1 / 2 : ℝ)))) ?_
      (hmaj_y.const_mul (|B| * (2 * √2 / √π))) ?_ ?_
    · intro n
      have hcont : ContinuousOn (fun y : ℝ =>
          (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
            (((1 / (2 * √π) : ℝ) : ℂ) * ∫ L in Icc (δ n) (R n),
              (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) *
            (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))) {y : ℝ | y ≠ 0} := by
        intro y hy
        have h1 : ContinuousAt (fun t : ℝ => (4 : ℂ) ^ (-((t : ℂ) * Complex.I))) y :=
          ContinuousAt.const_cpow (by fun_prop) (Or.inl (by norm_num))
        have h2 : ContinuousAt (fun t : ℝ => Complex.Gamma ((t : ℂ) * Complex.I)) y :=
          (Complex.differentiableAt_Gamma _ (fun m => fun h => by
            have := congrArg Complex.im h; simp at this; exact hy this)).continuousAt.comp (by fun_prop)
        have h3 : ContinuousAt (fun t : ℝ => ∫ L in Icc (δ n) (R n),
            (1 - Complex.exp (-((t : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) y := by
          refine continuousAt_of_dominated (bound := fun _ => 2 * (δ n) ^ (-(3 / 2 : ℝ))) ?_ ?_
            (integrableOn_const (by simp)) ?_
          · exact Eventually.of_forall fun t =>
              ((continuousOn_const.sub (by fun_prop)).mul
                (Complex.continuous_ofReal.comp_continuousOn
                  (ContinuousOn.rpow_const continuousOn_id (fun L (hL : L ∈ Icc (δ n) (R n)) =>
                    Or.inl (lt_of_lt_of_le (hδR n).1 hL.1).ne')))).aestronglyMeasurable
                measurableSet_Icc
          · exact Eventually.of_forall fun t => by
              filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL
              have hL0 : 0 < L := lt_of_lt_of_le (hδR n).1 hL.1
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos hL0 _).le]
              have hbd := norm_one_sub_exp_neg_le_min (w := ((t : ℂ) * Complex.I) * (L : ℂ)) (by simp)
              rw [show -((t : ℂ) * Complex.I) * (L : ℂ) = -(((t : ℂ) * Complex.I) * (L : ℂ)) by ring]
              exact mul_le_mul (hbd.trans (min_le_right _ _))
                (Real.rpow_le_rpow_of_nonpos (hδR n).1 hL.1 (by norm_num)) (by positivity) (by norm_num)
          · filter_upwards [ae_restrict_mem measurableSet_Icc] with L _
            exact (continuousAt_const.sub (Complex.continuous_exp.continuousAt.comp (by fun_prop))).mul continuousAt_const
        have h4 : ContinuousAt (fun t : ℝ => (Δ : ℂ) ^ (-((t : ℂ) * Complex.I))) y :=
          ContinuousAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hΔ.ne'))
        exact (((h1.mul h2).mul (continuousAt_const.mul h3)).mul h4).continuousWithinAt
      have hrestrict : volume.restrict ({y : ℝ | y ≠ 0} : Set ℝ) = volume :=
        Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr (measure_singleton 0))
      have h := hcont.aestronglyMeasurable (μ := volume) isOpen_ne.measurableSet
      rwa [hrestrict] at h
    · intro n
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with y hy
      have hy0 : y ≠ 0 := hy
      have hy_pos : 0 < |y| := abs_pos.mpr hy0
      rw [norm_mul, norm_mul, norm_mul, norm_mul, hnorm_4 y, hnorm_Δ y, one_mul, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * √π))]
      have hinner_bd : ‖∫ L in Icc (δ n) (R n),
          (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤
          4 * √2 * √|y| := by
        calc ‖∫ L in Icc (δ n) (R n),
              (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)‖
            ≤ ∫ L in Icc (δ n) (R n),
              ‖(1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ L in Icc (δ n) (R n), min (|y| * L) 2 * L ^ (-(3 / 2 : ℝ)) := by
              refine setIntegral_mono_on ?_
                ((integrableOn_min_rpow_neg_three_halves_nonneg (abs_nonneg y)).mono_set (fun L hL => lt_of_lt_of_le (hδR n).1 hL.1))
                measurableSet_Icc fun L hL => ?_
              · exact (ContinuousOn.norm ((continuousOn_const.sub (by fun_prop)).mul
                  (Complex.continuous_ofReal.comp_continuousOn
                    (ContinuousOn.rpow_const continuousOn_id (fun L (hL : L ∈ Icc (δ n) (R n)) =>
                      Or.inl (lt_of_lt_of_le (hδR n).1 hL.1).ne'))))).integrableOn_compact isCompact_Icc
              · have hL0 : 0 < L := lt_of_lt_of_le (hδR n).1 hL.1
                rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos hL0 _).le]
                have hbd := norm_one_sub_exp_neg_le_min (w := ((y : ℂ) * Complex.I) * (L : ℂ)) (by simp)
                rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
                  Real.norm_eq_abs, Real.norm_of_nonneg hL0.le] at hbd
                rw [show -((y : ℂ) * Complex.I) * (L : ℂ) = -(((y : ℂ) * Complex.I) * (L : ℂ)) by ring]
                exact mul_le_mul_of_nonneg_right hbd (by positivity)
          _ ≤ ∫ L in Ioi (0 : ℝ), min (|y| * L) 2 * L ^ (-(3 / 2 : ℝ)) :=
              setIntegral_mono_set (integrableOn_min_rpow_neg_three_halves_nonneg (abs_nonneg y))
                (ae_restrict_of_forall_mem measurableSet_Ioi fun L hL =>
                  mul_nonneg (le_min (mul_nonneg (abs_nonneg y) hL.le) (by norm_num)) (Real.rpow_pos_of_pos hL _).le)
                (Eventually.of_forall fun L hL => lt_of_lt_of_le (hδR n).1 hL.1)
          _ ≤ 4 * √2 * √|y| := integral_min_rpow_neg_three_halves_le hy_pos
      calc ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ *
            ((1 / (2 * √π)) * ‖∫ L in Icc (δ n) (R n),
              (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)‖)
          ≤ (|B| * (1 + |y|) ^ (-(2 : ℝ)) / |y|) * ((1 / (2 * √π)) * (4 * √2 * √|y|)) :=
            mul_le_mul (hnorm_G y hy0) (mul_le_mul_of_nonneg_left hinner_bd (by positivity))
              (by positivity) (by positivity)
        _ = |B| * (2 * √2 / √π) * ((1 + |y|) ^ (-(2 : ℝ)) * (|y| ^ (-(1 : ℝ)) * |y| ^ (1 / 2 : ℝ))) := by
            rw [Real.rpow_neg_one, Real.sqrt_eq_rpow |y|]; ring
        _ = |B| * (2 * √2 / √π) * ((1 + |y|) ^ (-(2 : ℝ)) * |y| ^ (-(1 / 2 : ℝ))) := by
            rw [← Real.rpow_add hy_pos]; norm_num
    · filter_upwards with y
      rw [cpow_half_I_mul_eq_integral y]
      have hint_L : IntegrableOn (fun L : ℝ =>
          (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) * ((L ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) (Ioi (0 : ℝ)) := by
        refine (integrableOn_min_rpow_neg_three_halves_nonneg (abs_nonneg y)).mono' ?_ ?_
        · exact ((continuousOn_const.sub (by fun_prop)).mul
            (Complex.continuous_ofReal.comp_continuousOn
              (ContinuousOn.rpow_const continuousOn_id (fun L hL => Or.inl (Set.mem_Ioi.mp hL).ne')))).aestronglyMeasurable
            measurableSet_Ioi
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
          have hL0 : 0 < L := hL
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos hL0 _).le]
          have hbd := norm_one_sub_exp_neg_le_min (w := ((y : ℂ) * Complex.I) * (L : ℂ)) (by simp)
          rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_of_nonneg hL0.le] at hbd
          rw [show -((y : ℂ) * Complex.I) * (L : ℂ) = -(((y : ℂ) * Complex.I) * (L : ℂ)) by ring]
          exact mul_le_mul_of_nonneg_right hbd (by positivity)
      have h3 := tendsto_setIntegral_Icc_Ioi hint_L
      exact ((tendsto_const_nhds.mul (tendsto_const_nhds.mul h3)).mul tendsto_const_nhds)
  simp_rw [hfub] at hlim_lhs
  exact tendsto_nhds_unique hlim_lhs hlim_rhs

/-- info: 'FormalResearch.SignUncertainty.uct_ce_preedge_T4_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_ce_preedge_T4_pos

/-- info: 'FormalResearch.SignUncertainty.uct_ce_preedge_T4_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_ce_preedge_T4_neg

/-- info: 'FormalResearch.SignUncertainty.cpow_half_I_mul_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cpow_half_I_mul_eq_integral

/-- info: 'FormalResearch.SignUncertainty.uct_sqrt_iy_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_sqrt_iy_inv

end FormalResearch.SignUncertainty
