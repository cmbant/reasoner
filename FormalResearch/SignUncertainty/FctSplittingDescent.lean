/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingDefs
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The descent bound `(fct:F-38-bnd)` and the Cauchy splitting integrals (`fct:splitting` (1)-(2))

Paper I (`constant_terms_five.tex`), Lemma FCT.6 `fct:splitting`, items (1) and (2), `(fct:F-38-bnd)`, `(fct:Fpm-def)`.

* `FctDescentStmt` is **`(fct:F-38-bnd)`**, the global descent bound `|F(σ+iy)| ≤ C c⁻¹/log(2+|y|)` on `5/16 ≤ σ ≤ 7/16`, for the
  concrete `F = fctFint` of `FctSplittingDefs.lean` and the chosen zero pair.  Its proof in the paper (proof of `fct:splitting` (1)) shifts the
  integration path of `Ψ_c` to the vertical ray `ζ + i[0,∞)` (this uses `I_ε(L₁, α) = 0`, `fctWarpI_pair`), writes `K₀A_ε = c⁻¹ ∂_t(e^{cΦ_Mel}) W`
  and integrates by parts twice, with `W, W', W''` bounded on the interior rectangle `5/16 ≤ Re ≤ 7/16` by `C|A₀(ζ)|(1+s)^C e^{-πs}`
  (hyperbolic factors of `H_*`, the Binet bounds for `B_c`, `(fct:gD-int)` for `D_{τ₁}`, `fct:phikill` (1) for `φ_kill`), `|Φ'| ≳ log(2+y)`
  (`Re g_tan(σ+iu) = -log(πu/2) + O(1)`) and `Re Φ_Mel` non-increasing along the ray.  The interior-strip estimates of these factors (`Re ≠ 0`)
  are not in Lean (the existing bounds are on the edges `Re = 0, 1`), so `(fct:F-38-bnd)` is a named input: the field `descent` of `FctMainHankelInputs`.
* `fctKsp_div_le`: the elementary kernel bound `|K_sp(t, ζ)/(t - ζ)| ≤ K (1+|y|)⁻²` on `Re t = σ`, `3/8 ≤ σ ≤ 7/16`, `Re ζ ≠ σ`.
* `fctCauchy_norm_le`, `fctSplittingNorm_of_descent`: **`N_c = 1 + O(c⁻¹)`** (`fct:splitting` (2)), proved from `FctDescentStmt`; this is the former field
  `splitting_norm`.

Class: `FctDescentStmt` is a named input (open); the rest is proved from it.
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

/-- **`(fct:F-38-bnd)`** (`fct:splitting` (1); named input): for `c ≥ c₀`, `ε = ±1`, uniformly in `y ∈ ℝ` and `σ ∈ [5/16, 7/16]`,
`|F(σ+iy)| ≤ C c⁻¹/log(2+|y|)`, where `F = Φ_c - 1 = fctFint` for the chosen zero pair of `fct:warp-asymp` (1). -/
def FctDescentStmt {K4 : ℝ} (h : FctWarpSolveStmt K4) : Prop :=
  ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∀ σ y : ℝ, 5 / 16 ≤ σ → σ ≤ 7 / 16 →
    ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((σ : ℂ) + y * Complex.I)‖ ≤ C * c⁻¹ / Real.log (2 + |y|)

/-- A lower bound `‖σ + iy‖ ≥ (3/16)(1+|y|)` for `σ ≥ 3/8`. -/
lemma norm_line_ge {σ : ℝ} (hσ : 3 / 8 ≤ σ) (y : ℝ) : 3 / 16 * (1 + |y|) ≤ ‖(σ : ℂ) + y * Complex.I‖ := by
  have h1 : |σ| ≤ ‖(σ : ℂ) + y * Complex.I‖ := by
    simpa using Complex.abs_re_le_norm ((σ : ℂ) + y * Complex.I)
  have h2 : |y| ≤ ‖(σ : ℂ) + y * Complex.I‖ := by
    simpa using Complex.abs_im_le_norm ((σ : ℂ) + y * Complex.I)
  rw [abs_of_nonneg (by linarith)] at h1
  have := abs_nonneg y
  nlinarith

/-- `‖σ + 1 + iy‖ ≤ 2 (1+|y|)` for `σ ≤ 1`, `σ ≥ 0`. -/
lemma norm_line_add_one_le {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (y : ℝ) :
    ‖((σ : ℂ) + y * Complex.I) + 1‖ ≤ 2 * (1 + |y|) := by
  have : ((σ : ℂ) + y * Complex.I) + 1 = ((σ + 1 : ℝ) : ℂ) + (y : ℂ) * Complex.I := by push_cast; ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  simp only [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ σ + 1)]
  linarith [abs_nonneg y]

/-- `‖σ + iy - ζ‖ ≥ κ(1+|y|)` with `κ = d/(1 + |Im ζ| + d)`, `d = |Re ζ - σ|`. -/
lemma norm_line_sub_ge {σ : ℝ} {ζ : ℂ} (hd : ζ.re ≠ σ) (y : ℝ) :
    |ζ.re - σ| / (1 + |ζ.im| + |ζ.re - σ|) * (1 + |y|) ≤ ‖((σ : ℂ) + y * Complex.I) - ζ‖ := by
  set d := |ζ.re - σ| with hd'
  have hdpos : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hd)
  have hre : (((σ : ℂ) + y * Complex.I) - ζ).re = σ - ζ.re := by simp
  have him : (((σ : ℂ) + y * Complex.I) - ζ).im = y - ζ.im := by simp
  have h1 : d ≤ ‖((σ : ℂ) + y * Complex.I) - ζ‖ := by
    have := Complex.abs_re_le_norm (((σ : ℂ) + y * Complex.I) - ζ)
    rw [hre] at this
    rw [hd', abs_sub_comm]; exact this
  have h2 : |y| - |ζ.im| ≤ ‖((σ : ℂ) + y * Complex.I) - ζ‖ := by
    have := Complex.abs_im_le_norm (((σ : ℂ) + y * Complex.I) - ζ)
    rw [him] at this
    have h3 : |y| - |ζ.im| ≤ |y - ζ.im| := by
      have := abs_sub_abs_le_abs_sub y ζ.im; linarith
    linarith
  set M := |ζ.im|
  have hM : 0 ≤ M := abs_nonneg _
  have hden : 0 < 1 + M + d := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  rcases le_or_gt |y| (M + d) with hy | hy
  · nlinarith [abs_nonneg y]
  · have : d * (1 + |y|) ≤ (|y| - M) * (1 + M + d) := by nlinarith [abs_nonneg y]
    nlinarith [abs_nonneg y]

/-- **Kernel bound.**  On `Re t = σ`, `3/8 ≤ σ ≤ 7/16`, with `Re ζ ≠ σ`: `|K_sp(t, ζ)/(t - ζ)| ≤ K (1+|y|)⁻²`, `K` depending only on `ζ` and `σ`. -/
lemma fctKsp_div_le {σ : ℝ} (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16) {ζ : ℂ} (hd : ζ.re ≠ σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ,
      ‖fctKsp ((σ : ℂ) + y * Complex.I) ζ / ((σ : ℂ) + y * Complex.I - ζ)‖ ≤ K / (1 + |y|) ^ 2 := by
  set κ : ℝ := |ζ.re - σ| / (1 + |ζ.im| + |ζ.re - σ|) with hκ
  have hdpos : 0 < |ζ.re - σ| := abs_pos.mpr (sub_ne_zero.mpr hd)
  have hκpos : 0 < κ := by positivity
  refine ⟨‖ζ‖ ^ 3 * (‖ζ + 1‖⁻¹) ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) / κ, by positivity, fun y => ?_⟩
  set t : ℂ := (σ : ℂ) + y * Complex.I with ht
  have hy : 0 < 1 + |y| := by positivity
  have h1 : 3 / 16 * (1 + |y|) ≤ ‖t‖ := norm_line_ge hσ y
  have h2 : ‖t + 1‖ ≤ 2 * (1 + |y|) := norm_line_add_one_le (σ := σ) (by linarith) (by linarith) y
  have h3 : κ * (1 + |y|) ≤ ‖t - ζ‖ := norm_line_sub_ge (σ := σ) hd y
  have htpos : 0 < ‖t‖ := lt_of_lt_of_le (by positivity) h1
  have hts : 0 < ‖t - ζ‖ := lt_of_lt_of_le (by positivity) h3
  set a := ‖ζ + 1‖⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  have key : ‖fctKsp t ζ / (t - ζ)‖ = ‖ζ‖ ^ 3 / ‖t‖ ^ 3 * (‖t + 1‖ * a) ^ 2 / ‖t - ζ‖ := by
    simp only [fctKsp, norm_div, norm_pow, norm_mul, ha]; ring
  rw [key]
  have hnum : ‖ζ‖ ^ 3 / ‖t‖ ^ 3 * (‖t + 1‖ * a) ^ 2 ≤
      ‖ζ‖ ^ 3 * a ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) / (1 + |y|) := by
    have e1 : ‖t‖ ^ 3 ≥ (3 / 16) ^ 3 * (1 + |y|) ^ 3 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 3
    have e2 : ‖t + 1‖ ^ 2 ≤ 2 ^ 2 * (1 + |y|) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [mul_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hy]
    have : ‖ζ‖ ^ 3 * (‖t + 1‖ ^ 2 * a ^ 2) * (1 + |y|) ≤
        ‖ζ‖ ^ 3 * (2 ^ 2 * (1 + |y|) ^ 2 * a ^ 2) * (1 + |y|) := by gcongr
    refine this.trans ?_
    have : ‖ζ‖ ^ 3 * a ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) * ‖t‖ ^ 3 ≥
        ‖ζ‖ ^ 3 * a ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) * ((3 / 16) ^ 3 * (1 + |y|) ^ 3) := by gcongr
    refine le_trans (le_of_eq ?_) this
    field_simp
  calc ‖ζ‖ ^ 3 / ‖t‖ ^ 3 * (‖t + 1‖ * a) ^ 2 / ‖t - ζ‖
      ≤ (‖ζ‖ ^ 3 * a ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) / (1 + |y|)) / (κ * (1 + |y|)) := by
        apply div_le_div₀ (by positivity) hnum (by positivity) h3
    _ = ‖ζ‖ ^ 3 * a ^ 2 * (2 ^ 2 / (3 / 16) ^ 3) / κ / (1 + |y|) ^ 2 := by
        field_simp

/-- `y ↦ (1+|y|)⁻²` is integrable on `ℝ`. -/
lemma integrable_inv_one_add_abs_sq : Integrable (fun y : ℝ => 1 / (1 + |y|) ^ 2) := by
  have h : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(2 : ℝ))) := integrable_one_add_norm (E := ℝ) (r := 2) (by simp)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp

/-- **The Cauchy integral is bounded by the sup of `|F|` on the contour.**  For `3/8 ≤ σ ≤ 7/16`, `Re ζ ≠ σ`, there is `K ≥ 0` (depending only on `σ, ζ`) with
`‖C_σ(ζ)‖ ≤ K B` whenever `|F(σ+iy)| ≤ B` for all `y`. -/
lemma fctCauchy_norm_le {σ : ℝ} (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16) {ζ : ℂ} (hd : ζ.re ≠ σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ K4 ε c L1 α B : ℝ, 0 ≤ B →
      (∀ y : ℝ, ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B) →
        ‖fctCauchy K4 ε c L1 α σ ζ‖ ≤ K * B := by
  obtain ⟨K, hK0, hK⟩ := fctKsp_div_le hσ hσ' hd
  refine ⟨(1 / (2 * π)) * K * ∫ y : ℝ, 1 / (1 + |y|) ^ 2, ?_, fun K4 ε c L1 α B hB hF => ?_⟩
  · have : 0 ≤ ∫ y : ℝ, 1 / (1 + |y|) ^ 2 := integral_nonneg fun y => by positivity
    positivity
  unfold fctCauchy
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hint : ‖∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α σ ζ y‖ ≤ ∫ y : ℝ, K * B * (1 / (1 + |y|) ^ 2) := by
    refine norm_integral_le_of_norm_le (integrable_inv_one_add_abs_sq.const_mul (K * B)) (Filter.Eventually.of_forall fun y => ?_)
    unfold fctCauchyIntegrand
    rw [mul_div_right_comm, norm_mul]
    calc _ ≤ (K / (1 + |y|) ^ 2) * B := by
          exact mul_le_mul (hK y) (hF y) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [integral_const_mul] at hint
  calc 1 / (2 * π) * ‖∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α σ ζ y‖
      ≤ 1 / (2 * π) * (K * B * ∫ y : ℝ, 1 / (1 + |y|) ^ 2) := by gcongr
    _ = _ := by ring

/-- **`fct:splitting` (2), `N_c = 1 + O_{K₄}(c⁻¹)`** (the former field `splitting_norm`), from the descent bound `(fct:F-38-bnd)`: `N_c = Re(1 - F₊(1))`,
`F₊(1)` the Cauchy integral on `Re t = 3/8` at `ζ = 1`. -/
theorem fctSplittingNorm_of_descent {K4 : ℝ} {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    FctSplittingNormStmt (fctNc h) := by
  obtain ⟨C, c₀, hC⟩ := hD
  obtain ⟨K, hK0, hK⟩ := fctCauchy_norm_le (σ := 3 / 8) le_rfl (by norm_num) (ζ := 1) (by norm_num)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|C| / Real.log 2 * K, max c₀ 1, fun ε c hε hc => ?_⟩
  have hc1 : 1 ≤ c := (le_max_right _ _).trans hc
  have hcpos : 0 < c := by linarith
  have hB : ∀ y : ℝ, ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (((3 / 8 : ℝ) : ℂ) + y * Complex.I)‖ ≤
      |C| / Real.log 2 * c⁻¹ := by
    intro y
    refine (hC ε c hε ((le_max_left _ _).trans hc) (3 / 8) y (by norm_num) (by norm_num)).trans ?_
    have h2 : Real.log 2 ≤ Real.log (2 + |y|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg y])
    calc C * c⁻¹ / Real.log (2 + |y|) ≤ |C| * c⁻¹ / Real.log (2 + |y|) := by
          gcongr
          · exact (Real.log_pos (by linarith [abs_nonneg y])).le
          · exact le_abs_self C
      _ ≤ |C| * c⁻¹ / Real.log 2 := by gcongr
      _ = _ := by ring
  have hnorm := hK K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) _ (by positivity) hB
  have hNc : fctNc h ε c - 1 = -(fctCauchy K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8) 1).re := by
    unfold fctNc fctNcC fctPhiWarp
    have h1 : ¬ ((1 : ℂ).re < 7 / 16) := by norm_num
    simp only [h1, ite_false]
    simp
  rw [hNc, abs_neg]
  refine (Complex.abs_re_le_norm _).trans (hnorm.trans (le_of_eq ?_))
  ring

/-- info: 'FormalResearch.SignUncertainty.fctSplittingNorm_of_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctSplittingNorm_of_descent

end FormalResearch.SignUncertainty
