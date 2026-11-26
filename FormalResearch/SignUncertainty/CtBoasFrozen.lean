module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasRegime
public import FormalResearch.SignUncertainty.CtBoasNeg
public import FormalResearch.SignUncertainty.CtBoasAverage

/-!
# `ct:boas` Step 4 output: the frozen windowed Fejér bound `ct:P-lb` in the form used by Step 5

`constant_terms_lower.tex`, `ct:boas` Steps 3-4, `ct:P-lb`.  For a feasible `f` (`T`, mass `M`), a frozen centre
`L₀ ≥ L_T` and the width `W = N/(c τ_j)`, `N² = 10⁶(1+L_j) log c`, the window integral
`P(L₀) = ∫ G_W(L-L₀) h(L) (1 + 2cos(cτ₀ L + φ)) dL` (`τ₀ = m⁻¹(L₀)`) satisfies `P(L₀) ≥ -Pb` with the explicit
`Pb = n M e^{-(L₀-L_T)²/(2W²)}/(√(2π)W) + 2M/(n√(2π)W) + 6nM c^{-20}(1+√(π/(2π²W²)))` (`hankel_frozen_P_lb`: the
Fejér inequality `hankel_P_lb_regime_of` with the negative part `hankel_window_neg_le` and `‖G h‖₁ ≤ M/(√(2π)W)`).
**Proved**, unconditional (regime hypotheses explicit).
-/

@[expose] public section

open Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow

/-- The explicit bound `Pb` of `ct:P-lb`. -/
noncomputable def hankelFrozenPb (c M W LT L0 : ℝ) (n : ℕ) : ℝ :=
  n * (M * (Real.exp (-(1 / (2 * W ^ 2)) * (L0 - LT) ^ 2) / (√(2 * π) * W))) +
    2 / n * (M / (√(2 * π) * W)) + 6 * n * M * ((c ^ 20)⁻¹ * (1 + √(π / (2 * π ^ 2 * W ^ 2))))

/-- `‖G_W h‖₁ ≤ M / (√(2π) W)`. -/
lemma integral_abs_gauss_mul_hankelHL_le {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    {W : ℝ} (hW : 0 < W) (L0 : ℝ) :
    ∫ x, |gaussK W (x - L0) * hankelHL c f x| ≤ hankelMass c f / (√(2 * π) * W) := by
  have hh := integrable_hankelHL hc hf
  have hG : ∀ y, gaussK W y ≤ 1 / (√(2 * π) * W) := fun y => by
    unfold gaussK
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 1 / (2 * W ^ 2) * y ^ 2 := by positivity
    linarith
  have hpt : ∀ x, |gaussK W (x - L0) * hankelHL c f x| ≤ (1 / (√(2 * π) * W)) * |hankelHL c f x| := fun x => by
    rw [abs_mul, abs_of_nonneg (gaussK_nonneg hW _)]
    exact mul_le_mul_of_nonneg_right (hG _) (abs_nonneg _)
  calc ∫ x, |gaussK W (x - L0) * hankelHL c f x| ≤ ∫ x, (1 / (√(2 * π) * W)) * |hankelHL c f x| :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hh.abs.const_mul _) (ae_of_all _ hpt)
    _ = hankelMass c f / (√(2 * π) * W) := by
        rw [integral_const_mul, integral_abs_hankelHL hc hf]; ring

/-- **`ct:P-lb`** for the frozen kernel, from `hankel_P_lb_regime_of` and the negative-part bound. -/
theorem hankel_frozen_P_lb {c ε T : ℝ} (hc3 : 3 ≤ c)
    (hF1 : 156000000000 * Real.log c ^ 2 ≤ (c ^ (1 / 3 : ℝ)) ^ 3)
    (hF2 : 8320 * Real.log c ≤ c ^ (1 / 3 : ℝ))
    {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    {τ0 τj Lj : ℝ} (hτ0 : 0 < τ0) (hτj1 : τ0 / 3 ≤ τj) (hτj2 : τj ≤ 3 * τ0) (hLj : 0 ≤ Lj)
    (hL1 : hankelEdgeM τ0 ≤ 1 + Lj) (hL2 : 1 + Lj ≤ 2 * (1 + hankelEdgeM τ0))
    (hlo : c ^ (-(1 / 3) : ℝ) ≤ hankelEdgeM τ0) (hhi : hankelEdgeM τ0 ≤ Real.log c)
    {n : ℕ} (hn : 2 ≤ n) (φ : ℝ) {Np2 W : ℝ} (hNpd : Np2 = 1000000 * (1 + Lj) * Real.log c)
    (hWd : W = √Np2 / (c * τj)) {LT : ℝ} (hLT : ∀ L, LT ≤ L → T ≤ c * (Real.exp L / π ^ 2))
    (hL0 : LT ≤ hankelEdgeM τ0) :
    -hankelFrozenPb c (hankelMass c f) W LT (hankelEdgeM τ0) n ≤
      ∫ x, gaussK W (x - hankelEdgeM τ0) * hankelHL c f x * (1 + 2 * Real.cos (c * τ0 * x + φ)) := by
  have hc0 : 0 < c := by linarith
  have hτj : 0 < τj := lt_of_lt_of_le (by positivity) hτj1
  have hlog1 : 1 ≤ Real.log c := by
    have : Real.exp 1 ≤ c := by
      have := Real.exp_one_lt_d9; linarith
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hNp : 0 < Np2 := by rw [hNpd]; positivity
  have hW : 0 < W := by rw [hWd]; exact div_pos (Real.sqrt_pos.2 hNp) (by positivity)
  have h1 := hankel_P_lb_regime_of hc3 hF1 hF2 hf.toIsHankelEigenfn hε hτ0 hτj1 hτj2 hLj hL1 hL2 hlo hhi hn φ hNpd hWd
  have hneg := hankel_window_neg_le hc0 hf hW hLT hL0
  have habs := integral_abs_gauss_mul_hankelHL_le hc0 hf.toIsHankelEigenfn hW (hankelEdgeM τ0)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn1 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine le_trans ?_ h1
  unfold hankelFrozenPb
  have a1 := mul_le_mul_of_nonneg_left hneg hn0
  have a2 := mul_le_mul_of_nonneg_left habs (by positivity : (0 : ℝ) ≤ 2 / n)
  linarith

/-- info: 'FormalResearch.SignUncertainty.hankel_frozen_P_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_frozen_P_lb

end FormalResearch.SignUncertainty
