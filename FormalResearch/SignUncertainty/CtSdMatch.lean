module

public import FormalResearch.SignUncertainty.CtSdMain

/-!
# The saddle-phase identity `(ct:theta-cfu-match)` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` (1), `(ct:theta-cfu-match)`.  **Proved.**
At the saddle `s_* = √(-a)` of the chart `τ = T(s;β)`, `θ_ε(T(s_*;β)) = s_* ψ(β)`, and with `v' = -Û_a`, `v = -Û`
one gets `2 v'^{1/2}(v - v') = -θ_ε(T(s_*;β))`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtSd

open FormalResearch.SignUncertainty.CtChart

lemma kap_cube : kap ^ 3 = 4 := by
  unfold kap CtAiry.kap
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma kap_mul_sqrt : kap * Real.sqrt kap = 2 := by
  have hk := kap_pos
  have h : (kap * Real.sqrt kap) ^ 2 = 2 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hk.le]; nlinarith [kap_cube]
  have hx : 0 < kap * Real.sqrt kap := by positivity
  have h2 : (kap * Real.sqrt kap - 2) * (kap * Real.sqrt kap + 2) = 0 := by nlinarith only [h]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linarith only [h3]
  · linarith only [h3, hx]

/-- **`(ct:theta-cfu-match)`**, phase at the saddle: `θ_ε(T(s_*;β)) = s_* ψ(β)` for `s_* = √(-a)`. -/
theorem theta_at_saddle {ε : ℝ} {ϑ : ℂ → ℂ} {ρ : ℝ} (hreg : ChartReg ε ϑ ρ) {β psi : ℝ} (hβ : |β| < ρ)
    (haC : aC (β : ℂ) = ((CtCfu.AF β : ℝ) : ℂ)) (hpsi : psiHat ϑ (β : ℂ) = (psi : ℂ))
    (ha : CtCfu.AF β ≤ 0) (hs : Real.sqrt (-CtCfu.AF β) < ρ)
    (hT : |Treal β (Real.sqrt (-CtCfu.AF β))| < 1 / 2) :
    CtOuter.outerTheta ε (Treal β (Real.sqrt (-CtCfu.AF β))) = Real.sqrt (-CtCfu.AF β) * psi := by
  set s : ℝ := Real.sqrt (-CtCfu.AF β) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = -CtCfu.AF β := Real.sq_sqrt (by linarith)
  have hsC : ‖(s : ℂ)‖ < ρ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]; exact hs
  have hβC : ‖(β : ℂ)‖ < ρ := by simpa using hβ
  obtain ⟨-, -, h3, -, h5, -⟩ := hreg (s : ℂ) (β : ℂ) hsC hβC
  have hTr := Tf_real_eq h3
  have hzero : (s : ℂ) ^ 2 - ysF (β : ℂ) = 0 := by
    rw [ysF_eq_neg_aC, haC]
    have : (s : ℂ) ^ 2 = ((s ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, hs2]; push_cast; ring
  rw [hzero, mul_zero, zero_mul, hpsi, hTr] at h5
  have := thOdd_real ε hT
  rw [this] at h5
  have h6 : ((CtOuter.outerTheta ε (Treal β s) : ℝ) : ℂ) = ((s * psi : ℝ) : ℂ) := by
    push_cast; linear_combination h5
  exact_mod_cast h6

/-- The algebraic form of `(ct:theta-cfu-match)`: `2 v'^{1/2}(v - v') = -s_* ψ`, where `v' = -Û_a`, `v = -Û`. -/
theorem match_algebra {lam a psi : ℝ} (hlam : 0 < lam) (ha : a ≤ 0) :
    2 * Real.sqrt (-(a / (kap * lam ^ 2))) * (-(Uhat lam a psi) - -(a / (kap * lam ^ 2))) =
      -(Real.sqrt (-a) * psi) := by
  have hk := kap_pos
  have hsk := Real.sqrt_pos.2 hk
  have h1 : -(Uhat lam a psi) - -(a / (kap * lam ^ 2)) = -(lam * psi / kap) := by
    unfold Uhat; field_simp; ring
  have h2 : Real.sqrt (-(a / (kap * lam ^ 2))) = Real.sqrt (-a) / (lam * Real.sqrt kap) := by
    have : -(a / (kap * lam ^ 2)) = (-a) / (lam * Real.sqrt kap) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hk.le]; field_simp
    rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  rw [h1, h2]
  have h3 := kap_mul_sqrt
  field_simp
  linear_combination (Real.sqrt (-a) * psi) * h3

/-- info: 'FormalResearch.SignUncertainty.CtSd.theta_at_saddle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_at_saddle

/-- info: 'FormalResearch.SignUncertainty.CtSd.match_algebra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms match_algebra

end FormalResearch.SignUncertainty.CtSd
