/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctBumpSymCheck

/-!
# `(fct:vac-paired)`: the paired decomposition of `O - F` (F2a, `fct:physical-budget` proof, vacuum integral)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:physical-budget`, display `(fct:vac-paired)`.

With `u = L - s` (`s = θ₁^ε / c`), `Ã₁ = L₁ - s` (so `L - L₁ = u - Ã₁`), the physical oscillation envelope
`O(L) = I_osc^{warp}(L) = P(u) |u - L₁ Φ(u)| / (L - L₁)`, where `P = I_osc^{DH₀}(1 + Δ_curv ∘ τ₀)` and `Φ(u) = φ_kill(i τ₀(u); a)`
(Proposition `fct:warp-asymp` (3)), and `F(L) = u/(L - L₁) · I_fl(u)` (`physF`).

**Proved here** (`physOsc_sub_physF_le`): the one-sided form of `(fct:vac-paired)`, for `P ≥ 0` and `u - L₁ Re Φ > 0`,
`O - F ≤ [u D_*(u) - L₁ Re Φ P + P (L₁ Im Φ)² / (2 (u - L₁ Re Φ))] / (u - Ã₁)`, `D_* = P - I_fl`
(from `‖z‖ = √(a² + b²) ≤ a + b²/(2a)`), together with the exact algebraic identities used to split the `1/u` expansions of parts (b)-(d)
(`vac_E1_eq`, `vac_E2_eq`).

Class: proved, no hypotheses.
-/

@[expose] public section

open Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.FctSym

/-- `I_osc^{warp}(L) = P(u) |u - L₁ Φ(u)| / (L - L₁)`, `u = L - s`, with `P = I_osc^{DH₀}(1 + Δ_curv ∘ τ₀)` and
`Φ(u) = φ_kill(i τ₀(u); a)` (`fct:warp-asymp` (3)). -/
noncomputable def physOsc (P : ℝ → ℝ) (Φ : ℝ → ℂ) (s L1 x : ℝ) : ℝ :=
  P (x - s) * ‖((x - s : ℝ) : ℂ) - (L1 : ℂ) * Φ (x - s)‖ / (x - L1)

/-- `‖u - L₁Φ‖ ≤ (u - L₁ Re Φ) + (L₁ Im Φ)²/(2 (u - L₁ Re Φ))` when `u - L₁ Re Φ > 0`. -/
lemma norm_sub_mul_le (u L1 : ℝ) (Φ : ℂ) (h : 0 < u - L1 * Φ.re) :
    ‖(u : ℂ) - (L1 : ℂ) * Φ‖ ≤ (u - L1 * Φ.re) + (L1 * Φ.im) ^ 2 / (2 * (u - L1 * Φ.re)) := by
  set a : ℝ := u - L1 * Φ.re with ha
  set b : ℝ := L1 * Φ.im with hb
  have hnorm : ‖(u : ℂ) - (L1 : ℂ) * Φ‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_im, Complex.mul_im, zero_sub, ha, hb]
    ring
  rw [hnorm]
  have h2a : 0 < 2 * a := by linarith
  have hnn : 0 ≤ a + b ^ 2 / (2 * a) := by positivity
  rw [Real.sqrt_le_left hnn]
  have e : (a + b ^ 2 / (2 * a)) ^ 2 = a ^ 2 + b ^ 2 + (b ^ 2 / (2 * a)) ^ 2 := by
    field_simp
    ring
  rw [e]
  nlinarith [sq_nonneg (b ^ 2 / (2 * a))]

/-- **`(fct:vac-paired)`, one-sided form** (`fct:physical-budget`): for `P(u) ≥ 0`, `u > 0`, `L - L₁ > 0`, `u - L₁ Re Φ > 0`,
`O - F ≤ [u (P - I_fl)(u) - L₁ Re Φ · P + P (L₁ Im Φ)² / (2 (u - L₁ Re Φ))] / (L - L₁)`, `u = L - s`. -/
lemma physOsc_sub_physF_le {P : ℝ → ℝ} {Φ : ℝ → ℂ} {s L1 x : ℝ} (hP : 0 ≤ P (x - s)) (hx : 0 < x - L1)
    (ha : 0 < (x - s) - L1 * (Φ (x - s)).re) :
    physOsc P Φ s L1 x - physF s L1 x ≤
      ((x - s) * (P (x - s) - uctIfl (x - s)) - L1 * (Φ (x - s)).re * P (x - s) +
        P (x - s) * (L1 * (Φ (x - s)).im) ^ 2 / (2 * ((x - s) - L1 * (Φ (x - s)).re))) / (x - L1) := by
  have hn := norm_sub_mul_le (x - s) L1 (Φ (x - s)) ha
  have h1 : P (x - s) * ‖((x - s : ℝ) : ℂ) - (L1 : ℂ) * Φ (x - s)‖ ≤
      P (x - s) * ((x - s - L1 * (Φ (x - s)).re) + (L1 * (Φ (x - s)).im) ^ 2 / (2 * (x - s - L1 * (Φ (x - s)).re))) :=
    mul_le_mul_of_nonneg_left hn hP
  unfold physOsc physF
  have e : P (x - s) * ‖((x - s : ℝ) : ℂ) - (L1 : ℂ) * Φ (x - s)‖ / (x - L1) - (x - s) / (x - L1) * uctIfl (x - s) =
      (P (x - s) * ‖((x - s : ℝ) : ℂ) - (L1 : ℂ) * Φ (x - s)‖ - (x - s) * uctIfl (x - s)) / (x - L1) := by
    field_simp
  rw [e]
  refine div_le_div_of_nonneg_right ?_ hx.le
  have e2 : P (x - s) * ((x - s - L1 * (Φ (x - s)).re) + (L1 * (Φ (x - s)).im) ^ 2 / (2 * (x - s - L1 * (Φ (x - s)).re))) -
      (x - s) * uctIfl (x - s) =
      (x - s) * (P (x - s) - uctIfl (x - s)) - L1 * (Φ (x - s)).re * P (x - s) +
        P (x - s) * (L1 * (Φ (x - s)).im) ^ 2 / (2 * ((x - s) - L1 * (Φ (x - s)).re)) := by
    ring
  linarith

/-- Exact identity `u/(u - A) = 1 + A/u + A²/u² + A³/(u²(u - A))` combined with `γ = 1 - κ u^{-3}`:
`γ u/(u - A) = 1 + A/u + A²/u² + (A³ - κ)/(u²(u - A))` (`u ≠ 0`, `u ≠ A`). -/
lemma vac_E1_eq {u A κ : ℝ} (hu : u ≠ 0) (hA : u - A ≠ 0) :
    (1 - κ * (u ^ 3)⁻¹) * (u / (u - A)) = 1 + A / u + A ^ 2 / u ^ 2 + (A ^ 3 - κ) / (u ^ 2 * (u - A)) := by
  field_simp
  ring

/-- Exact identity `γ/(u - A) = 1/u + (A - κ u^{-2})/(u(u - A))`. -/
lemma vac_E2_eq {u A κ : ℝ} (hu : u ≠ 0) (hA : u - A ≠ 0) :
    (1 - κ * (u ^ 3)⁻¹) / (u - A) = 1 / u + (A - κ * (u ^ 2)⁻¹) / (u * (u - A)) := by
  field_simp
  ring

end FormalResearch.SignUncertainty.FctSym
