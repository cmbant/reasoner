/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpZero
public import FormalResearch.SignUncertainty.FctWarpAdmiss

/-!
# The splitting function `Φ̂_c` and the normalisation `N_c` as definitions (`fct:splitting`, `(fct:Phihat-def)`)

Paper I (`constant_terms_five.tex`), `(fct:A-Psi-def)`, `(fct:F-def)`, `(fct:Fpm-def)`, `(fct:Phiwarp-def)`, `(fct:Phihat-def)`.

For `H₀ = H_*`, fixed `K₄`, `ε = ±1`, `c` and a zero pair `(L₁, α)` (`ξ₁ = e^{L₁}/π²`):

* `fctPsi` : `Ψ_c(ζ) = K₀(ζ, ξ₁)⁻¹ ∫₀^ζ K₀ A_ε dt` along the segment `t = sζ`, `s ∈ [0,1]` (the strip is convex, so this is the paper's
  path-independent integral); `A_ε = fctWarpA`.  The value at `ζ = 0` is `0`.
* `fctPhiC` : `Φ_c = c Ψ_c / (D_{τ₁} (H_*/G_ε))` and `fctFint = Φ_c - 1 = F` (`(fct:F-def)`).
* `fctCauchy σ` : the Cauchy splitting integral of `(fct:Fpm-def)` along `Re t = σ`,
  `(1/2πi) ∫ K_sp(t, ζ) F(t)/(t - ζ) dt = (1/2π) ∫ K_sp F(σ+iy)/(σ+iy-ζ) dy`.
* `fctPhiWarp` : `Φ^warp_c` of `(fct:Phiwarp-def)`.  **Deviation (continuation across the jump line).**  The paper's definition on
  `Re ζ < 3/8` and `Re ζ > 3/8` leaves the line `Re ζ = 3/8` undefined (the integral has its pole on the contour), while
  `fct:splitting` (2) asserts holomorphy on all `Re ζ > 0`.  So that Lean's value on that line is the continuation, `F_-` is taken
  with the contour `Re t = 7/16` for `Re ζ < 7/16` (equal to the paper's `F_-` on `Re ζ < 3/8` by Cauchy's theorem, since `F` is holomorphic and
  `O(c⁻¹/log)` on `3/8 ≤ Re ≤ 7/16`, `fct:splitting` (1)), and `1 - F_+` with the contour `Re t = 3/8` for `Re ζ ≥ 7/16`.
* `fctNcC = Φ^warp_c(1) = 1 - F₊(1)` (complex), `fctNc = Re` of it (`N_c` is real by real symmetry), `fctBetaC = Φ^warp'_c(1)/N_c`,
  `fctQ1 = q₁`, and `fctPhiHat = Φ^warp_c/N_c + β_c q₁` (`(fct:Phihat-def)`).

`Bochner integrals are 0 for non-integrable integrands`: the integrability of the segment integral of `Ψ_c` and of the two Cauchy integrands is
stated, not assumed away: `FctSplittingIntStmt` (a field of `FctMainHankelInputs`).  Without it the integrals could take the junk value `0`.

The zero pair is the chosen one of `fct:warp-asymp` (1) (`fctWarpL1`, `fctWarpAlpha`), `fctPhiHat K4 h`.
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

/-- `Ψ_c(ζ) = K₀(ζ, ξ₁)⁻¹ ∫₀^ζ K₀(t, ξ₁) A_ε(t) dt` (`(fct:A-Psi-def)`), along the segment `t = sζ`. -/
noncomputable def fctPsi (K4 ε c L1 α : ℝ) (ζ : ℂ) : ℂ :=
  (mellinK0 c ζ (fctXi1 L1))⁻¹ *
    (ζ * ∫ s in (0 : ℝ)..1, mellinK0 c ((s : ℂ) * ζ) (fctXi1 L1) * fctWarpA K4 ε c L1 α ((s : ℂ) * ζ))

/-- `Φ_c = c G_ε Ψ_c / (D_{τ₁} H_*)` (`(fct:F-def)`), with `H_*/G_ε = ctHG`. -/
noncomputable def fctPhiC (K4 ε c L1 α : ℝ) (ζ : ℂ) : ℂ :=
  (c : ℂ) * fctPsi K4 ε c L1 α ζ / (fctDcompAt K4 c α ζ * ctHG ε ζ)

/-- `F = Φ_c - 1` (`(fct:F-def)`). -/
noncomputable def fctFint (K4 ε c L1 α : ℝ) (ζ : ℂ) : ℂ := fctPhiC K4 ε c L1 α ζ - 1

/-- `K_sp(t, ζ) = (ζ/t)³ ((t+1)/(ζ+1))²` (`(fct:Fpm-def)`). -/
noncomputable def fctKsp (t ζ : ℂ) : ℂ := (ζ / t) ^ 3 * ((t + 1) / (ζ + 1)) ^ 2

/-- The Cauchy splitting integrand along `Re t = σ`, `t = σ + iy`. -/
noncomputable def fctCauchyIntegrand (K4 ε c L1 α σ : ℝ) (ζ : ℂ) (y : ℝ) : ℂ :=
  fctKsp ((σ : ℂ) + y * Complex.I) ζ * fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I) /
    ((σ : ℂ) + y * Complex.I - ζ)

/-- `(1/2πi) ∫_{Re t = σ} K_sp(t, ζ) F(t)/(t - ζ) dt = (1/2π) ∫ ... dy` (`(fct:Fpm-def)`). -/
noncomputable def fctCauchy (K4 ε c L1 α σ : ℝ) (ζ : ℂ) : ℂ :=
  ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, fctCauchyIntegrand K4 ε c L1 α σ ζ y

/-- `Φ^warp_c` (`(fct:Phiwarp-def)`; contour `7/16` for the `F_-` part, see the module docstring). -/
noncomputable def fctPhiWarp (K4 ε c L1 α : ℝ) (ζ : ℂ) : ℂ :=
  if ζ.re < 7 / 16 then fctPhiC K4 ε c L1 α ζ - fctCauchy K4 ε c L1 α (7 / 16) ζ
  else 1 - fctCauchy K4 ε c L1 α (3 / 8) ζ

/-- `N_c = Φ^warp_c(1) = 1 - F₊(1)` (complex form). -/
noncomputable def fctNcC (K4 ε c L1 α : ℝ) : ℂ := fctPhiWarp K4 ε c L1 α 1

/-- `β_c = Φ^warp_c'(1)/N_c` (`(fct:Phihat-def)`). -/
noncomputable def fctBetaC (K4 ε c L1 α : ℝ) : ℂ :=
  deriv (fctPhiWarp K4 ε c L1 α) 1 / fctNcC K4 ε c L1 α

/-- `q₁(ζ) = 16 ζ³ (1 - ζ)/(ζ + 1)⁴`. -/
noncomputable def fctQ1 (ζ : ℂ) : ℂ := 16 * ζ ^ 3 * (1 - ζ) / (ζ + 1) ^ 4

/-- `Φ̂_c = Φ^warp_c/N_c + β_c q₁` (`(fct:Phihat-def)`) for the zero pair `(L₁, α)`. -/
noncomputable def fctPhiHatAt (K4 ε c L1 α : ℝ) (ζ : ℂ) : ℂ :=
  fctPhiWarp K4 ε c L1 α ζ / fctNcC K4 ε c L1 α + fctBetaC K4 ε c L1 α * fctQ1 ζ

/-- **`Φ̂_c`** of `fct:splitting` for the chosen zero pair of `fct:warp-asymp` (1). -/
noncomputable def fctPhiHat {K4 : ℝ} (h : FctWarpSolveStmt K4) : ℝ → ℝ → ℂ → ℂ :=
  fun ε c => fctPhiHatAt K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)

/-- **`N_c = Φ^warp_c(1) = 1 - F₊(1)`** of `fct:splitting` (real part; `N_c` is real by real symmetry). -/
noncomputable def fctNc {K4 : ℝ} (h : FctWarpSolveStmt K4) : ℝ → ℝ → ℝ :=
  fun ε c => (fctNcC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)).re

/-- Integrability of the integrals in the definitions (so that no Bochner junk value `0` enters): for `c ≥ c₀`, the segment
integrand of `Ψ_c` on `ζ ∈ S̄`, `Re ζ ≤ 7/16`, and the Cauchy integrands of `(fct:Fpm-def)` (contour `7/16` for `Re ζ < 7/16`, contour `3/8` for
`Re ζ ≥ 7/16`) are integrable (`fct:splitting` (2) and (3): `|F(σ+iy)| = O(c⁻¹/log(2+|y|))`, `K_sp F/(t-ζ) = O(|t|⁻²/log)`). -/
def FctSplittingIntStmt {K4 : ℝ} (h : FctWarpSolveStmt K4) : Prop :=
  ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
    (∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 7 / 16 →
      IntervalIntegrable (fun s : ℝ => mellinK0 c ((s : ℂ) * ζ) (fctXi1 (fctWarpL1 h ε c)) *
        fctWarpA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((s : ℂ) * ζ)) volume 0 1) ∧
    (∀ ζ : ℂ, 0 < ζ.re → ζ.re < 7 / 16 →
      Integrable (fctCauchyIntegrand K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (7 / 16) ζ)) ∧
    (∀ ζ : ℂ, 7 / 16 ≤ ζ.re →
      Integrable (fctCauchyIntegrand K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) (3 / 8) ζ))

end FormalResearch.SignUncertainty
