/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctDcomp
public import FormalResearch.SignUncertainty.FctPhiKillCore
public import FormalResearch.SignUncertainty.FctMainHankelDefs
public import FormalResearch.CohnElkies.MellinKernel

/-!
# The complex zero functional `I_ε(L₁, α)` and the zero pair of `fct:warp-asymp` (1)

Paper I (`constant_terms_five.tex`), Section FCT.3 (`fct:s3-warp`, `(fct:A-Psi-def)`) and Proposition FCT.5 (`fct:warp-asymp`) (1).

**Definitions** (all from existing Lean objects).  With `H₀ = H_*`, `K₄ ≥ 1`, `τ₁ = c^{-1/4}`, `a = c^{-1/12}`:

* `fctXi1 L₁ = e^{L₁}/π²` (`ξ₁`);
* `fctWarpA K4 ε c L₁ α t = (g_tan t + L₁ φ_kill(t; a)) D_{τ₁}(t) (H_*/G_ε)(t)` (`A_ε`, `(fct:A-Psi-def)`), with `g_tan = stripG`,
  `φ_kill = phiKill`, `D_{τ₁} = fctDcompAt` (`fct:comp-D`, parameter `α` free) and `H_*/G_ε = ctHG`;
* `fctWarpI K4 ε c L₁ α = ∫₀^{i∞} K₀(t, ξ₁) A_ε(t) dt = i ∫₀^∞ K₀(iτ, ξ₁) A_ε(iτ) dτ` (`I_ε(L₁, α)`), with `K₀ = mellinK0`.

**Integrability.**  `I_ε` is a Bochner integral, which is `0` for a non-integrable integrand.  The paper's integrand is `O(τ^{-1/2})` at `0` and
`O(e^{-π τ}poly(τ))` at `∞` (`|H₀(iτ)| = O(e^{-πτ})`), hence integrable; this is not proved in Lean, so it is part of the statement of the zero:
`FctWarpZero` is `IntegrableOn` **and** `fctWarpI = 0`, so that the zero condition cannot hold through the junk value.

**The zero pair.**  `FctWarpSolveStmt K4` is `fct:warp-asymp` (1): for `c ≥ c₀` and `ε = ±1` there is a unique `(L₁, α)` in the class
`L₁ > 0`, `|T₁ − Δ₅^ε(c)| ≤ C c⁻¹` (`T₁ = (c/π²) e^{L₁}`), `|α| ≤ C c^{-2/3}` with `FctWarpZero`.  `fctWarpPair` is the pair chosen from it
(`Classical.epsilon`; the junk value for `c < c₀` is never used), `fctWarpT1`, `fctWarpAlpha` the data `T₁`, `α`; `fctWarpZero_of_solve` recovers
the size statement `FctWarpZeroStmt`, which the rest of `fct:main-hankel` consumes.  The exact IBP identity `(fct:exact-ibp)` is not part of this file.

Class: definitions; `FctWarpSolveStmt` is a named input (open).
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

/-- `ξ₁ = e^{L₁}/π²` (`fct:s3-warp`). -/
noncomputable def fctXi1 (L1 : ℝ) : ℝ := Real.exp L1 / π ^ 2

/-- `A_ε(t) = (g_tan(t) + L₁ φ_kill(t; a)) D_{τ₁}(t) H_*(t)/G_ε(t)` (`(fct:A-Psi-def)`), `a = c^{-1/12}`, `H₀ = H_*`; the compensator `D_{τ₁}`
is the one of `fct:comp-D` for the parameter `α`.  (At `t = 0` Lean's `ctHG` is a junk value; the paper's `A_ε` is only used on the open strip and its
imaginary axis `t = iτ`, `τ > 0`.) -/
noncomputable def fctWarpA (K4 ε c L1 α : ℝ) (t : ℂ) : ℂ :=
  (stripG t + (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t) * fctDcompAt K4 c α t * ctHG ε t

/-- The integrand `τ ↦ K₀(iτ, ξ₁) A_ε(iτ)` of `I_ε(L₁, α) = i ∫₀^∞ K₀(iτ, ξ₁) A_ε(iτ) dτ`. -/
noncomputable def fctWarpIntegrand (K4 ε c L1 α : ℝ) (τ : ℝ) : ℂ :=
  mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) * fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)

/-- **The complex zero functional** `I_ε(L₁, α) := ∫₀^{i∞} K₀(t, ξ₁) A_ε(t) dt` (`fct:s3-warp`), along the imaginary axis `t = iτ`,
`dt = i dτ`.  Meaningful where `fctWarpIntegrand` is integrable on `(0, ∞)` (`FctWarpZero` requires it). -/
noncomputable def fctWarpI (K4 ε c L1 α : ℝ) : ℂ :=
  Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrand K4 ε c L1 α τ

/-- `I_ε(L₁, α) = 0` with the integral convergent (no junk-value zero). -/
def FctWarpZero (K4 ε c L1 α : ℝ) : Prop :=
  IntegrableOn (fctWarpIntegrand K4 ε c L1 α) (Ioi (0 : ℝ)) ∧ fctWarpI K4 ε c L1 α = 0

/-- The uniqueness class of `fct:warp-asymp` (1): `L₁ > 0` (the domain of `I_ε`), `|T₁ − Δ₅^ε(c)| ≤ C c⁻¹` with `T₁ = (c/π²) e^{L₁}`,
`|α| ≤ C c^{-2/3}`. -/
def FctWarpClass (C ε c L1 α : ℝ) : Prop :=
  0 < L1 ∧ |c / π ^ 2 * Real.exp L1 - ctDelta5 ε c| ≤ C * c⁻¹ ∧ |α| ≤ C * c ^ (-(2 / 3 : ℝ))

/-- **`fct:warp-asymp` (1)** (Proposition FCT.5, `constant_terms_five.tex`; named input): for `K₄` fixed there are `C, c₀` such that for `ε = ±1`
and `c ≥ c₀` there is exactly one pair `(L₁, α)` with `L₁ > 0`, `|T₁ − Δ₅^ε(c)| ≤ C c⁻¹`, `|α| ≤ C c^{-2/3}` and `I_ε(L₁, α) = 0`
(`FctWarpZero`).  The IBP identity `(fct:exact-ibp)` is not stated here. -/
def FctWarpSolveStmt (K4 : ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
    ∃! p : ℝ × ℝ, FctWarpClass C ε c p.1 p.2 ∧ FctWarpZero K4 ε c p.1 p.2

/-- The zero pair `(L₁, α)(ε, c)` chosen from `FctWarpSolveStmt` (the unique one for `c ≥ c₀`; a junk value otherwise, never used). -/
noncomputable def fctWarpPair {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c : ℝ) : ℝ × ℝ :=
  Classical.epsilon fun p : ℝ × ℝ => FctWarpClass h.choose ε c p.1 p.2 ∧ FctWarpZero K4 ε c p.1 p.2

/-- `L₁(c)` of the zero pair. -/
noncomputable def fctWarpL1 {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c : ℝ) : ℝ := (fctWarpPair h ε c).1

/-- `T₁ = (c/π²) e^{L₁}` of the zero pair (`fct:warp-asymp` (1)). -/
noncomputable def fctWarpT1 {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c : ℝ) : ℝ :=
  c / π ^ 2 * Real.exp (fctWarpL1 h ε c)

/-- `α(c)` of the zero pair. -/
noncomputable def fctWarpAlpha {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c : ℝ) : ℝ := (fctWarpPair h ε c).2

/-- For `c ≥ c₀` the chosen pair is in the class and is a zero (with convergent integral). -/
theorem fctWarpPair_spec {K4 : ℝ} (h : FctWarpSolveStmt K4) {ε c : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : h.choose_spec.choose ≤ c) :
    FctWarpClass h.choose ε c (fctWarpPair h ε c).1 (fctWarpPair h ε c).2 ∧
      FctWarpZero K4 ε c (fctWarpPair h ε c).1 (fctWarpPair h ε c).2 := by
  obtain ⟨p, hp, -⟩ := h.choose_spec.choose_spec ε c hε hc
  exact Classical.epsilon_spec (p := fun p : ℝ × ℝ => FctWarpClass h.choose ε c p.1 p.2 ∧ FctWarpZero K4 ε c p.1 p.2) ⟨p, hp⟩

/-- Uniqueness: any pair of the class with `I_ε = 0` is the chosen one (`c ≥ c₀`). -/
theorem fctWarpPair_unique {K4 : ℝ} (h : FctWarpSolveStmt K4) {ε c : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : h.choose_spec.choose ≤ c)
    {L1 α : ℝ} (hcl : FctWarpClass h.choose ε c L1 α) (hz : FctWarpZero K4 ε c L1 α) :
    fctWarpPair h ε c = (L1, α) := by
  obtain ⟨p, -, hu⟩ := h.choose_spec.choose_spec ε c hε hc
  have h1 := hu _ (fctWarpPair_spec h hε hc)
  have h2 := hu (L1, α) ⟨hcl, hz⟩
  exact h1.trans h2.symm

/-- The size statement `FctWarpZeroStmt` (`|T₁ − Δ₅| ≤ C c⁻¹`, `|α| ≤ C c^{-2/3}`) for the chosen zero pair: a consequence of `fct:warp-asymp` (1). -/
theorem fctWarpZero_of_solve {K4 : ℝ} (h : FctWarpSolveStmt K4) : FctWarpZeroStmt (fctWarpT1 h) (fctWarpAlpha h) :=
  ⟨h.choose, h.choose_spec.choose, fun _ _ hε hc =>
    ⟨(fctWarpPair_spec h hε hc).1.2.1, (fctWarpPair_spec h hε hc).1.2.2⟩⟩

/-- The pair is a zero of `I_ε`. -/
theorem fctWarpI_pair {K4 : ℝ} (h : FctWarpSolveStmt K4) {ε c : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : h.choose_spec.choose ≤ c) :
    fctWarpI K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) = 0 :=
  (fctWarpPair_spec h hε hc).2.2

/-- `physL1` of `T₁ = (c/π²) e^{L₁}` is `L₁` (`c > 0`). -/
theorem physL1_fctWarpT1 {K4 : ℝ} (h : FctWarpSolveStmt K4) {ε c : ℝ} (hc : 0 < c) :
    Real.log (π ^ 2 * fctWarpT1 h ε c / c) = fctWarpL1 h ε c := by
  unfold fctWarpT1
  have : π ^ 2 * (c / π ^ 2 * Real.exp (fctWarpL1 h ε c)) / c = Real.exp (fctWarpL1 h ε c) := by
    field_simp [Real.pi_pos.ne', hc.ne']
  rw [this, Real.log_exp]

/-- info: 'FormalResearch.SignUncertainty.fctWarpZero_of_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpZero_of_solve

/-- info: 'FormalResearch.SignUncertainty.fctWarpPair_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpPair_unique

/-- info: 'FormalResearch.SignUncertainty.fctWarpI_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpI_pair

end FormalResearch.SignUncertainty
