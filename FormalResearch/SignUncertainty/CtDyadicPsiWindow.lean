module

public import Mathlib
public import FormalResearch.SignUncertainty.CtLowerDefs
public import FormalResearch.SignUncertainty.CtCfuData
public import FormalResearch.SignUncertainty.CtKappaNeg

/-!
# `ct:cfu` (`ct:psi-def`): the phase shift `ψ_ε` is `C¹`, bounded and negative near `0⁻`

`constant_terms_lower.tex`, `ct:psi-def`/`ct:psi-coeffs` and `ct:taper-harnack` (c) ("`ψ_ε ∘ a ∈ C¹(0, Λ₂]` has bounded
derivative"): for the Lean `ctPsi ε` (built from the Lean `ctTau0`), there are `ρ, M > 0` with, for every `a ∈ (-ρ, 0)`,
`ctPsi ε a < 0` (from `ψ₀ = (12/π²)^{1/3} θ₁^ε < 0`, `ctKappa_neg`), `|ctPsi ε a| ≤ M`, and `ctPsi ε` differentiable at `a`
with `|ctPsi ε a'| ≤ M`.  This is `ctPsi_window`; it is the only property of `ψ_ε` the taper `v = -û∘ũ∘ξ` needs
(`û' = 1 + c^{-1}ψ' ≥ 1/2`, `v ≥ v'`).  **Proved**, unconditional (`ε = ±1`).
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies in
/-- **`ψ_ε` near `0⁻`** (`ct:psi-def`): `ρ, M > 0` such that on `(-ρ, 0)` the function `ctPsi ε` is negative, bounded by `M`,
and differentiable with derivative bounded by `M`. -/
lemma ctPsi_window {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ ρ M : ℝ, 0 < ρ ∧ 0 ≤ M ∧ ∀ a ∈ Ioo (-ρ) 0, ctPsi ε a < 0 ∧ |ctPsi ε a| ≤ M ∧
      HasDerivAt (ctPsi ε) (deriv (ctPsi ε) a) a ∧ |deriv (ctPsi ε) a| ≤ M := by
  obtain ⟨ρ, τ0, ψ, Ξ, hρ, hψ, hΞ, hmain, hψ0, -⟩ := CtCfu.cfu_psi_langer hε
  have hctPsi : ∀ a ∈ Ioo (-ρ) 0, ctPsi ε a = ψ a := by
    intro a ha
    obtain ⟨hpos, hphi, huniq, hψa, -⟩ := hmain a ha
    have hspec : 0 < ctTau0 a ∧
        edgePhi (hankelEdgeM (ctTau0 a)) (ctTau0 a) =
          (2 / 3) * (-a) ^ ((3 : ℝ) / 2) :=
      Classical.epsilon_spec (p := fun τ : ℝ => 0 < τ ∧
        edgePhi (hankelEdgeM τ) τ =
          (2 / 3) * (-a) ^ ((3 : ℝ) / 2)) ⟨τ0 a, hpos, hphi⟩
    have : ctTau0 a = τ0 a := huniq _ hspec.1 hspec.2
    unfold ctPsi
    rw [this, hψa]
  have h1 : ContDiffAt ℝ 1 ψ 0 := hψ.of_le (by simp)
  have hd : ContDiffAt ℝ 0 (deriv ψ) 0 := h1.derivWithin (m := 0) (by simp)
  have hψ00 : ψ 0 < 0 := by
    rw [hψ0]
    have h := ctKappa_neg hε
    unfold ctKappa at h
    have h2 : CtOuter.ctTheta1 ε < 0 := by
      by_contra hc
      push Not at hc
      have : 0 ≤ CtOuter.ctTheta1 ε / π ^ 2 := div_nonneg hc (by positivity)
      linarith
    exact mul_neg_of_pos_of_neg (by positivity) h2
  have hcont : ContinuousAt ψ 0 := h1.continuousAt
  have hev1 : ∀ᶠ a in 𝓝 (0 : ℝ), ψ a < 0 := hcont.eventually (gt_mem_nhds hψ00)
  have hev2 : ∀ᶠ a in 𝓝 (0 : ℝ), |ψ a| < |ψ 0| + 1 := by
    have : ∀ᶠ a in 𝓝 (0 : ℝ), |ψ a| < |ψ 0| + 1 :=
      (continuous_abs.continuousAt.comp hcont).eventually (gt_mem_nhds (by simp only [Function.comp_apply]; linarith))
    exact this
  have hev3 : ∀ᶠ a in 𝓝 (0 : ℝ), |deriv ψ a| < |deriv ψ 0| + 1 :=
    (continuous_abs.continuousAt.comp hd.continuousAt).eventually (gt_mem_nhds (by simp only [Function.comp_apply]; linarith))
  have hev4 : ∀ᶠ a in 𝓝 (0 : ℝ), ContDiffAt ℝ 1 ψ a := h1.eventually (by simp)
  obtain ⟨r, hr, hrr⟩ := Metric.eventually_nhds_iff.mp (hev1.and (hev2.and (hev3.and hev4)))
  refine ⟨min ρ r, max (|ψ 0| + 1) (|deriv ψ 0| + 1), lt_min hρ hr,
    (by linarith [abs_nonneg (ψ 0), le_max_left (|ψ 0| + 1) (|deriv ψ 0| + 1)]), ?_⟩
  intro a ha
  have haρ : a ∈ Ioo (-ρ) 0 :=
    ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ha.1, ha.2⟩
  have hdist : dist a 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ha.1, min_le_right ρ r], by linarith [ha.2, lt_min hρ hr]⟩
  obtain ⟨hn, hb, hdb, hcd⟩ := hrr hdist
  have hopen : Ioo (-ρ) 0 ∈ 𝓝 a := Ioo_mem_nhds haρ.1 haρ.2
  have heq : ctPsi ε =ᶠ[𝓝 a] ψ := by
    filter_upwards [hopen] with b hb using hctPsi b hb
  have hdiff : HasDerivAt ψ (deriv ψ a) a := (hcd.differentiableAt (by simp)).hasDerivAt
  have hdiff' : HasDerivAt (ctPsi ε) (deriv ψ a) a := hdiff.congr_of_eventuallyEq heq
  have hderiv : deriv (ctPsi ε) a = deriv ψ a := heq.deriv_eq
  rw [hctPsi a haρ, hderiv]
  refine ⟨hn, ?_, hderiv ▸ hdiff', ?_⟩
  · exact hb.le.trans (le_max_left _ _)
  · exact hdb.le.trans (le_max_right _ _)

/-- info: 'FormalResearch.SignUncertainty.ctPsi_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctPsi_window

end FormalResearch.SignUncertainty
