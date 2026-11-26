module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicMoments
public import FormalResearch.SignUncertainty.CtBoasFarPhase
public import FormalResearch.SignUncertainty.CtDyadicRadius

/-!
# `ct:dyadic` (2) and (4): the statements, as a named input structure

`constant_terms_lower.tex`, `ct:dyadic` (2) (one good Airy radius `R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]` with `η(R) ≤ C c^{-1/3}`; since
PR 298 unconditional, from two Cauchy moments and the absolute second moment) and (4) (the combined dual identity at a good
radius, no `1_{E_un}` term):

`P_R(H) + g_vac/(2π) + ∫_{ξ ≥ ξ(-v₀)} w̃_R(ξ)[1 - 2 sin(cΦ_Ph(τ₀(L);L) - θ_ε(τ₀(L)))] dm(ξ) = O(c⁻¹η_R + c^{-4/3} log c)`,
`v₀ = c^{4/7}`.

Both are about the concrete objects: `ctBudget R ε c f` (`= P_R(H) + g_vac/2π`), `ctTaper` (`w̃_R(ξ(L))`), `hankelHL` (`dm = h dL`),
`boasX` (`X = cΦ_Ph(τ₀) - θ_ε(τ₀)`, so `1 - 2 sin X = boasKernel`), the lower limit `ctLv0 c = L(ξ(-v₀)) = log(π² ξ(-c^{4/7}))`, and,
since `CtDyadicEta`, the paper's `η(R)` (`ctEta`: the two circle integrals with the complex Airy envelope `airyEnv` and the complex
chart `ctPhiC`) and good Airy radii (`ctGoodRadius`, `ap:E2`).

* `CtDyadicRadiusStatement c₁` is `ct:dyadic` (2).  It is **proved** from the three named hypotheses `chart`, `gregData`, `etaTransfer`
  (`CtDyadicInputs.radius`, `ct_dyadic_radius` in `CtDyadicRadius`): the complex chart of `ct:cfu`, the boundary inputs of the Cauchy-moment
  argument (the part of `ct:dyadic` (1) that (2) uses), and the unfolding of the two circle integrals of `η`.
* `CtDyadicInputs.combined` is `ct:dyadic` (4), not proved.

Together with `ct:boas` (`∫_{L ≥ L_min} ... ≥ -O(c^{-4/3} log c)`, via the fields of `BoasInputs`) they give the field `pass` of
`CtLowerInputs`; that combination is not done here.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `L(ξ(-v₀)) = log(π² ξ(-v₀))`, `v₀ = c^{4/7}` (lower limit of the integral in `(ct:combined)`). -/
noncomputable def ctLv0 (c : ℝ) : ℝ := Real.log (π ^ 2 * hankelXi c (-(c ^ (4 / 7 : ℝ))))

/-- **`ct:dyadic` (2)** for the concrete `η = ctEta` and good radii `ctGoodRadius` (`c₁ > 0` is the constant of `ct:cfu`): a good radius `R`
in the window `[c₁²c^{2/3}, 4c₁²c^{2/3}]` with `η(R) ≤ C c^{-1/3}`, uniformly in `c ≥ c₀`, `ε = ±1` and the feasible `f` with `M[f] = 1`,
`ũ₁ > φ_c(a₁)`. -/
def CtDyadicRadiusStatement (c₁ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 → 0 < ctGap ε c T →
      ∃ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧ ctGoodRadius R ∧
        ctEta c₁ ε c f R ≤ C * c ^ (-(1 / 3) : ℝ)

/-- **Inputs of `ct:dyadic` (2), (4)**: the three named hypotheses behind (2) (see `CtDyadicRadius`: `CtChartComplex`, `CtGRegData`,
`CtEtaTransfer`) and `ct:dyadic` (4) (`(ct:combined)` at every good radius in the window, about `ctBudget`, `ctTaper`, `hankelHL`,
`boasKernel`, `ctEta`). -/
structure CtDyadicInputs (c₁ : ℝ) : Prop where
  chart : CtChartComplex c₁
  gregData : CtGRegData c₁
  etaTransfer : CtEtaTransfer c₁
  /-- `ct:dyadic` (4), `(ct:combined)`: at every good radius in the window. -/
  combined : ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 → 0 < ctGap ε c T →
      ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) → ctGoodRadius R →
        |ctBudget R ε c f +
            ∫ L in Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L)| ≤
          C * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ) * Real.log c)

/-- **`ct:dyadic` (2) from the inputs** (`c₁ > 0`). -/
theorem CtDyadicInputs.radius {c₁ : ℝ} (hc₁ : 0 < c₁) (I : CtDyadicInputs c₁) : CtDyadicRadiusStatement c₁ :=
  ct_dyadic_radius hc₁ I.chart I.gregData I.etaTransfer

end FormalResearch.SignUncertainty
