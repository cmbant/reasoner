module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicMoments
public import FormalResearch.SignUncertainty.CtBoasFarPhase

/-!
# `ct:dyadic` (2) and (4): the statements, as a named input structure

`constant_terms_lower.tex`, `ct:dyadic` (2) (one good Airy radius `R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]` with `η(R) ≤ C c^{-1/3}`; since
PR 298 unconditional, from two Cauchy moments and the absolute second moment) and (4) (the combined dual identity at a good
radius, no `1_{E_un}` term):

`P_R(H) + g_vac/(2π) + ∫_{ξ ≥ ξ(-v₀)} w̃_R(ξ)[1 - 2 sin(cΦ_Ph(τ₀(L);L) - θ_ε(τ₀(L)))] dm(ξ) = O(c⁻¹η_R + c^{-4/3} log c)`,
`v₀ = c^{4/7}`.

`CtDyadicInputs c₁` states them about the concrete objects: `ctBudget R ε c f` (`= P_R(H) + g_vac/2π`), `ctTaper` (`w̃_R(ξ(L))`),
`hankelHL` (`dm = h dL`), `boasX` (`X = cΦ_Ph(τ₀) - θ_ε(τ₀)`, so `1 - 2 sin X = boasKernel`), and the lower limit
`ctLv0 c = L(ξ(-v₀)) = log(π² ξ(-c^{4/7}))` of the integral.  The paper's `η(R) = ∮_{|ũ|=R}|Ψ̃|/|e| + ∮_{|u|=R}|f_c|/|e|` (the
complex Airy envelope `e`) and the good-Airy-radius predicate (`ap:E2`, `gt:1.0p`) are **not yet defined in Lean**; they enter as the data
fields `eta` and `good` (a function and a predicate of `(ε, c, f, R)`), so `CtDyadicInputs` is a hypothesis about an arbitrary such
pair and is not the proved statement.  Fields: `radius` = `ct:dyadic` (2); `combined` = `ct:dyadic` (4).  Together with
`ct:boas` (`∫_{L ≥ L_min} ... ≥ -O(c^{-4/3} log c)`, via the fields of `BoasInputs`) they give the field `pass` of `CtLowerInputs`;
that combination is not done here.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `L(ξ(-v₀)) = log(π² ξ(-v₀))`, `v₀ = c^{4/7}` (lower limit of the integral in `(ct:combined)`). -/
noncomputable def ctLv0 (c : ℝ) : ℝ := Real.log (π ^ 2 * hankelXi c (-(c ^ (4 / 7 : ℝ))))

/-- **`ct:dyadic` (2) and (4)** about the concrete objects (see the module docstring); `c₁ > 0` is the constant of `ct:cfu`
(the window `[c₁²c^{2/3}, 4c₁²c^{2/3}]`), `eta`/`good` are the (not yet defined) `η(R)` and good-radius predicate. -/
structure CtDyadicInputs (c₁ : ℝ) where
  eta : ℝ → ℝ → (ℝ → ℝ) → ℝ → ℝ
  good : ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop
  /-- `ct:dyadic` (2): a good radius in the window with `η(R) ≤ C c^{-1/3}`. -/
  radius : ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 → 0 < ctGap ε c T →
      ∃ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧ good ε c f R ∧
        eta ε c f R ≤ C * c ^ (-(1 / 3) : ℝ)
  /-- `ct:dyadic` (4), `(ct:combined)`: at every good radius in the window. -/
  combined : ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 → 0 < ctGap ε c T →
      ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) → good ε c f R →
        |ctBudget R ε c f +
            ∫ L in Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L)| ≤
          C * (c⁻¹ * eta ε c f R + c ^ (-(4 / 3) : ℝ) * Real.log c)

end FormalResearch.SignUncertainty
