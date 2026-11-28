module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicMoments
public import FormalResearch.SignUncertainty.CtBoasFarPhase
public import FormalResearch.SignUncertainty.CtDyadicRadius

/-!
# `ct:dyadic` (2): lower limit `ctLv0` and `CtDyadicRadiusStatement`

`constant_terms_lower.tex`, `ct:dyadic` (2) (one good Airy radius `R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]`
with `η(R) ≤ C c^{-1/3}`): proved unconditionally in `CtBandTop.ct_dyadic_radius_proved`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `L(ξ(-v₀)) = log(π² ξ(-v₀))`, `v₀ = c^{4/7}` (lower limit of the integral in `(ct:combined)`). -/
noncomputable def ctLv0 (c : ℝ) : ℝ := Real.log (π ^ 2 * hankelXi c (-(c ^ (4 / 7 : ℝ))))

/-- **`ct:dyadic` (2)** for the concrete `η = ctEta` and good radii `ctGoodRadius` (`c₁ > 0` is the constant of `ct:cfu`): a good radius `R`
in the window `[c₁²c^{2/3}, 4c₁²c^{2/3}]` with `η(R) ≤ C c^{-1/3}`, uniformly in `c ≥ c₀`, `ε = ±1` and the feasible `f` with `M[f] = 1`,
`ũ₁ > φ_c(a₁)`. -/
def CtDyadicRadiusStatement (c₁ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T < c * hankelXi c (FormalResearch.Special.airyZero 1) → 0 < ctGap ε c T →
      ∃ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧ ctGoodRadius R ∧
        ctEta c₁ ε c f R ≤ C * c ^ (-(1 / 3) : ℝ)

/-- `c^s ≥ M` for large `c`, `s > 0`. -/
lemma ev_rpow_ge {s : ℝ} (hs : 0 < s) (M : ℝ) : ∀ᶠ c : ℝ in atTop, M ≤ c ^ s :=
  (tendsto_rpow_atTop hs).eventually_ge_atTop M

/-- Large-`c` window-radius comparison `2 ≤ c^{4/7}` and `c^{4/7} + 1/2 ≤ c₁² c^{2/3}`. -/
lemma ev_hcR {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∀ᶠ c : ℝ in atTop, 2 ≤ c ^ (4 / 7 : ℝ) ∧ c ^ (4 / 7 : ℝ) + 1 / 2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by
  filter_upwards [ev_rpow_ge (by norm_num : (0 : ℝ) < 4 / 7) 2, ev_rpow_ge (by norm_num : (0 : ℝ) < 2 / 21) (5 / (4 * c₁ ^ 2)),
    eventually_gt_atTop (0 : ℝ)] with c h1 h2 hc
  refine ⟨h1, ?_⟩
  have e : c ^ (2 / 3 : ℝ) = c ^ (4 / 7 : ℝ) * c ^ (2 / 21 : ℝ) := by
    rw [← Real.rpow_add hc]; norm_num
  rw [e]
  have h3 : 5 / 4 ≤ c₁ ^ 2 * c ^ (2 / 21 : ℝ) := by
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith
  nlinarith

end FormalResearch.SignUncertainty
