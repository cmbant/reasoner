module

public import Mathlib
public import FormalResearch.SignUncertainty.CtLower
public import FormalResearch.SignUncertainty.CtBoasEventual
public import FormalResearch.SignUncertainty.CtCombinedTop
public import FormalResearch.SignUncertainty.CtTransBand
public import FormalResearch.SignUncertainty.CtRoscAssembly
public import FormalResearch.SignUncertainty.CtRoscBookProof
public import FormalResearch.SignUncertainty.CtWindowAssembly

/-!
# `thm:ct-lower` unconditional

Combines all five pieces of `ct:dyadic` (4) (`ct_combined_rosc`, `ct_combined_trunc`,
`ct_combined_window`, `ct_combined_outer`, `ct_combined_trans`) via `ct_dyadicCombined_of_bounds`
to prove `ct_combined`, and combines `ct_combined` with `ct_boas_concrete` (`CtBoasEventual`)
via `ct_lower_of_boas` to prove `ct_lower : CtLowerStatement` unconditionally.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty

/-- **`ct:dyadic` (4), `(ct:combined)` (`constant_terms_lower.tex`)**: for every sufficiently
small `c₁ > 0`, `CtDyadicCombinedStatement c₁` holds unconditionally. -/
theorem ct_combined :
    ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtDyadicCombinedStatement c₁ := by
  obtain ⟨γ₀, hγ₀, H⟩ := ct_dyadicCombined_of_bounds
  obtain ⟨g₁, hg₁, h₁⟩ := ct_combined_rosc
  obtain ⟨g₂, hg₂, h₂⟩ := ct_combined_trunc
  obtain ⟨g₃, hg₃, h₃⟩ := ct_combined_window
  obtain ⟨g₄, hg₄, h₄⟩ := ct_combined_outer
  obtain ⟨g₅, hg₅, h₅⟩ := ct_combined_trans
  refine ⟨min γ₀ (min g₁ (min g₂ (min g₃ (min g₄ (min g₅ ctChartC1))))),
    lt_min hγ₀ (lt_min hg₁ (lt_min hg₂ (lt_min hg₃ (lt_min hg₄ (lt_min hg₅ ctChartC1_pos))))),
    fun c₁ hc₁ hle => ?_⟩
  exact H c₁ hc₁ (hle.trans (min_le_left _ _))
    (h₁ c₁ hc₁ (hle.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (ct_rosc_book hc₁ (hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
          (min_le_right _ _)))))))))
    (h₂ c₁ hc₁ (hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
    (h₃ c₁ hc₁ (hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))))
    (h₄ c₁ hc₁ (hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))
    (h₅ c₁ hc₁ (hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))))))

/-- **`thm:ct-lower` (`eq:ct-lower`, left half, `constant_terms_lower.tex`)**:
for every `c ≥ c₀` and `ε = ±1`, every feasible Hankel threshold satisfies
`Δ₅^ε(c) - C c⁻¹ log c ≤ T`. Unconditional. -/
theorem ct_lower : CtLowerStatement :=
  ct_lower_of_boas ct_combined ct_boas_concrete

/-- info: 'FormalResearch.SignUncertainty.ct_combined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_combined

/-- info: 'FormalResearch.SignUncertainty.ct_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_lower

end FormalResearch.SignUncertainty
