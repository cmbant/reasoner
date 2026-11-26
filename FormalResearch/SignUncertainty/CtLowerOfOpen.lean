module

public import Mathlib
public import FormalResearch.SignUncertainty.CtTransBand
public import FormalResearch.SignUncertainty.CtRoscBookProof

/-!
# `thm:ct-lower` from `window` and the Airy comparison

`ct_lower` with `CtLowerInputs.dyadic` replaced by `CtCombinedOpen` (the one step `window`) and `CtRoscInputs`.  The steps `trunc`, `outer`, `trans`, `rosc` are `ct_combined_trunc`,
`ct_combined_outer`, `ct_combined_trans`, `ct_combined_rosc`; the Hankel bookkeeping `CtRoscBook` of `rosc` is proved (`ct_rosc_book`), so the only named input of `rosc` left is
the pure-Airy comparison `AiryRplusComparison`.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty

/-- **The named input of `rosc`** (`(ct:rosc)`, `CtRoscAssembly`): the pure-Airy comparison `AiryRplusComparison` (DLMF 9.7.5/9.7.9 on the upper
semicircle).  (The Hankel bookkeeping `CtRoscBook` is proved, `ct_rosc_book`.) -/
structure CtRoscInputs : Prop where
  airy : AiryRplusComparison

/-- **`thm:ct-lower` from `window` and the input of `rosc`**: `ct_lower` with `CtLowerInputs.dyadic` replaced by `CtCombinedOpen` (`window`) and
`CtRoscInputs`; the steps `trunc`, `outer`, `trans`, `rosc` are `ct_combined_trunc`, `ct_combined_outer`, `ct_combined_trans`, `ct_combined_rosc`. -/
theorem ct_lower_of_open
    (P : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtCombinedOpen c₁) (Q : CtRoscInputs) :
    CtLowerStatement := by
  obtain ⟨c₁₀, hc₁₀, hP⟩ := P
  obtain ⟨g₁, hg₁, hT⟩ := ct_combined_trunc
  obtain ⟨g₂, hg₂, hO⟩ := ct_combined_outer
  obtain ⟨g₃, hg₃, hR⟩ := ct_combined_trans
  obtain ⟨g₄, hg₄, hRo⟩ := ct_combined_rosc Q.airy
  refine ct_lower_of_pieces ⟨min c₁₀ (min g₁ (min g₂ (min g₃ (min g₄ ctChartC1)))),
    lt_min hc₁₀ (lt_min hg₁ (lt_min hg₂ (lt_min hg₃ (lt_min hg₄ ctChartC1_pos)))), fun c₁ h1 h2 => ?_⟩
  have a1 : c₁ ≤ c₁₀ := h2.trans (min_le_left _ _)
  have a2 : c₁ ≤ g₁ := h2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have a3 : c₁ ≤ g₂ := h2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have a4 : c₁ ≤ g₃ :=
    h2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have a5 : c₁ ≤ g₄ := h2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))))
  have a6 : c₁ ≤ ctChartC1 := h2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))))
  exact ⟨hRo c₁ h1 a5 (ct_rosc_book h1 a6), hT c₁ h1 a2, (hP c₁ h1 a1).window, hO c₁ h1 a3, hR c₁ h1 a4⟩

/-- info: 'FormalResearch.SignUncertainty.ct_lower_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_lower_of_open

end FormalResearch.SignUncertainty
