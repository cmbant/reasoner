module

public import Mathlib
public import FormalResearch.SignUncertainty.CtLower
public import FormalResearch.SignUncertainty.CtBoasEventual
public import FormalResearch.SignUncertainty.CtCombinedTop
public import FormalResearch.SignUncertainty.CtTransBand
public import FormalResearch.SignUncertainty.CtRoscAssembly
public import FormalResearch.SignUncertainty.CtRoscBookProof
public import FormalResearch.SignUncertainty.CtWindowAssembly
public import FormalResearch.SignUncertainty.CtLowerLogFreeSkeleton
public import FormalResearch.SignUncertainty.CtWindowSigned
public import FormalResearch.SignUncertainty.CtBoasExactAssembly

/-!
# `thm:ct-lower` unconditional (log-free)

Combines the five log-free pieces of `ct:dyadic` (4) (`ct_combined_rosc_sharp`,
`ct_combined_trunc_sharp`, `window_signed_proved`, `ct_combined_outer_sharp`,
`ct_combined_trans_sharp`) via `ct_dyadicCombined_sharp_of_bounds` to prove
`ct_combined_sharp`, and combines `ct_combined_sharp` with `boas_sharp_proved`
(`CtBoasExactAssembly`) via `ct_lower_of_boas_logfree` to prove
`ct_lower : CtLowerStatement` (`Δ₅^ε(c) - C c⁻¹ ≤ T`) unconditionally.
The older `c⁻¹ log c` form is kept as the one-line corollary `ct_lower_log` (`ct_combined`
retaining the older combined bound).
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

/-- **Log-free `ct:dyadic` (4), `(ct:combined)` (`constant_terms_lower.tex`)**: for every
sufficiently small `c₁ > 0`, `CtDyadicCombinedSharpStatement c₁` holds unconditionally. -/
theorem ct_combined_sharp :
    ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtDyadicCombinedSharpStatement c₁ := by
  obtain ⟨γ_d, hγ_d, hd⟩ := ct_dyadicCombined_sharp_of_bounds
  obtain ⟨γ_r, hγ_r, hr⟩ := ct_combined_rosc_sharp
  obtain ⟨γ_t, hγ_t, ht⟩ := ct_combined_trunc_sharp
  obtain ⟨γ_w, hγ_w, hw⟩ := window_signed_proved
  obtain ⟨γ_o, hγ_o, ho⟩ := ct_combined_outer_sharp
  obtain ⟨γ_tr, hγ_tr, htr⟩ := ct_combined_trans_sharp
  refine ⟨min γ_d (min γ_r (min γ_t (min γ_w (min γ_o (min γ_tr ctChartC1))))),
    lt_min hγ_d (lt_min hγ_r (lt_min hγ_t (lt_min hγ_w (lt_min hγ_o (lt_min hγ_tr ctChartC1_pos))))),
    fun c₁ hc₁ hle => ?_⟩
  exact hd c₁ hc₁ (hle.trans (min_le_left _ _))
    (hr c₁ hc₁ (hle.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (ct_rosc_book hc₁ (hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
          (min_le_right _ _)))))))))
    (ht c₁ hc₁ (hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
    (hw c₁ hc₁ (hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))))
    (ho c₁ hc₁ (hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))
    (htr c₁ hc₁ (hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))))))

/-- **`thm:ct-lower` (`eq:ct-lower`, left half, `constant_terms_lower.tex`)**:
for every `c ≥ c₀` and `ε = ±1`, every feasible Hankel threshold satisfies
`Δ₅^ε(c) - C c⁻¹ ≤ T`. Unconditional. -/
theorem ct_lower : CtLowerStatement :=
  ct_lower_of_boas_logfree ct_combined_sharp boas_sharp_proved

/-- One-line corollary retaining the older `c⁻¹ log c` form. -/
theorem ct_lower_log : CtLowerLogStatement :=
  ct_lower_log_of_sharp ct_lower

/-- info: 'FormalResearch.SignUncertainty.ct_combined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_combined

/-- info: 'FormalResearch.SignUncertainty.ct_combined_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_combined_sharp

/-- info: 'FormalResearch.SignUncertainty.ct_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_lower

/-- info: 'FormalResearch.SignUncertainty.ct_lower_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_lower_log

end FormalResearch.SignUncertainty
