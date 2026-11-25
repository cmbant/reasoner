module

public import FormalResearch.SignUncertainty.HankelThresholds
public import FormalResearch.SignUncertainty.HbUpperM1

/-!
# `thm:hankel-one-two` (`u1cl:main`, Corollary L.1, one level): `T_c^ε = c/π² + A c^{1/3} + O(1)`

Source: `CFT/sign_uncertainty/paper/u1c_o1_lower.tex`, Corollary L.1 (`u1cl:main` = `thm:hankel-one-two`), one-level part
(`N = Ai` in `thm:hb-thresholds`, `A = |a₁|/β₁` = `airyOrderCoeff`).  The two-level part (Clark angle) is not formalised.

The statement is the two-sided bound for the Hankel threshold `hankelT ε c`, the infimum of feasible thresholds, for both
eigenvalues `ε = ±1` and all large real `c`.  It is assembled from the two proved halves `hb_thresholds_lower`
(`HankelThresholds.lean`) and `hbThresholdsUpper` (`HbUpperM1.lean`) by `hankelT_sub_model_le` (`Headlines.lean`).

Status: proved, unconditional.
-/

@[expose] public section

open scoped Real

namespace FormalResearch.SignUncertainty

/-- **`thm:hankel-one-two`, one level** (Corollary L.1 of `u1c_o1_lower.tex`; proved): there are `C, c₀` with
`|T_c^ε - (c/π² + A c^{1/3})| ≤ C` for every `c ≥ c₀` and `ε = ±1`, where `A = airyOrderCoeff = |a₁|/β₁` and
`T_c^ε = hankelT ε c` is the infimum of the feasible thresholds. -/
theorem hankel_one_two :
    ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      |hankelT ε c - (c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ))| ≤ C := by
  obtain ⟨C₁, c₁, hlow⟩ := hb_thresholds_lower
  obtain ⟨C₂, c₂, hup⟩ := hbThresholdsUpper
  refine ⟨max C₁ C₂, max c₁ c₂, fun c hc ε hε => ?_⟩
  exact hankelT_sub_model_le (hlow c ((le_max_left _ _).trans hc) ε hε)
    (hup c ((le_max_right _ _).trans hc) ε hε)

/-- info: 'FormalResearch.SignUncertainty.hankel_one_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_one_two

end FormalResearch.SignUncertainty
