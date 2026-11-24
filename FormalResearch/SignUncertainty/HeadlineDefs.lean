module

public import FormalResearch.SignUncertainty.Radii

/-!
# Statements of the one-level lower thresholds and of the shell reduction

`HbThresholdsLower` (`thm:hb-thresholds` lower half) and `ShellReduction` (`thm:ce-shell-reduction`), split out of
`Headlines.lean` so that their proofs (`HankelThresholds.lean`, `CEShellReduction.lean`) can precede it.
-/

@[expose] public section

open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `thm:hb-thresholds` at `(P, Q) = (1, 0)`, lower half (`u1cl:multilevel`, Theorem L.2): every
feasible threshold, for either eigenvalue, is at least `c/π² + A c^{1/3} - C` once `c` is large. -/
def HbThresholdsLower : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ (T : ℝ) (f : ℝ → ℝ),
    IsHankelFeasible c ε T f → c / π ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) - C ≤ T

/-- `thm:ce-shell-reduction` (Theorem HB--CE.L) for `D`, bounded offsets: every admissible radius
satisfies `R²/2 ≥ d/(2π²) - (t_m/β₁)(d/2)^{1/3} - O(1)`, uniformly over the allowed offsets. -/
def ShellReduction (D : ShellHBData) : Prop :=
  ∀ R_off : ℝ, 0 ≤ R_off → ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d →
    ∀ r : ℝ → ℕ → ℝ, (∀ t d', |r t d'| ≤ R_off) →
      ∀ R ∈ ceShellRadiusSet D r d,
        (d : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) - C ≤ R ^ 2 / 2

end FormalResearch.SignUncertainty
