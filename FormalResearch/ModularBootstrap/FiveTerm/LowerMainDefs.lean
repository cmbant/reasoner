module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerPhaseChart
public import FormalResearch.ModularBootstrap.FiveTerm.LowerCorL
public import FormalResearch.ModularBootstrap.FixedWeightTip.PropositionP
public import FormalResearch.Special.AiryEnvelope

/-!
# Shared definitions for `cts:lower-main` (`LowerMain` and `LowerGood*`)

Extracted from `LowerMain.lean` so that `LowerGoodCircle`, `LowerGoodArea`,
`LowerGoodWtilde`, and `LowerGoodMain` can be imported before `LowerMain` and
`LowerMainVirasoro` without an import cycle.
-/

@[expose] public section

open Real Complex Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.FixedWeightTip

noncomputable section

/-- `R_max = 4 c_1² c^{2/3}`, the radius of the shifted Airy chart. -/
def lowerRmax (c1 c : ℝ) : ℝ := 4 * c1 ^ 2 * c ^ (2 / 3 : ℝ)

/-- `R_min = c_1² c^{2/3}`, the lower end of the range of macroscopic good radii. -/
def lowerRmin (c1 c : ℝ) : ℝ := c1 ^ 2 * c ^ (2 / 3 : ℝ)

/-- The Hardy taper `W_6(u) = (1 - (u/R)^{12})²`. -/
def lowerW6 (R u : ℝ) : ℝ := (1 - (u / R) ^ 12) ^ 2

/-- The complementary taper `w_R(v) = 1 - W_6(-v)`. -/
def lowerWR (R v : ℝ) : ℝ := 1 - lowerW6 R (-v)

/-- `f(u) = Ψ̃(φ_c(u)) φ_c'(u)`, the density transported by the shifted chart `φ_c`. -/
noncomputable def lowerF (prob : FixedWeightProblem) (phi : ℝ → ℂ → ℂ) (c : ℝ) (g : ℝ → ℝ) (u : ℂ) : ℂ :=
  psiTilde prob c g (phi c u) * deriv (phi c) u

/-- `H(u) = W_6(u) f(u)` on the real axis (real part). -/
noncomputable def lowerH (prob : FixedWeightProblem) (phi : ℝ → ℂ → ℂ) (c : ℝ) (g : ℝ → ℝ) (R x : ℝ) : ℝ :=
  lowerW6 R x * (lowerF prob phi c g (x : ℂ)).re

/-- The Airy node sum `P_R(F) = Σ_{n ≤ N} F(a_n)/Ai'(a_n)²` over the `N` zeros inside the circle. -/
noncomputable def lowerPNodes (N : ℕ) (F : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, F (airyZero n) / airyAi' (airyZero n) ^ 2

/-- The circle bound `η(R) = ∮_{|ũ|=R} |Ψ̃|/|e| |dũ| + ∮_{|u|=R} |f|/|e| |du|`. -/
noncomputable def lowerEta (prob : FixedWeightProblem) (phi : ℝ → ℂ → ℂ) (c : ℝ) (g : ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π),
    R * (‖psiTilde prob c g (circleMap 0 R θ)‖ + ‖lowerF prob phi c g (circleMap 0 R θ)‖) /
      airyEnv (circleMap 0 R θ)

/-- `R` is a good Airy radius with `N` zeros inside: the lower bound `‖Ai‖² ≥ (1+R)^{-1/2} e/(25π)` holds
on the circle `|u| = R` (`AiryGoodCircles`) and `a_n` lies inside exactly for `n ≤ N`. -/
def LowerGoodCircle (N : ℕ) (R : ℝ) : Prop :=
  (∀ u : ℂ, ‖u‖ = R → 1 / (25 * π) * (1 + R) ^ (-(1 / 2 : ℝ)) * airyEnv u ≤ ‖airyAiC u‖ ^ 2) ∧
  ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ |airyZero n| < R)

open Classical in
/-- **`cts:cauchy-dual` (1), the part consumed by `cts:lower-main`**: the shifted Airy chart `φ_c = û⁻¹` (data `phi`, `uhat`)
is holomorphic on a neighbourhood of `|u| ≤ R_max`, real on the real axis, `φ_c' = 1 + O(c⁻¹)`,
`|φ_c(u) - u| ≤ C c^{-1/3}`, `û(φ_c(x)) = x`, and (`cts:phic-exp`)
`φ_c(a_1) = a_1 - (c_0/c_*) c^{-1/3} - γ_0 a_1 c^{-1} + O(c^{-4/3})`. -/
def LowerChart (c0 γ0 : ℝ) (c1 : ℝ) (phi : ℝ → ℂ → ℂ) (uhat : ℝ → ℝ → ℝ) : Prop :=
  ∃ cc C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, cc ≤ c →
    (∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ)) ∧
    (∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0) ∧
    (∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ C * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ C * c ^ (-1 : ℝ)) ∧
    (∀ x : ℝ, |x| ≤ lowerRmax c1 c → uhat c (phi c (x : ℂ)).re = x) ∧
    |(phi c (airyZero 1 : ℂ)).re -
        (airyZero 1 - c0 / cStar * c ^ (-(1 / 3 : ℝ)) - γ0 * airyZero 1 * c ^ (-1 : ℝ))| ≤
      C * c ^ (-(4 / 3 : ℝ))

/-- Hypothesis of `cts:rosc-uncond`: `ũ_1(g) > φ_c(a_1)`. -/
def LowerViolator (phi : ℝ → ℂ → ℂ) (c T : ℝ) : Prop :=
  (phi c (airyZero 1 : ℂ)).re < virasoroUT c T

/-- The range of macroscopic good radii. -/
def LowerRadiusRange (c1 c R : ℝ) : Prop := lowerRmin c1 c ≤ R ∧ R ≤ lowerRmax c1 c

end

end FormalResearch.ModularBootstrap.FiveTerm
