module

public import Mathlib
public import FormalResearch.SignUncertainty.CtLowerDefs
public import FormalResearch.SignUncertainty.HankelLangerPsi
public import FormalResearch.SignUncertainty.HankelTransportInt
public import FormalResearch.Special.AiryGoodCircles

/-!
# `ct:dyadic`: the concrete circle quantity `η(R)` and good Airy radii

`constant_terms_lower.tex`, `ct:dyadic`: with `f_c(u) = Ψ̃(φ_c(u)) φ_c'(u)` and the Airy envelope `e(u) = exp(-(4/3) Re u^{3/2})`,

`η(R) = ∮_{|ũ|=R} |Ψ̃(ũ)| / |e(ũ)| |dũ| + ∮_{|u|=R} |f_c(u)| / |e(u)| |du|`,

and a *good Airy radius* is one with `|Ai| ≥ c (1+|u|)^{-1/4} e(u)^{1/2}` on `|u| = R` (`ap:E2`, `AIRY_POISSON`; `gt:1.0p`).

* `ctGoodRadius R`: the Lean form of `ap:E2` with the constant `c² = 1/(25π)` of `good_circle_exists` (`AiryGoodCircles`); it is a
  property of `Ai` alone, so it does not depend on `(ε, c, f)`.
* `ctPhiC c₁ ε c`: the complex chart `φ_c`.  In Lean `ctPhi` is the real inverse of `û` on the window domain `ctPhiDom`
  (`ψ_ε` is formalised as `C^∞`, not analytic, at `a = 0`); the paper's `φ_c` on `|u| ≤ R_max = 4c₁²c^{2/3}` is its holomorphic
  continuation (`ct:cfu`: `ψ_ε` is analytic across `a = 0`; `ct:phic-exp`).  `ctPhiC` is *defined* as that continuation (a holomorphic
  function on a disc of radius `> R_max` agreeing with `ctPhi` on the real window; unique there by the identity theorem), and is
  the junk function `0` where no continuation exists.  That the continuation exists, with the properties used, is the named
  hypothesis `CtChartComplex` (not proved).
* `ctFcC`: `f_c(u) = Ψ̃(φ_c(u)) φ_c'(u)` for complex `u`; `ctEta`: `η(R)` as the circle integral `∫_0^{2π} R(...)/e dθ`
  (`|dũ| = R dθ`; the same normalisation as `lowerEta` of Paper II).

No result here; definitions and the single hypothesis predicate `CtChartComplex`.
-/

@[expose] public section

open Complex Metric
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- **Good Airy radius** (`ap:E2`): `‖Ai(u)‖² ≥ (1/(25π)) (1+R)^{-1/2} e(u)` on the whole circle `|u| = R`
(so `Ai` has no zero there).  Holds for all `R = r²` with `|(2/3) r³ - (π/4 + mπ)| ≤ 1/4` and `r ≥ 10`
(`lowerGood_circle_of_phase`, Paper II), which is a set of positive measure in every `[r₀, (3/2) r₀]`. -/
def ctGoodRadius (R : ℝ) : Prop :=
  ∀ u : ℂ, ‖u‖ = R → 1 / (25 * π) * (1 + R) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ ‖airyAiC u‖ ^ 2

/-- `R_max = 4c₁²c^{2/3}`, the radius of the chart `φ_c` (`ct:cfu`). -/
noncomputable def ctRmax (c₁ c : ℝ) : ℝ := 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)

/-- `F` is a holomorphic continuation of the real chart `ctPhi ε c` to a disc of radius `> R_max = 4c₁²c^{2/3}`: holomorphic
on `ball 0 ρ` (`ρ > R_max`) and equal to `ctPhi ε c` on the part `|x| ≤ R_max` of its real domain `ctPhiDom ε c`. -/
def IsCtChartExt (c₁ ε c : ℝ) (F : ℂ → ℂ) : Prop :=
  (∃ ρ : ℝ, ctRmax c₁ c < ρ ∧ DifferentiableOn ℂ F (ball 0 ρ)) ∧
    ∀ x : ℝ, x ∈ ctPhiDom ε c → |x| ≤ ctRmax c₁ c → F (x : ℂ) = (ctPhi ε c x : ℂ)

open Classical in
/-- **The complex chart `φ_c`** (`ct:cfu`): the holomorphic continuation of `ctPhi ε c` to `|u| ≤ R_max` (`0` if there is none).
Unique on `ball 0 ρ` by the identity theorem once the real window `[-R_max, 0] ⊆ ctPhiDom ε c`. -/
noncomputable def ctPhiC (c₁ ε c : ℝ) : ℂ → ℂ :=
  if h : ∃ F, IsCtChartExt c₁ ε c F then h.choose else fun _ => 0

lemma ctPhiC_spec {c₁ ε c : ℝ} (h : ∃ F, IsCtChartExt c₁ ε c F) : IsCtChartExt c₁ ε c (ctPhiC c₁ ε c) := by
  unfold ctPhiC
  simpa only [h, dite_true] using h.choose_spec

/-- `f_c(u) = Ψ̃(φ_c(u)) φ_c'(u)` for complex `u` (`Ψ̃ = hankelPsi c f`). -/
noncomputable def ctFcC (c₁ ε c : ℝ) (f : ℝ → ℝ) (u : ℂ) : ℂ :=
  hankelPsi c f (ctPhiC c₁ ε c u) * deriv (ctPhiC c₁ ε c) u

/-- **`η(R)`** of `ct:dyadic`: `∮_{|ũ|=R} |Ψ̃|/e |dũ| + ∮_{|u|=R} |f_c|/e |du|`, as `∫_0^{2π} R (‖Ψ̃‖ + ‖f_c‖)/e dθ` on the circle
`u = R e^{iθ}` (`|du| = R dθ`; `e(u) = airyEnv u`). -/
noncomputable def ctEta (c₁ ε c : ℝ) (f : ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * π),
    R * (‖hankelPsi c f (circleMap 0 R θ)‖ + ‖ctFcC c₁ ε c f (circleMap 0 R θ)‖) / airyEnv (circleMap 0 R θ)

/-- **The complex-chart facts of `ct:cfu`** (named hypothesis, not proved; `ct:phic-exp`, analyticity of `ψ_ε` across `a = 0`):
for `c ≥ c₀` and `ε = ±1`, the real window `[-R_max, 0]` lies in the domain `ctPhiDom` of `φ_c`, `φ_c` has a holomorphic
continuation to a disc of radius `> R_max = 4c₁²c^{2/3}`, it is real on the real axis, and on `|u| ≤ R_max`,
`|φ_c(u) - u| ≤ C c^{-1/3}` and `|φ_c'(u) - 1| ≤ C c^{-1}`. -/
def CtChartComplex (c₁ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ c : ℝ, c₀ ≤ c →
    (∃ F, IsCtChartExt c₁ ε c F) ∧
    (∀ x : ℝ, -ctRmax c₁ c ≤ x → x ≤ 0 → x ∈ ctPhiDom ε c) ∧
    (∀ x : ℝ, |x| ≤ ctRmax c₁ c → (ctPhiC c₁ ε c (x : ℂ)).im = 0) ∧
    (∀ u : ℂ, ‖u‖ ≤ ctRmax c₁ c →
      ‖ctPhiC c₁ ε c u - u‖ ≤ C * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (ctPhiC c₁ ε c) u - 1‖ ≤ C * c ^ (-1 : ℝ))

lemma ctEta_nonneg (c₁ ε c : ℝ) (f : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ ctEta c₁ ε c f R := by
  unfold ctEta
  refine intervalIntegral.integral_nonneg (by positivity [Real.pi_pos]) fun θ _ => ?_
  exact div_nonneg (mul_nonneg hR (add_nonneg (norm_nonneg _) (norm_nonneg _))) (airyEnv_pos _).le

end FormalResearch.SignUncertainty
