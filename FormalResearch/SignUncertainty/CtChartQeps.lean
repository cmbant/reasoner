module

public import FormalResearch.SignUncertainty.CtChartReal
public import FormalResearch.SignUncertainty.CtChartBounds

/-!
# Expansion of `Q_ε` at `(0,0)` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2/3: `Q_ε(0;0) = Q_geo(0,0)`, `∂_s Q_ε(0;0) = i h̃_ε(0,0)`,
`Q_ε(s;a) = Q_0 + i h̃(0,0) s + R_ε`, `R_ε = O(|a| + |s|²)`, `∂_s R_ε = O(|a| + |s|)`.  **Proved.**
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma Qeps_zero (ϑ : ℂ → ℂ) : Qeps ϑ (0, 0) = Qgeo (0, 0) := by
  simp [Qeps, Xph]

lemma dyF_Qeps_zero {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0) :
    dyF (Qeps ϑ) (0, 0) = Complex.I * htil ϑ (0, 0) := by
  have h1 : HasDerivAt (fun y : ℂ => Qeps ϑ (y, 0)) (dyF (Qeps ϑ) (0, 0)) 0 :=
    hasDerivAt_slice1 (q := (0, 0)) ((contDiffAt_Qeps hA).differentiableAt (by simp))
  exact h1.unique (hasDerivAt_Qeps_zero hA)

lemma contDiffAt_psiHat {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0) : ContDiffAt ℂ ∞' (psiHat ϑ) 0 := by
  unfold psiHat
  have h1 : ContDiffAt ℂ ∞' (fun β : ℂ => (ysF β, β)) 0 := contDiffAt_ysF.prodMk contDiffAt_id
  exact ContDiffAt.comp (g := hF ϑ) (f := fun β : ℂ => (ysF β, β)) 0 (by simpa [ysF_zero] using contDiffAt_hF hA) h1

/-- **`ct:cfu` Step 2/3, expansion of `Q_ε`.**  With `Q_0 = Q_geo(0,0)`: near `(0,0)`,
`|Q_ε(s;β) - Q_0 - i h̃(0,0) s| ≤ C(|β| + |s|²)` and `|∂_s Q_ε(s;β) - i h̃(0,0)| ≤ C(|s| + |β|)`. -/
theorem Qeps_expansion {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0) :
    ∃ C ρ : ℝ, 0 < ρ ∧ ∀ s β : ℂ, ‖s‖ < ρ → ‖β‖ < ρ →
      ‖Qeps ϑ (s, β) - Qgeo (0, 0) - Complex.I * htil ϑ (0, 0) * s‖ ≤ C * (‖β‖ + ‖s‖ ^ 2) ∧
      ‖dyF (Qeps ϑ) (s, β) - Complex.I * htil ϑ (0, 0)‖ ≤ C * (‖s‖ + ‖β‖) := by
  obtain ⟨C, ρ, hρ, h⟩ := taylor_s_bounds (contDiffAt_Qeps hA)
  refine ⟨C, ρ, hρ, fun s β hs hβ => ?_⟩
  have := h s β hs hβ
  rwa [Qeps_zero, dyF_Qeps_zero hA] at this

/-- info: 'FormalResearch.SignUncertainty.CtChart.Qeps_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qeps_expansion

end FormalResearch.SignUncertainty.CtChart
