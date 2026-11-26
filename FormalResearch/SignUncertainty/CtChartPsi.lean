module

public import FormalResearch.SignUncertainty.CtChartQeps
public import FormalResearch.SignUncertainty.CtCfuData

/-!
# The chart data agree with the real Step 2 data (`ct:cfu` Step 2/3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2 (`ct:psi-def`, `ct:langer-inv`) versus
Step 3 (the `β = b²` chart).  **Proved.**  For real `β` near `0` the complex-chart objects are the real Step 2 objects:
`d_C(β) = d(β)`, `a_C(β) = A(β)`, `ϑ(β) = θ̂(β)`, `L_C(β) = N(β)`; hence for the real Langer parameter `a` near `0` with
`β = z_A(a)`:
`a_C(β) = a`, `ψ̂(β) = ψ(a) = θ̂(z_A a)/d(z_A a)` (`psiOf`), and `exp(L_C(β))/π² = Ξ(a)`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

open CtOuter CtCfu

lemma analyticAt_ofReal_comp {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0) :
    AnalyticAt ℝ (fun x : ℝ => ϑ (x : ℂ)) 0 := by
  have h1 : AnalyticAt ℝ ϑ ((0 : ℝ) : ℂ) := by simpa using hA.restrictScalars (𝕜 := ℝ)
  exact h1.comp (Complex.ofRealCLM.analyticAt 0)

/-- `ϑ_ε` agrees with the real germ `θ̂_ε` on a two-sided real neighbourhood of `0` (identity theorem). -/
lemma vartheta_real2 {ε : ℝ} {ϑ : ℂ → ℂ} {th : ℝ → ℝ} (hA : AnalyticAt ℂ ϑ 0) (hthA : AnalyticAt ℝ th 0)
    (hϑ : ∀ᶠ τ in 𝓝 (0 : ℂ), thOdd ε τ = τ * ϑ (τ ^ 2))
    (hth : ∀ᶠ τ in 𝓝 (0 : ℝ), outerTheta ε τ = τ * th (τ ^ 2)) :
    ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), ϑ (x : ℂ) = (th x : ℂ) := by
  have hr := vartheta_real hϑ hth
  have hg : AnalyticAt ℝ (fun x : ℝ => ϑ (x : ℂ) - (th x : ℂ)) 0 := by
    refine (analyticAt_ofReal_comp hA).sub ?_
    exact (Complex.ofRealCLM.analyticAt (th 0)).comp hthA
  rcases hg.eventually_eq_zero_or_eventually_ne_zero with h | h
  · filter_upwards [h] with x hx using sub_eq_zero.mp hx
  · exfalso
    have h1 : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), ϑ (x : ℂ) - (th x : ℂ) ≠ 0 :=
      h.filter_mono (nhdsGT_le_nhdsNE 0)
    have h2 : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), ϑ (x : ℂ) - (th x : ℂ) = 0 := by
      filter_upwards [hr] with x hx using sub_eq_zero.mpr hx
    obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
    exact hx1 hx2

lemma fC_ofReal (x : ℝ) : fC (x : ℂ) = (fF x : ℂ) := by
  unfold fC fF
  rw [nC_ofReal, ntC_ofReal]
  push_cast; ring

/-- For real `x` near `0`, `d_C(x) = d(x)`. -/
lemma dC_ofReal : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), dC (x : ℂ) = (dF x : ℂ) := by
  have hf : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), 0 < fF x := by
    have := contDiffAt_fF.continuousAt.eventually (lt_mem_nhds (by rw [fF_zero]; positivity : (0 : ℝ) < fF 0))
    exact this
  filter_upwards [hf] with x hx
  unfold dC dF
  rw [fC_ofReal]
  have hpos : 0 < (3 / 2) * fF x := by positivity
  have e1 : ((3 / 2 : ℂ) * (fF x : ℂ)) = (((3 / 2) * fF x : ℝ) : ℂ) := by push_cast; ring
  rw [e1, ← Complex.ofReal_log hpos.le, Real.rpow_def_of_pos hpos]
  rw [show ((Real.log ((3 / 2) * fF x) : ℝ) : ℂ) / 3 = ((Real.log ((3 / 2) * fF x) * (1 / 3) : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_exp]

lemma aC_ofReal : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), aC (x : ℂ) = (AF x : ℝ) := by
  filter_upwards [dC_ofReal] with x hx
  unfold aC AF
  rw [hx]; push_cast; ring

lemma LC_ofReal (x : ℝ) : LC (x : ℂ) = (NF x : ℂ) := by
  unfold LC NF
  rw [nC_ofReal]; push_cast; ring

/-- For real `x` near `0`, `ψ̂(x) = θ̂(x)/d(x)`. -/
lemma psiHat_ofReal {ε : ℝ} {ϑ : ℂ → ℂ} {th : ℝ → ℝ} (hA : AnalyticAt ℂ ϑ 0) (hthA : AnalyticAt ℝ th 0)
    (hϑ : ∀ᶠ τ in 𝓝 (0 : ℂ), thOdd ε τ = τ * ϑ (τ ^ 2))
    (hth : ∀ᶠ τ in 𝓝 (0 : ℝ), outerTheta ε τ = τ * th (τ ^ 2)) :
    ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), psiHat ϑ (x : ℂ) = ((th x / dF x : ℝ) : ℂ) := by
  have h1 := (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).eventually (psiHat_eq ϑ)
  filter_upwards [h1, vartheta_real2 hA hthA hϑ hth, dC_ofReal] with x e1 e2 e3
  rw [e1, e2, e3]
  push_cast; rfl

/-- **Link to Step 2.** For the real Langer parameter `a` near `0`, with `β = z_A(a)`: the chart parameter reproduces `a`,
`ψ̂(β) = ψ(a)` (`psiOf`), and `exp(L_C(β))/π² = Ξ(a)`. -/
theorem psiHat_link {ε : ℝ} {ϑ : ℂ → ℂ} {th : ℝ → ℝ} (hA : AnalyticAt ℂ ϑ 0) (hthA : AnalyticAt ℝ th 0)
    (hϑ : ∀ᶠ τ in 𝓝 (0 : ℂ), thOdd ε τ = τ * ϑ (τ ^ 2))
    (hth : ∀ᶠ τ in 𝓝 (0 : ℝ), outerTheta ε τ = τ * th (τ ^ 2)) :
    ∀ᶠ a : ℝ in 𝓝 (0 : ℝ),
      aC ((zA a : ℝ) : ℂ) = (a : ℂ) ∧ psiHat ϑ ((zA a : ℝ) : ℂ) = ((psiOf th a : ℝ) : ℂ) ∧
        Complex.exp (LC ((zA a : ℝ) : ℂ)) / (π : ℂ) ^ 2 = ((Xi a : ℝ) : ℂ) := by
  filter_upwards [tendsto_zA.eventually aC_ofReal, tendsto_zA.eventually (psiHat_ofReal hA hthA hϑ hth),
    AF_zA_eventually] with a h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, h3]
  · rw [h2]; rfl
  · rw [LC_ofReal]
    unfold Xi
    push_cast
    rfl

/-- info: 'FormalResearch.SignUncertainty.CtChart.psiHat_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psiHat_link

end FormalResearch.SignUncertainty.CtChart
