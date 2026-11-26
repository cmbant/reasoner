module

public import FormalResearch.SignUncertainty.CtCfuTheta
public import FormalResearch.SignUncertainty.CtChartHad

/-!
# The complex even quotient `ϑ_ε` of the phase `θ_ε` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2/3 (`θ_ε(τ) = τ ϑ_ε(τ²)`).  **Proved.**
`θ_ε` extends holomorphically to `|τ| < 1/2` (`thetaExt`); its odd part is divided by `τ` to give an even analytic function,
so `θ_ε(τ) = τ ϑ_ε(τ²)` with `ϑ_ε` complex analytic at `0`, real on real arguments, and equal to the real germ `θ̂_ε` of `theta_hat`
on small positive reals.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

open CtOuter

/-- The odd part of `Θ_ε = thetaExt ε`. -/
noncomputable def thOdd (ε : ℝ) (τ : ℂ) : ℂ := (thetaExt ε τ - thetaExt ε (-τ)) / 2

lemma thOdd_neg (ε : ℝ) (τ : ℂ) : thOdd ε (-τ) = - thOdd ε τ := by
  unfold thOdd; simp only [neg_neg]; ring

lemma thOdd_zero (ε : ℝ) : thOdd ε 0 = 0 := by simp [thOdd]

lemma analyticAt_thOdd (ε : ℝ) : AnalyticAt ℂ (thOdd ε) 0 := by
  have hb : Metric.ball (0 : ℂ) (1 / 2) ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
  have d1 := differentiableOn_thetaExt ε
  have d2 : DifferentiableOn ℂ (fun τ : ℂ => thetaExt ε (-τ)) (Metric.ball (0 : ℂ) (1 / 2)) :=
    d1.comp (by fun_prop : Differentiable ℂ fun τ : ℂ => -τ).differentiableOn
      (fun τ hτ => by simpa [mem_ball_zero_iff] using hτ)
  exact DifferentiableOn.analyticAt (s := Metric.ball (0 : ℂ) (1 / 2)) ((d1.sub d2).div_const 2) hb

lemma thOdd_real (ε : ℝ) {τ : ℝ} (hτ : |τ| < 1 / 2) : thOdd ε (τ : ℂ) = (outerTheta ε τ : ℂ) := by
  have h1 := thetaExt_real (ε := ε) hτ
  have h2 := thetaExt_real (ε := ε) (τ := -τ) (by simpa using hτ)
  unfold thOdd
  have : ((-τ : ℝ) : ℂ) = -(τ : ℂ) := by push_cast; ring
  rw [this] at h2
  rw [h1, h2, outerTheta_neg ε τ]
  push_cast; ring

/-- `θ_ε(τ) = τ ϑ_ε(τ²)` near `0` with `ϑ_ε` complex analytic. -/
lemma exists_vartheta (ε : ℝ) :
    ∃ ϑ : ℂ → ℂ, AnalyticAt ℂ ϑ 0 ∧ ∀ᶠ τ in 𝓝 (0 : ℂ), thOdd ε τ = τ * ϑ (τ ^ 2) := by
  have hg : AnalyticAt ℂ (dslope (thOdd ε) 0) 0 := by
    obtain ⟨p, r, hp⟩ := analyticAt_thOdd ε
    exact (hp.hasFPowerSeriesAt.dslope_fslope).analyticAt
  have hslope : ∀ x, x ≠ 0 → dslope (thOdd ε) 0 x = thOdd ε x / x := by
    intro x hx; rw [dslope_of_ne _ hx, slope_def_field, thOdd_zero]; simp
  have hev : ∀ x, dslope (thOdd ε) 0 (-x) = dslope (thOdd ε) 0 x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · rw [hslope x hx, hslope (-x) (neg_ne_zero.mpr hx), thOdd_neg, neg_div_neg_eq]
  obtain ⟨ϑ, hϑ, heq⟩ := CtCfu.exists_sq_of_even hg hev
  refine ⟨ϑ, hϑ, ?_⟩
  filter_upwards [heq] with τ hτ
  by_cases h0 : τ = 0
  · simp [h0, thOdd_zero]
  · rw [← hτ, hslope τ h0]; field_simp

lemma tendsto_sqrt_gt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (Real.continuous_sqrt.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx using Real.sqrt_pos.mpr hx

/-- `ϑ_ε` agrees with the real germ `θ̂_ε` on small positive reals. -/
lemma vartheta_real {ε : ℝ} {ϑ : ℂ → ℂ} {th : ℝ → ℝ}
    (hϑ : ∀ᶠ τ in 𝓝 (0 : ℂ), thOdd ε τ = τ * ϑ (τ ^ 2))
    (hth : ∀ᶠ τ in 𝓝 (0 : ℝ), outerTheta ε τ = τ * th (τ ^ 2)) :
    ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), ϑ (x : ℂ) = (th x : ℂ) := by
  have h1 : ∀ᶠ τ : ℝ in 𝓝 (0 : ℝ), thOdd ε (τ : ℂ) = (τ : ℂ) * ϑ ((τ : ℂ) ^ 2) :=
    (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).eventually hϑ
  have h3 : ∀ᶠ τ : ℝ in 𝓝 (0 : ℝ), |τ| < 1 / 2 := by
    have : Metric.ball (0 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [this] with τ hτ
    simpa using hτ
  have h4 : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), thOdd ε (τ : ℂ) = (τ : ℂ) * ϑ ((τ : ℂ) ^ 2) ∧
      outerTheta ε τ = τ * th (τ ^ 2) ∧ |τ| < 1 / 2 :=
    (h1.and (hth.and h3)).filter_mono nhdsWithin_le_nhds
  filter_upwards [tendsto_sqrt_gt.eventually h4, self_mem_nhdsWithin] with x hx hx0
  obtain ⟨e1, e2, e3⟩ := hx
  have hx0' : (0 : ℝ) < x := hx0
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0').ne'
  have e4 := thOdd_real ε e3
  rw [e2] at e4
  rw [e1] at e4
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0'.le
  have e5 : ((Real.sqrt x : ℝ) : ℂ) * ϑ (((Real.sqrt x : ℝ) : ℂ) ^ 2) =
      ((Real.sqrt x * th (Real.sqrt x ^ 2) : ℝ) : ℂ) := e4
  rw [← Complex.ofReal_pow, hsq] at e5
  push_cast at e5
  exact mul_left_cancel₀ (by exact_mod_cast hs) e5

/-- `ϑ_ε` is conjugation symmetric near `0`. -/
lemma vartheta_conj {ε : ℝ} {ϑ : ℂ → ℂ} {th : ℝ → ℝ} (hA : AnalyticAt ℂ ϑ 0)
    (hϑ : ∀ᶠ τ in 𝓝 (0 : ℂ), thOdd ε τ = τ * ϑ (τ ^ 2))
    (hth : ∀ᶠ τ in 𝓝 (0 : ℝ), outerTheta ε τ = τ * th (τ ^ 2)) :
    ∀ᶠ z in 𝓝 (0 : ℂ), ϑ (starRingEnd ℂ z) = starRingEnd ℂ (ϑ z) := by
  have hr := vartheta_real hϑ hth
  have h := eventually_eq_of_real (analyticAt_conj_conj hA) hA (by
    filter_upwards [hr] with x hx
    simp [hx])
  filter_upwards [h] with z hz
  have := congrArg (starRingEnd ℂ) hz
  simpa using this

end FormalResearch.SignUncertainty.CtChart
