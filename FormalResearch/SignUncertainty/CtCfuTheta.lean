module

public import FormalResearch.SignUncertainty.CtCfuEven
public import FormalResearch.SignUncertainty.CtOuterTheta3

/-!
# `θ_ε(τ) = τ θ̂(τ²)` with `θ̂` analytic

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 2.  **Proved.**
`θ_ε` is odd and real-analytic (`ct:outer` (2)), so `θ_ε(τ)/τ` is even and analytic and `θ_ε(τ) = τ θ̂_ε(τ²)` near `0`
with `θ̂_ε` analytic, `θ̂_ε(0) = θ_1^ε`, `θ̂_ε'(0) = θ_3^ε`.
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtCfu

open CtOuter

theorem theta_hat {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ th : ℝ → ℝ, AnalyticAt ℝ th 0 ∧ (∀ᶠ τ in 𝓝 (0 : ℝ), outerTheta ε τ = τ * th (τ ^ 2)) ∧
      th 0 = ctTheta1 ε ∧ deriv th 0 = ctTheta3 ε := by
  set θ := outerTheta ε with hθ
  have hθan : AnalyticAt ℝ θ 0 :=
    (contDiff_omega_iff_analyticOnNhd.mp (contDiff_outerTheta ε)) 0 (mem_univ _)
  have hodd : ∀ x, θ (-x) = -θ x := outerTheta_neg ε
  have hθ0 : θ 0 = 0 := by have := hodd 0; simp at this; linarith
  obtain ⟨p, r, hp⟩ := hθan
  have hg : AnalyticAt ℝ (dslope θ 0) 0 := (hp.hasFPowerSeriesAt.dslope_fslope).analyticAt
  have hslope : ∀ x, x ≠ 0 → dslope θ 0 x = θ x / x := by
    intro x hx; rw [dslope_of_ne θ hx, slope_def_field, hθ0]; simp
  have hev : ∀ x, dslope θ 0 (-x) = dslope θ 0 x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · rw [hslope x hx, hslope (-x) (neg_ne_zero.mpr hx), hodd, neg_div_neg_eq]
  obtain ⟨th, hth, heq⟩ := exists_sq_of_even hg hev
  have hrel : ∀ᶠ τ in 𝓝 (0 : ℝ), θ τ = τ * th (τ ^ 2) := by
    filter_upwards [heq] with τ hτ
    by_cases h0 : τ = 0
    · simp [h0, hθ0]
    · rw [← hτ, hslope τ h0]; field_simp
  have hth0 : th 0 = deriv θ 0 := by
    have := heq.self_of_nhds
    simpa [dslope_same] using this.symm
  -- Taylor remainder
  obtain ⟨C, hC⟩ := ct_outer_part2_taylor_values hε
  have hT : ∀ τ : ℝ, |τ| ≤ 1 → τ ≠ 0 → |dslope θ 0 τ - ctTheta1 ε - ctTheta3 ε * τ ^ 2| ≤ C * |τ| ^ 4 := by
    intro τ hτ h0
    have := hC τ hτ
    rw [hslope τ h0]
    have e : θ τ / τ - ctTheta1 ε - ctTheta3 ε * τ ^ 2 = (θ τ - ctTheta1 ε * τ - ctTheta3 ε * τ ^ 3) / τ := by
      field_simp
    rw [e, abs_div]
    have hτp : 0 < |τ| := abs_pos.mpr h0
    rw [div_le_iff₀ hτp]
    calc _ ≤ C * |τ| ^ 5 := this
      _ = C * |τ| ^ 4 * |τ| := by ring
  -- `deriv θ 0 = θ₁`
  have hd1 : deriv θ 0 = ctTheta1 ε := by
    have hdiff : HasDerivAt θ (deriv θ 0) 0 := (hp.hasFPowerSeriesAt.analyticAt.differentiableAt).hasDerivAt
    have h1 : Tendsto (fun τ : ℝ => θ τ / τ) (𝓝[≠] 0) (𝓝 (deriv θ 0)) := by
      have := hasDerivAt_iff_tendsto_slope.mp hdiff
      refine this.congr fun τ => ?_
      rw [slope_def_field, hθ0]; simp
    have h2 : Tendsto (fun τ : ℝ => θ τ / τ) (𝓝[≠] 0) (𝓝 (ctTheta1 ε)) := by
      have hb : Tendsto (fun τ : ℝ => |ctTheta3 ε| * τ ^ 2 + C * |τ| ^ 4) (𝓝 0) (𝓝 0) := by
        have : Continuous fun τ : ℝ => |ctTheta3 ε| * τ ^ 2 + C * |τ| ^ 4 := by fun_prop
        simpa using this.tendsto 0
      refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        (hb.mono_left nhdsWithin_le_nhds))
      have hnear0 : ∀ᶠ τ in 𝓝 (0 : ℝ), |τ| ≤ 1 := by
        filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with τ hτ
        simpa [Real.dist_eq] using hτ
      have hnear : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), |τ| ≤ 1 := Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear0
      filter_upwards [hnear, self_mem_nhdsWithin] with τ hτ h0
      have h0' : τ ≠ 0 := h0
      have := hT τ hτ h0'
      rw [← hslope τ h0', Real.norm_eq_abs]
      calc |dslope θ 0 τ - ctTheta1 ε| = |(dslope θ 0 τ - ctTheta1 ε - ctTheta3 ε * τ ^ 2) + ctTheta3 ε * τ ^ 2| := by ring_nf
        _ ≤ |dslope θ 0 τ - ctTheta1 ε - ctTheta3 ε * τ ^ 2| + |ctTheta3 ε * τ ^ 2| := abs_add_le _ _
        _ ≤ C * |τ| ^ 4 + |ctTheta3 ε| * τ ^ 2 := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg τ)]; exact add_le_add this le_rfl
        _ = _ := by ring
    exact tendsto_nhds_unique h1 h2
  refine ⟨th, hth, hrel, by rw [hth0, hd1], ?_⟩
  -- `th' 0 = θ₃`
  have hdth : HasDerivAt th (deriv th 0) 0 := hth.differentiableAt.hasDerivAt
  have h1 : Tendsto (fun z : ℝ => (th z - th 0) / z) (𝓝[>] 0) (𝓝 (deriv th 0)) := by
    have := (hasDerivAt_iff_tendsto_slope.mp hdth).mono_left (nhdsWithin_mono (0 : ℝ) (fun z (hz : z ∈ Ioi (0 : ℝ)) => (ne_of_gt hz : z ≠ 0)))
    refine this.congr fun z => ?_
    rw [slope_def_field, sub_zero]
  have h2 : Tendsto (fun z : ℝ => (th z - th 0) / z) (𝓝[>] 0) (𝓝 (ctTheta3 ε)) := by
    have hb : Tendsto (fun z : ℝ => C * z) (𝓝 0) (𝓝 0) := by
      have : Continuous fun z : ℝ => C * z := by fun_prop
      simpa using this.tendsto 0
    refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (hb.mono_left nhdsWithin_le_nhds))
    have hsq : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto (0 : ℝ))
      simpa using this.mono_left nhdsWithin_le_nhds
    have hev := hsq.eventually heq
    have hnear : ∀ᶠ z in 𝓝[>] (0 : ℝ), Real.sqrt z ≤ 1 := by
      have : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := hsq
      exact this.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hev, hnear, self_mem_nhdsWithin] with z hz hn hzpos
    have hz0 : 0 < z := hzpos
    have hs0 : Real.sqrt z ≠ 0 := (Real.sqrt_pos.mpr hz0).ne'
    have hsq2 : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz0.le
    have key := hT (Real.sqrt z) (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hn) hs0
    rw [hsq2] at hz
    have hth0' : th 0 = ctTheta1 ε := by rw [hth0, hd1]
    have hz' : dslope θ 0 (Real.sqrt z) = th z := hz
    rw [hz'] at key
    have hpow : |Real.sqrt z| ^ 4 = z ^ 2 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt z ^ 4 = (Real.sqrt z ^ 2) ^ 2 := by ring
        _ = z ^ 2 := by rw [hsq2]
    rw [hsq2, hpow] at key
    rw [Real.norm_eq_abs, hth0']
    have e : (th z - ctTheta1 ε) / z - ctTheta3 ε = (th z - ctTheta1 ε - ctTheta3 ε * z) / z := by
      field_simp
    rw [e, abs_div, abs_of_pos hz0, div_le_iff₀ hz0]
    calc _ ≤ C * z ^ 2 := key
      _ = C * z * z := by ring
  exact tendsto_nhds_unique h1 h2

/-- info: 'FormalResearch.SignUncertainty.CtCfu.theta_hat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_hat

end FormalResearch.SignUncertainty.CtCfu
