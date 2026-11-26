module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# An even analytic germ is an analytic function of the square

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 2 (`m(τ) = τ² n(τ²)`, `θ_ε(τ) = τ θ̂(τ²)`).  **Proved.**
If `g : 𝕜 → 𝕜` (`𝕜 = ℝ` or `ℂ`) is analytic at `0` and even, there is `ĝ` analytic at `0` with `g x = ĝ (x²)` near `0`.
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtCfu

lemma exists_sq_of_even {𝕜 : Type*} [RCLike 𝕜] {g : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g 0) (heven : ∀ x, g (-x) = g x) :
    ∃ gh : 𝕜 → 𝕜, AnalyticAt 𝕜 gh 0 ∧ ∀ᶠ x in 𝓝 (0 : 𝕜), g x = gh (x ^ 2) := by
  obtain ⟨p, r, hp⟩ := hg
  have hr : 0 < r := hp.r_pos
  set c : ℕ → 𝕜 := fun j => p.coeff (2 * j) with hc
  set q : FormalMultilinearSeries 𝕜 𝕜 𝕜 := FormalMultilinearSeries.ofScalars 𝕜 c with hq
  -- radius of `q`
  have hrad : ∀ s : NNReal, (s : ENNReal) < r → ((s ^ 2 : NNReal) : ENNReal) ≤ q.radius := by
    intro s hs
    obtain ⟨C, hC0, hC⟩ := p.norm_mul_pow_le_of_lt_radius (lt_of_lt_of_le hs hp.r_le)
    refine q.le_radius_of_bound C (fun j => ?_)
    have h1 : ‖q j‖ = ‖p (2 * j)‖ := by
      simp only [hq, FormalMultilinearSeries.ofScalars_norm, hc, p.norm_apply_eq_norm_coef]
    rw [h1]
    have := hC (2 * j)
    simpa [pow_mul] using this
  -- positivity of the radius
  have hpos : 0 < q.radius := by
    obtain ⟨s, hs0, hs⟩ : ∃ s : NNReal, 0 < s ∧ (s : ENNReal) < r := by
      obtain ⟨t, ht0, ht⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
      exact ⟨t, by exact_mod_cast ht0, ht⟩
    refine lt_of_lt_of_le ?_ (hrad s hs)
    exact_mod_cast pow_pos hs0 2
  -- the series identity
  have hsum : ∀ x : 𝕜, x ∈ Metric.eball (0 : 𝕜) r → HasSum (fun j : ℕ => c j * (x ^ 2) ^ j) (g x) := by
    intro x hxr
    have hxr' : -x ∈ Metric.eball (0 : 𝕜) r := by simpa using hxr
    have h1 := hp.hasSum hxr
    have h2 := hp.hasSum hxr'
    simp only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] at h1 h2
    have h3 := h1.add h2
    rw [heven x] at h3
    have h4 : HasSum ((fun n : ℕ => x ^ n * p.coeff n + (-x) ^ n * p.coeff n) ∘ (fun j : ℕ => 2 * j)) (g x + g x) := by
      refine ((Function.Injective.hasSum_iff (fun a b h => by omega) (fun n hn => ?_)).mpr h3)
      have : ¬ Even n := by
        intro he; obtain ⟨j, hj⟩ := he; exact hn ⟨j, by show 2 * j = n; omega⟩
      have : Odd n := Nat.not_even_iff_odd.mp this
      simp [this.neg_pow]
    have h5 := h4.mul_left (1 / 2 : 𝕜)
    have e : (fun j : ℕ => 1 / 2 * ((fun n : ℕ => x ^ n * p.coeff n + (-x) ^ n * p.coeff n) ∘ (fun j : ℕ => 2 * j)) j) =
        fun j : ℕ => c j * (x ^ 2) ^ j := by
      funext j
      simp only [Function.comp, hc, pow_mul, Even.neg_pow (by simp : Even (2 * j)), pow_mul]
      ring
    rw [e] at h5
    convert h5 using 1
    ring
  refine ⟨q.sum, ?_, ?_⟩
  · exact (q.hasFPowerSeriesOnBall hpos).analyticAt
  · have hnhds : Metric.eball (0 : 𝕜) r ∈ 𝓝 (0 : 𝕜) := Metric.eball_mem_nhds 0 hr
    filter_upwards [hnhds] with x hx
    have := (hsum x hx).tsum_eq
    rw [← this]
    simp only [FormalMultilinearSeries.sum, hq, FormalMultilinearSeries.ofScalars_apply_eq]
    refine tsum_congr fun j => ?_
    simp [mul_comm]

/-- info: 'FormalResearch.SignUncertainty.CtCfu.exists_sq_of_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_sq_of_even

end FormalResearch.SignUncertainty.CtCfu
