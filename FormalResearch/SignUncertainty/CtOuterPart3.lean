module

public import FormalResearch.SignUncertainty.CtOuterAsymp

/-!
# `ct:outer` (3): derivative bounds for `θ_-`

**Proved.**  For every `n ≥ 1`, `|θ_-^{(n)}(τ)| ≤ C_n (1+|τ|)² e^{-π|τ|}` for `|τ| ≥ 1`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- For `τ > 5`: `θ_-^{(n)} = φ^{(n)} + F_{ũ₁}^{(n)}` (`n ≥ 1`). -/
lemma theta_neg_iter_split {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 5 < τ) :
    iteratedDeriv n (outerTheta (-1)) τ = iteratedDeriv n (phi0 utl0) τ + iteratedDeriv n GF τ := by
  have hθ : ContDiffAt ℝ (n : WithTop ℕ∞) (outerTheta (-1)) τ :=
    ((contDiff_outerTheta (-1)).of_le le_top).contDiffAt
  have hG : ContDiffAt ℝ (n : WithTop ℕ∞) GF τ :=
    (contDiff_GF.of_le (by exact_mod_cast le_top)).contDiffAt
  have hQ : ContDiffAt ℝ (n : WithTop ℕ∞) (fun x => π / 2 + outerTheta (-1) x) τ :=
    contDiffAt_const.add hθ
  have hev : phi0 utl0 =ᶠ[𝓝 τ] (fun x => π / 2 + outerTheta (-1) x) - GF := by
    filter_upwards [lt_mem_nhds hτ] with x hx
    have := theta_neg_split (τ := x) hx.le
    simp only [Pi.sub_apply]
    linarith
  rw [hev.iteratedDeriv_eq n, iteratedDeriv_sub hQ hG, iteratedDeriv_const_add hn]
  ring

/-- Pass from a bound for `τ ≥ 6` to one for `τ ≥ 1`, for a continuous function. -/
lemma ext_bound {g : ℝ → ℝ} (hg : Continuous g) {K : ℝ}
    (h : ∀ τ : ℝ, 6 ≤ τ → |g τ| ≤ K * ((1 + τ) ^ 2 * Real.exp (-π * τ))) :
    ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ τ → |g τ| ≤ C * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := g) (s := Icc (1 : ℝ) 6) hg.continuousOn
  refine ⟨|K| + |B| * Real.exp (6 * π), fun τ hτ => ?_⟩
  have hX : 0 ≤ (1 + τ) ^ 2 * Real.exp (-π * τ) := by positivity
  by_cases h6 : 6 ≤ τ
  · refine (h τ h6).trans ?_
    have : 0 ≤ |B| * Real.exp (6 * π) * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := by positivity
    nlinarith only [le_abs_self K, hX, this]
  · have ht : τ ∈ Icc (1 : ℝ) 6 := ⟨hτ, (not_le.mp h6).le⟩
    have h1 := hB τ ht
    rw [Real.norm_eq_abs] at h1
    have h2 : Real.exp (-(6 * π)) ≤ (1 + τ) ^ 2 * Real.exp (-π * τ) := by
      have : Real.exp (-(6 * π)) ≤ Real.exp (-π * τ) := by
        apply Real.exp_le_exp.mpr; nlinarith only [Real.pi_pos, not_le.mp h6]
      have h3 : (1 : ℝ) ≤ (1 + τ) ^ 2 := by nlinarith only [hτ]
      nlinarith only [this, h3, Real.exp_pos (-π * τ)]
    have hex : Real.exp (6 * π) * Real.exp (-(6 * π)) = 1 := by rw [← Real.exp_add]; simp
    calc |g τ| ≤ B := h1
      _ ≤ |B| := le_abs_self B
      _ = |B| * Real.exp (6 * π) * Real.exp (-(6 * π)) := by rw [mul_assoc, hex, mul_one]
      _ ≤ |B| * Real.exp (6 * π) * ((1 + τ) ^ 2 * Real.exp (-π * τ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ _ := by
          have : 0 ≤ |K| * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := by positivity
          nlinarith only [this]

/-- Transfer a bound from `τ ≥ 1` to `τ ≤ -1` for a (even/odd) smooth function's iterated derivative. -/
lemma bound_two_sided {f : ℝ → ℝ} {c : ℝ} (hc : |c| = 1) (hf : ∀ x, f (-x) = c * f x)
    (hd : ∀ n : ℕ, ContDiff ℝ n f) (n : ℕ) {C : ℝ}
    (h : ∀ τ : ℝ, 1 ≤ τ → |iteratedDeriv n f τ| ≤ C * ((1 + τ) ^ 2 * Real.exp (-π * τ))) :
    ∀ τ : ℝ, 1 ≤ |τ| → |iteratedDeriv n f τ| ≤ C * ((1 + |τ|) ^ 2 * Real.exp (-π * |τ|)) := by
  intro τ hτ
  rcases le_abs'.mp hτ with h1 | h1
  · -- τ ≤ -1
    have hn := abs_iteratedDeriv_neg hc hf hd n (-τ)
    rw [neg_neg] at hn
    rw [hn, abs_of_nonpos (by linarith : τ ≤ 0), ]
    exact h (-τ) (by linarith)
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ)]
    exact h τ h1

/-- **Derivative bounds for `θ_-`**: `|θ_-^{(n)}(τ)| ≤ C_n (1+|τ|)² e^{-π|τ|}` for `|τ| ≥ 1`, `n ≥ 1`. -/
theorem theta_neg_deriv_bound {n : ℕ} (hn : 0 < n) : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |iteratedDeriv n (outerTheta (-1)) τ| ≤ C * ((1 + |τ|) ^ 2 * Real.exp (-π * |τ|)) := by
  obtain ⟨K, hK⟩ := phi0_deriv_bound measurable_utl0 integrable_utl0 (fun t ht => utl0_eq_zero (by linarith)) n
  obtain ⟨C, hC⟩ := GF_deriv_bound n
  have hcd : ∀ m : ℕ, ContDiff ℝ m (outerTheta (-1)) := fun m => (contDiff_outerTheta (-1)).of_le le_top
  have hcont : Continuous (iteratedDeriv n (outerTheta (-1))) :=
    (contDiff_outerTheta (-1)).continuous_iteratedDeriv n le_top
  have hb : ∀ τ : ℝ, 6 ≤ τ → |iteratedDeriv n (outerTheta (-1)) τ| ≤
      (|K| + |C|) * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := by
    intro τ hτ
    rw [theta_neg_iter_split hn (by linarith)]
    have h1 := hK τ (by linarith)
    have h2 := hC τ (by linarith)
    have e1 : Real.exp (-π * τ) ≤ (1 + τ) ^ 2 * Real.exp (-π * τ) := by
      have : (1 : ℝ) ≤ (1 + τ) ^ 2 := by nlinarith only [hτ]
      nlinarith only [this, Real.exp_pos (-π * τ)]
    have hX : 0 ≤ (1 + τ) ^ 2 * Real.exp (-π * τ) := by positivity
    calc _ ≤ |iteratedDeriv n (phi0 utl0) τ| + |iteratedDeriv n GF τ| := abs_add_le _ _
      _ ≤ K * Real.exp (-π * τ) + C * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := add_le_add h1 h2
      _ ≤ |K| * ((1 + τ) ^ 2 * Real.exp (-π * τ)) + |C| * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := by
          apply add_le_add
          · calc K * Real.exp (-π * τ) ≤ |K| * Real.exp (-π * τ) :=
                mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
              _ ≤ |K| * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := mul_le_mul_of_nonneg_left e1 (abs_nonneg K)
          · exact mul_le_mul_of_nonneg_right (le_abs_self C) hX
      _ = _ := by ring
  obtain ⟨C', hC'⟩ := ext_bound hcont hb
  refine ⟨C', bound_two_sided (c := -1) (by simp) (fun x => by rw [outerTheta_neg]; ring) hcd n hC'⟩

/-- info: 'FormalResearch.SignUncertainty.CtOuter.theta_neg_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_neg_deriv_bound

end FormalResearch.SignUncertainty.CtOuter
