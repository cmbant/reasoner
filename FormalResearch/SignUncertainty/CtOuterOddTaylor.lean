module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Fifth-order Taylor expansion of a smooth odd function (support for `ct:outer` (2))

Generic real analysis, no paper content.  **Proved.**  If `f : ℝ → ℝ` is `C^∞` and odd, then there is `C` with
`|f x - f'(0) x - (f'''(0)/6) x³| ≤ C |x|⁵` for `|x| ≤ 1`: the even Taylor coefficients vanish by oddness and
the remainder is bounded by Taylor's theorem with the Lagrange form on `[0, 1]`.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.SignUncertainty.CtOuter

lemma iteratedDeriv_even_zero_of_odd {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) {k : ℕ} (hk : Even k) :
    iteratedDeriv k f 0 = 0 := by
  have h1 := iteratedDeriv_comp_neg k f 0
  have h2 : (fun x => f (-x)) = -f := funext fun x => by simp [hodd x]
  rw [h2, iteratedDeriv_neg] at h1
  rw [neg_zero, hk.neg_one_pow, one_smul] at h1
  linarith

theorem odd_taylor5 {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hodd : ∀ x, f (-x) = -f x) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ≤ 1 →
      |f x - deriv f 0 * x - iteratedDeriv 3 f 0 / 6 * x ^ 3| ≤ C * |x| ^ 5 := by
  have hc5 : ContDiff ℝ 5 f := hf.of_le (by exact_mod_cast le_top)
  have hcont : Continuous (iteratedDeriv 5 f) := hc5.continuous_iteratedDeriv 5 (by norm_num)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont.continuousOn
  have hud : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have h0 : iteratedDeriv 0 f 0 = 0 := iteratedDeriv_even_zero_of_odd hodd (by decide)
  have h2 : iteratedDeriv 2 f 0 = 0 := iteratedDeriv_even_zero_of_odd hodd (by decide)
  have h4 : iteratedDeriv 4 f 0 = 0 := iteratedDeriv_even_zero_of_odd hodd (by decide)
  have hpos : ∀ x ∈ Icc (0 : ℝ) 1, |f x - deriv f 0 * x - iteratedDeriv 3 f 0 / 6 * x ^ 3| ≤ B / 24 * |x| ^ 5 := by
    intro x hx
    have hcdon : ContDiffOn ℝ (4 + 1 : ℕ) f (Icc 0 1) := hf.contDiffOn.of_le (by exact_mod_cast le_top)
    have hbd : ∀ y ∈ Icc (0 : ℝ) 1, ‖iteratedDerivWithin (4 + 1) f (Icc 0 1) y‖ ≤ B := by
      intro y hy
      rw [iteratedDerivWithin_eq_iteratedDeriv hud ((hf.of_le le_top).contDiffAt) hy]
      exact hB y hy
    have := taylor_mean_remainder_bound (n := 4) (C := B) hcdon hx hbd
    have hT : taylorWithinEval f 4 (Icc 0 1) 0 x = deriv f 0 * x + iteratedDeriv 3 f 0 / 6 * x ^ 3 := by
      rw [taylor_within_apply]
      have hmem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
      have e : ∀ k : ℕ, iteratedDerivWithin k f (Icc 0 1) 0 = iteratedDeriv k f 0 := fun k =>
        iteratedDerivWithin_eq_iteratedDeriv hud ((hf.of_le le_top).contDiffAt) hmem
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, e, h0, h2, h4, sub_zero]
      have hd1 : iteratedDeriv 1 f 0 = deriv f 0 := by rw [iteratedDeriv_one]
      rw [hd1]
      simp [Nat.factorial]
      ring
    rw [hT] at this
    have hx0 : |x| = x := abs_of_nonneg hx.1
    calc |f x - deriv f 0 * x - iteratedDeriv 3 f 0 / 6 * x ^ 3|
        = ‖f x - (deriv f 0 * x + iteratedDeriv 3 f 0 / 6 * x ^ 3)‖ := by
          rw [Real.norm_eq_abs]; ring_nf
      _ ≤ B * (x - 0) ^ (4 + 1) / (Nat.factorial 4 : ℕ) := this
      _ = B / 24 * |x| ^ 5 := by
          rw [hx0]; norm_num [Nat.factorial]; ring
  refine ⟨B / 24, fun x hx => ?_⟩
  rcases le_total 0 x with hx0 | hx0
  · exact hpos x ⟨hx0, by linarith [abs_le.mp hx]⟩
  · have h := hpos (-x) ⟨by linarith, by linarith [abs_le.mp hx]⟩
    have e1 : f x = -f (-x) := by have := hodd (-x); rwa [neg_neg] at this
    have e2 : deriv f 0 * x + iteratedDeriv 3 f 0 / 6 * x ^ 3 =
        -(deriv f 0 * (-x) + iteratedDeriv 3 f 0 / 6 * (-x) ^ 3) := by ring
    rw [abs_neg] at h
    calc |f x - deriv f 0 * x - iteratedDeriv 3 f 0 / 6 * x ^ 3|
        = |-(f (-x) - deriv f 0 * (-x) - iteratedDeriv 3 f 0 / 6 * (-x) ^ 3)| := by
          rw [e1]; ring_nf
      _ = |f (-x) - deriv f 0 * (-x) - iteratedDeriv 3 f 0 / 6 * (-x) ^ 3| := abs_neg _
      _ ≤ B / 24 * |x| ^ 5 := h

end FormalResearch.SignUncertainty.CtOuter
