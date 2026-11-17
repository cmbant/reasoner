module

public import FormalResearch.Special.BarnesG

/-!
# Linear growth of `ψ` and quadratic growth of `Q` on `Re z ≥ 1/2`

From Gauss' series (`digamma_eq_series`): for `Re z ≥ 1/2`,
`|ψ(z)| ≤ C (1 + |z|)` with an explicit-type constant `C = γ + 2 ∑_{k≥1} k⁻²`, hence
`|Q(z)| ≤ C' (1 + |z|)²` for `Q = barnesQ`.

This is weaker than the logarithmic bound `ψ(z) = O(log |z|)` in vertical strips (DLMF 5.11.2) that
the paper quotes; the polynomial bound is all that the contour argument of `thm:BG` needs (it is
multiplied by `e^{-π|ξ|}`).  Not formalised: the sharp `O(log)` bound.
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex

local notation "γ" => Real.eulerMascheroniConstant

lemma norm_psiTerm_le_half {z : ℂ} (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖psiTerm z k‖ ≤ ‖z - 1‖ * (2 * (1 / ((k : ℝ) + 1) ^ 2)) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : (k : ℝ) + 1 ≤ ‖(k : ℂ) + 1‖ := by
    refine le_trans ?_ (Complex.re_le_norm _); simp
  have h2 : ((k : ℝ) + 1) / 2 ≤ ‖(k : ℂ) + z‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [Complex.add_re, Complex.natCast_re]; linarith
  have hne1 : (k : ℂ) + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne2 : (k : ℂ) + z ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have heq : psiTerm z k = (z - 1) / (((k : ℂ) + 1) * ((k : ℂ) + z)) := by
    unfold psiTerm; field_simp; ring
  rw [heq, norm_div, norm_mul]
  calc ‖z - 1‖ / (‖(k : ℂ) + 1‖ * ‖(k : ℂ) + z‖)
      ≤ ‖z - 1‖ / (((k : ℝ) + 1) * (((k : ℝ) + 1) / 2)) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          (mul_le_mul h1 h2 (by positivity) (le_trans hkp.le h1))
    _ = ‖z - 1‖ * (2 * (1 / ((k : ℝ) + 1) ^ 2)) := by field_simp

lemma summable_invSq : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
  simpa using (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))

/-- `∑_{k ≥ 1} k⁻²` (as a sum over `(k+1)⁻²`). -/
noncomputable def invSqSum : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2

lemma invSqSum_nonneg : 0 ≤ invSqSum := tsum_nonneg fun k => by positivity

/-- Linear growth of `ψ` on `Re z ≥ 1/2`. -/
theorem norm_digamma_le {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖digamma z‖ ≤ (|γ| + 2 * invSqSum) * (1 + ‖z‖) := by
  have hz0 : 0 < z.re := by linarith
  rw [digamma_eq_series hz0]
  have hg : HasSum (fun k : ℕ => ‖z - 1‖ * (2 * (1 / ((k : ℝ) + 1) ^ 2)))
      (‖z - 1‖ * (2 * invSqSum)) :=
    (summable_invSq.hasSum.mul_left 2).mul_left _
  have h1 := tsum_of_norm_bounded hg (fun k => norm_psiTerm_le_half hz k)
  have h2 : ‖-(γ : ℂ) + ∑' k : ℕ, ((1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z))‖ ≤
      |γ| + ‖z - 1‖ * (2 * invSqSum) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · simp
    · exact h1
  refine h2.trans ?_
  have hn : ‖z - 1‖ ≤ ‖z‖ + 1 := by simpa using norm_sub_le z 1
  have hγ : 0 ≤ |γ| := abs_nonneg _
  have hS := invSqSum_nonneg
  nlinarith [norm_nonneg z, mul_nonneg hS (norm_nonneg z), mul_nonneg hγ (norm_nonneg z)]

/-- Quadratic growth of `Q` on `Re z ≥ 1/2`. -/
theorem norm_barnesQ_le : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖barnesQ z‖ ≤ C * (1 + ‖z‖) ^ 2 := by
  set c : ℝ := |Real.log (2 * Real.pi) / 2 - 1 / 2|
  set K : ℝ := |γ| + 2 * invSqSum
  have hK : 0 ≤ K := by have := invSqSum_nonneg; have := abs_nonneg γ; positivity
  refine ⟨c + 1 + K + 1, by positivity, fun z hz => ?_⟩
  have hψ := norm_digamma_le hz
  have hn : ‖z - 1‖ ≤ ‖z‖ + 1 := by simpa using norm_sub_le z 1
  unfold barnesQ
  have e1 : ‖((Real.log (2 * Real.pi) / 2 - 1 / 2 : ℝ) : ℂ) - (z - 1) + (z - 1) * digamma z‖ ≤
      c + ‖z - 1‖ + ‖z - 1‖ * ‖digamma z‖ := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) (by rw [norm_mul]))
    simp only [c, Complex.norm_real, Real.norm_eq_abs]
    simp
  have hz0 := norm_nonneg z
  have e2 : ‖z - 1‖ * ‖digamma z‖ ≤ (‖z‖ + 1) * (K * (1 + ‖z‖)) :=
    mul_le_mul hn hψ (norm_nonneg _) (by positivity)
  nlinarith [mul_nonneg hK hz0, mul_nonneg hz0 hz0, mul_nonneg (mul_nonneg hK hz0) hz0, abs_nonneg (Real.log (2 * Real.pi) / 2 - 1 / 2)]

end FormalResearch.Special.Barnes
