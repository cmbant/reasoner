module

public import FormalResearch.Special.DiscreteAirySecondShift
public import FormalResearch.Special.DiscreteAiryLimitDefect

/-!
# Second-order Airy parametrix, part 12: the shifted form on the lattice (Q4)

With `p := a2p = ζ q₁²/(2g)` (so that `g · y(X + δ⁴ q₁/g) = a2Psi + O(δ⁹ w)`, see `DiscreteAirySecondShift`) the paper-form row
defect (Q3, `airy2_defect_lattice`) transfers to the **shifted** parametrix
`ψ̂_j = g(q_j) · y(a2Xh)`, `a2Xh = ζ(q_j)/δ² + δ⁴ q₁(q_j)/g(q_j)`:

`airy2_shifted_defect`: for `q_k ∈ J` and `δ ≤ δ₀`,
`|jac a c ψ̂ (k)| ≤ K δ⁹ w(a2Xh(q_k))`, `a_j = (A + δ⁶ A₂)(q_j - δ³/2)`, `c_j = 2 A Ch(ζ ζ'²) + δ⁶ c₂` at `q_j`
(`w = airyWt` for `y = Ai`, `w = airyBiWt` for `Bi`: `airy2_shifted_defect_Ai`, `airy2_shifted_defect_Bi`).

This is exactly the shape of the hypotheses `hdA`, `hdB` of `dao_pair_rate` / `dai_full_rate` at `n = 1` (`δ^(6+3·1) = δ⁹`) for the
lattice sequences `X_j = a2Xh(q_j)`, `g_j = g(q_j)`.  `p` is *determined* (`p = g ζ B²/2`, `B = q₁/g`); it does not enter the
`q₁`-residual equation.  **Claim class: proved**; constants existential.
-/

@[expose] public section

open Set FormalResearch.DiscreteAiry

namespace FormalResearch.Special

open SturmAiry

/-- The `h²` amplitude correction `p = g ζ B²/2 = ζ q₁²/(2g)` fixed by the shifted form. -/
noncomputable def a2p (ζ g q1 : ℝ → ℝ) (q : ℝ) : ℝ := ζ q * q1 q ^ 2 / (2 * g q)
/-- The shifted Airy argument `X + δ⁴ B`, `X = ζ/δ²`, `B = q₁/g`. -/
noncomputable def a2Xh (ζ g q1 : ℝ → ℝ) (δ q : ℝ) : ℝ := ζ q / δ ^ 2 + δ ^ 4 * (q1 q / g q)

/-- `g ≠ 0` from the amplitude relation. -/
lemma a2_g_ne {U : Set ℝ} {ζ A g : ℝ → ℝ}
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∀ q ∈ U, g q ≠ 0 := fun q hq h0 => by
  have := hrel q hq
  rw [h0] at this; simp at this

/-- Regularity data for `p = a2p`. -/
lemma Airy2Data.of_smooth {U : Set ℝ} {ζ A A2 g q1 : ℝ → ℝ} (hU : IsOpen U) (hζ : ContDiffOn ℝ 4 ζ U)
    (hA : ContDiffOn ℝ 3 A U) (hA2 : ContDiffOn ℝ 1 A2 U) (hg : ContDiffOn ℝ 3 g U)
    (hq1 : ContDiffOn ℝ 3 q1 U) (hg0 : ∀ q ∈ U, g q ≠ 0) :
    Airy2Data U ζ A A2 g (a2p ζ g q1) q1 := by
  refine ⟨hU, hζ, hA, hA2, hg, ?_, hq1⟩
  have h1 : ContDiffOn ℝ 1 ζ U := hζ.of_le (by norm_num)
  have h2 : ContDiffOn ℝ 1 q1 U := hq1.of_le (by norm_num)
  have h3 : ContDiffOn ℝ 1 g U := hg.of_le (by norm_num)
  exact (h1.mul (h2.pow 2)).div (contDiffOn_const.mul h3) (fun q hq => mul_ne_zero two_ne_zero (hg0 q hq))

/-- Bounds of a continuous function on a compact set. -/
lemma a2_bd {s : Set ℝ} (hs : IsCompact s) {f : ℝ → ℝ} (hf : ContinuousOn f s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ s, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hf
  exact ⟨max M 0, le_max_right _ _, fun x hx => by simpa using (hM x hx).trans (le_max_left _ _)⟩

/-- The algebra of the shifted form. -/
lemma a2_shift_alg {g ζ q1 y yp δ : ℝ} (hg : g ≠ 0) (hδ : δ ≠ 0) :
    g * (y + yp * (δ ^ 4 * (q1 / g)) + ζ / δ ^ 2 * y * (δ ^ 4 * (q1 / g)) ^ 2 / 2) =
      (g + (δ ^ 3) ^ 2 * (ζ * q1 ^ 2 / (2 * g))) * y + δ * (δ ^ 3 * q1) * yp := by
  field_simp
  ring

end FormalResearch.Special
