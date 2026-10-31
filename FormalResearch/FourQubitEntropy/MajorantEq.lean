import FormalResearch.FourQubitEntropy.Majorant
import FormalResearch.FourQubitEntropy.PaperECriticalZeroOrbits

/-!
# Cubic spectral majorants: the equality clause under the paper's hypotheses

Paper E, `spectral_corollaries.tex`, `prop:fqe-majorant`: if the cubic `h = a x³ + b x² + c x + d`
majorises `f` on `[0,1]`, agrees with `f` at `1/6` and `1/2`, and `a > 0`, `α := -b - 17a/12 > 0`,
then `E_f(ψ) = E_f(M₄)` holds precisely on the two Hilbert-Schmidt LU orbits (those of `M₄` and
`conj M₄`). No strict majorisation of `f` by `h` off the nodes is assumed.

`Majorant.lean` proves this equality clause (`majorant_eq_iff`) only under the extra hypothesis
`hstrict : f < h` off the nodes. Here the paper's proof is formalised: equality in the gap identity
(`majorant_gap`) forces `P = 1` (as `α > 0`) and `F = 0` (as `a > 0`); the classification of the zeros
of `F` (`PaperECritical.moment_zeros`) puts `ψ` in one of five LU orbits, and the three Bell-pair
orbits have `P = 3/2 ≠ 1`.

`majorant_eq_iff_of_pos` is the new theorem. `majorant_eq_iff` is not derived from it (it allows
`a = 0`, which the paper's clause excludes, and `Majorant.lean` cannot import the zero-set
classification without a rebuild of its many dependents); the two statements are independent.
-/

namespace FormalResearch.FourQubitEntropy

open PaperECritical

/-- **`prop:fqe-majorant`, equality clause, paper hypotheses**: for a majorant cubic with `a > 0` and
`b + 17a/12 < 0` (both coefficient inequalities strict), and no hypothesis on `f` beyond
`Majorant f a b c d`, a unit four-qubit vector has `E_f(ψ) = E_f(M₄)` iff it is local-unitarily
equivalent to `M₄` or `conj M₄`. -/
theorem majorant_eq_iff_of_pos {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d) (ha : 0 < a)
    (hb : b + 17 * a / 12 < 0) (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    meanSpec f ψ = meanSpec f M4 ↔ LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ := by
  constructor
  · intro heq
    have g := majorant_gap hM ψ hψ
    have hP := purity_ge ψ
    rw [hψ] at hP
    have hF := sexticF_nonneg ψ
    have hs := majorantSlack_nonneg hM ψ hψ
    have k1 : 0 ≤ (-b - 17 * a / 12) * (purity ψ - 1) := mul_nonneg (by linarith) (by nlinarith)
    have k2 : 0 ≤ a / 12 * sexticF ψ := mul_nonneg (by linarith) hF
    rw [heq] at g
    have hP1 : purity ψ = 1 := by
      have : (-b - 17 * a / 12) * (purity ψ - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by linarith)
      · linarith
    have hF0 : sexticF ψ = 0 := by
      have : a / 12 * sexticF ψ = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by linarith)
      · exact h
    rcases (moment_zeros ψ hψ).mp hF0 with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
      rw [purity_localApply ha hb hc hd, bell2_vals.2.1] at hP1
      norm_num at hP1
    · exfalso
      obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
      rw [purity_localApply ha hb hc hd, bell13_vals.2.1] at hP1
      norm_num at hP1
    · exfalso
      obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
      rw [purity_localApply ha hb hc hd, bell14_vals.2.1] at hP1
      norm_num at hP1
  · rintro (h | h)
    · rw [meanSpec_of_LU f M4_unit M4_cutQuadratics h, meanSpec_M4]
    · rw [meanSpec_of_LU f (by rw [normSqPsi_conj]; exact M4_unit) M4_cutQuadratics.conj h,
        meanSpec_M4]

/-- info: 'FormalResearch.FourQubitEntropy.majorant_eq_iff_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms majorant_eq_iff_of_pos

end FormalResearch.FourQubitEntropy
