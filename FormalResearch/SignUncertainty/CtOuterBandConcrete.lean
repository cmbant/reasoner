module

public import FormalResearch.SignUncertainty.CtOuterBandMain
public import FormalResearch.SignUncertainty.CtMDeriv

/-!
# The dispersion `m = hankelEdgeM` satisfies the hypotheses of the outer-band theorem

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4 (`mat:T4`(f)(M2):
`τ/(1+τ²) ≤ m' ≤ (π²/6) τ/(1+τ²)`; `|m^{(k)}| ≤ C_k (1+τ)^{-k}`).  **Proved.**
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtOsc

open CtMDeriv CtOuter

lemma iteratedDeriv_one_m {τ : ℝ} (hτ : 0 < τ) : iteratedDeriv 1 hankelEdgeM τ = mPrime τ := by
  rw [iteratedDeriv_succ', (deriv_hankelEdgeM_eventually hτ).iteratedDeriv_eq 0]
  simp

/-- `m = hankelEdgeM` with `m', m'', m'''` is `MData C₀` for some `C₀ > 0`. -/
theorem mdata_hankel : ∃ C0 : ℝ, 0 < C0 ∧
    MData C0 hankelEdgeM (iteratedDeriv 1 hankelEdgeM) (iteratedDeriv 2 hankelEdgeM) (iteratedDeriv 3 hankelEdgeM) := by
  obtain ⟨C2, h2⟩ := m_iter_bound 2 (by norm_num)
  obtain ⟨C3, h3⟩ := m_iter_bound 3 (by norm_num)
  have hpi := Real.pi_pos
  set C0 : ℝ := max (π ^ 2 / 6) (max C2 C3) with hC0
  have hC0p : 0 < C0 := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C0, hC0p, ?_⟩
  refine
    { C0nn := hC0p.le
      d0 := fun τ hτ => ?_
      d1 := fun τ hτ => ?_
      d2 := fun τ hτ => ?_
      c3 := ?_
      lo := fun τ hτ => ?_
      hi := fun τ hτ => ?_
      b2 := fun τ hτ => ?_
      b3 := fun τ hτ => ?_ }
  · simpa using hasDerivAt_m_iter 0 hτ
  · simpa using hasDerivAt_m_iter 1 hτ
  · simpa using hasDerivAt_m_iter 2 hτ
  · intro τ hτ
    exact (hasDerivAt_m_iter 3 hτ).continuousAt.continuousWithinAt
  · rw [iteratedDeriv_one_m hτ]; exact (mPrime_bounds hτ).1
  · rw [iteratedDeriv_one_m hτ]
    refine (mPrime_bounds hτ).2.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have := h2 τ hτ
    refine this.trans ?_
    exact div_le_div_of_nonneg_right ((le_max_left C2 C3).trans (le_max_right _ _)) (by positivity)
  · have := h3 τ hτ
    refine this.trans ?_
    exact div_le_div_of_nonneg_right ((le_max_right C2 C3).trans (le_max_right _ _)) (by positivity)

end FormalResearch.SignUncertainty.CtOsc
