module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperMainInputs
public import FormalResearch.Special.AiryPrimitiveNeg

/-!
# `cts:tip-shared` (c): decay of the Airy primitives

`airyPrimitiveDecay : AiryPrimitiveDecay` (**proved, unconditional**): `B(t) = O(|t|^{-3/4})` and
`C(t) = t B(t) - Ai'(t) = O(|t|^{-5/4})` as `t → -∞`.  The proof (`Special.AiryPrimitiveNeg`) integrates by parts once with
`Ai'' = x Ai` and uses only the envelope bounds of `Ai`, `Ai'` on the negative axis, so the oscillatory second-order terms
of the paper (DLMF 9.7.5, 9.7.9-10) are not needed.  Here `airyPrimB` (`1 - ∫_{Ioi t} Ai`) is identified with
`Bneg t = 2/3 - ∫_t^0 Ai`.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.Special.AiryPrimNeg

lemma airyPrimB_eq {t : ℝ} (ht : t ≤ 0) : airyPrimB t = Bneg t := by
  have hi : ∀ a b : ℝ, IntervalIntegrable airyAi volume a b :=
    fun a b => differentiable_airyAi.continuous.intervalIntegrable _ _
  have h0 : IntegrableOn airyAi (Ioi 0) := integrableOn_airyAi_Ioi
  have h1 : IntegrableOn airyAi (Ioc t 0) := (hi t 0).1
  have hU : (∫ s in Ioi t, airyAi s) = (∫ s in t..0, airyAi s) + 1 / 3 := by
    have := setIntegral_union (μ := volume) (f := airyAi) (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h0
    rw [Ioc_union_Ioi_eq_Ioi ht, integral_Ioi_airyAi, ← intervalIntegral.integral_of_le ht] at this
    exact this
  unfold airyPrimB Bneg
  rcases ht.eq_or_lt with rfl | hlt
  · simp only [lt_self_iff_false, ite_false]
    rw [hU]; simp; norm_num
  · simp only [not_lt.mpr ht, ite_false]
    rw [hU]; ring

/-- **`cts:tip-shared` (c)**: `B(t) = O(|t|^{-3/4})`, `C(t) = O(|t|^{-5/4})` as `t → -∞`. -/
theorem airyPrimitiveDecay : AiryPrimitiveDecay := by
  refine ⟨16, fun t ht => ?_⟩
  have h := Bneg_decay ht
  have hB := airyPrimB_eq (t := t) (by linarith)
  have habs : |t| = -t := abs_of_neg (by linarith)
  unfold airyPrimC
  rw [hB, habs]
  exact h

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.airyPrimitiveDecay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyPrimitiveDecay

end FormalResearch.ModularBootstrap.FiveTerm
