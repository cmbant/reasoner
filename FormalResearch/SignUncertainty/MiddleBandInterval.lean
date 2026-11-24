module

public import Mathlib
public import FormalResearch.CohnElkies.TwoIBPPhase

/-!
# Whole-line integrals versus interval integrals (`GT.2a`, more 1)

Elementary reductions between the integral over `ℝ` and interval integrals, for a function `h`
vanishing off a compact interval (or off two symmetric half-intervals).

* `mb_integral_eq_interval`: if `h = 0` off `[α, β]`, then `∫ h` over `ℝ` equals `∫ x in α..β, h x`.
  Classes: proved. Mostly a restatement of Mathlib's `setIntegral_eq_integral_of_forall_compl_eq_zero`
  together with the interval-to-`Icc` conversion `twoIbp_interval_eq_Icc` (from
  `FormalResearch.CohnElkies.TwoIBPPhase`).
* `mb_integral_split_two_halves`: if `h = 0` off `[-β, -α] ∪ [α, β]` with `0 < α ≤ β` and `h` integrable,
  then `∫ h` is the sum of the two interval integrals over `[-β, -α]` and `[α, β]`. Classes: proved.
  The hypothesis `0 < α` gives disjointness of the two halves: for `α = 0` they meet at `0`, and the
  split (which needs disjointness for `setIntegral_union`) is not claimed there.
* `mb_norm_integral_le_two_halves`: the triangle-inequality consequence of the split. Classes: proved.

The first theorem assumes no integrability: the set-integral identity holds for every `h`, with Mathlib's
convention that a non-integrable function has integral `0` on both sides.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The whole-line integral of a function vanishing off `[α, β]` (with `α ≤ β`) is the interval
integral over `α..β`. Classes: proved (restates Mathlib's `setIntegral_eq_integral_of_forall_compl_eq_zero`
and `twoIbp_interval_eq_Icc`). -/
theorem mb_integral_eq_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℝ → E}
    {α β : ℝ} (hαβ : α ≤ β) (hsupp : ∀ x, x ∉ Set.Icc α β → h x = 0) :
    ∫ x, h x = ∫ x in α..β, h x := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    FormalResearch.CohnElkies.twoIbp_interval_eq_Icc hαβ]

/-- Splitting the whole-line integral of a function vanishing off the two symmetric half-intervals
`[-β, -α] ∪ [α, β]` into the two interval integrals, for `0 < α ≤ β` and `h` integrable.
Classes: proved. The hypothesis `0 < α` makes the two halves disjoint (`-α < 0 < α`). -/
theorem mb_integral_split_two_halves {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ → E} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ x, x ∉ Set.Icc (-β) (-α) ∪ Set.Icc α β → h x = 0)
    (hint : MeasureTheory.Integrable h) :
    ∫ x, h x = (∫ x in (-β)..(-α), h x) + ∫ x in α..β, h x := by
  have hdisj : Disjoint (Set.Icc (-β) (-α)) (Set.Icc α β) :=
    Set.disjoint_left.2 fun x hx1 hx2 => by linarith [hx1.2, hx2.1]
  have hneg : -β ≤ -α := by linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    MeasureTheory.setIntegral_union hdisj measurableSet_Icc hint.integrableOn hint.integrableOn,
    FormalResearch.CohnElkies.twoIbp_interval_eq_Icc hneg,
    FormalResearch.CohnElkies.twoIbp_interval_eq_Icc hαβ]

/-- The norm of the whole-line integral is at most the sum of the norms of the two interval integrals
(same hypotheses as `mb_integral_split_two_halves`). Classes: proved (from the split and the triangle
inequality `norm_add_le`). -/
theorem mb_norm_integral_le_two_halves {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ → E} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ x, x ∉ Set.Icc (-β) (-α) ∪ Set.Icc α β → h x = 0)
    (hint : MeasureTheory.Integrable h) :
    ‖∫ x, h x‖ ≤ ‖∫ x in (-β)..(-α), h x‖ + ‖∫ x in α..β, h x‖ := by
  rw [mb_integral_split_two_halves hα hαβ hsupp hint]
  exact norm_add_le _ _

/-! `#print axioms` guards. -/

/-- info: 'FormalResearch.SignUncertainty.mb_integral_eq_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_integral_eq_interval

/-- info: 'FormalResearch.SignUncertainty.mb_integral_split_two_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_integral_split_two_halves

/-- info: 'FormalResearch.SignUncertainty.mb_norm_integral_le_two_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_norm_integral_le_two_halves

end FormalResearch.SignUncertainty
