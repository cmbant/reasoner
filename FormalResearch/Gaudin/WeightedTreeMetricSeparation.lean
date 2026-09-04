import Mathlib
import FormalResearch.Gaudin.WeightedTreeMetric

namespace FormalResearch.Gaudin

/-- A single Boolean mismatch vanishes exactly when the bits agree. -/
theorem bitMismatch_eq_zero_iff (a b : Bool) :
    bitMismatch a b = 0 ↔ a = b := by
  simp [bitMismatch]

/-- Hamming distance on Boolean indicator functions separates points. -/
theorem hamming_eq_zero_iff {ι : Type*} [Fintype ι]
    (a b : ι → Bool) :
    hamming a b = 0 ↔ a = b := by
  unfold hamming
  rw [Finset.sum_eq_zero_iff]
  simp [bitMismatch_eq_zero_iff, funext_iff]

/-- With positive edge and vertex weights, the Gaudin weighted tree distance
vanishes exactly when both encoded incidence systems agree. -/
theorem weightedTreeDistance_eq_zero_iff
    {E V : Type*} [Fintype E] [Fintype V]
    {ell nu : Nat} (hEll : 0 < ell) (hNu : 0 < nu)
    (e₁ e₂ : E → Bool) (v₁ v₂ : V → Bool) :
    weightedTreeDistance ell nu e₁ e₂ v₁ v₂ = 0 ↔
      e₁ = e₂ ∧ v₁ = v₂ := by
  simp [weightedTreeDistance, hamming_eq_zero_iff,
    Nat.ne_of_gt hEll, Nat.ne_of_gt hNu]

/-- Positive-weight weighted tree distance is strictly positive for distinct
encoded tree data. -/
theorem weightedTreeDistance_pos_iff
    {E V : Type*} [Fintype E] [Fintype V]
    {ell nu : Nat} (hEll : 0 < ell) (hNu : 0 < nu)
    (e₁ e₂ : E → Bool) (v₁ v₂ : V → Bool) :
    0 < weightedTreeDistance ell nu e₁ e₂ v₁ v₂ ↔
      e₁ ≠ e₂ ∨ v₁ ≠ v₂ := by
  rw [Nat.pos_iff_ne_zero, ne_eq,
    weightedTreeDistance_eq_zero_iff hEll hNu e₁ e₂ v₁ v₂]
  tauto

end FormalResearch.Gaudin
