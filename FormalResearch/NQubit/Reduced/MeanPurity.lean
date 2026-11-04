module

public import FormalResearch.NQubit.Reduced.PartialTrace
public import FormalResearch.NQubit.TimeReversal.OddSector

/-!
# Mean purities of cuts

* `meanRdmPurity ψ k = C(n,k)^{-1} Σ_{|S| = k} tr (ρ_S²)` with `ρ_S = rdm ψ S` the explicit partial trace;
  `meanRdmPurity_eq_meanPurity` identifies it with `meanPurity` (the swap form);
* `meanPurity_eq_lin`: `a_s = Σ_j aQ n s j · A_j`, `aQ n s j = C(n-j,s-j)/(2^s C(n,s))` for `j ≤ s`;
* `meanPurity_compl`: `a_s = a_{n-s}` for a pure state.
-/

@[expose] public section


open scoped ComplexConjugate BigOperators
open FormalResearch.NQubit.Pauli
open FormalResearch.NQubit.TimeReversal

namespace FormalResearch.NQubit.Reduced

/-! ### The mean purities `a_s` -/

/-- `π_k(ψ) = C(n,k)^{-1} Σ_{|S|=k} tr(ρ_S²)` with `ρ_S` the explicit partial trace. -/
noncomputable def meanRdmPurity {n : ℕ} (ψ : Ψ n) (k : ℕ) : ℝ :=
  (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (Matrix.trace (rdm ψ S * rdm ψ S)).re)
    / (Nat.choose n k : ℝ)

theorem meanRdmPurity_eq_meanPurity {n : ℕ} (ψ : Ψ n) (k : ℕ) : meanRdmPurity ψ k = meanPurity ψ k := by
  unfold meanRdmPurity meanPurity cutPuritySum cutPuritySumOn
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← swapPurity_eq_trace]
  rfl

/-- The coefficient of `A_j` in `a_s`. -/
def aQ (n s j : ℕ) : ℚ :=
  if j ≤ s then (Nat.choose (n - j) (s - j) : ℚ) / (2 ^ s * (Nat.choose n s : ℚ)) else 0

/-- `a_s = (2^s C(n,s))^{-1} Σ_{j ≤ s} C(n-j,s-j) A_j`. -/
theorem meanPurity_eq_lin {n : ℕ} (ψ : Ψ n) {s : ℕ} (hs : s ≤ n) :
    meanPurity ψ s = ∑ j ∈ Finset.range (n + 1), (aQ n s j : ℝ) * weightEnum ψ j := by
  have h := cutPuritySum_eq ψ s
  have hC : (Nat.choose n s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hs).ne'
  have h2 : (2 : ℝ) ^ s ≠ 0 := by positivity
  unfold meanPurity
  rw [div_eq_iff hC]
  have h3 : cutPuritySum ψ s = (∑ j ∈ Finset.range (n + 1),
      (if j ≤ s then (Nat.choose (n - j) (s - j) : ℝ) else 0) * weightEnum ψ j) / 2 ^ s := by
    rw [← h]; field_simp
  rw [h3, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold aQ
  by_cases hj : j ≤ s
  · simp only [hj, ite_true]; push_cast; field_simp
  · simp [hj]

/-- **`a_s = a_{n-s}`** for a pure state. -/
theorem meanPurity_compl {n : ℕ} (ψ : Ψ n) {s : ℕ} (hs : s ≤ n) : meanPurity ψ s = meanPurity ψ (n - s) := by
  unfold meanPurity
  rw [cutPuritySum_compl ψ s hs, ← Nat.choose_symm hs]

end FormalResearch.NQubit.Reduced
