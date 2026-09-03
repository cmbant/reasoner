import Mathlib
import FormalResearch.QIB2.HammingGate

namespace FormalResearch.QIB2

open Complex
open scoped BigOperators

/-- Scalar swap eigenvalue on a simultaneous swap-eigenvector: `-1` on an
odd/singlet rung and `+1` on a triplet/even rung. -/
def swapEigenvalue {ι : Type*} [DecidableEq ι] (odd : Finset ι) (i : ι) : ℂ :=
  if i ∈ odd then -1 else 1

lemma canonical_gate_on_swap_eigenvalue {ι : Type*} [DecidableEq ι]
    (odd : Finset ι) (i : ι) :
    gateA + gateB * swapEigenvalue odd i = if i ∈ odd then I else 1 := by
  by_cases h : i ∈ odd
  · simp [swapEigenvalue, h, canonical_gate_at_minus]
  · simp [swapEigenvalue, h, canonical_gate_at_plus]

/-- Exact finite-copy phase law: on a joint swap eigenvector with odd-rung set
`odd`, the tensor-product flagship gate has phase `i` to the number of odd
rungs.  This is the scalar spectral statement behind `U_d = sum_m i^m E_m`. -/
theorem canonical_gate_phase_by_odd_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (odd : Finset ι) :
    (∏ i : ι, (gateA + gateB * swapEigenvalue odd i)) = I ^ odd.card := by
  simp_rw [canonical_gate_on_swap_eigenvalue]
  rw [Finset.prod_ite_mem_eq]
  simp [Finset.prod_const]

/-- Specialization to `d` Hamming rungs. -/
theorem canonical_gate_phase_fin {d : Nat} (odd : Finset (Fin d)) :
    (∏ i : Fin d, (gateA + gateB * swapEigenvalue odd i)) = I ^ odd.card :=
  canonical_gate_phase_by_odd_count odd

end FormalResearch.QIB2
