import FormalResearch.QIA.ExactRecoveryHeisenbergMemoryBound
import FormalResearch.QIA.MatrixTraceAdjointUnital

/-!
# QI-A exact-recovery memory bound with the canonical trace adjoint

This module removes the arbitrary Heisenberg adjoint witness from the finite
exact-recovery converse. The adjoint is the canonical `matrixTraceAdjoint` of
the Schrödinger recovery map. Trace preservation supplies unitality of that
adjoint automatically.

The remaining genuinely physical adjoint-side input is positivity of the
canonical pullback. No complete-positivity theorem is proved here.
-/

namespace FormalResearch.QIA

noncomputable section

/-- Exact recovery through a trace-preserving recovery map forces the Hilbert
memory dimension bound when the canonical trace adjoint is positive. -/
theorem exactRecoveryCanonicalAdjoint_card_le_memory
    {J q : Type*} [Fintype J] [DecidableEq J]
    [Fintype q] [DecidableEq q]
    (omega : J → Matrix q q ℂ)
    (R : Matrix q q ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hRstarPos : ∀ A : Matrix J J ℂ,
      A.PosSemidef → (matrixTraceAdjoint R A).PosSemidef)
    (hRtrace : ∀ X : Matrix q q ℂ,
      Matrix.trace (R X) = Matrix.trace X)
    (hrecover : ∀ j, R (omega j) = coordinateProjector j)
    (homega : ∀ j, omega j ≤ (1 : Matrix q q ℂ)) :
    Fintype.card J ≤ Fintype.card q := by
  exact exactRecoveryAdjoint_card_le_memory
    omega R (matrixTraceAdjoint R) hRstarPos
      (matrixTraceAdjoint_one_eq_one_of_tracePreserving R hRtrace)
      (fun A X => matrixTraceAdjoint_spec R A X)
      hrecover homega

/-- QI-A multiplicity-profile specialization with the canonical adjoint. -/
theorem multiplicityMemoryDimension_le_of_exactRecoveryCanonicalAdjoint
    {α q : Type*} [Fintype α] [DecidableEq α]
    [Fintype q] [DecidableEq q]
    (g : α → Nat)
    (omega : multiplicityMemoryCarrier g → Matrix q q ℂ)
    (R : Matrix q q ℂ →ₗ[ℂ]
      Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ)
    (hRstarPos : ∀ A :
      Matrix (multiplicityMemoryCarrier g) (multiplicityMemoryCarrier g) ℂ,
      A.PosSemidef → (matrixTraceAdjoint R A).PosSemidef)
    (hRtrace : ∀ X : Matrix q q ℂ,
      Matrix.trace (R X) = Matrix.trace X)
    (hrecover : ∀ j, R (omega j) = coordinateProjector j)
    (homega : ∀ j, omega j ≤ (1 : Matrix q q ℂ)) :
    multiplicityMemoryDimension g ≤ Fintype.card q := by
  have h := exactRecoveryCanonicalAdjoint_card_le_memory
    omega R hRstarPos hRtrace hrecover homega
  rw [multiplicityMemoryCarrier_card g] at h
  exact h

end

end FormalResearch.QIA
