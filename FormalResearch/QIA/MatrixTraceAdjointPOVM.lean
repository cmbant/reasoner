import FormalResearch.QIA.MatrixTraceAdjointPositivity
import FormalResearch.QIA.MatrixTraceAdjointUnital

/-!
# QI-A POVM transport through the finite matrix trace adjoint

For a finite matrix encoding, positivity of the Schrodinger-picture map makes
its canonical trace adjoint positive, while trace preservation makes that
adjoint unital. Therefore every target POVM pulls back to a genuine source
POVM: each effect remains positive semidefinite and the effects still sum to
the identity.

This is the finite-dimensional Heisenberg-picture POVM bridge. It does not
assert complete positivity or construct the concrete QI-A channel.
-/

namespace FormalResearch.QIA

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

/-- A positive, trace-preserving finite matrix encoding pulls every target POVM
back through `matrixTraceAdjoint` to a source POVM. -/
theorem matrixTraceAdjoint_povm_of_posSemidef_preserving_tracePreserving
    {J h q : Type*} [Fintype J]
    [Fintype h] [DecidableEq h] [Fintype q] [DecidableEq q]
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (hCpos : ∀ X : Matrix h h ℂ, X.PosSemidef → (C X).PosSemidef)
    (hTP : ∀ X : Matrix h h ℂ, Matrix.trace (C X) = Matrix.trace X)
    (F : J → Matrix q q ℂ)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ)) :
    (∀ j, (matrixTraceAdjoint C (F j)).PosSemidef) ∧
      (∑ j, matrixTraceAdjoint C (F j)) = (1 : Matrix h h ℂ) := by
  constructor
  · intro j
    exact matrixTraceAdjoint_posSemidef_of_posSemidef_preserving
      C hCpos (hFpos j)
  · rw [← map_sum, hPOVM]
    exact matrixTraceAdjoint_one_eq_one_of_tracePreserving C hTP

/-- Consequently, the pulled-back POVM statistics sum to the source trace. -/
theorem sum_trace_matrixTraceAdjoint_povm_eq_trace
    {J h q : Type*} [Fintype J]
    [Fintype h] [DecidableEq h] [Fintype q] [DecidableEq q]
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (hCpos : ∀ X : Matrix h h ℂ, X.PosSemidef → (C X).PosSemidef)
    (hTP : ∀ X : Matrix h h ℂ, Matrix.trace (C X) = Matrix.trace X)
    (F : J → Matrix q q ℂ)
    (hFpos : ∀ j, (F j).PosSemidef)
    (hPOVM : (∑ j, F j) = (1 : Matrix q q ℂ))
    (X : Matrix h h ℂ) :
    (∑ j, Matrix.trace (matrixTraceAdjoint C (F j) * X)) = Matrix.trace X := by
  have hPB :=
    (matrixTraceAdjoint_povm_of_posSemidef_preserving_tracePreserving
      C hCpos hTP F hFpos hPOVM).2
  calc
    (∑ j, Matrix.trace (matrixTraceAdjoint C (F j) * X)) =
        Matrix.trace ((∑ j, matrixTraceAdjoint C (F j)) * X) := by
      simp [Finset.sum_mul]
    _ = Matrix.trace X := by simp [hPB]

end

end FormalResearch.QIA
