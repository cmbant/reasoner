import FormalResearch.QIA.MatrixTraceAdjoint

/-!
# QI-A trace preservation and Heisenberg unitality

For finite matrix algebras, trace preservation of a Schrödinger-picture linear
map is equivalent to unitality of its canonical trace adjoint. This is the
finite algebraic part of the standard Schrödinger/Heisenberg channel bridge.

No positivity or complete positivity statement is made here.
-/

namespace FormalResearch.QIA

noncomputable section

/-- A trace-preserving finite matrix linear map has unital canonical trace
adjoint. -/
theorem matrixTraceAdjoint_one_eq_one_of_tracePreserving
    {h q : Type*} [Fintype h] [DecidableEq h] [Fintype q] [DecidableEq q]
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ)
    (hTP : ∀ X : Matrix h h ℂ, Matrix.trace (C X) = Matrix.trace X) :
    matrixTraceAdjoint C (1 : Matrix q q ℂ) = (1 : Matrix h h ℂ) := by
  apply (Matrix.ext_iff_trace_mul_right).2
  intro X
  rw [← matrixTraceAdjoint_spec C (1 : Matrix q q ℂ) X]
  simpa using hTP X

/-- Conversely, unitality of the canonical trace adjoint is exactly trace
preservation of the Schrödinger-picture map. -/
theorem matrixTraceAdjoint_one_eq_one_iff_tracePreserving
    {h q : Type*} [Fintype h] [DecidableEq h] [Fintype q] [DecidableEq q]
    (C : Matrix h h ℂ →ₗ[ℂ] Matrix q q ℂ) :
    matrixTraceAdjoint C (1 : Matrix q q ℂ) = (1 : Matrix h h ℂ) ↔
      ∀ X : Matrix h h ℂ, Matrix.trace (C X) = Matrix.trace X := by
  constructor
  · intro hunital X
    have hspec := matrixTraceAdjoint_spec C (1 : Matrix q q ℂ) X
    rw [hunital] at hspec
    simpa using hspec
  · exact matrixTraceAdjoint_one_eq_one_of_tracePreserving C

end

end FormalResearch.QIA
