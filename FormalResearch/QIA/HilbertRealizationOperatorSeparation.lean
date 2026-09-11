import FormalResearch.QIA.HermitianCoherentPowerSeparation
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Hilbert-realization operator separation for QI-A

The algebraic `SymmetricPower` quotient does not carry a canonical norm or inner product in
Mathlib.  This module therefore keeps the Hilbert realization explicit: a linear equivalence
from algebraic symmetric power into the chosen physical Hilbert model is supplied as data.

Under that realization, a symmetric linear operator whose coherent quadratic statistic
vanishes is zero.  The only continuity hypothesis is the same pullback continuity already
used by the coherent-power spanning bridge; constructing the concrete physical realization
and discharging this continuity hypothesis remain separate model-specific steps.
-/

namespace FormalResearch.QIA

open scoped TensorProduct InnerProductSpace

noncomputable section

/-- Pull a Hilbert-space operator back to a sesquilinear form on algebraic symmetric power
through an explicit linear Hilbert realization. -/
def symmetricPowerOperatorForm
    {E H : Type*} [AddCommMonoid E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ}
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ] H)
    (A : H →ₗ[ℂ] H) :
    SymmetricPower ℂ (Fin n) E →ₗ⋆[ℂ]
      SymmetricPower ℂ (Fin n) E →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ _ _
    (fun u v => inner ℂ (ι u) (A (ι v)))
    (by intro u₁ u₂ v; simp [inner_add_left])
    (by intro c u v; simp [inner_smul_left, smul_eq_mul])
    (by intro u v₁ v₂; simp [inner_add_right])
    (by intro c u v; simp [inner_smul_right, smul_eq_mul])

@[simp] theorem symmetricPowerOperatorForm_apply
    {E H : Type*} [AddCommMonoid E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ}
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ] H)
    (A : H →ₗ[ℂ] H)
    (u v : SymmetricPower ℂ (Fin n) E) :
    symmetricPowerOperatorForm ι A u v = inner ℂ (ι u) (A (ι v)) := rfl

/-- A symmetric Hilbert-space operator pulls back to a Hermitian sesquilinear form. -/
theorem symmetricPowerOperatorForm_isSymm
    {E H : Type*} [AddCommMonoid E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ}
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ] H)
    (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric) :
    (symmetricPowerOperatorForm ι A).IsSymm := by
  constructor
  intro u v
  change star (inner ℂ (ι u) (A (ι v))) = inner ℂ (ι v) (A (ι u))
  calc
    star (inner ℂ (ι u) (A (ι v))) =
        inner ℂ (A (ι v)) (ι u) := by
      simpa only [starRingEnd_apply] using
        (inner_conj_symm (A (ι v)) (ι u))
    _ = inner ℂ (ι v) (A (ι u)) := hA (ι v) (ι u)

/-- Operator form of coherent-copy separation through an explicit Hilbert realization.

This is the direct operator-level specialization of
`symmetricPower_hermitian_form_eq_zero_of_coherent_diagonal`.  It deliberately does not
postulate a canonical Hilbert structure on algebraic `SymmetricPower`: the realization `ι`
is explicit, so later source-specific work can identify it with the physical symmetric
subspace used in QI-A. -/
theorem symmetricPower_hilbert_realization_operator_eq_zero_of_coherent_diagonal
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ}
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ] H)
    (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric)
    (hcont : ∀ u : SymmetricPower ℂ (Fin n) E,
      Continuous fun v : Fin n → E =>
        inner ℂ (ι u) (A (ι (SymmetricPower.tprod ℂ v))))
    (hdiag : ∀ x : E,
      inner ℂ
        (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))
        (A (ι (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))) = 0) :
    A = 0 := by
  let B := symmetricPowerOperatorForm ι A
  have hBsymm : B.IsSymm := by
    dsimp [B]
    exact symmetricPowerOperatorForm_isSymm ι A hA
  have hBzero : B = 0 :=
    symmetricPower_hermitian_form_eq_zero_of_coherent_diagonal
      B hBsymm
      (by
        intro u
        simpa [B] using hcont u)
      (by
        intro x
        simpa [B] using hdiag x)
  apply LinearMap.ext
  intro v
  have hv : B (ι.symm (A v)) (ι.symm v) = 0 := by
    rw [hBzero]
    rfl
  have hv' : inner ℂ (A v) (A v) = 0 := by
    simpa [B] using hv
  simpa using inner_self_eq_zero.mp hv'

end

end FormalResearch.QIA
