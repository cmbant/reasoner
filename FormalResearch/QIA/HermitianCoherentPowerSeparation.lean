import FormalResearch.QIA.CoherentPowerSymmetricSpan
import FormalResearch.QIA.CoherentPhaseOrthogonality
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-!
# Hermitian coherent-power separation on symmetric tensor power

This module combines the finite phase extraction for bidegree `(n,n)` forms with the
coherent-power spanning theorem on `SymmetricPower`.  It gives the source-facing
sesquilinear form version of QI-A's coherent-copy separation lemma: a Hermitian form on
the actual symmetric tensor power is zero when its quadratic statistic vanishes on every
coherent power, under the continuity hypothesis needed by the existing polarization
bridge.
-/

namespace FormalResearch.QIA

open scoped TensorProduct

noncomputable section

/-- On the actual symmetric tensor power, vanishing of a sesquilinear form on the
coherent diagonal already forces all coherent cross terms to vanish.  This step does
not require Hermitian symmetry. -/
theorem symmetricPower_sesquilinear_coherent_cross_eq_zero_of_diagonal
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    {n : ℕ}
    (B : SymmetricPower ℂ (Fin n) E →ₗ⋆[ℂ]
      SymmetricPower ℂ (Fin n) E →ₗ[ℂ] ℂ)
    (hdiag : ∀ x : E,
      B (SymmetricPower.tprod ℂ (fun _ : Fin n => x))
        (SymmetricPower.tprod ℂ (fun _ : Fin n => x)) = 0)
    (x y : E) :
    B (SymmetricPower.tprod ℂ (fun _ : Fin n => x))
      (SymmetricPower.tprod ℂ (fun _ : Fin n => y)) = 0 := by
  exact sesquilinear_coherent_cross_eq_zero_of_diagonal
    (SymmetricPower.tprod ℂ) B hdiag x y

/-- Hermitian coherent-copy separation on the algebraic symmetric tensor power.

A Hermitian sesquilinear form is zero if its coherent diagonal vanishes.  The only
analytic input is continuity of each right pullback along the canonical symmetric
tensor map, exactly the hypothesis used by `symmetricPower_linear_eq_zero_of_coherent_power`.
This is the form-level bridge corresponding to the manuscript's Hermitian operator
separation lemma; identifying a concrete Hilbert-space operator with such a form is a
separate specialization. -/
theorem symmetricPower_hermitian_form_eq_zero_of_coherent_diagonal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ}
    (B : SymmetricPower ℂ (Fin n) E →ₗ⋆[ℂ]
      SymmetricPower ℂ (Fin n) E →ₗ[ℂ] ℂ)
    (hB : B.IsSymm)
    (hcont : ∀ u : SymmetricPower ℂ (Fin n) E,
      Continuous fun v : Fin n → E => B u (SymmetricPower.tprod ℂ v))
    (hdiag : ∀ x : E,
      B (SymmetricPower.tprod ℂ (fun _ : Fin n => x))
        (SymmetricPower.tprod ℂ (fun _ : Fin n => x)) = 0) :
    B = 0 := by
  have hcross : ∀ x y : E,
      B (SymmetricPower.tprod ℂ (fun _ : Fin n => x))
        (SymmetricPower.tprod ℂ (fun _ : Fin n => y)) = 0 := by
    intro x y
    exact symmetricPower_sesquilinear_coherent_cross_eq_zero_of_diagonal B hdiag x y
  have hleft : ∀ x : E,
      B (SymmetricPower.tprod ℂ (fun _ : Fin n => x)) = 0 := by
    intro x
    exact symmetricPower_linear_eq_zero_of_coherent_power
      (B (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))
      (hcont (SymmetricPower.tprod ℂ (fun _ : Fin n => x)))
      (hcross x)
  have hright : ∀ (u : SymmetricPower ℂ (Fin n) E) (x : E),
      B u (SymmetricPower.tprod ℂ (fun _ : Fin n => x)) = 0 := by
    intro u x
    apply hB.isRefl.eq_zero
    rw [hleft x]
    rfl
  have hu : ∀ u : SymmetricPower ℂ (Fin n) E, B u = 0 := by
    intro u
    exact symmetricPower_linear_eq_zero_of_coherent_power
      (B u) (hcont u) (hright u)
  apply LinearMap.ext
  intro u
  exact hu u

end

end FormalResearch.QIA