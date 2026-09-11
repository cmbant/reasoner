import FormalResearch.QIA.SymmetricMultilinearDiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-!
# Coherent powers separate scalar functionals on symmetric tensor power

This module is the first source-faithful bridge from the abstract diagonal-polarization
lemma to QI-A's actual symmetric tensor model.  A complex-linear scalar functional on
`Sym[ℂ]^n E` is zero once its pullback along the canonical symmetric tensor map is
continuous and vanishes on every coherent power `x^{⊙ n}`.

The result intentionally stops short of QI-A's Hermitian coherent-copy separation lemma:
the remaining step is the genuinely bidegree-`(n,n)` passage from a Hermitian operator's
quadratic statistic to scalar functionals of this kind.
-/

namespace FormalResearch.QIA

open Equiv
open scoped TensorProduct

noncomputable section

/-- A scalar linear functional on the actual complex symmetric tensor power is determined
by its values on coherent powers, provided its pullback along the canonical symmetric
multilinear map is continuous.

This is the concrete `SymmetricPower` bridge supplied by diagonal polarization; it does
not identify the Hermitian bidegree-`(n,n)` form needed for the full operator statement. -/
theorem symmetricPower_linear_eq_zero_of_coherent_power
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (L : SymmetricPower ℂ (Fin n) E →ₗ[ℂ] ℂ)
    (hcont : Continuous fun v : Fin n → E => L (SymmetricPower.tprod ℂ v))
    (hdiag : ∀ x : E,
      L (SymmetricPower.tprod ℂ (fun _ : Fin n => x)) = 0) :
    L = 0 := by
  let f : E [×n]→L[ℂ] ℂ :=
    ⟨L.compMultilinearMap (SymmetricPower.tprod ℂ), hcont⟩
  have hsymm : ∀ σ : Equiv.Perm (Fin n),
      (f.restrictScalars ℝ).domDomCongr σ = f.restrictScalars ℝ := by
    intro σ
    apply ContinuousMultilinearMap.ext
    intro v
    change L (SymmetricPower.tprod ℂ (fun i => v (σ i))) =
      L (SymmetricPower.tprod ℂ v)
    rw [SymmetricPower.tprod_equiv]
  have hdiag' : ∀ x : E, (f.restrictScalars ℝ) (fun _ => x) = 0 := by
    intro x
    exact hdiag x
  have hfR : f.restrictScalars ℝ = 0 :=
    continuousMultilinearMap_eq_zero_of_symmetric_diagonal
      (f := f.restrictScalars ℝ) hsymm hdiag'
  have htprod : ∀ v : Fin n → E, L (SymmetricPower.tprod ℂ v) = 0 := by
    intro v
    have h := congrArg (fun g : E [×n]→L[ℝ] ℂ => g v) hfR
    simpa [f] using h
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℂ
      (Set.range (SymmetricPower.tprod ℂ (ι := Fin n) (M := E))) := by
    rw [SymmetricPower.span_tprod_eq_top]
    exact Submodule.mem_top
  refine Submodule.span_induction hx ?_ (by simp) ?_ ?_
  · intro y hy
    rcases hy with ⟨v, rfl⟩
    exact htprod v
  · intro y z hy hz
    simp [hy, hz]
  · intro a y hy
    simp [hy]

end

end FormalResearch.QIA
