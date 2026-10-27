import Mathlib
import FormalResearch.FrameFree.PolyImageBasic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Polynomial images: the point set of a finitely generated algebra

Namespace `FormalResearch.FrameFree.PolyImage`.

For generators `y : ι → B` of a `ℂ`-algebra `B`, `pointSet y = {p | ∃ ζ : B →ₐ[ℂ] ℂ, ∀ i, ζ (y i) = p i}` is the
zero locus of the relations (`mem_pointSet_iff`), hence closed (`isClosed_pointSet`).  Also the specialisation
of a polynomial relation at a point: `isRoot_map_of_point`.
-/

namespace FormalResearch.FrameFree.PolyImage

open Polynomial

section

variable {B : Type*} [CommRing B] [Algebra ℂ B] {ι : Type*}

/-- Points of `B` in the coordinates given by the generators `y`. -/
def pointSet (y : ι → B) : Set (ι → ℂ) := {p | ∃ ζ : B →ₐ[ℂ] ℂ, ∀ i, ζ (y i) = p i}

theorem mem_pointSet_iff (y : ι → B) (hy : Function.Surjective (MvPolynomial.aeval y : MvPolynomial ι ℂ →ₐ[ℂ] B))
    (p : ι → ℂ) :
    p ∈ pointSet y ↔ ∀ q : MvPolynomial ι ℂ, MvPolynomial.aeval y q = 0 → MvPolynomial.eval p q = 0 := by
  constructor
  · rintro ⟨ζ, hζ⟩ q hq
    have h1 : ζ (MvPolynomial.aeval y q) = MvPolynomial.aeval (fun i => ζ (y i)) q := by
      rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    rw [hq, map_zero] at h1
    have h2 : (fun i => ζ (y i)) = p := funext hζ
    rw [h2] at h1
    simpa [MvPolynomial.coe_aeval_eq_eval] using h1.symm
  · intro h
    have hker : RingHom.ker (MvPolynomial.aeval y : MvPolynomial ι ℂ →ₐ[ℂ] B).toRingHom ≤
        RingHom.ker (MvPolynomial.aeval p : MvPolynomial ι ℂ →ₐ[ℂ] ℂ).toRingHom := by
      intro q hq
      have : MvPolynomial.aeval y q = 0 := hq
      have := h q this
      simpa [MvPolynomial.coe_aeval_eq_eval] using this
    refine ⟨AlgHom.liftOfSurjective _ hy _ hker, fun i => ?_⟩
    have := AlgHom.liftOfSurjective_apply (MvPolynomial.aeval y : MvPolynomial ι ℂ →ₐ[ℂ] B) hy
      (MvPolynomial.aeval p) hker (MvPolynomial.X i)
    simpa using this

theorem isClosed_pointSet (y : ι → B)
    (hy : Function.Surjective (MvPolynomial.aeval y : MvPolynomial ι ℂ →ₐ[ℂ] B)) :
    IsClosed (pointSet y) := by
  have : pointSet y = ⋂ q ∈ {q : MvPolynomial ι ℂ | MvPolynomial.aeval y q = 0},
      {p : ι → ℂ | MvPolynomial.eval p q = 0} := by
    ext p
    simp only [mem_pointSet_iff y hy, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

end

section

variable {d : ℕ} {B : Type*} [CommRing B] [Algebra ℂ B] [Algebra (MvPolynomial (Fin d) ℂ) B]
  [IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) B]

/-- A `ℂ`-point of `B` restricted to the base `ℂ[x₁..x_d]` is evaluation at its values on the `xⱼ`. -/
theorem comp_toAlgHom_eq (ζ : B →ₐ[ℂ] ℂ) :
    ζ.comp (IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin d) ℂ) B) =
      MvPolynomial.aeval (fun j => ζ (algebraMap (MvPolynomial (Fin d) ℂ) B (MvPolynomial.X j))) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp

theorem map_algebraMap_eq (ζ : B →ₐ[ℂ] ℂ) (p : MvPolynomial (Fin d) ℂ) :
    ζ (algebraMap (MvPolynomial (Fin d) ℂ) B p) =
      MvPolynomial.eval (fun j => ζ (algebraMap (MvPolynomial (Fin d) ℂ) B (MvPolynomial.X j))) p := by
  have := congrArg (fun φ : MvPolynomial (Fin d) ℂ →ₐ[ℂ] ℂ => φ p) (comp_toAlgHom_eq (B := B) ζ)
  simpa [MvPolynomial.coe_aeval_eq_eval] using this

/-- The value of a point at an element `u` is a root of the specialisation of any relation of `u`. -/
theorem isRoot_map_of_point (ζ : B →ₐ[ℂ] ℂ) (u : B) (F : (MvPolynomial (Fin d) ℂ)[X])
    (hF : Polynomial.aeval u F = 0) :
    (F.map (MvPolynomial.eval
      (fun j => ζ (algebraMap (MvPolynomial (Fin d) ℂ) B (MvPolynomial.X j))))).IsRoot (ζ u) := by
  have h1 : ζ (Polynomial.aeval u F) = Polynomial.eval₂
      ((ζ.toRingHom).comp (algebraMap (MvPolynomial (Fin d) ℂ) B)) (ζ u) F := by
    rw [Polynomial.aeval_def]
    exact Polynomial.hom_eval₂ F (algebraMap (MvPolynomial (Fin d) ℂ) B) ζ.toRingHom u
  have h2 : (ζ.toRingHom).comp (algebraMap (MvPolynomial (Fin d) ℂ) B) = MvPolynomial.eval
      (fun j => ζ (algebraMap (MvPolynomial (Fin d) ℂ) B (MvPolynomial.X j))) := by
    ext p
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.eval_C]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
      rfl
    · simp
  rw [hF, map_zero, h2] at h1
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  exact h1.symm

end

end FormalResearch.FrameFree.PolyImage
