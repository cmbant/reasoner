import Mathlib
import FormalResearch.FrameFree.PolyImageBasic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Polynomial images: lifting points along integral extensions

Namespace `FormalResearch.FrameFree.PolyImage`.

* `exists_algHom_extend`: if `B` is a finitely generated `ℂ`-algebra, integral over a `ℂ`-subalgebra `A`, every
  `ℂ`-point of `A` extends to a `ℂ`-point of `B` (lying over + closed points).
* `exists_point_over`: let `P` be an integrally closed domain, `B ⊇ P` a finitely generated domain integral over
  `P`, `θ ∈ B`.  Every point `x` of `P` and root `r` of the minimal polynomial `minpoly P θ` evaluated at `x` come
  from a point `ζ` of `B` with `ζ θ = r` (because `P[θ] ≅ P[T]/(minpoly)`).
-/

namespace FormalResearch.FrameFree.PolyImage

open Polynomial

/-- Points of a subalgebra over which the ambient algebra is integral extend. -/
theorem exists_algHom_extend {B : Type*} [CommRing B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (A : Subalgebra ℂ B) [hint : Algebra.IsIntegral A B] (ψ : A →ₐ[ℂ] ℂ) :
    ∃ ζ : B →ₐ[ℂ] ℂ, ζ.comp A.val = ψ := by
  have hsurj : Function.Surjective (ψ : A →+* ℂ) := fun c => ⟨algebraMap ℂ A c, by simp⟩
  have hmax : (RingHom.ker (ψ : A →+* ℂ)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨Q, hQ, hQA⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B)
    (RingHom.ker (ψ : A →+* ℂ)) (by
      intro a ha
      have : a = 0 := Subtype.ext (by simpa using ha)
      simp [this])
  obtain ⟨η, hη⟩ := exists_algHom_ker_eq Q
  refine ⟨η, algHom_eq_of_ker_eq ?_⟩
  rw [← hQA, ← hη]
  ext a
  simp [Ideal.under]

/-- Points over a point of the base with prescribed value of an integral element `θ`: any root `r` of
`(minpoly P θ)` evaluated at `x` occurs. -/
theorem exists_point_over {P B : Type*} [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    [CommRing B] [IsDomain B]
    [Algebra ℂ P] [Algebra ℂ B] [Algebra P B] [IsScalarTower ℂ P B] [Algebra.FiniteType ℂ B]
    [Algebra.IsIntegral P B] [Module.IsTorsionFree P B]
    (θ : B) (x : P →ₐ[ℂ] ℂ) (r : ℂ)
    (hr : Polynomial.eval₂ (x : P →+* ℂ) r (minpoly P θ) = 0) :
    ∃ ζ : B →ₐ[ℂ] ℂ, ζ.comp (IsScalarTower.toAlgHom ℂ P B) = x ∧ ζ θ = r := by
  have hθ : IsIntegral P θ := Algebra.IsIntegral.isIntegral θ
  let e : P[X] →ₐ[ℂ] B := (Polynomial.aeval θ : P[X] →ₐ[P] B).restrictScalars ℂ
  let ψ0 : P[X] →ₐ[ℂ] ℂ := (Polynomial.aeval r).comp (Polynomial.mapAlgHom x)
  have hψ0 : ∀ p : P[X], ψ0 p = Polynomial.eval₂ (x : P →+* ℂ) r p := by
    intro p
    rw [Polynomial.eval₂_eq_eval_map]
    rfl
  have hker : RingHom.ker e.rangeRestrict.toRingHom ≤ RingHom.ker ψ0.toRingHom := by
    intro p hp
    have hp' : Polynomial.aeval θ p = 0 := by
      have := congrArg Subtype.val (show e.rangeRestrict p = 0 from hp)
      simpa [e] using this
    obtain ⟨q, rfl⟩ := minpoly.isIntegrallyClosed_dvd hθ hp'
    simp [hψ0, Polynomial.eval₂_mul, hr]
  let ψ : e.range →ₐ[ℂ] ℂ := AlgHom.liftOfSurjective e.rangeRestrict e.rangeRestrict_surjective ψ0 hker
  have hmem : ∀ q : P, algebraMap P B q ∈ e.range := fun q => ⟨Polynomial.C q, by simp [e]⟩
  have hint : Algebra.IsIntegral e.range B := by
    let j : P →+* e.range := (algebraMap P B).codRestrict e.range hmem
    letI : Algebra P e.range := j.toAlgebra
    haveI : IsScalarTower P e.range B := IsScalarTower.of_algebraMap_eq (fun q => rfl)
    exact ⟨fun b => (Algebra.IsIntegral.isIntegral (R := P) b).tower_top⟩
  obtain ⟨ζ, hζ⟩ := exists_algHom_extend e.range ψ
  have hψ : ∀ p : P[X], ζ (e p) = ψ0 p := by
    intro p
    have h1 : ζ (e p) = ψ ⟨e p, p, rfl⟩ := by
      have := congrArg (fun φ : e.range →ₐ[ℂ] ℂ => φ ⟨e p, p, rfl⟩) hζ
      simpa using this
    rw [h1]
    exact AlgHom.liftOfSurjective_apply e.rangeRestrict e.rangeRestrict_surjective ψ0 hker p
  refine ⟨ζ, ?_, ?_⟩
  · ext q
    have := hψ (Polynomial.C q)
    simpa [e, ψ0] using this
  · have := hψ Polynomial.X
    simpa [e, ψ0] using this

end FormalResearch.FrameFree.PolyImage
