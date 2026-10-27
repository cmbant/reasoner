import Mathlib
import FormalResearch.FrameFree.PolyImageBasic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Polynomial images: the generic fibre (Chevalley)

Namespace `FormalResearch.FrameFree.PolyImage`.

`exists_open_in_range_comap`: for an injective finitely presented homomorphism `f : R → S` of domains, the image of
`Spec S → Spec R` (constructible by Chevalley, `PrimeSpectrum.isConstructible_range_comap`) contains the generic
point, hence a basic open `D(v)`, `v ≠ 0`.

`exists_ne_zero_points_lift`: for a finitely generated `ℂ`-algebra `B ⊆ C` of domains, there is `v ≠ 0` in `B` such
that every `ℂ`-point `ζ` of `B` with `ζ v ≠ 0` is the restriction of a `ℂ`-point of `C`.
-/

namespace FormalResearch.FrameFree.PolyImage

open PrimeSpectrum

theorem exists_open_in_range_comap {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (f : R →+* S) (hf : f.FinitePresentation) (hinj : Function.Injective f) :
    ∃ v : R, v ≠ 0 ∧ ∀ p : PrimeSpectrum R, v ∉ p.asIdeal → p ∈ Set.range (comap f) := by
  obtain ⟨T, hT⟩ := exists_constructibleSetData_iff.2 (isConstructible_range_comap hf)
  have hbot : (⟨⊥, inferInstance⟩ : PrimeSpectrum R) ∈ Set.range (comap f) := by
    refine ⟨⟨⊥, inferInstance⟩, ?_⟩
    apply PrimeSpectrum.ext
    exact Ideal.comap_bot_of_injective f hinj
  rw [← hT] at hbot
  simp only [ConstructibleSetData.toSet, Set.mem_iUnion] at hbot
  obtain ⟨C, hCT, hC⟩ := hbot
  refine ⟨C.f, ?_, fun p hp => ?_⟩
  · intro h0
    apply hC.2
    simp [h0]
  · rw [← hT]
    simp only [ConstructibleSetData.toSet, Set.mem_iUnion]
    refine ⟨C, hCT, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := hg
      have : C.g i = 0 := by
        have := hC.1 ⟨i, rfl⟩
        simpa using this
      simp [this]
    · simpa [mem_zeroLocus] using hp

section

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra ℂ B] [Algebra ℂ C] [Algebra B C]
  [IsScalarTower ℂ B C] [Algebra.FiniteType ℂ B] [Algebra.FiniteType ℂ C] [IsDomain B] [IsDomain C]

theorem exists_ne_zero_points_lift (hinj : Function.Injective (algebraMap B C)) :
    ∃ v : B, v ≠ 0 ∧ ∀ ζ : B →ₐ[ℂ] ℂ, ζ v ≠ 0 →
      ∃ η : C →ₐ[ℂ] ℂ, ∀ b, η (algebraMap B C b) = ζ b := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℂ B
  have : Algebra.FiniteType B C := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B C
  have hfp : (algebraMap B C).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finiteType.1 inferInstance)
  obtain ⟨v, hv0, hv⟩ := exists_open_in_range_comap (algebraMap B C) hfp hinj
  refine ⟨v, hv0, fun ζ hζ => ?_⟩
  have hsurj : Function.Surjective (ζ : B →+* ℂ) := fun c => ⟨algebraMap ℂ B c, by simp⟩
  have hmax : (RingHom.ker (ζ : B →+* ℂ)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨⟨q, hq⟩, hqm⟩ := hv ⟨RingHom.ker (ζ : B →+* ℂ), hmax.isPrime⟩ (by simpa using hζ)
  have hq' : q.comap (algebraMap B C) = RingHom.ker (ζ : B →+* ℂ) := congrArg PrimeSpectrum.asIdeal hqm
  obtain ⟨q', hq'max, hqq'⟩ := Ideal.exists_le_maximal q hq.ne_top
  obtain ⟨η, hη⟩ := exists_algHom_ker_eq q'
  refine ⟨η, fun b => ?_⟩
  have hcomap : q'.comap (algebraMap B C) = RingHom.ker (ζ : B →+* ℂ) := by
    refine (hmax.eq_of_le (Ideal.comap_ne_top _ hq'max.ne_top) ?_).symm
    rw [← hq']; exact Ideal.comap_mono hqq'
  have hker : RingHom.ker ((η.restrictScalars ℂ).comp (IsScalarTower.toAlgHom ℂ B C) : B →+* ℂ) =
      RingHom.ker (ζ : B →+* ℂ) := by
    rw [← hcomap, ← hη]; rfl
  have := algHom_eq_of_ker_eq (ζ := (η.comp (IsScalarTower.toAlgHom ℂ B C))) (η := ζ) hker
  exact congrArg (fun φ : B →ₐ[ℂ] ℂ => φ b) this

end

end FormalResearch.FrameFree.PolyImage
