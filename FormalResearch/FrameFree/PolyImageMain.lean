import Mathlib
import FormalResearch.FrameFree.PolyImageOpen
import FormalResearch.FrameFree.PolyImageChevalley

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Euclidean density of polynomial images (finite case)

Namespace `FormalResearch.FrameFree.PolyImage`.

* `exists_point_near`: for a finitely generated `ℂ`-domain `B` with generators `y` and `v ≠ 0`, every `ℂ`-point of
  `B` is a limit of `ℂ`-points not killing `v` (Noether normalization, the norm trick giving `c ≠ 0` with
  `c ∈ vB ∩ ℂ[x₁..x_d]`, and `exists_point_near_of_normalization`).
* `polyImageClosure_fin`: if every polynomial vanishing on the image of a polynomial map `Φ : ℂ^κ → ℂ^ι`
  (`ι`, `κ` finite) vanishes at `z`, then `z` lies in the Euclidean closure of the image.
-/

namespace FormalResearch.FrameFree.PolyImage

open Polynomial Filter Topology

section

variable {B : Type*} [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
  {ι : Type*} [Fintype ι]

theorem exists_point_near (y : ι → B)
    (hy : Function.Surjective (MvPolynomial.aeval y : MvPolynomial ι ℂ →ₐ[ℂ] B))
    {v : B} (hv : v ≠ 0) (ζ : B →ₐ[ℂ] ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ζ' : B →ₐ[ℂ] ℂ, ζ' v ≠ 0 ∧ ∀ i, ‖ζ' (y i) - ζ (y i)‖ < ε := by
  obtain ⟨d, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg ℂ B
  letI : Algebra (MvPolynomial (Fin d) ℂ) B := g.toRingHom.toAlgebra
  have hsc : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) B :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have hint : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) B := ⟨fun x => hgint x⟩
  have hfaith : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) B) := hginj
  have htf : Module.IsTorsionFree (MvPolynomial (Fin d) ℂ) B :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hfaith
  -- the norm trick
  have hvint : IsIntegral (MvPolynomial (Fin d) ℂ) v := hint.isIntegral v
  have hne := Ideal.under_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ) (I := Ideal.span {v}) hv
    (Ideal.subset_span rfl) hvint
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hc)
  obtain ⟨ζ', hζ'c, hζ'⟩ := exists_point_near_of_normalization y hy hc0 ζ hε
  refine ⟨ζ', ?_, hζ'⟩
  intro h0
  apply hζ'c
  rw [← ha, map_mul, h0, mul_zero]

end

section

variable {ι κ : Type*} [Finite ι] [Finite κ]

theorem polyImageClosure_fin (Φ : ι → MvPolynomial κ ℂ) (z : ι → ℂ)
    (h : ∀ p : MvPolynomial ι ℂ, (∀ t : κ → ℂ, MvPolynomial.eval (fun i => MvPolynomial.eval t (Φ i)) p = 0) →
      MvPolynomial.eval z p = 0) :
    z ∈ closure (Set.range fun (t : κ → ℂ) (i : ι) => MvPolynomial.eval t (Φ i)) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  let C := MvPolynomial κ ℂ
  let e : MvPolynomial ι ℂ →ₐ[ℂ] C := MvPolynomial.aeval Φ
  let B : Subalgebra ℂ C := e.range
  have hsurj : Function.Surjective e.rangeRestrict := e.rangeRestrict_surjective
  have : Algebra.FiniteType ℂ ↥B := Algebra.FiniteType.of_surjective e.rangeRestrict hsurj
  let y : ι → ↥B := fun i => e.rangeRestrict (MvPolynomial.X i)
  have hay : (MvPolynomial.aeval y : MvPolynomial ι ℂ →ₐ[ℂ] ↥B) = e.rangeRestrict := by
    apply MvPolynomial.algHom_ext; intro i; simp [y]
  have hy : Function.Surjective (MvPolynomial.aeval y : MvPolynomial ι ℂ →ₐ[ℂ] ↥B) := by
    rw [hay]; exact hsurj
  have hyC : ∀ i, (y i : C) = Φ i := fun i => by simp [y, e]
  -- `z` is a point of `B`
  have hz : z ∈ pointSet y := by
    rw [mem_pointSet_iff y hy]
    intro p hp
    apply h p
    intro t
    have h1 : e p = 0 := by
      have := congrArg Subtype.val hp
      rwa [hay] at this
    have h3 : (MvPolynomial.aeval t : C →ₐ[ℂ] ℂ) (e p) =
        MvPolynomial.aeval (fun i => MvPolynomial.aeval t (Φ i)) p := by
      rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    rw [h1, map_zero] at h3
    exact h3.symm
  obtain ⟨ζ, hζ⟩ := hz
  -- generic fibre (Chevalley) of `B ⊆ C`
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_points_lift (B := ↥B) (C := C) (fun a b hab => Subtype.ext hab)
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨ζ', hζ'v, hζ'⟩ := exists_point_near y hy hv0 ζ hε
  obtain ⟨η, hη⟩ := hv ζ' hζ'v
  refine ⟨fun i => MvPolynomial.eval (fun k => η (MvPolynomial.X k)) (Φ i), ⟨_, rfl⟩, ?_⟩
  rw [dist_pi_lt_iff hε]
  intro i
  have h1 : MvPolynomial.eval (fun k => η (MvPolynomial.X k)) (Φ i) = ζ' (y i) := by
    have : η (Φ i) = ζ' (y i) := by
      rw [← hη (y i)]
      exact congrArg η (hyC i).symm
    rw [← this]
    conv_rhs => rw [MvPolynomial.aeval_unique η]
    rfl
  rw [h1, Complex.dist_eq, ← hζ i, norm_sub_rev]
  exact hζ' i

end

end FormalResearch.FrameFree.PolyImage
