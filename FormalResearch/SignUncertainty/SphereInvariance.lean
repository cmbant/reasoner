module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import FormalResearch.SignUncertainty.EuclidSplit

/-!
# The sphere measure of `ℝ^d` is invariant under linear isometries

`USph d` is the unit sphere of `ℝ^d` and `sphMeas d = volume.toSphere` its surface measure. A linear
isometry `A` acts on it (`sphereMap A`) preserving `sphMeas` (`sphereMap_measurePreserving`), so
`∫_ω k(⟪v, ω⟫) dω` depends only on `‖v‖` (`sphere_integral_inner_eq`).
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace Pointwise

namespace FormalResearch.SignUncertainty

/-- The unit sphere of `ℝ^d`. -/
abbrev USph (d : ℕ) := Metric.sphere (0 : EuclSp d) 1

/-- The surface measure on the unit sphere. -/
noncomputable def sphMeas (d : ℕ) : Measure (USph d) := (volume : Measure (EuclSp d)).toSphere

instance (d : ℕ) : IsFiniteMeasure (sphMeas d) := by unfold sphMeas; infer_instance

instance (d : ℕ) : (sphMeas d).IsOpenPosMeasure := by unfold sphMeas; infer_instance

/-- A linear isometry acting on the unit sphere. -/
noncomputable def sphereMap {d : ℕ} (A : EuclSp d ≃ₗᵢ[ℝ] EuclSp d) : USph d ≃ᵐ USph d where
  toFun ω := ⟨A ω.1, by simp [mem_sphere_zero_iff_norm.1 ω.2]⟩
  invFun ω := ⟨A.symm ω.1, by simp [mem_sphere_zero_iff_norm.1 ω.2]⟩
  left_inv ω := by simp
  right_inv ω := by simp
  measurable_toFun :=
    Measurable.subtype_mk (A.continuous.measurable.comp measurable_subtype_coe)
  measurable_invFun :=
    Measurable.subtype_mk (A.symm.continuous.measurable.comp measurable_subtype_coe)

@[simp] lemma coe_sphereMap {d : ℕ} (A : EuclSp d ≃ₗᵢ[ℝ] EuclSp d) (ω : USph d) :
    ((sphereMap A ω : USph d) : EuclSp d) = A ω := rfl

lemma sphereMap_measurePreserving {d : ℕ} [NeZero d] (A : EuclSp d ≃ₗᵢ[ℝ] EuclSp d) :
    MeasurePreserving (sphereMap A) (sphMeas d) (sphMeas d) := by
  refine ⟨(sphereMap A).measurable, ?_⟩
  refine Measure.ext fun s hs => ?_
  rw [MeasurableEquiv.map_apply, sphMeas, Measure.toSphere_apply' _ ((sphereMap A).measurable hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap A ⁻¹' s) : Set (EuclSp d)) =
      A ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set (EuclSp d))) := by
    ext x
    constructor
    · rintro ⟨t, ht, y, ⟨ω, hωs, rfl⟩, rfl⟩
      exact ⟨t, ht, ((sphereMap A ω : USph d) : EuclSp d), ⟨sphereMap A ω, hωs, rfl⟩, by simp⟩
    · rintro ⟨t, ht, y, ⟨η, hηs, rfl⟩, hx⟩
      refine ⟨t, ht, (((sphereMap A).symm η : USph d) : EuclSp d),
        ⟨(sphereMap A).symm η, by simpa using hηs, rfl⟩, ?_⟩
      have hAη : A (((sphereMap A).symm η : USph d) : EuclSp d) = (η : EuclSp d) := by
        show A (A.symm (η : EuclSp d)) = η
        simp
      apply A.injective
      rw [map_smul, hAη]
      exact hx
  rw [hset]
  exact MeasurePreserving.measure_preimage_equiv (f := A.toHomeomorph.toMeasurableEquiv)
    A.measurePreserving _

/-- `∫ g(Aω) dω = ∫ g(ω) dω` on the sphere. -/
lemma integral_sphereMap {d : ℕ} [NeZero d] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : EuclSp d ≃ₗᵢ[ℝ] EuclSp d) (g : USph d → F) :
    ∫ ω, g (sphereMap A ω) ∂sphMeas d = ∫ ω, g ω ∂sphMeas d :=
  (sphereMap_measurePreserving A).integral_comp' g

/-- Two vectors of equal norm are exchanged by a linear isometry equivalence (a reflection). -/
lemma exists_linearIsometryEquiv_map' {d : ℕ} {u v : EuclSp d} (h : ‖u‖ = ‖v‖) :
    ∃ A : EuclSp d ≃ₗᵢ[ℝ] EuclSp d, A u = v :=
  ⟨Submodule.reflection (ℝ ∙ (u - v))ᗮ, Submodule.reflection_sub h⟩

/-- **`∫_ω k(⟪v, ω⟫) dω` depends only on `‖v‖`.** -/
lemma sphere_integral_inner_eq {d : ℕ} [NeZero d] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℝ → F) {v w : EuclSp d} (h : ‖v‖ = ‖w‖) :
    ∫ ω : USph d, k (⟪v, (ω : EuclSp d)⟫) ∂sphMeas d = ∫ ω : USph d, k (⟪w, (ω : EuclSp d)⟫) ∂sphMeas d := by
  obtain ⟨A, hA⟩ := exists_linearIsometryEquiv_map' h
  rw [← integral_sphereMap A (fun ω : USph d => k (⟪w, (ω : EuclSp d)⟫))]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [coe_sphereMap]
  rw [← hA, A.inner_map_map]

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.sphere_integral_inner_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphere_integral_inner_eq

end FormalResearch.SignUncertainty
