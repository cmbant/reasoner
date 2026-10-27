import Mathlib
import FormalResearch.QIB.BlockStructure

/-!
# Real orthonormal bases of conjugation-closed subspaces

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis, no new axiom).

`exists_real_onb`: a subspace `U ⊆ ℂ^ι` closed under entrywise conjugation has an orthonormal basis of
*real* vectors (`star g = g`) for the standard Hermitian form.  Used by `RealCoordsStructure.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate

namespace FormalResearch.QIB

section Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A subspace closed under entrywise conjugation. -/
def ConjClosed (U : Submodule ℂ (ι → ℂ)) : Prop := ∀ v ∈ U, star v ∈ U

theorem star_mulVec_map (c : Matrix ι ι ℂ) (v : ι → ℂ) :
    star (c *ᵥ v) = c.map conj *ᵥ star v := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.star_apply, star_sum, star_mul']

theorem star_smul_vec (a : ℂ) (v : ι → ℂ) : star (a • v) = conj a • star v := by
  funext i
  simp [Pi.star_apply, mul_comm]

/-- The coercion `ℝ^ι → ℂ^ι`. -/
noncomputable def realToComplex : EuclideanSpace ℝ ι →ₗ[ℝ] (ι → ℂ) where
  toFun x := fun i => ((x i : ℝ) : ℂ)
  map_add' x y := by funext i; simp
  map_smul' c x := by funext i; simp

theorem star_realToComplex (x : EuclideanSpace ℝ ι) :
    star (realToComplex x) = realToComplex x := by
  funext i; simp [realToComplex, Pi.star_apply]

theorem star_realToComplex_dot (x y : EuclideanSpace ℝ ι) :
    star (realToComplex x) ⬝ᵥ realToComplex y = ((inner ℝ x y : ℝ) : ℂ) := by
  simp only [dotProduct, realToComplex, LinearMap.coe_mk, AddHom.coe_mk, Pi.star_apply,
    Complex.star_def, Complex.conj_ofReal]
  rw [PiLp.inner_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem exists_real_onb (U : Submodule ℂ (ι → ℂ)) (hU : ConjClosed U) :
    ∃ (m : ℕ) (g : Fin m → ι → ℂ), (∀ i, g i ∈ U) ∧ (∀ i, star (g i) = g i) ∧
      (∀ i j, star (g i) ⬝ᵥ g j = if i = j then 1 else 0) ∧
      ∀ v ∈ U, v = ∑ i, (star (g i) ⬝ᵥ v) • g i := by
  let Ur : Submodule ℝ (EuclideanSpace ℝ ι) := (U.restrictScalars ℝ).comap realToComplex
  let b := stdOrthonormalBasis ℝ Ur
  refine ⟨_, fun i => realToComplex ((b i : Ur) : EuclideanSpace ℝ ι), ?_, ?_, ?_, ?_⟩
  · intro i
    exact (b i).2
  · intro i
    exact star_realToComplex _
  · intro i j
    rw [star_realToComplex_dot]
    have h := (orthonormal_iff_ite.1 b.orthonormal) i j
    rw [Submodule.coe_inner] at h
    rw [h]
    split_ifs <;> simp
  · intro v hv
    -- real and imaginary parts
    let vr : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => (v i).re)
    let vi : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => (v i).im)
    have hvr : realToComplex vr = (1 / 2 : ℂ) • (v + star v) := by
      funext i
      simp [realToComplex, vr, Pi.star_apply, Complex.star_def]
      rw [Complex.add_conj]; push_cast; ring
    have hvi : realToComplex vi = (1 / (2 * Complex.I)) • (v - star v) := by
      funext i
      simp [realToComplex, vi, Pi.star_apply, Complex.star_def]
      rw [Complex.sub_conj]; push_cast
      field_simp
      rw [Complex.I_sq]; ring
    have hvr_mem : vr ∈ Ur := by
      show realToComplex vr ∈ U
      rw [hvr]
      exact U.smul_mem _ (U.add_mem hv (hU v hv))
    have hvi_mem : vi ∈ Ur := by
      show realToComplex vi ∈ U
      rw [hvi]
      exact U.smul_mem _ (U.sub_mem hv (hU v hv))
    have hv_eq : v = realToComplex vr + Complex.I • realToComplex vi := by
      funext i
      simp [realToComplex, vr, vi, Complex.re_add_im]
      rw [mul_comm]; exact (Complex.re_add_im _).symm.trans (by ring)
    have h1 := b.sum_repr' (⟨vr, hvr_mem⟩ : Ur)
    have h2 := b.sum_repr' (⟨vi, hvi_mem⟩ : Ur)
    have h1' := congrArg (fun z : Ur => realToComplex (z : EuclideanSpace ℝ ι)) h1
    have h2' := congrArg (fun z : Ur => realToComplex (z : EuclideanSpace ℝ ι)) h2
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at h1' h2'
    have hdot : ∀ i, star (realToComplex ((b i : Ur) : EuclideanSpace ℝ ι)) ⬝ᵥ v =
        ((inner ℝ ((b i : Ur) : EuclideanSpace ℝ ι) vr : ℝ) : ℂ) +
          Complex.I * ((inner ℝ ((b i : Ur) : EuclideanSpace ℝ ι) vi : ℝ) : ℂ) := by
      intro i
      conv_lhs => rw [hv_eq]
      rw [dotProduct_add, dotProduct_smul, star_realToComplex_dot, star_realToComplex_dot]
      rfl
    conv_lhs => rw [hv_eq]
    rw [← h1', ← h2']
    simp only [Submodule.coe_inner, hdot, add_smul, Finset.sum_add_distrib, Finset.smul_sum,
      mul_smul, Complex.coe_smul]
end Real

end FormalResearch.QIB
