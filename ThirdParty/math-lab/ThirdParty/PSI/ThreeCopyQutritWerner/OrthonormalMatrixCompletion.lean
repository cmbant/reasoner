module

public import Mathlib

@[expose] public section


/-! Complete an actual finite rectangular complex isometry to a square unitary,
retaining every original column through an explicit injective index map. -/
noncomputable section
open scoped BigOperators Matrix
namespace ThreeCopyQutritWerner

theorem orthonormal_matrix_completion {n k : Type*}
    [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (W : Matrix n k ℂ) (hW : Wᴴ * W = 1) :
    ∃ (U : Matrix n n ℂ) (e : k ↪ n), Uᴴ * U = 1 ∧
      ∀ i j, U i (e j) = W i j := by
  classical
  let v : k → EuclideanSpace ℂ n := fun j => WithLp.toLp 2 (fun i => W i j)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := congrArg (fun M : Matrix k k ℂ => M i j) hW
    simpa [v, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using h
  have hvr : Orthonormal ℂ (Subtype.val : Set.range v → EuclideanSpace ℂ n) :=
    (orthonormal_subtype_range hv.linearIndependent.injective).mpr hv
  obtain ⟨s, b, hs, hb⟩ := hvr.exists_orthonormalBasis_extension
  let f : k ↪ ↥s :=
    ⟨fun j => ⟨v j, hs (Set.mem_range_self j)⟩,
      fun i j hij => hv.linearIndependent.injective (congrArg Subtype.val hij)⟩
  have hcard : Fintype.card ↥s = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis b.toBasis]
    simp
  let e : ↥s ≃ n := Fintype.equivOfCardEq hcard
  let c := b.reindex e
  let U : Matrix n n ℂ := fun i j => c j i
  refine ⟨U, f.trans e.toEmbedding, ?_, ?_⟩
  · ext i j
    change (∑ x, star (c i x) * c j x) = if i = j then 1 else 0
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
      mul_comm] using c.inner_eq_ite i j
  · intro i j
    change (b.reindex e) (e (f j)) i = W i j
    rw [OrthonormalBasis.reindex_apply, e.symm_apply_apply]
    have hbj : b (f j) = v j := by
      rw [show b (f j) = ((↑) : ↥s → EuclideanSpace ℂ n) (f j) from congrFun hb (f j)]
      rfl
    rw [hbj]

end ThreeCopyQutritWerner
