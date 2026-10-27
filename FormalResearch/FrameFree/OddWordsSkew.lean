import Mathlib

/-!
# Dimension of the skew-adjoint endomorphisms of a real inner product space

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved** (no hypothesis).

`finrank_skewAdjoint_end`: for a finite-dimensional real inner product space `E` of dimension `g`,
the real space of skew-adjoint endomorphisms has dimension `C(g, 2)`.  Route: an orthonormal basis
identifies `End E` with `Matrix (Fin g) (Fin g) ℝ` as a `*`-algebra (`LinearMap.toMatrixOrthonormal`),
skew matrices are determined by their strictly upper entries (`skewMatrix_equiv`), and the number of
pairs `i < j` is `C(g, 2)` (`card_lt_pairs`).  This is the `Σ C(g_j, 2)` counting step of Paper P,
`prop:oddwords` (iii): odd invariants are `i ·` (real antisymmetric matrices on each real-type
multiplicity space).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FormalResearch.FrameFree.OddWords

/-- The pairs `i < j` in `Fin g`. -/
abbrev LtPairs (g : ℕ) := {p : Fin g × Fin g // p.1 < p.2}

theorem card_lt_pairs (g : ℕ) : Fintype.card (LtPairs g) = g.choose 2 := by
  classical
  have h1 : Fintype.card (LtPairs g) = (Finset.univ.filter fun p : Fin g × Fin g => p.1 < p.2).card := by
    rw [Fintype.card_subtype]
  have h2 : (Finset.univ.filter fun p : Fin g × Fin g => p.2 < p.1).card
      = (Finset.univ.filter fun p : Fin g × Fin g => p.1 < p.2).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simpa using hp
    · intro p _ q _ h; simpa [Prod.ext_iff, and_comm] using h
    · intro q hq; exact ⟨(q.2, q.1), by simpa using hq, rfl⟩
  have h4 : (Finset.univ : Finset (Fin g × Fin g)).filter (fun p => p.1 ≠ p.2)
      = (Finset.univ.filter fun p : Fin g × Fin g => p.1 < p.2)
        ∪ (Finset.univ.filter fun p : Fin g × Fin g => p.2 < p.1) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h; rcases lt_or_gt_of_ne h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact ne_of_lt h
      · exact ne_of_gt h
  have h5 : Finset.card ((Finset.univ : Finset (Fin g)).offDiag) = g * g - g := by
    rw [Finset.offDiag_card]; simp
  have h6 : ((Finset.univ : Finset (Fin g)).offDiag)
      = (Finset.univ : Finset (Fin g × Fin g)).filter (fun p => p.1 ≠ p.2) := by
    ext p; simp [Finset.mem_offDiag]
  have hd : Disjoint (Finset.univ.filter fun p : Fin g × Fin g => p.1 < p.2)
      (Finset.univ.filter fun p : Fin g × Fin g => p.2 < p.1) := by
    rw [Finset.disjoint_left]; intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact lt_asymm hp hq
  rw [h6, h4, Finset.card_union_of_disjoint hd, h2] at h5
  rw [h1, Nat.choose_two_right]
  have : 2 * (Finset.univ.filter fun p : Fin g × Fin g => p.1 < p.2).card = g * (g - 1) := by
    rw [Nat.mul_sub_one]; omega
  omega

/-- Skew-adjoint real matrices are determined by their strictly upper entries. -/
noncomputable def skewMatrixEquiv (g : ℕ) :
    skewAdjoint (Matrix (Fin g) (Fin g) ℝ) ≃ₗ[ℝ] (LtPairs g → ℝ) where
  toFun A p := (A : Matrix (Fin g) (Fin g) ℝ) p.1.1 p.1.2
  map_add' A B := by ext p; simp
  map_smul' c A := by ext p; simp
  invFun c :=
    ⟨Matrix.of fun i j => if h : i < j then c ⟨(i, j), h⟩ else if h' : j < i then - c ⟨(j, i), h'⟩ else 0,
      by
        rw [skewAdjoint.mem_iff]
        ext i j
        simp only [Matrix.star_apply, Matrix.of_apply, Matrix.neg_apply, star_trivial]
        by_cases h : i < j
        · simp [h, not_lt.2 h.le]
        · by_cases h' : j < i
          · simp [h, h']
          · simp [h, h']⟩
  left_inv A := by
    apply Subtype.ext
    have hA := A.2
    rw [skewAdjoint.mem_iff] at hA
    ext i j
    simp only [Matrix.of_apply]
    have hs : ∀ a b, (A : Matrix (Fin g) (Fin g) ℝ) b a = - (A : Matrix (Fin g) (Fin g) ℝ) a b := by
      intro a b
      have := congrFun (congrFun hA a) b
      simpa [Matrix.star_apply] using this
    by_cases h : i < j
    · simp [h]
    · by_cases h' : j < i
      · simp [h, h', hs j i]
      · have : i = j := le_antisymm (not_lt.1 h') (not_lt.1 h)
        subst this
        have := hs i i
        simp [h, h']; linarith
  right_inv c := by
    ext p
    simp [p.2]

theorem finrank_skewAdjoint_matrix (g : ℕ) :
    Module.finrank ℝ (skewAdjoint (Matrix (Fin g) (Fin g) ℝ)) = g.choose 2 := by
  rw [(skewMatrixEquiv g).finrank_eq, Module.finrank_fintype_fun_eq_card, card_lt_pairs]

/-- The inclusion of the skew-adjoint endomorphisms as a real linear map. -/
def skewAdjointSubtype (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : skewAdjoint (E →ₗ[ℝ] E) →ₗ[ℝ] (E →ₗ[ℝ] E) where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance finite_skewAdjoint_end (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Module.Finite ℝ (skewAdjoint (E →ₗ[ℝ] E)) :=
  Module.Finite.of_injective (skewAdjointSubtype E) Subtype.val_injective

instance free_skewAdjoint_end (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Module.Free ℝ (skewAdjoint (E →ₗ[ℝ] E)) :=
  Module.Free.of_divisionRing ℝ _

/-- **Counting step.**  For a finite-dimensional real inner product space `E`, the skew-adjoint
endomorphisms form a real space of dimension `C(dim E, 2)`. -/
theorem finrank_skewAdjoint_end (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Module.finrank ℝ (skewAdjoint (E →ₗ[ℝ] E)) = (Module.finrank ℝ E).choose 2 := by
  let b := stdOrthonormalBasis ℝ E
  let e := LinearMap.toMatrixOrthonormal b
  let φ : skewAdjoint (E →ₗ[ℝ] E) ≃ₗ[ℝ] skewAdjoint (Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) :=
    { toFun := fun x => ⟨e x.1, by
        rw [skewAdjoint.mem_iff, ← map_star, skewAdjoint.star_val_eq, map_neg]⟩
      invFun := fun y => ⟨e.symm y.1, by
        rw [skewAdjoint.mem_iff, ← map_star, skewAdjoint.star_val_eq, map_neg]⟩
      map_add' := fun x y => by ext1; simp
      map_smul' := fun c x => by ext1; simp
      left_inv := fun x => by ext1; simp
      right_inv := fun y => by ext1; simp }
  rw [φ.finrank_eq, finrank_skewAdjoint_matrix]

end FormalResearch.FrameFree.OddWords
