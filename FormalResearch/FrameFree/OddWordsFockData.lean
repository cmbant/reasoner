import Mathlib
import FormalResearch.FrameFree.OddWordsSl2
import FormalResearch.FrameFree.OddWordsFock

/-!
# The Fock space as an `Sl2Data` (Paper P, `prop:oddwords` (iii))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

`fockData n : Sl2Data n (EuclideanSpace ℝ (Cube n))` is the total-spin structure of `n` qubits:
`L = Lm n`, `adjoint L = (Lm n)ᵀ`, `H = diag (n - 2 |x|)`, weight space `W_m` = functions supported
on the Hamming sphere `|x| = m` (dimension `C(n,m)`, `card_wt`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Module LinearMap Finset

namespace FormalResearch.FrameFree.OddWords

variable {n : ℕ}

/-- A real matrix as an endomorphism of the Euclidean space on `Cube n`. -/
noncomputable def ofMat (A : Matrix (Cube n) (Cube n) ℝ) :
    EuclideanSpace ℝ (Cube n) →ₗ[ℝ] EuclideanSpace ℝ (Cube n) :=
  Matrix.toEuclideanLin A

theorem ofMat_apply (A : Matrix (Cube n) (Cube n) ℝ) (v : EuclideanSpace ℝ (Cube n)) (x : Cube n) :
    ofMat A v x = ∑ y, A x y * v y := by
  simp [ofMat, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

theorem ofMat_mul (A B : Matrix (Cube n) (Cube n) ℝ) : ofMat (A * B) = ofMat A * ofMat B := by
  ext v x
  simp [ofMat, Matrix.toLpLin_mul_same]

theorem ofMat_sub (A B : Matrix (Cube n) (Cube n) ℝ) : ofMat (A - B) = ofMat A - ofMat B := by
  simp [ofMat]

theorem ofMat_smul (c : ℝ) (A : Matrix (Cube n) (Cube n) ℝ) : ofMat (c • A) = c • ofMat A := by
  simp [ofMat]

theorem ofMat_add (A B : Matrix (Cube n) (Cube n) ℝ) : ofMat (A + B) = ofMat A + ofMat B := by
  simp [ofMat]

theorem ofMat_neg (A : Matrix (Cube n) (Cube n) ℝ) : ofMat (-A) = -ofMat A := by
  simp [ofMat]

theorem ofMat_injective : Function.Injective (ofMat (n := n)) :=
  (Matrix.toEuclideanLin (n := Cube n) (m := Cube n) (𝕜 := ℝ)).injective

theorem ofMat_transpose (A : Matrix (Cube n) (Cube n) ℝ) : ofMat A.transpose = adjoint (ofMat A) := by
  have := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this

theorem wt_eq_card (x : Cube n) : wt x = (Finset.univ.filter fun i => x i = 1).card := by
  rw [wt, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (x i).2
  rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h | h <;> simp [h]

theorem card_wt (m : ℕ) : Fintype.card {x : Cube n // wt x = m} = n.choose m := by
  classical
  rw [Fintype.card_subtype]
  have h := Finset.card_powersetCard m (Finset.univ : Finset (Fin n))
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  refine Finset.card_bij (fun x _ => Finset.univ.filter fun i => x i = 1) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by rw [← wt_eq_card]; simpa using hx⟩
  · intro x _ y _ hxy
    funext i
    have := congrArg (fun s : Finset (Fin n) => i ∈ s) hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h1 | h1 <;> rcases Fin.exists_fin_two.1 ⟨y i, rfl⟩ with h2 | h2 <;>
      simp_all
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    refine ⟨fun i => if i ∈ s then 1 else 0, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [wt_eq_card]
      convert hs.2 using 2
      ext i; simp
    · ext i; simp


theorem ofMat_diagonal_apply (d : Cube n → ℝ) (v : EuclideanSpace ℝ (Cube n)) (x : Cube n) :
    ofMat (Matrix.diagonal d) v x = d x * v x := by
  rw [ofMat_apply, Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [Matrix.diagonal_apply_ne _ (Ne.symm hy)]
  · simp

theorem adjoint_ofMat_Lm : adjoint (ofMat (Lm n)) = ofMat (Lm n).transpose :=
  (ofMat_transpose _).symm

theorem adjoint_Lm_mul_sub :
    adjoint (ofMat (Lm n)) * ofMat (Lm n) - ofMat (Lm n) * adjoint (ofMat (Lm n)) = ofMat (Hm n) := by
  rw [adjoint_ofMat_Lm, ← ofMat_mul, ← ofMat_mul, ← ofMat_sub, Rm_mul_Lm_sub]

theorem mem_eigen_Hm {μ : ℝ} {v : EuclideanSpace ℝ (Cube n)} :
    ofMat (Hm n) v = μ • v ↔ ∀ x, ((n : ℝ) - 2 * wt x) * v x = μ * v x := by
  constructor
  · intro h x
    have := congrArg (fun w : EuclideanSpace ℝ (Cube n) => w x) h
    simpa [Hm_eq_diagonal, ofMat_diagonal_apply] using this
  · intro h
    ext x
    simpa [Hm_eq_diagonal, ofMat_diagonal_apply] using h x

theorem eigen_Hm_eq_span (m : ℕ) :
    End.eigenspace (adjoint (ofMat (Lm n)) * ofMat (Lm n) - ofMat (Lm n) * adjoint (ofMat (Lm n)))
      ((n : ℝ) - 2 * m) =
    Submodule.span ℝ (Set.range fun x : {x : Cube n // wt x = m} =>
      (EuclideanSpace.basisFun (Cube n) ℝ) x.1) := by
  classical
  have key : ∀ v : EuclideanSpace ℝ (Cube n),
      (∀ x, ((n : ℝ) - 2 * wt x) * v x = ((n : ℝ) - 2 * m) * v x) ↔ ∀ x, wt x ≠ m → v x = 0 := by
    intro v
    refine forall_congr' fun x => ?_
    by_cases h : wt x = m
    · simp [h]
    · have : ((n : ℝ) - 2 * wt x) - ((n : ℝ) - 2 * m) ≠ 0 := by
        intro h0
        apply h
        have : (wt x : ℝ) = m := by linarith
        exact_mod_cast this
      constructor
      · intro h1 _
        have : (((n : ℝ) - 2 * wt x) - ((n : ℝ) - 2 * m)) * v x = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left ‹_›
      · intro h1; rw [h1 h]; simp
  ext v
  rw [End.mem_eigenspace_iff, adjoint_Lm_mul_sub, mem_eigen_Hm, key]
  constructor
  · intro hv
    have : v = ∑ x : {x : Cube n // wt x = m}, v x.1 • (EuclideanSpace.basisFun (Cube n) ℝ) x.1 := by
      ext y
      simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply]
      by_cases hy : wt y = m
      · rw [Finset.sum_eq_single ⟨y, hy⟩]
        · simp
        · intro b _ hb
          have : b.1 ≠ y := fun h => hb (Subtype.ext h)
          simp [Ne.symm this]
        · simp
      · rw [hv y hy]
        refine (Finset.sum_eq_zero fun b _ => ?_).symm
        have : b.1 ≠ y := fun h => hy (h ▸ b.2)
        simp [Ne.symm this]
    rw [this]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  · intro hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨y, hy⟩, rfl⟩ := hw
      intro x hx
      have : x ≠ y := fun h => hx (h ▸ hy)
      simp [this]
    | zero => intro x _; rfl
    | add a b _ _ ha hb => intro x hx; simp [ha x hx, hb x hx]
    | smul c a _ ha => intro x hx; simp [ha x hx]

/-- The total-spin structure on `n` qubits. -/
noncomputable def fockData (n : ℕ) : Sl2Data n (EuclideanSpace ℝ (Cube n)) where
  L := ofMat (Lm n)
  hHL := by
    rw [adjoint_Lm_mul_sub, ← ofMat_mul, ← ofMat_mul, ← ofMat_sub, Hm_mul_Lm_sub, ofMat_smul]
  finrank_V := by simp [finrank_euclideanSpace, ]
  hspec := by
    intro μ hμ v hv
    rw [adjoint_Lm_mul_sub, mem_eigen_Hm] at hv
    ext x
    have h := hv x
    have hne : ((n : ℝ) - 2 * wt x) - μ ≠ 0 := fun h0 => hμ (wt x) (wt_le x) (by linarith)
    have : (((n : ℝ) - 2 * wt x) - μ) * v x = 0 := by linarith
    simpa [hne] using this
  decomp := by
    intro v
    refine ⟨fun m => WithLp.toLp 2 (fun x => if wt x = m then v x else 0), ?_, ?_⟩
    · intro m
      rw [adjoint_Lm_mul_sub, mem_eigen_Hm]
      intro x
      by_cases h : wt x = m
      · simp [h]
      · simp [h]
    · ext x
      simp only [WithLp.ofLp_sum, Finset.sum_apply]
      rw [Finset.sum_eq_single (wt x)]
      · simp
      · intro m _ hm; simp [Ne.symm hm]
      · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (wt_le x))) h
  finrank_W := by
    intro m
    rw [eigen_Hm_eq_span, finrank_span_eq_card, Fintype.card_subtype, ← card_wt m, Fintype.card_subtype]
    · exact (EuclideanSpace.basisFun (Cube n) ℝ).toBasis.linearIndependent.comp _ Subtype.val_injective

end FormalResearch.FrameFree.OddWords
