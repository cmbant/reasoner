import Mathlib
import FormalResearch.QIB1.ApolarCoherentKernel

namespace FormalResearch.QIB1

/-- Real scalar extension of the certified square pivot block. -/
def apolarSquareR (d : Nat) : Matrix (Fin (d - 2)) (Fin (d - 2)) ℝ :=
  fun r c => (apolarSquare d r c : ℝ)

/-- The real full matrix contains the same canonical square block. -/
theorem apolarFullR_selected (d : Nat) :
    (apolarFullR d).submatrix id (@apolarSelectedCol d) = apolarSquareR d := by
  ext r c
  change (apolarFull d r (apolarSelectedCol c) : ℝ) = (apolarSquare d r c : ℝ)
  exact_mod_cast congrFun (congrFun (apolarFull_selected d) r) c

/-- The real pivot block remains upper triangular. -/
theorem apolarSquareR_upper (d : Nat) : (apolarSquareR d).IsUpperTriangular := by
  intro i j hij
  change (apolarSquare d i j : ℝ) = 0
  exact_mod_cast apolarSquare_upper d hij

/-- Its diagonal entries are the same positive pivots. -/
theorem apolarSquareR_diag (d : Nat) (i : Fin (d - 2)) :
    apolarSquareR d i i = (apolarPivot d i.val : ℝ) := by
  exact_mod_cast apolarSquare_diag d i

/-- Hence the real pivot determinant is strictly positive. -/
theorem apolarSquareR_det_pos {d : Nat} (hd : 3 ≤ d) :
    0 < (apolarSquareR d).det := by
  rw [Matrix.det_of_isUpperTriangular (apolarSquareR d) (apolarSquareR_upper d)]
  apply Finset.prod_pos
  intro i hi
  rw [apolarSquareR_diag]
  exact_mod_cast apolarPivot_pos (by omega : i.val + 3 ≤ d)

/-- The real apolar differential has maximal row rank. -/
theorem apolarFullR_rank {d : Nat} (hd : 3 ≤ d) :
    (apolarFullR d).rank = d - 2 := by
  apply Nat.le_antisymm
  · simpa using Matrix.rank_le_card_height (apolarFullR d)
  · have hsq : (apolarSquareR d).rank = d - 2 := by
      rw [Matrix.rank_of_det_ne_zero (ne_of_gt (apolarSquareR_det_pos hd)), Fintype.card_fin]
    calc
      d - 2 = (apolarSquareR d).rank := hsq.symm
      _ = ((apolarFullR d).submatrix id (@apolarSelectedCol d)).rank := by
        rw [apolarFullR_selected]
      _ ≤ (apolarFullR d).rank :=
        Matrix.rank_submatrix_le (apolarFullR d) id (@apolarSelectedCol d)

/-- Rank-nullity gives a three-dimensional real kernel as well. -/
theorem apolarFullR_kernel_finrank {d : Nat} (hd : 3 ≤ d) :
    Module.finrank ℝ (LinearMap.ker (apolarFullR d).mulVecLin) = 3 := by
  have hnull := (apolarFullR d).mulVecLin.finrank_range_add_finrank_ker
  have hrange :
      Module.finrank ℝ (LinearMap.range (apolarFullR d).mulVecLin) = d - 2 := by
    change (apolarFullR d).rank = d - 2
    exact apolarFullR_rank hd
  rw [hrange, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hnull
  omega

/-- The three real valence coherent vectors: `b=0,+√3,-√3`. -/
def apolarValenceFamily (d : Nat) : Fin 3 → (Fin (d + 1) → ℝ) :=
  ![apolarCoherent d 0,
    apolarCoherent d (Real.sqrt 3),
    apolarCoherent d (-Real.sqrt 3)]

/-- Each of the three valence vectors lies in the real apolar kernel. -/
theorem apolarValenceFamily_mem_kernel {d : Nat} (hd : 3 ≤ d) (i : Fin 3) :
    apolarValenceFamily d i ∈ LinearMap.ker (apolarFullR d).mulVecLin := by
  have hs := apolarCoherent_sqrt_three_mem_kernel hd
  fin_cases i
  · simpa [apolarValenceFamily] using
      apolarCoherent_mem_kernel hd 0 (Or.inl rfl)
  · simpa [apolarValenceFamily] using hs.1
  · simpa [apolarValenceFamily] using hs.2

/-- The three valence coherent vectors are linearly independent.  Only the
first three monomial coefficients are needed: the resulting 3×3 Vandermonde
minor has nonzero factors `d`, `choose d 2`, and `√3`. -/
theorem apolarValenceFamily_linearIndependent {d : Nat} (hd : 3 ≤ d) :
    LinearIndependent ℝ (apolarValenceFamily d) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrFun hg (⟨0, by omega⟩ : Fin (d + 1))
  have h1 := congrFun hg (⟨1, by omega⟩ : Fin (d + 1))
  have h2 := congrFun hg (⟨2, by omega⟩ : Fin (d + 1))
  simp [Fin.sum_univ_succ, apolarValenceFamily, apolarCoherent] at h0 h1 h2
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hcN : 0 < d.choose 2 := Nat.choose_pos (by omega)
  have hc : (0 : ℝ) < d.choose 2 := by exact_mod_cast hcN
  have hg0 : g 0 = 0 := by nlinarith
  have hg1 : g 1 = 0 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hg2 : g 2 = 0 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

/-- The valence family, viewed intrinsically as vectors in the kernel. -/
def apolarValenceKernelFamily {d : Nat} (hd : 3 ≤ d) :
    Fin 3 → LinearMap.ker (apolarFullR d).mulVecLin :=
  Set.codRestrict (apolarValenceFamily d)
    (LinearMap.ker (apolarFullR d).mulVecLin)
    (apolarValenceFamily_mem_kernel hd)

/-- The intrinsic kernel family is linearly independent. -/
theorem apolarValenceKernelFamily_linearIndependent {d : Nat} (hd : 3 ≤ d) :
    LinearIndependent ℝ (apolarValenceKernelFamily hd) := by
  exact (apolarValenceFamily_linearIndependent hd).codRestrict
    (LinearMap.ker (apolarFullR d).mulVecLin) (apolarValenceFamily_mem_kernel hd)

/-- Full valence-span theorem over the natural real scalar extension: the
kernel of `D_F` is exactly spanned by the three coherent powers associated to
the roots `b=0,±√3` of `b(3-b²)`. -/
theorem apolar_valence_span_eq_kernel {d : Nat} (hd : 3 ≤ d) :
    Submodule.span ℝ (Set.range (apolarValenceKernelFamily hd)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [← (apolarValenceKernelFamily_linearIndependent hd).finrank_span_eq_card]
  rw [Fintype.card_fin, apolarFullR_kernel_finrank hd]

end FormalResearch.QIB1
