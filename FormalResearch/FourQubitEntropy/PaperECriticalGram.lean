import Mathlib

/-!
# Simultaneous diagonalisation of commuting real symmetric matrices

Linear-algebra input for `lem:fqe-real-gram` of Paper E: a finite commuting family of real symmetric
matrices over a finite index type is diagonalised by one real orthogonal matrix. Proved from the joint
eigenspace decomposition `LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`.
-/

open Module
open scoped Matrix

namespace FormalResearch.FourQubitEntropy.PaperECritical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix whose columns are an orthonormal basis of `ℝ^ι` is orthogonal. -/
theorem basisMatrix_orth (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    (Matrix.of fun i k => b k i)ᵀ * (Matrix.of fun i k => b k i) = 1 := by
  ext k l
  have := b.inner_eq_ite k l
  simp only [EuclideanSpace.inner_eq_star_dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [← this]
  simp only [dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A finite commuting family of real symmetric matrices is simultaneously diagonalised by a real
orthogonal matrix `O` (`Oᵀ O = 1`): `M i * O = O * diagonal d` for some `d`. -/
theorem exists_orthogonal_simul_diag {m : ℕ} (M : Fin m → Matrix ι ι ℝ)
    (hs : ∀ i, (M i)ᵀ = M i) (hc : ∀ i j, M i * M j = M j * M i) :
    ∃ O : Matrix ι ι ℝ, Oᵀ * O = 1 ∧ ∀ i, ∃ d : ι → ℝ, M i * O = O * Matrix.diagonal d := by
  classical
  let T : Fin m → Module.End ℝ (EuclideanSpace ℝ ι) := fun i => Matrix.toEuclideanLin (M i)
  have hT : ∀ i, (T i).IsSymmetric := fun i => by
    rw [show T i = Matrix.toEuclideanLin (M i) from rfl, Matrix.isSymmetric_toEuclideanLin_iff]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hs i
  have hC : Pairwise (Function.onFun Commute T) := fun i j _ => by
    have := (Matrix.toLpLinAlgEquiv (R := ℝ) (n := ι) 2).map_mul (M i) (M j)
    have h2 := (Matrix.toLpLinAlgEquiv (R := ℝ) (n := ι) 2).map_mul (M j) (M i)
    show T i * T j = T j * T i
    have e1 : T i * T j = (Matrix.toLpLinAlgEquiv (R := ℝ) (n := ι) 2) (M i * M j) := this.symm
    have e2 : T j * T i = (Matrix.toLpLinAlgEquiv (R := ℝ) (n := ι) 2) (M j * M i) := h2.symm
    rw [e1, e2, hc]
  set V : (Fin m → ℝ) → Submodule ℝ (EuclideanSpace ℝ ι) :=
    fun α => ⨅ j, Module.End.eigenspace (T j) (α j) with hVdef
  have hV' := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  have hfin : {α | V α ≠ ⊥}.Finite := Submodule.finite_ne_bot_of_iSupIndep hV'.independent
  have : Fintype {α // V α ≠ ⊥} := (Set.Finite.fintype hfin)
  let W : {α // V α ≠ ⊥} → Submodule ℝ (EuclideanSpace ℝ ι) := fun α => V α.1
  have hW' : OrthogonalFamily ℝ (fun i => W i) fun i => (W i).subtypeₗᵢ := by
    intro f g hfg
    exact hV' (fun h => hfg (Subtype.ext h))
  have htop : ⨆ α, W α = ⊤ := by
    have := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
    rw [eq_top_iff, ← this]
    refine iSup_le fun α => ?_
    by_cases h : V α = ⊥
    · rw [show (⨅ i, Module.End.eigenspace (T i) (α i)) = V α from rfl, h]; exact bot_le
    · exact le_iSup W ⟨α, h⟩
  have hI : DirectSum.IsInternal W := by
    rw [hW'.isInternal_iff, htop]; exact Submodule.top_orthogonal_eq_bot
  have hn : finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := finrank_euclideanSpace
  let b0 := hI.subordinateOrthonormalBasis hn hW'
  let b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) := b0.reindex (Fintype.equivFin ι).symm
  have hmem : ∀ k : ι, ∃ α : Fin m → ℝ, ∀ j, T j (b k) = α j • b k := by
    intro k
    have h := hI.subordinateOrthonormalBasis_subordinate hn ((Fintype.equivFin ι) k) hW'
    refine ⟨(hI.subordinateOrthonormalBasisIndex hn ((Fintype.equivFin ι) k) hW').1, fun j => ?_⟩
    have h2 := (Submodule.mem_iInf _).1 h j
    have := Module.End.mem_eigenspace_iff.1 h2
    simpa [b, b0] using this
  choose α hα using hmem
  refine ⟨Matrix.of fun i k => b k i, ?_, fun j => ⟨fun k => α k j, ?_⟩⟩
  · exact basisMatrix_orth b
  · ext i k
    have h := congrArg (fun v => v i) (hα k j)
    simp only [T, Matrix.toEuclideanLin] at h
    simp [Matrix.mul_apply, Matrix.diagonal, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct] at h ⊢
    rw [h, mul_comm]

end FormalResearch.FourQubitEntropy.PaperECritical
