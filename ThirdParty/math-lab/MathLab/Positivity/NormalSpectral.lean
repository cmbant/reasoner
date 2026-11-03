module

/-
NormalSpectral.lean

The spectral theorem for normal complex matrices: if `Nᴴ N = N Nᴴ` then `N = U D Uᴴ` with `U`
unitary and `D` diagonal (`normal_spectral`).

Mathlib proves the Hermitian case and the joint eigenspace decomposition of two commuting symmetric
operators (`LinearMap.IsSymmetric.directSum_isInternal_of_commute`). A normal matrix is `H + iK` with
`H = (N + Nᴴ)/2` and `K = (N - Nᴴ)/(2i)` Hermitian and commuting, so an orthonormal basis subordinate
to the joint eigenspaces of `H` and `K` diagonalizes it.
-/
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.Hermitian

@[expose] public section

open Matrix

noncomputable section

namespace MathLab

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Spectral theorem for normal matrices**: a complex matrix commuting with its adjoint is
`U * diagonal d * Uᴴ` for a unitary `U`. -/
theorem normal_spectral (N : Matrix ι ι ℂ) (hN : Nᴴ * N = N * Nᴴ) :
    ∃ (U : Matrix ι ι ℂ) (d : ι → ℂ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ N = U * diagonal d * Uᴴ := by
  classical
  set Hm : Matrix ι ι ℂ := (1 / 2 : ℂ) • (N + Nᴴ) with hHm
  set Km : Matrix ι ι ℂ := (-Complex.I / 2) • (N - Nᴴ) with hKm
  have hHmH : Hm.IsHermitian := by
    rw [IsHermitian, hHm, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose,
      add_comm]
    congr 1
    simp
  have hKmH : Km.IsHermitian := by
    rw [IsHermitian, hKm, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    have hs : star (-Complex.I / 2) = -(-Complex.I / 2) := by
      apply Complex.ext <;> norm_num
    rw [hs, neg_smul, ← smul_neg, neg_sub]
  have hsum : N = Hm + Complex.I • Km := by
    rw [hHm, hKm, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcomm : Hm * Km = Km * Hm := by
    have key : (N + Nᴴ) * (N - Nᴴ) = (N - Nᴴ) * (N + Nᴴ) := by
      simp only [add_mul, mul_add, sub_mul, mul_sub, hN]
      abel
    rw [hHm, hKm, smul_mul_smul_comm, smul_mul_smul_comm, key, mul_comm (1 / 2 : ℂ)]
  clear_value Hm Km
  set TH := toEuclideanLin Hm with hTH
  set TK := toEuclideanLin Km with hTK
  have hTHs : TH.IsSymmetric := isSymmetric_toEuclideanLin_iff.2 hHmH
  have hTKs : TK.IsSymmetric := isSymmetric_toEuclideanLin_iff.2 hKmH
  have hTc : Commute TH TK := by
    show TH * TK = TK * TH
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, hTH, hTK, ← toLpLin_mul_same,
      ← toLpLin_mul_same, hcomm]
  have hint := LinearMap.IsSymmetric.directSum_isInternal_of_commute hTHs hTKs hTc
  have horth := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hTHs hTKs
  -- only finitely many joint eigenspaces are nonzero; restrict to those
  set V : ℂ × ℂ → Submodule ℂ (EuclideanSpace ℂ ι) :=
    fun i => Module.End.eigenspace TH i.2 ⊓ Module.End.eigenspace TK i.1 with hV
  let : Fintype {i // V i ≠ ⊥} := hint.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hint' : DirectSum.IsInternal fun i : {i // V i ≠ ⊥} => V i :=
    DirectSum.isInternal_ne_bot_iff.2 hint
  have horth' := horth.comp (f := fun i : {i // V i ≠ ⊥} => i.1) Subtype.val_injective
  set b₀ := hint'.subordinateOrthonormalBasis finrank_euclideanSpace horth' with hb₀
  set b := b₀.reindex (Fintype.equivFin ι).symm with hb
  have heig : ∀ j, ∃ α β : ℂ, TH (b j) = α • b j ∧ TK (b j) = β • b j := by
    intro j
    have hm := hint'.subordinateOrthonormalBasis_subordinate finrank_euclideanSpace
      ((Fintype.equivFin ι) j) horth'
    have hbj : b j = b₀ ((Fintype.equivFin ι) j) := by
      rw [hb, OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    rw [hbj]
    exact ⟨_, _, Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hm).1,
      Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hm).2⟩
  choose α β hα hβ using heig
  set d : ι → ℂ := fun j => α j + Complex.I * β j with hd
  have hNb : ∀ j, N *ᵥ (b j).ofLp = d j • (b j).ofLp := by
    intro j
    have h1 : Hm *ᵥ (b j).ofLp = α j • (b j).ofLp := by
      have := congrArg WithLp.ofLp (hα j)
      simpa [hTH, toLpLin_apply] using this
    have h2 : Km *ᵥ (b j).ofLp = β j • (b j).ofLp := by
      have := congrArg WithLp.ofLp (hβ j)
      simpa [hTK, toLpLin_apply] using this
    rw [hsum, add_mulVec, smul_mulVec, h1, h2, smul_smul, hd, add_smul]
  set U : Matrix ι ι ℂ := Matrix.of fun i j => (b j).ofLp i with hU
  have hUU : Uᴴ * U = 1 := by
    ext j k
    have h := (orthonormal_iff_ite.1 b.orthonormal) j k
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    simp only [hU, conjTranspose_apply, Matrix.of_apply, dotProduct, Pi.star_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUU
  have hNU : N * U = U * diagonal d := by
    ext i j
    rw [mul_diagonal]
    have := congrFun (hNb j) i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, hU, Matrix.of_apply, this]
    ring
  refine ⟨U, d, hUU, hUU', ?_⟩
  calc N = N * (U * Uᴴ) := by rw [hUU', mul_one]
    _ = U * diagonal d * Uᴴ := by rw [← mul_assoc, hNU]

end MathLab

end

end -- public section

#print axioms MathLab.normal_spectral
