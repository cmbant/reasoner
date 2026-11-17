module

public import Mathlib
public import FormalResearch.MatrixAnalysis.TraceNorm
public import FormalResearch.MatrixAnalysis.Spectral.Lidskii
public import FormalResearch.MatrixAnalysis.Spectral.HoffmanWielandt
public import FormalResearch.MatrixAnalysis.Spectral.KyFanProj

/-!
# Weyl, interlacing, Ky Fan and Lidskii for Hermitian matrices

Namespace `FormalResearch.MatrixAnalysis.Spectral`.  Claim class: **proved** (no hypothesis, no new axiom).

Matrix form of `Spectral.MinMax`, `Spectral.Weyl`, `Spectral.KyFan` and `Spectral.Lidskii`.  For a Hermitian
`A : Matrix n n 𝕜` (`𝕜 = ℝ` or `ℂ`), `λ_j(A) := hA.eigenvalues₀ j` (`j : Fin (Fintype.card n)`, Mathlib's
descending list; `λ_0 ≥ ⋯ ≥ λ_{N-1}`, `N = card n`) is `hT.eigenvalues` for `T = toEuclideanLin A`
(`eigenvalues₀_eq`), so every abstract statement transfers verbatim.

* `herm_courant_fischer_maxmin`, `herm_courant_fischer_minmax`: Courant–Fischer.
* `herm_weyl_add_le`, `herm_weyl_le_add`: `λ_{i+j}(A+B) ≤ λ_i(A) + λ_j(B)` and the dual.
* `herm_eigenvalues₀_mono`: Loewner monotonicity.  `herm_abs_eigenvalues₀_sub_le`: `|λ_k(A) - λ_k(B)| ≤ ‖A - B‖`
  (spectral norm).
* `herm_interlace_le`, `herm_interlace_ge`: Cauchy interlacing for `Jᴴ A J` with `Jᴴ J = 1`;
  `herm_interlace_submatrix_*`: principal submatrices.
* `herm_partial_sum_add_le`: Ky Fan subadditivity.
* `herm_sum_sq_eigenvalues₀_eq`, `herm_hoffman_wielandt`: `Σ_j λ_j(C)² = Σ_{ij} |C_ij|²` and Hoffman–Wielandt
  `Σ_j (λ_j(A) - λ_j(B))² ≤ Σ_{ij} |(A-B)_{ij}|²`; `herm_sum_mul_le`: von Neumann `Re tr(AB) ≤ Σ λ_j(A)λ_j(B)`.
* `herm_kyFan_projection_le`, `herm_kyFan_projection_isGreatest`: Ky Fan maximum principle
  `Σ_{i<k} λ_i(A) = max { Re tr(PA) : P = P* = P², tr P = k }`.
* `herm_lidskii_sum_le`, `herm_lidskii_abs_sum_le`, `herm_lidskii_tnorm`: Lidskii, the last one with the
  repository's `tnorm`: `Σ_j |λ_j(A) - λ_j(B)| ≤ ‖A - B‖₁`.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis.Spectral

open Module Matrix

/-- Eigenvalues only depend on the operator. -/
theorem eigenvalues_congr {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {T₁ T₂ : E →ₗ[𝕜] E} (h : T₁ = T₂)
    (h1 : T₁.IsSymmetric) (h2 : T₂.IsSymmetric) {N : ℕ} (hN : finrank 𝕜 E = N) :
    h1.eigenvalues hN = h2.eigenvalues hN := by
  subst h; rfl

section Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  {A B : Matrix n n 𝕜}

/-- The symmetric operator `toEuclideanLin A` of a Hermitian matrix. -/
theorem hsym (hA : A.IsHermitian) : (toEuclideanLin A).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr hA

theorem eigenvalues₀_eq (hA : A.IsHermitian) :
    hA.eigenvalues₀ = (hsym hA).eigenvalues finrank_euclideanSpace := rfl

theorem eigenvalues₀_add (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (hA.add hB).eigenvalues₀ = ((hsym hA).add (hsym hB)).eigenvalues finrank_euclideanSpace :=
  eigenvalues_congr (map_add _ _ _) _ _ _

theorem eigenvalues₀_sub (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (hA.sub hB).eigenvalues₀ = ((hsym hA).sub (hsym hB)).eigenvalues finrank_euclideanSpace :=
  eigenvalues_congr (map_sub _ _ _) _ _ _

/-- The Rayleigh form of `toEuclideanLin A` is `Re (x* A x)`. -/
theorem rq_toEuclideanLin (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    rq (toEuclideanLin A) x = RCLike.re (star (WithLp.ofLp x) ⬝ᵥ A *ᵥ WithLp.ofLp x) := by
  simp [rq, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, dotProduct_comm]

theorem eigenvalues₀_congr {A B : Matrix n n 𝕜} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hA.eigenvalues₀ = hB.eigenvalues₀ := by
  subst h; rfl

/-- Reindexing the eigenvalues from `Fin (card n)` to `n`. -/
theorem sum_eigenvalues₀_eq (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ∑ j, f (hA.eigenvalues₀ j) = ∑ i, f (hA.eigenvalues i) := by
  unfold Matrix.IsHermitian.eigenvalues
  exact (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun j => f (hA.eigenvalues₀ j))).symm

theorem trace_toEuclideanLin (M : Matrix n n 𝕜) :
    (toEuclideanLin M).trace 𝕜 (EuclideanSpace 𝕜 n) = M.trace := by
  rw [LinearMap.trace_eq_matrix_trace 𝕜 (EuclideanSpace.basisFun n 𝕜).toBasis,
    toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

section CourantFischer

/-- **Courant–Fischer (max–min) for Hermitian matrices.** -/
theorem herm_courant_fischer_maxmin (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    IsGreatest {c : ℝ | ∃ V : Submodule 𝕜 (EuclideanSpace 𝕜 n), finrank 𝕜 V = k + 1 ∧
      ∀ x ∈ V, c * ‖x‖ ^ 2 ≤ RCLike.re (star (WithLp.ofLp x) ⬝ᵥ A *ᵥ WithLp.ofLp x)}
      (hA.eigenvalues₀ k) := by
  have := courant_fischer_maxmin (hsym hA) finrank_euclideanSpace k
  simp only [rq_toEuclideanLin] at this
  exact this

/-- **Courant–Fischer (min–max) for Hermitian matrices.** -/
theorem herm_courant_fischer_minmax (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    IsLeast {c : ℝ | ∃ W : Submodule 𝕜 (EuclideanSpace 𝕜 n), finrank 𝕜 W = Fintype.card n - k ∧
      ∀ x ∈ W, RCLike.re (star (WithLp.ofLp x) ⬝ᵥ A *ᵥ WithLp.ofLp x) ≤ c * ‖x‖ ^ 2}
      (hA.eigenvalues₀ k) := by
  have := courant_fischer_minmax (hsym hA) finrank_euclideanSpace k
  simp only [rq_toEuclideanLin] at this
  exact this

end CourantFischer

section Weyl

/-- **Weyl's inequality.** -/
theorem herm_weyl_add_le (hA : A.IsHermitian) (hB : B.IsHermitian) (i j k : Fin (Fintype.card n))
    (hk : (k : ℕ) = i + j) :
    (hA.add hB).eigenvalues₀ k ≤ hA.eigenvalues₀ i + hB.eigenvalues₀ j := by
  rw [eigenvalues₀_add hA hB]
  exact weyl_add_le (hsym hA) (hsym hB) finrank_euclideanSpace i j k hk

/-- **Weyl's inequality (dual form).** -/
theorem herm_weyl_le_add (hA : A.IsHermitian) (hB : B.IsHermitian) (i j k : Fin (Fintype.card n))
    (hk : (i : ℕ) + j + 1 = k + Fintype.card n) :
    hA.eigenvalues₀ i + hB.eigenvalues₀ j ≤ (hA.add hB).eigenvalues₀ k := by
  rw [eigenvalues₀_add hA hB]
  exact weyl_le_add (hsym hA) (hsym hB) finrank_euclideanSpace i j k hk

/-- **Loewner monotonicity of ordered eigenvalues.** -/
theorem herm_eigenvalues₀_mono (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x : n → 𝕜, 0 ≤ RCLike.re (star x ⬝ᵥ (B - A) *ᵥ x)) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  refine eigenvalue_mono (hsym hA) (hsym hB) finrank_euclideanSpace (fun x => ?_) k
  have := h (WithLp.ofLp x)
  rw [sub_mulVec, dotProduct_sub, map_sub, sub_nonneg] at this
  rwa [rq_toEuclideanLin, rq_toEuclideanLin]

/-- **Weyl's perturbation theorem**, `ε`-form: if `‖(A - B) x‖ ≤ ε ‖x‖` then `|λ_k(A) - λ_k(B)| ≤ ε`. -/
theorem herm_abs_eigenvalues₀_sub_le (hA : A.IsHermitian) (hB : B.IsHermitian) {ε : ℝ}
    (h : ∀ x : EuclideanSpace 𝕜 n, ‖toEuclideanLin (A - B) x‖ ≤ ε * ‖x‖) (k : Fin (Fintype.card n)) :
    |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ ε :=
  abs_eigenvalue_sub_le (hsym hA) (hsym hB) finrank_euclideanSpace
    (fun x => by simpa [map_sub] using h x) k

open scoped Matrix.Norms.L2Operator in
/-- **Weyl's perturbation theorem** in the spectral norm: `|λ_k(A) - λ_k(B)| ≤ ‖A - B‖`. -/
theorem herm_abs_eigenvalues₀_sub_le_norm (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : Fin (Fintype.card n)) : |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ ‖A - B‖ :=
  herm_abs_eigenvalues₀_sub_le hA hB (fun x => Matrix.l2_opNorm_mulVec (A - B) x) k

end Weyl

section Interlace

variable {m : Type*} [Fintype m] [DecidableEq m] (J : Matrix n m 𝕜) (hJ : Jᴴ * J = 1)

include hJ in
theorem inner_toEuclideanLin_isometry (x y : EuclideanSpace 𝕜 m) :
    inner 𝕜 (toEuclideanLin J x) (toEuclideanLin J y) = inner 𝕜 x y := by
  rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← LinearMap.comp_apply,
    ← Matrix.toLpLin_mul_same, hJ, Matrix.toLpLin_one, LinearMap.id_apply]

/-- `toEuclideanLin J` as a linear isometry when `Jᴴ J = 1`. -/
noncomputable def isometryOfConjTransposeMul : EuclideanSpace 𝕜 m →ₗᵢ[𝕜] EuclideanSpace 𝕜 n :=
  (toEuclideanLin J).isometryOfInner (inner_toEuclideanLin_isometry J hJ)

include hJ in
theorem card_le_of_conjTranspose_mul : Fintype.card m ≤ Fintype.card n := by
  have := LinearMap.finrank_le_finrank_of_injective (isometryOfConjTransposeMul J hJ).injective
  simpa [finrank_euclideanSpace] using this

include hJ in
theorem hcomp_conj (y : EuclideanSpace 𝕜 m) :
    inner 𝕜 y (toEuclideanLin (Jᴴ * A * J) y) =
      inner 𝕜 (isometryOfConjTransposeMul J hJ y) (toEuclideanLin A (isometryOfConjTransposeMul J hJ y)) := by
  simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]
  rfl

include hJ in
/-- **Cauchy interlacing (upper).**  `λ_k(Jᴴ A J) ≤ λ_k(A)` for `Jᴴ J = 1`. -/
theorem herm_interlace_le (hA : A.IsHermitian) (k : Fin (Fintype.card m)) (k' : Fin (Fintype.card n))
    (hk : (k' : ℕ) = k) :
    (isHermitian_conjTranspose_mul_mul J hA).eigenvalues₀ k ≤ hA.eigenvalues₀ k' := by
  have hkn : (k : ℕ) < Fintype.card n := by
    have := card_le_of_conjTranspose_mul J hJ; omega
  have := interlace_le (hsym hA) finrank_euclideanSpace (hsym (isHermitian_conjTranspose_mul_mul J hA))
    finrank_euclideanSpace (isometryOfConjTransposeMul J hJ) (hcomp_conj J hJ) k hkn
  obtain rfl : k' = ⟨k, by omega⟩ := Fin.ext hk
  exact this

include hJ in
/-- **Cauchy interlacing (lower).**  `λ_{k'}(A) ≤ λ_k(Jᴴ A J)` for `k' + card m = k + card n`. -/
theorem herm_interlace_ge (hA : A.IsHermitian) (k : Fin (Fintype.card m)) (k' : Fin (Fintype.card n))
    (hk : (k' : ℕ) + Fintype.card m = k + Fintype.card n) :
    hA.eigenvalues₀ k' ≤ (isHermitian_conjTranspose_mul_mul J hA).eigenvalues₀ k :=
  interlace_ge (hsym hA) finrank_euclideanSpace (hsym (isHermitian_conjTranspose_mul_mul J hA))
    finrank_euclideanSpace (isometryOfConjTransposeMul J hJ) (hcomp_conj J hJ) k k' hk

end Interlace

section Submatrix

variable {m : Type*} [Fintype m] [DecidableEq m] (f : m → n) (hf : Function.Injective f)

/-- The `0/1` matrix of the coordinate embedding `f`. -/
def embedMatrix : Matrix n m 𝕜 := Matrix.of fun i a => if f a = i then 1 else 0

omit [Fintype m] in
include hf in
theorem embedMatrix_conjTranspose_mul :
    (embedMatrix (𝕜 := 𝕜) f)ᴴ * embedMatrix (𝕜 := 𝕜) f = 1 := by
  ext a b
  simp [embedMatrix, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]

omit [Fintype m] [DecidableEq m] in
theorem embedMatrix_conj (A : Matrix n n 𝕜) :
    (embedMatrix (𝕜 := 𝕜) f)ᴴ * A * embedMatrix (𝕜 := 𝕜) f = A.submatrix f f := by
  ext a b
  simp [embedMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_ite_eq]

include hf in
/-- **Cauchy interlacing for principal submatrices (upper).**  `λ_k(A_S) ≤ λ_k(A)`. -/
theorem herm_interlace_submatrix_le (hA : A.IsHermitian) (k : Fin (Fintype.card m))
    (k' : Fin (Fintype.card n)) (hk : (k' : ℕ) = k) :
    (hA.submatrix f).eigenvalues₀ k ≤ hA.eigenvalues₀ k' := by
  have := herm_interlace_le (embedMatrix (𝕜 := 𝕜) f) (embedMatrix_conjTranspose_mul f hf) hA k k' hk
  rwa [eigenvalues₀_congr (embedMatrix_conj f A) (isHermitian_conjTranspose_mul_mul _ hA) (hA.submatrix f)] at this

include hf in
/-- **Cauchy interlacing for principal submatrices (lower).**  `λ_{k'}(A) ≤ λ_k(A_S)` when
`k' + card m = k + card n`. -/
theorem herm_interlace_submatrix_ge (hA : A.IsHermitian) (k : Fin (Fintype.card m))
    (k' : Fin (Fintype.card n)) (hk : (k' : ℕ) + Fintype.card m = k + Fintype.card n) :
    hA.eigenvalues₀ k' ≤ (hA.submatrix f).eigenvalues₀ k := by
  have := herm_interlace_ge (embedMatrix (𝕜 := 𝕜) f) (embedMatrix_conjTranspose_mul f hf) hA k k' hk
  rwa [eigenvalues₀_congr (embedMatrix_conj f A) (isHermitian_conjTranspose_mul_mul _ hA) (hA.submatrix f)] at this

end Submatrix

section KyFanLidskii

/-- **Ky Fan subadditivity** for Hermitian matrices: the sum of the `k` largest eigenvalues is subadditive. -/
theorem herm_partial_sum_add_le (hA : A.IsHermitian) (hB : B.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card n) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card n) => (i : ℕ) < k), (hA.add hB).eigenvalues₀ i ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card n) => (i : ℕ) < k), hA.eigenvalues₀ i +
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card n) => (i : ℕ) < k), hB.eigenvalues₀ i := by
  rw [eigenvalues₀_add hA hB]
  exact partial_sum_add_le (hsym hA) (hsym hB) finrank_euclideanSpace hk

/-- **Lidskii–Wielandt** for Hermitian matrices: for `J` of cardinality `k`,
`Σ_{j∈J} (λ_j(A) - λ_j(B)) ≤ Σ_{i<k} λ_i(A - B)`. -/
theorem herm_lidskii_sum_le (hA : A.IsHermitian) (hB : B.IsHermitian) (J : Finset (Fin (Fintype.card n))) :
    ∑ j ∈ J, (hA.eigenvalues₀ j - hB.eigenvalues₀ j) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card n) => (i : ℕ) < J.card),
        (hA.sub hB).eigenvalues₀ i := by
  rw [eigenvalues₀_sub hA hB]
  exact lidskii_sum_le finrank_euclideanSpace (hsym hA) (hsym hB) J

/-- **Lidskii, absolute form** for Hermitian matrices over `ℝ` or `ℂ`:
`Σ_j |λ_j(A) - λ_j(B)| ≤ Σ_i |λ_i(A - B)|`. -/
theorem herm_lidskii_abs_sum_le (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤ ∑ i, |(hA.sub hB).eigenvalues i| := by
  rw [← sum_eigenvalues₀_eq (hA.sub hB) (fun x => |x|), eigenvalues₀_sub hA hB]
  exact lidskii_abs_sum_le finrank_euclideanSpace (hsym hA) (hsym hB)

end KyFanLidskii

section KyFanProjection

/-- **Ky Fan inequality, projection form**, for Hermitian matrices: for an orthogonal projection `P`
(`P* = P`, `P² = P`) of trace `k`, `Re tr(PA) ≤ Σ_{i<k} λ_i(A)`. -/
theorem herm_kyFan_projection_le (hA : A.IsHermitian) (P : Matrix n n 𝕜) (hP : P.IsHermitian)
    (hPP : P * P = P) {k : ℕ} (hk : P.trace = (k : 𝕜)) :
    RCLike.re (P * A).trace ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card n) => (i : ℕ) < k), hA.eigenvalues₀ i := by
  have h := kyFan_projection_le (hsym hA) finrank_euclideanSpace (hsym hP)
    (by rw [← Matrix.toLpLin_mul_same, hPP]) (k := k) (by rw [trace_toEuclideanLin, hk])
  rwa [← Matrix.toLpLin_mul_same, trace_toEuclideanLin] at h

/-- **Ky Fan maximum principle for Hermitian matrices.**  For `k ≤ card n`,
`Σ_{i<k} λ_i(A) = max { Re tr(PA) : P = P* = P², tr P = k }`. -/
theorem herm_kyFan_projection_isGreatest (hA : A.IsHermitian) {k : ℕ} (hk : k ≤ Fintype.card n) :
    IsGreatest {s : ℝ | ∃ P : Matrix n n 𝕜, P.IsHermitian ∧ P * P = P ∧ P.trace = (k : 𝕜) ∧
        s = RCLike.re (P * A).trace}
      (∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card n) => (i : ℕ) < k), hA.eigenvalues₀ i) := by
  obtain ⟨⟨Q, hQ, hQQ, hQk, hQs⟩, hub⟩ := kyFan_projection_isGreatest (hsym hA) finrank_euclideanSpace hk
  set P : Matrix n n 𝕜 := (toEuclideanLin (𝕜 := 𝕜) (m := n) (n := n)).symm Q with hP
  have hPQ : toEuclideanLin P = Q := (toEuclideanLin (𝕜 := 𝕜) (m := n) (n := n)).apply_symm_apply Q
  refine ⟨⟨P, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact isSymmetric_toEuclideanLin_iff.mp (hPQ ▸ hQ)
  · apply toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, hPQ, hQQ]
  · rw [← trace_toEuclideanLin, hPQ, hQk]
  · refine hQs.trans ?_
    rw [← hPQ, ← Matrix.toLpLin_mul_same, trace_toEuclideanLin]
  · rintro s ⟨P', hP', hP'P', hk', rfl⟩
    exact herm_kyFan_projection_le hA P' hP' hP'P' hk'

end KyFanProjection

section Frobenius

/-- `Σ_j λ_j(C)² = Σ_{ij} |C_ij|²` for Hermitian `C`. -/
theorem herm_sum_sq_eigenvalues₀_eq (hC : A.IsHermitian) :
    ∑ j, hC.eigenvalues₀ j ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h := sum_sq_eigenvalues_eq (hsym hC) finrank_euclideanSpace (EuclideanSpace.basisFun n 𝕜)
  refine h.trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.toLpLin_apply]

/-- **Hoffman–Wielandt** for Hermitian matrices:
`Σ_j (λ_j(A) - λ_j(B))² ≤ Σ_{ij} |(A - B)_{ij}|²`. -/
theorem herm_hoffman_wielandt (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j, (hA.eigenvalues₀ j - hB.eigenvalues₀ j) ^ 2 ≤ ∑ i, ∑ j, ‖(A - B) i j‖ ^ 2 := by
  rw [← herm_sum_sq_eigenvalues₀_eq (hA.sub hB), eigenvalues₀_sub hA hB]
  exact hoffman_wielandt (hsym hA) (hsym hB) finrank_euclideanSpace

/-- **Von Neumann's trace inequality** (Hermitian form): `Re tr(AB) ≤ Σ_j λ_j(A) λ_j(B)`. -/
theorem herm_sum_mul_le (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace ≤ ∑ j, hA.eigenvalues₀ j * hB.eigenvalues₀ j := by
  have htr : (toEuclideanLin (A * B)).trace 𝕜 (EuclideanSpace 𝕜 n) = (A * B).trace := by
    rw [LinearMap.trace_eq_matrix_trace 𝕜 (EuclideanSpace.basisFun n 𝕜).toBasis,
      toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  rw [← htr, LinearMap.trace_eq_sum_inner _ ((hsym hB).eigenvectorBasis finrank_euclideanSpace), map_sum]
  have h := sum_mul_rq_le (hsym hA) (hsym hB) finrank_euclideanSpace
  have e : ∀ j, RCLike.re (inner 𝕜 ((hsym hB).eigenvectorBasis finrank_euclideanSpace j)
      (toEuclideanLin (A * B) ((hsym hB).eigenvectorBasis finrank_euclideanSpace j))) =
      hB.eigenvalues₀ j * rq (toEuclideanLin A) ((hsym hB).eigenvectorBasis finrank_euclideanSpace j) := by
    intro j
    rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, (hsym hB).apply_eigenvectorBasis, map_smul,
      inner_smul_right, RCLike.re_ofReal_mul]
    rfl
  simp_rw [e]
  exact h.trans (le_of_eq (Finset.sum_congr rfl fun j _ => mul_comm _ _))

end Frobenius

section RankOne

omit [Fintype n] [DecidableEq n] in
theorem isHermitian_vecMulVec_star (v : n → 𝕜) : (vecMulVec v (star v)).IsHermitian := by
  ext i j
  simp [conjTranspose_apply, vecMulVec_apply, mul_comm]

theorem toEuclideanLin_vecMulVec (v : n → 𝕜) :
    toEuclideanLin (vecMulVec v (star v)) = rankOne (𝕜 := 𝕜) (WithLp.toLp 2 v) := by
  ext x : 1
  simp only [rankOne, Matrix.toLpLin_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, EuclideanSpace.inner_eq_star_dotProduct,
    vecMulVec_mulVec]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, PiLp.smul_apply]
  rw [dotProduct_comm (star v), mul_comm]

/-- **Rank-one interlacing.**  For `v : n → 𝕜` and `k = l + 1`,
`λ_k(A) ≤ λ_k(A + v v*) ≤ λ_l(A)`. -/
theorem herm_interlace_rankOne (hA : A.IsHermitian) (v : n → 𝕜) (l k : Fin (Fintype.card n))
    (hk : (k : ℕ) = l + 1) :
    hA.eigenvalues₀ k ≤ (hA.add (isHermitian_vecMulVec_star v)).eigenvalues₀ k ∧
    (hA.add (isHermitian_vecMulVec_star v)).eigenvalues₀ k ≤ hA.eigenvalues₀ l := by
  have h := interlace_rankOne (hsym hA) finrank_euclideanSpace (WithLp.toLp 2 v) l k hk
  have e : (hA.add (isHermitian_vecMulVec_star v)).eigenvalues₀ =
      ((hsym hA).add (isSymmetric_rankOne (𝕜 := 𝕜) (WithLp.toLp 2 v))).eigenvalues
        finrank_euclideanSpace :=
    eigenvalues_congr (by rw [map_add, toEuclideanLin_vecMulVec]) _ _ _
  rw [e]
  exact h

end RankOne

end Matrix

section Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lidskii's theorem for the trace norm.**  For Hermitian `A, B : Matrix n n ℂ`,
`Σ_j |λ_j(A) - λ_j(B)| ≤ ‖A - B‖₁`, where `‖·‖₁ = FormalResearch.MatrixAnalysis.tnorm`. -/
theorem herm_lidskii_tnorm {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤ FormalResearch.MatrixAnalysis.tnorm (A - B) := by
  rw [FormalResearch.MatrixAnalysis.tnorm_eq (hA.sub hB)]
  exact herm_lidskii_abs_sum_le hA hB

open scoped ComplexOrder in
/-- **Loewner monotonicity** for complex Hermitian matrices: `B - A ⪰ 0` implies `λ_k(A) ≤ λ_k(B)`. -/
theorem herm_eigenvalues₀_mono_posSemidef {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : (B - A).PosSemidef) (k : Fin (Fintype.card n)) : hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k :=
  herm_eigenvalues₀_mono hA hB (fun x => h.re_dotProduct_nonneg x) k

end Complex

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_courant_fischer_maxmin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_courant_fischer_maxmin

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_courant_fischer_minmax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_courant_fischer_minmax

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_weyl_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_weyl_add_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_weyl_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_weyl_le_add

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_eigenvalues₀_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_eigenvalues₀_mono

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_eigenvalues₀_mono_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_eigenvalues₀_mono_posSemidef

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_abs_eigenvalues₀_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_abs_eigenvalues₀_sub_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_abs_eigenvalues₀_sub_le_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_abs_eigenvalues₀_sub_le_norm

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_interlace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_interlace_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_interlace_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_interlace_ge

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_interlace_submatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_interlace_submatrix_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_interlace_submatrix_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_interlace_submatrix_ge

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_interlace_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_interlace_rankOne

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_partial_sum_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_partial_sum_add_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_lidskii_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_lidskii_sum_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_lidskii_abs_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_lidskii_abs_sum_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_lidskii_tnorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_lidskii_tnorm

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_sum_sq_eigenvalues₀_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_sum_sq_eigenvalues₀_eq

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_hoffman_wielandt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_hoffman_wielandt

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_sum_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_sum_mul_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_kyFan_projection_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_kyFan_projection_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.herm_kyFan_projection_isGreatest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.herm_kyFan_projection_isGreatest

end FormalResearch.MatrixAnalysis.Spectral
