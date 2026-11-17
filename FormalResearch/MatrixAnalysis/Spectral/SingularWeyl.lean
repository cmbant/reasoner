module

public import FormalResearch.MatrixAnalysis.Spectral.Weyl

/-!
# Weyl's inequality for singular values

Namespace `FormalResearch.MatrixAnalysis.Spectral`.  Claim class: **proved** (no hypothesis, no new axiom).

For linear maps `S, T : E →ₗ[𝕜] F` between finite-dimensional inner product spaces over `ℝ` or `ℂ`,
`dim E = N`, let `σ_k(T) = T.singularValues k` (Mathlib: `√ μ_k(T† T)`, zero for `k ≥ N`).

* `rq_adjoint_comp`: `Re⟪x, T† T x⟫ = ‖T x‖²`.
* `singularValues_le_of_subspace`: if `‖T x‖ ≤ c ‖x‖` on a subspace of dimension `≥ N - k` then `σ_k(T) ≤ c`.
* `norm_apply_le_singularValues`: `‖T x‖ ≤ σ_k(T) ‖x‖` on `span{v_k, …, v_{N-1}}` (right singular vectors).
* `singularValues_add_le`: **Weyl for singular values**, `σ_{i+j}(S+T) ≤ σ_i(S) + σ_j(T)` for all `i, j : ℕ`
  (Horn–Johnson, Thm 7.3.8(a)); no Hermitian dilation is needed because the min–max certificate applies to
  `‖T x‖` directly.
* `abs_singularValues_sub_le`: `‖(S - T) x‖ ≤ ε ‖x‖` for all `x` implies `|σ_k(S) - σ_k(T)| ≤ ε`.
* `singularValues_zero_le`, `norm_apply_le_singularValues_zero`: `σ_0` is the operator norm.

Not formalised here: Fan's dominance/Ky Fan norms of singular values, and Horn's multiplicative inequalities.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis.Spectral

open Module

section

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F) {N : ℕ} (hN : finrank 𝕜 E = N)

theorem rq_adjoint_comp (x : E) : rq (LinearMap.adjoint T ∘ₗ T) x = ‖T x‖ ^ 2 := by
  simp only [rq, LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]

include hN in
/-- Eigenvalues of `T† T` are the squares of the singular values. -/
theorem sq_singularValues_eq (k : Fin N) :
    T.singularValues k ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hN k :=
  T.sq_singularValues_fin hN k

include hN in
/-- **Upper certificate for singular values.** -/
theorem singularValues_le_of_subspace {W : Submodule 𝕜 E} {c : ℝ} (hc : 0 ≤ c) (k : Fin N)
    (hW : N - (k : ℕ) ≤ finrank 𝕜 W) (h : ∀ x ∈ W, ‖T x‖ ≤ c * ‖x‖) :
    T.singularValues k ≤ c := by
  have h1 : T.isSymmetric_adjoint_comp_self.eigenvalues hN k ≤ c ^ 2 :=
    eigenvalue_le_of_subspace T.isSymmetric_adjoint_comp_self hN k hW (fun x hx => by
      rw [rq_adjoint_comp]
      calc ‖T x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by gcongr; exact h x hx
        _ = c ^ 2 * ‖x‖ ^ 2 := by ring)
  rw [← sq_singularValues_eq T hN k] at h1
  exact le_of_sq_le_sq (by simpa using h1) hc |>.trans le_rfl

include hN in
/-- The singular-vector certificate: on `span{v_k, …, v_{N-1}}` one has `‖T x‖ ≤ σ_k ‖x‖`. -/
theorem norm_apply_le_singularValues (k : Fin N) {x : E}
    (hx : x ∈ botSpan T.isSymmetric_adjoint_comp_self hN k) : ‖T x‖ ≤ T.singularValues k * ‖x‖ := by
  have h := rq_le_eigenvalue_mul_botSpan T.isSymmetric_adjoint_comp_self hN k hx
  rw [rq_adjoint_comp, ← sq_singularValues_eq T hN k] at h
  have h0 := T.singularValues_nonneg k
  have : ‖T x‖ ^ 2 ≤ (T.singularValues k * ‖x‖) ^ 2 := by nlinarith
  exact le_of_sq_le_sq this (by positivity)

end

section Weyl

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F] (S T : E →ₗ[𝕜] F) {N : ℕ} (hN : finrank 𝕜 E = N)

include hN in
/-- **Weyl's inequality for singular values (finite range).** -/
theorem singularValues_add_le_fin (i j k : Fin N) (hk : (k : ℕ) = i + j) :
    (S + T).singularValues k ≤ S.singularValues i + T.singularValues j := by
  have hi := i.isLt
  have hj := j.isLt
  refine singularValues_le_of_subspace (S + T) hN
    (add_nonneg (S.singularValues_nonneg _) (T.singularValues_nonneg _)) k
    (W := botSpan S.isSymmetric_adjoint_comp_self hN i ⊓ botSpan T.isSymmetric_adjoint_comp_self hN j)
    ?_ ?_
  · have := finrank_add_le_finrank_inf (botSpan S.isSymmetric_adjoint_comp_self hN i)
      (botSpan T.isSymmetric_adjoint_comp_self hN j)
    rw [finrank_botSpan _ hN, finrank_botSpan _ hN, hN] at this
    omega
  · rintro x ⟨hxS, hxT⟩
    have h1 := norm_apply_le_singularValues S hN i hxS
    have h2 := norm_apply_le_singularValues T hN j hxT
    calc ‖(S + T) x‖ = ‖S x + T x‖ := rfl
      _ ≤ ‖S x‖ + ‖T x‖ := norm_add_le _ _
      _ ≤ (S.singularValues i + T.singularValues j) * ‖x‖ := by linarith

/-- **Weyl's inequality for singular values.**  `σ_{i+j}(S+T) ≤ σ_i(S) + σ_j(T)` for all `i, j : ℕ`. -/
theorem singularValues_add_le (i j : ℕ) :
    (S + T).singularValues (i + j) ≤ S.singularValues i + T.singularValues j := by
  set N := finrank 𝕜 E with hNdef
  by_cases h : i + j < N
  · exact singularValues_add_le_fin S T (N := N) rfl ⟨i, by omega⟩ ⟨j, by omega⟩ ⟨i + j, h⟩ rfl
  · rw [LinearMap.singularValues_of_finrank_le _ (by omega)]
    exact add_nonneg (S.singularValues_nonneg _) (T.singularValues_nonneg _)

/-- `σ_0(T) ≤ c` if `‖T x‖ ≤ c ‖x‖` for all `x`. -/
theorem singularValues_zero_le {c : ℝ} (hc : 0 ≤ c) (h : ∀ x, ‖T x‖ ≤ c * ‖x‖) :
    T.singularValues 0 ≤ c := by
  rcases Nat.eq_zero_or_pos (finrank 𝕜 E) with h0 | hpos
  · rw [LinearMap.singularValues_of_finrank_le _ (by omega)]; exact hc
  · have := singularValues_le_of_subspace T (N := finrank 𝕜 E) rfl (W := ⊤) hc ⟨0, hpos⟩
      (by simp) (fun x _ => h x)
    exact this

/-- `‖T x‖ ≤ σ_0(T) ‖x‖`. -/
theorem norm_apply_le_singularValues_zero (x : E) : ‖T x‖ ≤ T.singularValues 0 * ‖x‖ := by
  rcases Nat.eq_zero_or_pos (finrank 𝕜 E) with h0 | hpos
  · have : Subsingleton E := Module.finrank_zero_iff.mp h0
    simp [Subsingleton.elim x 0]
  · have h := rq_le_eigenvalues_zero_mul T.isSymmetric_adjoint_comp_self (N := finrank 𝕜 E) rfl hpos x
    rw [rq_adjoint_comp] at h
    have h2 := sq_singularValues_eq T (N := finrank 𝕜 E) rfl ⟨0, hpos⟩
    have h0 := T.singularValues_nonneg 0
    have : ‖T x‖ ^ 2 ≤ (T.singularValues 0 * ‖x‖) ^ 2 := by
      have : T.singularValues ((⟨0, hpos⟩ : Fin (finrank 𝕜 E)) : ℕ) = T.singularValues 0 := rfl
      rw [mul_pow]
      rw [← h2] at h
      rw [this] at h
      exact h
    exact le_of_sq_le_sq this (by positivity)

/-- **Weyl's perturbation theorem for singular values.** -/
theorem abs_singularValues_sub_le {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : ℕ) :
    |S.singularValues k - T.singularValues k| ≤ ε := by
  have key : ∀ (S T : E →ₗ[𝕜] F), (∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) →
      S.singularValues k ≤ T.singularValues k + ε := by
    intro S T h
    have h1 := singularValues_add_le T (S - T) k 0
    rw [add_sub_cancel, add_zero] at h1
    have h2 := singularValues_zero_le (S - T) hε h
    linarith
  have h1 := key S T h
  have h2 := key T S (fun x => by rw [← norm_neg, ← LinearMap.neg_apply, neg_sub]; exact h x)
  rw [abs_le]
  constructor <;> linarith

end Weyl

section MatrixForm

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Singular values of a rectangular matrix, as those of `toEuclideanLin A`. -/
noncomputable def matSingularValues (A : Matrix m n 𝕜) : ℕ →₀ ℝ := (toEuclideanLin A).singularValues

/-- **Weyl's inequality for singular values of matrices.** -/
theorem matSingularValues_add_le (A B : Matrix m n 𝕜) (i j : ℕ) :
    matSingularValues (A + B) (i + j) ≤ matSingularValues A i + matSingularValues B j := by
  have := singularValues_add_le (toEuclideanLin A) (toEuclideanLin B) i j
  rwa [← map_add] at this

open scoped Matrix.Norms.L2Operator in
/-- **Weyl's perturbation theorem for matrix singular values** in the spectral norm. -/
theorem abs_matSingularValues_sub_le (A B : Matrix m n 𝕜) (k : ℕ) :
    |matSingularValues A k - matSingularValues B k| ≤ ‖A - B‖ := by
  unfold matSingularValues
  exact abs_singularValues_sub_le _ _ (norm_nonneg _)
    (fun x => by rw [← map_sub]; exact Matrix.l2_opNorm_mulVec (A - B) x) k

end MatrixForm

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.singularValues_le_of_subspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.singularValues_le_of_subspace

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.norm_apply_le_singularValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.norm_apply_le_singularValues

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.singularValues_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.singularValues_add_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.singularValues_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.singularValues_zero_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.norm_apply_le_singularValues_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.norm_apply_le_singularValues_zero

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.abs_singularValues_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.abs_singularValues_sub_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.matSingularValues_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.matSingularValues_add_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.abs_matSingularValues_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.abs_matSingularValues_sub_le

end FormalResearch.MatrixAnalysis.Spectral
