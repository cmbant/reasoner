import Mathlib

/-!
# Double commutant for `*`-subalgebras of `M_n(ℂ)` (elementary, via the von Neumann trick)

Namespace `FormalResearch.FrameFree.Twirls`.

**`bicommutant_mem`.**  Let `B ⊆ M_n(ℂ)` be a subalgebra closed under the conjugate transpose.  If `T`
commutes with every matrix that commutes with all of `B`, then `T ∈ B`.

Mathlib has no bicommutant theorem for `*`-algebras.  The proof uses the left-multiplication action
of `B` on `M_n(ℂ)` (`n` copies of the standard module), the orthogonal projection `P` of `M_n(ℂ)`
(Frobenius inner product) onto the subspace `B`, and the identity `1 ∈ B`:

1. `P` commutes with left multiplication by every `b ∈ B` (`projB_mul`), because `B` is closed under
   left multiplication by `B` and `B*`, hence so is `Bᗮ`;
2. `P` has the matrix-entry form `(P X)_{aj} = Σ_k (Q_{jk} X)_{ak}` with `Q_{jk} ∈ B'`
   (`projB_apply_eq`, `Qm_comm`), so `P` commutes with left multiplication by every `T ∈ B''`;
3. `T = T·1 = T·P(1) = P(T·1) ∈ B`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open scoped ComplexOrder

namespace FormalResearch.FrameFree.Twirls

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrices as vectors of the Euclidean space `ℂ^{ι×ι}` (Frobenius inner product). -/
noncomputable def toE : Matrix ι ι ℂ →ₗ[ℂ] EuclideanSpace ℂ (ι × ι) where
  toFun M := WithLp.toLp 2 (fun p : ι × ι => M p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Vectors of `ℂ^{ι×ι}` as matrices. -/
noncomputable def ofE : EuclideanSpace ℂ (ι × ι) →ₗ[ℂ] Matrix ι ι ℂ where
  toFun x := Matrix.of fun i j => x (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ofE_toE (M : Matrix ι ι ℂ) : ofE (toE M) = M := by ext i j; rfl

theorem inner_toE (A B : Matrix ι ι ℂ) : inner ℂ (toE A) (toE B) = (Aᴴ * B).trace := by
  simp only [PiLp.inner_apply, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.inner_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_comm]; rfl

section Bicommutant

variable (B : Subalgebra ℂ (Matrix ι ι ℂ))

/-- Orthogonal projection (Frobenius) of `M_n(ℂ)` onto the subspace `B`. -/
noncomputable def projB : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  ofE ∘ₗ ((B.toSubmodule.map toE).starProjection : EuclideanSpace ℂ (ι × ι) →L[ℂ] _).toLinearMap
    ∘ₗ toE

theorem projB_mem (X : Matrix ι ι ℂ) : projB B X ∈ B := by
  have h := Submodule.starProjection_apply_mem (B.toSubmodule.map toE) (toE X)
  obtain ⟨b, hb, hbe⟩ := Submodule.mem_map.1 h
  have : projB B X = b := by
    show ofE ((B.toSubmodule.map toE).starProjection (toE X)) = b
    rw [← hbe]; simp
  rw [this]; exact hb

theorem projB_orth (X : Matrix ι ι ℂ) {c : Matrix ι ι ℂ} (hc : c ∈ B) :
    ((X - projB B X)ᴴ * c).trace = 0 := by
  have h := Submodule.starProjection_inner_eq_zero (K := B.toSubmodule.map toE) (toE X) (toE c)
    (Submodule.mem_map_of_mem hc)
  have e : toE X - (B.toSubmodule.map toE).starProjection (toE X) = toE (X - projB B X) := by
    have : toE (projB B X) = (B.toSubmodule.map toE).starProjection (toE X) := by
      obtain ⟨b, hb, hbe⟩ := Submodule.mem_map.1
        (Submodule.starProjection_apply_mem (B.toSubmodule.map toE) (toE X))
      have h2 : projB B X = b := by
        show ofE ((B.toSubmodule.map toE).starProjection (toE X)) = b
        rw [← hbe]; simp
      rw [h2]; exact hbe
    rw [map_sub, this]
  rw [e, inner_toE] at h
  exact h

theorem projB_unique (X Y : Matrix ι ι ℂ) (hY : Y ∈ B)
    (h : ∀ c ∈ B, ((X - Y)ᴴ * c).trace = 0) : projB B X = Y := by
  have hD : projB B X - Y ∈ B := B.sub_mem (projB_mem B X) hY
  have h0 : ((projB B X - Y)ᴴ * (projB B X - Y)).trace = 0 := by
    have h1 := h _ hD
    have h2 := projB_orth B X hD
    have e : (projB B X - Y)ᴴ * (projB B X - Y)
        = (X - Y)ᴴ * (projB B X - Y) - (X - projB B X)ᴴ * (projB B X - Y) := by
      rw [← Matrix.sub_mul, ← Matrix.conjTranspose_sub]
      congr 2; abel
    rw [e, Matrix.trace_sub, h1, h2, sub_zero]
  exact sub_eq_zero.1 (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h0)

theorem projB_of_mem {X : Matrix ι ι ℂ} (hX : X ∈ B) : projB B X = X :=
  projB_unique B X X hX fun c _ => by simp

/-- `P` commutes with left multiplication by `b ∈ B` (needs `B = B*`). -/
theorem projB_mul (hB : ∀ b ∈ B, bᴴ ∈ B) {b : Matrix ι ι ℂ} (hb : b ∈ B) (X : Matrix ι ι ℂ) :
    projB B (b * X) = b * projB B X := by
  refine projB_unique B _ _ (B.mul_mem hb (projB_mem B X)) fun c hc => ?_
  have := projB_orth B X (B.mul_mem (hB b hb) hc)
  rw [← Matrix.mul_sub, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  exact this

/-- The matrix `Q_{jk}` with `(Q_{jk})_{ab} = (P E_{bk})_{aj}`. -/
noncomputable def Qm (j k : ι) : Matrix ι ι ℂ :=
  Matrix.of fun a b => projB B (Matrix.single b k (1 : ℂ)) a j

theorem mul_single_eq (c : Matrix ι ι ℂ) (b k : ι) :
    c * Matrix.single b k (1 : ℂ) = ∑ d, c d b • Matrix.single d k (1 : ℂ) := by
  ext a k'
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, eq_comm]

theorem Qm_comm (hB : ∀ b ∈ B, bᴴ ∈ B) {c : Matrix ι ι ℂ} (hc : c ∈ B) (j k : ι) :
    c * Qm B j k = Qm B j k * c := by
  ext a b
  have h1 : (c * Qm B j k) a b = (c * projB B (Matrix.single b k (1 : ℂ))) a j := by
    simp [Qm, Matrix.mul_apply]
  rw [h1, ← projB_mul B hB hc, mul_single_eq, map_sum]
  simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Qm, Matrix.mul_apply,
    Matrix.of_apply]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

theorem projB_apply_eq (X : Matrix ι ι ℂ) (a j : ι) :
    projB B X a j = ∑ k, (Qm B j k * X) a k := by
  have hs : ∀ b k, Matrix.single b k (X b k) = X b k • Matrix.single b k (1 : ℂ) := by
    intro b k; rw [Matrix.smul_single]; simp
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [hs, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Qm, Matrix.of_apply]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- `P` commutes with left multiplication by every `T` in the bicommutant. -/
theorem projB_mul_of_bicomm (hB : ∀ b ∈ B, bᴴ ∈ B) (T : Matrix ι ι ℂ)
    (hT : ∀ Y : Matrix ι ι ℂ, (∀ b ∈ B, Y * b = b * Y) → Y * T = T * Y) (X : Matrix ι ι ℂ) :
    projB B (T * X) = T * projB B X := by
  ext a j
  rw [projB_apply_eq]
  have hQ : ∀ k, Qm B j k * T = T * Qm B j k := fun k =>
    hT _ fun b hb => (Qm_comm B hB hb j k).symm
  have e1 : ∀ k, (Qm B j k * (T * X)) a k = (T * (Qm B j k * X)) a k := fun k => by
    rw [← Matrix.mul_assoc, hQ k, Matrix.mul_assoc]
  simp only [e1, Matrix.mul_apply, projB_apply_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]

/-- **Double commutant theorem** for `*`-subalgebras of `M_n(ℂ)`: `B'' = B`. -/
theorem bicommutant_mem (hB : ∀ b ∈ B, bᴴ ∈ B) (T : Matrix ι ι ℂ)
    (hT : ∀ Y : Matrix ι ι ℂ, (∀ b ∈ B, Y * b = b * Y) → Y * T = T * Y) : T ∈ B := by
  have h := projB_mul_of_bicomm B hB T hT 1
  rw [Matrix.mul_one, projB_of_mem B B.one_mem, Matrix.mul_one] at h
  rw [← h]; exact projB_mem B T

end Bicommutant

end FormalResearch.FrameFree.Twirls
