module

public import ThreeCopyQutritWerner.Imports

@[expose] public section


/-!
# Rank factorisation and the trace bound for low-rank complex matrices

General, reusable facts about complex matrices over finite index types:

* `rank_le_iff_exists_mul`: `C.rank ≤ r` iff `C = X * B` with an `r`-indexed middle type.
* `normSq_trace_le_mul_of_rank_le`: `|Tr C|² ≤ r * ‖C‖_F²` when `C.rank ≤ r`.
* `normSq_trace_le_two_mul_of_rank_le_two`: the case `r = 2`.
-/

namespace ThreeCopyQutritWerner

open Matrix

/-- Rank factorisation through the dimension of the range of `C.mulVecLin`. -/
theorem exists_mul_fin_finrank {m n : Type*} [Fintype m] [Fintype n] (C : Matrix m n ℂ) :
    ∃ (X : Matrix m (Fin (Module.finrank ℂ (LinearMap.range C.mulVecLin))) ℂ)
      (B : Matrix (Fin (Module.finrank ℂ (LinearMap.range C.mulVecLin))) n ℂ), C = X * B := by
  classical
  let b := Module.finBasis ℂ (LinearMap.range C.mulVecLin)
  let φ : ∀ i : m, (LinearMap.range C.mulVecLin) →ₗ[ℂ] ℂ := fun i =>
    (LinearMap.proj i : (m → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (LinearMap.range C.mulVecLin).subtype
  let w : n → LinearMap.range C.mulVecLin := fun j =>
    ⟨C.mulVecLin (Pi.single j 1), LinearMap.mem_range_self C.mulVecLin (Pi.single j 1)⟩
  refine ⟨Matrix.of fun i k => φ i (b k), Matrix.of fun k j => b.repr (w j) k, ?_⟩
  ext i j
  have h := congrArg (φ i) (b.sum_repr (w j))
  rw [map_sum] at h
  simp only [map_smul, smul_eq_mul] at h
  have h4 : φ i (w j) = C i j := by
    show (C *ᵥ Pi.single j 1) i = C i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← h4, ← h, Matrix.mul_apply]
  first
    | exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    | simp [mul_comm]

/-- A complex matrix has rank at most `r` iff it factors through `Fin r`. -/
theorem rank_le_iff_exists_mul {m n : Type*} [Fintype m] [Fintype n] (C : Matrix m n ℂ) (r : ℕ) :
    C.rank ≤ r ↔ ∃ (X : Matrix m (Fin r) ℂ) (B : Matrix (Fin r) n ℂ), C = X * B := by
  constructor
  · intro h
    have h' : Module.finrank ℂ (LinearMap.range C.mulVecLin) ≤ r := h
    obtain ⟨X', B', hXB⟩ := exists_mul_fin_finrank C
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h'
    subst hk
    refine ⟨(Matrix.fromCols X' (0 : Matrix m (Fin k) ℂ)).submatrix id finSumFinEquiv.symm,
      (Matrix.fromRows B' (0 : Matrix (Fin k) n ℂ)).submatrix finSumFinEquiv.symm id, ?_⟩
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero,
      Matrix.submatrix_id_id]
    exact hXB
  · rintro ⟨X, B, rfl⟩
    exact (Matrix.rank_mul_le_left X B).trans
      ((Matrix.rank_le_card_width X).trans_eq (Fintype.card_fin r))

/-- Cauchy–Schwarz for finite complex sums, in `Complex.normSq` form. -/
theorem normSq_sum_mul_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    Complex.normSq (∑ x ∈ s, f x * g x) ≤
      (∑ x ∈ s, Complex.normSq (f x)) * ∑ x ∈ s, Complex.normSq (g x) := by
  have h1 : ‖∑ x ∈ s, f x * g x‖ ≤ ∑ x ∈ s, ‖f x‖ * ‖g x‖ :=
    (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun x _ => norm_mul _ _)
  have h2 : (∑ x ∈ s, ‖f x‖ * ‖g x‖) ^ 2 ≤ (∑ x ∈ s, ‖f x‖ ^ 2) * ∑ x ∈ s, ‖g x‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun x => ‖f x‖) (fun x => ‖g x‖)
  have h3 : ‖∑ x ∈ s, f x * g x‖ ^ 2 ≤ (∑ x ∈ s, ‖f x‖ * ‖g x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  simp only [Complex.normSq_eq_norm_sq]
  exact h3.trans h2

/-- The squared Frobenius norm as the trace of `Aᴴ * A`. -/
theorem trace_conjTranspose_mul_self_eq {a b : Type*} [Fintype a] [Fintype b]
    (A : Matrix a b ℂ) :
    (Aᴴ * A).trace = ((∑ i, ∑ j, Complex.normSq (A i j) : ℝ) : ℂ) := by
  have key : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := fun z => by
    rw [mul_comm]
    exact Complex.mul_conj z
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum, key]
  exact Finset.sum_comm

/-- The trace bound under an explicit factorisation `U * B` with orthonormal columns of `U`. -/
theorem normSq_trace_mul_le_of_conjTranspose_mul_self_eq_one {n k : Type*} [Fintype n]
    [Fintype k] [DecidableEq k] (U : Matrix n k ℂ) (B : Matrix k n ℂ) (hU : Uᴴ * U = 1) :
    Complex.normSq (U * B).trace ≤
      (Fintype.card k : ℝ) * ∑ i, ∑ j, Complex.normSq ((U * B) i j) := by
  have hUF : (∑ i, ∑ l, Complex.normSq (U i l)) = (Fintype.card k : ℝ) := by
    apply Complex.ofReal_injective
    rw [← trace_conjTranspose_mul_self_eq, hU, Matrix.trace_one]
    simp
  have hBF : (∑ l, ∑ i, Complex.normSq (B l i)) = ∑ i, ∑ j, Complex.normSq ((U * B) i j) := by
    apply Complex.ofReal_injective
    rw [← trace_conjTranspose_mul_self_eq B, ← trace_conjTranspose_mul_self_eq (U * B),
      Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U B, hU, Matrix.one_mul]
  have htr : (U * B).trace = ∑ p : n × k, U p.1 p.2 * B p.2 p.1 := by
    rw [Fintype.sum_prod_type]
    simp [Matrix.trace, Matrix.mul_apply]
  have hcs : Complex.normSq (∑ p : n × k, U p.1 p.2 * B p.2 p.1) ≤
      (∑ p : n × k, Complex.normSq (U p.1 p.2)) * ∑ p : n × k, Complex.normSq (B p.2 p.1) :=
    normSq_sum_mul_le Finset.univ (fun p : n × k => U p.1 p.2) (fun p : n × k => B p.2 p.1)
  have e1 : (∑ p : n × k, Complex.normSq (U p.1 p.2)) = (Fintype.card k : ℝ) := by
    rw [Fintype.sum_prod_type]
    exact hUF
  have e2 : (∑ p : n × k, Complex.normSq (B p.2 p.1)) =
      ∑ i, ∑ j, Complex.normSq ((U * B) i j) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact hBF
  rw [← htr, e1, e2] at hcs
  exact hcs

/-- Orthonormal rank factorisation: `C = U * B` with `Uᴴ * U = 1` and `C.rank` columns. -/
theorem exists_orthonormal_mul {m n : Type*} [Fintype m] [Fintype n] (C : Matrix m n ℂ) :
    ∃ (d : ℕ) (U : Matrix m (Fin d) ℂ) (B : Matrix (Fin d) n ℂ),
      d = C.rank ∧ Uᴴ * U = 1 ∧ C = U * B := by
  classical
  let e : (m → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ m := (WithLp.linearEquiv 2 ℂ (m → ℂ)).symm
  let W : Submodule ℂ (EuclideanSpace ℂ m) := (LinearMap.range C.mulVecLin).map e.toLinearMap
  have hW : Module.finrank ℂ W = C.rank := LinearEquiv.finrank_map_eq e _
  let b := stdOrthonormalBasis ℂ W
  let w : n → W := fun j =>
    ⟨e (C.mulVecLin (Pi.single j 1)),
      Submodule.mem_map_of_mem (LinearMap.mem_range_self C.mulVecLin (Pi.single j 1))⟩
  let φ : ∀ i : m, W →ₗ[ℂ] ℂ := fun i =>
    (LinearMap.proj i : (m → ℂ) →ₗ[ℂ] ℂ) ∘ₗ e.symm.toLinearMap ∘ₗ W.subtype
  refine ⟨Module.finrank ℂ W,
    Matrix.of fun i k => WithLp.ofLp ((b k : W) : EuclideanSpace ℂ m) i,
    Matrix.of fun k j => b.repr (w j) k, hW, ?_, ?_⟩
  · ext k l
    have h := orthonormal_iff_ite.mp b.orthonormal k l
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [Matrix.one_apply]
    refine Eq.trans ?_ h
    rw [Matrix.mul_apply]
    first
      | exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      | simp [dotProduct, Matrix.conjTranspose_apply, mul_comm]
  · ext i j
    have h := congrArg (φ i) (b.sum_repr (w j))
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    have h4 : φ i (w j) = C i j := by
      show (C *ᵥ Pi.single j 1) i = C i j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← h4, ← h, Matrix.mul_apply]
    first
      | exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      | simp [mul_comm]

/-- For a square complex matrix of rank at most `r`, `|Tr C|² ≤ r * ‖C‖_F²`. -/
theorem normSq_trace_le_mul_of_rank_le {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (r : ℕ) (h : C.rank ≤ r) :
    Complex.normSq C.trace ≤ (r : ℝ) * ∑ i, ∑ j, Complex.normSq (C i j) := by
  obtain ⟨d, U, B, hd, hU, hC⟩ := exists_orthonormal_mul C
  have h1 := normSq_trace_mul_le_of_conjTranspose_mul_self_eq_one U B hU
  rw [← hC, Fintype.card_fin] at h1
  have hdr : (d : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast hd.trans_le h
  exact h1.trans (mul_le_mul_of_nonneg_right hdr
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _))

/-- For a square complex matrix of rank at most two, `|Tr C|² ≤ 2 * ‖C‖_F²`. -/
theorem normSq_trace_le_two_mul_of_rank_le_two {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (h : C.rank ≤ 2) :
    Complex.normSq C.trace ≤ 2 * ∑ i, ∑ j, Complex.normSq (C i j) := by
  have h2 := normSq_trace_le_mul_of_rank_le C 2 h
  exact_mod_cast h2

end ThreeCopyQutritWerner
