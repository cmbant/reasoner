module

/-
Duality.lean

From states to maps: if every PPT state on ℂⁿ ⊗ ℂᵐ is separable, then every positive map Mₙ → Mₘ is
decomposable (`allDecomposable_of_allPPTSeparable`).

This is the bridge the read cap needs. Woronowicz's theorem is proved in the literature for states
(every PPT state on ℂ² ⊗ ℂ³ is separable), while `ReadCap.lean` needs it for maps. With this file,
`readcap_of_pptSeparable23` derives the Letter's read cap from the state form of Woronowicz's theorem.

  Part 1  Definitions: positive semidefinite (`IsPSD`), partial transpose (`pt`), PPT, separable, the
          Choi matrix, and the decomposable cone `{P + pt Q : P, Q ⪰ 0}`.
  Part 2  Algebra: a real quadratic form means a Hermitian matrix; positive maps preserve Hermiticity;
          the Choi matrix of a positive map is Hermitian and block positive; a Choi matrix in the cone
          gives Kraus families.
  Part 3  Topology: the cone is closed. Its slices of bounded trace are images of compact sets.
  Part 4  Separation (Hahn–Banach): a Choi matrix outside the cone would be detected by a PPT state on
          which it is negative, and a separable state cannot do that.

Check: compile ChoiDark.lean and ReadCap.lean to .olean files first (scripts/check_lean.py does this).
Needs a Mathlib v4.26.0 build that includes `Mathlib.Analysis.Matrix.Order`.
-/
public import MathLab.ChainTheory.ReadCap
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Matrix ComplexOrder

noncomputable section

namespace ChainDuality

open ChoiDark ChainReadCap

variable {n m : ℕ}

/-! ## Part 1. Definitions -/

/-- Indices of `ℂⁿ ⊗ ℂᵐ`. -/
abbrev Idx (n m : ℕ) := Fin n × Fin m

/-- Operators on `ℂⁿ ⊗ ℂᵐ`. -/
abbrev Mat (n m : ℕ) := Matrix (Idx n m) (Idx n m) ℂ

/-- Positive semidefinite: every `v† P v` is real and nonnegative. -/
def IsPSD {ι : Type*} [Fintype ι] (P : Matrix ι ι ℂ) : Prop :=
  ∀ v : ι → ℂ, 0 ≤ (star v ⬝ᵥ (P *ᵥ v)).re ∧ (star v ⬝ᵥ (P *ᵥ v)).im = 0

/-- The partial transpose on the second factor: `pt X ((a,k),(b,l)) = X ((a,l),(b,k))`. -/
def pt (X : Mat n m) : Mat n m := fun x y => X (x.1, y.2) (y.1, x.2)

/-- A PPT operator: it and its partial transpose are positive semidefinite. -/
def IsPPT (ρ : Mat n m) : Prop := IsPSD ρ ∧ IsPSD (pt ρ)

/-- The product vector `x ⊗ y`. -/
def prodVec (x : Fin n → ℂ) (y : Fin m → ℂ) : Idx n m → ℂ := fun z => x z.1 * y z.2

/-- Separable: a finite sum of rank-one product projectors `|x ⊗ y⟩⟨x ⊗ y|` (weights absorbed). -/
def IsSeparable (ρ : Mat n m) : Prop :=
  ∃ (r : ℕ) (x : Fin r → Fin n → ℂ) (y : Fin r → Fin m → ℂ),
    ρ = ∑ s, vecMulVec (prodVec (x s) (y s)) (star (prodVec (x s) (y s)))

/-- Every PPT operator on `ℂⁿ ⊗ ℂᵐ` is separable. -/
def AllPPTSeparable (n m : ℕ) : Prop := ∀ ρ : Mat n m, IsPPT ρ → IsSeparable ρ

/-- The Choi matrix `C((a,k),(b,l)) = Φ(E_ab)_kl`. -/
noncomputable def choi (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) : Mat n m :=
  fun x y => Φ (single x.1 y.1 1) x.2 y.2

/-- The decomposable cone `{P + pt Q : P, Q ⪰ 0}`. -/
def DecCone (n m : ℕ) : Set (Mat n m) := {X | ∃ P Q : Mat n m, IsPSD P ∧ IsPSD Q ∧ X = P + pt Q}

/-! ## Part 2. Algebra -/

section Quad

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem star_single_one (i : ι) : star (Pi.single i (1 : ℂ) : ι → ℂ) = Pi.single i 1 := by
  rw [← Pi.single_star, star_one]

theorem quad_single (M : Matrix ι ι ℂ) (i : ι) :
    star (Pi.single i 1 : ι → ℂ) ⬝ᵥ (M *ᵥ Pi.single i 1) = M i i := by
  rw [star_single_one, mulVec_single_one, single_dotProduct, col_apply, one_mul]

theorem quad_pair (M : Matrix ι ι ℂ) (i j : ι) (c : ℂ) :
    star ((Pi.single i 1 : ι → ℂ) + c • (Pi.single j 1 : ι → ℂ)) ⬝ᵥ
        (M *ᵥ ((Pi.single i 1 : ι → ℂ) + c • (Pi.single j 1 : ι → ℂ)))
      = M i i + c * M i j + star c * M j i + star c * c * M j j := by
  rw [star_add, star_smul, star_single_one, star_single_one, mulVec_add, mulVec_smul, mulVec_single_one,
    mulVec_single_one]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, single_dotProduct, col_apply,
    smul_eq_mul]
  ring

/-- **A matrix with real quadratic form is Hermitian** (complex polarization). -/
theorem hermitian_of_im_quad {M : Matrix ι ι ℂ} (h : ∀ v : ι → ℂ, (star v ⬝ᵥ (M *ᵥ v)).im = 0) :
    Mᴴ = M := by
  ext i j
  rw [conjTranspose_apply]
  have hi := h (Pi.single i 1 : ι → ℂ)
  have hj := h (Pi.single j 1 : ι → ℂ)
  have h1 := h ((Pi.single j 1 : ι → ℂ) + (1 : ℂ) • (Pi.single i 1 : ι → ℂ))
  have hI := h ((Pi.single j 1 : ι → ℂ) + Complex.I • (Pi.single i 1 : ι → ℂ))
  rw [quad_single] at hi hj
  rw [quad_pair] at h1 hI
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.star_def, map_one, Complex.conj_I,
    Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at h1 hI
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    nlinarith
  · simp only [Complex.star_def, Complex.conj_im]
    nlinarith

omit [DecidableEq ι] in
/-- A Hermitian matrix has real quadratic form. -/
theorem im_quad_of_hermitian {M : Matrix ι ι ℂ} (h : Mᴴ = M) (v : ι → ℂ) :
    (star v ⬝ᵥ (M *ᵥ v)).im = 0 := by
  have hM : ∀ i j, star (M i j) = M j i := fun i j => by
    have := congrFun (congrFun h j) i
    rwa [conjTranspose_apply] at this
  have hs : star (star v ⬝ᵥ (M *ᵥ v)) = star v ⬝ᵥ (M *ᵥ v) := by
    simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum, hM]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have := congrArg Complex.im hs
  rw [Complex.star_def, Complex.conj_im] at this
  linarith

theorem IsPSD.hermitian {P : Matrix ι ι ℂ} (h : IsPSD P) : Pᴴ = P :=
  hermitian_of_im_quad fun v => (h v).2

omit [DecidableEq ι] in
/-- Rank-one projectors `v v†` are positive semidefinite. -/
theorem isPSD_rank_one (v : ι → ℂ) : IsPSD (vecMulVec v (star v)) := by
  intro w
  have e : star w ⬝ᵥ (vecMulVec v (star v) *ᵥ w) = (star w ⬝ᵥ v) * star (star w ⬝ᵥ v) := by
    rw [show star (star w ⬝ᵥ v) = ∑ j, w j * star (v j) by
      simp only [dotProduct, star_sum, star_mul', Pi.star_apply, star_star]]
    rw [show star w ⬝ᵥ v = ∑ i, star (w i) * v i from rfl, Finset.sum_mul_sum]
    simp only [dotProduct, mulVec, vecMulVec_apply, Pi.star_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e, Complex.star_def, Complex.mul_conj]
  exact ⟨by simpa using Complex.normSq_nonneg _, by simp⟩

omit [DecidableEq ι] in
theorem isPSD_zero : IsPSD (0 : Matrix ι ι ℂ) := fun v => by simp

omit [DecidableEq ι] in
theorem IsPSD.add {P Q : Matrix ι ι ℂ} (hP : IsPSD P) (hQ : IsPSD Q) : IsPSD (P + Q) := fun v => by
  rw [add_mulVec, dotProduct_add, Complex.add_re, Complex.add_im]
  exact ⟨add_nonneg (hP v).1 (hQ v).1, by rw [(hP v).2, (hQ v).2, add_zero]⟩

omit [DecidableEq ι] in
theorem IsPSD.smul {P : Matrix ι ι ℂ} (hP : IsPSD P) {t : ℝ} (ht : 0 ≤ t) : IsPSD (t • P) := fun v => by
  rw [smul_mulVec, dotProduct_smul, Complex.smul_re, Complex.smul_im, smul_eq_mul, smul_eq_mul]
  exact ⟨mul_nonneg ht (hP v).1, by rw [(hP v).2, mul_zero]⟩

theorem IsPSD.diag {P : Matrix ι ι ℂ} (hP : IsPSD P) (i : ι) : 0 ≤ (P i i).re ∧ (P i i).im = 0 := by
  have := hP (Pi.single i 1 : ι → ℂ)
  rwa [quad_single] at this

end Quad

/-- Rank-one inputs `v v†` are `Bᴴ B` for the one-row `B = v†`. -/
theorem rank_one_gram {k : ℕ} (v : Fin k → ℂ) :
    (Matrix.of fun (_ : Fin 1) (i : Fin k) => star (v i))ᴴ * Matrix.of (fun (_ : Fin 1) i => star (v i))
      = vecMulVec v (star v) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, vecMulVec_apply]

/-- A positive map takes rank-one inputs to Hermitian matrices. -/
theorem positive_rank_one_herm {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ}
    (hΦ : IsPositive Φ) (v : Fin n → ℂ) : (Φ (vecMulVec v (star v)))ᴴ = Φ (vecMulVec v (star v)) := by
  apply hermitian_of_im_quad
  intro w
  have := (hΦ 1 (Matrix.of fun _ i => star (v i)) w).2
  rwa [rank_one_gram] at this

theorem single_diag_rank_one (a : Fin n) :
    (single a a (1 : ℂ)) = vecMulVec (Pi.single a 1 : Fin n → ℂ) (star (Pi.single a 1 : Fin n → ℂ)) := by
  rw [star_single_one, single_eq_single_vecMulVec_single]

theorem rank_one_expand (a b : Fin n) (c : ℂ) :
    vecMulVec ((Pi.single a 1 : Fin n → ℂ) + c • (Pi.single b 1 : Fin n → ℂ))
        (star ((Pi.single a 1 : Fin n → ℂ) + c • (Pi.single b 1 : Fin n → ℂ)))
      = single a a (1 : ℂ) + star c • single a b 1 + c • single b a 1 + (c * star c) • single b b 1 := by
  rw [star_add, star_smul, star_single_one, star_single_one, add_vecMulVec, vecMulVec_add, vecMulVec_add,
    smul_vecMulVec, smul_vecMulVec, vecMulVec_smul, vecMulVec_smul, ← single_eq_single_vecMulVec_single,
    ← single_eq_single_vecMulVec_single, ← single_eq_single_vecMulVec_single,
    ← single_eq_single_vecMulVec_single, smul_smul]
  abel

/-- **A positive map preserves Hermiticity on matrix units**: `Φ(E_ab)† = Φ(E_ba)`. -/
theorem positive_single_herm {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ}
    (hΦ : IsPositive Φ) (a b : Fin n) : (Φ (single a b 1))ᴴ = Φ (single b a 1) := by
  have hv := positive_rank_one_herm hΦ
  have hd : ∀ x : Fin n, (Φ (single x x 1))ᴴ = Φ (single x x 1) := fun x => by
    rw [single_diag_rank_one]; exact hv _
  set H1 : Matrix (Fin n) (Fin n) ℂ := single a b 1 + single b a 1 with hH1
  set H2 : Matrix (Fin n) (Fin n) ℂ := Complex.I • single a b 1 - Complex.I • single b a 1 with hH2
  have h1 : (Φ H1)ᴴ = Φ H1 := by
    have e : H1 = vecMulVec ((Pi.single a 1 : Fin n → ℂ) + (1 : ℂ) • (Pi.single b 1 : Fin n → ℂ))
        (star ((Pi.single a 1 : Fin n → ℂ) + (1 : ℂ) • (Pi.single b 1 : Fin n → ℂ))) - single a a 1
          - single b b 1 := by
      rw [rank_one_expand, hH1]
      simp only [star_one, one_smul, mul_one]
      abel
    rw [e, map_sub, map_sub, conjTranspose_sub, conjTranspose_sub, hv, hd, hd]
  have h2 : (Φ H2)ᴴ = Φ H2 := by
    have hc : (-Complex.I) * star (-Complex.I) = 1 := by
      simp
    have e : H2 = vecMulVec ((Pi.single a 1 : Fin n → ℂ) + (-Complex.I) • (Pi.single b 1 : Fin n → ℂ))
        (star ((Pi.single a 1 : Fin n → ℂ) + (-Complex.I) • (Pi.single b 1 : Fin n → ℂ))) - single a a 1
          - single b b 1 := by
      rw [rank_one_expand, hc, one_smul, hH2]
      simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg, neg_smul]
      abel
    rw [e, map_sub, map_sub, conjTranspose_sub, conjTranspose_sub, hv, hd, hd]
  have eab : single a b (1 : ℂ) = (1 / 2 : ℂ) • (H1 - Complex.I • H2) := by
    simp only [hH1, hH2, smul_sub, smul_add, smul_smul, Complex.I_mul_I]
    module
  have eba : single b a (1 : ℂ) = (1 / 2 : ℂ) • (H1 + Complex.I • H2) := by
    simp only [hH1, hH2, smul_sub, smul_add, smul_smul, Complex.I_mul_I]
    module
  clear_value H1 H2
  rw [eab, eba]
  simp only [map_smul, map_sub, map_add, conjTranspose_smul, conjTranspose_sub, h1, h2]
  congr 1
  · simp
  · rw [Complex.star_def, Complex.conj_I, neg_smul, sub_neg_eq_add]

/-- **Positive maps preserve Hermiticity**: `Φ(Xᴴ) = Φ(X)ᴴ`. -/
theorem positive_conjTranspose {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ}
    (hΦ : IsPositive Φ) (X : Matrix (Fin n) (Fin n) ℂ) : Φ Xᴴ = (Φ X)ᴴ := by
  ext k l
  rw [linear_expand Φ Xᴴ k l, conjTranspose_apply, linear_expand Φ X l k, star_sum]
  simp only [conjTranspose_apply, star_sum, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← positive_single_herm hΦ a b, conjTranspose_apply]

/-- **The Choi matrix of a positive map is Hermitian.** -/
theorem choi_hermitian {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ}
    (hΦ : IsPositive Φ) : (choi Φ)ᴴ = choi Φ := by
  ext x y
  simp only [conjTranspose_apply, choi]
  rw [← positive_single_herm hΦ x.1 y.1, conjTranspose_apply, star_star]

/-- On a product vector the Choi form is `y† Φ(x̄ x̄†) y`. -/
theorem choi_prodVec (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (x : Fin n → ℂ) (y : Fin m → ℂ) :
    star (prodVec x y) ⬝ᵥ (choi Φ *ᵥ prodVec x y)
      = star y ⬝ᵥ (Φ (vecMulVec (star x) x) *ᵥ y) := by
  simp only [dotProduct, mulVec, choi, prodVec, Pi.star_apply, star_mul', Fintype.sum_prod_type,
    linear_expand Φ (vecMulVec (star x) x), vecMulVec_apply, Finset.mul_sum, Finset.sum_mul]
  calc ∑ a, ∑ k, ∑ b, ∑ l, star (x a) * star (y k) * (Φ (single a b 1) k l * (x b * y l))
      = ∑ k, ∑ a, ∑ b, ∑ l, star (x a) * star (y k) * (Φ (single a b 1) k l * (x b * y l)) :=
        Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ l, ∑ b, star (x a) * star (y k) * (Φ (single a b 1) k l * (x b * y l)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, star (x a) * star (y k) * (Φ (single a b 1) k l * (x b * y l)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The Choi matrix of a positive map is block positive.** -/
theorem choi_block_positive {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ}
    (hΦ : IsPositive Φ) (x : Fin n → ℂ) (y : Fin m → ℂ) :
    0 ≤ (star (prodVec x y) ⬝ᵥ (choi Φ *ᵥ prodVec x y)).re := by
  rw [choi_prodVec]
  have := (hΦ 1 (Matrix.of fun _ i => star (star x i)) y).1
  rwa [rank_one_gram, star_star] at this

/-- A positive semidefinite matrix is a Gram matrix `Bᴴ B` (Mathlib, via the C*-algebra order). -/
theorem IsPSD.gram {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ} (h : IsPSD P) :
    ∃ B : Matrix ι ι ℂ, P = Bᴴ * B := by
  have hP : P.PosSemidef := Matrix.posSemidef_iff_dotProduct_mulVec.2
    ⟨h.hermitian, fun x => Complex.nonneg_iff.2 ⟨(h x).1, (h x).2.symm⟩⟩
  open scoped MatrixOrder in
  exact CStarAlgebra.nonneg_iff_eq_star_mul_self.1 (Matrix.nonneg_iff_posSemidef.2 hP)

/-- **A Choi matrix in the cone gives a decomposition.** -/
theorem decomposable_of_choi_mem {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ}
    (h : choi Φ ∈ DecCone n m) : IsDecomposable Φ := by
  obtain ⟨P, Q, hP, hQ, hC⟩ := h
  obtain ⟨B, rfl⟩ := hP.gram
  obtain ⟨D, rfl⟩ := hQ.gram
  set e := (Fintype.equivFin (Idx n m)).symm
  refine ⟨Fintype.card (Idx n m), Fintype.card (Idx n m),
    fun s => Matrix.of fun k a => star (B (e s) (a, k)),
    fun t => Matrix.of fun k b => D (e t) (b, k), fun X => ?_⟩
  ext k l
  rw [linear_expand Φ X k l]
  have hc : ∀ a b, Φ (single a b 1) k l = choi Φ (a, k) (b, l) := fun _ _ => rfl
  simp only [hc, hC, Matrix.add_apply, pt, Matrix.mul_apply, conjTranspose_apply, Matrix.sum_apply,
    Matrix.of_apply, transpose_apply, star_star, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul]
  rw [Equiv.sum_comp e (fun s => ∑ x, ∑ x_1, star (B s (x_1, k)) * X x_1 x * B s (x, l)),
    Equiv.sum_comp e (fun t => ∑ x, ∑ x_1, D t (x_1, k) * X x x_1 * star (D t (x, l)))]
  congr 1
  · calc ∑ a, ∑ b, ∑ s, X a b * (star (B s (a, k)) * B s (b, l))
        = ∑ a, ∑ s, ∑ b, X a b * (star (B s (a, k)) * B s (b, l)) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ s, ∑ a, ∑ b, X a b * (star (B s (a, k)) * B s (b, l)) := Finset.sum_comm
      _ = ∑ s, ∑ b, ∑ a, X a b * (star (B s (a, k)) * B s (b, l)) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring
  · calc ∑ a, ∑ b, ∑ t, X a b * (star (D t (a, l)) * D t (b, k))
        = ∑ a, ∑ t, ∑ b, X a b * (star (D t (a, l)) * D t (b, k)) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ t, ∑ a, ∑ b, X a b * (star (D t (a, l)) * D t (b, k)) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring

/-! ## Part 3. The cone is closed -/

/-- The real part of the trace. -/
def retr (X : Mat n m) : ℝ := (∑ x, X x x).re

theorem pt_add (X Y : Mat n m) : pt (X + Y) = pt X + pt Y := rfl

theorem pt_smul (t : ℝ) (X : Mat n m) : pt (t • X) = t • pt X := rfl

theorem pt_zero : pt (0 : Mat n m) = 0 := rfl

theorem retr_add (X Y : Mat n m) : retr (X + Y) = retr X + retr Y := by
  simp [retr, Finset.sum_add_distrib]

theorem retr_pt (X : Mat n m) : retr (pt X) = retr X := by
  simp [retr, pt]

theorem continuous_retr : Continuous (retr (n := n) (m := m)) :=
  Complex.continuous_re.comp (continuous_finsetSum _ fun x _ => continuous_id.matrix_elem x x)

theorem continuous_pt : Continuous (pt (n := n) (m := m)) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

theorem continuous_quad {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    Continuous fun P : Matrix ι ι ℂ => star v ⬝ᵥ (P *ᵥ v) := by
  simp only [dotProduct, mulVec]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    (continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem i j).mul continuous_const)

theorem isClosed_psd {ι : Type*} [Fintype ι] : IsClosed {P : Matrix ι ι ℂ | IsPSD P} := by
  have e : {P : Matrix ι ι ℂ | IsPSD P}
      = ⋂ v : ι → ℂ, {P | 0 ≤ (star v ⬝ᵥ (P *ᵥ v)).re} ∩ {P | (star v ⬝ᵥ (P *ᵥ v)).im = 0} := by
    ext P
    simp [IsPSD, Set.mem_iInter]
  rw [e]
  exact isClosed_iInter fun v =>
    (isClosed_le continuous_const (Complex.continuous_re.comp (continuous_quad v))).inter
      (isClosed_eq (Complex.continuous_im.comp (continuous_quad v)) continuous_const)

theorem IsPSD.retr_eq {P : Mat n m} : retr P = ∑ x, (P x x).re := by
  simp [retr, Complex.re_sum]

theorem IsPSD.retr_nonneg {P : Mat n m} (hP : IsPSD P) : 0 ≤ retr P := by
  rw [IsPSD.retr_eq]
  exact Finset.sum_nonneg fun x _ => (hP.diag x).1

theorem IsPSD.diag_le_retr {P : Mat n m} (hP : IsPSD P) (x : Idx n m) : (P x x).re ≤ retr P := by
  rw [IsPSD.retr_eq]
  exact Finset.single_le_sum (f := fun y => (P y y).re) (fun y _ => (hP.diag y).1) (Finset.mem_univ x)

/-- Entries of a positive semidefinite matrix are bounded by twice its trace. -/
theorem IsPSD.norm_entry_le {P : Mat n m} (hP : IsPSD P) (x y : Idx n m) : ‖P x y‖ ≤ 2 * retr P := by
  have hH := hP.hermitian
  have hyx : P y x = star (P x y) := by
    have := congrFun (congrFun hH y) x
    rw [conjTranspose_apply] at this
    exact this.symm
  have q : ∀ c : ℂ, 0 ≤ (P x x + c * P x y + star c * star (P x y) + star c * c * P y y).re := fun c => by
    have := (hP ((Pi.single x 1 : Idx n m → ℂ) + c • (Pi.single y 1 : Idx n m → ℂ))).1
    rwa [quad_pair, hyx] at this
  have h1 := q 1
  have h2 := q (-1)
  have h3 := q Complex.I
  have h4 := q (-Complex.I)
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, map_one, map_neg, Complex.conj_I, Complex.one_re, Complex.one_im, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im] at h1 h2 h3 h4
  have dx := hP.diag_le_retr x
  have dy := hP.diag_le_retr y
  have ix := (hP.diag x).2
  have iy := (hP.diag y).2
  have hre : |(P x y).re| ≤ retr P := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have him : |(P x y).im| ≤ retr P := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  linarith [Complex.norm_le_abs_re_add_abs_im (P x y)]

/-- Pairs `(P, Q)` of positive semidefinite matrices with `tr P + tr Q ≤ R`. -/
def slice (R : ℝ) : Set (Mat n m × Mat n m) :=
  {pq | IsPSD pq.1 ∧ IsPSD pq.2 ∧ retr pq.1 + retr pq.2 ≤ R}

theorem isCompact_slice (R : ℝ) : IsCompact (slice (n := n) (m := m) R) := by
  let box : Set (Mat n m) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) (2 * R)
  have hbox : IsCompact box := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine (hbox.prod hbox).of_isClosed_subset ?_ ?_
  · have hc : Continuous fun pq : Mat n m × Mat n m => retr pq.1 + retr pq.2 :=
      (continuous_retr.comp continuous_fst).add (continuous_retr.comp continuous_snd)
    exact (isClosed_psd.preimage continuous_fst).inter
      ((isClosed_psd.preimage continuous_snd).inter (isClosed_le hc continuous_const))
  · rintro ⟨P, Q⟩ ⟨hP, hQ, hR⟩
    have hP0 := hP.retr_nonneg
    have hQ0 := hQ.retr_nonneg
    refine ⟨fun x _ y _ => ?_, fun x _ y _ => ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      linarith [hP.norm_entry_le x y]
    · rw [Metric.mem_closedBall, dist_zero_right]
      linarith [hQ.norm_entry_le x y]

theorem decCone_inter_eq (R : ℝ) :
    DecCone n m ∩ {X | retr X ≤ R} = (fun pq : Mat n m × Mat n m => pq.1 + pt pq.2) '' slice R := by
  ext X
  constructor
  · rintro ⟨⟨P, Q, hP, hQ, rfl⟩, hR⟩
    refine ⟨(P, Q), ⟨hP, hQ, ?_⟩, rfl⟩
    simpa [Set.mem_ofPred_eq, retr_add, retr_pt] using hR
  · rintro ⟨⟨P, Q⟩, ⟨hP, hQ, hR⟩, rfl⟩
    refine ⟨⟨P, Q, hP, hQ, rfl⟩, ?_⟩
    simpa [Set.mem_ofPred_eq, retr_add, retr_pt] using hR

/-- **The decomposable cone is closed.** -/
theorem isClosed_decCone : IsClosed (DecCone n m) := by
  refine isClosed_of_closure_subset fun X hX => ?_
  have hU : IsOpen {Y : Mat n m | retr Y < retr X + 1} := isOpen_lt continuous_retr continuous_const
  have hXU : X ∈ {Y : Mat n m | retr Y < retr X + 1} := by simp
  have h1 := hU.inter_closure ⟨hXU, hX⟩
  have hK : IsClosed (DecCone n m ∩ {Y | retr Y ≤ retr X + 1}) := by
    rw [decCone_inter_eq]
    exact ((isCompact_slice _).image (continuous_fst.add (continuous_pt.comp continuous_snd))).isClosed
  have hsub : {Y : Mat n m | retr Y < retr X + 1} ∩ DecCone n m ⊆ DecCone n m ∩ {Y | retr Y ≤ retr X + 1} :=
    fun Y hY => ⟨hY.2, show retr Y ≤ retr X + 1 from le_of_lt hY.1⟩
  exact (closure_minimal hsub hK h1).1

theorem convex_decCone : Convex ℝ (DecCone n m) := by
  rintro X ⟨P₁, Q₁, hP₁, hQ₁, rfl⟩ Y ⟨P₂, Q₂, hP₂, hQ₂, rfl⟩ a b ha hb _
  refine ⟨a • P₁ + b • P₂, a • Q₁ + b • Q₂, (hP₁.smul ha).add (hP₂.smul hb), (hQ₁.smul ha).add (hQ₂.smul hb), ?_⟩
  rw [pt_add, pt_smul, pt_smul, smul_add, smul_add]
  abel

theorem zero_mem_decCone : (0 : Mat n m) ∈ DecCone n m :=
  ⟨0, 0, isPSD_zero, isPSD_zero, by rw [pt_zero, add_zero]⟩

theorem smul_mem_decCone {X : Mat n m} (hX : X ∈ DecCone n m) {t : ℝ} (ht : 0 ≤ t) : t • X ∈ DecCone n m := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := hX
  exact ⟨t • P, t • Q, hP.smul ht, hQ.smul ht, by rw [smul_add, pt_smul]⟩

/-! ## Part 4. Separation -/

/-- The trace pairing `tr(ρ X)`. -/
def pair (ρ X : Mat n m) : ℂ := ∑ y, ∑ x, ρ y x * X x y

theorem pair_rank_one (ρ : Mat n m) (v : Idx n m → ℂ) :
    pair ρ (vecMulVec v (star v)) = star v ⬝ᵥ (ρ *ᵥ v) := by
  simp only [pair, dotProduct, mulVec, vecMulVec_apply, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem pair_rank_one_left (z : Idx n m → ℂ) (X : Mat n m) :
    pair (vecMulVec z (star z)) X = star z ⬝ᵥ (X *ᵥ z) := by
  simp only [pair, dotProduct, mulVec, vecMulVec_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem pair_add (A B X : Mat n m) : pair (A + B) X = pair A X + pair B X := by
  simp only [pair, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem pair_sum_left {ι : Type*} (s : Finset ι) (ρ : ι → Mat n m) (X : Mat n m) :
    pair (∑ i ∈ s, ρ i) X = ∑ i ∈ s, pair (ρ i) X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pair]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_add, ih]

theorem pair_pt (ρ X : Mat n m) : pair ρ (pt X) = pair (pt ρ) X := by
  simp only [pair, pt, Fintype.sum_prod_type]
  calc ∑ b, ∑ l, ∑ a, ∑ k, ρ (b, l) (a, k) * X (a, l) (b, k)
      = ∑ b, ∑ a, ∑ l, ∑ k, ρ (b, l) (a, k) * X (a, l) (b, k) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ k, ∑ l, ρ (b, l) (a, k) * X (a, l) (b, k) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b, ∑ k, ∑ a, ∑ l, ρ (b, l) (a, k) * X (a, l) (b, k) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem pt_hermitian {ρ : Mat n m} (h : ρᴴ = ρ) : (pt ρ)ᴴ = pt ρ := by
  ext x y
  have := congrFun (congrFun h (x.1, y.2)) (y.1, x.2)
  simp only [conjTranspose_apply] at this ⊢
  simpa [pt] using this

/-- On Hermitian matrices, the real part of the pairing sees only the Hermitian part of `ρ`. -/
theorem re_pair_conjTranspose (ρ X : Mat n m) (hX : Xᴴ = X) : (pair ρᴴ X).re = (pair ρ X).re := by
  have hXs : ∀ x y, star (X x y) = X y x := fun x y => by
    have := congrFun (congrFun hX y) x
    rwa [conjTranspose_apply] at this
  have e : pair ρᴴ X = star (pair ρ X) := by
    simp only [pair, conjTranspose_apply, star_sum, star_mul', hXs]
    rw [Finset.sum_comm]
  rw [e, Complex.star_def, Complex.conj_re]

/-- A continuous `ℂ`-linear functional on matrices is a trace pairing. -/
theorem dual_eq_pair (f : StrongDual ℂ (Mat n m)) (X : Mat n m) :
    f X = pair (fun y x => f (single x y 1)) X := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, pair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [show ∀ a b : Idx n m, single a b (X a b) = X a b • single a b (1 : ℂ) from fun a b => by
      rw [Matrix.smul_single, smul_eq_mul, mul_one],
    map_smul, smul_eq_mul, mul_comm]

/-- On Hermitian matrices, the real part of a continuous functional is `re tr(W ·)` for a Hermitian
`W`. -/
theorem exists_hermitian_pair (f : StrongDual ℂ (Mat n m)) :
    ∃ W : Mat n m, Wᴴ = W ∧ ∀ X : Mat n m, Xᴴ = X → (pair W X).re = (f X).re := by
  set ρ₀ : Mat n m := fun y x => f (single x y 1) with hρ₀
  refine ⟨(1 / 2 : ℂ) • (ρ₀ + ρ₀ᴴ), ?_, fun X hX => ?_⟩
  · rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  · have hsplit : pair ((1 / 2 : ℂ) • (ρ₀ + ρ₀ᴴ)) X = (1 / 2 : ℂ) * (pair ρ₀ X + pair ρ₀ᴴ X) := by
      simp only [pair, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hsplit, dual_eq_pair f X, ← hρ₀]
    have hr := re_pair_conjTranspose ρ₀ X hX
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im]
    norm_num
    linarith

instance : LocallyConvexSpace ℝ (Mat n m) :=
  (inferInstance : LocallyConvexSpace ℝ (Idx n m → Idx n m → ℂ))

/-- **A separable state is nonnegative on the Choi matrix of every positive map.** -/
theorem pair_choi_nonneg_of_separable {ρ : Mat n m} (h : IsSeparable ρ)
    {Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hΦ : IsPositive Φ) :
    0 ≤ (pair ρ (choi Φ)).re := by
  obtain ⟨r, x, y, rfl⟩ := h
  rw [pair_sum_left, Complex.re_sum]
  refine Finset.sum_nonneg fun s _ => ?_
  rw [pair_rank_one_left]
  exact choi_block_positive hΦ (x s) (y s)

/-- **States to maps, pairing form**: if every PPT state pairs nonnegatively with the Choi matrix of
every positive map, every positive map is decomposable. -/
theorem allDecomposable_of_pptPairing
    (h : ∀ ρ : Mat n m, IsPPT ρ → ∀ Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ,
      IsPositive Φ → 0 ≤ (pair ρ (choi Φ)).re) : AllDecomposable n m := by
  intro Φ hΦ
  apply decomposable_of_choi_mem
  by_contra hC
  obtain ⟨f, u, hfC, hfD⟩ :=
    RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ) convex_decCone isClosed_decCone hC
  simp only [RCLike.re_to_complex] at hfC hfD
  have hu : u < 0 := by simpa using hfD 0 zero_mem_decCone
  -- the separating functional is nonnegative on the cone
  have hpos : ∀ b ∈ DecCone n m, 0 ≤ (f b).re := by
    intro b hb
    by_contra hneg
    push Not at hneg
    have ht : 0 < u / (f b).re := div_pos_of_neg_of_neg hu hneg
    have := hfD ((u / (f b).re) • b) (smul_mem_decCone hb ht.le)
    rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  -- the functional as a Hermitian matrix
  obtain ⟨ρ, hρH, hre⟩ := exists_hermitian_pair f
  -- ρ is PPT
  have hρPPT : IsPPT ρ := by
    refine ⟨fun v => ⟨?_, im_quad_of_hermitian hρH v⟩, fun v => ⟨?_, im_quad_of_hermitian (pt_hermitian hρH) v⟩⟩
    · rw [← pair_rank_one, hre _ (isPSD_rank_one v).hermitian]
      exact hpos _ ⟨vecMulVec v (star v), 0, isPSD_rank_one v, isPSD_zero, by rw [pt_zero, add_zero]⟩
    · rw [← pair_rank_one, ← pair_pt, hre _ (pt_hermitian (isPSD_rank_one v).hermitian)]
      exact hpos _ ⟨0, vecMulVec v (star v), isPSD_zero, isPSD_rank_one v, by rw [zero_add]⟩
  -- the hypothesis: PPT states are nonnegative on Choi matrices of positive maps
  have hnn : 0 ≤ (f (choi Φ)).re := by
    rw [← hre _ (choi_hermitian hΦ)]
    exact h ρ hρPPT Φ hΦ
  linarith

/-- **States to maps**: if every PPT state on ℂⁿ ⊗ ℂᵐ is separable, every positive map Mₙ → Mₘ is
decomposable. -/
theorem allDecomposable_of_allPPTSeparable (h : AllPPTSeparable n m) : AllDecomposable n m :=
  allDecomposable_of_pptPairing fun ρ hρ _ hΦ => pair_choi_nonneg_of_separable (h ρ hρ) hΦ

/-- **The read cap from the state form of Woronowicz's theorem**: if every PPT operator on `ℂ² ⊗ ℂ³` is
separable, the Letter's read cap holds for its own readability. -/
theorem readcap_of_pptSeparable23 (h : AllPPTSeparable 2 3) : ReadCap Readable :=
  readcap_of_woronowicz (allDecomposable_of_allPPTSeparable h)

end ChainDuality

end

end -- public section

#print axioms ChainDuality.hermitian_of_im_quad
#print axioms ChainDuality.positive_conjTranspose
#print axioms ChainDuality.decomposable_of_choi_mem
#print axioms ChainDuality.isClosed_decCone
#print axioms ChainDuality.allDecomposable_of_allPPTSeparable
#print axioms ChainDuality.readcap_of_pptSeparable23
