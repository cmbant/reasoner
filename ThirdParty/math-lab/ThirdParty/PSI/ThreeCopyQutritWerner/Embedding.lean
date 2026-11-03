module

public import ThreeCopyQutritWerner.InteriorConverse

@[expose] public section


/-!
# Isometric local embeddings and site permutations

Manuscript Theorem 2.1, unequal dimensions, the case `d_i ≤ 3` (by embedding every site
isometrically into `ℂ³`), and manuscript eq. (21) for an arbitrary active site.

* `embed₃ J₁ J₂ J₃ C = (J₁ ⊗ J₂ ⊗ J₃) C (J₁ ⊗ J₂ ⊗ J₃)†`.  For isometries `Jᵢ† Jᵢ = 1` it
  preserves `N`, `A`, `B`, `T₀`, hence every `q_α` (`energy_embed₃`), and it does not increase
  the rank (`rank_embed₃_le`).
* `endpointEnergy_nonneg_of_card_le_three`: a REDUCTION.  The qutrit endpoint inequality
  (open claim T2.1a, kept as the hypothesis `hq`) implies the endpoint inequality for all local
  dimensions at most three.
* `energy_submatrix_siteEquiv₂`, `energy_submatrix_siteEquiv₃`: the energy is invariant under
  exchanging the sites.
* `familyI_endpoint_zero_general` and its site-2 and site-3 versions: eq. (21) for every
  two-plane `E`, unit vectors `χ`, `η`, and every active site.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- `‖M‖_F² = Tr (M† M)`. -/
theorem ofReal_frobSq_eq_trace {n m : Type*} [Fintype n] [Fintype m] (M : Matrix n m ℂ) :
    ((frobSq M : ℝ) : ℂ) = (Mᴴ * M).trace :=
  (trace_conjTranspose_mul_self_eq M).symm

section Isometry

variable {m m' : Type*} [Fintype m] [Fintype m'] [DecidableEq m]

/-- The trace is invariant under conjugation by an isometry. -/
theorem trace_conj_isometry (K : Matrix m' m ℂ) (hK : Kᴴ * K = 1) (Y : Matrix m m ℂ) :
    (K * Y * Kᴴ).trace = Y.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hK, Matrix.one_mul]

theorem conjTranspose_conj_mul_conj (K : Matrix m' m ℂ) (hK : Kᴴ * K = 1)
    (X : Matrix m m ℂ) : (K * X * Kᴴ)ᴴ * (K * X * Kᴴ) = K * (Xᴴ * X) * Kᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Kᴴ K, hK, Matrix.one_mul]

/-- The Frobenius norm is invariant under conjugation by an isometry. -/
theorem frobSq_conj_isometry (K : Matrix m' m ℂ) (hK : Kᴴ * K = 1) (X : Matrix m m ℂ) :
    frobSq (K * X * Kᴴ) = frobSq X := by
  have h : ((frobSq (K * X * Kᴴ) : ℝ) : ℂ) = ((frobSq X : ℝ) : ℂ) := by
    rw [ofReal_frobSq_eq_trace, ofReal_frobSq_eq_trace, conjTranspose_conj_mul_conj K hK,
      trace_conj_isometry K hK]
  exact_mod_cast h

/-- `∑ᵢ (U G U†)ᵢᵢ = Tr G` for an isometry `U`, written out. -/
theorem sum_isometry_collapse (U : Matrix m' m ℂ) (hU : Uᴴ * U = 1) (g : m → m → ℂ) :
    ∑ i, ∑ q, ∑ p, U i p * g p q * star (U i q) = ∑ j, g j j := by
  have h := trace_conj_isometry U hU (Matrix.of g)
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Finset.sum_mul] at h
  exact h

end Isometry

section Kron

theorem kron_apply {l n p q : Type*} (U : Matrix l n ℂ) (V : Matrix p q ℂ) (x : l × p)
    (y : n × q) : (U ⊗ₖ V) x y = U x.1 y.1 * V x.2 y.2 := rfl

theorem kron_isometry {l n p q : Type*} [Fintype l] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (U : Matrix l n ℂ) (V : Matrix p q ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) : (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV,
    Matrix.one_kronecker_one]

variable {L R L' R' : Type*} [Fintype L] [Fintype R] [Fintype L'] [Fintype R']

/-- Partial trace over the first factor commutes with a local isometry on it. -/
theorem ptraceL_conj [DecidableEq L] (U : Matrix L' L ℂ) (V : Matrix R' R ℂ)
    (hU : Uᴴ * U = 1) (X : Matrix (L × R) (L × R) ℂ) :
    ptraceL ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᴴ) = V * ptraceL X * Vᴴ := by
  ext r s
  calc ptraceL ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᴴ) r s
      = ∑ i, ∑ q₁, ∑ q₂, ∑ p₁, ∑ p₂,
          U i p₁ * V r p₂ * X (p₁, p₂) (q₁, q₂) * star (U i q₁ * V s q₂) := by
        simp only [ptraceL, Matrix.mul_apply, Matrix.conjTranspose_apply, kron_apply,
          Finset.sum_mul, Fintype.sum_prod_type]
    _ = ∑ i, ∑ q₁, ∑ p₁, ∑ q₂, ∑ p₂,
          U i p₁ * V r p₂ * X (p₁, p₂) (q₁, q₂) * star (U i q₁ * V s q₂) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q₁ _ => Finset.sum_comm
    _ = ∑ i, ∑ q₁, ∑ p₁, U i p₁ *
          (∑ q₂, ∑ p₂, V r p₂ * X (p₁, p₂) (q₁, q₂) * star (V s q₂)) * star (U i q₁) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q₁ _ =>
          Finset.sum_congr rfl fun p₁ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun q₂ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p₂ _ => ?_
        rw [star_mul]
        ring
    _ = ∑ j, ∑ q₂, ∑ p₂, V r p₂ * X (j, p₂) (j, q₂) * star (V s q₂) :=
        sum_isometry_collapse U hU _
    _ = ∑ q₂, ∑ j, ∑ p₂, V r p₂ * X (j, p₂) (j, q₂) * star (V s q₂) := Finset.sum_comm
    _ = ∑ q₂, ∑ p₂, ∑ j, V r p₂ * X (j, p₂) (j, q₂) * star (V s q₂) :=
        Finset.sum_congr rfl fun q₂ _ => Finset.sum_comm
    _ = (V * ptraceL X * Vᴴ) r s := by
        simp only [ptraceL, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum,
          Finset.sum_mul]

/-- Partial trace over the second factor commutes with a local isometry on it. -/
theorem ptraceR_conj [DecidableEq R] (U : Matrix L' L ℂ) (V : Matrix R' R ℂ)
    (hV : Vᴴ * V = 1) (X : Matrix (L × R) (L × R) ℂ) :
    ptraceR ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᴴ) = U * ptraceR X * Uᴴ := by
  ext r s
  calc ptraceR ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᴴ) r s
      = ∑ k, ∑ q₁, ∑ q₂, ∑ p₁, ∑ p₂,
          U r p₁ * V k p₂ * X (p₁, p₂) (q₁, q₂) * star (U s q₁ * V k q₂) := by
        simp only [ptraceR, Matrix.mul_apply, Matrix.conjTranspose_apply, kron_apply,
          Finset.sum_mul, Fintype.sum_prod_type]
    _ = ∑ k, ∑ q₂, ∑ q₁, ∑ p₁, ∑ p₂,
          U r p₁ * V k p₂ * X (p₁, p₂) (q₁, q₂) * star (U s q₁ * V k q₂) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ q₂, ∑ q₁, ∑ p₂, ∑ p₁,
          U r p₁ * V k p₂ * X (p₁, p₂) (q₁, q₂) * star (U s q₁ * V k q₂) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q₂ _ =>
          Finset.sum_congr rfl fun q₁ _ => Finset.sum_comm
    _ = ∑ k, ∑ q₂, ∑ p₂, ∑ q₁, ∑ p₁,
          U r p₁ * V k p₂ * X (p₁, p₂) (q₁, q₂) * star (U s q₁ * V k q₂) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q₂ _ => Finset.sum_comm
    _ = ∑ k, ∑ q₂, ∑ p₂, V k p₂ *
          (∑ q₁, ∑ p₁, U r p₁ * X (p₁, p₂) (q₁, q₂) * star (U s q₁)) * star (V k q₂) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q₂ _ =>
          Finset.sum_congr rfl fun p₂ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun q₁ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p₁ _ => ?_
        rw [star_mul]
        ring
    _ = ∑ j, ∑ q₁, ∑ p₁, U r p₁ * X (p₁, j) (q₁, j) * star (U s q₁) :=
        sum_isometry_collapse V hV _
    _ = ∑ q₁, ∑ j, ∑ p₁, U r p₁ * X (p₁, j) (q₁, j) * star (U s q₁) := Finset.sum_comm
    _ = ∑ q₁, ∑ p₁, ∑ j, U r p₁ * X (p₁, j) (q₁, j) * star (U s q₁) :=
        Finset.sum_congr rfl fun q₁ _ => Finset.sum_comm
    _ = (U * ptraceR X * Uᴴ) r s := by
        simp only [ptraceR, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum,
          Finset.sum_mul]

end Kron

section SiteIndex

theorem siteEquiv₂_apply' {α β γ : Type*} (x : β × α × γ) :
    (siteEquiv₂ x : α × β × γ) = (x.2.1, x.1, x.2.2) := rfl

theorem siteEquiv₃_apply' {α β γ : Type*} (x : γ × α × β) :
    (siteEquiv₃ x : α × β × γ) = (x.2.1, x.2.2, x.1) := rfl

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

theorem ptrace₂_eq_ptrace₁_submatrix (Y : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₂ Y = ptrace₁ (Y.submatrix siteEquiv₂ siteEquiv₂) := rfl

theorem ptrace₁₃_eq_ptrace₂₃_submatrix (Y : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁₃ Y = ptrace₂₃ (Y.submatrix siteEquiv₂ siteEquiv₂) := rfl

theorem ptrace₃_eq_ptrace₁_submatrix (Y : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₃ Y = ptrace₁ (Y.submatrix siteEquiv₃ siteEquiv₃) := rfl

theorem ptrace₁₂_eq_ptrace₂₃_submatrix (Y : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁₂ Y = ptrace₂₃ (Y.submatrix siteEquiv₃ siteEquiv₃) := rfl

theorem ptrace₂₃_eq_ptraceR (Y : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₂₃ Y = ptraceR Y := by
  ext i i'
  simp only [ptrace₂₃, ptraceR, Fintype.sum_prod_type]

end SiteIndex

section Embed

variable {a b c a' b' c' : Type*} [Fintype a] [Fintype b] [Fintype c]
  [Fintype a'] [Fintype b'] [Fintype c']

/-- The local embedding `(J₁ ⊗ J₂ ⊗ J₃) C (J₁ ⊗ J₂ ⊗ J₃)†` of a three-site operator. -/
def embed₃ (J₁ : Matrix a' a ℂ) (J₂ : Matrix b' b ℂ) (J₃ : Matrix c' c ℂ)
    (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (a' × b' × c') (a' × b' × c') ℂ :=
  fun x y => ∑ p, ∑ q, J₁ x.1 p.1 * J₂ x.2.1 p.2.1 * J₃ x.2.2 p.2.2 * C p q *
    star (J₁ y.1 q.1) * star (J₂ y.2.1 q.2.1) * star (J₃ y.2.2 q.2.2)

theorem embed₃_eq_mul (J₁ : Matrix a' a ℂ) (J₂ : Matrix b' b ℂ) (J₃ : Matrix c' c ℂ)
    (C : Matrix (a × b × c) (a × b × c) ℂ) :
    embed₃ J₁ J₂ J₃ C = (J₁ ⊗ₖ (J₂ ⊗ₖ J₃)) * C * (J₁ ⊗ₖ (J₂ ⊗ₖ J₃))ᴴ := by
  ext x y
  simp only [embed₃, Matrix.mul_apply, Matrix.conjTranspose_apply, kron_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [star_mul]
  ring

/-- `rank ((J₁ ⊗ J₂ ⊗ J₃) C (J₁ ⊗ J₂ ⊗ J₃)†) ≤ rank C`. -/
theorem rank_embed₃_le (J₁ : Matrix a' a ℂ) (J₂ : Matrix b' b ℂ) (J₃ : Matrix c' c ℂ)
    (C : Matrix (a × b × c) (a × b × c) ℂ) : (embed₃ J₁ J₂ J₃ C).rank ≤ C.rank := by
  rw [embed₃_eq_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem embed₃_submatrix_siteEquiv₂ (J₁ : Matrix a' a ℂ) (J₂ : Matrix b' b ℂ)
    (J₃ : Matrix c' c ℂ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    (embed₃ J₁ J₂ J₃ C).submatrix siteEquiv₂ siteEquiv₂ =
      embed₃ J₂ J₁ J₃ (C.submatrix siteEquiv₂ siteEquiv₂) := by
  ext x y
  simp only [Matrix.submatrix_apply, embed₃]
  symm
  refine Fintype.sum_equiv siteEquiv₂ _ _ fun p => ?_
  refine Fintype.sum_equiv siteEquiv₂ _ _ fun q => ?_
  simp only [siteEquiv₂_apply']
  ring

theorem embed₃_submatrix_siteEquiv₃ (J₁ : Matrix a' a ℂ) (J₂ : Matrix b' b ℂ)
    (J₃ : Matrix c' c ℂ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    (embed₃ J₁ J₂ J₃ C).submatrix siteEquiv₃ siteEquiv₃ =
      embed₃ J₃ J₁ J₂ (C.submatrix siteEquiv₃ siteEquiv₃) := by
  ext x y
  simp only [Matrix.submatrix_apply, embed₃]
  symm
  refine Fintype.sum_equiv siteEquiv₃ _ _ fun p => ?_
  refine Fintype.sum_equiv siteEquiv₃ _ _ fun q => ?_
  simp only [siteEquiv₃_apply']
  ring

variable [DecidableEq a] [DecidableEq b] [DecidableEq c]
variable {J₁ : Matrix a' a ℂ} {J₂ : Matrix b' b ℂ} {J₃ : Matrix c' c ℂ}

theorem kron₃_isometry (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1) (hJ₃ : J₃ᴴ * J₃ = 1) :
    (J₁ ⊗ₖ (J₂ ⊗ₖ J₃))ᴴ * (J₁ ⊗ₖ (J₂ ⊗ₖ J₃)) = 1 :=
  kron_isometry J₁ (J₂ ⊗ₖ J₃) hJ₁ (kron_isometry J₂ J₃ hJ₂ hJ₃)

theorem frobSq_embed₃ (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1) (hJ₃ : J₃ᴴ * J₃ = 1)
    (C : Matrix (a × b × c) (a × b × c) ℂ) : frobSq (embed₃ J₁ J₂ J₃ C) = frobSq C := by
  rw [embed₃_eq_mul, frobSq_conj_isometry _ (kron₃_isometry hJ₁ hJ₂ hJ₃)]

theorem trace_embed₃ (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1) (hJ₃ : J₃ᴴ * J₃ = 1)
    (C : Matrix (a × b × c) (a × b × c) ℂ) : (embed₃ J₁ J₂ J₃ C).trace = C.trace := by
  rw [embed₃_eq_mul, trace_conj_isometry _ (kron₃_isometry hJ₁ hJ₂ hJ₃)]

/-- `Tr₁ ((J₁ ⊗ J₂ ⊗ J₃) C (…)†) = (J₂ ⊗ J₃) (Tr₁ C) (J₂ ⊗ J₃)†`. -/
theorem ptrace₁_embed₃ (hJ₁ : J₁ᴴ * J₁ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁ (embed₃ J₁ J₂ J₃ C) = (J₂ ⊗ₖ J₃) * ptrace₁ C * (J₂ ⊗ₖ J₃)ᴴ := by
  rw [embed₃_eq_mul]
  exact ptraceL_conj J₁ (J₂ ⊗ₖ J₃) hJ₁ C

/-- `Tr₂₃ ((J₁ ⊗ J₂ ⊗ J₃) C (…)†) = J₁ (Tr₂₃ C) J₁†`. -/
theorem ptrace₂₃_embed₃ (hJ₂ : J₂ᴴ * J₂ = 1) (hJ₃ : J₃ᴴ * J₃ = 1)
    (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₂₃ (embed₃ J₁ J₂ J₃ C) = J₁ * ptrace₂₃ C * J₁ᴴ := by
  rw [ptrace₂₃_eq_ptraceR, ptrace₂₃_eq_ptraceR, embed₃_eq_mul]
  exact ptraceR_conj J₁ (J₂ ⊗ₖ J₃) (kron_isometry J₂ J₃ hJ₂ hJ₃) C

theorem frobSq_ptrace₁_embed₃ (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1)
    (hJ₃ : J₃ᴴ * J₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    frobSq (ptrace₁ (embed₃ J₁ J₂ J₃ C)) = frobSq (ptrace₁ C) := by
  rw [ptrace₁_embed₃ hJ₁, frobSq_conj_isometry _ (kron_isometry J₂ J₃ hJ₂ hJ₃)]

theorem frobSq_ptrace₂₃_embed₃ (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1)
    (hJ₃ : J₃ᴴ * J₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    frobSq (ptrace₂₃ (embed₃ J₁ J₂ J₃ C)) = frobSq (ptrace₂₃ C) := by
  rw [ptrace₂₃_embed₃ hJ₂ hJ₃, frobSq_conj_isometry _ hJ₁]

theorem frobSq_ptrace₂_embed₃ (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1)
    (hJ₃ : J₃ᴴ * J₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    frobSq (ptrace₂ (embed₃ J₁ J₂ J₃ C)) = frobSq (ptrace₂ C) := by
  rw [ptrace₂_eq_ptrace₁_submatrix, ptrace₂_eq_ptrace₁_submatrix, embed₃_submatrix_siteEquiv₂]
  exact frobSq_ptrace₁_embed₃ hJ₂ hJ₁ hJ₃ _

theorem frobSq_ptrace₃_embed₃ (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1)
    (hJ₃ : J₃ᴴ * J₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    frobSq (ptrace₃ (embed₃ J₁ J₂ J₃ C)) = frobSq (ptrace₃ C) := by
  rw [ptrace₃_eq_ptrace₁_submatrix, ptrace₃_eq_ptrace₁_submatrix, embed₃_submatrix_siteEquiv₃]
  exact frobSq_ptrace₁_embed₃ hJ₃ hJ₁ hJ₂ _

theorem frobSq_ptrace₁₃_embed₃ (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1)
    (hJ₃ : J₃ᴴ * J₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    frobSq (ptrace₁₃ (embed₃ J₁ J₂ J₃ C)) = frobSq (ptrace₁₃ C) := by
  rw [ptrace₁₃_eq_ptrace₂₃_submatrix, ptrace₁₃_eq_ptrace₂₃_submatrix,
    embed₃_submatrix_siteEquiv₂]
  exact frobSq_ptrace₂₃_embed₃ hJ₂ hJ₁ hJ₃ _

theorem frobSq_ptrace₁₂_embed₃ (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1)
    (hJ₃ : J₃ᴴ * J₃ = 1) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    frobSq (ptrace₁₂ (embed₃ J₁ J₂ J₃ C)) = frobSq (ptrace₁₂ C) := by
  rw [ptrace₁₂_eq_ptrace₂₃_submatrix, ptrace₁₂_eq_ptrace₂₃_submatrix,
    embed₃_submatrix_siteEquiv₃]
  exact frobSq_ptrace₂₃_embed₃ hJ₃ hJ₁ hJ₂ _

/-- Local isometries preserve `N`, `A`, `B`, `T₀`, hence `q_α` for every real `α`. -/
theorem energy_embed₃ (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1) (hJ₃ : J₃ᴴ * J₃ = 1)
    (α : ℝ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    energy α (embed₃ J₁ J₂ J₃ C) = energy α C := by
  unfold energy invN invA invB invT
  rw [frobSq_embed₃ hJ₁ hJ₂ hJ₃, trace_embed₃ hJ₁ hJ₂ hJ₃, frobSq_ptrace₁_embed₃ hJ₁ hJ₂ hJ₃,
    frobSq_ptrace₂_embed₃ hJ₁ hJ₂ hJ₃, frobSq_ptrace₃_embed₃ hJ₁ hJ₂ hJ₃,
    frobSq_ptrace₁₂_embed₃ hJ₁ hJ₂ hJ₃, frobSq_ptrace₁₃_embed₃ hJ₁ hJ₂ hJ₃,
    frobSq_ptrace₂₃_embed₃ hJ₁ hJ₂ hJ₃]

theorem invN_embed₃ (hJ₁ : J₁ᴴ * J₁ = 1) (hJ₂ : J₂ᴴ * J₂ = 1) (hJ₃ : J₃ᴴ * J₃ = 1)
    (C : Matrix (a × b × c) (a × b × c) ℂ) : invN (embed₃ J₁ J₂ J₃ C) = invN C :=
  frobSq_embed₃ hJ₁ hJ₂ hJ₃ C

end Embed

section Reduction

/-- The coordinate isometry `ℂ^α → ℂ^μ` of an injection `α ↪ μ`. -/
def coordIso {α μ : Type*} [DecidableEq μ] (e : α ↪ μ) : Matrix μ α ℂ :=
  (1 : Matrix μ μ ℂ).submatrix id e

theorem coordIso_isometry {α μ : Type*} [Fintype α] [Fintype μ] [DecidableEq α]
    [DecidableEq μ] (e : α ↪ μ) : (coordIso e)ᴴ * coordIso e = 1 := by
  unfold coordIso
  first
    | rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
        ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul,
        Matrix.submatrix_one_embedding]
    | (ext p q
       simp [Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix_apply])

/-- Manuscript Theorem 2.1, unequal dimensions, the case `d_i ≤ 3`, as a REDUCTION: the qutrit
endpoint inequality `hq` (open claim T2.1a) implies `q(C) ≥ 0` for every complex matrix of
rank at most two on sites of dimensions at most three. -/
theorem endpointEnergy_nonneg_of_card_le_three (hq : QutritEndpointInequality)
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b]
    [DecidableEq c] (ha : Fintype.card a ≤ 3) (hb : Fintype.card b ≤ 3)
    (hc : Fintype.card c ≤ 3) (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2) :
    0 ≤ endpointEnergy C := by
  have hq' : ∀ D : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      D.rank ≤ 2 → 0 ≤ endpointEnergy D := hq
  obtain ⟨ea⟩ := Function.Embedding.nonempty_of_card_le (ha.trans_eq (Fintype.card_fin 3).symm)
  obtain ⟨eb⟩ := Function.Embedding.nonempty_of_card_le (hb.trans_eq (Fintype.card_fin 3).symm)
  obtain ⟨ec⟩ := Function.Embedding.nonempty_of_card_le (hc.trans_eq (Fintype.card_fin 3).symm)
  have h := hq' (embed₃ (coordIso ea) (coordIso eb) (coordIso ec) C)
    ((rank_embed₃_le _ _ _ C).trans hC)
  unfold endpointEnergy at h ⊢
  rwa [energy_embed₃ (coordIso_isometry ea) (coordIso_isometry eb) (coordIso_isometry ec)]
    at h

/-- Theorem 2.1, interval bound, for local dimensions at most three, CONDITIONAL on the qutrit
endpoint inequality `hq` (open claim T2.1a). -/
theorem sharpCurve_mul_invN_le_energy_of_card_le_three (hq : QutritEndpointInequality)
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b]
    [DecidableEq c] (ha : Fintype.card a ≤ 3) (hb : Fintype.card b ≤ 3)
    (hc : Fintype.card c ≤ 3) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2)
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2) :
    sharpCurve α * invN C ≤ energy α C :=
  sharpCurve_mul_invN_le_energy_of_endpointEnergy_nonneg C hC h0 h1
    (endpointEnergy_nonneg_of_card_le_three hq ha hb hc C hC)

end Reduction

section Sites

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- The energy is invariant under exchanging sites 1 and 2. -/
theorem energy_submatrix_siteEquiv₂ (α : ℝ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    energy α (C.submatrix siteEquiv₂ siteEquiv₂) = energy α C := by
  have h1 : ptrace₁ (C.submatrix siteEquiv₂ siteEquiv₂) = ptrace₂ C := rfl
  have h2 : ptrace₂ (C.submatrix siteEquiv₂ siteEquiv₂) = ptrace₁ C := rfl
  have h3 : ptrace₃ (C.submatrix siteEquiv₂ siteEquiv₂) =
      (ptrace₃ C).submatrix (Equiv.prodComm b a) (Equiv.prodComm b a) := rfl
  have h12 : ptrace₁₂ (C.submatrix siteEquiv₂ siteEquiv₂) = ptrace₁₂ C := by
    ext k k'
    simp only [ptrace₁₂, Matrix.submatrix_apply, siteEquiv₂_apply']
    exact Finset.sum_comm
  have h13 : ptrace₁₃ (C.submatrix siteEquiv₂ siteEquiv₂) = ptrace₂₃ C := rfl
  have h23 : ptrace₂₃ (C.submatrix siteEquiv₂ siteEquiv₂) = ptrace₁₃ C := rfl
  unfold energy invN invA invB invT
  rw [h1, h2, h3, h12, h13, h23, frobSq_submatrix_equiv, frobSq_submatrix_equiv,
    trace_submatrix_equiv']
  ring

/-- The energy is invariant under moving site 3 to the front. -/
theorem energy_submatrix_siteEquiv₃ (α : ℝ) (C : Matrix (a × b × c) (a × b × c) ℂ) :
    energy α (C.submatrix siteEquiv₃ siteEquiv₃) = energy α C := by
  have h1 : ptrace₁ (C.submatrix siteEquiv₃ siteEquiv₃) = ptrace₃ C := rfl
  have h2 : ptrace₂ (C.submatrix siteEquiv₃ siteEquiv₃) =
      (ptrace₁ C).submatrix (Equiv.prodComm c b) (Equiv.prodComm c b) := rfl
  have h3 : ptrace₃ (C.submatrix siteEquiv₃ siteEquiv₃) =
      (ptrace₂ C).submatrix (Equiv.prodComm c a) (Equiv.prodComm c a) := rfl
  have h12 : ptrace₁₂ (C.submatrix siteEquiv₃ siteEquiv₃) = ptrace₁₃ C := by
    ext j j'
    simp only [ptrace₁₂, ptrace₁₃, Matrix.submatrix_apply, siteEquiv₃_apply']
    exact Finset.sum_comm
  have h13 : ptrace₁₃ (C.submatrix siteEquiv₃ siteEquiv₃) = ptrace₂₃ C := by
    ext i i'
    simp only [ptrace₁₃, ptrace₂₃, Matrix.submatrix_apply, siteEquiv₃_apply']
    exact Finset.sum_comm
  have h23 : ptrace₂₃ (C.submatrix siteEquiv₃ siteEquiv₃) = ptrace₁₂ C := rfl
  unfold energy invN invA invB invT
  rw [h1, h2, h3, h12, h13, h23, frobSq_submatrix_equiv, frobSq_submatrix_equiv,
    frobSq_submatrix_equiv, trace_submatrix_equiv']
  ring

/-- Moving the active site from the front to site 2 preserves rank, `N` and `q`. -/
theorem endpoint_zero_transport₂ (T : Matrix (b × a × c) (b × a × c) ℂ)
    (h : T.rank ≤ 2 ∧ invN T = 1 ∧ endpointEnergy T = 0) :
    (T.submatrix siteEquiv₂.symm siteEquiv₂.symm).rank ≤ 2 ∧
      invN (T.submatrix siteEquiv₂.symm siteEquiv₂.symm) = 1 ∧
      endpointEnergy (T.submatrix siteEquiv₂.symm siteEquiv₂.symm) = 0 := by
  obtain ⟨hr, hN, hq⟩ := h
  have hT : (T.submatrix siteEquiv₂.symm siteEquiv₂.symm).submatrix siteEquiv₂ siteEquiv₂ =
      T := by
    ext x y
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.rank_submatrix]
    exact hr
  · unfold invN at hN ⊢
    rw [frobSq_submatrix_equiv]
    exact hN
  · unfold endpointEnergy at hq ⊢
    rw [← energy_submatrix_siteEquiv₂, hT]
    exact hq

/-- Moving the active site from the front to site 3 preserves rank, `N` and `q`. -/
theorem endpoint_zero_transport₃ (T : Matrix (c × a × b) (c × a × b) ℂ)
    (h : T.rank ≤ 2 ∧ invN T = 1 ∧ endpointEnergy T = 0) :
    (T.submatrix siteEquiv₃.symm siteEquiv₃.symm).rank ≤ 2 ∧
      invN (T.submatrix siteEquiv₃.symm siteEquiv₃.symm) = 1 ∧
      endpointEnergy (T.submatrix siteEquiv₃.symm siteEquiv₃.symm) = 0 := by
  obtain ⟨hr, hN, hq⟩ := h
  have hT : (T.submatrix siteEquiv₃.symm siteEquiv₃.symm).submatrix siteEquiv₃ siteEquiv₃ =
      T := by
    ext x y
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.rank_submatrix]
    exact hr
  · unfold invN at hN ⊢
    rw [frobSq_submatrix_equiv]
    exact hN
  · unfold endpointEnergy at hq ⊢
    rw [← energy_submatrix_siteEquiv₃, hT]
    exact hq

end Sites

section FamilyI

theorem normSq_inv_sqrt_two : Complex.normSq ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) = 1 / 2 := by
  rw [Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    <;> norm_num

/-- Manuscript eq. (21), site 1 active: for every two-plane `E = span(f₁, f₂)` and all unit
vectors `χ`, `η` on sites 2 and 3, `(P_E/√2) ⊗ |χ⟩⟨η|` has rank at most two, `N = 1` and
endpoint energy zero. -/
theorem familyI_endpoint_zero_general {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (f₁ f₂ : a → ℂ) (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0)
    (χ η : b × c → ℂ) (hχ : vecNormSq χ = 1) (hη : vecNormSq η = 1) :
    (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)).rank ≤ 2 ∧
      invN (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)) = 1 ∧
      endpointEnergy (tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · refine rank_le_two_of_eq_mul _
      (Matrix.of fun x k => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (![f₁, f₂] k) x.1 * χ x.2)
      (Matrix.of fun k y => (starRingEnd ℂ) ((![f₁, f₂] k) y.1) * (starRingEnd ℂ) (η y.2)) ?_
    ext x y
    simp only [Matrix.smul_apply, smul_eq_mul, tensor₂, Matrix.add_apply, ketBra,
      Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  · unfold invN
    rw [frobSq_tensor₂, frobSq_smul, frobSq_proj f₁ f₂ h1 h2 h12, frobSq_ketBra_vecNormSq, hχ,
      hη, normSq_inv_sqrt_two] <;> norm_num
  · unfold endpointEnergy
    rw [energy_tensor₂, frobSq_smul, frobSq_proj f₁ f₂ h1 h2 h12, Matrix.trace_smul,
      trace_proj f₁ f₂ h1 h2, smul_eq_mul, Complex.normSq_mul, normSq_two_complex,
      normSq_inv_sqrt_two]
    ring

/-- Manuscript eq. (21), site 2 active. -/
theorem familyI_endpoint_zero_site₂ {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (f₁ f₂ : b → ℂ) (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0)
    (χ η : a × c → ℂ) (hχ : vecNormSq χ = 1) (hη : vecNormSq η = 1) :
    ((tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)).submatrix siteEquiv₂.symm siteEquiv₂.symm).rank ≤ 2 ∧
      invN ((tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)).submatrix siteEquiv₂.symm siteEquiv₂.symm) = 1 ∧
      endpointEnergy ((tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)).submatrix siteEquiv₂.symm siteEquiv₂.symm) = 0 :=
  endpoint_zero_transport₂ _ (familyI_endpoint_zero_general f₁ f₂ h1 h2 h12 χ η hχ hη)

/-- Manuscript eq. (21), site 3 active. -/
theorem familyI_endpoint_zero_site₃ {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (f₁ f₂ : c → ℂ) (h1 : vecNormSq f₁ = 1) (h2 : vecNormSq f₂ = 1) (h12 : braket f₁ f₂ = 0)
    (χ η : a × b → ℂ) (hχ : vecNormSq χ = 1) (hη : vecNormSq η = 1) :
    ((tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)).submatrix siteEquiv₃.symm siteEquiv₃.symm).rank ≤ 2 ∧
      invN ((tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)).submatrix siteEquiv₃.symm siteEquiv₃.symm) = 1 ∧
      endpointEnergy ((tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂))
        (ketBra χ η)).submatrix siteEquiv₃.symm siteEquiv₃.symm) = 0 :=
  endpoint_zero_transport₃ _ (familyI_endpoint_zero_general f₁ f₂ h1 h2 h12 χ η hχ hη)

end FamilyI

end ThreeCopyQutritWerner

end
