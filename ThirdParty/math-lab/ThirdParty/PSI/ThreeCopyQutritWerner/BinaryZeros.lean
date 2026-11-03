module

public import ThreeCopyQutritWerner.Corollaries
public import ThreeCopyQutritWerner.PPTRegion

@[expose] public section


/-!
# Families II and III of qutrit endpoint zeros (Theorem 5.1, toward the inclusion "⊇")

Manuscript Theorem 5.1 lists three families of normalized rank-two endpoint zeros. In the
notation of these files, with
`ε = [[0,1],[-1,0]]`, `J_r = ε^{⊗r}`, `B_r(U) = U ε Uᵀ J_r⁻¹ / √2` (`U : ℂ² → (ℂ²)^{⊗r}` an
isometry, plain transpose) and local binary embeddings `V` (tensor products of isometries
`ℂ² → ℂ³`):  II: `|a⟩⟨b| ⊗ V B₂(U) V†`,  III: `V B₃(U) V†`.  Family I is in `Embedding.lean`.

Proof route.

* Qubit lemma (`endpointEnergy_eq_zero_of_antisymm`): on three qubit sites, `q(C) = 0`
  whenever `K = C J₃ᵀ` is antisymmetric.  By eq. (6), `q(C) = 27 ⟨vec C, (ρ^Γ)^{⊗3} vec C⟩`
  with `ρ = ρ_{2,1/2}`; `vec (K J₃) = W^{⊗3} vec K` for `W = 1 ⊗ εᵀ`, and
  `W† ρ^Γ W = (1 + F)/6` (`epsW_conj_partialTranspose_werner`).  The operator
  `((1 + F)/2)^{⊗3}` is invariant under the global swap of the two parties, while
  `vec K` is odd under it, so the expectation vanishes.
* `B₃(U) J₃ᵀ = -(U ε Uᵀ)/√2` and `B₂(U) J₂ᵀ = (U ε Uᵀ)/√2` are antisymmetric because
  `J₃⁻¹ = J₃ᵀ`, `J₃ᵀ J₃ᵀ = -1`, `J₂⁻¹ = J₂ᵀ`, `J₂ᵀ J₂ᵀ = 1`.
* Family III: energy invariance under local isometric embeddings (`energy_embed₃`).
* Family II: `q(|a⟩⟨b| ⊗ X) = (‖a‖²‖b‖² - |⟨b,a⟩|²/2) Q(X)` (`energy_tensor₂`) and
  `Q(V B₂ V†) = Q(B₂)`; `2 Q(B₂) = q(ε ⊗ B₂) = 0` by the qubit lemma.
* Normalization and singular values (family III): `M = U ε Uᵀ J⁻¹` satisfies `M M† M = M`, so
  `M† M` is idempotent, `B† B = (M† M)/2` and `(C† C)² = (C† C)/2`; with `‖C‖_F = 1` this says
  both nonzero singular values equal `1/√2`.

Covered here: family III completely (rank, `N`, `q`, singular values); an overall phase is
absorbed by `U ↦ e^{iθ/2} U`. Family II: rank, `N` and `q`, with `|a⟩⟨b|` on site 1. The family II
singular values, its site-2/site-3 placements and the family I singular values are in the
`ZeroFamilies.lean`.
-/

noncomputable section

open scoped Matrix Kronecker ComplexOrder

namespace ThreeCopyQutritWerner

/-! ### Facts about `ε` and `J_r` -/

theorem epsMat_transpose : epsMatᵀ = -epsMat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [epsMat]

theorem epsMat_transpose_mul_self : epsMatᵀ * epsMat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [epsMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem epsMat_mul_transpose : epsMat * epsMatᵀ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [epsMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem epsMat_mul_conjTranspose : epsMat * epsMatᴴ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [epsMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem epsMat_transpose_conjTranspose : epsMatᵀᴴ = epsMat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [epsMat]

theorem epsMat_transpose_mul_transpose : epsMatᵀ * epsMatᵀ = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [epsMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem frobSq_epsMat_transpose : frobSq epsMatᵀ = 2 := by
  norm_num [frobSq, epsMat, Fin.sum_univ_two]

theorem frobSq_epsMat : frobSq epsMat = 2 := by
  norm_num [frobSq, epsMat, Fin.sum_univ_two]

theorem trace_epsMat : epsMat.trace = 0 := by
  simp [epsMat, Matrix.trace, Fin.sum_univ_two]

theorem epsJ₂_transpose : epsJ₂ᵀ = epsMatᵀ ⊗ₖ epsMatᵀ := by
  rw [epsJ₂, Matrix.kroneckerMap_transpose]

theorem epsJ₃_transpose : epsJ₃ᵀ = epsMatᵀ ⊗ₖ (epsMatᵀ ⊗ₖ epsMatᵀ) := by
  rw [epsJ₃, Matrix.kroneckerMap_transpose, Matrix.kroneckerMap_transpose]

theorem epsJ₂_transpose_mul_self : epsJ₂ᵀ * epsJ₂ = 1 := by
  rw [epsJ₂_transpose, epsJ₂, ← Matrix.mul_kronecker_mul, epsMat_transpose_mul_self,
    Matrix.one_kronecker_one]

theorem epsJ₃_transpose_mul_self : epsJ₃ᵀ * epsJ₃ = 1 := by
  rw [epsJ₃_transpose, epsJ₃, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    epsMat_transpose_mul_self, Matrix.one_kronecker_one, Matrix.one_kronecker_one]

theorem epsJ₂_inv : epsJ₂⁻¹ = epsJ₂ᵀ := Matrix.inv_eq_left_inv epsJ₂_transpose_mul_self

theorem epsJ₃_inv : epsJ₃⁻¹ = epsJ₃ᵀ := Matrix.inv_eq_left_inv epsJ₃_transpose_mul_self

theorem epsJ₃_transpose_mul_conjTranspose : epsJ₃ᵀ * epsJ₃ᵀᴴ = 1 := by
  rw [epsJ₃_transpose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    epsMat_transpose_conjTranspose, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    epsMat_transpose_mul_self, Matrix.one_kronecker_one, Matrix.one_kronecker_one]

theorem epsJ₂_transpose_mul_conjTranspose : epsJ₂ᵀ * epsJ₂ᵀᴴ = 1 := by
  rw [epsJ₂_transpose, Matrix.conjTranspose_kronecker, epsMat_transpose_conjTranspose,
    ← Matrix.mul_kronecker_mul, epsMat_transpose_mul_self, Matrix.one_kronecker_one]

theorem neg_one_kronecker_neg_one {m n : Type*} [DecidableEq m] [DecidableEq n] :
    (-1 : Matrix m m ℂ) ⊗ₖ (-1 : Matrix n n ℂ) = 1 := by
  ext x y
  simp only [Matrix.kroneckerMap_apply, Matrix.neg_apply, Matrix.one_apply, Prod.ext_iff]
  by_cases h₁ : x.1 = y.1 <;> by_cases h₂ : x.2 = y.2 <;> simp [h₁, h₂]

theorem epsJ₂_transpose_mul_transpose : epsJ₂ᵀ * epsJ₂ᵀ = 1 := by
  rw [epsJ₂_transpose, ← Matrix.mul_kronecker_mul, epsMat_transpose_mul_transpose,
    neg_one_kronecker_neg_one]

theorem epsJ₃_transpose_mul_transpose : epsJ₃ᵀ * epsJ₃ᵀ = -1 := by
  rw [epsJ₃_transpose, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    epsMat_transpose_mul_transpose, neg_one_kronecker_neg_one]
  ext x y
  simp only [Matrix.kroneckerMap_apply, Matrix.neg_apply, Matrix.one_apply, Prod.ext_iff]
  by_cases h₁ : x.1 = y.1 <;> by_cases h₂ : x.2.1 = y.2.1 <;> by_cases h₃ : x.2.2 = y.2.2 <;>
    simp [h₁, h₂, h₃]

/-! ### Matrix helpers -/

section Helpers

theorem mul_mul_cancel_of_mul_eq_one {l m n : Type*} [Fintype l] [Fintype m] [DecidableEq m]
    (A : Matrix m l ℂ) (A' : Matrix l m ℂ) (h : A * A' = 1) (X : Matrix m n ℂ) :
    A * (A' * X) = X := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

theorem transpose_mul_conjTranspose_transpose {ι : Type*} [Fintype ι]
    (U : Matrix ι (Fin 2) ℂ) (hU : Uᴴ * U = 1) : Uᵀ * Uᵀᴴ = 1 := by
  have h : Uᵀ * Uᵀᴴ = (Uᴴ * U)ᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [h, hU, Matrix.transpose_one]

theorem transpose_mul_eps_mul_transpose {ι : Type*} [Fintype ι] (U : Matrix ι (Fin 2) ℂ) :
    (U * epsMat * Uᵀ)ᵀ = -(U * epsMat * Uᵀ) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, epsMat_transpose,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem frobSq_transpose' {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    frobSq Mᵀ = frobSq M := by
  simp only [frobSq, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem frobSq_isometry_mul {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    [DecidableEq κ] (U : Matrix ι κ ℂ) (hU : Uᴴ * U = 1) (X : Matrix κ ν ℂ) :
    frobSq (U * X) = frobSq X := by
  have h : ((frobSq (U * X) : ℝ) : ℂ) = ((frobSq X : ℝ) : ℂ) := by
    rw [ofReal_frobSq_eq_trace, ofReal_frobSq_eq_trace, Matrix.conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
  exact_mod_cast h

theorem frobSq_mul_unitary {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) (O : Matrix n n ℂ) (hO : O * Oᴴ = 1) : frobSq (M * O) = frobSq M := by
  have h : ((frobSq (M * O) : ℝ) : ℂ) = ((frobSq M : ℝ) : ℂ) := by
    rw [ofReal_frobSq_eq_trace, ofReal_frobSq_eq_trace]
    calc ((M * O)ᴴ * (M * O)).trace = (Oᴴ * (Mᴴ * M * O)).trace := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (Mᴴ * M * O * Oᴴ).trace := Matrix.trace_mul_comm _ _
      _ = (Mᴴ * M).trace := by rw [Matrix.mul_assoc (Mᴴ * M), hO, Matrix.mul_one]
  exact_mod_cast h

/-- `‖U ε Uᵀ‖_F² = 2` for an isometry `U : ℂ² → ℂ^ι`. -/
theorem frobSq_U_eps_Ut {ι : Type*} [Fintype ι] (U : Matrix ι (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    frobSq (U * epsMat * Uᵀ) = 2 := by
  rw [Matrix.mul_assoc, frobSq_isometry_mul U hU, ← frobSq_transpose', Matrix.transpose_mul,
    Matrix.transpose_transpose, frobSq_isometry_mul U hU, frobSq_epsMat_transpose]

/-- `M = U ε Uᵀ O` is a partial isometry: `M M† M = M`. -/
theorem U_eps_Ut_partialIsometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι (Fin 2) ℂ) (hU : Uᴴ * U = 1) (O : Matrix ι ι ℂ) (hO : O * Oᴴ = 1) :
    U * epsMat * Uᵀ * O * (U * epsMat * Uᵀ * O)ᴴ * (U * epsMat * Uᵀ * O) =
      U * epsMat * Uᵀ * O := by
  have hUt := transpose_mul_conjTranspose_transpose U hU
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [mul_mul_cancel_of_mul_eq_one O Oᴴ hO, mul_mul_cancel_of_mul_eq_one Uᵀ Uᵀᴴ hUt,
    mul_mul_cancel_of_mul_eq_one epsMat epsMatᴴ epsMat_mul_conjTranspose,
    mul_mul_cancel_of_mul_eq_one Uᴴ U hU]

theorem conjTranspose_mul_self_idem {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) (hM : M * Mᴴ * M = M) : Mᴴ * M * (Mᴴ * M) = Mᴴ * M := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc M Mᴴ M, hM]

/-- `(W X W†)(W Y W†) = W (X Y) W†` for an isometry `W`. -/
theorem conj_mul_conj {m m' : Type*} [Fintype m] [Fintype m'] [DecidableEq m]
    (W : Matrix m' m ℂ) (hW : Wᴴ * W = 1) (X Y : Matrix m m ℂ) :
    W * X * Wᴴ * (W * Y * Wᴴ) = W * (X * Y) * Wᴴ := by
  simp only [Matrix.mul_assoc]
  rw [mul_mul_cancel_of_mul_eq_one Wᴴ W hW]

end Helpers

/-! ### Three copies and the partial transpose on qubits -/

section ThreeCopies

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem tripleCopy_mul' (M N : Matrix (m × n) (m × n) ℂ) :
    tripleCopy (M * N) = tripleCopy M * tripleCopy N := by
  rw [tripleCopy_eq_submatrix_kronecker, tripleCopy_eq_submatrix_kronecker,
    tripleCopy_eq_submatrix_kronecker, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
    Matrix.submatrix_mul_equiv]

theorem tripleCopy_conjTranspose (M : Matrix (m × n) (m × n) ℂ) :
    tripleCopy Mᴴ = (tripleCopy M)ᴴ := by
  ext x y
  simp only [tripleCopy, Matrix.conjTranspose_apply, star_mul'] <;> ring

theorem tripleCopy_smul (z : ℂ) (M : Matrix (m × n) (m × n) ℂ) :
    tripleCopy (z • M) = z ^ 3 • tripleCopy M := by
  ext x y
  simp only [tripleCopy, Matrix.smul_apply, smul_eq_mul]
  ring

end ThreeCopies

theorem expectation_smul_left {ι : Type*} [Fintype ι] (z : ℂ) (M : Matrix ι ι ℂ)
    (v : ι → ℂ) : expectation (z • M) v = z * expectation M v := by
  simp only [expectation, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem expectation_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι ι ℂ)
    (W : Matrix ι κ ℂ) (v : κ → ℂ) :
    expectation M (W *ᵥ v) = expectation (Wᴴ * M * W) v := by
  rw [expectation_eq_dotProduct, expectation_eq_dotProduct, Matrix.star_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- `vec (K M) = (1 ⊗ Mᵀ) vec K`. -/
theorem vec_mul_eq_mulVec {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (K : Matrix A B ℂ) (M : Matrix B B ℂ) :
    vec (K * M) = (Matrix.of fun (x y : A × B) =>
      (if x.1 = y.1 then (1 : ℂ) else 0) * M y.2 x.2) *ᵥ vec K := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [vec, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Fintype.sum_prod_type]
  symm
  rw [Finset.sum_eq_single a]
  · simp only [eq_self_iff_true, ↓reduceIte, one_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · intro a' _ ha'
    simp only [if_neg (Ne.symm ha'), zero_mul, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- `1 ⊗ εᵀ` on one pair `(A, B)`: it acts on the `B` index. -/
def epsW : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => (if x.1 = y.1 then 1 else 0) * epsMat y.2 x.2

/-- The projector `(1 + F)/2` onto the symmetric subspace of `ℂ² ⊗ ℂ²`. -/
def psym : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := (1 / 2 : ℂ) • (1 + swapOp (Fin 2))

theorem tripleCopy_epsW :
    tripleCopy epsW = Matrix.of fun (x y : (Fin 2 × Fin 2 × Fin 2) × (Fin 2 × Fin 2 × Fin 2)) =>
      (if x.1 = y.1 then (1 : ℂ) else 0) * epsJ₃ y.2 x.2 := by
  ext ⟨⟨a₁, a₂, a₃⟩, ⟨b₁, b₂, b₃⟩⟩ ⟨⟨c₁, c₂, c₃⟩, ⟨d₁, d₂, d₃⟩⟩
  simp only [tripleCopy, epsW, Matrix.of_apply, epsJ₃, Matrix.kroneckerMap_apply, Prod.mk.injEq]
  by_cases h₁ : a₁ = c₁ <;> by_cases h₂ : a₂ = c₂ <;> by_cases h₃ : a₃ = c₃ <;>
    simp [h₁, h₂, h₃] <;> ring

theorem vec_mul_epsJ₃ (K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    vec (K * epsJ₃) = tripleCopy epsW *ᵥ vec K := by
  rw [tripleCopy_epsW, vec_mul_eq_mulVec]

set_option maxHeartbeats 1000000 in
/-- On one qubit pair, `(1 ⊗ εᵀ)† ρ_{2,1/2}^Γ (1 ⊗ εᵀ) = (1 + F)/6`. -/
theorem epsW_conj_partialTranspose_werner :
    epsWᴴ * partialTranspose (werner 2 (1 / 2)) * epsW = (1 / 3 : ℂ) • psym := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, epsW, psym,
    partialTranspose_werner_apply', siteKer, swapOp, Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply, smul_eq_mul, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> norm_num [epsMat]

theorem psym_apply_swap (x : Fin 2 × Fin 2) (a b : Fin 2) : psym x (b, a) = psym x (a, b) := by
  obtain ⟨u, v⟩ := x
  simp only [psym, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, swapOp, Prod.mk.injEq,
    smul_eq_mul]
  ring

theorem tripleCopy_psym_swap (x y : (Fin 2 × Fin 2 × Fin 2) × (Fin 2 × Fin 2 × Fin 2)) :
    tripleCopy psym x y.swap = tripleCopy psym x y := by
  obtain ⟨⟨a₁, a₂, a₃⟩, ⟨b₁, b₂, b₃⟩⟩ := y
  show psym (x.1.1, x.2.1) (b₁, a₁) * psym (x.1.2.1, x.2.2.1) (b₂, a₂) *
      psym (x.1.2.2, x.2.2.2) (b₃, a₃) =
    psym (x.1.1, x.2.1) (a₁, b₁) * psym (x.1.2.1, x.2.2.1) (a₂, b₂) *
      psym (x.1.2.2, x.2.2.2) (a₃, b₃)
  rw [psym_apply_swap _ a₁ b₁, psym_apply_swap _ a₂ b₂, psym_apply_swap _ a₃ b₃]

/-- The symmetric projector on every pair annihilates `vec K` for antisymmetric `K`. -/
theorem tripleCopy_psym_mulVec_eq_zero
    (K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) (hK : Kᵀ = -K) :
    tripleCopy psym *ᵥ vec K = 0 := by
  funext x
  have hs : (tripleCopy psym *ᵥ vec K) x = -((tripleCopy psym *ᵥ vec K) x) := by
    calc (tripleCopy psym *ᵥ vec K) x
        = ∑ y, tripleCopy psym x y * vec K y := rfl
      _ = ∑ y, tripleCopy psym x (Equiv.prodComm _ _ y) * vec K (Equiv.prodComm _ _ y) :=
          (Equiv.sum_comp (Equiv.prodComm _ _) _).symm
      _ = ∑ y, -(tripleCopy psym x y * vec K y) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Equiv.prodComm_apply, tripleCopy_psym_swap]
          have h : vec K y.swap = -vec K y := by
            show K y.2 y.1 = -K y.1 y.2
            have := congrFun (congrFun hK y.1) y.2
            simpa using this
          rw [h, mul_neg]
      _ = -((tripleCopy psym *ᵥ vec K) x) := by
          rw [Finset.sum_neg_distrib] <;> rfl
  show (tripleCopy psym *ᵥ vec K) x = 0
  linear_combination hs / 2

theorem expectation_tripleCopy_psym_eq_zero
    (K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) (hK : Kᵀ = -K) :
    expectation (tripleCopy psym) (vec K) = 0 := by
  rw [expectation_eq_dotProduct, tripleCopy_psym_mulVec_eq_zero K hK]
  simp

/-- Qubit lemma: on three qubit sites, `q(C) = 0` whenever `C J₃ᵀ` is antisymmetric. -/
theorem endpointEnergy_eq_zero_of_antisymm
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (h : (C * epsJ₃ᵀ)ᵀ = -(C * epsJ₃ᵀ)) : endpointEnergy C = 0 := by
  obtain ⟨K, hK, rfl⟩ : ∃ K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ,
      Kᵀ = -K ∧ C = K * epsJ₃ :=
    ⟨C * epsJ₃ᵀ, h, by rw [Matrix.mul_assoc, epsJ₃_transpose_mul_self, Matrix.mul_one]⟩
  have hE := expectation_partialTranspose_tripleCopy_werner 2 (1 / 2) (K * epsJ₃)
  have h0 : expectation (partialTranspose (tripleCopy (werner 2 (1 / 2))))
      (vec (K * epsJ₃)) = 0 := by
    rw [partialTranspose_tripleCopy, vec_mul_epsJ₃, expectation_mulVec,
      ← tripleCopy_conjTranspose, ← tripleCopy_mul', ← tripleCopy_mul',
      epsW_conj_partialTranspose_werner, tripleCopy_smul, expectation_smul_left,
      expectation_tripleCopy_psym_eq_zero K hK, mul_zero]
  rw [h0] at hE
  have hne : ((((2 : ℕ) : ℂ) * (((2 : ℕ) : ℂ) - (((1 / 2 : ℝ)) : ℂ)))⁻¹) ^ 3 ≠ 0 := by
    norm_num
  have h1 : ((energy (1 / 2) (K * epsJ₃) : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hE.symm with h' | h'
    · exact absurd h' hne
    · exact h'
  unfold endpointEnergy
  exact_mod_cast h1

/-! ### Family III -/

theorem binaryB₃_mul_transpose (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) :
    binaryB₃ U * epsJ₃ᵀ = -((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (U * epsMat * Uᵀ)) := by
  rw [binaryB₃, epsJ₃_inv, Matrix.smul_mul, Matrix.mul_assoc (U * epsMat * Uᵀ),
    epsJ₃_transpose_mul_transpose, Matrix.mul_neg, Matrix.mul_one, smul_neg]

theorem binaryB₃_antisymm (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) :
    (binaryB₃ U * epsJ₃ᵀ)ᵀ = -(binaryB₃ U * epsJ₃ᵀ) := by
  rw [binaryB₃_mul_transpose, Matrix.transpose_neg, Matrix.transpose_smul,
    transpose_mul_eps_mul_transpose, smul_neg]

theorem endpointEnergy_binaryB₃ (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) :
    endpointEnergy (binaryB₃ U) = 0 :=
  endpointEnergy_eq_zero_of_antisymm _ (binaryB₃_antisymm U)

theorem binaryB₃_eq_mul (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) :
    binaryB₃ U = U * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (epsMat * Uᵀ * epsJ₃⁻¹)) := by
  rw [binaryB₃, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

theorem rank_binaryB₃_le (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) :
    (binaryB₃ U).rank ≤ 2 :=
  rank_le_two_of_eq_mul _ _ _ (binaryB₃_eq_mul U)

theorem frobSq_binaryB₃ (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    frobSq (binaryB₃ U) = 1 := by
  rw [binaryB₃, frobSq_smul, normSq_inv_sqrt_two, epsJ₃_inv,
    frobSq_mul_unitary (U * epsMat * Uᵀ) epsJ₃ᵀ epsJ₃_transpose_mul_conjTranspose,
    frobSq_U_eps_Ut U hU]
  norm_num

/-- `|1/√2|² = 1/2`, as `star c * c`. -/
theorem star_inv_sqrt_two_mul_self :
    star ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, normSq_inv_sqrt_two]
  norm_num

theorem binaryB₃_conjTranspose_mul_self (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) :
    (binaryB₃ U)ᴴ * binaryB₃ U = (1 / 2 : ℂ) •
      ((U * epsMat * Uᵀ * epsJ₃ᵀ)ᴴ * (U * epsMat * Uᵀ * epsJ₃ᵀ)) := by
  rw [binaryB₃, epsJ₃_inv, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, star_inv_sqrt_two_mul_self]

theorem binaryB₃_conjTranspose_mul_self_sq (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) :
    (binaryB₃ U)ᴴ * binaryB₃ U * ((binaryB₃ U)ᴴ * binaryB₃ U) =
      (1 / 2 : ℂ) • ((binaryB₃ U)ᴴ * binaryB₃ U) := by
  have hM := conjTranspose_mul_self_idem _
    (U_eps_Ut_partialIsometry U hU epsJ₃ᵀ epsJ₃_transpose_mul_conjTranspose)
  rw [binaryB₃_conjTranspose_mul_self, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM,
    smul_smul]

theorem familyIII_eq_embed₃ (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    familyIII U V₁ V₂ V₃ = embed₃ V₁ V₂ V₃ (binaryB₃ U) := by
  rw [familyIII, embed₃_eq_mul]

/-- Theorem 5.1, family III (inclusion "⊇"): every `V B₃(U) V†` is a normalized complex
27 × 27 matrix of rank at most two with endpoint energy zero, and `(C†C)² = (C†C)/2`, i.e.
both nonzero singular values equal `1/√2`. -/
theorem familyIII_endpoint_zero (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) (h₁ : V₁ᴴ * V₁ = 1)
    (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1) :
    (familyIII U V₁ V₂ V₃).rank ≤ 2 ∧ invN (familyIII U V₁ V₂ V₃) = 1 ∧
      endpointEnergy (familyIII U V₁ V₂ V₃) = 0 ∧
      (familyIII U V₁ V₂ V₃)ᴴ * familyIII U V₁ V₂ V₃ *
          ((familyIII U V₁ V₂ V₃)ᴴ * familyIII U V₁ V₂ V₃) =
        (1 / 2 : ℂ) • ((familyIII U V₁ V₂ V₃)ᴴ * familyIII U V₁ V₂ V₃) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [familyIII_eq_embed₃]
    exact (rank_embed₃_le _ _ _ _).trans (rank_binaryB₃_le U)
  · rw [familyIII_eq_embed₃, invN_embed₃ h₁ h₂ h₃]
    exact frobSq_binaryB₃ U hU
  · rw [familyIII_eq_embed₃]
    unfold endpointEnergy
    rw [energy_embed₃ h₁ h₂ h₃]
    exact endpointEnergy_binaryB₃ U
  · have hW := kron₃_isometry h₁ h₂ h₃
    rw [familyIII, conjTranspose_conj_mul_conj _ hW, conj_mul_conj _ hW,
      binaryB₃_conjTranspose_mul_self_sq U hU, Matrix.mul_smul, Matrix.smul_mul]

/-! ### Family II -/

theorem tensor₂_eq_kronecker {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι ι ℂ)
    (N : Matrix κ κ ℂ) : tensor₂ M N = M ⊗ₖ N := by
  ext x y; rfl

theorem binaryB₂_mul_transpose (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) :
    binaryB₂ U * epsJ₂ᵀ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (U * epsMat * Uᵀ) := by
  rw [binaryB₂, epsJ₂_inv, Matrix.smul_mul, Matrix.mul_assoc (U * epsMat * Uᵀ),
    epsJ₂_transpose_mul_transpose, Matrix.mul_one]

/-- `ε ⊗ B₂(U)` on three qubit sites has endpoint energy zero. -/
theorem endpointEnergy_eps_tensor_binaryB₂ (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) :
    endpointEnergy (tensor₂ epsMat (binaryB₂ U)) = 0 := by
  apply endpointEnergy_eq_zero_of_antisymm
  have hJ : epsJ₃ᵀ = epsMatᵀ ⊗ₖ epsJ₂ᵀ := by
    rw [epsJ₃, epsJ₂, Matrix.kroneckerMap_transpose]
  have hK : tensor₂ epsMat (binaryB₂ U) * epsJ₃ᵀ =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (U * epsMat * Uᵀ)) := by
    rw [tensor₂_eq_kronecker, hJ, ← Matrix.mul_kronecker_mul, epsMat_mul_transpose,
      binaryB₂_mul_transpose]
  have hY := transpose_mul_eps_mul_transpose U
  rw [hK]
  ext x y
  have hYe : (U * epsMat * Uᵀ) y.2 x.2 = -(U * epsMat * Uᵀ) x.2 y.2 := by
    have h' := congrFun (congrFun hY x.2) y.2
    simpa using h'
  simp only [Matrix.transpose_apply, Matrix.kroneckerMap_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hYe]
  by_cases h : x.1 = y.1
  · simp [h]
  · simp [h, Ne.symm h]

/-- The two-site factor of `energy_tensor₂` at `α = 1/2`. -/
def twoSiteEndpoint {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix (ι × κ) (ι × κ) ℂ) : ℝ :=
  frobSq X - 1 / 2 * (frobSq (ptraceL X) + frobSq (ptraceR X)) +
    (1 / 2) ^ 2 * Complex.normSq X.trace

theorem twoSiteEndpoint_binaryB₂ (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) :
    twoSiteEndpoint (binaryB₂ U) = 0 := by
  have h := endpointEnergy_eps_tensor_binaryB₂ U
  unfold endpointEnergy at h
  rw [energy_tensor₂, frobSq_epsMat, trace_epsMat, Complex.normSq_zero] at h
  unfold twoSiteEndpoint
  linear_combination h / 2

theorem twoSiteEndpoint_conj {L R L' R' : Type*} [Fintype L] [Fintype R] [Fintype L']
    [Fintype R'] [DecidableEq L] [DecidableEq R] (U : Matrix L' L ℂ) (V : Matrix R' R ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (X : Matrix (L × R) (L × R) ℂ) :
    twoSiteEndpoint ((U ⊗ₖ V) * X * (U ⊗ₖ V)ᴴ) = twoSiteEndpoint X := by
  have hW := kron_isometry U V hU hV
  unfold twoSiteEndpoint
  rw [frobSq_conj_isometry _ hW, ptraceL_conj U V hU, ptraceR_conj U V hV,
    frobSq_conj_isometry V hV, frobSq_conj_isometry U hU, trace_conj_isometry _ hW]

theorem frobSq_binaryB₂ (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    frobSq (binaryB₂ U) = 1 := by
  rw [binaryB₂, frobSq_smul, normSq_inv_sqrt_two, epsJ₂_inv,
    frobSq_mul_unitary (U * epsMat * Uᵀ) epsJ₂ᵀ epsJ₂_transpose_mul_conjTranspose,
    frobSq_U_eps_Ut U hU]
  norm_num

theorem binaryB₂_eq_mul (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) :
    binaryB₂ U = U * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (epsMat * Uᵀ * epsJ₂⁻¹)) := by
  rw [binaryB₂, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

/-- `|a⟩⟨b| ⊗ V B₂(U) V†` factors through `Unit × Fin 2`, so its rank is at most two. -/
theorem rank_familyII_le (a b : Fin 3 → ℂ) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) : (familyII a b U V₂ V₃).rank ≤ 2 := by
  have hK : ketBra a b = (Matrix.of fun i (_ : Unit) => a i) *
      (Matrix.of fun (_ : Unit) j => (starRingEnd ℂ) (b j)) := by
    ext i j
    simp [ketBra, Matrix.mul_apply]
  have hX : (V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ = ((V₂ ⊗ₖ V₃) * U) *
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (epsMat * Uᵀ * epsJ₂⁻¹)) * (V₂ ⊗ₖ V₃)ᴴ) := by
    rw [binaryB₂_eq_mul]
    simp only [Matrix.mul_assoc]
  rw [familyII, tensor₂_eq_kronecker, hK, hX, Matrix.mul_kronecker_mul]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))

/-- Theorem 5.1, family II with `|a⟩⟨b|` on site 1: for unit `a`, `b` and isometries `U`,
`V₂`, `V₃`, the matrix `|a⟩⟨b| ⊗ V B₂(U) V†` has rank at most two, `N = 1` and endpoint energy
zero.  Its singular values and the site-2/site-3 placements are not stated yet. -/
theorem familyII_endpoint_zero (a b : Fin 3 → ℂ) (ha : vecNormSq a = 1) (hb : vecNormSq b = 1)
    (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ)
    (h₂ : V₂ᴴ * V₂ = 1) (h₃ : V₃ᴴ * V₃ = 1) :
    (familyII a b U V₂ V₃).rank ≤ 2 ∧ invN (familyII a b U V₂ V₃) = 1 ∧
      endpointEnergy (familyII a b U V₂ V₃) = 0 := by
  have hW := kron_isometry V₂ V₃ h₂ h₃
  refine ⟨rank_familyII_le a b U V₂ V₃, ?_, ?_⟩
  · have ha' : ∑ y, Complex.normSq (a y) = 1 := ha
    have hb' : ∑ y, Complex.normSq (b y) = 1 := hb
    unfold familyII invN
    rw [frobSq_tensor₂, frobSq_ketBra, frobSq_conj_isometry _ hW, frobSq_binaryB₂ U hU, ha', hb']
    norm_num
  · unfold endpointEnergy familyII
    rw [energy_tensor₂]
    have h0 := twoSiteEndpoint_conj V₂ V₃ h₂ h₃ (binaryB₂ U)
    rw [twoSiteEndpoint_binaryB₂] at h0
    unfold twoSiteEndpoint at h0
    rw [h0, mul_zero]

end ThreeCopyQutritWerner

end
