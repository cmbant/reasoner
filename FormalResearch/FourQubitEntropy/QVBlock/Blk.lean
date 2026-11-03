module

public import FormalResearch.FourQubitEntropy.QVBlock.Kron

/-!
# Block form `Blk` and the spin-sector decomposition of `⊗_q Blk` (QV block calculus, T5/T6)

Per qubit the row index of the intertwiner `C` is `Idx = Σ j, Fin (dim j) × Fin (mult j)`
(spin `j`, magnetic index `k`, multiplicity index `μ`).

* `blk dim X`: block diagonal matrix with block `1_{dim j} ⊗ X j` (T5).
* `spinEquiv`: `(Q → Idx) ≃ Σ p : Q → J, (magnetic) × (multiplicity)`, regrouping by spin tuples `p`.
* `blkSpin dim Y`: for a family `Y p` of matrices on the multiplicity space `⊗_q ℂ^{mult (p q)}`,
  the matrix on `Q → Idx` that is `1 ⊗ Y p` on the sector `p` (and `0` between sectors).
  It is additive and multiplicative (`blkSpin_mul`).
* `kronPi_blk` (T6): `⊗_q blk (X̂ q) = blkSpin (p ↦ ⊗_q X̂ q (p q))`.
-/

@[expose] public section


open scoped Matrix BigOperators Kronecker

namespace FormalResearch.FourQubitEntropy.QVBlock

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [CommRing 𝕜]
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The per-qubit row index `Σ j, Fin (dim j) × Fin (mult j)`. -/
abbrev Idx (dim mult : J → ℕ) : Type _ := Σ j : J, Fin (dim j) × Fin (mult j)

theorem one_kronecker_mul {l m : Type*} [Fintype l] [Fintype m] [DecidableEq l]
    (A B : Matrix m m 𝕜) :
    (1 : Matrix l l 𝕜) ⊗ₖ (A * B) = ((1 : Matrix l l 𝕜) ⊗ₖ A) * ((1 : Matrix l l 𝕜) ⊗ₖ B) := by
  rw [← Matrix.mul_kronecker_mul, one_mul]

section Blk
variable (dim : J → ℕ) {mult : J → ℕ}

/-- `Blk(X) = ⊕_j 1_{dim j} ⊗ X j`, in the row order `(j, k, μ)` (T5). -/
def blk (X : ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜) : Matrix (Idx dim mult) (Idx dim mult) 𝕜 :=
  Matrix.blockDiagonal' fun j => (1 : Matrix (Fin (dim j)) (Fin (dim j)) 𝕜) ⊗ₖ X j

theorem blk_same (X : ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜) (j : J) (k k' : Fin (dim j))
    (μ μ' : Fin (mult j)) :
    blk dim X ⟨j, (k, μ)⟩ ⟨j, (k', μ')⟩ = (if k = k' then 1 else 0) * X j μ μ' := by
  simp [blk, Matrix.one_apply]

theorem blk_ne (X : ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜) {j j' : J} (h : j ≠ j')
    (a : Fin (dim j) × Fin (mult j)) (b : Fin (dim j') × Fin (mult j')) :
    blk dim X ⟨j, a⟩ ⟨j', b⟩ = 0 :=
  Matrix.blockDiagonal'_apply_ne _ _ _ h

theorem blk_mul (X Y : ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜) :
    blk dim (X * Y) = blk dim X * blk dim Y := by
  unfold blk
  rw [← Matrix.blockDiagonal'_mul]
  congr 1
  funext j
  exact one_kronecker_mul (l := Fin (dim j)) _ _

theorem blk_one : blk dim (1 : ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜) = 1 := by
  unfold blk
  have : ∀ j, (1 : Matrix (Fin (dim j)) (Fin (dim j)) 𝕜) ⊗ₖ
      ((1 : ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜) j) = 1 := fun j => by
    simp
  simp only [this]
  exact Matrix.blockDiagonal'_one

/-- `blk` is injective when all magnetic dimensions are positive. -/
theorem blk_injective (hdim : ∀ j, 0 < dim j) :
    Function.Injective (blk dim : (∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜) → _) := by
  intro X Y h
  funext j
  ext μ μ'
  have := congrFun (congrFun h ⟨j, (⟨0, hdim j⟩, μ)⟩) ⟨j, (⟨0, hdim j⟩, μ')⟩
  simpa [blk_same] using this

end Blk

section Spin
variable (dim : J → ℕ) {mult : J → ℕ}
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Regrouping `(Q → Σ j, A j) ≃ Σ p : Q → J, ∀ q, A (p q)` for `A j = Fin (dim j) × Fin (mult j)`,
with the product pulled out. -/
def spinEquiv (dim mult : J → ℕ) :
    (Q → Idx dim mult) ≃
      Σ p : Q → J, (∀ q, Fin (dim (p q))) × (∀ q, Fin (mult (p q))) where
  toFun a := ⟨fun q => (a q).1, (fun q => (a q).2.1, fun q => (a q).2.2)⟩
  invFun x := fun q => ⟨x.1 q, (x.2.1 q, x.2.2 q)⟩
  left_inv a := by funext q; rfl
  right_inv x := rfl

/-- The matrix on `Q → Idx` that is `1 ⊗ Y p` on the spin sector `p`. -/
def blkSpin (Y : ∀ p : Q → J, Matrix (∀ q, Fin (mult (p q))) (∀ q, Fin (mult (p q))) 𝕜) :
    Matrix (Q → Idx dim mult) (Q → Idx dim mult) 𝕜 :=
  (Matrix.blockDiagonal' fun p =>
    (1 : Matrix (∀ q, Fin (dim (p q))) (∀ q, Fin (dim (p q))) 𝕜) ⊗ₖ Y p).submatrix
      (spinEquiv dim mult) (spinEquiv dim mult)

theorem blkSpin_mul (Y Z : ∀ p : Q → J, Matrix (∀ q, Fin (mult (p q))) (∀ q, Fin (mult (p q))) 𝕜) :
    blkSpin dim (fun p => Y p * Z p) = blkSpin dim Y * blkSpin dim Z := by
  unfold blkSpin
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  rw [← Matrix.blockDiagonal'_mul]
  congr 1
  funext p
  exact one_kronecker_mul (l := ∀ q, Fin (dim (p q))) _ _

theorem blkSpin_add (Y Z : ∀ p : Q → J, Matrix (∀ q, Fin (mult (p q))) (∀ q, Fin (mult (p q))) 𝕜) :
    blkSpin dim (fun p => Y p + Z p) = blkSpin dim Y + blkSpin dim Z := by
  unfold blkSpin
  have : (Matrix.blockDiagonal' fun p =>
      (1 : Matrix (∀ q, Fin (dim (p q))) (∀ q, Fin (dim (p q))) 𝕜) ⊗ₖ (Y p + Z p)) =
      (Matrix.blockDiagonal' fun p =>
        (1 : Matrix (∀ q, Fin (dim (p q))) (∀ q, Fin (dim (p q))) 𝕜) ⊗ₖ Y p) +
      (Matrix.blockDiagonal' fun p =>
        (1 : Matrix (∀ q, Fin (dim (p q))) (∀ q, Fin (dim (p q))) 𝕜) ⊗ₖ Z p) := by
    rw [← Matrix.blockDiagonal'_add]
    congr 1
    funext p
    exact Matrix.kronecker_add _ _ _
  rw [this]
  rfl

theorem blkSpin_smul (c : 𝕜)
    (Y : ∀ p : Q → J, Matrix (∀ q, Fin (mult (p q))) (∀ q, Fin (mult (p q))) 𝕜) :
    blkSpin dim (fun p => c • Y p) = c • blkSpin dim Y := by
  unfold blkSpin
  have : (Matrix.blockDiagonal' fun p =>
      (1 : Matrix (∀ q, Fin (dim (p q))) (∀ q, Fin (dim (p q))) 𝕜) ⊗ₖ (c • Y p)) =
      c • (Matrix.blockDiagonal' fun p =>
        (1 : Matrix (∀ q, Fin (dim (p q))) (∀ q, Fin (dim (p q))) 𝕜) ⊗ₖ Y p) := by
    ext ⟨p, i⟩ ⟨p', j⟩
    simp only [Matrix.blockDiagonal'_apply', Matrix.smul_apply]
    split_ifs <;> simp [Matrix.kroneckerMap_apply, mul_left_comm]
  rw [this]
  rfl

theorem blkSpin_zero :
    blkSpin dim (fun p : Q → J => (0 : Matrix (∀ q, Fin (mult (p q))) (∀ q, Fin (mult (p q))) 𝕜))
      = 0 := by
  unfold blkSpin
  ext a b
  simp [Matrix.blockDiagonal'_apply]

theorem blkSpin_sum {ι : Type*} (s : Finset ι)
    (Y : ι → ∀ p : Q → J, Matrix (∀ q, Fin (mult (p q))) (∀ q, Fin (mult (p q))) 𝕜) :
    blkSpin dim (fun p => ∑ i ∈ s, Y i p) = ∑ i ∈ s, blkSpin dim (Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using blkSpin_zero dim
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [blkSpin_add, ih]

/-- **T6.** The Kronecker product over the qubits of block matrices is block diagonal over spin
tuples `p`, with block `1 ⊗ (⊗_q X̂_q (p q))`. -/
theorem kronPi_blk (Xh : Q → ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) 𝕜) :
    kronPi (fun q => blk dim (Xh q)) = blkSpin dim (fun p => kronPi (fun q => Xh q (p q))) := by
  ext a b
  obtain ⟨⟨p, k, μ⟩, rfl⟩ := (spinEquiv dim mult).symm.surjective a
  obtain ⟨⟨p', k', μ'⟩, rfl⟩ := (spinEquiv dim mult).symm.surjective b
  have ha : ∀ q, ((spinEquiv dim mult).symm ⟨p, (k, μ)⟩ : Q → Idx dim mult) q =
      ⟨p q, (k q, μ q)⟩ := fun q => rfl
  have hb : ∀ q, ((spinEquiv dim mult).symm ⟨p', (k', μ')⟩ : Q → Idx dim mult) q =
      ⟨p' q, (k' q, μ' q)⟩ := fun q => rfl
  simp only [kronPi_apply, ha, hb, blkSpin, Matrix.submatrix_apply, Equiv.apply_symm_apply]
  by_cases hp : p = p'
  · subst hp
    simp only [blk_same, Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply,
      Finset.prod_mul_distrib, kronPi_apply]
    congr 1
    have := congrFun (congrFun (kronPi_one (𝕜 := 𝕜) (Q := Q)
      (m := fun q => Fin (dim (p q)))) k) k'
    simpa [Matrix.one_apply] using this
  · obtain ⟨q, hq⟩ := Function.ne_iff.mp hp
    rw [Finset.prod_eq_zero (Finset.mem_univ q) (blk_ne dim _ hq _ _),
      Matrix.blockDiagonal'_apply_ne _ _ _ hp]

end Spin

end FormalResearch.FourQubitEntropy.QVBlock
