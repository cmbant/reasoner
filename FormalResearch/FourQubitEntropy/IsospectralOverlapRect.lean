import FormalResearch.FourQubitEntropy.IsospectralOverlap

/-!
# Isospectral overlap lemma: rectangular coefficient matrices and attainment

Source: `ResearchNotes/QI/four_qubit_entropy/spectral_spinflip_bound.tex`, Lemma
`lem:fqe-isospectral-overlap`.

`IsospectralOverlap.lean` proves the lemma for square coefficient matrices (equal local dimensions).
This module proves it for an arbitrary pair of local dimensions `ι`, `κ` (coefficient matrices
`M W : Matrix ι κ ℂ`) and the attainment clause.

* `isospectral_overlap_rect` (**proved**): `M W : Matrix ι κ ℂ` with `‖M‖_F = 1` whose marginals are
  related by unitaries `P` (on `ι`) and `Q` (on `κ`) (`W Wᴴ = P (M Mᴴ) Pᴴ`, `Wᴴ W = Q (Mᴴ M) Qᴴ`, i.e.
  `ψ` and `φ` have the same Schmidt coefficients, the Schmidt bases being unrelated) satisfy
  `(2l - 1)₊² ≤ |tr Mᴴ W|² + ½(‖M Mᴴ - W Wᴴ‖² + ‖Mᴴ M - Wᴴ W‖²)` for every eigenvalue `l` of `M Mᴴ`
  (for `l > 1/2` this is the top Schmidt coefficient `λ₁`, and for `l ≤ 1/2` the right side is `0`).
  Proof: padding to the square matrices `fromBlocks 0 M 0 0` on `ι ⊕ κ` and applying the square case.
* `isospectral_overlap_schmidt` (**proved**): the same for Schmidt decompositions
  `M = U D Vᴴ`, `W = U' D V'ᴴ` with the same coefficient matrix `D` (arbitrary rectangular `D`).
* `isospectral_overlap_attained` (**proved**): attainment. For coefficient matrices
  `M = U D Vᴴ` and `W = U D' Vᴴ`, `D = rectDiag s`, `D' = rectDiag s'` with `s' 0 = s 0`,
  `s' a = - s a` for `a ≥ 1` (the sign of every Schmidt term except the first is changed),
  `Σ_a s_a² = 1`, `λ₁ = s₀² ≥ 1/2` the largest Schmidt coefficient: `M, W` have the same Schmidt
  coefficients and equality holds in the lemma, with value `(2λ₁ - 1)²`; both marginal mismatches
  vanish and the overlap is `tr Mᴴ W = 2λ₁ - 1`.
  (Here `Fin m × Fin n` and the rectangular diagonal `rectDiag` model `ℂ^m ⊗ ℂ^n`.)

All statements are proved, with no hypothesis assuming a conclusion.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Finset

namespace FormalResearch.FourQubitEntropy.Isospectral

section Rect
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Squared Frobenius norm of a rectangular matrix. -/
noncomputable def fnR (A : Matrix ι κ ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (A i j)

/-- The padding `M ↦ [[0, M], [0, 0]]` into a square matrix on `ι ⊕ κ`. -/
def padM (M : Matrix ι κ ℂ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := Matrix.fromBlocks 0 M 0 0

theorem fn2_fromBlocks_diag (A : Matrix ι ι ℂ) :
    fn2 (Matrix.fromBlocks A (0 : Matrix ι κ ℂ) (0 : Matrix κ ι ℂ) (0 : Matrix κ κ ℂ)) = fn2 A := by
  simp [fn2, Fintype.sum_sum_type]

theorem fn2_fromBlocks_diag' (A : Matrix κ κ ℂ) :
    fn2 (Matrix.fromBlocks (0 : Matrix ι ι ℂ) (0 : Matrix ι κ ℂ) (0 : Matrix κ ι ℂ) A) = fn2 A := by
  simp [fn2, Fintype.sum_sum_type]

theorem fn2_padM (M : Matrix ι κ ℂ) : fn2 (padM M) = fnR M := by
  simp [fn2, fnR, padM, Fintype.sum_sum_type]

theorem padM_mul_conjT (M : Matrix ι κ ℂ) :
    padM M * (padM M)ᴴ = Matrix.fromBlocks (M * Mᴴ) 0 0 0 := by
  simp [padM, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem padM_conjT_mul (M : Matrix ι κ ℂ) :
    (padM M)ᴴ * padM M = Matrix.fromBlocks 0 0 0 (Mᴴ * M) := by
  simp [padM, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem trace_padM (M W : Matrix ι κ ℂ) :
    Matrix.trace ((padM M)ᴴ * padM W) = Matrix.trace (Mᴴ * W) := by
  simp [padM, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.trace,
    Fintype.sum_sum_type]

theorem padU_mem_left (P : Matrix ι ι ℂ) (hP : P ∈ Matrix.unitaryGroup ι ℂ) :
    (Matrix.fromBlocks P (0 : Matrix ι κ ℂ) (0 : Matrix κ ι ℂ) (1 : Matrix κ κ ℂ)) ∈
      Matrix.unitaryGroup (ι ⊕ κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have := Matrix.mem_unitaryGroup_iff.mp hP
  rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, add_zero, zero_add]
  rw [← Matrix.star_eq_conjTranspose, this, Matrix.fromBlocks_one]

theorem padU_mem_right (Q : Matrix κ κ ℂ) (hQ : Q ∈ Matrix.unitaryGroup κ ℂ) :
    (Matrix.fromBlocks (1 : Matrix ι ι ℂ) (0 : Matrix ι κ ℂ) (0 : Matrix κ ι ℂ) Q) ∈
      Matrix.unitaryGroup (ι ⊕ κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have := Matrix.mem_unitaryGroup_iff.mp hQ
  rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, add_zero, zero_add]
  rw [← Matrix.star_eq_conjTranspose, this, Matrix.fromBlocks_one]

/-- **Isospectral overlap lemma** (`lem:fqe-isospectral-overlap`), arbitrary local dimensions. -/
theorem isospectral_overlap_rect (M W : Matrix ι κ ℂ) (P : Matrix ι ι ℂ) (Q : Matrix κ κ ℂ)
    (hM : fnR M = 1)
    (hP : P ∈ Matrix.unitaryGroup ι ℂ) (hQ : Q ∈ Matrix.unitaryGroup κ ℂ)
    (hA : W * Wᴴ = P * (M * Mᴴ) * Pᴴ) (hB : Wᴴ * W = Q * (Mᴴ * M) * Qᴴ)
    (u : ι → ℂ) (hu : u ≠ 0) (l : ℝ) (hMu : (M * Mᴴ) *ᵥ u = (l : ℂ) • u) :
    (max (2 * l - 1) 0) ^ 2 ≤ Complex.normSq (Matrix.trace (Mᴴ * W))
      + (fn2 (M * Mᴴ - W * Wᴴ) + fn2 (Mᴴ * M - Wᴴ * W)) / 2 := by
  have h := isospectral_overlap (padM M) (padM W)
    (Matrix.fromBlocks P (0 : Matrix ι κ ℂ) (0 : Matrix κ ι ℂ) (1 : Matrix κ κ ℂ))
    (Matrix.fromBlocks (1 : Matrix ι ι ℂ) (0 : Matrix ι κ ℂ) (0 : Matrix κ ι ℂ) Q)
    (by rw [fn2_padM, hM]) (padU_mem_left P hP) (padU_mem_right Q hQ)
    (by
      rw [padM_mul_conjT, padM_mul_conjT, hA]
      simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply])
    (by
      rw [padM_conjT_mul, padM_conjT_mul, hB]
      simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply])
    (Sum.elim u 0) (by
      intro h0
      apply hu
      funext i
      simpa using congrFun h0 (Sum.inl i)) l (by
      rw [padM_mul_conjT]
      ext (i | k)
      · simpa [Matrix.fromBlocks_mulVec] using congrFun hMu i
      · simp [Matrix.fromBlocks_mulVec])
  rw [trace_padM, padM_mul_conjT, padM_mul_conjT, padM_conjT_mul, padM_conjT_mul] at h
  have e1 : (Matrix.fromBlocks (M * Mᴴ) 0 0 0 - Matrix.fromBlocks (W * Wᴴ) 0 0 0 :
      Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) = Matrix.fromBlocks (M * Mᴴ - W * Wᴴ) 0 0 0 := by
    ext (i | k) (j | k') <;> simp
  have e2 : (Matrix.fromBlocks 0 0 0 (Mᴴ * M) - Matrix.fromBlocks 0 0 0 (Wᴴ * W) :
      Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) = Matrix.fromBlocks 0 0 0 (Mᴴ * M - Wᴴ * W) := by
    ext (i | k) (j | k') <;> simp
  rw [e1, e2, fn2_fromBlocks_diag, fn2_fromBlocks_diag'] at h
  exact h

theorem gram_left (D : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hV : V ∈ Matrix.unitaryGroup κ ℂ) :
    (U * D * Vᴴ) * (U * D * Vᴴ)ᴴ = U * (D * Dᴴ) * Uᴴ := by
  have hV1 : Vᴴ * V = 1 := unitary_conjT_mul hV
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ, hV1, Matrix.one_mul]

theorem gram_right (D : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (U * D * Vᴴ)ᴴ * (U * D * Vᴴ) = V * (Dᴴ * D) * Vᴴ := by
  have hU1 : Uᴴ * U = 1 := unitary_conjT_mul hU
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul]

theorem fnR_eq_trace (A : Matrix ι κ ℂ) : ((fnR A : ℝ) : ℂ) = Matrix.trace (A * Aᴴ) := by
  simp only [fnR, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj]

theorem fnR_schmidt (D : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup κ ℂ) :
    fnR (U * D * Vᴴ) = fnR D := by
  have hU1 : Uᴴ * U = 1 := unitary_conjT_mul hU
  have : ((fnR (U * D * Vᴴ) : ℝ) : ℂ) = ((fnR D : ℝ) : ℂ) := by
    rw [fnR_eq_trace, fnR_eq_trace, gram_left D U V hV, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      hU1, Matrix.one_mul]
  exact_mod_cast this

/-- **Isospectral overlap lemma for Schmidt decompositions with the same coefficient matrix**
`M = U D Vᴴ`, `W = U' D V'ᴴ` (`U, U'` unitary on `ι`, `V, V'` unitary on `κ`, `D` any rectangular
coefficient matrix; for a Schmidt decomposition `D` is a nonnegative rectangular diagonal). The two
states then have the same squared Schmidt coefficients and unrelated Schmidt bases. -/
theorem isospectral_overlap_schmidt (D : Matrix ι κ ℂ) (U U' : Matrix ι ι ℂ) (V V' : Matrix κ κ ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hU' : U' ∈ Matrix.unitaryGroup ι ℂ)
    (hV : V ∈ Matrix.unitaryGroup κ ℂ) (hV' : V' ∈ Matrix.unitaryGroup κ ℂ)
    (hD : fnR D = 1) (u : ι → ℂ) (hu : u ≠ 0) (l : ℝ)
    (hMu : ((U * D * Vᴴ) * (U * D * Vᴴ)ᴴ) *ᵥ u = (l : ℂ) • u) :
    (max (2 * l - 1) 0) ^ 2 ≤ Complex.normSq (Matrix.trace ((U * D * Vᴴ)ᴴ * (U' * D * V'ᴴ)))
      + (fn2 ((U * D * Vᴴ) * (U * D * Vᴴ)ᴴ - (U' * D * V'ᴴ) * (U' * D * V'ᴴ)ᴴ)
        + fn2 ((U * D * Vᴴ)ᴴ * (U * D * Vᴴ) - (U' * D * V'ᴴ)ᴴ * (U' * D * V'ᴴ))) / 2 := by
  have hU1 : Uᴴ * U = 1 := unitary_conjT_mul hU
  have hU2 : U * Uᴴ = 1 := unitary_mul_conjT hU
  have hU1' : U'ᴴ * U' = 1 := unitary_conjT_mul hU'
  have hU2' : U' * U'ᴴ = 1 := unitary_mul_conjT hU'
  have hV1 : Vᴴ * V = 1 := unitary_conjT_mul hV
  have hV2 : V * Vᴴ = 1 := unitary_mul_conjT hV
  have hV1' : V'ᴴ * V' = 1 := unitary_conjT_mul hV'
  have hV2' : V' * V'ᴴ = 1 := unitary_mul_conjT hV'
  have hMM := gram_left D U V hV
  have hWW := gram_left D U' V' hV'
  have hMM' := gram_right D U V hU
  have hWW' := gram_right D U' V' hU'
  have hPm : U' * Uᴴ ∈ Matrix.unitaryGroup ι ℂ :=
    Submonoid.mul_mem _ hU' (conjT_mem_unitary hU)
  have hQm : V' * Vᴴ ∈ Matrix.unitaryGroup κ ℂ :=
    Submonoid.mul_mem _ hV' (conjT_mem_unitary hV)
  refine isospectral_overlap_rect (U * D * Vᴴ) (U' * D * V'ᴴ) (U' * Uᴴ) (V' * Vᴴ) ?_ hPm hQm ?_ ?_
    u hu l hMu
  · rw [fnR_schmidt D U V hU hV, hD]
  · rw [hWW, hMM]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have hc : ∀ Y : Matrix ι ι ℂ, Uᴴ * (U * Y) = Y := fun Y => by
      rw [← Matrix.mul_assoc, hU1, Matrix.one_mul]
    simp only [hc]
  · rw [hWW', hMM']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have hc : ∀ Y : Matrix κ κ ℂ, Vᴴ * (V * Y) = Y := fun Y => by
      rw [← Matrix.mul_assoc, hV1, Matrix.one_mul]
    simp only [hc]

end Rect

/-! ### Rectangular diagonal matrices and attainment -/

section Attain

/-- The rectangular diagonal matrix `ℂ^n → ℂ^m` with diagonal entries `s 0, s 1, …` (real). -/
noncomputable def rectDiag (m n : ℕ) (s : ℕ → ℝ) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i j => if i.val = j.val then (s i.val : ℂ) else 0

theorem rectDiag_mul_conjT (m n : ℕ) (s : ℕ → ℝ) :
    rectDiag m n s * (rectDiag m n s)ᴴ =
      Matrix.diagonal (fun i : Fin m => if i.val < n then ((s i.val ^ 2 : ℝ) : ℂ) else 0) := by
  ext i i'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rectDiag, Matrix.of_apply,
    Matrix.diagonal_apply]
  by_cases hii : i = i'
  · subst hii
    by_cases h : i.val < n
    · rw [Finset.sum_eq_single (⟨i.val, h⟩ : Fin n)]
      · simp [h]; ring
      · intro j _ hj
        have : i.val ≠ j.val := fun e => hj (Fin.ext e.symm)
        simp [this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [h]
      · intro j _
        have : i.val ≠ j.val := by have := j.2; omega
        simp [this]
  · rw [Finset.sum_eq_zero]
    · simp [hii]
    · intro j _
      by_cases h1 : i.val = j.val
      · have : i'.val ≠ j.val := fun e => hii (Fin.ext (h1.trans e.symm))
        simp [this]
      · simp [h1]

theorem rectDiag_conjT_mul (m n : ℕ) (s t : ℕ → ℝ) :
    (rectDiag m n s)ᴴ * rectDiag m n t =
      Matrix.diagonal (fun j : Fin n => if j.val < m then ((s j.val * t j.val : ℝ) : ℂ) else 0) := by
  ext j j'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rectDiag, Matrix.of_apply,
    Matrix.diagonal_apply]
  by_cases hjj : j = j'
  · subst hjj
    by_cases h : j.val < m
    · rw [Finset.sum_eq_single (⟨j.val, h⟩ : Fin m)]
      · simp [h]
      · intro i _ hi
        have : i.val ≠ j.val := fun e => hi (Fin.ext e)
        simp [this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [h]
      · intro i _
        have : i.val ≠ j.val := by have := i.2; omega
        simp [this]
  · rw [Finset.sum_eq_zero]
    · simp [hjj]
    · intro i _
      by_cases h1 : i.val = j.val
      · have : i.val ≠ j'.val := fun e => hjj (Fin.ext (h1.symm.trans e))
        simp [this]
      · simp [h1]

theorem sum_fin_ite (k b : ℕ) (f : ℕ → ℝ) :
    ∑ i : Fin k, (if i.val < b then f i.val else 0) = ∑ a ∈ Finset.range (min k b), f a := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if a < b then f a else 0) k, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext a
  simp [lt_min_iff]

/-- The sign-flipped Schmidt coefficients: the first is kept, every other one changes sign. -/
def flipFirst (s : ℕ → ℝ) : ℕ → ℝ := fun a => if a = 0 then s 0 else - s a

theorem flipFirst_sq (s : ℕ → ℝ) (a : ℕ) : flipFirst s a ^ 2 = s a ^ 2 := by
  unfold flipFirst; split_ifs with h
  · rw [h]
  · ring

/-- **Attainment clause of `lem:fqe-isospectral-overlap`.** For a unit state with Schmidt coefficients
`s a` (`Σ s_a² = 1`, `λ_a = s_a²`, the first coefficient the largest, `λ₁ = s₀² ≥ 1/2`; the maximality `hmax` only records that `s₀²` is `λ₁`) in an arbitrary
Schmidt basis (`M = U D Vᴴ`, `D = rectDiag s`), the state `W = U D' Vᴴ` with every Schmidt term except
the first sign-changed has the same marginals (so the same squared Schmidt coefficients), overlap
`tr Mᴴ W = 2λ₁ - 1`, and attains the bound `(2λ₁ - 1)₊²` with equality. -/
theorem isospectral_overlap_attained (m n : ℕ) (s : ℕ → ℝ)
    (hunit : ∑ a ∈ Finset.range (min m n), s a ^ 2 = 1)
    (hmax : ∀ a < min m n, s a ^ 2 ≤ s 0 ^ 2) (hhalf : 1 / 2 ≤ s 0 ^ 2)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    let M := U * rectDiag m n s * Vᴴ
    let W := U * rectDiag m n (flipFirst s) * Vᴴ
    fnR M = 1 ∧ W * Wᴴ = M * Mᴴ ∧ Wᴴ * W = Mᴴ * M ∧
      Matrix.trace (Mᴴ * W) = ((2 * s 0 ^ 2 - 1 : ℝ) : ℂ) ∧
      Complex.normSq (Matrix.trace (Mᴴ * W))
        + (fn2 (M * Mᴴ - W * Wᴴ) + fn2 (Mᴴ * M - Wᴴ * W)) / 2
        = (max (2 * s 0 ^ 2 - 1) 0) ^ 2 := by
  intro M W
  have hU1 : Uᴴ * U = 1 := unitary_conjT_mul hU
  have hV2 : V * Vᴴ = 1 := unitary_mul_conjT hV
  obtain ⟨N, hN⟩ : ∃ N, min m n = N + 1 := by
    rcases Nat.eq_zero_or_pos (min m n) with h | h
    · rw [h] at hunit; simp at hunit
    · exact ⟨min m n - 1, by omega⟩
  -- Gram matrices
  have hDD : rectDiag m n (flipFirst s) * (rectDiag m n (flipFirst s))ᴴ =
      rectDiag m n s * (rectDiag m n s)ᴴ := by
    rw [rectDiag_mul_conjT, rectDiag_mul_conjT]
    simp only [flipFirst_sq]
  have hDD' : (rectDiag m n (flipFirst s))ᴴ * rectDiag m n (flipFirst s) =
      (rectDiag m n s)ᴴ * rectDiag m n s := by
    rw [rectDiag_conjT_mul, rectDiag_conjT_mul]
    simp only [← pow_two, flipFirst_sq]
  have hWW : W * Wᴴ = M * Mᴴ := by
    simp only [W, M]; rw [gram_left _ _ _ hV, gram_left _ _ _ hV, hDD]
  have hWW' : Wᴴ * W = Mᴴ * M := by
    simp only [W, M]; rw [gram_right _ _ _ hU, gram_right _ _ _ hU, hDD']
  -- the sums
  have hsq : ∑ a ∈ Finset.range (N + 1), s a ^ 2 = 1 := by rw [← hN]; exact hunit
  have hs1 : ∑ a ∈ Finset.range (N + 1), s a ^ 2 = ∑ a ∈ Finset.range N, s (a + 1) ^ 2 + s 0 ^ 2 :=
    Finset.sum_range_succ' _ _
  have hov : ∑ a ∈ Finset.range (min m n), s a * flipFirst s a = 2 * s 0 ^ 2 - 1 := by
    rw [hN, Finset.sum_range_succ']
    simp only [flipFirst, Nat.succ_ne_zero, ite_false, ite_true]
    have : ∑ a ∈ Finset.range N, s (a + 1) * -s (a + 1) = -∑ a ∈ Finset.range N, s (a + 1) ^ 2 := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [this]; nlinarith
  -- the three scalars
  have hfn : fnR M = 1 := by
    simp only [M]
    rw [fnR_schmidt _ _ _ hU hV]
    have h : ((fnR (rectDiag m n s) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [fnR_eq_trace, rectDiag_mul_conjT, Matrix.trace_diagonal]
      rw [← hunit, ← sum_fin_ite m n (fun a => s a ^ 2)]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    exact_mod_cast h
  have htr : Matrix.trace (Mᴴ * W) = ((2 * s 0 ^ 2 - 1 : ℝ) : ℂ) := by
    have e : Mᴴ * W = V * ((rectDiag m n s)ᴴ * rectDiag m n (flipFirst s)) * Vᴴ := by
      simp only [M, W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul]
    rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, show Vᴴ * V = 1 from unitary_conjT_mul hV,
      Matrix.one_mul, rectDiag_conjT_mul, Matrix.trace_diagonal, ← hov, min_comm,
      ← sum_fin_ite n m (fun a => s a * flipFirst s a)]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  refine ⟨hfn, hWW, hWW', htr, ?_⟩
  rw [htr, hWW, hWW', sub_self, sub_self]
  have h0 : fn2 (0 : Matrix (Fin m) (Fin m) ℂ) = 0 := by simp [fn2]
  have h0' : fn2 (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [fn2]
  rw [h0, h0', Complex.normSq_ofReal, max_eq_left (by linarith)]
  ring

end Attain


/-- info: 'FormalResearch.FourQubitEntropy.Isospectral.isospectral_overlap_rect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms isospectral_overlap_rect
/-- info: 'FormalResearch.FourQubitEntropy.Isospectral.isospectral_overlap_schmidt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms isospectral_overlap_schmidt
/-- info: 'FormalResearch.FourQubitEntropy.Isospectral.isospectral_overlap_attained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms isospectral_overlap_attained

end FormalResearch.FourQubitEntropy.Isospectral
