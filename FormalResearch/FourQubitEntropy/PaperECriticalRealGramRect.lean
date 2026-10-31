import FormalResearch.FourQubitEntropy.PaperECriticalRealGram

/-!
# Simultaneous real singular values, rectangular case (`lem:fqe-real-gram`)

Paper E, `critical_four_qubit_normal_form.tex`, Lemma `lem:fqe-real-gram`: for a complex `m × n`
matrix `Z`, the Gram matrices `Z Zᴴ` and `Zᴴ Z` are both real if and only if
`Z = O₁ D O₂ᵀ` with `O₁ ∈ O(m)`, `O₂ ∈ O(n)` real orthogonal and `D` a complex rectangular diagonal
matrix (`D i j = 0` unless `i = j` as natural numbers; `IsRectDiag`).

`PaperECriticalRealGram.lean` proves the square case (`real_gram_square`), which is all the critical
normal form needs. Here the rectangular case is derived from it by padding `Z` with zero rows and
columns to a square `N × N` matrix (`N = max m n`): the square normal form `O₁ diag(v) O₂ᵀ` has
columns `u_k`, `w_k` (for `v_k ≠ 0`) supported on the first `m` and `n` coordinates; these form
orthonormal families in `ℝ^m`, `ℝ^n`, which are completed to orthonormal bases
(`rect_complete`) and arranged so that the diagonal sits on the main diagonal.

* `real_gram_rect` (**proved**): the iff, in the paper's wording, for `Z : Matrix (Fin m) (Fin n) ℂ`.
* The orthogonal factors are in `O(m)`, `O(n)` as in the lemma; the `SO` refinement used for the
  square normal form is `real_gram_square_SO`.

No hypotheses; no `sorry`.
-/

open scoped Matrix ComplexConjugate

namespace FormalResearch.FourQubitEntropy.PaperECritical

/-- A rectangular matrix is diagonal when every off-diagonal entry (`i ≠ j` as naturals) vanishes. -/
def IsRectDiag {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  ∀ i : Fin m, ∀ j : Fin n, i.val ≠ j.val → D i j = 0

/-- Entrywise real-to-complex cast of a real matrix. -/
noncomputable def rcR {α β : Type*} (O : Matrix α β ℝ) : Matrix α β ℂ := O.map (fun x : ℝ => (x : ℂ))

theorem rcR_apply {α β : Type*} (O : Matrix α β ℝ) (i : α) (j : β) : rcR O i j = (O i j : ℂ) := rfl

/-- Extending an orthonormal family of `r` vectors in `ℝ^m` to an orthonormal basis, with the
family occupying the first `r` coordinates. -/
theorem orth_extend (m r : ℕ) (f : Fin r → Fin m → ℝ)
    (hf : ∀ a b, ∑ i, f a i * f b i = if a = b then 1 else 0) :
    ∃ hr : r ≤ m, ∃ b : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)),
      ∀ (a : Fin r) (i : Fin m), b ⟨a.val, lt_of_lt_of_le a.2 hr⟩ i = f a i := by
  let F : Fin r → EuclideanSpace ℝ (Fin m) := fun a => WithLp.toLp 2 (f a)
  have hon : Orthonormal ℝ F := by
    rw [orthonormal_iff_ite]
    intro a b
    simp only [F, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
    rw [← hf a b]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hr : r ≤ m := by
    have := hon.linearIndependent.fintype_card_le_finrank
    simpa using this
  refine ⟨hr, ?_⟩
  let v' : Fin m → EuclideanSpace ℝ (Fin m) := fun i => if h : i.val < r then F ⟨i.val, h⟩ else 0
  let s : Set (Fin m) := {i | i.val < r}
  have hon' : Orthonormal ℝ (s.domRestrict v') := by
    have : s.domRestrict v' = F ∘ (fun x : s => (⟨x.1.val, x.2⟩ : Fin r)) := by
      funext x
      have hx : x.1.val < r := x.2
      simp [v', hx]
    rw [this]
    refine hon.comp _ ?_
    intro x y hxy
    apply Subtype.ext
    apply Fin.ext
    simpa using congrArg Fin.val hxy
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin m)) hon'
  refine ⟨b, fun a i => ?_⟩
  have hmem : (⟨a.val, lt_of_lt_of_le a.2 hr⟩ : Fin m) ∈ s := a.2
  have := hb _ hmem
  rw [this]
  simp [v', a.2, F]

/-- Rectangular completion: orthonormal families `f` in `ℝ^m` and `g` in `ℝ^n` indexed by `Fin r`
and weights `v` give a rectangular diagonal normal form with `O₁ D O₂ᵀ = Σ_a v_a f_a g_aᵀ`. -/
theorem rect_complete (m n r : ℕ) (f : Fin r → Fin m → ℝ) (g : Fin r → Fin n → ℝ) (v : Fin r → ℂ)
    (hf : ∀ a b, ∑ i, f a i * f b i = if a = b then 1 else 0)
    (hg : ∀ a b, ∑ j, g a j * g b j = if a = b then 1 else 0) :
    ∃ (O₁ : Matrix (Fin m) (Fin m) ℝ) (O₂ : Matrix (Fin n) (Fin n) ℝ) (D : Matrix (Fin m) (Fin n) ℂ),
      O₁ᵀ * O₁ = 1 ∧ O₂ᵀ * O₂ = 1 ∧ IsRectDiag D ∧
      ∀ i j, (rcR O₁ * D * (rcR O₂)ᵀ) i j = ∑ a, v a * (f a i : ℂ) * (g a j : ℂ) := by
  obtain ⟨hrm, b₁, hb₁⟩ := orth_extend m r f hf
  obtain ⟨hrn, b₂, hb₂⟩ := orth_extend n r g hg
  let D : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun a c =>
    if h : a.val = c.val ∧ a.val < r then v ⟨a.val, h.2⟩ else 0
  refine ⟨Matrix.of fun i k => b₁ k i, Matrix.of fun j k => b₂ k j, D, basisMatrix_orth b₁,
    basisMatrix_orth b₂, ?_, ?_⟩
  · intro a c hac
    simp [D, hac]
  · intro i j
    have h1 : ∀ a : Fin m, ∑ c : Fin n, (b₁ a i : ℂ) * D a c * (b₂ c j : ℂ) =
        if h : a.val < r then (b₁ a i : ℂ) * v ⟨a.val, h⟩ * (b₂ ⟨a.val, lt_of_lt_of_le h hrn⟩ j : ℂ)
        else 0 := by
      intro a
      by_cases h : a.val < r
      · rw [Finset.sum_eq_single (⟨a.val, lt_of_lt_of_le h hrn⟩ : Fin n)]
        · simp [D, h]
        · intro c _ hc
          have : a.val ≠ c.val := fun e => hc (Fin.ext e.symm)
          simp [D, this]
        · simp
      · rw [Finset.sum_eq_zero]
        · simp [h]
        · intro c _
          simp [D, h]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, rcR_apply, Matrix.of_apply]
    have : ∀ a : Fin m, ∑ c : Fin n, ((b₁ a i : ℝ) : ℂ) * D a c * ((b₂ c j : ℝ) : ℂ) =
        ∑ c : Fin n, ((b₁ a i : ℝ) : ℂ) * D a c * ((b₂ c j : ℝ) : ℂ) := fun _ => rfl
    calc ∑ c : Fin n, (∑ a : Fin m, ((b₁ a i : ℝ) : ℂ) * D a c) * ((b₂ c j : ℝ) : ℂ)
        = ∑ a : Fin m, ∑ c : Fin n, ((b₁ a i : ℝ) : ℂ) * D a c * ((b₂ c j : ℝ) : ℂ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ a : Fin m, (if h : a.val < r then
            (b₁ a i : ℂ) * v ⟨a.val, h⟩ * (b₂ ⟨a.val, lt_of_lt_of_le h hrn⟩ j : ℂ) else 0) :=
          Finset.sum_congr rfl fun a _ => h1 a
      _ = ∑ a : Fin r, v a * (f a i : ℂ) * (g a j : ℂ) := by
          symm
          refine Fintype.sum_of_injective (Fin.castLE hrm) (Fin.castLE_injective hrm) _ _ ?_ ?_
          · intro a ha
            have : ¬ a.val < r := by
              intro h
              exact ha ⟨⟨a.val, h⟩, Fin.ext rfl⟩
            simp [this]
          · intro a
            have e1 := hb₁ a i
            have e2 := hb₂ a j
            simp only [Fin.castLE, a.2, dite_true]
            rw [e1, e2]
            ring

/-! ### The converse direction -/

theorem rcR_mul {α β γ : Type*} [Fintype β] (A : Matrix α β ℝ) (B : Matrix β γ ℝ) :
    rcR (A * B) = rcR A * rcR B := by
  ext i j
  simp [rcR_apply, Matrix.mul_apply]

theorem rcR_transpose {α β : Type*} (A : Matrix α β ℝ) : (rcR A)ᵀ = rcR Aᵀ := by
  ext i j; simp [rcR_apply]

theorem rcR_conjTranspose {α β : Type*} (A : Matrix α β ℝ) : (rcR A)ᴴ = rcR Aᵀ := by
  ext i j; simp [rcR_apply, Matrix.conjTranspose_apply]

theorem rcR_one {α : Type*} [DecidableEq α] : rcR (1 : Matrix α α ℝ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [rcR_apply, Matrix.one_apply, h]

theorem im_conj_real {α β γ δ : Type*} [Fintype β] [Fintype γ] (A : Matrix α β ℝ) (B : Matrix δ γ ℝ)
    (X : Matrix β γ ℂ) (hX : ∀ a b, (X a b).im = 0) (i : α) (j : δ) :
    ((rcR A * X * (rcR B)ᵀ) i j).im = 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rcR_apply, Finset.sum_mul, Complex.im_sum]
  refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun b _ => ?_
  simp [Complex.mul_im, hX b c]

theorem rectDiag_gram_left {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℂ) (hD : IsRectDiag D)
    (a a' : Fin m) : ((D * Dᴴ) a a').im = 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.im_sum]
  by_cases h : a = a'
  · subst h
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Complex.star_def, Complex.mul_conj]; simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h1 : a.val = c.val
    · have : a'.val ≠ c.val := fun e => h (Fin.ext (h1.trans e.symm))
      simp [hD a' c this]
    · simp [hD a c h1]

theorem rectDiag_gram_right {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℂ) (hD : IsRectDiag D)
    (c c' : Fin n) : ((Dᴴ * D) c c').im = 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.im_sum]
  by_cases h : c = c'
  · subst h
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.ofReal_im _
  · refine Finset.sum_eq_zero fun a _ => ?_
    by_cases h1 : a.val = c.val
    · have : a.val ≠ c'.val := fun e => h (Fin.ext (h1.symm.trans e))
      have h0 := hD a c' this
      simp [h0]
    · have h0 := hD a c h1
      simp [h0]

theorem rcR_transpose_conjTranspose {α β : Type*} (A : Matrix α β ℝ) : ((rcR A)ᵀ)ᴴ = rcR A := by
  ext i j; simp [rcR_apply, Matrix.conjTranspose_apply]

theorem real_gram_rect_of_normal_form {m n : ℕ} (O₁ : Matrix (Fin m) (Fin m) ℝ)
    (O₂ : Matrix (Fin n) (Fin n) ℝ) (D : Matrix (Fin m) (Fin n) ℂ) (h1 : O₁ᵀ * O₁ = 1)
    (h2 : O₂ᵀ * O₂ = 1) (hD : IsRectDiag D) :
    (∀ i j, (((rcR O₁ * D * (rcR O₂)ᵀ) * (rcR O₁ * D * (rcR O₂)ᵀ)ᴴ) i j).im = 0) ∧
    (∀ i j, ((((rcR O₁ * D * (rcR O₂)ᵀ)ᴴ * (rcR O₁ * D * (rcR O₂)ᵀ)) i j).im = 0)) := by
  have hO2 : (rcR O₂)ᵀ * rcR O₂ = 1 := by rw [rcR_transpose, ← rcR_mul, h2, rcR_one]
  have hO1 : (rcR O₁)ᵀ * rcR O₁ = 1 := by rw [rcR_transpose, ← rcR_mul, h1, rcR_one]
  have k2 : ∀ X : Matrix (Fin n) (Fin m) ℂ, (rcR O₂)ᵀ * (rcR O₂ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hO2, Matrix.one_mul]
  have k1 : ∀ X : Matrix (Fin m) (Fin n) ℂ, (rcR O₁)ᵀ * (rcR O₁ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hO1, Matrix.one_mul]
  have c1 : (rcR O₁)ᴴ = (rcR O₁)ᵀ := by rw [rcR_conjTranspose, rcR_transpose]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (rcR O₁ * D * (rcR O₂)ᵀ) * (rcR O₁ * D * (rcR O₂)ᵀ)ᴴ =
        rcR O₁ * (D * Dᴴ) * (rcR O₁)ᵀ := by
      simp only [Matrix.conjTranspose_mul, rcR_transpose_conjTranspose, c1, Matrix.mul_assoc]
      rw [k2]
    rw [this]
    exact im_conj_real _ _ _ (rectDiag_gram_left D hD) i j
  · have : (rcR O₁ * D * (rcR O₂)ᵀ)ᴴ * (rcR O₁ * D * (rcR O₂)ᵀ) =
        rcR O₂ * (Dᴴ * D) * (rcR O₂)ᵀ := by
      simp only [Matrix.conjTranspose_mul, rcR_transpose_conjTranspose, c1, Matrix.mul_assoc]
      rw [k1]
    rw [this]
    exact im_conj_real _ _ _ (rectDiag_gram_right D hD) i j

/-! ### The forward direction, by padding to the square case -/

theorem real_gram_rect_exists {m n : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ)
    (h1 : ∀ i j, ((Z * Zᴴ) i j).im = 0) (h2 : ∀ i j, ((Zᴴ * Z) i j).im = 0) :
    ∃ (O₁ : Matrix (Fin m) (Fin m) ℝ) (O₂ : Matrix (Fin n) (Fin n) ℝ) (D : Matrix (Fin m) (Fin n) ℂ),
      O₁ᵀ * O₁ = 1 ∧ O₂ᵀ * O₂ = 1 ∧ IsRectDiag D ∧ Z = rcR O₁ * D * (rcR O₂)ᵀ := by
  classical
  obtain ⟨N, hN⟩ : ∃ N, N = max m n := ⟨_, rfl⟩
  have hm : m ≤ N := hN ▸ le_max_left _ _
  have hn : n ≤ N := hN ▸ le_max_right _ _
  let Z' : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j =>
    if h : i.val < m ∧ j.val < n then Z ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0
  have hZc : ∀ i j, Z' (Fin.castLE hm i) (Fin.castLE hn j) = Z i j := by
    intro i j; simp [Z', i.2, j.2]
  have hrow : ∀ (i : Fin N) j, m ≤ i.val → Z' i j = 0 := by
    intro i j hi; simp [Z', not_lt.mpr hi]
  have hcol : ∀ i (j : Fin N), n ≤ j.val → Z' i j = 0 := by
    intro i j hj; simp [Z', not_lt.mpr hj]
  -- Gram matrices of the padding
  have g1 : ∀ i i', (Z' * Z'ᴴ) i i' =
      if h : i.val < m ∧ i'.val < m then (Z * Zᴴ) ⟨i.val, h.1⟩ ⟨i'.val, h.2⟩ else 0 := by
    intro i i'
    by_cases hi : i.val < m
    · by_cases hi' : i'.val < m
      · rw [dif_pos ⟨hi, hi'⟩]
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
        symm
        refine Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ _ ?_ ?_
        · intro j hj
          have : ¬ j.val < n := fun h => hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
          simp [Z', this]
        · intro j'
          simp [Z', hi, hi', j'.2]
      · rw [dif_neg (fun h => hi' h.2)]
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
        exact Finset.sum_eq_zero fun j _ => by simp [Z', hi']
    · rw [dif_neg (fun h => hi h.1)]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      exact Finset.sum_eq_zero fun j _ => by simp [Z', hi]
  have g2 : ∀ j j', (Z'ᴴ * Z') j j' =
      if h : j.val < n ∧ j'.val < n then (Zᴴ * Z) ⟨j.val, h.1⟩ ⟨j'.val, h.2⟩ else 0 := by
    intro j j'
    by_cases hj : j.val < n
    · by_cases hj' : j'.val < n
      · rw [dif_pos ⟨hj, hj'⟩]
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
        symm
        refine Fintype.sum_of_injective (Fin.castLE hm) (Fin.castLE_injective hm) _ _ ?_ ?_
        · intro i hi
          have : ¬ i.val < m := fun h => hi ⟨⟨i.val, h⟩, Fin.ext rfl⟩
          simp [Z', this]
        · intro i'
          simp [Z', hj, hj', i'.2]
      · rw [dif_neg (fun h => hj' h.2)]
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
        exact Finset.sum_eq_zero fun i _ => by simp [Z', hj']
    · rw [dif_neg (fun h => hj h.1)]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      exact Finset.sum_eq_zero fun i _ => by simp [Z', hj]
  have h1' : ∀ i i', ((Z' * Z'ᴴ) i i').im = 0 := by
    intro i i'; rw [g1]; split_ifs
    · exact h1 _ _
    · simp
  have h2' : ∀ j j', ((Z'ᴴ * Z') j j').im = 0 := by
    intro j j'; rw [g2]; split_ifs
    · exact h2 _ _
    · simp
  obtain ⟨O₁, O₂, v, hO1, hO2, hZ'⟩ := real_gram_square Z' h1' h2'
  have hent : ∀ i j, Z' i j = ∑ k, (O₁ i k : ℂ) * v k * (O₂ j k : ℂ) := by
    intro i j
    rw [hZ', Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal]
    simp [rc_apply]
  have hc2 : (rc O₂)ᵀ * rc O₂ = 1 := by rw [rc_transpose, ← map_mul, hO2, map_one]
  have hc1 : (rc O₁)ᵀ * rc O₁ = 1 := by rw [rc_transpose, ← map_mul, hO1, map_one]
  have eA : Z' * rc O₂ = rc O₁ * Matrix.diagonal v := by
    rw [hZ', Matrix.mul_assoc, hc2, Matrix.mul_one]
  have eB : (rc O₁)ᵀ * Z' = Matrix.diagonal v * (rc O₂)ᵀ := by
    rw [hZ', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hc1, Matrix.one_mul]
  -- support of the singular vectors
  have supA : ∀ k, v k ≠ 0 → ∀ i : Fin N, m ≤ i.val → O₁ i k = 0 := by
    intro k hk i hi
    have := congrFun (congrFun eA i) k
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at this
    rw [Finset.sum_eq_zero (fun j _ => by rw [hrow i j hi, zero_mul])] at this
    have h0 : (O₁ i k : ℂ) * v k = 0 := by simpa [rc_apply] using this.symm
    exact_mod_cast (mul_eq_zero.mp h0).resolve_right hk
  have supB : ∀ k, v k ≠ 0 → ∀ j : Fin N, n ≤ j.val → O₂ j k = 0 := by
    intro k hk j hj
    have := congrFun (congrFun eB k) j
    rw [Matrix.mul_apply, Matrix.diagonal_mul] at this
    rw [Finset.sum_eq_zero (fun i _ => by rw [hcol i j hj, mul_zero])] at this
    have h0 : v k * (O₂ j k : ℂ) = 0 := by simpa [rc_apply] using this.symm
    exact_mod_cast (mul_eq_zero.mp h0).resolve_left hk
  -- the families
  let S := {k : Fin N // v k ≠ 0}
  let r := Fintype.card S
  let e : S ≃ Fin r := Fintype.equivFin S
  let f : Fin r → Fin m → ℝ := fun a i => O₁ (Fin.castLE hm i) (e.symm a).1
  let g : Fin r → Fin n → ℝ := fun a j => O₂ (Fin.castLE hn j) (e.symm a).1
  let w : Fin r → ℂ := fun a => v (e.symm a).1
  have orth1 : ∀ k l : Fin N, v k ≠ 0 → v l ≠ 0 →
      ∑ i : Fin m, O₁ (Fin.castLE hm i) k * O₁ (Fin.castLE hm i) l = if k = l then 1 else 0 := by
    intro k l hk hl
    have h := congrFun (congrFun hO1 k) l
    rw [Matrix.mul_apply] at h
    simp only [Matrix.transpose_apply, Matrix.one_apply] at h
    rw [← h]
    refine Fintype.sum_of_injective (Fin.castLE hm) (Fin.castLE_injective hm) _ _ ?_ ?_
    · intro i hi
      have : m ≤ i.val := by
        by_contra hlt
        exact hi ⟨⟨i.val, not_le.mp hlt⟩, Fin.ext rfl⟩
      simp [supA k hk i this]
    · intro i; rfl
  have orth2 : ∀ k l : Fin N, v k ≠ 0 → v l ≠ 0 →
      ∑ j : Fin n, O₂ (Fin.castLE hn j) k * O₂ (Fin.castLE hn j) l = if k = l then 1 else 0 := by
    intro k l hk hl
    have h := congrFun (congrFun hO2 k) l
    rw [Matrix.mul_apply] at h
    simp only [Matrix.transpose_apply, Matrix.one_apply] at h
    rw [← h]
    refine Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ _ ?_ ?_
    · intro j hj
      have : n ≤ j.val := by
        by_contra hlt
        exact hj ⟨⟨j.val, not_le.mp hlt⟩, Fin.ext rfl⟩
      simp [supB k hk j this]
    · intro j; rfl
  have hf : ∀ a b, ∑ i, f a i * f b i = if a = b then 1 else 0 := by
    intro a b
    have := orth1 (e.symm a).1 (e.symm b).1 (e.symm a).2 (e.symm b).2
    simp only [f]
    rw [this]
    by_cases hab : a = b
    · simp [hab]
    · have : (e.symm a).1 ≠ (e.symm b).1 := fun h => hab (e.symm.injective (Subtype.ext h))
      simp [this, hab]
  have hg : ∀ a b, ∑ j, g a j * g b j = if a = b then 1 else 0 := by
    intro a b
    have := orth2 (e.symm a).1 (e.symm b).1 (e.symm a).2 (e.symm b).2
    simp only [g]
    rw [this]
    by_cases hab : a = b
    · simp [hab]
    · have : (e.symm a).1 ≠ (e.symm b).1 := fun h => hab (e.symm.injective (Subtype.ext h))
      simp [this, hab]
  obtain ⟨P₁, P₂, D, hP1, hP2, hD, hPD⟩ := rect_complete m n r f g w hf hg
  refine ⟨P₁, P₂, D, hP1, hP2, hD, ?_⟩
  ext i j
  rw [hPD i j, ← hZc i j, hent]
  have hsub : ∑ k : Fin N, (O₁ (Fin.castLE hm i) k : ℂ) * v k * (O₂ (Fin.castLE hn j) k : ℂ)
      = ∑ s : S, (O₁ (Fin.castLE hm i) s.1 : ℂ) * v s.1 * (O₂ (Fin.castLE hn j) s.1 : ℂ) := by
    calc _ = ∑ k ∈ Finset.univ.filter (fun k => v k ≠ 0),
          (O₁ (Fin.castLE hm i) k : ℂ) * v k * (O₂ (Fin.castLE hn j) k : ℂ) := by
          symm
          refine Finset.sum_filter_of_ne fun k _ hk => ?_
          by_contra h
          exact hk (by simp [h])
      _ = _ := Finset.sum_subtype _ (by simp) _
  rw [hsub, ← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [w, f, g]
  ring

/-- **`lem:fqe-real-gram`** (simultaneous real singular values), rectangular case as stated in the
paper: for a complex `m × n` matrix `Z`, the Gram matrices `Z Zᴴ` and `Zᴴ Z` are real iff
`Z = O₁ D O₂ᵀ` with `O₁ ∈ O(m)`, `O₂ ∈ O(n)` real orthogonal and `D` complex rectangular
diagonal. -/
theorem real_gram_rect {m n : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) :
    ((∀ i j, ((Z * Zᴴ) i j).im = 0) ∧ (∀ i j, ((Zᴴ * Z) i j).im = 0)) ↔
      ∃ (O₁ : Matrix (Fin m) (Fin m) ℝ) (O₂ : Matrix (Fin n) (Fin n) ℝ)
        (D : Matrix (Fin m) (Fin n) ℂ),
        O₁ᵀ * O₁ = 1 ∧ O₂ᵀ * O₂ = 1 ∧ IsRectDiag D ∧ Z = rcR O₁ * D * (rcR O₂)ᵀ := by
  constructor
  · rintro ⟨h1, h2⟩
    exact real_gram_rect_exists Z h1 h2
  · rintro ⟨O₁, O₂, D, h1, h2, hD, rfl⟩
    exact real_gram_rect_of_normal_form O₁ O₂ D h1 h2 hD

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.real_gram_rect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms real_gram_rect

end FormalResearch.FourQubitEntropy.PaperECritical
