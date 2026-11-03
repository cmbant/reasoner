module

/-
WoronowiczBase.lean

Tools for Woronowicz's theorem on ℂ² ⊗ ℂᵐ: block matrices, local operations, and the step from a
normal dilation to a separable decomposition (Woerdeman, "The separability problem and normal
completions", Linear Algebra Appl. 376 (2004); the easy direction).
-/
public import MathLab.ChainTheory.Stormer
public import MathLab.Positivity.NormalSpectral
public import MathLab.Positivity.NormalCompletion

@[expose] public section

open Matrix ComplexOrder
open scoped Kronecker

noncomputable section

namespace ChainWoronowicz

open ChoiDark ChainReadCap ChainDuality ChainStormer

variable {m : ℕ}

/-! ## Separable operators form a cone -/

theorem isSeparable_zero {n m : ℕ} : IsSeparable (0 : Mat n m) :=
  ⟨0, Fin.elim0, Fin.elim0, by simp⟩

theorem isSeparable_add {n m : ℕ} {ρ₁ ρ₂ : Mat n m} (h₁ : IsSeparable ρ₁) (h₂ : IsSeparable ρ₂) :
    IsSeparable (ρ₁ + ρ₂) := by
  obtain ⟨r₁, x₁, y₁, rfl⟩ := h₁
  obtain ⟨r₂, x₂, y₂, rfl⟩ := h₂
  have := isSeparable_of_fintype (ι := Fin r₁ ⊕ Fin r₂) (Sum.elim x₁ x₂) (Sum.elim y₁ y₂)
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using this

theorem isSeparable_smul {n m : ℕ} {ρ : Mat n m} (h : IsSeparable ρ) {t : ℝ} (ht : 0 ≤ t) :
    IsSeparable (t • ρ) := by
  obtain ⟨r, x, y, rfl⟩ := h
  refine ⟨r, fun s => ((Real.sqrt t : ℝ) : ℂ) • x s, y, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ext i j
  have hs : ((Real.sqrt t : ℝ) : ℂ) * star ((Real.sqrt t : ℝ) : ℂ) = ((t : ℝ) : ℂ) := by
    rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt ht]
  simp only [Matrix.smul_apply, vecMulVec_apply, prodVec, Pi.smul_apply, smul_eq_mul, Pi.star_apply,
    star_mul', Complex.real_smul]
  rw [← hs]
  ring

theorem isSeparable_sum {n m : ℕ} {ι : Type*} (s : Finset ι) (ρ : ι → Mat n m)
    (h : ∀ i ∈ s, IsSeparable (ρ i)) : IsSeparable (∑ i ∈ s, ρ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSeparable_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSeparable_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## Block matrices on ℂ² ⊗ ℂᵐ -/

/-- The block matrix `[[P, Q], [R, S]]`: the block `(a, b)` sits at rows `(a, ·)` and columns `(b, ·)`. -/
def blk (P Q R S : Matrix (Fin m) (Fin m) ℂ) : Mat 2 m :=
  fun x y => (![![P, Q], ![R, S]] x.1 y.1) x.2 y.2

/-- The block `(a, b)` of an operator on `ℂ² ⊗ ℂᵐ`. -/
def blkOf (ρ : Mat 2 m) (a b : Fin 2) : Matrix (Fin m) (Fin m) ℂ := fun k l => ρ (a, k) (b, l)

theorem blk_blkOf (ρ : Mat 2 m) :
    blk (blkOf ρ 0 0) (blkOf ρ 0 1) (blkOf ρ 1 0) (blkOf ρ 1 1) = ρ := by
  ext ⟨a, k⟩ ⟨b, l⟩
  fin_cases a <;> fin_cases b <;> rfl

@[simp] theorem blkOf_blk (P Q R S : Matrix (Fin m) (Fin m) ℂ) :
    blkOf (blk P Q R S) 0 0 = P ∧ blkOf (blk P Q R S) 0 1 = Q ∧ blkOf (blk P Q R S) 1 0 = R ∧
      blkOf (blk P Q R S) 1 1 = S :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem blk_add (P Q R S P' Q' R' S' : Matrix (Fin m) (Fin m) ℂ) :
    blk P Q R S + blk P' Q' R' S' = blk (P + P') (Q + Q') (R + R') (S + S') := by
  ext ⟨a, k⟩ ⟨b, l⟩
  fin_cases a <;> fin_cases b <;> rfl

theorem blk_mul (P Q R S P' Q' R' S' : Matrix (Fin m) (Fin m) ℂ) :
    blk P Q R S * blk P' Q' R' S' =
      blk (P * P' + Q * R') (P * Q' + Q * S') (R * P' + S * R') (R * Q' + S * S') := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp only [blk, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, 
    ]
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply]

theorem blk_conjTranspose (P Q R S : Matrix (Fin m) (Fin m) ℂ) :
    (blk P Q R S)ᴴ = blk Pᴴ Rᴴ Qᴴ Sᴴ := by
  ext ⟨a, k⟩ ⟨b, l⟩
  fin_cases a <;> fin_cases b <;> rfl

theorem pt_blk (P Q R S : Matrix (Fin m) (Fin m) ℂ) : pt (blk P Q R S) = blk Pᵀ Qᵀ Rᵀ Sᵀ := by
  ext ⟨a, k⟩ ⟨b, l⟩
  fin_cases a <;> fin_cases b <;> rfl

/-- A rank-one product projector as a block matrix. -/
theorem prodVec_proj_blk (g : Fin 2 → ℂ) (w : Fin m → ℂ) :
    vecMulVec (prodVec g w) (star (prodVec g w)) =
      blk ((g 0 * star (g 0)) • vecMulVec w (star w)) ((g 0 * star (g 1)) • vecMulVec w (star w))
        ((g 1 * star (g 0)) • vecMulVec w (star w)) ((g 1 * star (g 1)) • vecMulVec w (star w)) := by
  ext ⟨a, k⟩ ⟨b, l⟩
  fin_cases a <;> fin_cases b <;>
    simp [blk, vecMulVec_apply, prodVec, Matrix.smul_apply, star_mul'] <;> ring

/-- A positive matrix in the corner `(1, 1)` is separable. -/
theorem isSeparable_blk_corner {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsPSD P) :
    IsSeparable (blk 0 0 0 P) := by
  obtain ⟨F, rfl⟩ := hP.gram
  have := isSeparable_of_fintype (fun _ : Fin m => (![0, 1] : Fin 2 → ℂ)) (fun i => star (F i))
  convert this using 1
  ext ⟨a, k⟩ ⟨b, l⟩
  simp only [Matrix.sum_apply, vecMulVec_apply, prodVec, Pi.star_apply, star_mul', star_star]
  fin_cases a <;> fin_cases b <;>
    simp [blk, Matrix.mul_apply, conjTranspose_apply, mul_comm]

/-! ## From a normal dilation to a separable decomposition -/

theorem blk_sum {ι : Type*} (t : Finset ι) (P Q R S : ι → Matrix (Fin m) (Fin m) ℂ) :
    ∑ j ∈ t, blk (P j) (Q j) (R j) (S j) = blk (∑ j ∈ t, P j) (∑ j ∈ t, Q j) (∑ j ∈ t, R j) (∑ j ∈ t, S j) := by
  ext ⟨a, k⟩ ⟨b, l⟩
  fin_cases a <;> fin_cases b <;> simp [blk, Matrix.sum_apply]

/-- `Σ_j c_j |w_j⟩⟨w_j|` over the columns `w_j` of `W` is `W diag(c) Wᴴ`. -/
theorem sum_smul_vecMulVec_cols {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix (Fin m) ι ℂ)
    (c : ι → ℂ) :
    ∑ j, c j • vecMulVec (fun i => W i j) (star fun i => W i j) = W * diagonal c * Wᴴ := by
  ext i l
  rw [Matrix.mul_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul,
    mul_diagonal, conjTranspose_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Woerdeman's criterion, the easy direction**: if `N` is a normal matrix on `ℂᵐ ⊕ ℂᵏ` with corner
`B` and `C ⪰ (N Nᴴ)₁₁`, then `[[1, B], [Bᴴ, C]]` is separable. The eigenvectors `u_j` of `N`, cut to
their first `m` coordinates `w_j`, give `[[1, B], [Bᴴ, (N Nᴴ)₁₁]] = Σ_j |(1, λ̄_j)⟩⟨(1, λ̄_j)| ⊗ |w_j⟩⟨w_j|`. -/
theorem sep_of_normal_dilation {κ : Type*} [Fintype κ] [DecidableEq κ]
    (N : Matrix (Fin m ⊕ κ) (Fin m ⊕ κ) ℂ) (hN : Nᴴ * N = N * Nᴴ) (C : Matrix (Fin m) (Fin m) ℂ)
    (hC : IsPSD (C - (N * Nᴴ).toBlocks₁₁)) :
    IsSeparable (blk 1 N.toBlocks₁₁ (N.toBlocks₁₁)ᴴ C) := by
  obtain ⟨U, d, hUU, hUU', hNU⟩ := MathLab.normal_spectral N hN
  set W : Matrix (Fin m) (Fin m ⊕ κ) ℂ := of fun i j => U (Sum.inl i) j with hW
  have hcorner : ∀ f : Fin m ⊕ κ → ℂ, (U * diagonal f * Uᴴ).toBlocks₁₁ = W * diagonal f * Wᴴ := by
    intro f
    ext i l
    simp only [toBlocks₁₁, of_apply]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [mul_diagonal, conjTranspose_apply, hW, of_apply]
  have hW1 : W * Wᴴ = 1 := by
    ext i l
    have h := congrFun (congrFun hUU' (Sum.inl i)) (Sum.inl l)
    simp only [Matrix.mul_apply, conjTranspose_apply, one_apply, Sum.inl.injEq] at h
    simp only [Matrix.mul_apply, conjTranspose_apply, one_apply, hW, of_apply, h]
  have hNN : N * Nᴴ = U * diagonal (fun j => d j * star (d j)) * Uᴴ := by
    have h : U * diagonal d * Uᴴ * (U * diagonal d * Uᴴ)ᴴ =
        U * (diagonal d * (Uᴴ * U) * (diagonal d)ᴴ) * Uᴴ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
    rw [hNU, h, hUU, mul_one, diagonal_conjTranspose, diagonal_mul_diagonal]
    rfl
  have hB : N.toBlocks₁₁ = W * diagonal d * Wᴴ := by rw [← hcorner, ← hNU]
  have hBH : (N.toBlocks₁₁)ᴴ = W * diagonal (fun j => star (d j)) * Wᴴ := by
    rw [hB, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
      ← Matrix.mul_assoc]
    rfl
  have hC1 : (N * Nᴴ).toBlocks₁₁ = W * diagonal (fun j => d j * star (d j)) * Wᴴ := by
    rw [hNN, hcorner]
  have hdec : blk 1 N.toBlocks₁₁ (N.toBlocks₁₁)ᴴ (N * Nᴴ).toBlocks₁₁ =
      ∑ j, vecMulVec (prodVec ![1, star (d j)] (fun i => W i j))
        (star (prodVec ![1, star (d j)] (fun i => W i j))) := by
    simp only [prodVec_proj_blk, Matrix.cons_val_zero, Matrix.cons_val_one, 
      star_one, star_star, one_mul, mul_one]
    rw [blk_sum, sum_smul_vecMulVec_cols, sum_smul_vecMulVec_cols, sum_smul_vecMulVec_cols,
      sum_smul_vecMulVec_cols, diagonal_one, Matrix.mul_one, hW1, ← hB, ← hBH, hC1]
    have hc : (fun j => d j * star (d j)) = (fun j => star (d j) * d j) :=
      funext fun j => mul_comm _ _
    rw [hc]
  have hsplit : blk 1 N.toBlocks₁₁ (N.toBlocks₁₁)ᴴ C =
      blk 1 N.toBlocks₁₁ (N.toBlocks₁₁)ᴴ (N * Nᴴ).toBlocks₁₁ +
        blk 0 0 0 (C - (N * Nᴴ).toBlocks₁₁) := by
    rw [blk_add]
    simp
  rw [hsplit, hdec]
  exact isSeparable_add (isSeparable_of_fintype _ _) (isSeparable_blk_corner hC)

/-! ## Local operations `ρ ↦ (G ⊗ M) ρ (G ⊗ M)ᴴ` -/

section LocalOps

variable {n n' n'' m' m'' : ℕ}

/-- Congruence preserves positivity. -/
theorem isPSD_conj {ι ι' : Type*} [Fintype ι] [Fintype ι'] {P : Matrix ι ι ℂ} (hP : IsPSD P)
    (X : Matrix ι' ι ℂ) : IsPSD (X * P * Xᴴ) := by
  intro v
  have e : star v ⬝ᵥ ((X * P * Xᴴ) *ᵥ v) = star (Xᴴ *ᵥ v) ⬝ᵥ (P *ᵥ (Xᴴ *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, star_mulVec,
      conjTranspose_conjTranspose]
  rw [e]
  exact hP _

/-- The local operation `ρ ↦ (G ⊗ M) ρ (G ⊗ M)ᴴ`. -/
def lop (G : Matrix (Fin n') (Fin n) ℂ) (M : Matrix (Fin m') (Fin m) ℂ) (ρ : Mat n m) : Mat n' m' :=
  (G ⊗ₖ M) * ρ * (G ⊗ₖ M)ᴴ

theorem lop_add (G : Matrix (Fin n') (Fin n) ℂ) (M : Matrix (Fin m') (Fin m) ℂ) (ρ₁ ρ₂ : Mat n m) :
    lop G M (ρ₁ + ρ₂) = lop G M ρ₁ + lop G M ρ₂ := by
  simp only [lop, Matrix.mul_add, Matrix.add_mul]

theorem lop_smul (G : Matrix (Fin n') (Fin n) ℂ) (M : Matrix (Fin m') (Fin m) ℂ) (c : ℂ)
    (ρ : Mat n m) : lop G M (c • ρ) = c • lop G M ρ := by
  simp only [lop, Matrix.mul_smul, Matrix.smul_mul]

theorem lop_zero (G : Matrix (Fin n') (Fin n) ℂ) (M : Matrix (Fin m') (Fin m) ℂ) :
    lop G M (0 : Mat n m) = 0 := by
  simp only [lop, Matrix.mul_zero, Matrix.zero_mul]

theorem lop_lop (G : Matrix (Fin n'') (Fin n') ℂ) (M : Matrix (Fin m'') (Fin m') ℂ)
    (G' : Matrix (Fin n') (Fin n) ℂ) (M' : Matrix (Fin m') (Fin m) ℂ) (ρ : Mat n m) :
    lop G M (lop G' M' ρ) = lop (G * G') (M * M') ρ := by
  simp only [lop, mul_kronecker_mul, conjTranspose_mul, Matrix.mul_assoc]

theorem lop_one (ρ : Mat n m) :
    lop (1 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) ρ = ρ := by
  simp [lop]

theorem lop_kron (G : Matrix (Fin n') (Fin n) ℂ) (M : Matrix (Fin m') (Fin m) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    lop G M (A ⊗ₖ B) = (G * A * Gᴴ) ⊗ₖ (M * B * Mᴴ) := by
  simp only [lop, conjTranspose_kronecker, ← mul_kronecker_mul]

theorem pt_kron (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    pt (A ⊗ₖ B) = A ⊗ₖ Bᵀ := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp [pt, kroneckerMap_apply]

theorem transpose_sandwich (M : Matrix (Fin m') (Fin m) ℂ) (X : Matrix (Fin m) (Fin m) ℂ) :
    (M * X * Mᴴ)ᵀ = M.map star * Xᵀ * (M.map star)ᴴ := by
  ext i j
  simp only [transpose_apply, Matrix.mul_apply, conjTranspose_apply, map_apply, star_star,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The partial transpose of a local operation. -/
theorem pt_lop (G : Matrix (Fin n') (Fin n) ℂ) (M : Matrix (Fin m') (Fin m) ℂ) (ρ : Mat n m) :
    pt (lop G M ρ) = lop G (M.map star) (pt ρ) := by
  induction ρ using Matrix.induction_on' with
  | h_zero => rw [lop_zero, pt_zero, pt_zero, lop_zero]
  | h_add p q hp hq => rw [lop_add, pt_add, hp, hq, pt_add, lop_add]
  | h_std_basis x y c =>
    obtain ⟨a, k⟩ := x
    obtain ⟨b, l⟩ := y
    have h : single (a, k) (b, l) c = single a b c ⊗ₖ single k l (1 : ℂ) := by
      rw [single_kronecker_single, mul_one]
    rw [h, lop_kron, pt_kron, pt_kron, lop_kron, transpose_sandwich]

theorem isPSD_lop (G : Matrix (Fin n') (Fin n) ℂ) (M : Matrix (Fin m') (Fin m) ℂ) {ρ : Mat n m}
    (h : IsPSD ρ) : IsPSD (lop G M ρ) :=
  isPSD_conj h _

theorem isPPT_lop (G : Matrix (Fin n') (Fin n) ℂ) (M : Matrix (Fin m') (Fin m) ℂ) {ρ : Mat n m}
    (h : IsPPT ρ) : IsPPT (lop G M ρ) :=
  ⟨isPSD_lop G M h.1, by rw [pt_lop]; exact isPSD_lop G _ h.2⟩

theorem kron_mulVec_prodVec (G : Matrix (Fin n') (Fin n) ℂ) (M : Matrix (Fin m') (Fin m) ℂ)
    (x : Fin n → ℂ) (y : Fin m → ℂ) :
    (G ⊗ₖ M) *ᵥ prodVec x y = prodVec (G *ᵥ x) (M *ᵥ y) := by
  ext ⟨a, k⟩
  simp only [mulVec, dotProduct, prodVec, kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isSeparable_lop (G : Matrix (Fin n') (Fin n) ℂ) (M : Matrix (Fin m') (Fin m) ℂ)
    {ρ : Mat n m} (h : IsSeparable ρ) : IsSeparable (lop G M ρ) := by
  obtain ⟨r, x, y, rfl⟩ := h
  refine ⟨r, fun s => G *ᵥ x s, fun s => M *ᵥ y s, ?_⟩
  simp only [lop, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← MathLab.vecMulVec_mulVec_star, kron_mulVec_prodVec]

end LocalOps

/-! ## Extreme rays of the PPT cone -/

/-- `ρ` spans an extreme ray of the PPT cone. -/
def IsExtremePPT {n m : ℕ} (ρ : Mat n m) : Prop :=
  IsPPT ρ ∧ ∀ ρ₁ ρ₂ : Mat n m, IsPPT ρ₁ → IsPPT ρ₂ → ρ = ρ₁ + ρ₂ → ∃ c : ℝ, ρ₁ = c • ρ

/-- Invertible local operations map extreme rays to extreme rays. -/
theorem isExtremePPT_lop {n m : ℕ} {G G' : Matrix (Fin n) (Fin n) ℂ}
    {M M' : Matrix (Fin m) (Fin m) ℂ} (hG : G' * G = 1) (hM : M' * M = 1) {ρ : Mat n m}
    (hρ : IsExtremePPT ρ) : IsExtremePPT (lop G M ρ) := by
  refine ⟨isPPT_lop G M hρ.1, fun ρ₁ ρ₂ h₁ h₂ h => ?_⟩
  have hG' : G * G' = 1 := mul_eq_one_comm.1 hG
  have hM' : M * M' = 1 := mul_eq_one_comm.1 hM
  have hback : ρ = lop G' M' ρ₁ + lop G' M' ρ₂ := by
    rw [← lop_add, ← h, lop_lop, hG, hM, lop_one]
  obtain ⟨c, hc⟩ := hρ.2 _ _ (isPPT_lop G' M' h₁) (isPPT_lop G' M' h₂) hback
  refine ⟨c, ?_⟩
  have : ρ₁ = lop G M (lop G' M' ρ₁) := by rw [lop_lop, hG', hM', lop_one]
  rw [this, hc, ← Complex.coe_smul, lop_smul, Complex.coe_smul]

/-! ## Block vectors and the blocks of a local operation -/

/-- The block vector `(a, b)` in `ℂ² ⊗ ℂᵐ`. -/
def bvec (a b : Fin m → ℂ) : Idx 2 m → ℂ := fun x => (![a, b] x.1) x.2

theorem blk_mulVec_bvec (P Q R S : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m → ℂ) :
    blk P Q R S *ᵥ bvec a b = bvec (P *ᵥ a + Q *ᵥ b) (R *ᵥ a + S *ᵥ b) := by
  ext ⟨i, k⟩
  fin_cases i <;> simp [blk, bvec, mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem star_bvec_dotProduct (a b c d : Fin m → ℂ) :
    star (bvec a b) ⬝ᵥ bvec c d = star a ⬝ᵥ c + star b ⬝ᵥ d := by
  simp [bvec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem bvec_eq_zero {a b : Fin m → ℂ} (h : bvec a b = 0) : a = 0 ∧ b = 0 := by
  constructor
  · ext k
    simpa [bvec] using congrFun h (0, k)
  · ext k
    simpa [bvec] using congrFun h (1, k)

theorem prodVec_eq_bvec (g : Fin 2 → ℂ) (w : Fin m → ℂ) :
    prodVec g w = bvec (g 0 • w) (g 1 • w) := by
  ext ⟨i, k⟩
  fin_cases i <;> rfl

/-- The blocks of `(1 ⊗ M) ρ (1 ⊗ M)ᴴ` are `M ρ_ab Mᴴ`. -/
theorem blkOf_lop_one {m' : ℕ} (M : Matrix (Fin m') (Fin m) ℂ) (ρ : Mat 2 m) (a b : Fin 2) :
    blkOf (lop 1 M ρ) a b = M * blkOf ρ a b * Mᴴ := by
  ext k l
  simp only [blkOf, lop, Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, one_apply, Finset.sum_add_distrib, add_mul]
  fin_cases a <;> fin_cases b <;> simp

/-- The corner block of `(G ⊗ 1) ρ (G ⊗ 1)ᴴ` for `G = [[1, z], [0, 1]]`. -/
theorem blkOf_lop_shear (z : ℂ) (ρ : Mat 2 m) :
    blkOf (lop !![1, z; 0, 1] 1 ρ) 0 0 =
      blkOf ρ 0 0 + star z • blkOf ρ 0 1 + z • blkOf ρ 1 0 + (z * star z) • blkOf ρ 1 1 := by
  ext k l
  simp only [blkOf, lop, Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, one_apply, Finset.sum_add_distrib, add_mul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp [apply_ite (starRingEnd ℂ),
    mul_ite, ite_mul, Finset.sum_ite_eq]
  ring

end ChainWoronowicz

end

end -- public section
