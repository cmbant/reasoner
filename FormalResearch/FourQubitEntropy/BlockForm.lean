import FormalResearch.FourQubitEntropy.MagicCoord

/-!
# Block form of a cut matrix with singlet top vector

In magic coordinates, `X Xᴴ = Xᴴ X = D = diag(1/6, 1/6, 1/2, 1/6)` (the `1/2` at the singlet index)
forces `X` to be block diagonal, `X = x₀ P ⊕ Y`.
-/

open scoped ComplexConjugate Matrix

namespace FormalResearch.FourQubitEntropy

/-- The index of the singlet `m₃` in the magic basis. -/
def sing : Fin 2 × Fin 2 := (1, 0)

noncomputable def dvec (i : Fin 2 × Fin 2) : ℂ := 1 / 6 + if i = sing then 1 / 3 else 0

/-- `D = diag(1/6, 1/6, 1/2, 1/6)`. -/
noncomputable def Dm : Mat4 := Matrix.diagonal dvec

/-- The projector onto the singlet coordinate. -/
noncomputable def Pm : Mat4 := Matrix.diagonal fun i => if i = sing then (1 : ℂ) else 0

theorem Pm_apply (j k : Fin 2 × Fin 2) : Pm j k = if j = sing ∧ k = sing then 1 else 0 := by
  unfold Pm
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [Matrix.diagonal_apply, hjk]
    intro h1 h2; exact hjk (h1.trans h2.symm)

theorem Pm_mul_apply (X : Mat4) (j k : Fin 2 × Fin 2) :
    (Pm * X) j k = if j = sing then X j k else 0 := by
  simp [Pm, Matrix.diagonal_mul]

theorem mul_Pm_apply (X : Mat4) (j k : Fin 2 × Fin 2) :
    (X * Pm) j k = if k = sing then X j k else 0 := by
  simp [Pm, Matrix.mul_diagonal]

theorem Pm_mul_Pm : Pm * Pm = Pm := by
  unfold Pm; rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp

section Block

variable {X : Mat4} (h1 : X * Xᴴ = Dm) (h2 : Xᴴ * X = Dm)
include h1 h2

theorem commute_D : X * Dm = Dm * X := by
  conv_lhs => rw [← h2]
  conv_rhs => rw [← h1]
  simp only [Matrix.mul_assoc]

theorem block_zero {j k : Fin 2 × Fin 2} (hjk : (j = sing) ≠ (k = sing)) : X j k = 0 := by
  have h := congrFun (congrFun (commute_D h1 h2) j) k
  simp only [Dm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hd : dvec k - dvec j ≠ 0 := by
    unfold dvec
    by_cases hj : j = sing <;> by_cases hk : k = sing <;> simp [hj, hk] at hjk ⊢ <;> norm_num
  have : X j k * (dvec k - dvec j) = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_right hd

theorem Pm_mul_X : Pm * X = (X sing sing) • Pm := by
  ext j k
  rw [Pm_mul_apply, Matrix.smul_apply, Pm_apply]
  by_cases hj : j = sing
  · by_cases hk : k = sing
    · simp [hj, hk]
    · have := block_zero h1 h2 (show (j = sing) ≠ (k = sing) by simp [hj, hk])
      simp [hj, hk]
      subst hj; exact this
  · simp [hj]

theorem X_mul_Pm : X * Pm = (X sing sing) • Pm := by
  ext j k
  rw [mul_Pm_apply, Matrix.smul_apply, Pm_apply]
  by_cases hk : k = sing
  · by_cases hj : j = sing
    · simp [hj, hk]
    · have := block_zero h1 h2 (show (j = sing) ≠ (k = sing) by simp [hj, hk])
      simp [hj, hk]
      subst hk; exact this
  · simp [hk]

end Block

/-! ### Unitary matrices on the complement of the singlet with maximal trace -/

theorem normSq_row_sum (S : Mat4) (hS : S * Sᴴ = 1 - Pm) (j : Fin 2 × Fin 2) :
    ∑ k, Complex.normSq (S j k) = if j = sing then 0 else 1 := by
  have h := congrFun (congrFun hS j) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.one_apply,
    Pm_apply] at h
  have e : ∀ k, ((Complex.normSq (S j k) : ℝ) : ℂ) = S j k * star (S j k) :=
    fun k => (Complex.mul_conj (S j k)).symm
  have h' : (((∑ k, Complex.normSq (S j k) : ℝ)) : ℂ) = (if j = sing then 0 else 1 : ℝ) := by
    push_cast
    simp only [e]
    rw [h]
    by_cases hj : j = sing <;> simp [hj]
  exact_mod_cast h'

theorem re_le_one {z : ℂ} (h : Complex.normSq z ≤ 1) : z.re ≤ 1 := by
  rw [Complex.normSq_apply] at h
  nlinarith [mul_self_nonneg z.im]

theorem eq_one_of_re {z : ℂ} (h : Complex.normSq z ≤ 1) (hre : z.re = 1) : z = 1 := by
  apply Complex.ext
  · simpa using hre
  · have h2 : z.im ^ 2 ≤ 0 := by
      rw [Complex.normSq_apply] at h
      nlinarith
    simpa using (pow_eq_zero_iff (two_ne_zero)).1 (le_antisymm h2 (sq_nonneg _))

theorem diag_of_trace (S : Mat4) (hS : S * Sᴴ = 1 - Pm) (lam : ℂ)
    (hl : Complex.normSq lam = 1) (ht : Matrix.trace S = 3 * lam) : S = lam • (1 - Pm) := by
  have hrow := normSq_row_sum S hS
  have le1 : ∀ j, j ≠ sing → Complex.normSq (S j j) ≤ 1 := by
    intro j hj
    have := hrow j
    rw [if_neg hj] at this
    rw [← this]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (S j k))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
  have hss : S sing sing = 0 := by
    have := hrow sing
    rw [if_pos rfl] at this
    have h0 : Complex.normSq (S sing sing) = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (S sing k))).1
        this sing (Finset.mem_univ _)
      exact this
    exact Complex.normSq_eq_zero.1 h0
  have hrow0 : ∀ k, S sing k = 0 := by
    intro k
    have := hrow sing
    rw [if_pos rfl] at this
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (S sing k))).1
      this k (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  -- the three diagonal entries away from the singlet
  set μ := (starRingEnd ℂ) lam with hμ
  have hμl : μ * lam = 1 := by
    rw [hμ, mul_comm, Complex.mul_conj]; exact_mod_cast hl
  have hnμ : Complex.normSq μ = 1 := by rw [hμ, Complex.normSq_conj]; exact hl
  have key : ∀ j, j ≠ sing → (μ * S j j).re ≤ 1 := by
    intro j hj
    apply re_le_one
    rw [map_mul, hnμ, one_mul]; exact le1 j hj
  have htr : (μ * S (0, 0) (0, 0)).re + (μ * S (0, 1) (0, 1)).re + (μ * S (1, 1) (1, 1)).re = 3 := by
    have h := ht
    simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, Fin.sum_univ_two] at h
    have h2 : μ * (S (0, 0) (0, 0) + S (0, 1) (0, 1) + S (1, 0) (1, 0) + S (1, 1) (1, 1)) = 3 := by
      have : S (0, 0) (0, 0) + S (0, 1) (0, 1) + S (1, 0) (1, 0) + S (1, 1) (1, 1) = 3 * lam := by
        linear_combination h
      rw [this]; linear_combination 3 * hμl
    have hs : S (1, 0) (1, 0) = 0 := hss
    rw [hs] at h2
    have := congrArg Complex.re h2
    simp only [mul_add, Complex.add_re, add_zero, mul_zero, Complex.zero_re] at this
    simpa using this
  have k0 := key (0, 0) (by simp [sing])
  have k1 := key (0, 1) (by simp [sing])
  have k3 := key (1, 1) (by simp [sing])
  have d0 : μ * S (0, 0) (0, 0) = 1 := by
    apply eq_one_of_re (by rw [map_mul, hnμ, one_mul]; exact le1 _ (by simp [sing]))
    linarith
  have d1 : μ * S (0, 1) (0, 1) = 1 := by
    apply eq_one_of_re (by rw [map_mul, hnμ, one_mul]; exact le1 _ (by simp [sing]))
    linarith
  have d3 : μ * S (1, 1) (1, 1) = 1 := by
    apply eq_one_of_re (by rw [map_mul, hnμ, one_mul]; exact le1 _ (by simp [sing]))
    linarith
  have diag : ∀ j, j ≠ sing → S j j = lam := by
    intro j hj
    have hz : μ * S j j = 1 := by
      fin_cases j
      · exact d0
      · exact d1
      · exact absurd rfl hj
      · exact d3
    calc S j j = lam * (μ * S j j) := by rw [← mul_assoc, mul_comm lam μ, hμl, one_mul]
      _ = lam := by rw [hz, mul_one]
  have off : ∀ j k, j ≠ sing → k ≠ j → S j k = 0 := by
    intro j k hj hkj
    have h1 := hrow j
    rw [if_neg hj] at h1
    have hd : Complex.normSq (S j j) = 1 := by rw [diag j hj, hl]
    have h2 : ∑ k', Complex.normSq (S j k') = Complex.normSq (S j j) +
        ∑ k' ∈ Finset.univ.erase j, Complex.normSq (S j k') :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    rw [h2, hd] at h1
    have h3 : ∑ k' ∈ Finset.univ.erase j, Complex.normSq (S j k') = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k' _ => Complex.normSq_nonneg (S j k'))).1 h3 k
      (Finset.mem_erase.2 ⟨hkj, Finset.mem_univ _⟩)
    exact Complex.normSq_eq_zero.1 this
  ext j k
  simp only [Matrix.smul_apply, Matrix.sub_apply, Pm_apply, Matrix.one_apply]
  by_cases hj : j = sing
  · rw [hj, hrow0 k]
    by_cases hk : k = sing
    · simp [hk]
    · have : sing ≠ k := fun h => hk h.symm
      simp [hk, this]
  · by_cases hk : k = j
    · rw [hk, diag j hj]
      simp [hj]
    · rw [off j k hj hk]
      have : j ≠ k := fun h => hk h.symm
      simp [this, hj]

/-! ### The complement block -/

theorem Pm_conjTranspose : Pmᴴ = Pm := by
  ext j k; simp [Pm_apply, Matrix.conjTranspose_apply, and_comm]

theorem Pm_transpose : Pmᵀ = Pm := by
  ext j k; simp [Pm_apply, Matrix.transpose_apply, and_comm]

theorem Dm_eq : Dm = (1 / 2 : ℂ) • Pm + (1 / 6 : ℂ) • (1 - Pm) := by
  ext j k
  by_cases hjk : j = k
  · subst hjk
    by_cases hj : j = sing
    · simp [Dm, dvec, Pm_apply, Matrix.one_apply, hj]; norm_num
    · simp [Dm, dvec, Pm_apply, Matrix.one_apply, hj]
  · have h' : ¬(j = sing ∧ k = sing) := fun ⟨a, b⟩ => hjk (a.trans b.symm)
    simp [Dm, dvec, Matrix.diagonal_apply, Pm_apply, Matrix.one_apply, hjk, h']

section Y

variable {X : Mat4} (h1 : X * Xᴴ = Dm) (h2 : Xᴴ * X = Dm)

/-- The complement block `Y = X - x₀ P`. -/
noncomputable def blockY (X : Mat4) : Mat4 := X - (X sing sing) • Pm

include h1 h2 in
theorem Pm_mul_Y : Pm * blockY X = 0 := by
  unfold blockY
  rw [Matrix.mul_sub, Matrix.mul_smul, Pm_mul_X h1 h2, Pm_mul_Pm]; simp

include h1 h2 in
theorem Y_mul_Pm : blockY X * Pm = 0 := by
  unfold blockY
  rw [Matrix.sub_mul, Matrix.smul_mul, X_mul_Pm h1 h2, Pm_mul_Pm]; simp

include h1 h2 in
theorem x0_normSq : X sing sing * (starRingEnd ℂ) (X sing sing) = 1 / 2 := by
  have h := congrFun (congrFun h1 sing) sing
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Dm, Matrix.diagonal_apply, dvec] at h
  rw [Finset.sum_eq_single sing] at h
  · simpa [dvec] using h.trans (by norm_num)
  · intro k _ hk
    have := block_zero h1 h2 (show (sing = sing) ≠ (k = sing) by simp [hk])
    simp [this]
  · simp

end Y

section YGram

variable {x0 : ℂ} {Y : Mat4} (hPY : Pm * Y = 0) (hYP : Y * Pm = 0)

include hPY hYP in
theorem Y_gram_left (hx0 : x0 * (starRingEnd ℂ) x0 = 1 / 2)
    (h1 : (x0 • Pm + Y) * (x0 • Pm + Y)ᴴ = Dm) : Y * Yᴴ = (1 / 6 : ℂ) • (1 - Pm) := by
  have hY1 : Pm * Yᴴ = 0 := by
    have := congrArg Matrix.conjTranspose hYP
    rwa [Matrix.conjTranspose_mul, Pm_conjTranspose, Matrix.conjTranspose_zero] at this
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Pm_conjTranspose] at h1
  have e : (x0 • Pm + Y) * ((star x0) • Pm + Yᴴ)
      = (x0 * star x0) • (Pm * Pm) + x0 • (Pm * Yᴴ) + (star x0) • (Y * Pm) + Y * Yᴴ := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [e, hY1, hYP, Pm_mul_Pm] at h1
  have hx : x0 * star x0 = 1 / 2 := hx0
  rw [hx, Dm_eq] at h1
  simpa using h1

include hPY hYP in
theorem Y_gram_right (hx0 : x0 * (starRingEnd ℂ) x0 = 1 / 2)
    (h2 : (x0 • Pm + Y)ᴴ * (x0 • Pm + Y) = Dm) : Yᴴ * Y = (1 / 6 : ℂ) • (1 - Pm) := by
  have hY1 : Yᴴ * Pm = 0 := by
    have := congrArg Matrix.conjTranspose hPY
    rwa [Matrix.conjTranspose_mul, Pm_conjTranspose, Matrix.conjTranspose_zero] at this
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Pm_conjTranspose] at h2
  have e : ((star x0) • Pm + Yᴴ) * (x0 • Pm + Y)
      = (star x0 * x0) • (Pm * Pm) + (star x0) • (Pm * Y) + x0 • (Yᴴ * Pm) + Yᴴ * Y := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [e, hY1, hPY, Pm_mul_Pm] at h2
  have hx : star x0 * x0 = 1 / 2 := by rw [mul_comm]; exact hx0
  rw [hx, Dm_eq] at h2
  simpa using h2

include hPY hYP in
theorem Y_trace (h3 : Matrix.trace ((x0 • Pm + Y)ᵀ * (x0 • Pm + Y)) = 0) :
    Matrix.trace (Y * Yᵀ) = -(x0 * x0) := by
  have hY1 : Yᵀ * Pm = 0 := by
    have := congrArg Matrix.transpose hPY
    rwa [Matrix.transpose_mul, Pm_transpose, Matrix.transpose_zero] at this
  have hY2 : Pm * Yᵀ = 0 := by
    have := congrArg Matrix.transpose hYP
    rwa [Matrix.transpose_mul, Pm_transpose, Matrix.transpose_zero] at this
  rw [Matrix.transpose_add, Matrix.transpose_smul, Pm_transpose] at h3
  have e : (x0 • Pm + Yᵀ) * (x0 • Pm + Y)
      = (x0 * x0) • (Pm * Pm) + x0 • (Pm * Y) + x0 • (Yᵀ * Pm) + Yᵀ * Y := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [e, hY1, hPY, Pm_mul_Pm] at h3
  have htp : Matrix.trace Pm = 1 := by simp [Matrix.trace, Pm_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, sing]
  simp only [smul_zero, add_zero, Matrix.trace_add, Matrix.trace_smul, htp, smul_eq_mul, mul_one,
    Matrix.trace_zero] at h3
  rw [Matrix.trace_mul_comm] at h3
  linear_combination h3

end YGram

/-! ### Real orthogonal complement -/

theorem transpose_mul_map_conj (Y : Mat4) : Yᵀ * Y.map (starRingEnd ℂ) = (Yᴴ * Y).map (starRingEnd ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]

theorem map_conj_one_sub_Pm : (1 - Pm : Mat4).map (starRingEnd ℂ) = 1 - Pm := by
  ext i j
  by_cases h : i = j
  · subst h; by_cases hi : i = sing <;> simp [Pm_apply, Matrix.one_apply, hi]
  · simp [Pm_apply, Matrix.one_apply, h]

theorem map_conj_smul_one_sub_Pm : ((1 / 6 : ℂ) • (1 - Pm : Mat4)).map (starRingEnd ℂ) = (1 / 6 : ℂ) • (1 - Pm) := by
  ext i j
  have := congrFun (congrFun map_conj_one_sub_Pm i) j
  have h6 : (starRingEnd ℂ) (1 / 6 : ℂ) = 1 / 6 := by
    rw [show (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) by push_cast; ring]; exact Complex.conj_ofReal _
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, h6] at this ⊢
  rw [this]

/-- A matrix `R` with `R Rᵀ = R Rᴴ = 1 - P` is real. -/
theorem real_of_orth (R : Mat4) (h1 : R * Rᵀ = 1 - Pm) (h2 : R * Rᴴ = 1 - Pm) :
    ∀ j k, (R j k).im = 0 := by
  intro j k
  have a := congrArg Complex.re (congrFun (congrFun h1 j) j)
  have b := congrArg Complex.re (congrFun (congrFun h2 j) j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] at a b
  have hsum : ∑ l, (R j l).im * (R j l).im = 0 := by
    have : ∑ l, ((R j l).re * (R j l).re - (R j l).im * (R j l).im) -
        ∑ l, ((R j l).re * (R j l).re - (R j l).im * -(R j l).im) =
        -2 * ∑ l, (R j l).im * (R j l).im := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_self_nonneg ((R j l).im))).1 hsum k
    (Finset.mem_univ _)
  exact mul_self_eq_zero.1 this

/-- The real projector onto the singlet coordinate. -/
def Prm : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := Matrix.diagonal fun i => if i = sing then 1 else 0

theorem Pm_eq_map : Pm = Prm.map (Complex.ofReal) := by
  ext i j
  by_cases h : i = j
  · subst h; by_cases hi : i = sing <;> simp [Pm, Prm, hi]
  · simp [Pm, Prm, Matrix.diagonal_apply, h]

/-- `1/√6`. -/
noncomputable def rt6 : ℂ := ((Real.sqrt 6 : ℝ) : ℂ)⁻¹

theorem rt6_mul_rt6 : rt6 * rt6 = 1 / 6 := by
  have h : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have h' : ((Real.sqrt 6 : ℝ) : ℂ) * ((Real.sqrt 6 : ℝ) : ℂ) = 6 := by exact_mod_cast h
  unfold rt6
  rw [← mul_inv, h']; norm_num

theorem normSq_x0 {x0 : ℂ} (h : x0 * (starRingEnd ℂ) x0 = 1 / 2) : Complex.normSq x0 = 1 / 2 := by
  rw [Complex.mul_conj] at h
  have : ((Complex.normSq x0 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; exact h
  exact_mod_cast this

end FormalResearch.FourQubitEntropy
