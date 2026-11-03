import FormalResearch.PPTThreeQubit.Witness

/-!
# The support argument: a biseparable operator supported on `R_s` satisfies `tr(H_s X) ≥ 0`

Source: `family.tex`, `prop:ppt3-witness` (end of (b)) and the proof of `thm:ppt3-family`.
If `ρ = B_s X B_s†` is biseparable, every vector `φᵢ` of a decomposition lies in `R_s = ran B_s`
(Lemma `phi_ker`: the three annihilating rows `K_0 = e`, `K_1 = o`, `K_2 = (3s,0,0,1,0,1,1,0)` of
`family.tex` — for general `s > 0` — vanish on every `φᵢ`), `B_s` has the explicit left inverse
`L`, and then `X = ∑ᵢ cᵢcᵢ†` with `cᵢ = Lφᵢ`, so `tr(H_s X) = ∑ᵢ re(cᵢ† H_s cᵢ) ≥ 0` by
`formH_nonneg_of_cutProduct`.  This covers every real `s > 0` and all three cuts, mixtures
included, with no symmetry hypothesis on `X`.
-/

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-- Second row of the annihilator: `K_2 = (3s, 0, 0, 1, 0, 1, 1, 0)`; the rows `K_0 = e`, `K_1 = o`
are `eVec`, `oVec`. -/
def k2 (s : ℝ) : Fin 8 → ℂ := ![3 * s, 0, 0, 1, 0, 1, 1, 0]

/-- `K_0 B_s = 0`. -/
theorem eVec_dot_Bs (s : ℝ) (y : Fin 5 → ℂ) : eVec ⬝ᵥ (Bs s *ᵥ y) = 0 := by
  rw [Bs_mulVec]
  simp [dotProduct, Fin.sum_univ_eight, eVec]
  linear_combination (-s * y 0 + y 3) * ω_sq_add_ω_add_one + y 3 * ω * ω_cube

/-- `K_1 B_s = 0`. -/
theorem oVec_dot_Bs (s : ℝ) (y : Fin 5 → ℂ) : oVec ⬝ᵥ (Bs s *ᵥ y) = 0 := by
  rw [Bs_mulVec]
  simp [dotProduct, Fin.sum_univ_eight, oVec]
  linear_combination (y 2 + y 4) * ω_sq_add_ω_add_one + y 4 * ω * ω_cube

/-- `K_2 B_s = 0`. -/
theorem k2_dot_Bs (s : ℝ) (y : Fin 5 → ℂ) : k2 s ⬝ᵥ (Bs s *ᵥ y) = 0 := by
  rw [Bs_mulVec]
  simp [dotProduct, Fin.sum_univ_eight, k2]
  linear_combination y 3 * ω_sq_add_ω_add_one

/-- `Lφ`: the coordinates of `φ` in the basis `(u_s, v, w, e, o)`; a left inverse of `B_s`. -/
def Lmat : Matrix (Fin 5) (Fin 8) ℂ :=
  Matrix.of ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1 / 3, 1 / 3, 0, 1 / 3, 0, 0, 0],
    ![0, 0, 0, 1 / 3, 0, ω ^ 2 / 3, ω / 3, 0],
    ![0, ω / 3, ω ^ 2 / 3, 0, 1 / 3, 0, 0, 0]]

theorem Lmat_mulVec (φ : Fin 8 → ℂ) :
    Lmat *ᵥ φ = ![φ 0, φ 7, (φ 1 + φ 2 + φ 4) / 3, (φ 3 + ω ^ 2 * φ 5 + ω * φ 6) / 3,
      (ω * φ 1 + ω ^ 2 * φ 2 + φ 4) / 3] := by
  ext i
  fin_cases i <;> simp [Lmat, mulVec, dotProduct, Fin.sum_univ_eight] <;> ring

/-- `L B_s = I`. -/
theorem Lmat_mulVec_Bs (s : ℝ) (y : Fin 5 → ℂ) : Lmat *ᵥ (Bs s *ᵥ y) = y := by
  rw [Bs_mulVec, Lmat_mulVec]
  ext i
  fin_cases i
  · simp
  · simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    linear_combination (y 4 / 3) * ω_sq_add_ω_add_one
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    linear_combination (-s * y 0 / 3) * ω_sq_add_ω_add_one + (2 * y 3 / 3) * ω_cube
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    linear_combination (y 2 / 3) * ω_sq_add_ω_add_one + (2 * y 4 / 3) * ω_cube

theorem Lmat_mul_Bs (s : ℝ) : Lmat * Bs s = 1 := by
  ext i j
  have := congrFun (Lmat_mulVec_Bs s (Pi.single j 1)) i
  rw [mulVec_mulVec] at this
  have h' : (Lmat * Bs s) i j = (Pi.single j (1 : ℂ) : Fin 5 → ℂ) i := by simpa using this
  rw [h', Matrix.one_apply, Pi.single_apply]

/-- If the three rows of the annihilator vanish on `φ`, then `φ = B_s (Lφ)`. -/
theorem Bs_Lmat_of_ker (s : ℝ) (φ : Fin 8 → ℂ) (h0 : eVec ⬝ᵥ φ = 0) (h1 : oVec ⬝ᵥ φ = 0)
    (h2 : k2 s ⬝ᵥ φ = 0) : Bs s *ᵥ (Lmat *ᵥ φ) = φ := by
  simp [dotProduct, Fin.sum_univ_eight, eVec, oVec, k2] at h0 h1 h2
  have hK0 : φ 3 + ω * φ 5 + ω ^ 2 * φ 6 = 0 := by linear_combination h0
  have hK1 : ω ^ 2 * φ 1 + ω * φ 2 + φ 4 = 0 := by linear_combination h1
  have hK2 : 3 * s * φ 0 + φ 3 + φ 5 + φ 6 = 0 := by linear_combination h2
  have hω := ω_sq_add_ω_add_one
  rw [Lmat_mulVec, Bs_mulVec]
  ext i
  fin_cases i
  · simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    linear_combination (ω^2/3 + 1/3) * hK1 + (-φ 1*ω^2/3 + 2*φ 1*ω/3 - 2*φ 1/3 + φ 2*ω^2/3 - 2*φ 2*ω/3 + φ 2/3) * hω
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    linear_combination (ω/3 + 1/3) * hK1 + (-φ 1*ω/3 + φ 1/3 + φ 2*ω/3 - 2*φ 2/3) * hω
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    linear_combination (-1/3) * hK0 + (ω^2/3 + ω/3) * hK2 + (-φ 0*s - φ 3/3) * hω
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    linear_combination (-1/3) * hK1 + (φ 1/3 + φ 2/3) * hω
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    linear_combination (ω/3 + 1/3) * hK0 + (ω^2/3 + ω/3) * hK2 + (-φ 0*s - φ 3/3 + φ 5*ω/3 - φ 5 - φ 6*ω/3) * hω
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    linear_combination (-ω/3) * hK0 + (-2*ω^2/3 - 2*ω/3 - 1) * hK2 + (2*φ 0*s + φ 3 + φ 5*ω^2/3 - φ 5*ω/3 + φ 5 + 2*φ 6*ω/3) * hω
  · simp

/-! ### Generic lemmas on rank-one decompositions -/

/-- `∑ᵢ |k·φᵢ|² = k (∑ᵢ |φᵢ⟩⟨φᵢ|) k†`. -/
theorem sum_normSq_dot {n m : ℕ} (φ : Fin n → Fin m → ℂ) (k : Fin m → ℂ) :
    ∑ i, ((Complex.normSq (k ⬝ᵥ φ i) : ℝ) : ℂ) =
      k ⬝ᵥ ((∑ i, vecMulVec (φ i) (star (φ i))) *ᵥ star k) := by
  have hs : ∀ v : Fin m → ℂ, (∑ i, vecMulVec (φ i) (star (φ i))) *ᵥ v
      = ∑ i, (star (φ i) ⬝ᵥ v) • φ i := by
    intro v
    ext j
    simp [mulVec, Matrix.sum_apply, dotProduct, Finset.sum_mul, vecMulVec_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hs, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, ← Complex.mul_conj, smul_eq_mul, star_dotProduct_star]
  rw [mul_comm]; rfl

/-- If `ρ = ∑ᵢ |φᵢ⟩⟨φᵢ|` and `k ρ k† = 0` then `k·φᵢ = 0` for all `i`. -/
theorem dot_eq_zero_of_sum {n m : ℕ} (φ : Fin n → Fin m → ℂ) (k : Fin m → ℂ)
    (h : k ⬝ᵥ ((∑ i, vecMulVec (φ i) (star (φ i))) *ᵥ star k) = 0) (i : Fin n) :
    k ⬝ᵥ φ i = 0 := by
  rw [← sum_normSq_dot] at h
  have h' : ∑ i, Complex.normSq (k ⬝ᵥ φ i) = 0 := by exact_mod_cast h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).mp h' i
    (Finset.mem_univ _)
  exact Complex.normSq_eq_zero.mp this

/-- If `k B y = 0` for all `y`, and `B X B†` is a sum of rank-ones `|φᵢ⟩⟨φᵢ|`, then `k·φᵢ = 0`. -/
theorem dot_eq_zero_of_range {n m r : ℕ} (B : Matrix (Fin m) (Fin r) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    (φ : Fin n → Fin m → ℂ) (hρ : B * X * Bᴴ = ∑ i, vecMulVec (φ i) (star (φ i)))
    (k : Fin m → ℂ) (hk : ∀ y, k ⬝ᵥ (B *ᵥ y) = 0) (i : Fin n) : k ⬝ᵥ φ i = 0 := by
  apply dot_eq_zero_of_sum φ k _ i
  rw [← hρ, ← mulVec_mulVec, ← mulVec_mulVec]
  exact hk _

/-- `tr(H_s |c⟩⟨c|) = c† H_s c` (real part). -/
theorem trace_Hs_vecMulVec_re (s : ℝ) (c : Fin 5 → ℂ) :
    (Hs s * vecMulVec c (star c)).trace.re = formH s c := by
  simp [Hs, formH, trace, diag, diagonal_mul, vecMulVec_apply, Complex.re_sum,
    Complex.normSq_apply]

/-- **Support criterion** (`prop:ppt3-witness`, last sentence, and the proof of
`thm:ppt3-family`).  Let `s > 0` and `X` a `5 × 5` coefficient matrix.  If `B_s X B_s†` is
biseparable (a finite sum of cut-product rank-ones across any cuts), then `re tr(H_s X) ≥ 0`.
No Hermiticity or symmetry hypothesis on `X` is needed. -/
theorem trace_Hs_nonneg_of_biseparable {s : ℝ} (hs : 0 < s) (X : Matrix (Fin 5) (Fin 5) ℂ)
    (h : IsBiseparable (Bs s * X * (Bs s)ᴴ)) : 0 ≤ (Hs s * X).trace.re := by
  obtain ⟨n, φ, hprod, hρ⟩ := h
  have hker : ∀ i, Bs s *ᵥ (Lmat *ᵥ φ i) = φ i := fun i =>
    Bs_Lmat_of_ker s (φ i)
      (dot_eq_zero_of_range (Bs s) X φ hρ eVec (eVec_dot_Bs s) i)
      (dot_eq_zero_of_range (Bs s) X φ hρ oVec (oVec_dot_Bs s) i)
      (dot_eq_zero_of_range (Bs s) X φ hρ (k2 s) (k2_dot_Bs s) i)
  have hX : X = ∑ i, vecMulVec (Lmat *ᵥ φ i) (star (Lmat *ᵥ φ i)) := by
    have h1 : Lmat * (Bs s * X * (Bs s)ᴴ) * Lmatᴴ = X := by
      have : Lmat * (Bs s * X * (Bs s)ᴴ) * Lmatᴴ = (Lmat * Bs s) * X * (Lmat * Bs s)ᴴ := by
        simp [Matrix.mul_assoc, conjTranspose_mul]
      rw [this, Lmat_mul_Bs]; simp
    rw [← h1, hρ, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]
  rw [hX, Finset.mul_sum, trace_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [trace_Hs_vecMulVec_re]
  apply formH_nonneg_of_cutProduct hs
  rw [hker i]
  exact hprod i

end

/-- info: 'FormalResearch.PPTThreeQubit.trace_Hs_nonneg_of_biseparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trace_Hs_nonneg_of_biseparable

end FormalResearch.PPTThreeQubit
