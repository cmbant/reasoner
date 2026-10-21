import FormalResearch.FourQubitEntropy.Classify

/-!
# The maximisers are the local-unitary images of `M₄` and `conj M₄`
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

theorem magicCoord_mul (K Z : Mat4) :
    magicCoord (K * Z) = (magicBᴴ * K * magicB) * magicCoord Z := by
  unfold magicCoord
  calc magicBᴴ * (K * Z) * magicB.map (starRingEnd ℂ)
      = magicBᴴ * K * (magicB * magicBᴴ) * Z * magicB.map (starRingEnd ℂ) := by
        rw [magicB_unitary']; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem map_ofReal_mul (A B : RMat4) :
    (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
  ext i j; simp [Matrix.mul_apply]

theorem map_ofReal_smul (σ : ℝ) (A : RMat4) :
    (σ • A).map Complex.ofReal = (σ : ℂ) • A.map Complex.ofReal := by
  ext i j; simp

theorem map_ofReal_sub (A B : RMat4) :
    (A - B).map Complex.ofReal = A.map Complex.ofReal - B.map Complex.ofReal := by
  ext i j; simp

theorem map_ofReal_one : (1 : RMat4).map Complex.ofReal = 1 := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- Rows and columns of `R` at the singlet vanish. -/
theorem R_sing_zero (R : RMat4) (h1 : R * Rᵀ = 1 - Prm) (h2 : Rᵀ * R = 1 - Prm) :
    R * Prm = 0 ∧ Prm * R = 0 := by
  have rowz : ∀ k, R sing k = 0 := by
    intro k
    have := congrFun (congrFun h1 sing) sing
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply, Prm,
      Matrix.diagonal_apply] at this
    simp at this
    have hsum : ∑ l, R sing l * R sing l = 0 := by simpa using this
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_self_nonneg (R sing l))).1 hsum k
      (Finset.mem_univ _)
    exact mul_self_eq_zero.1 this
  have colz : ∀ k, R k sing = 0 := by
    intro k
    have := congrFun (congrFun h2 sing) sing
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply, Prm,
      Matrix.diagonal_apply] at this
    simp at this
    have hsum : ∑ l, R l sing * R l sing = 0 := by simpa using this
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_self_nonneg (R l sing))).1 hsum k
      (Finset.mem_univ _)
    exact mul_self_eq_zero.1 this
  constructor
  · ext i j
    simp only [Prm, Matrix.mul_diagonal, Matrix.zero_apply]
    by_cases h : j = sing <;> simp [h, colz i]
  · ext i j
    simp only [Prm, Matrix.diagonal_mul, Matrix.zero_apply]
    by_cases h : i = sing <;> simp [h, rowz j]

theorem Prm_transpose : Prmᵀ = Prm := by
  unfold Prm; exact Matrix.diagonal_transpose _

theorem Prm_mul_Prm : Prm * Prm = Prm := by
  unfold Prm; rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp

theorem rotX_neg_one_mul (M : RMat4) (hM : M * Prm = 0) :
    rotX (-1) 0 * (Fd - Prm) = -(1 - Prm) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [rotX, Fd, Prm, sing, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.diagonal_apply]

/-- A real orthogonal block with trivial singlet row and column is rotated to `±(1 - P)`. -/
theorem reduce_R (R : RMat4) (h1 : R * Rᵀ = 1 - Prm) (h2 : Rᵀ * R = 1 - Prm) :
    ∃ G : RMat4, Rlz G ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ G * R = σ • (1 - Prm) := by
  obtain ⟨hRP, hPR⟩ := R_sing_zero R h1 h2
  have hRtP : Rᵀ * Prm = 0 := by
    have := congrArg Matrix.transpose hPR
    rwa [Matrix.transpose_mul, Prm_transpose, Matrix.transpose_zero] at this
  have hPRt : Prm * Rᵀ = 0 := by
    have := congrArg Matrix.transpose hRP
    rwa [Matrix.transpose_mul, Prm_transpose, Matrix.transpose_zero] at this
  set Q : RMat4 := R + Prm with hQ
  have hQt : Qᵀ = Rᵀ + Prm := by rw [hQ, Matrix.transpose_add, Prm_transpose]
  have hQ1 : Q * Qᵀ = 1 := by
    rw [hQt, hQ]
    simp only [Matrix.add_mul, Matrix.mul_add, h1, hRP, hPRt, Prm_mul_Prm]
    abel
  have hQ2 : Qᵀ * Q = 1 := by
    rw [hQt, hQ]
    simp only [Matrix.add_mul, Matrix.mul_add, h2, hRtP, hPR, Prm_mul_Prm]
    abel
  have hQ3 : Q * Prm = Prm := by rw [hQ]; simp only [Matrix.add_mul, hRP, Prm_mul_Prm]; abel
  have hQ4 : Prm * Q = Prm := by rw [hQ]; simp only [Matrix.mul_add, hPR, Prm_mul_Prm]; abel
  obtain ⟨G, hG, hGQ⟩ := euler4 Q hQ1 hQ2 hQ3 hQ4
  have hGP : G * Prm = Prm := hG.2.1
  have hGR : G * R = G * Q - Prm := by
    rw [hQ, Matrix.mul_add, hGP]; abel
  rcases hGQ with h | h
  · refine ⟨G, hG, 1, Or.inl rfl, ?_⟩
    rw [hGR, h, one_smul]
  · refine ⟨rotX (-1) 0 * G, (rlz_rotX (by norm_num)).mul hG, -1, Or.inr rfl, ?_⟩
    rw [Matrix.mul_assoc, hGR, h]
    rw [rotX_neg_one_mul R hRP, neg_one_smul]

theorem coord_unit_scalar {s0 : ℂ} (h : Complex.normSq s0 = 1) : (starRingEnd ℂ) s0 * s0 = 1 := by
  rw [mul_comm, Complex.mul_conj, h]; simp

/-- **Classification.** A unit vector with maximally mixed one-qubit marginals, `τ = 0`, and a cut
matrix `12|34` with spectrum `{1/2, 1/6, 1/6, 1/6}` is a local-unitary image of `M₄` or `conj M₄`. -/
theorem classify (ψ : Psi) (hn : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hq : (red12 ψ - (1 / 6 : ℂ) • 1) * (red12 ψ - (1 / 2 : ℂ) • 1) = 0)
    (hτ : spinFlipForm ψ = 0) : LUEquiv ψ M4 ∨ LUEquiv ψ (Psi.conj M4) := by
  obtain ⟨a1, a2, ha1, ha2, hred, hgram⟩ := normalize_both ψ hn hW hq
  set ψ2 := localApply a1ᴴ 1 a2ᴴ 1 ψ with hψ2
  have hL1 : LUEquiv ψ ψ2 := by
    refine ⟨a1ᴴ, 1, a2ᴴ, 1, ?_, by simp, ?_, by simp, rfl⟩
    · rw [Matrix.conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp ha1
    · rw [Matrix.conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp ha2
  set X := magicCoord (zmat ψ2) with hX0
  have h1 : X * Xᴴ = Dm := by
    rw [hX0, coord_mul_conjTranspose, ← red12_zmat, hred, Gs_coord_left]
  have h2 : Xᴴ * X = Dm := by
    rw [hX0, coord_conjTranspose_mul, hgram, Gs_coord_right]
  have h3 : Matrix.trace (Xᵀ * X) = 0 := by
    rw [hX0, ← spinFlip_coord]; exact spinFlip_localApply_zero hτ
  obtain ⟨s0, ε, R, hns0, hε, hRR1, hRR2, hX⟩ := block_structure X h1 h2 h3
  obtain ⟨G, hG, σ, hσ, hGR⟩ := reduce_R R hRR1 hRR2
  obtain ⟨⟨c, hc, hcG⟩, hGP, -⟩ := hG
  -- apply `c ⊗ c` on qubits `1,2`
  set ψ3 := rowLU (kron c c) ψ2 with hψ3
  have hL2 : LUEquiv ψ2 ψ3 := LUEquiv_rows hc hc ψ2
  have hX3 : magicCoord (zmat ψ3) = s0 • (ε • Pm + (σ : ℂ) • rt6 • (1 - Pm)) := by
    rw [hψ3, zmat_rowLU, magicCoord_mul, hcG, ← hX0, hX]
    have e1 : G.map Complex.ofReal * Pm = Pm := by
      rw [Pm_eq_map, ← map_ofReal_mul, hGP]
    have e2 : G.map Complex.ofReal * R.map Complex.ofReal = (σ : ℂ) • (1 - Pm) := by
      rw [← map_ofReal_mul, hGR, map_ofReal_smul, Pm_eq_map, ← map_ofReal_one, ← map_ofReal_sub]
    rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, e1, e2, smul_comm]
  have hμ : (starRingEnd ℂ) (s0 * σ) * (s0 * σ) = 1 := by
    have hs := coord_unit_scalar hns0
    have hσ' : (σ : ℂ) * σ = 1 := by rcases hσ with rfl | rfl <;> simp
    have hσc : (starRingEnd ℂ) (σ : ℂ) = σ := Complex.conj_ofReal σ
    calc (starRingEnd ℂ) (s0 * σ) * (s0 * σ)
        = ((starRingEnd ℂ) s0 * s0) * ((σ : ℂ) * σ) := by rw [map_mul, hσc]; ring
      _ = 1 := by rw [hs, hσ']; norm_num
  have hfinal : ∀ (φ : Psi) (ε' : ℂ), zmat φ = magicB * Xtarget ε' * magicBᵀ →
      s0 • (ε • Pm + (σ : ℂ) • rt6 • (1 - Pm)) = (s0 * σ) • Xtarget ε' → LUEquiv ψ φ := by
    intro φ ε' hφ hform
    have hz : zmat ψ3 = (s0 * σ) • zmat φ := by
      rw [zmat_eq_coord (zmat ψ3), hX3, hform, hφ, Matrix.mul_smul, Matrix.smul_mul]
    have hψ3eq : ψ3 = fun a b c d => (s0 * σ) * φ a b c d := by
      funext a b c d
      have := congrFun (congrFun hz (a, b)) (c, d)
      simpa [zmat] using this
    exact (hL1.trans hL2).trans (hψ3eq ▸ LUEquiv_scalar hμ φ)
  rcases hσ with rfl | rfl <;> rcases hε with h | h
  · left
    refine hfinal M4 (Complex.I * rt) zmat_M4 ?_
    rw [h]; simp only [Xtarget]; push_cast; module
  · right
    refine hfinal (Psi.conj M4) (-(Complex.I * rt)) zmat_M4_conj ?_
    rw [h]; simp only [Xtarget]; push_cast; module
  · right
    refine hfinal (Psi.conj M4) (-(Complex.I * rt)) zmat_M4_conj ?_
    rw [h]; simp only [Xtarget]; push_cast; module
  · left
    refine hfinal M4 (Complex.I * rt) zmat_M4 ?_
    rw [h]; simp only [Xtarget]; push_cast; module

end FormalResearch.FourQubitEntropy
