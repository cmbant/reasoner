import FormalResearch.FourQubitEntropy.Normalize
import FormalResearch.FourQubitEntropy.BlockStructure
import FormalResearch.FourQubitEntropy.Realize

/-!
# Classification of the maximisers
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

theorem sv_conj (p : Fin 2 × Fin 2) : (starRingEnd ℂ) (sv p) = sv p := by
  obtain ⟨a, b⟩ := p
  rw [sv_apply]; simp [map_mul, rt_conj]
  fin_cases a <;> fin_cases b <;> simp [eps2]

theorem projVec_sv_eq_B : projVec sv = magicB * Pm * magicBᴴ := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [projVec, sv, magicB, Pm_apply, sing, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, rt_conj]

theorem projVec_sv_eq_Bbar : projVec sv = magicB.map (starRingEnd ℂ) * Pm * magicBᵀ := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [projVec, sv, magicB, Pm_apply, sing, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, rt_conj]

theorem Gs_coord_left : magicBᴴ * Gs * magicB = Dm := by
  unfold Gs
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, magicB_unitary, projVec_sv_eq_B]
  have : magicBᴴ * (magicB * Pm * magicBᴴ) * magicB = Pm := by
    calc magicBᴴ * (magicB * Pm * magicBᴴ) * magicB
        = (magicBᴴ * magicB) * Pm * (magicBᴴ * magicB) := by simp only [Matrix.mul_assoc]
      _ = Pm := by rw [magicB_unitary]; simp
  rw [this, Dm_eq]
  have e : (1 : Mat4) = Pm + (1 - Pm) := by abel
  conv_rhs => rw [← sub_add_cancel (1 : Mat4) Pm]
  module

theorem Gs_coord_right : magicBᵀ * Gs * magicB.map (starRingEnd ℂ) = Dm := by
  unfold Gs
  have h1 : magicBᵀ * magicB.map (starRingEnd ℂ) = 1 := unitary_transpose_mul magicB_unitary
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, h1, projVec_sv_eq_Bbar]
  have : magicBᵀ * (magicB.map (starRingEnd ℂ) * Pm * magicBᵀ) * magicB.map (starRingEnd ℂ) = Pm := by
    calc magicBᵀ * (magicB.map (starRingEnd ℂ) * Pm * magicBᵀ) * magicB.map (starRingEnd ℂ)
        = (magicBᵀ * magicB.map (starRingEnd ℂ)) * Pm * (magicBᵀ * magicB.map (starRingEnd ℂ)) := by
          simp only [Matrix.mul_assoc]
      _ = Pm := by rw [h1]; simp
  rw [this, Dm_eq]
  conv_rhs => rw [← sub_add_cancel (1 : Mat4) Pm]
  module

theorem coord_of_eq {Z X : Mat4} (h : Z = magicB * X * magicBᵀ) : magicCoord Z = X := by
  unfold magicCoord
  rw [h]
  calc magicBᴴ * (magicB * X * magicBᵀ) * magicB.map (starRingEnd ℂ)
      = (magicBᴴ * magicB) * X * (magicBᵀ * magicB.map (starRingEnd ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = X := by
        have h1 : magicBᵀ * magicB.map (starRingEnd ℂ) = 1 := unitary_transpose_mul magicB_unitary
        rw [magicB_unitary, h1]; simp

/-- The coordinate matrix of `M₄`: `diag(1/√6, 1/√6, i/√2, 1/√6)`. -/
noncomputable def Xtarget (ε : ℂ) : Mat4 := ε • Pm + rt6 • (1 - Pm)

theorem rt6_eq_real : rt6 = (((1 / Real.sqrt 6 : ℝ)) : ℂ) := by
  unfold rt6; push_cast; ring

theorem sqrt3_rt6 : (Real.sqrt 3 : ℝ) * (1 / Real.sqrt 6) = 1 / Real.sqrt 2 := by
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [h6]; field_simp

theorem omega_eq : omega = -1 / 2 + (((Real.sqrt 3 : ℝ) : ℂ) / 2) * Complex.I := by
  apply Complex.ext <;> simp [omega]

theorem omega_conj_eq : (starRingEnd ℂ) omega = -1 / 2 - (((Real.sqrt 3 : ℝ) : ℂ) / 2) * Complex.I := by
  rw [omega_eq]; simp [map_add, map_mul, map_div₀, map_ofNat]; ring

theorem M4_apply (a b c d : Fin 2) : M4 a b c d = rt6 * (if (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨ (a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 0) then 1
     else if (a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 0) then omega
     else if (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) then (starRingEnd ℂ) omega
     else 0) := by
  unfold M4; rw [rt6_eq_real]

set_option maxHeartbeats 8000000 in
theorem zmat_M4 : zmat M4 = magicB * Xtarget (Complex.I * rt) * magicBᵀ := by
  have hr := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact hr
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) * rt6 = rt := by
    rw [rt6_eq_real]; unfold rt; rw [← Complex.ofReal_mul, sqrt3_rt6]; push_cast; ring
  have hrt3 : rt ^ 3 = rt / 2 := by rw [show rt ^ 3 = rt * rt ^ 2 by ring, hrt2]; ring
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [zmat, M4_apply, Xtarget, Pm_apply, sing, magicB, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, omega_eq, omega_conj_eq, map_ofNat]
  all_goals (try ring_nf)
  all_goals (try simp only [Complex.I_sq, hrt2])
  all_goals (try ring_nf)
  all_goals (try rw [hrt3])
  all_goals (first | done | linear_combination (Complex.I / 2) * h3 | linear_combination (-(Complex.I) / 2) * h3)

theorem M4_conj_apply (a b c d : Fin 2) : Psi.conj M4 a b c d = rt6 * (if (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨ (a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 0) then 1
     else if (a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 0) then (starRingEnd ℂ) omega
     else if (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) then omega
     else 0) := by
  have hr6 : (starRingEnd ℂ) rt6 = rt6 := by rw [rt6_eq_real]; exact Complex.conj_ofReal _
  unfold Psi.conj
  rw [M4_apply, map_mul, hr6]
  congr 1
  split_ifs <;> simp

set_option maxHeartbeats 8000000 in
theorem zmat_M4_conj : zmat (Psi.conj M4) = magicB * Xtarget (-(Complex.I * rt)) * magicBᵀ := by
  have hr := rt_mul_rt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact hr
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) * rt6 = rt := by
    rw [rt6_eq_real]; unfold rt; rw [← Complex.ofReal_mul, sqrt3_rt6]; push_cast; ring
  have hrt3 : rt ^ 3 = rt / 2 := by rw [show rt ^ 3 = rt * rt ^ 2 by ring, hrt2]; ring
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [zmat, M4_conj_apply, Xtarget, Pm_apply, sing, magicB, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, omega_eq, omega_conj_eq, map_ofNat]
  all_goals (try ring_nf)
  all_goals (try simp only [Complex.I_sq, hrt2])
  all_goals (try ring_nf)
  all_goals (try rw [hrt3])
  all_goals (first | done | linear_combination (Complex.I / 2) * h3 | linear_combination (-(Complex.I) / 2) * h3)

/-! ### Composition of local unitaries -/

theorem LUEquiv.trans {ψ φ χ : Psi} (h1 : LUEquiv ψ φ) (h2 : LUEquiv φ χ) : LUEquiv ψ χ := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h1
  obtain ⟨a', b', c', d', ha', hb', hc', hd', rfl⟩ := h2
  refine ⟨a' * a, b' * b, c' * c, d' * d, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc aᴴ * a'ᴴ * (a' * a) = aᴴ * (a'ᴴ * a') * a := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha', Matrix.mul_one, ha]
  · rw [Matrix.conjTranspose_mul]
    calc bᴴ * b'ᴴ * (b' * b) = bᴴ * (b'ᴴ * b') * b := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hb', Matrix.mul_one, hb]
  · rw [Matrix.conjTranspose_mul]
    calc cᴴ * c'ᴴ * (c' * c) = cᴴ * (c'ᴴ * c') * c := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc', Matrix.mul_one, hc]
  · rw [Matrix.conjTranspose_mul]
    calc dᴴ * d'ᴴ * (d' * d) = dᴴ * (d'ᴴ * d') * d := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hd', Matrix.mul_one, hd]
  · rw [localApply_comp]

theorem LUEquiv.refl (ψ : Psi) : LUEquiv ψ ψ :=
  ⟨1, 1, 1, 1, by simp, by simp, by simp, by simp, localApply_one ψ⟩

theorem localApply_rows (a b : Op1) (ψ : Psi) : localApply a b 1 1 ψ = rowLU (kron a b) ψ := by
  unfold localApply
  rw [kron_one, ← ofZmat_zmat (colLU 1 (rowLU (kron a b) ψ))]
  rw [zmat_colLU]; simp

theorem LUEquiv_rows {a b : Op1} (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) (ψ : Psi) :
    LUEquiv ψ (rowLU (kron a b) ψ) :=
  ⟨a, b, 1, 1, ha, hb, by simp, by simp, localApply_rows a b ψ⟩

theorem LUEquiv_scalar {μ : ℂ} (hμ : (starRingEnd ℂ) μ * μ = 1) (φ : Psi) :
    LUEquiv (fun a b c d => μ * φ a b c d) φ := by
  refine ⟨(starRingEnd ℂ) μ • 1, 1, 1, 1, ?_, by simp, by simp, by simp, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : star ((starRingEnd ℂ) μ) * (starRingEnd ℂ) μ = 1 := by
      rw [mul_comm]; simpa using hμ
    rw [this]; simp
  · funext p q r s
    simp only [localApply_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases s <;> simp [← mul_assoc, hμ]

end FormalResearch.FourQubitEntropy
