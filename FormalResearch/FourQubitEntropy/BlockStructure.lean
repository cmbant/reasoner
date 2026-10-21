import FormalResearch.FourQubitEntropy.BlockForm

/-!
# The structure theorem for a critical coordinate matrix with singlet top vector

`X Xᴴ = Xᴴ X = diag(1/6, 1/6, 1/2, 1/6)` and `tr(Xᵀ X) = 0` force
`X = s (ε P + R/√6)` with `|s| = 1`, `ε = ± i/√2` and `R` real, `R Rᵀ = Rᵀ R = 1 - P`.
-/

open scoped ComplexConjugate Matrix

namespace FormalResearch.FourQubitEntropy

theorem S6_gram (Y : Mat4) (hPY : Pm * Y = 0) (hYP : Y * Pm = 0)
    (hYY : Y * Yᴴ = (1 / 6 : ℂ) • (1 - Pm)) (hYtY : Yᴴ * Y = (1 / 6 : ℂ) • (1 - Pm)) :
    ((6 : ℂ) • (Y * Yᵀ)) * ((6 : ℂ) • (Y * Yᵀ))ᴴ = 1 - Pm := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, transpose_conjTranspose]
  have e : Yᵀ * Y.map star = (1 / 6 : ℂ) • (1 - Pm) := by
    have := transpose_mul_map_conj Y
    rw [hYtY, map_conj_smul_one_sub_Pm] at this
    exact this
  calc ((6 : ℂ) • (Y * Yᵀ)) * (star (6 : ℂ) • (Y.map star * Yᴴ))
      = ((6 : ℂ) * star (6 : ℂ)) • (Y * (Yᵀ * Y.map star) * Yᴴ) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
        rw [mul_comm]
    _ = 1 - Pm := by
        rw [e]
        have : Y * ((1 / 6 : ℂ) • (1 - Pm)) * Yᴴ = (1 / 6 : ℂ) • (Y * Yᴴ) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one, hYP, sub_zero]
        rw [this, hYY]
        have h6 : (6 : ℂ) * star (6 : ℂ) = 36 := by simp; norm_num
        rw [h6, smul_smul, smul_smul]
        norm_num

theorem block_structure (X : Mat4) (h1 : X * Xᴴ = Dm) (h2 : Xᴴ * X = Dm)
    (h3 : Matrix.trace (Xᵀ * X) = 0) :
    ∃ (s0 ε : ℂ) (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ),
      Complex.normSq s0 = 1 ∧ (ε = Complex.I * rt ∨ ε = -(Complex.I * rt)) ∧
      R * Rᵀ = 1 - Prm ∧ Rᵀ * R = 1 - Prm ∧
      X = s0 • (ε • Pm + rt6 • R.map Complex.ofReal) := by
  obtain ⟨x0, hx0def⟩ : ∃ x0, x0 = X sing sing := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = blockY X := ⟨_, rfl⟩
  have hPY : Pm * Y = 0 := hYdef ▸ Pm_mul_Y h1 h2
  have hYP : Y * Pm = 0 := hYdef ▸ Y_mul_Pm h1 h2
  have hx0 : x0 * (starRingEnd ℂ) x0 = 1 / 2 := hx0def ▸ x0_normSq h1 h2
  have hX : X = x0 • Pm + Y := by rw [hx0def, hYdef]; unfold blockY; abel
  rw [hX] at h1 h2 h3
  have hYY := Y_gram_left hPY hYP hx0 h1
  have hYtY := Y_gram_right hPY hYP hx0 h2
  have htr := Y_trace hPY hYP h3
  have hS6 := S6_gram Y hPY hYP hYY hYtY
  have hnx : Complex.normSq x0 = 1 / 2 := normSq_x0 hx0
  -- the diagonal lemma
  set lam : ℂ := -2 * (x0 * x0) with hlam
  have hnl : Complex.normSq lam = 1 := by
    have h2 : Complex.normSq (-2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
    rw [hlam, map_mul, map_mul, hnx, h2]; norm_num
  have hS : (6 : ℂ) • (Y * Yᵀ) = lam • (1 - Pm) := by
    apply diag_of_trace _ hS6 lam hnl
    rw [Matrix.trace_smul, htr, hlam, smul_eq_mul]; ring
  have hlam0 : lam ≠ 0 := by
    intro h; rw [h] at hnl; simp at hnl
  have hYYt : Y * Yᵀ = (lam / 6) • (1 - Pm) := by
    have := congrArg (fun M => (1 / 6 : ℂ) • M) hS
    simp only [smul_smul] at this
    rw [show (1 / 6 : ℂ) * 6 = 1 by norm_num, one_smul] at this
    rw [this]; congr 1; ring
  obtain ⟨s0, hs0⟩ := IsAlgClosed.exists_pow_nat_eq lam (show 0 < 2 by norm_num)
  have hs0ne : s0 ≠ 0 := by
    intro h; rw [h] at hs0; apply hlam0; rw [← hs0]; norm_num
  have hns0 : Complex.normSq s0 = 1 := by
    have h : Complex.normSq s0 ^ 2 = 1 := by rw [← map_pow, hs0, hnl]
    nlinarith [Complex.normSq_nonneg s0]
  have hsc : s0 * (starRingEnd ℂ) s0 = 1 := by
    rw [Complex.mul_conj, hns0]; simp
  -- the normalised block
  set c : ℂ := ((Real.sqrt 6 : ℝ) : ℂ) * s0⁻¹ with hc
  have h6 : ((Real.sqrt 6 : ℝ) : ℂ) ^ 2 = 6 := by
    have h : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
    rw [pow_two]; exact_mod_cast h
  set Rc : Mat4 := c • Y with hRc
  have hcc : c * c = 6 / lam := by
    rw [hc]; field_simp; rw [h6, ← hs0]; ring
  have hcconj : c * (starRingEnd ℂ) c = 6 := by
    rw [hc, map_mul, map_inv₀, Complex.conj_ofReal]
    have : (starRingEnd ℂ) s0 = s0⁻¹ := (inv_eq_of_mul_eq_one_right hsc).symm
    rw [this, inv_inv]
    field_simp; rw [h6]
  have hR1 : Rc * Rcᵀ = 1 - Pm := by
    rw [hRc, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hYYt, smul_smul,
      hcc]
    have : 6 / lam * (lam / 6) = 1 := by field_simp
    rw [this, one_smul]
  have hR2 : Rc * Rcᴴ = 1 - Pm := by
    rw [hRc, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hYY, smul_smul]
    have : c * star c * (1 / 6) = 1 := by
      have : c * star c = 6 := hcconj
      rw [this]; norm_num
    rw [this, one_smul]
  have hR3 : Rcᴴ * Rc = 1 - Pm := by
    rw [hRc, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hYtY, smul_smul]
    have : star c * c * (1 / 6) = 1 := by
      have : star c * c = 6 := by rw [mul_comm]; exact hcconj
      rw [this]; norm_num
    rw [this, one_smul]
  have hreal := real_of_orth Rc hR1 hR2
  obtain ⟨R, hRR⟩ : ∃ R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, Rc = R.map Complex.ofReal :=
    ⟨Matrix.of fun j k => (Rc j k).re, by
      ext j k; apply Complex.ext <;> simp [hreal j k]⟩
  have hinj : ∀ A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ,
      A.map Complex.ofReal = B.map Complex.ofReal → A = B := fun A B h => by
    ext j k
    have := congrFun (congrFun h j) k
    simpa using this
  have hPm : (1 - Pm : Mat4) = (1 - Prm).map Complex.ofReal := by
    rw [Pm_eq_map]; ext j k; by_cases h : j = k <;> simp [Matrix.one_apply, h]
  have hRRt : R * Rᵀ = 1 - Prm := by
    apply hinj
    have e : (R * Rᵀ).map Complex.ofReal = R.map Complex.ofReal * (R.map Complex.ofReal)ᵀ := by
      ext j k; simp [Matrix.mul_apply, Matrix.transpose_apply]
    rw [e, ← hRR, hR1, hPm]
  have hRtR : Rᵀ * R = 1 - Prm := by
    apply hinj
    have e : (Rᵀ * R).map Complex.ofReal = (R.map Complex.ofReal)ᴴ * R.map Complex.ofReal := by
      ext j k; simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    rw [e, ← hRR, hR3, hPm]
  -- the top coordinate
  have hx0ne : x0 ≠ 0 := by
    intro h; rw [h] at hnx; simp at hnx
  have hx2 : x0 * x0 = -(s0 ^ 2) / 2 := by rw [hs0, hlam]; ring
  set ε : ℂ := x0 * s0⁻¹ with hε
  have hε2 : ε * ε = -(1 / 2) := by
    rw [hε]
    have : (x0 * s0⁻¹) * (x0 * s0⁻¹) = (x0 * x0) / s0 ^ 2 := by field_simp
    rw [this, hx2]; field_simp
  have hI : (Complex.I * rt) * (Complex.I * rt) = -(1 / 2) := by
    have := rt_mul_rt
    calc (Complex.I * rt) * (Complex.I * rt) = (Complex.I * Complex.I) * (rt * rt) := by ring
      _ = -(1 / 2) := by rw [this, Complex.I_mul_I]; norm_num
  have hεcases : ε = Complex.I * rt ∨ ε = -(Complex.I * rt) := by
    have : (ε - Complex.I * rt) * (ε + Complex.I * rt) = 0 := by
      linear_combination hε2 - hI
    rcases mul_eq_zero.1 this with h | h
    · left; exact sub_eq_zero.1 h
    · right; exact eq_neg_of_add_eq_zero_left h
  refine ⟨s0, ε, R, hns0, hεcases, hRRt, hRtR, ?_⟩
  have hx0eq : x0 = s0 * ε := by rw [hε]; field_simp
  have hYeq : Y = (s0 * rt6) • Rc := by
    rw [hRc, smul_smul]
    have : s0 * rt6 * c = 1 := by
      rw [hc, rt6]
      have : ((Real.sqrt 6 : ℝ) : ℂ) ≠ 0 := by
        intro h
        have h0 : Real.sqrt 6 = 0 := by exact_mod_cast h
        have : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
        linarith
      field_simp
    rw [this, one_smul]
  rw [hX, hx0eq, hYeq, ← hRR, smul_add, smul_smul, smul_smul]
  simp only [hRc, smul_smul, mul_assoc]

end FormalResearch.FourQubitEntropy
