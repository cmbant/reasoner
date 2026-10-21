import FormalResearch.FourQubitEntropy.Entropy

/-!
# `M₄` attains the entropy bound

`M₄ = (|0011⟩ + |1100⟩ + ω(|0101⟩ + |1010⟩) + ω²(|0110⟩ + |1001⟩))/√6`, `ω = e^{2πi/3}`. Each of its
three marginals `R` satisfies `(R - 1/6)(R - 1/2) = 0` and has trace `1`, so its spectrum is
`{1/2, 1/6, 1/6, 1/6}` and `-λ ln λ` is affine on it.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

/-- `ω = e^{2πi/3}`. -/
noncomputable def omega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem omega_sq : omega * omega = conj omega := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;> simp [omega] <;> nlinarith

theorem omega_mul_conj : omega * conj omega = 1 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;> simp [omega] <;> nlinarith

/-- The vector `M₄`. -/
noncomputable def M4 : Psi := fun a b c d =>
  (1 / Real.sqrt 6 : ℝ) *
    (if (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨ (a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 0) then 1
     else if (a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 0) then omega
     else if (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) then conj omega
     else 0)

theorem M4_unit : normSqPsi M4 = 1 := by
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have hω : Complex.normSq omega = 1 := by
    have := omega_mul_conj
    rw [Complex.mul_conj] at this
    exact_mod_cast this
  simp [normSqPsi, M4, Fin.sum_univ_two, Complex.normSq_mul, Complex.normSq_conj, hω]
  field_simp
  nlinarith

theorem omega_sq_add : omega ^ 2 + omega + 1 = 0 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;> simp [omega, pow_two] <;> nlinarith

theorem conj_omega : conj omega = omega ^ 2 := by rw [pow_two, omega_sq]

/-- Reduction of powers of `ω` and of `1/√6` for the `M₄` computations. -/
theorem omega_pow3 : omega ^ 3 = 1 := by
  linear_combination (omega - 1) * omega_sq_add
theorem omega_pow4 : omega ^ 4 = omega := by
  linear_combination (omega ^ 2 - omega) * omega_sq_add
theorem omega_pow5 : omega ^ 5 = omega ^ 2 := by
  linear_combination (omega ^ 3 - omega ^ 2) * omega_sq_add

theorem omega_pow_red (n : ℕ) : omega ^ n = omega ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, omega_pow3, one_pow, one_mul]

theorem sqrt6_inv_sq : ((Real.sqrt 6 : ℂ))⁻¹ ^ 2 = 1 / 6 := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem red12_M4 : (red12 M4 - (1 / 6 : ℂ) • 1) * (red12 M4 - (1 / 2 : ℂ) • 1) = 0 := by
  have h2 := sqrt6_inv_sq
  have h4 : ((Real.sqrt 6 : ℂ))⁻¹ ^ 4 = 1 / 36 := by
    have : ((Real.sqrt 6 : ℂ))⁻¹ ^ 4 = (((Real.sqrt 6 : ℂ))⁻¹ ^ 2) ^ 2 := by ring
    rw [this, h2]; norm_num
  have p3 := omega_pow3
  have p4 := omega_pow4
  have p5 := omega_pow5
  have p2 : omega ^ 2 = -omega - 1 := by linear_combination omega_sq_add
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, red12, M4, Fintype.sum_prod_type,
    Fin.sum_univ_two, conj_omega] <;>
  ring_nf <;>
  simp only [h2, h4, omega_pow_red 3, omega_pow_red 4, omega_pow_red 5, omega_pow_red 6,
    omega_pow_red 7, omega_pow_red 8, omega_pow_red 9, omega_pow_red 10, omega_pow_red 11,
    omega_pow_red 12, Nat.reduceMod, pow_zero, pow_one, p2] <;>
  ring_nf
  all_goals simp


theorem red13_M4 : (red13 M4 - (1 / 6 : ℂ) • 1) * (red13 M4 - (1 / 2 : ℂ) • 1) = 0 := by
  have h2 := sqrt6_inv_sq
  have h4 : ((Real.sqrt 6 : ℂ))⁻¹ ^ 4 = 1 / 36 := by
    have : ((Real.sqrt 6 : ℂ))⁻¹ ^ 4 = (((Real.sqrt 6 : ℂ))⁻¹ ^ 2) ^ 2 := by ring
    rw [this, h2]; norm_num
  have p3 := omega_pow3
  have p4 := omega_pow4
  have p5 := omega_pow5
  have p2 : omega ^ 2 = -omega - 1 := by linear_combination omega_sq_add
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, red13, M4, Fintype.sum_prod_type,
    Fin.sum_univ_two, conj_omega] <;>
  ring_nf <;>
  simp only [h2, h4, omega_pow_red 3, omega_pow_red 4, omega_pow_red 5, omega_pow_red 6,
    omega_pow_red 7, omega_pow_red 8, omega_pow_red 9, omega_pow_red 10, omega_pow_red 11,
    omega_pow_red 12, Nat.reduceMod, pow_zero, pow_one, p2] <;>
  ring_nf
  all_goals simp


theorem red14_M4 : (red14 M4 - (1 / 6 : ℂ) • 1) * (red14 M4 - (1 / 2 : ℂ) • 1) = 0 := by
  have h2 := sqrt6_inv_sq
  have h4 : ((Real.sqrt 6 : ℂ))⁻¹ ^ 4 = 1 / 36 := by
    have : ((Real.sqrt 6 : ℂ))⁻¹ ^ 4 = (((Real.sqrt 6 : ℂ))⁻¹ ^ 2) ^ 2 := by ring
    rw [this, h2]; norm_num
  have p3 := omega_pow3
  have p4 := omega_pow4
  have p5 := omega_pow5
  have p2 : omega ^ 2 = -omega - 1 := by linear_combination omega_sq_add
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, red14, M4, Fintype.sum_prod_type,
    Fin.sum_univ_two, conj_omega] <;>
  ring_nf <;>
  simp only [h2, h4, omega_pow_red 3, omega_pow_red 4, omega_pow_red 5, omega_pow_red 6,
    omega_pow_red 7, omega_pow_red 8, omega_pow_red 9, omega_pow_red 10, omega_pow_red 11,
    omega_pow_red 12, Nat.reduceMod, pow_zero, pow_one, p2] <;>
  ring_nf
  all_goals simp


/-- A Hermitian `R` with `(R - 1/6)(R - 1/2) = 0` has eigenvalues in `{1/6, 1/2}`. -/
theorem eigenvalue_of_quadratic {R : Mat4} (hR : R.IsHermitian)
    (h : (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0) (i : Fin 2 × Fin 2) :
    hR.eigenvalues i = 1 / 6 ∨ hR.eigenvalues i = 1 / 2 := by
  have hv0 := hR.mulVec_eigenvectorBasis i
  set v : Fin 2 × Fin 2 → ℂ := ⇑(hR.eigenvectorBasis i) with hvdef
  have hv : R *ᵥ v = ((hR.eigenvalues i : ℝ) : ℂ) • v := by
    rw [hv0]; exact (Complex.coe_smul _ _).symm
  have hne : v ≠ 0 := by
    have := hR.eigenvectorBasis.orthonormal.ne_zero i
    intro h0; apply this; ext j; exact congrFun h0 j
  have key : ((((hR.eigenvalues i : ℝ) : ℂ) - 1 / 6) * (((hR.eigenvalues i : ℝ) : ℂ) - 1 / 2)) • v = 0 := by
    have e1 : (R - (1 / 2 : ℂ) • 1) *ᵥ v = (((hR.eigenvalues i : ℝ) : ℂ) - 1 / 2) • v := by
      rw [Matrix.sub_mulVec, hv, Matrix.smul_mulVec, Matrix.one_mulVec]; module
    have e2 : (R - (1 / 6 : ℂ) • 1) *ᵥ ((((hR.eigenvalues i : ℝ) : ℂ) - 1 / 2) • v)
        = ((((hR.eigenvalues i : ℝ) : ℂ) - 1 / 6) * (((hR.eigenvalues i : ℝ) : ℂ) - 1 / 2)) • v := by
      rw [Matrix.mulVec_smul, Matrix.sub_mulVec, hv, Matrix.smul_mulVec, Matrix.one_mulVec]
      module
    rw [← e2, ← e1, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]
  rcases smul_eq_zero.mp key with hz | hz
  · rcases mul_eq_zero.mp hz with h1 | h2
    · left
      have h' : ((hR.eigenvalues i : ℝ) : ℂ) = ((1 / 6 : ℝ) : ℂ) := by
        rw [sub_eq_zero.mp h1]; push_cast; ring
      exact_mod_cast h'
    · right
      have h' : ((hR.eigenvalues i : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
        rw [sub_eq_zero.mp h2]; push_cast; ring
      exact_mod_cast h'
  · exact absurd hz hne

/-- The entropy sum of a unit Hermitian matrix with spectrum in `{1/6, 1/2}`. -/
theorem entropy_sum_of_quadratic {R : Mat4} (hR : R.IsHermitian)
    (h : (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0) (htr : (Matrix.trace R).re = 1) :
    ∑ i, Real.negMulLog (hR.eigenvalues i) = Real.log 2 + Real.log 3 / 2 := by
  have hf : ∀ i, Real.negMulLog (hR.eigenvalues i)
      = (Real.log 2 - Real.log 3 / 2) * hR.eigenvalues i + Real.log 3 / 4 := by
    intro i
    rcases eigenvalue_of_quadratic hR h i with h1 | h1 <;> rw [h1]
    · rw [Real.negMulLog, one_div, Real.log_inv, show (6 : ℝ) = 2 * 3 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      ring
    · rw [Real.negMulLog, one_div, Real.log_inv]
      ring
  have hs : ∑ i, hR.eigenvalues i = 1 := by
    have := sum_eigenvalues_pow hR 1
    simp only [pow_one] at this
    rw [this, htr]
  simp only [hf, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
  simp
  ring

theorem meanEntropy_M4 : meanEntropy M4 = 1 + Real.log 3 / (2 * Real.log 2) := by
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have t12 : (Matrix.trace (red12 M4)).re = 1 := by rw [trace_red12, M4_unit]; simp
  have t13 : (Matrix.trace (red13 M4)).re = 1 := by rw [trace_red13, M4_unit]; simp
  have t14 : (Matrix.trace (red14 M4)).re = 1 := by rw [trace_red14, M4_unit]; simp
  unfold meanEntropy vnEntropy
  rw [entropy_sum_of_quadratic _ red12_M4 t12, entropy_sum_of_quadratic _ red13_M4 t13,
    entropy_sum_of_quadratic _ red14_M4 t14]
  field_simp
  ring

/-- The entropy bound is attained: `M₄` is a maximiser. -/
theorem meanEntropy_M4_max (ψ : Psi) (hψ : normSqPsi ψ = 1) : meanEntropy ψ ≤ meanEntropy M4 := by
  rw [meanEntropy_M4]; exact meanEntropy_le ψ hψ

end FormalResearch.FourQubitEntropy
