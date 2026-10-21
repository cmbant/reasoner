import FormalResearch.FourQubitEntropy.Attainment

/-!
# The equality case, first half: what entropy equality forces

If a unit vector attains the entropy bound, then `P = 1` (so `W₁ = 0` and `τ = 0`), `F = 0`, and
each cut's reduced matrix satisfies `(R - 1/6)(R - 1/2) = 0`.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

theorem quadratic_of_eigenvalues {R : Mat4} (hR : R.IsHermitian)
    (h : ∀ i, hR.eigenvalues i = 1 / 6 ∨ hR.eigenvalues i = 1 / 2) :
    (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0 := by
  have h1 : star (eigU hR) * eigU hR = 1 := Unitary.coe_star_mul_self hR.eigenvectorUnitary
  have h0 : eigU hR * star (eigU hR) = 1 := Unitary.coe_mul_star_self hR.eigenvectorUnitary
  have hspec : R = eigU hR * Matrix.diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ)) *
      star (eigU hR) := by
    have := hR.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  set U := eigU hR
  set D : Mat4 := Matrix.diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ))
  have hshift : ∀ c : ℂ, R - c • 1 = U * (D - c • 1) * star U := by
    intro c
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h0, ← hspec]
  have hdiag : ∀ c : ℂ, D - c • 1 = Matrix.diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ) - c) := by
    intro c
    ext i j
    by_cases hij : i = j
    · subst hij; simp [D]
    · simp [D, hij, Matrix.one_apply, Matrix.diagonal_apply]
  rw [hshift, hshift, hdiag, hdiag]
  calc U * Matrix.diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ) - 1 / 6) * star U *
        (U * Matrix.diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ) - 1 / 2) * star U)
      = U * (Matrix.diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ) - 1 / 6) *
          (star U * U) * Matrix.diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ) - 1 / 2)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by
        rw [h1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        have : (fun i => (((hR.eigenvalues i : ℝ) : ℂ) - 1 / 6) * (((hR.eigenvalues i : ℝ) : ℂ) - 1 / 2))
            = fun _ => (0 : ℂ) := by
          funext i
          rcases h i with h | h <;> simp [h] <;> norm_num
        rw [this]; simp

/-- The Hermite cubic summed over a cut's spectrum. -/
theorem cut_cubic_sum {R : Mat4} (hR : R.IsHermitian) :
    ∑ i, hermCubic (hR.eigenvalues i)
      = hermA * (Matrix.trace (R * R * R)).re + hermB * (Matrix.trace (R * R)).re
        + hermC * (Matrix.trace R).re + 4 * hermD := by
  have e3 : ∑ i, hR.eigenvalues i ^ 3 = (Matrix.trace (R * R * R)).re := by
    rw [sum_eigenvalues_pow hR 3, pow_succ, pow_two]
  have e2 : ∑ i, hR.eigenvalues i ^ 2 = (Matrix.trace (R * R)).re := by
    rw [sum_eigenvalues_pow hR 2, pow_two]
  have e1 : ∑ i, hR.eigenvalues i = (Matrix.trace R).re := by
    simpa using sum_eigenvalues_pow hR 1
  simp only [hermCubic, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e3, e2, e1]
  simp

/-- The slack of the cubic majorant on a cut's spectrum. -/
noncomputable def cutSlack {R : Mat4} (hR : R.IsHermitian) : ℝ :=
  ∑ i, (hermCubic (hR.eigenvalues i) - Real.negMulLog (hR.eigenvalues i))

theorem cutSlack_nonneg {R : Mat4} (hR : R.IsHermitian) (hp : R.PosSemidef) :
    0 ≤ cutSlack hR :=
  Finset.sum_nonneg fun i _ => sub_nonneg.2 (negMulLog_le_hermCubic (hp.eigenvalues_nonneg i))

theorem cutSlack_eq_zero {R : Mat4} (hR : R.IsHermitian) (hp : R.PosSemidef)
    (h : cutSlack hR = 0) (i : Fin 2 × Fin 2) :
    hR.eigenvalues i = 1 / 6 ∨ hR.eigenvalues i = 1 / 2 := by
  have hterm : ∀ j ∈ Finset.univ, 0 ≤ hermCubic (hR.eigenvalues j) - Real.negMulLog (hR.eigenvalues j) :=
    fun j _ => sub_nonneg.2 (negMulLog_le_hermCubic (hp.eigenvalues_nonneg j))
  have := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 h i (Finset.mem_univ i)
  exact negMulLog_eq_hermCubic (hp.eigenvalues_nonneg i) (by linarith)

/-- **What entropy equality forces.** -/
theorem equality_conditions (ψ : Psi) (hψ : normSqPsi ψ = 1)
    (heq : meanEntropy ψ = 1 + Real.log 3 / (2 * Real.log 2)) :
    purity ψ = 1 ∧
      (∀ i, (red12_herm ψ).eigenvalues i = 1 / 6 ∨ (red12_herm ψ).eigenvalues i = 1 / 2) ∧
      (∀ i, (red13_herm ψ).eigenvalues i = 1 / 6 ∨ (red13_herm ψ).eigenvalues i = 1 / 2) ∧
      (∀ i, (red14_herm ψ).eigenvalues i = 1 / 6 ∨ (red14_herm ψ).eigenvalues i = 1 / 2) := by
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l3a := lt_log_three
  have l3b := log_three_lt
  have hA := hermA_pos
  have hP := purity_ge ψ
  have hF := sexticF_nonneg ψ
  rw [hψ] at hP
  have hT : sexticF ψ = 17 * purity ψ - 12 * cubicMoment ψ - 12 := by
    unfold sexticF; rw [hψ]; ring
  -- total entropy sum
  have hS : (∑ i, Real.negMulLog ((red12_herm ψ).eigenvalues i))
      + (∑ i, Real.negMulLog ((red13_herm ψ).eigenvalues i))
      + (∑ i, Real.negMulLog ((red14_herm ψ).eigenvalues i))
      = 3 * Real.log 2 + 3 / 2 * Real.log 3 := by
    unfold meanEntropy vnEntropy at heq
    rw [← add_div, ← add_div, div_div, div_eq_iff (by positivity)] at heq
    rw [heq]; field_simp
  -- the cubic sums
  have t12 : (Matrix.trace (red12 ψ)).re = 1 := by rw [trace_red12, hψ]; simp
  have t13 : (Matrix.trace (red13 ψ)).re = 1 := by rw [trace_red13, hψ]; simp
  have t14 : (Matrix.trace (red14 ψ)).re = 1 := by rw [trace_red14, hψ]; simp
  have c12 := cut_cubic_sum (red12_herm ψ)
  have c13 := cut_cubic_sum (red13_herm ψ)
  have c14 := cut_cubic_sum (red14_herm ψ)
  rw [t12] at c12
  rw [t13] at c13
  rw [t14] at c14
  have s12 : cutSlack (red12_herm ψ) = (hermA * (Matrix.trace (red12 ψ * red12 ψ * red12 ψ)).re
      + hermB * (Matrix.trace (red12 ψ * red12 ψ)).re + hermC * 1 + 4 * hermD)
      - ∑ i, Real.negMulLog ((red12_herm ψ).eigenvalues i) := by
    unfold cutSlack; rw [Finset.sum_sub_distrib, c12]
  have s13 : cutSlack (red13_herm ψ) = (hermA * (Matrix.trace (red13 ψ * red13 ψ * red13 ψ)).re
      + hermB * (Matrix.trace (red13 ψ * red13 ψ)).re + hermC * 1 + 4 * hermD)
      - ∑ i, Real.negMulLog ((red13_herm ψ).eigenvalues i) := by
    unfold cutSlack; rw [Finset.sum_sub_distrib, c13]
  have s14 : cutSlack (red14_herm ψ) = (hermA * (Matrix.trace (red14 ψ * red14 ψ * red14 ψ)).re
      + hermB * (Matrix.trace (red14 ψ * red14 ψ)).re + hermC * 1 + 4 * hermD)
      - ∑ i, Real.negMulLog ((red14_herm ψ).eigenvalues i) := by
    unfold cutSlack; rw [Finset.sum_sub_distrib, c14]
  have n12 := cutSlack_nonneg (red12_herm ψ) (red12_psd ψ)
  have n13 := cutSlack_nonneg (red13_herm ψ) (red13_psd ψ)
  have n14 := cutSlack_nonneg (red14_herm ψ) (red14_psd ψ)
  have hb : 0 < -(hermB + 17 / 12 * hermA) := by unfold hermB hermA; linarith
  have hP' : 0 ≤ purity ψ - 1 := by linarith
  have k1 := mul_nonneg hA.le hF
  have k2 := mul_nonneg hb.le hP'
  -- the identity: slack total = k2 + k1/12
  have hc : cubicMoment ψ = (17 * purity ψ - 12 - sexticF ψ) / 12 := by linarith
  have hid : hermB + 5 / 12 * hermA + 3 * hermC + 12 * hermD = 3 * Real.log 2 + 3 / 2 * Real.log 3 := by
    unfold hermA hermB hermC hermD; ring
  have hcm : cubicMoment ψ = (Matrix.trace (red12 ψ * red12 ψ * red12 ψ)).re
      + (Matrix.trace (red13 ψ * red13 ψ * red13 ψ)).re
      + (Matrix.trace (red14 ψ * red14 ψ * red14 ψ)).re := rfl
  have hpu : purity ψ = (Matrix.trace (red12 ψ * red12 ψ)).re + (Matrix.trace (red13 ψ * red13 ψ)).re
      + (Matrix.trace (red14 ψ * red14 ψ)).re := rfl
  have tot : cutSlack (red12_herm ψ) + cutSlack (red13_herm ψ) + cutSlack (red14_herm ψ)
      + (-(hermB + 17 / 12 * hermA)) * (purity ψ - 1) + hermA * sexticF ψ / 12 = 0 := by
    rw [s12, s13, s14]
    rw [hcm] at hc
    rw [hpu] at hc ⊢
    linear_combination (-1 : ℝ) * hS + hermA * hc + hid
  have hz2 : (-(hermB + 17 / 12 * hermA)) * (purity ψ - 1) = 0 := by linarith
  have hz12 : cutSlack (red12_herm ψ) = 0 := by linarith
  have hz13 : cutSlack (red13_herm ψ) = 0 := by linarith
  have hz14 : cutSlack (red14_herm ψ) = 0 := by linarith
  refine ⟨?_, cutSlack_eq_zero _ (red12_psd ψ) hz12, cutSlack_eq_zero _ (red13_psd ψ) hz13,
    cutSlack_eq_zero _ (red14_psd ψ) hz14⟩
  rcases mul_eq_zero.1 hz2 with h | h
  · exact absurd h hb.ne'
  · linarith

end FormalResearch.FourQubitEntropy
