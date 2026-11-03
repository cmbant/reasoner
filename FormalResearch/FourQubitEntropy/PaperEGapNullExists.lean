module

public import FormalResearch.FourQubitEntropy.PaperEGapNullBloch

/-!
# Null-critical states: existence of the product factorisation

A unit critical normal vector `v` with `Σ v_k² = 0` is `v = B†(a ⊗ b)` for unit `a, b` (`exists_vOf`), the
auxiliary-qubit factorisation of `critical_orbit_stability.tex`: `w = B v` has coefficient matrix of
determinant `Σ v_k²/2`.
-/

@[expose] public section


set_option linter.unusedSimpArgs false

open scoped ComplexConjugate

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- A `2×2` complex matrix of determinant zero and unit Frobenius norm is a product `a bᵀ` of unit vectors. -/
theorem factor2 (W00 W01 W10 W11 : ℂ) (hd : W00 * W11 = W01 * W10)
    (hn : Complex.normSq W00 + Complex.normSq W01 + Complex.normSq W10 + Complex.normSq W11 = 1) :
    ∃ a0 a1 b0 b1 : ℂ, Complex.normSq a0 + Complex.normSq a1 = 1 ∧
      Complex.normSq b0 + Complex.normSq b1 = 1 ∧
      a0 * b0 = W00 ∧ a0 * b1 = W01 ∧ a1 * b0 = W10 ∧ a1 * b1 = W11 := by
  by_cases h : Complex.normSq W00 + Complex.normSq W01 = 0
  · have h0 : Complex.normSq W00 = 0 := by
      have := Complex.normSq_nonneg W00; have := Complex.normSq_nonneg W01; linarith
    have h1 : Complex.normSq W01 = 0 := by
      have := Complex.normSq_nonneg W00; have := Complex.normSq_nonneg W01; linarith
    have e0 := Complex.normSq_eq_zero.mp h0
    have e1 := Complex.normSq_eq_zero.mp h1
    refine ⟨0, 1, W10, W11, by simp, by linarith, by simp [e0], by simp [e1], by simp, by simp⟩
  · have hpos : 0 < Complex.normSq W00 + Complex.normSq W01 := by
      have := Complex.normSq_nonneg W00; have := Complex.normSq_nonneg W01
      exact lt_of_le_of_ne (by linarith) (Ne.symm h)
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = Real.sqrt (Complex.normSq W00 + Complex.normSq W01) := ⟨_, rfl⟩
    have hρ2 : ρ ^ 2 = Complex.normSq W00 + Complex.normSq W01 := by rw [hρ]; exact Real.sq_sqrt hpos.le
    have hρpos : 0 < ρ := by rw [hρ]; exact Real.sqrt_pos.mpr hpos
    have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρpos.ne'
    set b0 : ℂ := W00 / ρ with hb0
    set b1 : ℂ := W01 / ρ with hb1
    have hb : Complex.normSq b0 + Complex.normSq b1 = 1 := by
      rw [hb0, hb1, map_div₀, map_div₀, Complex.normSq_ofReal]
      field_simp
      nlinarith [hρ2]
    set a1 : ℂ := W10 * conj b0 + W11 * conj b1 with ha1
    have hbb0 : conj b0 * b0 = (Complex.normSq b0 : ℂ) := by rw [Complex.normSq_eq_conj_mul_self]
    have hbb1 : conj b1 * b1 = (Complex.normSq b1 : ℂ) := by rw [Complex.normSq_eq_conj_mul_self]
    have hbC : (Complex.normSq b0 : ℂ) + (Complex.normSq b1 : ℂ) = 1 := by exact_mod_cast hb
    have hcross : W11 * b0 = W10 * b1 := by
      rw [hb0, hb1]; field_simp; linear_combination hd
    have e10 : a1 * b0 = W10 := by
      have : a1 * b0 = W10 * (conj b0 * b0 + conj b1 * b1) := by
        rw [ha1]; linear_combination (conj b1) * hcross
      rw [this, hbb0, hbb1, hbC, mul_one]
    have e11 : a1 * b1 = W11 := by
      have : a1 * b1 = W11 * (conj b0 * b0 + conj b1 * b1) := by
        rw [ha1]; linear_combination (-(conj b0)) * hcross
      rw [this, hbb0, hbb1, hbC, mul_one]
    have hn1 : Complex.normSq W10 + Complex.normSq W11 = Complex.normSq a1 := by
      rw [← e10, ← e11, map_mul, map_mul, ← mul_add, hb, mul_one]
    refine ⟨(ρ : ℂ), a1, b0, b1, ?_, hb, ?_, ?_, e10, e11⟩
    · rw [Complex.normSq_ofReal, ← hn1]; nlinarith [hρ2]
    · rw [hb0]; field_simp
    · rw [hb1]; field_simp

/-- **Existence of the auxiliary qubits**: a unit vector `v` with `Σ v_k² = 0` is `B†(a ⊗ b)` for unit
`a, b`. -/
theorem exists_vOf (v : V) (hn : Nv v = 1) (hτ : ∑ k, v k ^ 2 = 0) :
    ∃ a0 a1 b0 b1 : ℂ, Complex.normSq a0 + Complex.normSq a1 = 1 ∧
      Complex.normSq b0 + Complex.normSq b1 = 1 ∧ vOf a0 a1 b0 b1 = v := by
  have hrt := rt_mul_rt
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hτ' : v (0, 0) ^ 2 + v (0, 1) ^ 2 + v (1, 0) ^ 2 + v (1, 1) ^ 2 = 0 := by
    simpa [Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc] using hτ
  have hdet : (rt * (v (0, 0) + Complex.I * v (1, 1))) * (rt * (v (0, 0) - Complex.I * v (1, 1))) =
      (rt * (Complex.I * v (0, 1) + v (1, 0))) * (rt * (Complex.I * v (0, 1) - v (1, 0))) := by
    have : rt * rt * (v (0, 0) ^ 2 + v (0, 1) ^ 2 + v (1, 0) ^ 2 + v (1, 1) ^ 2) = 0 := by rw [hτ']; ring
    linear_combination this - (rt * rt * (v (1, 1) ^ 2 + v (0, 1) ^ 2)) * hI
  have hnorm : Complex.normSq (rt * (v (0, 0) + Complex.I * v (1, 1))) +
      Complex.normSq (rt * (Complex.I * v (0, 1) + v (1, 0))) +
      Complex.normSq (rt * (Complex.I * v (0, 1) - v (1, 0))) +
      Complex.normSq (rt * (v (0, 0) - Complex.I * v (1, 1))) = 1 := by
    have hN : Complex.normSq (v (0, 0)) + Complex.normSq (v (0, 1)) + Complex.normSq (v (1, 0)) +
        Complex.normSq (v (1, 1)) = 1 := by
      simpa [Nv, Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc] using hn
    simp only [Complex.normSq_mul, normSq_rt]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at hN ⊢
    nlinarith [hN]
  obtain ⟨a0, a1, b0, b1, ha, hb, e00, e01, e10, e11⟩ := factor2 _ _ _ _ hdet (by linarith [hnorm])
  refine ⟨a0, a1, b0, b1, ha, hb, ?_⟩
  funext k
  obtain ⟨k1, k2⟩ := k
  fin_cases k1 <;> fin_cases k2
  · show rt * (a0 * b0 + a1 * b1) = v (0, 0)
    rw [e00, e11]
    linear_combination (2 * v (0, 0)) * hrt
  · show rt * (-Complex.I * (a0 * b1 + a1 * b0)) = v (0, 1)
    rw [e01, e10]
    linear_combination (2 * v (0, 1)) * hrt + (-(2 * rt * rt * v (0, 1))) * hI
  · show rt * (a0 * b1 - a1 * b0) = v (1, 0)
    rw [e01, e10]
    linear_combination (2 * v (1, 0)) * hrt
  · show rt * (-Complex.I * (a0 * b0 - a1 * b1)) = v (1, 1)
    rw [e00, e11]
    linear_combination (2 * v (1, 1)) * hrt + (-(2 * rt * rt * v (1, 1))) * hI

end FormalResearch.FourQubitEntropy.CO
