import FormalResearch.FourQubitEntropy.Marginals

/-!
# The top eigenvector of a cut matrix with spectrum `{1/2, 1/6, 1/6, 1/6}`
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

theorem exists_top_vec {R : Mat4} (hR : R.IsHermitian)
    (hq : (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0) (htr : (Matrix.trace R).re = 1) :
    ∃ u : Fin 2 × Fin 2 → ℂ, ∑ i, Complex.normSq (u i) = 1 ∧
      ∀ i j, R i j = (if i = j then (1 / 6 : ℂ) else 0) + (1 / 3 : ℂ) * (u i * (starRingEnd ℂ) (u j)) := by
  have hnodes := eigenvalue_of_quadratic hR hq
  have hsum : ∑ i, hR.eigenvalues i = 1 := by
    have := sum_eigenvalues_pow hR 1
    simp only [pow_one] at this
    rw [this, htr]
  have hlam : ∀ i, hR.eigenvalues i = 1 / 6 + if hR.eigenvalues i = 1 / 2 then 1 / 3 else 0 := by
    intro i
    rcases hnodes i with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  set S := Finset.univ.filter (fun i => hR.eigenvalues i = 1 / 2) with hS
  have hcard : (S.card : ℝ) = 1 := by
    have : ∑ i, hR.eigenvalues i = ∑ i : Fin 2 × Fin 2, (1 / 6 + if hR.eigenvalues i = 1 / 2 then (1 / 3 : ℝ) else 0) :=
      Finset.sum_congr rfl fun i _ => hlam i
    rw [Finset.sum_add_distrib, ← Finset.sum_filter] at this
    simp at this
    rw [hS]
    linarith
  have hc1 : S.card = 1 := by exact_mod_cast hcard
  obtain ⟨i0, hi0⟩ := Finset.card_eq_one.1 hc1
  have hk : ∀ k, hR.eigenvalues k = 1 / 2 ↔ k = i0 := by
    intro k
    have := Finset.ext_iff.1 hi0 k
    simpa [hS] using this
  have h1 : star (eigU hR) * eigU hR = 1 := Unitary.coe_star_mul_self hR.eigenvectorUnitary
  have h0 : eigU hR * star (eigU hR) = 1 := Unitary.coe_mul_star_self hR.eigenvectorUnitary
  have hspec : R = eigU hR * Matrix.diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ)) *
      star (eigU hR) := by
    have := hR.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  refine ⟨fun i => eigU hR i i0, ?_, ?_⟩
  · have := congrFun (congrFun h1 i0) i0
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, if_true] at this
    have e : ∀ i, ((Complex.normSq (eigU hR i i0) : ℝ) : ℂ) = star (eigU hR i i0) * eigU hR i i0 := by
      intro i; rw [mul_comm]; exact (Complex.mul_conj _).symm
    have : (((∑ i, Complex.normSq (eigU hR i i0) : ℝ)) : ℂ) = 1 := by
      push_cast; simp only [e]; exact this
    exact_mod_cast this
  · intro i j
    have hdelta : ∑ k, eigU hR i k * star (eigU hR j k) = if i = j then 1 else 0 := by
      have := congrFun (congrFun h0 i) j
      simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using this
    have hRij : R i j = ∑ k, eigU hR i k * ((hR.eigenvalues k : ℝ) : ℂ) * star (eigU hR j k) := by
      conv_lhs => rw [hspec]
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_diagonal]
      simp [Matrix.star_apply]
    rw [hRij]
    have hl : ∀ k, ((hR.eigenvalues k : ℝ) : ℂ) = 1 / 6 + if k = i0 then 1 / 3 else 0 := by
      intro k
      have := hlam k
      by_cases hk' : k = i0
      · have h2 : hR.eigenvalues k = 1 / 2 := (hk k).2 hk'
        rw [h2]; simp [hk']; norm_num
      · have h2 : hR.eigenvalues k ≠ 1 / 2 := fun h => hk' ((hk k).1 h)
        rw [if_neg h2] at this
        rw [this, if_neg hk']; push_cast; ring
    simp only [hl]
    have : ∀ k, eigU hR i k * (1 / 6 + if k = i0 then (1 / 3 : ℂ) else 0) * star (eigU hR j k)
        = (1 / 6 : ℂ) * (eigU hR i k * star (eigU hR j k))
          + if k = i0 then (1 / 3 : ℂ) * (eigU hR i i0 * star (eigU hR j i0)) else 0 := by
      intro k
      by_cases hk' : k = i0
      · subst hk'; simp; ring
      · simp [hk']; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hdelta]
    simp

end FormalResearch.FourQubitEntropy
