import FormalResearch.FourQubitEntropy.PaperEGoSliceFinal

/-!
# GO glue: rays of the certificate

A certificate ray is a pair of real `4×4` matrices `(a, b)` with `a + b` orthogonal and `a = M Π`,
`Π` a rank-one orthogonal projector: then `a = P e₀ e₀ᵀ Qᵀ`, `b = P (1 - e₀ e₀ᵀ) Qᵀ` for orthogonal `P, Q`
(`ray_exists`), the state `χ` with magic coordinates `P diag(η₀) Qᵀ` is in `𝓜` (`orbit_mem4`), and
`|⟨χ, Z⟩|² = (re² + 3 im²)/6` with `re = 3⟨a,X⟩ + ⟨b,Y⟩`, `im = ⟨a,Y⟩ - ⟨b,X⟩` (`ray_normSq`).
Claim class: proved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset
open scoped ComplexConjugate Matrix

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

/-- An orthogonal matrix with prescribed first column. -/
theorem exists_orth_col (q : Fin 4 → ℝ) (hq : ∑ k, q k ^ 2 = 1) :
    ∃ Q : M4R, Qᵀ * Q = 1 ∧ ∀ j, Q j 0 = q j := by
  simp only [Fin.sum_univ_four] at hq
  by_cases h : q 0 = 1
  · have h1 : q 1 = 0 := by nlinarith [sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3)]
    have h2 : q 2 = 0 := by nlinarith [sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3)]
    have h3 : q 3 = 0 := by nlinarith [sq_nonneg (q 1), sq_nonneg (q 2), sq_nonneg (q 3)]
    refine ⟨1, by simp, fun j => ?_⟩
    fin_cases j <;> simp [Matrix.one_apply, h, h1, h2, h3]
  · have hN2 : ∑ k, (![q 0 - 1, q 1, q 2, q 3] : Fin 4 → ℝ) k ^ 2 = 2 - 2 * q 0 := by
      simp [Fin.sum_univ_four]; nlinarith
    have hne : (2 - 2 * q 0) ≠ 0 := by intro h'; apply h; linarith
    refine ⟨reflMat ![q 0 - 1, q 1, q 2, q 3], reflMat_orth (by rw [hN2]; exact hne), fun j => ?_⟩
    fin_cases j <;> simp [reflMat, hN2] <;> field_simp <;> ring

/-- A rank-one projector `Π` and an orthogonal `M`: orthogonal `P, Q` with `P Qᵀ = M`, `P e₀ (Q e₀)ᵀ = M Π`. -/
theorem ray_exists (M Pi : M4R) (hM : Mᵀ * M = 1) (hs : Piᵀ = Pi) (hi : Pi * Pi = Pi)
    (ht : Matrix.trace Pi = 1) (hr : ∀ i j k l, Pi i j * Pi k l = Pi i l * Pi k j) :
    ∃ P Q : M4R, Pᵀ * P = 1 ∧ Qᵀ * Q = 1 ∧ (∀ i j, ∑ k, P i k * Q j k = M i j) ∧
      ∀ i j, P i 0 * Q j 0 = (M * Pi) i j := by
  have hsym : ∀ i j, Pi j i = Pi i j := fun i j => by
    have := congrFun (congrFun hs i) j
    simpa [Matrix.transpose_apply] using this
  have hdiag : ∀ k, Pi k k = ∑ l, Pi l k ^ 2 := fun k => by
    have := congrFun (congrFun hi k) k
    simp only [Matrix.mul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsym k l]; ring
  obtain ⟨k, hk⟩ : ∃ k, Pi k k ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have : Matrix.trace Pi = 0 := by simp [Matrix.trace, hcon]
    rw [ht] at this; exact one_ne_zero this
  have hkpos : 0 < Pi k k := by
    rcases lt_or_eq_of_le (show 0 ≤ Pi k k by rw [hdiag]; exact Finset.sum_nonneg fun l _ => sq_nonneg _) with h | h
    · exact h
    · exact absurd h.symm hk
  set rt := Real.sqrt (Pi k k) with hsq
  have hsq2 : rt ^ 2 = Pi k k := Real.sq_sqrt hkpos.le
  have hsqpos : 0 < rt := Real.sqrt_pos.2 hkpos
  set q : Fin 4 → ℝ := fun i => Pi i k / rt with hq
  have hqq : ∀ i j, q i * q j = Pi i j := by
    intro i j
    show Pi i k / rt * (Pi j k / rt) = Pi i j
    rw [div_mul_div_comm, ← sq, hsq2, div_eq_iff hkpos.ne']
    have := hr i j k k
    rw [← hsym k j] at this
    linarith
  have hqn : ∑ i, q i ^ 2 = 1 := by
    simp only [hq, div_pow]
    rw [← Finset.sum_div, ← hdiag k, hsq2, div_self hkpos.ne']
  obtain ⟨Q, hQ, hQ0⟩ := exists_orth_col q hqn
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  refine ⟨M * Q, Q, ?_, hQ, ?_, ?_⟩
  · rw [Matrix.transpose_mul]
    calc Qᵀ * Mᵀ * (M * Q) = Qᵀ * (Mᵀ * M) * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM, Matrix.mul_one, hQ]
  · intro i j
    have : (M * Q * Qᵀ) i j = M i j := by rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
    rw [← this]
    simp [Matrix.mul_apply]
  · intro i j
    simp only [Matrix.mul_apply, hQ0]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_assoc, hqq]

/-- `|⟨χ, Z⟩|²` for the orbit state with coordinates `P diag(η₀) Qᵀ`. -/
theorem normSq_ip_orbit (v : SV) (P Q : M4R) (χ : Psi)
    (hc : ∀ p q : Fin 2 × Fin 2, magicCoord (zmat χ) p q =
      1 * ∑ k : Fin 4, (P (pairIdx p) k : ℂ) * etaC 0 k * (Q (pairIdx q) k : ℂ)) :
    Complex.normSq (ip χ (sState v)) =
      ((3 * (Pᵀ * sX v * Q) 0 0 + ((Pᵀ * sY v * Q) 1 1 + (Pᵀ * sY v * Q) 2 2 + (Pᵀ * sY v * Q) 3 3)) ^ 2 +
        3 * ((Pᵀ * sY v * Q) 0 0 - ((Pᵀ * sX v * Q) 1 1 + (Pᵀ * sX v * Q) 2 2 + (Pᵀ * sX v * Q) 3 3)) ^ 2) / 6 := by
  rw [ip_orbit v P Q 1 χ hc]
  obtain ⟨hk2, hk6, hk3⟩ := sqrt_factsG
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hr2 : (1 / Real.sqrt 2 : ℝ) = Real.sqrt 3 * (1 / Real.sqrt 6) := by
    have e6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    have p2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have p3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    rw [e6]; field_simp
  have hr6 : (1 / Real.sqrt 6 : ℝ) ^ 2 = 1 / 6 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have c1 : ∀ k : Fin 4, k ≠ 0 → (starRingEnd ℂ) (etaC 0 k) =
      -(Complex.I * ((1 / Real.sqrt 6 : ℝ) : ℂ)) := by
    intro k hk
    rw [etaC0_pos k hk, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have c0 : (starRingEnd ℂ) (etaC 0 0) = ((Real.sqrt 3 * (1 / Real.sqrt 6) : ℝ) : ℂ) := by
    rw [etaC0_0', Complex.conj_ofReal, hr2]
  simp only [Fin.sum_univ_four, c1 1 (by decide), c1 2 (by decide), c1 3 (by decide), c0, map_one,
    one_mul, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  generalize (1 / Real.sqrt 6 : ℝ) = r at hr6 ⊢
  generalize (Pᵀ * sX v * Q) 0 0 = x0
  generalize (Pᵀ * sX v * Q) 1 1 = x1
  generalize (Pᵀ * sX v * Q) 2 2 = x2
  generalize (Pᵀ * sX v * Q) 3 3 = x3
  generalize (Pᵀ * sY v * Q) 0 0 = y0
  generalize (Pᵀ * sY v * Q) 1 1 = y1
  generalize (Pᵀ * sY v * Q) 2 2 = y2
  generalize (Pᵀ * sY v * Q) 3 3 = y3
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := hk3
  refine Eq.trans (b := r ^ 2 * ((Real.sqrt 3 * Real.sqrt 3 * x0 + (y1 + y2 + y3)) ^ 2 +
    (Real.sqrt 3 * Real.sqrt 3) * (y0 - (x1 + x2 + x3)) ^ 2)) (by ring) ?_
  rw [h3, hr6]; ring

theorem diag0_PAQ (P Q A : M4R) :
    (Pᵀ * A * Q) 0 0 = ∑ i, ∑ j, A i j * (P i 0 * Q j 0) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
  ring

theorem trace_PAQ (P Q A : M4R) :
    (Pᵀ * A * Q) 0 0 + (Pᵀ * A * Q) 1 1 + (Pᵀ * A * Q) 2 2 + (Pᵀ * A * Q) 3 3 =
      ∑ i, ∑ j, A i j * (∑ k, P i k * Q j k) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
  ring

/-- **A ray is in `𝓜`**: the overlap of the ray state with the slice state. -/
theorem ray_mem (v : SV) (P Q a b : M4R) (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1)
    (ha : ∀ i j, P i 0 * Q j 0 = a i j) (hab : ∀ i j, ∑ k, P i k * Q j k = a i j + b i j) :
    ∃ χ : Psi, InOrbit χ ∧ Complex.normSq (ip χ (sState v)) =
      ((3 * (∑ i, ∑ j, a i j * sX v i j) + ∑ i, ∑ j, b i j * sY v i j) ^ 2 +
        3 * ((∑ i, ∑ j, a i j * sY v i j) - ∑ i, ∑ j, b i j * sX v i j) ^ 2) / 6 := by
  obtain ⟨χ, hχ, hc⟩ := orbit_mem4 P Q hP hQ 1 (by simp)
  refine ⟨χ, hχ, ?_⟩
  rw [normSq_ip_orbit v P Q χ hc]
  have hx0 : (Pᵀ * sX v * Q) 0 0 = ∑ i, ∑ j, a i j * sX v i j := by
    rw [diag0_PAQ]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ha]; ring
  have hy0 : (Pᵀ * sY v * Q) 0 0 = ∑ i, ∑ j, a i j * sY v i j := by
    rw [diag0_PAQ]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ha]; ring
  have hxs : (Pᵀ * sX v * Q) 1 1 + (Pᵀ * sX v * Q) 2 2 + (Pᵀ * sX v * Q) 3 3 =
      ∑ i, ∑ j, b i j * sX v i j := by
    have := trace_PAQ P Q (sX v)
    rw [hx0] at this
    have h2 : ∑ i, ∑ j, sX v i j * (∑ k, P i k * Q j k) =
        (∑ i, ∑ j, a i j * sX v i j) + ∑ i, ∑ j, b i j * sX v i j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hab]; ring
    linarith
  have hys : (Pᵀ * sY v * Q) 1 1 + (Pᵀ * sY v * Q) 2 2 + (Pᵀ * sY v * Q) 3 3 =
      ∑ i, ∑ j, b i j * sY v i j := by
    have := trace_PAQ P Q (sY v)
    rw [hy0] at this
    have h2 : ∑ i, ∑ j, sY v i j * (∑ k, P i k * Q j k) =
        (∑ i, ∑ j, a i j * sY v i j) + ∑ i, ∑ j, b i j * sY v i j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hab]; ring
    linarith
  rw [hx0, hy0, hxs, hys]

end

end FormalResearch.FourQubitEntropy.GO
