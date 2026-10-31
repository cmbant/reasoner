import FormalResearch.FourQubitEntropy.RenyiFullDefs
import FormalResearch.FourQubitEntropy.RenyiFullStieltjes

/-!
# Monotonicity of `Σ λᵢ^q` in the determinant at fixed `p` and `t`

Paper E, `lem:fqe-renyi-determinant` (`sup_renyi.tex`, `sec:sup-determinant`): for `1 < q < 2`, at fixed
trace one, second moment `p` and third moment `t`, `H_q(λ)` is nondecreasing in the spectral
determinant `d = ∏ λᵢ`.

Proof (Stieltjes form).  For `s > 0` and a probability vector, with `P_λ(s) = ∏(λᵢ + s)`,
`Σᵢ λᵢ²/(λᵢ + s) = (1 - 4s) + s² P_λ'(s)/P_λ(s)`, where `P_λ' = 4s³ + 3s² + (1-p)s + (1-3p+2t)/6`
depends on `(p, t)` only and `P_λ(s) = s⁴ + s³ + ((1-p)/2)s² + ((1-3p+2t)/6)s + d`.  Hence at fixed
`(p, t)` the sum is a decreasing function of `d`, for every `s`.  Integrating against `s^{q-2}`
(`stieltjes_rpow`) gives `Zmono`: larger determinant, smaller `Σ λᵢ^q`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy MeasureTheory Set

/-- The spectral determinant of a four-point vector. -/
def det4 (l : Fin 4 → ℝ) : ℝ := l 0 * l 1 * l 2 * l 3

theorem prod_shift_eq {l : Fin 4 → ℝ} (hs : ∑ i, l i = 1) (s : ℝ) :
    (l 0 + s) * (l 1 + s) * (l 2 + s) * (l 3 + s) =
      s ^ 4 + s ^ 3 + (1 - pur l) / 2 * s ^ 2 + (1 - 3 * pur l + 2 * cub l) / 6 * s + det4 l := by
  simp only [Fin.sum_univ_four] at hs
  unfold pur cub det4
  simp only [Fin.sum_univ_four]
  have hd : l 3 = 1 - l 0 - l 1 - l 2 := by linarith
  rw [hd]; ring

theorem deriv_shift_eq {l : Fin 4 → ℝ} (hs : ∑ i, l i = 1) (s : ℝ) :
    (l 1 + s) * (l 2 + s) * (l 3 + s) + (l 0 + s) * (l 2 + s) * (l 3 + s) +
      (l 0 + s) * (l 1 + s) * (l 3 + s) + (l 0 + s) * (l 1 + s) * (l 2 + s) =
      4 * s ^ 3 + 3 * s ^ 2 + (1 - pur l) * s + (1 - 3 * pur l + 2 * cub l) / 6 := by
  simp only [Fin.sum_univ_four] at hs
  unfold pur cub
  simp only [Fin.sum_univ_four]
  have hd : l 3 = 1 - l 0 - l 1 - l 2 := by linarith
  rw [hd]; ring

/-- `Σᵢ stInt q (λᵢ) s = s^{q-2} [(1 - 4s) + s² D / P]` with `D`, `P` as above. -/
theorem stInt_sum_eq {q : ℝ} {l : Fin 4 → ℝ} (hl : IsProb4 l) {s : ℝ} (hs : 0 < s) :
    ∑ i, stInt q (l i) s = s ^ (q - 2) * ((1 - 4 * s) +
      s ^ 2 * (4 * s ^ 3 + 3 * s ^ 2 + (1 - pur l) * s + (1 - 3 * pur l + 2 * cub l) / 6) /
        (s ^ 4 + s ^ 3 + (1 - pur l) / 2 * s ^ 2 + (1 - 3 * pur l + 2 * cub l) / 6 * s + det4 l)) := by
  obtain ⟨h0, hsum⟩ := hl
  rw [← prod_shift_eq hsum s, ← deriv_shift_eq hsum s]
  simp only [Fin.sum_univ_four, stInt]
  rw [← mul_add, ← mul_add, ← mul_add]
  congr 1
  have := stieltjes_alg_aux (h0 0) (h0 1) (h0 2) (h0 3) hs
  have e1 : l 0 + l 1 + l 2 + l 3 = 1 := by simpa [Fin.sum_univ_four] using hsum
  rw [this, e1]


theorem det4_nonneg {l : Fin 4 → ℝ} (h : IsProb4 l) : 0 ≤ det4 l := by
  unfold det4
  have := h.1 0; have := h.1 1; have := h.1 2; have := h.1 3
  positivity

/-- Pointwise comparison of the Stieltjes sums: a larger determinant gives a smaller sum. -/
theorem stInt_sum_mono {q : ℝ} {l l' : Fin 4 → ℝ} (hl : IsProb4 l) (hl' : IsProb4 l')
    (hp : pur l = pur l') (ht : cub l = cub l') (hd : det4 l ≤ det4 l') {s : ℝ} (hs : 0 < s) :
    ∑ i, stInt q (l' i) s ≤ ∑ i, stInt q (l i) s := by
  rw [stInt_sum_eq hl hs, stInt_sum_eq hl' hs, ← hp, ← ht]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hs.le _)
  have hP : 0 < s ^ 4 + s ^ 3 + (1 - pur l) / 2 * s ^ 2 + (1 - 3 * pur l + 2 * cub l) / 6 * s + det4 l := by
    rw [← prod_shift_eq hl.2 s]
    have := hl.1 0; have := hl.1 1; have := hl.1 2; have := hl.1 3
    positivity
  have hP' : 0 < s ^ 4 + s ^ 3 + (1 - pur l) / 2 * s ^ 2 + (1 - 3 * pur l + 2 * cub l) / 6 * s + det4 l' := by
    have e := prod_shift_eq hl'.2 s
    rw [← hp, ← ht] at e
    rw [← e]
    have := hl'.1 0; have := hl'.1 1; have := hl'.1 2; have := hl'.1 3
    positivity
  have hD : 0 ≤ s ^ 2 * (4 * s ^ 3 + 3 * s ^ 2 + (1 - pur l) * s + (1 - 3 * pur l + 2 * cub l) / 6) := by
    rw [← deriv_shift_eq hl.2 s]
    have := hl.1 0; have := hl.1 1; have := hl.1 2; have := hl.1 3
    positivity
  have key : (s ^ 2 * (4 * s ^ 3 + 3 * s ^ 2 + (1 - pur l) * s + (1 - 3 * pur l + 2 * cub l) / 6)) /
        (s ^ 4 + s ^ 3 + (1 - pur l) / 2 * s ^ 2 + (1 - 3 * pur l + 2 * cub l) / 6 * s + det4 l') ≤
      (s ^ 2 * (4 * s ^ 3 + 3 * s ^ 2 + (1 - pur l) * s + (1 - 3 * pur l + 2 * cub l) / 6)) /
        (s ^ 4 + s ^ 3 + (1 - pur l) / 2 * s ^ 2 + (1 - 3 * pur l + 2 * cub l) / 6 * s + det4 l) := by
    apply div_le_div_of_nonneg_left hD hP (by linarith)
  linarith

/-- **`lem:fqe-renyi-determinant` (monotonicity)**: for `1 < q < 2` and four-point probability vectors
with equal `p` and `t`, a larger determinant gives a smaller `Σ λᵢ^q`, i.e. a larger `H_q`. -/
theorem Zmono {q : ℝ} (h1 : 1 < q) (h2 : q < 2) {l l' : Fin 4 → ℝ} (hl : IsProb4 l)
    (hl' : IsProb4 l') (hp : pur l = pur l') (ht : cub l = cub l') (hd : det4 l ≤ det4 l') :
    ∑ i, l' i ^ q ≤ ∑ i, l i ^ q := by
  have hI := stI_pos h1 h2
  have int_l : ∀ i, IntegrableOn (stInt q (l i)) (Ioi 0) := fun i =>
    stInt_integrableOn_nonneg h1 h2 (hl.1 i)
  have int_l' : ∀ i, IntegrableOn (stInt q (l' i)) (Ioi 0) := fun i =>
    stInt_integrableOn_nonneg h1 h2 (hl'.1 i)
  have eq_l : ∫ s in Ioi (0 : ℝ), ∑ i, stInt q (l i) s = (∑ i, l i ^ q) * stI q := by
    rw [integral_finset_sum _ (fun i _ => int_l i), Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => stieltjes_rpow_nonneg h1 h2 (hl.1 i))
  have eq_l' : ∫ s in Ioi (0 : ℝ), ∑ i, stInt q (l' i) s = (∑ i, l' i ^ q) * stI q := by
    rw [integral_finset_sum _ (fun i _ => int_l' i), Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => stieltjes_rpow_nonneg h1 h2 (hl'.1 i))
  have hmono : ∫ s in Ioi (0 : ℝ), ∑ i, stInt q (l' i) s ≤ ∫ s in Ioi (0 : ℝ), ∑ i, stInt q (l i) s := by
    apply setIntegral_mono_on (integrable_finset_sum _ (fun i _ => int_l' i))
      (integrable_finset_sum _ (fun i _ => int_l i)) measurableSet_Ioi
    intro s hs
    exact stInt_sum_mono hl hl' hp ht hd hs
  rw [eq_l, eq_l'] at hmono
  exact le_of_mul_le_mul_right hmono hI

end FormalResearch.FourQubitEntropy.RenyiFull
