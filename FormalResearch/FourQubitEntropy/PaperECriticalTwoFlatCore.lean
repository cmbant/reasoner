import Mathlib

/-!
# Two-flat rigidity: the scalar core (`prop:fqe-two-flat-rigidity`, bound `(TF)`)

Paper E, `renyi_uncapped_reduction.tex`. For a unit vector `u` (the amplitudes of a cut of a critical
state, so the cut spectrum is `λ_k = |u_k|²`) and a real `P` with `2P = 2 + |Σ u_k²|²` (the purity
identity at criticality), if `λ_i ≥ 1/2` then
`P - Σ λ_k² - 1/2 ≥ (Σ_{j≠i} λ_j)² - Σ_{j≠i} λ_j² = 2 e₂(λ_j : j ≠ i)`,
and equality holds when every other `u_j²` has the phase opposite to `u_i²`.

Pure algebra over `ℂ`: proved, axiom-free (`propext`, `Classical.choice`, `Quot.sound`).
-/

open scoped ComplexConjugate

namespace FormalResearch.FourQubitEntropy.PaperECritical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normSq_eq_norm_sq' (z : ℂ) : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z

/-- Reverse triangle inequality for `s = Σ u_k²`: `|s| ≥ 2 λ_i - 1` when `Σ λ = 1`. -/
theorem norm_sum_sq_ge (u : ι → ℂ) (hn : ∑ k, Complex.normSq (u k) = 1) (i : ι) :
    2 * Complex.normSq (u i) - 1 ≤ ‖∑ k, u k ^ 2‖ := by
  have hs : ∑ k, u k ^ 2 = u i ^ 2 + ∑ k ∈ Finset.univ.erase i, u k ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hnorm : ∀ k, ‖u k ^ 2‖ = Complex.normSq (u k) := fun k => by
    rw [norm_pow, Complex.normSq_eq_norm_sq]
  have h1 : ‖∑ k ∈ Finset.univ.erase i, u k ^ 2‖ ≤ ∑ k ∈ Finset.univ.erase i, Complex.normSq (u k) := by
    calc _ ≤ ∑ k ∈ Finset.univ.erase i, ‖u k ^ 2‖ := norm_sum_le _ _
      _ = _ := Finset.sum_congr rfl (fun k _ => hnorm k)
  have h2 : ∑ k ∈ Finset.univ.erase i, Complex.normSq (u k) = 1 - Complex.normSq (u i) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hn]
  have h3 : ‖u i ^ 2‖ - ‖∑ k ∈ Finset.univ.erase i, u k ^ 2‖ ≤ ‖∑ k, u k ^ 2‖ := by
    rw [hs]; have := norm_sub_norm_le (u i ^ 2) (-(∑ k ∈ Finset.univ.erase i, u k ^ 2))
    rw [norm_neg, sub_neg_eq_add] at this; exact this
  rw [hnorm i] at h3
  linarith

/-- `|Σ u_k²|² ≥ (2λ_i - 1)²` when `λ_i ≥ 1/2`. -/
theorem tau_lower (u : ι → ℂ) (hn : ∑ k, Complex.normSq (u k) = 1) (i : ι)
    (hi : 1 / 2 ≤ Complex.normSq (u i)) :
    (2 * Complex.normSq (u i) - 1) ^ 2 ≤ Complex.normSq (∑ k, u k ^ 2) := by
  rw [normSq_eq_norm_sq' (∑ k, u k ^ 2)]
  exact pow_le_pow_left₀ (by linarith) (norm_sum_sq_ge u hn i) 2

/-- **Crossed purity cost, scalar form of `(TF)`**: if `2P = 2 + |Σ u_k²|²`, `Σ|u_k|² = 1` and
`|u_i|² ≥ 1/2`, then `P - Σ|u_k|⁴ - 1/2 ≥ (Σ_{j≠i} λ_j)² - Σ_{j≠i} λ_j²`, the right side being
`2 e₂` of the other three spectrum entries. -/
theorem two_flat_core (u : ι → ℂ) (hn : ∑ k, Complex.normSq (u k) = 1) (P : ℝ)
    (hP : 2 * P = 2 + Complex.normSq (∑ k, u k ^ 2)) (i : ι)
    (hi : 1 / 2 ≤ Complex.normSq (u i)) :
    (∑ j ∈ Finset.univ.erase i, Complex.normSq (u j)) ^ 2 -
        ∑ j ∈ Finset.univ.erase i, Complex.normSq (u j) ^ 2
      ≤ P - ∑ k, Complex.normSq (u k) ^ 2 - 1 / 2 := by
  have h1 := tau_lower u hn i hi
  have h2 : ∑ j ∈ Finset.univ.erase i, Complex.normSq (u j) = 1 - Complex.normSq (u i) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hn]
  have h3 : ∑ j ∈ Finset.univ.erase i, Complex.normSq (u j) ^ 2
      = ∑ k, Complex.normSq (u k) ^ 2 - Complex.normSq (u i) ^ 2 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  rw [h2, h3]
  nlinarith

/-- Second inequality of `(TF)`: the other three entries `a ≥ b, c` give `2(ab + ac + bc) ≥ (b + c)²`. -/
theorem two_flat_second {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : b ≤ a) (hac : c ≤ a) :
    (b + c) ^ 2 ≤ 2 * (a * b + a * c + b * c) := by nlinarith [mul_nonneg hb hc]

/-- Sharpness of the first inequality of `(TF)`: if every other `u_j²` has phase opposite to `u_i²`
(`u_j² = -t_j u_i²`, `t_j ≥ 0`), then `|Σ u_k²|² = (2λ_i - 1)²`, i.e. equality in `two_flat_core`. -/
theorem tau_equality (u : ι → ℂ) (hn : ∑ k, Complex.normSq (u k) = 1) (i : ι)
    (hi : 1 / 2 ≤ Complex.normSq (u i))
    (hopp : ∀ j, j ≠ i → ∃ t : ℝ, 0 ≤ t ∧ u j ^ 2 = -(t : ℂ) * u i ^ 2) :
    Complex.normSq (∑ k, u k ^ 2) = (2 * Complex.normSq (u i) - 1) ^ 2 := by
  choose! t ht0 htj using hopp
  have hpos : 0 < Complex.normSq (u i) := by linarith
  have hui : u i ≠ 0 := fun h => by simp [h] at hpos
  have hnorm : ∀ k, ‖u k ^ 2‖ = Complex.normSq (u k) := fun k => by
    rw [norm_pow, Complex.normSq_eq_norm_sq]
  have hs : ∑ k, u k ^ 2 = u i ^ 2 * (1 - ∑ j ∈ Finset.univ.erase i, (t j : ℂ)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      Finset.sum_congr rfl (fun j hj => htj j (Finset.ne_of_mem_erase hj))]
    simp only [neg_mul, Finset.sum_neg_distrib, ← Finset.sum_mul]
    ring
  have hl : ∀ j, j ≠ i → Complex.normSq (u j) = t j * Complex.normSq (u i) := by
    intro j hj
    have := congrArg norm (htj j hj)
    rw [hnorm j, norm_mul, norm_neg, Complex.norm_real, hnorm i, Real.norm_of_nonneg (ht0 j hj)] at this
    exact this
  have hsum : (∑ j ∈ Finset.univ.erase i, t j) * Complex.normSq (u i) = 1 - Complex.normSq (u i) := by
    have h2 : ∑ j ∈ Finset.univ.erase i, Complex.normSq (u j) = 1 - Complex.normSq (u i) := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hn]
    rw [Finset.sum_mul, ← h2]
    exact Finset.sum_congr rfl (fun j hj => (hl j (Finset.ne_of_mem_erase hj)).symm)
  have hT : ((∑ j ∈ Finset.univ.erase i, (t j : ℂ))) = ((∑ j ∈ Finset.univ.erase i, t j : ℝ) : ℂ) := by
    push_cast; rfl
  set T := ∑ j ∈ Finset.univ.erase i, t j
  have hN : Complex.normSq (1 - (T : ℂ)) = (1 - T) ^ 2 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.normSq_ofReal]; ring
  rw [hs, hT, Complex.normSq_mul, map_pow, hN]
  have : (1 - T) * Complex.normSq (u i) = 2 * Complex.normSq (u i) - 1 := by
    nlinarith
  calc Complex.normSq (u i) ^ 2 * (1 - T) ^ 2 = ((1 - T) * Complex.normSq (u i)) ^ 2 := by ring
    _ = _ := by rw [this]

end FormalResearch.FourQubitEntropy.PaperECritical
