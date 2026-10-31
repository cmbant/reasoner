import FormalResearch.FourQubitEntropy.PaperECriticalTwoFlatCore

/-!
# Two-flat rigidity: equality in the reverse triangle inequality (scalar core)

Paper E, `renyi_uncapped_reduction.tex`, `prop:fqe-two-flat-rigidity`: on the critical locus the first
inequality of `(TF)` is an equality exactly when all nonzero squares of the other normal-form
amplitudes have a phase opposite to the square of the largest amplitude. The scalar statement is
`tau_eq_iff`: for a unit vector `u` and `i` with `|u_i|² ≥ 1/2`,
`|Σ u_k²|² = (2|u_i|² - 1)²` iff for every `j ≠ i` there is `t ≥ 0` with `u_j² = -t u_i²`
(the `⇐` direction is `tau_equality` in `PaperECriticalTwoFlatCore.lean`).
-/

open scoped ComplexConjugate

namespace FormalResearch.FourQubitEntropy.PaperECritical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eq_neg_norm_of_re {z : ℂ} (h : z.re = -‖z‖) : z = -((‖z‖ : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa using h
  · have h2 : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have : z.im ^ 2 = 0 := by rw [h] at h2; nlinarith
    simpa using this

/-- Equality case of the reverse triangle inequality `tau_lower`. -/
theorem tau_eq_iff (u : ι → ℂ) (hn : ∑ k, Complex.normSq (u k) = 1) (i : ι)
    (hi : 1 / 2 ≤ Complex.normSq (u i)) :
    Complex.normSq (∑ k, u k ^ 2) = (2 * Complex.normSq (u i) - 1) ^ 2 ↔
      ∀ j, j ≠ i → ∃ t : ℝ, 0 ≤ t ∧ u j ^ 2 = -(t : ℂ) * u i ^ 2 := by
  constructor
  swap
  · exact tau_equality u hn i hi
  intro heq
  set l : ℝ := Complex.normSq (u i) with hl
  have lpos : 0 < l := by linarith
  set a : ℂ := u i ^ 2 with ha
  have hnorm : ∀ k, ‖u k ^ 2‖ = Complex.normSq (u k) := fun k => by
    rw [norm_pow, Complex.normSq_eq_norm_sq]
  have hna : ‖a‖ = l := hnorm i
  have hSig : ‖∑ k, u k ^ 2‖ = 2 * l - 1 := by
    have h1 : ‖∑ k, u k ^ 2‖ ^ 2 = (2 * l - 1) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; exact heq
    exact (pow_left_inj₀ (norm_nonneg _) (by linarith) (by norm_num)).mp h1
  set X : ℂ := (∑ k, u k ^ 2) * conj a with hX
  have hXn : ‖X‖ = (2 * l - 1) * l := by
    rw [hX, norm_mul, hSig, RCLike.norm_conj, hna]
  have hsplit : X = ((l * l : ℝ) : ℂ) + ∑ j ∈ Finset.univ.erase i, u j ^ 2 * conj a := by
    rw [hX, Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    rw [ha, ← ha, Complex.mul_conj, Complex.normSq_eq_norm_sq, hna]; push_cast; ring
  have hsumj : ∑ j ∈ Finset.univ.erase i, Complex.normSq (u j) = 1 - l := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hn]
  have hre : X.re = l * l + ∑ j ∈ Finset.univ.erase i, (u j ^ 2 * conj a).re := by
    rw [hsplit]; simp [Complex.re_sum]
  have hnj : ∀ j, ‖u j ^ 2 * conj a‖ = Complex.normSq (u j) * l := fun j => by
    rw [norm_mul, RCLike.norm_conj, hna, hnorm]
  have hle : ∀ j, -‖u j ^ 2 * conj a‖ ≤ (u j ^ 2 * conj a).re := fun j => by
    have := Complex.abs_re_le_norm (u j ^ 2 * conj a)
    have := neg_abs_le (u j ^ 2 * conj a).re
    linarith
  have hReX : X.re ≤ ‖X‖ := Complex.re_le_norm X
  have hsum0 : ∑ j ∈ Finset.univ.erase i, ((u j ^ 2 * conj a).re + ‖u j ^ 2 * conj a‖) = 0 := by
    have h1 : ∑ j ∈ Finset.univ.erase i, ‖u j ^ 2 * conj a‖ = (1 - l) * l := by
      rw [Finset.sum_congr rfl (fun j _ => hnj j), ← Finset.sum_mul, hsumj]
    rw [Finset.sum_add_distrib, h1]
    have h2 : ∑ j ∈ Finset.univ.erase i, (u j ^ 2 * conj a).re ≥ -((1 - l) * l) := by
      calc ∑ j ∈ Finset.univ.erase i, (u j ^ 2 * conj a).re
          ≥ ∑ j ∈ Finset.univ.erase i, -‖u j ^ 2 * conj a‖ := Finset.sum_le_sum fun j _ => hle j
        _ = -((1 - l) * l) := by rw [Finset.sum_neg_distrib, h1]
    nlinarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by linarith [hle j])).mp hsum0
  intro j hj
  have hj0 := hz j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  have hrj : (u j ^ 2 * conj a).re = -‖u j ^ 2 * conj a‖ := by linarith
  have hw := eq_neg_norm_of_re hrj
  rw [hnj j] at hw
  refine ⟨Complex.normSq (u j) / l, div_nonneg (Complex.normSq_nonneg _) lpos.le, ?_⟩
  have hconj : conj a * a = ((l * l : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hna]; push_cast; ring
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast lpos.ne'
  have key : u j ^ 2 * ((l * l : ℝ) : ℂ) = -(((Complex.normSq (u j) * l : ℝ)) : ℂ) * a := by
    calc u j ^ 2 * ((l * l : ℝ) : ℂ) = (u j ^ 2 * conj a) * a := by rw [← hconj]; ring
      _ = _ := by rw [hw]
  have hll : ((l * l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero lpos.ne' lpos.ne'
  apply mul_right_cancel₀ hll
  rw [key]
  push_cast
  field_simp

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.tau_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tau_eq_iff

end FormalResearch.FourQubitEntropy.PaperECritical
