import FormalResearch.FourQubitEntropy.PaperECriticalSextic
import FormalResearch.FourQubitEntropy.PaperECriticalZeroAlg
import FormalResearch.FourQubitEntropy.PaperECriticalSexticLU

/-!
# Zero set of `F` on the critical slice

For `v : ℂ^{2×2}` with `Σ |v_k|² = 1`, the twelve equations behind `Zsum v = 0`
(`sexticF_Gv`) are classified by `zero_classify`: (A) one nonzero coordinate, (B) `|v_k|² = 1/4`
with all `v_k²` equal, (C) `|v_k|² ∈ {1/6, 1/2}` with `Σ v_k² = 0`.
Proved, no `native_decide`.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

/-- The standard enumeration of the four magic-basis coordinates. -/
def e4 : Fin 4 → Fin 2 × Fin 2 := ![(0, 0), (0, 1), (1, 0), (1, 1)]

theorem e4_injective : Function.Injective e4 := by decide

theorem e4_surjective : Function.Surjective e4 := by decide

theorem Zterm_nonneg (v : Fin 2 × Fin 2 → ℂ) (i j k : Fin 2 × Fin 2) : 0 ≤ Zterm v i j k :=
  Complex.normSq_nonneg _

set_option maxHeartbeats 2000000 in
/-- All twelve equations behind `Zsum v = 0`, in the form `(ZE)` for distinct indices. -/
theorem Zsum_zero_eqs (v : Fin 2 × Fin 2 → ℂ) (h : Zsum v = 0) :
    ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      (starRingEnd ℂ) (v (e4 i)) * (v (e4 j) ^ 2 - v (e4 k) ^ 2) +
        2 * v (e4 i) * ((Complex.normSq (v (e4 j)) : ℂ) - (Complex.normSq (v (e4 k)) : ℂ)) = 0 := by
  have hz : ∀ i j k, Zterm v i j k = 0 → (starRingEnd ℂ) (v i) * (v j ^ 2 - v k ^ 2) +
      2 * v i * ((Complex.normSq (v j) : ℂ) - (Complex.normSq (v k) : ℂ)) = 0 := fun i j k h =>
    Complex.normSq_eq_zero.mp h
  unfold Zsum at h
  have n1 := Zterm_nonneg v (0, 0) (0, 1) (1, 0)
  have n2 := Zterm_nonneg v (0, 0) (0, 1) (1, 1)
  have n3 := Zterm_nonneg v (0, 0) (1, 0) (1, 1)
  have n4 := Zterm_nonneg v (0, 1) (0, 0) (1, 0)
  have n5 := Zterm_nonneg v (0, 1) (0, 0) (1, 1)
  have n6 := Zterm_nonneg v (0, 1) (1, 0) (1, 1)
  have n7 := Zterm_nonneg v (1, 0) (0, 0) (0, 1)
  have n8 := Zterm_nonneg v (1, 0) (0, 0) (1, 1)
  have n9 := Zterm_nonneg v (1, 0) (0, 1) (1, 1)
  have n10 := Zterm_nonneg v (1, 1) (0, 0) (0, 1)
  have n11 := Zterm_nonneg v (1, 1) (0, 0) (1, 0)
  have n12 := Zterm_nonneg v (1, 1) (0, 1) (1, 0)
  have h1 := hz _ _ _ (show Zterm v (0, 0) (0, 1) (1, 0) = 0 by linarith)
  have h2 := hz _ _ _ (show Zterm v (0, 0) (0, 1) (1, 1) = 0 by linarith)
  have h3 := hz _ _ _ (show Zterm v (0, 0) (1, 0) (1, 1) = 0 by linarith)
  have h4 := hz _ _ _ (show Zterm v (0, 1) (0, 0) (1, 0) = 0 by linarith)
  have h5 := hz _ _ _ (show Zterm v (0, 1) (0, 0) (1, 1) = 0 by linarith)
  have h6 := hz _ _ _ (show Zterm v (0, 1) (1, 0) (1, 1) = 0 by linarith)
  have h7 := hz _ _ _ (show Zterm v (1, 0) (0, 0) (0, 1) = 0 by linarith)
  have h8 := hz _ _ _ (show Zterm v (1, 0) (0, 0) (1, 1) = 0 by linarith)
  have h9 := hz _ _ _ (show Zterm v (1, 0) (0, 1) (1, 1) = 0 by linarith)
  have h10 := hz _ _ _ (show Zterm v (1, 1) (0, 0) (0, 1) = 0 by linarith)
  have h11 := hz _ _ _ (show Zterm v (1, 1) (0, 0) (1, 0) = 0 by linarith)
  have h12 := hz _ _ _ (show Zterm v (1, 1) (0, 1) (1, 0) = 0 by linarith)
  intro i j k hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [e4] at hij hik hjk ⊢ <;>
  first
    | linear_combination h1
    | linear_combination -h1
    | linear_combination h2
    | linear_combination -h2
    | linear_combination h3
    | linear_combination -h3
    | linear_combination h4
    | linear_combination -h4
    | linear_combination h5
    | linear_combination -h5
    | linear_combination h6
    | linear_combination -h6
    | linear_combination h7
    | linear_combination -h7
    | linear_combination h8
    | linear_combination -h8
    | linear_combination h9
    | linear_combination -h9
    | linear_combination h10
    | linear_combination -h10
    | linear_combination h11
    | linear_combination -h11
    | linear_combination h12
    | linear_combination -h12


theorem sum_e4 {M : Type*} [AddCommMonoid M] (f : Fin 2 × Fin 2 → M) :
    ∑ i : Fin 4, f (e4 i) = ∑ k, f k := by
  simp [Fin.sum_univ_four, Fintype.sum_prod_type, Fin.sum_univ_two, e4, add_assoc]

/-- **`prop:fqe-moment-zeros`, algebraic part** (proved). If `Σ |v_k|² = 1` and `Zsum v = 0`
then (A) `v` has a single nonzero coordinate, or (B) `|v_k|² = 1/4` for all `k` and all `v_k²`
are equal, or (C) `|v_k|² ∈ {1/6, 1/2}` for all `k` and `Σ v_k² = 0`. -/
theorem Gv_zero_cases (v : Fin 2 × Fin 2 → ℂ) (hn : ∑ k, Complex.normSq (v k) = 1)
    (hZ : Zsum v = 0) :
    (∃ k, ∀ j, j ≠ k → v j = 0) ∨
      ((∀ k, Complex.normSq (v k) = 1 / 4) ∧ ∀ k, v k ^ 2 = v (0, 0) ^ 2) ∨
      ((∀ k, Complex.normSq (v k) = 1 / 6 ∨ Complex.normSq (v k) = 1 / 2) ∧ ∑ k, v k ^ 2 = 0) := by
  have hE := Zsum_zero_eqs v hZ
  have key := zero_classify (fun i => v (e4 i) ^ 2) (fun i => Complex.normSq (v (e4 i)))
    (fun i => Complex.normSq_nonneg _)
    (fun i => by rw [norm_pow, Complex.normSq_eq_norm_sq])
    (by rw [sum_e4 (fun k => Complex.normSq (v k))]; exact hn)
    (by
      intro i j k hij hik hjk
      have e := hE i j k hij hik hjk
      have hmc := (Complex.mul_conj (v (e4 i))).symm
      beta_reduce
      linear_combination (v (e4 i)) * e + ((v (e4 j)) ^ 2 - (v (e4 k)) ^ 2) * hmc)
  rcases key with ⟨i, hi⟩ | hB | ⟨hC1, hC2⟩
  · left
    refine ⟨e4 i, fun j hj => ?_⟩
    obtain ⟨j', rfl⟩ := e4_surjective j
    have hj' : j' ≠ i := fun h => hj (by rw [h])
    have := hi j' hj'
    simpa using this
  · right; left
    refine ⟨fun k => ?_, fun k => ?_⟩
    · obtain ⟨i, rfl⟩ := e4_surjective k; exact (hB i).1
    · obtain ⟨i, rfl⟩ := e4_surjective k; exact (hB i).2
  · right; right
    refine ⟨fun k => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := e4_surjective k; exact hC1 i
    · rw [← sum_e4 (fun k => v k ^ 2)]; exact hC2

end FormalResearch.FourQubitEntropy.PaperECritical
