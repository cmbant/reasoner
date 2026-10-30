import FormalResearch.FourQubitEntropy.PaperECriticalZeroOrbits
import FormalResearch.FourQubitEntropy.PaperEGenDefect

/-
# Critical-orbit stability: the twelve cut probabilities (`thm:fqe-critical-orbit-sharp`)

For a vector `v` of the critical normal form (`Gv v`), the twelve cut probabilities
`pr v` are `|v_k|²`, `|(H₊ v)_k|²`, `|(H₋ v)_k|²`, `Qv v = 18 N P - 12 T - 13 N³` is the sextic
`Q` of `G(v)` (`sexticQ_Gv`), and the three-term identity `eq:fqe-critical-three-term`
(`Qv_three_term`) holds as a polynomial identity.  The symmetry lemmas show that coordinate swaps,
coordinate sign flips, `H₊`, `H₋` and unit phases permute the twelve probabilities.
-/

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

abbrev V := Fin 2 × Fin 2 → ℂ

/-- `N = ∑ |v_k|²`. -/
noncomputable def Nv (v : V) : ℝ := ∑ k, Complex.normSq (v k)

/-- The twelve cut probabilities `|v_k|²`, `|(H₊v)_k|²`, `|(H₋v)_k|²`. -/
noncomputable def pr (v : V) : Fin 12 → ℝ :=
  ![Complex.normSq (v (0, 0)), Complex.normSq (v (0, 1)), Complex.normSq (v (1, 0)), Complex.normSq (v (1, 1)),
    Complex.normSq (wp v (0, 0)), Complex.normSq (wp v (0, 1)), Complex.normSq (wp v (1, 0)),
    Complex.normSq (wp v (1, 1)), Complex.normSq (wm v (0, 0)), Complex.normSq (wm v (0, 1)),
    Complex.normSq (wm v (1, 0)), Complex.normSq (wm v (1, 1))]

/-- `Q = 18 N P - 12 T - 13 N³` in terms of the twelve cut probabilities. -/
noncomputable def Qv (v : V) : ℝ :=
  18 * Nv v * ∑ k, pr v k ^ 2 - 12 * ∑ k, pr v k ^ 3 - 13 * Nv v ^ 3

theorem sum12 (f : Fin 12 → ℝ) : ∑ k, f k =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp [Fin.sum_univ_succ]; ring

theorem sexticQ_Gv (v : V) : sexticQ (Gv v) = Qv v := by
  rw [sexticQ_eq, Gv_n, Gv_purity, Gv_cubic]
  unfold Qv Nv
  rw [sum12 (fun k => pr v k ^ 2), sum12 (fun k => pr v k ^ 3)]
  simp only [pr, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp
  ring


/-- Swap two coordinates. -/
def swapV (a b : Fin 2 × Fin 2) (v : V) : V := fun p => v (Equiv.swap a b p)

theorem pr_wp (v : V) (k : Fin 12) :
    pr (wp v) k = pr v (![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11] k) := by
  fin_cases k <;> simp [pr, wp, wm, Complex.normSq_apply] <;> ring

theorem pr_wm (v : V) (k : Fin 12) :
    pr (wm v) k = pr v (![8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3] k) := by
  fin_cases k <;> simp [pr, wp, wm, Complex.normSq_apply] <;> ring

theorem pr_swap1 (v : V) (k : Fin 12) :
    pr (swapV (0, 0) (0, 1) v) k = pr v (![1, 0, 2, 3, 5, 4, 6, 7, 9, 8, 10, 11] k) := by
  fin_cases k <;> simp [pr, wp, wm, swapV, Equiv.swap_apply_def, Complex.normSq_apply] <;> ring

theorem pr_swap2 (v : V) (k : Fin 12) :
    pr (swapV (0, 0) (1, 0) v) k = pr v (![2, 1, 0, 3, 4, 7, 6, 5, 10, 9, 8, 11] k) := by
  fin_cases k <;> simp [pr, wp, wm, swapV, Equiv.swap_apply_def, Complex.normSq_apply] <;> ring

theorem pr_swap3 (v : V) (k : Fin 12) :
    pr (swapV (0, 0) (1, 1) v) k = pr v (![3, 1, 2, 0, 7, 5, 6, 4, 11, 9, 10, 8] k) := by
  fin_cases k <;> simp [pr, wp, wm, swapV, Equiv.swap_apply_def, Complex.normSq_apply] <;> ring


/-- Flip the sign of one coordinate. -/
def flipV (j : Fin 2 × Fin 2) (v : V) : V := fun p => if p = j then -v p else v p

set_option maxHeartbeats 4000000 in
theorem pr_flip1 (v : V) (k : Fin 12) :
    pr (flipV (0, 1) v) k = pr v (![0, 1, 2, 3, 11, 10, 9, 8, 7, 6, 5, 4] k) := by
  fin_cases k <;> simp [pr, wp, wm, flipV, Complex.normSq_apply] <;> ring

set_option maxHeartbeats 4000000 in
theorem pr_flip2 (v : V) (k : Fin 12) :
    pr (flipV (1, 0) v) k = pr v (![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7] k) := by
  fin_cases k <;> simp [pr, wp, wm, flipV, Complex.normSq_apply] <;> ring

set_option maxHeartbeats 4000000 in
theorem pr_flip3 (v : V) (k : Fin 12) :
    pr (flipV (1, 1) v) k = pr v (![0, 1, 2, 3, 9, 8, 11, 10, 5, 4, 7, 6] k) := by
  fin_cases k <;> simp [pr, wp, wm, flipV, Complex.normSq_apply] <;> ring

/-- Multiplication by a unit complex number. -/
def smulV (c : ℂ) (v : V) : V := fun p => c * v p

theorem wp_smul (c : ℂ) (v : V) : wp (smulV c v) = smulV c (wp v) := by
  funext p; rcases p with ⟨a, b⟩; fin_cases a <;> fin_cases b <;> simp [wp, smulV] <;> ring

theorem wm_smul (c : ℂ) (v : V) : wm (smulV c v) = smulV c (wm v) := by
  funext p; rcases p with ⟨a, b⟩; fin_cases a <;> fin_cases b <;> simp [wm, smulV] <;> ring

theorem Nv_smul (c : ℂ) (v : V) : Nv (smulV c v) = Complex.normSq c * Nv v := by
  simp [Nv, smulV, Complex.normSq_mul, Finset.mul_sum]

theorem pr_smul (c : ℂ) (v : V) (k : Fin 12) :
    pr (smulV c v) k = Complex.normSq c * pr v k := by
  fin_cases k <;> simp [pr, wp_smul, wm_smul, smulV, Complex.normSq_mul]

/-- `Nv` of the other transforms. -/
theorem Nv_eq_pr (v : V) : Nv v = pr v 0 + pr v 1 + pr v 2 + pr v 3 := by
  simp [Nv, pr, Fintype.sum_prod_type, Fin.sum_univ_two]; ring

/-- `Q` is invariant when the twelve probabilities are permuted and `N` is preserved. -/
theorem Qv_of_perm {u v : V} (σ : Equiv.Perm (Fin 12)) (hN : Nv u = Nv v)
    (h : ∀ k, pr u k = pr v (σ k)) : Qv u = Qv v := by
  have h2 : ∑ k, pr u k ^ 2 = ∑ k, pr v k ^ 2 := by
    simp_rw [h]; exact Equiv.sum_comp σ (fun k => pr v k ^ 2)
  have h3 : ∑ k, pr u k ^ 3 = ∑ k, pr v k ^ 3 := by
    simp_rw [h]; exact Equiv.sum_comp σ (fun k => pr v k ^ 3)
  unfold Qv; rw [h2, h3, hN]

end FormalResearch.FourQubitEntropy.CO
