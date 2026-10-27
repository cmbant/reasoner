import Mathlib
import FormalResearch.FrameFree.OddWordsFock

/-!
# Powers of the total lowering operator (Paper P, `prop:oddwords` (iii))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

For `x z : Cube n` let `z ≤ x` (`Below x z`) mean that `z` is `x` with some `1`s reset to `0`, and
`dd x z` the number of such resets.  `Strat k` is the 0/1 matrix of the pairs with `z ≤ x` and
`dd x z = k`.  `Lm_mul_Strat : Lm n * Strat k = (k+1) • Strat (k+1)`, hence
`Lm_pow_eq : Lm n ^ k = k! • Strat k`: the exponential `exp (t Lm)` has the explicit entries
`t^{dd x z}` (this is the `n`-fold tensor power of the unipotent `(1 0; t 1)`, see `OddWordsGroup`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Matrix

namespace FormalResearch.FrameFree.OddWords

variable {n : ℕ}

/-- `z` is obtained from `x` by resetting some `1`s to `0`. -/
def Below (x z : Cube n) : Prop := ∀ j, z j = 1 → x j = 1

/-- The number of `1`s of `x` reset to `0` in `z`. -/
def dd (x z : Cube n) : ℕ := ∑ j, if x j = 1 ∧ z j = 0 then 1 else 0

open Classical in
/-- The 0/1 matrix of the pairs `z ≤ x` with `dd x z = k`. -/
noncomputable def Strat (n k : ℕ) : Matrix (Cube n) (Cube n) ℝ :=
  Matrix.of fun x z => if Below x z ∧ dd x z = k then 1 else 0

theorem dd_update (x z : Cube n) (i : Fin n) (hx : x i = 1) :
    dd (Function.update x i 0) z + (if z i = 0 then 1 else 0) = dd x z := by
  unfold dd
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h : ∑ j ∈ univ.erase i, (if Function.update x i 0 j = 1 ∧ z j = 0 then 1 else 0)
      = ∑ j ∈ univ.erase i, (if x j = 1 ∧ z j = 0 then 1 else 0) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h]
  simp [hx]
  omega

theorem below_update (x z : Cube n) (i : Fin n) (hx : x i = 1) :
    Below (Function.update x i 0) z ↔ Below x z ∧ z i = 0 := by
  constructor
  · intro h
    have hzi : z i = 0 := by
      have := h i
      rcases Fin.exists_fin_two.1 ⟨z i, rfl⟩ with h0 | h0
      · exact h0
      · exfalso; have := this h0; simp at this
    refine ⟨fun j hj => ?_, hzi⟩
    by_cases hji : j = i
    · subst hji; rw [hzi] at hj; exact absurd hj (by decide)
    · have := h j hj; rwa [Function.update_of_ne hji] at this
  · rintro ⟨h, hzi⟩ j hj
    by_cases hji : j = i
    · subst hji; rw [hzi] at hj; exact absurd hj (by decide)
    · rw [Function.update_of_ne hji]; exact h j hj

theorem Lm_mul_Strat (k : ℕ) : Lm n * Strat n k = ((k : ℝ) + 1) • Strat n (k + 1) := by
  classical
  ext x z
  simp only [Matrix.mul_apply, Lm_apply, Strat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ i : Fin n, ∑ y : Cube n, (if x i = 1 ∧ y = Function.update x i 0 then (1 : ℝ) else 0) *
      (if Below y z ∧ dd y z = k then 1 else 0)
      = if x i = 1 ∧ Below (Function.update x i 0) z ∧ dd (Function.update x i 0) z = k then 1 else 0 := by
    intro i
    by_cases hx : x i = 1
    · rw [Finset.sum_eq_single (Function.update x i 0)]
      · simp [hx]
      · intro y _ hy; simp [hy]
      · simp
    · simp [hx]
  simp_rw [h1]
  have h2 : ∀ i : Fin n, (if x i = 1 ∧ Below (Function.update x i 0) z ∧ dd (Function.update x i 0) z = k
      then (1 : ℝ) else 0) =
      if (Below x z ∧ dd x z = k + 1) ∧ (x i = 1 ∧ z i = 0) then 1 else 0 := by
    intro i
    by_cases hx : x i = 1
    · have e1 := below_update x z i hx
      have e2 := dd_update x z i hx
      by_cases hz : z i = 0
      · rw [hz] at e2
        simp only [ite_true] at e2
        simp only [hx, true_and, e1, hz, and_true]
        have : dd (Function.update x i 0) z = k ↔ dd x z = k + 1 := by omega
        simp only [this]
      · have : ¬ z i = 0 := hz
        simp [hx, this, e1]
    · simp [hx]
  simp_rw [h2]
  by_cases hP : Below x z ∧ dd x z = k + 1
  · simp only [hP, true_and, ite_true, mul_one]
    have : ∑ i : Fin n, (if x i = 1 ∧ z i = 0 then (1 : ℝ) else 0) = (dd x z : ℝ) := by
      unfold dd; push_cast; rfl
    rw [this, hP.2]; push_cast; ring
  · simp [hP]

theorem Strat_zero : Strat n 0 = 1 := by
  classical
  ext x z
  simp only [Strat, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = z
  · subst h
    have : dd x x = 0 := by
      unfold dd; refine Finset.sum_eq_zero fun j _ => ?_
      rcases Fin.exists_fin_two.1 ⟨x j, rfl⟩ with h | h <;> simp [h]
    simp [this, Below]
  · simp only [h, ite_false]
    rw [ite_eq_right_iff]
    rintro ⟨hb, hd⟩
    exfalso
    apply h
    funext j
    have h0 : (if x j = 1 ∧ z j = 0 then 1 else 0) = 0 := by
      unfold dd at hd
      exact (Finset.sum_eq_zero_iff.1 hd) j (Finset.mem_univ j)
    have h1 := hb j
    rcases Fin.exists_fin_two.1 ⟨x j, rfl⟩ with ha | ha <;>
      rcases Fin.exists_fin_two.1 ⟨z j, rfl⟩ with hb' | hb' <;> simp_all

theorem Lm_pow_eq (k : ℕ) : Lm n ^ k = (k.factorial : ℝ) • Strat n k := by
  induction k with
  | zero => simp [Strat_zero]
  | succ k ih =>
    rw [pow_succ', ih, Matrix.mul_smul, Lm_mul_Strat, smul_smul, Nat.factorial_succ]
    push_cast; ring_nf

end FormalResearch.FrameFree.OddWords
