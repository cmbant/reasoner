module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Cumulative rounding (tool for `int:cheb`)

`CFT/modular_bootstrap/paper/integrality.tex`, proof of Lemma INT-M (`int:cheb`), "Grid and
rounding": for a list of non-negative weights `w_0, …, w_{L-1}` of integer total `N`, with partial
sums `C_i`, put `w̃_i = ⌊C_{i+1}⌋ - ⌊C_i⌋`.  Then `∑ w̃_i = N`, `w̃_i ≥ ⌊w_i⌋`, and the defect against
any sequence `c` is the Abel sum `∑ (w_i - w̃_i) c_i = ∑ S_i (c_i - c_{i+1})`, with
`S_i = {C_{i+1}} ∈ [0,1)` (`int:defect-ibp`, discrete form).  **Proved.**
-/

@[expose] public section

open Finset

namespace FormalResearch.ModularBootstrap.Integrality

/-- Partial sums `C_i = ∑_{r < i} w_r`. -/
def partialSum (w : ℕ → ℝ) (i : ℕ) : ℝ := ∑ r ∈ range i, w r

/-- The rounding defect `S_i = C_{i+1} - ⌊C_{i+1}⌋`. -/
noncomputable def roundDefect (w : ℕ → ℝ) (i : ℕ) : ℝ :=
  partialSum w (i + 1) - (⌊partialSum w (i + 1)⌋₊ : ℝ)

lemma partialSum_nonneg {w : ℕ → ℝ} {L : ℕ} (hw : ∀ i < L, 0 ≤ w i) {i : ℕ} (hi : i ≤ L) :
    0 ≤ partialSum w i :=
  sum_nonneg fun r hr => hw r (lt_of_lt_of_le (mem_range.1 hr) hi)

/-- Abel summation for the rounding defect (no integrality needed). -/
lemma rounding_abel_aux (w : ℕ → ℝ) (c : ℕ → ℝ) (L : ℕ) :
    ∑ i ∈ range L, ((w i) - ((⌊partialSum w (i + 1)⌋₊ : ℝ) - ⌊partialSum w i⌋₊)) * c i =
      ∑ i ∈ range L, roundDefect w i * (c i - c (i + 1)) +
        (partialSum w L - (⌊partialSum w L⌋₊ : ℝ)) * c L := by
  induction L with
  | zero => simp [partialSum]
  | succ L ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    have hps : partialSum w (L + 1) = partialSum w L + w L := by simp [partialSum, sum_range_succ]
    unfold roundDefect
    rw [hps]
    ring

lemma floor_partialSum_zero (w : ℕ → ℝ) : ⌊partialSum w 0⌋₊ = 0 := by simp [partialSum]

/-- **Cumulative rounding.**  Non-negative weights `w_0,…,w_{L-1}` of integer total `N` are
rounded to natural numbers `t_i ≥ ⌊w_i⌋` of the same total, with Abel-summation defect
`∑ (w_i - t_i) c_i = ∑ S_i (c_i - c_{i+1})`, `0 ≤ S_i < 1`. -/
theorem cumulative_rounding (w : ℕ → ℝ) (L : ℕ) (hw : ∀ i < L, 0 ≤ w i) (N : ℕ)
    (hN : ∑ i ∈ range L, w i = N) :
    ∃ t : ℕ → ℕ, (∑ i ∈ range L, t i = N) ∧ (∀ i < L, ⌊w i⌋₊ ≤ t i) ∧
      ∃ S : ℕ → ℝ, (∀ i < L, 0 ≤ S i ∧ S i < 1) ∧
        ∀ c : ℕ → ℝ, ∑ i ∈ range L, ((w i) - t i) * c i = ∑ i ∈ range L, S i * (c i - c (i + 1)) := by
  have hC : ∀ i, i ≤ L → 0 ≤ partialSum w i := fun i hi => partialSum_nonneg hw hi
  have hmono : ∀ i < L, ⌊partialSum w i⌋₊ ≤ ⌊partialSum w (i + 1)⌋₊ := by
    intro i hi
    apply Nat.floor_mono
    have : partialSum w (i + 1) = partialSum w i + w i := by simp [partialSum, sum_range_succ]
    rw [this]; linarith [hw i hi]
  refine ⟨fun i => ⌊partialSum w (i + 1)⌋₊ - ⌊partialSum w i⌋₊, ?_, ?_, roundDefect w, ?_, ?_⟩
  · -- total
    have hcast : ∀ i ∈ range L, (((⌊partialSum w (i + 1)⌋₊ - ⌊partialSum w i⌋₊ : ℕ)) : ℝ) =
        (⌊partialSum w (i + 1)⌋₊ : ℝ) - ⌊partialSum w i⌋₊ := fun i hi => by
      rw [Nat.cast_sub (hmono i (mem_range.1 hi))]
    have hsumR : ((∑ i ∈ range L, (⌊partialSum w (i + 1)⌋₊ - ⌊partialSum w i⌋₊ : ℕ) : ℕ) : ℝ) =
        (N : ℝ) := by
      rw [Nat.cast_sum, sum_congr rfl hcast, sum_range_sub (fun i => (⌊partialSum w i⌋₊ : ℝ))]
      have : partialSum w L = N := hN
      rw [this, Nat.floor_natCast, floor_partialSum_zero]
      simp
    exact_mod_cast hsumR
  · -- t_i ≥ ⌊w_i⌋
    intro i hi
    have h1 : partialSum w (i + 1) = partialSum w i + w i := by simp [partialSum, sum_range_succ]
    have hle : ⌊partialSum w i⌋₊ + ⌊w i⌋₊ ≤ ⌊partialSum w (i + 1)⌋₊ := by
      apply Nat.le_floor
      push_cast
      rw [h1]
      have a1 := Nat.floor_le (hC i hi.le)
      have a2 := Nat.floor_le (hw i hi)
      linarith
    show ⌊w i⌋₊ ≤ ⌊partialSum w (i + 1)⌋₊ - ⌊partialSum w i⌋₊
    omega
  · -- defect in [0,1)
    intro i hi
    have h := hC (i + 1) (by omega)
    unfold roundDefect
    exact ⟨sub_nonneg.2 (Nat.floor_le h), by linarith [Nat.lt_floor_add_one (partialSum w (i + 1))]⟩
  · intro c
    have hcast : ∀ i ∈ range L, ((w i) - (((⌊partialSum w (i + 1)⌋₊ - ⌊partialSum w i⌋₊ : ℕ)) : ℝ)) =
        ((w i) - ((⌊partialSum w (i + 1)⌋₊ : ℝ) - ⌊partialSum w i⌋₊)) := fun i hi => by
      rw [Nat.cast_sub (hmono i (mem_range.1 hi))]
    have h := rounding_abel_aux w c L
    have hL : partialSum w L - (⌊partialSum w L⌋₊ : ℝ) = 0 := by
      have : partialSum w L = N := hN
      rw [this, Nat.floor_natCast]; simp
    rw [hL, zero_mul, add_zero] at h
    rw [← h]
    refine sum_congr rfl fun i hi => ?_
    rw [hcast i hi]

end FormalResearch.ModularBootstrap.Integrality
