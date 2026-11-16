/-
Copyright (c) 2026 Antony Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antony Lewis
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJSymmetry

/-!

# Recoupling coefficients with a vanishing spin

The recoupling coefficient of `SixJ` when `j₁ = 0` or `j₃ = 0` is `1`.

## i. Overview

All spins are doubled naturals, as in `SixJ`. The comparison `sixJ_eq_sixJSym` with the symmetric
sum of 3j symbols needs `0 < a`, because it uses the independence of the recoupling coefficient
of `M`. The cases `a = 0` and `c = 0` are therefore treated directly, at `M = J`, where `sixJ` is
defined.

1. A Clebsch–Gordan coefficient with a vanishing spin is a Kronecker delta:
   `⟨0 0, j m | j m⟩ = 1` (`cgCoefficient_zero_left`) and `⟨j m, 0 0 | j m⟩ = 1`
   (`cgCoefficient_zero_right`), by induction on `m` with the lowering operator.
2. For `a = 0` (then `k₁ = 0` and `K = k₃`) or `c = 0` (then `k₃ = 0` and `K = k₁`) the sum over
   four Clebsch–Gordan coefficients of `recoupling_eq_sum` collapses to the orthogonality sum
   for `V(b) ⊗ V(c)`, respectively `V(a) ⊗ V(b)`: `recoupling_zero_left` and
   `recoupling_zero_right` show that the recoupling coefficient is `1`.

## ii. Key results

- `cgCoefficient_zero_left`, `cgCoefficient_zero_right`: Clebsch–Gordan coefficients with a
  vanishing spin.
- `recoupling_zero_left`, `recoupling_zero_right`: the recoupling coefficient for `a = 0`,
  respectively `c = 0`.

## iii. Table of contents

- A. Clebsch–Gordan coefficients with a vanishing spin
- B. The recoupling coefficient

## iv. References

- A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press (1957),
  chapter 6.

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open StandardSl2Module

open scoped TensorProduct

/-!

## A. Clebsch–Gordan coefficients with a vanishing spin

-/

lemma ρE_normVec_zero (n : ℕ) : (ρE : Module.End ℝ (StandardSl2Module ℝ n)) (normVec n 0) = 0 := by
  rw [normVec, map_smul, ρE_vNat_zero, smul_zero]

/-- `⟨0 0, j m | j m⟩ = 1`: coupling to a vanishing spin does not change the state. -/
lemma cgCoefficient_zero_left {n l ν : ℕ} (hl : l ≤ n) (hν : ν ≤ n) :
    cgCoefficient 0 n 0 l 0 ν = if ν = l then 1 else 0 := by
  induction l generalizing ν with
  | zero =>
    by_cases h : ν = 0
    · subst h
      simp [cgCoefficient_stretched]
    · rw [ite_eq_right h, cgCoefficient_eq_zero_of_ne (by omega) (Nat.zero_le _) (Nat.zero_le _)
        (by omega)]
  | succ l ih =>
    by_cases h : ν = l + 1
    · subst h
      rw [ite_eq_left rfl]
      have hF := tensorF_coupledVec (m := 0) (n := n) (k := 0) (l := l) (Nat.zero_le _)
        (Nat.zero_le _) (by omega)
      have hE : tensorE 0 n (normVec 0 0 ⊗ₜ normVec n (l + 1)) =
          Real.sqrt (((l : ℝ) + 1) * (((0 + n - 2 * 0 : ℕ) : ℝ) - l)) •
            (normVec 0 0 ⊗ₜ normVec n l) := by
        rw [tensorE, diagEnd_tmul, ρE_normVec_zero, TensorProduct.zero_tmul,
          ρE_normVec_succ (by omega), TensorProduct.tmul_smul]
        simp
      have hr : 0 < Real.sqrt (((l : ℝ) + 1) * (((0 + n - 2 * 0 : ℕ) : ℝ) - l)) := by
        refine Real.sqrt_pos.mpr (mul_pos (by positivity) ?_)
        have : (l : ℝ) + 1 ≤ n := by exact_mod_cast hl
        simp only [Nat.zero_add, mul_zero, Nat.sub_zero]
        linarith
      have key := tensorForm_tensorE (normVec 0 0 ⊗ₜ normVec n (l + 1)) (coupledVec 0 n 0 l)
      rw [hE, hF] at key
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at key
      rw [← cgCoefficient, ← cgCoefficient, ih (by omega) (by omega),
        ite_eq_left (rfl : l = l)] at key
      exact mul_left_cancel₀ hr.ne'
        (by linarith : _ * cgCoefficient 0 n 0 (l + 1) 0 (l + 1) = _ * 1)
    · rw [ite_eq_right h, cgCoefficient_eq_zero_of_ne (by omega) (Nat.zero_le _) (Nat.zero_le _)
        (by omega)]

/-- `⟨j m, 0 0 | j m⟩ = 1`. -/
lemma cgCoefficient_zero_right {m l α : ℕ} (hl : l ≤ m) (hα : α ≤ m) :
    cgCoefficient m 0 0 l α 0 = if α = l then 1 else 0 := by
  induction l generalizing α with
  | zero =>
    by_cases h : α = 0
    · subst h
      simp [cgCoefficient_stretched]
    · rw [ite_eq_right h, cgCoefficient_eq_zero_of_ne (by omega) (Nat.zero_le _) (Nat.zero_le _)
        (by omega)]
  | succ l ih =>
    by_cases h : α = l + 1
    · subst h
      rw [ite_eq_left rfl]
      have hF := tensorF_coupledVec (m := m) (n := 0) (k := 0) (l := l) (Nat.zero_le _)
        (Nat.zero_le _) (by omega)
      have hE : tensorE m 0 (normVec m (l + 1) ⊗ₜ normVec 0 0) =
          Real.sqrt (((l : ℝ) + 1) * (((m + 0 - 2 * 0 : ℕ) : ℝ) - l)) •
            (normVec m l ⊗ₜ normVec 0 0) := by
        rw [tensorE, diagEnd_tmul, ρE_normVec_zero, TensorProduct.tmul_zero,
          ρE_normVec_succ (by omega), TensorProduct.smul_tmul']
        simp
      have hr : 0 < Real.sqrt (((l : ℝ) + 1) * (((m + 0 - 2 * 0 : ℕ) : ℝ) - l)) := by
        refine Real.sqrt_pos.mpr (mul_pos (by positivity) ?_)
        have : (l : ℝ) + 1 ≤ m := by exact_mod_cast hl
        simp only [Nat.add_zero, mul_zero, Nat.sub_zero]
        linarith
      have key := tensorForm_tensorE (normVec m (l + 1) ⊗ₜ normVec 0 0) (coupledVec m 0 0 l)
      rw [hE, hF] at key
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at key
      rw [← cgCoefficient, ← cgCoefficient, ih (by omega) (by omega),
        ite_eq_left (rfl : l = l)] at key
      exact mul_left_cancel₀ hr.ne'
        (by linarith : _ * cgCoefficient m 0 0 (l + 1) (l + 1) 0 = _ * 1)
    · rw [ite_eq_right h, cgCoefficient_eq_zero_of_ne (by omega) (Nat.zero_le _) (Nat.zero_le _)
        (by omega)]

/-!

## B. The recoupling coefficient

-/

/-- For `a = 0` the recoupling coefficient at `M = J` is `1`. -/
lemma recoupling_zero_left {b c K : ℕ} (hab : 0 < 0 + b) (hbc : 0 < b + c)
    {k₁ : Fin (min 0 b + 1)} {k₃ : Fin (min b c + 1)} (hA : ValidA 0 b c K k₁)
    (hB : ValidB 0 b c K k₃) : recoupling hab hbc K 0 k₁ k₃ = 1 := by
  have h₁ := k₁.isLt
  have h₃ := k₃.isLt
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have e₁ : (k₁ : ℕ) = 0 := by omega
  have e₃ : (k₃ : ℕ) = K := by omega
  have eKb : K ≤ b := by omega
  have eKc : K ≤ c := by omega
  rw [recoupling_eq_sum, e₁, e₃]
  simp only [Nat.zero_add, mul_zero, Nat.sub_zero, Nat.sub_self, Finset.sum_range_one]
  have h1 : ∀ x₂ x₁ : ℕ, ∑ x ∈ Finset.range (b + c - 2 * K + 1),
      cgCoefficient 0 (b + c - 2 * K) 0 0 0 x * cgCoefficient b c K x x₂ x₁ =
        cgCoefficient b c K 0 x₂ x₁ := by
    intro x₂ x₁
    rw [Finset.sum_eq_single 0]
    · rw [cgCoefficient_zero_left (Nat.zero_le _) (Nat.zero_le _), ite_eq_left rfl, one_mul]
    · intro ν hν hne
      rw [cgCoefficient_zero_left (Nat.zero_le _) (by simpa [Nat.lt_succ_iff] using hν),
        ite_eq_right hne, zero_mul]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
  have h2 : ∀ μ ∈ Finset.range (b + 1), ∀ γ : ℕ, cgCoefficient b c K 0 μ γ *
      ∑ β ∈ Finset.range (b + 1), cgCoefficient 0 b 0 μ 0 β * cgCoefficient b c K 0 β γ =
        cgCoefficient b c K 0 μ γ * cgCoefficient b c K 0 μ γ := by
    intro μ hμ γ
    have hμb : μ ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hμ)
    rw [Finset.sum_eq_single μ]
    · rw [cgCoefficient_zero_left hμb hμb, ite_eq_left rfl, one_mul]
    · intro β hβ hne
      rw [cgCoefficient_zero_left hμb (Nat.lt_succ_iff.mp (Finset.mem_range.mp hβ)),
        ite_eq_right hne, zero_mul]
    · intro h
      exact absurd hμ h
  simp only [h1]
  rw [Finset.sum_congr rfl fun μ hμ => Finset.sum_congr rfl fun γ _ => h2 μ hμ γ]
  exact (sum_cgCoefficient_mul hbc eKb eKc eKb eKc (Nat.zero_le _)).trans (by simp)

/-- For `c = 0` the recoupling coefficient at `M = J` is `1`. -/
lemma recoupling_zero_right {a b K : ℕ} (hab : 0 < a + b) (hbc : 0 < b + 0)
    {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b 0 + 1)} (hA : ValidA a b 0 K k₁)
    (hB : ValidB a b 0 K k₃) : recoupling hab hbc K 0 k₁ k₃ = 1 := by
  have h₁ := k₁.isLt
  have h₃ := k₃.isLt
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have e₁ : (k₁ : ℕ) = K := by omega
  have e₃ : (k₃ : ℕ) = 0 := by omega
  have eKa : K ≤ a := by omega
  have eKb : K ≤ b := by omega
  rw [recoupling_eq_sum, e₁, e₃]
  simp only [Nat.add_zero, Nat.zero_add, mul_zero, Nat.sub_zero, Nat.sub_self,
    Finset.sum_range_one]
  have h1 : ∀ α β : ℕ, β ≤ b → ∑ ν ∈ Finset.range (b + 1),
      cgCoefficient a b K 0 α ν * cgCoefficient b 0 0 ν β 0 = cgCoefficient a b K 0 α β := by
    intro α β hβ
    rw [Finset.sum_eq_single β]
    · rw [cgCoefficient_zero_right hβ hβ, ite_eq_left rfl, mul_one]
    · intro ν hν hne
      rw [cgCoefficient_zero_right (Nat.lt_succ_iff.mp (Finset.mem_range.mp hν)) hβ,
        ite_eq_right (Ne.symm hne), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hβ)) h
  rw [Finset.sum_eq_single 0]
  · rw [cgCoefficient_zero_right (Nat.zero_le _) (Nat.zero_le _), ite_eq_left rfl, one_mul]
    rw [Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β hβ => by
      rw [h1 α β (Nat.lt_succ_iff.mp (Finset.mem_range.mp hβ))]]
    exact (sum_cgCoefficient_mul hab eKa eKb eKa eKb (Nat.zero_le _)).trans (by simp)
  · intro μ hμ hne
    rw [cgCoefficient_zero_right (Nat.zero_le _) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hμ)),
      ite_eq_right hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

end PhyslibAlpha.Sl2
