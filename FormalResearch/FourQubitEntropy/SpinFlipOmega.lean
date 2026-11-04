module

public import FormalResearch.NQubit.TimeReversal.Omega
public import FormalResearch.NQubit.Pauli.Conjugation
public import FormalResearch.NQubit.Reduced.Purity

/-!
# Balanced-cut purities of `Ω_z` for `m = 3, 4, 5, 6`, and the seven-qubit spin-flip gap

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_graph_parity.tex` and `spinflip_purification.tex`.
For a normalised `m`-qubit `z`, the time-reversal purification `Ω_z` (`FormalResearch.NQubit.TimeReversal.omegaState`) is a unit
`(m+1)`-qubit state whose purity enumerator is given by that of `z`; `balanced_m3`–`balanced_m6` evaluate the
balanced-cut purity for `m = 3, …, 6` by linear algebra from the identities of `NQubit/Reduced/Purity.lean`.

* `seven_spinflip_gap`: for a normalised six-qubit `z`, `Ω_z` is a unit seven-qubit state and its balanced-cut
  purity (average over the 35 three-qubit subsets) is `19/140 + (A₁ + 3A₂ + 6τ₆)/140 ≥ 19/140`;
* `seven_spinflip_gap_eq_iff`: equality iff `z` is two-uniform (`A₁ = A₂ = 0`) with `τ₆(z) = 0`.

Claim class: **proved**.
-/

@[expose] public section

open scoped ComplexConjugate BigOperators Matrix
open FormalResearch.NQubit
open FormalResearch.NQubit.Pauli
open FormalResearch.NQubit.Reduced
open FormalResearch.NQubit.TimeReversal

namespace FormalResearch.FourQubitEntropy.SpinFlip

theorem balanced_m3 (z : Ψ 3) (hz : nsq z = 1) :
    cutPuritySum (omegaState z) 2 / 6 = 1 / 2 := by
  rw [cutPuritySum_split (omegaState z) 0 2 (by norm_num)]
  have hQk := cutPuritySumExcl_omegaState z 2
  have hQn := cutPuritySumExcl_omegaState z 2
  have hsum := sum_weightEnum z
  have hsgn := sum_signed_weightEnum z
  have hA0 := weightEnum_zero z
  have hE1 := cutPuritySum_eq z 1
  have hE2 := cutPuritySum_eq z 2
  have hC1 := cutPuritySum_compl z 1 (by norm_num)
  rw [hz] at hsum hA0
  norm_num [Finset.sum_range_succ, Nat.choose] at hQk hQn hsum hsgn hA0 hE1 hE2 hC1 ⊢
  linear_combination (1/2) * hA0 + (1/6) * hE1 + (-1/12) * hE2 + (-1/3) * hC1 + (1/24) * hQk + (1/24) * hQn

theorem balanced_m4 (z : Ψ 4) (hz : nsq z = 1) :
    cutPuritySum (omegaState z) 2 / 10 = 3 / 10 + (weightEnum z 1 + 4 * tau z) / 20 := by
  rw [cutPuritySum_split (omegaState z) 0 2 (by norm_num)]
  have hQk := cutPuritySumExcl_omegaState z 2
  have hQn := cutPuritySumExcl_omegaState z 3
  have hsum := sum_weightEnum z
  have hsgn := sum_signed_weightEnum z
  have hA0 := weightEnum_zero z
  have hE1 := cutPuritySum_eq z 1
  have hE2 := cutPuritySum_eq z 2
  have hE3 := cutPuritySum_eq z 3
  have hC1 := cutPuritySum_compl z 1 (by norm_num)
  rw [hz] at hsum hA0
  norm_num [Finset.sum_range_succ, Nat.choose] at hQk hQn hsum hsgn hA0 hE1 hE2 hE3 hC1 ⊢
  linear_combination (1/2) * hA0 + (-1/80) * hsum + (1/80) * hsgn + (1/10) * hE1 + (-1/40) * hE3 + (-1/5) * hC1 + (1/40) * hQk + (1/80) * hQn

theorem balanced_m5 (z : Ψ 5) (hz : nsq z = 1) :
    cutPuritySum (omegaState z) 3 / 20 = 1 / 8 + 3 * weightEnum z 2 / 80 := by
  rw [cutPuritySum_split (omegaState z) 0 3 (by norm_num)]
  have hQk := cutPuritySumExcl_omegaState z 3
  have hQn := cutPuritySumExcl_omegaState z 3
  have hsum := sum_weightEnum z
  have hsgn := sum_signed_weightEnum z
  have hA0 := weightEnum_zero z
  have hE1 := cutPuritySum_eq z 1
  have hE2 := cutPuritySum_eq z 2
  have hE3 := cutPuritySum_eq z 3
  have hE4 := cutPuritySum_eq z 4
  have hC1 := cutPuritySum_compl z 1 (by norm_num)
  have hC2 := cutPuritySum_compl z 2 (by norm_num)
  rw [hz] at hsum hA0
  norm_num [Finset.sum_range_succ, Nat.choose] at hQk hQn hsum hsgn hA0 hE1 hE2 hE3 hE4 hC1 hC2 ⊢
  linear_combination (1/8) * hA0 + (1/160) * hQk + (1/160) * hQn

theorem balanced_m6 (z : Ψ 6) (hz : nsq z = 1) :
    cutPuritySum (omegaState z) 3 / 35 = 19 / 140 + (weightEnum z 1 + 3 * weightEnum z 2 + 6 * tau z) / 140 := by
  rw [cutPuritySum_split (omegaState z) 0 3 (by norm_num)]
  have hQk := cutPuritySumExcl_omegaState z 3
  have hQn := cutPuritySumExcl_omegaState z 4
  have hsum := sum_weightEnum z
  have hsgn := sum_signed_weightEnum z
  have hA0 := weightEnum_zero z
  have hE1 := cutPuritySum_eq z 1
  have hE2 := cutPuritySum_eq z 2
  have hE3 := cutPuritySum_eq z 3
  have hE4 := cutPuritySum_eq z 4
  have hE5 := cutPuritySum_eq z 5
  have hC1 := cutPuritySum_compl z 1 (by norm_num)
  have hC2 := cutPuritySum_compl z 2 (by norm_num)
  rw [hz] at hsum hA0
  norm_num [Finset.sum_range_succ, Nat.choose] at hQk hQn hsum hsgn hA0 hE1 hE2 hE3 hE4 hE5 hC1 hC2 ⊢
  linear_combination (5/28) * hA0 + (-3/4480) * hsum + (3/4480) * hsgn + (3/140) * hE1 + (-1/280) * hE2 + (1/1120) * hE4 + (-3/2240) * hE5 + (-3/70) * hC1 + (1/70) * hC2 + (1/280) * hQk + (1/560) * hQn

/-- **Seven-qubit spin-flip gap** (`eq:seven-spinflip-gap`): for a normalised six-qubit `z`,
`Ω_z` is a unit seven-qubit state and its balanced-cut purity (average over the 35 three-qubit
subsets) is `19/140 + (A₁ + 3A₂ + 6τ₆)/140 ≥ 19/140`. -/
theorem seven_spinflip_gap (z : Ψ 6) (hz : nsq z = 1) :
    nsq (omegaState z) = 1 ∧
    cutPuritySum (omegaState z) 3 / 35 = 19 / 140 + (weightEnum z 1 + 3 * weightEnum z 2 + 6 * tau z) / 140 ∧
    19 / 140 ≤ cutPuritySum (omegaState z) 3 / 35 := by
  refine ⟨by rw [nsq_omegaState, hz], balanced_m6 z hz, ?_⟩
  rw [balanced_m6 z hz]
  have h1 := weightEnum_nonneg z 1
  have h2 := weightEnum_nonneg z 2
  have h3 := tau_nonneg z
  linarith

/-- Equality case of the seven-qubit gap: `z` is two-uniform (`A₁ = A₂ = 0`) with `τ₆(z) = 0`. -/
theorem seven_spinflip_gap_eq_iff (z : Ψ 6) (hz : nsq z = 1) :
    cutPuritySum (omegaState z) 3 / 35 = 19 / 140 ↔ weightEnum z 1 = 0 ∧ weightEnum z 2 = 0 ∧ tau z = 0 := by
  rw [balanced_m6 z hz]
  have h1 := weightEnum_nonneg z 1
  have h2 := weightEnum_nonneg z 2
  have h3 := tau_nonneg z
  constructor
  · intro h
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨a, b, c⟩
    rw [a, b, c]; norm_num

end FormalResearch.FourQubitEntropy.SpinFlip
