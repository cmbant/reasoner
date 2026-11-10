module

public import FormalResearch.NQubit.Shadow.Stabilizer
public import FormalResearch.NQubit.Reduced.MeanPurity
public import FormalResearch.NQubit.Pauli.Hermitian

/-!
# Seven-qubit stabilizer states: `π₃ ≥ 19/140` (`prop:stab7`)

`QI/multiqubit_entanglement/seven_qubit_entanglement/icosahedral_state.tex`, `prop:stab7`: every seven-qubit
stabilizer state has `π₃ ≥ 19/140`, hence the seven-qubit minimum `121/917` is not attained by a stabilizer state.

The paper's proof is reproduced in Lean for every stabilizer state (`IsStabilizerState`: `2^7` commuting Pauli
words, each with `⟨P⟩² = 1`), not only for graph states:

* `pi3_identity`: `280 π₃ = 35 + 15 A₁ + 5 A₂ + A₃` for every unit seven-qubit vector;
* `shadow_identity`: `4 S₁ = 7 + A₁ + A₂ - A₃`, from complementarity of the mean purities `π_s = π_{7-s}` and
  `Σ A_j = 2^7`, with `S_1 = shadowCoeff ψ 1` the shadow coefficient of Rains' transform;
* `stab7`: for a stabilizer state `A_j` and `S_1` are non-negative integers (`NQubit/Shadow/Stabilizer`),
  which forces `15 A₁ + 5 A₂ + A₃ ≥ 3`, hence `π₃ ≥ 38/280 = 19/140`;
* `stab7_ne_ico`: no seven-qubit stabilizer state has `π₃ = 121/917`.

Sharpness is the Fano/wheel graph state of `SevenQubitStab7` (`pi3_witness`).
-/

@[expose] public section


open FormalResearch.NQubit FormalResearch.NQubit.Pauli FormalResearch.NQubit.Shadow
  FormalResearch.NQubit.Reduced FormalResearch.NQubit.TimeReversal

namespace FormalResearch.FourQubitEntropy.SevenQubitStabilizer

variable (ψ : Ψ 7)

theorem purity_rel (hψ : nsq ψ = 1) :
    weightEnum ψ 0 = 1 ∧ ∑ j ∈ Finset.range 8, weightEnum ψ j = 128 ∧
    meanPurity ψ 1 = meanPurity ψ 6 ∧ meanPurity ψ 2 = meanPurity ψ 5 ∧
    meanPurity ψ 3 = meanPurity ψ 4 := by
  refine ⟨weightEnum_zero_of_unit ψ hψ, ?_, meanPurity_compl ψ (by norm_num : 1 ≤ 7),
    meanPurity_compl ψ (by norm_num : 2 ≤ 7), meanPurity_compl ψ (by norm_num : 3 ≤ 7)⟩
  rw [sum_weightEnum, hψ]; norm_num

/-- `280 π₃ = 35 + 15 A₁ + 5 A₂ + A₃`. -/
theorem pi3_identity (hψ : nsq ψ = 1) :
    280 * meanPurity ψ 3 = 35 + 15 * weightEnum ψ 1 + 5 * weightEnum ψ 2 + weightEnum ψ 3 := by
  rw [meanPurity_eq_lin ψ (by norm_num : 3 ≤ 7)]
  have h0 := weightEnum_zero_of_unit ψ hψ
  simp [Finset.sum_range_succ, aQ, Nat.choose, h0]
  ring

/-- `4 S₁ = 7 + A₁ + A₂ - A₃`. -/
theorem shadow_identity (hψ : nsq ψ = 1) :
    4 * shadowCoeff ψ 1 = 7 + weightEnum ψ 1 + weightEnum ψ 2 - weightEnum ψ 3 := by
  obtain ⟨h0, hs, h16, h25, h34⟩ := purity_rel ψ hψ
  rw [shadowCoeff_eq_lin]
  rw [meanPurity_eq_lin ψ (by norm_num : 1 ≤ 7), meanPurity_eq_lin ψ (by norm_num : 6 ≤ 7)] at h16
  rw [meanPurity_eq_lin ψ (by norm_num : 2 ≤ 7), meanPurity_eq_lin ψ (by norm_num : 5 ≤ 7)] at h25
  rw [meanPurity_eq_lin ψ (by norm_num : 3 ≤ 7), meanPurity_eq_lin ψ (by norm_num : 4 ≤ 7)] at h34
  simp [Finset.sum_range_succ, aQ, shQ, Nat.choose] at h16 h25 h34 hs ⊢
  linarith

/-- **`prop:stab7`**: every seven-qubit stabilizer state has `π₃ ≥ 19/140`. -/
theorem stab7 (h : IsStabilizerState ψ) : (19 : ℝ) / 140 ≤ meanPurity ψ 3 := by
  have hψ := h.1
  obtain ⟨m1, h1⟩ := h.weightEnum_nat 1
  obtain ⟨m2, h2⟩ := h.weightEnum_nat 2
  obtain ⟨m3, h3⟩ := h.weightEnum_nat 3
  obtain ⟨s, hs⟩ := h.shadowCoeff_nat 1
  have hp := pi3_identity ψ hψ
  have hsh := shadow_identity ψ hψ
  rw [h1, h2, h3] at hp hsh
  rw [hs] at hsh
  have hz : (4 * s : ℤ) = 7 + m1 + m2 - m3 := by exact_mod_cast hsh
  have hge : (3 : ℤ) ≤ 15 * m1 + 5 * m2 + m3 := by omega
  have hge' : (3 : ℝ) ≤ 15 * m1 + 5 * m2 + m3 := by exact_mod_cast hge
  linarith

/-- No seven-qubit stabilizer state has `π₃ = 121/917`, the value of the icosahedral state. -/
theorem stab7_ne_ico (h : IsStabilizerState ψ) : meanPurity ψ 3 ≠ 121 / 917 := by
  intro he
  have := stab7 ψ h
  rw [he] at this
  norm_num at this

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitStabilizer.stab7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stab7

/-- info: 'FormalResearch.FourQubitEntropy.SevenQubitStabilizer.shadow_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shadow_identity

end FormalResearch.FourQubitEntropy.SevenQubitStabilizer
