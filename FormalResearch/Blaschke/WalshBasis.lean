import Mathlib
import FormalResearch.Blaschke.WalshWronskianLinearMap

namespace FormalResearch.Blaschke

open scoped BigOperators

lemma walshCharacter_toggle_not_mem {n : Nat}
    (T S : Finset (Fin n)) {k : Fin n} (hk : k ∉ T) :
    walshCharacter T (toggleSubset k S) = walshCharacter T S := by
  unfold walshCharacter
  apply Finset.prod_congr rfl
  intro j hj
  exact booleanSign_toggle_other S (by
    intro hjk
    subst j
    exact hk hj)

/-- Every Walsh character takes values ±1, hence has pointwise square one. -/
theorem walshCharacter_mul_self {n : Nat} (T S : Finset (Fin n)) :
    walshCharacter T S * walshCharacter T S = 1 := by
  unfold walshCharacter
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j hj
  by_cases hjs : j ∈ S <;> simp [booleanSign, hjs]

/-- Distinct Walsh characters have zero correlation on the full Boolean cube;
a character has squared norm `2^n`. -/
theorem walshCharacter_orthogonal {n : Nat}
    (T U : Finset (Fin n)) :
    (∑ S : Finset (Fin n), walshCharacter T S * walshCharacter U S) =
      if T = U then (((2^n : Nat) : ℚ)) else 0 := by
  by_cases hTU : T = U
  · subst U
    simp_rw [walshCharacter_mul_self]
    simp [Fintype.card_finset, Fintype.card_fin]
  · have hsymm : (T ∆ U).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hzero
      have : T = U := by
        ext k
        have hk := congrArg (fun V : Finset (Fin n) => k ∈ V) hzero
        simp [Finset.mem_symmDiff] at hk
        tauto
      exact hTU this
    obtain ⟨k, hk⟩ := hsymm
    have hmem : (k ∈ T ∧ k ∉ U) ∨ (k ∉ T ∧ k ∈ U) := by
      simpa [Finset.mem_symmDiff] using hk
    let F : Finset (Fin n) → ℚ :=
      fun S => walshCharacter T S * walshCharacter U S
    have hneg : ∀ S : Finset (Fin n), F (toggleEquiv k S) = -F S := by
      intro S
      rcases hmem with h | h
      · rw [show toggleEquiv k S = toggleSubset k S from rfl,
          walshCharacter_toggle T S h.1,
          walshCharacter_toggle_not_mem U S h.2]
        ring
      · rw [show toggleEquiv k S = toggleSubset k S from rfl,
          walshCharacter_toggle_not_mem T S h.1,
          walshCharacter_toggle U S h.2]
        ring
    have hperm := (toggleEquiv k).sum_comp F
    have hs : (∑ S, F S) = -(∑ S, F S) := by
      calc
        (∑ S, F S) = ∑ S, F (toggleEquiv k S) := hperm.symm
        _ = ∑ S, -F S := by
          apply Fintype.sum_congr
          intro S
          rw [hneg]
        _ = -(∑ S, F S) := by simp
    simp [hTU]
    dsimp [F] at hs
    linarith

/-- The `2^n` Walsh coefficient vectors form a linearly independent family in
the full function space on the Boolean cube. -/
theorem walshVector_linearIndependent {n : Nat} :
    LinearIndependent ℚ (fun T : Finset (Fin n) => walshVector T) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha T
  have hpoint : ∀ S : Finset (Fin n),
      (∑ U : Finset (Fin n), a U * walshCharacter U S) = 0 := by
    intro S
    have hS := congrFun ha S
    simpa [walshVector, Pi.smul_apply, smul_eq_mul] using hS
  have hcorr :
      (∑ S : Finset (Fin n),
        (∑ U : Finset (Fin n), a U * walshCharacter U S) *
          walshCharacter T S) = 0 := by
    simp_rw [hpoint, zero_mul]
    simp
  rw [Finset.sum_mul, Fintype.sum_comm] at hcorr
  simp_rw [← mul_assoc, walshCharacter_orthogonal] at hcorr
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_pos] at hcorr
  have hpow : (((2^n : Nat) : ℚ)) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hcorr).resolve_right hpow

/-- Since the Walsh family has exactly the dimension of the Boolean function
space, it is a basis. -/
noncomputable def walshBasis (n : Nat) :
    Basis (Finset (Fin n)) ℚ (Finset (Fin n) → ℚ) :=
  basisOfLinearIndependentOfCardEqFinrank walshVector_linearIndependent (by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_finset, Fintype.card_fin])

end FormalResearch.Blaschke
