import Mathlib

namespace FormalResearch.Blaschke

open scoped BigOperators symmDiff

/-- The ±1 Boolean coordinate used in the Blaschke zero-flip family. -/
def booleanSign {n : Nat} (S : Finset (Fin n)) (j : Fin n) : ℚ :=
  if j ∈ S then 1 else -1

/-- Walsh character indexed by a subset T of the flip coordinates. -/
def walshCharacter {n : Nat} (T S : Finset (Fin n)) : ℚ :=
  ∏ j ∈ T, booleanSign S j

/-- Toggle one Boolean coordinate by symmetric difference. -/
def toggleSubset {n : Nat} (k : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S ∆ {k}

/-- Toggling a fixed coordinate is an involutive equivalence of the Boolean cube. -/
def toggleEquiv {n : Nat} (k : Fin n) : Finset (Fin n) ≃ Finset (Fin n) where
  toFun := toggleSubset k
  invFun := toggleSubset k
  left_inv := by
    intro S
    ext i
    by_cases hik : i = k <;> subst_vars <;>
      simp [toggleSubset, Finset.mem_symmDiff]
  right_inv := by
    intro S
    ext i
    by_cases hik : i = k <;> subst_vars <;>
      simp [toggleSubset, Finset.mem_symmDiff]

lemma booleanSign_toggle_same {n : Nat} (S : Finset (Fin n)) (k : Fin n) :
    booleanSign (toggleSubset k S) k = - booleanSign S k := by
  by_cases hk : k ∈ S <;> simp [booleanSign, toggleSubset, Finset.mem_symmDiff, hk]

lemma booleanSign_toggle_other {n : Nat} (S : Finset (Fin n)) {j k : Fin n}
    (hjk : j ≠ k) :
    booleanSign (toggleSubset k S) j = booleanSign S j := by
  by_cases hj : j ∈ S <;>
    simp [booleanSign, toggleSubset, Finset.mem_symmDiff, hj, hjk]

/-- A Walsh character changes sign when one of its own coordinates is toggled. -/
lemma walshCharacter_toggle {n : Nat} (T S : Finset (Fin n)) {k : Fin n}
    (hk : k ∈ T) :
    walshCharacter T (toggleSubset k S) = - walshCharacter T S := by
  unfold walshCharacter
  rw [← Finset.prod_erase_mul T (fun j => booleanSign (toggleSubset k S) j) hk]
  rw [← Finset.prod_erase_mul T (fun j => booleanSign S j) hk]
  have herase :
      (∏ j ∈ T.erase k, booleanSign (toggleSubset k S) j) =
        ∏ j ∈ T.erase k, booleanSign S j := by
    apply Finset.prod_congr rfl
    intro j hj
    exact booleanSign_toggle_other S (Finset.ne_of_mem_erase hj)
  rw [herase, booleanSign_toggle_same]
  ring

/-- If k lies in T but k≠j, the product χ_T(S) x_j(S) changes sign under
coordinate-k toggling. -/
lemma walsh_coordinate_term_toggle {n : Nat} (T S : Finset (Fin n)) {j k : Fin n}
    (hk : k ∈ T) (hkj : k ≠ j) :
    walshCharacter T (toggleSubset k S) * booleanSign (toggleSubset k S) j =
      -(walshCharacter T S * booleanSign S j) := by
  rw [walshCharacter_toggle T S hk,
    booleanSign_toggle_other S hkj.symm]
  ring

/-- Boolean orthogonality against one coordinate: any Walsh character
containing another coordinate has zero correlation with x_j. -/
theorem walsh_coordinate_orthogonal {n : Nat} (T : Finset (Fin n)) {j k : Fin n}
    (hk : k ∈ T) (hkj : k ≠ j) :
    (∑ S : Finset (Fin n), walshCharacter T S * booleanSign S j) = 0 := by
  let F : Finset (Fin n) → ℚ := fun S => walshCharacter T S * booleanSign S j
  have hperm := (toggleEquiv k).sum_comp F
  have hneg : ∀ S : Finset (Fin n), F (toggleEquiv k S) = -F S := by
    intro S
    exact walsh_coordinate_term_toggle T S hk hkj
  have hs : (∑ S, F S) = -(∑ S, F S) := by
    calc
      (∑ S, F S) = ∑ S, F (toggleEquiv k S) := hperm.symm
      _ = ∑ S, -F S := by apply Fintype.sum_congr; intro S; rw [hneg]
      _ = -(∑ S, F S) := by simp
  dsimp [F] at hs ⊢
  linarith

/-- A finite set with at least two elements always contains an element distinct
from any prescribed coordinate. -/
lemma exists_mem_ne_of_one_lt_card {n : Nat} (T : Finset (Fin n))
    (hT : 1 < T.card) (j : Fin n) : ∃ k ∈ T, k ≠ j := by
  by_contra h
  push_neg at h
  have hsub : T ⊆ {j} := by
    intro k hk
    simp [h k hk]
  have hc := Finset.card_le_card hsub
  simp at hc
  omega

/-- Hence every Walsh character of level at least two is orthogonal to every
linear Boolean coordinate. -/
theorem walsh_coordinate_orthogonal_of_card {n : Nat} (T : Finset (Fin n))
    (hT : 1 < T.card) (j : Fin n) :
    (∑ S : Finset (Fin n), walshCharacter T S * booleanSign S j) = 0 := by
  obtain ⟨k, hk, hkj⟩ := exists_mem_ne_of_one_lt_card T hT j
  exact walsh_coordinate_orthogonal T hk hkj

/-- Full Boolean collapse for a linear sign observable.  The Wronskian sign
formula in the Blaschke handoff has exactly this form, so all Walsh levels
`|T|≥2` vanish after applying that linearized Wronskian map; in particular all
odd levels at least three lie in its kernel. -/
theorem walsh_linear_sign_collapse {n : Nat} (T : Finset (Fin n))
    (hT : 1 < T.card) (c : Fin n → ℚ) :
    (∑ S : Finset (Fin n),
      walshCharacter T S * (∑ j : Fin n, c j * booleanSign S j)) = 0 := by
  calc
    (∑ S : Finset (Fin n),
      walshCharacter T S * (∑ j : Fin n, c j * booleanSign S j)) =
      ∑ S : Finset (Fin n), ∑ j : Fin n,
        walshCharacter T S * (c j * booleanSign S j) := by
          apply Fintype.sum_congr
          intro S
          rw [Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ S : Finset (Fin n),
        walshCharacter T S * (c j * booleanSign S j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin n, c j *
        (∑ S : Finset (Fin n), walshCharacter T S * booleanSign S j) := by
          apply Fintype.sum_congr
          intro j
          rw [Finset.mul_sum]
          apply Fintype.sum_congr
          intro S
          ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [walsh_coordinate_orthogonal_of_card T hT j, mul_zero]

/-- Module-valued version of the same collapse.  This is the form needed for
polynomial-valued Wronskian atoms: every degree-≥2 Walsh character annihilates
an arbitrary linear combination of Boolean signs with coefficients in a
`ℚ`-module. -/
theorem walsh_linear_sign_collapse_smul {n : Nat} {M : Type*}
    [AddCommGroup M] [Module ℚ M]
    (T : Finset (Fin n)) (hT : 1 < T.card) (c : Fin n → M) :
    (∑ S : Finset (Fin n),
      walshCharacter T S • (∑ j : Fin n, booleanSign S j • c j)) = 0 := by
  calc
    (∑ S : Finset (Fin n),
      walshCharacter T S • (∑ j : Fin n, booleanSign S j • c j)) =
      ∑ S : Finset (Fin n), ∑ j : Fin n,
        (walshCharacter T S * booleanSign S j) • c j := by
          apply Fintype.sum_congr
          intro S
          rw [Finset.smul_sum]
          apply Fintype.sum_congr
          intro j
          rw [smul_smul]
    _ = ∑ j : Fin n, ∑ S : Finset (Fin n),
        (walshCharacter T S * booleanSign S j) • c j := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin n,
        (∑ S : Finset (Fin n), walshCharacter T S * booleanSign S j) • c j := by
          apply Fintype.sum_congr
          intro j
          rw [Finset.sum_smul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [walsh_coordinate_orthogonal_of_card T hT j, zero_smul]

end FormalResearch.Blaschke
