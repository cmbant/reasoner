module

public import FormalResearch.Racah.P2ThreeJVanish

/-!
# The `3j` recurrences at the boundary rows (all rows)

`threeJ_recurrence` (DLMF 34.3.15) and `threeJ_recurrence_m` (DLMF 34.3.14) are stated in the
library under the hypothesis that all three symbols involved are admissible.  Here the hypotheses
on the *neighbouring* symbols are dropped: only the symbol in the middle is required to be
admissible.  When a neighbour is not admissible its Racah sum vanishes
(`racahSum3_zero_of_not_isNat`), so the neighbour is `0` and the corresponding term of the
recurrence is absent -- exactly the zero-extension convention used for the finite lattice
(Weyl P2, `thm:3jspectral`, where the boundary rows are closed by `a_h(x_max+h) = a_h(x_min-h) = 0`).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

lemma not_isTri_imp {a b c : ℚ} (h : ¬ IsTri a b c) :
    ¬ IsNat (a + b - c) ∨ ¬ IsNat (a - b + c) ∨ ¬ IsNat (-a + b + c) := by
  unfold IsTri at h
  tauto

/-- **DLMF 34.3.15 at every row**: only the central symbol `(j₁ j₂ j₃; m₁ m₂ m₃)` is required to
be admissible; neighbours `j₁ ± 1` that are out of range are zero. -/
theorem threeJ_recurrence_all (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) (hm : m₁ + m₂ + m₃ = 0)
    (h : IsTri j₁ j₂ j₃) (h1 : IsNat (j₁ + m₁)) (h2 : IsNat (j₁ - m₁)) :
    (2 * (j₁ : ℝ) + 1) * ((((j₂ : ℝ) * (j₂ + 1) - j₃ * (j₃ + 1)) * m₁ -
        j₁ * (j₁ + 1) * ((m₃ : ℝ) - m₂))) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ =
      ((j₁ : ℝ) + 1) * E3 j₂ j₃ m₁ (j₁ : ℝ) * threeJ (j₁ - 1) j₂ j₃ m₁ m₂ m₃
        + (j₁ : ℝ) * E3 j₂ j₃ m₁ ((j₁ : ℝ) + 1) * threeJ (j₁ + 1) j₂ j₃ m₁ m₂ m₃ := by
  have hrec := racahSum3_recurrence j₁ j₂ j₃ m₁ m₂
  have em3 : (m₃ : ℝ) = -(m₁ : ℝ) - m₂ := by
    have : (m₃ : ℚ) = -m₁ - m₂ := by linarith
    rw [this]; push_cast; ring
  have ep : E3 j₂ j₃ m₁ ((j₁ : ℝ) + 1) *
        (Real.sqrt (triSq (j₁ + 1) j₂ j₃) * Real.sqrt (fq (j₁ + 1 + m₁) * fq (j₁ + 1 - m₁))) *
        racahSum3 (j₁ + 1) j₂ j₃ m₁ m₂ =
      (((j₁ : ℝ) + 1 + j₂ - j₃) * ((j₁ : ℝ) + 1 - j₂ + j₃) * ((j₁ : ℝ) + 1 + m₁) *
        ((j₁ : ℝ) + 1 - m₁)) *
        (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁))) *
        racahSum3 (j₁ + 1) j₂ j₃ m₁ m₂ := by
    by_cases hp : IsTri (j₁ + 1) j₂ j₃
    · rw [EW3_plus h hp h1 h2]
    · have : racahSum3 (j₁ + 1) j₂ j₃ m₁ m₂ = 0 :=
        racahSum3_zero_of_not_isNat _ _ _ _ _ m₃ (by linarith)
          (by rcases not_isTri_imp hp with h | h | h <;> tauto)
      rw [this]; ring
  have emn : E3 j₂ j₃ m₁ (j₁ : ℝ) *
        (Real.sqrt (triSq (j₁ - 1) j₂ j₃) * Real.sqrt (fq (j₁ - 1 + m₁) * fq (j₁ - 1 - m₁))) *
        racahSum3 (j₁ - 1) j₂ j₃ m₁ m₂ =
      (((j₂ : ℝ) + j₃ + 1 - j₁) * ((j₁ : ℝ) + j₂ + j₃ + 1)) *
        (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁))) *
        racahSum3 (j₁ - 1) j₂ j₃ m₁ m₂ := by
    by_cases hmn : IsTri (j₁ - 1) j₂ j₃ ∧ IsNat (j₁ - 1 + m₁) ∧ IsNat (j₁ - 1 - m₁)
    · rw [EW3_minus h hmn.1 hmn.2.1 hmn.2.2]
    · have : racahSum3 (j₁ - 1) j₂ j₃ m₁ m₂ = 0 := by
        refine racahSum3_zero_of_not_isNat _ _ _ _ _ m₃ (by linarith) ?_
        by_contra hcon
        push Not at hcon
        exact hmn ⟨⟨hcon.1, hcon.2.1, hcon.2.2.1⟩, hcon.2.2.2.1, hcon.2.2.2.2.1⟩
      rw [this]; ring
  rw [threeJ_factor hm, threeJ_factor hm, threeJ_factor hm,
    show j₁ - 1 - j₂ - m₃ = (j₁ - j₂ - m₃) - 1 by ring,
    show j₁ + 1 - j₂ - m₃ = (j₁ - j₂ - m₃) + 1 by ring, sgn_sub_one, sgn_add_one]
  rw [em3]
  linear_combination
    (sgn (j₁ - j₂ - m₃) * Real.sqrt (fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) *
      (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁)))) * hrec
    + (((j₁ : ℝ) + 1) * sgn (j₁ - j₂ - m₃) *
      Real.sqrt (fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃))) * emn
    + ((j₁ : ℝ) * sgn (j₁ - j₂ - m₃) *
      Real.sqrt (fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃))) * ep

/-- **DLMF 34.3.14 at every row**: only the central symbol is required to be admissible in its
`m₂, m₃` projections (`j₂ ± m₂`, `j₃ ± m₃` natural); the neighbours `(m₂±1, m₃∓1)` that are out of
range are zero. -/
theorem threeJ_recurrence_m_all (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) (hm : m₁ + m₂ + m₃ = 0)
    (a1 : IsNat (j₂ + m₂)) (a4 : IsNat (j₃ - m₃)) (b1 : IsNat (j₂ - m₂))
    (b3 : IsNat (j₃ + m₃)) :
    (((j₁ : ℝ) * (j₁ + 1) - j₂ * (j₂ + 1) - j₃ * (j₃ + 1)) - 2 * (m₂ : ℝ) * m₃) *
        threeJ j₁ j₂ j₃ m₁ m₂ m₃ =
      Real.sqrt (((j₂ : ℝ) - m₂) * ((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1) * ((j₃ : ℝ) + m₃)) *
          threeJ j₁ j₂ j₃ m₁ (m₂ + 1) (m₃ - 1)
        + Real.sqrt (((j₂ : ℝ) - m₂ + 1) * ((j₂ : ℝ) + m₂) * ((j₃ : ℝ) - m₃) *
            ((j₃ : ℝ) + m₃ + 1)) * threeJ j₁ j₂ j₃ m₁ (m₂ - 1) (m₃ + 1) := by
  have hrec := racahSum3_m_recurrence j₁ j₂ j₃ m₁ m₂
  have em3 : (m₃ : ℝ) = -(m₁ : ℝ) - m₂ := by
    have : (m₃ : ℚ) = -m₁ - m₂ := by linarith
    rw [this]; push_cast; ring
  have hmp : m₁ + (m₂ + 1) + (m₃ - 1) = 0 := by linarith
  have hmm : m₁ + (m₂ - 1) + (m₃ + 1) = 0 := by linarith
  have ep : Real.sqrt (((j₂ : ℝ) - m₂) * ((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1) *
        ((j₃ : ℝ) + m₃)) * Rm j₂ j₃ (m₂ + 1) (m₃ - 1) * racahSum3 j₁ j₂ j₃ m₁ (m₂ + 1) =
      (((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1)) * Rm j₂ j₃ m₂ m₃ *
        racahSum3 j₁ j₂ j₃ m₁ (m₂ + 1) := by
    by_cases hp : IsNat (j₂ - (m₂ + 1)) ∧ IsNat (j₃ + (m₃ - 1))
    · rw [Rm_plus a1 hp.1 hp.2 a4]
    · have : racahSum3 j₁ j₂ j₃ m₁ (m₂ + 1) = 0 := by
        refine racahSum3_zero_of_not_isNat _ _ _ _ _ (m₃ - 1) hmp ?_
        by_contra hcon
        push Not at hcon
        exact hp ⟨hcon.2.2.2.2.2.2.1, hcon.2.2.2.2.2.2.2.1⟩
      rw [this]; ring
  have emn : Real.sqrt (((j₂ : ℝ) - m₂ + 1) * ((j₂ : ℝ) + m₂) * ((j₃ : ℝ) - m₃) *
        ((j₃ : ℝ) + m₃ + 1)) * Rm j₂ j₃ (m₂ - 1) (m₃ + 1) * racahSum3 j₁ j₂ j₃ m₁ (m₂ - 1) =
      (((j₂ : ℝ) - m₂ + 1) * ((j₃ : ℝ) + m₃ + 1)) * Rm j₂ j₃ m₂ m₃ *
        racahSum3 j₁ j₂ j₃ m₁ (m₂ - 1) := by
    by_cases hq : IsNat (j₂ + (m₂ - 1)) ∧ IsNat (j₃ - (m₃ + 1))
    · rw [Rm_minus b1 hq.1 b3 hq.2]
    · have : racahSum3 j₁ j₂ j₃ m₁ (m₂ - 1) = 0 := by
        refine racahSum3_zero_of_not_isNat _ _ _ _ _ (m₃ + 1) hmm ?_
        by_contra hcon
        push Not at hcon
        exact hq ⟨hcon.2.2.2.2.2.1, hcon.2.2.2.2.2.2.2.2⟩
      rw [this]; ring
  rw [threeJ_factor hm, threeJ_factor hmp, threeJ_factor hmm,
    show j₁ - j₂ - (m₃ - 1) = (j₁ - j₂ - m₃) + 1 by ring,
    show j₁ - j₂ - (m₃ + 1) = (j₁ - j₂ - m₃) - 1 by ring, sgn_add_one, sgn_sub_one]
  unfold Rm at ep emn
  have hrec' : (((j₁ : ℝ) * (j₁ + 1) - j₂ * (j₂ + 1) - j₃ * (j₃ + 1)) - 2 * (m₂ : ℝ) * m₃) *
        racahSum3 j₁ j₂ j₃ m₁ m₂ +
      ((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1) * racahSum3 j₁ j₂ j₃ m₁ (m₂ + 1) +
      ((j₂ : ℝ) - m₂ + 1) * ((j₃ : ℝ) + m₃ + 1) * racahSum3 j₁ j₂ j₃ m₁ (m₂ - 1) = 0 := by
    rw [em3]; linear_combination hrec
  linear_combination
    (sgn (j₁ - j₂ - m₃) * (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁))) *
      Real.sqrt (fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃))) * hrec'
    + (sgn (j₁ - j₂ - m₃) * (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁)))) * ep
    + (sgn (j₁ - j₂ - m₃) * (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁)))) * emn

/-- info: 'FormalResearch.Racah.threeJ_recurrence_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_recurrence_all

/-- info: 'FormalResearch.Racah.threeJ_recurrence_m_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_recurrence_m_all

end FormalResearch.Racah
