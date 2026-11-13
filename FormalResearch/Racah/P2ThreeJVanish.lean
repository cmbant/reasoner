module

public import FormalResearch.Wigner.ThreeJSym

/-!
# Vanishing of Racah's `3j` sum outside the admissible range

`racahSum3 j₁ j₂ j₃ m₁ m₂` (with `m₃ = -m₁-m₂`) vanishes as soon as one of the nine quantities
`j₁+j₂-j₃`, `j₁-j₂+j₃`, `-j₁+j₂+j₃`, `jᵢ ± mᵢ` is not a natural number.  Three of them
(`j₁+j₂-j₃`, `j₁-m₁`, `j₂+m₂`) kill every term of the sum; the others follow from the three
symmetries of the sum (`racahSum3_neg`, `racahSum3_swap12`, `racahSum3_swap23`).  This is what
turns the interior recurrences (`threeJ_recurrence`, `threeJ_recurrence_m`) into statements valid
at the boundary rows, where a neighbouring symbol is out of range (Weyl P2, `thm:3jspectral`).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

lemma term3_zero_of_not_isNat_arg4 {j₁ j₂ j₃ m₁ m₂ : ℚ} (hM : ¬ IsNat (j₂ + m₂)) (s : ℕ)
    (ε : ℝ) : term3 j₁ j₂ j₃ m₁ m₂ s ε = 0 := by
  rw [term3_eq]
  by_cases h : ifa (j₂ + m₂ - s) = 0
  · rw [h]; ring
  · exfalso
    obtain ⟨n, hn⟩ := ifa_ne_zero_isNat h
    exact hM ⟨n + s, by push_cast; linarith⟩

lemma racahSum3_zero_q1 {j₁ j₂ j₃ m₁ m₂ : ℚ} (h : ¬ IsNat (j₁ + j₂ - j₃)) :
    racahSum3 j₁ j₂ j₃ m₁ m₂ = 0 :=
  racahSum3_eq_zero_of_term _ _ _ _ _ (fun s => term3_zero_of_not_isNat_arg2 h s _)

lemma racahSum3_zero_j1m {j₁ j₂ j₃ m₁ m₂ : ℚ} (h : ¬ IsNat (j₁ - m₁)) :
    racahSum3 j₁ j₂ j₃ m₁ m₂ = 0 :=
  racahSum3_eq_zero_of_term _ _ _ _ _ (fun s => term3_zero_of_not_isNat_arg3 h s _)

lemma racahSum3_zero_j2p {j₁ j₂ j₃ m₁ m₂ : ℚ} (h : ¬ IsNat (j₂ + m₂)) :
    racahSum3 j₁ j₂ j₃ m₁ m₂ = 0 :=
  racahSum3_eq_zero_of_term _ _ _ _ _ (fun s => term3_zero_of_not_isNat_arg4 h s _)

/-- Via `m ↦ -m`: `R(m) = sgn(j₁+j₂-j₃) R(-m)`. -/
lemma racahSum3_eq_neg (j₁ j₂ j₃ m₁ m₂ : ℚ) :
    racahSum3 j₁ j₂ j₃ m₁ m₂ = sgn (j₁ + j₂ - j₃) * racahSum3 j₁ j₂ j₃ (-m₁) (-m₂) := by
  have := racahSum3_neg j₁ j₂ j₃ (-m₁) (-m₂)
  rw [neg_neg, neg_neg] at this
  exact this

lemma racahSum3_zero_j1p {j₁ j₂ j₃ m₁ m₂ : ℚ} (h : ¬ IsNat (j₁ + m₁)) :
    racahSum3 j₁ j₂ j₃ m₁ m₂ = 0 := by
  rw [racahSum3_eq_neg, racahSum3_zero_j1m (m₁ := -m₁) (by rwa [sub_neg_eq_add]), mul_zero]

lemma racahSum3_zero_j2m {j₁ j₂ j₃ m₁ m₂ : ℚ} (h : ¬ IsNat (j₂ - m₂)) :
    racahSum3 j₁ j₂ j₃ m₁ m₂ = 0 := by
  rw [racahSum3_eq_neg, racahSum3_zero_j2p (m₂ := -m₂) (by rwa [← sub_eq_add_neg]), mul_zero]

/-- Via the swap of columns 2, 3: `R(j₂,j₃) = sgn(j₁-m₁) R(j₃,j₂)`. -/
lemma racahSum3_eq_swap23 (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) (hm : m₁ + m₂ + m₃ = 0) :
    racahSum3 j₁ j₂ j₃ m₁ m₂ = sgn (j₁ - m₁) * racahSum3 j₁ j₃ j₂ m₁ m₃ := by
  have := racahSum3_swap23 j₁ j₃ j₂ m₁ m₃ m₂ (by linarith)
  exact this

lemma racahSum3_zero_q2 {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (hm : m₁ + m₂ + m₃ = 0)
    (h : ¬ IsNat (j₁ - j₂ + j₃)) : racahSum3 j₁ j₂ j₃ m₁ m₂ = 0 := by
  rw [racahSum3_eq_swap23 j₁ j₂ j₃ m₁ m₂ m₃ hm,
    racahSum3_zero_q1 (j₂ := j₃) (j₃ := j₂) (by rwa [show j₁ + j₃ - j₂ = j₁ - j₂ + j₃ by ring]),
    mul_zero]

lemma racahSum3_zero_j3p {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (hm : m₁ + m₂ + m₃ = 0)
    (h : ¬ IsNat (j₃ + m₃)) : racahSum3 j₁ j₂ j₃ m₁ m₂ = 0 := by
  rw [racahSum3_eq_swap23 j₁ j₂ j₃ m₁ m₂ m₃ hm, racahSum3_zero_j2p (j₂ := j₃) h, mul_zero]

lemma racahSum3_zero_j3m {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (hm : m₁ + m₂ + m₃ = 0)
    (h : ¬ IsNat (j₃ - m₃)) : racahSum3 j₁ j₂ j₃ m₁ m₂ = 0 := by
  rw [racahSum3_eq_swap23 j₁ j₂ j₃ m₁ m₂ m₃ hm, racahSum3_zero_j2m (j₂ := j₃) h, mul_zero]

lemma racahSum3_zero_q3 {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (hm : m₁ + m₂ + m₃ = 0)
    (h : ¬ IsNat (-j₁ + j₂ + j₃)) : racahSum3 j₁ j₂ j₃ m₁ m₂ = 0 := by
  have h0 : racahSum3 j₂ j₁ j₃ m₂ m₁ = 0 :=
    racahSum3_zero_q2 (m₃ := m₃) (by linarith) (by rwa [show j₂ - j₁ + j₃ = -j₁ + j₂ + j₃ by ring])
  have := racahSum3_swap12 j₂ j₁ j₃ m₂ m₁
  rw [h0, mul_zero] at this
  exact this

/-- **`R = 0` outside the admissible range**: if any of the nine quantities
`j₁+j₂-j₃`, `j₁-j₂+j₃`, `-j₁+j₂+j₃`, `jᵢ ± mᵢ` (`m₃ = -m₁-m₂`) is not a natural number,
Racah's sum is zero. -/
theorem racahSum3_zero_of_not_isNat (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) (hm : m₁ + m₂ + m₃ = 0)
    (h : ¬ IsNat (j₁ + j₂ - j₃) ∨ ¬ IsNat (j₁ - j₂ + j₃) ∨ ¬ IsNat (-j₁ + j₂ + j₃) ∨
      ¬ IsNat (j₁ + m₁) ∨ ¬ IsNat (j₁ - m₁) ∨ ¬ IsNat (j₂ + m₂) ∨ ¬ IsNat (j₂ - m₂) ∨
      ¬ IsNat (j₃ + m₃) ∨ ¬ IsNat (j₃ - m₃)) :
    racahSum3 j₁ j₂ j₃ m₁ m₂ = 0 := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact racahSum3_zero_q1 h
  · exact racahSum3_zero_q2 hm h
  · exact racahSum3_zero_q3 hm h
  · exact racahSum3_zero_j1p h
  · exact racahSum3_zero_j1m h
  · exact racahSum3_zero_j2p h
  · exact racahSum3_zero_j2m h
  · exact racahSum3_zero_j3p hm h
  · exact racahSum3_zero_j3m hm h

/-- info: 'FormalResearch.Racah.racahSum3_zero_of_not_isNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racahSum3_zero_of_not_isNat

end FormalResearch.Racah
