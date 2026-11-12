module

public import FormalResearch.Wigner.SixJRecurrence
public import FormalResearch.Wigner.Symmetry

/-!
# The `6j` recurrence at the ends of the admissible range

`sixJ_recurrence` (DLMF 34.5.11) needs the triangle conditions for the three symbols involved.
`sixJ_recurrence_ext` is the same identity with **no hypotheses**, for every rational first
argument: at the ends of the admissible range the neighbouring symbol vanishes and either the
coefficient `E` vanishes or the rational Racah sum itself vanishes (a triangle inequality is
violated, which kills a product of two inverse factorials).  This is what the summation by parts
in the orthogonality relation (DLMF 34.5.14) needs at the endpoints.
-/

@[expose] public section

namespace FormalResearch.Wigner

lemma isNat_sub_one_of_ne {x : ℚ} (h : IsNat x) (h0 : x ≠ 0) : IsNat (x - 1) := by
  obtain ⟨n, rfl⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
    have : n ≠ 0 := by rintro rfl; simp at h0
    omega⟩
  exact ⟨m, by push_cast; ring⟩

/-- If `(y,a,b)` is a triangle but `(y+1,a,b)` is not, then `y = a + b`. -/
lemma tri_next_fail {y a b : ℚ} (h : IsTri y a b) (h' : ¬ IsTri (y + 1) a b) : a + b = y := by
  obtain ⟨h1, h2, h3⟩ := h
  by_contra hne
  apply h'
  refine ⟨?_, ?_, ?_⟩
  · have := isNat_add_one h1; convert this using 1; ring
  · have := isNat_add_one h2; convert this using 1; ring
  · have h3' : -y + a + b ≠ 0 := fun h0 => hne (by linarith)
    have := isNat_sub_one_of_ne h3 h3'
    convert this using 1; ring

/-- If `(y,a,b)` is a triangle but `(y-1,a,b)` is not, then `y = b - a` or `y = a - b`. -/
lemma tri_prev_fail {y a b : ℚ} (h : IsTri y a b) (h' : ¬ IsTri (y - 1) a b) :
    y = b - a ∨ y = a - b := by
  obtain ⟨h1, h2, h3⟩ := h
  by_contra hne
  push Not at hne
  apply h'
  refine ⟨?_, ?_, ?_⟩
  · have := isNat_sub_one_of_ne h1 (fun h0 => hne.1 (by linarith))
    convert this using 1; ring
  · have := isNat_sub_one_of_ne h2 (fun h0 => hne.2 (by linarith))
    convert this using 1; ring
  · have := isNat_add_one h3; convert this using 1; ring

lemma P7_eq_zero_of_pair (x : Fin 7 → ℚ) (i j : Fin 7) (h : x i + x j < 0) : P7 x = 0 := by
  unfold P7
  by_cases hi : x i < 0
  · exact Finset.prod_eq_zero (Finset.mem_univ i) (ifa_eq_zero_of_neg hi)
  · exact Finset.prod_eq_zero (Finset.mem_univ j) (ifa_eq_zero_of_neg (by linarith))

lemma racahSum6_eq_zero_of_term {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ}
    (h : ∀ σ : ℚ, P7 ![σ - j₁ - j₂ - j₃, σ - j₁ - l₂ - l₃, σ - l₁ - j₂ - l₃, σ - l₁ - l₂ - j₃,
      j₁ + j₂ + l₁ + l₂ - σ, j₂ + j₃ + l₂ + l₃ - σ, j₃ + j₁ + l₃ + l₁ - σ] = 0) :
    racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  unfold racahSum6 term6
  simp [h]

/-- The Racah sum vanishes when the first entry exceeds the sum of the other two entries of a
triad containing it. -/
lemma racahSum6_eq_zero_top {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : j₂ + j₃ < j₁ ∨ l₂ + l₃ < j₁) :
    racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  apply racahSum6_eq_zero_of_term
  intro σ
  rcases h with h | h
  · exact P7_eq_zero_of_pair _ 1 5 (by simp; linarith)
  · exact P7_eq_zero_of_pair _ 0 5 (by simp; linarith)

/-- The Racah sum vanishes when the first entry violates a lower triangle inequality. -/
lemma racahSum6_eq_zero_bot {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ}
    (h : j₁ + j₂ < j₃ ∨ j₃ + j₁ < j₂ ∨ j₁ + l₂ < l₃ ∨ j₁ + l₃ < l₂) :
    racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  apply racahSum6_eq_zero_of_term
  intro σ
  rcases h with h | h | h | h
  · exact P7_eq_zero_of_pair _ 3 4 (by simp; linarith)
  · exact P7_eq_zero_of_pair _ 2 6 (by simp; linarith)
  · exact P7_eq_zero_of_pair _ 2 4 (by simp; linarith)
  · exact P7_eq_zero_of_pair _ 3 6 (by simp; linarith)

lemma E6_eq_zero {a b c d x : ℝ}
    (h : x ^ 2 = (a - b) ^ 2 ∨ (a + b + 1) ^ 2 = x ^ 2 ∨ x ^ 2 = (c - d) ^ 2 ∨
      (c + d + 1) ^ 2 = x ^ 2) : E6 a b c d x = 0 := by
  unfold E6
  rw [Real.sqrt_eq_zero_of_nonpos]
  rcases h with h | h | h | h
  · rw [h]; simp
  · rw [← h]; simp
  · rw [h]; simp
  · rw [← h]; simp

lemma sixJ_eq_zero_of_not_tri12 {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : ¬ (IsTri j₁ j₂ j₃ ∧ IsTri j₁ l₂ l₃)) :
    sixJ j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  rw [sixJ_factor]
  rcases not_and_or.mp h with h | h
  · rw [triSq_eq_zero_of_not_isTri h]; simp
  · rw [triSq_eq_zero_of_not_isTri h]; simp

/-- **DLMF 34.5.11 without triangle hypotheses**: the `6j` recurrence in the first entry holds for
every rational first entry (all symbols zero-extended). -/
theorem sixJ_recurrence_ext (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    (2 * (j₁ : ℝ) + 1) *
          ((((j₃ : ℝ) * (j₃ + 1) + j₂ * (j₂ + 1) - j₁ * (j₁ + 1)) *
              ((l₃ : ℝ) * (l₃ + 1) + l₂ * (l₂ + 1) - j₁ * (j₁ + 1))) -
            2 * ((j₃ : ℝ) * (j₃ + 1) * (l₃ * (l₃ + 1)) + j₂ * (j₂ + 1) * (l₂ * (l₂ + 1)) -
              j₁ * (j₁ + 1) * (l₁ * (l₁ + 1)))) * sixJ j₁ j₂ j₃ l₁ l₂ l₃ =
      (j₁ : ℝ) * E6 j₂ j₃ l₂ l₃ ((j₁ : ℝ) + 1) * sixJ (j₁ + 1) j₂ j₃ l₁ l₂ l₃
        + ((j₁ : ℝ) + 1) * E6 j₂ j₃ l₂ l₃ (j₁ : ℝ) * sixJ (j₁ - 1) j₂ j₃ l₁ l₂ l₃ := by
  by_cases hT : IsTri j₁ j₂ j₃ ∧ IsTri j₁ l₂ l₃
  · obtain ⟨h1, h2⟩ := hT
    by_cases hCc : IsTri l₁ j₂ l₃ ∧ IsTri l₁ l₂ j₃
    · have hw : (0 : ℚ) ≤ l₁ + j₂ + l₃ := by
        have := hCc.1.sum_nonneg
        exact_mod_cast this
      have hrec := racahSum6_recurrence j₁ j₂ j₃ l₁ l₂ l₃ hw
      -- the upper neighbour
      have e1 : (((j₁ : ℝ) + 1 + j₂ - j₃) * ((j₁ : ℝ) + 1 - j₂ + j₃) * ((j₁ : ℝ) + 1 + l₂ - l₃) *
            ((j₁ : ℝ) + 1 - l₂ + l₃)) *
          (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (triSq j₁ l₂ l₃)) *
            racahSum6 (j₁ + 1) j₂ j₃ l₁ l₂ l₃ =
          E6 j₂ j₃ l₂ l₃ ((j₁ : ℝ) + 1) *
            (Real.sqrt (triSq (j₁ + 1) j₂ j₃) * Real.sqrt (triSq (j₁ + 1) l₂ l₃)) *
            racahSum6 (j₁ + 1) j₂ j₃ l₁ l₂ l₃ := by
        by_cases hp : IsTri (j₁ + 1) j₂ j₃ ∧ IsTri (j₁ + 1) l₂ l₃
        · rw [EW_plus h1 h2 hp.1 hp.2]
        · have : racahSum6 (j₁ + 1) j₂ j₃ l₁ l₂ l₃ = 0 := by
            apply racahSum6_eq_zero_top
            rcases not_and_or.mp hp with hp | hp
            · left; have := tri_next_fail h1 hp; linarith
            · right; have := tri_next_fail h2 hp; linarith
          rw [this]; simp
      have e2 : (((j₂ : ℝ) + j₃ + 1 - j₁) * ((j₂ : ℝ) + j₃ + 1 + j₁) * ((l₂ : ℝ) + l₃ + 1 - j₁) *
            ((l₂ : ℝ) + l₃ + 1 + j₁)) *
          (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (triSq j₁ l₂ l₃)) *
            racahSum6 (j₁ - 1) j₂ j₃ l₁ l₂ l₃ =
          E6 j₂ j₃ l₂ l₃ (j₁ : ℝ) *
            (Real.sqrt (triSq (j₁ - 1) j₂ j₃) * Real.sqrt (triSq (j₁ - 1) l₂ l₃)) *
            racahSum6 (j₁ - 1) j₂ j₃ l₁ l₂ l₃ := by
        by_cases hm : IsTri (j₁ - 1) j₂ j₃ ∧ IsTri (j₁ - 1) l₂ l₃
        · rw [EW_minus h1 h2 hm.1 hm.2]
        · have : racahSum6 (j₁ - 1) j₂ j₃ l₁ l₂ l₃ = 0 := by
            apply racahSum6_eq_zero_bot
            rcases not_and_or.mp hm with hm | hm
            · rcases tri_prev_fail h1 hm with h | h
              · left; linarith
              · right; left; linarith
            · rcases tri_prev_fail h2 hm with h | h
              · right; right; left; linarith
              · right; right; right; linarith
          rw [this]; simp
      rw [sixJ_factor j₁ j₂ j₃ l₁ l₂ l₃, sixJ_factor (j₁ + 1) j₂ j₃ l₁ l₂ l₃,
        sixJ_factor (j₁ - 1) j₂ j₃ l₁ l₂ l₃]
      linear_combination
        ((Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (triSq j₁ l₂ l₃)) *
          (Real.sqrt (triSq l₁ j₂ l₃) * Real.sqrt (triSq l₁ l₂ j₃))) * hrec
        + (j₁ : ℝ) * (Real.sqrt (triSq l₁ j₂ l₃) * Real.sqrt (triSq l₁ l₂ j₃)) * e1
        + ((j₁ : ℝ) + 1) * (Real.sqrt (triSq l₁ j₂ l₃) * Real.sqrt (triSq l₁ l₂ j₃)) * e2
    · have hz : ∀ F : ℚ, sixJ F j₂ j₃ l₁ l₂ l₃ = 0 := by
        intro F
        rw [sixJ_factor]
        rcases not_and_or.mp hCc with h | h
        · rw [triSq_eq_zero_of_not_isTri h]; simp
        · rw [triSq_eq_zero_of_not_isTri h]; simp
      simp [hz]
  · rw [sixJ_eq_zero_of_not_tri12 hT, mul_zero]
    have hq : ¬ (IsTri j₁ j₂ j₃ ∧ IsTri j₁ l₂ l₃) := hT
    -- the upper term
    have t1 : (j₁ : ℝ) * E6 j₂ j₃ l₂ l₃ ((j₁ : ℝ) + 1) * sixJ (j₁ + 1) j₂ j₃ l₁ l₂ l₃ = 0 := by
      by_cases hp : IsTri (j₁ + 1) j₂ j₃ ∧ IsTri (j₁ + 1) l₂ l₃
      · have : E6 j₂ j₃ l₂ l₃ ((j₁ : ℝ) + 1) = 0 := by
          apply E6_eq_zero
          rcases not_and_or.mp hq with h | h
          · have := tri_prev_fail (y := j₁ + 1) hp.1 (by rw [add_sub_cancel_right]; exact h)
            left
            rcases this with h | h
            · have : (j₁ : ℝ) + 1 = j₃ - j₂ := by exact_mod_cast h
              rw [this]; ring
            · have : (j₁ : ℝ) + 1 = j₂ - j₃ := by exact_mod_cast h
              rw [this]
          · have := tri_prev_fail (y := j₁ + 1) hp.2 (by rw [add_sub_cancel_right]; exact h)
            right; right; left
            rcases this with h | h
            · have : (j₁ : ℝ) + 1 = l₃ - l₂ := by exact_mod_cast h
              rw [this]; ring
            · have : (j₁ : ℝ) + 1 = l₂ - l₃ := by exact_mod_cast h
              rw [this]
        rw [this]; ring
      · rw [sixJ_eq_zero_of_not_tri12 hp]; ring
    have t2 : ((j₁ : ℝ) + 1) * E6 j₂ j₃ l₂ l₃ (j₁ : ℝ) * sixJ (j₁ - 1) j₂ j₃ l₁ l₂ l₃ = 0 := by
      by_cases hm : IsTri (j₁ - 1) j₂ j₃ ∧ IsTri (j₁ - 1) l₂ l₃
      · have : E6 j₂ j₃ l₂ l₃ (j₁ : ℝ) = 0 := by
          apply E6_eq_zero
          rcases not_and_or.mp hq with h | h
          · have := tri_next_fail (y := j₁ - 1) hm.1 (by rw [sub_add_cancel]; exact h)
            right; left
            have : (j₂ : ℝ) + j₃ = j₁ - 1 := by exact_mod_cast this
            rw [this]; ring
          · have := tri_next_fail (y := j₁ - 1) hm.2 (by rw [sub_add_cancel]; exact h)
            right; right; right
            have : (l₂ : ℝ) + l₃ = j₁ - 1 := by exact_mod_cast this
            rw [this]; ring
        rw [this]; ring
      · rw [sixJ_eq_zero_of_not_tri12 hm]; ring
    rw [t1, t2]; ring

/-- info: 'FormalResearch.Wigner.sixJ_recurrence_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_recurrence_ext

end FormalResearch.Wigner
