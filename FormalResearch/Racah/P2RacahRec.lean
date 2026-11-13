module

public import FormalResearch.Wigner.SixJRecurrence
public import FormalResearch.Wigner.Symmetry

/-!
# `6j` recurrence valid on the whole admissible range (DLMF 34.5.11 with boundary rows)

`Wigner.sixJ_recurrence` assumes the triangle conditions for the three symbols with first entry
`j₁ - 1`, `j₁`, `j₁ + 1`.  The Weyl/P2 recurrence (`lem:6jrec`) is used on the whole finite range
`f₀ ≤ f ≤ f₁`, including the two boundary rows, where one neighbour is not admissible.  Here we
show that the recurrence holds for **all** rational spins as soon as the two triads containing
`j₁` itself are admissible: when a neighbouring triad fails, the corresponding Racah sum is
empty (one of the twelve differences `b_j - a_i` of the triad sums and quad sums is negative), so
that neighbour is `0`, and the identity is the truncated recurrence.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

lemma ifa_pair_zero (x y : ℚ) (h : x + y < 0) : ifa x = 0 ∨ ifa y = 0 := by
  by_contra hc
  push Not at hc
  rcases lt_or_ge x 0 with hx | hx
  · exact hc.1 (ifa_eq_zero_of_neg hx)
  · exact hc.2 (ifa_eq_zero_of_neg (by linarith))

private lemma racahSum6_zero_of {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ}
    (h : ∀ σ : ℚ, ifa (σ - j₁ - j₂ - j₃) * ifa (σ - j₁ - l₂ - l₃) * ifa (σ - l₁ - j₂ - l₃) *
      ifa (σ - l₁ - l₂ - j₃) * ifa (j₁ + j₂ + l₁ + l₂ - σ) * ifa (j₂ + j₃ + l₂ + l₃ - σ) *
        ifa (j₃ + j₁ + l₃ + l₁ - σ) = 0) :
    racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  unfold racahSum6
  refine finsum_eq_zero_of_forall_eq_zero fun t => ?_
  unfold term6
  rw [P7_vec, h]
  ring

/-- Triad `(j₁ j₂ j₃)` violated: `j₁ + j₂ - j₃ < 0`. -/
lemma racahSum6_zero_d1 {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : j₁ + j₂ - j₃ < 0) :
    racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  refine racahSum6_zero_of fun σ => ?_
  rcases ifa_pair_zero (σ - l₁ - l₂ - j₃) (j₁ + j₂ + l₁ + l₂ - σ) (by linarith) with h' | h' <;>
    simp [h']

/-- Triad `(j₁ j₂ j₃)` violated: `j₁ - j₂ + j₃ < 0`. -/
lemma racahSum6_zero_d2 {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : j₁ - j₂ + j₃ < 0) :
    racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  refine racahSum6_zero_of fun σ => ?_
  rcases ifa_pair_zero (σ - l₁ - j₂ - l₃) (j₃ + j₁ + l₃ + l₁ - σ) (by linarith) with h' | h' <;>
    simp [h']

/-- Triad `(j₁ j₂ j₃)` violated: `-j₁ + j₂ + j₃ < 0`. -/
lemma racahSum6_zero_d3 {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : -j₁ + j₂ + j₃ < 0) :
    racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  refine racahSum6_zero_of fun σ => ?_
  rcases ifa_pair_zero (σ - j₁ - l₂ - l₃) (j₂ + j₃ + l₂ + l₃ - σ) (by linarith) with h' | h' <;>
    simp [h']

/-- Triad `(j₁ l₂ l₃)` violated: `j₁ + l₂ - l₃ < 0`. -/
lemma racahSum6_zero_e1 {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : j₁ + l₂ - l₃ < 0) :
    racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  refine racahSum6_zero_of fun σ => ?_
  rcases ifa_pair_zero (σ - l₁ - j₂ - l₃) (j₁ + j₂ + l₁ + l₂ - σ) (by linarith) with h' | h' <;>
    simp [h']

/-- Triad `(j₁ l₂ l₃)` violated: `j₁ - l₂ + l₃ < 0`. -/
lemma racahSum6_zero_e2 {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : j₁ - l₂ + l₃ < 0) :
    racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  refine racahSum6_zero_of fun σ => ?_
  rcases ifa_pair_zero (σ - l₁ - l₂ - j₃) (j₃ + j₁ + l₃ + l₁ - σ) (by linarith) with h' | h' <;>
    simp [h']

/-- Triad `(j₁ l₂ l₃)` violated: `-j₁ + l₂ + l₃ < 0`. -/
lemma racahSum6_zero_e3 {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : -j₁ + l₂ + l₃ < 0) :
    racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  refine racahSum6_zero_of fun σ => ?_
  rcases ifa_pair_zero (σ - j₁ - j₂ - j₃) (j₂ + j₃ + l₂ + l₃ - σ) (by linarith) with h' | h' <;>
    simp [h']

lemma isNat_pred_of_nonneg {x : ℚ} (hx : IsNat x) (h : 0 ≤ x - 1) : IsNat (x - 1) := by
  obtain ⟨n, rfl⟩ := hx
  have hn : 1 ≤ n := by
    have : (1 : ℚ) ≤ n := by linarith
    exact_mod_cast this
  exact ⟨n - 1, by push_cast [Nat.cast_sub hn]; ring⟩

/-- If `f` is admissible and `f+1` is not, the Racah sum with first entry `f+1` is empty. -/
lemma racahSum6_succ_zero {f j₂ j₃ l₁ l₂ l₃ : ℚ} (h1 : IsTri f j₂ j₃) (h2 : IsTri f l₂ l₃)
    (hn : ¬ (IsTri (f + 1) j₂ j₃ ∧ IsTri (f + 1) l₂ l₃)) :
    racahSum6 (f + 1) j₂ j₃ l₁ l₂ l₃ = 0 := by
  rcases not_and_or.mp hn with h | h
  · apply racahSum6_zero_d3
    by_contra hc
    apply h
    refine ⟨?_, ?_, ?_⟩
    · have := isNat_add_one h1.1
      rwa [show f + j₂ - j₃ + 1 = f + 1 + j₂ - j₃ by ring] at this
    · have := isNat_add_one h1.2.1
      rwa [show f - j₂ + j₃ + 1 = f + 1 - j₂ + j₃ by ring] at this
    · have := isNat_pred_of_nonneg h1.2.2 (by linarith)
      rwa [show -f + j₂ + j₃ - 1 = -(f + 1) + j₂ + j₃ by ring] at this
  · apply racahSum6_zero_e3
    by_contra hc
    apply h
    refine ⟨?_, ?_, ?_⟩
    · have := isNat_add_one h2.1
      rwa [show f + l₂ - l₃ + 1 = f + 1 + l₂ - l₃ by ring] at this
    · have := isNat_add_one h2.2.1
      rwa [show f - l₂ + l₃ + 1 = f + 1 - l₂ + l₃ by ring] at this
    · have := isNat_pred_of_nonneg h2.2.2 (by linarith)
      rwa [show -f + l₂ + l₃ - 1 = -(f + 1) + l₂ + l₃ by ring] at this

/-- If `f` is admissible and `f-1` is not, the Racah sum with first entry `f-1` is empty. -/
lemma racahSum6_pred_zero {f j₂ j₃ l₁ l₂ l₃ : ℚ} (h1 : IsTri f j₂ j₃) (h2 : IsTri f l₂ l₃)
    (hn : ¬ (IsTri (f - 1) j₂ j₃ ∧ IsTri (f - 1) l₂ l₃)) :
    racahSum6 (f - 1) j₂ j₃ l₁ l₂ l₃ = 0 := by
  have key : ∀ {b c : ℚ}, IsTri f b c → ¬ IsTri (f - 1) b c →
      (f - 1 + b - c < 0 ∨ f - 1 - b + c < 0) := by
    intro b c h hn
    by_contra hc
    push Not at hc
    apply hn
    refine ⟨?_, ?_, ?_⟩
    · have := isNat_pred_of_nonneg h.1 (by linarith)
      rwa [show f + b - c - 1 = f - 1 + b - c by ring] at this
    · have := isNat_pred_of_nonneg h.2.1 (by linarith)
      rwa [show f - b + c - 1 = f - 1 - b + c by ring] at this
    · have := isNat_add_one h.2.2
      rwa [show -f + b + c + 1 = -(f - 1) + b + c by ring] at this
  rcases not_and_or.mp hn with h | h
  · rcases key h1 h with hc | hc
    · exact racahSum6_zero_d1 (by linarith)
    · exact racahSum6_zero_d2 (by linarith)
  · rcases key h2 h with hc | hc
    · exact racahSum6_zero_e1 (by linarith)
    · exact racahSum6_zero_e2 (by linarith)

/-- **DLMF 34.5.11 on the whole admissible range.**  As `Wigner.sixJ_recurrence`, but only the two
triads that contain `j₁` itself are assumed admissible: if `j₁ ± 1` is not admissible, the
corresponding symbol is `0`, and the identity is the truncated (boundary-row) recurrence. -/
theorem sixJ_recurrence_of_tri (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ)
    (h1 : IsTri j₁ j₂ j₃) (h2 : IsTri j₁ l₂ l₃) :
    (2 * (j₁ : ℝ) + 1) *
          ((((j₃ : ℝ) * (j₃ + 1) + j₂ * (j₂ + 1) - j₁ * (j₁ + 1)) *
              ((l₃ : ℝ) * (l₃ + 1) + l₂ * (l₂ + 1) - j₁ * (j₁ + 1))) -
            2 * ((j₃ : ℝ) * (j₃ + 1) * (l₃ * (l₃ + 1)) + j₂ * (j₂ + 1) * (l₂ * (l₂ + 1)) -
              j₁ * (j₁ + 1) * (l₁ * (l₁ + 1)))) * sixJ j₁ j₂ j₃ l₁ l₂ l₃ =
      (j₁ : ℝ) * E6 j₂ j₃ l₂ l₃ ((j₁ : ℝ) + 1) * sixJ (j₁ + 1) j₂ j₃ l₁ l₂ l₃
        + ((j₁ : ℝ) + 1) * E6 j₂ j₃ l₂ l₃ (j₁ : ℝ) * sixJ (j₁ - 1) j₂ j₃ l₁ l₂ l₃ := by
  by_cases hCc : IsTri l₁ j₂ l₃ ∧ IsTri l₁ l₂ j₃
  · have hw : (0 : ℚ) ≤ l₁ + j₂ + l₃ := by
      have := hCc.1.sum_nonneg
      exact_mod_cast this
    have hrec := racahSum6_recurrence j₁ j₂ j₃ l₁ l₂ l₃ hw
    set Dc := Real.sqrt (triSq l₁ j₂ l₃) * Real.sqrt (triSq l₁ l₂ j₃) with hDc
    set D0 := Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (triSq j₁ l₂ l₃) with hD0
    have Fp : (j₁ : ℝ) * E6 j₂ j₃ l₂ l₃ ((j₁ : ℝ) + 1) * sixJ (j₁ + 1) j₂ j₃ l₁ l₂ l₃ =
        (j₁ : ℝ) * (((j₁ : ℝ) + 1 + j₂ - j₃) * ((j₁ : ℝ) + 1 - j₂ + j₃) *
          ((j₁ : ℝ) + 1 + l₂ - l₃) * ((j₁ : ℝ) + 1 - l₂ + l₃)) *
          (D0 * Dc * racahSum6 (j₁ + 1) j₂ j₃ l₁ l₂ l₃) := by
      by_cases hp : IsTri (j₁ + 1) j₂ j₃ ∧ IsTri (j₁ + 1) l₂ l₃
      · have e1 := EW_plus h1 h2 hp.1 hp.2
        rw [sixJ_factor]
        linear_combination ((j₁ : ℝ) * Dc * racahSum6 (j₁ + 1) j₂ j₃ l₁ l₂ l₃) * e1
      · have hz := racahSum6_succ_zero (l₁ := l₁) h1 h2 hp
        rw [sixJ_factor, hz]; ring
    have Fm : ((j₁ : ℝ) + 1) * E6 j₂ j₃ l₂ l₃ (j₁ : ℝ) * sixJ (j₁ - 1) j₂ j₃ l₁ l₂ l₃ =
        ((j₁ : ℝ) + 1) * (((j₂ : ℝ) + j₃ + 1 - j₁) * ((j₂ : ℝ) + j₃ + 1 + j₁) *
          ((l₂ : ℝ) + l₃ + 1 - j₁) * ((l₂ : ℝ) + l₃ + 1 + j₁)) *
          (D0 * Dc * racahSum6 (j₁ - 1) j₂ j₃ l₁ l₂ l₃) := by
      by_cases hm : IsTri (j₁ - 1) j₂ j₃ ∧ IsTri (j₁ - 1) l₂ l₃
      · have e2 := EW_minus h1 h2 hm.1 hm.2
        rw [sixJ_factor]
        linear_combination (((j₁ : ℝ) + 1) * Dc * racahSum6 (j₁ - 1) j₂ j₃ l₁ l₂ l₃) * e2
      · have hz := racahSum6_pred_zero (l₁ := l₁) h1 h2 hm
        rw [sixJ_factor, hz]; ring
    rw [sixJ_factor j₁ j₂ j₃ l₁ l₂ l₃]
    linear_combination (D0 * Dc) * hrec - Fp - Fm
  · have hz : ∀ F : ℚ, sixJ F j₂ j₃ l₁ l₂ l₃ = 0 := by
      intro F
      rw [sixJ_factor]
      rcases not_and_or.mp hCc with h | h
      · rw [triSq_eq_zero_of_not_isTri h]; simp
      · rw [triSq_eq_zero_of_not_isTri h]; simp
    simp [hz]

/-- info: 'FormalResearch.Racah.SixJ.sixJ_recurrence_of_tri' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_recurrence_of_tri

end FormalResearch.Racah.SixJ
