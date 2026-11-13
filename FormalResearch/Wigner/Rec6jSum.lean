module

public import FormalResearch.Wigner.Rec6j

/-!
# The summed `6j` recurrence

From the pointwise telescoping identity `rec6_pointwise` to the recurrence of the finite sum
`racahSum6` (rational form of DLMF 34.5.11).
-/

@[expose] public section

namespace FormalResearch.Wigner

lemma term6_eq_zero {j₁ j₂ j₃ l₁ l₂ l₃ σ : ℚ} (ε φ : ℝ) (h : j₂ + j₃ + l₂ + l₃ - σ < 0) :
    term6 j₁ j₂ j₃ l₁ l₂ l₃ σ ε φ = 0 := by
  unfold term6 P7
  rw [Fin.prod_univ_seven]
  simp [ifa_eq_zero_of_neg h]

lemma H6_eq_zero {j₁ j₂ j₃ l₁ l₂ l₃ σ : ℚ} (ε φ : ℝ) (h : j₂ + j₃ + l₂ + l₃ - σ < 0) :
    H6 j₁ j₂ j₃ l₁ l₂ l₃ σ ε φ = 0 := by
  unfold H6 P7
  rw [Fin.prod_univ_seven]
  simp [ifa_eq_zero_of_neg h]

lemma H6_zero {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (ε φ : ℝ) (hw : 0 ≤ l₁ + j₂ + l₃) :
    H6 j₁ j₂ j₃ l₁ l₂ l₃ 0 ε φ = 0 := by
  rcases hw.lt_or_eq with h | h
  · unfold H6 P7
    rw [Fin.prod_univ_seven]
    have : ifa (-l₁ - j₂ - l₃) = 0 := ifa_eq_zero_of_neg (by linarith)
    simp [this]
  · unfold H6
    have h' : ((l₁ : ℝ) + j₂ + l₃) = 0 := by exact_mod_cast h.symm
    have : ((0 : ℚ) : ℝ) - l₁ - j₂ - l₃ = 0 := by push_cast; linarith
    rw [this]; simp

lemma racahSum6_eq_sum (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) (N : ℕ) (hN : j₂ + j₃ + l₂ + l₃ < N) :
    racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ =
      ∑ t ∈ Finset.range N,
        term6 j₁ j₂ j₃ l₁ l₂ l₃ t ((-1 : ℝ) ^ t) (((t + 1).factorial : ℕ) : ℝ) := by
  unfold racahSum6
  apply finsum_eq_sum_of_support_subset
  intro s hs
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hs
  exact term6_eq_zero _ _ (by have : (N : ℚ) ≤ s := by exact_mod_cast not_lt.mp hlt
                              linarith)

/-- **Three-term recurrence of the `6j` Racah sum in `j₁`** (the rational form of DLMF 34.5.11),
valid for all rational spins with `0 ≤ l₁ + j₂ + l₃`. -/
theorem racahSum6_recurrence (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) (hw : 0 ≤ l₁ + j₂ + l₃) :
    (2 * (j₁ : ℝ) + 1) *
          ((((j₃ : ℝ) * (j₃ + 1) + j₂ * (j₂ + 1) - j₁ * (j₁ + 1)) *
              ((l₃ : ℝ) * (l₃ + 1) + l₂ * (l₂ + 1) - j₁ * (j₁ + 1))) -
            2 * ((j₃ : ℝ) * (j₃ + 1) * (l₃ * (l₃ + 1)) + j₂ * (j₂ + 1) * (l₂ * (l₂ + 1)) -
              j₁ * (j₁ + 1) * (l₁ * (l₁ + 1)))) * racahSum6 j₁ j₂ j₃ l₁ l₂ l₃
      - (j₁ : ℝ) * (((j₁ : ℝ) + 1 + j₂ - j₃) * (j₁ + 1 - j₂ + j₃) * (j₁ + 1 + l₂ - l₃) *
          (j₁ + 1 - l₂ + l₃)) * racahSum6 (j₁ + 1) j₂ j₃ l₁ l₂ l₃
      - ((j₁ : ℝ) + 1) * (((j₂ : ℝ) + j₃ + 1 - j₁) * (j₂ + j₃ + 1 + j₁) * (l₂ + l₃ + 1 - j₁) *
          (l₂ + l₃ + 1 + j₁)) * racahSum6 (j₁ - 1) j₂ j₃ l₁ l₂ l₃ = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, j₂ + j₃ + l₂ + l₃ < N :=
    ⟨⌈j₂ + j₃ + l₂ + l₃⌉₊ + 1, by
      have := Nat.le_ceil (j₂ + j₃ + l₂ + l₃)
      push_cast; linarith⟩
  rw [racahSum6_eq_sum j₁ j₂ j₃ l₁ l₂ l₃ N hN, racahSum6_eq_sum (j₁ + 1) j₂ j₃ l₁ l₂ l₃ N hN,
    racahSum6_eq_sum (j₁ - 1) j₂ j₃ l₁ l₂ l₃ N hN, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  set Hn : ℕ → ℝ := fun t =>
    H6 j₁ j₂ j₃ l₁ l₂ l₃ t ((-1 : ℝ) ^ t) (((t + 1).factorial : ℕ) : ℝ) with hHn
  calc _ = ∑ t ∈ Finset.range N, (Hn (t + 1) - Hn t) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        have := rec6_pointwise j₁ j₂ j₃ l₁ l₂ l₃ (t : ℚ) ((-1 : ℝ) ^ t)
          (((t + 1).factorial : ℕ) : ℝ)
        simp only [hHn]
        rw [pow_succ, show ((t + 1 : ℕ) : ℚ) = (t : ℚ) + 1 by push_cast; ring,
          show (-1 : ℝ) ^ t * -1 = -((-1 : ℝ) ^ t) by ring,
          show (((t + 1 + 1).factorial : ℕ) : ℝ) = (((t : ℚ) : ℝ) + 2) * (((t + 1).factorial : ℕ) : ℝ)
            by rw [Nat.factorial_succ (t + 1)]; push_cast; ring]
        exact this
    _ = 0 := by
        apply sum_range_telescope
        · simp only [hHn]
          have := H6_zero (j₁ := j₁) (j₂ := j₂) (j₃ := j₃) (l₁ := l₁) (l₂ := l₂) (l₃ := l₃)
            ((-1 : ℝ) ^ 0) (((0 + 1).factorial : ℕ) : ℝ) hw
          simpa using this
        · simp only [hHn]
          exact H6_eq_zero _ _ (by have : (N : ℚ) ≤ N := le_rfl
                                   linarith)

/-- info: 'FormalResearch.Wigner.racahSum6_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racahSum6_recurrence

end FormalResearch.Wigner
