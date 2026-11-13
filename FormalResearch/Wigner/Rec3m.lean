module

public import FormalResearch.Wigner.Rec3j

/-!
# The `m`-recurrence for the Racah sum of the `3j` symbol

Rational form of DLMF 34.3.14: for all rational arguments,
`C S(m₂) + ρ₊ S(m₂+1) + ρ₋ S(m₂-1) = 0` with `m₃ = -m₁-m₂`.  The telescoping certificate is a
constant multiple of a single summand-like product (`H3m`).
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- The telescoping primitive of the `m`-recurrence of the `3j` Racah sum. -/
noncomputable def H3m (j₁ j₂ j₃ m₁ m₂ σ : ℚ) (ε : ℝ) : ℝ :=
  ε * ((j₁ : ℝ) - j₂ - j₃ - 1) *
    P6 ![σ - 1, j₁ + j₂ - j₃ - σ, j₁ - m₁ - σ, j₂ + m₂ - σ + 1, j₃ - j₂ + m₁ + σ - 1,
      j₃ - j₁ - m₂ + σ]

lemma rec3m_assemble (C rp rm ε c U A1 A2 A3 B1 B2 B3 : ℝ)
    (key : C * ((B3 + 1) * (A3 + 1)) + rp * (A3 * (A3 + 1)) + rm * (B3 * (B3 + 1)) =
      c * (-(B1 * B2 * (B3 + 1)) - A1 * A2 * (A3 + 1))) :
    C * (ε * ((B3 + 1) * (A3 + 1)) * U) + rp * (ε * (A3 * (A3 + 1)) * U) +
        rm * (ε * (B3 * (B3 + 1)) * U) =
      (-ε) * c * (B1 * B2 * (B3 + 1)) * U - ε * c * (A1 * A2 * (A3 + 1)) * U := by
  linear_combination (ε * U) * key

set_option maxRecDepth 10000 in
/-- The pointwise telescoping identity behind the `m`-recurrence of the `3j` Racah sum. -/
lemma rec3m_pointwise (j₁ j₂ j₃ m₁ m₂ σ : ℚ) (ε : ℝ) :
    (((j₁ : ℝ) * (j₁ + 1) - j₂ * (j₂ + 1) - j₃ * (j₃ + 1)) -
        2 * (m₂ : ℝ) * (-(m₁ : ℝ) - m₂)) * term3 j₁ j₂ j₃ m₁ m₂ σ ε
      + (((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) + m₁ + m₂ + 1)) * term3 j₁ j₂ j₃ m₁ (m₂ + 1) σ ε
      + (((j₂ : ℝ) - m₂ + 1) * ((j₃ : ℝ) - m₁ - m₂ + 1)) * term3 j₁ j₂ j₃ m₁ (m₂ - 1) σ ε
    = H3m j₁ j₂ j₃ m₁ m₂ (σ + 1) (-ε) - H3m j₁ j₂ j₃ m₁ m₂ σ ε := by
  have hR : ∀ (x : Fin 6 → ℚ) (k : Fin 6 → ℕ),
      (∀ i, ![σ, j₁ + j₂ - j₃ - σ, j₁ - m₁ - σ, j₂ + m₂ - σ + 1, j₃ - j₂ + m₁ + σ,
        j₃ - j₁ - m₂ + σ + 1] i = x i + k i) →
      P6 x = (∏ i, ∏ j ∈ Finset.range (k i), ((x i : ℝ) + (j + 1))) *
        P6 ![σ, j₁ + j₂ - j₃ - σ, j₁ - m₁ - σ, j₂ + m₂ - σ + 1, j₃ - j₂ + m₁ + σ,
          j₃ - j₁ - m₂ + σ + 1] :=
    fun x k h => P6_rel h
  generalize P6 ![σ, j₁ + j₂ - j₃ - σ, j₁ - m₁ - σ, j₂ + m₂ - σ + 1, j₃ - j₂ + m₁ + σ,
    j₃ - j₁ - m₂ + σ + 1] = U at hR
  have t0 : term3 j₁ j₂ j₃ m₁ m₂ σ ε =
      ε * ((((j₂ : ℝ) + m₂ - σ + 1)) * (((j₃ : ℝ) - j₁ - m₂ + σ + 1))) * U := by
    unfold term3
    rw [hR ![σ, j₁ + j₂ - j₃ - σ, j₁ - m₁ - σ, j₂ + m₂ - σ, j₃ - j₂ + m₁ + σ,
      j₃ - j₁ - m₂ + σ] ![0, 0, 0, 1, 0, 1] (by intro i; fin_cases i <;> simp)]
    simp only [Fin.prod_univ_six]
    try simp
    ring
  have t1 : term3 j₁ j₂ j₃ m₁ (m₂ + 1) σ ε =
      ε * (((j₃ : ℝ) - j₁ - m₂ + σ) * (((j₃ : ℝ) - j₁ - m₂ + σ + 1))) * U := by
    unfold term3
    rw [hR ![σ, j₁ + j₂ - j₃ - σ, j₁ - m₁ - σ, j₂ + (m₂ + 1) - σ, j₃ - j₂ + m₁ + σ,
      j₃ - j₁ - (m₂ + 1) + σ] ![0, 0, 0, 0, 0, 2] (by intro i; fin_cases i <;> simp <;> ring)]
    simp only [Fin.prod_univ_six]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have t2 : term3 j₁ j₂ j₃ m₁ (m₂ - 1) σ ε =
      ε * (((j₂ : ℝ) + m₂ - σ) * (((j₂ : ℝ) + m₂ - σ + 1))) * U := by
    unfold term3
    rw [hR ![σ, j₁ + j₂ - j₃ - σ, j₁ - m₁ - σ, j₂ + (m₂ - 1) - σ, j₃ - j₂ + m₁ + σ,
      j₃ - j₁ - (m₂ - 1) + σ] ![0, 0, 0, 2, 0, 0] (by intro i; fin_cases i <;> simp <;> ring)]
    simp only [Fin.prod_univ_six]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have tH0 : H3m j₁ j₂ j₃ m₁ m₂ σ ε =
      ε * ((j₁ : ℝ) - j₂ - j₃ - 1) * ((σ : ℝ) * (((j₃ : ℝ) - j₂ + m₁ + σ)) *
        (((j₃ : ℝ) - j₁ - m₂ + σ + 1))) * U := by
    unfold H3m
    rw [hR ![σ - 1, j₁ + j₂ - j₃ - σ, j₁ - m₁ - σ, j₂ + m₂ - σ + 1, j₃ - j₂ + m₁ + σ - 1,
      j₃ - j₁ - m₂ + σ] ![1, 0, 0, 0, 1, 1] (by intro i; fin_cases i <;> simp)]
    simp only [Fin.prod_univ_six]
    try simp
    ring
  have tH1 : H3m j₁ j₂ j₃ m₁ m₂ (σ + 1) (-ε) =
      (-ε) * ((j₁ : ℝ) - j₂ - j₃ - 1) * ((((j₁ : ℝ) + j₂ - j₃ - σ)) * (((j₁ : ℝ) - m₁ - σ)) *
        (((j₂ : ℝ) + m₂ - σ + 1))) * U := by
    unfold H3m
    rw [hR ![σ + 1 - 1, j₁ + j₂ - j₃ - (σ + 1), j₁ - m₁ - (σ + 1), j₂ + m₂ - (σ + 1) + 1,
      j₃ - j₂ + m₁ + (σ + 1) - 1, j₃ - j₁ - m₂ + (σ + 1)] ![0, 1, 1, 1, 0, 0]
      (by intro i; fin_cases i <;> simp <;> ring)]
    simp only [Fin.prod_univ_six]
    try simp
    ring
  rw [t0, t1, t2, tH1, tH0]
  exact rec3m_assemble _ _ _ _ _ _ _ _ _ _ _ _ (by ring)


lemma H3m_eq_zero {j₁ j₂ j₃ m₁ m₂ σ : ℚ} (ε : ℝ) (h : j₂ + m₂ - σ + 1 < 0) :
    H3m j₁ j₂ j₃ m₁ m₂ σ ε = 0 := by
  unfold H3m P6
  rw [Fin.prod_univ_six]
  simp [ifa_eq_zero_of_neg h]

lemma H3m_zero (j₁ j₂ j₃ m₁ m₂ : ℚ) (ε : ℝ) : H3m j₁ j₂ j₃ m₁ m₂ 0 ε = 0 := by
  unfold H3m P6
  rw [Fin.prod_univ_six]
  have : ifa (-1) = 0 := ifa_eq_zero_of_neg (by norm_num)
  simp [this]

/-- **Three-term `m`-recurrence of the `3j` Racah sum** (the rational form of DLMF 34.3.14),
valid for all rational arguments; `m₃ = -m₁-m₂`. -/
theorem racahSum3_m_recurrence (j₁ j₂ j₃ m₁ m₂ : ℚ) :
    (((j₁ : ℝ) * (j₁ + 1) - j₂ * (j₂ + 1) - j₃ * (j₃ + 1)) -
        2 * (m₂ : ℝ) * (-(m₁ : ℝ) - m₂)) * racahSum3 j₁ j₂ j₃ m₁ m₂
      + (((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) + m₁ + m₂ + 1)) * racahSum3 j₁ j₂ j₃ m₁ (m₂ + 1)
      + (((j₂ : ℝ) - m₂ + 1) * ((j₃ : ℝ) - m₁ - m₂ + 1)) * racahSum3 j₁ j₂ j₃ m₁ (m₂ - 1) = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, j₂ + m₂ + 1 < N :=
    ⟨⌈j₂ + m₂ + 1⌉₊ + 1, by
      have := Nat.le_ceil (j₂ + m₂ + 1)
      push_cast; linarith⟩
  rw [racahSum3_eq_sum j₁ j₂ j₃ m₁ m₂ N (by linarith),
    racahSum3_eq_sum j₁ j₂ j₃ m₁ (m₂ + 1) N (by linarith),
    racahSum3_eq_sum j₁ j₂ j₃ m₁ (m₂ - 1) N (by linarith), Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  set Hn : ℕ → ℝ := fun s => H3m j₁ j₂ j₃ m₁ m₂ s ((-1 : ℝ) ^ s) with hHn
  calc _ = ∑ s ∈ Finset.range N, (Hn (s + 1) - Hn s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        have := rec3m_pointwise j₁ j₂ j₃ m₁ m₂ (s : ℚ) ((-1 : ℝ) ^ s)
        simp only [hHn]
        rw [pow_succ, show ((s + 1 : ℕ) : ℚ) = (s : ℚ) + 1 by push_cast; ring]
        rw [show (-1 : ℝ) ^ s * -1 = -((-1 : ℝ) ^ s) by ring]
        exact this
    _ = 0 := by
        apply sum_range_telescope
        · simp only [hHn]
          simpa using H3m_zero j₁ j₂ j₃ m₁ m₂ 1
        · simp only [hHn]
          exact H3m_eq_zero _ (by linarith)

/-- info: 'FormalResearch.Wigner.racahSum3_m_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racahSum3_m_recurrence

end FormalResearch.Wigner
