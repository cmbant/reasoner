module

public import FormalResearch.Wigner.Defs
public import FormalResearch.Wigner.Rec3jKey

/-!
# The `j₁`-recurrence for the Racah sum of the `3j` symbol

`racahSum3 j₁ j₂ j₃ m₁ m₂` is the sum of DLMF 34.2.4 (with `m₃ = -m₁-m₂`) without its prefactors.
`racahSum3_recurrence` is the three-term recurrence in `j₁` (the rational form of DLMF 34.3.15);
it holds for **all** rational arguments.  The proof is a telescoping certificate:
`rec3_pointwise` shows that the combination of the three summands is `H (s+1) - H s` termwise,
with `H` an explicit polynomial multiple of a summand-like product (`H3`).
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- The summand of Racah's `3j` sum, as a function of the (rational) index `σ` and a sign `ε`. -/
noncomputable def term3 (j₁ j₂ j₃ m₁ m₂ σ : ℚ) (ε : ℝ) : ℝ :=
  ε * P6 ![σ, j₁ + j₂ - j₃ - σ, j₁ - m₁ - σ, j₂ + m₂ - σ, j₃ - j₂ + m₁ + σ, j₃ - j₁ - m₂ + σ]

/-- The sum in Racah's formula for the `3j` symbol (DLMF 34.2.4), without prefactors. -/
noncomputable def racahSum3 (j₁ j₂ j₃ m₁ m₂ : ℚ) : ℝ :=
  ∑ᶠ s : ℕ, term3 j₁ j₂ j₃ m₁ m₂ s ((-1 : ℝ) ^ s)

/-- The telescoping primitive of the `3j` recurrence. -/
noncomputable def H3 (j₁ j₂ j₃ m₁ m₂ σ : ℚ) (ε : ℝ) : ℝ :=
  ε * ((σ : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ) * Q3 j₁ j₂ j₃ m₁ m₂ σ) *
    P6 ![σ, j₁ + j₂ - j₃ - σ + 1, j₁ - m₁ - σ + 1, j₂ + m₂ - σ, j₃ - j₂ + m₁ + σ,
      j₃ - j₁ - m₂ + σ]

lemma rec3_assemble (C ρm ρp ε U P R0 R1 R2 X Y : ℝ) (key : C * R0 + ρm * R1 + ρp * R2 + X + Y = 0) :
    C * (ε * (P * R0) * U) + ρm * (ε * (P * R1) * U) + ρp * (ε * (P * R2) * U) =
      (-ε) * (P * X) * U - ε * (P * Y) * U := by
  linear_combination (ε * P * U) * key

set_option maxRecDepth 10000 in
/-- The pointwise telescoping identity behind the `j₁`-recurrence of the `3j` Racah sum. -/
lemma rec3_pointwise (j₁ j₂ j₃ m₁ m₂ σ : ℚ) (ε : ℝ) :
    (2 * (j₁ : ℝ) + 1) * (((j₂ : ℝ) * (j₂ + 1) - j₃ * (j₃ + 1)) * m₁ -
        j₁ * (j₁ + 1) * (-(m₁ : ℝ) - m₂ - m₂)) * term3 j₁ j₂ j₃ m₁ m₂ σ ε
      + ((j₁ : ℝ) + 1) * (((j₂ : ℝ) + j₃ + 1 - j₁) * (j₁ + j₂ + j₃ + 1)) *
          term3 (j₁ - 1) j₂ j₃ m₁ m₂ σ ε
      + (j₁ : ℝ) * (((j₁ : ℝ) + 1 + j₂ - j₃) * (j₁ + 1 - j₂ + j₃) * (j₁ + 1 + m₁) * (j₁ + 1 - m₁)) *
          term3 (j₁ + 1) j₂ j₃ m₁ m₂ σ ε
    = H3 j₁ j₂ j₃ m₁ m₂ (σ + 1) (-ε) - H3 j₁ j₂ j₃ m₁ m₂ σ ε := by
  have hR : ∀ (x : Fin 6 → ℚ) (k : Fin 6 → ℕ),
      (∀ i, ![σ + 1, j₁ + j₂ - j₃ - σ + 1, j₁ - m₁ - σ + 1, j₂ + m₂ - σ + 1,
        j₃ - j₂ + m₁ + σ + 1, j₃ - j₁ - m₂ + σ + 1] i = x i + k i) →
      P6 x = (∏ i, ∏ j ∈ Finset.range (k i), ((x i : ℝ) + (j + 1))) *
        P6 ![σ + 1, j₁ + j₂ - j₃ - σ + 1, j₁ - m₁ - σ + 1, j₂ + m₂ - σ + 1,
          j₃ - j₂ + m₁ + σ + 1, j₃ - j₁ - m₂ + σ + 1] :=
    fun x k h => P6_rel h
  generalize P6 ![σ + 1, j₁ + j₂ - j₃ - σ + 1, j₁ - m₁ - σ + 1, j₂ + m₂ - σ + 1,
    j₃ - j₂ + m₁ + σ + 1, j₃ - j₁ - m₂ + σ + 1] = U at hR
  have t0 : term3 j₁ j₂ j₃ m₁ m₂ σ ε = ε * (((σ + 1 : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ + 1) *
      ((j₂ : ℝ) + m₂ - σ + 1)) * (((j₃ : ℝ) - j₁ - m₂ + σ + 1) * ((j₁ : ℝ) + j₂ - j₃ - σ + 1) *
      ((j₁ : ℝ) - m₁ - σ + 1))) * U := by
    unfold term3
    rw [hR ![σ, j₁ + j₂ - j₃ - σ, j₁ - m₁ - σ, j₂ + m₂ - σ, j₃ - j₂ + m₁ + σ, j₃ - j₁ - m₂ + σ]
      ![1, 1, 1, 1, 1, 1] (by intro i; fin_cases i <;> simp)]
    simp only [Fin.prod_univ_six]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have t1 : term3 (j₁ - 1) j₂ j₃ m₁ m₂ σ ε = ε * (((σ + 1 : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ + 1) *
      ((j₂ : ℝ) + m₂ - σ + 1)) * (((j₁ : ℝ) + j₂ - j₃ - σ) * ((j₁ : ℝ) + j₂ - j₃ - σ + 1) *
      ((j₁ : ℝ) - m₁ - σ) * ((j₁ : ℝ) - m₁ - σ + 1))) * U := by
    unfold term3
    rw [hR ![σ, j₁ - 1 + j₂ - j₃ - σ, j₁ - 1 - m₁ - σ, j₂ + m₂ - σ, j₃ - j₂ + m₁ + σ,
      j₃ - (j₁ - 1) - m₂ + σ] ![1, 2, 2, 1, 1, 0] (by intro i; fin_cases i <;> simp <;> ring)]
    simp only [Fin.prod_univ_six]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have t2 : term3 (j₁ + 1) j₂ j₃ m₁ m₂ σ ε = ε * (((σ + 1 : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ + 1) *
      ((j₂ : ℝ) + m₂ - σ + 1)) * (((j₃ : ℝ) - j₁ - m₂ + σ) * ((j₃ : ℝ) - j₁ - m₂ + σ + 1))) * U := by
    unfold term3
    rw [hR ![σ, j₁ + 1 + j₂ - j₃ - σ, j₁ + 1 - m₁ - σ, j₂ + m₂ - σ, j₃ - j₂ + m₁ + σ,
      j₃ - (j₁ + 1) - m₂ + σ] ![1, 0, 0, 1, 1, 2] (by intro i; fin_cases i <;> simp <;> ring)]
    simp only [Fin.prod_univ_six]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have tH0 : H3 j₁ j₂ j₃ m₁ m₂ σ ε = ε * (((σ + 1 : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ + 1) *
      ((j₂ : ℝ) + m₂ - σ + 1)) * ((σ : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ) *
      ((j₃ : ℝ) - j₁ - m₂ + σ + 1) * Q3 j₁ j₂ j₃ m₁ m₂ σ)) * U := by
    unfold H3
    rw [hR ![σ, j₁ + j₂ - j₃ - σ + 1, j₁ - m₁ - σ + 1, j₂ + m₂ - σ, j₃ - j₂ + m₁ + σ,
      j₃ - j₁ - m₂ + σ] ![1, 0, 0, 1, 1, 1] (by intro i; fin_cases i <;> simp)]
    simp only [Fin.prod_univ_six]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have tH1 : H3 j₁ j₂ j₃ m₁ m₂ (σ + 1) (-ε) = (-ε) * (((σ + 1 : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ + 1) *
      ((j₂ : ℝ) + m₂ - σ + 1)) * (Q3 j₁ j₂ j₃ m₁ m₂ ((σ : ℝ) + 1) *
      (((j₁ : ℝ) + j₂ - j₃ - σ + 1) * ((j₁ : ℝ) - m₁ - σ + 1) * ((j₂ : ℝ) + m₂ - σ)))) * U := by
    unfold H3
    rw [hR ![σ + 1, j₁ + j₂ - j₃ - (σ + 1) + 1, j₁ - m₁ - (σ + 1) + 1, j₂ + m₂ - (σ + 1),
      j₃ - j₂ + m₁ + (σ + 1), j₃ - j₁ - m₂ + (σ + 1)] ![0, 1, 1, 2, 0, 0]
      (by intro i; fin_cases i <;> simp <;> ring)]
    simp only [Fin.prod_univ_six]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  rw [t0, t1, t2, tH1, tH0]
  exact rec3_assemble _ _ _ _ _ _ _ _ _ _ _ (rec3_key (σ : ℝ) j₁ j₂ j₃ m₁ m₂)


lemma term3_eq_zero {j₁ j₂ j₃ m₁ m₂ σ : ℚ} (ε : ℝ) (h : j₂ + m₂ - σ < 0) :
    term3 j₁ j₂ j₃ m₁ m₂ σ ε = 0 := by
  unfold term3 P6
  rw [Fin.prod_univ_six]
  simp [ifa_eq_zero_of_neg h]

lemma H3_eq_zero {j₁ j₂ j₃ m₁ m₂ σ : ℚ} (ε : ℝ) (h : j₂ + m₂ - σ < 0) :
    H3 j₁ j₂ j₃ m₁ m₂ σ ε = 0 := by
  unfold H3 P6
  rw [Fin.prod_univ_six]
  simp [ifa_eq_zero_of_neg h]

lemma racahSum3_eq_sum (j₁ j₂ j₃ m₁ m₂ : ℚ) (N : ℕ) (hN : j₂ + m₂ < N) :
    racahSum3 j₁ j₂ j₃ m₁ m₂ =
      ∑ s ∈ Finset.range N, term3 j₁ j₂ j₃ m₁ m₂ s ((-1 : ℝ) ^ s) := by
  unfold racahSum3
  apply finsum_eq_sum_of_support_subset
  intro s hs
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hs
  exact term3_eq_zero _ (by have : (N : ℚ) ≤ s := by exact_mod_cast not_lt.mp hlt
                            linarith)

/-- **Three-term recurrence of the `3j` Racah sum in `j₁`** (the rational form of DLMF 34.3.15),
valid for all rational arguments. -/
theorem racahSum3_recurrence (j₁ j₂ j₃ m₁ m₂ : ℚ) :
    (2 * (j₁ : ℝ) + 1) * (((j₂ : ℝ) * (j₂ + 1) - j₃ * (j₃ + 1)) * m₁ -
        j₁ * (j₁ + 1) * (-(m₁ : ℝ) - m₂ - m₂)) * racahSum3 j₁ j₂ j₃ m₁ m₂
      + ((j₁ : ℝ) + 1) * (((j₂ : ℝ) + j₃ + 1 - j₁) * (j₁ + j₂ + j₃ + 1)) *
          racahSum3 (j₁ - 1) j₂ j₃ m₁ m₂
      + (j₁ : ℝ) * (((j₁ : ℝ) + 1 + j₂ - j₃) * (j₁ + 1 - j₂ + j₃) * (j₁ + 1 + m₁) * (j₁ + 1 - m₁)) *
          racahSum3 (j₁ + 1) j₂ j₃ m₁ m₂ = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, j₂ + m₂ < N :=
    ⟨⌈j₂ + m₂⌉₊ + 1, by
      have := Nat.le_ceil (j₂ + m₂)
      push_cast; linarith⟩
  rw [racahSum3_eq_sum j₁ j₂ j₃ m₁ m₂ N hN, racahSum3_eq_sum (j₁ - 1) j₂ j₃ m₁ m₂ N hN,
    racahSum3_eq_sum (j₁ + 1) j₂ j₃ m₁ m₂ N hN, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  set Hn : ℕ → ℝ := fun s => H3 j₁ j₂ j₃ m₁ m₂ s ((-1 : ℝ) ^ s) with hHn
  calc _ = ∑ s ∈ Finset.range N, (Hn (s + 1) - Hn s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        have := rec3_pointwise j₁ j₂ j₃ m₁ m₂ (s : ℚ) ((-1 : ℝ) ^ s)
        simp only [hHn]
        rw [pow_succ, show ((s + 1 : ℕ) : ℚ) = (s : ℚ) + 1 by push_cast; ring]
        rw [show (-1 : ℝ) ^ s * -1 = -((-1 : ℝ) ^ s) by ring]
        exact this
    _ = 0 := by
        apply sum_range_telescope
        · simp [hHn, H3]
        · simp only [hHn]
          exact H3_eq_zero _ (by have : (N : ℚ) ≤ N := le_rfl
                                 linarith)

/-- info: 'FormalResearch.Wigner.racahSum3_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racahSum3_recurrence

end FormalResearch.Wigner
