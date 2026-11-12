module

public import FormalResearch.Wigner.Defs
public import FormalResearch.Wigner.Rec6jKey

/-!
# The `j₁`-recurrence for the Racah sum of the `6j` symbol

`racahSum6 j₁ j₂ j₃ l₁ l₂ l₃` is the sum of DLMF 34.4.2 without its four `Δ` prefactors.
`racahSum6_recurrence` is the three-term recurrence in `j₁` (the rational form of DLMF 34.5.11);
it holds for all rational spins with `0 ≤ l₁ + j₂ + l₃`.  The proof is a telescoping certificate:
`rec6_pointwise` shows that the combination of the three summands equals `H (t+1) - H t`
termwise (`H6`), by the reduction to `rec6_key`.
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- The telescoping primitive of the `6j` recurrence. -/
noncomputable def H6 (j₁ j₂ j₃ l₁ l₂ l₃ σ : ℚ) (ε φ : ℝ) : ℝ :=
  ε * φ * ((((σ : ℝ) - l₁ - j₂ - l₃)) * (((σ : ℝ) - l₁ - l₂ - j₃)) * Q6 j₁ j₂ j₃ l₁ l₂ l₃ (σ : ℝ)) *
    P7 ![σ - j₁ - j₂ - j₃, σ - j₁ - l₂ - l₃, σ - l₁ - j₂ - l₃, σ - l₁ - l₂ - j₃, j₁ + j₂ + l₁ + l₂ - σ + 1, j₂ + j₃ + l₂ + l₃ - σ, j₃ + j₁ + l₃ + l₁ - σ + 1]

lemma rec6_assemble (C0 C1 C2 ε φ U P R0 R1 R2 X Y : ℝ)
    (key : C0 * R0 - C1 * R1 - C2 * R2 + X + Y = 0) :
    C0 * (ε * φ * (P * R0) * U) - C1 * (ε * φ * (P * R1) * U) - C2 * (ε * φ * (P * R2) * U) =
      (-ε) * φ * (P * X) * U - ε * φ * (P * Y) * U := by
  linear_combination (ε * φ * P * U) * key

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- The pointwise telescoping identity behind the `j₁`-recurrence of the `6j` Racah sum. -/
lemma rec6_pointwise (j₁ j₂ j₃ l₁ l₂ l₃ σ : ℚ) (ε φ : ℝ) :
    (2 * (j₁ : ℝ) + 1) *
          ((((j₃ : ℝ) * (j₃ + 1) + j₂ * (j₂ + 1) - j₁ * (j₁ + 1)) *
              ((l₃ : ℝ) * (l₃ + 1) + l₂ * (l₂ + 1) - j₁ * (j₁ + 1))) -
            2 * ((j₃ : ℝ) * (j₃ + 1) * (l₃ * (l₃ + 1)) + j₂ * (j₂ + 1) * (l₂ * (l₂ + 1)) -
              j₁ * (j₁ + 1) * (l₁ * (l₁ + 1)))) * term6 j₁ j₂ j₃ l₁ l₂ l₃ σ ε φ
      - (j₁ : ℝ) * (((j₁ : ℝ) + 1 + j₂ - j₃) * (j₁ + 1 - j₂ + j₃) * (j₁ + 1 + l₂ - l₃) *
          (j₁ + 1 - l₂ + l₃)) * term6 (j₁ + 1) j₂ j₃ l₁ l₂ l₃ σ ε φ
      - ((j₁ : ℝ) + 1) * (((j₂ : ℝ) + j₃ + 1 - j₁) * (j₂ + j₃ + 1 + j₁) * (l₂ + l₃ + 1 - j₁) *
          (l₂ + l₃ + 1 + j₁)) * term6 (j₁ - 1) j₂ j₃ l₁ l₂ l₃ σ ε φ
    = H6 j₁ j₂ j₃ l₁ l₂ l₃ (σ + 1) (-ε) (((σ : ℝ) + 2) * φ) - H6 j₁ j₂ j₃ l₁ l₂ l₃ σ ε φ := by
  have hR : ∀ (x : Fin 7 → ℚ) (k : Fin 7 → ℕ),
      (∀ i, ![σ - j₁ - j₂ - j₃ + 1, σ - j₁ - l₂ - l₃ + 1, σ - l₁ - j₂ - l₃ + 1, σ - l₁ - l₂ - j₃ + 1, j₁ + j₂ + l₁ + l₂ - σ + 1, j₂ + j₃ + l₂ + l₃ - σ, j₃ + j₁ + l₃ + l₁ - σ + 1] i = x i + k i) →
      P7 x = (∏ i, ∏ j ∈ Finset.range (k i), ((x i : ℝ) + (j + 1))) *
        P7 ![σ - j₁ - j₂ - j₃ + 1, σ - j₁ - l₂ - l₃ + 1, σ - l₁ - j₂ - l₃ + 1, σ - l₁ - l₂ - j₃ + 1, j₁ + j₂ + l₁ + l₂ - σ + 1, j₂ + j₃ + l₂ + l₃ - σ, j₃ + j₁ + l₃ + l₁ - σ + 1] :=
    fun x k h => P7_rel h
  generalize P7 ![σ - j₁ - j₂ - j₃ + 1, σ - j₁ - l₂ - l₃ + 1, σ - l₁ - j₂ - l₃ + 1, σ - l₁ - l₂ - j₃ + 1, j₁ + j₂ + l₁ + l₂ - σ + 1, j₂ + j₃ + l₂ + l₃ - σ, j₃ + j₁ + l₃ + l₁ - σ + 1] = U at hR
  have t0 : term6 j₁ j₂ j₃ l₁ l₂ l₃ σ ε φ = ε * φ * (((((σ : ℝ) - l₁ - j₂ - l₃) + 1) * (((σ : ℝ) - l₁ - l₂ - j₃) + 1)) * ((((σ : ℝ) - j₁ - j₂ - j₃) + 1) * (((σ : ℝ) - j₁ - l₂ - l₃) + 1) * (((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) + 1) * (((j₃ : ℝ) + j₁ + l₃ + l₁ - σ) + 1))) * U := by
    unfold term6
    rw [hR ![σ - j₁ - j₂ - j₃, σ - j₁ - l₂ - l₃, σ - l₁ - j₂ - l₃, σ - l₁ - l₂ - j₃, j₁ + j₂ + l₁ + l₂ - σ, j₂ + j₃ + l₂ + l₃ - σ, j₃ + j₁ + l₃ + l₁ - σ] ![1, 1, 1, 1, 1, 0, 1]
      (by intro i; fin_cases i <;> simp)]
    simp only [Fin.prod_univ_seven]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have t1 : term6 (j₁ + 1) j₂ j₃ l₁ l₂ l₃ σ ε φ = ε * φ * (((((σ : ℝ) - l₁ - j₂ - l₃) + 1) * (((σ : ℝ) - l₁ - l₂ - j₃) + 1)) * (((σ : ℝ) - j₁ - j₂ - j₃) * (((σ : ℝ) - j₁ - j₂ - j₃) + 1) * ((σ : ℝ) - j₁ - l₂ - l₃) * (((σ : ℝ) - j₁ - l₂ - l₃) + 1))) * U := by
    unfold term6
    rw [hR ![σ - (j₁ + 1) - j₂ - j₃, σ - (j₁ + 1) - l₂ - l₃, σ - l₁ - j₂ - l₃, σ - l₁ - l₂ - j₃, j₁ + 1 + j₂ + l₁ + l₂ - σ, j₂ + j₃ + l₂ + l₃ - σ, j₃ + (j₁ + 1) + l₃ + l₁ - σ] ![2, 2, 1, 1, 0, 0, 0]
      (by intro i; fin_cases i <;> simp <;> ring)]
    simp only [Fin.prod_univ_seven]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have t2 : term6 (j₁ - 1) j₂ j₃ l₁ l₂ l₃ σ ε φ = ε * φ * (((((σ : ℝ) - l₁ - j₂ - l₃) + 1) * (((σ : ℝ) - l₁ - l₂ - j₃) + 1)) * (((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) * (((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) + 1) * ((j₃ : ℝ) + j₁ + l₃ + l₁ - σ) * (((j₃ : ℝ) + j₁ + l₃ + l₁ - σ) + 1))) * U := by
    unfold term6
    rw [hR ![σ - (j₁ - 1) - j₂ - j₃, σ - (j₁ - 1) - l₂ - l₃, σ - l₁ - j₂ - l₃, σ - l₁ - l₂ - j₃, j₁ - 1 + j₂ + l₁ + l₂ - σ, j₂ + j₃ + l₂ + l₃ - σ, j₃ + (j₁ - 1) + l₃ + l₁ - σ] ![0, 0, 1, 1, 2, 0, 2]
      (by intro i; fin_cases i <;> simp <;> ring)]
    simp only [Fin.prod_univ_seven]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have tH0 : H6 j₁ j₂ j₃ l₁ l₂ l₃ σ ε φ = ε * φ * (((((σ : ℝ) - l₁ - j₂ - l₃) + 1) * (((σ : ℝ) - l₁ - l₂ - j₃) + 1)) * (((σ : ℝ) - l₁ - j₂ - l₃) * ((σ : ℝ) - l₁ - l₂ - j₃) * ((((σ : ℝ) - j₁ - j₂ - j₃) + 1) * (((σ : ℝ) - j₁ - l₂ - l₃) + 1)) * Q6 j₁ j₂ j₃ l₁ l₂ l₃ (σ : ℝ))) * U := by
    unfold H6
    rw [hR ![σ - j₁ - j₂ - j₃, σ - j₁ - l₂ - l₃, σ - l₁ - j₂ - l₃, σ - l₁ - l₂ - j₃, j₁ + j₂ + l₁ + l₂ - σ + 1, j₂ + j₃ + l₂ + l₃ - σ, j₃ + j₁ + l₃ + l₁ - σ + 1] ![1, 1, 1, 1, 0, 0, 0]
      (by intro i; fin_cases i <;> simp <;> ring)]
    simp only [Fin.prod_univ_seven]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have tH1 : H6 j₁ j₂ j₃ l₁ l₂ l₃ (σ + 1) (-ε) (((σ : ℝ) + 2) * φ) =
      (-ε) * φ * (((((σ : ℝ) - l₁ - j₂ - l₃) + 1) * (((σ : ℝ) - l₁ - l₂ - j₃) + 1)) * (((σ : ℝ) + 2) * Q6 j₁ j₂ j₃ l₁ l₂ l₃ ((σ : ℝ) + 1) * (((j₂ : ℝ) + j₃ + l₂ + l₃ - σ) * (((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) + 1) * (((j₃ : ℝ) + j₁ + l₃ + l₁ - σ) + 1)))) * U := by
    unfold H6
    rw [hR ![σ + 1 - j₁ - j₂ - j₃, σ + 1 - j₁ - l₂ - l₃, σ + 1 - l₁ - j₂ - l₃, σ + 1 - l₁ - l₂ - j₃, j₁ + j₂ + l₁ + l₂ - (σ + 1) + 1, j₂ + j₃ + l₂ + l₃ - (σ + 1), j₃ + j₁ + l₃ + l₁ - (σ + 1) + 1] ![0, 0, 0, 0, 1, 1, 1]
      (by intro i; fin_cases i <;> simp <;> ring)]
    simp only [Fin.prod_univ_seven]
    try simp
    try simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  rw [t0, t1, t2, tH1, tH0]
  exact rec6_assemble _ _ _ _ _ _ _ _ _ _ _ _
    (rec6_key (σ : ℝ) j₁ j₂ j₃ l₁ l₂ l₃ ((σ : ℝ) - j₁ - j₂ - j₃) ((σ : ℝ) - j₁ - l₂ - l₃) ((σ : ℝ) - l₁ - j₂ - l₃) ((σ : ℝ) - l₁ - l₂ - j₃) ((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) ((j₂ : ℝ) + j₃ + l₂ + l₃ - σ) ((j₃ : ℝ) + j₁ + l₃ + l₁ - σ)
      rfl rfl rfl rfl rfl rfl rfl)


end FormalResearch.Wigner
