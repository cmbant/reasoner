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


lemma rec6_ifa0 (x r : ℚ) (h : r = x) : ifa x = ifa r := by rw [h]

lemma rec6_ifa1 (x r : ℚ) (h : r = x + 1) : ifa x = ((x : ℝ) + 1) * ifa r := by
  rw [h]; exact (ifa_shift x).symm

lemma rec6_ifa2 (x r : ℚ) (h : r = x + 2) : ifa x = ((x : ℝ) + 1) * (((x : ℝ) + 2) * ifa r) := by
  have h1 := ifa_shift x
  have h2 := ifa_shift (x + 1)
  rw [h, show x + 2 = x + 1 + 1 by ring, ← h1, ← h2]
  push_cast; ring

lemma rec6_P7_mk (x₀ x₁ x₂ x₃ x₄ x₅ x₆ : ℚ) :
    P7 ![x₀, x₁, x₂, x₃, x₄, x₅, x₆] =
      ifa x₀ * ifa x₁ * ifa x₂ * ifa x₃ * ifa x₄ * ifa x₅ * ifa x₆ := by
  simp [P7, Fin.prod_univ_seven]

lemma rec6_P7_t0 (x₀ x₁ x₂ x₃ x₄ x₅ x₆ r₀ r₁ r₂ r₃ r₄ r₅ r₆ : ℚ) (c₀ c₁ c₂ c₃ c₄ c₆ : ℝ)
    (h0 : r₀ = x₀ + 1) (h1 : r₁ = x₁ + 1) (h2 : r₂ = x₂ + 1) (h3 : r₃ = x₃ + 1) (h4 : r₄ = x₄ + 1) (h5 : r₅ = x₅) (h6 : r₆ = x₆ + 1)
    (hc0 : (x₀ : ℝ) + 1 = c₀) (hc1 : (x₁ : ℝ) + 1 = c₁) (hc2 : (x₂ : ℝ) + 1 = c₂) (hc3 : (x₃ : ℝ) + 1 = c₃) (hc4 : (x₄ : ℝ) + 1 = c₄) (hc6 : (x₆ : ℝ) + 1 = c₆) :
    P7 ![x₀, x₁, x₂, x₃, x₄, x₅, x₆] = (c₀ * c₁ * c₂ * c₃ * c₄ * c₆) * P7 ![r₀, r₁, r₂, r₃, r₄, r₅, r₆] := by
  subst hc0 hc1 hc2 hc3 hc4 hc6
  rw [rec6_P7_mk, rec6_P7_mk, rec6_ifa1 x₀ r₀ h0, rec6_ifa1 x₁ r₁ h1, rec6_ifa1 x₂ r₂ h2, rec6_ifa1 x₃ r₃ h3, rec6_ifa1 x₄ r₄ h4, rec6_ifa0 x₅ r₅ h5, rec6_ifa1 x₆ r₆ h6]
  ring

lemma rec6_P7_t1 (x₀ x₁ x₂ x₃ x₄ x₅ x₆ r₀ r₁ r₂ r₃ r₄ r₅ r₆ : ℚ) (c₀ c₁ c₂ c₃ : ℝ)
    (h0 : r₀ = x₀ + 2) (h1 : r₁ = x₁ + 2) (h2 : r₂ = x₂ + 1) (h3 : r₃ = x₃ + 1) (h4 : r₄ = x₄) (h5 : r₅ = x₅) (h6 : r₆ = x₆)
    (hc0 : (x₀ : ℝ) + 1 = c₀) (hc1 : (x₁ : ℝ) + 1 = c₁) (hc2 : (x₂ : ℝ) + 1 = c₂) (hc3 : (x₃ : ℝ) + 1 = c₃) :
    P7 ![x₀, x₁, x₂, x₃, x₄, x₅, x₆] = ((c₀ * (c₀ + 1)) * (c₁ * (c₁ + 1)) * c₂ * c₃) * P7 ![r₀, r₁, r₂, r₃, r₄, r₅, r₆] := by
  subst hc0 hc1 hc2 hc3
  rw [rec6_P7_mk, rec6_P7_mk, rec6_ifa2 x₀ r₀ h0, rec6_ifa2 x₁ r₁ h1, rec6_ifa1 x₂ r₂ h2, rec6_ifa1 x₃ r₃ h3, rec6_ifa0 x₄ r₄ h4, rec6_ifa0 x₅ r₅ h5, rec6_ifa0 x₆ r₆ h6]
  ring

lemma rec6_P7_t2 (x₀ x₁ x₂ x₃ x₄ x₅ x₆ r₀ r₁ r₂ r₃ r₄ r₅ r₆ : ℚ) (c₂ c₃ c₄ c₆ : ℝ)
    (h0 : r₀ = x₀) (h1 : r₁ = x₁) (h2 : r₂ = x₂ + 1) (h3 : r₃ = x₃ + 1) (h4 : r₄ = x₄ + 2) (h5 : r₅ = x₅) (h6 : r₆ = x₆ + 2)
    (hc2 : (x₂ : ℝ) + 1 = c₂) (hc3 : (x₃ : ℝ) + 1 = c₃) (hc4 : (x₄ : ℝ) + 1 = c₄) (hc6 : (x₆ : ℝ) + 1 = c₆) :
    P7 ![x₀, x₁, x₂, x₃, x₄, x₅, x₆] = (c₂ * c₃ * (c₄ * (c₄ + 1)) * (c₆ * (c₆ + 1))) * P7 ![r₀, r₁, r₂, r₃, r₄, r₅, r₆] := by
  subst hc2 hc3 hc4 hc6
  rw [rec6_P7_mk, rec6_P7_mk, rec6_ifa0 x₀ r₀ h0, rec6_ifa0 x₁ r₁ h1, rec6_ifa1 x₂ r₂ h2, rec6_ifa1 x₃ r₃ h3, rec6_ifa2 x₄ r₄ h4, rec6_ifa0 x₅ r₅ h5, rec6_ifa2 x₆ r₆ h6]
  ring

lemma rec6_P7_tH0 (x₀ x₁ x₂ x₃ x₄ x₅ x₆ r₀ r₁ r₂ r₃ r₄ r₅ r₆ : ℚ) (c₀ c₁ c₂ c₃ : ℝ)
    (h0 : r₀ = x₀ + 1) (h1 : r₁ = x₁ + 1) (h2 : r₂ = x₂ + 1) (h3 : r₃ = x₃ + 1) (h4 : r₄ = x₄) (h5 : r₅ = x₅) (h6 : r₆ = x₆)
    (hc0 : (x₀ : ℝ) + 1 = c₀) (hc1 : (x₁ : ℝ) + 1 = c₁) (hc2 : (x₂ : ℝ) + 1 = c₂) (hc3 : (x₃ : ℝ) + 1 = c₃) :
    P7 ![x₀, x₁, x₂, x₃, x₄, x₅, x₆] = (c₀ * c₁ * c₂ * c₃) * P7 ![r₀, r₁, r₂, r₃, r₄, r₅, r₆] := by
  subst hc0 hc1 hc2 hc3
  rw [rec6_P7_mk, rec6_P7_mk, rec6_ifa1 x₀ r₀ h0, rec6_ifa1 x₁ r₁ h1, rec6_ifa1 x₂ r₂ h2, rec6_ifa1 x₃ r₃ h3, rec6_ifa0 x₄ r₄ h4, rec6_ifa0 x₅ r₅ h5, rec6_ifa0 x₆ r₆ h6]
  ring

lemma rec6_P7_tH1 (x₀ x₁ x₂ x₃ x₄ x₅ x₆ r₀ r₁ r₂ r₃ r₄ r₅ r₆ : ℚ) (c₄ c₅ c₆ : ℝ)
    (h0 : r₀ = x₀) (h1 : r₁ = x₁) (h2 : r₂ = x₂) (h3 : r₃ = x₃) (h4 : r₄ = x₄ + 1) (h5 : r₅ = x₅ + 1) (h6 : r₆ = x₆ + 1)
    (hc4 : (x₄ : ℝ) + 1 = c₄) (hc5 : (x₅ : ℝ) + 1 = c₅) (hc6 : (x₆ : ℝ) + 1 = c₆) :
    P7 ![x₀, x₁, x₂, x₃, x₄, x₅, x₆] = (c₄ * c₅ * c₆) * P7 ![r₀, r₁, r₂, r₃, r₄, r₅, r₆] := by
  subst hc4 hc5 hc6
  rw [rec6_P7_mk, rec6_P7_mk, rec6_ifa0 x₀ r₀ h0, rec6_ifa0 x₁ r₁ h1, rec6_ifa0 x₂ r₂ h2, rec6_ifa0 x₃ r₃ h3, rec6_ifa1 x₄ r₄ h4, rec6_ifa1 x₅ r₅ h5, rec6_ifa1 x₆ r₆ h6]
  ring


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
  obtain ⟨U, hU⟩ : ∃ U, P7 ![σ - j₁ - j₂ - j₃ + 1, σ - j₁ - l₂ - l₃ + 1, σ - l₁ - j₂ - l₃ + 1, σ - l₁ - l₂ - j₃ + 1, j₁ + j₂ + l₁ + l₂ - σ + 1, j₂ + j₃ + l₂ + l₃ - σ, j₃ + j₁ + l₃ + l₁ - σ + 1] = U := ⟨_, rfl⟩
  have t0 : term6 j₁ j₂ j₃ l₁ l₂ l₃ σ ε φ = ε * φ * (((((σ : ℝ) - l₁ - j₂ - l₃) + 1) * (((σ : ℝ) - l₁ - l₂ - j₃) + 1)) * ((((σ : ℝ) - j₁ - j₂ - j₃) + 1) * (((σ : ℝ) - j₁ - l₂ - l₃) + 1) * (((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) + 1) * (((j₃ : ℝ) + j₁ + l₃ + l₁ - σ) + 1))) * U := by
    unfold term6
    rw [rec6_P7_t0 (σ - j₁ - j₂ - j₃) (σ - j₁ - l₂ - l₃) (σ - l₁ - j₂ - l₃) (σ - l₁ - l₂ - j₃) (j₁ + j₂ + l₁ + l₂ - σ) (j₂ + j₃ + l₂ + l₃ - σ) (j₃ + j₁ + l₃ + l₁ - σ) (σ - j₁ - j₂ - j₃ + 1) (σ - j₁ - l₂ - l₃ + 1) (σ - l₁ - j₂ - l₃ + 1) (σ - l₁ - l₂ - j₃ + 1) (j₁ + j₂ + l₁ + l₂ - σ + 1) (j₂ + j₃ + l₂ + l₃ - σ) (j₃ + j₁ + l₃ + l₁ - σ + 1) (((σ : ℝ) - j₁ - j₂ - j₃) + 1) (((σ : ℝ) - j₁ - l₂ - l₃) + 1) (((σ : ℝ) - l₁ - j₂ - l₃) + 1) (((σ : ℝ) - l₁ - l₂ - j₃) + 1) (((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) + 1) (((j₃ : ℝ) + j₁ + l₃ + l₁ - σ) + 1)
      (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring), hU]
    ac_rfl
  have t1 : term6 (j₁ + 1) j₂ j₃ l₁ l₂ l₃ σ ε φ = ε * φ * (((((σ : ℝ) - l₁ - j₂ - l₃) + 1) * (((σ : ℝ) - l₁ - l₂ - j₃) + 1)) * (((σ : ℝ) - j₁ - j₂ - j₃) * (((σ : ℝ) - j₁ - j₂ - j₃) + 1) * ((σ : ℝ) - j₁ - l₂ - l₃) * (((σ : ℝ) - j₁ - l₂ - l₃) + 1))) * U := by
    unfold term6
    rw [rec6_P7_t1 (σ - (j₁ + 1) - j₂ - j₃) (σ - (j₁ + 1) - l₂ - l₃) (σ - l₁ - j₂ - l₃) (σ - l₁ - l₂ - j₃) (j₁ + 1 + j₂ + l₁ + l₂ - σ) (j₂ + j₃ + l₂ + l₃ - σ) (j₃ + (j₁ + 1) + l₃ + l₁ - σ) (σ - j₁ - j₂ - j₃ + 1) (σ - j₁ - l₂ - l₃ + 1) (σ - l₁ - j₂ - l₃ + 1) (σ - l₁ - l₂ - j₃ + 1) (j₁ + j₂ + l₁ + l₂ - σ + 1) (j₂ + j₃ + l₂ + l₃ - σ) (j₃ + j₁ + l₃ + l₁ - σ + 1) ((σ : ℝ) - j₁ - j₂ - j₃) ((σ : ℝ) - j₁ - l₂ - l₃) (((σ : ℝ) - l₁ - j₂ - l₃) + 1) (((σ : ℝ) - l₁ - l₂ - j₃) + 1)
      (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring), hU]
    ac_rfl
  have t2 : term6 (j₁ - 1) j₂ j₃ l₁ l₂ l₃ σ ε φ = ε * φ * (((((σ : ℝ) - l₁ - j₂ - l₃) + 1) * (((σ : ℝ) - l₁ - l₂ - j₃) + 1)) * (((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) * (((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) + 1) * ((j₃ : ℝ) + j₁ + l₃ + l₁ - σ) * (((j₃ : ℝ) + j₁ + l₃ + l₁ - σ) + 1))) * U := by
    unfold term6
    rw [rec6_P7_t2 (σ - (j₁ - 1) - j₂ - j₃) (σ - (j₁ - 1) - l₂ - l₃) (σ - l₁ - j₂ - l₃) (σ - l₁ - l₂ - j₃) (j₁ - 1 + j₂ + l₁ + l₂ - σ) (j₂ + j₃ + l₂ + l₃ - σ) (j₃ + (j₁ - 1) + l₃ + l₁ - σ) (σ - j₁ - j₂ - j₃ + 1) (σ - j₁ - l₂ - l₃ + 1) (σ - l₁ - j₂ - l₃ + 1) (σ - l₁ - l₂ - j₃ + 1) (j₁ + j₂ + l₁ + l₂ - σ + 1) (j₂ + j₃ + l₂ + l₃ - σ) (j₃ + j₁ + l₃ + l₁ - σ + 1) (((σ : ℝ) - l₁ - j₂ - l₃) + 1) (((σ : ℝ) - l₁ - l₂ - j₃) + 1) ((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) ((j₃ : ℝ) + j₁ + l₃ + l₁ - σ)
      (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring), hU]
    ac_rfl
  have tH0 : H6 j₁ j₂ j₃ l₁ l₂ l₃ σ ε φ = ε * φ * (((((σ : ℝ) - l₁ - j₂ - l₃) + 1) * (((σ : ℝ) - l₁ - l₂ - j₃) + 1)) * (((σ : ℝ) - l₁ - j₂ - l₃) * ((σ : ℝ) - l₁ - l₂ - j₃) * ((((σ : ℝ) - j₁ - j₂ - j₃) + 1) * (((σ : ℝ) - j₁ - l₂ - l₃) + 1)) * Q6 j₁ j₂ j₃ l₁ l₂ l₃ (σ : ℝ))) * U := by
    unfold H6
    rw [rec6_P7_tH0 (σ - j₁ - j₂ - j₃) (σ - j₁ - l₂ - l₃) (σ - l₁ - j₂ - l₃) (σ - l₁ - l₂ - j₃) (j₁ + j₂ + l₁ + l₂ - σ + 1) (j₂ + j₃ + l₂ + l₃ - σ) (j₃ + j₁ + l₃ + l₁ - σ + 1) (σ - j₁ - j₂ - j₃ + 1) (σ - j₁ - l₂ - l₃ + 1) (σ - l₁ - j₂ - l₃ + 1) (σ - l₁ - l₂ - j₃ + 1) (j₁ + j₂ + l₁ + l₂ - σ + 1) (j₂ + j₃ + l₂ + l₃ - σ) (j₃ + j₁ + l₃ + l₁ - σ + 1) (((σ : ℝ) - j₁ - j₂ - j₃) + 1) (((σ : ℝ) - j₁ - l₂ - l₃) + 1) (((σ : ℝ) - l₁ - j₂ - l₃) + 1) (((σ : ℝ) - l₁ - l₂ - j₃) + 1)
      (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring), hU]
    ac_rfl
  have tH1 : H6 j₁ j₂ j₃ l₁ l₂ l₃ (σ + 1) (-ε) (((σ : ℝ) + 2) * φ) =
      (-ε) * φ * (((((σ : ℝ) - l₁ - j₂ - l₃) + 1) * (((σ : ℝ) - l₁ - l₂ - j₃) + 1)) * (((σ : ℝ) + 2) * Q6 j₁ j₂ j₃ l₁ l₂ l₃ ((σ : ℝ) + 1) * (((j₂ : ℝ) + j₃ + l₂ + l₃ - σ) * (((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) + 1) * (((j₃ : ℝ) + j₁ + l₃ + l₁ - σ) + 1)))) * U := by
    have e2 : (((σ + 1 : ℚ) : ℝ) - l₁ - j₂ - l₃) = ((σ : ℝ) - l₁ - j₂ - l₃) + 1 := by push_cast; ring
    have e3 : (((σ + 1 : ℚ) : ℝ) - l₁ - l₂ - j₃) = ((σ : ℝ) - l₁ - l₂ - j₃) + 1 := by push_cast; ring
    unfold H6
    rw [e2, e3]
    rw [rec6_P7_tH1 (σ + 1 - j₁ - j₂ - j₃) (σ + 1 - j₁ - l₂ - l₃) (σ + 1 - l₁ - j₂ - l₃) (σ + 1 - l₁ - l₂ - j₃) (j₁ + j₂ + l₁ + l₂ - (σ + 1) + 1) (j₂ + j₃ + l₂ + l₃ - (σ + 1)) (j₃ + j₁ + l₃ + l₁ - (σ + 1) + 1) (σ - j₁ - j₂ - j₃ + 1) (σ - j₁ - l₂ - l₃ + 1) (σ - l₁ - j₂ - l₃ + 1) (σ - l₁ - l₂ - j₃ + 1) (j₁ + j₂ + l₁ + l₂ - σ + 1) (j₂ + j₃ + l₂ + l₃ - σ) (j₃ + j₁ + l₃ + l₁ - σ + 1) (((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) + 1) ((j₂ : ℝ) + j₃ + l₂ + l₃ - σ) (((j₃ : ℝ) + j₁ + l₃ + l₁ - σ) + 1)
      (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring), hU]
    push_cast
    ac_rfl
  rw [t0, t1, t2, tH1, tH0]
  exact rec6_assemble _ _ _ _ _ _ _ _ _ _ _ _
    (rec6_key (σ : ℝ) j₁ j₂ j₃ l₁ l₂ l₃ ((σ : ℝ) - j₁ - j₂ - j₃) ((σ : ℝ) - j₁ - l₂ - l₃) ((σ : ℝ) - l₁ - j₂ - l₃) ((σ : ℝ) - l₁ - l₂ - j₃) ((j₁ : ℝ) + j₂ + l₁ + l₂ - σ) ((j₂ : ℝ) + j₃ + l₂ + l₃ - σ) ((j₃ : ℝ) + j₁ + l₃ + l₁ - σ)
      rfl rfl rfl rfl rfl rfl rfl)


end FormalResearch.Wigner
