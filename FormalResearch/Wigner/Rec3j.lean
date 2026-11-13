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


lemma rec3_ifa0 (x r : ℚ) (h : r = x) : ifa x = ifa r := by rw [h]

lemma rec3_ifa1 (x r : ℚ) (h : r = x + 1) : ifa x = ((x : ℝ) + 1) * ifa r := by
  rw [h]; exact (ifa_shift x).symm

lemma rec3_ifa2 (x r : ℚ) (h : r = x + 2) : ifa x = ((x : ℝ) + 1) * (((x : ℝ) + 2) * ifa r) := by
  have h1 := ifa_shift x
  have h2 := ifa_shift (x + 1)
  rw [h, show x + 2 = x + 1 + 1 by ring, ← h1, ← h2]
  push_cast; ring

lemma rec3_P6_mk (x₀ x₁ x₂ x₃ x₄ x₅ : ℚ) :
    P6 ![x₀, x₁, x₂, x₃, x₄, x₅] = ifa x₀ * ifa x₁ * ifa x₂ * ifa x₃ * ifa x₄ * ifa x₅ := by
  simp [P6, Fin.prod_univ_six]

lemma rec3_P6_t0 (x₀ x₁ x₂ x₃ x₄ x₅ r₀ r₁ r₂ r₃ r₄ r₅ : ℚ) (c₀ c₁ c₂ c₃ c₄ c₅ : ℝ)
    (h0 : r₀ = x₀ + 1) (h1 : r₁ = x₁ + 1) (h2 : r₂ = x₂ + 1) (h3 : r₃ = x₃ + 1) (h4 : r₄ = x₄ + 1) (h5 : r₅ = x₅ + 1)
    (hc0 : (x₀ : ℝ) + 1 = c₀) (hc1 : (x₁ : ℝ) + 1 = c₁) (hc2 : (x₂ : ℝ) + 1 = c₂) (hc3 : (x₃ : ℝ) + 1 = c₃) (hc4 : (x₄ : ℝ) + 1 = c₄) (hc5 : (x₅ : ℝ) + 1 = c₅) :
    P6 ![x₀, x₁, x₂, x₃, x₄, x₅] = (c₀ * c₁ * c₂ * c₃ * c₄ * c₅) * P6 ![r₀, r₁, r₂, r₃, r₄, r₅] := by
  subst hc0 hc1 hc2 hc3 hc4 hc5
  rw [rec3_P6_mk, rec3_P6_mk, rec3_ifa1 x₀ r₀ h0, rec3_ifa1 x₁ r₁ h1, rec3_ifa1 x₂ r₂ h2, rec3_ifa1 x₃ r₃ h3, rec3_ifa1 x₄ r₄ h4, rec3_ifa1 x₅ r₅ h5]
  ring

lemma rec3_P6_t1 (x₀ x₁ x₂ x₃ x₄ x₅ r₀ r₁ r₂ r₃ r₄ r₅ : ℚ) (c₀ c₁ c₂ c₃ c₄ : ℝ)
    (h0 : r₀ = x₀ + 1) (h1 : r₁ = x₁ + 2) (h2 : r₂ = x₂ + 2) (h3 : r₃ = x₃ + 1) (h4 : r₄ = x₄ + 1) (h5 : r₅ = x₅)
    (hc0 : (x₀ : ℝ) + 1 = c₀) (hc1 : (x₁ : ℝ) + 1 = c₁) (hc2 : (x₂ : ℝ) + 1 = c₂) (hc3 : (x₃ : ℝ) + 1 = c₃) (hc4 : (x₄ : ℝ) + 1 = c₄) :
    P6 ![x₀, x₁, x₂, x₃, x₄, x₅] = (c₀ * (c₁ * (c₁ + 1)) * (c₂ * (c₂ + 1)) * c₃ * c₄) * P6 ![r₀, r₁, r₂, r₃, r₄, r₅] := by
  subst hc0 hc1 hc2 hc3 hc4
  rw [rec3_P6_mk, rec3_P6_mk, rec3_ifa1 x₀ r₀ h0, rec3_ifa2 x₁ r₁ h1, rec3_ifa2 x₂ r₂ h2, rec3_ifa1 x₃ r₃ h3, rec3_ifa1 x₄ r₄ h4, rec3_ifa0 x₅ r₅ h5]
  ring

lemma rec3_P6_t2 (x₀ x₁ x₂ x₃ x₄ x₅ r₀ r₁ r₂ r₃ r₄ r₅ : ℚ) (c₀ c₃ c₄ c₅ : ℝ)
    (h0 : r₀ = x₀ + 1) (h1 : r₁ = x₁) (h2 : r₂ = x₂) (h3 : r₃ = x₃ + 1) (h4 : r₄ = x₄ + 1) (h5 : r₅ = x₅ + 2)
    (hc0 : (x₀ : ℝ) + 1 = c₀) (hc3 : (x₃ : ℝ) + 1 = c₃) (hc4 : (x₄ : ℝ) + 1 = c₄) (hc5 : (x₅ : ℝ) + 1 = c₅) :
    P6 ![x₀, x₁, x₂, x₃, x₄, x₅] = (c₀ * c₃ * c₄ * (c₅ * (c₅ + 1))) * P6 ![r₀, r₁, r₂, r₃, r₄, r₅] := by
  subst hc0 hc3 hc4 hc5
  rw [rec3_P6_mk, rec3_P6_mk, rec3_ifa1 x₀ r₀ h0, rec3_ifa0 x₁ r₁ h1, rec3_ifa0 x₂ r₂ h2, rec3_ifa1 x₃ r₃ h3, rec3_ifa1 x₄ r₄ h4, rec3_ifa2 x₅ r₅ h5]
  ring

lemma rec3_P6_tH0 (x₀ x₁ x₂ x₃ x₄ x₅ r₀ r₁ r₂ r₃ r₄ r₅ : ℚ) (c₀ c₃ c₄ c₅ : ℝ)
    (h0 : r₀ = x₀ + 1) (h1 : r₁ = x₁) (h2 : r₂ = x₂) (h3 : r₃ = x₃ + 1) (h4 : r₄ = x₄ + 1) (h5 : r₅ = x₅ + 1)
    (hc0 : (x₀ : ℝ) + 1 = c₀) (hc3 : (x₃ : ℝ) + 1 = c₃) (hc4 : (x₄ : ℝ) + 1 = c₄) (hc5 : (x₅ : ℝ) + 1 = c₅) :
    P6 ![x₀, x₁, x₂, x₃, x₄, x₅] = (c₀ * c₃ * c₄ * c₅) * P6 ![r₀, r₁, r₂, r₃, r₄, r₅] := by
  subst hc0 hc3 hc4 hc5
  rw [rec3_P6_mk, rec3_P6_mk, rec3_ifa1 x₀ r₀ h0, rec3_ifa0 x₁ r₁ h1, rec3_ifa0 x₂ r₂ h2, rec3_ifa1 x₃ r₃ h3, rec3_ifa1 x₄ r₄ h4, rec3_ifa1 x₅ r₅ h5]
  ring

lemma rec3_P6_tH1 (x₀ x₁ x₂ x₃ x₄ x₅ r₀ r₁ r₂ r₃ r₄ r₅ : ℚ) (c₁ c₂ c₃ : ℝ)
    (h0 : r₀ = x₀) (h1 : r₁ = x₁ + 1) (h2 : r₂ = x₂ + 1) (h3 : r₃ = x₃ + 2) (h4 : r₄ = x₄) (h5 : r₅ = x₅)
    (hc1 : (x₁ : ℝ) + 1 = c₁) (hc2 : (x₂ : ℝ) + 1 = c₂) (hc3 : (x₃ : ℝ) + 1 = c₃) :
    P6 ![x₀, x₁, x₂, x₃, x₄, x₅] = (c₁ * c₂ * (c₃ * (c₃ + 1))) * P6 ![r₀, r₁, r₂, r₃, r₄, r₅] := by
  subst hc1 hc2 hc3
  rw [rec3_P6_mk, rec3_P6_mk, rec3_ifa0 x₀ r₀ h0, rec3_ifa1 x₁ r₁ h1, rec3_ifa1 x₂ r₂ h2, rec3_ifa2 x₃ r₃ h3, rec3_ifa0 x₄ r₄ h4, rec3_ifa0 x₅ r₅ h5]
  ring


/-- The pointwise telescoping identity behind the `j₁`-recurrence of the `3j` Racah sum. -/
lemma rec3_pointwise (j₁ j₂ j₃ m₁ m₂ σ : ℚ) (ε : ℝ) :
    (2 * (j₁ : ℝ) + 1) * (((j₂ : ℝ) * (j₂ + 1) - j₃ * (j₃ + 1)) * m₁ -
        j₁ * (j₁ + 1) * (-(m₁ : ℝ) - m₂ - m₂)) * term3 j₁ j₂ j₃ m₁ m₂ σ ε
      + ((j₁ : ℝ) + 1) * (((j₂ : ℝ) + j₃ + 1 - j₁) * (j₁ + j₂ + j₃ + 1)) *
          term3 (j₁ - 1) j₂ j₃ m₁ m₂ σ ε
      + (j₁ : ℝ) * (((j₁ : ℝ) + 1 + j₂ - j₃) * (j₁ + 1 - j₂ + j₃) * (j₁ + 1 + m₁) * (j₁ + 1 - m₁)) *
          term3 (j₁ + 1) j₂ j₃ m₁ m₂ σ ε
    = H3 j₁ j₂ j₃ m₁ m₂ (σ + 1) (-ε) - H3 j₁ j₂ j₃ m₁ m₂ σ ε := by
  obtain ⟨U, hU⟩ : ∃ U, P6 ![σ + 1, j₁ + j₂ - j₃ - σ + 1, j₁ - m₁ - σ + 1, j₂ + m₂ - σ + 1, j₃ - j₂ + m₁ + σ + 1, j₃ - j₁ - m₂ + σ + 1] = U := ⟨_, rfl⟩
  have t0 : term3 j₁ j₂ j₃ m₁ m₂ σ ε = ε * (((σ + 1 : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ + 1) *
      ((j₂ : ℝ) + m₂ - σ + 1)) * (((j₃ : ℝ) - j₁ - m₂ + σ + 1) * ((j₁ : ℝ) + j₂ - j₃ - σ + 1) *
      ((j₁ : ℝ) - m₁ - σ + 1))) * U := by
    unfold term3
    rw [rec3_P6_t0 (σ) (j₁ + j₂ - j₃ - σ) (j₁ - m₁ - σ) (j₂ + m₂ - σ) (j₃ - j₂ + m₁ + σ) (j₃ - j₁ - m₂ + σ) (σ + 1) (j₁ + j₂ - j₃ - σ + 1) (j₁ - m₁ - σ + 1) (j₂ + m₂ - σ + 1) (j₃ - j₂ + m₁ + σ + 1) (j₃ - j₁ - m₂ + σ + 1) (σ + 1 : ℝ) ((j₁ : ℝ) + j₂ - j₃ - σ + 1) ((j₁ : ℝ) - m₁ - σ + 1) ((j₂ : ℝ) + m₂ - σ + 1) ((j₃ : ℝ) - j₂ + m₁ + σ + 1) ((j₃ : ℝ) - j₁ - m₂ + σ + 1)
      (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) rfl (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring), hU]
    ac_rfl
  have t1 : term3 (j₁ - 1) j₂ j₃ m₁ m₂ σ ε = ε * (((σ + 1 : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ + 1) *
      ((j₂ : ℝ) + m₂ - σ + 1)) * (((j₁ : ℝ) + j₂ - j₃ - σ) * ((j₁ : ℝ) + j₂ - j₃ - σ + 1) *
      ((j₁ : ℝ) - m₁ - σ) * ((j₁ : ℝ) - m₁ - σ + 1))) * U := by
    unfold term3
    rw [rec3_P6_t1 (σ) (j₁ - 1 + j₂ - j₃ - σ) (j₁ - 1 - m₁ - σ) (j₂ + m₂ - σ) (j₃ - j₂ + m₁ + σ) (j₃ - (j₁ - 1) - m₂ + σ) (σ + 1) (j₁ + j₂ - j₃ - σ + 1) (j₁ - m₁ - σ + 1) (j₂ + m₂ - σ + 1) (j₃ - j₂ + m₁ + σ + 1) (j₃ - j₁ - m₂ + σ + 1) (σ + 1 : ℝ) ((j₁ : ℝ) + j₂ - j₃ - σ) ((j₁ : ℝ) - m₁ - σ) ((j₂ : ℝ) + m₂ - σ + 1) ((j₃ : ℝ) - j₂ + m₁ + σ + 1)
      (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) rfl (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring), hU]
    ac_rfl
  have t2 : term3 (j₁ + 1) j₂ j₃ m₁ m₂ σ ε = ε * (((σ + 1 : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ + 1) *
      ((j₂ : ℝ) + m₂ - σ + 1)) * (((j₃ : ℝ) - j₁ - m₂ + σ) * ((j₃ : ℝ) - j₁ - m₂ + σ + 1))) * U := by
    unfold term3
    rw [rec3_P6_t2 (σ) (j₁ + 1 + j₂ - j₃ - σ) (j₁ + 1 - m₁ - σ) (j₂ + m₂ - σ) (j₃ - j₂ + m₁ + σ) (j₃ - (j₁ + 1) - m₂ + σ) (σ + 1) (j₁ + j₂ - j₃ - σ + 1) (j₁ - m₁ - σ + 1) (j₂ + m₂ - σ + 1) (j₃ - j₂ + m₁ + σ + 1) (j₃ - j₁ - m₂ + σ + 1) (σ + 1 : ℝ) ((j₂ : ℝ) + m₂ - σ + 1) ((j₃ : ℝ) - j₂ + m₁ + σ + 1) ((j₃ : ℝ) - j₁ - m₂ + σ)
      (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) rfl (by push_cast; ring) (by push_cast; ring) (by push_cast; ring), hU]
    ac_rfl
  have tH0 : H3 j₁ j₂ j₃ m₁ m₂ σ ε = ε * (((σ + 1 : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ + 1) *
      ((j₂ : ℝ) + m₂ - σ + 1)) * ((σ : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ) *
      ((j₃ : ℝ) - j₁ - m₂ + σ + 1) * Q3 j₁ j₂ j₃ m₁ m₂ σ)) * U := by
    unfold H3
    rw [rec3_P6_tH0 (σ) (j₁ + j₂ - j₃ - σ + 1) (j₁ - m₁ - σ + 1) (j₂ + m₂ - σ) (j₃ - j₂ + m₁ + σ) (j₃ - j₁ - m₂ + σ) (σ + 1) (j₁ + j₂ - j₃ - σ + 1) (j₁ - m₁ - σ + 1) (j₂ + m₂ - σ + 1) (j₃ - j₂ + m₁ + σ + 1) (j₃ - j₁ - m₂ + σ + 1) (σ + 1 : ℝ) ((j₂ : ℝ) + m₂ - σ + 1) ((j₃ : ℝ) - j₂ + m₁ + σ + 1) ((j₃ : ℝ) - j₁ - m₂ + σ + 1)
      (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) rfl (by push_cast; ring) (by push_cast; ring) (by push_cast; ring), hU]
    ac_rfl
  have tH1 : H3 j₁ j₂ j₃ m₁ m₂ (σ + 1) (-ε) = (-ε) * (((σ + 1 : ℝ) * ((j₃ : ℝ) - j₂ + m₁ + σ + 1) *
      ((j₂ : ℝ) + m₂ - σ + 1)) * (Q3 j₁ j₂ j₃ m₁ m₂ ((σ : ℝ) + 1) *
      (((j₁ : ℝ) + j₂ - j₃ - σ + 1) * ((j₁ : ℝ) - m₁ - σ + 1) * ((j₂ : ℝ) + m₂ - σ)))) * U := by
    have e1 : (((j₃ : ℝ) - j₂ + m₁ + ((σ + 1 : ℚ) : ℝ))) = (j₃ : ℝ) - j₂ + m₁ + σ + 1 := by push_cast; ring
    unfold H3
    rw [e1]
    rw [rec3_P6_tH1 (σ + 1) (j₁ + j₂ - j₃ - (σ + 1) + 1) (j₁ - m₁ - (σ + 1) + 1) (j₂ + m₂ - (σ + 1)) (j₃ - j₂ + m₁ + (σ + 1)) (j₃ - j₁ - m₂ + (σ + 1)) (σ + 1) (j₁ + j₂ - j₃ - σ + 1) (j₁ - m₁ - σ + 1) (j₂ + m₂ - σ + 1) (j₃ - j₂ + m₁ + σ + 1) (j₃ - j₁ - m₂ + σ + 1) ((j₁ : ℝ) + j₂ - j₃ - σ + 1) ((j₁ : ℝ) - m₁ - σ + 1) ((j₂ : ℝ) + m₂ - σ)
      (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring), hU]
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
