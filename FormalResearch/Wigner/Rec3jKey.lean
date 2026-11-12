module

public import Mathlib

/-!
# The `j₁`-recurrence for the Racah sum of the `3j` symbol

`racahSum3 j₁ j₂ j₃ m₁ m₂` is the sum of DLMF 34.2.4 (with `m₃ = -m₁-m₂`) without its prefactors.
Its three-term recurrence in `j₁` (the rational form of DLMF 34.3.15, `racahSum3_recurrence`)
holds for **all** rational arguments.  The proof is an explicit telescoping certificate: a
polynomial `Q3` such that the combination of the three summands equals `H (s+1) - H s`
termwise (`rec3_pointwise`).  All three summands and `H` carry the common factor
`(s+1)(s+j₃-j₂+m₁+1)(j₂+m₂-s+1)` against a common reference product, which is cancelled before
the polynomial identity (`rec3_key`) is checked.
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- The polynomial in the telescoping certificate of the `3j` recurrence. -/
noncomputable def Q3 (j₁ j₂ j₃ m₁ m₂ σ : ℝ) : ℝ :=
  ((j₁ + 1)*(j₁ - j₂ - j₃ - 1)) * σ ^ 2 + (-3*j₁^3 + 2*j₁^2*j₂ + 4*j₁^2*j₃ - 2*j₁^2*m₂ - 2*j₁^2 + j₁*j₂^2 - 2*j₁*j₂*m₁ + 5*j₁*j₂ - j₁*j₃^2 + 5*j₁*j₃ - j₁*m₁ - 2*j₁*m₂ + 3*j₁ + j₂^2 - j₂*m₁ + 3*j₂ - j₃^2 - j₃*m₁ + j₃ - m₁ + 2) * σ + (2*j₁^4 - j₁^3*j₂ - 4*j₁^3*j₃ + 3*j₁^3*m₂ + 2*j₁^3 - j₁^2*j₂^2 - j₁^2*j₂*j₃ + 3*j₁^2*j₂*m₁ + j₁^2*j₂*m₂ - 5*j₁^2*j₂ + 2*j₁^2*j₃^2 - j₁^2*j₃*m₂ - 7*j₁^2*j₃ - j₁^2*m₁*m₂ + 2*j₁^2*m₁ + 6*j₁^2*m₂ - 3*j₁^2 + j₁*j₂^2*m₁ - 2*j₁*j₂^2 - j₁*j₂*j₃*m₁ - j₁*j₂*j₃ + j₁*j₂*m₁*m₂ + 4*j₁*j₂*m₁ + j₁*j₂*m₂ - 6*j₁*j₂ + 3*j₁*j₃^2 - j₁*j₃*m₁*m₂ + j₁*j₃*m₁ - j₁*j₃*m₂ - 3*j₁*j₃ - j₁*m₁*m₂ + 3*j₁*m₁ + 3*j₁*m₂ - 4*j₁ + j₂^2*m₁ - j₂^2 + 2*j₂*m₁ - 2*j₂ - j₃^2*m₁ + j₃^2 + m₁ - 1)

/-- The reduced polynomial identity behind the `3j` recurrence. -/
lemma rec3_key (s j₁ j₂ j₃ m₁ m₂ : ℝ) :
    (2 * j₁ + 1) * ((j₂ * (j₂ + 1) - j₃ * (j₃ + 1)) * m₁ - j₁ * (j₁ + 1) * (-m₁ - m₂ - m₂)) *
        ((j₃ - j₁ - m₂ + s + 1) * (j₁ + j₂ - j₃ - s + 1) * (j₁ - m₁ - s + 1))
      + (j₁ + 1) * ((j₂ + j₃ + 1 - j₁) * (j₁ + j₂ + j₃ + 1)) *
        ((j₁ + j₂ - j₃ - s) * (j₁ + j₂ - j₃ - s + 1) * (j₁ - m₁ - s) * (j₁ - m₁ - s + 1))
      + j₁ * ((j₁ + 1 + j₂ - j₃) * (j₁ + 1 - j₂ + j₃) * (j₁ + 1 + m₁) * (j₁ + 1 - m₁)) *
        ((j₃ - j₁ - m₂ + s) * (j₃ - j₁ - m₂ + s + 1))
      + Q3 j₁ j₂ j₃ m₁ m₂ (s + 1) * ((j₁ + j₂ - j₃ - s + 1) * (j₁ - m₁ - s + 1) * (j₂ + m₂ - s))
      + s * (j₃ - j₂ + m₁ + s) * (j₃ - j₁ - m₂ + s + 1) * Q3 j₁ j₂ j₃ m₁ m₂ s = 0 := by
  unfold Q3
  ring

end FormalResearch.Wigner
