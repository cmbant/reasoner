module

public import Mathlib

/-!
# Reduced polynomial identity behind the `6j` recurrence

`Q6` is the quadratic (in the summation index `t`) of the telescoping certificate for the
three-term recurrence of Racah's `6j` sum in the first argument `f` (DLMF 34.5.11).
`rec6_key` is the polynomial identity left after cancelling the common factor `(a₃+1)(a₄+1)` of
all five summand-like products.  It is stated with the seven linear forms
`a₁ = t-f-j₂-j₃`, `a₂ = t-f-l₂-l₃`, `a₃ = t-l₁-j₂-l₃`, `a₄ = t-l₁-l₂-j₃`,
`b₁ = f+j₂+l₁+l₂-t`, `b₂ = j₂+j₃+l₂+l₃-t`, `b₃ = j₃+f+l₃+l₁-t` as separate variables; the
spins and `t` are linear combinations of them, so the proof eliminates the spins and checks the
identity in the atoms, where it is about four times smaller.
-/

@[expose] public section

namespace FormalResearch.Wigner

set_option maxHeartbeats 2000000 in
/-- The quadratic of the telescoping certificate of the `6j` recurrence. -/
noncomputable def Q6 (f j₂ j₃ l₁ l₂ l₃ t : ℝ) : ℝ :=
  (-2*f^2*l₁ - f^2 + 2*f*j₂*l₂ + f*j₂ + 2*f*j₃*l₃ + f*j₃ - 2*f*l₁ + f*l₂ + f*l₃ + j₂*l₂ + j₂*l₃ + j₂ + j₃*l₂ + j₃*l₃ + j₃ + l₂ + l₃ + 1) * t ^ 2 + (6*f^3*l₁ + 4*f^3 + 2*f^2*j₂*j₃ + 2*f^2*j₂*l₁ - 6*f^2*j₂*l₂ - f^2*j₂ + 2*f^2*j₃*l₁ - 6*f^2*j₃*l₃ - f^2*j₃ + 2*f^2*l₁^2 + 2*f^2*l₁*l₂ + 2*f^2*l₁*l₃ + 10*f^2*l₁ + 2*f^2*l₂*l₃ - f^2*l₂ - f^2*l₃ + 4*f^2 - 2*f*j₂^2*l₂ - f*j₂^2 - 2*f*j₂*j₃*l₂ - 2*f*j₂*j₃*l₃ - 2*f*j₂*l₁*l₂ - 2*f*j₂*l₁*l₃ - 2*f*j₂*l₂^2 - 2*f*j₂*l₂*l₃ - 8*f*j₂*l₂ - 6*f*j₂*l₃ - 4*f*j₂ - 2*f*j₃^2*l₃ - f*j₃^2 - 2*f*j₃*l₁*l₂ - 2*f*j₃*l₁*l₃ - 2*f*j₃*l₂*l₃ - 6*f*j₃*l₂ - 2*f*j₃*l₃^2 - 8*f*j₃*l₃ - 4*f*j₃ + 2*f*l₁^2 + 2*f*l₁ - f*l₂^2 - 4*f*l₂ - f*l₃^2 - 4*f*l₃ - 2*f - j₂^2*l₂ - j₂^2*l₃ - j₂^2 - 2*j₂*j₃*l₂ - 2*j₂*j₃*l₃ - 2*j₂*j₃ - 2*j₂*l₁*l₂ - 2*j₂*l₁*l₃ - 2*j₂*l₁ - j₂*l₂^2 - 2*j₂*l₂*l₃ - 4*j₂*l₂ - j₂*l₃^2 - 4*j₂*l₃ - 3*j₂ - j₃^2*l₂ - j₃^2*l₃ - j₃^2 - 2*j₃*l₁*l₂ - 2*j₃*l₁*l₃ - 2*j₃*l₁ - j₃*l₂^2 - 2*j₃*l₂*l₃ - 4*j₃*l₂ - j₃*l₃^2 - 4*j₃*l₃ - 3*j₃ - 2*l₁*l₂ - 2*l₁*l₃ - 2*l₁ - l₂^2 - 2*l₂*l₃ - 3*l₂ - l₃^2 - 3*l₃ - 2) * t + (-4*f^4*l₁ - 3*f^4 - 3*f^3*j₂*j₃ - 3*f^3*j₂*l₁ + 5*f^3*j₂*l₂ - f^3*j₂ - 3*f^3*j₃*l₁ + 5*f^3*j₃*l₃ - f^3*j₃ - 3*f^3*l₁^2 - 3*f^3*l₁*l₂ - 3*f^3*l₁*l₃ - 10*f^3*l₁ - 3*f^3*l₂*l₃ - f^3*l₂ - f^3*l₃ - 5*f^3 - f^2*j₂^2*j₃ - f^2*j₂^2*l₁ + 3*f^2*j₂^2*l₂ - f^2*j₂*j₃^2 - 2*f^2*j₂*j₃*l₁ + 2*f^2*j₂*j₃*l₂ + 2*f^2*j₂*j₃*l₃ - 3*f^2*j₂*j₃ - f^2*j₂*l₁^2 + 2*f^2*j₂*l₁*l₂ + 2*f^2*j₂*l₁*l₃ - 3*f^2*j₂*l₁ + 3*f^2*j₂*l₂^2 + 2*f^2*j₂*l₂*l₃ + 9*f^2*j₂*l₂ + 6*f^2*j₂*l₃ + f^2*j₂ - f^2*j₃^2*l₁ + 3*f^2*j₃^2*l₃ - f^2*j₃*l₁^2 + 2*f^2*j₃*l₁*l₂ + 2*f^2*j₃*l₁*l₃ - 3*f^2*j₃*l₁ + 2*f^2*j₃*l₂*l₃ + 6*f^2*j₃*l₂ + 3*f^2*j₃*l₃^2 + 9*f^2*j₃*l₃ + f^2*j₃ - f^2*l₁^2*l₂ - f^2*l₁^2*l₃ - 3*f^2*l₁^2 - f^2*l₁*l₂^2 - 2*f^2*l₁*l₂*l₃ - 3*f^2*l₁*l₂ - f^2*l₁*l₃^2 - 3*f^2*l₁*l₃ - 4*f^2*l₁ - f^2*l₂^2*l₃ - f^2*l₂*l₃^2 - 3*f^2*l₂*l₃ + f^2*l₂ + f^2*l₃ + f*j₂^2*j₃*l₂ + f*j₂^2*j₃*l₃ + f*j₂^2*l₁*l₂ + f*j₂^2*l₁*l₃ + f*j₂^2*l₂^2 + f*j₂^2*l₂*l₃ + 3*f*j₂^2*l₂ + 3*f*j₂^2*l₃ + f*j₂^2 + f*j₂*j₃^2*l₂ + f*j₂*j₃^2*l₃ + 2*f*j₂*j₃*l₁*l₂ + 2*f*j₂*j₃*l₁*l₃ + f*j₂*j₃*l₂^2 + 2*f*j₂*j₃*l₂*l₃ + 6*f*j₂*j₃*l₂ + f*j₂*j₃*l₃^2 + 6*f*j₂*j₃*l₃ + 3*f*j₂*j₃ + f*j₂*l₁^2*l₂ + f*j₂*l₁^2*l₃ + f*j₂*l₁*l₂^2 + 2*f*j₂*l₁*l₂*l₃ + 6*f*j₂*l₁*l₂ + f*j₂*l₁*l₃^2 + 6*f*j₂*l₁*l₃ + 3*f*j₂*l₁ + f*j₂*l₂^2*l₃ + 3*f*j₂*l₂^2 + f*j₂*l₂*l₃^2 + 6*f*j₂*l₂*l₃ + 8*f*j₂*l₂ + 3*f*j₂*l₃^2 + 9*f*j₂*l₃ + 4*f*j₂ + f*j₃^2*l₁*l₂ + f*j₃^2*l₁*l₃ + f*j₃^2*l₂*l₃ + 3*f*j₃^2*l₂ + f*j₃^2*l₃^2 + 3*f*j₃^2*l₃ + f*j₃^2 + f*j₃*l₁^2*l₂ + f*j₃*l₁^2*l₃ + f*j₃*l₁*l₂^2 + 2*f*j₃*l₁*l₂*l₃ + 6*f*j₃*l₁*l₂ + f*j₃*l₁*l₃^2 + 6*f*j₃*l₁*l₃ + 3*f*j₃*l₁ + f*j₃*l₂^2*l₃ + 3*f*j₃*l₂^2 + f*j₃*l₂*l₃^2 + 6*f*j₃*l₂*l₃ + 9*f*j₃*l₂ + 3*f*j₃*l₃^2 + 8*f*j₃*l₃ + 4*f*j₃ + f*l₁^2 + 3*f*l₁*l₂ + 3*f*l₁*l₃ + 4*f*l₁ + f*l₂^2 + 3*f*l₂*l₃ + 4*f*l₂ + f*l₃^2 + 4*f*l₃ + 3*f + j₂^2*j₃*l₂ + j₂^2*j₃*l₃ + j₂^2*j₃ + j₂^2*l₁*l₂ + j₂^2*l₁*l₃ + j₂^2*l₁ + j₂^2*l₂*l₃ + j₂^2*l₂ + j₂^2*l₃^2 + 2*j₂^2*l₃ + j₂^2 + j₂*j₃^2*l₂ + j₂*j₃^2*l₃ + j₂*j₃^2 + 2*j₂*j₃*l₁*l₂ + 2*j₂*j₃*l₁*l₃ + 2*j₂*j₃*l₁ + j₂*j₃*l₂^2 + 2*j₂*j₃*l₂*l₃ + 4*j₂*j₃*l₂ + j₂*j₃*l₃^2 + 4*j₂*j₃*l₃ + 3*j₂*j₃ + j₂*l₁^2*l₂ + j₂*l₁^2*l₃ + j₂*l₁^2 + j₂*l₁*l₂^2 + 2*j₂*l₁*l₂*l₃ + 4*j₂*l₁*l₂ + j₂*l₁*l₃^2 + 4*j₂*l₁*l₃ + 3*j₂*l₁ + j₂*l₂^2*l₃ + j₂*l₂^2 + j₂*l₂*l₃^2 + 4*j₂*l₂*l₃ + 3*j₂*l₂ + 2*j₂*l₃^2 + 4*j₂*l₃ + 2*j₂ + j₃^2*l₁*l₂ + j₃^2*l₁*l₃ + j₃^2*l₁ + j₃^2*l₂^2 + j₃^2*l₂*l₃ + 2*j₃^2*l₂ + j₃^2*l₃ + j₃^2 + j₃*l₁^2*l₂ + j₃*l₁^2*l₃ + j₃*l₁^2 + j₃*l₁*l₂^2 + 2*j₃*l₁*l₂*l₃ + 4*j₃*l₁*l₂ + j₃*l₁*l₃^2 + 4*j₃*l₁*l₃ + 3*j₃*l₁ + j₃*l₂^2*l₃ + 2*j₃*l₂^2 + j₃*l₂*l₃^2 + 4*j₃*l₂*l₃ + 4*j₃*l₂ + j₃*l₃^2 + 3*j₃*l₃ + 2*j₃ + l₁^2*l₂ + l₁^2*l₃ + l₁^2 + l₁*l₂^2 + 2*l₁*l₂*l₃ + 3*l₁*l₂ + l₁*l₃^2 + 3*l₁*l₃ + 2*l₁ + l₂^2*l₃ + l₂^2 + l₂*l₃^2 + 3*l₂*l₃ + 2*l₂ + l₃^2 + 2*l₃ + 1)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The reduced polynomial identity behind the `6j` recurrence. -/
lemma rec6_key (t f j₂ j₃ l₁ l₂ l₃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ : ℝ)
    (ha₁ : a₁ = t - f - j₂ - j₃) (ha₂ : a₂ = t - f - l₂ - l₃) (ha₃ : a₃ = t - l₁ - j₂ - l₃)
    (ha₄ : a₄ = t - l₁ - l₂ - j₃) (hb₁ : b₁ = f + j₂ + l₁ + l₂ - t)
    (hb₂ : b₂ = j₂ + j₃ + l₂ + l₃ - t) (hb₃ : b₃ = j₃ + f + l₃ + l₁ - t) :
    (2 * f + 1) *
          (((j₃ * (j₃ + 1) + j₂ * (j₂ + 1) - f * (f + 1)) *
              (l₃ * (l₃ + 1) + l₂ * (l₂ + 1) - f * (f + 1))) -
            2 * (j₃ * (j₃ + 1) * (l₃ * (l₃ + 1)) + j₂ * (j₂ + 1) * (l₂ * (l₂ + 1)) -
              f * (f + 1) * (l₁ * (l₁ + 1)))) *
        ((a₁ + 1) * (a₂ + 1) * (b₁ + 1) * (b₃ + 1))
      - f * ((f + 1 + j₂ - j₃) * (f + 1 - j₂ + j₃) * (f + 1 + l₂ - l₃) * (f + 1 - l₂ + l₃)) *
        (a₁ * (a₁ + 1) * a₂ * (a₂ + 1))
      - (f + 1) * ((j₂ + j₃ + 1 - f) * (j₂ + j₃ + 1 + f) * (l₂ + l₃ + 1 - f) * (l₂ + l₃ + 1 + f)) *
        (b₁ * (b₁ + 1) * b₃ * (b₃ + 1))
      + (t + 2) * Q6 f j₂ j₃ l₁ l₂ l₃ (t + 1) * (b₂ * (b₁ + 1) * (b₃ + 1))
      + a₃ * a₄ * ((a₁ + 1) * (a₂ + 1)) * Q6 f j₂ j₃ l₁ l₂ l₃ t = 0 := by
  have hf : f = (a₃ + a₄ + b₁ + b₃) / 2 := by linarith
  have hj₂ : j₂ = (a₂ + a₄ + b₁ + b₂) / 2 := by linarith
  have hj₃ : j₃ = (a₂ + a₃ + b₂ + b₃) / 2 := by linarith
  have hl₁ : l₁ = (a₁ + a₂ + b₁ + b₃) / 2 := by linarith
  have hl₂ : l₂ = (a₁ + a₃ + b₁ + b₂) / 2 := by linarith
  have hl₃ : l₃ = (a₁ + a₄ + b₂ + b₃) / 2 := by linarith
  have ht : t = a₁ + a₂ + a₃ + a₄ + b₁ + b₂ + b₃ := by linarith
  unfold Q6
  clear ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃
  subst hf hj₂ hj₃ hl₁ hl₂ hl₃
  subst ht
  ring

end FormalResearch.Wigner
