module

public import FormalResearch.Wigner.TriRatio
public import FormalResearch.Wigner.Rec6jSum

/-!
# The `6j` recurrence of Schulten and Gordon (DLMF 34.5.11–34.5.13)

`sixJ_recurrence` is DLMF 34.5.11 for the Racah `6j` symbol `sixJ`, with `E` as in DLMF 34.5.13,
under the triangle conditions that DLMF assumes for each of the three symbols involved.  It is
obtained from the rational recurrence `racahSum6_recurrence` of the Racah sum by absorbing the
square roots of the triangle coefficients: `E(j₁+1) Δ(j₁+1) = ρ₊ Δ(j₁)` and
`E(j₁) Δ(j₁-1) = ρ₋ Δ(j₁)` with polynomial `ρ±` (`EW_plus`, `EW_minus`).
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- DLMF 34.5.13: `E(x)`, with `j₂ j₃` and `l₂ l₃` the fixed entries. -/
noncomputable def E6 (j₂ j₃ l₂ l₃ x : ℝ) : ℝ :=
  Real.sqrt ((x ^ 2 - (j₂ - j₃) ^ 2) * ((j₂ + j₃ + 1) ^ 2 - x ^ 2) *
    (x ^ 2 - (l₂ - l₃) ^ 2) * ((l₂ + l₃ + 1) ^ 2 - x ^ 2))

lemma IsNat.nonneg_real {x : ℚ} (h : IsNat x) : (0 : ℝ) ≤ (x : ℝ) := by
  obtain ⟨n, rfl⟩ := h
  push_cast; positivity

lemma IsTri.sum_nonneg {a b c : ℚ} (h : IsTri a b c) : (0 : ℝ) ≤ (a : ℝ) + b + c := by
  obtain ⟨h1, h2, h3⟩ := h
  have := h1.nonneg_real; have := h2.nonneg_real; have := h3.nonneg_real
  push_cast at *; linarith

lemma triSq_eq_zero_of_not_isTri {a b c : ℚ} (h : ¬ IsTri a b c) : triSq a b c = 0 := by
  unfold triSq
  by_cases h1 : IsNat (a + b - c)
  · by_cases h2 : IsNat (a - b + c)
    · have h3 : ¬ IsNat (-a + b + c) := fun h3 => h ⟨h1, h2, h3⟩
      simp [fq_of_not_isNat h3]
    · simp [fq_of_not_isNat h2]
  · simp [fq_of_not_isNat h1]

lemma sqrt_mul_sq_eq {E A B A' B' ρ : ℝ} (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hA' : 0 ≤ A') (hB' : 0 ≤ B') (h : E ^ 2 * (A * B) = ρ ^ 2 * (A' * B')) :
    E * (Real.sqrt A * Real.sqrt B) = ρ * (Real.sqrt A' * Real.sqrt B') := by
  have h1 : (E * (Real.sqrt A * Real.sqrt B)) ^ 2 = (ρ * (Real.sqrt A' * Real.sqrt B')) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB, Real.sq_sqrt hA',
      Real.sq_sqrt hB']
    exact h
  exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1

/-- `E(f+1) Δ(f+1) = ρ₊ Δ(f)`, where `Δ(F) = Δ(F,j₂,j₃) Δ(F,l₂,l₃)`. -/
lemma EW_plus {f j₂ j₃ l₂ l₃ : ℚ} (h1 : IsTri f j₂ j₃) (h2 : IsTri f l₂ l₃)
    (h1p : IsTri (f + 1) j₂ j₃) (h2p : IsTri (f + 1) l₂ l₃) :
    E6 j₂ j₃ l₂ l₃ ((f : ℝ) + 1) *
        (Real.sqrt (triSq (f + 1) j₂ j₃) * Real.sqrt (triSq (f + 1) l₂ l₃)) =
      (((f : ℝ) + 1 + j₂ - j₃) * ((f : ℝ) + 1 - j₂ + j₃) * ((f : ℝ) + 1 + l₂ - l₃) *
        ((f : ℝ) + 1 - l₂ + l₃)) *
        (Real.sqrt (triSq f j₂ j₃) * Real.sqrt (triSq f l₂ l₃)) := by
  have hsq1 := triSq_succ_mul h1 h1p
  have hsq2 := triSq_succ_mul h2 h2p
  have ha := h1p.1.nonneg_real
  have hb := h1p.2.1.nonneg_real
  have hu := h1p.2.2.nonneg_real
  have hc := h2p.1.nonneg_real
  have hd := h2p.2.1.nonneg_real
  have hv := h2p.2.2.nonneg_real
  have hs1 := h1.sum_nonneg
  have hs2 := h2.sum_nonneg
  push_cast at ha hb hu hc hd hv hs1 hs2
  have hA := (triSq_pos h1p).le
  have hB := (triSq_pos h2p).le
  have hA' := (triSq_pos h1).le
  have hB' := (triSq_pos h2).le
  have hP : (0 : ℝ) ≤ (((f : ℝ) + 1) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2) *
      (((j₂ : ℝ) + j₃ + 1) ^ 2 - ((f : ℝ) + 1) ^ 2) *
      (((f : ℝ) + 1) ^ 2 - ((l₂ : ℝ) - l₃) ^ 2) * (((l₂ : ℝ) + l₃ + 1) ^ 2 - ((f : ℝ) + 1) ^ 2) := by
    have e : (((f : ℝ) + 1) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2) *
      (((j₂ : ℝ) + j₃ + 1) ^ 2 - ((f : ℝ) + 1) ^ 2) *
      (((f : ℝ) + 1) ^ 2 - ((l₂ : ℝ) - l₃) ^ 2) * (((l₂ : ℝ) + l₃ + 1) ^ 2 - ((f : ℝ) + 1) ^ 2) =
      (((f : ℝ) + 1 + j₂ - j₃) * ((f : ℝ) + 1 - j₂ + j₃)) *
        (((j₂ : ℝ) + j₃ - f) * ((f : ℝ) + j₂ + j₃ + 2)) *
      (((f : ℝ) + 1 + l₂ - l₃) * ((f : ℝ) + 1 - l₂ + l₃)) *
        (((l₂ : ℝ) + l₃ - f) * ((f : ℝ) + l₂ + l₃ + 2)) := by ring
    rw [e]
    have : 0 ≤ ((j₂ : ℝ) + j₃ - f) := by linarith
    have : 0 ≤ ((l₂ : ℝ) + l₃ - f) := by linarith
    positivity
  apply sqrt_mul_sq_eq (Real.sqrt_nonneg _) (by positivity) hA hB hA' hB'
  rw [Real.sq_sqrt hP]
  have e : (((f : ℝ) + 1) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2) *
      (((j₂ : ℝ) + j₃ + 1) ^ 2 - ((f : ℝ) + 1) ^ 2) *
      (((f : ℝ) + 1) ^ 2 - ((l₂ : ℝ) - l₃) ^ 2) * (((l₂ : ℝ) + l₃ + 1) ^ 2 - ((f : ℝ) + 1) ^ 2) =
      (((f : ℝ) + 1 + j₂ - j₃) * ((f : ℝ) + 1 - j₂ + j₃)) *
        (((j₂ : ℝ) + j₃ - f) * ((f : ℝ) + j₂ + j₃ + 2)) *
      (((f : ℝ) + 1 + l₂ - l₃) * ((f : ℝ) + 1 - l₂ + l₃)) *
        (((l₂ : ℝ) + l₃ - f) * ((f : ℝ) + l₂ + l₃ + 2)) := by ring
  rw [e]
  linear_combination
    (((f : ℝ) + 1 + j₂ - j₃) * ((f : ℝ) + 1 - j₂ + j₃) * ((f : ℝ) + 1 + l₂ - l₃) *
        ((f : ℝ) + 1 - l₂ + l₃) *
      (((l₂ : ℝ) + l₃ - f) * ((f : ℝ) + l₂ + l₃ + 2) * triSq (f + 1) l₂ l₃)) * hsq1 +
    (((f : ℝ) + 1 + j₂ - j₃) * ((f : ℝ) + 1 - j₂ + j₃) * ((f : ℝ) + 1 + l₂ - l₃) *
        ((f : ℝ) + 1 - l₂ + l₃) *
      (((f : ℝ) + 1 + j₂ - j₃) * ((f : ℝ) + 1 - j₂ + j₃) * triSq f j₂ j₃)) * hsq2

/-- `E(f) Δ(f-1) = ρ₋ Δ(f)`. -/
lemma EW_minus {f j₂ j₃ l₂ l₃ : ℚ} (h1 : IsTri f j₂ j₃) (h2 : IsTri f l₂ l₃)
    (h1m : IsTri (f - 1) j₂ j₃) (h2m : IsTri (f - 1) l₂ l₃) :
    E6 j₂ j₃ l₂ l₃ (f : ℝ) *
        (Real.sqrt (triSq (f - 1) j₂ j₃) * Real.sqrt (triSq (f - 1) l₂ l₃)) =
      (((j₂ : ℝ) + j₃ + 1 - f) * ((j₂ : ℝ) + j₃ + 1 + f) * ((l₂ : ℝ) + l₃ + 1 - f) *
        ((l₂ : ℝ) + l₃ + 1 + f)) *
        (Real.sqrt (triSq f j₂ j₃) * Real.sqrt (triSq f l₂ l₃)) := by
  have hsq1 := triSq_pred_mul h1 h1m
  have hsq2 := triSq_pred_mul h2 h2m
  have hp := h1.1.nonneg_real
  have hq := h1.2.1.nonneg_real
  have hr := h1m.2.2.nonneg_real
  have hp' := h2.1.nonneg_real
  have hq' := h2.2.1.nonneg_real
  have hr' := h2m.2.2.nonneg_real
  have hs1 := h1.sum_nonneg
  have hs2 := h2.sum_nonneg
  push_cast at hp hq hr hp' hq' hr' hs1 hs2
  have hA := (triSq_pos h1m).le
  have hB := (triSq_pos h2m).le
  have hA' := (triSq_pos h1).le
  have hB' := (triSq_pos h2).le
  have e : ((f : ℝ) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2) * (((j₂ : ℝ) + j₃ + 1) ^ 2 - (f : ℝ) ^ 2) *
      ((f : ℝ) ^ 2 - ((l₂ : ℝ) - l₃) ^ 2) * (((l₂ : ℝ) + l₃ + 1) ^ 2 - (f : ℝ) ^ 2) =
      (((f : ℝ) + j₂ - j₃) * ((f : ℝ) - j₂ + j₃)) *
        (((j₂ : ℝ) + j₃ + 1 - f) * ((j₂ : ℝ) + j₃ + 1 + f)) *
      (((f : ℝ) + l₂ - l₃) * ((f : ℝ) - l₂ + l₃)) *
        (((l₂ : ℝ) + l₃ + 1 - f) * ((l₂ : ℝ) + l₃ + 1 + f)) := by ring
  have hP : (0 : ℝ) ≤ ((f : ℝ) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2) * (((j₂ : ℝ) + j₃ + 1) ^ 2 - (f : ℝ) ^ 2) *
      ((f : ℝ) ^ 2 - ((l₂ : ℝ) - l₃) ^ 2) * (((l₂ : ℝ) + l₃ + 1) ^ 2 - (f : ℝ) ^ 2) := by
    rw [e]
    have : 0 ≤ ((j₂ : ℝ) + j₃ + 1 - f) := by linarith
    have : 0 ≤ ((l₂ : ℝ) + l₃ + 1 - f) := by linarith
    have : 0 ≤ ((j₂ : ℝ) + j₃ + 1 + f) := by linarith
    have : 0 ≤ ((l₂ : ℝ) + l₃ + 1 + f) := by linarith
    positivity
  have hρ : 0 ≤ (((j₂ : ℝ) + j₃ + 1 - f) * ((j₂ : ℝ) + j₃ + 1 + f) * ((l₂ : ℝ) + l₃ + 1 - f) *
        ((l₂ : ℝ) + l₃ + 1 + f)) := by
    have : 0 ≤ ((j₂ : ℝ) + j₃ + 1 - f) := by linarith
    have : 0 ≤ ((l₂ : ℝ) + l₃ + 1 - f) := by linarith
    have : 0 ≤ ((j₂ : ℝ) + j₃ + 1 + f) := by linarith
    have : 0 ≤ ((l₂ : ℝ) + l₃ + 1 + f) := by linarith
    positivity
  apply sqrt_mul_sq_eq (Real.sqrt_nonneg _) hρ hA hB hA' hB'
  rw [Real.sq_sqrt hP, e]
  linear_combination
    (((j₂ : ℝ) + j₃ + 1 - f) * ((j₂ : ℝ) + j₃ + 1 + f) * ((l₂ : ℝ) + l₃ + 1 - f) *
        ((l₂ : ℝ) + l₃ + 1 + f) *
      (((f : ℝ) + l₂ - l₃) * ((f : ℝ) - l₂ + l₃) * triSq (f - 1) l₂ l₃)) * hsq1 +
    (((j₂ : ℝ) + j₃ + 1 - f) * ((j₂ : ℝ) + j₃ + 1 + f) * ((l₂ : ℝ) + l₃ + 1 - f) *
        ((l₂ : ℝ) + l₃ + 1 + f) *
      (((j₂ : ℝ) + j₃ + 1 - f) * ((j₂ : ℝ) + j₃ + 1 + f) * triSq f j₂ j₃)) * hsq2

lemma sixJ_factor (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    sixJ j₁ j₂ j₃ l₁ l₂ l₃ =
      (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (triSq j₁ l₂ l₃)) *
        (Real.sqrt (triSq l₁ j₂ l₃) * Real.sqrt (triSq l₁ l₂ j₃)) *
        racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ := by
  unfold sixJ; ring

/-- **DLMF 34.5.11** (Schulten–Gordon recurrence for the `6j` symbol in its first entry), with
`E` as in DLMF 34.5.13, under the triangle conditions for the three symbols involved. -/
theorem sixJ_recurrence (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ)
    (h1 : IsTri j₁ j₂ j₃) (h2 : IsTri j₁ l₂ l₃)
    (h1p : IsTri (j₁ + 1) j₂ j₃) (h2p : IsTri (j₁ + 1) l₂ l₃)
    (h1m : IsTri (j₁ - 1) j₂ j₃) (h2m : IsTri (j₁ - 1) l₂ l₃) :
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
    have e1 := EW_plus h1 h2 h1p h2p
    have e2 := EW_minus h1 h2 h1m h2m
    rw [sixJ_factor j₁ j₂ j₃ l₁ l₂ l₃, sixJ_factor (j₁ + 1) j₂ j₃ l₁ l₂ l₃,
      sixJ_factor (j₁ - 1) j₂ j₃ l₁ l₂ l₃]
    linear_combination
      ((Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (triSq j₁ l₂ l₃)) *
        (Real.sqrt (triSq l₁ j₂ l₃) * Real.sqrt (triSq l₁ l₂ j₃))) * hrec
      - ((j₁ : ℝ) * ((Real.sqrt (triSq l₁ j₂ l₃) * Real.sqrt (triSq l₁ l₂ j₃))) *
          racahSum6 (j₁ + 1) j₂ j₃ l₁ l₂ l₃) * e1
      - (((j₁ : ℝ) + 1) * ((Real.sqrt (triSq l₁ j₂ l₃) * Real.sqrt (triSq l₁ l₂ j₃))) *
          racahSum6 (j₁ - 1) j₂ j₃ l₁ l₂ l₃) * e2
  · have hz : ∀ F : ℚ, sixJ F j₂ j₃ l₁ l₂ l₃ = 0 := by
      intro F
      rw [sixJ_factor]
      rcases not_and_or.mp hCc with h | h
      · rw [triSq_eq_zero_of_not_isTri h]; simp
      · rw [triSq_eq_zero_of_not_isTri h]; simp
    simp [hz]

/-- info: 'FormalResearch.Wigner.sixJ_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_recurrence

end FormalResearch.Wigner
