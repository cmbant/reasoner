module

public import FormalResearch.Wigner.SpecialValues
public import FormalResearch.Wigner.ThreeJ

/-!
# The stretched `3j` symbol

For `j₃ = j₁ + j₂` Racah's sum has the single term `σ = 0` (DLMF 34.3.6), which gives the extremal
seed used for the minimal-rank `3j` recurrence.
-/

@[expose] public section

namespace FormalResearch.Wigner

lemma P6_vec (a0 a1 a2 a3 a4 a5 : ℚ) :
    P6 ![a0, a1, a2, a3, a4, a5] = ifa a0 * ifa a1 * ifa a2 * ifa a3 * ifa a4 * ifa a5 := by
  unfold P6
  rw [Fin.prod_univ_six]
  simp

/-- **Stretched `3j` symbol** (DLMF 34.3.6): for `j₃ = j₁ + j₂`, with
`A = j₁+m₁`, `B = j₁-m₁`, `C = j₂+m₂`, `D = j₂-m₂`. -/
theorem threeJ_stretched {A B C D : ℕ} {j₁ j₂ m₁ m₂ m₃ : ℚ} (hm : m₁ + m₂ + m₃ = 0)
    (hA : j₁ + m₁ = A) (hB : j₁ - m₁ = B) (hC : j₂ + m₂ = C) (hD : j₂ - m₂ = D) :
    threeJ j₁ j₂ (j₁ + j₂) m₁ m₂ m₃ =
      sgn (j₁ - j₂ - m₃) *
        Real.sqrt (((A + B).factorial : ℝ) * ((C + D).factorial : ℝ) * ((B + D).factorial : ℝ) *
          ((A + C).factorial : ℝ) /
            (((A + B + C + D + 1).factorial : ℝ) * (A.factorial : ℝ) * B.factorial *
              C.factorial * D.factorial)) := by
  unfold threeJ
  rw [ite_eq_left hm]
  have hX : triSq j₁ j₂ (j₁ + j₂) =
      ((A + B).factorial : ℝ) * ((C + D).factorial : ℝ) / ((A + B + C + D + 1).factorial : ℝ) := by
    have := triSq_of_nat (a := j₁) (b := j₂) (c := j₁ + j₂) (p := 0) (q := A + B) (r := C + D)
      (by simp) (by push_cast; linarith) (by push_cast; linarith)
    rw [this]
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, zero_add]
    rw [show A + B + (C + D) + 1 = A + B + C + D + 1 by ring]
  have f1 : fq (j₁ + m₁) = (A.factorial : ℝ) := by rw [hA, fq_natCast]
  have f2 : fq (j₁ - m₁) = (B.factorial : ℝ) := by rw [hB, fq_natCast]
  have f3 : fq (j₂ + m₂) = (C.factorial : ℝ) := by rw [hC, fq_natCast]
  have f4 : fq (j₂ - m₂) = (D.factorial : ℝ) := by rw [hD, fq_natCast]
  have f5 : fq (j₁ + j₂ + m₃) = ((B + D).factorial : ℝ) := by
    rw [show j₁ + j₂ + m₃ = ((B + D : ℕ) : ℚ) by push_cast; linarith, fq_natCast]
  have f6 : fq (j₁ + j₂ - m₃) = ((A + C).factorial : ℝ) := by
    rw [show j₁ + j₂ - m₃ = ((A + C : ℕ) : ℚ) by push_cast; linarith, fq_natCast]
  have hsum : racahSum3 j₁ j₂ (j₁ + j₂) m₁ m₂ =
      ((B.factorial : ℝ) * C.factorial * A.factorial * D.factorial)⁻¹ := by
    unfold racahSum3
    rw [finsum_eq_single _ 0]
    · unfold term3
      rw [P6_vec]
      rw [show j₁ + j₂ - (j₁ + j₂) - ((0 : ℕ) : ℚ) = 0 by push_cast; ring,
        show j₁ - m₁ - ((0 : ℕ) : ℚ) = (B : ℚ) by push_cast; linarith,
        show j₂ + m₂ - ((0 : ℕ) : ℚ) = (C : ℚ) by push_cast; linarith,
        show j₁ + j₂ - j₂ + m₁ + ((0 : ℕ) : ℚ) = (A : ℚ) by push_cast; linarith,
        show j₁ + j₂ - j₁ - m₂ + ((0 : ℕ) : ℚ) = (D : ℚ) by push_cast; linarith]
      simp only [Nat.cast_zero, ifa_zero, ifa_natCast, pow_zero]
      field_simp
    · intro s hs
      unfold term3
      rw [P6_vec]
      have : ifa (j₁ + j₂ - (j₁ + j₂) - (s : ℚ)) = 0 := by
        apply ifa_eq_zero_of_neg
        have : (1 : ℚ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs
        linarith
      rw [this]; simp
  rw [hsum, hX, f1, f2, f3, f4, f5, f6]
  have hK : 0 ≤ ((B.factorial : ℝ) * C.factorial * A.factorial * D.factorial)⁻¹ := by positivity
  have hXn : 0 ≤ ((A + B).factorial : ℝ) * ((C + D).factorial : ℝ) / ((A + B + C + D + 1).factorial : ℝ) := by
    positivity
  have hYn : 0 ≤ (A.factorial : ℝ) * B.factorial * C.factorial * D.factorial *
      ((B + D).factorial : ℝ) * ((A + C).factorial : ℝ) := by positivity
  have hrhs : ((A + B).factorial : ℝ) * ((C + D).factorial : ℝ) * ((B + D).factorial : ℝ) *
          ((A + C).factorial : ℝ) /
            (((A + B + C + D + 1).factorial : ℝ) * (A.factorial : ℝ) * B.factorial *
              C.factorial * D.factorial) =
      (((A + B).factorial : ℝ) * ((C + D).factorial : ℝ) / ((A + B + C + D + 1).factorial : ℝ)) *
        ((A.factorial : ℝ) * B.factorial * C.factorial * D.factorial *
          ((B + D).factorial : ℝ) * ((A + C).factorial : ℝ)) *
        (((B.factorial : ℝ) * C.factorial * A.factorial * D.factorial)⁻¹) ^ 2 := by
    have h1 : ((A.factorial : ℝ)) ≠ 0 := by positivity
    have h2 : ((B.factorial : ℝ)) ≠ 0 := by positivity
    have h3 : ((C.factorial : ℝ)) ≠ 0 := by positivity
    have h4 : ((D.factorial : ℝ)) ≠ 0 := by positivity
    have h5 : (((A + B + C + D + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hrhs, Real.sqrt_mul (mul_nonneg hXn hYn), Real.sqrt_sq hK,
    Real.sqrt_mul hXn]
  ring

/-- info: 'FormalResearch.Wigner.threeJ_stretched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_stretched

end FormalResearch.Wigner
