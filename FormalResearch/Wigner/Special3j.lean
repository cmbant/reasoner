module

public import FormalResearch.Wigner.ThreeJSym

/-!
# Special values of the Wigner `3j` symbol (DLMF 34.3.1, 34.3.5)
-/

@[expose] public section

namespace FormalResearch.Wigner

lemma fq_zero : fq 0 = 1 := by simpa using fq_natCast 0

/-- **DLMF 34.3.1**: `(j j 0; m -m 0) = (-1)^(j-m) / √(2j+1)`. -/
theorem threeJ_zero_right {j m : ℚ} (ha : IsNat (j + m)) (hb : IsNat (j - m)) :
    threeJ j j 0 m (-m) 0 = sgn (j - m) / Real.sqrt (2 * (j : ℝ) + 1) := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  have hj : (2 * (j : ℝ) + 1) = ((a + b + 1 : ℕ) : ℝ) := by
    have : (2 * j + 1 : ℚ) = ((a + b + 1 : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  unfold threeJ
  rw [if_pos (by ring)]
  have hS : sgn (j - j - 0) = 1 := by
    rw [show j - j - 0 = ((0 : ℤ) : ℚ) by simp, sgn_intCast]; simp
  have hT : triSq j j 0 = ((a + b + 1 : ℕ) : ℝ)⁻¹ := by
    rw [triSq_of_nat (p := a + b) (q := 0) (r := 0) (by push_cast; linarith) (by simp)
      (by simp)]
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one, add_zero]
    rw [Nat.factorial_succ]
    push_cast
    have : ((a + b).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have f1 : fq (j + m) = (a.factorial : ℝ) := by rw [ha, fq_natCast]
  have f2 : fq (j - m) = (b.factorial : ℝ) := by rw [hb, fq_natCast]
  have f3 : fq (j + -m) = (b.factorial : ℝ) := by
    rw [← sub_eq_add_neg, hb, fq_natCast]
  have f4 : fq (j - -m) = (a.factorial : ℝ) := by
    rw [sub_neg_eq_add, ha, fq_natCast]
  have f5 : fq ((0 : ℚ) + 0) = 1 := by rw [add_zero, fq_zero]
  have f6 : fq ((0 : ℚ) - 0) = 1 := by rw [sub_zero, fq_zero]
  have hsum : racahSum3 j j 0 m (-m) = (-1 : ℝ) ^ b * ((a.factorial : ℝ) * b.factorial)⁻¹ := by
    unfold racahSum3
    rw [finsum_eq_single _ b]
    · rw [term3_eq]
      rw [show j + j - 0 - (b : ℚ) = (a : ℚ) by linarith,
        show j - m - (b : ℚ) = ((0 : ℕ) : ℚ) by push_cast; linarith,
        show j + -m - (b : ℚ) = ((0 : ℕ) : ℚ) by push_cast; linarith,
        show 0 - j + m + (b : ℚ) = ((0 : ℕ) : ℚ) by push_cast; linarith,
        show 0 - j - -m + (b : ℚ) = ((0 : ℕ) : ℚ) by push_cast; linarith]
      simp only [ifa_natCast, Nat.factorial_zero, Nat.cast_one, inv_one]
      field_simp
    · intro s hs
      rw [term3_eq]
      rcases lt_or_gt_of_ne hs with h | h
      · have : ifa (0 - j + m + (s : ℚ)) = 0 := by
          apply ifa_eq_zero_of_neg
          have : (s : ℚ) + 1 ≤ b := by exact_mod_cast h
          linarith
        rw [this]; ring
      · have : ifa (j - m - (s : ℚ)) = 0 := by
          apply ifa_eq_zero_of_neg
          have : (b : ℚ) + 1 ≤ s := by exact_mod_cast h
          linarith
        rw [this]; ring
  rw [hsum, hT, f1, f2, f3, f4, f5, f6, hS, hj, hb, sgn_natCast]
  have hK : 0 ≤ ((a.factorial : ℝ) * b.factorial)⁻¹ := by positivity
  rw [show (a.factorial : ℝ) * b.factorial * b.factorial * a.factorial * 1 * 1 =
      ((a.factorial : ℝ) * b.factorial) ^ 2 by ring]
  have hA : (a.factorial : ℝ) * b.factorial ≠ 0 := by positivity
  rw [Real.sqrt_sq (by positivity), Real.sqrt_inv]
  have : (0 : ℝ) < Real.sqrt ((a + b + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  field_simp

lemma sgn_of_not_int {x : ℚ} (h : ¬ ∃ n : ℤ, x = n) : sgn x = 0 := by
  unfold sgn
  rw [dif_neg h]

/-- the other cases (a consequence of the triangle conditions; not a separate DLMF equation): `(j₁ j₂ 0; m₁ m₂ 0) = 0` for `j₁ ≠ j₂`. -/
theorem threeJ_zero_right_of_ne {j₁ j₂ : ℚ} (h : j₁ ≠ j₂) (m₁ m₂ : ℚ) :
    threeJ j₁ j₂ 0 m₁ m₂ 0 = 0 := by
  unfold threeJ
  split_ifs
  · have : triSq j₁ j₂ 0 = 0 := by
      unfold triSq
      by_cases h1 : IsNat (j₁ + j₂ - 0)
      · by_cases h2 : IsNat (j₁ - j₂ + 0)
        · by_cases h3 : IsNat (-j₁ + j₂ + 0)
          · exfalso
            obtain ⟨a, ha⟩ := h2
            obtain ⟨b, hb⟩ := h3
            apply h
            have : (a : ℚ) + b = 0 := by rw [← ha, ← hb]; ring
            have ha0 : (a : ℚ) = 0 := by
              have := (Nat.cast_nonneg a : (0 : ℚ) ≤ a)
              have := (Nat.cast_nonneg b : (0 : ℚ) ≤ b)
              linarith
            linarith
          · rw [fq_of_not_isNat h3]; ring
        · rw [fq_of_not_isNat h2]; ring
      · rw [fq_of_not_isNat h1]; ring
    rw [this]; simp
  · rfl

/-- **DLMF 34.3.5**, odd `J`: the symbol `(j₁ j₂ j₃; 0 0 0)` vanishes unless `j₁+j₂+j₃` is an even
integer.  (Consequence of `threeJ_neg`.) -/
theorem threeJ_zero_of_odd {j₁ j₂ j₃ : ℚ} (h : ¬ ∃ g : ℤ, j₁ + j₂ + j₃ = 2 * g) :
    threeJ j₁ j₂ j₃ 0 0 0 = 0 := by
  have key := threeJ_neg j₁ j₂ j₃ 0 0 0
  simp only [neg_zero] at key
  by_cases hJ : ∃ n : ℤ, j₁ + j₂ + j₃ = n
  · obtain ⟨n, hn⟩ := hJ
    rw [hn, sgn_intCast] at key
    rcases Int.even_or_odd' n with ⟨k, hk | hk⟩
    · exact absurd ⟨k, by rw [hn, hk]; push_cast; ring⟩ h
    · rw [hk, zpow_add₀ (by norm_num), zpow_mul] at key
      norm_num at key
      linarith
  · rw [sgn_of_not_int hJ] at key
    linarith

/-- info: 'FormalResearch.Wigner.threeJ_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_zero_right

/-- info: 'FormalResearch.Wigner.threeJ_zero_right_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_zero_right_of_ne

/-- info: 'FormalResearch.Wigner.threeJ_zero_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_zero_of_odd

end FormalResearch.Wigner
