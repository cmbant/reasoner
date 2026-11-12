module

public import FormalResearch.Wigner.Defs

/-!
# Special values of the `6j` symbol

`sixJ_zero_left` is DLMF 34.5.1: `{j₁ j₂ j₃; 0 j₃ j₂} = (-1)^{j₁+j₂+j₃} / √((2j₂+1)(2j₃+1))`.
Besides being a standard value, it checks the normalisation and sign conventions of `sixJ`.
-/

@[expose] public section

namespace FormalResearch.Wigner

lemma triSq_of_nat {a b c : ℚ} {p q r : ℕ} (h1 : a + b - c = p) (h2 : a - b + c = q)
    (h3 : -a + b + c = r) :
    triSq a b c = (p.factorial : ℝ) * q.factorial * r.factorial / ((p + q + r + 1).factorial : ℝ) := by
  unfold triSq
  have hs : a + b + c + 1 = ((p + q + r + 1 : ℕ) : ℚ) := by push_cast; linarith
  rw [h1, h2, h3, hs, fq_natCast, fq_natCast, fq_natCast, ifa_natCast]
  rw [div_eq_mul_inv]

/-- **DLMF 34.5.1.** -/
theorem sixJ_zero_left {j₁ j₂ j₃ : ℚ} (h : IsTri j₁ j₂ j₃) (N : ℕ) (hN : (N : ℚ) = j₁ + j₂ + j₃) :
    sixJ j₁ j₂ j₃ 0 j₃ j₂ =
      (-1 : ℝ) ^ N / Real.sqrt ((2 * (j₂ : ℝ) + 1) * (2 * (j₃ : ℝ) + 1)) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := h
  have hNabc : N = a + b + c := by
    have : (N : ℚ) = ((a + b + c : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have hT : triSq j₁ j₂ j₃ = (a.factorial : ℝ) * b.factorial * c.factorial / ((N + 1).factorial : ℝ) := by
    rw [triSq_of_nat ha hb hc, hNabc]
  have hT' : triSq j₁ j₃ j₂ = (a.factorial : ℝ) * b.factorial * c.factorial / ((N + 1).factorial : ℝ) := by
    rw [triSq_of_nat (p := b) (q := a) (r := c) (by linarith) (by linarith) (by linarith), hNabc]
    rw [show b + a + c + 1 = a + b + c + 1 by ring]
    ring
  have h2 : triSq 0 j₂ j₂ = ((a + c + 1 : ℕ) : ℝ)⁻¹ := by
    rw [triSq_of_nat (p := 0) (q := 0) (r := a + c) (by simp) (by simp) (by push_cast; linarith)]
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, Nat.factorial_succ]
    push_cast
    have : ((a + c).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have h3 : triSq 0 j₃ j₃ = ((b + c + 1 : ℕ) : ℝ)⁻¹ := by
    rw [triSq_of_nat (p := 0) (q := 0) (r := b + c) (by simp) (by simp) (by push_cast; linarith)]
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, Nat.factorial_succ]
    push_cast
    have : ((b + c).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  -- the Racah sum has the single term `t = N`
  have hsum : racahSum6 j₁ j₂ j₃ 0 j₃ j₂ =
      (-1 : ℝ) ^ N * ((N + 1).factorial : ℝ) *
        (((a.factorial : ℝ) * b.factorial * c.factorial)⁻¹) := by
    unfold racahSum6
    rw [finsum_eq_single _ N]
    · unfold term6
      have hv : (![(N : ℚ) - j₁ - j₂ - j₃, (N : ℚ) - j₁ - j₃ - j₂, (N : ℚ) - 0 - j₂ - j₂,
          (N : ℚ) - 0 - j₃ - j₃, j₁ + j₂ + 0 + j₃ - N, j₂ + j₃ + j₃ + j₂ - N,
          j₃ + j₁ + j₂ + 0 - N] : Fin 7 → ℚ) =
          ![((0 : ℕ) : ℚ), ((0 : ℕ) : ℚ), (b : ℚ), (a : ℚ), ((0 : ℕ) : ℚ), (c : ℚ), ((0 : ℕ) : ℚ)] := by
        funext i
        fin_cases i <;> simp <;> linarith
      rw [hv]
      unfold P7
      rw [Fin.prod_univ_seven]
      have i0 : ifa 0 = 1 := by simpa using ifa_natCast 0
      simp [ifa_natCast, i0]
      left; ring
    · intro t ht
      unfold term6 P7
      rcases lt_or_gt_of_ne ht with hlt | hgt
      · have : ifa ((t : ℚ) - j₁ - j₂ - j₃) = 0 := by
          apply ifa_eq_zero_of_neg
          have : (t : ℚ) + 1 ≤ N := by exact_mod_cast hlt
          linarith
        rw [Fin.prod_univ_seven]
        simp [this]
      · have : ifa (j₁ + j₂ + j₃ - (t : ℚ)) = 0 := by
          apply ifa_eq_zero_of_neg
          have : (N : ℚ) + 1 ≤ t := by exact_mod_cast hgt
          linarith
        rw [Fin.prod_univ_seven]
        simp [this]
  unfold sixJ
  rw [hsum, hT, hT', h2, h3]
  have e2 : (2 * (j₂ : ℝ) + 1) = ((a + c + 1 : ℕ) : ℝ) := by
    have : (2 * j₂ + 1 : ℚ) = ((a + c + 1 : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have e3 : (2 * (j₃ : ℝ) + 1) = ((b + c + 1 : ℕ) : ℝ) := by
    have : (2 * j₃ + 1 : ℚ) = ((b + c + 1 : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have hT0 : 0 ≤ (a.factorial : ℝ) * b.factorial * c.factorial / ((N + 1).factorial : ℝ) := by
    positivity
  have hX : (0 : ℝ) < ((a + c + 1 : ℕ) : ℝ) := by positivity
  have hY : (0 : ℝ) < ((b + c + 1 : ℕ) : ℝ) := by positivity
  rw [Real.sqrt_inv, Real.sqrt_inv, Real.mul_self_sqrt hT0, e2, e3,
    Real.sqrt_mul hX.le]
  have h1 : ((a.factorial : ℝ)) ≠ 0 := by positivity
  have h2' : ((b.factorial : ℝ)) ≠ 0 := by positivity
  have h3' : ((c.factorial : ℝ)) ≠ 0 := by positivity
  have h4 : (((N + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h5 : Real.sqrt ((a + c + 1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hX).ne'
  have h6 : Real.sqrt ((b + c + 1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hY).ne'
  field_simp

/-- info: 'FormalResearch.Wigner.sixJ_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_zero_left

end FormalResearch.Wigner
