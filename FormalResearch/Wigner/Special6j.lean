module

public import FormalResearch.Wigner.SpecialValues
public import FormalResearch.Wigner.Stretched3j

/-!
# Special values of the `6j` symbol (DLMF 34.5.2)

`sixJ_half_a`: `{j₁ j₂ j₃; 1/2 j₃-1/2 j₂+1/2}`.  Racah's sum has the single term `t = j₁+j₂+j₃`.
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- **DLMF 34.5.2.**  `{j₁ j₂ j₃; 1/2, j₃-1/2, j₂+1/2} = (-1)^J
[(j₁+j₃-j₂)(j₁+j₂-j₃+1) / ((2j₂+1)(2j₂+2)(2j₃)(2j₃+1))]^(1/2)`, `J = j₁+j₂+j₃`,
under the triangle conditions of the two triads `(j₁ j₂ j₃)` and `(j₁, j₃-1/2, j₂+1/2)`
(these force `2j₃ ≥ 1`). -/
theorem sixJ_half_a {j₁ j₂ j₃ : ℚ} (h : IsTri j₁ j₂ j₃) (h' : IsTri j₁ (j₃ - 1 / 2) (j₂ + 1 / 2))
    (N : ℕ) (hN : (N : ℚ) = j₁ + j₂ + j₃) :
    sixJ j₁ j₂ j₃ (1 / 2) (j₃ - 1 / 2) (j₂ + 1 / 2) =
      (-1 : ℝ) ^ N * Real.sqrt (((j₁ + j₃ - j₂) * (j₁ + j₂ - j₃ + 1)) /
        ((2 * (j₂ : ℝ) + 1) * (2 * j₂ + 2) * (2 * j₃) * (2 * j₃ + 1))) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := h
  obtain ⟨⟨s, hs⟩, -, -⟩ := h'
  have hqs : q = s + 1 := by
    have : (q : ℚ) = ((s + 1 : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  subst hqs
  have hNp : N = p + s + 1 + r := by
    have : (N : ℚ) = ((p + s + 1 + r : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have h2j2 : 2 * j₂ = ((p + r : ℕ) : ℚ) := by push_cast; linarith
  have h2j3 : 2 * j₃ = ((s + 1 + r : ℕ) : ℚ) := by push_cast; linarith
  -- the four triangle coefficients
  have T1 : triSq j₁ j₂ j₃ =
      (p.factorial : ℝ) * (s + 1).factorial * r.factorial / ((N + 1).factorial : ℝ) := by
    rw [triSq_of_nat hp hq hr, hNp, show p + (s + 1) + r + 1 = p + s + 1 + r + 1 by ring]
  have T2 : triSq j₁ (j₃ - 1 / 2) (j₂ + 1 / 2) =
      (s.factorial : ℝ) * (p + 1).factorial * r.factorial / ((N + 1).factorial : ℝ) := by
    rw [triSq_of_nat (p := s) (q := p + 1) (r := r) (by linarith) (by push_cast; linarith)
      (by linarith), hNp, show s + (p + 1) + r + 1 = p + s + 1 + r + 1 by ring]
  have T3 : triSq (1 / 2) j₂ (j₂ + 1 / 2) =
      (((p + r : ℕ) : ℝ) + 1)⁻¹ * (((p + r : ℕ) : ℝ) + 2)⁻¹ := by
    rw [triSq_of_nat (p := 0) (q := 1) (r := p + r) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith)]
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, Nat.factorial_one]
    rw [show 1 + (p + r) + 1 = (p + r) + 2 by ring, Nat.factorial_succ, Nat.factorial_succ]
    have : ((p + r).factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have T4 : triSq (1 / 2) (j₃ - 1 / 2) j₃ =
      (((s + 1 + r : ℕ) : ℝ))⁻¹ * (((s + 1 + r : ℕ) : ℝ) + 1)⁻¹ := by
    rw [triSq_of_nat (p := 0) (q := 1) (r := s + r) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith)]
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, Nat.factorial_one]
    rw [show 1 + (s + r) + 1 = (s + r) + 2 by ring, Nat.factorial_succ, Nat.factorial_succ]
    have : ((s + r).factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    try ring
  -- the Racah sum has the single term `t = N`
  have hsum : racahSum6 j₁ j₂ j₃ (1 / 2) (j₃ - 1 / 2) (j₂ + 1 / 2) =
      (-1 : ℝ) ^ N * ((N + 1).factorial : ℝ) *
        (((s.factorial : ℝ) * p.factorial * r.factorial)⁻¹) := by
    unfold racahSum6
    rw [finsum_eq_single _ N]
    · unfold term6
      rw [P7_vec]
      have e0 : (N : ℚ) - j₁ - j₂ - j₃ = 0 := by linarith
      have e1 : (N : ℚ) - j₁ - (j₃ - 1 / 2) - (j₂ + 1 / 2) = 0 := by linarith
      have e2 : (N : ℚ) - 1 / 2 - j₂ - (j₂ + 1 / 2) = (s : ℚ) := by
        have : (N : ℚ) = ((p + s + 1 + r : ℕ) : ℚ) := by exact_mod_cast hNp
        push_cast at this h2j2; linarith
      have e3 : (N : ℚ) - 1 / 2 - (j₃ - 1 / 2) - j₃ = (p : ℚ) := by
        have : (N : ℚ) = ((p + s + 1 + r : ℕ) : ℚ) := by exact_mod_cast hNp
        push_cast at this h2j3; linarith
      have e4 : j₁ + j₂ + 1 / 2 + (j₃ - 1 / 2) - (N : ℚ) = 0 := by linarith
      have e5 : j₂ + j₃ + (j₃ - 1 / 2) + (j₂ + 1 / 2) - (N : ℚ) = (r : ℚ) := by linarith
      have e6 : j₃ + j₁ + (j₂ + 1 / 2) + 1 / 2 - (N : ℚ) = 1 := by linarith
      rw [e0, e1, e2, e3, e4, e5, e6, ifa_zero, ifa_one, ifa_natCast, ifa_natCast, ifa_natCast]
      simp only [one_mul, mul_one]
      field_simp
    · intro t ht
      unfold term6
      rw [P7_vec]
      rcases lt_or_gt_of_ne ht with hlt | hgt
      · have : ifa ((t : ℚ) - j₁ - j₂ - j₃) = 0 := by
          apply ifa_eq_zero_of_neg
          have : (t : ℚ) + 1 ≤ N := by exact_mod_cast hlt
          linarith
        rw [this]; simp
      · have : ifa (j₁ + j₂ + 1 / 2 + (j₃ - 1 / 2) - (t : ℚ)) = 0 := by
          apply ifa_eq_zero_of_neg
          have : (N : ℚ) + 1 ≤ t := by exact_mod_cast hgt
          linarith
        rw [this]; simp
  -- the real-valued side
  have d1 : ((j₁ : ℝ) + j₃ - j₂) = ((s + 1 : ℕ) : ℝ) := by
    have : j₁ + j₃ - j₂ = ((s + 1 : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have d2 : ((j₁ : ℝ) + j₂ - j₃ + 1) = ((p + 1 : ℕ) : ℝ) := by
    have : j₁ + j₂ - j₃ + 1 = ((p + 1 : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have d3 : (2 * (j₂ : ℝ) + 1) = ((p + r : ℕ) : ℝ) + 1 := by
    have : 2 * j₂ + 1 = ((p + r : ℕ) : ℚ) + 1 := by rw [h2j2]
    exact_mod_cast this
  have d4 : (2 * (j₂ : ℝ) + 2) = ((p + r : ℕ) : ℝ) + 2 := by
    have : 2 * j₂ + 2 = ((p + r : ℕ) : ℚ) + 2 := by rw [h2j2]
    exact_mod_cast this
  have d5 : (2 * (j₃ : ℝ)) = ((s + 1 + r : ℕ) : ℝ) := by
    exact_mod_cast h2j3
  have d6 : (2 * (j₃ : ℝ) + 1) = ((s + 1 + r : ℕ) : ℝ) + 1 := by rw [d5]
  unfold sixJ
  rw [hsum, T1, T2, T3, T4, d1, d2, d3, d4, d6, d5]
  have hF : ((N + 1).factorial : ℝ) ≠ 0 := by positivity
  have h1 : (p.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (s.factorial : ℝ) ≠ 0 := by positivity
  have h3 : (r.factorial : ℝ) ≠ 0 := by positivity
  have hX : (p.factorial : ℝ) * (s + 1).factorial * r.factorial / ((N + 1).factorial : ℝ) *
      ((s.factorial : ℝ) * (p + 1).factorial * r.factorial / ((N + 1).factorial : ℝ)) *
      ((((p + r : ℕ) : ℝ) + 1)⁻¹ * (((p + r : ℕ) : ℝ) + 2)⁻¹) *
      (((s + 1 + r : ℕ) : ℝ)⁻¹ * (((s + 1 + r : ℕ) : ℝ) + 1)⁻¹) =
      (((s + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ) /
        ((((p + r : ℕ) : ℝ) + 1) * (((p + r : ℕ) : ℝ) + 2) * ((s + 1 + r : ℕ) : ℝ) *
          (((s + 1 + r : ℕ) : ℝ) + 1))) *
        ((p.factorial : ℝ) * s.factorial * r.factorial / ((N + 1).factorial : ℝ)) ^ 2 := by
    rw [Nat.factorial_succ s, Nat.factorial_succ p]
    push_cast
    have a1 : ((p : ℝ) + r + 1) ≠ 0 := by positivity
    have a2 : ((p : ℝ) + r + 2) ≠ 0 := by positivity
    have a3 : ((s : ℝ) + 1 + r) ≠ 0 := by positivity
    have a4 : ((s : ℝ) + 1 + r + 1) ≠ 0 := by positivity
    field_simp
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
    ← Real.sqrt_mul (by positivity), hX, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]
  field_simp


/-- info: 'FormalResearch.Wigner.sixJ_half_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_half_a

end FormalResearch.Wigner
