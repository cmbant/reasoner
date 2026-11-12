module

public import FormalResearch.Wigner.Basic

/-!
# Racah's formulas for the Wigner `6j` and `3j` symbols

Spins are rational numbers; admissibility (integrality and triangle inequalities) is encoded by
the zero extension of the inverse factorial, so the symbols vanish outside their natural domain.

* `triSq a b c = (a+b-c)!(a-b+c)!(-a+b+c)!/(a+b+c+1)!`, the square of Racah's `Δ(abc)`
  (DLMF 34.2.5);
* `racahSum6` is the single sum of DLMF 34.4.2 without the four `Δ` prefactors, and
  `sixJ` the `6j` symbol of DLMF 34.4.2 itself.

The sum is taken over `t : ℕ`; for nonnegative spins every term with `t < 0` vanishes, so this is
the same finite sum as in the textbook.
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- `x!` for a rational `x` that is a natural number, and `0` otherwise. -/
noncomputable def fq (x : ℚ) : ℝ :=
  if x.den = 1 ∧ 0 ≤ x.num then ((x.num.toNat.factorial : ℕ) : ℝ) else 0

/-- `x` is a natural number. -/
def IsNat (x : ℚ) : Prop := ∃ n : ℕ, x = n

/-- `(a, b, c)` satisfies the triangle conditions with integral sum: the three numbers
`a+b-c`, `a-b+c`, `-a+b+c` are natural numbers. -/
def IsTri (a b c : ℚ) : Prop := IsNat (a + b - c) ∧ IsNat (a - b + c) ∧ IsNat (-a + b + c)

lemma fq_natCast (n : ℕ) : fq (n : ℚ) = (n.factorial : ℝ) := by
  simp [fq]

lemma fq_of_isNat {x : ℚ} (h : IsNat x) : ∃ n : ℕ, x = n ∧ fq x = (n.factorial : ℝ) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n, rfl, fq_natCast n⟩

lemma fq_pos_of_isNat {x : ℚ} (h : IsNat x) : 0 < fq x := by
  obtain ⟨n, rfl, h2⟩ := fq_of_isNat h
  rw [h2]; positivity

lemma fq_of_not_isNat {x : ℚ} (h : ¬ IsNat x) : fq x = 0 := by
  unfold fq
  rw [if_neg]
  rintro ⟨h1, h2⟩
  apply h
  refine ⟨x.num.toNat, ?_⟩
  have hx : (x.num : ℚ) = x := (Rat.den_eq_one_iff x).mp h1
  rw [← hx]
  exact_mod_cast (Int.toNat_of_nonneg h2).symm

/-- `(n+1)! = (n+1) · n!`. -/
lemma fq_succ {x : ℚ} (h : IsNat x) : fq (x + 1) = ((x : ℝ) + 1) * fq x := by
  obtain ⟨n, rfl, h2⟩ := fq_of_isNat h
  rw [h2, show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) by push_cast; ring, fq_natCast, Nat.factorial_succ]
  push_cast; ring

/-- The square of Racah's `Δ(a b c)`. -/
noncomputable def triSq (a b c : ℚ) : ℝ :=
  fq (a + b - c) * fq (a - b + c) * fq (-a + b + c) * ifa (a + b + c + 1)

/-- The summand of Racah's `6j` sum as a function of the (rational) index `σ`, a sign `ε` and the
value `φ` of `(σ+1)!`.  The factors are `1/a!` for the arguments `σ - j₁ - j₂ - j₃`,
`σ - j₁ - l₂ - l₃`, `σ - l₁ - j₂ - l₃`, `σ - l₁ - l₂ - j₃`, `j₁ + j₂ + l₁ + l₂ - σ`,
`j₂ + j₃ + l₂ + l₃ - σ`, `j₃ + j₁ + l₃ + l₁ - σ`. -/
noncomputable def term6 (j₁ j₂ j₃ l₁ l₂ l₃ σ : ℚ) (ε φ : ℝ) : ℝ :=
  ε * φ * P7 ![σ - j₁ - j₂ - j₃, σ - j₁ - l₂ - l₃, σ - l₁ - j₂ - l₃, σ - l₁ - l₂ - j₃,
    j₁ + j₂ + l₁ + l₂ - σ, j₂ + j₃ + l₂ + l₃ - σ, j₃ + j₁ + l₃ + l₁ - σ]

/-- The sum in Racah's formula for the `6j` symbol (DLMF 34.4.2), without the `Δ` prefactors. -/
noncomputable def racahSum6 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) : ℝ :=
  ∑ᶠ t : ℕ, term6 j₁ j₂ j₃ l₁ l₂ l₃ t ((-1 : ℝ) ^ t) (((t + 1).factorial : ℕ) : ℝ)

/-- The Wigner `6j` symbol `{j₁ j₂ j₃; l₁ l₂ l₃}`, by Racah's formula (DLMF 34.4.2). -/
noncomputable def sixJ (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) : ℝ :=
  Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (triSq j₁ l₂ l₃) * Real.sqrt (triSq l₁ j₂ l₃) *
    Real.sqrt (triSq l₁ l₂ j₃) * racahSum6 j₁ j₂ j₃ l₁ l₂ l₃

lemma ifa_natCast (n : ℕ) : ifa (n : ℚ) = ((n.factorial : ℝ))⁻¹ := by
  have := ifa_intCast (n : ℤ)
  simp only [Int.cast_natCast] at this
  rw [this, invFact_natCast]

lemma triSq_pos {a b c : ℚ} (h : IsTri a b c) : 0 < triSq a b c := by
  obtain ⟨⟨n1, hn1⟩, ⟨n2, hn2⟩, ⟨n3, hn3⟩⟩ := h
  have hs : a + b + c + 1 = ((n1 + n2 + n3 + 1 : ℕ) : ℚ) := by
    push_cast; linarith
  unfold triSq
  rw [hs, ifa_natCast, hn1, hn2, hn3, fq_natCast, fq_natCast, fq_natCast]
  positivity

end FormalResearch.Wigner
