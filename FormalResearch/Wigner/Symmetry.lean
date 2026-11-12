module

public import FormalResearch.Wigner.Defs

/-!
# Tetrahedral symmetries of the `6j` symbol

Column swaps `(1 2)`, `(2 3)` and the exchange of upper and lower entries in columns `1, 2` act on
the Racah sum by permuting the seven inverse factorials, and on the four `Δ` factors by permuting them.
They generate the 24-element symmetry group of the `6j` symbol.
-/

@[expose] public section

namespace FormalResearch.Wigner

lemma P7_vec (a0 a1 a2 a3 a4 a5 a6 : ℚ) :
    P7 ![a0, a1, a2, a3, a4, a5, a6] =
      ifa a0 * ifa a1 * ifa a2 * ifa a3 * ifa a4 * ifa a5 * ifa a6 := by
  unfold P7
  rw [Fin.prod_univ_seven]
  simp

lemma triSq_comm12 (a b c : ℚ) : triSq a b c = triSq b a c := by
  unfold triSq
  rw [show b + a - c = a + b - c by ring, show b - a + c = -a + b + c by ring,
    show -b + a + c = a - b + c by ring, show b + a + c + 1 = a + b + c + 1 by ring]
  ring

lemma triSq_comm23 (a b c : ℚ) : triSq a b c = triSq a c b := by
  unfold triSq
  rw [show a + c - b = a - b + c by ring, show a - c + b = a + b - c by ring,
    show -a + c + b = -a + b + c by ring, show a + c + b + 1 = a + b + c + 1 by ring]
  ring

lemma term6_swap12 (j₁ j₂ j₃ l₁ l₂ l₃ σ : ℚ) (ε φ : ℝ) :
    term6 j₂ j₁ j₃ l₂ l₁ l₃ σ ε φ = term6 j₁ j₂ j₃ l₁ l₂ l₃ σ ε φ := by
  unfold term6
  rw [P7_vec, P7_vec]
  rw [show σ - j₂ - j₁ - j₃ = σ - j₁ - j₂ - j₃ by ring,
    show σ - j₂ - l₁ - l₃ = σ - l₁ - j₂ - l₃ by ring,
    show σ - l₂ - j₁ - l₃ = σ - j₁ - l₂ - l₃ by ring,
    show j₂ + j₁ + l₂ + l₁ - σ = j₁ + j₂ + l₁ + l₂ - σ by ring,
    show j₁ + j₃ + l₁ + l₃ - σ = j₃ + j₁ + l₃ + l₁ - σ by ring,
    show j₃ + j₂ + l₃ + l₂ - σ = j₂ + j₃ + l₂ + l₃ - σ by ring]
  ring_nf

lemma term6_swap23 (j₁ j₂ j₃ l₁ l₂ l₃ σ : ℚ) (ε φ : ℝ) :
    term6 j₁ j₃ j₂ l₁ l₃ l₂ σ ε φ = term6 j₁ j₂ j₃ l₁ l₂ l₃ σ ε φ := by
  unfold term6
  rw [P7_vec, P7_vec]
  rw [show σ - j₁ - j₃ - j₂ = σ - j₁ - j₂ - j₃ by ring,
    show σ - j₁ - l₃ - l₂ = σ - j₁ - l₂ - l₃ by ring,
    show σ - l₁ - j₃ - l₂ = σ - l₁ - l₂ - j₃ by ring,
    show σ - l₁ - l₃ - j₂ = σ - l₁ - j₂ - l₃ by ring,
    show j₁ + j₃ + l₁ + l₃ - σ = j₃ + j₁ + l₃ + l₁ - σ by ring,
    show j₃ + j₂ + l₃ + l₂ - σ = j₂ + j₃ + l₂ + l₃ - σ by ring,
    show j₂ + j₁ + l₂ + l₁ - σ = j₁ + j₂ + l₁ + l₂ - σ by ring]
  ring

lemma term6_exch12 (j₁ j₂ j₃ l₁ l₂ l₃ σ : ℚ) (ε φ : ℝ) :
    term6 l₁ l₂ j₃ j₁ j₂ l₃ σ ε φ = term6 j₁ j₂ j₃ l₁ l₂ l₃ σ ε φ := by
  unfold term6
  rw [P7_vec, P7_vec]
  rw [show l₁ + l₂ + j₁ + j₂ - σ = j₁ + j₂ + l₁ + l₂ - σ by ring,
    show l₂ + j₃ + j₂ + l₃ - σ = j₂ + j₃ + l₂ + l₃ - σ by ring,
    show j₃ + l₁ + l₃ + j₁ - σ = j₃ + j₁ + l₃ + l₁ - σ by ring]
  ring

lemma racahSum6_swap12 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    racahSum6 j₂ j₁ j₃ l₂ l₁ l₃ = racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ := by
  unfold racahSum6; simp only [term6_swap12]

lemma racahSum6_swap23 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    racahSum6 j₁ j₃ j₂ l₁ l₃ l₂ = racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ := by
  unfold racahSum6; simp only [term6_swap23]

lemma racahSum6_exch12 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    racahSum6 l₁ l₂ j₃ j₁ j₂ l₃ = racahSum6 j₁ j₂ j₃ l₁ l₂ l₃ := by
  unfold racahSum6; simp only [term6_exch12]

/-- Swapping columns 1 and 2. -/
theorem sixJ_swap12 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    sixJ j₂ j₁ j₃ l₂ l₁ l₃ = sixJ j₁ j₂ j₃ l₁ l₂ l₃ := by
  unfold sixJ
  rw [racahSum6_swap12, triSq_comm12 j₂ j₁ j₃, triSq_comm12 j₂ l₁ l₃, triSq_comm12 l₂ j₁ l₃,
    triSq_comm12 l₂ l₁ j₃]
  ring

/-- Swapping columns 2 and 3. -/
theorem sixJ_swap23 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    sixJ j₁ j₃ j₂ l₁ l₃ l₂ = sixJ j₁ j₂ j₃ l₁ l₂ l₃ := by
  unfold sixJ
  rw [racahSum6_swap23, triSq_comm23 j₁ j₃ j₂, triSq_comm23 j₁ l₃ l₂, triSq_comm23 l₁ j₃ l₂,
    triSq_comm23 l₁ l₃ j₂]
  ring

/-- Exchanging upper and lower entries in columns 1 and 2. -/
theorem sixJ_exch12 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    sixJ l₁ l₂ j₃ j₁ j₂ l₃ = sixJ j₁ j₂ j₃ l₁ l₂ l₃ := by
  unfold sixJ
  rw [racahSum6_exch12]
  ring

/-- info: 'FormalResearch.Wigner.sixJ_swap12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_swap12

/-- info: 'FormalResearch.Wigner.sixJ_swap23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_swap23

/-- info: 'FormalResearch.Wigner.sixJ_exch12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_exch12

end FormalResearch.Wigner
