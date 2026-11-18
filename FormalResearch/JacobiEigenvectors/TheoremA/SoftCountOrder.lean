module

public import Mathlib

/-!
# Paper J, Layer 2 (L2.C7): the order argument of Step 6 ("the `k`-th from the top is the one in window `k`")

Source: app_thmA, Step 6, item *Order*.  A purely combinatorial lemma on a strictly decreasing eigenvalue list `X_0 > ... > X_N`
(indices `Fin (N+1)`, the index order is the order of decreasing energy) with a window label.

Proved here (axiom-pinned):
* `order_label`: let `inR` pick out the indices in the range, `lab` be a window label which is monotone along the index
  (larger energy, smaller label), injective on the range (at most one eigenvalue per window) and onto every window
  below the label of `i` (existence of an eigenvalue in each such window); if every index above `i` lies in the range, then `lab i = i`
  (the eigenvalues above `i` are exactly one in each window `0, ..., lab i - 1`, so `i` is the number of windows below).
* `order_label_real`: the same for a strictly antitone `X : Fin (N+1) -> R`, a real range predicate and a real-variable label,
  in the form used by the counting argument (`TheoremA/SoftCount.lean`).

Differences from the paper: the paper's "no eigenvalue lies above window 0" is not a separate hypothesis: windows are indexed by
`k : N`, so a label exists for every eigenvalue of the range (`lab` takes values in `N`).
-/

@[expose] public section

namespace FormalResearch.JacobiEigenvectors.TheoremA

theorem order_label {n : ℕ} (inR : Fin (n + 1) → Prop) (lab : Fin (n + 1) → ℕ) (i : Fin (n + 1)) (hi : inR i)
    (hup : ∀ i' : Fin (n + 1), i' < i → inR i')
    (hmono : ∀ i' i'' : Fin (n + 1), inR i' → inR i'' → i' ≤ i'' → lab i' ≤ lab i'')
    (hinj : ∀ i' i'' : Fin (n + 1), inR i' → inR i'' → lab i' = lab i'' → i' = i'')
    (hsurj : ∀ j : ℕ, j < lab i → ∃ i' : Fin (n + 1), inR i' ∧ lab i' = j) : lab i = (i : ℕ) := by
  have hcard : (Finset.Iio i).card = (Finset.range (lab i)).card := by
    refine Finset.card_bij (fun i' _ => lab i') ?_ ?_ ?_
    · intro i' hi'
      have hlt : i' < i := Finset.mem_Iio.mp hi'
      have hR := hup i' hlt
      have hle := hmono i' i hR hi hlt.le
      have hne : lab i' ≠ lab i := fun h => (ne_of_lt hlt) (hinj i' i hR hi h)
      exact Finset.mem_range.mpr (lt_of_le_of_ne hle hne)
    · intro a ha b hb hab
      exact hinj a b (hup a (Finset.mem_Iio.mp ha)) (hup b (Finset.mem_Iio.mp hb)) hab
    · intro j hj
      obtain ⟨i', hR', hl⟩ := hsurj j (Finset.mem_range.mp hj)
      refine ⟨i', ?_, hl⟩
      refine Finset.mem_Iio.mpr ?_
      by_contra hcon
      push Not at hcon
      have := hmono i i' hi hR' hcon
      have hj' := Finset.mem_range.mp hj
      omega
  rw [Fin.card_Iio, Finset.card_range] at hcard
  exact hcard.symm

/-- the real-variable form: a strictly decreasing eigenvalue list, a range `R`, a window label of the energy. -/
theorem order_label_real {n : ℕ} (X : Fin (n + 1) → ℝ) (hX : StrictAnti X) (R : Set ℝ) (lab : ℝ → ℕ)
    (i : Fin (n + 1)) (hi : X i ∈ R) (hup : ∀ i' : Fin (n + 1), i' < i → X i' ∈ R)
    (hmono : ∀ x y : ℝ, x ∈ R → y ∈ R → y ≤ x → lab x ≤ lab y)
    (hinj : ∀ x y : ℝ, x ∈ R → y ∈ R → lab x = lab y → x = y)
    (hsurj : ∀ j : ℕ, j < lab (X i) → ∃ i' : Fin (n + 1), X i' ∈ R ∧ lab (X i') = j) : lab (X i) = (i : ℕ) := by
  refine order_label (fun i' => X i' ∈ R) (fun i' => lab (X i')) i hi hup ?_ ?_ hsurj
  · intro i' i'' h1 h2 h
    exact hmono _ _ h1 h2 (hX.antitone h)
  · intro i' i'' h1 h2 h
    exact hX.injective (hinj _ _ h1 h2 h)

end FormalResearch.JacobiEigenvectors.TheoremA

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.order_label_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.order_label_real
