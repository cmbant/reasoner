module

public import Mathlib

/-!
# Summation over the `j₃`-lattice and Green's identity for three-term recurrences

`lsum a b f = ∑_{k ∈ ℕ} f (a + b - k)` is the sum over the lattice `x = a + b - k`.  Every `x` with
`IsTri x a b` is of this form, and `6j` symbols are zero-extended, so for functions vanishing at
negative arguments it is the finite sum over the admissible range.

`green_lsum` is the discrete Green identity behind the orthogonality of eigenvectors of a
Jacobi-type operator: two solutions `s`, `s'` of
`(P x + 2 (2x+1) x (x+1) Λ) s x = x E(x+1) s(x+1) + (x+1) E(x) s(x-1)` with different `Λ` satisfy
`(Λ - Λ') ∑ (2x+1) s s' = 0`.  The value at `x = 0` of the cross identity is a hypothesis
(`h0`), because the weight `x (x+1)` vanishes there.
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- Sum over the lattice `x = a + b - k`, `k ∈ ℕ`. -/
noncomputable def lsum (a b : ℚ) (f : ℚ → ℝ) : ℝ := ∑ᶠ k : ℕ, f (a + b - k)

lemma lsum_eq_sum {a b : ℚ} {f : ℚ → ℝ} (hf : ∀ x : ℚ, x < 0 → f x = 0) (N : ℕ)
    (hN : a + b < N) : lsum a b f = ∑ k ∈ Finset.range N, f (a + b - k) := by
  unfold lsum
  apply finsum_eq_sum_of_support_subset
  intro k hk
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hk
  apply hf
  have : (N : ℚ) ≤ k := by exact_mod_cast not_lt.mp hlt
  linarith

lemma exists_nat_gt_lattice (a b : ℚ) : ∃ N : ℕ, a + b < N :=
  ⟨⌈a + b⌉₊ + 1, by
    have := Nat.le_ceil (a + b)
    push_cast; linarith⟩

lemma lsum_comb {a b : ℚ} {f g : ℚ → ℝ} (hf : ∀ x : ℚ, x < 0 → f x = 0)
    (hg : ∀ x : ℚ, x < 0 → g x = 0) (p q : ℝ) :
    lsum a b (fun x => p * f x + q * g x) = p * lsum a b f + q * lsum a b g := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt_lattice a b
  have h1 : ∀ x : ℚ, x < 0 → p * f x + q * g x = 0 := by
    intro x hx; rw [hf x hx, hg x hx]; ring
  rw [lsum_eq_sum h1 N0 hN0, lsum_eq_sum hf N0 hN0, lsum_eq_sum hg N0 hN0, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]

lemma lsum_congr {a b : ℚ} {f g : ℚ → ℝ} (h : ∀ x, f x = g x) : lsum a b f = lsum a b g := by
  unfold lsum; simp only [h]

lemma lsum_smul {a b : ℚ} {f : ℚ → ℝ} (hf : ∀ x : ℚ, x < 0 → f x = 0) (p : ℝ) :
    lsum a b (fun x => p * f x) = p * lsum a b f := by
  have := lsum_comb (a := a) (b := b) (f := f) (g := f) hf hf p 0
  simpa using this

/-- `g` of Green's identity. -/
noncomputable def greenG (E s s' : ℚ → ℝ) (y : ℚ) : ℝ :=
  E y * (s y * s' (y - 1) - s' y * s (y - 1)) / y

lemma greenG_eq_zero_of_nonpos {E s s' : ℚ → ℝ} (hs : ∀ x : ℚ, x < 0 → s x = 0)
    (hs' : ∀ x : ℚ, x < 0 → s' x = 0) {y : ℚ} (hy : y ≤ 0) : greenG E s s' y = 0 := by
  rcases hy.lt_or_eq with h | h
  · unfold greenG
    rw [hs y h, hs' y h, hs (y - 1) (by linarith), hs' (y - 1) (by linarith)]; simp
  · subst h; simp [greenG]

/-- The pointwise cross identity for `x > 0`. -/
lemma green_cross {E s s' : ℚ → ℝ} {P : ℚ → ℝ} {Λ Λ' : ℝ}
    (hr : ∀ x : ℚ, (P x + 2 * (2 * (x : ℝ) + 1) * x * (x + 1) * Λ) * s x =
      x * E (x + 1) * s (x + 1) + (x + 1) * E x * s (x - 1))
    (hr' : ∀ x : ℚ, (P x + 2 * (2 * (x : ℝ) + 1) * x * (x + 1) * Λ') * s' x =
      x * E (x + 1) * s' (x + 1) + (x + 1) * E x * s' (x - 1))
    {x : ℚ} (hx : 0 < x) :
    2 * (Λ - Λ') * ((2 * (x : ℝ) + 1) * (s x * s' x)) =
      greenG E s s' (x + 1) - greenG E s s' x := by
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  have hx1 : (x : ℝ) + 1 ≠ 0 := by
    have : (0 : ℝ) < x := by exact_mod_cast hx
    linarith
  unfold greenG
  simp only [add_sub_cancel_right, Rat.cast_add, Rat.cast_one]
  have h1 := hr x
  have h2 := hr' x
  field_simp
  linear_combination (s' x) * h1 - (s x) * h2

theorem green_lsum {a b : ℚ} {E s s' : ℚ → ℝ} {P : ℚ → ℝ} {Λ Λ' : ℝ}
    (hs : ∀ x : ℚ, x < 0 → s x = 0) (hs' : ∀ x : ℚ, x < 0 → s' x = 0)
    (htop : s (a + b + 1) = 0 ∧ s' (a + b + 1) = 0)
    (hr : ∀ x : ℚ, (P x + 2 * (2 * (x : ℝ) + 1) * x * (x + 1) * Λ) * s x =
      x * E (x + 1) * s (x + 1) + (x + 1) * E x * s (x - 1))
    (hr' : ∀ x : ℚ, (P x + 2 * (2 * (x : ℝ) + 1) * x * (x + 1) * Λ') * s' x =
      x * E (x + 1) * s' (x + 1) + (x + 1) * E x * s' (x - 1))
    (h0 : 2 * (Λ - Λ') * (s 0 * s' 0) = E 1 * (s 1 * s' 0 - s' 1 * s 0)) :
    (Λ - Λ') * lsum a b (fun x => (2 * (x : ℝ) + 1) * (s x * s' x)) = 0 := by
  have hpt : ∀ x : ℚ, 2 * (Λ - Λ') * ((2 * (x : ℝ) + 1) * (s x * s' x)) =
      greenG E s s' (x + 1) - greenG E s s' x := by
    intro x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [hs x hx, hs' x hx]
      have : greenG E s s' (x + 1) = 0 := by
        unfold greenG
        simp [hs x hx, hs' x hx]
      rw [this, greenG_eq_zero_of_nonpos hs hs' hx.le]; ring
    · subst hx
      rw [greenG_eq_zero_of_nonpos hs hs' le_rfl]
      unfold greenG
      norm_num
      linarith [h0]
    · exact green_cross hr hr' hx
  obtain ⟨N0, hN0⟩ := exists_nat_gt_lattice a b
  obtain ⟨N, hN⟩ : ∃ N : ℕ, a + b + 1 ≤ N := ⟨N0 + 1, by push_cast; linarith⟩
  have hz : ∀ x : ℚ, x < 0 → (2 * (x : ℝ) + 1) * (s x * s' x) = 0 := by
    intro x hx; rw [hs x hx]; ring
  rw [lsum_eq_sum hz N (by linarith)]
  have hS : ∑ k ∈ Finset.range N,
      (greenG E s s' (a + b - k + 1) - greenG E s s' (a + b - k)) = 0 := by
    have := Finset.sum_range_sub' (fun i : ℕ => greenG E s s' (a + b + 1 - i)) N
    have e : ∀ k : ℕ, greenG E s s' (a + b - k + 1) - greenG E s s' (a + b - k) =
        greenG E s s' (a + b + 1 - k) - greenG E s s' (a + b + 1 - ((k + 1 : ℕ) : ℚ)) := by
      intro k
      rw [show (a + b - k + 1 : ℚ) = a + b + 1 - k by ring,
        show (a + b - k : ℚ) = a + b + 1 - ((k + 1 : ℕ) : ℚ) by push_cast; ring]
    rw [Finset.sum_congr rfl (fun k _ => e k), this]
    have h1 : greenG E s s' (a + b + 1 - ((0 : ℕ) : ℚ)) = 0 := by
      have := htop
      unfold greenG
      simp [this.1, this.2]
    have h2 : greenG E s s' (a + b + 1 - (N : ℚ)) = 0 :=
      greenG_eq_zero_of_nonpos hs hs' (by linarith)
    rw [h1, h2]; ring
  have key : 2 * ((Λ - Λ') * ∑ k ∈ Finset.range N,
      (2 * (((a + b - k : ℚ)) : ℝ) + 1) * (s (a + b - k) * s' (a + b - k))) = 0 := by
    rw [mul_left_comm, Finset.mul_sum, Finset.mul_sum]
    simp only [← mul_assoc]
    rw [← hS]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hpt (a + b - k)
    rw [← this]; ring
  linarith

/-- info: 'FormalResearch.Wigner.green_lsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms green_lsum

end FormalResearch.Wigner
