module

public import Mathlib

/-!
# A terminating very-well-poised `₅F₄` sum (Dougall)

`dougall_sum` is the evaluation
`∑_{m=0}^{P} T(m) = A! B! (A+B+P+1)! (A+B+G+1)! / ((A+B+1)! P! G!)`  for `P ≤ G`,
`T(m) = (N-2m) (B+G-m)! (A+m)! (B+P-m)! (A+N-m)! / ((N-m)! (P-m)! (G-m)! m!)`, `N = G+B+P+1`,
which is the total mass of the Racah weight and gives the normalisation of the `6j` orthogonality
relation.  Proof: induction on `P`, using the creative-telescoping certificate
`T(P+1,m) - ρ T(P,m) = g(m+1) - g(m)` with `ρ = (A+B+P+2)/(P+1)` and the pure factorial product `g`.
-/

@[expose] public section

namespace FormalResearch.Wigner

open Nat

noncomputable def Tf (A B P G m : ℕ) : ℝ :=
  (((G + B + P + 1 : ℕ) : ℝ) - 2 * m) * (((B + G - m)! : ℕ) : ℝ) * (((A + m)! : ℕ) : ℝ) *
    (((B + P - m)! : ℕ) : ℝ) * (((A + G + B + P + 1 - m)! : ℕ) : ℝ) /
  ((((G + B + P + 1 - m)! : ℕ) : ℝ) * (((P - m)! : ℕ) : ℝ) * (((G - m)! : ℕ) : ℝ) *
    ((m ! : ℕ) : ℝ))

noncomputable def gf (A B P G m : ℕ) : ℝ :=
  -(m : ℝ) * (((B + G + 1 - m)! : ℕ) : ℝ) * (((A + m)! : ℕ) : ℝ) *
    (((B + P + 1 - m)! : ℕ) : ℝ) * (((A + G + B + P + 2 - m)! : ℕ) : ℝ) /
  (((P : ℝ) + 1) * (((G + B + P + 2 - m)! : ℕ) : ℝ) * (((P + 1 - m)! : ℕ) : ℝ) *
    (((G - m)! : ℕ) : ℝ) * ((m ! : ℕ) : ℝ))

lemma Tf_cert (A B P G m : ℕ) (hm : m ≤ P) (hPG : P < G) :
    Tf A B (P + 1) G m - ((A + B + P + 2 : ℝ) / (P + 1)) * Tf A B P G m =
      gf A B P G (m + 1) - gf A B P G m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_lt hPG
  unfold Tf gf
  rw [show B + (m + k + h + 1) - m = B + k + h + 1 by omega,
    show B + (m + k + 1) - m = B + k + 1 by omega,
    show A + (m + k + h + 1) + B + (m + k + 1) + 1 - m = A + m + 2 * k + h + B + 3 by omega,
    show m + k + h + 1 + B + (m + k + 1) + 1 - m = m + 2 * k + h + B + 3 by omega,
    show m + k + 1 - m = k + 1 by omega,
    show m + k + h + 1 - m = k + h + 1 by omega,
    show B + (m + k) - m = B + k by omega,
    show A + (m + k + h + 1) + B + (m + k) + 1 - m = A + m + 2 * k + h + B + 2 by omega,
    show m + k + h + 1 + B + (m + k) + 1 - m = m + 2 * k + h + B + 2 by omega,
    show m + k - m = k by omega,
    show B + (m + k + h + 1) + 1 - (m + 1) = B + k + h + 1 by omega,
    show B + (m + k) + 1 - (m + 1) = B + k by omega,
    show A + (m + k + h + 1) + B + (m + k) + 2 - (m + 1) = A + m + 2 * k + h + B + 2 by omega,
    show m + k + h + 1 + B + (m + k) + 2 - (m + 1) = m + 2 * k + h + B + 2 by omega,
    show m + k + 1 - (m + 1) = k by omega,
    show m + k + h + 1 - (m + 1) = k + h by omega,
    show B + (m + k + h + 1) + 1 - m = B + k + h + 2 by omega,
    show B + (m + k) + 1 - m = B + k + 1 by omega,
    show A + (m + k + h + 1) + B + (m + k) + 2 - m = A + m + 2 * k + h + B + 3 by omega,
    show m + k + h + 1 + B + (m + k) + 2 - m = m + 2 * k + h + B + 3 by omega]
  have f1 : (((B + k + h + 2)! : ℕ) : ℝ) = ((B : ℝ) + k + h + 2) * (((B + k + h + 1)! : ℕ) : ℝ) := by
    rw [show B + k + h + 2 = (B + k + h + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have f2 : (((B + k + 1)! : ℕ) : ℝ) = ((B : ℝ) + k + 1) * (((B + k)! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f3 : (((A + m + 2 * k + h + B + 3)! : ℕ) : ℝ) =
      ((A : ℝ) + m + 2 * k + h + B + 3) * (((A + m + 2 * k + h + B + 2)! : ℕ) : ℝ) := by
    rw [show A + m + 2 * k + h + B + 3 = (A + m + 2 * k + h + B + 2) + 1 by ring,
      Nat.factorial_succ]; push_cast; ring
  have f4 : (((m + 2 * k + h + B + 3)! : ℕ) : ℝ) =
      ((m : ℝ) + 2 * k + h + B + 3) * (((m + 2 * k + h + B + 2)! : ℕ) : ℝ) := by
    rw [show m + 2 * k + h + B + 3 = (m + 2 * k + h + B + 2) + 1 by ring, Nat.factorial_succ]
    push_cast; ring
  have f5 : (((k + 1)! : ℕ) : ℝ) = ((k : ℝ) + 1) * ((k ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f6 : (((k + h + 1)! : ℕ) : ℝ) = ((k : ℝ) + h + 1) * (((k + h)! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f7 : (((A + (m + 1))! : ℕ) : ℝ) = ((A : ℝ) + m + 1) * (((A + m)! : ℕ) : ℝ) := by
    rw [show A + (m + 1) = (A + m) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have f8 : (((m + 1)! : ℕ) : ℝ) = ((m : ℝ) + 1) * ((m ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f9 : (((k + h + 1)! : ℕ) : ℝ) = ((k : ℝ) + h + 1) * (((k + h)! : ℕ) : ℝ) := f6
  rw [f1, f2, f3, f4, f5, f6, f7, f8]
  push_cast
  have p1 : (0 : ℝ) < (((B + k + h + 1)! : ℕ) : ℝ) := by positivity
  have p2 : (0 : ℝ) < (((A + m)! : ℕ) : ℝ) := by positivity
  have p3 : (0 : ℝ) < (((B + k)! : ℕ) : ℝ) := by positivity
  have p4 : (0 : ℝ) < (((A + m + 2 * k + h + B + 2)! : ℕ) : ℝ) := by positivity
  have q1 : (0 : ℝ) < (((m + 2 * k + h + B + 2)! : ℕ) : ℝ) := by positivity
  have q2 : (0 : ℝ) < ((k ! : ℕ) : ℝ) := by positivity
  have q3 : (0 : ℝ) < (((k + h)! : ℕ) : ℝ) := by positivity
  have q4 : (0 : ℝ) < ((m ! : ℕ) : ℝ) := by positivity
  generalize (((B + k + h + 1)! : ℕ) : ℝ) = Y1 at p1 ⊢
  generalize (((A + m)! : ℕ) : ℝ) = Y2 at p2 ⊢
  generalize (((B + k)! : ℕ) : ℝ) = Y3 at p3 ⊢
  generalize (((A + m + 2 * k + h + B + 2)! : ℕ) : ℝ) = Y4 at p4 ⊢
  generalize (((m + 2 * k + h + B + 2)! : ℕ) : ℝ) = Z1 at q1 ⊢
  generalize ((k ! : ℕ) : ℝ) = Z2 at q2 ⊢
  generalize (((k + h)! : ℕ) : ℝ) = Z3 at q3 ⊢
  generalize ((m ! : ℕ) : ℝ) = Z4 at q4 ⊢
  have hA : (0 : ℝ) ≤ A := by positivity
  have hB : (0 : ℝ) ≤ B := by positivity
  have hm : (0 : ℝ) ≤ m := by positivity
  have hk : (0 : ℝ) ≤ k := by positivity
  have hh : (0 : ℝ) ≤ h := by positivity
  field_simp
  ring

lemma gf_zero (A B P G : ℕ) : gf A B P G 0 = 0 := by simp [gf]

lemma Tf_endpoint (A B P G : ℕ) (hPG : P < G) :
    Tf A B (P + 1) G (P + 1) + gf A B P G (P + 1) = 0 := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_lt hPG
  unfold Tf gf
  rw [show B + (P + h + 1) - (P + 1) = B + h by omega,
    show B + (P + 1) - (P + 1) = B by omega,
    show A + (P + h + 1) + B + (P + 1) + 1 - (P + 1) = A + P + h + B + 2 by omega,
    show P + h + 1 + B + (P + 1) + 1 - (P + 1) = P + h + B + 2 by omega,
    show P + 1 - (P + 1) = 0 by omega,
    show P + h + 1 - (P + 1) = h by omega,
    show B + (P + h + 1) + 1 - (P + 1) = B + h + 1 by omega,
    show B + P + 1 - (P + 1) = B by omega,
    show A + (P + h + 1) + B + P + 2 - (P + 1) = A + P + h + B + 2 by omega,
    show P + h + 1 + B + P + 2 - (P + 1) = P + h + B + 2 by omega]
  have f1 : (((B + h + 1)! : ℕ) : ℝ) = ((B : ℝ) + h + 1) * (((B + h)! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f2 : (((P + 1)! : ℕ) : ℝ) = ((P : ℝ) + 1) * ((P ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [f1, f2]
  have p1 : (0 : ℝ) < (((B + h)! : ℕ) : ℝ) := by positivity
  have p2 : (0 : ℝ) < (((A + (P + 1))! : ℕ) : ℝ) := by positivity
  have p3 : (0 : ℝ) < ((B ! : ℕ) : ℝ) := by positivity
  have p4 : (0 : ℝ) < (((A + P + h + B + 2)! : ℕ) : ℝ) := by positivity
  have p5 : (0 : ℝ) < (((P + h + B + 2)! : ℕ) : ℝ) := by positivity
  have p6 : (0 : ℝ) < ((h ! : ℕ) : ℝ) := by positivity
  have p7 : (0 : ℝ) < ((P ! : ℕ) : ℝ) := by positivity
  push_cast
  field_simp
  ring

/-- The step `P → P + 1` of the Dougall sum. -/
lemma Tf_step (A B P G : ℕ) (hPG : P < G) :
    ∑ m ∈ Finset.range (P + 2), Tf A B (P + 1) G m =
      ((A + B + P + 2 : ℝ) / (P + 1)) * ∑ m ∈ Finset.range (P + 1), Tf A B P G m := by
  rw [Finset.sum_range_succ]
  have hs : ∑ m ∈ Finset.range (P + 1),
      (Tf A B (P + 1) G m - ((A + B + P + 2 : ℝ) / (P + 1)) * Tf A B P G m) =
      ∑ m ∈ Finset.range (P + 1), (gf A B P G (m + 1) - gf A B P G m) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    exact Tf_cert A B P G m (by simpa [Nat.lt_succ_iff] using hm) hPG
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_range_sub (gf A B P G),
    gf_zero] at hs
  have := Tf_endpoint A B P G hPG
  linarith

noncomputable def Rf (A B P G : ℕ) : ℝ :=
  (((A)! : ℕ) : ℝ) * ((B ! : ℕ) : ℝ) * (((A + B + P + 1)! : ℕ) : ℝ) * (((A + B + G + 1)! : ℕ) : ℝ) /
    ((((A + B + 1)! : ℕ) : ℝ) * ((P ! : ℕ) : ℝ) * ((G ! : ℕ) : ℝ))

lemma Rf_succ (A B P G : ℕ) : Rf A B (P + 1) G = ((A + B + P + 2 : ℝ) / (P + 1)) * Rf A B P G := by
  unfold Rf
  have f1 : (((A + B + (P + 1) + 1)! : ℕ) : ℝ) = ((A : ℝ) + B + P + 2) * (((A + B + P + 1)! : ℕ) : ℝ) := by
    rw [show A + B + (P + 1) + 1 = (A + B + P + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have f2 : (((P + 1)! : ℕ) : ℝ) = ((P : ℝ) + 1) * ((P ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [f1, f2]
  have p1 : (0 : ℝ) < ((P ! : ℕ) : ℝ) := by positivity
  have p2 : (0 : ℝ) < (((A + B + 1)! : ℕ) : ℝ) := by positivity
  have p3 : (0 : ℝ) < ((G ! : ℕ) : ℝ) := by positivity
  field_simp

/-- **Dougall-type sum.** For `P ≤ G`:
`∑_{m=0}^{P} T(m) = A! B! (A+B+P+1)! (A+B+G+1)! / ((A+B+1)! P! G!)`. -/
theorem dougall_sum (A B G : ℕ) : ∀ P : ℕ, P ≤ G →
    ∑ m ∈ Finset.range (P + 1), Tf A B P G m = Rf A B P G := by
  intro P
  induction P with
  | zero =>
    intro _
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    unfold Tf Rf
    simp only [Nat.sub_zero, Nat.add_zero, Nat.factorial_zero, Nat.cast_one,
      Nat.cast_zero, mul_zero, sub_zero, mul_one]
    rw [show B + G = G + B by ring]
    have f1 : (((G + B + 1)! : ℕ) : ℝ) = ((G : ℝ) + B + 1) * (((G + B)! : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have e : A + G + B + 1 = A + B + G + 1 := by ring
    rw [e, f1]
    have p1 : (0 : ℝ) < (((G + B)! : ℕ) : ℝ) := by positivity
    have p2 : (0 : ℝ) < (((A + B + 1)! : ℕ) : ℝ) := by positivity
    have p3 : (0 : ℝ) < ((G ! : ℕ) : ℝ) := by positivity
    push_cast
    field_simp
  | succ P ih =>
    intro hP
    rw [Tf_step A B P G (by omega), ih (by omega), Rf_succ]

lemma Tf_symm (A B P G m : ℕ) : Tf A B P G m = Tf A B G P m := by
  unfold Tf
  rw [show P + B + G + 1 = G + B + P + 1 by ring,
    show A + P + B + G + 1 - m = A + G + B + P + 1 - m by
      rw [show A + P + B + G + 1 = A + G + B + P + 1 by ring]]
  ring

lemma Rf_symm (A B P G : ℕ) : Rf A B P G = Rf A B G P := by
  unfold Rf; ring

/-- The Dougall sum without the hypothesis `P ≤ G`, summed up to `min P G`. -/
theorem dougall_sum' (A B P G : ℕ) :
    ∑ m ∈ Finset.range (min P G + 1), Tf A B P G m = Rf A B P G := by
  rcases le_total P G with h | h
  · rw [min_eq_left h]; exact dougall_sum A B G P h
  · rw [min_eq_right h]
    have := dougall_sum A B P G h
    rw [Rf_symm, ← this]
    refine Finset.sum_congr rfl fun m _ => Tf_symm A B P G m

/-- info: 'FormalResearch.Wigner.dougall_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dougall_sum

/-- info: 'FormalResearch.Wigner.dougall_sum'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dougall_sum'

end FormalResearch.Wigner
