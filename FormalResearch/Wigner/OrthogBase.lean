module

public import FormalResearch.Wigner.OrthogRatio
public import FormalResearch.Wigner.OrthogDougall

/-!
# The `6j` norm at the lowest admissible `μ`: a single Racah term

If a triangle inequality of the `6j` symbol is an equality (`λ + c = b`), the Racah sum has the
single term `t = x + a + b`.  Together with the Dougall sum `dougall_sum` this evaluates
`(2λ+1) ∑ₓ (2x+1) {x a b; λ c d}² = 1` at `λ = b - c`.
-/

@[expose] public section

namespace FormalResearch.Wigner

open Nat

lemma racahSum6_deg {x a b l c d : ℚ} {N0 p1 u2 u3 m p2 : ℕ} (hN : (N0 : ℚ) = x + a + b)
    (h1 : (p1 : ℚ) = a + b - c - d) (h2 : (u2 : ℚ) = x + b - l - d)
    (h3 : (u3 : ℚ) = x + a - l - c) (h4 : l + c - b = 0) (h5 : (m : ℚ) = c + d - x)
    (h6 : (p2 : ℚ) = d + l - a) :
    racahSum6 x a b l c d = (-1 : ℝ) ^ N0 * (((N0 + 1).factorial : ℕ) : ℝ) *
      ((((p1.factorial : ℕ) : ℝ) * (u2.factorial : ℕ) * (u3.factorial : ℕ) * (m.factorial : ℕ) *
        (p2.factorial : ℕ))⁻¹) := by
  unfold racahSum6
  rw [finsum_eq_single _ N0]
  · unfold term6
    rw [P7_vec]
    have e0 : (N0 : ℚ) - x - a - b = ((0 : ℕ) : ℚ) := by push_cast; linarith
    have e1 : (N0 : ℚ) - x - c - d = (p1 : ℚ) := by linarith
    have e2 : (N0 : ℚ) - l - a - d = (u2 : ℚ) := by linarith
    have e3 : (N0 : ℚ) - l - c - b = (u3 : ℚ) := by linarith
    have e4 : x + a + l + c - (N0 : ℚ) = ((0 : ℕ) : ℚ) := by push_cast; linarith
    have e5 : a + b + c + d - (N0 : ℚ) = (m : ℚ) := by linarith
    have e6 : b + x + d + l - (N0 : ℚ) = (p2 : ℚ) := by linarith
    rw [e0, e1, e2, e3, e4, e5, e6]
    simp only [ifa_natCast, Nat.factorial_zero, Nat.cast_one, inv_one, mul_inv]
    ring
  · intro t ht
    unfold term6 P7
    rcases lt_or_gt_of_ne ht with hlt | hgt
    · have : ifa ((t : ℚ) - x - a - b) = 0 := by
        apply ifa_eq_zero_of_neg
        have : (t : ℚ) + 1 ≤ N0 := by exact_mod_cast hlt
        linarith
      rw [Fin.prod_univ_seven]
      simp [this]
    · have : ifa (x + a + l + c - (t : ℚ)) = 0 := by
        apply ifa_eq_zero_of_neg
        have : (N0 : ℚ) + 1 ≤ t := by exact_mod_cast hgt
        linarith
      rw [Fin.prod_univ_seven]
      simp [this]


/-- The constant `p₃! (p₁+p₂)! γ! / ((p₁+p₂+p₃+1)! (p₁+p₂+γ+1)! p₁! p₂!)`. -/
noncomputable def Cl (p1 p2 p3 g : ℕ) : ℝ :=
  (((p3)! : ℕ) : ℝ) * (((p1 + p2)! : ℕ) : ℝ) * ((g ! : ℕ) : ℝ) /
    ((((p1 + p2 + p3 + 1)! : ℕ) : ℝ) * (((p1 + p2 + g + 1)! : ℕ) : ℝ) * ((p1 ! : ℕ) : ℝ) *
      ((p2 ! : ℕ) : ℝ))

/-- At the lowest admissible `λ = b - c` each summand of the norm is an explicit multiple of the
Dougall term. -/
lemma deg_summand {x a b l c d : ℚ} {p1 p2 m r3 rg : ℕ}
    (hl : l = b - c) (h1 : l + a - d = p1) (h2 : l - a + d = p2)
    (h3 : -l + a + d = ((m + r3 : ℕ) : ℚ)) (hc : 2 * c = ((m + rg : ℕ) : ℚ))
    (hx : x = c + d - m) :
    (2 * (x : ℝ) + 1) * (sixJ x a b l c d) ^ 2 =
      Cl p1 p2 (m + r3) (m + rg) * Tf p1 p2 (m + r3) (m + rg) m := by
  push_cast at h3 hc
  have t1 : triSq x a b = ((r3.factorial : ℕ) : ℝ) * ((p2 + rg).factorial : ℕ) *
      ((p1 + m).factorial : ℕ) / (((p1 + p2 + m + rg + r3 + 1).factorial : ℕ) : ℝ) := by
    rw [triSq_of_nat (p := r3) (q := p2 + rg) (r := p1 + m) (by linarith) (by push_cast; linarith)
      (by push_cast; linarith)]
    rw [show r3 + (p2 + rg) + (p1 + m) + 1 = p1 + p2 + m + rg + r3 + 1 by omega]
  have t2 : triSq x c d = ((rg.factorial : ℕ) : ℝ) * ((p2 + r3).factorial : ℕ) *
      ((m).factorial : ℕ) / (((m + rg + p2 + r3 + 1).factorial : ℕ) : ℝ) := by
    rw [triSq_of_nat (p := rg) (q := p2 + r3) (r := m) (by linarith) (by push_cast; linarith)
      (by linarith)]
    rw [show rg + (p2 + r3) + m + 1 = m + rg + p2 + r3 + 1 by omega]
  have t3 : triSq l a d = ((p1.factorial : ℕ) : ℝ) * (p2.factorial : ℕ) *
      ((m + r3).factorial : ℕ) / (((p1 + p2 + (m + r3) + 1).factorial : ℕ) : ℝ) := by
    rw [triSq_of_nat (p := p1) (q := p2) (r := m + r3) (by linarith) (by linarith)
      (by push_cast; linarith)]
  have t4 : triSq l c b = (((p1 + p2).factorial : ℕ) : ℝ) * ((m + rg).factorial : ℕ) /
      (((p1 + p2 + (m + rg) + 1).factorial : ℕ) : ℝ) := by
    rw [triSq_of_nat (p := 0) (q := p1 + p2) (r := m + rg) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith)]
    rw [show 0 + (p1 + p2) + (m + rg) + 1 = p1 + p2 + (m + rg) + 1 by omega]
    simp
  have hR := racahSum6_deg (x := x) (a := a) (b := b) (l := l) (c := c) (d := d)
    (N0 := p1 + p2 + m + rg + r3) (p1 := p1) (u2 := rg) (u3 := r3) (m := m) (p2 := p2)
    (by push_cast; linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have n1 : 0 ≤ triSq x a b := by rw [t1]; positivity
  have n2 : 0 ≤ triSq x c d := by rw [t2]; positivity
  have n3 : 0 ≤ triSq l a d := by rw [t3]; positivity
  have n4 : 0 ≤ triSq l c b := by rw [t4]; positivity
  have hsq : (sixJ x a b l c d) ^ 2 = triSq x a b * triSq x c d * triSq l a d * triSq l c b *
      (racahSum6 x a b l c d) ^ 2 := by
    unfold sixJ
    simp only [mul_pow, Real.sq_sqrt n1, Real.sq_sqrt n2, Real.sq_sqrt n3, Real.sq_sqrt n4]
  have hsign : ((-1 : ℝ) ^ (p1 + p2 + m + rg + r3)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  have hR2 : (racahSum6 x a b l c d) ^ 2 =
      ((((p1 + p2 + m + rg + r3 + 1).factorial : ℕ) : ℝ)) ^ 2 *
        ((((p1.factorial : ℕ) : ℝ) * (rg.factorial : ℕ) * (r3.factorial : ℕ) * (m.factorial : ℕ) *
          (p2.factorial : ℕ))⁻¹) ^ 2 := by
    rw [hR, mul_pow, mul_pow, hsign, one_mul]
  have h2x : (2 * (x : ℝ) + 1) = ((rg : ℝ) + p2 + r3 + 1) := by
    have : 2 * x + 1 = ((rg : ℚ) + p2 + r3 + 1) := by linarith
    exact_mod_cast this
  rw [hsq, hR2, t1, t2, t3, t4, h2x]
  unfold Cl Tf
  rw [show p2 + (m + rg) - m = p2 + rg by omega,
    show p2 + (m + r3) - m = p2 + r3 by omega,
    show p1 + (m + rg) + p2 + (m + r3) + 1 - m = p1 + p2 + m + rg + r3 + 1 by omega,
    show m + rg + p2 + (m + r3) + 1 - m = m + rg + p2 + r3 + 1 by omega,
    show m + r3 - m = r3 by omega, show m + rg - m = rg by omega]
  have hp : (((m + rg + p2 + (m + r3) + 1 : ℕ) : ℝ) - 2 * m) = (rg : ℝ) + p2 + r3 + 1 := by
    push_cast; ring
  rw [hp]
  have q1 : (0 : ℝ) < ((r3.factorial : ℕ) : ℝ) := by positivity
  have q2 : (0 : ℝ) < (((p2 + rg).factorial : ℕ) : ℝ) := by positivity
  have q3 : (0 : ℝ) < (((p1 + m).factorial : ℕ) : ℝ) := by positivity
  have q4 : (0 : ℝ) < (((p1 + p2 + m + rg + r3 + 1).factorial : ℕ) : ℝ) := by positivity
  have q5 : (0 : ℝ) < ((rg.factorial : ℕ) : ℝ) := by positivity
  have q6 : (0 : ℝ) < (((p2 + r3).factorial : ℕ) : ℝ) := by positivity
  have q7 : (0 : ℝ) < ((m.factorial : ℕ) : ℝ) := by positivity
  have q8 : (0 : ℝ) < (((m + rg + p2 + r3 + 1).factorial : ℕ) : ℝ) := by positivity
  have q9 : (0 : ℝ) < ((p1.factorial : ℕ) : ℝ) := by positivity
  have q10 : (0 : ℝ) < ((p2.factorial : ℕ) : ℝ) := by positivity
  have q11 : (0 : ℝ) < (((m + r3).factorial : ℕ) : ℝ) := by positivity
  have q12 : (0 : ℝ) < (((p1 + p2 + (m + r3) + 1).factorial : ℕ) : ℝ) := by positivity
  have q13 : (0 : ℝ) < (((p1 + p2).factorial : ℕ) : ℝ) := by positivity
  have q14 : (0 : ℝ) < (((m + rg).factorial : ℕ) : ℝ) := by positivity
  have q15 : (0 : ℝ) < (((p1 + p2 + (m + rg) + 1).factorial : ℕ) : ℝ) := by positivity
  field_simp


lemma not_isNat_of_neg {y : ℚ} (h : y < 0) : ¬ IsNat y := by
  rintro ⟨n, hn⟩
  have : (0 : ℚ) ≤ n := by positivity
  linarith

/-- **Normalisation at the lowest admissible `λ = b - c`.** -/
theorem orth_norm_base (a b c d : ℚ) (h : OAdm a b c d (b - c)) :
    (2 * (((b - c : ℚ)) : ℝ) + 1) * OA a b c d (b - c) (b - c) = 1 := by
  obtain ⟨⟨⟨p1, h1⟩, ⟨p2, h2⟩, ⟨p3, h3⟩⟩, ⟨-, -, ⟨g, hg⟩⟩⟩ := h
  have hc : 2 * c = (g : ℚ) := by linarith
  set K := min p3 g with hK
  -- the summand as a function of `k`
  set f : ℚ → ℝ := fun x => (2 * (x : ℝ) + 1) * (sixJ x a b (b - c) c d * sixJ x a b (b - c) c d)
    with hf
  have hfm : ∀ m : ℕ, m ≤ K → f (c + d - m) = Cl p1 p2 p3 g * Tf p1 p2 p3 g m := by
    intro m hm
    have hm3 : m ≤ p3 := le_trans hm (min_le_left _ _)
    have hmg : m ≤ g := le_trans hm (min_le_right _ _)
    obtain ⟨r3, hr3⟩ := Nat.exists_eq_add_of_le hm3
    obtain ⟨rg, hrg⟩ := Nat.exists_eq_add_of_le hmg
    have := deg_summand (x := c + d - m) (a := a) (b := b) (l := b - c) (c := c) (d := d)
      (p1 := p1) (p2 := p2) (m := m) (r3 := r3) (rg := rg) rfl h1 h2
      (by rw [← hr3]; exact h3) (by rw [← hrg]; exact hc) rfl
    rw [← hr3, ← hrg] at this
    simp only [hf]
    rw [← sq]
    exact this
  have hlat : ∀ k : ℕ, f (a + b - k) =
      if p1 ≤ k ∧ k - p1 ≤ K then Cl p1 p2 p3 g * Tf p1 p2 p3 g (k - p1) else 0 := by
    intro k
    split_ifs with hk
    · obtain ⟨hk1, hk2⟩ := hk
      have : (a + b - k : ℚ) = c + d - ((k - p1 : ℕ) : ℚ) := by
        rw [Nat.cast_sub hk1]; linarith
      rw [this]; exact hfm _ hk2
    · -- the symbol vanishes
      have hz : sixJ (a + b - k) a b (b - c) c d = 0 := by
        apply sixJ_eq_zero_of_not_tri12
        rintro ⟨t1, t2⟩
        apply hk
        obtain ⟨⟨n1, hn1⟩, -, -⟩ := t1
        obtain ⟨⟨n2, hn2⟩, -, ⟨n3, hn3⟩⟩ := t2
        have e1 : (k : ℚ) ≤ p1 + p3 := by
          have : (0 : ℚ) ≤ n1 := by positivity
          linarith
        have e2 : (k : ℚ) ≤ p1 + g := by
          have : (0 : ℚ) ≤ n2 := by positivity
          linarith
        have e3 : (p1 : ℚ) ≤ k := by
          have : (0 : ℚ) ≤ n3 := by positivity
          linarith
        have e1' : k ≤ p1 + p3 := by exact_mod_cast e1
        have e2' : k ≤ p1 + g := by exact_mod_cast e2
        have e3' : p1 ≤ k := by exact_mod_cast e3
        rw [hK]
        omega
      simp only [hf, hz]; ring
  have hsum : OA a b c d (b - c) (b - c) = Cl p1 p2 p3 g * Rf p1 p2 p3 g := by
    unfold OA lsum
    rw [← dougall_sum' p1 p2 p3 g, ← hK, Finset.mul_sum]
    change ∑ᶠ k : ℕ, f (a + b - k) = _
    simp only [hlat]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (p1 + (K + 1))), Finset.sum_range_add]
    · have h0 : ∑ k ∈ Finset.range p1,
          (if p1 ≤ k ∧ k - p1 ≤ K then Cl p1 p2 p3 g * Tf p1 p2 p3 g (k - p1) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have : k < p1 := Finset.mem_range.mp hk
        rw [ite_eq_right_iff]; intro hc; exfalso; omega
      rw [h0, zero_add]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm' : m < K + 1 := Finset.mem_range.mp hm
      have hcond : p1 ≤ p1 + m ∧ p1 + m - p1 ≤ K := ⟨by omega, by omega⟩
      split_ifs
      rw [Nat.add_sub_cancel_left]
    · intro k hk
      simp only [Function.mem_support, ne_eq] at hk
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hlt
      apply hk
      rw [ite_eq_right_iff]; intro hc; exfalso; omega
  rw [hsum]
  have hl2 : (2 * (((b - c : ℚ)) : ℝ) + 1) = (p1 : ℝ) + p2 + 1 := by
    have : 2 * (b - c) + 1 = (p1 : ℚ) + p2 + 1 := by linarith
    exact_mod_cast this
  rw [hl2]
  unfold Cl Rf
  have f1 : (((p1 + p2 + 1).factorial : ℕ) : ℝ) = ((p1 : ℝ) + p2 + 1) * (((p1 + p2).factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have q1 : (0 : ℝ) < ((p3.factorial : ℕ) : ℝ) := by positivity
  have q2 : (0 : ℝ) < ((g.factorial : ℕ) : ℝ) := by positivity
  have q3 : (0 : ℝ) < (((p1 + p2).factorial : ℕ) : ℝ) := by positivity
  have q4 : (0 : ℝ) < (((p1 + p2 + p3 + 1).factorial : ℕ) : ℝ) := by positivity
  have q5 : (0 : ℝ) < (((p1 + p2 + g + 1).factorial : ℕ) : ℝ) := by positivity
  have q6 : (0 : ℝ) < ((p1.factorial : ℕ) : ℝ) := by positivity
  have q7 : (0 : ℝ) < ((p2.factorial : ℕ) : ℝ) := by positivity
  have hs1 : (0 : ℝ) < (p1 : ℝ) + p2 + 1 := by positivity
  rw [show p1 + p2 + p3 + 1 = p1 + p2 + p3 + 1 from rfl, f1]
  field_simp

/-- info: 'FormalResearch.Wigner.orth_norm_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orth_norm_base

end FormalResearch.Wigner
