module

public import FormalResearch.Wigner.Symmetry

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

lemma ifa_pred (x : ℚ) : ifa (x - 1) = (x : ℝ) * ifa x := by
  have := ifa_shift (x - 1)
  rw [show x - 1 + 1 = x by ring] at this
  rw [← this]; push_cast; ring

lemma ifa_zero : ifa 0 = 1 := by simpa using ifa_natCast 0

lemma ifa_one : ifa 1 = 1 := by simpa using ifa_natCast 1

/-- **DLMF 34.5.7.** `{a b c; 1 c b} = (-1)^{a+b+c+1} 2[b(b+1)+c(c+1)-a(a+1)] /
√(2b(2b+1)(2b+2) 2c(2c+1)(2c+2))`, for `2b, 2c ≥ 1`. -/
theorem sixJ_one_left {a b c : ℚ} (h : IsTri a b c) (N : ℕ) (hN : (N : ℚ) = a + b + c)
    (hb1 : 1 ≤ 2 * b) (hc1 : 1 ≤ 2 * c) :
    sixJ a b c 1 c b =
      (-1 : ℝ) ^ (N + 1) * (2 * ((b : ℝ) * (b + 1) + c * (c + 1) - a * (a + 1))) /
        Real.sqrt ((2 * (b : ℝ)) * (2 * b + 1) * (2 * b + 2) *
          ((2 * (c : ℝ)) * (2 * c + 1) * (2 * c + 2))) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := h
  have hNpqr : N = p + q + r := by
    have : (N : ℚ) = ((p + q + r : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨v, hv⟩ : ∃ v, p + r = v + 1 := ⟨p + r - 1, by
    have : (1 : ℚ) ≤ ((p + r : ℕ) : ℚ) := by push_cast; linarith
    have : 1 ≤ p + r := by exact_mod_cast this
    omega⟩
  obtain ⟨z, hz⟩ : ∃ z, q + r = z + 1 := ⟨q + r - 1, by
    have : (1 : ℚ) ≤ ((q + r : ℕ) : ℚ) := by push_cast; linarith
    have : 1 ≤ q + r := by exact_mod_cast this
    omega⟩
  have hT : triSq a b c = (p.factorial : ℝ) * q.factorial * r.factorial / ((N + 1).factorial : ℝ) := by
    rw [triSq_of_nat hp hq hr, hNpqr]
  have hT' : triSq a c b = (p.factorial : ℝ) * q.factorial * r.factorial / ((N + 1).factorial : ℝ) := by
    rw [triSq_of_nat (p := q) (q := p) (r := r) (by linarith) (by linarith) (by linarith), hNpqr,
      show q + p + r + 1 = p + q + r + 1 by ring]
    ring
  have hB : triSq 1 b b = ((v + 1 : ℕ) : ℝ)⁻¹ * ((v + 2 : ℕ) : ℝ)⁻¹ * ((v + 3 : ℕ) : ℝ)⁻¹ := by
    rw [triSq_of_nat (p := 1) (q := 1) (r := v) (by simp) (by simp)
      (by have : (p : ℚ) + r = v + 1 := by exact_mod_cast hv
          linarith)]
    simp only [Nat.factorial_one, Nat.cast_one, one_mul]
    rw [show 1 + 1 + v + 1 = v + 3 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ, show v + 3 = v + 2 + 1 by ring]
    have : (v.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hC : triSq 1 c c = ((z + 1 : ℕ) : ℝ)⁻¹ * ((z + 2 : ℕ) : ℝ)⁻¹ * ((z + 3 : ℕ) : ℝ)⁻¹ := by
    rw [triSq_of_nat (p := 1) (q := 1) (r := z) (by simp) (by simp)
      (by have : (q : ℚ) + r = z + 1 := by exact_mod_cast hz
          linarith)]
    simp only [Nat.factorial_one, Nat.cast_one, one_mul]
    rw [show 1 + 1 + z + 1 = z + 3 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ, show z + 3 = z + 2 + 1 by ring]
    have : (z.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hsum : racahSum6 a b c 1 c b =
      (-1 : ℝ) ^ N * ((N + 1).factorial : ℝ) * (q : ℝ) * p *
          (((p.factorial : ℝ) * q.factorial * r.factorial)⁻¹) +
        (-1 : ℝ) ^ (N + 1) * ((N + 2).factorial : ℝ) * r *
          (((p.factorial : ℝ) * q.factorial * r.factorial)⁻¹) := by
    unfold racahSum6
    rw [finsum_eq_sum_of_support_subset _ (s := {N, N + 1}), Finset.sum_pair (by omega)]
    · unfold term6
      rw [P7_vec, P7_vec]
      have e0 : (N : ℚ) - a - b - c = 0 := by linarith
      have e1 : (N : ℚ) - a - c - b = 0 := by linarith
      have e2 : (N : ℚ) - 1 - b - b = (q : ℚ) - 1 := by linarith
      have e3 : (N : ℚ) - 1 - c - c = (p : ℚ) - 1 := by linarith
      have e4 : a + b + 1 + c - (N : ℚ) = 1 := by linarith
      have e5 : b + c + c + b - (N : ℚ) = r := by linarith
      have e6 : c + a + b + 1 - (N : ℚ) = 1 := by linarith
      have f0 : ((N + 1 : ℕ) : ℚ) - a - b - c = 1 := by push_cast; linarith
      have f1 : ((N + 1 : ℕ) : ℚ) - a - c - b = 1 := by push_cast; linarith
      have f2 : ((N + 1 : ℕ) : ℚ) - 1 - b - b = q := by push_cast; linarith
      have f3 : ((N + 1 : ℕ) : ℚ) - 1 - c - c = p := by push_cast; linarith
      have f4 : a + b + 1 + c - ((N + 1 : ℕ) : ℚ) = 0 := by push_cast; linarith
      have f5 : b + c + c + b - ((N + 1 : ℕ) : ℚ) = (r : ℚ) - 1 := by push_cast; linarith
      have f6 : c + a + b + 1 - ((N + 1 : ℕ) : ℚ) = 0 := by push_cast; linarith
      rw [e0, e1, e2, e3, e4, e5, e6, f0, f1, f2, f3, f4, f5, f6, ifa_pred (q : ℚ), ifa_pred (p : ℚ),
        ifa_pred (r : ℚ), ifa_zero, ifa_one, ifa_natCast, ifa_natCast, ifa_natCast]
      push_cast
      ring
    · intro t ht
      simp only [Function.mem_support, ne_eq] at ht
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hno
      push Not at hno
      apply ht
      unfold term6
      rw [P7_vec]
      rcases lt_or_gt_of_ne hno.1 with hlt | hgt
      · have : ifa ((t : ℚ) - a - b - c) = 0 := by
          apply ifa_eq_zero_of_neg
          have : (t : ℚ) + 1 ≤ N := by exact_mod_cast hlt
          linarith
        rw [this]; simp
      · have hgt2 : N + 1 < t := lt_of_le_of_ne hgt (Ne.symm hno.2)
        have : ifa (a + b + 1 + c - (t : ℚ)) = 0 := by
          apply ifa_eq_zero_of_neg
          have : (N : ℚ) + 2 ≤ t := by exact_mod_cast hgt2
          linarith
        rw [this]; simp
  have hbq : (b : ℝ) = ((p + r : ℕ) : ℝ) / 2 := by
    have : b = ((p + r : ℕ) : ℚ) / 2 := by push_cast; linarith
    rw [this]; push_cast; ring
  have key : 2 * ((b : ℝ) * (b + 1) + c * (c + 1) - a * (a + 1)) =
      (r : ℝ) * (N + 2) - p * q := by
    have e : (a : ℚ) = (p + q) / 2 := by linarith
    have e' : (b : ℚ) = (p + r) / 2 := by linarith
    have e'' : (c : ℚ) = (q + r) / 2 := by linarith
    have hN' : (N : ℚ) = p + q + r := by rw [hN]; linarith
    have : 2 * ((b : ℚ) * (b + 1) + c * (c + 1) - a * (a + 1)) = (r : ℚ) * (N + 2) - p * q := by
      rw [e, e', e'', hN']; ring
    exact_mod_cast this
  have hu : 2 * (b : ℝ) = ((v + 1 : ℕ) : ℝ) := by
    have : 2 * b = ((v + 1 : ℕ) : ℚ) := by
      have : (p : ℚ) + r = v + 1 := by exact_mod_cast hv
      push_cast; linarith
    exact_mod_cast this
  have hw : 2 * (c : ℝ) = ((z + 1 : ℕ) : ℝ) := by
    have : 2 * c = ((z + 1 : ℕ) : ℚ) := by
      have : (q : ℚ) + r = z + 1 := by exact_mod_cast hz
      push_cast; linarith
    exact_mod_cast this
  unfold sixJ
  rw [hsum, hT, hT', hB, hC, key, hu, hw]
  have hUv : (0 : ℝ) < ((v + 1 : ℕ) : ℝ) * ((v + 2 : ℕ) : ℝ) * ((v + 3 : ℕ) : ℝ) := by positivity
  have hWz : (0 : ℝ) < ((z + 1 : ℕ) : ℝ) * ((z + 2 : ℕ) : ℝ) * ((z + 3 : ℕ) : ℝ) := by positivity
  have e1 : ((v + 1 : ℕ) : ℝ)⁻¹ * ((v + 2 : ℕ) : ℝ)⁻¹ * ((v + 3 : ℕ) : ℝ)⁻¹ =
      (((v + 1 : ℕ) : ℝ) * ((v + 2 : ℕ) : ℝ) * ((v + 3 : ℕ) : ℝ))⁻¹ := by
    rw [mul_inv, mul_inv]
  have e2 : ((z + 1 : ℕ) : ℝ)⁻¹ * ((z + 2 : ℕ) : ℝ)⁻¹ * ((z + 3 : ℕ) : ℝ)⁻¹ =
      (((z + 1 : ℕ) : ℝ) * ((z + 2 : ℕ) : ℝ) * ((z + 3 : ℕ) : ℝ))⁻¹ := by
    rw [mul_inv, mul_inv]
  have e3 : ((v + 1 : ℕ) : ℝ) * (((v + 1 : ℕ) : ℝ) + 1) * (((v + 1 : ℕ) : ℝ) + 2) *
      (((z + 1 : ℕ) : ℝ) * (((z + 1 : ℕ) : ℝ) + 1) * (((z + 1 : ℕ) : ℝ) + 2)) =
      (((v + 1 : ℕ) : ℝ) * ((v + 2 : ℕ) : ℝ) * ((v + 3 : ℕ) : ℝ)) *
        (((z + 1 : ℕ) : ℝ) * ((z + 2 : ℕ) : ℝ) * ((z + 3 : ℕ) : ℝ)) := by
    push_cast; ring
  have hT0 : 0 ≤ (p.factorial : ℝ) * q.factorial * r.factorial / ((N + 1).factorial : ℝ) := by
    positivity
  rw [e1, e2, e3, Real.sqrt_inv, Real.sqrt_inv, Real.mul_self_sqrt hT0, Real.sqrt_mul hUv.le]
  have h5 : Real.sqrt (((v + 1 : ℕ) : ℝ) * ((v + 2 : ℕ) : ℝ) * ((v + 3 : ℕ) : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr hUv).ne'
  have h6 : Real.sqrt (((z + 1 : ℕ) : ℝ) * ((z + 2 : ℕ) : ℝ) * ((z + 3 : ℕ) : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr hWz).ne'
  have h1 : ((p.factorial : ℝ)) ≠ 0 := by positivity
  have h2 : ((q.factorial : ℝ)) ≠ 0 := by positivity
  have h3 : ((r.factorial : ℝ)) ≠ 0 := by positivity
  have h4 : (((N + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ (N + 1), pow_succ]
  push_cast
  field_simp
  ring

/-- info: 'FormalResearch.Wigner.sixJ_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_zero_left

/-- info: 'FormalResearch.Wigner.sixJ_one_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_one_left

end FormalResearch.Wigner
