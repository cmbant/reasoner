module

public import FormalResearch.Wigner.Stretched3j
public import FormalResearch.Wigner.Symmetry

/-!
# Symmetries of the Wigner `3j` symbol (DLMF 34.3.8, 34.3.9, 34.3.10)

The zero-extended `threeJ` is invariant under even permutations of the columns, changes by
`(-1)^(j₁+j₂+j₃)` under odd ones, and by the same sign when all `m` are negated.  With the
zero-extended sign `sgn` the statements hold for all rational arguments:
`sgn (j₁+j₂+j₃)` is `(-1)^(j₁+j₂+j₃)` when the sum is an integer, and the symbol vanishes when it is not.

The proofs are termwise: each transposition acts on Racah's sum by reflecting the summation index,
`σ ↦ M - σ` with `M = j₁+j₂-j₃` (swap of columns 1, 2 and negation of all `m`) or `M = j₁-m₁`
(swap of columns 2, 3), and the signs are tracked with `sgn`.
-/

@[expose] public section

namespace FormalResearch.Wigner

/-! ### The sign `sgn` -/

lemma sgn_intCast (n : ℤ) : sgn (n : ℚ) = (-1 : ℝ) ^ n := by
  unfold sgn
  have h : ∃ m : ℤ, (n : ℚ) = m := ⟨n, rfl⟩
  rw [dif_pos h]
  have : h.choose = n := by exact_mod_cast h.choose_spec.symm
  rw [this]

lemma sgn_natCast (n : ℕ) : sgn (n : ℚ) = (-1 : ℝ) ^ n := by
  have := sgn_intCast (n : ℤ)
  simpa using this

lemma sgn_add_int (x : ℚ) (n : ℤ) : sgn (x + n) = (-1 : ℝ) ^ n * sgn x := by
  by_cases h : ∃ m : ℤ, x = m
  · obtain ⟨m, rfl⟩ := h
    rw [← Int.cast_add, sgn_intCast, sgn_intCast, zpow_add₀ (by norm_num), mul_comm]
  · have h' : ¬ ∃ m : ℤ, x + n = m := by
      rintro ⟨m, hm⟩; exact h ⟨m - n, by push_cast; linarith⟩
    unfold sgn
    rw [dif_neg h, dif_neg h']; simp

lemma sgn_neg' (x : ℚ) : sgn (-x) = sgn x := by
  by_cases h : ∃ m : ℤ, x = m
  · obtain ⟨m, rfl⟩ := h
    rw [← Int.cast_neg, sgn_intCast, sgn_intCast, zpow_neg, ← inv_zpow, inv_neg_one]
  · have h' : ¬ ∃ m : ℤ, -x = m := by
      rintro ⟨m, hm⟩; exact h ⟨-m, by push_cast; linarith⟩
    unfold sgn
    rw [dif_neg h, dif_neg h']

lemma neg_one_zpow_add_two_mul (n k : ℤ) : (-1 : ℝ) ^ (n + 2 * k) = (-1 : ℝ) ^ n := by
  rw [zpow_add₀ (by norm_num), zpow_mul]; norm_num

lemma sgn_mul_self_of_int {x : ℚ} (h : ∃ m : ℤ, x = m) : sgn x * sgn x = 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [sgn_intCast, ← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num

/-! ### Reflection of the Racah sum -/

lemma term3_eq (j₁ j₂ j₃ m₁ m₂ σ : ℚ) (ε : ℝ) :
    term3 j₁ j₂ j₃ m₁ m₂ σ ε = ε * (ifa σ * ifa (j₁ + j₂ - j₃ - σ) * ifa (j₁ - m₁ - σ) *
      ifa (j₂ + m₂ - σ) * ifa (j₃ - j₂ + m₁ + σ) * ifa (j₃ - j₁ - m₂ + σ)) := by
  unfold term3
  rw [P6_vec]

lemma ifa_congr {x y : ℚ} (h : x = y) : ifa x = ifa y := by rw [h]

lemma finsum_reflect (F G : ℕ → ℝ) (M : ℕ) (hF : ∀ s, M < s → F s = 0)
    (hG : ∀ s, M < s → G s = 0) (c : ℝ) (h : ∀ s, s ≤ M → G (M - s) = c * F s) :
    ∑ᶠ s, G s = c * ∑ᶠ s, F s := by
  have sF : Function.support F ⊆ ↑(Finset.range (M + 1)) := by
    intro s hs
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hs (hF s (by omega))
  have sG : Function.support G ⊆ ↑(Finset.range (M + 1)) := by
    intro s hs
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hs (hG s (by omega))
  rw [finsum_eq_sum_of_support_subset _ sF, finsum_eq_sum_of_support_subset _ sG, Finset.mul_sum,
    ← Finset.sum_range_reflect G (M + 1)]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ M := by simp at hs; omega
  rw [show M + 1 - 1 - s = M - s by omega]
  exact h s hs'

lemma neg_one_pow_sub {s M : ℕ} (hs : s ≤ M) :
    (-1 : ℝ) ^ (M - s) = (-1 : ℝ) ^ M * (-1 : ℝ) ^ s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_sub_cancel_left, pow_add]
  have h : (-1 : ℝ) ^ s * (-1 : ℝ) ^ s = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(-1 : ℝ) ^ k) * h

lemma term3_zero_arg2 {j₁ j₂ j₃ m₁ m₂ : ℚ} {M s : ℕ} (hM : j₁ + j₂ - j₃ = M) (hs : M < s)
    (ε : ℝ) : term3 j₁ j₂ j₃ m₁ m₂ s ε = 0 := by
  rw [term3_eq, ifa_eq_zero_of_neg (x := j₁ + j₂ - j₃ - s)
    (by have : (M : ℚ) < s := by exact_mod_cast hs
        linarith)]
  ring

lemma term3_zero_arg3 {j₁ j₂ j₃ m₁ m₂ : ℚ} {M s : ℕ} (hM : j₁ - m₁ = M) (hs : M < s)
    (ε : ℝ) : term3 j₁ j₂ j₃ m₁ m₂ s ε = 0 := by
  rw [term3_eq, ifa_eq_zero_of_neg (x := j₁ - m₁ - s)
    (by have : (M : ℚ) < s := by exact_mod_cast hs
        linarith)]
  ring

lemma ifa_ne_zero_isNat {x : ℚ} (h : ifa x ≠ 0) : IsNat x := by
  by_contra hn
  apply h
  by_cases hx : ∃ n : ℤ, x = n
  · obtain ⟨n, rfl⟩ := hx
    rw [ifa_intCast]
    apply invFact_of_neg
    by_contra hge
    exact hn ⟨n.toNat, by
      have : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
      rw [← Int.cast_natCast, this]⟩
  · exact ifa_of_not_int hx

lemma term3_zero_of_not_isNat_arg2 {j₁ j₂ j₃ m₁ m₂ : ℚ} (hM : ¬ IsNat (j₁ + j₂ - j₃)) (s : ℕ)
    (ε : ℝ) : term3 j₁ j₂ j₃ m₁ m₂ s ε = 0 := by
  rw [term3_eq]
  by_cases h : ifa (j₁ + j₂ - j₃ - s) = 0
  · rw [h]; ring
  · exfalso
    obtain ⟨n, hn⟩ := ifa_ne_zero_isNat h
    exact hM ⟨n + s, by push_cast; linarith⟩

lemma term3_zero_of_not_isNat_arg3 {j₁ j₂ j₃ m₁ m₂ : ℚ} (hM : ¬ IsNat (j₁ - m₁)) (s : ℕ)
    (ε : ℝ) : term3 j₁ j₂ j₃ m₁ m₂ s ε = 0 := by
  rw [term3_eq]
  by_cases h : ifa (j₁ - m₁ - s) = 0
  · rw [h]; ring
  · exfalso
    obtain ⟨n, hn⟩ := ifa_ne_zero_isNat h
    exact hM ⟨n + s, by push_cast; linarith⟩

lemma racahSum3_eq_zero_of_term (j₁ j₂ j₃ m₁ m₂ : ℚ)
    (h : ∀ s : ℕ, term3 j₁ j₂ j₃ m₁ m₂ s ((-1 : ℝ) ^ s) = 0) : racahSum3 j₁ j₂ j₃ m₁ m₂ = 0 := by
  unfold racahSum3
  simp [h]

/-- Swapping the first two columns: pointwise identity under `σ ↦ M - σ`. -/
lemma term3_swap12 (j₁ j₂ j₃ m₁ m₂ M σ : ℚ) (hM : j₁ + j₂ - j₃ = M) (ε : ℝ) :
    term3 j₂ j₁ j₃ m₂ m₁ (M - σ) ε = term3 j₁ j₂ j₃ m₁ m₂ σ ε := by
  rw [term3_eq, term3_eq]
  rw [ifa_congr (x := M - σ) (y := j₁ + j₂ - j₃ - σ) (by rw [← hM]),
    ifa_congr (x := j₂ + j₁ - j₃ - (M - σ)) (y := σ) (by rw [← hM]; ring),
    ifa_congr (x := j₂ - m₂ - (M - σ)) (y := j₃ - j₁ - m₂ + σ) (by rw [← hM]; ring),
    ifa_congr (x := j₁ + m₁ - (M - σ)) (y := j₃ - j₂ + m₁ + σ) (by rw [← hM]; ring),
    ifa_congr (x := j₃ - j₁ + m₂ + (M - σ)) (y := j₂ + m₂ - σ) (by rw [← hM]; ring),
    ifa_congr (x := j₃ - j₂ - m₁ + (M - σ)) (y := j₁ - m₁ - σ) (by rw [← hM]; ring)]
  ring

/-- Negating all `m`: pointwise identity under `σ ↦ M - σ`. -/
lemma term3_neg (j₁ j₂ j₃ m₁ m₂ M σ : ℚ) (hM : j₁ + j₂ - j₃ = M) (ε : ℝ) :
    term3 j₁ j₂ j₃ (-m₁) (-m₂) (M - σ) ε = term3 j₁ j₂ j₃ m₁ m₂ σ ε := by
  rw [term3_eq, term3_eq]
  rw [ifa_congr (x := M - σ) (y := j₁ + j₂ - j₃ - σ) (by rw [← hM]),
    ifa_congr (x := j₁ + j₂ - j₃ - (M - σ)) (y := σ) (by rw [← hM]; ring),
    ifa_congr (x := j₁ - -m₁ - (M - σ)) (y := j₃ - j₂ + m₁ + σ) (by rw [← hM]; ring),
    ifa_congr (x := j₂ + -m₂ - (M - σ)) (y := j₃ - j₁ - m₂ + σ) (by rw [← hM]; ring),
    ifa_congr (x := j₃ - j₂ + -m₁ + (M - σ)) (y := j₁ - m₁ - σ) (by rw [← hM]; ring),
    ifa_congr (x := j₃ - j₁ - -m₂ + (M - σ)) (y := j₂ + m₂ - σ) (by rw [← hM]; ring)]
  ring

/-- Swapping columns 2 and 3 (with `m₃ = -m₁-m₂`): pointwise identity under `σ ↦ M - σ`. -/
lemma term3_swap23 (j₁ j₂ j₃ m₁ m₂ M σ : ℚ) (hM : j₁ - m₁ = M) (ε : ℝ) :
    term3 j₁ j₃ j₂ m₁ (-m₁ - m₂) (M - σ) ε = term3 j₁ j₂ j₃ m₁ m₂ σ ε := by
  rw [term3_eq, term3_eq]
  rw [ifa_congr (x := M - σ) (y := j₁ - m₁ - σ) (by rw [← hM]),
    ifa_congr (x := j₁ + j₃ - j₂ - (M - σ)) (y := j₃ - j₂ + m₁ + σ) (by rw [← hM]; ring),
    ifa_congr (x := j₁ - m₁ - (M - σ)) (y := σ) (by rw [← hM]; ring),
    ifa_congr (x := j₃ + (-m₁ - m₂) - (M - σ)) (y := j₃ - j₁ - m₂ + σ) (by rw [← hM]; ring),
    ifa_congr (x := j₂ - j₃ + m₁ + (M - σ)) (y := j₁ + j₂ - j₃ - σ) (by rw [← hM]; ring),
    ifa_congr (x := j₂ - j₁ - (-m₁ - m₂) + (M - σ)) (y := j₂ + m₂ - σ) (by rw [← hM]; ring)]
  ring

/-- Racah's sum under the swap of the first two columns. -/
lemma racahSum3_swap12 (j₁ j₂ j₃ m₁ m₂ : ℚ) :
    racahSum3 j₂ j₁ j₃ m₂ m₁ = sgn (j₁ + j₂ - j₃) * racahSum3 j₁ j₂ j₃ m₁ m₂ := by
  by_cases hN : IsNat (j₁ + j₂ - j₃)
  · obtain ⟨M, hM⟩ := hN
    have hM' : j₂ + j₁ - j₃ = M := by rw [← hM]; ring
    rw [hM, sgn_natCast]
    unfold racahSum3
    refine finsum_reflect _ _ M (fun s hs => term3_zero_arg2 hM hs _)
      (fun s hs => term3_zero_arg2 hM' hs _) _ (fun s hs => ?_)
    have e : ((M - s : ℕ) : ℚ) = (M : ℚ) - s := by push_cast [Nat.cast_sub hs]; ring
    rw [e, neg_one_pow_sub hs, term3_swap12 j₁ j₂ j₃ m₁ m₂ (M : ℚ) s hM, term3_eq, term3_eq]
    ring
  · have h' : ¬ IsNat (j₂ + j₁ - j₃) := by rwa [add_comm j₂ j₁]
    rw [racahSum3_eq_zero_of_term _ _ _ _ _ (fun s => term3_zero_of_not_isNat_arg2 h' s _),
      racahSum3_eq_zero_of_term _ _ _ _ _ (fun s => term3_zero_of_not_isNat_arg2 hN s _)]
    simp

/-- Racah's sum under negation of all `m`. -/
lemma racahSum3_neg (j₁ j₂ j₃ m₁ m₂ : ℚ) :
    racahSum3 j₁ j₂ j₃ (-m₁) (-m₂) = sgn (j₁ + j₂ - j₃) * racahSum3 j₁ j₂ j₃ m₁ m₂ := by
  by_cases hN : IsNat (j₁ + j₂ - j₃)
  · obtain ⟨M, hM⟩ := hN
    rw [hM, sgn_natCast]
    unfold racahSum3
    refine finsum_reflect _ _ M (fun s hs => term3_zero_arg2 hM hs _)
      (fun s hs => term3_zero_arg2 hM hs _) _ (fun s hs => ?_)
    have e : ((M - s : ℕ) : ℚ) = (M : ℚ) - s := by push_cast [Nat.cast_sub hs]; ring
    rw [e, neg_one_pow_sub hs, term3_neg j₁ j₂ j₃ m₁ m₂ (M : ℚ) s hM, term3_eq, term3_eq]
    ring
  · rw [racahSum3_eq_zero_of_term _ _ _ _ _ (fun s => term3_zero_of_not_isNat_arg2 hN s _),
      racahSum3_eq_zero_of_term _ _ _ _ _ (fun s => term3_zero_of_not_isNat_arg2 hN s _)]
    simp

/-- Racah's sum under the swap of columns 2 and 3. -/
lemma racahSum3_swap23 (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) (hm : m₁ + m₂ + m₃ = 0) :
    racahSum3 j₁ j₃ j₂ m₁ m₃ = sgn (j₁ - m₁) * racahSum3 j₁ j₂ j₃ m₁ m₂ := by
  have h3 : m₃ = -m₁ - m₂ := by linarith
  subst h3
  by_cases hN : IsNat (j₁ - m₁)
  · obtain ⟨M, hM⟩ := hN
    rw [hM, sgn_natCast]
    unfold racahSum3
    refine finsum_reflect _ _ M (fun s hs => term3_zero_arg3 hM hs _)
      (fun s hs => term3_zero_arg3 hM hs _) _ (fun s hs => ?_)
    have e : ((M - s : ℕ) : ℚ) = (M : ℚ) - s := by push_cast [Nat.cast_sub hs]; ring
    rw [e, neg_one_pow_sub hs, term3_swap23 j₁ j₂ j₃ m₁ m₂ (M : ℚ) s hM, term3_eq, term3_eq]
    ring
  · rw [racahSum3_eq_zero_of_term _ _ _ _ _ (fun s => term3_zero_of_not_isNat_arg3 hN s _),
      racahSum3_eq_zero_of_term _ _ _ _ _ (fun s => term3_zero_of_not_isNat_arg3 hN s _)]
    simp

/-! ### Sign bookkeeping -/

lemma sign_swap12 {j₁ j₂ j₃ m₃ : ℚ} (h3p : IsNat (j₃ + m₃)) (h3m : IsNat (j₃ - m₃)) :
    sgn (j₂ - j₁ - m₃) * sgn (j₁ + j₂ - j₃) = sgn (j₁ + j₂ + j₃) * sgn (j₁ - j₂ - m₃) := by
  obtain ⟨p, hp⟩ := h3p
  obtain ⟨q, hq⟩ := h3m
  have e1 : j₂ - j₁ - m₃ = -((j₁ - j₂ - m₃) + (((p : ℤ) - (q : ℤ) : ℤ) : ℚ)) := by
    push_cast; linarith
  have e2 : j₁ + j₂ + j₃ = (j₁ + j₂ - j₃) + (((p : ℤ) + (q : ℤ) : ℤ) : ℚ) := by
    push_cast; linarith
  rw [e1, sgn_neg', sgn_add_int, e2, sgn_add_int,
    show (p : ℤ) + q = ((p : ℤ) - q) + 2 * q by ring, neg_one_zpow_add_two_mul]
  ring

lemma sign_swap23 {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (hm : m₁ + m₂ + m₃ = 0) (h2m : IsNat (j₂ - m₂))
    (h3m : IsNat (j₃ - m₃)) :
    sgn (j₁ - j₃ - m₂) * sgn (j₁ - m₁) = sgn (j₁ + j₂ + j₃) * sgn (j₁ - j₂ - m₃) := by
  obtain ⟨p, hp⟩ := h2m
  obtain ⟨q, hq⟩ := h3m
  have e1 : j₁ - j₃ - m₂ = (j₁ - j₂ - m₃) + (((p : ℤ) - (q : ℤ) : ℤ) : ℚ) := by
    push_cast; linarith
  have e2 : j₁ + j₂ + j₃ = (j₁ - m₁) + (((p : ℤ) + (q : ℤ) : ℤ) : ℚ) := by
    push_cast; linarith
  rw [e1, sgn_add_int, e2, sgn_add_int,
    show (p : ℤ) + q = ((p : ℤ) - q) + 2 * q by ring, neg_one_zpow_add_two_mul]
  ring

lemma isNat_of_fq_ne {x : ℚ} (h : fq x ≠ 0) : IsNat x := by
  by_contra hn
  exact h (fq_of_not_isNat hn)

lemma prefactor_isNat {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ}
    (h : Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁) * fq (j₂ + m₂) *
      fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) ≠ 0) :
    IsTri j₁ j₂ j₃ ∧ IsNat (j₁ + m₁) ∧ IsNat (j₁ - m₁) ∧ IsNat (j₂ + m₂) ∧ IsNat (j₂ - m₂) ∧
      IsNat (j₃ + m₃) ∧ IsNat (j₃ - m₃) := by
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  have t1 : triSq j₁ j₂ j₃ ≠ 0 := fun e => h1 (by rw [e, Real.sqrt_zero])
  have t2 : fq (j₁ + m₁) * fq (j₁ - m₁) * fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) *
      fq (j₃ - m₃) ≠ 0 := fun e => h2 (by rw [e, Real.sqrt_zero])
  unfold triSq at t1
  simp only [ne_eq, mul_eq_zero, not_or] at t1 t2
  obtain ⟨⟨⟨a, b⟩, c⟩, _⟩ := t1
  obtain ⟨⟨⟨⟨⟨d, e⟩, f⟩, g⟩, i⟩, k⟩ := t2
  exact ⟨⟨isNat_of_fq_ne a, isNat_of_fq_ne b, isNat_of_fq_ne c⟩, isNat_of_fq_ne d,
    isNat_of_fq_ne e, isNat_of_fq_ne f, isNat_of_fq_ne g, isNat_of_fq_ne i, isNat_of_fq_ne k⟩

/-! ### The symmetries -/

/-- **DLMF 34.3.9** (swap of columns 1 and 2): odd permutations multiply the `3j` symbol by
`(-1)^(j₁+j₂+j₃)`; `sgn` is the zero-extended sign, and the symbol vanishes unless `j₁+j₂+j₃` is
an integer. -/
theorem threeJ_swap12 (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    threeJ j₂ j₁ j₃ m₂ m₁ m₃ = sgn (j₁ + j₂ + j₃) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  unfold threeJ
  by_cases hm : m₁ + m₂ + m₃ = 0
  · rw [if_pos (by linarith : m₂ + m₁ + m₃ = 0), if_pos hm, triSq_comm12 j₂ j₁ j₃,
      racahSum3_swap12,
      show fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₁ + m₁) * fq (j₁ - m₁) * fq (j₃ + m₃) *
        fq (j₃ - m₃) = fq (j₁ + m₁) * fq (j₁ - m₁) * fq (j₂ + m₂) * fq (j₂ - m₂) *
          fq (j₃ + m₃) * fq (j₃ - m₃) by ring]
    by_cases hT : Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁) *
        fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) = 0
    · rcases mul_eq_zero.mp hT with h | h <;> simp [h]
    · obtain ⟨-, -, -, -, -, h3p, h3m⟩ := prefactor_isNat hT
      have key := sign_swap12 (j₁ := j₁) (j₂ := j₂) h3p h3m
      linear_combination (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁) *
        fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) *
          racahSum3 j₁ j₂ j₃ m₁ m₂) * key
  · rw [if_neg (by intro h; apply hm; linarith), if_neg hm]; simp

/-- **DLMF 34.3.9** (swap of columns 2 and 3). -/
theorem threeJ_swap23 (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    threeJ j₁ j₃ j₂ m₁ m₃ m₂ = sgn (j₁ + j₂ + j₃) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  unfold threeJ
  by_cases hm : m₁ + m₂ + m₃ = 0
  · rw [if_pos (by linarith : m₁ + m₃ + m₂ = 0), if_pos hm, triSq_comm23 j₁ j₃ j₂,
      racahSum3_swap23 j₁ j₂ j₃ m₁ m₂ m₃ hm,
      show fq (j₁ + m₁) * fq (j₁ - m₁) * fq (j₃ + m₃) * fq (j₃ - m₃) * fq (j₂ + m₂) *
        fq (j₂ - m₂) = fq (j₁ + m₁) * fq (j₁ - m₁) * fq (j₂ + m₂) * fq (j₂ - m₂) *
          fq (j₃ + m₃) * fq (j₃ - m₃) by ring]
    by_cases hT : Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁) *
        fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) = 0
    · rcases mul_eq_zero.mp hT with h | h <;> simp [h]
    · obtain ⟨-, -, -, -, h2m, -, h3m⟩ := prefactor_isNat hT
      have key := sign_swap23 (j₁ := j₁) hm h2m h3m
      linear_combination (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁) *
        fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) *
          racahSum3 j₁ j₂ j₃ m₁ m₂) * key
  · rw [if_neg (by intro h; apply hm; linarith), if_neg hm]; simp

/-- **DLMF 34.3.10** (negation of all projections). -/
theorem threeJ_neg (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    threeJ j₁ j₂ j₃ (-m₁) (-m₂) (-m₃) = sgn (j₁ + j₂ + j₃) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  unfold threeJ
  by_cases hm : m₁ + m₂ + m₃ = 0
  · rw [if_pos (by linarith : -m₁ + -m₂ + -m₃ = 0), if_pos hm, racahSum3_neg,
      show fq (j₁ + -m₁) * fq (j₁ - -m₁) * fq (j₂ + -m₂) * fq (j₂ - -m₂) * fq (j₃ + -m₃) *
        fq (j₃ - -m₃) = fq (j₁ + m₁) * fq (j₁ - m₁) * fq (j₂ + m₂) * fq (j₂ - m₂) *
          fq (j₃ + m₃) * fq (j₃ - m₃) by
        simp only [← sub_eq_add_neg, sub_neg_eq_add]; ring]
    by_cases hT : Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁) *
        fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) = 0
    · rcases mul_eq_zero.mp hT with h | h <;> simp [h]
    · obtain ⟨-, -, -, -, -, h3p, h3m⟩ := prefactor_isNat hT
      have key := sign_swap12 (j₁ := j₁) (j₂ := j₂) h3p h3m
      rw [show j₂ - j₁ - m₃ = -(j₁ - j₂ - -m₃) by ring, sgn_neg'] at key
      linear_combination (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁) *
        fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) *
          racahSum3 j₁ j₂ j₃ m₁ m₂) * key
  · rw [if_neg (by intro h; apply hm; linarith), if_neg hm]; simp

lemma isInt_sum_of_ne_zero {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (h : threeJ j₁ j₂ j₃ m₁ m₂ m₃ ≠ 0) :
    ∃ n : ℤ, j₁ + j₂ + j₃ = n := by
  unfold threeJ at h
  by_cases hm : m₁ + m₂ + m₃ = 0
  · rw [if_pos hm] at h
    have h1 := left_ne_zero_of_mul (left_ne_zero_of_mul h)
    have h2 := left_ne_zero_of_mul h1
    have h3 := right_ne_zero_of_mul h1
    have t1 : triSq j₁ j₂ j₃ ≠ 0 := fun e => h3 (by rw [e, Real.sqrt_zero])
    unfold triSq at t1
    simp only [ne_eq, mul_eq_zero, not_or] at t1
    obtain ⟨⟨⟨a, b⟩, c⟩, _⟩ := t1
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ : IsTri j₁ j₂ j₃ :=
      ⟨isNat_of_fq_ne a, isNat_of_fq_ne b, isNat_of_fq_ne c⟩
    exact ⟨(x : ℤ) + y + z, by push_cast; linarith⟩
  · rw [if_neg hm] at h; exact absurd rfl h

lemma sgn_sum_sq (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    sgn (j₁ + j₂ + j₃) * sgn (j₁ + j₂ + j₃) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ =
      threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  by_cases h : threeJ j₁ j₂ j₃ m₁ m₂ m₃ = 0
  · rw [h]; ring
  · rw [sgn_mul_self_of_int (isInt_sum_of_ne_zero h)]; ring

/-- **DLMF 34.3.8** (cyclic permutation of the columns). -/
theorem threeJ_cyc (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    threeJ j₂ j₃ j₁ m₂ m₃ m₁ = threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  rw [show threeJ j₂ j₃ j₁ m₂ m₃ m₁ = sgn (j₂ + j₁ + j₃) * threeJ j₂ j₁ j₃ m₂ m₁ m₃ from
    threeJ_swap23 j₂ j₁ j₃ m₂ m₁ m₃, threeJ_swap12, ← mul_assoc,
    show j₂ + j₁ + j₃ = j₁ + j₂ + j₃ by ring, sgn_sum_sq]

/-- **DLMF 34.3.8** (cyclic permutation of the columns, other direction). -/
theorem threeJ_cyc' (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    threeJ j₃ j₁ j₂ m₃ m₁ m₂ = threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  rw [show threeJ j₃ j₁ j₂ m₃ m₁ m₂ = sgn (j₁ + j₃ + j₂) * threeJ j₁ j₃ j₂ m₁ m₃ m₂ from
    threeJ_swap12 j₁ j₃ j₂ m₁ m₃ m₂, threeJ_swap23, ← mul_assoc,
    show j₁ + j₃ + j₂ = j₁ + j₂ + j₃ by ring, sgn_sum_sq]

/-- **DLMF 34.3.9** (swap of columns 1 and 3). -/
theorem threeJ_swap13 (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) :
    threeJ j₃ j₂ j₁ m₃ m₂ m₁ = sgn (j₁ + j₂ + j₃) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  rw [show threeJ j₃ j₂ j₁ m₃ m₂ m₁ = sgn (j₃ + j₁ + j₂) * threeJ j₃ j₁ j₂ m₃ m₁ m₂ from
    threeJ_swap23 j₃ j₁ j₂ m₃ m₁ m₂, threeJ_cyc', show j₃ + j₁ + j₂ = j₁ + j₂ + j₃ by ring]

/-- `threeJ` vanishes when `j₁ + j₂ + j₃` is not an integer. -/
theorem threeJ_eq_zero_of_not_int {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (h : ¬ ∃ n : ℤ, j₁ + j₂ + j₃ = n) :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ = 0 :=
  by_contra fun hne => h (isInt_sum_of_ne_zero hne)

/-- info: 'FormalResearch.Wigner.threeJ_swap12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_swap12

/-- info: 'FormalResearch.Wigner.threeJ_swap23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_swap23

/-- info: 'FormalResearch.Wigner.threeJ_swap13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_swap13

/-- info: 'FormalResearch.Wigner.threeJ_cyc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_cyc

/-- info: 'FormalResearch.Wigner.threeJ_cyc'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_cyc'

/-- info: 'FormalResearch.Wigner.threeJ_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_neg

end FormalResearch.Wigner
