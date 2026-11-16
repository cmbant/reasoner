module

public import FormalResearch.Special.AiryFirstZeros

/-!
# The ordered zeros `a_1 > a_2 > …` of `Ai`

`airyZeroCount x` is the number of zeros of `Ai` in `(x, 0]` (finite: `IsPruferLift.zeros_finite`).  For a zero `z ≤ 0`
the count is `-k` where `θ z = kπ` for the (normalised) Prüfer angle, so it is strictly decreasing along the zeros
and takes every value `k ∈ ℕ` exactly once on the zeros (`airy_node_exists_unique`, `airy_zeros_ncard`).  Hence

* `airyZero n` (`n ≥ 1`) **is the unique zero `a_n` of `Ai` with exactly `n - 1` zeros in `(a_n, 0]`**, i.e. the
  `n`-th zero counted from the origin (for `n = 0` the junk value `a_1`);
* `airyZero_strictAnti`: `a_{n+1} < a_n`; `airyZero_next`: every zero `z < a_n` satisfies `z ≤ a_{n+1}`;
  `exists_airyZero_eq`: every zero `z ≤ 0` is `a_n` for `n = #(zeros in (z, 0]) + 1`;
* `airyZero_one`: `a_1 ∈ (-2.35, -2.33)`; `airyZero_two`: `a_2 ∈ (-4.84, -4)`; `airyZero_three`: `a_3 < -4.84`;
  consequently `Ai` has exactly one zero in `(-4, 0]` and exactly two in `(-4.84, 0]`
  (`airyZeroCount_neg_four`, `airyZeroCount_neg_484`) — the finite count of `AiryFirstZeros`.

All proved (the numerical input is `AiryFirstZeros`).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special

open SturmAiry

/-- The set of zeros of `Ai` in `(x, 0]`. -/
def airyZeroSet (x : ℝ) : Set ℝ := {t | t ∈ Ioc x 0 ∧ airyAi t = 0}

/-- The number of zeros of `Ai` in `(x, 0]`. -/
noncomputable def airyZeroCount (x : ℝ) : ℕ := (airyZeroSet x).ncard

lemma airyZeroSet_finite (x : ℝ) : (airyZeroSet x).Finite := by
  obtain ⟨θ, hθ, -⟩ := airy_exists_prufer
  exact hθ.zeros_finite x 0

/-- Along the zeros the count strictly decreases: `z < z'` zeros, `z' ≤ 0` give `count z' < count z`. -/
lemma airyZeroCount_lt {z z' : ℝ} (hz' : airyAi z' = 0) (hz'0 : z' ≤ 0) (h : z < z') :
    airyZeroCount z' < airyZeroCount z := by
  unfold airyZeroCount
  refine Set.ncard_lt_ncard ?_ (airyZeroSet_finite z)
  refine ⟨fun t ht => ⟨⟨h.trans ht.1.1, ht.1.2⟩, ht.2⟩, fun hsub => ?_⟩
  have := hsub (show z' ∈ airyZeroSet z from ⟨⟨h, hz'0⟩, hz'⟩)
  exact lt_irrefl _ this.1.1

/-- Every count `k` is attained by a zero `≤ 0`. -/
lemma exists_zero_count (k : ℕ) : ∃ z : ℝ, z ≤ 0 ∧ airyAi z = 0 ∧ airyZeroCount z = k := by
  obtain ⟨θ, hθ, hlo, hhi, -⟩ := airy_exists_prufer
  have hpi := Real.pi_pos
  have hm : (0 : ℝ) + ((-(k : ℤ) : ℤ) : ℝ) * Real.pi ≤ θ 0 := by
    push_cast; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  obtain ⟨z, ⟨hz0, hzθ, hzc⟩, -⟩ := airy_node_exists_unique hθ hm
  have hzAi : airyAi z = 0 := by simpa [combo] using hzc
  refine ⟨z, hz0, hzAi, ?_⟩
  have hc := airy_zeros_ncard hθ (by linarith) hhi hz0
  have hfl : ⌊θ z / Real.pi⌋ = -(k : ℤ) := by
    rw [hzθ, zero_add]
    have : (((-(k : ℤ) : ℤ) : ℝ) * Real.pi) / Real.pi = ((-(k : ℤ) : ℤ) : ℝ) := by field_simp
    rw [this, Int.floor_intCast]
  rw [hfl] at hc
  unfold airyZeroCount airyZeroSet
  have : (((({t | t ∈ Ioc z 0 ∧ airyAi t = 0}).ncard : ℕ)) : ℤ) = k := by simpa using hc
  exact_mod_cast this

/-- Two zeros `≤ 0` with the same count coincide. -/
lemma airyZero_eq_of_count_eq {z z' : ℝ} (hz : airyAi z = 0) (hz0 : z ≤ 0) (hz' : airyAi z' = 0)
    (hz'0 : z' ≤ 0) (h : airyZeroCount z = airyZeroCount z') : z = z' := by
  rcases lt_trichotomy z z' with hlt | heq | hgt
  · have := airyZeroCount_lt hz' hz'0 hlt; omega
  · exact heq
  · have := airyZeroCount_lt hz hz0 hgt; omega

/-- **The ordered zeros** `a_1 > a_2 > …` of `Ai`: `airyZero n` (`n ≥ 1`) is the unique zero `a_n ≤ 0` with exactly
`n - 1` zeros in `(a_n, 0]`.  (`airyZero 0 = a_1` is a junk value.) -/
noncomputable def airyZero (n : ℕ) : ℝ := Classical.choose (exists_zero_count (n - 1))

lemma airyZero_nonpos (n : ℕ) : airyZero n ≤ 0 :=
  (Classical.choose_spec (exists_zero_count (n - 1))).1

/-- `Ai (a_n) = 0`. -/
theorem airyAi_airyZero (n : ℕ) : airyAi (airyZero n) = 0 :=
  (Classical.choose_spec (exists_zero_count (n - 1))).2.1

/-- `a_n` has exactly `n - 1` zeros in `(a_n, 0]`. -/
theorem airyZeroCount_airyZero (n : ℕ) : airyZeroCount (airyZero n) = n - 1 :=
  (Classical.choose_spec (exists_zero_count (n - 1))).2.2

/-- Characterisation: a zero `z ≤ 0` with `n - 1` zeros in `(z, 0]` is `a_n`. -/
theorem eq_airyZero {n : ℕ} {z : ℝ} (hz : airyAi z = 0) (hz0 : z ≤ 0) (hc : airyZeroCount z = n - 1) :
    z = airyZero n :=
  airyZero_eq_of_count_eq hz hz0 (airyAi_airyZero n) (airyZero_nonpos n)
    (by rw [hc, airyZeroCount_airyZero])

/-- **Strict monotonicity**: `a_{n+1} < a_n` (`n ≥ 1`). -/
theorem airyZero_strictAnti {n : ℕ} (hn : 1 ≤ n) : airyZero (n + 1) < airyZero n := by
  rcases lt_trichotomy (airyZero (n + 1)) (airyZero n) with h | h | h
  · exact h
  · have := airyZeroCount_airyZero (n + 1); rw [h, airyZeroCount_airyZero] at this; omega
  · have := airyZeroCount_lt (airyAi_airyZero (n + 1)) (airyZero_nonpos _) h
    rw [airyZeroCount_airyZero, airyZeroCount_airyZero] at this; omega

/-- **Next zero**: every zero `z < a_n` satisfies `z ≤ a_{n+1}` (`n ≥ 1`). -/
theorem airyZero_next {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz : airyAi z = 0) (hzn : z < airyZero n) :
    z ≤ airyZero (n + 1) := by
  by_contra hcon
  push Not at hcon
  have hz0 : z ≤ 0 := hzn.le.trans (airyZero_nonpos n)
  have h1 := airyZeroCount_lt hz hz0 hcon |>.trans_eq (airyZeroCount_airyZero (n + 1)) |>.trans_eq rfl
  have h2 := airyZeroCount_lt (airyAi_airyZero n) (airyZero_nonpos n) hzn
  rw [airyZeroCount_airyZero] at h2
  omega

/-- Every zero `z ≤ 0` of `Ai` is some `a_n`, `n ≥ 1`. -/
theorem exists_airyZero_eq {z : ℝ} (hz : airyAi z = 0) (hz0 : z ≤ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ z = airyZero n :=
  ⟨airyZeroCount z + 1, by omega, eq_airyZero hz hz0 (by omega)⟩

/-- `a_n < 0`. -/
lemma airyZero_neg (n : ℕ) : airyZero n < 0 := by
  refine lt_of_le_of_ne (airyZero_nonpos n) fun h => ?_
  have := airyAi_airyZero n
  rw [h] at this
  exact (airyAi_pos le_rfl).ne' this

/-- The antitone sequence: `a_m < a_n` for `1 ≤ n < m`. -/
theorem airyZero_lt_of_lt {n m : ℕ} (hn : 1 ≤ n) (h : n < m) : airyZero m < airyZero n := by
  induction m, h using Nat.le_induction with
  | base => exact airyZero_strictAnti hn
  | succ m hm ih => exact (airyZero_strictAnti (by omega)).trans ih

section Values

/-- `a_1 ∈ (-2.35, -2.33)` and `a_2 ∈ (-4.84, -4)`, `a_3 < -4.84`, with the zero set in `[-4.84, 0]` equal
to `{a_1, a_2}`. -/
lemma airyZero_first_values :
    -2.35 < airyZero 1 ∧ airyZero 1 < -2.33 ∧ -4.84 < airyZero 2 ∧ airyZero 2 < -4 ∧
      airyZero 3 < -4.84 ∧
      ∀ z : ℝ, -4.84 ≤ z → z ≤ 0 → airyAi z = 0 → z = airyZero 1 ∨ z = airyZero 2 := by
  obtain ⟨a, w, ha1, ha2, hw1, hw2, ha0, hw0, hcl⟩ := airy_zeros_Icc
  -- counts of a and w
  have hca : airyZeroCount a = 0 := by
    unfold airyZeroCount airyZeroSet
    have : {t | t ∈ Ioc a 0 ∧ airyAi t = 0} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro ht ht0
      rcases hcl t (by linarith [ht.1]) ht.2 ht0 with h | h
      · exact lt_irrefl _ (h ▸ ht.1)
      · linarith [ht.1]
    rw [this]; simp
  have hcw : airyZeroCount w = 1 := by
    unfold airyZeroCount airyZeroSet
    have : {t | t ∈ Ioc w 0 ∧ airyAi t = 0} = {a} := by
      ext t
      simp only [Set.mem_ofPred_eq, mem_singleton_iff]
      constructor
      · rintro ⟨ht, ht0⟩
        rcases hcl t (by linarith [ht.1]) ht.2 ht0 with h | h
        · exact h
        · exact absurd h (ne_of_gt ht.1)
      · rintro rfl; exact ⟨⟨by linarith, by linarith⟩, ha0⟩
    rw [this]; simp
  have e1 : a = airyZero 1 := eq_airyZero ha0 (by linarith) (by simpa using hca)
  have e2 : w = airyZero 2 := eq_airyZero hw0 (by linarith) (by simpa using hcw)
  have h3 : airyZero 3 < -4.84 := by
    by_contra hcon
    push Not at hcon
    have h31 : airyZero 3 < airyZero 1 := airyZero_lt_of_lt (by norm_num) (by norm_num)
    have h32 : airyZero 3 < airyZero 2 := airyZero_lt_of_lt (by norm_num) (by norm_num)
    rcases hcl (airyZero 3) hcon (airyZero_nonpos 3) (airyAi_airyZero 3) with h | h <;> linarith
  refine ⟨e1 ▸ ha1, e1 ▸ ha2, e2 ▸ hw1, e2 ▸ hw2, h3, fun z hz1 hz2 hz0 => ?_⟩
  rcases hcl z hz1 hz2 hz0 with h | h
  · exact Or.inl (h.trans e1)
  · exact Or.inr (h.trans e2)

theorem airyZero_one : -2.35 < airyZero 1 ∧ airyZero 1 < -2.33 :=
  ⟨airyZero_first_values.1, airyZero_first_values.2.1⟩

theorem airyZero_two : -4.84 < airyZero 2 ∧ airyZero 2 < -4 :=
  ⟨airyZero_first_values.2.2.1, airyZero_first_values.2.2.2.1⟩

theorem airyZero_three : airyZero 3 < -4.84 := airyZero_first_values.2.2.2.2.1

/-- **Exactly one zero in `(-4, 0]`.** -/
theorem airyZeroCount_neg_four : airyZeroCount (-4) = 1 := by
  obtain ⟨h1, h2, -, h4, -, hcl⟩ := airyZero_first_values
  unfold airyZeroCount airyZeroSet
  have : {t | t ∈ Ioc (-4 : ℝ) 0 ∧ airyAi t = 0} = {airyZero 1} := by
    ext t
    simp only [Set.mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨ht, ht0⟩
      rcases hcl t (by linarith [ht.1]) ht.2 ht0 with h | h
      · exact h
      · rw [h] at ht; linarith [ht.1]
    · rintro rfl; exact ⟨⟨by linarith, by linarith⟩, airyAi_airyZero 1⟩
  rw [this]; simp

/-- **Exactly two zeros in `(-4.84, 0]`.** -/
theorem airyZeroCount_neg_484 : airyZeroCount (-4.84) = 2 := by
  obtain ⟨h1, h2, h3, h4, -, hcl⟩ := airyZero_first_values
  unfold airyZeroCount airyZeroSet
  have hne : airyZero 1 ≠ airyZero 2 := by intro h; linarith
  have : {t | t ∈ Ioc (-4.84 : ℝ) 0 ∧ airyAi t = 0} = {airyZero 1, airyZero 2} := by
    ext t
    simp only [Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨ht, ht0⟩
      exact hcl t ht.1.le ht.2 ht0
    · rintro (rfl | rfl)
      · exact ⟨⟨by linarith, by linarith⟩, airyAi_airyZero 1⟩
      · exact ⟨⟨h3, by linarith⟩, airyAi_airyZero 2⟩
  rw [this, Set.ncard_pair hne]

end Values

/-- info: 'FormalResearch.Special.airyZero_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_strictAnti

/-- info: 'FormalResearch.Special.airyZero_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZero_next

/-- info: 'FormalResearch.Special.airyZeroCount_neg_484' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyZeroCount_neg_484

end FormalResearch.Special
