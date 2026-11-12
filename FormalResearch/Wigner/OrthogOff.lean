module

public import FormalResearch.Wigner.OrthogRec
public import FormalResearch.Wigner.OrthogAbs
public import FormalResearch.Wigner.SpecialValues

/-!
# Off-diagonal orthogonality of `6j` symbols (DLMF 34.5.14, `l₃ ≠ l₃'` part)

For fixed `a b c d` the function `x ↦ sixJ x a b μ c d` solves, in the summation variable `x`, the
three-term recurrence `sixJ_recurrence_ext` with spectral parameter `μ(μ+1)`.  Green's identity
(`green_lsum`) then shows `∑ₓ (2x+1) {x a b; μ c d} {x a b; μ' c d} = 0` unless `μ(μ+1) = μ'(μ'+1)`.
The one value that the recurrence does not control, `x = 0` (possible only for `a = b`, `c = d`),
is supplied by the special values `{μ c a; 0 a c}` and `{μ c a; 1 a c}`.
-/

@[expose] public section

namespace FormalResearch.Wigner

lemma IsTri.nonneg_first {y a b : ℚ} (h : IsTri y a b) : 0 ≤ y := by
  obtain ⟨⟨n, hn⟩, ⟨m, hm⟩, -⟩ := h
  have : (0 : ℚ) ≤ n + m := by positivity
  linarith

lemma IsTri.comm23 {a b c : ℚ} (h : IsTri a b c) : IsTri a c b := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · convert h2 using 1; ring
  · convert h1 using 1; ring
  · convert h3 using 1; ring

lemma sixJ_eq_zero_of_not_tri3 {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : ¬ IsTri l₁ l₂ j₃) :
    sixJ j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  rw [sixJ_factor, triSq_eq_zero_of_not_isTri h]; simp

lemma sixJ_eq_zero_of_not_tri4 {j₁ j₂ j₃ l₁ l₂ l₃ : ℚ} (h : ¬ IsTri l₁ j₂ l₃) :
    sixJ j₁ j₂ j₃ l₁ l₂ l₃ = 0 := by
  rw [sixJ_factor, triSq_eq_zero_of_not_isTri h]; simp

lemma not_isTri_one_zero : ¬ IsTri 1 0 0 := by
  rintro ⟨-, -, ⟨n, hn⟩⟩
  have : (0 : ℚ) ≤ n := by positivity
  linarith

lemma not_isTri_succ_top {a b : ℚ} : ¬ IsTri (a + b + 1) a b := by
  rintro ⟨-, -, ⟨n, hn⟩⟩
  have : (0 : ℚ) ≤ n := by positivity
  linarith

/-- The value `{x a a; μ c c}` at `x = 0`: `DLMF 34.5.1`. -/
lemma sixJ_zero_x {a c ν : ℚ} (h : IsTri ν c a) :
    ∃ N : ℕ, (N : ℚ) = ν + c + a ∧
      sixJ 0 a a ν c c = (-1 : ℝ) ^ N / Real.sqrt ((2 * (c : ℝ) + 1) * (2 * (a : ℝ) + 1)) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := h
  refine ⟨p + q + r, by push_cast; linarith, ?_⟩
  rw [← sixJ_exch12 0 a a ν c c]
  exact sixJ_zero_left ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ (p + q + r) (by push_cast; linarith)

/-- The value `{1 a a; μ c c}`: `DLMF 34.5.7`. -/
lemma sixJ_one_x {a c ν : ℚ} (h : IsTri ν c a) (ha : 1 ≤ 2 * a) (hc : 1 ≤ 2 * c) :
    ∃ N : ℕ, (N : ℚ) = ν + c + a ∧
      sixJ 1 a a ν c c = (-1 : ℝ) ^ (N + 1) *
        (2 * ((c : ℝ) * (c + 1) + a * (a + 1) - ν * (ν + 1))) /
        Real.sqrt ((2 * (c : ℝ)) * (2 * c + 1) * (2 * c + 2) *
          ((2 * (a : ℝ)) * (2 * a + 1) * (2 * a + 2))) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := h
  refine ⟨p + q + r, by push_cast; linarith, ?_⟩
  rw [← sixJ_exch12 1 a a ν c c]
  exact sixJ_one_left ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ (p + q + r) (by push_cast; linarith) hc ha

/-- The cross identity at `x = 0` for `a = b`, `c = d`. -/
lemma cross_zero_special {a c μ μ' : ℚ} (h : IsTri μ c a) (h' : IsTri μ' c a) :
    2 * ((μ : ℝ) * (μ + 1) - μ' * (μ' + 1)) *
        (sixJ 0 a a μ c c * sixJ 0 a a μ' c c) =
      E6 a a c c ((1 : ℚ) : ℝ) *
        (sixJ 1 a a μ c c * sixJ 0 a a μ' c c - sixJ 1 a a μ' c c * sixJ 0 a a μ c c) := by
  obtain ⟨N, hN, h0⟩ := sixJ_zero_x h
  obtain ⟨N', hN', h0'⟩ := sixJ_zero_x h'
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := h
  obtain ⟨⟨p', hp'⟩, ⟨q', hq'⟩, ⟨r', hr'⟩⟩ := h'
  have ha2 : 2 * a = ((q + r : ℕ) : ℚ) := by push_cast; linarith
  have hc2 : 2 * c = ((p + r : ℕ) : ℚ) := by push_cast; linarith
  by_cases hd : a = 0 ∨ c = 0
  · have hz : sixJ 1 a a μ c c = 0 ∧ sixJ 1 a a μ' c c = 0 := by
      have hn : ¬ (IsTri 1 a a ∧ IsTri 1 c c) := by
        rintro ⟨h1, h2⟩
        rcases hd with rfl | rfl
        · exact not_isTri_one_zero h1
        · exact not_isTri_one_zero h2
      exact ⟨sixJ_eq_zero_of_not_tri12 hn, sixJ_eq_zero_of_not_tri12 hn⟩
    have hμ : μ = μ' := by
      rcases hd with rfl | rfl
      · have : (0 : ℚ) ≤ q := by positivity
        have : (0 : ℚ) ≤ r := by positivity
        have : (0 : ℚ) ≤ q' := by positivity
        have : (0 : ℚ) ≤ r' := by positivity
        linarith
      · have : (0 : ℚ) ≤ p := by positivity
        have : (0 : ℚ) ≤ r := by positivity
        have : (0 : ℚ) ≤ p' := by positivity
        have : (0 : ℚ) ≤ r' := by positivity
        linarith
    subst hμ
    simp [hz.1]
  push Not at hd
  have hA : 1 ≤ 2 * a := by
    have hne : q + r ≠ 0 := by
      intro h0
      apply hd.1
      have : ((q + r : ℕ) : ℚ) = 0 := by exact_mod_cast h0
      linarith
    have : 1 ≤ q + r := Nat.one_le_iff_ne_zero.mpr hne
    have : (1 : ℚ) ≤ ((q + r : ℕ) : ℚ) := by exact_mod_cast this
    linarith
  have hC : 1 ≤ 2 * c := by
    have hne : p + r ≠ 0 := by
      intro h0
      apply hd.2
      have : ((p + r : ℕ) : ℚ) = 0 := by exact_mod_cast h0
      linarith
    have : 1 ≤ p + r := Nat.one_le_iff_ne_zero.mpr hne
    have : (1 : ℚ) ≤ ((p + r : ℕ) : ℚ) := by exact_mod_cast this
    linarith
  obtain ⟨M, hM, h1⟩ := sixJ_one_x ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ hA hC
  obtain ⟨M', hM', h1'⟩ := sixJ_one_x ⟨⟨p', hp'⟩, ⟨q', hq'⟩, ⟨r', hr'⟩⟩ hA hC
  have hMN : M = N := by
    have : (M : ℚ) = N := by rw [hM, hN]
    exact_mod_cast this
  have hMN' : M' = N' := by
    have : (M' : ℚ) = N' := by rw [hM', hN']
    exact_mod_cast this
  subst hMN hMN'
  have hA' : (1 : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hA
  have hC' : (1 : ℝ) ≤ 2 * (c : ℝ) := by exact_mod_cast hC
  set u := Real.sqrt ((2 * (c : ℝ) + 1) * (2 * (a : ℝ) + 1)) with hu
  have hDz : 0 < (2 * (c : ℝ) + 1) * (2 * (a : ℝ) + 1) := by positivity
  have hu0 : 0 < u := Real.sqrt_pos.mpr hDz
  have hP : 0 < ((2 * (a : ℝ)) * (2 * a + 2)) * ((2 * (c : ℝ)) * (2 * c + 2)) := by positivity
  have hE : E6 a a c c ((1 : ℚ) : ℝ) = Real.sqrt (((2 * (a : ℝ)) * (2 * a + 2)) *
      ((2 * (c : ℝ)) * (2 * c + 2))) := by
    unfold E6
    congr 1
    push_cast
    ring
  have hD1 : (2 * (c : ℝ)) * (2 * c + 1) * (2 * c + 2) *
      ((2 * (a : ℝ)) * (2 * a + 1) * (2 * a + 2)) =
      ((2 * (c : ℝ) + 1) * (2 * (a : ℝ) + 1)) *
        (((2 * (a : ℝ)) * (2 * a + 2)) * ((2 * (c : ℝ)) * (2 * c + 2))) := by ring
  have hs1 : Real.sqrt ((2 * (c : ℝ)) * (2 * c + 1) * (2 * c + 2) *
      ((2 * (a : ℝ)) * (2 * a + 1) * (2 * a + 2))) =
      u * Real.sqrt (((2 * (a : ℝ)) * (2 * a + 2)) * ((2 * (c : ℝ)) * (2 * c + 2))) := by
    rw [hD1, Real.sqrt_mul hDz.le]
  have he0 : 0 < Real.sqrt (((2 * (a : ℝ)) * (2 * a + 2)) * ((2 * (c : ℝ)) * (2 * c + 2))) :=
    Real.sqrt_pos.mpr hP
  have hu2 : u * u = (2 * (c : ℝ) + 1) * (2 * (a : ℝ) + 1) := Real.mul_self_sqrt hDz.le
  rw [h0, h0', h1, h1', hE, hs1, pow_succ, pow_succ]
  set e := Real.sqrt (((2 * (a : ℝ)) * (2 * a + 2)) * ((2 * (c : ℝ)) * (2 * c + 2)))
  field_simp
  ring


/-- The recurrence in the summation variable, with the spectral term `2 (2x+1) x (x+1) μ (μ+1)`
separated. -/
lemma orth_recurrence (a b c d μ : ℚ) (x : ℚ) :
    (((2 * (x : ℝ) + 1) *
        (((b : ℝ) * (b + 1) + a * (a + 1) - x * (x + 1)) *
            ((d : ℝ) * (d + 1) + c * (c + 1) - x * (x + 1)) -
          2 * ((b : ℝ) * (b + 1) * (d * (d + 1)) + a * (a + 1) * (c * (c + 1))))) +
      2 * (2 * (x : ℝ) + 1) * x * (x + 1) * ((μ : ℝ) * (μ + 1))) * sixJ x a b μ c d =
    (x : ℝ) * E6 a b c d (((x + 1 : ℚ)) : ℝ) * sixJ (x + 1) a b μ c d +
      ((x : ℝ) + 1) * E6 a b c d (x : ℝ) * sixJ (x - 1) a b μ c d := by
  have := sixJ_recurrence_ext x a b μ c d
  push_cast
  linear_combination this

/-- **DLMF 34.5.14, off-diagonal part**: for `μ (μ+1) ≠ μ' (μ'+1)`,
`∑_x (2x+1) {x a b; μ c d} {x a b; μ' c d} = 0`, the sum over the lattice `x = a + b - k`. -/
theorem sixJ_orth_offdiag (a b c d μ μ' : ℚ) (hne : (μ : ℝ) * (μ + 1) ≠ μ' * (μ' + 1)) :
    lsum a b (fun x => (2 * (x : ℝ) + 1) * (sixJ x a b μ c d * sixJ x a b μ' c d)) = 0 := by
  have hs : ∀ (ν x : ℚ), x < 0 → sixJ x a b ν c d = 0 := by
    intro ν x hx
    apply sixJ_eq_zero_of_not_tri12
    rintro ⟨h, -⟩
    have := h.nonneg_first
    linarith
  have hmain := green_lsum (a := a) (b := b)
    (E := fun y : ℚ => E6 a b c d (y : ℝ)) (s := fun x : ℚ => sixJ x a b μ c d)
    (s' := fun x : ℚ => sixJ x a b μ' c d)
    (P := fun x : ℚ => (2 * (x : ℝ) + 1) *
        (((b : ℝ) * (b + 1) + a * (a + 1) - x * (x + 1)) *
            ((d : ℝ) * (d + 1) + c * (c + 1) - x * (x + 1)) -
          2 * ((b : ℝ) * (b + 1) * (d * (d + 1)) + a * (a + 1) * (c * (c + 1)))))
    (Λ := (μ : ℝ) * (μ + 1)) (Λ' := (μ' : ℝ) * (μ' + 1))
    (hs μ) (hs μ')
    ⟨sixJ_eq_zero_of_not_tri12 (fun h => not_isTri_succ_top h.1),
      sixJ_eq_zero_of_not_tri12 (fun h => not_isTri_succ_top h.1)⟩
    (fun x => orth_recurrence a b c d μ x) (fun x => orth_recurrence a b c d μ' x) ?_
  · have h := mul_eq_zero.mp hmain
    rcases h with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  · -- the cross identity at `x = 0`
    by_cases hT : IsTri 0 a b ∧ IsTri 0 c d
    · obtain ⟨⟨⟨n1, hn1⟩, ⟨n2, hn2⟩, -⟩, ⟨⟨m1, hm1⟩, ⟨m2, hm2⟩, -⟩⟩ := hT
      have hab : a = b := by
        have : (0 : ℚ) ≤ n1 := by positivity
        have : (0 : ℚ) ≤ n2 := by positivity
        linarith
      have hcd : c = d := by
        have : (0 : ℚ) ≤ m1 := by positivity
        have : (0 : ℚ) ≤ m2 := by positivity
        linarith
      subst hab hcd
      by_cases hA : IsTri μ c a
      · by_cases hA' : IsTri μ' c a
        · exact cross_zero_special hA hA'
        · have hz : ∀ y, sixJ y a a μ' c c = 0 := fun y => sixJ_eq_zero_of_not_tri3 hA'
          simp [hz]
      · have hz : ∀ y, sixJ y a a μ c c = 0 := fun y => sixJ_eq_zero_of_not_tri3 hA
        simp [hz]
    · have hz : ∀ ν, sixJ 0 a b ν c d = 0 := fun ν => sixJ_eq_zero_of_not_tri12 (by simpa using hT)
      simp [hz]

/-- info: 'FormalResearch.Wigner.sixJ_orth_offdiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_orth_offdiag

end FormalResearch.Wigner
