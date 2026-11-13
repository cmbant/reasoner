module

public import FormalResearch.Wigner.OrthogOff

/-!
# Norm ratio for the `6j` orthogonality relation

Fix `a b c d`.  `normSq μ = ∑ₓ (2x+1) {x a b; μ c d}²`.  The recurrence in the entry `μ`
(`sixJ_recurrence_ext` after `sixJ_exch12`) has spectral parameter `x(x+1)`; combining it with the
off-diagonal orthogonality `sixJ_orth_offdiag` shows that `(2μ+1) normSq μ` does not depend on
`μ` (for `μ > 0`), as for classical orthogonal polynomials: `h_{n+1}/h_n` is a ratio of
recurrence coefficients.
-/

@[expose] public section

namespace FormalResearch.Wigner

/-- `∑ₓ (2x+1) {x a b; μ c d} {x a b; ν c d}`. -/
noncomputable def OA (a b c d μ ν : ℚ) : ℝ :=
  lsum a b (fun x => (2 * (x : ℝ) + 1) * (sixJ x a b μ c d * sixJ x a b ν c d))

/-- `∑ₓ (2x+1) x(x+1) {x a b; μ c d} {x a b; ν c d}`. -/
noncomputable def OB (a b c d μ ν : ℚ) : ℝ :=
  lsum a b (fun x => (2 * (x : ℝ) + 1) * ((x : ℝ) * (x + 1)) *
    (sixJ x a b μ c d * sixJ x a b ν c d))

lemma sixJ_neg_x {a b c d : ℚ} (μ : ℚ) {x : ℚ} (hx : x < 0) : sixJ x a b μ c d = 0 := by
  apply sixJ_eq_zero_of_not_tri12
  rintro ⟨h, -⟩
  have := h.nonneg_first
  linarith

lemma OA_symm (a b c d μ ν : ℚ) : OA a b c d μ ν = OA a b c d ν μ := by
  unfold OA; apply lsum_congr; intro x; ring

lemma OB_symm (a b c d μ ν : ℚ) : OB a b c d μ ν = OB a b c d ν μ := by
  unfold OB; apply lsum_congr; intro x; ring

/-- The recurrence in the entry `μ`, spectral parameter `x (x+1)`. -/
lemma orth_lambda_recurrence (a b c d x μ : ℚ) :
    ((2 * (μ : ℝ) + 1) *
        (((b : ℝ) * (b + 1) + c * (c + 1) - μ * (μ + 1)) *
            ((d : ℝ) * (d + 1) + a * (a + 1) - μ * (μ + 1)) -
          2 * ((b : ℝ) * (b + 1) * (d * (d + 1)) + c * (c + 1) * (a * (a + 1)))) +
      2 * (2 * (μ : ℝ) + 1) * μ * (μ + 1) * ((x : ℝ) * (x + 1))) * sixJ x a b μ c d =
    (μ : ℝ) * E6 c b a d (((μ + 1 : ℚ)) : ℝ) * sixJ x a b (μ + 1) c d +
      ((μ : ℝ) + 1) * E6 c b a d (μ : ℝ) * sixJ x a b (μ - 1) c d := by
  have := sixJ_recurrence_ext μ c b x a d
  rw [sixJ_exch12 x a b μ c d, sixJ_exch12 x a b (μ + 1) c d, sixJ_exch12 x a b (μ - 1) c d]
    at this
  push_cast
  linear_combination this

/-- The summed recurrence in `μ`. -/
lemma orth_sum_relation (a b c d μ ν : ℚ) :
    ((2 * (μ : ℝ) + 1) *
        (((b : ℝ) * (b + 1) + c * (c + 1) - μ * (μ + 1)) *
            ((d : ℝ) * (d + 1) + a * (a + 1) - μ * (μ + 1)) -
          2 * ((b : ℝ) * (b + 1) * (d * (d + 1)) + c * (c + 1) * (a * (a + 1))))) *
        OA a b c d μ ν +
      2 * (2 * (μ : ℝ) + 1) * μ * (μ + 1) * OB a b c d μ ν =
    (μ : ℝ) * E6 c b a d (((μ + 1 : ℚ)) : ℝ) * OA a b c d (μ + 1) ν +
      ((μ : ℝ) + 1) * E6 c b a d (μ : ℝ) * OA a b c d (μ - 1) ν := by
  have hz : ∀ (ρ : ℚ) (x : ℚ), x < 0 → (2 * (x : ℝ) + 1) * (sixJ x a b ρ c d * sixJ x a b ν c d) = 0 := by
    intro ρ x hx; rw [sixJ_neg_x ρ hx]; ring
  have hz2 : ∀ (ρ : ℚ) (x : ℚ), x < 0 →
      (2 * (x : ℝ) + 1) * ((x : ℝ) * (x + 1)) * (sixJ x a b ρ c d * sixJ x a b ν c d) = 0 := by
    intro ρ x hx; rw [sixJ_neg_x ρ hx]; ring
  have h := lsum_congr (a := a) (b := b)
    (f := fun x : ℚ => ((2 * (μ : ℝ) + 1) *
        (((b : ℝ) * (b + 1) + c * (c + 1) - μ * (μ + 1)) *
            ((d : ℝ) * (d + 1) + a * (a + 1) - μ * (μ + 1)) -
          2 * ((b : ℝ) * (b + 1) * (d * (d + 1)) + c * (c + 1) * (a * (a + 1))))) *
        ((2 * (x : ℝ) + 1) * (sixJ x a b μ c d * sixJ x a b ν c d)) +
      (2 * (2 * (μ : ℝ) + 1) * μ * (μ + 1)) *
        ((2 * (x : ℝ) + 1) * ((x : ℝ) * (x + 1)) * (sixJ x a b μ c d * sixJ x a b ν c d)))
    (g := fun x : ℚ => ((μ : ℝ) * E6 c b a d (((μ + 1 : ℚ)) : ℝ)) *
        ((2 * (x : ℝ) + 1) * (sixJ x a b (μ + 1) c d * sixJ x a b ν c d)) +
      (((μ : ℝ) + 1) * E6 c b a d (μ : ℝ)) *
        ((2 * (x : ℝ) + 1) * (sixJ x a b (μ - 1) c d * sixJ x a b ν c d)))
    (by
      intro x
      have := orth_lambda_recurrence a b c d x μ
      linear_combination ((2 * (x : ℝ) + 1) * sixJ x a b ν c d) * this)
  rw [lsum_comb (hz μ) (hz2 μ), lsum_comb (hz (μ + 1)) (hz (μ - 1))] at h
  unfold OA OB
  linear_combination h

/-- `(2μ+1) ∑ₓ (2x+1) {x a b; μ c d}²` is independent of `μ` (here the step `μ → μ+1`, `μ > 0`,
under non-vanishing of the recurrence coefficient). -/
theorem orth_norm_ratio (a b c d μ : ℚ) (hμ : 0 < μ)
    (hF : E6 c b a d (((μ + 1 : ℚ)) : ℝ) ≠ 0) :
    (2 * (μ : ℝ) + 3) * OA a b c d (μ + 1) (μ + 1) = (2 * (μ : ℝ) + 1) * OA a b c d μ μ := by
  have hμ' : (0 : ℝ) < μ := by exact_mod_cast hμ
  have o1 : OA a b c d μ (μ + 1) = 0 := by
    apply sixJ_orth_offdiag
    push_cast
    intro h
    nlinarith
  have o2 : OA a b c d (μ - 1) (μ + 1) = 0 := by
    apply sixJ_orth_offdiag
    push_cast
    intro h
    nlinarith
  have o3 : OA a b c d (μ + 1 + 1) μ = 0 := by
    apply sixJ_orth_offdiag
    push_cast
    intro h
    nlinarith
  have o4 : OA a b c d (μ + 1) μ = 0 := by rw [OA_symm, o1]
  have h1 := orth_sum_relation a b c d μ (μ + 1)
  have h2 := orth_sum_relation a b c d (μ + 1) μ
  rw [o1, o2] at h1
  rw [o3, o4, add_sub_cancel_right, OB_symm a b c d (μ + 1) μ] at h2
  push_cast at h1 h2 hF
  have hne : (μ : ℝ) * ((μ : ℝ) + 2) * E6 c b a d ((μ : ℝ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  linear_combination (-(2 * (μ : ℝ) + 3) * ((μ : ℝ) + 2)) * h1 +
    ((μ : ℝ) * (2 * μ + 1)) * h2

/-- Admissibility of `μ` for the matrix `{x a b; μ c d}`: the two triads containing `μ`. -/
def OAdm (a b c d μ : ℚ) : Prop := IsTri μ a d ∧ IsTri μ c b

lemma IsTri.of_between {μ a d : ℚ} {n : ℕ} (h0 : IsTri μ a d) (h1 : IsTri (μ + n) a d) {k : ℕ}
    (hk : k ≤ n) : IsTri (μ + k) a d := by
  obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, -⟩ := h0
  obtain ⟨-, -, ⟨p3, hp3⟩⟩ := h1
  refine ⟨⟨p1 + k, ?_⟩, ⟨p2 + k, ?_⟩, ⟨p3 + (n - k), ?_⟩⟩
  · push_cast; linarith
  · push_cast; linarith
  · have : ((n - k : ℕ) : ℚ) = n - k := by push_cast [Nat.cast_sub hk]; ring
    push_cast [this]; linarith

lemma OAdm.of_between {a b c d μ : ℚ} {n : ℕ} (h0 : OAdm a b c d μ) (h1 : OAdm a b c d (μ + n))
    {k : ℕ} (hk : k ≤ n) : OAdm a b c d (μ + k) :=
  ⟨h0.1.of_between h1.1 hk, h0.2.of_between h1.2 hk⟩

lemma E6_ne_zero_of_adm {a b c d μ : ℚ} (h : OAdm a b c d μ) (h' : OAdm a b c d (μ + 1)) :
    E6 c b a d (((μ + 1 : ℚ)) : ℝ) ≠ 0 := by
  obtain ⟨⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, -⟩, ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩, -⟩⟩ := h
  obtain ⟨⟨-, -, ⟨p3, hp3⟩⟩, ⟨-, -, ⟨q3, hq3⟩⟩⟩ := h'
  have e1 : (μ : ℝ) + a - d = p1 := by exact_mod_cast hp1
  have e2 : (μ : ℝ) - a + d = p2 := by exact_mod_cast hp2
  have e3 : -((μ : ℝ) + 1) + a + d = p3 := by exact_mod_cast (by linarith : -(μ + 1) + a + d = p3)
  have f1 : (μ : ℝ) + c - b = q1 := by exact_mod_cast hq1
  have f2 : (μ : ℝ) - c + b = q2 := by exact_mod_cast hq2
  have f3 : -((μ : ℝ) + 1) + c + b = q3 := by exact_mod_cast (by linarith : -(μ + 1) + c + b = q3)
  have n1 : (0 : ℝ) ≤ p1 := by positivity
  have n2 : (0 : ℝ) ≤ p2 := by positivity
  have n3 : (0 : ℝ) ≤ p3 := by positivity
  have m1 : (0 : ℝ) ≤ q1 := by positivity
  have m2 : (0 : ℝ) ≤ q2 := by positivity
  have m3 : (0 : ℝ) ≤ q3 := by positivity
  unfold E6
  push_cast
  apply (Real.sqrt_pos.mpr _).ne'
  have g1 : 0 < ((μ : ℝ) + 1) ^ 2 - ((c : ℝ) - b) ^ 2 := by
    have : ((μ : ℝ) + 1) ^ 2 - ((c : ℝ) - b) ^ 2 =
        ((μ : ℝ) + 1 + c - b) * ((μ : ℝ) + 1 - c + b) := by ring
    rw [this]; apply mul_pos <;> linarith
  have g2 : 0 < ((c : ℝ) + b + 1) ^ 2 - ((μ : ℝ) + 1) ^ 2 := by
    have : ((c : ℝ) + b + 1) ^ 2 - ((μ : ℝ) + 1) ^ 2 =
        ((c : ℝ) + b + 1 - (μ + 1)) * ((c : ℝ) + b + 1 + (μ + 1)) := by ring
    rw [this]; apply mul_pos <;> linarith
  have g3 : 0 < ((μ : ℝ) + 1) ^ 2 - ((a : ℝ) - d) ^ 2 := by
    have : ((μ : ℝ) + 1) ^ 2 - ((a : ℝ) - d) ^ 2 =
        ((μ : ℝ) + 1 + a - d) * ((μ : ℝ) + 1 - a + d) := by ring
    rw [this]; apply mul_pos <;> linarith
  have g4 : 0 < ((a : ℝ) + d + 1) ^ 2 - ((μ : ℝ) + 1) ^ 2 := by
    have : ((a : ℝ) + d + 1) ^ 2 - ((μ : ℝ) + 1) ^ 2 =
        ((a : ℝ) + d + 1 - (μ + 1)) * ((a : ℝ) + d + 1 + (μ + 1)) := by ring
    rw [this]; apply mul_pos <;> linarith
  positivity

/-- The degenerate step `μ = 0 → 1` of the norm ratio, where the recurrence in `μ` carries no
information at `μ = 0`: here `a = d`, `c = b` and `{x a b; 1 b a}` is an explicit multiple of
`{x a b; 0 b a}` (DLMF 34.5.1 and 34.5.7). -/
theorem orth_norm_step_zero (a b : ℚ) (h1 : OAdm a b b a 1) :
    3 * OA a b b a 1 1 = OA a b b a 0 0 := by
  obtain ⟨hA1, hB1⟩ := h1
  -- `1 ≤ 2a`, `1 ≤ 2b`
  have ha : 1 ≤ 2 * a := by
    obtain ⟨-, -, ⟨n, hn⟩⟩ := hA1
    have : (0 : ℚ) ≤ n := by positivity
    linarith
  have hb : 1 ≤ 2 * b := by
    obtain ⟨-, -, ⟨n, hn⟩⟩ := hB1
    have : (0 : ℚ) ≤ n := by positivity
    linarith
  have ha' : (1 : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ 2 * (b : ℝ) := by exact_mod_cast hb
  set Dz : ℝ := (2 * (a : ℝ) + 1) * (2 * (b : ℝ) + 1) with hDz
  set P : ℝ := ((2 * (a : ℝ)) * (2 * a + 2)) * ((2 * (b : ℝ)) * (2 * b + 2)) with hP
  have hDz0 : 0 < Dz := by positivity
  have hP0 : 0 < P := by positivity
  set u := Real.sqrt Dz with hu
  set e := Real.sqrt P with he
  have hu0 : 0 < u := Real.sqrt_pos.mpr hDz0
  have he0 : 0 < e := Real.sqrt_pos.mpr hP0
  have hD1 : ((2 * (a : ℝ)) * (2 * a + 1) * (2 * a + 2)) * ((2 * (b : ℝ)) * (2 * b + 1) * (2 * b + 2))
      = Dz * P := by rw [hDz, hP]; ring
  have hs1 : Real.sqrt (((2 * (a : ℝ)) * (2 * a + 1) * (2 * a + 2)) *
      ((2 * (b : ℝ)) * (2 * b + 1) * (2 * b + 2))) = u * e := by
    rw [hD1, Real.sqrt_mul hDz0.le]
  -- the explicit relation
  set K : ℝ := (a : ℝ) * (a + 1) + b * (b + 1) with hK
  have hrel : ∀ x : ℚ, sixJ x a b 1 b a =
      -(2 / e) * (K - (x : ℝ) * (x + 1)) * sixJ x a b 0 b a := by
    intro x
    by_cases hx : IsTri x a b
    · obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, ⟨p3, hp3⟩⟩ := hx
      have hN : ((p1 + p2 + p3 : ℕ) : ℚ) = x + a + b := by push_cast; linarith
      rw [sixJ_zero_left ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, ⟨p3, hp3⟩⟩ (p1 + p2 + p3) hN.symm.symm,
        sixJ_one_left ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, ⟨p3, hp3⟩⟩ (p1 + p2 + p3) hN.symm.symm ha hb,
        pow_succ, hs1]
      rw [hK]
      field_simp
      ring
    · have hz : ∀ ν : ℚ, sixJ x a b ν b a = 0 := fun ν =>
        sixJ_eq_zero_of_not_tri12 (fun h => hx h.1)
      rw [hz, hz]; ring
  have hz : ∀ (ν : ℚ) (x : ℚ), x < 0 → sixJ x a b ν b a = 0 := fun ν x hx => sixJ_neg_x ν hx
  set f1 : ℚ → ℝ := fun x => (2 * (x : ℝ) + 1) * ((K - (x : ℝ) * (x + 1)) *
    (sixJ x a b 0 b a * sixJ x a b 0 b a)) with hf1
  set f2 : ℚ → ℝ := fun x => (2 * (x : ℝ) + 1) * ((K - (x : ℝ) * (x + 1)) ^ 2 *
    (sixJ x a b 0 b a * sixJ x a b 0 b a)) with hf2
  have hf1z : ∀ x : ℚ, x < 0 → f1 x = 0 := fun x hx => by simp [hf1, hz 0 x hx]
  have hf2z : ∀ x : ℚ, x < 0 → f2 x = 0 := fun x hx => by simp [hf2, hz 0 x hx]
  have hκ : (2 / e) * e = 2 := by field_simp
  -- OA 1 0
  have eA10 : OA a b b a 1 0 = -(2 / e) * lsum a b f1 := by
    unfold OA
    rw [← lsum_smul hf1z]
    apply lsum_congr; intro x
    rw [hrel x]; simp only [hf1]; ring
  have eB10 : OB a b b a 1 0 = -(2 / e) * K * lsum a b f1 + (2 / e) * lsum a b f2 := by
    have : OB a b b a 1 0 = lsum a b (fun x => (-(2 / e) * K) * f1 x + (2 / e) * f2 x) := by
      unfold OB
      apply lsum_congr; intro x
      rw [hrel x]; simp only [hf1, hf2]; ring
    rw [this, lsum_comb hf1z hf2z]
  have eA11 : OA a b b a 1 1 = (2 / e) ^ 2 * lsum a b f2 := by
    unfold OA
    rw [← lsum_smul hf2z]
    apply lsum_congr; intro x
    rw [hrel x]; simp only [hf2]; ring
  have o10 : OA a b b a 1 0 = 0 := by
    apply sixJ_orth_offdiag; norm_num
  have o20 : OA a b b a 2 0 = 0 := by
    apply sixJ_orth_offdiag; norm_num
  have l1 : lsum a b f1 = 0 := by
    rw [o10] at eA10
    have : (2 / e) ≠ 0 := by positivity
    have h2 : (2 / e) * lsum a b f1 = 0 := by linarith
    exact (mul_eq_zero.mp h2).resolve_left this
  have hE : E6 b b a a (((1 : ℚ)) : ℝ) = e := by
    unfold E6
    rw [he, hP]
    congr 1
    push_cast
    ring
  have h := orth_sum_relation a b b a 1 0
  have hs : ((1 : ℚ) + 1) = 2 := by norm_num
  have hs0 : ((1 : ℚ) - 1) = 0 := by norm_num
  rw [hs, hs0, o10, o20] at h
  push_cast at h
  have hE2 : E6 b b a a (1 : ℝ) = e := by simpa using hE
  rw [hE2] at h
  rw [eB10, l1] at h
  rw [eA11]
  have hcl : (2 / e) * e = 2 := hκ
  -- `12 κ L₂ = 2 e OA₀₀`
  have h' : 12 * ((2 / e) * lsum a b f2) = 2 * e * OA a b b a 0 0 := by linarith
  have key : 3 * ((2 / e) ^ 2 * lsum a b f2) = OA a b b a 0 0 := by
    have : (2 / e) ^ 2 * lsum a b f2 = (2 / e) * ((2 / e) * lsum a b f2) := by ring
    rw [this]
    have h6 : (2 / e) * lsum a b f2 = e * OA a b b a 0 0 / 6 := by linarith
    rw [h6]
    field_simp
    nlinarith [hκ]
  exact key

lemma OAdm.zero_eq {a b c d : ℚ} (h : OAdm a b c d 0) : a = d ∧ c = b := by
  obtain ⟨⟨⟨n1, hn1⟩, ⟨n2, hn2⟩, -⟩, ⟨⟨m1, hm1⟩, ⟨m2, hm2⟩, -⟩⟩ := h
  have : (0 : ℚ) ≤ n1 := by positivity
  have : (0 : ℚ) ≤ n2 := by positivity
  have : (0 : ℚ) ≤ m1 := by positivity
  have : (0 : ℚ) ≤ m2 := by positivity
  constructor <;> linarith

/-- Along the admissible `μ`-lattice starting at `μ₀ ≥ 0`, `(2μ+1) ∑ₓ (2x+1) {x a b; μ c d}²` is
constant. -/
theorem orth_norm_chain (a b c d μ₀ : ℚ) (h0 : 0 ≤ μ₀) (hadm : OAdm a b c d μ₀) (n : ℕ)
    (hn : OAdm a b c d (μ₀ + n)) :
    (2 * ((μ₀ + n : ℚ) : ℝ) + 1) * OA a b c d (μ₀ + n) (μ₀ + n) =
      (2 * (μ₀ : ℝ) + 1) * OA a b c d μ₀ μ₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev : OAdm a b c d (μ₀ + (n : ℕ)) := hadm.of_between hn (Nat.le_succ n)
    have ih' := ih hprev
    by_cases hpos : 0 < μ₀ + n
    · have hF := E6_ne_zero_of_adm hprev (by
        have : μ₀ + ((n + 1 : ℕ) : ℚ) = μ₀ + n + 1 := by push_cast; ring
        rw [← this]; exact hn)
      have := orth_norm_ratio a b c d (μ₀ + n) hpos hF
      have e : μ₀ + ((n + 1 : ℕ) : ℚ) = μ₀ + n + 1 := by push_cast; ring
      rw [e]
      push_cast at this ih' ⊢
      linarith
    · have hμ : μ₀ = 0 := by
        have : (0 : ℚ) ≤ n := by positivity
        linarith
      have hn0 : n = 0 := by
        have : (0 : ℚ) ≤ μ₀ := h0
        have h' : (n : ℚ) ≤ 0 := by linarith
        exact_mod_cast le_antisymm h' (by positivity)
      subst hμ hn0
      obtain ⟨rfl, rfl⟩ := hadm.zero_eq
      have h1 : OAdm a c c a 1 := by simpa using hn
      have := orth_norm_step_zero a c h1
      simp only [zero_add, Nat.cast_one, Rat.cast_one, Rat.cast_zero] at this ⊢
      linarith

/-- info: 'FormalResearch.Wigner.orth_norm_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orth_norm_ratio

/-- info: 'FormalResearch.Wigner.orth_norm_step_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orth_norm_step_zero

/-- info: 'FormalResearch.Wigner.orth_norm_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orth_norm_chain

end FormalResearch.Wigner
